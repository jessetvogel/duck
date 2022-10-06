import Aesop

open Lean
open Lean.Elab
open Lean.Elab.Term
open Lean.Elab.Command
open Lean.Meta

declare_syntax_cat queryBinder

syntax "(" ident+ ":" term ")" : queryBinder

declare_syntax_cat query
syntax queryBinder* ":" queryBinder+ : query

def mkForalls [Monad m] [MonadQuotation m] (xs : Array (Name × Term))
    (e : Term) : m Term :=
  let vs := xs.map (mkIdent ·.fst)
  let ts := xs.map (·.snd)
  `(∀ $[($vs:ident : $ts:term)]*, $e:term)

def mkExistss [Monad m] [MonadQuotation m] (xs : Array (Name × Term))
    (e : Term) : m Term := do
  let vs := xs.map (mkIdent ·.fst)
  let ts := xs.map (·.snd)
  `(∃ $[($vs:ident : $ts:term)]*, $e:term)

def queryBindersToArray (stx : Array (TSyntax `queryBinder)) :
    TermElabM (Array (Name × Term)) :=
  stx.concatMapM λ stx => withRef stx do
    match stx with
    | `(queryBinder| ($ids:ident* : $t:term)) =>
      return ids.map λ id => (id.getId, t)
    | _ => throwUnsupportedSyntax

@[inline]
def matchExistsIntro : Expr → Option (Level × Expr × Expr × Expr × Expr)
  | .app (.app (.app (.app (.const ``Exists.intro [u]) type) p) w) e =>
    some (u, type, p, w, e)
  | _ => none

-- Matches an expression of type
--
--   ∃ (x₁ : T₁), ..., (xₙ : Tₙ), U.
--
-- `k` is executed in a modified local context where for each binder (xᵢ : Tᵢ),
-- we have a local def `xᵢ : Tᵢ := wᵢ`. `k` receives as input the `FVarId`s of
-- these local defs and a term of type `U`.
--
-- Matching is performed up to `whnf`. If there are less than `n` applications
-- of `Exists.intro` in the given expression, matching stops early.
def existsIntroBoundedTelescope (e : Expr) (n : Nat)
    (k : Array FVarId → Expr → MetaM α) : MetaM α := do
  go (Array.mkEmpty n) e n
  where
    go (fvarIds : Array FVarId) (e : Expr) : Nat → MetaM α
      | 0 => k fvarIds e
      | n + 1 => do
        let e ← whnf e
        match matchExistsIntro e with
        | none => k fvarIds e
        | some (_, ty, p, w, e) =>
          let userName ← forallBoundedTelescope p (some 1) λ fvars _ =>
            if h : 0 < fvars.size then
              fvars.get ⟨0, h⟩ |>.fvarId!.getUserName
            else
              mkFreshUserName `h
          withLetDecl userName ty w λ letDecl => do
            let letDeclFVarId := letDecl.fvarId!
            let e := (← kabstract e w).instantiate1 (mkFVar letDeclFVarId)
            check e <|> throwError
              "existsIntroBoundedTelescope: result of kabstract is not type-correct"
            go (fvarIds.push letDeclFVarId) e n

def printResult (e : Expr) (assumptionStxs : Array (Name × Term))
    (conclusionStxs : Array (Name × Term)) : MetaM MessageData :=
  let numConclusions := conclusionStxs.size
  existsIntroBoundedTelescope e numConclusions λ fvarIds _ => do
    if h : fvarIds.size = conclusionStxs.size then
      let conclusionsMsgs ← fvarIds.mapIdxM λ i fvarId => do
        let value ← reduceAll (← fvarId.getDecl).value
        have : i < conclusionStxs.size := by simp [←h, i.isLt]
        let (name, type) := conclusionStxs[i]
        let name := name.eraseMacroScopes
        return m!"{name} := {value}"
      let assumptionsMsg := joinLn $ assumptionStxs.map λ (name, type) =>
        m!"{name} : {type}"
      let assumptionsMsg :=
        if assumptionsMsg.isEmpty then m!"" else assumptionsMsg ++ "\n"
      addMessageContextFull $ assumptionsMsg ++ "---\n" ++ joinLn conclusionsMsgs
    else
      throwError "printResult: unexpected number of ∃ binders"
  where
    joinLn (msgs : Array MessageData) : MessageData :=
      .joinSep msgs.toList "\n"

def duckAesop (goal : MVarId) : MetaM (List MVarId) := do
  let rs ← Aesop.Frontend.getDefaultRuleSet (includeGlobalSimpTheorems := false)
    -- We do not include the global simp set (i.e. the @[simp] lemmas). This is
    -- important for two reasons:
    --
    -- - The global simp set rewrites `∃ x : T, True` to `T` and
    --   `∃ x : T, ∃ h : P x, ∃ h : P x, True` to `∃ x : T, P x`. This messes up
    --   our parser.
    -- - Rewriting leads to incomprehensible proof terms.
  let (goals, _) ← Aesop.search goal (ruleSet? := rs)
  return goals.toList

def duckAesopProof? (goal : MVarId) : MetaM (Option Expr) :=
  try
    discard $ duckAesop goal
    getExprMVarAssignment? goal
  catch error => do
    trace[debug] error.toMessageData
    return none

open Lean.Elab.Tactic in
elab &"duck_aesop" : tactic =>
  liftMetaTactic duckAesop

elab cmd:"#query" q:query : command => withRef cmd do
  match q with
  | `(query| $p₁:queryBinder* : $p₂:queryBinder*) => liftTermElabM do
    let assumptionStxs ← queryBindersToArray p₁
    let conclusionStxs ← queryBindersToArray p₂
    let stx ← mkForalls assumptionStxs (← mkExistss conclusionStxs (← `(True)))
    let msg ← withoutModifyingState do
      let tgt ← elabTermAndSynthesize stx (some $ mkSort levelZero)
      let goal := (← mkFreshExprMVar (some tgt)).mvarId!
      let (_, goal) ← goal.introN assumptionStxs.size
      let (some result) ← duckAesopProof? goal
        | throwError "No solution found."
      goal.withContext do
        addMessageContext (← printResult result assumptionStxs conclusionStxs)
    logInfo msg
  | _ => throwUnsupportedSyntax
