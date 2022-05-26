import Aesop
import Lean

open Lean
open Lean.Elab
open Lean.Elab.Term
open Lean.Elab.Command
open Lean.Meta

declare_syntax_cat queryBinder
syntax "(" ident+ ":" term ")" : queryBinder

declare_syntax_cat query
syntax queryBinder* ":" queryBinder+ : query

def mkForalls [Monad m] [MonadQuotation m] (xs : Array (Name × Syntax))
    (e : Syntax) : m Syntax :=
  let vs := xs.map (mkIdent ·.fst)
  let ts := xs.map (·.snd)
  `(∀ $[($vs:ident : $ts:term)]*, $e:term)

def mkExistss [Monad m] [MonadQuotation m] (xs : Array (Name × Syntax))
    (e : Syntax) : m Syntax := do
  let vs := xs.map (mkIdent ·.fst)
  let ts := xs.map (·.snd)
  `(∃ $[($vs:ident : $ts:term)]*, $e:term)

def queryBindersToArray (stx : Array Syntax) :
    TermElabM (Array (Name × Syntax)) :=
  stx.concatMapM λ stx => withRef stx do
    match stx with
    | `(queryBinder| ($ids:ident* : $t:term)) =>
      return ids.map λ id => (id.getId, t)
    | _ => throwUnsupportedSyntax

@[inline]
def matchExistsIntro : Expr → Option (Level × Expr × Expr × Expr × Expr)
  | .app (.app (.app (.app (.const ``Exists.intro [u] _) type _) p _ ) w _) e _ =>
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
        | some (u, ty, p, w, e) =>
          let userName ← forallBoundedTelescope p (some 1) λ fvars e =>
            if h : 0 < fvars.size then
              return (← getLocalDecl $ fvars.get ⟨0, h⟩ |>.fvarId!).userName
            else
              mkFreshUserName `h
          withLetDecl userName ty w λ letDecl => do
            let letDeclFVarId := letDecl.fvarId!
            let e := (← kabstract e w).instantiate1 (mkFVar letDeclFVarId)
            check e <|> throwError
              "existsIntroBoundedTelescope: result of kabstract is not type-correct"
            go (fvarIds.push letDeclFVarId) e n

def printResult (e : Expr) (assumptionStxs : Array (Name × Syntax))
    (conclusionStxs : Array (Name × Syntax)) : MetaM MessageData :=
  let numAssumptions := assumptionStxs.size
  let numConclusions := conclusionStxs.size
  existsIntroBoundedTelescope e numConclusions λ fvarIds _ => do
    if fvarIds.size != numConclusions then
      throwError "printResult: unexpected number of ∃ binders"
    let conclusionsMsgs ← fvarIds.mapIdxM λ i fvarId => do
      let value ← reduceAll (← getLocalDecl fvarId).value
      let (name, type) := conclusionStxs[i]
      let name := name.eraseMacroScopes
      return m!"{name} : {type} := {value}"

    let assumptionsMsg := joinLn $ assumptionStxs.map λ (name, type) =>
      m!"{name} : {type}"
    let assumptionsMsg :=
      if assumptionsMsg.isEmpty then m!"" else assumptionsMsg ++ "\n"
    addMessageContextFull $ assumptionsMsg ++ "---\n" ++ joinLn conclusionsMsgs
  where
    joinLn (msgs : Array MessageData) : MessageData :=
      .joinSep msgs.toList "\n"

def aesopWrapper (goal : MVarId) : TermElabM (Option Expr) :=
  try
    discard $ Aesop.bestFirst goal
    getExprMVarAssignment? goal
  catch _ => return none

elab cmd:"#query" q:query : command => withRef cmd do
  match q with
  | `(query| $p₁:queryBinder* : $p₂:queryBinder*) => liftTermElabM none do
    let assumptionStxs ← queryBindersToArray p₁
    let conclusionStxs ← queryBindersToArray p₂
    let stx ← mkForalls assumptionStxs (← mkExistss conclusionStxs (← `(True)))
    let msg ← withoutModifyingState do
      let tgt ← elabTermAndSynthesize stx (some $ mkSort levelZero)
      let goal := (← mkFreshExprMVar (some tgt)).mvarId!
      let (_, goal) ← introN goal assumptionStxs.size
      let (some result) ← aesopWrapper goal
        | throwError "No solution found."
      withMVarContext goal do
        addMessageContext (← printResult result assumptionStxs conclusionStxs)
    logInfo msg
  | _ => throwUnsupportedSyntax
