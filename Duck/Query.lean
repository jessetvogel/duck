import Aesop
import Lean

open Lean
open Lean.Elab
open Lean.Elab.Term
open Lean.Meta
open Command

declare_syntax_cat queryBinder
syntax "(" ident+ ":" term ")" : queryBinder

declare_syntax_cat query
syntax queryBinder* ":" queryBinder+ : query

def mkForall (xs : Array (Syntax × Syntax)) (e : Syntax) : Command.CommandElabM Syntax :=
  let vs := xs.map Prod.fst
  let ts := xs.map Prod.snd
  `(∀ $[($vs:ident : $ts:term)]*, $e:term)

def mkExists (xs : Array (Syntax × Syntax)) (e : Syntax) : Command.CommandElabM Syntax :=
  let vs := xs.map Prod.fst
  let ts := xs.map Prod.snd
  `(∃ $[($vs:ident : $ts:term)]*, $e:term)

-- TODO : add stuff to local context, so we don't get into trouble
def extractExists (n : Nat) (expr : Expr) : MetaM (List Expr × Expr) := do
  match n with
  | 0 => return ([], expr)
  | n' + 1 => do
    -- Use `whnf` because of reasons
    let (obj, proof) := match (← whnf expr) with
    | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``Exists.intro _ _) type _) h _) obj _) proof _ => (obj, proof)
    | _ => panic! "expression does not have expected form (in extractExists)"
    -- Use `reduce` to simplify the objects. Note: we don't need to simplify any proofs
    let obj ← reduce (skipProofs := true) obj
    -- Continue recursively
    let (objs, proof) ← extractExists n' proof
    return (obj :: objs, proof)

def extractForall (n : Nat) (expr : Expr) : MetaM (List Expr × Expr) := do
  match n with
  | 0 => return ([], expr)
  | n' + 1 => do
    -- Use `whnf` because of reasons
    let whnfExpr ← whnf expr
    let (obj, proof) := match whnfExpr with
    | Expr.lam _ obj proof _ => (obj, proof)
    | _ => panic! "expression does not have expected form (in extractForall)"
    -- Use `reduce` to simplify the objects. Note: we don't need to simplify any proofs
    let obj ← reduce (skipProofs := true) obj
    -- Continue recursively
    let (objs, proof) ← extractForall n' proof
    return (obj :: objs, proof)

def queryBindersToArray (stx : Array Syntax) : Array (Syntax × Syntax) :=
  stx.concatMap λ s => match s with
  | `(queryBinder| ($i:ident* : $t:term)) => i.map λ id => (id, t)
  | _ => #[]

def aesopWrapper (goal : MVarId) : TermElabM (Option Expr) :=
  withMVarContext goal do
    -- Configure Aesop
    let config : Aesop.Frontend.TacticConfig := {
      additionalRules := #[]
      erasedRules := #[]
      enabledRuleSets := #[Aesop.defaultRuleSetName, Aesop.builtinRuleSetName]
      options := {}
    }

    let profile := Aesop.Profile.empty

    try
      -- Call Aesop.search
      let search ← Aesop.search Aesop.BestFirstQueue config goal profile
      -- Return assignment
      Lean.Meta.getExprMVarAssignment? goal
    catch error => do
      -- If search failed, return none as solution
      return none

elab cmd:"#query" q:query : command => do
  match q with
  | `(query| $p₁:queryBinder* : $p₂:queryBinder*) => do
    -- Convert query-syntax to ∀...Σ...-syntax
    let argsForall := queryBindersToArray p₁
    let argsExists := queryBindersToArray p₂
    let m := argsForall.size
    let n := argsExists.size
    let stxTrue := Syntax.ident SourceInfo.none "".toSubstring `True []
    let stxTrue ← `(True)
    let stxExists ← if n == 0 then pure stxTrue else mkExists argsExists stxTrue
    let stxForall ← if m == 0 then pure stxExists else mkForall argsForall stxExists
    let stx := stxForall

    let result ← liftTermElabM none do
      -- Elaborate Syntax into Expr
      let expr ← elabTerm stx none
      -- Create meta variable (goal) from constructed term
      let goalExpr ← mkFreshExprMVar (some expr) MetavarKind.natural Name.anonymous
      let goal := goalExpr.mvarId!
      let goalType ← getMVarType goal
      -- Call Aesop with the goal 
      match ← aesopWrapper goal with
      | some solution => do
        let (objs₁, pf) ← extractForall m solution
        let (objs₂, pf) ← extractExists n pf
        return some (objs₁, objs₂)
      | none => return none

    -- Print result
    match result with
    | some result => logInfoAt cmd $ toMessageData result
    | none => do
      throw $ Exception.error cmd "No solution found.."

  | _ => throwUnsupportedSyntax 
