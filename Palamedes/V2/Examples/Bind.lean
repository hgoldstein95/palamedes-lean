import Palamedes.V2.Synthesizer

import Mathlib.Lean.Expr
import Lean.Elab.Tactic.NormCast

open Gen CorrectGen
open Lean Meta Elab Tactic Term

/-- Extracts the conjuncts of an ∧-expression. -/
private partial def getConjuncts (e: Expr) : TacticM (List Expr) := do
  match_expr e with
  | And p q => do
    let lhs_conjuncts ← getConjuncts p
    let rhs_conjuncts ← getConjuncts q
    return lhs_conjuncts ++ rhs_conjuncts
  | _ => return [e]

/-- Partitions a list of expressions based on whether or not they use a given `FVarId`.  -/
private def partitionContainsFVar (var : FVarId) (exprs : List Expr) : List Expr × List Expr :=
  match exprs with
  | .nil => ([], [])
  | .cons e es =>
    let (rest_t,rest_f) := partitionContainsFVar var es
    if e.containsFVar var then
      (e :: rest_t, rest_f)
    else
      (rest_t, e :: rest_f)

/-- Proves a goal of the form `e = e'` by partitioning the conjuncts in the RHS based on whether or
  not they contain `v`.

  E.g., the goal `?a ∧ ?b = v < 3 ∧ x = 5 ∧ 1 < v` is solved with
  ```
  ?a = (x = 5)
  ?b = (v < 3 ∧ 1 < v)
  ```
  -/
elab "partition_conjuncts " v:ident : tactic =>
  withMainContext do
    let g ← getMainGoal
    let goalDecl ← g.getDecl
    let goalTy := goalDecl.type
    let var ← elabAsFVar v
    match_expr goalTy with
    | Eq _α _lhs rhs =>
      -- Get and partition the conjuncts
      let conjuncts ← getConjuncts rhs
      let (varIn, varNotIn) := partitionContainsFVar var conjuncts

      -- Create a new `rhs` with the appropriate grouping of conjuncts
      let rhs' := mkAppN (.const ``And []) #[
          varNotIn.foldr (fun a b => mkAppN (.const ``And []) #[a, b]) (.const ``True []),
          varIn.foldr (fun a b => mkAppN (.const ``And []) #[a, b]) (.const ``True []),
        ]

      -- Create a new goal and prove it with aesop
      let goalTy' ← mkAppM ``Eq #[rhs', rhs]
      let g' ← mkFreshExprMVar (some goalTy')
      let _ ← runTactic g'.mvarId! (← `(tactic| aesop))

      -- NOTE: This was the trick to getting this to work. Checking that the goal type is equal to
      -- the new goal type unifies the metavariables.
      if ← isDefEq goalTy goalTy' then
        closeMainGoal `partitionResult g'
    | _ => pure ()

def genTwoBetweens2 : CorrectGen (λ (v : Nat × Nat) => ∃ x, (2 ≤ x ∧ x ≤ 6) ∧ ∃ y, 2 ≤ y ∧ y ≤ 100 ∧ v = (x,y)) := by
  apply convert (by rfl) (cbind _ _)
  · gapply (cbetween (by omega))
  · intro a
    -- NOTE: Rather than try to prove the whole equality, I just did the funext / congrArg on the
    -- outside. It doesn't matter too much. Note that we're now passing v directly.
    apply convert (by funext v; apply congrArg; funext; partition_conjuncts v) (cbind _ _)
    . cgenerator_search
    . cgenerator_search
