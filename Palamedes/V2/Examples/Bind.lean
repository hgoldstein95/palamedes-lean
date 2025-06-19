import Palamedes.V2.Synthesizer

import Mathlib.Lean.Expr
import Lean.Elab.Tactic.NormCast

open Gen CorrectGen
open Lean Meta Elab Tactic Term

/-- Extracts the conjuncts of an ∧-expression.

    NOTE: This needs to be in `MetaM`, although I'm not 100% sure why. I think it may have
    something to do with how `match_expr` works under the hood? -/
partial def getConjuncts (e : Expr) : MetaM (List Expr) := do
  match_expr e with
  | And p q => return (← getConjuncts p) ++ (← getConjuncts q)
  | _ => return [e]

/-- Proves a goal of the form `?a ∧ ?b = e` by partitioning the conjuncts in `e` based on whether or
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
      let (varIn, varNotIn) := conjuncts.partition (·.containsFVar var)

      -- Create a new `rhs` with the appropriate grouping of conjuncts
      let rhs' := mkAppN (.const ``And []) #[
          varNotIn.foldr (fun a b => mkAppN (.const ``And []) #[a, b]) (.const ``True []),
          varIn.foldr (fun a b => mkAppN (.const ``And []) #[a, b]) (.const ``True []),
        ]

      -- Assert that our goal's type is actually `rhs' = rhs` and prove the equality with aesop
      let goalTy' ← mkAppM ``Eq #[rhs', rhs]
      if ← isDefEq goalTy goalTy' then
        let ([], _) ← runTactic g (← `(tactic| aesop))
          | throwError "aesop could not prove {← instantiateMVars goalTy'}"

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
