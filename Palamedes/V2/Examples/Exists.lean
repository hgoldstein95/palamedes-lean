import Palamedes.V2.Synthesizer
import Palamedes.V2.Examples.Bind
import Mathlib.Lean.Expr

open Gen CorrectGen


def genOneGtOther3: CorrectGen (λ (v : Nat × Nat) => ∃ y x, x > y ∧ v = (x,y)) := by
  gapply (cbind _ _)
  · gapply carbNat
  · intro b
    apply (cbind _ _)
    · gapply cgt
    · intro a
      gapply cpure (a.val,b.val)


theorem exists_swap_2nd' {α β : Type}(P : α → β → Prop) : (∃ x: α, ∃ y: β, P x y) = (∃ y: β, ∃ x: α, P x y) := by
 simp_all only [eq_iff_iff]
 apply Iff.intro
 · intro a
   obtain ⟨w, h⟩ := a
   obtain ⟨w_1, h⟩ := h
   apply Exists.intro
   · apply Exists.intro
     · exact h
 · intro a
   obtain ⟨w, h⟩ := a
   obtain ⟨w_1, h⟩ := h
   apply Exists.intro
   · apply Exists.intro
     · exact h

syntax "exists_swap_2nd" : tactic
macro_rules
| `(tactic| exists_swap_2nd) => `(tactic| conv => congr; intro v; rw[exists_swap_2nd'])

theorem exists_swap_3rd' {α β γ : Type}(P : α → β → γ → Prop) : (∃ x: α, ∃ y : β, ∃ z : γ,  P x y z) = (∃ z : γ, ∃ x: α, ∃ y: β,  P x y z) := by
  simp_all only [eq_iff_iff]
  apply Iff.intro
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨w_1, h⟩ := h
    obtain ⟨w_2, h⟩ := h
    apply Exists.intro
    · apply Exists.intro
      · apply Exists.intro
        · exact h
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨w_1, h⟩ := h
    obtain ⟨w_2, h⟩ := h
    apply Exists.intro
    · apply Exists.intro
      · apply Exists.intro
        · exact h

syntax "exists_swap_3rd" : tactic
macro_rules
| `(tactic| exists_swap_3rd) => `(tactic| conv => congr; intro v; rw[exists_swap_3rd'])

def genOneGtOther4: CorrectGen (λ (v : Nat × Nat) => ∃ x y, x > y ∧ v = (x,y)) := by
  --conv => congr; intro v; rw[exists_swap_2nd']
  exists_swap_2nd
  --exists_swap_3rd --rewrite failed, yay
  gapply (cbind _ _) --full proof of genOneGtOther3
  · gapply carbNat
  · intro b
    apply (cbind _ _)
    · gapply cgt
    · intro a
      gapply cpure (a.val,b.val)


def genOneGtOther5: CorrectGen (λ (v : Nat × Nat × Nat) => ∃ x y z, x > y ∧ v = (x,y,z)) := by
  --exists_swap_2nd --works yay
  exists_swap_3rd
  gapply (cbind _ _) --full proof of genOneGtOther3
  · gapply carbNat
  · intro c
    exists_swap_2nd
    gapply (cbind _ _)
    · gapply carbNat
    · intro b
      apply (cbind _ _)
      · gapply cgt
      · intro a
        gapply cpure (a.val,b.val,c.val)

-- def genOneGtOther : Gen (Nat × Nat) := by
--   generator_search (fun (v : Nat × Nat) => ∃ x y, x > 2 ∧ v = (x,y))

-- def genOneGtOther2 : Gen (Nat × Nat) := by
--   generator_search (fun (v : Nat × Nat) => ∃ x y, x > y ∧ v = (x,y))



-- theorem hoist' {α : Type} {P: α → Prop} {Q: Prop}:
--   (∃ t: α, Q ∧ P t) ↔ (Q ∧ ∃ t: α, P t) := by
--   simp_all only [exists_and_left]

open Lean Meta Elab Tactic Term in
private def hoistInner (e : Expr) (var : FVarId) (pushIn : List Expr) : MetaM ((List Expr) × Expr) := do
  let res ← match_expr e with
  | Exists α prop =>
    match prop with
    | (.lam name type lam_body binfo) =>
      let conjuncts ← getConjuncts lam_body
      let (exists_clauses, other) := conjuncts.partition (·.isAppOf `Exists)
      let (varIn, varNotIn) := other.partition (·.containsFVar var)
      match exists_clauses with
      | .nil => --inner-most (v clauses stop here)
        let (bvarIn, bvarNotIn) := varNotIn.partition (fun e' => (Expr.bvar 0).occurs e')
        let clauses' := bvarIn ++ pushIn ++ varIn
        let existsProp := (clauses'.drop 1).foldl (fun a b => mkAppN (.const ``And []) #[a, b]) (clauses'[0]?.getD (.const ``True []))
        let exists' :=  mkApp2 e.getAppFn α (.lam name type existsProp binfo)
        logInfo exists'
        let rest := bvarNotIn.map (fun e' => e'.lowerLooseBVars 1 1)
        dbg_trace f!"{rest}, {exists'}"
        return (rest, exists')
      | (.cons exists_clause .nil) => --recurse
        let (rest,inner_exists) ← hoistInner exists_clause var varIn
        dbg_trace rest
        let (bvarIn, bvarNotIn) := (varNotIn ++ rest).partition (fun e' => (Expr.bvar 0).occurs e')
        let clauses' := bvarIn ++ [inner_exists] -- want to keep the ∃ last so bind will be happy
        let existsProp := (clauses'.drop 1).foldl (fun a b => mkAppN (.const ``And []) #[a, b]) (clauses'[0]!)
        let exists' :=  mkApp2 e.getAppFn α (.lam name type existsProp binfo)
        logInfo exists'
        let rest' := bvarNotIn.map (fun e' => e'.lowerLooseBVars 1 1)
        dbg_trace f!"{rest'}, {exists'}"
        return (rest', exists')
      | _ => throwUnsupportedSyntax -- if this is not a sequence of ∃ this is not for us
    | _ => throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax

open Lean Meta Elab Tactic Term Conv in
elab "hoist'"  v:ident : conv => withMainContext do
  let g ← getMainGoal
  let body ← instantiateMVars (← Conv.getLhs)
  let var ← elabAsFVar v
  let (rest,inner_exists) ← hoistInner body var .nil
  let body' := if rest.isEmpty then
    inner_exists
  else
    let outer := (rest.drop 1).foldl (fun a b => mkAppN (.const ``And []) #[a, b]) (rest[0]!)
    mkAppN (.const ``And []) #[outer, inner_exists]
  -- Create a new goal and prove it with aesop
  let goalTy' ← mkAppM ``Eq #[body,body']
  let g' ← mkFreshExprMVar (some goalTy')
  let _ ← runTactic g'.mvarId! (← `(tactic| aesop))
  -- update lhs using the proof from aesop
  Conv.updateLhs body' g'


syntax "hoist" : tactic
macro_rules
| `(tactic| hoist) => `(tactic| conv => congr; intro v; hoist' v)

def genTwoBetweens: CorrectGen (fun (v: Nat × Nat) => ∃ x, ∃ y, 2 ≤ x ∧ x ≤ 6 ∧ 2 ≤ y ∧ y ≤ 100 ∧ v = (x,y)) := by
  hoist
  --conv => congr; simp only [hoist']; simp only [← and_assoc] --tactic will need to mess with associativity more generally
  apply (cbind _ _)
  · gapply (cbetween_partial)
  · intro x
    apply (cbind _ _)
    · gapply cbetween_partial
    · intro y
      gapply cpure _




def genTwoBetweens3: CorrectGen (fun (v: Nat × Nat) => ∃ x, 2 ≤ x ∧ ∃ y,  x ≤ 6 ∧ 2 ≤ y ∧ y ≤ 100 ∧ v = (x,y)) := by
  hoist
  apply (cbind _ _)
  · gapply (cbetween_partial)
  · intro x
    apply (cbind _ _)
    · gapply cbetween_partial
    · intro y
      gapply cpure _
