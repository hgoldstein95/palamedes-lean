import Palamedes.V2.Synthesizer

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
  sorry


def genOneGtOther5: CorrectGen (λ (v : Nat × Nat × Nat) => ∃ x y z, x > y ∧ v = (x,y,z)) := by
  --exists_swap_2nd --works yay
  exists_swap_3rd
  sorry

-- def genOneGtOther : Gen (Nat × Nat) := by
--   generator_search (fun (v : Nat × Nat) => ∃ x y, x > 2 ∧ v = (x,y))

-- def genOneGtOther2 : Gen (Nat × Nat) := by
--   generator_search (fun (v : Nat × Nat) => ∃ x y, x > y ∧ v = (x,y))
