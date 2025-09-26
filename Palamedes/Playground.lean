import Aesop



-- set_option trace.aesop true
-- example : (P → R) ∧ (Q → R) → P ∨ Q → R ∧ True := by
--   intro a a_1
--   --intros
--   --unfold
--   simp
--   obtain ⟨left, right⟩ := a
--   cases a_1
--   simp_all
--   simp_all

-- set_option trace.aesop true
-- example : ∃ x, x + 1 = 3 := by
--   refine Exists.intro ?x ?p
--   case p => exact rfl


---------------------------------------

set_option trace.aesop.debug true
example : ∃ x y, 0 < x ∧ x < y ∧ y < 3 := by
  sorry
  -- refine Exists.intro ?x ?p
  -- case p =>
  --   apply And.intro
  --   case right =>
  --     exact rfl
  --   simp
