import Palamedes.Synthesizer

open Gen CorrectGen

namespace Nonempty

@[simp]
def isNonempty : Tree α → Bool
  | .leaf => false
  | .node l _ r => true && isNonempty l && isNonempty r

def genNonempty : Gen (Tree Nat) := by
  -- generator_search (fun t => isNonempty t = true)
  let cg : CorrectGen (fun t : Tree Nat => isNonempty t = true) := by
    (normalize_and_apply_unfold)
    ((repeat apply duncurry); intro)
    ((repeat apply duncurry); intro)
    (goal_is_or; clear_unused_assumptions; apply s_caseBool (by nth_assumption 0) (by intros; rflm))
    · (normalize_and_apply)
      · (apply s_arbNat)
      · ((repeat apply duncurry); intro)
        (normalize_and_apply)
    · (normalize_and_apply)
      · (normalize_and_apply)
      · (normalize_and_apply)
        · (apply s_arbNat)
        · ((repeat apply duncurry); intro)
          (normalize_and_apply)
          · (normalize_and_apply)
            · (normalize_and_apply)
            · (normalize_and_apply)
          · (normalize_and_apply)
  let g : Gen (Tree ℕ) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
  let _ : Gen.total g := by
    totality
  exact g

end Nonempty
