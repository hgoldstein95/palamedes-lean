import Palamedes.Synthesizer

open Gen CorrectGen

@[simp]
def genReview : Gen Nat := indexed (fun n => pure (some n))

theorem supportReviewEmpty : ∀ n, ¬ (n ∈ 〚genReview〛) := by
  simp_all
  exists 1
