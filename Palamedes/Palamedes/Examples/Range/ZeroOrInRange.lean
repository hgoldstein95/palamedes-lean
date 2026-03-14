import Palamedes.Synthesizer

open Gen CorrectGen

def genZeroOrInRange (lo hi : Nat) : Gen Nat := by
  generator_search fun n => n = 0 ∨ (lo ≤ n ∧ n ≤ hi)
