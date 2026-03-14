import Palamedes.Synthesizer

open Gen CorrectGen

def genThreePlusOne : Gen Nat := by
  generator_search (fun b => ∃ a, a = 3 ∧ b = a + 1)
