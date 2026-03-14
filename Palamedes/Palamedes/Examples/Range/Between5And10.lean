import Palamedes.Synthesizer

open Gen CorrectGen

def genBetween5And10 : Gen Nat := by
  generator_search (fun n => 5 ≤ n ∧ n ≤ 10)
