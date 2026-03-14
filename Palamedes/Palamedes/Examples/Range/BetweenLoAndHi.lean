import Palamedes.Synthesizer

open Gen CorrectGen

def genBetweenLoAndHi (lo hi : Nat) : Gen Nat := by
  generator_search (fun n => lo ≤ n ∧ n ≤ hi) allow_partial
