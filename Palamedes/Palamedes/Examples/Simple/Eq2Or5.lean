import Palamedes.Synthesizer

open Gen CorrectGen

def genEq2Or5 : Gen Nat := by
  generator_search (fun a => a = 2 ∨ a = 5)
