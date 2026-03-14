import Palamedes.Synthesizer

open Gen CorrectGen

def genEq2' : Gen Nat := by
  generator_search (2 = ·)
