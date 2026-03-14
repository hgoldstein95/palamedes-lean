import Palamedes.Synthesizer

open Gen CorrectGen

def genGt5 : Gen Nat := by
  generator_search fun n => n > 5
