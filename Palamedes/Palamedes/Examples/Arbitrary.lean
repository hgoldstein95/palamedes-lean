import Palamedes.Synthesizer

open Gen CorrectGen

def genUnit : Gen Unit := by
  generator_search (fun (_ : Unit) => True)

def genBool : Gen Bool := by
  generator_search (fun _ => True)

def genNat : Gen Nat := by
  generator_search (fun _ => True)
