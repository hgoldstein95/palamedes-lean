import Palamedes.Synthesizer

open Gen CorrectGen

namespace EvenLen

@[simp]
def isEvenLen : List α → Bool
  | [] => true
  | _ :: xs => !(isEvenLen xs)

def genEvenLen : Gen (List Nat) := by
  generator_search (fun xs => isEvenLen xs = true)

end EvenLen
