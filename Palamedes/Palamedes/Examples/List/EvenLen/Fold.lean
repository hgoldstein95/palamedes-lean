import Palamedes.Synthesizer

open Gen CorrectGen

namespace EvenLenFold

@[simp]
def isEvenLenFold (xs : List α) : Bool :=
  List.fold (fun _ b => !b) true xs

def genEvenLenFold : Gen (List Nat) := by
  generator_search (fun xs => isEvenLenFold xs = true)

end EvenLenFold
