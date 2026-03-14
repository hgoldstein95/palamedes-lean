import Palamedes.Synthesizer

open Gen CorrectGen

namespace AllEvensFold

@[simp]
def isAllEvensFold (xs : List Nat) : Bool :=
  List.fold (fun x b => x % 2 == 0 && b) true xs

def genAllEvensFold : Gen (List Nat) := by
  generator_search (fun xs => isAllEvensFold xs = true)

end AllEvensFold
