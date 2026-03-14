import Palamedes.Synthesizer

open Gen CorrectGen

namespace TrueFold

@[simp]
def isTrueFold (xs : List α) : Bool :=
  List.fold (fun _ b => b) true xs

def genTrueFold : Gen (List Nat) := by
  generator_search (fun xs => isTrueFold xs = true)

end TrueFold
