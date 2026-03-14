import Palamedes.Synthesizer

open Gen CorrectGen

namespace LengthKFold

@[simp]
def lengthFold (xs : List α) : Nat :=
  List.fold (fun _ b => b + 1) 0 xs

def genLengthKFold {k : Nat} : Gen (List Nat) := by
  generator_search (fun xs => lengthFold xs = k)

end LengthKFold
