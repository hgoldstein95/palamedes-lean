import Palamedes.Synthesizer

open Gen CorrectGen

namespace LengthKAllTwosFold

@[simp]
def isLengthKAllTwosFold (k : Nat) (xs : List Nat) :=
  List.fold (fun _ b => b + 1) 0 xs = k ∧ List.fold (fun x b => x == 2 && b) true xs

def genLengthKAllTwosFold (k : Nat) : Gen (List Nat) := by
  generator_search (fun xs => isLengthKAllTwosFold k xs = true)

end LengthKAllTwosFold
