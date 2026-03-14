import Palamedes.Synthesizer

open Gen CorrectGen

namespace LengthKAllTwos

@[simp]
def isAllTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && isAllTwos xs

@[simp]
def isLengthKAllTwos (k : Nat) (xs : List Nat) : Bool :=
  xs.length == k && isAllTwos xs

@[simp]
def genLengthKAllTwos (k : Nat) : Gen (List Nat) := by
  generator_search (fun xs => isLengthKAllTwos k xs = true)

end LengthKAllTwos
