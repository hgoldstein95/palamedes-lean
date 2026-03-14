import Palamedes.Synthesizer

open Gen CorrectGen

namespace AllTwosEvenLen

@[simp]
def isAllTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && isAllTwos xs

@[simp]
def isEvenLen : List α → Bool
  | [] => true
  | _ :: xs => !(isEvenLen xs)

@[simp]
def isAllTwosEvenLen (xs : List Nat) : Bool :=
  isAllTwos xs && isEvenLen xs

def genAllTwosEvenLen : Gen (List Nat) := by
  generator_search (fun xs => isAllTwosEvenLen xs = true)

end AllTwosEvenLen
