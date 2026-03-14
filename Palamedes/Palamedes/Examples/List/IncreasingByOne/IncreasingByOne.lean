import Palamedes.Synthesizer

open Gen CorrectGen

namespace IncreasingByOneList

@[simp]
def isIncreasingByOneAux (xs : List Nat) (prev : Nat) : Bool :=
  match xs with
  | [] => true
  | x :: xs' => x == prev + 1 && isIncreasingByOneAux xs' x

@[simp]
def isIncreasingByOne (xs : List Nat) : Bool :=
  isIncreasingByOneAux xs 0

def genIncreasingByOneRec : Gen (List Nat) := by
  generator_search (fun xs => isIncreasingByOne xs = true)

end IncreasingByOneList
