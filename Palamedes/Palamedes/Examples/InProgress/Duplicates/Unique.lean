import Palamedes.Synthesizer

open Gen CorrectGen

@[simp]
def isUniqueAux [BEq α] (xs : List α) (soFar : List α) :=
  match xs with
  | [] => false
  | x :: xs' => List.elem x soFar && isUniqueAux xs' (x :: soFar)

@[simp]
def isUnique [BEq α] (xs : List α) :=
  isUniqueAux xs []

def getUnique : Gen (List Nat) := by
  --- generator_search (fun xs => isUnique xs)
  sorry
