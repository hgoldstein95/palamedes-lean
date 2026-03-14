import Palamedes.Synthesizer

open Gen CorrectGen

@[simp]
def isNotUniqueAux [BEq α] (xs : List α) (soFar : List α) :=
  match xs with
  | [] => false
  | x :: xs' => List.elem x soFar || isNotUniqueAux xs' (x :: soFar)

@[simp]
def isNotUnique [BEq α] (xs : List α) :=
  isNotUniqueAux xs []

def genNotUnique : Gen (List Nat) := by
  --- generator_search (fun xs => isNotUnique xs)
  sorry
