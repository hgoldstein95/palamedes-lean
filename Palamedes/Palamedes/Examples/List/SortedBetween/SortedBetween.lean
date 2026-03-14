import Palamedes.Synthesizer

open Gen CorrectGen

namespace SortedBetween

@[simp]
def isSortedBetween (xs : List Nat) : Nat × Nat → Bool := fun (lo, hi) =>
  match xs with
  | [] => true
  | x :: xs' => (lo <= x && x <= hi) && isSortedBetween xs' (x, hi)

def genSortedBetween (lo hi : Nat) : Gen (List Nat) := by
  generator_search (fun xs => isSortedBetween xs (lo, hi) = true)

end SortedBetween
