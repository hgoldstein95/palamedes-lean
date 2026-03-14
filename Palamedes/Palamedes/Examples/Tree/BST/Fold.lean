import Palamedes.Synthesizer

open Gen CorrectGen

namespace BSTFold

@[simp]
def isBSTFold (lo hi : Nat) (t : Tree Nat) : Bool :=
  Tree.fold
        (fun bl x br s =>
          match s with
          | (sl, sr) => (decide (sl ≤ x) && decide (x ≤ sr)) && bl (sl, x - 1) && br (x + 1, sr))
        (fun _ => true) t (lo, hi)

def genBSTFold (lo hi : Nat) : Gen (Tree Nat) := by
  generator_search (fun t  => isBSTFold lo hi t = true)

end BSTFold
