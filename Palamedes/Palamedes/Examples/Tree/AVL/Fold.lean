import Palamedes.Synthesizer

open Gen CorrectGen

namespace AVLFold

@[simp]
def isAVLFold (height lo hi : Nat) (t : Tree Nat) : Bool :=
  Tree.fold
      (fun bl x br bounds =>
        match bounds with
        | (sl, sr) => decide (sl ≤ x) && decide (x ≤ sr)
          && bl (sl, x - 1) && br (x + 1, sr))
      (fun _ => true) t (lo, hi) = true
    ∧
    Tree.fold
      (fun bl _ br h => decide (h > 0) && bl (h - 1) && br (h - 1))
      (fun h => decide (h ≤ 1)) t height

set_option maxHeartbeats 1000000

def genAVLFold (height lo hi : Nat) : Gen (Tree Nat) := by
  generator_search (fun t => isAVLFold height lo hi t = true) allow_partial

end AVLFold
