import Palamedes.Synthesizer

open Gen CorrectGen

namespace BST

@[simp]
def isBST : Tree Nat → (Nat × Nat) → Bool := fun t ⟨lo, hi⟩ =>
  match t with
  | .leaf => true
  | .node l x r =>
    (lo <= x && x <= hi) &&
    isBST l ⟨lo, x - 1⟩ &&
    isBST r ⟨x + 1, hi⟩

def genBST (lo hi : Nat) : Gen (Tree Nat) := by
  generator_search (fun t => isBST t (lo, hi) = true)

end BST
