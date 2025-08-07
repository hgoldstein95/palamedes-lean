import Palamedes.Synthesizer

open Gen CorrectGen

namespace AVL

@[simp]
def isBST (t : Tree Nat) : Nat × Nat →  Bool := fun (lo, hi) =>
  match t with
  | .leaf => true
  | .node l x r =>
    (lo <= x && x <= hi) &&
    isBST l ⟨lo, x - 1⟩ &&
    isBST r ⟨x + 1, hi⟩

@[simp]
def isBalanced (t : Tree Nat) (height : Nat) : Bool :=
  match t with
  | .leaf => height <= 1
  | .node l _ r =>
    height > 0 &&
    isBalanced l (height - 1) &&
    isBalanced r (height - 1)

@[simp]
def isAVL (height lo hi : Nat) (t : Tree Nat) : Bool :=
  isBalanced t height && isBST t (lo, hi)

def genAVL (height lo hi : Nat) : Gen (Tree Nat) := by
  generator_search (fun t => isAVL height lo hi t = true) allow_partial

end AVL
