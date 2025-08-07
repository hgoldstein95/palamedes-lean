import Palamedes.Synthesizer
import Palamedes.Data.Color

open Gen CorrectGen

namespace RBT

@[simp]
def rrAux : Tree (Color × α) → Bool → Bool := λ t isRedChild =>
 match t with
 | .leaf => true
 | .node l c r => if c.fst == .red then !isRedChild && rrAux l true && rrAux r true else rrAux l false && rrAux r false

@[simp]
def rr : Tree (Color × α) → Bool := λ t => rrAux t false

@[simp]
def bh : Tree (Color × α) → Nat → Bool := λ t height =>
 match t with
 | .leaf => height == 0
 | .node l c r => if c.fst == .red then bh l height && bh r height else height >= 0 && bh l (height - 1) && bh r (height - 1)

@[simp]
def isBST : Tree (α × Nat) → (Nat × Nat) → Bool := λ t ⟨lo, hi⟩ =>
  match t with
  | .leaf => true
  | .node l (_, x) r => (lo <= x && x <= hi) && isBST l ⟨lo, x - 1⟩ && isBST r ⟨x + 1, hi⟩

set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

def genRR : Gen (Tree (Color × Nat)) := by
  generator_search (fun t => rr t = true)

def genBH (height : Nat) : Gen (Tree (Color × Nat)) := by
  generator_search (fun t => bh t height = true)

def genIsBST (lo hi : Nat) : Gen (Tree (Color × Nat)) := by
  generator_search (fun t => isBST t (lo, hi) = true) allow_partial

def genRBT (height lo hi : Nat) : Gen (Tree (Color × Nat)) := by
  generator_search (fun t => rr t = true ∧ isBST t (lo, hi) = true ∧ bh t height = true) allow_partial

end RBT
