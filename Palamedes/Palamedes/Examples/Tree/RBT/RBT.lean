import Palamedes.Synthesizer
import Palamedes.Data.Color

open Gen CorrectGen

namespace RBT

@[simp]
def isRRAux : Tree (Color × α) → Bool → Bool := λ t isRedChild =>
 match t with
 | .leaf => true
 | .node l c r => if c.fst == .red then !isRedChild && isRRAux l true && isRRAux r true else isRRAux l false && isRRAux r false

@[simp]
def isRR : Tree (Color × α) → Bool := λ t => isRRAux t false

@[simp]
def isBH : Tree (Color × α) → Nat → Bool := λ t height =>
 match t with
 | .leaf => height == 0
 | .node l c r => if c.fst == .red then isBH l height && isBH r height else height >= 0 && isBH l (height - 1) && isBH r (height - 1)

@[simp]
def isBST : Tree (α × Nat) → (Nat × Nat) → Bool := λ t ⟨lo, hi⟩ =>
  match t with
  | .leaf => true
  | .node l (_, x) r => (lo <= x && x <= hi) && isBST l ⟨lo, x - 1⟩ && isBST r ⟨x + 1, hi⟩

set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

@[simp]
def isRBT : Tree (Color × Nat) → Nat → Nat → Nat → Bool := λ t height lo hi =>
  isRR t = true ∧ isBST t (lo, hi) = true ∧ isBH t height = true

def genRBT (height lo hi : Nat) : Gen (Tree (Color × Nat)) := by
  generator_search (fun t => isRBT t height lo hi) allow_partial

end RBT
