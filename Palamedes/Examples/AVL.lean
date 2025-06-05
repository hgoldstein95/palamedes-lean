import Palamedes.Synth
import Palamedes.Sample
import Palamedes.Data.Tree
import Mathlib.Tactic.Convert

namespace AVL

#set_up_palamedes_simp

@[aesop simp (rule_sets := [palamedes])]
def isBST : Tree Nat → (Nat × Nat) → Bool := λ t (lo, hi) =>
  match t with
  | .leaf => true
  | .node l x r =>
    (lo <= x && x <= hi) &&
    isBST l (lo, x - 1) &&
    isBST r (x + 1, hi)

def genBST (lo hi : Nat) : CGen (λ v => isBST v (lo, hi)) := by
  --palamedes
  sorry

@[aesop simp (rule_sets := [palamedes])]
def isBalanced : Tree Nat → Nat → Bool := λ t height =>
  match t with
  | .leaf => height <= 1
  | .node l _ r =>
    height > 0 &&
    -- TODO: formerly we had to have `true` here; try to find a way to make that unnecessary
    isBalanced l (height - 1) &&
    isBalanced r (height - 1)

def genBalanced (height : Nat) : CGen (λ v => isBalanced v height) := by
  -- TODO: Get rid of this too
  -- conv => arg 1; intro v; apply Tree.coerce_to_accuM (by aesop) (by aesop)
  -- palamedes
  sorry

set_option maxHeartbeats 1000000

-- def genAVL
--     (height lo hi : Nat) :
--     CGen (λ t => isBalanced t height ∧ isBST t (lo, hi)) := by
--   conv =>
--     arg 1
--     intro t
--     lhs
--     apply Tree.coerce_to_accuM (by aesop) (by aesop)
--   conv =>
--     arg 1
--     intro t
--     rhs
--     apply Tree.coerce_to_accuM (by aesop) (by aesop)
--   simp [Tree.merge_accuM]
--   apply synth_accuTreeM
--   intro b s
--   simp [isBalanced, isBST]
--   apply synth_or
--   . exact ⟨.assume (s.fst ≤ 1) (λ _ => .ret TreeF.leaf), by simp⟩
--   . palamedes
