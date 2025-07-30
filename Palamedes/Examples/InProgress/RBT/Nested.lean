import Palamedes.Synthesizer
import Palamedes.Data.Color

open Gen CorrectGen

namespace RBT

@[simp]
def rrAux : Tree (Color × α) → Bool → Bool := λ t isRedChild =>
 match t with
 | .leaf => true
 | .node l (.red, _) r => !isRedChild && rrAux l true && rrAux r true
 | .node l (.black, _) r => rrAux l false && rrAux r false

@[simp]
def rr : Tree (Color × α) → Bool := λ t => rrAux t false

@[simp]
def bh : Tree (Color × α) → Nat → Bool := λ t height =>
 match t with
 | .leaf => height == 1
 | .node l (.red, _) r => bh l height && bh r height
 | .node l (.black, _) r =>
    height > 0 &&
    bh l (height - 1) &&
    bh r (height - 1)

@[simp]
def isBST : Tree (α × Nat) → (Nat × Nat) → Bool := λ t ⟨lo, hi⟩ =>
  match t with
  | .leaf => true
  | .node l (_, x) r =>
    (lo <= x && x <= hi) &&
    isBST l ⟨lo, x - 1⟩ &&
    isBST r ⟨x + 1, hi⟩

set_option palamedes.debug true

def genRBT (height lo hi : Nat) : Gen (Tree (Color × Nat)) := by
  -- generator_search (fun t => rr t = true ∧ bh t height = true ∧ isBST t (lo, hi) = true)
  -- let cg : CorrectGen (fun t => r  br t = true ∧ bh t height = true ∧ isBST t (lo, hi) = true) := by
  --   apply convert (by
  --     funext
  --     simp_predicate
  --     rw [← Tree.merge_accuM]; apply and_congr
  --     . sorry
  --     . rw [← Tree.merge_accuM]; apply and_congr
  --       . conv => rhs; lhs; apply congrFun; apply (Tree.coerce_to_fold (by aesop) (by intros; simp_all; rflm))
  --         sorry
  --       . sorry
  --     -- repeat'
  --     --   (first
  --     --     | rw [← Tree.merge_accuM]; apply and_congr
  --     --     | (first
  --     --         | conv => rhs; lhs; apply (Tree.coerce_to_fold (by aesop) (by intros; simp_all; rflm))
  --     --         | conv => rhs; lhs; apply congrFun; apply (Tree.coerce_to_fold (by aesop) (by intros; simp_all; rflm))
  --     --         | skip
  --     --        first
  --     --         | rw [← Tree.fold_accu_Option_true]; (try aesop); done
  --     --         | rw [← Tree.fold_accu_Option_function]; (try aesop); done
  --     --         | rw [← Tree.fold_accu_Option_function_true];
  --     --           (try intros; simp only [bind, Option.bind, pure, Option.some_inj, ← Bool.eq_iff_iff]; aesop); done
  --     --         | rw [← Tree.fold_accu_Option_basic]; (try aesop); done))
  --     ) (Tree.s_unfold _)
  --   all_goals sorry
  --   -- cgenerator_search
  -- let g : Gen (Tree (Color × ℕ)) := by
  --   optimize_gen cg.val
  -- let _ : support cg.val = support g := by
  --   optimality
  -- let _ : Gen.total g := by
  --   totality
  -- exact g
  sorry

end RBT
