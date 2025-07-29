import Palamedes.Synthesizer

open Gen CorrectGen

namespace RBTFold

@[simp]
def rrFold (t : Tree (Color × α)) : Bool :=
  Tree.fold
    (fun bl c br isRedChild =>
      if c.fst == .red then !isRedChild && bl true && br true else bl false && br false)
    (fun _ => true)
    t
    false

@[simp]
def bhFold (t : Tree (Color × α)) (height : Nat) : Bool :=
  Tree.fold
    (fun bl c br h =>
      if c.fst == .red then bl h && br h else h > 0 && bl (h - 1) && br (h - 1))
    (fun _ => true)
    t
    height

@[simp]
def isBSTFold (lo hi : Nat) (t : Tree Nat) : Bool :=
  Tree.fold
        (fun bl x br s =>
          match s with
          | (sl, sr) => (decide (sl ≤ x) && decide (x ≤ sr)) && bl (sl, x - 1) && br (x + 1, sr))
        (fun _ => true) t (lo, hi)

def genBSTFold (lo hi : Nat) : Gen (Tree Nat) := by
  generator_search (fun t => isBSTFold lo hi t = true)

set_option palamedes.debug true

def genRRFold : Gen (Tree (Color × Nat)) := by
  -- generator_search (fun t => rrFold t = true)
  let cg : CorrectGen (fun t => rrFold t = true) := by
    (goal_is_eq_or_and; apply convert (by
      funext
      simp_predicate
      rw [← Tree.fold_accu_cond_bool]
      simp
      aesop
    ) (Tree.s_unfold _))
    sorry
  let g : Gen (Tree (Color × ℕ)) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
  let _ : Gen.total g := by
    totality
  exact g

def genBHFold (height : Nat) : Gen (Tree (Color × Nat)) := by
  generator_search (fun t => bhFold t height = true)

/-
@[simp]
def isRBTFold (lo hi height : Nat) (t : Tree Color) : Bool :=
  rrFold t && bhFold t height
  --isBSTFold lo hi t -/

end RBTFold
