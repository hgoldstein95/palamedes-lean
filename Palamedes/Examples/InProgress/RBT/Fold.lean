import Palamedes.Synthesizer
import Palamedes.Sample

open Gen CorrectGen

namespace RBTFold

@[simp]
def rrFold (t : Tree (Color × α)) : Bool :=
  Tree.fold
    (fun bl c br isRedChild => if c.fst == .red then !isRedChild && bl true && br true else bl false && br false)
    (fun _ => true)
    t
    false

@[simp]
def bhFold (t : Tree (Color × α)) (height : Nat) : Bool :=
  Tree.fold
    (fun bl c br h => if c.fst == .red then bl h && br h else h >= 0 && bl (h - 1) && br (h - 1))
    (fun h => h == 0)
    t
    height

@[simp]
def isBSTFold (t : Tree (α × Nat)) : Nat × Nat -> Bool := fun (lo, hi) =>
  Tree.fold
        (fun bl x br s =>
          match s with
          | (sl, sr) => (decide (sl ≤ x.snd) && decide (x.snd ≤ sr)) && bl (sl, x.snd - 1) && br (x.snd + 1, sr))
        (fun _ => true) t (lo, hi)

set_option palamedes.debug true
set_option maxHeartbeats 3000000
set_option maxRecDepth 3000
set_option diagnostics true
set_option trace.debug true
set_option trace.profiler true
set_option trace.aesop.forward.debug true
set_option trace.aesop.stats true

/- def genBSTFold (lo hi : Nat) : Gen (Tree (Color × Nat)) := by
  generator_search (fun t => isBSTFold t (lo, hi) = true)

def genRRFold : Gen (Tree (Color × Nat)) := by
  generator_search (fun t => rrFold t = true)

def genBHFold (height : Nat)  : Gen (Tree (Color × Nat)) := by
  generator_search (fun t => bhFold t height = true)

@[simp]
def isRRBHFold (height : Nat) (t : Tree (Color × Nat)) : Bool :=
  bhFold t height = true ∧ rrFold t = true

def genRRBHFold (height : Nat) : Gen (Tree (Color × Nat)) := by
  generator_search (fun t => isRRBHFold height t = true)

@[simp]
def isRRBSTFold (lo hi : Nat) (t : Tree (Color × Nat)) : Bool :=
  isBSTFold t (lo, hi) = true ∧ rrFold t = true

def genRRBSTFold (lo hi : Nat) : Gen (Tree (Color × Nat)) := by
  generator_search (fun t => isRRBSTFold lo hi t = true) allow_partial

@[simp]
def isBHBSTFold (lo hi height : Nat) (t : Tree (Color × Nat)) : Bool :=
  isBSTFold t (lo, hi) = true ∧ bhFold t height = true

def genBHBSTFold (lo hi height : Nat) : Gen (Tree (Color × Nat)) := by
  generator_search (fun t => isBHBSTFold lo hi height t = true) allow_partial -/

@[simp]
def isRBTFold (height lo hi : Nat) (t : Tree (Color × Nat)) : Bool :=
  isBSTFold t (lo, hi) = true ∧ bhFold t height = true ∧ rrFold t = true

def genRBTFold (height lo hi : Nat) : Gen (Tree (Color × Nat)) := by
  -- generator_search (fun t => isRBTFold lo hi height t = true) allow_partial
  let cg : CorrectGen (fun t : Tree (Color × Nat) => isRBTFold height lo hi t = true) := by
    /- normalize_and_unfold
    repeat ((repeat apply duncurry); intro)
    goal_is_or; clear_unused_assumptions; apply s_caseBool (by nth_assumption 0) (by intros; rflm)
    . cgenerator_search?
    . cgenerator_search? -/
    cgenerator_search?
  let g : Gen (Tree (Color × ℕ)) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
  /- let _ : Gen.total g := by
    totality -/
  exact g

end RBTFold
