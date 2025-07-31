import Palamedes.Synthesizer

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
    (fun bl c br h => if c.fst == .red then bl h && br h else h > 0 && bl (h - 1) && br (h - 1))
    (fun h => h == 1)
    t
    height

set_option palamedes.debug true
set_option maxHeartbeats 2000000
set_option maxRecDepth 800
set_option diagnostics true

@[simp]
def isBSTFold (lo hi : Nat) (t : Tree (α × Nat)) : Bool :=
  Tree.fold
        (fun bl x br s =>
          match s with
          | (sl, sr) => (decide (sl ≤ x.snd) && decide (x.snd ≤ sr)) && bl (sl, x.snd - 1) && br (x.snd + 1, sr))
        (fun _ => true) t (lo, hi)

def genBSTFold (lo hi : Nat) : Gen (Tree (Color × Nat)) := by
  generator_search (fun t => isBSTFold lo hi t = true) allow_partial

def genRRFold : Gen (Tree (Color × Nat)) := by
  generator_search (fun t => rrFold t = true)

def genBHFold (height : Nat) : Gen (Tree (Color × Nat)) := by
  generator_search (fun t => bhFold t height = true)

@[simp]
def isRBTFold (lo hi height : Nat) (t : Tree (Color × Nat)) : Bool :=
  isBSTFold lo hi t && rrFold t && bhFold t height

def genRBTFold (lo hi height : Nat) : Gen (Tree (Color × Nat)) := by
  generator_search (fun t => isRBTFold lo hi height t = true) allow_partial

end RBTFold
