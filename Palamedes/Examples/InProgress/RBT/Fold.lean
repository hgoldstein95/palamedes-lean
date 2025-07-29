import Palamedes.Synthesizer

open Gen CorrectGen

namespace RBTFold

/-
Equivalent to
  Tree.fold
    (fun bl c br isRedChild =>
      if c.fst == .red then !isRedChild && bl true && br true else bl false && br false)
    (fun _ => true)
    t
    false
-/
@[simp]
def rrFold (t : Tree (Color × α)) : Bool :=
  Tree.fold
    (fun bl c br isRedChild =>
      if (fun c => c.fst == .red) c
        then (fun s => !s) isRedChild && bl ((fun _ _ => true) c isRedChild) && br ((fun _ _ => true) c isRedChild)
        else (fun _ => true) isRedChild && bl ((fun _ _ => false) c isRedChild) && br ((fun _ _ => false) c isRedChild))
    (fun _ => true)
    t
    false

/-
Equavalent to
  Tree.fold
    (fun bl c br h =>
      if c.fst == .red then bl h && br h else h > 0 && bl (h - 1) && br (h - 1))
    (fun h => h == 1)
    t
    height
-/
@[simp]
def bhFold (t : Tree (Color × α)) (height : Nat) : Bool :=
  Tree.fold
    (fun bl c br h =>
      if (fun c => c.fst == .red) c
        then (fun _ => true) h && bl ((fun _ h => h) c h) && br ((fun _ h => h) c h)
        else (fun h => h > 0) h && bl ((fun _ h => h - 1) c h) && br ((fun _ h => h - 1) c h))
    (fun h => h == 1)
    t
    height

@[simp]
def isBSTFold (lo hi : Nat) (t : Tree (Color × Nat)) : Bool :=
  Tree.fold
        (fun bl x br s =>
          match s with
          | (sl, sr) => (decide (sl ≤ x.snd) && decide (x.snd ≤ sr)) && bl (sl, x.snd - 1) && br (x.snd + 1, sr))
        (fun _ => true) t (lo, hi)

def genBSTFold (lo hi : Nat) : Gen (Tree (Color × Nat)) := by
  generator_search (fun t => isBSTFold lo hi t = true)

set_option palamedes.debug true
set_option maxHeartbeats 1000000
set_option maxRecDepth 800

def genRRFold : Gen (Tree (Color × Nat)) := by
  generator_search (fun t => rrFold t = true)

def genBHFold (height : Nat) : Gen (Tree (Color × Nat)) := by
  generator_search (fun t => bhFold t height = true)

@[simp]
def isRBTFold (lo hi height : Nat) (t : Tree (Color × Nat)) : Bool :=
  rrFold t && bhFold t height && isBSTFold lo hi t

end RBTFold
