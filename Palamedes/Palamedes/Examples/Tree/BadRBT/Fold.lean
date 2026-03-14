import Palamedes.Synthesizer
import Palamedes.Sample

open Gen CorrectGen

namespace RBTFold

@[simp]
def isRRFold (t : Tree (Color × α)) : Bool :=
  Tree.fold
    (fun bl c br isRedChild => if c.fst == .red then !isRedChild && bl true && br true else bl false && br false)
    (fun _ => true)
    t
    false

@[simp]
def isBHFold (t : Tree (Color × α)) (height : Nat) : Bool :=
  Tree.fold
    (fun bl c br h => if c.fst == .red then bl h && br h else h >= 0 && bl (h - 1) && br (h - 1))
    (fun h => h == 0)
    t
    height

set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

@[simp]
def isRBTFold (height : Nat) (t : Tree (Color × Nat)) : Bool :=
  isBHFold t height = true ∧ isRRFold t = true

def genRBTFold (height : Nat) : Gen (Tree (Color × Nat)) := by
  generator_search (fun t => isRBTFold height t = true)

end RBTFold
