import Palamedes.Synthesizer

open Gen CorrectGen

namespace CompleteFold

@[simp]
def isMaxDepthFold (t : Tree Nat) (n : Nat) : Bool :=
  Tree.fold (fun bl _ br s => decide (s > 0) && bl (s - 1) && br (s - 1)) (fun _ => true) t n

def genMaxDepthFold (n : Nat) : Gen (Tree Nat) := by
  generator_search (fun t => isMaxDepthFold t n = true)

end CompleteFold
