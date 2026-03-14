import Palamedes.Synthesizer

open Gen CorrectGen

namespace CompleteFold

@[simp]
def isCompleteFold (t : Tree Nat) (n : Nat) : Bool :=
  Tree.fold (fun bl _ br s => decide (s > 0) && bl (s - 1) && br (s - 1)) (fun s => s == 0) t n

def genCompleteFold (n : Nat) : Gen (Tree Nat) := by
  generator_search (fun t => isCompleteFold t n = true)

end CompleteFold
