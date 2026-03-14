import Palamedes.Synthesizer

open Gen CorrectGen

namespace Complete

@[simp]
def isMaxDepth (t : Tree α) (n : Nat) : Bool :=
  match t with
  | .leaf => true
  | .node l _ r =>
    n > 0 &&
    isMaxDepth l (n - 1) &&
    isMaxDepth r (n - 1)

def genComplete (n : Nat) : Gen (Tree Nat) := by
  generator_search (fun t => isMaxDepth t n = true)

end Complete
