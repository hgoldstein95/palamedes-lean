import Palamedes.Synthesizer

open Gen CorrectGen

namespace IncreasingByOneTree

@[simp]
def isIncreasingByOneAux (t : Tree Nat) (prev : Nat) : Bool :=
  match t with
  | .leaf => true
  | .node l x r => x == prev + 1 && isIncreasingByOneAux l x && isIncreasingByOneAux r x

@[simp]
def isIncreasingByOne (t : Tree Nat) : Bool :=
  isIncreasingByOneAux t 0

def genIncreasingByOne : Gen (Tree Nat) := by
  generator_search (fun t => isIncreasingByOne t = true)

end IncreasingByOneTree
