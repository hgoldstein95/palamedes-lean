import Palamedes.Synthesizer

open Gen CorrectGen

namespace AllTwosTreeFold

@[simp]
def isAllTwosFold (t : Tree Nat) : Bool :=
  Tree.fold (fun bl x br => x == 2 && bl && br) true t

def genAllTwosFold : Gen (Tree Nat) := by
  generator_search (fun t => isAllTwosFold t = true)

end AllTwosTreeFold
