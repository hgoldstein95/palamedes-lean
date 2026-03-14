import Palamedes.Synthesizer

open Gen CorrectGen

namespace AllTwosTree

@[simp]
def isAllTwos : Tree Nat → Bool
  | .leaf => true
  | .node l x r => x = 2 && isAllTwos l && isAllTwos r

def genAllTwos : Gen (Tree Nat) := by
  generator_search (fun t => isAllTwos t)

end AllTwosTree
