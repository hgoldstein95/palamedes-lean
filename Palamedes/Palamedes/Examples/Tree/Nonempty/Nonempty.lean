import Palamedes.Synthesizer

open Gen CorrectGen

namespace Nonempty

@[simp]
def isNonempty : Tree α → Bool
  | .leaf => false
  | .node l _ r => true && isNonempty l && isNonempty r

def genNonempty : Gen (Tree Nat) := by
  generator_search (fun t => isNonempty t = true)

end Nonempty
