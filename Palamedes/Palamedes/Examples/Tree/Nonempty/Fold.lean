import Palamedes.Synthesizer

open Gen CorrectGen

namespace NonemptyFold

def isNonemptyFold (t : Tree α) : Bool :=
  Tree.fold (fun _ _ _ => true) false t

def genNonemptyFold : Gen (Tree Nat) := by
  generator_search (fun t => isNonemptyFold t = true)

end NonemptyFold
