import Palamedes.Synthesizer

open Gen CorrectGen

namespace AllTwos

@[simp]
def isAllTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && isAllTwos xs

def genAllTwos : Gen (List Nat) := by
  generator_search (fun xs => isAllTwos xs)

end AllTwos
