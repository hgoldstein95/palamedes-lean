import Palamedes.Synthesizer

open Gen CorrectGen

namespace AllEvens

@[simp]
def isAllEvens : List Nat → Bool
  | [] => true
  | x :: xs => x % 2 = 0 && isAllEvens xs

def genAllEvens : Gen (List Nat) := by
  generator_search (fun xs => isAllEvens xs)

end AllEvens
