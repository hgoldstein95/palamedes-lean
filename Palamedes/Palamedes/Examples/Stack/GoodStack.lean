import Palamedes.Synthesizer

open Gen CorrectGen

namespace GoodStack

@[simp]
def isGoodNat (n : Nat) : Bool :=
  n == 0 || n == 1

@[simp]
def isGoodAtom : Atom → Bool
  | .atm n _ => isGoodNat n

@[simp]
def isGoodStack (s : Stack) (n : Nat) : Bool :=
  match s with
  | .mty => n == 0
  | .cons x s' => (n > 0 && isGoodAtom x) && isGoodStack s' (n - 1)
  | .ret_cons pc s' => (n > 0 && isGoodAtom pc) && isGoodStack s' (n - 1)

def genGoodStack (n : Nat) : Gen Stack := by
  generator_search (fun s => isGoodStack s n = true)

end GoodStack
