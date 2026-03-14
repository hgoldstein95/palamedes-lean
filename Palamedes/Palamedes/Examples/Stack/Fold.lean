import Palamedes.Synthesizer

open Gen CorrectGen

namespace GoodStackFold

@[simp]
def isGoodNat (n : Nat) : Bool :=
  n == 0 || n == 1

@[simp]
def isGoodAtom : Atom → Bool
  | .atm n _ => isGoodNat n

def isGoodStackFold (s : Stack) (n : Nat) : Bool :=
  Stack.fold (fun i => i == 0) (fun x acc i => isGoodAtom x && acc (i - 1)) (fun pc acc i => isGoodAtom pc && acc (i - 1)) s n

def genGoodStackFold (n : Nat) : Gen Stack := by
  generator_search (fun s => isGoodStackFold s n = true)

end GoodStackFold
