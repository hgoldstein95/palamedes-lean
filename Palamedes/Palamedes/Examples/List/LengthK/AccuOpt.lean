import Palamedes.Synthesizer

open Gen CorrectGen

namespace LengthKAccuOpt

@[simp]
def lengthAccuOpt (xs : List α) : Option Nat :=
  List.accuM
    (fun _ _ => ())
    (fun _ b _ => some (b + 1))
    (fun _ => some 0)
    xs
    ()

def genLengthKAccuOpt {k : Nat} : Gen (List Nat) := by
  generator_search (fun xs => lengthAccuOpt xs = some k)

end LengthKAccuOpt
