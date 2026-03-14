import Palamedes.Synthesizer

open Gen CorrectGen

namespace TrueAccuOpt

@[simp]
def isTrueAccuOpt (xs : List α) : Option Unit :=
  List.accuM
      (fun _ _ => ())
      (fun _ _ _ => guard true)
      (fun _ => some ())
      xs
      ()

def genTrueAccuOpt : Gen (List Nat) := by
  generator_search (fun xs => isTrueAccuOpt xs = some ())

end TrueAccuOpt
