import Palamedes.Synthesizer

open Gen CorrectGen

namespace AllTwosAccuOpt

@[simp]
def isAllTwosAccuOpt (xs : List Nat) : Option Unit :=
  List.accuM
      (fun _ _ => ())
      (fun x _ _ => guard (x == 2))
      (fun _ => some ())
      xs
      ()

def genAllTwosAccuOpt : Gen (List Nat) := by
  generator_search (fun xs => isAllTwosAccuOpt xs = some ())

end AllTwosAccuOpt
