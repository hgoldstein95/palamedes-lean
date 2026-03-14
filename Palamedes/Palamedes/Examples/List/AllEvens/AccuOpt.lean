import Palamedes.Synthesizer

open Gen CorrectGen

namespace AllEvensAccuOpt

@[simp]
def isAllEvensAccuOpt (xs : List Nat) : Option Unit :=
  List.accuM (fun _ _ => ()) (fun x _ _ => guard (x % 2 == 0)) (fun _ => some ()) xs ()

def genAllEvensAccuOpt : Gen (List Nat) := by
  generator_search (fun xs => isAllEvensAccuOpt xs = some ())

end AllEvensAccuOpt
