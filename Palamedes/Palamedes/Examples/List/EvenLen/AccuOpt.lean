import Palamedes.Synthesizer

open Gen CorrectGen

namespace EvenLenAccuOpt

@[simp]
def isEvenLenAccuOpt (xs : List α) : Option Bool :=
  List.accuM
      (fun _ _ => ())
      (fun _ b _ => some (!b))
      (fun _ => some true)
      xs
      ()

def genEvenLenAccuOpt : Gen (List Nat) := by
  generator_search (fun xs => isEvenLenAccuOpt xs = some true)

end EvenLenAccuOpt
