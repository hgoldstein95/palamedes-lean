import Palamedes.Synthesizer

open Gen CorrectGen

namespace LengthK

def genLengthK {k : Nat} : Gen (List Nat) := by
  generator_search (fun xs => List.length xs = k)

end LengthK
