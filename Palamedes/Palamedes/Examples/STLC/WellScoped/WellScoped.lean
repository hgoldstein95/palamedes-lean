import Palamedes.Synthesizer

open Gen CorrectGen

namespace WellScoped

@[simp]
def isWellScoped (t : Term) (varCap : Nat) : Bool :=
  match t with
  | .unit => true
  | .var n => n < varCap
  | .abs _ t => isWellScoped t (varCap + 1)
  | .app t₁ t₂ => isWellScoped t₁ varCap && isWellScoped t₂ varCap

def genWellScoped : Gen Term := by
  generator_search (fun t => isWellScoped t 0 = true)

end WellScoped
