import Palamedes.V2.Gen
import Palamedes.V2.CorrectGen
import Palamedes.V2.Total

namespace Gen

def arbBool : Gen Bool := pick (pure true) (pure false)

namespace CorrectGen

@[reducible]
def carbBool : @CorrectGen Bool (fun _ => True) :=
  Subtype.mk arbBool (by simp [arbBool])

@[reducible]
def caseBool
    (b : Bool)
    (gt : (b = true) → @CorrectGen α P)
    (gf : (b = false) → @CorrectGen α P) :
    @CorrectGen α P :=
  Subtype.mk (if h : b then (gt h).val else (gf (by simp [h])).val) <| by
    split <;> rename_i h
    . simp [(gt h).property]
    . simp [(gf _).property]

end CorrectGen

namespace Total

@[simp]
def total_arbBool : total (arbBool : Gen Bool) := by
  simp [arbBool]

@[simp]
def total_Bool_rec (hf : total gf) (ht : total gt) : total (Bool.rec gf gt b) := by
  cases b <;> simp_all

end Total

end Gen
