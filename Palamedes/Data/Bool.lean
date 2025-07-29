import Palamedes.Gen
import Palamedes.CorrectGen
import Palamedes.Total

namespace Gen

def arbBool : Gen Bool := pick (pure true) (pure false)

def tru : Gen Bool := pure true
def fls : Gen Bool := pure false

namespace CorrectGen

@[reducible]
def s_arbBool : @CorrectGen Bool (fun _ => True) :=
  Subtype.mk arbBool (by simp [arbBool])

def s_true : @CorrectGen Bool (fun b => b = true) :=
  Subtype.mk tru (by simp [tru])

def s_false : @CorrectGen Bool (fun b => b = false) :=
  Subtype.mk fls (by simp [fls])

@[reducible]
def s_caseBool
    {Q : α → Prop}
    {P : α → Bool → Prop}
    (b : Bool)
    (h : ∀ {a}, P a b = Q a)
    (gt : CorrectGen (fun a => P a true))
    (gf : CorrectGen (fun a => P a false)) :
    CorrectGen Q :=
  Subtype.mk (if h : b then gt.val else gf.val) <| by
    match b with
    | true => simp [gt.property, h]
    | false => simp [gf.property, h]

end CorrectGen

namespace Total

@[simp, aesop safe (rule_sets := [totality])]
theorem total_arbBool : total (arbBool : Gen Bool) := by
  simp [arbBool]

@[simp, aesop safe (rule_sets := [totality])]
theorem total_tru : total (tru : Gen Bool) := by
  simp [tru]

@[simp, aesop safe (rule_sets := [totality])]
theorem total_fls : total (fls : Gen Bool) := by
  simp [fls]

@[simp, aesop safe (rule_sets := [totality])]
theorem total_Bool_rec (hf : total gf) (ht : total gt) : total (Bool.rec gf gt b) := by
  cases b <;> simp_all

end Total

end Gen
