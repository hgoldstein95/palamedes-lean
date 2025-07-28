import Palamedes.Gen
import Palamedes.CorrectGen
import Palamedes.Total

section TypeDef

inductive Color where
  | red
  | black
deriving DecidableEq

end TypeDef

namespace Gen

@[irreducible]
def arbColor : Gen Color := pick (pure .red) (pure .black)

@[simp]
def red : Gen Color := pure .red

@[simp]
def black : Gen Color := pure .black

@[simp]
theorem support_arbColor :
    support arbColor = fun _ => True := by
    funext x; cases x <;> simp_all [arbColor]

namespace CorrectGen

@[reducible]
def s_arbColor : @CorrectGen Color (fun _ => True) :=
  Subtype.mk arbColor <| by
    funext v
    simp

@[reducible]
def s_black : @CorrectGen Color (fun c => ¬c = .red) :=
  Subtype.mk black <| by
    funext v
    cases v <;> aesop

@[reducible]
def s_red : @CorrectGen Color (fun c => ¬c = .black) :=
  Subtype.mk red <| by
    funext v
    cases v <;> aesop

@[reducible]
def s_caseColor
    {Q : α → Prop}
    {P : α → Color → Prop}
    (c: Color)
    (h : ∀ {a}, P a c = Q a)
    (gr : CorrectGen (fun a => P a .red))
    (gb : CorrectGen (fun a => P a .black)) :
    CorrectGen Q :=
  Subtype.mk (if c = .red then gr.val else gb.val) <| by
    match c with
    | .red => simp [gr.property, h]
    | .black => simp [gb.property, h]

end CorrectGen

namespace Total

@[simp, aesop safe (rule_sets := [totality])]
theorem total_arbColor : total (arbColor : Gen Color) := by
  simp [arbColor]

@[simp, aesop safe (rule_sets := [totality])]
theorem total_red : total (red : Gen Color) := by
  simp [red]

@[simp, aesop safe (rule_sets := [totality])]
theorem total_black : total (black : Gen Color) := by
  simp [black]

end Total

end Gen
