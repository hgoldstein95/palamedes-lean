import Palamedes.Total
import Palamedes.CorrectGen
import Palamedes.Optimizer
import Palamedes.RuleSets

namespace Gen

namespace CorrectGen

@[reducible]
def s_arbTuple
    {P : α × β → Prop}
    (g : CorrectGen (fun (p : α × β) => ∃ (a : α) (b : β), P (a, b) ∧ p = (a, b))) :
    CorrectGen (fun (p : α × β) => P p) :=
  Subtype.mk g.val <| by
    funext (a, b)
    simp_all [g.property]

end CorrectGen

end Gen
