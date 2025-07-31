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

def Tuple.unfold (a : Gen α) (b : Gen β) : Gen (α × β) :=
  .bind a (fun a => .bind b (fun b => .ret (a, b)))

theorem Tuple.support_unfold_congr {α β : Type} {a a' : Gen α} {b b' : Gen β}
    {ha : support a = support a' }
    {hb : support b = support b' } :
    support (Tuple.unfold a b) = support (Tuple.unfold a' b') := by
  unfold Tuple.unfold
  simp [support]
  aesop

end CorrectGen

end Gen
