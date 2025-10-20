import Palamedes.Gen

def CorrectGen (P : α → Prop) := {g : Gen α // g.support = P}

namespace Gen

namespace CorrectGen

@[reducible]
def s_pure
    (a' : α) :
    CorrectGen (fun a => a = a') :=
  Subtype.mk (pure a') <| by
    simp

@[reducible]
def s_bind
    {P : α → Prop}
    {Q : α → β → Prop}
    (x : CorrectGen P)
    (f : (a : α) → CorrectGen (Q a)) :
    CorrectGen (fun b => ∃ a, P a ∧ Q a b) :=
  Subtype.mk (x.val >>= fun a => (f a).val) <| by
    funext b
    simp
    apply Iff.intro <;>
      (intro ⟨a, ha⟩;
       exists a
       simp_all [x.property, (f a).property])

@[reducible]
def s_pick
    {P Q : α → Prop}
    (l r : Nat)
    (x : CorrectGen P)
    (y : CorrectGen Q) :
    CorrectGen (fun a => WeightedOr l (P a) r (Q a)) :=
  Subtype.mk (pick l x.val r y.val) <| by
    simp [x.property, y.property]

@[reducible]
def convert
    (h : P = Q)
    (g : CorrectGen P) :
    CorrectGen Q :=
  Subtype.mk g.val <| by
    simp [h, g.property]

@[reducible]
def duncurry
    {F : α × β → Type u} :
    ((a : α) → (b : β) → F (a, b)) → (p : α × β) → F p :=
  fun f p => f p.1 p.2

end CorrectGen

end Gen
