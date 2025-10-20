
import Aesop

inductive WeightedOr (l : Nat) (a : Prop) (r : Nat) (b : Prop) : Prop where
  | inl (h : a) : WeightedOr l a r b
  | inr (h : b) : WeightedOr l a r b

theorem WeightedOr.elim {c : Prop} (h : WeightedOr l a r b) (left : a → c) (right : b → c) : c :=
  match h with
  | WeightedOr.inl h => left h
  | WeightedOr.inr h => right h
@[symm] theorem WeightedOr.symm : WeightedOr l a r b → WeightedOr r b l a := .rec .inr .inl
theorem WeightedOr.comm : WeightedOr l a r b ↔ WeightedOr r b l a := Iff.intro WeightedOr.symm WeightedOr.symm
@[simp] theorem weighted_or_comm : WeightedOr l a r b ↔ WeightedOr r b l a := WeightedOr.comm
theorem WeightedOr.imp (f : a → c) (g : b → d) (h : WeightedOr l a r b) :
  WeightedOr l c r d := h.elim (inl ∘ f) (inr ∘ g)
theorem WeightedOr.imp_left (f : a → b) : a ∨ c → b ∨ c := .imp f id
theorem WeightedOr.imp_right (f : b → c) : a ∨ b → a ∨ c := .imp id f

theorem weighted_or_iff_right_of_imp (ha : a → b) : (WeightedOr l a r b) ↔ b :=
  Iff.intro (WeightedOr.rec ha id) .inr
theorem weighted_or_iff_left_of_imp  (hb : b → a) : (WeightedOr l a r b) ↔ a  :=
  Iff.intro (WeightedOr.rec id hb) .inl

@[simp] theorem weighted_or_iff_left_iff_imp  : (WeightedOr l a r b ↔ a) ↔ (b → a) :=
  Iff.intro (·.mp ∘ WeightedOr.inr) weighted_or_iff_left_of_imp
@[simp] theorem weighted_or_iff_right_iff_imp : (WeightedOr l a r b ↔ b) ↔ (a → b) :=
  by rw [weighted_or_comm, weighted_or_iff_left_iff_imp]
@[simp] theorem iff_weighted_or_self {a b : Prop} : (b ↔ WeightedOr l a r b) ↔ (a → b) :=
  propext (@Iff.comm _ b) ▸ @weighted_or_iff_right_iff_imp l a r b
@[simp] theorem iff_self_weighted_or {a b : Prop} : (a ↔ WeightedOr l a r b) ↔ (b → a) :=
  propext (@Iff.comm _ a) ▸ @weighted_or_iff_left_iff_imp l a r b

@[simp] theorem weighted_or_true (p : Prop) : (WeightedOr l p r True) = True := eq_true (.inr trivial)
@[simp] theorem true_weighted_or (p : Prop) : (WeightedOr l True r p) = True := eq_true (.inl trivial)
@[simp] theorem weighted_or_false (p : Prop) : (WeightedOr l p r False) = p := propext ⟨fun (.inl h) => h, .inl⟩
@[simp] theorem false_weighted_or (p : Prop) : (WeightedOr l False r p) = p := propext ⟨fun (.inr h) => h, .inr⟩
