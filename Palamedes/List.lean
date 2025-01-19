import Palamedes.Free
import Palamedes.Support

inductive ListF (α β : Type) where
  | nil : ListF α β
  | cons : (a : α) → (b : β) → ListF α β

def List.accu
    {α β σ : Type}
    (st : α → σ → σ)
    (f : α → β → σ → β)
    (z : σ → β)
    (xs : List α)
    (s : σ) :
    β :=
  match xs with
  | [] => z s
  | x :: xs => f x (List.accu st f z xs (st x s)) s

def List.accuM
    [Monad m]
    {α β σ : Type}
    (st : α → σ → σ)
    (f : α → β → σ → m β)
    (z : σ → m β)
    (xs : List α)
    (s : σ) :
    m β :=
  match xs with
  | [] => z s
  | x :: xs => do f x (← List.accuM st f z xs (st x s)) s

@[simp]
def support_unfoldr (P : β → ListF α β → Prop) (b : β) (xs : List α) : Prop :=
  match xs with
  | [] => P b .nil
  | x :: xs => ∃ b', P b (.cons x b') ∧ support_unfoldr P b' xs

def unfoldr' (n : Nat) (f : β → Gen (ListF α β)) (b : β) : Gen (Option (List α)) :=
  match n with
  | 0 => pure none
  | n + 1 => do
    match (← f b) with
    | .nil => pure (some [])
    | .cons x b' => .map (x :: .) <$> unfoldr' n f b'

theorem support_unfoldr' :
    support (.sized (λ n => unfoldr' n f b)) = support_unfoldr (λ b' => support (f b')) b := by
  funext xs
  induction xs generalizing b with
  | nil =>
    simp_all
    apply Iff.intro
    . intro ⟨n, h⟩
      match n with
      | 0 => simp_all
      | n + 1 =>
        simp_all [unfoldr', Functor.map, bind]
        have ⟨v', hv'1, hv'2⟩ := h
        match v' with
        | .nil => simp_all
        | .cons _ _ =>
          simp_all [unfoldr', bind]
          have ⟨v'', hv''⟩ := hv'2
          match v'' with
          | .none => simp_all
          | .some [] => simp_all [Option.map]
          | .some (x :: xs) => simp_all
    . intro h
      exists 1
      simp [unfoldr', bind]
      exists .nil
  | cons x xs ih =>
    simp_all
    apply Iff.intro
    . intro ⟨n, h⟩
      match n with
      | 0 => simp_all
      | n + 1 =>
        simp_all [unfoldr', Functor.map, bind]
        have ⟨v', hv'1, hv'2⟩ := h
        match v' with
        | .nil => simp_all
        | .cons _ b'' =>
          simp_all [unfoldr', bind]
          have ⟨v'', hv''⟩ := hv'2
          match v'' with
          | .none => simp_all
          | .some ys =>
            simp_all
            obtain ⟨hv'', rfl, rfl⟩ := hv''
            exists b''
            apply And.intro hv'1
            apply (@ih b'').mp
            exists n
    . intro ⟨b', hx, hxs⟩
      have ⟨n, h⟩ := ih.mpr hxs
      exists n + 1
      simp_all [unfoldr', bind]
      exists ListF.cons x b'
      simp_all [Functor.map]
      exists some xs
