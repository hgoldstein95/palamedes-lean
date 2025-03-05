import Palamedes.Free

@[simp]
def support : Gen α → α → Prop
  | .ret v' => (. = v')
  | .pick _ x y => λ v => support x v ∨ support y v
  | .choose lo hi _ => λ v => lo ≤ v ∧ v ≤ hi
  | .sized f => λ v => ∃ n, support (f n) (some v)
  | .bind x f => λ v => ∃ v', support x v' ∧ support (f v') v
  | .guardIn P _ f => λ v => ∃ h : P, support (f h) v

notation v " ∈ " "〚" g "〛" => support g v

abbrev CGen {α : Type} (P : α → Prop) :=
  {g : Gen α // ∀ v, support g v ↔ P v}

abbrev CompleteGen {α : Type} (P : α → Prop) :=
  {g : Gen α // ∀ v, P v → support g v}

abbrev SoundGen {α : Type} (P : α → Prop) :=
  {g : Gen α // ∀ v, support g v → P v}

class Arbitrary (α : Type) where
  arbitrary : @CGen α (λ _ => True)

instance : Arbitrary Unit where
  arbitrary := ⟨pure (), by simp⟩

theorem optPick_pick (x y : Gen α) : support (optPick w x y) = support (.pick w x y) := by
  generalize hn : genMeasure x + genMeasure y = n
  induction n generalizing x y
  case zero =>
    cases hx : x with
    | guardIn P _ f =>
      by_cases h : P
      . simp_all [optPick]
      . simp_all [optPick]
        funext v
        subst hx
        simp_all only [not_false_eq_true, eq_iff_iff, iff_or_self, forall_exists_index, forall_false]
    | _ =>
      cases hy : y with
      | guardIn Q _ g =>
        by_cases h' : Q
        . simp_all [optPick]
        . simp_all [optPick]
          funext x
          subst hy hx
          simp_all only [eq_iff_iff, iff_self_or, forall_exists_index, forall_false]
      | _ => simp_all [optPick]
  case succ m ih =>
    cases x with
    | guardIn P _ f =>
      by_cases h : P
      . simp_all [optPick]
        rw [← ih]
        conv at hn =>
          lhs
          rw [Nat.add_assoc]
          rw [Nat.add_comm]
        simp at hn
        exact hn
      . simp_all [optPick]
        funext v
        simp_all only [not_false_eq_true, eq_iff_iff, iff_or_self, forall_exists_index, forall_false]
    | _ =>
      cases hy : y with
      | guardIn Q _ g =>
        by_cases h' : Q
        . simp_all [optPick]
          conv at hn => lhs; rw [Nat.add_comm]
          simp_all
        . simp_all [optPick]
      | _ => simp_all [optPick]

instance : Arbitrary Bool where
  arbitrary := ⟨
    pick (pure true) (pure false),
    by simp [optPick_pick, pick]
  ⟩

def arbNat (fuel : Nat) : Gen (Option Nat) :=
  match fuel with
  | 0 => pure none
  | n + 1 =>
    pick (pure (some 0))
          (.map (1 + .) <$> arbNat n)

theorem optBind_bind : support (optBind x f) = support (.bind x f) := by
  funext v
  induction x generalizing v <;> simp_all [optBind]
  case bind x g ih1 ih2 =>
    apply Iff.intro
    . intro ⟨v', h, ⟨a, ha, hv'⟩⟩
      exists a
      apply (And.intro . hv')
      exists v'
    . intro h
      have ⟨v', ⟨a, ha1, ha2⟩, hv'⟩ := h
      exists a
      apply And.intro ha1
      exists v'
  case guardIn P _ g ih =>
    apply Iff.intro
    . intro ⟨v', a, ⟨ha1, ha2⟩⟩
      exists a
      apply (And.intro . ha2)
      exists v'
    . intro ⟨a, ⟨⟨v', hv'1⟩, hv'2⟩⟩
      simp_all only [exists_true_left]
      apply Exists.intro
      · apply And.intro
        on_goal 2 => exact hv'2
        · simp_all only

instance : Arbitrary Nat where
  arbitrary :=  ⟨
      Gen.sized arbNat,
      by
        intro v
        induction v with
        | zero => simp; exists 1; unfold arbNat; unfold pick; rw [optPick_pick]; simp
        | succ n ih =>
          simp_all
          have ⟨n', hn'⟩ := ih
          exists n' + 1
          unfold arbNat
          simp [pick, optPick_pick, Functor.map, optBind_bind]
          exists some n
          simp_arith
          assumption
    ⟩
