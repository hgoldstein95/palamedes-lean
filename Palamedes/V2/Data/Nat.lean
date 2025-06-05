import Palamedes.V2.Gen
import Palamedes.V2.CorrectGen
import Palamedes.V2.Total

namespace Gen

@[irreducible]
def arbNat : Gen Nat := indexed go
  where
    go : Nat → Gen (Option Nat)
      | 0 => pure none
      | n + 1 => pick (pure (some 0)) (.map (1 + .) <$> go n)

def gt (lo : Nat) : Gen Nat := (lo + 1 + · ) <$> arbNat

def choose (lo hi : Nat) (h : lo ≤ hi := by simp) : Gen Nat :=
  if h' : lo = hi then pure lo else pick (pure lo) (choose (lo + 1) hi (by omega))

namespace Gen

@[simp]
theorem support_arbNat :
    support arbNat = fun _ => True := by
  simp [arbNat, arbNat.go]
  funext v
  induction v with
  | zero => simp; exists 1; simp [arbNat, arbNat.go]
  | succ n ih =>
    simp_all
    have ⟨n', hn'⟩ := ih
    exists n' + 1
    simp [arbNat, arbNat.go]
    exists some n
    simp +arith [hn']

@[simp]
theorem support_gt :
    support (gt lo) = fun a => lo < a := by
  simp [gt]
  funext a
  simp
  apply Iff.intro
  . omega
  . intro h
    induction h with
    | refl => simp
    | step a ih =>
      have ⟨x, hx⟩ := ih
      exists x + 1
      omega

@[simp]
theorem support_choose :
    support (choose lo hi h) = fun a => lo ≤ a ∧ a ≤ hi := by
  generalize hn : hi - lo = n
  funext v
  induction n generalizing lo hi v with
  | zero =>
    unfold choose
    split <;> simp <;> omega
  | succ n' ih =>
    unfold choose
    split
    . simp
      omega
    . simp
      apply Iff.intro
      . intro hv
        cases hv with
        | inl hv => simp_all
        | inr hv =>
          have h : hi - (lo + 1) = n' := by omega
          rw [ih h] at hv
          omega
      . intro hbw
        by_cases v = lo
        . left; assumption
        . right
          rw [ih _] <;> omega

@[simp]
def support_Nat_rec
    {gz : (n = 0) → Gen α}
    {gs : (n' : Nat) → (n = n' + 1) → Gen α} :
    support (Nat.rec
            (motive := fun x => (n = x) → Gen α)
            (fun h => gz h)
            (fun a _ b => gs a b)
            n
            rfl) =
    (fun a =>
      (∃ h : n = 0, a ∈ 〚gz h〛) ∨
      (∃ (n' : Nat) (h : n = n' + 1), a ∈ 〚gs n' h〛)) := by
  funext
  simp
  apply Iff.intro
  . intro h
    cases n <;> aesop
  . intro h
    cases h <;> aesop

end Gen

namespace CorrectGen

@[reducible]
def carbNat : @CorrectGen Nat (λ _ => True) :=
  Subtype.mk arbNat <| by
    funext v
    simp

@[reducible]
def caseNat
    (n : Nat)
    (gz : (n = 0) → @CorrectGen α P)
    (gs : (n' : Nat) → (n = n' + 1) → @CorrectGen α P) :
    @CorrectGen α P :=
    Subtype.mk
      (Nat.rec
        (motive := fun x => (n = x) → Gen α)
        (fun h => (gz h).val)
        (fun a _ b => (gs a b).val)
        n
        rfl) <| by
    match n with
    | 0 => exact (gz _).property
    | n' + 1 => exact (gs _ _).property

@[reducible]
def cbetween
    {lo hi : Nat}
    (h : lo ≤ hi) :
    CorrectGen (λ v => lo ≤ v ∧ v ≤ hi) :=
  Subtype.mk (choose lo hi h) <| by
    funext v
    simp

@[reducible]
def cbetween_partial
    {lo hi : Nat} :
    CorrectGen (λ v => lo ≤ v ∧ v ≤ hi) :=
  Subtype.mk (assume (lo ≤ hi) (λ h => choose lo hi (by simp_all only [decide_eq_true_eq]))) <| by
    funext v
    simp
    exact Nat.le_trans

@[reducible]
def cgt
    {lo : Nat} :
    CorrectGen (λ v => lo < v) :=
  Subtype.mk (gt lo) <| by
    simp

end CorrectGen

namespace Total

@[simp]
def total_arbNat : total arbNat := by
  simp [arbNat]
  apply total_indexed
  intro n
  induction n <;> simp [arbNat.go, *]

@[simp]
def total_Nat_rec
    {gz : (n = 0) → Gen α}
    {gs : (n' : Nat) → (n = n' + 1) → Gen α}
    (hz : ∀ h, total (gz h))
    (hs : ∀ n' gn', total (gs n' gn')) :
    total (Nat.rec
          (motive := fun x => (n = x) → Gen α)
          (fun h => gz h)
          (fun a _ b => gs a b)
          n
          rfl)
  := by
  cases n
  case zero => exact hz rfl
  case succ n' => simp_all only

@[simp]
def total_choose : total (choose lo hi h) := by
  generalize hn : hi - lo = n
  induction n generalizing lo hi h with
  | zero =>
    unfold choose
    have : lo = hi := by omega
    simp [this]
  | succ n' ih =>
    unfold choose
    split
    . simp
    . apply total_pick
      . simp
      . apply ih
        omega

@[simp]
def total_gt : total (gt lo) := by simp [gt]

end Total

end Gen
