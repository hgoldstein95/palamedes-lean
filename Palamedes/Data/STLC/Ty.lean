import Palamedes.Support

-- TODO: contravariance?

/- Type definitions -/

inductive Ty : Type where
  | unit
  | arrow (τ₁ τ₂ : Ty)
  deriving DecidableEq, Repr

/- Base functor -/

inductive TyF (α : Type) where
  | unit : TyF α
  | arrow : (τ₁ : α) → (τ₂ : α) → TyF α

theorem TyF_or
    {α : Type}
    {P : Prop}
    {Q : α → α → Prop}
    {τ : TyF α} :
    TyF.rec P Q τ ↔ (P ∧ τ = .unit) ∨ (∃ b₁ b₂, τ = .arrow b₁ b₂ ∧ Q b₁ b₂) := by
  match τ with
  | .unit => simp
  | .arrow _ _ => aesop

/- Recursion schemes -/

def Ty.fold
    {α : Type}
    (f : α → α → α)
    (z : α)
    (τ : Ty) :
    α :=
  match τ with
  | .unit => z
  | .arrow τ₁ τ₂ => f (Ty.fold f z τ₁) (Ty.fold f z τ₂)

@[simp] theorem Ty.fold_unit : Ty.fold f z .unit = z := rfl
@[simp] theorem Ty.fold_arrow {τ₁ τ₂ : Ty} {f : α → α → α} {z} :
    Ty.fold f z (.arrow τ₁ τ₂) = f (Ty.fold f z τ₁) (Ty.fold f z τ₂) := rfl

def Ty.accuM
    [Monad m]
    {α σ : Type}
    (st : σ → σ × σ)
    (f : α → α → σ → m α)
    (z : σ → m α)
    (t : Ty)
    (i : σ) :
    m α :=
  match t with
  | .unit => z i
  | .arrow τ₁ τ₂ => do
    let (s₁, s₂) := st i
    f (← Ty.accuM st f z τ₁ s₁) (← Ty.accuM st f z τ₂ s₂) i

@[simp] theorem Ty.accuM_unit
  [Monad m] {α σ} {st : σ → σ × σ} {f : α → α → σ → m α} {z : σ → m α} {i : σ} :
  Ty.accuM st f z (.unit : Ty) i = z i := rfl
@[simp] theorem Ty.accuM_arrow
  [Monad m] {α σ} {st : σ → σ × σ} {f : α → α → σ → m α} {z : σ → m α}
      {i : σ} {τ₁ τ₂ : Ty} :
  Ty.accuM st f z (.arrow τ₁ τ₂) i =
   (do
    let (s₁, s₂) := st i
    f (← Ty.accuM st f z τ₁ s₁) (← Ty.accuM st f z τ₂ s₂) i) := by rfl

/- Fold special cases -/

theorem Ty.fold_accu_Option_basic
    {α : Type}
    {v : α}
    {τ : Ty}
    {z : α}
    {f : α → α → α} :
    Ty.fold f z τ = v ↔
    Ty.accuM
      (fun _ => ((), ()))
      (fun τ₁ τ₂ _ => some (f τ₁ τ₂))
      (fun _ => some z)
      τ
      () = some v := by
    induction τ generalizing v <;> simp_all [Ty.fold, Ty.accuM]
    case arrow τ₁ τ₂ ih₁ ih₂ =>
        replace ih₁ := @ih₁ (Ty.fold f z τ₁)
        replace ih₂ := @ih₂ (Ty.fold f z τ₂)
        simp_all [Ty.fold, Ty.accuM]

theorem Ty.fold_accu_Option_true
    {τ : Ty}
    {f : Bool → Bool → Bool}
    (h : ∀ acc₁ acc₂, f acc₁ acc₂ = (acc₁ && acc₂)) :
    Ty.fold f true τ = true ↔
    Ty.accuM
      (fun _ => ((), ()))
      (fun _ _ _ => some ())
      (fun _ => some ())
      τ
      () = some () := by
    induction τ <;> simp_all [Ty.fold, Ty.accuM]
    case arrow τ₁ τ₂ ih₁ ih₂ =>
        apply Iff.intro <;> intro hf
        . -- (->)
          generalize hv₁ : fold f true τ₁ = v₁
          generalize hv₂ : fold f true τ₂ = v₂
          cases v₁ <;> cases v₂ <;>
            simp_all [Ty.fold, Ty.accuM, guard]
        . -- (<-)
          rw [Option.bind_eq_some] at hf
          replace ⟨ v₁, hf ⟩ := hf
          rw [Option.bind_eq_some] at hf
          replace ⟨ h₁, ⟨ v₂, h₂ ⟩ ⟩ := hf
          simp_all [Ty.fold, Ty.accuM, guard]

theorem Ty.fold_accu_Option_function
    {α σ : Type}
    {i : σ}
    {v : α}
    {τ : Ty}
    {z : (σ → α)}
    {f : (σ → α) → (σ → α) → (σ → α)}
    {g : α → α → σ → Option α}
    {st₁ st₂ : σ → σ}
    (h : ∀ acc₁ acc₂ s w,
      f acc₁ acc₂ s = w ↔ (do g (← acc₁ (st₁ s)) (← acc₂ (st₂ s)) s) = some w)
    :
    Ty.fold f z τ i = v ↔
    Ty.accuM
      (fun s => (st₁ s, st₂ s))
      g
      (fun s => some (z s))
      τ
      i = some v := by
    induction τ generalizing v i <;> simp_all [Ty.fold, Ty.accuM, Option.bind_eq_some]
    case arrow τ₁ τ₂ ih₁ ih₂ =>
      apply Iff.intro <;> intro hg
      . -- (->)
        exists (Ty.fold f z τ₁ (st₁ i))
        rw [← ih₁] <;> simp_all
        exists (Ty.fold f z τ₂ (st₂ i))
        rw [← ih₂] <;> simp_all
      . -- (<-)
        replace ⟨ v₁, h₁, v₂, h₂, hg ⟩ := hg
        rw [← ih₁] at h₁
        rw [← ih₂] at h₂
        rw [h₁, h₂]
        apply hg

theorem Ty.fold_accu_Option_function_true
    {σ : Type}
    {i : σ}
    {τ : Ty}
    {f : (σ → Bool) → (σ → Bool) → (σ → Bool)}
    {g : σ → Bool}
    {st₁ st₂ : σ → σ}
    (h : ∀ acc₁ acc₂ s,
      f acc₁ acc₂ s = true ↔ (do (return (g s) && (← acc₁ (st₁ s)) && (← acc₂ (st₂ s)))) = some true)
    :
    Ty.fold f (λ _ => true) τ i = true ↔
    Ty.accuM
      (fun s => (st₁ s, st₂ s))
      (fun _ _ s => guard $ g s)
      (fun _ => some ())
      τ
      i = some () := by
    induction τ generalizing i <;> simp_all [Ty.fold, Ty.accuM, Option.bind_eq_some, guard]
    case arrow τ₁ τ₂ ih₁ ih₂ =>
      apply Iff.intro <;> intro hg <;> simp_all
      replace ⟨⟨ v₁, h₁ ⟩, ⟨ v₂, h₂ ⟩ , hg⟩ := hg <;> simp_all

/- Unfold -/

private def Ty.unfold_aux (n : Nat) (f : α → Gen (TyF α)) (x : α) : Gen (Option Ty) :=
  match n with
  | 0 => pure none
  | n + 1 => do
    match (← f x) with
    | .unit => pure (some .unit)
    | .arrow b₁ b₂ => do
      let τ₁ ← Ty.unfold_aux n f b₁
      let τ₂ ← Ty.unfold_aux n f b₂
      pure (do pure (.arrow (← τ₁) (← τ₂)))

attribute [local simp]
  bind
  optBind_bind
in
theorem Ty.unfold_aux_monotonic :
    some v ∈ 〚Ty.unfold_aux n f x〛 →
    some v ∈ 〚Ty.unfold_aux (n + m) f x〛 := by
  induction n generalizing v f x
  case zero =>
    simp [Ty.unfold_aux]
  case succ n' ih =>
    unfold Ty.unfold_aux
    simp
    intro τ hτ h
    cases τ <;> simp_all +arith
    case unit =>
      exists TyF.unit
    case arrow τ₁ τ₂ =>
      replace ⟨ ov₁, h₁, ov₂, h₂, h ⟩ := h
      cases ov₁ <;> simp_all
      case some v₁ =>
        cases ov₂ <;> simp_all
        case some v₂ =>
        exists (TyF.arrow τ₁ τ₂)
        simp_all
        exists v₁
        simp_all [ih]
        exists v₂
        simp_all [ih]

def Ty.unfold (f : α → Gen (TyF α)) (x : α) : Gen Ty :=
  .indexed (λ n => Ty.unfold_aux n f x)

@[simp]
def Ty.unfold_support (P : α → TyF α → Prop) (x : α) (τ : Ty) : Prop :=
  match τ with
  | .unit => P x .unit
  | .arrow τ₁ τ₂ => ∃ b₁ b₂,
    P x (.arrow b₁ b₂) ∧
    Ty.unfold_support P b₁ τ₁ ∧
    Ty.unfold_support P b₂ τ₂

attribute [local simp]
  Bind.bind
  Ty.unfold
  Ty.unfold_aux
  Functor.map
  optBind_bind
in
theorem Ty.unfold_support_ok :
    support (Ty.unfold f x) = Ty.unfold_support (λ x' => support (f x')) x := by
  funext s
  simp_all
  induction s generalizing x with
  | unit =>
    apply Iff.intro
    . intro ⟨n, h⟩
      cases n <;> simp_all
      case succ n' =>
        replace ⟨v', hv', h⟩ := h
        cases v' <;> simp_all
        case arrow τ₁ τ₂ =>
          replace ⟨ov₁, h₁, ov₂, h₂, h⟩ := h
          cases ov₁ <;> simp_all
          cases ov₂ <;> simp_all
    . intros h
      exists 1
      simp
      exists TyF.unit
  | arrow τ₁ τ₂ ih₁ ih₂ =>
    apply Iff.intro
    . intro ⟨n, h⟩
      cases n <;> simp_all; case succ n =>
      replace ⟨v', hv', h⟩ := h
      cases v' <;> simp_all
      case arrow b₁ b₂ =>
        replace ⟨ov₁, hv₁, ov₂, hv₂, h⟩ := h
        cases ov₁ <;> simp_all
        case some v₁ =>
          cases ov₂ <;> simp_all
          case some v₂ =>
            exists b₁, b₂
            apply And.intro hv'
            rw [← @ih₁ b₁, ← @ih₂ b₂]
            apply And.intro <;> exists n
    . intro ⟨b₁, b₂, hx, h₁, h₂⟩
      rw [← @ih₁ b₁] at h₁
      replace ⟨n₁, h₁⟩ := h₁
      rw [← @ih₂ b₂] at h₂
      replace ⟨n₂, h₂⟩ := h₂
      exists (n₁ + n₂ + 1)
      simp_all
      exists TyF.arrow b₁ b₂
      simp_all
      exists (some τ₁)
      simp_all [Ty.unfold_aux_monotonic]
      exists (some τ₂)
      rw [Nat.add_comm]
      simp_all [Ty.unfold_aux_monotonic]

/- Conversion of recursive functions to fold -/

theorem Ty.coerce_to_fold
    {τ : Ty}
    {f : Ty → α} -- function to be coerced
    {z : α}
    {g : α → α → α}
    (h₁ : f .unit = z)
    (h₂ : ∀ τ₁ τ₂, f (.arrow τ₁ τ₂) = g (f τ₁) (f τ₂)) :
    f τ = τ.fold g z := by
  induction τ <;> simp_all

/- Merging two accumulators -/

theorem Ty.merge_accuM
    {τ : Ty}
    {st₁ : σ₁ → σ₁ × σ₁}
    {st₂ : σ₂ → σ₂ × σ₂}
    {f₁ : α₁ → α₁ → σ₁ → Option α₁}
    {f₂ : α₂ → α₂ → σ₂ → Option α₂}
    {z₁ : σ₁ → Option α₁} {z₂ : σ₂ → Option α₂}
    {i₁ : σ₁} {i₂ : σ₂}
    {x₁ : α₁} {x₂ : α₂}
    :
    (τ.accuM st₁ f₁ z₁ i₁ = some x₁ ∧ τ.accuM st₂ f₂ z₂ i₂ = some x₂)
    ↔
    (τ.accuM
      (λ (s₁, s₂) => (((st₁ s₁).1, (st₂ s₂).1), ((st₁ s₁).2, (st₂ s₂).2)))
      (λ (x₁₁, x₁₂) (x₂₁, x₂₂) (s₁, s₂) => do (← f₁ x₁₁ x₂₁ s₁, ← f₂ x₁₂ x₂₂ s₂))
      (λ (s₁, s₂) => do (← z₁ s₁, ← z₂ s₂))
      (i₁, i₂) = some (x₁, x₂)) := by
  induction τ generalizing i₁ i₂ x₁ x₂ <;> simp_all
  case unit =>
    apply Iff.intro <;> intro h
    . -- (->)
      rw [h.left, h.right]
      simp
    . -- (<-)
      generalize hx₁ : (z₁ i₁) = x₁
      generalize hx₂ : (z₂ i₂) = x₂
      cases x₁ <;> cases x₂ <;> simp_all
  case arrow τ₁ τ₂ ih₁ ih₂ =>
    apply Iff.intro
    . -- (->)
      intro ⟨ h₁, h₂ ⟩
      rw [Option.bind_eq_some] at h₁ h₂
      replace ⟨ v₁₁, ⟨ hv₁₁, h₁ ⟩  ⟩ := @h₁
      replace ⟨ v₁₂, ⟨ hv₁₂, h₂ ⟩  ⟩ := @h₂
      rw [Option.bind_eq_some] at h₁ h₂
      replace ⟨ v₂₁, ⟨ hv₂₁, h₁ ⟩  ⟩ := @h₁
      replace ⟨ v₂₂, ⟨ hv₂₂, h₂ ⟩  ⟩ := @h₂
      replace ih₁ := @ih₁ (st₁ i₁).1 (st₂ i₂).1 v₁₁ v₁₂
      replace ih₂ := @ih₂ (st₁ i₁).2 (st₂ i₂).2 v₂₁ v₂₂
      simp_all
    . -- (<-)
      intro h
      rw [Option.bind_eq_some] at h
      replace ⟨ ⟨ v₁₁, v₁₂ ⟩ , ⟨ h₁, h ⟩ ⟩ := @h
      rw [Option.bind_eq_some] at h
      replace ⟨ ⟨ v₂₁, v₂₂ ⟩ , ⟨ h₂, h ⟩ ⟩ := @h
      rw [Option.bind_eq_some] at h
      replace ⟨ v₁, ⟨ hv₁ , h ⟩ ⟩ := @h
      rw [Option.bind_eq_some] at h
      replace ⟨ v₂, ⟨ hv₂ , h ⟩ ⟩ := @h
      replace ih₁ := @ih₁ (st₁ i₁).1 (st₂ i₂).1 v₁₁ v₁₂
      replace ih₂ := @ih₂ (st₁ i₁).2 (st₂ i₂).2 v₂₁ v₂₂
      simp_all

/- Pretty printing -/

def Ty.toString : Ty → String
  | .unit => "()"
  | .arrow τ₁ τ₂ => s!"({Ty.toString τ₁} → {Ty.toString τ₂})"

instance : ToString Ty where
  toString := Ty.toString

/- Arbitrary instance -/

def genTy : Nat → Gen (Option Ty)
  | .zero => pure none
  | .succ n' =>
    pick
      (pure (some Ty.unit))
      (do
        let g := genTy n'
        let oτ₁ ← g
        let oτ₂ ← g
        pure (Ty.arrow <$> oτ₁ <*> oτ₂))

theorem genTy_monotonic
    (hn : some v ∈ 〚genTy n〛) :
    some v ∈ 〚genTy (m + n)〛:= by
  induction n generalizing v <;>
    simp_all [← Nat.add_assoc, genTy, pick, optPick_pick, bind, optBind_bind]
  case succ n' ih =>
    cases v <;> simp_all
    case arrow τ₁ τ₂ =>
      replace ⟨ ov₁, h₁, ov₂, h₂, hn ⟩ := hn
      cases ov₁ <;> try contradiction
      case some v₁ =>
        cases ov₂ <;> try contradiction
        case some v₂ =>
          exists v₁ <;> simp_all
          exists v₂ <;> simp_all

instance : Arbitrary Ty where
  arbitrary := ⟨
    Gen.indexed genTy, by
      intro τ
      induction τ <;> simp_all <;> unfold genTy
      case unit =>
        exists 1
        simp_all [pick, optPick_pick]
      case arrow τ₁ τ₂ ih₁ ih₂ =>
        replace ⟨ n₁, ih₁ ⟩ := ih₁
        replace ⟨ n₂, ih₂ ⟩ := ih₂
        replace ih₁ := @genTy_monotonic n₁ τ₁ n₂ ih₁
        replace ih₂ := @genTy_monotonic n₂ τ₂ n₁ ih₂
        rw [Nat.add_comm] at ih₁
        exists (n₁ + n₂ + 1)
          <;> simp_all [pick, optPick_pick, bind, optBind_bind]
        exists (some τ₁) <;> simp_all
        exists (some τ₂)
      ⟩
