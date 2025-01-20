import Palamedes.Synth
import Palamedes.Sample

inductive Ty : Type where
  | unit
  | arrow (τ₁ τ₂ : Ty)
  deriving DecidableEq, Repr

def genTy (n : Nat) : Gen (Option Ty) :=
  Nat.fold (λ _ (g : Gen (Option Ty)) =>
    .pick (4, 1)
      (λ () => (pure (some Ty.unit)))
      (λ () => (.bind (λ () => g) (λ g1 =>
       .bind (λ () => g) (λ g2 =>
       pure (Ty.arrow <$> g1 <*> g2))))))
    n
    (pure none)

theorem Nat.fold_some
    (hf : ∀ {n b v}, some v ∈ 〚f n b〛 → some v ∈ 〚f (n + 1) b〛)
    (h : some v ∈ 〚Nat.fold f n (pure none)〛) :
    some v ∈ 〚f n (Nat.fold f (n - 1) (pure none))〛 := by
  induction n with
  | zero => simp_all
  | succ n' ih =>
    simp_all [Nat.fold]

theorem genTy_monotonic
    (hn : some v ∈ 〚genTy n〛) :
    some v ∈ 〚genTy (m + n)〛:= by
  unfold genTy at *
  induction n generalizing v with
  | zero => simp_all
  | succ n' ih =>
    match v with
    | .unit => simp_all [Nat.fold, wpick, optPick_pick, bind, optBind_bind]
    | .arrow τ₁ τ₂ =>
      simp [Nat.fold, wpick, optPick_pick, bind, optBind_bind] at hn
      have ⟨τ₁', hτ₁, ⟨τ₂', hτ₂, heq⟩⟩ := hn
      have ⟨rfl, rfl⟩ : τ₁ = τ₁' ∧ τ₂ = τ₂' := by
        cases τ₁' <;> cases τ₂' <;> (simp_all [Option.map, Seq.seq]; try contradiction)
      clear heq
      unfold Nat.fold
      simp [wpick, optPick_pick, bind, optBind_bind]
      exists some τ₁
      apply And.intro (ih hτ₁)
      exists some τ₂
      apply And.intro (ih hτ₂)
      simp [Option.map, Seq.seq]

attribute [local simp] genTy in
instance : Arbitrary Ty where
  arbitrary := ⟨
    Gen.sized genTy, by
      intro τ
      induction τ with
      | unit =>
        simp_all
        exists 1
        simp [Nat.fold, wpick, optPick_pick]
      | arrow τ₁ τ₂ ih₁ ih₂ =>
        simp_all
        have ⟨n₁, ih₁⟩ := ih₁
        have ⟨n₂, ih₂⟩ := ih₂
        exists n₁ + n₂ + 1
        simp_all [Nat.fold, wpick, optPick_pick, bind, optBind_bind]
        exists some τ₁
        apply And.intro
        . conv =>
            arg 1
            arg 2
            rw [Nat.add_comm]
          apply genTy_monotonic ih₁
        . exists some τ₂
          apply And.intro
          . apply genTy_monotonic ih₂
          . rfl
  ⟩

inductive Term : Type where
  | unit
  | var (n : Nat)
  | abs (τ : Ty) (t : Term)
  | app (t₁ t₂ : Term)
  deriving Repr

inductive TermF : Type → Type where
  | unitStep : TermF β
  | varStep : (n : Nat) → TermF β
  | absStep : (τ : Ty) → (t : β) → TermF β
  | appStep : (t₁ t₂ : β) → TermF β

def Term.fold (f : TermF β → β) : Term → β
  | .unit => f .unitStep
  | .var n => f (.varStep n)
  | .abs τ t => f (.absStep τ (Term.fold f t))
  | .app t₁ t₂ => f (.appStep (Term.fold f t₁) (Term.fold f t₂))

def Term.accu
    {β σ : Type}
    (stAbs : Ty → σ → σ)
    (stApp : σ → σ × σ)
    (f : TermF β → σ → β)
    (t : Term)
    (s : σ) :
    β :=
  match t with
  | .unit => f .unitStep s
  | .var n => f (.varStep n) s
  | .abs τ t => f (.absStep τ (Term.accu stAbs stApp f t (stAbs τ s))) s
  | .app t₁ t₂ =>
    let (s₁, s₂) := stApp s
    f (.appStep (Term.accu stAbs stApp f t₁ s₁) (Term.accu stAbs stApp f t₂ s₂)) s

def Term.accuM
    [Monad m]
    {β σ : Type}
    (stAbs : Ty → σ → σ)
    (stApp : σ → σ × σ)
    (f : TermF β → σ → m β)
    (t : Term)
    (s : σ) :
    m β :=
  match t with
  | .unit => f .unitStep s
  | .var n => f (.varStep n) s
  | .abs τ t => do f (.absStep τ (← Term.accuM stAbs stApp f t (stAbs τ s))) s
  | .app t₁ t₂ => do
    let (s₁, s₂) := stApp s
    f (.appStep (← Term.accuM stAbs stApp f t₁ s₁) (← Term.accuM stAbs stApp f t₂ s₂)) s

def Term.unfold' (n : Nat) (f : β → Gen (TermF β)) (b : β) : Gen (Option Term) :=
  Nat.fold (λ _ (g : β → Gen (Option Term)) => λ b =>
    .bind (λ () => f b) (λ x =>
      match x with
      | .unitStep => pure (some .unit)
      | .varStep n => pure (some (.var n))
      | .absStep τ bt =>
        .bind (λ () => g bt) (λ t =>
        pure (.abs τ <$> t))
      | .appStep bt₁ bt₂ =>
        .bind (λ () => g bt₁) (λ t₁ =>
        .bind (λ () => g bt₂) (λ t₂ =>
        pure (.app <$> t₁ <*> t₂)))))
    n
    (λ _ => pure none)
    b

attribute [local simp] Seq.seq in
theorem Term.unfold'_monotonic
    (hn : some v ∈ 〚Term.unfold' n f b〛) :
    some v ∈ 〚Term.unfold' (m + n) f b〛:= by
  unfold Term.unfold' at *
  induction n generalizing v b with
  | zero => simp_all
  | succ n' ih =>
    simp [Nat.fold, bind, optBind_bind] at hn
    have ⟨v', hv'1, hv'2⟩ := hn
    match v' with
    | .unitStep =>
      unfold Nat.fold
      simp [bind, optBind_bind]
      exists .unitStep
    | .varStep n =>
      unfold Nat.fold
      simp [bind, optBind_bind]
      exists .varStep n
    | .absStep τ t =>
      unfold Nat.fold
      simp [bind, optBind_bind]
      exists .absStep τ t
      simp [optBind_bind]
      apply And.intro hv'1
      simp [optBind_bind] at hv'2
      have ⟨v'', hv''⟩ := hv'2
      exists v''
      match v'' with
      | none => aesop
      | some v'' =>
        simp [bind, optBind, optBind_bind] at ih
        apply And.intro
        . apply ih
          simp_all only [Option.some_bind, Option.some.injEq]
        . simp_all only [Option.some_bind, Option.some.injEq]
    | .appStep t₁ t₂ =>
      unfold Nat.fold
      simp [bind, optBind_bind]
      exists .appStep t₁ t₂
      simp [optBind_bind]
      apply And.intro hv'1
      simp [optBind_bind] at hv'2
      have ⟨v''₁, hv''₁, v''₂, hv''₂⟩ := hv'2
      match v''₁, v''₂ with
      | some v''₁, some v''₂ =>
        exists v''₁
        simp [bind, optBind, optBind_bind] at ih
        apply And.intro
        . apply ih
          simp_all only [Option.some_bind, Option.some.injEq]
        . exists v''₂
          apply And.intro
          . apply ih
            simp_all only [Option.some_bind, Option.some.injEq]
          . simp_all only [Option.some_bind, Option.some.injEq]
      | none, _ => aesop
      | _, none => aesop

def Term.unfold (f : β → Gen (TermF β)) (b : β) : Gen Term :=
  Gen.sized (λ n => Term.unfold' n f b)

@[simp]
def Term.unfold_support (P : β → TermF β → Prop) (b : β) : Term → Prop
  | .unit => P b .unitStep
  | .var n => P b (.varStep n)
  | .abs τ t => ∃ bt, P b (.absStep τ bt) ∧ Term.unfold_support P bt t
  | .app t₁ t₂ => ∃ bt₁ bt₂,
    P b (.appStep bt₁ bt₂) ∧
    Term.unfold_support P bt₁ t₁ ∧
    Term.unfold_support P bt₂ t₂

attribute [local simp] Seq.seq in
theorem Term.unfold_unfold_support :
    support (Term.unfold f b) = Term.unfold_support (λ b' => support (f b')) b := by
  funext v
  unfold Term.unfold
  unfold Term.unfold'
  simp [bind]
  apply Iff.intro
  . intro ⟨n, hn⟩
    induction n generalizing b v with
    | zero => simp_all
    | succ n' ih =>
      simp_all [Nat.fold, optBind_bind]
      have ⟨v', hv'1, hv'2⟩ := hn
      match v' with
      | .unitStep => simp_all
      | .varStep n => simp_all
      | .absStep τ t =>
        simp_all [optBind_bind]
        have ⟨v'', hv''1, hv''2⟩ := hv'2
        match v'' with
        | none => simp_all
        | some v'' => aesop
      | .appStep τ t =>
        simp_all [optBind_bind]
        have ⟨v''₁, hv''1, ⟨v''₂, hv''2, hv''3⟩⟩ := hv'2
        match v''₁, v''₂ with
        | some v''₁, some v''₂ => aesop
        | none, _ => aesop
        | _, none => aesop
  . intro h
    induction v generalizing b with
    | unit =>
      exists 1
      simp_all [Nat.fold, optBind_bind]
      exists .unitStep
    | var n =>
      exists 1
      simp_all [Nat.fold, optBind_bind]
      exists .varStep n
    | abs τ t ih =>
      simp_all
      have ⟨bt, hstep, h⟩ := h
      have ⟨n, hn⟩ := ih h
      exists n + 1
      simp_all [Nat.fold, optBind_bind]
      exists .absStep τ bt
      simp_all [optBind_bind]
      exists t
    | app t₁ t₂ ih₁ ih₂ =>
      simp_all
      have ⟨bt₁, bt₂, hstep, h₁, h₂⟩ := h
      have ⟨n₁, hn₁⟩ := ih₁ h₁
      have ⟨n₂, hn₂⟩ := ih₂ h₂
      exists (n₁ + n₂ + 1)
      simp_all [Nat.fold, optBind_bind]
      exists .appStep bt₁ bt₂
      simp_all [optBind_bind]
      exists t₁
      apply And.intro
      . conv =>
          arg 1
          arg 2
          rw [Nat.add_comm]
        apply (Term.unfold'_monotonic hn₁)
      . exists t₂
        apply And.intro
        . apply (Term.unfold'_monotonic hn₂)
        . aesop

abbrev Term.synth_accuM
    {β σ : Type}
    {stAbs : Ty → σ → σ}
    {stApp : σ → σ × σ}
    {f : TermF β → σ → Option β}
    {s : σ}
    {b : β}
    (g : (b : β) → (s : σ) → CGen
      (TermF.rec
        (f .unitStep s = some b)
        (λ n => f (.varStep n) s = some b)
        (λ τ t => f (.absStep τ t) s = some b)
        (λ t₁ t₂ => f (.appStep t₁ t₂) s = some b))) :
    CGen (λ (v : Term) => Term.accuM stAbs stApp f v s = some b) := by
  exists Term.unfold
    (λ (b, s) => do
      match (← (g b s).val) with
      | .unitStep => pure .unitStep
      | .varStep n => pure (.varStep n)
      | .absStep τ bt => do
        let s' := stAbs τ s
        pure (.absStep τ (bt, s'))
      | .appStep bt₁ bt₂ => do
        let (s₁, s₂) := stApp s
        pure (.appStep (bt₁, s₁) (bt₂, s₂)))
    (b, s)
  intro v
  rw [Term.unfold_unfold_support]
  induction v generalizing b s with
  | unit =>
    simp_all [Term.accuM, bind, optBind_bind]
    have g_prop := (g b s).property .unitStep
    aesop
  | var n =>
    simp_all [Term.accuM, bind, optBind_bind]
    have g_prop := (g b s).property (.varStep n)
    aesop
  | abs τ t ih =>
    simp_all [Term.accuM, bind, optBind_bind]
    generalize ho : accuM stAbs stApp f t (stAbs τ s) = o at *
    match o with
    | none => aesop
    | some bt =>
      have g_prop := (g b s).property (.absStep τ bt)
      aesop
  | app t₁ t₂ ih₁ ih₂ =>
    simp_all [Term.accuM, bind, optBind_bind]
    generalize ho₁ : accuM stAbs stApp f t₁ (stApp s).fst = o₁ at *
    match o₁ with
    | none => aesop
    | some bt₁ =>
      generalize ho₂ : accuM stAbs stApp f t₂ (stApp s).snd = o₂ at *
      match o₂ with
      | none => aesop
      | some bt₂ =>
        have g_prop := (g b s).property (.appStep bt₁ bt₂)
        simp_all [Option.some_bind]
        rw [← g_prop]
        apply Iff.intro
        . aesop
        . intro h
          exists bt₁
          exists (stApp s).fst
          exists bt₂
          exists (stApp s).snd
          aesop

theorem Ty.deforest_eq
    {b b_unit : β}
    {b_arrow : Ty → Ty → β} :
    Ty.rec b_unit (λ τ₁ τ₂ _ _ => b_arrow τ₁ τ₂) τ = b ↔
    Ty.rec (b_unit = b) (λ τ₁ τ₂ _ _ => b_arrow τ₁ τ₂ = b) τ := by
  induction τ <;> aesop

theorem Ty.as_or
    {P_unit : Prop}
    {P_arrow : Ty → Ty → Prop} :
    Ty.rec P_unit (λ τ₁ τ₂ _ _ => P_arrow τ₁ τ₂) τ ↔
    (τ = .unit ∧ P_unit) ∨ (∃ τ₁ τ₂, τ = .arrow τ₁ τ₂ ∧ P_arrow τ₁ τ₂) := by
  induction τ <;> aesop

theorem TermF.as_or :
    TermF.rec P_unit P_var P_app P_abs t ↔
    ((t = .unitStep ∧ P_unit) ∨
     (∃ n, t = .varStep n ∧ P_var n) ∨
     (∃ τ t', t = .absStep τ t' ∧ P_app τ t') ∨
     (∃ t₁ t₂, t = .appStep t₁ t₂ ∧ P_abs t₁ t₂)) := by
  induction t <;> aesop

def elements (xs : List α) (h : xs.length > 0) : Gen α :=
  match xs with
  | x :: xs =>
    match hxs : xs with
    | [] => pure x
    | _ :: _ => pick (pure x) (elements xs (by rw [hxs]; simp))

theorem support_elements
    {xs : List α} {v : α} {h : xs.length > 0} :
    v ∈ 〚elements xs h〛↔ v ∈ xs := by
  induction xs with
  | nil => simp_all; contradiction
  | cons x xs ih =>
    match hxs : xs with
    | [] => simp_all
    | _ :: _ =>
      simp [elements, pick, optPick_pick] at ih
      simp [elements, pick, optPick_pick] at hxs
      simp [elements, pick, optPick_pick] at h
      simp [elements, pick, optPick_pick]
      subst hxs
      simp_all only [List.length_cons, gt_iff_lt, Nat.lt_add_left_iff_pos, Nat.zero_lt_succ]

def indicesOf [DecidableEq α] (xs : List α) (a : α) : Gen Nat :=
  let inds := (xs.enum.filter (λ (_, x) => x == a)).map (λ (n, _) => n)
  .guardIn (inds.length > 0)
           (if h : inds.length > 0 then isTrue h else isFalse h)
           (λ h => elements inds h)

def synth_get? [DecidableEq α] {xs : List α} {a : α} : CGen (fun (n : Nat) => xs[n]? = some a) := by
  exists indicesOf xs a
  intro v
  simp [indicesOf, support_elements]
  apply Iff.intro
  . intro ⟨_, h2⟩
    exact List.mk_mem_enum_iff_getElem?.mp h2
  . intro h
    apply And.intro
    . rw [← List.mk_mem_enum_iff_getElem?] at h
      apply List.length_pos_of_mem
      simp_all only [List.mem_filter, beq_iff_eq]
      apply And.intro
      · exact h
      · simp_all only
    . exact List.mk_mem_enum_iff_getElem?.mpr h

theorem Option.rec_exists : Option.rec False (λ _ => True) o ↔ ∃ v, o = some v := by
  match o with
  | none => simp
  | some v => simp

def Ctx := List Ty

def hasType_natural (Γ : Ctx) : Term → Option Ty
  | .unit => pure .unit
  | .var n => Γ.get? n
  | .abs τ t => .arrow τ <$> hasType_natural (τ :: Γ) t
  | .app t1 t2 => do
    match ← hasType_natural Γ t1 with
    | .arrow τ1 τ2 => do
      let τ3 ← hasType_natural Γ t2
      guard (τ1 == τ3)
      pure τ2
    | .unit => failure

def hasType_fold (Γ : Ctx) (t : Term) : Option Ty :=
  Term.fold
    (λ (s : TermF (Ctx → Option Ty)) =>
      match s with
      | .unitStep => λ _ => pure Ty.unit
      | .varStep n => λ Γ => Γ.get? n
      | .absStep τ hasType_t => λ Γ => .arrow τ <$> hasType_t (τ :: Γ)
      | .appStep hasType_t₁ hasType_t₂ => λ Γ => do
        match ← hasType_t₁ Γ with
        | .arrow τ1 τ2 => do
          let τ3 ← hasType_t₂ Γ
          guard (τ1 == τ3)
          pure τ2
        | .unit => failure)
    t
    Γ

def hasType_accu (Γ : Ctx) (t : Term) : Option Ty :=
  Term.accu
    (λ τ Γ => τ :: Γ)
    (λ Γ => (Γ, Γ))
    (λ (s : TermF (Option Ty)) Γ =>
      match s with
      | .unitStep => pure Ty.unit
      | .varStep n => Γ.get? n
      | .absStep τ τt => .arrow τ <$> τt
      | .appStep τt₁ τt₂ => do
        match ← τt₁ with
        | .arrow τ1 τ2 => do
          let τ3 ← τt₂
          guard (τ1 == τ3)
          pure τ2
        | .unit => failure)
    t
    Γ

@[simp]
def hasType (Γ : Ctx) (t : Term) : Option Ty :=
  Term.accuM
    (λ τ Γ => τ :: Γ)
    (λ Γ => (Γ, Γ))
    (λ (s : TermF Ty) Γ =>
      match s with
      | .unitStep => pure Ty.unit
      | .varStep n => Γ.get? n
      | .absStep τ τt => pure (.arrow τ τt)
      | .appStep τt₁ τt₂ =>
        match τt₁ with
        | .arrow τ1 τ2 => do guard (τ1 == τt₂); pure τ2
        | .unit => failure)
    t
    Γ

def genWellTyped_manual (Γ : Ctx) : CGen (λ (v : Term) =>
    match hasType Γ v with
    | some _ => True
    | none => False) := by
  unfold genWellTyped_manual.match_1
  simp [Option.rec_exists]
  apply synth_bind_arb
  intro τ
  apply Term.synth_accuM
  intro τ Γ
  simp [TermF.as_or]
  match τ with
  | .unit =>
    simp
    apply synth_or
    . apply synth_pure
    . apply synth_or
      . conv => congr; intro v; congr; intro x; rw [and_comm]
        apply synth_bind
        . apply synth_get?
        . intro n
          apply synth_pure
      . unfold hasType_natural.match_1
        simp_all [guard, ite, failure, deforest_decidable_bind, deforest_decidable_eq, decidable_or, Ty.deforest_eq, Ty.as_or]
        conv => congr; intro v; rw [exists_comm]
        apply synth_bind_arb
        intro τ₁
        conv => congr; intro v; congr; intro x; rw [and_comm]
        apply synth_bind
        . apply synth_pure
        . intro τ₂
          apply synth_pure
  | .arrow τ₁ τ₂ =>
    simp
    apply synth_or
    . conv => congr; intro v; congr; intro x; rw [and_comm]
      apply synth_bind
      . apply synth_get?
      . intro n
        apply synth_pure
    . apply synth_or
      . apply synth_pure
      . unfold hasType_natural.match_1
        set_option smartUnfolding false in
        simp_all [guard, ite, failure, deforest_decidable_bind, deforest_decidable_eq, decidable_or, Ty.deforest_eq, Ty.as_or]
        conv => congr; intro v; rw [exists_comm]
        apply synth_bind_arb
        intro τ₁
        conv => congr; intro v; congr; intro x; rw [and_comm]
        apply synth_bind
        . apply synth_pure
        . intro τ₂
          apply synth_pure

attribute [simp]
  guard
  failure
  ite
  deforest_decidable_bind
  deforest_decidable_eq
  decidable_or
  Ty.deforest_eq
  Ty.as_or
  TermF.as_or
  ListF_or
  TreeF_or
  fold_foldM
  merge_foldM
  Option.rec_exists
attribute [-simp]
  Prod.forall
attribute [-aesop]
  Subtype
add_aesop_rules unsafe [
  apply synth_bind,
  apply synth_bind_arb,
  apply synth_or,
  apply synth_pure,
  apply synth_true,
  apply synth_tuple,
  apply synth_unfoldM,
  apply synth_accuM,
  apply synth_accuTreeM,
  apply synth_between,
  apply Term.synth_accuM,
  (by apply Term.synth_accuM; intro b s; cases b),
  apply synth_get?,
  (by (conv => congr; intro v; congr; intro x; rw [and_comm]); apply synth_bind),
  (by (conv => congr; intro v; rw [eq_comm]); apply synth_pure),
  (by (conv => congr; intro v; rw [exists_comm]); apply synth_bind_arb),
]

def genWellTyped (Γ : Ctx) : CGen (λ (v : Term) =>
    match hasType Γ v with
    | some _ => True
    | none => False) := by
  aesop
    (add unsafe (by unfold hasType_natural.match_1))
    (add unsafe (by unfold genWellTyped_manual.match_1))

-- #eval sampleN 10 (genWellTyped []).val
