import Palamedes.Support

/- Type definitions -/
/- adapted from https://github.com/QuickChick/QuickChick/tree/master/examples/ifc-basic -/

inductive Label where
  | low
  | high

inductive Atom where
  | atm (z : Int) (l : Label)

inductive Stack where
  | mty
  | cons (a : Atom) (s : Stack)
  | ret_cons (pc : Atom) (s : Stack)

/- Base functor -/

inductive StackF (α : Type) where
  | mty : StackF α
  | cons : (z : Atom) → (s : α) → StackF α
  | ret_cons : (pc : Atom) → (s : α) → StackF α

theorem StackF_or
  {α : Type}
  {P : Prop}
  {Q : Atom → α → Prop}
  {R : Atom → α → Prop}
  {s : StackF α} :
  StackF.rec P Q R s ↔
    (P ∧ s = .mty)
    ∨ (∃ z s', s = .cons z s' ∧ Q z s')
    ∨ (∃ pc s', s = .ret_cons pc s' ∧ R pc s') := by
  match s with
  | .mty => simp
  | .cons _ _ => aesop
  | .ret_cons _ _ => aesop

/- Recursion schemes -/

def Stack.fold
  {α : Type}
  (f : (Atom ⊕ Atom) → α → α)
  (z : α)
  (s : Stack) : α :=
  match s with
  | .mty => z
  | .cons x s' => f (Sum.inl x) (Stack.fold f z s')
  | .ret_cons pc s' => f (Sum.inr pc) (Stack.fold f z s')

@[simp] theorem Stack.fold_mty : Stack.fold f z .mty = z := rfl
@[simp] theorem Stack.fold_cons {x} {s : Stack} {f : (Atom ⊕ Atom) → β → β} {z} :
    Stack.fold f z (.cons x s) = f (Sum.inl x) (Stack.fold f z s) := rfl
@[simp] theorem Stack.fold_ret_cons {x} {s : Stack} {f : (Atom ⊕ Atom) → β → β} {z} :
    Stack.fold f z (.ret_cons x s) = f (Sum.inr x) (Stack.fold f z s) := rfl

def Stack.accuM
  [Monad m]
  {α σ : Type}
  (st : (Atom ⊕ Atom) → σ → σ)
  (f : (Atom ⊕ Atom) → α → σ → m α)
  (z : σ → m α)
  (s : Stack)
  (i : σ) : m α :=
  match s with
  | .mty => z i
  | .cons x s' => do
     f (Sum.inl x) (← Stack.accuM st f z s' (st (Sum.inl x) i)) i
  | .ret_cons pc s' => do
     f (Sum.inr pc) (← Stack.accuM st f z s' (st (Sum.inr pc) i)) i

@[simp] theorem Stack.accuM_nil [Monad m] {st : (Atom ⊕ Atom) → σ → σ}
  {f : (Atom ⊕ Atom) → β → σ → m β} {z : σ → m β} {i : σ} :
  Stack.accuM st f z .mty i = z i := rfl
@[simp] theorem Stack.accuM_cons  [Monad m] {st : (Atom ⊕ Atom) → σ → σ}
  {f : (Atom ⊕ Atom) → β → σ → m β} {z : σ → m β} {i : σ} {x} {s : Stack} :
    Stack.accuM st f z (.cons x s) i
    = (do f (Sum.inl x) (← Stack.accuM st f z s (st (Sum.inl x) i)) i) := rfl
@[simp] theorem Stack.accuM_ret_cons [Monad m] {st : (Atom ⊕ Atom) → σ → σ}
  {f : (Atom ⊕ Atom) → β → σ → m β} {z : σ → m β} {i : σ} {pc} {s : Stack} :
    Stack.accuM st f z (.ret_cons pc s) i
    = (do f (Sum.inr pc) (← Stack.accuM st f z s (st (Sum.inr pc) i)) i) := rfl

/- Fold special cases -/

theorem Stack.fold_accu_Option_basic
    {α : Type}
    {v : α}
    {s : Stack}
    {z : α}
    {f : (Atom ⊕ Atom) → α → α} :
    Stack.fold f z s = v ↔
    Stack.accuM
      (fun _ _ => ())
      (fun x s' _ => some (f x s'))
      (fun _ => some z)
      s
      () = some v := by
    induction s generalizing v <;> simp_all [Stack.fold, Stack.accuM]
    case cons x s' ih =>
      replace ih := @ih (Stack.fold f z s')
      simp_all [Stack.fold, Stack.accuM]
    case ret_cons pc s' ih =>
      replace ih := @ih (Stack.fold f z s')
      simp_all [Stack.fold, Stack.accuM]

theorem Stack.fold_accu_Option_true
    {g : (Atom ⊕ Atom) → Bool}
    {f : (Atom ⊕ Atom) → Bool → Bool}
    (h : ∀ x acc, f x acc = (g x && acc)) :
    Stack.fold f true s = true ↔
    Stack.accuM
      (fun _ _ => ())
      (fun x _ _ => guard (g x))
      (fun _ => some ())
      s
      () = some () := by
    induction s <;> simp_all [Stack.fold, Stack.accuM]
    case cons x s' ih =>
        apply Iff.intro <;> intro hf
        . -- (->)
          generalize hv : fold f true s' = v
          cases v <;>
            simp_all [Stack.fold, Stack.accuM, guard]
        . -- (<-)
          rw [Option.bind_eq_some] at hf
          replace ⟨ v, hf ⟩ := hf
          simp_all [Stack.fold, Stack.accuM, guard]
    case ret_cons pc s' ih =>
        apply Iff.intro <;> intro hf
        . -- (->)
          generalize hv : fold f true s' = v
          cases v <;>
            simp_all [Stack.fold, Stack.accuM, guard]
        . -- (<-)
          rw [Option.bind_eq_some] at hf
          replace ⟨ v, hf ⟩ := hf
          simp_all [Stack.fold, Stack.accuM, guard]

theorem Stack.fold_accu_Option_function
    {β σ : Type}
    {i : σ}
    {v : β}
    {s : Stack}
    {z : (σ → β)}
    {f : (Atom ⊕ Atom) → (σ → β) → (σ → β)}
    {g : (Atom ⊕ Atom) → β → σ → Option β}
    {st : (Atom ⊕ Atom) → σ → σ}
    (h : ∀ x acc s w,
      f x acc s = w ↔ (do g x (← acc (st x s)) s) = some w)
    :
    Stack.fold f z s i = v ↔
    Stack.accuM
      st
      g
      (fun s => some (z s))
      s
      i = some v := by
    induction s generalizing v i <;> simp_all [Stack.fold, Stack.accuM, Option.bind_eq_some]
    case cons x s' ih =>
      apply Iff.intro <;> intro hg
      . -- (->)
        exists (Stack.fold f z s' (st (Sum.inl x) i))
        simp_all
        rw [← ih]
      . -- (<-)
        replace ⟨w, ⟨hgw, hg⟩⟩ := hg
        rw [← ih] at hgw
        rw [hgw]
        apply hg
    case ret_cons pc s' ih =>
      apply Iff.intro <;> intro hg
      . -- (->)
        exists (Stack.fold f z s' (st (Sum.inr pc) i))
        simp_all
        rw [← ih]
      . -- (<-)
        replace ⟨w, ⟨hgw, hg⟩⟩ := hg
        rw [← ih] at hgw
        rw [hgw]
        apply hg

theorem Stack.fold_accu_Option_function_true
    {σ : Type}
    {i : σ}
    {s : Stack}
    {f : (Atom ⊕ Atom) → (σ → Bool) → (σ → Bool)}
    {g : (Atom ⊕ Atom) → σ → Bool}
    {st :  (Atom ⊕ Atom) → σ → σ}
    (h : ∀ x acc s',
      f x acc s' = true ↔ (do (return (g x s') && (← acc (st x s')))) = some true)
    :
    Stack.fold f (λ _ => true) s i = true ↔
    Stack.accuM
      st
      (fun x _ s => guard $ g x s)
      (fun _ => some ())
      s
      i = some () := by
    induction s generalizing i <;> simp_all [Stack.fold, Stack.accuM, Option.bind_eq_some, guard]
    all_goals
      (apply Iff.intro <;> intro hg <;> simp_all <;>
      replace ⟨ ⟨ v, hv ⟩ , hg⟩ := hg <;> simp_all)

/- Unfold -/

private def Stack.unfold_aux (n : Nat) (f : α → Gen (StackF α)) (x : α)
  : Gen (Option Stack) :=
  match n with
  | 0 => pure none
  | n' + 1 => do
    match (← f x) with
    | .mty => pure (some .mty)
    | .cons x vs => do
      let s ← Stack.unfold_aux n' f vs
      pure (do pure (.cons x (← s)))
    | .ret_cons pc vs => do
      let s ← Stack.unfold_aux n' f vs
      pure (do pure (.ret_cons pc (← s)))

theorem Stack.unfold_aux_monotonic :
    some v ∈ 〚Stack.unfold_aux n f b〛 →
    some v ∈ 〚Stack.unfold_aux (n + 1) f b〛 := by
  induction n generalizing v f b
  case zero =>
    simp [Stack.unfold_aux]
  case succ n' ih =>
    unfold Stack.unfold_aux
    simp [bind, optBind_bind]
    intro s hs hv
    exists s
    apply And.intro hs
    cases s <;> simp_all [Functor.map, bind, optBind_bind, Option.map]
    all_goals
      replace ⟨ v', hv ⟩ := hv <;>
      exists v' <;>
      cases v' <;> simp_all

def Stack.unfold (f : α → Gen (StackF α)) (x : α) : Gen Stack :=
  .indexed (λ n => Stack.unfold_aux n f x)

@[simp]
def Stack.unfold_support (P : α → StackF α → Prop) (v : α) (s : Stack) : Prop :=
  match s with
  | .mty => P v .mty
  | .cons x s' => ∃ v', P v (.cons x v') ∧ Stack.unfold_support P v' s'
  | .ret_cons pc s' => ∃ v', P v (.ret_cons pc v') ∧ Stack.unfold_support P v' s'

attribute [local simp]
  Bind.bind
  Stack.unfold
  Stack.unfold_aux
  Functor.map
  optBind_bind
in
theorem Stack.unfold_support_ok :
    support (Stack.unfold f b) = Stack.unfold_support (λ b' => support (f b')) b := by
  funext s
  simp_all
  induction s generalizing b with
  | mty =>
    apply Iff.intro
    . intro ⟨n, h⟩
      cases n <;> simp_all
      case succ n' =>
        have ⟨v', hv'1, hv'2⟩ := h
        cases v' <;> simp_all
        all_goals
          have ⟨v'', hv''⟩ := hv'2
          cases v'' <;> simp_all
    . intros h
      exists 1
      simp
      exists StackF.mty
  | cons x s' ih =>
    apply Iff.intro
    . intro ⟨n, h⟩
      cases n <;> simp_all; case succ n =>
      have ⟨v', hv'1, hv'2⟩ := h; clear h
      cases v' <;> simp_all
      case cons _ b'' =>
        have ⟨v'', hv''⟩ := hv'2
        cases v'' <;> simp_all
        obtain ⟨hv'', rfl, rfl⟩ := hv''
        exists b''
        apply And.intro hv'1
        apply (@ih b'').mp
        exists n
      case ret_cons _ b'' =>
        have ⟨v'', hv''⟩ := hv'2
        cases v'' <;> simp_all
    . intro ⟨b', hx, hs⟩
      have ⟨n, h⟩ := ih.mpr hs
      exists n + 1
      simp_all
      exists StackF.cons x b'
      simp_all
      exists (some s')
  | ret_cons pc s' ih =>
    apply Iff.intro
    . intro ⟨n, h⟩
      cases n <;> simp_all; case succ n =>
      replace ⟨v', hv', h⟩ := h
      cases v' <;> simp_all
      case cons _ b'' =>
        have ⟨v'', hv''⟩ := h
        cases v'' <;> simp_all
      case ret_cons _ b'' =>
        have ⟨v'', hv''⟩ := h
        cases v'' <;> simp_all
        obtain ⟨hv'', rfl, rfl⟩ := hv''
        exists b''
        apply And.intro hv'
        apply (@ih b'').mp
        exists n
    .
      intro ⟨b', hx, hs⟩
      have ⟨n, h⟩ := ih.mpr hs
      exists (n + 1)
      simp_all
      exists (StackF.ret_cons pc b')
      simp_all
      exists (some s')

/- Conversion of recursive functions to fold -/

theorem Stack.coerce_to_fold
    {s : Stack}
    {f : Stack → α}
    {z : α}
    {g : (Atom ⊕ Atom) → α → α}
    (hm : f .mty = z)
    (hc : ∀ x s', f (.cons x s') = g (Sum.inl x) (f s'))
    (hr : ∀ pc s', f (.ret_cons pc s') = g (Sum.inr pc) (f s')) :
    f s = s.fold g z := by
  induction s <;> simp_all

/- Merging two accumulators-/

theorem Stack.merge_accuM
    {s : Stack}
    {st₁ : (Atom ⊕ Atom) → σ₁ → σ₁}
    {st₂ : (Atom ⊕ Atom) → σ₂ → σ₂}
    {f₁ : (Atom ⊕ Atom) → α₁ → σ₁ → Option α₁}
    {f₂ : (Atom ⊕ Atom) → α₂ → σ₂ → Option α₂}
    {s₁ : σ₁} {s₂ : σ₂}
    {z₁ : σ₁ → Option α₁} {z₂ : σ₂ → Option α₂}
    {v₁ : α₁} {v₂ : α₂}
    :
    (s.accuM st₁ f₁ z₁ s₁ = some v₁ ∧ s.accuM st₂ f₂ z₂ s₂ = some v₂)
    ↔
    (s.accuM
      (λ x (s₁, s₂) => (st₁ x s₁, st₂ x s₂))
      (λ x (v₁, v₂) (s₁, s₂) => do (← f₁ x v₁ s₁, ← f₂ x v₂ s₂))
      (λ (s₁, s₂) => do (← z₁ s₁, ← z₂ s₂))
      (s₁, s₂) = some (v₁, v₂)) := by
    induction s generalizing st₁ st₂ f₁ f₂ s₁ s₂ z₁ z₂ v₁ v₂
    case mty => simp_all [Stack.accuM, Option.bind_eq_some]
    case cons y s' ih =>
      simp_all [Stack.accuM, Option.bind_eq_some]
      apply Iff.intro
      . -- (->)
        intro ⟨ ⟨ v₁', ⟨ hv1h, hv1tl ⟩ ⟩ , ⟨ v₂', ⟨ hv2h, hv2tl ⟩ ⟩ ⟩
        exists v₁', v₂'
        replace ih := @ih st₁ st₂ f₁ f₂ (st₁ (Sum.inl y) s₁) (st₂ (Sum.inl y) s₂) z₁ z₂ v₁' v₂'
        simp_all [Stack.accuM, Option.bind_eq_some]
      . -- (<-)
        intro ⟨ v₁', v₂', h, h1, h2 ⟩
        replace ih := @ih st₁ st₂ f₁ f₂ (st₁ (Sum.inl y) s₁) (st₂ (Sum.inl y) s₂) z₁ z₂ v₁' v₂'
        apply And.intro
        . exists v₁'
          simp_all [Stack.accuM, Option.bind_eq_some]
        . exists v₂'
          simp_all [Stack.accuM, Option.bind_eq_some]
    case ret_cons pc s' ih =>
      simp_all [Stack.accuM, Option.bind_eq_some]
      apply Iff.intro
      . -- (->)
        intro ⟨ ⟨ v₁', ⟨ hv1h, hv1tl ⟩ ⟩ , ⟨ v₂', ⟨ hv2h, hv2tl ⟩ ⟩ ⟩
        exists v₁', v₂'
        replace ih := @ih st₁ st₂ f₁ f₂ (st₁ (Sum.inr pc) s₁) (st₂ (Sum.inr pc) s₂) z₁ z₂ v₁' v₂'
        simp_all [Stack.accuM, Option.bind_eq_some]
      . -- (<-)
        intro ⟨ v₁', v₂', h, h1, h2 ⟩
        replace ih := @ih st₁ st₂ f₁ f₂ (st₁ (Sum.inr pc) s₁) (st₂ (Sum.inr pc) s₂) z₁ z₂ v₁' v₂'
        apply And.intro
        . exists v₁'
          simp_all [Stack.accuM, Option.bind_eq_some]
        . exists v₂'
          simp_all [Stack.accuM, Option.bind_eq_some]

/- Pretty printing -/
def Label.toString : Label → String
  | .low => "low"
  | .high => "high"

instance : ToString Label where
  toString := Label.toString

def Atom.toString : Atom → String
  | .atm z l => s!"({z} {l})"

instance : ToString Atom where
  toString := Atom.toString

def Stack.toString : Stack → String
  | .mty => "(empty)"
  | .cons a s  => s!"(cons {a} {Stack.toString s})"
  | .ret_cons pc s => s!"(ret_cons {pc} {Stack.toString s})"

instance : ToString Stack where
  toString := Stack.toString

/- Arbitrary instances for supporting types -/

instance : Arbitrary Label where
  arbitrary := ⟨
      pick (pure .low) (pure .high),
      by intro v <;> cases v <;> simp [pick, optPick]
    ⟩

instance : Arbitrary Int where
  arbitrary := ⟨
      bind Arbitrary.arbitrary.val (λ n => pick (pure (Int.ofNat n)) (pure (Int.negSucc n))),
      by
        intro v
        simp [-support, bind, optBind_bind]
        cases v
        case ofNat n =>
          exists n
          rw [Arbitrary.arbitrary.property] <;> simp [pick, optPick_pick]
        case negSucc n =>
          exists n
          rw [Arbitrary.arbitrary.property] <;> simp [pick, optPick_pick]
    ⟩

instance : Arbitrary Atom where
  arbitrary := ⟨
      bind Arbitrary.arbitrary.val (λ z => bind Arbitrary.arbitrary.val (λ l => pure $ .atm z l)),
      by
        simp [bind, optBind_bind, Arbitrary.arbitrary.property]
        intro ⟨ z, l ⟩
        exists z, l
    ⟩
