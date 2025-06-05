import Palamedes.Support

/- Type definition -/

inductive Tree (α : Type) where
  | leaf : Tree α
  | node : (l : Tree α) → (x : α) → (r : Tree α) → Tree α

/- Base functor -/

inductive TreeF (α β : Type) where
  | leaf : TreeF α β
  | node : (l : β) → (x : α) → (r : β) → TreeF α β

theorem TreeF_or
    {α β : Type}
    {P : Prop}
    {Q : β → α → β → Prop}
    {t : TreeF α β} :
    TreeF.rec P Q t ↔ (P ∧ t = .leaf) ∨ (∃ bl x br, t = .node bl x br ∧ Q bl x br) := by
  match t with
  | .leaf => simp
  | .node _ _ _ => aesop

/- Recursion schemes -/

def Tree.fold
    {α β : Type}
    (f : β → α → β → β)
    (z : β)
    (t : Tree α) :
    β :=
  match t with
  | .leaf => z
  | .node l x r => f (Tree.fold f z l) x (Tree.fold f z r)

@[simp] theorem Tree.fold_leaf : Tree.fold f z .leaf = z := rfl
@[simp] theorem Tree.fold_node {x} {l r : Tree α} {f : β → α → β → β} {z} :
    Tree.fold f z (.node l x r) = f (Tree.fold f z l) x (Tree.fold f z r) := rfl

def Tree.accuM
    [Monad m]
    {α β σ : Type}
    (st : α → σ → σ × σ)
    (f : β → α → β → σ → m β)
    (z : σ → m β)
    (t : Tree α)
    (i : σ) :
    m β :=
  match t with
  | .leaf => z i
  | .node l x r => do
    let (sl, sr) := st x i
    f (← Tree.accuM st f z l sl) x (← Tree.accuM st f z r sr) i

@[simp] theorem Tree.accuM_leaf
  [Monad m] {α σ} {st : α → σ → σ × σ} {f : β → α → β → σ → m β} {z : σ → m β} {i : σ} :
  Tree.accuM st f z (.leaf : Tree α) i = z i := rfl
@[simp] theorem Tree.accuM_node
  [Monad m] {α σ} {st : α → σ → σ × σ} {f : β → α → β → σ → m β} {z : σ → m β} {i : σ} {x} {l r : Tree α} :
  Tree.accuM st f z (.node l x r) i =
   (do
    let (sl, sr) := st x i
    f (← Tree.accuM st f z l sl) x (← Tree.accuM st f z r sr) i) := by rfl

/- Fold special cases -/

theorem Tree.fold_accu_Option_basic
    {α β : Type}
    {v : β}
    {t : Tree α}
    {z : β}
    {f : β → α → β → β} :
    Tree.fold f z t = v ↔
    Tree.accuM
      (fun _ _ => ((), ()))
      (fun l x r _ => some (f l x r))
      (fun _ => some z)
      t
      () = some v := by
    induction t generalizing v <;> simp_all [Tree.fold, Tree.accuM]
    case node l x r ihl ihr =>
        replace ihl := @ihl (Tree.fold f z l)
        replace ihr := @ihr (Tree.fold f z r)
        simp_all [Tree.fold, Tree.accuM]

theorem Tree.fold_accu_Option_true
    {α : Type}
    {t : Tree α}
    {g : α → Bool}
    {f : Bool → α → Bool → Bool}
    (h : ∀ accL x accR, f accL x accR = (g x && accL && accR)) :
    Tree.fold f true t = true ↔
    Tree.accuM
      (fun _ _ => ((), ()))
      (fun _ x _ _ => guard (g x))
      (fun _ => some ())
      t
      () = some () := by
    induction t <;> simp_all [Tree.fold, Tree.accuM]
    case node l x r ihl ihr =>
        apply Iff.intro <;> intro hf
        . -- (->)
          generalize hvl : fold f true l = vl
          generalize hvr : fold f true r = vr
          cases vl <;> cases vr <;>
            simp_all [Tree.fold, Tree.accuM, guard]
        . -- (<-)
          rw [Option.bind_eq_some] at hf
          replace ⟨ vl, hf ⟩ := hf
          rw [Option.bind_eq_some] at hf
          replace ⟨ h1, ⟨ v, h2 ⟩ ⟩ := hf
          simp_all [Tree.fold, Tree.accuM, guard]

theorem Tree.fold_accu_Option_function
    {α β σ : Type}
    {i : σ}
    {v : β}
    {t : Tree α}
    {z : (σ → β)}
    {f : (σ → β) → α → (σ → β) → (σ → β)}
    {g : β → α → β → σ → Option β}
    {stl str :  α → σ → σ}
    (h : ∀ accL x accR s w,
      f accL x accR s = w ↔ (do g (← accL (stl x s)) x (← accR (str x s)) s) = some w)
    :
    Tree.fold f z t i = v ↔
    Tree.accuM
      (fun x s => (stl x s, str x s))
      g
      (fun s => some (z s))
      t
      i = some v := by
    induction t generalizing v i <;> simp_all [Tree.fold, Tree.accuM, Option.bind_eq_some]
    case node l x r ihl ihr =>
      apply Iff.intro <;> intro hg
      . -- (->)
        exists (Tree.fold f z l (stl x i))
        rw [← ihl] <;> simp_all
        exists (Tree.fold f z r (str x i))
        rw [← ihr] <;> simp_all
      . -- (<-)
        replace ⟨ vl, hl, vR, hr, hg ⟩ := hg
        rw [← ihl] at hl
        rw [← ihr] at hr
        rw [hl, hr]
        apply hg

theorem Tree.fold_accu_Option_function_true
    {α σ : Type}
    {i : σ}
    {t : Tree α}
    {f : (σ → Bool) → α → (σ → Bool) → (σ → Bool)}
    {g : α → σ → Bool}
    {stL stR :  α → σ → σ}
    (h : ∀ accL x accR s,
      f accL x accR s = true ↔ (do (return (g x s) && (← accL (stL x s)) && (← accR (stR x s)))) = some true)
    :
    Tree.fold f (λ _ => true) t i = true ↔
    Tree.accuM
      (fun x s => (stL x s, stR x s))
      (fun _ x _ s => guard $ g x s)
      (fun _ => some ())
      t
      i = some () := by
    induction t generalizing i <;> simp_all [Tree.fold, Tree.accuM, Option.bind_eq_some, guard]
    case node l x r ihl ihr =>
      apply Iff.intro <;> intro hg <;> simp_all
      replace ⟨⟨ vl, hl ⟩, ⟨ vr, hr ⟩ , hg⟩ := hg <;> simp_all

/- Unfold -/

private def Tree.unfold_aux (n : Nat) (f : β → Gen (TreeF α β)) (b : β) : Gen (Option (Tree α)) :=
  match n with
  | 0 => pure none
  | n + 1 => do
    match (← f b) with
    | .leaf => pure (some .leaf)
    | .node bl x br => do
      let l ← Tree.unfold_aux n f bl
      let r ← Tree.unfold_aux n f br
      pure (do pure (.node (← l) x (← r)))

attribute [local simp]
  bind
  optBind_bind
in
theorem Tree.unfold_aux_monotonic :
    some v ∈ 〚Tree.unfold_aux n f b〛 →
    some v ∈ 〚Tree.unfold_aux (n + m) f b〛 := by
  induction n generalizing v f b
  case zero =>
    simp [Tree.unfold_aux]
  case succ n' ih =>
    unfold Tree.unfold_aux
    simp
    intro t ht h
    cases t <;> simp_all +arith
    case leaf =>
      exists TreeF.leaf
    case node l x r =>
      replace ⟨ ovl, hl, ovr, hr, h ⟩ := h
      cases ovl <;> simp_all
      case some vl =>
        cases ovr <;> simp_all
        case some vr =>
        exists (TreeF.node l x r)
        simp_all
        exists vl
        simp_all [ih]
        exists vr
        simp_all [ih]

def Tree.unfold (f : β → Gen (TreeF α β)) (v : β) : Gen (Tree α) :=
  .indexed (λ n => Tree.unfold_aux n f v)

@[simp]
def Tree.unfold_support (P : β → TreeF α β → Prop) (b : β) (t : Tree α) : Prop :=
  match t with
  | .leaf => P b .leaf
  | .node l x r => ∃ bl br,
    P b (.node bl x br) ∧
    Tree.unfold_support P bl l ∧
    Tree.unfold_support P br r

attribute [local simp]
  Bind.bind
  Tree.unfold
  Tree.unfold_aux
  Functor.map
  optBind_bind
in
theorem Tree.unfold_support_ok :
    support (Tree.unfold f b) = Tree.unfold_support (λ b' => support (f b')) b := by
  funext s
  simp_all
  induction s generalizing b with
  | leaf =>
    apply Iff.intro
    . intro ⟨n, h⟩
      cases n <;> simp_all
      case succ n' =>
        replace ⟨v', hv', h⟩ := h
        cases v' <;> simp_all
        case node l x r =>
          replace ⟨ovl, hl, ovr, hr, h⟩ := h
          cases ovl <;> simp_all
          cases ovr <;> simp_all
    . intros h
      exists 1
      simp
      exists TreeF.leaf
  | node l x r ihl ihr =>
    apply Iff.intro
    . intro ⟨n, h⟩
      cases n <;> simp_all; case succ n =>
      replace ⟨v', hv', h⟩ := h
      cases v' <;> simp_all
      case node bl x br =>
        replace ⟨ovl, hvl, ovr, hvr, h⟩ := h
        cases ovl <;> simp_all
        case some vl =>
          cases ovr <;> simp_all
          case some vr =>
            exists bl, br
            apply And.intro hv'
            rw [← @ihl bl, ← @ihr br]
            apply And.intro <;> exists n
    . intro ⟨bl, br, hx, hl, hr⟩
      rw [← @ihl bl] at hl
      replace ⟨nl, hl⟩ := hl
      rw [← @ihr br] at hr
      replace ⟨nr, hr⟩ := hr
      exists (nl + nr + 1)
      simp_all
      exists TreeF.node bl x br
      simp_all
      exists (some l)
      simp_all [Tree.unfold_aux_monotonic]
      exists (some r)
      rw [Nat.add_comm]
      simp_all [Tree.unfold_aux_monotonic]

/- Conversion of recursive functions to fold -/

theorem Tree.coerce_to_fold
    {t : Tree α}
    {f : Tree α → β} -- function to be coerced
    {z : β}
    {g : β → α → β → β}
    (h1 : f .leaf = z)
    (h2 : ∀ l x r, f (.node l x r) = g (f l) x (f r)) :
    f t = t.fold g z := by
  induction t <;> simp_all

/- Merging two accumulators -/

theorem Tree.merge_accuM
    {t : Tree α}
    {st₁ : α → σ₁ → σ₁ × σ₁}
    {st₂ : α → σ₂ → σ₂ × σ₂}
    {f₁ : β₁ → α → β₁ → σ₁ → Option β₁}
    {f₂ : β₂ → α → β₂ → σ₂ → Option β₂}
    {s₁ : σ₁} {s₂ : σ₂}
    {z₁ : σ₁ → Option β₁} {z₂ : σ₂ → Option β₂}
    {b₁ : β₁} {b₂ : β₂}
    :
    (t.accuM st₁ f₁ z₁ s₁ = some b₁ ∧ t.accuM st₂ f₂ z₂ s₂ = some b₂)
    ↔
    (t.accuM
      (λ x (s₁, s₂) => (((st₁ x s₁).1, (st₂ x s₂).1), ((st₁ x s₁).2, (st₂ x s₂).2)))
      (λ (bl₁, bl₂) x (br₁, br₂) (s₁, s₂) => do (← f₁ bl₁ x br₁ s₁, ← f₂ bl₂ x br₂ s₂))
      (λ (s₁, s₂) => do (← z₁ s₁, ← z₂ s₂))
      (s₁, s₂) = some (b₁, b₂)) := by
  induction t generalizing st₁ st₂ f₁ f₂ s₁ s₂ z₁ z₂ b₁ b₂
  case leaf =>
    simp [accuM]
    apply Iff.intro <;> intro H
    . -- (->)
      rw [H.left, H.right]
      simp
    . -- (<-)
      generalize Hx1 : (z₁ s₁) = x1
      generalize Hx2 : (z₂ s₂) = x2
      cases x1 <;> cases x2 <;> simp_all
  case node l x r IHl IHr =>
    apply Iff.intro
    . -- (->)
      intro ⟨ H1, H2 ⟩
      unfold accuM at H1 H2 ⊢
      simp at H1 H2 ⊢
      rw [Option.bind_eq_some] at H1 H2
      replace ⟨ lv₁, ⟨ Hlv₁, H1 ⟩  ⟩ := @H1
      replace ⟨ lv₂, ⟨ Hlv₂, H2 ⟩  ⟩ := @H2
      rw [Option.bind_eq_some] at H1 H2
      replace ⟨ rv₁, ⟨ Hrv₁, H1 ⟩  ⟩ := @H1
      replace ⟨ rv₂, ⟨ Hrv₂, H2 ⟩  ⟩ := @H2
      replace IHl := @IHl st₁ st₂ f₁ f₂ (st₁ x s₁).fst (st₂ x s₂).fst z₁ z₂ lv₁ lv₂
      replace IHr := @IHr st₁ st₂ f₁ f₂ (st₁ x s₁).snd (st₂ x s₂).snd z₁ z₂ rv₁ rv₂
      simp_all
    . -- (<-)
      intro H
      unfold accuM at H ⊢
      simp at H ⊢
      rw [Option.bind_eq_some] at H
      replace ⟨ ⟨ lv₁, lv₂ ⟩ , ⟨ Hlv, H ⟩  ⟩ := @H
      rw [Option.bind_eq_some] at H
      replace ⟨ ⟨ rv₁, rv₂ ⟩ , ⟨ Hrv, H ⟩ ⟩ := @H
      rw [Option.bind_eq_some] at H
      replace ⟨ v₁, ⟨ Hv₁ , H ⟩ ⟩ := @H
      rw [Option.bind_eq_some] at H
      replace ⟨ v₂, ⟨ Hv₂ , H ⟩ ⟩ := @H
      replace IHl := @IHl st₁ st₂ f₁ f₂ (st₁ x s₁).fst (st₂ x s₂).fst z₁ z₂ lv₁ lv₂
      replace IHr := @IHr st₁ st₂ f₁ f₂ (st₁ x s₁).snd (st₂ x s₂).snd z₁ z₂ rv₁ rv₂
      simp_all

/- Pretty printing -/

def Tree.toString [ToString α] : Tree α → String
  | .leaf => "(leaf)"
  | .node l x r => s!"(node {Tree.toString l} {x} {Tree.toString r})"

instance [ToString α] : ToString (Tree α) where
  toString := Tree.toString

/- TODO: can probably remove these

def Tree.accu
    {α β σ : Type}
    (st : α → σ → σ × σ)
    (f : β → α → β → σ → β)
    (z : σ → β)
    (t : Tree α)
    (s : σ) :
    β :=
  match t with
  | .leaf => z s
  | .node l x r =>
    let (sl, sr) := st x s
    f (Tree.accu st f z l sl) x (Tree.accu st f z r sr) s

def Tree.foldM
    [Monad m]
    {α β : Type}
    (f : β → α → β → m β)
    (z : m β)
    (t : Tree α) :
    m β :=
  match t with
  | .leaf => z
  | .node l x r => do
    f (← Tree.foldM f z l) x (← Tree.foldM f z r)

@[simp] theorem foldM_leaf [Monad m] {f : β → α → β → m β} {z : m β} : Tree.foldM f z .leaf = z := rfl
@[simp] theorem foldM_node [Monad m] [LawfulMonad m] {x : α} {l r : Tree α} {f : β → α → β → m β} {z : m β} :
    Tree.foldM f z (.node l x r) = l.foldM f z >>= λ vL => r.foldM f z >>= f vL x := by
  simp only [Tree.foldM]

theorem Tree.coerce_to_foldM
    {t : Tree α}
    {f : Tree α → Bool} -- function to be coerced
    {p : α → Bool}
    (h1 : f .leaf = true)
    (h2 : ∀ l x r, f (.node l x r) = (p x && f l && f r)) :
    (f t) = (t.foldM (λ () x () => guard (p x)) () = some ()) := by
  induction t with
  | leaf =>
    simp [h1]
  | node l x r ih =>
    simp [h2]
    match Hl : Tree.foldM (λ () y () => guard (p y)) () l with
    | none => simp_all
    | some vL => match Hr : Tree.foldM (λ () y () => guard (p y)) () r with
      | none => simp_all
      | some vR => simp_all [guard]

theorem Tree.coerce_to_accuM
    {t : Tree α}
    {f : Tree α → σ → Bool}
    {p : α → σ → Bool}
    {st₁ : α → σ → σ}
    {st₂ : α → σ → σ}
    {z : σ → Bool}
    (h₁ : ∀ s, f .leaf s = z s)
    (h₂ : ∀ l x r s, f (.node l x r) s = (p x s && f l (st₁ x s) && f r (st₂ x s))) :
    (f t s) = (t.accuM (λ x s => ⟨st₁ x s, st₂ x s⟩) (λ () x () s => guard (p x s)) (λ s => guard (z s)) s = some ()) := by
  induction t generalizing s with
  | leaf => simp [Tree.accuM, h₁, guard]
  | node l x r ih =>
    simp [Tree.accuM, h₂]
    apply Iff.intro
    . aesop
    . intro h
      simp_all [Option.bind, guard]
      aesop

-/
