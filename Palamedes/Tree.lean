import Palamedes.Free
import Palamedes.Support

inductive Tree (α : Type) where
  | leaf : Tree α
  | node : (l : Tree α) → (x : α) → (r : Tree α) → Tree α

def treeToString [ToString α] : Tree α → String
  | .leaf => "(leaf)"
  | .node l x r => s!"(node {treeToString l} {x} {treeToString r})"

instance [ToString α] : ToString (Tree α) where
  toString := treeToString

inductive TreeF (α β : Type) where
  | leaf : TreeF α β
  | node : (l : β) → (x : α) → (r : β) → TreeF α β

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

def Tree.fold
    {α β : Type}
    (f : β → α → β → β)
    (z : β)
    (t : Tree α) :
    β :=
  match t with
  | .leaf => z
  | .node l x r => f (Tree.fold f z l) x (Tree.fold f z r)

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

def Tree.accuM
    [Monad m]
    {α β σ : Type}
    (st : α → σ → σ × σ)
    (f : β → α → β → σ → m β)
    (z : σ → m β)
    (t : Tree α)
    (s : σ) :
    m β :=
  match t with
  | .leaf => z s
  | .node l x r => do
    let (sl, sr) := st x s
    f (← Tree.accuM st f z l sl) x (← Tree.accuM st f z r sr) s

theorem fold_accuM
    [Monad m]
    {α β σ : Type}
    {st : α → σ → σ × σ}
    {s : σ}
    {t : Tree α}
    {z : σ → m β}
    {f : β → α → β → σ → m β}
    {f' : (σ → m β) → α → (σ → m β) → σ → m β} :
    f' = (λ bl x br => λ s => do
      let (sl, sr) := st x s
      f (← bl sl) x (← br sr) s) →
    Tree.fold f' z t s = Tree.accuM st f z t s := by
  induction t generalizing s <;> simp_all [Tree.fold, Tree.accuM]

def unfoldTree (n : Nat) (f : β → Gen (TreeF α β)) (b : β) : Gen (Option (Tree α)) :=
  match n with
  | 0 => pure none
  | n + 1 => do
    match (← f b) with
    | .leaf => pure (some .leaf)
    | .node bl x br => do
      let l ← unfoldTree n f bl
      let r ← unfoldTree n f br
      pure (do pure (.node (← l) x (← r)))

@[simp]
def support_unfoldTree (P : β → TreeF α β → Prop) (b : β) (xs : Tree α) : Prop :=
  match xs with
  | .leaf => P b .leaf
  | .node l x r => ∃ bl br,
    P b (.node bl x br) ∧
    support_unfoldTree P bl l ∧
    support_unfoldTree P br r

theorem unfoldTree_monotonic'
    {n : Nat}
    {f : β → Gen (TreeF α β)}
    {b : β} :
    .some v ∈ 〚unfoldTree n f b〛→
    .some v ∈ 〚unfoldTree (n + 1) f b〛:= by
  intro hn
  induction v generalizing n b with
  | leaf =>
    match n with
    | 0 => simp_all
    | .succ _ =>
      simp_all [unfoldTree, bind]
      have ⟨v', hv'1, hv'2⟩ := hn
      exists v'
      match v' with
      | .leaf => simp_all
      | .node _ _ _ =>
        simp_all [bind]
        have ⟨a, ⟨_, ⟨b, _, _⟩⟩⟩ := hv'2
        match a, b with
        | .some _, .some _ => simp_all
  | node l x r ihl ihr =>
    match n with
    | 0 => simp_all
    | .succ n' =>
      simp_all [unfoldTree, bind]
      have ⟨v', hv'1, hv'2⟩ := hn
      exists v'
      match v' with
      | .node bl y br =>
        simp_all [unfoldTree, bind]
        have ⟨ll, hll, rr, hrr, h⟩ := hv'2
        clear hv'2
        match ll, rr with
        | .none, _ => simp_all
        | _, .none => simp_all
        | .some ll, some rr =>
          simp_all [unfoldTree, bind]
          cases h
          replace ihl := ihl hll
          replace ihr := ihr hrr
          clear hll
          clear hrr
          exists (some l)
          apply And.intro
          . rename_i left right
            subst left
            simp_all only
          . exists some rr
            rename_i left right
            subst left
            simp_all only [Option.some_bind, and_self]

theorem unfoldTree_monotonic
    {n m : Nat}
    {f : β → Gen (TreeF α β)}
    {b : β} :
    n ≤ m →
    .some v ∈ 〚unfoldTree n f b〛→
    .some v ∈ 〚unfoldTree m f b〛:= by
  intro hlt hn
  induction m generalizing n with
  | zero =>
    cases hlt
    simp_all
  | succ m' ih =>
    have : n = m' + 1 ∨ n ≤ m' := by cases hlt <;> simp_all
    match this with
    | .inl h => subst h; simp_all
    | .inr h =>
      have := ih h hn
      apply unfoldTree_monotonic' this

theorem support_unfoldTree_ok :
    support (.sized (λ n => unfoldTree n f b)) = support_unfoldTree (λ b' => support (f b')) b := by
  funext t
  induction t generalizing b with
  | leaf =>
    simp_all
    apply Iff.intro
    . intro ⟨n, h⟩
      match n with
      | 0 => simp_all
      | n + 1 =>
        simp_all [unfoldTree, bind]
        have ⟨v', hv'1, hv'2⟩ := h
        match v' with
        | .leaf => simp_all
        | .node _ _ _ =>
          simp_all [unfoldTree, bind]
          have ⟨l'', hl'', r'', hr''⟩ := hv'2
          match l'', r'' with
          | .none, _ => simp_all
          | _, .none => simp_all
          | .some .leaf, .some (.node _ _ _) => simp_all [Option.bind]
          | .some (.node _ _ _), .some .leaf => simp_all [Option.bind]
          | .some (.node _ _ _), .some (.node _ _ _) => simp_all
    . intro h
      exists 1
      simp [unfoldTree, bind]
      exists .leaf
  | node l x r ih_l ih_r =>
    simp_all
    apply Iff.intro
    . intro ⟨n, h⟩
      match n with
      | 0 => simp_all
      | n + 1 =>
        simp_all [unfoldTree, bind]
        have ⟨v', hv'1, hv'2⟩ := h
        match v' with
        | .leaf => simp_all
        | .node bl'' x br'' =>
          simp_all [unfoldTree, bind]
          have ⟨l'', hl'', r'', hr'', hv''⟩ := hv'2
          match l'', r'' with
          | .none, _ => simp_all
          | _, .none => simp_all
          | .some l, .some r =>
            simp_all
            obtain ⟨rfl, rfl, rfl⟩ := hv''
            exists bl''
            exists br''
            apply And.intro hv'1
            apply And.intro
            . apply (@ih_l bl'').mp
              exists n
            . apply (@ih_r br'').mp
              exists n
    . intro ⟨bl, br, hx, hl, hr⟩
      have ⟨nl, hl⟩ := ih_l.mpr hl
      have ⟨nr, hr⟩ := ih_r.mpr hr
      exists nl + nr + 1
      simp_all [unfoldTree, bind]
      exists .node bl x br
      simp_all [unfoldTree, bind]
      exists some l
      apply And.intro
      . apply @unfoldTree_monotonic _ _ _ nl (nl + nr)
        . simp
        . assumption
      . exists some r
        apply And.intro
        . apply @unfoldTree_monotonic _ _ _ nr (nl + nr)
          . simp
          . assumption
        . simp
