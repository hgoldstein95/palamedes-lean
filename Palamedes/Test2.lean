import Aesop
import Plausible

inductive Gen : Type → Type 1 where
  | ret : α → Gen α
  | bind : Gen α → (α → Gen β) → Gen β
  | pick : Gen α → Gen α → Gen α
  | div : Gen α

instance : Pure Gen where
  pure a := Gen.ret a

instance : Bind Gen where
  bind := Gen.bind

instance : Monad Gen where

inductive Gen.rel : Gen α → Gen α  → Prop where
  | refl : Gen.rel x x
  | div : Gen.rel div x
  | pick : Gen.rel x₁ x₂ → Gen.rel y₁ y₂ → Gen.rel (.pick x₁ y₁) (.pick x₂ y₂)
  | bind : Gen.rel x₁ x₂ → (∀ y, Gen.rel (f₁ y) (f₂ y)) → Gen.rel (.bind x₁ f₁) (.bind x₂ f₂)

instance : Lean.Order.PartialOrder (Gen α) where
  rel := Gen.rel
  rel_refl := by intro; constructor
  rel_trans := by
    intro x y z h1 h2; induction h1 <;> cases h2 <;> grind [Gen.rel]
  rel_antisymm := by
    intro x y h1 h2; induction h1 <;> cases h2 <;> try grind
    congr
    · grind
    · grind

open Classical in
noncomputable def Gen.csup (c : Gen α → Prop) : Gen α :=
  if _ : ∀ x, c x → x = .div then
    .div
  -- /- pick one element, filter all elements with the same constuctor, recurse -/
  else if h : ∃ a, ∀ x, c x → x = .ret a ∨ x = .div then
    .ret (Classical.choose h)
  else if h : ∃ yz, ∀ x, c x → x = .pick yz.1 yz.2 ∨ x = .div then
    let (y, z) := Classical.choose h
    .pick y z
  else if h : ∃ (yf : Σ (β : Type), Gen β × (β → Gen α)), ∀ x, c x → x = .bind yf.2.1 yf.2.2 ∨ x = .div then
    let ⟨_, (y, f)⟩ := Classical.choose h
    .bind y f
  else
    .div

noncomputable instance : Lean.Order.CCPO (Gen α) where
  csup := Gen.csup
  csup_spec := by
    intros x c hc
    fun_cases Gen.csup c
    case _ =>
      apply Iff.intro
      . grind
      . intros; constructor
    case _ h h' =>
      have h_choose := Classical.choose_spec h'
      apply Iff.intro
      . intro h'' y hy
        simp_all
        cases h''
        cases h_choose _ hy
        case _ hy =>
          subst hy
          constructor
        case _ hy =>
          subst hy
          constructor
      . grind
    case _ h_div h_ret h_pick y z h_choose_pair =>
      have h_choose_spec := Classical.choose_spec h_pick
      apply Iff.intro
      . intros h_rel w hw
        simp_all
        cases h_rel
        case _ =>
          cases h_choose_spec _ hw
          case _ hw =>
            subst hw
            constructor
          case _ hw =>
            subst hw
            constructor
        case _ y' z' hy' hz' =>
          cases h_choose_spec _ hw
          case _ hw =>
            subst hw
            constructor <;> assumption
          case _ hw =>
            subst hw
            constructor
      . grind
    case _ h_div h_ret h_pick h_bind β y f h_choose_bind =>
      have h_choose_spec := Classical.choose_spec h_bind
      apply Iff.intro
      . intros h_rel w hw
        simp_all
        cases h_rel
        case _ =>
          cases h_choose_spec _ hw
          case _ hw =>
            subst hw
            sorry
          case _ hw =>
            subst hw
            constructor
        case _ =>
          cases h_choose_spec _ hw
          case _ hw =>
            subst hw
            sorry
          case _ hw =>
            subst hw
            constructor
      . grind
    case _ =>
      simp_all
      cases x
      . sorry
      . sorry
      . sorry
      . sorry


instance : Lean.Order.MonoBind Gen where
  bind_mono_left h := by
    apply Gen.rel.bind
    · assumption
    · intro y; apply Gen.rel.refl
  bind_mono_right h := by
    apply Gen.rel.bind
    · apply Gen.rel.refl
    · assumption

def support : Gen α → α → Prop
  | .div =>  fun _ => False
  | .ret a => (. = a)
  | .pick x y => fun a => support x a ∨ support y a
  | .bind x f => fun b => ∃ a, support x a ∧ support (f a) b

partial def Gen.run : Gen α → Plausible.Gen α
  | .div => throw (.genError "assume check failed")
  | .ret a => pure a
  | .pick x y => Plausible.Gen.oneOf #[x.run, y.run] (by simp)
  | .bind x f => x.run >>= Gen.run ∘ f

def genList : Gen (List Bool) := do
  if ← Gen.pick (pure true) (pure false) then
    return []
  else do
    let x ← Gen.pick (pure true) (pure false)
    let xs ← genList
    return x :: xs
partial_fixpoint

theorem genList_complete : ∀ xs, support genList xs
  | [] => by
    rw [genList]
    simp [support]
  | _ :: xs => by
    rw [genList]
    simp [support]
    exact genList_complete _

inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
deriving Repr

def choose (lo hi : Nat) (h : lo ≤ hi) := do
  if h' : lo = hi then
    return lo
  else
    Gen.pick (pure lo) (choose (.succ lo) hi (by grind))

theorem support_choose : lo ≤ x ∧ x ≤ hi → support (choose lo hi h) x := by
  fun_induction choose <;> grind [= support.eq_def, = choose.eq_def]

theorem support_choose' : support (choose lo hi h) x → lo ≤ x ∧ x ≤ hi := by
  fun_induction choose <;> grind [= support.eq_def, = choose.eq_def]

def genBST (lo hi : Nat) : Gen (Tree Nat) := do
  if h : lo > hi then
    return .leaf
  else
    if ← Gen.pick (pure true) (pure false) then
      return .leaf
    else do
      let x ← choose lo hi (by grind)
      let l ← genBST lo (x - 1)
      let r ← genBST (x + 1) hi
      return .node l x r
partial_fixpoint

def isBST (lo hi : Nat) : Tree Nat → Bool
  | .leaf => true
  | .node l x r =>
    lo ≤ x && x ≤ hi &&
    isBST lo (x - 1) l &&
    isBST (x + 1) hi r

theorem support_genBST (lo hi : Nat) (t : Tree Nat) :
    isBST lo hi t → support (genBST lo hi) t := by
  intro h
  fun_induction isBST lo hi t <;> rw [genBST]
  case _ lo hi =>
    by_cases hb : lo > hi <;> simp [hb, support]
  case _ lo hi l x r ih₁ ih₂ =>
    have : ¬ lo > hi := by grind
    simp [this, support]
    exists x
    simp_all [support_choose]

theorem support_genBST' (lo hi : Nat) (t : Tree Nat) :
    support (genBST lo hi) t → isBST lo hi t := by
  intro h
  induction t generalizing lo hi
  case leaf => rw [isBST]
  case node l x r ih_l ih_r =>
    rw [isBST]
    simp
    rw [genBST] at h
    by_cases hb : lo > hi <;>
      aesop
        (add safe support_choose')
        (add simp support)

example (lo hi : Nat) :
    support (genBST lo hi) = (fun t => isBST lo hi t = true) := by
  grind [support_genBST, support_genBST']

#eval! do
  for _ in [0:100] do
    IO.println <| s!"{← Plausible.Gen.run genList.run 10}"

#eval! do
  for _ in [0:100] do
    IO.println <| s!"{repr (← Plausible.Gen.run (genBST 0 10).run 10)}"
