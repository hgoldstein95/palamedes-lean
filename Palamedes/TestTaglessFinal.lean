/-!
The big idea with this exploration is that I want to work towards a _tagless final_ version of the
generator that I had in the previous version. Rather than implement `Gen` as a data structure, I'll
implement it as a type class. And the end goal is going to be to instantiate a given concrete,
partially-fixpointed `∀ [Gen gen], gen α` at types `α → Prop` which I can use for proofs and also
at type `IO α` which I can run.
-/

inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
deriving Repr

def Tree.isBST (lo hi : Nat) : Tree Nat → Prop
  | leaf => true
  | node l x r =>
    lo ≤ x ∧ x ≤ hi ∧
    isBST lo (x - 1) l ∧
    isBST (x + 1) hi r

/-- Note that this definition follows the structure of `Tree.genBST` below. -/
def Tree.isBSTCoinductive (lo hi : Nat) (t : Tree Nat) : Prop :=
  (t = leaf)
  ∨
  (∃ (x : Nat) (l r : Tree Nat),
    lo ≤ x ∧ x ≤ hi ∧
    isBSTCoinductive lo (x - 1) l ∧
    isBSTCoinductive (x + 1) hi r ∧
    t = node l x r)
coinductive_fixpoint

example {t : Tree Nat} : t.isBST lo hi ↔ t.isBSTCoinductive lo hi := by
  fun_induction Tree.isBST <;> grind [= Tree.isBST, = Tree.isBSTCoinductive]

/-- A class capturing basic operations of a generator monad. Technically only one of these is
necessary, although there are efficiency reasons to implement them independently. -/
class Pick (m : Type → Type) where
  pick : m α → m α → m α
  choose : Nat → Nat → m Nat

section PropM

/-!
My idea is that it might be possible to recreate `Tree.isBSTCoinductive` as a monadic computation if
we use the right monad.
-/

open Pick Lean.Order

def PropM (α : Type) := α → Prop

instance : Pure PropM where
  pure a  a' := a = a'

instance : Bind PropM where
  bind m f b := ∃ a, m a ∧ f a b

instance : Pick PropM where
  pick p q := fun a => p a ∨ q a
  choose lo hi := fun a => lo ≤ a ∧ a ≤ hi

instance : PartialOrder (PropM α) := inferInstanceAs (PartialOrder (FlatOrder (fun _ => False)))
noncomputable instance : CCPO (PropM α) := inferInstanceAs (CCPO (FlatOrder (fun _ => False)))

/-- I hope this is possible? I tried to prove it but got stuck. Might just be that my `PartialOrder`
is the wrong one. -/
noncomputable instance : MonoBind PropM := sorry

/--
error: Could not prove 'Tree.isBSTCoinductiveMonad' to be monotone in its recursive calls:
  Cannot eliminate recursive call `Tree.isBSTCoinductiveMonad lo (x - 1)` enclosed in
    do
      let __do_lift ← pick (pure true) (pure false)
      if __do_lift = true then pure leaf
        else do
          let x ← choose lo hi
          let l ← isBSTCoinductiveMonad lo (x - 1)
          let r ← isBSTCoinductiveMonad (x + 1) hi
          pure (l.node x r)
  Tried to apply 'monotone_bind', but failed.
  Possible cause: A missing `MonoBind` instance.
  Use `set_option trace.Elab.Tactic.monotonicity true` to debug.
-/
#guard_msgs in
def Tree.isBSTCoinductiveMonad (lo hi : Nat) : PropM (Tree Nat) := do
  if lo > hi then
    return leaf
  else
    if ← pick (pure true) (pure false) then
      return leaf
    else
      let x ← choose lo hi
      let l ← Tree.isBSTCoinductiveMonad lo (x - 1)
      let r ← Tree.isBSTCoinductiveMonad (x + 1) hi
      return node l x r
coinductive_fixpoint

end PropM

section IO

/-!
This is the IO interpretation of the generator above. Syntactically they're basically identical, but
only one of them actually works...
-/

open Pick

instance : Pick IO where
  pick x y := do
    let coin ← IO.rand 0 1
    if coin = 0 then x else y
  choose lo hi := IO.rand lo hi

def Tree.genBST (lo hi : Nat) : IO (Tree Nat) := do
  if lo > hi then
    return leaf
  else
    if ← pick (pure true) (pure false) then
      return leaf
    else
      let x ← choose lo hi
      let l ← Tree.genBST lo (x - 1)
      let r ← Tree.genBST (x + 1) hi
      return node l x r
partial_fixpoint

#eval for _ in [0:20] do
  IO.println s!"{repr (← Tree.genBST 0 10)}"

end IO
