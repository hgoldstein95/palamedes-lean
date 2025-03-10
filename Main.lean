import Palamedes.Synth
import Palamedes.Sample
import Palamedes.Tree
import Mathlib.Tactic.Convert
import Ssreflect.Lang

attribute [simp]
  guard
  failure
  ite -- NOTE This may be a problem
  deforest_decidable_bind
  deforest_decidable_eq
  decidable_or
  ListF_or
  TreeF_or
  fold_foldM
  merge_foldM
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
  (by (conv => congr; intro v; congr; intro x; rw [and_comm]); apply synth_bind),
  (by (conv => congr; intro v; rw [eq_comm]); apply synth_pure),
]
add_aesop_rules 5% [
  cases Nat,
  cases Bool,
]

def genTwo : CGen (λ v => v = 2) := by
  aesop

def genTwo' : CGen (2 = .) := by
  aesop

def genTwoOrThree : CGen (λ v => v = 2 ∨ v = 3) := by
  aesop

def genTwoOrThreeOrFour : CGen (λ v => v = 2 ∨ v = 3 ∨ v = 4) := by
  aesop

def genTwoAndThree : CGen (λ (v : Int × Int) => v.fst = 2 ∧ v.snd = 3) := by
  aesop

def genTwoAndThree' : CGen (λ (v : Nat × Nat) => ∃ a, ∃ b, a = 2 ∧ b = 3 ∧ v = (a, b)) := by
  aesop

def genThreeAndTwo : CGen (λ (v : Int × Int) => v.snd = 3 ∧ v.fst = 2) := by
  aesop

def genThreeAndTwo' : CGen (λ (v : Int × Int) => ∃ a, ∃ b, b = 3 ∧ a = 2 ∧ v = (a, b)) := by
  aesop

def genAllTwos : CGen (λ v => List.foldrM (λ x () => guard (x == 2)) () v = Option.some ()) := by
  aesop

def genEvenLength [Arbitrary α] :
    CGen (λ (v : List α) => List.foldr (λ _ b => not b) true v) := by
  aesop

def genLengthK {k : Nat} [Arbitrary α] :
    CGen (λ (v : List α) => List.foldr (λ _ len_xs => len_xs + 1) 0 v = k) := by
  simp only [fold_foldM]
  aesop

def genEvenLengthTwos :
    CGen (λ (v : List Nat) => List.foldrM (λ x b => do guard (x == 2); pure (not b)) true v = Option.some true) := by
  aesop

def genLengthKTwos {k : Nat} :
    CGen (λ (v : List Nat) =>
      List.foldr (λ _ l => l + 1) 0 v = k ∧
      List.foldrM (λ x () => guard (x == 2)) () v = Option.some ()) := by
  simp only [fold_foldM]
  aesop

def genIncreasingByOne :
    CGen (λ v =>
      List.accuM (λ x _ => x)
                 (λ x () => λ (prev : Int) => do guard (x == prev + 1))
                 (λ _ => pure ())
                 v
                 0 = some ()) := by
  aesop

def genTreeIncreasingByOne :
    CGen (λ v =>
      Tree.accuM (λ x _ => (x, x))
                 (λ () x () => λ (prev : Int) => do guard (x == prev + 1))
                 (λ _ => pure ())
                 v
                 0 = some ()) := by
  aesop

def genBetween : CGen (λ v => 3 ≤ v ∧ v ≤ 10) := by
  aesop

def genSortedBetween
    (lo hi : Nat) :
    CGen (λ v =>
      List.accuM (λ x _ => x)
                 (λ x () => λ (prev : Nat) => do guard (prev ≤ x ∧ x ≤ hi))
                 (λ _ => pure ())
                 v
                 lo = some ()) := by
  aesop

def isBST (lo hi : Nat) (t : Tree Nat) : Option Unit :=
  Tree.accuM (λ x p => ((p.fst, x - 1), (x + 1, p.snd)))
             (λ () x () => λ (p : Nat × Nat) => do guard (p.fst ≤ x ∧ x ≤ p.snd))
             (λ _ => pure ())
             t
             (lo, hi)

def genBST (lo hi : Nat) : CGen (λ v => isBST lo hi v = some ()) := by
  aesop

#eval sampleN 10 (genBST 50 100).val

def foo (x) :=
  let y := x + 1;
  y + 1

def bar : Gen ℕ := choose 0 100

#check bar

def xyGenInstance : Gen (ℕ × ℕ) := do
  let x <- choose 0 200
  let y <- choose 0 200
  if x <= y
  then pure (x, y)
  else pure (y, x)

#check Exists.intro xyGenInstance

-- Verifying XY ordered
def genXYOrdered : CGen (λ (v : Nat × Nat) =>
                            0 ≤ v.1 ∧ v.1 ≤ v.2 ∧ v.2 ≤ 200) :=
  Subtype.mk xyGenInstance (by
    move=>[x y]
    apply Iff.intro=>H//==
    . scase: H=>//= =>w[[H1 H2]] [v][[H3 H4]]
      scase: (w.decLe v)=>//H5 /== ->->
      omega
    move: H=>//=[H1 [H2 H3]]
    exists x; constructor
    . omega
    exists y; constructor
    . omega
    move: H2
    sby scase: (x.decLe y)
    )

------------  Experiments with dep-typed choose

-- An alternative version of Gen.choose that in addition to
-- the generator gives a proof for the range of its values
def choose' (lo hi : Nat) (h : lo ≤ hi := by simp) :
  CGen (λ v => lo ≤ v ∧ v ≤ hi) :=
  Subtype.mk (Gen.choose lo hi h)
             (by sby intro v; apply Iff.intro)

/-
Now, what we could do is to redefine the Gen constructors,
making them keep the proofs that were used for their construction
in a way we defined choose'.

This makes this calculus of generators much closer to a
program logic where each statement comes with pre/postconditions
regarding the nature of its arguments and the resulting
generator. For instance, choose' above now features the
postcondition that preserves information about its inputs.

This will allow us to write the following program, which
is currently unexpressible:

def xyGenInstance : Gen (ℕ × ℕ) := do
  let x <- choose 0 200
  let y <- choose x 200 // needs the proof that 0 <= x <= 200
  pure (x, y)
-/


def main := IO.print =<< sampleN 10 (genSortedBetween 2 10).val
