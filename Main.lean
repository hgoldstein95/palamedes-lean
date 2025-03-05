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
  simp_all only [fold_foldM]
  apply synth_unfoldM
  intro b
  simp_all only [Option.some.injEq, ListF_or]
  cases k with
  | zero =>
    cases b with
    | zero =>
      simp_all only [true_and, Nat.add_one_ne_zero, and_false, exists_const, exists_false, or_false]
      apply synth_pure
    | succ
      n =>
      simp_all only [Nat.add_one_ne_zero, false_and, Nat.add_right_cancel_iff, exists_eq_right, false_or]
      apply synth_bind_arb
      intro a
      apply synth_pure
  | succ n =>
    cases b with
    | zero =>
      simp_all only [true_and, Nat.add_one_ne_zero, and_false, exists_const, exists_false, or_false]
      apply synth_pure
    | succ
      n_1 =>
      simp_all only [Nat.add_one_ne_zero, false_and, Nat.add_right_cancel_iff, exists_eq_right, false_or]
      apply synth_bind_arb
      intro a
      apply synth_pure

def genEvenLengthTwos :
    CGen (λ (v : List Nat) => List.foldrM (λ x b => do guard (x == 2); pure (not b)) true v = Option.some true) := by
  aesop

def genLengthKTwos {k : Nat} :
    CGen (λ (v : List Nat) =>
      List.foldr (λ _ l => l + 1) 0 v = k ∧
      List.foldrM (λ x () => guard (x == 2)) () v = Option.some ()) := by
  simp_all only [fold_foldM, guard, beq_iff_eq, ite, failure, Option.pure_def, merge_foldM, Option.bind_eq_bind,
    deforest_decidable_bind, Option.none_bind, Option.some_bind]

  apply synth_unfoldM
  intro b
  simp_all only [deforest_decidable_eq, reduceCtorEq, Option.some.injEq, decidable_or, beq_iff_eq, and_false,
    false_or, ListF_or, Prod.exists, exists_and_right]
  obtain ⟨fst, snd⟩ := b
  simp_all only [Prod.mk.injEq, and_true]
  cases k with
  | zero =>
    cases fst with
    | zero =>
      simp_all only [true_and, Nat.add_one_ne_zero, and_false, exists_const, or_false]
      apply synth_pure
    | succ
      n =>
      simp_all only [Nat.add_one_ne_zero, false_and, Nat.add_right_cancel_iff, exists_eq_right_right, exists_eq_right,
        false_or]
      apply synth_bind_arb
      intro a
      apply synth_pure
  | succ n =>
    cases fst with
    | zero =>
      simp_all only [true_and, Nat.add_one_ne_zero, and_false, exists_const, or_false]
      apply synth_pure
    | succ
      n_1 =>
      simp_all only [Nat.add_one_ne_zero, false_and, Nat.add_right_cancel_iff, exists_eq_right_right, exists_eq_right,
        false_or]
      apply synth_bind_arb
      intro a
      apply synth_pure

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

def main := IO.print =<< sampleN 10 (genSortedBetween 2 10).val
