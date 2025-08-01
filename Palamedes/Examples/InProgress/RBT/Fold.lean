import Palamedes.Synthesizer
import Palamedes.Sample

open Gen CorrectGen

namespace RBTFold

@[simp]
def rrFold (t : Tree (Color × α)) : Bool :=
  Tree.fold
    (fun bl c br isRedChild => if c.fst == .red then !isRedChild && bl true && br true else bl false && br false)
    (fun _ => true)
    t
    false

@[simp]
def bhFold (t : Tree (Color × α)) (height : Nat) : Bool :=
  Tree.fold
    (fun bl c br h => if c.fst == .red then bl h && br h else h >= 0 && bl (h - 1) && br (h - 1))
    (fun h => h == 0)
    t
    height

@[simp]
def isBSTFold (t : Tree (α × Nat)) : Nat × Nat -> Bool := fun (lo, hi) =>
  Tree.fold
        (fun bl x br s =>
          match s with
          | (sl, sr) => (decide (sl ≤ x.snd) && decide (x.snd ≤ sr)) && bl (sl, x.snd - 1) && br (x.snd + 1, sr))
        (fun _ => true) t (lo, hi)

set_option palamedes.debug true
set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

/-

 (goal_is_eq_or_and; apply convert (by norm_for_Tree_unfold) (Tree.s_unfold _))
    ((repeat apply duncurry); intro)
    ((repeat apply duncurry); intro)
    ((repeat apply duncurry); intro)
    (apply convert (by norm_for_pick) (s_pick _ _))
    · (apply convert (by norm_for_pure) (s_pure _))
    · (apply convert (by norm_for_bind) (s_bind _ _))
      · (apply s_between_partial)
      · ((repeat apply duncurry); intro)
        (apply convert (by norm_for_bind) (s_bind _ _))
        · (apply s_arbUnit)
        · ((repeat apply duncurry); intro)
          (apply convert (by norm_for_bind) (s_bind _ _))
          · (apply s_arbUnit)
          · ((repeat apply duncurry); intro)
            (apply convert (by norm_for_pure) (s_pure _))

            -/

def genBSTFold (lo hi : Nat) : Gen (Tree (Color × Nat)) := by
  -- generator_search (fun t => isBSTFold t (lo, hi) = true)
  let cg : CorrectGen (fun t : Tree (Color × Nat) => isBSTFold t (lo, hi) = true) := by
    (goal_is_eq_or_and; apply convert (by norm_for_Tree_unfold) (Tree.s_unfold _))
    ((repeat apply duncurry); intro)
    ((repeat apply duncurry); intro)
    ((repeat apply duncurry); intro)
    (apply convert (by norm_for_pick) (s_pick _ _))
    · (apply convert (by norm_for_pure) (s_pure _))
    · (apply convert (by norm_for_pick) (s_pick _ _))
      · (apply convert (by norm_for_bind) (s_bind _ _))
        · (apply s_between_partial)
        · ((repeat apply duncurry); intro)
          (apply convert (by norm_for_bind) (s_bind _ _))
          · (apply s_arbUnit)
          · ((repeat apply duncurry); intro)
            (apply convert (by norm_for_bind) (s_bind _ _))
            · (apply s_arbUnit)
            · ((repeat apply duncurry); intro)
              (apply convert (by norm_for_pure) (s_pure _))
      · (apply convert (by norm_for_bind) (s_bind _ _))
        · (apply s_between_partial)
        · ((repeat apply duncurry); intro)
          (apply convert (by norm_for_bind) (s_bind _ _))
          · (apply s_arbUnit)
          · ((repeat apply duncurry); intro)
            (apply convert (by norm_for_bind) (s_bind _ _))
            · (apply s_arbUnit)
            · ((repeat apply duncurry); intro)
              (apply convert (by norm_for_pure) (s_pure _))
  let g : Gen (Tree (Color × ℕ)) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
  let _ : Gen.total g := by
    totality
  exact g

def genRRFold : Gen (Tree (Color × Nat)) := by
  -- generator_search (fun t => rrFold t = true)
  let cg : CorrectGen (fun t : Tree (Color × Nat) => rrFold t = true) := by
    (goal_is_eq_or_and; apply convert (by norm_for_Tree_unfold) (Tree.s_unfold _))
    ((repeat apply duncurry); intro)
    ((repeat apply duncurry); intro)
    (goal_is_or; clear_unused_assumptions; apply s_caseBool (by nth_assumption 1) (by intros; rflm))
    · (apply convert (by norm_for_pick) (s_pick _ _))
      · (apply convert (by norm_for_pure) (s_pure _))
      · (goal_is_or; clear_unused_assumptions; apply s_caseBool (by nth_assumption 0) (by intros; rflm))
        · (apply convert (by norm_for_bind) (s_bind _ _))
          · (apply s_arbNat)
          · ((repeat apply duncurry); intro)
            (apply convert (by norm_for_pure) (s_pure _))
        · (apply convert (by norm_for_pick) (s_pick _ _))
          · (apply convert (by norm_for_bind) (s_bind _ _))
            · (apply s_arbNat)
            · ((repeat apply duncurry); intro)
              (apply convert (by norm_for_pure) (s_pure _))
          · (apply convert (by norm_for_bind) (s_bind _ _))
            · (apply s_arbNat)
            · ((repeat apply duncurry); intro)
              (apply convert (by norm_for_pure) (s_pure _))
    · (apply convert (by norm_for_pick) (s_pick _ _))
      · (apply convert (by norm_for_bind) (s_bind _ _))
        · (apply s_arbNat)
        · ((repeat apply duncurry); intro)
          (apply convert (by norm_for_pick) (s_pick _ _))
          · (apply convert (by norm_for_pick) (s_pick _ _))
            · (apply convert (by norm_for_pure) (s_pure _))
            · (apply convert (by norm_for_pure) (s_pure _))
          · (goal_is_or; clear_unused_assumptions; apply s_caseBool (by nth_assumption 0) (by intros; rflm))
            · (apply convert (by norm_for_pick) (s_pick _ _))
              · (apply convert (by norm_for_pure) (s_pure _))
              · (apply convert (by norm_for_pure) (s_pure _))
            · (apply convert (by norm_for_pure) (s_pure _))
      · (apply convert (by norm_for_bind) (s_bind _ _))
        · (apply s_arbNat)
        · ((repeat apply duncurry); intro)
          (apply convert (by norm_for_pick) (s_pick _ _))
          · (apply convert (by norm_for_pick) (s_pick _ _))
            · (apply convert (by norm_for_pure) (s_pure _))
            · (apply convert (by norm_for_pure) (s_pure _))
          · (apply convert (by norm_for_pure) (s_pure _))
  let g : Gen (Tree (Color × ℕ)) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
  let _ : Gen.total g := by
    totality
  exact g

def genBHFold (height : Nat)  : Gen (Tree (Color × Nat)) := by
  -- generator_search (fun t => bhFold t height = true)
  let cg : CorrectGen (fun t : Tree (Color × Nat) => bhFold t height = true) := by
    cgenerator_search?
  let g : Gen (Tree (Color × ℕ)) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
  let _ : Gen.total g := by
    totality
  exact g

@[simp]
def isRRBHFold (height : Nat) (t : Tree (Color × Nat)) : Bool :=
  bhFold t height = true ∧ rrFold t = true

def genRRBHFold (height : Nat) : Gen (Tree (Color × Nat)) := by
  -- generator_search (fun t => isRRBHFold height t = true)
  let cg : CorrectGen (fun t : Tree (Color × Nat) => isRRBHFold height t = true) := by
    goal_is_eq_or_and; apply convert (by norm_for_Tree_unfold) (Tree.s_unfold _)
    repeat ((repeat apply duncurry); intro)
    (goal_is_or; clear_unused_assumptions; apply s_caseNat (by nth_assumption 0) (by intros; rflm))
    . (goal_is_or; clear_unused_assumptions; apply s_caseBool (by nth_assumption 0) (by intros; rflm))
      . (goal_is_or; clear_unused_assumptions; apply s_caseBool (by nth_assumption 0) (by intros; rflm))
        . (goal_is_or; clear_unused_assumptions; apply s_caseBool (by nth_assumption 0) (by intros; rflm))
          . apply convert (by norm_for_pick) (s_pick _ _)
            . apply convert (by norm_for_pure) (s_pure _)
            . apply convert (by norm_for_bind) (s_bind _ _)
              . apply s_arbNat
              . intro
                apply convert (by norm_for_pure) (s_pure _)
          . apply convert (by norm_for_bind) (s_bind _ _)
            . apply s_arbNat
            . intro
              (apply convert (by norm_for_pick) (s_pick _ _))
              · (apply convert (by norm_for_pick) (s_pick _ _))
                · (apply convert (by norm_for_pure) (s_pure _))
                · (apply convert (by norm_for_pure) (s_pure _))
              · (apply convert (by norm_for_pure) (s_pure _))
        . (goal_is_or; clear_unused_assumptions; apply s_caseBool (by nth_assumption 0) (by intros; rflm))
          . apply convert (by norm_for_pick) (s_pick _ _)
            . (apply convert (by norm_for_bind) (s_bind _ _))
              · (apply s_arbNat)
              · ((repeat apply duncurry); intro)
                (apply convert (by norm_for_pick) (s_pick _ _))
                · (apply convert (by norm_for_pick) (s_pick _ _))
                  · (apply convert (by norm_for_pure) (s_pure _))
                  · (apply convert (by norm_for_pure) (s_pure _))
                · (apply convert (by norm_for_pick) (s_pick _ _))
                  · (apply convert (by norm_for_pure) (s_pure _))
                  · (apply convert (by norm_for_pure) (s_pure _))
            . apply convert (by norm_for_bind) (s_bind _ _)
              . apply s_arbNat
              . intro
                cgenerator_search
          . cgenerator_search
      . (goal_is_or; clear_unused_assumptions; apply s_caseBool (by nth_assumption 0) (by intros; rflm))
        . (goal_is_or; clear_unused_assumptions; apply s_caseBool (by nth_assumption 0) (by intros; rflm))
          . cgenerator_search
          . cgenerator_search
        . (goal_is_or; clear_unused_assumptions; apply s_caseBool (by nth_assumption 0) (by intros; rflm))
          . cgenerator_search
          . cgenerator_search
    . repeat ((repeat apply duncurry); intro)
      (goal_is_or; clear_unused_assumptions; apply s_caseBool (by nth_assumption 0) (by intros; rflm))
      . (goal_is_or; clear_unused_assumptions; apply s_caseBool (by nth_assumption 0) (by intros; rflm))
        . (goal_is_or; clear_unused_assumptions; apply s_caseBool (by nth_assumption 0) (by intros; rflm))
          . cgenerator_search
          . cgenerator_search
        . (goal_is_or; clear_unused_assumptions; apply s_caseBool (by nth_assumption 0) (by intros; rflm))
          . cgenerator_search
          . cgenerator_search
      . (goal_is_or; clear_unused_assumptions; apply s_caseBool (by nth_assumption 0) (by intros; rflm))
        . (goal_is_or; clear_unused_assumptions; apply s_caseBool (by nth_assumption 0) (by intros; rflm))
          . cgenerator_search
          . cgenerator_search
        . (goal_is_or; clear_unused_assumptions; apply s_caseBool (by nth_assumption 0) (by intros; rflm))
          . cgenerator_search
          . cgenerator_search
  let g : Gen (Tree (Color × ℕ)) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
  let _ : Gen.total g := by
    totality
  exact g

/-
@[simp]
def isRBTFold (lo hi height : Nat) (t : Tree (Color × Nat)) : Bool :=
  isBSTFold t (lo, hi) = true ∧ bhFold t height = true ∧ rrFold t = true

def genRBTFold (lo hi height : Nat) : Gen (Tree (Color × Nat)) := by
  -- generator_search (fun t => isRBTFold lo hi height t = true) allow_partial
  let cg : CorrectGen (fun t => isRBTFold lo hi height t = true) := by
    goal_is_eq_or_and; apply convert (by norm_for_Tree_unfold) (Tree.s_unfold _)
    repeat ((repeat apply duncurry); intro)
    (goal_is_or; clear_unused_assumptions; apply s_caseNat (by nth_assumption 0) (by intros; rflm))
    .
  let g : Gen (Tree (Color × ℕ)) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
  let _ : Gen.total g := by
    totality
  exact g -/

end RBTFold
