import Palamedes.Synthesizer
import Palamedes.Data.Color

open Gen CorrectGen

namespace RBList

@[simp]
def rrAuxList : List Color → Bool → Bool := λ t isRedChild =>
 match t with
 | .nil => true
 | .cons c tl =>
   if (fun c => c = .red) c then (fun c => !c) isRedChild && rrAuxList tl ((fun _ _ => true) c isRedChild)
                                else (fun _ => true) isRedChild && rrAuxList tl ((fun _ _ => false) c isRedChild)

@[simp]
def rrList : List Color → Bool := λ xs => rrAuxList xs false

@[simp]
def bhList : List Color → Nat → Bool := λ xs height =>
 match xs with
 | .nil => height == 1
 | .cons h tl => if h == .red then bhList tl height else height > 0 && bhList tl (height - 1)

open Gen CorrectGen

set_option palamedes.debug true

def genRRFold : Gen (List Color) := by
  -- generator_search (fun xs => rrList xs = true)
  let cg : CorrectGen (fun xs => rrList xs = true) := by
    (goal_is_eq_or_and; apply convert (by
      funext
      simp_predicate
      goal_is_not_fold_list;
      conv => rhs; lhs; apply congrFun; apply List.coerce_to_fold (by rflm) (by
        intros; simp_all [- Bool.not_eq_eq_eq_not]; rflm)
      rw [← List.fold_accu_cond]
      rw [Option.some.injEq]
    ) (List.s_unfold _))
    ((repeat apply duncurry); intro)
    ((repeat apply duncurry); intro)
    (goal_is_or; clear_unused_assumptions; apply s_caseBool (by nth_assumption 1) (by intros; rflm))
    · (goal_is_or; clear_unused_assumptions; apply s_caseBool (by nth_assumption 0) (by intros; rflm))
      · (apply convert (by norm_for_pick) (s_pick _ _))
        · (apply convert (by norm_for_pure) (s_pure _))
        · (apply convert (by norm_for_bind) (s_bind _ _))
          · (apply s_black)
          · ((repeat apply duncurry); intro)
            (apply convert (by norm_for_pure) (s_pure _))
      · (apply convert (by norm_for_pick) (s_pick _ _))
        · (apply convert (by norm_for_pure) (s_pure _))
        · (apply convert (by norm_for_bind) (s_bind _ _))
          · (apply s_arbColor)
          · ((repeat apply duncurry); intro)
            (apply convert (by norm_for_pure) (s_pure _))
    · (goal_is_or; clear_unused_assumptions; apply s_caseBool (by nth_assumption 0) (by intros; rflm))
      · (apply convert (by norm_for_bind) (s_bind _ _))
        · (apply s_arbColor)
        · ((repeat apply duncurry); intro)
          (goal_is_or; clear_unused_assumptions; apply s_caseColor (by nth_assumption 0) (by intros; rflm))
          · (apply convert (by norm_for_pick) (s_pick _ _))
            · (apply convert (by norm_for_pure) (s_pure _))
            · (apply convert (by norm_for_pure) (s_pure _))
          · (apply convert (by norm_for_pure) (s_pure _))
      · (apply convert (by norm_for_bind) (s_bind _ _))
        · (apply s_arbColor)
        · ((repeat apply duncurry); intro)
          (apply convert (by norm_for_pure) (s_pure _))
  let g : Gen (List Color) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
  let _ : Gen.total g := by
    totality
  exact g

def genBHFold (height : Nat) : Gen (List Color) := by
  generator_search (fun xs => bhList xs height = true)
