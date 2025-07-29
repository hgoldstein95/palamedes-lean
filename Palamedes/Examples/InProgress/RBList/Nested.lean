import Palamedes.Synthesizer
import Palamedes.Data.Color

open Gen CorrectGen

namespace RBList

@[simp]
def rrAuxList : List Color → Bool → Bool := λ t isRedChild =>
 match t with
 | .nil => true
 | .cons .red tl => !isRedChild && rrAuxList tl true
 | .cons .black tl => rrAuxList tl false

@[simp]
def rrList : List Color → Bool := λ xs => rrAuxList xs false

@[simp]
def bhList : List Color → Nat → Bool := λ xs height =>
 match xs with
 | .nil => height == 1
 | .cons .red tl => bhList tl height
 | .cons .black tl => height > 0 && bhList tl (height - 1)

open Gen CorrectGen

/-
def genRRFold : Gen (List Color) := by
  -- generator_search (fun xs => rrList xs = true)
  let cg : CorrectGen (fun xs => rrList xs = true) := by
   (goal_is_eq_or_and; apply convert (by
      funext
      simp_predicate
      goal_is_not_fold_list; conv => rhs; lhs; apply congrFun; apply List.coerce_to_fold (by rflm) (by
        intros x xs
        cases x <;> simp_all [- Bool.not_eq_eq_eq_not] <;> funext

      )
      rw [← List.fold_accu_cond_bool]
      simp
      aesop
    ) (List.s_unfold _))
    cgenerator_search
  let g : Gen (List Color) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
  let _ : Gen.total g := by
    totality
  exact g

def genBHFold (height : Nat) : Gen (List Color) := by
  generator_search (fun xs => bhList xs height = true) -/
