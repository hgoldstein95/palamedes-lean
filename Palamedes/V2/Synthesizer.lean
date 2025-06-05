import Palamedes.V2.Gen
import Palamedes.V2.CorrectGen
import Palamedes.V2.RuleSets
import Palamedes.V2.Total
import Palamedes.V2.Tactics
import Palamedes.V2.Data.List
import Palamedes.V2.Data.Unit
import Palamedes.V2.Data.Bool
import Palamedes.V2.Data.Nat
import Mathlib.Tactic.FailIfNoProgress

open Gen CorrectGen

macro "simp_list_predicate" : tactic =>
  `(tactic|
    first
      | rw [← List.fold_accu_Option_true]; (try aesop); done
      | rw [← List.fold_accu_Option_function]; (try aesop); done
      | rw [← List.fold_accu_Option_function_true]; (try aesop); done
      | rw [← List.fold_accu_Option_basic]; (try aesop); done)

macro "simp_predicate" : tactic =>
  `(tactic|
    first
      | funext
        simp [guard, *]
        first
          | exact Eq.comm
          | simp_list_predicate
          | apply exists_congr; intro; rw [true_and]
          | rfl
      | rfl)

macro "gapply " t:term : tactic =>
  `(tactic| apply convert (by simp_predicate) $t)

add_aesop_rules unsafe (rule_sets := [synthesis]) [
  (by fail_if_no_progress intros),
  (by assumption),
  (by gapply (cpure _)),
  (by gapply (cpick _ _)),
  (by gapply (cbind _ _)),
  (by gapply (List.cunfold _)),
  (by gapply carbUnit),
  (by gapply carbBool),
  (by gapply carbNat),
  (by gapply cgt),
  (by gapply cbetween_partial),
  (by gapply (cbetween (by first | aesop | omega))),
]

add_aesop_rules 5% (rule_sets := [synthesis]) [
  (by apply caseBool (by assumption)),
  (by apply caseNat (by assumption))
]

add_aesop_rules unsafe (rule_sets := [totality]) [
  Total.total_pick,
  Total.total_bind,
  Total.total_assume,
  Total.total_indexed,
  Total.total_internalizeProofs,
  Total.total_map,
  Total.total_pure,
  Total.List.total_unfold,
  Total.total_Bool_rec,
  Total.total_Nat_rec
]
