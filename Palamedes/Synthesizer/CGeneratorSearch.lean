import Palamedes.Gen
import Palamedes.CorrectGen
import Palamedes.RuleSets
import Palamedes.Total
import Palamedes.Data.List
import Palamedes.Data.Stack.Stack
import Palamedes.Data.STLC.Term
import Palamedes.Data.STLC.Ty
import Palamedes.Data.STLC.Context
import Palamedes.Data.Tree
import Palamedes.Data.Unit
import Palamedes.Data.Nat
import Palamedes.Data.Bool
import Palamedes.Data.Color
import Palamedes.Util

open Gen CorrectGen

section Guards

macro "goal_is_mergeable" : tactic =>
  `(tactic|
    first
      | change _ ↔ _ ∧ _
      | change _ ↔ (_ && _) = true)

macro "goal_is_not_fold_list" : tactic =>
  `(tactic|
    (fail_if_success
      (first
        | change _ ↔ List.fold _ _ _ = _
        | change _ ↔ @List.fold _ (_ → _ : Type) _ _ _ _ = _)))

macro "goal_is_not_fold_tree" : tactic =>
  `(tactic|
    (fail_if_success
      (first
        | change _ ↔ Tree.fold _ _ _ = _
        | change _ ↔ @Tree.fold _ (_ → _ : Type) _ _ _ _ = _)))

macro "goal_is_not_fold_stack" : tactic =>
  `(tactic|
    (fail_if_success
      (first
        | change _ ↔ Stack.fold _ _ _ _ = _
        | change _ ↔ @Stack.fold (_ → _ : Type) _ _ _ _ _ = _)))

macro "goal_is_not_fold_ty" : tactic =>
  `(tactic|
    (fail_if_success
      (first
        | change _ ↔ Ty.fold _ _ _ = _
        | change _ ↔ @Ty.fold (_ → _ : Type) _ _ _ _ = _)))

macro "goal_is_not_fold_term" : tactic =>
  `(tactic|
    (fail_if_success
      (first
        | change _ ↔ Term.fold _ _ _ _ _ = _
        | change _ ↔ @Term.fold (_ → _ : Type) _ _ _ _ _ _ = _)))

macro "goal_is_eq_or_and" : tactic =>
  `(tactic|
    first
      | guard_target = CorrectGen (fun _ => _ = _)
      | guard_target = CorrectGen (fun _ => _ ∧ _))

macro "goal_is_or" : tactic =>
  `(tactic| guard_target = CorrectGen (fun _ => _ ∨ _))

end Guards

section Simplifiers

macro "simp_predicate" : tactic => `(tactic| try simp [guard, Option.bind_eq_some_iff, -beq_iff_eq, -Bool.true_and, *])

macro "simp_bexp" : tactic => `(tactic|
  try simp only [bind, Option.bind, pure, Option.some_inj, ← Bool.eq_iff_iff])

end Simplifiers

section Normalizers

macro "preprocess" : tactic =>
  `(tactic|
    (funext
     simp_predicate))

section Merges

macro "rw_list_merge" : tactic =>
  `(tactic|
    (goal_is_mergeable
     rw [← List.merge_accuM]
     apply and_congr))

macro "rw_tree_merge" : tactic =>
  `(tactic|
    (goal_is_mergeable
     rw [← Tree.merge_accuM]
     apply and_congr))

macro "rw_stack_merge" : tactic =>
  `(tactic|
    (goal_is_mergeable
     rw [← Stack.merge_accuM]
     apply and_congr))

macro "rw_ty_merge" : tactic =>
  `(tactic|
    (goal_is_mergeable
     rw [← Ty.merge_accuM]
     apply and_congr))

macro "rw_term_merge" : tactic =>
  `(tactic|
    (goal_is_mergeable
     rw [← Term.merge_accuM]
     apply and_congr))

macro "rw_and_iff_list" : tactic =>
  `(tactic| conv =>
        pattern fun _ => _
        intro _ acc _
        /- TODO: this is overly specific, we don't want to limit this to cases where the goal looks like (acc _)
           How do we reference the current goal and pass that, whatever it is, to ←Bool.and_true? -/
        try conv => (arg 3; fail_if_success {guard_target = _ && _}; rw [←Bool.and_true (acc _), Bool.and_comm])
        try conv => (arg 2; fail_if_success {guard_target = _ && _}; rw [←Bool.and_true (acc _), Bool.and_comm]))

macro "rw_and_iff_tree" : tactic =>
  `(tactic| conv =>
        pattern fun _ => _
        intro accL _ accR _
        /- TODO: this is overly specific, we don't want to limit this to cases where the goal looks like (accL _ && accR _)
           How do we reference the current goal and pass that, whatever it is, to ←Bool.and_true? -/
        try conv => (arg 3; fail_if_success {guard_target = _ && _ && _}; rw [←Bool.and_true (accL _ && accR _), Bool.and_comm]; try rw [←Bool.and_assoc])
        try conv => (arg 2; fail_if_success {guard_target = _ && _ && __}; rw [←Bool.and_true (accL _ && accR _), Bool.and_comm]; try rw [←Bool.and_assoc]))

end Merges

section Coercions

macro "list_coerce_fold" : tactic =>
  `(tactic|
    -- todo: the bool lemma in List.coerce_to_fold (in Data.List) is overfitting to the evenLen example
    (first
      | goal_is_not_fold_list; conv => rhs; lhs; apply List.coerce_to_fold (by rflm) (by intros; simp_all [- Bool.not_eq_eq_eq_not, -beq_iff_eq]; rflm)
      | goal_is_not_fold_list; conv => rhs; lhs; apply congrFun; apply List.coerce_to_fold (by rflm) (by intros; simp_all [- Bool.not_eq_eq_eq_not, -beq_iff_eq]; rflm)
      | skip))

macro "tree_coerce_fold" : tactic =>
  `(tactic|
    (first
      | goal_is_not_fold_tree; conv => rhs; lhs; apply (Tree.coerce_to_fold (by aesop) (by intros; simp_all; rflm))
      | goal_is_not_fold_tree; conv => rhs; lhs; apply congrFun; apply (Tree.coerce_to_fold (by aesop) (by intros; simp_all; rflm))
      | skip))

macro "stack_coerce_fold" : tactic =>
  `(tactic|
    (first
      | goal_is_not_fold_stack; conv => rhs; lhs; apply (Stack.coerce_to_fold (by rflm) (by intros; simp_all; rflm) (by intros; simp_all; rflm))
      | goal_is_not_fold_stack; conv => rhs; lhs; apply congrFun; apply (Stack.coerce_to_fold (by rflm) (by intros; simp_all; rflm) (by intros; simp_all; rflm))
      | skip))

macro "ty_coerce_fold" : tactic =>
  `(tactic|
    (first
      | goal_is_not_fold_ty; conv => rhs; lhs; apply Ty.coerce_to_fold
      | goal_is_not_fold_ty; conv => rhs; lhs; apply congrFun; apply Ty.coerce_to_fold
      | skip ))

macro "term_coerce_fold" : tactic =>
  `(tactic|
    (first
      | goal_is_not_fold_term; conv => rhs; lhs; apply (Term.coerce_to_fold (by rflm) (by aesop) (by intros; simp_all; rflm) (by intros; simp_all; rflm))
      | goal_is_not_fold_term; conv => rhs; lhs; apply congrFun; apply (Term.coerce_to_fold (by rflm) (by aesop) (by intros; simp_all; rflm) (by intros; simp_all; rflm))
      | skip))

end Coercions

section ConvertToAccuM

macro "list_convert_to_accuM" : tactic =>
  `(tactic|
    (first
      | rw [← List.fold_accu_Option_true] <;> (try library_search); done
      | rw [← List.fold_accu_Option_function]; (try library_search); done
      | rw [← List.fold_accu_Option_function_true] <;> simp_bexp <;> (try library_search); done
      | rw [← List.fold_accu_Option_basic]; done
      | rw_and_iff_list; rw [← List.fold_accu_cond, Option.some.injEq]; (try aesop); done))

macro "tree_convert_to_accuM" : tactic =>
  `(tactic|
    (first
      | rw [← Tree.fold_accu_Option_true]; (try library_search); done
      | rw [← Tree.fold_accu_Option_function]; (try library_search); done
      | rw [← Tree.fold_accu_Option_function_true]; (try intros; simp_bexp; library_search); done
      | rw [← Tree.fold_accu_Option_basic]; (try library_search); done
      | rw_and_iff_tree; rw [← Tree.fold_accu_cond, Option.some.injEq]; (try aesop); done))

macro "stack_convert_to_accuM" : tactic =>
  `(tactic|
    (first
      | rw [← Stack.fold_accu_Option_true (by library_search) (by library_search)]; done
      | rw [← Stack.fold_accu_Option_function (by library_search) (by library_search)]; done
      | rw [← Stack.fold_accu_Option_function_true] <;> (simp_bexp; library_search); done
      | rw [← Stack.fold_accu_Option_basic]; (try library_search); done))

macro "ty_convert_to_accuM" : tactic =>
  `(tactic|
    (first
      | rw [← Ty.fold_accu_Option_true] <;> (try library_search); done
      | rw [← Ty.fold_accu_Option_function]; (try library_search); done
      | rw [← Ty.fold_accu_Option_function_true]; (simp_bexp; library_search); done
      | rw [← Ty.fold_accu_Option_basic]; done))

macro "term_convert_to_accuM" : tactic =>
  `(tactic|
    (first
      | rw [← Term.fold_accu_Option_true]; (try library_search); done
      | rw [← Term.fold_accu_Option_function]; (try library_search); done
      | rw [← Term.fold_accu_Option_function_true] <;> (intros; simp_bexp; library_search); done
      | rw [← Term.fold_accu_Option_function_Option] <;> (try aesop); done
      | rw [← Term.fold_accu_Option_basic]; done))

end ConvertToAccuM

macro "norm_for_List_unfold" : tactic =>
  `(tactic|
    (preprocess
     (repeat' rw_list_merge) <;> (first
                                  | list_coerce_fold; list_convert_to_accuM
                                  | simp; list_coerce_fold; list_convert_to_accuM)))

macro "norm_for_Tree_unfold" : tactic =>
  `(tactic|
    (preprocess
     (repeat' rw_tree_merge) <;> (first
                                  | tree_coerce_fold; tree_convert_to_accuM
                                  | simp; tree_coerce_fold; tree_convert_to_accuM)))

macro "norm_for_Stack_unfold" : tactic =>
  `(tactic|
    (preprocess
     (repeat' rw_stack_merge) <;> (stack_coerce_fold; stack_convert_to_accuM)))

macro "norm_for_Ty_unfold" : tactic =>
  `(tactic|
    (preprocess
     (repeat' rw_ty_merge) <;> (ty_coerce_fold; ty_convert_to_accuM)))

macro "norm_for_Term_unfold" : tactic =>
  `(tactic|
    (preprocess
     (repeat' rw_term_merge) <;> (term_coerce_fold; term_convert_to_accuM)))

macro "norm_for_pure" : tactic =>
  `(tactic| (
    funext
    unfold_matches
    simp_predicate
    first
      | rfl
      | exact Eq.comm))

macro "norm_for_pick" : tactic =>
  `(tactic| (
    funext
    simp_predicate
    try simp [← Decidable.or_iff_not_imp_left]
    rfl))

macro "norm_for_bind" : tactic =>
  `(tactic| (
    funext
    simp_predicate
    first
      | rfl
      | apply exists_congr; intro; rw [true_and]))

macro "norm_for_bind'" : tactic =>
  `(tactic| (
    funext
    simp_predicate
    rw [exists_comm]
    first
      | rfl
      | apply exists_congr; intro; rw [true_and]))

macro "norm_for_elements" : tactic =>
  `(tactic|
    (funext
     simp_predicate
     first
       | rfl
       | rw [getElem?_eq_some_iff_indexesOf_getElem?_eq_some]))

end Normalizers

section AesopRules

add_aesop_rules safe (rule_sets := [synthesis]) [
  (by (repeat apply duncurry); intro),
  (by apply convert (by norm_for_pure) (s_pure _)),
]

add_aesop_rules unsafe (rule_sets := [synthesis]) [
  (by assumption),
  (by apply convert (by norm_for_pick) (s_pick _ _)),
  (by apply convert (by norm_for_bind) (s_bind _ _)),
  (by apply convert (by norm_for_bind') (s_bind _ _)), -- TODO Fix this
  (by goal_is_eq_or_and; apply convert (by norm_for_List_unfold) (List.s_unfold _)),
  (by goal_is_eq_or_and; apply convert (by norm_for_Tree_unfold) (Tree.s_unfold _)),
  (by goal_is_eq_or_and; apply convert (by norm_for_Stack_unfold) (Stack.s_unfold _)),
  (by goal_is_eq_or_and; apply convert (by norm_for_Term_unfold) (Term.s_unfold _)),
  (by apply s_arbUnit),
  (by apply s_arbBool),
  (by apply s_arbColor),
  (by apply s_black),
  (by apply s_red),
  (by apply s_arbNat),
  (by apply s_arbTy),
  (by apply s_arbLabel),
  (by apply s_arbAtom _),
  (by apply s_gt),
  (by apply s_lt_partial),
  (by apply s_between_partial),
  (by apply (s_between (by first | aesop | omega))),
  (by apply convert (by norm_for_elements) (s_elements_partial _)),
]

add_aesop_rules 5% (rule_sets := [synthesis]) [
  (by goal_is_or; clear_unused_assumptions; apply s_caseBool (by nth_assumption 0) (by intros; rflm)),
  (by goal_is_or; clear_unused_assumptions; apply s_caseBool (by nth_assumption 1) (by intros; rflm)),
  (by goal_is_or; clear_unused_assumptions; apply s_caseColor (by nth_assumption 0) (by intros; rflm)),
  (by goal_is_or; clear_unused_assumptions; apply s_caseColor (by nth_assumption 1) (by intros; rflm)),
  (by goal_is_or; clear_unused_assumptions; apply s_caseTy (by nth_assumption 0) (by intros; rflm)),
  (by goal_is_or; clear_unused_assumptions; apply s_caseTy (by nth_assumption 1) (by intros; rflm)),
  (by goal_is_or; clear_unused_assumptions; apply s_caseNat (by nth_assumption 0) (by intros; rflm)),
  (by goal_is_or; clear_unused_assumptions; apply s_caseNat (by nth_assumption 1) (by intros; rflm)),
]

end AesopRules

section API

macro "cgenerator_search" : tactic =>
  `(tactic|
    aesop
      (rule_sets := [-default, -builtin, synthesis])
      (config := {enableSimp := false, maxRuleApplications := 1000}))

macro "cgenerator_search?" : tactic =>
  `(tactic|
    aesop?
      (rule_sets := [-default, -builtin, synthesis])
      (config := {enableSimp := false, maxRuleApplications := 1000}))

end API
