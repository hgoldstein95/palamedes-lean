From Coq Require Import Classes.DecidableClass.
From Coq Require Import Lia.
From Coq Require Import ZArith.

Definition int := Z.
Variable stlc_term: Type.
Variable stlc_ty: Type.
Variable stlc_tyctx: Type.
Variable is_const : stlc_term -> Prop.
Variable is_abs : stlc_term -> Prop.
Variable is_var : stlc_term -> Prop.
Variable typing : stlc_tyctx -> stlc_term -> stlc_ty -> Prop.
Variable num_app : stlc_term -> int -> Prop.
Variable num_arr: stlc_ty -> int -> Prop.
Variable stlc_ty_nat : stlc_ty -> Prop.
Variable stlc_ty_arr1 : stlc_ty -> stlc_ty -> Prop.
Variable stlc_ty_arr2 : stlc_ty -> stlc_ty -> Prop.
Variable stlc_const : stlc_term -> int -> Prop.
Variable stlc_id : stlc_term -> int -> Prop.
Variable stlc_app1 : stlc_term -> stlc_term -> Prop.
Variable stlc_app2 : stlc_term -> stlc_term -> Prop.
Variable stlc_abs_ty : stlc_term -> stlc_ty -> Prop.
Variable stlc_abs_body : stlc_term -> stlc_term -> Prop.
Variable stlc_tyctx_emp : stlc_tyctx -> Prop.
Variable stlc_tyctx_hd : stlc_tyctx -> stlc_ty -> Prop.
Variable stlc_tyctx_tl : stlc_tyctx -> stlc_tyctx -> Prop.

Lemma stlc_term_destruct (term: stlc_term) : (exists c, stlc_const term c) \/ (exists id, stlc_id term id) \/ (exists t1 t2, stlc_app1 term t1 /\ stlc_app2 term t2) \/ (exists ty body, stlc_abs_ty term ty /\ stlc_abs_body term body).
Admitted.

Lemma stlc_typing_abs_tau_destruct (gamma: stlc_tyctx) (v: stlc_term) (tau: stlc_ty) (ty: stlc_ty):
  typing gamma v tau -> stlc_abs_ty v ty -> stlc_ty_arr1 tau ty /\ exists body_ty, stlc_ty_arr2 tau body_ty.
Admitted.

Lemma stlc_typing_app_tau_destruct (gamma: stlc_tyctx) (v: stlc_term) (tau: stlc_ty) (t1: stlc_term) (t2: stlc_term):
  typing gamma v tau -> stlc_app1 v t1 -> stlc_app2 v t2 ->
  exists func_ty arg_ty, stlc_ty_arr1 func_ty arg_ty /\ stlc_ty_arr2 func_ty tau /\ typing gamma t1 func_ty /\ typing gamma t2 arg_ty.
Admitted.

Lemma stlc_tyctx_cons (ty: stlc_ty) (gamma: stlc_tyctx): exists v, stlc_tyctx_hd v ty /\ stlc_tyctx_tl v gamma.
Admitted.

Lemma stlc_num_app_geq_0  (v: stlc_term) (n: int) : num_app v n -> (0 <= n)%Z.
Admitted.
#[export] Hint Resolve stlc_num_app_geq_0: core.

Lemma stlc_num_app_abs_body_eq (v: stlc_term) (body: stlc_term) (n: int): stlc_abs_body v body -> num_app v n -> num_app body n.
Admitted.
#[export] Hint Resolve stlc_num_app_abs_body_eq: core.

Lemma stlc_num_app_abs_body_eq_rev (v: stlc_term) (body: stlc_term) (n: int): stlc_abs_body v body -> num_app body n -> num_app v n.
Admitted.
#[export] Hint Resolve stlc_num_app_abs_body_eq_rev: core.

Lemma stlc_num_app_app_rev (v: stlc_term) (t1: stlc_term) (t2: stlc_term) (n: int):
  (stlc_app1 v t1 -> stlc_app2 v t2 -> num_app v n -> exists m1 m2, num_app t1 m1 /\ num_app t2 m2 /\ (m1 + m2 = n - 1))%Z.
Admitted.

Lemma stlc_abd_typing_rev (gamma: stlc_tyctx) (v: stlc_term) (tau: stlc_ty) (ty: stlc_ty) (body: stlc_term) (body_ty: stlc_ty) (gamma1: stlc_tyctx) :
  typing gamma v tau -> stlc_abs_ty v ty -> stlc_abs_body v body -> stlc_tyctx_hd gamma1 ty -> stlc_tyctx_tl gamma1 gamma -> typing gamma1 body body_ty.
Admitted.
#[export] Hint Resolve stlc_abd_typing_rev: core.

Lemma stlc_id_is_var (v: stlc_term) (id: int) : stlc_id v id -> is_var v.
Admitted.
#[export] Hint Resolve stlc_id_is_var: core.

Lemma stlc_const_is_const (v: stlc_term) (c: int): stlc_const v c -> is_const v.
Admitted.
#[export] Hint Resolve stlc_const_is_const: core.

Lemma stlc_const_typing_nat (gamma: stlc_tyctx) (v: stlc_term) (tau: stlc_ty) (c: int): stlc_const v c -> typing gamma v tau -> stlc_ty_nat tau.
Admitted.
#[export] Hint Resolve stlc_const_typing_nat: core.

Lemma stlc_num_arr_geq_0 (tau: stlc_ty) (n: int): (num_arr tau n -> n >= 0)%Z.
Admitted.
#[export] Hint Resolve stlc_num_arr_geq_0: core.

Lemma stlc_num_arr_arr (tau: stlc_ty) (tau_body: stlc_ty) (m: int):
  stlc_ty_arr2 tau tau_body -> (num_arr tau_body (m - 1) <-> num_arr tau m)%Z.
Admitted.

Lemma stlc_const_num_app_0 (v: stlc_term) (n: int): (is_const v -> num_app v n -> n = 0)%Z.
Admitted.
#[export] Hint Resolve stlc_const_num_app_0: core.

Lemma stlc_typing_num_arr (gamma: stlc_tyctx) (v: stlc_term) (tau: stlc_ty) : typing gamma v tau -> exists n, num_arr tau n.
Admitted.

Ltac destr :=
  match goal with
  | [ H: _ /\ _ |- _]  => destruct H
  | [ H: exists _, _|- _]  => destruct H
  end.

Lemma gen_term_size_dec_dec: (forall num_arr_tau, (num_arr_tau >= 0 -> (forall num, (num >= 0 -> (forall gamma, (forall tau, (num_arr tau num_arr_tau -> (forall v, ((typing gamma v tau /\ num_app v num) -> ((num = 0 /\ typing gamma v tau /\ num_app v 0) \/ (~num = 0 /\ (exists x_2, ((x_2 /\ (exists arg_tau, (exists b_1, (0 <= b_1 /\ b_1 = num /\ (exists num_app_func, (0 <= num_app_func /\ num_app_func < b_1 /\ (exists b_3, (0 <= b_3 /\ b_3 = (num - num_app_func) /\ (exists num_app_arg, (0 <= num_app_arg /\ num_app_arg < b_3 /\ (exists func_ty, (stlc_ty_arr1 func_ty arg_tau /\ stlc_ty_arr2 func_ty tau /\ (exists num_arr_func_ty, (num_arr func_ty num_arr_func_ty /\ (exists num_arr_tau_1, (num_arr_tau_1 >= 0 /\ num_arr_tau_1 = num_arr_func_ty /\ (exists num_1, (num_1 >= 0 /\ num_arr_tau_1 >= 0 /\ (num_1 < num \/ (num_1 <= num /\ num_arr_tau_1 < num_arr_tau)) /\ num_1 = num_app_func /\ (exists x_9, (stlc_ty_arr1 x_9 arg_tau /\ stlc_ty_arr2 x_9 tau /\ (exists tau_1, (num_arr tau_1 num_arr_tau_1 /\ tau_1 = x_9 /\ (exists func, (typing gamma func tau_1 /\ num_app func num_1 /\ (exists num_arr_arg_ty, (num_arr arg_tau num_arr_arg_ty /\ (exists num_arr_tau_2, (num_arr_tau_2 >= 0 /\ num_arr_tau_2 = num_arr_arg_ty /\ (exists num_2, (num_2 >= 0 /\ num_arr_tau_2 >= 0 /\ (num_2 < num \/ (num_2 <= num /\ num_arr_tau_2 < num_arr_tau)) /\ num_2 = num_app_arg /\ (exists tau_2, (num_arr tau_2 num_arr_tau_2 /\ tau_2 = arg_tau /\ (exists arg, (typing gamma arg tau_2 /\ num_app arg num_2 /\ stlc_app1 v func /\ stlc_app2 v arg)))))))))))))))))))))))))))))))))) \/ (~x_2 /\ (exists tau1, (exists tau2, (stlc_ty_arr1 tau tau1 /\ stlc_ty_arr2 tau tau2 /\ (exists num_arr_tau2, (num_arr tau2 num_arr_tau2 /\ (exists num_arr_tau_3, (num_arr_tau_3 >= 0 /\ num_arr_tau_3 = num_arr_tau2 /\ (exists num_3, (num_3 >= 0 /\ num_arr_tau_3 >= 0 /\ (num_3 < num \/ (num_3 <= num /\ num_arr_tau_3 < num_arr_tau)) /\ num_3 = num /\ (exists x_15, (stlc_tyctx_hd x_15 tau1 /\ stlc_tyctx_tl x_15 gamma /\ (exists tau_3, (num_arr tau_3 num_arr_tau_3 /\ tau_3 = tau2 /\ (exists body, (typing x_15 body tau_3 /\ num_app body num_3 /\ stlc_abs_ty v tau1 /\ stlc_abs_body v body)))))))))))))))))))))))))))))%Z.
Proof.
  intros. destruct H2 as (Htyping & Hnum). destruct (Z.eqb_spec num 0)%Z.
  - left. subst. intuition.
  - right. intuition.
    destruct (stlc_term_destruct v) as [(c & Hconst) | [ (id & Hvar) | [ (t1 & t2 & Happ1 & Happ2) | (ty & body & Hty & Hbody) ] ] ].
    + assert (num = 0)%Z; eauto. intuition.
    + admit.
    + exists True. left. intuition.
      destruct (stlc_typing_app_tau_destruct gamma v tau t1 t2) as (func_tau & arg_tau & Harr1 & Harr2 & Htyping1 & Htyping2); auto.
      exists arg_tau. exists num. intuition.
      destruct (stlc_num_app_app_rev v t1 t2 num) as (m1 & m2 & Hm1 & Hm2 & Hm1m2n); auto.
      exists m1.
      assert (0 <= m1)%Z; eauto. assert (0 <= m2)%Z; eauto.
      intuition; eauto.
      exists (num - m1)%Z. intuition.
      exists m2. intuition; eauto.
      exists func_tau. intuition.
      assert (num_arr func_tau (num_arr_tau + 1)%Z). {
        rewrite <- stlc_num_arr_arr; eauto.
        assert (num_arr_tau + 1 - 1 = num_arr_tau)%Z. lia. rewrite H4. auto.      }
      exists (num_arr_tau + 1)%Z. intuition.
      exists (num_arr_tau + 1)%Z. intuition.
      exists m1. intuition.
      exists func_tau. intuition.
      exists func_tau. intuition.
      exists t1. intuition.
      destruct (stlc_typing_num_arr gamma t2 arg_tau) as (num_arr_arg_ty & Hnum_arr_arg_ty); auto.
      exists num_arr_arg_ty. intuition.
      exists num_arr_arg_ty. intuition. eauto.
      exists m2. intuition; eauto.
      exists arg_tau. intuition.
      exists t2. intuition.
    + exists False. right. intuition.
      edestruct (stlc_typing_abs_tau_destruct gamma v tau) as (Htyarr1 & (body_ty & Htyarr2)); eauto.
      exists ty, body_ty. intuition.
      assert (num_arr body_ty (num_arr_tau - 1)%Z). { rewrite stlc_num_arr_arr; eauto. }
      exists (num_arr_tau - 1)%Z. intuition.
      exists (num_arr_tau - 1)%Z. intuition. eauto.
      exists num. intuition. eauto.
      destruct (stlc_tyctx_cons ty gamma) as (gamma1 & Hg1 & Hg2).
      exists gamma1. intuition.
      exists body_ty. intuition.
      exists body. intuition; eauto.
Qed.


Lemma gen_term_size_dec:
  (forall num_arr_tau, (num_arr_tau >= 0 -> (forall num, (num >= 0 -> (forall gamma, (forall tau, (num_arr tau num_arr_tau -> (forall v, ((typing gamma v tau /\ num_app v num) -> ((num = 0 /\ typing gamma v tau /\ num_app v 0) \/ (~num = 0 /\ (exists x_2, ((x_2 /\ typing gamma v tau /\ is_var v) \/ (~x_2 /\ (exists x_4, ((x_4 /\ (exists arg_tau, (exists b_1, (0 <= b_1 /\ b_1 = num /\ (exists num_app_func, (0 <= num_app_func /\ num_app_func < b_1 /\ (exists b_3, (0 <= b_3 /\ b_3 = (num - num_app_func) /\ (exists num_app_arg, (0 <= num_app_arg /\ num_app_arg < b_3 /\ (exists func_ty, (stlc_ty_arr1 func_ty arg_tau /\ stlc_ty_arr2 func_ty tau /\ (exists num_arr_func_ty, (num_arr func_ty num_arr_func_ty /\ (exists num_arr_tau_1, (num_arr_tau_1 >= 0 /\ num_arr_tau_1 = num_arr_func_ty /\ (exists num_1, (num_1 >= 0 /\ num_arr_tau_1 >= 0 /\ (num_arr_tau_1 < num_arr_tau \/ num_1 < num) /\ num_1 = num_app_func /\ (exists x_11, (stlc_ty_arr1 x_11 arg_tau /\ stlc_ty_arr2 x_11 tau /\ (exists tau_2, (num_arr tau_2 num_arr_tau_1 /\ tau_2 = x_11 /\ (exists func, (typing gamma func tau_2 /\ num_app func num_1 /\ (exists num_arr_arg_ty, (num_arr arg_tau num_arr_arg_ty /\ (exists num_arr_tau_2, (num_arr_tau_2 >= 0 /\ num_arr_tau_2 = num_arr_arg_ty /\ (exists num_2, (num_2 >= 0 /\ num_arr_tau_2 >= 0 /\ (num_arr_tau_2 < num_arr_tau \/ num_2 < num) /\ num_2 = num_app_arg /\ (exists tau_3, (num_arr tau_3 num_arr_tau_2 /\ tau_3 = arg_tau /\ (exists arg, (typing gamma arg tau_3 /\ num_app arg num_2 /\ stlc_app1 v func /\ stlc_app2 v arg)))))))))))))))))))))))))))))))))) \/ (~x_4 /\ (exists tau1, (exists tau2, (stlc_ty_arr1 tau tau1 /\ stlc_ty_arr2 tau tau2 /\ (exists num_arr_tau2, (num_arr tau2 num_arr_tau2 /\ (exists num_arr_tau_3, (num_arr_tau_3 >= 0 /\ num_arr_tau_3 = num_arr_tau2 /\ (exists num_3, (num_3 >= 0 /\ num_arr_tau_3 >= 0 /\ (num_arr_tau_3 < num_arr_tau \/ num_3 < num) /\ num_3 = num /\ (exists x_17, (stlc_tyctx_hd x_17 tau1 /\ stlc_tyctx_tl x_17 gamma /\ (exists tau_4, (num_arr tau_4 num_arr_tau_3 /\ tau_4 = tau2 /\ (exists body, (typing x_17 body tau_4 /\ num_app body num_3 /\ stlc_abs_ty v tau1 /\ stlc_abs_body v body))))))))))))))))))))))))))))))))%Z.
Proof.
  intros. destruct H2 as (Htyping & Hnum). destruct (Z.eqb_spec num 0)%Z.
  - left. subst. intuition.
  - right. intuition.
    destruct (stlc_term_destruct v) as [(c & Hconst) | [ (id & Hvar) | [ (t1 & t2 & Happ1 & Happ2) | (ty & body & Hty & Hbody) ] ] ].
    + assert (num = 0)%Z; eauto. intuition.
    + exists True. left. intuition; eauto.
    + exists False. right. intuition.
      exists True. left. intuition.
      destruct (stlc_typing_app_tau_destruct gamma v tau t1 t2) as (func_tau & arg_tau & Harr1 & Harr2 & Htyping1 & Htyping2); auto.
      exists arg_tau. exists num. intuition.
      destruct (stlc_num_app_app_rev v t1 t2 num) as (m1 & m2 & Hm1 & Hm2 & Hm1m2n); auto.
      exists m1.
      assert (0 <= m1)%Z; eauto. assert (0 <= m2)%Z; eauto.
      intuition; eauto.
      exists (num - m1)%Z. intuition.
      exists m2. intuition; eauto.
      exists func_tau. intuition.
      assert (num_arr func_tau (num_arr_tau + 1)%Z). {
        rewrite <- stlc_num_arr_arr; eauto.
        assert (num_arr_tau + 1 - 1 = num_arr_tau)%Z. lia. rewrite H4. auto.      }
      exists (num_arr_tau + 1)%Z. intuition.
      exists (num_arr_tau + 1)%Z. intuition.
      exists m1. intuition.
      exists func_tau. intuition.
      exists func_tau. intuition.
      exists t1. intuition.
      destruct (stlc_typing_num_arr gamma t2 arg_tau) as (num_arr_arg_ty & Hnum_arr_arg_ty); auto.
      exists num_arr_arg_ty. intuition.
      exists num_arr_arg_ty. intuition. eauto.
      exists m2. intuition; eauto.
      exists arg_tau. intuition.
      exists t2. intuition.
    + exists False. right. intuition.
      exists False. right. intuition.
      edestruct (stlc_typing_abs_tau_destruct gamma v tau) as (Htyarr1 & (body_ty & Htyarr2)); eauto.
      exists ty, body_ty. intuition.
      assert (num_arr body_ty (num_arr_tau - 1)%Z). { rewrite stlc_num_arr_arr; eauto. }
      exists (num_arr_tau - 1)%Z. intuition.
      exists (num_arr_tau - 1)%Z. intuition. eauto.
      exists num. intuition. eauto.
      destruct (stlc_tyctx_cons ty gamma) as (gamma1 & Hg1 & Hg2).
      exists gamma1. intuition.
      exists body_ty. intuition.
      exists body. intuition; eauto.
Qed.

Lemma gen_term_size_dec1:(
forall dec, (dec >= 0 -> (forall gamma, (forall tau, (forall num, ((num >= 0 /\ num_arr tau ((dec - num) - num)) -> (forall v, ((~num = 0 /\ (exists x_2, (~x_2 /\ (exists x_4, (x_4 /\ (exists arg_tau, (exists b_1, (0 <= b_1 /\ b_1 = num /\ (exists num_func, (0 <= num_func /\ num_func < b_1 /\ (exists b_3, (0 <= b_3 /\ b_3 = (num - num_func) /\ (exists num_arg, (0 <= num_arg /\ num_arg < b_3 /\ (exists dec_1, (dec_1 >= 0 /\ 0 <= dec_1 /\ dec_1 < dec /\ dec_1 = (((dec - 1) - num_arg) - num_arg) /\ (exists x_12, (stlc_ty_arr1 x_12 arg_tau /\ stlc_ty_arr2 x_12 tau /\ (exists num_0, (num_0 >= 0 /\ num_arr x_12 ((dec_1 - num_0) - num_0) /\ num_0 = num_func /\ (exists func, (typing gamma func x_12 /\ num_app func num_0 /\ v = (((dec - 2) - num_func) - num_func))))))))))))))))))))))) -> (~num = 0 /\ (exists x_2, (~x_2 /\ (exists x_4, (x_4 /\ (exists arg_tau, (exists b_1, (0 <= b_1 /\ b_1 = num /\ (exists num_func, (0 <= num_func /\ num_func < b_1 /\ (exists b_3, (0 <= b_3 /\ b_3 = (num - num_func) /\ (exists num_arg, (0 <= num_arg /\ num_arg < b_3 /\ (exists dec_1, (dec_1 >= 0 /\ 0 <= dec_1 /\ dec_1 < dec /\ dec_1 = (((dec - 1) - num_arg) - num_arg) /\ (exists x_12, (stlc_ty_arr1 x_12 arg_tau /\ stlc_ty_arr2 x_12 tau /\ (exists num_0, (num_0 >= 0 /\ num_arr x_12 ((dec_1 - num_0) - num_0) /\ num_0 = num_func /\ (exists func, (typing gamma func x_12 /\ num_app func num_0 /\ 0 <= v /\ v < dec))))))))))))))))))))))))))))))%Z.
Proof.
  intros. repeat destr. intuition. clear x H2 x0 H4. subst.
  exists False. intuition. exists True. intuition.
  exists x1, num. intuition.
  exists x3. intuition. exists (num - x3)%Z. intuition.
  exists x5. intuition. exists (dec - 1 - x5 - x5)%Z. intuition.
  exists x7. intuition. exists x3. intuition.
  exists x9. intuition.
  eapply stlc_num_arr_arr in H20; eauto. lia.
Qed.

Lemma gen_term_size:
  (forall dec, (dec >= 0 -> (forall num, (num >= 0 -> (forall tau, (dec_pair tau dec num -> (forall gamma, (forall v, ((typing gamma v tau /\ num_app v num) -> (((num = 0) /\ typing gamma v tau /\ num_app v 0) \/ (~(num = 0) /\ (exists x_2, ((x_2 /\ typing gamma v tau /\ is_var v) \/ (~x_2 /\ (exists x_4, ((x_4 /\ (exists arg_tau, (exists b_1, (0 <= b_1 /\ b_1 = num /\ (exists num_func, (0 <= num_func /\ num_func < b_1 /\ (exists b_3, (0 <= b_3 /\ b_3 = (num - num_func) /\ (exists num_arg, (0 <= num_arg /\ num_arg < b_3 /\ (exists a_4, (a_4 > 0 /\ a_4 = dec /\ (exists dec_dec, (0 <= dec_dec /\ dec_dec < a_4 /\ (exists dec_1, (dec_1 >= 0 /\ 0 <= dec_1 /\ dec_1 < dec /\ dec_1 = dec_dec /\ (exists num_0, (num_0 >= 0 /\ num_0 = num_func /\ (exists x_10, (stlc_ty_arr1 x_10 arg_tau /\ stlc_ty_arr2 x_10 tau /\ (exists tau_2, (dec_pair tau_2 dec_1 num_0 /\ tau_2 = x_10 /\ (exists func, (typing gamma func tau_2 /\ num_app func num_0 /\ (exists dec_2, (dec_2 >= 0 /\ 0 <= dec_2 /\ dec_2 < dec /\ dec_2 = dec_dec /\ (exists num_1, (num_1 >= 0 /\ num_1 = num_arg /\ (exists tau_3, (dec_pair tau_3 dec_2 num_1 /\ tau_3 = arg_tau /\ (exists arg, (typing gamma arg tau_3 /\ num_app arg num_1 /\ stlc_app1 v func /\ stlc_app2 v arg)))))))))))))))))))))))))))))))) \/ (~x_4 /\ ((stlc_ty_nat tau /\ is_const v) \/ (exists tau1, (exists tau2, (stlc_ty_arr1 tau tau1 /\ stlc_ty_arr2 tau tau2 /\ (exists a_6, (a_6 > 0 /\ a_6 = dec /\ (exists dec_dec1, (0 <= dec_dec1 /\ dec_dec1 < a_6 /\ (exists dec_3, (dec_3 >= 0 /\ 0 <= dec_3 /\ dec_3 < dec /\ dec_3 = dec_dec1 /\ (exists num_2, (num_2 >= 0 /\ num_2 = num /\ (exists tau_4, (dec_pair tau_4 dec_3 num_2 /\ tau_4 = tau2 /\ (exists x_18, (stlc_tyctx_hd x_18 tau1 /\ stlc_tyctx_tl x_18 gamma /\ (exists body, (typing x_18 body tau_4 /\ num_app body num_2 /\ stlc_abs_ty v tau1 /\ stlc_abs_body v body)))))))))))))))))))))))))))))))))))%Z.
Proof.
  intros. destruct H2 as (Htyping & Hnum). destruct (Z.eqb_spec num 0)%Z.
  - left. subst. intuition.
  - right. intuition.
    destruct (stlc_term_destruct v) as [(c & Hconst) | [ (id & Hvar) | [ (t1 & t2 & Happ1 & Happ2) | (ty & body & Hty & Hbody) ] ] ].
    + exists False. right. intuition.
      exists False. right. intuition.
      left. intuition; eauto.
    + exists True. left. intuition; eauto.
    + exists False. right. intuition.
      exists True. left. intuition.
      destruct (stlc_typing_app_tau_destruct gamma v tau t1 t2) as (func_tau & arg_tau & Harr1 & Harr2 & Htyping1 & Htyping2); auto.
      exists arg_tau. exists num. intuition.
      destruct (stlc_num_app_app_rev v t1 t2 num) as (m1 & m2 & Hm1 & Hm2 & Hm1m2n); auto.
      exists m1.
      assert (0 <= m1)%Z; eauto. assert (0 <= m2)%Z; eauto.
      intuition; eauto.
      exists (num - m1)%Z. intuition.
      exists m2. intuition; eauto.
      exists dec. intuition; eauto.
      destruct (stlc_dec_num_lt_lt tau dec num func_tau m1 arg_tau m2) as (dec1 & Hdec1 & Hdec2 & Hdec1dec); intuition.
      exists dec1. intuition; eauto. exists dec1. intuition; eauto. apply stlc_dec_leq_0 in Hdec1; intuition.
      exists m1. intuition. exists func_tau. intuition.
      exists func_tau. intuition.
      exists t1. intuition.
      exists dec1. intuition. apply stlc_dec_leq_0 in Hdec2; intuition. apply stlc_dec_leq_0 in Hdec2; intuition.
      exists m2. intuition. exists arg_tau. intuition.
      exists t2. intuition.
    + exists False. right. intuition.
      exists False. right. intuition.
      right.
      edestruct (stlc_typing_abs_tau_destruct gamma v tau) as (Htyarr1 & (body_ty & Htyarr2)); eauto.
      exists ty, body_ty. intuition.
      exists dec. intuition. eauto.
      destruct (stlc_dec_num_arr_body_lt tau dec num body_ty) as (dec1 & Hdec1 & Hdec1dec); auto.
      exists (dec1)%Z. intuition; eauto.
      exists (dec1)%Z. intuition; eauto. eapply stlc_dec_leq_0 in Hdec1; eauto. lia.
      exists num. intuition.
      exists (body_ty)%Z. intuition.
      destruct (stlc_tyctx_cons ty gamma) as (gamma1 & Hg1 & Hg2).
      exists gamma1. intuition.
      exists body. intuition; eauto.
Qed.
(* abduction *)

Lemma depth_heap_abduction: (forall d, (0 <= d -> (forall mx, (forall v, ((heap v /\ ((exists u, (depth v u /\ u <= d)) /\ (forall u, (root v u -> u < mx)))) -> ((~leaf v /\ ~mx = 0 /\ d = 0) \/ (~leaf v /\ ~mx = 0 /\ ~d = 0) \/ (leaf v /\ ~mx = 0 /\ ~d = 0) \/ (leaf v /\ mx = 0 /\ ~d = 0) \/ (d = 0 /\ leaf v) \/ (~d = 0 /\ (exists x_1, (~x_1 /\ (exists n, (n < mx /\ (exists d_1, (0 <= d_1 /\ d_1 < d /\ d_1 = (d - 1) /\ (exists lt, (heap lt /\ (exists u, (depth lt u /\ u <= d_1)) /\ (forall u, (root lt u -> u < n)) /\ (exists d_2, (0 <= d_2 /\ d_2 < d /\ d_2 = (d - 1) /\ (exists rt, (heap rt /\ (exists u, (depth rt u /\ u <= d_2)) /\ (forall u, (root rt u -> u < n)) /\ root v n /\ lch v lt /\ rch v rt)))))))))))))))))))%Z.
Proof.
  intros. destruct (Z.eqb_spec d 0)%Z.
  - do 4 right. left. subst. intuition. destruct H0 as (s & Hs & Hs'). eauto. admit.
  - destruct H0 as (Hv & (s & Hs & Hs') & HH).
    destruct (decide_leaf v).
    + do 2 right.
      destruct (Z.eqb mx 0)%Z eqn: Hz; intuition.
    + right.
      destruct (Z.eqb mx 0)%Z eqn: Hz; auto.
      2:{ intuition. }
      do 4 right. intuition.
      exists False. intuition.
      destruct (tree_not_leaf_ex v) as (x & lt & rt & Hx & Hlt & Hrt); auto.
      exists x; eauto. intuition.
      exists (d - 1)%Z. intuition.
      exists lt. intuition; eauto. edestruct (tree_depth_lt_ex) as (d1 & Hd1); eauto. exists d1. intuition; eauto.
      eapply tree_depth_lt_minus_1 in Hlt; eauto. lia.
      exists (d - 1)%Z. intuition.
      exists rt. intuition; eauto. edestruct (tree_depth_rt_ex) as (d1 & Hd1); eauto. exists d1. intuition; eauto.
      eapply tree_depth_rt_minus_1 in Hrt; eauto. lia.
Admitted.



Lemma sized_bst_gen: (
                       forall d, (0 <= d -> (forall lo, (forall hi, (lo < hi -> (forall v, (((forall u, (tree_mem v u -> (lo < u /\ u < hi))) /\ (bst v /\ (forall n, (depth v n -> n <= d)))) -> ((d = 0 /\ leaf v) \/ (~d = 0 /\ (exists x_1, ((x_1 /\ leaf v) \/ (~x_1 /\ (lo + 1) < hi /\ (exists b_3, ((1 + lo) < b_3 /\ b_3 = hi /\ (exists x, (lo < x /\ x < b_3 /\ (exists d_1, (0 <= d_1 /\ d_1 < d /\ d_1 = (d - 1) /\ (exists hi_0, (lo < hi_0 /\ hi_0 = x /\ (exists lt, ((forall u, (tree_mem lt u -> (lo < u /\ u < hi_0))) /\ bst lt /\ (forall n, (depth lt n -> n <= d_1)) /\ (exists d_2, (0 <= d_2 /\ d_2 < d /\ d_2 = (d - 1) /\ (exists hi_1, (x < hi_1 /\ hi_1 = hi /\ (exists rt, ((forall u, (tree_mem rt u -> (x < u /\ u < hi_1))) /\ bst rt /\ (forall n, (depth rt n -> n <= d_2)) /\ root v x /\ lch v lt /\ rch v rt))))))))))))))))))))))))))))%Z.
Proof.
  intros. destruct (Z.eqb_spec d 0)%Z.
  - left. subst. intuition. destruct (tree_bst_depth_ex v) as (d & Hd); eauto. admit.
  - right. intuition.
    destruct (decide_leaf v).
    + exists True. intuition.
    + exists False. right.
      destruct (tree_bst_depth_ex v) as (dd & Hdd); eauto.
      assert (dd <= d)%Z as Hddd; eauto.
      destruct (tree_not_leaf_ex v) as (x & lt & rt & Hx & Hlt & Hrt); auto.
      assert (lo < x /\ x < hi)%Z. { eauto; lia. }
      intuition.
      exists hi. intuition.
      exists x; eauto. intuition.
      exists (d - 1)%Z. intuition.
      exists x; eauto. intuition.
      exists lt. intuition; eauto. apply H2. eauto.
      eapply tree_depth_lt_minus_1 in H5; eauto. lia.
      exists (d - 1)%Z. intuition.
      exists hi; eauto. intuition.
      exists rt. intuition; eauto. apply H2; eauto.
      eapply tree_depth_rt_minus_1 in H5; eauto. lia.
Qed.

Lemma complete_tree_gen: (forall s, (0 <= s -> (forall v, ((depth v s /\ complete v) -> ((s = 0 /\ leaf v) \/ (~s = 0 /\ (exists s_1, (0 <= s_1 /\ s_1 < s /\ s_1 = (s - 1) /\ (exists lt, (depth lt s_1 /\ complete lt /\ (exists s_2, (0 <= s_2 /\ s_2 < s /\ s_2 = (s - 1) /\ (exists rt, (depth rt s_2 /\ complete rt /\ (exists n, (root v n /\ (lch v lt /\ rch v rt)))))))))))))))))%Z.
Proof.
  intros. destruct (Z.eqb_spec s 0)%Z.
  - left. subst. intuition.
  - right. intuition.
    assert (~ leaf v); eauto.
    destruct (tree_not_leaf_ex v) as (x & lt & rt & Hx & Hlt & Hrt); auto.
    exists (s - 1)%Z. intuition.
    exists lt. intuition; eauto.
    exists (s - 1)%Z. intuition.
    exists rt. intuition; eauto.
Qed.

Lemma depth_heap_gen:(
                        forall d, (0 <= d -> (forall mx, (forall v, ((heap v /\ ((exists u, (depth v u /\ u <= d)) /\ (forall u, (root v u -> u < mx)))) -> ((d = 0 /\ leaf v) \/ (~d = 0 /\ (exists x_1, ((x_1 /\ leaf v) \/ (~x_1 /\ (exists n, ((n < mx /\ (exists d_1, ((0 <= d_1 /\ d_1 = (d - 1)) /\ (exists lt, (((d_1 < d /\ d_1 >= 0) /\ heap lt /\ ((exists u, (depth lt u /\ u <= d_1)) /\ (forall u, (root lt u -> u < n)))) /\ (exists d_2, ((0 <= d_2 /\ d_2 = (d - 1)) /\ (exists rt, (((d_2 < d /\ d_2 >= 0) /\ heap rt /\ ((exists u, (depth rt u /\ u <= d_2)) /\ (forall u, (root rt u -> u < n)))) /\ root v n /\ (lch v lt /\ rch v rt)))))))))) \/ (~n < mx /\ leaf v)))))))))))))%Z.
Proof.
  intros. destruct (Z.eqb_spec d 0)%Z.
  - left. subst. intuition. destruct H0 as (s & Hs & Hs'). apply tree_depth_0_leaf. admit.
  - right. intuition. destruct H0 as (s & Hs & Hs').
    destruct (decide_leaf v).
    + exists True. intuition.
    + exists False. right. intuition.
      destruct (tree_not_leaf_ex v) as (x & lt & rt & Hx & Hlt & Hrt); auto.
      exists x; eauto. left. intuition.
      exists (d - 1)%Z. intuition.
      exists lt. intuition; eauto. eapply tree_depth_lt_ex in Hlt; eauto. destruct Hlt as (d1 & Hd1 & Hd1s). exists d1.
      intuition.
      exists (d - 1)%Z. intuition.
      exists rt. intuition; eauto. eapply tree_depth_rt_ex in Hrt; eauto. destruct Hrt as (d1 & Hd1 & Hd1s). exists d1.
      intuition.
Qed.


Lemma ranged_set_gen:
  (forall diff, (0 <= diff -> (forall lo, (forall v, (((forall u, (tree_mem v u -> (lo < u /\ u < (lo + diff)))) /\ bst v) -> (((lo + diff) <= (1 + lo) /\ leaf v) \/ (~(lo + diff) <= (1 + lo) /\ (exists x_2, ((x_2 /\ leaf v) \/ (~x_2 /\ (exists b_2, (((1 + lo) < b_2 /\ b_2 = (lo + diff)) /\ (exists x, ((lo < x /\ x < b_2) /\ (exists diff_1, ((0 <= diff_1 /\ diff_1 = (x - lo)) /\ (exists hi_0, ((hi_0 = (lo + diff_1) /\ hi_0 = x) /\ (exists lt, (((diff_1 < diff /\ diff_1 >= 0) /\ (forall u, (tree_mem lt u -> (lo < u /\ u < hi_0))) /\ bst lt) /\ (exists diff_2, ((0 <= diff_2 /\ diff_2 = ((lo + diff) - x)) /\ (exists hi_1, ((hi_1 = (x + diff_2) /\ hi_1 = (lo + diff)) /\ (exists rt, (((diff_2 < diff /\ diff_2 >= 0) /\ (forall u, (tree_mem rt u -> (x < u /\ u < hi_1))) /\ bst rt) /\ root v x /\ (lch v lt /\ rch v rt)))))))))))))))))))))))))))%Z.
Proof.
  intros. destruct (Z.leb_spec diff 1)%Z.
  - left. intuition.
    destruct (decide_leaf v); intuition.
    destruct (tree_not_leaf_ex v) as (x & lt & rt & Hx & Hlt & Hrt); auto.
    apply tree_root_mem in Hx. apply H2 in Hx. lia.
  - right. intuition.
    destruct (decide_leaf v).
    + exists True. intuition.
    + exists False. right. intuition.
      destruct (tree_not_leaf_ex v) as (x & lt & rt & Hx & Hlt & Hrt); auto.
      exists (lo + diff)%Z. intuition.
      exists x. intuition.
      { apply tree_root_mem in Hx. apply H2 in Hx. lia. }
      { apply tree_root_mem in Hx. apply H2 in Hx. lia. }
      exists (x - lo)%Z. intuition.
      { apply tree_root_mem in Hx. apply H2 in Hx. lia. }
      exists x. intuition.
      exists lt. intuition; eauto.
      { apply tree_root_mem in Hx. apply H2 in Hx. lia. }
      { apply tree_root_mem in Hx. apply H2 in Hx. lia. }
      { eapply tree_mem_lch_mem in H4; eauto. apply H2 in H4. lia. }
      exists (lo + diff - x)%Z. intuition.
      { apply tree_root_mem in Hx. apply H2 in Hx. lia. }
      exists (x + (lo + diff - x))%Z. intuition.
      exists rt. intuition; eauto.
      { apply tree_root_mem in Hx. apply H2 in Hx. lia. }
      { apply tree_root_mem in Hx. apply H2 in Hx. lia. }
      { eapply tree_mem_rch_mem in H4; eauto. apply H2 in H4. lia. }
Qed.


Lemma depth_tree_gen:
(forall s, (0 <= s -> (forall v, ((exists u, (depth v u/\ u <= s)) -> ((s = 0/\ leaf v) \/ (~s = 0/\ (exists x_1, ((x_1/\ leaf v) \/ (~x_1/\ (exists s_1, ((0 <= s_1/\ s_1 = (s - 1))/\ (exists lt, (((s_1 < s/\ s_1 >= 0)/\ (exists u, (depth lt u/\ u <= s_1)))/\ (exists s_2, ((0 <= s_2/\ s_2 = (s - 1))/\ (exists rt, (((s_2 < s/\ s_2 >= 0)/\ (exists u, (depth rt u/\ u <= s_2)))/\ (exists n, (root v n/\ (lch v lt/\ rch v rt))))))))))))))))))))%Z.
Proof.
  intros. destruct (Z.eqb_spec size 0).
  - left. subst. intuition.
  - right. intuition.
    destruct (decide_emp v).
    + apply list_len_not_0_not_emp in H1; auto. intuition.
    + exists (size - 1)%Z. intuition.
      destruct (list_not_emp_ex_hd _ H0) as (x & Hx).
      destruct (list_not_emp_ex_tl _ H0) as (l & Hl).
      exists l. intuition; eauto.
Qed.
