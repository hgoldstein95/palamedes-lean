Require Import List.
Require Import Lia.
Import ListNotations.

From Coq Require Export Logic.Classical_Pred_Type.

From MyProject Require Import Tactics.


Inductive hd : list nat -> nat -> Prop :=
| lhd1: forall u u', u = u' -> hd [u] u'
| lhd2: forall l u u', u = u' ->  hd (u :: l) u'.

Inductive tl : list nat -> list nat -> Prop :=
| ltl2: forall u l l', l = l' ->  tl (u :: l) l'.

Inductive len : list nat -> nat -> Prop :=
| llen1: len [] 0
| llen2: forall l u n, len (l) n -> len (u :: l) (n + 1).

Inductive emp : list nat -> Prop :=
| lemp1: emp [].

Inductive sorted : list nat -> Prop :=
| lsorted1: sorted []
| lsorted2: forall n, sorted [n]
| lsorted3: forall n n' l, sorted (n' :: l) -> n <= n' -> sorted (n :: n' :: l).

Hint Constructors hd: core.
Hint Constructors tl: core.
Hint Constructors emp: core.
Hint Constructors len: core.
Hint Constructors sorted: core.

Lemma list_emp_no_hd : forall l, (forall x, ((emp l) -> ~(hd l x))). Proof.
        intros. destruct l. unfold not. intro. my_inversion H0. my_inversion H.
 Qed. Hint Resolve list_emp_no_hd: core.

Lemma list_emp_no_tl : forall l, (forall l1, ((emp l) -> ~(tl l l1))). Proof.     intros. destruct l. unfold not. intro. my_inversion H0. my_inversion H. Qed. Hint Resolve list_emp_no_tl: core.

Lemma list_no_emp_exists_tl : forall l, (exists l1, (~(emp l) -> (tl l l1))). Proof.
        intros. destruct l.
    - econstructor. unfold not. intros. exfalso. apply H. constructor. Unshelve. constructor.
    - repeat econstructor.
Qed. Hint Resolve list_no_emp_exists_tl: core.

Lemma list_no_emp_exists_hd : forall l, (exists x, (~(emp l) -> (hd l x))). Proof.     intro. destruct l.
    - econstructor. unfold not. intro. exfalso. apply H. constructor. Unshelve. constructor.
    - repeat econstructor. Qed. Hint Resolve list_no_emp_exists_hd: core.

Lemma list_hd_no_emp : forall l, (forall x, ((hd l x) -> ~(emp l))). Proof.
        intros. destruct l.
    - my_inversion H.
    - unfold not. intro. my_inversion H0.
 Qed. Hint Resolve list_hd_no_emp: core.

Lemma list_tl_no_emp : forall l, (forall l1, ((tl l l1) -> ~(emp l))). Proof.
        intros. destruct l.
    - my_inversion H.
    - unfold not. intro. my_inversion H0.
 Qed. Hint Resolve list_tl_no_emp: core.

Lemma list_len_0_emp : forall l, ((emp l) -> (len l 0)). Proof.
    intros. my_inversion H. constructor.
 Qed. Hint Resolve list_len_0_emp: core.

Lemma list_positive_len_is_not_emp : forall l, (forall n, (((len l n) /\ (n > 0)) -> ~(emp l))). Proof.
        intros. simp. induction l.
    - my_inversion H. my_inversion H0.
    - unfold not. intro. my_inversion H1.
 Qed. Hint Resolve list_positive_len_is_not_emp: core.
(*
Lemma list_is_not_emp_positive_len : forall l, (exists n, (~(emp l) -> ((len l n) /\ (n > 0)))). Proof.
    intro. eexists. induction l; split.
    - unfold not in H. exfalso. apply H. constructor.
    - unfold not in H. exfalso. apply H. constructor.
    - unfold not in IHl. econstructor. clear H.
    - unfold not in IHl. admit.

 Qed. Hint Resolve list_is_not_emp_positive_len: core.

Lemma list_tl_len_plus_1 : forall l, (forall l1, (forall n, (((tl l l1) /\ (len l1 n)) -> (len l (n + 1))))). Proof. Qed. Hint Resolve list_tl_len_plus_1: core.

Lemma list_emp_sorted : forall l, ((emp l) -> (sorted l)). Proof. Qed. Hint Resolve list_emp_sorted: core.

Lemma list_single_sorted : forall l, ((len l 1) -> (sorted l)). Proof. Qed. Hint Resolve list_single_sorted: core.

Lemma list_tl_sorted : forall l, (forall l1, (((tl l l1) /\ (sorted l)) -> (sorted l1))). Proof. Qed. Hint Resolve list_tl_sorted: core.

Lemma list_hd_sorted : forall l, (forall l1, (forall x, (forall y, (((tl l l1) /\ (sorted l)) -> ((emp l1) \/ (((hd l1 y) /\ (hd l x)) -> (x <= y))))))). Proof. Qed. Hint Resolve list_hd_sorted: core.

Lemma list_sorted_hd : forall l, (forall l1, (forall x, (forall y, (((tl l l1) /\ ((sorted l1) /\ ((hd l y) /\ ((hd l1 x) /\ (y <= x))))) -> (sorted l))))). Proof. Qed. Hint Resolve list_sorted_hd: core.
 *)