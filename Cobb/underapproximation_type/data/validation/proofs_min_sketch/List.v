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

Inductive list_mem: list nat -> nat -> Prop :=
| lmem1: forall l u, list_mem (u :: l) u
| lmem2: forall l u v, list_mem l u -> list_mem (v :: l) u.

Inductive sorted : list nat -> Prop :=
| lsorted1: sorted []
| lsorted2: forall n, sorted [n]
| lsorted3: forall n n' l, sorted (n' :: l) -> n <= n' -> sorted (n :: n' :: l).

Inductive uniq : list nat -> Prop :=
| luniq1 : uniq []
| luniq2 : forall n, uniq [n]
| luniq3 : forall n l, uniq l -> not (list_mem l n) -> uniq (n :: l).

Hint Constructors hd: core.
Hint Constructors tl: core.
Hint Constructors emp: core.
Hint Constructors len: core.
Hint Constructors sorted: core.
Hint Constructors uniq: core.
Hint Constructors list_mem: core.




Lemma list_emp_no_hd : forall l, (forall x, (emp l -> ~hd l x)). Proof.
    intros. destruct l. unfold not. intro. my_inversion H0. my_inversion H.
 Qed. Hint Resolve list_emp_no_hd: core.


Lemma list_emp_no_tl : forall l, (forall l1, (emp l -> ~tl l l1)). Proof.
    intros. destruct l. unfold not. intro. my_inversion H0. my_inversion H.
 Qed. Hint Resolve list_emp_no_tl: core.


Lemma list_no_emp_exists_tl : forall l, (exists l1, (~emp l -> tl l l1)). Proof.
    intros. destruct l.
    - econstructor. unfold not. intros. exfalso. apply H. constructor. Unshelve. constructor.
    - repeat econstructor.
Qed. Hint Resolve list_no_emp_exists_tl: core.

Lemma list_no_emp_exists_hd : forall l, (exists x, (~emp l -> hd l x)). Proof.
    intro. destruct l.
    - econstructor. unfold not. intro. exfalso. apply H. constructor. Unshelve. constructor.
    - repeat econstructor.
Qed. Hint Resolve list_no_emp_exists_hd: core.


Lemma list_hd_no_emp : forall l, (forall x, (hd l x -> ~emp l)). Proof.
    intros. destruct l.
    - my_inversion H.
    - unfold not. intro. my_inversion H0.
Qed. Hint Resolve list_hd_no_emp: core.


Lemma list_tl_no_emp : forall l, (forall l1, (tl l l1 -> ~emp l)). Proof.
    intros. destruct l.
    - my_inversion H.
    - unfold not. intro. my_inversion H0.
Qed. Hint Resolve list_tl_no_emp: core.

Lemma list_len_geq_0 : forall l, (forall n, (len l n -> n >= 0)). Proof.
    intros. lia.
Qed. Hint Resolve list_len_geq_0: core.

Lemma list_hd_leq : forall l, (forall x, (forall y, ((x <= y /\ hd l y) -> (forall u, (hd l u -> x <= u))))). Proof.
    intros. simp. my_inversion H0; clear H0.
    -  my_inversion H1.
    - my_inversion H1.
 Qed. Hint Resolve list_hd_leq: core.

Lemma list_len_0_emp : forall l, (emp l -> len l 0). Proof.
    intros. my_inversion H. constructor.
 Qed. Hint Resolve list_len_0_emp: core.

Lemma list_emp_len_0 : forall l, (forall n, ((emp l /\ len l n) -> n = 0)). Proof.
    intros. simp. my_inversion H. my_inversion H0.
 Qed. Hint Resolve list_emp_len_0: core.

Lemma list_positive_len_is_not_emp : forall l, (forall n, ((len l n /\ n > 0) -> ~emp l)). Proof.
    intros. simp. induction l.
    - my_inversion H. my_inversion H0.
    - unfold not. intro. my_inversion H1.
 Qed. Hint Resolve list_positive_len_is_not_emp: core.

Lemma list_tl_len_plus_1 : forall l, (forall l1, (forall n, (tl l l1 -> (len l1 n <-> len l (n + 1))))). Proof.
    intros. split; intro.
    - my_inversion H. auto.
    - my_inversion H. my_inversion H0. assert (n0 = n). lia. subst. auto.
 Qed. Hint Resolve list_tl_len_plus_1: core.

Lemma list_hd_is_mem : forall l, (forall u, (hd l u -> list_mem l u)). Proof.
    intros. my_inversion H. auto. auto.
 Qed. Hint Resolve list_hd_is_mem: core.

Lemma list_emp_no_mem : forall l, (forall u, (emp l -> ~list_mem l u)). Proof.
    intros. my_inversion H. unfold not. intro. my_inversion H0.
 Qed. Hint Resolve list_emp_no_mem: core.

Lemma list_tl_mem : forall l, (forall l1, (forall u, ((tl l l1 /\ list_mem l1 u) -> list_mem l u))). Proof.
    intros. simp. my_inversion H. constructor. auto.
 Qed. Hint Resolve list_tl_mem: core.

Lemma list_cons_mem : forall l, (forall l1, (forall u, ((tl l l1 /\ list_mem l u) -> (list_mem l1 u \/ hd l u)))). Proof.
    intros. simp. my_inversion H. my_inversion H0. right. auto. left. auto.
 Qed. Hint Resolve list_cons_mem: core.

Lemma list_emp_sorted : forall l, (emp l -> sorted l). Proof.
    intros. my_inversion H. constructor.
Qed. Hint Resolve list_emp_sorted: core.

Lemma list_single_sorted : forall l, (len l 1 -> sorted l). Proof.
    intros. my_inversion H. my_inversion H2.
    - constructor.
    - lia.
 Qed. Hint Resolve list_single_sorted: core.

Lemma list_tl_sorted : forall l, (forall l1, ((tl l l1 /\ sorted l) -> sorted l1)). Proof.
    intros. simp. my_inversion H. my_inversion H0. constructor.
 Qed. Hint Resolve list_tl_sorted: core.

Lemma list_hd_sorted : forall l, (forall l1, (forall x, (forall y, ((tl l l1 /\ sorted l) -> (emp l1 \/ ((hd l1 y /\ hd l x) -> x <= y)))))). Proof.
    intros. simp. my_inversion H. my_inversion H0.
    - left. constructor.
    - right. intro. simp. clear H. my_inversion H1.
    + my_inversion H2.
    + my_inversion H2.
 Qed. Hint Resolve list_hd_sorted: core.

Lemma list_sorted_hd : forall l, (forall l1, (forall x, (forall y, ((tl l l1 /\ (sorted l1 /\ (hd l y /\ (hd l1 x /\ y <= x)))) -> sorted l)))). Proof.
    intros. simp. induction l. my_inversion H1. my_inversion H1; clear H1. constructor. my_inversion H; clear H. my_inversion H2. constructor; auto. constructor; auto.
 Qed. Hint Resolve list_sorted_hd: core.

Lemma list_emp_unique : forall l, (emp l -> uniq l). Proof.
    intros. my_inversion H. constructor.
 Qed. Hint Resolve list_emp_unique: core.

Lemma list_tl_unique : forall l, (forall l1, ((tl l l1 /\ uniq l) -> uniq l1)). Proof.
    intros. simp. my_inversion H. my_inversion H0. constructor.
 Qed. Hint Resolve list_tl_unique: core.

Lemma not_list_hd_unique : not (forall l, (forall l1, (forall x, ((tl l l1 /\ (uniq l /\ hd l1 x))) -> ~list_mem l1 x))). Proof.
    apply ex_not_not_all. exists (0 :: [1]). apply ex_not_not_all. exists [1]. apply ex_not_not_all. exists 1. unfold not. intros. apply H.
    - split; auto. split; auto. constructor; auto. unfold not. intros. my_inversion H0. my_inversion H4.
    - constructor.
 Qed. Hint Resolve not_list_hd_unique: core.

 Lemma list_hd_unique : (forall l, (forall l1, (forall x, ((tl l l1 /\ (uniq l /\ hd l x))) -> ~list_mem l1 x))). Proof.
    intros. simp. my_inversion H. my_inversion H1.
    - unfold not. intro. my_inversion H2.
    - clear H. clear H1. my_inversion H0. unfold not. intro. my_inversion H.
 Qed. Hint Resolve list_hd_unique: core.

Lemma list_hd_tl_unique : forall l, (forall l1, (forall x, ((tl l l1 /\ (uniq l1 /\ (hd l x /\ ~list_mem l1 x))) -> uniq l))). Proof.
    intros. simp. my_inversion H; clear H. my_inversion H1.
    - auto.
    - constructor; auto.
 Qed. Hint Resolve list_hd_tl_unique: core.

 Lemma list_unique_hd_tl : forall l, (exists l1, (exists x, ((uniq l /\ ~emp l) -> (hd l x /\ (tl l l1 /\ ~list_mem l1 x))))). Proof.
    intros. destruct l.
    - repeat econstructor; destruct H; unfold not in H0; exfalso; apply H0; constructor. Unshelve. constructor. constructor.
    - eexists. exists n. intro. split.
        + auto. Unshelve. auto.
        + split.
            * auto.
            * unfold not. intro. my_inversion H. my_inversion H1. my_inversion H0.
  Qed. Hint Resolve list_unique_hd_tl: core.