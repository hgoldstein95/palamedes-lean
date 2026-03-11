Require Import Setoid.
Require Import Lia.

From Coq Require Export Logic.Classical_Pred_Type.

From MyProject Require Import Tactics.

Inductive RBTree : Type :=
| RBLeaf
| RBNode (color : bool) (l : RBTree) (v : nat) (r : RBTree).

Inductive rb_leaf : RBTree -> Prop :=
| rb_leaf_i: rb_leaf RBLeaf.

Inductive rb_root  : RBTree -> nat -> Prop :=
| rb_root_i: forall v v' c l r, v = v' -> rb_root (RBNode c l v r) v'.

Inductive rb_root_color : RBTree  -> bool -> Prop :=
| rb_root_color_i: forall v c c' l r, c = c' -> rb_root_color (RBNode c l v r) c'.

Inductive rb_lch : RBTree -> RBTree -> Prop :=
| rb_lch_i: forall v c l l' r, l = l' -> rb_lch (RBNode c l v r) l'.

Inductive rb_rch  : RBTree -> RBTree  -> Prop :=
| rb_rch_i: forall v c l r' r, r = r' -> rb_rch (RBNode c l v r) r'.

Inductive num_black : RBTree -> nat -> Prop :=
| num_black_leaf : num_black RBLeaf 0
| num_black_node_true : forall v l r n,
  num_black l n -> num_black r n ->
  num_black (RBNode true l v r) n
| num_black_node_false : forall v l r n,
  num_black l n -> num_black r n ->
  num_black (RBNode false l v r) (1 + n).

Inductive no_red_red : RBTree -> Prop :=
| no_red_red_leaf : no_red_red RBLeaf
| no_red_red_true : forall v l r, no_red_red l -> no_red_red r -> ~ (rb_root_color l true) -> ~(rb_root_color r true) -> no_red_red ((RBNode true l v r))
| no_red_red_false : forall v l r, no_red_red l -> no_red_red r -> no_red_red ((RBNode false l v r)).

Hint Constructors rb_leaf: core.
Hint Constructors rb_root: core.
Hint Constructors rb_root_color: core.
Hint Constructors rb_lch: core.
Hint Constructors rb_rch: core.
Hint Constructors num_black: core.
Hint Constructors no_red_red: core.
Hint Unfold not: core.

Lemma rbtree_leaf_is_leaf : forall l, (forall l2, ((rb_leaf l /\ rb_leaf l2) -> l = l2)). Proof.
  intros. simp. my_inversion H. my_inversion H0.
 Qed. Hint Resolve rbtree_leaf_is_leaf: core.

Lemma rbtree_rb_leaf_no_rb_root : forall l, (forall x, (rb_leaf l -> ~rb_root l x)).
Proof.
intros.
  destruct H. unfold not. intros. my_inversion H.
Qed.
Hint Resolve rbtree_rb_leaf_no_rb_root: core.


Lemma rbtree_rb_leaf_no_rb_root_color : forall l, (forall x, (rb_leaf l -> ~rb_root_color l x)). Proof. intros.
  destruct H. unfold not. intros. my_inversion H. Qed. Hint Resolve rbtree_rb_leaf_no_rb_root_color: core.

Lemma rbtree_no_rb_leaf_exists_rb_root : forall l, (exists x, (~rb_leaf l -> rb_root l x)). Proof.
  intros. induction l.
  - repeat econstructor. unfold not. intros. destruct H. constructor.
  - repeat econstructor. Unshelve. constructor.
 Qed. Hint Resolve rbtree_no_rb_leaf_exists_rb_root: core.


Lemma rbtree_rb_leaf_no_ch : forall l, (forall l1, (rb_leaf l -> ~(rb_lch l l1 \/ rb_rch l l1))). Proof.
  intros. unfold not. intros. induction H0. my_inversion H0. my_inversion H. induction H. my_inversion H0.
Qed. Hint Resolve rbtree_rb_leaf_no_ch: core.

Lemma rbtree_no_rb_leaf_exists_ch : forall l, (exists l1, (exists l2, (~rb_leaf l -> (rb_lch l l1 /\ rb_rch l l2)))). Proof.
  intros. induction l.
  - repeat econstructor.
    + destruct H. constructor. Unshelve. constructor. constructor.
    + destruct H. constructor.
  - repeat econstructor.
Qed. Hint Resolve rbtree_no_rb_leaf_exists_ch: core.

Lemma rbtree_no_rb_leaf_exists_rb_root_color : forall l, (exists x, (~rb_leaf l -> rb_root_color l x)). Proof.
  intros. induction l.
  - repeat econstructor. intro. destruct H. constructor. Unshelve. constructor.
  - repeat econstructor.
Qed. Hint Resolve rbtree_no_rb_leaf_exists_rb_root_color: core.

Lemma rbtree_rb_root_no_rb_leaf : forall l, (forall x, (rb_root l x -> ~rb_leaf l)). Proof.
  intros. destruct H. unfold not. intros. my_inversion H0.
 Qed. Hint Resolve rbtree_rb_root_no_rb_leaf: core.

Lemma rbtree_rb_root_color_no_rb_leaf : forall l, (forall x, (rb_root_color l x -> ~rb_leaf l)). Proof.
  intros.
  destruct l. my_inversion H. unfold not. intros. my_inversion H0.

 Qed. Hint Resolve rbtree_rb_root_color_no_rb_leaf: core.

Lemma rbtree_ch_no_rb_leaf : forall l, (forall l1, ((rb_lch l l1 \/ rb_rch l l1) -> ~rb_leaf l)). Proof.
  intros. destruct H.
  - destruct l. my_inversion H. unfold not. intros. my_inversion H0.
  - destruct l. my_inversion H. unfold not. intros. my_inversion H0.
 Qed. Hint Resolve rbtree_ch_no_rb_leaf: core.

Lemma not_rbtree_root_lch_rch : not (forall l, (forall x, (forall l1, (forall l2, (rb_root l x -> (rb_lch l l1 /\ rb_rch l l2)))))). Proof. intros. apply ex_not_not_all. exists (RBNode (true) (RBLeaf) (1) (RBLeaf)). apply ex_not_not_all. exists 1. apply ex_not_not_all. exists (RBNode (true) (RBLeaf) (1) (RBLeaf)). apply ex_not_not_all. exists (RBNode (true) (RBLeaf) (1) (RBLeaf)). unfold not. intros. destruct H. auto. my_inversion H.
Qed. Hint Resolve not_rbtree_root_lch_rch: core.

Lemma rbtree_root_lch_rch : forall l, (forall x,  (exists l1, (exists l2, (rb_root l x -> (rb_lch l l1 /\ rb_rch l l2))))). Proof. intros. induction l.
- repeat econstructor. inversion H. inversion H. Unshelve. constructor. constructor.
- repeat econstructor.
Qed. Hint Resolve rbtree_root_lch_rch: core.

Lemma root_color_single : forall v, ~(rb_root_color v false /\ rb_root_color v true). Proof.
  intros. apply rewrite_not_conj. unfold not. destruct v. constructor. intros. my_inversion H. destruct color. left. simp. my_inversion H. right. simp. my_inversion H.

Qed. Hint Resolve root_color_single: core.


Lemma leaf_no_root_color : forall v, (rb_leaf v -> (~rb_root_color v false /\ ~rb_root_color v true)). Proof.
  intros. constructor. inversion H. simp. simp.

 Qed. Hint Resolve leaf_no_root_color: core.


(* num_black lemmas*)
Lemma rbtree_num_black_0_rb_leaf : forall l, ((num_black l 0 /\ ~rb_root_color l true) -> rb_leaf l). Proof.
  intros. destruct H. induction l. constructor. my_inversion H; clear H. destruct H0. eauto.
Qed. Hint Resolve rbtree_num_black_0_rb_leaf: core.

Lemma rbtree_num_black_geq_0 : forall l, (forall n, (num_black l n -> n >= 0)). Proof.
  intros. induction n. eauto. lia.
Qed. Hint Resolve rbtree_num_black_geq_0: core.

Lemma rbtree_rb_leaf_num_black_0 : forall l, (forall n, ((rb_leaf l /\ num_black l n) -> n = 0)). Proof.
  intros. induction n. reflexivity. my_inversion H. my_inversion H0. my_inversion H1.
Qed. Hint Resolve rbtree_rb_leaf_num_black_0: core.

Lemma rbtree_rb_leaf_num_black_0_second : forall l, (rb_leaf l -> num_black l 0). Proof.
  intros. my_inversion H. constructor.
Qed. Hint Resolve rbtree_rb_leaf_num_black_0_second: core.

Lemma rbtree_positive_num_black_is_not_rb_leaf : forall l, (forall n, ((num_black l n /\ n > 0) -> ~rb_leaf l)). Proof.
  intros. unfold not. intros. my_inversion H0. my_inversion H. my_inversion H1. my_inversion H2.
Qed. Hint Resolve rbtree_positive_num_black_is_not_rb_leaf: core.

Lemma num_black_root_black_lt_minus_1 : forall v, (forall lt, (forall h, ((rb_root_color v false /\ (num_black v h /\ rb_lch v lt)) -> num_black lt (h - 1)))). Proof.
  intros. my_inversion H; clear H. my_inversion H1; clear H1. my_inversion H2; clear H2. my_inversion H; clear H. my_inversion H0; clear H0. simp. rewrite PeanoNat.Nat.sub_0_r. auto.
Qed. Hint Resolve num_black_root_black_lt_minus_1: core.

Lemma num_black_root_black_rt_minus_1 : forall v, (forall rt, (forall h, ((rb_root_color v false /\ (num_black v h /\ rb_rch v rt)) -> num_black rt (h - 1)))). Proof.
  intros. my_inversion H; clear H. my_inversion H1; clear H1. my_inversion H0. my_inversion H. rewrite PeanoNat.Nat.add_sub_swap. simp. my_inversion H2. auto.
Qed. Hint Resolve num_black_root_black_rt_minus_1: core.

Lemma num_black_root_red_lt_same : forall v, (forall lt, (forall h, ((rb_root_color v true /\ (num_black v h /\ rb_lch v lt)) -> num_black lt h))). Proof.
  intros. simp. my_inversion H0.  my_inversion H1. my_inversion H1. my_inversion H1. my_inversion H.
Qed. Hint Resolve num_black_root_red_lt_same: core.

Lemma num_black_root_red_rt_same : forall v, (forall rt, (forall h, ((rb_root_color v true /\ (num_black v h /\ rb_rch v rt)) -> num_black rt h))). Proof.
  intros. simp. my_inversion H0. my_inversion H. my_inversion H1. my_inversion H.
Qed. Hint Resolve num_black_root_red_rt_same: core.

Lemma num_black_root_from_lt_rt : forall v, (forall lt, (forall rt, (forall h, ((num_black lt h /\ (num_black rt h /\ (rb_rch v rt /\ (rb_lch v lt /\ rb_root_color v true)))) -> num_black v h)))). Proof.
  intros. simp. induction v. my_inversion H3. my_inversion H3; clear H3. my_inversion H2; clear H2. my_inversion H1; clear H1. constructor. auto. auto.
Qed. Hint Resolve num_black_root_from_lt_rt: core.

Lemma num_black_root_from_lt_rt_plus_1 : forall v, (forall lt, (forall rt, (forall h, ((num_black lt h /\ (num_black rt h /\ (rb_rch v rt /\ (rb_lch v lt /\ rb_root_color v false)))) -> num_black v (h + 1))))). Proof.
  intros. simp. induction v. my_inversion H3. my_inversion H3; clear H3. my_inversion H2; clear H2. my_inversion H1; clear H1. rewrite PeanoNat.Nat.add_1_r. constructor. auto. auto.
Qed. Hint Resolve num_black_root_from_lt_rt_plus_1: core.

(* no_red_red *)
Lemma rbtree_rb_leaf_no_red_red : forall l, (rb_leaf l -> no_red_red l). Proof.
  intros. induction l. constructor. my_inversion H.
Qed. Hint Resolve rbtree_rb_leaf_no_red_red: core.

Lemma num_black_root_black_0_rt_red : forall v, (forall rt, ((num_black v 0 /\ rb_rch v rt) -> rb_root_color v true)). Proof.
  intros. simp. induction v. my_inversion H0. my_inversion H. auto.
 Qed. Hint Resolve num_black_root_black_0_rt_red: core.

Lemma no_red_red_lt : forall v, (forall lt, ((no_red_red v /\ rb_lch v lt) -> no_red_red lt)). Proof.
  intros. simp. my_inversion H. my_inversion H0. my_inversion H0. my_inversion H0.
Qed. Hint Resolve no_red_red_lt: core.

Lemma no_red_red_rt : forall v, (forall rt, ((no_red_red v /\ rb_rch v rt) -> no_red_red rt)). Proof.
  intros. simp. my_inversion H. my_inversion H0. my_inversion H0. my_inversion H0.
Qed. Hint Resolve no_red_red_rt: core.

Lemma no_red_red_root_red_lt_not_red : forall v, (forall lt, ((no_red_red v /\ (rb_lch v lt /\ rb_root_color v true)) -> ~rb_root_color lt true)). Proof.
  intros. simp. my_inversion H. my_inversion H1. my_inversion H0. my_inversion H1.
 Qed. Hint Resolve no_red_red_root_red_lt_not_red: core.

Lemma no_red_red_root_red_rt_not_red : forall v, (forall rt, ((no_red_red v /\ (rb_rch v rt /\ rb_root_color v true)) -> ~rb_root_color rt true)). Proof.
  intros. simp. my_inversion H. my_inversion H1. my_inversion H0. my_inversion H1.
Qed. Hint Resolve no_red_red_root_red_rt_not_red: core.

Lemma no_red_red_given_lt_rt_black_root : forall v, (forall lt, (forall rt, ((no_red_red lt /\ (no_red_red rt /\ (rb_lch v lt /\ (rb_rch v rt /\ rb_root_color v false)))) -> no_red_red v))). Proof.
  intros. simp. induction v. constructor. destruct color. my_inversion H3. constructor. my_inversion H1. my_inversion H2.
 Qed. Hint Resolve no_red_red_given_lt_rt_black_root: core.

Lemma no_red_red_given_lt_rt_red_root : forall v, (forall lt, (forall rt, ((no_red_red lt /\ (no_red_red rt /\ (rb_lch v lt /\ (rb_rch v rt /\ (~rb_root_color lt true /\ (~rb_root_color rt true /\ rb_root_color v true)))))) -> no_red_red v))). Proof.
  intros. simp. induction v. constructor. destruct color. constructor. my_inversion H1. my_inversion H2. my_inversion H1. my_inversion H2. my_inversion H5.
 Qed. Hint Resolve no_red_red_given_lt_rt_red_root: core.

Lemma black_lt_black_num_black_gt_1 : forall v, (forall lt, (forall h, ((num_black v h /\ (rb_lch v lt /\ (rb_root_color v false /\ rb_root_color lt false))) -> h > 1))). Proof.
  intros. simp. my_inversion H; clear H. my_inversion H1. my_inversion H1.

   clear H1. my_inversion H0; clear H0.

   my_inversion H2. clear H2. my_inversion H3; clear H3. destruct n0. eauto. constructor. apply le_n_S.  apply PeanoNat.Nat.le_1_succ.
 Qed. Hint Resolve black_lt_black_num_black_gt_1: core.

Lemma black_rt_black_num_black_gt_1 : forall v, (forall rt, (forall h, ((num_black v h /\ (rb_rch v rt /\ (rb_root_color v false /\ rb_root_color rt false))) -> h > 1))). Proof.
  intros. simp. my_inversion H; clear H. my_inversion H1. my_inversion H1.

   clear H1. my_inversion H0; clear H0. my_inversion H4. my_inversion H2. my_inversion H2. destruct n0. eauto. constructor. apply le_n_S.  apply PeanoNat.Nat.le_1_succ.
Qed. Hint Resolve black_rt_black_num_black_gt_1: core.








Lemma not_num_black_root_black_0_lt_leaf : not (forall v, (forall lt, ((num_black v 0 /\ rb_lch v lt) -> rb_leaf lt))). Proof.
  apply ex_not_not_all. exists (RBNode true (RBNode true RBLeaf 1 RBLeaf ) 1 RBLeaf ).
  apply ex_not_not_all. exists (RBNode true RBLeaf 1 RBLeaf ). unfold not. intros. assert (num_black (RBNode true (RBNode true RBLeaf 1 RBLeaf) 1 RBLeaf) 0 /\
rb_lch (RBNode true (RBNode true RBLeaf 1 RBLeaf) 1 RBLeaf)
(RBNode true RBLeaf 1 RBLeaf)).  split; auto. apply H in H0. my_inversion H0.
Qed. Hint Resolve not_num_black_root_black_0_lt_leaf: core.

Lemma num_black_root_black_0_lt_leaf : forall v, (forall lt, ((no_red_red v /\ num_black v 0 /\ rb_lch v lt) -> rb_leaf lt)). Proof.
  intros v lt. destruct lt. simp. simp. my_inversion H1. my_inversion H. destruct color. my_inversion H. unfold not in H8. exfalso. apply H8. auto. my_inversion H0. my_inversion H10. my_inversion H0.
Qed. Hint Resolve num_black_root_black_0_lt_leaf: core.


Lemma not_num_black_root_black_0_rt_leaf : not (forall v, (forall rt, ((num_black v 0 /\ rb_rch v rt) -> rb_leaf rt))).
Proof.
  apply ex_not_not_all. exists (RBNode true RBLeaf 1 (RBNode true RBLeaf 1 RBLeaf ) ).
  apply ex_not_not_all. exists (RBNode true RBLeaf 1 RBLeaf ). unfold not. intros. assert (num_black (RBNode true RBLeaf 1 (RBNode true RBLeaf 1 RBLeaf)) 0 /\
rb_rch (RBNode true RBLeaf 1 (RBNode true RBLeaf 1 RBLeaf))
(RBNode true RBLeaf 1 RBLeaf)). split; auto. apply H in H0. my_inversion H0.
Qed. Hint Resolve not_num_black_root_black_0_rt_leaf: core.

Lemma num_black_root_black_0_rt_leaf : forall v, (forall rt, ((no_red_red v /\ num_black v 0 /\ rb_rch v rt) -> rb_leaf rt)). Proof.
  intros v lt. destruct lt. simp. simp. my_inversion H1. my_inversion H. destruct color. my_inversion H. unfold not in H9. exfalso. apply H9. auto. my_inversion H0. my_inversion H11. my_inversion H0.
Qed. Hint Resolve num_black_root_black_0_rt_leaf: core.
