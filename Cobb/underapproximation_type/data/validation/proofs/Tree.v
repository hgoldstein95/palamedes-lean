Require Import Setoid.
Require Import Lia.

From Coq Require Export Logic.Classical_Pred_Type.

From MyProject Require Import Tactics.

Inductive Tree : Type :=
| Leaf
| Node (l : Tree) (v : nat) (r : Tree).

Inductive depth : Tree -> nat -> Prop :=
| depth_leaf : depth Leaf 0
| depth_node : forall v l r n n1 n2,
  depth l n1 -> depth r n2 ->
  n = (max n1 n2) ->
  depth (Node l v r) (S n).

Inductive complete : Tree -> Prop :=
| CompleteLeaf :
complete Leaf
| CompleteNode : forall n x l r,
complete l -> complete r -> depth l n -> depth r n -> depth (Node l x r) (S n) ->
complete (Node l x r).

Inductive leaf : Tree -> Prop :=
| leaf_i : leaf Leaf.

Inductive root : Tree -> nat -> Prop :=
| root_i : forall l v r, root (Node l v r) v.

Inductive lch : Tree -> Tree -> Prop :=
| lch_i: forall v l r, lch (Node l v r) l.

Inductive rch  : Tree -> Tree  -> Prop :=
| rch_i: forall v l r, rch (Node l v r) r.

Inductive tree_mem : Tree -> nat -> Prop :=
| BstNode_root : forall l v r, tree_mem (Node l v r) v
| BstNode_child : forall l v c r, (tree_mem l c \/ tree_mem r c) -> tree_mem (Node l v r) c.

Inductive lower_bound : Tree -> nat -> Prop :=
| LowerBoundBaseCase : forall r x y, bst (Node Leaf x r) -> y < x -> lower_bound (Node Leaf x r) y
| LowerBoundRecursiveCase : forall l l1 x, bst l -> not (leaf l1) -> lch l l1 -> lower_bound l1 x -> lower_bound l x

with upper_bound : Tree -> nat -> Prop :=
| UpperBoundBaseCase : forall l x y, bst (Node l x Leaf) -> y > x -> upper_bound (Node l x Leaf) y
| UpperBoundRecursiveCase : forall l l1 x, bst l -> not (leaf l1) -> rch l l1 -> upper_bound l1 x -> upper_bound l x

with bst : Tree -> Prop :=
| BstLeaf : bst Leaf
| BstNode : forall x l r, (

    (not (leaf l)) -> upper_bound l x
   ) -> (
    (not (leaf r)) -> lower_bound r x) -> bst l -> bst r -> bst (Node l x r).

Inductive tree_incr_one : Tree -> Prop :=
| incr_one_leaf : tree_incr_one Leaf
| incr_one_node_left l n r : 
    tree_incr_one (Node l (n + 1) r) -> 
    tree_incr_one (Node (Node l (n + 1) r) n Leaf)
| incr_one_node_right l n r : 
    tree_incr_one (Node l (n + 1) r) -> 
    tree_incr_one (Node Leaf n (Node l (n + 1) r))
| incr_one_node_both l1 l2 n r1 r2 : 
    tree_incr_one (Node l1 (n + 1) r1) -> 
    tree_incr_one (Node l2 (n + 1) r2) ->
    tree_incr_one (Node (Node l1 (n + 1) r1) n (Node l2 (n + 1) r2))
.

Inductive avl_balanced : nat -> Tree -> Prop :=
| bal_leaf0 : avl_balanced 0 Leaf
| bal_leaf1 : avl_balanced 1 Leaf
| bal_node : forall n t1 t2 m,
    avl_balanced n t1 -> avl_balanced n t2 -> avl_balanced (S n) (Node t1 m t2).

    
Hint Constructors leaf: core.
Hint Constructors root: core.
Hint Constructors lch: core.
Hint Constructors rch: core.
Hint Constructors depth: core.
Hint Constructors complete: core.
Hint Constructors tree_mem: core.
Hint Constructors bst: core.
Hint Constructors avl_balanced: core.
Hint Constructors lower_bound : core.
Hint Constructors upper_bound : core.
Hint Constructors tree_incr_one: core.
Hint Unfold not: core.

Lemma tree_no_root_is_tree : forall l, forall i, not ( (root l i) /\ leaf l).
Proof.
    intro. destruct l.
    - intro. unfold not. intro. my_inversion H. my_inversion H0.
    - intro. unfold not. intro. my_inversion H. my_inversion H1.
Qed.

Lemma tree_depth_exists : forall l, exists n, depth l n.
Proof.
    intro. induction l.
    - exists 0. constructor.
    - my_inversion IHl1. my_inversion IHl2. exists (S (max x x0)). econstructor; eauto.
Qed.

Lemma tree_leaf_depth_0_disjoint : forall l, exists n, (depth l 0 /\ leaf l) \/ (depth l n /\ n > 0 /\ not (leaf l)).
Proof.
    intros. destruct (tree_depth_exists l) as [n H]. destruct l.
    - eexists. left. split; auto.
    - eexists. right. split. eapply H. split. my_inversion H. lia. unfold not. intro. my_inversion H0. Unshelve. constructor.
Qed.

Lemma tree_complete_leaf : forall l, (leaf l -> complete l). Proof.
    intros. my_inversion H. auto.
 Qed. Hint Resolve tree_complete_leaf: core.

Lemma tree_depth_leaf : forall l, (leaf l -> depth l 0). Proof.
    intros. my_inversion H. auto.
 Qed. Hint Resolve tree_depth_leaf: core.

Lemma tree_complete_node : forall l, (forall l1, (forall l2, (forall n, ((complete l1 /\ (complete l2 /\ (depth l1 n /\ (depth l2 n /\ (lch l l1 /\ rch l l2))))) -> complete l)))). Proof.
intros. simp. destruct l.
    - constructor.
    - my_inversion H3; clear H3. my_inversion H4; clear H4. econstructor; eauto. econstructor; eauto. lia.
 Qed. Hint Resolve tree_complete_node: core.

Lemma tree_depth_node : forall l, (forall l1, (forall l2, (forall n1, (forall n2, (((depth l1 n1) /\ ((depth l2 n2) /\ ((lch l l1) /\ (rch l l2)))) -> (((n1 > n2) -> (depth l (n1 + 1))) /\ ((n2 >= n1) -> (depth l (n2 + 1))))))))). Proof.
    intros. simp. destruct l; split; intro; my_inversion H1; clear H1; my_inversion H2; clear H2.
    - assert (n1 + 1 = S n1). lia. rewrite H1. econstructor; eauto. lia.
    - assert (n2 + 1 = S n2). lia. rewrite H1. econstructor; eauto. lia.
 Qed. Hint Resolve tree_depth_node: core.

Lemma tree_complete_lch_complete : forall l, (forall l1, ((lch l l1 /\ complete l) -> complete l1)). Proof.
    intros. simp. my_inversion H0. my_inversion H. my_inversion H.
 Qed. Hint Resolve tree_complete_lch_complete: core.

Lemma tree_complete_rch_complete : forall l, (forall l1, ((rch l l1 /\ complete l) -> complete l1)). Proof.
    intros. simp. my_inversion H0. my_inversion H. my_inversion H.
 Qed. Hint Resolve tree_complete_rch_complete: core.

Lemma max_helper : forall n1 n2, 0 = Nat.max n1 n2 -> (n1 = 0 /\ n2 = 0). Proof.
    intros. destruct n1; destruct n2; auto. my_inversion H.
Qed.

Lemma max_helper2 : forall n n1 n2, n = Nat.max n1 n2 -> (n1 = n \/ n2 = n). Proof.
    intros. destruct n1; destruct n2; auto. my_inversion H. simp.
    apply PeanoNat.Nat.max_case. left; auto. right; auto.
Qed.

Lemma max_helper3 : forall n1 n2, (n1 = Nat.max n1 n2 \/ n2 = Nat.max n1 n2). Proof.
    intros.
    apply PeanoNat.Nat.max_case. left; auto. right; auto.
Qed.

Lemma depth_helper : forall t n1 n2, depth t n1 -> depth t n2 -> n1 = n2.
Proof.
    induction t; simpl; intros.
    + inversion H. inversion H0. reflexivity.
    + inversion H; subst. inversion H0; subst.
      specialize IHt2 with n3 n4.
      specialize IHt1 with n0 n1.
      apply IHt1 in H4.
      - subst. apply IHt2 in H6.
      * subst. reflexivity.
      * assumption.
      - assumption.
Qed.

Lemma tree_complete_lch_depth_minus_1 : forall l, (forall l1, (forall n, ((lch l l1 /\ (complete l /\ depth l n)) -> depth l1 (n - 1)))). Proof.
    intros. simp. destruct l.
    - my_inversion H.
    - my_inversion H0. my_inversion H; clear H. my_inversion H1. apply PeanoNat.Nat.max_case.
        + assert (S n2 - 1 = n2); try lia. rewrite H; auto.
        + assert (S n3 - 1 = n3); try lia. rewrite H. assert (n3 = n0).
            * eapply depth_helper; eauto.
            * subst; auto.
Qed. Hint Resolve tree_complete_lch_depth_minus_1: core.

Lemma tree_complete_rch_depth_minus_1 : forall l, (forall l1, (forall n, ((rch l l1 /\ (complete l /\ depth l n)) -> depth l1 (n - 1)))).
Proof.
    intros. simp. destruct l.
    - my_inversion H.
    - my_inversion H0. my_inversion H; clear H. my_inversion H1. apply PeanoNat.Nat.max_case.
        + assert (S n2 - 1 = n2); try lia. rewrite H. assert (n2 = n0).
            * eapply depth_helper; eauto.
            * subst; auto.
        + assert (S n3 - 1 = n3); try lia. rewrite H; auto.
Qed. Hint Resolve tree_complete_rch_depth_minus_1: core.

 Lemma tree_leaf_bst : forall l, (leaf l -> bst l). Proof.
    intros. my_inversion H. constructor.
  Qed. Hint Resolve tree_leaf_bst: core.

Lemma tree_bst_lch_bst : forall l, (forall l1, ((lch l l1 /\ bst l) -> bst l1)). Proof.
    intros. simp. my_inversion H0.
    - my_inversion H.
    - my_inversion H.
 Qed. Hint Resolve tree_bst_lch_bst: core.

Lemma tree_bst_rch_bst : forall l, (forall l1, ((rch l l1 /\ bst l) -> bst l1)). Proof.
    intros. simp. my_inversion H0.
    - my_inversion H.
    - my_inversion H.
 Qed. Hint Resolve tree_bst_rch_bst: core.

Lemma tree_leaf_mem : forall l, (forall x, ((leaf l) -> ~(tree_mem l x))). Proof.
    intros. destruct l.
    - unfold not. intro. my_inversion H0.
    - my_inversion H.
 Qed. Hint Resolve tree_leaf_mem: core.

(* Lemma tree_bst_lch_mem_lt_root : forall l, (forall l1, (forall x, (forall y, ((bst l /\ (lch l l1 /\ (root l x /\ tree_mem l1 y))) -> y < x)))). Proof.
    intros. simp.
    - my_inversion H.
        + my_inversion H1.
        + my_inversion H1; clear H1. my_inversion H0; clear H0. apply H3. auto.
 Qed. Hint Resolve tree_bst_lch_mem_lt_root: core.

Lemma tree_bst_rch_mem_gt_root : forall l, (forall l1, (forall x, (forall y, ((bst l /\ (rch l l1 /\ (root l x /\ tree_mem l1 y))) -> x < y)))). Proof.
        intros. simp.
    - my_inversion H.
        + my_inversion H1.
        + my_inversion H1; clear H1. my_inversion H0; clear H0. apply H4. auto.
 Qed. Hint Resolve tree_bst_rch_mem_gt_root: core. *)

(* Lemma tree_bst_lch_mem_lt_root : forall l, (forall l1, (forall x, (((bst l) /\ ((lch l l1) /\ (root l x))) -> (forall y, ((tree_mem l1 y) -> (y < x)))))). Proof.
    intros. simp. my_inversion H1; clear H1. my_inversion H; clear H. my_inversion H2; clear H2. apply H5. auto.
 Qed. Hint Resolve tree_bst_lch_mem_lt_root: core. *)

(* Lemma tree_bst_lch_mem_lt_root_2 : forall l, (forall l1, (exists x, (((bst l) /\ ((lch l l1) /\ (forall y, ((tree_mem l y) -> (x < y))))) -> (forall z, ((tree_mem l1 z) -> (x < z)))))). Proof.
    intros. eexists. intros. simp. my_inversion H; clear H; my_inversion H1; clear H1. apply H2. clear H2. constructor. left. auto. Unshelve. constructor.
 Qed. Hint Resolve tree_bst_lch_mem_lt_root_2: core. *)

Lemma tree_node_bst : forall l, (forall l1, (forall l2, (forall x, (((bst l1) /\ ((bst l2) /\ ((lch l l1) /\ ((rch l l2) /\ ((root l x) /\ ((~(leaf l1) -> (upper_bound l1 x)) /\ (~(leaf l2) -> (lower_bound l2 x)))))))) -> (bst l))))). Proof.
 intros. simp. destruct l.
 - my_inversion H1.
 - constructor; my_inversion H1; clear H1; my_inversion H2; clear H2; my_inversion H3; clear H3; auto.
Qed. Hint Resolve tree_node_bst: core.

(* Lemma tree_node_bst : forall l, (forall l1, (forall l2, (forall x, (((bst l1) /\ ((bst l2) /\ ((lch l l1) /\ ((rch l l2) /\ ((root l x) /\ ((forall y1, ((tree_mem l1 y1) -> (y1 < x))) /\ (forall y2, ((tree_mem l2 y2) -> (x < y2))))))))) -> (bst l))))). Proof.
    intros. simp. destruct l.
    - my_inversion H3.
    - my_inversion H1; clear H1. my_inversion H2; clear H2. my_inversion H3; clear H3. constructor; auto.
Qed. Hint Resolve tree_node_bst: core. *)

Lemma tree_root_mem : forall l, (forall x, (root l x -> tree_mem l x)).
Proof.
    intros. my_inversion H. auto.
Qed. Hint Resolve tree_root_mem: core.

Lemma tree_mem_lch_mem : forall l, (forall l1, (forall x, ((lch l l1 /\ tree_mem l1 x) -> tree_mem l x))). Proof.
    intros. simp. my_inversion H; clear H. auto.
Qed. Hint Resolve tree_mem_lch_mem: core.

Lemma tree_mem_rch_mem : forall l, (forall l1, (forall x, ((rch l l1 /\ tree_mem l1 x) -> tree_mem l x))). Proof.
    intros. simp. my_inversion H. auto.
 Qed. Hint Resolve tree_mem_rch_mem: core.

Lemma tree_mem_destruct : forall l, (forall l1, (forall l2, (forall x, (((tree_mem l x) /\ ((lch l l1) /\ (rch l l2))) -> ((root l x) \/ ((tree_mem l1 x) \/ (tree_mem l2 x))))))). Proof.
    intros. simp. my_inversion H.
    - left; auto.
    - right. my_inversion H2; my_inversion H1; my_inversion H0.
Qed.  Hint Resolve tree_mem_destruct: core.

Lemma tree_leaf_no_root : forall l, (forall x, (leaf l -> ~root l x)). Proof.
    intros. my_inversion H. unfold not. intro. my_inversion H0.
 Qed. Hint Resolve tree_leaf_no_root: core.

Lemma tree_leaf_no_ch : forall l, (forall l1, (leaf l -> ~(lch l l1 \/ rch l l1))). Proof.
    intros. unfold not; intro. my_inversion H. my_inversion H0; my_inversion H1.
 Qed. Hint Resolve tree_leaf_no_ch: core.

Lemma tree_no_leaf_exists_lch : forall l, (exists l1, (~(leaf l) -> (lch l l1))). Proof.
    intros. destruct l; eexists; intro.
    - destruct H. constructor.
    - econstructor. Unshelve. constructor.
 Qed. Hint Resolve tree_no_leaf_exists_lch: core.

Lemma tree_no_leaf_exists_rch : forall l, (exists l2, (~(leaf l) -> (rch l l2))). Proof.
        intros. destruct l; eexists; intro.
    - destruct H. constructor.
    - econstructor. Unshelve. constructor.
 Qed. Hint Resolve tree_no_leaf_exists_rch: core.

Lemma tree_no_leaf_exists_root : forall l, (exists x, (~leaf l -> root l x)). Proof.
    intros. destruct l; repeat econstructor. intro. destruct H. constructor. Unshelve. constructor.
 Qed. Hint Resolve tree_no_leaf_exists_root: core.

Lemma tree_root_no_leaf : forall l, (forall x, (root l x -> ~leaf l)). Proof.
    - intros. my_inversion H. unfold not. intros. my_inversion H0.
 Qed. Hint Resolve tree_root_no_leaf: core.

Lemma tree_lch_no_leaf : forall l, (forall l1, ((lch l l1) -> ~(leaf l))). Proof.
    intros. my_inversion H; clear H. unfold not; intro; my_inversion H.
Qed. Hint Resolve tree_lch_no_leaf: core.

Lemma tree_rch_no_leaf : forall l, (forall l1, ((rch l l1) -> ~(leaf l))). Proof.
    intros. my_inversion H; clear H. unfold not; intro; my_inversion H.
 Qed. Hint Resolve tree_rch_no_leaf: core.


Lemma tree_root_unique : forall l, (forall x, (forall y, (((root l x) /\ (root l y)) -> (x = y)))). Proof.
    intros. destruct H. my_inversion H. my_inversion H0.
 Qed. Hint Resolve tree_root_unique: core.

 Lemma tree_lch_unique : forall l, (forall l1, (forall l2, (((lch l l1) /\ (lch l l2)) -> (l1 = l2)))). Proof.
    intros. destruct H. my_inversion H. my_inversion H0.
  Qed. Hint Resolve tree_lch_unique: core.

Lemma tree_rch_unique : forall l, (forall l1, (forall l2, (((rch l l1) /\ (rch l l2)) -> (l1 = l2)))). Proof.
    intros. destruct H. my_inversion H. my_inversion H0.
 Qed. Hint Resolve tree_rch_unique: core.

Lemma tree_leaf_unique : forall l, (forall l1, (((leaf l) /\ (leaf l1)) -> (l = l1))). Proof.
    intros. destruct H. my_inversion H. my_inversion H0.
Qed. Hint Resolve tree_leaf_unique: core.

Lemma tree_leaf_or_root : forall l, ((leaf l) \/ (exists x, (root l x))). Proof.
    intros. destruct l.
    - left. constructor.
    - right. repeat econstructor.
 Qed. Hint Resolve tree_leaf_or_root: core.

Lemma tree_depth_geq_0 : forall l, (forall n, (depth l n -> n >= 0)). Proof.
    intros. lia.
 Qed. Hint Resolve tree_depth_geq_0: core.

Lemma tree_leaf_depth_0 : forall l, (forall n, ((leaf l /\ depth l n) -> n = 0)). Proof.
    intros. simp. my_inversion H. my_inversion H0.
 Qed. Hint Resolve tree_leaf_depth_0: core.

Lemma tree_leaf_depth_0_alt : forall l, ( (leaf l -> depth l 0)). Proof.
    intros. simp.
 Qed. Hint Resolve tree_leaf_depth_0: core.

(* Lemma tree_node_gt_0 : forall l, forall x, (forall n, ((root l x /\ depth l n) -> n > 0)). Proof.
    intro l. induction l;
    intros; simp.
    - my_inversion H.
    - my_inversion H0. lia.
 Qed. Hint Resolve tree_leaf_depth_0: core. *)

Lemma tree_positive_depth_is_not_leaf : forall l, (forall n, ((depth l n /\ n > 0) -> ~leaf l)). Proof.
    intros. simp. unfold not. intro. my_inversion H1. my_inversion H. my_inversion H0.
 Qed. Hint Resolve tree_positive_depth_is_not_leaf: core.


(* Lemma tree_ch_depth_ex : forall l, (forall l1, (forall n, (exists n1, (((lch l l1 \/ rch l l1) /\ depth l n) -> depth l1 n1)))). Proof.
    intros. assert (exists n', depth l1 n'). apply tree_depth_exists. destruct H. exists x. intro. auto.
Qed. Hint Resolve tree_ch_depth_ex: core. *)

Lemma tree_depth_unique : forall t1 n1 n2, depth t1 n1 /\ depth t1 n2 -> n1 = n2.
Proof.
    intro. induction t1.
    - intros. destruct H. my_inversion H. my_inversion H0.
    - intros. destruct H. my_inversion H. my_inversion H0. specialize (IHt1_1 n0 n1). destruct IHt1_1.
        + split; auto.
        + specialize (IHt1_2 n3 n4). destruct IHt1_2.
            * split; auto.
            * lia.
Qed. Hint Resolve tree_depth_unique: core.

Lemma tree_lch_depth_minus_1 : forall l, (forall l1, (forall n, (forall n1, (((lch l l1) /\ ((depth l n) /\ (depth l1 n1))) -> (n1 <= (n - 1)))))). Proof.
    intros. destruct H. destruct H0. my_inversion H; clear H. my_inversion H0; clear H0. assert (n1 = n2). eapply tree_depth_unique. split; eauto. lia.
Qed. Hint Resolve tree_lch_depth_minus_1: core.

Lemma tree_rch_depth_minus_1 : forall l, (forall l1, (forall n, (forall n1, (((rch l l1) /\ ((depth l n) /\ (depth l1 n1))) -> (n1 <= (n - 1)))))). Proof.
    intros. destruct H. destruct H0. my_inversion H; clear H. my_inversion H0; clear H0. assert (n1 = n3). eapply tree_depth_unique. split; eauto. lia.
Qed. Hint Resolve tree_rch_depth_minus_1: core.

Lemma tree_lch_depth_minus_1_alt : forall l, (forall l1, (forall n, (exists n1, (((lch l l1) /\ (depth l n)) -> ((depth l1 n1) /\ ((n1 <= (n - 1)) /\ (n1 >= 0))))))). Proof.
    intros. assert (exists n1, depth l1 n1). apply tree_depth_exists. destruct H. eexists. intros. simp. split.
    + eauto.
    + my_inversion H0; clear H0. my_inversion H1; clear H1. split.
        * assert (x = n1). eapply tree_depth_unique. split; eauto. lia.
        * eapply tree_depth_geq_0. eauto.
 Qed. Hint Resolve tree_lch_depth_minus_1_alt: core.

Lemma tree_rch_depth_minus_1_alt : forall l, (forall l1, (forall n, (exists n1, (((rch l l1) /\ (depth l n)) -> ((depth l1 n1) /\ ((n1 <= (n - 1)) /\ (n1 >= 0))))))). Proof.
    intros. assert (exists n1, depth l1 n1). apply tree_depth_exists. destruct H. eexists. intros. simp. split.
    + eauto.
    + my_inversion H0; clear H0. my_inversion H1; clear H1. split.
        * assert (x = n2). eapply tree_depth_unique. split; eauto. lia.
        * eapply tree_depth_geq_0. eauto.
Qed. Hint Resolve tree_rch_depth_minus_1_alt: core.

Lemma tree_depth_0_is_leaf : forall l, (forall n, ((depth l n /\ n = 0) -> leaf l)). Proof.
    intros. simp. my_inversion H. constructor.
Qed. Hint Resolve tree_depth_0_is_leaf: core.

Lemma tree_depth_0_is_leaf_alt : forall l, (((depth l 0) -> leaf l)). Proof.
    intros. simp.
Qed. Hint Resolve tree_depth_0_is_leaf: core.


Lemma tree_depth_node_lch : forall l, (forall l1, (forall l2, (forall n1, (forall n2, (((depth l1 n1) /\ ((depth l2 n2) /\ ((lch l l1) /\ ((rch l l2) /\ (n1 >= n2))))) -> (depth l (n1 + 1))))))). Proof.
    intros. simp. my_inversion H1; clear H1. my_inversion H2; clear H2.  rewrite PeanoNat.Nat.add_1_r. econstructor; eauto. lia.
 Qed. Hint Resolve tree_depth_node_lch: core.

Lemma tree_depth_node_rch : forall l, (forall l1, (forall l2, (forall n1, (forall n2, (((depth l1 n1) /\ ((depth l2 n2) /\ ((lch l l1) /\ ((rch l l2) /\ (n2 >= n1))))) -> (depth l (n2 + 1))))))). Proof.
        intros. simp. my_inversion H1; clear H1. my_inversion H2; clear H2.  rewrite PeanoNat.Nat.add_1_r. econstructor; eauto. lia.
 Qed. Hint Resolve tree_depth_node_rch: core.

Lemma tree_depth_rch : forall l, (forall l1, (forall n, (((rch l l1) /\ (depth l n)) -> (exists n1, ((depth l1 n1) /\ ((n1 + 1) <= n)))))). Proof.
    intros. simp. my_inversion H; clear H. my_inversion H0; clear H0. eexists. split. eauto. lia.
 Qed. Hint Resolve tree_depth_rch: core.

Lemma tree_depth_lch : forall l, (forall l1, (forall n, (((lch l l1) /\ (depth l n)) -> (exists n1, ((depth l1 n1) /\ ((n1 + 1) <= n)))))). Proof.
    intros. simp. my_inversion H. my_inversion H0. eexists. split. eauto. lia.
 Qed. Hint Resolve tree_depth_lch: core.

Lemma lower_upper_bound_helper : forall t x y, upper_bound t x /\ lower_bound t y -> y < x.
Proof. intro. induction t; intros; simp.
- my_inversion H. my_inversion H3.
- my_inversion H; clear H; my_inversion H0; clear H0.
    + lia.
    + my_inversion H2; clear H2. my_inversion H5; clear H5. apply H7 in H1. clear H7. specialize (IHt1 v y). assert (y < v). auto. lia.
    + my_inversion H3; clear H3. my_inversion H8; clear H8. apply H6 in H2. clear H6. specialize (IHt2 x v). assert (v < x). auto. lia.
    + my_inversion H3; clear H3. my_inversion H6; clear H6. my_inversion H; clear H. apply H8 in H5. clear H8. apply H9 in H2; clear H9. assert (y < v). auto. assert (v < x). auto. lia.
Qed. Hint Resolve lower_upper_bound_helper: core.

Lemma tree_lower_bound_base : forall l, (forall l1, (forall x, (forall y, (((bst l /\ root l x) /\ ((lch l l1) /\ ((leaf l1) /\ (y < x)))) -> (lower_bound l y))))). Proof.
   intros. simp. my_inversion H0; clear H0. my_inversion H; clear H. my_inversion H1; clear H1. my_inversion H3; clear H3. econstructor; auto.
 Qed. Hint Resolve tree_lower_bound_base: core.

Lemma tree_lower_bound : forall l, (forall l1, (forall x, (forall y, (((bst l) /\ ((root l x) /\ ((lch l l1) /\ (~(leaf l1) /\ ((lower_bound l1 y) /\ (y < x)))))) -> (lower_bound l y))))). Proof.
    intros. simp.
 Qed. Hint Resolve tree_lower_bound :core.

Lemma tree_lower_bound_other : forall l, (forall l1, (forall x, (((root l x) /\ ((bst l /\ lch l l1) /\ (~(leaf l1) /\ (lower_bound l1 x)))) -> (lower_bound l x)))). Proof.
    intros. simp.
Qed. Hint Resolve tree_lower_bound_other: core.

Lemma tree_lower_bound_destruct : forall l, (forall l1, (forall x, (((lower_bound l x) /\ ((lch l l1) /\ ~(leaf l1))) -> (lower_bound l1 x)))). Proof.
    intros. simp. my_inversion H0; clear H0. my_inversion H; clear H.
    - unfold not in H1. exfalso. apply H1. constructor.
    - my_inversion H3.
 Qed. Hint Resolve tree_lower_bound_destruct: core.

 Lemma tree_lower_bound_destruct_2 : forall l, (forall l1, (forall x, (((bst l) /\ ((root l x) /\ ((rch l l1) /\ ~(leaf l1)))) -> (lower_bound l1 x)))). Proof.
    intros. simp. my_inversion H0; clear H0. my_inversion H1; clear H1. my_inversion H. apply H5. auto.
  Qed. Hint Resolve tree_lower_bound_destruct_2: core.


Lemma tree_lower_bound_root : forall l, (forall x, (forall y, (((bst l) /\ ((root l x) /\ (lower_bound l y))) -> (y < x)))). Proof.
    intros. simp. my_inversion H1; clear H1.
    - my_inversion H0.
    - my_inversion H4; clear H4. my_inversion H0; clear H0. clear H2. my_inversion H. apply H4 in H3. eapply lower_upper_bound_helper. eauto.
 Qed. Hint Resolve tree_lower_bound_root: core.

Lemma tree_upper_bound_base : forall l, (forall l1, (forall x, (forall y, (((bst l /\ root l x) /\ ((rch l l1) /\ ((leaf l1) /\ (y > x)))) -> (upper_bound l y))))). Proof.
    intros. simp. my_inversion H3; clear H3. my_inversion H0; clear H0. my_inversion H1; clear H1. constructor; auto.
 Qed. Hint Resolve tree_upper_bound_base: core.

Lemma tree_upper_bound_other : forall l, (forall l1, (forall x, (((bst l /\ root l x) /\ ((rch l l1) /\ (~(leaf l1) /\ (upper_bound l1 x)))) -> (upper_bound l x)))). Proof.
    intros. simp.
Qed. Hint Resolve tree_upper_bound_other: core.

Lemma tree_upper_bound_destruct : forall l, (forall l1, (forall x, (((upper_bound l x) /\ ((rch l l1) /\ ~(leaf l1))) -> (upper_bound l1 x)))). Proof.
    intros. simp.  my_inversion H0; clear H0.  my_inversion H; clear H.
    - unfold not in H1. exfalso. apply H1. constructor.
    - my_inversion H0; clear H0.
     my_inversion H3; clear H3.
Qed. Hint Resolve tree_upper_bound_destruct: core.


Lemma tree_upper_bound_destruct_2 : forall l, (forall l1, (forall x, (((bst l) /\ ((root l x) /\ ((lch l l1) /\ ~(leaf l1)))) -> (upper_bound l1 x)))). Proof.
        intros. simp.  my_inversion H1; clear H1.  my_inversion H0; clear H0.
    - my_inversion H; clear H. auto.
Qed. Hint Resolve tree_upper_bound_destruct_2: core.

Lemma upper_bound_helper : forall l x y, upper_bound l x /\  x < y -> upper_bound l y.
Proof.
    intros. simp. induction l.
    - my_inversion H. my_inversion H3.
    - my_inversion H; clear H.
        + my_inversion H5; clear H5. econstructor; eauto. lia.
        + my_inversion H3; clear H3. eapply UpperBoundRecursiveCase; eauto.
Qed. Hint Resolve  upper_bound_helper: core.

Lemma lower_bound_helper : forall l x y, lower_bound l x /\  x > y -> lower_bound l y.
Proof.
    intros. simp. induction l.
    - my_inversion H. my_inversion H3.
    - my_inversion H; clear H.
        + my_inversion H5; clear H5. econstructor; eauto. lia.
        + my_inversion H3; clear H3. eapply LowerBoundRecursiveCase; eauto.
Qed. Hint Resolve  lower_bound_helper: core.

Lemma node_lower_helper : forall l x r y, lower_bound (Node l x r) y -> x > y
with node_upper_helper : forall l x r y, upper_bound (Node l x r) y -> x < y.
Proof.
    - intro l. induction l.
        + intros. my_inversion H. auto. my_inversion H2. my_inversion H3. my_inversion H6.
        + intros. my_inversion H; clear H. my_inversion H2; clear H2. apply IHl1 in H3. my_inversion H0. assert (upper_bound (Node l1 v l2) x). apply H5. clear H5. unfold not. intro. my_inversion H.
         eapply node_upper_helper in H. lia.
    - intro. intro. intro. generalize dependent l. generalize dependent x. induction r.
        + intros. my_inversion H. auto. my_inversion H2; clear H2. my_inversion H. auto.
        unfold not in H1. exfalso. apply H1. constructor.
        + intros. my_inversion H; clear H. my_inversion H2; clear H2. apply node_upper_helper in H3. my_inversion H0. assert (lower_bound (Node r1 v r2) x). apply H6. unfold not. intro. my_inversion H. eapply node_lower_helper in H. lia.
Qed.

Lemma upper_lower_separate_by_atleast_one : forall l, (forall x, (forall y, (((bst l) /\ ((upper_bound l x) /\ (lower_bound l y))) -> ((y + 1) < x)))). Proof.
    intro. induction l.
    - intros. simp. my_inversion H1. my_inversion H4.
    - intros. simp. assert (y < v). eapply node_lower_helper; eauto. assert (v < x). eapply node_upper_helper; eauto. lia.
 Qed. Hint Resolve upper_lower_separate_by_atleast_one: core.

(*  Lemma tree_lower_bound_destruct_2 : forall l, (forall l1, (forall x, (((bst l /\ root l x) /\ ((rch l l1) /\ ~(leaf l1))) -> (lower_bound l1 x)))). Proof.
    intros. simp. my_inversion H0; clear H0. my_inversion H2; clear H2. my_inversion H. auto.
  Qed. Hint Resolve tree_lower_bound_destruct_2: core. *)

(*   Lemma tree_lower_bound_root : forall l, (forall x, (forall y, (((bst l /\ root l x) /\ (lower_bound l y)) -> (y < x)))). Proof.
    intros. simp. my_inversion H1; clear H1. my_inversion H; clear H. my_inversion H0; clear H0. my_inversion H2; clear H2. apply H4 in H1. clear H4. assert (y + 1 < x). eapply upper_lower_separate_by_atleast_one; eauto. lia.
   Qed. Hint Resolve tree_lower_bound_root: core.
 *)
(* Lemma tree_upper_bound_destruct_2 : forall l, (forall l1, (forall x, (((bst l) /\ ((root l x) /\ ((lch l l1) /\ ~(leaf l1)))) -> (upper_bound l1 x)))). Proof.
    intros. simp. my_inversion H1; clear H1. my_inversion H0; clear H0. my_inversion H. apply H4 in H2; clear H4. auto.
 Qed. Hint Resolve tree_upper_bound_destruct_2: core.

Lemma tree_upper_bound_root : forall l, (forall x, (forall y, (((bst l) /\ ((root l x) /\ (upper_bound l y))) -> (y > x)))). Proof.
   intros. simp. my_inversion H1; clear H1; my_inversion H; clear H; my_inversion H0; clear H0.
    my_inversion H4; clear H4. apply H6 in H3; clear H6. assert (y > x + 1).  eapply upper_lower_separate_by_atleast_one; eauto. lia.
 Qed. Hint Resolve tree_upper_bound_root: core. *)