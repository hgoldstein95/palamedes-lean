Require Import Logic.ClassicalFacts.

Tactic Notation "simplify_eq" := repeat match goal with
  | _ => congruence || (progress subst)
  | H : ?x = ?x |- _ => clear H
  | H : _ = _ |- _ => progress injection H as H
  | H1 : ?o = Some ?x, H2 : ?o = Some ?y |- _ =>
  assert (y = x) by congruence; clear H2
end.

Ltac my_inversion H := inversion H; subst; simplify_eq.

Ltac simp := repeat match goal with
| H : False |- _ => destruct H
| H : ex _ |- _ => destruct H
| H : _ /\ _ |- _ => destruct H
| H : _ * _ |- _ => destruct H
| H : ?P -> ?Q, H2 : ?P |- _ => specialize (H H2)
| |- forall x,_ => intro
| _ => progress (simpl in *; simplify_eq)
| _ => solve [eauto]
end.

Axiom excluded_middle: excluded_middle.
Lemma rewrite_not_conj P Q: not (P /\ Q) <-> (not P) \/ (not Q).
Proof.
  split; intros; auto.
  - destruct (excluded_middle P).
    + right. intro. auto.
    + left. auto.
  - intro. destruct H0. destruct H; auto.
Qed.
Lemma rewrite_not_not P: not (not P) <-> P.
Proof.
  split; intros; auto.
  - destruct (excluded_middle P); auto.
    exfalso. auto.
Qed.