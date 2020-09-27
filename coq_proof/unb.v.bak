Require Import Basics.
Require Import Setoid.
Require Import Psatz.
(* Require Import Logic. *)

Inductive tree_parent: nat -> nat -> nat -> Prop :=
| tp: forall dt u v, tree_parent dt u v.

Inductive member: nat -> nat -> Prop :=
| mb: forall u v, member u v.

Inductive head: nat -> nat -> Prop :=
| hd: forall u v, head u v.

Notation "A ---> B" := (member A B) (at level 80, right associativity).
Notation "A :- B" := (head A B) (at level 80, right associativity).
Notation "A : B |> C" := (tree_parent A B C) (at level 80, right associativity).

Inductive insert: nat -> nat -> nat -> Prop :=
| inst: forall x tree1 tree2,
    ((forall u v, tree1: u |> v -> u >= v) ->
    ((forall u v, tree2: u |> v -> u >= v) /\
                 (forall u, tree2 ---> u <-> (tree1 ---> u \/ u = x)))) ->
    insert x tree1 tree2.

Inductive t: nat -> nat -> nat -> nat -> Prop :=
| mkt: forall tree1 x tree2 tree3,
    ((forall u v,
         ((tree1: u |> v \/ tree2: u |> v \/ (u = x /\ (tree1 ---> v \/ tree2 ---> v)))
          <-> tree3: u |> v)) /\
     (forall u,
         ((tree1 ---> u \/ tree2 ---> u \/ u = x) <-> tree3 ---> u)) /\
     tree3:- x
    ) -> t tree1 x tree2 tree3.

Ltac desconj :=
  match goal with
  | H: _ /\ _ |- _ => destruct H
  end.

Ltac invclear H :=
  inversion H; subst; clear H; repeat desconj.

Ltac specify H u v:=
  remember (H u v) eqn: zz; clear zz H.

Axiom ax: forall tree1 u v, (tree1 :- u) /\ (tree1 ---> v) -> tree1: u |> v.

Lemma unbalanced_set (tree1 tree2 tree3 tree4 tree5 x y: nat):
  t tree1 y tree2 tree3 /\ x < y /\ insert x tree1 tree4 /\ t tree4 y tree2 tree5 ->
  insert x tree3 tree5.
Proof.
  intros. repeat desconj.
  invclear H1. apply inst. intros.
  invclear H.
  assert (forall u v : nat, tree1 : u |> v -> u >= v). {
    intros. apply H1. rewrite <- (H u v). auto.
  }
  assert (forall u v : nat, tree2 : u |> v -> u >= v). {
    intros. apply H1. rewrite <- (H u v). auto.
  }
  assert (forall u v : nat, tree4 : u |> v -> u >= v). {
    apply H3 in H6. repeat desconj.
    auto.
  }
  assert (forall u : nat, (tree4 ---> u <-> tree1 ---> u \/ u = x)). {
    apply H3 in H6. repeat desconj.
    auto.
  }
  invclear H2.
  split.
  - intros. rewrite <- (H2 u v) in H12.
    destruct H12; auto.
    destruct H12; auto.
    repeat desconj. subst.
    destruct H13.
    + rewrite (H9 v) in H12. destruct H12.
      * assert (tree_parent tree3 y v). apply (ax _ _ v). split; auto.
        rewrite <- (H4 v). auto.
        apply (H1 y v) in H13. lia.
      * subst. lia.
    + assert (tree_parent tree3 y v). apply (ax _ _ v). split; auto.
        rewrite <- (H4 v). auto.
        apply (H1 y v) in H13. lia.
  - intros. rewrite <- (H10 u). split; intros.
    + destruct H12. rewrite (H9 u) in H12. destruct H12; auto.
      left. rewrite <- (H4 u). auto.
      destruct H12. left. rewrite <- (H4 u). auto. left. rewrite <- (H4 u). auto.
    + destruct H12.
      * rewrite <- (H4 u) in H12.
        destruct H12. left. rewrite (H9 u). auto.
        destruct H12; auto.
      * left. rewrite (H9 u). auto.
Qed.
