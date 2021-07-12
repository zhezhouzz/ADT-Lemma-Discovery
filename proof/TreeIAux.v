Require Import Tactics.
Require Import Setoid.

Require Import Logic.ClassicalFacts.

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

Definition key := nat.
Inductive treei (V : Type) : Type :=
| E
| T (k : key) (l : treei V) (v : V) (r : treei V).
Arguments E {V}.
Arguments T {V}.

Inductive treei_head : treei nat -> nat -> Prop :=
| thd1: forall u u' l k r, u = u' -> treei_head (T l k u r) u'.

Inductive treei_member: treei nat -> nat -> Prop :=
| tmem1: forall u u' l k r, u = u' -> treei_member (T l k u r) u'
| tmem2: forall u v l k r, treei_member l v -> treei_member (T k l u r) v
| tmem3: forall u v l k r, treei_member r v -> treei_member (T k l u r) v.

Inductive treei_left: treei nat -> nat -> nat -> Prop :=
| tl1: forall u u' v v' l k r,
    u = u' -> v = v' -> treei_member l v -> treei_left (T k l u r) u' v'
| tl2: forall u v w l k r, treei_left l u v -> treei_left (T k l w r) u v
| tl3: forall u v w l k r, treei_left r u v -> treei_left (T k l w r) u v.

Inductive treei_right: treei nat -> nat -> nat -> Prop :=
| tr1: forall u u' v v' l k r,
    u = u' -> v = v' -> treei_member r v -> treei_right (T k l u r) u' v'
| tr2: forall u v w l k r, treei_right l u v -> treei_right (T k l w r) u v
| tr3: forall u v w l k r, treei_right r u v -> treei_right (T k l w r) u v.

Definition treei_ancestor (t: treei nat) (u: nat) (v: nat): Prop :=
  (treei_left t u v) \/ (treei_right t u v).

Inductive treei_parallel: treei nat -> nat -> nat -> Prop :=
| tp1: forall u u' v v' w l k r,
    u = u' -> v = v' -> treei_member l u -> treei_member r v ->
    treei_parallel (T k l w r) u' v'
| tp2: forall u v w l k r, treei_parallel l u v -> treei_parallel (T k l w r) u v
| tp3: forall u v w l k r, treei_parallel r u v -> treei_parallel (T k l w r) u v.

Hint Constructors treei_head: core.
Hint Constructors treei_member: core.
Hint Constructors treei_left: core.
Hint Constructors treei_right: core.
Hint Constructors treei_parallel: core.

Hint Unfold not: core.
Hint Unfold treei_ancestor: core.

Lemma thd_lmem1: forall (t: treei nat) (u: nat), treei_head t u -> treei_member t u.
Proof. intros. induction H; subst; auto. Qed.

Hint Resolve thd_lmem1: core.

Lemma thd: forall (l: treei nat) (u: nat) (v: nat), treei_head l u -> treei_head l v -> u = v.
Proof.
  intros. destruct l.
  - inversion H.
  - inversion H; inversion H0; subst; auto.
Qed.

Hint Resolve thd: core.

Lemma tl_lmem1: forall (l: treei nat) (u: nat) (v: nat), treei_left l u v -> treei_member l u.
Proof. intros. induction H; subst; auto. Qed.

Lemma tl_lmem2: forall (l: treei nat) (u: nat) (v: nat), treei_left l u v -> treei_member l v.
Proof. intros. induction H; subst; auto. Qed.

Lemma tr_lmem1: forall (l: treei nat) (u: nat) (v: nat), treei_right l u v -> treei_member l u.
Proof. intros. induction H; subst; auto. Qed.

Lemma tr_lmem2: forall (l: treei nat) (u: nat) (v: nat), treei_right l u v -> treei_member l v.
Proof. intros. induction H; subst; auto. Qed.

Lemma tp_lmem1: forall (l: treei nat) (u: nat) (v: nat), treei_parallel l u v -> treei_member l u.
Proof. intros. induction H; subst; auto. Qed.

Lemma tp_lmem2: forall (l: treei nat) (u: nat) (v: nat), treei_parallel l u v -> treei_member l v.
Proof. intros. induction H; subst; auto. Qed.

Hint Resolve tl_lmem1: core.
Hint Resolve tl_lmem2: core.
Hint Resolve tr_lmem1: core.
Hint Resolve tr_lmem2: core.
Hint Resolve tp_lmem1: core.
Hint Resolve tp_lmem2: core.

Lemma rewrite_not_disj P Q: not (P \/ Q) <-> (not P) /\ (not Q).
Proof. split; auto. intros. intro. destruct H. destruct H0; contradiction. Qed.

Ltac invsub H := inversion H; subst.

Definition it (b:nat) (x:nat) (l:treei nat) (r: treei nat) :=
  T b l x r.

Inductive it_spec: nat -> nat -> treei nat -> treei nat -> treei nat -> Prop :=
| canonical_t_spec: forall b l x r t,
    (forall u, treei_head t u <-> u = x) ->
    (forall u, treei_member t u <-> ((u = x) \/ (treei_member l u) \/ (treei_member r u))) ->
    (forall u v, treei_left t u v <->
            ((treei_left l u v) \/ (treei_left r u v) \/ ((u = x) /\ (treei_member l v)))) ->
    (forall u v, treei_right t u v <->
                 ((treei_right l u v) \/ (treei_right r u v) \/ ((u = x) /\ (treei_member r v)))) ->
    (forall u v, treei_parallel t u v <->
            ((treei_parallel l u v) \/ (treei_parallel r u v) \/ ((treei_member l u) /\ (treei_member r v)))) ->
    it_spec b x l r t.

Lemma it_it_spec: forall (k: nat) (l: treei nat) (x: nat) (r: treei nat) (t: treei nat),
    it k x l r = t -> it_spec k x l r t.
Proof.
  unfold it.
  intros; subst; apply canonical_t_spec; intro.
  - split; auto. intro. invsub H; auto.
  - split; intros; auto; invsub H; auto. destruct_pairs. subst.
    destruct H; auto. destruct H; auto.
  - split; intros; auto. invsub H; auto. destruct H; auto. destruct H; auto. destruct H; eauto.
  - split; intros; auto. invsub H; auto. destruct H; auto. destruct H; auto. destruct H; eauto.
  - split; intros; auto. invsub H; auto. destruct H. apply tp2; auto. destruct H. apply tp3; auto. destruct H; apply tp1 with u v; auto.
Qed.

Definition rank (tr: treei nat): nat :=
  match tr with
  | E => 0
  | T r _ _ _ => r
  end.

Definition imaket (x:nat) (a:treei nat) (b: treei nat) :=
  if Nat.leb (rank b) (rank a) then T (rank b + 1) a x b
  else T (rank a + 1) a x b.

Definition imaket_t (x:nat) (a:treei nat) (b: treei nat) : exists k,
    imaket x a b = it k x a b.
Proof.
  unfold it.
  unfold imaket. unfold rank.
  induction a, b; simpl.
  - exists 1. auto.
  - destruct k; simpl.
    + exists 1; auto.
    + exists 1; auto.
  - exists 1. auto.
  - destruct (PeanoNat.Nat.leb_spec0 k0 k).
    + exists (k0 + 1). auto.
    + exists (k + 1). auto.
Qed.

Inductive imaket_spec: nat -> treei nat -> treei nat -> treei nat -> Prop :=
| canonical_maket_spec: forall l x r t,
    (forall u, treei_head t u <-> u = x) ->
    (forall u, treei_member t u <-> ((u = x) \/ (treei_member l u) \/ (treei_member r u))) ->
    (forall u v, treei_left t u v <->
            ((treei_left l u v) \/ (treei_left r u v) \/ ((u = x) /\ (treei_member l v)))) ->
    (forall u v, treei_right t u v <->
                 ((treei_right l u v) \/ (treei_right r u v) \/ ((u = x) /\ (treei_member r v)))) ->
    (forall u v, treei_parallel t u v <->
            ((treei_parallel l u v) \/ (treei_parallel r u v) \/ ((treei_member l u) /\ (treei_member r v)))) ->
    imaket_spec x l r t.

Ltac not_empty :=
  match goal with
  | H: treei_head E _ \/ _ |- _ => destruct H; subst; eauto; try not_empty
  | H: treei_member E _ \/ _ |- _ => destruct H; subst; eauto; try not_empty
  | H: treei_left E _ _ \/ _ |- _ => destruct H; subst; eauto; try not_empty
  | H: treei_right E _ _ \/ _|- _ => destruct H; subst; eauto; try not_empty
  | H: treei_parallel E _ _ \/ _ |- _ => destruct H; subst; eauto; try not_empty
  | H: _ \/ treei_head E _ _ |- _ => destruct H; subst; eauto; try not_empty
  | H: _ \/ treei_member E _ _ |- _ => destruct H; subst; eauto; try not_empty
  | H: _ \/ treei_left E _ _ |- _ => destruct H; subst; eauto; try not_empty
  | H: _ \/ treei_right E _ _ |- _ => destruct H; subst; eauto; try not_empty
  | H: _ \/ treei_parallel E _ _ |- _ => destruct H; subst; eauto; try not_empty
  | H: _ \/ _ \/ treei_head E _ _ |- _ => destruct H; subst; eauto; try not_empty
  | H: _ \/ _ \/ treei_member E _ _ |- _ => destruct H; subst; eauto; try not_empty
  | H: _ \/ _ \/ treei_left E _ _ |- _ => destruct H; subst; eauto; try not_empty
  | H: _ \/ _ \/ treei_right E _ _ |- _ => destruct H; subst; eauto; try not_empty
  | H: _ \/ _ \/ treei_parallel E _ _ |- _ => destruct H; subst; eauto; try not_empty
  | H: treei_head E _ /\ _ |- _ => destruct H; subst; eauto; try not_empty
  | H: treei_member E _ /\ _ |- _ => destruct H; subst; eauto; try not_empty
  | H: treei_left E _ _ /\ _ |- _ => destruct H; subst; eauto; try not_empty
  | H: treei_right E _ _ /\ _|- _ => destruct H; subst; eauto; try not_empty
  | H: treei_parallel E _ _ /\ _ |- _ => destruct H; subst; eauto; try not_empty
  | H: _ /\ treei_head E _ |- _ => destruct H; subst; eauto; try not_empty
  | H: _ /\ treei_member E _ _ |- _ => destruct H; subst; eauto; try not_empty
  | H: _ /\ treei_left E _ _ |- _ => destruct H; subst; eauto; try not_empty
  | H: _ /\ treei_right E _ _ |- _ => destruct H; subst; eauto; try not_empty
  | H: _ /\ treei_parallel E _ _ |- _ => destruct H; subst; eauto; try not_empty
  | H: treei_head E _ |- _ => inversion H
  | H: treei_member E _ |- _ => inversion H
  | H: treei_left E _ _ |- _ => inversion H
  | H: treei_right E _ _ |- _ => inversion H
  | H: treei_parallel E _ _ |- _ => inversion H
  end.

Lemma imaket_imaket_spec: forall (l: treei nat) (x: nat) (r: treei nat) (t: treei nat),
    imaket x l r = t -> imaket_spec x l r t.
Proof.
  intros. destruct (imaket_t x l r).
  rewrite H0 in H. clear H0. apply it_it_spec in H. inversion H; subst.
  apply canonical_maket_spec; auto.
Qed.

Definition ie : treei nat := E.

Inductive ie_spec: treei nat -> Prop :=
| canonical_e_spec: forall t,
    (forall u, not (treei_head t u)) ->
    (forall u, not (treei_member t u)) ->
    (forall u v, not (treei_left t u v)) ->
    (forall u v, not (treei_right t u v)) ->
    ie_spec t.

Lemma ie_ie_spec: ie_spec ie.
Proof.
  intros; subst; apply canonical_e_spec; intros; try (intro; inversion H).
Qed.

Ltac destruct_disj :=
 match goal with
 | [H : (_ \/ _) |- _] => destruct H
 | [H : _ |- (_ /\ _)] => split
 end.

Ltac solve_eq :=
  match goal with
  | [H : _ |- (_ = _) ] => (try symmetry; eauto); eauto
  end.

Ltac solve_not :=
  match goal with
  | [H : _ |- (not _) ] => intro Z
  end; subst; eauto.

Ltac solve_disjs := repeat (destruct_disj);
                    destruct_pairs; subst;
                    try contradiction; try solve_eq; try solve_not; eauto;
                    try (exfalso; eauto).

Ltac solve_it :=
  intro btspec;
  inversion btspec as [a b c d e Hhd Hmem Hl Hr Hp]; subst;
  try setoid_rewrite Hhd; try setoid_rewrite Hmem; try setoid_rewrite Hl; try setoid_rewrite Hr; try setoid_rewrite Hp;
  clear Hhd Hmem Hl Hr Hp;
  repeat ((repeat setoid_rewrite rewrite_not_conj);
          (repeat setoid_rewrite rewrite_not_disj);
          (repeat setoid_rewrite rewrite_not_not));
  intros; destruct_pairs; eauto; try solve_disjs.

Ltac solve_imaket :=
  intro btspec;
  inversion btspec as [b c d e Hhd Hmem Hl Hr Hp];  try unfold treei_ancestor; subst;
  try setoid_rewrite Hhd; try setoid_rewrite Hmem; try setoid_rewrite Hl; try setoid_rewrite Hr; try setoid_rewrite Hp;
  clear Hhd Hmem Hl Hr Hp;
  repeat ((repeat setoid_rewrite rewrite_not_conj);
          (repeat setoid_rewrite rewrite_not_disj);
          (repeat setoid_rewrite rewrite_not_not));
  intros; destruct_pairs; eauto; try solve_disjs.

Ltac solve_ie :=
  intro espec;
  inversion espec as [a Hhd Hmem Hl Hr]; subst;
  try setoid_rewrite Hhd; try setoid_rewrite Hmem; try setoid_rewrite Hl; try setoid_rewrite Hr; intros;
    try apply Hhd;
    try apply Hmem;
    try apply Hl;
    try apply Hr;
    eauto.

