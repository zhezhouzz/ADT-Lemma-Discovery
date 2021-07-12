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

Definition key := bool.
Inductive treeb (V : Type) : Type :=
| E
| T (k : key) (l : treeb V) (v : V) (r : treeb V).
Arguments E {V}.
Arguments T {V}.

Inductive treeb_head : treeb nat -> nat -> Prop :=
| thd1: forall u u' l k r, u = u' -> treeb_head (T l k u r) u'.

Inductive treeb_member: treeb nat -> nat -> Prop :=
| tmem1: forall u u' l k r, u = u' -> treeb_member (T l k u r) u'
| tmem2: forall u v l k r, treeb_member l v -> treeb_member (T k l u r) v
| tmem3: forall u v l k r, treeb_member r v -> treeb_member (T k l u r) v.

Inductive treeb_left: treeb nat -> nat -> nat -> Prop :=
| tl1: forall u u' v v' l k r,
    u = u' -> v = v' -> treeb_member l v -> treeb_left (T k l u r) u' v'
| tl2: forall u v w l k r, treeb_left l u v -> treeb_left (T k l w r) u v
| tl3: forall u v w l k r, treeb_left r u v -> treeb_left (T k l w r) u v.

Inductive treeb_right: treeb nat -> nat -> nat -> Prop :=
| tr1: forall u u' v v' l k r,
    u = u' -> v = v' -> treeb_member r v -> treeb_right (T k l u r) u' v'
| tr2: forall u v w l k r, treeb_right l u v -> treeb_right (T k l w r) u v
| tr3: forall u v w l k r, treeb_right r u v -> treeb_right (T k l w r) u v.

Definition treeb_ancestor (t: treeb nat) (u: nat) (v: nat): Prop :=
  (treeb_left t u v) \/ (treeb_right t u v).

Inductive treeb_parallel: treeb nat -> nat -> nat -> Prop :=
| tp1: forall u u' v v' w l k r,
    u = u' -> v = v' -> treeb_member l u -> treeb_member r v ->
    treeb_parallel (T k l w r) u' v'
| tp2: forall u v w l k r, treeb_parallel l u v -> treeb_parallel (T k l w r) u v
| tp3: forall u v w l k r, treeb_parallel r u v -> treeb_parallel (T k l w r) u v.

Hint Constructors treeb_head: core.
Hint Constructors treeb_member: core.
Hint Constructors treeb_left: core.
Hint Constructors treeb_right: core.

Hint Unfold not: core.
Hint Unfold treeb_ancestor: core.

Lemma thd_lmem1: forall (t: treeb nat) (u: nat), treeb_head t u -> treeb_member t u.
Proof. intros. induction H; subst; auto. Qed.

Hint Resolve thd_lmem1: core.

Lemma thd: forall (l: treeb nat) (u: nat) (v: nat), treeb_head l u -> treeb_head l v -> u = v.
Proof.
  intros. destruct l.
  - inversion H.
  - inversion H; inversion H0; subst; auto.
Qed.

Hint Resolve thd: core.

Lemma tl_lmem1: forall (l: treeb nat) (u: nat) (v: nat), treeb_left l u v -> treeb_member l u.
Proof. intros. induction H; subst; auto. Qed.

Lemma tl_lmem2: forall (l: treeb nat) (u: nat) (v: nat), treeb_left l u v -> treeb_member l v.
Proof. intros. induction H; subst; auto. Qed.

Lemma tr_lmem1: forall (l: treeb nat) (u: nat) (v: nat), treeb_right l u v -> treeb_member l u.
Proof. intros. induction H; subst; auto. Qed.

Lemma tr_lmem2: forall (l: treeb nat) (u: nat) (v: nat), treeb_right l u v -> treeb_member l v.
Proof. intros. induction H; subst; auto. Qed.

Lemma tp_lmem1: forall (l: treeb nat) (u: nat) (v: nat), treeb_parallel l u v -> treeb_member l u.
Proof. intros. induction H; subst; auto. Qed.

Lemma tp_lmem2: forall (l: treeb nat) (u: nat) (v: nat), treeb_parallel l u v -> treeb_member l v.
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

Definition bt (b:bool) (l:treeb nat) (x:nat) (r: treeb nat) :=
  T b l x r.

Inductive bt_spec: bool -> treeb nat -> nat -> treeb nat -> treeb nat -> Prop :=
| canonical_t_spec: forall b l x r t,
    (forall u, treeb_head t u <-> u = x) ->
    (forall u, treeb_member t u <-> ((u = x) \/ (treeb_member l u) \/ (treeb_member r u))) ->
    (forall u v, treeb_left t u v <->
            ((treeb_left l u v) \/ (treeb_left r u v) \/ ((u = x) /\ (treeb_member l v)))) ->
    (forall u v, treeb_right t u v <->
                 ((treeb_right l u v) \/ (treeb_right r u v) \/ ((u = x) /\ (treeb_member r v)))) ->
    (forall u v, treeb_parallel t u v <->
            ((treeb_parallel l u v) \/ (treeb_parallel r u v) \/ ((treeb_member l u) /\ (treeb_member r v)))) ->
    bt_spec b l x r t.

Lemma bt_bt_spec: forall (k: bool) (l: treeb nat) (x: nat) (r: treeb nat) (t: treeb nat),
    bt k l x r = t -> bt_spec k l x r t.
Proof.
  unfold bt.
  intros; subst; apply canonical_t_spec; intro.
  - split; auto. intro. invsub H; auto.
  - split; intros; auto; invsub H; auto. destruct_pairs. subst.
    destruct H; auto. destruct H; auto.
  - split; intros; auto. invsub H; auto. destruct H; auto. destruct H; auto. destruct H; eauto.
  - split; intros; auto. invsub H; auto. destruct H; auto. destruct H; auto. destruct H; eauto.
  - split; intros; auto. invsub H; auto. destruct H. apply tp2; auto. destruct H. apply tp3; auto. destruct H; apply tp1 with u v; auto.
Qed.

Definition be: treeb nat := E.

Inductive be_spec: treeb nat -> Prop :=
| canonical_e_spec: forall t,
    (forall u, not (treeb_head t u)) ->
    (forall u, not (treeb_member t u)) ->
    (forall u v, not (treeb_left t u v)) ->
    (forall u v, not (treeb_right t u v)) ->
    be_spec t.

Lemma be_be_spec: be_spec be.
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

Ltac solve_bt :=
  intro btspec;
  inversion btspec as [a b c d e Hhd Hmem Hl Hr Hp]; subst;
  try setoid_rewrite Hhd; try setoid_rewrite Hmem; try setoid_rewrite Hl; try setoid_rewrite Hr; try setoid_rewrite Hp;
  clear Hhd Hmem Hl Hr Hp;
  repeat ((repeat setoid_rewrite rewrite_not_conj);
          (repeat setoid_rewrite rewrite_not_disj);
          (repeat setoid_rewrite rewrite_not_not));
  intros; destruct_pairs; eauto; try solve_disjs.

Ltac solve_be :=
  intro espec;
  inversion espec as [a Hhd Hmem Hl Hr]; subst;
  try setoid_rewrite Hhd; try setoid_rewrite Hmem; try setoid_rewrite Hl; try setoid_rewrite Hr; intros;
    try apply Hhd;
    try apply Hmem;
    try apply Hl;
    try apply Hr;
    eauto.
