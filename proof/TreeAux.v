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

Inductive tree (V : Type) : Type :=
| E
| T (l : tree V) (v : V) (r : tree V).
Arguments E {V}.
Arguments T {V}.

Inductive tree_head : tree nat -> nat -> Prop :=
| thd1: forall u u' l r, u = u' -> tree_head (T l u r) u'.

Inductive tree_member: tree nat -> nat -> Prop :=
| tmem1: forall u u' l r, u = u' -> tree_member (T l u r) u'
| tmem2: forall u v l r, tree_member l v -> tree_member (T l u r) v
| tmem3: forall u v l r, tree_member r v -> tree_member (T l u r) v.

Inductive tree_left: tree nat -> nat -> nat -> Prop :=
| tl1: forall u u' v v' l r,
    u = u' -> v = v' -> tree_member l v -> tree_left (T l u r) u' v'
| tl2: forall u v w l r, tree_left l u v -> tree_left (T l w r) u v
| tl3: forall u v w l r, tree_left r u v -> tree_left (T l w r) u v.

Inductive tree_right: tree nat -> nat -> nat -> Prop :=
| tr1: forall u u' v v' l r,
    u = u' -> v = v' -> tree_member r v -> tree_right (T l u r) u' v'
| tr2: forall u v w l r, tree_right l u v -> tree_right (T l w r) u v
| tr3: forall u v w l r, tree_right r u v -> tree_right (T l w r) u v.

Definition tree_ancestor (t: tree nat) (u: nat) (v: nat): Prop :=
  (tree_left t u v) \/ (tree_right t u v).

Hint Constructors tree_head: core.
Hint Constructors tree_member: core.
Hint Constructors tree_left: core.
Hint Constructors tree_right: core.

Hint Unfold not: core.
Hint Unfold tree_ancestor: core.

Lemma thd_lmem1: forall (t: tree nat) (u: nat), tree_head t u -> tree_member t u.
Proof.
  intros.
  destruct H; auto.
Qed.

Hint Resolve thd_lmem1: core.

Lemma thd: forall (l: tree nat) (u: nat) (v: nat), tree_head l u -> tree_head l v -> u = v.
Proof.
  intros. destruct l.
  - inversion H.
  - inversion H; inversion H0; subst; auto.
Qed.

Hint Resolve thd: core.

Lemma tl_lmem1: forall (l: tree nat) (u: nat) (v: nat), tree_left l u v -> tree_member l u.
Proof. intros. induction H; auto. Qed.

Lemma tl_lmem2: forall (l: tree nat) (u: nat) (v: nat), tree_left l u v -> tree_member l v.
Proof. intros. induction H; subst; auto. Qed.

Lemma tr_lmem1: forall (l: tree nat) (u: nat) (v: nat), tree_right l u v -> tree_member l u.
Proof. intros. induction H; subst; auto. Qed.

Lemma tr_lmem2: forall (l: tree nat) (u: nat) (v: nat), tree_right l u v -> tree_member l v.
Proof. intros. induction H; subst; auto. Qed.

Hint Resolve tl_lmem1: core.
Hint Resolve tl_lmem2: core.
Hint Resolve tr_lmem1: core.
Hint Resolve tr_lmem2: core.

Lemma rewrite_not_disj P Q: not (P \/ Q) <-> (not P) /\ (not Q).
Proof. split; auto. intros. intro. destruct H. destruct H0; contradiction. Qed.

Ltac invsub H := inversion H; subst.

Definition t (l:tree nat) (x:nat) (r: tree nat) :=
  T l x r.

Inductive t_spec: tree nat -> nat -> tree nat -> tree nat -> Prop :=
| canonical_t_spec: forall l x r t,
    (forall u, tree_head t u <-> u = x) ->
    (forall u, tree_member t u <-> ((u = x) \/ (tree_member l u) \/ (tree_member r u))) ->
    (forall u v, tree_left t u v <->
            ((tree_left l u v) \/ (tree_left r u v) \/ ((u = x) /\ (tree_member l v)))) ->
    (forall u v, tree_right t u v <->
            ((tree_right l u v) \/ (tree_right r u v) \/ ((u = x) /\ (tree_member r v)))) ->
    t_spec l x r t.

Lemma t_t_spec: forall (l: tree nat) (x: nat) (r: tree nat) (tr: tree nat),
    t l x r = tr ->  t_spec l x r tr.
Proof.
  intros; subst; apply canonical_t_spec; intro.
  - split; auto. intro. invsub H; auto.
  - split; intros; auto; invsub H; auto. destruct_pairs. subst.
    destruct H; auto. destruct H; auto.
  - split; intros; auto. invsub H; auto. destruct H; auto. destruct H; auto. destruct H; eauto.
  - split; intros; auto. invsub H; auto. destruct H; auto. destruct H; auto. destruct H; eauto.
Qed.

Definition e: tree nat := E.

Inductive e_spec: tree nat -> Prop :=
| canonical_e_spec: forall t,
    (forall u, not (tree_head t u)) ->
    (forall u, not (tree_member t u)) ->
    (forall u v, not (tree_left t u v)) ->
    (forall u v, not (tree_right t u v)) ->
    e_spec t.

Lemma e_e_spec: e_spec e.
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

Ltac solve_t :=
  intro tspec;
  inversion tspec as [a b c d Hhd Hmem Hl Hr]; subst;
  try setoid_rewrite Hhd; try setoid_rewrite Hmem; try setoid_rewrite Hl; try setoid_rewrite Hr;
  clear Hhd Hmem Hl Hr;
  repeat ((repeat setoid_rewrite rewrite_not_conj);
          (repeat setoid_rewrite rewrite_not_disj);
          (repeat setoid_rewrite rewrite_not_not));
  intros; destruct_pairs; eauto; try solve_disjs.

Ltac solve_e :=
  intro espec;
  inversion espec as [a Hhd Hmem Hl Hr]; subst;
  try setoid_rewrite Hhd; try setoid_rewrite Hmem; try setoid_rewrite Hl; try setoid_rewrite Hr; intros;
    try apply Hhd;
    try apply Hmem;
    try apply Hl;
    try apply Hr;
    eauto.
