Require Import ListAux.
Require Import TreeAux.
Lemma stream2consistent_Nil0 (il_0:list nat) (u_0:nat) (u_1:nat) : (nil_spec  il_0) -> ((True) -> (not (list_member  il_0 u_1))).
Proof. solve_nil; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Nil1 (il_0:list nat) (u_0:nat) (u_1:nat) : (nil_spec  il_0) -> ((True) -> (not (list_order  il_0 u_1 u_0))).
Proof. solve_nil; try (assert (u_0 = u_1); subst; eauto). Qed.

