Require Import ListAux.
Require Import TreeAux.
Lemma batchedq2consistent_ListNil0 (il_0:list nat) (u_0:nat) (u_1:nat) : (nil_spec  il_0) -> ((True) -> True).
Proof. solve_nil; try (assert (u_0 = u_1); subst; eauto). Qed.

