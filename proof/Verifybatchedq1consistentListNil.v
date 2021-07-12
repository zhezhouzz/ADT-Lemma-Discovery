Require Import ListAux.
Require Import TreeAux.
Lemma batchedq1consistent_ListNil0 (il_0:list nat) (u_0:nat) : (nil_spec  il_0) -> ((True) -> True).
Proof. solve_nil. Qed.

