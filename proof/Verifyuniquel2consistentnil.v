Require Import ListAux.
Require Import TreeAux.
Lemma uniquel2consistent_nil0 (il_0:list nat) (u_0:nat) : (nil_spec  il_0) -> ((True) -> (not (list_head  il_0 u_0))).
Proof. solve_nil. Qed.

Lemma uniquel2consistent_nil1 (il_0:list nat) (u_0:nat) : (nil_spec  il_0) -> ((True) -> (not (list_once  il_0 u_0))).
Proof. solve_nil. Qed.

