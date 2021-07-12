Require Import ListAux.
Require Import TreeAux.
Lemma bankersq1consistent_BankersqNil0 (il_0:list nat) (u_0:nat) : (nil_spec  il_0) -> ((True) -> (not (list_member  il_0 u_0))).
Proof. solve_nil. Qed.
