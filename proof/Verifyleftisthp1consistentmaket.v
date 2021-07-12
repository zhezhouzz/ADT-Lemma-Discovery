Require Import ListAux.
Require Import TreeIAux.
Lemma leftisthp1consistent_maket0 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (u_0 = i_0))/\(not (treei_member  iti_0 u_0))/\(treei_member  iti_2 u_0)) -> (treei_member  iti_1 u_0)).
Proof. solve_imaket. Qed.

Lemma leftisthp1consistent_maket1 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (treei_member  iti_2 u_0))) -> (not (treei_member  iti_0 u_0))).
Proof. solve_imaket. Qed.

Lemma leftisthp1consistent_maket2 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (treei_member  iti_2 u_0))) -> (not (u_0 = i_0))).
Proof. solve_imaket. Qed.

Lemma leftisthp1consistent_maket3 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (treei_member  iti_2 u_0))) -> (not (treei_member  iti_1 u_0))).
Proof. solve_imaket. Qed.

