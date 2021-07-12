Require Import ListAux.
Require Import TreeIAux.
Lemma leftisthp1consistent_t0 (i_0:nat) (i_1:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) : (it_spec  i_0 i_1 iti_0 iti_1 iti_2) -> (((u_0 = i_1)) -> (treei_member  iti_2 i_1)).
Proof. solve_it. Qed.

Lemma leftisthp1consistent_t1 (i_0:nat) (i_1:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) : (it_spec  i_0 i_1 iti_0 iti_1 iti_2) -> (((treei_member  iti_0 u_0)/\(not (u_0 = i_1))) -> (treei_member  iti_2 u_0)).
Proof. solve_it. Qed.

Lemma leftisthp1consistent_t2 (i_0:nat) (i_1:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) : (it_spec  i_0 i_1 iti_0 iti_1 iti_2) -> (((treei_member  iti_1 u_0)/\(not (treei_member  iti_0 u_0))/\(not (u_0 = i_1))) -> (treei_member  iti_2 u_0)).
Proof. solve_it. Qed.

Lemma leftisthp1consistent_t3 (i_0:nat) (i_1:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) : (it_spec  i_0 i_1 iti_0 iti_1 iti_2) -> (((not (treei_member  iti_1 u_0))/\(not (treei_member  iti_0 u_0))/\(not (u_0 = i_1))) -> (not (treei_member  iti_2 u_0))).
Proof. solve_it. Qed.

