Require Import ListAux.
Require Import TreeBAux.
Lemma rbset1consistent_t0 (b_0:bool) (itb_0:treeb nat) (i_0:nat) (itb_1:treeb nat) (itb_2:treeb nat) (u_0:nat) : (bt_spec  b_0 itb_0 i_0 itb_1 itb_2) -> (((not (u_0 = i_0))/\(not (treeb_member  itb_0 u_0))/\(treeb_member  itb_2 u_0)) -> (treeb_member  itb_1 u_0)).
Proof. solve_bt. Qed.

Lemma rbset1consistent_t1 (b_0:bool) (itb_0:treeb nat) (i_0:nat) (itb_1:treeb nat) (itb_2:treeb nat) (u_0:nat) : (bt_spec  b_0 itb_0 i_0 itb_1 itb_2) -> (((not (treeb_member  itb_2 u_0))) -> (not (treeb_member  itb_0 u_0))).
Proof. solve_bt. Qed.

Lemma rbset1consistent_t2 (b_0:bool) (itb_0:treeb nat) (i_0:nat) (itb_1:treeb nat) (itb_2:treeb nat) (u_0:nat) : (bt_spec  b_0 itb_0 i_0 itb_1 itb_2) -> (((not (treeb_member  itb_2 u_0))) -> (not (u_0 = i_0))).
Proof. solve_bt. Qed.

Lemma rbset1consistent_t3 (b_0:bool) (itb_0:treeb nat) (i_0:nat) (itb_1:treeb nat) (itb_2:treeb nat) (u_0:nat) : (bt_spec  b_0 itb_0 i_0 itb_1 itb_2) -> (((not (treeb_member  itb_2 u_0))) -> (not (treeb_member  itb_1 u_0))).
Proof. solve_bt. Qed.

