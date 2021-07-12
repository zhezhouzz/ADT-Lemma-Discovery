Require Import ListAux.
Require Import TreeAux.
Lemma trie1consistent_nil0 (il_0:list nat) (u_0:nat) : (nil_spec  il_0) -> ((True) -> True).
Proof. solve_nil. Qed.

