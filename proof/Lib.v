Require Import ListAux.
Require Import TreeAux.
Require Import TreeIAux.
Require Import TreeBAux.
Definition bankersq_BankersqNil := nil.
Definition bankersq_BankersqCons := push.
Definition bankersq_Lazy := id.
Definition bankersq_Force := id.
Definition bankersq_BankersqReverse := List.rev.
Definition bankersq_BankersqConcat := concat.
Definition batchedq_ListNil := nil.
Definition batchedq_ListIsEmpty := is_empty.
Definition batchedq_ListRev := List.rev.
Definition batchedq_ListCons := push.
Definition customstk_is_empty := is_empty.
Definition customstk_push := push.
Definition customstk_top := top.
Definition customstk_tail := tail.
Definition stream_Nil := nil.
Definition stream_Lazy := id.
Definition stream_Force := id.
Definition uniquel_nil := nil.
Definition uniquel_cons := push.
Definition leftisthp_e := ie.
Definition leftisthp_t := it.
Definition leftisthp_maket := imaket.
Definition unbset_e := e.
Definition unbset_t := t.
Definition rbset_t := bt.
Definition trie_triet := t.
Definition trie_cons := push.
Definition trie_nil := nil.
Definition trie_e := e.
