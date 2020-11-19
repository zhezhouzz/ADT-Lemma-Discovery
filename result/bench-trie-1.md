## trie

#### prog

```
let rec ins default i a m =
  match m with
  | Trie.Leaf ->
    (match i with
     | [] -> Trie.Node(Trie.Leaf, a, Trie.Leaf)
     | z :: i' ->
       if z > 0
       then Trie.Node(ins default i' a Trie.Leaf, default, Trie.Leaf)
       else Trie.Node(Trie.Leaf, default, ins default i' a Trie.Leaf)
    )
  | Trie.Node(l, y, r) ->
    (match i with
     | [] -> Trie.Node(l, a, r)
     | z :: i' ->
       if z > 0
       then Trie.Node(ins default i' a l, y, r)
       else Trie.Node(l, y, ins default i' a r)
    )
```
#### vc

```
(TrieE(tree0) => 
 (
  (TrieE(tree1) => 
   (
    ((IsEmpty(l1) /\ TrieT(tree0,y,tree0,tree3)) => 
     Ins(x,l1,y,tree1,tree3)
    ) /\
    (Cons(z,l2,l1) => 
     (ite Lt(z,0)
         ((Ins(x,l2,y,tree0,tree3) /\ TrieT(tree3,x,tree0,tree4)) => 
          Ins(x,l1,y,tree1,tree4)
         )
         ((Ins(x,l2,y,tree0,tree3) /\ TrieT(tree0,x,tree3,tree4)) => 
          Ins(x,l1,y,tree1,tree4)
         ))
    )
   )
  ) /\
  (TrieT(tree5,y,tree6,tree1) => 
   (
    ((IsEmpty(l1) /\ TrieT(tree5,x,tree6,tree7)) => 
     Ins(x,l1,y,tree1,tree7)
    ) /\
    (Cons(z,l2,l1) => 
     (ite Lt(z,0)
         ((Ins(x,l2,y,tree5,tree3) /\ TrieT(tree3,y,tree6,tree4)) => 
          Ins(x,l1,y,tree1,tree4)
         )
         ((Ins(x,l2,y,tree6,tree3) /\ TrieT(tree5,y,tree3,tree4)) => 
          Ins(x,l1,y,tree1,tree4)
         ))
    )
   )
  )
 )
)
```

#### specs
##### Cons

```
Cons(x0,l0,l1):=
forall u_0 u_1,(
 (list_head(l1,u_0) <==> 
  (x0==u_0)) &&
 (list_member(l1,u_0) <==> 
  (list_order(l1,x0,u_0) || list_head(l1,u_0))) &&
 (list_order(l1,u_0,u_1) <==> 
  (
   list_order(l0,u_0,u_1) ||
   (list_head(l1,u_0) && list_member(l0,u_1))
  ))
)
```

##### IsEmpty

```
IsEmpty(l2):=
forall u_0,(
true &&
 !list_member(l2,u_0)
)
```

##### TrieE

```
TrieE(tr3):=
forall u_0,(
 !tree_member(tr3,u_0) &&
 !!true
)
```

##### TrieT

```
TrieT(tr0,x1,tr1,tr2):=
forall u_0 u_1,(
 (tree_head(tr2,u_0) <==> 
  (x1==u_0)) &&
 (tree_member(tr2,u_0) <==> 
  (
   tree_parallel(tr2,u_0,x1) ||
   (
    tree_right(tr2,x1,u_0) ||
    (tree_left(tr2,x1,u_0) || tree_head(tr2,u_0))
   )
  )) &&
 (tree_left(tr2,u_0,u_1) <==> 
  (
   tree_left(tr0,u_0,u_1) ||
   (
    (
     (tree_left(tr1,u_0,u_1) && tree_head(tr2,u_0)) ==> 
     tree_member(tr0,u_1)
    ) &&
    (
     !tree_left(tr1,u_0,u_1) ==> 
     (tree_head(tr2,u_0) && tree_member(tr0,u_1))
    )
   )
  )) &&
 (tree_right(tr2,u_0,u_1) <==> 
  (
   tree_right(tr1,u_0,u_1) ||
   (
    (
     (tree_right(tr0,u_0,u_1) && tree_head(tr2,u_0)) ==> 
     tree_member(tr1,u_1)
    ) &&
    (
     !tree_right(tr0,u_0,u_1) ==> 
     (tree_head(tr2,u_0) && tree_member(tr1,u_1))
    )
   )
  )) &&
 (tree_parallel(tr2,u_0,u_1) <==> 
  (
   tree_parallel(tr0,u_0,u_1) ||
   (
    tree_right(tr2,x1,u_1) &&
    (tree_left(tr2,x1,u_0) || tree_parallel(tr1,u_0,u_1))
   )
  ))
)
```
#### assertion-1

```
Ins(x,l1,y,tree1,tree2):=
forall u,(
 tree_member(tree2,u) ==> 
 (tree_member(tree1,u) || (u==y) || (u==x))
)
```

#### lemma-1

```
forall dt u_1 u_0,(
 (
  tree_head(dt,u_1) ==> 
  (
   (
    tree_member(dt,u_0) ==> 
    (
     tree_member(dt,u_1) &&
     (
      tree_left(dt,u_1,u_0) ||
      (
       tree_right(dt,u_1,u_0) ||
       !tree_parallel(dt,u_0,u_1)
      )
     )
    )
   ) &&
   (
    !tree_member(dt,u_0) ==> 
    (
     !tree_head(dt,u_0) &&
     (
      !tree_parallel(dt,u_1,u_0) &&
      (
       !tree_right(dt,u_1,u_0) &&
       (
        !tree_left(dt,u_0,u_1) &&
        !tree_right(dt,u_0,u_1)
       )
      )
     )
    )
   )
  )
 ) &&
 (
  !tree_head(dt,u_1) ==> 
  (
   (
    tree_right(dt,u_1,u_0) ==> 
    (
     tree_member(dt,u_0) &&
     (
      tree_parallel(dt,u_0,u_1) ||
      (
       tree_right(dt,u_0,u_1) ||
       (
        tree_left(dt,u_0,u_1) ||
        (
         tree_left(dt,u_1,u_0) ||
         (
          !tree_head(dt,u_0) &&
          tree_member(dt,u_1)
         )
        )
       )
      )
     )
    )
   ) &&
   (
    !tree_right(dt,u_1,u_0) ==> 
    (
     (
      tree_member(dt,u_1) ==> 
      (
       (
        tree_member(dt,u_0) ==> 
        (
         tree_left(dt,u_0,u_1) ||
         (
          tree_right(dt,u_0,u_1) ||
          (
           tree_parallel(dt,u_0,u_1) ||
           (
            !tree_head(dt,u_0) &&
            (
             tree_left(dt,u_1,u_0) ||
             (tree_parallel(dt,u_1,u_0) || (u_1==u_0))
            )
           )
          )
         )
        )
       ) &&
       (
        !tree_member(dt,u_0) ==> 
        (
         !tree_left(dt,u_1,u_0) &&
         (
          !tree_left(dt,u_0,u_1) &&
          (
           !tree_right(dt,u_0,u_1) &&
           !tree_parallel(dt,u_0,u_1)
          )
         )
        )
       )
      )
     ) &&
     (
      !tree_member(dt,u_1) ==> 
      (
       !tree_parallel(dt,u_0,u_1) &&
       (
        !tree_left(dt,u_1,u_0) &&
        (
         !tree_right(dt,u_0,u_1) &&
         (
          !tree_parallel(dt,u_1,u_0) &&
          !tree_left(dt,u_0,u_1)
         )
        )
       )
      )
     )
    )
   )
  )
 )
)
```
