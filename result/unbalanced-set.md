## unbalanced-set

#### prog

```
let rec insert x tree3 =
  match tree3 with
  | E -> T (E, x, E)
  | T (tree1, y, tree2) ->
    if Element.lt x y then T (insert x tree1, y, tree2)
    else if Element.lt y x then T (tree1, y, insert x tree2)
    else T (tree1, y, tree2)
```
#### vc

```
(
 ((
 E(tree3) /\
 E(tree1) /\
 E(tree2) /\
 T(tree1,x,tree2,tree5)
) => 
  Insert(x,tree3,tree5)
 ) /\
 ((
 T(tree1,y,tree2,tree3) /\
 (ite Lt(x,y)
     (Insert(x,tree1,tree4) /\ T(tree4,y,tree2,tree5))
     (ite Lt(y,x)
         (Insert(x,tree2,tree4) /\ T(tree1,y,tree4,tree5))
         T(tree1,y,tree2,tree5)))
) => 
  Insert(x,tree3,tree5)
 )
)
```

#### specs
##### E

```
E(tr3):=
forall u_0,(
 !tree_member(tr3,u_0) &&
 !!true
)
```

##### T

```
T(tr0,x0,tr1,tr2):=
forall u_0 u_1,(
 (tree_head(tr2,u_0) <==> 
  (x0==u_0)) &&
 (tree_member(tr2,u_0) <==> 
  (
   tree_parallel(tr2,x0,u_0) ||
   (
    tree_left(tr2,x0,u_0) ||
    (tree_right(tr2,x0,u_0) || tree_head(tr2,u_0))
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
    tree_parallel(tr1,u_0,u_1) ||
    (tree_right(tr2,x0,u_1) && tree_left(tr2,x0,u_0))
   )
  ))
)
```

#### assertion-1

```
Insert(x,tree1,tree2):=
forall u,(tree_member(tree2,u) <==> 
 (tree_member(tree1,u) || (u==x)))
```

#### lemma-1

```
forall dt u_1 u_0,(
 (
  tree_member(dt,u_1) ==> 
  (
   (
    tree_head(dt,u_0) ==> 
    (
     (
      tree_left(dt,u_1,u_0) ==> 
      (
       (
        (u_1==u_0) ==> 
        !tree_once(dt,u_1)
       ) &&
       (
        !(u_1==u_0) ==> 
        (
         tree_node(dt,u_1) &&
         (tree_left(dt,u_0,u_1) || tree_right(dt,u_0,u_1))
        )
       )
      )
     ) &&
     (
      !tree_left(dt,u_1,u_0) ==> 
      (
       tree_member(dt,u_0) &&
       (
        (
         tree_parallel(dt,u_1,u_0) ==> 
         (
          tree_right(dt,u_0,u_1) ||
          (
           !tree_head(dt,u_1) &&
           (
            !(u_1==u_0) &&
            (tree_left(dt,u_0,u_1) && tree_node(dt,u_0))
           )
          )
         )
        ) &&
        (
         !tree_parallel(dt,u_1,u_0) ==> 
         (
          (tree_right(dt,u_1,u_0) ==> tree_node(dt,u_1)) &&
          (
           !tree_right(dt,u_1,u_0) ==> 
           (
            (
             tree_once(dt,u_0) ==> 
             (
              tree_left(dt,u_0,u_1) ||
              (
               !tree_parallel(dt,u_0,u_1) &&
               (
                tree_once(dt,u_1) ||
                (
                 tree_node(dt,u_1) ||
                 (tree_right(dt,u_0,u_1) && tree_node(dt,u_0))
                )
               )
              )
             )
            ) &&
            (
             !tree_once(dt,u_0) ==> 
             (
              tree_right(dt,u_0,u_1) ||
              (
               !tree_head(dt,u_1) &&
               (
                tree_node(dt,u_1) ||
                (tree_left(dt,u_0,u_1) && tree_node(dt,u_0))
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
     )
    )
   ) &&
   (
    !tree_head(dt,u_0) ==> 
    (
     (
      tree_left(dt,u_0,u_1) ==> 
      (
       tree_node(dt,u_0) &&
       (
        tree_parallel(dt,u_1,u_0) ||
        (
         tree_parallel(dt,u_0,u_1) ||
         (
          (
           (tree_left(dt,u_1,u_0) && tree_right(dt,u_1,u_0)) ==> 
           !tree_right(dt,u_0,u_1)
          ) &&
          (
           !tree_left(dt,u_1,u_0) ==> 
           (
            tree_right(dt,u_1,u_0) ||
            (
             !tree_head(dt,u_1) &&
             (tree_right(dt,u_0,u_1) ==> tree_once(dt,u_0))
            )
           )
          )
         )
        )
       )
      )
     ) &&
     (
      !tree_left(dt,u_0,u_1) ==> 
      (
       (
        (u_1==u_0) ==> 
        (
         tree_parallel(dt,u_1,u_0) ||
         (
          (
           tree_right(dt,u_1,u_0) ==> 
           !tree_once(dt,u_1)
          ) &&
          (
           !tree_right(dt,u_1,u_0) ==> 
           tree_once(dt,u_1)
          )
         )
        )
       ) &&
       (
        !(u_1==u_0) ==> 
        (
         (
          tree_right(dt,u_0,u_1) ==> 
          (
           tree_node(dt,u_0) &&
           (
            tree_right(dt,u_1,u_0) ||
            (
             tree_left(dt,u_1,u_0) ||
             (
              tree_node(dt,u_1) ==> 
              (
               !tree_head(dt,u_1) &&
               tree_member(dt,u_0)
              )
             )
            )
           )
          )
         ) &&
         (
          !tree_right(dt,u_0,u_1) ==> 
          (
           (
            tree_head(dt,u_1) ==> 
            (
             (
              tree_parallel(dt,u_1,u_0) ==> 
              (
               tree_left(dt,u_1,u_0) ||
               (tree_right(dt,u_1,u_0) && tree_member(dt,u_0))
              )
             ) &&
             (
              !tree_parallel(dt,u_1,u_0) ==> 
              (
               (tree_parallel(dt,u_0,u_1) ==> tree_member(dt,u_0)) &&
               (
                !tree_parallel(dt,u_0,u_1) ==> 
                (
                 (
                  tree_left(dt,u_1,u_0) ==> 
                  (
                   tree_node(dt,u_0) ||
                   (tree_member(dt,u_0) && tree_node(dt,u_1))
                  )
                 ) &&
                 (
                  !tree_left(dt,u_1,u_0) ==> 
                  (
                   (
                    tree_member(dt,u_0) ==> 
                    (
                     tree_node(dt,u_0) ||
                     (
                      tree_once(dt,u_1) ==> 
                      (
                       tree_once(dt,u_0) ||
                       (tree_right(dt,u_1,u_0) && tree_node(dt,u_1))
                      )
                     )
                    )
                   ) &&
                   (
                    !tree_member(dt,u_0) ==> 
                    (
                     tree_once(dt,u_1) ||
                     (
                      tree_node(dt,u_1) &&
                      !tree_node(dt,u_0)
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
           ) &&
           (
            !tree_head(dt,u_1) ==> 
            (
             (
              tree_once(dt,u_1) ==> 
              (
               (tree_left(dt,u_1,u_0) ==> tree_node(dt,u_1)) &&
               (
                !tree_left(dt,u_1,u_0) ==> 
                (
                 (
                  tree_once(dt,u_0) ==> 
                  (
                   tree_parallel(dt,u_1,u_0) ||
                   (tree_parallel(dt,u_0,u_1) || tree_right(dt,u_1,u_0))
                  )
                 ) &&
                 (
                  !tree_once(dt,u_0) ==> 
                  (
                   tree_node(dt,u_0) ||
                   (
                    (tree_parallel(dt,u_1,u_0) ==> tree_member(dt,u_0)) &&
                    (
                     !tree_parallel(dt,u_1,u_0) ==> 
                     (
                      tree_node(dt,u_1) ||
true
                     )
                    )
                   )
                  )
                 )
                )
               )
              )
             ) &&
             (
              !tree_once(dt,u_1) ==> 
              (
               (
                tree_node(dt,u_0) ==> 
                (
                 tree_parallel(dt,u_1,u_0) ||
                 (
                  tree_left(dt,u_1,u_0) ||
                  (
                   tree_node(dt,u_1) &&
                   (tree_parallel(dt,u_0,u_1) || tree_right(dt,u_1,u_0))
                  )
                 )
                )
               ) &&
               (
                !tree_node(dt,u_0) ==> 
                (
                 (
                  tree_left(dt,u_1,u_0) ==> 
                  (
                   tree_parallel(dt,u_1,u_0) ||
                   (
                    tree_member(dt,u_0) &&
                    (tree_right(dt,u_1,u_0) ==> tree_parallel(dt,u_0,u_1))
                   )
                  )
                 ) &&
                 (
                  !tree_left(dt,u_1,u_0) ==> 
                  (
                   (
                    tree_node(dt,u_1) ==> 
                    (
                     tree_once(dt,u_0) ||
                     (
                      tree_parallel(dt,u_0,u_1) ||
                      (
                       (tree_member(dt,u_0) ==> tree_right(dt,u_1,u_0)) &&
                       (
                        !tree_member(dt,u_0) ==> 
                        (
                         !tree_right(dt,u_1,u_0) &&
                         !tree_parallel(dt,u_1,u_0)
                        )
                       )
                      )
                     )
                    )
                   ) &&
                   (
                    !tree_node(dt,u_1) ==> 
                    (
                     !tree_right(dt,u_1,u_0) &&
                     (
                      (tree_parallel(dt,u_1,u_0) ==> tree_member(dt,u_0)) &&
                      (
                       !tree_parallel(dt,u_1,u_0) ==> 
true
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
  )
 ) &&
 (
  !tree_member(dt,u_1) ==> 
  (
   !tree_node(dt,u_1) &&
   (
    !tree_parallel(dt,u_1,u_0) &&
    (
     !tree_left(dt,u_1,u_0) &&
     (
      !tree_right(dt,u_0,u_1) &&
      (
       !tree_once(dt,u_1) &&
       (
        !tree_parallel(dt,u_0,u_1) &&
        (
         !tree_left(dt,u_0,u_1) &&
         (
          !tree_right(dt,u_1,u_0) &&
          (
           (u_1==u_0) ||
           (
            (
             (tree_member(dt,u_0) && tree_head(dt,u_0)) ==> 
             (tree_node(dt,u_0) || tree_once(dt,u_0))
            ) &&
            (
             !tree_member(dt,u_0) ==> 
             (
              !tree_head(dt,u_0) &&
              !tree_node(dt,u_0)
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
   )
  )
 )
)
```

#### assertion-2

```
Insert(x,tree1,tree2):=
forall u v,(
 (
  tree_head(tree1,x) ==> 
  (tree_left(tree1,u,v) ==> tree_left(tree2,u,v))
 ) &&
 (tree_member(tree2,u) <==> 
  (tree_member(tree1,u) || (u==x)))
)
```

#### lemma-2

```
forall dt u_1 u_0,(
 (
  (u_1==u_0) ==> 
  (
   tree_member(dt,u_1) ||
   (
    !tree_head(dt,u_1) &&
    !tree_right(dt,u_1,u_0)
   )
  )
 ) &&
 (
  !(u_1==u_0) ==> 
  (
   (
    tree_head(dt,u_1) ==> 
    (
     (
      tree_member(dt,u_0) ==> 
      (tree_left(dt,u_1,u_0) || tree_right(dt,u_1,u_0))
     ) &&
     (
      !tree_member(dt,u_0) ==> 
      (
       tree_member(dt,u_1) &&
       (
        !tree_right(dt,u_0,u_1) &&
        (
         !tree_left(dt,u_0,u_1) &&
         !tree_parallel(dt,u_0,u_1)
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
      tree_member(dt,u_1) ==> 
      (
       (
        tree_member(dt,u_0) ==> 
        (
         tree_left(dt,u_0,u_1) ||
         (
          tree_right(dt,u_0,u_1) ||
          (
           tree_right(dt,u_1,u_0) ||
           (
            !tree_head(dt,u_0) &&
            (
             tree_left(dt,u_1,u_0) ||
             (tree_parallel(dt,u_1,u_0) || tree_parallel(dt,u_0,u_1))
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
          !tree_right(dt,u_1,u_0) &&
          !tree_parallel(dt,u_1,u_0)
         )
        )
       )
      )
     ) &&
     (
      !tree_member(dt,u_1) ==> 
      (
       !tree_parallel(dt,u_1,u_0) &&
       (
        !tree_right(dt,u_1,u_0) &&
        (
         !tree_left(dt,u_0,u_1) &&
         (
          !tree_left(dt,u_1,u_0) &&
          (
           !tree_right(dt,u_0,u_1) &&
           !tree_parallel(dt,u_0,u_1)
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
)
```

