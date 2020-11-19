## leftist-heap

#### prog

```
let rec merge tree1 tree2 =
  match tree1, tree2 with
  | tree1, Leftisthp.E -> tree1
  | Leftisthp.E, tree2 -> tree2
  | Leftisthp.T (rank1, x, a1, b1), Leftisthp.T (rank2, y, a2, b2) ->
    if Elem.leq x y then Leftisthp.makeT x a1 (merge b1 tree2)
    else Leftisthp.makeT y a2 (merge tree1 b2)
```
#### vc

```
(
 (LeftisthpIsEmpty(tree2) => Merge(tree1,tree2,tree1)) /\
 (LeftisthpIsEmpty(tree1) => Merge(tree1,tree2,tree2)) /\
 ((
 LeftisthpT(rank1,x,a1,b1,tree1) /\
 LeftisthpT(rank2,y,a2,b2,tree2) /\
 (ite Le(x,y)
     (Merge(b1,tree2,tmp) /\ LeftisthpMakeT(x,a1,tmp,tree3))
     (Merge(tree1,b2,tmp) /\ LeftisthpMakeT(y,a2,tmp,tree3)))
) => 
  Merge(tree1,tree2,tree3)
 )
)
```

#### specs
##### LeftisthpIsEmpty

```
LeftisthpIsEmpty(tr6):=
forall u_0,(
 !treei_member(tr6,u_0) &&
 !!true
)
```

##### LeftisthpMakeT

```
LeftisthpMakeT(x2,tr3,tr4,tr5):=
forall u_0 u_1,(
 (treei_head(tr5,u_0) <==> 
  (x2==u_0)) &&
 (treei_member(tr5,u_0) <==> 
  (
   treei_parallel(tr5,u_0,x2) ||
   (
    treei_right(tr5,x2,u_0) ||
    (treei_left(tr5,x2,u_0) || treei_head(tr5,u_0))
   )
  )) &&
 (treei_left(tr5,u_0,u_1) <==> 
  (
   treei_left(tr3,u_0,u_1) ||
   (
    (
     (treei_left(tr4,u_0,u_1) && treei_head(tr5,u_0)) ==> 
     treei_member(tr3,u_1)
    ) &&
    (
     !treei_left(tr4,u_0,u_1) ==> 
     (treei_head(tr5,u_0) && treei_member(tr3,u_1))
    )
   )
  )) &&
 (treei_right(tr5,u_0,u_1) <==> 
  (
   treei_right(tr4,u_0,u_1) ||
   (
    (
     (treei_right(tr3,u_0,u_1) && treei_head(tr5,u_0)) ==> 
     treei_member(tr4,u_1)
    ) &&
    (
     !treei_right(tr3,u_0,u_1) ==> 
     (treei_head(tr5,u_0) && treei_member(tr4,u_1))
    )
   )
  )) &&
 (treei_parallel(tr5,u_0,u_1) <==> 
  (
   treei_parallel(tr3,u_0,u_1) ||
   (
    treei_right(tr5,x2,u_1) &&
    (treei_left(tr5,x2,u_0) || treei_parallel(tr4,u_0,u_1))
   )
  ))
)
```

##### LeftisthpT

```
LeftisthpT(x0,x1,tr0,tr1,tr2):=
forall u_0 u_1,(
 (treei_head(tr2,u_0) <==> 
  (x1==u_0)) &&
 (treei_member(tr2,u_0) <==> 
  (treei_right(tr2,x1,u_0) || treei_left(tr2,x1,u_0))) &&
 (treei_left(tr2,u_0,u_1) <==> 
  (
   treei_left(tr0,u_0,u_1) ||
   (
    (
     (treei_left(tr1,u_0,u_1) && treei_head(tr2,u_0)) ==> 
     treei_member(tr0,u_1)
    ) &&
    (
     !treei_left(tr1,u_0,u_1) ==> 
     (treei_head(tr2,u_0) && treei_member(tr0,u_1))
    )
   )
  )) &&
 (treei_right(tr2,u_0,u_1) <==> 
  (
   treei_right(tr1,u_0,u_1) ||
   (
    (
     treei_right(tr0,u_0,u_1) ==> 
     (
      treei_member(tr1,u_1) ||
      !treei_head(tr2,u_0)
     )
    ) &&
    (
     !treei_right(tr0,u_0,u_1) ==> 
     (treei_head(tr2,u_0) && treei_member(tr1,u_1))
    )
   )
  )) &&
 (treei_parallel(tr2,u_0,u_1) <==> 
  (
   treei_parallel(tr1,u_0,u_1) ||
   (
    treei_left(tr2,x1,u_0) &&
    (treei_right(tr2,x1,u_1) || treei_parallel(tr0,u_0,u_1))
   )
  ))
)
```
#### assertion-1

```
Merge(tree1,tree2,tree3):=
forall u,(treei_member(tree3,u) <==> 
 (treei_member(tree1,u) || treei_member(tree2,u)))
```

#### lemma-1

```
forall dt u_1 u_0,(
 (
  (u_1==u_0) ==> 
  (
   (
    treei_member(dt,u_1) ==> 
    (
     treei_node(dt,u_1) ||
     (
      !treei_left(dt,u_1,u_0) &&
      !treei_right(dt,u_1,u_0)
     )
    )
   ) &&
   (
    !treei_member(dt,u_1) ==> 
    (
     !treei_node(dt,u_1) &&
     (
      !treei_left(dt,u_1,u_0) &&
      (
       !treei_head(dt,u_1) &&
       (
        !treei_right(dt,u_1,u_0) &&
        !treei_parallel(dt,u_1,u_0)
       )
      )
     )
    )
   )
  )
 ) &&
 (
  !(u_1==u_0) ==> 
  (
   (
    treei_head(dt,u_1) ==> 
    (
     !treei_head(dt,u_0) &&
     (
      (
       treei_member(dt,u_0) ==> 
       (
        treei_left(dt,u_1,u_0) ||
        (
         (
          treei_parallel(dt,u_1,u_0) ==> 
          (
           treei_node(dt,u_0) ||
           !treei_right(dt,u_0,u_1)
          )
         ) &&
         (
          !treei_parallel(dt,u_1,u_0) ==> 
          (
           treei_right(dt,u_0,u_1) ||
           (treei_member(dt,u_1) && treei_right(dt,u_1,u_0))
          )
         )
        )
       )
      ) &&
      (
       !treei_member(dt,u_0) ==> 
       (
        treei_member(dt,u_1) &&
        (
         !treei_right(dt,u_1,u_0) &&
         (
          !treei_parallel(dt,u_1,u_0) &&
          (
           !treei_left(dt,u_0,u_1) &&
           (
            !treei_right(dt,u_0,u_1) &&
            !treei_parallel(dt,u_0,u_1)
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
    !treei_head(dt,u_1) ==> 
    (
     (
      treei_head(dt,u_0) ==> 
      (
       (
        treei_member(dt,u_1) ==> 
        (
         treei_left(dt,u_0,u_1) ||
         (
          (
           treei_parallel(dt,u_0,u_1) ==> 
           (
            treei_node(dt,u_1) ||
            !treei_right(dt,u_1,u_0)
           )
          ) &&
          (
           !treei_parallel(dt,u_0,u_1) ==> 
           (
            treei_right(dt,u_1,u_0) ||
            (treei_member(dt,u_0) && treei_right(dt,u_0,u_1))
           )
          )
         )
        )
       ) &&
       (
        !treei_member(dt,u_1) ==> 
        (
         treei_member(dt,u_0) &&
         (
          !treei_right(dt,u_0,u_1) &&
          (
           !treei_parallel(dt,u_0,u_1) &&
           (
            !treei_left(dt,u_1,u_0) &&
            (
             !treei_right(dt,u_1,u_0) &&
             !treei_parallel(dt,u_1,u_0)
            )
           )
          )
         )
        )
       )
      )
     ) &&
     (
      !treei_head(dt,u_0) ==> 
      (
       (
        treei_member(dt,u_1) ==> 
        (
         treei_right(dt,u_0,u_1) ||
         (
          (treei_parallel(dt,u_0,u_1) ==> treei_member(dt,u_0)) &&
          (
           !treei_parallel(dt,u_0,u_1) ==> 
           (
            (
             treei_left(dt,u_1,u_0) ==> 
             (
              treei_right(dt,u_1,u_0) ||
              (treei_member(dt,u_0) && treei_node(dt,u_1))
             )
            ) &&
            (
             !treei_left(dt,u_1,u_0) ==> 
             (
              treei_node(dt,u_0) ||
              (
               !treei_left(dt,u_0,u_1) &&
               (
                (treei_parallel(dt,u_1,u_0) ==> treei_member(dt,u_0)) &&
                (
                 !treei_parallel(dt,u_1,u_0) ==> 
                 (
                  treei_node(dt,u_1) ||
                  (
                   !treei_member(dt,u_0) &&
                   !treei_right(dt,u_1,u_0)
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
        !treei_member(dt,u_1) ==> 
        (
         !treei_node(dt,u_1) &&
         (
          !treei_right(dt,u_0,u_1) &&
          (
           !treei_parallel(dt,u_0,u_1) &&
           (
            !treei_left(dt,u_0,u_1) &&
            !treei_parallel(dt,u_1,u_0)
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
