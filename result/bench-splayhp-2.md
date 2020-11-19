## splay-heap

#### prog

```
let rec partition pivot = function
  | E -> E, E
  | T (a, x, b) as tr ->
    if Elem.leq x pivot then
      match b with
      | E -> tr, E
      | T (b1, y, b2) ->
        if Elem.leq y pivot then
          let small, big = partition pivot b2 in
          T (T (a, x, b1), y, small), big
        else
          let small, big = partition pivot b1 in
          T (a, x, small), T (big, y, b2)
    else
      match a with
      | E -> E, tr
      | T (a1, y, a2) ->
        if Elem.leq y pivot then
          let small, big = partition pivot a2 in
          T (a1, y, small), T (big, x, b)
        else
          let small, big = partition pivot a1 in
          small, T (big, y, T (a2, x, b))
```
#### vc

```
(E(tree0) => 
 (
  (E(tr) => Partition(pivot,tr,tr,tr)) /\
  (T(a,x,b,tr) => 
   (ite Le(x,pivot)
       (
        (E(b) => Partition(pivot,tr,tr,tree0)) /\
        (T(b1,y,b2,b) => 
         (ite Le(y,pivot)
             ((
 Partition(pivot,b2,small,big) /\
 T(a,x,b1,tmp1) /\
 T(tmp1,y,small,tmp2)
) => 
              Partition(pivot,tr,tmp2,big)
             )
             ((
 Partition(pivot,b1,small,big) /\
 T(a,x,small,tmp1) /\
 T(big,y,b2,tmp2)
) => 
              Partition(pivot,tr,tmp1,tmp2)
             ))
        )
       )
       (
        (E(a) => Partition(pivot,tr,tree0,tr)) /\
        (T(a1,y,a2,a) => 
         (ite Le(y,pivot)
             ((
 Partition(pivot,a2,small,big) /\
 T(a1,y,small,tmp1) /\
 T(big,x,b,tmp2)
) => 
              Partition(pivot,tr,tmp1,tmp2)
             )
             ((
 Partition(pivot,a1,small,big) /\
 T(a2,x,b,tmp1) /\
 T(big,y,tmp1,tmp2)
) => 
              Partition(pivot,tr,small,tmp2)
             ))
        )
       ))
  )
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
T(tree0,x,tree1,tree2):=
forall u v,(
 (tree_head(tree2,u) <==> 
  (x==u)) &&
 (tree_member(tree2,u) <==> 
  (tree_left(tree2,x,u) || tree_right(tree2,x,u) || tree_head(tree2,u))) &&
 (tree_left(tree2,u,v) <==> 
  (
   tree_left(tree0,u,v) ||
   tree_left(tree1,u,v) ||
   (tree_head(tree2,u) && tree_member(tree0,v))
  )) &&
 (tree_right(tree2,u,v) <==> 
  (
   tree_right(tree0,u,v) ||
   tree_right(tree1,u,v) ||
   (tree_head(tree2,u) && tree_member(tree1,v))
  )) &&
 (tree_parallel(tree2,u,v) <==> 
  (
   tree_parallel(tree0,u,v) ||
   tree_parallel(tree1,u,v) ||
   (tree_left(tree2,x,u) && tree_right(tree2,x,v))
  ))
)
```
#### assertion-2

```
Partition(x,tree1,tree2,tree3):=
forall u,(
 (tree_member(tree2,u) || tree_member(tree3,u)) ==> 
 tree_member(tree1,u)
)
```

#### lemma-2

```
forall dt u_0 u_1,(
 (
  tree_left(dt,u_0,u_1) ==> 
  (
   tree_member(dt,u_0) &&
   (
    tree_parallel(dt,u_1,u_0) ||
    (
     tree_left(dt,u_1,u_0) ||
     (
      tree_parallel(dt,u_0,u_1) ||
      (
       tree_head(dt,u_1) ||
       (
        (
         (tree_head(dt,u_0) && tree_right(dt,u_1,u_0)) ==> 
         !tree_right(dt,u_0,u_1)
        ) &&
        (
         !tree_head(dt,u_0) ==> 
         tree_member(dt,u_1)
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
    tree_member(dt,u_1) ==> 
    (
     tree_head(dt,u_0) ||
     (
      (u_1==u_0) ||
      (
       (
        tree_member(dt,u_0) ==> 
        (
         tree_parallel(dt,u_0,u_1) ||
         (
          tree_parallel(dt,u_1,u_0) ||
          (
           (
            (tree_right(dt,u_0,u_1) && tree_left(dt,u_1,u_0)) ==> 
            !tree_right(dt,u_1,u_0)
           ) &&
           (
            !tree_right(dt,u_0,u_1) ==> 
            (tree_left(dt,u_1,u_0) || tree_right(dt,u_1,u_0))
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
     )
    )
   ) &&
   (
    !tree_member(dt,u_1) ==> 
    (
     !tree_left(dt,u_1,u_0) &&
     (
      !tree_right(dt,u_0,u_1) &&
      (
       !tree_head(dt,u_1) &&
       (
        !tree_parallel(dt,u_1,u_0) &&
        (
         tree_member(dt,u_0) ||
         (
          (u_1==u_0) ||
          (
           !tree_head(dt,u_0) &&
           !tree_right(dt,u_1,u_0)
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
