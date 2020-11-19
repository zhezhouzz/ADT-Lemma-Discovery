## batched-queue

#### prog

```
let tail =
  match r with
  | [], _ -> raise Empty
  | _ :: f, r ->
    if f = [] then List.rev r, f else f, r
```
#### vc

```
(ListCons(x,f,l1) => 
 (
  ((ListIsEmpty(f) /\ ListRev(r,l2)) => 
   Tail(l1,r,l2,f)
  ) /\
  (~ListIsEmpty(f) => 
   Tail(l1,r,f,r)
  )
 )
)
```

#### specs
##### ListCons

```
ListCons(x0,l0,l1):=
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

##### ListIsEmpty

```
ListIsEmpty(l2):=
forall u_0,(
true &&
 !list_member(l2,u_0)
)
```

##### ListRev

```
ListRev(l3,l4):=
forall u_0 u_1,(
 (
  (
   list_head(l4,u_0) ==> 
   (
    list_member(l4,u_0) &&
    (
     list_order(l4,u_1,u_0) ==> 
     (
      list_order(l4,u_0,u_1) &&
      !list_head(l3,u_0)
     )
    )
   )
  ) &&
  (
   (
    !list_order(l4,u_1,u_0) &&
    (
     list_member(l4,u_0) &&
     (
      !list_head(l3,u_0) &&
      (
       list_member(l4,u_1) ==> 
       (
        list_order(l4,u_0,u_1) &&
        !list_head(l3,u_1)
       )
      )
     )
    )
   ) ==> 
   list_head(l4,u_0)
  )
 ) &&
 (list_member(l4,u_0) <==> 
  list_member(l3,u_0)) &&
 (list_order(l4,u_0,u_1) <==> 
  list_order(l3,u_1,u_0))
)
```
#### assertion-1

```
Tail(l1,l2,l3,l4):=
forall u,((list_member(l3,u) || list_head(l1,u) || list_member(l4,u)) <==> 
 (list_member(l1,u) || list_member(l2,u)))
```

#### lemma-1

```
forall dt u_1 u_0,(
 (
  list_member(dt,u_1) ==> 
  (
   list_order(dt,u_0,u_1) ||
   (
    list_head(dt,u_1) ||
    (
     (u_1==u_0) ||
true
    )
   )
  )
 ) &&
 (
  !list_member(dt,u_1) ==> 
  (
   !list_order(dt,u_0,u_1) &&
   (
    !list_head(dt,u_1) &&
    (
     list_member(dt,u_0) ||
     (
      (u_1==u_0) ||
      (
       !list_order(dt,u_1,u_0) &&
       !list_head(dt,u_0)
      )
     )
    )
   )
  )
 )
)
```
