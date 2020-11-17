## uniuqe list

#### prog

```
let rec set_add a x =
  match x with
  | [] -> [a]
  | a1 :: x1 =>
    if a == a1 then a1 :: x1 else a1 :: (set_add a x1)
```
#### vc

```
(ite IsEmpty(l1)
    (Cons(x,l1,l2) => SetAdd(x,l1,l2))
    (Cons(y,l3,l1) => 
     (ite Eq(x,y)
         SetAdd(x,l1,l1)
         ((SetAdd(x,l3,l4) /\ Cons(y,l4,l5)) => 
          SetAdd(x,l1,l5)
         ))
    ))
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

#### assertion-1

```
SetAdd(x,l1,l2):=
forall u,(list_member(l2,u) <==> 
 ((u==x) || list_member(l1,u)))
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

#### assertion-2

```
SetAdd(x,l1,l2):=
forall u,(
 (list_once(l1,u) ==> list_once(l2,u)) &&
 (list_member(l2,u) <==> 
  ((u==x) || list_member(l1,u)))
)
```

#### lemma-2

```
forall dt u_1 u_0,(
 (
  list_order(dt,u_1,u_0) ==> 
  (
   (
    list_once(dt,u_1) ==> 
    (
     list_member(dt,u_1) &&
     (
      list_member(dt,u_0) &&
      !(u_1==u_0)
     )
    )
   ) &&
   (
    !list_once(dt,u_1) ==> 
    list_member(dt,u_1)
   )
  )
 ) &&
 (
  !list_order(dt,u_1,u_0) ==> 
  (
   (
    list_member(dt,u_1) ==> 
    (
     (
      list_head(dt,u_1) ==> 
      (
       (list_member(dt,u_0) ==> list_once(dt,u_1)) &&
       (
        !list_member(dt,u_0) ==> 
        !list_once(dt,u_0)
       )
      )
     ) &&
     (
      !list_head(dt,u_1) ==> 
      (
       list_once(dt,u_1) ||
       (
        list_once(dt,u_0) ||
        !(u_1==u_0)
       )
      )
     )
    )
   ) &&
   (
    !list_member(dt,u_1) ==> 
    (
     !list_once(dt,u_1) &&
     (
      !list_order(dt,u_0,u_1) &&
      (
       list_member(dt,u_0) ||
       (
        !list_head(dt,u_1) &&
        (
         (u_1==u_0) ||
         (
          !list_head(dt,u_0) &&
          !list_once(dt,u_0)
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

