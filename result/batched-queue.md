## batched-queue

#### prog

```
let snoc (lenf, f, lenr, r) x =
  let lenr = lenr + 1 in
  let r = lazy (Cons (x, r)) in
  if lenr <= lenf then (lenf, f, lenr, r)
  else (lenf + lenr, f ++ reverse r, 0, lazy Nil)

```

#### vc

```
(Cons(x,f,l1) =>
 (
  ((IsEmpty(f) /\ Rev(r,l2)) =>
   Tail(l1,r,l2,f)
  ) /\
  (~IsEmpty(f) =>
   Tail(l1,r,f,r)
  )
 )
)
```

#### specs

##### libs-cons

```
Cons(x0,l0,l1):=
forall u_0 u_1,(
 (list_member(l1,u_0) <=>
  (list_order(l1,x0,u_0) \/ list_head(l1,u_0))) /\
 (list_head(l1,u_0) <=>
  (x0==u_0)) /\
 (list_order(l1,u_0,u_1) <=>
  (
   list_order(l0,u_0,u_1) \/
   (list_head(l1,u_0) /\ list_member(l0,u_1))
  ))
)
```

##### libs-is-empty

```
IsEmpty(l2):=
forall u_0 u_1,(
true /\
 ~(list_member(l2,u_0) \/ list_member(l2,u_1))
)
```

##### libs-rev

```
Rev(l3,l4):=
forall u_0 u_1,(
 (list_member(l4,u_0) <=>
  list_member(l3,u_0)) /\
 (
  (
   list_head(l4,u_0) =>
   (
    list_order(l4,u_0,u_1) \/
    (
     list_member(l4,u_0) /\
     (
      ~list_member(l4,u_1) \/
      (
       ~list_order(l4,u_1,u_0) /\
       ~list_head(l3,u_0)
      )
     )
    )
   )
  ) /\
  (
   ~true =>
   list_head(l4,u_0)
  )
 ) /\
 (list_order(l4,u_0,u_1) <=>
  list_order(l3,u_1,u_0))
)
```

#### assertion-1

```
Tail(l1,l2,l3,l4):=
forall u v,((list_member(l3,u) \/ list_member(l4,u) \/ list_head(l1,u)) <=>
 (list_member(l1,u) \/ list_member(l2,u)))
```

#### axiom-1

```
	forall dt u_0 u_1,(ite list_head(dt,u_0)
    (
     list_member(dt,u_1) \/
     (
      list_member(dt,u_0) /\
      ~list_order(dt,u_0,u_1)
     )
    )
    (
     (u_0==u_1) \/
     (ite list_member(dt,u_1)
         (
          list_member(dt,u_0) \/
          ~list_order(dt,u_1,u_0)
         )
         (
          ~list_head(dt,u_1) /\
          ~list_order(dt,u_0,u_1)
         ))
    ))
```

#### assertion-2

```
Tail(l1,l2,l3,l4):=
forall u v,(
 ((list_member(l3,u) \/ list_member(l4,u) \/ list_head(l1,u)) <=>
  (list_member(l1,u) \/ list_member(l2,u))) /\
 (
  (list_order(l3,u,v) \/ list_order(l4,v,u)) =>
  (list_order(l1,u,v) \/ list_order(l2,v,u))
 )
)
```

#### axiom-2

```
forall dt u_0 u_1,(ite list_member(dt,u_0)
    (
     list_member(dt,u_1) \/
     ~list_order(dt,u_0,u_1)
    )
    (
     ~list_head(dt,u_0) /\
     (
      ~list_order(dt,u_1,u_0) /\
      (
       list_member(dt,u_1) \/
       (
        (u_0==u_1) \/
        (
         ~list_head(dt,u_1) /\
         ~list_order(dt,u_0,u_1)
        )
       )
      )
     )
    ))
```
