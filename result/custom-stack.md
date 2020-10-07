## custom-stack

#### prog

```
let rec concat l1 l2 =
  if is_empty l1 then l2
  else cons (stack_head l1) (concat (stack_tail l1) l2)
```

#### vc

```
(ite IsEmpty(l1)
    Concat(l1,l2,l2)
    ((
 StackHead(l1,x) /\
 StackTail(l1,l3) /\
 Concat(l3,l2,l4) /\
 Cons(x,l4,l5)
) =>
     Concat(l1,l2,l5)
    ))
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

##### libs-stack-head

```

StackHead(l3,x1):=
forall u_0 u_1,((x1==u_0) <=>
 list_head(l3,u_0))
```

##### libs-stack-tail

```
StackTail(l4,l5):=
forall u_0 u_1,(
 (
  (
   list_member(l5,u_0) =>
   (
    list_order(l4,u_1,u_0) \/
    (
     list_member(l4,u_0) /\
     (
      ~list_head(l4,u_0) \/
      (
       list_head(l5,u_0) \/
       ~list_member(l4,u_1)
      )
     )
    )
   )
  ) /\
  (
   (
    list_order(l4,u_1,u_0) \/
    (
     list_head(l5,u_0) \/
     (
      list_member(l4,u_0) /\
      ~list_head(l4,u_0)
     )
    )
   ) =>
   list_member(l5,u_0)
  )
 ) /\
 (
  (
   list_head(l5,u_0) =>
   (
    list_member(l5,u_0) /\
    (
     ~list_order(l4,u_1,u_0) \/
     (
      (u_0==u_1) \/
      (ite list_order(l5,u_0,u_1)
          list_order(l5,u_1,u_0)
          ~list_member(l5,u_1))
     )
    )
   )
  ) /\
  (
   (
    list_order(l5,u_0,u_1) /\
    (
     ~list_order(l4,u_1,u_0) /\
     list_head(l4,u_0)
    )
   ) =>
   list_head(l5,u_0)
  )
 ) /\
 (
  (
   list_order(l5,u_0,u_1) =>
   (list_order(l4,u_0,u_1) /\ list_member(l5,u_0))
  ) /\
  (
   (
    list_order(l4,u_0,u_1) /\
    (
     ~list_head(l4,u_0) \/
     (
      list_member(l5,u_0) /\
      (
       ~list_head(l4,u_1) /\
       (list_head(l5,u_0) \/ list_head(l5,u_1))
      )
     )
    )
   ) =>
   list_order(l5,u_0,u_1)
  )
 )
)
```

#### assertion-1

```
Concat(l1,l2,l3):=
forall u,(list_member(l3,u) <=>
 (list_member(l1,u) \/ list_member(l2,u)))
```

#### axiom-1

```
forall dt u_0 u_1,(ite list_member(dt,u_0)
    (
     list_member(dt,u_1) \/
     (
      ~list_order(dt,u_0,u_1) /\
      (
       ~list_head(dt,u_1) /\
       ~list_order(dt,u_1,u_0)
      )
     )
    )
    (
     ~list_head(dt,u_0) /\
     (
      ~list_order(dt,u_1,u_0) /\
      (
       ~list_order(dt,u_0,u_1) /\
       (
        ~list_head(dt,u_1) \/
        list_member(dt,u_1)
       )
      )
     )
    ))
```

#### assertion-2

```
Concat(l1,l2,l3):=
forall u v,(
 (list_member(l3,u) <=>
  (list_member(l1,u) \/ list_member(l2,u))) /\
 (
  (list_order(l1,u,v) \/ list_order(l2,u,v)) =>
  list_order(l3,u,v)
 )
)
```

#### axiom-2

```
forall dt u_0 u_1,(ite list_member(dt,u_0)
    (
     list_member(dt,u_1) \/
     (
      list_head(dt,u_0) \/
      (
       ~list_head(dt,u_1) /\
       ~list_order(dt,u_0,u_1)
      )
     )
    )
    (
     ~list_order(dt,u_1,u_0) /\
     (
      ~list_head(dt,u_0) /\
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

#### assertion-3

```
Concat(l1,l2,l3):=
forall u,(
 (list_member(l3,u) <=>
  (list_member(l1,u) \/ list_member(l2,u))) /\
 (
  list_head(l3,u) =>
  (list_head(l1,u) \/ list_head(l2,u))
 )
)
```

#### axiom-3

```
	forall dt u_0 u_1,(ite list_member(dt,u_0)
    (
     list_order(dt,u_1,u_0) \/
     (
      (u_0==u_1) \/
      ~list_head(dt,u_1)
     )
    )
    (
     ~list_head(dt,u_0) /\
     (
      ~list_order(dt,u_1,u_0) /\
      (
       ~list_head(dt,u_1) \/
       list_member(dt,u_1)
      )
     )
    ))
```
