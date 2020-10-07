## bankers-queue

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
((
 Plus(lenr,1,lenr') /\
 Cons(x,r,l1) /\
 Lazy(l1,r')
) =>
 (ite Le(lenr',lenf)
     Snoc(lenf,f,lenr,r,x,lenf,f,lenr',r')
     ((
 Plus(lenf,lenr',y) /\
 Reverse(r',l2) /\
 Concat(f,l2,l3) /\
 Nil(l4) /\
 Lazy(l4,l5)
) =>
      Snoc(lenf,f,lenr,r,x,y,l3,0,l5)
     ))
)
```

#### specs

##### libs-concat

```
Concat(l7,l8,l9):=
forall u_0 u_1,(
 (list_member(l9,u_0) <=>
  (
   list_order(l9,u_0,u_1) \/
   (list_member(l8,u_0) \/ list_member(l7,u_0))
  )) /\
 (
  (
   list_head(l9,u_0) =>
   (
    list_head(l7,u_0) \/
    (
     ~list_member(l7,u_1) /\
     (
      list_head(l8,u_0) /\
      ~list_member(l7,u_0)
     )
    )
   )
  ) /\
  (list_head(l7,u_0) => list_head(l9,u_0))
 ) /\
 (list_order(l9,u_0,u_1) <=>
  (
   list_order(l8,u_0,u_1) \/
   (
    list_order(l7,u_0,u_1) \/
    (list_member(l7,u_0) /\ list_member(l8,u_1))
   )
  ))
)
```

##### libs-cons

```
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

##### libs-lazy

```
Lazy(l3,l4):=
forall u_0 u_1,(
 (list_member(l4,u_0) <=>
  list_member(l3,u_0)) /\
 (list_head(l4,u_0) <=>
  list_head(l3,u_0)) /\
 (list_order(l4,u_0,u_1) <=>
  list_order(l3,u_0,u_1))
)
```

##### libs-nil

```
Nil(l2):=
forall u_0 u_1,(
true /\
 ~(list_member(l2,u_0) \/ list_member(l2,u_1))
)
```

##### libs-reverse

```
Reverse(l5,l6):=
forall u_0 u_1,(
 (list_member(l6,u_0) <=>
  list_member(l5,u_0)) /\
 (
  (
   list_head(l6,u_0) =>
   (
    list_order(l6,u_0,u_1) \/
    (
     list_member(l6,u_0) /\
     ~list_order(l6,u_1,u_0)
    )
   )
  ) /\
  (
   (
    ~list_order(l6,u_1,u_0) /\
    (
     list_member(l6,u_0) /\
     (
      ~list_head(l5,u_0) /\
      (
       ~list_member(l6,u_1) \/
       (
        list_order(l6,u_0,u_1) /\
        ~list_head(l5,u_1)
       )
      )
     )
    )
   ) =>
   list_head(l6,u_0)
  )
 ) /\
 (list_order(l6,u_0,u_1) <=>
  list_order(l5,u_1,u_0))
)
```

#### assertion-1

```
Snoc(lenf,f,lenr,r,x,lenf',f',lenr',r'):=
forall u,((list_member(f,u) \/ list_member(r,u)) <=>
 (
  (list_member(f',u) /\ list_member(r',x)) \/
  list_order(r',x,u) \/
  list_order(f',u,x)
 ))
```

#### axiom-1

```
forall dt u_0 u_1,(ite list_member(dt,u_0)
    (
     list_order(dt,u_0,u_1) \/
     (
      (u_0==u_1) \/
      (ite list_head(dt,u_0)
          (
           ~list_head(dt,u_1) /\
           ~list_order(dt,u_1,u_0)
          )
          (
           list_order(dt,u_1,u_0) \/
           ~list_member(dt,u_1)
          ))
     )
    )
    (
     ~list_head(dt,u_0) /\
     (
      ~list_order(dt,u_0,u_1) /\
      ~list_order(dt,u_1,u_0)
     )
    ))
```

#### assertion-2

```
Snoc(lenf,f,lenr,r,x,lenf',f',lenr',r'):=
forall u,((list_member(f,u) \/ list_member(r,u) \/ (u==x)) <=>
 (list_member(f',u) \/ list_member(r',u)))
```

#### axiom-2

```
	forall dt u_0 u_1,(ite list_order(dt,u_0,u_1)
    (list_member(dt,u_0) /\ list_member(dt,u_1))
    (
     ~list_order(dt,u_1,u_0) \/
     (list_member(dt,u_0) /\ list_member(dt,u_1))
    ))
```
