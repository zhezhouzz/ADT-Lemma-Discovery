## stream

#### prog

```
let rec reverse' acc s =
  lazy (
    match s with
    | lazy Nil -> Lazy.force acc
    | lazy (Cons (hd, tl)) -> Lazy.force (reverse' (lazy (Cons (hd, acc))) tl))
```
#### vc

```
(
 ((
 Nil(tmp1) /\
 Lazy(tmp1,s) /\
 Force(acc,tmp3) /\
 Lazy(tmp3,l3)
) => 
  Reverse(acc,s,l3)
 ) /\
 ((
 Cons(hd,tl,tmp1) /\
 Lazy(tmp1,s) /\
 Cons(hd,acc,tmp2) /\
 Lazy(tmp2,tmp3) /\
 Reverse(tmp3,tl,tmp4) /\
 Force(tmp4,tmp5) /\
 Lazy(tmp5,l3)
) => 
  Reverse(acc,s,l3)
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

##### Force

```
Force(l5,l6):=
forall u_0 u_1,(
 (list_head(l6,u_0) <==> 
  list_head(l5,u_0)) &&
 (list_member(l6,u_0) <==> 
  list_member(l5,u_0)) &&
 (list_order(l6,u_0,u_1) <==> 
  list_order(l5,u_0,u_1))
)
```

##### Lazy

```
Lazy(l3,l4):=
forall u_0 u_1,(
 (list_head(l4,u_0) <==> 
  list_head(l3,u_0)) &&
 (list_member(l4,u_0) <==> 
  list_member(l3,u_0)) &&
 (list_order(l4,u_0,u_1) <==> 
  list_order(l3,u_0,u_1))
)
```

##### Nil

```
Nil(l2):=
forall u_0,(
true &&
 !list_member(l2,u_0)
)
```
#### assertion-2

```
Reverse(l1,l2,l3):=
forall u v,(
 (
  (
   list_order(l1,u,v) ||
   list_order(l2,v,u) ||
   (list_member(l2,u) && list_member(l1,v))
  ) ==> 
  list_order(l3,u,v)
 ) &&
 (list_member(l3,u) <==> 
  (list_member(l1,u) || list_member(l2,u)))
)
```

#### lemma-2

```
forall dt u_1 u_0,(
 (
  list_member(dt,u_1) ==> 
  (
   list_member(dt,u_0) ||
   !list_order(dt,u_1,u_0)
  )
 ) &&
 (
  !list_member(dt,u_1) ==> 
  (
   !list_next(dt,u_1,u_0) &&
   (
    !list_order(dt,u_0,u_1) &&
    !list_order(dt,u_1,u_0)
   )
  )
 )
)
```
