## bankers-queue

#### prog

```
let snoc (lenf, f, lenr, r) x =
  let lenr = lenr + 1 in
  let r = lazy (Bankersq.cons (x, r)) in
  if lenr <= lenf then (lenf, f, lenr, r)
  else (lenf + lenr, f ++ Bankersq.reverse r, 0, lazy Bankersq.nil)
```

#### vc

```
((
 equal(const1,1) /\
 (
  Plus(lenr,const1,lenr') /\
  (
   BankersqCons(x,r,tmp0) /\
   (
    Lazy(tmp0,r') /\
    (ite Le(lenr',lenf')
        (
         equal(x1,lenf) /\
         equal(x2,f) /\
         equal(x3,lenr') /\
         equal(x4,r')
        )
        (
         Plus(lenf,lenr',tmp1) /\
         (
          BankersqReverse(r',tmp5) /\
          (
           BankersqConcat(f,tmp5,tmp2) /\
           (
            equal(tmp3,0) /\
            (
             BankersqNil(tmp6) /\
             (
              Lazy(tmp6,tmp4) /\
              (
               equal(x1,tmp1) /\
               equal(x2,tmp2) /\
               equal(x3,tmp3) /\
               equal(x4,tmp4)
              )
             )
            )
           )
          )
         )
        ))
   )
  )
 )
) => 
 Snoc(lenf,f,lenr,r,x,x1,x2,x3,x4)
)
```

#### specs
##### BankersqConcat

```
BankersqConcat(l7,l8,l9):=
forall u_0 u_1,(
 (
  (
   list_head(l9,u_0) ==> 
   (
    list_head(l7,u_0) ||
    (
     !list_member(l7,u_1) &&
     (
      list_head(l8,u_0) &&
      !list_member(l7,u_0)
     )
    )
   )
  ) &&
  (list_head(l7,u_0) ==> list_head(l9,u_0))
 ) &&
 (list_member(l9,u_0) <==> 
  (
   list_order(l9,u_0,u_1) ||
   (list_member(l8,u_0) || list_member(l7,u_0))
  )) &&
 (list_order(l9,u_0,u_1) <==> 
  (
   list_order(l8,u_0,u_1) ||
   (
    list_order(l7,u_0,u_1) ||
    (list_member(l7,u_0) && list_member(l8,u_1))
   )
  ))
)
```

##### BankersqCons

```
BankersqCons(x0,l0,l1):=
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

##### BankersqNil

```
BankersqNil(l2):=
forall u_0,(
true &&
 !list_member(l2,u_0)
)
```

##### BankersqReverse

```
BankersqReverse(l5,l6):=
forall u_0 u_1,(
 (
  (
   list_head(l6,u_0) ==> 
   (
    list_order(l6,u_0,u_1) ||
    (
     list_member(l6,u_0) &&
     !list_order(l6,u_1,u_0)
    )
   )
  ) &&
  (
   !true ==> 
   list_head(l6,u_0)
  )
 ) &&
 (list_member(l6,u_0) <==> 
  list_member(l5,u_0)) &&
 (list_order(l6,u_0,u_1) <==> 
  list_order(l5,u_1,u_0))
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
#### assertion-2

```
Snoc(lenf,f,lenr,r,x,lenf',f',lenr',r'):=
forall u,((list_member(f,u) || list_member(r,u) || (u==x)) <==> 
 (list_member(f',u) || list_member(r',u)))
```

#### lemma-2

```
forall dt u_1 u_0,(
 (
  list_member(dt,u_1) ==> 
  (
   (
    list_head(dt,u_0) ==> 
    (
     list_order(dt,u_0,u_1) ||
     (
      (u_1==u_0) &&
      !list_next(dt,u_1,u_0)
     )
    )
   ) &&
   (
    !list_head(dt,u_0) ==> 
    (
     (
      (u_1==u_0) ==> 
      (
       list_order(dt,u_1,u_0) ||
       !list_next(dt,u_1,u_0)
      )
     ) &&
     (
      !(u_1==u_0) ==> 
      (
       (
        list_order(dt,u_1,u_0) ==> 
        (
         list_order(dt,u_0,u_1) ||
         (
          list_head(dt,u_1) ||
          (
           list_member(dt,u_0) &&
           !list_next(dt,u_0,u_1)
          )
         )
        )
       ) &&
       (
        !list_order(dt,u_1,u_0) ==> 
        (
         !list_next(dt,u_1,u_0) &&
         (list_member(dt,u_0) ==> list_order(dt,u_0,u_1))
        )
       )
      )
     )
    )
   )
  )
 ) &&
 (
  !list_member(dt,u_1) ==> 
  (
   !list_next(dt,u_1,u_0) &&
   (
    !list_head(dt,u_1) &&
    (
     !list_order(dt,u_0,u_1) &&
     !list_order(dt,u_1,u_0)
    )
   )
  )
 )
)
```
