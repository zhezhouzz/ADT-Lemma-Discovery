## custom-stack

#### prog

```
let rec concat l1 l2 =
  if Stack.is_empty l1 then l2
  else Stack.push (Stack.top l1) (concat (Stack.tail l1) l2)
```

#### vc

```
(ite StackIsEmpty(l1)
    Concat(l1,l2,l2)
    ((
 StackTop(l1,x) /\
 StackTail(l1,l3) /\
 Concat(l3,l2,l4) /\
 StackPush(x,l4,l5)
) => 
     Concat(l1,l2,l5)
    ))
```

#### specs
##### StackIsEmpty

```
StackIsEmpty(l2):=
forall u_0,(
true &&
 !list_member(l2,u_0)
)
```

##### StackPush

```
StackPush(x0,l0,l1):=
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

##### StackTail

```
StackTail(l4,l5):=
forall u_0 u_1,(
 (
  (
   list_head(l5,u_0) ==> 
   (
    list_member(l5,u_0) &&
    (
     list_order(l5,u_1,u_0) ==> 
     (
      list_order(l5,u_0,u_1) &&
      (list_head(l4,u_0) ==> list_head(l4,u_1))
     )
    )
   )
  ) &&
  (
   (
    !list_member(l4,u_1) &&
    (
     list_member(l5,u_0) &&
     !list_head(l4,u_0)
    )
   ) ==> 
   list_head(l5,u_0)
  )
 ) &&
 (
  (
   list_member(l5,u_0) ==> 
   (
    list_order(l4,u_1,u_0) ||
    (
     list_member(l4,u_0) &&
     (
      list_head(l5,u_0) ||
      (
       list_order(l5,u_0,u_1) ||
       (
        !list_order(l4,u_0,u_1) &&
        !list_head(l4,u_1)
       )
      )
     )
    )
   )
  ) &&
  (
   (
    list_order(l4,u_1,u_0) ||
    (
     list_head(l5,u_0) ||
     (
      list_order(l5,u_0,u_1) ||
      (
       (u_0==u_1) &&
       (
        !list_head(l4,u_0) &&
        list_member(l4,u_0)
       )
      )
     )
    )
   ) ==> 
   list_member(l5,u_0)
  )
 ) &&
 (
  (
   list_order(l5,u_0,u_1) ==> 
   (list_order(l4,u_0,u_1) && list_member(l5,u_0))
  ) &&
  (
   (
    list_order(l4,u_0,u_1) &&
    (
     list_head(l4,u_0) ==> 
     (
      !list_order(l4,u_1,u_0) &&
      list_member(l5,u_0)
     )
    )
   ) ==> 
   list_order(l5,u_0,u_1)
  )
 )
)
```

##### StackTop

```
StackTop(l3,x1):=
forall u_0 u_1,((x1==u_0) <==> 
 list_head(l3,u_0))
```

#### assertion-1

```
Concat(l1,l2,l3):=
forall u v,(
 list_head(l1,u) ==> 
 list_member(l3,u)
)
```

#### lemma-1

```
forall dt u_0,(
 list_member(dt,u_0) ||
 !list_head(dt,u_0)
)
```

#### assertion-2

```
Concat(l1,l2,l3):=
forall u,(list_member(l3,u) <==> 
 (list_member(l1,u) || list_member(l2,u)))
```

#### lemma-2

```
forall dt u_1 u_0,(
 (
  list_member(dt,u_1) ==> 
  (
   (
    list_member(dt,u_0) ==> 
    (
     (
      list_head(dt,u_1) ==> 
      (
       list_order(dt,u_0,u_1) ||
       (
        !list_next(dt,u_0,u_1) &&
        (list_order(dt,u_1,u_0) || list_head(dt,u_0))
       )
      )
     ) &&
     (
      !list_head(dt,u_1) ==> 
      (
       list_order(dt,u_1,u_0) ||
       (
        !list_next(dt,u_1,u_0) &&
        (list_order(dt,u_0,u_1) || (u_1==u_0))
       )
      )
     )
    )
   ) &&
   (
    !list_member(dt,u_0) ==> 
    (
     !list_next(dt,u_1,u_0) &&
     (
      list_head(dt,u_1) ||
      (
       !list_order(dt,u_1,u_0) &&
       !list_head(dt,u_0)
      )
     )
    )
   )
  )
 ) &&
 (
  !list_member(dt,u_1) ==> 
  (
   !list_head(dt,u_1) &&
   (
    !list_next(dt,u_1,u_0) &&
    (
     !list_order(dt,u_0,u_1) &&
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
)
```

#### assertion-3

```
Concat(l1,l2,l3):=
forall u v,(
 (list_member(l3,u) <==> 
  (list_member(l1,u) || list_member(l2,u))) &&
 (
  (list_order(l1,u,v) || list_order(l2,u,v)) ==> 
  list_order(l3,u,v)
 )
)
```

#### lemma-3

```
forall dt u_1 u_0,(
 (
  list_member(dt,u_1) ==> 
  (
   list_order(dt,u_0,u_1) ||
   (
    (u_1==u_0) ||
    !list_head(dt,u_0)
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

#### assertion-4

```
Concat(l1,l2,l3):=
forall u,(
 (list_member(l3,u) <==> 
  (list_member(l1,u) || list_member(l2,u))) &&
 (
  list_head(l3,u) ==> 
  (list_head(l1,u) || list_head(l2,u))
 )
)
```

#### lemma-4

```
forall dt u_1 u_0,(
 (
  list_member(dt,u_1) ==> 
  (
   (
    (list_last(dt,u_1) && list_last(dt,u_0)) ==> 
    (
     (u_1==u_0) &&
     (list_order(dt,u_1,u_0) || list_once(dt,u_1))
    )
   ) &&
   (
    !list_last(dt,u_1) ==> 
    (
     list_last(dt,u_0) ||
     (
      (
       (u_1==u_0) ==> 
       (
        list_order(dt,u_1,u_0) ||
        (
         list_once(dt,u_1) &&
         !list_next(dt,u_1,u_0)
        )
       )
      ) &&
      (
       !(u_1==u_0) ==> 
       (
        (
         list_once(dt,u_0) ==> 
         (list_order(dt,u_1,u_0) || list_order(dt,u_0,u_1))
        ) &&
        (
         !list_once(dt,u_0) ==> 
         (
          (
           list_head(dt,u_1) ==> 
           (
            list_member(dt,u_0) ||
            !list_next(dt,u_1,u_0)
           )
          ) &&
          (
           !list_head(dt,u_1) ==> 
           (
            list_once(dt,u_1) ||
            (
             (
              list_member(dt,u_0) ==> 
              (list_order(dt,u_0,u_1) || list_order(dt,u_1,u_0))
             ) &&
             (
              !list_member(dt,u_0) ==> 
              (
               !list_order(dt,u_1,u_0) &&
               (
                !list_head(dt,u_0) &&
                !list_next(dt,u_1,u_0)
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
  !list_member(dt,u_1) ==> 
  (
   (
    list_member(dt,u_0) ==> 
    (
     !list_next(dt,u_0,u_1) &&
     (
      !list_once(dt,u_1) &&
      (
       !list_order(dt,u_1,u_0) &&
       (
        !list_next(dt,u_1,u_0) &&
        (
         !(u_1==u_0) &&
         (
          !list_order(dt,u_0,u_1) &&
          (
           !list_head(dt,u_1) &&
           !list_last(dt,u_1)
          )
         )
        )
       )
      )
     )
    )
   ) &&
   (
    !list_member(dt,u_0) ==> 
    (
     !list_next(dt,u_1,u_0) &&
     (
      !list_once(dt,u_1) &&
      (
       !list_order(dt,u_0,u_1) &&
       (
        !list_last(dt,u_1) &&
        (
         !list_head(dt,u_1) &&
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
   )
  )
 )
)
```

