## redblack-set

#### prog

```
let rec merge tree1 tree2 =
  match tree1, tree2 with
  | tree1, E -> tree1
  | E, tree2 -> tree2
  | T (rank1, x, a1, b1), T (rank2, y, a2, b2) ->
    if Elem.leq x y then makeT x a1 (merge b1 tree2)
    else makeT y a2 (merge tree1 b2)
```

#### vc

```
((
 B(r1) /\
 R(r2) /\
 E(tmpe)
) =>
 (
  ((
 T(r2,a,x,b,tmp1) /\
 T(r2,tmp1,y,c,tree1) /\
 T(r1,a,x,b,tmp2) /\
 T(r1,c,z,d,tmp3) /\
 T(r2,tmp2,y,tmp3,tmp4)
) =>
   Balance(r1,tree1,z,d,tmp4)
  ) /\
  ((
 T(r2,b,y,c,tmp1) /\
 T(r2,tmpe,x,tmp1,tree1) /\
 T(r1,tmpe,x,b,tmp2) /\
 T(r1,c,z,d,tmp3) /\
 T(r2,tmp2,y,tmp3,tmp4)
) =>
   Balance(r1,tree1,z,d,tmp4)
  ) /\
  ((T(r2,tmpe,x,tmpe,tree1) /\ T(r2,tree1,z,d,tmp4)) =>
   Balance(r1,tree1,z,d,tmp4)
  ) /\
  ((
 T(r2,b,y,c,tmp1) /\
 T(r2,tmp1,z,d,tree2) /\
 T(r1,tmpe,x,b,tmp2) /\
 T(r1,c,z,d,tmp3) /\
 T(r2,tmp2,y,tmp3,tmp4)
) =>
   Balance(r1,tmpe,x,tree2,tmp4)
  ) /\
  ((
 T(r2,c,z,d,tmp1) /\
 T(r2,tmpe,y,tmp1,tree2) /\
 T(r1,tmpe,x,tmpe,tmp2) /\
 T(r1,c,z,d,tmp3) /\
 T(r2,tmp2,y,tmp3,tmp4)
) =>
   Balance(r1,tmpe,x,tree2,tmp4)
  ) /\
  (T(r2,tmpe,x,tmpe,tmp4) =>
   Balance(r1,tmpe,x,tmpe,tmp4)
  ) /\
  (T(r1,b,x,d,tmp4) =>
   Balance(r1,b,x,d,tmp4)
  )
 )
)
```

#### specs

##### libs-t

```
T(b0,tr0,x0,tr1,tr2):=
forall u_0 u_1,(
 (treeb_head(tr2,u_0) <=>
  (x0==u_0)) /\
 (treeb_member(tr2,u_0) <=>
  (
   treeb_left(tr2,x0,u_0) \/
   (treeb_right(tr2,x0,u_0) \/ treeb_head(tr2,u_0))
  )) /\
 (treeb_left(tr2,u_0,u_1) <=>
  (
   treeb_left(tr0,u_0,u_1) \/
   (ite treeb_left(tr1,u_0,u_1)
       (
        treeb_member(tr0,u_1) \/
        ~treeb_head(tr2,u_0)
       )
       (treeb_head(tr2,u_0) /\ treeb_member(tr0,u_1)))
  )) /\
 (treeb_right(tr2,u_0,u_1) <=>
  (
   treeb_right(tr1,u_0,u_1) \/
   (ite treeb_right(tr0,u_0,u_1)
       (
        ~treeb_head(tr2,u_0) \/
        treeb_member(tr1,u_1)
       )
       (treeb_head(tr2,u_0) /\ treeb_member(tr1,u_1)))
  )) /\
 (treeb_parallel(tr2,u_0,u_1) <=>
  (
   treeb_parallel(tr0,u_0,u_1) \/
   (
    treeb_right(tr2,x0,u_1) /\
    (treeb_left(tr2,x0,u_0) \/ treeb_parallel(tr1,u_0,u_1))
   )
  ))
)
```

##### libs-e

```
forall u_0 u_1,(
 (
  ~treeb_member(tr3,u_0) /\
  ~treeb_member(tr3,u_1)
 ) /\
 ~~true
)
```

#### assertion-1

```
Balance(r1,tree1,x,tree2,tree3):=
forall u,(treeb_member(tree3,u) <=>
 (treeb_member(tree1,u) \/ treeb_member(tree2,u) \/ (u==x)))
```

#### axiom-1

```
forall dt u_0 u_1,(ite treeb_member(dt,u_0)
    (
     treeb_left(dt,u_1,u_0) \/
     (ite treeb_head(dt,u_1)
         (
          treeb_left(dt,u_0,u_1) \/
          (ite treeb_head(dt,u_0)
              (
               treeb_right(dt,u_0,u_1) \/
               ~treeb_parallel(dt,u_0,u_1)
              )
              ~treeb_right(dt,u_0,u_1))
         )
         (
          treeb_parallel(dt,u_0,u_1) \/
          (
           (u_0==u_1) \/
           (ite treeb_member(dt,u_1)
               (
                treeb_left(dt,u_0,u_1) \/
                (
                 treeb_parallel(dt,u_1,u_0) \/
                 (
                  treeb_right(dt,u_0,u_1) /\
                  ~treeb_right(dt,u_1,u_0)
                 )
                )
               )
               (
                ~treeb_right(dt,u_0,u_1) /\
                (
                 treeb_head(dt,u_0) \/
                 (
                  ~treeb_left(dt,u_0,u_1) /\
                  ~treeb_parallel(dt,u_1,u_0)
                 )
                )
               ))
          )
         ))
    )
    (
     ~treeb_left(dt,u_1,u_0) /\
     (
      ~treeb_right(dt,u_1,u_0) /\
      (
       ~treeb_parallel(dt,u_0,u_1) /\
       (
        treeb_member(dt,u_1) \/
        (
         (u_0==u_1) \/
         (
          ~treeb_head(dt,u_0) /\
          (
           ~treeb_head(dt,u_1) /\
           (
            ~treeb_left(dt,u_0,u_1) /\
            (
             ~treeb_right(dt,u_0,u_1) /\
             ~treeb_parallel(dt,u_1,u_0)
            )
           )
          )
         )
        )
       )
      )
     )
    ))
```

#### assertion-2

```
Balance(r1,tree1,x,tree2,tree3):=
(forall u v,(
 (
  (treeb_left(tree1,u,v) \/ treeb_right(tree1,u,v) \/ treeb_parallel(tree1,u,v)) =>
  ~(u==v)
 ) /\
 (
  (treeb_left(tree2,u,v) \/ treeb_right(tree2,u,v) \/ treeb_parallel(tree2,u,v)) =>
  ~(u==v)
 ) /\
 (
  (treeb_member(tree1,u) /\ treeb_member(tree1,v)) =>
  ~(u==v)
 ) /\
 (
  (treeb_member(tree1,u) \/ treeb_member(tree2,u)) =>
  ~(u==x)
 )
)) =>
(forall u v,(
 (
  (treeb_left(tree3,u,v) \/ treeb_right(tree3,u,v) \/ treeb_parallel(tree3,u,v)) =>
  ~(u==v)
 ) /\
 (treeb_member(tree3,u) <=>
  (treeb_member(tree1,u) \/ treeb_member(tree2,u) \/ (u==x)))
))
```

#### axiom-2

```
forall dt u_0 u_1,(ite treeb_member(dt,u_0)
    (
     treeb_left(dt,u_0,u_1) \/
     (
      treeb_right(dt,u_1,u_0) \/
      (
       treeb_left(dt,u_1,u_0) \/
       (
        ~treeb_member(dt,u_1) \/
        (
         treeb_right(dt,u_0,u_1) \/
         (ite treeb_parallel(dt,u_0,u_1)
             ~treeb_head(dt,u_0)
             ((u_0==u_1) \/ treeb_parallel(dt,u_1,u_0)))
        )
       )
      )
     )
    )
    (
     treeb_member(dt,u_1) \/
     (
      ~treeb_head(dt,u_0) /\
      (
       ~treeb_left(dt,u_0,u_1) /\
       (
        ~treeb_left(dt,u_1,u_0) /\
        (
         ~treeb_right(dt,u_0,u_1) /\
         (
          ~treeb_head(dt,u_1) /\
          (
           ~treeb_right(dt,u_1,u_0) /\
           ~treeb_parallel(dt,u_0,u_1)
          )
         )
        )
       )
      )
     )
    ))
```
