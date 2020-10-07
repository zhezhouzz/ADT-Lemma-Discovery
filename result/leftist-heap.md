## leftist-heap

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
(
 (E(tree2) => Merge(tree1,tree2,tree1)) /\
 (E(tree1) => Merge(tree1,tree2,tree2)) /\
 ((
 T(rank1,x,a1,b1,tree1) /\
 T(rank2,y,a2,b2,tree2) /\
 (ite Le(x,y)
     (Merge(b1,tree2,tmp) /\ makeT(x,a1,tmp,tree3))
     (Merge(tree1,b2,tmp) /\ makeT(y,a2,tmp,tree3)))
) =>
  Merge(tree1,tree2,tree3)
 )
)
```

#### specs

##### libs-t

```
T(x0,x1,tr0,tr1,tr2):=
forall u_0 u_1,(
 (treei_head(tr2,u_0) <=>
  (x1==u_0)) /\
 (treei_member(tr2,u_0) <=>
  (
   treei_left(tr2,x1,u_0) \/
   (treei_right(tr2,x1,u_0) \/ treei_head(tr2,u_0))
  )) /\
 (treei_left(tr2,u_0,u_1) <=>
  (
   treei_left(tr0,u_0,u_1) \/
   (ite treei_head(tr2,u_0)
       treei_member(tr0,u_1)
       treei_left(tr1,u_0,u_1))
  )) /\
 (treei_right(tr2,u_0,u_1) <=>
  (
   treei_right(tr1,u_0,u_1) \/
   (ite treei_right(tr0,u_0,u_1)
       (
        ~treei_head(tr2,u_0) \/
        treei_member(tr1,u_1)
       )
       (treei_head(tr2,u_0) /\ treei_member(tr1,u_1)))
  )) /\
 (treei_parallel(tr2,u_0,u_1) <=>
  (ite treei_right(tr2,x1,u_1)
      (treei_left(tr2,x1,u_0) \/ treei_parallel(tr1,u_0,u_1))
      treei_parallel(tr0,u_0,u_1)))
)
```

##### libs-e

```
E(tr6):=
forall u_0 u_1,(
 (
  ~treei_member(tr6,u_0) /\
  ~treei_member(tr6,u_1)
 ) /\
 ~~true
)
```

##### libs-makeT

```
makeT(x2,tr3,tr4,tr5):=
forall u_0 u_1,(
 (treei_head(tr5,u_0) <=>
  (x2==u_0)) /\
 (treei_member(tr5,u_0) <=>
  (
   treei_member(tr3,u_0) \/
   (treei_member(tr4,u_0) \/ treei_head(tr5,u_0))
  )) /\
 (treei_left(tr5,u_0,u_1) <=>
  (ite treei_left(tr3,u_0,u_1)
      (
       ~treei_head(tr5,u_0) \/
       (
        treei_member(tr4,u_1) \/
        ~treei_right(tr5,x2,u_1)
       )
      )
      (ite treei_left(tr4,u_0,u_1)
          (
           treei_parallel(tr5,u_1,u_0) \/
           ~treei_right(tr5,u_0,u_1)
          )
          (
           treei_head(tr5,u_0) /\
           (
            treei_member(tr5,u_1) /\
            (ite treei_head(tr4,x2)
                (
                 treei_head(tr5,u_1) \/
                 ~treei_right(tr5,x2,u_1)
                )
                (ite treei_head(tr5,u_1)
                    (ite treei_member(tr3,x2)
                        (
                         ~treei_right(tr5,x2,u_1) \/
                         treei_member(tr4,x2)
                        )
                        (
                         ~treei_right(tr5,x2,u_1) /\
                         treei_member(tr4,x2)
                        ))
                    (
                     ~treei_right(tr5,x2,u_1) \/
                     (treei_member(tr4,u_1) /\ treei_member(tr3,u_1))
                    )))
           )
          )))) /\
 (treei_right(tr5,u_0,u_1) <=>
  (ite treei_left(tr5,u_0,x2)
      (ite treei_parallel(tr5,x2,u_1)
          (
           treei_right(tr4,u_0,u_1) \/
           (ite treei_left(tr4,u_0,x2)
               treei_right(tr3,u_0,u_1)
               (ite (u_0==u_1)
                   (ite treei_right(tr3,u_0,u_1)
                       (
                        ~treei_head(tr5,u_0) \/
                        treei_member(tr4,x2)
                       )
                       (treei_head(tr5,u_0) /\ treei_member(tr4,x2)))
                   (ite treei_member(tr3,x2)
                       (ite treei_left(tr4,x2,u_0)
                           treei_right(tr3,u_0,u_1)
                           (
                            treei_head(tr5,x2) /\
                            (
                             treei_member(tr5,x2) /\
                             (
                              treei_member(tr5,u_0) /\
                              (
                               treei_member(tr5,u_1) /\
                               (
                                ~treei_right(tr4,u_0,x2) /\
                                (
                                 treei_member(tr3,u_0) /\
                                 (ite treei_left(tr4,x2,u_1)
                                     (
                                      treei_left(tr5,u_0,u_1) \/
                                      (
                                       ~treei_head(tr4,u_1) \/
                                       treei_right(tr3,u_0,u_1)
                                      )
                                     )
                                     (ite treei_left(tr4,u_0,u_1)
                                         treei_right(tr3,u_0,u_1)
                                         (
                                          ~treei_right(tr4,x2,u_1) /\
                                          (
                                           ~treei_right(tr4,u_1,x2) /\
                                           (ite treei_parallel(tr4,u_0,x2)
                                               treei_right(tr3,u_0,u_1)
                                               (ite treei_parallel(tr5,u_0,u_1)
                                                   (
                                                    ~treei_left(tr5,x2,u_0) \/
                                                    (ite treei_right(tr4,x2,u_0)
                                                        treei_right(tr3,u_0,u_1)
                                                        (ite treei_parallel(tr5,u_0,x2)
                                                            (ite treei_parallel(tr5,x2,u_0)
                                                                (ite treei_head(tr3,u_1)
                                                                    (
                                                                     ~treei_parallel(tr3,u_0,u_1) \/
                                                                     (
                                                                      treei_head(tr5,u_0) /\
                                                                      (
                                                                       treei_member(tr4,u_1) \/
                                                                       ~treei_left(tr5,x2,u_1)
                                                                      )
                                                                     )
                                                                    )
                                                                    (ite treei_head(tr4,x2)
                                                                        (
                                                                         ~treei_left(tr5,x2,u_1) \/
                                                                         treei_right(tr3,x2,u_0)
                                                                        )
                                                                        (ite treei_left(tr3,u_1,x2)
                                                                            (
                                                                             treei_right(tr3,u_0,u_1) \/
                                                                             (
                                                                              treei_left(tr5,u_0,u_1) /\
                                                                              (
                                                                               treei_member(tr4,x2) \/
                                                                               (treei_member(tr4,u_1) /\ treei_head(tr5,u_0))
                                                                              )
                                                                             )
                                                                            )
                                                                            (
                                                                             treei_right(tr3,u_1,u_0) \/
                                                                             (ite treei_left(tr3,u_1,u_0)
                                                                                 ~treei_head(tr5,u_1)
                                                                                 (
                                                                                  ~treei_right(tr3,u_1,x2) /\
                                                                                  (ite treei_head(tr4,u_0)
                                                                                      treei_right(tr3,u_0,u_1)
                                                                                      (ite treei_head(tr5,u_1)
                                                                                          treei_right(tr3,u_0,u_1)
                                                                                          (
                                                                                           ~(x2==u_1) /\
                                                                                           (ite treei_right(tr3,x2,u_0)
                                                                                               treei_member(tr4,u_1)
                                                                                               (
                                                                                                treei_parallel(tr3,u_1,x2) \/
                                                                                                (
                                                                                                 treei_member(tr4,u_1) /\
                                                                                                 (
                                                                                                  treei_right(tr3,u_0,u_1) \/
                                                                                                  (
                                                                                                   treei_head(tr5,u_0) /\
                                                                                                   (
                                                                                                    ~treei_left(tr5,x2,u_1) \/
                                                                                                    treei_member(tr3,u_1)
                                                                                                   )
                                                                                                  )
                                                                                                 )
                                                                                                )
                                                                                               ))
                                                                                          )))
                                                                                 ))
                                                                            ))))
                                                                treei_right(tr3,u_0,u_1))
                                                            (ite treei_member(tr4,u_1)
                                                                (treei_head(tr5,u_0) \/ treei_right(tr3,u_0,u_1))
                                                                treei_parallel(tr5,x2,u_0))))
                                                   )
                                                   treei_right(tr3,u_0,u_1)))
                                          )
                                         )))
                                )
                               )
                              )
                             )
                            )
                           ))
                       treei_head(tr3,u_1))))
          )
          (
           treei_right(tr4,u_0,u_1) /\
           ~treei_head(tr5,u_0)
          ))
      (
       treei_right(tr4,u_0,u_1) \/
       (
        treei_right(tr3,u_0,u_1) \/
        (
         treei_head(tr5,u_0) /\
         (
          treei_parallel(tr5,x2,u_1) \/
          (ite treei_member(tr3,u_1)
              (
               treei_member(tr4,u_1) \/
               ~treei_left(tr5,x2,u_1)
              )
              (
               treei_member(tr4,x2) \/
               (
                ~treei_left(tr5,x2,u_1) /\
                treei_head(tr4,u_1)
               )
              ))
         )
        )
       )
      ))) /\
 (treei_parallel(tr5,u_0,u_1) <=>
  (
   treei_parallel(tr3,u_0,u_1) \/
   (ite treei_right(tr5,x2,u_1)
       (treei_left(tr5,x2,u_0) \/ treei_parallel(tr4,u_0,u_1))
       treei_parallel(tr4,u_0,u_1))
  ))
)
```

#### assertion-1

```
Merge(tree1,tree2,tree3):=
forall u,(treei_member(tree3,u) <=>
 (treei_member(tree1,u) \/ treei_member(tree2,u)))
```

#### axiom-1

```
forall dt u_0 u_1,(ite treei_member(dt,u_0)
    (
     (u_0==u_1) \/
     (ite treei_parallel(dt,u_0,u_1)
         (ite treei_left(dt,u_0,u_1)
             (
              ~treei_head(dt,u_1) \/
              treei_left(dt,u_1,u_0)
             )
             (
              treei_head(dt,u_1) \/
              (
               treei_member(dt,u_1) /\
               (
                ~treei_head(dt,u_0) \/
                ~treei_left(dt,u_1,u_0)
               )
              )
             ))
         (ite treei_member(dt,u_1)
             (
              ~treei_right(dt,u_0,u_1) \/
              (
               ~treei_right(dt,u_1,u_0) \/
               (
                treei_parallel(dt,u_1,u_0) \/
                (
                 ~treei_head(dt,u_0) /\
                 ~treei_left(dt,u_0,u_1)
                )
               )
              )
             )
             (
              ~treei_parallel(dt,u_1,u_0) /\
              (
               ~treei_left(dt,u_1,u_0) /\
               (
                ~treei_right(dt,u_0,u_1) /\
                ~treei_right(dt,u_1,u_0)
               )
              )
             )))
    )
    (
     ~treei_parallel(dt,u_0,u_1) /\
     (
      ~treei_right(dt,u_1,u_0) /\
      (
       ~treei_head(dt,u_0) /\
       (
        ~treei_left(dt,u_0,u_1) /\
        (
         ~treei_left(dt,u_1,u_0) /\
         (
          ~treei_right(dt,u_0,u_1) /\
          (
           (u_0==u_1) \/
           (
            ~treei_parallel(dt,u_1,u_0) /\
            (
             ~treei_head(dt,u_1) \/
             treei_member(dt,u_1)
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
Merge(tree1,tree2,tree3):=
forall u v,(
 (
  (
   treei_head(tree3,u) /\
   (treei_head(tree1,v) \/ treei_head(tree2,v))
  ) =>
  (u<=v)
 ) /\
 (treei_member(tree3,u) <=>
  (treei_member(tree1,u) \/ treei_member(tree2,u)))
)
```

#### axiom-2

```
forall dt u_0 u_1,(ite treei_member(dt,u_0)
    (
     (u_0==u_1) \/
     (ite treei_member(dt,u_1)
         (
          ~treei_head(dt,u_1) \/
          ~treei_head(dt,u_0)
         )
         (
          ~treei_left(dt,u_0,u_1) /\
          (
           treei_head(dt,u_0) \/
           (
            ~treei_left(dt,u_1,u_0) /\
            ~treei_parallel(dt,u_0,u_1)
           )
          )
         ))
    )
    (
     ~treei_left(dt,u_1,u_0) /\
     (
      ~treei_head(dt,u_0) /\
      (
       ~treei_left(dt,u_0,u_1) /\
       (
        ~treei_right(dt,u_0,u_1) /\
        (
         ~treei_right(dt,u_1,u_0) /\
         (
          (u_0==u_1) \/
          (
           ~treei_parallel(dt,u_1,u_0) /\
           (
            ~treei_head(dt,u_1) \/
            treei_member(dt,u_1)
           )
          )
         )
        )
       )
      )
     )
    ))
```
