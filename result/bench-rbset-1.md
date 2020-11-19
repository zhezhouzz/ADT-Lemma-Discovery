## redblack-set

#### prog

```
let balance = function
  | B, Rbset.T (R, Rbset.T (R, a, x, b), y, c), z, d -> Rbset.makeT (R, Rbset.makeT (B, a, x, b), y, Rbset.makeT (B, c, z, d))
  | B, Rbset.T (R, Rbset.E, x, Rbset.T (R, b, y, c)), z, d -> Rbset.makeT (R, Rbset.makeT (B, Rbset.E, x, b), y, Rbset.makeT (B, c, z, d))
  | B, Rbset.T (R, Rbset.E, x, Rbset.E), z, d -> Rbset.makeT (R, Rbset.makeT (R, Rbset.E, x, Rbset.E), z, d)
  | B, Rbset.E, x, Rbset.T (R, Rbset.T (R, b, y, c), z, d) -> Rbset.makeT (R, Rbset.makeT (B, Rbset.E, x, b), y, Rbset.makeT (B, c, z, d))
  | B, Rbset.E, x, Rbset.T (R, Rbset.E, y, Rbset.T (R, c, z, d)) -> Rbset.makeT (R, Rbset.makeT (B, Rbset.E, x, Rbset.E), y, Rbset.makeT (B, c, z, d))
  | B, Rbset.E, x, Rbset.T (R, Rbset.E, y, Rbset.E) -> Rbset.makeT (R, Rbset.E, x, Rbset.makeT (R, Rbset.E, y, Rbset.E))
  | B, Rbset.E, x, Rbset.E -> Rbset.makeT (R, Rbset.E, x, Rbset.E)
  | R, b, x, d -> Rbset.makeT (R, b, x, d)
```
#### vc

```
((
 B(r1) /\
 R(r2) /\
 RbsetIsEmpty(tmpe)
) => 
 (
  ((
 RbsetMaketree(r2,a,x,b,tmp1) /\
 RbsetMaketree(r2,tmp1,y,c,tree1) /\
 RbsetMaketree(r1,a,x,b,tmp2) /\
 RbsetMaketree(r1,c,z,d,tmp3) /\
 RbsetMaketree(r2,tmp2,y,tmp3,tmp4)
) => 
   Balance(r1,tree1,z,d,tmp4)
  ) /\
  ((
 RbsetMaketree(r2,b,y,c,tmp1) /\
 RbsetMaketree(r2,tmpe,x,tmp1,tree1) /\
 RbsetMaketree(r1,tmpe,x,b,tmp2) /\
 RbsetMaketree(r1,c,z,d,tmp3) /\
 RbsetMaketree(r2,tmp2,y,tmp3,tmp4)
) => 
   Balance(r1,tree1,z,d,tmp4)
  ) /\
  ((RbsetMaketree(r2,tmpe,x,tmpe,tree1) /\ RbsetMaketree(r2,tree1,z,d,tmp4)) => 
   Balance(r1,tree1,z,d,tmp4)
  ) /\
  ((
 RbsetMaketree(r2,b,y,c,tmp1) /\
 RbsetMaketree(r2,tmp1,z,d,tree2) /\
 RbsetMaketree(r1,tmpe,x,b,tmp2) /\
 RbsetMaketree(r1,c,z,d,tmp3) /\
 RbsetMaketree(r2,tmp2,y,tmp3,tmp4)
) => 
   Balance(r1,tmpe,x,tree2,tmp4)
  ) /\
  ((
 RbsetMaketree(r2,c,z,d,tmp1) /\
 RbsetMaketree(r2,tmpe,y,tmp1,tree2) /\
 RbsetMaketree(r1,tmpe,x,tmpe,tmp2) /\
 RbsetMaketree(r1,c,z,d,tmp3) /\
 RbsetMaketree(r2,tmp2,y,tmp3,tmp4)
) => 
   Balance(r1,tmpe,x,tree2,tmp4)
  ) /\
  (RbsetMaketree(r2,tmpe,x,tmpe,tmp4) => 
   Balance(r1,tmpe,x,tmpe,tmp4)
  ) /\
  (RbsetMaketree(r1,b,x,d,tmp4) => 
   Balance(r1,b,x,d,tmp4)
  )
 )
)
```

#### specs

##### RbsetIsEmpty

```
RbsetIsEmpty(tr3):=
forall u_0,(
 !treeb_member(tr3,u_0) &&
 !!true
)
```

##### RbsetMaketree

```
RbsetMaketree(b0,tr0,x0,tr1,tr2):=
forall u_0 u_1,(
 (treeb_head(tr2,u_0) <==> 
  (x0==u_0)) &&
 (treeb_member(tr2,u_0) <==> 
  (
   treeb_left(tr2,x0,u_0) ||
   (treeb_right(tr2,x0,u_0) || treeb_head(tr2,u_0))
  )) &&
 (treeb_left(tr2,u_0,u_1) <==> 
  (
   treeb_left(tr0,u_0,u_1) ||
   (
    (
     (treeb_left(tr1,u_0,u_1) && treeb_head(tr2,u_0)) ==> 
     treeb_member(tr0,u_1)
    ) &&
    (
     !treeb_left(tr1,u_0,u_1) ==> 
     (treeb_head(tr2,u_0) && treeb_member(tr0,u_1))
    )
   )
  )) &&
 (treeb_right(tr2,u_0,u_1) <==> 
  (
   treeb_right(tr1,u_0,u_1) ||
   (
    (
     (treeb_right(tr0,u_0,u_1) && treeb_head(tr2,u_0)) ==> 
     treeb_member(tr1,u_1)
    ) &&
    (
     !treeb_right(tr0,u_0,u_1) ==> 
     (treeb_head(tr2,u_0) && treeb_member(tr1,u_1))
    )
   )
  )) &&
 (treeb_parallel(tr2,u_0,u_1) <==> 
  (
   treeb_parallel(tr0,u_0,u_1) ||
   (
    treeb_parallel(tr1,u_0,u_1) ||
    (treeb_right(tr2,x0,u_1) && treeb_left(tr2,x0,u_0))
   )
  ))
)
```
#### assertion-1

```
Balance(r1,tree1,x,tree2,tree3):=
forall u,(treeb_member(tree3,u) <==> 
 (treeb_member(tree1,u) || treeb_member(tree2,u) || (u==x)))
```

#### lemma-1

```
forall dt u_1 u_0,(
 (
  treeb_head(dt,u_1) ==> 
  (
   (
    treeb_member(dt,u_0) ==> 
    (
     (
      treeb_head(dt,u_0) ==> 
      (
       (
        treeb_once(dt,u_1) ==> 
        (
         !treeb_left(dt,u_1,u_0) &&
         (
          !treeb_right(dt,u_1,u_0) &&
          !treeb_parallel(dt,u_1,u_0)
         )
        )
       ) &&
       (
        !treeb_once(dt,u_1) ==> 
        (treeb_left(dt,u_1,u_0) || treeb_right(dt,u_1,u_0))
       )
      )
     ) &&
     (
      (
       !treeb_head(dt,u_0) &&
       treeb_once(dt,u_1)
      ) ==> 
      (
       treeb_right(dt,u_1,u_0) ||
       (
        !treeb_left(dt,u_0,u_1) &&
        !treeb_parallel(dt,u_0,u_1)
       )
      )
     )
    )
   ) &&
   (
    !treeb_member(dt,u_0) ==> 
    (
     treeb_member(dt,u_1) &&
     (
      !treeb_left(dt,u_1,u_0) &&
      (
       !treeb_parallel(dt,u_0,u_1) &&
       (
        !treeb_right(dt,u_1,u_0) &&
        !treeb_once(dt,u_0)
       )
      )
     )
    )
   )
  )
 ) &&
 (
  !treeb_head(dt,u_1) ==> 
  (
   (
    (u_1==u_0) ==> 
    (
     (
      treeb_member(dt,u_1) ==> 
      (
       treeb_parallel(dt,u_1,u_0) ||
       (
        (
         treeb_once(dt,u_1) ==> 
         (
          !treeb_left(dt,u_1,u_0) &&
          !treeb_right(dt,u_1,u_0)
         )
        ) &&
        (
         !treeb_once(dt,u_1) ==> 
         (treeb_left(dt,u_1,u_0) || treeb_right(dt,u_1,u_0))
        )
       )
      )
     ) &&
     (
      !treeb_member(dt,u_1) ==> 
      (
       !treeb_left(dt,u_1,u_0) &&
       (
        !treeb_once(dt,u_1) &&
        (
         !treeb_right(dt,u_1,u_0) &&
         !treeb_parallel(dt,u_1,u_0)
        )
       )
      )
     )
    )
   ) &&
   (
    !(u_1==u_0) ==> 
    (
     (
      treeb_once(dt,u_1) ==> 
      (
       treeb_right(dt,u_0,u_1) ||
       (
        treeb_member(dt,u_1) &&
        (
         treeb_parallel(dt,u_0,u_1) ||
         (
          (
           (treeb_head(dt,u_0) && treeb_once(dt,u_0)) ==> 
           !treeb_parallel(dt,u_1,u_0)
          ) &&
          (
           !treeb_head(dt,u_0) ==> 
           (
            treeb_parallel(dt,u_1,u_0) ||
            (
             (
              treeb_once(dt,u_0) ==> 
              (
               treeb_member(dt,u_0) &&
               (
                treeb_left(dt,u_1,u_0) ||
                (treeb_left(dt,u_0,u_1) || treeb_right(dt,u_1,u_0))
               )
              )
             ) &&
             (
              !treeb_once(dt,u_0) ==> 
              (
               treeb_member(dt,u_0) ||
               (
                !treeb_left(dt,u_1,u_0) &&
                !treeb_left(dt,u_0,u_1)
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
      !treeb_once(dt,u_1) ==> 
      (
       (
        treeb_member(dt,u_1) ==> 
        (
         treeb_parallel(dt,u_1,u_0) ||
         (
          treeb_right(dt,u_0,u_1) ||
          (
           (
            (
             (treeb_left(dt,u_0,u_1) && treeb_head(dt,u_0)) &&
             treeb_once(dt,u_0)
            ) ==> 
            !treeb_left(dt,u_1,u_0)
           ) &&
           (
            !treeb_left(dt,u_0,u_1) ==> 
            (
             treeb_left(dt,u_1,u_0) ||
             (
              treeb_once(dt,u_0) ||
              (
               (
                treeb_member(dt,u_0) ==> 
                (treeb_right(dt,u_1,u_0) || treeb_parallel(dt,u_0,u_1))
               ) &&
               (
                !treeb_member(dt,u_0) ==> 
                (
                 !treeb_right(dt,u_1,u_0) &&
                 !treeb_parallel(dt,u_0,u_1)
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
        !treeb_member(dt,u_1) ==> 
        (
         (
          treeb_member(dt,u_0) ==> 
          (
           !treeb_right(dt,u_0,u_1) &&
           (
            !treeb_parallel(dt,u_1,u_0) &&
            !treeb_left(dt,u_0,u_1)
           )
          )
         ) &&
         (
          !treeb_member(dt,u_0) ==> 
          (
           !treeb_left(dt,u_0,u_1) &&
           (
            !treeb_left(dt,u_1,u_0) &&
            (
             !treeb_parallel(dt,u_1,u_0) &&
             (
              !treeb_right(dt,u_0,u_1) &&
              (
               !treeb_head(dt,u_0) &&
               (
                !treeb_right(dt,u_1,u_0) &&
                (
                 !treeb_parallel(dt,u_0,u_1) &&
                 !treeb_once(dt,u_0)
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
  )
 )
)
```
