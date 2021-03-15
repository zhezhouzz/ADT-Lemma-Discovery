(declare-fun list_member (Int Int) Bool)
(declare-fun list_head (Int Int) Bool)
(declare-fun Inv (Bool Int) Bool)

(assert
 (forall ((s1 Int) (s2 Int))
         (let (
               (a!2 (forall ((u Int))
                            (and (= (list_member s2 u)
                                    (or (list_member s1 u) (list_member s2 u)))
                                 (=> (list_head s2 u) (or (list_head s1 u) (list_head s2 u)))))))
           (not (=> (Inv true s1) a!2)))
         )
  )
(check-sat)
