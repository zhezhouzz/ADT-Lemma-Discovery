(assert
 (forall ((a (Array Int Int)))
         (=>
          (forall ((u Int)) (>= (select a u) 0))
         (>= (select a 3) 0)
         )
         )
 )
(check-sat)

(check-sat-using (then qe smt))
