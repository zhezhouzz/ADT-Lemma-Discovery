(declare-fun l1Reach_ (Int Int Int) Bool)
(declare-fun l1Reach (Int Int) Bool)
(declare-fun l1Next (Int Int) Bool)

(define-fun iff ((p Bool) (q Bool)) Bool
  (and (=> p q) (=> q p))
  )

;; closure definition
(assert (forall ((u Int) (v Int) (k Int))
                (iff
                 (l1Reach_ u v k)
                 (or
                  (exists ((z Int) (zk Int)) (and (l1Next u z) (l1Reach_ z v (- zk 1))))
                  (l1Next u v)
                  )
                 )))
(assert (forall ((u Int) (v Int))
                (exists ((k Int)) (and (> k 0) (l1Reach_ u v k)))
                ))

(assert (not(=>
         (forall ((u Int) (v Int)) (=> (l1Next u v) (< u v)))
         (forall ((u Int) (v Int)) (=> (l1Reach u v) (< u v)))
         )))

(check-sat)
