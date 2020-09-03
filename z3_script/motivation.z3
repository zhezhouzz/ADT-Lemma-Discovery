(declare-fun l2Reach (Int Int) Bool)
(declare-fun l1Reach (Int Int) Bool)
(declare-fun l2Next (Int Int) Bool)
(declare-fun l1Next (Int Int) Bool)

(define-fun iff ((p Bool) (q Bool)) Bool
  (and (=> p q) (=> q p))
  )

;; closure definition
(assert (forall ((u Int) (v Int))
                (iff
                 (l1Reach u v)
                 (or
                  (exists ((z Int)) (and (l1Next u z) (l1Reach z v)))
                  (l1Next u v)
                  )
                 )))

(assert (forall ((u Int) (v Int))
                (iff
                 (l2Reach u v)
                 (or
                  (exists ((z Int)) (and (l2Next u z) (l2Reach z v)))
                  (l2Next u v)
                  )
                 )))

;; specification
(assert
 (forall ((u Int) (v Int)) (and
                            (=> (l2Reach u v) (l1Reach u v))
                            (=> (and (l1Next u v) (not (l1Next v u))) (l2Reach u v))
                            )
         )
 )
;; elements in the tree are distinct
(assert (forall ((u Int)) (not (l1Reach u u))))
(assert (forall ((u Int) (v Int) (w Int)) (=> (and (l1Next u v) (l1Next u w)) (= v w))))

(push)

(assert (not (forall ((u Int) (v Int)) (=> (l1Next u v) (l2Next u v)))))
(check-sat)
