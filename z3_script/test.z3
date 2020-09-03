(define-fun iff ((a Bool) (b Bool)) Bool
  (and (=> a b) (=> b a))
  )

(declare-fun next_star (Int Int) Bool)
(assert
 (and
  (forall ((a Int) (b Int))
          iff (= a b) (and (next_star a b) (next_star b a))
          )
  (forall ((a Int) (b Int) (c Int))
          (=> (and (next_star a b) (next_star b c)) (next_star a c))
          )
  (forall ((a Int) (b Int) (c Int))
          (=> (and (next_star a b) (next_star a c))
             (or (next_star b c) (next_star c b)))
          )
  )
 )

(declare-fun next_star2 (Int Int) Bool)
(assert
 (and
  (forall ((a Int) (b Int))
          iff (= a b) (and (next_star2 a b) (next_star2 b a))
          )
  (forall ((a Int) (b Int) (c Int))
          (=> (and (next_star2 a b) (next_star2 b c)) (next_star2 a c))
          )
  (forall ((a Int) (b Int) (c Int))
          (=> (and (next_star2 a b) (next_star2 a c))
             (or (next_star2 b c) (next_star2 c b)))
          )
  )
 )

(define-fun ac ((a Bool) (b Bool)) Bool
  (and (=> a b) (=> b a))
  )

(check-sat)
(get-model)

;; (assert (= l2 (tail l1)))
;; (assert (= 1 (length l2)))
;; (assert (not (= (length l1) (+ 1 (length l2)))))
;; (check-sat)
;; (get-model)
