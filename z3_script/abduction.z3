;; (define-fun range ((a Int)) Bool
;;              (or (= a 1) (= a 2) (= a 3))
;;              )
;; (declare-const b Int)
;; (assert (forall ((a Int))
;;                 (=> (range a) (> b a))
;;                 )
;;         )
;; (apply qe)
;; (exit)

(declare-fun member (Int Int) Bool)
(define-fun range ((l Int)) Bool
  (or
   (forall ((u Int)) (= (member l u) (= u 1)))
   (forall ((u Int)) (= (member l u) (= u 2)))
   )
  )
(declare-const l1 Int)
(declare-const l2 Int)

(assert
 (forall ((u Int) (v Int))
          (=> (and (range l1) (range l2) (member l1 u) (member l2 v)) (> u v))
         )
 )
(apply qe)
(exit)
