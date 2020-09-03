(declare-fun Ordering (Int Int Int) Bool)
(declare-fun Member (Int Int) Bool)

(define-fun cex_limit_ordering ((maxnum Int)) Bool
  (forall ((l Int) (u Int) (v Int))
          (=>
           (or
            (< u 0) (< v 0) (> u maxnum) (> v maxnum)
            )
           (not (Ordering l u v))
           )
          )
  )

(define-fun cex_limit_member ((maxnum Int)) Bool
  (forall ((l Int) (u Int))
          (=>
           (or
            (< u 0) (> u maxnum)
            )
           (not (Member l u))
           )
          )
  )

(define-fun cex_limit ((maxnum Int)) Bool
  (and (cex_limit_ordering maxnum) (cex_limit_member maxnum))
  )

(define-fun spec ((l1 Int) (l2 Int)) Bool
  (and
   (forall ((u Int)) (iff (Member l1 u) (Member l2 u)))
   (forall ((u Int) (v Int)) (iff (Ordering l1 u v) (Ordering l2 u v)))
   )
  )

(define-fun post ((l1 Int) (l2 Int)) Bool
  (forall ((u Int) (v Int)) (=> (Ordering l1 u v) (Member l2 u)))
  )

(assert (spec 1 2))
(assert (not (post 1 2)))
(assert (cex_limit 0))
(push)

(check-sat)
(echo "ordering l1")
(eval (Ordering 1 0 0))
(eval (Ordering 1 0 1))
(eval (Ordering 1 1 0))
(eval (Ordering 1 1 1))
(echo "ordering l2")
(eval (Ordering 2 0 0))
(eval (Ordering 2 0 1))
(eval (Ordering 2 1 0))
(eval (Ordering 2 1 1))
(echo "membership l1")
(eval (Member 1 0))
(eval (Member 1 1))
(echo "membership l2")
(eval (Member 2 0))
(eval (Member 2 1))
