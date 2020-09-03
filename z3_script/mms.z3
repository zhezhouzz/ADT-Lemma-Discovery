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

(define-fun spec ((l1 Int) (l2 Int) (l3 Int)) Bool
  (forall ((u Int) (v Int))
          (and
           ;; (=> (Ordering l1 u v) (Ordering l3 u v))
           (Member l3 1)
           (not (Ordering l3 1 1))
           )
          )
  )

(define-fun post ((l1 Int) (l3 Int)) Bool
  (forall ((u Int) (v Int))
          (and
           (=> (Ordering l1 u v) (Ordering l3 u v))
           (not (Ordering l3 1 1))
           )
          )
  )

(assert (spec 1 2 3))
;; (assert (not (post 1 3)))
;; (assert (cex_limit 0))
(push)

(check-sat)
(eval Ordering)
(eval Member)
