(declare-fun l2Reach (Int Int) Bool)
(declare-fun l1Reach (Int Int) Bool)
(declare-fun l2Next (Int Int) Bool)
(declare-fun l1Next (Int Int) Bool)

(define-fun limit_l1Reach ((maxnum Int)) Bool
  (forall ((u Int) (v Int))
          (=>
           (or
           (< u 0) (< v 0) (> u maxnum) (> v maxnum)
           )
           (not (l1Reach u v))
           )
          )
  )

(define-fun limit_l2Reach ((maxnum Int)) Bool
  (forall ((u Int) (v Int))
          (=>
           (or
            (< u 0) (< v 0) (> u maxnum) (> v maxnum)
            )
           (not (l2Reach u v))
           )
          )
  )

(define-fun limit_l1Next ((maxnum Int)) Bool
  (forall ((u Int) (v Int))
          (=>
           (or
            (< u 0) (< v 0) (> u maxnum) (> v maxnum)
            )
           (not (l1Next u v))
           )
          )
  )

(define-fun limit_l2Next ((maxnum Int)) Bool
  (forall ((u Int) (v Int))
          (=>
           (or
            (< u 0) (< v 0) (> u maxnum) (> v maxnum)
            )
           (not (l2Next u v))
           )
          )
  )

(define-fun limit ((maxnum Int)) Bool
  (and (limit_l1Reach maxnum) (limit_l2Reach maxnum)
       (limit_l1Next maxnum) (limit_l1Next maxnum))
  )

(define-fun l1_reach_trans ((none Bool)) Bool
  (forall ((u Int) (v Int) (w Int))
          (=>
           (and (l1Reach u v) (l1Reach v w))
           (l1Reach u w)
           )
          )
  )

(define-fun l2_reach_trans ((none Bool)) Bool
  (forall ((u Int) (v Int) (w Int))
          (=>
           (and (l2Reach u v) (l2Reach v w))
           (l2Reach u w)
           )
          )
  )

(define-fun l1_forall_constant ((none Bool)) Bool
  (forall ((u Int) (v Int) (w Int))
          (iff
           (l1Next u v)
           (and (l1Reach u v)
                (=> (and (l1Reach u w) (not (= v w))) (l1Reach v w))
                )
           )
          )
  )
(define-fun l2_forall_constant ((none Bool)) Bool
  (forall ((u Int) (v Int) (w Int))
          (iff
           (l2Next u v)
           (and (l2Reach u v)
                (=> (and (l2Reach u w) (not (= v w))) (l2Reach v w))
                )
           )
          )
  )
(define-fun l1_distinct ((none Bool)) Bool
  (forall ((u Int)) (not (l1Reach u u)))
  )
(define-fun spec ((none Bool)) Bool
  (forall ((u Int) (v Int))
          (and
           (=> (l2Reach u v) (and (l1Reach u v) (not (= u v))))
           (=> (and (l1Reach u v) (not (l1Reach v u))) (l2Reach u v))
           )
          )
  )
(define-fun post ((none Bool)) Bool
  (forall ((u Int) (v Int)) (=> (l1Next u v) (l2Next u v)))
  )
;; (assert (l1_forall_constant true))
;; (assert (l2_forall_constant true))
;; (assert (l1_reach_trans true))
;; (assert (l2_reach_trans true))

;; (assert (forall ((u Int) (v Int))
;;                 (=>
;;                  (and (l1Reach u v) (l1Reach u v))
;;                  (or (l1Reach u u) (l1Reach v v))
;;                  )
;;                 )
;;         )

(assert (forall ((u Int) (v Int))
                (and
                 ;; (forall ((w Int)) (=> (and (l1Next u v) (l1Next u w)) (= w v)))
                 (iff
                  (and (l1Reach u v)
                       (forall ((w Int)) (=> (and (l1Reach u w) (not (= w v))) (l1Reach v w)))
                       )
                  (l1Next u v)
                  )
                 (not (and (l1Reach u v) (l1Reach v u)))
                 )
                )
        )

(assert (forall ((u Int) (v Int))
                (and
                 ;; (forall ((w Int)) (=> (and (l2Next u v) (l2Next u w)) (= w v)))
                 (=> (l2Next u v)
                  (and (l2Reach u v)
                       (forall ((w Int)) (=> (and (l2Reach u w) (not (= w v))) (l2Reach v w)))
                       )
                  )
                 (=>
                  (and (l2Reach u v)
                       (forall ((w Int)) (=> (and (l2Reach u w) (not (= w v))) (l2Reach v w)))
                       )
                  (l2Next u v)
                  )
                 (not (and (l2Reach u v) (l2Reach v u)))
                 )
                )
 )

(assert (spec true))
;; elements in the tree are distinct
(assert (l1_distinct true))
;; (assert (forall ((u Int) (v Int) (w Int)) (=> (and (l1Next u v) (l1Next u w)) (= v w))))
;; (assert (limit 2))
(push)

(assert (not (forall ((u Int) (v Int)) (=> (l1Next u v) (l2Next u v)))))
;; (assert (l1Next 0 1))
;; (assert (l1Next 1 2))
;; (assert (l1Reach 0 1))
;; (assert (l1Reach 1 2))
;; (assert (l1Reach 0 2))
;; (assert (l2Reach 0 1))
;; (assert (l2Reach 1 2))
;; (assert (l2Reach 0 2))
;; (assert (not (l2Next 0 1)))
(check-sat)
(eval (l1Next 0 1))
(eval (l1Next 0 2))
(eval (l1Next 1 0))
(eval (l1Next 1 2))
(eval (l1Next 2 0))
(eval (l1Next 2 1))
(eval (l1Reach 2 0))
(eval (l2Reach 2 0))
(eval (l2Reach 2 1))
(eval (l2Next 2 1))
