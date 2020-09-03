(declare-fun l2Reach (Int Int) Bool)
(declare-fun l1Reach (Int Int) Bool)
(declare-fun l2Next (Int Int) Bool)
(declare-fun l1Next (Int Int) Bool)

(define-fun iff ((p Bool) (q Bool)) Bool
  (and (=> p q) (=> q p))
  )

;; closure definition
;; (assert (forall ((u Int) (v Int) (w Int))
;;                 (=>
;;                  (and
;;                   (=> (and (l1Reach u w) (not (= v w))) (l1Reach v w))
;;                   (l1Reach u v)
;;                   (not (l1Reach u u))
;;                   )
;;                  (l1Next u v)
;;                  )))

;; (assert (forall ((u Int) (v Int) (w Int))
;;                 (=>
;;                  (and (l1Next u v) (not (= v w)))
;;                  (and
;;                   (=> (l1Reach u w) (l1Reach v w))
;;                   (l1Reach u v)
;;                   )
;;                  )))

;; (assert (forall ((u Int) (v Int) (w Int))
;;                 (=>
;;                  (and
;;                   (=> (and (l2Reach u w) (not (= v w))) (l2Reach v w))
;;                   (l2Reach u v)
;;                   (not (l2Reach u u))
;;                   )
;;                  (l2Next u v)
;;                  )))

;; (assert (forall ((u Int) (v Int) (w Int))
;;                 (=>
;;                  (and (l2Next u v) (not (= v w)))
;;                  (and
;;                   (=> (l2Reach u w) (l2Reach v w))
;;                   (l2Reach u v)
;;                   )
;;                  )))

;; step2

;; (assert (forall ((u Int) (v Int) (w Int))
;;                 (iff
;;                  (l1Next u v)
;;                  (and (l1Reach u v)
;;                       (=> (and (l1Reach u w) (not (= v w))) (l1Reach v w))
;;                       )
;;                  )
;;                 ))

;; (assert (forall ((u Int) (v Int) (w Int))
;;                 (iff
;;                  (l2Next u v)
;;                  (and (l2Reach u v)
;;                       (=> (and (l2Reach u w) (not (= v w))) (l2Reach v w))
;;                       )
;;                  )
;;                 ))

;; (assert (forall ((u Int) (v Int) (w Int))
;;                 (=>
;;                  (and (l1Next u v) (l1Next v w))
;;                  (l1Next u w)
;;                  )
;;                 ))

;; (assert (forall ((u Int) (v Int) (w Int))
;;                 (=>
;;                  (and (l2Next u v) (l2Next v w))
;;                  (l2Next u w)
;;                  )
;;                 ))

;; exists

(assert (forall ((u Int) (v Int))
                (=>
                 (and (l1Reach u v) (not (l1Reach u u)))
                 (or (l1Next u v)
                      (exists ((w Int)) (and (l1Next u w) (l1Reach w v)))
                      )
                 )
                ))

(assert (forall ((u Int) (v Int))
                (=>
                 (and (l2Reach u v) (not (l2Reach u u)))
                 (or (l2Next u v)
                     (exists ((w Int)) (and (l2Next u w) (l2Reach w v)))
                     )
                 )
                ))

(assert (forall ((u Int) (v Int))
                (=>
                 (or (l1Next u v)
                     (exists ((w Int)) (and (l1Next u w) (l1Reach w v) (not (l1Reach w w))))
                     )
                (l1Reach u v)
                ))
        )

(assert (forall ((u Int) (v Int))
                (=>
                 (or (l2Next u v)
                     (exists ((w Int)) (and (l2Next u w) (l2Reach w v) (not (l2Reach w w))))
                     )
                 (l2Reach u v)
                 ))
        )

;; specification
;; (assert
;;  (forall ((u Int) (v Int)) (iff (l2Reach u v) (l1Reach u v))
;;          )
;;  )

(assert
 (forall ((u Int) (v Int))
         (and
          (=> (l2Reach u v) (and (l1Reach u v) (not (= u v))))
          (=> (and (l1Reach u v) (not (l1Reach v u))) (l2Reach u v))
          )
         )
 )
;; elements in the tree are distinct
(assert (forall ((u Int)) (not (l1Reach u u))))
(assert (forall ((u Int) (v Int) (w Int)) (=> (and (l1Next u v) (l1Next u w)) (= v w))))

(push)

(assert (not (forall ((u Int) (v Int)) (=> (l1Next u v) (l2Next u v)))))
(check-sat)

;; 1,2,3
;;  u v w next(u,v) reach(u,v) reach(u,w) reach(v,w) =(u,v) =(u,w) =(v,w)
;; (1,1,1)  _         _          _          _          t       t      t
;; (1,1,2)  _         _          t          t          t       _      _
;; (1,1,3)  _         _          t          t          t       _      _
;; (1,2,1)  t         t          _          _          _       t      _
;; (1,2,2)  t         t          t          _          _       _      t
;; (1,2,3)  t         t          t          t          _       _      _
;; (1,3,1)  _         t          _          _          _       t      _
;; (1,3,2)  _         t          t          _          _       _      _
;; (1,3,3)  _         t          t          _          _       _      t
;; (2,1,1)  _         _          _          _          _       _      t
;; (2,1,2)  _         _          _          t          _       t      _
;; (2,1,3)  _         _          t          t          _       _      _
;; (2,2,1)  _         _          _          _          t       _      _
;; (2,2,2)  _         _          _          _          t       t      t
;; (2,2,3)  _         _          t          t          t       _      _
;; (2,3,1)  t         t          _          _          _       _      _
;; (2,3,2)  t         t          _          _          _       t      _
;; (2,3,3)  t         t          t          _          _       _      t
;; (3,1,1)  _         _          _          _          _       _      t
;; (3,1,2)  _         _          _          t          _       _      _
;; (3,1,3)  _         _          _          t          _       t      _
;; (3,2,1)  _         _          _          _          _       _      _
;; (3,2,2)  _         _          _          _          _       _      t
;; (3,2,3)  _         _          _          t          _       t      _
;; (3,3,1)  _         _          _          _          t       _      _
;; (3,3,2)  _         _          _          _          t       _      _
;; (3,3,3)  _         _          _          _          t       t      t
