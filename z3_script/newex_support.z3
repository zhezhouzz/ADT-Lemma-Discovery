(define-fun iff ((p Bool) (q Bool)) Bool
  (and (=> p q) (=> q p))
  )

(declare-const l0_loc (Array Int Int))
(declare-const l0_length (Int))
(declare-fun l0_order_loc (Int Int) Bool)

(define-fun l0_member ((u Int)) Bool
  (exists ((uidx Int)) (and (>= uidx 0) (<= uidx l0_length) (= (select l0_loc uidx) u)))
  )

(define-fun l0_order ((u Int) (v Int)) Bool
  (exists ((uidx Int) (vidx Int)) (and (>= uidx 0) (>= vidx 0)
                                  (<= uidx l0_length) (<= vidx l0_length)
                                  (= (select l0_loc uidx) u)
                                  (= (select l0_loc vidx) v)
                                  (l0_order_loc u v)
                                  ))
  )

(assert (forall ((u Int) (v Int)) (iff (and (l0_order_loc u v) (l0_order_loc v u)) (= u v))))
(assert (forall ((u Int) (v Int) (w Int)) (=> (and (l0_order_loc u v) (l0_order_loc v w)) (l0_order_loc u w))))
(assert (forall ((u Int) (v Int) (w Int)) (=> (and (l0_order_loc u v) (l0_order_loc u w)) (or (l0_order_loc v w) (l0_order_loc w v)))))

(declare-const l1_loc (Array Int Int))
(declare-const l1_length (Int))
(declare-fun l1_order_loc (Int Int) Bool)

(define-fun l1_member ((u Int)) Bool
  (exists ((uidx Int)) (and (>= uidx 0) (<= uidx l1_length) (= (select l1_loc uidx) u)))
  )

(define-fun l1_order ((u Int) (v Int)) Bool
  (exists ((uidx Int) (vidx Int)) (and (>= uidx 0) (>= vidx 0)
                                  (<= uidx l1_length) (<= vidx l1_length)
                                  (= (select l1_loc uidx) u)
                                  (= (select l1_loc vidx) v)
                                  (l1_order_loc u v)
                                  ))
  )

(assert (forall ((u Int) (v Int)) (iff (and (l1_order_loc u v) (l1_order_loc v u)) (= u v))))
(assert (forall ((u Int) (v Int) (w Int)) (=> (and (l1_order_loc u v) (l1_order_loc v w)) (l1_order_loc u w))))
(assert (forall ((u Int) (v Int) (w Int)) (=> (and (l1_order_loc u v) (l1_order_loc u w)) (or (l1_order_loc v w) (l1_order_loc w v)))))

(declare-const l2_loc (Array Int Int))
(declare-const l2_length (Int))
(declare-fun l2_order_loc (Int Int) Bool)

(define-fun l2_member ((u Int)) Bool
  (exists ((uidx Int)) (and (>= uidx 0) (<= uidx l2_length) (= (select l2_loc uidx) u)))
  )

(define-fun l2_order ((u Int) (v Int)) Bool
  (exists ((uidx Int) (vidx Int)) (and (>= uidx 0) (>= vidx 0)
                                  (<= uidx l2_length) (<= vidx l2_length)
                                  (= (select l2_loc uidx) u)
                                  (= (select l2_loc vidx) v)
                                  (l2_order_loc u v)
                                  ))
  )

(assert (forall ((u Int) (v Int)) (iff (and (l2_order_loc u v) (l2_order_loc v u)) (= u v))))
(assert (forall ((u Int) (v Int) (w Int)) (=> (and (l2_order_loc u v) (l2_order_loc v w)) (l2_order_loc u w))))
(assert (forall ((u Int) (v Int) (w Int)) (=> (and (l2_order_loc u v) (l2_order_loc u w)) (or (l2_order_loc v w) (l2_order_loc w v)))))

;; specification
(assert
 (forall ((u Int) (v Int)) (iff
                            (l2_order v u)
                            (or (l0_order u v) (l1_order u v) (and (l0_member u) (l1_member v)))
                            ))
 )

(push)

(assert (forall ((u Int) (v Int)) (=> (l0_order u v) (<= u v))))
(assert (forall ((u Int) (v Int)) (=> (l1_order u v) (<= u v))))
(assert (forall ((u Int) (v Int)) (=> (and (l0_member u) (l1_member v)) (<= u v))))
(assert (not (forall ((u Int) (v Int)) (=> (l2_order u v) (>= u v)))))

(check-sat)
(get-model)
