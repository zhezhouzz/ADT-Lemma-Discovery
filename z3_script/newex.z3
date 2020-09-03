(declare-fun l_member (Int) Bool)
(declare-fun l_order (Int Int) Bool)
(declare-fun t_member (Int) Bool)
(declare-fun t_left_children (Int Int) Bool)
(declare-fun t_right_children (Int Int) Bool)
(declare-fun t_adj_children (Int Int) Bool)

(define-fun TreeReachStar ((a Int) (b Int)) Bool
  (or
   (t_left_children a b)
   (t_right_children a b)
   (t_adj_children a b)
   )
  )

(define-fun ListReachStar ((a Int) (b Int)) Bool
  (l_order a b)
  )

(define-fun TreeReach ((a Int) (b Int)) Bool
  (and (TreeReachStar a b) (forall ((w Int)) (=> (and (TreeReachStar a w) (not (= b w))) (TreeReachStar b w))))
  )

(define-fun ListReach ((a Int) (b Int)) Bool
  (and (ListReachStar a b) (forall ((w Int)) (=> (and (ListReachStar a w) (not (= b w))) (ListReachStar b w))))
  )

(define-fun iff ((p Bool) (q Bool)) Bool
  (and (=> p q) (=> q p))
  )

;; specification
(assert
 (forall ((u Int)) (iff (l_member u) (t_member u)))
 )

;; specification
(assert
 (forall ((u Int) (v Int)) (iff (TreeReachStar u v) (ListReachStar u v)))
 )

(push)

(assert (forall ((u Int)) (not (TreeReachStar u u))))
(assert (not (forall ((u Int) (v Int)) (=> (TreeReach u v) (ListReach u v)))))
(check-sat)
(get-model)

(pop)

(assert (forall ((u Int)) (not (TreeReachStar u u))))
(assert (not (forall ((u Int) (v Int) (w Int)) (=> (and (t_left_children w u) (t_right_children w v)) (ListReachStar u v)))))
(check-sat)
(get-model)
