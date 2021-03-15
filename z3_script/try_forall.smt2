(declare-fun member (Int Int) Bool)
(declare-fun hd (Int Int) Bool)

(define-fun f1 ((A Int) (x Int)) Bool
   (forall ((u Int))
      (= (member A x) (= u x))
   )
  )

(define-fun f2 ((A Int) (x Int)) Bool
  (forall ((u Int))
          (= (hd A x) (= u x))
          )
  )

(declare-const x Int)
(declare-const y Int)
(declare-const A Int)

(push)
(assert
 (not (=> (and (f1 A x) (f1 A y)) (= x y)))
 )
(check-sat)
(pop)

(push)
(assert
 (not (=> (and (f2 A x) (f2 A y)) (= x y)))
 )
(check-sat)
(pop)
