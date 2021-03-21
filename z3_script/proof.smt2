(declare-fun p_f (Int Int) Bool)
(declare-fun delta_f (Int Int Int Int) Bool)
(declare-fun delta_f_weaker (Int Int Int Int) Bool)

(assert
 (forall ((x Int) (y Int) (u Int) (v Int))
         (=>
          (delta_f x y u v)
          (delta_f_weaker x y u v)
          )
         )
 )

(assert
 (forall ((x Int) (y Int))
         (=
          (p_f x y)
          (forall ((u Int) (v Int))
                  (delta_f x y u v)
                  )
          )
         )
 )

(declare-const x Int)
(declare-const y Int)

(assert
 (not
  (=>
   (p_f x y)
   (forall ((u Int) (v Int))
           (delta_f_weaker x y u v)
           )
   )
  )
 )

;; (assert
;;  (not
;;  (=>
;;   (forall ((x Int) (y Int))
;;           (=
;;            (p_f x y)
;;            (forall ((u Int) (v Int))
;;                    (delta_f x y u v)
;;                    )
;;            )
;;           )
;;   (forall ((x Int) (y Int))
;;           (=
;;            (p_f x y)
;;            (forall ((u Int) (v Int))
;;                    (delta_f_weaker x y u v)
;;                    )
;;            )
;;           )
;;   )
;;  )
;;  )

(check-sat)
(get-model)
