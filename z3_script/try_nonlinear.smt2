(declare-fun p (Int Int) Bool)
(declare-fun f (Int Int Int) Bool)
(declare-fun g (Int Int Int) Bool)
;; (declare-const x Int)
;; (declare-const y Int)
;; (declare-const z Int)
(declare-const fv1 Bool)
(declare-const fv2 Bool)

(define-fun g_current ((pxu Bool) (pyu Bool)) Bool
  (or
   (and (= pxu false) (= pyu false))
   (and (= pxu false) (= pyu true))
   (and (= pxu true) (= pyu true))
   )
  ;; false
  )

(assert
 (and
  (not (and (= fv1 false) (= fv2 false)))
  (not (and (= fv1 false) (= fv2 true)))
  (not (and (= fv1 true) (= fv2 true)))
  )
 )

(forall (pxu Bool) (pyu Bool) (pzu Bool)
        (or
         (or (g_current pxu pyu) (and (= pxu fv1) (= pyu fv2)))
         (or (g_current pyu pzu) (and (= pyu fv1) (= pzu fv2)))
         )
        )
(forall ((w Int)) (=> (p x w) (p z w)))

(assert
 (not
 (forall ((x Int) (y Int) (z Int))
         (=>
          (and (forall ((w Int))
                       (or (g_current x y w) (and (= (p x w) fv1) (= (p y w) fv2)))
                       )
               (forall ((w Int))
                       (or (g_current y z w) (and (= (p y w) fv1) (= (p z w) fv2)))
                       )
               )
          (forall ((w Int)) (=> (p x w) (p z w)))
          )
         )
 )
 )
(check-sat)
(get-model)
(eval fv1)
(eval fv2)
