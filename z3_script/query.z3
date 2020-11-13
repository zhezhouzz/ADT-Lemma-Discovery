; This example illustrates basic arithmetic and 
; uninterpreted functions

(define-fun g ((x!0 Int) (x!1 Int)) Int
    (ite (and (= x!0 2) (= x!1 2)) 0
      0))
  (define-fun f ((x!0 Int)) Int
    (ite (= x!0 2) (- 1)
    (ite (= x!0 3) 1
      (- 1))))
(assert (exists ((v Int) (u Int)) (> (f u) (g u v))))
(check-sat)
(get-model)
