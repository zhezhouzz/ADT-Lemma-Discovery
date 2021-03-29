(declare-fun list_member (Int Int) Bool)
(declare-fun list_head (Int Int) Bool)

(declare-const s1 Int)
(declare-const s2 Int)
(declare-const nu_top Int)
(declare-const nu_tail Int)
(declare-const nu_concat Int)
(declare-const nu Int)

;; feature vector
(declare-const _fv!0 Bool)
(declare-const _fv!1 Bool)
(declare-const _fv!2 Bool)
(declare-const _fv!3 Bool)
(declare-const _fv!4 Bool)

(assert
(let ((a!1 (and (forall ((u_0 Int)) (not (list_member s1 u_0))) (= s2 nu)))
      (a!2 (forall ((u_0 Int))
             (or (=> (not (list_member s1 u_0)) (not (list_head s1 u_0))) true)))
      (a!3 (forall ((u_0 Int))
             (let ((a!1 (=> (and (list_member s1 u_0)
                                 (not (list_member nu_tail u_0)))
                            (list_head s1 u_0)))
                   (a!2 (=> (not (list_member s1 u_0))
                            (and (not (list_member nu_tail u_0))
                                 (not (list_head s1 u_0)))))
                   (a!3 (=> (and (list_member s1 u_0)
                                 (not (list_member nu_tail u_0)))
                            (list_head nu_tail u_0))))
             (let ((a!4 (and a!3
                             (=> (not (list_member s1 u_0))
                                 (not (list_member nu_tail u_0))))))
               (or (and a!1 a!2) (=> (not (list_head s1 u_0)) a!4))))))
      (a!4 (forall ((u_0 Int))
             (let ((a!1 (and (=> (and (list_member nu_tail u_0)
                                      (list_head nu_tail u_0))
                                 (list_head nu_concat u_0))
                             (=> (not (list_member nu_tail u_0))
                                 (not (list_head nu_concat u_0)))))
                   (a!4 (=> (not (list_member nu_concat u_0))
                            (and (not (list_member nu_tail u_0))
                                 (not (list_head nu_tail u_0))
                                 (not (list_member s2 u_0))
                                 (not (list_head s2 u_0))
                                 (not (list_head nu_concat u_0))))))
             (let ((a!2 (=> (and (list_member s2 u_0) (not (list_head s2 u_0)))
                            a!1)))
             (let ((a!3 (and a!2
                             (=> (not (list_member s2 u_0))
                                 (list_member nu_tail u_0)))))
               (and (=> (list_member nu_concat u_0) a!3) a!4))))))
      (a!6 (forall ((u Int))
             (and (= (list_member nu u)
                     (or (list_member s1 u) (list_member s2 u)))
                  (=> (list_head nu u) (or (list_head s1 u) (list_head s2 u))))))
      (a!7 (ite _fv!3 (ite _fv!2 (ite _fv!4 true (not true)) true) (not true)))
      (a!8 (ite _fv!0
                (ite _fv!1 (ite _fv!4 true (not true)) true)
                (ite _fv!1 (not true) (ite _fv!4 (not true) true))))
      (a!10 (not (or (and _fv!0 _fv!1 _fv!2 _fv!3 (not _fv!4))
                     (and (not _fv!0) _fv!1 _fv!2 _fv!3 (not _fv!4))
                     (and (not _fv!0) (not _fv!1) (not _fv!2) (not _fv!3) _fv!4)))))
(let ((a!5 (and a!2
                (forall ((u_0 Int))
                  (let ((a!1 (=> (not (list_member s1 u_0))
                                 (and (not (list_member s1 nu_top))
                                      (not (= u_0 nu_top))))))
                  (let ((a!2 (and (=> (and (list_member s1 u_0)
                                           (list_member s1 nu_top))
                                      (= u_0 nu_top))
                                  a!1)))
                  (let ((a!3 (and (=> (and (list_head s1 u_0)
                                           (list_head s1 nu_top))
                                      a!2)
                                  (=> (not (list_head s1 u_0))
                                      (not (= u_0 nu_top))))))
                  (let ((a!4 (or (and (list_member s1 nu_top)
                                      (list_head s1 nu_top)
                                      (=> (list_head s1 u_0) (= u_0 nu_top)))
                                 a!3
                                 (and (= (list_member s1 u_0) _fv!0)
                                      (= (list_member s1 nu_top) _fv!1)
                                      (= (list_head s1 u_0) _fv!2)
                                      (= (list_head s1 nu_top) _fv!3)
                                      (= (= u_0 nu_top) _fv!4)))))
                    (and a!4))))))
                a!3
                a!4
                (forall ((u_0 Int))
                  (let ((a!1 (=> (not (list_member nu_concat u_0))
                                 (and (not (list_member nu u_0))
                                      (not (list_head nu_concat u_0))))))
                  (let ((a!2 (=> (not (= u_0 nu_top))
                                 (and (not (list_head nu u_0))
                                      (=> (list_member nu_concat u_0)
                                          (list_member nu u_0))
                                      a!1))))
                    (and (list_head nu nu_top) (list_member nu nu_top) a!2))))))
      (a!9 (or (ite _fv!1 a!7 (not true))
               (ite _fv!2 (ite _fv!3 a!8 true) (ite _fv!4 (not true) true)))))
  (and
   ;; \Sigma[\Delta] ==> \Phi, there are two paths(a!1 and a!5)
   (=> (or a!1 a!5) a!6)
   ;; pos feature vector is not consistent with initial solution
   (not a!9)
   ;; pos feature vector is euqal to tested feature vectors
   a!10)))
 )
(check-sat)
(eval _fv!0)
(eval _fv!1)
(eval _fv!2)
(eval _fv!3)
(eval _fv!4)