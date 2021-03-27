(declare-fun list_member (Int Int) Bool)
(declare-fun list_head (Int Int) Bool)

(declare-const s1 Int)
(declare-const s2 Int)
(declare-const nu_top Int)
(declare-const nu_tail Int)
(declare-const nu_concat Int)
(declare-const nu Int)

(assert
 (let (
       ;; is_empty(s1) = false
       (a!1 (forall ((u_0 Int))
                    (=> (not (list_member s1 u_0)) (not (list_head s1 u_0)))))
       ;; top(s1) = nu_top
       (a!2 (forall ((u_0 Int))
                    (and (list_member s1 nu_top)
                         (list_head s1 nu_top)
                         (=> (list_head s1 u_0) (= u_0 nu_top)))))
       ;; concat(nu_tail, s2) = nu_concat
       (a!3 (forall ((u_0 Int))
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
       ;; post(s1, s2, nu)
       (a!5 (forall ((u Int))
                    (and (= (list_member nu u)
                            (or (list_member s1 u) (list_member s2 u)))
                         (=> (list_head nu u) (or (list_head s1 u) (list_head s2 u)))))))
   (let ((a!4 (and
               ;; is_empty(s1) = false
               a!1
               ;; top(s1) = nu_top
               a!2
               ;; tail(s1) = nu_tail
               (forall ((u_0 Int))
                       (let ((a!1 (=> (and (list_member s1 u_0)
                                          (not (list_member nu_tail u_0)))
                                     (list_head s1 u_0)))
                             (a!2 (=> (not (list_member s1 u_0))
                                     (and (not (list_member nu_tail u_0))
                                          (not (list_head s1 u_0))))))
                         (and a!1 a!2)))
               ;; concat(nu_tail, s2) = nu_concat
               a!3
               ;; push(nu_top, nu_concat, s2) = nu
               (forall ((u_0 Int))
                       (let ((a!1 (=> (not (list_member nu_concat u_0))
                                     (and (not (list_member nu u_0))
                                          (not (list_head nu_concat u_0))))))
                         (let ((a!2 (=> (not (= u_0 nu_top))
                                       (and (not (list_head nu u_0))
                                            (=> (list_member nu_concat u_0)
                                               (list_member nu u_0))
                                            a!1))))
                           (and (list_head nu nu_top) (list_member nu nu_top) a!2)))))))
     (not (=> a!4 a!5))))
 )
(check-sat)
