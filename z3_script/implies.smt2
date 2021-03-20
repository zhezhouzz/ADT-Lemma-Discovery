(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)

(assert
 (not
 (=
  (=> (or a b) c)
  (and (=> a c) (=> b c))
  )
 )
 )
(check-sat)
