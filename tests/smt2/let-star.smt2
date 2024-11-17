(declare-sort L)
(declare-const x L)
(declare-fun f (L) L)
(assert (not (=
  (let* ((x (f x)) (x (f x)) (x (f x))) x)
  (f (f (f x)))
 )))
 (check-sat)