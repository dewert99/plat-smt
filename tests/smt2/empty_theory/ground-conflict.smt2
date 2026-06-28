(declare-const a Bool)
(assert (= a (not a)))
(check-sat)
(check-sat)