(declare-sort S1)
(declare-const a S1)
(declare-fun b () S1)
(declare-const x Bool)
(assert x)
(assert ((as = Bool) (as a S1) (as b S1)))
(check-sat)
(get-value (a b x))
(get-model)
(check-sat-assuming (((as not Bool) (and x (= ((as a S1)) (b))))))
(get-unsat-core)