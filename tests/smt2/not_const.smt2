(declare-fun a () Bool)
(assert (not a))
(check-sat)
(get-model)
