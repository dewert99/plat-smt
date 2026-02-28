; Models returned depend on the number of sorts declared before
(declare-sort M)
(declare-fun p (Bool) Bool)
(declare-fun f (Bool) M)
(check-sat)
(get-model)
(get-value ((p true) (p false) (f true) (f false)))