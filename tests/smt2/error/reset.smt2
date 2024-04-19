(set-option :print-success true)
(set-option :produce-models false)
(check-sat)
(get-model) ; fail
(reset-assertions)
(check-sat)
(get-model) ; fail
(reset)
(check-sat)
(get-model) ; succeed