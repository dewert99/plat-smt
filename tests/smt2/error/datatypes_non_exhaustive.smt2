(declare-datatypes ((OBool 0)) (((none) (some (unwrap Bool)))))
(declare-const o OBool)
(assert (match o (((some b) b))))