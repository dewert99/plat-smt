(declare-const i Bool)
(declare-const x Bool)
(declare-const y Bool)
(declare-const o Bool)
(assert (or (if i x y) o))
(check-sat-assuming ((not o) (not y)))
(get-value (i x y o))
(get-model)
(declare-sort U)
(declare-const a U)
(declare-const b U)
(assert (= (if i a b) b))
(check-sat-assuming ((not (= a b))))
(get-value (i x y o a b))
(get-model)