(declare-sort ET)
(declare-fun f (ET ET) ET)
(declare-const al ET)
(define-const bl ET (f al al))
(define-const cl ET (f bl bl))
(define-const dl ET (f cl cl))
(declare-const ar ET)
(define-const br ET (f ar ar))
(define-const cr ET (f br br))
(define-const dr ET (f cr cr))
(check-sat-assuming ((= al ar) (not (= dl dr))))
(get-unsat-core)