(declare-const z Bool)
(define-const x Bool (or (! false :named y) unbound))
(define-const x Bool true)
(define-const y Bool false) ; these should work since the first command failed and nothing was bound
(define-const a Bool (! z :named a))