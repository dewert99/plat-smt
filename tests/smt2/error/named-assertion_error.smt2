(check-sat-assuming ((! false :named x) unbound))
(declare-const x Bool)
(check-sat)