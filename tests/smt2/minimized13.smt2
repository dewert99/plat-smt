(set-logic QF_UF)
(declare-sort U 0)
(declare-fun u3 () U)
(declare-fun u4 () U)
(declare-fun b1 () Bool)
; v5 = (ite b1 u4 u3)
; v6 = b2 = (= v5 u4)
; v8 = b3 = (= v5 u3)
(assert (let ((x (ite b1 u4 u3))) true))
; b4 = (= u4 u3)
; v11 = b1 = (not b4)
; v9 = (not b1) = b4
(assert (= b1 (distinct u4 u3)))
(check-sat)
