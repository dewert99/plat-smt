(set-logic QF_UF)
(declare-sort U 0)
(declare-fun u3 () U)
(declare-fun u4 () U)
(declare-fun p (U) Bool)
(declare-fun b1 () Bool)
(declare-fun b2 () Bool) ; v7 = b2 | v8 = !b2
(declare-fun b3 () Bool) ; v11 = b3 | v10 = !b3
(assert (= b1 (p u3)))
; v5 = b1 = (p u3)
(assert (let ((b4 (p u4))) (= b2 b4)))
; v6 = b4 = (p u3) | v9 = !b4
; union v6 v7
; union v8 v9
(assert (= u3 u4))
; union v5 v6
(assert (= b3 (not b2)))
; union v10 v7
; union v11 v8
(assert (or b2 (not b3)))
(check-sat)
