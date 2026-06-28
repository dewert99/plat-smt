(set-logic QF_UF)
(declare-sort U 0)
(declare-sort T 0)
(declare-fun f (U) U)
(declare-fun b1 () Bool) ; v15 (not b1 == v16)
(declare-fun b2 () Bool)
(declare-fun b3 () Bool) ; v12 (not b3 == v13)
(declare-fun b4 () Bool) ;
(declare-fun t3 () T)
(declare-fun u4 () U)
(declare-fun u5 () U)
(declare-fun t6 () T)
(declare-fun t7 () T)
(declare-fun u8 () U)
(assert (not (= t7 t6))) ; b5/v10
(assert (= (= t3 t6) b3)) ; b6/v11
; b3 = b6
(assert (= b1 (not (= t3 t7)))) ; b7/v14
; b1 = b7
(assert (= b2 (not (= t3 t6))))
; b2 = !b6 = !b3
(assert (= b1 (not b4)))
; b1 = b7 = !b4
(assert (not (= (f u8) (f (ite b3 u5 (ite b4 u8 u5))))))
; v23 = (f u8)
; v24 = (ite b4 u8 u5)
; v25 = b10 = (= v24 u8)
; v27 = b11 = (= v24 u5)
; v28 = (ite b3 u5 v24) 
; v29 = b12 = (= v28 u5)
; v31 = b13 = (= v28 v24)
; v32 = (f v28)
; v33 = b14 = (= v23 v32)
(check-sat)
