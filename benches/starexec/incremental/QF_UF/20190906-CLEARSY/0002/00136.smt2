(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(set-info :source |
Generated by: David Deharbe, CLEARSY
Generated on: 2019-09-06
Generator: bxml;pog;pog2smt (Atelier B)
Application: B-method
Target solver: CVC4, Z3
|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unknown)
; Prelude
(declare-sort U 0)
(declare-fun |*i| (U U) U)
(declare-fun |+i| (U U) U)
(declare-fun |-i| (U U) U)
(declare-fun idiv (U U) U)
(declare-fun |*r| (U U) U)
(declare-fun |+r| (U U) U)
(declare-fun |-r| (U U) U)
(declare-fun rdiv (U U) U)
(declare-fun modulo (U U) U)
(declare-fun |<i| (U U) Bool)
(declare-fun |<=i| (U U) Bool)
(declare-fun |>i| (U U) Bool)
(declare-fun |>=i| (U U) Bool)
(declare-fun |<r| (U U) Bool)
(declare-fun |<=r| (U U) Bool)
(declare-fun |>r| (U U) Bool)
(declare-fun |>=r| (U U) Bool)
(declare-fun iuminus (U) U)
(declare-fun ruminus (U) U)
(declare-fun TRUE () U)
(declare-fun FALSE () U)
(assert (not (= TRUE FALSE)))
(declare-fun empty () U)
(declare-fun bool (Bool) U)
(declare-fun BOOL () U)
(declare-fun INT () U)
(declare-fun INTEGER () U)
(declare-fun NAT () U)
(declare-fun NAT1 () U)
(declare-fun NATURAL () U)
(declare-fun NATURAL1 () U)
(declare-fun FLOAT () U)
(declare-fun MaxInt () U)
(declare-fun MinInt () U)
(declare-fun |STRING| () U)
(declare-fun REAL () U)
(declare-fun set_prod (U U) U)
(declare-fun set_diff (U U) U)
(declare-fun mapplet (U U) U)
(declare-fun |**i| (U U) U)
(declare-fun |**r| (U U) U)
(declare-fun |+->| (U U) U)
(declare-fun |+->>| (U U) U)
(declare-fun |-->| (U U) U)
(declare-fun |-->>| (U U) U)
(declare-fun |<->| (U U) U)
(declare-fun |>+>| (U U) U)
(declare-fun |>->| (U U) U)
(declare-fun |>+>>| (U U) U)
(declare-fun |>->>| (U U) U)
(declare-fun |->| (U U) U)
(declare-fun interval (U U) U)
(declare-fun composition (U U) U)
(declare-fun binary_inter (U U) U)
(declare-fun restriction_head (U U) U)
(declare-fun semicolon (U U) U)
(declare-fun |<+| (U U) U)
(declare-fun |<-| (U U) U)
(declare-fun domain_subtraction (U U) U)
(declare-fun domain_restriction (U U) U)
(declare-fun |><| (U U) U)
(declare-fun parallel_product (U U) U)
(declare-fun binary_union (U U) U)
(declare-fun restriction_tail (U U) U)
(declare-fun concatenate (U U) U)
(declare-fun range_restriction (U U) U)
(declare-fun range_subtraction (U U) U)
(declare-fun image (U U) U)
(declare-fun apply (U U) U)
(declare-fun prj1 (U U) U)
(declare-fun prj2 (U U) U)
(declare-fun iterate (U U) U)
(declare-fun |const| (U U) U)
(declare-fun rank (U U) U)
(declare-fun father (U U) U)
(declare-fun subtree (U U) U)
(declare-fun arity (U U) U)
(declare-fun |+f| (U U) U)
(declare-fun |-f| (U U) U)
(declare-fun |*f| (U U) U)
(declare-fun |fdiv| (U U) U)
(declare-fun tbin (U U U) U)
(declare-fun son (U U U) U)
(declare-fun mem (U U) Bool)
(declare-fun subset (U U) Bool)
(declare-fun strict_subset (U U) Bool)
(declare-fun |<=f| (U U) Bool)
(declare-fun |<f| (U U) Bool)
(declare-fun |>=f| (U U) Bool)
(declare-fun |>f| (U U) Bool)
(declare-fun imax (U) U)
(declare-fun imin (U) U)
(declare-fun rmax (U) U)
(declare-fun rmin (U) U)
(declare-fun card (U) U)
(declare-fun dom (U) U)
(declare-fun ran (U) U)
(declare-fun POW (U) U)
(declare-fun POW1 (U) U)
(declare-fun FIN (U) U)
(declare-fun FIN1 (U) U)
(declare-fun union (U) U)
(declare-fun inter (U) U)
(declare-fun seq (U) U)
(declare-fun seq1 (U) U)
(declare-fun iseq (U) U)
(declare-fun iseq1 (U) U)
(declare-fun inverse (U) U)
(declare-fun size (U) U)
(declare-fun perm (U) U)
(declare-fun first (U) U)
(declare-fun last (U) U)
(declare-fun id (U) U)
(declare-fun closure (U) U)
(declare-fun closure1 (U) U)
(declare-fun tail (U) U)
(declare-fun front (U) U)
(declare-fun reverse (U) U)
(declare-fun rev (U) U)
(declare-fun conc (U) U)
(declare-fun succ (U) U)
(declare-fun pred (U) U)
(declare-fun rel (U) U)
(declare-fun fnc (U) U)
(declare-fun real (U) U)
(declare-fun floor (U) U)
(declare-fun ceiling (U) U)
(declare-fun tree (U) U)
(declare-fun btree (U) U)
(declare-fun top (U) U)
(declare-fun sons (U) U)
(declare-fun prefix (U) U)
(declare-fun postfix (U) U)
(declare-fun sizet (U) U)
(declare-fun mirror (U) U)
(declare-fun left (U) U)
(declare-fun right (U) U)
(declare-fun infix (U) U)
(declare-fun ubin (U) U)
(declare-fun SEQ (U) U)
(declare-fun SET (U) U)
; Opaque formulas
(declare-fun e0 () U)
(declare-fun e16 () U)
(declare-fun e35 () U)
(declare-fun e34 () U)
(declare-fun e8 () U)
(declare-fun e10 () U)
(declare-fun e12 () U)
(declare-fun e14 () U)
(declare-fun e21 () U)
(declare-fun g_s0_1 () U)
(declare-fun g_s1_2 () U)
(declare-fun g_s10_15 () U)
(declare-fun g_s11_17 () U)
(declare-fun g_s12_18 () U)
(declare-fun g_s13_19 () U)
(declare-fun g_s14_20 () U)
(declare-fun g_s15_22 () U)
(declare-fun g_s16_23 () U)
(declare-fun g_s17_24 () U)
(declare-fun g_s18_25 () U)
(declare-fun g_s19_26 () U)
(declare-fun g_s2_3 () U)
(declare-fun g_s20_27 () U)
(declare-fun g_s21_28 () U)
(declare-fun g_s22_32 () U)
(declare-fun g_s23_33 () U)
(declare-fun g_s27_36 () U)
(declare-fun g_s28_37 () U)
(declare-fun g_s29_38 () U)
(declare-fun g_s3_4 () U)
(declare-fun g_s4_5 () U)
(declare-fun g_s5_6 () U)
(declare-fun g_s6_7 () U)
(declare-fun g_s7_9 () U)
(declare-fun g_s8_11 () U)
(declare-fun g_s9_13 () U)
(declare-fun e29 () U)
(declare-fun e30 () U)
(declare-fun e31 () U)
; Defines
(define-fun |def_B definitions| () Bool (and (= NAT (interval e0 MaxInt)) (= INT (interval MinInt MaxInt))))
(define-fun |def_ctx| () Bool true)
(define-fun |def_seext| () Bool true)
(define-fun |def_lprp| () Bool (and (not (= g_s0_1 empty)) (= g_s1_2 (SET (mapplet g_s6_7 (mapplet g_s5_6 (mapplet g_s4_5 (mapplet g_s3_4 g_s2_3)))))) (= g_s7_9 (interval e0 e8)) (= g_s8_11 (interval e0 e10)) (= g_s9_13 (interval e0 e12)) (= g_s10_15 (interval e0 e14)) (= g_s11_17 (interval e16 e8)) (= g_s12_18 (interval e16 e10)) (= g_s13_19 (interval e16 e12)) (= g_s14_20 (interval e16 e14)) (= g_s15_22 (interval e21 e14)) (= g_s16_23 g_s9_13) (subset g_s17_24 g_s0_1) (mem g_s18_25 g_s0_1) (= g_s17_24 (set_diff g_s0_1 (SET g_s18_25))) (mem g_s19_26 (|-->| (set_prod g_s10_15 g_s10_15) g_s10_15)) (mem g_s20_27 (|-->| (set_prod g_s10_15 g_s10_15) g_s10_15)) (mem g_s21_28 (|-->| (set_prod g_s10_15 g_s14_20) g_s10_15)) (= g_s19_26 e29) (= g_s20_27 e30) (= g_s21_28 e31)))
(define-fun |def_inprp| () Bool true)
(define-fun |def_inext| () Bool true)
(define-fun |def_inv| () Bool true)
(define-fun |def_ass| () Bool true)
(define-fun |def_cst| () Bool true)
(define-fun |def_sets| () Bool (and (not (= g_s0_1 empty)) (= g_s1_2 (SET (mapplet g_s6_7 (mapplet g_s5_6 (mapplet g_s4_5 (mapplet g_s3_4 g_s2_3))))))))
; PO group 0 
(push 1)
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_cst|)
(assert |def_sets|)
(define-fun lh_1 () Bool (= g_s7_9 (interval e0 e8)))
(define-fun lh_2 () Bool (= g_s8_11 (interval e0 e10)))
(define-fun lh_3 () Bool (= g_s9_13 (interval e0 e12)))
(define-fun lh_4 () Bool (= g_s10_15 (interval e0 e14)))
(define-fun lh_5 () Bool (= g_s11_17 (interval e16 e8)))
(define-fun lh_6 () Bool (= g_s12_18 (interval e16 e10)))
(define-fun lh_7 () Bool (= g_s13_19 (interval e16 e12)))
(define-fun lh_8 () Bool (= g_s14_20 (interval e16 e14)))
(define-fun lh_9 () Bool (= g_s15_22 (interval e21 e14)))
(define-fun lh_10 () Bool (= g_s16_23 g_s9_13))
(define-fun lh_11 () Bool (subset g_s17_24 g_s0_1))
(define-fun lh_12 () Bool (mem g_s18_25 g_s0_1))
(define-fun lh_13 () Bool (= g_s17_24 (set_diff g_s0_1 (SET g_s18_25))))
(define-fun lh_14 () Bool (mem g_s19_26 (|-->| (set_prod g_s10_15 g_s10_15) g_s10_15)))
(define-fun lh_15 () Bool (mem g_s20_27 (|-->| (set_prod g_s10_15 g_s10_15) g_s10_15)))
(define-fun lh_16 () Bool (mem g_s21_28 (|-->| (set_prod g_s10_15 g_s14_20) g_s10_15)))
(define-fun lh_17 () Bool (mem g_s22_32 g_s10_15))
(define-fun lh_18 () Bool (mem g_s23_33 g_s10_15))
(define-fun lh_19 () Bool (= g_s19_26 e29))
(define-fun lh_20 () Bool (= g_s20_27 e30))
(define-fun lh_21 () Bool (mem g_s23_33 g_s14_20))
; PO 1 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18) (|<=i| e0 e34))))
(check-sat)
(pop 1)
; PO 2 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18) (|<=i| e0 (|+i| g_s22_32 g_s23_33)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18) (|<=i| e16 (|**i| e35 e34)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19) (mem (bool (|>=i| g_s22_32 g_s23_33)) (dom (SET (mapplet (mapplet FALSE (|+i| (|-i| (|**i| e35 e34) g_s23_33) g_s22_32)) (mapplet TRUE (|-i| g_s22_32 g_s23_33)))))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 5 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19) (mem (SET (mapplet (mapplet FALSE (|+i| (|-i| (|**i| e35 e34) g_s23_33) g_s22_32)) (mapplet TRUE (|-i| g_s22_32 g_s23_33)))) (|+->| (dom (SET (mapplet (mapplet FALSE (|+i| (|-i| (|**i| e35 e34) g_s23_33) g_s22_32)) (mapplet TRUE (|-i| g_s22_32 g_s23_33))))) (ran (SET (mapplet (mapplet FALSE (|+i| (|-i| (|**i| e35 e34) g_s23_33) g_s22_32)) (mapplet TRUE (|-i| g_s22_32 g_s23_33))))))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 6 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19) (|<=i| e0 e34))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 7 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_19 lh_20 lh_21) (not (= g_s23_33 e0)))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 1 
(push 1)
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_cst|)
(assert |def_lprp|)
(assert |def_inprp|)
(assert |def_inext|)
(assert |def_seext|)
(assert |def_inv|)
(assert |def_ass|)
(assert (mem g_s27_36 g_s10_15))
(assert (mem g_s28_37 g_s10_15))
(assert (mem g_s29_38 g_s10_15))
; PO 1 in group 1
(push 1)
(assert (not (mem g_s19_26 (|+->| (dom g_s19_26) (ran g_s19_26)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 1
(push 1)
(assert (not (mem (mapplet g_s27_36 g_s28_37) (dom g_s19_26))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
(exit)