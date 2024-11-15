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
(declare-fun e12 () U)
(declare-fun e0 () U)
(declare-fun e64 () U)
(declare-fun e16 () U)
(declare-fun e14 () U)
(declare-fun e13 () U)
(declare-fun g_s0_1 () U)
(declare-fun g_s1_2 () U)
(declare-fun g_s10_11 () U)
(declare-fun g_s11_15 () U)
(declare-fun g_s12_17 () U)
(declare-fun g_s13_18 () U)
(declare-fun g_s14_19 () U)
(declare-fun g_s15_20 () U)
(declare-fun g_s16_21 () U)
(declare-fun g_s17_22 () U)
(declare-fun g_s18_23 () U)
(declare-fun g_s19_24 () U)
(declare-fun g_s2_3 () U)
(declare-fun g_s20_25 () U)
(declare-fun g_s21_26 () U)
(declare-fun g_s22_27 () U)
(declare-fun g_s23_28 () U)
(declare-fun g_s24_29 () U)
(declare-fun g_s25_30 () U)
(declare-fun g_s26_31 () U)
(declare-fun g_s27_32 () U)
(declare-fun g_s28_33 () U)
(declare-fun g_s29_34 () U)
(declare-fun g_s3_5 () U)
(declare-fun g_s30_35 () U)
(declare-fun g_s31_36 () U)
(declare-fun g_s32_37 () U)
(declare-fun g_s33_38 () U)
(declare-fun g_s34_39 () U)
(declare-fun g_s35_40 () U)
(declare-fun g_s36_41 () U)
(declare-fun g_s37_42 () U)
(declare-fun g_s38_43 () U)
(declare-fun g_s39_44 () U)
(declare-fun g_s4_4 () U)
(declare-fun g_s40_60 () U)
(declare-fun g_s41_61 () U)
(declare-fun g_s42_62 () U)
(declare-fun g_s43_63 () U)
(declare-fun g_s5_7 () U)
(declare-fun g_s6_6 () U)
(declare-fun g_s7_9 () U)
(declare-fun g_s8_8 () U)
(declare-fun g_s9_10 () U)
(declare-fun e51 () U)
(declare-fun e52 () U)
(declare-fun e53 () U)
(declare-fun e45 () U)
(declare-fun e48 () U)
(declare-fun e46 () U)
(declare-fun e49 () U)
(declare-fun e47 () U)
(declare-fun e50 () U)
(declare-fun e54 () U)
(declare-fun e55 () U)
(declare-fun e56 () U)
(declare-fun e57 () U)
(declare-fun e58 () U)
(declare-fun e59 () U)
; Defines
(define-fun |def_B definitions| () Bool (and (= NAT (interval e0 MaxInt)) (= INT (interval MinInt MaxInt))))
(define-fun |def_ctx| () Bool (and (= g_s0_1 (SET (mapplet g_s2_3 g_s1_2))) (mem g_s3_5 g_s4_4) (mem g_s5_7 g_s6_6) (mem g_s7_9 g_s8_8) (mem g_s9_10 g_s8_8) (mem g_s10_11 g_s8_8) (= g_s3_5 e12) (= g_s5_7 e13) (= g_s7_9 e14) (and (|>=i| g_s9_10 e0) (|<=i| g_s9_10 g_s7_9)) (and (|>=i| g_s10_11 e0) (|<=i| g_s10_11 g_s7_9)) (not (= g_s9_10 g_s10_11)) (= g_s11_15 (SET (mapplet g_s10_11 g_s9_10))) (|<=i| g_s9_10 e16) (|<=i| g_s10_11 e16) (= g_s12_17 (SET (mapplet (mapplet FALSE g_s10_11) (mapplet TRUE g_s9_10)))) (= g_s4_4 (interval e0 e12)) (= g_s6_6 (interval e0 e13)) (= g_s8_8 (interval e0 e14))))
(define-fun |def_seext| () Bool (and (mem g_s12_17 (|+->| BOOL g_s8_8)) (mem g_s12_17 (|+->| BOOL g_s6_6)) (mem g_s12_17 (|+->| BOOL g_s4_4))))
(define-fun |def_lprp| () Bool (and (mem g_s13_18 (|-->| (set_prod g_s4_4 g_s8_8) g_s4_4)) (mem g_s14_19 (|-->| (set_prod g_s4_4 g_s8_8) g_s4_4)) (mem g_s15_20 (|-->| g_s4_4 g_s4_4)) (mem g_s16_21 (|-->| (set_prod g_s4_4 g_s4_4) g_s4_4)) (mem g_s17_22 (|-->| (set_prod g_s4_4 g_s4_4) g_s4_4)) (mem g_s18_23 (|-->| (set_prod g_s4_4 g_s4_4) g_s4_4)) (mem g_s19_24 (|-->| (set_prod g_s6_6 g_s8_8) g_s6_6)) (mem g_s20_25 (|-->| (set_prod g_s6_6 g_s8_8) g_s6_6)) (mem g_s21_26 (|-->| g_s6_6 g_s6_6)) (mem g_s22_27 (|-->| (set_prod g_s6_6 g_s6_6) g_s6_6)) (mem g_s23_28 (|-->| (set_prod g_s6_6 g_s6_6) g_s6_6)) (mem g_s24_29 (|-->| (set_prod g_s6_6 g_s6_6) g_s6_6)) (mem g_s25_30 (|-->| (set_prod g_s8_8 g_s8_8) g_s8_8)) (mem g_s26_31 (|-->| (set_prod g_s8_8 g_s8_8) g_s8_8)) (mem g_s27_32 (|-->| g_s8_8 g_s8_8)) (mem g_s28_33 (|-->| (set_prod g_s8_8 g_s8_8) g_s8_8)) (mem g_s29_34 (|-->| (set_prod g_s8_8 g_s8_8) g_s8_8)) (mem g_s30_35 (|-->| (set_prod g_s8_8 g_s8_8) g_s8_8)) (mem g_s31_36 (|-->| (set_prod g_s4_4 g_s4_4) g_s4_4)) (mem g_s32_37 (|-->| (set_prod g_s4_4 g_s4_4) g_s4_4)) (mem g_s33_38 (|-->| (set_prod g_s4_4 g_s4_4) g_s4_4)) (mem g_s34_39 (|-->| (set_prod g_s6_6 g_s6_6) g_s6_6)) (mem g_s35_40 (|-->| (set_prod g_s6_6 g_s6_6) g_s6_6)) (mem g_s36_41 (|-->| (set_prod g_s6_6 g_s6_6) g_s6_6)) (mem g_s37_42 (|-->| (set_prod g_s8_8 g_s8_8) g_s8_8)) (mem g_s38_43 (|-->| (set_prod g_s8_8 g_s8_8) g_s8_8)) (mem g_s39_44 (|-->| (set_prod g_s8_8 g_s8_8) g_s8_8)) (= g_s13_18 e45) (= g_s19_24 e46) (= g_s25_30 e47) (= g_s14_19 e48) (= g_s20_25 e49) (= g_s26_31 e50) (= g_s31_36 e51) (= g_s32_37 e52) (= g_s33_38 e53) (= g_s34_39 e54) (= g_s35_40 e55) (= g_s36_41 e56) (= g_s37_42 e57) (= g_s38_43 e58) (= g_s39_44 e59)))
(define-fun |def_inprp| () Bool true)
(define-fun |def_inext| () Bool true)
(define-fun |def_inv| () Bool true)
(define-fun |def_ass| () Bool true)
(define-fun |def_cst| () Bool true)
(define-fun |def_sets| () Bool true)
; PO group 0 
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_cst|)
(assert |def_sets|)
(define-fun lh_1 () Bool (mem g_s13_18 (|-->| (set_prod g_s4_4 g_s8_8) g_s4_4)))
(define-fun lh_2 () Bool (mem g_s14_19 (|-->| (set_prod g_s4_4 g_s8_8) g_s4_4)))
(define-fun lh_3 () Bool (mem g_s15_20 (|-->| g_s4_4 g_s4_4)))
(define-fun lh_4 () Bool (mem g_s16_21 (|-->| (set_prod g_s4_4 g_s4_4) g_s4_4)))
(define-fun lh_5 () Bool (mem g_s17_22 (|-->| (set_prod g_s4_4 g_s4_4) g_s4_4)))
(define-fun lh_6 () Bool (mem g_s18_23 (|-->| (set_prod g_s4_4 g_s4_4) g_s4_4)))
(define-fun lh_7 () Bool (mem g_s19_24 (|-->| (set_prod g_s6_6 g_s8_8) g_s6_6)))
(define-fun lh_8 () Bool (mem g_s20_25 (|-->| (set_prod g_s6_6 g_s8_8) g_s6_6)))
(define-fun lh_9 () Bool (mem g_s21_26 (|-->| g_s6_6 g_s6_6)))
(define-fun lh_10 () Bool (mem g_s22_27 (|-->| (set_prod g_s6_6 g_s6_6) g_s6_6)))
(define-fun lh_11 () Bool (mem g_s23_28 (|-->| (set_prod g_s6_6 g_s6_6) g_s6_6)))
(define-fun lh_12 () Bool (mem g_s24_29 (|-->| (set_prod g_s6_6 g_s6_6) g_s6_6)))
(define-fun lh_13 () Bool (mem g_s25_30 (|-->| (set_prod g_s8_8 g_s8_8) g_s8_8)))
(define-fun lh_14 () Bool (mem g_s26_31 (|-->| (set_prod g_s8_8 g_s8_8) g_s8_8)))
(define-fun lh_15 () Bool (mem g_s27_32 (|-->| g_s8_8 g_s8_8)))
(define-fun lh_16 () Bool (mem g_s28_33 (|-->| (set_prod g_s8_8 g_s8_8) g_s8_8)))
(define-fun lh_17 () Bool (mem g_s29_34 (|-->| (set_prod g_s8_8 g_s8_8) g_s8_8)))
(define-fun lh_18 () Bool (mem g_s30_35 (|-->| (set_prod g_s8_8 g_s8_8) g_s8_8)))
(define-fun lh_19 () Bool (mem g_s31_36 (|-->| (set_prod g_s4_4 g_s4_4) g_s4_4)))
(define-fun lh_20 () Bool (mem g_s32_37 (|-->| (set_prod g_s4_4 g_s4_4) g_s4_4)))
(define-fun lh_21 () Bool (mem g_s33_38 (|-->| (set_prod g_s4_4 g_s4_4) g_s4_4)))
(define-fun lh_22 () Bool (mem g_s34_39 (|-->| (set_prod g_s6_6 g_s6_6) g_s6_6)))
(define-fun lh_23 () Bool (mem g_s35_40 (|-->| (set_prod g_s6_6 g_s6_6) g_s6_6)))
(define-fun lh_24 () Bool (mem g_s36_41 (|-->| (set_prod g_s6_6 g_s6_6) g_s6_6)))
(define-fun lh_25 () Bool (mem g_s37_42 (|-->| (set_prod g_s8_8 g_s8_8) g_s8_8)))
(define-fun lh_26 () Bool (mem g_s38_43 (|-->| (set_prod g_s8_8 g_s8_8) g_s8_8)))
(define-fun lh_27 () Bool (mem g_s39_44 (|-->| (set_prod g_s8_8 g_s8_8) g_s8_8)))
(define-fun lh_28 () Bool (mem g_s40_60 g_s4_4))
(define-fun lh_29 () Bool (mem g_s41_61 g_s8_8))
(define-fun lh_30 () Bool (= g_s13_18 e45))
(define-fun lh_31 () Bool (mem g_s40_60 g_s6_6))
(define-fun lh_32 () Bool (= g_s19_24 e46))
(define-fun lh_33 () Bool (mem g_s40_60 g_s8_8))
(define-fun lh_34 () Bool (= g_s25_30 e47))
(define-fun lh_35 () Bool (= g_s14_19 e48))
(define-fun lh_36 () Bool (= g_s20_25 e49))
(define-fun lh_37 () Bool (= g_s26_31 e50))
(define-fun lh_38 () Bool (mem g_s41_61 g_s4_4))
(define-fun lh_39 () Bool (= g_s31_36 e51))
(define-fun lh_40 () Bool (= g_s32_37 e52))
(define-fun lh_41 () Bool (= g_s33_38 e53))
(define-fun lh_42 () Bool (mem g_s42_62 g_s6_6))
(define-fun lh_43 () Bool (mem g_s43_63 g_s6_6))
(define-fun lh_44 () Bool (= g_s34_39 e54))
(define-fun lh_45 () Bool (= g_s35_40 e55))
(define-fun lh_46 () Bool (= g_s36_41 e56))
(define-fun lh_47 () Bool (mem g_s42_62 g_s8_8))
(define-fun lh_48 () Bool (mem g_s43_63 g_s8_8))
(define-fun lh_49 () Bool (= g_s37_42 e57))
(define-fun lh_50 () Bool (= g_s38_43 e58))
; PO 1 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_28 lh_29) (|<=i| e0 g_s41_61))))
(check-sat)
(pop 1)
; PO 2 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_28 lh_29) (|<=i| e0 (|*i| g_s40_60 (|**i| e16 g_s41_61))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_28 lh_29) (|<=i| e64 (|+i| g_s3_5 e64)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_29 lh_30 lh_31) (|<=i| e0 g_s41_61))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 5 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_29 lh_30 lh_31) (|<=i| e0 (|*i| g_s40_60 (|**i| e16 g_s41_61))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 6 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_29 lh_30 lh_31) (|<=i| e64 (|+i| g_s5_7 e64)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 7 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_29 lh_30 lh_32 lh_33) (|<=i| e0 g_s41_61))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 8 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_29 lh_30 lh_32 lh_33) (|<=i| e0 (|*i| g_s40_60 (|**i| e16 g_s41_61))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 9 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_29 lh_30 lh_32 lh_33) (|<=i| e64 (|+i| g_s7_9 e64)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 10 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_28 lh_29 lh_30 lh_32 lh_34) (not (= (|**i| e16 g_s41_61) e0)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 11 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_28 lh_29 lh_30 lh_32 lh_34) (|<=i| e0 g_s41_61))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 12 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_29 lh_30 lh_31 lh_32 lh_34 lh_35) (not (= (|**i| e16 g_s41_61) e0)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 13 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_29 lh_30 lh_31 lh_32 lh_34 lh_35) (|<=i| e0 g_s41_61))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 14 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_29 lh_30 lh_32 lh_33 lh_34 lh_35 lh_36) (not (= (|**i| e16 g_s41_61) e0)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 15 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_29 lh_30 lh_32 lh_33 lh_34 lh_35 lh_36) (|<=i| e0 g_s41_61))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 16 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_28 lh_30 lh_32 lh_34 lh_35 lh_36 lh_37 lh_38) (|<=i| e0 (|+i| g_s40_60 g_s41_61)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 17 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_28 lh_30 lh_32 lh_34 lh_35 lh_36 lh_37 lh_38) (|<=i| e64 (|+i| g_s3_5 e64)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 18 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_28 lh_30 lh_32 lh_34 lh_35 lh_36 lh_37 lh_38 lh_39) (|<=i| e0 (|+i| (|+i| (|-i| g_s40_60 g_s41_61) g_s3_5) e64)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 19 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_28 lh_30 lh_32 lh_34 lh_35 lh_36 lh_37 lh_38 lh_39) (|<=i| e64 (|+i| g_s3_5 e64)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 20 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_28 lh_30 lh_32 lh_34 lh_35 lh_36 lh_37 lh_38 lh_39 lh_40) (|<=i| e0 (|*i| g_s40_60 g_s41_61)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 21 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_28 lh_30 lh_32 lh_34 lh_35 lh_36 lh_37 lh_38 lh_39 lh_40) (|<=i| e64 (|+i| g_s3_5 e64)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 22 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_30 lh_32 lh_34 lh_35 lh_36 lh_37 lh_39 lh_40 lh_41 lh_42 lh_43) (|<=i| e0 (|+i| g_s42_62 g_s43_63)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 23 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_30 lh_32 lh_34 lh_35 lh_36 lh_37 lh_39 lh_40 lh_41 lh_42 lh_43) (|<=i| e64 (|+i| g_s5_7 e64)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 24 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_30 lh_32 lh_34 lh_35 lh_36 lh_37 lh_39 lh_40 lh_41 lh_42 lh_43 lh_44) (|<=i| e0 (|+i| (|+i| (|-i| g_s42_62 g_s43_63) g_s5_7) e64)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 25 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_30 lh_32 lh_34 lh_35 lh_36 lh_37 lh_39 lh_40 lh_41 lh_42 lh_43 lh_44) (|<=i| e64 (|+i| g_s5_7 e64)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 26 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_30 lh_32 lh_34 lh_35 lh_36 lh_37 lh_39 lh_40 lh_41 lh_42 lh_43 lh_44 lh_45) (|<=i| e0 (|*i| g_s42_62 g_s43_63)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 27 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_30 lh_32 lh_34 lh_35 lh_36 lh_37 lh_39 lh_40 lh_41 lh_42 lh_43 lh_44 lh_45) (|<=i| e64 (|+i| g_s5_7 e64)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 28 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_30 lh_32 lh_34 lh_35 lh_36 lh_37 lh_39 lh_40 lh_41 lh_44 lh_45 lh_46 lh_47 lh_48) (|<=i| e0 (|+i| g_s42_62 g_s43_63)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 29 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_30 lh_32 lh_34 lh_35 lh_36 lh_37 lh_39 lh_40 lh_41 lh_44 lh_45 lh_46 lh_47 lh_48) (|<=i| e64 (|+i| g_s7_9 e64)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 30 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_30 lh_32 lh_34 lh_35 lh_36 lh_37 lh_39 lh_40 lh_41 lh_44 lh_45 lh_46 lh_47 lh_48 lh_49) (|<=i| e0 (|+i| (|+i| (|-i| g_s42_62 g_s43_63) g_s7_9) e64)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 31 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_30 lh_32 lh_34 lh_35 lh_36 lh_37 lh_39 lh_40 lh_41 lh_44 lh_45 lh_46 lh_47 lh_48 lh_49) (|<=i| e64 (|+i| g_s7_9 e64)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 32 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_30 lh_32 lh_34 lh_35 lh_36 lh_37 lh_39 lh_40 lh_41 lh_44 lh_45 lh_46 lh_47 lh_48 lh_49 lh_50) (|<=i| e0 (|*i| g_s42_62 g_s43_63)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 33 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_30 lh_32 lh_34 lh_35 lh_36 lh_37 lh_39 lh_40 lh_41 lh_44 lh_45 lh_46 lh_47 lh_48 lh_49 lh_50) (|<=i| e64 (|+i| g_s7_9 e64)))))
(set-info :status unknown)
(check-sat)
(pop 1)
(exit)