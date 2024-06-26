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
(declare-fun e1 () U)
(declare-fun e0 () U)
(declare-fun e5 () U)
(declare-fun e3 () U)
(declare-fun g_s0_2 () U)
(declare-fun g_s1_4 () U)
(declare-fun g_s10_14 () U)
(declare-fun g_s11_15 () U)
(declare-fun g_s12_16 () U)
(declare-fun g_s13_17 () U)
(declare-fun g_s14_18 () U)
(declare-fun g_s15_19 () U)
(declare-fun g_s16_20 () U)
(declare-fun g_s17_21 () U)
(declare-fun g_s18_22 () U)
(declare-fun g_s19_23 () U)
(declare-fun g_s2_6 () U)
(declare-fun g_s20_24 () U)
(declare-fun g_s21_25 () U)
(declare-fun g_s22_26 () U)
(declare-fun g_s23_27 () U)
(declare-fun g_s24_28 () U)
(declare-fun g_s25_29 () U)
(declare-fun g_s26_30 () U)
(declare-fun g_s27_31 () U)
(declare-fun g_s28_32 () U)
(declare-fun g_s29_33 () U)
(declare-fun g_s3_7 () U)
(declare-fun g_s37_49 () U)
(declare-fun g_s38_50 () U)
(declare-fun g_s39_57 () U)
(declare-fun g_s4_8 () U)
(declare-fun g_s40_58 () U)
(declare-fun g_s41_59 () U)
(declare-fun g_s42_52 () U)
(declare-fun g_s43_54 () U)
(declare-fun g_s43$1_60 () U)
(declare-fun g_s44_55 () U)
(declare-fun g_s44$1_61 () U)
(declare-fun g_s5_9 () U)
(declare-fun g_s52_62 () U)
(declare-fun g_s53_63 () U)
(declare-fun g_s54_64 () U)
(declare-fun g_s6_10 () U)
(declare-fun g_s7_11 () U)
(declare-fun g_s8_12 () U)
(declare-fun g_s9_13 () U)
(declare-fun e40 () U)
(declare-fun e41 () U)
(declare-fun e42 () U)
(declare-fun e34 () U)
(declare-fun e37 () U)
(declare-fun e35 () U)
(declare-fun e38 () U)
(declare-fun e36 () U)
(declare-fun e39 () U)
(declare-fun e43 () U)
(declare-fun e44 () U)
(declare-fun e45 () U)
(declare-fun e46 () U)
(declare-fun e47 () U)
(declare-fun e48 () U)
(declare-fun e56 () U)
(declare-fun e53 () U)
(declare-fun e51 () U)
; Defines
(define-fun |def_B definitions| () Bool (and (= NAT (interval e0 MaxInt)) (= INT (interval MinInt MaxInt))))
(define-fun |def_ctx| () Bool (and (= g_s0_2 (interval e0 e1)) (= g_s1_4 (interval e0 e3)) (= g_s2_6 (interval e0 e5)) (mem g_s3_7 (|-->| (set_prod g_s0_2 g_s2_6) g_s0_2)) (mem g_s4_8 (|-->| (set_prod g_s0_2 g_s2_6) g_s0_2)) (mem g_s5_9 (|-->| g_s0_2 g_s0_2)) (mem g_s6_10 (|-->| (set_prod g_s0_2 g_s0_2) g_s0_2)) (mem g_s7_11 (|-->| (set_prod g_s0_2 g_s0_2) g_s0_2)) (mem g_s8_12 (|-->| (set_prod g_s0_2 g_s0_2) g_s0_2)) (mem g_s9_13 (|-->| (set_prod g_s1_4 g_s2_6) g_s1_4)) (mem g_s10_14 (|-->| (set_prod g_s1_4 g_s2_6) g_s1_4)) (mem g_s11_15 (|-->| g_s1_4 g_s1_4)) (mem g_s12_16 (|-->| (set_prod g_s1_4 g_s1_4) g_s1_4)) (mem g_s13_17 (|-->| (set_prod g_s1_4 g_s1_4) g_s1_4)) (mem g_s14_18 (|-->| (set_prod g_s1_4 g_s1_4) g_s1_4)) (mem g_s15_19 (|-->| (set_prod g_s2_6 g_s2_6) g_s2_6)) (mem g_s16_20 (|-->| (set_prod g_s2_6 g_s2_6) g_s2_6)) (mem g_s17_21 (|-->| g_s2_6 g_s2_6)) (mem g_s18_22 (|-->| (set_prod g_s2_6 g_s2_6) g_s2_6)) (mem g_s19_23 (|-->| (set_prod g_s2_6 g_s2_6) g_s2_6)) (mem g_s20_24 (|-->| (set_prod g_s2_6 g_s2_6) g_s2_6)) (mem g_s21_25 (|-->| (set_prod g_s0_2 g_s0_2) g_s0_2)) (mem g_s22_26 (|-->| (set_prod g_s0_2 g_s0_2) g_s0_2)) (mem g_s23_27 (|-->| (set_prod g_s0_2 g_s0_2) g_s0_2)) (mem g_s24_28 (|-->| (set_prod g_s1_4 g_s1_4) g_s1_4)) (mem g_s25_29 (|-->| (set_prod g_s1_4 g_s1_4) g_s1_4)) (mem g_s26_30 (|-->| (set_prod g_s1_4 g_s1_4) g_s1_4)) (mem g_s27_31 (|-->| (set_prod g_s2_6 g_s2_6) g_s2_6)) (mem g_s28_32 (|-->| (set_prod g_s2_6 g_s2_6) g_s2_6)) (mem g_s29_33 (|-->| (set_prod g_s2_6 g_s2_6) g_s2_6)) (= g_s3_7 e34) (= g_s9_13 e35) (= g_s15_19 e36) (= g_s4_8 e37) (= g_s10_14 e38) (= g_s16_20 e39) (= g_s21_25 e40) (= g_s22_26 e41) (= g_s23_27 e42) (= g_s24_28 e43) (= g_s25_29 e44) (= g_s26_30 e45) (= g_s27_31 e46) (= g_s28_32 e47) (= g_s29_33 e48)))
(define-fun |def_seext| () Bool true)
(define-fun |def_lprp| () Bool (and (mem g_s37_49 (|-->| (set_prod g_s2_6 g_s1_4) g_s1_4)) (mem g_s38_50 (|+->| (set_prod (set_prod (seq g_s2_6) NATURAL) g_s1_4) (set_prod (set_prod (seq g_s2_6) NATURAL) g_s1_4))) (= g_s38_50 e51) (mem g_s42_52 (|+->| (set_prod (set_prod (seq g_s2_6) NATURAL) g_s1_4) (set_prod (set_prod (seq g_s2_6) NATURAL) g_s1_4))) (= g_s42_52 e53)))
(define-fun |def_inprp| () Bool true)
(define-fun |def_inext| () Bool true)
(define-fun |def_inv| () Bool (and (mem g_s43_54 (|-->| (set_prod g_s2_6 g_s0_2) g_s0_2)) (mem g_s44_55 (|+->| (set_prod (set_prod (seq g_s2_6) NATURAL) g_s0_2) (set_prod (set_prod (seq g_s2_6) NATURAL) g_s0_2))) (= g_s44_55 e56)))
(define-fun |def_ass| () Bool true)
(define-fun |def_cst| () Bool true)
(define-fun |def_sets| () Bool true)
; PO group 0 
(push 1)
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_cst|)
(assert |def_sets|)
(define-fun lh_1 () Bool (mem g_s37_49 (|-->| (set_prod g_s2_6 g_s1_4) g_s1_4)))
(define-fun lh_2 () Bool (mem g_s38_50 (|+->| (set_prod (set_prod (seq g_s2_6) NATURAL) g_s1_4) (set_prod (set_prod (seq g_s2_6) NATURAL) g_s1_4))))
(define-fun lh_3 () Bool (mem g_s39_57 (seq g_s2_6)))
(define-fun lh_4 () Bool (mem g_s40_58 NATURAL))
(define-fun lh_5 () Bool (mem g_s40_58 (dom g_s39_57)))
(define-fun lh_6 () Bool (mem g_s41_59 g_s1_4))
(define-fun lh_7 () Bool (= g_s38_50 e51))
(define-fun lh_8 () Bool (mem g_s42_52 (|+->| (set_prod (set_prod (seq g_s2_6) NATURAL) g_s1_4) (set_prod (set_prod (seq g_s2_6) NATURAL) g_s1_4))))
; PO 1 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6) (mem g_s37_49 (|+->| (dom g_s37_49) (ran g_s37_49))))))
(check-sat)
(pop 1)
; PO 2 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6) (mem g_s39_57 (|+->| (dom g_s39_57) (ran g_s39_57))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6) (mem (mapplet (apply g_s39_57 g_s40_58) g_s41_59) (dom g_s37_49)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8) (mem g_s24_28 (|+->| (dom g_s24_28) (ran g_s24_28))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 5 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8) (mem g_s39_57 (|+->| (dom g_s39_57) (ran g_s39_57))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 6 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8) (mem (mapplet (apply g_s39_57 g_s40_58) g_s41_59) (dom g_s24_28)))))
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
(define-fun lh_1 () Bool (mem g_s43_54 (|-->| (set_prod g_s2_6 g_s0_2) g_s0_2)))
(define-fun lh_2 () Bool (mem g_s44_55 (|+->| (set_prod (set_prod (seq g_s2_6) NATURAL) g_s0_2) (set_prod (set_prod (seq g_s2_6) NATURAL) g_s0_2))))
(define-fun lh_3 () Bool (mem g_s39_57 (seq g_s2_6)))
(define-fun lh_4 () Bool (mem g_s40_58 NATURAL))
(define-fun lh_5 () Bool (mem g_s40_58 (dom g_s39_57)))
(define-fun lh_6 () Bool (mem g_s41_59 g_s0_2))
; PO 1 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6) (mem g_s43_54 (|+->| (dom g_s43_54) (ran g_s43_54))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6) (mem g_s39_57 (|+->| (dom g_s39_57) (ran g_s39_57))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6) (mem (mapplet (apply g_s39_57 g_s40_58) g_s41_59) (dom g_s43_54)))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 2 
(push 1)
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_cst|)
(assert |def_lprp|)
(assert |def_inprp|)
(assert |def_inext|)
(assert |def_seext|)
(define-fun lh_1 () Bool (mem g_s43$1_60 (|-->| (set_prod g_s2_6 g_s0_2) g_s0_2)))
(define-fun lh_2 () Bool (mem g_s44$1_61 (|+->| (set_prod (set_prod (seq g_s2_6) NATURAL) g_s0_2) (set_prod (set_prod (seq g_s2_6) NATURAL) g_s0_2))))
(define-fun lh_3 () Bool (mem g_s39_57 (seq g_s2_6)))
(define-fun lh_4 () Bool (mem g_s40_58 NATURAL))
(define-fun lh_5 () Bool (mem g_s40_58 (dom g_s39_57)))
(define-fun lh_6 () Bool (mem g_s41_59 g_s0_2))
; PO 1 in group 2
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6) (mem g_s43$1_60 (|+->| (dom g_s43$1_60) (ran g_s43$1_60))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 2
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6) (mem g_s39_57 (|+->| (dom g_s39_57) (ran g_s39_57))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 2
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6) (mem (mapplet (apply g_s39_57 g_s40_58) g_s41_59) (dom g_s43$1_60)))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 3 
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
(assert (mem g_s52_62 g_s2_6))
(assert (mem g_s53_63 g_s1_4))
(assert (mem g_s54_64 g_s1_4))
; PO 1 in group 3
(push 1)
(assert (not (mem g_s37_49 (|+->| (dom g_s37_49) (ran g_s37_49)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 3
(push 1)
(assert (not (mem (mapplet g_s52_62 g_s53_63) (dom g_s37_49))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 4 
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
(assert (mem g_s52_62 g_s2_6))
(assert (mem g_s53_63 g_s0_2))
(assert (mem g_s54_64 g_s0_2))
; PO 1 in group 4
(push 1)
(assert (not (mem g_s43_54 (|+->| (dom g_s43_54) (ran g_s43_54)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 4
(push 1)
(assert (not (mem (mapplet g_s52_62 g_s53_63) (dom g_s43_54))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
(exit)