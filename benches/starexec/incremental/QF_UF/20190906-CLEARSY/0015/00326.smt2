(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(set-info :source |
Generated by: David Deharbe, CLEARSY
Generated on: 2019-09-09
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
(declare-fun e15 () U)
(declare-fun g_s0_1 () U)
(declare-fun g_s1_2 () U)
(declare-fun g_s10_11 () U)
(declare-fun g_s13_14 () U)
(declare-fun g_s14_16 () U)
(declare-fun g_s15_17 () U)
(declare-fun g_s16_18 () U)
(declare-fun g_s17_19 () U)
(declare-fun g_s18_20 () U)
(declare-fun g_s19_21 () U)
(declare-fun g_s2_3 () U)
(declare-fun g_s20_22 () U)
(declare-fun g_s21_23 () U)
(declare-fun g_s22_24 () U)
(declare-fun g_s23_25 () U)
(declare-fun g_s24_26 () U)
(declare-fun g_s25_27 () U)
(declare-fun g_s26_28 () U)
(declare-fun g_s27_29 () U)
(declare-fun g_s28_30 () U)
(declare-fun g_s29_31 () U)
(declare-fun g_s3_4 () U)
(declare-fun g_s30_32 () U)
(declare-fun g_s31_33 () U)
(declare-fun g_s32_34 () U)
(declare-fun g_s33_35 () U)
(declare-fun g_s34_36 () U)
(declare-fun g_s35_37 () U)
(declare-fun g_s36_38 () U)
(declare-fun g_s37_39 () U)
(declare-fun g_s38_40 () U)
(declare-fun g_s39_41 () U)
(declare-fun g_s4_5 () U)
(declare-fun g_s40_42 () U)
(declare-fun g_s41_43 () U)
(declare-fun g_s42_44 () U)
(declare-fun g_s43_45 () U)
(declare-fun g_s44_46 () U)
(declare-fun g_s45_47 () U)
(declare-fun g_s46_48 () U)
(declare-fun g_s47_49 () U)
(declare-fun g_s48_50 () U)
(declare-fun g_s49_51 () U)
(declare-fun g_s5_6 () U)
(declare-fun g_s50_52 () U)
(declare-fun g_s51_53 () U)
(declare-fun g_s52_54 () U)
(declare-fun g_s58_55 () U)
(declare-fun g_s58_56 () U)
(declare-fun g_s58_57 () U)
(declare-fun g_s6_7 () U)
(declare-fun g_s7_8 () U)
(declare-fun g_s76_58 () U)
(declare-fun g_s77$1_59 () U)
(declare-fun g_s8_9 () U)
(declare-fun g_s9_10 () U)
(declare-fun e13 () U)
(declare-fun e12 () U)
; Defines
(define-fun |def_B definitions| () Bool (and (= NAT (interval e0 MaxInt)) (= INT (interval MinInt MaxInt))))
(define-fun |def_ctx| () Bool (and (not (= g_s0_1 empty)) (not (= g_s1_2 empty)) (not (= g_s2_3 empty)) (not (= g_s3_4 empty)) (not (= g_s4_5 empty)) (not (= g_s5_6 empty)) (not (= g_s6_7 empty)) (not (= g_s7_8 empty)) (not (= g_s8_9 empty)) (not (= g_s9_10 empty)) (mem g_s10_11 (|-->| (set_prod INTEGER NATURAL) INTEGER)) (= g_s10_11 (binary_union e13 e12)) (mem g_s13_14 (|-->| BOOL NAT)) (= g_s13_14 (SET (mapplet (mapplet FALSE e0) (mapplet TRUE e15))))))
(define-fun |def_seext| () Bool  (mem g_s14_16 g_s8_9))
(define-fun |def_lprp| () Bool (and (not (= g_s15_17 empty)) (not (= g_s16_18 empty)) (not (= g_s17_19 empty)) (not (= g_s18_20 empty)) (not (= g_s19_21 empty)) (not (= g_s20_22 empty)) (not (= g_s21_23 empty)) (not (= g_s22_24 empty)) (not (= g_s23_25 empty)) (not (= g_s24_26 empty)) (subset g_s25_27 g_s15_17) (mem g_s26_28 g_s15_17) (not (mem g_s26_28 g_s25_27)) (mem g_s27_29 (|+->| NAT g_s15_17)) (mem g_s27_29 (perm g_s25_27)) (subset g_s28_30 g_s16_18) (mem g_s29_31 g_s16_18) (not (mem g_s29_31 g_s28_30)) (mem g_s30_32 (|+->| NAT g_s16_18)) (mem g_s30_32 (perm g_s28_30)) (subset g_s31_33 g_s17_19) (mem g_s32_34 g_s17_19) (not (mem g_s32_34 g_s31_33)) (mem g_s33_35 (|+->| NAT g_s17_19)) (mem g_s33_35 (perm g_s31_33)) (subset g_s34_36 g_s18_20) (mem g_s35_37 g_s18_20) (not (mem g_s35_37 g_s34_36)) (mem g_s36_38 (|+->| NAT g_s18_20)) (mem g_s36_38 (perm g_s34_36)) (subset g_s37_39 g_s19_21) (mem g_s38_40 g_s19_21) (not (mem g_s38_40 g_s37_39)) (mem g_s39_41 (|+->| NAT g_s19_21)) (mem g_s39_41 (perm g_s37_39)) (subset g_s40_42 g_s20_22) (mem g_s41_43 g_s20_22) (not (mem g_s41_43 g_s40_42)) (mem g_s42_44 (|+->| NAT g_s20_22)) (mem g_s42_44 (perm g_s40_42)) (subset g_s43_45 g_s21_23) (mem g_s44_46 g_s21_23) (not (mem g_s44_46 g_s43_45)) (mem g_s45_47 (|+->| NAT g_s21_23)) (mem g_s45_47 (perm g_s43_45)) (subset g_s46_48 g_s22_24) (mem g_s47_49 g_s22_24) (not (mem g_s47_49 g_s46_48)) (mem g_s48_50 (|+->| NAT g_s22_24)) (mem g_s48_50 (perm g_s46_48)) (mem g_s49_51 g_s23_25) (mem g_s50_52 (|-->| g_s23_25 g_s16_18)) (= (apply g_s50_52 g_s49_51) g_s29_31) (subset g_s51_53 g_s24_26) (mem g_s52_54 g_s24_26) (not (mem g_s52_54 g_s51_53))))
(define-fun |def_inprp| () Bool true)
(define-fun |def_inext| () Bool true)
(define-fun |def_inv| () Bool true)
(define-fun |def_ass| () Bool true)
(define-fun |def_cst| () Bool true)
(define-fun |def_sets| () Bool (and (not (= g_s15_17 empty)) (not (= g_s16_18 empty)) (not (= g_s17_19 empty)) (not (= g_s18_20 empty)) (not (= g_s19_21 empty)) (not (= g_s20_22 empty)) (not (= g_s21_23 empty)) (not (= g_s22_24 empty)) (not (= g_s23_25 empty)) (not (= g_s24_26 empty))))
; PO group 0 
(push 1)
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_cst|)
(assert |def_sets|)
(define-fun lh_1 () Bool (subset g_s25_27 g_s15_17))
(define-fun lh_2 () Bool (mem g_s26_28 g_s15_17))
(define-fun lh_3 () Bool (not (mem g_s26_28 g_s25_27)))
(define-fun lh_4 () Bool (mem g_s27_29 (|+->| NAT g_s15_17)))
(define-fun lh_5 () Bool (mem g_s27_29 (perm g_s25_27)))
(define-fun lh_6 () Bool (subset g_s28_30 g_s16_18))
(define-fun lh_7 () Bool (mem g_s29_31 g_s16_18))
(define-fun lh_8 () Bool (not (mem g_s29_31 g_s28_30)))
(define-fun lh_9 () Bool (mem g_s30_32 (|+->| NAT g_s16_18)))
(define-fun lh_10 () Bool (mem g_s30_32 (perm g_s28_30)))
(define-fun lh_11 () Bool (subset g_s31_33 g_s17_19))
(define-fun lh_12 () Bool (mem g_s32_34 g_s17_19))
(define-fun lh_13 () Bool (not (mem g_s32_34 g_s31_33)))
(define-fun lh_14 () Bool (mem g_s33_35 (|+->| NAT g_s17_19)))
(define-fun lh_15 () Bool (mem g_s33_35 (perm g_s31_33)))
(define-fun lh_16 () Bool (subset g_s34_36 g_s18_20))
(define-fun lh_17 () Bool (mem g_s35_37 g_s18_20))
(define-fun lh_18 () Bool (not (mem g_s35_37 g_s34_36)))
(define-fun lh_19 () Bool (mem g_s36_38 (|+->| NAT g_s18_20)))
(define-fun lh_20 () Bool (mem g_s36_38 (perm g_s34_36)))
(define-fun lh_21 () Bool (subset g_s37_39 g_s19_21))
(define-fun lh_22 () Bool (mem g_s38_40 g_s19_21))
(define-fun lh_23 () Bool (not (mem g_s38_40 g_s37_39)))
(define-fun lh_24 () Bool (mem g_s39_41 (|+->| NAT g_s19_21)))
(define-fun lh_25 () Bool (mem g_s39_41 (perm g_s37_39)))
(define-fun lh_26 () Bool (subset g_s40_42 g_s20_22))
(define-fun lh_27 () Bool (mem g_s41_43 g_s20_22))
(define-fun lh_28 () Bool (not (mem g_s41_43 g_s40_42)))
(define-fun lh_29 () Bool (mem g_s42_44 (|+->| NAT g_s20_22)))
(define-fun lh_30 () Bool (mem g_s42_44 (perm g_s40_42)))
(define-fun lh_31 () Bool (subset g_s43_45 g_s21_23))
(define-fun lh_32 () Bool (mem g_s44_46 g_s21_23))
(define-fun lh_33 () Bool (not (mem g_s44_46 g_s43_45)))
(define-fun lh_34 () Bool (mem g_s45_47 (|+->| NAT g_s21_23)))
(define-fun lh_35 () Bool (mem g_s45_47 (perm g_s43_45)))
(define-fun lh_36 () Bool (subset g_s46_48 g_s22_24))
(define-fun lh_37 () Bool (mem g_s47_49 g_s22_24))
(define-fun lh_38 () Bool (not (mem g_s47_49 g_s46_48)))
(define-fun lh_39 () Bool (mem g_s48_50 (|+->| NAT g_s22_24)))
(define-fun lh_40 () Bool (mem g_s48_50 (perm g_s46_48)))
(define-fun lh_41 () Bool (mem g_s49_51 g_s23_25))
(define-fun lh_42 () Bool (mem g_s50_52 (|-->| g_s23_25 g_s16_18)))
; PO 1 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem g_s25_27 (FIN g_s25_27)))))
(check-sat)
(pop 1)
; PO 2 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9) (mem g_s28_30 (FIN g_s28_30)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14) (mem g_s31_33 (FIN g_s31_33)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19) (mem g_s34_36 (FIN g_s34_36)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 5 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24) (mem g_s37_39 (FIN g_s37_39)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 6 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_28 lh_29) (mem g_s40_42 (FIN g_s40_42)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 7 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_28 lh_29 lh_30 lh_31 lh_32 lh_33 lh_34) (mem g_s43_45 (FIN g_s43_45)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 8 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_28 lh_29 lh_30 lh_31 lh_32 lh_33 lh_34 lh_35 lh_36 lh_37 lh_38 lh_39) (mem g_s46_48 (FIN g_s46_48)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 9 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_28 lh_29 lh_30 lh_31 lh_32 lh_33 lh_34 lh_35 lh_36 lh_37 lh_38 lh_39 lh_40 lh_41 lh_42) (mem g_s49_51 (dom g_s50_52)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 10 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24 lh_25 lh_26 lh_27 lh_28 lh_29 lh_30 lh_31 lh_32 lh_33 lh_34 lh_35 lh_36 lh_37 lh_38 lh_39 lh_40 lh_41 lh_42) (mem g_s50_52 (|+->| (dom g_s50_52) (ran g_s50_52))))))
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
(define-fun lh_1 () Bool (mem (card g_s25_27) INT))
; PO 1 in group 1
(push 1)
(assert (not (mem g_s25_27 (FIN g_s25_27))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 1
(push 1)
(assert (not (=> lh_1 (mem g_s25_27 (FIN g_s25_27)))))
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
(assert |def_inv|)
(assert |def_ass|)
(assert (mem g_s58_55 NATURAL))
(assert (mem g_s58_55 (dom g_s27_29)))
; PO 1 in group 2
(assert (not (mem g_s27_29 (|+->| (dom g_s27_29) (ran g_s27_29)))))
(set-info :status unknown)
(check-sat)
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
(assert (mem g_s58_56 g_s15_17))
(assert (mem g_s58_56 (ran g_s27_29)))
; PO 1 in group 3
(push 1)
(assert (not (mem g_s58_56 (dom (inverse g_s27_29)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 3
(push 1)
(assert (not (mem (inverse g_s27_29) (|+->| (dom (inverse g_s27_29)) (ran (inverse g_s27_29))))))
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
(define-fun lh_1 () Bool (mem (card g_s28_30) INT))
; PO 1 in group 4
(push 1)
(assert (not (mem g_s28_30 (FIN g_s28_30))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 4
(push 1)
(assert (not (=> lh_1 (mem g_s28_30 (FIN g_s28_30)))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 5 
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
(assert (mem g_s58_55 NATURAL))
(assert (mem g_s58_55 (dom g_s30_32)))
; PO 1 in group 5
(assert (not (mem g_s30_32 (|+->| (dom g_s30_32) (ran g_s30_32)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO group 6 
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
(assert (mem g_s58_57 g_s16_18))
(assert (mem g_s58_57 (ran g_s30_32)))
; PO 1 in group 6
(push 1)
(assert (not (mem g_s58_57 (dom (inverse g_s30_32)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 6
(push 1)
(assert (not (mem (inverse g_s30_32) (|+->| (dom (inverse g_s30_32)) (ran (inverse g_s30_32))))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 7 
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
(define-fun lh_1 () Bool (mem (card g_s31_33) INT))
; PO 1 in group 7
(push 1)
(assert (not (mem g_s31_33 (FIN g_s31_33))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 7
(push 1)
(assert (not (=> lh_1 (mem g_s31_33 (FIN g_s31_33)))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 8 
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
(assert (mem g_s58_55 NATURAL))
(assert (mem g_s58_55 (dom g_s33_35)))
; PO 1 in group 8
(assert (not (mem g_s33_35 (|+->| (dom g_s33_35) (ran g_s33_35)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO group 9 
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
(define-fun lh_1 () Bool (mem (card g_s34_36) INT))
; PO 1 in group 9
(push 1)
(assert (not (mem g_s34_36 (FIN g_s34_36))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 9
(push 1)
(assert (not (=> lh_1 (mem g_s34_36 (FIN g_s34_36)))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 10 
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
(assert (mem g_s58_55 NATURAL))
(assert (mem g_s58_55 (dom g_s36_38)))
; PO 1 in group 10
(assert (not (mem g_s36_38 (|+->| (dom g_s36_38) (ran g_s36_38)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO group 11 
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
(define-fun lh_1 () Bool (mem (card g_s37_39) INT))
; PO 1 in group 11
(push 1)
(assert (not (mem g_s37_39 (FIN g_s37_39))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 11
(push 1)
(assert (not (=> lh_1 (mem g_s37_39 (FIN g_s37_39)))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 12 
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
(assert (mem g_s58_55 NATURAL))
(assert (mem g_s58_55 (dom g_s39_41)))
; PO 1 in group 12
(assert (not (mem g_s39_41 (|+->| (dom g_s39_41) (ran g_s39_41)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO group 13 
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
(define-fun lh_1 () Bool (mem (card g_s40_42) INT))
; PO 1 in group 13
(push 1)
(assert (not (mem g_s40_42 (FIN g_s40_42))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 13
(push 1)
(assert (not (=> lh_1 (mem g_s40_42 (FIN g_s40_42)))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 14 
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
(assert (mem g_s58_55 NATURAL))
(assert (mem g_s58_55 (dom g_s42_44)))
; PO 1 in group 14
(assert (not (mem g_s42_44 (|+->| (dom g_s42_44) (ran g_s42_44)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO group 15 
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
(define-fun lh_1 () Bool (mem (card g_s43_45) INT))
; PO 1 in group 15
(push 1)
(assert (not (mem g_s43_45 (FIN g_s43_45))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 15
(push 1)
(assert (not (=> lh_1 (mem g_s43_45 (FIN g_s43_45)))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 16 
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
(assert (mem g_s58_55 NATURAL))
(assert (mem g_s58_55 (dom g_s45_47)))
; PO 1 in group 16
(assert (not (mem g_s45_47 (|+->| (dom g_s45_47) (ran g_s45_47)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO group 17 
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
(define-fun lh_1 () Bool (mem (card g_s46_48) INT))
; PO 1 in group 17
(push 1)
(assert (not (mem g_s46_48 (FIN g_s46_48))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 17
(push 1)
(assert (not (=> lh_1 (mem g_s46_48 (FIN g_s46_48)))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 18 
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
(assert (mem g_s58_55 NATURAL))
(assert (mem g_s58_55 (dom g_s48_50)))
; PO 1 in group 18
(assert (not (mem g_s48_50 (|+->| (dom g_s48_50) (ran g_s48_50)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO group 19 
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
(assert (mem g_s76_58 g_s23_25))
(define-fun lh_1 () Bool (mem g_s77$1_59 g_s16_18))
; PO 1 in group 19
(push 1)
(assert (not (=> lh_1 (mem g_s50_52 (|+->| (dom g_s50_52) (ran g_s50_52))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 19
(push 1)
(assert (not (=> lh_1 (mem g_s76_58 (dom g_s50_52)))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
(exit)