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
(declare-fun g_s0_1 () U)
(declare-fun g_s1_2 () U)
(declare-fun g_s11_12 () U)
(declare-fun g_s12_13 () U)
(declare-fun g_s13_14 () U)
(declare-fun g_s14_15 () U)
(declare-fun g_s15_16 () U)
(declare-fun g_s16_17 () U)
(declare-fun g_s17_18 () U)
(declare-fun g_s18_19 () U)
(declare-fun g_s19_20 () U)
(declare-fun g_s2_3 () U)
(declare-fun g_s20_21 () U)
(declare-fun g_s21_22 () U)
(declare-fun g_s22_23 () U)
(declare-fun g_s23_24 () U)
(declare-fun g_s24_25 () U)
(declare-fun g_s25_26 () U)
(declare-fun g_s26_27 () U)
(declare-fun g_s27_28 () U)
(declare-fun g_s28_29 () U)
(declare-fun g_s29_30 () U)
(declare-fun g_s3_4 () U)
(declare-fun g_s30_31 () U)
(declare-fun g_s31_32 () U)
(declare-fun g_s32_33 () U)
(declare-fun g_s33_34 () U)
(declare-fun g_s34_35 () U)
(declare-fun g_s35_36 () U)
(declare-fun g_s36_37 () U)
(declare-fun g_s37_38 () U)
(declare-fun g_s38_39 () U)
(declare-fun g_s39_40 () U)
(declare-fun g_s4_5 () U)
(declare-fun g_s40_41 () U)
(declare-fun g_s41_42 () U)
(declare-fun g_s42_43 () U)
(declare-fun g_s43_44 () U)
(declare-fun g_s44_45 () U)
(declare-fun g_s45_46 () U)
(declare-fun g_s46_47 () U)
(declare-fun g_s47_48 () U)
(declare-fun g_s48_49 () U)
(declare-fun g_s49_50 () U)
(declare-fun g_s5_6 () U)
(declare-fun g_s50_51 () U)
(declare-fun g_s53_53 () U)
(declare-fun g_s54_54 () U)
(declare-fun g_s55_55 () U)
(declare-fun g_s56_56 () U)
(declare-fun g_s57_57 () U)
(declare-fun g_s58_58 () U)
(declare-fun g_s59_59 () U)
(declare-fun g_s6_7 () U)
(declare-fun g_s60_60 () U)
(declare-fun g_s61_61 () U)
(declare-fun g_s62_62 () U)
(declare-fun g_s63_63 () U)
(declare-fun g_s64_64 () U)
(declare-fun g_s65_65 () U)
(declare-fun g_s66_66 () U)
(declare-fun g_s67_67 () U)
(declare-fun g_s68_68 () U)
(declare-fun g_s69_69 () U)
(declare-fun g_s7_9 () U)
(declare-fun g_s70_70 () U)
(declare-fun g_s71_71 () U)
(declare-fun g_s72_72 () U)
(declare-fun g_s73_74 () U)
(declare-fun g_s74_73 () U)
(declare-fun g_s75_76 () U)
(declare-fun g_s76_75 () U)
(declare-fun g_s77_77 () U)
(declare-fun g_s78_79 () U)
(declare-fun g_s79_78 () U)
(declare-fun g_s80_80 () U)
(declare-fun g_s81_81 () U)
(declare-fun g_s82_82 () U)
(declare-fun g_s83_83 () U)
(declare-fun g_s84_84 () U)
(declare-fun g_s84$1_85 () U)
(declare-fun g_s88_86 () U)
(declare-fun g_s9_11 () U)
(declare-fun g_s91_88 () U)
(declare-fun g_s91$1_87 () U)
(declare-fun g_s93_90 () U)
(declare-fun g_s93$1_89 () U)
(declare-fun g_s93$2_91 () U)
(declare-fun e8 () U)
(declare-fun e10 () U)
(declare-fun e52 () U)
; Defines
(define-fun |def_B definitions| () Bool (and (= NAT (interval e0 MaxInt)) (= INT (interval MinInt MaxInt))))
(define-fun |def_ctx| () Bool (and (not (= g_s0_1 empty)) (not (= g_s1_2 empty)) (not (= g_s2_3 empty)) (not (= g_s3_4 empty)) (not (= g_s4_5 empty)) (not (= g_s5_6 empty)) (not (= g_s6_7 empty)) (= g_s7_9 e8) (= g_s9_11 e10) (= g_s11_12 INT) (= g_s12_13 NAT) (= g_s13_14 NAT1) (subset g_s13_14 g_s12_13) (subset g_s12_13 g_s11_12) (mem g_s14_15 g_s11_12) (mem g_s14_15 g_s12_13) (not (mem g_s14_15 g_s13_14)) (mem g_s15_16 g_s11_12) (not (mem g_s15_16 g_s12_13)) (= g_s16_17 INT) (subset g_s17_18 g_s0_1) (mem g_s18_19 g_s0_1) (mem g_s18_19 g_s17_18) (mem g_s19_20 g_s0_1) (not (mem g_s19_20 g_s17_18)) (mem g_s20_21 (|+->| NAT g_s0_1)) (mem g_s20_21 (perm g_s17_18)) (= (card g_s17_18) g_s21_22) (subset g_s22_23 g_s1_2) (mem g_s23_24 g_s1_2) (mem g_s23_24 g_s22_23) (mem g_s24_25 g_s1_2) (not (mem g_s24_25 g_s22_23)) (mem g_s25_26 (|+->| NAT g_s1_2)) (mem g_s25_26 (perm g_s22_23)) (= (card g_s22_23) g_s26_27) (mem g_s27_28 (|+->| (set_prod g_s16_17 g_s16_17) g_s16_17)) (subset g_s28_29 g_s16_17) (mem g_s29_30 (|-->| (set_prod g_s12_13 g_s12_13) g_s16_17)) (mem g_s30_31 (|+->| (set_prod g_s12_13 g_s16_17) g_s12_13)) (mem g_s31_32 (|-->| (set_prod g_s12_13 g_s16_17) g_s12_13)) (mem g_s32_33 (|-->| (set_prod g_s12_13 g_s16_17) (POW g_s12_13))) (mem g_s33_34 (|-->| (set_prod g_s12_13 g_s12_13) (POW g_s12_13))) (mem g_s34_35 (|-->| (set_prod g_s12_13 g_s12_13) (POW g_s12_13))) (mem g_s35_36 (|-->| (set_prod g_s12_13 g_s12_13) (POW g_s12_13))) (mem g_s36_37 (|-->| (set_prod g_s12_13 g_s12_13) (POW g_s12_13))) (mem g_s37_38 (|<->| g_s12_13 g_s12_13)) (mem g_s38_39 (|<->| g_s12_13 g_s12_13)) (mem g_s39_40 (|<->| (set_prod g_s12_13 g_s16_17) g_s12_13)) (mem g_s40_41 (|<->| (set_prod g_s12_13 g_s16_17) g_s12_13)) (mem g_s41_42 (|<->| (set_prod g_s12_13 g_s16_17) g_s12_13)) (mem g_s42_43 (|<->| (set_prod g_s12_13 g_s16_17) g_s12_13)) (mem g_s43_44 (|<->| g_s12_13 g_s12_13)) (mem g_s44_45 (|<->| g_s12_13 g_s12_13)) (mem g_s45_46 (|<->| (set_prod g_s12_13 g_s16_17) g_s12_13)) (mem g_s46_47 (|<->| (set_prod g_s12_13 g_s16_17) g_s12_13)) (mem g_s47_48 (|<->| (set_prod g_s12_13 g_s16_17) g_s12_13)) (mem g_s48_49 (|<->| (set_prod g_s12_13 g_s16_17) g_s12_13)) (mem g_s49_50 (|-->| (set_prod g_s12_13 g_s12_13) g_s12_13)) (mem g_s50_51 (|-->| (set_prod g_s12_13 g_s12_13) g_s12_13)) (= (dom g_s30_31) (set_prod g_s12_13 NAT)) (= (dom g_s27_28) e52) (subset g_s53_53 g_s2_3) (mem g_s54_54 g_s2_3) (not (mem g_s54_54 g_s53_53)) (mem g_s55_55 (|+->| NAT g_s2_3)) (mem g_s55_55 (perm g_s53_53)) (subset g_s56_56 g_s3_4) (mem g_s57_57 g_s3_4) (not (mem g_s57_57 g_s56_56)) (mem g_s58_58 (|+->| NAT g_s3_4)) (mem g_s58_58 (perm g_s56_56)) (subset g_s59_59 g_s4_5) (mem g_s60_60 g_s4_5) (not (mem g_s60_60 g_s59_59)) (mem g_s61_61 (|+->| NAT g_s4_5)) (mem g_s61_61 (perm g_s59_59)) (subset g_s62_62 g_s5_6) (mem g_s63_63 g_s5_6) (not (mem g_s63_63 g_s62_62)) (mem g_s64_64 (|+->| NAT g_s5_6)) (mem g_s64_64 (perm g_s62_62)) (subset g_s65_65 g_s6_7) (mem g_s66_66 g_s6_7) (not (mem g_s66_66 g_s65_65)) (mem g_s67_67 (|+->| NAT g_s6_7)) (mem g_s67_67 (perm g_s65_65)) (mem g_s68_68 (|>->| g_s53_53 g_s22_23)) (mem g_s69_69 (|>->| g_s56_56 g_s22_23)) (mem g_s70_70 g_s1_2) (=> (not (= g_s71_71 e0)) (mem g_s70_70 g_s22_23)) (mem g_s72_72 (|>->| g_s62_62 g_s22_23)) (= (binary_inter (ran g_s68_68) (ran g_s69_69)) empty) (= (binary_inter (ran g_s68_68) (ran g_s72_72)) empty) (= (binary_inter (ran g_s72_72) (ran g_s69_69)) empty) (=> (not (= g_s71_71 e0)) (not (mem g_s70_70 (ran g_s68_68)))) (=> (not (= g_s71_71 e0)) (not (mem g_s70_70 (ran g_s69_69)))) (=> (not (= g_s71_71 e0)) (not (mem g_s70_70 (ran g_s72_72))))))
(define-fun |def_seext| () Bool (and (mem g_s73_74 (|+->| g_s62_62 g_s74_73)) (mem g_s75_76 (|+->| g_s62_62 g_s76_75)) (mem g_s77_77 (|-->| g_s62_62 NAT)) (mem g_s78_79 (|-->| g_s62_62 (POW g_s79_78))) (mem g_s80_80 (|+->| g_s62_62 g_s12_13)) (mem g_s81_81 (|+->| g_s62_62 g_s12_13)) (subset g_s82_82 g_s62_62) (subset g_s83_83 g_s62_62)))
(define-fun |def_lprp| () Bool true)
(define-fun |def_inprp| () Bool true)
(define-fun |def_inext| () Bool true)
(define-fun |def_mchcst| () Bool true)
(define-fun |def_aprp| () Bool true)
(define-fun |def_abs| () Bool  (mem g_s84_84 (|+->| g_s62_62 g_s12_13)))
(define-fun |def_inv| () Bool (and (= g_s84_84 g_s84$1_85) (mem g_s84$1_85 (|+->| g_s62_62 g_s12_13))))
(define-fun |def_ass| () Bool true)
(define-fun |def_sets| () Bool true)
; PO group 0 
(push 1)
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_mchcst|)
(assert |def_aprp|)
(assert |def_lprp|)
(assert |def_inprp|)
(assert |def_inext|)
(assert |def_seext|)
; PO 1 in group 0
(assert (not (mem empty (|+->| g_s62_62 g_s12_13))))
(check-sat)
(pop 1)
; PO group 1 
(push 1)
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_mchcst|)
(assert |def_aprp|)
(assert |def_lprp|)
(assert |def_inprp|)
(assert |def_inext|)
(assert |def_seext|)
(assert |def_abs|)
(assert |def_inv|)
(assert |def_ass|)
(assert (mem g_s88_86 g_s5_6))
(assert (mem g_s88_86 g_s62_62))
(assert (mem g_s88_86 g_s5_6))
(assert (mem g_s88_86 g_s62_62))
; PO 1 in group 1
(assert (not (mem (domain_subtraction (SET g_s88_86) g_s84$1_85) (|+->| g_s62_62 g_s12_13))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO group 2 
(push 1)
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_mchcst|)
(assert |def_aprp|)
(assert |def_lprp|)
(assert |def_inprp|)
(assert |def_inext|)
(assert |def_seext|)
(assert |def_abs|)
(assert |def_inv|)
(assert |def_ass|)
(assert (mem g_s88_86 g_s5_6))
(assert (mem g_s88_86 g_s62_62))
(assert (mem g_s88_86 g_s5_6))
(assert (mem g_s88_86 g_s62_62))
(define-fun lh_1 () Bool (mem g_s88_86 (binary_inter g_s83_83 (dom g_s80_80))))
(define-fun lh_2 () Bool (not (mem g_s88_86 (dom g_s84$1_85))))
; PO 1 in group 2
(assert (not (=> (and lh_1 lh_2) (mem (|<+| g_s84$1_85 (SET (mapplet g_s88_86 (apply g_s80_80 g_s88_86)))) (|+->| g_s62_62 g_s12_13)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO group 3 
(push 1)
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_mchcst|)
(assert |def_aprp|)
(assert |def_lprp|)
(assert |def_inprp|)
(assert |def_inext|)
(assert |def_seext|)
(assert |def_abs|)
(assert |def_inv|)
(assert |def_ass|)
(assert (mem g_s88_86 g_s5_6))
(assert (mem g_s88_86 g_s62_62))
(assert (= g_s91_88 g_s91$1_87))
(assert (mem g_s88_86 g_s5_6))
(assert (mem g_s88_86 g_s62_62))
; PO 1 in group 3
(assert (not (= (bool (mem g_s88_86 (dom g_s84_84))) (bool (mem g_s88_86 (dom g_s84$1_85))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO group 4 
(push 1)
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_mchcst|)
(assert |def_aprp|)
(assert |def_lprp|)
(assert |def_inprp|)
(assert |def_inext|)
(assert |def_seext|)
(assert |def_abs|)
(assert |def_inv|)
(assert |def_ass|)
(assert (mem g_s88_86 g_s5_6))
(assert (mem g_s88_86 g_s62_62))
(assert (mem g_s88_86 (dom g_s84_84)))
(assert (= g_s93_90 g_s93$1_89))
; PO 1 in group 4
(assert (not (mem g_s88_86 (dom g_s84$1_85))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO group 5 
(push 1)
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_mchcst|)
(assert |def_aprp|)
(assert |def_lprp|)
(assert |def_inprp|)
(assert |def_inext|)
(assert |def_seext|)
(assert |def_abs|)
(assert |def_inv|)
(assert |def_ass|)
(assert (mem g_s88_86 g_s5_6))
(assert (mem g_s88_86 g_s62_62))
(assert (mem g_s88_86 (dom g_s84_84)))
(assert (= g_s93_90 g_s93$1_89))
(assert (mem g_s88_86 g_s5_6))
(assert (mem g_s88_86 g_s62_62))
(assert (mem g_s88_86 (dom g_s84$1_85)))
(define-fun lh_1 () Bool (mem g_s93$2_91 g_s11_12))
(define-fun lh_2 () Bool (= g_s93$2_91 (apply g_s84$1_85 g_s88_86)))
; PO 1 in group 5
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem (apply g_s84_84 g_s88_86) g_s11_12))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 5
(push 1)
(assert (not (=> (and lh_1 lh_2) (= (apply g_s84_84 g_s88_86) g_s93$2_91))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 6 
(push 1)
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_mchcst|)
(assert |def_aprp|)
(assert |def_lprp|)
(assert |def_inprp|)
(assert |def_inext|)
(assert |def_seext|)
(assert |def_abs|)
(assert |def_inv|)
(assert |def_ass|)
(assert (mem g_s88_86 g_s5_6))
(assert (mem g_s88_86 g_s62_62))
(assert (= g_s91_88 g_s91$1_87))
(assert (= g_s93_90 g_s93$1_89))
(assert (mem g_s88_86 g_s5_6))
(assert (mem g_s88_86 g_s62_62))
(define-fun lh_1 () Bool (mem g_s88_86 (dom g_s84$1_85)))
(define-fun lh_2 () Bool (mem g_s93$2_91 g_s11_12))
(define-fun lh_3 () Bool (= g_s93$2_91 (apply g_s84$1_85 g_s88_86)))
(define-fun lh_4 () Bool (mem g_s88_86 (dom g_s84_84)))
; PO 1 in group 6
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem (apply g_s84_84 g_s88_86) g_s11_12))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 6
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (= (bool (mem g_s88_86 (dom g_s84_84))) (bool (mem g_s88_86 (dom g_s84$1_85)))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 6
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (= (apply g_s84_84 g_s88_86) g_s93$2_91))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 7 
(push 1)
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_mchcst|)
(assert |def_aprp|)
(assert |def_lprp|)
(assert |def_inprp|)
(assert |def_inext|)
(assert |def_seext|)
(assert |def_abs|)
(assert |def_inv|)
(assert |def_ass|)
(assert (mem g_s88_86 g_s5_6))
(assert (mem g_s88_86 g_s62_62))
(assert (mem g_s88_86 g_s5_6))
(assert (mem g_s88_86 g_s62_62))
(define-fun lh_1 () Bool (mem g_s88_86 (binary_inter g_s83_83 (dom g_s80_80))))
(define-fun lh_2 () Bool (not (mem g_s88_86 (dom g_s84$1_85))))
; PO 1 in group 7
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem g_s80_80 (|+->| (dom g_s80_80) (ran g_s80_80))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 7
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem g_s88_86 (dom g_s80_80)))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 8 
(push 1)
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_mchcst|)
(assert |def_aprp|)
(assert |def_lprp|)
(assert |def_inprp|)
(assert |def_inext|)
(assert |def_seext|)
(assert |def_abs|)
(assert |def_inv|)
(assert |def_ass|)
(assert (mem g_s88_86 g_s5_6))
(assert (mem g_s88_86 g_s62_62))
(assert (mem g_s88_86 (dom g_s84_84)))
(assert (mem g_s88_86 g_s5_6))
(assert (mem g_s88_86 g_s62_62))
(assert (mem g_s88_86 (dom g_s84$1_85)))
(define-fun lh_1 () Bool (mem g_s93$2_91 g_s11_12))
; PO 1 in group 8
(assert (not (=> lh_1 (mem g_s84$1_85 (|+->| (dom g_s84$1_85) (ran g_s84$1_85))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO group 9 
(push 1)
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_mchcst|)
(assert |def_aprp|)
(assert |def_lprp|)
(assert |def_inprp|)
(assert |def_inext|)
(assert |def_seext|)
(assert |def_abs|)
(assert |def_inv|)
(assert |def_ass|)
(assert (mem g_s88_86 g_s5_6))
(assert (mem g_s88_86 g_s62_62))
(assert (mem g_s88_86 g_s5_6))
(assert (mem g_s88_86 g_s62_62))
(define-fun lh_1 () Bool (mem g_s88_86 (dom g_s84$1_85)))
(define-fun lh_2 () Bool (mem g_s93$2_91 g_s11_12))
; PO 1 in group 9
(assert (not (=> (and lh_1 lh_2) (mem g_s84$1_85 (|+->| (dom g_s84$1_85) (ran g_s84$1_85))))))
(set-info :status unknown)
(check-sat)
(pop 1)
(exit)