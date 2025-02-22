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
(declare-fun e30 () U)
(declare-fun g_s0_1 () U)
(declare-fun g_s1_2 () U)
(declare-fun g_s10_11 () U)
(declare-fun g_s100_103 () U)
(declare-fun g_s101_104 () U)
(declare-fun g_s102_105 () U)
(declare-fun g_s103_106 () U)
(declare-fun g_s104_107 () U)
(declare-fun g_s105_108 () U)
(declare-fun g_s106_109 () U)
(declare-fun g_s107_110 () U)
(declare-fun g_s108_111 () U)
(declare-fun g_s109_112 () U)
(declare-fun g_s110_113 () U)
(declare-fun g_s111_114 () U)
(declare-fun g_s112_115 () U)
(declare-fun g_s113_116 () U)
(declare-fun g_s114_117 () U)
(declare-fun g_s120_118 () U)
(declare-fun g_s13_14 () U)
(declare-fun g_s14_16 () U)
(declare-fun g_s15_17 () U)
(declare-fun g_s16_18 () U)
(declare-fun g_s17_20 () U)
(declare-fun g_s18_19 () U)
(declare-fun g_s19_22 () U)
(declare-fun g_s2_3 () U)
(declare-fun g_s20_21 () U)
(declare-fun g_s21_24 () U)
(declare-fun g_s22_23 () U)
(declare-fun g_s23_25 () U)
(declare-fun g_s24_27 () U)
(declare-fun g_s25_26 () U)
(declare-fun g_s26_28 () U)
(declare-fun g_s27_29 () U)
(declare-fun g_s28_32 () U)
(declare-fun g_s29_31 () U)
(declare-fun g_s3_4 () U)
(declare-fun g_s30_33 () U)
(declare-fun g_s31_34 () U)
(declare-fun g_s32_35 () U)
(declare-fun g_s33_36 () U)
(declare-fun g_s34_37 () U)
(declare-fun g_s35_38 () U)
(declare-fun g_s36_39 () U)
(declare-fun g_s37_40 () U)
(declare-fun g_s38_41 () U)
(declare-fun g_s39_42 () U)
(declare-fun g_s4_5 () U)
(declare-fun g_s40_43 () U)
(declare-fun g_s41_44 () U)
(declare-fun g_s42_45 () U)
(declare-fun g_s43_46 () U)
(declare-fun g_s44_47 () U)
(declare-fun g_s45_48 () U)
(declare-fun g_s46_49 () U)
(declare-fun g_s47_50 () U)
(declare-fun g_s48_51 () U)
(declare-fun g_s49_52 () U)
(declare-fun g_s5_6 () U)
(declare-fun g_s50_53 () U)
(declare-fun g_s51_54 () U)
(declare-fun g_s52_55 () U)
(declare-fun g_s53_56 () U)
(declare-fun g_s54_57 () U)
(declare-fun g_s55_58 () U)
(declare-fun g_s56_59 () U)
(declare-fun g_s57_60 () U)
(declare-fun g_s58_61 () U)
(declare-fun g_s59_62 () U)
(declare-fun g_s6_7 () U)
(declare-fun g_s60_63 () U)
(declare-fun g_s61_64 () U)
(declare-fun g_s62_65 () U)
(declare-fun g_s63_66 () U)
(declare-fun g_s64_67 () U)
(declare-fun g_s65_68 () U)
(declare-fun g_s66_69 () U)
(declare-fun g_s67_70 () U)
(declare-fun g_s68_71 () U)
(declare-fun g_s69_72 () U)
(declare-fun g_s7_8 () U)
(declare-fun g_s70_73 () U)
(declare-fun g_s71_74 () U)
(declare-fun g_s72_75 () U)
(declare-fun g_s73_76 () U)
(declare-fun g_s74_77 () U)
(declare-fun g_s75_78 () U)
(declare-fun g_s76_79 () U)
(declare-fun g_s77_80 () U)
(declare-fun g_s78_81 () U)
(declare-fun g_s79_82 () U)
(declare-fun g_s8_9 () U)
(declare-fun g_s80_83 () U)
(declare-fun g_s81_84 () U)
(declare-fun g_s82_85 () U)
(declare-fun g_s83_86 () U)
(declare-fun g_s84_87 () U)
(declare-fun g_s85_88 () U)
(declare-fun g_s86_89 () U)
(declare-fun g_s87_90 () U)
(declare-fun g_s88_91 () U)
(declare-fun g_s89_92 () U)
(declare-fun g_s9_10 () U)
(declare-fun g_s90_93 () U)
(declare-fun g_s91_94 () U)
(declare-fun g_s92_95 () U)
(declare-fun g_s93_96 () U)
(declare-fun g_s94_97 () U)
(declare-fun g_s95_98 () U)
(declare-fun g_s96_99 () U)
(declare-fun g_s97_100 () U)
(declare-fun g_s98_101 () U)
(declare-fun g_s99_102 () U)
(declare-fun e13 () U)
(declare-fun e12 () U)
; Defines
(define-fun |def_B definitions| () Bool (and (= NAT (interval e0 MaxInt)) (= INT (interval MinInt MaxInt))))
(define-fun |def_ctx| () Bool (and (not (= g_s0_1 empty)) (not (= g_s1_2 empty)) (not (= g_s2_3 empty)) (not (= g_s3_4 empty)) (not (= g_s4_5 empty)) (not (= g_s5_6 empty)) (not (= g_s6_7 empty)) (not (= g_s7_8 empty)) (not (= g_s8_9 empty)) (not (= g_s9_10 empty)) (mem g_s10_11 (|-->| (set_prod INTEGER NATURAL) INTEGER)) (= g_s10_11 (binary_union e13 e12)) (mem g_s13_14 (|-->| BOOL NAT)) (= g_s13_14 (SET (mapplet (mapplet FALSE e0) (mapplet TRUE e15)))) (|<i| g_s14_16 MaxInt) (|<i| g_s15_17 MaxInt) (|<i| g_s16_18 MaxInt) (|<=i| g_s17_20 g_s18_19) (|<=i| g_s19_22 g_s20_21) (|<=i| g_s21_24 g_s22_23) (|<=i| g_s23_25 g_s22_23) (|<i| g_s24_27 g_s25_26) (not (mem g_s26_28 (interval g_s24_27 g_s25_26))) (= g_s27_29 MaxInt) (= g_s28_32 (|*i| g_s29_31 e30)) (mem g_s14_16 NAT) (mem g_s15_17 NAT) (mem g_s16_18 NAT) (mem g_s30_33 NAT) (mem g_s31_34 NAT) (mem g_s32_35 NAT) (mem g_s33_36 NAT) (mem g_s34_37 NAT) (mem g_s35_38 NAT) (mem g_s36_39 NAT) (mem g_s37_40 NAT) (mem g_s38_41 NAT) (mem g_s39_42 NAT) (mem g_s40_43 NAT) (mem g_s20_21 NAT) (mem g_s41_44 NAT) (mem g_s42_45 NAT) (mem g_s43_46 NAT) (mem g_s44_47 NAT) (mem g_s45_48 NAT) (mem g_s46_49 NAT) (mem g_s47_50 NAT) (mem g_s48_51 NAT1) (mem g_s49_52 NAT) (mem g_s19_22 NAT) (mem g_s50_53 NAT) (mem g_s51_54 NAT) (mem g_s52_55 NAT) (mem g_s53_56 NAT) (mem g_s54_57 NAT) (mem g_s55_58 NAT) (mem g_s56_59 NAT) (mem g_s57_60 NAT) (mem g_s58_61 NAT) (mem g_s59_62 NAT) (mem g_s60_63 NAT) (mem g_s61_64 NAT) (mem g_s18_19 NAT) (mem g_s17_20 NAT) (mem g_s62_65 NAT) (mem g_s63_66 NAT) (mem g_s64_67 NAT) (mem g_s65_68 NAT) (mem g_s66_69 NAT) (mem g_s67_70 NAT) (mem g_s68_71 NAT) (mem g_s69_72 NAT) (mem g_s70_73 NAT) (mem g_s71_74 NAT) (mem g_s72_75 NAT) (mem g_s73_76 NAT) (mem g_s74_77 NAT) (mem g_s75_78 NAT) (mem g_s76_79 NAT) (mem g_s77_80 NAT) (mem g_s78_81 NAT1) (mem g_s79_82 NAT) (mem g_s80_83 NAT) (mem g_s81_84 NAT) (mem g_s82_85 NAT) (mem g_s83_86 NAT) (mem g_s22_23 NAT) (mem g_s21_24 NAT) (mem g_s23_25 NAT) (mem g_s28_32 NAT) (mem g_s29_31 NAT) (mem g_s84_87 NAT) (mem g_s27_29 NAT) (mem g_s85_88 NAT) (mem g_s86_89 NAT) (mem g_s24_27 INT) (mem g_s25_26 NAT) (mem g_s26_28 INT)))
(define-fun |def_seext| () Bool  (mem g_s87_90 g_s8_9))
(define-fun |def_lprp| () Bool (and (not (= g_s88_91 empty)) (not (= g_s89_92 empty)) (not (= g_s90_93 empty)) (not (= g_s91_94 empty)) (not (= g_s92_95 empty)) (subset g_s93_96 g_s88_91) (mem g_s94_97 g_s88_91) (not (mem g_s94_97 g_s93_96)) (mem g_s95_98 (|+->| NAT g_s88_91)) (mem g_s95_98 (perm g_s93_96)) (mem (card g_s93_96) NAT) (subset g_s96_99 g_s89_92) (mem g_s97_100 g_s89_92) (not (mem g_s97_100 g_s96_99)) (mem g_s98_101 (|+->| NAT g_s89_92)) (mem g_s98_101 (perm g_s96_99)) (subset g_s99_102 g_s90_93) (mem g_s100_103 g_s90_93) (not (mem g_s100_103 g_s99_102)) (mem g_s101_104 (|+->| NAT g_s90_93)) (mem g_s101_104 (perm g_s99_102)) (subset g_s102_105 g_s91_94) (mem g_s103_106 g_s91_94) (not (mem g_s103_106 g_s102_105)) (mem g_s104_107 (|+->| NAT g_s91_94)) (mem g_s104_107 (perm g_s102_105)) (mem g_s105_108 g_s92_95) (subset g_s106_109 INT) (= g_s106_109 (interval e0 g_s78_81)) (subset g_s107_110 g_s106_109) (subset g_s107_110 NAT) (mem g_s108_111 g_s106_109) (not (mem g_s108_111 g_s107_110)) (= g_s109_112 INT) (subset g_s110_113 NAT) (subset g_s110_113 g_s109_112) (mem g_s111_114 g_s109_112) (not (mem g_s111_114 g_s110_113)) (= g_s112_115 INT) (subset g_s113_116 INT) (subset g_s113_116 g_s112_115) (mem g_s114_117 g_s112_115) (not (mem g_s114_117 g_s113_116))))
(define-fun |def_inprp| () Bool true)
(define-fun |def_inext| () Bool true)
(define-fun |def_inv| () Bool true)
(define-fun |def_ass| () Bool true)
(define-fun |def_cst| () Bool true)
(define-fun |def_sets| () Bool (and (not (= g_s88_91 empty)) (not (= g_s89_92 empty)) (not (= g_s90_93 empty)) (not (= g_s91_94 empty)) (not (= g_s92_95 empty))))
; PO group 0 
(push 1)
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_cst|)
(assert |def_sets|)
(define-fun lh_1 () Bool (subset g_s93_96 g_s88_91))
(define-fun lh_2 () Bool (mem g_s94_97 g_s88_91))
(define-fun lh_3 () Bool (not (mem g_s94_97 g_s93_96)))
(define-fun lh_4 () Bool (mem g_s95_98 (|+->| NAT g_s88_91)))
(define-fun lh_5 () Bool (mem g_s95_98 (perm g_s93_96)))
(define-fun lh_6 () Bool (mem (card g_s93_96) NAT))
(define-fun lh_7 () Bool (subset g_s96_99 g_s89_92))
(define-fun lh_8 () Bool (mem g_s97_100 g_s89_92))
(define-fun lh_9 () Bool (not (mem g_s97_100 g_s96_99)))
(define-fun lh_10 () Bool (mem g_s98_101 (|+->| NAT g_s89_92)))
(define-fun lh_11 () Bool (mem g_s98_101 (perm g_s96_99)))
(define-fun lh_12 () Bool (subset g_s99_102 g_s90_93))
(define-fun lh_13 () Bool (mem g_s100_103 g_s90_93))
(define-fun lh_14 () Bool (not (mem g_s100_103 g_s99_102)))
(define-fun lh_15 () Bool (mem g_s101_104 (|+->| NAT g_s90_93)))
(define-fun lh_16 () Bool (mem g_s101_104 (perm g_s99_102)))
(define-fun lh_17 () Bool (subset g_s102_105 g_s91_94))
(define-fun lh_18 () Bool (mem g_s103_106 g_s91_94))
(define-fun lh_19 () Bool (not (mem g_s103_106 g_s102_105)))
(define-fun lh_20 () Bool (mem g_s104_107 (|+->| NAT g_s91_94)))
; PO 1 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem g_s93_96 (FIN g_s93_96)))))
(check-sat)
(pop 1)
; PO 2 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5) (mem g_s93_96 (FIN g_s93_96)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10) (mem g_s96_99 (FIN g_s96_99)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15) (mem g_s99_102 (FIN g_s99_102)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 5 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20) (mem g_s102_105 (FIN g_s102_105)))))
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
(define-fun lh_1 () Bool (mem (card g_s93_96) INT))
; PO 1 in group 1
(push 1)
(assert (not (mem g_s93_96 (FIN g_s93_96))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 1
(push 1)
(assert (not (=> lh_1 (mem g_s93_96 (FIN g_s93_96)))))
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
(assert (mem g_s120_118 NATURAL))
(assert (mem g_s120_118 (dom g_s95_98)))
; PO 1 in group 2
(assert (not (mem g_s95_98 (|+->| (dom g_s95_98) (ran g_s95_98)))))
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
(define-fun lh_1 () Bool (mem (card g_s96_99) INT))
; PO 1 in group 3
(push 1)
(assert (not (mem g_s96_99 (FIN g_s96_99))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 3
(push 1)
(assert (not (=> lh_1 (mem g_s96_99 (FIN g_s96_99)))))
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
(assert (mem g_s120_118 NATURAL))
(assert (mem g_s120_118 (dom g_s98_101)))
; PO 1 in group 4
(assert (not (mem g_s98_101 (|+->| (dom g_s98_101) (ran g_s98_101)))))
(set-info :status unknown)
(check-sat)
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
(define-fun lh_1 () Bool (mem (card g_s99_102) INT))
; PO 1 in group 5
(push 1)
(assert (not (mem g_s99_102 (FIN g_s99_102))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 5
(push 1)
(assert (not (=> lh_1 (mem g_s99_102 (FIN g_s99_102)))))
(set-info :status unknown)
(check-sat)
(pop 1)
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
(assert (mem g_s120_118 NATURAL))
(assert (mem g_s120_118 (dom g_s101_104)))
; PO 1 in group 6
(assert (not (mem g_s101_104 (|+->| (dom g_s101_104) (ran g_s101_104)))))
(set-info :status unknown)
(check-sat)
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
(define-fun lh_1 () Bool (mem (card g_s102_105) INT))
; PO 1 in group 7
(push 1)
(assert (not (mem g_s102_105 (FIN g_s102_105))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 7
(push 1)
(assert (not (=> lh_1 (mem g_s102_105 (FIN g_s102_105)))))
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
(assert (mem g_s120_118 NATURAL))
(assert (mem g_s120_118 (dom g_s104_107)))
; PO 1 in group 8
(assert (not (mem g_s104_107 (|+->| (dom g_s104_107) (ran g_s104_107)))))
(set-info :status unknown)
(check-sat)
(pop 1)
(exit)