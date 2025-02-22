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
(declare-fun e18 () U)
(declare-fun e0 () U)
(declare-fun e47 () U)
(declare-fun e22 () U)
(declare-fun e20 () U)
(declare-fun e42 () U)
(declare-fun e19 () U)
(declare-fun g_s0_1 () U)
(declare-fun g_s1_2 () U)
(declare-fun g_s10_10 () U)
(declare-fun g_s100_118 () U)
(declare-fun g_s101_119 () U)
(declare-fun g_s102_120 () U)
(declare-fun g_s103_121 () U)
(declare-fun g_s104_122 () U)
(declare-fun g_s105_123 () U)
(declare-fun g_s106_124 () U)
(declare-fun g_s107_125 () U)
(declare-fun g_s108_126 () U)
(declare-fun g_s109_127 () U)
(declare-fun g_s11_13 () U)
(declare-fun g_s110_128 () U)
(declare-fun g_s111_129 () U)
(declare-fun g_s112_130 () U)
(declare-fun g_s113_131 () U)
(declare-fun g_s114_132 () U)
(declare-fun g_s115_133 () U)
(declare-fun g_s116_134 () U)
(declare-fun g_s117$1_135 () U)
(declare-fun g_s12_12 () U)
(declare-fun g_s121$1_136 () U)
(declare-fun g_s122$1_137 () U)
(declare-fun g_s123$1_138 () U)
(declare-fun g_s13_15 () U)
(declare-fun g_s14_14 () U)
(declare-fun g_s15_16 () U)
(declare-fun g_s16_17 () U)
(declare-fun g_s17_21 () U)
(declare-fun g_s18_23 () U)
(declare-fun g_s19_25 () U)
(declare-fun g_s2_3 () U)
(declare-fun g_s20_24 () U)
(declare-fun g_s21_27 () U)
(declare-fun g_s22_26 () U)
(declare-fun g_s23_28 () U)
(declare-fun g_s24_29 () U)
(declare-fun g_s25_30 () U)
(declare-fun g_s26_31 () U)
(declare-fun g_s27_32 () U)
(declare-fun g_s28_33 () U)
(declare-fun g_s29_34 () U)
(declare-fun g_s3_4 () U)
(declare-fun g_s30_35 () U)
(declare-fun g_s31_36 () U)
(declare-fun g_s32_37 () U)
(declare-fun g_s33_38 () U)
(declare-fun g_s34_39 () U)
(declare-fun g_s35_40 () U)
(declare-fun g_s36_41 () U)
(declare-fun g_s37_43 () U)
(declare-fun g_s38_44 () U)
(declare-fun g_s39_45 () U)
(declare-fun g_s4_5 () U)
(declare-fun g_s40_46 () U)
(declare-fun g_s41_48 () U)
(declare-fun g_s42_49 () U)
(declare-fun g_s43_50 () U)
(declare-fun g_s44_51 () U)
(declare-fun g_s45_52 () U)
(declare-fun g_s46_53 () U)
(declare-fun g_s47_54 () U)
(declare-fun g_s48_55 () U)
(declare-fun g_s49_56 () U)
(declare-fun g_s5_6 () U)
(declare-fun g_s50_57 () U)
(declare-fun g_s51_58 () U)
(declare-fun g_s52_59 () U)
(declare-fun g_s53_60 () U)
(declare-fun g_s54_61 () U)
(declare-fun g_s55_62 () U)
(declare-fun g_s56_63 () U)
(declare-fun g_s57_64 () U)
(declare-fun g_s58_65 () U)
(declare-fun g_s59_66 () U)
(declare-fun g_s6_7 () U)
(declare-fun g_s60_67 () U)
(declare-fun g_s61_68 () U)
(declare-fun g_s62_69 () U)
(declare-fun g_s63_70 () U)
(declare-fun g_s64_71 () U)
(declare-fun g_s65_72 () U)
(declare-fun g_s66_73 () U)
(declare-fun g_s67_74 () U)
(declare-fun g_s68_75 () U)
(declare-fun g_s69_76 () U)
(declare-fun g_s7_8 () U)
(declare-fun g_s70_77 () U)
(declare-fun g_s71_78 () U)
(declare-fun g_s72_79 () U)
(declare-fun g_s73_80 () U)
(declare-fun g_s74_81 () U)
(declare-fun g_s75_82 () U)
(declare-fun g_s76_83 () U)
(declare-fun g_s77_84 () U)
(declare-fun g_s78_85 () U)
(declare-fun g_s79_86 () U)
(declare-fun g_s8_9 () U)
(declare-fun g_s80_87 () U)
(declare-fun g_s81_88 () U)
(declare-fun g_s82_89 () U)
(declare-fun g_s83_90 () U)
(declare-fun g_s84_91 () U)
(declare-fun g_s85_92 () U)
(declare-fun g_s86_93 () U)
(declare-fun g_s87_94 () U)
(declare-fun g_s88_95 () U)
(declare-fun g_s89_96 () U)
(declare-fun g_s9_11 () U)
(declare-fun g_s90_97 () U)
(declare-fun g_s91_98 () U)
(declare-fun g_s92_99 () U)
(declare-fun g_s97_115 () U)
(declare-fun g_s98_116 () U)
(declare-fun g_s99_117 () U)
(declare-fun e106 () U)
(declare-fun e107 () U)
(declare-fun e108 () U)
(declare-fun e100 () U)
(declare-fun e103 () U)
(declare-fun e101 () U)
(declare-fun e104 () U)
(declare-fun e102 () U)
(declare-fun e105 () U)
(declare-fun e109 () U)
(declare-fun e110 () U)
(declare-fun e111 () U)
(declare-fun e112 () U)
(declare-fun e113 () U)
(declare-fun e114 () U)
; Defines
(define-fun |def_B definitions| () Bool (and (= NAT (interval e0 MaxInt)) (= INT (interval MinInt MaxInt))))
(define-fun |def_ctx| () Bool (and (= g_s0_1 (SET (mapplet g_s2_3 g_s1_2))) (= g_s3_4 (SET (mapplet g_s8_9 (mapplet g_s7_8 (mapplet g_s6_7 (mapplet g_s5_6 g_s4_5)))))) (mem g_s9_11 g_s10_10) (mem g_s11_13 g_s12_12) (mem g_s13_15 g_s14_14) (mem g_s15_16 g_s14_14) (mem g_s16_17 g_s14_14) (= g_s9_11 e18) (= g_s11_13 e19) (= g_s13_15 e20) (and (|>=i| g_s15_16 e0) (|<=i| g_s15_16 g_s13_15)) (and (|>=i| g_s16_17 e0) (|<=i| g_s16_17 g_s13_15)) (not (= g_s15_16 g_s16_17)) (= g_s17_21 (SET (mapplet g_s16_17 g_s15_16))) (|<=i| g_s15_16 e22) (|<=i| g_s16_17 e22) (= g_s18_23 (SET (mapplet (mapplet FALSE g_s16_17) (mapplet TRUE g_s15_16)))) (mem g_s19_25 (|-->| (set_prod (set_prod (set_prod g_s10_10 (|-->| (interval e0 g_s20_24) g_s10_10)) g_s14_14) g_s10_10) g_s12_12)) (mem g_s21_27 (|-->| (set_prod (set_prod (set_prod g_s10_10 (|-->| (interval e0 g_s22_26) g_s10_10)) g_s14_14) g_s10_10) g_s12_12)) (mem g_s23_28 g_s10_10) (mem g_s24_29 g_s10_10) (not (= g_s23_28 g_s24_29)) (mem g_s25_30 NAT1) (mem g_s26_31 g_s10_10) (|<i| g_s26_31 (|-i| g_s9_11 g_s11_13)) (mem g_s27_32 g_s10_10) (= g_s27_32 (|+i| g_s26_31 g_s25_30)) (mem g_s28_33 g_s10_10) (mem g_s29_34 g_s10_10) (mem g_s30_35 NAT1) (mem g_s31_36 NAT1) (mem g_s25_30 NAT1) (mem g_s32_37 g_s10_10) (mem g_s33_38 g_s10_10) (mem g_s34_39 g_s10_10) (= g_s33_38 (|+i| g_s32_37 g_s30_35)) (= g_s34_39 (|+i| g_s32_37 g_s31_36)) (mem g_s35_40 g_s12_12) (mem g_s36_41 g_s10_10) (|<=i| g_s36_41 e42) (mem g_s37_43 NAT1) (mem g_s38_44 g_s10_10) (|<i| g_s38_44 (|-i| g_s9_11 g_s11_13)) (mem g_s39_45 g_s10_10) (= g_s39_45 (|+i| g_s38_44 g_s37_43)) (mem g_s40_46 g_s10_10) (|<=i| e47 g_s40_46) (mem g_s41_48 g_s10_10) (mem g_s42_49 g_s10_10) (mem g_s43_50 g_s10_10) (|<i| g_s43_50 (|-i| g_s9_11 g_s11_13)) (mem g_s44_51 g_s10_10) (mem g_s45_52 NAT1) (= g_s44_51 (|+i| g_s43_50 g_s45_52)) (mem g_s46_53 NATURAL1) (mem g_s47_54 g_s10_10) (= g_s47_54 (|+i| g_s43_50 g_s46_53)) (mem g_s48_55 g_s10_10) (mem g_s49_56 g_s10_10) (mem g_s50_57 g_s10_10) (mem g_s51_58 g_s10_10) (mem g_s52_59 g_s12_12) (|<i| (|*i| e22 g_s52_59) g_s11_13) (mem g_s53_60 NAT1) (mem g_s54_61 g_s12_12) (mem g_s55_62 g_s12_12) (= g_s55_62 (|+i| g_s54_61 g_s53_60)) (mem g_s56_63 g_s10_10) (mem g_s57_64 g_s10_10) (mem g_s58_65 g_s10_10) (mem g_s59_66 g_s10_10) (mem g_s60_67 g_s10_10) (mem g_s61_68 g_s10_10) (mem g_s62_69 g_s10_10) (mem g_s63_70 g_s10_10) (mem g_s64_71 g_s10_10) (mem g_s65_72 g_s10_10) (mem g_s66_73 (|-->| (set_prod g_s10_10 g_s14_14) g_s10_10)) (mem g_s67_74 (|-->| (set_prod g_s10_10 g_s14_14) g_s10_10)) (mem g_s68_75 (|-->| g_s10_10 g_s10_10)) (mem g_s69_76 (|-->| (set_prod g_s10_10 g_s10_10) g_s10_10)) (mem g_s70_77 (|-->| (set_prod g_s10_10 g_s10_10) g_s10_10)) (mem g_s71_78 (|-->| (set_prod g_s10_10 g_s10_10) g_s10_10)) (mem g_s72_79 (|-->| (set_prod g_s12_12 g_s14_14) g_s12_12)) (mem g_s73_80 (|-->| (set_prod g_s12_12 g_s14_14) g_s12_12)) (mem g_s74_81 (|-->| g_s12_12 g_s12_12)) (mem g_s75_82 (|-->| (set_prod g_s12_12 g_s12_12) g_s12_12)) (mem g_s76_83 (|-->| (set_prod g_s12_12 g_s12_12) g_s12_12)) (mem g_s77_84 (|-->| (set_prod g_s12_12 g_s12_12) g_s12_12)) (mem g_s78_85 (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14)) (mem g_s79_86 (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14)) (mem g_s80_87 (|-->| g_s14_14 g_s14_14)) (mem g_s81_88 (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14)) (mem g_s82_89 (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14)) (mem g_s83_90 (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14)) (mem g_s84_91 (|-->| (set_prod g_s10_10 g_s10_10) g_s10_10)) (mem g_s85_92 (|-->| (set_prod g_s10_10 g_s10_10) g_s10_10)) (mem g_s86_93 (|-->| (set_prod g_s10_10 g_s10_10) g_s10_10)) (mem g_s87_94 (|-->| (set_prod g_s12_12 g_s12_12) g_s12_12)) (mem g_s88_95 (|-->| (set_prod g_s12_12 g_s12_12) g_s12_12)) (mem g_s89_96 (|-->| (set_prod g_s12_12 g_s12_12) g_s12_12)) (mem g_s90_97 (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14)) (mem g_s91_98 (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14)) (mem g_s92_99 (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14)) (= g_s66_73 e100) (= g_s72_79 e101) (= g_s78_85 e102) (= g_s67_74 e103) (= g_s73_80 e104) (= g_s79_86 e105) (= g_s84_91 e106) (= g_s85_92 e107) (= g_s86_93 e108) (= g_s87_94 e109) (= g_s88_95 e110) (= g_s89_96 e111) (= g_s90_97 e112) (= g_s91_98 e113) (= g_s92_99 e114) (= g_s10_10 (interval e0 e18)) (= g_s12_12 (interval e0 e19)) (= g_s14_14 (interval e0 e20)) (mem g_s97_115 g_s10_10) (|<i| g_s97_115 g_s9_11)))
(define-fun |def_seext| () Bool (and (mem g_s98_116 g_s10_10) (mem g_s99_117 g_s10_10) (mem g_s100_118 g_s14_14) (or (= g_s100_118 e47) (= g_s100_118 e22)) (mem g_s101_119 g_s10_10) (mem g_s102_120 g_s10_10) (mem g_s103_121 g_s10_10) (mem g_s104_122 g_s10_10) (mem g_s105_123 g_s10_10) (mem g_s106_124 g_s10_10) (mem g_s107_125 (|-->| (interval e0 g_s22_26) g_s14_14)) (mem g_s108_126 g_s10_10) (mem g_s109_127 g_s10_10) (mem g_s110_128 g_s10_10) (mem g_s111_129 g_s10_10) (mem g_s112_130 g_s10_10) (mem g_s113_131 (|-->| (interval e0 e22) g_s14_14)) (mem g_s114_132 (|-->| (interval e0 e22) g_s14_14)) (mem g_s115_133 g_s12_12) (mem g_s116_134 (|-->| (interval e0 g_s97_115) g_s14_14)) (mem g_s18_23 (|+->| BOOL g_s14_14)) (mem g_s18_23 (|+->| BOOL g_s12_12)) (mem g_s18_23 (|+->| BOOL g_s10_10))))
(define-fun |def_mchcst| () Bool true)
(define-fun |def_aprp| () Bool true)
(define-fun |def_abs| () Bool true)
(define-fun |def_inv| () Bool  (mem g_s117$1_135 g_s10_10))
(define-fun |def_ass| () Bool true)
(define-fun |def_sets| () Bool true)
(define-fun |def_imlprp| () Bool true)
(define-fun |def_imprp| () Bool true)
(define-fun |def_imext| () Bool true)
; PO group 0 
(push 1)
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_mchcst|)
(assert |def_aprp|)
(assert |def_imlprp|)
(assert |def_imprp|)
(assert |def_imext|)
(assert |def_seext|)
; PO 1 in group 0
(assert (not (mem e0 g_s10_10)))
(check-sat)
(pop 1)
; PO group 1 
(push 1)
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_mchcst|)
(assert |def_aprp|)
(assert |def_imlprp|)
(assert |def_imprp|)
(assert |def_imext|)
(assert |def_seext|)
(assert |def_abs|)
(assert |def_inv|)
(assert |def_ass|)
(define-fun lh_1 () Bool (mem g_s121$1_136 g_s10_10))
(define-fun lh_2 () Bool (mem g_s122$1_137 g_s10_10))
(define-fun lh_3 () Bool (mem g_s123$1_138 g_s10_10))
; PO 1 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (mem g_s84_91 (|+->| (dom g_s84_91) (ran g_s84_91))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (mem (mapplet g_s117$1_135 g_s97_115) (dom g_s84_91)))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
(exit)