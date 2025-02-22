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
(declare-fun g_s10_11 () U)
(declare-fun g_s100_101 () U)
(declare-fun g_s101_102 () U)
(declare-fun g_s102_103 () U)
(declare-fun g_s103_104 () U)
(declare-fun g_s104_105 () U)
(declare-fun g_s105_106 () U)
(declare-fun g_s106_107 () U)
(declare-fun g_s107_108 () U)
(declare-fun g_s108_109 () U)
(declare-fun g_s109_110 () U)
(declare-fun g_s11_12 () U)
(declare-fun g_s110_111 () U)
(declare-fun g_s111_112 () U)
(declare-fun g_s112_113 () U)
(declare-fun g_s113_114 () U)
(declare-fun g_s114_115 () U)
(declare-fun g_s115_116 () U)
(declare-fun g_s116_117 () U)
(declare-fun g_s117_119 () U)
(declare-fun g_s118_118 () U)
(declare-fun g_s119_120 () U)
(declare-fun g_s12_13 () U)
(declare-fun g_s120_121 () U)
(declare-fun g_s121_122 () U)
(declare-fun g_s122_123 () U)
(declare-fun g_s123_124 () U)
(declare-fun g_s124_125 () U)
(declare-fun g_s125_126 () U)
(declare-fun g_s126_127 () U)
(declare-fun g_s127_128 () U)
(declare-fun g_s128_129 () U)
(declare-fun g_s129_130 () U)
(declare-fun g_s13_14 () U)
(declare-fun g_s130_131 () U)
(declare-fun g_s131_132 () U)
(declare-fun g_s132_134 () U)
(declare-fun g_s133_133 () U)
(declare-fun g_s134_135 () U)
(declare-fun g_s135_137 () U)
(declare-fun g_s136_136 () U)
(declare-fun g_s137_138 () U)
(declare-fun g_s138_139 () U)
(declare-fun g_s139_140 () U)
(declare-fun g_s14_15 () U)
(declare-fun g_s140_141 () U)
(declare-fun g_s141_142 () U)
(declare-fun g_s142_143 () U)
(declare-fun g_s146_144 () U)
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
(declare-fun g_s42_44 () U)
(declare-fun g_s43_43 () U)
(declare-fun g_s44_45 () U)
(declare-fun g_s45_46 () U)
(declare-fun g_s46_47 () U)
(declare-fun g_s47_49 () U)
(declare-fun g_s48_48 () U)
(declare-fun g_s49_50 () U)
(declare-fun g_s5_6 () U)
(declare-fun g_s50_51 () U)
(declare-fun g_s51_52 () U)
(declare-fun g_s52_53 () U)
(declare-fun g_s53_54 () U)
(declare-fun g_s54_55 () U)
(declare-fun g_s55_56 () U)
(declare-fun g_s56_57 () U)
(declare-fun g_s57_58 () U)
(declare-fun g_s58_59 () U)
(declare-fun g_s59_60 () U)
(declare-fun g_s6_7 () U)
(declare-fun g_s60_61 () U)
(declare-fun g_s61_62 () U)
(declare-fun g_s62_63 () U)
(declare-fun g_s63_64 () U)
(declare-fun g_s64_65 () U)
(declare-fun g_s65_66 () U)
(declare-fun g_s66_67 () U)
(declare-fun g_s67_68 () U)
(declare-fun g_s68_69 () U)
(declare-fun g_s69_70 () U)
(declare-fun g_s7_8 () U)
(declare-fun g_s70_71 () U)
(declare-fun g_s71_72 () U)
(declare-fun g_s72_73 () U)
(declare-fun g_s73_74 () U)
(declare-fun g_s74_75 () U)
(declare-fun g_s75_77 () U)
(declare-fun g_s76_76 () U)
(declare-fun g_s77_78 () U)
(declare-fun g_s78_79 () U)
(declare-fun g_s79_80 () U)
(declare-fun g_s8_9 () U)
(declare-fun g_s80_81 () U)
(declare-fun g_s81_82 () U)
(declare-fun g_s82_83 () U)
(declare-fun g_s83_84 () U)
(declare-fun g_s84_85 () U)
(declare-fun g_s85_86 () U)
(declare-fun g_s86_87 () U)
(declare-fun g_s87_88 () U)
(declare-fun g_s88_89 () U)
(declare-fun g_s89_90 () U)
(declare-fun g_s9_10 () U)
(declare-fun g_s90_91 () U)
(declare-fun g_s91_92 () U)
(declare-fun g_s92_93 () U)
(declare-fun g_s93_94 () U)
(declare-fun g_s94_95 () U)
(declare-fun g_s95_96 () U)
(declare-fun g_s96_97 () U)
(declare-fun g_s97_98 () U)
(declare-fun g_s98_99 () U)
(declare-fun g_s99_100 () U)
; Defines
(define-fun |def_B definitions| () Bool (and (= NAT (interval e0 MaxInt)) (= INT (interval MinInt MaxInt))))
(define-fun |def_ctx| () Bool (and (= g_s0_1 (SET (mapplet g_s2_3 g_s1_2))) (= g_s3_4 (SET (mapplet g_s6_7 (mapplet g_s5_6 g_s4_5)))) (= g_s7_8 (SET (mapplet g_s11_12 (mapplet g_s10_11 (mapplet g_s9_10 g_s8_9))))) (= g_s12_13 (SET (mapplet g_s17_18 (mapplet g_s16_17 (mapplet g_s15_16 (mapplet g_s14_15 g_s13_14)))))) (= g_s18_19 (SET (mapplet g_s24_25 (mapplet g_s23_24 (mapplet g_s22_23 (mapplet g_s21_22 (mapplet g_s20_21 g_s19_20))))))) (= g_s25_26 (SET (mapplet g_s32_33 (mapplet g_s31_32 (mapplet g_s30_31 (mapplet g_s29_30 (mapplet g_s28_29 (mapplet g_s27_28 g_s26_27)))))))) (not (= g_s33_34 empty)) (not (= g_s34_35 empty)) (not (= g_s35_36 empty)) (not (= g_s36_37 empty)) (not (= g_s37_38 empty)) (= g_s38_39 (SET (mapplet g_s41_42 (mapplet g_s40_41 g_s39_40)))) (mem g_s42_44 g_s43_43) (|>i| g_s42_44 e0) (mem g_s44_45 g_s43_43) (|>i| g_s44_45 e0) (mem g_s45_46 g_s43_43) (|>i| g_s45_46 e0) (mem g_s46_47 g_s43_43) (|>i| g_s46_47 e0) (mem g_s47_49 g_s48_48) (mem g_s49_50 g_s48_48) (mem g_s50_51 g_s48_48) (mem g_s51_52 g_s43_43) (|>i| g_s51_52 e0) (mem g_s52_53 g_s48_48) (mem g_s53_54 g_s43_43) (|>i| g_s53_54 e0) (mem g_s54_55 g_s43_43) (|>i| g_s54_55 e0) (mem g_s55_56 g_s43_43) (|>i| g_s55_56 e0) (mem g_s56_57 g_s43_43) (|>i| g_s56_57 e0) (mem g_s57_58 g_s43_43) (|>i| g_s57_58 e0) (mem g_s58_59 g_s43_43) (|>i| g_s58_59 e0) (mem g_s59_60 g_s43_43) (|>i| g_s59_60 e0) (mem g_s60_61 g_s43_43) (|>i| g_s60_61 e0) (mem g_s61_62 g_s43_43) (|>i| g_s61_62 e0) (mem g_s62_63 g_s43_43) (|>i| g_s62_63 e0) (mem g_s63_64 g_s43_43) (|>i| g_s63_64 e0) (mem g_s64_65 g_s43_43) (|>i| g_s64_65 e0) (|<i| g_s55_56 g_s64_65) (mem g_s65_66 g_s43_43) (|>i| g_s65_66 e0) (mem g_s66_67 g_s43_43) (|>i| g_s66_67 e0) (mem g_s67_68 g_s43_43) (|>i| g_s67_68 e0) (mem g_s68_69 g_s43_43) (|>i| g_s68_69 e0) (mem g_s69_70 g_s43_43) (|>i| g_s69_70 e0) (mem g_s70_71 g_s43_43) (|>i| g_s70_71 e0) (mem g_s71_72 g_s43_43) (|>i| g_s71_72 e0) (mem g_s72_73 g_s43_43) (|>i| g_s72_73 e0) (mem g_s73_74 g_s43_43) (|>i| g_s73_74 e0) (mem g_s74_75 g_s43_43) (|>i| g_s74_75 e0) (mem g_s75_77 g_s76_76) (mem g_s75_77 g_s77_78) (mem g_s78_79 g_s43_43) (|>i| g_s78_79 e0) (mem g_s79_80 g_s48_48) (mem g_s80_81 g_s48_48) (mem g_s81_82 g_s48_48) (mem g_s82_83 g_s48_48) (mem g_s83_84 g_s48_48) (mem g_s84_85 g_s48_48) (mem g_s85_86 g_s48_48) (mem g_s86_87 g_s48_48) (mem g_s87_88 g_s43_43) (mem g_s88_89 g_s48_48) (mem g_s89_90 g_s48_48) (mem g_s90_91 g_s48_48) (mem g_s91_92 g_s48_48) (mem g_s92_93 g_s48_48) (mem g_s93_94 g_s48_48) (mem g_s94_95 g_s48_48) (mem g_s95_96 g_s48_48) (mem g_s96_97 g_s48_48) (mem g_s97_98 g_s48_48) (mem g_s98_99 g_s43_43) (|>i| g_s98_99 e0) (mem g_s99_100 g_s43_43) (|>=i| g_s99_100 e0) (mem (|+i| g_s98_99 g_s99_100) g_s43_43) (mem g_s100_101 g_s48_48) (mem g_s101_102 g_s48_48) (mem g_s102_103 g_s43_43) (mem g_s103_104 g_s43_43) (mem g_s104_105 g_s43_43) (= g_s48_48 NATURAL) (mem g_s105_106 g_s43_43) (= g_s105_106 e0) (subset g_s106_107 g_s33_34) (mem g_s107_108 g_s33_34) (not (mem g_s107_108 g_s106_107)) (subset g_s108_109 g_s34_35) (mem g_s109_110 g_s34_35) (not (mem g_s109_110 g_s108_109)) (subset g_s110_111 g_s35_36) (mem g_s111_112 g_s35_36) (not (mem g_s111_112 g_s110_111)) (mem g_s112_113 (|+->| NAT g_s35_36)) (mem g_s112_113 (perm g_s110_111)) (= g_s113_114 INT) (= g_s114_115 NAT) (mem g_s115_116 g_s113_114) (not (mem g_s115_116 g_s114_115)) (mem g_s116_117 g_s113_114) (mem g_s116_117 g_s114_115) (mem g_s117_119 (|>->| g_s110_111 g_s118_118)) (subset g_s119_120 g_s36_37) (mem g_s120_121 g_s36_37) (not (mem g_s120_121 g_s119_120)) (mem g_s121_122 (|+->| NAT g_s36_37)) (mem g_s121_122 (perm g_s119_120)) (subset g_s122_123 g_s37_38) (mem g_s123_124 g_s37_38) (not (mem g_s123_124 g_s122_123)) (mem g_s124_125 (|+->| NAT g_s37_38)) (mem g_s124_125 (perm g_s122_123))))
(define-fun |def_seext| () Bool (and (subset g_s125_126 g_s110_111) (mem g_s126_127 (|-->| g_s110_111 INTEGER)) (subset g_s127_128 g_s110_111) (subset g_s128_129 g_s110_111) (subset g_s129_130 g_s110_111) (mem g_s130_131 (|+->| g_s110_111 g_s106_107)) (mem g_s131_132 (|+->| g_s110_111 g_s77_78)) (mem g_s132_134 (|+->| g_s110_111 g_s133_133)) (mem g_s134_135 (|+->| g_s110_111 g_s77_78)) (mem g_s135_137 (|<->| g_s110_111 g_s136_136)) (mem g_s137_138 (|+->| g_s110_111 g_s114_115)) (subset g_s138_139 g_s110_111)))
(define-fun |def_lprp| () Bool true)
(define-fun |def_inprp| () Bool true)
(define-fun |def_inext| () Bool true)
(define-fun |def_inv| () Bool (and (mem g_s139_140 (|-->| g_s110_111 g_s0_1)) (mem g_s140_141 (|-->| g_s110_111 g_s48_48)) (subset g_s141_142 g_s110_111) (subset g_s142_143 g_s110_111)))
(define-fun |def_ass| () Bool true)
(define-fun |def_cst| () Bool true)
(define-fun |def_sets| () Bool true)
; PO group 0 
(push 1)
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_cst|)
(assert |def_lprp|)
(assert |def_inprp|)
(assert |def_inext|)
(assert |def_seext|)
; PO 1 in group 0
(push 1)
(assert (not (mem (set_prod g_s110_111 (SET e0)) (|-->| g_s110_111 g_s48_48))))
(check-sat)
(pop 1)
; PO 2 in group 0
(push 1)
(assert (not (mem (set_prod g_s110_111 (SET g_s1_2)) (|-->| g_s110_111 g_s0_1))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 0
(push 1)
(assert (not (subset empty g_s110_111)))
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
(assert (mem g_s146_144 g_s35_36))
(assert (mem g_s146_144 g_s110_111))
; PO 1 in group 1
(push 1)
(assert (not (subset (set_diff g_s142_143 (SET g_s146_144)) g_s110_111)))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 1
(push 1)
(assert (not (subset (set_diff g_s141_142 (SET g_s146_144)) g_s110_111)))
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
(assert (mem g_s146_144 g_s35_36))
(assert (mem g_s146_144 g_s110_111))
(assert (= (apply g_s139_140 g_s146_144) g_s1_2))
(assert (mem g_s146_144 g_s127_128))
(assert (mem g_s146_144 (dom g_s137_138)))
(assert (= (apply g_s137_138 g_s146_144) g_s116_117))
; PO 1 in group 2
(push 1)
(assert (not (mem (|<+| g_s139_140 (SET (mapplet g_s146_144 g_s2_3))) (|-->| g_s110_111 g_s0_1))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 2
(push 1)
(assert (not (mem (|<+| g_s140_141 (SET (mapplet g_s146_144 g_s81_82))) (|-->| g_s110_111 g_s48_48))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 2
(push 1)
(assert (not (subset (binary_union g_s142_143 (SET g_s146_144)) g_s110_111)))
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
(assert (mem g_s146_144 g_s35_36))
(assert (mem g_s146_144 g_s110_111))
(assert (= (apply g_s139_140 g_s146_144) g_s2_3))
(assert (or (not (mem g_s146_144 g_s125_126)) (|<=i| (apply g_s140_141 g_s146_144) g_s78_79)))
; PO 1 in group 3
(push 1)
(assert (not (mem (|<+| g_s139_140 (SET (mapplet g_s146_144 g_s1_2))) (|-->| g_s110_111 g_s0_1))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 3
(push 1)
(assert (not (subset (binary_union g_s141_142 (SET g_s146_144)) g_s110_111)))
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
(assert (mem g_s146_144 g_s35_36))
(assert (mem g_s146_144 g_s110_111))
(assert (= (apply g_s139_140 g_s146_144) g_s2_3))
(assert (not (or (not (mem g_s146_144 g_s125_126)) (|<=i| (apply g_s140_141 g_s146_144) g_s78_79))))
(assert (mem g_s146_144 g_s127_128))
(assert (mem g_s146_144 (dom g_s137_138)))
(assert (= (apply g_s137_138 g_s146_144) g_s116_117))
; PO 1 in group 4
(assert (not (subset (binary_union g_s142_143 (SET g_s146_144)) g_s110_111)))
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
(assert (mem g_s146_144 g_s35_36))
(assert (mem g_s146_144 g_s110_111))
(assert (= (apply g_s139_140 g_s146_144) g_s2_3))
(assert (not (or (not (mem g_s146_144 g_s125_126)) (|<=i| (apply g_s140_141 g_s146_144) g_s78_79))))
(assert (or (mem g_s146_144 g_s127_128) (mem g_s146_144 g_s129_130) (mem g_s146_144 g_s128_129)))
; PO 1 in group 5
(assert (not (mem (|<+| g_s140_141 (SET (mapplet g_s146_144 g_s81_82))) (|-->| g_s110_111 g_s48_48))))
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
(assert (mem g_s146_144 g_s35_36))
(assert (mem g_s146_144 g_s110_111))
(assert (= (apply g_s139_140 g_s146_144) g_s2_3))
(assert (not (or (not (mem g_s146_144 g_s125_126)) (|<=i| (apply g_s140_141 g_s146_144) g_s78_79))))
(assert (not (or (mem g_s146_144 g_s127_128) (mem g_s146_144 g_s129_130) (mem g_s146_144 g_s128_129))))
; PO 1 in group 6
(assert (not (mem (|<+| g_s140_141 (SET (mapplet g_s146_144 (|-i| (apply g_s140_141 g_s146_144) g_s78_79)))) (|-->| g_s110_111 g_s48_48))))
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
(define-fun lh_1 () Bool (mem g_s146_144 g_s35_36))
(define-fun lh_2 () Bool (mem g_s146_144 g_s110_111))
(define-fun lh_3 () Bool (= (apply g_s139_140 g_s146_144) g_s1_2))
(define-fun lh_4 () Bool (mem g_s146_144 g_s127_128))
(define-fun lh_5 () Bool (mem g_s146_144 (dom g_s137_138)))
; PO 1 in group 7
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem g_s139_140 (|+->| (dom g_s139_140) (ran g_s139_140))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 7
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem g_s146_144 (dom g_s139_140)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 7
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5) (mem g_s137_138 (|+->| (dom g_s137_138) (ran g_s137_138))))))
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
(define-fun lh_1 () Bool (mem g_s146_144 g_s35_36))
(define-fun lh_2 () Bool (mem g_s146_144 g_s110_111))
; PO 1 in group 8
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem g_s139_140 (|+->| (dom g_s139_140) (ran g_s139_140))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 8
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem g_s146_144 (dom g_s139_140)))))
(set-info :status unknown)
(check-sat)
(pop 1)
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
(assert (mem g_s146_144 g_s35_36))
(assert (mem g_s146_144 g_s110_111))
(assert (= (apply g_s139_140 g_s146_144) g_s1_2))
(define-fun lh_1 () Bool (mem g_s146_144 g_s127_128))
(define-fun lh_2 () Bool (mem g_s146_144 (dom g_s137_138)))
; PO 1 in group 9
(assert (not (=> (and lh_1 lh_2) (mem g_s137_138 (|+->| (dom g_s137_138) (ran g_s137_138))))))
(set-info :status unknown)
(check-sat)
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
(define-fun lh_1 () Bool (mem g_s146_144 g_s35_36))
(define-fun lh_2 () Bool (mem g_s146_144 g_s110_111))
(define-fun lh_3 () Bool (= (apply g_s139_140 g_s146_144) g_s2_3))
(define-fun lh_4 () Bool (not (not (mem g_s146_144 g_s125_126))))
; PO 1 in group 10
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem g_s139_140 (|+->| (dom g_s139_140) (ran g_s139_140))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 10
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem g_s146_144 (dom g_s139_140)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 10
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem g_s146_144 (dom g_s140_141)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 10
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem g_s140_141 (|+->| (dom g_s140_141) (ran g_s140_141))))))
(set-info :status unknown)
(check-sat)
(pop 1)
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
(define-fun lh_1 () Bool (mem g_s146_144 g_s35_36))
(define-fun lh_2 () Bool (mem g_s146_144 g_s110_111))
(define-fun lh_3 () Bool (= (apply g_s139_140 g_s146_144) g_s2_3))
(define-fun lh_4 () Bool (not (not (mem g_s146_144 g_s125_126))))
(define-fun lh_5 () Bool (not (or (not (mem g_s146_144 g_s125_126)) (|<=i| (apply g_s140_141 g_s146_144) g_s78_79))))
(define-fun lh_6 () Bool (mem g_s146_144 g_s127_128))
(define-fun lh_7 () Bool (mem g_s146_144 (dom g_s137_138)))
; PO 1 in group 11
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem g_s139_140 (|+->| (dom g_s139_140) (ran g_s139_140))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 11
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem g_s146_144 (dom g_s139_140)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 11
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem g_s146_144 (dom g_s140_141)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 11
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem g_s140_141 (|+->| (dom g_s140_141) (ran g_s140_141))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 5 in group 11
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_5 lh_6 lh_7) (mem g_s137_138 (|+->| (dom g_s137_138) (ran g_s137_138))))))
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
(define-fun lh_1 () Bool (mem g_s146_144 g_s35_36))
(define-fun lh_2 () Bool (mem g_s146_144 g_s110_111))
(define-fun lh_3 () Bool (= (apply g_s139_140 g_s146_144) g_s2_3))
(define-fun lh_4 () Bool (not (not (mem g_s146_144 g_s125_126))))
; PO 1 in group 12
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem g_s139_140 (|+->| (dom g_s139_140) (ran g_s139_140))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 12
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem g_s146_144 (dom g_s139_140)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 12
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem g_s146_144 (dom g_s140_141)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 12
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem g_s140_141 (|+->| (dom g_s140_141) (ran g_s140_141))))))
(set-info :status unknown)
(check-sat)
(pop 1)
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
(assert (mem g_s146_144 g_s35_36))
(assert (mem g_s146_144 g_s110_111))
(assert (= (apply g_s139_140 g_s146_144) g_s2_3))
(assert (not (or (not (mem g_s146_144 g_s125_126)) (|<=i| (apply g_s140_141 g_s146_144) g_s78_79))))
(define-fun lh_1 () Bool (mem g_s146_144 g_s127_128))
(define-fun lh_2 () Bool (mem g_s146_144 (dom g_s137_138)))
; PO 1 in group 13
(assert (not (=> (and lh_1 lh_2) (mem g_s137_138 (|+->| (dom g_s137_138) (ran g_s137_138))))))
(set-info :status unknown)
(check-sat)
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
(define-fun lh_1 () Bool (mem g_s146_144 g_s35_36))
(define-fun lh_2 () Bool (mem g_s146_144 g_s110_111))
(define-fun lh_3 () Bool (= (apply g_s139_140 g_s146_144) g_s2_3))
(define-fun lh_4 () Bool (not (not (mem g_s146_144 g_s125_126))))
; PO 1 in group 14
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem g_s139_140 (|+->| (dom g_s139_140) (ran g_s139_140))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 14
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem g_s146_144 (dom g_s139_140)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 14
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem g_s146_144 (dom g_s140_141)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 14
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem g_s140_141 (|+->| (dom g_s140_141) (ran g_s140_141))))))
(set-info :status unknown)
(check-sat)
(pop 1)
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
(define-fun lh_1 () Bool (mem g_s146_144 g_s35_36))
(define-fun lh_2 () Bool (mem g_s146_144 g_s110_111))
(define-fun lh_3 () Bool (= (apply g_s139_140 g_s146_144) g_s2_3))
(define-fun lh_4 () Bool (not (not (mem g_s146_144 g_s125_126))))
; PO 1 in group 15
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem g_s139_140 (|+->| (dom g_s139_140) (ran g_s139_140))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 15
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem g_s146_144 (dom g_s139_140)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 15
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem g_s146_144 (dom g_s140_141)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 15
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem g_s140_141 (|+->| (dom g_s140_141) (ran g_s140_141))))))
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
(assert (mem g_s146_144 g_s35_36))
(assert (mem g_s146_144 g_s110_111))
(assert (= (apply g_s139_140 g_s146_144) g_s2_3))
(assert (not (or (not (mem g_s146_144 g_s125_126)) (|<=i| (apply g_s140_141 g_s146_144) g_s78_79))))
(assert (not (or (mem g_s146_144 g_s127_128) (mem g_s146_144 g_s129_130) (mem g_s146_144 g_s128_129))))
; PO 1 in group 16
(push 1)
(assert (not (mem g_s146_144 (dom g_s140_141))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 16
(push 1)
(assert (not (mem g_s140_141 (|+->| (dom g_s140_141) (ran g_s140_141)))))
(set-info :status unknown)
(check-sat)
(pop 1)
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
(define-fun lh_1 () Bool (mem g_s146_144 g_s35_36))
(define-fun lh_2 () Bool (mem g_s146_144 g_s110_111))
(define-fun lh_3 () Bool (= (apply g_s139_140 g_s146_144) g_s2_3))
(define-fun lh_4 () Bool (not (not (mem g_s146_144 g_s125_126))))
; PO 1 in group 17
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem g_s139_140 (|+->| (dom g_s139_140) (ran g_s139_140))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 17
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem g_s146_144 (dom g_s139_140)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 17
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem g_s146_144 (dom g_s140_141)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 17
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem g_s140_141 (|+->| (dom g_s140_141) (ran g_s140_141))))))
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
(define-fun lh_1 () Bool (mem g_s146_144 g_s35_36))
(define-fun lh_2 () Bool (mem g_s146_144 g_s110_111))
; PO 1 in group 18
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem g_s139_140 (|+->| (dom g_s139_140) (ran g_s139_140))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 18
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem g_s146_144 (dom g_s139_140)))))
(set-info :status unknown)
(check-sat)
(pop 1)
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
(assert (mem g_s146_144 g_s35_36))
(assert (mem g_s146_144 g_s110_111))
(assert (= (apply g_s139_140 g_s146_144) g_s2_3))
(define-fun lh_1 () Bool (not (not (mem g_s146_144 g_s125_126))))
; PO 1 in group 19
(push 1)
(assert (not (=> lh_1 (mem g_s146_144 (dom g_s140_141)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 19
(push 1)
(assert (not (=> lh_1 (mem g_s140_141 (|+->| (dom g_s140_141) (ran g_s140_141))))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 20 
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
(assert (mem g_s146_144 g_s35_36))
(assert (mem g_s146_144 g_s110_111))
; PO 1 in group 20
(push 1)
(assert (not (mem g_s139_140 (|+->| (dom g_s139_140) (ran g_s139_140)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 20
(push 1)
(assert (not (mem g_s146_144 (dom g_s139_140))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 21 
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
(assert (mem g_s146_144 g_s35_36))
(assert (mem g_s146_144 g_s110_111))
; PO 1 in group 21
(push 1)
(assert (not (mem g_s139_140 (|+->| (dom g_s139_140) (ran g_s139_140)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 21
(push 1)
(assert (not (mem g_s146_144 (dom g_s139_140))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
(exit)