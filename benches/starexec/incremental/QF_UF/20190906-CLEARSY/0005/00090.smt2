(set-info :smt-lib-version 2.6)
(set-logic UF)
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
(declare-fun e93 () U)
(declare-fun e22 () U)
(declare-fun e125 () U)
(declare-fun e124 () U)
(declare-fun e20 () U)
(declare-fun e122 () U)
(declare-fun e88 () U)
(declare-fun e172 () U)
(declare-fun e171 () U)
(declare-fun e169 () U)
(declare-fun e170 () U)
(declare-fun e19 () U)
(declare-fun g_s0_1 () U)
(declare-fun g_s1_2 () U)
(declare-fun g_s10_10 () U)
(declare-fun g_s100_118 () U)
(declare-fun g_s101_119 () U)
(declare-fun g_s102_120 () U)
(declare-fun g_s103_121 () U)
(declare-fun g_s104_123 () U)
(declare-fun g_s105_126 () U)
(declare-fun g_s106_127 () U)
(declare-fun g_s107_128 () U)
(declare-fun g_s108_129 () U)
(declare-fun g_s109_130 () U)
(declare-fun g_s11_13 () U)
(declare-fun g_s110_131 () U)
(declare-fun g_s111_132 () U)
(declare-fun g_s112_133 () U)
(declare-fun g_s113_134 () U)
(declare-fun g_s114_135 () U)
(declare-fun g_s115_136 () U)
(declare-fun g_s116_137 () U)
(declare-fun g_s117_138 () U)
(declare-fun g_s118_139 () U)
(declare-fun g_s119_140 () U)
(declare-fun g_s12_12 () U)
(declare-fun g_s120_141 () U)
(declare-fun g_s121_142 () U)
(declare-fun g_s122_143 () U)
(declare-fun g_s123_144 () U)
(declare-fun g_s124_145 () U)
(declare-fun g_s125_146 () U)
(declare-fun g_s126_147 () U)
(declare-fun g_s127_148 () U)
(declare-fun g_s128_149 () U)
(declare-fun g_s129_150 () U)
(declare-fun g_s13_15 () U)
(declare-fun g_s130_151 () U)
(declare-fun g_s131_152 () U)
(declare-fun g_s132_153 () U)
(declare-fun g_s133_154 () U)
(declare-fun g_s134_155 () U)
(declare-fun g_s135_156 () U)
(declare-fun g_s136_157 () U)
(declare-fun g_s136$1_162 () U)
(declare-fun g_s137_158 () U)
(declare-fun g_s137$1_164 () U)
(declare-fun g_s138_159 () U)
(declare-fun g_s138$1_161 () U)
(declare-fun g_s139_160 () U)
(declare-fun g_s139$1_163 () U)
(declare-fun g_s14_14 () U)
(declare-fun g_s140$1_165 () U)
(declare-fun g_s146$1_166 () U)
(declare-fun g_s147$1_167 () U)
(declare-fun g_s148$1_168 () U)
(declare-fun g_s15_16 () U)
(declare-fun g_s16_17 () U)
(declare-fun g_s17_21 () U)
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
(declare-fun g_s3_4 () U)
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
(declare-fun g_s4_5 () U)
(declare-fun g_s40_45 () U)
(declare-fun g_s41_46 () U)
(declare-fun g_s42_47 () U)
(declare-fun g_s43_48 () U)
(declare-fun g_s44_49 () U)
(declare-fun g_s45_50 () U)
(declare-fun g_s5_6 () U)
(declare-fun g_s50_67 () U)
(declare-fun g_s51_66 () U)
(declare-fun g_s52_69 () U)
(declare-fun g_s53_68 () U)
(declare-fun g_s54_70 () U)
(declare-fun g_s55_71 () U)
(declare-fun g_s56_72 () U)
(declare-fun g_s57_73 () U)
(declare-fun g_s58_74 () U)
(declare-fun g_s59_75 () U)
(declare-fun g_s6_7 () U)
(declare-fun g_s60_76 () U)
(declare-fun g_s61_77 () U)
(declare-fun g_s62_78 () U)
(declare-fun g_s63_79 () U)
(declare-fun g_s64_80 () U)
(declare-fun g_s65_81 () U)
(declare-fun g_s66_82 () U)
(declare-fun g_s67_83 () U)
(declare-fun g_s68_84 () U)
(declare-fun g_s69_85 () U)
(declare-fun g_s7_8 () U)
(declare-fun g_s70_86 () U)
(declare-fun g_s71_87 () U)
(declare-fun g_s72_89 () U)
(declare-fun g_s73_90 () U)
(declare-fun g_s74_91 () U)
(declare-fun g_s75_92 () U)
(declare-fun g_s76_94 () U)
(declare-fun g_s77_95 () U)
(declare-fun g_s78_96 () U)
(declare-fun g_s79_97 () U)
(declare-fun g_s8_9 () U)
(declare-fun g_s80_98 () U)
(declare-fun g_s81_99 () U)
(declare-fun g_s82_100 () U)
(declare-fun g_s83_101 () U)
(declare-fun g_s84_102 () U)
(declare-fun g_s85_103 () U)
(declare-fun g_s86_104 () U)
(declare-fun g_s87_105 () U)
(declare-fun g_s88_106 () U)
(declare-fun g_s89_107 () U)
(declare-fun g_s9_11 () U)
(declare-fun g_s90_108 () U)
(declare-fun g_s91_109 () U)
(declare-fun g_s92_110 () U)
(declare-fun g_s93_111 () U)
(declare-fun g_s94_112 () U)
(declare-fun g_s95_113 () U)
(declare-fun g_s96_114 () U)
(declare-fun g_s97_115 () U)
(declare-fun g_s98_116 () U)
(declare-fun g_s99_117 () U)
(declare-fun e57 () U)
(declare-fun e58 () U)
(declare-fun e59 () U)
(declare-fun e51 () U)
(declare-fun e54 () U)
(declare-fun e52 () U)
(declare-fun e55 () U)
(declare-fun e53 () U)
(declare-fun e56 () U)
(declare-fun e60 () U)
(declare-fun e61 () U)
(declare-fun e62 () U)
(declare-fun e63 () U)
(declare-fun e64 () U)
(declare-fun e65 () U)
; Defines
(define-fun |def_B definitions| () Bool (and (= NAT (interval e0 MaxInt)) (= INT (interval MinInt MaxInt))))
(define-fun |def_ctx| () Bool (and (= g_s0_1 (SET (mapplet g_s2_3 g_s1_2))) (= g_s3_4 (SET (mapplet g_s8_9 (mapplet g_s7_8 (mapplet g_s6_7 (mapplet g_s5_6 g_s4_5)))))) (mem g_s9_11 g_s10_10) (mem g_s11_13 g_s12_12) (mem g_s13_15 g_s14_14) (mem g_s15_16 g_s14_14) (mem g_s16_17 g_s14_14) (= g_s9_11 e18) (= g_s11_13 e19) (= g_s13_15 e20) (and (|>=i| g_s15_16 e0) (|<=i| g_s15_16 g_s13_15)) (and (|>=i| g_s16_17 e0) (|<=i| g_s16_17 g_s13_15)) (not (= g_s15_16 g_s16_17)) (= g_s17_21 (SET (mapplet g_s16_17 g_s15_16))) (|<=i| g_s15_16 e22) (|<=i| g_s16_17 e22) (= g_s18_23 (SET (mapplet (mapplet FALSE g_s16_17) (mapplet TRUE g_s15_16)))) (= g_s10_10 (interval e0 e18)) (= g_s12_12 (interval e0 e19)) (= g_s14_14 (interval e0 e20)) (mem g_s19_24 (|-->| (set_prod g_s10_10 g_s14_14) g_s10_10)) (mem g_s20_25 (|-->| (set_prod g_s10_10 g_s14_14) g_s10_10)) (mem g_s21_26 (|-->| g_s10_10 g_s10_10)) (mem g_s22_27 (|-->| (set_prod g_s10_10 g_s10_10) g_s10_10)) (mem g_s23_28 (|-->| (set_prod g_s10_10 g_s10_10) g_s10_10)) (mem g_s24_29 (|-->| (set_prod g_s10_10 g_s10_10) g_s10_10)) (mem g_s25_30 (|-->| (set_prod g_s12_12 g_s14_14) g_s12_12)) (mem g_s26_31 (|-->| (set_prod g_s12_12 g_s14_14) g_s12_12)) (mem g_s27_32 (|-->| g_s12_12 g_s12_12)) (mem g_s28_33 (|-->| (set_prod g_s12_12 g_s12_12) g_s12_12)) (mem g_s29_34 (|-->| (set_prod g_s12_12 g_s12_12) g_s12_12)) (mem g_s30_35 (|-->| (set_prod g_s12_12 g_s12_12) g_s12_12)) (mem g_s31_36 (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14)) (mem g_s32_37 (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14)) (mem g_s33_38 (|-->| g_s14_14 g_s14_14)) (mem g_s34_39 (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14)) (mem g_s35_40 (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14)) (mem g_s36_41 (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14)) (mem g_s37_42 (|-->| (set_prod g_s10_10 g_s10_10) g_s10_10)) (mem g_s38_43 (|-->| (set_prod g_s10_10 g_s10_10) g_s10_10)) (mem g_s39_44 (|-->| (set_prod g_s10_10 g_s10_10) g_s10_10)) (mem g_s40_45 (|-->| (set_prod g_s12_12 g_s12_12) g_s12_12)) (mem g_s41_46 (|-->| (set_prod g_s12_12 g_s12_12) g_s12_12)) (mem g_s42_47 (|-->| (set_prod g_s12_12 g_s12_12) g_s12_12)) (mem g_s43_48 (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14)) (mem g_s44_49 (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14)) (mem g_s45_50 (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14)) (= g_s19_24 e51) (= g_s25_30 e52) (= g_s31_36 e53) (= g_s20_25 e54) (= g_s26_31 e55) (= g_s32_37 e56) (= g_s37_42 e57) (= g_s38_43 e58) (= g_s39_44 e59) (= g_s40_45 e60) (= g_s41_46 e61) (= g_s42_47 e62) (= g_s43_48 e63) (= g_s44_49 e64) (= g_s45_50 e65) (mem g_s50_67 (|-->| (set_prod (set_prod (set_prod g_s10_10 (|-->| (interval e0 g_s51_66) g_s10_10)) g_s14_14) g_s10_10) g_s12_12)) (mem g_s52_69 (|-->| (set_prod (set_prod (set_prod g_s10_10 (|-->| (interval e0 g_s53_68) g_s10_10)) g_s14_14) g_s10_10) g_s12_12)) (mem g_s54_70 (|-->| (set_prod g_s10_10 g_s10_10) g_s10_10)) (= (apply g_s54_70 (mapplet e0 e0)) e0) (mem g_s55_71 (|-->| (set_prod g_s12_12 g_s12_12) g_s12_12)) (mem g_s56_72 (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14)) (mem g_s57_73 (|-->| (set_prod g_s10_10 g_s10_10) g_s10_10)) (mem g_s58_74 g_s10_10) (mem g_s59_75 g_s10_10) (not (= g_s58_74 g_s59_75)) (mem g_s60_76 NAT1) (mem g_s61_77 g_s10_10) (|<i| g_s61_77 (|-i| g_s9_11 g_s11_13)) (mem g_s62_78 g_s10_10) (= g_s62_78 (|+i| g_s61_77 g_s60_76)) (mem g_s63_79 g_s10_10) (mem g_s64_80 g_s10_10) (mem g_s65_81 NAT1) (mem g_s66_82 NAT1) (mem g_s60_76 NAT1) (mem g_s67_83 g_s10_10) (mem g_s68_84 g_s10_10) (mem g_s69_85 g_s10_10) (= g_s68_84 (|+i| g_s67_83 g_s65_81)) (= g_s69_85 (|+i| g_s67_83 g_s66_82)) (mem g_s70_86 g_s12_12) (mem g_s71_87 g_s10_10) (|<=i| g_s71_87 e88) (mem g_s72_89 NAT1) (mem g_s73_90 g_s10_10) (|<i| g_s73_90 (|-i| g_s9_11 g_s11_13)) (mem g_s74_91 g_s10_10) (= g_s74_91 (|+i| g_s73_90 g_s72_89)) (mem g_s75_92 g_s10_10) (|<=i| e93 g_s75_92) (mem g_s76_94 g_s10_10) (mem g_s77_95 g_s10_10) (mem g_s78_96 g_s10_10) (|<i| g_s78_96 (|-i| g_s9_11 g_s11_13)) (mem g_s79_97 g_s10_10) (mem g_s80_98 NAT1) (= g_s79_97 (|+i| g_s78_96 g_s80_98)) (mem g_s81_99 NATURAL1) (mem g_s82_100 g_s10_10) (= g_s82_100 (|+i| g_s78_96 g_s81_99)) (mem g_s83_101 g_s10_10) (mem g_s84_102 g_s10_10) (mem g_s85_103 g_s10_10) (mem g_s86_104 g_s10_10) (mem g_s87_105 g_s12_12) (|<i| (|*i| e22 g_s87_105) g_s11_13) (mem g_s88_106 NAT1) (mem g_s89_107 g_s12_12) (mem g_s90_108 g_s12_12) (= g_s90_108 (|+i| g_s89_107 g_s88_106)) (mem g_s91_109 g_s10_10) (mem g_s92_110 g_s10_10) (mem g_s93_111 g_s10_10) (mem g_s94_112 g_s10_10) (mem g_s95_113 g_s10_10) (mem g_s96_114 g_s10_10) (mem g_s97_115 g_s10_10) (mem g_s98_116 g_s10_10) (mem g_s99_117 g_s10_10) (mem g_s100_118 g_s10_10) (mem g_s101_119 g_s10_10) (|<i| g_s101_119 g_s9_11) (mem g_s53_68 g_s10_10) (= g_s53_68 (|-i| g_s101_119 e93)) (mem g_s102_120 g_s10_10) (mem g_s51_66 g_s10_10) (|<i| g_s102_120 g_s9_11) (= g_s51_66 (|-i| g_s102_120 e93)) (mem g_s103_121 g_s12_12) (|<=i| g_s103_121 e122) (mem g_s104_123 g_s12_12) (|<=i| (|+i| g_s103_121 g_s104_123) e124) (|<=i| e125 g_s51_66) (|<=i| e124 g_s101_119)))
(define-fun |def_seext| () Bool (and (mem g_s105_126 g_s10_10) (mem g_s106_127 g_s10_10) (mem g_s107_128 g_s10_10) (mem g_s108_129 g_s10_10) (mem g_s109_130 g_s10_10) (mem g_s110_131 g_s10_10) (mem g_s111_132 g_s10_10) (mem g_s112_133 g_s10_10) (mem g_s113_134 g_s10_10) (mem g_s114_135 g_s10_10) (mem g_s115_136 g_s10_10) (mem g_s116_137 g_s10_10) (mem g_s117_138 g_s10_10) (mem g_s118_139 g_s10_10) (mem g_s119_140 g_s14_14) (or (= g_s119_140 e93) (= g_s119_140 e22)) (mem g_s120_141 g_s10_10) (mem g_s121_142 g_s10_10) (mem g_s122_143 g_s10_10) (mem g_s123_144 g_s10_10) (mem g_s124_145 g_s10_10) (mem g_s125_146 g_s10_10) (mem g_s126_147 (|-->| (interval e0 g_s53_68) g_s14_14)) (mem g_s127_148 g_s10_10) (mem g_s128_149 g_s10_10) (mem g_s129_150 g_s10_10) (mem g_s130_151 g_s10_10) (mem g_s131_152 g_s10_10) (mem g_s132_153 (|-->| (interval e0 e22) g_s14_14)) (mem g_s133_154 (|-->| (interval e0 e22) g_s14_14)) (mem g_s134_155 g_s12_12) (mem g_s18_23 (|+->| BOOL g_s14_14)) (mem g_s18_23 (|+->| BOOL g_s12_12)) (mem g_s18_23 (|+->| BOOL g_s10_10))))
(define-fun |def_mchcst| () Bool true)
(define-fun |def_aprp| () Bool true)
(define-fun |def_abs| () Bool (and (mem g_s135_156 BOOL) (mem g_s136_157 g_s10_10) (mem g_s137_158 g_s10_10) (mem g_s138_159 g_s10_10) (mem g_s139_160 g_s14_14) (mem g_s135_156 BOOL)))
(define-fun |def_inv| () Bool (and (= g_s138_159 g_s138$1_161) (= g_s136_157 g_s136$1_162) (= g_s139_160 g_s139$1_163) (= g_s137_158 g_s137$1_164) (mem g_s140$1_165 g_s14_14) (mem g_s138$1_161 g_s10_10) (mem g_s136$1_162 g_s10_10) (mem g_s139$1_163 g_s14_14) (mem g_s137$1_164 g_s10_10) (= g_s140$1_165 (apply g_s18_23 g_s135_156))))
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
(push 1)
(assert (not (mem e0 g_s10_10)))
(check-sat)
(pop 1)
; PO 2 in group 0
(push 1)
(assert (not (= g_s16_17 (apply g_s18_23 FALSE))))
(set-info :status unknown)
(check-sat)
(pop 1)
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
(define-fun lh_1 () Bool (|<i| g_s136$1_162 g_s9_11))
; PO 1 in group 1
(push 1)
(assert (not (=> lh_1 (mem e93 g_s10_10))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 1
(push 1)
(assert (not (=> lh_1 (|<=i| (|+i| g_s136$1_162 e93) g_s9_11))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 2 
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
(define-fun lh_1 () Bool (mem g_s146$1_166 BOOL))
(define-fun lh_2 () Bool (mem g_s147$1_167 BOOL))
(define-fun lh_3 () Bool (mem g_s148$1_168 g_s10_10))
(define-fun lh_4 () Bool (= (bool (and (= (bool (|<=i| g_s136$1_162 g_s137$1_164)) TRUE) (= (bool (|<=i| g_s112_133 g_s138$1_161)) TRUE))) TRUE))
(define-fun lh_5 () Bool (= (bool (or (= (bool (or (= (bool (or (= (bool (= g_s139$1_163 g_s16_17)) TRUE) (= (bool (= (bool (= (apply g_s22_27 (mapplet g_s113_134 e170)) e169)) FALSE)) TRUE))) TRUE) (= (bool (= (apply g_s22_27 (mapplet g_s114_135 e171)) e0)) TRUE))) TRUE) (= (bool (= (bool (= (apply g_s22_27 (mapplet g_s115_136 e19)) e172)) FALSE)) TRUE))) TRUE))
(define-fun lh_6 () Bool (or (and (|<=i| g_s136$1_162 g_s137$1_164) (|<=i| g_s112_133 g_s138$1_161) (= g_s139$1_163 g_s16_17)) (not (= (apply g_s22_27 (mapplet g_s113_134 e170)) e169)) (= (apply g_s22_27 (mapplet g_s114_135 e171)) e0) (not (= (apply g_s22_27 (mapplet g_s115_136 e19)) e172))))
(define-fun lh_7 () Bool (|<=i| g_s136$1_162 g_s137$1_164))
(define-fun lh_8 () Bool (|<=i| g_s112_133 g_s138$1_161))
(define-fun lh_9 () Bool (not (and (|<=i| g_s136$1_162 g_s137$1_164) (|<=i| g_s112_133 g_s138$1_161))))
; PO 1 in group 2
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_9) (= g_s15_16 (apply g_s18_23 TRUE)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 2
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_9) (= g_s139$1_163 g_s16_17))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 2
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8) (= g_s15_16 (apply g_s18_23 TRUE)))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 3 
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
(define-fun lh_1 () Bool (= g_s138_159 g_s138$1_161))
(define-fun lh_2 () Bool (= g_s136_157 g_s136$1_162))
(define-fun lh_3 () Bool (= g_s139_160 g_s139$1_163))
(define-fun lh_4 () Bool (= g_s137_158 g_s137$1_164))
(define-fun lh_5 () Bool (mem g_s140$1_165 g_s14_14))
(define-fun lh_6 () Bool (mem g_s138$1_161 g_s10_10))
(define-fun lh_7 () Bool (mem g_s136$1_162 g_s10_10))
(define-fun lh_8 () Bool (mem g_s139$1_163 g_s14_14))
(define-fun lh_9 () Bool (mem g_s137$1_164 g_s10_10))
; PO 1 in group 3
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9) (mem g_s135_156 (dom g_s18_23)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 3
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9) (mem g_s18_23 (|+->| (dom g_s18_23) (ran g_s18_23))))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 4 
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
(define-fun lh_1 () Bool (mem g_s146$1_166 BOOL))
(define-fun lh_2 () Bool (mem g_s147$1_167 BOOL))
(define-fun lh_3 () Bool (mem g_s148$1_168 g_s10_10))
(define-fun lh_4 () Bool (= (bool (and (= (bool (|<=i| g_s136$1_162 g_s137$1_164)) TRUE) (= (bool (|<=i| g_s112_133 g_s138$1_161)) TRUE))) TRUE))
; PO 1 in group 4
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem g_s22_27 (|+->| (dom g_s22_27) (ran g_s22_27))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 4
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem (mapplet g_s114_135 e171) (dom g_s22_27)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 4
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem (mapplet g_s115_136 e19) (dom g_s22_27)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 4
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem (mapplet g_s113_134 e170) (dom g_s22_27)))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
(exit)