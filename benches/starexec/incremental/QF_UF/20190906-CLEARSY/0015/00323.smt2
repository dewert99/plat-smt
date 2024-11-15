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
(declare-fun e17 () U)
(declare-fun g_s0_1 () U)
(declare-fun g_s1_2 () U)
(declare-fun g_s10_11 () U)
(declare-fun g_s100_103 () U)
(declare-fun g_s101_102 () U)
(declare-fun g_s102_105 () U)
(declare-fun g_s103_104 () U)
(declare-fun g_s104_107 () U)
(declare-fun g_s105_106 () U)
(declare-fun g_s106_109 () U)
(declare-fun g_s107_108 () U)
(declare-fun g_s108_111 () U)
(declare-fun g_s109_110 () U)
(declare-fun g_s11_12 () U)
(declare-fun g_s110_113 () U)
(declare-fun g_s111_112 () U)
(declare-fun g_s112_115 () U)
(declare-fun g_s113_114 () U)
(declare-fun g_s114_117 () U)
(declare-fun g_s115_116 () U)
(declare-fun g_s116_119 () U)
(declare-fun g_s117_118 () U)
(declare-fun g_s118_121 () U)
(declare-fun g_s119_120 () U)
(declare-fun g_s12_13 () U)
(declare-fun g_s120_123 () U)
(declare-fun g_s121_122 () U)
(declare-fun g_s122_125 () U)
(declare-fun g_s123_124 () U)
(declare-fun g_s124_127 () U)
(declare-fun g_s125_126 () U)
(declare-fun g_s126_129 () U)
(declare-fun g_s127_128 () U)
(declare-fun g_s128_131 () U)
(declare-fun g_s129_130 () U)
(declare-fun g_s130_133 () U)
(declare-fun g_s131_132 () U)
(declare-fun g_s132_135 () U)
(declare-fun g_s133_134 () U)
(declare-fun g_s134_137 () U)
(declare-fun g_s135_136 () U)
(declare-fun g_s136_139 () U)
(declare-fun g_s137_138 () U)
(declare-fun g_s138_141 () U)
(declare-fun g_s139_140 () U)
(declare-fun g_s140_143 () U)
(declare-fun g_s141_142 () U)
(declare-fun g_s142_145 () U)
(declare-fun g_s143_144 () U)
(declare-fun g_s144_146 () U)
(declare-fun g_s145_147 () U)
(declare-fun g_s146_148 () U)
(declare-fun g_s147_149 () U)
(declare-fun g_s148_150 () U)
(declare-fun g_s149_151 () U)
(declare-fun g_s15_16 () U)
(declare-fun g_s150_152 () U)
(declare-fun g_s151_153 () U)
(declare-fun g_s152_154 () U)
(declare-fun g_s153_155 () U)
(declare-fun g_s154_156 () U)
(declare-fun g_s155_157 () U)
(declare-fun g_s156_158 () U)
(declare-fun g_s157_159 () U)
(declare-fun g_s158_160 () U)
(declare-fun g_s159_161 () U)
(declare-fun g_s16_18 () U)
(declare-fun g_s160_162 () U)
(declare-fun g_s161_163 () U)
(declare-fun g_s162_164 () U)
(declare-fun g_s163_165 () U)
(declare-fun g_s164_166 () U)
(declare-fun g_s165_167 () U)
(declare-fun g_s166_168 () U)
(declare-fun g_s167_169 () U)
(declare-fun g_s168_170 () U)
(declare-fun g_s169_171 () U)
(declare-fun g_s17_19 () U)
(declare-fun g_s173_172 () U)
(declare-fun g_s174$1_173 () U)
(declare-fun g_s178_174 () U)
(declare-fun g_s18_20 () U)
(declare-fun g_s180_175 () U)
(declare-fun g_s186_176 () U)
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
(declare-fun g_s32_35 () U)
(declare-fun g_s33_34 () U)
(declare-fun g_s34_37 () U)
(declare-fun g_s35_36 () U)
(declare-fun g_s36_39 () U)
(declare-fun g_s37_38 () U)
(declare-fun g_s38_41 () U)
(declare-fun g_s39_40 () U)
(declare-fun g_s4_5 () U)
(declare-fun g_s40_43 () U)
(declare-fun g_s41_42 () U)
(declare-fun g_s42_45 () U)
(declare-fun g_s43_44 () U)
(declare-fun g_s44_47 () U)
(declare-fun g_s45_46 () U)
(declare-fun g_s46_49 () U)
(declare-fun g_s47_48 () U)
(declare-fun g_s48_51 () U)
(declare-fun g_s49_50 () U)
(declare-fun g_s5_6 () U)
(declare-fun g_s50_53 () U)
(declare-fun g_s51_52 () U)
(declare-fun g_s52_55 () U)
(declare-fun g_s53_54 () U)
(declare-fun g_s54_57 () U)
(declare-fun g_s55_56 () U)
(declare-fun g_s56_59 () U)
(declare-fun g_s57_58 () U)
(declare-fun g_s58_61 () U)
(declare-fun g_s59_60 () U)
(declare-fun g_s6_7 () U)
(declare-fun g_s60_63 () U)
(declare-fun g_s61_62 () U)
(declare-fun g_s62_65 () U)
(declare-fun g_s63_64 () U)
(declare-fun g_s64_67 () U)
(declare-fun g_s65_66 () U)
(declare-fun g_s66_69 () U)
(declare-fun g_s67_68 () U)
(declare-fun g_s68_71 () U)
(declare-fun g_s69_70 () U)
(declare-fun g_s7_8 () U)
(declare-fun g_s70_73 () U)
(declare-fun g_s71_72 () U)
(declare-fun g_s72_75 () U)
(declare-fun g_s73_74 () U)
(declare-fun g_s74_77 () U)
(declare-fun g_s75_76 () U)
(declare-fun g_s76_79 () U)
(declare-fun g_s77_78 () U)
(declare-fun g_s78_81 () U)
(declare-fun g_s79_80 () U)
(declare-fun g_s8_9 () U)
(declare-fun g_s80_83 () U)
(declare-fun g_s81_82 () U)
(declare-fun g_s82_85 () U)
(declare-fun g_s83_84 () U)
(declare-fun g_s84_87 () U)
(declare-fun g_s85_86 () U)
(declare-fun g_s86_89 () U)
(declare-fun g_s87_88 () U)
(declare-fun g_s88_91 () U)
(declare-fun g_s89_90 () U)
(declare-fun g_s9_10 () U)
(declare-fun g_s90_93 () U)
(declare-fun g_s91_92 () U)
(declare-fun g_s92_95 () U)
(declare-fun g_s93_94 () U)
(declare-fun g_s94_97 () U)
(declare-fun g_s95_96 () U)
(declare-fun g_s96_99 () U)
(declare-fun g_s97_98 () U)
(declare-fun g_s98_101 () U)
(declare-fun g_s99_100 () U)
(declare-fun e15 () U)
(declare-fun e14 () U)
; Defines
(define-fun |def_B definitions| () Bool (and (= NAT (interval e0 MaxInt)) (= INT (interval MinInt MaxInt))))
(define-fun |def_ctx| () Bool (and (not (= g_s0_1 empty)) (not (= g_s1_2 empty)) (not (= g_s2_3 empty)) (not (= g_s3_4 empty)) (not (= g_s4_5 empty)) (not (= g_s5_6 empty)) (not (= g_s6_7 empty)) (not (= g_s7_8 empty)) (not (= g_s8_9 empty)) (not (= g_s9_10 empty)) (not (= g_s10_11 empty)) (not (= g_s11_12 empty)) (mem g_s12_13 (|-->| (set_prod INTEGER NATURAL) INTEGER)) (= g_s12_13 (binary_union e15 e14)) (mem g_s15_16 (|-->| BOOL NAT)) (= g_s15_16 (SET (mapplet (mapplet FALSE e0) (mapplet TRUE e17)))) (= g_s16_18 INT) (= g_s17_19 NAT) (= g_s18_20 NAT1) (subset g_s18_20 g_s17_19) (subset g_s17_19 g_s16_18) (mem g_s19_21 g_s16_18) (mem g_s19_21 g_s17_19) (not (mem g_s19_21 g_s18_20)) (mem g_s20_22 g_s16_18) (not (mem g_s20_22 g_s17_19)) (= g_s21_23 INT) (subset g_s22_24 g_s10_11) (mem g_s23_25 g_s10_11) (mem g_s23_25 g_s22_24) (mem g_s24_26 g_s10_11) (not (mem g_s24_26 g_s22_24)) (mem g_s25_27 (|+->| NAT g_s10_11)) (mem g_s25_27 (perm g_s22_24)) (= (card g_s22_24) g_s26_28) (subset g_s27_29 g_s11_12) (mem g_s28_30 g_s11_12) (mem g_s28_30 g_s27_29) (mem g_s29_31 g_s11_12) (not (mem g_s29_31 g_s27_29)) (mem g_s30_32 (|+->| NAT g_s11_12)) (mem g_s30_32 (perm g_s27_29)) (= (card g_s27_29) g_s31_33) (|<=i| g_s32_35 g_s33_34) (|<=i| g_s34_37 g_s35_36) (|<=i| g_s36_39 g_s37_38) (|<=i| g_s38_41 g_s39_40) (|<=i| g_s40_43 g_s41_42) (|<=i| g_s42_45 g_s43_44) (|<=i| g_s44_47 g_s45_46) (|<=i| g_s46_49 g_s47_48) (|<=i| g_s48_51 g_s49_50) (|<=i| g_s50_53 g_s51_52) (|<=i| g_s52_55 g_s53_54) (|<=i| g_s54_57 g_s55_56) (|<=i| g_s56_59 g_s57_58) (|<=i| g_s58_61 g_s59_60) (|<=i| g_s58_61 e17) (|<=i| g_s60_63 g_s61_62) (|<=i| g_s62_65 g_s63_64) (|<=i| g_s64_67 g_s65_66) (|<=i| g_s66_69 g_s67_68) (|<=i| g_s68_71 g_s69_70) (|<=i| g_s70_73 g_s71_72) (|<=i| g_s72_75 g_s73_74) (|<=i| g_s74_77 g_s75_76) (|<=i| g_s76_79 g_s77_78) (|<=i| g_s78_81 g_s79_80) (|<=i| g_s80_83 g_s81_82) (|<=i| g_s82_85 g_s83_84) (|<=i| g_s84_87 g_s85_86) (|<=i| g_s86_89 g_s87_88) (|<=i| g_s88_91 g_s89_90) (|<=i| g_s90_93 g_s91_92) (|<=i| g_s92_95 g_s93_94) (|<=i| g_s94_97 g_s95_96) (|<=i| g_s96_99 g_s97_98) (|<=i| g_s98_101 g_s99_100) (|<=i| g_s100_103 g_s101_102) (|<=i| g_s102_105 g_s103_104) (|<=i| g_s104_107 g_s105_106) (|<=i| g_s106_109 g_s107_108) (|<=i| g_s108_111 g_s109_110) (|<=i| g_s110_113 g_s111_112) (|<=i| g_s112_115 g_s113_114) (|<=i| g_s114_117 g_s115_116) (|<=i| g_s116_119 g_s117_118) (|<=i| g_s118_121 g_s119_120) (|<=i| g_s120_123 g_s121_122) (|<=i| g_s122_125 g_s123_124) (|<=i| g_s124_127 g_s125_126) (|<=i| g_s126_129 g_s127_128) (|<=i| g_s78_81 g_s76_79) (|<=i| g_s128_131 g_s129_130) (|<=i| g_s130_133 g_s131_132) (|<=i| g_s132_135 g_s133_134) (|<=i| g_s134_137 g_s135_136) (|<=i| g_s136_139 g_s137_138) (|<=i| g_s138_141 g_s139_140) (|<=i| g_s140_143 g_s141_142) (|<=i| g_s140_143 g_s138_141) (|<=i| g_s142_145 g_s143_144) (|<=i| g_s142_145 g_s138_141) (|<=i| g_s32_35 g_s26_28) (|<=i| g_s54_57 g_s31_33) (|<=i| g_s56_59 g_s31_33) (|<=i| g_s58_61 g_s31_33) (|<=i| g_s60_63 g_s31_33) (|<=i| (|+i| (|+i| (|+i| g_s56_59 g_s54_57) g_s60_63) g_s58_61) g_s31_33) (mem g_s32_35 NAT) (mem g_s34_37 NAT) (mem g_s36_39 NAT) (mem g_s38_41 NAT) (mem g_s40_43 NAT) (mem g_s42_45 NAT) (mem g_s44_47 NAT) (mem g_s46_49 NAT) (mem g_s48_51 NAT) (mem g_s50_53 NAT) (mem g_s52_55 NAT) (mem g_s54_57 NAT) (mem g_s56_59 NAT) (mem g_s58_61 NAT) (mem g_s60_63 NAT) (mem g_s62_65 NAT1) (mem g_s64_67 NAT) (mem g_s66_69 NAT) (mem g_s68_71 NAT) (mem g_s70_73 NAT) (mem g_s72_75 NAT) (mem g_s74_77 NAT) (mem g_s76_79 NAT) (mem g_s78_81 NAT) (mem g_s80_83 NAT) (mem g_s82_85 NAT) (mem g_s84_87 NAT) (mem g_s122_125 NAT) (mem g_s124_127 NAT) (mem g_s126_129 g_s144_146) (mem g_s88_91 NAT) (mem g_s90_93 NAT) (mem g_s92_95 NAT) (mem g_s94_97 NAT) (mem g_s96_99 NAT) (mem g_s98_101 NAT) (mem g_s100_103 NAT) (mem g_s102_105 NAT) (mem g_s104_107 NAT) (mem g_s106_109 NAT) (mem g_s108_111 NAT) (mem g_s110_113 NAT) (mem g_s112_115 NAT) (mem g_s114_117 NAT) (mem g_s116_119 NAT) (mem g_s118_121 NAT) (mem g_s120_123 NAT) (mem g_s86_89 NAT) (mem g_s128_131 NAT) (mem g_s130_133 NAT) (mem g_s132_135 NAT) (mem g_s134_137 NAT) (mem g_s136_139 NAT) (mem g_s138_141 NAT) (mem g_s140_143 NAT) (mem g_s142_145 NAT)))
(define-fun |def_seext| () Bool  (mem g_s145_147 g_s8_9))
(define-fun |def_lprp| () Bool (and (not (= g_s146_148 empty)) (not (= g_s147_149 empty)) (not (= g_s148_150 empty)) (not (= g_s149_151 empty)) (not (= g_s150_152 empty)) (subset g_s151_153 g_s146_148) (mem g_s152_154 g_s146_148) (not (mem g_s152_154 g_s151_153)) (mem g_s153_155 (|+->| NAT g_s146_148)) (mem g_s153_155 (perm g_s151_153)) (subset g_s154_156 g_s147_149) (mem g_s155_157 g_s147_149) (not (mem g_s155_157 g_s154_156)) (mem g_s156_158 (|+->| NAT g_s147_149)) (mem g_s156_158 (perm g_s154_156)) (subset g_s157_159 g_s148_150) (mem g_s158_160 g_s148_150) (not (mem g_s158_160 g_s157_159)) (mem g_s159_161 (|+->| NAT g_s148_150)) (mem g_s159_161 (perm g_s157_159)) (subset g_s160_162 g_s149_151) (mem g_s161_163 g_s149_151) (not (mem g_s161_163 g_s160_162)) (mem g_s162_164 (|+->| NAT g_s149_151)) (mem g_s162_164 (perm g_s160_162)) (subset g_s163_165 g_s150_152) (mem g_s164_166 g_s150_152) (not (mem g_s164_166 g_s163_165)) (mem g_s165_167 (|+->| NAT g_s150_152)) (mem g_s165_167 (perm g_s163_165)) (mem g_s166_168 (|>->| g_s151_153 g_s27_29)) (mem g_s167_169 (|>->| g_s154_156 g_s27_29)) (mem g_s168_170 g_s11_12) (=> (not (= g_s58_61 e0)) (mem g_s168_170 g_s27_29)) (mem g_s169_171 (|>->| g_s160_162 g_s27_29)) (= (binary_inter (ran g_s166_168) (ran g_s167_169)) empty) (= (binary_inter (ran g_s166_168) (ran g_s169_171)) empty) (= (binary_inter (ran g_s169_171) (ran g_s167_169)) empty) (=> (not (= g_s58_61 e0)) (not (mem g_s168_170 (ran g_s166_168)))) (=> (not (= g_s58_61 e0)) (not (mem g_s168_170 (ran g_s167_169)))) (=> (not (= g_s58_61 e0)) (not (mem g_s168_170 (ran g_s169_171))))))
(define-fun |def_inprp| () Bool true)
(define-fun |def_inext| () Bool true)
(define-fun |def_inv| () Bool true)
(define-fun |def_ass| () Bool true)
(define-fun |def_cst| () Bool true)
(define-fun |def_sets| () Bool (and (not (= g_s146_148 empty)) (not (= g_s147_149 empty)) (not (= g_s148_150 empty)) (not (= g_s149_151 empty)) (not (= g_s150_152 empty))))
; PO group 0 
(push 1)
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_cst|)
(assert |def_sets|)
(define-fun lh_1 () Bool (subset g_s151_153 g_s146_148))
(define-fun lh_2 () Bool (mem g_s152_154 g_s146_148))
(define-fun lh_3 () Bool (not (mem g_s152_154 g_s151_153)))
(define-fun lh_4 () Bool (mem g_s153_155 (|+->| NAT g_s146_148)))
(define-fun lh_5 () Bool (mem g_s153_155 (perm g_s151_153)))
(define-fun lh_6 () Bool (subset g_s154_156 g_s147_149))
(define-fun lh_7 () Bool (mem g_s155_157 g_s147_149))
(define-fun lh_8 () Bool (not (mem g_s155_157 g_s154_156)))
(define-fun lh_9 () Bool (mem g_s156_158 (|+->| NAT g_s147_149)))
(define-fun lh_10 () Bool (mem g_s156_158 (perm g_s154_156)))
(define-fun lh_11 () Bool (subset g_s157_159 g_s148_150))
(define-fun lh_12 () Bool (mem g_s158_160 g_s148_150))
(define-fun lh_13 () Bool (not (mem g_s158_160 g_s157_159)))
(define-fun lh_14 () Bool (mem g_s159_161 (|+->| NAT g_s148_150)))
(define-fun lh_15 () Bool (mem g_s159_161 (perm g_s157_159)))
(define-fun lh_16 () Bool (subset g_s160_162 g_s149_151))
(define-fun lh_17 () Bool (mem g_s161_163 g_s149_151))
(define-fun lh_18 () Bool (not (mem g_s161_163 g_s160_162)))
(define-fun lh_19 () Bool (mem g_s162_164 (|+->| NAT g_s149_151)))
(define-fun lh_20 () Bool (mem g_s162_164 (perm g_s160_162)))
(define-fun lh_21 () Bool (subset g_s163_165 g_s150_152))
(define-fun lh_22 () Bool (mem g_s164_166 g_s150_152))
(define-fun lh_23 () Bool (not (mem g_s164_166 g_s163_165)))
(define-fun lh_24 () Bool (mem g_s165_167 (|+->| NAT g_s150_152)))
; PO 1 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem g_s151_153 (FIN g_s151_153)))))
(check-sat)
(pop 1)
; PO 2 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9) (mem g_s154_156 (FIN g_s154_156)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14) (mem g_s157_159 (FIN g_s157_159)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19) (mem g_s160_162 (FIN g_s160_162)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 5 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15 lh_16 lh_17 lh_18 lh_19 lh_20 lh_21 lh_22 lh_23 lh_24) (mem g_s163_165 (FIN g_s163_165)))))
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
(assert (mem g_s173_172 g_s146_148))
(assert (mem g_s173_172 g_s151_153))
(define-fun lh_1 () Bool (mem g_s174$1_173 g_s11_12))
(define-fun lh_2 () Bool (mem g_s174$1_173 g_s27_29))
; PO 1 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem g_s166_168 (|+->| (dom g_s166_168) (ran g_s166_168))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem g_s173_172 (dom g_s166_168)))))
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
(define-fun lh_1 () Bool (mem (card g_s151_153) INT))
; PO 1 in group 2
(push 1)
(assert (not (mem g_s151_153 (FIN g_s151_153))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 2
(push 1)
(assert (not (=> lh_1 (mem g_s151_153 (FIN g_s151_153)))))
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
(assert (mem g_s178_174 NATURAL))
(assert (mem g_s178_174 (dom g_s153_155)))
; PO 1 in group 3
(assert (not (mem g_s153_155 (|+->| (dom g_s153_155) (ran g_s153_155)))))
(set-info :status unknown)
(check-sat)
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
(assert (mem g_s180_175 g_s147_149))
(assert (mem g_s180_175 g_s154_156))
(define-fun lh_1 () Bool (mem g_s174$1_173 g_s11_12))
(define-fun lh_2 () Bool (mem g_s174$1_173 g_s27_29))
; PO 1 in group 4
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem g_s167_169 (|+->| (dom g_s167_169) (ran g_s167_169))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 4
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem g_s180_175 (dom g_s167_169)))))
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
(define-fun lh_1 () Bool (mem (card g_s154_156) INT))
; PO 1 in group 5
(push 1)
(assert (not (mem g_s154_156 (FIN g_s154_156))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 5
(push 1)
(assert (not (=> lh_1 (mem g_s154_156 (FIN g_s154_156)))))
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
(assert (mem g_s178_174 NATURAL))
(assert (mem g_s178_174 (dom g_s156_158)))
; PO 1 in group 6
(assert (not (mem g_s156_158 (|+->| (dom g_s156_158) (ran g_s156_158)))))
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
(define-fun lh_1 () Bool (mem (card g_s157_159) INT))
; PO 1 in group 7
(push 1)
(assert (not (mem g_s157_159 (FIN g_s157_159))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 7
(push 1)
(assert (not (=> lh_1 (mem g_s157_159 (FIN g_s157_159)))))
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
(assert (mem g_s178_174 NATURAL))
(assert (mem g_s178_174 (dom g_s159_161)))
; PO 1 in group 8
(assert (not (mem g_s159_161 (|+->| (dom g_s159_161) (ran g_s159_161)))))
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
(assert (mem g_s186_176 g_s149_151))
(assert (mem g_s186_176 g_s160_162))
(define-fun lh_1 () Bool (mem g_s174$1_173 g_s11_12))
(define-fun lh_2 () Bool (mem g_s174$1_173 g_s27_29))
; PO 1 in group 9
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem g_s169_171 (|+->| (dom g_s169_171) (ran g_s169_171))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 9
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem g_s186_176 (dom g_s169_171)))))
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
(define-fun lh_1 () Bool (mem (card g_s160_162) INT))
; PO 1 in group 10
(push 1)
(assert (not (mem g_s160_162 (FIN g_s160_162))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 10
(push 1)
(assert (not (=> lh_1 (mem g_s160_162 (FIN g_s160_162)))))
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
(assert (mem g_s178_174 NATURAL))
(assert (mem g_s178_174 (dom g_s162_164)))
; PO 1 in group 11
(assert (not (mem g_s162_164 (|+->| (dom g_s162_164) (ran g_s162_164)))))
(set-info :status unknown)
(check-sat)
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
(define-fun lh_1 () Bool (mem (card g_s163_165) INT))
; PO 1 in group 12
(push 1)
(assert (not (mem g_s163_165 (FIN g_s163_165))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 12
(push 1)
(assert (not (=> lh_1 (mem g_s163_165 (FIN g_s163_165)))))
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
(assert (mem g_s178_174 NATURAL))
(assert (mem g_s178_174 (dom g_s165_167)))
; PO 1 in group 13
(assert (not (mem g_s165_167 (|+->| (dom g_s165_167) (ran g_s165_167)))))
(set-info :status unknown)
(check-sat)
(pop 1)
(exit)