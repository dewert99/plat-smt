(set-info :smt-lib-version 2.6)
(set-logic UF)
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
(declare-fun e118 () U)
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
(declare-fun g_s114_116 () U)
(declare-fun g_s115_115 () U)
(declare-fun g_s116_117 () U)
(declare-fun g_s117_119 () U)
(declare-fun g_s118_120 () U)
(declare-fun g_s119_121 () U)
(declare-fun g_s12_13 () U)
(declare-fun g_s120_122 () U)
(declare-fun g_s121_123 () U)
(declare-fun g_s122_124 () U)
(declare-fun g_s123_125 () U)
(declare-fun g_s124_126 () U)
(declare-fun g_s125_127 () U)
(declare-fun g_s126_128 () U)
(declare-fun g_s127_129 () U)
(declare-fun g_s128_130 () U)
(declare-fun g_s129_131 () U)
(declare-fun g_s13_14 () U)
(declare-fun g_s130_132 () U)
(declare-fun g_s131_133 () U)
(declare-fun g_s132_134 () U)
(declare-fun g_s133_135 () U)
(declare-fun g_s134_136 () U)
(declare-fun g_s135_137 () U)
(declare-fun g_s136_138 () U)
(declare-fun g_s137_139 () U)
(declare-fun g_s138_140 () U)
(declare-fun g_s139_141 () U)
(declare-fun g_s14_15 () U)
(declare-fun g_s140_142 () U)
(declare-fun g_s141_143 () U)
(declare-fun g_s142_144 () U)
(declare-fun g_s143_145 () U)
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
(declare-fun g_s156_159 () U)
(declare-fun g_s157_158 () U)
(declare-fun g_s158_160 () U)
(declare-fun g_s159_161 () U)
(declare-fun g_s16_17 () U)
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
(declare-fun g_s17_18 () U)
(declare-fun g_s170_172 () U)
(declare-fun g_s171_173 () U)
(declare-fun g_s172_174 () U)
(declare-fun g_s173_175 () U)
(declare-fun g_s174_176 () U)
(declare-fun g_s175_177 () U)
(declare-fun g_s176_178 () U)
(declare-fun g_s177_179 () U)
(declare-fun g_s178_180 () U)
(declare-fun g_s179_181 () U)
(declare-fun g_s18_19 () U)
(declare-fun g_s180_182 () U)
(declare-fun g_s181_183 () U)
(declare-fun g_s182_184 () U)
(declare-fun g_s183_185 () U)
(declare-fun g_s184_186 () U)
(declare-fun g_s185_187 () U)
(declare-fun g_s186_188 () U)
(declare-fun g_s187_189 () U)
(declare-fun g_s19_20 () U)
(declare-fun g_s191_190 () U)
(declare-fun g_s192$1_191 () U)
(declare-fun g_s195$1_192 () U)
(declare-fun g_s198$1_193 () U)
(declare-fun g_s2_3 () U)
(declare-fun g_s20_21 () U)
(declare-fun g_s201$1_194 () U)
(declare-fun g_s204$1_195 () U)
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
(declare-fun g_s75_76 () U)
(declare-fun g_s76_77 () U)
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
(define-fun |def_ctx| () Bool (and (= g_s0_1 (SET (mapplet g_s2_3 g_s1_2))) (= g_s3_4 (SET (mapplet g_s7_8 (mapplet g_s6_7 (mapplet g_s5_6 g_s4_5))))) (= g_s8_9 (SET (mapplet g_s12_13 (mapplet g_s11_12 (mapplet g_s10_11 g_s9_10))))) (= g_s13_14 (SET (mapplet g_s22_23 (mapplet g_s21_22 (mapplet g_s20_21 (mapplet g_s19_20 (mapplet g_s18_19 (mapplet g_s17_18 (mapplet g_s16_17 (mapplet g_s15_16 g_s14_15)))))))))) (= g_s23_24 (SET (mapplet g_s26_27 (mapplet g_s25_26 g_s24_25)))) (= g_s27_28 (SET (mapplet g_s29_30 g_s28_29))) (= g_s30_31 (SET (mapplet g_s33_34 (mapplet g_s32_33 g_s31_32)))) (= g_s34_35 (SET (mapplet g_s36_37 g_s35_36))) (= g_s37_38 (SET (mapplet g_s41_42 (mapplet g_s40_41 (mapplet g_s39_40 g_s38_39))))) (= g_s42_43 (SET (mapplet g_s44_45 g_s43_44))) (= g_s45_46 (SET (mapplet g_s48_49 (mapplet g_s47_48 g_s46_47)))) (= g_s49_50 (SET (mapplet g_s52_53 (mapplet g_s51_52 g_s50_51)))) (= g_s53_54 (SET (mapplet g_s55_56 g_s54_55))) (= g_s56_57 (SET (mapplet g_s59_60 (mapplet g_s58_59 g_s57_58)))) (= g_s60_61 (SET (mapplet g_s65_66 (mapplet g_s64_65 (mapplet g_s63_64 (mapplet g_s62_63 g_s61_62)))))) (= g_s66_67 (SET (mapplet g_s69_70 (mapplet g_s68_69 g_s67_68)))) (= g_s70_71 (SET (mapplet g_s73_74 (mapplet g_s72_73 g_s71_72)))) (= g_s74_75 (SET (mapplet g_s77_78 (mapplet g_s76_77 g_s75_76)))) (= g_s78_79 (SET (mapplet g_s81_82 (mapplet g_s80_81 g_s79_80)))) (= g_s82_83 (SET (mapplet g_s85_86 (mapplet g_s84_85 g_s83_84)))) (= g_s86_87 (SET (mapplet g_s93_94 (mapplet g_s92_93 (mapplet g_s91_92 (mapplet g_s90_91 (mapplet g_s89_90 (mapplet g_s88_89 g_s87_88)))))))) (not (= g_s94_95 empty)) (not (= g_s95_96 empty)) (not (= g_s96_97 empty)) (= g_s97_98 (SET (mapplet g_s104_105 (mapplet g_s103_104 (mapplet g_s102_103 (mapplet g_s101_102 (mapplet g_s100_101 (mapplet g_s99_100 g_s98_99)))))))) (not (= g_s105_106 empty)) (not (= g_s106_107 empty)) (not (= g_s107_108 empty)) (not (= g_s108_109 empty)) (not (= g_s109_110 empty)) (not (= g_s110_111 empty)) (not (= g_s111_112 empty)) (not (= g_s112_113 empty)) (not (= g_s113_114 empty)) (= g_s114_116 (interval (iuminus g_s115_115) g_s115_115)) (= g_s116_117 (interval e0 g_s115_115)) (= g_s117_119 (interval e118 g_s115_115)) (subset g_s117_119 g_s116_117) (subset g_s116_117 g_s114_116) (subset g_s116_117 NAT) (subset g_s117_119 NAT1) (subset g_s114_116 INT) (mem g_s118_120 g_s114_116) (mem g_s118_120 g_s116_117) (not (mem g_s118_120 g_s117_119)) (mem g_s119_121 g_s114_116) (not (mem g_s119_121 g_s116_117)) (= g_s120_122 (interval (iuminus g_s115_115) g_s115_115)) (subset g_s120_122 INT) (subset g_s121_123 g_s94_95) (mem g_s122_124 g_s94_95) (mem g_s122_124 g_s121_123) (mem g_s123_125 g_s94_95) (not (mem g_s123_125 g_s121_123)) (mem g_s124_126 (|+->| NAT g_s94_95)) (mem g_s124_126 (perm g_s121_123)) (= (card g_s121_123) g_s125_127) (subset g_s126_128 g_s95_96) (mem g_s127_129 g_s95_96) (mem g_s127_129 g_s126_128) (mem g_s128_130 g_s95_96) (not (mem g_s128_130 g_s126_128)) (mem g_s129_131 (|+->| NAT g_s95_96)) (mem g_s129_131 (perm g_s126_128)) (= (card g_s126_128) g_s130_132) (subset g_s131_133 INT) (subset g_s132_134 NAT) (subset g_s132_134 g_s131_133) (mem g_s133_135 g_s131_133) (not (mem g_s133_135 g_s132_134)) (= g_s134_136 INTEGER) (subset g_s135_137 INTEGER) (subset g_s135_137 g_s134_136) (mem g_s136_138 g_s134_136) (not (mem g_s136_138 g_s135_137)) (= g_s137_139 INTEGER) (= g_s138_140 NATURAL) (subset g_s138_140 g_s137_139) (mem g_s139_141 g_s138_140) (mem g_s140_142 g_s138_140) (mem g_s141_143 g_s137_139) (not (mem g_s141_143 g_s138_140)) (|<=i| g_s139_141 g_s140_142) (subset g_s142_144 g_s96_97) (mem g_s143_145 g_s96_97) (not (mem g_s143_145 g_s142_144)) (mem g_s144_146 (|+->| NAT g_s96_97)) (mem g_s144_146 (perm g_s142_144)) (subset g_s132_134 g_s135_137) (subset g_s145_147 g_s97_98) (not (mem g_s104_105 g_s145_147)) (= g_s145_147 (SET (mapplet g_s103_104 (mapplet g_s102_103 (mapplet g_s101_102 (mapplet g_s100_101 (mapplet g_s99_100 g_s98_99))))))) (mem g_s146_148 (|>->| g_s145_147 g_s86_87)) (= g_s146_148 (SET (mapplet (mapplet g_s103_104 g_s92_93) (mapplet (mapplet g_s102_103 g_s91_92) (mapplet (mapplet g_s101_102 g_s90_91) (mapplet (mapplet g_s100_101 g_s89_90) (mapplet (mapplet g_s99_100 g_s88_89) (mapplet g_s98_99 g_s87_88)))))))) (mem g_s147_149 (|-->| g_s97_98 g_s86_87)) (subset g_s148_150 g_s105_106) (mem g_s149_151 g_s105_106) (not (mem g_s149_151 g_s148_150)) (subset g_s150_152 g_s106_107) (mem g_s151_153 g_s106_107) (not (mem g_s151_153 g_s150_152)) (subset g_s152_154 g_s107_108) (mem g_s153_155 g_s107_108) (not (mem g_s153_155 g_s152_154)) (subset g_s154_156 g_s108_109) (mem g_s155_157 g_s108_109) (not (mem g_s155_157 g_s154_156)) (subset g_s156_159 g_s157_158) (not (mem g_s158_160 g_s156_159)) (= g_s156_159 (SET (mapplet g_s161_163 (mapplet g_s160_162 g_s159_161)))) (mem g_s162_164 (|+->| g_s154_156 g_s152_154)) (mem g_s163_165 (|+->| g_s152_154 g_s154_156)) (subset g_s164_166 g_s109_110) (mem g_s165_167 g_s109_110) (not (mem g_s165_167 g_s164_166)) (mem g_s166_168 (|+->| NAT g_s109_110)) (mem g_s166_168 (perm g_s164_166)) (subset g_s167_169 g_s110_111) (mem g_s168_170 g_s110_111) (not (mem g_s168_170 g_s167_169)) (mem g_s169_171 (|+->| NAT g_s110_111)) (mem g_s169_171 (perm g_s167_169)) (subset g_s170_172 g_s111_112) (mem g_s171_173 g_s111_112) (not (mem g_s171_173 g_s170_172)) (subset g_s172_174 g_s23_24) (not (mem g_s24_25 g_s172_174)) (= g_s172_174 (SET (mapplet g_s26_27 g_s25_26))) (subset g_s173_175 g_s112_113) (mem g_s174_176 g_s112_113) (not (mem g_s174_176 g_s173_175)) (mem g_s175_177 (|+->| NAT g_s112_113)) (mem g_s175_177 (perm g_s173_175)) (subset g_s176_178 g_s113_114) (mem g_s177_179 g_s113_114) (not (mem g_s177_179 g_s176_178)) (mem g_s178_180 (|+->| NAT g_s113_114)) (mem g_s178_180 (perm g_s176_178)) (mem g_s179_181 (|>->| g_s176_178 g_s121_123))))
(define-fun |def_seext| () Bool true)
(define-fun |def_lprp| () Bool true)
(define-fun |def_inprp| () Bool true)
(define-fun |def_inext| () Bool true)
(define-fun |def_inv| () Bool (and (mem g_s180_182 (|+->| g_s176_178 g_s152_154)) (mem g_s181_183 (|+->| g_s176_178 g_s145_147)) (mem g_s182_184 (|+->| g_s176_178 g_s164_166)) (subset g_s183_185 g_s176_178) (mem g_s184_186 (|+->| g_s176_178 g_s132_134)) (subset g_s185_187 g_s176_178) (mem g_s186_188 (|+->| g_s176_178 g_s116_117)) (subset g_s187_189 g_s176_178)))
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
(assert (not (mem empty (|+->| g_s176_178 g_s132_134))))
(check-sat)
(pop 1)
; PO 2 in group 0
(push 1)
(assert (not (mem empty (|+->| g_s176_178 g_s116_117))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 0
(push 1)
(assert (not (mem empty (|+->| g_s176_178 g_s152_154))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 0
(push 1)
(assert (not (mem empty (|+->| g_s176_178 g_s164_166))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 5 in group 0
(push 1)
(assert (not (mem (set_prod g_s176_178 (SET g_s98_99)) (|+->| g_s176_178 g_s145_147))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 6 in group 0
(push 1)
(assert (not (subset empty g_s176_178)))
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
(assert (mem g_s191_190 g_s113_114))
(assert (mem g_s191_190 g_s176_178))
(define-fun lh_1 () Bool (mem g_s191_190 (dom g_s180_182)))
(define-fun lh_2 () Bool (mem g_s192$1_191 g_s107_108))
; PO 1 in group 1
(assert (not (=> (and lh_1 lh_2) (mem g_s180_182 (|+->| (dom g_s180_182) (ran g_s180_182))))))
(set-info :status unknown)
(check-sat)
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
(assert (mem g_s191_190 g_s113_114))
(assert (mem g_s191_190 g_s176_178))
(define-fun lh_1 () Bool (mem g_s191_190 (dom g_s181_183)))
(define-fun lh_2 () Bool (mem g_s195$1_192 g_s97_98))
; PO 1 in group 2
(assert (not (=> (and lh_1 lh_2) (mem g_s181_183 (|+->| (dom g_s181_183) (ran g_s181_183))))))
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
(assert (mem g_s191_190 g_s113_114))
(assert (mem g_s191_190 g_s176_178))
(assert (mem g_s191_190 (dom g_s181_183)))
(define-fun lh_1 () Bool (mem g_s195$1_192 g_s97_98))
; PO 1 in group 3
(assert (not (=> lh_1 (mem g_s181_183 (|+->| (dom g_s181_183) (ran g_s181_183))))))
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
(assert (mem g_s191_190 g_s113_114))
(assert (mem g_s191_190 g_s176_178))
(define-fun lh_1 () Bool (mem g_s191_190 (dom g_s182_184)))
(define-fun lh_2 () Bool (mem g_s198$1_193 g_s109_110))
; PO 1 in group 4
(assert (not (=> (and lh_1 lh_2) (mem g_s182_184 (|+->| (dom g_s182_184) (ran g_s182_184))))))
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
(assert (mem g_s191_190 g_s113_114))
(assert (mem g_s191_190 g_s176_178))
(assert (mem g_s191_190 (dom g_s182_184)))
(define-fun lh_1 () Bool (mem g_s198$1_193 g_s109_110))
; PO 1 in group 5
(assert (not (=> lh_1 (mem g_s182_184 (|+->| (dom g_s182_184) (ran g_s182_184))))))
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
(assert (mem g_s191_190 g_s113_114))
(assert (mem g_s191_190 g_s176_178))
(define-fun lh_1 () Bool (mem g_s191_190 (dom g_s184_186)))
(define-fun lh_2 () Bool (mem g_s201$1_194 g_s131_133))
; PO 1 in group 6
(assert (not (=> (and lh_1 lh_2) (mem g_s184_186 (|+->| (dom g_s184_186) (ran g_s184_186))))))
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
(assert (mem g_s191_190 g_s113_114))
(assert (mem g_s191_190 g_s176_178))
(assert (mem g_s191_190 (dom g_s184_186)))
(define-fun lh_1 () Bool (mem g_s201$1_194 g_s131_133))
; PO 1 in group 7
(assert (not (=> lh_1 (mem g_s184_186 (|+->| (dom g_s184_186) (ran g_s184_186))))))
(set-info :status unknown)
(check-sat)
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
(assert (mem g_s191_190 g_s113_114))
(assert (mem g_s191_190 g_s176_178))
(define-fun lh_1 () Bool (mem g_s191_190 (dom g_s186_188)))
(define-fun lh_2 () Bool (mem g_s204$1_195 g_s114_116))
; PO 1 in group 8
(assert (not (=> (and lh_1 lh_2) (mem g_s186_188 (|+->| (dom g_s186_188) (ran g_s186_188))))))
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
(assert (mem g_s191_190 g_s113_114))
(assert (mem g_s191_190 g_s176_178))
(assert (mem g_s191_190 (dom g_s186_188)))
(define-fun lh_1 () Bool (mem g_s204$1_195 g_s114_116))
; PO 1 in group 9
(assert (not (=> lh_1 (mem g_s186_188 (|+->| (dom g_s186_188) (ran g_s186_188))))))
(set-info :status unknown)
(check-sat)
(pop 1)
(exit)