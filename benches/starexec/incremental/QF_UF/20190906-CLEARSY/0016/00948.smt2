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
(declare-fun e178 () U)
(declare-fun e187 () U)
(declare-fun e189 () U)
(declare-fun e191 () U)
(declare-fun e193 () U)
(declare-fun e195 () U)
(declare-fun e197 () U)
(declare-fun e199 () U)
(declare-fun e201 () U)
(declare-fun e203 () U)
(declare-fun e205 () U)
(declare-fun e207 () U)
(declare-fun e209 () U)
(declare-fun e211 () U)
(declare-fun e213 () U)
(declare-fun e215 () U)
(declare-fun e217 () U)
(declare-fun e219 () U)
(declare-fun e221 () U)
(declare-fun e223 () U)
(declare-fun e225 () U)
(declare-fun e227 () U)
(declare-fun e229 () U)
(declare-fun e231 () U)
(declare-fun e233 () U)
(declare-fun e235 () U)
(declare-fun e237 () U)
(declare-fun e239 () U)
(declare-fun e241 () U)
(declare-fun e243 () U)
(declare-fun e245 () U)
(declare-fun e247 () U)
(declare-fun e249 () U)
(declare-fun e251 () U)
(declare-fun e253 () U)
(declare-fun e255 () U)
(declare-fun e257 () U)
(declare-fun e259 () U)
(declare-fun e261 () U)
(declare-fun e263 () U)
(declare-fun e265 () U)
(declare-fun e267 () U)
(declare-fun e269 () U)
(declare-fun e271 () U)
(declare-fun e273 () U)
(declare-fun e275 () U)
(declare-fun e277 () U)
(declare-fun e279 () U)
(declare-fun e281 () U)
(declare-fun e283 () U)
(declare-fun e285 () U)
(declare-fun e287 () U)
(declare-fun e289 () U)
(declare-fun e291 () U)
(declare-fun e293 () U)
(declare-fun e295 () U)
(declare-fun e297 () U)
(declare-fun e299 () U)
(declare-fun e301 () U)
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
(declare-fun g_s117_118 () U)
(declare-fun g_s118_119 () U)
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
(declare-fun g_s132_133 () U)
(declare-fun g_s133_134 () U)
(declare-fun g_s134_135 () U)
(declare-fun g_s135_136 () U)
(declare-fun g_s136_137 () U)
(declare-fun g_s137_138 () U)
(declare-fun g_s138_139 () U)
(declare-fun g_s139_140 () U)
(declare-fun g_s14_15 () U)
(declare-fun g_s140_141 () U)
(declare-fun g_s141_142 () U)
(declare-fun g_s142_143 () U)
(declare-fun g_s143_144 () U)
(declare-fun g_s144_145 () U)
(declare-fun g_s145_146 () U)
(declare-fun g_s146_147 () U)
(declare-fun g_s147_148 () U)
(declare-fun g_s148_149 () U)
(declare-fun g_s149_150 () U)
(declare-fun g_s15_16 () U)
(declare-fun g_s150_151 () U)
(declare-fun g_s151_152 () U)
(declare-fun g_s152_153 () U)
(declare-fun g_s153_154 () U)
(declare-fun g_s154_155 () U)
(declare-fun g_s155_156 () U)
(declare-fun g_s156_157 () U)
(declare-fun g_s157_158 () U)
(declare-fun g_s158_159 () U)
(declare-fun g_s159_160 () U)
(declare-fun g_s16_17 () U)
(declare-fun g_s160_161 () U)
(declare-fun g_s161_162 () U)
(declare-fun g_s162_163 () U)
(declare-fun g_s163_164 () U)
(declare-fun g_s164_165 () U)
(declare-fun g_s165_166 () U)
(declare-fun g_s166_167 () U)
(declare-fun g_s167_168 () U)
(declare-fun g_s168_169 () U)
(declare-fun g_s169_170 () U)
(declare-fun g_s17_18 () U)
(declare-fun g_s170_171 () U)
(declare-fun g_s171_172 () U)
(declare-fun g_s172_173 () U)
(declare-fun g_s173_174 () U)
(declare-fun g_s176_177 () U)
(declare-fun g_s177_180 () U)
(declare-fun g_s179_182 () U)
(declare-fun g_s18_19 () U)
(declare-fun g_s181_183 () U)
(declare-fun g_s182_184 () U)
(declare-fun g_s183_185 () U)
(declare-fun g_s184_186 () U)
(declare-fun g_s185_188 () U)
(declare-fun g_s186_190 () U)
(declare-fun g_s187_192 () U)
(declare-fun g_s188_194 () U)
(declare-fun g_s189_196 () U)
(declare-fun g_s19_20 () U)
(declare-fun g_s190_198 () U)
(declare-fun g_s191_200 () U)
(declare-fun g_s192_202 () U)
(declare-fun g_s193_204 () U)
(declare-fun g_s194_206 () U)
(declare-fun g_s195_208 () U)
(declare-fun g_s196_210 () U)
(declare-fun g_s197_212 () U)
(declare-fun g_s198_214 () U)
(declare-fun g_s199_216 () U)
(declare-fun g_s2_3 () U)
(declare-fun g_s20_21 () U)
(declare-fun g_s200_218 () U)
(declare-fun g_s201_220 () U)
(declare-fun g_s202_222 () U)
(declare-fun g_s203_224 () U)
(declare-fun g_s204_226 () U)
(declare-fun g_s205_228 () U)
(declare-fun g_s206_230 () U)
(declare-fun g_s207_232 () U)
(declare-fun g_s208_234 () U)
(declare-fun g_s209_236 () U)
(declare-fun g_s21_22 () U)
(declare-fun g_s210_238 () U)
(declare-fun g_s211_240 () U)
(declare-fun g_s212_242 () U)
(declare-fun g_s213_244 () U)
(declare-fun g_s214_246 () U)
(declare-fun g_s215_248 () U)
(declare-fun g_s216_250 () U)
(declare-fun g_s217_252 () U)
(declare-fun g_s218_254 () U)
(declare-fun g_s219_256 () U)
(declare-fun g_s22_23 () U)
(declare-fun g_s220_258 () U)
(declare-fun g_s221_260 () U)
(declare-fun g_s222_262 () U)
(declare-fun g_s223_264 () U)
(declare-fun g_s224_266 () U)
(declare-fun g_s225_268 () U)
(declare-fun g_s226_270 () U)
(declare-fun g_s227_272 () U)
(declare-fun g_s228_274 () U)
(declare-fun g_s229_276 () U)
(declare-fun g_s23_24 () U)
(declare-fun g_s230_278 () U)
(declare-fun g_s231_280 () U)
(declare-fun g_s232_282 () U)
(declare-fun g_s233_284 () U)
(declare-fun g_s234_286 () U)
(declare-fun g_s235_288 () U)
(declare-fun g_s236_290 () U)
(declare-fun g_s237_292 () U)
(declare-fun g_s238_294 () U)
(declare-fun g_s239_296 () U)
(declare-fun g_s24_25 () U)
(declare-fun g_s240_298 () U)
(declare-fun g_s241_300 () U)
(declare-fun g_s242_302 () U)
(declare-fun g_s243_303 () U)
(declare-fun g_s244_304 () U)
(declare-fun g_s245_305 () U)
(declare-fun g_s246_306 () U)
(declare-fun g_s247_307 () U)
(declare-fun g_s248_308 () U)
(declare-fun g_s249_309 () U)
(declare-fun g_s25_26 () U)
(declare-fun g_s250_310 () U)
(declare-fun g_s251$1_311 () U)
(declare-fun g_s252$1_312 () U)
(declare-fun g_s253$1_313 () U)
(declare-fun g_s254$1_314 () U)
(declare-fun g_s255$1_315 () U)
(declare-fun g_s259_316 () U)
(declare-fun g_s259$1_317 () U)
(declare-fun g_s26_27 () U)
(declare-fun g_s260_318 () U)
(declare-fun g_s260$1_322 () U)
(declare-fun g_s263_319 () U)
(declare-fun g_s263$1_320 () U)
(declare-fun g_s264_321 () U)
(declare-fun g_s266_323 () U)
(declare-fun g_s266$1_324 () U)
(declare-fun g_s269_325 () U)
(declare-fun g_s269_327 () U)
(declare-fun g_s269$1_326 () U)
(declare-fun g_s269$1_328 () U)
(declare-fun g_s27_28 () U)
(declare-fun g_s271_329 () U)
(declare-fun g_s272$1_330 () U)
(declare-fun g_s276_331 () U)
(declare-fun g_s276$1_332 () U)
(declare-fun g_s277_333 () U)
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
(declare-fun e179 () U)
(declare-fun e181 () U)
(declare-fun e176 () U)
(declare-fun e175 () U)
; Defines
(define-fun |def_B definitions| () Bool (and (= NAT (interval e0 MaxInt)) (= INT (interval MinInt MaxInt))))
(define-fun |def_ctx| () Bool (and (= g_s0_1 (SET (mapplet g_s2_3 g_s1_2))) (= g_s3_4 (SET (mapplet g_s7_8 (mapplet g_s6_7 (mapplet g_s5_6 g_s4_5))))) (= g_s8_9 (SET (mapplet g_s12_13 (mapplet g_s11_12 (mapplet g_s10_11 g_s9_10))))) (= g_s13_14 (SET (mapplet g_s22_23 (mapplet g_s21_22 (mapplet g_s20_21 (mapplet g_s19_20 (mapplet g_s18_19 (mapplet g_s17_18 (mapplet g_s16_17 (mapplet g_s15_16 g_s14_15)))))))))) (= g_s23_24 (SET (mapplet g_s26_27 (mapplet g_s25_26 g_s24_25)))) (= g_s27_28 (SET (mapplet g_s29_30 g_s28_29))) (= g_s30_31 (SET (mapplet g_s33_34 (mapplet g_s32_33 g_s31_32)))) (= g_s34_35 (SET (mapplet g_s36_37 g_s35_36))) (= g_s37_38 (SET (mapplet g_s41_42 (mapplet g_s40_41 (mapplet g_s39_40 g_s38_39))))) (= g_s42_43 (SET (mapplet g_s44_45 g_s43_44))) (= g_s45_46 (SET (mapplet g_s48_49 (mapplet g_s47_48 g_s46_47)))) (= g_s49_50 (SET (mapplet g_s52_53 (mapplet g_s51_52 g_s50_51)))) (= g_s53_54 (SET (mapplet g_s55_56 g_s54_55))) (= g_s56_57 (SET (mapplet g_s59_60 (mapplet g_s58_59 g_s57_58)))) (= g_s60_61 (SET (mapplet g_s65_66 (mapplet g_s64_65 (mapplet g_s63_64 (mapplet g_s62_63 g_s61_62)))))) (= g_s66_67 (SET (mapplet g_s69_70 (mapplet g_s68_69 g_s67_68)))) (= g_s70_71 (SET (mapplet g_s73_74 (mapplet g_s72_73 g_s71_72)))) (= g_s74_75 (SET (mapplet g_s77_78 (mapplet g_s76_77 g_s75_76)))) (= g_s78_79 (SET (mapplet g_s81_82 (mapplet g_s80_81 g_s79_80)))) (= g_s82_83 (SET (mapplet g_s85_86 (mapplet g_s84_85 g_s83_84)))) (= g_s86_87 (SET (mapplet g_s93_94 (mapplet g_s92_93 (mapplet g_s91_92 (mapplet g_s90_91 (mapplet g_s89_90 (mapplet g_s88_89 g_s87_88)))))))) (= g_s94_95 (SET (mapplet g_s98_99 (mapplet g_s97_98 (mapplet g_s96_97 g_s95_96))))) (= g_s99_100 (SET (mapplet g_s103_104 (mapplet g_s102_103 (mapplet g_s101_102 g_s100_101))))) (= g_s104_105 (SET (mapplet g_s107_108 (mapplet g_s106_107 g_s105_106)))) (= g_s108_109 (SET (mapplet g_s112_113 (mapplet g_s111_112 (mapplet g_s110_111 g_s109_110))))) (= g_s113_114 (SET (mapplet g_s117_118 (mapplet g_s116_117 (mapplet g_s115_116 g_s114_115))))) (= g_s118_119 (SET (mapplet g_s122_123 (mapplet g_s121_122 (mapplet g_s120_121 g_s119_120))))) (= g_s123_124 (SET (mapplet g_s127_128 (mapplet g_s126_127 (mapplet g_s125_126 g_s124_125))))) (= g_s128_129 (SET (mapplet g_s131_132 (mapplet g_s130_131 g_s129_130)))) (= g_s132_133 (SET (mapplet g_s136_137 (mapplet g_s135_136 (mapplet g_s134_135 g_s133_134))))) (= g_s137_138 (SET (mapplet g_s140_141 (mapplet g_s139_140 g_s138_139)))) (= g_s141_142 (SET (mapplet g_s144_145 (mapplet g_s143_144 g_s142_143)))) (= g_s145_146 (SET (mapplet g_s152_153 (mapplet g_s151_152 (mapplet g_s150_151 (mapplet g_s149_150 (mapplet g_s148_149 (mapplet g_s147_148 g_s146_147)))))))) (= g_s153_154 (SET (mapplet g_s157_158 (mapplet g_s156_157 (mapplet g_s155_156 g_s154_155))))) (= g_s158_159 (SET (mapplet g_s162_163 (mapplet g_s161_162 (mapplet g_s160_161 g_s159_160))))) (not (= g_s163_164 empty)) (not (= g_s164_165 empty)) (not (= g_s165_166 empty)) (not (= g_s166_167 empty)) (not (= g_s167_168 empty)) (not (= g_s168_169 empty)) (not (= g_s169_170 empty)) (not (= g_s170_171 empty)) (not (= g_s171_172 empty)) (not (= g_s172_173 empty)) (mem g_s173_174 (|-->| (set_prod INTEGER NATURAL) INTEGER)) (= g_s173_174 (binary_union e176 e175)) (mem g_s176_177 (|-->| BOOL NAT)) (= g_s176_177 (SET (mapplet (mapplet FALSE e0) (mapplet TRUE e178)))) (= g_s177_180 e179) (= g_s179_182 e181)))
(define-fun |def_seext| () Bool (and (= g_s181_183 TRUE) (= g_s182_184 FALSE) (= g_s183_185 e0) (= g_s184_186 e178) (= g_s185_188 e187) (= g_s186_190 e189) (= g_s187_192 e191) (= g_s188_194 e193) (= g_s189_196 e195) (= g_s190_198 e197) (= g_s191_200 e199) (= g_s192_202 e201) (= g_s193_204 e203) (= g_s194_206 e205) (= g_s195_208 e207) (= g_s196_210 e209) (= g_s197_212 e211) (= g_s198_214 e213) (= g_s199_216 e215) (= g_s200_218 e217) (= g_s201_220 e219) (= g_s202_222 e221) (= g_s203_224 e223) (= g_s204_226 e225) (= g_s205_228 e227) (= g_s206_230 e229) (= g_s207_232 e231) (= g_s208_234 e233) (= g_s209_236 e235) (= g_s210_238 e237) (= g_s211_240 e239) (= g_s212_242 e241) (= g_s213_244 e243) (= g_s214_246 e245) (= g_s215_248 e247) (= g_s216_250 e249) (= g_s217_252 e251) (= g_s218_254 e253) (= g_s219_256 e255) (= g_s220_258 e257) (= g_s221_260 e259) (= g_s222_262 e261) (= g_s223_264 e263) (= g_s224_266 e265) (= g_s225_268 e267) (= g_s226_270 e269) (= g_s227_272 e271) (= g_s228_274 e273) (= g_s229_276 e275) (= g_s230_278 e277) (= g_s231_280 e279) (= g_s232_282 e281) (= g_s233_284 e283) (= g_s234_286 e285) (= g_s235_288 e287) (= g_s236_290 e289) (= g_s237_292 e291) (= g_s238_294 e293) (= g_s239_296 e295) (= g_s240_298 e297) (= g_s241_300 e299) (= g_s242_302 e301) (mem g_s243_303 g_s171_172)))
(define-fun |def_mchcst| () Bool true)
(define-fun |def_aprp| () Bool (and (subset g_s244_304 g_s99_100) (not (mem g_s100_101 g_s244_304)) (= g_s244_304 (SET (mapplet g_s103_104 g_s102_103))) (subset g_s245_305 g_s99_100) (not (mem g_s100_101 g_s245_305)) (= g_s245_305 (SET (mapplet g_s103_104 (mapplet g_s102_103 g_s101_102)))) (mem g_s246_306 (|>->>| g_s244_304 g_s244_304)) (= (binary_inter g_s246_306 (id g_s244_304)) empty) (mem g_s247_307 (|>->| g_s30_31 g_s99_100)) (not (mem (apply g_s247_307 g_s31_32) g_s244_304)) (mem g_s248_308 (|>->>| g_s45_46 (set_diff g_s99_100 (SET g_s101_102)))) (mem g_s249_309 (|>->>| (set_diff g_s99_100 (SET g_s101_102)) g_s45_46)) (= g_s248_308 (inverse g_s249_309)) (not (mem (apply g_s248_308 g_s46_47) g_s244_304)) (mem g_s250_310 (|-->| g_s37_38 g_s30_31)) (= (apply g_s250_310 g_s41_42) g_s31_32)))
(define-fun |def_abs| () Bool true)
(define-fun |def_inv| () Bool (and (mem g_s251$1_311 g_s99_100) (mem g_s252$1_312 g_s99_100) (mem g_s253$1_313 g_s99_100) (mem g_s254$1_314 g_s45_46) (mem g_s255$1_315 g_s30_31)))
(define-fun |def_ass| () Bool true)
(define-fun |def_sets| () Bool true)
(define-fun |def_imlprp| () Bool (and (= g_s244_304 (SET (mapplet g_s103_104 g_s102_103))) (= g_s246_306 (SET (mapplet (mapplet g_s103_104 g_s102_103) (mapplet g_s102_103 g_s103_104)))) (= g_s247_307 (SET (mapplet (mapplet g_s33_34 g_s103_104) (mapplet (mapplet g_s32_33 g_s102_103) (mapplet g_s31_32 g_s100_101))))) (= g_s248_308 (SET (mapplet (mapplet g_s48_49 g_s103_104) (mapplet (mapplet g_s47_48 g_s102_103) (mapplet g_s46_47 g_s100_101))))) (= g_s249_309 (SET (mapplet (mapplet g_s103_104 g_s48_49) (mapplet (mapplet g_s102_103 g_s47_48) (mapplet g_s100_101 g_s46_47))))) (= g_s250_310 (SET (mapplet (mapplet g_s41_42 g_s31_32) (mapplet (mapplet g_s40_41 g_s33_34) (mapplet (mapplet g_s39_40 g_s32_33) (mapplet g_s38_39 g_s31_32))))))))
(define-fun |def_imprp| () Bool true)
(define-fun |def_imext| () Bool true)
; PO group 0 
(push 1)
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_imprp|)
; PO 1 in group 0
(push 1)
(assert (not (not (mem g_s100_101 (SET (mapplet g_s103_104 g_s102_103))))))
(check-sat)
(pop 1)
; PO 2 in group 0
(push 1)
(assert (not (not (mem g_s100_101 (SET (mapplet g_s103_104 (mapplet g_s102_103 g_s101_102)))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 0
(push 1)
(assert (not (not (mem (apply (SET (mapplet (mapplet g_s33_34 g_s103_104) (mapplet (mapplet g_s32_33 g_s102_103) (mapplet g_s31_32 g_s100_101)))) g_s31_32) (SET (mapplet g_s103_104 g_s102_103))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 0
(push 1)
(assert (not (not (mem (apply (SET (mapplet (mapplet g_s48_49 g_s103_104) (mapplet (mapplet g_s47_48 g_s102_103) (mapplet g_s46_47 g_s100_101)))) g_s46_47) (SET (mapplet g_s103_104 g_s102_103))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 5 in group 0
(push 1)
(assert (not (mem (SET (mapplet (mapplet g_s103_104 g_s102_103) (mapplet g_s102_103 g_s103_104))) (|>->>| (SET (mapplet g_s103_104 g_s102_103)) (SET (mapplet g_s103_104 g_s102_103))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 6 in group 0
(push 1)
(assert (not (mem (SET (mapplet (mapplet g_s33_34 g_s103_104) (mapplet (mapplet g_s32_33 g_s102_103) (mapplet g_s31_32 g_s100_101)))) (|>->| g_s30_31 g_s99_100))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 7 in group 0
(push 1)
(assert (not (mem (SET (mapplet (mapplet g_s48_49 g_s103_104) (mapplet (mapplet g_s47_48 g_s102_103) (mapplet g_s46_47 g_s100_101)))) (|>->>| g_s45_46 (set_diff g_s99_100 (SET g_s101_102))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 8 in group 0
(push 1)
(assert (not (mem (SET (mapplet (mapplet g_s103_104 g_s48_49) (mapplet (mapplet g_s102_103 g_s47_48) (mapplet g_s100_101 g_s46_47)))) (|>->>| (set_diff g_s99_100 (SET g_s101_102)) g_s45_46))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 9 in group 0
(push 1)
(assert (not (mem (SET (mapplet (mapplet g_s41_42 g_s31_32) (mapplet (mapplet g_s40_41 g_s33_34) (mapplet (mapplet g_s39_40 g_s32_33) (mapplet g_s38_39 g_s31_32))))) (|-->| g_s37_38 g_s30_31))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 10 in group 0
(push 1)
(assert (not (subset (SET (mapplet g_s103_104 g_s102_103)) g_s99_100)))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 11 in group 0
(push 1)
(assert (not (subset (SET (mapplet g_s103_104 (mapplet g_s102_103 g_s101_102))) g_s99_100)))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 12 in group 0
(push 1)
(assert (not (= (binary_inter (SET (mapplet (mapplet g_s103_104 g_s102_103) (mapplet g_s102_103 g_s103_104))) (id (SET (mapplet g_s103_104 g_s102_103)))) empty)))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 13 in group 0
(push 1)
(assert (not (= (apply (SET (mapplet (mapplet g_s41_42 g_s31_32) (mapplet (mapplet g_s40_41 g_s33_34) (mapplet (mapplet g_s39_40 g_s32_33) (mapplet g_s38_39 g_s31_32))))) g_s41_42) g_s31_32)))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 14 in group 0
(push 1)
(assert (not (= (SET (mapplet (mapplet g_s48_49 g_s103_104) (mapplet (mapplet g_s47_48 g_s102_103) (mapplet g_s46_47 g_s100_101)))) (inverse (SET (mapplet (mapplet g_s103_104 g_s48_49) (mapplet (mapplet g_s102_103 g_s47_48) (mapplet g_s100_101 g_s46_47))))))))
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
(assert (= g_s259$1_317 g_s259_316))
(define-fun lh_1 () Bool (mem g_s260_318 g_s99_100))
(define-fun lh_2 () Bool (mem g_s260_318 g_s244_304))
(define-fun lh_3 () Bool (= g_s260_318 g_s102_103))
(define-fun lh_4 () Bool (= g_s260_318 g_s103_104))
(define-fun lh_5 () Bool (not (= g_s260_318 g_s102_103)))
(define-fun lh_6 () Bool (not (= g_s260_318 g_s103_104)))
; PO 1 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_4) (= g_s102_103 (apply g_s246_306 g_s260_318)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (= g_s103_104 (apply g_s246_306 g_s260_318)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_5 lh_6) (= g_s100_101 (apply g_s246_306 g_s260_318)))))
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
(assert (= g_s263$1_320 g_s263_319))
(define-fun lh_1 () Bool (mem g_s264_321 g_s30_31))
(define-fun lh_2 () Bool (= g_s264_321 g_s32_33))
(define-fun lh_3 () Bool (= g_s264_321 g_s33_34))
(define-fun lh_4 () Bool (not (= g_s264_321 g_s32_33)))
(define-fun lh_5 () Bool (not (= g_s264_321 g_s33_34)))
; PO 1 in group 2
(push 1)
(assert (not (=> (and lh_1 lh_2) (= g_s102_103 (apply g_s247_307 g_s264_321)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 2
(push 1)
(assert (not (=> (and lh_1 lh_3) (= g_s103_104 (apply g_s247_307 g_s264_321)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 2
(push 1)
(assert (not (=> (and lh_1 lh_4 lh_5) (= g_s100_101 (apply g_s247_307 g_s264_321)))))
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
(assert |def_inv|)
(assert |def_ass|)
(assert (= g_s260$1_322 g_s260_318))
(define-fun lh_1 () Bool (mem g_s266_323 g_s45_46))
(define-fun lh_2 () Bool (= g_s266_323 g_s47_48))
(define-fun lh_3 () Bool (= g_s266_323 g_s48_49))
(define-fun lh_4 () Bool (not (= g_s266_323 g_s47_48)))
(define-fun lh_5 () Bool (not (= g_s266_323 g_s48_49)))
; PO 1 in group 3
(push 1)
(assert (not (=> (and lh_1 lh_2) (= g_s102_103 (apply g_s248_308 g_s266_323)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 3
(push 1)
(assert (not (=> (and lh_1 lh_3) (= g_s103_104 (apply g_s248_308 g_s266_323)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 3
(push 1)
(assert (not (=> (and lh_1 lh_4 lh_5) (= g_s100_101 (apply g_s248_308 g_s266_323)))))
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
(assert (= g_s266$1_324 g_s266_323))
(define-fun lh_1 () Bool (mem g_s260_318 g_s99_100))
(define-fun lh_2 () Bool (mem g_s260_318 g_s244_304))
(define-fun lh_3 () Bool (= g_s260_318 g_s102_103))
(define-fun lh_4 () Bool (= g_s260_318 g_s103_104))
(define-fun lh_5 () Bool (not (= g_s260_318 g_s102_103)))
(define-fun lh_6 () Bool (not (= g_s260_318 g_s103_104)))
; PO 1 in group 4
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (= g_s47_48 (apply g_s249_309 g_s260_318)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 4
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_4) (= g_s48_49 (apply g_s249_309 g_s260_318)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 4
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_5 lh_6) (= g_s46_47 (apply g_s249_309 g_s260_318)))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 5 
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
(assert (= g_s269$1_326 g_s269_325))
(define-fun lh_1 () Bool (mem g_s260_318 g_s99_100))
; PO 1 in group 5
(assert (not (=> lh_1 (= (bool (or (= (bool (= g_s260_318 g_s102_103)) TRUE) (= (bool (= g_s260_318 g_s103_104)) TRUE))) (bool (mem g_s260_318 g_s244_304))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO group 6 
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
(assert (= g_s269$1_328 g_s269_327))
(define-fun lh_1 () Bool (mem g_s271_329 g_s163_164))
(define-fun lh_2 () Bool (mem g_s272$1_330 INTEGER))
(define-fun lh_3 () Bool (= g_s272$1_330 g_s184_186))
; PO 1 in group 6
(assert (not (=> (and lh_1 lh_2 lh_3) (mem g_s102_103 (binary_inter g_s99_100 g_s244_304)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO group 7 
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
(assert (= g_s269$1_326 g_s269_325))
(define-fun lh_1 () Bool (mem g_s260_318 g_s99_100))
; PO 1 in group 7
(assert (not (=> lh_1 (= (bool (not (= g_s260_318 g_s100_101))) (bool (mem g_s260_318 g_s245_305))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO group 8 
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
(assert (= g_s269$1_328 g_s269_327))
(define-fun lh_1 () Bool (mem g_s271_329 g_s163_164))
(define-fun lh_2 () Bool (mem g_s272$1_330 INTEGER))
(define-fun lh_3 () Bool (= g_s272$1_330 g_s184_186))
; PO 1 in group 8
(assert (not (=> (and lh_1 lh_2 lh_3) (mem g_s102_103 (binary_inter g_s99_100 g_s245_305)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO group 9 
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
(assert (= g_s276$1_332 g_s276_331))
(define-fun lh_1 () Bool (mem g_s277_333 g_s37_38))
(define-fun lh_2 () Bool (= g_s277_333 g_s38_39))
(define-fun lh_3 () Bool (= g_s277_333 g_s39_40))
(define-fun lh_4 () Bool (= g_s277_333 g_s40_41))
(define-fun lh_5 () Bool (= g_s277_333 g_s41_42))
(define-fun lh_6 () Bool (not (= g_s277_333 g_s38_39)))
(define-fun lh_7 () Bool (not (= g_s277_333 g_s39_40)))
(define-fun lh_8 () Bool (not (= g_s277_333 g_s40_41)))
(define-fun lh_9 () Bool (not (= g_s277_333 g_s41_42)))
; PO 1 in group 9
(push 1)
(assert (not (=> (and lh_1 lh_2) (= g_s31_32 (apply g_s250_310 g_s277_333)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 9
(push 1)
(assert (not (=> (and lh_1 lh_5) (= g_s31_32 (apply g_s250_310 g_s277_333)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 9
(push 1)
(assert (not (=> (and lh_1 lh_4) (= g_s33_34 (apply g_s250_310 g_s277_333)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 9
(push 1)
(assert (not (=> (and lh_1 lh_3) (= g_s32_33 (apply g_s250_310 g_s277_333)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 5 in group 9
(push 1)
(assert (not (=> (and lh_1 lh_6 lh_7 lh_8 lh_9) (= g_s31_32 (apply g_s250_310 g_s277_333)))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
(exit)