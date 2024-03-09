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
(declare-fun e40 () U)
(declare-fun e0 () U)
(declare-fun e56 () U)
(declare-fun e155 () U)
(declare-fun e50 () U)
(declare-fun e104 () U)
(declare-fun e76 () U)
(declare-fun e109 () U)
(declare-fun e293 () U)
(declare-fun e107 () U)
(declare-fun e94 () U)
(declare-fun e74 () U)
(declare-fun e298 () U)
(declare-fun e183 () U)
(declare-fun e295 () U)
(declare-fun e101 () U)
(declare-fun e92 () U)
(declare-fun e69 () U)
(declare-fun e72 () U)
(declare-fun e154 () U)
(declare-fun e44 () U)
(declare-fun e188 () U)
(declare-fun e164 () U)
(declare-fun e42 () U)
(declare-fun e224 () U)
(declare-fun g_s0_1 () U)
(declare-fun g_s1_2 () U)
(declare-fun g_s10_11 () U)
(declare-fun g_s100_115 () U)
(declare-fun g_s101_116 () U)
(declare-fun g_s102_117 () U)
(declare-fun g_s103_118 () U)
(declare-fun g_s104_119 () U)
(declare-fun g_s105_120 () U)
(declare-fun g_s106_121 () U)
(declare-fun g_s107_122 () U)
(declare-fun g_s108_123 () U)
(declare-fun g_s109_124 () U)
(declare-fun g_s11_12 () U)
(declare-fun g_s110_125 () U)
(declare-fun g_s111_126 () U)
(declare-fun g_s112_127 () U)
(declare-fun g_s113_128 () U)
(declare-fun g_s114_129 () U)
(declare-fun g_s115_130 () U)
(declare-fun g_s116_131 () U)
(declare-fun g_s117_132 () U)
(declare-fun g_s118_133 () U)
(declare-fun g_s119_134 () U)
(declare-fun g_s12_13 () U)
(declare-fun g_s120_135 () U)
(declare-fun g_s121_136 () U)
(declare-fun g_s122_137 () U)
(declare-fun g_s123_138 () U)
(declare-fun g_s124_139 () U)
(declare-fun g_s125_140 () U)
(declare-fun g_s126_141 () U)
(declare-fun g_s127_142 () U)
(declare-fun g_s128_143 () U)
(declare-fun g_s129_144 () U)
(declare-fun g_s13_14 () U)
(declare-fun g_s130_145 () U)
(declare-fun g_s131_146 () U)
(declare-fun g_s132_147 () U)
(declare-fun g_s133_148 () U)
(declare-fun g_s134_149 () U)
(declare-fun g_s135_150 () U)
(declare-fun g_s136_151 () U)
(declare-fun g_s137_152 () U)
(declare-fun g_s138_153 () U)
(declare-fun g_s139_156 () U)
(declare-fun g_s14_15 () U)
(declare-fun g_s140_157 () U)
(declare-fun g_s141_158 () U)
(declare-fun g_s142_159 () U)
(declare-fun g_s143_160 () U)
(declare-fun g_s144_161 () U)
(declare-fun g_s145_162 () U)
(declare-fun g_s146_163 () U)
(declare-fun g_s147_165 () U)
(declare-fun g_s148_166 () U)
(declare-fun g_s149_167 () U)
(declare-fun g_s15_16 () U)
(declare-fun g_s150_168 () U)
(declare-fun g_s151_169 () U)
(declare-fun g_s152_170 () U)
(declare-fun g_s153_171 () U)
(declare-fun g_s154_173 () U)
(declare-fun g_s155_172 () U)
(declare-fun g_s156_174 () U)
(declare-fun g_s157_175 () U)
(declare-fun g_s158_176 () U)
(declare-fun g_s159_177 () U)
(declare-fun g_s16_17 () U)
(declare-fun g_s160_178 () U)
(declare-fun g_s161_179 () U)
(declare-fun g_s162_180 () U)
(declare-fun g_s163_181 () U)
(declare-fun g_s164_182 () U)
(declare-fun g_s165_184 () U)
(declare-fun g_s166_185 () U)
(declare-fun g_s167_186 () U)
(declare-fun g_s168_187 () U)
(declare-fun g_s169_189 () U)
(declare-fun g_s17_18 () U)
(declare-fun g_s170_190 () U)
(declare-fun g_s171_191 () U)
(declare-fun g_s172_192 () U)
(declare-fun g_s173_193 () U)
(declare-fun g_s174_194 () U)
(declare-fun g_s175_195 () U)
(declare-fun g_s176_196 () U)
(declare-fun g_s177_197 () U)
(declare-fun g_s178_198 () U)
(declare-fun g_s179_199 () U)
(declare-fun g_s18_19 () U)
(declare-fun g_s180_200 () U)
(declare-fun g_s181_201 () U)
(declare-fun g_s182_202 () U)
(declare-fun g_s183_203 () U)
(declare-fun g_s184_204 () U)
(declare-fun g_s185_205 () U)
(declare-fun g_s186_206 () U)
(declare-fun g_s187_207 () U)
(declare-fun g_s188_208 () U)
(declare-fun g_s189_209 () U)
(declare-fun g_s19_20 () U)
(declare-fun g_s190_210 () U)
(declare-fun g_s191_211 () U)
(declare-fun g_s192_212 () U)
(declare-fun g_s193_213 () U)
(declare-fun g_s194_214 () U)
(declare-fun g_s195_215 () U)
(declare-fun g_s196_216 () U)
(declare-fun g_s197_217 () U)
(declare-fun g_s198_218 () U)
(declare-fun g_s199_219 () U)
(declare-fun g_s2_3 () U)
(declare-fun g_s20_21 () U)
(declare-fun g_s200_220 () U)
(declare-fun g_s201_221 () U)
(declare-fun g_s202_222 () U)
(declare-fun g_s203_223 () U)
(declare-fun g_s204_225 () U)
(declare-fun g_s205_226 () U)
(declare-fun g_s206_227 () U)
(declare-fun g_s207_228 () U)
(declare-fun g_s208_229 () U)
(declare-fun g_s209_230 () U)
(declare-fun g_s21_22 () U)
(declare-fun g_s210_231 () U)
(declare-fun g_s211_232 () U)
(declare-fun g_s212_233 () U)
(declare-fun g_s213_234 () U)
(declare-fun g_s214_235 () U)
(declare-fun g_s215_236 () U)
(declare-fun g_s216_238 () U)
(declare-fun g_s217_237 () U)
(declare-fun g_s218_239 () U)
(declare-fun g_s219_240 () U)
(declare-fun g_s22_23 () U)
(declare-fun g_s220_241 () U)
(declare-fun g_s221_242 () U)
(declare-fun g_s222_243 () U)
(declare-fun g_s223_244 () U)
(declare-fun g_s224_245 () U)
(declare-fun g_s225_246 () U)
(declare-fun g_s226_247 () U)
(declare-fun g_s227_248 () U)
(declare-fun g_s228_249 () U)
(declare-fun g_s229_250 () U)
(declare-fun g_s23_24 () U)
(declare-fun g_s230_251 () U)
(declare-fun g_s231_252 () U)
(declare-fun g_s232_253 () U)
(declare-fun g_s233_254 () U)
(declare-fun g_s234_255 () U)
(declare-fun g_s235_256 () U)
(declare-fun g_s236_257 () U)
(declare-fun g_s237_258 () U)
(declare-fun g_s238_259 () U)
(declare-fun g_s239_260 () U)
(declare-fun g_s24_25 () U)
(declare-fun g_s240_261 () U)
(declare-fun g_s241_262 () U)
(declare-fun g_s242_263 () U)
(declare-fun g_s243_264 () U)
(declare-fun g_s244_265 () U)
(declare-fun g_s245_266 () U)
(declare-fun g_s246_267 () U)
(declare-fun g_s247_268 () U)
(declare-fun g_s248_269 () U)
(declare-fun g_s249_270 () U)
(declare-fun g_s25_26 () U)
(declare-fun g_s250_271 () U)
(declare-fun g_s251_272 () U)
(declare-fun g_s252_273 () U)
(declare-fun g_s253_274 () U)
(declare-fun g_s254_275 () U)
(declare-fun g_s255_276 () U)
(declare-fun g_s256_277 () U)
(declare-fun g_s257_278 () U)
(declare-fun g_s258_279 () U)
(declare-fun g_s259_280 () U)
(declare-fun g_s26_27 () U)
(declare-fun g_s260_281 () U)
(declare-fun g_s261_282 () U)
(declare-fun g_s262_283 () U)
(declare-fun g_s263_284 () U)
(declare-fun g_s264_285 () U)
(declare-fun g_s265_286 () U)
(declare-fun g_s266_287 () U)
(declare-fun g_s267_288 () U)
(declare-fun g_s268_289 () U)
(declare-fun g_s269_290 () U)
(declare-fun g_s27_28 () U)
(declare-fun g_s270_291 () U)
(declare-fun g_s271_292 () U)
(declare-fun g_s272_294 () U)
(declare-fun g_s273_296 () U)
(declare-fun g_s274_297 () U)
(declare-fun g_s28_29 () U)
(declare-fun g_s282_299 () U)
(declare-fun g_s283_300 () U)
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
(declare-fun g_s39_41 () U)
(declare-fun g_s4_5 () U)
(declare-fun g_s40_43 () U)
(declare-fun g_s41_45 () U)
(declare-fun g_s42_46 () U)
(declare-fun g_s43_47 () U)
(declare-fun g_s44_48 () U)
(declare-fun g_s45_49 () U)
(declare-fun g_s46_51 () U)
(declare-fun g_s47_52 () U)
(declare-fun g_s48_53 () U)
(declare-fun g_s49_54 () U)
(declare-fun g_s5_6 () U)
(declare-fun g_s50_55 () U)
(declare-fun g_s51_57 () U)
(declare-fun g_s52_58 () U)
(declare-fun g_s53_59 () U)
(declare-fun g_s54_60 () U)
(declare-fun g_s55_61 () U)
(declare-fun g_s56_62 () U)
(declare-fun g_s57_63 () U)
(declare-fun g_s58_64 () U)
(declare-fun g_s59_65 () U)
(declare-fun g_s6_7 () U)
(declare-fun g_s60_66 () U)
(declare-fun g_s61_67 () U)
(declare-fun g_s62_68 () U)
(declare-fun g_s63_70 () U)
(declare-fun g_s64_71 () U)
(declare-fun g_s65_73 () U)
(declare-fun g_s66_75 () U)
(declare-fun g_s67_77 () U)
(declare-fun g_s68_78 () U)
(declare-fun g_s69_79 () U)
(declare-fun g_s7_8 () U)
(declare-fun g_s70_80 () U)
(declare-fun g_s71_81 () U)
(declare-fun g_s72_82 () U)
(declare-fun g_s73_83 () U)
(declare-fun g_s74_84 () U)
(declare-fun g_s75_85 () U)
(declare-fun g_s76_86 () U)
(declare-fun g_s77_87 () U)
(declare-fun g_s78_88 () U)
(declare-fun g_s79_89 () U)
(declare-fun g_s8_9 () U)
(declare-fun g_s80_90 () U)
(declare-fun g_s81_91 () U)
(declare-fun g_s82_93 () U)
(declare-fun g_s83_95 () U)
(declare-fun g_s84_96 () U)
(declare-fun g_s85_97 () U)
(declare-fun g_s86_98 () U)
(declare-fun g_s87_99 () U)
(declare-fun g_s88_100 () U)
(declare-fun g_s89_102 () U)
(declare-fun g_s9_10 () U)
(declare-fun g_s90_103 () U)
(declare-fun g_s91_105 () U)
(declare-fun g_s92_106 () U)
(declare-fun g_s93_108 () U)
(declare-fun g_s96_111 () U)
(declare-fun g_s97_112 () U)
(declare-fun g_s98_113 () U)
(declare-fun g_s99_114 () U)
(declare-fun e110 () U)
; Defines
(define-fun |def_B definitions| () Bool (and (= NAT (interval e0 MaxInt)) (= INT (interval MinInt MaxInt))))
(define-fun |def_ctx| () Bool (and (= g_s0_1 (SET (mapplet g_s7_8 (mapplet g_s6_7 (mapplet g_s5_6 (mapplet g_s4_5 (mapplet g_s3_4 (mapplet g_s2_3 g_s1_2)))))))) (= g_s8_9 (SET (mapplet g_s16_17 (mapplet g_s15_16 (mapplet g_s14_15 (mapplet g_s13_14 (mapplet g_s12_13 (mapplet g_s11_12 (mapplet g_s10_11 g_s9_10))))))))) (= g_s17_18 (SET (mapplet g_s19_20 g_s18_19))) (= g_s20_21 (SET (mapplet g_s26_27 (mapplet g_s25_26 (mapplet g_s24_25 (mapplet g_s23_24 (mapplet g_s22_23 g_s21_22))))))) (= g_s27_28 (SET (mapplet g_s30_31 (mapplet g_s29_30 g_s28_29)))) (= g_s31_32 (SET (mapplet g_s38_39 (mapplet g_s37_38 (mapplet g_s36_37 (mapplet g_s35_36 (mapplet g_s34_35 (mapplet g_s33_34 g_s32_33)))))))) (= g_s39_41 (interval e0 e40)) (= g_s40_43 (interval e0 e42)) (= g_s41_45 (interval e0 e44)) (mem g_s42_46 g_s41_45) (mem g_s43_47 g_s41_45) (mem g_s44_48 g_s41_45) (mem g_s45_49 g_s41_45) (= (SET (mapplet g_s45_49 (mapplet g_s44_48 (mapplet g_s43_47 g_s42_46)))) (interval e0 e50)) (mem g_s46_51 g_s41_45) (mem g_s47_52 g_s41_45) (mem g_s48_53 g_s41_45) (mem g_s49_54 g_s41_45) (mem g_s50_55 g_s41_45) (= g_s51_57 (|-->| (interval e56 e50) g_s41_45)) (mem g_s52_58 g_s41_45) (mem g_s53_59 g_s41_45) (mem g_s54_60 g_s41_45) (mem g_s55_61 g_s41_45) (mem g_s56_62 g_s41_45) (mem g_s57_63 g_s41_45) (mem g_s58_64 g_s41_45) (mem g_s59_65 g_s41_45) (mem g_s60_66 g_s41_45) (mem g_s54_60 g_s41_45) (not (mem g_s52_58 (SET (mapplet g_s54_60 (mapplet g_s60_66 (mapplet g_s59_65 (mapplet g_s58_64 (mapplet g_s57_63 (mapplet g_s56_62 (mapplet g_s55_61 g_s53_59)))))))))) (not (mem g_s53_59 (SET (mapplet g_s54_60 (mapplet g_s60_66 (mapplet g_s59_65 (mapplet g_s58_64 (mapplet g_s57_63 (mapplet g_s56_62 g_s55_61))))))))) (not (mem g_s55_61 (SET (mapplet g_s54_60 (mapplet g_s60_66 (mapplet g_s59_65 (mapplet g_s58_64 (mapplet g_s57_63 g_s56_62)))))))) (not (mem g_s56_62 (SET (mapplet g_s54_60 (mapplet g_s60_66 (mapplet g_s59_65 (mapplet g_s58_64 g_s57_63))))))) (not (mem g_s57_63 (SET (mapplet g_s54_60 (mapplet g_s60_66 (mapplet g_s59_65 g_s58_64)))))) (not (mem g_s58_64 (SET (mapplet g_s54_60 (mapplet g_s60_66 g_s59_65))))) (not (mem g_s59_65 (SET (mapplet g_s54_60 g_s60_66)))) (not (mem g_s60_66 (SET g_s54_60))) (mem g_s61_67 g_s41_45) (mem g_s62_68 g_s41_45) (|<=i| e69 g_s62_68) (mem g_s63_70 g_s41_45) (mem g_s64_71 g_s41_45) (= g_s64_71 (|-i| g_s63_70 e56)) (|<=i| g_s64_71 e72) (mem g_s65_73 g_s41_45) (|<=i| (|+i| g_s64_71 e74) g_s62_68) (mem g_s66_75 g_s51_57) (= g_s66_75 (set_prod (interval e56 e50) (SET e44))) (mem g_s67_77 (|-->| (interval e0 e76) g_s41_45)) (= g_s67_77 (set_prod (interval e0 e76) (SET e0))) (mem g_s68_78 (|-->| (interval e0 e76) g_s41_45)) (= g_s68_78 (set_prod (interval e0 e76) (SET e44))) (mem g_s69_79 g_s41_45) (mem g_s70_80 g_s41_45) (mem g_s71_81 g_s41_45) (mem g_s72_82 g_s41_45) (mem g_s73_83 g_s41_45) (mem g_s74_84 g_s41_45) (mem g_s75_85 g_s41_45) (mem g_s76_86 g_s41_45) (mem g_s77_87 g_s40_43) (mem g_s78_88 g_s39_41) (mem g_s79_89 (|-->| (interval e0 e44) g_s40_43)) (mem g_s80_90 g_s41_45) (mem g_s81_91 g_s41_45) (|<=i| g_s81_91 e92) (mem g_s82_93 g_s41_45) (|<=i| g_s82_93 e94) (mem g_s83_95 g_s41_45) (|<=i| g_s83_95 e94) (mem g_s84_96 g_s40_43) (mem g_s85_97 g_s40_43) (mem g_s86_98 (|-->| (interval e0 e44) g_s40_43)) (mem g_s87_99 g_s41_45) (mem g_s88_100 g_s41_45) (|<=i| e101 g_s87_99) (= g_s88_100 (|-i| g_s87_99 e56)) (mem g_s89_102 (|-->| (interval e0 e50) g_s41_45)) (mem g_s90_103 (|-->| (interval e0 e50) g_s41_45)) (mem g_s91_105 (|-->| (interval e0 e104) g_s41_45)) (mem g_s92_106 g_s41_45) (|<=i| e56 g_s92_106) (|<=i| g_s92_106 e107) (mem g_s93_108 g_s41_45) (|<=i| g_s93_108 e109) (= e110 e44) (mem g_s96_111 g_s41_45) (mem g_s97_112 g_s39_41) (mem g_s98_113 g_s39_41) (mem g_s99_114 g_s39_41) (mem g_s100_115 g_s39_41) (mem g_s101_116 g_s39_41) (mem g_s102_117 g_s39_41) (mem g_s103_118 g_s39_41) (mem g_s104_119 g_s39_41) (mem g_s105_120 g_s39_41) (mem g_s106_121 g_s39_41) (mem g_s107_122 g_s39_41) (mem g_s108_123 g_s39_41) (mem g_s109_124 g_s39_41) (mem g_s110_125 g_s39_41) (mem g_s111_126 g_s39_41) (mem g_s112_127 g_s39_41) (mem g_s113_128 g_s39_41) (mem g_s114_129 g_s39_41) (mem g_s115_130 g_s39_41) (mem g_s116_131 g_s39_41) (mem g_s117_132 g_s39_41) (mem g_s118_133 g_s39_41) (mem g_s119_134 g_s39_41) (mem g_s120_135 g_s39_41) (mem g_s121_136 g_s39_41) (mem g_s122_137 g_s39_41) (mem g_s123_138 g_s39_41) (mem g_s124_139 g_s39_41) (mem g_s125_140 g_s39_41) (mem g_s126_141 g_s39_41) (mem g_s127_142 g_s39_41) (mem g_s128_143 g_s39_41) (mem g_s129_144 g_s39_41) (mem g_s130_145 g_s39_41) (mem g_s131_146 g_s39_41) (mem g_s132_147 g_s39_41) (mem g_s133_148 g_s40_43) (mem g_s134_149 g_s40_43) (mem g_s135_150 g_s39_41) (mem g_s136_151 g_s39_41) (mem g_s137_152 g_s41_45) (mem g_s138_153 g_s41_45) (|<=i| g_s138_153 e154) (|<=i| e155 g_s138_153) (mem g_s139_156 g_s40_43) (|<=i| e56 g_s139_156) (|<i| g_s139_156 e42) (mem g_s140_157 g_s41_45) (|<=i| e56 g_s140_157) (mem g_s141_158 g_s40_43) (mem g_s142_159 g_s40_43) (mem g_s143_160 g_s40_43) (mem g_s144_161 g_s40_43) (mem g_s145_162 g_s40_43) (mem g_s146_163 g_s40_43) (|<=i| g_s146_163 e164) (mem g_s147_165 g_s40_43) (|<=i| g_s147_165 e164) (mem g_s148_166 g_s40_43) (mem g_s149_167 (|-->| (interval e0 e109) g_s40_43)) (mem g_s150_168 (|-->| (interval e0 e109) g_s40_43)) (mem g_s151_169 g_s40_43) (|<=i| g_s151_169 e164) (mem g_s152_170 g_s40_43) (|<=i| g_s152_170 e164) (mem g_s153_171 g_s39_41) (|<i| g_s153_171 (|-i| g_s154_173 g_s155_172)) (mem g_s156_174 g_s40_43) (mem g_s157_175 g_s40_43) (mem g_s158_176 g_s41_45) (mem g_s159_177 g_s41_45) (mem g_s160_178 g_s41_45) (mem g_s161_179 g_s41_45) (|<=i| e56 g_s161_179) (mem g_s162_180 g_s41_45) (mem g_s163_181 g_s41_45) (mem g_s164_182 g_s41_45) (|<=i| e155 g_s164_182) (|<=i| g_s164_182 e183) (mem g_s165_184 g_s41_45) (|<=i| g_s165_184 e154) (mem g_s166_185 g_s41_45) (mem g_s167_186 g_s41_45) (mem g_s168_187 g_s40_43) (|<=i| g_s168_187 e188) (mem g_s169_189 g_s39_41) (mem g_s170_190 g_s39_41) (mem g_s171_191 g_s39_41) (mem g_s172_192 g_s39_41) (mem g_s173_193 g_s39_41) (mem g_s174_194 g_s39_41) (mem g_s175_195 g_s39_41) (mem g_s176_196 g_s40_43) (mem g_s177_197 g_s40_43) (mem g_s178_198 g_s40_43) (mem g_s179_199 g_s40_43) (mem g_s180_200 g_s39_41) (mem g_s181_201 g_s39_41) (mem g_s182_202 g_s40_43) (mem g_s183_203 g_s40_43) (mem g_s184_204 g_s40_43) (mem g_s185_205 g_s39_41) (mem g_s186_206 g_s39_41) (mem g_s187_207 g_s39_41) (mem g_s188_208 g_s39_41) (mem g_s189_209 g_s39_41) (mem g_s190_210 g_s39_41) (mem g_s191_211 g_s39_41) (mem g_s192_212 g_s39_41) (mem g_s193_213 g_s39_41) (mem g_s194_214 g_s39_41) (mem g_s195_215 g_s39_41) (mem g_s196_216 g_s39_41) (mem g_s197_217 g_s39_41) (mem g_s198_218 g_s39_41) (mem g_s199_219 g_s39_41) (mem g_s200_220 g_s39_41) (mem g_s201_221 g_s39_41) (mem g_s202_222 g_s39_41) (mem g_s203_223 g_s39_41) (|<=i| g_s203_223 e224) (mem g_s204_225 g_s41_45) (|<=i| e56 g_s204_225) (|<=i| g_s204_225 e154) (mem g_s205_226 g_s41_45) (mem g_s206_227 g_s39_41)))
(define-fun |def_seext| () Bool (and (mem g_s207_228 (|-->| (interval e0 g_s62_68) g_s41_45)) (mem g_s208_229 g_s41_45) (mem g_s209_230 g_s41_45) (mem g_s210_231 g_s41_45) (mem g_s211_232 g_s41_45) (mem g_s212_233 g_s41_45) (mem g_s213_234 g_s41_45) (mem g_s214_235 g_s40_43) (mem g_s215_236 (|-->| (interval e0 e155) g_s41_45)) (= g_s216_238 (composition g_s217_237 g_s215_236)) (mem g_s218_239 g_s39_41) (mem g_s219_240 g_s40_43) (mem g_s220_241 (|-->| (interval e0 e155) g_s41_45)) (mem g_s221_242 (|-->| (interval e0 e155) g_s41_45)) (mem g_s222_243 g_s39_41) (mem g_s223_244 g_s39_41) (mem g_s224_245 g_s41_45) (mem g_s225_246 g_s41_45) (mem g_s226_247 (|-->| (interval e0 (|-i| g_s225_246 e56)) g_s41_45)) (mem g_s227_248 g_s40_43) (mem g_s228_249 g_s40_43) (mem g_s229_250 g_s40_43) (mem g_s230_251 g_s41_45) (mem g_s231_252 g_s41_45) (mem g_s232_253 g_s41_45) (mem g_s233_254 (|-->| (interval e0 (|-i| g_s232_253 e56)) g_s41_45)) (mem g_s234_255 g_s41_45) (mem g_s235_256 (|-->| (interval e0 e76) g_s41_45)) (mem g_s236_257 g_s41_45) (mem g_s237_258 (|-->| (interval e0 e155) g_s41_45)) (mem g_s238_259 g_s41_45) (mem g_s239_260 (|-->| (interval e0 e76) g_s41_45)) (mem g_s240_261 (|-->| (interval e0 e155) g_s41_45)) (mem g_s241_262 g_s39_41) (mem g_s242_263 g_s40_43) (mem g_s243_264 g_s40_43) (mem g_s244_265 g_s40_43) (mem g_s245_266 g_s39_41) (mem g_s246_267 g_s39_41) (mem g_s247_268 g_s39_41) (mem g_s248_269 g_s39_41) (mem g_s249_270 g_s41_45) (mem g_s250_271 g_s41_45) (mem g_s251_272 (|-->| (interval e56 g_s93_108) g_s40_43)) (mem g_s252_273 (|-->| (interval e56 g_s93_108) g_s40_43)) (mem g_s253_274 (|-->| (interval e56 g_s93_108) g_s41_45)) (mem g_s254_275 (|-->| (interval e56 g_s93_108) g_s40_43)) (mem g_s255_276 g_s40_43) (mem g_s256_277 (|-->| (interval e56 g_s92_106) g_s41_45)) (mem g_s257_278 (|-->| (interval e56 g_s92_106) g_s41_45)) (mem g_s258_279 (|-->| (interval e56 g_s92_106) g_s41_45)) (mem g_s259_280 (|-->| (interval e56 g_s92_106) g_s41_45)) (= g_s260_281 (composition g_s217_237 g_s237_258)) (= g_s261_282 (composition g_s217_237 g_s240_261)) (mem g_s262_283 (|-->| (interval e0 e76) g_s41_45)) (mem g_s263_284 g_s41_45) (mem g_s264_285 g_s39_41) (mem g_s265_286 g_s41_45) (mem g_s266_287 (|-->| (interval e0 e76) g_s41_45)) (mem g_s267_288 g_s40_43) (mem g_s268_289 g_s40_43) (mem g_s269_290 g_s41_45) (mem g_s270_291 (|-->| (interval e0 g_s62_68) g_s41_45)) (mem g_s271_292 g_s40_43) (mem g_s272_294 (|-->| (interval e0 e293) g_s41_45)) (|<i| (|+i| g_s82_93 g_s83_95) e295) (mem g_s216_238 g_s51_57) (mem g_s260_281 g_s51_57) (mem g_s261_282 g_s51_57)))
(define-fun |def_lprp| () Bool true)
(define-fun |def_inprp| () Bool true)
(define-fun |def_inext| () Bool true)
(define-fun |def_inv| () Bool (and (mem g_s273_296 g_s41_45) (mem g_s274_297 g_s51_57)))
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
(assert (not (mem e0 g_s41_45)))
(check-sat)
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
; PO 1 in group 1
(assert (not (mem (imin (SET (mapplet (|+i| g_s273_296 e56) e44))) g_s41_45)))
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
(assert (= g_s213_234 g_s59_65))
(assert (= g_s212_233 e298))
; PO 1 in group 2
(assert (not (mem (composition g_s217_237 g_s237_258) g_s51_57)))
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
; PO 1 in group 3
(push 1)
(assert (not (not (= (SET (mapplet (|+i| g_s273_296 e56) e44)) empty))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 3
(push 1)
(assert (not (mem (binary_inter (SET (mapplet (|+i| g_s273_296 e56) e44)) (set_diff INTEGER NATURAL)) (FIN INTEGER))))
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
(assert (mem g_s282_299 g_s41_45))
(assert (and (|>=i| g_s282_299 e0) (|<=i| g_s282_299 e155)))
(assert (mem (|+i| g_s282_299 e56) (dom g_s274_297)))
(assert (mem g_s283_300 g_s41_45))
; PO 1 in group 4
(assert (not (mem g_s274_297 (|+->| (dom g_s274_297) (ran g_s274_297)))))
(set-info :status unknown)
(check-sat)
(pop 1)
(exit)