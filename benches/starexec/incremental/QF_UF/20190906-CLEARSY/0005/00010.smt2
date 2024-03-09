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
(declare-fun e260 () U)
(declare-fun e155 () U)
(declare-fun e0 () U)
(declare-fun e204 () U)
(declare-fun e159 () U)
(declare-fun e203 () U)
(declare-fun e232 () U)
(declare-fun e206 () U)
(declare-fun e381 () U)
(declare-fun e212 () U)
(declare-fun e257 () U)
(declare-fun e207 () U)
(declare-fun e231 () U)
(declare-fun e321 () U)
(declare-fun e322 () U)
(declare-fun e233 () U)
(declare-fun e249 () U)
(declare-fun e251 () U)
(declare-fun e247 () U)
(declare-fun e319 () U)
(declare-fun e263 () U)
(declare-fun e320 () U)
(declare-fun e282 () U)
(declare-fun e229 () U)
(declare-fun e157 () U)
(declare-fun e338 () U)
(declare-fun e283 () U)
(declare-fun e156 () U)
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
(declare-fun g_s142_147 () U)
(declare-fun g_s143_144 () U)
(declare-fun g_s144_146 () U)
(declare-fun g_s145_145 () U)
(declare-fun g_s146_143 () U)
(declare-fun g_s147_149 () U)
(declare-fun g_s148_148 () U)
(declare-fun g_s149_150 () U)
(declare-fun g_s15_16 () U)
(declare-fun g_s150_151 () U)
(declare-fun g_s151_152 () U)
(declare-fun g_s152_153 () U)
(declare-fun g_s153_154 () U)
(declare-fun g_s154_158 () U)
(declare-fun g_s155_160 () U)
(declare-fun g_s156_161 () U)
(declare-fun g_s157_162 () U)
(declare-fun g_s158_163 () U)
(declare-fun g_s159_164 () U)
(declare-fun g_s16_17 () U)
(declare-fun g_s160_165 () U)
(declare-fun g_s161_166 () U)
(declare-fun g_s162_167 () U)
(declare-fun g_s163_168 () U)
(declare-fun g_s164_169 () U)
(declare-fun g_s165_170 () U)
(declare-fun g_s166_171 () U)
(declare-fun g_s167_172 () U)
(declare-fun g_s168_173 () U)
(declare-fun g_s169_174 () U)
(declare-fun g_s17_18 () U)
(declare-fun g_s170_175 () U)
(declare-fun g_s171_176 () U)
(declare-fun g_s172_177 () U)
(declare-fun g_s173_178 () U)
(declare-fun g_s174_179 () U)
(declare-fun g_s175_180 () U)
(declare-fun g_s176_181 () U)
(declare-fun g_s177_182 () U)
(declare-fun g_s178_183 () U)
(declare-fun g_s179_184 () U)
(declare-fun g_s18_19 () U)
(declare-fun g_s180_185 () U)
(declare-fun g_s181_186 () U)
(declare-fun g_s182_187 () U)
(declare-fun g_s187_205 () U)
(declare-fun g_s188_208 () U)
(declare-fun g_s189_209 () U)
(declare-fun g_s19_20 () U)
(declare-fun g_s190_210 () U)
(declare-fun g_s191_211 () U)
(declare-fun g_s192_213 () U)
(declare-fun g_s193_214 () U)
(declare-fun g_s194_215 () U)
(declare-fun g_s195_216 () U)
(declare-fun g_s196_217 () U)
(declare-fun g_s197_218 () U)
(declare-fun g_s198_219 () U)
(declare-fun g_s199_220 () U)
(declare-fun g_s2_3 () U)
(declare-fun g_s20_21 () U)
(declare-fun g_s200_221 () U)
(declare-fun g_s201_222 () U)
(declare-fun g_s202_223 () U)
(declare-fun g_s203_224 () U)
(declare-fun g_s204_225 () U)
(declare-fun g_s205_226 () U)
(declare-fun g_s206_227 () U)
(declare-fun g_s207_228 () U)
(declare-fun g_s208_230 () U)
(declare-fun g_s209_234 () U)
(declare-fun g_s21_22 () U)
(declare-fun g_s210_235 () U)
(declare-fun g_s211_236 () U)
(declare-fun g_s212_237 () U)
(declare-fun g_s213_238 () U)
(declare-fun g_s214_239 () U)
(declare-fun g_s215_240 () U)
(declare-fun g_s216_241 () U)
(declare-fun g_s217_242 () U)
(declare-fun g_s218_243 () U)
(declare-fun g_s219_244 () U)
(declare-fun g_s22_23 () U)
(declare-fun g_s220_245 () U)
(declare-fun g_s221_246 () U)
(declare-fun g_s222_248 () U)
(declare-fun g_s223_250 () U)
(declare-fun g_s224_252 () U)
(declare-fun g_s225_253 () U)
(declare-fun g_s226_254 () U)
(declare-fun g_s227_255 () U)
(declare-fun g_s228_256 () U)
(declare-fun g_s229_259 () U)
(declare-fun g_s23_24 () U)
(declare-fun g_s230_258 () U)
(declare-fun g_s231_261 () U)
(declare-fun g_s232_262 () U)
(declare-fun g_s233_264 () U)
(declare-fun g_s234_265 () U)
(declare-fun g_s235_266 () U)
(declare-fun g_s236_267 () U)
(declare-fun g_s237_268 () U)
(declare-fun g_s238_269 () U)
(declare-fun g_s239_270 () U)
(declare-fun g_s24_25 () U)
(declare-fun g_s240_271 () U)
(declare-fun g_s241_272 () U)
(declare-fun g_s242_273 () U)
(declare-fun g_s243_274 () U)
(declare-fun g_s244_275 () U)
(declare-fun g_s245_276 () U)
(declare-fun g_s246_277 () U)
(declare-fun g_s247_278 () U)
(declare-fun g_s248_279 () U)
(declare-fun g_s249_280 () U)
(declare-fun g_s25_26 () U)
(declare-fun g_s250_281 () U)
(declare-fun g_s251_284 () U)
(declare-fun g_s252_285 () U)
(declare-fun g_s253_286 () U)
(declare-fun g_s254_287 () U)
(declare-fun g_s255_288 () U)
(declare-fun g_s256_289 () U)
(declare-fun g_s257_290 () U)
(declare-fun g_s258_291 () U)
(declare-fun g_s259_292 () U)
(declare-fun g_s26_27 () U)
(declare-fun g_s260_293 () U)
(declare-fun g_s261_294 () U)
(declare-fun g_s262_295 () U)
(declare-fun g_s263_296 () U)
(declare-fun g_s264_297 () U)
(declare-fun g_s265_298 () U)
(declare-fun g_s266_299 () U)
(declare-fun g_s267_300 () U)
(declare-fun g_s268_301 () U)
(declare-fun g_s269_302 () U)
(declare-fun g_s27_28 () U)
(declare-fun g_s270_303 () U)
(declare-fun g_s271_304 () U)
(declare-fun g_s272_305 () U)
(declare-fun g_s273_306 () U)
(declare-fun g_s274_307 () U)
(declare-fun g_s275_308 () U)
(declare-fun g_s276_309 () U)
(declare-fun g_s277_310 () U)
(declare-fun g_s278_311 () U)
(declare-fun g_s279_312 () U)
(declare-fun g_s28_29 () U)
(declare-fun g_s280_313 () U)
(declare-fun g_s281_314 () U)
(declare-fun g_s282_315 () U)
(declare-fun g_s283_316 () U)
(declare-fun g_s284_317 () U)
(declare-fun g_s285_318 () U)
(declare-fun g_s286_323 () U)
(declare-fun g_s287_324 () U)
(declare-fun g_s288_325 () U)
(declare-fun g_s289_326 () U)
(declare-fun g_s29_30 () U)
(declare-fun g_s290_327 () U)
(declare-fun g_s291_328 () U)
(declare-fun g_s292_329 () U)
(declare-fun g_s293_330 () U)
(declare-fun g_s294_331 () U)
(declare-fun g_s295_332 () U)
(declare-fun g_s296_333 () U)
(declare-fun g_s297_334 () U)
(declare-fun g_s298_335 () U)
(declare-fun g_s299_336 () U)
(declare-fun g_s3_4 () U)
(declare-fun g_s30_31 () U)
(declare-fun g_s300_337 () U)
(declare-fun g_s301_339 () U)
(declare-fun g_s302_340 () U)
(declare-fun g_s303_341 () U)
(declare-fun g_s304_342 () U)
(declare-fun g_s305_343 () U)
(declare-fun g_s306_344 () U)
(declare-fun g_s307_345 () U)
(declare-fun g_s308_346 () U)
(declare-fun g_s309_347 () U)
(declare-fun g_s31_32 () U)
(declare-fun g_s310_348 () U)
(declare-fun g_s311_349 () U)
(declare-fun g_s312_350 () U)
(declare-fun g_s313_351 () U)
(declare-fun g_s314_352 () U)
(declare-fun g_s315_353 () U)
(declare-fun g_s316_354 () U)
(declare-fun g_s317_355 () U)
(declare-fun g_s318_356 () U)
(declare-fun g_s319_357 () U)
(declare-fun g_s32_33 () U)
(declare-fun g_s320_358 () U)
(declare-fun g_s321_359 () U)
(declare-fun g_s322_360 () U)
(declare-fun g_s323_361 () U)
(declare-fun g_s324_362 () U)
(declare-fun g_s325_363 () U)
(declare-fun g_s326_364 () U)
(declare-fun g_s327_365 () U)
(declare-fun g_s328_366 () U)
(declare-fun g_s329_367 () U)
(declare-fun g_s33_34 () U)
(declare-fun g_s330_368 () U)
(declare-fun g_s331_369 () U)
(declare-fun g_s333_370 () U)
(declare-fun g_s333$1_371 () U)
(declare-fun g_s334$1_372 () U)
(declare-fun g_s334$2_378 () U)
(declare-fun g_s335$1_373 () U)
(declare-fun g_s335$2_379 () U)
(declare-fun g_s336$1_374 () U)
(declare-fun g_s337$1_375 () U)
(declare-fun g_s338$1_376 () U)
(declare-fun g_s338$2_380 () U)
(declare-fun g_s339$1_377 () U)
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
(declare-fun e194 () U)
(declare-fun e195 () U)
(declare-fun e196 () U)
(declare-fun e188 () U)
(declare-fun e191 () U)
(declare-fun e190 () U)
(declare-fun e193 () U)
(declare-fun e189 () U)
(declare-fun e192 () U)
(declare-fun e200 () U)
(declare-fun e201 () U)
(declare-fun e202 () U)
(declare-fun e197 () U)
(declare-fun e198 () U)
(declare-fun e199 () U)
; Defines
(define-fun |def_B definitions| () Bool (and (= NAT (interval e0 MaxInt)) (= INT (interval MinInt MaxInt))))
(define-fun |def_ctx| () Bool (and (= g_s0_1 (SET (mapplet g_s2_3 g_s1_2))) (= g_s3_4 (SET (mapplet g_s51_52 (mapplet g_s50_51 (mapplet g_s49_50 (mapplet g_s48_49 (mapplet g_s47_48 (mapplet g_s46_47 (mapplet g_s45_46 (mapplet g_s44_45 (mapplet g_s43_44 (mapplet g_s42_43 (mapplet g_s41_42 (mapplet g_s40_41 (mapplet g_s39_40 (mapplet g_s38_39 (mapplet g_s37_38 (mapplet g_s36_37 (mapplet g_s35_36 (mapplet g_s34_35 (mapplet g_s33_34 (mapplet g_s32_33 (mapplet g_s31_32 (mapplet g_s30_31 (mapplet g_s29_30 (mapplet g_s28_29 (mapplet g_s27_28 (mapplet g_s26_27 (mapplet g_s25_26 (mapplet g_s24_25 (mapplet g_s23_24 (mapplet g_s22_23 (mapplet g_s21_22 (mapplet g_s20_21 (mapplet g_s19_20 (mapplet g_s18_19 (mapplet g_s17_18 (mapplet g_s16_17 (mapplet g_s15_16 (mapplet g_s14_15 (mapplet g_s13_14 (mapplet g_s12_13 (mapplet g_s11_12 (mapplet g_s10_11 (mapplet g_s9_10 (mapplet g_s8_9 (mapplet g_s7_8 (mapplet g_s6_7 (mapplet g_s5_6 g_s4_5))))))))))))))))))))))))))))))))))))))))))))))))) (= g_s52_53 (SET (mapplet g_s60_61 (mapplet g_s59_60 (mapplet g_s58_59 (mapplet g_s57_58 (mapplet g_s56_57 (mapplet g_s55_56 (mapplet g_s54_55 g_s53_54))))))))) (= g_s61_62 (SET (mapplet g_s88_89 (mapplet g_s87_88 (mapplet g_s86_87 (mapplet g_s85_86 (mapplet g_s84_85 (mapplet g_s83_84 (mapplet g_s82_83 (mapplet g_s81_82 (mapplet g_s80_81 (mapplet g_s79_80 (mapplet g_s78_79 (mapplet g_s77_78 (mapplet g_s76_77 (mapplet g_s75_76 (mapplet g_s74_75 (mapplet g_s73_74 (mapplet g_s72_73 (mapplet g_s71_72 (mapplet g_s70_71 (mapplet g_s69_70 (mapplet g_s68_69 (mapplet g_s67_68 (mapplet g_s66_67 (mapplet g_s65_66 (mapplet g_s64_65 (mapplet g_s63_64 g_s62_63)))))))))))))))))))))))))))) (= g_s89_90 (SET (mapplet g_s91_92 g_s90_91))) (= g_s92_93 (SET (mapplet g_s101_102 (mapplet g_s100_101 (mapplet g_s99_100 (mapplet g_s98_99 (mapplet g_s97_98 (mapplet g_s96_97 (mapplet g_s95_96 (mapplet g_s94_95 g_s93_94)))))))))) (= g_s102_103 (SET (mapplet g_s105_106 (mapplet g_s104_105 g_s103_104)))) (= g_s106_107 (SET (mapplet g_s108_109 g_s107_108))) (= g_s109_110 (SET (mapplet g_s116_117 (mapplet g_s115_116 (mapplet g_s114_115 (mapplet g_s113_114 (mapplet g_s112_113 (mapplet g_s111_112 g_s110_111)))))))) (= g_s117_118 (SET (mapplet g_s126_127 (mapplet g_s125_126 (mapplet g_s124_125 (mapplet g_s123_124 (mapplet g_s122_123 (mapplet g_s121_122 (mapplet g_s120_121 (mapplet g_s119_120 g_s118_119)))))))))) (= g_s127_128 (SET (mapplet g_s131_132 (mapplet g_s130_131 (mapplet g_s129_130 g_s128_129))))) (= g_s132_133 (SET (mapplet g_s135_136 (mapplet g_s134_135 g_s133_134)))) (= g_s136_137 (SET (mapplet g_s141_142 (mapplet g_s140_141 (mapplet g_s139_140 (mapplet g_s138_139 g_s137_138)))))) (mem g_s142_147 (|-->| (set_prod (set_prod (set_prod g_s143_144 (|-->| (interval e0 g_s144_146) g_s143_144)) g_s145_145) g_s143_144) g_s146_143)) (mem g_s147_149 (|-->| (set_prod (set_prod (set_prod g_s143_144 (|-->| (interval e0 g_s148_148) g_s143_144)) g_s145_145) g_s143_144) g_s146_143)) (mem g_s149_150 g_s143_144) (mem g_s150_151 g_s146_143) (mem g_s151_152 g_s145_145) (mem g_s152_153 g_s145_145) (mem g_s153_154 g_s145_145) (= g_s149_150 e155) (= g_s150_151 e156) (= g_s151_152 e157) (and (|>=i| g_s152_153 e0) (|<=i| g_s152_153 g_s151_152)) (and (|>=i| g_s153_154 e0) (|<=i| g_s153_154 g_s151_152)) (not (= g_s152_153 g_s153_154)) (= g_s154_158 (SET (mapplet g_s153_154 g_s152_153))) (|<=i| g_s152_153 e159) (|<=i| g_s153_154 e159) (= g_s155_160 (SET (mapplet (mapplet FALSE g_s153_154) (mapplet TRUE g_s152_153)))) (= g_s143_144 (interval e0 e155)) (= g_s146_143 (interval e0 e156)) (= g_s145_145 (interval e0 e157)) (mem g_s156_161 (|-->| (set_prod g_s143_144 g_s145_145) g_s143_144)) (mem g_s157_162 (|-->| (set_prod g_s143_144 g_s145_145) g_s143_144)) (mem g_s158_163 (|-->| g_s143_144 g_s143_144)) (mem g_s159_164 (|-->| (set_prod g_s143_144 g_s143_144) g_s143_144)) (mem g_s160_165 (|-->| (set_prod g_s143_144 g_s143_144) g_s143_144)) (mem g_s161_166 (|-->| (set_prod g_s143_144 g_s143_144) g_s143_144)) (mem g_s162_167 (|-->| (set_prod g_s146_143 g_s145_145) g_s146_143)) (mem g_s163_168 (|-->| (set_prod g_s146_143 g_s145_145) g_s146_143)) (mem g_s164_169 (|-->| g_s146_143 g_s146_143)) (mem g_s165_170 (|-->| (set_prod g_s146_143 g_s146_143) g_s146_143)) (mem g_s166_171 (|-->| (set_prod g_s146_143 g_s146_143) g_s146_143)) (mem g_s167_172 (|-->| (set_prod g_s146_143 g_s146_143) g_s146_143)) (mem g_s168_173 (|-->| (set_prod g_s145_145 g_s145_145) g_s145_145)) (mem g_s169_174 (|-->| (set_prod g_s145_145 g_s145_145) g_s145_145)) (mem g_s170_175 (|-->| g_s145_145 g_s145_145)) (mem g_s171_176 (|-->| (set_prod g_s145_145 g_s145_145) g_s145_145)) (mem g_s172_177 (|-->| (set_prod g_s145_145 g_s145_145) g_s145_145)) (mem g_s173_178 (|-->| (set_prod g_s145_145 g_s145_145) g_s145_145)) (mem g_s174_179 (|-->| (set_prod g_s143_144 g_s143_144) g_s143_144)) (mem g_s175_180 (|-->| (set_prod g_s143_144 g_s143_144) g_s143_144)) (mem g_s176_181 (|-->| (set_prod g_s143_144 g_s143_144) g_s143_144)) (mem g_s177_182 (|-->| (set_prod g_s146_143 g_s146_143) g_s146_143)) (mem g_s178_183 (|-->| (set_prod g_s146_143 g_s146_143) g_s146_143)) (mem g_s179_184 (|-->| (set_prod g_s146_143 g_s146_143) g_s146_143)) (mem g_s180_185 (|-->| (set_prod g_s145_145 g_s145_145) g_s145_145)) (mem g_s181_186 (|-->| (set_prod g_s145_145 g_s145_145) g_s145_145)) (mem g_s182_187 (|-->| (set_prod g_s145_145 g_s145_145) g_s145_145)) (= g_s156_161 e188) (= g_s162_167 e189) (= g_s168_173 e190) (= g_s157_162 e191) (= g_s163_168 e192) (= g_s169_174 e193) (= g_s174_179 e194) (= g_s175_180 e195) (= g_s176_181 e196) (= g_s177_182 e197) (= g_s178_183 e198) (= g_s179_184 e199) (= g_s180_185 e200) (= g_s181_186 e201) (= g_s182_187 e202) (= g_s187_205 (|-->| (interval e204 e203) g_s145_145)) (mem g_s188_208 (|-->| (set_prod (interval e0 e207) (interval e0 e206)) g_s145_145)) (mem g_s189_209 (|-->| (set_prod (interval e0 e207) (interval e0 e159)) g_s145_145)) (mem g_s190_210 (|-->| (set_prod (interval e0 e207) (interval e0 e159)) g_s145_145)) (mem g_s191_211 g_s145_145) (|<=i| e212 g_s191_211) (mem g_s192_213 (|-->| (interval e0 e207) g_s146_143)) (mem g_s193_214 (|-->| (interval e0 e207) g_s146_143)) (mem g_s194_215 g_s143_144) (mem g_s195_216 g_s145_145) (mem g_s196_217 g_s145_145) (mem g_s197_218 g_s145_145) (mem g_s198_219 g_s145_145) (mem g_s199_220 g_s145_145) (mem g_s200_221 g_s145_145) (mem g_s201_222 g_s145_145) (mem g_s202_223 g_s145_145) (mem g_s203_224 g_s145_145) (mem g_s204_225 g_s146_143) (not (= g_s203_224 g_s199_220)) (mem g_s205_226 g_s145_145) (mem g_s206_227 g_s145_145) (mem g_s207_228 g_s145_145) (|<=i| g_s207_228 e229) (mem g_s208_230 g_s145_145) (|<=i| (|+i| g_s207_228 e231) g_s206_227) (|<=i| (|+i| g_s208_230 e232) g_s206_227) (|<=i| e233 g_s206_227) (mem g_s209_234 g_s187_205) (= g_s209_234 (set_prod (interval e204 e203) (SET e157))) (mem g_s210_235 g_s145_145) (mem g_s211_236 g_s145_145) (mem g_s212_237 g_s145_145) (mem g_s213_238 g_s145_145) (mem g_s214_239 g_s145_145) (mem g_s215_240 g_s145_145) (mem g_s216_241 g_s145_145) (mem g_s217_242 g_s145_145) (mem g_s218_243 g_s145_145) (mem g_s219_244 g_s143_144) (mem g_s220_245 (|-->| (interval e0 e157) g_s146_143)) (mem g_s221_246 g_s145_145) (|<=i| g_s221_246 e247) (mem g_s222_248 g_s145_145) (|<i| g_s222_248 e249) (mem g_s223_250 g_s145_145) (|<i| g_s223_250 e249) (|<i| (|+i| g_s222_248 g_s223_250) e251) (mem g_s224_252 g_s146_143) (mem g_s225_253 g_s145_145) (mem g_s226_254 g_s145_145) (mem g_s227_255 g_s145_145) (mem g_s228_256 g_s145_145) (|<=i| e257 g_s226_254) (|<=i| g_s226_254 e247) (|<=i| (|+i| g_s229_259 g_s230_258) (idiv (|*i| (|*i| g_s221_246 g_s191_211) (|-i| e251 g_s223_250)) e251)) (|<=i| e0 (|-i| (|+i| e156 g_s230_258) (idiv (|*i| (|*i| g_s221_246 g_s191_211) (|-i| e251 g_s223_250)) e251))) (|<=i| (|+i| g_s229_259 g_s230_258) (|*i| g_s221_246 g_s191_211)) (|<=i| (idiv (|*i| (|*i| g_s221_246 g_s191_211) (|-i| e251 g_s222_248)) e251) (|+i| (idiv (|*i| (|*i| g_s221_246 g_s191_211) (|+i| e251 g_s223_250)) e251) e204)) (|<=i| (|*i| g_s191_211 (|-i| e251 g_s223_250)) g_s149_150) (|<=i| (idiv (|*i| g_s221_246 (|*i| g_s191_211 (|-i| e251 g_s223_250))) e251) e156) (|<=i| g_s229_259 (idiv (|*i| (|*i| g_s221_246 g_s191_211) (|-i| e251 g_s223_250)) e251)) (|<=i| (|*i| g_s221_246 g_s191_211) e156) (|<=i| e0 (|-i| (|+i| e204 (|*i| g_s221_246 g_s191_211)) (idiv (|*i| (|*i| g_s221_246 g_s191_211) (|-i| (|-i| e251 g_s223_250) g_s222_248)) e251))) (|<=i| (idiv (|*i| (|*i| g_s221_246 g_s191_211) (|-i| e251 g_s223_250)) e251) (|*i| g_s221_246 g_s191_211)) (|<=i| e0 (|-i| (|+i| e204 (idiv (|*i| (|*i| g_s221_246 g_s191_211) (|-i| e251 g_s223_250)) e251)) (idiv (|*i| (|*i| g_s221_246 g_s191_211) (|-i| (|-i| e251 g_s223_250) g_s222_248)) e251))) (|<=i| (|*i| g_s221_246 g_s191_211) (idiv (|*i| (|*i| g_s221_246 g_s191_211) (|+i| e251 g_s223_250)) e251)) (|<=i| e0 (|-i| (|+i| e204 (|*i| g_s221_246 g_s191_211)) (idiv (|*i| (|*i| g_s221_246 g_s191_211) (|-i| e251 g_s222_248)) e251))) (|<=i| e0 (|+i| e204 (|*i| g_s221_246 g_s191_211))) (|<=i| e0 (|-i| (|+i| (|+i| e156 g_s229_259) g_s230_258) (|*i| g_s221_246 g_s191_211))) (|<=i| e0 (|-i| (|-i| e260 g_s218_243) (|*i| g_s221_246 g_s191_211))) (|<=i| e0 (|-i| (|-i| e260 g_s218_243) (idiv (|*i| (|*i| g_s221_246 g_s191_211) (|-i| e251 g_s223_250)) e251))) (|<=i| (|*i| (|*i| e159 g_s221_246) g_s191_211) e155) (|<=i| (|*i| (|*i| e159 g_s221_246) g_s191_211) e260) (|<=i| e0 (|-i| (|-i| e260 g_s218_243) (|*i| (|*i| e159 g_s221_246) g_s191_211))) (mem g_s231_261 g_s145_145) (|<i| g_s231_261 g_s151_152) (mem g_s232_262 g_s145_145) (|<=i| e263 g_s231_261) (= g_s232_262 (|-i| g_s231_261 e204)) (mem g_s233_264 g_s145_145) (mem g_s234_265 g_s145_145) (= g_s233_264 e159) (= g_s234_265 e204) (mem g_s235_266 g_s146_143) (mem g_s236_267 g_s146_143) (mem g_s237_268 g_s146_143) (mem g_s238_269 g_s145_145) (mem g_s239_270 g_s145_145) (mem g_s240_271 g_s145_145) (mem g_s241_272 g_s145_145) (mem g_s242_273 g_s145_145) (mem g_s243_274 g_s145_145) (not (= g_s242_273 g_s243_274)) (mem g_s244_275 g_s145_145) (mem g_s245_276 g_s145_145) (mem g_s246_277 g_s145_145) (not (= g_s244_275 g_s245_276)) (not (= g_s244_275 g_s246_277)) (not (= g_s245_276 g_s246_277)) (mem g_s247_278 g_s143_144) (mem g_s248_279 g_s145_145) (mem g_s249_280 g_s145_145) (mem g_s250_281 g_s146_143) (|<=i| e282 g_s250_281) (|<=i| g_s250_281 e283) (|<=i| g_s206_227 g_s250_281) (mem g_s251_284 (|-->| (interval e0 e157) g_s146_143)) (mem g_s252_285 g_s143_144) (mem g_s253_286 g_s143_144) (mem g_s254_287 g_s146_143) (mem g_s255_288 g_s146_143) (mem g_s256_289 g_s143_144) (mem g_s257_290 g_s143_144) (mem g_s258_291 g_s143_144) (mem g_s259_292 g_s143_144) (mem g_s260_293 g_s143_144) (mem g_s261_294 g_s143_144) (mem g_s262_295 g_s143_144) (mem g_s263_296 g_s143_144) (mem g_s264_297 g_s143_144) (mem g_s265_298 g_s143_144) (mem g_s266_299 g_s143_144) (mem g_s267_300 g_s143_144) (mem g_s268_301 g_s143_144) (mem g_s269_302 g_s143_144) (mem g_s270_303 g_s143_144) (mem g_s271_304 g_s143_144) (mem g_s272_305 g_s143_144) (mem g_s273_306 g_s143_144) (mem g_s274_307 g_s143_144) (mem g_s275_308 g_s143_144) (mem g_s276_309 g_s143_144) (mem g_s277_310 g_s146_143) (mem g_s278_311 (|-->| (interval e0 e159) g_s145_145)) (mem g_s279_312 g_s145_145) (|<i| g_s279_312 g_s151_152) (mem g_s280_313 g_s145_145) (= g_s280_313 (|-i| g_s279_312 e204)) (mem g_s281_314 g_s145_145) (|<=i| g_s281_314 g_s279_312) (= g_s281_314 e159) (mem g_s282_315 g_s145_145) (mem g_s283_316 g_s145_145) (= g_s283_316 g_s282_315) (= g_s283_316 e159) (mem g_s284_317 (|-->| (interval e0 e203) g_s145_145)) (mem g_s285_318 (|-->| (interval e0 e203) g_s145_145)) (|<=i| (|+i| e319 (|*i| e257 g_s279_312)) g_s250_281) (|<=i| (|+i| e320 (|*i| e203 g_s226_254)) g_s250_281) (|<=i| (|*i| e257 g_s279_312) e321) (|<=i| (|*i| e203 g_s226_254) e322) (mem g_s286_323 (|-->| (interval e0 e159) g_s145_145)) (mem g_s287_324 g_s143_144) (mem g_s288_325 g_s143_144) (not (= g_s287_324 g_s288_325)) (mem g_s289_326 NAT1) (mem g_s290_327 g_s143_144) (|<i| g_s290_327 (|-i| g_s149_150 g_s150_151)) (mem g_s291_328 g_s143_144) (= g_s291_328 (|+i| g_s290_327 g_s289_326)) (mem g_s292_329 g_s143_144) (mem g_s293_330 g_s143_144) (mem g_s294_331 NAT1) (mem g_s295_332 NAT1) (mem g_s289_326 NAT1) (mem g_s296_333 g_s143_144) (mem g_s297_334 g_s143_144) (mem g_s298_335 g_s143_144) (= g_s297_334 (|+i| g_s296_333 g_s294_331)) (= g_s298_335 (|+i| g_s296_333 g_s295_332)) (mem g_s299_336 g_s146_143) (mem g_s300_337 g_s143_144) (|<=i| g_s300_337 e338) (mem g_s301_339 NAT1) (mem g_s302_340 g_s143_144) (|<i| g_s302_340 (|-i| g_s149_150 g_s150_151)) (mem g_s303_341 g_s143_144) (= g_s303_341 (|+i| g_s302_340 g_s301_339)) (mem g_s304_342 g_s143_144) (|<=i| e204 g_s304_342) (mem g_s305_343 g_s143_144) (mem g_s306_344 g_s143_144) (mem g_s307_345 g_s143_144) (|<i| g_s307_345 (|-i| g_s149_150 g_s150_151)) (mem g_s308_346 g_s143_144) (mem g_s309_347 NAT1) (= g_s308_346 (|+i| g_s307_345 g_s309_347)) (mem g_s310_348 NATURAL1) (mem g_s311_349 g_s143_144) (= g_s311_349 (|+i| g_s307_345 g_s310_348)) (mem g_s312_350 g_s143_144) (mem g_s313_351 g_s143_144) (mem g_s314_352 g_s143_144) (mem g_s315_353 g_s143_144) (mem g_s316_354 g_s146_143) (|<i| (|*i| e159 g_s316_354) g_s150_151) (mem g_s317_355 NAT1) (mem g_s318_356 g_s146_143) (mem g_s319_357 g_s146_143) (= g_s319_357 (|+i| g_s318_356 g_s317_355)) (mem g_s320_358 g_s143_144) (mem g_s321_359 g_s143_144) (mem g_s322_360 g_s143_144) (mem g_s323_361 g_s143_144) (mem g_s324_362 g_s143_144) (mem g_s325_363 g_s143_144) (mem g_s326_364 g_s143_144) (mem g_s327_365 g_s143_144) (mem g_s328_366 g_s143_144) (mem g_s329_367 g_s143_144)))
(define-fun |def_seext| () Bool (and (mem g_s330_368 (seq g_s145_145)) (|<=i| (size g_s330_368) g_s232_262) (mem g_s331_369 g_s146_143) (mem g_s155_160 (|+->| BOOL g_s145_145)) (mem g_s155_160 (|+->| BOOL g_s146_143)) (mem g_s155_160 (|+->| BOOL g_s143_144))))
(define-fun |def_mchcst| () Bool true)
(define-fun |def_aprp| () Bool true)
(define-fun |def_abs| () Bool true)
(define-fun |def_inv| () Bool true)
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
(assert |def_abs|)
(assert |def_inv|)
(assert |def_ass|)
(assert (= g_s333$1_371 g_s333_370))
(define-fun lh_1 () Bool (mem g_s333_370 g_s146_143))
(define-fun lh_2 () Bool (|<=i| e159 (size g_s330_368)))
(define-fun lh_3 () Bool (mem g_s334$1_372 g_s146_143))
(define-fun lh_4 () Bool (mem g_s335$1_373 g_s145_145))
(define-fun lh_5 () Bool (mem g_s336$1_374 g_s146_143))
(define-fun lh_6 () Bool (mem g_s337$1_375 g_s146_143))
(define-fun lh_7 () Bool (mem g_s338$1_376 g_s145_145))
(define-fun lh_8 () Bool (mem g_s339$1_377 g_s145_145))
(define-fun lh_9 () Bool (mem (size g_s330_368) g_s145_145))
(define-fun lh_10 () Bool (mem g_s334$2_378 g_s146_143))
(define-fun lh_11 () Bool (and (|>=i| g_s335$2_379 e159) (|<=i| g_s335$2_379 (size g_s330_368))))
(define-fun lh_12 () Bool (mem g_s338$2_380 g_s145_145))
(define-fun lh_13 () Bool (|<i| g_s335$2_379 (size g_s330_368)))
(define-fun lh_14 () Bool (mem g_s335$2_379 g_s145_145))
(define-fun lh_15 () Bool (and (|>=i| g_s335$2_379 e0) (|<=i| g_s335$2_379 (|-i| (size g_s330_368) e204))))
; PO 1 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9) (and (|>=i| e159 e159) (|<=i| e159 (size g_s330_368))))))
(check-sat)
(pop 1)
; PO 2 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9) (mem e156 g_s146_143))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12) (|<=i| e0 (|-i| (|+i| (size g_s330_368) e203) g_s335$2_379)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13) (mem g_s335$2_379 g_s145_145))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 5 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13) (and (|>=i| g_s335$2_379 e0) (|<=i| g_s335$2_379 (|-i| (size g_s330_368) e204))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 6 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15) (and (|>=i| (apply g_s180_185 (mapplet g_s335$2_379 e204)) e159) (|<=i| (apply g_s180_185 (mapplet g_s335$2_379 e204)) (size g_s330_368))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 7 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15) (mem (apply g_s330_368 (|+i| g_s335$2_379 e204)) g_s145_145))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 8 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15) (mem (apply g_s166_171 (mapplet (apply g_s163_168 (mapplet g_s334$2_378 e381)) (apply g_s220_245 (apply g_s165_170 (mapplet (apply g_s166_171 (mapplet g_s334$2_378 (apply g_s165_170 (mapplet e157 (apply g_s330_368 (|+i| g_s335$2_379 e204)))))) e157))))) g_s146_143))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 9 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11 lh_12 lh_13 lh_14 lh_15) (|<i| (|-i| (|+i| (size g_s330_368) e203) (apply g_s180_185 (mapplet g_s335$2_379 e204))) (|-i| (|+i| (size g_s330_368) e203) g_s335$2_379)))))
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
(assert (mem g_s333_370 g_s146_143))
(assert (|<=i| e159 (size g_s330_368)))
(define-fun lh_1 () Bool (mem g_s334$1_372 g_s146_143))
(define-fun lh_2 () Bool (mem g_s335$1_373 g_s145_145))
(define-fun lh_3 () Bool (mem g_s336$1_374 g_s146_143))
(define-fun lh_4 () Bool (mem g_s337$1_375 g_s146_143))
(define-fun lh_5 () Bool (mem g_s338$1_376 g_s145_145))
(define-fun lh_6 () Bool (mem g_s339$1_377 g_s145_145))
(define-fun lh_7 () Bool (mem (size g_s330_368) g_s145_145))
(define-fun lh_8 () Bool (mem g_s334$2_378 g_s146_143))
(define-fun lh_9 () Bool (and (|>=i| g_s335$2_379 e159) (|<=i| g_s335$2_379 (size g_s330_368))))
(define-fun lh_10 () Bool (mem g_s338$2_380 g_s145_145))
(define-fun lh_11 () Bool (|<i| g_s335$2_379 (size g_s330_368)))
; PO 1 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11) (mem g_s180_185 (|+->| (dom g_s180_185) (ran g_s180_185))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11) (mem g_s165_170 (|+->| (dom g_s165_170) (ran g_s165_170))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11) (mem g_s163_168 (|+->| (dom g_s163_168) (ran g_s163_168))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11) (mem g_s166_171 (|+->| (dom g_s166_171) (ran g_s166_171))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 5 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11) (mem g_s220_245 (|+->| (dom g_s220_245) (ran g_s220_245))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 6 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11) (mem (mapplet e157 (apply g_s330_368 (|+i| g_s335$2_379 e204))) (dom g_s165_170)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 7 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11) (mem (mapplet g_s334$2_378 e381) (dom g_s163_168)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 8 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11) (mem (mapplet g_s334$2_378 (apply g_s165_170 (mapplet e157 (apply g_s330_368 (|+i| g_s335$2_379 e204))))) (dom g_s166_171)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 9 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11) (mem (mapplet g_s335$2_379 e204) (dom g_s180_185)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 10 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11) (mem (mapplet (apply g_s163_168 (mapplet g_s334$2_378 e381)) (apply g_s220_245 (apply g_s165_170 (mapplet (apply g_s166_171 (mapplet g_s334$2_378 (apply g_s165_170 (mapplet e157 (apply g_s330_368 (|+i| g_s335$2_379 e204)))))) e157)))) (dom g_s166_171)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 11 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11) (mem (mapplet (apply g_s166_171 (mapplet g_s334$2_378 (apply g_s165_170 (mapplet e157 (apply g_s330_368 (|+i| g_s335$2_379 e204)))))) e157) (dom g_s165_170)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 12 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10 lh_11) (mem (apply g_s165_170 (mapplet (apply g_s166_171 (mapplet g_s334$2_378 (apply g_s165_170 (mapplet e157 (apply g_s330_368 (|+i| g_s335$2_379 e204)))))) e157)) (dom g_s220_245)))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
(exit)