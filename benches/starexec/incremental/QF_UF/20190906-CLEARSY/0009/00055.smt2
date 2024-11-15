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
(declare-fun e0 () U)
(declare-fun e27 () U)
(declare-fun e29 () U)
(declare-fun e31 () U)
(declare-fun e33 () U)
(declare-fun e35 () U)
(declare-fun e37 () U)
(declare-fun e39 () U)
(declare-fun e41 () U)
(declare-fun e43 () U)
(declare-fun e45 () U)
(declare-fun e47 () U)
(declare-fun e49 () U)
(declare-fun e51 () U)
(declare-fun e53 () U)
(declare-fun e55 () U)
(declare-fun e57 () U)
(declare-fun e59 () U)
(declare-fun e61 () U)
(declare-fun e63 () U)
(declare-fun e65 () U)
(declare-fun e67 () U)
(declare-fun e69 () U)
(declare-fun e71 () U)
(declare-fun e73 () U)
(declare-fun e75 () U)
(declare-fun e77 () U)
(declare-fun e79 () U)
(declare-fun e81 () U)
(declare-fun e83 () U)
(declare-fun e85 () U)
(declare-fun e87 () U)
(declare-fun e89 () U)
(declare-fun e91 () U)
(declare-fun e93 () U)
(declare-fun e95 () U)
(declare-fun e97 () U)
(declare-fun e99 () U)
(declare-fun e101 () U)
(declare-fun e103 () U)
(declare-fun e105 () U)
(declare-fun e107 () U)
(declare-fun e109 () U)
(declare-fun e111 () U)
(declare-fun e113 () U)
(declare-fun e115 () U)
(declare-fun e117 () U)
(declare-fun e119 () U)
(declare-fun e121 () U)
(declare-fun e123 () U)
(declare-fun e125 () U)
(declare-fun e127 () U)
(declare-fun e129 () U)
(declare-fun e131 () U)
(declare-fun e133 () U)
(declare-fun e135 () U)
(declare-fun e137 () U)
(declare-fun e139 () U)
(declare-fun e141 () U)
(declare-fun e143 () U)
(declare-fun g_s0_1 () U)
(declare-fun g_s1_2 () U)
(declare-fun g_s10_11 () U)
(declare-fun g_s100_160 () U)
(declare-fun g_s101_161 () U)
(declare-fun g_s101$1_164 () U)
(declare-fun g_s102_162 () U)
(declare-fun g_s102$1_165 () U)
(declare-fun g_s103_163 () U)
(declare-fun g_s103$1_166 () U)
(declare-fun g_s108_167 () U)
(declare-fun g_s108$1_168 () U)
(declare-fun g_s109$1_169 () U)
(declare-fun g_s11_12 () U)
(declare-fun g_s110$1_170 () U)
(declare-fun g_s12_13 () U)
(declare-fun g_s13_15 () U)
(declare-fun g_s14_14 () U)
(declare-fun g_s15_17 () U)
(declare-fun g_s16_16 () U)
(declare-fun g_s17_19 () U)
(declare-fun g_s18_18 () U)
(declare-fun g_s19_21 () U)
(declare-fun g_s2_3 () U)
(declare-fun g_s20_20 () U)
(declare-fun g_s21_22 () U)
(declare-fun g_s22_23 () U)
(declare-fun g_s23_24 () U)
(declare-fun g_s24_25 () U)
(declare-fun g_s25_26 () U)
(declare-fun g_s26_28 () U)
(declare-fun g_s27_30 () U)
(declare-fun g_s28_32 () U)
(declare-fun g_s29_34 () U)
(declare-fun g_s3_4 () U)
(declare-fun g_s30_36 () U)
(declare-fun g_s31_38 () U)
(declare-fun g_s32_40 () U)
(declare-fun g_s33_42 () U)
(declare-fun g_s34_44 () U)
(declare-fun g_s35_46 () U)
(declare-fun g_s36_48 () U)
(declare-fun g_s37_50 () U)
(declare-fun g_s38_52 () U)
(declare-fun g_s39_54 () U)
(declare-fun g_s4_5 () U)
(declare-fun g_s40_56 () U)
(declare-fun g_s41_58 () U)
(declare-fun g_s42_60 () U)
(declare-fun g_s43_62 () U)
(declare-fun g_s44_64 () U)
(declare-fun g_s45_66 () U)
(declare-fun g_s46_68 () U)
(declare-fun g_s47_70 () U)
(declare-fun g_s48_72 () U)
(declare-fun g_s49_74 () U)
(declare-fun g_s5_6 () U)
(declare-fun g_s50_76 () U)
(declare-fun g_s51_78 () U)
(declare-fun g_s52_80 () U)
(declare-fun g_s53_82 () U)
(declare-fun g_s54_84 () U)
(declare-fun g_s55_86 () U)
(declare-fun g_s56_88 () U)
(declare-fun g_s57_90 () U)
(declare-fun g_s58_92 () U)
(declare-fun g_s59_94 () U)
(declare-fun g_s6_7 () U)
(declare-fun g_s60_96 () U)
(declare-fun g_s61_98 () U)
(declare-fun g_s62_100 () U)
(declare-fun g_s63_102 () U)
(declare-fun g_s64_104 () U)
(declare-fun g_s65_106 () U)
(declare-fun g_s66_108 () U)
(declare-fun g_s67_110 () U)
(declare-fun g_s68_112 () U)
(declare-fun g_s69_114 () U)
(declare-fun g_s7_8 () U)
(declare-fun g_s70_116 () U)
(declare-fun g_s71_118 () U)
(declare-fun g_s72_120 () U)
(declare-fun g_s73_122 () U)
(declare-fun g_s74_124 () U)
(declare-fun g_s75_126 () U)
(declare-fun g_s76_128 () U)
(declare-fun g_s77_130 () U)
(declare-fun g_s78_132 () U)
(declare-fun g_s79_134 () U)
(declare-fun g_s8_9 () U)
(declare-fun g_s80_136 () U)
(declare-fun g_s81_138 () U)
(declare-fun g_s82_140 () U)
(declare-fun g_s83_142 () U)
(declare-fun g_s84_144 () U)
(declare-fun g_s85_146 () U)
(declare-fun g_s86_145 () U)
(declare-fun g_s87_148 () U)
(declare-fun g_s88_147 () U)
(declare-fun g_s89_149 () U)
(declare-fun g_s9_10 () U)
(declare-fun g_s90_150 () U)
(declare-fun g_s91_152 () U)
(declare-fun g_s92_151 () U)
(declare-fun g_s93_154 () U)
(declare-fun g_s94_153 () U)
(declare-fun g_s95_155 () U)
(declare-fun g_s96_156 () U)
(declare-fun g_s97_157 () U)
(declare-fun g_s98_158 () U)
(declare-fun g_s99_159 () U)
; Defines
(define-fun |def_B definitions| () Bool (and (= NAT (interval e0 MaxInt)) (= INT (interval MinInt MaxInt))))
(define-fun |def_ctx| () Bool (and (= g_s0_1 INT) (= g_s1_2 NAT) (= g_s2_3 NAT1) (subset g_s2_3 g_s1_2) (subset g_s1_2 g_s0_1) (= g_s3_4 INT) (= g_s4_5 NAT) (subset g_s4_5 g_s3_4) (mem g_s5_6 g_s0_1) (mem g_s5_6 g_s1_2) (not (mem g_s5_6 g_s2_3)) (mem g_s6_7 g_s0_1) (not (mem g_s6_7 g_s1_2)) (mem g_s7_8 g_s3_4) (mem g_s7_8 g_s4_5) (mem g_s8_9 g_s3_4) (not (mem g_s8_9 g_s4_5)) (= g_s9_10 INT) (= g_s10_11 INT) (= g_s11_12 NATURAL) (= g_s12_13 NATURAL) (mem g_s13_15 g_s14_14) (mem g_s15_17 g_s16_16) (mem g_s17_19 g_s18_18) (mem g_s19_21 g_s20_20) (mem g_s21_22 g_s18_18) (mem g_s22_23 g_s18_18)))
(define-fun |def_seext| () Bool (and (= g_s23_24 TRUE) (= g_s24_25 FALSE) (= g_s25_26 e0) (= g_s26_28 e27) (= g_s27_30 e29) (= g_s28_32 e31) (= g_s29_34 e33) (= g_s30_36 e35) (= g_s31_38 e37) (= g_s32_40 e39) (= g_s33_42 e41) (= g_s34_44 e43) (= g_s35_46 e45) (= g_s36_48 e47) (= g_s37_50 e49) (= g_s38_52 e51) (= g_s39_54 e53) (= g_s40_56 e55) (= g_s41_58 e57) (= g_s42_60 e59) (= g_s43_62 e61) (= g_s44_64 e63) (= g_s45_66 e65) (= g_s46_68 e67) (= g_s47_70 e69) (= g_s48_72 e71) (= g_s49_74 e73) (= g_s50_76 e75) (= g_s51_78 e77) (= g_s52_80 e79) (= g_s53_82 e81) (= g_s54_84 e83) (= g_s55_86 e85) (= g_s56_88 e87) (= g_s57_90 e89) (= g_s58_92 e91) (= g_s59_94 e93) (= g_s60_96 e95) (= g_s61_98 e97) (= g_s62_100 e99) (= g_s63_102 e101) (= g_s64_104 e103) (= g_s65_106 e105) (= g_s66_108 e107) (= g_s67_110 e109) (= g_s68_112 e111) (= g_s69_114 e113) (= g_s70_116 e115) (= g_s71_118 e117) (= g_s72_120 e119) (= g_s73_122 e121) (= g_s74_124 e123) (= g_s75_126 e125) (= g_s76_128 e127) (= g_s77_130 e129) (= g_s78_132 e131) (= g_s79_134 e133) (= g_s80_136 e135) (= g_s81_138 e137) (= g_s82_140 e139) (= g_s83_142 e141) (= g_s84_144 e143) (mem g_s85_146 g_s86_145) (mem g_s87_148 g_s88_147) (mem g_s89_149 g_s86_145) (mem g_s90_150 g_s86_145) (mem g_s91_152 (|+->| g_s92_151 g_s16_16)) (mem g_s93_154 g_s94_153) (mem g_s95_155 g_s94_153) (mem g_s96_156 g_s0_1) (mem g_s97_157 g_s3_4) (mem g_s98_158 g_s0_1) (mem g_s99_159 g_s3_4) (mem g_s100_160 BOOL)))
(define-fun |def_mchcst| () Bool true)
(define-fun |def_aprp| () Bool true)
(define-fun |def_abs| () Bool (and (mem g_s101_161 BOOL) (mem g_s102_162 g_s0_1) (mem g_s103_163 g_s3_4)))
(define-fun |def_inv| () Bool (and (= g_s101_161 g_s101$1_164) (= g_s102_162 g_s102$1_165) (= g_s103_163 g_s103$1_166) (mem g_s101$1_164 BOOL) (mem g_s102$1_165 g_s0_1) (mem g_s103$1_166 g_s3_4)))
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
(define-fun lh_1 () Bool (= g_s100_160 TRUE))
(define-fun lh_2 () Bool (= g_s93_154 g_s22_23))
(define-fun lh_3 () Bool (= g_s95_155 g_s17_19))
; PO 1 in group 0
(assert (not (=> (and lh_1 lh_2 lh_3) (= TRUE g_s23_24))))
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
(define-fun lh_1 () Bool (= g_s100_160 TRUE))
(define-fun lh_2 () Bool (not (and (= g_s93_154 g_s22_23) (= g_s95_155 g_s17_19))))
; PO 1 in group 1
(assert (not (=> (and lh_1 lh_2) (= FALSE g_s24_25))))
(set-info :status unknown)
(check-sat)
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
(assert (= g_s108$1_168 g_s108_167))
(define-fun lh_1 () Bool (= g_s100_160 TRUE))
(define-fun lh_2 () Bool (mem g_s109$1_169 g_s94_153))
(define-fun lh_3 () Bool (= g_s109$1_169 g_s22_23))
(define-fun lh_4 () Bool (mem g_s110$1_170 g_s94_153))
(define-fun lh_5 () Bool (= g_s110$1_170 g_s17_19))
; PO 1 in group 2
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5) (= (bool (and (= (bool (= g_s93_154 g_s109$1_169)) TRUE) (= (bool (= g_s95_155 g_s110$1_170)) TRUE))) (bool (and (= g_s93_154 g_s22_23) (= g_s95_155 g_s17_19)))))))
(set-info :status unknown)
(check-sat)
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
(define-fun lh_1 () Bool (not (= g_s100_160 TRUE)))
; PO 1 in group 3
(assert (not (=> lh_1 (= FALSE g_s24_25))))
(set-info :status unknown)
(check-sat)
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
(assert (= g_s108$1_168 g_s108_167))
; PO 1 in group 4
(assert (not (= g_s100_160 (bool (= g_s100_160 TRUE)))))
(set-info :status unknown)
(check-sat)
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
(assert (= g_s108$1_168 g_s108_167))
(define-fun lh_1 () Bool (= g_s101$1_164 TRUE))
(define-fun lh_2 () Bool (mem g_s96_156 g_s0_1))
(define-fun lh_3 () Bool (mem g_s97_157 g_s3_4))
; PO 1 in group 5
(assert (not (=> (and lh_1 lh_2 lh_3) (= (bool (and (= (bool (mem g_s96_156 g_s1_2)) TRUE) (= (bool (mem g_s97_157 g_s4_5)) TRUE))) (bool (and (mem g_s96_156 g_s1_2) (mem g_s97_157 g_s4_5)))))))
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
(assert (= g_s108$1_168 g_s108_167))
; PO 1 in group 6
(assert (not (= g_s101$1_164 (bool (= g_s101$1_164 TRUE)))))
(set-info :status unknown)
(check-sat)
(pop 1)
(exit)