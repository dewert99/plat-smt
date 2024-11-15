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
(declare-fun e49 () U)
(declare-fun e51 () U)
(declare-fun e53 () U)
(declare-fun e55 () U)
(declare-fun e57 () U)
(declare-fun e39 () U)
(declare-fun e60 () U)
(declare-fun e62 () U)
(declare-fun e64 () U)
(declare-fun e66 () U)
(declare-fun e68 () U)
(declare-fun e70 () U)
(declare-fun e72 () U)
(declare-fun e74 () U)
(declare-fun e76 () U)
(declare-fun e78 () U)
(declare-fun e80 () U)
(declare-fun e82 () U)
(declare-fun e84 () U)
(declare-fun e86 () U)
(declare-fun e88 () U)
(declare-fun e90 () U)
(declare-fun e92 () U)
(declare-fun e94 () U)
(declare-fun e96 () U)
(declare-fun e98 () U)
(declare-fun e100 () U)
(declare-fun e102 () U)
(declare-fun e104 () U)
(declare-fun e106 () U)
(declare-fun e44 () U)
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
(declare-fun e145 () U)
(declare-fun e147 () U)
(declare-fun e149 () U)
(declare-fun e151 () U)
(declare-fun e153 () U)
(declare-fun e155 () U)
(declare-fun e157 () U)
(declare-fun e159 () U)
(declare-fun e161 () U)
(declare-fun e43 () U)
(declare-fun g_s0_1 () U)
(declare-fun g_s1_2 () U)
(declare-fun g_s10_11 () U)
(declare-fun g_s100_160 () U)
(declare-fun g_s101_162 () U)
(declare-fun g_s102_163 () U)
(declare-fun g_s103_164 () U)
(declare-fun g_s104_165 () U)
(declare-fun g_s108_166 () U)
(declare-fun g_s108_170 () U)
(declare-fun g_s108$1_167 () U)
(declare-fun g_s108$1_171 () U)
(declare-fun g_s109_172 () U)
(declare-fun g_s109_168 () U)
(declare-fun g_s11_12 () U)
(declare-fun g_s110$1_169 () U)
(declare-fun g_s12_13 () U)
(declare-fun g_s15_16 () U)
(declare-fun g_s16_19 () U)
(declare-fun g_s18_21 () U)
(declare-fun g_s2_3 () U)
(declare-fun g_s20_23 () U)
(declare-fun g_s21_22 () U)
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
(declare-fun g_s32_34 () U)
(declare-fun g_s33_35 () U)
(declare-fun g_s34_36 () U)
(declare-fun g_s35_37 () U)
(declare-fun g_s36_38 () U)
(declare-fun g_s37_40 () U)
(declare-fun g_s38_41 () U)
(declare-fun g_s39_42 () U)
(declare-fun g_s4_5 () U)
(declare-fun g_s40_45 () U)
(declare-fun g_s41_46 () U)
(declare-fun g_s42_47 () U)
(declare-fun g_s43_48 () U)
(declare-fun g_s44_50 () U)
(declare-fun g_s45_52 () U)
(declare-fun g_s46_54 () U)
(declare-fun g_s47_56 () U)
(declare-fun g_s48_58 () U)
(declare-fun g_s49_59 () U)
(declare-fun g_s5_6 () U)
(declare-fun g_s50_61 () U)
(declare-fun g_s51_63 () U)
(declare-fun g_s52_65 () U)
(declare-fun g_s53_67 () U)
(declare-fun g_s54_69 () U)
(declare-fun g_s55_71 () U)
(declare-fun g_s56_73 () U)
(declare-fun g_s57_75 () U)
(declare-fun g_s58_77 () U)
(declare-fun g_s59_79 () U)
(declare-fun g_s6_7 () U)
(declare-fun g_s60_81 () U)
(declare-fun g_s61_83 () U)
(declare-fun g_s62_85 () U)
(declare-fun g_s63_87 () U)
(declare-fun g_s64_89 () U)
(declare-fun g_s65_91 () U)
(declare-fun g_s66_93 () U)
(declare-fun g_s67_95 () U)
(declare-fun g_s68_97 () U)
(declare-fun g_s69_99 () U)
(declare-fun g_s7_8 () U)
(declare-fun g_s70_101 () U)
(declare-fun g_s71_103 () U)
(declare-fun g_s72_105 () U)
(declare-fun g_s73_107 () U)
(declare-fun g_s74_108 () U)
(declare-fun g_s75_110 () U)
(declare-fun g_s76_112 () U)
(declare-fun g_s77_114 () U)
(declare-fun g_s78_116 () U)
(declare-fun g_s79_118 () U)
(declare-fun g_s8_9 () U)
(declare-fun g_s80_120 () U)
(declare-fun g_s81_122 () U)
(declare-fun g_s82_124 () U)
(declare-fun g_s83_126 () U)
(declare-fun g_s84_128 () U)
(declare-fun g_s85_130 () U)
(declare-fun g_s86_132 () U)
(declare-fun g_s87_134 () U)
(declare-fun g_s88_136 () U)
(declare-fun g_s89_138 () U)
(declare-fun g_s9_10 () U)
(declare-fun g_s90_140 () U)
(declare-fun g_s91_142 () U)
(declare-fun g_s92_144 () U)
(declare-fun g_s93_146 () U)
(declare-fun g_s94_148 () U)
(declare-fun g_s95_150 () U)
(declare-fun g_s96_152 () U)
(declare-fun g_s97_154 () U)
(declare-fun g_s98_156 () U)
(declare-fun g_s99_158 () U)
(declare-fun e18 () U)
(declare-fun e20 () U)
(declare-fun e15 () U)
(declare-fun e14 () U)
; Defines
(define-fun |def_B definitions| () Bool (and (= NAT (interval e0 MaxInt)) (= INT (interval MinInt MaxInt))))
(define-fun |def_ctx| () Bool (and (not (= g_s0_1 empty)) (not (= g_s1_2 empty)) (not (= g_s2_3 empty)) (not (= g_s3_4 empty)) (not (= g_s4_5 empty)) (not (= g_s5_6 empty)) (not (= g_s6_7 empty)) (not (= g_s7_8 empty)) (not (= g_s8_9 empty)) (not (= g_s9_10 empty)) (not (= g_s10_11 empty)) (not (= g_s11_12 empty)) (mem g_s12_13 (|-->| (set_prod INTEGER NATURAL) INTEGER)) (= g_s12_13 (binary_union e15 e14)) (mem g_s15_16 (|-->| BOOL NAT)) (= g_s15_16 (SET (mapplet (mapplet FALSE e0) (mapplet TRUE e17)))) (= g_s16_19 e18) (= g_s18_21 e20) (= g_s20_23 (interval (iuminus g_s21_22) g_s21_22)) (= g_s22_24 (interval e0 g_s21_22)) (= g_s23_25 (interval e17 g_s21_22)) (subset g_s23_25 g_s22_24) (subset g_s22_24 g_s20_23) (subset g_s22_24 NAT) (subset g_s23_25 NAT1) (subset g_s20_23 INT) (mem g_s24_26 g_s20_23) (mem g_s24_26 g_s22_24) (not (mem g_s24_26 g_s23_25)) (mem g_s25_27 g_s20_23) (not (mem g_s25_27 g_s22_24)) (= g_s26_28 (interval (iuminus g_s21_22) g_s21_22)) (subset g_s26_28 INT) (subset g_s27_29 g_s10_11) (mem g_s28_30 g_s10_11) (mem g_s28_30 g_s27_29) (mem g_s29_31 g_s10_11) (not (mem g_s29_31 g_s27_29)) (mem g_s30_32 (|+->| NAT g_s10_11)) (mem g_s30_32 (perm g_s27_29)) (= (card g_s27_29) g_s31_33) (subset g_s32_34 g_s11_12) (mem g_s33_35 g_s11_12) (mem g_s33_35 g_s32_34) (mem g_s34_36 g_s11_12) (not (mem g_s34_36 g_s32_34)) (mem g_s35_37 (|+->| NAT g_s11_12)) (mem g_s35_37 (perm g_s32_34)) (= (card g_s32_34) g_s36_38) (mem g_s21_22 NAT1) (= g_s21_22 (|-i| MaxInt e39)) (mem g_s37_40 NAT1) (mem g_s38_41 NAT1) (mem g_s39_42 NAT1) (mem g_s31_33 NAT1) (mem g_s36_38 NAT1) (= g_s31_33 e43) (= g_s36_38 e44)))
(define-fun |def_seext| () Bool (and (= g_s40_45 TRUE) (= g_s41_46 FALSE) (= g_s42_47 e0) (= g_s43_48 e17) (= g_s44_50 e49) (= g_s45_52 e51) (= g_s46_54 e53) (= g_s47_56 e55) (= g_s48_58 e57) (= g_s49_59 e39) (= g_s50_61 e60) (= g_s51_63 e62) (= g_s52_65 e64) (= g_s53_67 e66) (= g_s54_69 e68) (= g_s55_71 e70) (= g_s56_73 e72) (= g_s57_75 e74) (= g_s58_77 e76) (= g_s59_79 e78) (= g_s60_81 e80) (= g_s61_83 e82) (= g_s62_85 e84) (= g_s63_87 e86) (= g_s64_89 e88) (= g_s65_91 e90) (= g_s66_93 e92) (= g_s67_95 e94) (= g_s68_97 e96) (= g_s69_99 e98) (= g_s70_101 e100) (= g_s71_103 e102) (= g_s72_105 e104) (= g_s73_107 e106) (= g_s74_108 e44) (= g_s75_110 e109) (= g_s76_112 e111) (= g_s77_114 e113) (= g_s78_116 e115) (= g_s79_118 e117) (= g_s80_120 e119) (= g_s81_122 e121) (= g_s82_124 e123) (= g_s83_126 e125) (= g_s84_128 e127) (= g_s85_130 e129) (= g_s86_132 e131) (= g_s87_134 e133) (= g_s88_136 e135) (= g_s89_138 e137) (= g_s90_140 e139) (= g_s91_142 e141) (= g_s92_144 e143) (= g_s93_146 e145) (= g_s94_148 e147) (= g_s95_150 e149) (= g_s96_152 e151) (= g_s97_154 e153) (= g_s98_156 e155) (= g_s99_158 e157) (= g_s100_160 e159) (= g_s101_162 e161) (mem g_s102_163 g_s8_9)))
(define-fun |def_mchcst| () Bool true)
(define-fun |def_aprp| () Bool (and (= g_s103_164 NATURAL) (mem g_s104_165 g_s26_28) (= g_s104_165 e0)))
(define-fun |def_abs| () Bool true)
(define-fun |def_inv| () Bool true)
(define-fun |def_ass| () Bool true)
(define-fun |def_sets| () Bool true)
(define-fun |def_imlprp| () Bool (and (= g_s103_164 NATURAL) (= g_s104_165 e0)))
(define-fun |def_imprp| () Bool true)
(define-fun |def_imext| () Bool true)
; PO group 0 
(push 1)
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_imprp|)
; PO 1 in group 0
(assert (not (mem e0 g_s26_28)))
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
(assert (= g_s108$1_167 g_s108_166))
(define-fun lh_1 () Bool (mem g_s109_168 g_s0_1))
(define-fun lh_2 () Bool (mem g_s110$1_169 INTEGER))
(define-fun lh_3 () Bool (not (= (bool (|>=i| g_s110$1_169 e0)) FALSE)))
; PO 1 in group 1
(assert (not (=> (and lh_1 lh_2 lh_3) (mem g_s110$1_169 g_s103_164))))
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
(assert (= g_s108$1_171 g_s108_170))
(define-fun lh_1 () Bool (mem g_s109_172 INTEGER))
; PO 1 in group 2
(assert (not (=> lh_1 (= (bool (|>=i| g_s109_172 e0)) (bool (mem g_s109_172 g_s103_164))))))
(set-info :status unknown)
(check-sat)
(pop 1)
(exit)