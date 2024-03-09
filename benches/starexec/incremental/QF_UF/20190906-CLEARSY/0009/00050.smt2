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
(declare-fun e0 () U)
(declare-fun e34 () U)
(declare-fun e36 () U)
(declare-fun e38 () U)
(declare-fun e40 () U)
(declare-fun e42 () U)
(declare-fun e44 () U)
(declare-fun e46 () U)
(declare-fun e48 () U)
(declare-fun e50 () U)
(declare-fun e52 () U)
(declare-fun e54 () U)
(declare-fun e56 () U)
(declare-fun e58 () U)
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
(declare-fun e108 () U)
(declare-fun e110 () U)
(declare-fun e112 () U)
(declare-fun e114 () U)
(declare-fun e116 () U)
(declare-fun e118 () U)
(declare-fun e120 () U)
(declare-fun e122 () U)
(declare-fun e124 () U)
(declare-fun e126 () U)
(declare-fun e128 () U)
(declare-fun e130 () U)
(declare-fun e132 () U)
(declare-fun e134 () U)
(declare-fun e136 () U)
(declare-fun e138 () U)
(declare-fun e140 () U)
(declare-fun e142 () U)
(declare-fun e144 () U)
(declare-fun e146 () U)
(declare-fun e148 () U)
(declare-fun e150 () U)
(declare-fun g_s0_1 () U)
(declare-fun g_s1_2 () U)
(declare-fun g_s10_10 () U)
(declare-fun g_s100_161 () U)
(declare-fun g_s101_160 () U)
(declare-fun g_s102_163 () U)
(declare-fun g_s103_162 () U)
(declare-fun g_s104_164 () U)
(declare-fun g_s105_165 () U)
(declare-fun g_s106_166 () U)
(declare-fun g_s107_167 () U)
(declare-fun g_s108$1_168 () U)
(declare-fun g_s11_12 () U)
(declare-fun g_s112_169 () U)
(declare-fun g_s112$1_170 () U)
(declare-fun g_s113_171 () U)
(declare-fun g_s113$1_172 () U)
(declare-fun g_s114_173 () U)
(declare-fun g_s117_174 () U)
(declare-fun g_s118_175 () U)
(declare-fun g_s12_13 () U)
(declare-fun g_s120$1_176 () U)
(declare-fun g_s13_14 () U)
(declare-fun g_s14_15 () U)
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
(declare-fun g_s33_35 () U)
(declare-fun g_s34_37 () U)
(declare-fun g_s35_39 () U)
(declare-fun g_s36_41 () U)
(declare-fun g_s37_43 () U)
(declare-fun g_s38_45 () U)
(declare-fun g_s39_47 () U)
(declare-fun g_s4_5 () U)
(declare-fun g_s40_49 () U)
(declare-fun g_s41_51 () U)
(declare-fun g_s42_53 () U)
(declare-fun g_s43_55 () U)
(declare-fun g_s44_57 () U)
(declare-fun g_s45_59 () U)
(declare-fun g_s46_61 () U)
(declare-fun g_s47_63 () U)
(declare-fun g_s48_65 () U)
(declare-fun g_s49_67 () U)
(declare-fun g_s5_6 () U)
(declare-fun g_s50_69 () U)
(declare-fun g_s51_71 () U)
(declare-fun g_s52_73 () U)
(declare-fun g_s53_75 () U)
(declare-fun g_s54_77 () U)
(declare-fun g_s55_79 () U)
(declare-fun g_s56_81 () U)
(declare-fun g_s57_83 () U)
(declare-fun g_s58_85 () U)
(declare-fun g_s59_87 () U)
(declare-fun g_s6_8 () U)
(declare-fun g_s60_89 () U)
(declare-fun g_s61_91 () U)
(declare-fun g_s62_93 () U)
(declare-fun g_s63_95 () U)
(declare-fun g_s64_97 () U)
(declare-fun g_s65_99 () U)
(declare-fun g_s66_101 () U)
(declare-fun g_s67_103 () U)
(declare-fun g_s68_105 () U)
(declare-fun g_s69_107 () U)
(declare-fun g_s7_7 () U)
(declare-fun g_s70_109 () U)
(declare-fun g_s71_111 () U)
(declare-fun g_s72_113 () U)
(declare-fun g_s73_115 () U)
(declare-fun g_s74_117 () U)
(declare-fun g_s75_119 () U)
(declare-fun g_s76_121 () U)
(declare-fun g_s77_123 () U)
(declare-fun g_s78_125 () U)
(declare-fun g_s79_127 () U)
(declare-fun g_s8_9 () U)
(declare-fun g_s80_129 () U)
(declare-fun g_s81_131 () U)
(declare-fun g_s82_133 () U)
(declare-fun g_s83_135 () U)
(declare-fun g_s84_137 () U)
(declare-fun g_s85_139 () U)
(declare-fun g_s86_141 () U)
(declare-fun g_s87_143 () U)
(declare-fun g_s88_145 () U)
(declare-fun g_s89_147 () U)
(declare-fun g_s9_11 () U)
(declare-fun g_s90_149 () U)
(declare-fun g_s91_151 () U)
(declare-fun g_s92_152 () U)
(declare-fun g_s93_153 () U)
(declare-fun g_s94_154 () U)
(declare-fun g_s95_155 () U)
(declare-fun g_s96_156 () U)
(declare-fun g_s97_158 () U)
(declare-fun g_s98_157 () U)
(declare-fun g_s99_159 () U)
; Defines
(define-fun |def_B definitions| () Bool (and (= NAT (interval e0 MaxInt)) (= INT (interval MinInt MaxInt))))
(define-fun |def_ctx| () Bool (and (not (= g_s0_1 empty)) (not (= g_s1_2 empty)) (not (= g_s2_3 empty)) (subset g_s3_4 g_s0_1) (mem g_s4_5 g_s0_1) (not (mem g_s4_5 g_s3_4)) (mem g_s5_6 (|+->| NAT g_s0_1)) (mem g_s5_6 (perm g_s3_4)) (mem g_s6_8 (|>->>| g_s3_4 g_s7_7)) (mem g_s8_9 (|>+>| g_s7_7 g_s3_4)) (mem g_s9_11 (|>->>| g_s3_4 g_s10_10)) (mem g_s11_12 (|>+>| g_s10_10 g_s3_4)) (= g_s8_9 (inverse g_s6_8)) (= g_s11_12 (inverse g_s9_11)) (subset g_s12_13 g_s1_2) (mem g_s13_14 g_s1_2) (not (mem g_s13_14 g_s12_13)) (mem g_s14_15 (|+->| NAT g_s1_2)) (mem g_s14_15 (perm g_s12_13)) (subset g_s15_16 g_s2_3) (mem g_s16_17 g_s2_3) (not (mem g_s16_17 g_s15_16)) (mem g_s17_18 (|+->| NAT g_s2_3)) (mem g_s17_18 (perm g_s15_16)) (subset g_s18_19 g_s2_3) (mem g_s19_20 g_s2_3) (not (mem g_s19_20 g_s18_19)) (mem g_s20_21 (|+->| NAT g_s2_3)) (mem g_s20_21 (perm g_s18_19)) (= g_s21_22 NAT) (= g_s22_23 NAT1) (subset g_s22_23 g_s21_22) (mem g_s23_24 g_s21_22) (not (mem g_s23_24 g_s22_23)) (= g_s24_25 NAT) (= g_s25_26 NAT1) (subset g_s25_26 g_s24_25) (mem g_s26_27 g_s24_25) (not (mem g_s26_27 g_s25_26)) (mem g_s27_28 g_s0_1) (mem g_s28_29 g_s0_1) (mem g_s29_30 g_s0_1)))
(define-fun |def_seext| () Bool (and (= g_s30_31 TRUE) (= g_s31_32 FALSE) (= g_s32_33 e0) (= g_s33_35 e34) (= g_s34_37 e36) (= g_s35_39 e38) (= g_s36_41 e40) (= g_s37_43 e42) (= g_s38_45 e44) (= g_s39_47 e46) (= g_s40_49 e48) (= g_s41_51 e50) (= g_s42_53 e52) (= g_s43_55 e54) (= g_s44_57 e56) (= g_s45_59 e58) (= g_s46_61 e60) (= g_s47_63 e62) (= g_s48_65 e64) (= g_s49_67 e66) (= g_s50_69 e68) (= g_s51_71 e70) (= g_s52_73 e72) (= g_s53_75 e74) (= g_s54_77 e76) (= g_s55_79 e78) (= g_s56_81 e80) (= g_s57_83 e82) (= g_s58_85 e84) (= g_s59_87 e86) (= g_s60_89 e88) (= g_s61_91 e90) (= g_s62_93 e92) (= g_s63_95 e94) (= g_s64_97 e96) (= g_s65_99 e98) (= g_s66_101 e100) (= g_s67_103 e102) (= g_s68_105 e104) (= g_s69_107 e106) (= g_s70_109 e108) (= g_s71_111 e110) (= g_s72_113 e112) (= g_s73_115 e114) (= g_s74_117 e116) (= g_s75_119 e118) (= g_s76_121 e120) (= g_s77_123 e122) (= g_s78_125 e124) (= g_s79_127 e126) (= g_s80_129 e128) (= g_s81_131 e130) (= g_s82_133 e132) (= g_s83_135 e134) (= g_s84_137 e136) (= g_s85_139 e138) (= g_s86_141 e140) (= g_s87_143 e142) (= g_s88_145 e144) (= g_s89_147 e146) (= g_s90_149 e148) (= g_s91_151 e150) (mem g_s92_152 g_s21_22) (mem g_s93_153 g_s24_25) (mem g_s94_154 g_s21_22) (mem g_s95_155 g_s21_22) (mem g_s96_156 (|+->| g_s15_16 g_s25_26)) (mem g_s97_158 g_s98_157) (mem g_s99_159 g_s98_157) (mem g_s100_161 g_s101_160) (mem g_s102_163 g_s103_162) (mem g_s104_164 g_s101_160) (mem g_s105_165 g_s103_162) (mem g_s106_166 BOOL)))
(define-fun |def_mchcst| () Bool true)
(define-fun |def_aprp| () Bool true)
(define-fun |def_abs| () Bool  (mem g_s107_167 (|+->| g_s2_3 g_s24_25)))
(define-fun |def_inv| () Bool (and (mem g_s108$1_168 (|-->| g_s2_3 g_s24_25)) (= g_s107_167 (range_restriction (domain_restriction g_s15_16 g_s108$1_168) g_s25_26))))
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
(assert (not (mem (set_prod g_s2_3 (SET g_s26_27)) (|-->| g_s2_3 g_s24_25))))
(check-sat)
(pop 1)
; PO 2 in group 0
(push 1)
(assert (not (= empty (range_restriction (domain_restriction g_s15_16 (set_prod g_s2_3 (SET g_s26_27))) g_s25_26))))
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
(assert (= g_s112$1_170 g_s112_169))
(assert (= g_s113$1_172 g_s113_171))
(define-fun lh_1 () Bool (mem g_s114_173 g_s2_3))
(define-fun lh_2 () Bool (mem g_s114_173 g_s15_16))
(define-fun lh_3 () Bool (mem (apply g_s108$1_168 g_s114_173) g_s24_25))
(define-fun lh_4 () Bool (mem g_s114_173 (dom g_s107_167)))
; PO 1 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem (apply g_s108$1_168 g_s114_173) g_s24_25))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem (apply g_s107_167 g_s114_173) g_s24_25))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (= (bool (mem (apply g_s108$1_168 g_s114_173) g_s25_26)) (bool (mem g_s114_173 (dom g_s107_167)))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (= (apply g_s108$1_168 g_s114_173) (apply g_s107_167 g_s114_173)))))
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
(define-fun lh_1 () Bool (= g_s117_174 g_s29_30))
(define-fun lh_2 () Bool (mem g_s117_174 g_s0_1))
(define-fun lh_3 () Bool (mem g_s117_174 g_s3_4))
(define-fun lh_4 () Bool (mem g_s118_175 g_s2_3))
(define-fun lh_5 () Bool (mem g_s118_175 g_s15_16))
; PO 1 in group 2
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5) (mem (|<+| g_s108$1_168 (SET (mapplet g_s118_175 g_s26_27))) (|-->| g_s2_3 g_s24_25)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 2
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5) (= (domain_subtraction (SET g_s118_175) g_s107_167) (range_restriction (domain_restriction g_s15_16 (|<+| g_s108$1_168 (SET (mapplet g_s118_175 g_s26_27)))) g_s25_26)))))
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
(define-fun lh_1 () Bool (= g_s117_174 g_s29_30))
(define-fun lh_2 () Bool (mem g_s117_174 g_s0_1))
(define-fun lh_3 () Bool (mem g_s117_174 g_s3_4))
(define-fun lh_4 () Bool (mem g_s118_175 g_s2_3))
(define-fun lh_5 () Bool (mem g_s118_175 g_s15_16))
(define-fun lh_6 () Bool (mem g_s118_175 (dom g_s96_156)))
(define-fun lh_7 () Bool (mem g_s120$1_176 g_s24_25))
(define-fun lh_8 () Bool (= g_s120$1_176 (apply g_s96_156 g_s118_175)))
(define-fun lh_9 () Bool (= (bool (mem g_s118_175 (dom g_s96_156))) TRUE))
; PO 1 in group 3
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9) (mem (|<+| g_s108$1_168 (SET (mapplet g_s118_175 g_s120$1_176))) (|-->| g_s2_3 g_s24_25)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 3
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9) (= (|<+| (domain_subtraction (SET g_s118_175) g_s107_167) (domain_restriction (SET g_s118_175) g_s96_156)) (range_restriction (domain_restriction g_s15_16 (|<+| g_s108$1_168 (SET (mapplet g_s118_175 g_s120$1_176)))) g_s25_26)))))
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
(assert (mem g_s114_173 g_s2_3))
(assert (mem g_s114_173 g_s15_16))
; PO 1 in group 4
(push 1)
(assert (not (mem g_s114_173 (dom g_s108$1_168))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 4
(push 1)
(assert (not (mem g_s108$1_168 (|+->| (dom g_s108$1_168) (ran g_s108$1_168)))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
(exit)