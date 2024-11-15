(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(set-info :source |
Generated by: David Deharbe, CLEARSY
Generated on: 2019-09-09
Generator: bxml;pog;pog2smt (Atelier B)
Application: Event-B
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
(declare-fun e145 () U)
(declare-fun g_s0_1 () U)
(declare-fun g_s1_2 () U)
(declare-fun g_s10_11 () U)
(declare-fun g_s100_157 () U)
(declare-fun g_s100$1_166 () U)
(declare-fun g_s102_158 () U)
(declare-fun g_s102$1_159 () U)
(declare-fun g_s105_160 () U)
(declare-fun g_s105$1_161 () U)
(declare-fun g_s107_162 () U)
(declare-fun g_s107$1_163 () U)
(declare-fun g_s11_12 () U)
(declare-fun g_s12_13 () U)
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
(declare-fun g_s28_30 () U)
(declare-fun g_s29_32 () U)
(declare-fun g_s3_4 () U)
(declare-fun g_s30_34 () U)
(declare-fun g_s31_36 () U)
(declare-fun g_s32_38 () U)
(declare-fun g_s33_40 () U)
(declare-fun g_s34_42 () U)
(declare-fun g_s35_44 () U)
(declare-fun g_s36_46 () U)
(declare-fun g_s37_48 () U)
(declare-fun g_s38_50 () U)
(declare-fun g_s39_52 () U)
(declare-fun g_s4_5 () U)
(declare-fun g_s40_54 () U)
(declare-fun g_s41_56 () U)
(declare-fun g_s42_58 () U)
(declare-fun g_s43_60 () U)
(declare-fun g_s44_62 () U)
(declare-fun g_s45_64 () U)
(declare-fun g_s46_66 () U)
(declare-fun g_s47_68 () U)
(declare-fun g_s48_70 () U)
(declare-fun g_s49_72 () U)
(declare-fun g_s5_6 () U)
(declare-fun g_s50_74 () U)
(declare-fun g_s51_76 () U)
(declare-fun g_s52_78 () U)
(declare-fun g_s53_80 () U)
(declare-fun g_s54_82 () U)
(declare-fun g_s55_84 () U)
(declare-fun g_s56_86 () U)
(declare-fun g_s57_88 () U)
(declare-fun g_s58_90 () U)
(declare-fun g_s59_92 () U)
(declare-fun g_s6_7 () U)
(declare-fun g_s60_94 () U)
(declare-fun g_s61_96 () U)
(declare-fun g_s62_98 () U)
(declare-fun g_s63_100 () U)
(declare-fun g_s64_102 () U)
(declare-fun g_s65_104 () U)
(declare-fun g_s66_106 () U)
(declare-fun g_s67_108 () U)
(declare-fun g_s68_110 () U)
(declare-fun g_s69_112 () U)
(declare-fun g_s7_8 () U)
(declare-fun g_s70_114 () U)
(declare-fun g_s71_116 () U)
(declare-fun g_s72_118 () U)
(declare-fun g_s73_120 () U)
(declare-fun g_s74_122 () U)
(declare-fun g_s75_124 () U)
(declare-fun g_s76_126 () U)
(declare-fun g_s77_128 () U)
(declare-fun g_s78_130 () U)
(declare-fun g_s79_132 () U)
(declare-fun g_s8_9 () U)
(declare-fun g_s80_134 () U)
(declare-fun g_s81_136 () U)
(declare-fun g_s82_138 () U)
(declare-fun g_s83_140 () U)
(declare-fun g_s84_142 () U)
(declare-fun g_s85_144 () U)
(declare-fun g_s86_146 () U)
(declare-fun g_s87_147 () U)
(declare-fun g_s88_148 () U)
(declare-fun g_s89_149 () U)
(declare-fun g_s9_10 () U)
(declare-fun g_s90_150 () U)
(declare-fun g_s91$1_151 () U)
(declare-fun g_s92$1_152 () U)
(declare-fun g_s93$1_153 () U)
(declare-fun g_s97_154 () U)
(declare-fun g_s98_155 () U)
(declare-fun g_s98$1_165 () U)
(declare-fun g_s99_156 () U)
(declare-fun g_s99$1_164 () U)
; Defines
(define-fun |def_B definitions| () Bool (and (= NAT (interval e0 MaxInt)) (= INT (interval MinInt MaxInt))))
(define-fun |def_ctx| () Bool (and (not (= g_s0_1 empty)) (not (= g_s1_2 empty)) (subset g_s2_3 g_s0_1) (mem g_s3_4 g_s0_1) (not (mem g_s3_4 g_s2_3)) (mem g_s4_5 (|+->| NAT g_s0_1)) (mem g_s4_5 (perm g_s2_3)) (mem g_s5_6 (|>->| g_s2_3 NAT)) (= g_s5_6 (inverse g_s4_5)) (= (card g_s2_3) g_s6_7) (subset g_s7_8 g_s1_2) (mem g_s8_9 g_s1_2) (not (mem g_s8_9 g_s7_8)) (mem g_s9_10 (|+->| NAT g_s1_2)) (mem g_s9_10 (perm g_s7_8)) (mem g_s10_11 (|>->| g_s7_8 NAT)) (= g_s10_11 (inverse g_s9_10)) (= (card g_s7_8) g_s11_12) (= g_s12_13 INT) (= g_s13_14 NAT) (= g_s14_15 NAT1) (subset g_s14_15 g_s13_14) (subset g_s13_14 g_s12_13) (= g_s15_16 INT) (= g_s16_17 NAT) (subset g_s16_17 g_s15_16) (mem g_s17_18 g_s12_13) (mem g_s17_18 g_s13_14) (not (mem g_s17_18 g_s14_15)) (mem g_s18_19 g_s12_13) (not (mem g_s18_19 g_s13_14)) (mem g_s19_20 g_s15_16) (mem g_s19_20 g_s16_17) (mem g_s20_21 g_s15_16) (not (mem g_s20_21 g_s16_17)) (= g_s21_22 INT) (= g_s22_23 INT) (= g_s23_24 NATURAL) (= g_s24_25 NATURAL)))
(define-fun |def_seext| () Bool (and (= g_s25_26 TRUE) (= g_s26_27 FALSE) (= g_s27_28 e0) (= g_s28_30 e29) (= g_s29_32 e31) (= g_s30_34 e33) (= g_s31_36 e35) (= g_s32_38 e37) (= g_s33_40 e39) (= g_s34_42 e41) (= g_s35_44 e43) (= g_s36_46 e45) (= g_s37_48 e47) (= g_s38_50 e49) (= g_s39_52 e51) (= g_s40_54 e53) (= g_s41_56 e55) (= g_s42_58 e57) (= g_s43_60 e59) (= g_s44_62 e61) (= g_s45_64 e63) (= g_s46_66 e65) (= g_s47_68 e67) (= g_s48_70 e69) (= g_s49_72 e71) (= g_s50_74 e73) (= g_s51_76 e75) (= g_s52_78 e77) (= g_s53_80 e79) (= g_s54_82 e81) (= g_s55_84 e83) (= g_s56_86 e85) (= g_s57_88 e87) (= g_s58_90 e89) (= g_s59_92 e91) (= g_s60_94 e93) (= g_s61_96 e95) (= g_s62_98 e97) (= g_s63_100 e99) (= g_s64_102 e101) (= g_s65_104 e103) (= g_s66_106 e105) (= g_s67_108 e107) (= g_s68_110 e109) (= g_s69_112 e111) (= g_s70_114 e113) (= g_s71_116 e115) (= g_s72_118 e117) (= g_s73_120 e119) (= g_s74_122 e121) (= g_s75_124 e123) (= g_s76_126 e125) (= g_s77_128 e127) (= g_s78_130 e129) (= g_s79_132 e131) (= g_s80_134 e133) (= g_s81_136 e135) (= g_s82_138 e137) (= g_s83_140 e139) (= g_s84_142 e141) (= g_s85_144 e143) (= g_s86_146 e145)))
(define-fun |def_mchcst| () Bool true)
(define-fun |def_aprp| () Bool true)
(define-fun |def_abs| () Bool (and (mem g_s87_147 (|+->| g_s2_3 g_s13_14)) (mem g_s88_148 (|+->| g_s2_3 g_s13_14)) (subset g_s89_149 g_s2_3) (= g_s90_150 (dom g_s87_147)) (= (dom g_s87_147) g_s90_150) (mem g_s87_147 (|+->| g_s2_3 g_s13_14)) (mem g_s88_148 (|+->| g_s2_3 g_s13_14)) (subset g_s89_149 g_s2_3) (subset g_s90_150 g_s2_3)))
(define-fun |def_inv| () Bool (and (mem g_s91$1_151 (|-->| g_s0_1 g_s12_13)) (mem g_s92$1_152 (|-->| g_s0_1 g_s12_13)) (mem g_s93$1_153 (|-->| g_s0_1 BOOL)) (= g_s87_147 (range_restriction (domain_restriction g_s2_3 g_s91$1_151) g_s13_14)) (= g_s88_148 (range_restriction (domain_restriction g_s2_3 g_s92$1_152) g_s13_14)) (= g_s89_149 (binary_inter g_s2_3 (image (inverse g_s93$1_153) (SET TRUE))))))
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
(assert (not (mem (set_prod g_s0_1 (SET FALSE)) (|-->| g_s0_1 BOOL))))
(check-sat)
(pop 1)
; PO 2 in group 0
(push 1)
(assert (not (mem (set_prod g_s0_1 (SET g_s18_19)) (|-->| g_s0_1 g_s12_13))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 0
(push 1)
(assert (not (= empty (binary_inter g_s2_3 (image (inverse (set_prod g_s0_1 (SET FALSE))) (SET TRUE))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 0
(push 1)
(assert (not (= empty (range_restriction (domain_restriction g_s2_3 (set_prod g_s0_1 (SET g_s18_19))) g_s13_14))))
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
(define-fun lh_1 () Bool (mem g_s97_154 g_s0_1))
(define-fun lh_2 () Bool (mem g_s97_154 g_s2_3))
(define-fun lh_3 () Bool (mem g_s98_155 g_s12_13))
(define-fun lh_4 () Bool (mem g_s99_156 g_s12_13))
(define-fun lh_5 () Bool (mem g_s100_157 BOOL))
(define-fun lh_6 () Bool (= (bool (mem g_s98_155 g_s14_15)) TRUE))
(define-fun lh_7 () Bool (= (bool (mem g_s99_156 g_s14_15)) TRUE))
(define-fun lh_8 () Bool (= g_s100_157 TRUE))
(define-fun lh_9 () Bool (mem g_s98_155 g_s14_15))
(define-fun lh_10 () Bool (mem g_s99_156 g_s14_15))
; PO 1 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10) (mem (|<+| g_s92$1_152 (SET (mapplet g_s97_154 g_s99_156))) (|-->| g_s0_1 g_s12_13)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10) (mem (|<+| g_s91$1_151 (SET (mapplet g_s97_154 g_s98_155))) (|-->| g_s0_1 g_s12_13)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10) (mem (|<+| g_s93$1_153 (SET (mapplet g_s97_154 g_s25_26))) (|-->| g_s0_1 BOOL)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10) (= (|<+| g_s88_148 (SET (mapplet g_s97_154 g_s99_156))) (range_restriction (domain_restriction g_s2_3 (|<+| g_s92$1_152 (SET (mapplet g_s97_154 g_s99_156)))) g_s13_14)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 5 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10) (= (|<+| g_s87_147 (SET (mapplet g_s97_154 g_s98_155))) (range_restriction (domain_restriction g_s2_3 (|<+| g_s91$1_151 (SET (mapplet g_s97_154 g_s98_155)))) g_s13_14)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 6 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4 lh_5 lh_6 lh_7 lh_8 lh_9 lh_10) (= (binary_union g_s89_149 (SET g_s97_154)) (binary_inter g_s2_3 (image (inverse (|<+| g_s93$1_153 (SET (mapplet g_s97_154 g_s25_26)))) (SET TRUE)))))))
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
(assert (= g_s102$1_159 g_s102_158))
(define-fun lh_1 () Bool (mem g_s97_154 g_s0_1))
(define-fun lh_2 () Bool (mem g_s97_154 g_s2_3))
(define-fun lh_3 () Bool (mem (apply g_s91$1_151 g_s97_154) g_s12_13))
; PO 1 in group 2
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem (apply g_s91$1_151 g_s97_154) g_s12_13))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 2
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (= (bool (mem (apply g_s91$1_151 g_s97_154) g_s13_14)) (bool (mem g_s97_154 (dom g_s87_147)))))))
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
(assert (= g_s105$1_161 g_s105_160))
(define-fun lh_1 () Bool (mem g_s97_154 g_s0_1))
(define-fun lh_2 () Bool (mem g_s97_154 g_s2_3))
(define-fun lh_3 () Bool (mem (apply g_s92$1_152 g_s97_154) g_s12_13))
; PO 1 in group 3
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem (apply g_s92$1_152 g_s97_154) g_s12_13))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 3
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (= (bool (mem (apply g_s92$1_152 g_s97_154) g_s13_14)) (bool (mem g_s97_154 (dom g_s88_148)))))))
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
(assert (= g_s107$1_163 g_s107_162))
(define-fun lh_1 () Bool (mem g_s97_154 g_s0_1))
(define-fun lh_2 () Bool (mem g_s97_154 g_s2_3))
(define-fun lh_3 () Bool (mem (apply g_s91$1_151 g_s97_154) g_s12_13))
; PO 1 in group 4
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem (apply g_s91$1_151 g_s97_154) g_s12_13))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 4
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (= (bool (mem (apply g_s91$1_151 g_s97_154) g_s13_14)) (bool (mem g_s97_154 (dom g_s87_147)))))))
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
(assert (= g_s99$1_164 g_s99_156))
(define-fun lh_1 () Bool (mem g_s97_154 g_s0_1))
(define-fun lh_2 () Bool (mem g_s97_154 g_s2_3))
(define-fun lh_3 () Bool (mem g_s97_154 (dom g_s88_148)))
; PO 1 in group 5
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (mem (apply g_s88_148 g_s97_154) g_s12_13))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 5
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (= (apply g_s92$1_152 g_s97_154) (apply g_s88_148 g_s97_154)))))
(set-info :status unknown)
(check-sat)
(pop 1)
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
(assert (= g_s98$1_165 g_s98_155))
(define-fun lh_1 () Bool (mem g_s97_154 g_s0_1))
(define-fun lh_2 () Bool (mem g_s97_154 g_s2_3))
(define-fun lh_3 () Bool (mem g_s97_154 (dom g_s87_147)))
; PO 1 in group 6
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (mem (apply g_s87_147 g_s97_154) g_s12_13))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 6
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (= (apply g_s91$1_151 g_s97_154) (apply g_s87_147 g_s97_154)))))
(set-info :status unknown)
(check-sat)
(pop 1)
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
(assert (= g_s100$1_166 g_s100_157))
(define-fun lh_1 () Bool (mem g_s97_154 g_s0_1))
(define-fun lh_2 () Bool (mem g_s97_154 g_s2_3))
; PO 1 in group 7
(assert (not (=> (and lh_1 lh_2) (= (apply g_s93$1_153 g_s97_154) (bool (mem g_s97_154 g_s89_149))))))
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
(assert (= g_s105$1_161 g_s105_160))
(assert (= g_s99$1_164 g_s99_156))
(define-fun lh_1 () Bool (mem g_s97_154 g_s0_1))
(define-fun lh_2 () Bool (mem g_s97_154 g_s2_3))
(define-fun lh_3 () Bool (mem (apply g_s92$1_152 g_s97_154) g_s12_13))
(define-fun lh_4 () Bool (mem g_s97_154 (dom g_s88_148)))
; PO 1 in group 8
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem (apply g_s92$1_152 g_s97_154) g_s12_13))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 8
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem (apply g_s88_148 g_s97_154) g_s12_13))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 8
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (= (bool (mem (apply g_s92$1_152 g_s97_154) g_s13_14)) (bool (mem g_s97_154 (dom g_s88_148)))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 8
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (= (apply g_s92$1_152 g_s97_154) (apply g_s88_148 g_s97_154)))))
(set-info :status unknown)
(check-sat)
(pop 1)
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
(assert (= g_s107$1_163 g_s107_162))
(assert (= g_s98$1_165 g_s98_155))
(define-fun lh_1 () Bool (mem g_s97_154 g_s0_1))
(define-fun lh_2 () Bool (mem g_s97_154 g_s2_3))
(define-fun lh_3 () Bool (mem (apply g_s91$1_151 g_s97_154) g_s12_13))
(define-fun lh_4 () Bool (mem g_s97_154 (dom g_s87_147)))
; PO 1 in group 9
(push 1)
(assert (not (=> (and lh_1 lh_2) (mem (apply g_s91$1_151 g_s97_154) g_s12_13))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 9
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem (apply g_s87_147 g_s97_154) g_s12_13))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 9
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (= (bool (mem (apply g_s91$1_151 g_s97_154) g_s13_14)) (bool (mem g_s97_154 (dom g_s87_147)))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 9
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (= (apply g_s91$1_151 g_s97_154) (apply g_s87_147 g_s97_154)))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 10 
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
(assert (mem g_s97_154 g_s0_1))
(assert (mem g_s97_154 g_s2_3))
(assert (mem g_s97_154 g_s0_1))
(assert (mem g_s97_154 g_s2_3))
; PO 1 in group 10
(push 1)
(assert (not (mem g_s91$1_151 (|+->| (dom g_s91$1_151) (ran g_s91$1_151)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 10
(push 1)
(assert (not (mem g_s97_154 (dom g_s91$1_151))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 11 
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
(assert (mem g_s97_154 g_s0_1))
(assert (mem g_s97_154 g_s2_3))
(assert (mem g_s97_154 g_s0_1))
(assert (mem g_s97_154 g_s2_3))
; PO 1 in group 11
(push 1)
(assert (not (mem g_s91$1_151 (|+->| (dom g_s91$1_151) (ran g_s91$1_151)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 11
(push 1)
(assert (not (mem g_s97_154 (dom g_s91$1_151))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 12 
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
(assert (mem g_s97_154 g_s0_1))
(assert (mem g_s97_154 g_s2_3))
(assert (mem g_s97_154 (dom g_s87_147)))
(assert (mem g_s97_154 g_s0_1))
(assert (mem g_s97_154 g_s2_3))
(assert (mem g_s97_154 (dom g_s87_147)))
; PO 1 in group 12
(push 1)
(assert (not (mem g_s91$1_151 (|+->| (dom g_s91$1_151) (ran g_s91$1_151)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 12
(push 1)
(assert (not (mem g_s97_154 (dom g_s91$1_151))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 13 
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
(assert (mem g_s97_154 g_s0_1))
(assert (mem g_s97_154 g_s2_3))
(assert (mem g_s97_154 g_s0_1))
(assert (mem g_s97_154 g_s2_3))
; PO 1 in group 13
(push 1)
(assert (not (mem g_s92$1_152 (|+->| (dom g_s92$1_152) (ran g_s92$1_152)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 13
(push 1)
(assert (not (mem g_s97_154 (dom g_s92$1_152))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 14 
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
(assert (mem g_s97_154 g_s0_1))
(assert (mem g_s97_154 g_s2_3))
(assert (mem g_s97_154 g_s0_1))
(assert (mem g_s97_154 g_s2_3))
; PO 1 in group 14
(push 1)
(assert (not (mem g_s92$1_152 (|+->| (dom g_s92$1_152) (ran g_s92$1_152)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 14
(push 1)
(assert (not (mem g_s97_154 (dom g_s92$1_152))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 15 
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
(assert (mem g_s97_154 g_s0_1))
(assert (mem g_s97_154 g_s2_3))
(assert (mem g_s97_154 (dom g_s88_148)))
(assert (mem g_s97_154 g_s0_1))
(assert (mem g_s97_154 g_s2_3))
(assert (mem g_s97_154 (dom g_s88_148)))
; PO 1 in group 15
(push 1)
(assert (not (mem g_s92$1_152 (|+->| (dom g_s92$1_152) (ran g_s92$1_152)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 15
(push 1)
(assert (not (mem g_s97_154 (dom g_s92$1_152))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 16 
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
(assert (mem g_s97_154 g_s0_1))
(assert (mem g_s97_154 g_s2_3))
(assert (mem g_s97_154 g_s0_1))
(assert (mem g_s97_154 g_s2_3))
; PO 1 in group 16
(push 1)
(assert (not (mem g_s93$1_153 (|+->| (dom g_s93$1_153) (ran g_s93$1_153)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 16
(push 1)
(assert (not (mem g_s97_154 (dom g_s93$1_153))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 17 
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
(assert (mem g_s97_154 g_s0_1))
(assert (mem g_s97_154 g_s2_3))
(assert (mem g_s97_154 g_s0_1))
(assert (mem g_s97_154 g_s2_3))
; PO 1 in group 17
(push 1)
(assert (not (mem g_s91$1_151 (|+->| (dom g_s91$1_151) (ran g_s91$1_151)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 17
(push 1)
(assert (not (mem g_s97_154 (dom g_s91$1_151))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
(exit)