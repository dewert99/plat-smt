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
(declare-fun e18 () U)
(declare-fun e0 () U)
(declare-fun e89 () U)
(declare-fun e22 () U)
(declare-fun e20 () U)
(declare-fun e84 () U)
(declare-fun e19 () U)
(declare-fun g_s0_1 () U)
(declare-fun g_s1_2 () U)
(declare-fun g_s10_10 () U)
(declare-fun g_s100_118 () U)
(declare-fun g_s101_128 () U)
(declare-fun g_s102_129 () U)
(declare-fun g_s106_126 () U)
(declare-fun g_s106$1_127 () U)
(declare-fun g_s11_13 () U)
(declare-fun g_s112_130 () U)
(declare-fun g_s113_131 () U)
(declare-fun g_s12_12 () U)
(declare-fun g_s13_15 () U)
(declare-fun g_s14_14 () U)
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
(declare-fun g_s68_85 () U)
(declare-fun g_s69_86 () U)
(declare-fun g_s7_8 () U)
(declare-fun g_s70_87 () U)
(declare-fun g_s71_88 () U)
(declare-fun g_s72_90 () U)
(declare-fun g_s73_91 () U)
(declare-fun g_s74_92 () U)
(declare-fun g_s75_93 () U)
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
(declare-fun e120 () U)
(declare-fun e125 () U)
(declare-fun e122 () U)
(declare-fun e124 () U)
(declare-fun e119 () U)
(declare-fun e121 () U)
(declare-fun e123 () U)
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
(define-fun |def_ctx| () Bool (and (= g_s0_1 (SET (mapplet g_s2_3 g_s1_2))) (= g_s3_4 (SET (mapplet g_s8_9 (mapplet g_s7_8 (mapplet g_s6_7 (mapplet g_s5_6 g_s4_5)))))) (mem g_s9_11 g_s10_10) (mem g_s11_13 g_s12_12) (mem g_s13_15 g_s14_14) (mem g_s15_16 g_s14_14) (mem g_s16_17 g_s14_14) (= g_s9_11 e18) (= g_s11_13 e19) (= g_s13_15 e20) (and (|>=i| g_s15_16 e0) (|<=i| g_s15_16 g_s13_15)) (and (|>=i| g_s16_17 e0) (|<=i| g_s16_17 g_s13_15)) (not (= g_s15_16 g_s16_17)) (= g_s17_21 (SET (mapplet g_s16_17 g_s15_16))) (|<=i| g_s15_16 e22) (|<=i| g_s16_17 e22) (= g_s18_23 (SET (mapplet (mapplet FALSE g_s16_17) (mapplet TRUE g_s15_16)))) (= g_s10_10 (interval e0 e18)) (= g_s12_12 (interval e0 e19)) (= g_s14_14 (interval e0 e20)) (mem g_s19_24 (|-->| (set_prod g_s10_10 g_s14_14) g_s10_10)) (mem g_s20_25 (|-->| (set_prod g_s10_10 g_s14_14) g_s10_10)) (mem g_s21_26 (|-->| g_s10_10 g_s10_10)) (mem g_s22_27 (|-->| (set_prod g_s10_10 g_s10_10) g_s10_10)) (mem g_s23_28 (|-->| (set_prod g_s10_10 g_s10_10) g_s10_10)) (mem g_s24_29 (|-->| (set_prod g_s10_10 g_s10_10) g_s10_10)) (mem g_s25_30 (|-->| (set_prod g_s12_12 g_s14_14) g_s12_12)) (mem g_s26_31 (|-->| (set_prod g_s12_12 g_s14_14) g_s12_12)) (mem g_s27_32 (|-->| g_s12_12 g_s12_12)) (mem g_s28_33 (|-->| (set_prod g_s12_12 g_s12_12) g_s12_12)) (mem g_s29_34 (|-->| (set_prod g_s12_12 g_s12_12) g_s12_12)) (mem g_s30_35 (|-->| (set_prod g_s12_12 g_s12_12) g_s12_12)) (mem g_s31_36 (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14)) (mem g_s32_37 (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14)) (mem g_s33_38 (|-->| g_s14_14 g_s14_14)) (mem g_s34_39 (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14)) (mem g_s35_40 (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14)) (mem g_s36_41 (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14)) (mem g_s37_42 (|-->| (set_prod g_s10_10 g_s10_10) g_s10_10)) (mem g_s38_43 (|-->| (set_prod g_s10_10 g_s10_10) g_s10_10)) (mem g_s39_44 (|-->| (set_prod g_s10_10 g_s10_10) g_s10_10)) (mem g_s40_45 (|-->| (set_prod g_s12_12 g_s12_12) g_s12_12)) (mem g_s41_46 (|-->| (set_prod g_s12_12 g_s12_12) g_s12_12)) (mem g_s42_47 (|-->| (set_prod g_s12_12 g_s12_12) g_s12_12)) (mem g_s43_48 (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14)) (mem g_s44_49 (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14)) (mem g_s45_50 (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14)) (= g_s19_24 e51) (= g_s25_30 e52) (= g_s31_36 e53) (= g_s20_25 e54) (= g_s26_31 e55) (= g_s32_37 e56) (= g_s37_42 e57) (= g_s38_43 e58) (= g_s39_44 e59) (= g_s40_45 e60) (= g_s41_46 e61) (= g_s42_47 e62) (= g_s43_48 e63) (= g_s44_49 e64) (= g_s45_50 e65) (mem g_s50_67 (|-->| (set_prod (set_prod (set_prod g_s10_10 (|-->| (interval e0 g_s51_66) g_s10_10)) g_s14_14) g_s10_10) g_s12_12)) (mem g_s52_69 (|-->| (set_prod (set_prod (set_prod g_s10_10 (|-->| (interval e0 g_s53_68) g_s10_10)) g_s14_14) g_s10_10) g_s12_12)) (mem g_s54_70 g_s10_10) (mem g_s55_71 g_s10_10) (not (= g_s54_70 g_s55_71)) (mem g_s56_72 NAT1) (mem g_s57_73 g_s10_10) (|<i| g_s57_73 (|-i| g_s9_11 g_s11_13)) (mem g_s58_74 g_s10_10) (= g_s58_74 (|+i| g_s57_73 g_s56_72)) (mem g_s59_75 g_s10_10) (mem g_s60_76 g_s10_10) (mem g_s61_77 NAT1) (mem g_s62_78 NAT1) (mem g_s56_72 NAT1) (mem g_s63_79 g_s10_10) (mem g_s64_80 g_s10_10) (mem g_s65_81 g_s10_10) (= g_s64_80 (|+i| g_s63_79 g_s61_77)) (= g_s65_81 (|+i| g_s63_79 g_s62_78)) (mem g_s66_82 g_s12_12) (mem g_s67_83 g_s10_10) (|<=i| g_s67_83 e84) (mem g_s68_85 NAT1) (mem g_s69_86 g_s10_10) (|<i| g_s69_86 (|-i| g_s9_11 g_s11_13)) (mem g_s70_87 g_s10_10) (= g_s70_87 (|+i| g_s69_86 g_s68_85)) (mem g_s71_88 g_s10_10) (|<=i| e89 g_s71_88) (mem g_s72_90 g_s10_10) (mem g_s73_91 g_s10_10) (mem g_s74_92 g_s10_10) (|<i| g_s74_92 (|-i| g_s9_11 g_s11_13)) (mem g_s75_93 g_s10_10) (mem g_s76_94 NAT1) (= g_s75_93 (|+i| g_s74_92 g_s76_94)) (mem g_s77_95 NATURAL1) (mem g_s78_96 g_s10_10) (= g_s78_96 (|+i| g_s74_92 g_s77_95)) (mem g_s79_97 g_s10_10) (mem g_s80_98 g_s10_10) (mem g_s81_99 g_s10_10) (mem g_s82_100 g_s10_10) (mem g_s83_101 g_s12_12) (|<i| (|*i| e22 g_s83_101) g_s11_13) (mem g_s84_102 NAT1) (mem g_s85_103 g_s12_12) (mem g_s86_104 g_s12_12) (= g_s86_104 (|+i| g_s85_103 g_s84_102)) (mem g_s87_105 g_s10_10) (mem g_s88_106 g_s10_10) (mem g_s89_107 g_s10_10) (mem g_s90_108 g_s10_10) (mem g_s91_109 g_s10_10) (mem g_s92_110 g_s10_10) (mem g_s93_111 g_s10_10) (mem g_s94_112 g_s10_10) (mem g_s95_113 g_s10_10) (mem g_s96_114 g_s10_10)))
(define-fun |def_seext| () Bool (and (mem g_s18_23 (|+->| BOOL g_s14_14)) (mem g_s18_23 (|+->| BOOL g_s12_12)) (mem g_s18_23 (|+->| BOOL g_s10_10))))
(define-fun |def_mchcst| () Bool true)
(define-fun |def_aprp| () Bool (and (mem g_s97_115 (|-->| (set_prod g_s10_10 g_s10_10) g_s10_10)) (= (apply g_s97_115 (mapplet e0 e0)) e0) (mem g_s98_116 (|-->| (set_prod g_s12_12 g_s12_12) g_s12_12)) (mem g_s99_117 (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14)) (mem g_s100_118 (|-->| (set_prod g_s10_10 g_s10_10) g_s10_10))))
(define-fun |def_abs| () Bool true)
(define-fun |def_inv| () Bool true)
(define-fun |def_ass| () Bool true)
(define-fun |def_sets| () Bool true)
(define-fun |def_imlprp| () Bool (and (= g_s97_115 (|<+| e120 e119)) (= g_s98_116 (|<+| e122 e121)) (= g_s99_117 (|<+| e124 e123)) (= g_s100_118 (|<+| e125 e119))))
(define-fun |def_imprp| () Bool true)
(define-fun |def_imext| () Bool true)
; PO group 0 
(push 1)
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_imprp|)
; PO 1 in group 0
(push 1)
(assert (not (mem (|<+| e122 e121) (|-->| (set_prod g_s12_12 g_s12_12) g_s12_12))))
(check-sat)
(pop 1)
; PO 2 in group 0
(push 1)
(assert (not (mem (|<+| e120 e119) (|-->| (set_prod g_s10_10 g_s10_10) g_s10_10))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 0
(push 1)
(assert (not (mem (|<+| e125 e119) (|-->| (set_prod g_s10_10 g_s10_10) g_s10_10))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 0
(push 1)
(assert (not (mem (|<+| e124 e123) (|-->| (set_prod g_s14_14 g_s14_14) g_s14_14))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 5 in group 0
(push 1)
(assert (not (= (apply (|<+| e120 e119) (mapplet e0 e0)) e0)))
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
(assert (= g_s106$1_127 g_s106_126))
(define-fun lh_1 () Bool (mem g_s101_128 g_s10_10))
(define-fun lh_2 () Bool (mem g_s102_129 g_s10_10))
(define-fun lh_3 () Bool (mem g_s106_126 g_s10_10))
(define-fun lh_4 () Bool (|<=i| g_s102_129 g_s101_128))
; PO 1 in group 1
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (= (apply g_s38_43 (mapplet g_s101_128 g_s102_129)) (apply g_s97_115 (mapplet g_s101_128 g_s102_129))))))
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
(assert (= g_s106$1_127 g_s106_126))
(define-fun lh_1 () Bool (mem g_s101_128 g_s12_12))
(define-fun lh_2 () Bool (mem g_s102_129 g_s12_12))
(define-fun lh_3 () Bool (mem g_s106_126 g_s12_12))
(define-fun lh_4 () Bool (|<=i| g_s102_129 g_s101_128))
; PO 1 in group 2
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (= (apply g_s41_46 (mapplet g_s101_128 g_s102_129)) (apply g_s98_116 (mapplet g_s101_128 g_s102_129))))))
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
(assert (= g_s106$1_127 g_s106_126))
(define-fun lh_1 () Bool (mem g_s101_128 g_s14_14))
(define-fun lh_2 () Bool (mem g_s102_129 g_s14_14))
(define-fun lh_3 () Bool (mem g_s106_126 g_s14_14))
(define-fun lh_4 () Bool (|<=i| g_s102_129 g_s101_128))
; PO 1 in group 3
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (= (apply g_s44_49 (mapplet g_s101_128 g_s102_129)) (apply g_s99_117 (mapplet g_s101_128 g_s102_129))))))
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
(assert (= g_s106$1_127 g_s106_126))
(define-fun lh_1 () Bool (mem g_s101_128 g_s10_10))
(define-fun lh_2 () Bool (mem g_s102_129 g_s10_10))
(define-fun lh_3 () Bool (mem g_s106_126 g_s10_10))
(define-fun lh_4 () Bool (|<=i| g_s102_129 g_s101_128))
; PO 1 in group 4
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (= (apply g_s38_43 (mapplet g_s101_128 g_s102_129)) (apply g_s100_118 (mapplet g_s101_128 g_s102_129))))))
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
(assert (= g_s106$1_127 g_s106_126))
(define-fun lh_1 () Bool (mem g_s112_130 g_s14_14))
(define-fun lh_2 () Bool (mem g_s113_131 g_s14_14))
(define-fun lh_3 () Bool (|<=i| (|+i| g_s112_130 g_s113_131) g_s13_15))
(define-fun lh_4 () Bool (mem g_s106_126 g_s14_14))
; PO 1 in group 5
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem (|+i| g_s112_130 g_s113_131) g_s14_14))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 5
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (= (apply g_s43_48 (mapplet g_s112_130 g_s113_131)) (|+i| g_s112_130 g_s113_131)))))
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
(assert (= g_s106$1_127 g_s106_126))
(define-fun lh_1 () Bool (mem g_s112_130 g_s14_14))
(define-fun lh_2 () Bool (mem g_s113_131 g_s14_14))
(define-fun lh_3 () Bool (|<=i| g_s113_131 g_s112_130))
(define-fun lh_4 () Bool (mem g_s106_126 g_s14_14))
; PO 1 in group 6
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem (|-i| g_s112_130 g_s113_131) g_s14_14))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 6
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (= (apply g_s44_49 (mapplet g_s112_130 g_s113_131)) (|-i| g_s112_130 g_s113_131)))))
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
(assert (= g_s106$1_127 g_s106_126))
(define-fun lh_1 () Bool (mem g_s112_130 g_s14_14))
(define-fun lh_2 () Bool (mem g_s113_131 g_s14_14))
(define-fun lh_3 () Bool (|<=i| (|*i| g_s112_130 g_s113_131) g_s13_15))
(define-fun lh_4 () Bool (mem g_s106_126 g_s14_14))
; PO 1 in group 7
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem (|*i| g_s112_130 g_s113_131) g_s14_14))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 7
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (= (apply g_s45_50 (mapplet g_s112_130 g_s113_131)) (|*i| g_s112_130 g_s113_131)))))
(set-info :status unknown)
(check-sat)
(pop 1)
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
(assert (= g_s106$1_127 g_s106_126))
(define-fun lh_1 () Bool (mem g_s112_130 g_s12_12))
(define-fun lh_2 () Bool (mem g_s113_131 g_s12_12))
(define-fun lh_3 () Bool (|<=i| (|+i| g_s112_130 g_s113_131) g_s11_13))
(define-fun lh_4 () Bool (mem g_s106_126 g_s12_12))
; PO 1 in group 8
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem (|+i| g_s112_130 g_s113_131) g_s12_12))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 8
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (= (apply g_s40_45 (mapplet g_s112_130 g_s113_131)) (|+i| g_s112_130 g_s113_131)))))
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
(assert (= g_s106$1_127 g_s106_126))
(define-fun lh_1 () Bool (mem g_s112_130 g_s12_12))
(define-fun lh_2 () Bool (mem g_s113_131 g_s12_12))
(define-fun lh_3 () Bool (|<=i| g_s113_131 g_s112_130))
(define-fun lh_4 () Bool (mem g_s106_126 g_s12_12))
; PO 1 in group 9
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem (|-i| g_s112_130 g_s113_131) g_s12_12))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 9
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (= (apply g_s41_46 (mapplet g_s112_130 g_s113_131)) (|-i| g_s112_130 g_s113_131)))))
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
(assert (= g_s106$1_127 g_s106_126))
(define-fun lh_1 () Bool (mem g_s112_130 g_s12_12))
(define-fun lh_2 () Bool (mem g_s113_131 g_s12_12))
(define-fun lh_3 () Bool (|<=i| (|*i| g_s112_130 g_s113_131) g_s11_13))
(define-fun lh_4 () Bool (mem g_s106_126 g_s12_12))
; PO 1 in group 10
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem (|*i| g_s112_130 g_s113_131) g_s12_12))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 10
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (= (apply g_s42_47 (mapplet g_s112_130 g_s113_131)) (|*i| g_s112_130 g_s113_131)))))
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
(assert (= g_s106$1_127 g_s106_126))
(define-fun lh_1 () Bool (mem g_s112_130 g_s10_10))
(define-fun lh_2 () Bool (mem g_s113_131 g_s10_10))
(define-fun lh_3 () Bool (|<=i| (|+i| g_s112_130 g_s113_131) g_s9_11))
(define-fun lh_4 () Bool (mem g_s106_126 g_s10_10))
; PO 1 in group 11
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem (|+i| g_s112_130 g_s113_131) g_s10_10))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 11
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (= (apply g_s37_42 (mapplet g_s112_130 g_s113_131)) (|+i| g_s112_130 g_s113_131)))))
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
(assert (= g_s106$1_127 g_s106_126))
(define-fun lh_1 () Bool (mem g_s112_130 g_s10_10))
(define-fun lh_2 () Bool (mem g_s113_131 g_s10_10))
(define-fun lh_3 () Bool (|<=i| g_s113_131 g_s112_130))
(define-fun lh_4 () Bool (mem g_s106_126 g_s10_10))
; PO 1 in group 12
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem (|-i| g_s112_130 g_s113_131) g_s10_10))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 12
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (= (apply g_s38_43 (mapplet g_s112_130 g_s113_131)) (|-i| g_s112_130 g_s113_131)))))
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
(assert (= g_s106$1_127 g_s106_126))
(define-fun lh_1 () Bool (mem g_s112_130 g_s10_10))
(define-fun lh_2 () Bool (mem g_s113_131 g_s10_10))
(define-fun lh_3 () Bool (|<=i| (|*i| g_s112_130 g_s113_131) g_s9_11))
(define-fun lh_4 () Bool (mem g_s106_126 g_s10_10))
; PO 1 in group 13
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (mem (|*i| g_s112_130 g_s113_131) g_s10_10))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 13
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3 lh_4) (= (apply g_s39_44 (mapplet g_s112_130 g_s113_131)) (|*i| g_s112_130 g_s113_131)))))
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
(assert (mem g_s101_128 g_s10_10))
(assert (mem g_s102_129 g_s10_10))
(assert (mem g_s106_126 g_s10_10))
(define-fun lh_1 () Bool (|<=i| g_s102_129 g_s101_128))
; PO 1 in group 14
(push 1)
(assert (not (=> lh_1 (mem g_s38_43 (|+->| (dom g_s38_43) (ran g_s38_43))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 14
(push 1)
(assert (not (=> lh_1 (mem (mapplet g_s101_128 g_s102_129) (dom g_s38_43)))))
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
(assert (mem g_s101_128 g_s12_12))
(assert (mem g_s102_129 g_s12_12))
(assert (mem g_s106_126 g_s12_12))
(define-fun lh_1 () Bool (|<=i| g_s102_129 g_s101_128))
; PO 1 in group 15
(push 1)
(assert (not (=> lh_1 (mem g_s41_46 (|+->| (dom g_s41_46) (ran g_s41_46))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 15
(push 1)
(assert (not (=> lh_1 (mem (mapplet g_s101_128 g_s102_129) (dom g_s41_46)))))
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
(assert (mem g_s101_128 g_s14_14))
(assert (mem g_s102_129 g_s14_14))
(assert (mem g_s106_126 g_s14_14))
(define-fun lh_1 () Bool (|<=i| g_s102_129 g_s101_128))
; PO 1 in group 16
(push 1)
(assert (not (=> lh_1 (mem g_s44_49 (|+->| (dom g_s44_49) (ran g_s44_49))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 16
(push 1)
(assert (not (=> lh_1 (mem (mapplet g_s101_128 g_s102_129) (dom g_s44_49)))))
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
(assert (mem g_s101_128 g_s10_10))
(assert (mem g_s102_129 g_s10_10))
(assert (mem g_s106_126 g_s10_10))
(define-fun lh_1 () Bool (|<=i| g_s102_129 g_s101_128))
; PO 1 in group 17
(push 1)
(assert (not (=> lh_1 (mem g_s38_43 (|+->| (dom g_s38_43) (ran g_s38_43))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 17
(push 1)
(assert (not (=> lh_1 (mem (mapplet g_s101_128 g_s102_129) (dom g_s38_43)))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 18 
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
(assert (mem g_s112_130 g_s14_14))
(assert (mem g_s113_131 g_s14_14))
(assert (|<=i| (|+i| g_s112_130 g_s113_131) g_s13_15))
(assert (mem g_s106_126 g_s14_14))
; PO 1 in group 18
(push 1)
(assert (not (mem g_s43_48 (|+->| (dom g_s43_48) (ran g_s43_48)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 18
(push 1)
(assert (not (mem (mapplet g_s112_130 g_s113_131) (dom g_s43_48))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 19 
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
(assert (mem g_s112_130 g_s14_14))
(assert (mem g_s113_131 g_s14_14))
(assert (|<=i| g_s113_131 g_s112_130))
(assert (mem g_s106_126 g_s14_14))
; PO 1 in group 19
(push 1)
(assert (not (mem g_s44_49 (|+->| (dom g_s44_49) (ran g_s44_49)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 19
(push 1)
(assert (not (mem (mapplet g_s112_130 g_s113_131) (dom g_s44_49))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 20 
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
(assert (mem g_s112_130 g_s14_14))
(assert (mem g_s113_131 g_s14_14))
(assert (|<=i| (|*i| g_s112_130 g_s113_131) g_s13_15))
(assert (mem g_s106_126 g_s14_14))
; PO 1 in group 20
(push 1)
(assert (not (mem g_s45_50 (|+->| (dom g_s45_50) (ran g_s45_50)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 20
(push 1)
(assert (not (mem (mapplet g_s112_130 g_s113_131) (dom g_s45_50))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 21 
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
(assert (mem g_s112_130 g_s12_12))
(assert (mem g_s113_131 g_s12_12))
(assert (|<=i| (|+i| g_s112_130 g_s113_131) g_s11_13))
(assert (mem g_s106_126 g_s12_12))
; PO 1 in group 21
(push 1)
(assert (not (mem g_s40_45 (|+->| (dom g_s40_45) (ran g_s40_45)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 21
(push 1)
(assert (not (mem (mapplet g_s112_130 g_s113_131) (dom g_s40_45))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 22 
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
(assert (mem g_s112_130 g_s12_12))
(assert (mem g_s113_131 g_s12_12))
(assert (|<=i| g_s113_131 g_s112_130))
(assert (mem g_s106_126 g_s12_12))
; PO 1 in group 22
(push 1)
(assert (not (mem g_s41_46 (|+->| (dom g_s41_46) (ran g_s41_46)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 22
(push 1)
(assert (not (mem (mapplet g_s112_130 g_s113_131) (dom g_s41_46))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 23 
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
(assert (mem g_s112_130 g_s12_12))
(assert (mem g_s113_131 g_s12_12))
(assert (|<=i| (|*i| g_s112_130 g_s113_131) g_s11_13))
(assert (mem g_s106_126 g_s12_12))
; PO 1 in group 23
(push 1)
(assert (not (mem g_s42_47 (|+->| (dom g_s42_47) (ran g_s42_47)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 23
(push 1)
(assert (not (mem (mapplet g_s112_130 g_s113_131) (dom g_s42_47))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 24 
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
(assert (mem g_s112_130 g_s10_10))
(assert (mem g_s113_131 g_s10_10))
(assert (|<=i| (|+i| g_s112_130 g_s113_131) g_s9_11))
(assert (mem g_s106_126 g_s10_10))
; PO 1 in group 24
(push 1)
(assert (not (mem g_s37_42 (|+->| (dom g_s37_42) (ran g_s37_42)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 24
(push 1)
(assert (not (mem (mapplet g_s112_130 g_s113_131) (dom g_s37_42))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 25 
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
(assert (mem g_s112_130 g_s10_10))
(assert (mem g_s113_131 g_s10_10))
(assert (|<=i| g_s113_131 g_s112_130))
(assert (mem g_s106_126 g_s10_10))
; PO 1 in group 25
(push 1)
(assert (not (mem g_s38_43 (|+->| (dom g_s38_43) (ran g_s38_43)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 25
(push 1)
(assert (not (mem (mapplet g_s112_130 g_s113_131) (dom g_s38_43))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
; PO group 26 
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
(assert (mem g_s112_130 g_s10_10))
(assert (mem g_s113_131 g_s10_10))
(assert (|<=i| (|*i| g_s112_130 g_s113_131) g_s9_11))
(assert (mem g_s106_126 g_s10_10))
; PO 1 in group 26
(push 1)
(assert (not (mem g_s39_44 (|+->| (dom g_s39_44) (ran g_s39_44)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 26
(push 1)
(assert (not (mem (mapplet g_s112_130 g_s113_131) (dom g_s39_44))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
(exit)