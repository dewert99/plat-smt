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
(declare-fun e28 () U)
(declare-fun e0 () U)
(declare-fun e57 () U)
(declare-fun e40 () U)
(declare-fun e30 () U)
(declare-fun e29 () U)
(declare-fun g_s0_1 () U)
(declare-fun g_s1_2 () U)
(declare-fun g_s10_11 () U)
(declare-fun g_s100_106 () U)
(declare-fun g_s101_107 () U)
(declare-fun g_s102_108 () U)
(declare-fun g_s103_109 () U)
(declare-fun g_s104_110 () U)
(declare-fun g_s105_111 () U)
(declare-fun g_s106_112 () U)
(declare-fun g_s107_113 () U)
(declare-fun g_s108_114 () U)
(declare-fun g_s109_115 () U)
(declare-fun g_s11_12 () U)
(declare-fun g_s110_116 () U)
(declare-fun g_s111_117 () U)
(declare-fun g_s112_118 () U)
(declare-fun g_s113_119 () U)
(declare-fun g_s114_120 () U)
(declare-fun g_s115_121 () U)
(declare-fun g_s116_122 () U)
(declare-fun g_s117_123 () U)
(declare-fun g_s118_124 () U)
(declare-fun g_s119_125 () U)
(declare-fun g_s12_13 () U)
(declare-fun g_s120_126 () U)
(declare-fun g_s121_127 () U)
(declare-fun g_s122_128 () U)
(declare-fun g_s123_129 () U)
(declare-fun g_s124_130 () U)
(declare-fun g_s125_131 () U)
(declare-fun g_s125$1_140 () U)
(declare-fun g_s126_132 () U)
(declare-fun g_s126$1_139 () U)
(declare-fun g_s127_133 () U)
(declare-fun g_s128_134 () U)
(declare-fun g_s129_135 () U)
(declare-fun g_s13_14 () U)
(declare-fun g_s133_136 () U)
(declare-fun g_s134_137 () U)
(declare-fun g_s135_138 () U)
(declare-fun g_s14_15 () U)
(declare-fun g_s142_141 () U)
(declare-fun g_s15_16 () U)
(declare-fun g_s16_17 () U)
(declare-fun g_s17_18 () U)
(declare-fun g_s18_19 () U)
(declare-fun g_s19_21 () U)
(declare-fun g_s2_3 () U)
(declare-fun g_s20_20 () U)
(declare-fun g_s21_23 () U)
(declare-fun g_s22_22 () U)
(declare-fun g_s23_25 () U)
(declare-fun g_s24_24 () U)
(declare-fun g_s25_26 () U)
(declare-fun g_s26_27 () U)
(declare-fun g_s27_31 () U)
(declare-fun g_s28_32 () U)
(declare-fun g_s29_33 () U)
(declare-fun g_s3_4 () U)
(declare-fun g_s30_34 () U)
(declare-fun g_s31_35 () U)
(declare-fun g_s32_36 () U)
(declare-fun g_s33_37 () U)
(declare-fun g_s34_38 () U)
(declare-fun g_s35_39 () U)
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
(declare-fun g_s46_51 () U)
(declare-fun g_s47_52 () U)
(declare-fun g_s48_53 () U)
(declare-fun g_s49_54 () U)
(declare-fun g_s5_6 () U)
(declare-fun g_s50_55 () U)
(declare-fun g_s51_56 () U)
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
(declare-fun g_s63_69 () U)
(declare-fun g_s64_70 () U)
(declare-fun g_s65_71 () U)
(declare-fun g_s66_72 () U)
(declare-fun g_s67_73 () U)
(declare-fun g_s68_74 () U)
(declare-fun g_s69_75 () U)
(declare-fun g_s7_8 () U)
(declare-fun g_s70_76 () U)
(declare-fun g_s71_77 () U)
(declare-fun g_s72_78 () U)
(declare-fun g_s73_79 () U)
(declare-fun g_s74_80 () U)
(declare-fun g_s75_81 () U)
(declare-fun g_s76_82 () U)
(declare-fun g_s77_83 () U)
(declare-fun g_s78_84 () U)
(declare-fun g_s79_85 () U)
(declare-fun g_s8_9 () U)
(declare-fun g_s80_86 () U)
(declare-fun g_s81_87 () U)
(declare-fun g_s82_88 () U)
(declare-fun g_s83_89 () U)
(declare-fun g_s84_90 () U)
(declare-fun g_s85_91 () U)
(declare-fun g_s86_92 () U)
(declare-fun g_s87_93 () U)
(declare-fun g_s88_94 () U)
(declare-fun g_s89_95 () U)
(declare-fun g_s9_10 () U)
(declare-fun g_s90_96 () U)
(declare-fun g_s91_97 () U)
(declare-fun g_s92_98 () U)
(declare-fun g_s93_99 () U)
(declare-fun g_s94_100 () U)
(declare-fun g_s95_101 () U)
(declare-fun g_s96_102 () U)
(declare-fun g_s97_103 () U)
(declare-fun g_s98_104 () U)
(declare-fun g_s99_105 () U)
; Defines
(define-fun |def_B definitions| () Bool (and (= NAT (interval e0 MaxInt)) (= INT (interval MinInt MaxInt))))
(define-fun |def_ctx| () Bool (and (= g_s0_1 (SET (mapplet g_s2_3 g_s1_2))) (= g_s3_4 (SET (mapplet g_s5_6 g_s4_5))) (= g_s6_7 (SET (mapplet g_s8_9 g_s7_8))) (= g_s9_10 (SET (mapplet g_s18_19 (mapplet g_s17_18 (mapplet g_s16_17 (mapplet g_s15_16 (mapplet g_s14_15 (mapplet g_s13_14 (mapplet g_s12_13 (mapplet g_s11_12 g_s10_11)))))))))) (mem g_s19_21 g_s20_20) (mem g_s21_23 g_s22_22) (mem g_s23_25 g_s24_24) (mem g_s25_26 g_s24_24) (mem g_s26_27 g_s24_24) (= g_s19_21 e28) (= g_s21_23 e29) (= g_s23_25 e30) (and (|>=i| g_s25_26 e0) (|<=i| g_s25_26 g_s23_25)) (and (|>=i| g_s26_27 e0) (|<=i| g_s26_27 g_s23_25)) (not (= g_s25_26 g_s26_27)) (= g_s27_31 (SET (mapplet g_s26_27 g_s25_26))) (= g_s28_32 (SET (mapplet (mapplet FALSE g_s26_27) (mapplet TRUE g_s25_26)))) (= g_s20_20 (interval e0 e28)) (= g_s22_22 (interval e0 e29)) (= g_s24_24 (interval e0 e30)) (mem g_s29_33 g_s24_24) (mem g_s30_34 g_s24_24) (mem g_s31_35 g_s22_22) (mem g_s32_36 g_s22_22) (mem g_s33_37 g_s20_20) (mem g_s34_38 g_s20_20) (mem g_s35_39 NATURAL) (|<=i| e40 g_s35_39) (mem g_s36_41 NATURAL) (|<=i| e40 g_s36_41) (mem g_s37_42 NATURAL) (|<=i| e40 g_s37_42) (|<=i| g_s35_39 g_s37_42) (mem g_s38_43 g_s24_24) (mem g_s39_44 g_s24_24) (= g_s39_44 (|+i| g_s38_43 g_s35_39)) (mem g_s40_45 g_s24_24) (= g_s40_45 (|+i| g_s38_43 g_s36_41)) (mem g_s41_46 g_s24_24) (= g_s41_46 (|+i| g_s38_43 g_s37_42)) (mem g_s42_47 g_s22_22) (mem g_s43_48 g_s22_22) (mem g_s44_49 g_s24_24) (|<=i| g_s42_47 g_s43_48) (mem g_s45_50 g_s20_20) (mem g_s46_51 g_s20_20) (mem g_s47_52 g_s20_20) (mem g_s48_53 g_s20_20) (mem g_s49_54 g_s20_20) (mem g_s50_55 g_s24_24) (|<=i| e40 g_s50_55) (mem g_s51_56 g_s24_24) (= g_s51_56 (|-i| g_s50_55 e57)) (mem g_s52_58 NATURAL1) (mem g_s53_59 NATURAL1) (mem g_s54_60 NATURAL1) (mem g_s55_61 NATURAL1) (mem g_s56_62 NATURAL1) (mem g_s57_63 NATURAL1) (mem g_s58_64 NATURAL1) (mem g_s59_65 NATURAL1) (mem g_s60_66 g_s24_24) (mem g_s61_67 g_s24_24) (= g_s61_67 (|+i| g_s60_66 g_s52_58)) (mem g_s62_68 g_s24_24) (mem g_s63_69 g_s24_24) (= g_s63_69 (|+i| g_s62_68 g_s53_59)) (mem g_s64_70 g_s24_24) (= g_s64_70 (|+i| g_s62_68 g_s54_60)) (mem g_s65_71 g_s24_24) (= g_s65_71 (|+i| g_s62_68 g_s55_61)) (mem g_s66_72 g_s24_24) (= g_s66_72 (|+i| g_s62_68 g_s56_62)) (mem g_s67_73 g_s24_24) (= g_s67_73 (|+i| g_s62_68 g_s57_63)) (mem g_s68_74 g_s24_24) (= g_s68_74 (|+i| g_s62_68 g_s58_64)) (mem g_s69_75 g_s24_24) (= g_s69_75 (|+i| g_s62_68 g_s59_65)) (mem g_s70_76 g_s20_20) (mem g_s71_77 g_s20_20) (mem g_s72_78 g_s20_20) (mem g_s73_79 g_s20_20) (mem g_s74_80 g_s20_20) (mem g_s75_81 g_s20_20) (mem g_s76_82 g_s20_20) (mem g_s77_83 g_s20_20) (mem g_s78_84 g_s20_20) (mem g_s79_85 g_s20_20) (mem g_s80_86 g_s20_20) (mem g_s81_87 g_s20_20) (mem g_s82_88 g_s20_20) (mem g_s83_89 g_s20_20) (mem g_s84_90 g_s20_20) (mem g_s85_91 g_s20_20) (mem g_s86_92 g_s20_20) (mem g_s87_93 g_s20_20) (mem g_s88_94 g_s20_20) (mem g_s89_95 g_s24_24) (|<=i| e0 g_s89_95) (|<=i| e40 g_s89_95) (mem g_s90_96 g_s24_24) (= g_s90_96 (|-i| g_s89_95 e57)) (mem g_s91_97 g_s24_24) (mem g_s92_98 g_s24_24) (= g_s92_98 (|-i| g_s91_97 e57)) (mem g_s93_99 g_s24_24) (mem g_s94_100 g_s24_24) (= g_s94_100 (|-i| g_s93_99 e57)) (mem g_s95_101 g_s22_22) (mem g_s96_102 g_s22_22) (mem g_s97_103 g_s22_22) (mem g_s98_104 g_s22_22) (not (= g_s97_103 g_s98_104)) (mem g_s99_105 g_s22_22) (mem g_s100_106 g_s22_22) (mem g_s101_107 g_s22_22) (mem g_s102_108 NATURAL) (= g_s102_108 (|-i| g_s100_106 g_s101_107)) (mem g_s103_109 g_s22_22) (mem g_s104_110 g_s22_22) (mem g_s105_111 g_s22_22) (mem g_s106_112 g_s22_22) (mem g_s107_113 g_s24_24) (mem g_s108_114 g_s24_24) (= g_s108_114 (|-i| g_s107_113 e57)) (= g_s93_99 (|*i| g_s89_95 g_s107_113)) (|<=i| e57 g_s107_113) (|<i| g_s107_113 g_s23_25) (mem g_s109_115 g_s24_24) (mem g_s110_116 g_s24_24) (mem g_s111_117 g_s20_20) (mem g_s112_118 g_s20_20) (mem g_s113_119 g_s20_20) (mem g_s114_120 g_s20_20) (mem g_s115_121 g_s20_20) (mem g_s116_122 g_s20_20) (= g_s116_122 (|-i| g_s115_121 e57)) (mem g_s117_123 g_s20_20) (mem g_s118_124 g_s20_20) (= g_s118_124 (|-i| g_s117_123 e57)) (mem g_s119_125 g_s24_24) (mem g_s120_126 g_s24_24) (mem g_s121_127 g_s20_20)))
(define-fun |def_seext| () Bool (and (mem g_s28_32 (|+->| BOOL g_s24_24)) (mem g_s28_32 (|+->| BOOL g_s22_22)) (mem g_s28_32 (|+->| BOOL g_s20_20))))
(define-fun |def_lprp| () Bool true)
(define-fun |def_inprp| () Bool true)
(define-fun |def_inext| () Bool true)
(define-fun |def_inv| () Bool (and (mem g_s122_128 NATURAL) (mem g_s123_129 NATURAL) (|<=i| g_s123_129 g_s122_128) (mem g_s124_130 BOOL) (subset g_s125_131 (interval e57 g_s122_128)) (subset g_s126_132 (interval e57 g_s122_128)) (subset g_s127_133 (interval e57 g_s122_128)) (subset g_s128_134 (interval e57 g_s122_128)) (subset g_s129_135 (interval e57 g_s122_128))))
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
(assert (not (mem e0 NATURAL)))
(check-sat)
(pop 1)
; PO 2 in group 0
(push 1)
(assert (not (subset empty (interval e57 e0))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 0
(push 1)
(assert (not (|<=i| e0 e0)))
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
(assert (mem g_s133_136 g_s24_24))
(assert (mem g_s134_137 g_s24_24))
(assert (mem g_s135_138 g_s24_24))
(assert (= g_s124_130 (bool (mem g_s122_128 g_s127_133))))
(assert (= g_s125_131 empty))
(define-fun lh_1 () Bool (= g_s133_136 g_s25_26))
(define-fun lh_2 () Bool (= g_s134_137 g_s26_27))
(define-fun lh_3 () Bool (= g_s135_138 g_s25_26))
(define-fun lh_4 () Bool (not (and (= g_s133_136 g_s25_26) (= g_s134_137 g_s26_27))))
; PO 1 in group 1
(push 1)
(assert (not (=> (and lh_3 lh_4) (mem (|+i| g_s122_128 e57) NATURAL))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 1
(push 1)
(assert (not (=> (and lh_3 lh_4) (subset g_s127_133 (interval e57 (|+i| g_s122_128 e57))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 1
(push 1)
(assert (not (=> (and lh_3 lh_4) (subset g_s125_131 (interval e57 (|+i| g_s122_128 e57))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 1
(push 1)
(assert (not (=> (and lh_3 lh_4) (subset g_s126_132 (interval e57 (|+i| g_s122_128 e57))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 5 in group 1
(push 1)
(assert (not (=> (and lh_3 lh_4) (subset g_s128_134 (interval e57 (|+i| g_s122_128 e57))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 6 in group 1
(push 1)
(assert (not (=> (and lh_3 lh_4) (subset (binary_union g_s129_135 (SET (|+i| g_s122_128 e57))) (interval e57 (|+i| g_s122_128 e57))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 7 in group 1
(push 1)
(assert (not (=> (and lh_3 lh_4) (|<=i| g_s123_129 (|+i| g_s122_128 e57)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 8 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (mem (|+i| g_s122_128 e57) NATURAL))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 9 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (subset g_s125_131 (interval e57 (|+i| g_s122_128 e57))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 10 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (subset g_s126_132 (interval e57 (|+i| g_s122_128 e57))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 11 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (subset (binary_union g_s127_133 (SET (|+i| g_s122_128 e57))) (interval e57 (|+i| g_s122_128 e57))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 12 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (subset (binary_union g_s128_134 (SET (|+i| g_s122_128 e57))) (interval e57 (|+i| g_s122_128 e57))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 13 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (subset (binary_union g_s129_135 (SET (|+i| g_s122_128 e57))) (interval e57 (|+i| g_s122_128 e57))))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 14 in group 1
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (|<=i| g_s123_129 (|+i| g_s122_128 e57)))))
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
(assert (mem g_s135_138 g_s24_24))
(assert (mem g_s122_128 g_s127_133))
(assert (mem g_s122_128 g_s128_134))
(assert (= (bool (= g_s135_138 g_s25_26)) (bool (mem g_s122_128 g_s129_135))))
(assert (= g_s123_129 (|-i| g_s122_128 e57)))
(assert (subset g_s126_132 (interval e57 (|-i| g_s122_128 e57))))
(assert (= g_s125_131 empty))
(define-fun lh_1 () Bool (mem g_s126$1_139 (POW (interval e57 g_s122_128))))
; PO 1 in group 2
(push 1)
(assert (not (=> lh_1 (mem (|+i| g_s123_129 e57) NATURAL))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 2
(push 1)
(assert (not (=> lh_1 (subset g_s126$1_139 (interval e57 g_s122_128)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 2
(push 1)
(assert (not (=> lh_1 (|<=i| (|+i| g_s123_129 e57) g_s122_128))))
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
(assert (|<=i| e57 g_s122_128))
(assert (mem g_s123_129 g_s127_133))
(assert (= g_s123_129 (|-i| g_s122_128 e57)))
(assert (= g_s125_131 empty))
(define-fun lh_1 () Bool (mem g_s125$1_140 (POW (binary_union g_s125_131 (SET g_s122_128)))))
; PO 1 in group 3
(assert (not (=> lh_1 (subset g_s125$1_140 (interval e57 g_s122_128)))))
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
(assert (mem g_s135_138 g_s24_24))
(assert (mem g_s135_138 g_s27_31))
(assert (not (mem g_s122_128 g_s127_133)))
(assert (not (mem g_s122_128 g_s128_134)))
(assert (mem (|-i| g_s122_128 e57) g_s127_133))
(assert (|<=i| e57 g_s122_128))
(assert (= (bool (= g_s135_138 g_s25_26)) (bool (mem g_s122_128 g_s129_135))))
(assert (= g_s123_129 (|-i| g_s122_128 e57)))
(assert (subset g_s126_132 (interval e57 (|-i| g_s122_128 e57))))
(assert (= g_s125_131 empty))
(define-fun lh_1 () Bool (mem g_s125$1_140 (POW (binary_union g_s125_131 (SET g_s122_128)))))
; PO 1 in group 4
(push 1)
(assert (not (=> lh_1 (mem (|+i| g_s123_129 e57) NATURAL))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 4
(push 1)
(assert (not (=> lh_1 (subset g_s125$1_140 (interval e57 g_s122_128)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 4
(push 1)
(assert (not (=> lh_1 (|<=i| (|+i| g_s123_129 e57) g_s122_128))))
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
(assert (mem g_s135_138 g_s24_24))
(assert (mem g_s135_138 g_s27_31))
(assert (not (mem g_s122_128 g_s127_133)))
(assert (not (mem g_s122_128 g_s128_134)))
(assert (not (mem (|-i| g_s122_128 e57) g_s127_133)))
(assert (|<=i| e57 g_s122_128))
(assert (= (bool (= g_s135_138 g_s25_26)) (bool (mem g_s122_128 g_s129_135))))
(assert (= g_s123_129 (|-i| g_s122_128 e57)))
(assert (subset g_s126_132 (interval e57 (|-i| g_s122_128 e57))))
(assert (= g_s125_131 empty))
(define-fun lh_1 () Bool (mem g_s125$1_140 (POW (binary_union g_s125_131 (SET g_s122_128)))))
; PO 1 in group 5
(push 1)
(assert (not (=> lh_1 (mem (|+i| g_s123_129 e57) NATURAL))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 5
(push 1)
(assert (not (=> lh_1 (subset g_s125$1_140 (interval e57 g_s122_128)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 5
(push 1)
(assert (not (=> lh_1 (|<=i| (|+i| g_s123_129 e57) g_s122_128))))
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
(assert (|<=i| e57 g_s122_128))
(assert (not (mem g_s123_129 g_s127_133)))
(assert (= g_s123_129 (|-i| g_s122_128 e57)))
(assert (subset g_s125_131 (SET g_s122_128)))
(define-fun lh_1 () Bool (mem g_s125$1_140 (POW (binary_union g_s125_131 (SET g_s122_128)))))
; PO 1 in group 6
(assert (not (=> lh_1 (subset g_s125$1_140 (interval e57 g_s122_128)))))
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
(assert (mem g_s142_141 g_s24_24))
(assert (|>=i| g_s122_128 e57))
; PO 1 in group 7
(push 1)
(assert (not (mem g_s28_32 (|+->| (dom g_s28_32) (ran g_s28_32)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 7
(push 1)
(assert (not (mem (bool (mem g_s122_128 g_s125_131)) (dom g_s28_32))))
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
(assert (mem g_s142_141 g_s24_24))
(assert (|>=i| g_s122_128 e57))
; PO 1 in group 8
(push 1)
(assert (not (mem g_s28_32 (|+->| (dom g_s28_32) (ran g_s28_32)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 8
(push 1)
(assert (not (mem (bool (mem (|-i| g_s122_128 e57) g_s127_133)) (dom g_s28_32))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
(exit)