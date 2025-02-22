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
(declare-fun e20 () U)
(declare-fun e0 () U)
(declare-fun e50 () U)
(declare-fun e33 () U)
(declare-fun e24 () U)
(declare-fun e22 () U)
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
(declare-fun g_s12_13 () U)
(declare-fun g_s120_125 () U)
(declare-fun g_s123_126 () U)
(declare-fun g_s124_127 () U)
(declare-fun g_s125_128 () U)
(declare-fun g_s13_14 () U)
(declare-fun g_s14_15 () U)
(declare-fun g_s15_16 () U)
(declare-fun g_s16_17 () U)
(declare-fun g_s17_18 () U)
(declare-fun g_s18_19 () U)
(declare-fun g_s19_21 () U)
(declare-fun g_s2_3 () U)
(declare-fun g_s20_23 () U)
(declare-fun g_s21_25 () U)
(declare-fun g_s22_26 () U)
(declare-fun g_s23_27 () U)
(declare-fun g_s24_28 () U)
(declare-fun g_s25_29 () U)
(declare-fun g_s26_30 () U)
(declare-fun g_s27_31 () U)
(declare-fun g_s28_32 () U)
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
(declare-fun g_s45_51 () U)
(declare-fun g_s46_52 () U)
(declare-fun g_s47_53 () U)
(declare-fun g_s48_54 () U)
(declare-fun g_s49_55 () U)
(declare-fun g_s5_6 () U)
(declare-fun g_s50_56 () U)
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
(define-fun |def_ctx| () Bool (and (= g_s0_1 (SET (mapplet g_s2_3 g_s1_2))) (= g_s3_4 (SET (mapplet g_s5_6 g_s4_5))) (= g_s6_7 (SET (mapplet g_s8_9 g_s7_8))) (= g_s9_10 (SET (mapplet g_s18_19 (mapplet g_s17_18 (mapplet g_s16_17 (mapplet g_s15_16 (mapplet g_s14_15 (mapplet g_s13_14 (mapplet g_s12_13 (mapplet g_s11_12 g_s10_11)))))))))) (= g_s19_21 (interval e0 e20)) (= g_s20_23 (interval e0 e22)) (= g_s21_25 (interval e0 e24)) (mem g_s22_26 g_s21_25) (mem g_s23_27 g_s21_25) (mem g_s24_28 g_s20_23) (mem g_s25_29 g_s20_23) (mem g_s26_30 g_s19_21) (mem g_s27_31 g_s19_21) (mem g_s28_32 NATURAL) (|<=i| e33 g_s28_32) (mem g_s29_34 NATURAL) (|<=i| e33 g_s29_34) (mem g_s30_35 NATURAL) (|<=i| e33 g_s30_35) (|<=i| g_s28_32 g_s30_35) (mem g_s31_36 g_s21_25) (mem g_s32_37 g_s21_25) (= g_s32_37 (|+i| g_s31_36 g_s28_32)) (mem g_s33_38 g_s21_25) (= g_s33_38 (|+i| g_s31_36 g_s29_34)) (mem g_s34_39 g_s21_25) (= g_s34_39 (|+i| g_s31_36 g_s30_35)) (mem g_s35_40 g_s20_23) (mem g_s36_41 g_s20_23) (mem g_s37_42 g_s21_25) (|<=i| g_s35_40 g_s36_41) (mem g_s38_43 g_s19_21) (mem g_s39_44 g_s19_21) (mem g_s40_45 g_s19_21) (mem g_s41_46 g_s19_21) (mem g_s42_47 g_s19_21) (mem g_s43_48 g_s21_25) (|<=i| e33 g_s43_48) (mem g_s44_49 g_s21_25) (= g_s44_49 (|-i| g_s43_48 e50)) (mem g_s45_51 NATURAL1) (mem g_s46_52 NATURAL1) (mem g_s47_53 NATURAL1) (mem g_s48_54 NATURAL1) (mem g_s49_55 NATURAL1) (mem g_s50_56 NATURAL1) (mem g_s51_57 NATURAL1) (mem g_s52_58 NATURAL1) (mem g_s53_59 g_s21_25) (mem g_s54_60 g_s21_25) (= g_s54_60 (|+i| g_s53_59 g_s45_51)) (mem g_s55_61 g_s21_25) (mem g_s56_62 g_s21_25) (= g_s56_62 (|+i| g_s55_61 g_s46_52)) (mem g_s57_63 g_s21_25) (= g_s57_63 (|+i| g_s55_61 g_s47_53)) (mem g_s58_64 g_s21_25) (= g_s58_64 (|+i| g_s55_61 g_s48_54)) (mem g_s59_65 g_s21_25) (= g_s59_65 (|+i| g_s55_61 g_s49_55)) (mem g_s60_66 g_s21_25) (= g_s60_66 (|+i| g_s55_61 g_s50_56)) (mem g_s61_67 g_s21_25) (= g_s61_67 (|+i| g_s55_61 g_s51_57)) (mem g_s62_68 g_s21_25) (= g_s62_68 (|+i| g_s55_61 g_s52_58)) (mem g_s63_69 g_s19_21) (mem g_s64_70 g_s19_21) (mem g_s65_71 g_s19_21) (mem g_s66_72 g_s19_21) (mem g_s67_73 g_s19_21) (mem g_s68_74 g_s19_21) (mem g_s69_75 g_s19_21) (mem g_s70_76 g_s19_21) (mem g_s71_77 g_s19_21) (mem g_s72_78 g_s19_21) (mem g_s73_79 g_s19_21) (mem g_s74_80 g_s19_21) (mem g_s75_81 g_s19_21) (mem g_s76_82 g_s19_21) (mem g_s77_83 g_s19_21) (mem g_s78_84 g_s19_21) (mem g_s79_85 g_s19_21) (mem g_s80_86 g_s19_21) (mem g_s81_87 g_s19_21) (mem g_s82_88 g_s21_25) (|<=i| e0 g_s82_88) (|<=i| e33 g_s82_88) (mem g_s83_89 g_s21_25) (= g_s83_89 (|-i| g_s82_88 e50)) (mem g_s84_90 g_s21_25) (mem g_s85_91 g_s21_25) (= g_s85_91 (|-i| g_s84_90 e50)) (mem g_s86_92 g_s21_25) (mem g_s87_93 g_s21_25) (= g_s87_93 (|-i| g_s86_92 e50)) (mem g_s88_94 g_s20_23) (mem g_s89_95 g_s20_23) (mem g_s90_96 g_s20_23) (mem g_s91_97 g_s20_23) (not (= g_s90_96 g_s91_97)) (mem g_s92_98 g_s20_23) (mem g_s93_99 g_s20_23) (mem g_s94_100 g_s20_23) (mem g_s95_101 NATURAL) (= g_s95_101 (|-i| g_s93_99 g_s94_100)) (mem g_s96_102 g_s20_23) (mem g_s97_103 g_s20_23) (mem g_s98_104 g_s20_23) (mem g_s99_105 g_s20_23) (mem g_s100_106 g_s21_25) (mem g_s101_107 g_s21_25) (= g_s101_107 (|-i| g_s100_106 e50)) (= g_s86_92 (|*i| g_s82_88 g_s100_106)) (|<=i| e50 g_s100_106) (|<i| g_s100_106 g_s102_108) (mem g_s103_109 g_s21_25) (mem g_s104_110 g_s21_25) (mem g_s105_111 g_s19_21) (mem g_s106_112 g_s19_21) (mem g_s107_113 g_s19_21) (mem g_s108_114 g_s19_21) (mem g_s109_115 g_s19_21) (mem g_s110_116 g_s19_21) (= g_s110_116 (|-i| g_s109_115 e50)) (mem g_s111_117 g_s19_21) (mem g_s112_118 g_s19_21) (= g_s112_118 (|-i| g_s111_117 e50)) (mem g_s113_119 g_s21_25) (mem g_s114_120 g_s21_25) (mem g_s115_121 g_s19_21)))
(define-fun |def_seext| () Bool true)
(define-fun |def_lprp| () Bool (and (mem g_s116_122 (|-->| (set_prod (interval e0 g_s83_89) (interval e0 g_s85_91)) g_s20_23)) (mem g_s117_123 (|-->| (interval e0 g_s83_89) g_s20_23)) (mem g_s118_124 (|-->| g_s20_23 g_s20_23))))
(define-fun |def_inprp| () Bool true)
(define-fun |def_inext| () Bool true)
(define-fun |def_inv| () Bool true)
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
(assert |def_inv|)
(assert |def_ass|)
(assert (mem g_s120_125 g_s20_23))
; PO 1 in group 0
(push 1)
(assert (not (mem g_s118_124 (|+->| (dom g_s118_124) (ran g_s118_124)))))
(check-sat)
(pop 1)
; PO 2 in group 0
(push 1)
(assert (not (mem g_s120_125 (dom g_s118_124))))
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
(assert (mem g_s123_126 g_s21_25))
(assert (and (|>=i| g_s123_126 e0) (|<=i| g_s123_126 g_s83_89)))
(assert (mem g_s124_127 g_s21_25))
(assert (and (|>=i| g_s124_127 e0) (|<=i| g_s124_127 g_s85_91)))
(assert (mem g_s125_128 g_s20_23))
; PO 1 in group 1
(push 1)
(assert (not (mem g_s116_122 (|+->| (dom g_s116_122) (ran g_s116_122)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 1
(push 1)
(assert (not (mem (mapplet g_s123_126 g_s124_127) (dom g_s116_122))))
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
(assert (mem g_s123_126 g_s21_25))
(assert (and (|>=i| g_s123_126 e0) (|<=i| g_s123_126 g_s83_89)))
(assert (mem g_s125_128 g_s20_23))
; PO 1 in group 2
(push 1)
(assert (not (mem g_s117_123 (|+->| (dom g_s117_123) (ran g_s117_123)))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 2
(push 1)
(assert (not (mem g_s123_126 (dom g_s117_123))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
(exit)