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
(declare-fun g_s113$1_122 () U)
(declare-fun g_s114_115 () U)
(declare-fun g_s114$1_123 () U)
(declare-fun g_s115_116 () U)
(declare-fun g_s116_117 () U)
(declare-fun g_s117_118 () U)
(declare-fun g_s118_119 () U)
(declare-fun g_s119_120 () U)
(declare-fun g_s12_13 () U)
(declare-fun g_s120_121 () U)
(declare-fun g_s125_124 () U)
(declare-fun g_s128_127 () U)
(declare-fun g_s128_125 () U)
(declare-fun g_s128_126 () U)
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
; Defines
(define-fun |def_B definitions| () Bool (and (= NAT (interval e0 MaxInt)) (= INT (interval MinInt MaxInt))))
(define-fun |def_ctx| () Bool (and (not (= g_s0_1 empty)) (not (= g_s1_2 empty)) (not (= g_s2_3 empty)) (not (= g_s3_4 empty)) (not (= g_s4_5 empty)) (not (= g_s5_6 empty)) (not (= g_s6_7 empty)) (not (= g_s7_8 empty)) (not (= g_s8_9 empty)) (not (= g_s9_10 empty)) (not (= g_s10_11 empty)) (= g_s11_12 (SET (mapplet g_s13_14 g_s12_13))) (not (= g_s14_15 empty)) (not (= g_s15_16 empty)) (not (= g_s16_17 empty)) (not (= g_s17_18 empty)) (not (= g_s18_19 empty)) (not (= g_s19_20 empty)) (not (= g_s20_21 empty)) (not (= g_s21_22 empty)) (not (= g_s22_23 empty)) (not (= g_s23_24 empty)) (not (= g_s24_25 empty)) (not (= g_s25_26 empty)) (not (= g_s26_27 empty)) (not (= g_s27_28 empty)) (not (= g_s28_29 empty)) (subset g_s29_30 g_s0_1) (mem g_s30_31 g_s0_1) (not (mem g_s30_31 g_s29_30)) (mem g_s31_32 (|+->| NAT g_s0_1)) (mem g_s31_32 (perm g_s29_30)) (subset g_s32_33 g_s1_2) (mem g_s33_34 g_s1_2) (not (mem g_s33_34 g_s32_33)) (mem g_s34_35 (|+->| NAT g_s1_2)) (mem g_s34_35 (perm g_s32_33)) (subset g_s35_36 g_s2_3) (mem g_s36_37 g_s2_3) (not (mem g_s36_37 g_s35_36)) (mem g_s37_38 (|+->| NAT g_s2_3)) (mem g_s37_38 (perm g_s35_36)) (subset g_s38_39 g_s3_4) (mem g_s39_40 g_s3_4) (not (mem g_s39_40 g_s38_39)) (mem g_s40_41 (|+->| NAT g_s3_4)) (mem g_s40_41 (perm g_s38_39)) (subset g_s41_42 g_s4_5) (mem g_s42_43 g_s4_5) (not (mem g_s42_43 g_s41_42)) (mem g_s43_44 (|+->| NAT g_s4_5)) (mem g_s43_44 (perm g_s41_42)) (subset g_s44_45 g_s5_6) (mem g_s45_46 g_s5_6) (not (mem g_s45_46 g_s44_45)) (mem g_s46_47 (|+->| NAT g_s5_6)) (mem g_s46_47 (perm g_s44_45)) (subset g_s47_48 g_s6_7) (mem g_s48_49 g_s6_7) (not (mem g_s48_49 g_s47_48)) (mem g_s49_50 (|+->| NAT g_s6_7)) (mem g_s49_50 (perm g_s47_48)) (= (card g_s47_48) g_s50_51) (subset g_s51_52 g_s7_8) (mem g_s52_53 g_s7_8) (not (mem g_s52_53 g_s51_52)) (mem g_s53_54 (|+->| NAT g_s7_8)) (mem g_s53_54 (perm g_s51_52)) (subset g_s54_55 g_s8_9) (mem g_s55_56 g_s8_9) (not (mem g_s55_56 g_s54_55)) (mem g_s56_57 (|+->| NAT g_s8_9)) (mem g_s56_57 (perm g_s54_55)) (= (card g_s54_55) g_s57_58) (subset g_s58_59 g_s9_10) (mem g_s59_60 g_s9_10) (not (mem g_s59_60 g_s58_59)) (mem g_s60_61 (|+->| NAT g_s9_10)) (mem g_s60_61 (perm g_s58_59)) (subset g_s61_62 g_s10_11) (mem g_s62_63 g_s10_11) (not (mem g_s62_63 g_s61_62)) (mem g_s63_64 (|+->| NAT g_s10_11)) (mem g_s63_64 (perm g_s61_62)) (subset g_s64_65 g_s14_15) (mem g_s65_66 g_s14_15) (not (mem g_s65_66 g_s64_65)) (mem g_s66_67 (|+->| NAT g_s14_15)) (mem g_s66_67 (perm g_s64_65)) (subset g_s67_68 g_s15_16) (mem g_s68_69 g_s15_16) (not (mem g_s68_69 g_s67_68)) (mem g_s69_70 (|+->| NAT g_s15_16)) (mem g_s69_70 (perm g_s67_68)) (subset g_s70_71 g_s16_17) (mem g_s71_72 g_s16_17) (not (mem g_s71_72 g_s70_71)) (mem g_s72_73 (|+->| NAT g_s16_17)) (mem g_s72_73 (perm g_s70_71)) (subset g_s73_74 g_s17_18) (mem g_s74_75 g_s17_18) (not (mem g_s74_75 g_s73_74)) (mem g_s75_76 (|+->| NAT g_s17_18)) (mem g_s75_76 (perm g_s73_74)) (subset g_s76_77 g_s18_19) (mem g_s77_78 g_s18_19) (not (mem g_s77_78 g_s76_77)) (mem g_s78_79 (|+->| NAT g_s18_19)) (mem g_s78_79 (perm g_s76_77)) (subset g_s79_80 g_s19_20) (mem g_s80_81 g_s19_20) (not (mem g_s80_81 g_s79_80)) (mem g_s81_82 (|+->| NAT g_s19_20)) (mem g_s81_82 (perm g_s79_80)) (subset g_s82_83 g_s20_21) (mem g_s83_84 g_s20_21) (not (mem g_s83_84 g_s82_83)) (mem g_s84_85 (|+->| NAT g_s20_21)) (mem g_s84_85 (perm g_s82_83)) (subset g_s85_86 g_s21_22) (mem g_s86_87 g_s21_22) (not (mem g_s86_87 g_s85_86)) (mem g_s87_88 (|+->| NAT g_s21_22)) (mem g_s87_88 (perm g_s85_86)) (subset g_s88_89 g_s22_23) (mem g_s89_90 g_s22_23) (not (mem g_s89_90 g_s88_89)) (mem g_s90_91 (|+->| NAT g_s22_23)) (mem g_s90_91 (perm g_s88_89)) (subset g_s91_92 g_s23_24) (mem g_s92_93 g_s23_24) (not (mem g_s92_93 g_s91_92)) (mem g_s93_94 (|+->| NAT g_s23_24)) (mem g_s93_94 (perm g_s91_92)) (subset g_s94_95 g_s24_25) (mem g_s95_96 g_s24_25) (not (mem g_s95_96 g_s94_95)) (subset g_s96_97 g_s25_26) (mem g_s97_98 g_s25_26) (not (mem g_s97_98 g_s96_97)) (mem g_s98_99 (|+->| NAT g_s25_26)) (mem g_s98_99 (perm g_s96_97)) (subset g_s99_100 g_s26_27) (mem g_s100_101 g_s26_27) (not (mem g_s100_101 g_s99_100)) (mem g_s101_102 (|+->| NAT g_s26_27)) (mem g_s101_102 (perm g_s99_100)) (subset g_s102_103 g_s27_28) (mem g_s103_104 g_s27_28) (not (mem g_s103_104 g_s102_103)) (mem g_s104_105 (|+->| NAT g_s27_28)) (mem g_s104_105 (perm g_s102_103)) (= (card g_s102_103) g_s105_106) (subset g_s106_107 g_s28_29) (mem g_s107_108 g_s28_29) (not (mem g_s107_108 g_s106_107)) (mem g_s108_109 g_s28_29) (mem g_s108_109 g_s106_107) (mem g_s109_110 g_s28_29) (mem g_s109_110 g_s106_107) (mem g_s110_111 g_s28_29) (mem g_s110_111 g_s106_107) (mem g_s111_112 g_s28_29) (mem g_s111_112 g_s106_107) (mem g_s112_113 (|+->| NAT g_s28_29)) (mem g_s112_113 (perm g_s106_107))))
(define-fun |def_seext| () Bool true)
(define-fun |def_lprp| () Bool true)
(define-fun |def_inprp| () Bool true)
(define-fun |def_inext| () Bool true)
(define-fun |def_inv| () Bool (and (subset g_s113_114 g_s32_33) (subset g_s114_115 g_s32_33) (= (binary_inter g_s114_115 g_s113_114) empty) (subset g_s115_116 g_s47_48) (subset g_s116_117 g_s47_48) (= (binary_inter g_s115_116 g_s116_117) empty) (subset g_s117_118 g_s54_55) (subset g_s118_119 g_s54_55) (= (binary_inter g_s117_118 g_s118_119) empty) (subset g_s119_120 g_s102_103) (subset g_s120_121 g_s102_103) (= (binary_inter g_s119_120 g_s120_121) empty)))
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
(define-fun lh_1 () Bool (subset g_s113$1_122 g_s32_33))
(define-fun lh_2 () Bool (subset g_s114$1_123 g_s32_33))
(define-fun lh_3 () Bool (= (binary_inter g_s114$1_123 g_s113$1_122) empty))
; PO 1 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (subset empty g_s102_103))))
(check-sat)
(pop 1)
; PO 2 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (subset empty g_s47_48))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (subset empty g_s54_55))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (= (binary_inter empty empty) empty))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 5 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (= (binary_inter empty empty) empty))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 6 in group 0
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (= (binary_inter empty empty) empty))))
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
; PO 1 in group 1
(push 1)
(assert (not (subset empty g_s32_33)))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 1
(push 1)
(assert (not (subset g_s32_33 g_s32_33)))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 1
(push 1)
(assert (not (= (binary_inter empty g_s32_33) empty)))
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
(assert (not (= g_s113_114 empty)))
(define-fun lh_1 () Bool (mem g_s125_124 g_s1_2))
(define-fun lh_2 () Bool (mem g_s125_124 g_s32_33))
(define-fun lh_3 () Bool (mem g_s125_124 g_s113_114))
; PO 1 in group 2
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (subset (set_diff g_s113_114 (SET g_s125_124)) g_s32_33))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 2
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (subset (binary_union g_s114_115 (SET g_s125_124)) g_s32_33))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 2
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (= (binary_inter (binary_union g_s114_115 (SET g_s125_124)) (set_diff g_s113_114 (SET g_s125_124))) empty))))
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
; PO 1 in group 3
(push 1)
(assert (not (subset empty g_s47_48)))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 3
(push 1)
(assert (not (subset g_s47_48 g_s47_48)))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 3
(push 1)
(assert (not (= (binary_inter g_s47_48 empty) empty)))
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
(assert (not (= g_s115_116 empty)))
(define-fun lh_1 () Bool (mem g_s128_125 g_s6_7))
(define-fun lh_2 () Bool (mem g_s128_125 g_s47_48))
(define-fun lh_3 () Bool (mem g_s128_125 g_s115_116))
; PO 1 in group 4
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (subset (set_diff g_s115_116 (SET g_s128_125)) g_s47_48))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 4
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (subset (binary_union g_s116_117 (SET g_s128_125)) g_s47_48))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 4
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (= (binary_inter (set_diff g_s115_116 (SET g_s128_125)) (binary_union g_s116_117 (SET g_s128_125))) empty))))
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
; PO 1 in group 5
(push 1)
(assert (not (subset empty g_s54_55)))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 5
(push 1)
(assert (not (subset g_s54_55 g_s54_55)))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 5
(push 1)
(assert (not (= (binary_inter g_s54_55 empty) empty)))
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
(assert (not (= g_s117_118 empty)))
(define-fun lh_1 () Bool (mem g_s128_126 g_s8_9))
(define-fun lh_2 () Bool (mem g_s128_126 g_s54_55))
(define-fun lh_3 () Bool (mem g_s128_126 g_s117_118))
; PO 1 in group 6
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (subset (set_diff g_s117_118 (SET g_s128_126)) g_s54_55))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 6
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (subset (binary_union g_s118_119 (SET g_s128_126)) g_s54_55))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 6
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (= (binary_inter (set_diff g_s117_118 (SET g_s128_126)) (binary_union g_s118_119 (SET g_s128_126))) empty))))
(set-info :status unknown)
(check-sat)
(pop 1)
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
; PO 1 in group 7
(push 1)
(assert (not (subset empty g_s102_103)))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 7
(push 1)
(assert (not (subset g_s102_103 g_s102_103)))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 7
(push 1)
(assert (not (= (binary_inter g_s102_103 empty) empty)))
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
(assert (not (= g_s119_120 empty)))
(define-fun lh_1 () Bool (mem g_s128_127 g_s27_28))
(define-fun lh_2 () Bool (mem g_s128_127 g_s102_103))
(define-fun lh_3 () Bool (mem g_s128_127 g_s119_120))
; PO 1 in group 8
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (subset (set_diff g_s119_120 (SET g_s128_127)) g_s102_103))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 2 in group 8
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (subset (binary_union g_s120_121 (SET g_s128_127)) g_s102_103))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 8
(push 1)
(assert (not (=> (and lh_1 lh_2 lh_3) (= (binary_inter (set_diff g_s119_120 (SET g_s128_127)) (binary_union g_s120_121 (SET g_s128_127))) empty))))
(set-info :status unknown)
(check-sat)
(pop 1)
(pop 1)
(exit)