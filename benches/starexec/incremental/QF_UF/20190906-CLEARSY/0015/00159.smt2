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
(declare-fun e31 () U)
(declare-fun g_s0_1 () U)
(declare-fun g_s1_2 () U)
(declare-fun g_s10_11 () U)
(declare-fun g_s100_102 () U)
(declare-fun g_s101_103 () U)
(declare-fun g_s102_104 () U)
(declare-fun g_s103_105 () U)
(declare-fun g_s104_106 () U)
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
(declare-fun g_s29_30 () U)
(declare-fun g_s3_4 () U)
(declare-fun g_s30_32 () U)
(declare-fun g_s31_33 () U)
(declare-fun g_s32_34 () U)
(declare-fun g_s33_35 () U)
(declare-fun g_s34_36 () U)
(declare-fun g_s35_37 () U)
(declare-fun g_s36_38 () U)
(declare-fun g_s37_39 () U)
(declare-fun g_s38_40 () U)
(declare-fun g_s39_41 () U)
(declare-fun g_s4_5 () U)
(declare-fun g_s40_42 () U)
(declare-fun g_s41_43 () U)
(declare-fun g_s42_44 () U)
(declare-fun g_s43_45 () U)
(declare-fun g_s44_46 () U)
(declare-fun g_s45_47 () U)
(declare-fun g_s46_48 () U)
(declare-fun g_s47_49 () U)
(declare-fun g_s48_50 () U)
(declare-fun g_s49_51 () U)
(declare-fun g_s5_6 () U)
(declare-fun g_s50_52 () U)
(declare-fun g_s51_53 () U)
(declare-fun g_s52_54 () U)
(declare-fun g_s53_55 () U)
(declare-fun g_s54_56 () U)
(declare-fun g_s55_57 () U)
(declare-fun g_s56_58 () U)
(declare-fun g_s57_59 () U)
(declare-fun g_s58_60 () U)
(declare-fun g_s59_61 () U)
(declare-fun g_s6_7 () U)
(declare-fun g_s60_62 () U)
(declare-fun g_s61_63 () U)
(declare-fun g_s62_64 () U)
(declare-fun g_s63_65 () U)
(declare-fun g_s64_66 () U)
(declare-fun g_s65_67 () U)
(declare-fun g_s66_68 () U)
(declare-fun g_s67_69 () U)
(declare-fun g_s68_70 () U)
(declare-fun g_s69_71 () U)
(declare-fun g_s7_8 () U)
(declare-fun g_s70_72 () U)
(declare-fun g_s71_73 () U)
(declare-fun g_s72_74 () U)
(declare-fun g_s73_75 () U)
(declare-fun g_s74_76 () U)
(declare-fun g_s75_77 () U)
(declare-fun g_s76_78 () U)
(declare-fun g_s77_79 () U)
(declare-fun g_s78_80 () U)
(declare-fun g_s79_81 () U)
(declare-fun g_s8_9 () U)
(declare-fun g_s80_82 () U)
(declare-fun g_s81_83 () U)
(declare-fun g_s82_84 () U)
(declare-fun g_s83_85 () U)
(declare-fun g_s84_86 () U)
(declare-fun g_s85_87 () U)
(declare-fun g_s86_88 () U)
(declare-fun g_s87_89 () U)
(declare-fun g_s88_90 () U)
(declare-fun g_s89_91 () U)
(declare-fun g_s9_10 () U)
(declare-fun g_s90_92 () U)
(declare-fun g_s91_93 () U)
(declare-fun g_s92_94 () U)
(declare-fun g_s93_95 () U)
(declare-fun g_s94_96 () U)
(declare-fun g_s95_97 () U)
(declare-fun g_s96_98 () U)
(declare-fun g_s97_99 () U)
(declare-fun g_s98_100 () U)
(declare-fun g_s99_101 () U)
(declare-fun e29 () U)
(declare-fun e28 () U)
; Defines
(define-fun |def_B definitions| () Bool (and (= NAT (interval e0 MaxInt)) (= INT (interval MinInt MaxInt))))
(define-fun |def_ctx| () Bool (and (not (= g_s0_1 empty)) (not (= g_s1_2 empty)) (not (= g_s2_3 empty)) (not (= g_s3_4 empty)) (not (= g_s4_5 empty)) (not (= g_s5_6 empty)) (not (= g_s6_7 empty)) (not (= g_s7_8 empty)) (not (= g_s8_9 empty)) (not (= g_s9_10 empty)) (not (= g_s10_11 empty)) (not (= g_s11_12 empty)) (not (= g_s12_13 empty)) (not (= g_s13_14 empty)) (not (= g_s14_15 empty)) (not (= g_s15_16 empty)) (not (= g_s16_17 empty)) (not (= g_s17_18 empty)) (not (= g_s18_19 empty)) (not (= g_s19_20 empty)) (not (= g_s20_21 empty)) (not (= g_s21_22 empty)) (not (= g_s22_23 empty)) (not (= g_s23_24 empty)) (not (= g_s24_25 empty)) (not (= g_s25_26 empty)) (mem g_s26_27 (|-->| (set_prod INTEGER NATURAL) INTEGER)) (= g_s26_27 (binary_union e29 e28)) (mem g_s29_30 (|-->| BOOL NAT)) (= g_s29_30 (SET (mapplet (mapplet FALSE e0) (mapplet TRUE e31)))) (= g_s30_32 INT) (= g_s31_33 NAT) (= g_s32_34 NAT1) (subset g_s32_34 g_s31_33) (subset g_s31_33 g_s30_32) (mem g_s33_35 g_s30_32) (mem g_s33_35 g_s31_33) (not (mem g_s33_35 g_s32_34)) (mem g_s34_36 g_s30_32) (not (mem g_s34_36 g_s31_33)) (= g_s35_37 INT) (subset g_s36_38 g_s8_9) (mem g_s37_39 g_s8_9) (mem g_s37_39 g_s36_38) (mem g_s38_40 g_s8_9) (not (mem g_s38_40 g_s36_38)) (mem g_s39_41 (|+->| NAT g_s8_9)) (mem g_s39_41 (perm g_s36_38)) (= (card g_s36_38) g_s40_42) (subset g_s41_43 g_s9_10) (mem g_s42_44 g_s9_10) (mem g_s42_44 g_s41_43) (mem g_s43_45 g_s9_10) (not (mem g_s43_45 g_s41_43)) (mem g_s44_46 (|+->| NAT g_s9_10)) (mem g_s44_46 (perm g_s41_43)) (= (card g_s41_43) g_s45_47) (subset g_s46_48 g_s10_11) (mem g_s47_49 g_s10_11) (not (mem g_s47_49 g_s46_48)) (mem g_s48_50 (|+->| NAT g_s10_11)) (mem g_s48_50 (perm g_s46_48)) (subset g_s49_51 g_s11_12) (mem g_s50_52 g_s11_12) (not (mem g_s50_52 g_s49_51)) (mem g_s51_53 (|+->| NAT g_s11_12)) (mem g_s51_53 (perm g_s49_51)) (subset g_s52_54 g_s12_13) (mem g_s53_55 g_s12_13) (not (mem g_s53_55 g_s52_54)) (mem g_s54_56 (|+->| NAT g_s12_13)) (mem g_s54_56 (perm g_s52_54)) (subset g_s55_57 g_s13_14) (mem g_s56_58 g_s13_14) (not (mem g_s56_58 g_s55_57)) (mem g_s57_59 (|+->| NAT g_s13_14)) (mem g_s57_59 (perm g_s55_57)) (subset g_s58_60 g_s14_15) (mem g_s59_61 g_s14_15) (not (mem g_s59_61 g_s58_60)) (mem g_s60_62 (|+->| NAT g_s14_15)) (mem g_s60_62 (perm g_s58_60)) (subset g_s61_63 g_s15_16) (mem g_s62_64 g_s15_16) (not (mem g_s62_64 g_s61_63)) (mem g_s63_65 (|+->| NAT g_s15_16)) (mem g_s63_65 (perm g_s61_63)) (subset g_s64_66 g_s16_17) (mem g_s65_67 g_s16_17) (not (mem g_s65_67 g_s64_66)) (mem g_s66_68 (|+->| NAT g_s16_17)) (mem g_s66_68 (perm g_s64_66)) (subset g_s67_69 g_s17_18) (mem g_s68_70 g_s17_18) (not (mem g_s68_70 g_s67_69)) (mem g_s69_71 (|+->| NAT g_s17_18)) (mem g_s69_71 (perm g_s67_69)) (mem g_s70_72 g_s18_19) (mem g_s71_73 (|-->| g_s18_19 g_s11_12)) (= (apply g_s71_73 g_s70_72) g_s50_52) (subset g_s72_74 g_s19_20) (mem g_s73_75 g_s19_20) (not (mem g_s73_75 g_s72_74)) (subset g_s74_76 g_s20_21) (mem g_s75_77 g_s20_21) (not (mem g_s75_77 g_s74_76)) (mem g_s76_78 (|+->| NAT g_s20_21)) (mem g_s76_78 (perm g_s74_76)) (subset g_s77_79 g_s21_22) (mem g_s78_80 g_s21_22) (not (mem g_s78_80 g_s77_79)) (mem g_s79_81 (|+->| NAT g_s21_22)) (mem g_s79_81 (perm g_s77_79)) (subset g_s80_82 g_s22_23) (mem g_s81_83 g_s22_23) (not (mem g_s81_83 g_s80_82)) (mem g_s82_84 (|+->| NAT g_s22_23)) (mem g_s82_84 (perm g_s80_82)) (subset g_s83_85 g_s23_24) (mem g_s84_86 g_s23_24) (not (mem g_s84_86 g_s83_85)) (mem g_s85_87 (|+->| NAT g_s23_24)) (mem g_s85_87 (perm g_s83_85)) (subset g_s86_88 g_s24_25) (mem g_s87_89 g_s24_25) (not (mem g_s87_89 g_s86_88)) (mem g_s88_90 (|+->| NAT g_s24_25)) (mem g_s88_90 (perm g_s86_88)) (mem g_s89_91 (|>->| g_s74_76 g_s41_43)) (mem g_s90_92 (|>->| g_s77_79 g_s41_43)) (mem g_s91_93 g_s9_10) (=> (not (= g_s92_94 e0)) (mem g_s91_93 g_s41_43)) (mem g_s93_95 (|>->| g_s83_85 g_s41_43)) (= (binary_inter (ran g_s89_91) (ran g_s90_92)) empty) (= (binary_inter (ran g_s89_91) (ran g_s93_95)) empty) (= (binary_inter (ran g_s93_95) (ran g_s90_92)) empty) (=> (not (= g_s92_94 e0)) (not (mem g_s91_93 (ran g_s89_91)))) (=> (not (= g_s92_94 e0)) (not (mem g_s91_93 (ran g_s90_92)))) (=> (not (= g_s92_94 e0)) (not (mem g_s91_93 (ran g_s93_95)))) (subset g_s94_96 g_s25_26) (mem g_s95_97 g_s25_26) (not (mem g_s95_97 g_s94_96)) (mem g_s96_98 (|+->| NAT g_s25_26)) (mem g_s96_98 (perm g_s94_96))))
(define-fun |def_seext| () Bool true)
(define-fun |def_lprp| () Bool true)
(define-fun |def_inprp| () Bool true)
(define-fun |def_inext| () Bool true)
(define-fun |def_inv| () Bool (and (mem g_s97_99 (|-->| g_s23_24 g_s12_13)) (mem g_s98_100 (|-->| g_s23_24 g_s10_11)) (mem g_s99_101 (|-->| g_s23_24 NAT)) (mem g_s100_102 (|-->| (set_prod g_s23_24 g_s25_26) g_s14_15)) (mem g_s101_103 (|-->| (set_prod g_s23_24 g_s25_26) BOOL)) (mem g_s102_104 (|-->| g_s23_24 g_s30_32)) (mem g_s103_105 (|-->| g_s23_24 g_s30_32)) (mem g_s104_106 (|-->| g_s23_24 BOOL))))
(define-fun |def_ass| () Bool true)
(define-fun |def_cst| () Bool true)
(define-fun |def_sets| () Bool true)
; PO group 0 
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_cst|)
(assert |def_lprp|)
(assert |def_inprp|)
(assert |def_inext|)
(assert |def_seext|)
; PO 1 in group 0
(push 1)
(assert (not (mem (set_prod g_s23_24 (SET FALSE)) (|-->| g_s23_24 BOOL))))
(check-sat)
(pop 1)
; PO 2 in group 0
(push 1)
(assert (not (mem (set_prod g_s23_24 (SET e0)) (|-->| g_s23_24 NAT))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 3 in group 0
(push 1)
(assert (not (mem (set_prod g_s23_24 (SET e0)) (|-->| g_s23_24 g_s30_32))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 4 in group 0
(push 1)
(assert (not (mem (set_prod g_s23_24 (SET g_s53_55)) (|-->| g_s23_24 g_s12_13))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 5 in group 0
(push 1)
(assert (not (mem (set_prod g_s23_24 (SET g_s47_49)) (|-->| g_s23_24 g_s10_11))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 6 in group 0
(push 1)
(assert (not (mem (set_prod (set_prod g_s23_24 g_s25_26) (SET FALSE)) (|-->| (set_prod g_s23_24 g_s25_26) BOOL))))
(set-info :status unknown)
(check-sat)
(pop 1)
; PO 7 in group 0
(push 1)
(assert (not (mem (set_prod (set_prod g_s23_24 g_s25_26) (SET g_s59_61)) (|-->| (set_prod g_s23_24 g_s25_26) g_s14_15))))
(set-info :status unknown)
(check-sat)
(pop 1)
(exit)