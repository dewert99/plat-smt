(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(set-info :source |
Generated by: Aman Goel (amangoel@umich.edu), Karem A. Sakallah (karem@umich.edu)
Generated on: 2018-04-06

Generated by the tool Averroes 2 (successor of [1]) which implements safety property
verification on hardware systems.

This SMT problem belongs to a set of SMT problems generated by applying Averroes 2
to benchmarks derived from [2-5].

A total of 412 systems (345 from [2], 19 from [3], 26 from [4], 22 from [5]) were
syntactically converted from their original formats (using [6, 7]), and given to 
Averroes 2 to perform property checking with abstraction (wide bit-vectors -> terms, 
wide operators -> UF) using SMT solvers [8, 9].

[1] Lee S., Sakallah K.A. (2014) Unbounded Scalable Verification Based on Approximate
Property-Directed Reachability and Datapath Abstraction. In: Biere A., Bloem R. (eds)
Computer Aided Verification. CAV 2014. Lecture Notes in Computer Science, vol 8559.
Springer, Cham
[2] http://fmv.jku.at/aiger/index.html#beem
[3] http://www.cs.cmu.edu/~modelcheck/vcegar
[4] http://www.cprover.org/hardware/v2c
[5] http://github.com/aman-goel/verilogbench
[6] http://www.clifford.at/yosys
[7] http://github.com/chengyinwu/V3
[8] http://github.com/Z3Prover/z3
[9] http://github.com/SRI-CSL/yices2

id: dyn_partition
query-maker: "Z3"
query-time: 3.012000 ms
query-class: abstract
query-category: assume
query-type: mus_core
status: unsat
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")

; 
(set-info :status sat)
(declare-sort utt3 0)
(declare-sort utt32 0)
(declare-sort utt29 0)
(declare-fun z$n6s3 () utt3)
(declare-fun z$n2s3 () utt3)
(declare-fun z$n1s3 () utt3)
(declare-fun z$n3s3 () utt3)
(declare-fun z$n7s3 () utt3)
(declare-fun z$n5s3 () utt3)
(declare-fun z$n4s3 () utt3)
(declare-fun z$n0s3 () utt3)
(declare-fun z$n0s32 () utt32)
(declare-fun z$n6s32 () utt32)
(declare-fun z$n4s32 () utt32)
(declare-fun z$n8s32 () utt32)
(declare-fun z$n3s32 () utt32)
(declare-fun z$n7s32 () utt32)
(declare-fun z$n2s32 () utt32)
(declare-fun z$n5s32 () utt32)
(declare-fun z$n1s32 () utt32)
(declare-fun x () utt3)
(declare-fun y () utt3)
(declare-fun Concat_32_3_29 (utt3 utt29) utt32)
(declare-fun z$n0s29 () utt29)
(declare-fun z$13 () utt32)
(declare-fun Add_32_32_32 (utt32 utt32) utt32)
(declare-fun z$16 () utt32)
(declare-fun z$24 () utt32)
(declare-fun z$26 () utt32)
(declare-fun Extract_3_2_0_32 (utt32) utt3)
(declare-fun z$18 () utt3)
(declare-fun z$20 () utt3)
(declare-fun x$next () utt3)
(declare-fun z$28 () utt3)
(declare-fun z$30 () utt3)
(declare-fun y$next () utt3)
(declare-fun z$103 () utt32)
(declare-fun z$106 () utt32)
(declare-fun z$97 () utt32)
(declare-fun z$100 () utt32)
(declare-fun b0 () Bool)
(declare-fun z$1 () Bool)
(declare-fun b1 () Bool)
(declare-fun z$3 () Bool)
(declare-fun z$6 () Bool)
(declare-fun z$8 () Bool)
(declare-fun z$9 () Bool)
(declare-fun z$188 () Bool)
(declare-fun z$313 () Bool)
(declare-fun z$510 () Bool)
(declare-fun z$511 () Bool)
(declare-fun z$330 () Bool)
(declare-fun z$591 () Bool)
(declare-fun z$593 () Bool)
(declare-fun z$833 () Bool)
(declare-fun z$946 () Bool)
(declare-fun z$949 () Bool)
(declare-fun z$950 () Bool)
(declare-fun z$87 () Bool)
(declare-fun z$806 () Bool)
(declare-fun z$1014 () Bool)
(declare-fun z$1015 () Bool)
(declare-fun z$128 () Bool)
(declare-fun z$688 () Bool)
(declare-fun z$689 () Bool)
(declare-fun z$130 () Bool)
(declare-fun z$677 () Bool)
(declare-fun z$678 () Bool)
(declare-fun z$1177 () Bool)
(declare-fun z$1235 () Bool)
(declare-fun z$1236 () Bool)
(declare-fun z$86 () Bool)
(declare-fun z$92 () Bool)
(declare-fun z$1158 () Bool)
(declare-fun z$1248 () Bool)
(declare-fun z$1249 () Bool)
(declare-fun z$1259 () Bool)
(declare-fun z$1260 () Bool)
(declare-fun z$1179 () Bool)
(declare-fun z$1270 () Bool)
(declare-fun z$1271 () Bool)
(declare-fun z$1226 () Bool)
(declare-fun z$1227 () Bool)
(declare-fun z$93 () Bool)
(declare-fun z$1085 () Bool)
(declare-fun z$1086 () Bool)
(declare-fun z$1378 () Bool)
(declare-fun z$1381 () Bool)
(declare-fun z$1382 () Bool)
(declare-fun z$1390 () Bool)
(declare-fun z$1393 () Bool)
(declare-fun z$1394 () Bool)
(declare-fun z$1408 () Bool)
(declare-fun z$1411 () Bool)
(declare-fun z$1412 () Bool)
(declare-fun LeEq_1_3_3 (utt3 utt3) Bool)
(declare-fun z$39 () Bool)
(declare-fun prop () Bool)
(declare-fun z$41 () Bool)
(declare-fun z$11 () Bool)
(declare-fun z$22 () Bool)
(declare-fun z$32 () Bool)
(declare-fun b0$next () Bool)
(declare-fun z$34 () Bool)
(declare-fun b1$next () Bool)
(declare-fun z$36 () Bool)
(declare-fun z$50 () Bool)
(declare-fun prop$next () Bool)
(declare-fun z$52 () Bool)
(declare-fun z$59 () Bool)
(declare-fun z$60 () Bool)
(declare-fun z$61 () Bool)
(declare-fun z$63 () Bool)
(declare-fun z$54 () Bool)
(declare-fun z$58 () Bool)
(declare-fun z$62 () Bool)
(declare-fun z$142 () Bool)
(declare-fun z$143 () Bool)
(declare-fun z$131 () Bool)
(declare-fun z$171 () Bool)
(declare-fun z$172 () Bool)
(declare-fun z$132 () Bool)
(declare-fun z$90 () Bool)
(declare-fun z$233 () Bool)
(declare-fun z$234 () Bool)
(declare-fun z$96 () Bool)
(declare-fun z$114 () Bool)
(declare-fun z$109 () Bool)
(declare-fun z$281 () Bool)
(declare-fun z$282 () Bool)
(declare-fun z$91 () Bool)
(declare-fun z$308 () Bool)
(declare-fun z$310 () Bool)
(declare-fun z$192 () Bool)
(declare-fun z$309 () Bool)
(declare-fun z$317 () Bool)
(declare-fun z$342 () Bool)
(declare-fun z$358 () Bool)
(declare-fun z$359 () Bool)
(declare-fun z$285 () Bool)
(declare-fun z$344 () Bool)
(declare-fun z$384 () Bool)
(declare-fun z$386 () Bool)
(declare-fun z$383 () Bool)
(declare-fun z$385 () Bool)
(declare-fun z$402 () Bool)
(declare-fun z$403 () Bool)
(declare-fun z$418 () Bool)
(declare-fun z$419 () Bool)
(declare-fun z$435 () Bool)
(declare-fun z$436 () Bool)
(declare-fun z$348 () Bool)
(declare-fun z$110 () Bool)
(declare-fun z$450 () Bool)
(declare-fun z$451 () Bool)
(declare-fun z$99 () Bool)
(declare-fun z$480 () Bool)
(declare-fun z$481 () Bool)
(declare-fun z$343 () Bool)
(declare-fun z$112 () Bool)
(declare-fun z$542 () Bool)
(declare-fun z$543 () Bool)
(declare-fun z$564 () Bool)
(declare-fun z$566 () Bool)
(declare-fun z$85 () Bool)
(declare-fun z$565 () Bool)
(declare-fun z$568 () Bool)
(declare-fun z$581 () Bool)
(declare-fun z$582 () Bool)
(declare-fun z$547 () Bool)
(declare-fun z$605 () Bool)
(declare-fun z$606 () Bool)
(declare-fun z$621 () Bool)
(declare-fun z$622 () Bool)
(declare-fun z$129 () Bool)
(declare-fun z$700 () Bool)
(declare-fun z$701 () Bool)
(declare-fun z$720 () Bool)
(declare-fun z$721 () Bool)
(declare-fun z$735 () Bool)
(declare-fun z$736 () Bool)
(declare-fun z$750 () Bool)
(declare-fun z$751 () Bool)
(declare-fun z$829 () Bool)
(declare-fun z$830 () Bool)
(declare-fun z$842 () Bool)
(declare-fun z$248 () Bool)
(declare-fun z$862 () Bool)
(declare-fun z$864 () Bool)
(declare-fun z$238 () Bool)
(declare-fun z$861 () Bool)
(declare-fun z$863 () Bool)
(declare-fun z$892 () Bool)
(declare-fun z$894 () Bool)
(declare-fun z$133 () Bool)
(declare-fun z$893 () Bool)
(declare-fun z$896 () Bool)
(declare-fun z$105 () Bool)
(declare-fun z$912 () Bool)
(declare-fun z$914 () Bool)
(declare-fun z$89 () Bool)
(declare-fun z$911 () Bool)
(declare-fun z$913 () Bool)
(declare-fun z$935 () Bool)
(declare-fun z$936 () Bool)
(declare-fun z$965 () Bool)
(declare-fun z$966 () Bool)
(declare-fun z$813 () Bool)
(declare-fun z$1001 () Bool)
(declare-fun z$1002 () Bool)
(declare-fun z$1032 () Bool)
(declare-fun z$1033 () Bool)
(declare-fun z$1110 () Bool)
(declare-fun z$1111 () Bool)
(declare-fun z$1148 () Bool)
(declare-fun z$1173 () Bool)
(declare-fun z$1174 () Bool)
(declare-fun z$1184 () Bool)
(declare-fun z$1212 () Bool)
(declare-fun z$1213 () Bool)
(declare-fun z$1287 () Bool)
(declare-fun z$1288 () Bool)
(declare-fun z$1309 () Bool)
(declare-fun z$1310 () Bool)
(declare-fun z$1352 () Bool)
(declare-fun z$1353 () Bool)
(declare-fun z$1368 () Bool)
(declare-fun z$1369 () Bool)
(declare-fun z$1455 () Bool)
(declare-fun z$1456 () Bool)
(declare-fun z$1185 () Bool)
(declare-fun z$1476 () Bool)
(declare-fun z$1477 () Bool)
(declare-fun z$1489 () Bool)
(declare-fun z$1491 () Bool)
(declare-fun z$1506 () Bool)
(declare-fun z$1507 () Bool)
(declare-fun z$1561 () Bool)
(declare-fun z$1586 () Bool)
(declare-fun z$1587 () Bool)
(declare-fun z$1590 () Bool)
(declare-fun z$1622 () Bool)
(declare-fun z$1624 () Bool)
(declare-fun z$1599 () Bool)
(declare-fun z$1240 () Bool)
(declare-fun z$1623 () Bool)
(declare-fun z$1630 () Bool)
(declare-fun z$1641 () Bool)
(declare-fun z$1644 () Bool)
(declare-fun z$1645 () Bool)
(declare-fun z$1663 () Bool)
(declare-fun z$1664 () Bool)
(declare-fun z$1687 () Bool)
(declare-fun z$1688 () Bool)
(declare-fun z$1706 () Bool)
(declare-fun z$1707 () Bool)
(declare-fun p$0 () Bool)
(declare-fun p$1 () Bool)
(declare-fun z$79 () Bool)
(declare-fun p$2 () Bool)
(declare-fun p$3 () Bool)
(declare-fun p$4 () Bool)
(declare-fun p$5 () Bool)
(declare-fun z$102 () Bool)
(declare-fun p$6 () Bool)
(declare-fun p$7 () Bool)
(declare-fun z$108 () Bool)
(declare-fun p$8 () Bool)
(declare-fun p$9 () Bool)
(declare-fun p$10 () Bool)
(declare-fun z$111 () Bool)
(declare-fun p$11 () Bool)
(declare-fun p$12 () Bool)
(declare-fun z$113 () Bool)
(declare-fun p$13 () Bool)
(declare-fun p$14 () Bool)
(declare-fun p$15 () Bool)
(declare-fun p$16 () Bool)
(declare-fun p$17 () Bool)
(assert
 (and (distinct z$n0s3 z$n4s3 z$n5s3 z$n7s3 z$n3s3 z$n1s3 z$n2s3 z$n6s3) true))
(assert
 (and (distinct z$n1s32 z$n5s32 z$n2s32 z$n7s32 z$n3s32 z$n8s32 z$n4s32 z$n6s32 z$n0s32) true))
(assert
 (let (($x126 (not b0)))
 (= z$1 $x126)))
(assert
 (let (($x209 (not b1)))
 (= z$3 $x209)))
(assert
 (let (($x212 (= x z$n0s3)))
 (= z$6 $x212)))
(assert
 (let (($x102 (= y z$n0s3)))
 (= z$8 $x102)))
(assert
 (= z$9 (and z$1 z$3 z$6 z$8)))
(assert
 (= z$188 (not z$9)))
(assert
 (let ((?x199 (Concat_32_3_29 x z$n0s29)))
 (= z$13 ?x199)))
(assert
 (let ((?x149 (Add_32_32_32 z$13 z$n1s32)))
 (= z$16 ?x149)))
(assert
 (let (($x4848 (= z$16 z$n1s32)))
 (= z$313 $x4848)))
(assert
 (= z$510 (and z$188 z$313)))
(assert
 (= z$511 (not z$510)))
(assert
 z$511)
(assert
 (let (($x4407 (= z$13 z$n1s32)))
 (= z$330 $x4407)))
(assert
 (= z$591 (and z$1 z$330)))
(assert
 (= z$593 (not z$591)))
(assert
 z$593)
(assert
 (= z$833 (and (distinct x z$n2s3) true)))
(assert
 (= z$946 (and z$1 z$833)))
(assert
 (= z$949 (and z$188 z$946)))
(assert
 (= z$950 (not z$949)))
(assert
 z$950)
(assert
 (= z$87 (and (distinct z$13 z$n1s32) true)))
(assert
 (let (($x1174 (= x z$n2s3)))
 (= z$806 $x1174)))
(assert
 (= z$1014 (and b0 z$87 z$806)))
(assert
 (= z$1015 (not z$1014)))
(assert
 z$1015)
(assert
 (let (($x1445 (= x y)))
 (= z$128 $x1445)))
(assert
 (= z$688 (and b0 z$3 z$128)))
(assert
 (= z$689 (not z$688)))
(assert
 z$689)
(assert
 (let ((?x151 (Concat_32_3_29 y z$n0s29)))
 (= z$24 ?x151)))
(assert
 (let (($x3289 (= z$24 z$13)))
 (= z$130 $x3289)))
(assert
 (= z$677 (and z$1 b1 z$130)))
(assert
 (= z$678 (not z$677)))
(assert
 z$678)
(assert
 (= z$1177 (and (distinct y z$n3s3) true)))
(assert
 (= z$1235 (and b1 z$87 z$128 z$1177)))
(assert
 (= z$1236 (not z$1235)))
(assert
 z$1236)
(assert
 (= z$86 (and (distinct x y) true)))
(assert
 (= z$92 (and (distinct z$24 z$n1s32) true)))
(assert
 (let (($x1185 (= y z$n3s3)))
 (= z$1158 $x1185)))
(assert
 (= z$1248 (and b1 z$86 z$92 z$1158)))
(assert
 (= z$1249 (not z$1248)))
(assert
 z$1249)
(assert
 (= z$1259 (and b0 z$86 z$1158)))
(assert
 (= z$1260 (not z$1259)))
(assert
 z$1260)
(assert
 (= z$1179 (and (distinct x z$n3s3) true)))
(assert
 (= z$1270 (and b0 b1 z$86 z$1179)))
(assert
 (= z$1271 (not z$1270)))
(assert
 z$1271)
(assert
 (= z$1226 (and b0 z$87 z$1179)))
(assert
 (= z$1227 (not z$1226)))
(assert
 z$1227)
(assert
 (let ((?x154 (Add_32_32_32 z$24 z$n1s32)))
 (= z$26 ?x154)))
(assert
 (= z$93 (and (distinct z$26 z$n1s32) true)))
(assert
 (= z$1085 (and z$3 z$93 z$330)))
(assert
 (= z$1086 (not z$1085)))
(assert
 z$1086)
(assert
 (= z$1378 (and z$313 z$128)))
(assert
 (= z$1381 (and z$188 z$1378)))
(assert
 (= z$1382 (not z$1381)))
(assert
 z$1382)
(assert
 (= z$1390 (and z$1 z$128 z$833)))
(assert
 (= z$1393 (and z$188 z$1390)))
(assert
 (= z$1394 (not z$1393)))
(assert
 z$1394)
(assert
 (= z$1408 (and z$3 z$833 z$1)))
(assert
 (= z$1411 (and z$188 z$1408)))
(assert
 (= z$1412 (not z$1411)))
(assert
 z$1412)
(assert
 (let (($x51 (LeEq_1_3_3 y x)))
 (= z$39 $x51)))
(assert
 (= z$41 (= prop z$39)))
(assert
 z$41)
(assert
 prop)
(assert
 (= z$11 (= b0 b1)))
(assert
 (let ((?x195 (Extract_3_2_0_32 z$16)))
 (= z$18 ?x195)))
(assert
 (let ((?x185 (ite z$11 z$18 x)))
 (= z$20 ?x185)))
(assert
 (let (($x113 (= x$next z$20)))
 (= z$22 $x113)))
(assert
 z$22)
(assert
 (let ((?x158 (Extract_3_2_0_32 z$26)))
 (= z$28 ?x158)))
(assert
 (let ((?x165 (ite z$11 y z$28)))
 (= z$30 ?x165)))
(assert
 (let (($x111 (= y$next z$30)))
 (= z$32 $x111)))
(assert
 z$32)
(assert
 (= z$34 (= b0$next z$3)))
(assert
 z$34)
(assert
 (= z$36 (= b1$next b0)))
(assert
 z$36)
(assert
 (let (($x72 (LeEq_1_3_3 y$next x$next)))
 (= z$50 $x72)))
(assert
 (= z$52 (= prop$next z$50)))
(assert
 z$52)
(assert
 (= z$59 (not z$50)))
(assert
 (let (($x43 (= y$next z$n0s3)))
 (= z$60 $x43)))
(assert
 (= z$61 (and z$59 z$60)))
(assert
 (= z$63 (not z$61)))
(assert
 z$63)
(assert
 (= z$54 (not z$39)))
(assert
 (= z$58 (and z$54 z$8)))
(assert
 (= z$62 (not z$58)))
(assert
 z$62)
(assert
 (= z$142 (and b0 z$3 z$39 z$59 z$86 z$22 z$32)))
(assert
 (= z$143 (not z$142)))
(assert
 z$143)
(assert
 (let (($x527 (= x$next y$next)))
 (= z$131 $x527)))
(assert
 (= z$171 (and z$1 z$3 z$131 z$6 z$8 z$22 z$32)))
(assert
 (= z$172 (not z$171)))
(assert
 z$172)
(assert
 (let ((?x236 (Concat_32_3_29 y$next z$n0s29)))
 (= z$103 ?x236)))
(assert
 (let ((?x248 (Add_32_32_32 z$103 z$n1s32)))
 (= z$106 ?x248)))
(assert
 (let ((?x132 (Concat_32_3_29 x$next z$n0s29)))
 (= z$97 ?x132)))
(assert
 (let ((?x224 (Add_32_32_32 z$97 z$n1s32)))
 (= z$100 ?x224)))
(assert
 (let (($x2970 (= z$106 z$100)))
 (= z$132 $x2970)))
(assert
 (= z$90 (and (distinct z$13 z$26) true)))
(assert
 (= z$233 (and b0 z$3 z$39 z$22 z$32 z$132 z$90)))
(assert
 (= z$234 (not z$233)))
(assert
 z$234)
(assert
 (= z$96 (and (distinct z$24 z$26) true)))
(assert
 z$96)
(assert
 (= z$114 (and (distinct z$103 z$106) true)))
(assert
 z$114)
(assert
 (= z$109 (and (distinct z$100 z$n1s32) true)))
(assert
 (= z$281 (and b0 b1 z$109 z$59 z$128 z$22 z$32)))
(assert
 (= z$282 (not z$281)))
(assert
 z$282)
(assert
 (= z$91 (and (distinct z$16 z$n1s32) true)))
(assert
 (= z$308 (and z$6 z$91)))
(assert
 (= z$310 (not z$308)))
(assert
 z$310)
(assert
 (let (($x3471 (= x$next z$n0s3)))
 (= z$192 $x3471)))
(assert
 (= z$309 (and z$192 z$109)))
(assert
 (= z$317 (not z$309)))
(assert
 z$317)
(assert
 (let (($x5123 (= z$103 z$n1s32)))
 (= z$342 $x5123)))
(assert
 (= z$358 (and z$342 z$330 z$22 z$59)))
(assert
 (= z$359 (not z$358)))
(assert
 z$359)
(assert
 (let (($x1849 (= z$100 z$n1s32)))
 (= z$285 $x1849)))
(assert
 (let (($x2373 (= z$97 z$n1s32)))
 (= z$344 $x2373)))
(assert
 (= z$384 (and z$285 z$344)))
(assert
 (= z$386 (not z$384)))
(assert
 z$386)
(assert
 (= z$383 (and z$313 z$330)))
(assert
 (= z$385 (not z$383)))
(assert
 z$385)
(assert
 (= z$402 (and z$330 z$285 z$22)))
(assert
 (= z$403 (not z$402)))
(assert
 z$403)
(assert
 (= z$418 (and b0 b1 z$39 z$330 z$32 z$22 z$59)))
(assert
 (= z$419 (not z$418)))
(assert
 z$419)
(assert
 (= z$435 (and b0 b1 z$39 z$59 z$22 z$32 z$109)))
(assert
 (= z$436 (not z$435)))
(assert
 z$436)
(assert
 (let (($x3583 (= z$26 z$n1s32)))
 (= z$348 $x3583)))
(assert
 (= z$110 (and (distinct z$103 z$n1s32) true)))
(assert
 (= z$450 (and b0 z$3 z$348 z$110 z$32)))
(assert
 (= z$451 (not z$450)))
(assert
 z$451)
(assert
 (= z$99 (and (distinct z$97 z$n1s32) true)))
(assert
 (= z$480 (and z$1 z$3 z$22 z$99 z$313)))
(assert
 (= z$481 (not z$480)))
(assert
 z$481)
(assert
 (let (($x2831 (= z$24 z$n1s32)))
 (= z$343 $x2831)))
(assert
 (= z$112 (and (distinct z$100 z$103) true)))
(assert
 (= z$542 (and z$344 z$343 z$112 z$110 z$32)))
(assert
 (= z$543 (not z$542)))
(assert
 z$543)
(assert
 (= z$564 (and z$86 z$343 z$330)))
(assert
 (= z$566 (not z$564)))
(assert
 z$566)
(assert
 (= z$85 (and (distinct x$next y$next) true)))
(assert
 (= z$565 (and z$85 z$342 z$344)))
(assert
 (= z$568 (not z$565)))
(assert
 z$568)
(assert
 (= z$581 (and b0 b1 z$22 z$344 z$330)))
(assert
 (= z$582 (not z$581)))
(assert
 z$582)
(assert
 (let (($x4665 (= z$100 z$103)))
 (= z$547 $x4665)))
(assert
 (= z$605 (and z$1 b1 z$547 z$343 z$99 z$32)))
(assert
 (= z$606 (not z$605)))
(assert
 z$606)
(assert
 (= z$621 (and z$1 b1 z$39 z$59 z$86 z$22 z$32)))
(assert
 (= z$622 (not z$621)))
(assert
 z$622)
(assert
 (let (($x2407 (= z$26 z$16)))
 (= z$129 $x2407)))
(assert
 (= z$700 (and z$1 z$3 z$22 z$32 z$547 z$129)))
(assert
 (= z$701 (not z$700)))
(assert
 z$701)
(assert
 (= z$720 (and z$1 z$3 z$22 z$91 z$344)))
(assert
 (= z$721 (not z$720)))
(assert
 z$721)
(assert
 (= z$735 (and z$1 z$3 z$59 z$129 z$109 z$32 z$22)))
(assert
 (= z$736 (not z$735)))
(assert
 z$736)
(assert
 (= z$750 (and z$1 b1 z$131 z$22 z$32 z$343 z$90)))
(assert
 (= z$751 (not z$750)))
(assert
 z$751)
(assert
 (= z$829 (and z$806 z$285 z$22)))
(assert
 (= z$830 (not z$829)))
(assert
 z$830)
(assert
 (= z$842 (and (distinct x$next z$n2s3) true)))
(assert
 (let (($x4162 (= z$97 z$106)))
 (= z$248 $x4162)))
(assert
 (= z$862 (and z$842 z$342 z$248)))
(assert
 (= z$864 (not z$862)))
(assert
 z$864)
(assert
 (let (($x4918 (= z$13 z$26)))
 (= z$238 $x4918)))
(assert
 (= z$861 (and z$833 z$343 z$238)))
(assert
 (= z$863 (not z$861)))
(assert
 z$863)
(assert
 (= z$892 (and z$86 z$130)))
(assert
 (= z$894 (not z$892)))
(assert
 z$894)
(assert
 (let (($x914 (= z$103 z$97)))
 (= z$133 $x914)))
(assert
 (= z$893 (and z$85 z$133)))
(assert
 (= z$896 (not z$893)))
(assert
 z$896)
(assert
 (= z$105 (and (distinct z$97 z$103) true)))
(assert
 (= z$912 (and z$105 z$132)))
(assert
 (= z$914 (not z$912)))
(assert
 z$914)
(assert
 (= z$89 (and (distinct z$13 z$24) true)))
(assert
 (= z$911 (and z$89 z$129)))
(assert
 (= z$913 (not z$911)))
(assert
 z$913)
(assert
 (= z$935 (and b0 b1 z$22 z$330 z$842)))
(assert
 (= z$936 (not z$935)))
(assert
 z$936)
(assert
 (= z$965 (and z$1 z$3 z$39 z$806 z$32 z$22 z$59)))
(assert
 (= z$966 (not z$965)))
(assert
 z$966)
(assert
 (let (($x2015 (= x$next z$n2s3)))
 (= z$813 $x2015)))
(assert
 (= z$1001 (and z$1 z$3 z$22 z$806 z$813)))
(assert
 (= z$1002 (not z$1001)))
(assert
 z$1002)
(assert
 (= z$1032 (and z$1 z$3 z$39 z$131 z$22 z$32 z$806)))
(assert
 (= z$1033 (not z$1032)))
(assert
 z$1033)
(assert
 (= z$1110 (and z$1 z$3 z$86 z$22 z$32 z$248)))
(assert
 (= z$1111 (not z$1110)))
(assert
 z$1111)
(assert
 (let (($x5193 (= x z$n3s3)))
 (= z$1148 $x5193)))
(assert
 (= z$1173 (and z$1158 z$1148 b1 b0 z$59 z$22 z$32)))
(assert
 (= z$1174 (not z$1173)))
(assert
 z$1174)
(assert
 (= z$1184 (and (distinct x$next z$n3s3) true)))
(assert
 (= z$1212 (and z$1 z$3 z$22 z$806 z$1184)))
(assert
 (= z$1213 (not z$1212)))
(assert
 z$1213)
(assert
 (= z$1287 (and z$1148 z$342 z$22 z$59)))
(assert
 (= z$1288 (not z$1287)))
(assert
 z$1288)
(assert
 (= z$1309 (and b0 b1 z$39 z$1148 z$32 z$22 z$59)))
(assert
 (= z$1310 (not z$1309)))
(assert
 z$1310)
(assert
 (= z$1352 (and z$1 b1 z$348 z$110 z$32)))
(assert
 (= z$1353 (not z$1352)))
(assert
 z$1353)
(assert
 (= z$1368 (and b0 b1 z$39 z$131 z$22 z$32 z$1148)))
(assert
 (= z$1369 (not z$1368)))
(assert
 z$1369)
(assert
 (= z$1455 (and b0 b1 z$22 z$32 z$238 z$248)))
(assert
 (= z$1456 (not z$1455)))
(assert
 z$1456)
(assert
 (= z$1185 (and (distinct y$next z$n3s3) true)))
(assert
 (= z$1476 (and b0 b1 z$1185 z$1148 z$248 z$22)))
(assert
 (= z$1477 (not z$1476)))
(assert
 z$1477)
(assert
 (= z$1489 (and z$1 z$238 z$833 z$1177)))
(assert
 (= z$1491 (not z$1489)))
(assert
 z$1491)
(assert
 (= z$1506 (and z$1 b1 z$39 z$131 z$22 z$32 z$90)))
(assert
 (= z$1507 (not z$1506)))
(assert
 z$1507)
(assert
 (let (($x3028 (= x z$n4s3)))
 (= z$1561 $x3028)))
(assert
 (= z$1586 (and z$1561 z$285 z$22)))
(assert
 (= z$1587 (not z$1586)))
(assert
 z$1587)
(assert
 (= z$1590 (and (distinct x z$n4s3) true)))
(assert
 (= z$1622 (and z$1590 z$1158 z$238)))
(assert
 (= z$1624 (not z$1622)))
(assert
 z$1624)
(assert
 (= z$1599 (and (distinct x$next z$n4s3) true)))
(assert
 (let (($x2199 (= y$next z$n3s3)))
 (= z$1240 $x2199)))
(assert
 (= z$1623 (and z$1599 z$1240 z$248)))
(assert
 (= z$1630 (not z$1623)))
(assert
 z$1630)
(assert
 (= z$1641 (and z$833 z$128 z$1 z$1590)))
(assert
 (= z$1644 (and z$188 z$1641)))
(assert
 (= z$1645 (not z$1644)))
(assert
 z$1645)
(assert
 (= z$1663 (and z$1 z$3 z$39 z$1561 z$32 z$22 z$59)))
(assert
 (= z$1664 (not z$1663)))
(assert
 z$1664)
(assert
 (= z$1687 (and z$1 z$3 z$39 z$59 z$22 z$32 z$109)))
(assert
 (= z$1688 (not z$1687)))
(assert
 z$1688)
(assert
 (= z$1706 (and b0 b1 z$22 z$1148 z$1599)))
(assert
 (= z$1707 (not z$1706)))
(assert
 z$1707)
(assert
 (=> p$0 b1$next))
(assert
 (let (($x72 (LeEq_1_3_3 y$next x$next)))
 (let (($x71 (= z$50 $x72)))
 (=> p$1 $x71))))
(assert
 (=> p$1 z$50))
(assert
 (=> p$2 (= z$79 (not b0$next))))
(assert
 (=> p$2 z$79))
(assert
 (let (($x138 (= z$85 (and (distinct x$next y$next) true))))
 (=> p$3 $x138)))
(assert
 (=> p$3 z$85))
(assert
 (let ((?x132 (Concat_32_3_29 x$next z$n0s29)))
 (let (($x124 (= z$97 ?x132)))
 (=> p$4 $x124))))
(assert
 (let (($x218 (= z$99 (and (distinct z$97 z$n1s32) true))))
 (=> p$4 $x218)))
(assert
 (=> p$4 z$99))
(assert
 (let ((?x132 (Concat_32_3_29 x$next z$n0s29)))
 (let (($x124 (= z$97 ?x132)))
 (=> p$5 $x124))))
(assert
 (let ((?x224 (Add_32_32_32 z$97 z$n1s32)))
 (let (($x225 (= z$100 ?x224)))
 (=> p$5 $x225))))
(assert
 (=> p$5 (= z$102 (and (distinct z$97 z$100) true))))
(assert
 (=> p$5 z$102))
(assert
 (let ((?x132 (Concat_32_3_29 x$next z$n0s29)))
 (let (($x124 (= z$97 ?x132)))
 (=> p$6 $x124))))
(assert
 (let ((?x236 (Concat_32_3_29 y$next z$n0s29)))
 (let (($x237 (= z$103 ?x236)))
 (=> p$6 $x237))))
(assert
 (let (($x241 (= z$105 (and (distinct z$97 z$103) true))))
 (=> p$6 $x241)))
(assert
 (=> p$6 z$105))
(assert
 (let ((?x132 (Concat_32_3_29 x$next z$n0s29)))
 (let (($x124 (= z$97 ?x132)))
 (=> p$7 $x124))))
(assert
 (let ((?x236 (Concat_32_3_29 y$next z$n0s29)))
 (let (($x237 (= z$103 ?x236)))
 (=> p$7 $x237))))
(assert
 (let ((?x248 (Add_32_32_32 z$103 z$n1s32)))
 (let (($x249 (= z$106 ?x248)))
 (=> p$7 $x249))))
(assert
 (=> p$7 (= z$108 (and (distinct z$97 z$106) true))))
(assert
 (=> p$7 z$108))
(assert
 (let ((?x132 (Concat_32_3_29 x$next z$n0s29)))
 (let (($x124 (= z$97 ?x132)))
 (=> p$8 $x124))))
(assert
 (let ((?x224 (Add_32_32_32 z$97 z$n1s32)))
 (let (($x225 (= z$100 ?x224)))
 (=> p$8 $x225))))
(assert
 (let (($x262 (= z$109 (and (distinct z$100 z$n1s32) true))))
 (=> p$8 $x262)))
(assert
 (=> p$8 z$109))
(assert
 (let ((?x236 (Concat_32_3_29 y$next z$n0s29)))
 (let (($x237 (= z$103 ?x236)))
 (=> p$9 $x237))))
(assert
 (let (($x270 (= z$110 (and (distinct z$103 z$n1s32) true))))
 (=> p$9 $x270)))
(assert
 (=> p$9 z$110))
(assert
 (let ((?x236 (Concat_32_3_29 y$next z$n0s29)))
 (let (($x237 (= z$103 ?x236)))
 (=> p$10 $x237))))
(assert
 (let ((?x248 (Add_32_32_32 z$103 z$n1s32)))
 (let (($x249 (= z$106 ?x248)))
 (=> p$10 $x249))))
(assert
 (=> p$10 (= z$111 (and (distinct z$106 z$n1s32) true))))
(assert
 (=> p$10 z$111))
(assert
 (let ((?x132 (Concat_32_3_29 x$next z$n0s29)))
 (let (($x124 (= z$97 ?x132)))
 (=> p$11 $x124))))
(assert
 (let ((?x224 (Add_32_32_32 z$97 z$n1s32)))
 (let (($x225 (= z$100 ?x224)))
 (=> p$11 $x225))))
(assert
 (let ((?x236 (Concat_32_3_29 y$next z$n0s29)))
 (let (($x237 (= z$103 ?x236)))
 (=> p$11 $x237))))
(assert
 (let (($x285 (= z$112 (and (distinct z$100 z$103) true))))
 (=> p$11 $x285)))
(assert
 (=> p$11 z$112))
(assert
 (let ((?x132 (Concat_32_3_29 x$next z$n0s29)))
 (let (($x124 (= z$97 ?x132)))
 (=> p$12 $x124))))
(assert
 (let ((?x224 (Add_32_32_32 z$97 z$n1s32)))
 (let (($x225 (= z$100 ?x224)))
 (=> p$12 $x225))))
(assert
 (let ((?x236 (Concat_32_3_29 y$next z$n0s29)))
 (let (($x237 (= z$103 ?x236)))
 (=> p$12 $x237))))
(assert
 (let ((?x248 (Add_32_32_32 z$103 z$n1s32)))
 (let (($x249 (= z$106 ?x248)))
 (=> p$12 $x249))))
(assert
 (=> p$12 (= z$113 (and (distinct z$100 z$106) true))))
(assert
 (=> p$12 z$113))
(assert
 (let ((?x236 (Concat_32_3_29 y$next z$n0s29)))
 (let (($x237 (= z$103 ?x236)))
 (=> p$13 $x237))))
(assert
 (let ((?x248 (Add_32_32_32 z$103 z$n1s32)))
 (let (($x249 (= z$106 ?x248)))
 (=> p$13 $x249))))
(assert
 (let (($x304 (= z$114 (and (distinct z$103 z$106) true))))
 (=> p$13 $x304)))
(assert
 (=> p$13 z$114))
(assert
 (let (($x3293 (= z$842 (and (distinct x$next z$n2s3) true))))
 (=> p$14 $x3293)))
(assert
 (=> p$14 z$842))
(assert
 (let (($x5301 (= z$1184 (and (distinct x$next z$n3s3) true))))
 (=> p$15 $x5301)))
(assert
 (=> p$15 z$1184))
(assert
 (let (($x5256 (= z$1185 (and (distinct y$next z$n3s3) true))))
 (=> p$16 $x5256)))
(assert
 (=> p$16 z$1185))
(assert
 (let (($x7401 (= z$1599 (and (distinct x$next z$n4s3) true))))
 (=> p$17 $x7401)))
(assert
 (=> p$17 z$1599))
(check-sat)
(assert p$0)
(assert p$1)
(assert p$2)
(assert p$3)
(assert p$4)
(assert p$5)
(assert p$6)
(assert p$7)
(assert p$8)
(assert p$9)
(assert p$10)
(assert p$11)
(assert p$12)
(assert p$13)
(assert p$14)
(assert p$15)
(assert p$16)
(assert p$17)
(set-info :status unsat)
(check-sat)
(exit)