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

id: itc99_b13
query-maker: "Yices 2"
query-time: 0.590000 ms
query-class: abstract
query-category: oneshot
query-type: regular
status: sat
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")

;
(set-info :status sat)
(declare-sort utt$2 0)
(declare-sort utt$3 0)
(declare-sort utt$4 0)
(declare-sort utt$8 0)
(declare-sort utt$10 0)
(declare-sort utt$24 0)
(declare-sort utt$30 0)
(declare-sort utt$31 0)
(declare-sort utt$32 0)
(declare-fun Concat_32_1_31 (Bool utt$31 ) utt$32)
(declare-fun Concat_32_2_30 (utt$2 utt$30 ) utt$32)
(declare-fun Concat_32_8_24 (utt$8 utt$24 ) utt$32)
(declare-fun Concat_4_1_3 (Bool utt$3 ) utt$4)
(declare-fun Extract_1_3_3_4 (utt$4 ) Bool)
(declare-fun Extract_2_9_8_10 (utt$10 ) utt$2)
(declare-fun y$1 () Bool)
(declare-fun y$10 () Bool)
(declare-fun y$12 () Bool)
(declare-fun y$14 () Bool)
(declare-fun y$16 () Bool)
(declare-fun y$18 () Bool)
(declare-fun y$20 () Bool)
(declare-fun y$22 () Bool)
(declare-fun y$223 () Bool)
(declare-fun y$225 () Bool)
(declare-fun y$228 () Bool)
(declare-fun y$231 () Bool)
(declare-fun y$236 () Bool)
(declare-fun y$239 () utt$2)
(declare-fun y$24 () Bool)
(declare-fun y$244 () Bool)
(declare-fun y$251 () Bool)
(declare-fun y$254 () Bool)
(declare-fun y$259 () Bool)
(declare-fun y$26 () Bool)
(declare-fun y$263 () Bool)
(declare-fun y$270 () Bool)
(declare-fun y$273 () Bool)
(declare-fun y$280 () Bool)
(declare-fun y$289 () Bool)
(declare-fun y$292 () Bool)
(declare-fun y$3 () Bool)
(declare-fun y$30 () Bool)
(declare-fun y$303 () Bool)
(declare-fun y$313 () Bool)
(declare-fun y$32 () Bool)
(declare-fun y$320 () Bool)
(declare-fun y$325 () Bool)
(declare-fun y$334 () Bool)
(declare-fun y$337 () Bool)
(declare-fun y$34 () Bool)
(declare-fun y$346 () Bool)
(declare-fun y$347 () Bool)
(declare-fun y$354 () Bool)
(declare-fun y$36 () Bool)
(declare-fun y$360 () Bool)
(declare-fun y$369 () Bool)
(declare-fun y$374 () Bool)
(declare-fun y$377 () Bool)
(declare-fun y$38 () Bool)
(declare-fun y$385 () Bool)
(declare-fun y$390 () Bool)
(declare-fun y$397 () Bool)
(declare-fun y$40 () Bool)
(declare-fun y$407 () Bool)
(declare-fun y$414 () utt$2)
(declare-fun y$42 () Bool)
(declare-fun y$44 () Bool)
(declare-fun y$47 () Bool)
(declare-fun y$49 () Bool)
(declare-fun y$5 () Bool)
(declare-fun y$550 () Bool)
(declare-fun y$552 () Bool)
(declare-fun y$554 () Bool)
(declare-fun y$556 () Bool)
(declare-fun y$582 () Bool)
(declare-fun y$605 () Bool)
(declare-fun y$606 () Bool)
(declare-fun y$607 () Bool)
(declare-fun y$608 () Bool)
(declare-fun y$609 () Bool)
(declare-fun y$610 () Bool)
(declare-fun y$613 () Bool)
(declare-fun y$627 () Bool)
(declare-fun y$628 () Bool)
(declare-fun y$629 () Bool)
(declare-fun y$630 () Bool)
(declare-fun y$631 () Bool)
(declare-fun y$632 () Bool)
(declare-fun y$645 () Bool)
(declare-fun y$662 () Bool)
(declare-fun y$663 () Bool)
(declare-fun y$664 () Bool)
(declare-fun y$665 () Bool)
(declare-fun y$666 () Bool)
(declare-fun y$667 () Bool)
(declare-fun y$678 () Bool)
(declare-fun y$8 () Bool)
(declare-fun y$S1 () Bool)
(declare-fun y$S2 () Bool)
(declare-fun y$add_mpx2 () Bool)
(declare-fun y$canale () utt$4)
(declare-fun y$canale$next () utt$4)
(declare-fun y$confirm () Bool)
(declare-fun y$conta_tmp () utt$4)
(declare-fun y$data_out () Bool)
(declare-fun y$error () Bool)
(declare-fun y$itfc_state () Bool)
(declare-fun y$load () Bool)
(declare-fun y$load_dato () Bool)
(declare-fun y$mpx () Bool)
(declare-fun y$mux_en () Bool)
(declare-fun y$n0s10 () utt$10)
(declare-fun y$n0s24 () utt$24)
(declare-fun y$n0s3 () utt$3)
(declare-fun y$n0s30 () utt$30)
(declare-fun y$n0s31 () utt$31)
(declare-fun y$n0s32 () utt$32)
(declare-fun y$n0s4 () utt$4)
(declare-fun y$n0s8 () utt$8)
(declare-fun y$n104s32 () utt$32)
(declare-fun y$n1s32 () utt$32)
(declare-fun y$n1s4 () utt$4)
(declare-fun y$next_bit () Bool)
(declare-fun y$out_reg () utt$8)
(declare-fun y$out_reg$next () utt$8)
(declare-fun y$prop () Bool)
(declare-fun y$prop0 () Bool)
(declare-fun y$prop0_op () Bool)
(declare-fun y$prop_1 () Bool)
(declare-fun y$prop_10 () Bool)
(declare-fun y$prop_10_op () Bool)
(declare-fun y$prop_11 () Bool)
(declare-fun y$prop_11_op () Bool)
(declare-fun y$prop_12 () Bool)
(declare-fun y$prop_12_op () Bool)
(declare-fun y$prop_13 () Bool)
(declare-fun y$prop_13_op () Bool)
(declare-fun y$prop_14 () Bool)
(declare-fun y$prop_14_op () Bool)
(declare-fun y$prop_15 () Bool)
(declare-fun y$prop_15_op () Bool)
(declare-fun y$prop_16 () Bool)
(declare-fun y$prop_16_op () Bool)
(declare-fun y$prop_17 () Bool)
(declare-fun y$prop_17_op () Bool)
(declare-fun y$prop_18 () Bool)
(declare-fun y$prop_18_op () Bool)
(declare-fun y$prop_19 () Bool)
(declare-fun y$prop_19_op () Bool)
(declare-fun y$prop_1_op () Bool)
(declare-fun y$prop_20 () Bool)
(declare-fun y$prop_20_op () Bool)
(declare-fun y$prop_21 () Bool)
(declare-fun y$prop_21_op () Bool)
(declare-fun y$prop_22 () Bool)
(declare-fun y$prop_22_op () Bool)
(declare-fun y$prop_4 () Bool)
(declare-fun y$prop_4_op () Bool)
(declare-fun y$prop_6 () Bool)
(declare-fun y$prop_6_op () Bool)
(declare-fun y$prop_7 () Bool)
(declare-fun y$prop_7_op () Bool)
(declare-fun y$prop_8 () Bool)
(declare-fun y$prop_8_op () Bool)
(declare-fun y$prop_9 () Bool)
(declare-fun y$prop_9_op () Bool)
(declare-fun y$rdy () Bool)
(declare-fun y$s$100 () Bool)
(declare-fun y$s$100_op () Bool)
(declare-fun y$s$101 () Bool)
(declare-fun y$s$101_op () Bool)
(declare-fun y$s$102 () Bool)
(declare-fun y$s$102_op () Bool)
(declare-fun y$s$103 () Bool)
(declare-fun y$s$103_op () Bool)
(declare-fun y$s$104 () Bool)
(declare-fun y$s$104_op () Bool)
(declare-fun y$s$105 () Bool)
(declare-fun y$s$105_op () Bool)
(declare-fun y$s$106 () Bool)
(declare-fun y$s$106_op () Bool)
(declare-fun y$s$87 () Bool)
(declare-fun y$s$87_op () Bool)
(declare-fun y$s$88 () Bool)
(declare-fun y$s$88_op () Bool)
(declare-fun y$s$89 () Bool)
(declare-fun y$s$89_op () Bool)
(declare-fun y$s$90 () Bool)
(declare-fun y$s$90_op () Bool)
(declare-fun y$s$91 () Bool)
(declare-fun y$s$91_op () Bool)
(declare-fun y$s$92 () Bool)
(declare-fun y$s$92_op () Bool)
(declare-fun y$s$93 () Bool)
(declare-fun y$s$93_op () Bool)
(declare-fun y$s$94 () Bool)
(declare-fun y$s$94_op () Bool)
(declare-fun y$s$95 () Bool)
(declare-fun y$s$95_op () Bool)
(declare-fun y$s$96 () Bool)
(declare-fun y$s$96_op () Bool)
(declare-fun y$s$97 () Bool)
(declare-fun y$s$97_op () Bool)
(declare-fun y$s$98 () Bool)
(declare-fun y$s$98_op () Bool)
(declare-fun y$s$99 () Bool)
(declare-fun y$s$99_op () Bool)
(declare-fun y$send () Bool)
(declare-fun y$send_data () Bool)
(declare-fun y$send_en () Bool)
(declare-fun y$shot () Bool)
(declare-fun y$soc () Bool)
(declare-fun y$tre () Bool)
(declare-fun y$tx_conta () utt$10)
(declare-fun y$tx_conta$next () utt$10)
(declare-fun y$tx_end () Bool)
(declare-fun y$w$10 () utt$32)
(declare-fun y$w$10_op () utt$32)
(declare-fun y$w$11 () utt$32)
(declare-fun y$w$11_op () utt$32)
(declare-fun y$w$12 () utt$32)
(declare-fun y$w$12_op () utt$32)
(declare-fun y$w$13 () utt$32)
(declare-fun y$w$13_op () utt$32)
(declare-fun y$w$14 () utt$32)
(declare-fun y$w$14_op () utt$32)
(declare-fun y$w$15 () utt$4)
(declare-fun y$w$15_op () utt$4)
(declare-fun y$w$16 () utt$32)
(declare-fun y$w$16_op () utt$32)
(declare-fun y$w$17 () utt$32)
(declare-fun y$w$17_op () utt$32)
(declare-fun y$w$18 () utt$32)
(declare-fun y$w$18_op () utt$32)
(declare-fun y$w$19 () utt$32)
(declare-fun y$w$19_op () utt$32)
(declare-fun y$w$2 () utt$32)
(declare-fun y$w$20 () utt$32)
(declare-fun y$w$20_op () utt$32)
(declare-fun y$w$21 () utt$32)
(declare-fun y$w$21_op () utt$32)
(declare-fun y$w$22 () utt$32)
(declare-fun y$w$22$next () utt$32)
(declare-fun y$w$22$next_op () utt$32)
(declare-fun y$w$22_op () utt$32)
(declare-fun y$w$2_op () utt$32)
(declare-fun y$w$3 () utt$32)
(declare-fun y$w$3_op () utt$32)
(declare-fun y$w$4 () Bool)
(declare-fun y$w$4$next () Bool)
(declare-fun y$w$5 () utt$32)
(declare-fun y$w$5$next () utt$32)
(declare-fun y$w$5$next_op () utt$32)
(declare-fun y$w$5_op () utt$32)
(declare-fun y$w$6 () utt$2)
(declare-fun y$w$6$next () utt$2)
(declare-fun y$w$7 () utt$32)
(declare-fun y$w$7$next () utt$32)
(declare-fun y$w$7$next_op () utt$32)
(declare-fun y$w$7_op () utt$32)
(declare-fun y$w$8 () utt$32)
(declare-fun y$w$8_op () utt$32)
(declare-fun y$w$9 () utt$32)
(declare-fun y$w$9_op () utt$32)
(assert (not (= y$n0s4 y$n1s4)))
(assert (distinct y$n104s32 y$n1s32 y$n0s32))
(assert (= y$S1 (not y$1)))
(assert (= y$S2 (not y$3)))
(assert (= y$add_mpx2 (not y$5)))
(assert (= y$8 (= y$n0s4 y$canale)))
(assert (= y$confirm (not y$10)))
(assert (= y$12 (= y$n0s4 y$conta_tmp)))
(assert (= y$data_out (not y$14)))
(assert (= y$error (not y$16)))
(assert (= y$itfc_state (not y$18)))
(assert (= y$load (not y$20)))
(assert (= y$load_dato (not y$22)))
(assert (= y$mpx (not y$24)))
(assert (= y$mux_en (not y$26)))
(assert (= y$30 (= y$out_reg y$n0s8)))
(assert (= y$rdy (not y$32)))
(assert (= y$send (not y$34)))
(assert (= y$send_data (not y$36)))
(assert (= y$send_en (not y$38)))
(assert (= y$shot (not y$40)))
(assert (= y$soc (not y$42)))
(assert (= y$tre (not y$44)))
(assert (= y$47 (= y$tx_conta y$n0s10)))
(assert (= y$tx_end (not y$49)))
(assert (= y$prop (not y$397)))
(assert (= y$w$2_op (Concat_32_1_31 y$error y$n0s31)))
(assert (= y$225 (not (= y$n1s32 y$w$2_op))))
(assert (= y$w$3_op (Concat_32_1_31 y$tre y$n0s31)))
(assert (= y$228 (= y$n1s32 y$w$3_op)))
(assert (= y$prop_1_op (or y$225 y$228)))
(assert (= y$231 (Extract_1_3_3_4 y$canale)))
(assert (= y$w$5_op (Concat_32_1_31 y$231 y$n0s31)))
(assert (= y$236 (= y$n0s32 y$w$5_op)))
(assert (= y$s$87_op (and y$prop_1_op y$236)))
(assert (= y$239 (Extract_2_9_8_10 y$tx_conta)))
(assert (= y$w$7_op (Concat_32_2_30 y$239 y$n0s30)))
(assert (= y$244 (= y$n0s32 y$w$7_op)))
(assert (= y$s$88_op (and y$s$87_op y$244)))
(assert (= y$w$8_op (Concat_32_1_31 y$mpx y$n0s31)))
(assert (= y$251 (not (= y$n1s32 y$w$8_op))))
(assert (= y$w$9_op (Concat_32_1_31 y$rdy y$n0s31)))
(assert (= y$254 (= y$n1s32 y$w$9_op)))
(assert (= y$prop_4_op (or y$251 y$254)))
(assert (= y$s$89_op (and y$s$88_op y$prop_4_op)))
(assert (= y$259 (= y$canale y$conta_tmp)))
(assert (= y$s$90_op (and y$s$89_op y$259)))
(assert (= (not (= y$n1s32 y$w$3_op)) y$263))
(assert (= (= y$n1s32 y$w$2_op) y$223))
(assert (= y$prop_6_op (or y$263 y$223)))
(assert (= y$s$91_op (and y$s$90_op y$prop_6_op)))
(assert (= y$w$10_op (Concat_32_1_31 y$load y$n0s31)))
(assert (= y$270 (= y$n0s32 y$w$10_op)))
(assert (= y$w$11_op (Concat_32_1_31 y$send y$n0s31)))
(assert (= y$273 (= y$n0s32 y$w$11_op)))
(assert (= y$prop_7_op (or y$270 y$273)))
(assert (= y$s$92_op (and y$s$91_op y$prop_7_op)))
(assert (= y$w$12_op (Concat_32_1_31 y$confirm y$n0s31)))
(assert (= y$280 (= y$n0s32 y$w$12_op)))
(assert (= y$prop_8_op (or y$270 y$280)))
(assert (= y$s$93_op (and y$s$92_op y$prop_8_op)))
(assert (= y$prop_9_op (or y$273 y$280)))
(assert (= y$s$94_op (and y$s$93_op y$prop_9_op)))
(assert (= y$289 (= y$n0s32 y$w$2_op)))
(assert (= y$w$13_op (Concat_32_1_31 y$send_en y$n0s31)))
(assert (= y$292 (= y$n0s32 y$w$13_op)))
(assert (= y$prop_10_op (or y$289 y$292)))
(assert (= y$s$95_op (and y$s$94_op y$prop_10_op)))
(assert (= y$prop_11_op (or y$280 y$289)))
(assert (= y$s$96_op (and y$s$95_op y$prop_11_op)))
(assert (= y$w$14_op (Concat_32_1_31 y$tx_end y$n0s31)))
(assert (= y$303 (= y$n0s32 y$w$14_op)))
(assert (= y$prop_12_op (or y$289 y$303)))
(assert (= y$s$97_op (and y$s$96_op y$prop_12_op)))
(assert (= y$prop_13_op (or y$280 y$292)))
(assert (= y$s$98_op (and y$s$97_op y$prop_13_op)))
(assert (= (not (= y$n0s32 y$w$13_op)) y$313))
(assert (= y$prop_14_op (or y$303 y$313)))
(assert (= y$s$99_op (and y$s$98_op y$prop_14_op)))
(assert (= y$320 (not (= y$n1s32 y$w$14_op))))
(assert (= y$w$15_op (Concat_4_1_3 y$next_bit y$n0s3)))
(assert (= y$325 (= y$n1s4 y$w$15_op)))
(assert (= y$prop_15_op (or y$320 y$325)))
(assert (= y$s$100_op (and y$s$99_op y$prop_15_op)))
(assert (= y$w$16_op (Concat_32_1_31 y$load_dato y$n0s31)))
(assert (= y$334 (not (= y$n1s32 y$w$16_op))))
(assert (= y$w$17_op (Concat_32_1_31 y$soc y$n0s31)))
(assert (= y$337 (= y$n1s32 y$w$17_op)))
(assert (= y$prop_16_op (or y$334 y$337)))
(assert (= y$s$101_op (and y$s$100_op y$prop_16_op)))
(assert (= y$w$18_op (Concat_32_1_31 y$send_data y$n0s31)))
(assert (= y$346 (not (= y$n0s32 y$w$18_op))))
(assert (= y$347 (= y$n0s32 y$w$17_op)))
(assert (= y$prop_17_op (or y$346 y$347)))
(assert (= y$s$102_op (and y$s$101_op y$prop_17_op)))
(assert (= y$w$19_op (Concat_32_1_31 y$add_mpx2 y$n0s31)))
(assert (= y$354 (= y$n1s32 y$w$19_op)))
(assert (= y$prop_18_op (or y$251 y$354)))
(assert (= y$s$103_op (and y$s$102_op y$prop_18_op)))
(assert (= (not (= y$n1s32 y$w$19_op)) y$360))
(assert (= y$prop_19_op (or y$228 y$360)))
(assert (= y$s$104_op (and y$s$103_op y$prop_19_op)))
(assert (= y$w$20_op (Concat_32_1_31 y$shot y$n0s31)))
(assert (= y$369 (not (= y$n1s32 y$w$20_op))))
(assert (= y$prop_20_op (or y$254 y$369)))
(assert (= y$s$105_op (and y$s$104_op y$prop_20_op)))
(assert (= y$374 (= y$n0s32 y$w$16_op)))
(assert (= y$w$21_op (Concat_32_1_31 y$mux_en y$n0s31)))
(assert (= y$377 (= y$n0s32 y$w$21_op)))
(assert (= y$prop_21_op (or y$374 y$377)))
(assert (= y$s$106_op (and y$s$105_op y$prop_21_op)))
(assert (= y$w$22_op (Concat_32_8_24 y$out_reg y$n0s24)))
(assert (= y$385 (= y$n0s32 y$w$22_op)))
(assert (= y$prop_22_op (or y$228 y$385)))
(assert (= y$prop0_op (and y$s$106_op y$prop_22_op)))
(assert (= y$390 (= y$prop y$prop0_op)))
(assert (= y$407 (Extract_1_3_3_4 y$canale$next)))
(assert (= y$407 (not y$606)))
(assert (= y$w$5$next_op (Concat_32_1_31 y$407 y$n0s31)))
(assert (= y$607 (not (= y$n0s32 y$w$5$next_op))))
(assert (= y$608 (and y$606 y$607)))
(assert (= y$608 (not y$610)))
(assert (= y$231 (not y$552)))
(assert (= (not (= y$n0s32 y$w$5_op)) y$554))
(assert (= y$605 (and y$552 y$554)))
(assert (= y$605 (not y$609)))
(assert (= y$628 (= y$n0s10 y$tx_conta$next)))
(assert (= y$414 (Extract_2_9_8_10 y$tx_conta$next)))
(assert (= y$w$7$next_op (Concat_32_2_30 y$414 y$n0s30)))
(assert (= y$629 (not (= y$n0s32 y$w$7$next_op))))
(assert (= y$630 (and y$628 y$629)))
(assert (= y$630 (not y$632)))
(assert (= (not (= y$n0s32 y$w$7_op)) y$556))
(assert (= y$627 (and y$47 y$556)))
(assert (= y$627 (not y$631)))
(assert (= y$663 (= y$n0s8 y$out_reg$next)))
(assert (= y$w$22$next_op (Concat_32_8_24 y$out_reg$next y$n0s24)))
(assert (= y$664 (not (= y$n0s32 y$w$22$next_op))))
(assert (= y$665 (and y$663 y$664)))
(assert (= y$665 (not y$667)))
(assert (= (not (= y$n0s32 y$w$22_op)) y$582))
(assert (= y$662 (and y$30 y$582)))
(assert (= y$662 (not y$666)))
(assert (= y$678 (and y$1 y$3 y$5 y$8 y$10 y$12 y$14 y$16 y$18 y$20 y$22 y$24 y$26 y$next_bit y$30 y$32 y$34 y$36 y$38 y$40 y$42 y$44 y$47 y$49 y$397 y$390 y$610 y$609 y$632 y$631 y$667 y$666)))
(assert y$678)
(check-sat)
(exit)