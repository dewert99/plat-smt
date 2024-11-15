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

id: sw_sym_ex_v
query-maker: "Z3"
query-time: 0.415000 ms
query-class: abstract
query-category: assume
query-type: mus_min
status: sat
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")

; 
(set-info :status sat)
(declare-sort utt8 0)
(declare-fun z$n254s8 () utt8)
(declare-fun z$n6s8 () utt8)
(declare-fun z$n255s8 () utt8)
(declare-fun z$n1s8 () utt8)
(declare-fun z$n4s8 () utt8)
(declare-fun z$n5s8 () utt8)
(declare-fun z$n3s8 () utt8)
(declare-fun z$n2s8 () utt8)
(declare-fun z$n0s8 () utt8)
(declare-fun Add_8_8_8 (utt8 utt8) utt8)
(declare-fun Y () utt8)
(declare-fun X () utt8)
(declare-fun z$84 () utt8)
(declare-fun Y$next () utt8)
(declare-fun X$next () utt8)
(declare-fun z$240 () utt8)
(declare-fun a () utt8)
(declare-fun c () utt8)
(declare-fun z$30 () utt8)
(declare-fun z$32 () utt8)
(declare-fun z$34 () utt8)
(declare-fun z$40 () utt8)
(declare-fun z$42 () utt8)
(declare-fun z$44 () utt8)
(declare-fun b () utt8)
(declare-fun z$96 () Bool)
(declare-fun z$336 () Bool)
(declare-fun LoneHot () Bool)
(declare-fun L5 () Bool)
(declare-fun z$409 () Bool)
(declare-fun z$410 () Bool)
(declare-fun z$237 () Bool)
(declare-fun z$421 () Bool)
(declare-fun z$422 () Bool)
(declare-fun L4 () Bool)
(declare-fun z$8 () Bool)
(declare-fun z$281 () Bool)
(declare-fun z$347 () Bool)
(declare-fun z$375 () Bool)
(declare-fun z$376 () Bool)
(declare-fun z$20 () Bool)
(declare-fun L7 () Bool)
(declare-fun z$14 () Bool)
(declare-fun prop () Bool)
(declare-fun z$205 () Bool)
(declare-fun L7$next () Bool)
(declare-fun z$217 () Bool)
(declare-fun prop$next () Bool)
(declare-fun z$218 () Bool)
(declare-fun L3 () Bool)
(declare-fun z$6 () Bool)
(declare-fun L1 () Bool)
(declare-fun z$2 () Bool)
(declare-fun z$243 () Bool)
(declare-fun z$24 () Bool)
(declare-fun z$26 () Bool)
(declare-fun z$27 () Bool)
(declare-fun z$36 () Bool)
(declare-fun z$38 () Bool)
(declare-fun z$46 () Bool)
(declare-fun z$344 () Bool)
(declare-fun z$345 () Bool)
(declare-fun z$427 () Bool)
(declare-fun z$291 () Bool)
(declare-fun z$442 () Bool)
(declare-fun z$444 () Bool)
(declare-fun z$424 () Bool)
(declare-fun z$441 () Bool)
(declare-fun z$443 () Bool)
(declare-fun L0 () Bool)
(declare-fun z$49 () Bool)
(declare-fun L0$next () Bool)
(declare-fun z$51 () Bool)
(declare-fun z$53 () Bool)
(declare-fun L1$next () Bool)
(declare-fun z$55 () Bool)
(declare-fun L2 () Bool)
(declare-fun z$57 () Bool)
(declare-fun L2$next () Bool)
(declare-fun z$59 () Bool)
(declare-fun Le_1_8_8 (utt8 utt8) Bool)
(declare-fun z$63 () Bool)
(declare-fun z$65 () Bool)
(declare-fun z$67 () Bool)
(declare-fun L3$next () Bool)
(declare-fun z$69 () Bool)
(declare-fun z$71 () Bool)
(declare-fun L4$next () Bool)
(declare-fun z$73 () Bool)
(declare-fun z$75 () Bool)
(declare-fun z$76 () Bool)
(declare-fun z$78 () Bool)
(declare-fun z$80 () Bool)
(declare-fun L5$next () Bool)
(declare-fun z$82 () Bool)
(declare-fun z$87 () Bool)
(declare-fun z$88 () Bool)
(declare-fun L6 () Bool)
(declare-fun z$90 () Bool)
(declare-fun z$92 () Bool)
(declare-fun L6$next () Bool)
(declare-fun z$94 () Bool)
(declare-fun z$97 () Bool)
(declare-fun z$99 () Bool)
(declare-fun z$101 () Bool)
(declare-fun z$103 () Bool)
(declare-fun z$105 () Bool)
(declare-fun z$4 () Bool)
(declare-fun z$107 () Bool)
(declare-fun z$109 () Bool)
(declare-fun z$111 () Bool)
(declare-fun z$10 () Bool)
(declare-fun z$113 () Bool)
(declare-fun z$12 () Bool)
(declare-fun z$115 () Bool)
(declare-fun z$117 () Bool)
(declare-fun z$119 () Bool)
(declare-fun z$120 () Bool)
(declare-fun z$122 () Bool)
(declare-fun z$124 () Bool)
(declare-fun z$126 () Bool)
(declare-fun z$128 () Bool)
(declare-fun z$130 () Bool)
(declare-fun z$132 () Bool)
(declare-fun z$134 () Bool)
(declare-fun z$136 () Bool)
(declare-fun z$138 () Bool)
(declare-fun z$140 () Bool)
(declare-fun z$142 () Bool)
(declare-fun z$144 () Bool)
(declare-fun z$146 () Bool)
(declare-fun z$148 () Bool)
(declare-fun z$150 () Bool)
(declare-fun z$152 () Bool)
(declare-fun z$154 () Bool)
(declare-fun z$156 () Bool)
(declare-fun z$158 () Bool)
(declare-fun z$160 () Bool)
(declare-fun z$162 () Bool)
(declare-fun z$164 () Bool)
(declare-fun z$166 () Bool)
(declare-fun z$168 () Bool)
(declare-fun z$170 () Bool)
(declare-fun z$172 () Bool)
(declare-fun z$174 () Bool)
(declare-fun z$176 () Bool)
(declare-fun z$178 () Bool)
(declare-fun z$180 () Bool)
(declare-fun z$182 () Bool)
(declare-fun z$184 () Bool)
(declare-fun z$186 () Bool)
(declare-fun z$188 () Bool)
(declare-fun z$190 () Bool)
(declare-fun z$192 () Bool)
(declare-fun z$194 () Bool)
(declare-fun z$196 () Bool)
(declare-fun z$198 () Bool)
(declare-fun z$200 () Bool)
(declare-fun LoneHot$next () Bool)
(declare-fun z$202 () Bool)
(declare-fun z$476 () Bool)
(declare-fun p$0 () Bool)
(declare-fun p$1 () Bool)
(declare-fun z$228 () Bool)
(declare-fun p$2 () Bool)
(declare-fun z$229 () Bool)
(declare-fun p$3 () Bool)
(declare-fun z$232 () Bool)
(declare-fun p$4 () Bool)
(declare-fun z$234 () Bool)
(declare-fun p$5 () Bool)
(declare-fun z$401 () Bool)
(declare-fun p$6 () Bool)
(declare-fun z$361 () Bool)
(declare-fun p$7 () Bool)
(assert
 (and (distinct z$n0s8 z$n2s8 z$n3s8 z$n5s8 z$n4s8 z$n1s8 z$n255s8 z$n6s8 z$n254s8) true))
(assert
 (let ((?x598 (Add_8_8_8 X Y)))
 (= z$84 ?x598)))
(assert
 (let (($x580 (= z$84 z$n4s8)))
 (= z$96 $x580)))
(assert
 (let (($x1223 (= X z$n3s8)))
 (= z$336 $x1223)))
(assert
 (= z$409 (and L5 LoneHot z$96 z$336)))
(assert
 (= z$410 (not z$409)))
(assert
 (= z$237 (and (distinct Y X) true)))
(assert
 (= z$421 (and L5 LoneHot z$96 z$237)))
(assert
 (= z$422 (not z$421)))
(assert
 (let (($x67 (not L4)))
 (= z$8 $x67)))
(assert
 (= z$281 (and (distinct X z$n0s8) true)))
(assert
 (= z$347 (and (distinct X z$n3s8) true)))
(assert
 (= z$375 (and z$281 z$347)))
(assert
 (= z$376 (not z$375)))
(assert
 (let (($x84 (= Y z$n0s8)))
 (= z$20 $x84)))
(assert
 (let (($x36 (not L7)))
 (= z$14 $x36)))
(assert
 (= z$205 (= prop z$14)))
(assert
 (= z$217 (not L7$next)))
(assert
 (= z$218 (= prop$next z$217)))
(assert
 (let (($x63 (not L3)))
 (= z$6 $x63)))
(assert
 (let (($x55 (not L1)))
 (= z$2 $x55)))
(assert
 (let ((?x364 (Add_8_8_8 X$next Y$next)))
 (= z$240 ?x364)))
(assert
 (let (($x367 (= z$240 z$n4s8)))
 (= z$243 $x367)))
(assert
 (let (($x92 (= a z$n0s8)))
 (= z$24 $x92)))
(assert
 (= z$26 (and (distinct c z$n0s8) true)))
(assert
 (= z$27 (and z$24 z$26)))
(assert
 (let ((?x103 (ite z$27 z$n2s8 c)))
 (= z$30 ?x103)))
(assert
 (let ((?x107 (ite L3 z$30 Y)))
 (= z$32 ?x107)))
(assert
 (let ((?x111 (ite LoneHot z$32 Y)))
 (= z$34 ?x111)))
(assert
 (let (($x115 (= Y$next z$34)))
 (= z$36 $x115)))
(assert
 (= z$38 (and (distinct a z$n0s8) true)))
(assert
 (let ((?x122 (ite z$38 z$n3s8 X)))
 (= z$40 ?x122)))
(assert
 (let ((?x126 (ite L1 z$40 X)))
 (= z$42 ?x126)))
(assert
 (let ((?x130 (ite LoneHot z$42 X)))
 (= z$44 ?x130)))
(assert
 (let (($x134 (= X$next z$44)))
 (= z$46 $x134)))
(assert
 (= z$344 (and z$336 z$20 z$6 z$2 z$243 z$36 z$46)))
(assert
 (= z$345 (not z$344)))
(assert
 (let (($x1236 (= X$next Y$next)))
 (= z$427 $x1236)))
(assert
 (let (($x492 (= Y$next z$n0s8)))
 (= z$291 $x492)))
(assert
 (= z$442 (and z$427 z$291 z$243)))
(assert
 (= z$444 (not z$442)))
(assert
 (let (($x1604 (= X Y)))
 (= z$424 $x1604)))
(assert
 (= z$441 (and z$424 z$20 z$96)))
(assert
 (= z$443 (not z$441)))
(assert
 (= z$49 (ite LoneHot false L0)))
(assert
 (= z$51 (= L0$next z$49)))
(assert
 (let (($x627 (ite LoneHot L0 L1)))
 (= z$53 $x627)))
(assert
 (= z$55 (= L1$next z$53)))
(assert
 (let (($x608 (ite LoneHot L1 L2)))
 (= z$57 $x608)))
(assert
 (= z$59 (= L2$next z$57)))
(assert
 (let (($x139 (Le_1_8_8 b z$n5s8)))
 (= z$63 $x139)))
(assert
 (= z$65 (and L2 z$63)))
(assert
 (let (($x614 (ite LoneHot z$65 L3)))
 (= z$67 $x614)))
(assert
 (= z$69 (= L3$next z$67)))
(assert
 (let (($x606 (ite LoneHot L3 L4)))
 (= z$71 $x606)))
(assert
 (= z$73 (= L4$next z$71)))
(assert
 (let (($x143 (not z$63)))
 (= z$75 $x143)))
(assert
 (= z$76 (and L2 z$75)))
(assert
 (let (($x150 (or L4 z$76)))
 (= z$78 $x150)))
(assert
 (let (($x154 (ite LoneHot z$78 L5)))
 (= z$80 $x154)))
(assert
 (= z$82 (= L5$next z$80)))
(assert
 (= z$87 (and (distinct z$84 z$n4s8) true)))
(assert
 (= z$88 (and L5 z$87)))
(assert
 (let (($x409 (or L6 z$88)))
 (= z$90 $x409)))
(assert
 (let (($x534 (ite LoneHot z$90 L6)))
 (= z$92 $x534)))
(assert
 (= z$94 (= L6$next z$92)))
(assert
 (= z$97 (and L5 z$96)))
(assert
 (let (($x571 (or L7 z$97)))
 (= z$99 $x571)))
(assert
 (let (($x568 (ite LoneHot z$99 L7)))
 (= z$101 $x568)))
(assert
 (= z$103 (= L7$next z$101)))
(assert
 (= z$105 (and L0 z$2)))
(assert
 (let (($x59 (not L2)))
 (= z$4 $x59)))
(assert
 (= z$107 (and z$105 z$4)))
(assert
 (= z$109 (and z$107 z$6)))
(assert
 (= z$111 (and z$109 z$8)))
(assert
 (let (($x71 (not L5)))
 (= z$10 $x71)))
(assert
 (= z$113 (and z$111 z$10)))
(assert
 (let (($x75 (not L6)))
 (= z$12 $x75)))
(assert
 (= z$115 (and z$113 z$12)))
(assert
 (= z$117 (and z$115 z$14)))
(assert
 (let (($x190 (not L0)))
 (= z$119 $x190)))
(assert
 (= z$120 (and z$119 L1)))
(assert
 (= z$122 (and z$120 z$4)))
(assert
 (= z$124 (and z$122 z$6)))
(assert
 (= z$126 (and z$124 z$8)))
(assert
 (= z$128 (and z$126 z$10)))
(assert
 (= z$130 (and z$128 z$12)))
(assert
 (= z$132 (and z$130 z$14)))
(assert
 (let (($x221 (or z$117 z$132)))
 (= z$134 $x221)))
(assert
 (= z$136 (and z$119 z$2)))
(assert
 (= z$138 (and z$136 L2)))
(assert
 (= z$140 (and z$138 z$6)))
(assert
 (= z$142 (and z$140 z$8)))
(assert
 (= z$144 (and z$142 z$10)))
(assert
 (= z$146 (and z$144 z$12)))
(assert
 (= z$148 (and z$146 z$14)))
(assert
 (let (($x253 (or z$134 z$148)))
 (= z$150 $x253)))
(assert
 (= z$152 (and z$136 z$4)))
(assert
 (= z$154 (and z$152 L3)))
(assert
 (= z$156 (and z$154 z$8)))
(assert
 (= z$158 (and z$156 z$10)))
(assert
 (= z$160 (and z$158 z$12)))
(assert
 (= z$162 (and z$160 z$14)))
(assert
 (let (($x281 (or z$150 z$162)))
 (= z$164 $x281)))
(assert
 (= z$166 (and z$152 z$6)))
(assert
 (= z$168 (and z$166 L4)))
(assert
 (= z$170 (and z$168 z$10)))
(assert
 (= z$172 (and z$170 z$12)))
(assert
 (= z$174 (and z$172 z$14)))
(assert
 (let (($x305 (or z$164 z$174)))
 (= z$176 $x305)))
(assert
 (= z$178 (and z$166 z$8)))
(assert
 (= z$180 (and z$178 L5)))
(assert
 (= z$182 (and z$180 z$12)))
(assert
 (= z$184 (and z$182 z$14)))
(assert
 (let (($x325 (or z$176 z$184)))
 (= z$186 $x325)))
(assert
 (= z$188 (and z$178 z$10)))
(assert
 (= z$190 (and z$188 L6)))
(assert
 (= z$192 (and z$190 z$14)))
(assert
 (let (($x341 (or z$186 z$192)))
 (= z$194 $x341)))
(assert
 (= z$196 (and z$188 z$12)))
(assert
 (= z$198 (and z$196 L7)))
(assert
 (let (($x353 (or z$194 z$198)))
 (= z$200 $x353)))
(assert
 (= z$202 (= LoneHot$next z$200)))
(assert
 (let (($x1650 (and z$410 z$422 z$8 z$376 z$20 z$205 prop z$218 z$345 z$444 z$443 z$36 z$46 z$51 z$55 z$59 z$69 z$73 z$82 z$94 z$103 z$202)))
 (= z$476 $x1650)))
(assert
 z$476)
(assert
 (=> p$0 L5$next))
(assert
 (let (($x45 (= z$217 (not L7$next))))
 (=> p$1 $x45)))
(assert
 (=> p$1 z$217))
(assert
 (=> p$2 (= z$228 (not L1$next))))
(assert
 (=> p$2 z$228))
(assert
 (=> p$3 (= z$229 (not L2$next))))
(assert
 (=> p$3 z$229))
(assert
 (=> p$4 (= z$232 (not L4$next))))
(assert
 (=> p$4 z$232))
(assert
 (=> p$5 (= z$234 (not L6$next))))
(assert
 (=> p$5 z$234))
(assert
 (=> p$6 (= z$401 (not LoneHot$next))))
(assert
 (=> p$6 z$401))
(assert
 (=> p$7 (= z$361 (and (distinct Y$next z$n0s8) true))))
(assert
 (=> p$7 z$361))
(check-sat)
(assert p$4)
(set-info :status sat)
(check-sat)
(exit)
