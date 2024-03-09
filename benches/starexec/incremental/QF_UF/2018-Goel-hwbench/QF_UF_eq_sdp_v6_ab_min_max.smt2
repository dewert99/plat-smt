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

id: eq_sdp_v6
query-maker: "Z3"
query-time: 0.385000 ms
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
(declare-fun z$n16s8 () utt8)
(declare-fun z$n4s8 () utt8)
(declare-fun z$n248s8 () utt8)
(declare-fun z$n252s8 () utt8)
(declare-fun z$n10s8 () utt8)
(declare-fun z$n8s8 () utt8)
(declare-fun z$n5s8 () utt8)
(declare-fun z$n2s8 () utt8)
(declare-fun z$n1s8 () utt8)
(declare-fun z$n0s8 () utt8)
(declare-fun im.p1_a () utt8)
(declare-fun im.p1_b () utt8)
(declare-fun im.p1_c () utt8)
(declare-fun im.p2_c () utt8)
(declare-fun im.p2_m () utt8)
(declare-fun im.p3_n () utt8)
(declare-fun ra1 () utt8)
(declare-fun ra2 () utt8)
(declare-fun ra3 () utt8)
(declare-fun rb1 () utt8)
(declare-fun rb2 () utt8)
(declare-fun rb3 () utt8)
(declare-fun rc1 () utt8)
(declare-fun rc2 () utt8)
(declare-fun rc3 () utt8)
(declare-fun Add_8_8_8 (utt8 utt8) utt8)
(declare-fun z$140 () utt8)
(declare-fun Sub_8_8_8 (utt8 utt8) utt8)
(declare-fun z$142 () utt8)
(declare-fun z$144 () utt8)
(declare-fun z$146 () utt8)
(declare-fun z$148 () utt8)
(declare-fun z$150 () utt8)
(declare-fun ra3$next () utt8)
(declare-fun rb3$next () utt8)
(declare-fun z$168 () utt8)
(declare-fun z$170 () utt8)
(declare-fun z$172 () utt8)
(declare-fun rc3$next () utt8)
(declare-fun z$174 () utt8)
(declare-fun z$176 () utt8)
(declare-fun z$178 () utt8)
(declare-fun im.p3_n$next () utt8)
(declare-fun z$44 () utt8)
(declare-fun rb2$next () utt8)
(declare-fun z$57 () utt8)
(declare-fun rc2$next () utt8)
(declare-fun z$84 () utt8)
(declare-fun ra2$next () utt8)
(declare-fun BitWiseAnd_8_8_8 (utt8 utt8) utt8)
(declare-fun z$110 () utt8)
(declare-fun z$113 () utt8)
(declare-fun z$115 () utt8)
(declare-fun z$117 () utt8)
(declare-fun z$119 () utt8)
(declare-fun im.p2_m$next () utt8)
(declare-fun z$123 () utt8)
(declare-fun im.p2_c$next () utt8)
(declare-fun im.p1_a$next () utt8)
(declare-fun z$350 () utt8)
(declare-fun z$294 () utt8)
(declare-fun ctl_b1 () Bool)
(declare-fun z$1 () Bool)
(declare-fun ctl_b2 () Bool)
(declare-fun z$3 () Bool)
(declare-fun ctl_b3 () Bool)
(declare-fun z$5 () Bool)
(declare-fun z$8 () Bool)
(declare-fun z$10 () Bool)
(declare-fun z$12 () Bool)
(declare-fun im.p1_ctl_2 () Bool)
(declare-fun z$14 () Bool)
(declare-fun z$16 () Bool)
(declare-fun im.p2_ctl_2 () Bool)
(declare-fun z$18 () Bool)
(declare-fun z$20 () Bool)
(declare-fun z$22 () Bool)
(declare-fun z$24 () Bool)
(declare-fun z$26 () Bool)
(declare-fun z$28 () Bool)
(declare-fun z$30 () Bool)
(declare-fun z$32 () Bool)
(declare-fun z$34 () Bool)
(declare-fun z$36 () Bool)
(declare-fun z$38 () Bool)
(declare-fun z$40 () Bool)
(declare-fun Extract_1_0_0_8 (utt8) Bool)
(declare-fun z$138 () Bool)
(declare-fun z$152 () Bool)
(declare-fun prop () Bool)
(declare-fun z$153 () Bool)
(declare-fun z$166 () Bool)
(declare-fun ctl_b3$next () Bool)
(declare-fun z$180 () Bool)
(declare-fun prop$next () Bool)
(declare-fun z$181 () Bool)
(declare-fun z$197 () Bool)
(declare-fun z$198 () Bool)
(declare-fun z$199 () Bool)
(declare-fun z$200 () Bool)
(declare-fun z$202 () Bool)
(declare-fun z$191 () Bool)
(declare-fun z$196 () Bool)
(declare-fun z$201 () Bool)
(declare-fun z$234 () Bool)
(declare-fun z$236 () Bool)
(declare-fun z$233 () Bool)
(declare-fun z$235 () Bool)
(declare-fun im.reset () Bool)
(declare-fun z$46 () Bool)
(declare-fun z$59 () Bool)
(declare-fun z$71 () Bool)
(declare-fun ctl_b2$next () Bool)
(declare-fun z$73 () Bool)
(declare-fun z$86 () Bool)
(declare-fun z$105 () Bool)
(declare-fun im.p2_ctl_2$next () Bool)
(declare-fun z$107 () Bool)
(declare-fun z$112 () Bool)
(declare-fun z$121 () Bool)
(declare-fun z$125 () Bool)
(declare-fun z$361 () Bool)
(declare-fun z$386 () Bool)
(declare-fun z$387 () Bool)
(declare-fun z$389 () Bool)
(declare-fun z$385 () Bool)
(declare-fun z$388 () Bool)
(declare-fun z$404 () Bool)
(declare-fun p$0 () Bool)
(declare-fun z$307 () Bool)
(declare-fun z$411 () Bool)
(declare-fun p$1 () Bool)
(assert
 (and (distinct z$n0s8 z$n1s8 z$n2s8 z$n5s8 z$n8s8 z$n10s8 z$n252s8 z$n248s8 z$n4s8 z$n16s8) true))
(assert
 (let (($x251 (not ctl_b1)))
 (= z$1 $x251)))
(assert
 (= z$3 (not ctl_b2)))
(assert
 (= z$5 (not ctl_b3)))
(assert
 (let (($x301 (= im.p1_a z$n0s8)))
 (= z$8 $x301)))
(assert
 (let (($x318 (= im.p1_b z$n0s8)))
 (= z$10 $x318)))
(assert
 (let (($x329 (= im.p1_c z$n0s8)))
 (= z$12 $x329)))
(assert
 (let (($x340 (not im.p1_ctl_2)))
 (= z$14 $x340)))
(assert
 (let (($x344 (= im.p2_c z$n0s8)))
 (= z$16 $x344)))
(assert
 (= z$18 (not im.p2_ctl_2)))
(assert
 (let (($x24 (= im.p2_m z$n0s8)))
 (= z$20 $x24)))
(assert
 (let (($x159 (= im.p3_n z$n0s8)))
 (= z$22 $x159)))
(assert
 (let (($x240 (= ra1 z$n0s8)))
 (= z$24 $x240)))
(assert
 (let (($x308 (= ra2 z$n0s8)))
 (= z$26 $x308)))
(assert
 (let (($x150 (= ra3 z$n0s8)))
 (= z$28 $x150)))
(assert
 (let (($x1161 (= rb1 z$n0s8)))
 (= z$30 $x1161)))
(assert
 (let (($x1095 (= rb2 z$n0s8)))
 (= z$32 $x1095)))
(assert
 (let (($x147 (= rb3 z$n0s8)))
 (= z$34 $x147)))
(assert
 (let (($x1099 (= rc1 z$n0s8)))
 (= z$36 $x1099)))
(assert
 (let (($x1054 (= rc2 z$n0s8)))
 (= z$38 $x1054)))
(assert
 (let (($x433 (= rc3 z$n0s8)))
 (= z$40 $x433)))
(assert
 (let (($x181 (Extract_1_0_0_8 ra3)))
 (= z$138 $x181)))
(assert
 (let ((?x259 (Add_8_8_8 ra3 rb3)))
 (= z$140 ?x259)))
(assert
 (let ((?x429 (Sub_8_8_8 ra3 rb3)))
 (= z$142 ?x429)))
(assert
 (let ((?x408 (ite z$138 z$140 z$142)))
 (= z$144 ?x408)))
(assert
 (let ((?x1113 (Add_8_8_8 z$144 rc3)))
 (= z$146 ?x1113)))
(assert
 (let ((?x1062 (Sub_8_8_8 z$144 rc3)))
 (= z$148 ?x1062)))
(assert
 (let ((?x1046 (ite ctl_b3 z$146 z$148)))
 (= z$150 ?x1046)))
(assert
 (let (($x1021 (= z$150 im.p3_n)))
 (= z$152 $x1021)))
(assert
 (= z$153 (= prop z$152)))
(assert
 (let (($x382 (Extract_1_0_0_8 ra3$next)))
 (= z$166 $x382)))
(assert
 (let ((?x903 (Add_8_8_8 ra3$next rb3$next)))
 (= z$168 ?x903)))
(assert
 (let ((?x513 (Sub_8_8_8 ra3$next rb3$next)))
 (= z$170 ?x513)))
(assert
 (let ((?x879 (ite z$166 z$168 z$170)))
 (= z$172 ?x879)))
(assert
 (let ((?x1497 (Add_8_8_8 z$172 rc3$next)))
 (= z$174 ?x1497)))
(assert
 (let ((?x852 (Sub_8_8_8 z$172 rc3$next)))
 (= z$176 ?x852)))
(assert
 (let ((?x17 (ite ctl_b3$next z$174 z$176)))
 (= z$178 ?x17)))
(assert
 (let (($x44 (= z$178 im.p3_n$next)))
 (= z$180 $x44)))
(assert
 (= z$181 (= prop$next z$180)))
(assert
 (= z$197 (and (distinct z$170 z$n0s8) true)))
(assert
 (let (($x111 (= rb3$next z$n0s8)))
 (= z$198 $x111)))
(assert
 (let (($x115 (= ra3$next z$n0s8)))
 (= z$199 $x115)))
(assert
 (= z$200 (and z$197 z$198 z$199)))
(assert
 (= z$202 (not z$200)))
(assert
 (= z$191 (and (distinct z$142 z$n0s8) true)))
(assert
 (= z$196 (and z$191 z$34 z$28)))
(assert
 (= z$201 (not z$196)))
(assert
 (= z$234 (and z$166 z$199)))
(assert
 (= z$236 (not z$234)))
(assert
 (= z$233 (and z$138 z$28)))
(assert
 (= z$235 (not z$233)))
(assert
 (let ((?x1177 (ite im.reset z$n0s8 rb1)))
 (= z$44 ?x1177)))
(assert
 (let (($x437 (= rb2$next z$44)))
 (= z$46 $x437)))
(assert
 (let ((?x1190 (ite im.reset z$n0s8 rc1)))
 (= z$57 ?x1190)))
(assert
 (let (($x1032 (= rc2$next z$57)))
 (= z$59 $x1032)))
(assert
 (= z$71 (ite im.reset false ctl_b1)))
(assert
 (= z$73 (= ctl_b2$next z$71)))
(assert
 (let ((?x847 (ite im.reset z$n0s8 ra1)))
 (= z$84 ?x847)))
(assert
 (let (($x1703 (= ra2$next z$84)))
 (= z$86 $x1703)))
(assert
 (= z$105 (ite im.reset false im.p1_ctl_2)))
(assert
 (= z$107 (= im.p2_ctl_2$next z$105)))
(assert
 (let ((?x1632 (BitWiseAnd_8_8_8 im.p1_a z$n1s8)))
 (= z$110 ?x1632)))
(assert
 (let (($x523 (= z$110 z$n1s8)))
 (= z$112 $x523)))
(assert
 (let ((?x937 (Add_8_8_8 im.p1_a im.p1_b)))
 (= z$113 ?x937)))
(assert
 (let ((?x799 (Sub_8_8_8 im.p1_a im.p1_b)))
 (= z$115 ?x799)))
(assert
 (let ((?x1705 (ite z$112 z$113 z$115)))
 (= z$117 ?x1705)))
(assert
 (let ((?x1224 (ite im.reset z$n0s8 z$117)))
 (= z$119 ?x1224)))
(assert
 (let (($x893 (= im.p2_m$next z$119)))
 (= z$121 $x893)))
(assert
 (let ((?x889 (ite im.reset z$n0s8 im.p1_c)))
 (= z$123 ?x889)))
(assert
 (let (($x885 (= im.p2_c$next z$123)))
 (= z$125 $x885)))
(assert
 (let ((?x2199 (BitWiseAnd_8_8_8 im.p1_a$next z$n1s8)))
 (= z$350 ?x2199)))
(assert
 (let (($x1674 (= z$350 z$n1s8)))
 (= z$361 $x1674)))
(assert
 (let (($x1667 (= im.p1_a$next z$n0s8)))
 (= z$386 $x1667)))
(assert
 (= z$387 (and z$361 z$386)))
(assert
 (= z$389 (not z$387)))
(assert
 (= z$385 (and z$112 z$8)))
(assert
 (= z$388 (not z$385)))
(assert
 (let (($x2204 (and z$1 z$3 z$5 z$8 z$10 z$12 z$14 z$16 z$18 z$20 z$22 z$24 z$26 z$28 z$30 z$32 z$34 z$36 z$38 z$40 z$153 prop z$181 z$202 z$201 z$236 z$235 z$46 z$59 z$73 z$86 z$107 z$121 z$125 z$389 z$388)))
 (= z$404 $x2204)))
(assert
 z$404)
(assert
 (let ((?x596 (Sub_8_8_8 im.p2_m$next im.p2_c$next)))
 (let (($x1494 (= z$294 ?x596)))
 (=> p$0 $x1494))))
(assert
 (=> p$0 (= z$307 (and (distinct z$294 im.p2_c$next) true))))
(assert
 (=> p$0 z$307))
(assert
 (=> p$1 (= z$411 (= im.p2_c$next im.p2_m$next))))
(assert
 (=> p$1 z$411))
(check-sat)
(assert p$1)
(set-info :status sat)
(check-sat)
(exit)