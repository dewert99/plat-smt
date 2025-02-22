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

id: cache_coherence_three
query-maker: "Z3"
query-time: 0.685000 ms
query-class: abstract
query-category: assume
query-type: mus_min
status: sat
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")

; 
(set-info :status sat)
(declare-sort utt2 0)
(declare-sort utt3 0)
(declare-sort utt32 0)
(declare-sort utt31 0)
(declare-fun z$n1s2 () utt2)
(declare-fun z$n2s2 () utt2)
(declare-fun z$n0s2 () utt2)
(declare-fun z$n4s3 () utt3)
(declare-fun z$n3s3 () utt3)
(declare-fun z$n1s3 () utt3)
(declare-fun z$n2s3 () utt3)
(declare-fun z$n5s3 () utt3)
(declare-fun z$n0s3 () utt3)
(declare-fun z$n0s32 () utt32)
(declare-fun z$n1s32 () utt32)
(declare-fun pcacheB.next_state () utt2)
(declare-fun pcacheA.next_state () utt2)
(declare-fun pcacheB.state () utt2)
(declare-fun pcacheA.state () utt2)
(declare-fun z$372 () utt32)
(declare-fun Concat_32_1_31 (Bool utt31) utt32)
(declare-fun z$n0s31 () utt31)
(declare-fun z$980 () utt32)
(declare-fun z$377 () utt32)
(declare-fun z$985 () utt32)
(declare-fun pcacheC.state () utt2)
(declare-fun z$385 () utt32)
(declare-fun z$990 () utt32)
(declare-fun pcacheA.state$next () utt2)
(declare-fun bus_arbiter.shared_snoop () utt3)
(declare-fun z$230 () utt32)
(declare-fun z$233 () utt32)
(declare-fun z$235 () utt32)
(declare-fun z$267 () utt32)
(declare-fun z$269 () utt32)
(declare-fun z$278 () utt32)
(declare-fun z$280 () utt32)
(declare-fun z$282 () utt32)
(declare-fun pcacheC.next_state () utt2)
(declare-fun z$312 () utt32)
(declare-fun z$314 () utt32)
(declare-fun z$325 () utt32)
(declare-fun z$327 () utt32)
(declare-fun z$329 () utt32)
(declare-fun z$405 () utt2)
(declare-fun z$407 () utt2)
(declare-fun z$409 () utt2)
(declare-fun z$411 () utt2)
(declare-fun z$413 () utt2)
(declare-fun z$415 () utt2)
(declare-fun z$417 () utt2)
(declare-fun z$419 () utt2)
(declare-fun z$421 () utt2)
(declare-fun z$423 () utt2)
(declare-fun z$425 () utt2)
(declare-fun z$427 () utt2)
(declare-fun z$429 () utt2)
(declare-fun z$431 () utt2)
(declare-fun z$433 () utt2)
(declare-fun z$435 () utt2)
(declare-fun z$437 () utt2)
(declare-fun z$439 () utt2)
(declare-fun z$441 () utt2)
(declare-fun z$443 () utt2)
(declare-fun z$445 () utt2)
(declare-fun z$447 () utt2)
(declare-fun z$449 () utt2)
(declare-fun z$451 () utt2)
(declare-fun z$453 () utt2)
(declare-fun z$455 () utt2)
(declare-fun z$457 () utt2)
(declare-fun pcacheA.next_state$next () utt2)
(declare-fun pcacheB.state$next () utt2)
(declare-fun z$634 () utt2)
(declare-fun z$636 () utt2)
(declare-fun z$638 () utt2)
(declare-fun z$640 () utt2)
(declare-fun z$642 () utt2)
(declare-fun z$644 () utt2)
(declare-fun z$646 () utt2)
(declare-fun z$648 () utt2)
(declare-fun z$650 () utt2)
(declare-fun z$652 () utt2)
(declare-fun z$654 () utt2)
(declare-fun z$656 () utt2)
(declare-fun z$658 () utt2)
(declare-fun z$660 () utt2)
(declare-fun z$662 () utt2)
(declare-fun z$664 () utt2)
(declare-fun z$666 () utt2)
(declare-fun z$668 () utt2)
(declare-fun z$670 () utt2)
(declare-fun z$672 () utt2)
(declare-fun z$674 () utt2)
(declare-fun z$676 () utt2)
(declare-fun z$678 () utt2)
(declare-fun z$680 () utt2)
(declare-fun z$682 () utt2)
(declare-fun pcacheB.next_state$next () utt2)
(declare-fun pcacheC.state$next () utt2)
(declare-fun z$856 () utt2)
(declare-fun z$858 () utt2)
(declare-fun z$860 () utt2)
(declare-fun z$862 () utt2)
(declare-fun z$864 () utt2)
(declare-fun z$866 () utt2)
(declare-fun z$868 () utt2)
(declare-fun z$870 () utt2)
(declare-fun z$872 () utt2)
(declare-fun z$874 () utt2)
(declare-fun z$876 () utt2)
(declare-fun z$878 () utt2)
(declare-fun z$880 () utt2)
(declare-fun z$882 () utt2)
(declare-fun z$884 () utt2)
(declare-fun z$886 () utt2)
(declare-fun z$888 () utt2)
(declare-fun z$890 () utt2)
(declare-fun z$892 () utt2)
(declare-fun z$894 () utt2)
(declare-fun z$896 () utt2)
(declare-fun z$898 () utt2)
(declare-fun z$900 () utt2)
(declare-fun z$902 () utt2)
(declare-fun z$904 () utt2)
(declare-fun pcacheC.next_state$next () utt2)
(declare-fun z$1009 () utt32)
(declare-fun z$1014 () utt32)
(declare-fun z$1018 () utt32)
(declare-fun z$1023 () utt32)
(declare-fun z$1029 () utt32)
(declare-fun z$1034 () utt32)
(declare-fun pcacheC.snoop_type () utt3)
(declare-fun z$110 () utt3)
(declare-fun pcacheB.snoop_type () utt3)
(declare-fun z$112 () utt3)
(declare-fun pcacheA.snoop_type () utt3)
(declare-fun z$114 () utt3)
(declare-fun bus_arbiter.shared_snoop$next () utt3)
(declare-fun z$1161 () Bool)
(declare-fun z$1078 () Bool)
(declare-fun bus_arbiter.bus_ackB () Bool)
(declare-fun z$3 () Bool)
(declare-fun bus_arbiter.is_snoop () Bool)
(declare-fun z$9 () Bool)
(declare-fun bus_arbiter.bus_ackC () Bool)
(declare-fun z$5 () Bool)
(declare-fun z$1050 () Bool)
(declare-fun z$1046 () Bool)
(declare-fun bus_arbiter.bus_ackA () Bool)
(declare-fun z$1 () Bool)
(declare-fun z$125 () Bool)
(declare-fun z$362 () Bool)
(declare-fun Extract_1_0_0_32 (utt32) Bool)
(declare-fun z$374 () Bool)
(declare-fun z$984 () Bool)
(declare-fun z$376 () Bool)
(declare-fun z$380 () Bool)
(declare-fun z$379 () Bool)
(declare-fun z$987 () Bool)
(declare-fun z$988 () Bool)
(declare-fun z$384 () Bool)
(declare-fun z$388 () Bool)
(declare-fun z$387 () Bool)
(declare-fun z$992 () Bool)
(declare-fun z$993 () Bool)
(declare-fun prop () Bool)
(declare-fun z$995 () Bool)
(declare-fun z$195 () Bool)
(declare-fun z$197 () Bool)
(declare-fun z$199 () Bool)
(declare-fun z$200 () Bool)
(declare-fun z$201 () Bool)
(declare-fun z$202 () Bool)
(declare-fun bus_arbiter.invalidate () Bool)
(declare-fun z$7 () Bool)
(declare-fun z$215 () Bool)
(declare-fun z$216 () Bool)
(declare-fun z$217 () Bool)
(declare-fun z$22 () Bool)
(declare-fun z$12 () Bool)
(declare-fun z$219 () Bool)
(declare-fun z$221 () Bool)
(declare-fun z$222 () Bool)
(declare-fun z$224 () Bool)
(declare-fun z$226 () Bool)
(declare-fun z$228 () Bool)
(declare-fun z$242 () Bool)
(declare-fun z$243 () Bool)
(declare-fun z$237 () Bool)
(declare-fun z$245 () Bool)
(declare-fun z$246 () Bool)
(declare-fun z$46 () Bool)
(declare-fun z$248 () Bool)
(declare-fun z$250 () Bool)
(declare-fun z$252 () Bool)
(declare-fun z$254 () Bool)
(declare-fun z$214 () Bool)
(declare-fun z$255 () Bool)
(declare-fun z$257 () Bool)
(declare-fun z$259 () Bool)
(declare-fun z$261 () Bool)
(declare-fun z$263 () Bool)
(declare-fun z$265 () Bool)
(declare-fun z$273 () Bool)
(declare-fun z$274 () Bool)
(declare-fun z$271 () Bool)
(declare-fun z$276 () Bool)
(declare-fun z$287 () Bool)
(declare-fun z$288 () Bool)
(declare-fun z$284 () Bool)
(declare-fun z$290 () Bool)
(declare-fun z$292 () Bool)
(declare-fun z$293 () Bool)
(declare-fun z$67 () Bool)
(declare-fun z$295 () Bool)
(declare-fun z$297 () Bool)
(declare-fun z$299 () Bool)
(declare-fun z$301 () Bool)
(declare-fun z$302 () Bool)
(declare-fun z$304 () Bool)
(declare-fun z$306 () Bool)
(declare-fun z$308 () Bool)
(declare-fun z$310 () Bool)
(declare-fun z$318 () Bool)
(declare-fun z$319 () Bool)
(declare-fun z$316 () Bool)
(declare-fun z$321 () Bool)
(declare-fun z$323 () Bool)
(declare-fun z$334 () Bool)
(declare-fun z$335 () Bool)
(declare-fun z$331 () Bool)
(declare-fun z$337 () Bool)
(declare-fun z$339 () Bool)
(declare-fun z$352 () Bool)
(declare-fun z$163 () Bool)
(declare-fun z$370 () Bool)
(declare-fun z$382 () Bool)
(declare-fun z$390 () Bool)
(declare-fun z$392 () Bool)
(declare-fun z$459 () Bool)
(declare-fun z$599 () Bool)
(declare-fun z$601 () Bool)
(declare-fun z$605 () Bool)
(declare-fun z$567 () Bool)
(declare-fun z$622 () Bool)
(declare-fun z$684 () Bool)
(declare-fun z$821 () Bool)
(declare-fun z$823 () Bool)
(declare-fun z$827 () Bool)
(declare-fun z$789 () Bool)
(declare-fun z$844 () Bool)
(declare-fun z$906 () Bool)
(declare-fun z$1008 () Bool)
(declare-fun z$1012 () Bool)
(declare-fun z$1011 () Bool)
(declare-fun z$1016 () Bool)
(declare-fun z$1017 () Bool)
(declare-fun z$1021 () Bool)
(declare-fun z$1020 () Bool)
(declare-fun z$1025 () Bool)
(declare-fun z$1026 () Bool)
(declare-fun z$1028 () Bool)
(declare-fun z$1032 () Bool)
(declare-fun z$1031 () Bool)
(declare-fun z$1036 () Bool)
(declare-fun z$1037 () Bool)
(declare-fun prop$next () Bool)
(declare-fun z$1039 () Bool)
(declare-fun pcacheC.inv_out () Bool)
(declare-fun pcacheC.bus_req () Bool)
(declare-fun z$83 () Bool)
(declare-fun pcacheB.inv_out () Bool)
(declare-fun pcacheB.bus_req () Bool)
(declare-fun z$85 () Bool)
(declare-fun pcacheA.inv_out () Bool)
(declare-fun pcacheA.bus_req () Bool)
(declare-fun z$87 () Bool)
(declare-fun bus_arbiter.invalidate$next () Bool)
(declare-fun z$89 () Bool)
(declare-fun z$92 () Bool)
(declare-fun bus_arbiter.bus_ackA$next () Bool)
(declare-fun z$94 () Bool)
(declare-fun z$96 () Bool)
(declare-fun z$98 () Bool)
(declare-fun bus_arbiter.bus_ackB$next () Bool)
(declare-fun z$100 () Bool)
(declare-fun z$102 () Bool)
(declare-fun z$104 () Bool)
(declare-fun z$106 () Bool)
(declare-fun bus_arbiter.bus_ackC$next () Bool)
(declare-fun z$108 () Bool)
(declare-fun z$116 () Bool)
(declare-fun z$118 () Bool)
(declare-fun z$120 () Bool)
(declare-fun bus_arbiter.is_snoop$next () Bool)
(declare-fun z$122 () Bool)
(declare-fun z$39 () Bool)
(declare-fun z$1319 () Bool)
(declare-fun p$0 () Bool)
(declare-fun z$1056 () Bool)
(declare-fun p$1 () Bool)
(declare-fun z$1058 () Bool)
(declare-fun p$2 () Bool)
(assert
 (and (distinct z$n0s2 z$n2s2 z$n1s2) true))
(assert
 (and (distinct z$n0s3 z$n5s3 z$n2s3 z$n1s3 z$n3s3 z$n4s3) true))
(assert
 (and (distinct z$n1s32 z$n0s32) true))
(assert
 (= z$1161 (and (distinct pcacheB.next_state z$n1s2) true)))
(assert
 (= z$1078 (and (distinct pcacheA.next_state z$n1s2) true)))
(assert
 (= z$3 (not bus_arbiter.bus_ackB)))
(assert
 (let (($x227 (not bus_arbiter.is_snoop)))
 (= z$9 $x227)))
(assert
 (= z$5 (not bus_arbiter.bus_ackC)))
(assert
 (= z$1050 (and (distinct pcacheB.state z$n1s2) true)))
(assert
 (= z$1046 (and (distinct pcacheA.state z$n1s2) true)))
(assert
 (= z$1 (not bus_arbiter.bus_ackA)))
(assert
 (let (($x44 (= pcacheA.state z$n1s2)))
 (= z$125 $x44)))
(assert
 (let ((?x47 (ite z$125 z$n1s32 z$n0s32)))
 (= z$372 ?x47)))
(assert
 (= z$362 (ite z$125 true false)))
(assert
 (let (($x56 (Extract_1_0_0_32 z$372)))
 (= z$374 $x56)))
(assert
 (= z$374 z$362))
(assert
 (let ((?x62 (Concat_32_1_31 z$374 z$n0s31)))
 (= z$980 ?x62)))
(assert
 (= z$984 (and (distinct z$980 z$n1s32) true)))
(assert
 (let (($x70 (= pcacheB.state z$n1s2)))
 (= z$376 $x70)))
(assert
 (let ((?x73 (ite z$376 z$n1s32 z$n0s32)))
 (= z$377 ?x73)))
(assert
 (= z$380 (ite z$376 true false)))
(assert
 (let (($x80 (Extract_1_0_0_32 z$377)))
 (= z$379 $x80)))
(assert
 (= z$379 z$380))
(assert
 (let ((?x85 (Concat_32_1_31 z$379 z$n0s31)))
 (= z$985 ?x85)))
(assert
 (let (($x89 (= z$985 z$n1s32)))
 (= z$987 $x89)))
(assert
 (let (($x92 (or z$984 z$987)))
 (= z$988 $x92)))
(assert
 (let (($x97 (= pcacheC.state z$n1s2)))
 (= z$384 $x97)))
(assert
 (let ((?x100 (ite z$384 z$n1s32 z$n0s32)))
 (= z$385 ?x100)))
(assert
 (= z$388 (ite z$384 true false)))
(assert
 (let (($x107 (Extract_1_0_0_32 z$385)))
 (= z$387 $x107)))
(assert
 (= z$387 z$388))
(assert
 (let ((?x112 (Concat_32_1_31 z$387 z$n0s31)))
 (= z$990 ?x112)))
(assert
 (let (($x116 (= z$990 z$n1s32)))
 (= z$992 $x116)))
(assert
 (let (($x119 (or z$988 z$992)))
 (= z$993 $x119)))
(assert
 (= z$995 (= prop z$993)))
(assert
 (let (($x351 (= pcacheA.state$next pcacheA.next_state)))
 (= z$195 $x351)))
(assert
 (let (($x355 (or z$9 bus_arbiter.bus_ackA)))
 (= z$197 $x355)))
(assert
 (let (($x359 (= bus_arbiter.shared_snoop z$n3s3)))
 (= z$199 $x359)))
(assert
 (let (($x362 (= bus_arbiter.shared_snoop z$n4s3)))
 (= z$200 $x362)))
(assert
 (let (($x365 (= bus_arbiter.shared_snoop z$n5s3)))
 (= z$201 $x365)))
(assert
 (let (($x368 (or z$199 z$200 z$201)))
 (= z$202 $x368)))
(assert
 (= z$7 (not bus_arbiter.invalidate)))
(assert
 (let (($x372 (= bus_arbiter.shared_snoop z$n1s3)))
 (= z$215 $x372)))
(assert
 (let (($x375 (= pcacheA.next_state z$n1s2)))
 (= z$216 $x375)))
(assert
 (let (($x378 (or z$215 z$216)))
 (= z$217 $x378)))
(assert
 (let (($x248 (= pcacheA.next_state z$n0s2)))
 (= z$22 $x248)))
(assert
 (let (($x231 (= bus_arbiter.shared_snoop z$n0s3)))
 (= z$12 $x231)))
(assert
 (let (($x382 (or z$12 z$215)))
 (= z$219 $x382)))
(assert
 (= z$221 (not z$219)))
(assert
 (= z$222 (and z$22 z$221)))
(assert
 (let (($x393 (or z$200 z$201)))
 (= z$224 $x393)))
(assert
 (= z$226 (and z$216 z$224)))
(assert
 (let (($x401 (or z$222 z$226)))
 (= z$228 $x401)))
(assert
 (let ((?x405 (Concat_32_1_31 z$1 z$n0s31)))
 (= z$230 ?x405)))
(assert
 (let ((?x409 (ite z$228 z$230 z$n0s32)))
 (= z$233 ?x409)))
(assert
 (let ((?x413 (ite z$217 z$n1s32 z$233)))
 (= z$235 ?x413)))
(assert
 (= z$242 (ite z$228 z$1 false)))
(assert
 (= z$243 (ite z$217 true z$242)))
(assert
 (let (($x423 (Extract_1_0_0_32 z$235)))
 (= z$237 $x423)))
(assert
 (= z$237 z$243))
(assert
 (let (($x428 (= pcacheB.next_state z$n1s2)))
 (= z$245 $x428)))
(assert
 (let (($x431 (or z$215 z$245)))
 (= z$246 $x431)))
(assert
 (let (($x286 (= pcacheB.next_state z$n0s2)))
 (= z$46 $x286)))
(assert
 (= z$248 (and z$46 z$221)))
(assert
 (= z$250 (and z$245 z$224)))
(assert
 (let (($x443 (or z$248 z$250)))
 (= z$252 $x443)))
(assert
 (let (($x447 (= pcacheA.next_state z$n2s2)))
 (= z$254 $x447)))
(assert
 (let (($x450 (= bus_arbiter.shared_snoop z$n2s3)))
 (= z$214 $x450)))
(assert
 (let (($x453 (or z$214 z$200)))
 (= z$255 $x453)))
(assert
 (let (($x457 (or z$255 z$201)))
 (= z$257 $x457)))
(assert
 (= z$259 (and z$215 z$216)))
(assert
 (let (($x465 (or z$257 z$259)))
 (= z$261 $x465)))
(assert
 (= z$263 (and z$199 z$22)))
(assert
 (let (($x473 (or z$261 z$263)))
 (= z$265 $x473)))
(assert
 (let ((?x477 (ite z$265 z$n1s32 z$n0s32)))
 (= z$267 ?x477)))
(assert
 (let ((?x481 (ite z$254 z$n0s32 z$267)))
 (= z$269 ?x481)))
(assert
 (= z$273 (ite z$265 true false)))
(assert
 (= z$274 (ite z$254 false z$273)))
(assert
 (let (($x491 (Extract_1_0_0_32 z$269)))
 (= z$271 $x491)))
(assert
 (= z$271 z$274))
(assert
 (let (($x496 (ite z$271 z$1 z$3)))
 (= z$276 $x496)))
(assert
 (let ((?x500 (Concat_32_1_31 z$276 z$n0s31)))
 (= z$278 ?x500)))
(assert
 (let ((?x504 (ite z$252 z$278 z$n0s32)))
 (= z$280 ?x504)))
(assert
 (let ((?x508 (ite z$246 z$n1s32 z$280)))
 (= z$282 ?x508)))
(assert
 (= z$287 (ite z$252 z$276 false)))
(assert
 (= z$288 (ite z$246 true z$287)))
(assert
 (let (($x518 (Extract_1_0_0_32 z$282)))
 (= z$284 $x518)))
(assert
 (= z$284 z$288))
(assert
 (let (($x523 (or z$237 z$284)))
 (= z$290 $x523)))
(assert
 (let (($x527 (= pcacheC.next_state z$n1s2)))
 (= z$292 $x527)))
(assert
 (let (($x530 (or z$215 z$292)))
 (= z$293 $x530)))
(assert
 (let (($x324 (= pcacheC.next_state z$n0s2)))
 (= z$67 $x324)))
(assert
 (= z$295 (and z$67 z$221)))
(assert
 (= z$297 (and z$292 z$224)))
(assert
 (let (($x542 (or z$295 z$297)))
 (= z$299 $x542)))
(assert
 (let (($x546 (= pcacheB.next_state z$n2s2)))
 (= z$301 $x546)))
(assert
 (let (($x549 (or z$271 z$301)))
 (= z$302 $x549)))
(assert
 (= z$304 (and z$215 z$245)))
(assert
 (let (($x557 (or z$257 z$304)))
 (= z$306 $x557)))
(assert
 (= z$308 (and z$199 z$46)))
(assert
 (let (($x565 (or z$306 z$308)))
 (= z$310 $x565)))
(assert
 (let ((?x569 (ite z$310 z$n1s32 z$n0s32)))
 (= z$312 ?x569)))
(assert
 (let ((?x573 (ite z$302 z$n0s32 z$312)))
 (= z$314 ?x573)))
(assert
 (= z$318 (ite z$310 true false)))
(assert
 (= z$319 (ite z$302 false z$318)))
(assert
 (let (($x583 (Extract_1_0_0_32 z$314)))
 (= z$316 $x583)))
(assert
 (= z$316 z$319))
(assert
 (let (($x588 (ite z$316 z$276 z$5)))
 (= z$321 $x588)))
(assert
 (let (($x592 (ite z$271 z$276 z$321)))
 (= z$323 $x592)))
(assert
 (let ((?x596 (Concat_32_1_31 z$323 z$n0s31)))
 (= z$325 ?x596)))
(assert
 (let ((?x600 (ite z$299 z$325 z$n0s32)))
 (= z$327 ?x600)))
(assert
 (let ((?x604 (ite z$293 z$n1s32 z$327)))
 (= z$329 ?x604)))
(assert
 (= z$334 (ite z$299 z$323 false)))
(assert
 (= z$335 (ite z$293 true z$334)))
(assert
 (let (($x614 (Extract_1_0_0_32 z$329)))
 (= z$331 $x614)))
(assert
 (= z$331 z$335))
(assert
 (let (($x619 (or z$290 z$331)))
 (= z$337 $x619)))
(assert
 (= z$339 (not z$337)))
(assert
 (let ((?x626 (ite z$339 z$n0s2 z$n1s2)))
 (= z$405 ?x626)))
(assert
 (let ((?x630 (ite z$7 z$405 pcacheA.state)))
 (= z$407 ?x630)))
(assert
 (let ((?x634 (ite bus_arbiter.invalidate z$n0s2 pcacheA.state)))
 (= z$409 ?x634)))
(assert
 (let ((?x638 (ite z$7 z$405 z$409)))
 (= z$411 ?x638)))
(assert
 (let ((?x642 (ite z$200 z$407 z$411)))
 (= z$413 ?x642)))
(assert
 (let ((?x646 (ite z$201 z$407 z$413)))
 (= z$415 ?x646)))
(assert
 (let ((?x650 (ite z$339 z$n0s2 pcacheA.state)))
 (= z$417 ?x650)))
(assert
 (let ((?x654 (ite z$7 z$417 pcacheA.state)))
 (= z$419 ?x654)))
(assert
 (let ((?x658 (ite z$215 z$n0s2 pcacheA.state)))
 (= z$421 ?x658)))
(assert
 (let ((?x662 (ite z$214 z$419 z$421)))
 (= z$423 ?x662)))
(assert
 (let ((?x666 (ite z$202 z$415 z$423)))
 (= z$425 ?x666)))
(assert
 (let ((?x670 (ite z$1 pcacheA.state z$425)))
 (= z$427 ?x670)))
(assert
 (= z$352 (and bus_arbiter.is_snoop z$1)))
(assert
 (let ((?x678 (ite bus_arbiter.invalidate z$n2s2 pcacheA.state)))
 (= z$429 ?x678)))
(assert
 (let (($x682 (= pcacheA.state z$n0s2)))
 (= z$163 $x682)))
(assert
 (let ((?x685 (ite z$7 z$n1s2 z$n2s2)))
 (= z$431 ?x685)))
(assert
 (let ((?x689 (ite z$163 z$431 pcacheA.state)))
 (= z$433 ?x689)))
(assert
 (let ((?x693 (ite z$125 z$429 z$433)))
 (= z$435 ?x693)))
(assert
 (let ((?x697 (ite z$200 z$435 z$433)))
 (= z$437 ?x697)))
(assert
 (let ((?x701 (ite z$201 z$435 z$437)))
 (= z$439 ?x701)))
(assert
 (let ((?x705 (ite z$125 z$n2s2 pcacheA.state)))
 (= z$441 ?x705)))
(assert
 (let ((?x709 (ite z$215 z$441 pcacheA.state)))
 (= z$443 ?x709)))
(assert
 (let ((?x713 (ite z$214 z$433 z$443)))
 (= z$445 ?x713)))
(assert
 (let ((?x717 (ite z$202 z$439 z$445)))
 (= z$447 ?x717)))
(assert
 (= z$370 (and z$214 z$125)))
(assert
 (= z$382 (and z$374 z$379)))
(assert
 (= z$390 (and z$382 z$387)))
(assert
 (= z$392 (not z$390)))
(assert
 (let ((?x736 (ite z$392 z$n0s2 pcacheA.state)))
 (= z$449 ?x736)))
(assert
 (let ((?x740 (ite z$370 z$449 pcacheA.next_state)))
 (= z$451 ?x740)))
(assert
 (let ((?x744 (ite z$237 z$447 z$451)))
 (= z$453 ?x744)))
(assert
 (let ((?x748 (ite z$352 z$453 pcacheA.next_state)))
 (= z$455 ?x748)))
(assert
 (let ((?x752 (ite z$197 z$427 z$455)))
 (= z$457 ?x752)))
(assert
 (let (($x756 (= pcacheA.next_state$next z$457)))
 (= z$459 $x756)))
(assert
 (let (($x759 (= pcacheB.state$next pcacheB.next_state)))
 (= z$599 $x759)))
(assert
 (let (($x763 (or z$9 bus_arbiter.bus_ackB)))
 (= z$601 $x763)))
(assert
 (let ((?x767 (ite z$7 z$405 pcacheB.state)))
 (= z$634 ?x767)))
(assert
 (let ((?x771 (ite bus_arbiter.invalidate z$n0s2 pcacheB.state)))
 (= z$636 ?x771)))
(assert
 (let ((?x775 (ite z$7 z$405 z$636)))
 (= z$638 ?x775)))
(assert
 (let ((?x779 (ite z$200 z$634 z$638)))
 (= z$640 ?x779)))
(assert
 (let ((?x783 (ite z$201 z$634 z$640)))
 (= z$642 ?x783)))
(assert
 (let ((?x787 (ite z$339 z$n0s2 pcacheB.state)))
 (= z$644 ?x787)))
(assert
 (let ((?x791 (ite z$7 z$644 pcacheB.state)))
 (= z$646 ?x791)))
(assert
 (let ((?x795 (ite z$215 z$n0s2 pcacheB.state)))
 (= z$648 ?x795)))
(assert
 (let ((?x799 (ite z$214 z$646 z$648)))
 (= z$650 ?x799)))
(assert
 (let ((?x803 (ite z$202 z$642 z$650)))
 (= z$652 ?x803)))
(assert
 (let ((?x807 (ite z$3 pcacheB.state z$652)))
 (= z$654 ?x807)))
(assert
 (= z$605 (and bus_arbiter.is_snoop z$3)))
(assert
 (let ((?x815 (ite bus_arbiter.invalidate z$n2s2 pcacheB.state)))
 (= z$656 ?x815)))
(assert
 (let (($x819 (= pcacheB.state z$n0s2)))
 (= z$567 $x819)))
(assert
 (let ((?x822 (ite z$567 z$431 pcacheB.state)))
 (= z$658 ?x822)))
(assert
 (let ((?x826 (ite z$376 z$656 z$658)))
 (= z$660 ?x826)))
(assert
 (let ((?x830 (ite z$200 z$660 z$658)))
 (= z$662 ?x830)))
(assert
 (let ((?x834 (ite z$201 z$660 z$662)))
 (= z$664 ?x834)))
(assert
 (let ((?x838 (ite z$376 z$n2s2 pcacheB.state)))
 (= z$666 ?x838)))
(assert
 (let ((?x842 (ite z$215 z$666 pcacheB.state)))
 (= z$668 ?x842)))
(assert
 (let ((?x846 (ite z$214 z$658 z$668)))
 (= z$670 ?x846)))
(assert
 (let ((?x850 (ite z$202 z$664 z$670)))
 (= z$672 ?x850)))
(assert
 (= z$622 (and z$214 z$376)))
(assert
 (let ((?x858 (ite z$392 z$n0s2 pcacheB.state)))
 (= z$674 ?x858)))
(assert
 (let ((?x862 (ite z$622 z$674 pcacheB.next_state)))
 (= z$676 ?x862)))
(assert
 (let ((?x866 (ite z$284 z$672 z$676)))
 (= z$678 ?x866)))
(assert
 (let ((?x870 (ite z$605 z$678 pcacheB.next_state)))
 (= z$680 ?x870)))
(assert
 (let ((?x874 (ite z$601 z$654 z$680)))
 (= z$682 ?x874)))
(assert
 (let (($x878 (= pcacheB.next_state$next z$682)))
 (= z$684 $x878)))
(assert
 (let (($x881 (= pcacheC.state$next pcacheC.next_state)))
 (= z$821 $x881)))
(assert
 (let (($x885 (or z$9 bus_arbiter.bus_ackC)))
 (= z$823 $x885)))
(assert
 (let ((?x889 (ite z$7 z$405 pcacheC.state)))
 (= z$856 ?x889)))
(assert
 (let ((?x893 (ite bus_arbiter.invalidate z$n0s2 pcacheC.state)))
 (= z$858 ?x893)))
(assert
 (let ((?x897 (ite z$7 z$405 z$858)))
 (= z$860 ?x897)))
(assert
 (let ((?x901 (ite z$200 z$856 z$860)))
 (= z$862 ?x901)))
(assert
 (let ((?x905 (ite z$201 z$856 z$862)))
 (= z$864 ?x905)))
(assert
 (let ((?x909 (ite z$339 z$n0s2 pcacheC.state)))
 (= z$866 ?x909)))
(assert
 (let ((?x913 (ite z$7 z$866 pcacheC.state)))
 (= z$868 ?x913)))
(assert
 (let ((?x917 (ite z$215 z$n0s2 pcacheC.state)))
 (= z$870 ?x917)))
(assert
 (let ((?x921 (ite z$214 z$868 z$870)))
 (= z$872 ?x921)))
(assert
 (let ((?x925 (ite z$202 z$864 z$872)))
 (= z$874 ?x925)))
(assert
 (let ((?x929 (ite z$5 pcacheC.state z$874)))
 (= z$876 ?x929)))
(assert
 (= z$827 (and bus_arbiter.is_snoop z$5)))
(assert
 (let ((?x937 (ite bus_arbiter.invalidate z$n2s2 pcacheC.state)))
 (= z$878 ?x937)))
(assert
 (let (($x941 (= pcacheC.state z$n0s2)))
 (= z$789 $x941)))
(assert
 (let ((?x944 (ite z$789 z$431 pcacheC.state)))
 (= z$880 ?x944)))
(assert
 (let ((?x948 (ite z$384 z$878 z$880)))
 (= z$882 ?x948)))
(assert
 (let ((?x952 (ite z$200 z$882 z$880)))
 (= z$884 ?x952)))
(assert
 (let ((?x956 (ite z$201 z$882 z$884)))
 (= z$886 ?x956)))
(assert
 (let ((?x960 (ite z$384 z$n2s2 pcacheC.state)))
 (= z$888 ?x960)))
(assert
 (let ((?x964 (ite z$215 z$888 pcacheC.state)))
 (= z$890 ?x964)))
(assert
 (let ((?x968 (ite z$214 z$880 z$890)))
 (= z$892 ?x968)))
(assert
 (let ((?x972 (ite z$202 z$886 z$892)))
 (= z$894 ?x972)))
(assert
 (= z$844 (and z$214 z$384)))
(assert
 (let ((?x980 (ite z$392 z$n0s2 pcacheC.state)))
 (= z$896 ?x980)))
(assert
 (let ((?x984 (ite z$844 z$896 pcacheC.next_state)))
 (= z$898 ?x984)))
(assert
 (let ((?x988 (ite z$331 z$894 z$898)))
 (= z$900 ?x988)))
(assert
 (let ((?x992 (ite z$827 z$900 pcacheC.next_state)))
 (= z$902 ?x992)))
(assert
 (let ((?x996 (ite z$823 z$876 z$902)))
 (= z$904 ?x996)))
(assert
 (let (($x1000 (= pcacheC.next_state$next z$904)))
 (= z$906 $x1000)))
(assert
 (let (($x128 (= pcacheA.state$next z$n1s2)))
 (= z$1008 $x128)))
(assert
 (let ((?x131 (ite z$1008 z$n1s32 z$n0s32)))
 (= z$1009 ?x131)))
(assert
 (= z$1012 (ite z$1008 true false)))
(assert
 (let (($x138 (Extract_1_0_0_32 z$1009)))
 (= z$1011 $x138)))
(assert
 (= z$1011 z$1012))
(assert
 (let ((?x143 (Concat_32_1_31 z$1011 z$n0s31)))
 (= z$1014 ?x143)))
(assert
 (= z$1016 (and (distinct z$1014 z$n1s32) true)))
(assert
 (let (($x151 (= pcacheB.state$next z$n1s2)))
 (= z$1017 $x151)))
(assert
 (let ((?x154 (ite z$1017 z$n1s32 z$n0s32)))
 (= z$1018 ?x154)))
(assert
 (= z$1021 (ite z$1017 true false)))
(assert
 (let (($x161 (Extract_1_0_0_32 z$1018)))
 (= z$1020 $x161)))
(assert
 (= z$1020 z$1021))
(assert
 (let ((?x166 (Concat_32_1_31 z$1020 z$n0s31)))
 (= z$1023 ?x166)))
(assert
 (let (($x170 (= z$1023 z$n1s32)))
 (= z$1025 $x170)))
(assert
 (let (($x173 (or z$1016 z$1025)))
 (= z$1026 $x173)))
(assert
 (let (($x178 (= pcacheC.state$next z$n1s2)))
 (= z$1028 $x178)))
(assert
 (let ((?x181 (ite z$1028 z$n1s32 z$n0s32)))
 (= z$1029 ?x181)))
(assert
 (= z$1032 (ite z$1028 true false)))
(assert
 (let (($x188 (Extract_1_0_0_32 z$1029)))
 (= z$1031 $x188)))
(assert
 (= z$1031 z$1032))
(assert
 (let ((?x193 (Concat_32_1_31 z$1031 z$n0s31)))
 (= z$1034 ?x193)))
(assert
 (let (($x197 (= z$1034 z$n1s32)))
 (= z$1036 $x197)))
(assert
 (let (($x200 (or z$1026 z$1036)))
 (= z$1037 $x200)))
(assert
 (= z$1039 (= prop$next z$1037)))
(assert
 (= z$83 (ite pcacheC.bus_req pcacheC.inv_out false)))
(assert
 (let (($x1119 (ite pcacheB.bus_req pcacheB.inv_out z$83)))
 (= z$85 $x1119)))
(assert
 (let (($x1007 (ite pcacheA.bus_req pcacheA.inv_out z$85)))
 (= z$87 $x1007)))
(assert
 (= z$89 (= bus_arbiter.invalidate$next z$87)))
(assert
 (= z$92 (ite pcacheA.bus_req true false)))
(assert
 (= z$94 (= bus_arbiter.bus_ackA$next z$92)))
(assert
 (= z$96 (ite pcacheB.bus_req true false)))
(assert
 (= z$98 (ite pcacheA.bus_req false z$96)))
(assert
 (= z$100 (= bus_arbiter.bus_ackB$next z$98)))
(assert
 (= z$102 (ite pcacheC.bus_req true false)))
(assert
 (= z$104 (ite pcacheB.bus_req false z$102)))
(assert
 (= z$106 (ite pcacheA.bus_req false z$104)))
(assert
 (= z$108 (= bus_arbiter.bus_ackC$next z$106)))
(assert
 (let ((?x1194 (ite pcacheC.bus_req pcacheC.snoop_type z$n0s3)))
 (= z$110 ?x1194)))
(assert
 (let ((?x1365 (ite pcacheB.bus_req pcacheB.snoop_type z$110)))
 (= z$112 ?x1365)))
(assert
 (let ((?x1286 (ite pcacheA.bus_req pcacheA.snoop_type z$112)))
 (= z$114 ?x1286)))
(assert
 (let (($x1353 (= bus_arbiter.shared_snoop$next z$114)))
 (= z$116 $x1353)))
(assert
 (= z$118 (ite pcacheB.bus_req true z$102)))
(assert
 (= z$120 (ite pcacheA.bus_req true z$118)))
(assert
 (= z$122 (= bus_arbiter.is_snoop$next z$120)))
(assert
 (= z$39 (not pcacheB.bus_req)))
(assert
 (let (($x1645 (and z$1161 z$1078 z$3 z$9 z$5 z$1050 z$1050 z$1046 z$1046 z$1 z$995 prop z$195 z$459 z$599 z$684 z$821 z$906 z$1039 z$89 z$94 z$100 z$108 z$116 z$122 z$39)))
 (= z$1319 $x1645)))
(assert
 z$1319)
(assert
 (=> p$0 bus_arbiter.is_snoop$next))
(assert
 (=> p$1 (= z$1056 (not bus_arbiter.bus_ackA$next))))
(assert
 (=> p$1 z$1056))
(assert
 (=> p$2 (= z$1058 (not bus_arbiter.bus_ackC$next))))
(assert
 (=> p$2 z$1058))
(check-sat)
(assert p$1)
(assert p$0)
(set-info :status sat)
(check-sat)
(exit)
