(set-info :smt-lib-version 2.6)
(set-logic QF_LRA)
(set-info :source |
TLP-GP automated DTP to SMT-LIB encoding for planning
by F.Maris and P.Regnier, IRIT - Universite Paul Sabatier, Toulouse

|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun St_spy_variable () Real)
(declare-fun t_Init_0 () Real)
(declare-fun t_Goal_4 () Real)
(declare-fun t_C_rb_ga1_gc1_3 () Real)
(declare-fun t_A_ra_ga2_gb1_1 () Real)
(declare-fun t_B_ra_rb_gb2_2 () Real)
(declare-fun t_A_ra_ga1_gb1_1 () Real)
(declare-fun t_B_ra_rb_gb1_2 () Real)
(declare-fun t_C_rb_ga1_gc2_3 () Real)
(assert (let ((?v_5 (- t_Goal_4 t_C_rb_ga1_gc1_3)) (?v_6 (- t_Goal_4 t_A_ra_ga2_gb1_1)) (?v_10 (- t_Goal_4 t_B_ra_rb_gb2_2)) (?v_0 (- t_Goal_4 t_A_ra_ga1_gb1_1)) (?v_1 (- t_Goal_4 t_B_ra_rb_gb1_2)) (?v_13 (- t_Goal_4 t_C_rb_ga1_gc2_3)) (?v_11 (- t_B_ra_rb_gb1_2 t_A_ra_ga1_gb1_1))) (let ((?v_7 (< ?v_11 5)) (?v_9 (- t_B_ra_rb_gb2_2 t_A_ra_ga1_gb1_1))) (let ((?v_8 (< ?v_9 5)) (?v_12 (- t_C_rb_ga1_gc2_3 t_B_ra_rb_gb1_2))) (let ((?v_2 (< ?v_12 4)) (?v_4 (- t_C_rb_ga1_gc1_3 t_B_ra_rb_gb1_2))) (let ((?v_3 (< ?v_4 4)) (?v_14 (- t_A_ra_ga2_gb1_1 t_A_ra_ga1_gb1_1))) (let ((?v_30 (< ?v_14 5)) (?v_29 (> ?v_14 5)) (?v_21 (< ?v_11 1)) (?v_15 (> ?v_11 1))) (let ((?v_31 (or ?v_21 ?v_15)) (?v_19 (< ?v_0 6)) (?v_16 (- t_A_ra_ga1_gb1_1 t_A_ra_ga2_gb1_1))) (let ((?v_27 (> ?v_16 5)) (?v_33 (- t_C_rb_ga1_gc2_3 t_A_ra_ga1_gb1_1))) (let ((?v_32 (< ?v_33 4)) (?v_25 (- t_C_rb_ga1_gc1_3 t_A_ra_ga1_gb1_1))) (let ((?v_26 (< ?v_25 4)) (?v_17 (- t_B_ra_rb_gb2_2 t_B_ra_rb_gb1_2))) (let ((?v_35 (< ?v_17 4)) (?v_34 (> ?v_17 4))) (let ((?v_20 (or ?v_35 ?v_34)) (?v_18 (- t_B_ra_rb_gb1_2 t_B_ra_rb_gb2_2))) (let ((?v_24 (> ?v_18 4)) (?v_23 (- t_B_ra_rb_gb1_2 t_A_ra_ga2_gb1_1))) (let ((?v_22 (> ?v_23 1)) (?v_28 (< ?v_23 1)) (?v_36 (or ?v_32 (> ?v_33 4)))) (and (= St_spy_variable (+ 1 t_Init_0)) (>= t_Goal_4 t_Init_0) (>= (- t_C_rb_ga1_gc1_3 t_Init_0) 0) (>= ?v_5 1) (>= (- t_A_ra_ga2_gb1_1 t_Init_0) 0) (>= ?v_6 5) (>= (- t_B_ra_rb_gb2_2 t_Init_0) 0) (>= ?v_10 4) (>= (- t_A_ra_ga1_gb1_1 t_Init_0) 0) (>= ?v_0 5) (>= (- t_B_ra_rb_gb1_2 t_Init_0) 0) (>= ?v_1 4) (>= (- t_C_rb_ga1_gc2_3 t_Init_0) 0) (>= ?v_13 1) ?v_7 ?v_8 (>= ?v_0 6) ?v_2 ?v_3 (>= ?v_1 5) ?v_2 ?v_3 ?v_3 (>= ?v_4 0) (>= ?v_5 2) (>= ?v_6 6) ?v_7 ?v_8 ?v_8 (>= ?v_9 0) (>= ?v_10 5) ?v_7 (>= ?v_11 0) ?v_2 (>= ?v_12 0) (>= ?v_13 2) (or ?v_30 ?v_29) ?v_31 (or ?v_19 ?v_15) (or ?v_27 (< ?v_16 5)) (or ?v_32 (< ?v_13 2)) (or ?v_26 (< ?v_5 2)) ?v_20 (or ?v_24 (< ?v_18 4)) (or ?v_15 ?v_19) (or ?v_22 (< ?v_6 6)) ?v_20 (or ?v_15 ?v_21) (or ?v_22 ?v_28) (or ?v_24 (< (- t_C_rb_ga1_gc1_3 t_B_ra_rb_gb2_2) 4)) (or (> ?v_25 4) ?v_26) (or (< ?v_23 5) ?v_27) (or (< (- t_B_ra_rb_gb2_2 t_A_ra_ga2_gb1_1) 5) ?v_27) (or ?v_28 ?v_22) (or ?v_29 ?v_30) ?v_31 ?v_36 (or (< (- t_C_rb_ga1_gc2_3 t_B_ra_rb_gb2_2) 4) ?v_24) (or ?v_34 ?v_35) ?v_31 ?v_36))))))))))))))))
(check-sat)
(exit)
