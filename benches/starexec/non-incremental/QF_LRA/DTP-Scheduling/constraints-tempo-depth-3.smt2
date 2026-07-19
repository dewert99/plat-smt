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
(declare-fun t_Goal_10 () Real)
(declare-fun t_C_N2_6 () Real)
(declare-fun t_B_N2_5 () Real)
(declare-fun t_C_N1_3 () Real)
(declare-fun t_B_N1_2 () Real)
(declare-fun t_A_N1_1 () Real)
(declare-fun t_A_N2_4 () Real)
(declare-fun t_A_N3_7 () Real)
(declare-fun t_B_N3_8 () Real)
(declare-fun t_C_N3_9 () Real)
(assert (let ((?v_5 (- t_Goal_10 t_C_N2_6)) (?v_4 (- t_Goal_10 t_B_N2_5)) (?v_2 (- t_Goal_10 t_C_N1_3)) (?v_1 (- t_Goal_10 t_B_N1_2)) (?v_0 (- t_Goal_10 t_A_N1_1)) (?v_3 (- t_Goal_10 t_A_N2_4)) (?v_6 (- t_Goal_10 t_A_N3_7)) (?v_7 (- t_Goal_10 t_B_N3_8)) (?v_20 (- t_Goal_10 t_C_N3_9)) (?v_15 (- t_B_N1_2 t_A_N1_1))) (let ((?v_14 (< ?v_15 5)) (?v_13 (- t_C_N1_3 t_B_N1_2))) (let ((?v_12 (< ?v_13 4)) (?v_11 (- t_B_N2_5 t_A_N2_4))) (let ((?v_10 (< ?v_11 5)) (?v_9 (- t_C_N2_6 t_B_N2_5))) (let ((?v_8 (< ?v_9 4)) (?v_17 (- t_B_N3_8 t_A_N3_7))) (let ((?v_16 (< ?v_17 5)) (?v_19 (- t_C_N3_9 t_B_N3_8))) (let ((?v_18 (< ?v_19 4)) (?v_29 (- t_A_N3_7 t_C_N2_6)) (?v_24 (- t_A_N2_4 t_C_N1_3)) (?v_21 (- t_A_N2_4 t_A_N1_1)) (?v_26 (- t_A_N3_7 t_A_N2_4))) (let ((?v_38 (< ?v_21 5)) (?v_22 (> ?v_15 1))) (let ((?v_37 (or ?v_38 ?v_22)) (?v_23 (< ?v_0 6)) (?v_25 (< (- t_C_N1_3 t_A_N1_1) 4))) (let ((?v_36 (or (< ?v_24 1) ?v_25)) (?v_35 (< ?v_26 5)) (?v_27 (> ?v_11 1))) (let ((?v_34 (or ?v_35 ?v_27)) (?v_28 (< ?v_3 6)) (?v_30 (< (- t_C_N2_6 t_A_N2_4) 4))) (let ((?v_33 (or (< ?v_29 1) ?v_30)) (?v_31 (> ?v_17 1))) (let ((?v_39 (or (< ?v_17 1) ?v_31)) (?v_32 (< ?v_6 6)) (?v_41 (- t_C_N3_9 t_A_N3_7))) (let ((?v_40 (< ?v_41 4))) (and (= St_spy_variable (+ 1 t_Init_0)) (>= t_Goal_10 t_Init_0) (>= (- t_C_N2_6 t_Init_0) 0) (>= ?v_5 1) (>= (- t_B_N2_5 t_Init_0) 0) (>= ?v_4 4) (>= (- t_C_N1_3 t_Init_0) 0) (>= ?v_2 1) (>= (- t_B_N1_2 t_Init_0) 0) (>= ?v_1 4) (>= (- t_A_N1_1 t_Init_0) 0) (>= ?v_0 5) (>= (- t_A_N2_4 t_Init_0) 0) (>= ?v_3 5) (>= (- t_A_N3_7 t_Init_0) 0) (>= ?v_6 5) (>= (- t_B_N3_8 t_Init_0) 0) (>= ?v_7 4) (>= (- t_C_N3_9 t_Init_0) 0) (>= ?v_20 1) ?v_14 (>= ?v_0 6) ?v_12 (>= ?v_1 5) (>= ?v_2 2) ?v_10 (>= ?v_3 6) ?v_8 (>= ?v_4 5) (>= ?v_5 2) ?v_16 (>= ?v_6 6) ?v_18 (>= ?v_7 5) ?v_8 ?v_8 (>= ?v_9 0) (>= ?v_29 1) ?v_10 ?v_10 (>= ?v_11 0) (>= (- t_A_N3_7 t_B_N2_5) 4) ?v_12 ?v_12 (>= ?v_13 0) (>= ?v_24 1) ?v_14 ?v_14 (>= ?v_15 0) (>= (- t_A_N2_4 t_B_N1_2) 4) (>= ?v_21 5) (>= ?v_26 5) ?v_16 (>= ?v_17 0) ?v_18 (>= ?v_19 0) (>= ?v_20 2) ?v_37 (or ?v_23 ?v_22) (or ?v_25 (< ?v_2 2)) (or ?v_22 ?v_23) ?v_36 ?v_34 (or ?v_28 ?v_27) (or ?v_30 (< ?v_5 2)) (or ?v_27 ?v_28) ?v_33 ?v_39 (or ?v_32 ?v_31) (or ?v_40 (< ?v_20 2)) (or ?v_31 ?v_32) (or ?v_27 (< ?v_11 1)) ?v_33 ?v_34 (or ?v_27 ?v_35) (or ?v_22 (< ?v_15 1)) ?v_36 ?v_37 (or ?v_22 ?v_38) ?v_39 (or ?v_40 (> ?v_41 4))))))))))))))))))
(check-sat)
(exit)
