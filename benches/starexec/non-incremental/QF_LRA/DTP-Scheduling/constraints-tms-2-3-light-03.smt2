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
(declare-fun t_Goal_6 () Real)
(declare-fun t_TREAT_CERAMIC2_p2_3 () Real)
(declare-fun t_BAKE_CERAMIC2_p2_k2_2 () Real)
(declare-fun t_TREAT_CERAMIC1_p1_3 () Real)
(declare-fun t_FIRE_KILN2_k2_1 () Real)
(declare-fun t_BAKE_CERAMIC1_p1_k2_2 () Real)
(declare-fun t_MAKE_STRUCTURE_p1_p2_4 () Real)
(declare-fun t_BAKE_STRUCTURE_p1_p2_k1_5 () Real)
(declare-fun t_FIRE_KILN1_k1_1 () Real)
(declare-fun t_BAKE_CERAMIC3_p3_k1_2 () Real)
(assert (let ((?v_6 (- t_Goal_6 t_BAKE_STRUCTURE_p1_p2_k1_5)) (?v_9 (- t_Goal_6 t_BAKE_CERAMIC3_p3_k1_2)) (?v_0 (- t_TREAT_CERAMIC2_p2_3 t_BAKE_CERAMIC2_p2_k2_2)) (?v_4 (- t_BAKE_CERAMIC1_p1_k2_2 t_FIRE_KILN2_k2_1))) (let ((?v_3 (<= ?v_4 5)) (?v_1 (- t_BAKE_CERAMIC2_p2_k2_2 t_FIRE_KILN2_k2_1)) (?v_2 (- t_TREAT_CERAMIC1_p1_3 t_BAKE_CERAMIC1_p1_k2_2)) (?v_8 (- t_BAKE_CERAMIC3_p3_k1_2 t_FIRE_KILN1_k1_1))) (let ((?v_7 (<= ?v_8 3)) (?v_5 (- t_BAKE_STRUCTURE_p1_p2_k1_5 t_FIRE_KILN1_k1_1))) (and (= St_spy_variable (+ 1 t_Init_0)) (>= t_Goal_6 t_Init_0) (>= (- t_TREAT_CERAMIC2_p2_3 t_Init_0) 0) (>= (- t_Goal_6 t_TREAT_CERAMIC2_p2_3) 2) (>= (- t_BAKE_CERAMIC2_p2_k2_2 t_Init_0) 0) (>= (- t_Goal_6 t_BAKE_CERAMIC2_p2_k2_2) 10) (>= (- t_TREAT_CERAMIC1_p1_3 t_Init_0) 0) (>= (- t_Goal_6 t_TREAT_CERAMIC1_p1_3) 3) (>= (- t_FIRE_KILN2_k2_1 t_Init_0) 0) (>= (- t_Goal_6 t_FIRE_KILN2_k2_1) 20) (>= (- t_BAKE_CERAMIC1_p1_k2_2 t_Init_0) 0) (>= (- t_Goal_6 t_BAKE_CERAMIC1_p1_k2_2) 15) (>= (- t_MAKE_STRUCTURE_p1_p2_4 t_Init_0) 0) (>= (- t_Goal_6 t_MAKE_STRUCTURE_p1_p2_4) 1) (>= (- t_BAKE_STRUCTURE_p1_p2_k1_5 t_Init_0) 0) (>= ?v_6 3) (>= (- t_FIRE_KILN1_k1_1 t_Init_0) 0) (>= (- t_Goal_6 t_FIRE_KILN1_k1_1) 8) (>= (- t_BAKE_CERAMIC3_p3_k1_2 t_Init_0) 0) (>= ?v_9 5) (<= ?v_0 8) (< ?v_0 8) (>= ?v_0 0) (>= (- t_MAKE_STRUCTURE_p1_p2_4 t_TREAT_CERAMIC2_p2_3) 2) ?v_3 (<= ?v_1 10) (< ?v_1 10) (>= ?v_1 0) (>= (- t_MAKE_STRUCTURE_p1_p2_4 t_BAKE_CERAMIC2_p2_k2_2) 10) (<= ?v_2 12) (< ?v_2 12) (>= ?v_2 0) (>= (- t_MAKE_STRUCTURE_p1_p2_4 t_TREAT_CERAMIC1_p1_3) 3) ?v_3 (>= ?v_4 0) (>= (- t_MAKE_STRUCTURE_p1_p2_4 t_BAKE_CERAMIC1_p1_k2_2) 15) (>= (- t_BAKE_STRUCTURE_p1_p2_k1_5 t_MAKE_STRUCTURE_p1_p2_4) 1) ?v_7 (<= ?v_5 5) (< ?v_5 5) (>= ?v_5 0) (>= ?v_6 4) ?v_7 (>= ?v_8 0) (>= ?v_9 6))))))
(check-sat)
(exit)
