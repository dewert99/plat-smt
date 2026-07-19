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
(declare-fun t_A_ra_ga_gb_1 () Real)
(declare-fun t_B_ra_rb_gb_2 () Real)
(declare-fun t_C_rb_ga_gc_3 () Real)
(assert (let ((?v_0 (- t_Goal_4 t_A_ra_ga_gb_1)) (?v_1 (- t_Goal_4 t_B_ra_rb_gb_2)) (?v_6 (- t_Goal_4 t_C_rb_ga_gc_3)) (?v_3 (- t_B_ra_rb_gb_2 t_A_ra_ga_gb_1))) (let ((?v_2 (< ?v_3 5)) (?v_5 (- t_C_rb_ga_gc_3 t_B_ra_rb_gb_2))) (let ((?v_4 (< ?v_5 4)) (?v_7 (> ?v_3 1))) (let ((?v_9 (or (< ?v_3 1) ?v_7)) (?v_8 (< ?v_0 6)) (?v_11 (- t_C_rb_ga_gc_3 t_A_ra_ga_gb_1))) (let ((?v_10 (< ?v_11 4))) (and (= St_spy_variable (+ 1 t_Init_0)) (>= t_Goal_4 t_Init_0) (>= (- t_A_ra_ga_gb_1 t_Init_0) 0) (>= ?v_0 5) (>= (- t_B_ra_rb_gb_2 t_Init_0) 0) (>= ?v_1 4) (>= (- t_C_rb_ga_gc_3 t_Init_0) 0) (>= ?v_6 1) ?v_2 (>= ?v_0 6) ?v_4 (>= ?v_1 5) ?v_2 (>= ?v_3 0) ?v_4 (>= ?v_5 0) (>= ?v_6 2) ?v_9 (or ?v_8 ?v_7) (or ?v_10 (< ?v_6 2)) (or ?v_7 ?v_8) ?v_9 (or ?v_10 (> ?v_11 4)))))))))
(check-sat)
(exit)
