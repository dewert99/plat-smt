(set-info :smt-lib-version 2.6)
(set-logic QF_LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 17126 For more info see: No further information available.
|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun yuscore2dollarskuscore30 () Real)
(declare-fun xuscore2dollarskuscore22 () Real)
(declare-fun stuscore2dollarskuscore30 () Real)
(assert (not (=> (and (and (and (and (= yuscore2dollarskuscore30 5) (= stuscore2dollarskuscore30 2)) (>= yuscore2dollarskuscore30 1)) (<= yuscore2dollarskuscore30 12)) (>= yuscore2dollarskuscore30 (- 5 (* 2 xuscore2dollarskuscore22)))) (or (= stuscore2dollarskuscore30 1) (>= yuscore2dollarskuscore30 5)))))
(check-sat)
(exit)
