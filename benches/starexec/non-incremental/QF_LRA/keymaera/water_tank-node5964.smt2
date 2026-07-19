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

 KeYmaera example: water_tank, node 5964 For more info see: No further information available.
|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun stuscore2dollarskuscore3 () Real)
(declare-fun yuscore2dollarskuscore3 () Real)
(assert (not (=> (and (and (and (= yuscore2dollarskuscore3 5) (= stuscore2dollarskuscore3 2)) (>= yuscore2dollarskuscore3 1)) (<= yuscore2dollarskuscore3 12)) (or (or (= stuscore2dollarskuscore3 1) (= stuscore2dollarskuscore3 3)) (>= yuscore2dollarskuscore3 5)))))
(check-sat)
(exit)
