(declare-sort ID)
(declare-const a0 ID)
(declare-const a1 ID)
(declare-const a2 ID)
(declare-const b0 ID)
(declare-const b1 ID)
(declare-const b2 ID)
(declare-const c0 ID)
(declare-const c1 ID)
(declare-const c2 ID)
(declare-const d0 ID)
(declare-const d1 ID)
(declare-const d2 ID)
(declare-const e0 ID)
;    a1    b1    c1    d1
;   /  \  /  \  /  \  /  \
; a0    b0    c0    d0    e0
;   \  /  \  /  \  /  \  /
;    a2    b2    c2    d2
(assert (! (not (= a0 e0)) :named ne))
(assert (! (or (and (= a0 a1) (= a1 b0)) (and (= a0 a2) (= a2 b0))) :named ab))
(assert (! (or (and (= b0 b1) (= b1 c0)) (and (= b0 b2) (= b2 c0))) :named bc))
(assert (! (or (and (= c0 c1) (= c1 d0)) (and (= c0 c2) (= c2 d0))) :named cd))
(assert (! (or (and (= d0 d1) (= d1 e0)) (and (= d0 d2) (= d2 e0))) :named de))
(check-sat)
(get-interpolants (and ne ab de) (and bc cd))
(get-interpolants (and ne ab bc) (and cd de))