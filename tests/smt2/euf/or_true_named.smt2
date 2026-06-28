(assert (or true (! false :named f)))
(assert f)
(check-sat)