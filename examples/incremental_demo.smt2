; Demonstrates the core incremental-reuse claim through a real .smt2 file,
; not just Rust-level unit tests.
(set-logic UF)
(declare-fun Knows (U U) Bool)
(declare-sort U 0)

(push 1)
(assert (forall ((x U)) (exists ((y U)) (Knows x y))))
(check-sat)
(pop 1)

(push 1)
(assert (forall ((x U)) (exists ((y U)) (Knows x y))))
(check-sat)
(pop 1)

; A genuinely unsatisfiable one, to check UNSAT still works after the
; reuse machinery has been exercised above.
(declare-fun P (U) Bool)
(assert (forall ((x U)) (and (P x) (not (P x)))))
(check-sat)
