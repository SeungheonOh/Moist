(declare-const $u$120 Int)
(assert (let ((|moist.dag.0| (= $u$120 10))) (ite (and |moist.dag.0| (= 1 1)) true (and (not |moist.dag.0|) (= 0 1)))))
(check-sat-using (or-else (try-for (then simplify propagate-values smt) 1000) (par-or (then simplify ctx-solver-simplify smt) smt)))
(get-model)
