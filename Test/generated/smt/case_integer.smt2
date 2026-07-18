(declare-const $u$120 Int)
(assert (and (>= $u$120 0) (= $u$120 2)))
(check-sat-using (or-else (try-for (then simplify propagate-values smt) 1000) (par-or (then simplify ctx-solver-simplify smt) smt)))
(get-model)
