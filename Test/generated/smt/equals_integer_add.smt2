(declare-const $u$120 Int)
(assert (= 10 (+ 5 $u$120)))
(check-sat-using (or-else (try-for (then simplify propagate-values smt) 1000) (par-or (then simplify ctx-solver-simplify smt) smt)))
(get-model)
