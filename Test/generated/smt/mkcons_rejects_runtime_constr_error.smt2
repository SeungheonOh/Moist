(assert true)
(check-sat-using (or-else (try-for (then simplify propagate-values smt) 1000) (par-or (then simplify ctx-solver-simplify smt) smt)))
(get-model)
