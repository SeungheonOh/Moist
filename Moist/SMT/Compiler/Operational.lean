import Moist.SMT.Compiler
import Moist.SMT.DagRender

/-!
# Operational rendering extension

This opt-in module adds `Expr.renderDag` and `Script.renderDag`.  They use Lean
runtime pointer identity to recover sharing and are therefore `unsafe`.  The
portable/certified compiler surface deliberately does not import this module.
-/
