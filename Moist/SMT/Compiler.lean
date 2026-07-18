import Moist.SMT.Compiler.InputChecked
import Moist.SMT.Compiler.OutputAnalysis
import Moist.SMT.Render

/-!
# Portable symbolic compiler surface

Import this module to compile supported UPLC terms into the typed SMT command
AST and render it with the transparent reference renderer.  Its import closure
does not contain `Moist.SMT.Semantics` or any `Moist.SMT.Soundness` module.

The `*InputChecked?` entry points validate caller-controlled inputs; their
names deliberately do not claim that generated commands have been
postvalidated or that a CEK theorem is attached.  Import the solver-boundary
proof modules when those stronger guarantees are required.

The pointer-sharing operational renderer is intentionally a separate opt-in
module, `Moist.SMT.Compiler.Operational`, because its use of runtime pointer
identity is outside the kernel-checked renderer boundary.
-/
