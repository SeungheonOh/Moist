import Moist.SMT.Compiler.Checked
import Moist.SMT.Render

/-!
# Portable symbolic compiler surface

Import this module to compile supported UPLC terms into the typed SMT command
AST and render it with the transparent reference renderer.  Its import closure
does not contain `Moist.SMT.Semantics` or any `Moist.SMT.Soundness` module.

The `compile?`, `compileBoolTrue?`, `compileIntEq?`, and `compileError?` entry
points validate caller-controlled input and the exact generated command AST.
The lower-level `*InputChecked?` functions deliberately validate input only.
Import the solver-boundary proof modules when a CEK theorem is also required.

The pointer-sharing operational renderer is intentionally a separate opt-in
module, `Moist.SMT.Compiler.Operational`, because its use of runtime pointer
identity is outside the kernel-checked renderer boundary.
-/
