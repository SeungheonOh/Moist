import Moist.SMT.Compiler.Checked
import Moist.SMT.Render

/-!
# Portable symbolic compiler surface

Import this module to compile supported UPLC terms into the typed SMT command
AST and render it with the transparent reference renderer.  Its import closure
does not contain `Moist.SMT.Semantics` or any `Moist.SMT.Soundness` module.

The general `compile?` entry point and its succeeds, Boolean, integer, and error
specializations validate caller-controlled input and the exact generated
command AST.
The `*WithAssertions?` variants restrict a target with arbitrary ordinary UPLC
assertions evaluated in the same symbolic environment.  Each assertion can
require any successful CEK value, an exact Boolean or integer, an actual CEK
error, or apply a caller-written UPLC predicate to an evaluated result; the
source-compatible default remains exact `Bool true`.  Refinement clients
should prefer `compileAssertionQueries?` (or its convenience variants), which
returns the assertion-satisfiability and target queries as one coupled result
while sharing assertion compilation. `AssertedTerm` attaches this metadata to
an ordinary deployable UPLC term, while `UplcQuery` may select an application
or result consumer without changing exact erasure of that source. The lower-level
`*InputChecked?` functions deliberately validate input only.  Import the
solver-boundary proof modules when a CEK theorem is also required.

The pointer-sharing operational renderer is intentionally a separate opt-in
module, `Moist.SMT.Compiler.Operational`, because its use of runtime pointer
identity is outside the kernel-checked renderer boundary.
-/
