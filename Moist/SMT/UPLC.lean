import Moist.SMT.Compiler.UPLC.Query

/-!
# UPLC symbolic compiler compatibility facade

The executable compiler is physically organized under
`Moist.SMT.Compiler.UPLC` by responsibility, while declarations retain the
historical `Moist.SMT.UPLC` namespace.  Importing this facade therefore keeps
the complete public API and all existing proof consumers source-compatible.
-/
