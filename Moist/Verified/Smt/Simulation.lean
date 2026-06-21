import Moist.Verified.Smt.Induction

/-! # Stage 2 — the matched-fuel structural simulation `symEval ≡ bigEval`

`sim_value`/`sim_error`/`error_stable` are now **derived** (`Induction.lean`) from the
`∀k`-extra-fuel mutual induction `EvalSim` (+ `bigEval_mono_le` for `error_stable`). This
file re-exports them for `Soundness.lean`. -/

namespace Moist.Verified.Smt
end Moist.Verified.Smt
