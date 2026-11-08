import Moist.Verified.GuardsSoundness.SinkRel

/-! # Soundness of checks before work

`checksFirst_refines`: for every MIR expression `e`, `e ⊑Ctxᴹ checksFirst e`.

`checksFirst` runs two walks over the hygienic copy of its input:

* `pushAsserts` moves every `if _ then u else error` consumer into the
  computation it consumes (`push_rel`), so the failing branches of that
  computation fail directly;
* `sinkUnits` moves a strict binding or a list/pair destructuring below the
  strict steps that follow it, down to the next check (`sinkWalk_rel`). Two
  steps are exchanged (`swap_rel`) when neither expression mentions the other
  step's binders, neither traces, and the second step's expression halts or
  fails under the facts in scope (`terminatesWith_sound`); a failure of either
  step is then a failure of both orders.
-/

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced Moist.Verified.ShapeFacts Moist.Verified.Guards

/-- Moving strict steps below the checks that follow them refines the input. -/
theorem sinkUnits_refines (e : Expr) : MIRCtxRefines e (Advanced.sinkUnits e) := by
  unfold Advanced.sinkUnits
  simp only
  refine mirCtxRefines_trans (Hygiene.uniqueOptimizationBinders_refines e) ?_
  split
  · rename_i hws
    exact mirCtxRefines_of_factRel hws (fun _ _ => trivial) (fun _ _ => trivial) (sinkWalk_rel [] _)
  · exact mirCtxRefines_refl _

/-- Checks before work: consumers pushed into the checks, strict steps moved below them. -/
theorem checksFirst_refines (e : Expr) : MIRCtxRefines e (Advanced.checksFirst e) :=
  mirCtxRefines_trans (pushAsserts_refines e) (sinkUnits_refines _)

end Moist.Verified.MIR
