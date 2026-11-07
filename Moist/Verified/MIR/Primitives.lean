import Moist.Verified.MIR.Primitives.Shared
import Moist.Verified.MIR.Primitives.LetFlattenBody
import Moist.Verified.MIR.Hoist
import Moist.Verified.MIR.Primitives.Atomize
import Moist.Verified.MIR.Primitives.LetFlattenRhsHead
import Moist.Verified.MIR.Primitives.Iterated

/-! # MIR rewrite primitives

Forward `MIRCtxRefines` rewrites on `.Let` structure, used by ANF
normalization and reusable by other passes.

* `Shared` — CEK-level glue (`obsRefinesK_of_steps_*`, stack augmentations).
* `LetFlattenBody` — `let bs₁ in let bs₂ in e` lowers like `let bs₁ ++ bs₂ in e`.
* `Moist.Verified.MIR.Hoist` — hoisting a `let` out of any evaluation frame
  (`mirCtxRefines_hoist`, `mirCtxRefines_hoist_wrapLet`).
* `Atomize` — `e ⊑ let x = e in x`.
* `LetFlattenRhsHead` — `flattenLetBinds` soundness.
* `Iterated` — list-level helpers (`Constr` congruence, `flattenLetBody`).
-/
