import Moist.Verified.MIR.Primitives.Shared
import Moist.Verified.MIR.Primitives.Atomize
import Moist.Verified.MIR.Primitives.LetFlattenBody
import Moist.Verified.MIR.Primitives.LetFlattenRhsHead
import Moist.Verified.MIR.Primitives.LetHoistForce
import Moist.Verified.MIR.Primitives.LetHoistAppLeft
import Moist.Verified.MIR.Primitives.LetHoistAppRightAtom
import Moist.Verified.MIR.Primitives.LetHoistCaseScrut
import Moist.Verified.MIR.Primitives.LetHoistConstrArg
import Moist.Verified.MIR.Primitives.Iterated

/-! # MIR rewrite primitives (general — reusable across compiler passes)

This module proves a library of `MIRCtxRefines` rewrites at the expression
level, generally useful for any optimisation pass that needs to manipulate
`.Let`, `.Apply`, `.Force`, `.Case`, or `.Constr` nodes. Each primitive comes
in `_fwd` / `_bwd` forms so it can be applied in either direction.

The contents are split across sub-modules under `Primitives/`:

* `Shared` — `FreshGt` invariant, `steps_trans`, `obsRefinesK_of_steps_*`,
  `stackRefK_funV_id_augment_*`, `envRefinesK_extend`, `stackRefK_force_augment`,
  and the `closedAt`/`shiftRename` compatibility lemmas used by downstream
  primitives.
* `Atomize` — `e ≈ .Let [(x, e, false)] (.Var x)`.
* `LetFlattenBody` — `.Let bs₁ (.Let bs₂ body) ≈ .Let (bs₁ ++ bs₂) body`.
* `LetFlattenRhsHead` — `.Let ((x, .Let bs e, er) :: rest) body ≈
  .Let (bs ++ (x, e, er) :: rest) body` (single/multi/full variants).
* `LetHoistForce` — `.Force (.Let bs body) ≈ .Let bs (.Force body)`.
* `LetHoistAppLeft` — `(.Let bs body) x ≈ .Let bs (body x)`.
* `LetHoistAppRightAtom` — `g (.Let bs body) ≈ .Let bs (g body)` when `g` is
  an atom.
* `LetHoistCaseScrut` — hoist a let out of the scrutinee of a `.Case`.
* `LetHoistConstrArg` — hoist a let out of one argument of a `.Constr`.
* `Iterated` — iterated-hoist helpers, `er`-flag normalisation, and the
  fix-non-Lam vacuous refinement helpers.

Clients should prefer the top-level `mirCtxRefines_*_fwd` / `_bwd` API;
`MIRRefines` and the `_close_pres_*` helpers are implementation details. -/
