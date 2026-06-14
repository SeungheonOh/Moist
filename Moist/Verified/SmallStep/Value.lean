import Moist.Plutus.Term
import Moist.CEK.Builtins

/-! # UPLC values (spec `V` + well-formed partial builtin applications `A`)

Ports the value grammar of the Plutus Core specification
(`untyped-values.tex`, Fig. `fig:untyped-cek-values`) to the de Bruijn
`Moist.Plutus.Term.Term`.

A *value* is a term that cannot itself undergo reduction:

* a constant `(con tn c)`,
* a delayed term `(delay M)`,
* a lambda `(lam x M)`,
* a constructor `(constr i V⃗)` all of whose fields are values,
* a **well-formed partial builtin application** `A` — a `(builtin b)`
  spine with a correctly-interleaved *prefix* of its argument signature
  consumed (forces at `argQ` positions, value arguments at `argV`
  positions), and **strictly fewer** consumed than the full arity (so it
  is not yet saturated).

The partial-application case is captured by `BSpine`, which mirrors the
CEK runtime value `CekValue.VBuiltin b args ea`: `args` is the list of
value arguments received so far (in application order) and `ea` is the
**non-empty** remaining argument signature.  Saturating spines
(`ea = .one _`) are deliberately *excluded* from `Value`; they are the
builtin redexes handled by `Step`.  Disjointness of `.more` (value) and
`.one` (redex) is what makes reduction deterministic.
-/

namespace Moist.Verified.SmallStep

open Moist.Plutus.Term (Term BuiltinFun)
open Moist.CEK (ArgKind ExpectedArgs expectedArgs)

mutual
  /-- A Plutus Core value: a term in normal form under `Step`. -/
  inductive Value : Term → Prop
    /-- A constant `(con tn c)`. -/
    | constant {cb} : Value (.Constant cb)
    /-- A delayed term `(delay M)` — its body is not evaluated. -/
    | delay {M} : Value (.Delay M)
    /-- A lambda `(lam x M)` — its body is not evaluated. -/
    | lam {x M} : Value (.Lam x M)
    /-- A fully-evaluated constructor `(constr i V⃗)`. -/
    | constr {i args} : ValueList args → Value (.Constr i args)
    /-- A well-formed *partial* builtin application. -/
    | builtin {t b args ea} : BSpine t b args ea → Value t

  /-- Pointwise lift of `Value` to a list of fields. -/
  inductive ValueList : List Term → Prop
    | nil : ValueList []
    | cons {t ts} : Value t → ValueList ts → ValueList (t :: ts)

  /-- `BSpine t b args ea`: `t` is a well-formed *partial* builtin spine
      for `b`, having received the value arguments `args` (application
      order), with `ea` the (always non-empty) remaining argument
      signature.  Mirrors `CekValue.VBuiltin b args.reverse ea`. -/
  inductive BSpine : Term → BuiltinFun → List Term → ExpectedArgs → Prop
    /-- The bare builtin `(builtin b)` expects its whole signature. -/
    | builtin {b} : BSpine (.Builtin b) b [] (expectedArgs b)
    /-- Apply a value argument where the signature expects one (`argV`),
        provided at least one more entry remains afterward (`.more`). -/
    | app {t b args rest v} :
        BSpine t b args (.more .argV rest) → Value v →
        BSpine (.Apply t v) b (args ++ [v]) rest
    /-- Apply `force` where the signature expects a type argument (`argQ`),
        provided at least one more entry remains afterward (`.more`). -/
    | force {t b args rest} :
        BSpine t b args (.more .argQ rest) →
        BSpine (.Force t) b args rest
end

end Moist.Verified.SmallStep
