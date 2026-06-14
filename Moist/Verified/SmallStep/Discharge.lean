import Moist.CEK.Machine
import Moist.Verified.RenameBase

/-! # Discharging CEK values to UPLC terms (proof-grade `readback`)

Total analogue of `Moist.CEK.readbackValue` (which is `partial`), using the
total `Moist.Verified.substTerm`.  `discharge v` "unloads" a CEK value into
the closed UPLC term it represents, substituting each environment binding for
the corresponding free de Bruijn index (spec `untyped-cek-machine.tex`,
Figs. `fig:discharge-val` / `fig:discharge-env`).

`reflect` is the (partial-inverse) interpretation of a value-term back into a
`CekValue`, with empty environments for closures.  It is *not* a left inverse
of `discharge` on the nose — discharge folds a closure's environment into its
body, which `reflect` cannot recover — but it satisfies
`discharge (reflect (discharge v)) = discharge v`, which is the bridge used by
the builtin reduction rule (`Step` routes builtin evaluation through the shared
`evalBuiltin`, so `reflect` converts the discharged value arguments back into
`CekValue`s for it).
-/

namespace Moist.Verified.SmallStep

open Moist.Plutus.Term (Term Const constType)
open Moist.CEK
open Moist.Verified (substTerm)

/-- The consumed argument kinds: the prefix of signature `full` that is not
    present in the remaining suffix `rem`.  Mirrors the (private)
    `consumedSteps` of `Moist.CEK.Readback`. -/
def consumedSteps : ExpectedArgs → ExpectedArgs → List ArgKind
  | full, rem =>
    if full = rem then []
    else match full with
      | .one k => [k]
      | .more k rest => k :: consumedSteps rest rem
  termination_by full => full

/-- Rebuild a builtin spine by applying the consumed forces/value-arguments to
    `acc`.  `args` are the already-discharged value arguments in application
    order. -/
def dischargeSpine : Term → List ArgKind → List Term → Term
  | acc, [], _ => acc
  | acc, .argQ :: rest, args => dischargeSpine (.Force acc) rest args
  | acc, .argV :: _, [] => acc
  | acc, .argV :: rest, a :: as => dischargeSpine (.Apply acc a) rest as

mutual
  /-- Discharge a CEK value to the closed UPLC term it represents. -/
  def discharge : CekValue → Term
    | .VCon c => .Constant (c, constType c)
    | .VLam body env => .Lam 0 (dischargeEnv env 1 body)
    | .VDelay body env => .Delay (dischargeEnv env 0 body)
    | .VConstr tag fields => .Constr tag (dischargeList fields)
    | .VBuiltin b args ea =>
        dischargeSpine (.Builtin b) (consumedSteps (expectedArgs b) ea)
          (dischargeList args).reverse
  termination_by v => sizeOf v

  /-- Discharge a list of CEK values pointwise. -/
  def dischargeList : List CekValue → List Term
    | [] => []
    | v :: vs => discharge v :: dischargeList vs
  termination_by vs => sizeOf vs

  /-- Discharge an environment into `body`: iterated open substitution of each
      binding (most-recent first) at the fixed position `depth + 1`.  `depth`
      is the number of binders above `body` to preserve (1 for `VLam`,
      0 for `VDelay`).  Matches `Moist.CEK.Readback.closeOver`. -/
  def dischargeEnv : CekEnv → Nat → Term → Term
    | .nil, _, body => body
    | .cons v rest, depth, body =>
        dischargeEnv rest depth (substTerm (depth + 1) (discharge v) body)
  termination_by env _ _ => sizeOf env
end

/-- Discharge an optional CEK value: `none` (builtin failure) becomes `Error`. -/
def dischargeResult : Option CekValue → Term
  | some v => discharge v
  | none => .Error

mutual
  /-- Interpret a value-term back as a `CekValue` (empty environments for
      closures; spine parsing for builtins).  Junk on non-values. -/
  def reflect : Term → CekValue
    | .Constant (c, _) => .VCon c
    | .Lam _ body => .VLam body .nil
    | .Delay body => .VDelay body .nil
    | .Constr i args => .VConstr i (reflectList args)
    | .Builtin b => .VBuiltin b [] (expectedArgs b)
    | .Apply t v =>
      match reflect t with
      | .VBuiltin b args (.more .argV rest) => .VBuiltin b (reflect v :: args) rest
      | _ => .VCon .Unit
    | .Force t =>
      match reflect t with
      | .VBuiltin b args (.more .argQ rest) => .VBuiltin b args rest
      | _ => .VCon .Unit
    | .Var _ => .VCon .Unit
    | .Case _ _ => .VCon .Unit
    | .Error => .VCon .Unit

  /-- `reflect` lifted to lists of value-terms. -/
  def reflectList : List Term → List CekValue
    | [] => []
    | t :: ts => reflect t :: reflectList ts
end

/-- Initial CEK state for a closed term. -/
def init (t : Term) : State := .compute [] .nil t

end Moist.Verified.SmallStep
