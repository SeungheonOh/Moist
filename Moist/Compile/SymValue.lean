import Moist.CEK.Value
import Moist.Smt.Syntax

/-! # Symbolic values — the mirror of `CekValue`

`SymVal` is `CekValue` with its one *value* slot replaced by a symbolic `SmtExpr`: a `VCon`
becomes an `sCon` carrying an `SmtExpr` (a possibly-symbolic constant), while closures
(`sLam`/`sDelay`), statically-known constructors (`sConstr`) and partially-applied builtins
(`sBuiltin`) keep the **exact same defunctionalized shape** as `CekValue`.  This is the
load-bearing decision (§2 of the plan): because closures are defunctionalized — functions
are *applied by the evaluator*, never by Lean, and never appear in the emitted SMT — the
adequacy proof's value relation (`γ`, `Moist/Compile/Adequacy.lean`) is **structural**, not
a higher-order logical relation.

`SymEnv` is a plain `List SymVal` with the *same 1-based de-Bruijn lookup convention* as
`Moist.CEK.CekEnv` (`Var 1` = head), so the concretization `γE` is a list homomorphism and
`lookup` commutes with it on the nose.
-/

namespace Moist.Compile

open Moist.Plutus.Term (Term Const BuiltinFun)
open Moist.CEK (ExpectedArgs)
open Moist.Smt (SmtExpr)

/-- Symbolic runtime value.  One-for-one with `Moist.CEK.CekValue`, except `VCon c`
    (a concrete constant) becomes `sCon e` (a symbolic `SmtExpr`). -/
inductive SymVal
  /-- A (possibly symbolic) constant, represented by an `SmtExpr`. -/
  | sCon     : SmtExpr → SymVal
  /-- A **fully concrete** constant of *any* type (`ByteString`, `Data`, `Unit`, lists, …).
      Lets the compiler defer concrete-argument builtins to the real `evalBuiltin`, giving
      full CEK builtin coverage on concrete data with an axiom-free agreement. -/
  | sConst   : Const → SymVal
  /-- Lambda closure: body + captured symbolic environment (defunctionalized = `VLam`). -/
  | sLam     : Term → List SymVal → SymVal
  /-- Delayed computation: body + captured environment (= `VDelay`). -/
  | sDelay   : Term → List SymVal → SymVal
  /-- Statically-known constructor: tag + symbolic fields (= `VConstr`). -/
  | sConstr  : Nat → List SymVal → SymVal
  /-- Partially applied builtin: function, accumulated args (reversed), remaining
      expected arguments (= `VBuiltin`). -/
  | sBuiltin : BuiltinFun → List SymVal → ExpectedArgs → SymVal
  /-- **Deferred symbolic choice** — the value of `ifThenElse c thenV elseV` when `c` is a
      symbolic boolean.  It is *not* forced yet (the branches may be `delay`s); forcing it
      (`symForce`) evaluates **both** branches and emits an SMT `ite`.  This is what turns a
      recursion guard into bounded unrolling: the recursive branch unfolds one level deeper,
      bottoming out at fuel exhaustion (→ `defined = false`).  `γ (sIte c a b)` picks `a` or
      `b` by `c` at the model, matching the CEK's concrete `ifThenElse`. -/
  | sIte : SmtExpr → SymVal → SymVal → SymVal
deriving Repr, Inhabited

/-- Symbolic environment: a stack of symbolic values, same convention as `CekEnv`. -/
abbrev SymEnv := List SymVal

namespace SymEnv

/-- Look up a de-Bruijn index (1-based), matching `Moist.CEK.CekEnv.lookup` exactly:
    `Var 1` = head, out-of-bounds = `none`. -/
def lookup : SymEnv → Nat → Option SymVal
  | [],       _     => none
  | _ :: _,   0     => none
  | v :: _,   1     => some v
  | _ :: rest, n+1  => lookup rest n

/-- Extend (prepend): the new value becomes `Var 1`, like `CekEnv.extend`. -/
@[inline] def extend (ρ : SymEnv) (v : SymVal) : SymEnv := v :: ρ

end SymEnv

/-- The output of symbolic evaluation: the symbolic value together with its **definedness**
    formula — a `Bool`-sorted `SmtExpr` that is `true` exactly at models where the
    *concrete* UPLC evaluation does **not** error (e.g. `divideInteger` contributes a
    `y ≠ 0` conjunct).  Partiality is threaded here, never inside `evalSmt` (§2.3). -/
structure SymOut where
  value   : SymVal
  defined : SmtExpr
deriving Repr, Inhabited

end Moist.Compile
