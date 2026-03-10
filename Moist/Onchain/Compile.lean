import Lean
import Moist.Plutus.Term
import Moist.MIR.Expr
import Moist.MIR.Optimize
import Moist.MIR.Optimize.PreLower
import Moist.MIR.Lower
import Moist.MIR.Pretty
import Moist.Onchain.Attribute
import Moist.Onchain.ToExpr
import Moist.Onchain.Translate

namespace Moist.Onchain

open Lean Elab Meta
open Moist.MIR (optimizeExpr preLowerInlineExpr lowerExpr)

-- Use a local alias to avoid ambiguity with Lean.Term
private abbrev UPLCTerm := Moist.Plutus.Term.Term

/-! # compile! Term Elaborator

`compile!` is a term elaborator that compiles an `@[onchain]` Lean definition
to a UPLC `Term` at elaboration time. The result is reflected back as a Lean
expression via `ToExpr`, producing a regular constant that can be exported
to other modules.

Usage:
```
@[onchain]
def myFun (x : Int) : Int := x

def myFunUPLC : Term := compile! myFun
```
-/

/-- Run the full compilation pipeline on a named constant.
    Returns the UPLC Term or an error message. -/
def compileToUPLC (name : Name) (optFresh : Nat := 1000) (lowerFresh : Nat := 5000)
    : MetaM (Except String UPLCTerm) := do
  let env ← getEnv
  -- 1. Get definition body
  let some ci := env.find? name
    | return .error s!"unknown constant: {name}"
  let some val := ci.value?
    | return .error s!"{name} has no definition body"
  -- 2. Translate Lean.Expr → MIR.Expr
  let mir ← try
    translateDef val
  catch e =>
    return .error s!"translation error: {← e.toMessageData.toString}"
  -- 3. Optimize MIR
  let opt := optimizeExpr mir optFresh
  -- 4. Pre-lower inline (substitute atoms, single-use, dead-pure)
  let prelow := preLowerInlineExpr opt lowerFresh
  -- 5. Lower MIR → UPLC
  return lowerExpr prelow (lowerFresh + 1000)

/-- The `compile!` term elaborator. -/
elab "compile!" id:ident : term => do
  let name ← resolveGlobalConstNoOverload id
  let env ← getEnv
  -- Verify @[onchain] attribute
  unless onchainAttr.hasTag env name do
    throwError "{name} is not marked @[onchain]"
  -- Run the pipeline
  let result ← compileToUPLC name
  match result with
  | .ok term =>
    -- Reflect the Term value back into a Lean.Expr via ToExpr
    return Moist.Onchain.ToExprInstances.uplcTermToExpr term
  | .error e =>
    throwError "compilation of {name} failed: {e}"

/-- Debug elaborator: shows the MIR before optimization. -/
elab "#show_mir" id:ident : command => do
  let name ← resolveGlobalConstNoOverload id
  let env ← getEnv
  let some ci := env.find? name
    | throwError "unknown constant: {name}"
  let some val := ci.value?
    | throwError "{name} has no definition body"
  let mir ← Elab.Command.liftTermElabM do
    try
      translateDef val
    catch e =>
      throwError "translation error: {← e.toMessageData.toString}"
  logInfo m!"MIR for {name}:\n{toString mir}"

/-- Debug elaborator: shows the MIR after optimization. -/
elab "#show_optimized_mir" id:ident : command => do
  let name ← resolveGlobalConstNoOverload id
  let env ← getEnv
  let some ci := env.find? name
    | throwError "unknown constant: {name}"
  let some val := ci.value?
    | throwError "{name} has no definition body"
  let mir ← Elab.Command.liftTermElabM do
    try
      translateDef val
    catch e =>
      throwError "translation error: {← e.toMessageData.toString}"
  let opt := optimizeExpr mir 1000
  let prelow := preLowerInlineExpr opt 5000
  logInfo m!"MIR for {name}:\n{toString prelow}"

/-- Debug elaborator: shows the raw Lean.Expr for a definition. -/
elab "#show_expr" id:ident : command => do
  let name ← resolveGlobalConstNoOverload id
  let env ← getEnv
  let some ci := env.find? name
    | throwError "unknown constant: {name}"
  let some val := ci.value?
    | throwError "{name} has no definition body"
  logInfo m!"Expr for {name}:\n{val}"

/-- Debug elaborator: shows the raw constructor structure of a definition. -/
elab "#show_raw_expr" id:ident : command => do
  let name ← resolveGlobalConstNoOverload id
  let env ← getEnv
  let some ci := env.find? name
    | throwError "unknown constant: {name}"
  let some val := ci.value?
    | throwError "{name} has no definition body"
  -- Print structure: peel one lambda, then show the body's constructor structure
  let rec showExpr (e : Lean.Expr) (depth : Nat) : String :=
    if depth > 8 then "..."
    else
      let indent := String.mk (List.replicate (depth * 2) ' ')
      match e with
      | .lam n _t b _bi => s!"{indent}lam {n}\n{showExpr b (depth + 1)}"
      | .app f a => s!"{indent}app\n{showExpr f (depth + 1)}\n{showExpr a (depth + 1)}"
      | .const n _ => s!"{indent}const {n}"
      | .bvar i => s!"{indent}bvar {i}"
      | .letE n _ v b _ => s!"{indent}letE {n}\n{showExpr v (depth + 1)}\n{showExpr b (depth + 1)}"
      | .forallE n _ b _ => s!"{indent}forallE {n}\n{showExpr b (depth + 1)}"
      | .lit l => s!"{indent}lit {repr l}"
      | .sort l => s!"{indent}sort {l}"
      | .mdata _ e => s!"{indent}mdata\n{showExpr e (depth + 1)}"
      | _ => s!"{indent}other {e.ctorName}"
  logInfo m!"{showExpr val 0}"

end Moist.Onchain
