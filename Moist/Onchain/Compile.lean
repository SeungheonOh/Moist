import Lean
import Moist.Plutus.Eval
import Moist.Plutus.Term
import Moist.Plutus.PrettyHuman
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
open Moist.MIR (optimizeExpr optimizeDebugBeta optimizeTraceExpr preLowerInlineExpr lowerExpr OptStep)

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
    translateDefByName name val
  catch e =>
    return .error s!"translation error: {← e.toMessageData.toString}"
  -- 3. Optimize MIR
  let opt := optimizeExpr mir optFresh
  -- 4. Pre-lower inline (substitute atoms, single-use, dead-pure)
  let prelow := preLowerInlineExpr opt lowerFresh
  -- 5. Lower MIR → UPLC
  return lowerExpr prelow (lowerFresh + 1000)

def compileExprToUPLC (expr : Lean.Expr) (optFresh : Nat := 1000) (lowerFresh : Nat := 5000)
    : MetaM (Except String UPLCTerm) := do
  let mir ← try
    translateDef expr
  catch e =>
    return .error s!"translation error: {← e.toMessageData.toString}"
  let opt := optimizeExpr mir optFresh
  let prelow := preLowerInlineExpr opt lowerFresh
  return lowerExpr prelow (lowerFresh + 1000)

private def compileConstToUPLCOrThrow (name : Name) (requireOnchain : Bool := true) : MetaM UPLCTerm := do
  let env ← getEnv
  if requireOnchain then
    unless onchainAttr.hasTag env name do
      throwError "{name} is not marked @[onchain]"
  let result ← compileToUPLC name
  match result with
  | .ok term => pure term
  | .error e => throwError "compilation of {name} failed: {e}"

/-- Build a synthetic Syntax ref pointing at a local definition's source range.
    Returns `none` for imported constants or if no declaration range is found. -/
private def defSyntaxRef? (name : Name) : CoreM (Option Syntax) := do
  let env ← getEnv
  if env.isImportedConst name then return none
  let some ranges ← findDeclarationRanges? name | return none
  let fileMap ← getFileMap
  return some (Syntax.ofRange ⟨fileMap.ofPosition ranges.range.pos,
                                fileMap.ofPosition ranges.range.endPos⟩)

private def elabCompiledConst (name : Name) : TermElabM Expr := do
  let term ← try
    compileConstToUPLCOrThrow name
  catch e =>
    if let some ref ← defSyntaxRef? name then
      logErrorAt ref e.toMessageData
      Elab.throwAbortTerm
    throw e
  -- Reflect the Term value back into a Lean.Expr via ToExpr
  return Moist.Onchain.ToExprInstances.uplcTermToExpr term

private def resolveCompileTarget (stx : Syntax) : TermElabM Name := do
  match stx with
  | `($id:ident) => resolveGlobalConstNoOverload id
  | _ =>
      let expr ← Term.elabTerm stx none
      let expr ← instantiateMVars expr
      match expr.getAppFn with
      | .const name _ => pure name
      | _ =>
          withRef stx do
            throwError "`.compile!` expects a constant name, for example `myValidator.compile!`"

private def compileTargetToUPLC (stx : Syntax) (requireOnchain : Bool := true) : TermElabM UPLCTerm := do
  let name ← resolveCompileTarget stx
  compileConstToUPLCOrThrow name requireOnchain

private def compileTermSyntaxToUPLCOrThrow (stx : Syntax) : TermElabM UPLCTerm := do
  let expr ← Term.elabTerm stx none
  let expr ← instantiateMVars expr
  let result ← compileExprToUPLC expr
  match result with
  | .ok term => pure term
  | .error e => throwError "compilation failed: {e}"

private def getExplicitAppTargets (stx : Syntax) : Array Syntax :=
  if stx.getKind == ``Lean.Parser.Term.app then
    #[stx[0]] ++ stx[1].getArgs
  else
    #[stx]

private def mkAppliedTerm (terms : Array UPLCTerm) : Option UPLCTerm :=
  match terms.toList with
  | [] => none
  | t :: ts => some <| ts.foldl (init := t) fun acc arg => .Apply acc arg

/-- The `compile!` term elaborator. -/
elab "compile!" id:ident : term => do
  let name ← resolveGlobalConstNoOverload id
  elabCompiledConst name

/-- Postfix `compile!` elaborator for `myDef.compile!`. -/
elab t:term "." "compile!" : term => do
  let name ← resolveCompileTarget t
  elabCompiledConst name

/-- Compile each explicit term in an application spine and evaluate the resulting UPLC term. -/
elab "#evaluatePrettyTerm" t:term : command => do
  let targets := getExplicitAppTargets t.raw
  let compiled ← Elab.Command.liftTermElabM do
    targets.mapM compileTermSyntaxToUPLCOrThrow
  let some applied := mkAppliedTerm compiled
    | throwError "`#evaluatePrettyTerm` expects at least one term"
  let result ← (Moist.Plutus.Eval.evalTerm applied : IO _)
  match result with
  | .ok r =>
      logInfo m!"Result: {r.term}\nCPU:    {r.budget.cpu}\nMemory: {r.budget.mem}"
  | .error (err, budget, msg) =>
      logInfo m!"Error: {err} - {msg}\nCPU:    {budget.cpu}\nMemory: {budget.mem}"

/-- Log a translation error at the definition's source location, then abort. -/
private def logTranslationErrorAtDef (name : Name) (e : Exception)
    : Elab.Command.CommandElabM α := do
  if let some ref ← Elab.Command.liftCoreM (defSyntaxRef? name) then
    logErrorAt ref e.toMessageData
    Elab.throwAbortCommand
  throw e

/-- Debug elaborator: shows the MIR before optimization. -/
elab "#show_mir" id:ident : command => do
  let name ← resolveGlobalConstNoOverload id
  let env ← getEnv
  let some ci := env.find? name
    | throwError "unknown constant: {name}"
  let some val := ci.value?
    | throwError "{name} has no definition body"
  let mir ← try
    Elab.Command.liftTermElabM (translateDefByName name val)
  catch e =>
    logTranslationErrorAtDef name e
  logInfo m!"MIR for {name}:\n{toString mir}"

/-- Debug elaborator: shows the MIR after optimization. -/
elab "#show_optimized_mir" id:ident : command => do
  let name ← resolveGlobalConstNoOverload id
  let env ← getEnv
  let some ci := env.find? name
    | throwError "unknown constant: {name}"
  let some val := ci.value?
    | throwError "{name} has no definition body"
  let mir ← try
    Elab.Command.liftTermElabM (translateDefByName name val)
  catch e =>
    logTranslationErrorAtDef name e
  let opt := optimizeExpr mir 1000
  let prelow := preLowerInlineExpr opt 5000
  logInfo m!"MIR for {name}:\n{toString prelow}"

/-- Debug elaborator: shows MIR after beta reduction + re-ANF (before simplify). -/
elab "#show_beta_mir" id:ident : command => do
  let name ← resolveGlobalConstNoOverload id
  let env ← getEnv
  let some ci := env.find? name
    | throwError "unknown constant: {name}"
  let some val := ci.value?
    | throwError "{name} has no definition body"
  let mir ← try
    Elab.Command.liftTermElabM (translateDefByName name val)
  catch e =>
    logTranslationErrorAtDef name e
  let (betaMir, betaChanged) := optimizeDebugBeta mir 1000
  logInfo m!"After beta (changed={betaChanged}):\n{toString betaMir}"

/-- Widget module for the interactive optimization trace viewer.
Renders a step selector (dropdown + prev/next buttons) with the MIR
for the selected step displayed below. -/
@[widget_module]
def optTraceWidget : Widget.Module where
  javascript := include_str "../../widget/OptTrace.jsx"

/-- Debug elaborator: interactive optimization trace in the InfoView.
Click through each optimization pass with prev/next buttons or the
dropdown. Usage: `#show_opt_trace myFun` -/
elab "#show_opt_trace" id:ident : command => do
  let name ← resolveGlobalConstNoOverload id
  let env ← getEnv
  let some ci := env.find? name
    | throwError "unknown constant: {name}"
  let some val := ci.value?
    | throwError "{name} has no definition body"
  let mir ← try
    Elab.Command.liftTermElabM (translateDefByName name val)
  catch e =>
    logTranslationErrorAtDef name e
  let steps := optimizeTraceExpr mir 1000
  -- Build JSON steps array: Input + trace steps + PreLowerInline
  let mut allSteps : Array Json := #[.mkObj [
    ("pass", .str "Input MIR"),
    ("expr", .str (toString mir)),
    ("changed", .bool false)
  ]]
  for s in steps do
    allSteps := allSteps.push (.mkObj [
      ("pass", .str s.pass),
      ("expr", .str (toString s.expr)),
      ("changed", .bool s.changed)
    ])
  if let some last := steps.back? then
    let prelow := preLowerInlineExpr last.expr 5000
    allSteps := allSteps.push (.mkObj [
      ("pass", .str "PreLowerInline"),
      ("expr", .str (toString prelow)),
      ("changed", .bool true)
    ])
  let props : Json := .mkObj [("steps", .arr allSteps)]
  Elab.Command.liftCoreM <|
    Widget.savePanelWidgetInfo optTraceWidget.javascriptHash.val (pure props) (← getRef)

/-- Compile each explicit term in an application spine to a single UPLC term. -/
private def compileAppSpineToUPLC (stx : Syntax) : Elab.Command.CommandElabM UPLCTerm := do
  let targets := getExplicitAppTargets stx
  let compiled ← Elab.Command.liftTermElabM do
    targets.mapM compileTermSyntaxToUPLCOrThrow
  let some applied := mkAppliedTerm compiled
    | throwError "expects at least one term"
  pure applied

/-- Debug elaborator: compiles any term to UPLC and shows standard Plutus textual format. -/
elab "#show_uplc" t:term : command => do
  let term ← compileAppSpineToUPLC t.raw
  logInfo m!"{Moist.Plutus.Pretty.prettyTerm term}"

/-- Debug elaborator: compiles any term to UPLC and shows human-readable output. -/
elab "#show_pretty_uplc" t:term : command => do
  let term ← compileAppSpineToUPLC t.raw
  logInfo m!"{Moist.Plutus.PrettyHuman.prettyHuman term}"

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
