import Lean
import Moist.Ptah.Term
import Moist.Ptah.PLift
import Moist.Plutus.Term
import Moist.Plutus.Encode
import Moist.Plutus.Eval
import Moist.Plutus.Pretty
import Moist.Plutus.PrettyHuman
import Moist.MIR.Optimize
import Moist.MIR.Optimize.PreLower
import Moist.MIR.Lower
import Moist.MIR.Pretty

namespace Moist.Ptah

open Moist.MIR (runFresh optimizeExpr preLowerInlineExpr lowerExpr)

def toMIR (t : Term a) (freshStart : Nat := 0) : Moist.MIR.Expr :=
  runFresh t.build freshStart

def compile (t : Term a)
    (optFresh : Nat := 1000) (lowerFresh : Nat := 5000)
    : Except String Moist.Plutus.Term.Program := do
  let mir := toMIR t
  let opt := optimizeExpr mir optFresh
  let prelow := preLowerInlineExpr opt lowerFresh
  let uplc ← lowerExpr prelow (lowerFresh + 1000)
  pure (.Program (.Version 1 1 0) uplc)

def compileUnoptimized (t : Term a)
    (lowerFresh : Nat := 5000)
    : Except String Moist.Plutus.Term.Program := do
  let mir := toMIR t
  let uplc ← lowerExpr mir lowerFresh
  pure (.Program (.Version 1 1 0) uplc)

def plift [PType a] [PLift a] (t : Term a) : IO (PLift.AsLean a) := do
  let prog ← match compile t with
    | .ok p => pure p
    | .error e => throw (.userError s!"plift: compile failed: {e}")
  let result ← match ← Moist.Plutus.Eval.eval prog with
    | .ok r => pure r
    | .error (err, _, msg) => throw (.userError s!"plift: eval failed: {err} - {msg}")
  match PLift.uplcToLean (a := a) result.term with
  | .ok v => pure v
  | .error e => throw (.userError s!"plift: {e}")

section Elaborators

def showMIR (t : Term a) : String :=
  toString (toMIR t)

def showUPLC (t : Term a) : String :=
  match compile t with
  | .ok (.Program _ uplc) => Moist.Plutus.PrettyHuman.prettyHuman uplc
  | .error e => s!"error: {e}"

def showUPLCRaw (t : Term a) : String :=
  match compile t with
  | .ok (.Program _ uplc) => Moist.Plutus.Pretty.prettyTerm uplc
  | .error e => s!"error: {e}"

def showMIROptimized (t : Term a) : String :=
  let mir := toMIR t
  let opt := optimizeExpr mir 1000
  let prelow := preLowerInlineExpr opt 5000
  toString prelow

def showHex (t : Term a) : String :=
  match compile t with
  | .ok prog => prog.encode.toHexString
  | .error e => s!"error: {e}"

def evalToString (t : Term a) : IO String := do
  let prog ← match compile t with
    | .ok p => pure p
    | .error e => throw (.userError s!"compile error: {e}")
  match ← Moist.Plutus.Eval.eval prog with
  | .ok r =>
    pure s!"{Moist.Plutus.PrettyHuman.prettyHuman r.term}\ncpu: {r.budget.cpu} | mem: {r.budget.mem}"
  | .error (err, budget, msg) =>
    pure s!"eval error: {err} — {msg}\ncpu: {budget.cpu} | mem: {budget.mem}"

open Lean Elab Command Term Meta in
private unsafe def evalPure (stx : TSyntax `term) (wrapper : Name) : CommandElabM Unit := do
  let result ← liftTermElabM do
    let e ← elabTerm (← `($(mkIdent wrapper) $stx)) (some (mkConst ``String))
    let e ← instantiateMVars e
    evalExpr String (mkConst ``String) e (safety := .unsafe)
  logInfo m!"{result}"

open Lean Elab Command Term Meta in
private unsafe def evalIO (stx : TSyntax `term) (wrapper : Name) : CommandElabM Unit := do
  let action ← liftTermElabM do
    let ioStringTy ← mkAppM ``IO #[mkConst ``String]
    let e ← elabTerm (← `($(mkIdent wrapper) $stx)) (some ioStringTy)
    let e ← instantiateMVars e
    evalExpr (IO String) ioStringTy e (safety := .unsafe)
  let result ← action
  logInfo m!"{result}"

open Lean Elab Command in
@[implemented_by evalPure]
private opaque evalPureSafe (stx : TSyntax `term) (wrapper : Name) : CommandElabM Unit

open Lean Elab Command in
@[implemented_by evalIO]
private opaque evalIOSafe (stx : TSyntax `term) (wrapper : Name) : CommandElabM Unit

open Lean Elab Command in
elab "#ptah_mir" t:term : command =>
  evalPureSafe t ``showMIR

open Lean Elab Command in
elab "#ptah_mir!" t:term : command =>
  evalPureSafe t ``showMIROptimized

open Lean Elab Command in
elab "#ptah_uplc" t:term : command =>
  evalPureSafe t ``showUPLC

open Lean Elab Command in
elab "#ptah_uplc!" t:term : command =>
  evalPureSafe t ``showUPLCRaw

open Lean Elab Command in
elab "#ptah_hex" t:term : command =>
  evalPureSafe t ``showHex

open Lean Elab Command in
elab "#ptah_eval" t:term : command =>
  evalIOSafe t ``evalToString

end Elaborators

end Moist.Ptah
