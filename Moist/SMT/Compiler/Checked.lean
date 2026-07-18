import Moist.SMT.Compiler.InputChecked
import Moist.SMT.Compiler.OutputAnalysis

/-!
# Fully checked proof-free SMT compiler

This is the production compilation boundary for callers that need a plain
`Option Script`, without importing any soundness proof.  It validates both
caller-controlled input and the exact generated script:

* command forms and fixed raw prelude text;
* the single, fixed solver-control suffix;
* renderer safety for every generated assertion; and
* Boolean sorting for every generated assertion.

The final two checks share one memoized traversal through
`Compiler.OutputAnalysis`.  Cache reuse is guarded by exact structural
identity, so it cannot change acceptance.  The proof module
`Moist.SMT.Soundness.CheckedCompiler` establishes equivalence to the four
transparent output predicates and attaches the CEK soundness certificate to
the exact script returned here.
-/

namespace Moist.SMT.Compiler

open Moist.Plutus.Term
open Moist.SMT.UPLC
open Moist.SMT.Compiler.Validation
open Moist.SMT.Compiler.OutputAnalysis

/-- Validate every compiler-owned part of an already generated script.

The sharing-aware assertion check is proved equivalent to the independent
transparent renderer and sort checks.  Keeping this definition proof-free
makes it directly portable to another implementation language. -/
def outputAccepted (declarations : List SymDecl)
    (script : Moist.SMT.Script) : Bool :=
  generatedCommandsSafe declarations script &&
    generatedSolverControlSafe script &&
    generatedAssertionsOutputSafe declarations script

/-- Return the same script exactly when all generated-output checks pass. -/
def outputChecked? (declarations : List SymDecl)
    (script : Moist.SMT.Script) : Option Moist.SMT.Script :=
  if outputAccepted declarations script then some script else none

/-- Compile one canonical script, after validating both its input and output.

`compileInputChecked?` constructs the script once.  `outputChecked?` consumes
that stored value; symbolic evaluation is never invoked a second time. -/
def compile? (kind : QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (term : Term) : Option Moist.SMT.Script := do
  let script ← compileInputChecked? kind fuel declarations term
  outputChecked? declarations script

def compileBoolTrue? (fuel : Nat) (declarations : List SymDecl)
    (term : Term) : Option Moist.SMT.Script :=
  compile? .boolTrue fuel declarations term

def compileIntEq? (fuel : Nat) (declarations : List SymDecl)
    (term : Term) (expected : Int) : Option Moist.SMT.Script :=
  compile? (.intEq expected) fuel declarations term

def compileError? (fuel : Nat) (declarations : List SymDecl)
    (term : Term) : Option Moist.SMT.Script :=
  compile? .error fuel declarations term

end Moist.SMT.Compiler
