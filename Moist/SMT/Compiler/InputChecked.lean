import Moist.SMT.Compiler.Validation

/-!
# Proof-free input-checked SMT compiler

This module is the portable production entry point.  It contains executable
checks and returns only the typed SMT script AST; no semantic theorem or
proof-carrying wrapper is required by callers that merely compile a query.

The unchecked `scriptFor*` functions remain useful low-level primitives.  The
functions below additionally reject unsupported UPLC builtins, malformed or
ambiguous declarations, and renderer-unsafe caller input.

Generated assertions are compiler-owned rather than caller-controlled.  They
are deliberately not subjected here to the output contract's unbounded
renderer and sort traversals: those walks expand shared symbolic decision DAGs
and can dominate compilation.  Canonical script construction still performs
its bounded prelude-dependency scan.  The proof-carrying solver boundary
validates the exact returned script before exposing its CEK soundness theorem;
a future construction-time invariant can eliminate that proof-side postcheck
without changing this API.
-/

namespace Moist.SMT.Compiler

open Moist.Plutus.Term
open Moist.SMT.UPLC
open Moist.SMT.Compiler.Validation

/-- The three production propositions currently exposed by the symbolic
compiler.  Integer equality intentionally carries a literal integer rather
than an arbitrary SMT expression. -/
inductive QueryKind where
  | boolTrue
  | intEq (expected : Int)
  | error
deriving Repr, BEq

/-- Validate all caller-controlled input before symbolic evaluation.

This is the single executable input gate.  Mandatory decoding assumptions
belong to the computational `declarationsInputSafe` check; `SymDecl` itself is
a proof-free record.  A foreign-language port must preserve this validation. -/
def inputAccepted (declarations : List SymDecl) (term : Term) : Bool :=
  symEnvNoOpaqueForSoundness (envOf declarations) &&
    declarationsRendererSafe declarations &&
    declarationsSortSafe declarations &&
    declarationsInputSafe declarations &&
    declarationNamesDistinct declarations &&
    !termUsesOpaqueBuiltinForSoundness term

/-- Construct the one canonical script for a checked query kind. -/
def scriptFor (kind : QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (term : Term) : Moist.SMT.Script :=
  match kind with
  | .boolTrue => scriptForBoolTrue fuel declarations term
  | .intEq expected =>
      scriptForIntEq fuel declarations term (.int expected)
  | .error => scriptForError fuel declarations term

/-- Compile after fail-closed validation of all caller-controlled input.

The canonical script is constructed once.  This function intentionally does
not run the output contract's unbounded renderer and sort traversals over its
generated assertion DAG; proof-carrying wrappers postcheck this exact stored
result without invoking `evalSym` a second time.  Script construction retains
the bounded prelude-dependency scan needed to select declarations.

The name is deliberately explicit: success certifies the input boundary, not
the compiler-owned output AST.  Use the proof-carrying query constructors when
a `GeneratedOutputContract` and CEK soundness endpoint are required. -/
def compileInputChecked? (kind : QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (term : Term) : Option Moist.SMT.Script :=
  if inputAccepted declarations term then
    some (scriptFor kind fuel declarations term)
  else
    none

def compileBoolTrueInputChecked? (fuel : Nat) (declarations : List SymDecl)
    (term : Term) : Option Moist.SMT.Script :=
  compileInputChecked? .boolTrue fuel declarations term

def compileIntEqInputChecked? (fuel : Nat) (declarations : List SymDecl)
    (term : Term) (expected : Int) : Option Moist.SMT.Script :=
  compileInputChecked? (.intEq expected) fuel declarations term

def compileErrorInputChecked? (fuel : Nat) (declarations : List SymDecl)
    (term : Term) : Option Moist.SMT.Script :=
  compileInputChecked? .error fuel declarations term

end Moist.SMT.Compiler
