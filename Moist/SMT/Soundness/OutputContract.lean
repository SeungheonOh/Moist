import Moist.SMT.Soundness.SolverInput

/-!
# Generated SMT output contract

`SupportedDeclarations` checks every expression supplied by a caller.  The
symbolic evaluator constructs a second, substantially larger expression: the
actual query assertion.  The executable checks live with the portable
compiler in `Moist.SMT.Compiler.Validation`; this module adds their
proof-carrying certificate for the public solver boundary.

The contract is deliberately about the typed `Script` AST before either the
transparent renderer or the pointer-based DAG renderer runs.  A successful
check certifies that the command stream contains only the fixed raw prelude,
checked declarations, assertions, the fixed solver tactic, and the final
model request.  It also certifies that every logical assertion belongs to the
reviewed renderer grammar and has SMT sort `Bool` under exactly the query
declarations.

This is not a replacement for symbolic-execution soundness.  Datatype
selectors and several UPLC operations are intentionally partial in the Lean
observation semantics and total-but-unspecified outside their domains in Z3.
Their path-sensitive guards are covered by the simulation proofs; a
context-free syntax checker cannot establish that stronger property.
-/

namespace Moist.SMT.UPLC.Soundness

/-- Proof-carrying result of validating generated output.  Every field is an
equation computed from the exact stored script and checked by the Lean kernel;
no solver result or admitted proposition is stored here. -/
structure GeneratedOutputContract (declarations : List SymDecl)
    (script : Moist.SMT.Script) : Type where
  commandsSafe : generatedCommandsSafe declarations script = true
  solverControlSafe : generatedSolverControlSafe script = true
  rendererSafe : generatedAssertionsRendererSafe script = true
  sortSafe : generatedAssertionsSortSafe declarations script = true

namespace GeneratedOutputContract

/-- Fail closed when compiler output leaves the reviewed, well-sorted
expression fragment. -/
def check (declarations : List SymDecl) (script : Moist.SMT.Script) :
    Option (GeneratedOutputContract declarations script) :=
  if hCommands : generatedCommandsSafe declarations script = true then
    if hControl : generatedSolverControlSafe script = true then
      if hRenderer : generatedAssertionsRendererSafe script = true then
        if hSort : generatedAssertionsSortSafe declarations script = true then
          some ⟨hCommands, hControl, hRenderer, hSort⟩
        else
          none
      else
        none
    else
      none
  else
    none

@[simp] theorem check_isSome (declarations : List SymDecl)
    (script : Moist.SMT.Script) :
    (check declarations script).isSome =
      (generatedCommandsSafe declarations script &&
        generatedSolverControlSafe script &&
        generatedAssertionsRendererSafe script &&
        generatedAssertionsSortSafe declarations script) := by
  by_cases hCommands : generatedCommandsSafe declarations script = true <;>
    by_cases hControl : generatedSolverControlSafe script = true <;>
    by_cases hRenderer : generatedAssertionsRendererSafe script = true <;>
    by_cases hSort : generatedAssertionsSortSafe declarations script = true <;>
    simp_all [check]

end GeneratedOutputContract

end Moist.SMT.UPLC.Soundness
