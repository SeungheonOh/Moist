import Moist.SMT.Compiler.InputChecked
import Moist.SMT.Soundness.Optimize

/-!
# Executable compiler contracts

This module contains semantic and script-accounting theorems about the
portable symbolic compiler.  Keeping these contracts out of
`Moist.SMT.UPLC` prevents executable users from importing the simulated Z3
semantics or the proof tree.
-/

namespace Moist.SMT.UPLC

open Moist.Plutus.Term

namespace SExpr

private theorem sameListWith_eq_true
    (same : SExpr → SExpr → Bool)
    (hsame : ∀ left right, same left right = true → left = right) :
    ∀ left right,
      sameListWith same left right = true → left = right
  | [], [], _ => rfl
  | left :: lefts, right :: rights, equal => by
      simp only [sameListWith, Bool.and_eq_true] at equal
      cases hsame left right equal.1
      cases sameListWith_eq_true same hsame lefts rights equal.2
      rfl
  | [], _ :: _, equal
  | _ :: _, [], equal => by
      simp [sameListWith] at equal

/-- The proof-free executable equality check can enable reflexive folding only
for expressions with exactly the same syntax.  Fuel exhaustion returns
`false`, so it can only miss an optimization. -/
theorem same?_eq_true : ∀ fuel left right,
    same? fuel left right = true → left = right
  | 0, _, _, equal => by simp [same?] at equal
  | _ + 1, .sym left, right, equal
  | _ + 1, .int left, right, equal
  | _ + 1, .bytes left, right, equal
  | _ + 1, .dataLit left, right, equal
  | _ + 1, .dataListLit left, right, equal
  | _ + 1, .dataPairListLit left, right, equal
  | _ + 1, .constListLit left, right, equal
  | _ + 1, .bool left, right, equal
  | _ + 1, .str left, right, equal => by
      cases right <;> simp_all [same?]
  | fuel + 1, .app leftName leftArgs, right, equal => by
      cases right with
      | app rightName rightArgs =>
          simp only [same?, Bool.and_eq_true, decide_eq_true_eq] at equal
          cases equal.1
          cases sameListWith_eq_true (same? fuel)
            (fun left right => same?_eq_true fuel left right)
            leftArgs rightArgs equal.2
          rfl
      | sym name | int name | bytes name | dataLit name | dataListLit name
      | dataPairListLit name | constListLit name | bool name | str name =>
          exact Bool.noConfusion equal
      | ite condition thenBranch elseBranch => exact Bool.noConfusion equal
  | fuel + 1, .ite leftCondition leftThen leftElse, right, equal => by
      cases right with
      | ite rightCondition rightThen rightElse =>
          change (same? fuel leftCondition rightCondition &&
            same? fuel leftThen rightThen &&
            same? fuel leftElse rightElse) = true at equal
          simp only [Bool.and_eq_true] at equal
          cases same?_eq_true fuel leftCondition rightCondition equal.1.1
          cases same?_eq_true fuel leftThen rightThen equal.1.2
          cases same?_eq_true fuel leftElse rightElse equal.2
          rfl
      | sym name | int name | bytes name | dataLit name | dataListLit name
      | dataPairListLit name | constListLit name | bool name | str name =>
          exact Bool.noConfusion equal
      | app name arguments => exact Bool.noConfusion equal

theorem sameAtom_eq_true {a b : SExpr} (h : sameAtom a b = true) :
    a = b := by
  cases a <;> cases b <;> simp_all [sameAtom]

@[simp] theorem anyBalanced_nil : anyBalanced [] = falseE := by
  simp [anyBalanced]

@[simp] theorem anyBalanced_singleton (x : SExpr) : anyBalanced [x] = x := by
  simp [anyBalanced]

@[simp] theorem anyBalanced_pair (x y : SExpr) :
    anyBalanced [x, y] = or x y := by
  simp [anyBalanced, orPairRound]

@[simp] theorem any_nil : any [] = falseE := by
  simp [any]

@[simp] theorem any_singleton (x : SExpr) : any [x] = x := by
  simp [any]

@[simp] theorem any_pair (x y : SExpr) : any [x, y] = or x y := by
  simp [any]

end SExpr

namespace SymDecl

/-- Proof-level meaning of the mandatory-assumption table.  The executable
compiler record deliberately does not carry this proposition; the checked
input boundary reconstructs it from its Boolean validator. -/
def WellFormed (name : String) (sort : Moist.SMT.SSort)
    (value : SymVal) (assumptions : List SExpr) : Prop :=
  ∃ required, symDeclRequired? name sort value = some required ∧
    ∀ e, e ∈ required → e ∈ assumptions

/-- The declaration invariant exposes the nonnegative-tag assertion required
by an integer declaration whose value is a symbolic constructor. -/
theorem constrTagNonnegative_mem (declaration : SymDecl)
    (hwellFormed : WellFormed declaration.name declaration.sort
      declaration.value declaration.assumptions)
    {tag : String} {fields : List SymVal}
    (hsort : declaration.sort = .int)
    (hvalue : declaration.value = .constr (.sym tag) fields)
    (hname : tag = declaration.name) :
    SExpr.ge (.sym tag) (.int 0) ∈ declaration.assumptions := by
  rcases declaration with ⟨name, sort, value, assumptions⟩
  simp only at hsort hvalue hname ⊢
  subst sort
  subst value
  subst name
  rcases hwellFormed with ⟨required, hrequired, hcontains⟩
  simp [symDeclRequired?] at hrequired
  subst required
  exact hcontains _ (by simp)

/-- Every declaration at SMT sort `Val` carries the exact validity assertion
needed to decode its model value into a CEK value. -/
theorem valValid_mem_of_sort (declaration : SymDecl)
    (hwellFormed : WellFormed declaration.name declaration.sort
      declaration.value declaration.assumptions)
    (hsort : declaration.sort = .val) :
    (.app "val_valid" [.sym declaration.name] : SExpr) ∈
      declaration.assumptions := by
  rcases declaration with ⟨name, sort, value, assumptions⟩
  simp only at hsort ⊢
  subst sort
  rcases hwellFormed with ⟨required, hrequired, hcontains⟩
  cases value <;> simp [symDeclRequired?] at hrequired
  case dyn expression =>
    cases expression <;> simp at hrequired
    case sym symbol =>
      rcases hrequired with ⟨rfl, hrequired⟩
      subst required
      exact hcontains _ (.head _)

end SymDecl

theorem evalBoolIs_assertionConjunction_true
    (model : Moist.SMT.Semantics.Model) (expressions : List SExpr) :
    Moist.SMT.Semantics.evalBoolIs model
        (assertionConjunction expressions) true = true ↔
      ∀ expression, expression ∈ expressions →
        Moist.SMT.Semantics.evalBoolIs model expression true = true := by
  induction expressions with
  | nil =>
      simp [assertionConjunction, SExpr.trueE, Moist.SMT.Expr.trueE,
        Moist.SMT.Semantics.evalBoolIs, Moist.SMT.Semantics.evalBool?,
        Moist.SMT.Semantics.eval]
  | cons expression expressions inductionHypothesis =>
      change
        Moist.SMT.Semantics.evalBoolIs model
            (Moist.SMT.Expr.and expression
              (assertionConjunction expressions)) true = true ↔ _
      rw [
        Moist.SMT.Semantics.evalBoolIs_and_true,
        inductionHypothesis]
      simp only [List.mem_cons, forall_eq_or_imp]

theorem groupedAssertions_true_iff
    (model : Moist.SMT.Semantics.Model) (assertions : List SExpr) :
    (∀ expression, expression ∈ groupedAssertions assertions →
      Moist.SMT.Semantics.evalBoolIs model expression true = true) ↔
    (∀ expression, expression ∈ assertions →
      Moist.SMT.Semantics.evalBoolIs model expression true = true) := by
  cases assertions with
  | nil => simp [groupedAssertions]
  | cons expression expressions =>
      cases expressions with
      | nil => simp [groupedAssertions]
      | cons next expressions =>
          simp only [groupedAssertions, List.mem_singleton, forall_eq]
          exact evalBoolIs_assertionConjunction_true model
            (expression :: next :: expressions)

private theorem assertions_preludeSection (part : PreludeSection) :
    part.commands.filterMap Moist.SMT.Command.assertion? = [] := by
  cases part <;> rfl

private theorem assertions_optionalPrelude (enabled : Bool)
    (commands : List Moist.SMT.Command)
    (hcommands : commands.filterMap Moist.SMT.Command.assertion? = []) :
    (if enabled then commands else []).filterMap
      Moist.SMT.Command.assertion? = [] := by
  cases enabled <;> simp [hcommands]

private theorem assertions_selectedPreludeSections (needs : PreludeNeeds)
    (sections : List PreludeSection) :
    (sections.flatMap fun part =>
      if needs.includes part then part.commands else []).filterMap
        Moist.SMT.Command.assertion? = [] := by
  induction sections with
  | nil => rfl
  | cons part sections ih =>
      simp only [List.flatMap_cons, List.filterMap_append]
      rw [assertions_optionalPrelude _ _ (assertions_preludeSection part), ih]
      rfl

private theorem assertions_preludeForAssertions (assertions : List SExpr) :
    (preludeForAssertions assertions).filterMap
      Moist.SMT.Command.assertion? = [] := by
  exact assertions_selectedPreludeSections _ _

private theorem assertions_fullPrelude :
    prelude.filterMap Moist.SMT.Command.assertion? = [] := by
  rfl

private theorem assertions_declCommands (decls : List SymDecl) :
    (declCommands decls).filterMap Moist.SMT.Command.assertion? = [] := by
  induction decls with
  | nil => rfl
  | cons _ decls _ => simp [declCommands, Moist.SMT.Command.assertion?]

private theorem assertions_assertCommands (assertions : List SExpr) :
    (assertions.map Moist.SMT.Command.assert).filterMap
      Moist.SMT.Command.assertion? = assertions := by
  induction assertions with
  | nil => rfl
  | cons _ assertions ih =>
      simp [Moist.SMT.Command.assertion?, ih]

private theorem assertions_assumptionCommands (decls : List SymDecl) :
    (assumptionCommands decls).filterMap Moist.SMT.Command.assertion? =
      decls.flatMap SymDecl.assumptions := by
  induction decls with
  | nil => rfl
  | cons decl decls ih =>
      change
        (decl.assumptions.map Moist.SMT.Command.assert ++
          assumptionCommands decls).filterMap Moist.SMT.Command.assertion? =
        decl.assumptions ++ decls.flatMap SymDecl.assumptions
      rw [List.filterMap_append, assertions_assertCommands, ih]

/-- Solver-control commands are assertion-neutral in the typed `Script` AST
for every tactic string.  This is the kernel-checked preservation theorem for
solver-strategy changes; it deliberately does not certify raw tactic syntax or
the separately documented SMT-LIB rendering boundary. -/
theorem scriptWithTactic_assertions (tactic : String) (decls : List SymDecl)
    (assertions : List SExpr) :
    (scriptWithTactic tactic decls assertions).assertions =
      decls.flatMap SymDecl.assumptions ++ groupedAssertions assertions := by
  simp only [scriptWithTactic, Moist.SMT.Script.assertions,
    List.filterMap_append]
  rw [assertions_preludeForAssertions, assertions_declCommands,
    assertions_assumptionCommands]
  simp only [groupedAssertionCommands, assertions_assertCommands]
  simp [Moist.SMT.Command.assertion?]

/-- Purely syntactic accounting for typed assertion commands.  This theorem
does not claim that Z3 returned a model, that the model satisfies the
assertions, or that raw prelude commands have any particular semantics; those
facts belong to `Soundness.CertifiedZ3Model`. -/
theorem scriptWith_assertions (decls : List SymDecl) (assertions : List SExpr) :
    (scriptWith decls assertions).assertions =
      decls.flatMap SymDecl.assumptions ++ groupedAssertions assertions := by
  exact scriptWithTactic_assertions z3QueryTactic decls assertions

theorem scriptWithFullPrelude_assertions (decls : List SymDecl)
    (assertions : List SExpr) :
    (scriptWithFullPrelude decls assertions).assertions =
      decls.flatMap SymDecl.assumptions ++ assertions := by
  simp only [scriptWithFullPrelude, Moist.SMT.Script.assertions,
    List.filterMap_append]
  rw [assertions_fullPrelude, assertions_declCommands,
    assertions_assumptionCommands, assertions_assertCommands]
  simp [Moist.SMT.Command.assertion?]

/-- Demand-selected prelude commands and caller-assertion grouping preserve
exactly the propositions transferred from a Z3 model into the executable SMT
semantics.  This is the semantic premise used by `CertifiedZ3Model`, so the
production CEK success and error endpoints see no change. -/
theorem scriptWith_assertionsTrue_iff_fullPrelude (m : Moist.SMT.Semantics.Model)
    (decls : List SymDecl) (assertions : List SExpr) :
    (∀ expression, expression ∈ (scriptWith decls assertions).assertions →
      Moist.SMT.Semantics.evalBoolIs m expression true = true) ↔
    (∀ expression,
      expression ∈ (scriptWithFullPrelude decls assertions).assertions →
        Moist.SMT.Semantics.evalBoolIs m expression true = true) := by
  rw [scriptWith_assertions, scriptWithFullPrelude_assertions]
  constructor
  · intro h expression hmember
    rcases List.mem_append.mp hmember with hassumption | hassertion
    · exact h expression (List.mem_append_left _ hassumption)
    · apply (groupedAssertions_true_iff m assertions).mp
        (fun grouped hgrouped =>
          h grouped (List.mem_append_right _ hgrouped))
      exact hassertion
  · intro h expression hmember
    rcases List.mem_append.mp hmember with hassumption | hgrouped
    · exact h expression (List.mem_append_left _ hassumption)
    · apply (groupedAssertions_true_iff m assertions).mpr
        (fun assertion hassertion =>
          h assertion (List.mem_append_right _ hassertion))
      exact hgrouped

/-- Exact assertion accounting for the standalone UPLC assertion
satisfiability query. -/
theorem scriptForAssertionsSatisfiable_assertions
    (decls : List SymDecl) (assertions : List UplcAssertion) :
    (scriptForAssertionsSatisfiable decls assertions).assertions =
      decls.flatMap SymDecl.assumptions ++
        groupedAssertions (uplcAssertionConditions decls assertions) := by
  exact scriptWith_assertions _ _

/-- Exact assertion accounting for a Boolean target restricted by UPLC
assertions.  Grouping is explicit so the solver-boundary proof must recover
each original predicate through `groupedAssertions_true_iff`. -/
theorem scriptForBoolTrueWithAssertions_assertions (fuel : Nat)
    (decls : List SymDecl) (assertions : List UplcAssertion) (t : Term) :
    (scriptForBoolTrueWithAssertions fuel decls assertions t).assertions =
      decls.flatMap SymDecl.assumptions ++ groupedAssertions
        (uplcAssertionConditions decls assertions ++
          [okBoolTrueCond (evalSym fuel (envOf decls) t)]) := by
  exact scriptWith_assertions _ _

/-- Exact assertion accounting for an integer target restricted by UPLC
assertions. -/
theorem scriptForIntEqWithAssertions_assertions (fuel : Nat)
    (decls : List SymDecl) (assertions : List UplcAssertion)
    (t : Term) (rhs : SExpr) :
    (scriptForIntEqWithAssertions fuel decls assertions t rhs).assertions =
      decls.flatMap SymDecl.assumptions ++ groupedAssertions
        (uplcAssertionConditions decls assertions ++
          [okIntEqCond (evalSym fuel (envOf decls) t) rhs]) := by
  exact scriptWith_assertions _ _

/-- Exact assertion accounting for an error target restricted by UPLC
assertions. -/
theorem scriptForErrorWithAssertions_assertions (fuel : Nat)
    (decls : List SymDecl) (assertions : List UplcAssertion) (t : Term) :
    (scriptForErrorWithAssertions fuel decls assertions t).assertions =
      decls.flatMap SymDecl.assumptions ++ groupedAssertions
        (uplcAssertionConditions decls assertions ++
          [errorCond (evalSym fuel (envOf decls) t)]) := by
  exact scriptWith_assertions _ _

/-- Generic exact accounting used by the proof-carrying asserted-query
boundary. -/
theorem scriptForWithAssertions_assertions
    (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (decls : List SymDecl) (assertions : List UplcAssertion) (t : Term) :
    (Moist.SMT.Compiler.scriptForWithAssertions
      kind fuel decls assertions t).assertions =
      decls.flatMap SymDecl.assumptions ++ groupedAssertions
        (uplcAssertionConditions decls assertions ++
          [Moist.SMT.Compiler.queryCondition kind
            (evalSym fuel (envOf decls) t)]) := by
  exact scriptWith_assertions _ _

/-- The coupled compiler reuses conditions operationally but produces the
same canonical non-vacuity script as the standalone constructor. -/
@[simp] theorem scriptsForWithAssertions_satisfiability
    (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (decls : List SymDecl) (assertions : List UplcAssertion) (t : Term) :
    (Moist.SMT.Compiler.scriptsForWithAssertions
      kind fuel decls assertions t).satisfiability =
      scriptForAssertionsSatisfiable decls assertions := by
  rfl

/-- The target half of the coupled compiler is exactly the existing canonical
asserted target script. -/
@[simp] theorem scriptsForWithAssertions_target
    (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (decls : List SymDecl) (assertions : List UplcAssertion) (t : Term) :
    (Moist.SMT.Compiler.scriptsForWithAssertions
      kind fuel decls assertions t).target =
      Moist.SMT.Compiler.scriptForWithAssertions
        kind fuel decls assertions t := by
  rfl

theorem scriptForBoolTrue_assertions (fuel : Nat) (decls : List SymDecl) (t : Term) :
    (scriptForBoolTrue fuel decls t).assertions =
      decls.flatMap SymDecl.assumptions ++
        [okBoolTrueCond (evalSym fuel (envOf decls) t)] := by
  rw [scriptForBoolTrue,
    scriptForBoolTrueWithAssertions_assertions]
  rfl

theorem scriptForIntEq_assertions (fuel : Nat) (decls : List SymDecl)
    (t : Term) (rhs : SExpr) :
    (scriptForIntEq fuel decls t rhs).assertions =
      decls.flatMap SymDecl.assumptions ++
        [okIntEqCond (evalSym fuel (envOf decls) t) rhs] := by
  rw [scriptForIntEq,
    scriptForIntEqWithAssertions_assertions]
  rfl

theorem scriptForError_assertions (fuel : Nat) (decls : List SymDecl) (t : Term) :
    (scriptForError fuel decls t).assertions =
      decls.flatMap SymDecl.assumptions ++
        [errorCond (evalSym fuel (envOf decls) t)] := by
  rw [scriptForError,
    scriptForErrorWithAssertions_assertions]
  rfl

end Moist.SMT.UPLC
