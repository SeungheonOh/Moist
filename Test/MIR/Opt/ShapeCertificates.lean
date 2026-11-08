import Moist.Verified.ShapesSoundness

/-- Tests evaluate under semantics variant E (the conformance-suite variant). -/
private local instance testSemVariant : Moist.CEK.SemVariant := .E

/-! # Generated binder capture in shape-checked dead code elimination

When the branches of a case on a known Boolean agree and the scrutinee may
fail, the simplifier keeps the scrutinee's evaluation in a fresh binding. The
binder used to be fresh only for the rewritten case (`maxUidExpr result + 1`).
It could therefore coincide with a binder of the enclosing program. The
rewritten right-hand side is recorded as a fact, and the Boolean result
analysis of a later case read the generated binding as a definition of the
captured outer name, wrongly classifying the scrutinee as a Boolean.

Below, `g` (uid 58) holds the integer `5`, `a` is bound to `g`, and the case
binding `x` has branches `a` and `a`; its rewritten form is
`let g = (unIData (I 1) == 1) in a`. The final case on `x` was then accepted
as a case on a Boolean with equal branches and replaced by `0`, although `x`
is the integer `5` and the original program fails.

The simplifier now draws generated binders above every binder of its input
(`base = maxUidExpr unique + 1`), which `shapeDCE_refines` relies on.
-/

namespace Test.MIR.Opt.ShapeCertificates

open Moist.CEK Moist.Plutus.Term Moist.Verified.Equivalence
open Moist.MIR

def g : VarId := ⟨58, .gen, "g"⟩
def a : VarId := ⟨57, .gen, "a"⟩
def x : VarId := ⟨59, .gen, "x"⟩

/-- A Boolean test whose integer operand is not known to be total. -/
def test : Expr :=
  .App (.App (.Builtin .EqualsInteger)
      (.App (.Builtin .UnIData) (.Lit (.Data (.I 1), .AtomicType .TypeData))))
    (.Lit (.Integer 1, .AtomicType .TypeInteger))

def zero : Expr := .Lit (.Integer 0, .AtomicType .TypeInteger)

def source : Expr :=
  .Let [(g, .Lit (.Integer 5, .AtomicType .TypeInteger), false), (a, .Var g, false),
      (x, .Case test [.Var a, .Var a], false)]
    (.Case (.Var x) [zero, zero])

/-- The output of the former binder choice: the checked binding reuses `g`. -/
def capturedOutput : Expr :=
  .Let [(g, .Lit (.Integer 5, .AtomicType .TypeInteger), false), (a, .Var g, false),
      (x, .Let [(⟨58, .gen, "checked"⟩, test, false)] (.Var a), false)]
    zero

/-- The former generated binder coincides with `g`. -/
theorem former_checked_binder_is_g :
    ((⟨maxUidExpr (.Case test [.Var a, .Var a]) + 1, .gen, "checked"⟩ : VarId) == g) = true := by
  simp [maxUidExpr, maxUidExprList, test, a, g, VarId.beq_true_iff]

def testTerm : Term :=
  .Apply (.Apply (.Builtin .EqualsInteger)
      (.Apply (.Builtin .UnIData) (.Constant (.Data (.I 1), .AtomicType .TypeData))))
    (.Constant (.Integer 1, .AtomicType .TypeInteger))

def zeroTerm : Term := .Constant (.Integer 0, .AtomicType .TypeInteger)

def sourceTerm : Term :=
  .Apply (.Lam 0 (.Apply (.Lam 0 (.Apply (.Lam 0 (.Case (.Var 1) [zeroTerm, zeroTerm]))
      (.Case testTerm [.Var 1, .Var 1])))
    (.Var 1))) (.Constant (.Integer 5, .AtomicType .TypeInteger))

def capturedTerm : Term :=
  .Apply (.Lam 0 (.Apply (.Lam 0 (.Apply (.Lam 0 zeroTerm) (.Apply (.Lam 0 (.Var 2)) testTerm)))
    (.Var 1))) (.Constant (.Integer 5, .AtomicType .TypeInteger))

theorem source_lowers : lowerTotalExpr [] source = some sourceTerm := by
  simp [source, sourceTerm, test, testTerm, zero, zeroTerm, lowerTotalExpr, expandFix, expandFixBinds,
    expandFixList, lowerTotal, lowerTotalLet, lowerTotalList, envLookupT, envLookupT.go, g, a, x, VarId.beq_true_iff]

theorem captured_lowers : lowerTotalExpr [] capturedOutput = some capturedTerm := by
  simp [capturedOutput, capturedTerm, test, testTerm, zero, zeroTerm, lowerTotalExpr, expandFix,
    expandFixBinds, lowerTotal, lowerTotalLet, envLookupT, envLookupT.go, g, a, x, VarId.beq_true_iff]

theorem source_errors : Reaches (.compute [] .nil sourceTerm) .error := ⟨40, rfl⟩

theorem captured_halts : Reaches (.compute [] .nil capturedTerm) (.halt (.VCon (.Integer 0))) := ⟨40, rfl⟩

theorem captured_term_not_refines : ¬Moist.Verified.Contextual.CtxRefines sourceTerm capturedTerm := by
  intro refines
  have errors := (refines .Hole (by simp [Moist.Verified.Contextual.fill, sourceTerm, testTerm, zeroTerm,
    Moist.Verified.closedAt, Moist.Verified.closedAtList])).2.error source_errors
  change Reaches (.compute [] .nil capturedTerm) .error at errors
  obtain ⟨fuel, returned⟩ := captured_halts
  have after := (Moist.Verified.AdvancedRefinement.reaches_after_prefix fuel rfl).mp errors
  rw [returned] at after
  obtain ⟨remaining, impossible⟩ := after
  have fixed : ∀ count value, steps count (.halt value) = .halt value := by
    intro count value
    induction count with
    | zero => rfl
    | succ count inductionHypothesis => exact inductionHypothesis
  rw [fixed] at impossible
  contradiction

/-- The output produced with the former binder choice does not refine the
    source program. -/
theorem checked_binder_capture_not_refines :
    ¬Moist.Verified.MIR.MIRCtxRefines source capturedOutput := by
  intro refines
  have := (refines []).2
  rw [source_lowers, captured_lowers] at this
  exact captured_term_not_refines this

/-- The corrected binder lies above every binder of the input. -/
theorem corrected_checked_binder_avoids_input :
    ((⟨max (maxUidExpr source + 1) (maxUidExpr (.Case test [.Var a, .Var a]) + 1), .gen, "checked"⟩ :
      VarId) == g) = false := by
  simp [source, maxUidExpr, maxUidExprList, maxUidExprBinds, test, zero, a, g, x, VarId.beq_false_iff]

end Test.MIR.Opt.ShapeCertificates
