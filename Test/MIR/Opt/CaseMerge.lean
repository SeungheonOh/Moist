import Test.MIR.Helpers
import Moist.MIR.Optimize

namespace Test.MIR.Opt.CaseMerge

open Moist.MIR
open Test.MIR
open Test.Framework

/-! ## Extra fixtures for case merge tests (uids 70+) -/

private def f0 : VarId := ⟨70, "f0"⟩
private def f1 : VarId := ⟨71, "f1"⟩
private def f2 : VarId := ⟨72, "f2"⟩
private def f3 : VarId := ⟨73, "f3"⟩
private def g0 : VarId := ⟨74, "g0"⟩
private def g1 : VarId := ⟨75, "g1"⟩
private def g2 : VarId := ⟨76, "g2"⟩
private def g3 : VarId := ⟨77, "g3"⟩
private def t1 : VarId := ⟨80, "t1"⟩
private def t2 : VarId := ⟨81, "t2"⟩
private def r  : VarId := ⟨82, "r"⟩

def tests : TestTree := suite "caseMerge" do
  -- Basic: two cases on the same scrutinee, single constructor
  test "cm_basic_two_cases" do
    -- let t1 = case x of [λf0 f1. f0]
    -- let t2 = case x of [λg0 g1. g1]
    -- in addInteger t1 t2
    -- Should merge into:
    -- case x of [λf0 f1. addInteger f0 f1]
    let e := Expr.Let
      [(t1, .Case (.Var x) [.Lam f0 (.Lam f1 (.Var f0))], false),
       (t2, .Case (.Var x) [.Lam g0 (.Lam g1 (.Var g1))], false)]
      (.App (.App (.Builtin .AddInteger) (.Var t1)) (.Var t2))
    let (result, changed) := caseMergePass e
    check "cm_basic_two_cases_changed" changed
    -- Verify no more Let at top level (absorbed into case branch)
    match result with
    | .Case (.Var scrutVar) _ => check "cm_basic_scrutinee" (scrutVar == x)
    | _ => throw (.userError "cm_basic: expected Case at top, got something else")

  -- Two constructors: case with two alts, two projections
  test "cm_two_ctors" do
    -- let t1 = case x of [λa0. a0, λb0 b1. b0]
    -- let t2 = case x of [λc0. c0, λd0 d1. d1]
    -- in constr 0 [t1, t2]
    let e := Expr.Let
      [(t1, .Case (.Var x) [.Lam f0 (.Var f0), .Lam f0 (.Lam f1 (.Var f0))], false),
       (t2, .Case (.Var x) [.Lam g0 (.Var g0), .Lam g0 (.Lam g1 (.Var g1))], false)]
      (.Constr 0 [.Var t1, .Var t2])
    let (result, changed) := caseMergePass e
    check "cm_two_ctors_changed" changed
    match result with
    | .Case (.Var scrutVar) alts =>
      check "cm_two_ctors_scrutinee" (scrutVar == x)
      check "cm_two_ctors_two_alts" (alts.length == 2)
    | _ => throw (.userError "cm_two_ctors: expected Case at top")

  -- Noop: cases on different scrutinees
  test "cm_different_scrutinees" do
    let e := Expr.Let
      [(t1, .Case (.Var x) [.Lam f0 (.Var f0)], false),
       (t2, .Case (.Var y) [.Lam g0 (.Var g0)], false)]
      (.App (.Var t1) (.Var t2))
    let (_, changed) := caseMergePass e
    check "cm_different_scrutinees_unchanged" (!changed)

  -- Noop: single case binding (no duplicate)
  test "cm_single_case" do
    let e := Expr.Let
      [(t1, .Case (.Var x) [.Lam f0 (.Var f0)], false)]
      (.Var t1)
    let (_, changed) := caseMergePass e
    check "cm_single_case_unchanged" (!changed)

  -- Bindings between cases are absorbed
  test "cm_bindings_between" do
    -- let t1 = case x of [λf0 f1. f0]
    -- let r  = addInteger t1 (lit 1)
    -- let t2 = case x of [λg0 g1. g1]
    -- in addInteger r t2
    let e := Expr.Let
      [(t1, .Case (.Var x) [.Lam f0 (.Lam f1 (.Var f0))], false),
       (r,  .App (.App (.Builtin .AddInteger) (.Var t1)) (intLit 1), false),
       (t2, .Case (.Var x) [.Lam g0 (.Lam g1 (.Var g1))], false)]
      (.App (.App (.Builtin .AddInteger) (.Var r)) (.Var t2))
    let (result, changed) := caseMergePass e
    check "cm_bindings_between_changed" changed
    -- The intermediate binding r should be absorbed into the case branch
    match result with
    | .Case (.Var scrutVar) _ => check "cm_bindings_between_scrutinee" (scrutVar == x)
    | _ => throw (.userError "cm_bindings_between: expected Case at top")

  -- Bindings before the first case are preserved
  test "cm_bindings_before" do
    -- let r  = addInteger (lit 1) (lit 2)
    -- let t1 = case x of [λf0. f0]
    -- let t2 = case x of [λg0. g0]
    -- in addInteger r (addInteger t1 t2)
    let e := Expr.Let
      [(r,  .App (.App (.Builtin .AddInteger) (intLit 1)) (intLit 2), false),
       (t1, .Case (.Var x) [.Lam f0 (.Var f0)], false),
       (t2, .Case (.Var x) [.Lam g0 (.Var g0)], false)]
      (.App (.App (.Builtin .AddInteger) (.Var r))
        (.App (.App (.Builtin .AddInteger) (.Var t1)) (.Var t2)))
    let (result, changed) := caseMergePass e
    check "cm_bindings_before_changed" changed
    -- The r binding should stay as a Let before the case
    match result with
    | .Let _ (.Case (.Var scrutVar) _) => check "cm_bindings_before_scrutinee" (scrutVar == x)
    | _ => throw (.userError "cm_bindings_before: expected Let wrapping Case")

  -- Shadowed scrutinee: scrutinee rebound before second case
  test "cm_scrutinee_shadowed" do
    -- let t1 = case x of [λf0. f0]
    -- let x  = lit 42       <-- shadows x
    -- let t2 = case x of [λg0. g0]
    -- in addInteger t1 t2
    let e := Expr.Let
      [(t1, .Case (.Var x) [.Lam f0 (.Var f0)], false),
       (x,  intLit 42, false),
       (t2, .Case (.Var x) [.Lam g0 (.Var g0)], false)]
      (.App (.App (.Builtin .AddInteger) (.Var t1)) (.Var t2))
    let (_, changed) := caseMergePass e
    -- hasDuplicateCase stops when scrutinee is rebound, so no merge
    check "cm_scrutinee_shadowed_unchanged" (!changed)

  -- Case-of-known-ctor inside a case branch body
  test "cm_known_ctor_resolution" do
    -- let t1 = case x of [λf0 f1. f0, λf0 f1 f2. f2]
    -- let t2 = case x of [λg0 g1. g1, λg0 g1 g2. g0]
    -- in constr 0 [t1, t2]
    -- After merge, in ctor-0 branch: case(x) resolves to alt 0 with known fields
    -- In ctor-1 branch: case(x) resolves to alt 1 with known fields
    let e := Expr.Let
      [(t1, .Case (.Var x)
        [.Lam f0 (.Lam f1 (.Var f0)),
         .Lam f0 (.Lam f1 (.Lam f2 (.Var f2)))], false),
       (t2, .Case (.Var x)
        [.Lam g0 (.Lam g1 (.Var g1)),
         .Lam g0 (.Lam g1 (.Lam g2 (.Var g0)))], false)]
      (.Constr 0 [.Var t1, .Var t2])
    let (result, changed) := caseMergePass e
    check "cm_known_ctor_changed" changed
    match result with
    | .Case (.Var scrutVar) alts =>
      check "cm_known_ctor_scrutinee" (scrutVar == x)
      check "cm_known_ctor_two_alts" (alts.length == 2)
    | _ => throw (.userError "cm_known_ctor: expected Case at top")

  -- Three cases on the same scrutinee (triple merge)
  test "cm_triple_case" do
    let t3 : VarId := ⟨83, "t3"⟩
    let h0 : VarId := ⟨84, "h0"⟩
    let h1 : VarId := ⟨85, "h1"⟩
    let e := Expr.Let
      [(t1, .Case (.Var x) [.Lam f0 (.Lam f1 (.Var f0))], false),
       (t2, .Case (.Var x) [.Lam g0 (.Lam g1 (.Var g1))], false),
       (t3, .Case (.Var x) [.Lam h0 (.Lam h1
         (.App (.App (.Builtin .AddInteger) (.Var h0)) (.Var h1)))], false)]
      (.Constr 0 [.Var t1, .Var t2, .Var t3])
    let (result, changed) := caseMergePass e
    check "cm_triple_case_changed" changed
    match result with
    | .Case (.Var scrutVar) _ => check "cm_triple_case_scrutinee" (scrutVar == x)
    | _ => throw (.userError "cm_triple_case: expected Case at top")

  -- Non-case binding as first binding, cases after
  test "cm_non_case_first" do
    let e := Expr.Let
      [(r,  intLit 100, false),
       (t1, .Case (.Var x) [.Lam f0 (.Var f0)], false),
       (t2, .Case (.Var x) [.Lam g0 (.App (.App (.Builtin .AddInteger) (.Var g0)) (.Var r))], false)]
      (.App (.App (.Builtin .AddInteger) (.Var t1)) (.Var t2))
    let (result, changed) := caseMergePass e
    check "cm_non_case_first_changed" changed
    match result with
    | .Let binds (.Case _ _) =>
      -- The lit binding should be before the case
      check "cm_non_case_first_prefix" (binds.length == 1)
    | _ => throw (.userError "cm_non_case_first: expected Let wrapping Case")

  -- Recurse into nested structures: case merge inside a Lam body
  test "cm_recurse_lam" do
    let e := Expr.Lam z
      (.Let
        [(t1, .Case (.Var x) [.Lam f0 (.Var f0)], false),
         (t2, .Case (.Var x) [.Lam g0 (.App (.Var g0) (.Var z))], false)]
        (.App (.Var t1) (.Var t2)))
    let (_, changed) := caseMergePass e
    check "cm_recurse_lam_changed" changed

  -- Recurse into nested structures: case merge inside Fix body
  test "cm_recurse_fix" do
    let e := Expr.Fix f
      (.Let
        [(t1, .Case (.Var x) [.Lam f0 (.Var f0)], false),
         (t2, .Case (.Var x) [.Lam g0 (.App (.Var f) (.Var g0))], false)]
        (.App (.Var t1) (.Var t2)))
    let (_, changed) := caseMergePass e
    check "cm_recurse_fix_changed" changed

  -- Recurse into Let RHS: case merge inside a binding RHS
  test "cm_recurse_let_rhs" do
    let e := Expr.Let
      [(r, .Let
        [(t1, .Case (.Var x) [.Lam f0 (.Var f0)], false),
         (t2, .Case (.Var x) [.Lam g0 (.Var g0)], false)]
        (.App (.Var t1) (.Var t2)), false)]
      (.Var r)
    let (_, changed) := caseMergePass e
    check "cm_recurse_let_rhs_changed" changed

  -- Leaves are unchanged
  test "cm_leaves_unchanged" do
    for (name, e) in [("cm_var", Expr.Var x), ("cm_lit", intLit 42),
                       ("cm_builtin", Expr.Builtin .AddInteger), ("cm_error", Expr.Error)] do
      let (_, ch) := caseMergePass e
      check s!"{name}_unchanged" (!ch)

  -- Case with non-Var scrutinee is not mergeable
  test "cm_non_var_scrutinee" do
    let e := Expr.Let
      [(t1, .Case (.App (.Var f) (.Var x)) [.Lam f0 (.Var f0)], false),
       (t2, .Case (.App (.Var f) (.Var x)) [.Lam g0 (.Var g0)], false)]
      (.App (.Var t1) (.Var t2))
    let (_, changed) := caseMergePass e
    -- findFirstMergeableCase only looks for Case (Var x), not Case (App ...)
    check "cm_non_var_scrutinee_unchanged" (!changed)

end Test.MIR.Opt.CaseMerge
