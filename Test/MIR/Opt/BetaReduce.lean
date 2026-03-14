import Test.MIR.Helpers
import Moist.MIR.Optimize

namespace Test.MIR.Opt.BetaReduce

open Moist.MIR
open Test.MIR
open Test.Framework

def tests : TestTree := suite "betaReduce" do
  -- Atomic arg: (λx. body) (Var z) → subst x z body
  test "beta_atomic_var" do
    let e := Expr.App (.Lam x (.App (.Var x) (.Var x))) (.Var z)
    let (r, ch) := runFresh (betaReducePass e) 1000
    checkAlphaEq "beta_atomic_var" r (.App (.Var z) (.Var z))
    check "beta_atomic_var_changed" ch

  -- Atomic arg: literal
  test "beta_atomic_lit" do
    let e := Expr.App (.Lam x (.Var x)) (intLit 42)
    let (r, ch) := runFresh (betaReducePass e) 1000
    checkAlphaEq "beta_atomic_lit" r (intLit 42)
    check "beta_atomic_lit_changed" ch

  -- Atomic arg: builtin
  test "beta_atomic_builtin" do
    let e := Expr.App (.Lam x (.App (.Var x) (.Var y))) (.Builtin .AddInteger)
    let (r, ch) := runFresh (betaReducePass e) 1000
    checkAlphaEq "beta_atomic_builtin" r (.App (.Builtin .AddInteger) (.Var y))
    check "beta_atomic_builtin_changed" ch

  -- Non-atomic arg: (λx. body) (App f y) → Let [(x, App f y)] body
  test "beta_nonatomic" do
    let e := Expr.App (.Lam x (.Var x)) (.App (.Var f) (.Var y))
    let (r, ch) := runFresh (betaReducePass e) 1000
    let expected := Expr.Let [(x, .App (.Var f) (.Var y), false)] (.Var x)
    checkAlphaEq "beta_nonatomic" r expected
    check "beta_nonatomic_changed" ch

  -- Non-atomic arg with complex body
  test "beta_nonatomic_complex_body" do
    let e := Expr.App
      (.Lam x (.App (.App (.Builtin .AddInteger) (.Var x)) (.Var x)))
      (.App (.Var f) (.Var y))
    let (r, ch) := runFresh (betaReducePass e) 1000
    -- Should become: Let [(x, App f y)] (App (App addInteger x) x)
    match r with
    | .Let [(_v, .App (.Var f') (.Var y'), false)] _ =>
      check "beta_nonatomic_complex_rhs" (f' == f && y' == y)
      check "beta_nonatomic_complex_changed" ch
    | _ => throw (.userError s!"expected Let, got: {pretty r}")

  -- No beta: App with non-Lam head
  test "beta_non_lam_head" do
    let e := Expr.App (.Var f) (.Var x)
    let (r, ch) := runFresh (betaReducePass e) 1000
    checkAlphaEq "beta_non_lam_head" r e
    check "beta_non_lam_head_unchanged" (!ch)

  -- Nested beta redex: both reduced (inside-out)
  test "beta_nested" do
    -- (λa. (λb. b) a) z → (λb. b) z → z
    -- inner: (λb. b) applied to (Var a) → Var a
    -- then outer: (λa. Var a) applied to (Var z) → Var z
    let e := Expr.App (.Lam a (.App (.Lam b (.Var b)) (.Var a))) (.Var z)
    let (r, ch) := runFresh (betaReducePass e) 1000
    checkAlphaEq "beta_nested" r (.Var z)
    check "beta_nested_changed" ch

  -- Beta inside Lam body
  test "beta_inside_lam" do
    let e := Expr.Lam z (.App (.Lam x (.Var x)) (.Var z))
    let (r, ch) := runFresh (betaReducePass e) 1000
    checkAlphaEq "beta_inside_lam" r (.Lam z (.Var z))
    check "beta_inside_lam_changed" ch

  -- Beta inside Fix body
  test "beta_inside_fix" do
    let e := Expr.Fix f (.App (.Lam x (.App (.Var f) (.Var x))) (.Var y))
    let (r, ch) := runFresh (betaReducePass e) 1000
    checkAlphaEq "beta_inside_fix" r (.Fix f (.App (.Var f) (.Var y)))
    check "beta_inside_fix_changed" ch

  -- Beta inside Force
  test "beta_inside_force" do
    let e := Expr.Force (.App (.Lam x (.Var x)) (.Var y))
    let (r, ch) := runFresh (betaReducePass e) 1000
    checkAlphaEq "beta_inside_force" r (.Force (.Var y))
    check "beta_inside_force_changed" ch

  -- Beta inside Delay
  test "beta_inside_delay" do
    let e := Expr.Delay (.App (.Lam x (.Var x)) (.Var y))
    let (r, ch) := runFresh (betaReducePass e) 1000
    checkAlphaEq "beta_inside_delay" r (.Delay (.Var y))
    check "beta_inside_delay_changed" ch

  -- Beta inside Constr arg
  test "beta_inside_constr" do
    let e := Expr.Constr 0 [.App (.Lam x (.Var x)) (.Var y), .Var z]
    let (r, ch) := runFresh (betaReducePass e) 1000
    checkAlphaEq "beta_inside_constr" r (.Constr 0 [.Var y, .Var z])
    check "beta_inside_constr_changed" ch

  -- Beta inside Case scrutinee
  test "beta_inside_case_scrut" do
    let e := Expr.Case (.App (.Lam x (.Var x)) (.Var y)) [.Var z]
    let (r, ch) := runFresh (betaReducePass e) 1000
    checkAlphaEq "beta_inside_case_scrut" r (.Case (.Var y) [.Var z])
    check "beta_inside_case_scrut_changed" ch

  -- Beta inside Case alt
  test "beta_inside_case_alt" do
    let e := Expr.Case (.Var x) [.App (.Lam a (.Var a)) (.Var y)]
    let (r, ch) := runFresh (betaReducePass e) 1000
    checkAlphaEq "beta_inside_case_alt" r (.Case (.Var x) [.Var y])
    check "beta_inside_case_alt_changed" ch

  -- Beta inside Let RHS
  test "beta_inside_let_rhs" do
    let e := Expr.Let [(a, .App (.Lam x (.Var x)) (.Var y), false)] (.Var a)
    let (r, ch) := runFresh (betaReducePass e) 1000
    checkAlphaEq "beta_inside_let_rhs" r (.Let [(a, .Var y, false)] (.Var a))
    check "beta_inside_let_rhs_changed" ch

  -- Beta inside Let body
  test "beta_inside_let_body" do
    let e := Expr.Let [(a, intLit 1, false)]
      (.App (.Lam x (.App (.Var x) (.Var a))) (.Var y))
    let (r, ch) := runFresh (betaReducePass e) 1000
    checkAlphaEq "beta_inside_let_body" r
      (.Let [(a, intLit 1, false)] (.App (.Var y) (.Var a)))
    check "beta_inside_let_body_changed" ch

  -- Leaves are unchanged
  test "beta_leaves_unchanged" do
    for (name, e) in [("beta_var", Expr.Var x), ("beta_lit", intLit 42),
                       ("beta_builtin", Expr.Builtin .AddInteger), ("beta_error", Expr.Error)] do
      let (r, ch) := runFresh (betaReducePass e) 1000
      checkAlphaEq name r e
      check s!"{name}_unchanged" (!ch)

  -- Multiple beta redexes in same App spine: (λx. λy. body) a b
  -- After beta on outer: (λy. body[x:=a]) b → beta on inner
  test "beta_curried" do
    let e := Expr.App (.App (.Lam x (.Lam y (.App (.Var x) (.Var y)))) (.Var z)) (.Var w)
    let (r, ch) := runFresh (betaReducePass e) 1000
    -- Inner beta: (Lam x (Lam y (App x y))) applied to z → Lam y (App z y)
    -- Outer beta: (Lam y (App z y)) applied to w → App z w
    checkAlphaEq "beta_curried" r (.App (.Var z) (.Var w))
    check "beta_curried_changed" ch

end Test.MIR.Opt.BetaReduce
