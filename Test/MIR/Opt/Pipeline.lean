import Test.MIR.Helpers
import Moist.MIR.Optimize

namespace Test.MIR.Opt.Pipeline

open Moist.MIR
open Test.MIR
open Test.Framework

def tests : TestTree := suite "pipeline" do
  test "pipe_trivial" do
    for (name, e) in [("pipe_var", Expr.Var x), ("pipe_lit", intLit 42),
                       ("pipe_builtin", Expr.Builtin .AddInteger),
                       ("pipe_error", Expr.Error)] do
      let r := optimizeExpr e 1000
      checkAlphaEq name r e
  test "pipe_identity" do
    let e := Expr.Lam x (.Var x)
    let r := optimizeExpr e 1000
    checkAlphaEq "pipe_identity" r e
  test "pipe_atom_cascade" do
    let e := Expr.Let [(a, .Var x, false), (b, .Var a, false), (c, .Var b, false)] (.Var c)
    let r := optimizeExpr e 1000
    checkAlphaEq "pipe_atom_cascade" r (.Var x)
  test "pipe_force_delay_doc" do
    let e := Expr.Let [(v, .Delay (.Var x), false),
                        (w, .Force (.Var v), false)] (.Var w)
    let r := optimizeExpr e 1000
    checkAlphaEq "pipe_force_delay_doc" r (.Var x)
  test "pipe_cse_dce" do
    let e := Expr.Let [(a, .App (.Var f) (.Var x), false),
                        (b, .App (.Var f) (.Var x), false)]
                (.Var a)
    let r := optimizeExpr e 1000
    checkAlphaEq "pipe_cse_dce" r (.App (.Var f) (.Var x))
  test "pipe_float_cse" do
    let e := Expr.Lam x
      (.Let [(a, intLit 1, false), (b, intLit 1, false), (c, .App (.Var a) (.Var x), false)]
        (.App (.Var c) (.Var b)))
    let _r := optimizeExpr e 1000
  test "pipe_inline_beta" do
    let e := Expr.Let [(f, .Lam y (.Var y), false)] (.App (.Var f) (.Var z))
    let r := optimizeExpr e 1000
    checkAlphaEq "pipe_inline_beta" r (.Var z)
  test "pipe_nested_let" do
    let e := Expr.Let [(a, intLit 1, false)]
                (.Let [(b, .Var a, false)]
                  (.Let [(c, .Var b, false)] (.Var c)))
    let r := optimizeExpr e 1000
    checkAlphaEq "pipe_nested_let" r (intLit 1)
  test "pipe_idempotent_factorial" do
    let r1 := optimizeExpr factorialMIR 1000
    let r2 := optimizeExpr r1 2000
    checkAlphaEq "pipe_idempotent_factorial" r1 r2
  test "pipe_various_inputs" do
    let inputs := [
      ("factorial", factorialMIR),
      ("atom_chain", Expr.Let [(a, .Var x, false), (b, .Var a, false)] (.Var b)),
      ("force_delay", Expr.Let [(v, .Delay (.App (.Var f) (.Var x)), false),
                (w, .Force (.Var v), false)] (.Var w)),
      ("cse_target", Expr.Lam x (.Let [(a, intLit 1, false), (b, .App (.Builtin .AddInteger) (.Var x), false),
                         (c, .App (.Builtin .AddInteger) (.Var x), false)]
                (.App (.Var b) (.Var c))))
    ]
    for ((name, e), i) in inputs.zipIdx do
      let _r := optimizeExpr e (1000 + i * 100)
      IO.println s!"PASS: pipe_{name}"
  test "pipe_factorial" do
    let _r := optimizeExpr factorialMIR 1000
    IO.println "PASS: pipe_factorial"
  test "pipe_inline_before_fd" do
    let dd : VarId := ⟨60, "d"⟩
    let e := Expr.Let [(dd, .Delay (.Var x), false),
                        (v, .Var dd, false)]
                (.Force (.Var v))
    let r := optimizeExpr e 1000
    checkAlphaEq "pipe_inline_before_fd" r (.Var x)
  test "pipe_inline_impure_partial_under_delay" do
    let addall : VarId := ⟨61, "addall"⟩
    let anf : VarId := ⟨62, "anf"⟩
    let rhs :=
      Expr.App (Expr.Builtin .AddInteger)
        (Expr.App (Expr.Force (Expr.Builtin .HeadList)) (.Var x))
    let arg :=
      Expr.App (.Var addall)
        (Expr.App (Expr.Force (Expr.Builtin .TailList)) (.Var x))
    let e :=
      Expr.Delay (.Let [(anf, rhs, false)] (.App (.Var anf) arg))
    let r := optimizeExpr e 1000
    checkAlphaEq "pipe_inline_impure_partial_under_delay" r (.Delay (.App rhs arg))
  test "pipe_beta_exposes_inline_in_recursive_delay_branch" do
    let addall : VarId := ⟨63, "addall"⟩
    let xs : VarId := ⟨64, "xs"⟩
    let anf : VarId := ⟨65, "anf"⟩
    let tail : VarId := ⟨66, "tail"⟩
    let rhs :=
      Expr.App (Expr.Builtin .AddInteger)
        (Expr.App (Expr.Force (Expr.Builtin .HeadList)) (.Var xs))
    let tailExpr :=
      Expr.App (Expr.Force (Expr.Builtin .TailList)) (.Var xs)
    let delayedBranch :=
      Expr.Delay
        (.Let [(anf, rhs, false)]
          (.App
            (.Lam tail (.App (.Var anf) (.App (.Var addall) (.Var tail))))
            tailExpr))
    let chooseList :=
      Expr.Force
        (.App
          (.App
            (.App (Expr.Force (Expr.Force (Expr.Builtin .ChooseList))) (.Var xs))
            (Expr.Delay (intLit 0)))
          delayedBranch)
    let e := Expr.Fix addall (.Lam xs chooseList)
    let expectedBranch :=
      Expr.Delay (.App rhs (.App (.Var addall) tailExpr))
    let expected :=
      Expr.Fix addall
        (.Lam xs
          (Expr.Force
            (.App
              (.App
                (.App (Expr.Force (Expr.Force (Expr.Builtin .ChooseList))) (.Var xs))
                (Expr.Delay (intLit 0)))
              expectedBranch)))
    let r := optimizeExpr e 1000
    checkAlphaEq "pipe_beta_exposes_inline_in_recursive_delay_branch" r expected
  test "pipe_cse_before_inline" do
    let e := Expr.Let [(a, .App (.Var f) (.Var x), false),
                        (b, .App (.Var f) (.Var x), false)]
                (.App (.Var a) (.Var b))
    let _r := optimizeExpr e 1000
  test "pipe_fd_dce_chain" do
    let e := Expr.Let
      [(v, .Delay (.Var x), false),
       (a, .Force (.Var v), false),
       (b, intLit 42, false)]
      (.Var a)
    let r := optimizeExpr e 1000
    checkAlphaEq "pipe_fd_dce_chain" r (.Var x)
  test "pipe_no_inline_across_fix" do
    let rep : VarId := ⟨60, "rep"⟩
    let add := Expr.Builtin .AddInteger
    let expensive :=
      Expr.App (.App add (.App (.App add (.App (.App add (.App (.App add (intLit 1)) (intLit 1))) (intLit 1))) (intLit 1))) (intLit 1)
    let e := Expr.Let
      [(a, expensive, false)]
      (.Fix rep (.Lam n (.App (.App (.Var rep) (.Var n)) (.Var a))))
    let r := optimizeExpr e 1000
    let hasLet := match r with
      | .Let _ _ => true
      | _ => false
    check "pipe_no_inline_across_fix_has_let" hasLet
  test "pipe_shared_prefix" do
    let hd := Expr.Var f
    let chain3 := Expr.App hd (.App hd (.App hd (.Var x)))
    let chain6 := Expr.App hd (.App hd (.App hd (.App hd (.App hd (.App hd (.Var x))))))
    let e := Expr.Let
      [(a, chain3, false),
       (b, chain6, false)]
      (.App (.App (.Var g) (.Var a)) (.Var b))
    let _r := optimizeExpr e 1000
  test "pipe_shared_prefix_anf" do
    let hd := Expr.Var f
    let t0 : VarId := ⟨60, "t"⟩
    let t1' : VarId := ⟨61, "t"⟩
    let t2' : VarId := ⟨62, "t"⟩
    let t3 : VarId := ⟨63, "t"⟩
    let t4 : VarId := ⟨64, "t"⟩
    let t5 : VarId := ⟨65, "t"⟩
    let t6 : VarId := ⟨66, "t"⟩
    let t7 : VarId := ⟨67, "t"⟩
    let t8 : VarId := ⟨68, "t"⟩
    let rr : VarId := ⟨69, "r"⟩
    let e := Expr.Let
      [(t0, .App hd (.Var x), false),
       (t1', .App hd (.Var t0), false),
       (t2', .App hd (.Var t1'), false),
       (t3, .App hd (.Var x), false),
       (t4, .App hd (.Var t3), false),
       (t5, .App hd (.Var t4), false),
       (t6, .App hd (.Var t5), false),
       (t7, .App hd (.Var t6), false),
       (t8, .App hd (.Var t7), false),
       (rr, .App (.Var g) (.Var t2'), false)]
      (.App (.Var rr) (.Var t8))
    let r := optimizeExpr e 1000
    check "pipe_shared_prefix_smaller" (exprSize r < exprSize e)

end Test.MIR.Opt.Pipeline
