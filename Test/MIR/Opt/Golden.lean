import Test.MIR.Helpers
import Moist.MIR.Optimize
import Test.Framework

namespace Test.MIR.Opt.Golden

open Moist.MIR
open Test.MIR
open Test.Framework

private def w : VarId := ⟨51, .source, "w"⟩
private def r : VarId := ⟨52, .source, "r"⟩

private def f0 : VarId := ⟨70, .source, "f0"⟩
private def f1 : VarId := ⟨71, .source, "f1"⟩
private def g0 : VarId := ⟨74, .source, "g0"⟩
private def g1 : VarId := ⟨75, .source, "g1"⟩
private def t1 : VarId := ⟨80, .source, "t1"⟩
private def t2 : VarId := ⟨81, .source, "t2"⟩

private def mkPassGolden (name : String) (input : Expr) (pass : Expr → Expr × Bool)
    : TreeBuilder Unit :=
  golden name <| pure <|
    let (result, changed) := pass input
    goldenSections [("output", pretty result), ("changed", s!"{changed}")]

private def mkInlineGolden (name : String) (input : Expr) (start : Nat := 1000)
    : TreeBuilder Unit :=
  golden name <| pure <|
    let (result, changed) := runFresh (inlinePass input) start
    goldenSections [("output", pretty result), ("changed", s!"{changed}")]

private def mkOptGolden (name : String) (input : Expr) (start : Nat := 1000)
    : TreeBuilder Unit :=
  golden name <| pure <|
    let result := optimizeExpr input start
    let isAnf := result.isANF
    goldenSections [("optimized", pretty result), ("isANF", s!"{isAnf}")]

private def mkBetaGolden (name : String) (input : Expr) (start : Nat := 1000)
    : TreeBuilder Unit :=
  golden name <| pure <|
    let (result, changed) := runFresh (betaReducePass input) start
    goldenSections [("output", pretty result), ("changed", s!"{changed}")]

private def mkEtaGolden (name : String) (input : Expr)
    : TreeBuilder Unit :=
  golden name <| pure <|
    let (result, changed) := etaReduce input
    goldenSections [("output", pretty result), ("changed", s!"{changed}")]

private def mkCaseMergeGolden (name : String) (input : Expr)
    : TreeBuilder Unit :=
  golden name <| pure <|
    let (result, changed) := caseMergePass input
    goldenSections [("output", pretty result), ("changed", s!"{changed}")]

def goldenTree : TestTree := suite "golden" do
  group "float" do
    mkPassGolden "opt_float_mixed"
      (Expr.Lam x
        (.Let [(a, intLit 1, false), (b, .App (.Var a) (.Var x), false)]
          (.App (.Var a) (.Var b))))
      floatOut
    mkPassGolden "opt_float_all"
      (Expr.Lam x (.Let [(a, intLit 1, false), (b, intLit 2, false)] (.Var x)))
      floatOut
    mkPassGolden "opt_float_seq_dep"
      (Expr.Lam x
        (.Let [(a, .App (.Var x) (.Var y), false), (b, .Var a, false), (c, intLit 1, false)]
          (.App (.Var b) (.Var c))))
      floatOut
    mkPassGolden "opt_float_fix"
      (Expr.Fix f (.Let [(a, intLit 1, false)] (.Lam x (.App (.Var f) (.Var a)))))
      floatOut
    mkPassGolden "opt_float_noop"
      (Expr.Lam x (.Let [(a, .App (.Var x) (.Var x), false)] (.Var a)))
      floatOut
  group "cse" do
    mkPassGolden "opt_cse_dup_app"
      (Expr.Let [(a, .App (.Var f) (.Var x), false),
                 (b, .App (.Var f) (.Var x), false)]
        (.App (.Var a) (.Var b)))
      (cse [])
    mkPassGolden "opt_cse_triple"
      (Expr.Let [(a, .Force (.Var x), false),
                 (b, .Force (.Var x), false),
                 (c, .Force (.Var x), false)]
        (.Constr 0 [.Var a, .Var b, .Var c]))
      (cse [])
    mkPassGolden "opt_cse_propagate"
      (Expr.Let [(a, .App (.Var f) (.Var x), false),
                 (b, .App (.Var f) (.Var x), false),
                 (c, .App (.Var g) (.Var b), false)]
        (.Var c))
      (cse [])
    mkPassGolden "opt_cse_noop"
      (Expr.Let [(a, .App (.Var f) (.Var x), false),
                 (b, .App (.Var f) (.Var y), false)]
        (.App (.Var a) (.Var b)))
      (cse [])
  group "dce" do
    mkPassGolden "opt_dce_pure_unused"
      (Expr.Let [(a, intLit 42, false), (b, .App (.Var f) (.Var x), false)] (.Var b))
      dce
    mkPassGolden "opt_dce_transitive"
      (Expr.Let [(a, intLit 42, false), (b, .Lam y (.Var a), false)] (.Var z))
      dce
    mkPassGolden "opt_dce_impure_kept"
      (Expr.Let [(a, .App .Error (.Var x), false)] (.Var y))
      dce
    mkPassGolden "opt_dce_mixed"
      (Expr.Let [(a, intLit 1, false), (b, intLit 2, false), (c, intLit 3, false)]
        (.App (.Var a) (.Var c)))
      dce
    mkPassGolden "opt_dce_error_kept"
      (Expr.Let [(a, .Error, false)] (.Var x))
      dce
  group "fd" do
    mkPassGolden "opt_fd_direct"
      (Expr.Force (.Delay (.App (.Var f) (.Var x))))
      forceDelay
    mkPassGolden "opt_fd_through_let"
      (Expr.Let [(v, .Delay (.Var x), false)] (.Force (.Var v)))
      forceDelay
    mkPassGolden "opt_fd_multi_force"
      (Expr.Let [(v, .Delay (.Var x), false)]
        (.App (.Force (.Var v)) (.Force (.Var v))))
      forceDelay
    mkPassGolden "opt_fd_mixed_noop"
      (Expr.Let [(v, .Delay (.Var x), false)]
        (.App (.Var v) (.Force (.Var v))))
      forceDelay
    mkPassGolden "opt_fd_rest_binding"
      (Expr.Let [(v, .Delay (.Var x), false), (b, .Force (.Var v), false)] (.Var b))
      forceDelay
  group "inline" do
    mkInlineGolden "opt_inline_atom"
      (Expr.Let [(a, .Var x, false)] (.App (.Var a) (.Var a)))
    mkInlineGolden "opt_inline_small_lam"
      (Expr.Let [(a, .Lam y (.Var y), false)]
        (.App (.Var a) (.App (.Var a) (.Var z))))
    mkInlineGolden "opt_inline_large_single"
      (Expr.Let [(a, .Lam y (.App (.Var y) (.App (.Var y) (.App (.Var y) (.Var y)))), false)]
        (.App (.Var a) (.Var z)))
    mkInlineGolden "opt_inline_large_fix"
      (Expr.Let [(a, .Lam y (.App (.Var y) (.App (.Var y) (.App (.Var y) (.Var y)))), false)]
        (.Fix g (.App (.Var a) (.Var g))))
    mkInlineGolden "opt_inline_beta"
      (Expr.App (.Lam x (.App (.Var x) (.Var x))) (.Var z))
    mkInlineGolden "opt_inline_chain"
      (Expr.Let [(a, .Var x, false), (b, .Var a, false), (c, .Var b, false)] (.Var c))
  group "cm" do
    mkCaseMergeGolden "opt_cm_basic"
      (Expr.Let
        [(t1, .Case (.Var x) [.Lam f0 (.Lam f1 (.Var f0))], false),
         (t2, .Case (.Var x) [.Lam g0 (.Lam g1 (.Var g1))], false)]
        (.App (.App (.Builtin .AddInteger) (.Var t1)) (.Var t2)))
    mkCaseMergeGolden "opt_cm_two_ctors"
      (Expr.Let
        [(t1, .Case (.Var x) [.Lam f0 (.Var f0), .Lam f0 (.Lam f1 (.Var f0))], false),
         (t2, .Case (.Var x) [.Lam g0 (.Var g0), .Lam g0 (.Lam g1 (.Var g1))], false)]
        (.Constr 0 [.Var t1, .Var t2]))
    mkCaseMergeGolden "opt_cm_noop"
      (Expr.Let
        [(t1, .Case (.Var x) [.Lam f0 (.Var f0)], false),
         (t2, .Case (.Var y) [.Lam g0 (.Var g0)], false)]
        (.App (.Var t1) (.Var t2)))
    mkCaseMergeGolden "opt_cm_absorb"
      (Expr.Let
        [(t1, .Case (.Var x) [.Lam f0 (.Lam f1 (.Var f0))], false),
         (r,  .App (.App (.Builtin .AddInteger) (.Var t1)) (intLit 1), false),
         (t2, .Case (.Var x) [.Lam g0 (.Lam g1 (.Var g1))], false)]
        (.App (.App (.Builtin .AddInteger) (.Var r)) (.Var t2)))
  group "eta" do
    mkEtaGolden "opt_eta_simple"
      (Expr.Lam x (.App (.Var f) (.Var x)))
    mkEtaGolden "opt_eta_multi"
      (Expr.Lam a (.Lam b (.App (.App (.Var f) (.Var a)) (.Var b))))
    mkEtaGolden "opt_eta_partial"
      (Expr.Lam x (.Lam y (.App (.Var g) (.Var y))))
    mkEtaGolden "opt_eta_noop"
      (Expr.Lam x (.App (.App (.Builtin .AddInteger) (.Var x)) (.Var x)))
    mkEtaGolden "opt_eta_order_mismatch"
      (Expr.Lam x (.Lam y (.App (.App (.Builtin .AddInteger) (.Var y)) (.Var x))))
  group "beta" do
    mkBetaGolden "opt_beta_atomic"
      (Expr.App (.Lam x (.Var x)) (.Var z))
    mkBetaGolden "opt_beta_nonatomic"
      (Expr.App (.Lam x (.Var x)) (.App (.Var f) (.Var y)))
    mkBetaGolden "opt_beta_nested"
      (Expr.App (.Lam a (.App (.Lam b (.Var b)) (.Var a))) (.Var z))
    mkBetaGolden "opt_beta_noop"
      (Expr.App (.Var f) (.Var x))
  group "pipe" do
    mkOptGolden "opt_pipe_simple"
      (Expr.Lam x
        (.Let [(a, intLit 1, false),
               (b, .App (.Builtin .AddInteger) (.Var x), false),
               (c, .App (.Builtin .AddInteger) (.Var x), false)]
          (.App (.Var b) (.Var c))))
    mkOptGolden "opt_pipe_fd_chain"
      (Expr.Let [(v, .Delay (.Var x), false),
                 (w, .Force (.Var v), false)]
        (.Var w))
    mkOptGolden "opt_pipe_cascade"
      (Expr.Let [(a, .Var x, false), (b, .Var a, false), (c, .Var b, false)] (.Var c))
    mkOptGolden "opt_pipe_inline_beta"
      (Expr.Let [(f, .Lam y (.Var y), false)] (.App (.Var f) (.Var z)))
    mkOptGolden "opt_pipe_nested_let"
      (Expr.Let [(a, intLit 1, false)]
        (.Let [(b, .Var a, false)]
          (.Let [(c, .Var b, false)] (.Var c))))
    mkOptGolden "opt_pipe_ifthenelse"
      (Expr.Force (.App (.App (.App (.Builtin .IfThenElse) (.Var x))
        (.Delay (intLit 1)))
        (.Delay (intLit 0))))
    mkOptGolden "opt_pipe_factorial" factorialMIR
    mkOptGolden "opt_pipe_fd_dce"
      (Expr.Let [(v, .Delay (.Var x), false),
                 (a, .Force (.Var v), false),
                 (b, intLit 42, false)]
        (.Var a))
    mkOptGolden "opt_pipe_already_optimal"
      (Expr.Lam x (.App (.Var f) (.Var x)))
    mkOptGolden "opt_pipe_shared_prefix"
      (Expr.Let
        [(a, .App (.Var f) (.App (.Var f) (.App (.Var f) (.Var x))), false),
         (b, .App (.Var f) (.App (.Var f) (.App (.Var f)
                (.App (.Var f) (.App (.Var f) (.App (.Var f) (.Var x)))))), false)]
        (.App (.App (.Var g) (.Var a)) (.Var b)))
    let rep : VarId := ⟨60, .source, "rep"⟩
    let add := Expr.Builtin .AddInteger
    let expensive :=
      Expr.App (.App add (.App (.App add (.App (.App add (.App (.App add (intLit 1)) (intLit 1))) (intLit 1))) (intLit 1))) (intLit 1)
    mkOptGolden "opt_pipe_no_inline_across_fix"
      (Expr.Let
        [(a, expensive, false)]
        (.Fix rep (.Lam n (.App (.App (.Var rep) (.Var n)) (.Var a)))))
    mkOptGolden "opt_pipe_case_merge"
      (Expr.Let
        [(t1, .Case (.Var x) [.Lam f0 (.Lam f1 (.Var f0))], false),
         (t2, .Case (.Var x) [.Lam g0 (.Lam g1 (.Var g1))], false)]
        (.App (.App (.Builtin .AddInteger) (.Var t1)) (.Var t2)))
    mkOptGolden "opt_pipe_eta"
      (Expr.Let [(a, .Lam x (.App (.Var f) (.Var x)), false)]
        (.App (.Var a) (.Var y)))
    mkOptGolden "opt_pipe_impure_deferred"
      (Expr.Let [(a, .App (.Var f) (.Var x), false)]
        (.Lam y (.Var a)))
    mkOptGolden "opt_pipe_beta_cse"
      (Expr.App
        (.App (.Builtin .AddInteger)
          (.App (.Lam a (.App (.Builtin .UnIData)
            (.App (.Force (.Builtin .HeadList))
              (.App (.Force (.Force (.Builtin .SndPair)))
                (.App (.Builtin .UnConstrData) (.Var x)))))) (.Var x)))
        (.App (.Lam b (.App (.Builtin .UnIData)
          (.App (.Force (.Builtin .HeadList))
            (.App (.Force (.Force (.Builtin .SndPair)))
              (.App (.Builtin .UnConstrData) (.Var x)))))) (.Var x)))

end Test.MIR.Opt.Golden
