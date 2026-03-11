import Test.MIR.Helpers
import Moist.MIR.Optimize
import Test.Framework

namespace Test.MIR.OptGolden

open Moist.MIR
open Test.MIR

/-! # Optimization Golden Tests

Golden test definitions for individual optimization passes and the full
pipeline. Each test case produces a formatted string for comparison against
`.expected` files.
-/

-- ## Additional Fixtures

private def v : VarId := ⟨50, "v"⟩
private def w : VarId := ⟨51, "w"⟩
private def c : VarId := ⟨9, "c"⟩
private def d : VarId := ⟨10, "d"⟩

-- ## Golden Case Builders

private def mkPassGolden (name : String) (input : Expr) (pass : Expr → Expr × Bool)
    : Test.Framework.GoldenSpec :=
  let (result, changed) := pass input
  let output := s!"--- Input ---\n{pretty input}\n--- Output ---\n{pretty result}\n--- Changed ---\n{changed}"
  { name, render := pure output }

private def mkInlineGolden (name : String) (input : Expr) (start : Nat := 1000)
    : Test.Framework.GoldenSpec :=
  let (result, changed) := runFresh (inlinePass input) start
  let output := s!"--- Input ---\n{pretty input}\n--- Output ---\n{pretty result}\n--- Changed ---\n{changed}"
  { name, render := pure output }

private def mkOptGolden (name : String) (input : Expr) (start : Nat := 1000)
    : Test.Framework.GoldenSpec :=
  let result := optimizeExpr input start
  let isAnf := result.isANF
  let output := s!"--- Input ---\n{pretty input}\n--- Optimized ---\n{pretty result}\n--- isANF ---\n{isAnf}"
  { name, render := pure output }

-- ## Golden Test Definitions

def optGoldenTests : List Test.Framework.GoldenSpec := [

  -- ### Float Out -/

  -- Pure binding floats out, impure stays
  mkPassGolden "opt_float_mixed"
    (Expr.Lam x
      (.Let [(a, intLit 1), (b, .App (.Var a) (.Var x))]
        (.App (.Var a) (.Var b))))
    floatOut,

  -- All bindings float
  mkPassGolden "opt_float_all"
    (Expr.Lam x (.Let [(a, intLit 1), (b, intLit 2)] (.Var x)))
    floatOut,

  -- Sequential scoping: a stays, b depends on a → stays, c floats
  mkPassGolden "opt_float_seq_dep"
    (Expr.Lam x
      (.Let [(a, .App (.Var x) (.Var y)), (b, .Var a), (c, intLit 1)]
        (.App (.Var b) (.Var c))))
    floatOut,

  -- Float out of Fix
  mkPassGolden "opt_float_fix"
    (Expr.Fix f (.Let [(a, intLit 1)] (.Lam x (.App (.Var f) (.Var a)))))
    floatOut,

  -- Nothing to float (impure or binder-dependent)
  mkPassGolden "opt_float_noop"
    (Expr.Lam x (.Let [(a, .App (.Var x) (.Var x))] (.Var a)))
    floatOut,

  -- ### CSE -/

  -- Duplicate App eliminated
  mkPassGolden "opt_cse_dup_app"
    (Expr.Let [(a, .App (.Var f) (.Var x)),
               (b, .App (.Var f) (.Var x))]
      (.App (.Var a) (.Var b)))
    cse,

  -- Triple duplicate
  mkPassGolden "opt_cse_triple"
    (Expr.Let [(a, .Force (.Var x)),
               (b, .Force (.Var x)),
               (c, .Force (.Var x))]
      (.Constr 0 [.Var a, .Var b, .Var c]))
    cse,

  -- Dup rename propagates into subsequent binding
  mkPassGolden "opt_cse_propagate"
    (Expr.Let [(a, .App (.Var f) (.Var x)),
               (b, .App (.Var f) (.Var x)),
               (c, .App (.Var g) (.Var b))]
      (.Var c))
    cse,

  -- No duplicates
  mkPassGolden "opt_cse_noop"
    (Expr.Let [(a, .App (.Var f) (.Var x)),
               (b, .App (.Var f) (.Var y))]
      (.App (.Var a) (.Var b)))
    cse,

  -- ### DCE -/

  -- Pure unused removed
  mkPassGolden "opt_dce_pure_unused"
    (Expr.Let [(a, intLit 42), (b, .App (.Var f) (.Var x))] (.Var b))
    dce,

  -- Transitive dead code
  mkPassGolden "opt_dce_transitive"
    (Expr.Let [(a, intLit 42), (b, .Lam y (.Var a))] (.Var z))
    dce,

  -- Impure unused kept (contains Error)
  mkPassGolden "opt_dce_impure_kept"
    (Expr.Let [(a, .App .Error (.Var x))] (.Var y))
    dce,

  -- Mixed: some removed, some kept
  mkPassGolden "opt_dce_mixed"
    (Expr.Let [(a, intLit 1), (b, intLit 2), (c, intLit 3)]
      (.App (.Var a) (.Var c)))
    dce,

  -- Error binding kept even if unused
  mkPassGolden "opt_dce_error_kept"
    (Expr.Let [(a, .Error)] (.Var x))
    dce,

  -- ### Force-Delay -/

  -- Direct cancellation
  mkPassGolden "opt_fd_direct"
    (Expr.Force (.Delay (.App (.Var f) (.Var x))))
    forceDelay,

  -- Through-let: all uses under Force
  mkPassGolden "opt_fd_through_let"
    (Expr.Let [(v, .Delay (.Var x))] (.Force (.Var v)))
    forceDelay,

  -- Through-let: multiple Force uses
  mkPassGolden "opt_fd_multi_force"
    (Expr.Let [(v, .Delay (.Var x))]
      (.App (.Force (.Var v)) (.Force (.Var v))))
    forceDelay,

  -- Through-let: mixed use → no change
  mkPassGolden "opt_fd_mixed_noop"
    (Expr.Let [(v, .Delay (.Var x))]
      (.App (.Var v) (.Force (.Var v))))
    forceDelay,

  -- Force in subsequent binding
  mkPassGolden "opt_fd_rest_binding"
    (Expr.Let [(v, .Delay (.Var x)), (b, .Force (.Var v))] (.Var b))
    forceDelay,

  -- ### Inline -/

  -- Atom inlining
  mkInlineGolden "opt_inline_atom"
    (Expr.Let [(a, .Var x)] (.App (.Var a) (.Var a))),

  -- Small value duplicated
  mkInlineGolden "opt_inline_small_lam"
    (Expr.Let [(a, .Lam y (.Var y))]
      (.App (.Var a) (.App (.Var a) (.Var z)))),

  -- Large value single use inlined
  mkInlineGolden "opt_inline_large_single"
    (Expr.Let [(a, .Lam y (.App (.Var y) (.App (.Var y) (.App (.Var y) (.Var y)))))]
      (.App (.Var a) (.Var z))),

  -- Large value under Fix: kept
  mkInlineGolden "opt_inline_large_fix"
    (Expr.Let [(a, .Lam y (.App (.Var y) (.App (.Var y) (.App (.Var y) (.Var y)))))]
      (.Fix g (.App (.Var a) (.Var g)))),

  -- Beta reduction
  mkInlineGolden "opt_inline_beta"
    (Expr.App (.Lam x (.App (.Var x) (.Var x))) (.Var z)),

  -- Chain of atom inlines
  mkInlineGolden "opt_inline_chain"
    (Expr.Let [(a, .Var x), (b, .Var a), (c, .Var b)] (.Var c)),

  -- ### Full Pipeline -/

  -- Simple: float + CSE + DCE
  mkOptGolden "opt_pipe_simple"
    (Expr.Lam x
      (.Let [(a, intLit 1),
             (b, .App (.Builtin .AddInteger) (.Var x)),
             (c, .App (.Builtin .AddInteger) (.Var x))]
        (.App (.Var b) (.Var c)))),

  -- Force-delay chain
  mkOptGolden "opt_pipe_fd_chain"
    (Expr.Let [(v, .Delay (.Var x)),
               (w, .Force (.Var v))]
      (.Var w)),

  -- Atom cascade
  mkOptGolden "opt_pipe_cascade"
    (Expr.Let [(a, .Var x), (b, .Var a), (c, .Var b)] (.Var c)),

  -- Inline + beta
  mkOptGolden "opt_pipe_inline_beta"
    (Expr.Let [(f, .Lam y (.Var y))] (.App (.Var f) (.Var z))),

  -- Nested let simplification
  mkOptGolden "opt_pipe_nested_let"
    (Expr.Let [(a, intLit 1)]
      (.Let [(b, .Var a)]
        (.Let [(c, .Var b)] (.Var c)))),

  -- IfThenElse pattern
  mkOptGolden "opt_pipe_ifthenelse"
    (Expr.Force (.App (.App (.App (.Builtin .IfThenElse) (.Var x))
      (.Delay (intLit 1)))
      (.Delay (intLit 0)))),

  -- Factorial
  mkOptGolden "opt_pipe_factorial" factorialMIR,

  -- Complex: force-delay feeds DCE
  mkOptGolden "opt_pipe_fd_dce"
    (Expr.Let [(v, .Delay (.Var x)),
               (a, .Force (.Var v)),
               (b, intLit 42)]
      (.Var a)),

  -- Already optimal expression
  mkOptGolden "opt_pipe_already_optimal"
    (Expr.Lam x (.App (.Var f) (.Var x))),

  -- Deeply nested application chains with shared prefix:
  --   let a = f(f(f(x))), b = f(f(f(f(f(f(x)))))) in g a b
  -- CSE should eliminate the shared sub-computations in the prefix.
  mkOptGolden "opt_pipe_shared_prefix"
    (Expr.Let
      [(a, .App (.Var f) (.App (.Var f) (.App (.Var f) (.Var x)))),
       (b, .App (.Var f) (.App (.Var f) (.App (.Var f)
              (.App (.Var f) (.App (.Var f) (.App (.Var f) (.Var x)))))))]
      (.App (.App (.Var g) (.Var a)) (.Var b))),

  -- Expensive computation must not be inlined across Fix boundary.
  -- let expensive = add(add(add(add(1,1),1),1),1)
  -- in fix rep. λ n . rep n expensive
  -- The binding must stay outside the Fix to avoid recomputation per call.
  let rep : VarId := ⟨60, "rep"⟩
  let add := Expr.Builtin .AddInteger
  let expensive :=
    Expr.App (.App add (.App (.App add (.App (.App add (.App (.App add (intLit 1)) (intLit 1))) (intLit 1))) (intLit 1))) (intLit 1)
  mkOptGolden "opt_pipe_no_inline_across_fix"
    (Expr.Let
      [(a, expensive)]
      (.Fix rep (.Lam n (.App (.App (.Var rep) (.Var n)) (.Var a)))))
]

end Test.MIR.OptGolden
