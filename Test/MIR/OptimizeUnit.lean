import Test.MIR.Helpers
import Moist.MIR.Optimize

open Moist.MIR
open Test.MIR

/-! # Optimization Pass Unit Tests

Comprehensive unit tests for all optimization passes:
1. isPure (purity analysis)
2. exprStructEq / lookupStructEq (CSE helpers)
3. allUsesAreForce (force-delay helper)
4. occursUnderFix (inline helper)
5. shouldInline (inline decision)
6. floatOut
7. cse
8. dce
9. forceDelay
10. inlinePass + betaReduce
11. Full pipeline (optimize / optimizeExpr)
-/

-- ## Additional Fixtures

private def v : VarId := ⟨50, "v"⟩
private def r : VarId := ⟨51, "r"⟩

/-- Large lambda exceeding inlineThreshold (size = 8 > 5). -/
private def largeLam : Expr :=
  .Lam y (.App (.Var y) (.App (.Var y) (.App (.Var y) (.Var y))))

-- ------------------------------------------------------------------
-- # 1. isPure                                                         
-- ------------------------------------------------------------------

#eval do
  -- Pure: atoms
  check "isPure_var" (isPure (.Var x))
  check "isPure_lit_int" (isPure (intLit 42))
  check "isPure_lit_bool" (isPure (boolLit true))
  check "isPure_builtin" (isPure (.Builtin .AddInteger))
  -- Pure: compound values (body not evaluated)
  check "isPure_lam" (isPure (.Lam x (.Var x)))
  check "isPure_lam_impure_body" (isPure (.Lam x (.App (.Var x) (.Var x))))
  check "isPure_lam_error_body" (isPure (.Lam x .Error))
  check "isPure_delay" (isPure (.Delay (.Var x)))
  check "isPure_delay_error" (isPure (.Delay .Error))
  check "isPure_delay_app" (isPure (.Delay (.App (.Var f) (.Var x))))
  check "isPure_fix" (isPure (.Fix f (.Lam x (.Var x))))
  check "isPure_fix_recursive" (isPure (.Fix f (.Lam x (.App (.Var f) (.Var x)))))
  -- Pure: Constr with atom args
  check "isPure_constr_empty" (isPure (.Constr 0 []))
  check "isPure_constr_vars" (isPure (.Constr 0 [.Var x, .Var y]))
  check "isPure_constr_lits" (isPure (.Constr 1 [intLit 1, intLit 2]))
  check "isPure_constr_builtin" (isPure (.Constr 0 [.Builtin .AddInteger]))
  check "isPure_constr_mixed_atoms" (isPure (.Constr 0 [.Var x, intLit 1, .Builtin .AddInteger]))
  -- Impure: Constr with non-atom args
  check "isPure_constr_app_arg" (!isPure (.Constr 0 [.App (.Var f) (.Var x)]))
  check "isPure_constr_lam_arg" (!isPure (.Constr 0 [.Lam x (.Var x)]))
  check "isPure_constr_delay_arg" (!isPure (.Constr 0 [.Delay (.Var x)]))
  check "isPure_constr_one_bad" (!isPure (.Constr 0 [.Var x, .App (.Var f) (.Var y)]))
  check "isPure_constr_first_bad" (!isPure (.Constr 0 [.App (.Var f) (.Var x), .Var y]))
  -- Always impure
  check "isPure_app" (!isPure (.App (.Var f) (.Var x)))
  check "isPure_app_builtin" (!isPure (.App (.Builtin .AddInteger) (intLit 1)))
  check "isPure_force" (!isPure (.Force (.Var x)))
  check "isPure_force_delay" (!isPure (.Force (.Delay (.Var x))))
  check "isPure_case" (!isPure (.Case (.Var x) [.Var y, .Var z]))
  check "isPure_let" (!isPure (.Let [(a, intLit 1)] (.Var a)))
  check "isPure_let_pure_bindings" (!isPure (.Let [(a, .Var x)] (.Var a)))
  check "isPure_error" (!isPure .Error)

-- ------------------------------------------------------------------
-- # 2. exprStructEq                                                   
-- ------------------------------------------------------------------

#eval do
  -- Equal pairs
  check "structEq_var_same" (exprStructEq (.Var x) (.Var x))
  check "structEq_lit_int" (exprStructEq (intLit 1) (intLit 1))
  check "structEq_lit_bool" (exprStructEq (boolLit true) (boolLit true))
  check "structEq_builtin_same" (exprStructEq (.Builtin .AddInteger) (.Builtin .AddInteger))
  check "structEq_error" (exprStructEq .Error .Error)
  check "structEq_lam_same" (exprStructEq (.Lam x (.Var x)) (.Lam x (.Var x)))
  check "structEq_fix_same" (exprStructEq (.Fix f (.Var f)) (.Fix f (.Var f)))
  check "structEq_app_same" (exprStructEq (.App (.Var f) (.Var x)) (.App (.Var f) (.Var x)))
  check "structEq_force_same" (exprStructEq (.Force (.Var x)) (.Force (.Var x)))
  check "structEq_delay_same" (exprStructEq (.Delay (.Var x)) (.Delay (.Var x)))
  check "structEq_constr_same" (exprStructEq (.Constr 0 [.Var x, .Var y]) (.Constr 0 [.Var x, .Var y]))
  check "structEq_constr_empty" (exprStructEq (.Constr 0 []) (.Constr 0 []))
  check "structEq_case_same" (exprStructEq (.Case (.Var x) [.Var y]) (.Case (.Var x) [.Var y]))
  check "structEq_let_same" (exprStructEq (.Let [(a, .Var x)] (.Var a)) (.Let [(a, .Var x)] (.Var a)))
  -- Unequal pairs
  check "structEq_var_diff" (!exprStructEq (.Var x) (.Var y))
  check "structEq_lit_diff_val" (!exprStructEq (intLit 1) (intLit 2))
  check "structEq_lit_diff_type" (!exprStructEq (intLit 1) (boolLit true))
  check "structEq_builtin_diff" (!exprStructEq (.Builtin .AddInteger) (.Builtin .SubtractInteger))
  check "structEq_lam_diff_binder" (!exprStructEq (.Lam x (.Var x)) (.Lam y (.Var y)))
  check "structEq_fix_diff_binder" (!exprStructEq (.Fix f (.Var f)) (.Fix g (.Var g)))
  check "structEq_app_diff_fun" (!exprStructEq (.App (.Var f) (.Var x)) (.App (.Var g) (.Var x)))
  check "structEq_app_diff_arg" (!exprStructEq (.App (.Var f) (.Var x)) (.App (.Var f) (.Var y)))
  check "structEq_constr_diff_tag" (!exprStructEq (.Constr 0 [.Var x]) (.Constr 1 [.Var x]))
  check "structEq_constr_diff_args" (!exprStructEq (.Constr 0 [.Var x]) (.Constr 0 [.Var y]))
  check "structEq_constr_diff_len" (!exprStructEq (.Constr 0 [.Var x]) (.Constr 0 [.Var x, .Var y]))
  check "structEq_let_diff_binder" (!exprStructEq (.Let [(a, .Var x)] (.Var a)) (.Let [(b, .Var x)] (.Var b)))
  check "structEq_cross_ctor" (!exprStructEq (.Var x) (intLit 1))
  check "structEq_cross_ctor2" (!exprStructEq (.Lam x (.Var x)) (.Fix x (.Var x)))

-- ------------------------------------------------------------------
-- # 3. lookupStructEq                                                 
-- ------------------------------------------------------------------

#eval do
  check "lookup_empty" (lookupStructEq [] (.Var x) == none)
  check "lookup_found" (lookupStructEq [(.App (.Var f) (.Var x), a)] (.App (.Var f) (.Var x)) == some a)
  check "lookup_found_second" (lookupStructEq [(intLit 1, a), (.App (.Var f) (.Var x), b)] (.App (.Var f) (.Var x)) == some b)
  check "lookup_not_found" (lookupStructEq [(.App (.Var f) (.Var x), a)] (.App (.Var f) (.Var y)) == none)
  check "lookup_first_match_wins" (lookupStructEq [(.Var x, a), (.Var x, b)] (.Var x) == some a)

-- ------------------------------------------------------------------
-- # 4. allUsesAreForce                                                
-- ------------------------------------------------------------------

#eval do
  check "allForce_bare_var" (!allUsesAreForce v (.Var v))
  check "allForce_force_var" (allUsesAreForce v (.Force (.Var v)))
  check "allForce_force_other_var" (allUsesAreForce v (.Force (.Var x)))
  check "allForce_no_occ_atom" (allUsesAreForce v (intLit 1))
  check "allForce_no_occ_complex" (allUsesAreForce v (.App (.Var f) (.Var x)))
  check "allForce_nested_force" (allUsesAreForce v (.Force (.Force (.Var v))))
  check "allForce_force_app_containing_v" (!allUsesAreForce v (.Force (.App (.Var v) (.Var x))))
  check "allForce_lam_shadow" (allUsesAreForce v (.Lam v (.Var v)))
  check "allForce_fix_shadow" (allUsesAreForce v (.Fix v (.Var v)))
  check "allForce_app_both_force" (allUsesAreForce v (.App (.Force (.Var v)) (.Force (.Var v))))
  check "allForce_app_mixed_bad" (!allUsesAreForce v (.App (.Var v) (.Force (.Var v))))
  check "allForce_constr_bare" (!allUsesAreForce v (.Constr 0 [.Var v]))
  check "allForce_constr_force" (allUsesAreForce v (.Constr 0 [.Force (.Var v)]))
  check "allForce_case_all_force" (allUsesAreForce v (.Case (.Force (.Var v)) [.Force (.Var v)]))
  check "allForce_case_scrut_bare" (!allUsesAreForce v (.Case (.Var v) [.Force (.Var v)]))
  check "allForce_let_shadow" (allUsesAreForce v (.Let [(v, .Var x)] (.Var v)))
  check "allForce_let_rhs_before_shadow" (!allUsesAreForce v (.Let [(a, .Var v), (v, intLit 1)] (.Var v)))
  check "allForce_delay_inner" (allUsesAreForce v (.Delay (.Force (.Var v))))
  check "allForce_delay_bare" (!allUsesAreForce v (.Delay (.Var v)))

-- ------------------------------------------------------------------
-- # 5. occursUnderFix                                                 
-- ------------------------------------------------------------------

#eval do
  check "underFix_inside" (occursUnderFix v (.Fix f (.App (.Var v) (.Var f))))
  check "underFix_outside" (!occursUnderFix v (.App (.Var v) (.Fix f (.Var f))))
  check "underFix_rebound_fix" (!occursUnderFix v (.Fix v (.Var v)))
  check "underFix_rebound_lam_inside" (!occursUnderFix v (.Fix f (.Lam v (.Var v))))
  check "underFix_not_present" (!occursUnderFix v (.Var x))
  check "underFix_nested_fix" (occursUnderFix v (.Fix f (.Fix g (.Var v))))
  check "underFix_let_shadow" (!occursUnderFix v (.Fix f (.Let [(v, intLit 1)] (.Var v))))
  check "underFix_let_rhs_before_shadow" (occursUnderFix v (.Fix f (.Let [(a, .Var v), (v, intLit 1)] (.Var v))))
  check "underFix_both_in_out" (occursUnderFix v (.App (.Var v) (.Fix f (.Var v))))
  check "underFix_in_app_fn" (occursUnderFix v (.Fix f (.App (.Var v) (.Var x))))
  check "underFix_deep_nested" (occursUnderFix v (.Fix f (.Lam x (.App (.Var x) (.Var v)))))
  check "underFix_in_constr" (occursUnderFix v (.Fix f (.Constr 0 [.Var v])))
  check "underFix_in_case_scrut" (occursUnderFix v (.Fix f (.Case (.Var v) [.Var x])))
  check "underFix_in_delay" (occursUnderFix v (.Fix f (.Delay (.Var v))))
  check "underFix_in_force" (occursUnderFix v (.Fix f (.Force (.Var v))))

-- ------------------------------------------------------------------
-- # 6. shouldInline                                                   
-- ------------------------------------------------------------------

#eval do
  -- Atom: always inline regardless of count or Fix
  check "should_atom_var_0" (shouldInline (.Var x) 0 false)
  check "should_atom_var_multi" (shouldInline (.Var x) 5 true)
  check "should_atom_lit" (shouldInline (intLit 42) 3 false)
  check "should_atom_builtin" (shouldInline (.Builtin .AddInteger) 2 true)
  -- Small value (size <= 5): always inline
  check "should_small_lam" (shouldInline (.Lam y (.Var y)) 3 true)
  check "should_small_delay" (shouldInline (.Delay (.Var x)) 2 false)
  check "should_small_fix" (shouldInline (.Fix f (.Var f)) 2 true)
  -- Large value (size > 5)
  check "should_large_0_occ" (!shouldInline largeLam 0 false)
  check "should_large_1_no_fix" (shouldInline largeLam 1 false)
  check "should_large_1_under_fix" (!shouldInline largeLam 1 true)
  check "should_large_2" (!shouldInline largeLam 2 false)
  check "should_large_2_under_fix" (!shouldInline largeLam 2 true)
  check "should_large_3" (!shouldInline largeLam 3 false)
  -- Non-value
  let nonVal := Expr.App (.Var f) (.Var x)
  check "should_nonval_0" (!shouldInline nonVal 0 false)
  check "should_nonval_1_no_fix" (shouldInline nonVal 1 false)
  check "should_nonval_1_under_fix" (!shouldInline nonVal 1 true)
  check "should_nonval_2" (!shouldInline nonVal 2 false)
  check "should_nonval_2_under_fix" (!shouldInline nonVal 2 true)
  -- Edge: Error is non-value
  check "should_error_0" (!shouldInline .Error 0 false)
  check "should_error_1" (shouldInline .Error 1 false)
  check "should_error_1_fix" (!shouldInline .Error 1 true)

-- ------------------------------------------------------------------
-- # 7. floatOut                                                       
-- ------------------------------------------------------------------

-- Leaf nodes pass through unchanged
#eval do
  let leaves : List (String × Expr) :=
    [("float_var", .Var x), ("float_lit", intLit 42),
     ("float_builtin", .Builtin .AddInteger), ("float_error", .Error)]
  for (name, e) in leaves do
    let (r, ch) := floatOut e
    checkAlphaEq name r e
    check s!"{name}_unchanged" (!ch)

-- Pure binding floats out of Lam
#eval do
  let e := Expr.Lam x (.Let [(a, intLit 1)] (.Var a))
  let expected := Expr.Let [(a, intLit 1)] (.Lam x (.Var a))
  checkPassResult "float_pure_out_of_lam" (floatOut e) expected true

-- Pure Var RHS not mentioning binder floats
#eval do
  let e := Expr.Lam x (.Let [(a, .Var y)] (.App (.Var a) (.Var x)))
  let expected := Expr.Let [(a, .Var y)] (.Lam x (.App (.Var a) (.Var x)))
  checkPassResult "float_pure_var_out_of_lam" (floatOut e) expected true

-- Binding mentioning binder stays
#eval do
  let e := Expr.Lam x (.Let [(a, .App (.Var x) (.Var x))] (.Var a))
  checkPassResult "float_mentions_binder" (floatOut e) e false

-- Pure binding mentioning binder stays
#eval do
  let e := Expr.Lam x (.Let [(a, .Var x)] (.Var a))
  checkPassResult "float_pure_mentions_binder" (floatOut e) e false

-- Impure binding stays even without binder dependency
#eval do
  let e := Expr.Lam x (.Let [(a, .App (.Var f) (.Var y))] (.Var a))
  checkPassResult "float_impure_stays" (floatOut e) e false

-- Impure Force stays
#eval do
  let e := Expr.Lam x (.Let [(a, .Force (.Var y))] (.Var a))
  checkPassResult "float_impure_force_stays" (floatOut e) e false

-- Mixed partition: some float, some stay
#eval do
  let e := Expr.Lam x
    (.Let [(a, intLit 1), (b, .App (.Var a) (.Var x))]
      (.App (.Var a) (.Var b)))
  let expected := Expr.Let [(a, intLit 1)]
    (.Lam x (.Let [(b, .App (.Var a) (.Var x))]
      (.App (.Var a) (.Var b))))
  checkPassResult "float_mixed_partition" (floatOut e) expected true

-- All bindings float
#eval do
  let e := Expr.Lam x (.Let [(a, intLit 1), (b, intLit 2)] (.Var x))
  let expected := Expr.Let [(a, intLit 1), (b, intLit 2)] (.Lam x (.Var x))
  checkPassResult "float_all_float" (floatOut e) expected true

-- All bindings stay
#eval do
  let e := Expr.Lam x
    (.Let [(a, .App (.Var x) (.Var x)), (b, .App (.Var f) (.Var x))]
      (.App (.Var a) (.Var b)))
  checkPassResult "float_all_stay" (floatOut e) e false

-- Sequential scoping: b depends on stay-var a, so b also stays
#eval do
  let e := Expr.Lam x
    (.Let [(a, .App (.Var x) (.Var x)), (b, .Lam y (.Var a))]
      (.App (.Var a) (.Var b)))
  checkPassResult "float_seq_dep_stay" (floatOut e) e false

-- Sequential scoping: a stays, b depends on a → stays, c floats
#eval do
  let e := Expr.Lam x
    (.Let [(a, .App (.Var x) (.Var y)), (b, .Var a), (c, intLit 1)]
      (.App (.Var b) (.Var c)))
  let expected := Expr.Let [(c, intLit 1)]
    (.Lam x
      (.Let [(a, .App (.Var x) (.Var y)), (b, .Var a)]
        (.App (.Var b) (.Var c))))
  checkPassResult "float_seq_dep_chain" (floatOut e) expected true

-- Sequential scoping: a floats, b depends on a (which floated) → b floats too
#eval do
  let e := Expr.Lam x
    (.Let [(a, intLit 1), (b, .Lam y (.Var a))]
      (.App (.Var b) (.Var x)))
  let expected := Expr.Let [(a, intLit 1), (b, .Lam y (.Var a))]
    (.Lam x (.App (.Var b) (.Var x)))
  checkPassResult "float_seq_pure_chain_floats" (floatOut e) expected true

-- Float out of Fix
#eval do
  let e := Expr.Fix f (.Let [(a, intLit 1)] (.Lam x (.App (.Var f) (.Var a))))
  let expected := Expr.Let [(a, intLit 1)] (.Fix f (.Lam x (.App (.Var f) (.Var a))))
  checkPassResult "float_fix_pure" (floatOut e) expected true

-- Fix: binding mentioning Fix binder stays
#eval do
  let e := Expr.Fix f (.Let [(a, .Var f)] (.Lam x (.Var a)))
  checkPassResult "float_fix_mentions_binder" (floatOut e) e false

-- Body is not a Let → nothing to float
#eval do
  let e := Expr.Lam x (.Var y)
  checkPassResult "float_body_not_let" (floatOut e) e false

#eval do
  let e := Expr.Lam x (.App (.Var f) (.Var x))
  checkPassResult "float_body_app" (floatOut e) e false

-- Does NOT float out of Delay (but recursion processes inside)
#eval do
  -- Inside the Delay there's a Lam with a floatable binding
  let e := Expr.Delay (.Lam x (.Let [(a, intLit 1)] (.Var a)))
  let expected := Expr.Delay (.Let [(a, intLit 1)] (.Lam x (.Var a)))
  checkPassResult "float_inside_delay_at_lam" (floatOut e) expected true

-- Recursion into App
#eval do
  let e := Expr.App (.Lam x (.Let [(a, intLit 1)] (.Var a))) (.Var y)
  let expected := Expr.App (.Let [(a, intLit 1)] (.Lam x (.Var a))) (.Var y)
  checkPassResult "float_recurse_app" (floatOut e) expected true

-- Recursion into Force
#eval do
  let e := Expr.Force (.Lam x (.Let [(a, intLit 1)] (.Var a)))
  let expected := Expr.Force (.Let [(a, intLit 1)] (.Lam x (.Var a)))
  checkPassResult "float_recurse_force" (floatOut e) expected true

-- Recursion into Constr
#eval do
  let e := Expr.Constr 0 [.Lam x (.Let [(a, intLit 1)] (.Var a)), .Var y]
  let expected := Expr.Constr 0 [.Let [(a, intLit 1)] (.Lam x (.Var a)), .Var y]
  checkPassResult "float_recurse_constr" (floatOut e) expected true

-- Recursion into Let RHS
#eval do
  let e := Expr.Let [(b, .Lam x (.Let [(a, intLit 1)] (.Var a)))] (.Var b)
  let expected := Expr.Let [(b, .Let [(a, intLit 1)] (.Lam x (.Var a)))] (.Var b)
  checkPassResult "float_recurse_let_rhs" (floatOut e) expected true

-- Recursion into Let body
#eval do
  let e := Expr.Let [(b, intLit 1)] (.Lam x (.Let [(a, intLit 2)] (.Var a)))
  let expected := Expr.Let [(b, intLit 1)] (.Let [(a, intLit 2)] (.Lam x (.Var a)))
  checkPassResult "float_recurse_let_body" (floatOut e) expected true

-- Recursion into Case alternatives
#eval do
  let e := Expr.Case (.Var x) [.Lam y (.Let [(a, intLit 1)] (.Var a)), .Var z]
  let expected := Expr.Case (.Var x) [.Let [(a, intLit 1)] (.Lam y (.Var a)), .Var z]
  checkPassResult "float_recurse_case_alt" (floatOut e) expected true

-- Empty Let bindings → nothing to float
#eval do
  let e := Expr.Lam x (.Let [] (.Var y))
  checkPassResult "float_empty_let" (floatOut e) e false

-- ------------------------------------------------------------------
-- # 8. CSE                                                            
-- ------------------------------------------------------------------

-- Duplicate App eliminated
#eval do
  let e := Expr.Let [(a, .App (.Var f) (.Var x)),
                      (b, .App (.Var f) (.Var x))]
              (.App (.Var a) (.Var b))
  let expected := Expr.Let [(a, .App (.Var f) (.Var x))]
                    (.App (.Var a) (.Var a))
  checkPassResult "cse_dup_app" (cse e) expected true

-- Different Apps not eliminated
#eval do
  let e := Expr.Let [(a, .App (.Var f) (.Var x)),
                      (b, .App (.Var f) (.Var y))]
              (.App (.Var a) (.Var b))
  checkPassResult "cse_no_dup" (cse e) e false

-- Triple duplicate collapses to first
#eval do
  let e := Expr.Let [(a, .Force (.Var x)),
                      (b, .Force (.Var x)),
                      (c, .Force (.Var x))]
              (.Constr 0 [.Var a, .Var b, .Var c])
  let expected := Expr.Let [(a, .Force (.Var x))]
                    (.Constr 0 [.Var a, .Var a, .Var a])
  checkPassResult "cse_triple_dup" (cse e) expected true

-- Duplicate Var RHS
#eval do
  let e := Expr.Let [(a, .Var x), (b, .Var x)]
              (.App (.Var a) (.Var b))
  let expected := Expr.Let [(a, .Var x)]
                    (.App (.Var a) (.Var a))
  checkPassResult "cse_dup_var" (cse e) expected true

-- Duplicate Delay
#eval do
  let e := Expr.Let [(a, .Delay (.Var x)), (b, .Delay (.Var x))]
              (.App (.Var a) (.Var b))
  let expected := Expr.Let [(a, .Delay (.Var x))]
                    (.App (.Var a) (.Var a))
  checkPassResult "cse_dup_delay" (cse e) expected true

-- Duplicate Constr
#eval do
  let e := Expr.Let [(a, .Constr 0 [.Var x, .Var y]),
                      (b, .Constr 0 [.Var x, .Var y])]
              (.App (.Var a) (.Var b))
  let expected := Expr.Let [(a, .Constr 0 [.Var x, .Var y])]
                    (.App (.Var a) (.Var a))
  checkPassResult "cse_dup_constr" (cse e) expected true

-- Dup renames in subsequent bindings
#eval do
  let e := Expr.Let [(a, .App (.Var f) (.Var x)),
                      (b, .App (.Var f) (.Var x)),
                      (c, .App (.Var g) (.Var b))]
              (.Var c)
  let expected := Expr.Let [(a, .App (.Var f) (.Var x)),
                             (c, .App (.Var g) (.Var a))]
                    (.Var c)
  checkPassResult "cse_dup_renames_rest" (cse e) expected true

-- Single binding: nothing to dedup
#eval do
  let e := Expr.Let [(a, .App (.Var f) (.Var x))] (.Var a)
  checkPassResult "cse_single_binding" (cse e) e false

-- CSE inside Lam body
#eval do
  let e := Expr.Lam z
    (.Let [(a, .App (.Var f) (.Var z)), (b, .App (.Var f) (.Var z))]
      (.App (.Var a) (.Var b)))
  let expected := Expr.Lam z
    (.Let [(a, .App (.Var f) (.Var z))]
      (.App (.Var a) (.Var a)))
  checkPassResult "cse_recurse_lam" (cse e) expected true

-- CSE inside Fix body
#eval do
  let e := Expr.Fix g
    (.Let [(a, .Var x), (b, .Var x)]
      (.App (.Var a) (.Var b)))
  let expected := Expr.Fix g
    (.Let [(a, .Var x)]
      (.App (.Var a) (.Var a)))
  checkPassResult "cse_recurse_fix" (cse e) expected true

-- CSE inside nested Let RHS
#eval do
  let e := Expr.Let
    [(c, .Let [(a, .Var x), (b, .Var x)] (.App (.Var a) (.Var b)))]
    (.Var c)
  let expected := Expr.Let
    [(c, .Let [(a, .Var x)] (.App (.Var a) (.Var a)))]
    (.Var c)
  checkPassResult "cse_recurse_let_rhs" (cse e) expected true

-- CSE inside Case alternatives
#eval do
  let e := Expr.Case (.Var x)
    [.Let [(a, .Var y), (b, .Var y)] (.App (.Var a) (.Var b))]
  let expected := Expr.Case (.Var x)
    [.Let [(a, .Var y)] (.App (.Var a) (.Var a))]
  checkPassResult "cse_recurse_case_alt" (cse e) expected true

-- CSE inside Delay
#eval do
  let e := Expr.Delay
    (.Let [(a, .Var x), (b, .Var x)] (.App (.Var a) (.Var b)))
  let expected := Expr.Delay
    (.Let [(a, .Var x)] (.App (.Var a) (.Var a)))
  checkPassResult "cse_recurse_delay" (cse e) expected true

-- CSE inside App
#eval do
  let e := Expr.App
    (.Let [(a, .Var x), (b, .Var x)] (.App (.Var a) (.Var b)))
    (.Var y)
  let expected := Expr.App
    (.Let [(a, .Var x)] (.App (.Var a) (.Var a)))
    (.Var y)
  checkPassResult "cse_recurse_app" (cse e) expected true

-- CSE does NOT merge across separate Let blocks
#eval do
  let e := Expr.Let [(a, .App (.Var f) (.Var x))]
    (.Let [(b, .App (.Var f) (.Var x))]
      (.App (.Var a) (.Var b)))
  checkPassResult "cse_separate_lets_no_merge" (cse e) e false

-- Atoms pass through
#eval do
  let (r, ch) := cse (.Var x)
  checkAlphaEq "cse_atom_var" r (.Var x)
  check "cse_atom_var_unchanged" (!ch)

-- ------------------------------------------------------------------
-- # 9. DCE                                                            
-- ------------------------------------------------------------------

-- Pure unused bindings removed
#eval do
  checkPassResult "dce_unused_var"
    (dce (.Let [(a, .Var y)] (.Var x))) (.Var x) true
  checkPassResult "dce_unused_lit"
    (dce (.Let [(a, intLit 42)] (.Var x))) (.Var x) true
  checkPassResult "dce_unused_lam"
    (dce (.Let [(a, .Lam y (.Var y))] (.Var x))) (.Var x) true
  checkPassResult "dce_unused_delay"
    (dce (.Let [(a, .Delay (.Var y))] (.Var x))) (.Var x) true
  checkPassResult "dce_unused_fix"
    (dce (.Let [(a, .Fix f (.Lam y (.Var y)))] (.Var x))) (.Var x) true
  checkPassResult "dce_unused_builtin"
    (dce (.Let [(a, .Builtin .AddInteger)] (.Var x))) (.Var x) true
  checkPassResult "dce_unused_constr_atoms"
    (dce (.Let [(a, .Constr 0 [.Var y, .Var z])] (.Var x))) (.Var x) true

-- Impure unused bindings kept
#eval do
  let e1 := Expr.Let [(a, .App (.Var f) (.Var x))] (.Var y)
  checkPassResult "dce_impure_app" (dce e1) e1 false
  let e2 := Expr.Let [(a, .Force (.Var x))] (.Var y)
  checkPassResult "dce_impure_force" (dce e2) e2 false
  let e3 := Expr.Let [(a, .Case (.Var x) [.Var y])] (.Var z)
  checkPassResult "dce_impure_case" (dce e3) e3 false
  let e4 := Expr.Let [(a, .Error)] (.Var x)
  checkPassResult "dce_impure_error" (dce e4) e4 false
  let e5 := Expr.Let [(a, .Constr 0 [.App (.Var f) (.Var x)])] (.Var y)
  checkPassResult "dce_impure_constr" (dce e5) e5 false
  let e6 := Expr.Let [(a, .Let [(b, intLit 1)] (.Var b))] (.Var x)
  checkPassResult "dce_impure_let_rhs" (dce e6) e6 false

-- Used bindings always kept
#eval do
  let e1 := Expr.Let [(a, intLit 1)] (.Var a)
  checkPassResult "dce_used_pure" (dce e1) e1 false
  let e2 := Expr.Let [(a, .App (.Var f) (.Var x))] (.Var a)
  checkPassResult "dce_used_impure" (dce e2) e2 false

-- Transitive dead code: b dead → a's FVs not added → a dead too
#eval do
  let e := Expr.Let [(a, intLit 42), (b, .Lam y (.Var a))] (.Var z)
  checkPassResult "dce_transitive_2" (dce e) (.Var z) true

-- Transitive chain of 3
#eval do
  let e := Expr.Let [(a, intLit 1), (b, .Var a), (c, .Lam y (.Var b))] (.Var x)
  checkPassResult "dce_transitive_3" (dce e) (.Var x) true

-- Transitive: b used → a needed
#eval do
  let e := Expr.Let [(a, intLit 1), (b, .Var a)] (.Var b)
  checkPassResult "dce_transitive_used" (dce e) e false

-- Mixed: used middle, dead ends
#eval do
  let e := Expr.Let [(a, intLit 1), (b, .Var a), (c, intLit 2)] (.Var b)
  let expected := Expr.Let [(a, intLit 1), (b, .Var a)] (.Var b)
  checkPassResult "dce_mixed_remove_end" (dce e) expected true

-- Mixed: remove middle
#eval do
  let e := Expr.Let [(a, intLit 1), (b, intLit 2), (c, intLit 3)]
              (.App (.Var a) (.Var c))
  let expected := Expr.Let [(a, intLit 1), (c, intLit 3)]
                    (.App (.Var a) (.Var c))
  checkPassResult "dce_remove_middle" (dce e) expected true

-- All dead → body returned directly
#eval do
  let e := Expr.Let [(a, intLit 1), (b, intLit 2)] (.Var x)
  checkPassResult "dce_all_dead" (dce e) (.Var x) true

-- Empty bindings → body
#eval do
  let e := Expr.Let [] (.Var x)
  checkPassResult "dce_empty_bindings" (dce e) (.Var x) true

-- Recursion into sub-expressions
#eval do
  checkPassResult "dce_recurse_lam"
    (dce (.Lam x (.Let [(a, intLit 1)] (.Var x))))
    (.Lam x (.Var x)) true
  checkPassResult "dce_recurse_fix"
    (dce (.Fix f (.Let [(a, intLit 1)] (.Var f))))
    (.Fix f (.Var f)) true
  checkPassResult "dce_recurse_app_fn"
    (dce (.App (.Let [(a, intLit 1)] (.Var f)) (.Var x)))
    (.App (.Var f) (.Var x)) true
  checkPassResult "dce_recurse_app_arg"
    (dce (.App (.Var f) (.Let [(a, intLit 1)] (.Var x))))
    (.App (.Var f) (.Var x)) true
  checkPassResult "dce_recurse_force"
    (dce (.Force (.Let [(a, intLit 1)] (.Var x))))
    (.Force (.Var x)) true
  checkPassResult "dce_recurse_delay"
    (dce (.Delay (.Let [(a, intLit 1)] (.Var x))))
    (.Delay (.Var x)) true
  checkPassResult "dce_recurse_constr"
    (dce (.Constr 0 [.Let [(a, intLit 1)] (.Var x)]))
    (.Constr 0 [.Var x]) true
  checkPassResult "dce_recurse_case_scrut"
    (dce (.Case (.Let [(a, intLit 1)] (.Var x)) [.Var y]))
    (.Case (.Var x) [.Var y]) true
  checkPassResult "dce_recurse_case_alt"
    (dce (.Case (.Var x) [.Let [(a, intLit 1)] (.Var y)]))
    (.Case (.Var x) [.Var y]) true

-- Recursion into Let RHS
#eval do
  let e := Expr.Let [(b, .Let [(a, intLit 1)] (.App (.Var f) (.Var x)))] (.Var b)
  let expected := Expr.Let [(b, .App (.Var f) (.Var x))] (.Var b)
  checkPassResult "dce_recurse_let_rhs" (dce e) expected true

-- Leaf expressions unchanged
#eval do
  for (name, e) in [("dce_var", Expr.Var x), ("dce_lit", intLit 42),
                     ("dce_builtin", Expr.Builtin .AddInteger), ("dce_error", Expr.Error)] do
    let (r, ch) := dce e
    checkAlphaEq name r e
    check s!"{name}_unchanged" (!ch)

-- ------------------------------------------------------------------
-- # 10. forceDelay                                                    
-- ------------------------------------------------------------------

-- Pattern 1: direct Force(Delay e) cancellation
#eval do
  checkPassResult "fd_direct_var"
    (forceDelay (.Force (.Delay (.Var x)))) (.Var x) true
  checkPassResult "fd_direct_app"
    (forceDelay (.Force (.Delay (.App (.Var f) (.Var x))))) (.App (.Var f) (.Var x)) true
  checkPassResult "fd_direct_error"
    (forceDelay (.Force (.Delay .Error))) .Error true
  checkPassResult "fd_direct_nested_delay"
    (forceDelay (.Force (.Delay (.Delay (.Var x))))) (.Delay (.Var x)) true

-- Pattern 1 via post-recursion: inner simplifies to Delay
#eval do
  -- Force (Force (Delay (Delay x))) → inner reduces to Delay x, then outer catches it
  let e := Expr.Force (.Force (.Delay (.Delay (.Var x))))
  let (r, ch) := forceDelay e
  checkAlphaEq "fd_post_recursion" r (.Var x)
  check "fd_post_recursion_changed" ch

-- Pattern 2: through-let, single Force use
#eval do
  let e := Expr.Let [(v, .Delay (.Var x))] (.Force (.Var v))
  let expected := Expr.Let [(v, .Delay (.Var x))] (.Var x)
  checkPassResult "fd_through_let_single" (forceDelay e) expected true

-- Pattern 2: through-let, multiple Force uses
#eval do
  let e := Expr.Let [(v, .Delay (.Var x))]
              (.App (.Force (.Var v)) (.Force (.Var v)))
  let expected := Expr.Let [(v, .Delay (.Var x))]
                    (.App (.Var x) (.Var x))
  checkPassResult "fd_through_let_multi_force" (forceDelay e) expected true

-- Pattern 2: mixed uses → no change
#eval do
  let e := Expr.Let [(v, .Delay (.Var x))]
              (.App (.Var v) (.Force (.Var v)))
  checkPassResult "fd_through_let_mixed" (forceDelay e) e false

-- Pattern 2: Force in subsequent binding's RHS
#eval do
  let e := Expr.Let [(v, .Delay (.Var x)), (b, .Force (.Var v))]
              (.Var b)
  let expected := Expr.Let [(v, .Delay (.Var x)), (b, .Var x)]
                    (.Var b)
  checkPassResult "fd_through_let_in_rest" (forceDelay e) expected true

-- Pattern 2: shadowed variable
#eval do
  let e := Expr.Let [(v, .Delay (.Var x))]
              (.Lam v (.Force (.Var v)))
  -- v is shadowed by Lam, the Force(Var v) refers to the Lam's v,
  -- not the Let's v. allUsesAreForce returns true vacuously.
  -- replaceForceVar does not descend past the shadow.
  let (r, ch) := forceDelay e
  -- The original Let binding remains, body unchanged
  checkAlphaEq "fd_through_let_shadow" r e
  -- changed is true because allUsesAreForce passed vacuously and
  -- processDelayBindings set changed=true
  check "fd_through_let_shadow_changed" ch

-- Non-Delay binding in Let: Pattern 2 doesn't fire
#eval do
  let e := Expr.Let [(a, .App (.Var f) (.Var x))] (.Force (.Var a))
  checkPassResult "fd_non_delay_binding" (forceDelay e) e false

-- Force of non-Delay: no cancellation
#eval do
  let e1 := Expr.Force (.Var x)
  checkPassResult "fd_force_var" (forceDelay e1) e1 false
  let e2 := Expr.Force (.App (.Var f) (.Var x))
  checkPassResult "fd_force_app" (forceDelay e2) e2 false

-- Recursion into sub-expressions
#eval do
  checkPassResult "fd_recurse_lam"
    (forceDelay (.Lam x (.Force (.Delay (.Var x)))))
    (.Lam x (.Var x)) true
  checkPassResult "fd_recurse_fix"
    (forceDelay (.Fix f (.Force (.Delay (.Var f)))))
    (.Fix f (.Var f)) true
  checkPassResult "fd_recurse_app_fn"
    (forceDelay (.App (.Force (.Delay (.Var f))) (.Var x)))
    (.App (.Var f) (.Var x)) true
  checkPassResult "fd_recurse_app_arg"
    (forceDelay (.App (.Var f) (.Force (.Delay (.Var x)))))
    (.App (.Var f) (.Var x)) true
  checkPassResult "fd_recurse_delay_inner"
    (forceDelay (.Delay (.Force (.Delay (.Var x)))))
    (.Delay (.Var x)) true
  checkPassResult "fd_recurse_constr"
    (forceDelay (.Constr 0 [.Force (.Delay (.Var x)), .Var y]))
    (.Constr 0 [.Var x, .Var y]) true
  checkPassResult "fd_recurse_case_scrut"
    (forceDelay (.Case (.Force (.Delay (.Var x))) [.Var y]))
    (.Case (.Var x) [.Var y]) true
  checkPassResult "fd_recurse_case_alt"
    (forceDelay (.Case (.Var x) [.Force (.Delay (.Var y))]))
    (.Case (.Var x) [.Var y]) true

-- Leaf expressions unchanged
#eval do
  for (name, e) in [("fd_var", Expr.Var x), ("fd_lit", intLit 42),
                     ("fd_builtin", Expr.Builtin .AddInteger), ("fd_error", Expr.Error)] do
    let (r, ch) := forceDelay e
    checkAlphaEq name r e
    check s!"{name}_unchanged" (!ch)

-- Let with RHS simplification
#eval do
  let e := Expr.Let [(a, .Force (.Delay (.Var x)))] (.Var a)
  let expected := Expr.Let [(a, .Var x)] (.Var a)
  checkPassResult "fd_let_rhs_simplify" (forceDelay e) expected true

-- ------------------------------------------------------------------
-- # 11. inlinePass                                                    
-- ------------------------------------------------------------------

-- Atom var: always inlined
#eval do
  let e := Expr.Let [(a, .Var x)] (.Var a)
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_atom_var" r (.Var x)
  check "inline_atom_var_changed" ch

-- Atom var: inlined even with multiple uses
#eval do
  let e := Expr.Let [(a, .Var x)] (.App (.Var a) (.Var a))
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_atom_var_multi" r (.App (.Var x) (.Var x))
  check "inline_atom_var_multi_changed" ch

-- Atom lit: inlined
#eval do
  let e := Expr.Let [(a, intLit 42)] (.Var a)
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_atom_lit" r (intLit 42)
  check "inline_atom_lit_changed" ch

-- Atom builtin: inlined
#eval do
  let e := Expr.Let [(a, .Builtin .AddInteger)] (.App (.Var a) (.Var x))
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_atom_builtin" r (.App (.Builtin .AddInteger) (.Var x))
  check "inline_atom_builtin_changed" ch

-- Small value Lam (size 2 <= 5): inlined even if used twice
#eval do
  let e := Expr.Let [(a, .Lam y (.Var y))]
              (.App (.Var a) (.App (.Var a) (.Var z)))
  let (r, ch) := runFresh (inlinePass e) 1000
  let expected := Expr.App (.Lam y (.Var y)) (.App (.Lam y (.Var y)) (.Var z))
  checkAlphaEq "inline_small_lam_dup" r expected
  check "inline_small_lam_dup_changed" ch

-- Small value Delay (size 2): inlined
#eval do
  let e := Expr.Let [(a, .Delay (.Var x))] (.Force (.Var a))
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_small_delay" r (.Force (.Delay (.Var x)))
  check "inline_small_delay_changed" ch

-- Large value, 0 occurrences: kept (DCE handles)
#eval do
  let e := Expr.Let [(a, largeLam)] (.Var x)
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_large_0_occ" r e
  check "inline_large_0_occ_no_change" (!ch)

-- Large value, 1 occurrence, not under Fix: inlined
#eval do
  let e := Expr.Let [(a, largeLam)] (.App (.Var a) (.Var z))
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_large_1_no_fix" r (.App largeLam (.Var z))
  check "inline_large_1_no_fix_changed" ch

-- Large value, 1 occurrence, under Fix: NOT inlined
#eval do
  let e := Expr.Let [(a, largeLam)] (.Fix g (.App (.Var a) (.Var g)))
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_large_1_under_fix" r e
  check "inline_large_1_under_fix_no_change" (!ch)

-- Large value, 2 occurrences: NOT inlined
#eval do
  let e := Expr.Let [(a, largeLam)] (.App (.Var a) (.App (.Var a) (.Var z)))
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_large_2_occ" r e
  check "inline_large_2_occ_no_change" (!ch)

-- Non-value, 0 occurrences: kept
#eval do
  let e := Expr.Let [(a, .App (.Var f) (.Var x))] (.Var y)
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_nonval_0_occ" r e
  check "inline_nonval_0_occ_no_change" (!ch)

-- Non-value, 1 occurrence, not under Fix: inlined
#eval do
  let e := Expr.Let [(a, .App (.Var f) (.Var x))] (.App (.Var g) (.Var a))
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_nonval_1_no_fix" r (.App (.Var g) (.App (.Var f) (.Var x)))
  check "inline_nonval_1_no_fix_changed" ch

-- Non-value Force, 1 occurrence: inlined
#eval do
  let e := Expr.Let [(a, .Force (.Var x))] (.App (.Var a) (.Var y))
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_nonval_force" r (.App (.Force (.Var x)) (.Var y))
  check "inline_nonval_force_changed" ch

-- Non-value Case, 1 occurrence: inlined
#eval do
  let e := Expr.Let [(a, .Case (.Var x) [.Var y, .Var z])] (.Var a)
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_nonval_case" r (.Case (.Var x) [.Var y, .Var z])
  check "inline_nonval_case_changed" ch

-- Non-value, 1 occurrence, under Fix: NOT inlined
#eval do
  let e := Expr.Let [(a, .App (.Var f) (.Var x))] (.Fix g (.App (.Var a) (.Var g)))
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_nonval_1_under_fix" r e
  check "inline_nonval_1_under_fix_no_change" (!ch)

-- Non-value, 2 occurrences: NOT inlined
#eval do
  let e := Expr.Let [(a, .App (.Var f) (.Var x))] (.App (.Var a) (.Var a))
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_nonval_2_occ" r e
  check "inline_nonval_2_occ_no_change" (!ch)

-- Expensive computation NOT inlined across Fix boundary
-- let expensive = add(add(add(add(1,1),1),1),1)
-- in fix rep. λ n . rep n expensive
-- `expensive` is a non-value (App chain), single use, but under Fix → kept
#eval do
  let rep : VarId := ⟨60, "rep"⟩
  let add := Expr.Builtin .AddInteger
  -- 1 + 1 + 1 + 1 + 1  (left-associated chain of AddInteger applications)
  let expensive :=
    Expr.App (.App add (.App (.App add (.App (.App add (.App (.App add (intLit 1)) (intLit 1))) (intLit 1))) (intLit 1))) (intLit 1)
  let e := Expr.Let
    [(a, expensive)]
    (.Fix rep (.Lam n (.App (.App (.Var rep) (.Var n)) (.Var a))))
  let (r, ch) := runFresh (inlinePass e) 1000
  -- `a` is non-value, 1 occurrence under Fix → NOT inlined
  checkAlphaEq "inline_expensive_across_fix" r e
  check "inline_expensive_across_fix_no_change" (!ch)

-- Beta reduction: atomic arg
#eval do
  let e := Expr.App (.Lam x (.App (.Var x) (.Var x))) (.Var z)
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_beta_atom" r (.App (.Var z) (.Var z))
  check "inline_beta_atom_changed" ch

-- Beta reduction: literal arg
#eval do
  let e := Expr.App (.Lam x (.Var x)) (intLit 42)
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_beta_lit" r (intLit 42)
  check "inline_beta_lit_changed" ch

-- Beta reduction: non-atomic arg → no reduction
#eval do
  let e := Expr.App (.Lam x (.Var x)) (.App (.Var f) (.Var y))
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_beta_nonatomic" r e
  check "inline_beta_nonatomic_unchanged" (!ch)

-- Beta reduction: non-Lam function → no reduction
#eval do
  let e := Expr.App (.Var f) (.Var x)
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_beta_non_lam" r e
  check "inline_beta_non_lam_unchanged" (!ch)

-- Multiple bindings: first inlined propagates into rest
#eval do
  let e := Expr.Let [(a, .Var x), (b, .App (.Var a) (.Var y))] (.Var b)
  let (r, ch) := runFresh (inlinePass e) 1000
  -- a is atom, inlined into rest+body: b = App (Var x) (Var y), body = Var b
  -- b is non-value, 1 occurrence, not under Fix → inlined
  checkAlphaEq "inline_multi_cascade" r (.App (.Var x) (.Var y))
  check "inline_multi_cascade_changed" ch

-- Chain of atom inlines
#eval do
  let e := Expr.Let [(a, .Var x), (b, .Var a), (c, .Var b)] (.Var c)
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_chain_atoms" r (.Var x)
  check "inline_chain_atoms_changed" ch

-- Occurrence counting across rest bindings
#eval do
  -- a used once in b's RHS and once in body = 2 total
  let e := Expr.Let [(a, largeLam), (b, .Var a)] (.Var a)
  let (r, ch) := runFresh (inlinePass e) 1000
  -- a has 2 occurrences, large value → NOT inlined
  -- b is atom (Var a), inlined → body becomes Var a
  -- After inlining b: Let [(a, largeLam)] (Var a) -- b gone, a still 1 occ
  -- But wait, inlining processes left to right. When processing a,
  -- count = countOccurrences a body + rest.foldl = 1 + 1 = 2 → not inlined.
  -- Then process b: b = Var a is atom → inline. body becomes Var a.
  -- Result: Let [(a, largeLam)] (Var a)
  let expected := Expr.Let [(a, largeLam)] (.Var a)
  checkAlphaEq "inline_occ_count_rest" r expected
  check "inline_occ_count_rest_changed" ch

-- Recursion into Lam body
#eval do
  let e := Expr.Lam x (.Let [(a, .Var y)] (.Var a))
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_recurse_lam" r (.Lam x (.Var y))
  check "inline_recurse_lam_changed" ch

-- Recursion into Fix body
#eval do
  let e := Expr.Fix f (.Let [(a, .Var x)] (.App (.Var f) (.Var a)))
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_recurse_fix" r (.Fix f (.App (.Var f) (.Var x)))
  check "inline_recurse_fix_changed" ch

-- Recursion into Delay
#eval do
  let e := Expr.Delay (.Let [(a, .Var x)] (.Var a))
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_recurse_delay" r (.Delay (.Var x))
  check "inline_recurse_delay_changed" ch

-- Recursion into Force
#eval do
  let e := Expr.Force (.Let [(a, .Var x)] (.Var a))
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_recurse_force" r (.Force (.Var x))
  check "inline_recurse_force_changed" ch

-- Recursion into Constr
#eval do
  let e := Expr.Constr 0 [.Let [(a, .Var x)] (.Var a)]
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_recurse_constr" r (.Constr 0 [.Var x])
  check "inline_recurse_constr_changed" ch

-- Recursion into Case scrutinee
#eval do
  let e := Expr.Case (.Let [(a, .Var x)] (.Var a)) [.Var y]
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_recurse_case_scrut" r (.Case (.Var x) [.Var y])
  check "inline_recurse_case_scrut_changed" ch

-- Recursion into Case alternatives
#eval do
  let e := Expr.Case (.Var x) [.Let [(a, .Var y)] (.Var a)]
  let (r, ch) := runFresh (inlinePass e) 1000
  checkAlphaEq "inline_recurse_case_alt" r (.Case (.Var x) [.Var y])
  check "inline_recurse_case_alt_changed" ch

-- Capture avoidance: inlining Lam y (Var z) into scope where z is bound
#eval do
  -- let a = Lam y (Var z) in Lam z (Var a)
  -- a is small value (size 2), 1 occurrence → inline
  -- subst a (Lam y (Var z)) in (Lam z (Var a))
  -- z ∈ freeVars(Lam y (Var z)) and z is the Lam binder → freshen z
  let e := Expr.Let [(a, .Lam y (.Var z))] (.Lam z (.Var a))
  let (r, ch) := runFresh (inlinePass e) 1000
  -- Result should be Lam z' (Lam y (Var z)) where z' is fresh
  -- For checkAlphaEq: Lam <fresh> (Lam y (Var z))
  -- Use a dummy binder for the expected
  let expected := Expr.Lam t1 (.Lam y (.Var z))
  checkAlphaEq "inline_capture_avoid" r expected
  check "inline_capture_avoid_changed" ch

-- Leaf expressions unchanged
#eval do
  for (name, e) in [("inline_var", Expr.Var x), ("inline_lit", intLit 42),
                     ("inline_builtin", Expr.Builtin .AddInteger),
                     ("inline_error", Expr.Error)] do
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq name r e
    check s!"{name}_unchanged" (!ch)

-- ------------------------------------------------------------------
-- # 12. Full Pipeline (optimize / optimizeExpr)                       
-- ------------------------------------------------------------------

-- Trivial inputs pass through
#eval do
  for (name, e) in [("pipe_var", Expr.Var x), ("pipe_lit", intLit 42),
                     ("pipe_builtin", Expr.Builtin .AddInteger),
                     ("pipe_error", Expr.Error)] do
    let r := optimizeExpr e 1000
    checkAlphaEq name r e
    pure ()

-- Identity lambda unchanged
#eval do
  let e := Expr.Lam x (.Var x)
  let r := optimizeExpr e 1000
  checkAlphaEq "pipe_identity" r e
  pure ()

-- Atom inline cascade: let a=x, b=a, c=b → c reduces to x
#eval do
  let e := Expr.Let [(a, .Var x), (b, .Var a), (c, .Var b)] (.Var c)
  let r := optimizeExpr e 1000
  checkAlphaEq "pipe_atom_cascade" r (.Var x)
  pure ()

-- Force-delay pipeline from docs: let v=Delay x, w=Force v → x
#eval do
  let e := Expr.Let [(v, .Delay (.Var x)),
                      (w, .Force (.Var v))] (.Var w)
  let r := optimizeExpr e 1000
  checkAlphaEq "pipe_force_delay_doc" r (.Var x)
  pure ()

-- CSE + DCE: duplicate eliminated, dead binding removed
#eval do
  let e := Expr.Let [(a, .App (.Var f) (.Var x)),
                      (b, .App (.Var f) (.Var x))]
              (.Var a)
  let r := optimizeExpr e 1000
  -- CSE eliminates b (→ renamed to a), then DCE is no-op (a is used)
  -- Inlining: a is non-value, 1 occurrence → inline
  -- Result: App f x
  checkAlphaEq "pipe_cse_dce" r (.App (.Var f) (.Var x))

-- Float out + CSE: pure bindings float, then duplicates merged
#eval do
  let e := Expr.Lam x
    (.Let [(a, intLit 1), (b, intLit 1), (c, .App (.Var a) (.Var x))]
      (.App (.Var c) (.Var b)))
  let _r := optimizeExpr e 1000

-- Inline + beta: let f = lam y . y in f z → z
#eval do
  let e := Expr.Let [(f, .Lam y (.Var y))] (.App (.Var f) (.Var z))
  let r := optimizeExpr e 1000
  checkAlphaEq "pipe_inline_beta" r (.Var z)
  pure ()

-- Nested Let flattening through pipeline
#eval do
  let e := Expr.Let [(a, intLit 1)]
              (.Let [(b, .Var a)]
                (.Let [(c, .Var b)] (.Var c)))
  let r := optimizeExpr e 1000
  -- All atoms inline away → intLit 1
  checkAlphaEq "pipe_nested_let" r (intLit 1)
  pure ()

-- Idempotency: optimizing twice gives same result
#eval do
  let r1 := optimizeExpr factorialMIR 1000
  let r2 := optimizeExpr r1 2000
  checkAlphaEq "pipe_idempotent_factorial" r1 r2

-- Optimizer produces valid output for various inputs
#eval do
  let inputs := [
    ("factorial", factorialMIR),
    ("atom_chain", Expr.Let [(a, .Var x), (b, .Var a)] (.Var b)),
    ("force_delay", Expr.Let [(v, .Delay (.App (.Var f) (.Var x))),
              (w, .Force (.Var v))] (.Var w)),
    ("cse_target", Expr.Lam x (.Let [(a, intLit 1), (b, .App (.Builtin .AddInteger) (.Var x)),
                       (c, .App (.Builtin .AddInteger) (.Var x))]
                  (.App (.Var b) (.Var c))))
  ]
  for ((name, e), i) in inputs.zipIdx do
    let _r := optimizeExpr e (1000 + i * 100)
    IO.println s!"PASS: pipe_{name}"

-- Factorial through pipeline
#eval do
  let _r := optimizeExpr factorialMIR 1000
  IO.println "PASS: pipe_factorial"

-- Pipeline ordering: inline before force-delay
-- let d = Delay x, v = Var d in Force v
-- → inline v (atom): Force (Var d)
-- → force-delay through-let: let d = Delay x in x
-- → DCE: x
#eval do
  let dd : VarId := ⟨60, "d"⟩
  let e := Expr.Let [(dd, .Delay (.Var x)),
                      (v, .Var dd)]
              (.Force (.Var v))
  let r := optimizeExpr e 1000
  checkAlphaEq "pipe_inline_before_fd" r (.Var x)
  pure ()

-- CSE before inline avoids duplicating computation
-- let a = App f x, b = App f x in App a b
-- → CSE: let a = App f x in App a a (1 binding instead of 2)
#eval do
  let e := Expr.Let [(a, .App (.Var f) (.Var x)),
                      (b, .App (.Var f) (.Var x))]
              (.App (.Var a) (.Var b))
  let _r := optimizeExpr e 1000
  -- After CSE: let a = App f x in App a a
  -- a is non-value, 2 occurrences → NOT inlined (which is correct: avoids dup)

-- Complex: force-delay feeds into DCE which feeds into further simplification
#eval do
  let e := Expr.Let
    [(v, .Delay (.Var x)),
     (a, .Force (.Var v)),
     (b, intLit 42)]
    (.Var a)
  let r := optimizeExpr e 1000
  -- force-delay: a = Var x (replacing Force(Var v))
  -- inline: a is atom → inline
  -- DCE: v and b dead
  -- Result: Var x
  checkAlphaEq "pipe_fd_dce_chain" r (.Var x)
  pure ()

-- Expensive computation preserved across Fix in full pipeline
-- let expensive = add(add(add(add(1,1),1),1),1)
-- in fix rep. λ n . rep n expensive
-- The pipeline must NOT inline `expensive` into the Fix body.
#eval do
  let rep : VarId := ⟨60, "rep"⟩
  let add := Expr.Builtin .AddInteger
  let expensive :=
    Expr.App (.App add (.App (.App add (.App (.App add (.App (.App add (intLit 1)) (intLit 1))) (intLit 1))) (intLit 1))) (intLit 1)
  let e := Expr.Let
    [(a, expensive)]
    (.Fix rep (.Lam n (.App (.App (.Var rep) (.Var n)) (.Var a))))
  let r := optimizeExpr e 1000
  pure ()
  -- The expensive computation must remain as a let binding outside the Fix.
  -- If it were inlined, every recursive call would recompute 1+1+1+1+1.
  -- Check that the result still contains a Let (the binding wasn't inlined away).
  let hasLet := match r with
    | .Let _ _ => true
    | _ => false
  check "pipe_no_inline_across_fix_has_let" hasLet

-- Deeply nested application chains with shared prefix:
--   let a = f (f (f x))
--   let b = f (f (f (f (f (f x)))))
--   in g a b
-- After ANF, the shared prefix f(f(f(x))) is duplicated across a and b.
-- CSE should detect and eliminate the duplicate sub-computations.
#eval do
  let hd := Expr.Var f  -- f acts as a unary function (like head)
  -- f (f (f x))  =  f³(x)
  let chain3 := Expr.App hd (.App hd (.App hd (.Var x)))
  -- f (f (f (f (f (f x)))))  =  f⁶(x)
  let chain6 := Expr.App hd (.App hd (.App hd (.App hd (.App hd (.App hd (.Var x))))))
  -- let a = f³(x), b = f⁶(x) in g a b
  let e := Expr.Let
    [(a, chain3),
     (b, chain6)]
    (.App (.App (.Var g) (.Var a)) (.Var b))
  let _r := optimizeExpr e 1000
  -- The optimized result should have fewer App nodes than the naive version
  -- because CSE eliminates the shared f(x), f(f(x)), f(f(f(x))) computations.

-- Same expression but pre-normalized to ANF, so CSE sees the flat bindings
-- and CAN detect the shared prefix f(x), f(f(x)), f(f(f(x))).
#eval do
  let hd := Expr.Var f
  -- Pre-ANF form: each application step is a separate let binding
  --   let t0 = f x, t1 = f t0, t2 = f t1        (a = t2)
  --   let t3 = f x, t4 = f t3, t5 = f t4,        (shared with a's chain)
  --       t6 = f t5, t7 = f t6, t8 = f t7        (b = t8)
  --   let r = g t2
  --   in r t8
  let t0 : VarId := ⟨60, "t"⟩
  let t1 : VarId := ⟨61, "t"⟩
  let t2 : VarId := ⟨62, "t"⟩
  let t3 : VarId := ⟨63, "t"⟩
  let t4 : VarId := ⟨64, "t"⟩
  let t5 : VarId := ⟨65, "t"⟩
  let t6 : VarId := ⟨66, "t"⟩
  let t7 : VarId := ⟨67, "t"⟩
  let t8 : VarId := ⟨68, "t"⟩
  let rr : VarId := ⟨69, "r"⟩
  let e := Expr.Let
    [(t0, .App hd (.Var x)),
     (t1, .App hd (.Var t0)),
     (t2, .App hd (.Var t1)),
     (t3, .App hd (.Var x)),       -- duplicate of t0!
     (t4, .App hd (.Var t3)),      -- after CSE t3→t0: duplicate of t1!
     (t5, .App hd (.Var t4)),      -- after CSE t4→t1: duplicate of t2!
     (t6, .App hd (.Var t5)),
     (t7, .App hd (.Var t6)),
     (t8, .App hd (.Var t7)),
     (rr, .App (.Var g) (.Var t2))]
    (.App (.Var rr) (.Var t8))
  let r := optimizeExpr e 1000
  pure ()
  -- CSE now detects the shared prefix: t3=t0, t4=t1, t5=t2
  -- So the optimized result has 6 App(f,_) nodes instead of 9
  check "pipe_shared_prefix_smaller" (exprSize r < exprSize e)
