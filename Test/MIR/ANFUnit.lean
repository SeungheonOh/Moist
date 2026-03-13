import Test.MIR.Helpers

open Moist.MIR
open Test.MIR

/-! # ANF Normalization Unit Tests

Each test verifies:
1. The normalized output matches the expected structure (via alphaEq)
2. The output satisfies isANF
-/

-- Atoms pass through unchanged

#eval do
  for (name, e) in [
    ("atom_var",     Expr.Var x),
    ("atom_lit",     intLit 42),
    ("atom_builtin", Expr.Builtin .AddInteger),
    ("atom_error",   Expr.Error)
  ] do
    let r := normalize e
    checkAlphaEq s!"{name}" r e
    checkANF s!"{name}_anf" r

-- App with atomic operands: already ANF, unchanged

#eval do
  let e := Expr.App (.Var f) (.Var x)
  let r := normalize e
  checkAlphaEq "app_atomic" r e
  checkANF "app_atomic_anf" r

-- App with non-atomic function: let-bind the function

#eval do
  -- App (App f x) y  -->  let t = App f x in App t y
  let e := Expr.App (.App (.Var f) (.Var x)) (.Var y)
  let r := normalize e
  let expected := Expr.Let [(t1, .App (.Var f) (.Var x), false)] (.App (.Var t1) (.Var y))
  checkAlphaEq "app_nonatomic_fun" r expected
  checkANF "app_nonatomic_fun_anf" r

-- App with non-atomic argument: let-bind the argument

#eval do
  -- App f (App g x)  -->  let t = App g x in App f t
  let e := Expr.App (.Var f) (.App (.Var g) (.Var x))
  let r := normalize e
  let expected := Expr.Let [(t1, .App (.Var g) (.Var x), false)] (.App (.Var f) (.Var t1))
  checkAlphaEq "app_nonatomic_arg" r expected
  checkANF "app_nonatomic_arg_anf" r

-- App with both sides non-atomic: let-bind both

#eval do
  -- App (App f x) (App g y)
  --   --> let t1 = App f x; t2 = App g y in App t1 t2
  let e := Expr.App (.App (.Var f) (.Var x)) (.App (.Var g) (.Var y))
  let r := normalize e
  let expected :=
    Expr.Let [(t1, .App (.Var f) (.Var x), false),
              (t2, .App (.Var g) (.Var y), false)]
      (.App (.Var t1) (.Var t2))
  checkAlphaEq "app_both_nonatomic" r expected
  checkANF "app_both_nonatomic_anf" r

-- Force with atomic operand: unchanged

#eval do
  let e := Expr.Force (.Var x)
  let r := normalize e
  checkAlphaEq "force_atomic" r e
  checkANF "force_atomic_anf" r

-- Force with non-atomic operand: let-bind

#eval do
  -- force (App f x)  -->  let t = App f x in force t
  let e := Expr.Force (.App (.Var f) (.Var x))
  let r := normalize e
  let expected := Expr.Let [(t1, .App (.Var f) (.Var x), false)] (.Force (.Var t1))
  checkAlphaEq "force_nonatomic" r expected
  checkANF "force_nonatomic_anf" r

-- Constr with all atomic args: unchanged

#eval do
  let e := Expr.Constr 0 [.Var x, .Var y, .Var z]
  let r := normalize e
  checkAlphaEq "constr_atomic" r e
  checkANF "constr_atomic_anf" r

-- Constr with one non-atomic arg

#eval do
  -- Constr 0 [App f x, y]  -->  let t = App f x in Constr 0 [t, y]
  let e := Expr.Constr 0 [.App (.Var f) (.Var x), .Var y]
  let r := normalize e
  let expected := Expr.Let [(t1, .App (.Var f) (.Var x), false)] (.Constr 0 [.Var t1, .Var y])
  checkAlphaEq "constr_one_nonatomic" r expected
  checkANF "constr_one_nonatomic_anf" r

-- Constr with multiple non-atomic args

#eval do
  -- Constr 0 [App f x, App g y, z]
  --   --> let t1 = App f x; t2 = App g y in Constr 0 [t1, t2, z]
  let e := Expr.Constr 0 [.App (.Var f) (.Var x), .App (.Var g) (.Var y), .Var z]
  let r := normalize e
  let expected :=
    Expr.Let [(t1, .App (.Var f) (.Var x), false),
              (t2, .App (.Var g) (.Var y), false)]
      (.Constr 0 [.Var t1, .Var t2, .Var z])
  checkAlphaEq "constr_multi_nonatomic" r expected
  checkANF "constr_multi_nonatomic_anf" r

-- Case with atomic scrutinee: unchanged

#eval do
  let e := Expr.Case (.Var x) [.Var y, .Var z]
  let r := normalize e
  checkAlphaEq "case_atomic_scrut" r e
  checkANF "case_atomic_scrut_anf" r

-- Case with non-atomic scrutinee: let-bind

#eval do
  -- case (App f x) of [y, z]  -->  let t = App f x in case t of [y, z]
  let e := Expr.Case (.App (.Var f) (.Var x)) [.Var y, .Var z]
  let r := normalize e
  let expected :=
    Expr.Let [(t1, .App (.Var f) (.Var x), false)] (.Case (.Var t1) [.Var y, .Var z])
  checkAlphaEq "case_nonatomic_scrut" r expected
  checkANF "case_nonatomic_scrut_anf" r

-- Case alternatives get normalized

#eval do
  let e := Expr.Case (.Var x) [
    .App (.App (.Var f) (.Var y)) (.Var z),
    .Var a
  ]
  let r := normalize e
  let expected := Expr.Case (.Var x) [
    .Let [(t1, .App (.Var f) (.Var y), false)] (.App (.Var t1) (.Var z)),
    .Var a
  ]
  checkAlphaEq "case_normalize_alts" r expected
  checkANF "case_normalize_alts_anf" r

-- Let: RHS gets normalized

#eval do
  -- let a = App (App f x) y in Var a
  --   --> let t = App f x; a = App t y in Var a
  let e := Expr.Let [(a, .App (.App (.Var f) (.Var x)) (.Var y), false)] (.Var a)
  let r := normalize e
  let expected := Expr.Let
    [(t1, .App (.Var f) (.Var x), false),
     (a, .App (.Var t1) (.Var y), false)]
    (.Var a)
  checkAlphaEq "let_normalize_rhs" r expected
  checkANF "let_normalize_rhs_anf" r

-- Let: body gets normalized

#eval do
  let e := Expr.Let [(a, intLit 1, false)] (.App (.App (.Var f) (.Var a)) (.Var x))
  let r := normalize e
  let expected := Expr.Let
    [(a, intLit 1, false),
     (t1, .App (.Var f) (.Var a), false)]
    (.App (.Var t1) (.Var x))
  checkAlphaEq "let_normalize_body" r expected
  checkANF "let_normalize_body_anf" r

-- Let: multiple bindings all normalized

#eval do
  let e := Expr.Let
    [(a, .App (.App (.Var f) (.Var x)) (.Var y), false),
     (b, .App (.App (.Var g) (.Var a)) (.Var z), false)]
    (.App (.Var a) (.Var b))
  let r := normalize e
  checkANF "let_multi_bind_anf" r

-- Lam: body gets normalized

#eval do
  let e := Expr.Lam x (.App (.App (.Var f) (.Var x)) (.Var y))
  let r := normalize e
  let expected := Expr.Lam x
    (.Let [(t1, .App (.Var f) (.Var x), false)] (.App (.Var t1) (.Var y)))
  checkAlphaEq "lam_normalize_body" r expected
  checkANF "lam_normalize_body_anf" r

-- Fix: body gets normalized

#eval do
  let e := Expr.Fix f (.Lam x (.App (.App (.Var f) (.Var x)) (.Var y)))
  let r := normalize e
  let expected := Expr.Fix f (.Lam x
    (.Let [(t1, .App (.Var f) (.Var x), false)] (.App (.Var t1) (.Var y))))
  checkAlphaEq "fix_normalize_body" r expected
  checkANF "fix_normalize_body_anf" r

-- Delay: content gets normalized

#eval do
  let e := Expr.Delay (.App (.App (.Var f) (.Var x)) (.Var y))
  let r := normalize e
  let expected := Expr.Delay
    (.Let [(t1, .App (.Var f) (.Var x), false)] (.App (.Var t1) (.Var y)))
  checkAlphaEq "delay_normalize" r expected
  checkANF "delay_normalize_anf" r

-- Deeply nested application chain
-- App (App (App Add 1) 2) 3
--   inner: App Add 1 -> atomic args, stays. Let-bind result for outer.

#eval do
  let add := Expr.Builtin .AddInteger
  let e := Expr.App (.App (.App add (intLit 1)) (intLit 2)) (intLit 3)
  let r := normalize e
  checkANF "nested_app_chain_anf" r
  -- Verify the result has atoms in all App positions
  check "nested_app_chain_structure" r.isANF

-- Idempotency: normalizing a normalized expression gives alpha-equivalent result

#eval do
  let e := Expr.App (.App (.Var f) (.Var x)) (.App (.Var g) (.Var y))
  let n1 := normalize e 100
  let n2 := normalize n1 200
  checkAlphaEq "idempotent" n2 n1
  checkANF "idempotent_anf" n2

-- Idempotency on a more complex expression

#eval do
  let e := Expr.Force (.App (.App (.Builtin .IfThenElse) (boolLit true))
    (.Delay (intLit 1)))
  let n1 := normalize e 100
  let n2 := normalize n1 200
  checkAlphaEq "idempotent_complex" n2 n1
  checkANF "idempotent_complex_anf" n2

-- Factorial normalizes to ANF

#eval do
  let r := normalize factorialMIR
  checkANF "factorial_anf" r

-- noSelfRef holds after normalization on various inputs

#eval do
  let inputs := [
    Expr.App (.App (.Var f) (.Var x)) (.Var y),
    Expr.App (.Var f) (.App (.Var g) (.Var x)),
    Expr.Force (.App (.Var f) (.Var x)),
    Expr.Constr 0 [.App (.Var f) (.Var x), .Var y],
    factorialMIR
  ]
  for (e, i) in inputs.zipIdx do
    let r := normalize e (100 + i * 50)
    checkANF s!"noSelfRef_after_normalize_{i}" r

-- Empty Let and Constr edge cases

#eval do
  let e := Expr.Let [] (.Var x)
  let r := normalize e
  checkAlphaEq "let_empty_binds" r (.Let [] (.Var x))
  checkANF "let_empty_binds_anf" r

#eval do
  let e := Expr.Constr 0 []
  let r := normalize e
  checkAlphaEq "constr_no_args" r (.Constr 0 [])
  checkANF "constr_no_args_anf" r
