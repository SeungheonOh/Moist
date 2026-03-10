import Test.MIR.Helpers

open Moist.MIR
open Test.MIR

/-! # Analysis Unit Tests -/

-- isAtom

#eval do
  check "isAtom_var" (Expr.Var x).isAtom
  check "isAtom_lit" (intLit 42).isAtom
  check "isAtom_builtin" (Expr.Builtin .AddInteger).isAtom
  check "not_isAtom_app" (!(Expr.App (.Var f) (.Var x)).isAtom)
  check "not_isAtom_lam" (!(Expr.Lam x (.Var x)).isAtom)
  check "not_isAtom_let" (!(Expr.Let [(x, .Var y)] (.Var x)).isAtom)
  check "not_isAtom_error" (!Expr.Error.isAtom)

-- isValue

#eval do
  check "isValue_var" (Expr.Var x).isValue
  check "isValue_lit" (intLit 42).isValue
  check "isValue_builtin" (Expr.Builtin .AddInteger).isValue
  check "isValue_lam" (Expr.Lam x (.Var x)).isValue
  check "isValue_delay" (Expr.Delay (.Var x)).isValue
  check "isValue_fix" (Expr.Fix f (.Lam x (.Var x))).isValue
  check "not_isValue_app" (!(Expr.App (.Var f) (.Var x)).isValue)
  check "not_isValue_force" (!(Expr.Force (.Var x)).isValue)
  check "not_isValue_constr" (!(Expr.Constr 0 [.Var x]).isValue)

-- freeVars

#eval do
  check "fv_var" ((freeVars (.Var x)).contains x)
  check "fv_var_only" (!(freeVars (.Var x)).contains y)
  check "fv_lit_empty" ((freeVars (intLit 42)).data.isEmpty)
  check "fv_builtin_empty" ((freeVars (.Builtin .AddInteger)).data.isEmpty)
  check "fv_error_empty" ((freeVars .Error).data.isEmpty)

#eval do
  -- Lam binds its parameter
  check "fv_lam_binds" (!(freeVars (.Lam x (.Var x))).contains x)
  check "fv_lam_free" ((freeVars (.Lam x (.Var y))).contains y)
  check "fv_lam_free_not_bound" (!(freeVars (.Lam x (.Var y))).contains x)

#eval do
  -- App unions free vars
  let e := Expr.App (.Var x) (.Var y)
  let fv := freeVars e
  check "fv_app_left" (fv.contains x)
  check "fv_app_right" (fv.contains y)

#eval do
  -- Fix binds the self-reference
  let e := Expr.Fix f (.Lam x (.App (.Var f) (.Var x)))
  let fv := freeVars e
  check "fv_fix_binds_self" (!fv.contains f)
  check "fv_fix_lam_binds_param" (!fv.contains x)
  check "fv_fix_closed" (fv.data.isEmpty)

#eval do
  -- Let sequential scoping: e2 can see x1, body sees both
  let e := Expr.Let
    [(x, .Var a),
     (y, .App (.Var x) (.Var b))]
    (.App (.Var x) (.Var y))
  let fv := freeVars e
  check "fv_let_seq_a_free" (fv.contains a)
  check "fv_let_seq_b_free" (fv.contains b)
  check "fv_let_seq_x_bound" (!fv.contains x)
  check "fv_let_seq_y_bound" (!fv.contains y)

#eval do
  -- Let: rhs of first binding cannot see later bindings
  -- let x = y in ... where y is defined LATER is still free
  let e := Expr.Let
    [(x, .Var y),
     (y, intLit 1)]
    (.Var x)
  let fv := freeVars e
  check "fv_let_forward_ref_y_free" (fv.contains y)

-- noSelfRef

#eval do
  check "noSelfRef_ok" (noSelfRef [(x, .Var y)])
  check "noSelfRef_ok_refs_earlier" (noSelfRef [(x, intLit 1), (y, .Var x)])
  check "noSelfRef_fail" (!(noSelfRef [(x, .Var x)]))
  check "noSelfRef_fail_second" (!(noSelfRef [(x, intLit 1), (y, .App (.Var y) (.Var x))]))
  check "noSelfRef_empty" (noSelfRef [])

-- countOccurrences

#eval do
  checkEq "count_zero" (countOccurrences x (intLit 42)) 0
  checkEq "count_one" (countOccurrences x (.Var x)) 1
  checkEq "count_two" (countOccurrences x (.App (.Var x) (.Var x))) 2

#eval do
  -- Shadowed by Lam
  checkEq "count_shadowed_lam" (countOccurrences x (.Lam x (.Var x))) 0

#eval do
  -- Shadowed partway through Let
  let e := Expr.Let
    [(y, .Var x),
     (x, intLit 1)]
    (.Var x)
  checkEq "count_let_before_shadow" (countOccurrences x e) 1

#eval do
  -- Not shadowed
  let e := Expr.Let [(y, .Var x)] (.Var x)
  checkEq "count_let_no_shadow" (countOccurrences x e) 2

-- exprSize

#eval do
  checkEq "size_var" (exprSize (.Var x)) 1
  checkEq "size_lit" (exprSize (intLit 42)) 1
  checkEq "size_app" (exprSize (.App (.Var f) (.Var x))) 3
  checkEq "size_lam" (exprSize (.Lam x (.Var x))) 2
  checkEq "size_let" (exprSize (.Let [(x, intLit 1)] (.Var x))) 3

-- isANF

#eval do
  check "isANF_var" (Expr.Var x).isANF
  check "isANF_lit" (intLit 42).isANF
  check "isANF_builtin" (Expr.Builtin .AddInteger).isANF
  check "isANF_error" Expr.Error.isANF
  check "isANF_app_atoms" (Expr.App (.Var f) (.Var x)).isANF
  check "isANF_force_atom" (Expr.Force (.Var x)).isANF
  check "isANF_constr_atoms" (Expr.Constr 0 [.Var x, .Var y]).isANF
  check "isANF_case_atom_scrut" (Expr.Case (.Var x) [.Var y, .Var z]).isANF
  check "isANF_lam_anf_body" (Expr.Lam x (.App (.Var f) (.Var x))).isANF
  check "isANF_let_valid" (Expr.Let [(x, intLit 1)] (.Var x)).isANF

#eval do
  -- Non-ANF: App with non-atomic function
  check "not_isANF_app_complex_fun"
    (!(Expr.App (.App (.Var f) (.Var x)) (.Var y)).isANF)
  -- Non-ANF: App with non-atomic arg
  check "not_isANF_app_complex_arg"
    (!(Expr.App (.Var f) (.App (.Var g) (.Var x))).isANF)
  -- Non-ANF: Force on non-atom
  check "not_isANF_force_complex"
    (!(Expr.Force (.App (.Var f) (.Var x))).isANF)
  -- Non-ANF: Constr with non-atom
  check "not_isANF_constr_complex"
    (!(Expr.Constr 0 [.App (.Var f) (.Var x)]).isANF)
  -- Non-ANF: self-referential Let
  check "not_isANF_self_ref"
    (!(Expr.Let [(x, .Var x)] (.Var x)).isANF)

-- uncurryApp

#eval do
  let (head, args) := uncurryApp (.App (.App (.Var f) (.Var x)) (.Var y))
  check "uncurry_head" (alphaEq head (.Var f))
  checkEq "uncurry_args_len" args.length 2

-- isClosed / fixIsRecursive

#eval do
  check "isClosed_lit" (isClosed (intLit 42))
  check "not_isClosed_var" (!isClosed (.Var x))
  check "isClosed_lam" (isClosed (.Lam x (.Var x)))

#eval do
  check "fixIsRecursive_yes" (fixIsRecursive f (.App (.Var f) (.Var x)))
  check "fixIsRecursive_no" (!fixIsRecursive f (.Var x))
