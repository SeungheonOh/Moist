import Moist.MIR.Optimize.Advanced.Shapes

namespace Moist.MIR.Advanced

/-! # Data builtins on values of known shape

`equalsData` costs about a million CPU units on every call, whatever the size of
its arguments. When one side `d` is known to be `B k`, the comparison only has
to check that the other side is a `B` value with the same bytes.
`chooseData x n n n n x` returns `x` when it is a `B` value and the `B` value
`n` otherwise, so

```
equalsData d x = equalsByteString k (unBData (chooseData x n n n n x))
```

whenever the bytes of `n` differ from `k`. The rewritten form costs much less
CPU but about eleven more machine steps, so it is applied only to keys `d` with
a dominating binding `k = unBData d`, the shape of decoded map keys compared in
lookup loops, and not to literal comparisons. `insertKeyBytes` binds
`t = appendByteString #00 k` and `n = bData t` right after `k`, once, when the
scope compares `d`, and the fact-driven simplifier (`dataComparison`) rewrites
the comparisons inside the scope.

A kind guard `force (ifThenElse (chooseData x …) (delay x) (delay error))`
whose single `True` selects one kind becomes the matching unData builtin,
evaluated for its check only: `let _ = unBData x in x`.
-/

open Moist.Plutus.Term

def boolLiteral? : Expr → Option Bool
  | .Lit (.Bool value, _) => some value
  | _ => none

/-- The unData builtin checking the kind selected by a one-hot `chooseData`
    guard. -/
def kindChecker : List Bool → Option BuiltinFun
  | [true, false, false, false, false] => some .UnConstrData
  | [false, true, false, false, false] => some .UnMapData
  | [false, false, true, false, false] => some .UnListData
  | [false, false, false, true, false] => some .UnIData
  | [false, false, false, false, true] => some .UnBData
  | _ => none

/-- `chooseData (Var x) c₀ … c₄` with Boolean literal branches selecting a
    single kind. -/
def kindGuard : Expr → Option (VarId × BuiltinFun)
  | .App (.App (.App (.App (.App (.App (.Force (.Builtin .ChooseData)) (.Var x)) c₀) c₁) c₂) c₃) c₄ => do
    let checker ← kindChecker [← boolLiteral? c₀, ← boolLiteral? c₁, ← boolLiteral? c₂,
      ← boolLiteral? c₃, ← boolLiteral? c₄]
    return (x, checker)
  | _ => none

def checkedBinder (x : VarId) : VarId := { uid := x.uid + 1, origin := .gen, hint := "checked" }

/-- Local rewrites that need no facts. -/
def dataCheckRewrite (expression : Expr) : Expr :=
  match expression with
  | .Force (.App (.App (.App (.Force (.Builtin .IfThenElse)) condition) (.Delay (.Var x))) (.Delay .Error)) =>
    match kindGuard condition with
    | some (y, checker) =>
      if y == x then .Let [(checkedBinder x, .App (.Builtin checker) (.Var x), false)] (.Var x)
      else expression
    | none => expression
  | _ => expression

def specializeDataChecks (expression : Expr) : Expr :=
  rewriteBottomUp dataCheckRewrite (exprSize expression) expression

/-! ## Bytes of keys compared with `equalsData` -/

/-- Whether some subexpression satisfies `p`. -/
def anyExpr (p : Expr → Bool) : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, expression =>
    p expression ||
      match expression with
      | .Lam _ body | .Fix _ body | .Force body | .Delay body => anyExpr p fuel body
      | .App function argument => anyExpr p fuel function || anyExpr p fuel argument
      | .Constr _ fields => fields.any (anyExpr p fuel)
      | .Case scrutinee alternatives => anyExpr p fuel scrutinee || alternatives.any (anyExpr p fuel)
      | .Let bindings body => bindings.any (fun binding => anyExpr p fuel binding.2.1) || anyExpr p fuel body
      | .Var _ | .Lit _ | .Builtin _ | .Error => false

/-- Every let binding of an expression. -/
def letBindingsOf : Nat → Expr → List (VarId × Expr)
  | 0, _ => []
  | fuel + 1, expression =>
    match expression with
    | .Let bindings body =>
      bindings.flatMap (fun binding => (binding.1, binding.2.1) :: letBindingsOf fuel binding.2.1) ++
        letBindingsOf fuel body
    | .Lam _ body | .Fix _ body | .Force body | .Delay body => letBindingsOf fuel body
    | .App function argument => letBindingsOf fuel function ++ letBindingsOf fuel argument
    | .Constr _ fields => fields.flatMap (letBindingsOf fuel)
    | .Case scrutinee alternatives =>
      letBindingsOf fuel scrutinee ++ alternatives.flatMap (letBindingsOf fuel)
    | .Var _ | .Lit _ | .Builtin _ | .Error => []

/-- An `equalsData` application between `d` and another variable, its partial
    application possibly bound by `bindings`. -/
def comparesKey (bindings : List (VarId × Expr)) (d : VarId) : Expr → Bool
  | .App function (.Var b) =>
    match resolveHead 64 bindings function with
    | .App (.Builtin .EqualsData) (.Var a) => (a == d && !(b == d)) || (b == d && !(a == d))
    | _ => false
  | _ => false

def zeroByteLiteral : Expr := .Lit (.ByteString zeroByte, .AtomicType .TypeByteString)

def prefixedKey (k : VarId) : Expr :=
  .App (.App (.Builtin .AppendByteString) zeroByteLiteral) (.Var k)

def isPrefixedKey (bindings : List (VarId × Expr)) (k : VarId) : Expr → Bool
  | .App function (.Var y) =>
    y == k &&
      match resolveHead 64 bindings function with
      | .App (.Builtin .AppendByteString) (.Lit (.ByteString bytes, _)) => bytes == zeroByte
      | _ => false
  | _ => false

def unBDataSource : Expr → Option VarId
  | .App (.Builtin .UnBData) (.Var d) => some d
  | _ => none

mutual
  def keyBytesWalk (base : Nat) (bindings : List (VarId × Expr)) (expression : Expr) : Expr :=
    match expression with
    | .Let binds body =>
      let processed := keyBytesBindings base bindings binds body
      .Let processed.1 processed.2
    | .Lam binder body => .Lam binder (keyBytesWalk base bindings body)
    | .Fix binder body => .Fix binder (keyBytesWalk base bindings body)
    | .App function argument => .App (keyBytesWalk base bindings function) (keyBytesWalk base bindings argument)
    | .Force body => .Force (keyBytesWalk base bindings body)
    | .Delay body => .Delay (keyBytesWalk base bindings body)
    | .Constr tag fields => .Constr tag (fields.attach.map fun ⟨field, _⟩ => keyBytesWalk base bindings field)
    | .Case scrutinee alternatives =>
      .Case (keyBytesWalk base bindings scrutinee)
        (alternatives.attach.map fun ⟨alternative, _⟩ => keyBytesWalk base bindings alternative)
    | .Var _ | .Lit _ | .Builtin _ | .Error => expression
  termination_by 2 * exprSize expression
  decreasing_by
    all_goals first
      | (simp only [exprSize]; omega)
      | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)

  def keyBytesBindings (base : Nat) (bindings : List (VarId × Expr)) :
      List (VarId × Expr × Bool) → Expr → List (VarId × Expr × Bool) × Expr
    | [], body => ([], keyBytesWalk base bindings body)
    | (binder, rhs, erased) :: rest, body =>
      let processed := keyBytesBindings base bindings rest body
      let rhs' := keyBytesWalk base bindings rhs
      let scope := Expr.Let processed.1 processed.2
      match unBDataSource rhs' with
      | some d =>
        if anyExpr (comparesKey bindings d) (exprSize scope) scope &&
            !anyExpr (isPrefixedKey bindings binder) (exprSize scope) scope then
          let bytes : VarId :=
            { uid := max base (max binder.uid (maxUidExpr scope) + 1), origin := .gen, hint := "keyBytes" }
          let other : VarId := { uid := bytes.uid + 1, origin := .gen, hint := "otherKey" }
          ((binder, rhs', erased) :: (bytes, prefixedKey binder, false) ::
            (other, .App (.Builtin .BData) (.Var bytes), false) :: processed.1, processed.2)
        else ((binder, rhs', erased) :: processed.1, processed.2)
      | none => ((binder, rhs', erased) :: processed.1, processed.2)
  termination_by binds body => 2 * (exprSizeBinds binds + exprSize body) + 1
  decreasing_by
    all_goals simp only [exprSizeBinds]
    all_goals first
      | omega
      | (have := exprSize_pos rhs; omega)
end

/-- Bind the bytes of each `unBData` key compared with `equalsData` in its
    scope, prefixed with a zero byte, and the `B` value of those bytes. -/
def insertKeyBytes (expression : Expr) : Expr :=
  let unique := uniqueOptimizationBinders expression
  if wellScoped unique then
    keyBytesWalk (maxUidExpr unique + 1) (letBindingsOf (exprSize unique) unique) unique
  else unique

end Moist.MIR.Advanced
