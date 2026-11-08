import Moist.MIR.Optimize.Advanced.Shapes

namespace Moist.MIR.Advanced

/-! # Data builtins on values of known shape

A kind guard `force (ifThenElse (chooseData x …) (delay x) (delay error))`
whose single `True` selects one kind becomes the matching unData builtin,
evaluated for its check only: `let _ = unBData x in x`.

`insertKeyGuards` binds, after each `k = unBData d` whose scope compares
`d` with `equalsData`, the length test, comparison and other `B` value that
`keyComparison` (in the fact-driven simplifier) uses to compare against `d`
without `equalsData`.
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

/-! ## Guards of keys compared with `equalsData` -/

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

/-- A case on an `equalsData` comparison with `d`. -/
def comparesKey (d : VarId) : Expr → Bool
  | .Case (.App (.App (.Builtin .EqualsData) first) second) [_, _] => first == .Var d || second == .Var d
  | _ => false

def isLengthOf (k : VarId) (expression : Expr) : Bool :=
  expression == lengthApp k

def unBDataSource : Expr → Option VarId
  | .App (.Builtin .UnBData) (.Var d) => some d
  | _ => none

mutual
  def keyGuardWalk (base : Nat) (expression : Expr) : Expr :=
    match expression with
    | .Let binds body =>
      let processed := keyGuardBindings base binds body
      .Let processed.1 processed.2
    | .Lam binder body => .Lam binder (keyGuardWalk base body)
    | .Fix binder body => .Fix binder (keyGuardWalk base body)
    | .App function argument => .App (keyGuardWalk base function) (keyGuardWalk base argument)
    | .Force body => .Force (keyGuardWalk base body)
    | .Delay body => .Delay (keyGuardWalk base body)
    | .Constr tag fields => .Constr tag (fields.attach.map fun ⟨field, _⟩ => keyGuardWalk base field)
    | .Case scrutinee alternatives =>
      .Case (keyGuardWalk base scrutinee)
        (alternatives.attach.map fun ⟨alternative, _⟩ => keyGuardWalk base alternative)
    | .Var _ | .Lit _ | .Builtin _ | .Error => expression
  termination_by 2 * exprSize expression
  decreasing_by
    all_goals first
      | (simp only [exprSize]; omega)
      | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)

  def keyGuardBindings (base : Nat) :
      List (VarId × Expr × Bool) → Expr → List (VarId × Expr × Bool) × Expr
    | [], body => ([], keyGuardWalk base body)
    | (binder, rhs, erased) :: rest, body =>
      let processed := keyGuardBindings base rest body
      let rhs' := keyGuardWalk base rhs
      let scope := Expr.Let processed.1 processed.2
      match unBDataSource rhs' with
      | some d =>
        if anyExpr (comparesKey d) (exprSize scope) scope &&
            !anyExpr (isLengthOf binder) (exprSize scope) scope then
          let first := max base (max binder.uid (max (maxUidExpr rhs') (maxUidExpr scope)) + 1)
          let lengthTest : VarId := { uid := first, origin := .gen, hint := "keyLength" }
          let compare : VarId := { uid := first + 1, origin := .gen, hint := "keyCompare" }
          let other : VarId := { uid := first + 2, origin := .gen, hint := "otherKey" }
          let headBinder : VarId := { uid := first + 3, origin := .gen, hint := "unit" }
          let tailBinder : VarId := { uid := first + 4, origin := .gen, hint := "units" }
          let bytes : VarId := { uid := first + 5, origin := .gen, hint := "bytes" }
          let choose : VarId := { uid := first + 6, origin := .gen, hint := "chooseData" }
          ((binder, rhs', erased) :: (lengthTest, guardLength binder, false) ::
            (compare, guardCompare d binder headBinder tailBinder bytes, false) ::
            (other, guardOther lengthTest, false) ::
            (choose, .Force (.Builtin .ChooseData), false) :: processed.1, processed.2)
        else ((binder, rhs', erased) :: processed.1, processed.2)
      | none => ((binder, rhs', erased) :: processed.1, processed.2)
  termination_by binds body => 2 * (exprSizeBinds binds + exprSize body) + 1
  decreasing_by
    all_goals simp only [exprSizeBinds]
    all_goals first
      | omega
      | (have := exprSize_pos rhs; omega)
end

/-- Bind, after each `k = unBData d` whose scope compares `d` with
    `equalsData`, the guards `keyComparison` compares against `d` with. -/
def insertKeyGuards (expression : Expr) : Expr :=
  let unique := uniqueOptimizationBinders expression
  if wellScoped unique then keyGuardWalk (maxUidExpr unique + 1) unique else unique

end Moist.MIR.Advanced
