import Moist.MIR.Optimize.Advanced.Shapes

namespace Moist.MIR.Advanced

/-! # Data builtins on values of known shape

A kind guard `force (ifThenElse (chooseData x …) (delay x) (delay error))`
whose single `True` selects one kind becomes the matching unData builtin,
evaluated for its check only: `let _ = unBData x in x`.

(`equalsData d x` against a key `d = B k` is not rewritten to
`equalsByteString k (unBData (chooseData x n n n n x))`: under builtin
semantics variant E `equalsByteString` and `appendByteString` reject
bytestrings longer than 65536 bytes, where `equalsData` and `unBData` succeed.)
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

end Moist.MIR.Advanced
