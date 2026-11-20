import Moist.MIR.Optimize.Advanced.Traversal

namespace Moist.MIR.Advanced

open Moist.Plutus.Term

/-- Both constants must fit one Plutus integer word. This preserves the
    integer checks and keeps the comparison's cost-model size fixed. -/
def oneWordThreshold (original shifted : Int) : Bool :=
  original.natAbs < 2 ^ 64 && shifted.natAbs < 2 ^ 64

/-- Use the cheaper inclusive comparison when one operand is a literal.
    Only saturated applications qualify, so no partially applied builtin
    values or evaluation order change. -/
def integerComparisonRoot (expression : Expr) : Expr :=
  match expression with
  | .App (.App (.Builtin .LessThanInteger) operand) (.Lit (.Integer k, .AtomicType .TypeInteger)) =>
    if oneWordThreshold k (k - 1) then
      .App (.App (.Builtin .LessThanEqualsInteger) operand) (.Lit (.Integer (k - 1), .AtomicType .TypeInteger))
    else expression
  | .App (.App (.Builtin .LessThanInteger) (.Lit (.Integer k, .AtomicType .TypeInteger))) operand =>
    if oneWordThreshold k (k + 1) then
      .App (.App (.Builtin .LessThanEqualsInteger) (.Lit (.Integer (k + 1), .AtomicType .TypeInteger))) operand
    else expression
  | _ => expression

def normalizeIntegerComparisons (expression : Expr) : Expr :=
  rewriteBottomUp integerComparisonRoot (exprSize expression) expression

end Moist.MIR.Advanced
