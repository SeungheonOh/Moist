import Test.MIR.Opt.Soundness
import Moist.MIR.Compile

namespace Test.MIR.Opt.IntegerComparisons

open Moist.MIR Moist.Plutus.Term Test.MIR Test.Framework

private def compare (builtin : BuiltinFun) (left right : Expr) : Expr :=
  .App (.App (.Builtin builtin) left) right

private def traced (value : Expr) : Expr :=
  .App (.App (.Force (.Builtin .Trace))
    (.Lit (.String "operand", .AtomicType .TypeString))) value

def tests : TestTree := suite "integer comparisons" do
  test "rewrites_saturated_comparisons" do
    let input := sourceVar 9100
    let operand := Expr.Var input
    let original := compare .LessThanInteger operand (intLit 2)
    let inclusive := compare .LessThanEqualsInteger operand (intLit 1)
    check "right literal decrements" (Advanced.integerComparisonRoot original == inclusive)
    check "left literal increments" (Advanced.integerComparisonRoot
      (compare .LessThanInteger (intLit (-1)) operand) ==
        compare .LessThanEqualsInteger (intLit 0) operand)
    check "production compiler sees the saturated comparison" (alphaEq
      (prepareForLowering (.Lam input original)) (.Lam input inclusive))
  test "leaves_partial_or_width_changing_comparisons" do
    let operand := Expr.Var (sourceVar 9100)
    let partialCall := Expr.App (.Builtin .LessThanInteger) (intLit 2)
    let high := compare .LessThanInteger (intLit (2 ^ (64 : Nat) - 1)) operand
    let low := compare .LessThanInteger operand (intLit (1 - 2 ^ (64 : Nat)))
    let wrongType := compare .LessThanInteger operand (.Lit (.Integer 2, .AtomicType .TypeBool))
    for candidate in [partialCall, high, low, wrongType] do
      check "ineligible comparison unchanged" (Advanced.normalizeIntegerComparisons candidate == candidate)
  test "preserves_operand_traces_values_and_failure" do
    let large := intLit (2 ^ (64 : Nat) + 1)
    for operand in [traced (intLit (-2)), traced (intLit 1), traced (intLit 2),
        traced large, traced (boolLit true), .Error] do
      for original in [compare .LessThanInteger operand (intLit 2),
          compare .LessThanInteger (intLit 2) operand] do
        let revised := Advanced.normalizeIntegerComparisons original
        check "same traces and result" ((← Soundness.tracedObservation revised) ==
          (← Soundness.tracedObservation original))

end Test.MIR.Opt.IntegerComparisons
