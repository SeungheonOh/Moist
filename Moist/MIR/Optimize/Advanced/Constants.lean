import Moist.MIR.Optimize.Advanced.Traversal
import Moist.Plutus.Encode

namespace Moist.MIR.Advanced

/-! Bounded folding for a deliberately small builtin subset. Scalar folding
checks literal annotations and the complete force/application protocol, rejects
failures and Trace, and bounds intermediate values. Data construction carries
explicit list element types instead of inferring them from empty payloads.
-/

open Moist.Plutus.Term

def foldableBuiltin : BuiltinFun → Bool
  | .AddInteger | .SubtractInteger | .MultiplyInteger | .DivideInteger
  | .QuotientInteger | .RemainderInteger | .ModInteger | .EqualsInteger
  | .LessThanInteger | .LessThanEqualsInteger | .AppendByteString
  | .LengthOfByteString | .EqualsByteString | .AppendString | .EqualsString
  | .EncodeUtf8 | .DecodeUtf8 => true
  | _ => false

def smallScalar : Const → Bool
  | .Integer number => number.natAbs < 2 ^ 256
  | .ByteString bytes => bytes.size <= 1024
  | .String string => string.utf8ByteSize <= 1024
  | .Bool _ | .Unit => true
  | _ => false

def constantValue : Expr → Option Moist.CEK.CekValue
  | .Lit (constant, annotation) =>
    if smallScalar constant && annotation == constType constant then some (.VCon constant) else none
  | .Builtin builtin =>
    if foldableBuiltin builtin then some (.VBuiltin builtin [] (Moist.CEK.expectedArgs builtin)) else none
  | .Force expression => do
    let .VBuiltin builtin arguments remaining ← constantValue expression | none
    if remaining.head != .argQ then none
    else return .VBuiltin builtin arguments (← remaining.tail)
  | .App function argument => do
    let .VBuiltin builtin arguments remaining ← constantValue function | none
    let value ← constantValue argument
    if remaining.head != .argV then none
    else match remaining.tail with
      | some rest => some (.VBuiltin builtin (value :: arguments) rest)
      | none => do
        let result ← Moist.CEK.evalBuiltin builtin (value :: arguments)
        match result with
        | .VCon constant => if smallScalar constant then some result else none
        | _ => none
  | _ => none

def foldConstant (expression : Expr) : Expr :=
  if expression.isAtom then expression else
  match constantValue expression with
  | some (.VCon constant) =>
    if smallScalar constant then .Lit (constant, constType constant) else expression
  | _ => expression

def constantFold (expression : Expr) : Expr :=
  rewriteBottomUp foldConstant (exprSize expression) expression

def dataListType : BuiltinType :=
  .TypeOperator (.TypeList (.AtomicType .TypeData))

def literalData : Expr → Option Moist.Plutus.Data
  | .Lit (.Data value, .AtomicType .TypeData) => some value
  | _ => none

def literalDataList : Expr → Option (List Moist.Plutus.Data)
  | .Lit (.ConstDataList values, annotation) =>
    if annotation == dataListType then some values else none
  | .Lit (.ConstList values, annotation) =>
    if annotation == dataListType then
      values.mapM fun value => match value with
        | .Data datum => some datum
        | _ => none
    else none
  | _ => none

def foldedDataConstructor : Expr → Option (Const × BuiltinType)
  | .App (.Builtin .IData) (.Lit (.Integer number, .AtomicType .TypeInteger)) =>
    some (.Data (.I number), .AtomicType .TypeData)
  | .App (.Builtin .BData) (.Lit (.ByteString value, .AtomicType .TypeByteString)) =>
    some (.Data (.B value), .AtomicType .TypeData)
  | .App (.Builtin .MkNilData) (.Lit (.Unit, .AtomicType .TypeUnit)) =>
    some (.ConstDataList [], dataListType)
  | .App (.App (.Force (.Builtin .MkCons)) head) tail => do
    let values := (← literalData head) :: (← literalDataList tail)
    match tail with
    | .Lit (.ConstList _, _) => return (.ConstList (values.map Const.Data), dataListType)
    | _ => return (.ConstDataList values, dataListType)
  | .App (.Builtin .ListData) fields => do
    return (.Data (.List (← literalDataList fields)), .AtomicType .TypeData)
  | .App (.App (.Builtin .ConstrData) (.Lit (.Integer tag, .AtomicType .TypeInteger))) fields => do
    if tag < 0 || tag >= 2 ^ 64 then none else
      return (.Data (.Constr tag (← literalDataList fields)), .AtomicType .TypeData)
  | _ => none

def foldDataConstructor (expression : Expr) : Expr :=
  match foldedDataConstructor expression with
  | some literal =>
    if (Moist.Plutus.Encode.encode_program
        (.Program (.Version 1 1 0) (.Constant literal))).toByteList.length <= 1024 then
      .Lit literal
    else expression
  | none => expression

def foldDataConstructors (expression : Expr) : Expr :=
  rewriteBottomUp foldDataConstructor (exprSize expression) expression

end Moist.MIR.Advanced
