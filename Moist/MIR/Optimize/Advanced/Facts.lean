import Moist.MIR.Optimize.Advanced.Traversal

namespace Moist.MIR.Advanced

open Moist.Plutus.Term

def resolveHead : Nat → List (VarId × Expr) → Expr → Expr
  | 0, _, expression => expression
  | fuel + 1, environment, .Var binder =>
    match environment.find? (fun entry => entry.1 == binder) with
    | some (_, rhs) => resolveHead fuel environment rhs
    | none => .Var binder
  | fuel + 1, environment, .App function argument =>
    .App (resolveHead fuel environment function) argument
  | fuel + 1, environment, .Force body => .Force (resolveHead fuel environment body)
  | _, _, expression => expression

def booleanBuiltin : BuiltinFun → Bool
  | .EqualsInteger | .LessThanInteger | .LessThanEqualsInteger
  | .EqualsByteString | .LessThanByteString | .LessThanEqualsByteString
  | .EqualsString | .EqualsData | .NullList | .VerifyEd25519Signature
  | .VerifyEcdsaSecp256k1Signature | .VerifySchnorrSecp256k1Signature => true
  | _ => false

def builtinProtocolAfterSuccess : Expr → Option (BuiltinFun × Moist.CEK.ExpectedArgs)
  | .Builtin builtin => some (builtin, Moist.CEK.expectedArgs builtin)
  | .Force body => do
    let (builtin, remaining) ← builtinProtocolAfterSuccess body
    if remaining.head != .argQ then none else
      return (builtin, ← remaining.tail)
  | .App function _ => do
    let (builtin, remaining) ← builtinProtocolAfterSuccess function
    if remaining.head != .argV then none else
      return (builtin, ← remaining.tail)
  | _ => none

def constructorPair : Nat → List (VarId × Expr) → Expr → Bool
  | 0, _, _ => false
  | fuel + 1, environment, expression =>
    match expression with
    | .Var binder =>
      (environment.find? (fun entry => entry.1 == binder)).any
        (fun entry => constructorPair fuel environment entry.2)
    | .App function _ =>
      match resolveHead fuel environment function with
      | .Builtin .UnConstrData => true
      | _ => false
    | _ => false

def knownList : Nat → List (VarId × Expr) → Expr → Bool
  | 0, _, _ => false
  | fuel + 1, environment, expression =>
    match expression with
    | .Var binder =>
      (environment.find? (fun entry => entry.1 == binder)).any
        (fun entry => knownList fuel environment entry.2)
    | .Lit (.ConstList _ _, .TypeOperator (.TypeList _)) => true
    | .App function argument =>
      match resolveHead fuel environment function with
      | .Builtin .UnListData | .Force (.Builtin .TailList) => true
      | .Force (.Force (.Builtin .SndPair)) => constructorPair fuel environment argument
      | _ => false
    | _ => false

end Moist.MIR.Advanced
