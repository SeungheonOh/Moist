import Test.MIR.Opt.Soundness

namespace Test.MIR.Opt.Differential

open Moist.MIR
open Test.MIR
open Test.Framework

private def choose (limit : Nat) : StateM Nat Nat := do
  let seed ← get
  let next := (seed * 1664525 + 1013904223) % 4294967296
  set next
  return (next / 65536) % limit

private def identifier : StateM Nat VarId := do
  let uid ← choose 16
  let origin := if (← choose 2) == 0 then VarOrigin.source else .gen
  return { uid, origin, hint := "generated" }

def generate : Nat → List VarId → StateM Nat Expr
  | 0, environment => do
    match ← choose 4 with
    | 0 => return .Error
    | 1 => return boolLit ((← choose 2) == 0)
    | 2 =>
      if environment.isEmpty then return intLit 0
      else return .Var (environment[(← choose environment.length)]!)
    | _ => return intLit (Int.ofNat (← choose 11) - 5)
  | depth + 1, environment => do
    match ← choose 13 with
    | 0 => generate 0 environment
    | 1 =>
      let binder ← identifier
      return .Lam binder (← generate depth (binder :: environment))
    | 2 => return .Delay (← generate depth environment)
    | 3 => return .Force (← generate depth environment)
    | 4 =>
      let binder ← identifier
      let rhs ← generate depth environment
      return .Let [(binder, rhs, false)] (← generate depth (binder :: environment))
    | 5 =>
      let tag ← choose 3
      let count ← choose 3
      let fields ← (List.range count).mapM (fun _ => generate depth environment)
      return .Constr tag fields
    | 6 =>
      let scrutinee ← generate depth environment
      let first ← generate depth environment
      let second ← generate depth environment
      return .Case scrutinee [first, second]
    | 7 =>
      let builtin := match ← choose 3 with
        | 0 => Moist.Plutus.Term.BuiltinFun.AddInteger
        | 1 => .SubtractInteger
        | _ => .DivideInteger
      return .App (.App (.Builtin builtin) (← generate depth environment))
        (← generate depth environment)
    | 8 =>
      let binder ← identifier
      let body ← generate depth (binder :: environment)
      return .App (.Lam binder body) (← generate depth environment)
    | 9 =>
      let message := s!"trace-{← choose 3}"
      return .App (.App (.Force (.Builtin .Trace))
        (.Lit (.String message, .AtomicType .TypeString))) (← generate depth environment)
    | 10 => return .App (intLit 1) (← generate depth environment)
    | 11 => return .Force (.Delay (← generate depth environment))
    | _ =>
      let builtin := if (← choose 2) == 0 then Moist.Plutus.Term.BuiltinFun.AddInteger else .HeadList
      return .Force (.Builtin builtin)

def contexts (expression : Expr) : List Expr :=
  let discard := fun result => Expr.App (.Lam (sourceVar 2000000) (intLit 17)) result
  let addOne := fun result => Expr.App (.App (.Builtin .AddInteger) result) (intLit 1)
  [discard expression,
   addOne expression,
   discard (.Force expression),
   discard (.App expression (intLit 1)),
   addOne (.App expression (intLit 1)),
   .Case expression [intLit 11, intLit 22, intLit 33]]

def tests : TestTree := suite "differential" do
  test "deterministic_closed_terms" do
    for seed in List.range 256 do
      let expression := (generate (3 + seed % 2) [] |>.run (seed + 1729)).1
      for (context, index) in (contexts expression).zipIdx do
        Soundness.preservesAll s!"seed={seed}, context={index}" context
    IO.println "18,432 differential pass/context comparisons passed (256 deterministic seeds)."

end Test.MIR.Opt.Differential
