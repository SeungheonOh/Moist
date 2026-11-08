import Test.MIR.FuzzReal.Gen

/-! # Probes of the machine semantics the optimizer relies on

Closed programs exercising `case` on builtin values (integers, Booleans,
unit, lists, pairs, Data), constructor cases with mismatched arities, list
and pair builtins on values of the wrong element type, and partial and over-
saturated builtin applications. They run like generated programs: every
optimizer variant against the unoptimized lowering on the real machine, and
the Lean model against the real machine. -/

namespace Test.MIR.FuzzReal.Probes

open Moist.MIR
open Moist.Plutus (Data)
open Moist.Plutus.Term
open Test.MIR.FuzzReal

private def v (n : Nat) : VarId := { uid := 90000 + n, origin := .source, hint := "q" }

def intListT : BuiltinType := .TypeOperator (.TypeList (.AtomicType .TypeInteger))
def boolListT : BuiltinType := .TypeOperator (.TypeList (.AtomicType .TypeBool))
def pairT : BuiltinType := .TypeOperator (.TypePair (.AtomicType .TypeData) (.AtomicType .TypeData))
def pairIntBoolT : BuiltinType :=
  .TypeOperator (.TypePair (.AtomicType .TypeInteger) (.AtomicType .TypeBool))

def intList (xs : List Int) : Expr := lit (.ConstList (xs.map .Integer)) intListT
def results (n : Nat) : List Expr := (List.range n).map fun k => intE (Int.ofNat (10 + k))

/-- An alternative taking `arity` arguments and returning them in a constructor. -/
def taking (arity : Nat) (tag : Nat) : Expr :=
  let names := (List.range arity).map fun k => v (tag * 10 + k)
  names.foldr .Lam (.Constr tag (names.map .Var))

def scrutinees : List (String × Expr) :=
  [("int-1", intE (-1)), ("int0", intE 0), ("int1", intE 1), ("int2", intE 2), ("int3", intE 3),
   ("false", boolE false), ("true", boolE true), ("unit", unitE),
   ("nil", intList []), ("list1", intList [7]), ("list2", intList [7, 8]),
   ("datalist-nil", dataListE []), ("datalist1", dataListE [.I 5]),
   ("pairdata", lit (.PairData (.I 1, .B ⟨#[2]⟩)) pairT),
   ("pair-int-bool", lit (.Pair (.Integer 1, .Bool true)) pairIntBoolT),
   ("data", dataE (.Constr 0 [])), ("bytes", bytesE ⟨#[1]⟩),
   ("constr0-0", .Constr 0 []), ("constr1-0", .Constr 1 []), ("constr0-2", .Constr 0 [intE 1, intE 2]),
   ("constr2-1", .Constr 2 [intE 1])]

def alternativeSets : List (String × List Expr) :=
  [("none", []), ("plain1", results 1), ("plain2", results 2), ("plain3", results 3),
   ("lam1", [taking 1 0]), ("lam2", [taking 2 0]), ("lam2-plain", [taking 2 0, intE 99]),
   ("plain-lam2", [intE 99, taking 2 1]), ("lam1-lam1", [taking 1 0, taking 1 1]),
   ("lam0-lam2-lam1", [taking 0 0, taking 2 1, taking 1 2])]

def caseProbes : List (String × Expr) :=
  scrutinees.flatMap fun (sName, s) =>
    alternativeSets.map fun (aName, alts) => (s!"case/{sName}/{aName}", Expr.Case s alts)

def builtinProbes : List (String × Expr) :=
  [("mkcons/int-on-intlist", consE (intE 1) (intList [2])),
   ("mkcons/int-on-intnil", consE (intE 1) (intList [])),
   ("mkcons/bool-on-intlist", consE (boolE true) (intList [2])),
   ("mkcons/bool-on-intnil", consE (boolE true) (intList [])),
   ("mkcons/data-on-intnil", consE (dataE (.I 1)) (intList [])),
   ("mkcons/int-on-datanil", consE (intE 1) (dataListE [])),
   ("mkcons/data-on-datanil", consE (dataE (.I 1)) (dataListE [])),
   ("mkcons/pair-on-pairnil", consE (lit (.PairData (.I 1, .I 2)) pairT)
      (lit (.ConstPairDataList []) (.TypeOperator (.TypeList pairT)))),
   ("mkcons/data-on-pairnil", consE (dataE (.I 1))
      (lit (.ConstPairDataList []) (.TypeOperator (.TypeList pairT)))),
   ("mkcons/int-on-boolnil", consE (intE 1) (lit (.ConstList []) boolListT)),
   ("head/intnil", headE (intList [])), ("tail/intnil", tailE (intList [])),
   ("null/int", nullE (intE 0)), ("head/data", headE (dataE (.List [.I 1]))),
   ("fst/pair-int-bool", fstE (lit (.Pair (.Integer 1, .Bool true)) pairIntBoolT)),
   ("snd/pair-int-bool", sndE (lit (.Pair (.Integer 1, .Bool true)) pairIntBoolT)),
   ("equalsData/list", app2 .EqualsData (dataE (.I 1)) (dataListE [])),
   ("listData/intlist", app1 .ListData (intList [1])),
   ("mapData/datalist", app1 .MapData (dataListE [.I 1])),
   ("unconstr/I", app1 .UnConstrData (dataE (.I 1))),
   ("chooseList/int", .Force (apps (.Force (.Force (.Builtin .ChooseList))) [intE 1, .Delay (intE 1), .Delay (intE 2)])),
   ("ifThenElse/int", apps (.Force (.Builtin .IfThenElse)) [intE 1, intE 1, intE 2]),
   ("ifThenElse/unforced", apps (.Builtin .IfThenElse) [boolE true, intE 1, intE 2]),
   ("add/forced", .Force (.Builtin .AddInteger)),
   ("add/over", apps (.Builtin .AddInteger) [intE 1, intE 2, intE 3]),
   ("add/partial-forced", .Force (.App (.Builtin .AddInteger) (intE 1))),
   ("trace/over", apps (.Force (.Builtin .Trace)) [stringE "m", .Lam (v 1) (.Var (v 1)), intE 5]),
   ("headList/twice-forced", .App (.Force (.Force (.Builtin .HeadList))) (intList [1])),
   ("fstPair/once-forced", .App (.Force (.Builtin .FstPair)) (lit (.PairData (.I 1, .I 2)) pairT)),
   ("apply/constant", .App (intE 1) (intE 2)), ("force/constant", .Force (intE 1)),
   ("force/lam", .Force (.Lam (v 2) (intE 1))), ("apply/delay", .App (.Delay (intE 1)) (intE 2)),
   ("apply/constr", .App (.Constr 0 []) (intE 1)), ("force/constr", .Force (.Constr 0 [])),
   ("divide/zero", app2 .DivideInteger (intE 1) (intE 0)),
   ("constr/error-field-unused", .Case (.Constr 1 [.Error]) [intE 1, intE 2]),
   ("let/unused-error", .Let [(v 3, .Error, false)] (intE 1)),
   ("let/unused-delay-error", .Let [(v 4, .Delay .Error, false)] (intE 1))]

def all : List (String × Expr) := caseProbes ++ builtinProbes

end Test.MIR.FuzzReal.Probes
