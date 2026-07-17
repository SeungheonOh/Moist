import Moist.Plutus.Term

namespace Moist.SMT

open Moist.Plutus (Data)
open Moist.Plutus.Term (Const)

/-! # Small SMTLib surface

This is intentionally tiny and first-order.  The UPLC symbolic compiler builds
terms in this datatype, then renders them to SMTLib2 for Z3.  Keeping this layer
simple is deliberate: later soundness only has to give a denotation for this
small expression language plus a fixed SMT prelude.
-/

inductive SSort where
  | bool
  | int
  | string
  | bytes
  | data
  | dataList
  | dataPairList
  | val
  | valList
  | g1
  | g2
  | ml
  | custom : String → SSort
deriving Repr, BEq

namespace SSort

def render : SSort → String
  | .bool => "Bool"
  | .int => "Int"
  | .string => "UString"
  | .bytes => "Bytes"
  | .data => "Data"
  | .dataList => "DataList"
  | .dataPairList => "DataPairList"
  | .val => "Val"
  | .valList => "ValList"
  | .g1 => "G1"
  | .g2 => "G2"
  | .ml => "MlResult"
  | .custom s => s

end SSort

inductive Expr where
  | sym : String → Expr
  | int : Int → Expr
  | bytes : ByteArray → Expr
  | dataLit : Data → Expr
  | dataListLit : List Data → Expr
  | dataPairListLit : List (Data × Data) → Expr
  | constListLit : List Const → Expr
  | bool : Bool → Expr
  | str : String → Expr
  | app : String → List Expr → Expr
  | ite : Expr → Expr → Expr → Expr
deriving Repr, BEq

namespace Expr

def trueE : Expr := .bool true
def falseE : Expr := .bool false

def not : Expr → Expr
  | .bool true => .bool false
  | .bool false => .bool true
  | a => .app "not" [a]

def andRight (a : Expr) : Expr → Expr
  | .bool false => falseE
  | .bool true => a
  | b => .app "and" [a, b]

def and : Expr → Expr → Expr
  | .bool false, _ => falseE
  | .bool true, b => b
  | a, b => andRight a b

def orRight (a : Expr) : Expr → Expr
  | .bool true => trueE
  | .bool false => a
  | b => .app "or" [a, b]

def or : Expr → Expr → Expr
  | .bool true, _ => trueE
  | .bool false, b => b
  | a, b => orRight a b
def imp (a b : Expr) : Expr := .app "=>" [a, b]
def eq (a b : Expr) : Expr := .app "=" [a, b]
def ne (a b : Expr) : Expr := not (eq a b)
def add (a b : Expr) : Expr := .app "+" [a, b]
def sub (a b : Expr) : Expr := .app "-" [a, b]
def mul (a b : Expr) : Expr := .app "*" [a, b]
def div (a b : Expr) : Expr := .app "div" [a, b]
def mod (a b : Expr) : Expr := .app "mod" [a, b]
def lt (a b : Expr) : Expr := .app "<" [a, b]
def le (a b : Expr) : Expr := .app "<=" [a, b]
def gt (a b : Expr) : Expr := .app ">" [a, b]
def ge (a b : Expr) : Expr := .app ">=" [a, b]

def all : List Expr → Expr
  | [] => trueE
  | [x] => x
  | x :: xs => xs.foldl and x

def any : List Expr → Expr
  | [] => falseE
  | [x] => x
  | x :: xs => xs.foldl or x

private def renderByte (b : UInt8) : String :=
  "(seq.unit " ++ toString b.toNat ++ ")"

private def renderBytes (bs : ByteArray) : String :=
  bs.data.foldl
    (fun acc b => "(seq.++ " ++ acc ++ " " ++ renderByte b ++ ")")
    "(as seq.empty Bytes)"

/--
Render strings as sequences of Unicode scalar values instead of SMT-LIB's
built-in `String` sort.  Z3's native string sort is intentionally restricted
to a smaller code-point range than Lean/UPLC strings, so using it would make
the compiler silently incomplete for otherwise valid constants.  `Char`
guarantees that every emitted element is a Unicode scalar value.
-/
private def renderString (s : String) : String :=
  s.data.foldl
    (fun acc c => "(seq.++ " ++ acc ++ " (seq.unit " ++ toString c.toNat ++ "))")
    "(as seq.empty UString)"

private def renderInt (i : Int) : String :=
  if i < 0 then "(- " ++ toString i.natAbs ++ ")" else toString i

mutual
  private def renderData : Data → String
    | .Constr tag fields => "(DConstr " ++ renderInt tag ++ " " ++ renderDataList fields ++ ")"
    | .Map ps => "(DMap " ++ renderDataPairList ps ++ ")"
    | .List xs => "(DList " ++ renderDataList xs ++ ")"
    | .I i => "(DI " ++ renderInt i ++ ")"
    | .B bs => "(DB " ++ renderBytes bs ++ ")"

  private def renderDataList : List Data → String
    | [] => "DNil"
    | x :: xs => "(DCons " ++ renderData x ++ " " ++ renderDataList xs ++ ")"

  private def renderDataPairList : List (Data × Data) → String
    | [] => "DPNil"
    | (k, v) :: xs => "(DPCons " ++ renderData k ++ " " ++ renderData v ++ " " ++ renderDataPairList xs ++ ")"

  private def renderConstVal : Const → String
    | .Integer i => "(VInt " ++ renderInt i ++ ")"
    | .ByteString bs => "(VBytes " ++ renderBytes bs ++ ")"
    | .String s => "(VString " ++ renderString s ++ ")"
    | .Unit => "VUnit"
    | .Bool b => "(VBool " ++ (if b then "true)" else "false)")
    | .ConstList xs => "(VList " ++ renderConstValList xs ++ ")"
    | .ConstDataList xs => "(VDataList " ++ renderDataList xs ++ ")"
    | .ConstPairDataList xs => "(VPairDataList " ++ renderDataPairList xs ++ ")"
    | .Pair (a, b) => "(VPair " ++ renderConstVal a ++ " " ++ renderConstVal b ++ ")"
    | .PairData (a, b) => "(VPairData " ++ renderData a ++ " " ++ renderData b ++ ")"
    | .Data d => "(VData " ++ renderData d ++ ")"
    | .ConstArray xs => "(VArray " ++ renderConstValList xs ++ ")"
    | .Bls12_381_G1_element => "(VG1 g1_default)"
    | .Bls12_381_G2_element => "(VG2 g2_default)"
    | .Bls12_381_MlResult => "(VMlResult ml_default)"

  private def renderConstValList : List Const → String
    | [] => "VNil"
    | x :: xs => "(VCons " ++ renderConstVal x ++ " " ++ renderConstValList xs ++ ")"
end

mutual
def render : Expr → String
  | .sym s => s
  | .int i => renderInt i
  | .bytes bs => renderBytes bs
  | .dataLit d => renderData d
  | .dataListLit xs => renderDataList xs
  | .dataPairListLit xs => renderDataPairList xs
  | .constListLit xs => renderConstValList xs
  | .bool true => "true"
  | .bool false => "false"
  | .str s => renderString s
  | .app f [] => f
  | .app f args => "(" ++ f ++ " " ++ renderArgs args ++ ")"
  | .ite c t e => "(ite " ++ render c ++ " " ++ render t ++ " " ++ render e ++ ")"

def renderArgs : List Expr → String
  | [] => ""
  | x :: xs => render x ++ renderArgsTail xs

def renderArgsTail : List Expr → String
  | [] => ""
  | x :: xs => " " ++ render x ++ renderArgsTail xs
end

end Expr

inductive Command where
  | raw : String → Command
  | comment : String → Command
  | setLogic : String → Command
  | declareConst : String → SSort → Command
  | declareFun : String → List SSort → SSort → Command
  | defineFun : String → List (String × SSort) → SSort → Expr → Command
  | assert : Expr → Command
  | checkSat : Command
  | checkSatUsing : String → Command
  | getModel : Command
  | getValue : List Expr → Command
deriving Repr

namespace Command

def renderBinder (b : String × SSort) : String :=
  "(" ++ b.1 ++ " " ++ b.2.render ++ ")"

def render : Command → String
  | .raw s => s
  | .comment s => "; " ++ s
  | .setLogic s => "(set-logic " ++ s ++ ")"
  | .declareConst n s => "(declare-const " ++ n ++ " " ++ s.render ++ ")"
  | .declareFun n args ret =>
      "(declare-fun " ++ n ++ " (" ++ String.intercalate " " (args.map SSort.render) ++ ") " ++ ret.render ++ ")"
  | .defineFun n args ret body =>
      "(define-fun " ++ n ++ " (" ++ String.intercalate " " (args.map renderBinder) ++ ") " ++
        ret.render ++ " " ++ body.render ++ ")"
  | .assert e => "(assert " ++ e.render ++ ")"
  | .checkSat => "(check-sat)"
  | .checkSatUsing tactic => "(check-sat-using " ++ tactic ++ ")"
  | .getModel => "(get-model)"
  | .getValue es => "(get-value (" ++ String.intercalate " " (es.map Expr.render) ++ "))"

/-- Extract the formula contributed by an assertion command. -/
def assertion? : Command → Option Expr
  | .assert e => some e
  | _ => none

end Command

structure Script where
  commands : List Command
deriving Repr

namespace Script

/-- The logical assertions in a script, independent of solver-control and
model-query commands. -/
def assertions (s : Script) : List Expr :=
  s.commands.filterMap Command.assertion?

def render (s : Script) : String :=
  String.intercalate "\n" (s.commands.map Command.render) ++ "\n"

end Script

/--
Encode an external name as an SMT-LIB simple symbol.

This is deliberately an encoding rather than replacement-by-underscore:
replacement aliases distinct input names, leading digits are not valid simple
symbols, and names such as `true`/`false` can shadow SMT Boolean literals in
Z3.  A fixed `$u$` namespace followed by decimal Unicode scalar values is
injective at the character-list level and contains only simple-symbol
characters.
-/
def sanitize (s : String) : String :=
  "$u$" ++ String.intercalate "_" (s.data.map fun c => toString c.toNat)

end Moist.SMT
