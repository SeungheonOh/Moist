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
  | .string => "String"
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

private def escapeString (s : String) : String :=
  let rec loop : List Char → List Char
    | [] => []
    | '"' :: cs => '"' :: '"' :: loop cs
    | c :: cs => c :: loop cs
  String.mk (loop s.data)

private def renderByte (b : UInt8) : String :=
  "(seq.unit " ++ toString b.toNat ++ ")"

private def renderBytes (bs : ByteArray) : String :=
  bs.data.foldl
    (fun acc b => "(seq.++ " ++ acc ++ " " ++ renderByte b ++ ")")
    "(as seq.empty Bytes)"

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
    | .String s => "(VString \"" ++ escapeString s ++ "\")"
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
  | .str s => "\"" ++ escapeString s ++ "\""
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
  | .getModel => "(get-model)"
  | .getValue es => "(get-value (" ++ String.intercalate " " (es.map Expr.render) ++ "))"

end Command

structure Script where
  commands : List Command
deriving Repr

namespace Script

def render (s : Script) : String :=
  String.intercalate "\n" (s.commands.map Command.render) ++ "\n"

end Script

def sanitize (s : String) : String :=
  let ok (c : Char) := c.isAlphanum || c == '_' || c == '-' || c == '.' || c == '$'
  let chars := s.data.map fun c => if ok c then c else '_'
  let out := String.mk chars
  if out.isEmpty then "x" else out

end Moist.SMT
