import Moist.Plutus.Term

namespace Moist.SMT

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

def and : Expr → Expr → Expr
  | .bool true, b => b
  | a, .bool true => a
  | .bool false, _ => .bool false
  | _, .bool false => .bool false
  | a, b => .app "and" [a, b]

def or : Expr → Expr → Expr
  | .bool false, b => b
  | a, .bool false => a
  | .bool true, _ => .bool true
  | _, .bool true => .bool true
  | a, b => .app "or" [a, b]
def imp (a b : Expr) : Expr := .app "=>" [a, b]
def eq (a b : Expr) : Expr :=
  if a == b then .bool true
  else
    match a, b with
    | .int _, .int _ => .bool false
    | .bool _, .bool _ => .bool false
    | .str _, .str _ => .bool false
    | _, _ => .app "=" [a, b]
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

partial def render : Expr → String
  | .sym s => s
  | .int i => if i < 0 then "(- " ++ toString i.natAbs ++ ")" else toString i
  | .bool true => "true"
  | .bool false => "false"
  | .str s => "\"" ++ escapeString s ++ "\""
  | .app f [] => f
  | .app f args => "(" ++ f ++ " " ++ String.intercalate " " (args.map render) ++ ")"
  | .ite c t e => "(ite " ++ render c ++ " " ++ render t ++ " " ++ render e ++ ")"

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
