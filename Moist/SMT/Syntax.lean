import Moist.Plutus.Term

namespace Moist.SMT

open Moist.Plutus (Data)
open Moist.Plutus.Term (Const)

/-!
# Portable SMT compiler syntax

This module is the dependency-minimal, executable surface shared by the
symbolic compiler, the renderers, and the proof model.  It deliberately
contains no renderer, simulated solver semantics, or soundness theorem.
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

/-- Convenience constructors for the unrestricted SMT AST.  The UPLC
compiler does not emit `=>`, native `div`, or native `mod`; checked production
queries reject unmodeled or partial uses at their fragment boundary. -/
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

end Expr

inductive Command where
  /-- Verbatim SMT-LIB, reserved by the production compiler for its fixed
  reviewed prelude.  Callers constructing raw scripts are outside the checked
  renderer/model boundary. -/
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
