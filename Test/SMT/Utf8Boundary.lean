import Moist.SMT.Soundness.SolverBoundary

namespace Test.SMT.Utf8Boundary

open Moist.Plutus.Term
open Moist.SMT
open Moist.SMT.UPLC

abbrev tyString : BuiltinType := .AtomicType .TypeString
abbrev tyBytes : BuiltinType := .AtomicType .TypeByteString
abbrev tyBool : BuiltinType := .AtomicType .TypeBool

def app (f x : Term) : Term := .Apply f x
def app1 (b : BuiltinFun) (x : Term) : Term := app (.Builtin b) x
def app2 (b : BuiltinFun) (x y : Term) : Term := app (app (.Builtin b) x) y
def string (s : String) : Term := .Constant (.String s, tyString)
def bytes (bs : ByteArray) : Term := .Constant (.ByteString bs, tyBytes)
def bool (b : Bool) : Term := .Constant (.Bool b, tyBool)

def encodedA : Term := app1 .EncodeUtf8 (string "a")

/-- Former Boolean false-positive: Z3 used to choose `encodeUtf8 "a" = #00`. -/
def boolCounterexample : Term :=
  app2 .EqualsByteString encodedA (bytes (ByteArray.mk #[0]))

/-- Former integer false-positive: Z3 used to choose a zero-length encoding. -/
def intCounterexample : Term := app1 .LengthOfByteString encodedA

/-- Former error false-positive: Z3 used to declare ASCII `#61` invalid. -/
def errorCounterexample : Term :=
  app1 .DecodeUtf8 (bytes (ByteArray.mk #[97]))

/-- Exercise the full Unicode scalar range, beyond Z3's native string sort. -/
def maxScalarEncoding : Term :=
  app2 .EqualsByteString
    (app1 .EncodeUtf8 (string (String.singleton (Char.ofNat 0x10FFFF))))
    (bytes (ByteArray.mk #[244, 143, 191, 191]))

def boolScript : Script := scriptForBoolTrue 20 [] boolCounterexample
def intScript : Script := scriptForIntEq 20 [] intCounterexample (.int 0)
def errorScript : Script := scriptForError 20 [] errorCounterexample
def maxScalarScript : Script := scriptForBoolTrue 20 [] maxScalarEncoding

/-- A generic `Val` case deliberately contains inactive, ill-typed selector
branches.  The internal truth semantics must mask those branches just as SMT
does, rather than turning the whole query into `none`. -/
def guardedCaseTerm : Term := .Case (.Var 1) [.Error, bool true]

def guardedDecl : SymDecl :=
  let d := symVal "guarded"
  d.withAssumptions
    [SExpr.eq (.sym d.name) (.app "VBool" [.bool true])]

def guardedQuery : SExpr :=
  okBoolTrueCond (evalSym 20 (envOf [guardedDecl]) guardedCaseTerm)

def guardedModel : Moist.SMT.Semantics.Model :=
  Moist.SMT.Semantics.Model.bind Moist.SMT.Semantics.Model.empty
    (Moist.SMT.sanitize "guarded")
    (.val (.bool true))

example : Moist.SMT.Semantics.evalBoolIs guardedModel guardedQuery true = true := by
  native_decide

def guardedScript : Script :=
  scriptForBoolTrue 20 [guardedDecl] guardedCaseTerm

/-- Exercise the production `Val` representation of strings, not just a
direct `UString` declaration.  This catches a sort drift between `VString`,
its selector, and the UTF-8 functions in the rendered prelude. -/
def symbolicValStringTerm : Term :=
  app2 .EqualsByteString
    (app1 .EncodeUtf8 (.Var 1))
    (bytes (ByteArray.mk #[97]))

def symbolicValStringDecl : SymDecl :=
  let d := symVal "symbolic_string"
  d.withAssumptions
    [SExpr.eq (.sym d.name) (.app "VString" [.str "a"])]

def symbolicValStringScript : Script :=
  scriptForBoolTrue 20 [symbolicValStringDecl] symbolicValStringTerm

private def expectZ3Prefix (name expected : String) (script : Script) : IO Unit := do
  let path : System.FilePath := s!"/tmp/moist-{name}.smt2"
  IO.FS.writeFile path script.render
  let result ← IO.Process.output { cmd := "z3", args := #[path.toString] }
  unless result.stdout.startsWith expected do
    throw <| IO.userError
      (name ++ ": expected Z3 prefix " ++ expected ++ ", got:\n" ++
        result.stdout ++ "\n" ++ result.stderr)

private def checkCekResults : IO Unit := do
  match (Moist.CEK.eval boolCounterexample).result with
  | .success (.VCon (.Bool false)) => pure ()
  | result => throw <| IO.userError s!"unexpected Boolean CEK result: {result}"
  match (Moist.CEK.eval intCounterexample).result with
  | .success (.VCon (.Integer 1)) => pure ()
  | result => throw <| IO.userError s!"unexpected integer CEK result: {result}"
  match (Moist.CEK.eval errorCounterexample).result with
  | .success (.VCon (.String "a")) => pure ()
  | result => throw <| IO.userError s!"unexpected decode CEK result: {result}"
  match (Moist.CEK.eval maxScalarEncoding).result with
  | .success (.VCon (.Bool true)) => pure ()
  | result => throw <| IO.userError s!"unexpected max-scalar CEK result: {result}"

unsafe def main : IO Unit := do
  checkCekResults
  expectZ3Prefix "utf8-bool-counterexample" "unsat" boolScript
  expectZ3Prefix "utf8-int-counterexample" "unsat" intScript
  expectZ3Prefix "utf8-error-counterexample" "unsat" errorScript
  expectZ3Prefix "utf8-max-scalar" "sat" maxScalarScript
  expectZ3Prefix "guarded-selector" "sat" guardedScript
  expectZ3Prefix "symbolic-val-string" "sat" symbolicValStringScript
  IO.println "UTF-8 and guarded-selector regressions passed"

end Test.SMT.Utf8Boundary

unsafe def main : IO Unit := Test.SMT.Utf8Boundary.main
