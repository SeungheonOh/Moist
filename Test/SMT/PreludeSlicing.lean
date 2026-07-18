import Moist.SMT.Soundness.SolverBoundary

/-!
# Demand-selected prelude regressions

These checks cover every dependency family selected by
`preludeForAssertions`.  The larger builtin differential executables cover
every production builtin; this file keeps a fast family-level Z3 smoke test
and the kernel-facing semantic/end-point audit together.
-/

namespace Test.SMT.PreludeSlicing

open Moist.SMT
open Moist.SMT.UPLC
open Moist.Plutus.Term

private abbrev tyInt : BuiltinType := .AtomicType .TypeInteger

private def xInt : SymDecl := symInt "prelude_x"

private def equalsIntegerAddExample : Term :=
  .Apply (.Apply (.Builtin .EqualsInteger)
      (.Apply (.Apply (.Builtin .AddInteger) (.Var 1))
        (.Constant (.Integer 1, tyInt))))
    (.Constant (.Integer 5, tyInt))

private def rawAtStartsWith (index : Nat) (expectedPrefix : String) : Bool :=
  match prelude[index]? with
  | some (.raw command) => command.startsWith expectedPrefix
  | _ => false

#guard prelude.length == 85
#guard corePrelude.length == 9
-- The section-boundary sentinels pin the reviewed full-prelude order.  The
-- implementation no longer uses these offsets; they are deliberately only a
-- regression tripwire for accidental command reordering.
#guard rawAtStartsWith 0 "(define-sort Bytes"
#guard rawAtStartsWith 1 "(define-sort UString"
#guard rawAtStartsWith 2 "(declare-sort G1"
#guard rawAtStartsWith 9 "(define-fun same_sign"
#guard rawAtStartsWith 11 "(define-fun-rec bytes_valid_at"
#guard rawAtStartsWith 13 "(define-fun unicode_scalar"
#guard rawAtStartsWith 16 "(define-funs-rec"
#guard rawAtStartsWith 17 "(define-fun uplc_tdiv"
#guard rawAtStartsWith 21 "(define-fun-rec bytes_lt_at"
#guard rawAtStartsWith 24 "(define-fun-rec vlist_length"
#guard rawAtStartsWith 29 "(define-fun utf8_cont"
#guard rawAtStartsWith 39 "(define-fun-rec uplc_pow_nat"
#guard rawAtStartsWith 77 "(define-fun-rec uplc_gcd"
#guard rawAtStartsWith 84 "(define-fun uplc_expModInteger"
#guard (preludeForAssertions []).length == 0
#guard (preludeForAssertions [.bool true]).length == 0
#guard (preludeForAssertions (symInt "x").assumptions).length == 0
#guard (preludeForAssertions (symBool "x").assumptions).length == 0
#guard (preludeForAssertions (symConstr "tag").assumptions).length == 0
#guard (preludeForAssertions (symBytes "x").assumptions).length == 3
#guard (preludeForAssertions (symString "x").assumptions).length == 4
#guard (preludeForAssertions (symData "x").assumptions).length == 15
#guard (preludeForAssertions (symVal "x").assumptions).length == 15
#guard (preludeForAssertions [.bytes (ByteArray.mk #[1])]).length == 1
#guard (preludeForAssertions [.str "x"]).length == 1
#guard (preludeForAssertions
  [.app "bytes_valid" [.bytes (ByteArray.mk #[])]]).length == 3
#guard (preludeForAssertions [.app "uplc_div" [.int 7, .int 2]]).length == 6
#guard (preludeForAssertions
  [.app "bytes_le" [.bytes (ByteArray.mk #[]),
    .bytes (ByteArray.mk #[])]]).length == 4
#guard (preludeForAssertions [.app "vlist_length" [.app "VNil" []]]).length == 14
#guard (preludeForAssertions [.app "uplc_encodeUtf8" [.str "x"]]).length == 12
#guard (preludeForAssertions
  [.app "uplc_countSetBits" [.bytes (ByteArray.mk #[1])]]).length == 47
#guard (preludeForAssertions
  [.app "uplc_expModInteger" [.int 2, .int 3, .int 5]]).length == 8
-- Known datatype declarations remain a core-only dependency, including the
-- tester syntax assembled dynamically by `SExpr.isCtor`.
#guard (preludeForAssertions [.app "VInt" [.int 1]]).length == 9
#guard (preludeForAssertions [SExpr.isCtor "VInt" (.app "VInt" [.int 1])]).length == 9
-- A future helper omitted from the registry must get the entire known prelude.
-- This is conservative dependency selection, not a declaration of that head;
-- the executable check below confirms Z3 still rejects a truly unknown name.
#guard (preludeForAssertions [.app "future_unregistered_helper" []]).length ==
  prelude.length
#guard (preludeForAssertions [.app "future_unregistered_helper" []]).map
    Command.render == prelude.map Command.render
-- Exhausting the bounded work-list scan is conservative: it restores the
-- complete prelude instead of risking a missing dependency.
#guard (preludeForAssertions (List.replicate 100001 (.bool true))).length ==
  prelude.length

-- A representative integer refinement query no longer carries unrelated
-- recursive theories.  The full reference remains available for a direct
-- size and solver benchmark.
#guard (scriptForBoolTrue 20 [xInt] equalsIntegerAddExample).render.length <
  (scriptWithFullPrelude [xInt]
    [okBoolTrueCond (evalSym 20 (envOf [xInt]) equalsIntegerAddExample)]).render.length

example (m : Semantics.Model) (decls : List SymDecl)
    (assertions : List SExpr) :
    (∀ expression, expression ∈ (scriptWith decls assertions).assertions →
      Semantics.evalBoolIs m expression true = true) ↔
    (∀ expression,
      expression ∈ (scriptWithFullPrelude decls assertions).assertions →
        Semantics.evalBoolIs m expression true = true) :=
  scriptWith_assertionsTrue_iff_fullPrelude m decls assertions

-- These are the unchanged certified-model-to-actual-CEK endpoints used by
-- the demand-selected production scripts.
#check Moist.SMT.UPLC.Soundness.BoolTrueQuery.sound
#check Moist.SMT.UPLC.Soundness.IntEqQuery.sound
#check Moist.SMT.UPLC.Soundness.ErrorQuery.sound

private def smokeFormulas : List (String × SExpr) :=
  [ ("coreless-bool", .bool true)
  , ("bytes-validation", .app "bytes_valid"
      [.bytes (ByteArray.mk #[0, 255])])
  , ("string-validation", .app "ustring_valid" [.str "A"])
  , ("data-validation", .app "data_valid" [.dataLit (.I 1)])
  , ("integer-division", SExpr.eq (.app "uplc_div" [.int 7, .int 2]) (.int 3))
  , ("bytes-ordering", .app "bytes_le"
      [.bytes (ByteArray.mk #[1]), .bytes (ByteArray.mk #[1, 2])])
  , ("list", SExpr.eq (.app "vlist_length" [.app "VNil" []]) (.int 0))
  , ("utf8", SExpr.eq (.app "uplc_encodeUtf8" [.str "A"])
      (.bytes (ByteArray.mk #[65])))
  , ("advanced-bytes",
      SExpr.eq (.app "uplc_countSetBits" [.bytes (ByteArray.mk #[0x0f])])
        (.int 4))
  , ("exp-mod",
      SExpr.eq (.app "uplc_expModInteger" [.int 2, .int 10, .int 17]) (.int 4))
  , ("known-core-symbol",
      SExpr.eq (.app "VInt" [.int 1]) (.app "VInt" [.int 1]))
  ]

private def firstLine (text : String) : String :=
  (text.splitOn "\n").head?.getD ""

private def hasSolverError (result : IO.Process.Output) : Bool :=
  !result.stderr.isEmpty || (result.stdout.splitOn "(error").length != 1

private def acceptedSat (result : IO.Process.Output) : Bool :=
  result.exitCode == 0 && !hasSolverError result && firstLine result.stdout == "sat"

def main : IO Unit := do
  for (name, formula) in smokeFormulas do
    let path : System.FilePath := s!"/tmp/moist-prelude-{name}.smt2"
    IO.FS.writeFile path (scriptWith [] [formula]).render
    let result ← IO.Process.output { cmd := "z3", args := #[path.toString] }
    unless acceptedSat result do
      throw <| IO.userError
        s!"{name}: demand-selected prelude failed:\n{result.stdout}{result.stderr}"
    IO.FS.removeFile path
    IO.println s!"{name}: sat without solver errors"

  let unknownPath : System.FilePath := "/tmp/moist-prelude-unknown-helper.smt2"
  let unknownFormula : SExpr := .app "future_unregistered_helper" []
  IO.FS.writeFile unknownPath (scriptWith [] [unknownFormula]).render
  let unknownResult ←
    IO.Process.output { cmd := "z3", args := #[unknownPath.toString] }
  IO.FS.removeFile unknownPath
  unless hasSolverError unknownResult && !acceptedSat unknownResult do
    throw <| IO.userError <|
      "unknown helper was not rejected as a solver error:\n" ++
        unknownResult.stdout ++ unknownResult.stderr
  IO.println "unknown helper: conservatively selected full prelude and Z3 rejected the head"

end Test.SMT.PreludeSlicing

unsafe def main : IO Unit := Test.SMT.PreludeSlicing.main
