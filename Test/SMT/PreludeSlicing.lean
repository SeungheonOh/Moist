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

#guard prelude.length == 85
#guard corePrelude.length == 9
#guard (preludeForAssertions []).length == 9
#guard (preludeForAssertions
  [.app "bytes_valid" [.bytes (ByteArray.mk #[])]]).length == 15
#guard (preludeForAssertions [.app "uplc_div" [.int 7, .int 2]]).length == 15
#guard (preludeForAssertions
  [.app "bytes_le" [.bytes (ByteArray.mk #[]),
    .bytes (ByteArray.mk #[])]]).length == 12
#guard (preludeForAssertions [.app "vlist_length" [.app "VNil" []]]).length == 14
#guard (preludeForAssertions [.app "uplc_encodeUtf8" [.str "x"]]).length == 19
#guard (preludeForAssertions
  [.app "uplc_countSetBits" [.bytes (ByteArray.mk #[1])]]).length == 47
#guard (preludeForAssertions [.app "uplc_expModInteger" [.int 2, .int 3, .int 5]]).length == 17
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
  [ ("core", .bool true)
  , ("validation", .app "bytes_valid" [.bytes (ByteArray.mk #[0, 255])])
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
  ]

private def firstLine (text : String) : String :=
  (text.splitOn "\n").head?.getD ""

def main : IO Unit := do
  for (name, formula) in smokeFormulas do
    let path : System.FilePath := s!"/tmp/moist-prelude-{name}.smt2"
    IO.FS.writeFile path (scriptWith [] [formula]).render
    let result ← IO.Process.output { cmd := "z3", args := #[path.toString] }
    unless result.exitCode == 0 && result.stderr.isEmpty &&
        firstLine result.stdout == "sat" &&
        (result.stdout.splitOn "(error").length == 1 do
      throw <| IO.userError
        s!"{name}: demand-selected prelude failed:\n{result.stdout}{result.stderr}"
    IO.FS.removeFile path
    IO.println s!"{name}: sat without solver errors"

end Test.SMT.PreludeSlicing

unsafe def main : IO Unit := Test.SMT.PreludeSlicing.main
