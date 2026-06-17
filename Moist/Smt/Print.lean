import Moist.Smt.Semantics

/-! # SMT-LIB serialization + z3 bridge (`toSMTLIB`, `z3_sound`)

The two remaining TCB items of the "trust z3" compromise live here (§0 of the plan):

* **`toSMTLIB`** — a small, auditable serializer `SmtExpr → String`.  It declares the free
  variables, defines the four Plutus integer division/modulo operators (floored vs
  truncated, which SMT-LIB does not provide natively) as `define-fun`s built from real
  `to_int`, emits `(assert e)` and `(check-sat)`.  Its fidelity to the SMT-LIB standard for
  the fragment we emit is the printer-gap TCB item, minimized here and defended by
  differential testing (§9.2).

* **`z3_sound`** — the single accepted axiom: if z3 reports `unsat` on `toSMTLIB e`, then `e`
  is unsatisfiable in the Lean meaning (`Unsat e`, i.e. against `evalSmt`).

Everything else (compiler adequacy) is a Lean proof; this file is the boundary to the
external solver.  The `IO` helpers (`runZ3`, `checkUnsat`, `findModel`) are for actually
invoking z3 (via `nix-shell -p z3`) in demos/tests — they carry no proof weight.
-/

namespace Moist.Smt

/-! ## Serialization -/

namespace SmtExpr

private def sortName : SmtSort → String
  | .int => "Int"
  | .bool => "Bool"
  | .data => "Data"
  | .bytes => "String"   -- ByteStrings modelled as SMT strings (len/=; differential-tested)
  | .list s => s!"(Lst {sortName s})"
  | .pair a b => s!"(Pair {sortName a} {sortName b})"

/-- Render a binary operator head.  Division/modulo use the `moist_*` `define-fun`s emitted
    in the preamble (floored `fdiv`/`fmod` for `DivideInteger`/`ModInteger`, truncated
    `tdiv`/`tmod` for `QuotientInteger`/`RemainderInteger`). -/
private def binHead : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*"
  | .fdiv => "moist_fdiv" | .fmod => "moist_fmod"
  | .tdiv => "moist_tdiv" | .tmod => "moist_tmod"
  | .le => "<=" | .lt => "<" | .eq => "="
  | .and_ => "and" | .or_ => "or"

/-- Render a unary `data`/`bytes` operator on the Plutus `Data` SMT datatype (constructors
    `mkConstr/mkMap/mkDList/mkI/mkB`, selectors `cTag/iVal/bVal`, testers `(_ is …)`). -/
private def uopRender (op : UnOp) (s : String) : String :=
  match op with
  | .iData     => s!"(mkI {s})"   | .bData    => s!"(mkB {s})"
  | .unIData   => s!"(iVal {s})"  | .unBData  => s!"(bVal {s})"
  | .constrTag => s!"(cTag {s})"  | .lenBytes => s!"(str.len {s})"
  | .isI       => s!"((_ is mkI) {s})"      | .isB    => s!"((_ is mkB) {s})"
  | .isConstr  => s!"((_ is mkConstr) {s})" | .isList => s!"((_ is mkDList) {s})"
  | .isMap     => s!"((_ is mkMap) {s})"
  | .dArgs     => s!"(cArgs {s})"  | .dItems => s!"(lItems {s})" | .dEntries => s!"(mEntries {s})"
  | .sha2_256  => s!"(moist_sha2_256 {s})"   | .sha3_256 => s!"(moist_sha3_256 {s})"
  | .blake2b_256 => s!"(moist_blake2b_256 {s})" | .blake2b_224 => s!"(moist_blake2b_224 {s})"
  | .keccak_256 => s!"(moist_keccak_256 {s})" | .ripemd_160 => s!"(moist_ripemd_160 {s})"
  | .serialiseData => s!"(moist_serialiseData {s})"

/-- Render an `SmtExpr` as an SMT-LIB s-expression. -/
def sexpr : SmtExpr → String
  | .var x _ => x
  | .litI n => if n < 0 then s!"(- {-n})" else toString n
  | .litB b => if b then "true" else "false"
  | .neg e => s!"(- {sexpr e})"
  | .not e => s!"(not {sexpr e})"
  | .bin op a b => s!"({binHead op} {sexpr a} {sexpr b})"
  | .uop op e => uopRender op (sexpr e)
  | .ite c a b => s!"(ite {sexpr c} {sexpr a} {sexpr b})"
  | .mkpair a b => s!"(mkPair {sexpr a} {sexpr b})"
  | .fstP e => s!"(pFst {sexpr e})"
  | .sndP e => s!"(pSnd {sexpr e})"
  | .nilL s => s!"(as lnil (Lst {sortName s}))"   -- typed empty list
  | .consL h t => s!"(lcons {sexpr h} {sexpr t})"
  | .headL _ e => s!"(lhead {sexpr e})"
  | .tailL e => s!"(ltail {sexpr e})"
  | .nullL e => s!"((_ is lnil) {sexpr e})"
  | .verifySig .ed25519 a b c => s!"(moist_verifyEd25519 {sexpr a} {sexpr b} {sexpr c})"
  | .verifySig .ecdsaSecp256k1 a b c => s!"(moist_verifyEcdsa {sexpr a} {sexpr b} {sexpr c})"
  | .verifySig .schnorrSecp256k1 a b c => s!"(moist_verifySchnorr {sexpr a} {sexpr b} {sexpr c})"

/-- Collect the free variables (name × sort), de-duplicated, preserving first-seen order. -/
def collectVars (e : SmtExpr) : List (String × SmtSort) :=
  go e [] |>.reverse
where
  go (e : SmtExpr) (acc : List (String × SmtSort)) : List (String × SmtSort) :=
    match e with
    | .var x s => if acc.any (·.1 == x) then acc else (x, s) :: acc
    | .litI _ | .litB _ | .nilL _ => acc
    | .neg a | .not a | .uop _ a | .fstP a | .sndP a | .headL _ a | .tailL a | .nullL a => go a acc
    | .bin _ a b | .mkpair a b | .consL a b => go b (go a acc)
    | .ite a b c | .verifySig _ a b c => go c (go b (go a acc))

end SmtExpr

/-- The fixed preamble: the four Plutus division/modulo operators as `define-fun`s.
    `fdiv` is floor division `⌊x/y⌋` (= `Int.fdiv`), realized via real `to_int`; `fmod` its
    companion remainder; `tdiv` truncates toward zero (= `Int.tdiv`); `tmod` its remainder.
    These are emitted unconditionally (z3 ignores unused definitions). -/
def smtPreamble : String :=
  "(define-fun moist_fdiv ((x Int) (y Int)) Int (to_int (/ (to_real x) (to_real y))))\n" ++
  "(define-fun moist_fmod ((x Int) (y Int)) Int (- x (* y (moist_fdiv x y))))\n" ++
  "(define-fun moist_tdiv ((x Int) (y Int)) Int " ++
    "(ite (= (>= x 0) (>= y 0)) (to_int (/ (to_real (abs x)) (to_real (abs y)))) " ++
    "(- (to_int (/ (to_real (abs x)) (to_real (abs y)))))))\n" ++
  "(define-fun moist_tmod ((x Int) (y Int)) Int (- x (* y (moist_tdiv x y))))\n"

/-- The Plutus `Data` type as an SMT-LIB recursive datatype (with its `DataList`, `DataPair`,
    `DataPairList` companions).  `ByteString` fields are SMT `String`s.  Emitted unconditionally
    (z3 ignores it when unused). -/
def dataPreamble : String :=
  -- Polymorphic builtin `Pair`/`Lst`, and `Data` recursive through `(Lst Data)` and
  -- `(Lst (Pair Data Data))` (its `Constr` fields / `List` items / `Map` entries).  Declared
  -- mutually so `unConstrData`/`unListData`/`unMapData` return genuine `(Lst …)`/`(Pair …)`.
  "(declare-datatypes ((Pair 2)) ((par (A B) ((mkPair (pFst A) (pSnd B))))))\n" ++
  "(declare-datatypes ((Lst 1)) ((par (A) ((lnil) (lcons (lhead A) (ltail (Lst A)))))))\n" ++
  "(declare-datatypes ((Data 0)) (((mkConstr (cTag Int) (cArgs (Lst Data))) " ++
       "(mkMap (mEntries (Lst (Pair Data Data)))) (mkDList (lItems (Lst Data))) " ++
       "(mkI (iVal Int)) (mkB (bVal String)))))\n"

/-- Uninterpreted declarations for the **axiomatized** cryptographic builtins (hashes are
    `String → String`, ByteStrings being modelled as SMT `String`s).  z3 reasons about them
    abstractly (only `x = y → f x = f y`), which is exactly the Lean axiom's content. -/
def cryptoPreamble : String :=
  "(declare-fun moist_sha2_256 (String) String)\n" ++
  "(declare-fun moist_sha3_256 (String) String)\n" ++
  "(declare-fun moist_blake2b_256 (String) String)\n" ++
  "(declare-fun moist_blake2b_224 (String) String)\n" ++
  "(declare-fun moist_keccak_256 (String) String)\n" ++
  "(declare-fun moist_ripemd_160 (String) String)\n" ++
  "(declare-fun moist_serialiseData (Data) String)\n" ++
  "(declare-fun moist_verifyEd25519 (String String String) Bool)\n" ++
  "(declare-fun moist_verifyEcdsa (String String String) Bool)\n" ++
  "(declare-fun moist_verifySchnorr (String String String) Bool)\n"

/-- Serialize an `SmtExpr` (the formula to be checked) into a complete SMT-LIB script:
    logic, `Data` datatype + division preambles, variable declarations, the assertion, and
    `(check-sat)`.  `(assert e)`; an `unsat` verdict therefore certifies `Unsat e`. -/
def toSMTLIB (e : SmtExpr) : String :=
  let vars := SmtExpr.collectVars e
  let decls := vars.foldl
    (fun acc (x, s) => acc ++ s!"(declare-const {x} {SmtExpr.sortName s})\n") ""
  "(set-logic ALL)\n" ++ dataPreamble ++ cryptoPreamble ++ smtPreamble ++ decls ++
    s!"(assert {SmtExpr.sexpr e})\n" ++ "(check-sat)\n"

/-! ## The trusted bridge (the one accepted axiom) -/

/-- **z3 soundness (the accepted compromise).**  If z3 reports `unsat` on the SMT-LIB script
    `toSMTLIB e`, then `e` is unsatisfiable in our Lean meaning of `SmtExpr` (`evalSmt`).
    This is the *only* axiom of the verified-compiler pipeline; everything up to it is a Lean
    proof, and the printer/standard-match gap it bundles is minimized and differentially
    tested (§9.2). -/
axiom z3_sound (e : SmtExpr) : z3_says_unsat (toSMTLIB e) → Unsat e

/-! ## z3 invocation (no proof weight — for demos/tests)

Runs z3 by writing the script to a temp file and shelling out.  Expects `z3` on `PATH`
(use `nix-shell -p z3 --run …`).  Parses the first token of stdout. -/

/-- Run z3 on an SMT-LIB script, returning its raw stdout (`sat`/`unsat`/`unknown` + model). -/
def runZ3 (script : String) : IO String := do
  let (handle, path) ← IO.FS.createTempFile
  handle.putStr script
  handle.flush
  let out ← IO.Process.output { cmd := "z3", args := #["-smt2", path.toString] }
  IO.FS.removeFile path
  if out.exitCode != 0 && out.stdout.isEmpty then
    throw (IO.userError s!"z3 failed: {out.stderr}")
  pure out.stdout

/-- z3 verdict on a formula. -/
inductive Z3Result | unsat | sat (model : String) | unknown
deriving Repr, BEq

/-- Check `e` for unsatisfiability with z3.  `unsat` ⟹ (with `z3_sound`) `Unsat e`. -/
def checkZ3 (e : SmtExpr) : IO Z3Result := do
  let raw ← runZ3 (toSMTLIB e)
  let firstLine := (raw.splitOn "\n").headD ""
  if firstLine.startsWith "unsat" then pure .unsat
  else if firstLine.startsWith "sat" then pure (.sat raw)
  else pure .unknown

/-- Ask z3 for a satisfying assignment of `e` (the bug-finding / counterexample direction;
    untrusted — the model is replayed through `bigEval`).  Emits `(get-model)`. -/
def findModel (e : SmtExpr) : IO (Option String) := do
  let script := toSMTLIB e ++ "(get-model)\n"
  let raw ← runZ3 script
  if (raw.splitOn "\n").headD "" |>.startsWith "sat" then pure (some raw) else pure none

end Moist.Smt
