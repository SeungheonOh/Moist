import Moist.Symbolic.Compile
import Moist.Verified.BigStep
import Moist.CEK.DecidableEq

/-! # Soundness of the UPLC → SMT compiler (Stage 2)

We prove the compiler **adequate** against the big-step evaluator `bigEval`
(itself proven ≡ CEK in both directions, axiom-clean, in `BigStep.lean`). The two
results the design promises, both phrased on the CEK via `bigEval_iff_halt`:

* **success ⇒ CEK halts** — if the compiled formula says the term completes
  without error and yields value `v` (under an SMT model `M`), then the CEK halts
  at the concretization of `v`  (`symbolic_success_sound`);
* **error ⇒ CEK fails** — if the compiled formula says the term *definitely*
  errors (error condition true, indeterminate condition false), then the CEK
  never halts with a value  (`symbolic_error_sound`).

## Architecture (everything below is PROVED — `sorry`-free, axiom-clean)

`denote M : SExpr → SVal` is the Lean-level meaning of an SMT expression under a
model `M` — the ground truth the *external* z3 trust boundary refers to (z3 ⊨ φ
iff `denote`-validity, which we do not re-axiomatize: `denote` interprets each SMT
operator as the corresponding Lean operation, so the modelled builtins are
*theorems*, not axioms). `γ M : SymV → Option CekValue` concretizes a symbolic
value. The core is the model-indexed simulation `Sim` (proved as the mutual
`simEval`/`simApply`/`simForce`) between `symEval` and `bigEval` at equal fuel;
`Stab` (proved as `stabEval`/`stabApply`/`stabForce`) is the determinacy /
upward fuel-stability of a determinate result. `Sim_holds`/`Stab_holds` package
them, and `symbolic_success_sound`/`symbolic_error_sound` are the two CEK theorems
— now **unconditional** (`#print axioms` = `propext`/`Quot.sound`/`Classical.choice`).

## Scope (the proven fragment)

The proven fragment is the higher-order core **plus the symbolic builtins**:
λ-calculus (`Var`/`Lam`/`Apply`), `Force`/`Delay`, simple constants
(`Integer`/`Bool`/`Unit`/`String`), `Error`, and the builtins in `preciseBuiltin`:
- **Integer** arithmetic/comparison `Add`/`Subtract`/`Multiply`/`Equals`/`LessThan`/
  `LessThanEquals` and the division family `Divide`/`Mod`/`Quotient`/`Remainder`
  (one-line `satBin`/`satBinDiv`);
- **String** `EqualsString`/`AppendString` (`satBinStr`);
- **ByteString** `EqualsByteString`/`AppendByteString` (`satBinBS`),
  `LengthOfByteString` (`satUnBS`), `IndexByteString` (`satIndexBS`, with a two-sided
  bounds guard) — via the `ByteArray ↔ List Int` bridge `baToBytes`/`bytesToBA`.
The partial-application/saturation machinery (`VBuiltin` accumulation) and the
reconciliation `satBuiltin` are all general. It proves the genuinely hard parts:
higher-order closures + environments, full **partiality** (apply-non-function,
force-non-delay, unbound-variable, *and builtin type-errors / division-by-zero /
index-out-of-bounds* all fail, both directions), and symbolic
arithmetic/equality/comparison/bytestring computation.

`ConsByteString` is the one ByteString builtin deliberately *excluded*: its
symbolic value `VBS (seq.++ (seq.unit n) bs)` carries the un-truncated integer `n`
in the byte sequence, so it is folding-clean only when `0 ≤ n ≤ 255` (= the
non-error condition); since `WfV` is maintained unconditionally, proving it would
need an *error-conditional* well-sortedness invariant (see `preciseBuiltin`).

**Model well-sortedness (`WfFO`).** The folding projectors (`V.sAsInt`/`V.sIsCon`)
strip a `V`-wrapper, exposing its inner expression; under an *arbitrary* model that
inner could denote to the wrong sort, which would make `equalsInteger` genuinely
unsound. We therefore carry `WfV`/`WfFO` (folding-clean) through the simulation:
established robustly for literal/builtin-result values, and for symbolic input
atoms exactly when the model assigns them their declared sort — which is precisely
what z3 guarantees. (The two `evalBuiltin_*_spec` axioms are the only non-standard
axioms; they are the trusted per-builtin input→output tables, true by `rfl` but
axiomatised because `evalBuiltin` whnf-times-out — the established BigStep pattern.)

The remaining builtins extend this same scaffold: `Data`/list/pair structural
builtins; and `ifThenElse`/`chooseX` + `Case`/`Constr` (needs the symbolic-branching
`choice` determinacy machinery). Opaque crypto/BLS stay out (the Moist CEK errors on
them).
-/

namespace Moist.Verified.SymbolicSoundness

open Moist.Symbolic
open Moist.Plutus.Term (Term Const BuiltinType BuiltinFun)
open Moist.Plutus (Data ByteString)
open Moist.CEK (CekValue CekEnv evalBuiltin expectedArgs)
open Moist.Verified.BigStep (bigEval bigEvalList applyVal applyValList forceVal
  evalBuiltin_AddInteger_spec evalBuiltin_SubtractInteger_spec evalBuiltin_MultiplyInteger_spec
  evalBuiltin_EqualsInteger_spec evalBuiltin_LessThanInteger_spec evalBuiltin_LessThanEqualsInteger_spec
  evalBuiltin_DivideInteger_spec evalBuiltin_ModInteger_spec
  evalBuiltin_QuotientInteger_spec evalBuiltin_RemainderInteger_spec
  evalBuiltin_EqualsString_spec evalBuiltin_AppendString_spec
  evalBuiltin_EqualsByteString_spec evalBuiltin_AppendByteString_spec
  evalBuiltin_LengthOfByteString_spec evalBuiltin_ConsByteString_spec
  evalBuiltin_IndexByteString_spec)
open Moist.Verified.Equivalence (Reaches steps)
open Moist.Verified.SmallStep (init)

/-! ## The semantic domain `SVal` and the model -/

/-- The Lean meaning of an SMT expression: one variant per emitted sort. -/
inductive SVal where
  | I    : Int → SVal                       -- Int
  | B    : Bool → SVal                      -- Bool
  | Str  : String → SVal                    -- String
  | Bytes: List Int → SVal                  -- (Seq Int)
  | Vv   : CekValue → SVal                  -- V  (a first-order CekValue: VCon/VConstr)
  | Dd   : Data → SVal                      -- D
  | DLl  : List Data → SVal                 -- DL
  | DMm  : List (Data × Data) → SVal        -- DM
  | VLl  : List CekValue → SVal             -- VL
  | bad                                     -- ill-sorted / out-of-(faithful)-scope
deriving Inhabited

namespace SVal
def asI : SVal → Int                  | .I n => n      | _ => 0
def asB : SVal → Bool                 | .B b => b      | _ => false
def asStr : SVal → String             | .Str s => s    | _ => ""
def asBytes : SVal → List Int         | .Bytes l => l  | _ => []
def asV : SVal → CekValue             | .Vv v => v     | _ => .VCon .Unit
def asD : SVal → Data                 | .Dd d => d     | _ => default
def asDL : SVal → List Data           | .DLl l => l    | _ => []
def asDM : SVal → List (Data × Data)  | .DMm l => l    | _ => []
def asVL : SVal → List CekValue       | .VLl l => l    | _ => []
end SVal

/-- An SMT model: interpretations of the declared symbolic constants and the
opaque uninterpreted functions. -/
structure Model where
  const : String → SVal
  uf    : String → List SVal → SVal

/-! ## ByteString ↔ `(Seq Int)` bridge -/

/-- Bytes (as a `List Int`) → `ByteArray`. -/
def bytesToBA (l : List Int) : ByteArray := ⟨(l.map (fun i => i.toNat.toUInt8)).toArray⟩
/-- `ByteArray` → bytes. -/
def baToBytes (ba : ByteArray) : List Int := ba.data.toList.map (fun b => Int.ofNat b.toNat)

/-! ### `ByteArray ↔ List Int` bridge (for the ByteString builtins)

`ByteArray`'s `append`/`get!` are `copySlice`/`Array`-based with sparse core lemmas,
so these are proved by unfolding to `Array` operations. -/

theorem bytesToBA_baToBytes (bs : ByteArray) : bytesToBA (baToBytes bs) = bs := by
  simp [bytesToBA, baToBytes, List.map_map, Function.comp_def]

theorem baToBytes_length (bs : ByteArray) : (baToBytes bs).length = bs.size := by
  simp [baToBytes, ByteArray.size]

/-- `ByteString` equality (`x.data == y.data`) bridges to `List Int` equality. -/
theorem baToBytes_beq (bs1 bs2 : ByteArray) : (baToBytes bs1 == baToBytes bs2) = (bs1 == bs2) := by
  have hl : (baToBytes bs1 == baToBytes bs2) = decide (bs1 = bs2) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by have := congrArg bytesToBA h; rwa [bytesToBA_baToBytes, bytesToBA_baToBytes] at this,
           fun h => by rw [h]⟩
  have hr : (bs1 == bs2) = decide (bs1 = bs2) := by
    show (bs1.data == bs2.data) = decide (bs1 = bs2)
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by cases bs1; cases bs2; simp_all, fun h => by rw [h]⟩
  rw [hl, hr]

theorem ba_append_data (a b : ByteArray) : (a ++ b).data = a.data ++ b.data := by
  show (ByteArray.append a b).data = _
  unfold ByteArray.append ByteArray.copySlice
  simp only [ByteArray.size, Nat.zero_add, Nat.sub_zero, Nat.min_self]
  rw [Array.extract_size, Array.extract_size]
  have he : a.data.extract (a.data.size + b.data.size) a.data.size = #[] := by
    apply Array.eq_empty_of_size_eq_zero; rw [Array.size_extract]; omega
  rw [he]; simp

theorem baToBytes_append (bs1 bs2 : ByteArray) :
    baToBytes (bs1 ++ bs2) = baToBytes bs1 ++ baToBytes bs2 := by
  simp only [baToBytes, ba_append_data, Array.toList_append, List.map_append]

theorem bytesToBA_append (bs1 bs2 : ByteArray) :
    bytesToBA (baToBytes bs1 ++ baToBytes bs2) = bs1 ++ bs2 := by
  rw [← baToBytes_append, bytesToBA_baToBytes]

theorem idx_bridge (bs : ByteArray) (k : Nat) (h : k < bs.size) :
    (((baToBytes bs)[k]?).getD 0) = Int.ofNat (bs.get! k).toNat := by
  have hk : k < bs.data.size := by simpa [ByteArray.size] using h
  simp only [baToBytes, List.getElem?_map, List.getElem?_eq_getElem (by simpa using hk),
    Option.map_some, Option.getD_some, Array.getElem_toList]
  simp [ByteArray.get!, getElem!_pos bs.data k hk]

theorem cons_bridge (n : Int) (bs : ByteArray) :
    bytesToBA (n :: baToBytes bs) = ByteArray.mk #[n.toNat.toUInt8] ++ bs := by
  apply ByteArray.ext
  rw [ba_append_data]
  have hid : (fun (b : UInt8) => (Int.ofNat b.toNat).toNat.toUInt8) = id := by funext b; simp
  simp only [bytesToBA, baToBytes, List.map_cons, List.map_map, Function.comp_def, hid, List.map_id]
  rw [List.toArray_cons, Array.toArray_toList]

/-! ## Structural equality on `SVal` (for SMT `=`) -/

private def beqCek (a b : CekValue) : Bool := decide (a = b)

def svalEq : SVal → SVal → Bool
  | .I a, .I b       => a == b
  | .B a, .B b       => a == b
  | .Str a, .Str b   => a == b
  | .Bytes a, .Bytes b => a == b
  | .Vv a, .Vv b     => beqCek a b
  | .Dd a, .Dd b     => a == b
  | .DLl a, .DLl b   => a == b
  | .DMm a, .DMm b   => a == b
  | .VLl a, .VLl b   => decide (a = b)
  | _, _ => false

/-! ## Denotation of SMT expressions

`denote M e` interprets `e` under model `M`. Every SMT operator maps to its Lean
counterpart (this is what makes the precise builtins provable rather than
axiomatic). Heads outside the faithful fragment (crypto/BLS UFs) map to `bad`. -/

open SVal (asI asB asStr asBytes asV asD asDL asDM asVL)

/-- Floor (Haskell `div`/`mod`) and truncated (`quot`/`rem`) helpers, the Lean
meaning of the SMT `define-fun`s `moist_fdiv`/`moist_fmod`/`moist_qdiv`/`moist_qrem`.
We take their meaning to be *exactly* the CEK's Plutus division (`haskellDiv`/
`haskellMod` for floor, `Int.tdiv`/`Int.tmod` for truncated) — i.e. the trust
boundary for division is that those SMT define-funs compute Plutus floor/truncated
division, which is their design intent. This makes the CEK agreement definitional
(no extra axioms, no number-theory reconciliation). -/
private def mFdiv (a b : Int) : Int := Moist.CEK.haskellDiv a b
private def mFmod (a b : Int) : Int := Moist.CEK.haskellMod a b
private def mQdiv (a b : Int) : Int := a.tdiv b
private def mQrem (a b : Int) : Int := a.tmod b

/-- A first-order `CekValue` back to a `Const` (for list/array/pair elements). -/
private def cekToConst : CekValue → Const
  | .VCon c => c
  | _ => .Unit

/-- A V-sort tester: does the denoted `V`-value have the given constructor? -/
private def vIs (con : String) (v : CekValue) : Bool :=
  match con, v with
  | "VInt",    .VCon (.Integer _)            => true
  | "VBS",     .VCon (.ByteString _)         => true
  | "VBool",   .VCon (.Bool _)               => true
  | "VUnit",   .VCon .Unit                   => true
  | "VStr",    .VCon (.String _)             => true
  | "VData",   .VCon (.Data _)               => true
  | "VList",   .VCon (.ConstList _)          => true
  | "VDList",  .VCon (.ConstDataList _)      => true
  | "VPDList", .VCon (.ConstPairDataList _)  => true
  | "VPair",   .VCon (.Pair _)               => true
  | "VPairD",  .VCon (.PairData _)           => true
  | "VArr",    .VCon (.ConstArray _)         => true
  | "VConstr", .VConstr _ _                  => true
  | _, _ => false

/-- A Data-kind tester. -/
private def dIsK (con : String) (d : Data) : Bool :=
  match con, d with
  | "DConstr", .Constr _ _ => true
  | "DMap",    .Map _      => true
  | "DList",   .List _     => true
  | "DI",      .I _        => true
  | "DB",      .B _        => true
  | _, _ => false

/-- Meaning of a nullary symbol: a nullary constructor, or a model constant. -/
private def dNull (M : Model) (a : String) : SVal :=
  if a = "VUnit" then .Vv (.VCon .Unit)
  else if a = "vnil" then .VLl []
  else if a = "dnil" then .DLl []
  else if a = "mnil" then .DMm []
  else if a = "(as seq.empty (Seq Int))" then .Bytes []
  else M.const a

/-- Meaning of a unary application, given the (already-denoted) argument. -/
private def dUn (f : String) (x : SVal) : SVal :=
  match f with
  | "not"   => .B (!(asB x))
  | "-"     => .I (- asI x)
  | "VInt"  => .Vv (.VCon (.Integer (asI x)))
  | "VBool" => .Vv (.VCon (.Bool (asB x)))
  | "VBS"   => .Vv (.VCon (.ByteString (bytesToBA (asBytes x))))
  | "VStr"  => .Vv (.VCon (.String (asStr x)))
  | "VData" => .Vv (.VCon (.Data (asD x)))
  | "VList" => .Vv (.VCon (.ConstList ((asVL x).map cekToConst)))
  | "VDList"=> .Vv (.VCon (.ConstDataList (asDL x)))
  | "VPDList"=> .Vv (.VCon (.ConstPairDataList (asDM x)))
  | "VArr"  => .Vv (.VCon (.ConstArray ((asVL x).map cekToConst)))
  | "viVal" => match asV x with | .VCon (.Integer n) => .I n | _ => .I 0
  | "vbVal" => match asV x with | .VCon (.Bool b) => .B b | _ => .B false
  | "vbsVal"=> match asV x with | .VCon (.ByteString bs) => .Bytes (baToBytes bs) | _ => .Bytes []
  | "vsVal" => match asV x with | .VCon (.String s) => .Str s | _ => .Str ""
  | "vdVal" => match asV x with | .VCon (.Data d) => .Dd d | _ => .bad
  | "vlElems"=> match asV x with | .VCon (.ConstList l) => .VLl (l.map .VCon) | _ => .VLl []
  | "vdlElems"=> match asV x with | .VCon (.ConstDataList l) => .DLl l | _ => .DLl []
  | "vpdlElems"=> match asV x with | .VCon (.ConstPairDataList l) => .DMm l | _ => .DMm []
  | "varrElems"=> match asV x with | .VCon (.ConstArray l) => .VLl (l.map .VCon) | _ => .VLl []
  | "vpFst" => match asV x with | .VCon (.Pair (a, _)) => .Vv (.VCon a) | _ => .bad
  | "vpSnd" => match asV x with | .VCon (.Pair (_, b)) => .Vv (.VCon b) | _ => .bad
  | "vpdFst"=> match asV x with | .VCon (.PairData (a, _)) => .Dd a | _ => .bad
  | "vpdSnd"=> match asV x with | .VCon (.PairData (_, b)) => .Dd b | _ => .bad
  | "vcTag" => match asV x with | .VConstr t _ => .I (Int.ofNat t) | _ => .I 0
  | "vcArgs"=> match asV x with | .VConstr _ fs => .VLl fs | _ => .VLl []
  | "DI"    => .Dd (.I (asI x))
  | "DB"    => .Dd (.B (bytesToBA (asBytes x)))
  | "DList" => .Dd (.List (asDL x))
  | "DMap"  => .Dd (.Map (asDM x))
  | "diVal" => match asD x with | .I n => .I n | _ => .I 0
  | "dbVal" => match asD x with | .B bs => .Bytes (baToBytes bs) | _ => .Bytes []
  | "dcTag" => match asD x with | .Constr n _ => .I n | _ => .I 0
  | "dcArgs"=> match asD x with | .Constr _ l => .DLl l | _ => .DLl []
  | "dmEntries"=> match asD x with | .Map l => .DMm l | _ => .DMm []
  | "dlElems"=> match asD x with | .List l => .DLl l | _ => .DLl []
  | "dhd"   => match asDL x with | d :: _ => .Dd d | _ => .bad
  | "dtl"   => match asDL x with | _ :: ds => .DLl ds | _ => .DLl []
  | "vhd"   => match asVL x with | v :: _ => .Vv v | _ => .bad
  | "vtl"   => match asVL x with | _ :: vs => .VLl vs | _ => .VLl []
  | "seq.len"  => .I (Int.ofNat (asBytes x).length)
  | "seq.unit" => .Bytes [asI x]
  | "is-vnil"  => .B (asVL x).isEmpty
  | "is-dnil"  => .B (asDL x).isEmpty
  | "is-mnil"  => .B (asDM x).isEmpty
  -- Explicit `is-V*` arms for the sorts the proofs reason about: semantically equal
  -- to the `startsWith` catch-all below, but `rfl`-reducible (String.startsWith is
  -- not definitionally reducible), so merged-value testers compute.
  | "is-VInt"  => .B (vIs "VInt" (asV x))
  | "is-VBool" => .B (vIs "VBool" (asV x))
  | "is-VBS"   => .B (vIs "VBS" (asV x))
  | "is-VStr"  => .B (vIs "VStr" (asV x))
  | "is-VData" => .B (vIs "VData" (asV x))
  | "is-VUnit"  => .B (vIs "VUnit" (asV x))
  | "is-VList"  => .B (vIs "VList" (asV x))
  | "is-VDList" => .B (vIs "VDList" (asV x))
  | "is-VPair"  => .B (vIs "VPair" (asV x))
  | "is-VPairD" => .B (vIs "VPairD" (asV x))
  | "is-VConstr"=> .B (vIs "VConstr" (asV x))
  | t =>
      if t.startsWith "is-V" then .B (vIs (t.drop 3) (asV x))
      else if t.startsWith "is-D" then .B (dIsK (t.drop 3) (asD x))
      else .bad

/-- Meaning of a binary application, given the two (already-denoted) arguments. -/
private def dBin (f : String) (x y : SVal) : SVal :=
  match f with
  | "and" => .B (asB x && asB y)
  | "or"  => .B (asB x || asB y)
  | "=>"  => .B (!(asB x) || asB y)
  | "="   => .B (svalEq x y)
  | "+"   => .I (asI x + asI y)
  | "-"   => .I (asI x - asI y)
  | "*"   => .I (asI x * asI y)
  | "<"   => .B (decide (asI x < asI y))
  | "<="  => .B (decide (asI x ≤ asI y))
  | ">="  => .B (decide (asI x ≥ asI y))
  | "moist_fdiv" => .I (mFdiv (asI x) (asI y))
  | "moist_fmod" => .I (mFmod (asI x) (asI y))
  | "moist_qdiv" => .I (mQdiv (asI x) (asI y))
  | "moist_qrem" => .I (mQrem (asI x) (asI y))
  | "VPair"  => .Vv (.VCon (.Pair (cekToConst (asV x), cekToConst (asV y))))
  | "VPairD" => .Vv (.VCon (.PairData (asD x, asD y)))
  | "VConstr"=> .Vv (.VConstr (asI x).toNat (asVL y))
  | "DConstr"=> .Dd (.Constr (asI x) (asDL y))
  | "dcons"  => .DLl (asD x :: asDL y)
  | "vcons"  => .VLl (asV x :: asVL y)
  | "seq.nth"=> .I (((asBytes x)[(asI y).toNat]?).getD 0)
  | "seq.++" => .Bytes (asBytes x ++ asBytes y)
  | "str.++" => .Str (asStr x ++ asStr y)
  | _ => .bad

/-- Meaning of a ternary application, given the three (already-denoted) arguments. -/
private def dTern (f : String) (x y z : SVal) : SVal :=
  match f with
  | "ite"  => if asB x then y else z
  | "mcons"=> .DMm ((asD x, asD y) :: asDM z)
  | "seq.extract" => .Bytes (((asBytes x).drop (asI y).toNat).take (asI z).toNat)
  | _ => .bad

/-- The Lean meaning of an SMT expression under `M` (structural; string dispatch
factored into the non-recursive `dNull`/`dUn`/`dBin`/`dTern`). -/
def denote (M : Model) : SExpr → SVal
  | .int n  => .I n
  | .bool b => .B b
  | .str s  => .Str s
  | .atom a => dNull M a
  | .app f [] => dNull M f
  | .app f [a] => dUn f (denote M a)
  | .app f [a, b] => dBin f (denote M a) (denote M b)
  | .app f [a, b, c] => dTern f (denote M a) (denote M b) (denote M c)
  | .app _ _ => .bad

/-- The boolean meaning of a Bool-sorted SMT expression. -/
def denoteB (M : Model) (e : SExpr) : Bool := SVal.asB (denote M e)

/-! ## Concretization of symbolic values -/

/-- A `List CekValue` as a `CekEnv` (order-preserving: head = `Var 1`). -/
def toCekEnv : List CekValue → CekEnv
  | []      => .nil
  | v :: vs => .cons v (toCekEnv vs)

/-! Concretize a symbolic value to a `CekValue` under model `M`. `none` means the
value is not realisable (an ill-sorted first-order value, or a sub-value that
isn't). Higher-order shapes carry their environment, recursively concretized. -/
mutual
def γ (M : Model) : SymV → Option CekValue
  -- A `.fo` value is *first-order* (`VCon`/`VConstr`); never a function.
  | .fo e => match denote M e with
             | .Vv (.VCon c) => some (.VCon c)
             | .Vv (.VConstr t l) => some (.VConstr t l)
             | _ => none
  | .lam body env => match γList M env with | some L => some (.VLam body (toCekEnv L)) | none => none
  | .delay body env => match γList M env with | some L => some (.VDelay body (toCekEnv L)) | none => none
  | .constr tag fs => match γList M fs with | some L => some (.VConstr tag L) | none => none
  | .builtin b args ea => match γList M args with | some L => some (.VBuiltin b L ea) | none => none
  | .choice c a b => if denoteB M c then γ M a else γ M b
def γList (M : Model) : List SymV → Option (List CekValue)
  | []      => some []
  | v :: vs => match γ M v with
               | some cv => match γList M vs with | some L => some (cv :: L) | none => none
               | none => none
end

/-- The environment relation: `ρs` concretizes (pointwise) to `ρ` under `M`. -/
def EnvRel (M : Model) (ρs : SymEnv) (ρ : CekEnv) : Prop :=
  (γList M ρs).map toCekEnv = some ρ

/-! ## The faithful fragment

A term is *faithful* when every builtin it mentions is precisely modelled (so the
compiler and `bigEval` agree exactly on it). -/

/-- The precisely-modelled builtins of the proven fragment. Extended one tier at a
time on the proved scaffold (Integer arithmetic + comparison first). -/
def preciseBuiltin : BuiltinFun → Bool
  | .AddInteger | .SubtractInteger | .MultiplyInteger
  | .EqualsInteger | .LessThanInteger | .LessThanEqualsInteger
  | .DivideInteger | .ModInteger | .QuotientInteger | .RemainderInteger
  | .EqualsString | .AppendString
  | .EqualsByteString | .AppendByteString | .LengthOfByteString
  | .IndexByteString => true
  -- `ConsByteString` is deliberately *excluded*: its symbolic value
  -- `VBS (seq.++ (seq.unit n) bs)` carries the **un-truncated** integer `n` in the
  -- byte sequence, so it is folding-clean (`WfFOR.pBS`/`cleanBS`) only when
  -- `0 ≤ n ≤ 255` — precisely the non-error condition. Since `WfV` is maintained
  -- unconditionally (it is consumed even in `satBuiltin`'s error arm), proving it
  -- would need an *error-conditional* well-sortedness invariant. Left as the one
  -- ByteString builtin outside the proven fragment.
  | _ => false

/-- The constants of the proven fragment (Integer/Bool/Unit/String — denote
directly, no `ByteString`/`Data` round-tripping). -/
def simpleConst : Const → Bool
  | .Integer _ | .Bool _ | .Unit | .String _ => true
  | _ => false

/-! A term is *faithful* (in the proven fragment): λ-calculus + `force`/`delay` +
the precise builtins + simple constants + `Constr`. `Case` and the structural
builtins are the next increment. -/
mutual
def faithfulB : Term → Bool
  | .Var _          => true
  | .Constant (c,_) => simpleConst c
  | .Builtin b      => preciseBuiltin b
  | .Lam _ body     => faithfulB body
  | .Apply f a      => faithfulB f && faithfulB a
  | .Delay t        => faithfulB t
  | .Force t        => faithfulB t
  | .Constr _ ms    => faithfulBList ms
  | .Case scrut alts => faithfulB scrut && faithfulBList alts
  | .Error          => true
def faithfulBList : List Term → Bool
  | []      => true
  | t :: ts => faithfulB t && faithfulBList ts
end

/-- A term is faithful (in the proven fragment). -/
def Faithful (t : Term) : Prop := faithfulB t = true

/-! ## Faithfulness of symbolic values

The evaluation invariant: every value reachable from a faithful term is faithful
— closures capture faithful bodies/environments, partial builtins are precise,
and `constr`/`choice` (out of fragment) never arise. This lets the builtin case
of the simulation invoke the builtin lemma and the `constr`/`choice` cases
discharge as impossible. -/

/-- The first-order shape restriction: a faithful `.fo` value is a *scalar* (its
static head is not one of the structured `V`-constructors). The fragment never
produces `VList`/`VDList`/`VPair`/`VPairD`/`VConstr`-headed first-order exprs (those
need list/pair builtins or constants outside the fragment), so `Case` on a `.fo`
scrutinee only ever hits the `Bool`/`Unit`/`Integer` (or error/indeterminate)
dispatch arms, never the structural ones (which would need a list/pair tier). -/
def foShapeOK (e : SExpr) : Prop :=
  V.vConName e ≠ some "VList" ∧ V.vConName e ≠ some "VDList" ∧
  V.vConName e ≠ some "VPair" ∧ V.vConName e ≠ some "VPairD" ∧
  V.vConName e ≠ some "VConstr"

mutual
def FaithfulV : SymV → Prop
  | .fo e => foShapeOK e
  | .lam body env => faithfulB body = true ∧ FaithfulVList env
  | .delay body env => faithfulB body = true ∧ FaithfulVList env
  | .constr _ fs => FaithfulVList fs
  | .builtin b args _ => preciseBuiltin b = true ∧ FaithfulVList args
  | .choice _ a b => FaithfulV a ∧ FaithfulV b
def FaithfulVList : List SymV → Prop
  | []      => True
  | v :: vs => FaithfulV v ∧ FaithfulVList vs
end

theorem foShapeOK_Vint (e : SExpr) : foShapeOK (V.int e) := by
  simp [foShapeOK, V.int, V.vConName, V.knownVCons]
theorem foShapeOK_Vbool (e : SExpr) : foShapeOK (V.bool e) := by
  simp [foShapeOK, V.bool, V.vConName, V.knownVCons]
theorem foShapeOK_Vstr (e : SExpr) : foShapeOK (V.str e) := by
  simp [foShapeOK, V.str, V.vConName, V.knownVCons]
theorem foShapeOK_Vbs (e : SExpr) : foShapeOK (V.bs e) := by
  simp [foShapeOK, V.bs, V.vConName, V.knownVCons]
theorem foShapeOK_Vdata (e : SExpr) : foShapeOK (V.data e) := by
  simp [foShapeOK, V.data, V.vConName, V.knownVCons]
theorem foShapeOK_unit : foShapeOK V.unit := by
  simp [foShapeOK, V.unit, V.vConName]
/-- `sIte` of two scalar-headed exprs is scalar-headed (a literal condition folds
to a branch; a symbolic one yields a head `"ite"`, not a structured constructor). -/
theorem foShapeOK_sIte (c a b : SExpr) (ha : foShapeOK a) (hb : foShapeOK b) :
    foShapeOK (SExpr.sIte c a b) := by
  cases c with
  | bool bv => cases bv <;> simpa only [SExpr.sIte]
  | int _ => simp [foShapeOK, SExpr.sIte, V.vConName, V.knownVCons]
  | str _ => simp [foShapeOK, SExpr.sIte, V.vConName, V.knownVCons]
  | atom _ => simp [foShapeOK, SExpr.sIte, V.vConName, V.knownVCons]
  | app _ _ => simp [foShapeOK, SExpr.sIte, V.vConName, V.knownVCons]

/-! `FaithfulV` is preserved by `mergeVal` (parallel to `wfV_mergeVal`). -/
mutual
theorem faithfulV_mergeVal (c : SExpr) : ∀ (a b : SymV),
    FaithfulV a → FaithfulV b → FaithfulV (mergeVal c a b)
  | .fo a, .fo b, ha, hb => by simp only [mergeVal]; exact foShapeOK_sIte c a b ha hb
  | .constr t1 fs1, .constr t2 fs2, ha, hb => by
      simp only [mergeVal]
      split
      · next hcond =>
          rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hcond
          obtain ⟨rfl, _⟩ := hcond
          exact faithfulVList_mergeValList c fs1 fs2 ha hb
      · exact ⟨ha, hb⟩
  | .fo _, .lam _ _, ha, hb | .fo _, .delay _ _, ha, hb | .fo _, .constr _ _, ha, hb
  | .fo _, .builtin _ _ _, ha, hb | .fo _, .choice _ _ _, ha, hb
  | .constr _ _, .fo _, ha, hb | .constr _ _, .lam _ _, ha, hb | .constr _ _, .delay _ _, ha, hb
  | .constr _ _, .builtin _ _ _, ha, hb | .constr _ _, .choice _ _ _, ha, hb
  | .lam _ _, _, ha, hb | .delay _ _, _, ha, hb | .builtin _ _ _, _, ha, hb
  | .choice _ _ _, _, ha, hb => ⟨ha, hb⟩
termination_by a _ _ _ => sizeOf a
theorem faithfulVList_mergeValList (c : SExpr) : ∀ (as bs : List SymV),
    FaithfulVList as → FaithfulVList bs → FaithfulVList (mergeValList c as bs)
  | [], [], _, _ => True.intro
  | a :: as, b :: bs, ha, hb => by
      simp only [FaithfulVList] at ha hb
      exact ⟨faithfulV_mergeVal c a b ha.1 hb.1, faithfulVList_mergeValList c as bs ha.2 hb.2⟩
  | [], _ :: _, _, _ => True.intro
  | _ :: _, [], _, _ => True.intro
termination_by as _ _ => sizeOf as
end

/-! ## Foundational denotation lemmas

The smart constructors denote to their intended Boolean operations, and `denote`
inverts the `Const`/`Data` encoders. These are the "z3-bridge-is-definitional"
facts — proved, not axiomatized. -/

-- Reduction lemmas: `denote` of an application reduces to the head helper applied
-- to the denoted arguments (so proofs rewrite rather than reduce the big matches).
@[simp] theorem denote_app1 (M : Model) (f : String) (a : SExpr) :
    denote M (.app f [a]) = dUn f (denote M a) := rfl
@[simp] theorem denote_app2 (M : Model) (f : String) (a b : SExpr) :
    denote M (.app f [a, b]) = dBin f (denote M a) (denote M b) := rfl
@[simp] theorem denote_app3 (M : Model) (f : String) (a b c : SExpr) :
    denote M (.app f [a, b, c]) = dTern f (denote M a) (denote M b) (denote M c) := rfl

-- Per-head reductions for the operators the proofs touch (each is `rfl`, fast).
@[simp] theorem denote_lit_bool (M : Model) (b : Bool) : denote M (.bool b) = .B b := rfl
@[simp] theorem denote_lit_int (M : Model) (n : Int) : denote M (.int n) = .I n := rfl
@[simp] theorem denote_lit_str (M : Model) (s : String) : denote M (.str s) = .Str s := rfl
@[simp] theorem dUn_not (x : SVal) : dUn "not" x = .B (!SVal.asB x) := rfl
@[simp] theorem dBin_or (x y : SVal) : dBin "or" x y = .B (SVal.asB x || SVal.asB y) := rfl
@[simp] theorem dBin_and (x y : SVal) : dBin "and" x y = .B (SVal.asB x && SVal.asB y) := rfl
@[simp] theorem dTern_ite (x y z : SVal) : dTern "ite" x y z = (if SVal.asB x then y else z) := rfl
@[simp] theorem asB_B (b : Bool) : SVal.asB (.B b) = b := rfl

@[simp] theorem denoteB_bool (M : Model) (b : Bool) : denoteB M (.bool b) = b := rfl

@[simp] theorem denoteB_sNot (M : Model) (e : SExpr) : denoteB M (SExpr.sNot e) = !(denoteB M e) := by
  unfold SExpr.sNot; split <;> simp_all [denoteB]

@[simp] theorem denoteB_sOr (M : Model) (a b : SExpr) :
    denoteB M (SExpr.sOr a b) = (denoteB M a || denoteB M b) := by
  unfold SExpr.sOr; split <;> simp_all [denoteB]

@[simp] theorem denoteB_sAnd (M : Model) (a b : SExpr) :
    denoteB M (SExpr.sAnd a b) = (denoteB M a && denoteB M b) := by
  unfold SExpr.sAnd; split <;> simp_all [denoteB]

theorem denote_sIte (M : Model) (c a b : SExpr) :
    denote M (SExpr.sIte c a b) = (if denoteB M c then denote M a else denote M b) := by
  unfold SExpr.sIte
  split
  · simp_all [denoteB]
  · simp_all [denoteB]
  · simp only [denote_app3, dTern_ite, denoteB]

@[simp] theorem denoteB_sIte (M : Model) (c a b : SExpr) :
    denoteB M (SExpr.sIte c a b) = (if denoteB M c then denoteB M a else denoteB M b) := by
  show SVal.asB (denote M (SExpr.sIte c a b)) = _
  rw [denote_sIte]; cases h : denoteB M c <;> simp [h, denoteB]

/-! ## `choice`/`mergeVal` distribution (the symbolic-branching engine)

`mergeVal c a b` builds `if c then a else b`, keeping `constr` structure where the
shapes agree and deferring to a `choice` otherwise. The key fact is that `γ`
distributes through it: concretizing the merge is the (model-decided) branch. This
is what lets every eliminator (`symApply`/`symForce`/`symCase`) push a `choice`
through to an SMT `ite` soundly. -/
mutual
theorem γ_mergeVal (M : Model) (c : SExpr) : ∀ (a b : SymV),
    γ M (mergeVal c a b) = if denoteB M c then γ M a else γ M b
  | .fo a, .fo b => by
      simp only [mergeVal]; rw [γ, denote_sIte]; cases h : denoteB M c <;> simp [h, γ]
  | .constr t1 fs1, .constr t2 fs2 => by
      simp only [mergeVal]
      split
      · next hcond =>
          rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hcond
          obtain ⟨rfl, hlen⟩ := hcond
          rw [γ, γList_mergeValList M c fs1 fs2 hlen]
          cases h : denoteB M c <;> simp [h, γ]
      · rfl
  | .fo _, .lam _ _ | .fo _, .delay _ _ | .fo _, .constr _ _ | .fo _, .builtin _ _ _
  | .fo _, .choice _ _ _
  | .constr _ _, .fo _ | .constr _ _, .lam _ _ | .constr _ _, .delay _ _
  | .constr _ _, .builtin _ _ _ | .constr _ _, .choice _ _ _
  | .lam _ _, _ | .delay _ _, _ | .builtin _ _ _, _ | .choice _ _ _, _ => by
      rfl
termination_by a _ => sizeOf a
theorem γList_mergeValList (M : Model) (c : SExpr) : ∀ (as bs : List SymV),
    as.length = bs.length →
    γList M (mergeValList c as bs) = if denoteB M c then γList M as else γList M bs
  | [], [], _ => by simp only [mergeValList]; cases h : denoteB M c <;> simp [h]
  | a :: as, b :: bs, hlen => by
      simp only [mergeValList, γList, γ_mergeVal M c a b,
        γList_mergeValList M c as bs (by simpa using hlen)]
      cases h : denoteB M c <;> simp [h, γList]
termination_by as _ _ => sizeOf as
end

/-! ## Foundational `denote` reductions (needed early by `WfFO`/`WfV`) -/

@[simp] theorem denote_atom (M : Model) (a : String) : denote M (.atom a) = dNull M a := rfl
@[simp] theorem dUn_VInt (x : SVal) : dUn "VInt" x = .Vv (.VCon (.Integer (SVal.asI x))) := rfl
@[simp] theorem dUn_VBool (x : SVal) : dUn "VBool" x = .Vv (.VCon (.Bool (SVal.asB x))) := rfl
@[simp] theorem dUn_VStr (x : SVal) : dUn "VStr" x = .Vv (.VCon (.String (SVal.asStr x))) := rfl
@[simp] theorem dUn_VBS (x : SVal) : dUn "VBS" x = .Vv (.VCon (.ByteString (bytesToBA (SVal.asBytes x)))) := rfl
@[simp] theorem dUn_VData (x : SVal) : dUn "VData" x = .Vv (.VCon (.Data (SVal.asD x))) := rfl
@[simp] theorem dUn_seqlen (x : SVal) : dUn "seq.len" x = .I (Int.ofNat (SVal.asBytes x).length) := rfl
@[simp] theorem dBin_VConstr (x y : SVal) :
    dBin "VConstr" x y = .Vv (.VConstr (SVal.asI x).toNat (SVal.asVL y)) := rfl
@[simp] theorem dNull_VUnit (M : Model) : dNull M "VUnit" = .Vv (.VCon .Unit) := rfl

/-! ## `γ` inversions used by the builtin simulation -/

/-- `γ` of a first-order value pins down its denotation to that value. -/
theorem γ_fo_denote {M : Model} {e : SExpr} {va : CekValue}
    (h : γ M (.fo e) = some va) : denote M e = .Vv va := by
  unfold γ at h; split at h <;> simp_all

/-- Inversion for a (possibly partial) builtin value. -/
theorem γ_builtin_inv {M : Model} {b : BuiltinFun} {args : List SymV} {ea} {vf : CekValue}
    (h : γ M (.builtin b args ea) = some vf) :
    ∃ L, γList M args = some L ∧ vf = .VBuiltin b L ea := by
  unfold γ at h
  cases hL : γList M args with
  | none => rw [hL] at h; simp at h
  | some L => rw [hL] at h; simp only [Option.some.injEq] at h; exact ⟨L, rfl, h.symm⟩

theorem γ_constr_inv {M : Model} {tag : Nat} {fs : List SymV} {vf : CekValue}
    (h : γ M (.constr tag fs) = some vf) :
    ∃ L, γList M fs = some L ∧ vf = .VConstr tag L := by
  unfold γ at h
  cases hL : γList M fs with
  | none => rw [hL] at h; simp at h
  | some L => rw [hL] at h; simp only [Option.some.injEq] at h; exact ⟨L, rfl, h.symm⟩

/-- `vIs "VInt"` holds only of integer values. -/
theorem vIs_VInt {va : CekValue} (h : vIs "VInt" va = true) : ∃ n, va = .VCon (.Integer n) := by
  cases va with
  | VCon c => cases c with
    | Integer n => exact ⟨n, rfl⟩
    | _ => simp [vIs] at h
  | _ => simp [vIs] at h

theorem vIs_VBS {va : CekValue} (h : vIs "VBS" va = true) : ∃ bs, va = .VCon (.ByteString bs) := by
  cases va with
  | VCon c => cases c with | ByteString bs => exact ⟨bs, rfl⟩ | _ => simp [vIs] at h
  | _ => simp [vIs] at h

theorem vIs_VStr {va : CekValue} (h : vIs "VStr" va = true) : ∃ s, va = .VCon (.String s) := by
  cases va with
  | VCon c => cases c with | String s => exact ⟨s, rfl⟩ | _ => simp [vIs] at h
  | _ => simp [vIs] at h

theorem vIs_VData {va : CekValue} (h : vIs "VData" va = true) : ∃ d, va = .VCon (.Data d) := by
  cases va with
  | VCon c => cases c with | Data d => exact ⟨d, rfl⟩ | _ => simp [vIs] at h
  | _ => simp [vIs] at h

theorem vIs_VBool {va : CekValue} (h : vIs "VBool" va = true) : ∃ b, va = .VCon (.Bool b) := by
  cases va with
  | VCon c => cases c with | Bool b => exact ⟨b, rfl⟩ | _ => simp [vIs] at h
  | _ => simp [vIs] at h

theorem vIs_VUnit {va : CekValue} (h : vIs "VUnit" va = true) : va = .VCon .Unit := by
  cases va with
  | VCon c => cases c with | Unit => rfl | _ => simp [vIs] at h
  | _ => simp [vIs] at h

/-! ## Model well-sortedness invariant `WfFO`

The folding projectors (`V.sAsInt`/`V.sIsCon`/…) strip a `V`-wrapper to expose its
inner expression; under an *arbitrary* (untyped) model that inner can denote to the
wrong sort, which would make e.g. `equalsInteger` unsound (`svalEq` is
constructor-sensitive while the value's identity goes through `asI`). `WfFO M e` is
the "folding-clean" invariant: `e` denotes to a first-order value `va`, the
projectors read off `va`'s components, and the testers reflect `va`'s constructor.
It holds *robustly* for literal constants and builtin results, and for symbolic
input atoms exactly when the model assigns them their declared sort — which is what
z3 guarantees. (Conjuncts are added per builtin tier.) -/
/-- The folding-clean record for `e` denoting first-order value `va`: every
projector reads off `va`'s component of its sort, and every tester reflects `va`'s
constructor. (Named fields so connection lemmas access exactly what they need and
new sorts can be added without disturbing the others.) -/
structure WfFOR (M : Model) (e : SExpr) (va : CekValue) : Prop where
  den   : denote M e = .Vv va
  pInt  : ∀ n, va = .VCon (.Integer n)      → denote M (V.sAsInt e)  = .I n
  pBool : ∀ b, va = .VCon (.Bool b)         → denote M (V.sAsBool e) = .B b
  pBS   : ∀ bs, va = .VCon (.ByteString bs) → denote M (V.sAsBS e)   = .Bytes (baToBytes bs)
  pStr  : ∀ s, va = .VCon (.String s)       → denote M (V.sAsStr e)  = .Str s
  pData : ∀ d, va = .VCon (.Data d)         → denote M (V.sAsData e) = .Dd d
  tInt  : denoteB M (V.sIsCon "VInt" e)  = vIs "VInt" va
  tBool : denoteB M (V.sIsCon "VBool" e) = vIs "VBool" va
  tBS   : denoteB M (V.sIsCon "VBS" e)   = vIs "VBS" va
  tStr  : denoteB M (V.sIsCon "VStr" e)  = vIs "VStr" va
  tData : denoteB M (V.sIsCon "VData" e) = vIs "VData" va
  -- Sort-testers for the remaining `constToTagAndFields`-relevant sorts, so the
  -- `Case`-on-constant dispatch can pin the scrutinee's *semantic* sort from its
  -- *syntactic* head (`vConName`). Like the others, these reflect `va`'s constructor.
  tUnit  : denoteB M (V.sIsCon "VUnit" e)   = vIs "VUnit" va
  tList  : denoteB M (V.sIsCon "VList" e)   = vIs "VList" va
  tDList : denoteB M (V.sIsCon "VDList" e)  = vIs "VDList" va
  tPair  : denoteB M (V.sIsCon "VPair" e)   = vIs "VPair" va
  tPairD : denoteB M (V.sIsCon "VPairD" e)  = vIs "VPairD" va
  tConstr: denoteB M (V.sIsCon "VConstr" e) = vIs "VConstr" va
  -- The byte-projection of *any* folding-clean value is a genuine byte list
  -- (`baToBytes` of some `ByteArray`), not just for `VBS` values: a non-`VBS`
  -- folds through `vbsVal` to `Bytes []`. This is what lets `appendByteString`
  -- combine clean operands into a clean result regardless of operand sort.
  cleanBS : ∃ ba, denote M (V.sAsBS e) = .Bytes (baToBytes ba)

def WfFO (M : Model) (e : SExpr) : Prop := ∃ va, WfFOR M e va

mutual
/-- Every first-order sub-value reachable in a computation is folding-clean. -/
def WfV (M : Model) : SymV → Prop
  | .fo e             => WfFO M e
  | .lam _ env        => WfVList M env
  | .delay _ env      => WfVList M env
  | .constr _ fs      => WfVList M fs
  | .builtin _ args _ => WfVList M args
  | .choice _ a b     => WfV M a ∧ WfV M b
def WfVList (M : Model) : List SymV → Prop
  | []      => True
  | v :: vs => WfV M v ∧ WfVList M vs
end

theorem wfVList_nil (M : Model) : WfVList M [] := True.intro

/-- Resolve a `WfFO` against a `γ`-value: the record is about that value. -/
theorem wfFOR_of {M : Model} {e : SExpr} {va : CekValue}
    (hwf : WfFO M e) (hγ : γ M (.fo e) = some va) : WfFOR M e va := by
  obtain ⟨va', hr⟩ := hwf
  have hvv : va = va' := by
    have : SVal.Vv va = SVal.Vv va' := (γ_fo_denote hγ) ▸ hr.den; injection this
  subst hvv; exact hr

theorem wf_int {M : Model} {e : SExpr} {va : CekValue}
    (hwf : WfFO M e) (hγ : γ M (.fo e) = some va) (hg : denoteB M (gInt e) = false) :
    ∃ n, va = .VCon (.Integer n) ∧ denote M (V.sAsInt e) = .I n := by
  have hr := wfFOR_of hwf hγ
  have ht : denoteB M (V.sIsCon "VInt" e) = true := by simpa [gInt, denoteB_sNot] using hg
  rw [hr.tInt] at ht
  obtain ⟨n, hn⟩ := vIs_VInt ht
  exact ⟨n, hn, hr.pInt n hn⟩

theorem wf_bs {M : Model} {e : SExpr} {va : CekValue}
    (hwf : WfFO M e) (hγ : γ M (.fo e) = some va) (hg : denoteB M (gBS e) = false) :
    ∃ bs, va = .VCon (.ByteString bs) ∧ denote M (V.sAsBS e) = .Bytes (baToBytes bs) := by
  have hr := wfFOR_of hwf hγ
  have ht : denoteB M (V.sIsCon "VBS" e) = true := by simpa [gBS, denoteB_sNot] using hg
  rw [hr.tBS] at ht
  obtain ⟨bs, hbs⟩ := vIs_VBS ht
  exact ⟨bs, hbs, hr.pBS bs hbs⟩

theorem wf_str {M : Model} {e : SExpr} {va : CekValue}
    (hwf : WfFO M e) (hγ : γ M (.fo e) = some va) (hg : denoteB M (gStr e) = false) :
    ∃ s, va = .VCon (.String s) ∧ denote M (V.sAsStr e) = .Str s := by
  have hr := wfFOR_of hwf hγ
  have ht : denoteB M (V.sIsCon "VStr" e) = true := by simpa [gStr, denoteB_sNot] using hg
  rw [hr.tStr] at ht
  obtain ⟨s, hs⟩ := vIs_VStr ht
  exact ⟨s, hs, hr.pStr s hs⟩

theorem wf_data {M : Model} {e : SExpr} {va : CekValue}
    (hwf : WfFO M e) (hγ : γ M (.fo e) = some va) (hg : denoteB M (gData e) = false) :
    ∃ d, va = .VCon (.Data d) ∧ denote M (V.sAsData e) = .Dd d := by
  have hr := wfFOR_of hwf hγ
  have ht : denoteB M (V.sIsCon "VData" e) = true := by simpa [gData, denoteB_sNot] using hg
  rw [hr.tData] at ht
  obtain ⟨d, hd⟩ := vIs_VData ht
  exact ⟨d, hd, hr.pData d hd⟩

/-! ## The core simulation (proved separately) -/

/-- **Simulation.** At equal fuel, for any model and concretizing environment, on
a faithful term: when the compiled result is determinate-and-non-erroring it
agrees with `bigEval` on a concrete value; when it is determinate-and-erroring,
`bigEval` errors too. -/
abbrev Sim : Prop := ∀ (M : Model) (n : Nat) (ρs : SymEnv) (ρ : CekEnv) (t : Term),
  EnvRel M ρs ρ → FaithfulVList ρs → WfVList M ρs → Faithful t →
  (denoteB M (symEval n ρs t).inc = false → denoteB M (symEval n ρs t).err = false →
     ∃ cv, γ M (symEval n ρs t).val = some cv ∧ bigEval n ρ t = some cv) ∧
  (denoteB M (symEval n ρs t).inc = false → denoteB M (symEval n ρs t).err = true →
     bigEval n ρ t = none)

/-- **Upward fuel-stability.** Once a result is determinate (`¬inc`) under `M`,
one more fuel level keeps it determinate and preserves its error condition. -/
abbrev Stab : Prop := ∀ (M : Model) (n : Nat) (ρs : SymEnv) (ρ : CekEnv) (t : Term),
  EnvRel M ρs ρ → FaithfulVList ρs → Faithful t →
  denoteB M (symEval n ρs t).inc = false →
    denoteB M (symEval (n+1) ρs t).inc = false ∧
    denoteB M (symEval (n+1) ρs t).err = denoteB M (symEval n ρs t).err

/-! ## Faithfulness preservation

Every value `symEval`/`symApply`/`symForce` produces from faithful inputs is
faithful. (Used so the simulation's builtin case can read off `preciseBuiltin b`,
and so `constr`/`choice` never arise.) -/

theorem faithfulVList_nil : FaithfulVList [] := True.intro

theorem symLookup_faithful : ∀ (ρs : SymEnv) (k : Nat) (v : SymV),
    FaithfulVList ρs → symLookup ρs k = some v → FaithfulV v
  | [], _, _, _, h => by simp [symLookup] at h
  | _ :: _, 0, _, _, h => by simp [symLookup] at h
  | w :: _, 1, v, hρ, h => by
      have hw : w = v := by simpa [symLookup] using h
      have h1 : FaithfulV w := by have := hρ; simp only [FaithfulVList] at this; exact this.1
      rw [hw] at h1; exact h1
  | _ :: rest, k + 2, v, hρ, h => by
      have hr : FaithfulVList rest := by have := hρ; simp only [FaithfulVList] at this; exact this.2
      exact symLookup_faithful rest (k + 1) v hr (by simpa [symLookup] using h)

/-- A saturated *precise* (non-pass-through) builtin always yields a first-order
value (every `symBuiltin` arm returns an `.fo`). Proved by filtering on
`preciseBuiltin` (only the precise constructors survive) then reducing. -/
theorem symSaturate_val_fo (b : BuiltinFun) (args : List SymV) (h : preciseBuiltin b = true) :
    ∃ e, (symSaturate b args).val = .fo e := by
  cases b <;> first | (exfalso; revert h; decide) | skip
  all_goals
    (show ∃ e, (symBuiltin _ (List.map Prod.snd (List.map reifyFO args.reverse))).val = .fo e
     generalize (List.map Prod.snd (List.map reifyFO args.reverse)) = R
     rcases R with _ | ⟨a, _ | ⟨b2, _ | ⟨c, t⟩⟩⟩ <;> exact ⟨_, rfl⟩)

/-- Encoded simple constants are scalar-headed. -/
theorem foShapeOK_simpleConst (c : Const) (h : simpleConst c = true) : foShapeOK (constToSExpr c) := by
  cases c
  case Integer n => simp only [constToSExpr]; exact foShapeOK_Vint _
  case Bool b => simp only [constToSExpr]; exact foShapeOK_Vbool _
  case Unit => exact foShapeOK_unit
  case String s => simp only [constToSExpr]; exact foShapeOK_Vstr _
  all_goals exact absurd h (by simp [simpleConst])

/-- Hence such a result is (model-independently) faithful: it is `.fo` of a
scalar-headed expr (`V.int`/`V.bool`/`V.str`/`V.bs`, or `V.unit` for a wrong arity). -/
theorem faithfulV_symSaturate (b : BuiltinFun) (args : List SymV) (h : preciseBuiltin b = true) :
    FaithfulV (symSaturate b args).val := by
  cases b <;> first | (exfalso; revert h; decide) | skip
  all_goals
    (show FaithfulV (symBuiltin _ (List.map Prod.snd (List.map reifyFO args.reverse))).val
     generalize (List.map Prod.snd (List.map reifyFO args.reverse)) = R
     rcases R with _ | ⟨a, _ | ⟨b2, _ | ⟨c, t⟩⟩⟩ <;>
       first
         | exact foShapeOK_unit | exact foShapeOK_Vint _ | exact foShapeOK_Vbool _
         | exact foShapeOK_Vstr _ | exact foShapeOK_Vbs _)

/-- A faithful alternative list, indexed, yields a faithful result value. -/
theorem faithfulVList_getElem? : ∀ (L : List SymR) (i : Nat) (r : SymR),
    FaithfulVList (L.map SymR.val) → L[i]? = some r → FaithfulV r.val
  | [], _, _, _, hi => by simp at hi
  | x :: xs, 0, r, h, hi => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simp only [List.map_cons, FaithfulVList] at h
      exact h.1
  | x :: xs, i+1, r, h, hi => by
      simp only [List.getElem?_cons_succ] at hi
      simp only [List.map_cons, FaithfulVList] at h
      exact faithfulVList_getElem? xs i r h.2 hi

/-- A faithful term-alternative list, indexed, yields a faithful term. -/
theorem faithfulBList_get : ∀ (alts : List Term) (i : Nat) (alt : Term),
    faithfulBList alts = true → alts[i]? = some alt → faithfulB alt = true
  | [], _, _, _, hi => by simp at hi
  | a :: as, 0, alt, h, hi => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simp only [faithfulBList, Bool.and_eq_true] at h
      exact h.1
  | a :: as, i+1, alt, h, hi => by
      simp only [List.getElem?_cons_succ] at hi
      simp only [faithfulBList, Bool.and_eq_true] at h
      exact faithfulBList_get as i alt h.2 hi

/-- `altOr` of a faithful alternative list is faithful. -/
theorem faithfulV_altOr (altRs : List SymR) (i : Nat)
    (h : FaithfulVList (altRs.map SymR.val)) : FaithfulV (altOr altRs i).val := by
  unfold altOr
  cases hi : altRs[i]? with
  | none => exact foShapeOK_unit
  | some r => exact faithfulVList_getElem? altRs i r h hi

/-- `dispatchIntFrom` over a faithful alternative list is faithful (nested merges). -/
theorem faithfulV_dispatchIntFrom (tagE : SExpr) : ∀ (i : Nat) (altRs : List SymR),
    FaithfulVList (altRs.map SymR.val) → FaithfulV (dispatchIntFrom tagE i altRs).val
  | _, [], _ => by simp only [dispatchIntFrom]; exact foShapeOK_unit
  | i, r :: rs, h => by
      simp only [dispatchIntFrom, symMerge]
      have h' : FaithfulV r.val ∧ FaithfulVList (rs.map SymR.val) := by
        simpa only [List.map_cons, FaithfulVList] using h
      exact faithfulV_mergeVal _ _ _ h'.1 (faithfulV_dispatchIntFrom tagE (i+1) rs h'.2)

mutual
theorem faithfulV_symEval : ∀ (n : Nat) (ρs : SymEnv) (t : Term),
    FaithfulVList ρs → Faithful t → FaithfulV (symEval n ρs t).val
  | 0, _, _, _, _ => by simp [symEval, incR, junk, FaithfulV, foShapeOK_unit]
  | _+1, ρs, .Var k, hρ, _ => by
      simp only [symEval]
      cases h : symLookup ρs k with
      | none => simp [errR, junk, FaithfulV, foShapeOK_unit]
      | some v => exact symLookup_faithful ρs k v hρ h
  | _+1, _, .Constant (c, _), _, ht => by
      simp only [symEval]; exact foShapeOK_simpleConst c (by simpa [Faithful, faithfulB] using ht)
  | _+1, _, .Builtin b, _, ht => by
      simp only [symEval]
      exact ⟨by simpa [Faithful, faithfulB] using ht, faithfulVList_nil⟩
  | _+1, ρs, .Lam _ body, hρ, ht => by
      simp only [symEval]; exact ⟨by simpa [Faithful, faithfulB] using ht, hρ⟩
  | _+1, ρs, .Delay body, hρ, ht => by
      simp only [symEval]; exact ⟨by simpa [Faithful, faithfulB] using ht, hρ⟩
  | n+1, ρs, .Apply f a, hρ, ht => by
      have hfa : faithfulB f = true ∧ faithfulB a = true := by
        have := ht; simp only [Faithful, faithfulB, Bool.and_eq_true] at this; exact this
      simp only [symEval]
      exact faithfulV_symApply n (symEval n ρs f).val (symEval n ρs a).val
        (faithfulV_symEval n ρs f hρ hfa.1) (faithfulV_symEval n ρs a hρ hfa.2)
  | n+1, ρs, .Force t, hρ, ht => by
      have ht' : Faithful t := by simpa [Faithful, faithfulB] using ht
      simp only [symEval]
      exact faithfulV_symForce n (symEval n ρs t).val (faithfulV_symEval n ρs t hρ ht')
  | n+1, ρs, .Constr tag ms, hρ, ht => by
      have hms : faithfulBList ms = true := by simpa [Faithful, faithfulB] using ht
      simp only [symEval]
      exact faithfulV_symEvalList n ρs ms hρ hms
  | n+1, ρs, .Case scrut alts, hρ, ht => by
      have ht' : faithfulB scrut = true ∧ faithfulBList alts = true := by
        simpa only [Faithful, faithfulB, Bool.and_eq_true] using ht
      simp only [symEval]
      exact faithfulV_symCase n ρs alts (symEval n ρs scrut).val hρ ht'.2
        (faithfulV_symEval n ρs scrut hρ ht'.1)
  | _+1, _, .Error, _, _ => by simp [symEval, errR, junk, FaithfulV, foShapeOK_unit]
termination_by n _ t => (n, sizeOf t)

theorem faithfulV_symApply : ∀ (n : Nat) (vf va : SymV),
    FaithfulV vf → FaithfulV va → FaithfulV (symApply n vf va).val
  | 0, _, _, _, _ => by simp [symApply, incR, junk, FaithfulV, foShapeOK_unit]
  | n+1, .lam body env, va, hf, ha => by
      have hbody : faithfulB body = true ∧ FaithfulVList env := hf
      simp only [symApply]
      exact faithfulV_symEval n (va :: env) body ⟨ha, hbody.2⟩ hbody.1
  | _+1, .builtin b args ea, va, hf, ha => by
      have hf' : preciseBuiltin b = true ∧ FaithfulVList args := hf
      obtain ⟨hpre, hargs⟩ := hf'
      simp only [symApply]
      cases h1 : ea.head with
      | argQ => simp [h1, errR, junk, FaithfulV, foShapeOK_unit]
      | argV =>
          cases h2 : ea.tail with
          | none => simp only [h1, h2]; exact faithfulV_symSaturate b (va :: args) hpre
          | some rest =>
              simp only [h1, h2]
              exact ⟨hpre, ha, hargs⟩
  | n+1, .choice c x y, va, hf, ha => by
      simp only [symApply]
      exact faithfulV_mergeVal c _ _ (faithfulV_symApply n x va hf.1 ha)
        (faithfulV_symApply n y va hf.2 ha)
  | _+1, .fo _, _, _, _ => by simp [symApply, errR, junk, FaithfulV, foShapeOK_unit]
  | _+1, .delay _ _, _, _, _ => by simp [symApply, errR, junk, FaithfulV, foShapeOK_unit]
  | _+1, .constr _ _, _, _, _ => by simp [symApply, errR, junk, FaithfulV, foShapeOK_unit]
termination_by n _ _ => (n, 0)

theorem faithfulV_symForce : ∀ (n : Nat) (vt : SymV),
    FaithfulV vt → FaithfulV (symForce n vt).val
  | 0, _, _ => by simp [symForce, incR, junk, FaithfulV, foShapeOK_unit]
  | n+1, .delay body env, ht => by
      have hbody : faithfulB body = true ∧ FaithfulVList env := ht
      simp only [symForce]
      exact faithfulV_symEval n env body hbody.2 hbody.1
  | _+1, .builtin b args ea, ht => by
      have ht' : preciseBuiltin b = true ∧ FaithfulVList args := ht
      obtain ⟨hpre, hargs⟩ := ht'
      simp only [symForce]
      cases h1 : ea.head with
      | argV => simp [h1, errR, junk, FaithfulV, foShapeOK_unit]
      | argQ =>
          cases h2 : ea.tail with
          | none => simp only [h1, h2]; exact faithfulV_symSaturate b args hpre
          | some rest => simp only [h1, h2]; exact ⟨hpre, hargs⟩
  | n+1, .choice c x y, ht => by
      simp only [symForce]
      exact faithfulV_mergeVal c _ _ (faithfulV_symForce n x ht.1) (faithfulV_symForce n y ht.2)
  | _+1, .fo _, _ => by simp [symForce, errR, junk, FaithfulV, foShapeOK_unit]
  | _+1, .lam _ _, _ => by simp [symForce, errR, junk, FaithfulV, foShapeOK_unit]
  | _+1, .constr _ _, _ => by simp [symForce, errR, junk, FaithfulV, foShapeOK_unit]
termination_by n vt => (n, sizeOf vt)
theorem faithfulV_symEvalList : ∀ (n : Nat) (ρs : SymEnv) (ms : List Term),
    FaithfulVList ρs → faithfulBList ms = true →
    FaithfulVList ((symEvalList n ρs ms).map SymR.val)
  | _, _, [], _, _ => by simp [symEvalList, FaithfulVList]
  | n, ρs, t :: ts, hρ, hms => by
      have hms' : faithfulB t = true ∧ faithfulBList ts = true := by
        simpa [faithfulBList, Bool.and_eq_true] using hms
      simp only [symEvalList, List.map]
      exact ⟨faithfulV_symEval n ρs t hρ hms'.1, faithfulV_symEvalList n ρs ts hρ hms'.2⟩
termination_by n _ ms => (n, sizeOf ms)

theorem faithfulV_symApplyList : ∀ (n : Nat) (vf : SymV) (args : List SymV),
    FaithfulV vf → FaithfulVList args → FaithfulV (symApplyList n vf args).val
  | _, vf, [], hf, _ => by simp only [symApplyList]; exact hf
  | n, vf, a :: as, hf, ha => by
      simp only [symApplyList]
      exact faithfulV_symApplyList n (symApply n vf a).val as
        (faithfulV_symApply n vf a hf ha.1) ha.2
termination_by n _ args => (n, sizeOf args)

theorem faithfulV_symCase : ∀ (n : Nat) (ρs : SymEnv) (alts : List Term) (scrut : SymV),
    FaithfulVList ρs → faithfulBList alts = true → FaithfulV scrut →
    FaithfulV (symCase n ρs alts scrut).val
  | 0, _, _, _, _, _, _ => by simp only [symCase]; exact foShapeOK_unit
  | m+1, ρs, alts, .constr tag fields, hρ, hms, hf => by
      simp only [symCase]
      cases ha : alts[tag]? with
      | none => exact foShapeOK_unit
      | some alt =>
          simp only [ha]
          exact faithfulV_symApplyList m (symEval m ρs alt).val fields
            (faithfulV_symEval m ρs alt hρ (faithfulBList_get alts tag alt hms ha)) hf
  | m+1, ρs, alts, .choice c x y, hρ, hms, hf => by
      simp only [symCase]
      exact faithfulV_mergeVal c _ _
        (faithfulV_symCase m ρs alts x hρ hms hf.1)
        (faithfulV_symCase m ρs alts y hρ hms hf.2)
  | m+1, ρs, alts, .fo e, hρ, hms, hf => by
      simp only [symCase]
      have hAR : FaithfulVList ((symEvalList m ρs alts).map SymR.val) :=
        faithfulV_symEvalList m ρs alts hρ hms
      have hf' : V.vConName e ≠ some "VList" ∧ V.vConName e ≠ some "VDList" ∧
                 V.vConName e ≠ some "VPair" ∧ V.vConName e ≠ some "VPairD" ∧
                 V.vConName e ≠ some "VConstr" := hf
      obtain ⟨hL, hDL, hP, hPD, _⟩ := hf'
      split <;> rename_i heq <;>
        first
          | exact foShapeOK_unit
          | exact absurd heq hL
          | exact absurd heq hDL
          | exact absurd heq hP
          | exact absurd heq hPD
          | exact faithfulV_dispatchIntFrom _ 0 _ hAR
          | (split <;>
              first
                | exact foShapeOK_unit
                | exact faithfulV_altOr _ 0 hAR
                | exact faithfulV_mergeVal _ _ _
                    (faithfulV_altOr _ 1 hAR) (faithfulV_altOr _ 0 hAR))
  | m+1, _, _, .lam _ _, _, _, _ => by simp only [symCase]; exact foShapeOK_unit
  | m+1, _, _, .delay _ _, _, _, _ => by simp only [symCase]; exact foShapeOK_unit
  | m+1, _, _, .builtin _ _ _, _, _, _ => by simp only [symCase]; exact foShapeOK_unit
termination_by n _ _ _ => (n, 0)
end

/-! ## `WfFO` base / closure lemmas and `WfV` preservation -/

/-- The *raw* byte-projection `vbsVal` always denotes to a genuine byte list: on a
`VBS` value it is `baToBytes` of the array, and on anything else it is `Bytes []`
(`= baToBytes ∅`). This is the engine behind the `cleanBS` field for every non-`VBS`
folding-clean value (whose `sAsBS` folds to `asBS`). -/
theorem denote_asBS_clean (M : Model) (e : SExpr) :
    ∃ ba, denote M (V.asBS e) = .Bytes (baToBytes ba) := by
  have he : denote M (V.asBS e)
      = (match SVal.asV (denote M e) with
         | .VCon (.ByteString bs) => .Bytes (baToBytes bs)
         | _ => .Bytes []) := by simp only [V.asBS, denote_app1]; rfl
  rw [he]; split
  · next bs _ => exact ⟨bs, rfl⟩
  · exact ⟨ByteArray.mk #[], by simp [baToBytes]⟩

/-- `V.unit` is folding-clean (it is a concrete `VCon Unit`). -/
theorem wfFO_unit (M : Model) : WfFO M V.unit := by
  refine ⟨.VCon .Unit, by simp only [V.unit, denote_atom, dNull_VUnit],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn; exact absurd hn (by simp)
  · intro b hb; exact absurd hb (by simp)
  · intro bs hbs; exact absurd hbs (by simp)
  · intro s hs; exact absurd hs (by simp)
  · intro d hd; exact absurd hd (by simp)
  all_goals first
    | exact denote_asBS_clean M _
    | simp [V.unit, V.sIsCon, V.vConName, vIs, denoteB, dNull]

/-- Any `V.int` wrapper of an `Int`-denoting expression is folding-clean. -/
theorem wfFO_Vint (M : Model) (e : SExpr) (k : Int) (h : denote M e = .I k) :
    WfFO M (V.int e) := by
  refine ⟨.VCon (.Integer k), by simp only [V.int, denote_app1, dUn_VInt, h, SVal.asI],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm; injection hm with hm'; injection hm' with hm''; subst hm''
    simp only [V.int, V.sAsInt, h]
  · intro b hb; exact absurd hb (by simp)
  · intro bs hbs; exact absurd hbs (by simp)
  · intro s hs; exact absurd hs (by simp)
  · intro d hd; exact absurd hd (by simp)
  all_goals first
    | exact denote_asBS_clean M _
    | simp [V.int, V.sIsCon, V.vConName, vIs, denoteB, V.knownVCons]

/-- Any `V.bool` wrapper of a `Bool`-denoting expression is folding-clean. -/
theorem wfFO_Vbool (M : Model) (e : SExpr) (c : Bool) (h : denote M e = .B c) :
    WfFO M (V.bool e) := by
  refine ⟨.VCon (.Bool c), by simp only [V.bool, denote_app1, dUn_VBool, h, SVal.asB],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn; exact absurd hn (by simp)
  · intro b hb; injection hb with hb'; injection hb' with hb''; subst hb''
    simp only [V.bool, V.sAsBool, h]
  · intro bs hbs; exact absurd hbs (by simp)
  · intro s hs; exact absurd hs (by simp)
  · intro d hd; exact absurd hd (by simp)
  all_goals first
    | exact denote_asBS_clean M _
    | simp [V.bool, V.sIsCon, V.vConName, vIs, denoteB, V.knownVCons]

/-- Any `V.str` wrapper of a `String`-denoting expression is folding-clean. -/
theorem wfFO_Vstr (M : Model) (e : SExpr) (s : String) (h : denote M e = .Str s) :
    WfFO M (V.str e) := by
  refine ⟨.VCon (.String s), by simp only [V.str, denote_app1, dUn_VStr, h, SVal.asStr],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn; exact absurd hn (by simp)
  · intro b hb; exact absurd hb (by simp)
  · intro bs hbs; exact absurd hbs (by simp)
  · intro s' hs'; injection hs' with h1; injection h1 with h2; subst h2
    simp only [V.str, V.sAsStr, h]
  · intro d hd; exact absurd hd (by simp)
  all_goals first
    | exact denote_asBS_clean M _
    | simp [V.str, V.sIsCon, V.vConName, vIs, denoteB, V.knownVCons]

/-- Any `V.data` wrapper of a `Data`-denoting expression is folding-clean. -/
theorem wfFO_Vdata (M : Model) (e : SExpr) (d : Data) (h : denote M e = .Dd d) :
    WfFO M (V.data e) := by
  refine ⟨.VCon (.Data d), by simp only [V.data, denote_app1, dUn_VData, h, SVal.asD],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn; exact absurd hn (by simp)
  · intro b hb; exact absurd hb (by simp)
  · intro bs hbs; exact absurd hbs (by simp)
  · intro s hs; exact absurd hs (by simp)
  · intro d' hd'; injection hd' with h1; injection h1 with h2; subst h2
    simp only [V.data, V.sAsData, h]
  all_goals first
    | exact denote_asBS_clean M _
    | simp [V.data, V.sIsCon, V.vConName, vIs, denoteB, V.knownVCons]

/-- Any `V.bs` wrapper of a `(Seq Int)`-denoting expression (matching `bs`'s bytes)
is folding-clean. -/
theorem wfFO_Vbs (M : Model) (e : SExpr) (bs : ByteArray) (h : denote M e = .Bytes (baToBytes bs)) :
    WfFO M (V.bs e) := by
  refine ⟨.VCon (.ByteString bs),
    by simp only [V.bs, denote_app1, dUn_VBS, h, SVal.asBytes, bytesToBA_baToBytes],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn; exact absurd hn (by simp)
  · intro b hb; exact absurd hb (by simp)
  · intro bs' hbs'; injection hbs' with h1; injection h1 with h2; subst h2
    simp only [V.bs, V.sAsBS, h]
  · intro s hs; exact absurd hs (by simp)
  · intro d hd; exact absurd hd (by simp)
  -- cleanBS: the folded projection `sAsBS (V.bs e) = e` denotes `bs`'s clean bytes.
  all_goals first
    | exact ⟨bs, by simp only [V.bs, V.sAsBS, h]⟩
    | simp [V.bs, V.sIsCon, V.vConName, vIs, denoteB, V.knownVCons]

/-- A `V.constr` expr is folding-clean: it concretizes to a `VConstr`, so every
*scalar* projector/tester is vacuous/`false` (matching `vIs _ (VConstr ..) = false`). -/
theorem wfFO_Vconstr (M : Model) (e1 e2 : SExpr) : WfFO M (V.constr e1 e2) := by
  refine ⟨.VConstr (SVal.asI (denote M e1)).toNat (SVal.asVL (denote M e2)),
    by simp only [V.constr, denote_app2]; rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn; exact absurd hn (by simp)
  · intro b hb; exact absurd hb (by simp)
  · intro bs hbs; exact absurd hbs (by simp)
  · intro s hs; exact absurd hs (by simp)
  · intro d hd; exact absurd hd (by simp)
  all_goals first
    | exact denote_asBS_clean M _
    | simp [V.constr, V.sIsCon, V.vConName, vIs, denoteB, V.knownVCons]

/-- Encoded simple constants are folding-clean. -/
theorem wfFO_simpleConst (M : Model) (c : Const) (h : simpleConst c = true) :
    WfFO M (constToSExpr c) := by
  cases c
  case Integer n => simp only [constToSExpr]; exact wfFO_Vint M (.int n) n rfl
  case Bool b => simp only [constToSExpr]; exact wfFO_Vbool M (.bool b) b rfl
  case Unit => exact wfFO_unit M
  case String s => simp only [constToSExpr]; exact wfFO_Vstr M (.str s) s rfl
  all_goals exact absurd h (by simp [simpleConst])

/-- A raw `ite` denotes to the model-decided branch. -/
theorem denote_ite_app (M : Model) (c a b : SExpr) :
    denote M (.app "ite" [c, a, b]) = if denoteB M c then denote M a else denote M b := by
  simp only [denote_app3, dTern_ite]; rfl

/-- **Merged-value well-sortedness.** A raw `ite` of two folding-clean exprs is
folding-clean: its head `"ite"` is not a known `V`-constructor, so every projector
folds to the *raw* `dUn` form, which reads the right component off the model-decided
branch's value. This is the heart of soundly pushing a `choice` through eliminators. -/
theorem wfFO_ite_app (M : Model) (c a b : SExpr) (ha : WfFO M a) (hb : WfFO M b) :
    WfFO M (.app "ite" [c, a, b]) := by
  obtain ⟨va, hra⟩ := ha
  obtain ⟨vb, hrb⟩ := hb
  have hden : denote M (.app "ite" [c, a, b]) = .Vv (if denoteB M c then va else vb) := by
    rw [denote_ite_app, hra.den, hrb.den]; cases denoteB M c <;> rfl
  refine ⟨if denoteB M c then va else vb, hden, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    show denote M (V.asInt (.app "ite" [c, a, b])) = .I n
    rw [V.asInt, denote_app1, hden, hn]; rfl
  · intro x hn
    show denote M (V.asBool (.app "ite" [c, a, b])) = .B x
    rw [V.asBool, denote_app1, hden, hn]; rfl
  · intro bs hn
    show denote M (V.asBS (.app "ite" [c, a, b])) = .Bytes (baToBytes bs)
    rw [V.asBS, denote_app1, hden, hn]; rfl
  · intro s hn
    show denote M (V.asStr (.app "ite" [c, a, b])) = .Str s
    rw [V.asStr, denote_app1, hden, hn]; rfl
  · intro d hn
    show denote M (V.asData (.app "ite" [c, a, b])) = .Dd d
    rw [V.asData, denote_app1, hden, hn]; rfl
  · show denoteB M (.app "is-VInt" [.app "ite" [c, a, b]]) = vIs "VInt" (if denoteB M c then va else vb)
    rw [denoteB, denote_app1, hden]; rfl
  · show denoteB M (.app "is-VBool" [.app "ite" [c, a, b]]) = vIs "VBool" (if denoteB M c then va else vb)
    rw [denoteB, denote_app1, hden]; rfl
  · show denoteB M (.app "is-VBS" [.app "ite" [c, a, b]]) = vIs "VBS" (if denoteB M c then va else vb)
    rw [denoteB, denote_app1, hden]; rfl
  · show denoteB M (.app "is-VStr" [.app "ite" [c, a, b]]) = vIs "VStr" (if denoteB M c then va else vb)
    rw [denoteB, denote_app1, hden]; rfl
  · show denoteB M (.app "is-VData" [.app "ite" [c, a, b]]) = vIs "VData" (if denoteB M c then va else vb)
    rw [denoteB, denote_app1, hden]; rfl
  · show denoteB M (.app "is-VUnit" [.app "ite" [c, a, b]]) = vIs "VUnit" (if denoteB M c then va else vb)
    rw [denoteB, denote_app1, hden]; rfl
  · show denoteB M (.app "is-VList" [.app "ite" [c, a, b]]) = vIs "VList" (if denoteB M c then va else vb)
    rw [denoteB, denote_app1, hden]; rfl
  · show denoteB M (.app "is-VDList" [.app "ite" [c, a, b]]) = vIs "VDList" (if denoteB M c then va else vb)
    rw [denoteB, denote_app1, hden]; rfl
  · show denoteB M (.app "is-VPair" [.app "ite" [c, a, b]]) = vIs "VPair" (if denoteB M c then va else vb)
    rw [denoteB, denote_app1, hden]; rfl
  · show denoteB M (.app "is-VPairD" [.app "ite" [c, a, b]]) = vIs "VPairD" (if denoteB M c then va else vb)
    rw [denoteB, denote_app1, hden]; rfl
  · show denoteB M (.app "is-VConstr" [.app "ite" [c, a, b]]) = vIs "VConstr" (if denoteB M c then va else vb)
    rw [denoteB, denote_app1, hden]; rfl
  · exact denote_asBS_clean M _

/-- `sIte` of two folding-clean exprs is folding-clean (a literal condition folds to
one branch; a symbolic one yields a clean raw `ite`). -/
theorem wfFO_sIte (M : Model) (c a b : SExpr) (ha : WfFO M a) (hb : WfFO M b) :
    WfFO M (SExpr.sIte c a b) := by
  cases c with
  | bool bv => cases bv <;> simpa only [SExpr.sIte]
  | int _ => exact wfFO_ite_app M _ a b ha hb
  | str _ => exact wfFO_ite_app M _ a b ha hb
  | atom _ => exact wfFO_ite_app M _ a b ha hb
  | app _ _ => exact wfFO_ite_app M _ a b ha hb

/-! `WfV` is preserved by `mergeVal`: merging two folding-clean values is
folding-clean (`fo`/`fo` → a clean `sIte` via `wfFO_sIte`; kept `constr` structure →
clean fields; a deferred `choice` → both sides clean). -/
mutual
theorem wfV_mergeVal (M : Model) (c : SExpr) : ∀ (a b : SymV),
    WfV M a → WfV M b → WfV M (mergeVal c a b)
  | .fo a, .fo b, ha, hb => by simp only [mergeVal]; exact wfFO_sIte M c a b ha hb
  | .constr t1 fs1, .constr t2 fs2, ha, hb => by
      simp only [mergeVal]
      split
      · next hcond =>
          rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hcond
          obtain ⟨rfl, hlen⟩ := hcond
          exact wfVList_mergeValList M c fs1 fs2 ha hb
      · exact ⟨ha, hb⟩
  | .fo _, .lam _ _, ha, hb | .fo _, .delay _ _, ha, hb | .fo _, .constr _ _, ha, hb
  | .fo _, .builtin _ _ _, ha, hb | .fo _, .choice _ _ _, ha, hb
  | .constr _ _, .fo _, ha, hb | .constr _ _, .lam _ _, ha, hb | .constr _ _, .delay _ _, ha, hb
  | .constr _ _, .builtin _ _ _, ha, hb | .constr _ _, .choice _ _ _, ha, hb
  | .lam _ _, _, ha, hb | .delay _ _, _, ha, hb | .builtin _ _ _, _, ha, hb
  | .choice _ _ _, _, ha, hb => ⟨ha, hb⟩
termination_by a _ _ _ => sizeOf a
theorem wfVList_mergeValList (M : Model) (c : SExpr) : ∀ (as bs : List SymV),
    WfVList M as → WfVList M bs → WfVList M (mergeValList c as bs)
  | [], [], _, _ => True.intro
  | a :: as, b :: bs, ha, hb => by
      simp only [WfVList] at ha hb
      exact ⟨wfV_mergeVal M c a b ha.1 hb.1, wfVList_mergeValList M c as bs ha.2 hb.2⟩
  | [], _ :: _, _, _ => True.intro
  | _ :: _, [], _, _ => True.intro
termination_by as _ _ => sizeOf as
end

/-- The reified first-order expr of any folding-clean value is folding-clean: `.fo`
is itself; `lam`/`delay`/`builtin` reify to `VUnit`; `constr` to a `VConstr` expr;
`choice` to a clean `sIte`. (Used so the builtin reconciliation can treat any
non-erroring argument — including a `choice`, reified to `sIte` — as a clean fo-expr.) -/
theorem reify_wf (M : Model) : ∀ (v : SymV), WfV M v → WfFO M (reifyFO v).2
  | .fo _, hw => hw
  | .lam _ _, _ => wfFO_unit M
  | .delay _ _, _ => wfFO_unit M
  | .builtin _ _ _, _ => wfFO_unit M
  | .constr _ _, _ => by simp only [reifyFO]; exact wfFO_Vconstr M _ _
  | .choice c a b, hw => by
      simp only [reifyFO]
      exact wfFO_sIte M c _ _ (reify_wf M a hw.1) (reify_wf M b hw.2)
termination_by v => sizeOf v

/-- `γ` through `.fo (sIte ..)` is the model-decided branch (as a `.fo`). -/
theorem γ_fo_sIte (M : Model) (c x y : SExpr) :
    γ M (.fo (SExpr.sIte c x y)) = if denoteB M c then γ M (.fo x) else γ M (.fo y) := by
  rw [γ, denote_sIte]; cases denoteB M c <;> rfl

/-- If the reified fo-expr of a faithful value concretizes to an *integer*, so does
the value itself. (A `lam`/`delay`/`builtin` reifies to `VUnit`, a `constr` to
`VConstr` — neither an integer — so only `.fo`/`choice` survive, and `choice`
recurses on the model-decided branch.) The engine for treating a `choice` builtin
argument soundly. -/
theorem reifyγ_int (M : Model) : ∀ {v : SymV} {n : Int}, FaithfulV v →
    γ M (.fo (reifyFO v).2) = some (.VCon (.Integer n)) → γ M v = some (.VCon (.Integer n))
  | .fo _, _, _, h => h
  | .lam _ _, _, _, h | .delay _ _, _, _, h | .builtin _ _ _, _, _, h => by
      simp [reifyFO, γ, V.unit, denote_atom, dNull_VUnit] at h
  | .constr _ _, _, _, h => by simp [reifyFO, γ, V.constr, denote_app2] at h
  | .choice c a b, n, hf, h => by
      simp only [reifyFO] at h; rw [γ_fo_sIte] at h; rw [γ]
      split at h <;> rename_i hc
      · rw [if_pos hc]; exact reifyγ_int M hf.1 h
      · rw [if_neg hc]; exact reifyγ_int M hf.2 h
termination_by v => sizeOf v

theorem reifyγ_str (M : Model) : ∀ {v : SymV} {s : String}, FaithfulV v →
    γ M (.fo (reifyFO v).2) = some (.VCon (.String s)) → γ M v = some (.VCon (.String s))
  | .fo _, _, _, h => h
  | .lam _ _, _, _, h | .delay _ _, _, _, h | .builtin _ _ _, _, _, h => by
      simp [reifyFO, γ, V.unit, denote_atom, dNull_VUnit] at h
  | .constr _ _, _, _, h => by simp [reifyFO, γ, V.constr, denote_app2] at h
  | .choice c a b, s, hf, h => by
      simp only [reifyFO] at h; rw [γ_fo_sIte] at h; rw [γ]
      split at h <;> rename_i hc
      · rw [if_pos hc]; exact reifyγ_str M hf.1 h
      · rw [if_neg hc]; exact reifyγ_str M hf.2 h
termination_by v => sizeOf v

theorem reifyγ_bs (M : Model) : ∀ {v : SymV} {bs : ByteArray}, FaithfulV v →
    γ M (.fo (reifyFO v).2) = some (.VCon (.ByteString bs)) → γ M v = some (.VCon (.ByteString bs))
  | .fo _, _, _, h => h
  | .lam _ _, _, _, h | .delay _ _, _, _, h | .builtin _ _ _, _, _, h => by
      simp [reifyFO, γ, V.unit, denote_atom, dNull_VUnit] at h
  | .constr _ _, _, _, h => by simp [reifyFO, γ, V.constr, denote_app2] at h
  | .choice c a b, bs, hf, h => by
      simp only [reifyFO] at h; rw [γ_fo_sIte] at h; rw [γ]
      split at h <;> rename_i hc
      · rw [if_pos hc]; exact reifyγ_bs M hf.1 h
      · rw [if_neg hc]; exact reifyγ_bs M hf.2 h
termination_by v => sizeOf v

/-- A faithful, folding-clean builtin argument whose integer guard is `false` is an
integer (even if it is a `choice`, reified to an `sIte`): combine `reify_wf` (clean
reified expr) + `wf_int` + `reifyγ_int` (value follows the merged projection). -/
theorem argInt (M : Model) {v : SymV} {c1 : CekValue} (hf : FaithfulV v) (hw : WfV M v)
    (hv : γ M v = some c1) (hg : denoteB M (gInt (reifyFO v).2) = false) :
    ∃ n, c1 = .VCon (.Integer n) ∧ denote M (V.sAsInt (reifyFO v).2) = .I n := by
  obtain ⟨va, hr⟩ := reify_wf M v hw
  have ht : denoteB M (V.sIsCon "VInt" (reifyFO v).2) = true := by simpa [gInt, denoteB_sNot] using hg
  rw [hr.tInt] at ht
  obtain ⟨n, hn⟩ := vIs_VInt ht
  have hγfo : γ M (.fo (reifyFO v).2) = some (.VCon (.Integer n)) := by rw [γ, hr.den, hn]
  have hvv : γ M v = some (.VCon (.Integer n)) := reifyγ_int M hf hγfo
  rw [hv] at hvv
  exact ⟨n, by injection hvv, hr.pInt n hn⟩

theorem argStr (M : Model) {v : SymV} {c1 : CekValue} (hf : FaithfulV v) (hw : WfV M v)
    (hv : γ M v = some c1) (hg : denoteB M (gStr (reifyFO v).2) = false) :
    ∃ s, c1 = .VCon (.String s) ∧ denote M (V.sAsStr (reifyFO v).2) = .Str s := by
  obtain ⟨va, hr⟩ := reify_wf M v hw
  have ht : denoteB M (V.sIsCon "VStr" (reifyFO v).2) = true := by simpa [gStr, denoteB_sNot] using hg
  rw [hr.tStr] at ht
  obtain ⟨s, hn⟩ := vIs_VStr ht
  have hγfo : γ M (.fo (reifyFO v).2) = some (.VCon (.String s)) := by rw [γ, hr.den, hn]
  have hvv : γ M v = some (.VCon (.String s)) := reifyγ_str M hf hγfo
  rw [hv] at hvv
  exact ⟨s, by injection hvv, hr.pStr s hn⟩

theorem argBS (M : Model) {v : SymV} {c1 : CekValue} (hf : FaithfulV v) (hw : WfV M v)
    (hv : γ M v = some c1) (hg : denoteB M (gBS (reifyFO v).2) = false) :
    ∃ bs, c1 = .VCon (.ByteString bs) ∧ denote M (V.sAsBS (reifyFO v).2) = .Bytes (baToBytes bs) := by
  obtain ⟨va, hr⟩ := reify_wf M v hw
  have ht : denoteB M (V.sIsCon "VBS" (reifyFO v).2) = true := by simpa [gBS, denoteB_sNot] using hg
  rw [hr.tBS] at ht
  obtain ⟨bs, hn⟩ := vIs_VBS ht
  have hγfo : γ M (.fo (reifyFO v).2) = some (.VCon (.ByteString bs)) := by rw [γ, hr.den, hn]
  have hvv : γ M v = some (.VCon (.ByteString bs)) := reifyγ_bs M hf hγfo
  rw [hv] at hvv
  exact ⟨bs, by injection hvv, hr.pBS bs hn⟩

/-- The reified value's non-first-order flag is `false` for any value concretizing
to a `VCon` (`lam`/etc. give a non-`VCon`, `constr` a `VConstr`; a `choice` follows
the model-decided branch). Used in the builtin *error* arms with `choice` arguments. -/
theorem nf_false_of_VCon (M : Model) : ∀ {v : SymV} {c : Const}, FaithfulV v →
    γ M v = some (.VCon c) → denoteB M (reifyFO v).1 = false
  | .fo _, _, _, _ => by simp [reifyFO, denoteB_bool]
  | .lam _ _, _, _, h | .delay _ _, _, _, h | .builtin _ _ _, _, _, h => by
      rw [γ] at h; split at h <;> simp_all
  | .constr _ _, _, _, h => by rw [γ] at h; split at h <;> simp_all
  | .choice c' a b, _, hf, h => by
      rw [γ] at h; simp only [reifyFO]; rw [denoteB_sIte]
      split at h <;> rename_i hc
      · rw [if_pos hc]; exact nf_false_of_VCon M hf.1 h
      · rw [if_neg hc]; exact nf_false_of_VCon M hf.2 h
termination_by v => sizeOf v

/-- Converse correspondence: if a value concretizes to an integer, so does its
reified fo-expr. (For the error arms: an int-valued `choice` arg has `false` guards.) -/
theorem reifyγ_int_rev (M : Model) : ∀ {v : SymV} {n : Int}, FaithfulV v →
    γ M v = some (.VCon (.Integer n)) → γ M (.fo (reifyFO v).2) = some (.VCon (.Integer n))
  | .fo _, _, _, h => h
  | .lam _ _, _, _, h | .delay _ _, _, _, h | .builtin _ _ _, _, _, h => by
      rw [γ] at h; split at h <;> simp_all
  | .constr _ _, _, _, h => by rw [γ] at h; split at h <;> simp_all
  | .choice c a b, n, hf, h => by
      rw [γ] at h; simp only [reifyFO]; rw [γ_fo_sIte]
      split at h <;> rename_i hc
      · rw [if_pos hc]; exact reifyγ_int_rev M hf.1 h
      · rw [if_neg hc]; exact reifyγ_int_rev M hf.2 h
termination_by v => sizeOf v

theorem reifyγ_str_rev (M : Model) : ∀ {v : SymV} {s : String}, FaithfulV v →
    γ M v = some (.VCon (.String s)) → γ M (.fo (reifyFO v).2) = some (.VCon (.String s))
  | .fo _, _, _, h => h
  | .lam _ _, _, _, h | .delay _ _, _, _, h | .builtin _ _ _, _, _, h => by
      rw [γ] at h; split at h <;> simp_all
  | .constr _ _, _, _, h => by rw [γ] at h; split at h <;> simp_all
  | .choice c a b, s, hf, h => by
      rw [γ] at h; simp only [reifyFO]; rw [γ_fo_sIte]
      split at h <;> rename_i hc
      · rw [if_pos hc]; exact reifyγ_str_rev M hf.1 h
      · rw [if_neg hc]; exact reifyγ_str_rev M hf.2 h
termination_by v => sizeOf v

theorem reifyγ_bs_rev (M : Model) : ∀ {v : SymV} {bs : ByteArray}, FaithfulV v →
    γ M v = some (.VCon (.ByteString bs)) → γ M (.fo (reifyFO v).2) = some (.VCon (.ByteString bs))
  | .fo _, _, _, h => h
  | .lam _ _, _, _, h | .delay _ _, _, _, h | .builtin _ _ _, _, _, h => by
      rw [γ] at h; split at h <;> simp_all
  | .constr _ _, _, _, h => by rw [γ] at h; split at h <;> simp_all
  | .choice c a b, bs, hf, h => by
      rw [γ] at h; simp only [reifyFO]; rw [γ_fo_sIte]
      split at h <;> rename_i hc
      · rw [if_pos hc]; exact reifyγ_bs_rev M hf.1 h
      · rw [if_neg hc]; exact reifyγ_bs_rev M hf.2 h
termination_by v => sizeOf v

/-- `WfV` lookup: a folding-clean environment yields folding-clean values. -/
theorem symLookup_wf (M : Model) : ∀ (ρs : SymEnv) (k : Nat) (v : SymV),
    WfVList M ρs → symLookup ρs k = some v → WfV M v
  | [], _, _, _, h => by simp [symLookup] at h
  | _ :: _, 0, _, _, h => by simp [symLookup] at h
  | w :: _, 1, v, hρ, h => by
      have hw : w = v := by simpa [symLookup] using h
      have h1 : WfV M w := by have := hρ; simp only [WfVList] at this; exact this.1
      rw [hw] at h1; exact h1
  | _ :: rest, k + 2, v, hρ, h => by
      have hr : WfVList M rest := by have := hρ; simp only [WfVList] at this; exact this.2
      exact symLookup_wf M rest (k + 1) v hr (by simpa [symLookup] using h)

/-- `Op.add` always denotes to an integer (the SMT `+` is total over the `Int` sort). -/
theorem denote_Opadd (M : Model) (x y : SExpr) :
    denote M (Op.add x y) = .I (SVal.asI (denote M x) + SVal.asI (denote M y)) := by
  simp only [Op.add, denote_app2]; rfl

theorem denote_Opsub (M : Model) (x y : SExpr) :
    denote M (Op.sub x y) = .I (SVal.asI (denote M x) - SVal.asI (denote M y)) := by
  simp only [Op.sub, denote_app2]; rfl

theorem denote_Opmul (M : Model) (x y : SExpr) :
    denote M (Op.mul x y) = .I (SVal.asI (denote M x) * SVal.asI (denote M y)) := by
  simp only [Op.mul, denote_app2]; rfl

theorem denote_Oplt (M : Model) (x y : SExpr) :
    denote M (Op.lt x y) = .B (decide (SVal.asI (denote M x) < SVal.asI (denote M y))) := by
  simp only [Op.lt, denote_app2]; rfl

theorem denote_Ople (M : Model) (x y : SExpr) :
    denote M (Op.le x y) = .B (decide (SVal.asI (denote M x) ≤ SVal.asI (denote M y))) := by
  simp only [Op.le, denote_app2]; rfl

/-- `sEq` always denotes to a boolean (whether or not it constant-folds). -/
theorem denote_sEq (M : Model) (x y : SExpr) :
    denote M (SExpr.sEq x y) = .B (svalEq (denote M x) (denote M y)) := by
  unfold SExpr.sEq
  split
  · rename_i p q; simp [denote, svalEq]
  · rename_i p q; simp [denote, svalEq]
  · simp only [denote_app2]; rfl

/-- The SMT string append denotes to string concatenation. -/
theorem denote_strapp (M : Model) (x y : SExpr) :
    denote M (.app "str.++" [x, y]) = .Str (SVal.asStr (denote M x) ++ SVal.asStr (denote M y)) := by
  simp only [denote_app2]; rfl

/-! ### `(Seq Int)` operator denotations. -/
theorem denote_seqlen (M : Model) (x : SExpr) :
    denote M (.app "seq.len" [x]) = .I (Int.ofNat (SVal.asBytes (denote M x)).length) := by
  simp only [denote_app1]; rfl
theorem denote_sequnit (M : Model) (x : SExpr) :
    denote M (.app "seq.unit" [x]) = .Bytes [SVal.asI (denote M x)] := by
  simp only [denote_app1]; rfl
theorem denote_seqapp (M : Model) (x y : SExpr) :
    denote M (.app "seq.++" [x, y]) = .Bytes (SVal.asBytes (denote M x) ++ SVal.asBytes (denote M y)) := by
  simp only [denote_app2]; rfl
theorem denote_seqnth (M : Model) (s i : SExpr) :
    denote M (.app "seq.nth" [s, i])
      = .I (((SVal.asBytes (denote M s))[(SVal.asI (denote M i)).toNat]?).getD 0) := by
  simp only [denote_app2]; rfl

/-- Membership extractor for `WfVList`. -/
theorem wfVList_mem (M : Model) : ∀ {l : List SymV} {v : SymV},
    WfVList M l → v ∈ l → WfV M v
  | [], _, _, hmem => absurd hmem (by simp)
  | w :: rest, v, hwl, hmem => by
      simp only [WfVList] at hwl
      rcases List.mem_cons.1 hmem with rfl | h
      · exact hwl.1
      · exact wfVList_mem M hwl.2 h

/-- The byte-projection of a reified folding-clean value is a genuine byte list.
For a `.fo` value this is the `cleanBS` field; for a non-`VBS` head the projection
folds through `vbsVal` (`denote_asBS_clean`); a `choice` reifies to an `sIte` whose
folds reduce to a sub-value's (recursively clean) projection. -/
theorem reifyFO_sAsBS_clean (M : Model) : ∀ (v : SymV), WfV M v →
    ∃ ba, denote M (V.sAsBS (reifyFO v).2) = .Bytes (baToBytes ba)
  | .fo e, hw => by obtain ⟨va, hr⟩ := hw; exact hr.cleanBS
  | .lam _ _, _ => denote_asBS_clean M _
  | .delay _ _, _ => denote_asBS_clean M _
  | .builtin _ _ _, _ => denote_asBS_clean M _
  | .constr _ _, _ => denote_asBS_clean M _
  | .choice c a b, hw => by
      cases c with
      | bool bv =>
          cases bv <;>
            first
              | exact reifyFO_sAsBS_clean M a hw.1
              | exact reifyFO_sAsBS_clean M b hw.2
      | int _ => exact denote_asBS_clean M _
      | str _ => exact denote_asBS_clean M _
      | atom _ => exact denote_asBS_clean M _
      | app _ _ => exact denote_asBS_clean M _
termination_by v => sizeOf v

/-- Appending two clean byte-projections yields a folding-clean `VBS` (the result
list is `baToBytes (ba₁ ++ ba₂)`). The engine behind `appendByteString`'s `WfV`. -/
theorem wfFO_append_bs (M : Model) (a b : SExpr)
    (ha : ∃ ba, denote M (V.sAsBS a) = .Bytes (baToBytes ba))
    (hb : ∃ ba, denote M (V.sAsBS b) = .Bytes (baToBytes ba)) :
    WfFO M (V.bs (Seq.append (V.sAsBS a) (V.sAsBS b))) := by
  obtain ⟨ba, hba⟩ := ha; obtain ⟨bb, hbb⟩ := hb
  refine wfFO_Vbs M _ (ba ++ bb) ?_
  show denote M (.app "seq.++" [V.sAsBS a, V.sAsBS b]) = _
  simp only [denote_seqapp, hba, hbb, SVal.asBytes, baToBytes_append]

/-- A saturated precise builtin yields a folding-clean (first-order) value. The
`WfVList` hypothesis is needed for `appendByteString`, whose `VBS` result is clean
only when its operands are. -/
theorem wfV_symSaturate (M : Model) (b : BuiltinFun) (args : List SymV)
    (h : preciseBuiltin b = true) (hwl : WfVList M args) : WfV M (symSaturate b args).val := by
  have keyA : ∀ (R : List SExpr), WfV M (symBuiltin .AddInteger R).val := fun R => by
    rcases R with _ | ⟨a, _ | ⟨b2, _ | ⟨c, t⟩⟩⟩ <;>
      first
        | exact wfFO_unit M
        | exact wfFO_Vint M _ _ (denote_Opadd M _ _)
  have keyE : ∀ (R : List SExpr), WfV M (symBuiltin .EqualsInteger R).val := fun R => by
    rcases R with _ | ⟨a, _ | ⟨b2, _ | ⟨c, t⟩⟩⟩ <;>
      first
        | exact wfFO_unit M
        | exact wfFO_Vbool M _ _ (denote_sEq M _ _)
  have keyS : ∀ (R : List SExpr), WfV M (symBuiltin .SubtractInteger R).val := fun R => by
    rcases R with _ | ⟨a, _ | ⟨b2, _ | ⟨c, t⟩⟩⟩ <;>
      first | exact wfFO_unit M | exact wfFO_Vint M _ _ (denote_Opsub M _ _)
  have keyM : ∀ (R : List SExpr), WfV M (symBuiltin .MultiplyInteger R).val := fun R => by
    rcases R with _ | ⟨a, _ | ⟨b2, _ | ⟨c, t⟩⟩⟩ <;>
      first | exact wfFO_unit M | exact wfFO_Vint M _ _ (denote_Opmul M _ _)
  have keyL : ∀ (R : List SExpr), WfV M (symBuiltin .LessThanInteger R).val := fun R => by
    rcases R with _ | ⟨a, _ | ⟨b2, _ | ⟨c, t⟩⟩⟩ <;>
      first | exact wfFO_unit M | exact wfFO_Vbool M _ _ (denote_Oplt M _ _)
  have keyLe : ∀ (R : List SExpr), WfV M (symBuiltin .LessThanEqualsInteger R).val := fun R => by
    rcases R with _ | ⟨a, _ | ⟨b2, _ | ⟨c, t⟩⟩⟩ <;>
      first | exact wfFO_unit M | exact wfFO_Vbool M _ _ (denote_Ople M _ _)
  have keyD : ∀ (R : List SExpr), WfV M (symBuiltin .DivideInteger R).val := fun R => by
    rcases R with _ | ⟨a, _ | ⟨b2, _ | ⟨c, t⟩⟩⟩ <;>
      first | exact wfFO_unit M | exact wfFO_Vint M _ _ (by simp only [denote_app2]; rfl)
  have keyMd : ∀ (R : List SExpr), WfV M (symBuiltin .ModInteger R).val := fun R => by
    rcases R with _ | ⟨a, _ | ⟨b2, _ | ⟨c, t⟩⟩⟩ <;>
      first | exact wfFO_unit M | exact wfFO_Vint M _ _ (by simp only [denote_app2]; rfl)
  have keyQ : ∀ (R : List SExpr), WfV M (symBuiltin .QuotientInteger R).val := fun R => by
    rcases R with _ | ⟨a, _ | ⟨b2, _ | ⟨c, t⟩⟩⟩ <;>
      first | exact wfFO_unit M | exact wfFO_Vint M _ _ (by simp only [denote_app2]; rfl)
  have keyR : ∀ (R : List SExpr), WfV M (symBuiltin .RemainderInteger R).val := fun R => by
    rcases R with _ | ⟨a, _ | ⟨b2, _ | ⟨c, t⟩⟩⟩ <;>
      first | exact wfFO_unit M | exact wfFO_Vint M _ _ (by simp only [denote_app2]; rfl)
  have keyEqStr : ∀ (R : List SExpr), WfV M (symBuiltin .EqualsString R).val := fun R => by
    rcases R with _ | ⟨a, _ | ⟨b2, _ | ⟨c, t⟩⟩⟩ <;>
      first | exact wfFO_unit M | exact wfFO_Vbool M _ _ (denote_sEq M _ _)
  have keyApStr : ∀ (R : List SExpr), WfV M (symBuiltin .AppendString R).val := fun R => by
    rcases R with _ | ⟨a, _ | ⟨b2, _ | ⟨c, t⟩⟩⟩ <;>
      first | exact wfFO_unit M | exact wfFO_Vstr M _ _ (denote_strapp M _ _)
  have keyEqBS : ∀ (R : List SExpr), WfV M (symBuiltin .EqualsByteString R).val := fun R => by
    rcases R with _ | ⟨a, _ | ⟨b2, _ | ⟨c, t⟩⟩⟩ <;>
      first | exact wfFO_unit M | exact wfFO_Vbool M _ _ (denote_sEq M _ _)
  have keyLen : ∀ (R : List SExpr), WfV M (symBuiltin .LengthOfByteString R).val := fun R => by
    rcases R with _ | ⟨a, _ | ⟨b2, t⟩⟩ <;>
      first | exact wfFO_unit M | exact wfFO_Vint M _ _ (denote_seqlen M _)
  have keyIdx : ∀ (R : List SExpr), WfV M (symBuiltin .IndexByteString R).val := fun R => by
    rcases R with _ | ⟨a, _ | ⟨b2, _ | ⟨c, t⟩⟩⟩ <;>
      first | exact wfFO_unit M | exact wfFO_Vint M _ _ (denote_seqnth M _ _)
  -- `AppendByteString`: its `VBS` result is clean because each operand's
  -- byte-projection is clean (`reifyFO_sAsBS_clean`, from the `WfVList`).
  have keyApBS : ∀ (R : List SExpr),
      (∀ e ∈ R, ∃ ba, denote M (V.sAsBS e) = .Bytes (baToBytes ba)) →
      WfV M (symBuiltin .AppendByteString R).val := fun R hcl => by
    rcases R with _ | ⟨a, _ | ⟨b2, _ | ⟨c, t⟩⟩⟩
    · exact wfFO_unit M
    · exact wfFO_unit M
    · exact wfFO_append_bs M a b2 (hcl a (by simp)) (hcl b2 (by simp))
    · exact wfFO_unit M
  cases b <;> first | (exfalso; revert h; decide) | skip
  case AddInteger => exact keyA _
  case SubtractInteger => exact keyS _
  case MultiplyInteger => exact keyM _
  case EqualsInteger => exact keyE _
  case LessThanInteger => exact keyL _
  case LessThanEqualsInteger => exact keyLe _
  case DivideInteger => exact keyD _
  case ModInteger => exact keyMd _
  case QuotientInteger => exact keyQ _
  case RemainderInteger => exact keyR _
  case EqualsString => exact keyEqStr _
  case AppendString => exact keyApStr _
  case EqualsByteString => exact keyEqBS _
  case LengthOfByteString => exact keyLen _
  case IndexByteString => exact keyIdx _
  case AppendByteString =>
    -- The reified argument exprs each have a clean byte-projection (from `WfVList`).
    show WfV M (symBuiltin .AppendByteString
      (List.map Prod.snd (List.map reifyFO args.reverse))).val
    refine keyApBS _ (fun e he => ?_)
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hp
    exact reifyFO_sAsBS_clean M w (wfVList_mem M hwl (List.mem_reverse.1 hw))

/-- A well-sorted alternative list, indexed, yields a well-sorted result value. -/
theorem wfVList_getElem? (M : Model) : ∀ (L : List SymR) (i : Nat) (r : SymR),
    WfVList M (L.map SymR.val) → L[i]? = some r → WfV M r.val
  | [], _, _, _, hi => by simp at hi
  | x :: xs, 0, r, h, hi => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simp only [List.map_cons, WfVList] at h
      exact h.1
  | x :: xs, i+1, r, h, hi => by
      simp only [List.getElem?_cons_succ] at hi
      simp only [List.map_cons, WfVList] at h
      exact wfVList_getElem? M xs i r h.2 hi

/-- `altOr` of a well-sorted alternative list is well-sorted. -/
theorem wfV_altOr (M : Model) (altRs : List SymR) (i : Nat)
    (h : WfVList M (altRs.map SymR.val)) : WfV M (altOr altRs i).val := by
  unfold altOr
  cases hi : altRs[i]? with
  | none => exact wfFO_unit M
  | some r => exact wfVList_getElem? M altRs i r h hi

/-- `dispatchIntFrom` over a well-sorted alternative list is well-sorted. -/
theorem wfV_dispatchIntFrom (M : Model) (tagE : SExpr) : ∀ (i : Nat) (altRs : List SymR),
    WfVList M (altRs.map SymR.val) → WfV M (dispatchIntFrom tagE i altRs).val
  | _, [], _ => by simp only [dispatchIntFrom]; exact wfFO_unit M
  | i, r :: rs, h => by
      simp only [dispatchIntFrom, symMerge]
      have h' : WfV M r.val ∧ WfVList M (rs.map SymR.val) := by
        simpa only [List.map_cons, WfVList] using h
      exact wfV_mergeVal M _ _ _ h'.1 (wfV_dispatchIntFrom M tagE (i+1) rs h'.2)

mutual
theorem wfV_symEval (M : Model) : ∀ (n : Nat) (ρs : SymEnv) (t : Term),
    FaithfulVList ρs → WfVList M ρs → Faithful t → WfV M (symEval n ρs t).val
  | 0, _, _, _, _, _ => by simp only [symEval, incR]; exact wfFO_unit M
  | _+1, ρs, .Var k, _, hwf, _ => by
      simp only [symEval]
      cases h : symLookup ρs k with
      | none => simp only [errR]; exact wfFO_unit M
      | some v => exact symLookup_wf M ρs k v hwf h
  | _+1, _, .Constant (c, _), _, _, ht => by
      simp only [symEval]; exact wfFO_simpleConst M c (by simpa [Faithful, faithfulB] using ht)
  | _+1, _, .Builtin b, _, _, _ => by simp only [symEval]; exact wfVList_nil M
  | _+1, ρs, .Lam _ body, _, hwf, _ => by simp only [symEval]; exact hwf
  | _+1, ρs, .Delay body, _, hwf, _ => by simp only [symEval]; exact hwf
  | n+1, ρs, .Apply f a, hfρ, hwf, ht => by
      have hf : faithfulB f = true ∧ faithfulB a = true := by
        have := ht; simp only [Faithful, faithfulB, Bool.and_eq_true] at this; exact this
      simp only [symEval]
      exact wfV_symApply M n (symEval n ρs f).val (symEval n ρs a).val
        (faithfulV_symEval n ρs f hfρ hf.1) (faithfulV_symEval n ρs a hfρ hf.2)
        (wfV_symEval M n ρs f hfρ hwf hf.1) (wfV_symEval M n ρs a hfρ hwf hf.2)
  | n+1, ρs, .Force t, hfρ, hwf, ht => by
      have ht' : Faithful t := by simpa [Faithful, faithfulB] using ht
      simp only [symEval]
      exact wfV_symForce M n (symEval n ρs t).val
        (faithfulV_symEval n ρs t hfρ ht') (wfV_symEval M n ρs t hfρ hwf ht')
  | n+1, ρs, .Constr tag ms, hfρ, hwf, ht => by
      have hms : faithfulBList ms = true := by simpa [Faithful, faithfulB] using ht
      simp only [symEval]
      exact wfV_symEvalList M n ρs ms hfρ hwf hms
  | n+1, ρs, .Case scrut alts, hfρ, hwf, ht => by
      have ht' : faithfulB scrut = true ∧ faithfulBList alts = true := by
        simpa only [Faithful, faithfulB, Bool.and_eq_true] using ht
      simp only [symEval]
      exact wfV_symCase M n ρs alts (symEval n ρs scrut).val hfρ hwf ht'.2
        (faithfulV_symEval n ρs scrut hfρ ht'.1)
        (wfV_symEval M n ρs scrut hfρ hwf ht'.1)
  | _+1, _, .Error, _, _, _ => by simp only [symEval, errR]; exact wfFO_unit M
termination_by n _ t => (n, sizeOf t)

theorem wfV_symApply (M : Model) : ∀ (n : Nat) (vf va : SymV),
    FaithfulV vf → FaithfulV va → WfV M vf → WfV M va → WfV M (symApply n vf va).val
  | 0, _, _, _, _, _, _ => by simp only [symApply, incR]; exact wfFO_unit M
  | n+1, .lam body env, va, hf, ha, hwf, hwa => by
      have hbody : faithfulB body = true ∧ FaithfulVList env := hf
      simp only [symApply]
      exact wfV_symEval M n (va :: env) body ⟨ha, hbody.2⟩ ⟨hwa, hwf⟩ hbody.1
  | _+1, .builtin b args ea, va, hf, _, hwf, hwa => by
      have hf' : preciseBuiltin b = true ∧ FaithfulVList args := hf
      simp only [symApply]
      cases h1 : ea.head with
      | argQ => simp only [h1, errR]; exact wfFO_unit M
      | argV =>
          cases h2 : ea.tail with
          | none => simp only [h1, h2]; exact wfV_symSaturate M b (va :: args) hf'.1 ⟨hwa, hwf⟩
          | some rest => simp only [h1, h2]; exact ⟨hwa, hwf⟩
  | n+1, .choice c x y, va, hf, ha, hwf, hwa => by
      simp only [symApply]
      exact wfV_mergeVal M c _ _
        (wfV_symApply M n x va hf.1 ha hwf.1 hwa)
        (wfV_symApply M n y va hf.2 ha hwf.2 hwa)
  | _+1, .fo _, _, _, _, _, _ => by simp only [symApply, errR]; exact wfFO_unit M
  | _+1, .delay _ _, _, _, _, _, _ => by simp only [symApply, errR]; exact wfFO_unit M
  | _+1, .constr _ _, _, _, _, _, _ => by simp only [symApply, errR]; exact wfFO_unit M
termination_by n _ _ => (n, 0)

theorem wfV_symForce (M : Model) : ∀ (n : Nat) (vt : SymV),
    FaithfulV vt → WfV M vt → WfV M (symForce n vt).val
  | 0, _, _, _ => by simp only [symForce, incR]; exact wfFO_unit M
  | n+1, .delay body env, ht, hwt => by
      have hbody : faithfulB body = true ∧ FaithfulVList env := ht
      simp only [symForce]
      exact wfV_symEval M n env body hbody.2 hwt hbody.1
  | _+1, .builtin b args ea, ht, hwt => by
      have ht' : preciseBuiltin b = true ∧ FaithfulVList args := ht
      simp only [symForce]
      cases h1 : ea.head with
      | argV => simp only [h1, errR]; exact wfFO_unit M
      | argQ =>
          cases h2 : ea.tail with
          | none => simp only [h1, h2]; exact wfV_symSaturate M b args ht'.1 hwt
          | some rest => simp only [h1, h2]; exact hwt
  | n+1, .choice c x y, ht, hwt => by
      simp only [symForce]
      exact wfV_mergeVal M c _ _
        (wfV_symForce M n x ht.1 hwt.1)
        (wfV_symForce M n y ht.2 hwt.2)
  | _+1, .fo _, _, _ => by simp only [symForce, errR]; exact wfFO_unit M
  | _+1, .lam _ _, _, _ => by simp only [symForce, errR]; exact wfFO_unit M
  | _+1, .constr _ _, _, _ => by simp only [symForce, errR]; exact wfFO_unit M
termination_by n vt => (n, sizeOf vt)
theorem wfV_symEvalList (M : Model) : ∀ (n : Nat) (ρs : SymEnv) (ms : List Term),
    FaithfulVList ρs → WfVList M ρs → faithfulBList ms = true →
    WfVList M ((symEvalList n ρs ms).map SymR.val)
  | _, _, [], _, _, _ => by simp [symEvalList, WfVList]
  | n, ρs, t :: ts, hfρ, hwf, hms => by
      have hms' : faithfulB t = true ∧ faithfulBList ts = true := by
        simpa [faithfulBList, Bool.and_eq_true] using hms
      simp only [symEvalList, List.map]
      exact ⟨wfV_symEval M n ρs t hfρ hwf hms'.1, wfV_symEvalList M n ρs ts hfρ hwf hms'.2⟩
termination_by n _ ms => (n, sizeOf ms)

theorem wfV_symApplyList (M : Model) : ∀ (n : Nat) (vf : SymV) (args : List SymV),
    FaithfulV vf → FaithfulVList args → WfV M vf → WfVList M args →
    WfV M (symApplyList n vf args).val
  | _, vf, [], _, _, hwf, _ => by simp only [symApplyList]; exact hwf
  | n, vf, a :: as, hf, ha, hwf, hwa => by
      simp only [symApplyList]
      exact wfV_symApplyList M n (symApply n vf a).val as
        (faithfulV_symApply n vf a hf ha.1) ha.2
        (wfV_symApply M n vf a hf ha.1 hwf hwa.1) hwa.2
termination_by n _ args => (n, sizeOf args)

theorem wfV_symCase (M : Model) : ∀ (n : Nat) (ρs : SymEnv) (alts : List Term) (scrut : SymV),
    FaithfulVList ρs → WfVList M ρs → faithfulBList alts = true → FaithfulV scrut → WfV M scrut →
    WfV M (symCase n ρs alts scrut).val
  | 0, _, _, _, _, _, _, _, _ => by simp only [symCase]; exact wfFO_unit M
  | m+1, ρs, alts, .constr tag fields, hfρ, hwρ, hms, hf, hwf => by
      simp only [symCase]
      cases ha : alts[tag]? with
      | none => exact wfFO_unit M
      | some alt =>
          simp only [ha]
          exact wfV_symApplyList M m (symEval m ρs alt).val fields
            (faithfulV_symEval m ρs alt hfρ (faithfulBList_get alts tag alt hms ha))
            hf
            (wfV_symEval M m ρs alt hfρ hwρ (faithfulBList_get alts tag alt hms ha))
            hwf
  | m+1, ρs, alts, .choice c x y, hfρ, hwρ, hms, hf, hwf => by
      simp only [symCase]
      exact wfV_mergeVal M c _ _
        (wfV_symCase M m ρs alts x hfρ hwρ hms hf.1 hwf.1)
        (wfV_symCase M m ρs alts y hfρ hwρ hms hf.2 hwf.2)
  | m+1, ρs, alts, .fo e, hfρ, hwρ, hms, hf, _ => by
      simp only [symCase]
      have hAR : WfVList M ((symEvalList m ρs alts).map SymR.val) :=
        wfV_symEvalList M m ρs alts hfρ hwρ hms
      have hf' : V.vConName e ≠ some "VList" ∧ V.vConName e ≠ some "VDList" ∧
                 V.vConName e ≠ some "VPair" ∧ V.vConName e ≠ some "VPairD" ∧
                 V.vConName e ≠ some "VConstr" := hf
      obtain ⟨hL, hDL, hP, hPD, _⟩ := hf'
      split <;> rename_i heq <;>
        first
          | exact wfFO_unit M
          | exact absurd heq hL
          | exact absurd heq hDL
          | exact absurd heq hP
          | exact absurd heq hPD
          | exact wfV_dispatchIntFrom M _ 0 _ hAR
          | (split <;>
              first
                | exact wfFO_unit M
                | exact wfV_altOr M _ 0 hAR
                | exact wfV_mergeVal M _ _ _
                    (wfV_altOr M _ 1 hAR) (wfV_altOr M _ 0 hAR))
  | m+1, _, _, .lam _ _, _, _, _, _, _ => by simp only [symCase]; exact wfFO_unit M
  | m+1, _, _, .delay _ _, _, _, _, _, _ => by simp only [symCase]; exact wfFO_unit M
  | m+1, _, _, .builtin _ _ _, _, _, _, _, _ => by simp only [symCase]; exact wfFO_unit M
termination_by n _ _ _ => (n, 0)
end

/-! ## Supporting lemmas for the simulation -/

/-- `denoteB` over a 3-element `sOrs` is the disjunction. -/
theorem denoteB_sOrs3 (M : Model) (a b c : SExpr) :
    denoteB M (sOrs [a, b, c]) = (denoteB M a || denoteB M b || denoteB M c) := by
  simp [sOrs, denoteB_sOr, Bool.or_assoc]

/-- `sOrs` cons (structural `foldr`, so `rfl`). -/
theorem sOrs_cons (a : SExpr) (as : List SExpr) : sOrs (a :: as) = SExpr.sOr a (sOrs as) := rfl

/-- Encoded simple constants denote back to themselves. -/
theorem denote_simpleConst (M : Model) (c : Const) (h : simpleConst c = true) :
    denote M (constToSExpr c) = .Vv (.VCon c) := by
  cases c <;> simp_all [simpleConst, constToSExpr, V.int, V.bool, V.str, V.unit,
    SVal.asI, SVal.asB, SVal.asStr]

/-- `γ` of an encoded simple constant. -/
theorem γ_const (M : Model) (c : Const) (h : simpleConst c = true) :
    γ M (.fo (constToSExpr c)) = some (.VCon c) := by
  rw [γ, denote_simpleConst M c h]

/-- Lookup in the symbolic environment matches lookup in the concretized CEK
environment (none ↔ none; some `v̂` ↔ some `γ v̂`). -/
theorem lookup_sound (M : Model) : ∀ (ρs : SymEnv) (L : List CekValue) (k : Nat),
    γList M ρs = some L →
    (symLookup ρs k = none → CekEnv.lookup (toCekEnv L) k = none) ∧
    (∀ v, symLookup ρs k = some v → ∃ cv, γ M v = some cv ∧ CekEnv.lookup (toCekEnv L) k = some cv)
  | [], L, k, hγ => by
      simp only [γList, Option.some.injEq] at hγ; subst hγ
      refine ⟨fun _ => ?_, fun v h => ?_⟩
      · cases k <;> rfl
      · simp [symLookup] at h
  | w :: rest, L, k, hγ => by
      simp only [γList] at hγ
      cases hw : γ M w with
      | none => rw [hw] at hγ; simp at hγ
      | some cv =>
        rw [hw] at hγ
        cases hL : γList M rest with
        | none => rw [hL] at hγ; simp at hγ
        | some L' =>
          rw [hL] at hγ; simp only [Option.some.injEq] at hγ; subst hγ
          match k with
          | 0 => exact ⟨fun _ => rfl, fun v h => by simp [symLookup] at h⟩
          | 1 => exact ⟨fun h => by simp [symLookup] at h,
                        fun v h => by simp only [symLookup, Option.some.injEq] at h; subst h
                                      exact ⟨cv, hw, rfl⟩⟩
          | k + 2 =>
            have ih := lookup_sound M rest L' (k + 1) hL
            refine ⟨fun h => ?_, fun v h => ?_⟩
            · have h' : symLookup rest (k + 1) = none := by simpa [symLookup] using h
              simpa [toCekEnv, CekEnv.lookup] using ih.1 h'
            · have h' : symLookup rest (k + 1) = some v := by simpa [symLookup] using h
              simpa [toCekEnv, CekEnv.lookup] using ih.2 v h'

/-! ## The realization relation and its constructors -/

/-- `r` realizes the concrete outcome `o` under `M`: when determinate and
non-erroring, `o` is `r`'s concretized value; when determinate and erroring, `o`
is `none`. -/
def RelR (M : Model) (r : SymR) (o : Option CekValue) : Prop :=
  (denoteB M r.inc = false → denoteB M r.err = false → ∃ cv, γ M r.val = some cv ∧ o = some cv) ∧
  (denoteB M r.inc = false → denoteB M r.err = true → o = none)

theorem relR_incR (M : Model) (o : Option CekValue) : RelR M incR o :=
  ⟨fun h _ => by simp [incR, denoteB_bool] at h, fun h _ => by simp [incR, denoteB_bool] at h⟩

theorem relR_errR (M : Model) {o : Option CekValue} (ho : o = none) : RelR M errR o :=
  ⟨fun _ he => by simp [errR, denoteB_bool] at he, fun _ _ => ho⟩

theorem relR_ok (M : Model) {v : SymV} {o : Option CekValue}
    (h : ∃ cv, γ M v = some cv ∧ o = some cv) : RelR M ⟨.bool false, .bool false, v⟩ o :=
  ⟨fun _ _ => h, fun _ he => by simp [denoteB_bool] at he⟩

/-! ## `γ` inversions and `applyVal`/`forceVal` on non-eliminable values -/

theorem envRel_inv {M : Model} {ρs : SymEnv} {ρ : CekEnv} (h : EnvRel M ρs ρ) :
    ∃ L, γList M ρs = some L ∧ ρ = toCekEnv L := by
  unfold EnvRel at h
  cases hg : γList M ρs with
  | none => rw [hg] at h; simp at h
  | some L => rw [hg] at h; simp only [Option.map_some, Option.some.injEq] at h; exact ⟨L, rfl, h.symm⟩

theorem γ_lam_inv {M : Model} {body env vf} (h : γ M (.lam body env) = some vf) :
    ∃ L, γList M env = some L ∧ vf = .VLam body (toCekEnv L) := by
  unfold γ at h
  cases hL : γList M env with
  | none => rw [hL] at h; simp at h
  | some L => rw [hL] at h; simp only [Option.some.injEq] at h; exact ⟨L, rfl, h.symm⟩

theorem γ_delay_inv {M : Model} {body env vt} (h : γ M (.delay body env) = some vt) :
    ∃ L, γList M env = some L ∧ vt = .VDelay body (toCekEnv L) := by
  unfold γ at h
  cases hL : γList M env with
  | none => rw [hL] at h; simp at h
  | some L => rw [hL] at h; simp only [Option.some.injEq] at h; exact ⟨L, rfl, h.symm⟩

theorem γ_fo_inv {M : Model} {e vf} (h : γ M (.fo e) = some vf) :
    (∃ c, vf = .VCon c) ∨ (∃ t l, vf = .VConstr t l) := by
  unfold γ at h
  split at h
  · injection h with h; exact Or.inl ⟨_, h.symm⟩
  · injection h with h; exact Or.inr ⟨_, _, h.symm⟩
  · exact absurd h (by simp)

theorem applyVal_VCon (n c va) : applyVal n (.VCon c) va = none := by cases n <;> simp [applyVal]
theorem applyVal_VConstr (n t l va) : applyVal n (.VConstr t l) va = none := by cases n <;> simp [applyVal]
theorem applyVal_VDelay (n b ρ va) : applyVal n (.VDelay b ρ) va = none := by cases n <;> simp [applyVal]
theorem forceVal_VCon (n c) : forceVal n (.VCon c) = none := by cases n <;> simp [forceVal]
theorem forceVal_VConstr (n t l) : forceVal n (.VConstr t l) = none := by cases n <;> simp [forceVal]
theorem forceVal_VLam (n b ρ) : forceVal n (.VLam b ρ) = none := by cases n <;> simp [forceVal]

/-! ## The saturated-builtin reconciliation `satBuiltin`

The core new obligation: `symSaturate b sargs` realizes `evalBuiltin b cargs`
whenever the symbolic args `sargs` concretize to `cargs`. `applyVal`/`forceVal`
call `evalBuiltin` exactly where `symApply`/`symForce` call `symSaturate`, so this
is what the builtin case of the simulation needs. -/

/-- A result whose indeterminate flag is literally `true` realizes anything. -/
theorem relR_of_inc_true (M : Model) {r : SymR} {o : Option CekValue}
    (h : r.inc = .bool true) : RelR M r o := by
  refine ⟨fun hinc _ => ?_, fun hinc _ => ?_⟩ <;>
    (rw [h] at hinc; simp [denoteB_bool] at hinc)

/-- `symMerge` reconciles with the model-decided branch: if each side relates to its
outcome, the merge relates to the `ite` of the outcomes. The engine for the `choice`
cases of `symApply`/`symForce`/`symCase`. -/
theorem symMerge_relR (M : Model) (c : SExpr) {r1 r2 : SymR} {o1 o2 : Option CekValue}
    (h1 : RelR M r1 o1) (h2 : RelR M r2 o2) :
    RelR M (symMerge c r1 r2) (if denoteB M c then o1 else o2) := by
  obtain ⟨h1s, h1e⟩ := h1
  obtain ⟨h2s, h2e⟩ := h2
  refine ⟨fun hinc herr => ?_, fun hinc herr => ?_⟩ <;>
    simp only [symMerge, denoteB_sIte] at hinc herr
  · rw [show (symMerge c r1 r2).val = mergeVal c r1.val r2.val from rfl, γ_mergeVal]
    cases hc : denoteB M c with
    | true => simp only [hc, if_true] at hinc herr ⊢; exact h1s hinc herr
    | false => simp only [hc, if_false] at hinc herr ⊢; exact h2s hinc herr
  · cases hc : denoteB M c with
    | true => simp only [hc, if_true] at hinc herr ⊢; exact h1e hinc herr
    | false => simp only [hc, if_false] at hinc herr ⊢; exact h2e hinc herr

/-! ## The fuel-stable simulation `SimR`

`SimR M n r g` packages the success/error correspondence (`RelR` at fuel `n`) with
**CEK-side fuel-stability**: once the symbolic result is determinate (`inc = false`),
the concrete fuel-indexed computation `g` is constant for all fuels `≥ n`. The third
component is what makes symbolic *branching* sound without any symbolic-side
fuel-determinacy (which is genuinely false for `choice`, because a `symMerge`'s `inc`
is an `ite`, never a literal). It is a statement about the *deterministic* CEK, so
equal results are literally equal — no congruence is ever needed, and the 1-fuel gap
of choice-distribution is absorbed because `g` is constant past `n`. -/
def SimR (M : Model) (n : Nat) (r : SymR) (g : Nat → Option CekValue) : Prop :=
  RelR M r (g n) ∧ (denoteB M r.inc = false → ∀ m, n ≤ m → g m = g n)

theorem simR_incR (M : Model) (n : Nat) (g : Nat → Option CekValue) : SimR M n incR g :=
  ⟨relR_incR M (g n), fun h _ _ => by simp [incR, denoteB_bool] at h⟩

/-- A definite error that is *fuel-independent* (a genuine type error: `none` at every fuel). -/
theorem simR_errR (M : Model) (n : Nat) {g : Nat → Option CekValue}
    (hg : ∀ m, g m = none) : SimR M n errR g :=
  ⟨relR_errR M (hg n), fun _ m _ => by rw [hg m, hg n]⟩

/-- A pure, fuel-stable success. -/
theorem simR_ok (M : Model) (n : Nat) {v : SymV} {g : Nat → Option CekValue} {cv : CekValue}
    (hγ : γ M v = some cv) (hgn : g n = some cv) (hstab : ∀ m, n ≤ m → g m = g n) :
    SimR M n ⟨.bool false, .bool false, v⟩ g :=
  ⟨relR_ok M ⟨cv, hγ, hgn⟩, fun _ => hstab⟩

/-- Fuel-stability lifts the simulation up one fuel level (unconditionally — vacuous when
`inc` holds, and otherwise `g` is already constant past `n`). -/
theorem simR_fuel_up (M : Model) (n : Nat) {r : SymR} {g : Nat → Option CekValue}
    (h : SimR M n r g) : SimR M (n+1) r g := by
  obtain ⟨⟨hs, he⟩, hf⟩ := h
  refine ⟨⟨fun hinc herr => ?_, fun hinc herr => ?_⟩, fun hinc m hm => ?_⟩
  · obtain ⟨cv, hγ, ho⟩ := hs hinc herr
    exact ⟨cv, hγ, by rw [hf hinc (n+1) (Nat.le_succ n)]; exact ho⟩
  · rw [hf hinc (n+1) (Nat.le_succ n)]; exact he hinc herr
  · rw [hf hinc m (Nat.le_of_succ_le hm), hf hinc (n+1) (Nat.le_succ n)]

/-- The merge of two fuel-stable simulations is a fuel-stable simulation of the
model-decided `ite` of the two computations. The engine for every `choice` case. -/
theorem symMerge_simR (M : Model) (n : Nat) (c : SExpr) {r1 r2 : SymR}
    {g1 g2 : Nat → Option CekValue} (h1 : SimR M n r1 g1) (h2 : SimR M n r2 g2) :
    SimR M n (symMerge c r1 r2) (fun k => if denoteB M c then g1 k else g2 k) := by
  obtain ⟨hrel1, hf1⟩ := h1
  obtain ⟨hrel2, hf2⟩ := h2
  refine ⟨symMerge_relR M c hrel1 hrel2, fun hinc m hm => ?_⟩
  simp only [symMerge, denoteB_sIte] at hinc
  cases hc : denoteB M c with
  | true => simp only [hc] at hinc ⊢; exact hf1 hinc m hm
  | false => simp only [hc] at hinc ⊢; exact hf2 hinc m hm

/-- When the condition is decided `true`, the merge simulates the *left* branch alone
(the right branch need not even concretize). The form used by the `choice` cases. -/
theorem symMerge_simR_left (M : Model) (n : Nat) (c : SExpr) (r1 r2 : SymR)
    {g : Nat → Option CekValue} (hc : denoteB M c = true) (h1 : SimR M n r1 g) :
    SimR M n (symMerge c r1 r2) g := by
  obtain ⟨⟨hs, he⟩, hf⟩ := h1
  refine ⟨⟨fun hinc herr => ?_, fun hinc herr => ?_⟩, fun hinc m hm => ?_⟩
  · simp only [symMerge, denoteB_sIte, hc, if_true] at hinc herr
    rw [show (symMerge c r1 r2).val = mergeVal c r1.val r2.val from rfl, γ_mergeVal]
    simp only [hc, if_true]
    exact hs hinc herr
  · simp only [symMerge, denoteB_sIte, hc, if_true] at hinc herr
    exact he hinc herr
  · simp only [symMerge, denoteB_sIte, hc, if_true] at hinc
    exact hf hinc m hm

/-- When the condition is decided `false`, the merge simulates the *right* branch alone. -/
theorem symMerge_simR_right (M : Model) (n : Nat) (c : SExpr) (r1 r2 : SymR)
    {g : Nat → Option CekValue} (hc : denoteB M c = false) (h2 : SimR M n r2 g) :
    SimR M n (symMerge c r1 r2) g := by
  obtain ⟨⟨hs, he⟩, hf⟩ := h2
  refine ⟨⟨fun hinc herr => ?_, fun hinc herr => ?_⟩, fun hinc m hm => ?_⟩
  · simp only [symMerge, denoteB_sIte, hc, if_false] at hinc herr
    rw [show (symMerge c r1 r2).val = mergeVal c r1.val r2.val from rfl, γ_mergeVal]
    simp only [hc, if_false]
    exact hs hinc herr
  · simp only [symMerge, denoteB_sIte, hc, if_false] at hinc herr
    exact he hinc herr
  · simp only [symMerge, denoteB_sIte, hc, if_false] at hinc
    exact hf hinc m hm

/-- Decompose `γList` of a two-element list. -/
theorem γList2 {M : Model} {a b : SymV} {L : List CekValue} (h : γList M [a, b] = some L) :
    ∃ ca cb, γ M a = some ca ∧ γ M b = some cb ∧ L = [ca, cb] := by
  simp only [γList] at h
  cases ha : γ M a with
  | none => rw [ha] at h; simp at h
  | some ca =>
    rw [ha] at h
    cases hb : γ M b with
    | none => rw [hb] at h; simp at h
    | some cb => rw [hb] at h; simp only [Option.some.injEq] at h; exact ⟨ca, cb, rfl, rfl, h.symm⟩

/-- The two args of a saturated binary-integer builtin, once its error condition is
ruled out, are concrete integers with clean projections. `v1` is the first-applied
operand (deeper in the reversed accumulation), `v2` the second. -/
theorem binIntClean {M : Model} {v1 v2 : SymV} {c1 c2 : CekValue}
    (hv1 : γ M v1 = some c1) (hv2 : γ M v2 = some c2)
    (hf1 : FaithfulV v1) (hf2 : FaithfulV v2) (hw1 : WfV M v1) (hw2 : WfV M v2)
    (hnf1 : denoteB M (reifyFO v1).1 = false) (hnf2 : denoteB M (reifyFO v2).1 = false)
    (hg1 : denoteB M (gInt (reifyFO v1).2) = false) (hg2 : denoteB M (gInt (reifyFO v2).2) = false) :
    ∃ n1 n2, c1 = .VCon (.Integer n1) ∧ c2 = .VCon (.Integer n2) ∧
      denote M (V.sAsInt (reifyFO v1).2) = .I n1 ∧ denote M (V.sAsInt (reifyFO v2).2) = .I n2 := by
  obtain ⟨n1, hc1, hp1⟩ := argInt M hf1 hw1 hv1 hg1
  obtain ⟨n2, hc2, hp2⟩ := argInt M hf2 hw2 hv2 hg2
  exact ⟨n1, n2, hc1, hc2, hp1, hp2⟩

/-- A folding-clean value concretizing to an integer has a `false` integer guard. -/
theorem gInt_false_of_int {M : Model} {e : SExpr} {n : Int}
    (hw : WfFO M e) (h : γ M (.fo e) = some (.VCon (.Integer n))) :
    denoteB M (gInt e) = false := by
  have hr := wfFOR_of hw h
  simp [gInt, denoteB_sNot, hr.tInt, vIs]

/-- An integer-valued builtin argument (possibly a `choice`) has `false` non-fo and
integer-guard flags — the engine for the *error* arms with `choice` arguments. -/
theorem intArgErr (M : Model) {v : SymV} {n : Int} (hf : FaithfulV v) (hw : WfV M v)
    (hv : γ M v = some (.VCon (.Integer n))) :
    denoteB M (reifyFO v).1 = false ∧ denoteB M (gInt (reifyFO v).2) = false :=
  ⟨nf_false_of_VCon M hf hv, gInt_false_of_int (reify_wf M v hw) (reifyγ_int_rev M hf hv)⟩

/-- The success arm of a binary-integer `evalBuiltin` spec fires only when both args
are concrete integers; otherwise the match is `none`. -/
theorem match2_int_none {α} (c2 c1 : CekValue) (F : Int → Int → α)
    (h : (∀ y, c2 ≠ .VCon (.Integer y)) ∨ (∀ x, c1 ≠ .VCon (.Integer x))) :
    (match [c2, c1] with
      | [.VCon (.Integer y), .VCon (.Integer x)] => some (F y x)
      | _ => none) = none := by
  rcases h with h | h
  · cases c2 with
    | VCon cc2 => cases cc2 <;> first | rfl | (exact absurd rfl (h _))
    | _ => rfl
  · cases c2 with
    | VCon cc2 =>
        cases cc2 <;> (try rfl) <;>
          (cases c1 with
           | VCon cc1 => cases cc1 <;> first | rfl | (exact absurd rfl (h _))
           | _ => rfl)
    | _ => rfl

/-- A binary integer builtin applied to ≠2 args is indeterminate (so any wrong arg
count realizes anything). The `[a,b]` arm fires only for exactly two args. -/
theorem symBuiltin_AddInteger_inc_ne2 (R : List SExpr) (h : R.length ≠ 2) :
    (symBuiltin .AddInteger R).inc = .bool true := by
  rcases R with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · rfl
  · rfl
  · exact absurd rfl h
  · rfl

theorem symBuiltin_EqualsInteger_inc_ne2 (R : List SExpr) (h : R.length ≠ 2) :
    (symBuiltin .EqualsInteger R).inc = .bool true := by
  rcases R with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · rfl
  · rfl
  · exact absurd rfl h
  · rfl

theorem symBuiltin_SubtractInteger_inc_ne2 (R : List SExpr) (h : R.length ≠ 2) :
    (symBuiltin .SubtractInteger R).inc = .bool true := by
  rcases R with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> first | rfl | exact absurd rfl h

theorem symBuiltin_MultiplyInteger_inc_ne2 (R : List SExpr) (h : R.length ≠ 2) :
    (symBuiltin .MultiplyInteger R).inc = .bool true := by
  rcases R with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> first | rfl | exact absurd rfl h

theorem symBuiltin_LessThanInteger_inc_ne2 (R : List SExpr) (h : R.length ≠ 2) :
    (symBuiltin .LessThanInteger R).inc = .bool true := by
  rcases R with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> first | rfl | exact absurd rfl h

theorem symBuiltin_LessThanEqualsInteger_inc_ne2 (R : List SExpr) (h : R.length ≠ 2) :
    (symBuiltin .LessThanEqualsInteger R).inc = .bool true := by
  rcases R with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> first | rfl | exact absurd rfl h

theorem symBuiltin_DivideInteger_inc_ne2 (R : List SExpr) (h : R.length ≠ 2) :
    (symBuiltin .DivideInteger R).inc = .bool true := by
  rcases R with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> first | rfl | exact absurd rfl h

theorem symBuiltin_ModInteger_inc_ne2 (R : List SExpr) (h : R.length ≠ 2) :
    (symBuiltin .ModInteger R).inc = .bool true := by
  rcases R with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> first | rfl | exact absurd rfl h

theorem symBuiltin_QuotientInteger_inc_ne2 (R : List SExpr) (h : R.length ≠ 2) :
    (symBuiltin .QuotientInteger R).inc = .bool true := by
  rcases R with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> first | rfl | exact absurd rfl h

theorem symBuiltin_RemainderInteger_inc_ne2 (R : List SExpr) (h : R.length ≠ 2) :
    (symBuiltin .RemainderInteger R).inc = .bool true := by
  rcases R with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> first | rfl | exact absurd rfl h

/-- **Generic binary-integer reconciliation.** A saturated binary builtin `b` whose
two args must be integers realizes `evalBuiltin b`, given: the symbolic/concrete
result builders `valE`/`cv`, the (`rfl`) `symSaturate` value/error reductions, the
`inc = true`-on-wrong-arity fact, the `γ`-of-result agreement, and the spec axiom.
Every binary Integer builtin is then a one-line application. -/
theorem satBin (M : Model) (b : BuiltinFun) (sargs : List SymV) (cargs : List CekValue)
    (hγ : γList M sargs = some cargs) (hf : FaithfulVList sargs) (hwf : WfVList M sargs)
    (valE : SExpr → SExpr → SExpr) (cv : Int → Int → CekValue)
    (hsatval : ∀ (v2 v1 : SymV), (symSaturate b [v2, v1]).val
        = .fo (valE (V.sAsInt (reifyFO v1).2) (V.sAsInt (reifyFO v2).2)))
    (hsaterr : ∀ (v2 v1 : SymV), (symSaturate b [v2, v1]).err
        = SExpr.sOr (sOrs [(reifyFO v1).1, (reifyFO v2).1])
                    (SExpr.sOr (gInt (reifyFO v1).2) (gInt (reifyFO v2).2)))
    (hsatinc : ∀ (s : List SymV), s.length ≠ 2 → (symSaturate b s).inc = .bool true)
    (hden : ∀ (e1 e2 : SExpr) (n1 n2 : Int), denote M e1 = .I n1 → denote M e2 = .I n2 →
        γ M (.fo (valE e1 e2)) = some (cv n1 n2))
    (hspec : ∀ args, evalBuiltin b args
        = match args with | [.VCon (.Integer y), .VCon (.Integer x)] => some (cv x y) | _ => none) :
    RelR M (symSaturate b sargs) (evalBuiltin b cargs) := by
  rcases sargs with _ | ⟨v2, _ | ⟨v1, _ | ⟨w, rest⟩⟩⟩
  · exact relR_of_inc_true M (hsatinc [] (by simp))
  · exact relR_of_inc_true M (hsatinc [v2] (by simp))
  · obtain ⟨c2, c1, hv2, hv1, rfl⟩ := γList2 hγ
    obtain ⟨hf2, hf1, -⟩ := hf
    obtain ⟨hw2, hw1, -⟩ := hwf
    refine ⟨fun _ herr => ?_, fun _ herr => ?_⟩
    · rw [hsaterr v2 v1] at herr
      simp only [sOrs, List.foldr, denoteB_sOr, denoteB_bool, Bool.or_eq_false_iff,
        Bool.or_false] at herr
      obtain ⟨⟨hnf1, hnf2⟩, hg1, hg2⟩ := herr
      obtain ⟨n1, n2, hc1, hc2, hp1, hp2⟩ :=
        binIntClean hv1 hv2 hf1 hf2 hw1 hw2 hnf1 hnf2 hg1 hg2
      refine ⟨cv n1 n2, ?_, ?_⟩
      · rw [hsatval v2 v1]; exact hden _ _ n1 n2 hp1 hp2
      · rw [hc1, hc2, hspec]
    · rw [hspec]
      refine match2_int_none c2 c1 (fun y x => cv x y) ?_
      by_cases h2 : ∃ y, c2 = .VCon (.Integer y)
      · by_cases h1 : ∃ x, c1 = .VCon (.Integer x)
        · exfalso
          obtain ⟨y, hy⟩ := h2; obtain ⟨x, hx⟩ := h1
          obtain ⟨hnf1, hg1f⟩ := intArgErr M hf1 hw1 (hx ▸ hv1)
          obtain ⟨hnf2, hg2f⟩ := intArgErr M hf2 hw2 (hy ▸ hv2)
          rw [hsaterr] at herr
          simp [sOrs, denoteB_sOr, denoteB_bool, hnf1, hnf2, hg1f, hg2f] at herr
        · exact Or.inr (fun x hx => h1 ⟨x, hx⟩)
      · exact Or.inl (fun y hy => h2 ⟨y, hy⟩)
  · exact relR_of_inc_true M (hsatinc (v2 :: v1 :: w :: rest) (by simp))

/-- Division variant of `match2_int_none`: the success arm fires only when both args
are integers *and* the divisor is non-zero. -/
theorem match2_int_div_none {α} (c2 c1 : CekValue) (F : Int → Int → α)
    (h : (∀ y, c2 ≠ .VCon (.Integer y)) ∨ (∀ x, c1 ≠ .VCon (.Integer x)) ∨ c2 = .VCon (.Integer 0)) :
    (match [c2, c1] with
      | [.VCon (.Integer y), .VCon (.Integer x)] => if y == 0 then none else some (F x y)
      | _ => none) = none := by
  rcases h with h | h | h
  · cases c2 with
    | VCon cc2 => cases cc2 <;> first | rfl | exact absurd rfl (h _)
    | _ => rfl
  · cases c2 with
    | VCon cc2 =>
        cases cc2 <;> (try rfl) <;>
          (cases c1 with
           | VCon cc1 => cases cc1 <;> first | rfl | exact absurd rfl (h _)
           | _ => rfl)
    | _ => rfl
  · subst h
    cases c1 with
    | VCon cc1 => cases cc1 <;> simp
    | _ => rfl

/-- **Generic binary-integer division reconciliation.** Like `satBin` but the error
condition carries the extra `divisor == 0` disjunct, and the spec is a guarded
`if y == 0 then none else some …`. -/
theorem satBinDiv (M : Model) (b : BuiltinFun) (sargs : List SymV) (cargs : List CekValue)
    (hγ : γList M sargs = some cargs) (hf : FaithfulVList sargs) (hwf : WfVList M sargs)
    (opName : String) (cekOp : Int → Int → Int)
    (hsatval : ∀ (v2 v1 : SymV), (symSaturate b [v2, v1]).val
        = .fo (V.int (.app opName [V.sAsInt (reifyFO v1).2, V.sAsInt (reifyFO v2).2])))
    (hsaterr : ∀ (v2 v1 : SymV), (symSaturate b [v2, v1]).err
        = SExpr.sOr (sOrs [(reifyFO v1).1, (reifyFO v2).1])
                    (sOrs [gInt (reifyFO v1).2, gInt (reifyFO v2).2,
                           SExpr.sEq (V.sAsInt (reifyFO v2).2) (.int 0)]))
    (hsatinc : ∀ (s : List SymV), s.length ≠ 2 → (symSaturate b s).inc = .bool true)
    (hopden : ∀ (x y : SExpr),
        denote M (.app opName [x, y]) = .I (cekOp (SVal.asI (denote M x)) (SVal.asI (denote M y))))
    (hspec : ∀ args, evalBuiltin b args
        = match args with
          | [.VCon (.Integer y), .VCon (.Integer x)] =>
              if y == 0 then none else some (.VCon (.Integer (cekOp x y)))
          | _ => none) :
    RelR M (symSaturate b sargs) (evalBuiltin b cargs) := by
  rcases sargs with _ | ⟨v2, _ | ⟨v1, _ | ⟨w, rest⟩⟩⟩
  · exact relR_of_inc_true M (hsatinc [] (by simp))
  · exact relR_of_inc_true M (hsatinc [v2] (by simp))
  · obtain ⟨c2, c1, hv2, hv1, rfl⟩ := γList2 hγ
    obtain ⟨hf2, hf1, -⟩ := hf
    obtain ⟨hw2, hw1, -⟩ := hwf
    refine ⟨fun _ herr => ?_, fun _ herr => ?_⟩
    · rw [hsaterr v2 v1] at herr
      simp only [sOrs, List.foldr, denoteB_sOr, denoteB_bool, Bool.or_eq_false_iff,
        Bool.or_false] at herr
      obtain ⟨⟨hnf1, hnf2⟩, hg1, hg2, hz⟩ := herr
      obtain ⟨n1, n2, hc1, hc2, hp1, hp2⟩ :=
        binIntClean hv1 hv2 hf1 hf2 hw1 hw2 hnf1 hnf2 hg1 hg2
      have hn2 : (n2 == 0) = false := by
        have : denoteB M (SExpr.sEq (V.sAsInt (reifyFO v2).2) (.int 0)) = (n2 == 0) := by
          rw [denoteB, denote_sEq, hp2, denote_lit_int]; simp [SVal.asB, svalEq]
        rw [this] at hz; exact hz
      refine ⟨.VCon (.Integer (cekOp n1 n2)), ?_, ?_⟩
      · rw [hsatval v2 v1]
        have hden : denote M (V.int (.app opName [V.sAsInt (reifyFO v1).2, V.sAsInt (reifyFO v2).2]))
                  = .Vv (.VCon (.Integer (cekOp n1 n2))) := by
          simp only [V.int, denote_app1, dUn_VInt, hopden, hp1, hp2, SVal.asI]
        simp only [γ, hden]
      · simp [hc1, hc2, hspec, hn2]
    · rw [hspec]
      refine match2_int_div_none c2 c1 (fun x y => CekValue.VCon (.Integer (cekOp x y))) ?_
      by_cases h2 : ∃ y, c2 = .VCon (.Integer y)
      · by_cases h1 : ∃ x, c1 = .VCon (.Integer x)
        · obtain ⟨y, hy⟩ := h2; obtain ⟨x, hx⟩ := h1
          by_cases hy0 : y = 0
          · exact Or.inr (Or.inr (by rw [hy, hy0]))
          · exfalso
            obtain ⟨hnf1, hg1f⟩ := intArgErr M hf1 hw1 (hx ▸ hv1)
            obtain ⟨hnf2, hg2f⟩ := intArgErr M hf2 hw2 (hy ▸ hv2)
            obtain ⟨n2', hcn, hp2'⟩ := argInt M hf2 hw2 (hy ▸ hv2) hg2f
            have hyn : y = n2' := by injection hcn with h'; injection h'
            have hzf : denoteB M (SExpr.sEq (V.sAsInt (reifyFO v2).2) (.int 0)) = false := by
              have : denoteB M (SExpr.sEq (V.sAsInt (reifyFO v2).2) (.int 0)) = (n2' == 0) := by
                rw [denoteB, denote_sEq, hp2', denote_lit_int]; simp [SVal.asB, svalEq]
              rw [this, ← hyn]; simpa using hy0
            rw [hsaterr] at herr
            simp [sOrs, denoteB_sOr, denoteB_bool, hnf1, hnf2, hg1f, hg2f, hzf] at herr
        · exact Or.inr (Or.inl (fun x hx => h1 ⟨x, hx⟩))
      · exact Or.inl (fun y hy => h2 ⟨y, hy⟩)
  · exact relR_of_inc_true M (hsatinc (v2 :: v1 :: w :: rest) (by simp))

/-! ### String tier helpers (parallel to the integer ones) -/

theorem gStr_false_of_str {M : Model} {e : SExpr} {s : String}
    (hw : WfFO M e) (h : γ M (.fo e) = some (.VCon (.String s))) :
    denoteB M (gStr e) = false := by
  have hr := wfFOR_of hw h; simp [gStr, denoteB_sNot, hr.tStr, vIs]

theorem strArgErr (M : Model) {v : SymV} {s : String} (hf : FaithfulV v) (hw : WfV M v)
    (hv : γ M v = some (.VCon (.String s))) :
    denoteB M (reifyFO v).1 = false ∧ denoteB M (gStr (reifyFO v).2) = false :=
  ⟨nf_false_of_VCon M hf hv, gStr_false_of_str (reify_wf M v hw) (reifyγ_str_rev M hf hv)⟩

theorem binStrClean {M : Model} {v1 v2 : SymV} {c1 c2 : CekValue}
    (hv1 : γ M v1 = some c1) (hv2 : γ M v2 = some c2)
    (hf1 : FaithfulV v1) (hf2 : FaithfulV v2) (hw1 : WfV M v1) (hw2 : WfV M v2)
    (hnf1 : denoteB M (reifyFO v1).1 = false) (hnf2 : denoteB M (reifyFO v2).1 = false)
    (hg1 : denoteB M (gStr (reifyFO v1).2) = false) (hg2 : denoteB M (gStr (reifyFO v2).2) = false) :
    ∃ s1 s2, c1 = .VCon (.String s1) ∧ c2 = .VCon (.String s2) ∧
      denote M (V.sAsStr (reifyFO v1).2) = .Str s1 ∧ denote M (V.sAsStr (reifyFO v2).2) = .Str s2 := by
  obtain ⟨s1, hc1, hp1⟩ := argStr M hf1 hw1 hv1 hg1
  obtain ⟨s2, hc2, hp2⟩ := argStr M hf2 hw2 hv2 hg2
  exact ⟨s1, s2, hc1, hc2, hp1, hp2⟩

theorem match2_str_none {α} (c2 c1 : CekValue) (F : String → String → α)
    (h : (∀ y, c2 ≠ .VCon (.String y)) ∨ (∀ x, c1 ≠ .VCon (.String x))) :
    (match [c2, c1] with
      | [.VCon (.String y), .VCon (.String x)] => some (F y x)
      | _ => none) = none := by
  rcases h with h | h
  · cases c2 with
    | VCon cc2 => cases cc2 <;> first | rfl | exact absurd rfl (h _)
    | _ => rfl
  · cases c2 with
    | VCon cc2 =>
        cases cc2 <;> (try rfl) <;>
          (cases c1 with
           | VCon cc1 => cases cc1 <;> first | rfl | exact absurd rfl (h _)
           | _ => rfl)
    | _ => rfl

/-- Generic binary-**String** reconciliation (parallel to `satBin`). -/
theorem satBinStr (M : Model) (b : BuiltinFun) (sargs : List SymV) (cargs : List CekValue)
    (hγ : γList M sargs = some cargs) (hf : FaithfulVList sargs) (hwf : WfVList M sargs)
    (valE : SExpr → SExpr → SExpr) (cv : String → String → CekValue)
    (hsatval : ∀ (v2 v1 : SymV), (symSaturate b [v2, v1]).val
        = .fo (valE (V.sAsStr (reifyFO v1).2) (V.sAsStr (reifyFO v2).2)))
    (hsaterr : ∀ (v2 v1 : SymV), (symSaturate b [v2, v1]).err
        = SExpr.sOr (sOrs [(reifyFO v1).1, (reifyFO v2).1])
                    (SExpr.sOr (gStr (reifyFO v1).2) (gStr (reifyFO v2).2)))
    (hsatinc : ∀ (s : List SymV), s.length ≠ 2 → (symSaturate b s).inc = .bool true)
    (hden : ∀ (e1 e2 : SExpr) (s1 s2 : String), denote M e1 = .Str s1 → denote M e2 = .Str s2 →
        γ M (.fo (valE e1 e2)) = some (cv s1 s2))
    (hspec : ∀ args, evalBuiltin b args
        = match args with | [.VCon (.String y), .VCon (.String x)] => some (cv x y) | _ => none) :
    RelR M (symSaturate b sargs) (evalBuiltin b cargs) := by
  rcases sargs with _ | ⟨v2, _ | ⟨v1, _ | ⟨w, rest⟩⟩⟩
  · exact relR_of_inc_true M (hsatinc [] (by simp))
  · exact relR_of_inc_true M (hsatinc [v2] (by simp))
  · obtain ⟨c2, c1, hv2, hv1, rfl⟩ := γList2 hγ
    obtain ⟨hf2, hf1, -⟩ := hf
    obtain ⟨hw2, hw1, -⟩ := hwf
    refine ⟨fun _ herr => ?_, fun _ herr => ?_⟩
    · rw [hsaterr v2 v1] at herr
      simp only [sOrs, List.foldr, denoteB_sOr, denoteB_bool, Bool.or_eq_false_iff,
        Bool.or_false] at herr
      obtain ⟨⟨hnf1, hnf2⟩, hg1, hg2⟩ := herr
      obtain ⟨s1, s2, hc1, hc2, hp1, hp2⟩ :=
        binStrClean hv1 hv2 hf1 hf2 hw1 hw2 hnf1 hnf2 hg1 hg2
      refine ⟨cv s1 s2, ?_, ?_⟩
      · rw [hsatval v2 v1]; exact hden _ _ s1 s2 hp1 hp2
      · rw [hc1, hc2, hspec]
    · rw [hspec]
      refine match2_str_none c2 c1 (fun y x => cv x y) ?_
      by_cases h2 : ∃ y, c2 = .VCon (.String y)
      · by_cases h1 : ∃ x, c1 = .VCon (.String x)
        · exfalso
          obtain ⟨y, hy⟩ := h2; obtain ⟨x, hx⟩ := h1
          obtain ⟨hnf1, hg1f⟩ := strArgErr M hf1 hw1 (hx ▸ hv1)
          obtain ⟨hnf2, hg2f⟩ := strArgErr M hf2 hw2 (hy ▸ hv2)
          rw [hsaterr] at herr
          simp [sOrs, denoteB_sOr, denoteB_bool, hnf1, hnf2, hg1f, hg2f] at herr
        · exact Or.inr (fun x hx => h1 ⟨x, hx⟩)
      · exact Or.inl (fun y hy => h2 ⟨y, hy⟩)
  · exact relR_of_inc_true M (hsatinc (v2 :: v1 :: w :: rest) (by simp))

theorem symBuiltin_EqualsString_inc_ne2 (R : List SExpr) (h : R.length ≠ 2) :
    (symBuiltin .EqualsString R).inc = .bool true := by
  rcases R with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> first | rfl | exact absurd rfl h

theorem symBuiltin_AppendString_inc_ne2 (R : List SExpr) (h : R.length ≠ 2) :
    (symBuiltin .AppendString R).inc = .bool true := by
  rcases R with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> first | rfl | exact absurd rfl h

/-! ### ByteString tier helpers (parallel to the string ones, via the
`ByteArray ↔ List Int` bridge `baToBytes`/`bytesToBA`) -/

/-- Decompose `γList` of a one-element list. -/
theorem γList1 {M : Model} {a : SymV} {L : List CekValue} (h : γList M [a] = some L) :
    ∃ ca, γ M a = some ca ∧ L = [ca] := by
  simp only [γList] at h
  cases ha : γ M a with
  | none => rw [ha] at h; simp at h
  | some ca => rw [ha] at h; simp only [Option.some.injEq] at h; exact ⟨ca, rfl, h.symm⟩

theorem gBS_false_of_bs {M : Model} {e : SExpr} {bs : ByteArray}
    (hw : WfFO M e) (h : γ M (.fo e) = some (.VCon (.ByteString bs))) :
    denoteB M (gBS e) = false := by
  have hr := wfFOR_of hw h; simp [gBS, denoteB_sNot, hr.tBS, vIs]

theorem bsArgErr (M : Model) {v : SymV} {bs : ByteArray} (hf : FaithfulV v) (hw : WfV M v)
    (hv : γ M v = some (.VCon (.ByteString bs))) :
    denoteB M (reifyFO v).1 = false ∧ denoteB M (gBS (reifyFO v).2) = false :=
  ⟨nf_false_of_VCon M hf hv, gBS_false_of_bs (reify_wf M v hw) (reifyγ_bs_rev M hf hv)⟩

theorem binBSClean {M : Model} {v1 v2 : SymV} {c1 c2 : CekValue}
    (hv1 : γ M v1 = some c1) (hv2 : γ M v2 = some c2)
    (hf1 : FaithfulV v1) (hf2 : FaithfulV v2) (hw1 : WfV M v1) (hw2 : WfV M v2)
    (hnf1 : denoteB M (reifyFO v1).1 = false) (hnf2 : denoteB M (reifyFO v2).1 = false)
    (hg1 : denoteB M (gBS (reifyFO v1).2) = false) (hg2 : denoteB M (gBS (reifyFO v2).2) = false) :
    ∃ bs1 bs2, c1 = .VCon (.ByteString bs1) ∧ c2 = .VCon (.ByteString bs2) ∧
      denote M (V.sAsBS (reifyFO v1).2) = .Bytes (baToBytes bs1) ∧
      denote M (V.sAsBS (reifyFO v2).2) = .Bytes (baToBytes bs2) := by
  obtain ⟨bs1, hc1, hp1⟩ := argBS M hf1 hw1 hv1 hg1
  obtain ⟨bs2, hc2, hp2⟩ := argBS M hf2 hw2 hv2 hg2
  exact ⟨bs1, bs2, hc1, hc2, hp1, hp2⟩

theorem unBSClean {M : Model} {v1 : SymV} {c1 : CekValue}
    (hv1 : γ M v1 = some c1) (hf1 : FaithfulV v1) (hw1 : WfV M v1)
    (hnf1 : denoteB M (reifyFO v1).1 = false) (hg1 : denoteB M (gBS (reifyFO v1).2) = false) :
    ∃ bs1, c1 = .VCon (.ByteString bs1) ∧
      denote M (V.sAsBS (reifyFO v1).2) = .Bytes (baToBytes bs1) := by
  obtain ⟨bs1, hc1, hp1⟩ := argBS M hf1 hw1 hv1 hg1
  exact ⟨bs1, hc1, hp1⟩

theorem match2_bs_none {α} (c2 c1 : CekValue) (F : ByteArray → ByteArray → α)
    (h : (∀ y, c2 ≠ .VCon (.ByteString y)) ∨ (∀ x, c1 ≠ .VCon (.ByteString x))) :
    (match [c2, c1] with
      | [.VCon (.ByteString y), .VCon (.ByteString x)] => some (F y x)
      | _ => none) = none := by
  rcases h with h | h
  · cases c2 with
    | VCon cc2 => cases cc2 <;> first | rfl | exact absurd rfl (h _)
    | _ => rfl
  · cases c2 with
    | VCon cc2 =>
        cases cc2 <;> (try rfl) <;>
          (cases c1 with
           | VCon cc1 => cases cc1 <;> first | rfl | exact absurd rfl (h _)
           | _ => rfl)
    | _ => rfl

theorem match1_bs_none {α} (c1 : CekValue) (F : ByteArray → α)
    (h : ∀ x, c1 ≠ .VCon (.ByteString x)) :
    (match [c1] with | [.VCon (.ByteString x)] => some (F x) | _ => none) = none := by
  cases c1 with
  | VCon cc1 => cases cc1 <;> first | rfl | exact absurd rfl (h _)
  | _ => rfl

/-- The `IndexByteString` success arm fires only when the args are an integer and a
bytestring *and* the index is in range; otherwise the match (or the inner guard) is
`none`. -/
theorem match2_idx_none {α} (c2 c1 : CekValue)
    (F : Int → ByteArray → α) (G : Int → ByteArray → Bool)
    (h : (∀ y, c2 ≠ .VCon (.Integer y)) ∨ (∀ x, c1 ≠ .VCon (.ByteString x)) ∨
         (∃ idx bs, c2 = .VCon (.Integer idx) ∧ c1 = .VCon (.ByteString bs) ∧ G idx bs = true)) :
    (match [c2, c1] with
      | [.VCon (.Integer idx), .VCon (.ByteString bs)] => if G idx bs then none else some (F idx bs)
      | _ => none) = none := by
  rcases h with h | h | ⟨idx, bs, h2, h1, hg⟩
  · cases c2 with
    | VCon cc2 => cases cc2 <;> first | rfl | exact absurd rfl (h _)
    | _ => rfl
  · cases c2 with
    | VCon cc2 =>
        cases cc2 <;> (try rfl) <;>
          (cases c1 with
           | VCon cc1 => cases cc1 <;> first | rfl | exact absurd rfl (h _)
           | _ => rfl)
    | _ => rfl
  · subst h2; subst h1; simp [hg]

/-- Generic binary-**ByteString** reconciliation (parallel to `satBinStr`). -/
theorem satBinBS (M : Model) (b : BuiltinFun) (sargs : List SymV) (cargs : List CekValue)
    (hγ : γList M sargs = some cargs) (hf : FaithfulVList sargs) (hwf : WfVList M sargs)
    (valE : SExpr → SExpr → SExpr) (cv : ByteArray → ByteArray → CekValue)
    (hsatval : ∀ (v2 v1 : SymV), (symSaturate b [v2, v1]).val
        = .fo (valE (V.sAsBS (reifyFO v1).2) (V.sAsBS (reifyFO v2).2)))
    (hsaterr : ∀ (v2 v1 : SymV), (symSaturate b [v2, v1]).err
        = SExpr.sOr (sOrs [(reifyFO v1).1, (reifyFO v2).1])
                    (SExpr.sOr (gBS (reifyFO v1).2) (gBS (reifyFO v2).2)))
    (hsatinc : ∀ (s : List SymV), s.length ≠ 2 → (symSaturate b s).inc = .bool true)
    (hden : ∀ (e1 e2 : SExpr) (bs1 bs2 : ByteArray),
        denote M e1 = .Bytes (baToBytes bs1) → denote M e2 = .Bytes (baToBytes bs2) →
        γ M (.fo (valE e1 e2)) = some (cv bs1 bs2))
    (hspec : ∀ args, evalBuiltin b args
        = match args with
          | [.VCon (.ByteString y), .VCon (.ByteString x)] => some (cv x y) | _ => none) :
    RelR M (symSaturate b sargs) (evalBuiltin b cargs) := by
  rcases sargs with _ | ⟨v2, _ | ⟨v1, _ | ⟨w, rest⟩⟩⟩
  · exact relR_of_inc_true M (hsatinc [] (by simp))
  · exact relR_of_inc_true M (hsatinc [v2] (by simp))
  · obtain ⟨c2, c1, hv2, hv1, rfl⟩ := γList2 hγ
    obtain ⟨hf2, hf1, -⟩ := hf
    obtain ⟨hw2, hw1, -⟩ := hwf
    refine ⟨fun _ herr => ?_, fun _ herr => ?_⟩
    · rw [hsaterr v2 v1] at herr
      simp only [sOrs, List.foldr, denoteB_sOr, denoteB_bool, Bool.or_eq_false_iff,
        Bool.or_false] at herr
      obtain ⟨⟨hnf1, hnf2⟩, hg1, hg2⟩ := herr
      obtain ⟨bs1, bs2, hc1, hc2, hp1, hp2⟩ :=
        binBSClean hv1 hv2 hf1 hf2 hw1 hw2 hnf1 hnf2 hg1 hg2
      refine ⟨cv bs1 bs2, ?_, ?_⟩
      · rw [hsatval v2 v1]; exact hden _ _ bs1 bs2 hp1 hp2
      · rw [hc1, hc2, hspec]
    · rw [hspec]
      refine match2_bs_none c2 c1 (fun y x => cv x y) ?_
      by_cases h2 : ∃ y, c2 = .VCon (.ByteString y)
      · by_cases h1 : ∃ x, c1 = .VCon (.ByteString x)
        · exfalso
          obtain ⟨y, hy⟩ := h2; obtain ⟨x, hx⟩ := h1
          obtain ⟨hnf1, hg1f⟩ := bsArgErr M hf1 hw1 (hx ▸ hv1)
          obtain ⟨hnf2, hg2f⟩ := bsArgErr M hf2 hw2 (hy ▸ hv2)
          rw [hsaterr] at herr
          simp [sOrs, denoteB_sOr, denoteB_bool, hnf1, hnf2, hg1f, hg2f] at herr
        · exact Or.inr (fun x hx => h1 ⟨x, hx⟩)
      · exact Or.inl (fun y hy => h2 ⟨y, hy⟩)
  · exact relR_of_inc_true M (hsatinc (v2 :: v1 :: w :: rest) (by simp))

/-- Generic unary-**ByteString** reconciliation (for `lengthOfByteString`). -/
theorem satUnBS (M : Model) (b : BuiltinFun) (sargs : List SymV) (cargs : List CekValue)
    (hγ : γList M sargs = some cargs) (hf : FaithfulVList sargs) (hwf : WfVList M sargs)
    (valE : SExpr → SExpr) (cv : ByteArray → CekValue)
    (hsatval : ∀ (v1 : SymV), (symSaturate b [v1]).val = .fo (valE (V.sAsBS (reifyFO v1).2)))
    (hsaterr : ∀ (v1 : SymV), (symSaturate b [v1]).err
        = SExpr.sOr (sOrs [(reifyFO v1).1]) (gBS (reifyFO v1).2))
    (hsatinc : ∀ (s : List SymV), s.length ≠ 1 → (symSaturate b s).inc = .bool true)
    (hden : ∀ (e : SExpr) (bs : ByteArray),
        denote M e = .Bytes (baToBytes bs) → γ M (.fo (valE e)) = some (cv bs))
    (hspec : ∀ args, evalBuiltin b args
        = match args with | [.VCon (.ByteString bs)] => some (cv bs) | _ => none) :
    RelR M (symSaturate b sargs) (evalBuiltin b cargs) := by
  rcases sargs with _ | ⟨v1, _ | ⟨w, rest⟩⟩
  · exact relR_of_inc_true M (hsatinc [] (by simp))
  · obtain ⟨c1, hv1, rfl⟩ := γList1 hγ
    obtain ⟨hf1, -⟩ := hf
    obtain ⟨hw1, -⟩ := hwf
    refine ⟨fun _ herr => ?_, fun _ herr => ?_⟩
    · rw [hsaterr v1] at herr
      simp only [sOrs, List.foldr, denoteB_sOr, denoteB_bool, Bool.or_false,
        Bool.or_eq_false_iff] at herr
      obtain ⟨hnf1, hg1⟩ := herr
      obtain ⟨bs, hc1, hp1⟩ := unBSClean hv1 hf1 hw1 hnf1 hg1
      refine ⟨cv bs, ?_, ?_⟩
      · rw [hsatval v1]; exact hden _ bs hp1
      · rw [hc1, hspec]
    · rw [hspec]
      refine match1_bs_none c1 cv ?_
      intro x hx
      obtain ⟨hnf1, hg1f⟩ := bsArgErr M hf1 hw1 (hx ▸ hv1)
      rw [hsaterr] at herr
      simp [sOrs, denoteB_sOr, denoteB_bool, hnf1, hg1f] at herr
  · exact relR_of_inc_true M (hsatinc (v1 :: w :: rest) (by simp))

theorem symBuiltin_EqualsByteString_inc_ne2 (R : List SExpr) (h : R.length ≠ 2) :
    (symBuiltin .EqualsByteString R).inc = .bool true := by
  rcases R with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> first | rfl | exact absurd rfl h

theorem symBuiltin_AppendByteString_inc_ne2 (R : List SExpr) (h : R.length ≠ 2) :
    (symBuiltin .AppendByteString R).inc = .bool true := by
  rcases R with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> first | rfl | exact absurd rfl h

theorem symBuiltin_IndexByteString_inc_ne2 (R : List SExpr) (h : R.length ≠ 2) :
    (symBuiltin .IndexByteString R).inc = .bool true := by
  rcases R with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> first | rfl | exact absurd rfl h

theorem symBuiltin_LengthOfByteString_inc_ne1 (R : List SExpr) (h : R.length ≠ 1) :
    (symBuiltin .LengthOfByteString R).inc = .bool true := by
  rcases R with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> first | rfl | exact absurd rfl h

/-- The two operands of `indexByteString`, once typed, are a concrete bytestring
and integer with clean projections (`v1` the bytestring, `v2` the index). -/
theorem binIdxClean {M : Model} {v1 v2 : SymV} {c1 c2 : CekValue}
    (hv1 : γ M v1 = some c1) (hv2 : γ M v2 = some c2)
    (hf1 : FaithfulV v1) (hf2 : FaithfulV v2) (hw1 : WfV M v1) (hw2 : WfV M v2)
    (hnf1 : denoteB M (reifyFO v1).1 = false) (hnf2 : denoteB M (reifyFO v2).1 = false)
    (hgbs : denoteB M (gBS (reifyFO v1).2) = false) (hgint : denoteB M (gInt (reifyFO v2).2) = false) :
    ∃ bs idx, c1 = .VCon (.ByteString bs) ∧ c2 = .VCon (.Integer idx) ∧
      denote M (V.sAsBS (reifyFO v1).2) = .Bytes (baToBytes bs) ∧
      denote M (V.sAsInt (reifyFO v2).2) = .I idx := by
  obtain ⟨bs, hc1, hpbs⟩ := argBS M hf1 hw1 hv1 hgbs
  obtain ⟨idx, hc2, hpidx⟩ := argInt M hf2 hw2 hv2 hgint
  exact ⟨bs, idx, hc1, hc2, hpbs, hpidx⟩

/-- The `Op.lt _ 0` guard denotes to `decide (idx < 0)` for a clean integer
projection. -/
theorem denoteB_lt_zero {M : Model} {e : SExpr} {idx : Int} (hp : denote M (V.sAsInt e) = .I idx) :
    denoteB M (Op.lt (V.sAsInt e) (.int 0)) = decide (idx < 0) := by
  rw [denoteB, denote_Oplt, hp, denote_lit_int]; simp [SVal.asB, SVal.asI]

/-- The `Op.le |bs| _` guard denotes to `decide (|bs| ≤ idx)` for clean projections. -/
theorem denoteB_len_le {M : Model} {e1 e2 : SExpr} {bs : ByteArray} {idx : Int}
    (hpb : denote M (V.sAsBS e1) = .Bytes (baToBytes bs)) (hpi : denote M (V.sAsInt e2) = .I idx) :
    denoteB M (Op.le (Seq.len (V.sAsBS e1)) (V.sAsInt e2)) = decide (Int.ofNat bs.size ≤ idx) := by
  rw [denoteB, denote_Ople, hpi]
  simp only [Seq.len, denote_seqlen, hpb, SVal.asB, SVal.asI, SVal.asBytes, baToBytes_length]

/-- `indexByteString` reconciliation (bespoke: mixed `BS`/`Int` operands and a
two-sided bounds guard `idx < 0 ∨ idx ≥ |bs|`). -/
theorem satIndexBS (M : Model) (sargs : List SymV) (cargs : List CekValue)
    (hγ : γList M sargs = some cargs) (hf : FaithfulVList sargs) (hwf : WfVList M sargs) :
    RelR M (symSaturate .IndexByteString sargs) (evalBuiltin .IndexByteString cargs) := by
  have hsatval : ∀ (v2 v1 : SymV), (symSaturate .IndexByteString [v2, v1]).val
      = .fo (V.int (Seq.nth (V.sAsBS (reifyFO v1).2) (V.sAsInt (reifyFO v2).2))) := fun _ _ => rfl
  have hsaterr : ∀ (v2 v1 : SymV), (symSaturate .IndexByteString [v2, v1]).err
      = SExpr.sOr (sOrs [(reifyFO v1).1, (reifyFO v2).1])
          (sOrs [gBS (reifyFO v1).2, gInt (reifyFO v2).2,
                 Op.lt (V.sAsInt (reifyFO v2).2) (.int 0),
                 Op.le (Seq.len (V.sAsBS (reifyFO v1).2)) (V.sAsInt (reifyFO v2).2)]) := fun _ _ => rfl
  have hinc : ∀ (s : List SymV), s.length ≠ 2 → (symSaturate .IndexByteString s).inc = .bool true := by
    intro s hl
    show (symBuiltin .IndexByteString (List.map Prod.snd (List.map reifyFO s.reverse))).inc = .bool true
    exact symBuiltin_IndexByteString_inc_ne2 _ (by simpa [List.length_map, List.length_reverse] using hl)
  have hspec := evalBuiltin_IndexByteString_spec
  rcases sargs with _ | ⟨v2, _ | ⟨v1, _ | ⟨w, rest⟩⟩⟩
  · exact relR_of_inc_true M (hinc [] (by simp))
  · exact relR_of_inc_true M (hinc [v2] (by simp))
  · obtain ⟨c2, c1, hv2, hv1, rfl⟩ := γList2 hγ
    obtain ⟨hf2, hf1, -⟩ := hf
    obtain ⟨hw2, hw1, -⟩ := hwf
    refine ⟨fun _ herr => ?_, fun _ herr => ?_⟩
    · rw [hsaterr v2 v1] at herr
      simp only [sOrs, List.foldr, denoteB_sOr, denoteB_bool, Bool.or_eq_false_iff,
        Bool.or_false] at herr
      obtain ⟨⟨hnf1, hnf2⟩, hgbs, hgint, hlt, hle⟩ := herr
      obtain ⟨bs, idx, hc1, hc2, hpbs, hpidx⟩ :=
        binIdxClean hv1 hv2 hf1 hf2 hw1 hw2 hnf1 hnf2 hgbs hgint
      rw [denoteB_lt_zero hpidx] at hlt
      rw [denoteB_len_le hpbs hpidx] at hle
      have h0 : (0 : Int) ≤ idx := Int.not_lt.mp (of_decide_eq_false hlt)
      have h1 : idx < Int.ofNat bs.size := Int.not_le.mp (of_decide_eq_false hle)
      have hkn : idx.toNat < bs.size :=
        (Int.toNat_lt h0).mpr (by rw [Int.ofNat_eq_natCast] at h1; exact h1)
      refine ⟨.VCon (.Integer (Int.ofNat (bs.get! idx.toNat).toNat)), ?_, ?_⟩
      · rw [hsatval v2 v1]
        simp only [γ, V.int, denote_app1, dUn_VInt, Seq.nth, denote_seqnth, hpbs, hpidx,
          SVal.asI, SVal.asBytes, idx_bridge bs idx.toNat hkn]
      · rw [hc1, hc2, hspec]
        have hg : (decide (idx < 0) || decide (idx ≥ Int.ofNat bs.size)) = false := by
          simp only [ge_iff_le, hlt, hle, Bool.or_self]
        simp only [hg, Bool.false_eq_true, if_false]
    · rw [hspec]
      refine match2_idx_none c2 c1
        (fun idx bs => CekValue.VCon (.Integer (Int.ofNat (bs.get! idx.toNat).toNat)))
        (fun idx bs => idx < 0 || idx ≥ Int.ofNat bs.size) ?_
      by_cases h2 : ∃ y, c2 = .VCon (.Integer y)
      · by_cases h1 : ∃ x, c1 = .VCon (.ByteString x)
        · obtain ⟨idx, hidx⟩ := h2; obtain ⟨bs, hbs⟩ := h1
          obtain ⟨hnf1, hgbsf⟩ := bsArgErr M hf1 hw1 (hbs ▸ hv1)
          obtain ⟨hnf2, hgintf⟩ := intArgErr M hf2 hw2 (hidx ▸ hv2)
          obtain ⟨bs2, idx2, hc1', hc2', hpbs, hpidx⟩ :=
            binIdxClean hv1 hv2 hf1 hf2 hw1 hw2 hnf1 hnf2 hgbsf hgintf
          refine Or.inr (Or.inr ⟨idx2, bs2, hc2', hc1', ?_⟩)
          rw [hsaterr v2 v1] at herr
          simp only [sOrs, List.foldr, denoteB_sOr, denoteB_bool, hnf1, hnf2, hgbsf, hgintf,
            Bool.false_or, Bool.or_false] at herr
          rw [denoteB_lt_zero hpidx, denoteB_len_le hpbs hpidx] at herr
          exact herr
        · exact Or.inr (Or.inl (fun x hx => h1 ⟨x, hx⟩))
      · exact Or.inl (fun y hy => h2 ⟨y, hy⟩)
  · exact relR_of_inc_true M (hinc (v2 :: v1 :: w :: rest) (by simp))

/-- A saturated *precise* builtin reconciles with `evalBuiltin` — each arithmetic /
comparison / division / string / bytestring builtin is a one-line
`satBin`/`satBinDiv`/`satBinStr`/`satBinBS`/`satUnBS`/`satIndexBS` application. -/
theorem satBuiltin (M : Model) (b : BuiltinFun) (sargs : List SymV) (cargs : List CekValue)
    (hγ : γList M sargs = some cargs) (hpre : preciseBuiltin b = true)
    (hf : FaithfulVList sargs) (hwf : WfVList M sargs) :
    RelR M (symSaturate b sargs) (evalBuiltin b cargs) := by
  cases b <;> first | (exfalso; revert hpre; decide) | skip
  case AddInteger =>
    exact satBin M _ sargs cargs hγ hf hwf (fun a b => V.int (Op.add a b))
      (fun n1 n2 => .VCon (.Integer (n1 + n2))) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun s hl => by
        show (symBuiltin .AddInteger (List.map Prod.snd (List.map reifyFO s.reverse))).inc = .bool true
        exact symBuiltin_AddInteger_inc_ne2 _ (by simpa [List.length_map, List.length_reverse] using hl))
      (fun e1 e2 n1 n2 h1 h2 => by
        simp only [γ, V.int, denote_app1, dUn_VInt, denote_Opadd, h1, h2, SVal.asI])
      evalBuiltin_AddInteger_spec
  case SubtractInteger =>
    exact satBin M _ sargs cargs hγ hf hwf (fun a b => V.int (Op.sub a b))
      (fun n1 n2 => .VCon (.Integer (n1 - n2))) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun s hl => by
        show (symBuiltin .SubtractInteger (List.map Prod.snd (List.map reifyFO s.reverse))).inc = .bool true
        exact symBuiltin_SubtractInteger_inc_ne2 _ (by simpa [List.length_map, List.length_reverse] using hl))
      (fun e1 e2 n1 n2 h1 h2 => by
        simp only [γ, V.int, denote_app1, dUn_VInt, denote_Opsub, h1, h2, SVal.asI])
      evalBuiltin_SubtractInteger_spec
  case MultiplyInteger =>
    exact satBin M _ sargs cargs hγ hf hwf (fun a b => V.int (Op.mul a b))
      (fun n1 n2 => .VCon (.Integer (n1 * n2))) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun s hl => by
        show (symBuiltin .MultiplyInteger (List.map Prod.snd (List.map reifyFO s.reverse))).inc = .bool true
        exact symBuiltin_MultiplyInteger_inc_ne2 _ (by simpa [List.length_map, List.length_reverse] using hl))
      (fun e1 e2 n1 n2 h1 h2 => by
        simp only [γ, V.int, denote_app1, dUn_VInt, denote_Opmul, h1, h2, SVal.asI])
      evalBuiltin_MultiplyInteger_spec
  case EqualsInteger =>
    exact satBin M _ sargs cargs hγ hf hwf (fun a b => V.bool (SExpr.sEq a b))
      (fun n1 n2 => .VCon (.Bool (n1 == n2))) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun s hl => by
        show (symBuiltin .EqualsInteger (List.map Prod.snd (List.map reifyFO s.reverse))).inc = .bool true
        exact symBuiltin_EqualsInteger_inc_ne2 _ (by simpa [List.length_map, List.length_reverse] using hl))
      (fun e1 e2 n1 n2 h1 h2 => by
        simp only [γ, V.bool, denote_app1, dUn_VBool, denote_sEq, h1, h2, SVal.asB, svalEq])
      evalBuiltin_EqualsInteger_spec
  case LessThanInteger =>
    exact satBin M _ sargs cargs hγ hf hwf (fun a b => V.bool (Op.lt a b))
      (fun n1 n2 => .VCon (.Bool (decide (n1 < n2)))) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun s hl => by
        show (symBuiltin .LessThanInteger (List.map Prod.snd (List.map reifyFO s.reverse))).inc = .bool true
        exact symBuiltin_LessThanInteger_inc_ne2 _ (by simpa [List.length_map, List.length_reverse] using hl))
      (fun e1 e2 n1 n2 h1 h2 => by
        simp only [γ, V.bool, denote_app1, dUn_VBool, denote_Oplt, h1, h2, SVal.asB, SVal.asI])
      evalBuiltin_LessThanInteger_spec
  case LessThanEqualsInteger =>
    exact satBin M _ sargs cargs hγ hf hwf (fun a b => V.bool (Op.le a b))
      (fun n1 n2 => .VCon (.Bool (decide (n1 ≤ n2)))) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun s hl => by
        show (symBuiltin .LessThanEqualsInteger (List.map Prod.snd (List.map reifyFO s.reverse))).inc = .bool true
        exact symBuiltin_LessThanEqualsInteger_inc_ne2 _ (by simpa [List.length_map, List.length_reverse] using hl))
      (fun e1 e2 n1 n2 h1 h2 => by
        simp only [γ, V.bool, denote_app1, dUn_VBool, denote_Ople, h1, h2, SVal.asB, SVal.asI])
      evalBuiltin_LessThanEqualsInteger_spec
  case DivideInteger =>
    exact satBinDiv M _ sargs cargs hγ hf hwf "moist_fdiv" Moist.CEK.haskellDiv
      (fun _ _ => rfl) (fun _ _ => rfl)
      (fun s hl => by
        show (symBuiltin .DivideInteger (List.map Prod.snd (List.map reifyFO s.reverse))).inc = .bool true
        exact symBuiltin_DivideInteger_inc_ne2 _ (by simpa [List.length_map, List.length_reverse] using hl))
      (fun x y => by simp only [denote_app2]; rfl)
      evalBuiltin_DivideInteger_spec
  case ModInteger =>
    exact satBinDiv M _ sargs cargs hγ hf hwf "moist_fmod" Moist.CEK.haskellMod
      (fun _ _ => rfl) (fun _ _ => rfl)
      (fun s hl => by
        show (symBuiltin .ModInteger (List.map Prod.snd (List.map reifyFO s.reverse))).inc = .bool true
        exact symBuiltin_ModInteger_inc_ne2 _ (by simpa [List.length_map, List.length_reverse] using hl))
      (fun x y => by simp only [denote_app2]; rfl)
      evalBuiltin_ModInteger_spec
  case QuotientInteger =>
    exact satBinDiv M _ sargs cargs hγ hf hwf "moist_qdiv" Int.tdiv
      (fun _ _ => rfl) (fun _ _ => rfl)
      (fun s hl => by
        show (symBuiltin .QuotientInteger (List.map Prod.snd (List.map reifyFO s.reverse))).inc = .bool true
        exact symBuiltin_QuotientInteger_inc_ne2 _ (by simpa [List.length_map, List.length_reverse] using hl))
      (fun x y => by simp only [denote_app2]; rfl)
      evalBuiltin_QuotientInteger_spec
  case RemainderInteger =>
    exact satBinDiv M _ sargs cargs hγ hf hwf "moist_qrem" Int.tmod
      (fun _ _ => rfl) (fun _ _ => rfl)
      (fun s hl => by
        show (symBuiltin .RemainderInteger (List.map Prod.snd (List.map reifyFO s.reverse))).inc = .bool true
        exact symBuiltin_RemainderInteger_inc_ne2 _ (by simpa [List.length_map, List.length_reverse] using hl))
      (fun x y => by simp only [denote_app2]; rfl)
      evalBuiltin_RemainderInteger_spec
  case EqualsString =>
    exact satBinStr M _ sargs cargs hγ hf hwf (fun a b => V.bool (SExpr.sEq a b))
      (fun s1 s2 => .VCon (.Bool (s1 == s2))) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun s hl => by
        show (symBuiltin .EqualsString (List.map Prod.snd (List.map reifyFO s.reverse))).inc = .bool true
        exact symBuiltin_EqualsString_inc_ne2 _ (by simpa [List.length_map, List.length_reverse] using hl))
      (fun e1 e2 s1 s2 h1 h2 => by
        simp only [γ, V.bool, denote_app1, dUn_VBool, denote_sEq, h1, h2, SVal.asB, svalEq])
      evalBuiltin_EqualsString_spec
  case AppendString =>
    exact satBinStr M _ sargs cargs hγ hf hwf (fun a b => V.str (.app "str.++" [a, b]))
      (fun s1 s2 => .VCon (.String (s1 ++ s2))) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun s hl => by
        show (symBuiltin .AppendString (List.map Prod.snd (List.map reifyFO s.reverse))).inc = .bool true
        exact symBuiltin_AppendString_inc_ne2 _ (by simpa [List.length_map, List.length_reverse] using hl))
      (fun e1 e2 s1 s2 h1 h2 => by
        simp only [γ, V.str, denote_app1, dUn_VStr, denote_strapp, h1, h2, SVal.asStr])
      evalBuiltin_AppendString_spec
  case EqualsByteString =>
    exact satBinBS M _ sargs cargs hγ hf hwf (fun a b => V.bool (SExpr.sEq a b))
      (fun bs1 bs2 => .VCon (.Bool (bs1 == bs2))) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun s hl => by
        show (symBuiltin .EqualsByteString (List.map Prod.snd (List.map reifyFO s.reverse))).inc = .bool true
        exact symBuiltin_EqualsByteString_inc_ne2 _ (by simpa [List.length_map, List.length_reverse] using hl))
      (fun e1 e2 bs1 bs2 h1 h2 => by
        simp only [γ, V.bool, denote_app1, dUn_VBool, denote_sEq, h1, h2, SVal.asB, svalEq,
          baToBytes_beq])
      evalBuiltin_EqualsByteString_spec
  case AppendByteString =>
    exact satBinBS M _ sargs cargs hγ hf hwf (fun a b => V.bs (Seq.append a b))
      (fun bs1 bs2 => .VCon (.ByteString (bs1 ++ bs2))) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun s hl => by
        show (symBuiltin .AppendByteString (List.map Prod.snd (List.map reifyFO s.reverse))).inc = .bool true
        exact symBuiltin_AppendByteString_inc_ne2 _ (by simpa [List.length_map, List.length_reverse] using hl))
      (fun e1 e2 bs1 bs2 h1 h2 => by
        simp only [γ, V.bs, denote_app1, dUn_VBS, Seq.append, denote_seqapp, h1, h2,
          SVal.asBytes, bytesToBA_append])
      evalBuiltin_AppendByteString_spec
  case LengthOfByteString =>
    exact satUnBS M _ sargs cargs hγ hf hwf (fun a => V.int (Seq.len a))
      (fun bs => .VCon (.Integer (Int.ofNat bs.size))) (fun _ => rfl) (fun _ => rfl)
      (fun s hl => by
        show (symBuiltin .LengthOfByteString (List.map Prod.snd (List.map reifyFO s.reverse))).inc = .bool true
        exact symBuiltin_LengthOfByteString_inc_ne1 _ (by simpa [List.length_map, List.length_reverse] using hl))
      (fun e bs h => by
        simp only [γ, V.int, Seq.len, denote_app1, dUn_VInt, dUn_seqlen, h, SVal.asI,
          SVal.asBytes, baToBytes_length])
      evalBuiltin_LengthOfByteString_spec
  case IndexByteString =>
    exact satIndexBS M sargs cargs hγ hf hwf

/-! ## CEK-side fuel-stability helpers (for `SimR`'s third component)

These say: once the sub-results are fuel-stable, the composite is. They are pure CEK
facts (no symbolic side), taking the sub-stabilities as hypotheses; the simulation
mutual supplies those from the IH. No congruence is ever needed — `bigEval`/`applyVal`
are deterministic, so equal results are literally equal. -/

theorem bigEval_leaf_stab {ρ : CekEnv} {t : Term} (n : Nat)
    (h : ∀ a b, bigEval (a+1) ρ t = bigEval (b+1) ρ t) :
    ∀ m, n+1 ≤ m → bigEval m ρ t = bigEval (n+1) ρ t := by
  intro m hm; obtain ⟨m', rfl⟩ : ∃ m', m = m'+1 := ⟨m-1, by omega⟩; exact h m' n

theorem applyVal_leaf_stab {vf va : CekValue} (n : Nat)
    (h : ∀ a b, applyVal (a+1) vf va = applyVal (b+1) vf va) :
    ∀ m, n+1 ≤ m → applyVal m vf va = applyVal (n+1) vf va := by
  intro m hm; obtain ⟨m', rfl⟩ : ∃ m', m = m'+1 := ⟨m-1, by omega⟩; exact h m' n

theorem forceVal_leaf_stab {vt : CekValue} (n : Nat)
    (h : ∀ a b, forceVal (a+1) vt = forceVal (b+1) vt) :
    ∀ m, n+1 ≤ m → forceVal m vt = forceVal (n+1) vt := by
  intro m hm; obtain ⟨m', rfl⟩ : ∃ m', m = m'+1 := ⟨m-1, by omega⟩; exact h m' n

theorem bigEval_apply_stab {ρ : CekEnv} {f a : Term} {n : Nat}
    (hf : ∀ m, n ≤ m → bigEval m ρ f = bigEval n ρ f)
    (ha : ∀ m, n ≤ m → bigEval m ρ a = bigEval n ρ a)
    (hap : ∀ vf va, bigEval n ρ f = some vf → bigEval n ρ a = some va →
        ∀ k, n ≤ k → applyVal k vf va = applyVal n vf va) :
    ∀ m, n+1 ≤ m → bigEval m ρ (.Apply f a) = bigEval (n+1) ρ (.Apply f a) := by
  intro m hm; obtain ⟨m', rfl⟩ : ∃ m', m = m'+1 := ⟨m-1, by omega⟩
  have hm' : n ≤ m' := by omega
  simp only [bigEval]; rw [hf m' hm', ha m' hm']
  cases hbf : bigEval n ρ f with
  | none => rfl
  | some vf => cases hba : bigEval n ρ a with
    | none => rfl
    | some va => exact hap vf va hbf hba m' hm'

theorem bigEval_force_stab {ρ : CekEnv} {t : Term} {n : Nat}
    (ht : ∀ m, n ≤ m → bigEval m ρ t = bigEval n ρ t)
    (hfo : ∀ vt, bigEval n ρ t = some vt → ∀ k, n ≤ k → forceVal k vt = forceVal n vt) :
    ∀ m, n+1 ≤ m → bigEval m ρ (.Force t) = bigEval (n+1) ρ (.Force t) := by
  intro m hm; obtain ⟨m', rfl⟩ : ∃ m', m = m'+1 := ⟨m-1, by omega⟩
  have hm' : n ≤ m' := by omega
  simp only [bigEval]; rw [ht m' hm']
  cases hbt : bigEval n ρ t with
  | none => rfl
  | some vt => exact hfo vt hbt m' hm'

theorem bigEvalList_stab {ρ : CekEnv} {n : Nat} : ∀ (ms : List Term),
    (∀ t ∈ ms, ∀ m, n ≤ m → bigEval m ρ t = bigEval n ρ t) →
    ∀ m, n ≤ m → bigEvalList m ρ ms = bigEvalList n ρ ms
  | [], _, _, _ => by simp only [bigEvalList]
  | t :: ts, h, m, hm => by
      simp only [bigEvalList]
      rw [h t (List.mem_cons.mpr (Or.inl rfl)) m hm]
      cases bigEval n ρ t with
      | none => rfl
      | some v => rw [bigEvalList_stab ts (fun t' ht' => h t' (List.mem_cons.mpr (Or.inr ht'))) m hm]

theorem bigEval_constr_stab {ρ : CekEnv} {tag : Nat} {ms : List Term} {n : Nat}
    (h : ∀ t ∈ ms, ∀ m, n ≤ m → bigEval m ρ t = bigEval n ρ t) :
    ∀ m, n+1 ≤ m → bigEval m ρ (.Constr tag ms) = bigEval (n+1) ρ (.Constr tag ms) := by
  intro m hm; obtain ⟨m', rfl⟩ : ∃ m', m = m'+1 := ⟨m-1, by omega⟩
  simp only [bigEval]; rw [bigEvalList_stab ms h m' (by omega)]

/-- The CEK `Case` dispatch on an already-evaluated scrutinee value (the body of
`bigEval`'s `Case` arm, factored out so the simulation can target it). -/
def cekCase (n : Nat) (ρ : CekEnv) (alts : List Term) : CekValue → Option CekValue
  | .VConstr tag fields =>
      match alts[tag]? with
      | some alt => match bigEval n ρ alt with
                    | some vAlt => applyValList n vAlt fields
                    | none => none
      | none => none
  | .VCon c =>
      match Moist.CEK.constToTagAndFields c with
      | some (tag, numCtors, fields) =>
          if numCtors > 0 && alts.length > numCtors then none
          else match alts[tag]? with
               | some alt => match bigEval n ρ alt with
                             | some vAlt => applyValList n vAlt fields
                             | none => none
               | none => none
      | none => none
  | _ => none

/-- `bigEval` on `Case` factors through `cekCase` once the scrutinee is evaluated. -/
theorem bigEval_Case_unfold (n : Nat) (ρ : CekEnv) (scrut : Term) (alts : List Term) :
    bigEval (n+1) ρ (.Case scrut alts)
      = match bigEval n ρ scrut with | some sv => cekCase n ρ alts sv | none => none := by
  simp only [bigEval]
  cases bigEval n ρ scrut with
  | none => rfl
  | some sv => cases sv <;> rfl

/-! ## `Case`-dispatch sim helpers (`altOr` / `dispatchIntFrom` ↔ the selected branch)

These relate the symbolic branch-selectors (`altOr` for Bool/Unit, `dispatchIntFrom`
for Integer) to picking-and-evaluating `alts[tag]`, given a per-alternative
simulation supplied by the caller (from `simEval` at the branch fuel). They are the
`.fo` (literal-constant scrutinee) heart of `simCase`. -/

theorem symEvalList_length (m : Nat) (ρs : SymEnv) : ∀ (alts : List Term),
    (symEvalList m ρs alts).length = alts.length
  | [] => by simp only [symEvalList, List.length_nil]
  | t :: ts => by simp only [symEvalList, List.length_cons]; rw [symEvalList_length m ρs ts]

theorem symEvalList_getElem? (m : Nat) (ρs : SymEnv) : ∀ (alts : List Term) (i : Nat),
    (symEvalList m ρs alts)[i]? = (alts[i]?).map (fun t => symEval m ρs t)
  | [], i => by simp [symEvalList]
  | t :: ts, 0 => by simp [symEvalList]
  | t :: ts, i+1 => by
      simp only [symEvalList, List.getElem?_cons_succ]; exact symEvalList_getElem? m ρs ts i

/-- `altOr` of the evaluated alternatives at index `i` simulates picking-and-evaluating
`alts[i]` (or `none` when out of range). -/
theorem altOr_sim (M : Model) (m : Nat) (ρs : SymEnv) (ρ : CekEnv) (alts : List Term) (i : Nat)
    (H : ∀ alt, alts[i]? = some alt → SimR M m (symEval m ρs alt) (fun k => bigEval k ρ alt)) :
    SimR M m (altOr (symEvalList m ρs alts) i)
      (fun k => match alts[i]? with | some alt => bigEval k ρ alt | none => none) := by
  unfold altOr
  rw [symEvalList_getElem? m ρs alts i]
  cases h : alts[i]? with
  | none => exact simR_errR M m (fun _ => rfl)
  | some alt => exact H alt h

/-- Integer dispatch: `dispatchIntFrom tagE start` over the evaluated alternatives
simulates picking-and-evaluating `alts[n - start]` when `start ≤ n`, else error
(`none`). At `start = 0` this is exactly `constToTagAndFields`'s Integer behaviour. -/
theorem dispatchIntFrom_sim (M : Model) (m : Nat) (ρs : SymEnv) (ρ : CekEnv)
    (tagE : SExpr) (n : Int) (hn : denote M tagE = .I n) :
    ∀ (alts : List Term) (start : Nat),
      (∀ (i : Nat) (alt : Term), alts[i]? = some alt →
        SimR M m (symEval m ρs alt) (fun k => bigEval k ρ alt)) →
      SimR M m (dispatchIntFrom tagE start (symEvalList m ρs alts))
        (fun k => if (Int.ofNat start) ≤ n then
                    (match alts[(n - (Int.ofNat start)).toNat]? with | some a => bigEval k ρ a | none => none)
                  else none)
  | [], start, _ => by
      simp only [symEvalList, dispatchIntFrom]
      refine simR_errR M m (fun k => ?_)
      simp only [List.getElem?_nil]
      split <;> rfl
  | a :: as, start, H => by
      simp only [symEvalList, dispatchIntFrom]
      have hsEq : denoteB M (SExpr.sEq tagE (.int (Int.ofNat start))) = (n == Int.ofNat start) := by
        rw [denoteB, denote_sEq, hn, denote_lit_int]; rfl
      by_cases hns : n = Int.ofNat start
      · have hc : denoteB M (SExpr.sEq tagE (.int (Int.ofNat start))) = true := by
          rw [hsEq, hns]; simp
        have hhead : SimR M m (symEval m ρs a) (fun k => bigEval k ρ a) := H 0 a rfl
        have hg : (fun k => if (Int.ofNat start) ≤ n then
                    (match (a :: as)[(n - (Int.ofNat start)).toNat]? with | some a' => bigEval k ρ a' | none => none)
                  else none)
                = (fun k => bigEval k ρ a) := by
          funext k
          have h1 : (Int.ofNat start) ≤ n := by omega
          have h2 : (n - (Int.ofNat start)).toNat = 0 := by omega
          rw [if_pos h1, h2]; rfl
        rw [hg]; exact symMerge_simR_left M m _ _ _ hc hhead
      · have hc : denoteB M (SExpr.sEq tagE (.int (Int.ofNat start))) = false := by
          rw [hsEq]; exact beq_eq_false_iff_ne.mpr hns
        have IH := dispatchIntFrom_sim M m ρs ρ tagE n hn as (start+1)
          (fun i alt h => H (i+1) alt (by rw [List.getElem?_cons_succ]; exact h))
        have hg : (fun k => if (Int.ofNat start) ≤ n then
                    (match (a :: as)[(n - (Int.ofNat start)).toNat]? with | some a' => bigEval k ρ a' | none => none)
                  else none)
                = (fun k => if (Int.ofNat (start+1)) ≤ n then
                    (match as[(n - (Int.ofNat (start+1))).toNat]? with | some a' => bigEval k ρ a' | none => none)
                  else none) := by
          funext k
          have hcs : (Int.ofNat (start+1)) = Int.ofNat start + 1 := Int.ofNat_succ start
          by_cases hle : (Int.ofNat start) ≤ n
          · have hsucc : (Int.ofNat (start+1)) ≤ n := by omega

            have hidx : (n - (Int.ofNat start)).toNat = (n - (Int.ofNat (start+1))).toNat + 1 := by omega
            rw [if_pos hle, if_pos hsucc, hidx, List.getElem?_cons_succ]
          · have hsucc : ¬ (Int.ofNat (start+1)) ≤ n := by omega
            rw [if_neg hle, if_neg hsucc]
        rw [hg]; exact symMerge_simR_right M m _ _ _ hc IH

/-- For a scrutinee whose syntactic head is none of the `Case`-able sorts, the CEK
`Case` dispatch errors (`none`): the `WfFOR` testers pin the *semantic* sort to match
the head, so `constToTagAndFields` rejects it. Justifies `symCase`'s `some _ => errR`. -/
theorem cekCase_none_of_vConName (M : Model) (k : Nat) (ρ : CekEnv) (alts : List Term)
    (e : SExpr) (sv : CekValue) (x : String) (hwfo : WfFOR M e sv) (heq : V.vConName e = some x)
    (h1 : x ≠ "VBool") (h2 : x ≠ "VUnit") (h3 : x ≠ "VInt") (h4 : x ≠ "VList")
    (h5 : x ≠ "VDList") (h6 : x ≠ "VPair") (h7 : x ≠ "VPairD") (h8 : x ≠ "VConstr") :
    cekCase k ρ alts sv = none := by
  have tst : ∀ (Y : String), denoteB M (V.sIsCon Y e) = (x == Y) := by
    intro Y; simp only [V.sIsCon, heq, denoteB_bool]
  cases sv with
  | VConstr t l =>
      have ht := hwfo.tConstr; rw [tst "VConstr"] at ht; simp only [vIs] at ht
      exact absurd (eq_of_beq ht) h8
  | VCon c0 =>
      cases c0 with
      | Bool b => have ht := hwfo.tBool; rw [tst "VBool"] at ht; simp only [vIs] at ht; exact absurd (eq_of_beq ht) h1
      | Unit => have ht := hwfo.tUnit; rw [tst "VUnit"] at ht; simp only [vIs] at ht; exact absurd (eq_of_beq ht) h2
      | Integer i => have ht := hwfo.tInt; rw [tst "VInt"] at ht; simp only [vIs] at ht; exact absurd (eq_of_beq ht) h3
      | ConstList l => have ht := hwfo.tList; rw [tst "VList"] at ht; simp only [vIs] at ht; exact absurd (eq_of_beq ht) h4
      | ConstDataList l => have ht := hwfo.tDList; rw [tst "VDList"] at ht; simp only [vIs] at ht; exact absurd (eq_of_beq ht) h5
      | Pair p => have ht := hwfo.tPair; rw [tst "VPair"] at ht; simp only [vIs] at ht; exact absurd (eq_of_beq ht) h6
      | PairData p => have ht := hwfo.tPairD; rw [tst "VPairD"] at ht; simp only [vIs] at ht; exact absurd (eq_of_beq ht) h7
      | String s => simp [cekCase, Moist.CEK.constToTagAndFields]
      | ByteString bs => simp [cekCase, Moist.CEK.constToTagAndFields]
      | Data d => simp [cekCase, Moist.CEK.constToTagAndFields]
      | ConstPairDataList l => simp [cekCase, Moist.CEK.constToTagAndFields]
      | ConstArray a => simp [cekCase, Moist.CEK.constToTagAndFields]
      | Bls12_381_G1_element => simp [cekCase, Moist.CEK.constToTagAndFields]
      | Bls12_381_G2_element => simp [cekCase, Moist.CEK.constToTagAndFields]
      | Bls12_381_MlResult => simp [cekCase, Moist.CEK.constToTagAndFields]
  | VLam _ _ => simp [cekCase]
  | VDelay _ _ => simp [cekCase]
  | VBuiltin _ _ _ => simp [cekCase]

mutual
theorem simEval : ∀ (M : Model) (n : Nat) (ρs : SymEnv) (ρ : CekEnv) (t : Term),
    EnvRel M ρs ρ → FaithfulVList ρs → WfVList M ρs → Faithful t →
    SimR M n (symEval n ρs t) (fun fuel => bigEval fuel ρ t)
  | M, 0, _, ρ, t, _, _, _, _ => by simp only [symEval]; exact simR_incR M 0 _
  | M, n+1, ρs, ρ, .Var k, hρ, _, _, _ => by
      obtain ⟨L, hL, rfl⟩ := envRel_inv hρ
      have hlk := lookup_sound M ρs L k hL
      refine ⟨?_, fun _ m hm => bigEval_leaf_stab n (fun a b => by simp only [bigEval]) m hm⟩
      simp only [symEval, bigEval]
      cases h : symLookup ρs k with
      | none => exact relR_errR M (hlk.1 h)
      | some v =>
        obtain ⟨cv, hγ, hcv⟩ := hlk.2 v h
        exact relR_ok M ⟨cv, hγ, hcv⟩
  | M, n+1, ρs, ρ, .Constant (c, bt), _, _, _, ht => by
      have hc : simpleConst c = true := by simpa [Faithful, faithfulB] using ht
      refine ⟨?_, fun _ m hm => bigEval_leaf_stab n (fun a b => by simp only [bigEval]) m hm⟩
      simp only [symEval]
      exact relR_ok M ⟨.VCon c, γ_const M c hc, by simp [bigEval]⟩
  | M, n+1, ρs, ρ, .Builtin b, _, _, _, _ => by
      refine ⟨?_, fun _ m hm => bigEval_leaf_stab n (fun a b => by simp only [bigEval]) m hm⟩
      simp only [symEval]
      exact relR_ok M ⟨.VBuiltin b [] (expectedArgs b), by simp [γ, γList], by simp [bigEval]⟩
  | M, n+1, ρs, ρ, .Lam _ body, hρ, _, _, _ => by
      obtain ⟨L, hL, rfl⟩ := envRel_inv hρ
      refine ⟨?_, fun _ m hm => bigEval_leaf_stab n (fun a b => by simp only [bigEval]) m hm⟩
      simp only [symEval]
      exact relR_ok M ⟨.VLam body (toCekEnv L), by simp [γ, hL], by simp [bigEval]⟩
  | M, n+1, ρs, ρ, .Delay body, hρ, _, _, _ => by
      obtain ⟨L, hL, rfl⟩ := envRel_inv hρ
      refine ⟨?_, fun _ m hm => bigEval_leaf_stab n (fun a b => by simp only [bigEval]) m hm⟩
      simp only [symEval]
      exact relR_ok M ⟨.VDelay body (toCekEnv L), by simp [γ, hL], by simp [bigEval]⟩
  | M, n+1, ρs, ρ, .Apply f a, hρ, henv, hwf, ht => by
      have hf : faithfulB f = true ∧ faithfulB a = true := by
        have := ht; simp only [Faithful, faithfulB, Bool.and_eq_true] at this; exact this
      obtain ⟨IHf, IHff⟩ := simEval M n ρs ρ f hρ henv hwf hf.1
      obtain ⟨IHa, IHaf⟩ := simEval M n ρs ρ a hρ henv hwf hf.2
      simp only [] at IHf IHa IHff IHaf
      have hfvf := faithfulV_symEval n ρs f henv hf.1
      have hfva := faithfulV_symEval n ρs a henv hf.2
      have hwvf := wfV_symEval M n ρs f henv hwf hf.1
      have hwva := wfV_symEval M n ρs a henv hwf hf.2
      refine ⟨?_, ?_⟩
      · simp only [symEval]
        refine ⟨fun hinc herr => ?_, fun hinc herr => ?_⟩
        · -- success
          simp only [denoteB_sOrs3, Bool.or_eq_false_iff] at hinc herr
          obtain ⟨⟨hfi, hai⟩, hpi⟩ := hinc
          obtain ⟨⟨hfe, hae⟩, hpe⟩ := herr
          obtain ⟨vf, hγf, hbf⟩ := IHf.1 hfi hfe
          obtain ⟨va, hγa, hba⟩ := IHa.1 hai hae
          obtain ⟨IHap, _⟩ := simApply M n (symEval n ρs f).val (symEval n ρs a).val vf va
            hγf hγa hfvf hfva hwvf hwva
          obtain ⟨v, hγv, hav⟩ := IHap.1 hpi hpe
          exact ⟨v, hγv, by simp only [bigEval, hbf, hba]; exact hav⟩
        · -- error
          simp only [denoteB_sOrs3, Bool.or_eq_false_iff] at hinc
          obtain ⟨⟨hfi, hai⟩, hpi⟩ := hinc
          by_cases hfe : denoteB M (symEval n ρs f).err = true
          · simp [bigEval, IHf.2 hfi hfe]
          · simp only [Bool.not_eq_true] at hfe
            obtain ⟨vf, hγf, hbf⟩ := IHf.1 hfi hfe
            by_cases hae : denoteB M (symEval n ρs a).err = true
            · simp [bigEval, hbf, IHa.2 hai hae]
            · simp only [Bool.not_eq_true] at hae
              obtain ⟨va, hγa, hba⟩ := IHa.1 hai hae
              obtain ⟨IHap, _⟩ := simApply M n (symEval n ρs f).val (symEval n ρs a).val vf va
                hγf hγa hfvf hfva hwvf hwva
              have hpe : denoteB M (symApply n (symEval n ρs f).val (symEval n ρs a).val).err = true := by
                have := herr; simp only [denoteB_sOrs3, hfe, hae, Bool.false_or, Bool.or_false] at this
                exact this
              simp only [bigEval, hbf, hba]
              exact IHap.2 hpi hpe
      · intro hinc m hm
        simp only [symEval, denoteB_sOrs3, Bool.or_eq_false_iff] at hinc
        obtain ⟨⟨hfi, hai⟩, hpi⟩ := hinc
        refine bigEval_apply_stab (fun m' hm' => IHff hfi m' hm') (fun m' hm' => IHaf hai m' hm') ?_ m hm
        intro vf va hbf hba k hk
        have hfe : denoteB M (symEval n ρs f).err = false := by
          by_cases h : denoteB M (symEval n ρs f).err = true
          · rw [IHf.2 hfi h] at hbf; exact absurd hbf (by simp)
          · simpa only [Bool.not_eq_true] using h
        have hae : denoteB M (symEval n ρs a).err = false := by
          by_cases h : denoteB M (symEval n ρs a).err = true
          · rw [IHa.2 hai h] at hba; exact absurd hba (by simp)
          · simpa only [Bool.not_eq_true] using h
        obtain ⟨vf', hγf, hbf'⟩ := IHf.1 hfi hfe
        obtain ⟨va', hγa, hba'⟩ := IHa.1 hai hae
        have hvf : vf' = vf := Option.some.inj (hbf'.symm.trans hbf)
        have hva : va' = va := Option.some.inj (hba'.symm.trans hba)
        subst hvf; subst hva
        obtain ⟨_, IHapf⟩ := simApply M n (symEval n ρs f).val (symEval n ρs a).val vf' va'
          hγf hγa hfvf hfva hwvf hwva
        exact IHapf hpi k hk
  | M, n+1, ρs, ρ, .Force t, hρ, henv, hwf, ht => by
      have ht' : Faithful t := by simpa [Faithful, faithfulB] using ht
      obtain ⟨IHt, IHtf⟩ := simEval M n ρs ρ t hρ henv hwf ht'
      simp only [] at IHt IHtf
      have hfvt := faithfulV_symEval n ρs t henv ht'
      have hwvt := wfV_symEval M n ρs t henv hwf ht'
      refine ⟨?_, ?_⟩
      · simp only [symEval]
        refine ⟨fun hinc herr => ?_, fun hinc herr => ?_⟩
        · simp only [denoteB_sOr, Bool.or_eq_false_iff] at hinc herr
          obtain ⟨hti, hfi⟩ := hinc
          obtain ⟨hte, hfe⟩ := herr
          obtain ⟨vt, hγt, hbt⟩ := IHt.1 hti hte
          obtain ⟨IHfo, _⟩ := simForce M n (symEval n ρs t).val vt hγt hfvt hwvt
          obtain ⟨v, hγv, hav⟩ := IHfo.1 hfi hfe
          exact ⟨v, hγv, by simp only [bigEval, hbt]; exact hav⟩
        · simp only [denoteB_sOr, Bool.or_eq_false_iff] at hinc
          obtain ⟨hti, hfi⟩ := hinc
          by_cases hte : denoteB M (symEval n ρs t).err = true
          · simp [bigEval, IHt.2 hti hte]
          · simp only [Bool.not_eq_true] at hte
            obtain ⟨vt, hγt, hbt⟩ := IHt.1 hti hte
            obtain ⟨IHfo, _⟩ := simForce M n (symEval n ρs t).val vt hγt hfvt hwvt
            have hfe : denoteB M (symForce n (symEval n ρs t).val).err = true := by
              have := herr; simp only [denoteB_sOr, hte, Bool.false_or] at this; exact this
            simp only [bigEval, hbt]
            exact IHfo.2 hfi hfe
      · intro hinc m hm
        simp only [symEval, denoteB_sOr, Bool.or_eq_false_iff] at hinc
        obtain ⟨hti, hfi⟩ := hinc
        refine bigEval_force_stab (fun m' hm' => IHtf hti m' hm') ?_ m hm
        intro vt hbt k hk
        have hte : denoteB M (symEval n ρs t).err = false := by
          by_cases h : denoteB M (symEval n ρs t).err = true
          · rw [IHt.2 hti h] at hbt; exact absurd hbt (by simp)
          · simpa only [Bool.not_eq_true] using h
        obtain ⟨vt', hγt, hbt'⟩ := IHt.1 hti hte
        have hvt : vt' = vt := Option.some.inj (hbt'.symm.trans hbt)
        subst hvt
        obtain ⟨_, IHfof⟩ := simForce M n (symEval n ρs t).val vt' hγt hfvt hwvt
        exact IHfof hfi k hk
  | M, n+1, ρs, ρ, .Constr tag ms, hρ, henv, hwf, ht => by
      have hms : faithfulBList ms = true := by simpa [Faithful, faithfulB] using ht
      obtain ⟨IHs, IHe, IHcf⟩ := simEvalList M n ρs ρ ms hρ henv hwf hms
      refine ⟨?_, ?_⟩
      · refine ⟨fun hinc herr => ?_, fun hinc herr => ?_⟩
        · obtain ⟨vs, hγ, hbe⟩ := IHs (by simpa only [symEval] using hinc) (by simpa only [symEval] using herr)
          exact ⟨.VConstr tag vs, by simp only [symEval, γ, hγ], by simp only [bigEval, hbe]⟩
        · have h := IHe (by simpa only [symEval] using hinc) (by simpa only [symEval] using herr)
          simp only [bigEval, h]
      · intro hinc m hm
        obtain ⟨m', rfl⟩ : ∃ m', m = m'+1 := ⟨m-1, by omega⟩
        simp only [bigEval]
        rw [IHcf (by simpa only [symEval] using hinc) m' (by omega)]
  | M, n+1, ρs, ρ, .Case scrut alts, hρ, henv, hwf, ht => by
      have ht' : faithfulB scrut = true ∧ faithfulBList alts = true := by
        have := ht; simp only [Faithful, faithfulB, Bool.and_eq_true] at this; exact this
      obtain ⟨IHsc, IHscf⟩ := simEval M n ρs ρ scrut hρ henv hwf ht'.1
      simp only [] at IHsc IHscf
      have hfvsc := faithfulV_symEval n ρs scrut henv ht'.1
      have hwvsc := wfV_symEval M n ρs scrut henv hwf ht'.1
      refine ⟨?_, ?_⟩
      · simp only [symEval]
        refine ⟨fun hinc herr => ?_, fun hinc herr => ?_⟩
        · simp only [denoteB_sOr, Bool.or_eq_false_iff] at hinc herr
          obtain ⟨hsci, hci⟩ := hinc
          obtain ⟨hsce, hce⟩ := herr
          obtain ⟨sv, hγsc, hbsc⟩ := IHsc.1 hsci hsce
          obtain ⟨IHc, _⟩ := simCase M n ρs ρ alts (symEval n ρs scrut).val sv hρ henv hwf ht'.2 hγsc hfvsc hwvsc
          obtain ⟨v, hγv, hcv⟩ := IHc.1 hci hce
          exact ⟨v, hγv, by rw [bigEval_Case_unfold, hbsc]; exact hcv⟩
        · simp only [denoteB_sOr, Bool.or_eq_false_iff] at hinc
          obtain ⟨hsci, hci⟩ := hinc
          by_cases hsce : denoteB M (symEval n ρs scrut).err = true
          · rw [bigEval_Case_unfold, IHsc.2 hsci hsce]
          · simp only [Bool.not_eq_true] at hsce
            obtain ⟨sv, hγsc, hbsc⟩ := IHsc.1 hsci hsce
            obtain ⟨IHc, _⟩ := simCase M n ρs ρ alts (symEval n ρs scrut).val sv hρ henv hwf ht'.2 hγsc hfvsc hwvsc
            have hce : denoteB M (symCase n ρs alts (symEval n ρs scrut).val).err = true := by
              have := herr; simp only [denoteB_sOr, hsce, Bool.false_or] at this; exact this
            rw [bigEval_Case_unfold, hbsc]; exact IHc.2 hci hce
      · intro hinc m hm
        simp only [symEval, denoteB_sOr, Bool.or_eq_false_iff] at hinc
        obtain ⟨hsci, hci⟩ := hinc
        obtain ⟨m', rfl⟩ : ∃ m', m = m'+1 := ⟨m-1, by omega⟩
        show bigEval (m'+1) ρ (.Case scrut alts) = bigEval (n+1) ρ (.Case scrut alts)
        rw [bigEval_Case_unfold, bigEval_Case_unfold, IHscf hsci m' (by omega)]
        cases hbsc : bigEval n ρ scrut with
        | none => rfl
        | some sv =>
          have hsce : denoteB M (symEval n ρs scrut).err = false := by
            by_cases h : denoteB M (symEval n ρs scrut).err = true
            · rw [IHsc.2 hsci h] at hbsc; exact absurd hbsc (by simp)
            · simpa only [Bool.not_eq_true] using h
          obtain ⟨sv', hγsc, hbsc'⟩ := IHsc.1 hsci hsce
          have hsv : sv' = sv := Option.some.inj (hbsc'.symm.trans hbsc)
          subst hsv
          obtain ⟨_, IHcf⟩ := simCase M n ρs ρ alts (symEval n ρs scrut).val sv' hρ henv hwf ht'.2 hγsc hfvsc hwvsc
          exact IHcf hci m' (by omega)
  | M, n+1, _, ρ, .Error, _, _, _, _ => by
      refine ⟨?_, fun _ m hm => bigEval_leaf_stab n (fun a b => by simp only [bigEval]) m hm⟩
      simp only [symEval]; exact relR_errR M (by simp [bigEval])
termination_by M n _ _ t => (n, sizeOf t)
decreasing_by all_goals (simp_wf; omega)

theorem simApply : ∀ (M : Model) (n : Nat) (vfh vah : SymV) (vf va : CekValue),
    γ M vfh = some vf → γ M vah = some va → FaithfulV vfh → FaithfulV vah →
    WfV M vfh → WfV M vah → SimR M n (symApply n vfh vah) (fun k => applyVal k vf va)
  | M, 0, _, _, vf, va, _, _, _, _, _, _ => by simp only [symApply]; exact simR_incR M 0 _
  | M, n+1, .lam body env, vah, vf, va, hvf, hva, hfvf, hfva, hwvf, hwva => by
      obtain ⟨Lenv, hLenv, rfl⟩ := γ_lam_inv hvf
      have hbody : faithfulB body = true ∧ FaithfulVList env := hfvf
      have hwenv : WfVList M env := hwvf
      have henv' : EnvRel M (vah :: env) ((toCekEnv Lenv).extend va) := by
        simp [EnvRel, γList, hva, hLenv, toCekEnv, CekEnv.extend]
      obtain ⟨IHb, IHbf⟩ := simEval M n (vah :: env) ((toCekEnv Lenv).extend va) body henv'
        ⟨hfva, hbody.2⟩ ⟨hwva, hwenv⟩ hbody.1
      simp only [] at IHb IHbf
      refine ⟨by simp only [symApply, applyVal]; exact IHb, ?_⟩
      intro hinc m hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m'+1 := ⟨m-1, by omega⟩
      simp only [applyVal]
      exact IHbf (by simpa only [symApply] using hinc) m' (by omega)
  | M, n+1, .builtin b args ea, vah, vf, va, hvf, hva, hfvf, hfva, hwvf, hwva => by
      obtain ⟨L, hL, rfl⟩ := γ_builtin_inv hvf
      obtain ⟨hpre, hfargs⟩ := (hfvf : preciseBuiltin b = true ∧ FaithfulVList args)
      have hwargs : WfVList M args := hwvf
      refine ⟨?_, fun _ m hm => applyVal_leaf_stab n (fun a b => by simp only [applyVal]) m hm⟩
      show RelR M (symApply (n+1) (.builtin b args ea) vah) (applyVal (n+1) (.VBuiltin b L ea) va)
      cases h1 : ea.head with
      | argQ =>
          have hs : symApply (n+1) (.builtin b args ea) vah = errR := by simp only [symApply, h1]
          have ha : applyVal (n+1) (.VBuiltin b L ea) va = none := by simp only [applyVal, h1]
          rw [hs, ha]; exact relR_errR M rfl
      | argV =>
          cases h2 : ea.tail with
          | some rest =>
              have hs : symApply (n+1) (.builtin b args ea) vah
                      = ⟨.bool false, .bool false, .builtin b (vah :: args) rest⟩ := by
                simp only [symApply, h1, h2]
              have ha : applyVal (n+1) (.VBuiltin b L ea) va = some (.VBuiltin b (va :: L) rest) := by
                simp only [applyVal, h1, h2]
              rw [hs, ha]
              exact relR_ok M ⟨.VBuiltin b (va :: L) rest, by simp [γ, γList, hva, hL], rfl⟩
          | none =>
              have hs : symApply (n+1) (.builtin b args ea) vah = symSaturate b (vah :: args) := by
                simp only [symApply, h1, h2]
              have ha : applyVal (n+1) (.VBuiltin b L ea) va = evalBuiltin b (va :: L) := by
                simp only [applyVal, h1, h2]
              rw [hs, ha]
              have hγl : γList M (vah :: args) = some (va :: L) := by simp [γList, hva, hL]
              exact satBuiltin M b (vah :: args) (va :: L) hγl hpre ⟨hfva, hfargs⟩ ⟨hwva, hwargs⟩
  | M, n+1, .choice c x y, vah, vf, va, hvf, hva, hfvf, hfva, hwvf, hwva => by
      simp only [symApply]
      refine simR_fuel_up M n ?_
      cases hc : denoteB M c with
      | true =>
          have hγx : γ M x = some vf := by simp only [γ, hc, if_true] at hvf; exact hvf
          exact symMerge_simR_left M n c _ _ hc
            (simApply M n x vah vf va hγx hva hfvf.1 hfva hwvf.1 hwva)
      | false =>
          have hγy : γ M y = some vf := by simp only [γ, hc, if_false] at hvf; exact hvf
          exact symMerge_simR_right M n c _ _ hc
            (simApply M n y vah vf va hγy hva hfvf.2 hfva hwvf.2 hwva)
  | M, n+1, .fo e, _, vf, va, hvf, _, _, _, _, _ => by
      rcases γ_fo_inv hvf with ⟨c, rfl⟩ | ⟨t, l, rfl⟩
      · refine ⟨?_, fun _ m hm => applyVal_leaf_stab n (fun a b => by simp only [applyVal]) m hm⟩
        simp only [symApply]; exact relR_errR M (applyVal_VCon (n+1) c va)
      · refine ⟨?_, fun _ m hm => applyVal_leaf_stab n (fun a b => by simp only [applyVal]) m hm⟩
        simp only [symApply]; exact relR_errR M (applyVal_VConstr (n+1) t l va)
  | M, n+1, .delay body env, _, vf, va, hvf, _, _, _, _, _ => by
      obtain ⟨L, _, rfl⟩ := γ_delay_inv hvf
      refine ⟨?_, fun _ m hm => applyVal_leaf_stab n (fun a b => by simp only [applyVal]) m hm⟩
      simp only [symApply]; exact relR_errR M (applyVal_VDelay (n+1) body (toCekEnv L) va)
  | M, n+1, .constr t fs, _, vf, va, hvf, _, _, _, _, _ => by
      obtain ⟨L, _, rfl⟩ := γ_constr_inv hvf
      refine ⟨?_, fun _ m hm => applyVal_leaf_stab n (fun a b => by simp only [applyVal]) m hm⟩
      simp only [symApply]; exact relR_errR M (applyVal_VConstr (n+1) t L va)
termination_by M n _ _ _ _ => (n, 0)

theorem simForce : ∀ (M : Model) (n : Nat) (vth : SymV) (vt : CekValue),
    γ M vth = some vt → FaithfulV vth → WfV M vth → SimR M n (symForce n vth) (fun k => forceVal k vt)
  | M, 0, _, vt, _, _, _ => by simp only [symForce]; exact simR_incR M 0 _
  | M, n+1, .delay body env, vt, hvt, hfvt, hwvt => by
      obtain ⟨Lenv, hLenv, rfl⟩ := γ_delay_inv hvt
      have hbody : faithfulB body = true ∧ FaithfulVList env := hfvt
      have hwenv : WfVList M env := hwvt
      have henv' : EnvRel M env (toCekEnv Lenv) := by simp [EnvRel, hLenv]
      obtain ⟨IHb, IHbf⟩ := simEval M n env (toCekEnv Lenv) body henv' hbody.2 hwenv hbody.1
      simp only [] at IHb IHbf
      refine ⟨by simp only [symForce, forceVal]; exact IHb, ?_⟩
      intro hinc m hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m'+1 := ⟨m-1, by omega⟩
      simp only [forceVal]
      exact IHbf (by simpa only [symForce] using hinc) m' (by omega)
  | M, n+1, .builtin b args ea, vt, hvt, hfvt, hwvt => by
      obtain ⟨L, hL, rfl⟩ := γ_builtin_inv hvt
      obtain ⟨hpre, hfargs⟩ := (hfvt : preciseBuiltin b = true ∧ FaithfulVList args)
      have hwargs : WfVList M args := hwvt
      refine ⟨?_, fun _ m hm => forceVal_leaf_stab n (fun a b => by simp only [forceVal]) m hm⟩
      show RelR M (symForce (n+1) (.builtin b args ea)) (forceVal (n+1) (.VBuiltin b L ea))
      cases h1 : ea.head with
      | argV =>
          have hs : symForce (n+1) (.builtin b args ea) = errR := by simp only [symForce, h1]
          have ha : forceVal (n+1) (.VBuiltin b L ea) = none := by simp only [forceVal, h1]
          rw [hs, ha]; exact relR_errR M rfl
      | argQ =>
          cases h2 : ea.tail with
          | some rest =>
              have hs : symForce (n+1) (.builtin b args ea)
                      = ⟨.bool false, .bool false, .builtin b args rest⟩ := by
                simp only [symForce, h1, h2]
              have ha : forceVal (n+1) (.VBuiltin b L ea) = some (.VBuiltin b L rest) := by
                simp only [forceVal, h1, h2]
              rw [hs, ha]
              exact relR_ok M ⟨.VBuiltin b L rest, by simp [γ, hL], rfl⟩
          | none =>
              have hs : symForce (n+1) (.builtin b args ea) = symSaturate b args := by
                simp only [symForce, h1, h2]
              have ha : forceVal (n+1) (.VBuiltin b L ea) = evalBuiltin b L := by
                simp only [forceVal, h1, h2]
              rw [hs, ha]
              exact satBuiltin M b args L hL hpre hfargs hwargs
  | M, n+1, .choice c x y, vt, hvt, hfvt, hwvt => by
      simp only [symForce]
      refine simR_fuel_up M n ?_
      cases hc : denoteB M c with
      | true =>
          have hγx : γ M x = some vt := by simp only [γ, hc, if_true] at hvt; exact hvt
          exact symMerge_simR_left M n c _ _ hc (simForce M n x vt hγx hfvt.1 hwvt.1)
      | false =>
          have hγy : γ M y = some vt := by simp only [γ, hc, if_false] at hvt; exact hvt
          exact symMerge_simR_right M n c _ _ hc (simForce M n y vt hγy hfvt.2 hwvt.2)
  | M, n+1, .fo e, vt, hvt, _, _ => by
      rcases γ_fo_inv hvt with ⟨c, rfl⟩ | ⟨t, l, rfl⟩
      · refine ⟨?_, fun _ m hm => forceVal_leaf_stab n (fun a b => by simp only [forceVal]) m hm⟩
        simp only [symForce]; exact relR_errR M (forceVal_VCon (n+1) c)
      · refine ⟨?_, fun _ m hm => forceVal_leaf_stab n (fun a b => by simp only [forceVal]) m hm⟩
        simp only [symForce]; exact relR_errR M (forceVal_VConstr (n+1) t l)
  | M, n+1, .lam body env, vt, hvt, _, _ => by
      obtain ⟨L, _, rfl⟩ := γ_lam_inv hvt
      refine ⟨?_, fun _ m hm => forceVal_leaf_stab n (fun a b => by simp only [forceVal]) m hm⟩
      simp only [symForce]; exact relR_errR M (forceVal_VLam (n+1) body (toCekEnv L))
  | M, n+1, .constr t fs, vt, hvt, _, _ => by
      obtain ⟨L, _, rfl⟩ := γ_constr_inv hvt
      refine ⟨?_, fun _ m hm => forceVal_leaf_stab n (fun a b => by simp only [forceVal]) m hm⟩
      simp only [symForce]; exact relR_errR M (forceVal_VConstr (n+1) t L)
termination_by M n _ _ => (n, 0)
/-- The field-list correspondence for `Constr`: the (combined-`sOrs`) outcomes of
`symEvalList` reconcile with `bigEvalList` — all fields succeed (collecting the
value list) or some field errors (so the whole list is `none`). -/
theorem simEvalList : ∀ (M : Model) (n : Nat) (ρs : SymEnv) (ρ : CekEnv) (ms : List Term),
    EnvRel M ρs ρ → FaithfulVList ρs → WfVList M ρs → faithfulBList ms = true →
    (denoteB M (sOrs ((symEvalList n ρs ms).map SymR.inc)) = false →
     denoteB M (sOrs ((symEvalList n ρs ms).map SymR.err)) = false →
     ∃ vs, γList M ((symEvalList n ρs ms).map SymR.val) = some vs ∧ bigEvalList n ρ ms = some vs) ∧
    (denoteB M (sOrs ((symEvalList n ρs ms).map SymR.inc)) = false →
     denoteB M (sOrs ((symEvalList n ρs ms).map SymR.err)) = true →
     bigEvalList n ρ ms = none) ∧
    (denoteB M (sOrs ((symEvalList n ρs ms).map SymR.inc)) = false →
     ∀ m, n ≤ m → bigEvalList m ρ ms = bigEvalList n ρ ms)
  | M, n, ρs, ρ, [], _, _, _, _ => by
      refine ⟨fun _ _ => ⟨[], by simp [symEvalList, γList], by simp [bigEvalList]⟩, fun _ herr => ?_,
              fun _ m _ => by simp only [bigEvalList]⟩
      simp [symEvalList, sOrs, denoteB_bool] at herr
  | M, n, ρs, ρ, t :: ts, hρ, henv, hwf, hms => by
      have hms' : faithfulB t = true ∧ faithfulBList ts = true := by
        simpa [faithfulBList, Bool.and_eq_true] using hms
      obtain ⟨IHt, IHtf⟩ := simEval M n ρs ρ t hρ henv hwf hms'.1
      simp only [] at IHt IHtf
      obtain ⟨IHtss, IHtse, IHtsf⟩ := simEvalList M n ρs ρ ts hρ henv hwf hms'.2
      refine ⟨fun hinc herr => ?_, fun hinc herr => ?_, fun hinc m hm => ?_⟩
      · simp only [symEvalList, List.map_cons, sOrs, List.foldr, denoteB_sOr,
          Bool.or_eq_false_iff] at hinc herr
        obtain ⟨vh, hγh, hbh⟩ := IHt.1 hinc.1 herr.1
        obtain ⟨vs, hγs, hbs⟩ := IHtss hinc.2 herr.2
        exact ⟨vh :: vs, by simp only [symEvalList, List.map_cons, γList, hγh, hγs],
               by simp only [bigEvalList, hbh, hbs]⟩
      · simp only [symEvalList, List.map_cons, sOrs, List.foldr, denoteB_sOr,
          Bool.or_eq_false_iff] at hinc
        simp only [symEvalList, List.map_cons, sOrs, List.foldr, denoteB_sOr,
          Bool.or_eq_true] at herr
        by_cases hte : denoteB M (symEval n ρs t).err = true
        · simp only [bigEvalList, IHt.2 hinc.1 hte]
        · simp only [Bool.not_eq_true] at hte
          obtain ⟨vh, hγh, hbh⟩ := IHt.1 hinc.1 hte
          have hre : denoteB M (sOrs ((symEvalList n ρs ts).map SymR.err)) = true := by
            rcases herr with h | h
            · exact absurd h (by rw [hte]; simp)
            · exact h
          simp only [bigEvalList, hbh, IHtse hinc.2 hre]
      · simp only [symEvalList, List.map_cons, sOrs, List.foldr, denoteB_sOr,
          Bool.or_eq_false_iff] at hinc
        simp only [bigEvalList]
        rw [IHtf hinc.1 m hm, IHtsf hinc.2 m hm]
termination_by M n _ _ ms => (n, sizeOf ms)

theorem simApplyList : ∀ (M : Model) (n : Nat) (vfh : SymV) (vahs : List SymV)
    (vf : CekValue) (vas : List CekValue),
    γ M vfh = some vf → γList M vahs = some vas → FaithfulV vfh → FaithfulVList vahs →
    WfV M vfh → WfVList M vahs → SimR M n (symApplyList n vfh vahs) (fun k => applyValList k vf vas)
  | M, n, vfh, [], vf, vas, hvf, hvas, _, _, _, _ => by
      obtain rfl : vas = [] := by simp only [γList] at hvas; exact (Option.some.inj hvas).symm
      simp only [symApplyList]
      exact simR_ok M n hvf (by simp only [applyValList]) (fun m _ => by simp only [applyValList])
  | M, n, vfh, vah :: vahs, vf, vas, hvf, hvas, hfvf, hfvas, hwvf, hwvas => by
      obtain ⟨va, hva, vas', hvas', rfl⟩ :
          ∃ va, γ M vah = some va ∧ ∃ vas', γList M vahs = some vas' ∧ vas = va :: vas' := by
        simp only [γList] at hvas
        cases hva : γ M vah with
        | none => rw [hva] at hvas; simp at hvas
        | some va => cases hvs : γList M vahs with
          | none => rw [hva, hvs] at hvas; simp at hvas
          | some vs => rw [hva, hvs] at hvas; exact ⟨va, rfl, vs, rfl, (Option.some.inj hvas).symm⟩
      have hfa := faithfulV_symApply n vfh vah hfvf hfvas.1
      have hwa := wfV_symApply M n vfh vah hfvf hfvas.1 hwvf hwvas.1
      obtain ⟨IHa, IHaf⟩ := simApply M n vfh vah vf va hvf hva hfvf hfvas.1 hwvf hwvas.1
      simp only [] at IHa IHaf
      refine ⟨?_, ?_⟩
      · simp only [symApplyList]
        refine ⟨fun hinc herr => ?_, fun hinc herr => ?_⟩
        · simp only [denoteB_sOr, Bool.or_eq_false_iff] at hinc herr
          obtain ⟨hai, h2i⟩ := hinc
          obtain ⟨hae, h2e⟩ := herr
          obtain ⟨vf', hγf', hbf'⟩ := IHa.1 hai hae
          obtain ⟨IH2, _⟩ := simApplyList M n (symApply n vfh vah).val vahs vf' vas' hγf' hvas' hfa hfvas.2 hwa hwvas.2
          obtain ⟨v, hγv, hav⟩ := IH2.1 h2i h2e
          exact ⟨v, hγv, by simp only [applyValList, hbf']; exact hav⟩
        · simp only [denoteB_sOr, Bool.or_eq_false_iff] at hinc
          obtain ⟨hai, h2i⟩ := hinc
          by_cases hae : denoteB M (symApply n vfh vah).err = true
          · simp only [applyValList, IHa.2 hai hae]
          · simp only [Bool.not_eq_true] at hae
            obtain ⟨vf', hγf', hbf'⟩ := IHa.1 hai hae
            obtain ⟨IH2, _⟩ := simApplyList M n (symApply n vfh vah).val vahs vf' vas' hγf' hvas' hfa hfvas.2 hwa hwvas.2
            have h2e : denoteB M (symApplyList n (symApply n vfh vah).val vahs).err = true := by
              have := herr; simp only [denoteB_sOr, hae, Bool.false_or] at this; exact this
            simp only [applyValList, hbf']; exact IH2.2 h2i h2e
      · intro hinc m hm
        simp only [symApplyList, denoteB_sOr, Bool.or_eq_false_iff] at hinc
        obtain ⟨hai, h2i⟩ := hinc
        show applyValList m vf (va :: vas') = applyValList n vf (va :: vas')
        simp only [applyValList]
        rw [IHaf hai m hm]
        cases hav : applyVal n vf va with
        | none => rfl
        | some vf' =>
          have hae : denoteB M (symApply n vfh vah).err = false := by
            by_cases h : denoteB M (symApply n vfh vah).err = true
            · have hn := IHa.2 hai h; rw [hn] at hav; exact absurd hav (by simp)
            · simpa only [Bool.not_eq_true] using h
          obtain ⟨vf'', hγf', hbf'⟩ := IHa.1 hai hae
          have hvv : vf'' = vf' := Option.some.inj (hbf'.symm.trans hav)
          subst hvv
          obtain ⟨_, IH2f⟩ := simApplyList M n (symApply n vfh vah).val vahs vf'' vas' hγf' hvas' hfa hfvas.2 hwa hwvas.2
          exact IH2f h2i m hm
termination_by M n _ vahs _ _ => (n, sizeOf vahs)

theorem simCase : ∀ (M : Model) (n : Nat) (ρs : SymEnv) (ρ : CekEnv) (alts : List Term)
    (scrutH : SymV) (sv : CekValue),
    EnvRel M ρs ρ → FaithfulVList ρs → WfVList M ρs → faithfulBList alts = true →
    γ M scrutH = some sv → FaithfulV scrutH → WfV M scrutH →
    SimR M n (symCase n ρs alts scrutH) (fun k => cekCase k ρ alts sv)
  | M, 0, ρs, ρ, alts, scrutH, sv, _, _, _, _, _, _, _ => by
      simp only [symCase]; exact simR_incR M 0 _
  | M, m+1, ρs, ρ, alts, .constr tag fields, sv, hρ, henv, hwf, hms, hγ, hfsc, hwsc => by
      obtain ⟨L, hL, rfl⟩ := γ_constr_inv hγ
      cases ha : alts[tag]? with
      | none =>
          simp only [symCase, ha]
          exact simR_errR M (m+1) (fun k => by simp only [cekCase, ha])
      | some alt =>
          have halt : faithfulB alt = true := faithfulBList_get alts tag alt hms ha
          obtain ⟨IHr, IHrf⟩ := simEval M m ρs ρ alt hρ henv hwf halt
          simp only [] at IHr IHrf
          have hfr := faithfulV_symEval m ρs alt henv halt
          have hwr := wfV_symEval M m ρs alt henv hwf halt
          have hffields : FaithfulVList fields := hfsc
          have hwfields : WfVList M fields := hwsc
          -- `cekCase k` is fuel-stable from `m` (symbolic alt eval is one fuel behind
          -- the CEK's, but fuel-stability of the deterministic CEK bridges the gap).
          have key : ∀ k, m ≤ k → denoteB M (symEval m ρs alt).inc = false →
              denoteB M (symApplyList m (symEval m ρs alt).val fields).inc = false →
              cekCase k ρ alts (.VConstr tag L) = cekCase m ρ alts (.VConstr tag L) := by
            intro k hk hri h2i
            simp only [cekCase, ha]
            rw [IHrf hri k hk]
            cases hbr : bigEval m ρ alt with
            | none => rfl
            | some vAlt =>
              have hre : denoteB M (symEval m ρs alt).err = false := by
                by_cases h : denoteB M (symEval m ρs alt).err = true
                · have hn := IHr.2 hri h; rw [hn] at hbr; exact absurd hbr (by simp)
                · simpa only [Bool.not_eq_true] using h
              obtain ⟨vAlt', hγr, hbr'⟩ := IHr.1 hri hre
              have hvv : vAlt' = vAlt := Option.some.inj (hbr'.symm.trans hbr)
              subst hvv
              obtain ⟨_, IH2f⟩ := simApplyList M m (symEval m ρs alt).val fields vAlt' L hγr hL hfr hffields hwr hwfields
              simp only [] at IH2f
              exact IH2f h2i k hk
          simp only [symCase, ha]
          refine ⟨?_, ?_⟩
          · refine ⟨fun hinc herr => ?_, fun hinc herr => ?_⟩
            · simp only [denoteB_sOr, Bool.or_eq_false_iff] at hinc herr
              obtain ⟨hri, h2i⟩ := hinc
              obtain ⟨hre, h2e⟩ := herr
              obtain ⟨vAlt, hγr, hbr⟩ := IHr.1 hri hre
              obtain ⟨IH2, _⟩ := simApplyList M m (symEval m ρs alt).val fields vAlt L hγr hL hfr hffields hwr hwfields
              simp only [] at IH2
              obtain ⟨v, hγv, hav⟩ := IH2.1 h2i h2e
              refine ⟨v, hγv, ?_⟩
              show cekCase (m+1) ρ alts (.VConstr tag L) = some v
              rw [key (m+1) (Nat.le_succ m) hri h2i]
              simp only [cekCase, ha, hbr]; exact hav
            · simp only [denoteB_sOr, Bool.or_eq_false_iff] at hinc
              obtain ⟨hri, h2i⟩ := hinc
              show cekCase (m+1) ρ alts (.VConstr tag L) = none
              rw [key (m+1) (Nat.le_succ m) hri h2i]
              by_cases hre : denoteB M (symEval m ρs alt).err = true
              · simp only [cekCase, ha, IHr.2 hri hre]
              · simp only [Bool.not_eq_true] at hre
                obtain ⟨vAlt, hγr, hbr⟩ := IHr.1 hri hre
                obtain ⟨IH2, _⟩ := simApplyList M m (symEval m ρs alt).val fields vAlt L hγr hL hfr hffields hwr hwfields
                simp only [] at IH2
                have h2e : denoteB M (symApplyList m (symEval m ρs alt).val fields).err = true := by
                  have := herr; simp only [denoteB_sOr, hre, Bool.false_or] at this; exact this
                simp only [cekCase, ha, hbr]; exact IH2.2 h2i h2e
          · intro hinc m' hm'
            simp only [symCase, ha, denoteB_sOr, Bool.or_eq_false_iff] at hinc
            obtain ⟨hri, h2i⟩ := hinc
            show cekCase m' ρ alts (.VConstr tag L) = cekCase (m+1) ρ alts (.VConstr tag L)
            rw [key m' (by omega) hri h2i, key (m+1) (Nat.le_succ m) hri h2i]
  | M, m+1, ρs, ρ, alts, .choice c x y, sv, hρ, henv, hwf, hms, hγ, hfsc, hwsc => by
      simp only [symCase]
      refine simR_fuel_up M m ?_
      cases hc : denoteB M c with
      | true =>
          have hγx : γ M x = some sv := by simp only [γ, hc, if_true] at hγ; exact hγ
          exact symMerge_simR_left M m c _ _ hc
            (simCase M m ρs ρ alts x sv hρ henv hwf hms hγx hfsc.1 hwsc.1)
      | false =>
          have hγy : γ M y = some sv := by simp only [γ, hc, if_false] at hγ; exact hγ
          exact symMerge_simR_right M m c _ _ hc
            (simCase M m ρs ρ alts y sv hρ henv hwf hms hγy hfsc.2 hwsc.2)
  | M, m+1, ρs, ρ, alts, .fo e, sv, hρ, henv, hwf, hms, hγ, hfsc, hwsc => by
      obtain ⟨va, hwfo⟩ := hwsc
      have hsveq : va = sv := by have h := γ_fo_denote hγ; rw [hwfo.den] at h; injection h
      subst hsveq
      have Halt : ∀ (i : Nat) (alt : Term), alts[i]? = some alt →
          SimR M m (symEval m ρs alt) (fun k => bigEval k ρ alt) :=
        fun i alt h => simEval M m ρs ρ alt hρ henv hwf (faithfulBList_get alts i alt hms h)
      have hlen : (symEvalList m ρs alts).length = alts.length := symEvalList_length m ρs alts
      obtain ⟨hfL, hfDL, hfP, hfPD, hfC⟩ := hfsc
      simp only [symCase]
      split
      · -- VBool
        rename_i heq
        have hb : vIs "VBool" va = true := by
          have ht := hwfo.tBool; simp only [V.sIsCon, heq, denoteB_bool] at ht; exact ht.symm
        obtain ⟨b, rfl⟩ := vIs_VBool hb
        have hpb : denoteB M (V.sAsBool e) = b := by rw [denoteB, hwfo.pBool b rfl]; rfl
        refine simR_fuel_up M m ?_
        cases b
        · by_cases hl : alts.length > 2
          · rw [if_pos (by rw [hlen]; exact hl)]
            exact simR_errR M m (fun k => by simp [cekCase, Moist.CEK.constToTagAndFields, hl])
          · rw [if_neg (by rw [hlen]; exact hl)]
            have hcek : (fun k => cekCase k ρ alts (.VCon (.Bool false)))
                      = (fun k => match alts[0]? with | some a => bigEval k ρ a | none => none) := by
              funext k
              rcases ha : alts[0]? with _ | alt
              · simp [cekCase, Moist.CEK.constToTagAndFields, hl, ha]
              · rcases hb : bigEval k ρ alt with _ | vAlt <;>
                  simp [cekCase, Moist.CEK.constToTagAndFields, hl, ha, hb, applyValList]
            rw [hcek]
            exact symMerge_simR_right M m _ _ _ hpb (altOr_sim M m ρs ρ alts 0 (fun alt h => Halt 0 alt h))
        · by_cases hl : alts.length > 2
          · rw [if_pos (by rw [hlen]; exact hl)]
            exact simR_errR M m (fun k => by simp [cekCase, Moist.CEK.constToTagAndFields, hl])
          · rw [if_neg (by rw [hlen]; exact hl)]
            have hcek : (fun k => cekCase k ρ alts (.VCon (.Bool true)))
                      = (fun k => match alts[1]? with | some a => bigEval k ρ a | none => none) := by
              funext k
              rcases ha : alts[1]? with _ | alt
              · simp [cekCase, Moist.CEK.constToTagAndFields, hl, ha]
              · rcases hb : bigEval k ρ alt with _ | vAlt <;>
                  simp [cekCase, Moist.CEK.constToTagAndFields, hl, ha, hb, applyValList]
            rw [hcek]
            exact symMerge_simR_left M m _ _ _ hpb (altOr_sim M m ρs ρ alts 1 (fun alt h => Halt 1 alt h))
      · -- VUnit
        rename_i heq
        have hu : vIs "VUnit" va = true := by
          have ht := hwfo.tUnit; simp only [V.sIsCon, heq, denoteB_bool] at ht; exact ht.symm
        rw [vIs_VUnit hu]
        refine simR_fuel_up M m ?_
        by_cases hl : alts.length > 1
        · rw [if_pos (by rw [hlen]; exact hl)]
          exact simR_errR M m (fun k => by simp [cekCase, Moist.CEK.constToTagAndFields, hl])
        · rw [if_neg (by rw [hlen]; exact hl)]
          have hcek : (fun k => cekCase k ρ alts (.VCon .Unit))
                    = (fun k => match alts[0]? with | some a => bigEval k ρ a | none => none) := by
            funext k
            rcases ha : alts[0]? with _ | alt
            · simp [cekCase, Moist.CEK.constToTagAndFields, hl, ha]
            · rcases hb : bigEval k ρ alt with _ | vAlt <;>
                simp [cekCase, Moist.CEK.constToTagAndFields, hl, ha, hb, applyValList]
          rw [hcek]
          exact altOr_sim M m ρs ρ alts 0 (fun alt h => Halt 0 alt h)
      · -- VInt
        rename_i heq
        have hi : vIs "VInt" va = true := by
          have ht := hwfo.tInt; simp only [V.sIsCon, heq, denoteB_bool] at ht; exact ht.symm
        obtain ⟨nn, rfl⟩ := vIs_VInt hi
        have hpi : denote M (V.sAsInt e) = .I nn := hwfo.pInt nn rfl
        refine simR_fuel_up M m ?_
        have hcek : (fun k => cekCase k ρ alts (.VCon (.Integer nn)))
                  = (fun k => if (0:Int) ≤ nn then
                      (match alts[(nn - (Int.ofNat 0)).toNat]? with | some a => bigEval k ρ a | none => none)
                    else none) := by
          funext k
          have h0 : (nn - (Int.ofNat 0)).toNat = nn.toNat := by simp
          rw [h0]
          by_cases hnn : (0:Int) ≤ nn
          · rw [if_pos hnn]
            rcases ha : alts[nn.toNat]? with _ | alt
            · simp [cekCase, Moist.CEK.constToTagAndFields, ge_iff_le, hnn, ha]
            · rcases hb : bigEval k ρ alt with _ | vAlt <;>
                simp [cekCase, Moist.CEK.constToTagAndFields, ge_iff_le, hnn, ha, hb, applyValList]
          · rw [if_neg hnn]
            simp [cekCase, Moist.CEK.constToTagAndFields, ge_iff_le, hnn]
        rw [hcek]
        exact dispatchIntFrom_sim M m ρs ρ (V.sAsInt e) nn hpi alts 0 (fun i alt h => Halt i alt h)
      · rename_i heq; exact absurd heq hfL
      · rename_i heq; exact absurd heq hfDL
      · rename_i heq; exact absurd heq hfP
      · rename_i heq; exact absurd heq hfPD
      · -- none → incR
        exact simR_incR M (m+1) _
      · -- catch-all (some val, none of the 7 case-able heads) → errR; CEK Case errors
        rename_i val hb hu hi hL hDL hP hPD heq
        refine simR_errR M (m+1) (fun k => ?_)
        exact cekCase_none_of_vConName M k ρ alts e va val hwfo heq hb hu hi hL hDL hP hPD
          (fun h => hfC (by rw [heq, h]))
  | M, m+1, ρs, ρ, alts, .lam _ _, sv, _, _, _, _, hγ, _, _ => by
      obtain ⟨L, _, rfl⟩ := γ_lam_inv hγ
      simp only [symCase]
      exact simR_errR M (m+1) (fun k => by simp only [cekCase])
  | M, m+1, ρs, ρ, alts, .delay _ _, sv, _, _, _, _, hγ, _, _ => by
      obtain ⟨L, _, rfl⟩ := γ_delay_inv hγ
      simp only [symCase]
      exact simR_errR M (m+1) (fun k => by simp only [cekCase])
  | M, m+1, ρs, ρ, alts, .builtin _ _ _, sv, _, _, _, _, hγ, _, _ => by
      obtain ⟨L, _, rfl⟩ := γ_builtin_inv hγ
      simp only [symCase]
      exact simR_errR M (m+1) (fun k => by simp only [cekCase])
termination_by M n _ _ _ scrutH _ => (n, 0)
end

/-- **`Sim` holds** for the proven fragment. -/
theorem Sim_holds : Sim := fun M n ρs ρ t hρ henv hwf ht => (simEval M n ρs ρ t hρ henv hwf ht).1

/-- A list of length two is a literal pair. -/
theorem list_len2 {α} (l : List α) (h : l.length = 2) : ∃ a b, l = [a, b] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · simp at h
  · simp at h
  · exact ⟨a, b, rfl⟩
  · simp only [List.length_cons] at h; omega

/-- A saturated precise builtin has a *literal* indeterminate flag (`true`/`false`),
hence is fuel-determinate. (Needed for `Stab`'s builtin case.) -/
theorem symSaturate_inc_lit (b : BuiltinFun) (args : List SymV) (h : preciseBuiltin b = true) :
    (symSaturate b args).inc = .bool false ∨ (symSaturate b args).inc = .bool true := by
  -- Uniform over arity: the `inc` field of every precise builtin's `symBuiltin`
  -- arm is a literal, determined by the (reversed, reified) argument shape.
  -- Exposing up to three cons cells suffices for all current precise builtins
  -- (unary/binary; no precise ternary arm exists).
  cases b <;> first | (exfalso; revert h; decide) | skip
  all_goals (
    show (symBuiltin _ (List.map Prod.snd (List.map reifyFO args.reverse))).inc = .bool false ∨
         (symBuiltin _ (List.map Prod.snd (List.map reifyFO args.reverse))).inc = .bool true
    generalize (List.map Prod.snd (List.map reifyFO args.reverse)) = R
    rcases R with _ | ⟨a, _ | ⟨b2, _ | ⟨c, t⟩⟩⟩ <;>
      first | exact Or.inl rfl | exact Or.inr rfl)

/-! ## Upward fuel-stability — now folded into `SimR`'s 3rd component.

The old `stab` mutual (symbolic-side fuel-determinacy `symEval (n+1)=symEval n`)
is gone: it is genuinely false for symbolic branching (a `symMerge`'s `inc` is an
`ite`, never a literal). What soundness actually needs — CEK-side fuel-stability,
`denoteB inc = false → ∀ m ≥ n, bigEval m = bigEval n` — is the third component of
`SimR`, proved in the same induction as the simulation, with no congruence. -/

/-! ## The two main theorems (in CEK terms), from `Sim`/`Stab` -/

/-- The empty environment concretizes to the empty CEK environment. -/
theorem envRel_nil (M : Model) : EnvRel M [] CekEnv.nil := by
  simp [EnvRel, γList, toCekEnv]

/-- **Success ⇒ the CEK halts.** If the compiled formula says a closed faithful
term completes without error and yields `v` (under model `M`), the CEK halts at
its concretization. Unconditional. -/
theorem symbolic_success_sound {n : Nat} {t : Term} (ht : Faithful t)
    (M : Model)
    (hinc : denoteB M (symEval n [] t).inc = false)
    (herr : denoteB M (symEval n [] t).err = false) :
    ∃ cv, γ M (symEval n [] t).val = some cv ∧ Reaches (init t) (.halt cv) := by
  have hr := simEval M n [] CekEnv.nil t (envRel_nil M) faithfulVList_nil (wfVList_nil M) ht
  obtain ⟨cv, hγ, hbig⟩ := hr.1.1 hinc herr
  exact ⟨cv, hγ, Moist.Verified.BigStep.bigEval_sound hbig⟩

/-- **Error ⇒ the CEK fails.** If the compiled formula says a closed faithful term
*definitely* errors (error true, indeterminate false), the CEK never halts with a
value. Unconditional. -/
theorem symbolic_error_sound {n : Nat} {t : Term} (ht : Faithful t)
    (M : Model)
    (hinc : denoteB M (symEval n [] t).inc = false)
    (herr : denoteB M (symEval n [] t).err = true) :
    ¬ ∃ v, Reaches (init t) (.halt v) := by
  -- `SimR` gives `bigEval n = none` (error sim) AND CEK fuel-stability
  -- (`∀ m ≥ n, bigEval m = bigEval n`); with downward `none`-persistence that forces
  -- `bigEval` to `none` at *every* fuel — no `stab` needed.
  have hsim := simEval M n [] CekEnv.nil t (envRel_nil M) faithfulVList_nil (wfVList_nil M) ht
  have hbn : bigEval n CekEnv.nil t = none := hsim.1.2 hinc herr
  have hfuel : ∀ m, n ≤ m → bigEval m CekEnv.nil t = bigEval n CekEnv.nil t := hsim.2 hinc
  have hall : ∀ f, bigEval f CekEnv.nil t = none := by
    intro f
    rcases Nat.le_total n f with hnf | hfn
    · rw [hfuel f hnf, hbn]
    · cases hbf : bigEval f CekEnv.nil t with
      | none => rfl
      | some v =>
        have h2 := Moist.Verified.BigStep.bigEval_mono_le hfn hbf
        rw [hbn] at h2; exact absurd h2 (by simp)
  rintro ⟨v, hreach⟩
  obtain ⟨f, hf⟩ := (Moist.Verified.BigStep.bigEval_iff_halt).2 hreach
  rw [hall f] at hf; exact absurd hf (by simp)

end Moist.Verified.SymbolicSoundness
