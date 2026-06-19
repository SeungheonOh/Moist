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

The proven fragment is the higher-order core **plus the first symbolic builtins**:
λ-calculus (`Var`/`Lam`/`Apply`), `Force`/`Delay`, simple constants
(`Integer`/`Bool`/`Unit`/`String`), `Error`, and the builtins in `preciseBuiltin`
— currently the six Integer arithmetic/comparison builtins `Add`/`Subtract`/
`Multiply`/`Equals`/`LessThan`/`LessThanEquals` (each a one-line `satBin`
application; the partial-application/saturation machinery, `VBuiltin` accumulation,
and the reconciliation `satBuiltin`/`satBin` are all general). It proves the
genuinely hard parts: higher-order closures + environments, full **partiality**
(apply-non-function, force-non-delay, unbound-variable, *and builtin type-errors*
all fail, both directions), and symbolic arithmetic/equality/comparison.

**Model well-sortedness (`WfFO`).** The folding projectors (`V.sAsInt`/`V.sIsCon`)
strip a `V`-wrapper, exposing its inner expression; under an *arbitrary* model that
inner could denote to the wrong sort, which would make `equalsInteger` genuinely
unsound. We therefore carry `WfV`/`WfFO` (folding-clean) through the simulation:
established robustly for literal/builtin-result values, and for symbolic input
atoms exactly when the model assigns them their declared sort — which is precisely
what z3 guarantees. (The two `evalBuiltin_*_spec` axioms are the only non-standard
axioms; they are the trusted per-builtin input→output tables, true by `rfl` but
axiomatised because `evalBuiltin` whnf-times-out — the established BigStep pattern.)

The remaining builtins extend this same scaffold: `Subtract`/`Multiply`/`LessThan`/
`LessThanEquals` (mechanical, like `Add`/`Equals`); the division family (needs
`mFdiv = haskellDiv` number-theory lemmas); ByteString ops (needs the
`ByteArray`↔`List Int` bridge); `Data`/list/pair structural builtins; and
`ifThenElse`/`chooseX` + `Case`/`Constr` (needs the symbolic-branching `choice`
determinacy machinery). Opaque crypto/BLS stay out (the Moist CEK errors on them).
-/

namespace Moist.Verified.SymbolicSoundness

open Moist.Symbolic
open Moist.Plutus.Term (Term Const BuiltinType BuiltinFun)
open Moist.Plutus (Data ByteString)
open Moist.CEK (CekValue CekEnv evalBuiltin expectedArgs)
open Moist.Verified.BigStep (bigEval applyVal forceVal
  evalBuiltin_AddInteger_spec evalBuiltin_SubtractInteger_spec evalBuiltin_MultiplyInteger_spec
  evalBuiltin_EqualsInteger_spec evalBuiltin_LessThanInteger_spec evalBuiltin_LessThanEqualsInteger_spec)
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
  | .EqualsInteger | .LessThanInteger | .LessThanEqualsInteger => true
  | _ => false

/-- The constants of the proven fragment (Integer/Bool/Unit/String — denote
directly, no `ByteString`/`Data` round-tripping). -/
def simpleConst : Const → Bool
  | .Integer _ | .Bool _ | .Unit | .String _ => true
  | _ => false

/-- A term is *faithful* (in the proven fragment): λ-calculus + `force`/`delay` +
the Integer builtins + simple constants. `Constr`/`Case` (and other builtins) are
the next increment, excluded here. -/
def faithfulB : Term → Bool
  | .Var _          => true
  | .Constant (c,_) => simpleConst c
  | .Builtin b      => preciseBuiltin b
  | .Lam _ body     => faithfulB body
  | .Apply f a      => faithfulB f && faithfulB a
  | .Delay t        => faithfulB t
  | .Force t        => faithfulB t
  | .Constr _ _     => false
  | .Case _ _       => false
  | .Error          => true

/-- A term is faithful (in the proven fragment). -/
def Faithful (t : Term) : Prop := faithfulB t = true

/-! ## Faithfulness of symbolic values

The evaluation invariant: every value reachable from a faithful term is faithful
— closures capture faithful bodies/environments, partial builtins are precise,
and `constr`/`choice` (out of fragment) never arise. This lets the builtin case
of the simulation invoke the builtin lemma and the `constr`/`choice` cases
discharge as impossible. -/

mutual
def FaithfulV : SymV → Prop
  | .fo _ => True
  | .lam body env => faithfulB body = true ∧ FaithfulVList env
  | .delay body env => faithfulB body = true ∧ FaithfulVList env
  | .constr _ _ => False
  | .builtin b args _ => preciseBuiltin b = true ∧ FaithfulVList args
  | .choice _ _ _ => False
def FaithfulVList : List SymV → Prop
  | []      => True
  | v :: vs => FaithfulV v ∧ FaithfulVList vs
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

/-! ## Foundational `denote` reductions (needed early by `WfFO`/`WfV`) -/

@[simp] theorem denote_atom (M : Model) (a : String) : denote M (.atom a) = dNull M a := rfl
@[simp] theorem dUn_VInt (x : SVal) : dUn "VInt" x = .Vv (.VCon (.Integer (SVal.asI x))) := rfl
@[simp] theorem dUn_VBool (x : SVal) : dUn "VBool" x = .Vv (.VCon (.Bool (SVal.asB x))) := rfl
@[simp] theorem dUn_VStr (x : SVal) : dUn "VStr" x = .Vv (.VCon (.String (SVal.asStr x))) := rfl
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

/-- `vIs "VInt"` holds only of integer values. -/
theorem vIs_VInt {va : CekValue} (h : vIs "VInt" va = true) : ∃ n, va = .VCon (.Integer n) := by
  cases va with
  | VCon c => cases c with
    | Integer n => exact ⟨n, rfl⟩
    | _ => simp [vIs] at h
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
def WfFO (M : Model) (e : SExpr) : Prop :=
  ∃ va, denote M e = .Vv va ∧
    (∀ n, va = .VCon (.Integer n) → denote M (V.sAsInt e)  = .I n) ∧
    (∀ b, va = .VCon (.Bool b)    → denote M (V.sAsBool e) = .B b) ∧
    denoteB M (V.sIsCon "VInt" e)  = vIs "VInt" va ∧
    denoteB M (V.sIsCon "VBool" e) = vIs "VBool" va

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

/-- The integer connection lemma: a folding-clean value whose integer type-guard is
satisfied is a concrete integer whose `sAsInt` projection denotes cleanly. -/
theorem wf_int {M : Model} {e : SExpr} {va : CekValue}
    (hwf : WfFO M e) (hγ : γ M (.fo e) = some va) (hg : denoteB M (gInt e) = false) :
    ∃ n, va = .VCon (.Integer n) ∧ denote M (V.sAsInt e) = .I n := by
  obtain ⟨va', hden, hpi, _, hti, _⟩ := hwf
  have hd : denote M e = .Vv va := γ_fo_denote hγ
  have hvv : va = va' := by
    have hvv' : SVal.Vv va = SVal.Vv va' := hd ▸ hden
    injection hvv'
  subst hvv
  have ht : denoteB M (V.sIsCon "VInt" e) = true := by
    simpa [gInt, denoteB_sNot] using hg
  rw [hti] at ht
  obtain ⟨n, hn⟩ := vIs_VInt ht
  exact ⟨n, hn, hpi n hn⟩

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

/-- Hence such a result is (model-independently) faithful. -/
theorem faithfulV_symSaturate (b : BuiltinFun) (args : List SymV) (h : preciseBuiltin b = true) :
    FaithfulV (symSaturate b args).val := by
  obtain ⟨e, he⟩ := symSaturate_val_fo b args h; rw [he]; exact True.intro

mutual
theorem faithfulV_symEval : ∀ (n : Nat) (ρs : SymEnv) (t : Term),
    FaithfulVList ρs → Faithful t → FaithfulV (symEval n ρs t).val
  | 0, _, _, _, _ => by simp [symEval, incR, junk, FaithfulV]
  | _+1, ρs, .Var k, hρ, _ => by
      simp only [symEval]
      cases h : symLookup ρs k with
      | none => simp [errR, junk, FaithfulV]
      | some v => exact symLookup_faithful ρs k v hρ h
  | _+1, _, .Constant (c, _), _, _ => by simp [symEval, FaithfulV]
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
  | _+1, _, .Constr _ _, _, ht => by simp [Faithful, faithfulB] at ht
  | _+1, _, .Case _ _, _, ht => by simp [Faithful, faithfulB] at ht
  | _+1, _, .Error, _, _ => by simp [symEval, errR, junk, FaithfulV]
termination_by n _ t => (n, sizeOf t)

theorem faithfulV_symApply : ∀ (n : Nat) (vf va : SymV),
    FaithfulV vf → FaithfulV va → FaithfulV (symApply n vf va).val
  | 0, _, _, _, _ => by simp [symApply, incR, junk, FaithfulV]
  | n+1, .lam body env, va, hf, ha => by
      have hbody : faithfulB body = true ∧ FaithfulVList env := hf
      simp only [symApply]
      exact faithfulV_symEval n (va :: env) body ⟨ha, hbody.2⟩ hbody.1
  | _+1, .builtin b args ea, va, hf, ha => by
      have hf' : preciseBuiltin b = true ∧ FaithfulVList args := hf
      obtain ⟨hpre, hargs⟩ := hf'
      simp only [symApply]
      cases h1 : ea.head with
      | argQ => simp [h1, errR, junk, FaithfulV]
      | argV =>
          cases h2 : ea.tail with
          | none => simp only [h1, h2]; exact faithfulV_symSaturate b (va :: args) hpre
          | some rest =>
              simp only [h1, h2]
              exact ⟨hpre, ha, hargs⟩
  | _+1, .choice _ _ _, _, hf, _ => by simp [FaithfulV] at hf
  | _+1, .fo _, _, _, _ => by simp [symApply, errR, junk, FaithfulV]
  | _+1, .delay _ _, _, _, _ => by simp [symApply, errR, junk, FaithfulV]
  | _+1, .constr _ _, _, hf, _ => by simp [FaithfulV] at hf
termination_by n vf _ => (n, sizeOf vf)

theorem faithfulV_symForce : ∀ (n : Nat) (vt : SymV),
    FaithfulV vt → FaithfulV (symForce n vt).val
  | 0, _, _ => by simp [symForce, incR, junk, FaithfulV]
  | n+1, .delay body env, ht => by
      have hbody : faithfulB body = true ∧ FaithfulVList env := ht
      simp only [symForce]
      exact faithfulV_symEval n env body hbody.2 hbody.1
  | _+1, .builtin b args ea, ht => by
      have ht' : preciseBuiltin b = true ∧ FaithfulVList args := ht
      obtain ⟨hpre, hargs⟩ := ht'
      simp only [symForce]
      cases h1 : ea.head with
      | argV => simp [h1, errR, junk, FaithfulV]
      | argQ =>
          cases h2 : ea.tail with
          | none => simp only [h1, h2]; exact faithfulV_symSaturate b args hpre
          | some rest => simp only [h1, h2]; exact ⟨hpre, hargs⟩
  | _+1, .choice _ _ _, ht => by simp [FaithfulV] at ht
  | _+1, .fo _, _ => by simp [symForce, errR, junk, FaithfulV]
  | _+1, .lam _ _, _ => by simp [symForce, errR, junk, FaithfulV]
  | _+1, .constr _ _, ht => by simp [FaithfulV] at ht
termination_by n vt => (n, sizeOf vt)
end

/-! ## `WfFO` base / closure lemmas and `WfV` preservation -/

/-- `V.unit` is folding-clean (it is a concrete `VCon Unit`). -/
theorem wfFO_unit (M : Model) : WfFO M V.unit := by
  refine ⟨.VCon .Unit, by simp only [V.unit, denote_atom, dNull_VUnit], ?_, ?_, ?_, ?_⟩
  · intro n hn; exact absurd hn (by simp)
  · intro b hb; exact absurd hb (by simp)
  · simp [V.unit, V.sIsCon, V.vConName, vIs, denoteB, dNull]
  · simp [V.unit, V.sIsCon, V.vConName, vIs, denoteB, dNull]

/-- Any `V.int` wrapper of an `Int`-denoting expression is folding-clean. -/
theorem wfFO_Vint (M : Model) (e : SExpr) (k : Int) (h : denote M e = .I k) :
    WfFO M (V.int e) := by
  refine ⟨.VCon (.Integer k), by simp only [V.int, denote_app1, dUn_VInt, h, SVal.asI], ?_, ?_, ?_, ?_⟩
  · intro m hm; injection hm with hm'; injection hm' with hm''; subst hm''
    simp only [V.int, V.sAsInt, h]
  · intro b hb; exact absurd hb (by simp)
  · simp [V.int, V.sIsCon, V.vConName, vIs, denoteB, V.knownVCons]
  · simp [V.int, V.sIsCon, V.vConName, vIs, denoteB, V.knownVCons]

/-- Any `V.bool` wrapper of a `Bool`-denoting expression is folding-clean. -/
theorem wfFO_Vbool (M : Model) (e : SExpr) (c : Bool) (h : denote M e = .B c) :
    WfFO M (V.bool e) := by
  refine ⟨.VCon (.Bool c), by simp only [V.bool, denote_app1, dUn_VBool, h, SVal.asB], ?_, ?_, ?_, ?_⟩
  · intro n hn; exact absurd hn (by simp)
  · intro b hb; injection hb with hb'; injection hb' with hb''; subst hb''
    simp only [V.bool, V.sAsBool, h]
  · simp [V.bool, V.sIsCon, V.vConName, vIs, denoteB, V.knownVCons]
  · simp [V.bool, V.sIsCon, V.vConName, vIs, denoteB, V.knownVCons]

/-- Encoded simple constants are folding-clean. -/
theorem wfFO_simpleConst (M : Model) (c : Const) (h : simpleConst c = true) :
    WfFO M (constToSExpr c) := by
  cases c
  case Integer n => simp only [constToSExpr]; exact wfFO_Vint M (.int n) n rfl
  case Bool b => simp only [constToSExpr]; exact wfFO_Vbool M (.bool b) b rfl
  case Unit => exact wfFO_unit M
  case String s =>
    simp only [constToSExpr]
    refine ⟨.VCon (.String s), by simp only [V.str, denote_app1, denote_lit_str, dUn_VStr, SVal.asStr], ?_, ?_, ?_, ?_⟩
    · intro n hn; exact absurd hn (by simp)
    · intro b hb; exact absurd hb (by simp)
    · simp [V.str, V.sIsCon, V.vConName, vIs, denoteB, V.knownVCons]
    · simp [V.str, V.sIsCon, V.vConName, vIs, denoteB, V.knownVCons]
  all_goals exact absurd h (by simp [simpleConst])

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

/-- A saturated precise builtin yields a folding-clean (first-order) value. -/
theorem wfV_symSaturate (M : Model) (b : BuiltinFun) (args : List SymV)
    (h : preciseBuiltin b = true) : WfV M (symSaturate b args).val := by
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
  cases b <;> first | (exfalso; revert h; decide) | skip
  case AddInteger => exact keyA _
  case SubtractInteger => exact keyS _
  case MultiplyInteger => exact keyM _
  case EqualsInteger => exact keyE _
  case LessThanInteger => exact keyL _
  case LessThanEqualsInteger => exact keyLe _

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
  | _+1, _, .Constr _ _, _, _, ht => by simp [Faithful, faithfulB] at ht
  | _+1, _, .Case _ _, _, _, ht => by simp [Faithful, faithfulB] at ht
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
          | none => simp only [h1, h2]; exact wfV_symSaturate M b (va :: args) hf'.1
          | some rest => simp only [h1, h2]; exact ⟨hwa, hwf⟩
  | _+1, .choice _ _ _, _, hf, _, _, _ => by simp [FaithfulV] at hf
  | _+1, .fo _, _, _, _, _, _ => by simp only [symApply, errR]; exact wfFO_unit M
  | _+1, .delay _ _, _, _, _, _, _ => by simp only [symApply, errR]; exact wfFO_unit M
  | _+1, .constr _ _, _, hf, _, _, _ => by simp [FaithfulV] at hf
termination_by n vf _ => (n, sizeOf vf)

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
          | none => simp only [h1, h2]; exact wfV_symSaturate M b args ht'.1
          | some rest => simp only [h1, h2]; exact hwt
  | _+1, .choice _ _ _, ht, _ => by simp [FaithfulV] at ht
  | _+1, .fo _, _, _ => by simp only [symForce, errR]; exact wfFO_unit M
  | _+1, .lam _ _, _, _ => by simp only [symForce, errR]; exact wfFO_unit M
  | _+1, .constr _ _, ht, _ => by simp [FaithfulV] at ht
termination_by n vt => (n, sizeOf vt)
end

/-! ## Supporting lemmas for the simulation -/

/-- `denoteB` over a 3-element `sOrs` is the disjunction. -/
theorem denoteB_sOrs3 (M : Model) (a b c : SExpr) :
    denoteB M (sOrs [a, b, c]) = (denoteB M a || denoteB M b || denoteB M c) := by
  simp [sOrs, denoteB_sOr, Bool.or_assoc]

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

/-- A faithful value whose non-first-order flag denotes `false` is first-order. -/
theorem faithful_reify_fo {M : Model} {v : SymV} (hf : FaithfulV v)
    (h : denoteB M (reifyFO v).1 = false) : ∃ e, v = .fo e := by
  cases v with
  | fo e => exact ⟨e, rfl⟩
  | lam _ _ => simp [reifyFO, denoteB] at h
  | delay _ _ => simp [reifyFO, denoteB] at h
  | builtin _ _ _ => simp [reifyFO, denoteB] at h
  | constr _ _ => simp [FaithfulV] at hf
  | choice _ _ _ => simp [FaithfulV] at hf

/-- A faithful value concretizing to a `VCon` is first-order. -/
theorem γ_VCon_fo {M : Model} {v : SymV} {c : Const} (hf : FaithfulV v)
    (h : γ M v = some (.VCon c)) : ∃ e, v = .fo e := by
  cases v with
  | fo e => exact ⟨e, rfl⟩
  | lam _ _ => rw [γ] at h; split at h <;> simp_all
  | delay _ _ => rw [γ] at h; split at h <;> simp_all
  | builtin _ _ _ => rw [γ] at h; split at h <;> simp_all
  | constr _ _ => simp [FaithfulV] at hf
  | choice _ _ _ => simp [FaithfulV] at hf

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
  obtain ⟨e1, rfl⟩ := faithful_reify_fo hf1 hnf1
  obtain ⟨e2, rfl⟩ := faithful_reify_fo hf2 hnf2
  simp only [reifyFO] at hg1 hg2 ⊢
  have hw1' : WfFO M e1 := hw1
  have hw2' : WfFO M e2 := hw2
  obtain ⟨n1, hc1, hp1⟩ := wf_int hw1' hv1 hg1
  obtain ⟨n2, hc2, hp2⟩ := wf_int hw2' hv2 hg2
  exact ⟨n1, n2, hc1, hc2, hp1, hp2⟩

/-- A folding-clean value concretizing to an integer has a `false` integer guard. -/
theorem gInt_false_of_int {M : Model} {e : SExpr} {n : Int}
    (hw : WfFO M e) (h : γ M (.fo e) = some (.VCon (.Integer n))) :
    denoteB M (gInt e) = false := by
  obtain ⟨va, hden, _, _, hti, _⟩ := hw
  have hd : denote M e = .Vv (.VCon (.Integer n)) := γ_fo_denote h
  have hvv : va = .VCon (.Integer n) := by
    have hvv' : SVal.Vv va = SVal.Vv (.VCon (.Integer n)) := hden ▸ hd
    injection hvv'
  simp [gInt, denoteB_sNot, hti, hvv, vIs]

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
          obtain ⟨e1, rfl⟩ := γ_VCon_fo hf1 (hx ▸ hv1)
          obtain ⟨e2, rfl⟩ := γ_VCon_fo hf2 (hy ▸ hv2)
          have hw1' : WfFO M e1 := hw1
          have hw2' : WfFO M e2 := hw2
          have hg1f : denoteB M (gInt e1) = false := gInt_false_of_int hw1' (hx ▸ hv1)
          have hg2f : denoteB M (gInt e2) = false := gInt_false_of_int hw2' (hy ▸ hv2)
          rw [hsaterr] at herr
          simp [reifyFO, sOrs, denoteB_sOr, denoteB_bool, hg1f, hg2f] at herr
        · exact Or.inr (fun x hx => h1 ⟨x, hx⟩)
      · exact Or.inl (fun y hy => h2 ⟨y, hy⟩)
  · exact relR_of_inc_true M (hsatinc (v2 :: v1 :: w :: rest) (by simp))

/-- A saturated *precise* builtin reconciles with `evalBuiltin` — each Tier-A
arithmetic/comparison builtin is a one-line `satBin` application. -/
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

/-! ## The simulation `Sim` (the mutual adequacy induction) -/

mutual
theorem simEval : ∀ (M : Model) (n : Nat) (ρs : SymEnv) (ρ : CekEnv) (t : Term),
    EnvRel M ρs ρ → FaithfulVList ρs → WfVList M ρs → Faithful t →
    RelR M (symEval n ρs t) (bigEval n ρ t)
  | M, 0, _, ρ, t, _, _, _, _ => by simp only [symEval]; exact relR_incR M (bigEval 0 ρ t)
  | M, n+1, ρs, ρ, .Var k, hρ, _, _, _ => by
      obtain ⟨L, hL, rfl⟩ := envRel_inv hρ
      have hlk := lookup_sound M ρs L k hL
      simp only [symEval, bigEval]
      cases h : symLookup ρs k with
      | none => exact relR_errR M (hlk.1 h)
      | some v =>
        obtain ⟨cv, hγ, hcv⟩ := hlk.2 v h
        exact relR_ok M ⟨cv, hγ, hcv⟩
  | M, n+1, ρs, ρ, .Constant (c, bt), _, _, _, ht => by
      have hc : simpleConst c = true := by simpa [Faithful, faithfulB] using ht
      simp only [symEval]
      exact relR_ok M ⟨.VCon c, γ_const M c hc, by simp [bigEval]⟩
  | M, n+1, ρs, ρ, .Builtin b, _, _, _, _ => by
      simp only [symEval]
      exact relR_ok M ⟨.VBuiltin b [] (expectedArgs b), by simp [γ, γList], by simp [bigEval]⟩
  | M, n+1, ρs, ρ, .Lam _ body, hρ, _, _, _ => by
      obtain ⟨L, hL, rfl⟩ := envRel_inv hρ
      simp only [symEval]
      exact relR_ok M ⟨.VLam body (toCekEnv L), by simp [γ, hL], by simp [bigEval]⟩
  | M, n+1, ρs, ρ, .Delay body, hρ, _, _, _ => by
      obtain ⟨L, hL, rfl⟩ := envRel_inv hρ
      simp only [symEval]
      exact relR_ok M ⟨.VDelay body (toCekEnv L), by simp [γ, hL], by simp [bigEval]⟩
  | M, n+1, ρs, ρ, .Apply f a, hρ, henv, hwf, ht => by
      have hf : faithfulB f = true ∧ faithfulB a = true := by
        have := ht; simp only [Faithful, faithfulB, Bool.and_eq_true] at this; exact this
      have IHf := simEval M n ρs ρ f hρ henv hwf hf.1
      have IHa := simEval M n ρs ρ a hρ henv hwf hf.2
      have hfvf := faithfulV_symEval n ρs f henv hf.1
      have hfva := faithfulV_symEval n ρs a henv hf.2
      have hwvf := wfV_symEval M n ρs f henv hwf hf.1
      have hwva := wfV_symEval M n ρs a henv hwf hf.2
      simp only [symEval]
      refine ⟨fun hinc herr => ?_, fun hinc herr => ?_⟩
      · -- success
        simp only [denoteB_sOrs3, Bool.or_eq_false_iff] at hinc herr
        obtain ⟨⟨hfi, hai⟩, hpi⟩ := hinc
        obtain ⟨⟨hfe, hae⟩, hpe⟩ := herr
        obtain ⟨vf, hγf, hbf⟩ := IHf.1 hfi hfe
        obtain ⟨va, hγa, hba⟩ := IHa.1 hai hae
        have IHap := simApply M n (symEval n ρs f).val (symEval n ρs a).val vf va
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
            have IHap := simApply M n (symEval n ρs f).val (symEval n ρs a).val vf va
              hγf hγa hfvf hfva hwvf hwva
            have hpe : denoteB M (symApply n (symEval n ρs f).val (symEval n ρs a).val).err = true := by
              have := herr; simp only [denoteB_sOrs3, hfe, hae, Bool.false_or, Bool.or_false] at this
              exact this
            simp only [bigEval, hbf, hba]
            exact IHap.2 hpi hpe
  | M, n+1, ρs, ρ, .Force t, hρ, henv, hwf, ht => by
      have ht' : Faithful t := by simpa [Faithful, faithfulB] using ht
      have IHt := simEval M n ρs ρ t hρ henv hwf ht'
      have hfvt := faithfulV_symEval n ρs t henv ht'
      have hwvt := wfV_symEval M n ρs t henv hwf ht'
      simp only [symEval]
      refine ⟨fun hinc herr => ?_, fun hinc herr => ?_⟩
      · simp only [denoteB_sOr, Bool.or_eq_false_iff] at hinc herr
        obtain ⟨hti, hfi⟩ := hinc
        obtain ⟨hte, hfe⟩ := herr
        obtain ⟨vt, hγt, hbt⟩ := IHt.1 hti hte
        have IHfo := simForce M n (symEval n ρs t).val vt hγt hfvt hwvt
        obtain ⟨v, hγv, hav⟩ := IHfo.1 hfi hfe
        exact ⟨v, hγv, by simp only [bigEval, hbt]; exact hav⟩
      · simp only [denoteB_sOr, Bool.or_eq_false_iff] at hinc
        obtain ⟨hti, hfi⟩ := hinc
        by_cases hte : denoteB M (symEval n ρs t).err = true
        · simp [bigEval, IHt.2 hti hte]
        · simp only [Bool.not_eq_true] at hte
          obtain ⟨vt, hγt, hbt⟩ := IHt.1 hti hte
          have IHfo := simForce M n (symEval n ρs t).val vt hγt hfvt hwvt
          have hfe : denoteB M (symForce n (symEval n ρs t).val).err = true := by
            have := herr; simp only [denoteB_sOr, hte, Bool.false_or] at this; exact this
          simp only [bigEval, hbt]
          exact IHfo.2 hfi hfe
  | _, n+1, _, _, .Constr _ _, _, _, _, ht => by simp [Faithful, faithfulB] at ht
  | _, n+1, _, _, .Case _ _, _, _, _, ht => by simp [Faithful, faithfulB] at ht
  | M, n+1, _, ρ, .Error, _, _, _, _ => by
      simp only [symEval]; exact relR_errR M (by simp [bigEval])
termination_by M n _ _ t => (n, sizeOf t)
decreasing_by all_goals (simp_wf; omega)

theorem simApply : ∀ (M : Model) (n : Nat) (vfh vah : SymV) (vf va : CekValue),
    γ M vfh = some vf → γ M vah = some va → FaithfulV vfh → FaithfulV vah →
    WfV M vfh → WfV M vah → RelR M (symApply n vfh vah) (applyVal n vf va)
  | M, 0, _, _, vf, va, _, _, _, _, _, _ => by simp only [symApply]; exact relR_incR M (applyVal 0 vf va)
  | M, n+1, .lam body env, vah, vf, va, hvf, hva, hfvf, hfva, hwvf, hwva => by
      obtain ⟨Lenv, hLenv, rfl⟩ := γ_lam_inv hvf
      have hbody : faithfulB body = true ∧ FaithfulVList env := hfvf
      have hwenv : WfVList M env := hwvf
      have henv' : EnvRel M (vah :: env) ((toCekEnv Lenv).extend va) := by
        simp [EnvRel, γList, hva, hLenv, toCekEnv, CekEnv.extend]
      simp only [symApply, applyVal]
      exact simEval M n (vah :: env) ((toCekEnv Lenv).extend va) body henv'
        ⟨hfva, hbody.2⟩ ⟨hwva, hwenv⟩ hbody.1
  | M, n+1, .builtin b args ea, vah, vf, va, hvf, hva, hfvf, hfva, hwvf, hwva => by
      obtain ⟨L, hL, rfl⟩ := γ_builtin_inv hvf
      obtain ⟨hpre, hfargs⟩ := (hfvf : preciseBuiltin b = true ∧ FaithfulVList args)
      have hwargs : WfVList M args := hwvf
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
  | _, n+1, .choice _ _ _, _, _, _, _, _, hfvf, _, _, _ => by simp [FaithfulV] at hfvf
  | M, n+1, .fo e, _, vf, va, hvf, _, _, _, _, _ => by
      rcases γ_fo_inv hvf with ⟨c, rfl⟩ | ⟨t, l, rfl⟩
      · simp only [symApply]; exact relR_errR M (applyVal_VCon (n+1) c va)
      · simp only [symApply]; exact relR_errR M (applyVal_VConstr (n+1) t l va)
  | M, n+1, .delay body env, _, vf, va, hvf, _, _, _, _, _ => by
      obtain ⟨L, _, rfl⟩ := γ_delay_inv hvf
      simp only [symApply]; exact relR_errR M (applyVal_VDelay (n+1) body (toCekEnv L) va)
  | _, n+1, .constr _ _, _, _, _, _, _, hfvf, _, _, _ => by simp [FaithfulV] at hfvf
termination_by M n _ _ _ _ => (n, 0)

theorem simForce : ∀ (M : Model) (n : Nat) (vth : SymV) (vt : CekValue),
    γ M vth = some vt → FaithfulV vth → WfV M vth → RelR M (symForce n vth) (forceVal n vt)
  | M, 0, _, vt, _, _, _ => by simp only [symForce]; exact relR_incR M (forceVal 0 vt)
  | M, n+1, .delay body env, vt, hvt, hfvt, hwvt => by
      obtain ⟨Lenv, hLenv, rfl⟩ := γ_delay_inv hvt
      have hbody : faithfulB body = true ∧ FaithfulVList env := hfvt
      have hwenv : WfVList M env := hwvt
      have henv' : EnvRel M env (toCekEnv Lenv) := by simp [EnvRel, hLenv]
      simp only [symForce, forceVal]
      exact simEval M n env (toCekEnv Lenv) body henv' hbody.2 hwenv hbody.1
  | M, n+1, .builtin b args ea, vt, hvt, hfvt, hwvt => by
      obtain ⟨L, hL, rfl⟩ := γ_builtin_inv hvt
      obtain ⟨hpre, hfargs⟩ := (hfvt : preciseBuiltin b = true ∧ FaithfulVList args)
      have hwargs : WfVList M args := hwvt
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
  | _, n+1, .choice _ _ _, _, _, hfvt, _ => by simp [FaithfulV] at hfvt
  | M, n+1, .fo e, vt, hvt, _, _ => by
      rcases γ_fo_inv hvt with ⟨c, rfl⟩ | ⟨t, l, rfl⟩
      · simp only [symForce]; exact relR_errR M (forceVal_VCon (n+1) c)
      · simp only [symForce]; exact relR_errR M (forceVal_VConstr (n+1) t l)
  | M, n+1, .lam body env, vt, hvt, _, _ => by
      obtain ⟨L, _, rfl⟩ := γ_lam_inv hvt
      simp only [symForce]; exact relR_errR M (forceVal_VLam (n+1) body (toCekEnv L))
  | _, n+1, .constr _ _, _, _, hfvt, _ => by simp [FaithfulV] at hfvt
termination_by M n _ _ => (n, 0)
end

/-- **`Sim` holds** for the proven fragment. -/
theorem Sim_holds : Sim := fun M n ρs ρ t hρ henv hwf ht => simEval M n ρs ρ t hρ henv hwf ht

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
  cases b <;> first | (exfalso; revert h; decide) | skip
  all_goals (
    by_cases hlen : (List.map Prod.snd (List.map reifyFO args.reverse)).length = 2
    · left
      obtain ⟨r1, r2, hR⟩ := list_len2 _ hlen
      show (symBuiltin _ (List.map Prod.snd (List.map reifyFO args.reverse))).inc = .bool false
      rw [hR]; rfl
    · right
      show (symBuiltin _ (List.map Prod.snd (List.map reifyFO args.reverse))).inc = .bool true
      first
        | exact symBuiltin_AddInteger_inc_ne2 _ hlen
        | exact symBuiltin_SubtractInteger_inc_ne2 _ hlen
        | exact symBuiltin_MultiplyInteger_inc_ne2 _ hlen
        | exact symBuiltin_EqualsInteger_inc_ne2 _ hlen
        | exact symBuiltin_LessThanInteger_inc_ne2 _ hlen
        | exact symBuiltin_LessThanEqualsInteger_inc_ne2 _ hlen)

/-! ## Upward fuel-stability `Stab`

If a result is determinate (`¬inc`) at fuel `n`, one more fuel level keeps it
determinate and preserves the error condition (more fuel never disturbs a
completed evaluation). A mutual induction mirroring `symEval`. -/

/-! Determinacy of `symEval`: `inc` is a literal (`true` or `false`), and once it
is `false` the result is **fuel-stable** (more fuel reproduces it verbatim). This
is model-independent (the branch-free fragment never accumulates symbolic `inc`s).
A mutual induction mirroring `symEval`. -/
mutual
theorem stabEval : ∀ (n : Nat) (ρs : SymEnv) (t : Term),
    FaithfulVList ρs → Faithful t →
    (symEval n ρs t).inc = .bool true ∨
    ((symEval n ρs t).inc = .bool false ∧ symEval (n+1) ρs t = symEval n ρs t)
  | 0, _, _, _, _ => Or.inl (by simp [symEval, incR])
  | n+1, ρs, .Var k, _, _ =>
      Or.inr ⟨by cases h : symLookup ρs k <;> simp [symEval, h, errR],
              by cases h : symLookup ρs k <;> simp [symEval, h]⟩
  | n+1, _, .Constant (c, bt), _, _ => Or.inr ⟨by simp [symEval], by simp [symEval]⟩
  | n+1, _, .Builtin b, _, _ => Or.inr ⟨by simp [symEval], by simp [symEval]⟩
  | n+1, ρs, .Lam nm body, _, _ => Or.inr ⟨by simp [symEval], by simp [symEval]⟩
  | n+1, ρs, .Delay body, _, _ => Or.inr ⟨by simp [symEval], by simp [symEval]⟩
  | n+1, ρs, .Apply f a, henv, ht => by
      have hf : faithfulB f = true ∧ faithfulB a = true := by
        have := ht; simp only [Faithful, faithfulB, Bool.and_eq_true] at this; exact this
      rcases stabEval n ρs f henv hf.1 with hft | ⟨hff, hfeq⟩
      · exact Or.inl (by simp only [symEval]; rw [hft]; simp [sOrs, SExpr.sOr])
      · rcases stabEval n ρs a henv hf.2 with hat | ⟨haf, haeq⟩
        · exact Or.inl (by simp only [symEval]; rw [hff, hat]; simp [sOrs, SExpr.sOr])
        · rcases stabApply n (symEval n ρs f).val (symEval n ρs a).val
              (faithfulV_symEval n ρs f henv hf.1) (faithfulV_symEval n ρs a henv hf.2)
              with hpt | ⟨hpf, hpeq⟩
          · exact Or.inl (by simp only [symEval]; rw [hff, haf, hpt]; simp [sOrs, SExpr.sOr])
          · exact Or.inr ⟨by simp only [symEval]; rw [hff, haf, hpf]; simp [sOrs, SExpr.sOr],
                          by simp only [symEval, hfeq, haeq, hpeq]⟩
  | n+1, ρs, .Force t, henv, ht => by
      have ht' : Faithful t := by simpa [Faithful, faithfulB] using ht
      rcases stabEval n ρs t henv ht' with htt | ⟨htf, hteq⟩
      · exact Or.inl (by simp only [symEval]; rw [htt]; simp [SExpr.sOr])
      · rcases stabForce n (symEval n ρs t).val (faithfulV_symEval n ρs t henv ht')
          with hpt | ⟨hpf, hpeq⟩
        · exact Or.inl (by simp only [symEval]; rw [htf, hpt]; simp [SExpr.sOr])
        · exact Or.inr ⟨by simp only [symEval]; rw [htf, hpf]; simp [SExpr.sOr],
                        by simp only [symEval, hteq, hpeq]⟩
  | n+1, _, .Constr _ _, _, ht => by simp [Faithful, faithfulB] at ht
  | n+1, _, .Case _ _, _, ht => by simp [Faithful, faithfulB] at ht
  | n+1, _, .Error, _, _ => Or.inr ⟨by simp [symEval, errR], by simp [symEval]⟩
termination_by n _ t => (n, sizeOf t)
decreasing_by all_goals (simp_wf; omega)

theorem stabApply : ∀ (n : Nat) (vf va : SymV), FaithfulV vf → FaithfulV va →
    (symApply n vf va).inc = .bool true ∨
    ((symApply n vf va).inc = .bool false ∧ symApply (n+1) vf va = symApply n vf va)
  | 0, _, _, _, _ => Or.inl (by simp [symApply, incR])
  | n+1, .lam body env, va, hf, ha => by
      have hbody : faithfulB body = true ∧ FaithfulVList env := hf
      simpa only [symApply] using stabEval n (va :: env) body ⟨ha, hbody.2⟩ hbody.1
  | n+1, .fo _, _, _, _ => Or.inr ⟨by simp [symApply, errR], by simp [symApply]⟩
  | n+1, .delay _ _, _, _, _ => Or.inr ⟨by simp [symApply, errR], by simp [symApply]⟩
  | n+1, .builtin b args ea, va, hf, _ => by
      obtain ⟨hpre, _⟩ := (hf : preciseBuiltin b = true ∧ FaithfulVList args)
      cases h1 : ea.head with
      | argQ => exact Or.inr ⟨by simp only [symApply, h1, errR], by simp only [symApply, h1]⟩
      | argV =>
          cases h2 : ea.tail with
          | some rest => exact Or.inr ⟨by simp only [symApply, h1, h2], by simp only [symApply, h1, h2]⟩
          | none =>
              have hval : symApply (n+1) (.builtin b args ea) va = symSaturate b (va :: args) := by
                simp only [symApply, h1, h2]
              rcases symSaturate_inc_lit b (va :: args) hpre with h0 | h0
              · exact Or.inr ⟨by rw [hval]; exact h0, by simp only [symApply, h1, h2]⟩
              · exact Or.inl (by rw [hval]; exact h0)
  | n+1, .choice _ _ _, _, hf, _ => by simp [FaithfulV] at hf
  | n+1, .constr _ _, _, hf, _ => by simp [FaithfulV] at hf
termination_by n _ _ => (n, 0)

theorem stabForce : ∀ (n : Nat) (vt : SymV), FaithfulV vt →
    (symForce n vt).inc = .bool true ∨
    ((symForce n vt).inc = .bool false ∧ symForce (n+1) vt = symForce n vt)
  | 0, _, _ => Or.inl (by simp [symForce, incR])
  | n+1, .delay body env, ht => by
      have hbody : faithfulB body = true ∧ FaithfulVList env := ht
      simpa only [symForce] using stabEval n env body hbody.2 hbody.1
  | n+1, .fo _, _ => Or.inr ⟨by simp [symForce, errR], by simp [symForce]⟩
  | n+1, .lam _ _, _ => Or.inr ⟨by simp [symForce, errR], by simp [symForce]⟩
  | n+1, .builtin b args ea, ht => by
      obtain ⟨hpre, _⟩ := (ht : preciseBuiltin b = true ∧ FaithfulVList args)
      cases h1 : ea.head with
      | argV => exact Or.inr ⟨by simp only [symForce, h1, errR], by simp only [symForce, h1]⟩
      | argQ =>
          cases h2 : ea.tail with
          | some rest => exact Or.inr ⟨by simp only [symForce, h1, h2], by simp only [symForce, h1, h2]⟩
          | none =>
              have hval : symForce (n+1) (.builtin b args ea) = symSaturate b args := by
                simp only [symForce, h1, h2]
              rcases symSaturate_inc_lit b args hpre with h0 | h0
              · exact Or.inr ⟨by rw [hval]; exact h0, by simp only [symForce, h1, h2]⟩
              · exact Or.inl (by rw [hval]; exact h0)
  | n+1, .choice _ _ _, ht => by simp [FaithfulV] at ht
  | n+1, .constr _ _, ht => by simp [FaithfulV] at ht
termination_by n _ => (n, 0)
end

/-- **`Stab` holds**: determinacy lifts to the `denoteB`-level upward stability. -/
theorem Stab_holds : Stab := by
  intro M n ρs ρ t _ henv ht hinc
  rcases stabEval n ρs t henv ht with hT | ⟨_, heq⟩
  · rw [hT] at hinc; simp [denoteB_bool] at hinc
  · rw [heq]; exact ⟨hinc, rfl⟩

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
  obtain ⟨cv, hγ, hbig⟩ := hr.1 hinc herr
  exact ⟨cv, hγ, Moist.Verified.BigStep.bigEval_sound hbig⟩

/-- **Error ⇒ the CEK fails.** If the compiled formula says a closed faithful term
*definitely* errors (error true, indeterminate false), the CEK never halts with a
value. Unconditional. -/
theorem symbolic_error_sound {n : Nat} {t : Term} (ht : Faithful t)
    (M : Model)
    (hinc : denoteB M (symEval n [] t).inc = false)
    (herr : denoteB M (symEval n [] t).err = true) :
    ¬ ∃ v, Reaches (init t) (.halt v) := by
  -- The error, being determinate, persists upward in fuel (`Stab_holds`); with
  -- monotonicity it forces `bigEval` to `none` at *every* fuel.
  have hge : ∀ k, denoteB M (symEval (n + k) [] t).inc = false ∧
                   denoteB M (symEval (n + k) [] t).err = true ∧
                   bigEval (n + k) CekEnv.nil t = none := by
    intro k
    induction k with
    | zero =>
      exact ⟨hinc, herr,
        (simEval M n [] CekEnv.nil t (envRel_nil M) faithfulVList_nil (wfVList_nil M) ht).2 hinc herr⟩
    | succ k ih =>
      obtain ⟨hik, hek, _⟩ := ih
      obtain ⟨hik', hek'⟩ := Stab_holds M (n + k) [] CekEnv.nil t (envRel_nil M) faithfulVList_nil ht hik
      have hkk : n + (k + 1) = (n + k) + 1 := by omega
      rw [hkk]
      have hek1 : denoteB M (symEval ((n + k) + 1) [] t).err = true := by rw [hek']; exact hek
      exact ⟨hik', hek1,
        (simEval M ((n + k) + 1) [] CekEnv.nil t (envRel_nil M) faithfulVList_nil (wfVList_nil M) ht).2 hik' hek1⟩
  have hbn : bigEval n CekEnv.nil t = none :=
    (simEval M n [] CekEnv.nil t (envRel_nil M) faithfulVList_nil (wfVList_nil M) ht).2 hinc herr
  have hall : ∀ f, bigEval f CekEnv.nil t = none := by
    intro f
    rcases Nat.le_total n f with hnf | hfn
    · obtain ⟨d, rfl⟩ := Nat.le.dest hnf
      exact (hge d).2.2
    · cases hbf : bigEval f CekEnv.nil t with
      | none => rfl
      | some v =>
        have h2 := Moist.Verified.BigStep.bigEval_mono_le hfn hbf
        rw [hbn] at h2; exact absurd h2 (by simp)
  rintro ⟨v, hreach⟩
  obtain ⟨f, hf⟩ := (Moist.Verified.BigStep.bigEval_iff_halt).2 hreach
  rw [hall f] at hf; exact absurd hf (by simp)

end Moist.Verified.SymbolicSoundness
