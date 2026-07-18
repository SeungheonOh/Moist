import Moist.SMT.Compiler.UPLC.Compaction
import Moist.CEK.Builtins

/-!
# UPLC compiler projections and literals

Guarded projections from symbolic values plus literal re-embedding used by
both static and symbolic builtin lowering.
-/

namespace Moist.SMT.UPLC

open Moist.Plutus.Term
open Moist.Plutus (Data ByteString)

structure Proj (α : Type) where
  guard : SExpr
  val : α
deriving Repr

namespace Proj

def pure (a : α) : Proj α := ⟨SExpr.trueE, a⟩
def fail (dummy : α) : Proj α := ⟨SExpr.falseE, dummy⟩
def map (f : α → β) (p : Proj α) : Proj β := ⟨p.guard, f p.val⟩

def map2 (f : α → β → γ) (a : Proj α) (b : Proj β) : Proj γ :=
  ⟨SExpr.and a.guard b.guard, f a.val b.val⟩

def map3 (f : α → β → γ → δ) (a : Proj α) (b : Proj β) (c : Proj γ) : Proj δ :=
  ⟨SExpr.all [a.guard, b.guard, c.guard], f a.val b.val c.val⟩

end Proj

def valueProj (ctor selector : String) (dummy : SExpr) : SymVal → Proj SExpr
  | .dyn v => ⟨SExpr.isCtor ctor v, .app selector [v]⟩
  | _ => Proj.fail dummy

def asInt : SymVal → Proj SExpr
  | .const (.integer i) => Proj.pure i
  | v => valueProj "VInt" "unVInt" (.int 0) v

def asBytes : SymVal → Proj SExpr
  | .const (.bytes b) => Proj.pure b
  | v => valueProj "VBytes" "unVBytes" (SExpr.seqEmpty "Bytes") v

def asString : SymVal → Proj SExpr
  | .const (.string s) => Proj.pure s
  | v => valueProj "VString" "unVString" (.str "") v

def asBool : SymVal → Proj SExpr
  | .const (.bool b) => Proj.pure b
  | v => valueProj "VBool" "unVBool" (.bool false) v

def asData : SymVal → Proj SExpr
  | .const (.data d) => Proj.pure d
  | v => valueProj "VData" "unVData" (.app "DI" [.int 0]) v

def asDataList : SymVal → Proj SExpr
  | .const (.dataList xs) => Proj.pure xs
  | .const (.constList _ _) => ⟨SExpr.falseE, .app "DNil" []⟩
  | v => valueProj "VDataList" "unVDataList" (.app "DNil" []) v

def asPairDataList : SymVal → Proj SExpr
  | .const (.pairDataList xs) => Proj.pure xs
  | v => valueProj "VPairDataList" "unVPairDataList" (.app "DPNil" []) v

def asConstList : SymVal → Proj SExpr
  | .const (.constList xs _) => Proj.pure xs
  | v => valueProj "VList" "unVList" (.app "VNil" []) v

def knownConstListLength : SymVal → Option Nat
  | .const (.constList expr hint) => hint.knownLength expr
  | _ => none

def consConstListValue (head : SExpr) : SymVal → SymVal
  | .const (.constList tail hint) =>
      .const (.constList (.app "VCons" [head, tail]) (.cons head hint))
  | value =>
      let tail := (asConstList value).val
      .const (.constList (.app "VCons" [head, tail]) .unknown)

def tailConstListValue : SymVal → SymVal
  | .const (.constList xs hint) =>
      .const (.constList (.app "vtail" [xs]) (.tail hint))
  | value =>
      let xs := (asConstList value).val
      .const (.constList (.app "vtail" [xs]) .unknown)

/-- Select the constant-list alternatives that can be reachable at a known
length.  This is intentionally only a selector: the outcomes themselves keep
their ordinary SMT constructor guards. -/
def constListBranches (hint : Option Nat) (nilOutcome consOutcome : Outcome) :
    List Outcome :=
  match hint with
  | some 0 => [nilOutcome]
  | some (_ + 1) => [consOutcome]
  | none => [nilOutcome, consOutcome]

def asArray : SymVal → Proj SExpr
  | .const (.array xs) => Proj.pure xs
  | v => valueProj "VArray" "unVArray" (.app "VNil" []) v

def asG1 : SymVal → Proj SExpr
  | .const (.g1 g) => Proj.pure g
  | v => valueProj "VG1" "unVG1" (.sym "g1_default") v

def asG2 : SymVal → Proj SExpr
  | .const (.g2 g) => Proj.pure g
  | v => valueProj "VG2" "unVG2" (.sym "g2_default") v

def asMl : SymVal → Proj SExpr
  | .const (.ml r) => Proj.pure r
  | v => valueProj "VMlResult" "unVMlResult" (.sym "ml_default") v

def asPairData : SymVal → Proj (SExpr × SExpr)
  | .const (.pairData a b) => Proj.pure (a, b)
  | .dyn v => ⟨SExpr.isCtor "VPairData" v, (.app "pdfst" [v], .app "pdsnd" [v])⟩
  | _ => Proj.fail (.app "DI" [.int 0], .app "DI" [.int 0])

def asPair : SymVal → Proj (SymVal × SymVal)
  | .pair a b => Proj.pure (a, b)
  | .dyn v => ⟨SExpr.isCtor "VPair" v, (.dyn (.app "vfst" [v]), .dyn (.app "vsnd" [v]))⟩
  | _ => Proj.fail (.dyn (.app "VUnit" []), .dyn (.app "VUnit" []))

def asConstVal : SymVal → Proj SExpr
  | .const c =>
      match encodeVal? (.const c) with
      | some v => Proj.pure v
      | none => Proj.fail (.app "VUnit" [])
  | .dyn v => ⟨.app "const_val_valid" [v], v⟩
  | .pair a b =>
      let a' := asConstVal a
      let b' := asConstVal b
      ⟨SExpr.and a'.guard b'.guard, .app "VPair" [a'.val, b'.val]⟩
  | .constr _ _ | .lam _ _ | .delay _ _ | .builtin _ _ _ =>
      Proj.fail (.app "VUnit" [])

def unitGuard : SymVal → SExpr
  | .const .unit => SExpr.trueE
  | .dyn v => SExpr.isCtor "VUnit" v
  | _ => SExpr.falseE

def checked1 (p : Proj α) (mk : α → SymVal) : List Outcome :=
  [.ok p.guard (mk p.val), .error (SExpr.not p.guard)]

def checkedBool (p : Proj SExpr) : List Outcome :=
  checked1 p (fun b => .const (.bool b))

def checkedConst (p : Proj SExpr) (mk : SExpr → SymConst) : List Outcome :=
  checked1 p (fun e => .const (mk e))

def checked2 (p : Proj α) (mk : α → List Outcome) : List Outcome :=
  (mk p.val).map (Outcome.guard p.guard) ++ [.error (SExpr.not p.guard)]

def bytesLiteral (bs : ByteString) : SExpr :=
  .bytes bs

mutual
  def dataLiteral : Data → SExpr
    | d => .dataLit d

  def dataListLiteral : List Data → SExpr
    | xs => .dataListLit xs

  def dataPairListLiteral : List (Data × Data) → SExpr
    | xs => .dataPairListLit xs
end

def constLiteral : Const → SymVal
  | .Integer i => .const (.integer (.int i))
  | .ByteString bs => .const (.bytes (bytesLiteral bs))
  | .String s => .const (.string (.str s))
  | .Unit => .const .unit
  | .Bool b => .const (.bool (.bool b))
  | .ConstList xs => .const (.constList (.constListLit xs) (.literal xs))
  | .ConstDataList xs => .const (.dataList (dataListLiteral xs))
  | .ConstPairDataList xs => .const (.pairDataList (dataPairListLiteral xs))
  | .Pair (a, b) => .pair (constLiteral a) (constLiteral b)
  | .PairData (a, b) => .const (.pairData (dataLiteral a) (dataLiteral b))
  | .Data d => .const (.data (dataLiteral d))
  | .ConstArray xs => .const (.array (.constListLit xs))
  | .Bls12_381_G1_element => .const (.g1 (.sym "g1_default"))
  | .Bls12_381_G2_element => .const (.g2 (.sym "g2_default"))
  | .Bls12_381_MlResult => .const (.ml (.sym "ml_default"))


end Moist.SMT.UPLC

