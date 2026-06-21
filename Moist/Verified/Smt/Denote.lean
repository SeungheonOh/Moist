import Moist.Verified.Smt.Model
import Moist.Verified.BigStep

/-! # Stage 2 — decoding & denotation (defs only)

The semantic-universe → reference-runtime decode (`decodeV`/`decodeD`), the model
well-formedness predicates (`WF*`), and the denotation of a symbolic value / environment
/ result (`denoteSymV`/`denoteEnv`/`denote{Inc,Err,Val}`). Kept separate from the
soundness *theorems* (`Soundness.lean`) so the simulation lemma files can depend on these
defs without an import cycle. -/

namespace Moist.Verified.Smt

open Moist.Symbolic
open Moist.CEK
open Moist.Plutus (Data ByteString)
open Moist.Plutus.Term (Const)

/-! ## Decoding the semantic universe to reference runtime values -/

/-- A semantic byte sequence to a `ByteArray` (truncating; exact under `WFSeq`). -/
def bytesToBA (s : List Int) : ByteArray := ⟨(s.map (fun n => UInt8.ofNat n.toNat)).toArray⟩

mutual
/-- Decode semantic `Data` to `Plutus.Data`. -/
def decodeD : SemD → Data
  | .constr i dl => .Constr i (decodeDL dl)
  | .map dm      => .Map (decodeDM dm)
  | .list dl     => .List (decodeDL dl)
  | .i n         => .I n
  | .b s         => .B (bytesToBA s)
/-- Decode a `SemDL` to `List Data`. -/
def decodeDL : SemDL → List Data
  | .nil      => []
  | .cons h t => decodeD h :: decodeDL t
/-- Decode a `SemDM` to `List (Data × Data)`. -/
def decodeDM : SemDM → List (Data × Data)
  | .nil        => []
  | .cons k v t => (decodeD k, decodeD v) :: decodeDM t
end

/-- Extract the `Const` carried by a first-order `CekValue` (junk on `VConstr`, which a
well-formed `ConstList`/`Pair`/`ConstArray` element never is). -/
def cekToConst : CekValue → Const
  | .VCon c => c
  | _       => .Unit

mutual
/-- Decode a semantic value to a reference `CekValue`. -/
def decodeV : SemV → CekValue
  | .int n    => .VCon (.Integer n)
  | .bs s     => .VCon (.ByteString (bytesToBA s))
  | .bool b   => .VCon (.Bool b)
  | .unit     => .VCon .Unit
  | .str s    => .VCon (.String s)
  | .data d   => .VCon (.Data (decodeD d))
  | .list vl  => .VCon (.ConstList ((decodeVL vl).map cekToConst))
  | .dlist dl => .VCon (.ConstDataList (decodeDL dl))
  | .pdlist dm=> .VCon (.ConstPairDataList (decodeDM dm))
  | .pair a b => .VCon (.Pair (cekToConst (decodeV a), cekToConst (decodeV b)))
  | .pairD a b=> .VCon (.PairData (decodeD a, decodeD b))
  | .arr vl   => .VCon (.ConstArray ((decodeVL vl).map cekToConst))
  | .constr tag fields => .VConstr tag.toNat (decodeVL fields)
  | .g1       => .VCon .Bls12_381_G1_element
  | .g2       => .VCon .Bls12_381_G2_element
  | .ml       => .VCon .Bls12_381_MlResult
/-- Decode a `SemVL` to `List CekValue`. -/
def decodeVL : SemVL → List CekValue
  | .nil      => []
  | .cons h t => decodeV h :: decodeVL t
end

/-! ## Well-formedness of a model (byte ranges) -/

/-- Every element of a semantic byte sequence is a real byte (`0..255`). -/
def WFSeq (s : List Int) : Prop := ∀ x ∈ s, 0 ≤ x ∧ x ≤ 255

mutual
def WFD : SemD → Prop
  | .constr _ dl => WFDL dl
  | .map dm      => WFDM dm
  | .list dl     => WFDL dl
  | .i _         => True
  | .b s         => WFSeq s
def WFDL : SemDL → Prop
  | .nil      => True
  | .cons h t => WFD h ∧ WFDL t
def WFDM : SemDM → Prop
  | .nil        => True
  | .cons k v t => WFD k ∧ WFD v ∧ WFDM t
end

mutual
def WFV : SemV → Prop
  | .int _     => True
  | .bs s      => WFSeq s
  | .bool _    => True
  | .unit      => True
  | .str _     => True
  | .data d    => WFD d
  | .list vl   => WFVL vl
  | .dlist dl  => WFDL dl
  | .pdlist dm => WFDM dm
  | .pair a b  => WFV a ∧ WFV b
  | .pairD a b => WFD a ∧ WFD b
  | .arr vl    => WFVL vl
  | .constr _ fields => WFVL fields
  | .g1 => True | .g2 => True | .ml => True
def WFVL : SemVL → Prop
  | .nil      => True
  | .cons h t => WFV h ∧ WFVL t
end

/-- Well-formedness of a `Dyn` (only the value-carrying sorts constrain bytes). -/
def WFDyn : Dyn → Prop
  | .seq s => WFSeq s
  | .d x   => WFD x
  | .dl x  => WFDL x
  | .dm x  => WFDM x
  | .v x   => WFV x
  | .vl x  => WFVL x
  | _      => True

mutual
/-- Well-formedness of a symbolic value under model `M` (recursively WF byte ranges;
closures require their captured environments WF). -/
def WFSymVal (M : Model) : SymV → Prop
  | .fo e          => WFDyn (evalDyn M e)
  | .lam _ ρ       => WFSymEnv M ρ
  | .delay _ ρ     => WFSymEnv M ρ
  | .constr _ fs   => WFSymList M fs
  | .builtin _ a _ => WFSymList M a
  | .choice c a b  => if (evalDyn M c).toBool then WFSymVal M a else WFSymVal M b
def WFSymList (M : Model) : List SymV → Prop
  | []      => True
  | v :: vs => WFSymVal M v ∧ WFSymList M vs
def WFSymEnv (M : Model) : SymEnv → Prop
  | []      => True
  | v :: vs => WFSymVal M v ∧ WFSymEnv M vs
end

/-! ## Denoting a symbolic value / environment / result -/

mutual
/-- Denote a symbolic value to a `CekValue` under model `M`. -/
def denoteSymV (M : Model) : SymV → CekValue
  | .fo e          => decodeV (evalDyn M e).toV
  | .lam body ρ    => .VLam body (denoteEnv M ρ)
  | .delay body ρ  => .VDelay body (denoteEnv M ρ)
  | .constr tag fs => .VConstr tag (denoteSymList M fs)
  | .builtin b a ea=> .VBuiltin b (denoteSymList M a) ea
  | .choice c a b  => if (evalDyn M c).toBool then denoteSymV M a else denoteSymV M b
def denoteSymList (M : Model) : List SymV → List CekValue
  | []      => []
  | v :: vs => denoteSymV M v :: denoteSymList M vs
/-- Denote a symbolic environment to a `CekEnv` (head = `Var 1`, order preserved). -/
def denoteEnv (M : Model) : SymEnv → CekEnv
  | []      => .nil
  | v :: vs => .cons (denoteSymV M v) (denoteEnv M vs)
end

/-- The model truth value of the indeterminate condition. -/
def denoteInc (M : Model) (r : SymR) : Bool := (evalDyn M r.inc).toBool
/-- The model truth value of the error condition. -/
def denoteErr (M : Model) (r : SymR) : Bool := (evalDyn M r.err).toBool
/-- The model value of the result. -/
def denoteVal (M : Model) (r : SymR) : CekValue := denoteSymV M r.val

end Moist.Verified.Smt
