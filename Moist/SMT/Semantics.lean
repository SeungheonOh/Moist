import Moist.SMT.Basic
import Moist.Plutus.ByteString
import Moist.Plutus.DecidableEq
import Moist.Plutus.Integer

namespace Moist.SMT.Semantics

open Moist.Plutus
open Moist.Plutus.Term

/-!
Executable denotational semantics for the first-order SMT expression layer used
by `Moist.SMT.UPLC`.  This is intentionally a semantics for our small `Expr`
AST, not a verifier for Z3.  A later Z3 bridge should say that a Z3 model for
the rendered SMTLib script denotes one of these `Model`s.
-/

mutual
  inductive Val where
    | int : Int → Val
    | bytes : ByteArray → Val
    | string : String → Val
    | bool : Bool → Val
    | unit : Val
    | list : List Val → Val
    | dataList : List Data → Val
    | pairDataList : List (Data × Data) → Val
    | pair : Val → Val → Val
    | pairData : Data → Data → Val
    | data : Data → Val
    | array : List Val → Val
    | g1 : String → Val
    | g2 : String → Val
    | ml : String → Val
    | constr : Int → List Val → Val
  deriving Repr

  inductive SVal where
    | bool : Bool → SVal
    | int : Int → SVal
    | string : String → SVal
    | bytes : ByteArray → SVal
    | data : Data → SVal
    | dataList : List Data → SVal
    | dataPairList : List (Data × Data) → SVal
    | val : Val → SVal
    | valList : List Val → SVal
    | g1 : String → SVal
    | g2 : String → SVal
    | ml : String → SVal
  deriving Repr
end

structure Model where
  valueOf : String → Option SVal

namespace Model

def empty : Model := ⟨fun _ => none⟩

def bind (m : Model) (name : String) (v : SVal) : Model :=
  ⟨fun x => if x == name then some v else m.valueOf x⟩

end Model

def bytesEmpty : ByteArray := ByteArray.empty

@[irreducible] def bytesSingletonValue (n : Int) : ByteArray :=
  Moist.Plutus.bytesSingletonValue n

@[irreducible] def bytesNthValue (bs : ByteArray) (i : Int) : Int :=
  Moist.Plutus.bytesNthValue bs i

@[irreducible] def bytesExtractValue (bs : ByteArray) (start len : Int) : ByteArray :=
  Moist.Plutus.bytesExtractValue bs start len

def bytesSingleton (n : Int) : Option ByteArray :=
  Moist.Plutus.bytesSingleton? n

private def bytesNth (bs : ByteArray) (i : Int) : Option Int :=
  Moist.Plutus.bytesNth? bs i

private def bytesExtract (bs : ByteArray) (start len : Int) : ByteArray :=
  Moist.Plutus.bytesExtractValue bs start len

private def bsLt (a b : ByteArray) : Bool :=
  Moist.Plutus.bytesLt a b

private def bsLe (a b : ByteArray) : Bool :=
  Moist.Plutus.bytesLe a b

private def sameSign (a b : Int) : Bool := (a >= 0) == (b >= 0)

private def haskellDiv (a b : Int) : Int :=
  Moist.Plutus.uplcIntegerDiv a b

private def haskellMod (a b : Int) : Int :=
  Moist.Plutus.uplcIntegerMod a b

mutual
  private def constValValid : Val → Bool
    | .int _ | .bytes _ | .string _ | .bool _ | .unit | .data _
    | .dataList _ | .pairDataList _ | .pairData _ _
    | .g1 _ | .g2 _ | .ml _ => true
    | .list xs => constValListValid xs
    | .pair a b => constValValid a && constValValid b
    | .array xs => constValListValid xs
    | .constr _ _ => false

  private def constValListValid : List Val → Bool
    | [] => true
    | x :: xs => constValValid x && constValListValid xs
end

mutual
  private def valValid : Val → Bool
    | .constr tag fields => tag >= 0 && valListValid fields
    | .list xs => constValListValid xs
    | .pair a b => constValValid a && constValValid b
    | .array xs => constValListValid xs
    | v => constValValid v

  private def valListValid : List Val → Bool
    | [] => true
    | x :: xs => valValid x && valListValid xs
end

private def isCtor (ctor : String) : SVal → Option Bool
  | .data (.Constr _ _) => some (ctor == "DConstr")
  | .data (.Map _) => some (ctor == "DMap")
  | .data (.List _) => some (ctor == "DList")
  | .data (.I _) => some (ctor == "DI")
  | .data (.B _) => some (ctor == "DB")
  | .dataList [] => some (ctor == "DNil")
  | .dataList (_ :: _) => some (ctor == "DCons")
  | .dataPairList [] => some (ctor == "DPNil")
  | .dataPairList (_ :: _) => some (ctor == "DPCons")
  | .val (.int _) => some (ctor == "VInt")
  | .val (.bytes _) => some (ctor == "VBytes")
  | .val (.string _) => some (ctor == "VString")
  | .val (.bool _) => some (ctor == "VBool")
  | .val .unit => some (ctor == "VUnit")
  | .val (.list _) => some (ctor == "VList")
  | .val (.dataList _) => some (ctor == "VDataList")
  | .val (.pairDataList _) => some (ctor == "VPairDataList")
  | .val (.pair _ _) => some (ctor == "VPair")
  | .val (.pairData _ _) => some (ctor == "VPairData")
  | .val (.data _) => some (ctor == "VData")
  | .val (.array _) => some (ctor == "VArray")
  | .val (.g1 _) => some (ctor == "VG1")
  | .val (.g2 _) => some (ctor == "VG2")
  | .val (.ml _) => some (ctor == "VMlResult")
  | .val (.constr _ _) => some (ctor == "VConstr")
  | .valList [] => some (ctor == "VNil")
  | .valList (_ :: _) => some (ctor == "VCons")
  | _ => none

private def isVIntSVal : SVal → Option Bool
  | .val (.int _) => some true
  | .val _ => some false
  | .data _ => some false
  | .dataList _ => some false
  | .dataPairList _ => some false
  | .valList _ => some false
  | _ => none

private def isVBoolSVal : SVal → Option Bool
  | .val (.bool _) => some true
  | .val _ => some false
  | .data _ => some false
  | .dataList _ => some false
  | .dataPairList _ => some false
  | .valList _ => some false
  | _ => none

private def valEq : Val → Val → Bool
  | .int a, .int b => a == b
  | .bytes a, .bytes b => a == b
  | .string a, .string b => a == b
  | .bool a, .bool b => a == b
  | .unit, .unit => true
  | .list as, .list bs => listEq as bs
  | .dataList as, .dataList bs => as == bs
  | .pairDataList as, .pairDataList bs => as == bs
  | .pair a₁ a₂, .pair b₁ b₂ => valEq a₁ b₁ && valEq a₂ b₂
  | .pairData a₁ a₂, .pairData b₁ b₂ => a₁ == b₁ && a₂ == b₂
  | .data a, .data b => a == b
  | .array as, .array bs => listEq as bs
  | .g1 a, .g1 b => a == b
  | .g2 a, .g2 b => a == b
  | .ml a, .ml b => a == b
  | .constr ta as, .constr tb bs => ta == tb && listEq as bs
  | _, _ => false
where
  listEq : List Val → List Val → Bool
    | [], [] => true
    | a :: as, b :: bs => valEq a b && listEq as bs
    | _, _ => false

private def svalEq : SVal → SVal → Bool
  | .bool a, .bool b => a == b
  | .int a, .int b => a == b
  | .string a, .string b => a == b
  | .bytes a, .bytes b => a == b
  | .data a, .data b => a == b
  | .dataList a, .dataList b => a == b
  | .dataPairList a, .dataPairList b => a == b
  | .val a, .val b => valEq a b
  | .valList a, .valList b => go a b
  | .g1 a, .g1 b => a == b
  | .g2 a, .g2 b => a == b
  | .ml a, .ml b => a == b
  | _, _ => false
where
  go : List Val → List Val → Bool
    | [], [] => true
    | a :: as, b :: bs => valEq a b && go as bs
    | _, _ => false

mutual
  def constToVal : Const → Val
    | .Integer i => .int i
    | .ByteString bs => .bytes bs
    | .String s => .string s
    | .Unit => .unit
    | .Bool b => .bool b
    | .ConstList xs => .list (constListToVals xs)
    | .ConstDataList xs => .dataList xs
    | .ConstPairDataList xs => .pairDataList xs
    | .Pair (a, b) => .pair (constToVal a) (constToVal b)
    | .PairData (a, b) => .pairData a b
    | .Data d => .data d
    | .ConstArray xs => .array (constListToVals xs)
    | .Bls12_381_G1_element => .g1 "g1_default"
    | .Bls12_381_G2_element => .g2 "g2_default"
    | .Bls12_381_MlResult => .ml "ml_default"

  def constListToVals : List Const → List Val
    | [] => []
    | c :: cs => constToVal c :: constListToVals cs
end

private def evalIsCtorApp (f : String) (args : List SVal) : Option SVal :=
  match f, args with
  | "(_ is DConstr)", [v] => (isCtor "DConstr" v).map SVal.bool
  | "(_ is DMap)", [v] => (isCtor "DMap" v).map SVal.bool
  | "(_ is DList)", [v] => (isCtor "DList" v).map SVal.bool
  | "(_ is DI)", [v] => (isCtor "DI" v).map SVal.bool
  | "(_ is DB)", [v] => (isCtor "DB" v).map SVal.bool
  | "(_ is DNil)", [v] => (isCtor "DNil" v).map SVal.bool
  | "(_ is DCons)", [v] => (isCtor "DCons" v).map SVal.bool
  | "(_ is DPNil)", [v] => (isCtor "DPNil" v).map SVal.bool
  | "(_ is DPCons)", [v] => (isCtor "DPCons" v).map SVal.bool
  | "(_ is VInt)", [v] => (isCtor "VInt" v).map SVal.bool
  | "(_ is VBytes)", [v] => (isCtor "VBytes" v).map SVal.bool
  | "(_ is VString)", [v] => (isCtor "VString" v).map SVal.bool
  | "(_ is VBool)", [v] => (isCtor "VBool" v).map SVal.bool
  | "(_ is VUnit)", [v] => (isCtor "VUnit" v).map SVal.bool
  | "(_ is VList)", [v] => (isCtor "VList" v).map SVal.bool
  | "(_ is VDataList)", [v] => (isCtor "VDataList" v).map SVal.bool
  | "(_ is VPairDataList)", [v] => (isCtor "VPairDataList" v).map SVal.bool
  | "(_ is VPair)", [v] => (isCtor "VPair" v).map SVal.bool
  | "(_ is VPairData)", [v] => (isCtor "VPairData" v).map SVal.bool
  | "(_ is VData)", [v] => (isCtor "VData" v).map SVal.bool
  | "(_ is VArray)", [v] => (isCtor "VArray" v).map SVal.bool
  | "(_ is VG1)", [v] => (isCtor "VG1" v).map SVal.bool
  | "(_ is VG2)", [v] => (isCtor "VG2" v).map SVal.bool
  | "(_ is VMlResult)", [v] => (isCtor "VMlResult" v).map SVal.bool
  | "(_ is VConstr)", [v] => (isCtor "VConstr" v).map SVal.bool
  | "(_ is VNil)", [v] => (isCtor "VNil" v).map SVal.bool
  | "(_ is VCons)", [v] => (isCtor "VCons" v).map SVal.bool
  | _, _ => none

private def evalApp (f : String) (vs : List SVal) : Option SVal :=
  match evalIsCtorApp f vs with
  | some v => some v
  | none =>
    match f, vs with
      | "not", [.bool a] => some (.bool (!a))
      | "and", [.bool a, .bool b] => some (.bool (a && b))
      | "or", [.bool a, .bool b] => some (.bool (a || b))
      | "=", [a, b] => some (.bool (svalEq a b))
      | "+", [.int a, .int b] => some (.int (a + b))
      | "-", [.int a, .int b] => some (.int (a - b))
      | "*", [.int a, .int b] => some (.int (a * b))
      | "<", [.int a, .int b] => some (.bool (a < b))
      | "<=", [.int a, .int b] => some (.bool (a <= b))
      | ">", [.int a, .int b] => some (.bool (a > b))
      | ">=", [.int a, .int b] => some (.bool (a >= b))
      | "seq.unit", [.int n] => SVal.bytes <$> bytesSingleton n
      | "seq.++", [.bytes a, .bytes b] => some (.bytes (a ++ b))
      | "seq.len", [.bytes a] => some (.int (Int.ofNat a.size))
      | "seq.nth", [.bytes a, .int i] => SVal.int <$> bytesNth a i
      | "seq.extract", [.bytes a, .int start, .int len] => some (.bytes (bytesExtract a start len))
      | "str.++", [.string a, .string b] => some (.string (a ++ b))
      | "same_sign", [.int a, .int b] => some (.bool (sameSign a b))
      | "abs_int", [.int a] => some (.int (Int.ofNat a.natAbs))
      | "uplc_tdiv", [.int a, .int b] => if b == 0 then none else some (.int (a.tdiv b))
      | "uplc_tmod", [.int a, .int b] => if b == 0 then none else some (.int (a.tmod b))
      | "uplc_div", [.int a, .int b] => if b == 0 then none else some (.int (haskellDiv a b))
      | "uplc_mod", [.int a, .int b] => if b == 0 then none else some (.int (haskellMod a b))
      | "bytes_lt", [.bytes a, .bytes b] => some (.bool (bsLt a b))
      | "bytes_le", [.bytes a, .bytes b] => some (.bool (bsLe a b))
      | "bytes_valid", [.bytes _] => some (.bool true)
      | "data_valid", [.data _] => some (.bool true)
      | "dlist_valid", [.dataList _] => some (.bool true)
      | "dplist_valid", [.dataPairList _] => some (.bool true)
      | "val_valid", [.val v] => some (.bool (valValid v))
      | "vlist_valid", [.valList xs] => some (.bool (xs.all valValid))
      | "const_val_valid", [.val v] => some (.bool (constValValid v))
      | "const_vlist_valid", [.valList xs] => some (.bool (xs.all constValValid))
      | "VInt", [.int i] => some (.val (.int i))
      | "VBytes", [.bytes bs] => some (.val (.bytes bs))
      | "VString", [.string s] => some (.val (.string s))
      | "VBool", [.bool b] => some (.val (.bool b))
      | "VUnit", [] => some (.val .unit)
      | "VList", [.valList xs] => some (.val (.list xs))
      | "VDataList", [.dataList xs] => some (.val (.dataList xs))
      | "VPairDataList", [.dataPairList xs] => some (.val (.pairDataList xs))
      | "VPair", [.val a, .val b] => some (.val (.pair a b))
      | "VPairData", [.data a, .data b] => some (.val (.pairData a b))
      | "VData", [.data d] => some (.val (.data d))
      | "VArray", [.valList xs] => some (.val (.array xs))
      | "VG1", [.g1 g] => some (.val (.g1 g))
      | "VG2", [.g2 g] => some (.val (.g2 g))
      | "VMlResult", [.ml r] => some (.val (.ml r))
      | "VConstr", [.int tag, .valList fields] => some (.val (.constr tag fields))
      | "VNil", [] => some (.valList [])
      | "VCons", [.val h, .valList t] => some (.valList (h :: t))
      | "unVInt", [.val (.int i)] => some (.int i)
      | "unVBytes", [.val (.bytes bs)] => some (.bytes bs)
      | "unVString", [.val (.string s)] => some (.string s)
      | "unVBool", [.val (.bool b)] => some (.bool b)
      | "unVList", [.val (.list xs)] => some (.valList xs)
      | "unVDataList", [.val (.dataList xs)] => some (.dataList xs)
      | "unVPairDataList", [.val (.pairDataList xs)] => some (.dataPairList xs)
      | "vfst", [.val (.pair a _)] => some (.val a)
      | "vsnd", [.val (.pair _ b)] => some (.val b)
      | "pdfst", [.val (.pairData a _)] => some (.data a)
      | "pdsnd", [.val (.pairData _ b)] => some (.data b)
      | "unVData", [.val (.data d)] => some (.data d)
      | "unVArray", [.val (.array xs)] => some (.valList xs)
      | "vConstrTag", [.val (.constr tag _)] => some (.int tag)
      | "vConstrFields", [.val (.constr _ fields)] => some (.valList fields)
      | "vhead", [.valList (h :: _)] => some (.val h)
      | "vtail", [.valList (_ :: t)] => some (.valList t)
      | "vlist_length", [.valList xs] => some (.int (Int.ofNat xs.length))
      | "vlist_drop", [.int n, .valList xs] =>
          some (.valList (if n < 0 then xs else xs.drop n.toNat))
      | "vlist_index", [.int n, .valList xs] =>
          if n < 0 then none else SVal.val <$> xs[n.toNat]?
      | "DConstr", [.int tag, .dataList fields] => some (.data (.Constr tag fields))
      | "DMap", [.dataPairList ps] => some (.data (.Map ps))
      | "DList", [.dataList xs] => some (.data (.List xs))
      | "DI", [.int i] => some (.data (.I i))
      | "DB", [.bytes bs] => some (.data (.B bs))
      | "dataConstrTag", [.data (.Constr tag _)] => some (.int tag)
      | "dataConstrFields", [.data (.Constr _ fields)] => some (.dataList fields)
      | "dataMapEntries", [.data (.Map ps)] => some (.dataPairList ps)
      | "dataListItems", [.data (.List xs)] => some (.dataList xs)
      | "dataInt", [.data (.I i)] => some (.int i)
      | "dataBytes", [.data (.B bs)] => some (.bytes bs)
      | "DNil", [] => some (.dataList [])
      | "DCons", [.data h, .dataList t] => some (.dataList (h :: t))
      | "dhead", [.dataList (h :: _)] => some (.data h)
      | "dtail", [.dataList (_ :: t)] => some (.dataList t)
      | "dlist_length", [.dataList xs] => some (.int (Int.ofNat xs.length))
      | "dlist_drop", [.int n, .dataList xs] =>
          some (.dataList (if n < 0 then xs else xs.drop n.toNat))
      | "DPNil", [] => some (.dataPairList [])
      | "DPCons", [.data k, .data v, .dataPairList t] => some (.dataPairList ((k, v) :: t))
      | "dpKey", [.dataPairList ((k, _) :: _)] => some (.data k)
      | "dpValue", [.dataPairList ((_, v) :: _)] => some (.data v)
      | "dpTail", [.dataPairList (_ :: t)] => some (.dataPairList t)
      | _, _ => none

private theorem evalApp_unVBytes (bs : ByteArray) :
    evalApp "unVBytes" [SVal.val (Val.bytes bs)] = some (SVal.bytes bs) := by
  rfl

private theorem evalApp_unVString (s : String) :
    evalApp "unVString" [SVal.val (Val.string s)] = some (SVal.string s) := by
  rfl

private theorem evalApp_unVData (d : Data) :
    evalApp "unVData" [SVal.val (Val.data d)] = some (SVal.data d) := by
  rfl

private theorem evalApp_unVDataList (xs : List Data) :
    evalApp "unVDataList" [SVal.val (Val.dataList xs)] = some (SVal.dataList xs) := by
  rfl

private theorem evalApp_unVPairDataList (xs : List (Data × Data)) :
    evalApp "unVPairDataList" [SVal.val (Val.pairDataList xs)] =
      some (SVal.dataPairList xs) := by
  rfl

private theorem evalApp_unVList (xs : List Val) :
    evalApp "unVList" [SVal.val (Val.list xs)] = some (SVal.valList xs) := by
  rfl

private theorem evalApp_unVArray (xs : List Val) :
    evalApp "unVArray" [SVal.val (Val.array xs)] = some (SVal.valList xs) := by
  rfl

private theorem evalApp_constValValid_constr_false (tag : Int) (fields : List Val) :
    evalApp "const_val_valid" [SVal.val (Val.constr tag fields)] =
      some (SVal.bool false) := by
  rfl

private theorem evalApp_vfst (a b : Val) :
    evalApp "vfst" [SVal.val (Val.pair a b)] = some (SVal.val a) := by
  rfl

private theorem evalApp_vsnd (a b : Val) :
    evalApp "vsnd" [SVal.val (Val.pair a b)] = some (SVal.val b) := by
  rfl

private theorem evalApp_pdfst (a b : Data) :
    evalApp "pdfst" [SVal.val (Val.pairData a b)] = some (SVal.data a) := by
  rfl

private theorem evalApp_pdsnd (a b : Data) :
    evalApp "pdsnd" [SVal.val (Val.pairData a b)] = some (SVal.data b) := by
  rfl

private theorem evalApp_vConstrTag (tag : Int) (fields : List Val) :
    evalApp "vConstrTag" [SVal.val (Val.constr tag fields)] = some (SVal.int tag) := by
  rfl

private theorem evalApp_vConstrFields (tag : Int) (fields : List Val) :
    evalApp "vConstrFields" [SVal.val (Val.constr tag fields)] = some (SVal.valList fields) := by
  rfl

private theorem evalApp_vhead (h : Val) (t : List Val) :
    evalApp "vhead" [SVal.valList (h :: t)] = some (SVal.val h) := by
  rfl

private theorem evalApp_vtail (h : Val) (t : List Val) :
    evalApp "vtail" [SVal.valList (h :: t)] = some (SVal.valList t) := by
  rfl

private theorem evalApp_dhead (h : Data) (t : List Data) :
    evalApp "dhead" [SVal.dataList (h :: t)] = some (SVal.data h) := by
  rfl

private theorem evalApp_dtail (h : Data) (t : List Data) :
    evalApp "dtail" [SVal.dataList (h :: t)] = some (SVal.dataList t) := by
  rfl

private theorem evalApp_add (a b : Int) :
    evalApp "+" [SVal.int a, SVal.int b] = some (SVal.int (a + b)) := by
  rfl

private theorem evalApp_sub (a b : Int) :
    evalApp "-" [SVal.int a, SVal.int b] = some (SVal.int (a - b)) := by
  rfl

private theorem evalApp_mul (a b : Int) :
    evalApp "*" [SVal.int a, SVal.int b] = some (SVal.int (a * b)) := by
  rfl

private theorem evalApp_eq_int (a b : Int) :
    evalApp "=" [SVal.int a, SVal.int b] = some (SVal.bool (a == b)) := by
  rfl

private theorem evalApp_lt (a b : Int) :
    evalApp "<" [SVal.int a, SVal.int b] = some (SVal.bool (a < b)) := by
  rfl

private theorem evalApp_le (a b : Int) :
    evalApp "<=" [SVal.int a, SVal.int b] = some (SVal.bool (a <= b)) := by
  rfl

private theorem evalApp_ge (a b : Int) :
    evalApp ">=" [SVal.int a, SVal.int b] = some (SVal.bool (a >= b)) := by
  rfl

private theorem evalApp_eq_bytes (a b : ByteArray) :
    evalApp "=" [SVal.bytes a, SVal.bytes b] = some (SVal.bool (a == b)) := by
  rfl

private theorem evalApp_eq_string (a b : String) :
    evalApp "=" [SVal.string a, SVal.string b] = some (SVal.bool (a == b)) := by
  rfl

private theorem evalApp_eq_data (a b : Data) :
    evalApp "=" [SVal.data a, SVal.data b] = some (SVal.bool (a == b)) := by
  rfl

private theorem evalApp_seqAppend (a b : ByteArray) :
    evalApp "seq.++" [SVal.bytes a, SVal.bytes b] = some (SVal.bytes (a ++ b)) := by
  rfl

private theorem evalApp_seqLen (a : ByteArray) :
    evalApp "seq.len" [SVal.bytes a] = some (SVal.int (Int.ofNat a.size)) := by
  rfl

private theorem evalApp_bytesLt (a b : ByteArray) :
    evalApp "bytes_lt" [SVal.bytes a, SVal.bytes b] =
      some (SVal.bool (Moist.Plutus.bytesLt a b)) := by
  rfl

private theorem evalApp_bytesLe (a b : ByteArray) :
    evalApp "bytes_le" [SVal.bytes a, SVal.bytes b] =
      some (SVal.bool (Moist.Plutus.bytesLe a b)) := by
  rfl

private theorem evalApp_strAppend (a b : String) :
    evalApp "str.++" [SVal.string a, SVal.string b] = some (SVal.string (a ++ b)) := by
  rfl

private theorem evalApp_isCtor_VBytes (sv : SVal) :
    evalApp "(_ is VBytes)" [sv] = (isCtor "VBytes" sv).map SVal.bool := by
  cases sv with
  | val v =>
      cases v <;> rfl
  | bool b => rfl
  | int i => rfl
  | string s => rfl
  | bytes bs => rfl
  | data d =>
      cases d <;> rfl
  | dataList xs =>
      cases xs <;> rfl
  | dataPairList xs =>
      cases xs <;> rfl
  | valList xs =>
      cases xs <;> rfl
  | g1 g => rfl
  | g2 g => rfl
  | ml r => rfl

private theorem evalApp_isCtor_VUnit (sv : SVal) :
    evalApp "(_ is VUnit)" [sv] = (isCtor "VUnit" sv).map SVal.bool := by
  cases sv with
  | val v =>
      cases v <;> rfl
  | bool b => rfl
  | int i => rfl
  | string s => rfl
  | bytes bs => rfl
  | data d =>
      cases d <;> rfl
  | dataList xs =>
      cases xs <;> rfl
  | dataPairList xs =>
      cases xs <;> rfl
  | valList xs =>
      cases xs <;> rfl
  | g1 g => rfl
  | g2 g => rfl
  | ml r => rfl

private theorem evalApp_isCtor_VList (sv : SVal) :
    evalApp "(_ is VList)" [sv] = (isCtor "VList" sv).map SVal.bool := by
  cases sv with
  | val v =>
      cases v <;> rfl
  | bool b => rfl
  | int i => rfl
  | string s => rfl
  | bytes bs => rfl
  | data d =>
      cases d <;> rfl
  | dataList xs =>
      cases xs <;> rfl
  | dataPairList xs =>
      cases xs <;> rfl
  | valList xs =>
      cases xs <;> rfl
  | g1 g => rfl
  | g2 g => rfl
  | ml r => rfl

private theorem evalApp_isCtor_VDataList (sv : SVal) :
    evalApp "(_ is VDataList)" [sv] = (isCtor "VDataList" sv).map SVal.bool := by
  cases sv with
  | val v =>
      cases v <;> rfl
  | bool b => rfl
  | int i => rfl
  | string s => rfl
  | bytes bs => rfl
  | data d =>
      cases d <;> rfl
  | dataList xs =>
      cases xs <;> rfl
  | dataPairList xs =>
      cases xs <;> rfl
  | valList xs =>
      cases xs <;> rfl
  | g1 g => rfl
  | g2 g => rfl
  | ml r => rfl

private theorem evalApp_isCtor_VPair (sv : SVal) :
    evalApp "(_ is VPair)" [sv] = (isCtor "VPair" sv).map SVal.bool := by
  cases sv with
  | val v =>
      cases v <;> rfl
  | bool b => rfl
  | int i => rfl
  | string s => rfl
  | bytes bs => rfl
  | data d =>
      cases d <;> rfl
  | dataList xs =>
      cases xs <;> rfl
  | dataPairList xs =>
      cases xs <;> rfl
  | valList xs =>
      cases xs <;> rfl
  | g1 g => rfl
  | g2 g => rfl
  | ml r => rfl

private theorem evalApp_isCtor_VPairData (sv : SVal) :
    evalApp "(_ is VPairData)" [sv] = (isCtor "VPairData" sv).map SVal.bool := by
  cases sv with
  | val v =>
      cases v <;> rfl
  | bool b => rfl
  | int i => rfl
  | string s => rfl
  | bytes bs => rfl
  | data d =>
      cases d <;> rfl
  | dataList xs =>
      cases xs <;> rfl
  | dataPairList xs =>
      cases xs <;> rfl
  | valList xs =>
      cases xs <;> rfl
  | g1 g => rfl
  | g2 g => rfl
  | ml r => rfl

private theorem evalApp_isCtor_VConstr (sv : SVal) :
    evalApp "(_ is VConstr)" [sv] = (isCtor "VConstr" sv).map SVal.bool := by
  cases sv with
  | val v =>
      cases v <;> rfl
  | bool b => rfl
  | int i => rfl
  | string s => rfl
  | bytes bs => rfl
  | data d =>
      cases d <;> rfl
  | dataList xs =>
      cases xs <;> rfl
  | dataPairList xs =>
      cases xs <;> rfl
  | valList xs =>
      cases xs <;> rfl
  | g1 g => rfl
  | g2 g => rfl
  | ml r => rfl

private theorem evalApp_isCtor_VString (sv : SVal) :
    evalApp "(_ is VString)" [sv] = (isCtor "VString" sv).map SVal.bool := by
  cases sv with
  | val v =>
      cases v <;> rfl
  | bool b => rfl
  | int i => rfl
  | string s => rfl
  | bytes bs => rfl
  | data d =>
      cases d <;> rfl
  | dataList xs =>
      cases xs <;> rfl
  | dataPairList xs =>
      cases xs <;> rfl
  | valList xs =>
      cases xs <;> rfl
  | g1 g => rfl
  | g2 g => rfl
  | ml r => rfl

private theorem evalApp_isCtor_VData (sv : SVal) :
    evalApp "(_ is VData)" [sv] = (isCtor "VData" sv).map SVal.bool := by
  cases sv with
  | val v =>
      cases v <;> rfl
  | bool b => rfl
  | int i => rfl
  | string s => rfl
  | bytes bs => rfl
  | data d =>
      cases d <;> rfl
  | dataList xs =>
      cases xs <;> rfl
  | dataPairList xs =>
      cases xs <;> rfl
  | valList xs =>
      cases xs <;> rfl
  | g1 g => rfl
  | g2 g => rfl
  | ml r => rfl

private theorem evalApp_isCtor_VPairDataList (sv : SVal) :
    evalApp "(_ is VPairDataList)" [sv] = (isCtor "VPairDataList" sv).map SVal.bool := by
  cases sv with
  | val v =>
      cases v <;> rfl
  | bool b => rfl
  | int i => rfl
  | string s => rfl
  | bytes bs => rfl
  | data d =>
      cases d <;> rfl
  | dataList xs =>
      cases xs <;> rfl
  | dataPairList xs =>
      cases xs <;> rfl
  | valList xs =>
      cases xs <;> rfl
  | g1 g => rfl
  | g2 g => rfl
  | ml r => rfl

private theorem evalApp_isCtor_VArray (sv : SVal) :
    evalApp "(_ is VArray)" [sv] = (isCtor "VArray" sv).map SVal.bool := by
  cases sv with
  | val v =>
      cases v <;> rfl
  | bool b => rfl
  | int i => rfl
  | string s => rfl
  | bytes bs => rfl
  | data d =>
      cases d <;> rfl
  | dataList xs =>
      cases xs <;> rfl
  | dataPairList xs =>
      cases xs <;> rfl
  | valList xs =>
      cases xs <;> rfl
  | g1 g => rfl
  | g2 g => rfl
  | ml r => rfl

private theorem evalApp_isCtor_VG1 (sv : SVal) :
    evalApp "(_ is VG1)" [sv] = (isCtor "VG1" sv).map SVal.bool := by
  cases sv with
  | val v =>
      cases v <;> rfl
  | bool b => rfl
  | int i => rfl
  | string s => rfl
  | bytes bs => rfl
  | data d =>
      cases d <;> rfl
  | dataList xs =>
      cases xs <;> rfl
  | dataPairList xs =>
      cases xs <;> rfl
  | valList xs =>
      cases xs <;> rfl
  | g1 g => rfl
  | g2 g => rfl
  | ml r => rfl

private theorem evalApp_isCtor_VG2 (sv : SVal) :
    evalApp "(_ is VG2)" [sv] = (isCtor "VG2" sv).map SVal.bool := by
  cases sv with
  | val v =>
      cases v <;> rfl
  | bool b => rfl
  | int i => rfl
  | string s => rfl
  | bytes bs => rfl
  | data d =>
      cases d <;> rfl
  | dataList xs =>
      cases xs <;> rfl
  | dataPairList xs =>
      cases xs <;> rfl
  | valList xs =>
      cases xs <;> rfl
  | g1 g => rfl
  | g2 g => rfl
  | ml r => rfl

private theorem evalApp_isCtor_VMlResult (sv : SVal) :
    evalApp "(_ is VMlResult)" [sv] = (isCtor "VMlResult" sv).map SVal.bool := by
  cases sv with
  | val v =>
      cases v <;> rfl
  | bool b => rfl
  | int i => rfl
  | string s => rfl
  | bytes bs => rfl
  | data d =>
      cases d <;> rfl
  | dataList xs =>
      cases xs <;> rfl
  | dataPairList xs =>
      cases xs <;> rfl
  | valList xs =>
      cases xs <;> rfl
  | g1 g => rfl
  | g2 g => rfl
  | ml r => rfl

private theorem evalApp_isCtor_DConstr (sv : SVal) :
    evalApp "(_ is DConstr)" [sv] = (isCtor "DConstr" sv).map SVal.bool := by
  cases sv with
  | val v =>
      cases v <;> rfl
  | bool b => rfl
  | int i => rfl
  | string s => rfl
  | bytes bs => rfl
  | data d =>
      cases d <;> rfl
  | dataList xs =>
      cases xs <;> rfl
  | dataPairList xs =>
      cases xs <;> rfl
  | valList xs =>
      cases xs <;> rfl
  | g1 g => rfl
  | g2 g => rfl
  | ml r => rfl

private theorem evalApp_isCtor_DMap (sv : SVal) :
    evalApp "(_ is DMap)" [sv] = (isCtor "DMap" sv).map SVal.bool := by
  cases sv with
  | val v =>
      cases v <;> rfl
  | bool b => rfl
  | int i => rfl
  | string s => rfl
  | bytes bs => rfl
  | data d =>
      cases d <;> rfl
  | dataList xs =>
      cases xs <;> rfl
  | dataPairList xs =>
      cases xs <;> rfl
  | valList xs =>
      cases xs <;> rfl
  | g1 g => rfl
  | g2 g => rfl
  | ml r => rfl

private theorem evalApp_isCtor_DList (sv : SVal) :
    evalApp "(_ is DList)" [sv] = (isCtor "DList" sv).map SVal.bool := by
  cases sv with
  | val v =>
      cases v <;> rfl
  | bool b => rfl
  | int i => rfl
  | string s => rfl
  | bytes bs => rfl
  | data d =>
      cases d <;> rfl
  | dataList xs =>
      cases xs <;> rfl
  | dataPairList xs =>
      cases xs <;> rfl
  | valList xs =>
      cases xs <;> rfl
  | g1 g => rfl
  | g2 g => rfl
  | ml r => rfl

private theorem evalApp_isCtor_DI (sv : SVal) :
    evalApp "(_ is DI)" [sv] = (isCtor "DI" sv).map SVal.bool := by
  cases sv with
  | val v =>
      cases v <;> rfl
  | bool b => rfl
  | int i => rfl
  | string s => rfl
  | bytes bs => rfl
  | data d =>
      cases d <;> rfl
  | dataList xs =>
      cases xs <;> rfl
  | dataPairList xs =>
      cases xs <;> rfl
  | valList xs =>
      cases xs <;> rfl
  | g1 g => rfl
  | g2 g => rfl
  | ml r => rfl

private theorem evalApp_isCtor_DB (sv : SVal) :
    evalApp "(_ is DB)" [sv] = (isCtor "DB" sv).map SVal.bool := by
  cases sv with
  | val v =>
      cases v <;> rfl
  | bool b => rfl
  | int i => rfl
  | string s => rfl
  | bytes bs => rfl
  | data d =>
      cases d <;> rfl
  | dataList xs =>
      cases xs <;> rfl
  | dataPairList xs =>
      cases xs <;> rfl
  | valList xs =>
      cases xs <;> rfl
  | g1 g => rfl
  | g2 g => rfl
  | ml r => rfl

mutual
  def eval (m : Model) : Expr → Option SVal
    | .sym "(as seq.empty Bytes)" => some (.bytes bytesEmpty)
    | .sym "(as seq.empty (Seq Int))" => some (.bytes bytesEmpty)
    | .sym "g1_default" => some (.g1 "g1_default")
    | .sym "g2_default" => some (.g2 "g2_default")
    | .sym "ml_default" => some (.ml "ml_default")
    | .sym s => m.valueOf s
    | .int i => some (.int i)
    | .bytes bs => some (.bytes bs)
    | .dataLit d => some (.data d)
    | .dataListLit xs => some (.dataList xs)
    | .dataPairListLit xs => some (.dataPairList xs)
    | .constListLit xs => some (.valList (constListToVals xs))
    | .bool b => some (.bool b)
    | .str s => some (.string s)
    | .ite c t e => do
        match ← eval m c with
        | .bool true => eval m t
        | .bool false => eval m e
        | _ => none
    | .app "not" [a] => do
        match ← eval m a with
        | .bool ba => some (.bool (!ba))
        | _ => none
    | .app "and" [a, b] => do
        match ← eval m a, ← eval m b with
        | .bool ba, .bool bb => some (.bool (ba && bb))
        | _, _ => none
    | .app "or" [a, b] => do
        match ← eval m a, ← eval m b with
        | .bool ba, .bool bb => some (.bool (ba || bb))
        | _, _ => none
    | .app "seq.unit" [e] => do
        match ← eval m e with
        | .int n => SVal.bytes <$> bytesSingleton n
        | _ => none
    | .app "seq.nth" [bs, idx] => do
        match ← eval m bs, ← eval m idx with
        | .bytes x, .int i => SVal.int <$> bytesNth x i
        | _, _ => none
    | .app "seq.extract" [bs, start, len] => do
        match ← eval m bs, ← eval m start, ← eval m len with
        | .bytes x, .int s, .int l => some (.bytes (bytesExtract x s l))
        | _, _, _ => none
    | .app "uplc_tdiv" [a, b] => do
        match ← eval m a, ← eval m b with
        | .int x, .int y =>
            if y == 0 then none
            else some (.int (Moist.Plutus.uplcIntegerTDiv x y))
        | _, _ => none
    | .app "uplc_tmod" [a, b] => do
        match ← eval m a, ← eval m b with
        | .int x, .int y =>
            if y == 0 then none
            else some (.int (Moist.Plutus.uplcIntegerTMod x y))
        | _, _ => none
    | .app "uplc_div" [a, b] => do
        match ← eval m a, ← eval m b with
        | .int x, .int y =>
            if y == 0 then none
            else some (.int (Moist.Plutus.uplcIntegerDiv x y))
        | _, _ => none
    | .app "uplc_mod" [a, b] => do
        match ← eval m a, ← eval m b with
        | .int x, .int y =>
            if y == 0 then none
            else some (.int (Moist.Plutus.uplcIntegerMod x y))
        | _, _ => none
    | .app "(_ is VInt)" [a] => do
        let v ← eval m a
        SVal.bool <$> isVIntSVal v
    | .app "(_ is VBool)" [a] => do
        let v ← eval m a
        SVal.bool <$> isVBoolSVal v
    | .app "unVInt" [a] => do
        match ← eval m a with
        | .val (.int i) => some (.int i)
        | _ => none
    | .app "unVBool" [a] => do
        match ← eval m a with
        | .val (.bool b) => some (.bool b)
        | _ => none
    | .app f args => do
        let vs ← evalList m args
        evalApp f vs
  termination_by e => sizeOf e
  decreasing_by
    all_goals
      simp_wf
      omega

  def evalList (m : Model) : List Expr → Option (List SVal)
    | [] => some []
    | e :: es => do
        let v ← eval m e
        let vs ← evalList m es
        some (v :: vs)
  termination_by es => sizeOf es
  decreasing_by
    all_goals
      simp_wf
      omega
end

def evalBool? (m : Model) (e : Expr) : Option Bool :=
  match eval m e with
  | some (.bool b) => some b
  | _ => none

def holds (m : Model) (e : Expr) : Prop :=
  evalBool? m e = some true

def evalBoolIs (m : Model) (e : Expr) (b : Bool) : Bool :=
  match evalBool? m e with
  | some b' => b' == b
  | none => false

@[simp] theorem evalBoolIs_trueE (m : Model) :
    evalBoolIs m Expr.trueE true = true := by
  simp [Expr.trueE, evalBoolIs, evalBool?, eval]

@[simp] theorem evalBoolIs_falseE (m : Model) :
    evalBoolIs m Expr.falseE true = false := by
  simp [Expr.falseE, evalBoolIs, evalBool?, eval]

theorem evalBoolIs_true_eq (m : Model) (e : Expr) :
    evalBoolIs m e true = true ↔ eval m e = some (.bool true) := by
  unfold evalBoolIs evalBool?
  cases he : eval m e with
  | none =>
      simp [he]
  | some v =>
      cases v with
      | bool b =>
          cases b <;> simp [he]
      | int i => simp [he]
      | string s => simp [he]
      | bytes bs => simp [he]
      | data d => simp [he]
      | dataList xs => simp [he]
      | dataPairList xs => simp [he]
      | val v => simp [he]
      | valList xs => simp [he]
      | g1 g => simp [he]
      | g2 g => simp [he]
      | ml r => simp [he]

set_option linter.unusedSimpArgs false in
private theorem evalBoolIs_app_and_true (m : Model) (a b : Expr) :
    evalBoolIs m (.app "and" [a, b]) true = true ↔
      evalBoolIs m a true = true ∧ evalBoolIs m b true = true := by
  unfold evalBoolIs evalBool?
  simp [eval]
  cases ha : eval m a with
  | none =>
      simp [ha]
  | some av =>
      cases av with
      | bool ba =>
          simp [ha]
          cases hb : eval m b with
          | none =>
              simp [hb]
          | some bv =>
              cases bv with
              | bool bb =>
                  cases ba <;> cases bb <;> simp [hb]
              | int i => simp [hb]
              | string s => simp [hb]
              | bytes bs => simp [hb]
              | data d => simp [hb]
              | dataList xs => simp [hb]
              | dataPairList xs => simp [hb]
              | val v => simp [hb]
              | valList xs => simp [hb]
              | g1 g => simp [hb]
              | g2 g => simp [hb]
              | ml r => simp [hb]
      | int i => simp [ha]
      | string s => simp [ha]
      | bytes bs => simp [ha]
      | data d => simp [ha]
      | dataList xs => simp [ha]
      | dataPairList xs => simp [ha]
      | val v => simp [ha]
      | valList xs => simp [ha]
      | g1 g => simp [ha]
      | g2 g => simp [ha]
      | ml r => simp [ha]

set_option linter.unusedSimpArgs false in
private theorem evalBoolIs_app_or_true (m : Model) (a b : Expr) :
    evalBoolIs m (.app "or" [a, b]) true = true →
      evalBoolIs m a true = true ∨ evalBoolIs m b true = true := by
  unfold evalBoolIs evalBool?
  simp [eval]
  cases ha : eval m a with
  | none =>
      simp [ha]
  | some av =>
      cases av with
      | bool ba =>
          simp [ha]
          cases hb : eval m b with
          | none =>
              simp [hb]
          | some bv =>
              cases bv with
              | bool bb =>
                  cases ba <;> cases bb <;> simp [hb]
              | int i => simp [hb]
              | string s => simp [hb]
              | bytes bs => simp [hb]
              | data d => simp [hb]
              | dataList xs => simp [hb]
              | dataPairList xs => simp [hb]
              | val v => simp [hb]
              | valList xs => simp [hb]
              | g1 g => simp [hb]
              | g2 g => simp [hb]
              | ml r => simp [hb]
      | int i => simp [ha]
      | string s => simp [ha]
      | bytes bs => simp [ha]
      | data d => simp [ha]
      | dataList xs => simp [ha]
      | dataPairList xs => simp [ha]
      | val v => simp [ha]
      | valList xs => simp [ha]
      | g1 g => simp [ha]
      | g2 g => simp [ha]
      | ml r => simp [ha]

set_option linter.unusedSimpArgs false in
private theorem evalBoolIs_app_not_true (m : Model) (a : Expr) :
    evalBoolIs m (.app "not" [a]) true = true ↔
      evalBoolIs m a false = true := by
  unfold evalBoolIs evalBool?
  simp [eval]
  cases ha : eval m a with
  | none =>
      simp [ha]
  | some av =>
      cases av with
      | bool ba =>
          cases ba <;> simp [ha]
      | int i => simp [ha]
      | string s => simp [ha]
      | bytes bs => simp [ha]
      | data d => simp [ha]
      | dataList xs => simp [ha]
      | dataPairList xs => simp [ha]
      | val v => simp [ha]
      | valList xs => simp [ha]
      | g1 g => simp [ha]
      | g2 g => simp [ha]
      | ml r => simp [ha]

theorem evalBoolIs_and_true (m : Model) (a b : Expr) :
    evalBoolIs m (Expr.and a b) true = true ↔
      evalBoolIs m a true = true ∧ evalBoolIs m b true = true := by
  simpa [Expr.and] using evalBoolIs_app_and_true m a b

theorem evalBoolIs_or_true (m : Model) (a b : Expr) :
    evalBoolIs m (Expr.or a b) true = true →
      evalBoolIs m a true = true ∨ evalBoolIs m b true = true := by
  simpa [Expr.or] using evalBoolIs_app_or_true m a b

theorem evalBoolIs_not_true (m : Model) (a : Expr) :
    evalBoolIs m (Expr.not a) true = true ↔
      evalBoolIs m a false = true := by
  cases a with
  | bool ba =>
      cases ba <;> simp [Expr.not, evalBoolIs, evalBool?, eval]
  | sym s =>
      simpa [Expr.not] using evalBoolIs_app_not_true m (.sym s)
  | int i =>
      simpa [Expr.not] using evalBoolIs_app_not_true m (.int i)
  | bytes bs =>
      simpa [Expr.not] using evalBoolIs_app_not_true m (.bytes bs)
  | dataLit d =>
      simpa [Expr.not] using evalBoolIs_app_not_true m (.dataLit d)
  | dataListLit xs =>
      simpa [Expr.not] using evalBoolIs_app_not_true m (.dataListLit xs)
  | dataPairListLit xs =>
      simpa [Expr.not] using evalBoolIs_app_not_true m (.dataPairListLit xs)
  | constListLit xs =>
      simpa [Expr.not] using evalBoolIs_app_not_true m (.constListLit xs)
  | str s =>
      simpa [Expr.not] using evalBoolIs_app_not_true m (.str s)
  | app f args =>
      simpa [Expr.not] using evalBoolIs_app_not_true m (.app f args)
  | ite c t e =>
      simpa [Expr.not] using evalBoolIs_app_not_true m (.ite c t e)

private theorem evalBoolIs_isCtor_true_core {m : Model} {e : Expr}
    {f ctor : String}
    (happ : ∀ sv, evalApp f [sv] = (isCtor ctor sv).map SVal.bool)
    (hevalApp : eval m (.app f [e]) = (do
      let vs ← evalList m [e]
      evalApp f vs))
    (h : evalBoolIs m (.app f [e]) true = true) :
    ∃ sv, eval m e = some sv ∧ isCtor ctor sv = some true := by
  unfold evalBoolIs evalBool? at h
  rw [hevalApp] at h
  change
    (match
      (match
        (do
          let vs ← evalList m [e]
          evalApp f vs) with
      | some (.bool b) => some b
      | _ => none) with
    | some b' => b' == true
    | none => false) = true at h
  rw [evalList.eq_def] at h
  cases he : eval m e with
  | none =>
      simp [he] at h
  | some sv =>
      simp [he, evalList.eq_def, happ sv] at h
      cases hc : isCtor ctor sv with
      | none =>
          simp [hc] at h
      | some b =>
          cases b <;> simp [hc] at h
          exact ⟨sv, by simp [he], hc⟩

theorem eval_unVInt_of {m : Model} {e : Expr} {i : Int}
    (h : eval m e = some (.val (.int i))) :
    eval m (.app "unVInt" [e]) = some (.int i) := by
  rw [eval.eq_def]
  change
    (do
      let v ← eval m e
      match v with
      | SVal.val (Val.int j) => some (SVal.int j)
      | _ => none) = some (.int i)
  rw [h]
  rfl

theorem evalBoolIs_isVInt_true {m : Model} {e : Expr}
    (h : evalBoolIs m (.app "(_ is VInt)" [e]) true = true) :
    ∃ i, eval m e = some (.val (.int i)) := by
  unfold evalBoolIs evalBool? at h
  rw [eval.eq_def] at h
  change
    (match
      (match
        (do
          let v ← eval m e
          SVal.bool <$> isVIntSVal v) with
        | some (.bool b) => some b
        | _ => none) with
    | some b' => b' == true
    | none => false) = true at h
  cases he : eval m e with
  | none =>
      simp [he] at h
  | some sv =>
      cases sv with
      | val v =>
          cases v with
          | int i =>
              exact ⟨i, by simp⟩
          | bytes bs =>
              simp [he, isVIntSVal] at h
          | string s =>
              simp [he, isVIntSVal] at h
          | bool b =>
              simp [he, isVIntSVal] at h
          | unit =>
              simp [he, isVIntSVal] at h
          | list xs =>
              simp [he, isVIntSVal] at h
          | dataList xs =>
              simp [he, isVIntSVal] at h
          | pairDataList xs =>
              simp [he, isVIntSVal] at h
          | pair a b =>
              simp [he, isVIntSVal] at h
          | pairData a b =>
              simp [he, isVIntSVal] at h
          | data d =>
              simp [he, isVIntSVal] at h
          | array xs =>
              simp [he, isVIntSVal] at h
          | g1 g =>
              simp [he, isVIntSVal] at h
          | g2 g =>
              simp [he, isVIntSVal] at h
          | ml r =>
              simp [he, isVIntSVal] at h
          | constr tag fields =>
              simp [he, isVIntSVal] at h
      | bool b =>
          simp [he, isVIntSVal] at h
      | int i =>
          simp [he, isVIntSVal] at h
      | string s =>
          simp [he, isVIntSVal] at h
      | bytes bs =>
          simp [he, isVIntSVal] at h
      | data d =>
          simp [he, isVIntSVal] at h
      | dataList xs =>
          simp [he, isVIntSVal] at h
      | dataPairList xs =>
          simp [he, isVIntSVal] at h
      | valList xs =>
          simp [he, isVIntSVal] at h
      | g1 g =>
          simp [he, isVIntSVal] at h
      | g2 g =>
          simp [he, isVIntSVal] at h
      | ml r =>
          simp [he, isVIntSVal] at h

theorem eval_unVBool_of {m : Model} {e : Expr} {b : Bool}
    (h : eval m e = some (.val (.bool b))) :
    eval m (.app "unVBool" [e]) = some (.bool b) := by
  rw [eval.eq_def]
  change
    (do
      let v ← eval m e
      match v with
      | SVal.val (Val.bool b') => some (SVal.bool b')
      | _ => none) = some (.bool b)
  rw [h]
  rfl

theorem evalBoolIs_isVBool_true {m : Model} {e : Expr}
    (h : evalBoolIs m (.app "(_ is VBool)" [e]) true = true) :
    ∃ b, eval m e = some (.val (.bool b)) := by
  unfold evalBoolIs evalBool? at h
  rw [eval.eq_def] at h
  change
    (match
      (match
        (do
          let v ← eval m e
          SVal.bool <$> isVBoolSVal v) with
        | some (.bool b) => some b
        | _ => none) with
    | some b' => b' == true
    | none => false) = true at h
  cases he : eval m e with
  | none =>
      simp [he] at h
  | some sv =>
      cases sv with
      | val v =>
          cases v with
          | bool b =>
              exact ⟨b, by simp⟩
          | int i =>
              simp [he, isVBoolSVal] at h
          | bytes bs =>
              simp [he, isVBoolSVal] at h
          | string s =>
              simp [he, isVBoolSVal] at h
          | unit =>
              simp [he, isVBoolSVal] at h
          | list xs =>
              simp [he, isVBoolSVal] at h
          | dataList xs =>
              simp [he, isVBoolSVal] at h
          | pairDataList xs =>
              simp [he, isVBoolSVal] at h
          | pair a b =>
              simp [he, isVBoolSVal] at h
          | pairData a b =>
              simp [he, isVBoolSVal] at h
          | data d =>
              simp [he, isVBoolSVal] at h
          | array xs =>
              simp [he, isVBoolSVal] at h
          | g1 g =>
              simp [he, isVBoolSVal] at h
          | g2 g =>
              simp [he, isVBoolSVal] at h
          | ml r =>
              simp [he, isVBoolSVal] at h
          | constr tag fields =>
              simp [he, isVBoolSVal] at h
      | bool b =>
          simp [he, isVBoolSVal] at h
      | int i =>
          simp [he, isVBoolSVal] at h
      | string s =>
          simp [he, isVBoolSVal] at h
      | bytes bs =>
          simp [he, isVBoolSVal] at h
      | data d =>
          simp [he, isVBoolSVal] at h
      | dataList xs =>
          simp [he, isVBoolSVal] at h
      | dataPairList xs =>
          simp [he, isVBoolSVal] at h
      | valList xs =>
          simp [he, isVBoolSVal] at h
      | g1 g =>
          simp [he, isVBoolSVal] at h
      | g2 g =>
          simp [he, isVBoolSVal] at h
      | ml r =>
          simp [he, isVBoolSVal] at h

theorem evalBoolIs_isVUnit_true {m : Model} {e : Expr}
    (h : evalBoolIs m (.app "(_ is VUnit)" [e]) true = true) :
    eval m e = some (.val .unit) := by
  obtain ⟨sv, he, hc⟩ :=
    evalBoolIs_isCtor_true_core (m := m) (e := e)
      (f := "(_ is VUnit)") (ctor := "VUnit") evalApp_isCtor_VUnit
      (by rw [eval.eq_def]; rfl) h
  cases sv with
  | val v =>
      cases v <;> simp [isCtor] at hc
      exact he
  | bool b => simp [isCtor] at hc
  | int i => simp [isCtor] at hc
  | string s => simp [isCtor] at hc
  | bytes bs => simp [isCtor] at hc
  | data d =>
      cases d <;> simp [isCtor] at hc
  | dataList xs =>
      cases xs <;> simp [isCtor] at hc
  | dataPairList xs =>
      cases xs <;> simp [isCtor] at hc
  | valList xs =>
      cases xs <;> simp [isCtor] at hc
  | g1 g => simp [isCtor] at hc
  | g2 g => simp [isCtor] at hc
  | ml r => simp [isCtor] at hc

theorem evalBoolIs_isVList_true {m : Model} {e : Expr}
    (h : evalBoolIs m (.app "(_ is VList)" [e]) true = true) :
    ∃ xs, eval m e = some (.val (.list xs)) := by
  obtain ⟨sv, he, hc⟩ :=
    evalBoolIs_isCtor_true_core (m := m) (e := e)
      (f := "(_ is VList)") (ctor := "VList") evalApp_isCtor_VList
      (by rw [eval.eq_def]; rfl) h
  cases sv with
  | val v =>
      cases v <;> simp [isCtor] at hc
      rename_i xs
      exact ⟨xs, he⟩
  | bool b => simp [isCtor] at hc
  | int i => simp [isCtor] at hc
  | string s => simp [isCtor] at hc
  | bytes bs => simp [isCtor] at hc
  | data d =>
      cases d <;> simp [isCtor] at hc
  | dataList xs =>
      cases xs <;> simp [isCtor] at hc
  | dataPairList xs =>
      cases xs <;> simp [isCtor] at hc
  | valList xs =>
      cases xs <;> simp [isCtor] at hc
  | g1 g => simp [isCtor] at hc
  | g2 g => simp [isCtor] at hc
  | ml r => simp [isCtor] at hc

theorem evalBoolIs_isVDataList_true {m : Model} {e : Expr}
    (h : evalBoolIs m (.app "(_ is VDataList)" [e]) true = true) :
    ∃ xs, eval m e = some (.val (.dataList xs)) := by
  obtain ⟨sv, he, hc⟩ :=
    evalBoolIs_isCtor_true_core (m := m) (e := e)
      (f := "(_ is VDataList)") (ctor := "VDataList") evalApp_isCtor_VDataList
      (by rw [eval.eq_def]; rfl) h
  cases sv with
  | val v =>
      cases v <;> simp [isCtor] at hc
      rename_i xs
      exact ⟨xs, he⟩
  | bool b => simp [isCtor] at hc
  | int i => simp [isCtor] at hc
  | string s => simp [isCtor] at hc
  | bytes bs => simp [isCtor] at hc
  | data d =>
      cases d <;> simp [isCtor] at hc
  | dataList xs =>
      cases xs <;> simp [isCtor] at hc
  | dataPairList xs =>
      cases xs <;> simp [isCtor] at hc
  | valList xs =>
      cases xs <;> simp [isCtor] at hc
  | g1 g => simp [isCtor] at hc
  | g2 g => simp [isCtor] at hc
  | ml r => simp [isCtor] at hc

theorem evalBoolIs_isVPair_true {m : Model} {e : Expr}
    (h : evalBoolIs m (.app "(_ is VPair)" [e]) true = true) :
    ∃ a b, eval m e = some (.val (.pair a b)) := by
  obtain ⟨sv, he, hc⟩ :=
    evalBoolIs_isCtor_true_core (m := m) (e := e)
      (f := "(_ is VPair)") (ctor := "VPair") evalApp_isCtor_VPair
      (by rw [eval.eq_def]; rfl) h
  cases sv with
  | val v =>
      cases v <;> simp [isCtor] at hc
      rename_i a b
      exact ⟨a, b, he⟩
  | bool b => simp [isCtor] at hc
  | int i => simp [isCtor] at hc
  | string s => simp [isCtor] at hc
  | bytes bs => simp [isCtor] at hc
  | data d =>
      cases d <;> simp [isCtor] at hc
  | dataList xs =>
      cases xs <;> simp [isCtor] at hc
  | dataPairList xs =>
      cases xs <;> simp [isCtor] at hc
  | valList xs =>
      cases xs <;> simp [isCtor] at hc
  | g1 g => simp [isCtor] at hc
  | g2 g => simp [isCtor] at hc
  | ml r => simp [isCtor] at hc

theorem evalBoolIs_isVPairData_true {m : Model} {e : Expr}
    (h : evalBoolIs m (.app "(_ is VPairData)" [e]) true = true) :
    ∃ a b, eval m e = some (.val (.pairData a b)) := by
  obtain ⟨sv, he, hc⟩ :=
    evalBoolIs_isCtor_true_core (m := m) (e := e)
      (f := "(_ is VPairData)") (ctor := "VPairData") evalApp_isCtor_VPairData
      (by rw [eval.eq_def]; rfl) h
  cases sv with
  | val v =>
      cases v <;> simp [isCtor] at hc
      rename_i a b
      exact ⟨a, b, he⟩
  | bool b => simp [isCtor] at hc
  | int i => simp [isCtor] at hc
  | string s => simp [isCtor] at hc
  | bytes bs => simp [isCtor] at hc
  | data d =>
      cases d <;> simp [isCtor] at hc
  | dataList xs =>
      cases xs <;> simp [isCtor] at hc
  | dataPairList xs =>
      cases xs <;> simp [isCtor] at hc
  | valList xs =>
      cases xs <;> simp [isCtor] at hc
  | g1 g => simp [isCtor] at hc
  | g2 g => simp [isCtor] at hc
  | ml r => simp [isCtor] at hc

theorem evalBoolIs_isVConstr_true {m : Model} {e : Expr}
    (h : evalBoolIs m (.app "(_ is VConstr)" [e]) true = true) :
    ∃ tag fields, eval m e = some (.val (.constr tag fields)) := by
  obtain ⟨sv, he, hc⟩ :=
    evalBoolIs_isCtor_true_core (m := m) (e := e)
      (f := "(_ is VConstr)") (ctor := "VConstr") evalApp_isCtor_VConstr
      (by rw [eval.eq_def]; rfl) h
  cases sv with
  | val v =>
      cases v <;> simp [isCtor] at hc
      rename_i tag fields
      exact ⟨tag, fields, he⟩
  | bool b => simp [isCtor] at hc
  | int i => simp [isCtor] at hc
  | string s => simp [isCtor] at hc
  | bytes bs => simp [isCtor] at hc
  | data d =>
      cases d <;> simp [isCtor] at hc
  | dataList xs =>
      cases xs <;> simp [isCtor] at hc
  | dataPairList xs =>
      cases xs <;> simp [isCtor] at hc
  | valList xs =>
      cases xs <;> simp [isCtor] at hc
  | g1 g => simp [isCtor] at hc
  | g2 g => simp [isCtor] at hc
  | ml r => simp [isCtor] at hc

theorem eval_add_of {m : Model} {a b : Expr} {x y : Int}
    (ha : eval m a = some (SVal.int x))
    (hb : eval m b = some (SVal.int y)) :
    eval m (.app "+" [a, b]) = some (SVal.int (x + y)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [a, b]
      evalApp "+" vs) = some (SVal.int (x + y))
  rw [evalList.eq_def]
  simp [ha]
  rw [evalList.eq_def]
  simp [hb]
  rw [evalList.eq_def]
  exact evalApp_add x y

theorem eval_sub_of {m : Model} {a b : Expr} {x y : Int}
    (ha : eval m a = some (SVal.int x))
    (hb : eval m b = some (SVal.int y)) :
    eval m (.app "-" [a, b]) = some (SVal.int (x - y)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [a, b]
      evalApp "-" vs) = some (SVal.int (x - y))
  rw [evalList.eq_def]
  simp [ha]
  rw [evalList.eq_def]
  simp [hb]
  rw [evalList.eq_def]
  exact evalApp_sub x y

theorem eval_mul_of {m : Model} {a b : Expr} {x y : Int}
    (ha : eval m a = some (SVal.int x))
    (hb : eval m b = some (SVal.int y)) :
    eval m (.app "*" [a, b]) = some (SVal.int (x * y)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [a, b]
      evalApp "*" vs) = some (SVal.int (x * y))
  rw [evalList.eq_def]
  simp [ha]
  rw [evalList.eq_def]
  simp [hb]
  rw [evalList.eq_def]
  exact evalApp_mul x y

theorem eval_uplc_tdiv_of {m : Model} {a b : Expr} {x y : Int}
    (ha : eval m a = some (SVal.int x))
    (hb : eval m b = some (SVal.int y))
    (hy : (y == 0) = false) :
    eval m (.app "uplc_tdiv" [a, b]) =
      some (SVal.int (Moist.Plutus.uplcIntegerTDiv x y)) := by
  have hneq : y ≠ 0 := by
    intro hz
    subst y
    simp at hy
  rw [eval.eq_def]
  simp [ha, hb, hneq]

theorem eval_uplc_tmod_of {m : Model} {a b : Expr} {x y : Int}
    (ha : eval m a = some (SVal.int x))
    (hb : eval m b = some (SVal.int y))
    (hy : (y == 0) = false) :
    eval m (.app "uplc_tmod" [a, b]) =
      some (SVal.int (Moist.Plutus.uplcIntegerTMod x y)) := by
  have hneq : y ≠ 0 := by
    intro hz
    subst y
    simp at hy
  rw [eval.eq_def]
  simp [ha, hb, hneq]

theorem eval_uplc_div_of {m : Model} {a b : Expr} {x y : Int}
    (ha : eval m a = some (SVal.int x))
    (hb : eval m b = some (SVal.int y))
    (hy : (y == 0) = false) :
    eval m (.app "uplc_div" [a, b]) =
      some (SVal.int (Moist.Plutus.uplcIntegerDiv x y)) := by
  have hneq : y ≠ 0 := by
    intro hz
    subst y
    simp at hy
  rw [eval.eq_def]
  simp [ha, hb, hneq]

theorem eval_uplc_mod_of {m : Model} {a b : Expr} {x y : Int}
    (ha : eval m a = some (SVal.int x))
    (hb : eval m b = some (SVal.int y))
    (hy : (y == 0) = false) :
    eval m (.app "uplc_mod" [a, b]) =
      some (SVal.int (Moist.Plutus.uplcIntegerMod x y)) := by
  have hneq : y ≠ 0 := by
    intro hz
    subst y
    simp at hy
  rw [eval.eq_def]
  simp [ha, hb, hneq]

theorem eval_eq_int_of {m : Model} {a b : Expr} {x y : Int}
    (ha : eval m a = some (SVal.int x))
    (hb : eval m b = some (SVal.int y)) :
    eval m (Expr.eq a b) = some (SVal.bool (x == y)) := by
  rw [Expr.eq, eval.eq_def]
  change
    (do
      let vs ← evalList m [a, b]
      evalApp "=" vs) = some (SVal.bool (x == y))
  rw [evalList.eq_def]
  simp [ha]
  rw [evalList.eq_def]
  simp [hb]
  rw [evalList.eq_def]
  exact evalApp_eq_int x y

theorem eval_lt_of {m : Model} {a b : Expr} {x y : Int}
    (ha : eval m a = some (SVal.int x))
    (hb : eval m b = some (SVal.int y)) :
    eval m (Expr.lt a b) = some (SVal.bool (x < y)) := by
  rw [Expr.lt, eval.eq_def]
  change
    (do
      let vs ← evalList m [a, b]
      evalApp "<" vs) = some (SVal.bool (x < y))
  rw [evalList.eq_def]
  simp [ha]
  rw [evalList.eq_def]
  simp [hb]
  rw [evalList.eq_def]
  exact evalApp_lt x y

theorem eval_le_of {m : Model} {a b : Expr} {x y : Int}
    (ha : eval m a = some (SVal.int x))
    (hb : eval m b = some (SVal.int y)) :
    eval m (Expr.le a b) = some (SVal.bool (x <= y)) := by
  rw [Expr.le, eval.eq_def]
  change
    (do
      let vs ← evalList m [a, b]
      evalApp "<=" vs) = some (SVal.bool (x <= y))
  rw [evalList.eq_def]
  simp [ha]
  rw [evalList.eq_def]
  simp [hb]
  rw [evalList.eq_def]
  exact evalApp_le x y

theorem eval_ge_of {m : Model} {a b : Expr} {x y : Int}
    (ha : eval m a = some (SVal.int x))
    (hb : eval m b = some (SVal.int y)) :
    eval m (Expr.ge a b) = some (SVal.bool (x >= y)) := by
  rw [Expr.ge, eval.eq_def]
  change
    (do
      let vs ← evalList m [a, b]
      evalApp ">=" vs) = some (SVal.bool (x >= y))
  rw [evalList.eq_def]
  simp [ha]
  rw [evalList.eq_def]
  simp [hb]
  rw [evalList.eq_def]
  exact evalApp_ge x y

theorem eval_eq_bytes_of {m : Model} {a b : Expr} {x y : ByteArray}
    (ha : eval m a = some (SVal.bytes x))
    (hb : eval m b = some (SVal.bytes y)) :
    eval m (Expr.eq a b) = some (SVal.bool (x == y)) := by
  rw [Expr.eq, eval.eq_def]
  change
    (do
      let vs ← evalList m [a, b]
      evalApp "=" vs) = some (SVal.bool (x == y))
  rw [evalList.eq_def]
  simp [ha]
  rw [evalList.eq_def]
  simp [hb]
  rw [evalList.eq_def]
  exact evalApp_eq_bytes x y

theorem eval_bytesLt_of {m : Model} {a b : Expr} {x y : ByteArray}
    (ha : eval m a = some (SVal.bytes x))
    (hb : eval m b = some (SVal.bytes y)) :
    eval m (.app "bytes_lt" [a, b]) =
      some (SVal.bool (Moist.Plutus.bytesLt x y)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [a, b]
      evalApp "bytes_lt" vs) =
        some (SVal.bool (Moist.Plutus.bytesLt x y))
  rw [evalList.eq_def]
  simp [ha]
  rw [evalList.eq_def]
  simp [hb]
  rw [evalList.eq_def]
  exact evalApp_bytesLt x y

theorem eval_bytesLe_of {m : Model} {a b : Expr} {x y : ByteArray}
    (ha : eval m a = some (SVal.bytes x))
    (hb : eval m b = some (SVal.bytes y)) :
    eval m (.app "bytes_le" [a, b]) =
      some (SVal.bool (Moist.Plutus.bytesLe x y)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [a, b]
      evalApp "bytes_le" vs) =
        some (SVal.bool (Moist.Plutus.bytesLe x y))
  rw [evalList.eq_def]
  simp [ha]
  rw [evalList.eq_def]
  simp [hb]
  rw [evalList.eq_def]
  exact evalApp_bytesLe x y

theorem eval_eq_string_of {m : Model} {a b : Expr} {x y : String}
    (ha : eval m a = some (SVal.string x))
    (hb : eval m b = some (SVal.string y)) :
    eval m (Expr.eq a b) = some (SVal.bool (x == y)) := by
  rw [Expr.eq, eval.eq_def]
  change
    (do
      let vs ← evalList m [a, b]
      evalApp "=" vs) = some (SVal.bool (x == y))
  rw [evalList.eq_def]
  simp [ha]
  rw [evalList.eq_def]
  simp [hb]
  rw [evalList.eq_def]
  exact evalApp_eq_string x y

theorem eval_eq_data_of {m : Model} {a b : Expr} {x y : Data}
    (ha : eval m a = some (SVal.data x))
    (hb : eval m b = some (SVal.data y)) :
    eval m (Expr.eq a b) = some (SVal.bool (x == y)) := by
  rw [Expr.eq, eval.eq_def]
  change
    (do
      let vs ← evalList m [a, b]
      evalApp "=" vs) = some (SVal.bool (x == y))
  rw [evalList.eq_def]
  simp [ha]
  rw [evalList.eq_def]
  simp [hb]
  rw [evalList.eq_def]
  exact evalApp_eq_data x y

theorem eval_seqAppend_of {m : Model} {a b : Expr} {x y : ByteArray}
    (ha : eval m a = some (SVal.bytes x))
    (hb : eval m b = some (SVal.bytes y)) :
    eval m (.app "seq.++" [a, b]) = some (SVal.bytes (x ++ y)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [a, b]
      evalApp "seq.++" vs) = some (SVal.bytes (x ++ y))
  rw [evalList.eq_def]
  simp [ha]
  rw [evalList.eq_def]
  simp [hb]
  rw [evalList.eq_def]
  exact evalApp_seqAppend x y

theorem eval_seqUnit_of {m : Model} {e : Expr} {x : Int}
    (he : eval m e = some (SVal.int x))
    (hge : 0 ≤ x)
    (hle : x ≤ 255) :
    eval m (.app "seq.unit" [e]) =
      some (SVal.bytes (bytesSingletonValue x)) := by
  have hnlt : ¬ x < 0 := by omega
  have hngt : ¬ x > 255 := by omega
  rw [eval.eq_def]
  simp [he, bytesSingleton, Moist.Plutus.bytesSingleton?, hnlt, hngt,
    bytesSingletonValue]

theorem eval_seqLen_of {m : Model} {a : Expr} {x : ByteArray}
    (ha : eval m a = some (SVal.bytes x)) :
    eval m (.app "seq.len" [a]) = some (SVal.int (Int.ofNat x.size)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [a]
      evalApp "seq.len" vs) = some (SVal.int (Int.ofNat x.size))
  rw [evalList.eq_def]
  simp [ha]
  rw [evalList.eq_def]
  exact evalApp_seqLen x

theorem eval_seqNth_of {m : Model} {bs idx : Expr} {x : ByteArray} {i : Int}
    (hbs : eval m bs = some (SVal.bytes x))
    (hidx : eval m idx = some (SVal.int i))
    (hge : 0 ≤ i)
    (hlt : i < Int.ofNat x.size) :
    eval m (.app "seq.nth" [bs, idx]) =
      some (SVal.int (bytesNthValue x i)) := by
  have hnlt : ¬ i < 0 := by omega
  have hnge : ¬ i ≥ Int.ofNat x.size := by omega
  have hlt' : i < ↑x.size := by
    simpa using hlt
  rw [eval.eq_def]
  simp [hbs, hidx, bytesNth, Moist.Plutus.bytesNth?, hnlt, hlt',
    bytesNthValue]

theorem eval_seqExtract_of {m : Model} {bs start len : Expr}
    {x : ByteArray} {s l : Int}
    (hbs : eval m bs = some (SVal.bytes x))
    (hstart : eval m start = some (SVal.int s))
    (hlen : eval m len = some (SVal.int l)) :
    eval m (.app "seq.extract" [bs, start, len]) =
      some (SVal.bytes (bytesExtractValue x s l)) := by
  rw [eval.eq_def]
  simp [hbs, hstart, hlen, bytesExtract, bytesExtractValue]

theorem eval_strAppend_of {m : Model} {a b : Expr} {x y : String}
    (ha : eval m a = some (SVal.string x))
    (hb : eval m b = some (SVal.string y)) :
    eval m (.app "str.++" [a, b]) = some (SVal.string (x ++ y)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [a, b]
      evalApp "str.++" vs) = some (SVal.string (x ++ y))
  rw [evalList.eq_def]
  simp [ha]
  rw [evalList.eq_def]
  simp [hb]
  rw [evalList.eq_def]
  exact evalApp_strAppend x y

theorem eval_unVBytes_of {m : Model} {e : Expr} {bs : ByteArray}
    (h : eval m e = some (SVal.val (Val.bytes bs))) :
    eval m (.app "unVBytes" [e]) = some (SVal.bytes bs) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "unVBytes" vs) = some (.bytes bs)
  rw [evalList.eq_def]
  simp [h]
  rw [evalList.eq_def]
  exact evalApp_unVBytes bs

theorem evalBoolIs_isVBytes_true {m : Model} {e : Expr}
    (h : evalBoolIs m (.app "(_ is VBytes)" [e]) true = true) :
    ∃ bs, eval m e = some (SVal.val (Val.bytes bs)) := by
  unfold evalBoolIs evalBool? at h
  rw [eval.eq_def] at h
  change
    (match
      (match
        (do
          let vs ← evalList m [e]
          evalApp "(_ is VBytes)" vs) with
        | some (.bool b) => some b
        | _ => none) with
    | some b' => b' == true
    | none => false) = true at h
  rw [evalList.eq_def] at h
  cases he : eval m e with
  | none =>
      simp [he] at h
  | some sv =>
      simp [he] at h
      simp [evalList.eq_def] at h
      rw [evalApp_isCtor_VBytes sv] at h
      cases sv with
      | val v =>
          cases v with
          | bytes bs => exact ⟨bs, rfl⟩
          | int i => simp [isCtor] at h
          | string s => simp [isCtor] at h
          | bool b => simp [isCtor] at h
          | unit => simp [isCtor] at h
          | list xs => simp [isCtor] at h
          | dataList xs => simp [isCtor] at h
          | pairDataList xs => simp [isCtor] at h
          | pair a b => simp [isCtor] at h
          | pairData a b => simp [isCtor] at h
          | data d => simp [isCtor] at h
          | array xs => simp [isCtor] at h
          | g1 g => simp [isCtor] at h
          | g2 g => simp [isCtor] at h
          | ml r => simp [isCtor] at h
          | constr tag fields => simp [isCtor] at h
      | bool b => simp [isCtor] at h
      | int i => simp [isCtor] at h
      | string s => simp [isCtor] at h
      | bytes bs => simp [isCtor] at h
      | data d =>
          cases d <;> simp [isCtor] at h
      | dataList xs =>
          cases xs <;> simp [isCtor] at h
      | dataPairList xs =>
          cases xs <;> simp [isCtor] at h
      | valList xs =>
          cases xs <;> simp [isCtor] at h
      | g1 g => simp [isCtor] at h
      | g2 g => simp [isCtor] at h
      | ml r => simp [isCtor] at h

theorem evalBoolIs_isVString_true {m : Model} {e : Expr}
    (h : evalBoolIs m (.app "(_ is VString)" [e]) true = true) :
    ∃ s, eval m e = some (SVal.val (Val.string s)) := by
  obtain ⟨sv, he, hc⟩ :=
    evalBoolIs_isCtor_true_core (m := m) (e := e)
      (f := "(_ is VString)") (ctor := "VString") evalApp_isCtor_VString
      (by rw [eval.eq_def]; rfl) h
  cases sv with
  | val v =>
      cases v <;> simp [isCtor] at hc
      rename_i s
      exact ⟨s, he⟩
  | bool b => simp [isCtor] at hc
  | int i => simp [isCtor] at hc
  | string s => simp [isCtor] at hc
  | bytes bs => simp [isCtor] at hc
  | data d =>
      cases d <;> simp [isCtor] at hc
  | dataList xs =>
      cases xs <;> simp [isCtor] at hc
  | dataPairList xs =>
      cases xs <;> simp [isCtor] at hc
  | valList xs =>
      cases xs <;> simp [isCtor] at hc
  | g1 g => simp [isCtor] at hc
  | g2 g => simp [isCtor] at hc
  | ml r => simp [isCtor] at hc

theorem evalBoolIs_isVData_true {m : Model} {e : Expr}
    (h : evalBoolIs m (.app "(_ is VData)" [e]) true = true) :
    ∃ d, eval m e = some (SVal.val (Val.data d)) := by
  obtain ⟨sv, he, hc⟩ :=
    evalBoolIs_isCtor_true_core (m := m) (e := e)
      (f := "(_ is VData)") (ctor := "VData") evalApp_isCtor_VData
      (by rw [eval.eq_def]; rfl) h
  cases sv with
  | val v =>
      cases v <;> simp [isCtor] at hc
      rename_i d
      exact ⟨d, he⟩
  | bool b => simp [isCtor] at hc
  | int i => simp [isCtor] at hc
  | string s => simp [isCtor] at hc
  | bytes bs => simp [isCtor] at hc
  | data d =>
      cases d <;> simp [isCtor] at hc
  | dataList xs =>
      cases xs <;> simp [isCtor] at hc
  | dataPairList xs =>
      cases xs <;> simp [isCtor] at hc
  | valList xs =>
      cases xs <;> simp [isCtor] at hc
  | g1 g => simp [isCtor] at hc
  | g2 g => simp [isCtor] at hc
  | ml r => simp [isCtor] at hc

theorem evalBoolIs_isVPairDataList_true {m : Model} {e : Expr}
    (h : evalBoolIs m (.app "(_ is VPairDataList)" [e]) true = true) :
    ∃ xs, eval m e = some (SVal.val (Val.pairDataList xs)) := by
  obtain ⟨sv, he, hc⟩ :=
    evalBoolIs_isCtor_true_core (m := m) (e := e)
      (f := "(_ is VPairDataList)") (ctor := "VPairDataList")
      evalApp_isCtor_VPairDataList (by rw [eval.eq_def]; rfl) h
  cases sv with
  | val v =>
      cases v <;> simp [isCtor] at hc
      rename_i xs
      exact ⟨xs, he⟩
  | bool b => simp [isCtor] at hc
  | int i => simp [isCtor] at hc
  | string s => simp [isCtor] at hc
  | bytes bs => simp [isCtor] at hc
  | data d =>
      cases d <;> simp [isCtor] at hc
  | dataList xs =>
      cases xs <;> simp [isCtor] at hc
  | dataPairList xs =>
      cases xs <;> simp [isCtor] at hc
  | valList xs =>
      cases xs <;> simp [isCtor] at hc
  | g1 g => simp [isCtor] at hc
  | g2 g => simp [isCtor] at hc
  | ml r => simp [isCtor] at hc

theorem evalBoolIs_isVArray_true {m : Model} {e : Expr}
    (h : evalBoolIs m (.app "(_ is VArray)" [e]) true = true) :
    ∃ xs, eval m e = some (SVal.val (Val.array xs)) := by
  obtain ⟨sv, he, hc⟩ :=
    evalBoolIs_isCtor_true_core (m := m) (e := e)
      (f := "(_ is VArray)") (ctor := "VArray") evalApp_isCtor_VArray
      (by rw [eval.eq_def]; rfl) h
  cases sv with
  | val v =>
      cases v <;> simp [isCtor] at hc
      rename_i xs
      exact ⟨xs, he⟩
  | bool b => simp [isCtor] at hc
  | int i => simp [isCtor] at hc
  | string s => simp [isCtor] at hc
  | bytes bs => simp [isCtor] at hc
  | data d =>
      cases d <;> simp [isCtor] at hc
  | dataList xs =>
      cases xs <;> simp [isCtor] at hc
  | dataPairList xs =>
      cases xs <;> simp [isCtor] at hc
  | valList xs =>
      cases xs <;> simp [isCtor] at hc
  | g1 g => simp [isCtor] at hc
  | g2 g => simp [isCtor] at hc
  | ml r => simp [isCtor] at hc

theorem evalBoolIs_isVG1_true {m : Model} {e : Expr}
    (h : evalBoolIs m (.app "(_ is VG1)" [e]) true = true) :
    ∃ g, eval m e = some (SVal.val (Val.g1 g)) := by
  obtain ⟨sv, he, hc⟩ :=
    evalBoolIs_isCtor_true_core (m := m) (e := e)
      (f := "(_ is VG1)") (ctor := "VG1") evalApp_isCtor_VG1
      (by rw [eval.eq_def]; rfl) h
  cases sv with
  | val v =>
      cases v <;> simp [isCtor] at hc
      rename_i g
      exact ⟨g, he⟩
  | bool b => simp [isCtor] at hc
  | int i => simp [isCtor] at hc
  | string s => simp [isCtor] at hc
  | bytes bs => simp [isCtor] at hc
  | data d =>
      cases d <;> simp [isCtor] at hc
  | dataList xs =>
      cases xs <;> simp [isCtor] at hc
  | dataPairList xs =>
      cases xs <;> simp [isCtor] at hc
  | valList xs =>
      cases xs <;> simp [isCtor] at hc
  | g1 g => simp [isCtor] at hc
  | g2 g => simp [isCtor] at hc
  | ml r => simp [isCtor] at hc

theorem evalBoolIs_isVG2_true {m : Model} {e : Expr}
    (h : evalBoolIs m (.app "(_ is VG2)" [e]) true = true) :
    ∃ g, eval m e = some (SVal.val (Val.g2 g)) := by
  obtain ⟨sv, he, hc⟩ :=
    evalBoolIs_isCtor_true_core (m := m) (e := e)
      (f := "(_ is VG2)") (ctor := "VG2") evalApp_isCtor_VG2
      (by rw [eval.eq_def]; rfl) h
  cases sv with
  | val v =>
      cases v <;> simp [isCtor] at hc
      rename_i g
      exact ⟨g, he⟩
  | bool b => simp [isCtor] at hc
  | int i => simp [isCtor] at hc
  | string s => simp [isCtor] at hc
  | bytes bs => simp [isCtor] at hc
  | data d =>
      cases d <;> simp [isCtor] at hc
  | dataList xs =>
      cases xs <;> simp [isCtor] at hc
  | dataPairList xs =>
      cases xs <;> simp [isCtor] at hc
  | valList xs =>
      cases xs <;> simp [isCtor] at hc
  | g1 g => simp [isCtor] at hc
  | g2 g => simp [isCtor] at hc
  | ml r => simp [isCtor] at hc

theorem evalBoolIs_isVMlResult_true {m : Model} {e : Expr}
    (h : evalBoolIs m (.app "(_ is VMlResult)" [e]) true = true) :
    ∃ r, eval m e = some (SVal.val (Val.ml r)) := by
  obtain ⟨sv, he, hc⟩ :=
    evalBoolIs_isCtor_true_core (m := m) (e := e)
      (f := "(_ is VMlResult)") (ctor := "VMlResult") evalApp_isCtor_VMlResult
      (by rw [eval.eq_def]; rfl) h
  cases sv with
  | val v =>
      cases v <;> simp [isCtor] at hc
      rename_i r
      exact ⟨r, he⟩
  | bool b => simp [isCtor] at hc
  | int i => simp [isCtor] at hc
  | string s => simp [isCtor] at hc
  | bytes bs => simp [isCtor] at hc
  | data d =>
      cases d <;> simp [isCtor] at hc
  | dataList xs =>
      cases xs <;> simp [isCtor] at hc
  | dataPairList xs =>
      cases xs <;> simp [isCtor] at hc
  | valList xs =>
      cases xs <;> simp [isCtor] at hc
  | g1 g => simp [isCtor] at hc
  | g2 g => simp [isCtor] at hc
  | ml r => simp [isCtor] at hc

theorem evalBoolIs_isDConstr_true {m : Model} {e : Expr}
    (h : evalBoolIs m (.app "(_ is DConstr)" [e]) true = true) :
    ∃ tag fields, eval m e = some (SVal.data (.Constr tag fields)) := by
  obtain ⟨sv, he, hc⟩ :=
    evalBoolIs_isCtor_true_core (m := m) (e := e)
      (f := "(_ is DConstr)") (ctor := "DConstr")
      evalApp_isCtor_DConstr (by rw [eval.eq_def]; rfl) h
  cases sv with
  | val v =>
      cases v <;> simp [isCtor] at hc
  | bool b => simp [isCtor] at hc
  | int i => simp [isCtor] at hc
  | string s => simp [isCtor] at hc
  | bytes bs => simp [isCtor] at hc
  | data d =>
      cases d <;> simp [isCtor] at hc
      rename_i tag fields
      exact ⟨tag, fields, he⟩
  | dataList xs =>
      cases xs <;> simp [isCtor] at hc
  | dataPairList xs =>
      cases xs <;> simp [isCtor] at hc
  | valList xs =>
      cases xs <;> simp [isCtor] at hc
  | g1 g => simp [isCtor] at hc
  | g2 g => simp [isCtor] at hc
  | ml r => simp [isCtor] at hc

theorem evalBoolIs_isDMap_true {m : Model} {e : Expr}
    (h : evalBoolIs m (.app "(_ is DMap)" [e]) true = true) :
    ∃ ps, eval m e = some (SVal.data (.Map ps)) := by
  obtain ⟨sv, he, hc⟩ :=
    evalBoolIs_isCtor_true_core (m := m) (e := e)
      (f := "(_ is DMap)") (ctor := "DMap")
      evalApp_isCtor_DMap (by rw [eval.eq_def]; rfl) h
  cases sv with
  | val v =>
      cases v <;> simp [isCtor] at hc
  | bool b => simp [isCtor] at hc
  | int i => simp [isCtor] at hc
  | string s => simp [isCtor] at hc
  | bytes bs => simp [isCtor] at hc
  | data d =>
      cases d <;> simp [isCtor] at hc
      rename_i ps
      exact ⟨ps, he⟩
  | dataList xs =>
      cases xs <;> simp [isCtor] at hc
  | dataPairList xs =>
      cases xs <;> simp [isCtor] at hc
  | valList xs =>
      cases xs <;> simp [isCtor] at hc
  | g1 g => simp [isCtor] at hc
  | g2 g => simp [isCtor] at hc
  | ml r => simp [isCtor] at hc

theorem evalBoolIs_isDList_true {m : Model} {e : Expr}
    (h : evalBoolIs m (.app "(_ is DList)" [e]) true = true) :
    ∃ xs, eval m e = some (SVal.data (.List xs)) := by
  obtain ⟨sv, he, hc⟩ :=
    evalBoolIs_isCtor_true_core (m := m) (e := e)
      (f := "(_ is DList)") (ctor := "DList")
      evalApp_isCtor_DList (by rw [eval.eq_def]; rfl) h
  cases sv with
  | val v =>
      cases v <;> simp [isCtor] at hc
  | bool b => simp [isCtor] at hc
  | int i => simp [isCtor] at hc
  | string s => simp [isCtor] at hc
  | bytes bs => simp [isCtor] at hc
  | data d =>
      cases d <;> simp [isCtor] at hc
      rename_i xs
      exact ⟨xs, he⟩
  | dataList xs =>
      cases xs <;> simp [isCtor] at hc
  | dataPairList xs =>
      cases xs <;> simp [isCtor] at hc
  | valList xs =>
      cases xs <;> simp [isCtor] at hc
  | g1 g => simp [isCtor] at hc
  | g2 g => simp [isCtor] at hc
  | ml r => simp [isCtor] at hc

theorem evalBoolIs_isDI_true {m : Model} {e : Expr}
    (h : evalBoolIs m (.app "(_ is DI)" [e]) true = true) :
    ∃ i, eval m e = some (SVal.data (.I i)) := by
  obtain ⟨sv, he, hc⟩ :=
    evalBoolIs_isCtor_true_core (m := m) (e := e)
      (f := "(_ is DI)") (ctor := "DI")
      evalApp_isCtor_DI (by rw [eval.eq_def]; rfl) h
  cases sv with
  | val v =>
      cases v <;> simp [isCtor] at hc
  | bool b => simp [isCtor] at hc
  | int i => simp [isCtor] at hc
  | string s => simp [isCtor] at hc
  | bytes bs => simp [isCtor] at hc
  | data d =>
      cases d <;> simp [isCtor] at hc
      rename_i i
      exact ⟨i, he⟩
  | dataList xs =>
      cases xs <;> simp [isCtor] at hc
  | dataPairList xs =>
      cases xs <;> simp [isCtor] at hc
  | valList xs =>
      cases xs <;> simp [isCtor] at hc
  | g1 g => simp [isCtor] at hc
  | g2 g => simp [isCtor] at hc
  | ml r => simp [isCtor] at hc

theorem evalBoolIs_isDB_true {m : Model} {e : Expr}
    (h : evalBoolIs m (.app "(_ is DB)" [e]) true = true) :
    ∃ bs, eval m e = some (SVal.data (.B bs)) := by
  obtain ⟨sv, he, hc⟩ :=
    evalBoolIs_isCtor_true_core (m := m) (e := e)
      (f := "(_ is DB)") (ctor := "DB")
      evalApp_isCtor_DB (by rw [eval.eq_def]; rfl) h
  cases sv with
  | val v =>
      cases v <;> simp [isCtor] at hc
  | bool b => simp [isCtor] at hc
  | int i => simp [isCtor] at hc
  | string s => simp [isCtor] at hc
  | bytes bs => simp [isCtor] at hc
  | data d =>
      cases d <;> simp [isCtor] at hc
      rename_i bs
      exact ⟨bs, he⟩
  | dataList xs =>
      cases xs <;> simp [isCtor] at hc
  | dataPairList xs =>
      cases xs <;> simp [isCtor] at hc
  | valList xs =>
      cases xs <;> simp [isCtor] at hc
  | g1 g => simp [isCtor] at hc
  | g2 g => simp [isCtor] at hc
  | ml r => simp [isCtor] at hc

theorem eval_unVString_of {m : Model} {e : Expr} {s : String}
    (h : eval m e = some (SVal.val (Val.string s))) :
    eval m (.app "unVString" [e]) = some (SVal.string s) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "unVString" vs) = some (.string s)
  rw [evalList.eq_def]
  simp [h]
  rw [evalList.eq_def]
  exact evalApp_unVString s

theorem eval_unVData_of {m : Model} {e : Expr} {d : Data}
    (h : eval m e = some (SVal.val (Val.data d))) :
    eval m (.app "unVData" [e]) = some (SVal.data d) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "unVData" vs) = some (.data d)
  rw [evalList.eq_def]
  simp [h]
  rw [evalList.eq_def]
  exact evalApp_unVData d

theorem eval_unVDataList_of {m : Model} {e : Expr} {xs : List Data}
    (h : eval m e = some (SVal.val (Val.dataList xs))) :
    eval m (.app "unVDataList" [e]) = some (SVal.dataList xs) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "unVDataList" vs) = some (.dataList xs)
  rw [evalList.eq_def]
  simp [h]
  rw [evalList.eq_def]
  exact evalApp_unVDataList xs

theorem eval_unVPairDataList_of {m : Model} {e : Expr} {xs : List (Data × Data)}
    (h : eval m e = some (SVal.val (Val.pairDataList xs))) :
    eval m (.app "unVPairDataList" [e]) = some (SVal.dataPairList xs) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "unVPairDataList" vs) = some (.dataPairList xs)
  rw [evalList.eq_def]
  simp [h]
  rw [evalList.eq_def]
  exact evalApp_unVPairDataList xs

theorem eval_unVList_of {m : Model} {e : Expr} {xs : List Val}
    (h : eval m e = some (SVal.val (Val.list xs))) :
    eval m (.app "unVList" [e]) = some (SVal.valList xs) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "unVList" vs) = some (.valList xs)
  rw [evalList.eq_def]
  simp [h]
  rw [evalList.eq_def]
  exact evalApp_unVList xs

theorem eval_unVArray_of {m : Model} {e : Expr} {xs : List Val}
    (h : eval m e = some (SVal.val (Val.array xs))) :
    eval m (.app "unVArray" [e]) = some (SVal.valList xs) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "unVArray" vs) = some (.valList xs)
  rw [evalList.eq_def]
  simp [h]
  rw [evalList.eq_def]
  exact evalApp_unVArray xs

theorem eval_vfst_of {m : Model} {e : Expr} {a b : Val}
    (h : eval m e = some (SVal.val (Val.pair a b))) :
    eval m (.app "vfst" [e]) = some (SVal.val a) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "vfst" vs) = some (.val a)
  rw [evalList.eq_def]
  simp [h]
  rw [evalList.eq_def]
  exact evalApp_vfst a b

theorem eval_vsnd_of {m : Model} {e : Expr} {a b : Val}
    (h : eval m e = some (SVal.val (Val.pair a b))) :
    eval m (.app "vsnd" [e]) = some (SVal.val b) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "vsnd" vs) = some (.val b)
  rw [evalList.eq_def]
  simp [h]
  rw [evalList.eq_def]
  exact evalApp_vsnd a b

theorem eval_pdfst_of {m : Model} {e : Expr} {a b : Data}
    (h : eval m e = some (SVal.val (Val.pairData a b))) :
    eval m (.app "pdfst" [e]) = some (SVal.data a) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "pdfst" vs) = some (.data a)
  rw [evalList.eq_def]
  simp [h]
  rw [evalList.eq_def]
  exact evalApp_pdfst a b

theorem eval_pdsnd_of {m : Model} {e : Expr} {a b : Data}
    (h : eval m e = some (SVal.val (Val.pairData a b))) :
    eval m (.app "pdsnd" [e]) = some (SVal.data b) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "pdsnd" vs) = some (.data b)
  rw [evalList.eq_def]
  simp [h]
  rw [evalList.eq_def]
  exact evalApp_pdsnd a b

theorem eval_vConstrTag_of {m : Model} {e : Expr} {tag : Int} {fields : List Val}
    (h : eval m e = some (SVal.val (Val.constr tag fields))) :
    eval m (.app "vConstrTag" [e]) = some (SVal.int tag) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "vConstrTag" vs) = some (.int tag)
  rw [evalList.eq_def]
  simp [h]
  rw [evalList.eq_def]
  exact evalApp_vConstrTag tag fields

theorem eval_vConstrFields_of {m : Model} {e : Expr} {tag : Int} {fields : List Val}
    (h : eval m e = some (SVal.val (Val.constr tag fields))) :
    eval m (.app "vConstrFields" [e]) = some (SVal.valList fields) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "vConstrFields" vs) = some (.valList fields)
  rw [evalList.eq_def]
  simp [h]
  rw [evalList.eq_def]
  exact evalApp_vConstrFields tag fields

theorem eval_vhead_of {m : Model} {e : Expr} {h : Val} {t : List Val}
    (he : eval m e = some (SVal.valList (h :: t))) :
    eval m (.app "vhead" [e]) = some (SVal.val h) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "vhead" vs) = some (.val h)
  rw [evalList.eq_def]
  simp [he]
  rw [evalList.eq_def]
  exact evalApp_vhead h t

theorem eval_vtail_of {m : Model} {e : Expr} {h : Val} {t : List Val}
    (he : eval m e = some (SVal.valList (h :: t))) :
    eval m (.app "vtail" [e]) = some (SVal.valList t) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "vtail" vs) = some (.valList t)
  rw [evalList.eq_def]
  simp [he]
  rw [evalList.eq_def]
  exact evalApp_vtail h t

theorem eval_vlist_length_of {m : Model} {e : Expr} {xs : List Val}
    (he : eval m e = some (SVal.valList xs)) :
    eval m (.app "vlist_length" [e]) = some (SVal.int (Int.ofNat xs.length)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "vlist_length" vs) = some (.int (Int.ofNat xs.length))
  rw [evalList.eq_def]
  simp [he]
  rw [evalList.eq_def]
  rfl

theorem eval_vlist_drop_of {m : Model} {n xs : Expr} {i : Int} {vs : List Val}
    (hn : eval m n = some (SVal.int i))
    (hxs : eval m xs = some (SVal.valList vs)) :
    eval m (.app "vlist_drop" [n, xs]) =
      some (SVal.valList (if i < 0 then vs else vs.drop i.toNat)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [n, xs]
      evalApp "vlist_drop" vs) =
        some (.valList (if i < 0 then vs else vs.drop i.toNat))
  rw [evalList.eq_def]
  simp [hn]
  rw [evalList.eq_def]
  simp [hxs]
  rw [evalList.eq_def]
  rfl

theorem eval_vlist_index_of {m : Model} {idx xs : Expr} {i : Int}
    {vs : List Val} {v : Val}
    (hidx : eval m idx = some (SVal.int i))
    (hxs : eval m xs = some (SVal.valList vs))
    (hge : 0 ≤ i)
    (hget : vs[i.toNat]? = some v) :
    eval m (.app "vlist_index" [idx, xs]) = some (SVal.val v) := by
  have hnlt : ¬ i < 0 := (Int.not_lt).mpr hge
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [idx, xs]
      evalApp "vlist_index" vs) = some (.val v)
  rw [evalList.eq_def]
  simp [hidx]
  rw [evalList.eq_def]
  simp [hxs]
  rw [evalList.eq_def]
  change (if i < 0 then none else SVal.val <$> vs[i.toNat]?) = some (SVal.val v)
  simp [hnlt, hget]

theorem eval_dhead_of {m : Model} {e : Expr} {h : Data} {t : List Data}
    (he : eval m e = some (SVal.dataList (h :: t))) :
    eval m (.app "dhead" [e]) = some (SVal.data h) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "dhead" vs) = some (.data h)
  rw [evalList.eq_def]
  simp [he]
  rw [evalList.eq_def]
  exact evalApp_dhead h t

theorem eval_dtail_of {m : Model} {e : Expr} {h : Data} {t : List Data}
    (he : eval m e = some (SVal.dataList (h :: t))) :
    eval m (.app "dtail" [e]) = some (SVal.dataList t) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "dtail" vs) = some (.dataList t)
  rw [evalList.eq_def]
  simp [he]
  rw [evalList.eq_def]
  exact evalApp_dtail h t

theorem eval_dlist_drop_of {m : Model} {n xs : Expr} {i : Int} {vs : List Data}
    (hn : eval m n = some (SVal.int i))
    (hxs : eval m xs = some (SVal.dataList vs)) :
    eval m (.app "dlist_drop" [n, xs]) =
      some (SVal.dataList (if i < 0 then vs else vs.drop i.toNat)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [n, xs]
      evalApp "dlist_drop" vs) =
        some (.dataList (if i < 0 then vs else vs.drop i.toNat))
  rw [evalList.eq_def]
  simp [hn]
  rw [evalList.eq_def]
  simp [hxs]
  rw [evalList.eq_def]
  rfl

theorem eval_DNil (m : Model) :
    eval m (.app "DNil" []) = some (.dataList []) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m []
      evalApp "DNil" vs) = some (.dataList [])
  rw [evalList.eq_def]
  rfl

theorem eval_DPNil (m : Model) :
    eval m (.app "DPNil" []) = some (.dataPairList []) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m []
      evalApp "DPNil" vs) = some (.dataPairList [])
  rw [evalList.eq_def]
  rfl

theorem eval_VInt_of {m : Model} {e : Expr} {i : Int}
    (h : eval m e = some (SVal.int i)) :
    eval m (.app "VInt" [e]) = some (.val (.int i)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "VInt" vs) = some (.val (.int i))
  rw [evalList.eq_def]
  simp [h]
  rw [evalList.eq_def]
  rfl

theorem eval_VBytes_of {m : Model} {e : Expr} {bs : ByteArray}
    (h : eval m e = some (SVal.bytes bs)) :
    eval m (.app "VBytes" [e]) = some (.val (.bytes bs)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "VBytes" vs) = some (.val (.bytes bs))
  rw [evalList.eq_def]
  simp [h]
  rw [evalList.eq_def]
  rfl

theorem eval_VString_of {m : Model} {e : Expr} {s : String}
    (h : eval m e = some (SVal.string s)) :
    eval m (.app "VString" [e]) = some (.val (.string s)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "VString" vs) = some (.val (.string s))
  rw [evalList.eq_def]
  simp [h]
  rw [evalList.eq_def]
  rfl

theorem eval_VBool_of {m : Model} {e : Expr} {b : Bool}
    (h : eval m e = some (SVal.bool b)) :
    eval m (.app "VBool" [e]) = some (.val (.bool b)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "VBool" vs) = some (.val (.bool b))
  rw [evalList.eq_def]
  simp [h]
  rw [evalList.eq_def]
  rfl

theorem eval_VUnit (m : Model) :
    eval m (.app "VUnit" []) = some (.val .unit) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m []
      evalApp "VUnit" vs) = some (.val .unit)
  rw [evalList.eq_def]
  rfl

theorem eval_VData_of {m : Model} {e : Expr} {d : Data}
    (h : eval m e = some (SVal.data d)) :
    eval m (.app "VData" [e]) = some (.val (.data d)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "VData" vs) = some (.val (.data d))
  rw [evalList.eq_def]
  simp [h]
  rw [evalList.eq_def]
  rfl

theorem eval_VList_of {m : Model} {e : Expr} {xs : List Val}
    (h : eval m e = some (SVal.valList xs)) :
    eval m (.app "VList" [e]) = some (.val (.list xs)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "VList" vs) = some (.val (.list xs))
  rw [evalList.eq_def]
  simp [h]
  rw [evalList.eq_def]
  rfl

theorem eval_VDataList_of {m : Model} {e : Expr} {xs : List Data}
    (h : eval m e = some (SVal.dataList xs)) :
    eval m (.app "VDataList" [e]) = some (.val (.dataList xs)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "VDataList" vs) = some (.val (.dataList xs))
  rw [evalList.eq_def]
  simp [h]
  rw [evalList.eq_def]
  rfl

theorem eval_VPairDataList_of {m : Model} {e : Expr}
    {xs : List (Data × Data)}
    (h : eval m e = some (SVal.dataPairList xs)) :
    eval m (.app "VPairDataList" [e]) = some (.val (.pairDataList xs)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "VPairDataList" vs) = some (.val (.pairDataList xs))
  rw [evalList.eq_def]
  simp [h]
  rw [evalList.eq_def]
  rfl

theorem eval_VPairData_of {m : Model} {a b : Expr} {da db : Data}
    (ha : eval m a = some (SVal.data da))
    (hb : eval m b = some (SVal.data db)) :
    eval m (.app "VPairData" [a, b]) = some (.val (.pairData da db)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [a, b]
      evalApp "VPairData" vs) = some (.val (.pairData da db))
  rw [evalList.eq_def]
  simp [ha]
  rw [evalList.eq_def]
  simp [hb]
  rw [evalList.eq_def]
  rfl

theorem eval_VArray_of {m : Model} {e : Expr} {xs : List Val}
    (h : eval m e = some (SVal.valList xs)) :
    eval m (.app "VArray" [e]) = some (.val (.array xs)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "VArray" vs) = some (.val (.array xs))
  rw [evalList.eq_def]
  simp [h]
  rw [evalList.eq_def]
  rfl

theorem eval_VG1_of {m : Model} {e : Expr} {g : String}
    (h : eval m e = some (SVal.g1 g)) :
    eval m (.app "VG1" [e]) = some (.val (.g1 g)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "VG1" vs) = some (.val (.g1 g))
  rw [evalList.eq_def]
  simp [h]
  rw [evalList.eq_def]
  rfl

theorem eval_VG2_of {m : Model} {e : Expr} {g : String}
    (h : eval m e = some (SVal.g2 g)) :
    eval m (.app "VG2" [e]) = some (.val (.g2 g)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "VG2" vs) = some (.val (.g2 g))
  rw [evalList.eq_def]
  simp [h]
  rw [evalList.eq_def]
  rfl

theorem eval_VMlResult_of {m : Model} {e : Expr} {r : String}
    (h : eval m e = some (SVal.ml r)) :
    eval m (.app "VMlResult" [e]) = some (.val (.ml r)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "VMlResult" vs) = some (.val (.ml r))
  rw [evalList.eq_def]
  simp [h]
  rw [evalList.eq_def]
  rfl

theorem evalBoolIs_constValValid_constr_false {m : Model} {e : Expr}
    {tag : Int} {fields : List Val}
    (h : eval m e = some (SVal.val (Val.constr tag fields))) :
    evalBoolIs m (.app "const_val_valid" [e]) false = true := by
  unfold evalBoolIs evalBool?
  rw [eval.eq_def]
  simp [evalList.eq_def, evalApp_constValValid_constr_false, h]

theorem eval_VPair_of {m : Model} {a b : Expr} {av bv : Val}
    (ha : eval m a = some (SVal.val av))
    (hb : eval m b = some (SVal.val bv)) :
    eval m (.app "VPair" [a, b]) = some (.val (.pair av bv)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [a, b]
      evalApp "VPair" vs) = some (.val (.pair av bv))
  rw [evalList.eq_def]
  simp [ha]
  rw [evalList.eq_def]
  simp [hb]
  rw [evalList.eq_def]
  rfl

theorem eval_VCons_of {m : Model} {h t : Expr} {hv : Val} {tv : List Val}
    (hh : eval m h = some (SVal.val hv))
    (ht : eval m t = some (SVal.valList tv)) :
    eval m (.app "VCons" [h, t]) = some (.valList (hv :: tv)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [h, t]
      evalApp "VCons" vs) = some (.valList (hv :: tv))
  rw [evalList.eq_def]
  simp [hh]
  rw [evalList.eq_def]
  simp [ht]
  rw [evalList.eq_def]
  rfl

theorem eval_DCons_of {m : Model} {h t : Expr} {hd : Data} {td : List Data}
    (hh : eval m h = some (SVal.data hd))
    (ht : eval m t = some (SVal.dataList td)) :
    eval m (.app "DCons" [h, t]) = some (.dataList (hd :: td)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [h, t]
      evalApp "DCons" vs) = some (.dataList (hd :: td))
  rw [evalList.eq_def]
  simp [hh]
  rw [evalList.eq_def]
  simp [ht]
  rw [evalList.eq_def]
  rfl

theorem eval_DConstr_of {m : Model} {tag fields : Expr} {i : Int}
    {xs : List Data}
    (htag : eval m tag = some (SVal.int i))
    (hfields : eval m fields = some (SVal.dataList xs)) :
    eval m (.app "DConstr" [tag, fields]) = some (.data (.Constr i xs)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [tag, fields]
      evalApp "DConstr" vs) = some (.data (.Constr i xs))
  rw [evalList.eq_def]
  simp [htag]
  rw [evalList.eq_def]
  simp [hfields]
  rw [evalList.eq_def]
  rfl

theorem eval_DMap_of {m : Model} {ps : Expr} {xs : List (Data × Data)}
    (hps : eval m ps = some (SVal.dataPairList xs)) :
    eval m (.app "DMap" [ps]) = some (.data (.Map xs)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [ps]
      evalApp "DMap" vs) = some (.data (.Map xs))
  rw [evalList.eq_def]
  simp [hps]
  rw [evalList.eq_def]
  rfl

theorem eval_DList_of {m : Model} {e : Expr} {xs : List Data}
    (he : eval m e = some (SVal.dataList xs)) :
    eval m (.app "DList" [e]) = some (.data (.List xs)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "DList" vs) = some (.data (.List xs))
  rw [evalList.eq_def]
  simp [he]
  rw [evalList.eq_def]
  rfl

theorem eval_DI_of {m : Model} {e : Expr} {i : Int}
    (he : eval m e = some (SVal.int i)) :
    eval m (.app "DI" [e]) = some (.data (.I i)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "DI" vs) = some (.data (.I i))
  rw [evalList.eq_def]
  simp [he]
  rw [evalList.eq_def]
  rfl

theorem eval_DB_of {m : Model} {e : Expr} {bs : ByteArray}
    (he : eval m e = some (SVal.bytes bs)) :
    eval m (.app "DB" [e]) = some (.data (.B bs)) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "DB" vs) = some (.data (.B bs))
  rw [evalList.eq_def]
  simp [he]
  rw [evalList.eq_def]
  rfl

theorem eval_dataConstrTag_of {m : Model} {e : Expr} {tag : Int}
    {fields : List Data}
    (he : eval m e = some (SVal.data (.Constr tag fields))) :
    eval m (.app "dataConstrTag" [e]) = some (.int tag) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "dataConstrTag" vs) = some (.int tag)
  rw [evalList.eq_def]
  simp [he]
  rw [evalList.eq_def]
  rfl

theorem eval_dataConstrFields_of {m : Model} {e : Expr} {tag : Int}
    {fields : List Data}
    (he : eval m e = some (SVal.data (.Constr tag fields))) :
    eval m (.app "dataConstrFields" [e]) = some (.dataList fields) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "dataConstrFields" vs) = some (.dataList fields)
  rw [evalList.eq_def]
  simp [he]
  rw [evalList.eq_def]
  rfl

theorem eval_dataMapEntries_of {m : Model} {e : Expr} {ps : List (Data × Data)}
    (he : eval m e = some (SVal.data (.Map ps))) :
    eval m (.app "dataMapEntries" [e]) = some (.dataPairList ps) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "dataMapEntries" vs) = some (.dataPairList ps)
  rw [evalList.eq_def]
  simp [he]
  rw [evalList.eq_def]
  rfl

theorem eval_dataListItems_of {m : Model} {e : Expr} {xs : List Data}
    (he : eval m e = some (SVal.data (.List xs))) :
    eval m (.app "dataListItems" [e]) = some (.dataList xs) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "dataListItems" vs) = some (.dataList xs)
  rw [evalList.eq_def]
  simp [he]
  rw [evalList.eq_def]
  rfl

theorem eval_dataInt_of {m : Model} {e : Expr} {i : Int}
    (he : eval m e = some (SVal.data (.I i))) :
    eval m (.app "dataInt" [e]) = some (.int i) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "dataInt" vs) = some (.int i)
  rw [evalList.eq_def]
  simp [he]
  rw [evalList.eq_def]
  rfl

theorem eval_dataBytes_of {m : Model} {e : Expr} {bs : ByteArray}
    (he : eval m e = some (SVal.data (.B bs))) :
    eval m (.app "dataBytes" [e]) = some (.bytes bs) := by
  rw [eval.eq_def]
  change
    (do
      let vs ← evalList m [e]
      evalApp "dataBytes" vs) = some (.bytes bs)
  rw [evalList.eq_def]
  simp [he]
  rw [evalList.eq_def]
  rfl

theorem evalBoolIs_isVUnit_true_of_val_unit {m : Model} {e : Expr}
    (he : eval m e = some (.val .unit)) :
    evalBoolIs m (.app "(_ is VUnit)" [e]) true = true := by
  exact (evalBoolIs_true_eq m (.app "(_ is VUnit)" [e])).mpr (by
    rw [eval.eq_def]
    change
      (do
        let vs ← evalList m [e]
        evalApp "(_ is VUnit)" vs) = some (.bool true)
    rw [evalList.eq_def]
    simp [he]
    rw [evalList.eq_def]
    rfl)

theorem evalBoolIs_isVNil_true_of_valList_nil {m : Model} {e : Expr}
    (he : eval m e = some (SVal.valList [])) :
    evalBoolIs m (.app "(_ is VNil)" [e]) true = true := by
  exact (evalBoolIs_true_eq m (.app "(_ is VNil)" [e])).mpr (by
    rw [eval.eq_def]
    change
      (do
        let vs ← evalList m [e]
        evalApp "(_ is VNil)" vs) = some (.bool true)
    rw [evalList.eq_def]
    simp [he]
    rw [evalList.eq_def]
    rfl)

theorem evalBoolIs_isVNil_false_of_valList_cons {m : Model} {e : Expr}
    {h : Val} {t : List Val}
    (he : eval m e = some (SVal.valList (h :: t))) :
    evalBoolIs m (.app "(_ is VNil)" [e]) false = true := by
  unfold evalBoolIs evalBool?
  rw [eval.eq_def]
  change
    (match
      (match
        (do
          let vs ← evalList m [e]
          evalApp "(_ is VNil)" vs) with
      | some (.bool b) => some b
      | _ => none) with
    | some b' => b' == false
    | none => false) = true
  rw [evalList.eq_def]
  simp [he]
  rw [evalList.eq_def]
  rfl

theorem evalBoolIs_not_isVNil_true_of_valList_cons {m : Model} {e : Expr}
    {h : Val} {t : List Val}
    (he : eval m e = some (SVal.valList (h :: t))) :
    evalBoolIs m (Expr.not (.app "(_ is VNil)" [e])) true = true := by
  exact (evalBoolIs_not_true m (.app "(_ is VNil)" [e])).mpr
    (evalBoolIs_isVNil_false_of_valList_cons he)

theorem evalBoolIs_isDNil_true_of_dataList_nil {m : Model} {e : Expr}
    (he : eval m e = some (SVal.dataList [])) :
    evalBoolIs m (.app "(_ is DNil)" [e]) true = true := by
  exact (evalBoolIs_true_eq m (.app "(_ is DNil)" [e])).mpr (by
    rw [eval.eq_def]
    change
      (do
        let vs ← evalList m [e]
        evalApp "(_ is DNil)" vs) = some (.bool true)
    rw [evalList.eq_def]
    simp [he]
    rw [evalList.eq_def]
    rfl)

theorem evalBoolIs_isDNil_false_of_dataList_cons {m : Model} {e : Expr}
    {h : Data} {t : List Data}
    (he : eval m e = some (SVal.dataList (h :: t))) :
    evalBoolIs m (.app "(_ is DNil)" [e]) false = true := by
  unfold evalBoolIs evalBool?
  rw [eval.eq_def]
  change
    (match
      (match
        (do
          let vs ← evalList m [e]
          evalApp "(_ is DNil)" vs) with
      | some (.bool b) => some b
      | _ => none) with
    | some b' => b' == false
    | none => false) = true
  rw [evalList.eq_def]
  simp [he]
  rw [evalList.eq_def]
  rfl

end Moist.SMT.Semantics
