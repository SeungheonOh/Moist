import Moist.SMT.Syntax

namespace Moist.SMT

open Moist.Plutus (Data)
open Moist.Plutus.Term (Const)

/-!
# Transparent SMT-LIB renderer

This is the portable reference renderer.  It is kept separate from syntax,
symbolic compilation, simulated solver semantics, and proof modules so ports
can translate and test this boundary directly.
-/

namespace SSort

def render : SSort → String
  | .bool => "Bool"
  | .int => "Int"
  | .string => "UString"
  | .bytes => "Bytes"
  | .data => "Data"
  | .dataList => "DataList"
  | .dataPairList => "DataPairList"
  | .val => "Val"
  | .valList => "ValList"
  | .g1 => "G1"
  | .g2 => "G2"
  | .ml => "MlResult"
  | .custom s => s

end SSort

namespace Expr

private def renderByte (b : UInt8) : String :=
  "(seq.unit " ++ toString b.toNat ++ ")"

private def renderBytes (bs : ByteArray) : String :=
  bs.data.foldl
    (fun acc b => "(seq.++ " ++ acc ++ " " ++ renderByte b ++ ")")
    "(as seq.empty Bytes)"

/--
Render strings as sequences of Unicode scalar values instead of SMT-LIB's
built-in `String` sort.  Z3's native string sort is intentionally restricted
to a smaller code-point range than Lean/UPLC strings, so using it would make
the compiler silently incomplete for otherwise valid constants.  `Char`
guarantees that every emitted element is a Unicode scalar value.
-/
private def renderString (s : String) : String :=
  s.data.foldl
    (fun acc c => "(seq.++ " ++ acc ++ " (seq.unit " ++ toString c.toNat ++ "))")
    "(as seq.empty UString)"

private def renderInt (i : Int) : String :=
  if i < 0 then "(- " ++ toString i.natAbs ++ ")" else toString i

mutual
  private def renderData : Data → String
    | .Constr tag fields => "(DConstr " ++ renderInt tag ++ " " ++ renderDataList fields ++ ")"
    | .Map ps => "(DMap " ++ renderDataPairList ps ++ ")"
    | .List xs => "(DList " ++ renderDataList xs ++ ")"
    | .I i => "(DI " ++ renderInt i ++ ")"
    | .B bs => "(DB " ++ renderBytes bs ++ ")"

  private def renderDataList : List Data → String
    | [] => "DNil"
    | x :: xs => "(DCons " ++ renderData x ++ " " ++ renderDataList xs ++ ")"

  private def renderDataPairList : List (Data × Data) → String
    | [] => "DPNil"
    | (k, v) :: xs => "(DPCons " ++ renderData k ++ " " ++ renderData v ++ " " ++ renderDataPairList xs ++ ")"

  private def renderConstVal : Const → String
    | .Integer i => "(VInt " ++ renderInt i ++ ")"
    | .ByteString bs => "(VBytes " ++ renderBytes bs ++ ")"
    | .String s => "(VString " ++ renderString s ++ ")"
    | .Unit => "VUnit"
    | .Bool b => "(VBool " ++ (if b then "true)" else "false)")
    | .ConstList xs => "(VList " ++ renderConstValList xs ++ ")"
    | .ConstDataList xs => "(VDataList " ++ renderDataList xs ++ ")"
    | .ConstPairDataList xs => "(VPairDataList " ++ renderDataPairList xs ++ ")"
    | .Pair (a, b) => "(VPair " ++ renderConstVal a ++ " " ++ renderConstVal b ++ ")"
    | .PairData (a, b) => "(VPairData " ++ renderData a ++ " " ++ renderData b ++ ")"
    | .Data d => "(VData " ++ renderData d ++ ")"
    | .ConstArray xs => "(VArray " ++ renderConstValList xs ++ ")"
    | .Bls12_381_G1_element => "(VG1 g1_default)"
    | .Bls12_381_G2_element => "(VG2 g2_default)"
    | .Bls12_381_MlResult => "(VMlResult ml_default)"

  private def renderConstValList : List Const → String
    | [] => "VNil"
    | x :: xs => "(VCons " ++ renderConstVal x ++ " " ++ renderConstValList xs ++ ")"
end

mutual
def render : Expr → String
  | .sym s => s
  | .int i => renderInt i
  | .bytes bs => renderBytes bs
  | .dataLit d => renderData d
  | .dataListLit xs => renderDataList xs
  | .dataPairListLit xs => renderDataPairList xs
  | .constListLit xs => renderConstValList xs
  | .bool true => "true"
  | .bool false => "false"
  | .str s => renderString s
  | .app f [] => f
  | .app f args => "(" ++ f ++ " " ++ renderArgs args ++ ")"
  | .ite c t e => "(ite " ++ render c ++ " " ++ render t ++ " " ++ render e ++ ")"

def renderArgs : List Expr → String
  | [] => ""
  | x :: xs => render x ++ renderArgsTail xs

def renderArgsTail : List Expr → String
  | [] => ""
  | x :: xs => " " ++ render x ++ renderArgsTail xs
end

end Expr

namespace Command

def renderBinder (b : String × SSort) : String :=
  "(" ++ b.1 ++ " " ++ b.2.render ++ ")"

def render : Command → String
  | .raw s => s
  | .comment s => "; " ++ s
  | .setLogic s => "(set-logic " ++ s ++ ")"
  | .declareConst n s => "(declare-const " ++ n ++ " " ++ s.render ++ ")"
  | .declareFun n args ret =>
      "(declare-fun " ++ n ++ " (" ++ String.intercalate " " (args.map SSort.render) ++ ") " ++ ret.render ++ ")"
  | .defineFun n args ret body =>
      "(define-fun " ++ n ++ " (" ++ String.intercalate " " (args.map renderBinder) ++ ") " ++
        ret.render ++ " " ++ body.render ++ ")"
  | .assert e => "(assert " ++ e.render ++ ")"
  | .checkSat => "(check-sat)"
  | .checkSatUsing tactic => "(check-sat-using " ++ tactic ++ ")"
  | .getModel => "(get-model)"
  | .getValue es => "(get-value (" ++ String.intercalate " " (es.map Expr.render) ++ "))"

end Command

namespace Script

def render (s : Script) : String :=
  String.intercalate "\n" (s.commands.map Command.render) ++ "\n"

end Script

end Moist.SMT
