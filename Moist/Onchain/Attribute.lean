import Lean

namespace Moist.Onchain

open Lean

initialize onchainAttr : TagAttribute ←
  registerTagAttribute `onchain
    "Mark a definition for compilation to Plutus UPLC"

initialize plutusSopAttr : TagAttribute ←
  registerTagAttribute `plutus_sop
    "Use SOP (Constr/Case) encoding for this inductive type"

initialize plutusDataAttr : TagAttribute ←
  registerTagAttribute `plutus_data
    "Use Data encoding for this inductive type"

inductive PlutusRepr
  | sop
  | data
deriving Repr, BEq, DecidableEq, Inhabited

def getPlutusRepr (env : Environment) (typeName : Name) : PlutusRepr :=
  if plutusDataAttr.hasTag env typeName then .data
  else .sop

end Moist.Onchain
