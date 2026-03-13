import Lean

namespace Moist.Onchain

open Lean

initialize onchainAttr : TagAttribute ←
  registerTagAttribute `onchain
    "Mark a definition for compilation to Plutus UPLC"

initialize plutusSopAttr : TagAttribute ←
  registerTagAttribute `plutus_sop
    "Use SOP (Constr/Case) encoding for this inductive type"

end Moist.Onchain
