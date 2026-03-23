import PlutusCore.UPLC.FlatEncoding

/-! # UPLC Flat Decoder

Thin compatibility wrapper around sc-fvt's FlatEncoding decoder.
The sc-fvt decoder produces named terms (PlutusCore.UPLC.Term.Term).
-/

namespace Moist.Plutus.Decode

namespace Internal
def decodeProgramFromBits := PlutusCore.UPLC.FlatEncoding.Internal.decodeProgramFromBits
end Internal

def decodeProgramFromHexString := PlutusCore.UPLC.FlatEncoding.decodeProgramFromHexString
def decodeProgramFromByteString := PlutusCore.UPLC.FlatEncoding.decodeProgramFromByteString

end Moist.Plutus.Decode
