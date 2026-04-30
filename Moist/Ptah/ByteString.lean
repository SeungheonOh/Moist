import Moist.Ptah.Term
import Moist.Ptah.PLam

namespace Moist.Ptah

def pappendByteString : Term (PByteString → PByteString → PByteString) :=
  punsafeBuiltin .AppendByteString

def pconsByteString : Term (PInteger → PByteString → PByteString) :=
  punsafeBuiltin .ConsByteString

def psliceByteString : Term (PInteger → PInteger → PByteString → PByteString) :=
  punsafeBuiltin .SliceByteString

def plengthOfByteString : Term (PByteString → PInteger) :=
  punsafeBuiltin .LengthOfByteString

def pindexByteString : Term (PByteString → PInteger → PInteger) :=
  punsafeBuiltin .IndexByteString

def pequalsByteString : Term (PByteString → PByteString → PBool) :=
  punsafeBuiltin .EqualsByteString

def plessThanByteString : Term (PByteString → PByteString → PBool) :=
  punsafeBuiltin .LessThanByteString

def plessThanEqualsByteString : Term (PByteString → PByteString → PBool) :=
  punsafeBuiltin .LessThanEqualsByteString

def psha2_256 : Term (PByteString → PByteString) :=
  punsafeBuiltin .Sha2_256

def psha3_256 : Term (PByteString → PByteString) :=
  punsafeBuiltin .Sha3_256

def pblake2b_256 : Term (PByteString → PByteString) :=
  punsafeBuiltin .Blake2b_256

def pblake2b_224 : Term (PByteString → PByteString) :=
  punsafeBuiltin .Blake2b_224

def pkeccak_256 : Term (PByteString → PByteString) :=
  punsafeBuiltin .Keccak_256

def pripemd_160 : Term (PByteString → PByteString) :=
  punsafeBuiltin .Ripemd_160

def pverifyEd25519Signature :
    Term (PByteString → PByteString → PByteString → PBool) :=
  punsafeBuiltin .VerifyEd25519Signature

def pverifyEcdsaSecp256k1Signature :
    Term (PByteString → PByteString → PByteString → PBool) :=
  punsafeBuiltin .VerifyEcdsaSecp256k1Signature

def pverifySchnorrSecp256k1Signature :
    Term (PByteString → PByteString → PByteString → PBool) :=
  punsafeBuiltin .VerifySchnorrSecp256k1Signature

def pintegerToByteString :
    Term (PBool → PInteger → PInteger → PByteString) :=
  punsafeBuiltin .IntegerToByteString

def pbyteStringToInteger :
    Term (PBool → PByteString → PInteger) :=
  punsafeBuiltin .ByteStringToInteger

def pserializeData : Term (PData → PByteString) :=
  punsafeBuiltin .SerializeData

end Moist.Ptah
