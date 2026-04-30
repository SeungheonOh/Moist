import Moist.Ptah.Term
import Moist.Ptah.PLam
import Moist.Ptah.PLift

namespace Moist.Ptah

def pappendString : Term (PString → PString → PString) :=
  punsafeBuiltin .AppendString

def pequalsString : Term (PString → PString → PBool) :=
  punsafeBuiltin .EqualsString

def pencodeUtf8 : Term (PString → PByteString) :=
  punsafeBuiltin .EncodeUtf8

def pdecodeUtf8 : Term (PByteString → PString) :=
  punsafeBuiltin .DecodeUtf8

def ptrace' [PType a] : Term (PString → a → a) :=
  pforce (punsafeBuiltin .Trace)

def ptrace [PType a] (msg : String) (x : Term a) : Term a :=
  ptrace' # pconstant msg # x

end Moist.Ptah
