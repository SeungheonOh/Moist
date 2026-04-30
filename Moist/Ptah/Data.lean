import Moist.Ptah.Term
import Moist.Ptah.PLam

namespace Moist.Ptah

def pconstrData : Term (PInteger → PBuiltinList PData → PData) :=
  punsafeBuiltin .ConstrData

def punConstrData : Term (PData → PBuiltinPair PInteger (PBuiltinList PData)) :=
  punsafeBuiltin .UnConstrData

def plistData : Term (PBuiltinList PData → PData) :=
  punsafeBuiltin .ListData

def punListData : Term (PData → PBuiltinList PData) :=
  punsafeBuiltin .UnListData

def pmapData : Term (PBuiltinList (PBuiltinPair PData PData) → PData) :=
  punsafeBuiltin .MapData

def punMapData : Term (PData → PBuiltinList (PBuiltinPair PData PData)) :=
  punsafeBuiltin .UnMapData

def piData : Term (PInteger → PData) :=
  punsafeBuiltin .IData

def punIData : Term (PData → PInteger) :=
  punsafeBuiltin .UnIData

def pbData : Term (PByteString → PData) :=
  punsafeBuiltin .BData

def punBData : Term (PData → PByteString) :=
  punsafeBuiltin .UnBData

def pequalsData : Term (PData → PData → PBool) :=
  punsafeBuiltin .EqualsData

def pchooseData [PType a] : Term (PData → a → a → a → a → a → a) :=
  pforce (punsafeBuiltin .ChooseData)

def pmkPairData : Term (PData → PData → PBuiltinPair PData PData) :=
  punsafeBuiltin .MkPairData

def pmkNilData : Term (PUnit → PBuiltinList PData) :=
  punsafeBuiltin .MkNilData

def pmkNilPairData : Term (PUnit → PBuiltinList (PBuiltinPair PData PData)) :=
  punsafeBuiltin .MkNilPairData

end Moist.Ptah
