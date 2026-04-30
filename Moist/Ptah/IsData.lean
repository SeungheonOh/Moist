import Moist.Ptah.Term
import Moist.Ptah.PLam
import Moist.Ptah.Data

namespace Moist.Ptah

class PIsData (a : Type) [PType a] where
  pdataImpl : Term a → Term PData
  pfromDataImpl : Term PData → Term a

def pdata [PType a] [PIsData a] (x : Term a) : Term (PAsData a) :=
  punsafeCoerce (PIsData.pdataImpl x)

def pfromData [PType a] [PIsData a] (x : Term (PAsData a)) : Term a :=
  PIsData.pfromDataImpl (punsafeCoerce x)

instance : PIsData PInteger where
  pdataImpl x := piData # x
  pfromDataImpl d := punIData # d

instance : PIsData PByteString where
  pdataImpl x := pbData # x
  pfromDataImpl d := punBData # d

instance : PIsData PData where
  pdataImpl x := x
  pfromDataImpl d := d

end Moist.Ptah
