import Moist.Ptah.Term
import Moist.Ptah.PLam
import Moist.Ptah.PLift

namespace Moist.Ptah

def punit : Term PUnit := pconstant ()

def pchooseUnit [PType a] : Term (PUnit → a → a) :=
  pforce (punsafeBuiltin .ChooseUnit)

end Moist.Ptah
