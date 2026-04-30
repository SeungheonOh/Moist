import Moist.Ptah.Term
import Moist.Ptah.PLam
import Moist.Ptah.PLift

namespace Moist.Ptah

def pif' [PType a] : Term (PBool → a → a → a) :=
  pforce (punsafeBuiltin .IfThenElse)

def pif [PType a] (cond : Term PBool) (t f : Term a) : Term a :=
  pforce (pif' # cond # pdelay t # pdelay f)

def pnot (x : Term PBool) : Term PBool :=
  pif x (pconstant false) (pconstant true)

def pand' (a b : Term PBool) : Term PBool :=
  pif a b (pconstant false)

def por' (a b : Term PBool) : Term PBool :=
  pif a (pconstant true) b

end Moist.Ptah
