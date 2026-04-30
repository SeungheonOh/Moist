import Moist.Ptah.Term

namespace Moist.Ptah

class PlutusType (a : Type) where
  toPType : PType a
  PInner : Type
  innerPType : PType PInner
  pcon' : a → Term PInner
  pmatch' : {r : Type} → [PType r] → Term PInner → (a → Term r) → Term r

attribute [instance] PlutusType.toPType
attribute [instance] PlutusType.innerPType

@[reducible] def PInner (a : Type) [PlutusType a] := PlutusType.PInner (a := a)

def pcon [PlutusType a] (x : a) : Term a :=
  punsafeCoerce (PlutusType.pcon' x)

def pmatch [pa : PlutusType a] [pr : PType r] (x : Term a) (f : a → Term r) : Term r :=
  @PlutusType.pmatch' a pa r pr (punsafeCoerce x) f

end Moist.Ptah
