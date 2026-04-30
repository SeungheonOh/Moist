import Moist.Ptah.Term
import Moist.Ptah.PLam
import Moist.Ptah.PlutusType

namespace Moist.Ptah

open Moist.MIR (Expr freshVar)

inductive PMaybe (a : Type) where
  | PJust : Term a → PMaybe a
  | PNothing : PMaybe a

instance [PType a] : PType (PMaybe a) where

instance [PType a] : PlutusType (PMaybe a) where
  toPType := inferInstance
  PInner := POpaque
  innerPType := inferInstance
  pcon' := fun
    | .PJust x => ⟨do pure (.Constr 0 [← x.build])⟩
    | .PNothing => ⟨pure (.Constr 1 [])⟩
  pmatch' inner f := ⟨do
    let scrut ← inner.build
    let vj ← freshVar "just"
    let altJust := Expr.Lam vj (← (f (.PJust ⟨pure (.Var vj)⟩)).build)
    let altNothing ← (f .PNothing).build
    pure (.Case scrut [altJust, altNothing])
  ⟩

def pfromMaybe [PType a] (dflt : Term a) (mx : Term (PMaybe a)) : Term a :=
  pmatch mx fun
    | .PJust x => x
    | .PNothing => dflt

def pisJust [PType a] (mx : Term (PMaybe a)) : Term PBool :=
  pmatch mx fun
    | .PJust _ => punsafeConstant (.Bool true) (.AtomicType .TypeBool)
    | .PNothing => punsafeConstant (.Bool false) (.AtomicType .TypeBool)

end Moist.Ptah
