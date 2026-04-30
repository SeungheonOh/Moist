import Moist.Ptah.Term
import Moist.Ptah.PLam
import Moist.Ptah.PlutusType
import Moist.Ptah.PLift

namespace Moist.Ptah

open Moist.MIR (Expr freshVar)

-- Scott-encoded list
inductive PList (a : Type) where
  | PCons : Term a → Term (PList a) → PList a
  | PNil : PList a

instance [PType a] : PType (PList a) where

instance [PType a] : PlutusType (PList a) where
  toPType := inferInstance
  PInner := POpaque
  innerPType := inferInstance
  pcon' := fun
    | .PCons h t => ⟨do pure (.Constr 0 [← h.build, ← t.build])⟩
    | .PNil => ⟨pure (.Constr 1 [])⟩
  pmatch' inner f := ⟨do
    let scrut ← inner.build
    let vh ← freshVar "h"
    let vt ← freshVar "t"
    let altCons := Expr.Lam vh (.Lam vt (← (f (.PCons ⟨pure (.Var vh)⟩ ⟨pure (.Var vt)⟩)).build))
    let altNil ← (f .PNil).build
    pure (.Case scrut [altCons, altNil])
  ⟩

-- Builtin list operations
def pheadList [PType a] : Term (PBuiltinList a → a) :=
  pforce (punsafeBuiltin .HeadList)

def ptailList [PType a] : Term (PBuiltinList a → PBuiltinList a) :=
  pforce (punsafeBuiltin .TailList)

def pnullList [PType a] : Term (PBuiltinList a → PBool) :=
  pforce (punsafeBuiltin .NullList)

def pmkCons [PType a] : Term (a → PBuiltinList a → PBuiltinList a) :=
  pforce (punsafeBuiltin .MkCons)

def pchooseList [PType a] [PType b] : Term (PBuiltinList a → b → b → b) :=
  pforce (pforce (punsafeBuiltin .ChooseList))

end Moist.Ptah
