import Moist.Ptah.Term
import Moist.Ptah.PLam
import Moist.Ptah.PlutusType

namespace Moist.Ptah

open Moist.MIR (Expr freshVar)

-- Scott-encoded pair
inductive PPair (a b : Type) where
  | PPair : Term a → Term b → PPair a b

instance [PType a] [PType b] : PType (PPair a b) where

instance [PType a] [PType b] : PlutusType (PPair a b) where
  toPType := inferInstance
  PInner := POpaque
  innerPType := inferInstance
  pcon' := fun
    | .PPair x y => ⟨do pure (.Constr 0 [← x.build, ← y.build])⟩
  pmatch' inner f := ⟨do
    let scrut ← inner.build
    let vx ← freshVar "fst"
    let vy ← freshVar "snd"
    let alt := Expr.Lam vx (.Lam vy (← (f (.PPair ⟨pure (.Var vx)⟩ ⟨pure (.Var vy)⟩)).build))
    pure (.Case scrut [alt])
  ⟩

-- Builtin pair operations
def pfstPair [PType a] [PType b] : Term (PBuiltinPair a b → a) :=
  pforce (pforce (punsafeBuiltin .FstPair))

def psndPair [PType a] [PType b] : Term (PBuiltinPair a b → b) :=
  pforce (pforce (punsafeBuiltin .SndPair))

end Moist.Ptah
