import Moist.MIR.Expr
import Moist.Plutus.Term

namespace Moist.Ptah

open Moist.MIR (Expr VarId FreshM FreshState freshVar runFresh)
open Moist.Plutus.Term (Const BuiltinType BuiltinFun AtomicType)

class PType (a : Type) where

inductive POpaque where
instance : PType POpaque where

inductive PInteger where
instance : PType PInteger where

inductive PBool where
instance : PType PBool where

inductive PByteString where
instance : PType PByteString where

inductive PString where
instance : PType PString where

inductive PUnit where
instance : PType PUnit where

inductive PData where
instance : PType PData where

instance [PType a] [PType b] : PType (a → b) where

inductive PDelayed (a : Type) where
instance [PType a] : PType (PDelayed a) where

inductive PAsData (a : Type) where
instance [PType a] : PType (PAsData a) where

inductive PBuiltinList (a : Type) where
instance [PType a] : PType (PBuiltinList a) where

inductive PBuiltinPair (a b : Type) where
instance [PType a] [PType b] : PType (PBuiltinPair a b) where

structure Term (a : Type) where
  build : FreshM Expr

@[inline] def punsafeCoerce (x : Term a) : Term b := ⟨x.build⟩

@[inline] def perror [PType a] : Term a := ⟨pure .Error⟩

@[inline] def punsafeBuiltin [PType a] (b : BuiltinFun) : Term a := ⟨pure (.Builtin b)⟩

@[inline] def punsafeConstant [PType a] (c : Const) (ty : BuiltinType) : Term a :=
  ⟨pure (.Lit (c, ty))⟩

end Moist.Ptah
