import Moist.Ptah.Term
import Moist.Ptah.PLam
import Moist.Ptah.PLift

namespace Moist.Ptah

open Moist.Plutus.Term (BuiltinFun)
open Moist.Plutus (Integer)

def paddInteger : Term (PInteger → PInteger → PInteger) :=
  punsafeBuiltin .AddInteger

def psubtractInteger : Term (PInteger → PInteger → PInteger) :=
  punsafeBuiltin .SubtractInteger

def pmultiplyInteger : Term (PInteger → PInteger → PInteger) :=
  punsafeBuiltin .MultiplyInteger

def pdivideInteger : Term (PInteger → PInteger → PInteger) :=
  punsafeBuiltin .DivideInteger

def pquotientInteger : Term (PInteger → PInteger → PInteger) :=
  punsafeBuiltin .QuotientInteger

def premainderInteger : Term (PInteger → PInteger → PInteger) :=
  punsafeBuiltin .RemainderInteger

def pmodInteger : Term (PInteger → PInteger → PInteger) :=
  punsafeBuiltin .ModInteger

def pequalsInteger : Term (PInteger → PInteger → PBool) :=
  punsafeBuiltin .EqualsInteger

def plessThanInteger : Term (PInteger → PInteger → PBool) :=
  punsafeBuiltin .LessThanInteger

def plessThanEqualsInteger : Term (PInteger → PInteger → PBool) :=
  punsafeBuiltin .LessThanEqualsInteger

instance : HAdd (Term PInteger) (Term PInteger) (Term PInteger) where
  hAdd a b := paddInteger # a # b

instance : HSub (Term PInteger) (Term PInteger) (Term PInteger) where
  hSub a b := psubtractInteger # a # b

instance : HMul (Term PInteger) (Term PInteger) (Term PInteger) where
  hMul a b := pmultiplyInteger # a # b

instance : HDiv (Term PInteger) (Term PInteger) (Term PInteger) where
  hDiv a b := pdivideInteger # a # b

instance : HMod (Term PInteger) (Term PInteger) (Term PInteger) where
  hMod a b := pmodInteger # a # b

instance : OfNat (Term PInteger) n where
  ofNat := pconstant (Int.ofNat n)

instance : Neg (Term PInteger) where
  neg x := psubtractInteger # (pconstant (0 : Integer)) # x

end Moist.Ptah
