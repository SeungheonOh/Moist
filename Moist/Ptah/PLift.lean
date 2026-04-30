import Moist.Ptah.Term
import Moist.Plutus.Term

namespace Moist.Ptah

open Moist.MIR (Expr)
open Moist.Plutus.Term (Const BuiltinType AtomicType)
open Moist.Plutus (Integer ByteString)

private abbrev UPLCTerm := Moist.Plutus.Term.Term

class PLift (a : Type) [PType a] where
  AsLean : Type
  pconstant : AsLean → Term a
  uplcToLean : UPLCTerm → Except String AsLean

instance : PLift PInteger where
  AsLean := Integer
  pconstant n := ⟨pure (.Lit (.Integer n, .AtomicType .TypeInteger))⟩
  uplcToLean
    | .Constant (.Integer n, _) => .ok n
    | t => .error s!"plift PInteger: expected integer constant, got {repr t}"

instance : PLift PBool where
  AsLean := Bool
  pconstant b := ⟨pure (.Lit (.Bool b, .AtomicType .TypeBool))⟩
  uplcToLean
    | .Constant (.Bool b, _) => .ok b
    | t => .error s!"plift PBool: expected bool constant, got {repr t}"

instance : PLift PString where
  AsLean := String
  pconstant s := ⟨pure (.Lit (.String s, .AtomicType .TypeString))⟩
  uplcToLean
    | .Constant (.String s, _) => .ok s
    | t => .error s!"plift PString: expected string constant, got {repr t}"

instance : PLift PByteString where
  AsLean := ByteString
  pconstant bs := ⟨pure (.Lit (.ByteString bs, .AtomicType .TypeByteString))⟩
  uplcToLean
    | .Constant (.ByteString bs, _) => .ok bs
    | t => .error s!"plift PByteString: expected bytestring constant, got {repr t}"

instance : PLift PUnit where
  AsLean := Unit
  pconstant _ := ⟨pure (.Lit (.Unit, .AtomicType .TypeUnit))⟩
  uplcToLean
    | .Constant (.Unit, _) => .ok ()
    | t => .error s!"plift PUnit: expected unit constant, got {repr t}"

instance : PLift PData where
  AsLean := Moist.Plutus.Data
  pconstant d := ⟨pure (.Lit (.Data d, .AtomicType .TypeData))⟩
  uplcToLean
    | .Constant (.Data d, _) => .ok d
    | t => .error s!"plift PData: expected data constant, got {repr t}"

export PLift (pconstant)

def pcon_int (n : Integer) : Term PInteger := pconstant n
def pcon_bool (b : Bool) : Term PBool := pconstant b
def pcon_str (s : String) : Term PString := pconstant s
def pcon_bs (bs : ByteString) : Term PByteString := pconstant bs

end Moist.Ptah
