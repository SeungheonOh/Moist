/-! # Plutus Core Types

Vendored type definitions for Plutus Core: Data, ByteString, Integer.
These are the minimal definitions needed by the Moist compiler.
-/

namespace Moist.Plutus

abbrev Integer := Int

abbrev ByteString := ByteArray

namespace ByteString

def toHex (bs : ByteString) : String :=
  Array.foldr (fun u acc => showWord8 u.toNat ++ acc) "" bs.data
where
  toHex (n : Nat) : String :=
    if n = 0 then "0" else if n = 1 then "1" else if n = 2 then "2" else
    if n = 3 then "3" else if n = 4 then "4" else if n = 5 then "5" else
    if n = 6 then "6" else if n = 7 then "7" else if n = 8 then "8" else
    if n = 9 then "9" else if n = 0xa then "a" else if n = 0xb then "b" else
    if n = 0xc then "c" else if n = 0xd then "d" else if n = 0xe then "e" else
    if n = 0xf then "f" else "<invalid byte>"
  showWord8 (n : Nat) : String := s!"{toHex (n / 16)}{toHex (n % 16)}"

def stringToByteString (s : String) : ByteString :=
  let rec loop
    | [], r => r
    | c :: cs, r => loop cs (r.push c.toNat.toUInt8)
  ByteArray.mk (loop s.data #[])

@[inline] def toString' (bs : ByteString) : String :=
  let chars := Array.foldr (fun u acc => (Char.ofNat u.toNat) :: acc) [] bs.data
  String.mk chars

end ByteString

instance : ToString ByteString where toString := ByteString.toString'
instance : Repr ByteString where reprPrec x _ := ByteString.toString' x
instance : Coe String ByteString where coe s := ByteString.stringToByteString s
instance : BEq ByteString where beq x y := x.data == y.data
instance : Ord ByteString where compare x y := Array.instOrd.compare x.data y.data
instance : LT ByteString where lt x y := x.data.toList < y.data.toList
instance : LE ByteString where le x y := x.data.toList ≤ y.data.toList
instance : DecidableLT ByteString := fun x y => inferInstanceAs (Decidable (x.data.toList < y.data.toList))
instance : DecidableLE ByteString := fun x y => inferInstanceAs (Decidable (x.data.toList ≤ y.data.toList))

inductive Data where
  | Constr : Integer → List Data → Data
  | Map : List (Data × Data) → Data
  | List : List Data → Data
  | I : Integer → Data
  | B : ByteString → Data
deriving Repr

mutual
  private def dataStr : Data → String
    | .Constr idx fields => s!"(Constr {idx} [{listDataStr "" fields}])"
    | .Map mxs => mapStr "" mxs
    | .List xs => s!"(List [{listDataStr "" xs}])"
    | .I i => s!"(I {i})"
    | .B bs => s!"(B {bs})"

  private def listDataStr (acc : String) : List Data → String
    | [] => acc
    | h :: tl =>
      let hStr := dataStr h
      if acc.isEmpty then listDataStr hStr tl
      else listDataStr s!"{acc}, {hStr}" tl

  private def mapStr (acc : String) : List (Data × Data) → String
    | [] => s!"(Map [{acc}])"
    | (x, y) :: tl =>
      let hstr := s!"({dataStr x}, {dataStr y})"
      if acc.isEmpty then mapStr hstr tl
      else mapStr s!"{acc}, {hstr}" tl
end

instance : ToString Data where toString := dataStr

mutual
  def eqData : Data → Data → Bool
    | .Constr i args, .Constr i' args' => i == i' && eqDataList args args'
    | .Map m, .Map m' => eqDataMap m m'
    | .List l, .List l' => eqDataList l l'
    | .I i, .I i' => i == i'
    | .B b, .B b' => b == b'
    | _, _ => false

  def eqDataList : List Data → List Data → Bool
    | [], [] => true
    | x :: xs, y :: ys => eqData x y && eqDataList xs ys
    | _, _ => false

  def eqDataMap : List (Data × Data) → List (Data × Data) → Bool
    | [], [] => true
    | (x, y) :: xs, (x', y') :: ys => eqData x x' && eqData y y' && eqDataMap xs ys
    | _, _ => false
end

instance : BEq Data where beq := eqData

/-- Decodes a ByteString to String using utf8 decoding. -/
def decodeUtf8 (bs : ByteString) : Except String String :=
  if h : String.validateUTF8 bs
  then pure (String.fromUTF8 bs h)
  else throw "decodeUtf8: invalid ByteString"

/-- Plutus AssocMap: a list of key-value pairs, encoded as Data.Map on-chain. -/
structure AssocMap (k v : Type) where
  toList : List (k × v)
deriving Repr, BEq

instance : EmptyCollection (AssocMap k v) where
  emptyCollection := ⟨[]⟩

end Moist.Plutus
