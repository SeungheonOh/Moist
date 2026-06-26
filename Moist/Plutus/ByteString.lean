namespace Moist.Plutus

@[irreducible] def bytesSingletonValue (n : Int) : ByteArray :=
  ByteArray.mk #[n.toNat.toUInt8]

def bytesSingleton? (n : Int) : Option ByteArray :=
  if n < 0 || n > 255 then none
  else some (bytesSingletonValue n)

@[irreducible] def bytesNthValue (bs : ByteArray) (i : Int) : Int :=
  Int.ofNat (bs.get! i.toNat).toNat

def bytesNth? (bs : ByteArray) (i : Int) : Option Int :=
  if i < 0 || i ≥ Int.ofNat bs.size then none
  else some (bytesNthValue bs i)

@[irreducible] def bytesExtractValue (bs : ByteArray) (start len : Int) : ByteArray :=
  let s := if start < 0 then 0 else start.toNat
  let l := if len < 0 then 0 else len.toNat
  let s := min s bs.size
  let e := min (s + l) bs.size
  bs.extract s e

theorem bytesExtractValue_clamp (bs : ByteArray) (start len : Int) :
    bytesExtractValue bs (if start < 0 then 0 else start)
        (if len < 0 then 0 else len) =
      bytesExtractValue bs start len := by
  unfold bytesExtractValue
  by_cases hs : start < 0 <;> by_cases hl : len < 0 <;>
    simp [hs, hl]

/-- Lexicographic less-than for ByteArrays. -/
def bytesLt (a b : ByteArray) : Bool :=
  let len := min a.size b.size
  go 0 len a b
where
  go (i len : Nat) (a b : ByteArray) : Bool :=
    if i >= len then a.size < b.size
    else
      let ai := a.get! i
      let bi := b.get! i
      if ai < bi then true
      else if ai > bi then false
      else go (i + 1) len a b

/-- Lexicographic less-than-or-equal for ByteArrays. -/
def bytesLe (a b : ByteArray) : Bool :=
  a == b || bytesLt a b

end Moist.Plutus
