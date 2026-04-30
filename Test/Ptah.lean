import Moist.Ptah.Prelude
import Moist.Plutus.Encode
import Moist.MIR.Pretty

open Moist.Ptah
open Moist.Plutus (Integer ByteString)

set_option linter.unusedVariables false

/-! ## Helpers -/

def pnil_int : Term (PList PInteger) := pcon PList.PNil
def pcons_int (x : Term PInteger) (xs : Term (PList PInteger)) : Term (PList PInteger) :=
  pcon (.PCons x xs)

def mkList (xs : List (Term PInteger)) : Term (PList PInteger) :=
  xs.foldr (fun x acc => pcons_int x acc) pnil_int

/-! ## 1. Arithmetic -/

def pid : Term (PInteger → PInteger) :=
  plam fun (x : Term PInteger) => x

def myAdd : Term (PInteger → PInteger → PInteger) :=
  plam fun (x : Term PInteger) (y : Term PInteger) => x + y

def myLet : Term PInteger :=
  plet (42 : Term PInteger) fun x => x + x

def fibonacci : Term (PInteger → PInteger) :=
  plam fun (n : Term PInteger) =>
    let go := pfix fun (self : Term (PInteger → PInteger → PInteger → PInteger))
                       (i : Term PInteger) =>
      plam fun (a : Term PInteger) (b : Term PInteger) =>
        pif (pequalsInteger # i # n)
          a
          (self # (i + 1) # b # (a + b))
    go # 0 # 0 # 1

def gcd' : Term (PInteger → PInteger → PInteger) :=
  pfix fun (self : Term (PInteger → PInteger → PInteger))
           (a : Term PInteger) =>
    plam fun (b : Term PInteger) =>
      pif (pequalsInteger # b # (0 : Term PInteger))
        a
        (self # b # (pmodInteger # a # b))

def power : Term (PInteger → PInteger → PInteger) :=
  pfix fun (self : Term (PInteger → PInteger → PInteger))
           (base : Term PInteger) =>
    plam fun (exp : Term PInteger) =>
      pif (pequalsInteger # exp # (0 : Term PInteger))
        (1 : Term PInteger)
        (base * (self # base # (exp - 1)))

def abs' : Term (PInteger → PInteger) :=
  plam fun (x : Term PInteger) =>
    pif (plessThanInteger # x # (0 : Term PInteger))
      (- x)
      x

/-! ## 2. Higher-order combinators -/

def pconst [PType a] [PType b] : Term (a → b → a) :=
  plam fun (x : Term a) (_ : Term b) => x

def pflip [PType a] [PType b] [PType c] :
    Term ((a → b → c) → b → a → c) :=
  plam fun (f : Term (a → b → c)) (x : Term b) (y : Term a) =>
    f # y # x

def pcompose [PType a] [PType b] [PType c] :
    Term ((b → c) → (a → b) → a → c) :=
  plam fun (f : Term (b → c)) (g : Term (a → b)) (x : Term a) =>
    f # (g # x)

def pon [PType a] [PType b] [PType c] :
    Term ((b → b → c) → (a → b) → a → a → c) :=
  plam fun (f : Term (b → b → c)) (g : Term (a → b))
           (x : Term a) (y : Term a) =>
    f # (g # x) # (g # y)

/-! ## 3. List operations -/

def plength : Term (PList PInteger → PInteger) :=
  pfix fun (self : Term (PList PInteger → PInteger))
           (xs : Term (PList PInteger)) =>
    pmatch xs fun
      | .PCons _ t => 1 + (self # t)
      | .PNil => (0 : Term PInteger)

def pmap : Term ((PInteger → PInteger) → PList PInteger → PList PInteger) :=
  plam fun (f : Term (PInteger → PInteger)) =>
    pfix fun (self : Term (PList PInteger → PList PInteger))
             (xs : Term (PList PInteger)) =>
      pmatch xs fun
        | .PCons h t => pcon (.PCons (f # h) (self # t))
        | .PNil => pcon PList.PNil

def pfilter : Term ((PInteger → PBool) → PList PInteger → PList PInteger) :=
  plam fun (pred : Term (PInteger → PBool)) =>
    pfix fun (self : Term (PList PInteger → PList PInteger))
             (xs : Term (PList PInteger)) =>
      pmatch xs fun
        | .PCons h t =>
            pif (pred # h)
              (pcon (.PCons h (self # t)))
              (self # t)
        | .PNil => pcon PList.PNil

def pfoldl' : Term ((PInteger → PInteger → PInteger) → PInteger → PList PInteger → PInteger) :=
  plam fun (f : Term (PInteger → PInteger → PInteger))
           (acc0 : Term PInteger) (xs : Term (PList PInteger)) =>
    let go := pfix fun (self : Term (PInteger → PList PInteger → PInteger))
                       (acc : Term PInteger) =>
      plam fun (ys : Term (PList PInteger)) =>
        pmatch ys fun
          | .PCons h t => self # (f # acc # h) # t
          | .PNil => acc
    go # acc0 # xs

def preverse : Term (PList PInteger → PList PInteger) :=
  plam fun (xs : Term (PList PInteger)) =>
    let go := pfix fun (self : Term (PList PInteger → PList PInteger → PList PInteger))
                       (src : Term (PList PInteger)) =>
      plam fun (acc : Term (PList PInteger)) =>
        pmatch src fun
          | .PCons h t => self # t # pcon (.PCons h acc)
          | .PNil => acc
    go # xs # pcon PList.PNil

def pzipWith :
    Term ((PInteger → PInteger → PInteger) → PList PInteger → PList PInteger → PList PInteger) :=
  plam fun (f : Term (PInteger → PInteger → PInteger)) =>
    pfix fun (self : Term (PList PInteger → PList PInteger → PList PInteger))
             (xs : Term (PList PInteger)) =>
      plam fun (ys : Term (PList PInteger)) =>
        pmatch xs fun
          | .PCons hx tx =>
              pmatch ys fun
                | .PCons hy ty => pcon (.PCons (f # hx # hy) (self # tx # ty))
                | .PNil => pcon PList.PNil
          | .PNil => pcon PList.PNil

def pany : Term ((PInteger → PBool) → PList PInteger → PBool) :=
  plam fun (pred : Term (PInteger → PBool)) =>
    pfix fun (self : Term (PList PInteger → PBool))
             (xs : Term (PList PInteger)) =>
      pmatch xs fun
        | .PCons h t => por' (pred # h) (self # t)
        | .PNil => pconstant false

def pall : Term ((PInteger → PBool) → PList PInteger → PBool) :=
  plam fun (pred : Term (PInteger → PBool)) =>
    pfix fun (self : Term (PList PInteger → PBool))
             (xs : Term (PList PInteger)) =>
      pmatch xs fun
        | .PCons h t => pand' (pred # h) (self # t)
        | .PNil => pconstant true

/-! ## 4. Maybe operations -/

def pmapMaybe [PType a] [PType b] (f : Term (a → b))
    (mx : Term (PMaybe a)) : Term (PMaybe b) :=
  pmatch mx fun
    | .PJust x => pcon (.PJust (f # x))
    | .PNothing => pcon .PNothing

def pbindMaybe [PType a] [PType b] (mx : Term (PMaybe a))
    (f : Term (a → PMaybe b)) : Term (PMaybe b) :=
  pmatch mx fun
    | .PJust x => f # x
    | .PNothing => pcon .PNothing

def pmaybeToBool [PType a] (mx : Term (PMaybe a)) : Term PBool :=
  pmatch mx fun
    | .PJust _ => pconstant true
    | .PNothing => pconstant false

/-! ## 5. Pair operations -/

def pfst [PType a] [PType b] (p : Term (PPair a b)) : Term a :=
  pmatch p fun | .PPair x _ => x

def psnd [PType a] [PType b] (p : Term (PPair a b)) : Term b :=
  pmatch p fun | .PPair _ y => y

def pmapFst [PType a] [PType a'] [PType b]
    (f : Term (a → a')) (p : Term (PPair a b)) : Term (PPair a' b) :=
  pmatch p fun | .PPair x y => pcon (.PPair (f # x) y)

def pmapSnd [PType a] [PType b] [PType b']
    (f : Term (b → b')) (p : Term (PPair a b)) : Term (PPair a b') :=
  pmatch p fun | .PPair x y => pcon (.PPair x (f # y))

def punpair [PType a] [PType b] [PType c]
    (f : Term (a → b → c)) (p : Term (PPair a b)) : Term c :=
  pmatch p fun | .PPair x y => f # x # y

/-! ## 6. PEither (derived) -/

inductive PEither (a b : Type) where
  | PLeft  : Term a → PEither a b
  | PRight : Term b → PEither a b

derive_plutustype PEither

/-! ## 6b. PTriple (derived — 3 fields, 1 ctor) -/

inductive PTriple (a b c : Type) where
  | PTriple : Term a → Term b → Term c → PTriple a b c

derive_plutustype PTriple

/-! ## 6c. POrdering (derived — 0 fields, 3 ctors) -/

inductive POrdering where
  | PLT : POrdering
  | PEQ : POrdering
  | PGT : POrdering

derive_plutustype POrdering

/-! ## 6d. Data-encoded types (derive_plutusdata) -/

inductive DPair (a b : Type) where
  | mk : Term a → Term b → DPair a b

derive_plutusdata_list DPair

inductive DMaybe (a : Type) where
  | DJust : Term a → DMaybe a
  | DNothing : DMaybe a

derive_plutusdata DMaybe

inductive DUnit where
  | mk : DUnit

derive_plutusdata DUnit

def dPairTest : Term (DPair PInteger PInteger → PInteger) :=
  plam fun (p : Term (DPair PInteger PInteger)) =>
    pmatch p fun
      | .mk x y => x + y

def dMaybeTest : Term (DMaybe PInteger → PInteger) :=
  plam fun (m : Term (DMaybe PInteger)) =>
    pmatch m fun
      | .DJust x => x
      | .DNothing => (0 : Term PInteger)

def dUnitTest : Term (DUnit → PInteger) :=
  plam fun (u : Term DUnit) =>
    pmatch u fun
      | .mk => (42 : Term PInteger)

-- Data round-trip: construct DPair as Data, pass through, destructure
def dPairRoundTrip : Term (PInteger → PInteger → PInteger) :=
  plam fun (x : Term PInteger) (y : Term PInteger) =>
    let pair := pcon (DPair.mk x y)
    pmatch pair fun
      | .mk a b => a + b

def peither [PType a] [PType b] [PType c]
    (fl : Term (a → c)) (fr : Term (b → c))
    (e : Term (PEither a b)) : Term c :=
  pmatch e fun
    | .PLeft x  => fl # x
    | .PRight y => fr # y

def pmapEither [PType a] [PType b] [PType c] [PType d]
    (fl : Term (a → c)) (fr : Term (b → d))
    (e : Term (PEither a b)) : Term (PEither c d) :=
  pmatch e fun
    | .PLeft x  => pcon (.PLeft (fl # x))
    | .PRight y => pcon (.PRight (fr # y))

def pisLeft [PType a] [PType b] (e : Term (PEither a b)) : Term PBool :=
  pmatch e fun
    | .PLeft _  => pconstant true
    | .PRight _ => pconstant false

/-! ## 7. Data encoding -/

def intToDataAndBack : Term (PInteger → PInteger) :=
  plam fun (n : Term PInteger) => pfromData (pdata n)

def checkDataEquality : Term (PData → PData → PBool) :=
  plam fun (d1 : Term PData) (d2 : Term PData) => pequalsData # d1 # d2

/-! ## 8. Builtin list operations -/

def builtinListLength : Term (PBuiltinList PData → PInteger) :=
  pfix fun (self : Term (PBuiltinList PData → PInteger))
           (xs : Term (PBuiltinList PData)) =>
    pif (pnullList # xs)
      (0 : Term PInteger)
      (1 + (self # (ptailList # xs)))

/-! ## 9. Tracing -/

def ptracedAdd : Term (PInteger → PInteger → PInteger) :=
  plam fun (x : Term PInteger) (y : Term PInteger) =>
    ptrace "computing sum" (x + y)

/-! ## 10. Let-chain pipeline -/

def doubleAndIncrement : Term (PInteger → PInteger) :=
  plam fun (x : Term PInteger) =>
    plet (x * (2 : Term PInteger)) fun doubled =>
      plet (doubled + (1 : Term PInteger)) fun result =>
        result

def pipeline : Term (PInteger → PInteger) :=
  plam fun (x : Term PInteger) =>
    plet (x * x) fun squared =>
      plet (squared + squared) fun doubled =>
        plet (doubled - (1 : Term PInteger)) fun result =>
          result

/-! ## 11. Validator-like patterns -/

def checkSignature : Term (PByteString → PByteString → PBool) :=
  plam fun (expected : Term PByteString) (actual : Term PByteString) =>
    pequalsByteString # expected # actual

def requireTrue [PType a] (cond : Term PBool) (msg : String) (k : Term a) : Term a :=
  pif cond k (ptrace msg perror)

def miniValidator :
    Term (PByteString → PInteger → PBuiltinList PData → PBool) :=
  plam fun (pkh : Term PByteString) (amount : Term PInteger)
           (_ctx : Term (PBuiltinList PData)) =>
    requireTrue (a := PBool)
      (plessThanInteger # (0 : Term PInteger) # amount)
      "amount must be positive" <|
    requireTrue (a := PBool)
      (plessThanInteger # (0 : Term PInteger) # (plengthOfByteString # pkh))
      "empty pubkey hash" <|
    pconstant true

/-! ## 12. Composed examples -/

def psafeHead : Term (PList PInteger → PMaybe PInteger) :=
  plam fun (xs : Term (PList PInteger)) =>
    pmatch xs fun
      | .PCons h _ => pcon (PMaybe.PJust h)
      | .PNil => pcon (PMaybe.PNothing)

def psumPositives : Term (PList PInteger → PInteger) :=
  plam fun (xs : Term (PList PInteger)) =>
    let positives := pfilter #
      (plam fun (n : Term PInteger) => plessThanInteger # (0 : Term PInteger) # n)
      # xs
    let go := pfix fun (self : Term (PList PInteger → PInteger))
                       (ys : Term (PList PInteger)) =>
      pmatch ys fun
        | .PCons h t => h + (self # t)
        | .PNil => (0 : Term PInteger)
    go # positives

-- Construct [1, 2, 3] and sum it end-to-end
def psum : Term (PList PInteger → PInteger) :=
  pfix fun (self : Term (PList PInteger → PInteger))
           (xs : Term (PList PInteger)) =>
    pmatch xs fun
      | .PCons h t => h + (self # t)
      | .PNil => (0 : Term PInteger)

def example1 : Term PInteger :=
  psum # mkList [1, 2, 3]

/-! ## Compilation tests -/

#eval do
  match compile pid with
  | .ok _ => IO.println "pid OK"
  | .error e => IO.println s!"FAIL: {e}"

#eval! do
  match compile fibonacci with
  | .ok _ => IO.println "fibonacci OK"
  | .error e => IO.println s!"FAIL: {e}"

#eval! do
  match compile gcd' with
  | .ok _ => IO.println "gcd OK"
  | .error e => IO.println s!"FAIL: {e}"

#eval! do
  match compile power with
  | .ok _ => IO.println "power OK"
  | .error e => IO.println s!"FAIL: {e}"

#eval do
  match compile abs' with
  | .ok _ => IO.println "abs OK"
  | .error e => IO.println s!"FAIL: {e}"

#eval! do
  match compile plength with
  | .ok _ => IO.println "plength OK"
  | .error e => IO.println s!"FAIL: {e}"

#eval! do
  match compile pmap with
  | .ok _ => IO.println "pmap OK"
  | .error e => IO.println s!"FAIL: {e}"

#eval! do
  match compile pfilter with
  | .ok _ => IO.println "pfilter OK"
  | .error e => IO.println s!"FAIL: {e}"

#eval! do
  match compile pfoldl' with
  | .ok _ => IO.println "pfoldl OK"
  | .error e => IO.println s!"FAIL: {e}"

#eval! do
  match compile preverse with
  | .ok _ => IO.println "preverse OK"
  | .error e => IO.println s!"FAIL: {e}"

#eval! do
  match compile pzipWith with
  | .ok _ => IO.println "pzipWith OK"
  | .error e => IO.println s!"FAIL: {e}"

#eval! do
  match compile pany with
  | .ok _ => IO.println "pany OK"
  | .error e => IO.println s!"FAIL: {e}"

#eval! do
  match compile pall with
  | .ok _ => IO.println "pall OK"
  | .error e => IO.println s!"FAIL: {e}"

#eval do
  match compile intToDataAndBack with
  | .ok _ => IO.println "intToDataAndBack OK"
  | .error e => IO.println s!"FAIL: {e}"

#eval! do
  match compile builtinListLength with
  | .ok _ => IO.println "builtinListLength OK"
  | .error e => IO.println s!"FAIL: {e}"

#eval do
  match compile ptracedAdd with
  | .ok _ => IO.println "ptracedAdd OK"
  | .error e => IO.println s!"FAIL: {e}"

#eval! do
  match compile doubleAndIncrement with
  | .ok _ => IO.println "doubleAndIncrement OK"
  | .error e => IO.println s!"FAIL: {e}"

#eval! do
  match compile pipeline with
  | .ok _ => IO.println "pipeline OK"
  | .error e => IO.println s!"FAIL: {e}"

#eval! do
  match compile miniValidator with
  | .ok _ => IO.println "miniValidator OK"
  | .error e => IO.println s!"FAIL: {e}"

#eval! do
  match compile psafeHead with
  | .ok _ => IO.println "psafeHead OK"
  | .error e => IO.println s!"FAIL: {e}"

#eval! do
  match compile psumPositives with
  | .ok _ => IO.println "psumPositives OK"
  | .error e => IO.println s!"FAIL: {e}"

#eval! do
  match compile example1 with
  | .ok _ => IO.println "example1 OK"
  | .error e => IO.println s!"FAIL: {e}"

-- Data-encoded type tests
#eval! do
  match compile dPairTest with
  | .ok _ => IO.println "dPairTest (data list) OK"
  | .error e => IO.println s!"FAIL: {e}"

#eval! do
  match compile dMaybeTest with
  | .ok _ => IO.println "dMaybeTest (data constr) OK"
  | .error e => IO.println s!"FAIL: {e}"

#eval! do
  match compile dUnitTest with
  | .ok _ => IO.println "dUnitTest (data constr) OK"
  | .error e => IO.println s!"FAIL: {e}"

#eval! do
  match compile dPairRoundTrip with
  | .ok _ => IO.println "dPairRoundTrip OK"
  | .error e => IO.println s!"FAIL: {e}"

-- Derived PEither: compile test
def eitherTest : Term (PEither PInteger PBool → PInteger) :=
  plam fun (e : Term (PEither PInteger PBool)) =>
    pmatch e fun
      | .PLeft n => n
      | .PRight b => pif b 1 0

-- Derived PTriple: construct and destructure
def tripleTest : Term (PTriple PInteger PInteger PInteger → PInteger) :=
  plam fun (t : Term (PTriple PInteger PInteger PInteger)) =>
    pmatch t fun
      | .PTriple x y z => x + y + z

-- Derived POrdering: 0-field enum
def ordToInt : Term (POrdering → PInteger) :=
  plam fun (o : Term POrdering) =>
    pmatch o fun
      | .PLT => (0 : Term PInteger)
      | .PEQ => (1 : Term PInteger)
      | .PGT => (2 : Term PInteger)

#eval! do
  match compile eitherTest with
  | .ok _ => IO.println "eitherTest (derived) OK"
  | .error e => IO.println s!"FAIL: {e}"

#eval! do
  match compile tripleTest with
  | .ok _ => IO.println "tripleTest (derived) OK"
  | .error e => IO.println s!"FAIL: {e}"

#eval! do
  match compile ordToInt with
  | .ok _ => IO.println "ordToInt (derived) OK"
  | .error e => IO.println s!"FAIL: {e}"

-- #ptah_mir: unoptimized MIR
#ptah_mir  pid
#ptah_mir  (plam fun (x : Term PInteger) (y : Term PInteger) => x + y)

-- #ptah_mir!: optimized + pre-lowered MIR
#ptah_mir! pid
#ptah_mir! (plam fun (x : Term PInteger) (y : Term PInteger) => x + y)

-- #ptah_uplc: human-readable UPLC
#ptah_uplc pid
#ptah_uplc (plam fun (x : Term PInteger) (y : Term PInteger) => x + y)

-- #ptah_uplc!: standard Plutus textual format
#ptah_uplc! pid
#ptah_uplc! (plam fun (x : Term PInteger) (y : Term PInteger) => x + y)

-- #ptah_hex: flat-encoded hex
#ptah_hex  pid
#ptah_hex  (plam fun (x : Term PInteger) (y : Term PInteger) => x + y)

/-! ## plift tests (require Zig FFI — run via `lake exe ptah_test`) -/

def main : IO Unit := do
  IO.println "=== plift tests ==="

  let v1 : Integer ← plift (42 : Term PInteger)
  IO.println s!"plift 42 = {v1}"
  assert! v1 == 42

  let v2 : Integer ← plift ((10 : Term PInteger) + (20 : Term PInteger))
  IO.println s!"plift (10 + 20) = {v2}"
  assert! v2 == 30

  let v3 : Bool ← plift (pconstant true : Term PBool)
  IO.println s!"plift true = {v3}"
  assert! v3 == true

  let v4 : String ← plift (pconstant "hello" : Term PString)
  IO.println s!"plift \"hello\" = {v4}"
  assert! v4 == "hello"

  let v5 : Unit ← plift punit
  IO.println s!"plift () = {repr v5}"

  let v6 : Integer ← plift ((7 : Term PInteger) * (6 : Term PInteger))
  IO.println s!"plift (7 * 6) = {v6}"
  assert! v6 == 42

  let v7 : Integer ← plift (pif (pconstant true) (1 : Term PInteger) 0)
  IO.println s!"plift (if true then 1 else 0) = {v7}"
  assert! v7 == 1

  let v8 : Integer ← plift (intToDataAndBack # (99 : Term PInteger))
  IO.println s!"plift (int→data→int 99) = {v8}"
  assert! v8 == 99

  let v9 : Integer ← plift example1
  IO.println s!"plift sum [1,2,3] = {v9}"
  assert! v9 == 6

  IO.println "all plift tests passed"
