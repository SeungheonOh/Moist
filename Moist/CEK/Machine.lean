import Moist.CEK.Builtins

namespace Moist.CEK

open Moist.Plutus.Term (Term Const BuiltinType BuiltinFun)

/-! # CEK Machine for UPLC

Small-step CEK machine for de Bruijn indexed UPLC terms.
Follows the sc-fvt reference implementation (input-output-hk/sc-fvt staging branch)
and the plutuz Zig CEK machine for budget enforcement.

## Budget Model

Evaluation takes an `ExBudget` limit. Costs are subtracted as execution proceeds:
- **Machine step costs** are charged at each `compute` entry (not on `return` transitions)
- **Builtin costs** are charged when a builtin becomes fully saturated
- If either CPU or memory goes negative, evaluation fails with `outOfBudget`

This matches plutuz's `restricting = true` mode used by the Cardano ledger.

## de Bruijn Convention

`Var n` (1-based): `Var 1` = innermost binding = head of environment.
-/

/-! ## ExBudget -/

structure ExBudget where
  cpu : Int := 0
  mem : Int := 0
deriving Repr, BEq, Inhabited

instance : Add ExBudget where
  add a b := ⟨a.cpu + b.cpu, a.mem + b.mem⟩

instance : Sub ExBudget where
  sub a b := ⟨a.cpu - b.cpu, a.mem - b.mem⟩

instance : ToString ExBudget where
  toString b := s!"(\{cpu: {b.cpu}\n| mem: {b.mem}})"

def ExBudget.zero : ExBudget := ⟨0, 0⟩

/-- Check if budget is exhausted (either dimension negative). -/
def ExBudget.isExhausted (b : ExBudget) : Bool :=
  b.cpu < 0 || b.mem < 0

/-! ## Machine Step Costs (Cost Model C) -/

def startupCost : ExBudget := ⟨100, 100⟩
def stepCost : ExBudget := ⟨16000, 100⟩

/-! ## Continuation Frames -/

inductive Frame where
  | force : Frame
  | arg : Term → CekEnv → Frame
  | funV : CekValue → Frame
  | applyArg : CekValue → Frame
  | constrField : Nat → List CekValue → List Term → CekEnv → Frame
  | caseScrutinee : List Term → CekEnv → Frame

abbrev Stack := List Frame

/-! ## Machine State -/

inductive State where
  | compute : Stack → CekEnv → Term → State
  | ret : Stack → CekValue → State
  | error : State
  | halt : CekValue → State

/-! ## Single Step Transition -/

/-- Map a constant value to a constructor tag, expected constructor count, and fields.
Returns `(tag, numCtors, fields)` where `numCtors = 0` means "don't check branch count". -/
def constToTagAndFields : Const → Option (Nat × Nat × List CekValue)
  | .Bool false => some (0, 2, [])
  | .Bool true => some (1, 2, [])
  | .Unit => some (0, 1, [])
  | .Integer n => if n >= 0 then some (n.toNat, 0, []) else none
  -- Plutus SOP: Cons=tag 0, Nil=tag 1
  | .ConstList [] => some (1, 2, [])
  | .ConstList (h :: t) => some (0, 2, [.VCon h, .VCon (.ConstList t)])
  | .ConstDataList [] => some (1, 2, [])
  | .ConstDataList (h :: t) => some (0, 2, [.VCon (.Data h), .VCon (.ConstDataList t)])
  | .Pair (a, b) => some (0, 1, [.VCon a, .VCon b])
  | .PairData (a, b) => some (0, 1, [.VCon (.Data a), .VCon (.Data b)])
  | _ => none

/-- Perform one step of the CEK machine (pure, no costing). -/
def step : State → State
  | .error => .error
  | .halt v => .halt v

  -- Compute transitions
  | .compute s ρ (.Var n) =>
    match ρ.lookup n with
    | some v => .ret s v
    | none => .error
  | .compute s _ (.Constant (c, _)) => .ret s (.VCon c)
  | .compute s _ (.Builtin b) => .ret s (.VBuiltin b [] (expectedArgs b))
  | .compute s ρ (.Lam _ body) => .ret s (.VLam body ρ)
  | .compute s ρ (.Delay body) => .ret s (.VDelay body ρ)
  | .compute s ρ (.Force e) => .compute (.force :: s) ρ e
  | .compute s ρ (.Apply f x) => .compute (.arg x ρ :: s) ρ f
  | .compute s ρ (.Constr tag (m :: ms)) =>
    .compute (.constrField tag [] ms ρ :: s) ρ m
  | .compute s _ (.Constr tag []) => .ret s (.VConstr tag [])
  | .compute s ρ (.Case scrut alts) =>
    .compute (.caseScrutinee alts ρ :: s) ρ scrut
  | .compute _ _ .Error => .error

  -- Return transitions
  | .ret [] v => .halt v
  | .ret (.force :: s) (.VDelay body ρ) => .compute s ρ body
  | .ret (.force :: s) (.VBuiltin b args ea) =>
    match ea.head with
    | .argQ =>
      match ea.tail with
      | some rest => .ret s (.VBuiltin b args rest)
      | none => match evalBuiltin b args with
        | some v => .ret s v
        | none => .error
    | .argV => .error
  | .ret (.force :: _) _ => .error
  | .ret (.arg m ρ :: s) vf => .compute (.funV vf :: s) ρ m
  | .ret (.funV (.VLam body ρ) :: s) vx => .compute s (ρ.extend vx) body
  | .ret (.funV (.VBuiltin b args ea) :: s) vx =>
    match ea.head with
    | .argV =>
      match ea.tail with
      | some rest => .ret s (.VBuiltin b (vx :: args) rest)
      | none => match evalBuiltin b (vx :: args) with
        | some v => .ret s v
        | none => .error
    | .argQ => .error
  | .ret (.funV _ :: _) _ => .error
  | .ret (.constrField tag done (m :: ms) ρ :: s) v =>
    .compute (.constrField tag (v :: done) ms ρ :: s) ρ m
  | .ret (.constrField tag done [] _ :: s) v =>
    .ret s (.VConstr tag ((v :: done).reverse))
  | .ret (.applyArg vx :: s) (.VLam body ρ) =>
    .compute s (ρ.extend vx) body
  | .ret (.applyArg vx :: s) (.VBuiltin b args ea) =>
    match ea.head with
    | .argV =>
      match ea.tail with
      | some rest => .ret s (.VBuiltin b (vx :: args) rest)
      | none => match evalBuiltin b (vx :: args) with
        | some v => .ret s v
        | none => .error
    | .argQ => .error
  | .ret (.applyArg _ :: _) _ => .error
  | .ret (.caseScrutinee alts ρ :: s) (.VConstr tag fields) =>
    match alts[tag]? with
    | some alt =>
      let fieldFrames := fields.map Frame.applyArg
      .compute (fieldFrames ++ s) ρ alt
    | none => .error
  | .ret (.caseScrutinee alts ρ :: s) (.VCon c) =>
    match constToTagAndFields c with
    | some (tag, numCtors, fields) =>
      if numCtors > 0 && alts.length > numCtors then .error
      else match alts[tag]? with
        | some alt =>
          let fieldFrames := fields.map Frame.applyArg
          .compute (fieldFrames ++ s) ρ alt
        | none => .error
    | none => .error
  | .ret (.caseScrutinee _ _ :: _) _ => .error

/-! ## Size Measurement for Builtin Costing -/

open Moist.Plutus (Data ByteString)

def integerSize (i : Int) : Nat :=
  if i == 0 then 1 else Nat.log2 i.natAbs / 64 + 1

def byteStringSize (bs : ByteArray) : Nat :=
  (bs.size - 1) / 8 + 1

partial def dataSize : Data → Nat
  | .Constr _ fields => 4 + fields.foldl (fun acc d => acc + dataSize d) 0
  | .Map pairs => 4 + pairs.foldl (fun acc (k, v) => acc + dataSize k + dataSize v) 0
  | .List items => 4 + items.foldl (fun acc d => acc + dataSize d) 0
  | .I i => 4 + integerSize i
  | .B bs => 4 + byteStringSize bs

partial def valueSize : CekValue → Nat
  | .VCon c => constSize c
  | .VConstr _ fields => fields.length
  | _ => 1
where
  constSize : Const → Nat
    | .Integer i => integerSize i
    | .ByteString bs => byteStringSize bs
    | .String s => s.length
    | .Bool _ => 1 | .Unit => 1
    | .Data d => dataSize d
    | .ConstList l => l.length
    | .ConstDataList l => l.length
    | .ConstPairDataList l => l.length
    | .ConstArray l => l.length
    | .Pair _ => 1 | .PairData _ => 1
    | .Bls12_381_G1_element => 18
    | .Bls12_381_G2_element => 36
    | .Bls12_381_MlResult => 72

/-! ## Builtin Costing

Compute the ExBudget cost of executing a fully saturated builtin.
Arguments are in reversed order (most recent first).
-/

private def argSizes (args : List CekValue) : List Nat :=
  args.reverse.map valueSize

private def cConst (c : Int) (_ : List Nat) : Int := c
private def cMaxSz (i s : Int) (sz : List Nat) : Int := match sz with
  | [x, y] => i + s * Int.ofNat (max x y) | _ => i
private def cMinSz (i s : Int) (sz : List Nat) : Int := match sz with
  | [x, y] => i + s * Int.ofNat (min x y) | _ => i
private def cAddSz (i s : Int) (sz : List Nat) : Int := match sz with
  | [x, y] => i + s * Int.ofNat (x + y) | _ => i
private def cMulSz (i s : Int) (sz : List Nat) : Int := match sz with
  | [x, y] => i + s * Int.ofNat (x * y) | _ => i
private def cSubSz (i s mn : Int) (sz : List Nat) : Int := match sz with
  | [x, y] => i + s * max mn (if x ≥ y then Int.ofNat (x - y) else mn)
  | _ => i
private def cLin (i s : Int) (n : Nat) : Int := i + s * Int.ofNat n
private def cLinDiag (c i s : Int) (sz : List Nat) : Int := match sz with
  | [x, y] => if x == y then i + s * Int.ofNat x else c | _ => c
private def cQuadXY (c00 c10 c01 c20 c11 c02 mn : Int) (sz : List Nat) : Int :=
  match sz with
  | [x, y] =>
    let xi := Int.ofNat x; let yi := Int.ofNat y
    max mn (c00 + c10*xi + c01*yi + c20*xi*xi + c11*xi*yi + c02*yi*yi)
  | _ => mn
private def cAboveDiag (c : Int) (f : List Nat → Int) (sz : List Nat) : Int :=
  match sz with | [x, y] => if x < y then c else f sz | _ => f sz
private def cQuad (c0 c1 c2 : Int) (n : Nat) : Int :=
  let s := Int.ofNat n; c0 + c1*s + c2*s*s

/-- Extract integer value from a CekValue argument (in application order). -/
private def argIntVal (args : List CekValue) (i : Nat) : Int :=
  match (args.reverse)[i]? with
  | some (.VCon (.Integer n)) => n
  | _ => 0

def builtinCost (b : BuiltinFun) (args : List CekValue) : ExBudget :=
  let sz := argSizes args
  let s0 := sz[0]?.getD 0; let s1 := sz[1]?.getD 0; let s2 := sz[2]?.getD 0
  ⟨cpuCost b args sz s0 s1 s2, memCost b args sz s0 s1 s2⟩
where
  cpuCost (b : BuiltinFun) (args : List CekValue) (sz : List Nat) (s0 s1 s2 : Nat) : Int := match b with
    | .AddInteger | .SubtractInteger => cMaxSz 100788 420 sz
    | .MultiplyInteger => cMulSz 90434 519 sz
    | .DivideInteger | .QuotientInteger | .RemainderInteger | .ModInteger =>
      cAboveDiag 85848 (cQuadXY 123203 1716 7305 57 549 (-900) 85848) sz
    | .EqualsInteger => cMinSz 51775 558 sz
    | .LessThanInteger => cMinSz 44749 541 sz
    | .LessThanEqualsInteger => cMinSz 43285 552 sz
    | .AppendByteString => cAddSz 1000 173 sz
    | .ConsByteString => cLin 72010 178 s1
    | .SliceByteString => cLin 20467 1 s2
    | .LengthOfByteString => 22100 | .IndexByteString => 13169
    | .EqualsByteString => cLinDiag 24548 29498 38 sz
    | .LessThanByteString | .LessThanEqualsByteString => cMinSz 28999 74 sz
    | .Sha2_256 => cLin 270652 22588 s0
    | .Sha3_256 => cLin 1457325 64566 s0
    | .Blake2b_256 => cLin 201305 8356 s0
    | .Blake2b_224 => cLin 207616 8310 s0
    | .Keccak_256 => cLin 2261318 64571 s0
    | .Ripemd_160 => cLin 1964219 24520 s0
    | .VerifyEd25519Signature => cLin 53384111 14333 s1
    | .VerifyEcdsaSecp256k1Signature => 43053543
    | .VerifySchnorrSecp256k1Signature => cLin 43574283 26308 s1
    | .AppendString => cAddSz 1000 59957 sz
    | .EqualsString => cLinDiag 39184 1000 60594 sz
    | .EncodeUtf8 => cLin 1000 42921 s0
    | .DecodeUtf8 => cLin 91189 769 s0
    | .IfThenElse => 76049 | .ChooseUnit => 61462 | .Trace => 59498
    | .FstPair => 141895 | .SndPair => 141992
    | .ChooseList => 132994 | .MkCons => 72362
    | .HeadList => 83150 | .TailList => 81663 | .NullList => 74433
    | .ChooseData => 94375
    | .ConstrData => 22151 | .MapData => 68246 | .ListData => 33852
    | .IData => 15299 | .BData => 11183
    | .UnConstrData => 24588 | .UnMapData => 24623 | .UnListData => 25933
    | .UnIData => 20744 | .UnBData => 20142
    | .EqualsData => cMinSz 898148 27279 sz
    | .MkPairData => 11546 | .MkNilData => 7243 | .MkNilPairData => 7391
    | .SerializeData => cLin 955506 213312 s0
    | .IntegerToByteString => cQuad 1293828 28716 63 s2
    | .ByteStringToInteger => cQuad 1006041 43623 251 s1
    | .AndByteString | .OrByteString | .XorByteString =>
      100181 + 726 * Int.ofNat s1 + 719 * Int.ofNat s2
    | .ComplementByteString => cLin 107878 680 s0
    | .ReadBit => 95336
    | .WriteBits => cLin 281145 18848 s1
    | .ReplicateByte =>
      -- Cost scales with result size: ceil(VALUE(count)/8) words
      let countVal := argIntVal args 0
      let resultWords := if countVal <= 0 then 0 else ((countVal + 7) / 8).toNat
      cLin 180194 159 resultWords
    | .ShiftByteString => cLin 158519 8942 s0
    | .RotateByteString => cLin 159378 8813 s0
    | .CountSetBits => cLin 107490 3298 s0
    | .FindFirstSetBit => cLin 106057 655 s0
    | .ExpModInteger =>
      -- exp_mod_cost with 50% penalty if base > modulus
      let e := Int.ofNat s1; let m := Int.ofNat s2
      let baseCost := 607153 + 231697*e*m + 53144*e*m*m
      if s0 > s2 then baseCost * 3 / 2 else baseCost
    | .Bls12_381_G1_add => 962335 | .Bls12_381_G1_neg => 267929
    | .Bls12_381_G1_scalarMul => cLin 76433006 8868 s0
    | .Bls12_381_G1_equal => 442008
    | .Bls12_381_G1_hashToGroup => cLin 52538055 3756 s0
    | .Bls12_381_G1_compress => 2780678 | .Bls12_381_G1_uncompress => 52948122
    | .Bls12_381_G2_add => 1995836 | .Bls12_381_G2_neg => 284546
    | .Bls12_381_G2_scalarMul => cLin 158221314 26549 s0
    | .Bls12_381_G2_equal => 901022
    | .Bls12_381_G2_hashToGroup => cLin 166917843 4307 s0
    | .Bls12_381_G2_compress => 3227919 | .Bls12_381_G2_uncompress => 74698472
    | .Bls12_381_millerLoop => 254006273
    | .Bls12_381_mulMlResult => 2174038 | .Bls12_381_finalVerify => 333849714
    | .DropList =>
      let countVal := argIntVal args 0
      cLin 116711 1957 countVal.natAbs
    | .Bls12_381_G1_multiScalarMul => cLin 321837444 25087669 s0
    | .Bls12_381_G2_multiScalarMul => cLin 617887431 67302824 s0
    | .IndexArray => 232010
    | .LengthOfArray => 231883
    | .ListToArray => cLin 1000 24838 s0
    | .InsertCoin => cLin 356924 18413 s0
    | .LookupCoin => cLin 219951 9444 s2
    | .ScaleValue => cLin 1000 277577 s1
    | .UnionValue => 1000
    | .ValueContains => 213283
    | .ValueData => cLin 1000 38159 s0
    | .UnValueData => cQuad 1000 95933 1 s0

  memCost (b : BuiltinFun) (args : List CekValue) (sz : List Nat) (s0 s1 s2 : Nat) : Int := match b with
    | .AddInteger | .SubtractInteger => cMaxSz 1 1 sz
    | .MultiplyInteger => cAddSz 0 1 sz
    | .DivideInteger | .QuotientInteger => cSubSz 0 1 1 sz
    | .RemainderInteger | .ModInteger => cLin 0 1 s1
    | .EqualsInteger | .LessThanInteger | .LessThanEqualsInteger => 1
    | .AppendByteString | .ConsByteString => cAddSz 0 1 sz
    | .SliceByteString => cLin 4 0 s2
    | .LengthOfByteString => 10 | .IndexByteString => 4
    | .EqualsByteString | .LessThanByteString | .LessThanEqualsByteString => 1
    | .Sha2_256 | .Sha3_256 | .Blake2b_256 | .Blake2b_224 | .Keccak_256 => 4
    | .Ripemd_160 => 3
    | .VerifyEd25519Signature | .VerifyEcdsaSecp256k1Signature
    | .VerifySchnorrSecp256k1Signature => 10
    | .AppendString => cAddSz 4 1 sz
    | .EqualsString => 1
    | .EncodeUtf8 | .DecodeUtf8 => cLin 4 2 s0
    | .IfThenElse => 1 | .ChooseUnit => 4 | .Trace => 32
    | .FstPair | .SndPair => 32 | .ChooseList => 32
    | .MkCons | .HeadList | .TailList | .NullList => 32
    | .ChooseData => 32
    | .ConstrData | .MapData | .ListData | .IData | .BData => 32
    | .UnConstrData | .UnMapData | .UnListData | .UnIData | .UnBData => 32
    | .EqualsData => 1
    | .MkPairData | .MkNilData | .MkNilPairData => 32
    | .SerializeData => cLin 0 2 s0
    | .IntegerToByteString =>
      -- literal_in_y_or_linear_in_z: y=width VALUE, z=SIZE(n)
      -- If width==0: 0 + 1*SIZE(n). Else: ceil(width/8) (bytestring word size)
      let widthVal := argIntVal args 1
      if widthVal == 0 then Int.ofNat s2
      else (widthVal + 7) / 8
    | .ByteStringToInteger => cLin 0 1 s1
    | .AndByteString | .OrByteString | .XorByteString => cLin 0 1 (max s1 s2)
    | .ComplementByteString => cLin 0 1 s0
    | .ReadBit | .CountSetBits | .FindFirstSetBit => 1
    | .WriteBits => cLin 0 1 s0
    | .ReplicateByte =>
      let countVal := argIntVal args 0
      let resultWords := if countVal <= 0 then 0 else ((countVal + 7) / 8).toNat
      cLin 1 1 resultWords
    | .ShiftByteString | .RotateByteString => cLin 0 1 s0
    | .ExpModInteger => cLin 0 1 s2
    | .Bls12_381_G1_add | .Bls12_381_G1_neg | .Bls12_381_G1_scalarMul
    | .Bls12_381_G1_hashToGroup | .Bls12_381_G1_uncompress => 18
    | .Bls12_381_G1_equal => 1 | .Bls12_381_G1_compress => 6
    | .Bls12_381_G2_add | .Bls12_381_G2_neg | .Bls12_381_G2_scalarMul
    | .Bls12_381_G2_hashToGroup | .Bls12_381_G2_uncompress => 36
    | .Bls12_381_G2_equal => 1 | .Bls12_381_G2_compress => 12
    | .Bls12_381_millerLoop | .Bls12_381_mulMlResult => 72
    | .Bls12_381_finalVerify => 1
    | .DropList => 4
    | .Bls12_381_G1_multiScalarMul => 18
    | .Bls12_381_G2_multiScalarMul => 36
    | .IndexArray => 32
    | .LengthOfArray => 10
    | .ListToArray => cLin 7 1 s0
    | .InsertCoin => cLin 45 21 s0
    | .LookupCoin => 1
    | .ScaleValue => cLin 12 21 s1
    | .UnionValue => cAddSz 24 21 sz
    | .ValueContains => 1
    | .ValueData => cLin 2 22 s0
    | .UnValueData => cLin 1 11 s0

/-! ## Cost of the Next Step

Compute the cost incurred by the next `step` call.
Machine step costs are charged at `compute` entry; return transitions
are free except when a builtin becomes saturated.
-/

def computeStepCost : State → ExBudget
  | .compute _ _ (.Var _) | .compute _ _ (.Constant _) | .compute _ _ (.Lam _ _)
  | .compute _ _ (.Apply _ _) | .compute _ _ (.Force _) | .compute _ _ (.Delay _)
  | .compute _ _ (.Builtin _) | .compute _ _ (.Constr _ _)
  | .compute _ _ (.Case _ _) => stepCost
  | .compute _ _ .Error => .zero
  -- Builtin saturation on return
  | .ret (.funV (.VBuiltin b args ea) :: _) vx =>
    if ea.head == .argV && ea.isFinal then builtinCost b (vx :: args) else .zero
  | .ret (.applyArg vx :: _) (.VBuiltin b args ea) =>
    if ea.head == .argV && ea.isFinal then builtinCost b (vx :: args) else .zero
  | .ret (.force :: _) (.VBuiltin b args ea) =>
    if ea.head == .argQ && ea.isFinal then builtinCost b args else .zero
  | _ => .zero

/-! ## Running the Machine with Budget Enforcement -/

/-- Machine evaluation result. -/
inductive CekResult where
  | success : CekValue → CekResult
  | failure : CekResult
  | outOfBudget : CekResult
deriving Inhabited

instance : ToString CekResult where
  toString
    | .success v => s!"success({v})"
    | .failure => "failure"
    | .outOfBudget => "out-of-budget"

/-- Result of evaluation including the consumed budget. -/
structure EvalResult where
  result   : CekResult
  consumed : ExBudget
deriving Inhabited

/-- Default Cardano mainnet budget limits (PlutusV3). -/
def defaultCpuBudget : Int := 10000000000
def defaultMemBudget : Int := 14000000

/-- Evaluate a closed UPLC term with a budget limit.
Returns the result and the consumed budget.
Budget is enforced: if either CPU or memory goes negative, returns `outOfBudget`. -/
partial def eval (t : Term) (cpuLimit : Int := defaultCpuBudget)
    (memLimit : Int := defaultMemBudget) : EvalResult :=
  let initial : ExBudget := ⟨cpuLimit, memLimit⟩
  let afterStartup := initial - startupCost
  if afterStartup.isExhausted then
    ⟨.outOfBudget, startupCost⟩
  else
    go afterStartup initial (.compute [] .nil t)
where
  go (remaining initial : ExBudget) (s : State) : EvalResult :=
    match s with
    | .halt v => ⟨.success v, initial - remaining⟩
    | .error => ⟨.failure, initial - remaining⟩
    | s =>
      let cost := computeStepCost s
      let remaining' := remaining - cost
      if remaining'.isExhausted then
        ⟨.outOfBudget, initial - remaining'⟩
      else
        go remaining' initial (step s)

end Moist.CEK
