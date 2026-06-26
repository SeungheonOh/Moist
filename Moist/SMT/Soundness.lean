import Moist.SMT.UPLC
import Moist.SMT.Semantics
import Moist.Verified.BigStep

namespace Moist.SMT.UPLC.Soundness

open Moist.Plutus.Term
open Moist.Verified.BigStep
open Moist.CEK (ArgKind ExpectedArgs expectedArgs CekEnv CekValue)

namespace SmtSem
abbrev Val := Moist.SMT.Semantics.Val
abbrev SVal := Moist.SMT.Semantics.SVal
abbrev Model := Moist.SMT.Semantics.Model
abbrev eval := Moist.SMT.Semantics.eval
abbrev evalBoolIs := Moist.SMT.Semantics.evalBoolIs
end SmtSem

abbrev tyBytes : BuiltinType := .AtomicType .TypeByteString
abbrev tyBool : BuiltinType := .AtomicType .TypeBool
abbrev tyListInt : BuiltinType := .TypeOperator (.TypeList (.AtomicType .TypeInteger))

def app (f x : Term) : Term := .Apply f x
def app1 (b : BuiltinFun) (x : Term) : Term := app (.Builtin b) x
def app2 (b : BuiltinFun) (x y : Term) : Term := app (app (.Builtin b) x) y
def int (n : Int) : Term := .Constant (.Integer n, .AtomicType .TypeInteger)
def forceBuiltin (b : BuiltinFun) : Term := .Force (.Builtin b)

def ifThenElse (c t e : Term) : Term :=
  app (app (app (forceBuiltin .IfThenElse) c) t) e

def lazyIf (c t e : Term) : Term :=
  .Force (ifThenElse c (.Delay t) (.Delay e))

def emptyBytes : Term :=
  .Constant (.ByteString ByteArray.empty, tyBytes)

def sha2Refl : Term :=
  app2 .EqualsByteString (app1 .Sha2_256 emptyBytes) (app1 .Sha2_256 emptyBytes)

def recursiveSumTerm : Term :=
  let body :=
    let x := .Var 1
    let self := .Var 2
    let cond := app2 .LessThanInteger x (int 0)
    let xMinusOne := app2 .SubtractInteger x (int 1)
    let recCall := app (app self self) xMinusOne
    let step := app2 .AddInteger x recCall
    lazyIf cond (int 0) step
  let sumF := .Lam 0 (.Lam 0 body)
  app (app sumF sumF) (.Var 1)

def envInt (n : Int) : CekEnv :=
  .cons (.VCon (.Integer n)) .nil

def bigEvalIntEq (fuel : Nat) (ρ : CekEnv) (t : Term) (expected : Int) : Bool :=
  match bigEval fuel ρ t with
  | some (.VCon (.Integer n)) => n == expected
  | _ => false

def bigEvalBoolTrue (fuel : Nat) (ρ : CekEnv) (t : Term) : Bool :=
  match bigEval fuel ρ t with
  | some (.VCon (.Bool true)) => true
  | _ => false

def bigEvalFails (fuel : Nat) (ρ : CekEnv) (t : Term) : Bool :=
  match bigEval fuel ρ t with
  | none => true
  | some _ => false

def equalsIntegerAddExample : Term :=
  app2 .EqualsInteger (int 10) (app2 .AddInteger (int 5) (.Var 1))

def caseIntegerExample : Term :=
  .Case (.Var 1) [.Error, .Error, .Constant (.Bool true, tyBool)]

def caseIfConstrExample : Term :=
  let cond := app2 .EqualsInteger (.Var 1) (int 10)
  .Case (ifThenElse cond (.Constr 1 []) (.Constr 0 [])) [.Error, .Constant (.Bool true, tyBool)]

def caseEmptyConstListMissingNilExample : Term :=
  .Case (.Constant (.ConstList [], tyListInt)) [.Constant (.Bool true, tyBool)]

def mkConsRejectsRuntimeConstrExample : Term :=
  app (app (forceBuiltin .MkCons) (.Constr 0 [])) (.Constant (.ConstList [], tyListInt))

def builtinOpaqueForSoundness : BuiltinFun → Bool
  | .Sha2_256 | .Sha3_256 | .Blake2b_256 | .VerifyEd25519Signature
  | .SerializeData
  | .VerifyEcdsaSecp256k1Signature | .VerifySchnorrSecp256k1Signature
  | .Bls12_381_G1_add | .Bls12_381_G1_neg | .Bls12_381_G1_scalarMul
  | .Bls12_381_G1_equal | .Bls12_381_G1_hashToGroup
  | .Bls12_381_G1_compress | .Bls12_381_G1_uncompress
  | .Bls12_381_G2_add | .Bls12_381_G2_neg | .Bls12_381_G2_scalarMul
  | .Bls12_381_G2_equal | .Bls12_381_G2_hashToGroup
  | .Bls12_381_G2_compress | .Bls12_381_G2_uncompress
  | .Bls12_381_millerLoop | .Bls12_381_mulMlResult | .Bls12_381_finalVerify
  | .Keccak_256 | .Blake2b_224
  | .IntegerToByteString | .ByteStringToInteger
  | .AndByteString | .OrByteString | .XorByteString | .ComplementByteString
  | .ReadBit | .WriteBits | .ReplicateByte | .ShiftByteString
  | .RotateByteString | .CountSetBits | .FindFirstSetBit
  | .Ripemd_160 | .ExpModInteger
  | .InsertCoin | .LookupCoin | .ScaleValue | .UnionValue | .ValueContains
  | .ValueData | .UnValueData
  | .Bls12_381_G1_multiScalarMul | .Bls12_381_G2_multiScalarMul => true
  | _ => false

def builtinAllowedForSoundness (b : BuiltinFun) : Bool :=
  !builtinOpaqueForSoundness b

mutual
  def termUsesOpaqueBuiltinForSoundness : Term → Bool
    | .Var _ => false
    | .Delay t => termUsesOpaqueBuiltinForSoundness t
    | .Lam _ body => termUsesOpaqueBuiltinForSoundness body
    | .Apply f a =>
        termUsesOpaqueBuiltinForSoundness f || termUsesOpaqueBuiltinForSoundness a
    | .Constant _ => false
    | .Force t => termUsesOpaqueBuiltinForSoundness t
    | .Error => false
    | .Builtin b => builtinOpaqueForSoundness b
    | .Constr _ fields => termsUseOpaqueBuiltinForSoundness fields
    | .Case scrut alts =>
        termUsesOpaqueBuiltinForSoundness scrut ||
          termsUseOpaqueBuiltinForSoundness alts

  def termsUseOpaqueBuiltinForSoundness : List Term → Bool
    | [] => false
    | t :: ts =>
        termUsesOpaqueBuiltinForSoundness t ||
          termsUseOpaqueBuiltinForSoundness ts
end

def termNoOpaqueBuiltinsForSoundness (t : Term) : Prop :=
  termUsesOpaqueBuiltinForSoundness t = false

mutual
  def symValNoOpaqueForSoundness : SymVal → Bool
    | .const _ => true
    | .dyn _ => true
    | .pair a b =>
        symValNoOpaqueForSoundness a && symValNoOpaqueForSoundness b
    | .constr _ fields => symValsNoOpaqueForSoundness fields
    | .lam body ρ =>
        termUsesOpaqueBuiltinForSoundness body == false &&
          symEnvNoOpaqueForSoundness ρ
    | .delay body ρ =>
        termUsesOpaqueBuiltinForSoundness body == false &&
          symEnvNoOpaqueForSoundness ρ
    | .builtin b args _ =>
        builtinAllowedForSoundness b && symValsNoOpaqueForSoundness args

  def symValsNoOpaqueForSoundness : List SymVal → Bool
    | [] => true
    | v :: vs =>
        symValNoOpaqueForSoundness v && symValsNoOpaqueForSoundness vs

  def symEnvNoOpaqueForSoundness : List SymVal → Bool
    | [] => true
    | v :: ρ =>
        symValNoOpaqueForSoundness v && symEnvNoOpaqueForSoundness ρ
end

theorem symEnvNoOpaque_lookup {ρ : List SymVal} {k : Nat} {v : SymVal}
    (hρ : symEnvNoOpaqueForSoundness ρ = true)
    (hlookup : lookupEnv ρ k = some v) :
    symValNoOpaqueForSoundness v = true := by
  induction ρ generalizing k with
  | nil =>
      simp [lookupEnv] at hlookup
  | cons x xs ih =>
      simp [symEnvNoOpaqueForSoundness] at hρ
      cases k with
      | zero =>
          simp [lookupEnv] at hlookup
      | succ k =>
          cases k with
          | zero =>
              simp [lookupEnv] at hlookup
              subst v
              exact hρ.1
          | succ k =>
              exact ih hρ.2 (by simpa [lookupEnv] using hlookup)

theorem symEnvNoOpaque_extend {ρ : List SymVal} {v : SymVal}
    (hρ : symEnvNoOpaqueForSoundness ρ = true)
    (hv : symValNoOpaqueForSoundness v = true) :
    symEnvNoOpaqueForSoundness (extendEnv ρ v) = true := by
  simp [extendEnv, symEnvNoOpaqueForSoundness, hv, hρ]

theorem symValNoOpaqueList_cons {v : SymVal} {vs : List SymVal}
    (hv : symValNoOpaqueForSoundness v = true)
    (hvs : symValsNoOpaqueForSoundness vs = true) :
    symValsNoOpaqueForSoundness (v :: vs) = true := by
  simp [symValsNoOpaqueForSoundness, hv, hvs]

theorem symValsNoOpaque_singleton {v : SymVal}
    (h : symValsNoOpaqueForSoundness [v] = true) :
    symValNoOpaqueForSoundness v = true := by
  simpa [symValsNoOpaqueForSoundness] using h

theorem symValsNoOpaque_pair {a b : SymVal}
    (h : symValsNoOpaqueForSoundness [b, a] = true) :
    symValNoOpaqueForSoundness b = true ∧
      symValNoOpaqueForSoundness a = true := by
  simpa [symValsNoOpaqueForSoundness] using h

theorem symValsNoOpaque_triple {a b c : SymVal}
    (h : symValsNoOpaqueForSoundness [c, b, a] = true) :
    symValNoOpaqueForSoundness c = true ∧
      symValNoOpaqueForSoundness b = true ∧
      symValNoOpaqueForSoundness a = true := by
  simpa [symValsNoOpaqueForSoundness] using h

theorem symValsNoOpaque_six {a b c d e f : SymVal}
    (h : symValsNoOpaqueForSoundness [f, e, d, c, b, a] = true) :
    symValNoOpaqueForSoundness f = true ∧
      symValNoOpaqueForSoundness e = true ∧
      symValNoOpaqueForSoundness d = true ∧
      symValNoOpaqueForSoundness c = true ∧
      symValNoOpaqueForSoundness b = true ∧
      symValNoOpaqueForSoundness a = true := by
  simpa [symValsNoOpaqueForSoundness] using h

theorem asPair_fst_noOpaque {p : SymVal}
    (h : symValNoOpaqueForSoundness p = true) :
    symValNoOpaqueForSoundness (asPair p).val.1 = true := by
  cases p <;> simp [asPair, Proj.pure, Proj.fail, symValNoOpaqueForSoundness] at h ⊢
  exact h.1

theorem asPair_snd_noOpaque {p : SymVal}
    (h : symValNoOpaqueForSoundness p = true) :
    symValNoOpaqueForSoundness (asPair p).val.2 = true := by
  cases p <;> simp [asPair, Proj.pure, Proj.fail, symValNoOpaqueForSoundness] at h ⊢
  exact h.2

theorem termNoOpaque_apply {f a : Term}
    (h : termNoOpaqueBuiltinsForSoundness (.Apply f a)) :
    termNoOpaqueBuiltinsForSoundness f ∧ termNoOpaqueBuiltinsForSoundness a := by
  simpa [termNoOpaqueBuiltinsForSoundness, termUsesOpaqueBuiltinForSoundness] using h

theorem termNoOpaque_force {t : Term}
    (h : termNoOpaqueBuiltinsForSoundness (.Force t)) :
    termNoOpaqueBuiltinsForSoundness t := by
  simpa [termNoOpaqueBuiltinsForSoundness, termUsesOpaqueBuiltinForSoundness] using h

theorem termNoOpaque_constr_fields {tag : Nat} {fields : List Term}
    (h : termNoOpaqueBuiltinsForSoundness (.Constr tag fields)) :
    termsUseOpaqueBuiltinForSoundness fields = false := by
  simpa [termNoOpaqueBuiltinsForSoundness, termUsesOpaqueBuiltinForSoundness] using h

theorem termNoOpaque_case {scrut : Term} {alts : List Term}
    (h : termNoOpaqueBuiltinsForSoundness (.Case scrut alts)) :
    termNoOpaqueBuiltinsForSoundness scrut ∧
      termsUseOpaqueBuiltinForSoundness alts = false := by
  simpa [termNoOpaqueBuiltinsForSoundness, termUsesOpaqueBuiltinForSoundness] using h

theorem termsNoOpaque_cons {t : Term} {ts : List Term}
    (h : termsUseOpaqueBuiltinForSoundness (t :: ts) = false) :
    termNoOpaqueBuiltinsForSoundness t ∧
      termsUseOpaqueBuiltinForSoundness ts = false := by
  simpa [termNoOpaqueBuiltinsForSoundness, termsUseOpaqueBuiltinForSoundness] using h

private theorem enumerate_go_mem_get?_aux {α} :
    ∀ (xs : List α) (start i : Nat) (x : α),
      (i, x) ∈ Moist.SMT.UPLC.enumerate.go start xs →
      ∃ k, xs[k]? = some x ∧ i = start + k := by
  intro xs
  induction xs with
  | nil =>
      intro start i x h
      simp [Moist.SMT.UPLC.enumerate.go] at h
  | cons y ys ih =>
      intro start i x h
      simp [Moist.SMT.UPLC.enumerate.go] at h
      rcases h with h | h
      · rcases h with ⟨rfl, rfl⟩
        exact ⟨0, by simp, by omega⟩
      · obtain ⟨k, hk, hi⟩ := ih (start + 1) i x h
        exact ⟨k + 1, by simp [hk], by omega⟩

theorem enumerate_mem_get? {α} {xs : List α} {i : Nat} {x : α}
    (h : (i, x) ∈ enumerate xs) : xs[i]? = some x := by
  unfold enumerate at h
  obtain ⟨k, hk, hi⟩ := enumerate_go_mem_get?_aux xs 0 i x h
  subst i
  simpa using hk

private theorem enumerate_go_get?_mem_aux {α} :
    ∀ (xs : List α) (start i : Nat) (x : α),
      xs[i]? = some x →
      (start + i, x) ∈ Moist.SMT.UPLC.enumerate.go start xs := by
  intro xs
  induction xs with
  | nil =>
      intro start i x h
      simp at h
  | cons y ys ih =>
      intro start i x h
      cases i with
      | zero =>
          simp at h
          subst x
          simp [Moist.SMT.UPLC.enumerate.go]
      | succ i =>
          simp at h
          have hmem := ih (start + 1) i x h
          simp [Moist.SMT.UPLC.enumerate.go]
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmem

theorem enumerate_get?_mem {α} {xs : List α} {i : Nat} {x : α}
    (h : xs[i]? = some x) : (i, x) ∈ enumerate xs := by
  unfold enumerate
  simpa using enumerate_go_get?_mem_aux xs 0 i x h

theorem termsNoOpaque_get? {alts : List Term} {i : Nat} {alt : Term}
    (hno : termsUseOpaqueBuiltinForSoundness alts = false)
    (hget : alts[i]? = some alt) :
    termNoOpaqueBuiltinsForSoundness alt := by
  induction alts generalizing i with
  | nil =>
      simp at hget
  | cons t ts ih =>
      have hsplit := termsNoOpaque_cons hno
      cases i with
      | zero =>
          simp at hget
          subst alt
          exact hsplit.1
      | succ i =>
          exact ih hsplit.2 (by simpa using hget)

def modelInt (name : String) (n : Int) : SmtSem.Model :=
  Moist.SMT.Semantics.Model.bind Moist.SMT.Semantics.Model.empty name (.int n)

def emptyModel : SmtSem.Model := Moist.SMT.Semantics.Model.empty

mutual
  def semValToConst? : SmtSem.Val → Option Const
    | .int i => some (.Integer i)
    | .bytes bs => some (.ByteString bs)
    | .string s => some (.String s)
    | .bool b => some (.Bool b)
    | .unit => some .Unit
    | .list xs => do
        let cs ← semValListToConstList? xs
        some (.ConstList cs)
    | .dataList xs => some (.ConstDataList xs)
    | .pairDataList xs => some (.ConstPairDataList xs)
    | .pair a b => do
        let ca ← semValToConst? a
        let cb ← semValToConst? b
        some (.Pair (ca, cb))
    | .pairData a b => some (.PairData (a, b))
    | .data d => some (.Data d)
    | .array xs => do
        let cs ← semValListToConstList? xs
        some (.ConstArray cs)
    | .g1 _ => some .Bls12_381_G1_element
    | .g2 _ => some .Bls12_381_G2_element
    | .ml _ => some .Bls12_381_MlResult
    | .constr _ _ => none

  def semValListToConstList? : List SmtSem.Val → Option (List Const)
    | [] => some []
    | v :: vs => do
        let c ← semValToConst? v
        let cs ← semValListToConstList? vs
        some (c :: cs)

  def semValToCek? : SmtSem.Val → Option CekValue
    | .constr tag fields => do
        if tag < 0 then none
        else
          let vs ← semValListToCekList? fields
          some (.VConstr tag.toNat vs)
    | v => do
        let c ← semValToConst? v
        some (.VCon c)

  def semValListToCekList? : List SmtSem.Val → Option (List CekValue)
    | [] => some []
    | v :: vs => do
        let cv ← semValToCek? v
        let cvs ← semValListToCekList? vs
        some (cv :: cvs)
end

mutual
  def symValToCek? (m : SmtSem.Model) : SymVal → Option CekValue
    | .const c => symConstToCek? m c
    | .dyn e => do
        match SmtSem.eval m e with
        | some (.val v) => semValToCek? v
        | _ => none
    | .pair a b => do
        let ca ← symValToCek? m a
        let cb ← symValToCek? m b
        match ca, cb with
        | .VCon ca, .VCon cb => some (.VCon (.Pair (ca, cb)))
        | _, _ => none
    | .constr tag fields => do
        match SmtSem.eval m tag with
        | some (.int i) =>
            if i < 0 then none
            else
              let vs ← symValListToCekList? m fields
              some (.VConstr i.toNat vs)
        | _ => none
    | .lam body ρ => do
        let env ← symEnvToCek? m ρ
        some (.VLam body env)
    | .delay body ρ => do
        let env ← symEnvToCek? m ρ
        some (.VDelay body env)
    | .builtin b args ea => do
        let vs ← symValListToCekList? m args
        some (.VBuiltin b vs ea)

  def symConstToCek? (m : SmtSem.Model) : SymConst → Option CekValue
    | .integer e =>
        match SmtSem.eval m e with
        | some (.int i) => some (.VCon (.Integer i))
        | _ => none
    | .bytes e =>
        match SmtSem.eval m e with
        | some (.bytes bs) => some (.VCon (.ByteString bs))
        | _ => none
    | .string e =>
        match SmtSem.eval m e with
        | some (.string s) => some (.VCon (.String s))
        | _ => none
    | .bool e =>
        match SmtSem.eval m e with
        | some (.bool b) => some (.VCon (.Bool b))
        | _ => none
    | .unit => some (.VCon .Unit)
    | .constList e =>
        match SmtSem.eval m e with
        | some (.valList xs) => do
            let cs ← semValListToConstList? xs
            some (.VCon (.ConstList cs))
        | _ => none
    | .dataList e =>
        match SmtSem.eval m e with
        | some (.dataList xs) => some (.VCon (.ConstDataList xs))
        | _ => none
    | .pairDataList e =>
        match SmtSem.eval m e with
        | some (.dataPairList xs) => some (.VCon (.ConstPairDataList xs))
        | _ => none
    | .pairData a b =>
        match SmtSem.eval m a, SmtSem.eval m b with
        | some (.data a), some (.data b) => some (.VCon (.PairData (a, b)))
        | _, _ => none
    | .data e =>
        match SmtSem.eval m e with
        | some (.data d) => some (.VCon (.Data d))
        | _ => none
    | .array e =>
        match SmtSem.eval m e with
        | some (.valList xs) => do
            let cs ← semValListToConstList? xs
            some (.VCon (.ConstArray cs))
        | _ => none
    | .g1 e =>
        match SmtSem.eval m e with
        | some (.g1 _) => some (.VCon .Bls12_381_G1_element)
        | _ => none
    | .g2 e =>
        match SmtSem.eval m e with
        | some (.g2 _) => some (.VCon .Bls12_381_G2_element)
        | _ => none
    | .ml e =>
        match SmtSem.eval m e with
        | some (.ml _) => some (.VCon .Bls12_381_MlResult)
        | _ => none

  def symValListToCekList? (m : SmtSem.Model) : List SymVal → Option (List CekValue)
    | [] => some []
    | v :: vs => do
        let cv ← symValToCek? m v
        let cvs ← symValListToCekList? m vs
        some (cv :: cvs)

  def symEnvToCek? (m : SmtSem.Model) : List SymVal → Option CekEnv
    | [] => some .nil
    | v :: vs => do
        let cv ← symValToCek? m v
        let env ← symEnvToCek? m vs
        some (.cons cv env)
end

def pcHolds (m : SmtSem.Model) (pc : SExpr) : Bool :=
  SmtSem.evalBoolIs m pc true

def outcomeOkSym? (m : SmtSem.Model) : Outcome → Option (SymVal × CekValue)
  | .ok pc v =>
      if pcHolds m pc then
        match symValToCek? m v with
        | some cv => some (v, cv)
        | none => none
      else none
  | _ => none

def outcomeErrorActive (m : SmtSem.Model) : Outcome → Bool
  | .error pc => pcHolds m pc
  | _ => false

def anyOkOutcome? (m : SmtSem.Model) : List Outcome → Option CekValue
  | [] => none
  | o :: os =>
      match outcomeOkSym? m o with
      | some (_, cv) => some cv
      | none => anyOkOutcome? m os

def anyErrorOutcome (m : SmtSem.Model) : List Outcome → Bool
  | [] => false
  | o :: os => outcomeErrorActive m o || anyErrorOutcome m os

def anyOkBoolTrue (m : SmtSem.Model) (outs : List Outcome) : Bool :=
  match anyOkOutcome? m outs with
  | some (.VCon (.Bool true)) => true
  | _ => false

theorem outcomeOkSym_ok {m : SmtSem.Model} {pc : SExpr} {v sv : SymVal}
    {cv : CekValue}
    (h : outcomeOkSym? m (Outcome.ok pc v) = some (sv, cv)) :
    pcHolds m pc = true ∧ sv = v ∧ symValToCek? m v = some cv := by
  unfold outcomeOkSym? at h
  cases hpc : pcHolds m pc <;> simp [hpc] at h
  cases hcv : symValToCek? m v <;> simp [hcv] at h
  rename_i cv'
  rcases h with ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, rfl⟩

theorem outcomeErrorActive_error {m : SmtSem.Model} {pc : SExpr}
    (h : outcomeErrorActive m (Outcome.error pc) = true) :
    pcHolds m pc = true := by
  simpa [outcomeErrorActive] using h

theorem outcomeOkSym_guard {m : SmtSem.Model} {g : SExpr} {inner : Outcome}
    {sv : SymVal} {cv : CekValue}
    (h : outcomeOkSym? m (Outcome.guard g inner) = some (sv, cv)) :
    pcHolds m g = true ∧ outcomeOkSym? m inner = some (sv, cv) := by
  cases inner with
  | ok pc v =>
      have hok := outcomeOkSym_ok h
      have hp := (Moist.SMT.Semantics.evalBoolIs_and_true m g pc).mp hok.1
      have hg : pcHolds m g = true := by simpa [pcHolds] using hp.1
      have hpc : pcHolds m pc = true := by simpa [pcHolds] using hp.2
      exact ⟨hg, by simp [outcomeOkSym?, hpc, hok.2.1, hok.2.2]⟩
  | error pc =>
      simp [Outcome.guard, outcomeOkSym?] at h
  | timeout pc =>
      simp [Outcome.guard, outcomeOkSym?] at h

theorem outcomeErrorActive_guard {m : SmtSem.Model} {g : SExpr} {inner : Outcome}
    (h : outcomeErrorActive m (Outcome.guard g inner) = true) :
    pcHolds m g = true ∧ outcomeErrorActive m inner = true := by
  cases inner with
  | ok pc v =>
      simp [Outcome.guard, outcomeErrorActive] at h
  | error pc =>
      have hp := outcomeErrorActive_error h
      have hand := (Moist.SMT.Semantics.evalBoolIs_and_true m g pc).mp hp
      exact ⟨hand.1, by simpa [outcomeErrorActive] using hand.2⟩
  | timeout pc =>
      simp [Outcome.guard, outcomeErrorActive] at h

theorem ok_mem_singleton {pc : SExpr} {v sv : SymVal} :
    Outcome.ok pc sv ∈ ok v → pc = SExpr.trueE ∧ sv = v := by
  intro h
  simpa [ok] using h

theorem err_mem_singleton {pc : SExpr} :
    Outcome.error pc ∈ err → pc = SExpr.trueE := by
  intro h
  simpa [err] using h

theorem symEnv_lookup_some_exists {m : SmtSem.Model} :
    ∀ {ρ : List SymVal} {env : CekEnv} {k : Nat} {v : SymVal},
      symEnvToCek? m ρ = some env →
      lookupEnv ρ k = some v →
      ∃ cv, symValToCek? m v = some cv ∧ env.lookup k = some cv
  | [], env, k, v, henv, hlookup => by
      simp [lookupEnv] at hlookup
  | x :: xs, env, k, v, henv, hlookup => by
      cases hx : symValToCek? m x <;> simp [symEnvToCek?, hx] at henv
      rename_i cvx
      cases hxs : symEnvToCek? m xs <;> simp [hxs] at henv
      rename_i envTail
      subst env
      cases k with
      | zero =>
          simp [lookupEnv] at hlookup
      | succ k =>
          cases k with
          | zero =>
              simp [lookupEnv] at hlookup
              subst v
              exact ⟨cvx, hx, by simp [Moist.CEK.CekEnv.lookup]⟩
          | succ k =>
              have ih := symEnv_lookup_some_exists (m := m)
                (ρ := xs) (env := envTail) (k := k + 1) (v := v) hxs
                (by simpa [lookupEnv] using hlookup)
              rcases ih with ⟨cv, hv, hlookupCek⟩
              exact ⟨cv, hv, by simpa [Moist.CEK.CekEnv.lookup] using hlookupCek⟩

theorem symEnv_lookup_none {m : SmtSem.Model} :
    ∀ {ρ : List SymVal} {env : CekEnv} {k : Nat},
      symEnvToCek? m ρ = some env →
      lookupEnv ρ k = none →
      env.lookup k = none
  | [], env, k, henv, hlookup => by
      simp [symEnvToCek?] at henv
      subst env
      cases k <;> rfl
  | x :: xs, env, k, henv, hlookup => by
      cases hx : symValToCek? m x <;> simp [symEnvToCek?, hx] at henv
      rename_i cvx
      cases hxs : symEnvToCek? m xs <;> simp [hxs] at henv
      rename_i envTail
      subst env
      cases k with
      | zero =>
          rfl
      | succ k =>
          cases k with
          | zero =>
              simp [lookupEnv] at hlookup
          | succ k =>
              have ih := symEnv_lookup_none (m := m)
                (ρ := xs) (env := envTail) (k := k + 1) hxs
                (by simpa [lookupEnv] using hlookup)
              simpa [Moist.CEK.CekEnv.lookup] using ih

theorem evalBoolIs_foldl_or_true {m : SmtSem.Model} :
    ∀ {xs : List SExpr} {acc : SExpr},
      SmtSem.evalBoolIs m (xs.foldl SExpr.or acc) true = true →
      SmtSem.evalBoolIs m acc true = true ∨
        ∃ x, x ∈ xs ∧ SmtSem.evalBoolIs m x true = true
  | [], acc, h => Or.inl h
  | x :: xs, acc, h => by
      have ih := evalBoolIs_foldl_or_true (m := m) (xs := xs)
        (acc := SExpr.or acc x) h
      rcases ih with hhead | htail
      · have hor := Moist.SMT.Semantics.evalBoolIs_or_true m acc x hhead
        rcases hor with hacc | hx
        · exact Or.inl hacc
        · exact Or.inr ⟨x, by simp, hx⟩
      · rcases htail with ⟨y, hy, htrue⟩
        exact Or.inr ⟨y, by simp [hy], htrue⟩

theorem evalBoolIs_any_true {m : SmtSem.Model} {xs : List SExpr}
    (h : SmtSem.evalBoolIs m (SExpr.any xs) true = true) :
    ∃ x, x ∈ xs ∧ SmtSem.evalBoolIs m x true = true := by
  cases xs with
  | nil =>
      simp [SExpr.any, Moist.SMT.Expr.any] at h
  | cons x xs =>
      cases xs with
      | nil =>
          exact ⟨x, by simp, by simpa [SExpr.any, Moist.SMT.Expr.any] using h⟩
      | cons y ys =>
          have hfold := evalBoolIs_foldl_or_true (m := m)
            (xs := y :: ys) (acc := x)
            (by simpa [SExpr.any, Moist.SMT.Expr.any] using h)
          rcases hfold with hx | htail
          · exact ⟨x, by simp, hx⟩
          · rcases htail with ⟨z, hz, hztrue⟩
            exact ⟨z, by simp [hz], hztrue⟩

def unsupportedCaseGuard (e : SExpr) : SExpr :=
  SExpr.any [
    SExpr.isCtor "VBytes" e, SExpr.isCtor "VString" e, SExpr.isCtor "VData" e,
    SExpr.isCtor "VPairDataList" e, SExpr.isCtor "VArray" e, SExpr.isCtor "VG1" e,
    SExpr.isCtor "VG2" e, SExpr.isCtor "VMlResult" e]

theorem unsupportedCaseGuard_true_cases {m : SmtSem.Model} {e : SExpr}
    (h : pcHolds m (unsupportedCaseGuard e) = true) :
    (∃ bs, SmtSem.eval m e = some (.val (.bytes bs))) ∨
    (∃ s, SmtSem.eval m e = some (.val (.string s))) ∨
    (∃ d, SmtSem.eval m e = some (.val (.data d))) ∨
    (∃ xs, SmtSem.eval m e = some (.val (.pairDataList xs))) ∨
    (∃ xs, SmtSem.eval m e = some (.val (.array xs))) ∨
    (∃ g, SmtSem.eval m e = some (.val (.g1 g))) ∨
    (∃ g, SmtSem.eval m e = some (.val (.g2 g))) ∨
    (∃ r, SmtSem.eval m e = some (.val (.ml r))) := by
  obtain ⟨x, hx, hxtrue⟩ := evalBoolIs_any_true (m := m)
    (by simpa [pcHolds, unsupportedCaseGuard] using h)
  simp [unsupportedCaseGuard] at hx
  rcases hx with hbytes | hstring | hdata | hpairDataList | harray | hg1 | hg2 | hml
  · rw [hbytes] at hxtrue
    exact Or.inl (Moist.SMT.Semantics.evalBoolIs_isVBytes_true hxtrue)
  · rw [hstring] at hxtrue
    exact Or.inr (Or.inl (Moist.SMT.Semantics.evalBoolIs_isVString_true hxtrue))
  · rw [hdata] at hxtrue
    exact Or.inr (Or.inr (Or.inl (Moist.SMT.Semantics.evalBoolIs_isVData_true hxtrue)))
  · rw [hpairDataList] at hxtrue
    exact Or.inr (Or.inr (Or.inr (Or.inl
      (Moist.SMT.Semantics.evalBoolIs_isVPairDataList_true hxtrue))))
  · rw [harray] at hxtrue
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (Moist.SMT.Semantics.evalBoolIs_isVArray_true hxtrue)))))
  · rw [hg1] at hxtrue
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (Moist.SMT.Semantics.evalBoolIs_isVG1_true hxtrue))))))
  · rw [hg2] at hxtrue
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (Moist.SMT.Semantics.evalBoolIs_isVG2_true hxtrue)))))))
  · rw [hml] at hxtrue
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Moist.SMT.Semantics.evalBoolIs_isVMlResult_true hxtrue)))))))

theorem unsupportedCaseGuard_false_of_supported {m : SmtSem.Model} {e : SExpr}
    {semv : SmtSem.Val}
    (h : pcHolds m (unsupportedCaseGuard e) = true)
    (he : SmtSem.eval m e = some (.val semv))
    (hsupported :
      (∀ bs, semv ≠ .bytes bs) ∧
      (∀ s, semv ≠ .string s) ∧
      (∀ d, semv ≠ .data d) ∧
      (∀ xs, semv ≠ .pairDataList xs) ∧
      (∀ xs, semv ≠ .array xs) ∧
      (∀ g, semv ≠ .g1 g) ∧
      (∀ g, semv ≠ .g2 g) ∧
      (∀ r, semv ≠ .ml r)) :
    False := by
  have hcases := unsupportedCaseGuard_true_cases (m := m) (e := e) h
  rcases hcases with
    ⟨bs, hbad⟩ | ⟨s, hbad⟩ | ⟨d, hbad⟩ | ⟨xs, hbad⟩ |
    ⟨xs, hbad⟩ | ⟨g, hbad⟩ | ⟨g, hbad⟩ | ⟨r, hbad⟩
  · rw [he] at hbad
    cases hbad
    exact hsupported.1 bs rfl
  · rw [he] at hbad
    cases hbad
    exact hsupported.2.1 s rfl
  · rw [he] at hbad
    cases hbad
    exact hsupported.2.2.1 d rfl
  · rw [he] at hbad
    cases hbad
    exact hsupported.2.2.2.1 xs rfl
  · rw [he] at hbad
    cases hbad
    exact hsupported.2.2.2.2.1 xs rfl
  · rw [he] at hbad
    cases hbad
    exact hsupported.2.2.2.2.2.1 g rfl
  · rw [he] at hbad
    cases hbad
    exact hsupported.2.2.2.2.2.2.1 g rfl
  · rw [he] at hbad
    cases hbad
    exact hsupported.2.2.2.2.2.2.2 r rfl

theorem evalBoolIs_true_false_contra {m : SmtSem.Model} {e : SExpr}
    (ht : SmtSem.evalBoolIs m e true = true)
    (hf : SmtSem.evalBoolIs m e false = true) : False := by
  unfold SmtSem.evalBoolIs Moist.SMT.Semantics.evalBoolIs at ht hf
  cases h : Moist.SMT.Semantics.evalBool? m e with
  | none =>
      simp [h] at ht
  | some b =>
      cases b <;> simp [h] at ht hf

theorem evalBoolIs_false_eq {m : SmtSem.Model} {e : SExpr} :
    SmtSem.evalBoolIs m e false = true ↔ SmtSem.eval m e = some (.bool false) := by
  unfold SmtSem.evalBoolIs Moist.SMT.Semantics.evalBoolIs
    Moist.SMT.Semantics.evalBool?
  cases he : SmtSem.eval m e with
  | none =>
      simp [he]
  | some v =>
      cases v with
      | bool b =>
          cases b <;> simp [he]
      | int i => simp [he]
      | string s => simp [he]
      | bytes bs => simp [he]
      | data d => simp [he]
      | dataList xs => simp [he]
      | dataPairList xs => simp [he]
      | val v => simp [he]
      | valList xs => simp [he]
      | g1 g => simp [he]
      | g2 g => simp [he]
      | ml r => simp [he]

theorem pcHolds_not_contra {m : SmtSem.Model} {e : SExpr}
    (ht : pcHolds m e = true)
    (hn : pcHolds m (SExpr.not e) = true) : False := by
  have hf : SmtSem.evalBoolIs m e false = true :=
    (Moist.SMT.Semantics.evalBoolIs_not_true m e).mp
      (by simpa [pcHolds] using hn)
  exact evalBoolIs_true_false_contra
    (by simpa [pcHolds] using ht) hf

theorem pcHolds_not_or_contra_left {m : SmtSem.Model} {a b : SExpr}
    (ha : pcHolds m a = true)
    (hn : pcHolds m (SExpr.not (SExpr.or a b)) = true) : False := by
  have hf : SmtSem.evalBoolIs m (SExpr.or a b) false = true :=
    (Moist.SMT.Semantics.evalBoolIs_not_true m (SExpr.or a b)).mp
      (by simpa [pcHolds] using hn)
  have horFalse := (evalBoolIs_false_eq (m := m) (e := SExpr.or a b)).mp hf
  have haEval :=
    (Moist.SMT.Semantics.evalBoolIs_true_eq m a).mp
      (by simpa [pcHolds] using ha)
  cases hbEval : SmtSem.eval m b with
  | none =>
      simp [SExpr.or, Moist.SMT.Expr.or, Moist.SMT.Semantics.eval, haEval,
        hbEval] at horFalse
  | some svb =>
      cases svb <;>
        simp [SExpr.or, Moist.SMT.Expr.or, Moist.SMT.Semantics.eval, haEval,
          hbEval] at horFalse

theorem pcHolds_not_or_contra_right {m : SmtSem.Model} {a b : SExpr}
    (hb : pcHolds m b = true)
    (hn : pcHolds m (SExpr.not (SExpr.or a b)) = true) : False := by
  have hf : SmtSem.evalBoolIs m (SExpr.or a b) false = true :=
    (Moist.SMT.Semantics.evalBoolIs_not_true m (SExpr.or a b)).mp
      (by simpa [pcHolds] using hn)
  have horFalse := (evalBoolIs_false_eq (m := m) (e := SExpr.or a b)).mp hf
  have hbEval :=
    (Moist.SMT.Semantics.evalBoolIs_true_eq m b).mp
      (by simpa [pcHolds] using hb)
  cases haEval : SmtSem.eval m a with
  | none =>
      simp [SExpr.or, Moist.SMT.Expr.or, Moist.SMT.Semantics.eval, haEval,
        hbEval] at horFalse
  | some sva =>
      cases sva <;>
        simp [SExpr.or, Moist.SMT.Expr.or, Moist.SMT.Semantics.eval, haEval,
          hbEval] at horFalse

theorem evalBoolIs_has_bool_eval {m : SmtSem.Model} {e : SExpr} {b : Bool}
    (h : SmtSem.evalBoolIs m e b = true) :
    ∃ b', SmtSem.eval m e = some (.bool b') := by
  unfold SmtSem.evalBoolIs Moist.SMT.Semantics.evalBoolIs
    Moist.SMT.Semantics.evalBool? at h
  cases he : Moist.SMT.Semantics.eval m e with
  | none =>
      simp [he] at h
  | some sv =>
      cases sv <;> simp [he] at h
      case bool bv =>
        exact ⟨bv, by simpa [SmtSem.eval] using he⟩

theorem evalBoolExists_all2 {m : SmtSem.Model} {a b : SExpr} {ba bb : Bool}
    (ha : SmtSem.eval m a = some (.bool ba))
    (hb : SmtSem.eval m b = some (.bool bb)) :
    ∃ bc, SmtSem.eval m (SExpr.all [a, b]) = some (.bool bc) := by
  refine ⟨ba && bb, ?_⟩
  change Moist.SMT.Semantics.eval m (.app "and" [a, b]) = some (.bool (ba && bb))
  rw [Moist.SMT.Semantics.eval.eq_def]
  simp [ha, hb]

theorem eval_not_of_bool {m : SmtSem.Model} {e : SExpr} {b : Bool}
    (h : SmtSem.eval m e = some (.bool b)) :
    SmtSem.eval m (SExpr.not e) = some (.bool (!b)) := by
  cases e <;> simp [SmtSem.eval, SExpr.not, Moist.SMT.Expr.not,
    Moist.SMT.Semantics.eval] at h ⊢
  case bool b0 =>
    subst b
    cases b0 <;> simp [SExpr.not, Moist.SMT.Expr.not,
      Moist.SMT.Semantics.eval]
  all_goals simp [h]

theorem pcHolds_eq_int {m : SmtSem.Model} {a b : SExpr} {x y : Int}
    (ha : SmtSem.eval m a = some (.int x))
    (hb : SmtSem.eval m b = some (.int y))
    (hpc : pcHolds m (SExpr.eq a b) = true) :
    x = y := by
  have heqEval := Moist.SMT.Semantics.eval_eq_int_of (m := m) (a := a) (b := b)
    (x := x) (y := y) ha hb
  change SmtSem.eval m (Expr.eq a b) = some (.bool (x == y)) at heqEval
  have hbool : SmtSem.eval m (SExpr.eq a b) = some (.bool true) :=
    (Moist.SMT.Semantics.evalBoolIs_true_eq m (SExpr.eq a b)).mp hpc
  change SmtSem.eval m (Expr.eq a b) = some (.bool true) at hbool
  rw [heqEval] at hbool
  simp at hbool
  exact hbool

theorem pcHolds_ne_int_zero {m : SmtSem.Model} {e : SExpr} {x : Int}
    (he : SmtSem.eval m e = some (.int x))
    (hpc : pcHolds m (SExpr.ne e (.int 0)) = true) :
    (x == 0) = false := by
  have hfalse :
      SmtSem.evalBoolIs m (SExpr.eq e (.int 0)) false = true :=
    (Moist.SMT.Semantics.evalBoolIs_not_true m (SExpr.eq e (.int 0))).mp hpc
  have hbool : SmtSem.eval m (SExpr.eq e (.int 0)) = some (.bool false) :=
    (evalBoolIs_false_eq (m := m) (e := SExpr.eq e (.int 0))).mp hfalse
  have heqEval := Moist.SMT.Semantics.eval_eq_int_of (m := m)
    (a := e) (b := .int 0) (x := x) (y := 0) he
    (by simp [Moist.SMT.Semantics.eval])
  change SmtSem.eval m (Expr.eq e (.int 0)) = some (.bool (x == 0)) at heqEval
  change SmtSem.eval m (Expr.eq e (.int 0)) = some (.bool false) at hbool
  rw [heqEval] at hbool
  simpa using hbool

theorem pcHolds_not_ne_int_zero {m : SmtSem.Model} {e : SExpr} {x : Int}
    (he : SmtSem.eval m e = some (.int x))
    (hpc : pcHolds m (SExpr.not (SExpr.ne e (.int 0))) = true) :
    x = 0 := by
  have hfalse :
      SmtSem.evalBoolIs m (SExpr.ne e (.int 0)) false = true :=
    (Moist.SMT.Semantics.evalBoolIs_not_true m (SExpr.ne e (.int 0))).mp
      (by simpa [pcHolds] using hpc)
  have hneEval : SmtSem.eval m (SExpr.ne e (.int 0)) = some (.bool false) :=
    (evalBoolIs_false_eq (m := m) (e := SExpr.ne e (.int 0))).mp hfalse
  have heqEval := Moist.SMT.Semantics.eval_eq_int_of (m := m)
    (a := e) (b := .int 0) (x := x) (y := 0) he
    (by simp [Moist.SMT.Semantics.eval])
  have hnotEval := eval_not_of_bool (m := m) (e := Expr.eq e (.int 0))
    (b := (x == 0)) heqEval
  change SmtSem.eval m (Expr.not (Expr.eq e (.int 0))) =
    some (.bool (!(x == 0))) at hnotEval
  change SmtSem.eval m (Expr.not (Expr.eq e (.int 0))) =
    some (.bool false) at hneEval
  rw [hnotEval] at hneEval
  simp at hneEval
  exact hneEval

theorem pcHolds_nonneg {m : SmtSem.Model} {e : SExpr} {x : Int}
    (he : SmtSem.eval m e = some (.int x))
    (hpc : pcHolds m (nonnegGuard e) = true) :
    0 ≤ x := by
  have hgeEval := Moist.SMT.Semantics.eval_ge_of (m := m) (a := e) (b := .int 0)
    (x := x) (y := 0) he (by simp [Moist.SMT.Semantics.eval])
  change SmtSem.eval m (Expr.ge e (.int 0)) = some (.bool (decide (x ≥ 0))) at hgeEval
  have hbool : SmtSem.eval m (nonnegGuard e) = some (.bool true) :=
    (Moist.SMT.Semantics.evalBoolIs_true_eq m (nonnegGuard e)).mp hpc
  change SmtSem.eval m (Expr.ge e (.int 0)) = some (.bool true) at hbool
  rw [hgeEval] at hbool
  simp at hbool
  exact hbool

theorem pcHolds_ge_int {m : SmtSem.Model} {a b : SExpr} {x y : Int}
    (ha : SmtSem.eval m a = some (.int x))
    (hb : SmtSem.eval m b = some (.int y))
    (hpc : pcHolds m (SExpr.ge a b) = true) :
    x ≥ y := by
  have hgeEval := Moist.SMT.Semantics.eval_ge_of (m := m) (a := a) (b := b)
    (x := x) (y := y) ha hb
  change SmtSem.eval m (Expr.ge a b) = some (.bool (decide (x ≥ y))) at hgeEval
  have hbool : SmtSem.eval m (SExpr.ge a b) = some (.bool true) :=
    (Moist.SMT.Semantics.evalBoolIs_true_eq m (SExpr.ge a b)).mp hpc
  change SmtSem.eval m (Expr.ge a b) = some (.bool true) at hbool
  rw [hgeEval] at hbool
  simp at hbool
  exact hbool

theorem pcHolds_le_int {m : SmtSem.Model} {a b : SExpr} {x y : Int}
    (ha : SmtSem.eval m a = some (.int x))
    (hb : SmtSem.eval m b = some (.int y))
    (hpc : pcHolds m (SExpr.le a b) = true) :
    x ≤ y := by
  have hleEval := Moist.SMT.Semantics.eval_le_of (m := m) (a := a) (b := b)
    (x := x) (y := y) ha hb
  change SmtSem.eval m (Expr.le a b) = some (.bool (decide (x ≤ y))) at hleEval
  have hbool : SmtSem.eval m (SExpr.le a b) = some (.bool true) :=
    (Moist.SMT.Semantics.evalBoolIs_true_eq m (SExpr.le a b)).mp hpc
  change SmtSem.eval m (Expr.le a b) = some (.bool true) at hbool
  rw [hleEval] at hbool
  simp at hbool
  exact hbool

theorem pcHolds_lt_int {m : SmtSem.Model} {a b : SExpr} {x y : Int}
    (ha : SmtSem.eval m a = some (.int x))
    (hb : SmtSem.eval m b = some (.int y))
    (hpc : pcHolds m (SExpr.lt a b) = true) :
    x < y := by
  have hltEval := Moist.SMT.Semantics.eval_lt_of (m := m) (a := a) (b := b)
    (x := x) (y := y) ha hb
  change SmtSem.eval m (Expr.lt a b) = some (.bool (decide (x < y))) at hltEval
  have hbool : SmtSem.eval m (SExpr.lt a b) = some (.bool true) :=
    (Moist.SMT.Semantics.evalBoolIs_true_eq m (SExpr.lt a b)).mp hpc
  change SmtSem.eval m (Expr.lt a b) = some (.bool true) at hbool
  rw [hltEval] at hbool
  simp at hbool
  exact hbool

theorem pcHolds_all2 {m : SmtSem.Model} {a b : SExpr}
    (h : pcHolds m (SExpr.all [a, b]) = true) :
    pcHolds m a = true ∧ pcHolds m b = true := by
  simpa [pcHolds, SExpr.all, Moist.SMT.Expr.all] using
    (Moist.SMT.Semantics.evalBoolIs_and_true m a b).mp h

theorem pcHolds_and_left {m : SmtSem.Model} {a b : SExpr}
    (h : pcHolds m (SExpr.and a b) = true) :
    pcHolds m a = true := by
  exact ((Moist.SMT.Semantics.evalBoolIs_and_true m a b).mp
    (by simpa [pcHolds] using h)).1

theorem pcHolds_if_and_left {m : SmtSem.Model} {p : Prop} [Decidable p]
    {a b : SExpr}
    (h : pcHolds m (if p then a else SExpr.and a b) = true) :
    pcHolds m a = true := by
  by_cases hp : p
  · simpa [hp] using h
  · exact pcHolds_and_left (m := m) (a := a) (b := b)
      (by simpa [hp] using h)

theorem pcHolds_all2_intro {m : SmtSem.Model} {a b : SExpr}
    (ha : pcHolds m a = true) (hb : pcHolds m b = true) :
    pcHolds m (SExpr.all [a, b]) = true := by
  simpa [pcHolds, SExpr.all, Moist.SMT.Expr.all] using
    (Moist.SMT.Semantics.evalBoolIs_and_true m a b).mpr ⟨ha, hb⟩

theorem pcHolds_and_intro {m : SmtSem.Model} {a b : SExpr}
    (ha : pcHolds m a = true) (hb : pcHolds m b = true) :
    pcHolds m (SExpr.and a b) = true := by
  simpa [pcHolds, SExpr.and, Moist.SMT.Expr.and] using
    (Moist.SMT.Semantics.evalBoolIs_and_true m a b).mpr ⟨ha, hb⟩

theorem pcHolds_ge_int_intro {m : SmtSem.Model} {a b : SExpr} {x y : Int}
    (ha : SmtSem.eval m a = some (.int x))
    (hb : SmtSem.eval m b = some (.int y))
    (hxy : y ≤ x) :
    pcHolds m (SExpr.ge a b) = true := by
  have hgeEval := Moist.SMT.Semantics.eval_ge_of (m := m) (a := a) (b := b)
    (x := x) (y := y) ha hb
  exact (Moist.SMT.Semantics.evalBoolIs_true_eq m (SExpr.ge a b)).mpr
    (by simpa [hxy] using hgeEval)

theorem pcHolds_lt_int_intro {m : SmtSem.Model} {a b : SExpr} {x y : Int}
    (ha : SmtSem.eval m a = some (.int x))
    (hb : SmtSem.eval m b = some (.int y))
    (hxy : x < y) :
    pcHolds m (SExpr.lt a b) = true := by
  have hltEval := Moist.SMT.Semantics.eval_lt_of (m := m) (a := a) (b := b)
    (x := x) (y := y) ha hb
  exact (Moist.SMT.Semantics.evalBoolIs_true_eq m (SExpr.lt a b)).mpr
    (by simpa [hxy] using hltEval)

theorem pcHolds_le_int_intro {m : SmtSem.Model} {a b : SExpr} {x y : Int}
    (ha : SmtSem.eval m a = some (.int x))
    (hb : SmtSem.eval m b = some (.int y))
    (hxy : x ≤ y) :
    pcHolds m (SExpr.le a b) = true := by
  have hleEval := Moist.SMT.Semantics.eval_le_of (m := m) (a := a) (b := b)
    (x := x) (y := y) ha hb
  exact (Moist.SMT.Semantics.evalBoolIs_true_eq m (SExpr.le a b)).mpr
    (by simpa [hxy] using hleEval)

theorem pcHolds_all3 {m : SmtSem.Model} {a b c : SExpr}
    (h : pcHolds m (SExpr.all [a, b, c]) = true) :
    pcHolds m a = true ∧ pcHolds m b = true ∧ pcHolds m c = true := by
  have h' :
      pcHolds m (SExpr.and (SExpr.and a b) c) = true := by
    simpa [SExpr.all, Moist.SMT.Expr.all] using h
  have hc := (Moist.SMT.Semantics.evalBoolIs_and_true m
    (SExpr.and a b) c).mp h'
  have hab := (Moist.SMT.Semantics.evalBoolIs_and_true m a b).mp hc.1
  exact ⟨hab.1, hab.2, hc.2⟩

theorem pcHolds_all3_intro {m : SmtSem.Model} {a b c : SExpr}
    (ha : pcHolds m a = true) (hb : pcHolds m b = true)
    (hc : pcHolds m c = true) :
    pcHolds m (SExpr.all [a, b, c]) = true := by
  have hab := pcHolds_and_intro (m := m) (a := a) (b := b) ha hb
  have habc := pcHolds_and_intro (m := m) (a := SExpr.and a b) (b := c) hab hc
  simpa [SExpr.all, Moist.SMT.Expr.all] using habc

theorem pcHolds_isDConstr_intro {m : SmtSem.Model} {e : SExpr}
    {tag : Int} {fields : List Plutus.Data}
    (he : SmtSem.eval m e = some (.data (.Constr tag fields))) :
    pcHolds m (SExpr.isCtor "DConstr" e) = true := by
  exact Moist.SMT.Semantics.evalBoolIs_isDConstr_true_of_data he

theorem pcHolds_isDMap_intro {m : SmtSem.Model} {e : SExpr}
    {ps : List (Plutus.Data × Plutus.Data)}
    (he : SmtSem.eval m e = some (.data (.Map ps))) :
    pcHolds m (SExpr.isCtor "DMap" e) = true := by
  exact Moist.SMT.Semantics.evalBoolIs_isDMap_true_of_data he

theorem pcHolds_isDList_intro {m : SmtSem.Model} {e : SExpr}
    {xs : List Plutus.Data}
    (he : SmtSem.eval m e = some (.data (.List xs))) :
    pcHolds m (SExpr.isCtor "DList" e) = true := by
  exact Moist.SMT.Semantics.evalBoolIs_isDList_true_of_data he

theorem pcHolds_isDI_intro {m : SmtSem.Model} {e : SExpr}
    {i : Int}
    (he : SmtSem.eval m e = some (.data (.I i))) :
    pcHolds m (SExpr.isCtor "DI" e) = true := by
  exact Moist.SMT.Semantics.evalBoolIs_isDI_true_of_data he

theorem pcHolds_isDB_intro {m : SmtSem.Model} {e : SExpr}
    {bs : ByteArray}
    (he : SmtSem.eval m e = some (.data (.B bs))) :
    pcHolds m (SExpr.isCtor "DB" e) = true := by
  exact Moist.SMT.Semantics.evalBoolIs_isDB_true_of_data he

theorem evalBoolIs_or_true_of_left {m : SmtSem.Model} {a b : SExpr}
    (ha : SmtSem.eval m a = some (.bool true))
    (hb : ∃ bb, SmtSem.eval m b = some (.bool bb)) :
    SmtSem.evalBoolIs m (SExpr.or a b) true = true := by
  rcases hb with ⟨bb, hb⟩
  unfold SmtSem.evalBoolIs Moist.SMT.Semantics.evalBoolIs
    Moist.SMT.Semantics.evalBool?
  simp [SExpr.or, Moist.SMT.Expr.or, Moist.SMT.Semantics.eval, ha, hb]

theorem evalBoolIs_or_true_of_right {m : SmtSem.Model} {a b : SExpr}
    (ha : ∃ ba, SmtSem.eval m a = some (.bool ba))
    (hb : SmtSem.eval m b = some (.bool true)) :
    SmtSem.evalBoolIs m (SExpr.or a b) true = true := by
  rcases ha with ⟨ba, ha⟩
  unfold SmtSem.evalBoolIs Moist.SMT.Semantics.evalBoolIs
    Moist.SMT.Semantics.evalBool?
  simp [SExpr.or, Moist.SMT.Expr.or, Moist.SMT.Semantics.eval, ha, hb]

theorem eval_or_bool_of_bool {m : SmtSem.Model} {a b : SExpr}
    (ha : ∃ ba, SmtSem.eval m a = some (.bool ba))
    (hb : ∃ bb, SmtSem.eval m b = some (.bool bb)) :
    ∃ bc, SmtSem.eval m (SExpr.or a b) = some (.bool bc) := by
  rcases ha with ⟨ba, ha⟩
  rcases hb with ⟨bb, hb⟩
  exact ⟨ba || bb,
    by simp [SExpr.or, Moist.SMT.Expr.or, Moist.SMT.Semantics.eval, ha, hb]⟩

theorem evalBoolIs_foldl_or_true_of_acc_true {m : SmtSem.Model} :
    ∀ {xs : List SExpr} {acc : SExpr},
      SmtSem.eval m acc = some (.bool true) →
      (∀ x, x ∈ xs → ∃ b, SmtSem.eval m x = some (.bool b)) →
      SmtSem.evalBoolIs m (xs.foldl SExpr.or acc) true = true
  | [], acc, hacc, _ =>
      (Moist.SMT.Semantics.evalBoolIs_true_eq m acc).mpr hacc
  | x :: xs, acc, hacc, hxs => by
      obtain ⟨b, hx⟩ := hxs x (by simp)
      have hor := evalBoolIs_or_true_of_left (m := m) (a := acc) (b := x)
        hacc ⟨b, hx⟩
      have horEval :
          SmtSem.eval m (SExpr.or acc x) = some (.bool true) :=
        (Moist.SMT.Semantics.evalBoolIs_true_eq m (SExpr.or acc x)).mp hor
      exact evalBoolIs_foldl_or_true_of_acc_true (m := m)
        (xs := xs) (acc := SExpr.or acc x) horEval
        (by intro y hy; exact hxs y (by simp [hy]))

theorem evalBoolIs_foldl_or_true_of_mem {m : SmtSem.Model} {x : SExpr} :
    ∀ {xs : List SExpr} {acc : SExpr},
      (∃ b, SmtSem.eval m acc = some (.bool b)) →
      x ∈ xs →
      SmtSem.eval m x = some (.bool true) →
      (∀ y, y ∈ xs → ∃ b, SmtSem.eval m y = some (.bool b)) →
      SmtSem.evalBoolIs m (xs.foldl SExpr.or acc) true = true
  | [], acc, _hacc, hxmem, _hxtrue, _hall => by
      simp at hxmem
  | y :: ys, acc, hacc, hxmem, hxtrue, hall => by
      simp at hxmem
      rcases hxmem with hxy | hxys
      · subst y
        have hor := evalBoolIs_or_true_of_right (m := m) (a := acc) (b := x)
          hacc hxtrue
        have horEval :
            SmtSem.eval m (SExpr.or acc x) = some (.bool true) :=
          (Moist.SMT.Semantics.evalBoolIs_true_eq m (SExpr.or acc x)).mp hor
        exact evalBoolIs_foldl_or_true_of_acc_true (m := m)
          (xs := ys) (acc := SExpr.or acc x) horEval
          (by intro z hz; exact hall z (by simp [hz]))
      · have hyBool : ∃ b, SmtSem.eval m y = some (.bool b) :=
          hall y (by simp)
        have hacc' := eval_or_bool_of_bool (m := m) (a := acc) (b := y)
          hacc hyBool
        exact evalBoolIs_foldl_or_true_of_mem (m := m) (x := x)
          (xs := ys) (acc := SExpr.or acc y) hacc' hxys hxtrue
          (by intro z hz; exact hall z (by simp [hz]))

theorem evalBoolIs_any_true_of_mem {m : SmtSem.Model} {x : SExpr} {xs : List SExpr}
    (hmem : x ∈ xs)
    (hx : SmtSem.eval m x = some (.bool true))
    (hall : ∀ y, y ∈ xs → ∃ b, SmtSem.eval m y = some (.bool b)) :
    SmtSem.evalBoolIs m (SExpr.any xs) true = true := by
  cases xs with
  | nil =>
      simp at hmem
  | cons y ys =>
      cases ys with
      | nil =>
          simp at hmem
          subst x
          simpa [SExpr.any, Moist.SMT.Expr.any] using
            (Moist.SMT.Semantics.evalBoolIs_true_eq m y).mpr hx
      | cons z zs =>
          simp [SExpr.any, Moist.SMT.Expr.any]
          simp at hmem
          rcases hmem with hxy | hxrest
          · subst x
            exact evalBoolIs_foldl_or_true_of_acc_true (m := m)
              (xs := z :: zs) (acc := y) hx
              (by intro w hw; exact hall w (by simp [hw]))
          · have hyBool : ∃ b, SmtSem.eval m y = some (.bool b) :=
              hall y (by simp)
            have hxmemTail : x ∈ z :: zs := by simpa using hxrest
            exact evalBoolIs_foldl_or_true_of_mem (m := m) (x := x)
              (xs := z :: zs) (acc := y) hyBool hxmemTail hx
              (by intro w hw; exact hall w (by simp [hw]))

theorem eval_eq_int_bool {m : SmtSem.Model} {tagExpr : SExpr}
    {tagInt : Int} {i : Nat}
    (htag : SmtSem.eval m tagExpr = some (.int tagInt)) :
    ∃ b, SmtSem.eval m (SExpr.eq tagExpr (.int (Int.ofNat i))) =
      some (.bool b) := by
  refine ⟨tagInt == Int.ofNat i, ?_⟩
  simpa using Moist.SMT.Semantics.eval_eq_int_of (m := m)
    (a := tagExpr) (b := .int (Int.ofNat i))
    (x := tagInt) (y := Int.ofNat i) htag
    (by simp [Moist.SMT.Semantics.eval])

theorem tagCovered_true_of_get {m : SmtSem.Model} {alts : List Term}
    {tagExpr : SExpr} {tagInt : Int} {i : Nat} {alt : Term}
    (htag : SmtSem.eval m tagExpr = some (.int tagInt))
    (htagEq : tagInt = Int.ofNat i)
    (hget : alts[i]? = some alt) :
    pcHolds m (SExpr.any ((enumerate alts).map fun (j, _) =>
      SExpr.eq tagExpr (.int (Int.ofNat j)))) = true := by
  have henum : (i, alt) ∈ enumerate alts := enumerate_get?_mem hget
  let x : SExpr := SExpr.eq tagExpr (.int (Int.ofNat i))
  have hmemMap : x ∈ (enumerate alts).map fun (j, _) =>
      SExpr.eq tagExpr (.int (Int.ofNat j)) := by
    exact List.mem_map.mpr ⟨(i, alt), henum, rfl⟩
  have hxEval : SmtSem.eval m x = some (.bool true) := by
    have heq := Moist.SMT.Semantics.eval_eq_int_of (m := m)
      (a := tagExpr) (b := .int (Int.ofNat i))
      (x := tagInt) (y := Int.ofNat i) htag
      (by simp [Moist.SMT.Semantics.eval])
    subst tagInt
    simpa [x] using heq
  have hall : ∀ y, y ∈ (enumerate alts).map
      (fun (j, _) => SExpr.eq tagExpr (.int (Int.ofNat j))) →
      ∃ b, SmtSem.eval m y = some (.bool b) := by
    intro y hy
    simp only [List.mem_map] at hy
    rcases hy with ⟨p, _hp, rfl⟩
    rcases p with ⟨j, _t⟩
    exact eval_eq_int_bool (m := m) (tagExpr := tagExpr)
      (tagInt := tagInt) (i := j) htag
  exact evalBoolIs_any_true_of_mem (m := m) (x := x) hmemMap hxEval hall

theorem eval_ite_of_bool {m : SmtSem.Model} {c t e : SExpr} {b : Bool}
    (hc : SmtSem.eval m c = some (.bool b)) :
    SmtSem.eval m (.ite c t e) =
      if b then SmtSem.eval m t else SmtSem.eval m e := by
  change Moist.SMT.Semantics.eval m (Expr.ite c t e) =
    if b then Moist.SMT.Semantics.eval m t else Moist.SMT.Semantics.eval m e
  rw [Moist.SMT.Semantics.eval.eq_def]
  simp [hc]
  cases b <;> rfl

theorem eval_nonneg_clamp_int_of {m : SmtSem.Model} {e : SExpr} {x : Int}
    (he : SmtSem.eval m e = some (.int x)) :
    SmtSem.eval m (SExpr.ite (SExpr.lt e (.int 0)) (.int 0) e) =
      some (.int (if x < 0 then 0 else x)) := by
  have hlt := Moist.SMT.Semantics.eval_lt_of (m := m) (a := e) (b := .int 0)
    (x := x) (y := 0) he (by simp [Moist.SMT.Semantics.eval])
  change SmtSem.eval m (SExpr.lt e (.int 0)) =
    some (.bool (decide (x < 0))) at hlt
  change Moist.SMT.Semantics.eval m
    (Expr.ite (SExpr.lt e (.int 0)) (.int 0) e) =
      some (.int (if x < 0 then 0 else x))
  rw [Moist.SMT.Semantics.eval.eq_def]
  simp [hlt]
  by_cases hx : x < 0 <;> simp [hx, he, Moist.SMT.Semantics.eval]

theorem intOfNat_eq_zero {i : Nat} (h : (0 : Int) = Int.ofNat i) : i = 0 := by
  have h' : Int.ofNat i = Int.ofNat 0 := by simpa using h.symm
  exact Int.ofNat.inj h'

theorem intOfNat_eq_one {i : Nat} (h : (1 : Int) = Int.ofNat i) : i = 1 := by
  have h' : Int.ofNat i = Int.ofNat 1 := by simpa using h.symm
  exact Int.ofNat.inj h'

/-!
The compiler is intentionally larger than the verified subset.  Restored
symbolic builtins, opaque functions, and symbolic case compilation are kept in
`UPLC.lean`; this file records the proof obligations needed to justify them
against CEK/big-step semantics.
-/

theorem semValToConst_constToVal : ∀ c,
    semValToConst? (Moist.SMT.Semantics.constToVal c) = some c := by
  intro c
  exact Const.rec
    (motive_1 := fun c => semValToConst? (Moist.SMT.Semantics.constToVal c) = some c)
    (motive_2 := fun xs =>
      semValListToConstList? (Moist.SMT.Semantics.constListToVals xs) = some xs)
    (motive_3 := fun p =>
      semValToConst? (Moist.SMT.Semantics.constToVal p.1) = some p.1 ∧
      semValToConst? (Moist.SMT.Semantics.constToVal p.2) = some p.2)
    (fun _ => by rfl)
    (fun _ => by rfl)
    (fun _ => by rfl)
    (by rfl)
    (fun _ => by rfl)
    (fun _ hxs => by simp [Moist.SMT.Semantics.constToVal, semValToConst?, hxs])
    (fun _ => by rfl)
    (fun _ => by rfl)
    (fun p hp => by
      cases p with
      | mk a b =>
          rcases hp with ⟨ha, hb⟩
          simp [Moist.SMT.Semantics.constToVal, semValToConst?, ha, hb])
    (fun p => by cases p; rfl)
    (fun _ => by rfl)
    (fun _ hxs => by simp [Moist.SMT.Semantics.constToVal, semValToConst?, hxs])
    (by rfl)
    (by rfl)
    (by rfl)
    (by rfl)
    (fun _ _ hc hcs => by
      simp [Moist.SMT.Semantics.constListToVals, semValListToConstList?, hc, hcs])
    (fun _ _ ha hb => ⟨ha, hb⟩)
    c

theorem semValListToConstList_constListToVals : ∀ xs,
    semValListToConstList? (Moist.SMT.Semantics.constListToVals xs) = some xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons c cs ih =>
      simp [Moist.SMT.Semantics.constListToVals, semValListToConstList?,
        semValToConst_constToVal c, ih]

theorem semValListToConstList_drop :
    ∀ {vals : List Moist.SMT.Semantics.Val} {cs : List Const} {n : Nat},
      semValListToConstList? vals = some cs →
      semValListToConstList? (vals.drop n) = some (cs.drop n) := by
  intro vals
  induction vals with
  | nil =>
      intro cs n h
      simp [semValListToConstList?] at h
      subst cs
      cases n <;> rfl
  | cons v vs ih =>
      intro cs n h
      cases hc : semValToConst? v <;> simp [semValListToConstList?, hc] at h
      rename_i c
      cases hcs : semValListToConstList? vs <;> simp [hcs] at h
      rename_i csTail
      subst cs
      cases n with
      | zero =>
          simp [semValListToConstList?, hc, hcs]
      | succ n =>
          simpa using ih (cs := csTail) (n := n) hcs

theorem semValListToConstList_length :
    ∀ {vals : List Moist.SMT.Semantics.Val} {cs : List Const},
      semValListToConstList? vals = some cs →
      vals.length = cs.length := by
  intro vals
  induction vals with
  | nil =>
      intro cs h
      simp [semValListToConstList?] at h
      subst cs
      rfl
  | cons v vs ih =>
      intro cs h
      cases hc : semValToConst? v <;> simp [semValListToConstList?, hc] at h
      cases hcs : semValListToConstList? vs <;> simp [hcs] at h
      subst cs
      simp [ih hcs]

set_option maxHeartbeats 0 in
theorem semValToCek_vcon_const {v : SmtSem.Val} {c : Const}
    (h : semValToCek? v = some (.VCon c)) :
    semValToConst? v = some c := by
  cases v with
  | int i => simpa [semValToCek?, semValToConst?] using h
  | bytes bs => simpa [semValToCek?, semValToConst?] using h
  | string s => simpa [semValToCek?, semValToConst?] using h
  | bool b => simpa [semValToCek?, semValToConst?] using h
  | unit => simpa [semValToCek?, semValToConst?] using h
  | data d => simpa [semValToCek?, semValToConst?] using h
  | dataList ds => simpa [semValToCek?, semValToConst?] using h
  | pairDataList ps => simpa [semValToCek?, semValToConst?] using h
  | pairData a b => simpa [semValToCek?, semValToConst?] using h
  | g1 g => simpa [semValToCek?, semValToConst?] using h
  | g2 g => simpa [semValToCek?, semValToConst?] using h
  | ml r => simpa [semValToCek?, semValToConst?] using h
  | list xs =>
      simp [semValToCek?, semValToConst?] at h ⊢
      cases hcs : semValListToConstList? xs <;> simp [hcs] at h ⊢
      exact h
  | pair a b =>
      simp [semValToCek?, semValToConst?] at h ⊢
      cases ha : semValToConst? a <;> simp [ha] at h ⊢
      cases hb : semValToConst? b <;> simp [hb] at h ⊢
      exact h
  | array xs =>
      simp [semValToCek?, semValToConst?] at h ⊢
      cases hcs : semValListToConstList? xs <;> simp [hcs] at h ⊢
      exact h
  | constr tag fields =>
      simp [semValToCek?] at h
      cases hfields : semValListToCekList? fields <;> simp [hfields] at h

mutual
  theorem semValToConst_constValCompatible {v : SmtSem.Val} {c : Const}
      (h : semValToConst? v = some c) :
      Moist.SMT.Semantics.constValCompatible v = true := by
    cases v with
    | int i => rfl
    | bytes bs => rfl
    | string s => rfl
    | bool b => rfl
    | unit => rfl
    | data d => rfl
    | dataList ds => rfl
    | pairDataList ps => rfl
    | pairData a b => rfl
    | g1 g => rfl
    | g2 g => rfl
    | ml r => rfl
    | constr tag fields => simp [semValToConst?] at h
    | list xs =>
        simp [semValToConst?] at h
        cases hcs : semValListToConstList? xs <;> simp [hcs] at h
        exact semValListToConstList_constValListCompatible hcs
    | pair a b =>
        simp [semValToConst?] at h
        cases ha : semValToConst? a <;> simp [ha] at h
        cases hb : semValToConst? b <;> simp [hb] at h
        simp [Moist.SMT.Semantics.constValCompatible,
          semValToConst_constValCompatible ha,
          semValToConst_constValCompatible hb]
    | array xs =>
        simp [semValToConst?] at h
        cases hcs : semValListToConstList? xs <;> simp [hcs] at h
        exact semValListToConstList_constValListCompatible hcs

  theorem semValListToConstList_constValListCompatible {xs : List SmtSem.Val}
      {cs : List Const}
      (h : semValListToConstList? xs = some cs) :
      Moist.SMT.Semantics.constValListCompatible xs = true := by
    cases xs with
    | nil => rfl
    | cons x xs =>
        simp [semValListToConstList?] at h
        cases hx : semValToConst? x <;> simp [hx] at h
        cases hxs : semValListToConstList? xs <;> simp [hxs] at h
        simp [Moist.SMT.Semantics.constValListCompatible,
          semValToConst_constValCompatible hx,
          semValListToConstList_constValListCompatible hxs]
end

theorem semValListToConstList_get? :
    ∀ {vals : List Moist.SMT.Semantics.Val} {cs : List Const}
      {i : Nat} {v : Moist.SMT.Semantics.Val},
      semValListToConstList? vals = some cs →
      vals[i]? = some v →
      ∃ c, cs[i]? = some c ∧ semValToConst? v = some c := by
  intro vals
  induction vals with
  | nil =>
      intro cs i v h hget
      simp at hget
  | cons x xs ih =>
      intro cs i v h hget
      cases hx : semValToConst? x <;> simp [semValListToConstList?, hx] at h
      rename_i cx
      cases hxs : semValListToConstList? xs <;> simp [hxs] at h
      rename_i cxs
      subst cs
      cases i with
      | zero =>
          simp at hget
          subst v
          exact ⟨cx, by simp, hx⟩
      | succ i =>
          simp at hget
          obtain ⟨c, hgetCs, hc⟩ := ih (cs := cxs) (i := i) hxs hget
          exact ⟨c, by simpa using hgetCs, hc⟩

theorem constLiteral_sound (m : SmtSem.Model) : ∀ c,
    symValToCek? m (constLiteral c) = some (.VCon c) := by
  intro c
  exact Const.rec
    (motive_1 := fun c => symValToCek? m (constLiteral c) = some (.VCon c))
    (motive_2 := fun _ => True)
    (motive_3 := fun p =>
      symValToCek? m (constLiteral p.1) = some (.VCon p.1) ∧
      symValToCek? m (constLiteral p.2) = some (.VCon p.2))
    (fun _ => by simp [constLiteral, symValToCek?, symConstToCek?, Moist.SMT.Semantics.eval])
    (fun _ => by
      simp [constLiteral, bytesLiteral, symValToCek?, symConstToCek?,
        Moist.SMT.Semantics.eval])
    (fun _ => by simp [constLiteral, symValToCek?, symConstToCek?, Moist.SMT.Semantics.eval])
    (by simp [constLiteral, symValToCek?, symConstToCek?])
    (fun _ => by simp [constLiteral, symValToCek?, symConstToCek?, Moist.SMT.Semantics.eval])
    (fun _ _ => by
      simp [constLiteral, symValToCek?, symConstToCek?, Moist.SMT.Semantics.eval,
        semValListToConstList_constListToVals])
    (fun _ => by
      simp [constLiteral, dataListLiteral, symValToCek?, symConstToCek?,
        Moist.SMT.Semantics.eval])
    (fun _ => by
      simp [constLiteral, dataPairListLiteral, symValToCek?, symConstToCek?,
        Moist.SMT.Semantics.eval])
    (fun p hp => by cases p; simp [constLiteral, symValToCek?, hp.1, hp.2])
    (fun p => by
      cases p
      simp [constLiteral, dataLiteral, symValToCek?, symConstToCek?,
        Moist.SMT.Semantics.eval])
    (fun _ => by
      simp [constLiteral, dataLiteral, symValToCek?, symConstToCek?,
        Moist.SMT.Semantics.eval])
    (fun _ _ => by
      simp [constLiteral, symValToCek?, symConstToCek?, Moist.SMT.Semantics.eval,
        semValListToConstList_constListToVals])
    (by simp [constLiteral, symValToCek?, symConstToCek?, Moist.SMT.Semantics.eval])
    (by simp [constLiteral, symValToCek?, symConstToCek?, Moist.SMT.Semantics.eval])
    (by simp [constLiteral, symValToCek?, symConstToCek?, Moist.SMT.Semantics.eval])
    trivial
    (fun _ _ _ _ => trivial)
    (fun _ _ ha hb => ⟨ha, hb⟩)
    c

theorem constLiteral_noOpaque : ∀ c,
    symValNoOpaqueForSoundness (constLiteral c) = true := by
  intro c
  exact Const.rec
    (motive_1 := fun c => symValNoOpaqueForSoundness (constLiteral c) = true)
    (motive_2 := fun _ => True)
    (motive_3 := fun p =>
      symValNoOpaqueForSoundness (constLiteral p.1) = true ∧
      symValNoOpaqueForSoundness (constLiteral p.2) = true)
    (fun _ => by simp [constLiteral, symValNoOpaqueForSoundness])
    (fun _ => by simp [constLiteral, symValNoOpaqueForSoundness])
    (fun _ => by simp [constLiteral, symValNoOpaqueForSoundness])
    (by simp [constLiteral, symValNoOpaqueForSoundness])
    (fun _ => by simp [constLiteral, symValNoOpaqueForSoundness])
    (fun _ _ => by simp [constLiteral, symValNoOpaqueForSoundness])
    (fun _ => by simp [constLiteral, symValNoOpaqueForSoundness])
    (fun _ => by simp [constLiteral, symValNoOpaqueForSoundness])
    (fun p hp => by cases p; simp [constLiteral, symValNoOpaqueForSoundness, hp.1, hp.2])
    (fun p => by cases p; simp [constLiteral, symValNoOpaqueForSoundness])
    (fun _ => by simp [constLiteral, symValNoOpaqueForSoundness])
    (fun _ _ => by simp [constLiteral, symValNoOpaqueForSoundness])
    (by simp [constLiteral, symValNoOpaqueForSoundness])
    (by simp [constLiteral, symValNoOpaqueForSoundness])
    (by simp [constLiteral, symValNoOpaqueForSoundness])
    trivial
    (fun _ _ _ _ => trivial)
    (fun _ _ ha hb => ⟨ha, hb⟩)
    c

theorem semValToCek_of_const {v : SmtSem.Val} {c : Const}
    (h : semValToConst? v = some c) :
    semValToCek? v = some (.VCon c) := by
  rw [semValToCek?.eq_def]
  cases v <;> simp [semValToConst?] at h ⊢
  all_goals try assumption
  all_goals try simp_all

theorem semValToCek_con_or_constr {v : SmtSem.Val} {cv : CekValue}
    (h : semValToCek? v = some cv) :
    (∃ c, cv = .VCon c) ∨ ∃ tag fields, cv = .VConstr tag fields := by
  rw [semValToCek?.eq_def] at h
  cases v <;> simp [semValToConst?] at h
  case constr tag fields =>
    rcases h with ⟨_, hbind⟩
    cases hfields : semValListToCekList? fields <;> simp [hfields] at hbind
    rename_i cfields
    subst cv
    exact Or.inr ⟨tag.toNat, cfields, rfl⟩
  case list xs =>
    cases hcs : semValListToConstList? xs <;> simp [hcs] at h
    subst cv
    exact Or.inl ⟨_, rfl⟩
  case pair a b =>
    cases ha : semValToConst? a <;> simp [ha] at h
    cases hb : semValToConst? b <;> simp [hb] at h
    subst cv
    exact Or.inl ⟨_, rfl⟩
  case array xs =>
    cases hcs : semValListToConstList? xs <;> simp [hcs] at h
    subst cv
    exact Or.inl ⟨_, rfl⟩
  all_goals
    subst cv
    exact Or.inl ⟨_, rfl⟩

theorem semValToCek_integer {v : SmtSem.Val} {i : Int}
    (h : semValToCek? v = some (.VCon (.Integer i))) :
    v = .int i := by
  rw [semValToCek?.eq_def] at h
  cases v <;> simp [semValToConst?] at h
  case int j =>
    subst i
    rfl
  case list vals =>
    cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  case pair a b =>
    cases ha : semValToConst? a <;> simp [ha] at h
    cases hb : semValToConst? b <;> simp [hb] at h
  case array vals =>
    cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  case constr tag fields =>
    rcases h with ⟨_hge, hfieldsBind⟩
    cases hfields : semValListToCekList? fields <;> simp [hfields] at hfieldsBind

theorem semValToCek_bytes {v : SmtSem.Val} {bs : ByteArray}
    (h : semValToCek? v = some (.VCon (.ByteString bs))) :
    v = .bytes bs := by
  rw [semValToCek?.eq_def] at h
  cases v <;> simp [semValToConst?] at h
  case bytes bs' =>
    subst bs
    rfl
  case list vals =>
    cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  case pair a b =>
    cases ha : semValToConst? a <;> simp [ha] at h
    cases hb : semValToConst? b <;> simp [hb] at h
  case array vals =>
    cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  case constr tag fields =>
    rcases h with ⟨_hge, hfieldsBind⟩
    cases hfields : semValListToCekList? fields <;> simp [hfields] at hfieldsBind

theorem semValToCek_string {v : SmtSem.Val} {s : String}
    (h : semValToCek? v = some (.VCon (.String s))) :
    v = .string s := by
  rw [semValToCek?.eq_def] at h
  cases v <;> simp [semValToConst?] at h
  case string s' =>
    subst s
    rfl
  case list vals =>
    cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  case pair a b =>
    cases ha : semValToConst? a <;> simp [ha] at h
    cases hb : semValToConst? b <;> simp [hb] at h
  case array vals =>
    cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  case constr tag fields =>
    rcases h with ⟨_hge, hfieldsBind⟩
    cases hfields : semValListToCekList? fields <;> simp [hfields] at hfieldsBind

theorem semValToCek_bool {v : SmtSem.Val} {b : Bool}
    (h : semValToCek? v = some (.VCon (.Bool b))) :
    v = .bool b := by
  rw [semValToCek?.eq_def] at h
  cases v <;> simp [semValToConst?] at h
  case bool b' =>
    subst b
    rfl
  case list vals =>
    cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  case pair a b =>
    cases ha : semValToConst? a <;> simp [ha] at h
    cases hb : semValToConst? b <;> simp [hb] at h
  case array vals =>
    cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  case constr tag fields =>
    rcases h with ⟨_hge, hfieldsBind⟩
    cases hfields : semValListToCekList? fields <;> simp [hfields] at hfieldsBind

theorem symConstToCek_bool {m : SmtSem.Model} {c : SymConst} {b : Bool}
    (h : symConstToCek? m c = some (.VCon (.Bool b))) :
    ∃ e, c = .bool e ∧ SmtSem.eval m e = some (.bool b) := by
  cases c with
  | integer e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | bytes e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | string e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | bool e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
      subst b
      exact ⟨e, rfl, he⟩
  | unit =>
      simp [symConstToCek?] at h
  | data e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | constList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
      case valList vals =>
        cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  | dataList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | pairDataList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | pairData a b =>
      simp [symConstToCek?] at h
      cases ha : SmtSem.eval m a <;> simp [ha] at h
      rename_i sva
      cases hb : SmtSem.eval m b <;> simp [ha, hb] at h
      rename_i svb
      cases sva <;> cases svb <;> simp [ha, hb] at h
  | array e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
      case valList vals =>
        cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  | g1 e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | g2 e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | ml e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h

theorem semValToCek_data {v : SmtSem.Val} {d : Plutus.Data}
    (h : semValToCek? v = some (.VCon (.Data d))) :
    v = .data d := by
  rw [semValToCek?.eq_def] at h
  cases v <;> simp [semValToConst?] at h
  case data d' =>
    subst d
    rfl
  case list vals =>
    cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  case pair a b =>
    cases ha : semValToConst? a <;> simp [ha] at h
    cases hb : semValToConst? b <;> simp [hb] at h
  case array vals =>
    cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  case constr tag fields =>
    rcases h with ⟨_hge, hfieldsBind⟩
    cases hfields : semValListToCekList? fields <;> simp [hfields] at hfieldsBind

theorem semValToCek_dataList {v : SmtSem.Val} {xs : List Plutus.Data}
    (h : semValToCek? v = some (.VCon (.ConstDataList xs))) :
    v = .dataList xs := by
  rw [semValToCek?.eq_def] at h
  cases v <;> simp [semValToConst?] at h
  case dataList ys =>
    subst xs
    rfl
  case list vals =>
    cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  case pair a b =>
    cases ha : semValToConst? a <;> simp [ha] at h
    cases hb : semValToConst? b <;> simp [hb] at h
  case array vals =>
    cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  case constr tag fields =>
    rcases h with ⟨_hge, hfieldsBind⟩
    cases hfields : semValListToCekList? fields <;> simp [hfields] at hfieldsBind

theorem semValToCek_pairDataList {v : SmtSem.Val}
    {xs : List (Plutus.Data × Plutus.Data)}
    (h : semValToCek? v = some (.VCon (.ConstPairDataList xs))) :
    v = .pairDataList xs := by
  rw [semValToCek?.eq_def] at h
  cases v <;> simp [semValToConst?] at h
  case pairDataList ys =>
    subst xs
    rfl
  case list vals =>
    cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  case pair a b =>
    cases ha : semValToConst? a <;> simp [ha] at h
    cases hb : semValToConst? b <;> simp [hb] at h
  case array vals =>
    cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  case constr tag fields =>
    rcases h with ⟨_hge, hfieldsBind⟩
    cases hfields : semValListToCekList? fields <;> simp [hfields] at hfieldsBind

theorem semValToCek_constList {v : SmtSem.Val} {cs : List Const}
    (h : semValToCek? v = some (.VCon (.ConstList cs))) :
    ∃ vals, v = .list vals ∧ semValListToConstList? vals = some cs := by
  rw [semValToCek?.eq_def] at h
  cases v <;> simp [semValToConst?] at h
  case list vals =>
    cases hcs : semValListToConstList? vals <;> simp [hcs] at h
    rename_i cs'
    subst cs
    exact ⟨vals, rfl, hcs⟩
  case pair a b =>
    cases ha : semValToConst? a <;> simp [ha] at h
    cases hb : semValToConst? b <;> simp [hb] at h
  case array vals =>
    cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  case constr tag fields =>
    rcases h with ⟨_hge, hfieldsBind⟩
    cases hfields : semValListToCekList? fields <;> simp [hfields] at hfieldsBind

theorem semValToCek_array {v : SmtSem.Val} {cs : List Const}
    (h : semValToCek? v = some (.VCon (.ConstArray cs))) :
    ∃ vals, v = .array vals ∧ semValListToConstList? vals = some cs := by
  rw [semValToCek?.eq_def] at h
  cases v <;> simp [semValToConst?] at h
  case list vals =>
    cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  case pair a b =>
    cases ha : semValToConst? a <;> simp [ha] at h
    cases hb : semValToConst? b <;> simp [hb] at h
  case array vals =>
    cases hcs : semValListToConstList? vals <;> simp [hcs] at h
    rename_i cs'
    subst cs
    exact ⟨vals, rfl, hcs⟩
  case constr tag fields =>
    rcases h with ⟨_hge, hfieldsBind⟩
    cases hfields : semValListToCekList? fields <;> simp [hfields] at hfieldsBind

theorem symConstToCek_integer {m : SmtSem.Model} {c : SymConst} {i : Int}
    (h : symConstToCek? m c = some (.VCon (.Integer i))) :
    ∃ e, c = .integer e ∧ SmtSem.eval m e = some (.int i) := by
  cases c with
  | integer e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
      subst i
      exact ⟨e, rfl, he⟩
  | bytes e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | string e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | bool e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | unit =>
      simp [symConstToCek?] at h
  | data e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | constList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
      case valList vals =>
        cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  | dataList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | pairDataList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | pairData a b =>
      simp [symConstToCek?] at h
      cases ha : SmtSem.eval m a <;> simp [ha] at h
      rename_i sva
      cases hb : SmtSem.eval m b <;> simp [ha, hb] at h
      rename_i svb
      cases sva <;> cases svb <;> simp [ha, hb] at h
  | array e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
      case valList vals =>
        cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  | g1 e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | g2 e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | ml e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h

theorem symConstToCek_bytes {m : SmtSem.Model} {c : SymConst} {bs : ByteArray}
    (h : symConstToCek? m c = some (.VCon (.ByteString bs))) :
    ∃ e, c = .bytes e ∧ SmtSem.eval m e = some (.bytes bs) := by
  cases c with
  | integer e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | bytes e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
      case bytes bs' =>
        subst bs
        exact ⟨e, rfl, he⟩
  | string e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | bool e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | unit =>
      simp [symConstToCek?] at h
  | data e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | constList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
      case valList vals =>
        cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  | dataList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | pairDataList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | pairData a b =>
      simp [symConstToCek?] at h
      cases ha : SmtSem.eval m a <;> simp [ha] at h
      rename_i sva
      cases hb : SmtSem.eval m b <;> simp [ha, hb] at h
      rename_i svb
      cases sva <;> cases svb <;> simp [ha, hb] at h
  | array e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
      case valList vals =>
        cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  | g1 e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | g2 e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | ml e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h

theorem symConstToCek_string {m : SmtSem.Model} {c : SymConst} {s : String}
    (h : symConstToCek? m c = some (.VCon (.String s))) :
    ∃ e, c = .string e ∧ SmtSem.eval m e = some (.string s) := by
  cases c with
  | integer e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | bytes e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | string e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
      case string s' =>
        subst s
        exact ⟨e, rfl, he⟩
  | bool e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | unit =>
      simp [symConstToCek?] at h
  | data e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | constList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
      case valList vals =>
        cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  | dataList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | pairDataList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | pairData a b =>
      simp [symConstToCek?] at h
      cases ha : SmtSem.eval m a <;> simp [ha] at h
      rename_i sva
      cases hb : SmtSem.eval m b <;> simp [ha, hb] at h
      rename_i svb
      cases sva <;> cases svb <;> simp [ha, hb] at h
  | array e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
      case valList vals =>
        cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  | g1 e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | g2 e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | ml e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h

theorem symConstToCek_data {m : SmtSem.Model} {c : SymConst} {d : Plutus.Data}
    (h : symConstToCek? m c = some (.VCon (.Data d))) :
    ∃ e, c = .data e ∧ SmtSem.eval m e = some (.data d) := by
  cases c with
  | integer e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | bytes e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | string e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | bool e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | unit =>
      simp [symConstToCek?] at h
  | data e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
      case data d' =>
        subst d
        exact ⟨e, rfl, he⟩
  | constList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
      case valList vals =>
        cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  | dataList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | pairDataList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | pairData a b =>
      simp [symConstToCek?] at h
      cases ha : SmtSem.eval m a <;> simp [ha] at h
      rename_i sva
      cases hb : SmtSem.eval m b <;> simp [ha, hb] at h
      rename_i svb
      cases sva <;> cases svb <;> simp [ha, hb] at h
  | array e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
      case valList vals =>
        cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  | g1 e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | g2 e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | ml e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h

theorem symConstToCek_dataList {m : SmtSem.Model} {c : SymConst} {xs : List Plutus.Data}
    (h : symConstToCek? m c = some (.VCon (.ConstDataList xs))) :
    ∃ e, c = .dataList e ∧ SmtSem.eval m e = some (.dataList xs) := by
  cases c with
  | integer e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | bytes e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | string e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | bool e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | unit =>
      simp [symConstToCek?] at h
  | data e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | constList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
      case valList vals =>
        cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  | dataList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
      case dataList ys =>
        subst xs
        exact ⟨e, rfl, he⟩
  | pairDataList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | pairData a b =>
      simp [symConstToCek?] at h
      cases ha : SmtSem.eval m a <;> simp [ha] at h
      rename_i sva
      cases hb : SmtSem.eval m b <;> simp [ha, hb] at h
      rename_i svb
      cases sva <;> cases svb <;> simp [ha, hb] at h
  | array e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
      case valList vals =>
        cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  | g1 e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | g2 e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | ml e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h

theorem symConstToCek_pairDataList {m : SmtSem.Model} {c : SymConst}
    {xs : List (Plutus.Data × Plutus.Data)}
    (h : symConstToCek? m c = some (.VCon (.ConstPairDataList xs))) :
    ∃ e, c = .pairDataList e ∧ SmtSem.eval m e = some (.dataPairList xs) := by
  cases c with
  | integer e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | bytes e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | string e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | bool e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | unit =>
      simp [symConstToCek?] at h
  | data e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | constList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
      case valList vals =>
        cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  | dataList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | pairDataList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
      case dataPairList ys =>
        subst xs
        exact ⟨e, rfl, he⟩
  | pairData a b =>
      simp [symConstToCek?] at h
      cases ha : SmtSem.eval m a <;> simp [ha] at h
      rename_i sva
      cases hb : SmtSem.eval m b <;> simp [ha, hb] at h
      rename_i svb
      cases sva <;> cases svb <;> simp [ha, hb] at h
  | array e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
      case valList vals =>
        cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  | g1 e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | g2 e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | ml e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h

theorem symConstToCek_constList {m : SmtSem.Model} {c : SymConst} {cs : List Const}
    (h : symConstToCek? m c = some (.VCon (.ConstList cs))) :
    ∃ e vals, c = .constList e ∧ SmtSem.eval m e = some (.valList vals) ∧
      semValListToConstList? vals = some cs := by
  cases c with
  | integer e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | bytes e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | string e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | bool e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | unit =>
      simp [symConstToCek?] at h
  | data e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | constList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
      case valList vals =>
        cases hcs : semValListToConstList? vals <;> simp [hcs] at h
        subst cs
        exact ⟨e, vals, rfl, he, hcs⟩
  | dataList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | pairDataList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | pairData a b =>
      simp [symConstToCek?] at h
      cases ha : SmtSem.eval m a <;> simp [ha] at h
      rename_i sva
      cases hb : SmtSem.eval m b <;> simp [ha, hb] at h
      rename_i svb
      cases sva <;> cases svb <;> simp [ha, hb] at h
  | array e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
      case valList vals =>
        cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  | g1 e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | g2 e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | ml e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h

theorem symConstToCek_array {m : SmtSem.Model} {c : SymConst} {cs : List Const}
    (h : symConstToCek? m c = some (.VCon (.ConstArray cs))) :
    ∃ e vals, c = .array e ∧ SmtSem.eval m e = some (.valList vals) ∧
      semValListToConstList? vals = some cs := by
  cases c with
  | integer e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | bytes e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | string e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | bool e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | unit =>
      simp [symConstToCek?] at h
  | data e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | constList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
      case valList vals =>
        cases hcs : semValListToConstList? vals <;> simp [hcs] at h
  | dataList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | pairDataList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | pairData a b =>
      simp [symConstToCek?] at h
      cases ha : SmtSem.eval m a <;> simp [ha] at h
      rename_i sva
      cases hb : SmtSem.eval m b <;> simp [ha, hb] at h
      rename_i svb
      cases sva <;> cases svb <;> simp [ha, hb] at h
  | array e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
      case valList vals =>
        cases hcs : semValListToConstList? vals <;> simp [hcs] at h
        subst cs
        exact ⟨e, vals, rfl, he, hcs⟩
  | g1 e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | g2 e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
  | ml e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h

theorem symConstToCek_vcon {m : SmtSem.Model} :
    ∀ {c : SymConst} {cv : CekValue},
      symConstToCek? m c = some cv → ∃ k, cv = .VCon k := by
  intro c cv h
  cases c <;> simp [symConstToCek?] at h
  case integer e =>
    cases he : SmtSem.eval m e <;> simp [he] at h
    rename_i sv
    cases sv <;> simp at h
    subst cv
    exact ⟨_, rfl⟩
  case bytes e =>
    cases he : SmtSem.eval m e <;> simp [he] at h
    rename_i sv
    cases sv <;> simp at h
    subst cv
    exact ⟨_, rfl⟩
  case string e =>
    cases he : SmtSem.eval m e <;> simp [he] at h
    rename_i sv
    cases sv <;> simp at h
    subst cv
    exact ⟨_, rfl⟩
  case bool e =>
    cases he : SmtSem.eval m e <;> simp [he] at h
    rename_i sv
    cases sv <;> simp at h
    subst cv
    exact ⟨_, rfl⟩
  case unit =>
    subst cv
    exact ⟨_, rfl⟩
  case constList e =>
    cases he : SmtSem.eval m e <;> simp [he] at h
    rename_i sv
    cases sv <;> simp at h
    rename_i xs
    cases hcs : semValListToConstList? xs <;> simp [hcs] at h
    subst cv
    exact ⟨_, rfl⟩
  case dataList e =>
    cases he : SmtSem.eval m e <;> simp [he] at h
    rename_i sv
    cases sv <;> simp at h
    subst cv
    exact ⟨_, rfl⟩
  case pairDataList e =>
    cases he : SmtSem.eval m e <;> simp [he] at h
    rename_i sv
    cases sv <;> simp at h
    subst cv
    exact ⟨_, rfl⟩
  case pairData a b =>
    cases ha : SmtSem.eval m a <;> simp [ha] at h
    rename_i sva
    cases sva <;> try simp at h
    case data da =>
      cases hb : SmtSem.eval m b <;> simp [hb] at h
      rename_i svb
      cases svb <;> simp at h
      subst cv
      exact ⟨_, rfl⟩
  case data e =>
    cases he : SmtSem.eval m e <;> simp [he] at h
    rename_i sv
    cases sv <;> simp at h
    subst cv
    exact ⟨_, rfl⟩
  case array e =>
    cases he : SmtSem.eval m e <;> simp [he] at h
    rename_i sv
    cases sv <;> simp at h
    rename_i xs
    cases hcs : semValListToConstList? xs <;> simp [hcs] at h
    subst cv
    exact ⟨_, rfl⟩
  case g1 e =>
    cases he : SmtSem.eval m e <;> simp [he] at h
    rename_i sv
    cases sv <;> simp [he] at h
    subst cv
    exact ⟨_, rfl⟩
  case g2 e =>
    cases he : SmtSem.eval m e <;> simp [he] at h
    rename_i sv
    cases sv <;> simp [he] at h
    subst cv
    exact ⟨_, rfl⟩
  case ml e =>
    cases he : SmtSem.eval m e <;> simp [he] at h
    rename_i sv
    cases sv <;> simp [he] at h
    subst cv
    exact ⟨_, rfl⟩

theorem bindOut_active_ok {m : SmtSem.Model} {xs : List Outcome} {k : SymVal → List Outcome}
    {out : Outcome} {sv : SymVal} {cv : CekValue}
    (hmem : out ∈ bindOut xs k)
    (hok : outcomeOkSym? m out = some (sv, cv)) :
    ∃ pc v inner,
      Outcome.ok pc v ∈ xs ∧ pcHolds m pc = true ∧ inner ∈ k v ∧
      outcomeOkSym? m inner = some (sv, cv) := by
  simp [bindOut, List.mem_flatMap] at hmem
  rcases hmem with ⟨outer, houter, hout⟩
  cases outer with
  | ok pc v =>
      simp at hout
      rcases hout with ⟨inner, hinner, rfl⟩
      have hg := outcomeOkSym_guard hok
      exact ⟨pc, v, inner, houter, hg.1, hinner, hg.2⟩
  | error pc =>
      simp at hout
      subst out
      simp [outcomeOkSym?] at hok
  | timeout pc =>
      simp at hout
      subst out
      simp [outcomeOkSym?] at hok

theorem bindOut_active_error {m : SmtSem.Model} {xs : List Outcome} {k : SymVal → List Outcome}
    {out : Outcome}
    (hmem : out ∈ bindOut xs k)
    (herr : outcomeErrorActive m out = true) :
    (∃ pc, Outcome.error pc ∈ xs ∧ pcHolds m pc = true) ∨
    (∃ pc v inner, Outcome.ok pc v ∈ xs ∧ pcHolds m pc = true ∧ inner ∈ k v ∧
      outcomeErrorActive m inner = true) := by
  simp [bindOut, List.mem_flatMap] at hmem
  rcases hmem with ⟨outer, houter, hout⟩
  cases outer with
  | ok pc v =>
      simp at hout
      rcases hout with ⟨inner, hinner, rfl⟩
      have hg := outcomeErrorActive_guard herr
      exact Or.inr ⟨pc, v, inner, houter, hg.1, hinner, hg.2⟩
  | error pc =>
      simp at hout
      subst out
      exact Or.inl ⟨pc, houter, by simpa [outcomeErrorActive, pcHolds] using herr⟩
  | timeout pc =>
      simp at hout
      subst out
      simp [outcomeErrorActive] at herr

set_option linter.unusedSimpArgs false in
theorem bindOut_path_ok {m : SmtSem.Model} {xs : List Outcome} {k : SymVal → List Outcome}
    {pc : SExpr} {v : SymVal}
    (hmem : Outcome.ok pc v ∈ bindOut xs k)
    (hpc : pcHolds m pc = true) :
    ∃ outerPc outerV innerPc,
      Outcome.ok outerPc outerV ∈ xs ∧ Outcome.ok innerPc v ∈ k outerV ∧
      pc = SExpr.and outerPc innerPc ∧
      pcHolds m outerPc = true ∧ pcHolds m innerPc = true := by
  simp [bindOut, List.mem_flatMap] at hmem
  rcases hmem with ⟨outer, houter, hout⟩
  cases outer with
  | ok outerPc outerV =>
      simp [Outcome.guard] at hout
      rcases hout with ⟨inner, hinner, hguard⟩
      cases inner with
      | ok innerPc innerV =>
          simp [Outcome.guard] at hguard
          rcases hguard with ⟨rfl, rfl⟩
          have hp := (Moist.SMT.Semantics.evalBoolIs_and_true m outerPc innerPc).mp hpc
          exact ⟨outerPc, outerV, innerPc, houter, hinner, rfl, hp.1, hp.2⟩
      | error innerPc => simp [Outcome.guard] at hguard
      | timeout innerPc => simp [Outcome.guard] at hguard
  | error outerPc =>
      simp [Outcome.guard] at hout
  | timeout outerPc =>
      simp [Outcome.guard] at hout

set_option linter.unusedSimpArgs false in
theorem bindOut_path_error {m : SmtSem.Model} {xs : List Outcome} {k : SymVal → List Outcome}
    {pc : SExpr}
    (hmem : Outcome.error pc ∈ bindOut xs k)
    (hpc : pcHolds m pc = true) :
    (Outcome.error pc ∈ xs ∧ pcHolds m pc = true) ∨
    (∃ outerPc outerV innerPc,
      Outcome.ok outerPc outerV ∈ xs ∧ Outcome.error innerPc ∈ k outerV ∧
      pc = SExpr.and outerPc innerPc ∧
      pcHolds m outerPc = true ∧ pcHolds m innerPc = true) := by
  simp [bindOut, List.mem_flatMap] at hmem
  rcases hmem with ⟨outer, houter, hout⟩
  cases outer with
  | ok outerPc outerV =>
      simp [Outcome.guard] at hout
      rcases hout with ⟨inner, hinner, hguard⟩
      cases inner with
      | ok innerPc innerV => simp [Outcome.guard] at hguard
      | error innerPc =>
          simp [Outcome.guard] at hguard
          subst pc
          have hp := (Moist.SMT.Semantics.evalBoolIs_and_true m outerPc innerPc).mp hpc
          exact Or.inr ⟨outerPc, outerV, innerPc, houter, hinner, rfl, hp.1, hp.2⟩
      | timeout innerPc => simp [Outcome.guard] at hguard
  | error outerPc =>
      simp [Outcome.guard] at hout
      subst pc
      exact Or.inl ⟨houter, hpc⟩
  | timeout outerPc =>
      simp [Outcome.guard] at hout

set_option linter.unusedSimpArgs false in
theorem checked2_path_ok {α} {m : SmtSem.Model} {p : Proj α}
    {mk : α → List Outcome} {pc : SExpr} {v : SymVal}
    (hmem : Outcome.ok pc v ∈ checked2 p mk)
    (hpc : pcHolds m pc = true) :
    ∃ innerPc,
      Outcome.ok innerPc v ∈ mk p.val ∧
      pc = SExpr.and p.guard innerPc ∧
      pcHolds m p.guard = true ∧
      pcHolds m innerPc = true := by
  unfold checked2 at hmem
  rcases List.mem_append.mp hmem with hmap | herr
  · rcases List.mem_map.mp hmap with ⟨inner, hinner, hguard⟩
    cases inner with
    | ok innerPc innerV =>
        simp [Outcome.guard] at hguard
        rcases hguard with ⟨rfl, rfl⟩
        have hp :=
          (Moist.SMT.Semantics.evalBoolIs_and_true m p.guard innerPc).mp hpc
        exact ⟨innerPc, hinner, rfl, hp.1, hp.2⟩
    | error innerPc =>
        simp [Outcome.guard] at hguard
    | timeout innerPc =>
        simp [Outcome.guard] at hguard
  · simp at herr

theorem checked2_active_error {α} {m : SmtSem.Model} {p : Proj α}
    {mk : α → List Outcome} {out : Outcome}
    (hmem : out ∈ checked2 p mk)
    (herr : outcomeErrorActive m out = true) :
    (∃ inner,
      inner ∈ mk p.val ∧ pcHolds m p.guard = true ∧
        outcomeErrorActive m inner = true) ∨
    pcHolds m (SExpr.not p.guard) = true := by
  unfold checked2 at hmem
  rcases List.mem_append.mp hmem with hmap | htail
  · rcases List.mem_map.mp hmap with ⟨inner, hinner, hguard⟩
    cases hguard
    have hg := outcomeErrorActive_guard herr
    exact Or.inl ⟨inner, hinner, hg.1, hg.2⟩
  · simp only [List.mem_singleton] at htail
    cases htail
    exact Or.inr (by simpa [outcomeErrorActive] using herr)

theorem branchOutcomes_active_ok {m : SmtSem.Model}
    {branches : List (SExpr × List Outcome)} {extraErrors : List SExpr}
    {out : Outcome} {sv : SymVal} {cv : CekValue}
    (hmem : out ∈ branchOutcomes branches extraErrors)
    (hok : outcomeOkSym? m out = some (sv, cv)) :
    ∃ g os inner,
      (g, os) ∈ branches ∧ pcHolds m g = true ∧ inner ∈ os ∧
      outcomeOkSym? m inner = some (sv, cv) := by
  induction branches with
  | nil =>
      simp [branchOutcomes] at hmem
      rcases hmem with ⟨g, hg, rfl⟩
      simp [outcomeOkSym?] at hok
  | cons br branches ih =>
      rcases br with ⟨g, os⟩
      simp [branchOutcomes, mapPc, List.mem_append, List.mem_map] at hmem
      rcases hmem with hthis | hrest
      · rcases hthis with ⟨inner, hinnerMem, hguard⟩
        subst out
        have hg := outcomeOkSym_guard hok
        exact ⟨g, os, inner, by simp, hg.1, hinnerMem, hg.2⟩
      · have htail : out ∈ branchOutcomes branches extraErrors := by
          simpa [branchOutcomes, mapPc, List.mem_append, List.mem_flatMap,
            List.mem_map] using hrest
        obtain ⟨g', os', inner, hbr, hg, hinner, hok'⟩ := ih htail
        exact ⟨g', os', inner, by simp [hbr], hg, hinner, hok'⟩

theorem branchOutcomes_active_error {m : SmtSem.Model}
    {branches : List (SExpr × List Outcome)} {extraErrors : List SExpr}
    {out : Outcome}
    (hmem : out ∈ branchOutcomes branches extraErrors)
    (herr : outcomeErrorActive m out = true) :
    (∃ g os inner,
      (g, os) ∈ branches ∧ pcHolds m g = true ∧ inner ∈ os ∧
      outcomeErrorActive m inner = true) ∨
    (∃ g, g ∈ extraErrors ∧ pcHolds m g = true) := by
  induction branches with
  | nil =>
      simp [branchOutcomes] at hmem
      rcases hmem with ⟨g, hg, rfl⟩
      exact Or.inr ⟨g, hg, by simpa [outcomeErrorActive, pcHolds] using herr⟩
  | cons br branches ih =>
      rcases br with ⟨g, os⟩
      simp [branchOutcomes, mapPc, List.mem_append, List.mem_map] at hmem
      rcases hmem with hthis | hrest
      · rcases hthis with ⟨inner, hinnerMem, hguard⟩
        subst out
        have hg := outcomeErrorActive_guard herr
        exact Or.inl ⟨g, os, inner, by simp, hg.1, hinnerMem, hg.2⟩
      · have htail : out ∈ branchOutcomes branches extraErrors := by
          simpa [branchOutcomes, mapPc, List.mem_append, List.mem_flatMap,
            List.mem_map] using hrest
        rcases ih htail with hbranch | hextra
        · rcases hbranch with ⟨g', os', inner, hbr, hg, hinner, herr'⟩
          exact Or.inl ⟨g', os', inner, by simp [hbr], hg, hinner, herr'⟩
        · exact Or.inr hextra

theorem branchOutcomes_path_ok {m : SmtSem.Model}
    {branches : List (SExpr × List Outcome)} {extraErrors : List SExpr}
    {pc : SExpr} {v : SymVal}
    (hmem : Outcome.ok pc v ∈ branchOutcomes branches extraErrors)
    (hpc : pcHolds m pc = true) :
    ∃ g os innerPc,
      (g, os) ∈ branches ∧ Outcome.ok innerPc v ∈ os ∧
      pc = SExpr.and g innerPc ∧ pcHolds m g = true ∧
      pcHolds m innerPc = true := by
  induction branches with
  | nil =>
      simp [branchOutcomes] at hmem
  | cons br branches ih =>
      rcases br with ⟨g, os⟩
      simp [branchOutcomes, mapPc, List.mem_append, List.mem_map] at hmem
      rcases hmem with hthis | hrest
      · rcases hthis with ⟨inner, hinnerMem, hguard⟩
        cases inner with
        | ok innerPc innerV =>
            simp [Outcome.guard] at hguard
            rcases hguard with ⟨rfl, rfl⟩
            have hp := (Moist.SMT.Semantics.evalBoolIs_and_true m g innerPc).mp hpc
            exact ⟨g, os, innerPc, by simp, hinnerMem, rfl, hp.1, hp.2⟩
        | error innerPc =>
            simp [Outcome.guard] at hguard
        | timeout innerPc =>
            simp [Outcome.guard] at hguard
      · have htail : Outcome.ok pc v ∈ branchOutcomes branches extraErrors := by
          simpa [branchOutcomes, mapPc, List.mem_append, List.mem_flatMap,
            List.mem_map] using hrest
        obtain ⟨g', os', innerPc, hbr, hinner, hpcEq, hg, hi⟩ := ih htail
        exact ⟨g', os', innerPc, by simp [hbr], hinner, hpcEq, hg, hi⟩

theorem symEnvToCek_extend {m : SmtSem.Model} {ρ : List SymVal} {env : CekEnv}
    {v : SymVal} {cv : CekValue}
    (henv : symEnvToCek? m ρ = some env)
    (hv : symValToCek? m v = some cv) :
    symEnvToCek? m (extendEnv ρ v) = some (env.extend cv) := by
  simp [extendEnv, symEnvToCek?, hv, henv, Moist.CEK.CekEnv.extend]

theorem symValListToCekList_cons {m : SmtSem.Model} {v : SymVal} {vs : List SymVal}
    {cv : CekValue} {cvs : List CekValue}
    (hv : symValToCek? m v = some cv)
    (hvs : symValListToCekList? m vs = some cvs) :
    symValListToCekList? m (v :: vs) = some (cv :: cvs) := by
  simp [symValListToCekList?, hv, hvs]

theorem asBool_true_to_cek {m : SmtSem.Model} {v : SymVal}
    (hg : pcHolds m (asBool v).guard = true)
    (hv : SmtSem.evalBoolIs m (asBool v).val true = true) :
    symValToCek? m v = some (.VCon (.Bool true)) := by
  cases v with
  | const c =>
      cases c <;> simp [asBool, valueProj, Proj.pure, Proj.fail, pcHolds] at hg hv ⊢
      case bool e =>
        have heval : SmtSem.eval m e = some (.bool true) :=
          (Moist.SMT.Semantics.evalBoolIs_true_eq m e).mp hv
        simp [symValToCek?, symConstToCek?, heval]
  | dyn e =>
      simp [asBool, valueProj, pcHolds] at hg hv ⊢
      obtain ⟨b, he⟩ := Moist.SMT.Semantics.evalBoolIs_isVBool_true hg
      have hun := Moist.SMT.Semantics.eval_unVBool_of (m := m) (e := e) he
      have hvEval : SmtSem.eval m (.app "unVBool" [e]) = some (.bool true) :=
        (Moist.SMT.Semantics.evalBoolIs_true_eq m (.app "unVBool" [e])).mp hv
      change Moist.SMT.Semantics.eval m (.app "unVBool" [e]) = some (.bool true) at hvEval
      rw [hun] at hvEval
      injection hvEval with hbv
      cases hbv
      simp [symValToCek?, he, semValToCek?, semValToConst?]
  | pair a b =>
      simp [asBool, valueProj, Proj.fail, pcHolds] at hg
  | constr tag fields =>
      simp [asBool, valueProj, Proj.fail, pcHolds] at hg
  | lam body ρ =>
      simp [asBool, valueProj, Proj.fail, pcHolds] at hg
  | delay body ρ =>
      simp [asBool, valueProj, Proj.fail, pcHolds] at hg
  | builtin b args ea =>
      simp [asBool, valueProj, Proj.fail, pcHolds] at hg

theorem asBool_false_to_cek {m : SmtSem.Model} {v : SymVal}
    (hg : pcHolds m (asBool v).guard = true)
    (hv : SmtSem.evalBoolIs m (asBool v).val false = true) :
    symValToCek? m v = some (.VCon (.Bool false)) := by
  cases v with
  | const c =>
      cases c <;> simp [asBool, valueProj, Proj.pure, Proj.fail, pcHolds] at hg hv ⊢
      case bool e =>
        have heval : SmtSem.eval m e = some (.bool false) :=
          (evalBoolIs_false_eq (m := m) (e := e)).mp hv
        simp [symValToCek?, symConstToCek?, heval]
  | dyn e =>
      simp [asBool, valueProj, pcHolds] at hg hv ⊢
      obtain ⟨b, he⟩ := Moist.SMT.Semantics.evalBoolIs_isVBool_true hg
      have hun := Moist.SMT.Semantics.eval_unVBool_of (m := m) (e := e) he
      have hvEval : SmtSem.eval m (.app "unVBool" [e]) = some (.bool false) :=
        (evalBoolIs_false_eq (m := m) (e := .app "unVBool" [e])).mp hv
      change Moist.SMT.Semantics.eval m (.app "unVBool" [e]) = some (.bool false) at hvEval
      rw [hun] at hvEval
      injection hvEval with hbv
      cases hbv
      simp [symValToCek?, he, semValToCek?, semValToConst?]
  | pair a b =>
      simp [asBool, valueProj, Proj.fail, pcHolds] at hg
  | constr tag fields =>
      simp [asBool, valueProj, Proj.fail, pcHolds] at hg
  | lam body ρ =>
      simp [asBool, valueProj, Proj.fail, pcHolds] at hg
  | delay body ρ =>
      simp [asBool, valueProj, Proj.fail, pcHolds] at hg
  | builtin b args ea =>
      simp [asBool, valueProj, Proj.fail, pcHolds] at hg

theorem asBool_guard_of_cek {m : SmtSem.Model} {v : SymVal} {b : Bool}
    (hv : symValToCek? m v = some (.VCon (.Bool b))) :
    pcHolds m (asBool v).guard = true := by
  cases v with
  | const c =>
      obtain ⟨e, hc, _he⟩ :=
        symConstToCek_bool (by simpa [symValToCek?] using hv)
      subst c
      simp [asBool, Proj.pure, pcHolds]
  | dyn e =>
      simp [asBool, valueProj, pcHolds, symValToCek?] at hv ⊢
      cases he : SmtSem.eval m e <;> simp [he] at hv
      rename_i sv
      cases sv <;> simp at hv
      case val val =>
        have hval := semValToCek_bool hv
        subst val
        exact Moist.SMT.Semantics.evalBoolIs_isVBool_of he
  | pair a b' =>
      simp [symValToCek?] at hv
      cases ha : symValToCek? m a <;> simp [ha] at hv
      rename_i cva
      cases hb : symValToCek? m b' <;> simp [hb] at hv
      rename_i cvb
      cases cva <;> cases cvb <;> simp at hv
  | constr tag fields =>
      simp [symValToCek?] at hv
      cases htag : SmtSem.eval m tag <;> simp [htag] at hv
      rename_i sv
      cases sv <;> simp [htag] at hv
      rename_i i
      by_cases hneg : i < 0
      · exact False.elim ((Int.not_le).mpr hneg hv.1)
      · cases hfields : symValListToCekList? m fields <;> simp [hfields] at hv
  | lam body ρ =>
      simp [symValToCek?] at hv
      cases henv : symEnvToCek? m ρ <;> simp [henv] at hv
  | delay body ρ =>
      simp [symValToCek?] at hv
      cases henv : symEnvToCek? m ρ <;> simp [henv] at hv
  | builtin bfn args ea =>
      simp [symValToCek?] at hv
      cases hargs : symValListToCekList? m args <;> simp [hargs] at hv

theorem symValListToCekList_singleton {m : SmtSem.Model} {v : SymVal}
    {cargs : List CekValue}
    (h : symValListToCekList? m [v] = some cargs) :
    ∃ cv, symValToCek? m v = some cv ∧ cargs = [cv] := by
  unfold symValListToCekList? at h
  cases hv : symValToCek? m v with
  | none =>
      simp [hv] at h
  | some cv =>
      simp [hv, symValListToCekList?] at h
      exact ⟨cv, rfl, h.symm⟩

theorem symValListToCekList_pair {m : SmtSem.Model} {a b : SymVal}
    {cargs : List CekValue}
    (h : symValListToCekList? m [b, a] = some cargs) :
    ∃ cb ca,
      symValToCek? m b = some cb ∧
      symValToCek? m a = some ca ∧
      cargs = [cb, ca] := by
  simp [symValListToCekList?] at h
  cases hb : symValToCek? m b <;> simp [hb] at h
  cases ha : symValToCek? m a <;> simp [ha] at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

theorem symValListToCekList_length {m : SmtSem.Model}
    {args : List SymVal} {cargs : List CekValue}
    (h : symValListToCekList? m args = some cargs) :
    cargs.length = args.length := by
  induction args generalizing cargs with
  | nil =>
      simp [symValListToCekList?] at h
      subst cargs
      rfl
  | cons v vs ih =>
      simp [symValListToCekList?] at h
      cases hv : symValToCek? m v <;> simp [hv] at h
      cases hvs : symValListToCekList? m vs <;> simp [hvs] at h
      subst cargs
      simp [ih hvs]

theorem symValListToCekList_triple {m : SmtSem.Model} {a b c : SymVal}
    {cargs : List CekValue}
    (h : symValListToCekList? m [c, b, a] = some cargs) :
    ∃ cc cb ca,
      symValToCek? m c = some cc ∧
      symValToCek? m b = some cb ∧
      symValToCek? m a = some ca ∧
      cargs = [cc, cb, ca] := by
  simp [symValListToCekList?] at h
  cases hc : symValToCek? m c <;> simp [hc] at h
  cases hb : symValToCek? m b <;> simp [hb] at h
  cases ha : symValToCek? m a <;> simp [ha] at h
  exact ⟨_, _, _, rfl, rfl, rfl, h.symm⟩

theorem symValListToCekList_six {m : SmtSem.Model} {a b c d e f : SymVal}
    {cargs : List CekValue}
    (h : symValListToCekList? m [f, e, d, c, b, a] = some cargs) :
    ∃ cf ce cd cc cb ca,
      symValToCek? m f = some cf ∧
      symValToCek? m e = some ce ∧
      symValToCek? m d = some cd ∧
      symValToCek? m c = some cc ∧
      symValToCek? m b = some cb ∧
      symValToCek? m a = some ca ∧
      cargs = [cf, ce, cd, cc, cb, ca] := by
  simp [symValListToCekList?] at h
  cases hf : symValToCek? m f <;> simp [hf] at h
  cases he : symValToCek? m e <;> simp [he] at h
  cases hd : symValToCek? m d <;> simp [hd] at h
  cases hc : symValToCek? m c <;> simp [hc] at h
  cases hb : symValToCek? m b <;> simp [hb] at h
  cases ha : symValToCek? m a <;> simp [ha] at h
  exact ⟨_, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, h.symm⟩

theorem asInt_sound {m : SmtSem.Model} {v : SymVal} {cv : CekValue}
    (hv : symValToCek? m v = some cv)
    (hg : pcHolds m (asInt v).guard = true) :
    ∃ i, cv = .VCon (.Integer i) ∧
      SmtSem.eval m (asInt v).val = some (.int i) := by
  cases v with
  | const c =>
      cases c <;> simp [asInt, valueProj, Proj.pure, Proj.fail, pcHolds,
        symValToCek?, symConstToCek?] at hv hg ⊢
      case integer e =>
        cases he : SmtSem.eval m e with
        | none =>
            simp [he] at hv
        | some sv =>
            cases sv <;> simp [he] at hv
            case int i =>
              subst cv
              exact ⟨i, rfl, by simpa [he]⟩
  | dyn e =>
      simp [asInt, valueProj, pcHolds, symValToCek?] at hv hg ⊢
      obtain ⟨i, he⟩ := Moist.SMT.Semantics.evalBoolIs_isVInt_true hg
      have hun := Moist.SMT.Semantics.eval_unVInt_of (m := m) (e := e) he
      simp [he, semValToCek?, semValToConst?] at hv
      subst cv
      exact ⟨i, rfl, hun⟩
  | pair a b =>
      simp [asInt, valueProj, Proj.fail, pcHolds] at hg
  | constr tag fields =>
      simp [asInt, valueProj, Proj.fail, pcHolds] at hg
  | lam body ρ =>
      simp [asInt, valueProj, Proj.fail, pcHolds] at hg
  | delay body ρ =>
      simp [asInt, valueProj, Proj.fail, pcHolds] at hg
  | builtin b args ea =>
      simp [asInt, valueProj, Proj.fail, pcHolds] at hg

theorem asInt_guard_of_cek {m : SmtSem.Model} {v : SymVal} {i : Int}
    (hv : symValToCek? m v = some (.VCon (.Integer i))) :
    pcHolds m (asInt v).guard = true := by
  cases v with
  | const c =>
      obtain ⟨e, hc, _he⟩ :=
        symConstToCek_integer (by simpa [symValToCek?] using hv)
      subst c
      simp [asInt, Proj.pure, pcHolds]
  | dyn e =>
      simp [asInt, valueProj, pcHolds, symValToCek?] at hv ⊢
      cases he : SmtSem.eval m e <;> simp [he] at hv
      rename_i sv
      cases sv <;> simp at hv
      case val val =>
        have hval := semValToCek_integer hv
        subst val
        exact Moist.SMT.Semantics.evalBoolIs_isVInt_of he
  | pair a b =>
      simp [symValToCek?] at hv
      cases ha : symValToCek? m a <;> simp [ha] at hv
      rename_i cva
      cases hb : symValToCek? m b <;> simp [hb] at hv
      rename_i cvb
      cases cva <;> cases cvb <;> simp at hv
  | constr tag fields =>
      simp [symValToCek?] at hv
      cases htag : SmtSem.eval m tag <;> simp [htag] at hv
      rename_i sv
      cases sv <;> simp [htag] at hv
      rename_i i'
      by_cases hneg : i' < 0
      · exact False.elim ((Int.not_le).mpr hneg hv.1)
      · cases hfields : symValListToCekList? m fields <;> simp [hfields] at hv
  | lam body ρ =>
      simp [symValToCek?] at hv
      cases henv : symEnvToCek? m ρ <;> simp [henv] at hv
  | delay body ρ =>
      simp [symValToCek?] at hv
      cases henv : symEnvToCek? m ρ <;> simp [henv] at hv
  | builtin b args ea =>
      simp [symValToCek?] at hv
      cases hargs : symValListToCekList? m args <;> simp [hargs] at hv

theorem asBytes_sound {m : SmtSem.Model} {v : SymVal} {cv : CekValue}
    (hv : symValToCek? m v = some cv)
    (hg : pcHolds m (asBytes v).guard = true) :
    ∃ bs, cv = .VCon (.ByteString bs) ∧
      SmtSem.eval m (asBytes v).val = some (.bytes bs) := by
  cases v with
  | const c =>
      cases c <;> simp [asBytes, valueProj, Proj.pure, Proj.fail, pcHolds,
        symValToCek?, symConstToCek?] at hv hg ⊢
      case bytes e =>
        cases he : SmtSem.eval m e with
        | none =>
            simp [he] at hv
        | some sv =>
            cases sv <;> simp [he] at hv
            case bytes bs =>
              subst cv
              exact ⟨bs, rfl, by simpa [he]⟩
  | dyn e =>
      simp [asBytes, valueProj, pcHolds, symValToCek?] at hv hg ⊢
      obtain ⟨bs, he⟩ := Moist.SMT.Semantics.evalBoolIs_isVBytes_true hg
      have hun := Moist.SMT.Semantics.eval_unVBytes_of (m := m) (e := e) he
      simp [he, semValToCek?, semValToConst?] at hv
      subst cv
      exact ⟨bs, rfl, hun⟩
  | pair a b =>
      simp [asBytes, valueProj, Proj.fail, pcHolds] at hg
  | constr tag fields =>
      simp [asBytes, valueProj, Proj.fail, pcHolds] at hg
  | lam body ρ =>
      simp [asBytes, valueProj, Proj.fail, pcHolds] at hg
  | delay body ρ =>
      simp [asBytes, valueProj, Proj.fail, pcHolds] at hg
  | builtin b args ea =>
      simp [asBytes, valueProj, Proj.fail, pcHolds] at hg

theorem asBytes_guard_of_cek {m : SmtSem.Model} {v : SymVal} {bs : ByteArray}
    (hv : symValToCek? m v = some (.VCon (.ByteString bs))) :
    pcHolds m (asBytes v).guard = true := by
  cases v with
  | const c =>
      obtain ⟨e, hc, _he⟩ :=
        symConstToCek_bytes (by simpa [symValToCek?] using hv)
      subst c
      simp [asBytes, Proj.pure, pcHolds]
  | dyn e =>
      simp [asBytes, valueProj, pcHolds, symValToCek?] at hv ⊢
      cases he : SmtSem.eval m e <;> simp [he] at hv
      rename_i sv
      cases sv <;> simp at hv
      case val val =>
        have hval := semValToCek_bytes hv
        subst val
        exact Moist.SMT.Semantics.evalBoolIs_isVBytes_of he
  | pair a b =>
      simp [symValToCek?] at hv
      cases ha : symValToCek? m a <;> simp [ha] at hv
      rename_i cva
      cases hb : symValToCek? m b <;> simp [hb] at hv
      rename_i cvb
      cases cva <;> cases cvb <;> simp at hv
  | constr tag fields =>
      simp [symValToCek?] at hv
      cases htag : SmtSem.eval m tag <;> simp [htag] at hv
      rename_i sv
      cases sv <;> simp [htag] at hv
      rename_i i
      by_cases hneg : i < 0
      · exact False.elim ((Int.not_le).mpr hneg hv.1)
      · cases hfields : symValListToCekList? m fields <;> simp [hfields] at hv
  | lam body ρ =>
      simp [symValToCek?] at hv
      cases henv : symEnvToCek? m ρ <;> simp [henv] at hv
  | delay body ρ =>
      simp [symValToCek?] at hv
      cases henv : symEnvToCek? m ρ <;> simp [henv] at hv
  | builtin b args ea =>
      simp [symValToCek?] at hv
      cases hargs : symValListToCekList? m args <;> simp [hargs] at hv

theorem asString_sound {m : SmtSem.Model} {v : SymVal} {cv : CekValue}
    (hv : symValToCek? m v = some cv)
    (hg : pcHolds m (asString v).guard = true) :
    ∃ s, cv = .VCon (.String s) ∧
      SmtSem.eval m (asString v).val = some (.string s) := by
  cases v with
  | const c =>
      cases c <;> simp [asString, valueProj, Proj.pure, Proj.fail, pcHolds,
        symValToCek?, symConstToCek?] at hv hg ⊢
      case string e =>
        cases he : SmtSem.eval m e with
        | none =>
            simp [he] at hv
        | some sv =>
            cases sv <;> simp [he] at hv
            case string s =>
              subst cv
              exact ⟨s, rfl, by simpa [he]⟩
  | dyn e =>
      simp [asString, valueProj, pcHolds, symValToCek?] at hv hg ⊢
      obtain ⟨s, he⟩ := Moist.SMT.Semantics.evalBoolIs_isVString_true hg
      have hun := Moist.SMT.Semantics.eval_unVString_of (m := m) (e := e) he
      simp [he, semValToCek?, semValToConst?] at hv
      subst cv
      exact ⟨s, rfl, hun⟩
  | pair a b =>
      simp [asString, valueProj, Proj.fail, pcHolds] at hg
  | constr tag fields =>
      simp [asString, valueProj, Proj.fail, pcHolds] at hg
  | lam body ρ =>
      simp [asString, valueProj, Proj.fail, pcHolds] at hg
  | delay body ρ =>
      simp [asString, valueProj, Proj.fail, pcHolds] at hg
  | builtin b args ea =>
      simp [asString, valueProj, Proj.fail, pcHolds] at hg

theorem asString_guard_of_cek {m : SmtSem.Model} {v : SymVal} {s : String}
    (hv : symValToCek? m v = some (.VCon (.String s))) :
    pcHolds m (asString v).guard = true := by
  cases v with
  | const c =>
      obtain ⟨e, hc, _he⟩ :=
        symConstToCek_string (by simpa [symValToCek?] using hv)
      subst c
      simp [asString, Proj.pure, pcHolds]
  | dyn e =>
      simp [asString, valueProj, pcHolds, symValToCek?] at hv ⊢
      cases he : SmtSem.eval m e <;> simp [he] at hv
      rename_i sv
      cases sv <;> simp at hv
      case val val =>
        have hval := semValToCek_string hv
        subst val
        exact Moist.SMT.Semantics.evalBoolIs_isVString_of he
  | pair a b =>
      simp [symValToCek?] at hv
      cases ha : symValToCek? m a <;> simp [ha] at hv
      rename_i cva
      cases hb : symValToCek? m b <;> simp [hb] at hv
      rename_i cvb
      cases cva <;> cases cvb <;> simp at hv
  | constr tag fields =>
      simp [symValToCek?] at hv
      cases htag : SmtSem.eval m tag <;> simp [htag] at hv
      rename_i sv
      cases sv <;> simp [htag] at hv
      rename_i i
      by_cases hneg : i < 0
      · exact False.elim ((Int.not_le).mpr hneg hv.1)
      · cases hfields : symValListToCekList? m fields <;> simp [hfields] at hv
  | lam body ρ =>
      simp [symValToCek?] at hv
      cases henv : symEnvToCek? m ρ <;> simp [henv] at hv
  | delay body ρ =>
      simp [symValToCek?] at hv
      cases henv : symEnvToCek? m ρ <;> simp [henv] at hv
  | builtin b args ea =>
      simp [symValToCek?] at hv
      cases hargs : symValListToCekList? m args <;> simp [hargs] at hv

theorem asData_sound {m : SmtSem.Model} {v : SymVal} {cv : CekValue}
    (hv : symValToCek? m v = some cv)
    (hg : pcHolds m (asData v).guard = true) :
    ∃ d, cv = .VCon (.Data d) ∧
      SmtSem.eval m (asData v).val = some (.data d) := by
  cases v with
  | const c =>
      cases c <;> simp [asData, valueProj, Proj.pure, Proj.fail, pcHolds,
        symValToCek?, symConstToCek?] at hv hg ⊢
      case data e =>
        cases he : SmtSem.eval m e with
        | none =>
            simp [he] at hv
        | some sv =>
            cases sv <;> simp [he] at hv
            case data d =>
              subst cv
              exact ⟨d, rfl, by simpa [he]⟩
  | dyn e =>
      simp [asData, valueProj, pcHolds, symValToCek?] at hv hg ⊢
      obtain ⟨d, he⟩ := Moist.SMT.Semantics.evalBoolIs_isVData_true hg
      have hun := Moist.SMT.Semantics.eval_unVData_of (m := m) (e := e) he
      simp [he, semValToCek?, semValToConst?] at hv
      subst cv
      exact ⟨d, rfl, hun⟩
  | pair a b =>
      simp [asData, valueProj, Proj.fail, pcHolds] at hg
  | constr tag fields =>
      simp [asData, valueProj, Proj.fail, pcHolds] at hg
  | lam body ρ =>
      simp [asData, valueProj, Proj.fail, pcHolds] at hg
  | delay body ρ =>
      simp [asData, valueProj, Proj.fail, pcHolds] at hg
  | builtin b args ea =>
      simp [asData, valueProj, Proj.fail, pcHolds] at hg

theorem asData_guard_of_cek {m : SmtSem.Model} {v : SymVal} {d : Plutus.Data}
    (hv : symValToCek? m v = some (.VCon (.Data d))) :
    pcHolds m (asData v).guard = true := by
  cases v with
  | const c =>
      obtain ⟨e, hc, _he⟩ :=
        symConstToCek_data (by simpa [symValToCek?] using hv)
      subst c
      simp [asData, Proj.pure, pcHolds]
  | dyn e =>
      simp [asData, valueProj, pcHolds, symValToCek?] at hv ⊢
      cases he : SmtSem.eval m e <;> simp [he] at hv
      rename_i sv
      cases sv <;> simp at hv
      case val val =>
        have hval := semValToCek_data hv
        subst val
        exact Moist.SMT.Semantics.evalBoolIs_isVData_of he
  | pair a b =>
      simp [symValToCek?] at hv
      cases ha : symValToCek? m a <;> simp [ha] at hv
      rename_i cva
      cases hb : symValToCek? m b <;> simp [hb] at hv
      rename_i cvb
      cases cva <;> cases cvb <;> simp at hv
  | constr tag fields =>
      simp [symValToCek?] at hv
      cases htag : SmtSem.eval m tag <;> simp [htag] at hv
      rename_i sv
      cases sv <;> simp [htag] at hv
      rename_i i
      by_cases hneg : i < 0
      · exact False.elim ((Int.not_le).mpr hneg hv.1)
      · cases hfields : symValListToCekList? m fields <;> simp [hfields] at hv
  | lam body ρ =>
      simp [symValToCek?] at hv
      cases henv : symEnvToCek? m ρ <;> simp [henv] at hv
  | delay body ρ =>
      simp [symValToCek?] at hv
      cases henv : symEnvToCek? m ρ <;> simp [henv] at hv
  | builtin b args ea =>
      simp [symValToCek?] at hv
      cases hargs : symValListToCekList? m args <;> simp [hargs] at hv

theorem asDataList_sound {m : SmtSem.Model} {v : SymVal} {cv : CekValue}
    (hv : symValToCek? m v = some cv)
    (hg : pcHolds m (asDataList v).guard = true) :
    ∃ xs, cv = .VCon (.ConstDataList xs) ∧
      SmtSem.eval m (asDataList v).val = some (.dataList xs) := by
  cases v with
  | const c =>
      cases c <;> simp [asDataList, valueProj, Proj.pure, Proj.fail, pcHolds,
        symValToCek?, symConstToCek?] at hv hg ⊢
      case dataList e =>
        cases he : SmtSem.eval m e with
        | none =>
            simp [he] at hv
        | some sv =>
            cases sv <;> simp [he] at hv
            case dataList xs =>
              subst cv
              exact ⟨xs, rfl, by simpa [he]⟩
  | dyn e =>
      simp [asDataList, valueProj, pcHolds, symValToCek?] at hv hg ⊢
      obtain ⟨xs, he⟩ := Moist.SMT.Semantics.evalBoolIs_isVDataList_true hg
      have hun := Moist.SMT.Semantics.eval_unVDataList_of (m := m) (e := e) he
      simp [he, semValToCek?, semValToConst?] at hv
      subst cv
      exact ⟨xs, rfl, hun⟩
  | pair a b =>
      simp [asDataList, valueProj, Proj.fail, pcHolds] at hg
  | constr tag fields =>
      simp [asDataList, valueProj, Proj.fail, pcHolds] at hg
  | lam body ρ =>
      simp [asDataList, valueProj, Proj.fail, pcHolds] at hg
  | delay body ρ =>
      simp [asDataList, valueProj, Proj.fail, pcHolds] at hg
  | builtin b args ea =>
      simp [asDataList, valueProj, Proj.fail, pcHolds] at hg

theorem asDataList_guard_of_cek {m : SmtSem.Model} {v : SymVal} {xs : List Plutus.Data}
    (hv : symValToCek? m v = some (.VCon (.ConstDataList xs))) :
    pcHolds m (asDataList v).guard = true := by
  cases v with
  | const c =>
      obtain ⟨e, hc, _he⟩ :=
        symConstToCek_dataList (by simpa [symValToCek?] using hv)
      subst c
      simp [asDataList, Proj.pure, pcHolds]
  | dyn e =>
      simp [asDataList, valueProj, pcHolds, symValToCek?] at hv ⊢
      cases he : SmtSem.eval m e <;> simp [he] at hv
      rename_i sv
      cases sv <;> simp at hv
      case val val =>
        have hval := semValToCek_dataList hv
        subst val
        exact Moist.SMT.Semantics.evalBoolIs_isVDataList_of he
  | pair a b =>
      simp [symValToCek?] at hv
      cases ha : symValToCek? m a <;> simp [ha] at hv
      rename_i cva
      cases hb : symValToCek? m b <;> simp [hb] at hv
      rename_i cvb
      cases cva <;> cases cvb <;> simp at hv
  | constr tag fields =>
      simp [symValToCek?] at hv
      cases htag : SmtSem.eval m tag <;> simp [htag] at hv
      rename_i sv
      cases sv <;> simp [htag] at hv
      rename_i i
      by_cases hneg : i < 0
      · exact False.elim ((Int.not_le).mpr hneg hv.1)
      · cases hfields : symValListToCekList? m fields <;> simp [hfields] at hv
  | lam body ρ =>
      simp [symValToCek?] at hv
      cases henv : symEnvToCek? m ρ <;> simp [henv] at hv
  | delay body ρ =>
      simp [symValToCek?] at hv
      cases henv : symEnvToCek? m ρ <;> simp [henv] at hv
  | builtin b args ea =>
      simp [symValToCek?] at hv
      cases hargs : symValListToCekList? m args <;> simp [hargs] at hv

theorem asPairDataList_sound {m : SmtSem.Model} {v : SymVal} {cv : CekValue}
    (hv : symValToCek? m v = some cv)
    (hg : pcHolds m (asPairDataList v).guard = true) :
    ∃ xs, cv = .VCon (.ConstPairDataList xs) ∧
      SmtSem.eval m (asPairDataList v).val = some (.dataPairList xs) := by
  cases v with
  | const c =>
      cases c <;> simp [asPairDataList, valueProj, Proj.pure, Proj.fail, pcHolds,
        symValToCek?, symConstToCek?] at hv hg ⊢
      case pairDataList e =>
        cases he : SmtSem.eval m e with
        | none =>
            simp [he] at hv
        | some sv =>
            cases sv <;> simp [he] at hv
            case dataPairList xs =>
              subst cv
              exact ⟨xs, rfl, by simpa [he]⟩
  | dyn e =>
      simp [asPairDataList, valueProj, pcHolds, symValToCek?] at hv hg ⊢
      obtain ⟨xs, he⟩ := Moist.SMT.Semantics.evalBoolIs_isVPairDataList_true hg
      have hun := Moist.SMT.Semantics.eval_unVPairDataList_of (m := m) (e := e) he
      simp [he, semValToCek?, semValToConst?] at hv
      subst cv
      exact ⟨xs, rfl, hun⟩
  | pair a b =>
      simp [asPairDataList, valueProj, Proj.fail, pcHolds] at hg
  | constr tag fields =>
      simp [asPairDataList, valueProj, Proj.fail, pcHolds] at hg
  | lam body ρ =>
      simp [asPairDataList, valueProj, Proj.fail, pcHolds] at hg
  | delay body ρ =>
      simp [asPairDataList, valueProj, Proj.fail, pcHolds] at hg
  | builtin b args ea =>
      simp [asPairDataList, valueProj, Proj.fail, pcHolds] at hg

theorem asPairDataList_guard_of_cek {m : SmtSem.Model} {v : SymVal}
    {xs : List (Plutus.Data × Plutus.Data)}
    (hv : symValToCek? m v = some (.VCon (.ConstPairDataList xs))) :
    pcHolds m (asPairDataList v).guard = true := by
  cases v with
  | const c =>
      obtain ⟨e, hc, _he⟩ :=
        symConstToCek_pairDataList (by simpa [symValToCek?] using hv)
      subst c
      simp [asPairDataList, Proj.pure, pcHolds]
  | dyn e =>
      simp [asPairDataList, valueProj, pcHolds, symValToCek?] at hv ⊢
      cases he : SmtSem.eval m e <;> simp [he] at hv
      rename_i sv
      cases sv <;> simp at hv
      case val val =>
        have hval := semValToCek_pairDataList hv
        subst val
        exact Moist.SMT.Semantics.evalBoolIs_isVPairDataList_of he
  | pair a b =>
      simp [symValToCek?] at hv
      cases ha : symValToCek? m a <;> simp [ha] at hv
      rename_i cva
      cases hb : symValToCek? m b <;> simp [hb] at hv
      rename_i cvb
      cases cva <;> cases cvb <;> simp at hv
  | constr tag fields =>
      simp [symValToCek?] at hv
      cases htag : SmtSem.eval m tag <;> simp [htag] at hv
      rename_i sv
      cases sv <;> simp [htag] at hv
      rename_i i
      by_cases hneg : i < 0
      · exact False.elim ((Int.not_le).mpr hneg hv.1)
      · cases hfields : symValListToCekList? m fields <;> simp [hfields] at hv
  | lam body ρ =>
      simp [symValToCek?] at hv
      cases henv : symEnvToCek? m ρ <;> simp [henv] at hv
  | delay body ρ =>
      simp [symValToCek?] at hv
      cases henv : symEnvToCek? m ρ <;> simp [henv] at hv
  | builtin b args ea =>
      simp [symValToCek?] at hv
      cases hargs : symValListToCekList? m args <;> simp [hargs] at hv

theorem asPairData_sound {m : SmtSem.Model} {v : SymVal} {cv : CekValue}
    (hv : symValToCek? m v = some cv)
    (hg : pcHolds m (asPairData v).guard = true) :
    ∃ a b, cv = .VCon (.PairData (a, b)) ∧
      SmtSem.eval m (asPairData v).val.1 = some (.data a) ∧
      SmtSem.eval m (asPairData v).val.2 = some (.data b) := by
  cases v with
  | const c =>
      cases c <;> simp [asPairData, Proj.pure, Proj.fail, pcHolds,
        symValToCek?, symConstToCek?] at hv hg ⊢
      case pairData a b =>
        cases ha : SmtSem.eval m a <;> simp [ha] at hv
        rename_i sva
        cases sva <;> try simp at hv
        case data da =>
          cases hb : SmtSem.eval m b <;> simp [hb] at hv
          rename_i svb
          cases svb <;> try simp at hv
          case data db =>
            subst cv
            exact ⟨da, db, rfl, by simpa [ha], by simpa [hb]⟩
  | dyn e =>
      simp [asPairData, pcHolds, symValToCek?] at hv hg ⊢
      obtain ⟨a, b, he⟩ := Moist.SMT.Semantics.evalBoolIs_isVPairData_true hg
      have hfst := Moist.SMT.Semantics.eval_pdfst_of (m := m) (e := e) he
      have hsnd := Moist.SMT.Semantics.eval_pdsnd_of (m := m) (e := e) he
      simp [he, semValToCek?, semValToConst?] at hv
      subst cv
      exact ⟨a, b, rfl, hfst, hsnd⟩
  | pair a b =>
      simp [asPairData, Proj.fail, pcHolds] at hg
  | constr tag fields =>
      simp [asPairData, Proj.fail, pcHolds] at hg
  | lam body ρ =>
      simp [asPairData, Proj.fail, pcHolds] at hg
  | delay body ρ =>
      simp [asPairData, Proj.fail, pcHolds] at hg
  | builtin b args ea =>
      simp [asPairData, Proj.fail, pcHolds] at hg

theorem asPair_sound {m : SmtSem.Model} {v : SymVal} {cv : CekValue}
    (hv : symValToCek? m v = some cv)
    (hg : pcHolds m (asPair v).guard = true) :
    ∃ a b,
      cv = .VCon (.Pair (a, b)) ∧
      symValToCek? m (asPair v).val.1 = some (.VCon a) ∧
      symValToCek? m (asPair v).val.2 = some (.VCon b) := by
  cases v with
  | const c =>
      cases c <;> simp [asPair, Proj.fail, pcHolds] at hg
  | dyn e =>
      simp [asPair, pcHolds, symValToCek?] at hv hg ⊢
      obtain ⟨av, bv, he⟩ := Moist.SMT.Semantics.evalBoolIs_isVPair_true hg
      have hfst := Moist.SMT.Semantics.eval_vfst_of (m := m) (e := e) he
      have hsnd := Moist.SMT.Semantics.eval_vsnd_of (m := m) (e := e) he
      simp [he, semValToCek?, semValToConst?] at hv
      cases ha : semValToConst? av <;> simp [ha] at hv
      rename_i ca
      cases hb : semValToConst? bv <;> simp [hb] at hv
      rename_i cb
      subst cv
      exact ⟨ca, cb, rfl,
        by simpa [symValToCek?, hfst] using semValToCek_of_const ha,
        by simpa [symValToCek?, hsnd] using semValToCek_of_const hb⟩
  | pair a b =>
      simp [asPair, Proj.pure, pcHolds, symValToCek?] at hv hg
      cases ha : symValToCek? m a <;> simp [ha] at hv
      rename_i cva
      cases hb : symValToCek? m b <;> simp [hb] at hv
      rename_i cvb
      cases cva with
      | VCon ca =>
          cases cvb with
          | VCon cb =>
              simp at hv
              subst cv
              exact ⟨ca, cb, rfl,
                by simpa [asPair, Proj.pure] using ha,
                by simpa [asPair, Proj.pure] using hb⟩
          | VDelay body ρ =>
              simp at hv
          | VLam body ρ =>
              simp at hv
          | VConstr tag fields =>
              simp at hv
          | VBuiltin b args ea =>
              simp at hv
      | VDelay body ρ =>
          simp at hv
      | VLam body ρ =>
          simp at hv
      | VConstr tag fields =>
          simp at hv
      | VBuiltin b args ea =>
          simp at hv
  | constr tag fields =>
      simp [asPair, Proj.fail, pcHolds] at hg
  | lam body ρ =>
      simp [asPair, Proj.fail, pcHolds] at hg
  | delay body ρ =>
      simp [asPair, Proj.fail, pcHolds] at hg
  | builtin b args ea =>
      simp [asPair, Proj.fail, pcHolds] at hg

theorem asPair_guard_of_cek {m : SmtSem.Model} {v : SymVal} {a b : Const}
    (hv : symValToCek? m v = some (.VCon (.Pair (a, b)))) :
    pcHolds m (asPair v).guard = true := by
  cases v with
  | const c =>
      exfalso
      cases c with
      | integer e =>
          cases he : SmtSem.eval m e with
          | none => simp [symValToCek?, symConstToCek?, he] at hv
          | some sv => cases sv <;> simp [symValToCek?, symConstToCek?, he] at hv
      | bytes e =>
          cases he : SmtSem.eval m e with
          | none => simp [symValToCek?, symConstToCek?, he] at hv
          | some sv => cases sv <;> simp [symValToCek?, symConstToCek?, he] at hv
      | string e =>
          cases he : SmtSem.eval m e with
          | none => simp [symValToCek?, symConstToCek?, he] at hv
          | some sv => cases sv <;> simp [symValToCek?, symConstToCek?, he] at hv
      | bool e =>
          cases he : SmtSem.eval m e with
          | none => simp [symValToCek?, symConstToCek?, he] at hv
          | some sv => cases sv <;> simp [symValToCek?, symConstToCek?, he] at hv
      | unit =>
          simp [symValToCek?, symConstToCek?] at hv
      | constList e =>
          cases he : SmtSem.eval m e with
          | none => simp [symValToCek?, symConstToCek?, he] at hv
          | some sv =>
              cases sv <;> simp [symValToCek?, symConstToCek?, he] at hv
              case valList xs =>
                cases hcs : semValListToConstList? xs <;> simp [hcs] at hv
      | dataList e =>
          cases he : SmtSem.eval m e with
          | none => simp [symValToCek?, symConstToCek?, he] at hv
          | some sv => cases sv <;> simp [symValToCek?, symConstToCek?, he] at hv
      | pairDataList e =>
          cases he : SmtSem.eval m e with
          | none => simp [symValToCek?, symConstToCek?, he] at hv
          | some sv => cases sv <;> simp [symValToCek?, symConstToCek?, he] at hv
      | pairData x y =>
          cases hx : SmtSem.eval m x with
          | none => simp [symValToCek?, symConstToCek?, hx] at hv
          | some svx =>
              cases hy : SmtSem.eval m y with
              | none => simp [symValToCek?, symConstToCek?, hx, hy] at hv
              | some svy =>
                  cases svx <;> cases svy <;>
                    simp [symValToCek?, symConstToCek?, hx, hy] at hv
      | data e =>
          cases he : SmtSem.eval m e with
          | none => simp [symValToCek?, symConstToCek?, he] at hv
          | some sv => cases sv <;> simp [symValToCek?, symConstToCek?, he] at hv
      | array e =>
          cases he : SmtSem.eval m e with
          | none => simp [symValToCek?, symConstToCek?, he] at hv
          | some sv =>
              cases sv <;> simp [symValToCek?, symConstToCek?, he] at hv
              case valList xs =>
                cases hcs : semValListToConstList? xs <;> simp [hcs] at hv
      | g1 e =>
          cases he : SmtSem.eval m e with
          | none => simp [symValToCek?, symConstToCek?, he] at hv
          | some sv => cases sv <;> simp [symValToCek?, symConstToCek?, he] at hv
      | g2 e =>
          cases he : SmtSem.eval m e with
          | none => simp [symValToCek?, symConstToCek?, he] at hv
          | some sv => cases sv <;> simp [symValToCek?, symConstToCek?, he] at hv
      | ml e =>
          cases he : SmtSem.eval m e with
          | none => simp [symValToCek?, symConstToCek?, he] at hv
          | some sv => cases sv <;> simp [symValToCek?, symConstToCek?, he] at hv
  | dyn e =>
      simp [asPair, pcHolds, symValToCek?] at hv ⊢
      cases he : SmtSem.eval m e with
      | none => simp [he] at hv
      | some sv =>
          cases sv <;> simp [he] at hv
          case val val =>
            cases val with
            | int i => simp [semValToCek?, semValToConst?] at hv
            | bytes bs => simp [semValToCek?, semValToConst?] at hv
            | string s => simp [semValToCek?, semValToConst?] at hv
            | bool b => simp [semValToCek?, semValToConst?] at hv
            | unit => simp [semValToCek?, semValToConst?] at hv
            | list xs =>
                cases hcs : semValListToConstList? xs <;>
                  simp [semValToCek?, semValToConst?, hcs] at hv
            | dataList xs => simp [semValToCek?, semValToConst?] at hv
            | pairDataList xs => simp [semValToCek?, semValToConst?] at hv
            | pair av bv =>
                cases ha : semValToConst? av <;>
                  simp [semValToCek?, semValToConst?, ha] at hv
                rename_i ca
                cases hb : semValToConst? bv <;> simp [hb] at hv
                rename_i cb
                exact Moist.SMT.Semantics.evalBoolIs_isVPair_of he
            | pairData da db => simp [semValToCek?, semValToConst?] at hv
            | data d => simp [semValToCek?, semValToConst?] at hv
            | array xs =>
                cases hcs : semValListToConstList? xs <;>
                  simp [semValToCek?, semValToConst?, hcs] at hv
            | g1 g => simp [semValToCek?, semValToConst?] at hv
            | g2 g => simp [semValToCek?, semValToConst?] at hv
            | ml r => simp [semValToCek?, semValToConst?] at hv
            | constr tag fields =>
                by_cases hneg : tag < 0
                · exact False.elim (by simpa [semValToCek?, hneg] using hv)
                · cases hfields : semValListToCekList? fields
                  · exact False.elim (by simp [semValToCek?, hneg, hfields] at hv)
                  · exact False.elim (by simp [semValToCek?, hneg, hfields] at hv)
  | pair x y =>
      simp [asPair, Proj.pure, pcHolds]
  | constr tag fields =>
      simp [symValToCek?] at hv
      cases htag : SmtSem.eval m tag <;> simp [htag] at hv
      rename_i sv
      cases sv <;> simp [htag] at hv
      rename_i i
      by_cases hneg : i < 0
      · exact False.elim ((Int.not_le).mpr hneg hv.1)
      · cases hfields : symValListToCekList? m fields
        · exact False.elim (by simp [hneg, hfields] at hv)
        · exact False.elim (by simp [hneg, hfields] at hv)
  | lam body ρ =>
      simp [symValToCek?] at hv
      cases henv : symEnvToCek? m ρ <;> simp [henv] at hv
  | delay body ρ =>
      simp [symValToCek?] at hv
      cases henv : symEnvToCek? m ρ <;> simp [henv] at hv
  | builtin b args ea =>
      simp [symValToCek?] at hv
      cases hargs : symValListToCekList? m args <;> simp [hargs] at hv

theorem asPairData_guard_of_cek {m : SmtSem.Model} {v : SymVal} {a b : Plutus.Data}
    (hv : symValToCek? m v = some (.VCon (.PairData (a, b)))) :
    pcHolds m (asPairData v).guard = true := by
  cases v with
  | const c =>
      cases c with
      | pairData x y =>
          simp [asPairData, Proj.pure, pcHolds]
      | integer e =>
          exfalso
          cases he : SmtSem.eval m e with
          | none => simp [symValToCek?, symConstToCek?, he] at hv
          | some sv => cases sv <;> simp [symValToCek?, symConstToCek?, he] at hv
      | bytes e =>
          exfalso
          cases he : SmtSem.eval m e with
          | none => simp [symValToCek?, symConstToCek?, he] at hv
          | some sv => cases sv <;> simp [symValToCek?, symConstToCek?, he] at hv
      | string e =>
          exfalso
          cases he : SmtSem.eval m e with
          | none => simp [symValToCek?, symConstToCek?, he] at hv
          | some sv => cases sv <;> simp [symValToCek?, symConstToCek?, he] at hv
      | bool e =>
          exfalso
          cases he : SmtSem.eval m e with
          | none => simp [symValToCek?, symConstToCek?, he] at hv
          | some sv => cases sv <;> simp [symValToCek?, symConstToCek?, he] at hv
      | unit =>
          exfalso
          simp [symValToCek?, symConstToCek?] at hv
      | constList e =>
          exfalso
          cases he : SmtSem.eval m e with
          | none => simp [symValToCek?, symConstToCek?, he] at hv
          | some sv =>
              cases sv <;> simp [symValToCek?, symConstToCek?, he] at hv
              case valList xs =>
                cases hcs : semValListToConstList? xs <;> simp [hcs] at hv
      | dataList e =>
          exfalso
          cases he : SmtSem.eval m e with
          | none => simp [symValToCek?, symConstToCek?, he] at hv
          | some sv => cases sv <;> simp [symValToCek?, symConstToCek?, he] at hv
      | pairDataList e =>
          exfalso
          cases he : SmtSem.eval m e with
          | none => simp [symValToCek?, symConstToCek?, he] at hv
          | some sv => cases sv <;> simp [symValToCek?, symConstToCek?, he] at hv
      | data e =>
          exfalso
          cases he : SmtSem.eval m e with
          | none => simp [symValToCek?, symConstToCek?, he] at hv
          | some sv => cases sv <;> simp [symValToCek?, symConstToCek?, he] at hv
      | array e =>
          exfalso
          cases he : SmtSem.eval m e with
          | none => simp [symValToCek?, symConstToCek?, he] at hv
          | some sv =>
              cases sv <;> simp [symValToCek?, symConstToCek?, he] at hv
              case valList xs =>
                cases hcs : semValListToConstList? xs <;> simp [hcs] at hv
      | g1 e =>
          exfalso
          cases he : SmtSem.eval m e with
          | none => simp [symValToCek?, symConstToCek?, he] at hv
          | some sv => cases sv <;> simp [symValToCek?, symConstToCek?, he] at hv
      | g2 e =>
          exfalso
          cases he : SmtSem.eval m e with
          | none => simp [symValToCek?, symConstToCek?, he] at hv
          | some sv => cases sv <;> simp [symValToCek?, symConstToCek?, he] at hv
      | ml e =>
          exfalso
          cases he : SmtSem.eval m e with
          | none => simp [symValToCek?, symConstToCek?, he] at hv
          | some sv => cases sv <;> simp [symValToCek?, symConstToCek?, he] at hv
  | dyn e =>
      simp [asPairData, pcHolds, symValToCek?] at hv ⊢
      cases he : SmtSem.eval m e with
      | none => simp [he] at hv
      | some sv =>
          cases sv <;> simp [he] at hv
          case val val =>
            cases val with
            | int i => simp [semValToCek?, semValToConst?] at hv
            | bytes bs => simp [semValToCek?, semValToConst?] at hv
            | string s => simp [semValToCek?, semValToConst?] at hv
            | bool b => simp [semValToCek?, semValToConst?] at hv
            | unit => simp [semValToCek?, semValToConst?] at hv
            | list xs =>
                cases hcs : semValListToConstList? xs <;>
                  simp [semValToCek?, semValToConst?, hcs] at hv
            | dataList xs => simp [semValToCek?, semValToConst?] at hv
            | pairDataList xs => simp [semValToCek?, semValToConst?] at hv
            | pair av bv =>
                cases ha : semValToConst? av <;>
                  simp [semValToCek?, semValToConst?, ha] at hv
                rename_i ca
                cases hb : semValToConst? bv <;> simp [hb] at hv
            | pairData da db =>
                exact Moist.SMT.Semantics.evalBoolIs_isVPairData_of he
            | data d => simp [semValToCek?, semValToConst?] at hv
            | array xs =>
                cases hcs : semValListToConstList? xs <;>
                  simp [semValToCek?, semValToConst?, hcs] at hv
            | g1 g => simp [semValToCek?, semValToConst?] at hv
            | g2 g => simp [semValToCek?, semValToConst?] at hv
            | ml r => simp [semValToCek?, semValToConst?] at hv
            | constr tag fields =>
                by_cases hneg : tag < 0
                · exact False.elim (by simpa [semValToCek?, hneg] using hv)
                · cases hfields : semValListToCekList? fields
                  · exact False.elim (by simp [semValToCek?, hneg, hfields] at hv)
                  · exact False.elim (by simp [semValToCek?, hneg, hfields] at hv)
  | pair x y =>
      simp [symValToCek?] at hv
      cases hx : symValToCek? m x <;> simp [hx] at hv
      rename_i cvx
      cases hy : symValToCek? m y <;> simp [hy] at hv
      rename_i cvy
      cases cvx <;> cases cvy <;> simp at hv
  | constr tag fields =>
      simp [symValToCek?] at hv
      cases htag : SmtSem.eval m tag <;> simp [htag] at hv
      rename_i sv
      cases sv <;> simp [htag] at hv
      rename_i i
      by_cases hneg : i < 0
      · exact False.elim ((Int.not_le).mpr hneg hv.1)
      · cases hfields : symValListToCekList? m fields
        · exact False.elim (by simp [hneg, hfields] at hv)
        · exact False.elim (by simp [hneg, hfields] at hv)
  | lam body ρ =>
      simp [symValToCek?] at hv
      cases henv : symEnvToCek? m ρ <;> simp [henv] at hv
  | delay body ρ =>
      simp [symValToCek?] at hv
      cases henv : symEnvToCek? m ρ <;> simp [henv] at hv
  | builtin b args ea =>
      simp [symValToCek?] at hv
      cases hargs : symValListToCekList? m args <;> simp [hargs] at hv

theorem asConstList_sound {m : SmtSem.Model} {v : SymVal} {cv : CekValue}
    (hv : symValToCek? m v = some cv)
    (hg : pcHolds m (asConstList v).guard = true) :
    ∃ vals cs, cv = .VCon (.ConstList cs) ∧
      SmtSem.eval m (asConstList v).val = some (.valList vals) ∧
      semValListToConstList? vals = some cs := by
  cases v with
  | const c =>
      cases c <;> simp [asConstList, valueProj, Proj.pure, Proj.fail, pcHolds,
        symValToCek?, symConstToCek?] at hv hg ⊢
      case constList e =>
        cases he : SmtSem.eval m e <;> simp [he] at hv
        rename_i sv
        cases sv <;> simp [he] at hv
        case valList vals =>
          cases hcs : semValListToConstList? vals <;> simp [hcs] at hv
          rename_i cs
          subst cv
          exact ⟨vals, cs, rfl, by simpa [he], hcs⟩
  | dyn e =>
      simp [asConstList, valueProj, pcHolds, symValToCek?] at hv hg ⊢
      obtain ⟨vals, he⟩ := Moist.SMT.Semantics.evalBoolIs_isVList_true hg
      have hun := Moist.SMT.Semantics.eval_unVList_of (m := m) (e := e) he
      simp [he, semValToCek?, semValToConst?] at hv
      cases hcs : semValListToConstList? vals <;> simp [hcs] at hv
      rename_i cs
      subst cv
      exact ⟨vals, cs, rfl, hun, hcs⟩
  | pair a b =>
      simp [asConstList, valueProj, Proj.fail, pcHolds] at hg
  | constr tag fields =>
      simp [asConstList, valueProj, Proj.fail, pcHolds] at hg
  | lam body ρ =>
      simp [asConstList, valueProj, Proj.fail, pcHolds] at hg
  | delay body ρ =>
      simp [asConstList, valueProj, Proj.fail, pcHolds] at hg
  | builtin b args ea =>
      simp [asConstList, valueProj, Proj.fail, pcHolds] at hg

theorem asConstList_guard_of_cek {m : SmtSem.Model} {v : SymVal} {cs : List Const}
    (hv : symValToCek? m v = some (.VCon (.ConstList cs))) :
    pcHolds m (asConstList v).guard = true := by
  cases v with
  | const c =>
      obtain ⟨e, vals, hc, _he, _hcs⟩ :=
        symConstToCek_constList (by simpa [symValToCek?] using hv)
      subst c
      simp [asConstList, Proj.pure, pcHolds]
  | dyn e =>
      simp [asConstList, valueProj, pcHolds, symValToCek?] at hv ⊢
      cases he : SmtSem.eval m e <;> simp [he] at hv
      rename_i sv
      cases sv <;> simp at hv
      case val val =>
        obtain ⟨vals, hval, _hcs⟩ := semValToCek_constList hv
        subst val
        exact Moist.SMT.Semantics.evalBoolIs_isVList_of he
  | pair a b =>
      simp [symValToCek?] at hv
      cases ha : symValToCek? m a <;> simp [ha] at hv
      rename_i cva
      cases hb : symValToCek? m b <;> simp [hb] at hv
      rename_i cvb
      cases cva <;> cases cvb <;> simp at hv
  | constr tag fields =>
      simp [symValToCek?] at hv
      cases htag : SmtSem.eval m tag <;> simp [htag] at hv
      rename_i sv
      cases sv <;> simp [htag] at hv
      rename_i i
      by_cases hneg : i < 0
      · exact False.elim ((Int.not_le).mpr hneg hv.1)
      · cases hfields : symValListToCekList? m fields <;> simp [hfields] at hv
  | lam body ρ =>
      simp [symValToCek?] at hv
      cases henv : symEnvToCek? m ρ <;> simp [henv] at hv
  | delay body ρ =>
      simp [symValToCek?] at hv
      cases henv : symEnvToCek? m ρ <;> simp [henv] at hv
  | builtin b args ea =>
      simp [symValToCek?] at hv
      cases hargs : symValListToCekList? m args <;> simp [hargs] at hv

theorem asArray_sound {m : SmtSem.Model} {v : SymVal} {cv : CekValue}
    (hv : symValToCek? m v = some cv)
    (hg : pcHolds m (asArray v).guard = true) :
    ∃ vals cs, cv = .VCon (.ConstArray cs) ∧
      SmtSem.eval m (asArray v).val = some (.valList vals) ∧
      semValListToConstList? vals = some cs := by
  cases v with
  | const c =>
      cases c <;> simp [asArray, valueProj, Proj.pure, Proj.fail, pcHolds,
        symValToCek?, symConstToCek?] at hv hg ⊢
      case array e =>
        cases he : SmtSem.eval m e <;> simp [he] at hv
        rename_i sv
        cases sv <;> simp [he] at hv
        case valList vals =>
          cases hcs : semValListToConstList? vals <;> simp [hcs] at hv
          rename_i cs
          subst cv
          exact ⟨vals, cs, rfl, by simpa [he], hcs⟩
  | dyn e =>
      simp [asArray, valueProj, pcHolds, symValToCek?] at hv hg ⊢
      obtain ⟨vals, he⟩ := Moist.SMT.Semantics.evalBoolIs_isVArray_true hg
      have hun := Moist.SMT.Semantics.eval_unVArray_of (m := m) (e := e) he
      simp [he, semValToCek?, semValToConst?] at hv
      cases hcs : semValListToConstList? vals <;> simp [hcs] at hv
      rename_i cs
      subst cv
      exact ⟨vals, cs, rfl, hun, hcs⟩
  | pair a b =>
      simp [asArray, valueProj, Proj.fail, pcHolds] at hg
  | constr tag fields =>
      simp [asArray, valueProj, Proj.fail, pcHolds] at hg
  | lam body ρ =>
      simp [asArray, valueProj, Proj.fail, pcHolds] at hg
  | delay body ρ =>
      simp [asArray, valueProj, Proj.fail, pcHolds] at hg
  | builtin b args ea =>
      simp [asArray, valueProj, Proj.fail, pcHolds] at hg

theorem asArray_guard_of_cek {m : SmtSem.Model} {v : SymVal} {cs : List Const}
    (hv : symValToCek? m v = some (.VCon (.ConstArray cs))) :
    pcHolds m (asArray v).guard = true := by
  cases v with
  | const c =>
      obtain ⟨e, vals, hc, _he, _hcs⟩ :=
        symConstToCek_array (by simpa [symValToCek?] using hv)
      subst c
      simp [asArray, Proj.pure, pcHolds]
  | dyn e =>
      simp [asArray, valueProj, pcHolds, symValToCek?] at hv ⊢
      cases he : SmtSem.eval m e <;> simp [he] at hv
      rename_i sv
      cases sv <;> simp at hv
      case val val =>
        obtain ⟨vals, hval, _hcs⟩ := semValToCek_array hv
        subst val
        exact Moist.SMT.Semantics.evalBoolIs_isVArray_of he
  | pair a b =>
      simp [symValToCek?] at hv
      cases ha : symValToCek? m a <;> simp [ha] at hv
      rename_i cva
      cases hb : symValToCek? m b <;> simp [hb] at hv
      rename_i cvb
      cases cva <;> cases cvb <;> simp at hv
  | constr tag fields =>
      simp [symValToCek?] at hv
      cases htag : SmtSem.eval m tag <;> simp [htag] at hv
      rename_i sv
      cases sv <;> simp [htag] at hv
      rename_i i
      by_cases hneg : i < 0
      · exact False.elim ((Int.not_le).mpr hneg hv.1)
      · cases hfields : symValListToCekList? m fields <;> simp [hfields] at hv
  | lam body ρ =>
      simp [symValToCek?] at hv
      cases henv : symEnvToCek? m ρ <;> simp [henv] at hv
  | delay body ρ =>
      simp [symValToCek?] at hv
      cases henv : symEnvToCek? m ρ <;> simp [henv] at hv
  | builtin b args ea =>
      simp [symValToCek?] at hv
      cases hargs : symValListToCekList? m args <;> simp [hargs] at hv

set_option maxHeartbeats 0 in
theorem asConstVal_sound {m : SmtSem.Model} {v : SymVal} {cv : CekValue}
    (hv : symValToCek? m v = some cv)
    (hg : pcHolds m (asConstVal v).guard = true) :
    ∃ c : Const, ∃ semv : Moist.SMT.Semantics.Val, cv = .VCon c ∧
      SmtSem.eval m (asConstVal v).val = some (.val semv) ∧
      semValToConst? semv = some c := by
  let motive1 := fun v : SymVal =>
    ∀ {cv : CekValue},
      symValToCek? m v = some cv →
      pcHolds m (asConstVal v).guard = true →
      ∃ c : Const, ∃ semv : Moist.SMT.Semantics.Val, cv = .VCon c ∧
        SmtSem.eval m (asConstVal v).val = some (.val semv) ∧
        semValToConst? semv = some c
  let motive2 := fun _ : List SymVal => True
  exact (SymVal.rec
    (motive_1 := motive1)
    (motive_2 := motive2)
    (fun sc => by
      intro cv hv _hg
      cases sc with
      | integer e =>
          simp [symValToCek?, symConstToCek?] at hv
          cases he : SmtSem.eval m e <;> simp [he] at hv
          rename_i sv
          cases sv <;> simp [he] at hv
          rename_i i
          subst cv
          refine Exists.intro (.Integer i) ?_
          refine Exists.intro (Moist.SMT.Semantics.Val.int i) ?_
          exact ⟨rfl, by
            simpa [asConstVal, encodeVal?, encodeVal?.encodeConst?, Proj.pure]
              using Moist.SMT.Semantics.eval_VInt_of he, rfl⟩
      | bytes e =>
          simp [symValToCek?, symConstToCek?] at hv
          cases he : SmtSem.eval m e <;> simp [he] at hv
          rename_i sv
          cases sv <;> simp [he] at hv
          rename_i bs
          subst cv
          refine Exists.intro (.ByteString bs) ?_
          refine Exists.intro (Moist.SMT.Semantics.Val.bytes bs) ?_
          exact ⟨rfl, by
            simpa [asConstVal, encodeVal?, encodeVal?.encodeConst?, Proj.pure]
              using Moist.SMT.Semantics.eval_VBytes_of he, rfl⟩
      | string e =>
          simp [symValToCek?, symConstToCek?] at hv
          cases he : SmtSem.eval m e <;> simp [he] at hv
          rename_i sv
          cases sv <;> simp [he] at hv
          rename_i s
          subst cv
          refine Exists.intro (.String s) ?_
          refine Exists.intro (Moist.SMT.Semantics.Val.string s) ?_
          exact ⟨rfl, by
            simpa [asConstVal, encodeVal?, encodeVal?.encodeConst?, Proj.pure]
              using Moist.SMT.Semantics.eval_VString_of he, rfl⟩
      | bool e =>
          simp [symValToCek?, symConstToCek?] at hv
          cases he : SmtSem.eval m e <;> simp [he] at hv
          rename_i sv
          cases sv <;> simp [he] at hv
          rename_i b
          subst cv
          refine Exists.intro (.Bool b) ?_
          refine Exists.intro (Moist.SMT.Semantics.Val.bool b) ?_
          exact ⟨rfl, by
            simpa [asConstVal, encodeVal?, encodeVal?.encodeConst?, Proj.pure]
              using Moist.SMT.Semantics.eval_VBool_of he, rfl⟩
      | unit =>
          simp [symValToCek?, symConstToCek?] at hv
          subst cv
          refine Exists.intro .Unit ?_
          refine Exists.intro Moist.SMT.Semantics.Val.unit ?_
          exact ⟨rfl, by
            simpa [asConstVal, encodeVal?, encodeVal?.encodeConst?, Proj.pure]
              using Moist.SMT.Semantics.eval_VUnit m, rfl⟩
      | data e =>
          simp [symValToCek?, symConstToCek?] at hv
          cases he : SmtSem.eval m e <;> simp [he] at hv
          rename_i sv
          cases sv <;> simp [he] at hv
          rename_i d
          subst cv
          refine Exists.intro (.Data d) ?_
          refine Exists.intro (Moist.SMT.Semantics.Val.data d) ?_
          exact ⟨rfl, by
            simpa [asConstVal, encodeVal?, encodeVal?.encodeConst?, Proj.pure]
              using Moist.SMT.Semantics.eval_VData_of he, rfl⟩
      | constList e =>
          simp [symValToCek?, symConstToCek?] at hv
          cases he : SmtSem.eval m e <;> simp [he] at hv
          rename_i sv
          cases sv <;> simp [he] at hv
          rename_i vals
          cases hcs : semValListToConstList? vals <;> simp [hcs] at hv
          rename_i cs
          subst cv
          refine Exists.intro (.ConstList cs) ?_
          refine Exists.intro (Moist.SMT.Semantics.Val.list vals) ?_
          exact ⟨rfl, by
            simpa [asConstVal, encodeVal?, encodeVal?.encodeConst?, Proj.pure]
              using Moist.SMT.Semantics.eval_VList_of he,
            by simp [semValToConst?, hcs]⟩
      | dataList e =>
          simp [symValToCek?, symConstToCek?] at hv
          cases he : SmtSem.eval m e <;> simp [he] at hv
          rename_i sv
          cases sv <;> simp [he] at hv
          rename_i xs
          subst cv
          refine Exists.intro (.ConstDataList xs) ?_
          refine Exists.intro (Moist.SMT.Semantics.Val.dataList xs) ?_
          exact ⟨rfl, by
            simpa [asConstVal, encodeVal?, encodeVal?.encodeConst?, Proj.pure]
              using Moist.SMT.Semantics.eval_VDataList_of he, rfl⟩
      | pairDataList e =>
          simp [symValToCek?, symConstToCek?] at hv
          cases he : SmtSem.eval m e <;> simp [he] at hv
          rename_i sv
          cases sv <;> simp [he] at hv
          rename_i xs
          subst cv
          refine Exists.intro (.ConstPairDataList xs) ?_
          refine Exists.intro (Moist.SMT.Semantics.Val.pairDataList xs) ?_
          exact ⟨rfl, by
            simpa [asConstVal, encodeVal?, encodeVal?.encodeConst?, Proj.pure]
              using Moist.SMT.Semantics.eval_VPairDataList_of he, rfl⟩
      | pairData a b =>
          simp [symValToCek?, symConstToCek?] at hv
          cases ha : SmtSem.eval m a <;> simp [ha] at hv
          rename_i sva
          cases hb : SmtSem.eval m b <;> simp [ha, hb] at hv
          rename_i svb
          cases sva <;> cases svb <;> simp [ha, hb] at hv
          rename_i da db
          subst cv
          refine Exists.intro (.PairData (da, db)) ?_
          refine Exists.intro (Moist.SMT.Semantics.Val.pairData da db) ?_
          exact ⟨rfl, by
            simpa [asConstVal, encodeVal?, encodeVal?.encodeConst?, Proj.pure]
              using Moist.SMT.Semantics.eval_VPairData_of ha hb, rfl⟩
      | array e =>
          simp [symValToCek?, symConstToCek?] at hv
          cases he : SmtSem.eval m e <;> simp [he] at hv
          rename_i sv
          cases sv <;> simp [he] at hv
          rename_i vals
          cases hcs : semValListToConstList? vals <;> simp [hcs] at hv
          rename_i cs
          subst cv
          refine Exists.intro (.ConstArray cs) ?_
          refine Exists.intro (Moist.SMT.Semantics.Val.array vals) ?_
          exact ⟨rfl, by
            simpa [asConstVal, encodeVal?, encodeVal?.encodeConst?, Proj.pure]
              using Moist.SMT.Semantics.eval_VArray_of he,
            by simp [semValToConst?, hcs]⟩
      | g1 e =>
          simp [symValToCek?, symConstToCek?] at hv
          cases he : SmtSem.eval m e <;> simp [he] at hv
          rename_i sv
          cases sv <;> simp [he] at hv
          rename_i g
          subst cv
          refine Exists.intro .Bls12_381_G1_element ?_
          refine Exists.intro (Moist.SMT.Semantics.Val.g1 g) ?_
          exact ⟨rfl, by
            simpa [asConstVal, encodeVal?, encodeVal?.encodeConst?, Proj.pure]
              using Moist.SMT.Semantics.eval_VG1_of he, rfl⟩
      | g2 e =>
          simp [symValToCek?, symConstToCek?] at hv
          cases he : SmtSem.eval m e <;> simp [he] at hv
          rename_i sv
          cases sv <;> simp [he] at hv
          rename_i g
          subst cv
          refine Exists.intro .Bls12_381_G2_element ?_
          refine Exists.intro (Moist.SMT.Semantics.Val.g2 g) ?_
          exact ⟨rfl, by
            simpa [asConstVal, encodeVal?, encodeVal?.encodeConst?, Proj.pure]
              using Moist.SMT.Semantics.eval_VG2_of he, rfl⟩
      | ml e =>
          simp [symValToCek?, symConstToCek?] at hv
          cases he : SmtSem.eval m e <;> simp [he] at hv
          rename_i sv
          cases sv <;> simp [he] at hv
          rename_i r
          subst cv
          refine Exists.intro .Bls12_381_MlResult ?_
          refine Exists.intro (Moist.SMT.Semantics.Val.ml r) ?_
          exact ⟨rfl, by
            simpa [asConstVal, encodeVal?, encodeVal?.encodeConst?, Proj.pure]
              using Moist.SMT.Semantics.eval_VMlResult_of he, rfl⟩)
    (fun e => by
      intro cv hv hg
      simp [asConstVal, pcHolds, symValToCek?] at hv hg
      cases he : SmtSem.eval m e <;> simp [he] at hv hg
      rename_i sv
      cases sv <;> simp [he] at hv hg
      rename_i semv
      cases semv <;> simp [semValToCek?, semValToConst?] at hv
      · rename_i i
        subst cv
        refine Exists.intro (.Integer i) ?_
        refine Exists.intro (Moist.SMT.Semantics.Val.int i) ?_
        exact ⟨rfl, by simpa [asConstVal] using he, rfl⟩
      · rename_i bs
        subst cv
        refine Exists.intro (.ByteString bs) ?_
        refine Exists.intro (Moist.SMT.Semantics.Val.bytes bs) ?_
        exact ⟨rfl, by simpa [asConstVal] using he, rfl⟩
      · rename_i s
        subst cv
        refine Exists.intro (.String s) ?_
        refine Exists.intro (Moist.SMT.Semantics.Val.string s) ?_
        exact ⟨rfl, by simpa [asConstVal] using he, rfl⟩
      · rename_i b
        subst cv
        refine Exists.intro (.Bool b) ?_
        refine Exists.intro (Moist.SMT.Semantics.Val.bool b) ?_
        exact ⟨rfl, by simpa [asConstVal] using he, rfl⟩
      · subst cv
        refine Exists.intro .Unit ?_
        refine Exists.intro Moist.SMT.Semantics.Val.unit ?_
        exact ⟨rfl, by simpa [asConstVal] using he, rfl⟩
      · rename_i vals
        cases hcs : semValListToConstList? vals <;> simp [hcs] at hv
        rename_i cs
        subst cv
        refine Exists.intro (.ConstList cs) ?_
        refine Exists.intro (Moist.SMT.Semantics.Val.list vals) ?_
        exact ⟨rfl, by simpa [asConstVal] using he, by simp [semValToConst?, hcs]⟩
      · rename_i xs
        subst cv
        refine Exists.intro (.ConstDataList xs) ?_
        refine Exists.intro (Moist.SMT.Semantics.Val.dataList xs) ?_
        exact ⟨rfl, by simpa [asConstVal] using he, rfl⟩
      · rename_i xs
        subst cv
        refine Exists.intro (.ConstPairDataList xs) ?_
        refine Exists.intro (Moist.SMT.Semantics.Val.pairDataList xs) ?_
        exact ⟨rfl, by simpa [asConstVal] using he, rfl⟩
      · rename_i av bv
        cases ha : semValToConst? av <;> simp [ha] at hv
        rename_i ca
        cases hb : semValToConst? bv <;> simp [hb] at hv
        rename_i cb
        subst cv
        refine Exists.intro (.Pair (ca, cb)) ?_
        refine Exists.intro (Moist.SMT.Semantics.Val.pair av bv) ?_
        exact ⟨rfl, by simpa [asConstVal] using he, by simp [semValToConst?, ha, hb]⟩
      · rename_i a b
        subst cv
        refine Exists.intro (.PairData (a, b)) ?_
        refine Exists.intro (Moist.SMT.Semantics.Val.pairData a b) ?_
        exact ⟨rfl, by simpa [asConstVal] using he, rfl⟩
      · rename_i d
        subst cv
        refine Exists.intro (.Data d) ?_
        refine Exists.intro (Moist.SMT.Semantics.Val.data d) ?_
        exact ⟨rfl, by simpa [asConstVal] using he, rfl⟩
      · rename_i vals
        cases hcs : semValListToConstList? vals <;> simp [hcs] at hv
        rename_i cs
        subst cv
        refine Exists.intro (.ConstArray cs) ?_
        refine Exists.intro (Moist.SMT.Semantics.Val.array vals) ?_
        exact ⟨rfl, by simpa [asConstVal] using he, by simp [semValToConst?, hcs]⟩
      · rename_i g
        subst cv
        refine Exists.intro .Bls12_381_G1_element ?_
        refine Exists.intro (Moist.SMT.Semantics.Val.g1 g) ?_
        exact ⟨rfl, by simpa [asConstVal] using he, rfl⟩
      · rename_i g
        subst cv
        refine Exists.intro .Bls12_381_G2_element ?_
        refine Exists.intro (Moist.SMT.Semantics.Val.g2 g) ?_
        exact ⟨rfl, by simpa [asConstVal] using he, rfl⟩
      · rename_i r
        subst cv
        refine Exists.intro .Bls12_381_MlResult ?_
        refine Exists.intro (Moist.SMT.Semantics.Val.ml r) ?_
        exact ⟨rfl, by simpa [asConstVal] using he, rfl⟩
      · rename_i tag fields
        have hfalse :=
          Moist.SMT.Semantics.evalBoolIs_constValValid_constr_false
            (m := m) (e := e) (tag := tag) (fields := fields) he
        exact False.elim (evalBoolIs_true_false_contra hg hfalse))
    (fun a b iha ihb => by
      intro cv hv hg
      simp [asConstVal, symValToCek?, pcHolds] at hv hg
      cases ha : symValToCek? m a <;> simp [ha] at hv
      rename_i cva
      cases hb : symValToCek? m b <;> simp [hb] at hv
      rename_i cvb
      cases cva with
      | VCon ca =>
          cases cvb with
          | VCon cb =>
              simp at hv
              subst cv
              have hp :=
                (Moist.SMT.Semantics.evalBoolIs_and_true m
                  (asConstVal a).guard (asConstVal b).guard).mp hg
              obtain ⟨ca', av, hcaEq, haEval, haConst⟩ :=
                iha (cv := .VCon ca) ha hp.1
              injection hcaEq with hcaEq'
              subst ca'
              obtain ⟨cb', bv, hcbEq, hbEval, hbConst⟩ :=
                ihb (cv := .VCon cb) hb hp.2
              injection hcbEq with hcbEq'
              subst cb'
              refine Exists.intro (.Pair (ca, cb)) ?_
              refine Exists.intro (Moist.SMT.Semantics.Val.pair av bv) ?_
              exact ⟨rfl, Moist.SMT.Semantics.eval_VPair_of haEval hbEval,
                by simp [semValToConst?, haConst, hbConst]⟩
          | VDelay body ρ => simp at hv
          | VLam body ρ => simp at hv
          | VConstr tag fields => simp at hv
          | VBuiltin b args ea => simp at hv
      | VDelay body ρ => simp at hv
      | VLam body ρ => simp at hv
      | VConstr tag fields => simp at hv
      | VBuiltin b args ea => simp at hv)
    (fun tag fields _ => by
      intro cv hv hg
      simp [asConstVal, Proj.fail, pcHolds] at hg)
    (fun body ρ _ => by
      intro cv hv hg
      simp [asConstVal, Proj.fail, pcHolds] at hg)
    (fun body ρ _ => by
      intro cv hv hg
      simp [asConstVal, Proj.fail, pcHolds] at hg)
    (fun b args ea _ => by
      intro cv hv hg
      simp [asConstVal, Proj.fail, pcHolds] at hg)
    trivial
    (fun _ _ _ _ => trivial)
    v) hv hg

set_option maxHeartbeats 0 in
theorem asConstVal_guard_of_cek {m : SmtSem.Model} {v : SymVal} {c : Const}
    (hv : symValToCek? m v = some (.VCon c)) :
    pcHolds m (asConstVal v).guard = true := by
  let motive1 := fun v : SymVal => ∀ {c : Const},
    symValToCek? m v = some (.VCon c) →
    pcHolds m (asConstVal v).guard = true
  let motive2 := fun _ : List SymVal => True
  exact (SymVal.rec
    (motive_1 := motive1)
    (motive_2 := motive2)
    (fun sc => by
      intro c hv
      cases sc <;> simp [asConstVal, encodeVal?, encodeVal?.encodeConst?,
        Proj.pure, pcHolds])
    (fun e => by
      intro c hv
      simp [asConstVal, symValToCek?, pcHolds] at hv ⊢
      cases he : SmtSem.eval m e <;> simp [he] at hv
      rename_i sv
      cases sv with
      | val val =>
          simp at hv
          have hconst : semValToConst? val = some c :=
            semValToCek_vcon_const hv
          have hcompat := semValToConst_constValCompatible hconst
          exact Moist.SMT.Semantics.evalBoolIs_constValValid_true_of_compatible
            he hcompat
      | bool b => simp [semValToCek?] at hv
      | int i => simp [semValToCek?] at hv
      | string s => simp [semValToCek?] at hv
      | bytes bs => simp [semValToCek?] at hv
      | data d => simp [semValToCek?] at hv
      | dataList ds => simp [semValToCek?] at hv
      | dataPairList ds => simp [semValToCek?] at hv
      | valList vs => simp [semValToCek?] at hv
      | g1 g => simp [semValToCek?] at hv
      | g2 g => simp [semValToCek?] at hv
      | ml r => simp [semValToCek?] at hv)
    (fun a b iha ihb => by
      intro c hv
      simp [symValToCek?, asConstVal, pcHolds] at hv ⊢
      cases ha : symValToCek? m a <;> simp [ha] at hv
      rename_i cva
      cases hb : symValToCek? m b <;> simp [hb] at hv
      rename_i cvb
      cases cva with
      | VCon ca =>
          cases cvb with
          | VCon cb =>
              simp at hv
              subst c
              exact pcHolds_and_intro (iha ha) (ihb hb)
          | VLam body ρ => simp at hv
          | VDelay body ρ => simp at hv
          | VConstr tag fields => simp at hv
          | VBuiltin b args ea => simp at hv
      | VLam body ρ => simp at hv
      | VDelay body ρ => simp at hv
      | VConstr tag fields => simp at hv
      | VBuiltin b args ea => simp at hv)
    (fun tag fields _ => by
      intro c hv
      simp [symValToCek?, asConstVal, Proj.fail, pcHolds] at hv ⊢
      cases htag : SmtSem.eval m tag <;> simp [htag] at hv
      rename_i sv
      cases sv <;> simp at hv
      rename_i i
      cases hfields : symValListToCekList? m fields <;> simp [hfields] at hv)
    (fun body ρ _ => by
      intro c hv
      simp [symValToCek?, asConstVal, Proj.fail, pcHolds] at hv ⊢
      cases henv : symEnvToCek? m ρ <;> simp [henv] at hv)
    (fun body ρ _ => by
      intro c hv
      simp [symValToCek?, asConstVal, Proj.fail, pcHolds] at hv ⊢
      cases henv : symEnvToCek? m ρ <;> simp [henv] at hv)
    (fun b args ea _ => by
      intro c hv
      simp [symValToCek?, asConstVal, Proj.fail, pcHolds] at hv ⊢
      cases hargs : symValListToCekList? m args <;> simp [hargs] at hv)
    trivial
    (fun _ _ _ _ => trivial)
    v) hv

theorem unitGuard_sound {m : SmtSem.Model} {u : SymVal} {cv : CekValue}
    (hu : symValToCek? m u = some cv)
    (hg : pcHolds m (unitGuard u) = true) :
    cv = .VCon .Unit := by
  cases u with
  | const c =>
      cases c <;> simp [unitGuard, pcHolds, symValToCek?, symConstToCek?] at hu hg ⊢
      · exact hu.symm
  | dyn e =>
      simp [unitGuard, pcHolds, symValToCek?] at hu hg
      have he := Moist.SMT.Semantics.evalBoolIs_isVUnit_true hg
      simp [he, semValToCek?, semValToConst?] at hu
      exact hu.symm
  | pair a b =>
      simp [unitGuard, pcHolds] at hg
  | constr tag fields =>
      simp [unitGuard, pcHolds] at hg
  | lam body ρ =>
      simp [unitGuard, pcHolds] at hg
  | delay body ρ =>
      simp [unitGuard, pcHolds] at hg
  | builtin b args ea =>
      simp [unitGuard, pcHolds] at hg

theorem semValToCek_unit {v : SmtSem.Val}
    (h : semValToCek? v = some (.VCon .Unit)) : v = .unit := by
  cases v with
  | int i =>
      simp [semValToCek?, semValToConst?] at h
  | bytes bs =>
      simp [semValToCek?, semValToConst?] at h
  | string s =>
      simp [semValToCek?, semValToConst?] at h
  | bool b =>
      simp [semValToCek?, semValToConst?] at h
  | unit =>
      rfl
  | list xs =>
      simp [semValToCek?, semValToConst?] at h
      cases hcs : semValListToConstList? xs <;> simp [hcs] at h
  | dataList xs =>
      simp [semValToCek?, semValToConst?] at h
  | pairDataList xs =>
      simp [semValToCek?, semValToConst?] at h
  | pair a b =>
      simp [semValToCek?, semValToConst?] at h
      cases ha : semValToConst? a <;> simp [ha] at h
      cases hb : semValToConst? b <;> simp [hb] at h
  | pairData a b =>
      simp [semValToCek?, semValToConst?] at h
  | data d =>
      simp [semValToCek?, semValToConst?] at h
  | array xs =>
      simp [semValToCek?, semValToConst?] at h
      cases hcs : semValListToConstList? xs <;> simp [hcs] at h
  | g1 g =>
      simp [semValToCek?, semValToConst?] at h
  | g2 g =>
      simp [semValToCek?, semValToConst?] at h
  | ml r =>
      simp [semValToCek?, semValToConst?] at h
  | constr tag fields =>
      simp [semValToCek?] at h
      rcases h with ⟨_, hvs⟩
      cases hv : semValListToCekList? fields <;> simp [hv] at hvs

theorem symConstToCek_unit {m : SmtSem.Model} {c : SymConst}
    (h : symConstToCek? m c = some (.VCon .Unit)) : c = .unit := by
  cases c with
  | integer e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e with
      | none => simp [he] at h
      | some sv => cases sv <;> simp [he] at h
  | bytes e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e with
      | none => simp [he] at h
      | some sv => cases sv <;> simp [he] at h
  | string e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e with
      | none => simp [he] at h
      | some sv => cases sv <;> simp [he] at h
  | bool e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e with
      | none => simp [he] at h
      | some sv => cases sv <;> simp [he] at h
  | unit =>
      rfl
  | data e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e with
      | none => simp [he] at h
      | some sv => cases sv <;> simp [he] at h
  | constList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e with
      | none => simp [he] at h
      | some sv =>
          cases sv <;> simp [he] at h
          case valList xs =>
            cases hcs : semValListToConstList? xs <;> simp [hcs] at h
  | dataList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e with
      | none => simp [he] at h
      | some sv => cases sv <;> simp [he] at h
  | pairDataList e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e with
      | none => simp [he] at h
      | some sv => cases sv <;> simp [he] at h
  | pairData a b =>
      simp [symConstToCek?] at h
      cases ha : SmtSem.eval m a with
      | none => simp [ha] at h
      | some sva =>
          cases hb : SmtSem.eval m b with
          | none => simp [ha, hb] at h
          | some svb =>
              cases sva <;> cases svb <;> simp [ha, hb] at h
  | array e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e with
      | none => simp [he] at h
      | some sv =>
          cases sv <;> simp [he] at h
          case valList xs =>
            cases hcs : semValListToConstList? xs <;> simp [hcs] at h
  | g1 e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e with
      | none => simp [he] at h
      | some sv => cases sv <;> simp [he] at h
  | g2 e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e with
      | none => simp [he] at h
      | some sv => cases sv <;> simp [he] at h
  | ml e =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e with
      | none => simp [he] at h
      | some sv => cases sv <;> simp [he] at h

theorem unitGuard_complete {m : SmtSem.Model} {u : SymVal}
    (hu : symValToCek? m u = some (.VCon .Unit)) :
    pcHolds m (unitGuard u) = true := by
  cases u with
  | const c =>
      have hc : c = .unit := symConstToCek_unit (m := m)
        (by simpa [symValToCek?] using hu)
      subst c
      simp [unitGuard, pcHolds]
  | dyn e =>
      simp [unitGuard, pcHolds, symValToCek?] at hu ⊢
      cases he : SmtSem.eval m e with
      | none =>
          simp [he] at hu
      | some sv =>
          cases sv with
          | val v =>
              have hv : v = .unit := semValToCek_unit (by
                simpa [he] using hu)
              subst v
              exact Moist.SMT.Semantics.evalBoolIs_isVUnit_true_of_val_unit he
          | bool b =>
              simp [he] at hu
          | int i =>
              simp [he] at hu
          | string s =>
              simp [he] at hu
          | bytes bs =>
              simp [he] at hu
          | data d =>
              simp [he] at hu
          | dataList xs =>
              simp [he] at hu
          | dataPairList xs =>
              simp [he] at hu
          | valList xs =>
              simp [he] at hu
          | g1 g =>
              simp [he] at hu
          | g2 g =>
              simp [he] at hu
          | ml r =>
              simp [he] at hu
  | pair a b =>
      simp [symValToCek?] at hu
      cases ha : symValToCek? m a <;> simp [ha] at hu
      cases hb : symValToCek? m b <;> simp [hb] at hu
      split at hu <;> simp at hu
  | constr tag fields =>
      simp [symValToCek?] at hu
      cases ht : SmtSem.eval m tag <;> simp [ht] at hu
      split at hu <;> simp at hu
      cases hvs : symValListToCekList? m fields <;> simp [hvs] at hu
  | lam body ρ =>
      simp [symValToCek?] at hu
      cases henv : symEnvToCek? m ρ <;> simp [henv] at hu
  | delay body ρ =>
      simp [symValToCek?] at hu
      cases henv : symEnvToCek? m ρ <;> simp [henv] at hu
  | builtin b args ea =>
      simp [symValToCek?] at hu
      cases hargs : symValListToCekList? m args <;> simp [hargs] at hu

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_AddInteger_eq (b a : SymVal) :
    evalBuiltinSym .AddInteger [b, a] =
      checkedConst (Proj.map2 SExpr.add (asInt a) (asInt b)) .integer := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_SubtractInteger_eq (b a : SymVal) :
    evalBuiltinSym .SubtractInteger [b, a] =
      checkedConst (Proj.map2 SExpr.sub (asInt a) (asInt b)) .integer := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_MultiplyInteger_eq (b a : SymVal) :
    evalBuiltinSym .MultiplyInteger [b, a] =
      checkedConst (Proj.map2 SExpr.mul (asInt a) (asInt b)) .integer := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_DivideInteger_eq (b a : SymVal) :
    evalBuiltinSym .DivideInteger [b, a] =
      (let p := Proj.map2 (fun a b => (a, b)) (asInt a) (asInt b)
       checked2 p fun (a, b) =>
        [.ok (divisionGuard b) (.const (.integer (.app "uplc_div" [a, b]))),
         .error (SExpr.not (divisionGuard b))]) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_QuotientInteger_eq (b a : SymVal) :
    evalBuiltinSym .QuotientInteger [b, a] =
      (let p := Proj.map2 (fun a b => (a, b)) (asInt a) (asInt b)
       checked2 p fun (a, b) =>
        [.ok (divisionGuard b) (.const (.integer (.app "uplc_tdiv" [a, b]))),
         .error (SExpr.not (divisionGuard b))]) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_RemainderInteger_eq (b a : SymVal) :
    evalBuiltinSym .RemainderInteger [b, a] =
      (let p := Proj.map2 (fun a b => (a, b)) (asInt a) (asInt b)
       checked2 p fun (a, b) =>
        [.ok (divisionGuard b) (.const (.integer (.app "uplc_tmod" [a, b]))),
         .error (SExpr.not (divisionGuard b))]) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_ModInteger_eq (b a : SymVal) :
    evalBuiltinSym .ModInteger [b, a] =
      (let p := Proj.map2 (fun a b => (a, b)) (asInt a) (asInt b)
       checked2 p fun (a, b) =>
        [.ok (divisionGuard b) (.const (.integer (.app "uplc_mod" [a, b]))),
         .error (SExpr.not (divisionGuard b))]) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_EqualsInteger_eq (b a : SymVal) :
    evalBuiltinSym .EqualsInteger [b, a] =
      checkedBool (Proj.map2 SExpr.eq (asInt a) (asInt b)) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_LessThanInteger_eq (b a : SymVal) :
    evalBuiltinSym .LessThanInteger [b, a] =
      checkedBool (Proj.map2 SExpr.lt (asInt a) (asInt b)) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_LessThanEqualsInteger_eq (b a : SymVal) :
    evalBuiltinSym .LessThanEqualsInteger [b, a] =
      checkedBool (Proj.map2 SExpr.le (asInt a) (asInt b)) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_AppendByteString_eq (b a : SymVal) :
    evalBuiltinSym .AppendByteString [b, a] =
      checkedConst (Proj.map2 SExpr.seqAppend (asBytes a) (asBytes b)) .bytes := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_ConsByteString_eq (bs n : SymVal) :
    evalBuiltinSym .ConsByteString [bs, n] =
      (let p := Proj.map2 (fun n bs => (n, bs)) (asInt n) (asBytes bs)
       checked2 p fun (n, bs) =>
        let inByte := SExpr.and (SExpr.ge n (.int 0)) (SExpr.le n (.int 255))
        [.ok inByte (.const (.bytes (SExpr.seqAppend (SExpr.seqUnit n) bs))),
         .error (SExpr.not inByte)]) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_SliceByteString_eq (bs len start : SymVal) :
    evalBuiltinSym .SliceByteString [bs, len, start] =
      (let p := Proj.map3 (fun start len bs => (start, len, bs))
        (asInt start) (asInt len) (asBytes bs)
       checkedConst (p.map fun (start, len, bs) =>
        let s := SExpr.ite (SExpr.lt start (.int 0)) (.int 0) start
        let l := SExpr.ite (SExpr.lt len (.int 0)) (.int 0) len
        SExpr.seqExtract bs s l) .bytes) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_LengthOfByteString_eq (bs : SymVal) :
    evalBuiltinSym .LengthOfByteString [bs] =
      checkedConst ((asBytes bs).map SExpr.seqLen) .integer := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_IndexByteString_eq (idx bs : SymVal) :
    evalBuiltinSym .IndexByteString [idx, bs] =
      (let p := Proj.map2 (fun bs idx => (bs, idx)) (asBytes bs) (asInt idx)
       checked2 p fun (bs, idx) =>
        let inRange := SExpr.and (SExpr.ge idx (.int 0)) (SExpr.lt idx (SExpr.seqLen bs))
        [.ok inRange (.const (.integer (SExpr.seqNth bs idx))),
         .error (SExpr.not inRange)]) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_EqualsByteString_eq (b a : SymVal) :
    evalBuiltinSym .EqualsByteString [b, a] =
      checkedBool (Proj.map2 SExpr.eq (asBytes a) (asBytes b)) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_LessThanByteString_eq (b a : SymVal) :
    evalBuiltinSym .LessThanByteString [b, a] =
      checkedBool (Proj.map2 (fun a b => .app "bytes_lt" [a, b])
        (asBytes a) (asBytes b)) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_LessThanEqualsByteString_eq (b a : SymVal) :
    evalBuiltinSym .LessThanEqualsByteString [b, a] =
      checkedBool (Proj.map2 (fun a b => .app "bytes_le" [a, b])
        (asBytes a) (asBytes b)) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_AppendString_eq (b a : SymVal) :
    evalBuiltinSym .AppendString [b, a] =
      checkedConst (Proj.map2 SExpr.strAppend (asString a) (asString b)) .string := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_EqualsString_eq (b a : SymVal) :
    evalBuiltinSym .EqualsString [b, a] =
      checkedBool (Proj.map2 SExpr.eq (asString a) (asString b)) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_EncodeUtf8_eq (s : SymVal) :
    evalBuiltinSym .EncodeUtf8 [s] =
      checkedConst ((asString s).map fun x => .app "uplc_encodeUtf8" [x]) .bytes := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_DecodeUtf8_eq (bs : SymVal) :
    evalBuiltinSym .DecodeUtf8 [bs] =
      checked2 (asBytes bs) fun b =>
        [.ok (.app "valid_utf8" [b]) (.const (.string (.app "uplc_decodeUtf8" [b]))),
         .error (SExpr.not (.app "valid_utf8" [b]))] := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_IfThenElse_eq (elseV thenV cond : SymVal) :
    evalBuiltinSym .IfThenElse [elseV, thenV, cond] =
      (let c := asBool cond
       [.ok (SExpr.and c.guard c.val) thenV,
        .ok (SExpr.and c.guard (SExpr.not c.val)) elseV,
        .error (SExpr.not c.guard)]) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_Trace_eq (result msg : SymVal) :
    evalBuiltinSym .Trace [result, msg] =
      checked2 (asString msg) fun _ => ok result := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_MkNilData_eq (u : SymVal) :
    evalBuiltinSym .MkNilData [u] =
      (let g := unitGuard u
       [.ok g (.const (.dataList (.app "DNil" []))), .error (SExpr.not g)]) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_MkNilPairData_eq (u : SymVal) :
    evalBuiltinSym .MkNilPairData [u] =
      (let g := unitGuard u
       [.ok g (.const (.pairDataList (.app "DPNil" []))), .error (SExpr.not g)]) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_ConstrData_eq (fields tag : SymVal) :
    evalBuiltinSym .ConstrData [fields, tag] =
      checkedConst
        (Proj.map2 (fun tag fields => .app "DConstr" [tag, fields])
          (asInt tag) (asDataList fields)) .data := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_MapData_eq (ps : SymVal) :
    evalBuiltinSym .MapData [ps] =
      checkedConst ((asPairDataList ps).map fun ps => .app "DMap" [ps]) .data := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_ListData_eq (xs : SymVal) :
    evalBuiltinSym .ListData [xs] =
      checkedConst ((asDataList xs).map fun xs => .app "DList" [xs]) .data := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_IData_eq (i : SymVal) :
    evalBuiltinSym .IData [i] =
      checkedConst ((asInt i).map fun i => .app "DI" [i]) .data := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_BData_eq (bs : SymVal) :
    evalBuiltinSym .BData [bs] =
      checkedConst ((asBytes bs).map fun bs => .app "DB" [bs]) .data := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_SerializeData_eq (d : SymVal) :
    evalBuiltinSym .SerializeData [d] =
      checkedConst ((asData d).map fun d => .app "uplc_serializeData" [d]) .bytes := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_EqualsData_eq (b a : SymVal) :
    evalBuiltinSym .EqualsData [b, a] =
      checkedBool (Proj.map2 SExpr.eq (asData a) (asData b)) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_MkPairData_eq (b a : SymVal) :
    evalBuiltinSym .MkPairData [b, a] =
      checked1 (Proj.map2 (fun a b => (a, b)) (asData a) (asData b))
        (fun (a, b) => SymVal.const (SymConst.pairData a b)) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_UnConstrData_eq (dVal : SymVal) :
    evalBuiltinSym .UnConstrData [dVal] =
      (let d := asData dVal
       checked2 d fun d =>
        let is := SExpr.isCtor "DConstr" d
        [.ok is (.const (.pairData
          (.app "DI" [.app "dataConstrTag" [d]])
          (.app "DList" [.app "dataConstrFields" [d]]))),
         .error (SExpr.not is)]) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_UnMapData_eq (dVal : SymVal) :
    evalBuiltinSym .UnMapData [dVal] =
      (let d := asData dVal
       checked2 d fun d =>
        let is := SExpr.isCtor "DMap" d
        [.ok is (.const (.pairDataList (.app "dataMapEntries" [d]))),
         .error (SExpr.not is)]) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_UnListData_eq (dVal : SymVal) :
    evalBuiltinSym .UnListData [dVal] =
      (let d := asData dVal
       checked2 d fun d =>
        let is := SExpr.isCtor "DList" d
        [.ok is (.const (.dataList (.app "dataListItems" [d]))),
         .error (SExpr.not is)]) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_UnIData_eq (dVal : SymVal) :
    evalBuiltinSym .UnIData [dVal] =
      (let d := asData dVal
       checked2 d fun d =>
        let is := SExpr.isCtor "DI" d
        [.ok is (.const (.integer (.app "dataInt" [d]))),
         .error (SExpr.not is)]) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_UnBData_eq (dVal : SymVal) :
    evalBuiltinSym .UnBData [dVal] =
      (let d := asData dVal
       checked2 d fun d =>
        let is := SExpr.isCtor "DB" d
        [.ok is (.const (.bytes (.app "dataBytes" [d]))),
         .error (SExpr.not is)]) := by
  rfl

def BuiltinOkSound (b : BuiltinFun) : Prop :=
  ∀ {m : SmtSem.Model} {args : List SymVal} {cargs : List CekValue}
    {pc : SExpr} {v : SymVal},
    symValListToCekList? m args = some cargs →
    symValsNoOpaqueForSoundness args = true →
    Outcome.ok pc v ∈ evalBuiltinSym b args →
    pcHolds m pc = true →
    ∃ cv, symValToCek? m v = some cv ∧
      symValNoOpaqueForSoundness v = true ∧
      Moist.CEK.evalBuiltin b cargs = some cv

def BuiltinErrorSound (b : BuiltinFun) : Prop :=
  ∀ {m : SmtSem.Model} {args : List SymVal} {cargs : List CekValue} {out : Outcome},
    symValListToCekList? m args = some cargs →
    out ∈ evalBuiltinSym b args →
    outcomeErrorActive m out = true →
    Moist.CEK.evalBuiltin b cargs = none

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_AddInteger : BuiltinOkSound .AddInteger := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_AddInteger_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asInt a).guard (asInt b).guard)
                  (SymVal.const (SymConst.integer
                    (SExpr.add (asInt a).val (asInt b).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt a).guard (asInt b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt a).guard (asInt b).guard).mp hpc
                obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                refine ⟨.VCon (.Integer (ia + ib)), ?_, ?_, ?_⟩
                ·
                  have hadd := Moist.SMT.Semantics.eval_add_of (m := m)
                    (a := (asInt a).val) (b := (asInt b).val)
                    (x := ia) (y := ib) hea heb
                  change SmtSem.eval m (SExpr.add (asInt a).val (asInt b).val) =
                    some (Moist.SMT.Semantics.SVal.int (ia + ib)) at hadd
                  simp [symValToCek?, symConstToCek?, hadd]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_SubtractInteger : BuiltinOkSound .SubtractInteger := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_SubtractInteger_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asInt a).guard (asInt b).guard)
                  (SymVal.const (SymConst.integer
                    (SExpr.sub (asInt a).val (asInt b).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt a).guard (asInt b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt a).guard (asInt b).guard).mp hpc
                obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                refine ⟨.VCon (.Integer (ia - ib)), ?_, ?_, ?_⟩
                ·
                  have hsub := Moist.SMT.Semantics.eval_sub_of (m := m)
                    (a := (asInt a).val) (b := (asInt b).val)
                    (x := ia) (y := ib) hea heb
                  change SmtSem.eval m (SExpr.sub (asInt a).val (asInt b).val) =
                    some (Moist.SMT.Semantics.SVal.int (ia - ib)) at hsub
                  simp [symValToCek?, symConstToCek?, hsub]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_MultiplyInteger : BuiltinOkSound .MultiplyInteger := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_MultiplyInteger_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asInt a).guard (asInt b).guard)
                  (SymVal.const (SymConst.integer
                    (SExpr.mul (asInt a).val (asInt b).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt a).guard (asInt b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt a).guard (asInt b).guard).mp hpc
                obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                refine ⟨.VCon (.Integer (ia * ib)), ?_, ?_, ?_⟩
                ·
                  have hmul := Moist.SMT.Semantics.eval_mul_of (m := m)
                    (a := (asInt a).val) (b := (asInt b).val)
                    (x := ia) (y := ib) hea heb
                  change SmtSem.eval m (SExpr.mul (asInt a).val (asInt b).val) =
                    some (Moist.SMT.Semantics.SVal.int (ia * ib)) at hmul
                  simp [symValToCek?, symConstToCek?, hmul]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_DivideInteger : BuiltinOkSound .DivideInteger := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_DivideInteger_eq b a] at hmem
              have hpath := checked2_path_ok hmem hpc
              rcases hpath with ⟨innerPc, hinner, _hpcEq, hpArgs, hpDiv⟩
              simp only [List.mem_cons, List.not_mem_nil] at hinner
              rcases hinner with hinner | hinner
              · injection hinner with hinnerPcEq hvEq
                subst innerPc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt a).guard (asInt b).guard).mp hpArgs
                obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                have hne : (ib == 0) = false :=
                  pcHolds_ne_int_zero heb hpDiv
                refine ⟨.VCon (.Integer (Moist.Plutus.uplcIntegerDiv ia ib)),
                  ?_, ?_, ?_⟩
                ·
                  have hdiv := Moist.SMT.Semantics.eval_uplc_div_of
                    (m := m) (a := (asInt a).val) (b := (asInt b).val)
                    (x := ia) (y := ib) hea heb hne
                  simpa [symValToCek?, symConstToCek?, Proj.map2, hdiv]
                · simp [symValNoOpaqueForSoundness]
                ·
                  have hneq : ib ≠ 0 := by
                    intro hz
                    subst ib
                    simp at hne
                  have hconst := Moist.CEK.evalBuiltinConst_DivideInteger_of
                    (a := ia) (b := ib) hne
                  simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
                    Moist.CEK.extractConsts, hconst,
                    Moist.CEK.builtinIntegerDiv, hneq]
              · rcases hinner with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_QuotientInteger : BuiltinOkSound .QuotientInteger := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_QuotientInteger_eq b a] at hmem
              have hpath := checked2_path_ok hmem hpc
              rcases hpath with ⟨innerPc, hinner, _hpcEq, hpArgs, hpDiv⟩
              simp only [List.mem_cons, List.not_mem_nil] at hinner
              rcases hinner with hinner | hinner
              · injection hinner with hinnerPcEq hvEq
                subst innerPc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt a).guard (asInt b).guard).mp hpArgs
                obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                have hne : (ib == 0) = false :=
                  pcHolds_ne_int_zero heb hpDiv
                refine ⟨.VCon (.Integer (Moist.Plutus.uplcIntegerTDiv ia ib)),
                  ?_, ?_, ?_⟩
                ·
                  have hdiv := Moist.SMT.Semantics.eval_uplc_tdiv_of
                    (m := m) (a := (asInt a).val) (b := (asInt b).val)
                    (x := ia) (y := ib) hea heb hne
                  simpa [symValToCek?, symConstToCek?, Proj.map2, hdiv]
                · simp [symValNoOpaqueForSoundness]
                ·
                  have hneq : ib ≠ 0 := by
                    intro hz
                    subst ib
                    simp at hne
                  have hconst := Moist.CEK.evalBuiltinConst_QuotientInteger_of
                    (a := ia) (b := ib) hne
                  simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
                    Moist.CEK.extractConsts, hconst,
                    Moist.CEK.builtinIntegerTDiv, hneq]
              · rcases hinner with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_RemainderInteger : BuiltinOkSound .RemainderInteger := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_RemainderInteger_eq b a] at hmem
              have hpath := checked2_path_ok hmem hpc
              rcases hpath with ⟨innerPc, hinner, _hpcEq, hpArgs, hpDiv⟩
              simp only [List.mem_cons, List.not_mem_nil] at hinner
              rcases hinner with hinner | hinner
              · injection hinner with hinnerPcEq hvEq
                subst innerPc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt a).guard (asInt b).guard).mp hpArgs
                obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                have hne : (ib == 0) = false :=
                  pcHolds_ne_int_zero heb hpDiv
                refine ⟨.VCon (.Integer (Moist.Plutus.uplcIntegerTMod ia ib)),
                  ?_, ?_, ?_⟩
                ·
                  have hmod := Moist.SMT.Semantics.eval_uplc_tmod_of
                    (m := m) (a := (asInt a).val) (b := (asInt b).val)
                    (x := ia) (y := ib) hea heb hne
                  simpa [symValToCek?, symConstToCek?, Proj.map2, hmod]
                · simp [symValNoOpaqueForSoundness]
                ·
                  have hneq : ib ≠ 0 := by
                    intro hz
                    subst ib
                    simp at hne
                  have hconst := Moist.CEK.evalBuiltinConst_RemainderInteger_of
                    (a := ia) (b := ib) hne
                  simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
                    Moist.CEK.extractConsts, hconst,
                    Moist.CEK.builtinIntegerTMod, hneq]
              · rcases hinner with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_ModInteger : BuiltinOkSound .ModInteger := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_ModInteger_eq b a] at hmem
              have hpath := checked2_path_ok hmem hpc
              rcases hpath with ⟨innerPc, hinner, _hpcEq, hpArgs, hpDiv⟩
              simp only [List.mem_cons, List.not_mem_nil] at hinner
              rcases hinner with hinner | hinner
              · injection hinner with hinnerPcEq hvEq
                subst innerPc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt a).guard (asInt b).guard).mp hpArgs
                obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                have hne : (ib == 0) = false :=
                  pcHolds_ne_int_zero heb hpDiv
                refine ⟨.VCon (.Integer (Moist.Plutus.uplcIntegerMod ia ib)),
                  ?_, ?_, ?_⟩
                ·
                  have hmod := Moist.SMT.Semantics.eval_uplc_mod_of
                    (m := m) (a := (asInt a).val) (b := (asInt b).val)
                    (x := ia) (y := ib) hea heb hne
                  simpa [symValToCek?, symConstToCek?, Proj.map2, hmod]
                · simp [symValNoOpaqueForSoundness]
                ·
                  have hneq : ib ≠ 0 := by
                    intro hz
                    subst ib
                    simp at hne
                  have hconst := Moist.CEK.evalBuiltinConst_ModInteger_of
                    (a := ia) (b := ib) hne
                  simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
                    Moist.CEK.extractConsts, hconst,
                    Moist.CEK.builtinIntegerMod, hneq]
              · rcases hinner with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_EqualsInteger : BuiltinOkSound .EqualsInteger := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_EqualsInteger_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asInt a).guard (asInt b).guard)
                  (SymVal.const (SymConst.bool
                    (SExpr.eq (asInt a).val (asInt b).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt a).guard (asInt b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt a).guard (asInt b).guard).mp hpc
                obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                refine ⟨.VCon (.Bool (ia == ib)), ?_, ?_, ?_⟩
                ·
                  have heq := Moist.SMT.Semantics.eval_eq_int_of (m := m)
                    (a := (asInt a).val) (b := (asInt b).val)
                    (x := ia) (y := ib) hea heb
                  change SmtSem.eval m (SExpr.eq (asInt a).val (asInt b).val) =
                    some (Moist.SMT.Semantics.SVal.bool (ia == ib)) at heq
                  simp [symValToCek?, symConstToCek?, heq]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_LessThanInteger : BuiltinOkSound .LessThanInteger := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_LessThanInteger_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asInt a).guard (asInt b).guard)
                  (SymVal.const (SymConst.bool
                    (SExpr.lt (asInt a).val (asInt b).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt a).guard (asInt b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt a).guard (asInt b).guard).mp hpc
                obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                refine ⟨.VCon (.Bool (ia < ib)), ?_, ?_, ?_⟩
                ·
                  have hlt := Moist.SMT.Semantics.eval_lt_of (m := m)
                    (a := (asInt a).val) (b := (asInt b).val)
                    (x := ia) (y := ib) hea heb
                  change SmtSem.eval m (SExpr.lt (asInt a).val (asInt b).val) =
                    some (Moist.SMT.Semantics.SVal.bool (ia < ib)) at hlt
                  simp [symValToCek?, symConstToCek?, hlt]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_LessThanEqualsInteger :
    BuiltinOkSound .LessThanEqualsInteger := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_LessThanEqualsInteger_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asInt a).guard (asInt b).guard)
                  (SymVal.const (SymConst.bool
                    (SExpr.le (asInt a).val (asInt b).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt a).guard (asInt b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt a).guard (asInt b).guard).mp hpc
                obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                refine ⟨.VCon (.Bool (ia <= ib)), ?_, ?_, ?_⟩
                ·
                  have hle := Moist.SMT.Semantics.eval_le_of (m := m)
                    (a := (asInt a).val) (b := (asInt b).val)
                    (x := ia) (y := ib) hea heb
                  change SmtSem.eval m (SExpr.le (asInt a).val (asInt b).val) =
                    some (Moist.SMT.Semantics.SVal.bool (ia <= ib)) at hle
                  simp [symValToCek?, symConstToCek?, hle]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_AppendByteString : BuiltinOkSound .AppendByteString := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_AppendByteString_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asBytes a).guard (asBytes b).guard)
                  (SymVal.const (SymConst.bytes
                    (SExpr.seqAppend (asBytes a).val (asBytes b).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asBytes a).guard (asBytes b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asBytes a).guard (asBytes b).guard).mp hpc
                obtain ⟨bsa, rfl, hea⟩ := asBytes_sound ha hp.1
                obtain ⟨bsb, rfl, heb⟩ := asBytes_sound hb hp.2
                refine ⟨.VCon (.ByteString (bsa ++ bsb)), ?_, ?_, ?_⟩
                ·
                  have happ := Moist.SMT.Semantics.eval_seqAppend_of (m := m)
                    (a := (asBytes a).val) (b := (asBytes b).val)
                    (x := bsa) (y := bsb) hea heb
                  change SmtSem.eval m (SExpr.seqAppend (asBytes a).val (asBytes b).val) =
                    some (Moist.SMT.Semantics.SVal.bytes (bsa ++ bsb)) at happ
                  simp [symValToCek?, symConstToCek?, happ]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_ConsByteString : BuiltinOkSound .ConsByteString := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons bsSym rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons nSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_ConsByteString_eq bsSym nSym] at hmem
              have hpath := checked2_path_ok hmem hpc
              rcases hpath with ⟨innerPc, hinner, _hpcEq, hpArgs, hpByte⟩
              simp only [List.mem_cons, List.not_mem_nil] at hinner
              rcases hinner with hinner | hinner
              · injection hinner with hinnerPcEq hvEq
                subst innerPc
                subst v
                obtain ⟨cbs, cn, hbsArg, hnArg, rfl⟩ :=
                  symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt nSym).guard (asBytes bsSym).guard).mp hpArgs
                obtain ⟨n, rfl, hnEval⟩ := asInt_sound hnArg hp.1
                obtain ⟨bs, rfl, hbsEval⟩ := asBytes_sound hbsArg hp.2
                have hpRange :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (SExpr.ge (asInt nSym).val (.int 0))
                    (SExpr.le (asInt nSym).val (.int 255))).mp hpByte
                have hge : 0 ≤ n :=
                  pcHolds_ge_int hnEval
                    (by simp [Moist.SMT.Semantics.eval]) hpRange.1
                have hle : n ≤ 255 :=
                  pcHolds_le_int hnEval
                    (by simp [Moist.SMT.Semantics.eval]) hpRange.2
                refine ⟨.VCon (.ByteString (Moist.Plutus.bytesSingletonValue n ++ bs)),
                  ?_, ?_, ?_⟩
                ·
                  have hunit := Moist.SMT.Semantics.eval_seqUnit_of
                    (m := m) (e := (asInt nSym).val) hnEval hge hle
                  have happ := Moist.SMT.Semantics.eval_seqAppend_of (m := m)
                    (a := SExpr.seqUnit (asInt nSym).val)
                    (b := (asBytes bsSym).val)
                    (x := Moist.SMT.Semantics.bytesSingletonValue n)
                    (y := bs) hunit hbsEval
                  change SmtSem.eval m
                    (SExpr.seqAppend (SExpr.seqUnit (asInt nSym).val)
                      (asBytes bsSym).val) =
                    some (Moist.SMT.Semantics.SVal.bytes
                      (Moist.SMT.Semantics.bytesSingletonValue n ++ bs)) at happ
                  simp [symValToCek?, symConstToCek?, Proj.map2, happ,
                    Moist.SMT.Semantics.bytesSingletonValue]
                · simp [symValNoOpaqueForSoundness]
                ·
                  have hnlt : ¬ n < 0 := by
                    intro hn
                    exact (Int.not_le.mpr hn) hge
                  have hngt : ¬ n > 255 := by
                    intro hn
                    exact (Int.not_le.mpr hn) hle
                  simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
                    Moist.CEK.extractConsts, Moist.CEK.evalBuiltinConst,
                    hnlt, hngt]
              · rcases hinner with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_SliceByteString : BuiltinOkSound .SliceByteString := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons bsSym rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons lenSym rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons startSym rest3 =>
              cases rest3 with
              | nil =>
                  rw [evalBuiltinSym_SliceByteString_eq bsSym lenSym startSym] at hmem
                  change Outcome.ok pc v ∈
                    [Outcome.ok
                      (SExpr.all [(asInt startSym).guard, (asInt lenSym).guard,
                        (asBytes bsSym).guard])
                      (SymVal.const (SymConst.bytes
                        (SExpr.seqExtract (asBytes bsSym).val
                          (SExpr.ite (SExpr.lt (asInt startSym).val (.int 0))
                            (.int 0) (asInt startSym).val)
                          (SExpr.ite (SExpr.lt (asInt lenSym).val (.int 0))
                            (.int 0) (asInt lenSym).val)))),
                     Outcome.error (SExpr.not
                      (SExpr.all [(asInt startSym).guard, (asInt lenSym).guard,
                        (asBytes bsSym).guard]))] at hmem
                  simp only [List.mem_cons, List.not_mem_nil] at hmem
                  rcases hmem with hmem | hmem
                  · injection hmem with hpcEq hvEq
                    subst pc
                    subst v
                    obtain ⟨cbs, clen, cstart, hbsArg, hlenArg, hstartArg, rfl⟩ :=
                      symValListToCekList_triple hargs
                    have hp := pcHolds_all3 (m := m) hpc
                    obtain ⟨start, rfl, hstartEval⟩ :=
                      asInt_sound hstartArg hp.1
                    obtain ⟨len, rfl, hlenEval⟩ :=
                      asInt_sound hlenArg hp.2.1
                    obtain ⟨bs, rfl, hbsEval⟩ :=
                      asBytes_sound hbsArg hp.2.2
                    refine ⟨.VCon (.ByteString
                      (Moist.Plutus.bytesExtractValue bs start len)), ?_, ?_, ?_⟩
                    ·
                      have hstartClamp :=
                        eval_nonneg_clamp_int_of (m := m)
                          (e := (asInt startSym).val) hstartEval
                      have hlenClamp :=
                        eval_nonneg_clamp_int_of (m := m)
                          (e := (asInt lenSym).val) hlenEval
                      have hextract := Moist.SMT.Semantics.eval_seqExtract_of (m := m)
                        (bs := (asBytes bsSym).val)
                        (start := SExpr.ite
                          (SExpr.lt (asInt startSym).val (.int 0))
                          (.int 0) (asInt startSym).val)
                        (len := SExpr.ite
                          (SExpr.lt (asInt lenSym).val (.int 0))
                          (.int 0) (asInt lenSym).val)
                        (x := bs)
                        (s := if start < 0 then 0 else start)
                        (l := if len < 0 then 0 else len)
                        hbsEval hstartClamp hlenClamp
                      unfold Moist.SMT.Semantics.bytesExtractValue at hextract
                      rw [Moist.Plutus.bytesExtractValue_clamp bs start len] at hextract
                      change SmtSem.eval m
                        (SExpr.seqExtract (asBytes bsSym).val
                          (SExpr.ite (SExpr.lt (asInt startSym).val (.int 0))
                            (.int 0) (asInt startSym).val)
                          (SExpr.ite (SExpr.lt (asInt lenSym).val (.int 0))
                            (.int 0) (asInt lenSym).val)) =
                        some (Moist.SMT.Semantics.SVal.bytes
                          (Moist.Plutus.bytesExtractValue bs start len)) at hextract
                      simp [symValToCek?, symConstToCek?, hextract]
                    · simp [symValNoOpaqueForSoundness]
                    · rfl
                  · rcases hmem with hbad | hfalse
                    · cases hbad
                    · cases hfalse
              | cons _ _ =>
                  change Outcome.ok pc v ∈ err at hmem
                  simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_LengthOfByteString : BuiltinOkSound .LengthOfByteString := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons bsSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_LengthOfByteString_eq bsSym] at hmem
          change Outcome.ok pc v ∈
            [Outcome.ok (asBytes bsSym).guard
              (SymVal.const (SymConst.integer (SExpr.seqLen (asBytes bsSym).val))),
             Outcome.error (SExpr.not (asBytes bsSym).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · injection hmem with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨cbs, hbs, rfl⟩ := symValListToCekList_singleton hargs
            obtain ⟨bs, rfl, hbsEval⟩ := asBytes_sound hbs hpc
            refine ⟨.VCon (.Integer (Int.ofNat bs.size)), ?_, ?_, ?_⟩
            ·
              have hlen := Moist.SMT.Semantics.eval_seqLen_of (m := m)
                (a := (asBytes bsSym).val) hbsEval
              change SmtSem.eval m (SExpr.seqLen (asBytes bsSym).val) =
                some (Moist.SMT.Semantics.SVal.int (Int.ofNat bs.size)) at hlen
              simp [symValToCek?, symConstToCek?, hlen]
            · simp [symValNoOpaqueForSoundness]
            · rfl
          · rcases hmem with hbad | hfalse
            · cases hbad
            · cases hfalse
      | cons _ rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_IndexByteString : BuiltinOkSound .IndexByteString := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons idxSym rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons bsSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_IndexByteString_eq idxSym bsSym] at hmem
              have hpath := checked2_path_ok hmem hpc
              rcases hpath with ⟨innerPc, hinner, _hpcEq, hpArgs, hpRange⟩
              simp only [List.mem_cons, List.not_mem_nil] at hinner
              rcases hinner with hinner | hinner
              · injection hinner with hinnerPcEq hvEq
                subst innerPc
                subst v
                obtain ⟨cidx, cbs, hidxArg, hbsArg, rfl⟩ :=
                  symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asBytes bsSym).guard (asInt idxSym).guard).mp hpArgs
                obtain ⟨idx, rfl, hidxEval⟩ := asInt_sound hidxArg hp.2
                obtain ⟨bs, rfl, hbsEval⟩ := asBytes_sound hbsArg hp.1
                have hpRangeSplit :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (SExpr.ge (asInt idxSym).val (.int 0))
                    (SExpr.lt (asInt idxSym).val
                      (SExpr.seqLen (asBytes bsSym).val))).mp hpRange
                have hge : 0 ≤ idx :=
                  pcHolds_ge_int hidxEval
                    (by simp [Moist.SMT.Semantics.eval]) hpRangeSplit.1
                have hlenEval := Moist.SMT.Semantics.eval_seqLen_of (m := m)
                  (a := (asBytes bsSym).val) hbsEval
                change SmtSem.eval m (SExpr.seqLen (asBytes bsSym).val) =
                  some (Moist.SMT.Semantics.SVal.int (Int.ofNat bs.size)) at hlenEval
                have hlt : idx < Int.ofNat bs.size :=
                  pcHolds_lt_int hidxEval hlenEval hpRangeSplit.2
                refine ⟨.VCon (.Integer (Moist.Plutus.bytesNthValue bs idx)),
                  ?_, ?_, ?_⟩
                ·
                  have hnth := Moist.SMT.Semantics.eval_seqNth_of (m := m)
                    (bs := (asBytes bsSym).val) (idx := (asInt idxSym).val)
                    (x := bs) (i := idx) hbsEval hidxEval hge hlt
                  have hnth' :
                      SmtSem.eval m
                        (SExpr.seqNth (asBytes bsSym).val (asInt idxSym).val) =
                      some (Moist.SMT.Semantics.SVal.int
                        (Moist.Plutus.bytesNthValue bs idx)) := by
                    simpa [SExpr.seqNth, Moist.SMT.Semantics.bytesNthValue] using hnth
                  change (match SmtSem.eval m
                      (SExpr.seqNth (asBytes bsSym).val (asInt idxSym).val) with
                    | some (Moist.SMT.Semantics.SVal.int i) =>
                        some (CekValue.VCon (.Integer i))
                    | _ => none) =
                    some (CekValue.VCon
                      (.Integer (Moist.Plutus.bytesNthValue bs idx)))
                  rw [hnth']
                · simp [symValNoOpaqueForSoundness]
                ·
                  have hnlt : ¬ idx < 0 := by
                    intro hn
                    exact (Int.not_le.mpr hn) hge
                  have hnge : ¬ idx ≥ Int.ofNat bs.size := by
                    intro hn
                    exact (Int.not_le.mpr hlt) hn
                  have hnotUpper : ¬ Int.ofNat bs.size ≤ idx := by
                    exact Int.not_le.mpr hlt
                  have hnotUpper' : ¬ (↑(ByteArray.size bs) : Int) ≤ idx := by
                    simpa using hnotUpper
                  simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
                    Moist.CEK.extractConsts, Moist.CEK.evalBuiltinConst, hnlt]
                  rw [if_neg hnotUpper']
              · rcases hinner with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_EqualsByteString : BuiltinOkSound .EqualsByteString := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_EqualsByteString_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asBytes a).guard (asBytes b).guard)
                  (SymVal.const (SymConst.bool
                    (SExpr.eq (asBytes a).val (asBytes b).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asBytes a).guard (asBytes b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asBytes a).guard (asBytes b).guard).mp hpc
                obtain ⟨bsa, rfl, hea⟩ := asBytes_sound ha hp.1
                obtain ⟨bsb, rfl, heb⟩ := asBytes_sound hb hp.2
                refine ⟨.VCon (.Bool (bsa == bsb)), ?_, ?_, ?_⟩
                ·
                  have heq := Moist.SMT.Semantics.eval_eq_bytes_of (m := m)
                    (a := (asBytes a).val) (b := (asBytes b).val)
                    (x := bsa) (y := bsb) hea heb
                  change SmtSem.eval m (SExpr.eq (asBytes a).val (asBytes b).val) =
                    some (Moist.SMT.Semantics.SVal.bool (bsa == bsb)) at heq
                  simp [symValToCek?, symConstToCek?, heq]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_LessThanByteString : BuiltinOkSound .LessThanByteString := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_LessThanByteString_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asBytes a).guard (asBytes b).guard)
                  (SymVal.const (SymConst.bool
                    (.app "bytes_lt" [(asBytes a).val, (asBytes b).val]))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asBytes a).guard (asBytes b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asBytes a).guard (asBytes b).guard).mp hpc
                obtain ⟨bsa, rfl, hea⟩ := asBytes_sound ha hp.1
                obtain ⟨bsb, rfl, heb⟩ := asBytes_sound hb hp.2
                refine ⟨.VCon (.Bool (Moist.Plutus.bytesLt bsa bsb)), ?_, ?_, ?_⟩
                ·
                  have hlt := Moist.SMT.Semantics.eval_bytesLt_of (m := m)
                    (a := (asBytes a).val) (b := (asBytes b).val)
                    (x := bsa) (y := bsb) hea heb
                  change SmtSem.eval m
                    (.app "bytes_lt" [(asBytes a).val, (asBytes b).val]) =
                    some (Moist.SMT.Semantics.SVal.bool
                      (Moist.Plutus.bytesLt bsa bsb)) at hlt
                  simp [symValToCek?, symConstToCek?, hlt]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_LessThanEqualsByteString :
    BuiltinOkSound .LessThanEqualsByteString := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_LessThanEqualsByteString_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asBytes a).guard (asBytes b).guard)
                  (SymVal.const (SymConst.bool
                    (.app "bytes_le" [(asBytes a).val, (asBytes b).val]))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asBytes a).guard (asBytes b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asBytes a).guard (asBytes b).guard).mp hpc
                obtain ⟨bsa, rfl, hea⟩ := asBytes_sound ha hp.1
                obtain ⟨bsb, rfl, heb⟩ := asBytes_sound hb hp.2
                refine ⟨.VCon (.Bool (Moist.Plutus.bytesLe bsa bsb)), ?_, ?_, ?_⟩
                ·
                  have hle := Moist.SMT.Semantics.eval_bytesLe_of (m := m)
                    (a := (asBytes a).val) (b := (asBytes b).val)
                    (x := bsa) (y := bsb) hea heb
                  change SmtSem.eval m
                    (.app "bytes_le" [(asBytes a).val, (asBytes b).val]) =
                    some (Moist.SMT.Semantics.SVal.bool
                      (Moist.Plutus.bytesLe bsa bsb)) at hle
                  simp [symValToCek?, symConstToCek?, hle]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
axiom evalBuiltinSym_active_ok_Sha2_256 : BuiltinOkSound .Sha2_256
axiom evalBuiltinSym_active_ok_Sha3_256 : BuiltinOkSound .Sha3_256
axiom evalBuiltinSym_active_ok_Blake2b_256 : BuiltinOkSound .Blake2b_256
axiom evalBuiltinSym_active_ok_VerifyEd25519Signature : BuiltinOkSound .VerifyEd25519Signature
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_AppendString : BuiltinOkSound .AppendString := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_AppendString_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asString a).guard (asString b).guard)
                  (SymVal.const (SymConst.string
                    (SExpr.strAppend (asString a).val (asString b).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asString a).guard (asString b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asString a).guard (asString b).guard).mp hpc
                obtain ⟨sa, rfl, hea⟩ := asString_sound ha hp.1
                obtain ⟨sb, rfl, heb⟩ := asString_sound hb hp.2
                refine ⟨.VCon (.String (sa ++ sb)), ?_, ?_, ?_⟩
                ·
                  have happ := Moist.SMT.Semantics.eval_strAppend_of (m := m)
                    (a := (asString a).val) (b := (asString b).val)
                    (x := sa) (y := sb) hea heb
                  change SmtSem.eval m (SExpr.strAppend (asString a).val (asString b).val) =
                    some (Moist.SMT.Semantics.SVal.string (sa ++ sb)) at happ
                  simp [symValToCek?, symConstToCek?, happ]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_EqualsString : BuiltinOkSound .EqualsString := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_EqualsString_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asString a).guard (asString b).guard)
                  (SymVal.const (SymConst.bool
                    (SExpr.eq (asString a).val (asString b).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asString a).guard (asString b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asString a).guard (asString b).guard).mp hpc
                obtain ⟨sa, rfl, hea⟩ := asString_sound ha hp.1
                obtain ⟨sb, rfl, heb⟩ := asString_sound hb hp.2
                refine ⟨.VCon (.Bool (sa == sb)), ?_, ?_, ?_⟩
                ·
                  have heq := Moist.SMT.Semantics.eval_eq_string_of (m := m)
                    (a := (asString a).val) (b := (asString b).val)
                    (x := sa) (y := sb) hea heb
                  change SmtSem.eval m (SExpr.eq (asString a).val (asString b).val) =
                    some (Moist.SMT.Semantics.SVal.bool (sa == sb)) at heq
                  simp [symValToCek?, symConstToCek?, heq]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltin_DecodeUtf8_of_valid {bs : ByteArray}
    (h : String.validateUTF8 bs) :
    Moist.CEK.evalBuiltin .DecodeUtf8 [.VCon (.ByteString bs)] =
      some (.VCon (.String (String.fromUTF8 bs h))) := by
  change (match (if h' : String.validateUTF8 bs then
      some (Const.String (String.fromUTF8 bs h')) else none) with
    | some c => some (CekValue.VCon c)
    | none => none) =
      some (.VCon (.String (String.fromUTF8 bs h)))
  simp [h]

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_EncodeUtf8 : BuiltinOkSound .EncodeUtf8 := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons sSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_EncodeUtf8_eq sSym] at hmem
          change Outcome.ok pc v ∈
            [Outcome.ok (asString sSym).guard
              (SymVal.const (SymConst.bytes
                (.app "uplc_encodeUtf8" [(asString sSym).val]))),
             Outcome.error (SExpr.not (asString sSym).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · injection hmem with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨cs, hs, rfl⟩ := symValListToCekList_singleton hargs
            obtain ⟨s, rfl, hsEval⟩ := asString_sound hs hpc
            refine ⟨.VCon (.ByteString s.toUTF8), ?_, ?_, ?_⟩
            ·
              have henc := Moist.SMT.Semantics.eval_uplcEncodeUtf8_of
                (m := m) (e := (asString sSym).val) (s := s) hsEval
              simp [symValToCek?, symConstToCek?, henc]
            · simp [symValNoOpaqueForSoundness]
            · rfl
          · rcases hmem with hbad | hfalse
            · cases hbad
            · cases hfalse
      | cons extra rest2 =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_DecodeUtf8 : BuiltinOkSound .DecodeUtf8 := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons bsSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_DecodeUtf8_eq bsSym] at hmem
          have hpath := checked2_path_ok hmem hpc
          rcases hpath with ⟨innerPc, hinner, hpcEq, hguard, hinnerPc⟩
          simp only [List.mem_cons, List.not_mem_nil] at hinner
          rcases hinner with hinner | hinner
          · injection hinner with hinnerPcEq hvEq
            subst innerPc
            subst v
            obtain ⟨cbs, hbs, rfl⟩ := symValListToCekList_singleton hargs
            obtain ⟨bs, rfl, hbsEval⟩ := asBytes_sound hbs hguard
            have hvalid := Moist.SMT.Semantics.validUtf8_of_evalBoolIs_validUtf8_true
              (m := m) (e := (asBytes bsSym).val) (bs := bs) hbsEval
              (by simpa [pcHolds] using hinnerPc)
            refine ⟨.VCon (.String (String.fromUTF8 bs hvalid)), ?_, ?_, ?_⟩
            ·
              have hdec := Moist.SMT.Semantics.eval_uplcDecodeUtf8_of
                (m := m) (e := (asBytes bsSym).val) (bs := bs) hbsEval hvalid
              simp [symValToCek?, symConstToCek?, hdec]
            · simp [symValNoOpaqueForSoundness]
            · exact evalBuiltin_DecodeUtf8_of_valid hvalid
          · rcases hinner with hbad | hfalse
            · cases hbad
            · cases hfalse
      | cons extra rest2 =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_IfThenElse : BuiltinOkSound .IfThenElse := by
  intro m args cargs pc v hargs hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons elseV rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons thenV rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons cond rest3 =>
              cases rest3 with
              | nil =>
                  rw [evalBuiltinSym_IfThenElse_eq elseV thenV cond] at hmem
                  change Outcome.ok pc v ∈
                    [Outcome.ok (SExpr.and (asBool cond).guard (asBool cond).val) thenV,
                     Outcome.ok (SExpr.and (asBool cond).guard
                      (SExpr.not (asBool cond).val)) elseV,
                     Outcome.error (SExpr.not (asBool cond).guard)] at hmem
                  simp only [List.mem_cons, List.not_mem_nil] at hmem
                  obtain ⟨noElse, noThen, _noCond⟩ :=
                    symValsNoOpaque_triple hnoArgs
                  obtain ⟨celse, cthen, ccond, helse, hthen, hcond, rfl⟩ :=
                    symValListToCekList_triple hargs
                  rcases hmem with hthenBranch | hrest
                  · injection hthenBranch with hpcEq hvEq
                    subst pc
                    subst v
                    have hp :=
                      (Moist.SMT.Semantics.evalBoolIs_and_true m
                        (asBool cond).guard (asBool cond).val).mp hpc
                    have hcondCek := asBool_true_to_cek (m := m) (v := cond)
                      hp.1 hp.2
                    rw [hcond] at hcondCek
                    injection hcondCek with hccond
                    subst ccond
                    refine ⟨cthen, hthen, noThen, ?_⟩
                    simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough]
                  · rcases hrest with helseBranch | hbad
                    · injection helseBranch with hpcEq hvEq
                      subst pc
                      subst v
                      have hp :=
                        (Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asBool cond).guard
                          (SExpr.not (asBool cond).val)).mp hpc
                      have hfalse :=
                        (Moist.SMT.Semantics.evalBoolIs_not_true m
                          (asBool cond).val).mp hp.2
                      have hcondCek := asBool_false_to_cek (m := m) (v := cond)
                        hp.1 hfalse
                      rw [hcond] at hcondCek
                      injection hcondCek with hccond
                      subst ccond
                      refine ⟨celse, helse, noElse, ?_⟩
                      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough]
                    · rcases hbad with hbad | hfalse
                      · cases hbad
                      · cases hfalse
              | cons _ _ =>
                  change Outcome.ok pc v ∈ err at hmem
                  simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_ChooseUnit : BuiltinOkSound .ChooseUnit := by
  intro m args cargs pc v hargs hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons result rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons unitV rest2 =>
          cases rest2 with
          | nil =>
              obtain ⟨noResult, _noUnit⟩ := symValsNoOpaque_pair hnoArgs
              obtain ⟨cresult, cunit, hresult, hunit, rfl⟩ :=
                symValListToCekList_pair hargs
              cases unitV with
              | const c =>
                  cases c <;>
                    try
                      change Outcome.ok pc v ∈ err at hmem
                      simp [err] at hmem
                  case unit =>
                    change Outcome.ok pc v ∈ ok result at hmem
                    simp [ok] at hmem
                    rcases hmem with ⟨rfl, rfl⟩
                    have hunitCek := unitGuard_sound (m := m) (u := SymVal.const .unit)
                      hunit hpc
                    subst cunit
                    refine ⟨cresult, hresult, noResult, ?_⟩
                    simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough]
              | dyn e =>
                  change Outcome.ok pc v ∈
                    [Outcome.ok (SExpr.isCtor "VUnit" e) result,
                     Outcome.error (SExpr.not (SExpr.isCtor "VUnit" e))] at hmem
                  simp only [List.mem_cons, List.not_mem_nil] at hmem
                  rcases hmem with hmem | hbad
                  · injection hmem with hpcEq hvEq
                    subst pc
                    subst v
                    have hunitCek := unitGuard_sound (m := m) (u := SymVal.dyn e)
                      hunit hpc
                    subst cunit
                    refine ⟨cresult, hresult, noResult, ?_⟩
                    simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough]
                  · rcases hbad with hbad | hfalse
                    · cases hbad
                    · cases hfalse
              | pair a b =>
                  change Outcome.ok pc v ∈ err at hmem
                  simp [err] at hmem
              | constr tag fields =>
                  change Outcome.ok pc v ∈ err at hmem
                  simp [err] at hmem
              | lam body ρ =>
                  change Outcome.ok pc v ∈ err at hmem
                  simp [err] at hmem
              | delay body ρ =>
                  change Outcome.ok pc v ∈ err at hmem
                  simp [err] at hmem
              | builtin b bargs ea =>
                  change Outcome.ok pc v ∈ err at hmem
                  simp [err] at hmem
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_Trace : BuiltinOkSound .Trace := by
  intro m args cargs pc v hargs hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons result rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons msg rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_Trace_eq result msg] at hmem
              have hpath := checked2_path_ok hmem hpc
              rcases hpath with ⟨innerPc, hinner, _hpcEq, hmsgGuard, _hinnerPc⟩
              change Outcome.ok innerPc v ∈ ok result at hinner
              simp [ok] at hinner
              rcases hinner with ⟨rfl, rfl⟩
              obtain ⟨noResult, _noMsg⟩ := symValsNoOpaque_pair hnoArgs
              obtain ⟨cresult, cmsg, hresult, hmsg, rfl⟩ :=
                symValListToCekList_pair hargs
              obtain ⟨s, rfl, _hmsgEval⟩ := asString_sound hmsg hmsgGuard
              refine ⟨cresult, hresult, noResult, ?_⟩
              simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough]
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0

theorem evalBuiltinSym_active_ok_FstPair : BuiltinOkSound .FstPair := by
  intro m args cargs pc v hargs hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons p rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈
            (let pp := asPair p
             let pd := asPairData p
             [Outcome.ok pp.guard pp.val.1,
              Outcome.ok pd.guard (.const (.data pd.val.1)),
              Outcome.error (SExpr.not (SExpr.or pp.guard pd.guard))]) at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cp, hp, rfl⟩ := symValListToCekList_singleton hargs
          have hnoP := symValsNoOpaque_singleton hnoArgs
          rcases hmem with hpair | hpd | herr
          · injection hpair with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨a, b, rfl, hfst, _hsnd⟩ := asPair_sound hp hpc
            refine ⟨.VCon a, hfst, asPair_fst_noOpaque hnoP, ?_⟩
            exact Moist.CEK.evalBuiltin_FstPair_pair a b
          · injection hpd with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨a, b, rfl, hfst, _hsnd⟩ := asPairData_sound hp hpc
            refine ⟨.VCon (.Data a), ?_, by simp [symValNoOpaqueForSoundness], ?_⟩
            · simp [symValToCek?, symConstToCek?, hfst]
            · exact Moist.CEK.evalBuiltin_FstPair_pairData a b
          · rcases herr with herr | hfalse
            · cases herr
            · cases hfalse
      | cons _ _ =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem

theorem evalBuiltinSym_active_ok_SndPair : BuiltinOkSound .SndPair := by
  intro m args cargs pc v hargs hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons p rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈
            (let pp := asPair p
             let pd := asPairData p
             [Outcome.ok pp.guard pp.val.2,
              Outcome.ok pd.guard (.const (.data pd.val.2)),
              Outcome.error (SExpr.not (SExpr.or pp.guard pd.guard))]) at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cp, hp, rfl⟩ := symValListToCekList_singleton hargs
          have hnoP := symValsNoOpaque_singleton hnoArgs
          rcases hmem with hpair | hpd | herr
          · injection hpair with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨a, b, rfl, _hfst, hsnd⟩ := asPair_sound hp hpc
            refine ⟨.VCon b, hsnd, asPair_snd_noOpaque hnoP, ?_⟩
            exact Moist.CEK.evalBuiltin_SndPair_pair a b
          · injection hpd with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨a, b, rfl, _hfst, hsnd⟩ := asPairData_sound hp hpc
            refine ⟨.VCon (.Data b), ?_, by simp [symValNoOpaqueForSoundness], ?_⟩
            · simp [symValToCek?, symConstToCek?, hsnd]
            · exact Moist.CEK.evalBuiltin_SndPair_pairData a b
          · rcases herr with herr | hfalse
            · cases herr
            · cases hfalse
      | cons _ _ =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_ChooseList : BuiltinOkSound .ChooseList := by
  intro m args cargs pc v hargs hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons consCase rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons nilCase rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons xs rest3 =>
              cases rest3 with
              | nil =>
                  change Outcome.ok pc v ∈
                    (let dl := asDataList xs
                     let vl := asConstList xs
                     let dBranches :=
                       [Outcome.ok (SExpr.and dl.guard (SExpr.isCtor "DNil" dl.val))
                          nilCase,
                        Outcome.ok
                          (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val)))
                          consCase]
                     let vBranches :=
                       [Outcome.ok (SExpr.and vl.guard (SExpr.isCtor "VNil" vl.val))
                          nilCase,
                        Outcome.ok
                          (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))
                          consCase]
                     dBranches ++ vBranches ++
                       [Outcome.error (SExpr.not (SExpr.or dl.guard vl.guard))]) at hmem
                  simp only [List.mem_cons, List.not_mem_nil, List.mem_append] at hmem
                  obtain ⟨ccons, cnil, cxs, hcons, hnil, hxs, rfl⟩ :=
                    symValListToCekList_triple hargs
                  obtain ⟨hnoCons, hnoNil, _hnoXs⟩ :=
                    symValsNoOpaque_triple hnoArgs
                  rcases hmem with hdv | herr
                  · rcases hdv with hd | hv
                    · rcases hd with hdNil | hdRest
                      · injection hdNil with hpcEq hvEq
                        subst pc
                        subst v
                        have hp :=
                          (Moist.SMT.Semantics.evalBoolIs_and_true m
                            (asDataList xs).guard
                            (SExpr.isCtor "DNil" (asDataList xs).val)).mp hpc
                        obtain ⟨ds, rfl, hEval⟩ := asDataList_sound hxs hp.1
                        cases ds with
                        | nil =>
                            exact ⟨cnil, hnil, hnoNil,
                              Moist.CEK.evalBuiltin_ChooseList_dataList_nil cnil ccons⟩
                        | cons d ds =>
                            have hfalse :=
                              Moist.SMT.Semantics.evalBoolIs_isDNil_false_of_dataList_cons
                                hEval
                            exact False.elim (evalBoolIs_true_false_contra hp.2 hfalse)
                      · rcases hdRest with hdCons | hdFalse
                        · injection hdCons with hpcEq hvEq
                          subst pc
                          subst v
                          have hp :=
                            (Moist.SMT.Semantics.evalBoolIs_and_true m
                              (asDataList xs).guard
                              (SExpr.not (SExpr.isCtor "DNil" (asDataList xs).val))).mp hpc
                          obtain ⟨ds, rfl, hEval⟩ := asDataList_sound hxs hp.1
                          cases ds with
                          | nil =>
                              have hnil :=
                                Moist.SMT.Semantics.evalBoolIs_isDNil_true_of_dataList_nil
                                  hEval
                              have hnot :=
                                (Moist.SMT.Semantics.evalBoolIs_not_true m
                                  (SExpr.isCtor "DNil" (asDataList xs).val)).mp hp.2
                              exact False.elim (evalBoolIs_true_false_contra hnil hnot)
                          | cons d ds =>
                              exact ⟨ccons, hcons, hnoCons,
                                Moist.CEK.evalBuiltin_ChooseList_dataList_cons
                                  d ds cnil ccons⟩
                        · cases hdFalse
                    · rcases hv with hvNil | hvRest
                      · injection hvNil with hpcEq hvEq
                        subst pc
                        subst v
                        have hp :=
                          (Moist.SMT.Semantics.evalBoolIs_and_true m
                            (asConstList xs).guard
                            (SExpr.isCtor "VNil" (asConstList xs).val)).mp hpc
                        obtain ⟨vals, cs, rfl, hEval, hconsts⟩ :=
                          asConstList_sound hxs hp.1
                        cases vals with
                        | nil =>
                            simp [semValListToConstList?] at hconsts
                            subst cs
                            exact ⟨cnil, hnil, hnoNil,
                              Moist.CEK.evalBuiltin_ChooseList_constList_nil cnil ccons⟩
                        | cons vh vt =>
                            have hfalse :=
                              Moist.SMT.Semantics.evalBoolIs_isVNil_false_of_valList_cons
                                hEval
                            exact False.elim (evalBoolIs_true_false_contra hp.2 hfalse)
                      · rcases hvRest with hvCons | hvFalse
                        · injection hvCons with hpcEq hvEq
                          subst pc
                          subst v
                          have hp :=
                            (Moist.SMT.Semantics.evalBoolIs_and_true m
                              (asConstList xs).guard
                              (SExpr.not (SExpr.isCtor "VNil" (asConstList xs).val))).mp hpc
                          obtain ⟨vals, cs, rfl, hEval, hconsts⟩ :=
                            asConstList_sound hxs hp.1
                          cases vals with
                          | nil =>
                              have hnil :=
                                Moist.SMT.Semantics.evalBoolIs_isVNil_true_of_valList_nil
                                  hEval
                              have hnot :=
                                (Moist.SMT.Semantics.evalBoolIs_not_true m
                                  (SExpr.isCtor "VNil" (asConstList xs).val)).mp hp.2
                              exact False.elim (evalBoolIs_true_false_contra hnil hnot)
                          | cons vh vt =>
                              cases hheadConst : semValToConst? vh <;>
                                simp [semValListToConstList?, hheadConst] at hconsts
                              rename_i ch
                              cases htailConst : semValListToConstList? vt <;>
                                simp [htailConst] at hconsts
                              rename_i ct
                              subst cs
                              exact ⟨ccons, hcons, hnoCons,
                                Moist.CEK.evalBuiltin_ChooseList_constList_cons
                                  ch ct cnil ccons⟩
                        · cases hvFalse
                  · rcases herr with herr | hfalse
                    · cases herr
                    · cases hfalse
              | cons _ _ =>
                  change Outcome.ok pc v ∈ err at hmem
                  simp [err] at hmem
theorem evalBuiltinSym_active_ok_MkCons : BuiltinOkSound .MkCons := by
  intro m args cargs pc v hargs hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons tail rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons head rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈
                (let dl := asDataList tail
                 let hd := asData head
                 let vl := asConstList tail
                 let hv := asConstVal head
                 let dataOk := SExpr.and dl.guard hd.guard
                 let constOk := SExpr.and vl.guard hv.guard
                 [Outcome.ok dataOk (.const (.dataList (.app "DCons" [hd.val, dl.val]))),
                  Outcome.ok constOk (.const (.constList (.app "VCons" [hv.val, vl.val]))),
                  Outcome.error (SExpr.not (SExpr.or dataOk constOk))]) at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨ctail, chead, htail, hhead, rfl⟩ :=
                symValListToCekList_pair hargs
              rcases hmem with hdata | hconst | herr
              · injection hdata with hpcEq hvEq
                subst pc
                subst v
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asDataList tail).guard (asData head).guard).mp hpc
                obtain ⟨ds, htailEq, htailEval⟩ := asDataList_sound htail hp.1
                subst ctail
                obtain ⟨d, hheadEq, hheadEval⟩ := asData_sound hhead hp.2
                subst chead
                have hconsEval :=
                  Moist.SMT.Semantics.eval_DCons_of
                    (m := m) (h := (asData head).val) (t := (asDataList tail).val)
                    hheadEval htailEval
                refine ⟨.VCon (.ConstDataList (d :: ds)), ?_,
                  by simp [symValNoOpaqueForSoundness], ?_⟩
                · simp [symValToCek?, symConstToCek?, hconsEval]
                · exact Moist.CEK.evalBuiltin_MkCons_dataList d ds
              · injection hconst with hpcEq hvEq
                subst pc
                subst v
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asConstList tail).guard (asConstVal head).guard).mp hpc
                obtain ⟨vals, cs, htailEq, htailEval, htailConsts⟩ :=
                  asConstList_sound htail hp.1
                subst ctail
                obtain ⟨c, semv, hheadEq, hheadEval, hheadConst⟩ :=
                  asConstVal_sound hhead hp.2
                subst chead
                have hconsEval :=
                  Moist.SMT.Semantics.eval_VCons_of
                    (m := m) (h := (asConstVal head).val) (t := (asConstList tail).val)
                    hheadEval htailEval
                refine ⟨.VCon (.ConstList (c :: cs)), ?_,
                  by simp [symValNoOpaqueForSoundness], ?_⟩
                · have hconstsCons :
                    semValListToConstList? (semv :: vals) = some (c :: cs) := by
                    simp [semValListToConstList?, hheadConst, htailConsts]
                  simp [symValToCek?, symConstToCek?, hconsEval, hconstsCons]
                · exact Moist.CEK.evalBuiltin_MkCons_constList c cs
              · rcases herr with herr | hfalse
                · cases herr
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_HeadList : BuiltinOkSound .HeadList := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons xs rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈
            (let dl := asDataList xs
             let vl := asConstList xs
             [Outcome.ok
                (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val)))
                (.const (.data (.app "dhead" [dl.val]))),
              Outcome.ok
                (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))
                (.dyn (.app "vhead" [vl.val])),
              Outcome.error (SExpr.not
                (SExpr.or
                  (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val)))
                  (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))))]) at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cxs, hxs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hd | hv | herr
          · injection hd with hpcEq hvEq
            subst pc
            subst v
            have hp :=
              (Moist.SMT.Semantics.evalBoolIs_and_true m
                (asDataList xs).guard
                (SExpr.not (SExpr.isCtor "DNil" (asDataList xs).val))).mp hpc
            obtain ⟨ds, rfl, hEval⟩ := asDataList_sound hxs hp.1
            cases ds with
            | nil =>
                have hnil :=
                  Moist.SMT.Semantics.evalBoolIs_isDNil_true_of_dataList_nil
                    hEval
                have hnot :=
                  (Moist.SMT.Semantics.evalBoolIs_not_true m
                    (SExpr.isCtor "DNil" (asDataList xs).val)).mp hp.2
                exact False.elim (evalBoolIs_true_false_contra hnil hnot)
            | cons d ds =>
                have hhead :=
                  Moist.SMT.Semantics.eval_dhead_of (m := m)
                    (e := (asDataList xs).val) (h := d) (t := ds) hEval
                refine ⟨.VCon (.Data d), ?_,
                  by simp [symValNoOpaqueForSoundness], ?_⟩
                · simp [symValToCek?, symConstToCek?, hhead]
                · exact Moist.CEK.evalBuiltin_HeadList_dataList d ds
          · injection hv with hpcEq hvEq
            subst pc
            subst v
            have hp :=
              (Moist.SMT.Semantics.evalBoolIs_and_true m
                (asConstList xs).guard
                (SExpr.not (SExpr.isCtor "VNil" (asConstList xs).val))).mp hpc
            obtain ⟨vals, cs, rfl, hEval, hconsts⟩ := asConstList_sound hxs hp.1
            cases vals with
            | nil =>
                simp [semValListToConstList?] at hconsts
                have hnil :=
                  Moist.SMT.Semantics.evalBoolIs_isVNil_true_of_valList_nil
                    hEval
                have hnot :=
                  (Moist.SMT.Semantics.evalBoolIs_not_true m
                    (SExpr.isCtor "VNil" (asConstList xs).val)).mp hp.2
                exact False.elim (evalBoolIs_true_false_contra hnil hnot)
            | cons vh vt =>
                cases hheadConst : semValToConst? vh <;>
                  simp [semValListToConstList?, hheadConst] at hconsts
                rename_i ch
                cases htailConst : semValListToConstList? vt <;>
                  simp [htailConst] at hconsts
                rename_i ct
                subst cs
                have hheadEval :=
                  Moist.SMT.Semantics.eval_vhead_of (m := m)
                    (e := (asConstList xs).val) (h := vh) (t := vt) hEval
                have hheadCek := semValToCek_of_const hheadConst
                refine ⟨.VCon ch, ?_,
                  by simp [symValNoOpaqueForSoundness], ?_⟩
                · simp [symValToCek?, hheadEval, hheadCek]
                · exact Moist.CEK.evalBuiltin_HeadList_constList ch ct
          · rcases herr with herr | hfalse
            · cases herr
            · cases hfalse
      | cons _ _ =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_TailList : BuiltinOkSound .TailList := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons xs rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈
            (let dl := asDataList xs
             let vl := asConstList xs
             [Outcome.ok
                (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val)))
                (.const (.dataList (.app "dtail" [dl.val]))),
              Outcome.ok
                (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))
                (.const (.constList (.app "vtail" [vl.val]))),
              Outcome.error (SExpr.not
                (SExpr.or
                  (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val)))
                  (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))))]) at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cxs, hxs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hd | hv | herr
          · injection hd with hpcEq hvEq
            subst pc
            subst v
            have hp :=
              (Moist.SMT.Semantics.evalBoolIs_and_true m
                (asDataList xs).guard
                (SExpr.not (SExpr.isCtor "DNil" (asDataList xs).val))).mp hpc
            obtain ⟨ds, rfl, hEval⟩ := asDataList_sound hxs hp.1
            cases ds with
            | nil =>
                have hnil :=
                  Moist.SMT.Semantics.evalBoolIs_isDNil_true_of_dataList_nil
                    hEval
                have hnot :=
                  (Moist.SMT.Semantics.evalBoolIs_not_true m
                    (SExpr.isCtor "DNil" (asDataList xs).val)).mp hp.2
                exact False.elim (evalBoolIs_true_false_contra hnil hnot)
            | cons d ds =>
                have htail :=
                  Moist.SMT.Semantics.eval_dtail_of (m := m)
                    (e := (asDataList xs).val) (h := d) (t := ds) hEval
                refine ⟨.VCon (.ConstDataList ds), ?_,
                  by simp [symValNoOpaqueForSoundness], ?_⟩
                · simp [symValToCek?, symConstToCek?, htail]
                · exact Moist.CEK.evalBuiltin_TailList_dataList d ds
          · injection hv with hpcEq hvEq
            subst pc
            subst v
            have hp :=
              (Moist.SMT.Semantics.evalBoolIs_and_true m
                (asConstList xs).guard
                (SExpr.not (SExpr.isCtor "VNil" (asConstList xs).val))).mp hpc
            obtain ⟨vals, cs, rfl, hEval, hconsts⟩ := asConstList_sound hxs hp.1
            cases vals with
            | nil =>
                simp [semValListToConstList?] at hconsts
                have hnil :=
                  Moist.SMT.Semantics.evalBoolIs_isVNil_true_of_valList_nil
                    hEval
                have hnot :=
                  (Moist.SMT.Semantics.evalBoolIs_not_true m
                    (SExpr.isCtor "VNil" (asConstList xs).val)).mp hp.2
                exact False.elim (evalBoolIs_true_false_contra hnil hnot)
            | cons vh vt =>
                cases hheadConst : semValToConst? vh <;>
                  simp [semValListToConstList?, hheadConst] at hconsts
                rename_i ch
                cases htailConst : semValListToConstList? vt <;>
                  simp [htailConst] at hconsts
                rename_i ct
                subst cs
                have htailEval :=
                  Moist.SMT.Semantics.eval_vtail_of (m := m)
                    (e := (asConstList xs).val) (h := vh) (t := vt) hEval
                refine ⟨.VCon (.ConstList ct), ?_,
                  by simp [symValNoOpaqueForSoundness], ?_⟩
                · simp [symValToCek?, symConstToCek?, htailEval, htailConst]
                · exact Moist.CEK.evalBuiltin_TailList_constList ch ct
          · rcases herr with herr | hfalse
            · cases herr
            · cases hfalse
      | cons _ _ =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_NullList : BuiltinOkSound .NullList := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons xs rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈
            (let dl := asDataList xs
             let vl := asConstList xs
             [Outcome.ok dl.guard (.const (.bool (SExpr.isCtor "DNil" dl.val))),
              Outcome.ok vl.guard (.const (.bool (SExpr.isCtor "VNil" vl.val))),
              Outcome.error (SExpr.not (SExpr.or dl.guard vl.guard))]) at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cxs, hxs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hd | hv | herr
          · injection hd with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨ds, rfl, hEval⟩ := asDataList_sound hxs hpc
            cases ds with
            | nil =>
                have hbool :
                    SmtSem.eval m (SExpr.isCtor "DNil" (asDataList xs).val) =
                      some (.bool true) :=
                  (Moist.SMT.Semantics.evalBoolIs_true_eq m
                    (SExpr.isCtor "DNil" (asDataList xs).val)).mp
                    (Moist.SMT.Semantics.evalBoolIs_isDNil_true_of_dataList_nil
                      hEval)
                refine ⟨.VCon (.Bool true), ?_,
                  by simp [symValNoOpaqueForSoundness], ?_⟩
                · simp [symValToCek?, symConstToCek?, hbool]
                · exact Moist.CEK.evalBuiltin_NullList_dataList []
            | cons d ds =>
                have hbool :
                    SmtSem.eval m (SExpr.isCtor "DNil" (asDataList xs).val) =
                      some (.bool false) :=
                  (evalBoolIs_false_eq (m := m)
                    (e := SExpr.isCtor "DNil" (asDataList xs).val)).mp
                    (Moist.SMT.Semantics.evalBoolIs_isDNil_false_of_dataList_cons
                      hEval)
                refine ⟨.VCon (.Bool false), ?_,
                  by simp [symValNoOpaqueForSoundness], ?_⟩
                · simp [symValToCek?, symConstToCek?, hbool]
                · exact Moist.CEK.evalBuiltin_NullList_dataList (d :: ds)
          · injection hv with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨vals, cs, rfl, hEval, hconsts⟩ := asConstList_sound hxs hpc
            cases vals with
            | nil =>
                simp [semValListToConstList?] at hconsts
                subst cs
                have hbool :
                    SmtSem.eval m (SExpr.isCtor "VNil" (asConstList xs).val) =
                      some (.bool true) :=
                  (Moist.SMT.Semantics.evalBoolIs_true_eq m
                    (SExpr.isCtor "VNil" (asConstList xs).val)).mp
                    (Moist.SMT.Semantics.evalBoolIs_isVNil_true_of_valList_nil
                      hEval)
                refine ⟨.VCon (.Bool true), ?_,
                  by simp [symValNoOpaqueForSoundness], ?_⟩
                · simp [symValToCek?, symConstToCek?, hbool]
                · exact Moist.CEK.evalBuiltin_NullList_constList []
            | cons vh vt =>
                cases hhead : semValToConst? vh <;>
                  simp [semValListToConstList?, hhead] at hconsts
                rename_i ch
                cases htail : semValListToConstList? vt <;>
                  simp [htail] at hconsts
                rename_i ct
                subst cs
                have hbool :
                    SmtSem.eval m (SExpr.isCtor "VNil" (asConstList xs).val) =
                      some (.bool false) :=
                  (evalBoolIs_false_eq (m := m)
                    (e := SExpr.isCtor "VNil" (asConstList xs).val)).mp
                    (Moist.SMT.Semantics.evalBoolIs_isVNil_false_of_valList_cons
                      hEval)
                refine ⟨.VCon (.Bool false), ?_,
                  by simp [symValNoOpaqueForSoundness], ?_⟩
                · simp [symValToCek?, symConstToCek?, hbool]
                · exact Moist.CEK.evalBuiltin_NullList_constList (ch :: ct)
          · rcases herr with herr | hfalse
            · cases herr
            · cases hfalse
      | cons _ _ =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_ChooseData : BuiltinOkSound .ChooseData := by
  intro m args cargs pc v hargs hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons bCase rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons iCase rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons listCase rest3 =>
              cases rest3 with
              | nil =>
                  change Outcome.ok pc v ∈ err at hmem
                  simp [err] at hmem
              | cons mapCase rest4 =>
                  cases rest4 with
                  | nil =>
                      change Outcome.ok pc v ∈ err at hmem
                      simp [err] at hmem
                  | cons constrCase rest5 =>
                      cases rest5 with
                      | nil =>
                          change Outcome.ok pc v ∈ err at hmem
                          simp [err] at hmem
                      | cons dVal rest6 =>
                          cases rest6 with
                          | nil =>
                              change Outcome.ok pc v ∈
                                (let d := asData dVal
                                 [Outcome.ok (SExpr.and d.guard (SExpr.isCtor "DConstr" d.val))
                                    constrCase,
                                  Outcome.ok (SExpr.and d.guard (SExpr.isCtor "DMap" d.val))
                                    mapCase,
                                  Outcome.ok (SExpr.and d.guard (SExpr.isCtor "DList" d.val))
                                    listCase,
                                  Outcome.ok (SExpr.and d.guard (SExpr.isCtor "DI" d.val))
                                    iCase,
                                  Outcome.ok (SExpr.and d.guard (SExpr.isCtor "DB" d.val))
                                    bCase,
                                  Outcome.error (SExpr.not d.guard)]) at hmem
                              simp only [List.mem_cons, List.not_mem_nil] at hmem
                              obtain ⟨cb, ci, cl, cm, cc, cd, hb, hi, hl, hm, hc, hd,
                                  rfl⟩ :=
                                symValListToCekList_six hargs
                              obtain ⟨hnoB, hnoI, hnoL, hnoM, hnoC, _hnoD⟩ :=
                                symValsNoOpaque_six hnoArgs
                              rcases hmem with hConstr | rest
                              · injection hConstr with hpcEq hvEq
                                subst pc
                                subst v
                                have hp :=
                                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                                    (asData dVal).guard
                                    (SExpr.isCtor "DConstr" (asData dVal).val)).mp hpc
                                obtain ⟨d, rfl, hdEval⟩ := asData_sound hd hp.1
                                obtain ⟨tag, fields, hctorEval⟩ :=
                                  Moist.SMT.Semantics.evalBoolIs_isDConstr_true hp.2
                                have hdEq0 := hctorEval.symm.trans hdEval
                                injection hdEq0 with hdEq
                                cases hdEq
                                exact ⟨cc, hc, hnoC,
                                  Moist.CEK.evalBuiltin_ChooseData_constr
                                    tag fields cb ci cl cm cc⟩
                              · rcases rest with hMap | rest
                                · injection hMap with hpcEq hvEq
                                  subst pc
                                  subst v
                                  have hp :=
                                    (Moist.SMT.Semantics.evalBoolIs_and_true m
                                      (asData dVal).guard
                                      (SExpr.isCtor "DMap" (asData dVal).val)).mp hpc
                                  obtain ⟨d, rfl, hdEval⟩ := asData_sound hd hp.1
                                  obtain ⟨ps, hctorEval⟩ :=
                                    Moist.SMT.Semantics.evalBoolIs_isDMap_true hp.2
                                  have hdEq0 := hctorEval.symm.trans hdEval
                                  injection hdEq0 with hdEq
                                  cases hdEq
                                  exact ⟨cm, hm, hnoM,
                                    Moist.CEK.evalBuiltin_ChooseData_map
                                      ps cb ci cl cm cc⟩
                                · rcases rest with hList | rest
                                  · injection hList with hpcEq hvEq
                                    subst pc
                                    subst v
                                    have hp :=
                                      (Moist.SMT.Semantics.evalBoolIs_and_true m
                                        (asData dVal).guard
                                        (SExpr.isCtor "DList" (asData dVal).val)).mp hpc
                                    obtain ⟨d, rfl, hdEval⟩ := asData_sound hd hp.1
                                    obtain ⟨xs, hctorEval⟩ :=
                                      Moist.SMT.Semantics.evalBoolIs_isDList_true hp.2
                                    have hdEq0 := hctorEval.symm.trans hdEval
                                    injection hdEq0 with hdEq
                                    cases hdEq
                                    exact ⟨cl, hl, hnoL,
                                      Moist.CEK.evalBuiltin_ChooseData_list
                                        xs cb ci cl cm cc⟩
                                  · rcases rest with hI | rest
                                    · injection hI with hpcEq hvEq
                                      subst pc
                                      subst v
                                      have hp :=
                                        (Moist.SMT.Semantics.evalBoolIs_and_true m
                                          (asData dVal).guard
                                          (SExpr.isCtor "DI" (asData dVal).val)).mp hpc
                                      obtain ⟨d, rfl, hdEval⟩ := asData_sound hd hp.1
                                      obtain ⟨i, hctorEval⟩ :=
                                        Moist.SMT.Semantics.evalBoolIs_isDI_true hp.2
                                      have hdEq0 := hctorEval.symm.trans hdEval
                                      injection hdEq0 with hdEq
                                      cases hdEq
                                      exact ⟨ci, hi, hnoI,
                                        Moist.CEK.evalBuiltin_ChooseData_i
                                          i cb ci cl cm cc⟩
                                    · rcases rest with hB | herr
                                      · injection hB with hpcEq hvEq
                                        subst pc
                                        subst v
                                        have hp :=
                                          (Moist.SMT.Semantics.evalBoolIs_and_true m
                                            (asData dVal).guard
                                            (SExpr.isCtor "DB" (asData dVal).val)).mp hpc
                                        obtain ⟨d, rfl, hdEval⟩ := asData_sound hd hp.1
                                        obtain ⟨bs, hctorEval⟩ :=
                                          Moist.SMT.Semantics.evalBoolIs_isDB_true hp.2
                                        have hdEq0 := hctorEval.symm.trans hdEval
                                        injection hdEq0 with hdEq
                                        cases hdEq
                                        exact ⟨cb, hb, hnoB,
                                          Moist.CEK.evalBuiltin_ChooseData_b
                                            bs cb ci cl cm cc⟩
                                      · rcases herr with herr | hfalse
                                        · cases herr
                                        · cases hfalse
                          | cons _ _ =>
                              change Outcome.ok pc v ∈ err at hmem
                              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_ConstrData : BuiltinOkSound .ConstrData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons fields rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons tag rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_ConstrData_eq fields tag] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asInt tag).guard (asDataList fields).guard)
                  (SymVal.const (SymConst.data
                    (.app "DConstr" [(asInt tag).val, (asDataList fields).val]))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt tag).guard (asDataList fields).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cfields, ctag, hfields, htag, rfl⟩ :=
                  symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt tag).guard (asDataList fields).guard).mp hpc
                obtain ⟨itag, rfl, htagEval⟩ := asInt_sound htag hp.1
                obtain ⟨xs, rfl, hfieldsEval⟩ := asDataList_sound hfields hp.2
                refine ⟨.VCon (.Data (.Constr itag xs)), ?_, ?_, ?_⟩
                ·
                  have hc := Moist.SMT.Semantics.eval_DConstr_of (m := m)
                    (tag := (asInt tag).val) (fields := (asDataList fields).val)
                    htagEval hfieldsEval
                  simp [symValToCek?, symConstToCek?, hc]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_MapData : BuiltinOkSound .MapData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons ps rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_MapData_eq ps] at hmem
          change Outcome.ok pc v ∈
            [Outcome.ok (asPairDataList ps).guard
              (SymVal.const (SymConst.data (.app "DMap" [(asPairDataList ps).val]))),
             Outcome.error (SExpr.not (asPairDataList ps).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · injection hmem with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨cps, hps, rfl⟩ := symValListToCekList_singleton hargs
            obtain ⟨xs, rfl, hpsEval⟩ := asPairDataList_sound hps hpc
            refine ⟨.VCon (.Data (.Map xs)), ?_, ?_, ?_⟩
            ·
              have hm := Moist.SMT.Semantics.eval_DMap_of (m := m)
                (ps := (asPairDataList ps).val) hpsEval
              simp [symValToCek?, symConstToCek?, hm]
            · simp [symValNoOpaqueForSoundness]
            · rfl
          · rcases hmem with hbad | hfalse
            · cases hbad
            · cases hfalse
      | cons _ rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_ListData : BuiltinOkSound .ListData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons xsSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_ListData_eq xsSym] at hmem
          change Outcome.ok pc v ∈
            [Outcome.ok (asDataList xsSym).guard
              (SymVal.const (SymConst.data (.app "DList" [(asDataList xsSym).val]))),
             Outcome.error (SExpr.not (asDataList xsSym).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · injection hmem with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨cxs, hxs, rfl⟩ := symValListToCekList_singleton hargs
            obtain ⟨xs, rfl, hxsEval⟩ := asDataList_sound hxs hpc
            refine ⟨.VCon (.Data (.List xs)), ?_, ?_, ?_⟩
            ·
              have hl := Moist.SMT.Semantics.eval_DList_of (m := m)
                (e := (asDataList xsSym).val) hxsEval
              simp [symValToCek?, symConstToCek?, hl]
            · simp [symValNoOpaqueForSoundness]
            · rfl
          · rcases hmem with hbad | hfalse
            · cases hbad
            · cases hfalse
      | cons _ rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_IData : BuiltinOkSound .IData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons iSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_IData_eq iSym] at hmem
          change Outcome.ok pc v ∈
            [Outcome.ok (asInt iSym).guard
              (SymVal.const (SymConst.data (.app "DI" [(asInt iSym).val]))),
             Outcome.error (SExpr.not (asInt iSym).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · injection hmem with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨ci, hi, rfl⟩ := symValListToCekList_singleton hargs
            obtain ⟨i, rfl, hiEval⟩ := asInt_sound hi hpc
            refine ⟨.VCon (.Data (.I i)), ?_, ?_, ?_⟩
            ·
              have hdi := Moist.SMT.Semantics.eval_DI_of (m := m)
                (e := (asInt iSym).val) hiEval
              simp [symValToCek?, symConstToCek?, hdi]
            · simp [symValNoOpaqueForSoundness]
            · rfl
          · rcases hmem with hbad | hfalse
            · cases hbad
            · cases hfalse
      | cons _ rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_BData : BuiltinOkSound .BData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons bsSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_BData_eq bsSym] at hmem
          change Outcome.ok pc v ∈
            [Outcome.ok (asBytes bsSym).guard
              (SymVal.const (SymConst.data (.app "DB" [(asBytes bsSym).val]))),
             Outcome.error (SExpr.not (asBytes bsSym).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · injection hmem with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨cbs, hbs, rfl⟩ := symValListToCekList_singleton hargs
            obtain ⟨bs, rfl, hbsEval⟩ := asBytes_sound hbs hpc
            refine ⟨.VCon (.Data (.B bs)), ?_, ?_, ?_⟩
            ·
              have hdb := Moist.SMT.Semantics.eval_DB_of (m := m)
                (e := (asBytes bsSym).val) hbsEval
              simp [symValToCek?, symConstToCek?, hdb]
            · simp [symValNoOpaqueForSoundness]
            · rfl
          · rcases hmem with hbad | hfalse
            · cases hbad
            · cases hfalse
      | cons _ rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_UnConstrData : BuiltinOkSound .UnConstrData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons dVal rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_UnConstrData_eq dVal] at hmem
          change Outcome.ok pc v ∈
            [Outcome.ok (SExpr.and (asData dVal).guard
              (SExpr.isCtor "DConstr" (asData dVal).val))
              (SymVal.const (SymConst.pairData
                (.app "DI" [.app "dataConstrTag" [(asData dVal).val]])
                (.app "DList" [.app "dataConstrFields" [(asData dVal).val]]))),
             Outcome.error (SExpr.and (asData dVal).guard
              (SExpr.not (SExpr.isCtor "DConstr" (asData dVal).val))),
             Outcome.error (SExpr.not (asData dVal).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · injection hmem with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨cd, hd, rfl⟩ := symValListToCekList_singleton hargs
            have hp :=
              (Moist.SMT.Semantics.evalBoolIs_and_true m
                (asData dVal).guard
                (SExpr.isCtor "DConstr" (asData dVal).val)).mp hpc
            obtain ⟨d, rfl, hdEval⟩ := asData_sound hd hp.1
            obtain ⟨tag, fields, hctorEval⟩ :=
              Moist.SMT.Semantics.evalBoolIs_isDConstr_true
                (m := m) (e := (asData dVal).val)
                (by simpa [pcHolds] using hp.2)
            change Moist.SMT.Semantics.eval m (asData dVal).val =
              some (Moist.SMT.Semantics.SVal.data d) at hdEval
            rw [hdEval] at hctorEval
            injection hctorEval with hdEq
            injection hdEq with hdDataEq
            subst d
            refine ⟨.VCon (.PairData (.I tag, .List fields)), ?_, ?_, ?_⟩
            ·
              have htagEval := Moist.SMT.Semantics.eval_dataConstrTag_of
                (m := m) (e := (asData dVal).val) hdEval
              have hfieldsEval := Moist.SMT.Semantics.eval_dataConstrFields_of
                (m := m) (e := (asData dVal).val) hdEval
              have hdi := Moist.SMT.Semantics.eval_DI_of (m := m)
                (e := .app "dataConstrTag" [(asData dVal).val]) htagEval
              have hdl := Moist.SMT.Semantics.eval_DList_of (m := m)
                (e := .app "dataConstrFields" [(asData dVal).val]) hfieldsEval
              simp [symValToCek?, symConstToCek?, hdi, hdl]
            · simp [symValNoOpaqueForSoundness]
            · rfl
          · rcases hmem with hbad | hmem
            · cases hbad
            · rcases hmem with hbad | hfalse
              · cases hbad
              · cases hfalse
      | cons _ rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_UnMapData : BuiltinOkSound .UnMapData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons dVal rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_UnMapData_eq dVal] at hmem
          change Outcome.ok pc v ∈
            [Outcome.ok (SExpr.and (asData dVal).guard
              (SExpr.isCtor "DMap" (asData dVal).val))
              (SymVal.const (SymConst.pairDataList
                (.app "dataMapEntries" [(asData dVal).val]))),
             Outcome.error (SExpr.and (asData dVal).guard
              (SExpr.not (SExpr.isCtor "DMap" (asData dVal).val))),
             Outcome.error (SExpr.not (asData dVal).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · injection hmem with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨cd, hd, rfl⟩ := symValListToCekList_singleton hargs
            have hp :=
              (Moist.SMT.Semantics.evalBoolIs_and_true m
                (asData dVal).guard
                (SExpr.isCtor "DMap" (asData dVal).val)).mp hpc
            obtain ⟨d, rfl, hdEval⟩ := asData_sound hd hp.1
            obtain ⟨ps, hmapEval⟩ :=
              Moist.SMT.Semantics.evalBoolIs_isDMap_true
                (m := m) (e := (asData dVal).val)
                (by simpa [pcHolds] using hp.2)
            change Moist.SMT.Semantics.eval m (asData dVal).val =
              some (Moist.SMT.Semantics.SVal.data d) at hdEval
            rw [hdEval] at hmapEval
            injection hmapEval with hdEq
            injection hdEq with hdDataEq
            subst d
            refine ⟨.VCon (.ConstPairDataList ps), ?_, ?_, ?_⟩
            ·
              have hentries := Moist.SMT.Semantics.eval_dataMapEntries_of
                (m := m) (e := (asData dVal).val) hdEval
              simp [symValToCek?, symConstToCek?, hentries]
            · simp [symValNoOpaqueForSoundness]
            · rfl
          · rcases hmem with hbad | hmem
            · cases hbad
            · rcases hmem with hbad | hfalse
              · cases hbad
              · cases hfalse
      | cons _ rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_UnListData : BuiltinOkSound .UnListData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons dVal rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_UnListData_eq dVal] at hmem
          change Outcome.ok pc v ∈
            [Outcome.ok (SExpr.and (asData dVal).guard
              (SExpr.isCtor "DList" (asData dVal).val))
              (SymVal.const (SymConst.dataList
                (.app "dataListItems" [(asData dVal).val]))),
             Outcome.error (SExpr.and (asData dVal).guard
              (SExpr.not (SExpr.isCtor "DList" (asData dVal).val))),
             Outcome.error (SExpr.not (asData dVal).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · injection hmem with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨cd, hd, rfl⟩ := symValListToCekList_singleton hargs
            have hp :=
              (Moist.SMT.Semantics.evalBoolIs_and_true m
                (asData dVal).guard
                (SExpr.isCtor "DList" (asData dVal).val)).mp hpc
            obtain ⟨d, rfl, hdEval⟩ := asData_sound hd hp.1
            obtain ⟨xs, hlistEval⟩ :=
              Moist.SMT.Semantics.evalBoolIs_isDList_true
                (m := m) (e := (asData dVal).val)
                (by simpa [pcHolds] using hp.2)
            change Moist.SMT.Semantics.eval m (asData dVal).val =
              some (Moist.SMT.Semantics.SVal.data d) at hdEval
            rw [hdEval] at hlistEval
            injection hlistEval with hdEq
            injection hdEq with hdDataEq
            subst d
            refine ⟨.VCon (.ConstDataList xs), ?_, ?_, ?_⟩
            ·
              have hitems := Moist.SMT.Semantics.eval_dataListItems_of
                (m := m) (e := (asData dVal).val) hdEval
              simp [symValToCek?, symConstToCek?, hitems]
            · simp [symValNoOpaqueForSoundness]
            · rfl
          · rcases hmem with hbad | hmem
            · cases hbad
            · rcases hmem with hbad | hfalse
              · cases hbad
              · cases hfalse
      | cons _ rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_UnIData : BuiltinOkSound .UnIData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons dVal rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_UnIData_eq dVal] at hmem
          change Outcome.ok pc v ∈
            [Outcome.ok (SExpr.and (asData dVal).guard
              (SExpr.isCtor "DI" (asData dVal).val))
              (SymVal.const (SymConst.integer
                (.app "dataInt" [(asData dVal).val]))),
             Outcome.error (SExpr.and (asData dVal).guard
              (SExpr.not (SExpr.isCtor "DI" (asData dVal).val))),
             Outcome.error (SExpr.not (asData dVal).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · injection hmem with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨cd, hd, rfl⟩ := symValListToCekList_singleton hargs
            have hp :=
              (Moist.SMT.Semantics.evalBoolIs_and_true m
                (asData dVal).guard
                (SExpr.isCtor "DI" (asData dVal).val)).mp hpc
            obtain ⟨d, rfl, hdEval⟩ := asData_sound hd hp.1
            obtain ⟨i, hiEval⟩ :=
              Moist.SMT.Semantics.evalBoolIs_isDI_true
                (m := m) (e := (asData dVal).val)
                (by simpa [pcHolds] using hp.2)
            change Moist.SMT.Semantics.eval m (asData dVal).val =
              some (Moist.SMT.Semantics.SVal.data d) at hdEval
            rw [hdEval] at hiEval
            injection hiEval with hdEq
            injection hdEq with hdDataEq
            subst d
            refine ⟨.VCon (.Integer i), ?_, ?_, ?_⟩
            ·
              have hint := Moist.SMT.Semantics.eval_dataInt_of
                (m := m) (e := (asData dVal).val) hdEval
              simp [symValToCek?, symConstToCek?, hint]
            · simp [symValNoOpaqueForSoundness]
            · rfl
          · rcases hmem with hbad | hmem
            · cases hbad
            · rcases hmem with hbad | hfalse
              · cases hbad
              · cases hfalse
      | cons _ rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_UnBData : BuiltinOkSound .UnBData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons dVal rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_UnBData_eq dVal] at hmem
          change Outcome.ok pc v ∈
            [Outcome.ok (SExpr.and (asData dVal).guard
              (SExpr.isCtor "DB" (asData dVal).val))
              (SymVal.const (SymConst.bytes
                (.app "dataBytes" [(asData dVal).val]))),
             Outcome.error (SExpr.and (asData dVal).guard
              (SExpr.not (SExpr.isCtor "DB" (asData dVal).val))),
             Outcome.error (SExpr.not (asData dVal).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · injection hmem with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨cd, hd, rfl⟩ := symValListToCekList_singleton hargs
            have hp :=
              (Moist.SMT.Semantics.evalBoolIs_and_true m
                (asData dVal).guard
                (SExpr.isCtor "DB" (asData dVal).val)).mp hpc
            obtain ⟨d, rfl, hdEval⟩ := asData_sound hd hp.1
            obtain ⟨bs, hbytesEval⟩ :=
              Moist.SMT.Semantics.evalBoolIs_isDB_true
                (m := m) (e := (asData dVal).val)
                (by simpa [pcHolds] using hp.2)
            change Moist.SMT.Semantics.eval m (asData dVal).val =
              some (Moist.SMT.Semantics.SVal.data d) at hdEval
            rw [hdEval] at hbytesEval
            injection hbytesEval with hdEq
            injection hdEq with hdDataEq
            subst d
            refine ⟨.VCon (.ByteString bs), ?_, ?_, ?_⟩
            ·
              have hbs := Moist.SMT.Semantics.eval_dataBytes_of
                (m := m) (e := (asData dVal).val) hdEval
              simp [symValToCek?, symConstToCek?, hbs]
            · simp [symValNoOpaqueForSoundness]
            · rfl
          · rcases hmem with hbad | hmem
            · cases hbad
            · rcases hmem with hbad | hfalse
              · cases hbad
              · cases hfalse
      | cons _ rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_EqualsData : BuiltinOkSound .EqualsData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_EqualsData_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asData a).guard (asData b).guard)
                  (SymVal.const (SymConst.bool
                    (SExpr.eq (asData a).val (asData b).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asData a).guard (asData b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asData a).guard (asData b).guard).mp hpc
                obtain ⟨da, rfl, hea⟩ := asData_sound ha hp.1
                obtain ⟨db, rfl, heb⟩ := asData_sound hb hp.2
                refine ⟨.VCon (.Bool (da == db)), ?_, ?_, ?_⟩
                ·
                  have heq := Moist.SMT.Semantics.eval_eq_data_of (m := m)
                    (a := (asData a).val) (b := (asData b).val)
                    (x := da) (y := db) hea heb
                  change SmtSem.eval m (SExpr.eq (asData a).val (asData b).val) =
                    some (Moist.SMT.Semantics.SVal.bool (da == db)) at heq
                  simp [symValToCek?, symConstToCek?, heq]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_MkPairData : BuiltinOkSound .MkPairData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_MkPairData_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asData a).guard (asData b).guard)
                  (SymVal.const (SymConst.pairData (asData a).val (asData b).val)),
                 Outcome.error (SExpr.not
                  (SExpr.and (asData a).guard (asData b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asData a).guard (asData b).guard).mp hpc
                obtain ⟨da, rfl, haEval⟩ := asData_sound ha hp.1
                obtain ⟨db, rfl, hbEval⟩ := asData_sound hb hp.2
                refine ⟨.VCon (.PairData (da, db)), ?_, ?_, ?_⟩
                · simp [symValToCek?, symConstToCek?, haEval, hbEval]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_MkNilData : BuiltinOkSound .MkNilData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons u rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_MkNilData_eq u] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · injection hmem with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨cu, hu, rfl⟩ := symValListToCekList_singleton hargs
            have hunit := unitGuard_sound hu hpc
            subst cu
            refine ⟨.VCon (.ConstDataList []), ?_, ?_, ?_⟩
            · simp [symValToCek?, symConstToCek?, Moist.SMT.Semantics.eval_DNil]
            · simp [symValNoOpaqueForSoundness]
            · rfl
          · rcases hmem with hbad | hfalse
            · cases hbad
            · cases hfalse
      | cons _ rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_MkNilPairData : BuiltinOkSound .MkNilPairData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons u rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_MkNilPairData_eq u] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · injection hmem with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨cu, hu, rfl⟩ := symValListToCekList_singleton hargs
            have hunit := unitGuard_sound hu hpc
            subst cu
            refine ⟨.VCon (.ConstPairDataList []), ?_, ?_, ?_⟩
            · simp [symValToCek?, symConstToCek?, Moist.SMT.Semantics.eval_DPNil]
            · simp [symValNoOpaqueForSoundness]
            · rfl
          · rcases hmem with hbad | hfalse
            · cases hbad
            · cases hfalse
      | cons _ rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
axiom evalBuiltinSym_active_ok_SerializeData : BuiltinOkSound .SerializeData
axiom evalBuiltinSym_active_ok_VerifyEcdsaSecp256k1Signature : BuiltinOkSound .VerifyEcdsaSecp256k1Signature
axiom evalBuiltinSym_active_ok_VerifySchnorrSecp256k1Signature : BuiltinOkSound .VerifySchnorrSecp256k1Signature
axiom evalBuiltinSym_active_ok_Bls12_381_G1_add : BuiltinOkSound .Bls12_381_G1_add
axiom evalBuiltinSym_active_ok_Bls12_381_G1_neg : BuiltinOkSound .Bls12_381_G1_neg
axiom evalBuiltinSym_active_ok_Bls12_381_G1_scalarMul : BuiltinOkSound .Bls12_381_G1_scalarMul
axiom evalBuiltinSym_active_ok_Bls12_381_G1_equal : BuiltinOkSound .Bls12_381_G1_equal
axiom evalBuiltinSym_active_ok_Bls12_381_G1_hashToGroup : BuiltinOkSound .Bls12_381_G1_hashToGroup
axiom evalBuiltinSym_active_ok_Bls12_381_G1_compress : BuiltinOkSound .Bls12_381_G1_compress
axiom evalBuiltinSym_active_ok_Bls12_381_G1_uncompress : BuiltinOkSound .Bls12_381_G1_uncompress
axiom evalBuiltinSym_active_ok_Bls12_381_G2_add : BuiltinOkSound .Bls12_381_G2_add
axiom evalBuiltinSym_active_ok_Bls12_381_G2_neg : BuiltinOkSound .Bls12_381_G2_neg
axiom evalBuiltinSym_active_ok_Bls12_381_G2_scalarMul : BuiltinOkSound .Bls12_381_G2_scalarMul
axiom evalBuiltinSym_active_ok_Bls12_381_G2_equal : BuiltinOkSound .Bls12_381_G2_equal
axiom evalBuiltinSym_active_ok_Bls12_381_G2_hashToGroup : BuiltinOkSound .Bls12_381_G2_hashToGroup
axiom evalBuiltinSym_active_ok_Bls12_381_G2_compress : BuiltinOkSound .Bls12_381_G2_compress
axiom evalBuiltinSym_active_ok_Bls12_381_G2_uncompress : BuiltinOkSound .Bls12_381_G2_uncompress
axiom evalBuiltinSym_active_ok_Bls12_381_millerLoop : BuiltinOkSound .Bls12_381_millerLoop
axiom evalBuiltinSym_active_ok_Bls12_381_mulMlResult : BuiltinOkSound .Bls12_381_mulMlResult
axiom evalBuiltinSym_active_ok_Bls12_381_finalVerify : BuiltinOkSound .Bls12_381_finalVerify
axiom evalBuiltinSym_active_ok_Keccak_256 : BuiltinOkSound .Keccak_256
axiom evalBuiltinSym_active_ok_Blake2b_224 : BuiltinOkSound .Blake2b_224
axiom evalBuiltinSym_active_ok_IntegerToByteString : BuiltinOkSound .IntegerToByteString
axiom evalBuiltinSym_active_ok_ByteStringToInteger : BuiltinOkSound .ByteStringToInteger
axiom evalBuiltinSym_active_ok_AndByteString : BuiltinOkSound .AndByteString
axiom evalBuiltinSym_active_ok_OrByteString : BuiltinOkSound .OrByteString
axiom evalBuiltinSym_active_ok_XorByteString : BuiltinOkSound .XorByteString
axiom evalBuiltinSym_active_ok_ComplementByteString : BuiltinOkSound .ComplementByteString
axiom evalBuiltinSym_active_ok_ReadBit : BuiltinOkSound .ReadBit
axiom evalBuiltinSym_active_ok_WriteBits : BuiltinOkSound .WriteBits
axiom evalBuiltinSym_active_ok_ReplicateByte : BuiltinOkSound .ReplicateByte
axiom evalBuiltinSym_active_ok_ShiftByteString : BuiltinOkSound .ShiftByteString
axiom evalBuiltinSym_active_ok_RotateByteString : BuiltinOkSound .RotateByteString
axiom evalBuiltinSym_active_ok_CountSetBits : BuiltinOkSound .CountSetBits
axiom evalBuiltinSym_active_ok_FindFirstSetBit : BuiltinOkSound .FindFirstSetBit
axiom evalBuiltinSym_active_ok_Ripemd_160 : BuiltinOkSound .Ripemd_160
axiom evalBuiltinSym_active_ok_ExpModInteger : BuiltinOkSound .ExpModInteger
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_DropList : BuiltinOkSound .DropList := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons xs rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons n rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈
                (let vl := Proj.map2 (fun n xs => .app "vlist_drop" [n, xs])
                    (asInt n) (asConstList xs)
                 let dl := Proj.map2 (fun n xs => .app "dlist_drop" [n, xs])
                    (asInt n) (asDataList xs)
                 [Outcome.ok vl.guard (.const (.constList vl.val)),
                  Outcome.ok dl.guard (.const (.dataList dl.val)),
                  Outcome.error (SExpr.not (SExpr.or vl.guard dl.guard))]) at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cxs, cn, hxs, hn, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hv | hd | herr
              · injection hv with hpcEq hvEq
                subst pc
                subst v
                change pcHolds m
                  (SExpr.and (asInt n).guard (asConstList xs).guard) = true at hpc
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt n).guard (asConstList xs).guard).mp hpc
                obtain ⟨i, rfl, hiEval⟩ := asInt_sound hn hp.1
                obtain ⟨vals, cs, rfl, hxsEval, hconsts⟩ :=
                  asConstList_sound hxs hp.2
                have hdropEval :=
                  Moist.SMT.Semantics.eval_vlist_drop_of (m := m)
                    (n := (asInt n).val) (xs := (asConstList xs).val)
                    hiEval hxsEval
                have hdropBase :
                    semValListToConstList? (vals.drop i.toNat) =
                      some (cs.drop i.toNat) :=
                  semValListToConstList_drop (vals := vals) (cs := cs)
                    (n := i.toNat) hconsts
                have hdropConsts :
                    semValListToConstList?
                        (if i < 0 then vals else vals.drop i.toNat) =
                      some (if i < 0 then cs else cs.drop i.toNat) := by
                  by_cases hneg : i < 0
                  · simp [hneg, hconsts]
                  · simpa [hneg] using hdropBase
                refine ⟨.VCon (if i < 0 then .ConstList cs else .ConstList (cs.drop i.toNat)),
                  ?_, by simp [symValNoOpaqueForSoundness], ?_⟩
                · by_cases hneg : i < 0
                  · simp [symValToCek?, symConstToCek?, Proj.map2,
                      hdropEval, hneg, hconsts]
                  · simp [symValToCek?, symConstToCek?, Proj.map2,
                      hdropEval, hneg, hdropBase]
                · exact Moist.CEK.evalBuiltin_DropList_constList cs i
              · injection hd with hpcEq hvEq
                subst pc
                subst v
                change pcHolds m
                  (SExpr.and (asInt n).guard (asDataList xs).guard) = true at hpc
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt n).guard (asDataList xs).guard).mp hpc
                obtain ⟨i, rfl, hiEval⟩ := asInt_sound hn hp.1
                obtain ⟨ds, rfl, hxsEval⟩ := asDataList_sound hxs hp.2
                have hdropEval :=
                  Moist.SMT.Semantics.eval_dlist_drop_of (m := m)
                    (n := (asInt n).val) (xs := (asDataList xs).val)
                    hiEval hxsEval
                refine ⟨.VCon (if i < 0 then .ConstDataList ds else .ConstDataList (ds.drop i.toNat)),
                  ?_, by simp [symValNoOpaqueForSoundness], ?_⟩
                · by_cases hneg : i < 0 <;>
                    simp [symValToCek?, symConstToCek?, Proj.map2, hdropEval, hneg]
                · exact Moist.CEK.evalBuiltin_DropList_dataList ds i
              · rcases herr with herr | hfalse
                · cases herr
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_IndexArray : BuiltinOkSound .IndexArray := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons idx rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons arr rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈
                checked2
                  (Proj.map2 (fun arr idx => (arr, idx)) (asArray arr) (asInt idx))
                  (fun (arr, idx) =>
                    let g := SExpr.and (SExpr.ge idx (.int 0))
                      (SExpr.lt idx (.app "vlist_length" [arr]))
                    [Outcome.ok g (.dyn (.app "vlist_index" [idx, arr])),
                     Outcome.error (SExpr.not g)]) at hmem
              have hpath := checked2_path_ok hmem hpc
              rcases hpath with ⟨innerPc, hinner, _hpcEq, hpArgs, hpRange⟩
              simp only [List.mem_cons, List.not_mem_nil] at hinner
              rcases hinner with hok | herr
              · injection hok with hinnerPcEq hvEq
                subst innerPc
                subst v
                obtain ⟨cidx, carr, hidxArg, harrArg, rfl⟩ :=
                  symValListToCekList_pair hargs
                change pcHolds m
                  (SExpr.and (asArray arr).guard (asInt idx).guard) = true at hpArgs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asArray arr).guard (asInt idx).guard).mp hpArgs
                obtain ⟨i, rfl, hiEval⟩ := asInt_sound hidxArg hp.2
                obtain ⟨vals, cs, rfl, harrEval, hconsts⟩ :=
                  asArray_sound harrArg hp.1
                have hpRangeSplit :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (SExpr.ge (asInt idx).val (.int 0))
                    (SExpr.lt (asInt idx).val
                      (.app "vlist_length" [(asArray arr).val]))).mp hpRange
                have hge : 0 ≤ i :=
                  pcHolds_ge_int hiEval (by simp [Moist.SMT.Semantics.eval])
                    hpRangeSplit.1
                have hlenEval := Moist.SMT.Semantics.eval_vlist_length_of
                  (m := m) (e := (asArray arr).val) harrEval
                have hlt : i < Int.ofNat vals.length :=
                  pcHolds_lt_int hiEval hlenEval hpRangeSplit.2
                have hidxNatLt : i.toNat < vals.length :=
                  (Int.toNat_lt hge).mpr hlt
                have hgetVals :
                    vals[i.toNat]? = some vals[i.toNat] :=
                  List.getElem?_eq_getElem hidxNatLt
                obtain ⟨c, hgetCs, hconst⟩ :=
                  semValListToConstList_get? (vals := vals) (cs := cs)
                    (i := i.toNat) (v := vals[i.toNat])
                    hconsts hgetVals
                have hindexEval :=
                  Moist.SMT.Semantics.eval_vlist_index_of (m := m)
                    (idx := (asInt idx).val) (xs := (asArray arr).val)
                    hiEval harrEval hge hgetVals
                have hcek := semValToCek_of_const hconst
                refine ⟨.VCon c, ?_,
                  by simp [symValNoOpaqueForSoundness], ?_⟩
                · simp [symValToCek?, Proj.map2, hindexEval, hcek]
                · exact Moist.CEK.evalBuiltin_IndexArray cs i hge hgetCs
              · rcases herr with herr | hfalse
                · cases herr
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_LengthOfArray : BuiltinOkSound .LengthOfArray := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons arr rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈
            [Outcome.ok (asArray arr).guard
              (SymVal.const (SymConst.integer
                (.app "vlist_length" [(asArray arr).val]))),
             Outcome.error (SExpr.not (asArray arr).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨carr, harr, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · injection hok with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨vals, cs, rfl, harrEval, hconsts⟩ :=
              asArray_sound harr hpc
            have hlenEval := Moist.SMT.Semantics.eval_vlist_length_of
              (m := m) (e := (asArray arr).val) harrEval
            have hlenNat : vals.length = cs.length :=
              semValListToConstList_length hconsts
            have hlenEvalCs :
                SmtSem.eval m (.app "vlist_length" [(asArray arr).val]) =
                  some (.int (Int.ofNat cs.length)) := by
              simpa [hlenNat] using hlenEval
            refine ⟨.VCon (.Integer (Int.ofNat cs.length)), ?_,
              by simp [symValNoOpaqueForSoundness], ?_⟩
            · simp [symValToCek?, symConstToCek?, hlenEvalCs]
            · exact Moist.CEK.evalBuiltin_LengthOfArray cs
          · rcases herr with herr | hfalse
            · cases herr
            · cases hfalse
      | cons _ _ =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_ListToArray : BuiltinOkSound .ListToArray := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons xs rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈
            [Outcome.ok (asConstList xs).guard
              (SymVal.const (SymConst.array (asConstList xs).val)),
             Outcome.error (SExpr.not (asConstList xs).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cxs, hxs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · injection hok with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨vals, cs, rfl, hxsEval, hconsts⟩ :=
              asConstList_sound hxs hpc
            refine ⟨.VCon (.ConstArray cs), ?_,
              by simp [symValNoOpaqueForSoundness], ?_⟩
            · simp [symValToCek?, symConstToCek?, hxsEval, hconsts]
            · exact Moist.CEK.evalBuiltin_ListToArray cs
          · rcases herr with herr | hfalse
            · cases herr
            · cases hfalse
      | cons _ _ =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem

theorem extractConsts_length {args : List CekValue} {cs : List Const}
    (h : Moist.CEK.extractConsts args = some cs) :
    cs.length = args.length := by
  induction args generalizing cs with
  | nil =>
      simp [Moist.CEK.extractConsts] at h
      subst cs
      rfl
  | cons v vs ih =>
      cases v <;> simp [Moist.CEK.extractConsts] at h
      rename_i c
      cases hvs : Moist.CEK.extractConsts vs <;> simp [hvs] at h
      subst cs
      simp [ih hvs]

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_AddInteger_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .AddInteger cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_AddInteger_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .AddInteger args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_AddInteger_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_AddInteger_none_of_pair_not_ints {b a : CekValue}
    (h : ∀ ib ia, ¬ (b = .VCon (.Integer ib) ∧ a = .VCon (.Integer ia))) :
    Moist.CEK.evalBuiltin .AddInteger [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_SubtractInteger_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .SubtractInteger cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_SubtractInteger_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .SubtractInteger args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_SubtractInteger_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_SubtractInteger_none_of_pair_not_ints {b a : CekValue}
    (h : ∀ ib ia, ¬ (b = .VCon (.Integer ib) ∧ a = .VCon (.Integer ia))) :
    Moist.CEK.evalBuiltin .SubtractInteger [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_MultiplyInteger_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .MultiplyInteger cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_MultiplyInteger_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .MultiplyInteger args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_MultiplyInteger_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_MultiplyInteger_none_of_pair_not_ints {b a : CekValue}
    (h : ∀ ib ia, ¬ (b = .VCon (.Integer ib) ∧ a = .VCon (.Integer ia))) :
    Moist.CEK.evalBuiltin .MultiplyInteger [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_EqualsInteger_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .EqualsInteger cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_EqualsInteger_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .EqualsInteger args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_EqualsInteger_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_EqualsInteger_none_of_pair_not_ints {b a : CekValue}
    (h : ∀ ib ia, ¬ (b = .VCon (.Integer ib) ∧ a = .VCon (.Integer ia))) :
    Moist.CEK.evalBuiltin .EqualsInteger [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_LessThanInteger_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .LessThanInteger cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_LessThanInteger_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .LessThanInteger args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_LessThanInteger_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_LessThanInteger_none_of_pair_not_ints {b a : CekValue}
    (h : ∀ ib ia, ¬ (b = .VCon (.Integer ib) ∧ a = .VCon (.Integer ia))) :
    Moist.CEK.evalBuiltin .LessThanInteger [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_LessThanEqualsInteger_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .LessThanEqualsInteger cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_LessThanEqualsInteger_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .LessThanEqualsInteger args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_LessThanEqualsInteger_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_LessThanEqualsInteger_none_of_pair_not_ints {b a : CekValue}
    (h : ∀ ib ia, ¬ (b = .VCon (.Integer ib) ∧ a = .VCon (.Integer ia))) :
    Moist.CEK.evalBuiltin .LessThanEqualsInteger [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_DivideInteger_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .DivideInteger cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_DivideInteger_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .DivideInteger args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_DivideInteger_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_DivideInteger_none_of_pair_not_ints {b a : CekValue}
    (h : ∀ ib ia, ¬ (b = .VCon (.Integer ib) ∧ a = .VCon (.Integer ia))) :
    Moist.CEK.evalBuiltin .DivideInteger [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

theorem evalBuiltin_DivideInteger_none_of_divisor_zero {a b : Int}
    (hb : b = 0) :
    Moist.CEK.evalBuiltin .DivideInteger [.VCon (.Integer b), .VCon (.Integer a)] = none := by
  subst b
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_QuotientInteger_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .QuotientInteger cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_QuotientInteger_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .QuotientInteger args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_QuotientInteger_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_QuotientInteger_none_of_pair_not_ints {b a : CekValue}
    (h : ∀ ib ia, ¬ (b = .VCon (.Integer ib) ∧ a = .VCon (.Integer ia))) :
    Moist.CEK.evalBuiltin .QuotientInteger [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

theorem evalBuiltin_QuotientInteger_none_of_divisor_zero {a b : Int}
    (hb : b = 0) :
    Moist.CEK.evalBuiltin .QuotientInteger [.VCon (.Integer b), .VCon (.Integer a)] = none := by
  subst b
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_RemainderInteger_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .RemainderInteger cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_RemainderInteger_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .RemainderInteger args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_RemainderInteger_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_RemainderInteger_none_of_pair_not_ints {b a : CekValue}
    (h : ∀ ib ia, ¬ (b = .VCon (.Integer ib) ∧ a = .VCon (.Integer ia))) :
    Moist.CEK.evalBuiltin .RemainderInteger [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

theorem evalBuiltin_RemainderInteger_none_of_divisor_zero {a b : Int}
    (hb : b = 0) :
    Moist.CEK.evalBuiltin .RemainderInteger [.VCon (.Integer b), .VCon (.Integer a)] = none := by
  subst b
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_ModInteger_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .ModInteger cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_ModInteger_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .ModInteger args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_ModInteger_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_ModInteger_none_of_pair_not_ints {b a : CekValue}
    (h : ∀ ib ia, ¬ (b = .VCon (.Integer ib) ∧ a = .VCon (.Integer ia))) :
    Moist.CEK.evalBuiltin .ModInteger [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

theorem evalBuiltin_ModInteger_none_of_divisor_zero {a b : Int}
    (hb : b = 0) :
    Moist.CEK.evalBuiltin .ModInteger [.VCon (.Integer b), .VCon (.Integer a)] = none := by
  subst b
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_AppendByteString_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .AppendByteString cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_EqualsByteString_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .EqualsByteString cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_LessThanByteString_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .LessThanByteString cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_LessThanEqualsByteString_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .LessThanEqualsByteString cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_AppendByteString_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .AppendByteString args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_AppendByteString_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_EqualsByteString_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .EqualsByteString args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_EqualsByteString_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_LessThanByteString_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .LessThanByteString args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_LessThanByteString_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_LessThanEqualsByteString_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .LessThanEqualsByteString args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_LessThanEqualsByteString_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_AppendByteString_none_of_pair_not_bytes {b a : CekValue}
    (h : ∀ bs2 bs1, ¬ (b = .VCon (.ByteString bs2) ∧ a = .VCon (.ByteString bs1))) :
    Moist.CEK.evalBuiltin .AppendByteString [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_EqualsByteString_none_of_pair_not_bytes {b a : CekValue}
    (h : ∀ bs2 bs1, ¬ (b = .VCon (.ByteString bs2) ∧ a = .VCon (.ByteString bs1))) :
    Moist.CEK.evalBuiltin .EqualsByteString [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_LessThanByteString_none_of_pair_not_bytes {b a : CekValue}
    (h : ∀ bs2 bs1, ¬ (b = .VCon (.ByteString bs2) ∧ a = .VCon (.ByteString bs1))) :
    Moist.CEK.evalBuiltin .LessThanByteString [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_LessThanEqualsByteString_none_of_pair_not_bytes {b a : CekValue}
    (h : ∀ bs2 bs1, ¬ (b = .VCon (.ByteString bs2) ∧ a = .VCon (.ByteString bs1))) :
    Moist.CEK.evalBuiltin .LessThanEqualsByteString [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_ConsByteString_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .ConsByteString cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_SliceByteString_none_of_length_ne_three {cs : List Const}
    (h : cs.length ≠ 3) :
    Moist.CEK.evalBuiltinConst .SliceByteString cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => cases c <;> cases c2 <;> rfl
          | cons c3 rest3 =>
              cases rest3 with
              | nil => exact False.elim (h rfl)
              | cons c4 rest4 =>
                  cases c <;> cases c2 <;> cases c3 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_IndexByteString_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .IndexByteString cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_ConsByteString_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .ConsByteString args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_ConsByteString_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_SliceByteString_none_of_length_ne_three {args : List CekValue}
    (h : args.length ≠ 3) :
    Moist.CEK.evalBuiltin .SliceByteString args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 3 := by
        intro hcs3
        apply h
        omega
      have hnone := evalBuiltinConst_SliceByteString_none_of_length_ne_three hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_IndexByteString_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .IndexByteString args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_IndexByteString_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_ConsByteString_none_of_pair_not_byte_int {bs n : CekValue}
    (h : ∀ bytes i, ¬ (bs = .VCon (.ByteString bytes) ∧ n = .VCon (.Integer i))) :
    Moist.CEK.evalBuiltin .ConsByteString [bs, n] = none := by
  cases bs with
  | VCon cbs =>
      cases n with
      | VCon cn =>
          cases cbs <;> cases cn <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cbs <;> rfl
      | VDelay body ρ => cases cbs <;> rfl
      | VConstr tag fields => cases cbs <;> rfl
      | VBuiltin fn args expected => cases cbs <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

theorem evalBuiltin_ConsByteString_none_of_byte_out_of_range {bs : ByteArray} {n : Int}
    (h : n < 0 ∨ 255 < n) :
    Moist.CEK.evalBuiltin .ConsByteString [.VCon (.ByteString bs), .VCon (.Integer n)] = none := by
  rcases h with hlt | hgt
  · simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
      Moist.CEK.extractConsts, Moist.CEK.evalBuiltinConst, hlt]
  · have hnlt : ¬ n < 0 := by omega
    simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
      Moist.CEK.extractConsts, Moist.CEK.evalBuiltinConst, hnlt, hgt]

set_option maxHeartbeats 0 in
theorem evalBuiltin_SliceByteString_none_of_triple_not_byte_int_int
    {bs len start : CekValue}
    (h : ∀ bytes l s,
      ¬ (bs = .VCon (.ByteString bytes) ∧
        len = .VCon (.Integer l) ∧ start = .VCon (.Integer s))) :
    Moist.CEK.evalBuiltin .SliceByteString [bs, len, start] = none := by
  cases bs with
  | VCon cbs =>
      cases len with
      | VCon clen =>
          cases start with
          | VCon cstart =>
              cases cbs <;> cases clen <;> cases cstart <;> try rfl
              exact False.elim (h _ _ _ ⟨rfl, rfl, rfl⟩)
          | VLam body ρ => cases cbs <;> cases clen <;> rfl
          | VDelay body ρ => cases cbs <;> cases clen <;> rfl
          | VConstr tag fields => cases cbs <;> cases clen <;> rfl
          | VBuiltin fn args expected => cases cbs <;> cases clen <;> rfl
      | VLam body ρ => cases cbs <;> rfl
      | VDelay body ρ => cases cbs <;> rfl
      | VConstr tag fields => cases cbs <;> rfl
      | VBuiltin fn args expected => cases cbs <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_IndexByteString_none_of_pair_not_int_byte {idx bs : CekValue}
    (h : ∀ i bytes, ¬ (idx = .VCon (.Integer i) ∧ bs = .VCon (.ByteString bytes))) :
    Moist.CEK.evalBuiltin .IndexByteString [idx, bs] = none := by
  cases idx with
  | VCon cidx =>
      cases bs with
      | VCon cbs =>
          cases cidx <;> cases cbs <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cidx <;> rfl
      | VDelay body ρ => cases cidx <;> rfl
      | VConstr tag fields => cases cidx <;> rfl
      | VBuiltin fn args expected => cases cidx <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

theorem evalBuiltin_IndexByteString_none_of_negative {bs : ByteArray} {idx : Int}
    (hidx : idx < 0) :
    Moist.CEK.evalBuiltin .IndexByteString [.VCon (.Integer idx), .VCon (.ByteString bs)] = none := by
  simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
    Moist.CEK.extractConsts, Moist.CEK.evalBuiltinConst, hidx]

theorem evalBuiltin_IndexByteString_none_of_nonnegative_out_of_range
    {bs : ByteArray} {idx : Int}
    (hidx : 0 ≤ idx) (hout : Int.ofNat bs.size ≤ idx) :
    Moist.CEK.evalBuiltin .IndexByteString [.VCon (.Integer idx), .VCon (.ByteString bs)] = none := by
  have hnlt : ¬ idx < 0 := by omega
  have hout' : (↑(ByteArray.size bs) : Int) ≤ idx := by simpa using hout
  simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
    Moist.CEK.extractConsts, Moist.CEK.evalBuiltinConst, hnlt]
  rw [if_pos hout']

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_LengthOfArray_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .LengthOfArray cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_ListToArray_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .ListToArray cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> rfl

theorem evalBuiltin_LengthOfArray_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .LengthOfArray args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_LengthOfArray_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_ListToArray_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .ListToArray args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_ListToArray_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_LengthOfArray_none_of_single_not_array {cv : CekValue}
    (h : ∀ cs, cv ≠ .VCon (.ConstArray cs)) :
    Moist.CEK.evalBuiltin .LengthOfArray [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | ConstArray cs => exact False.elim (h cs rfl)
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Data d => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

theorem evalBuiltin_ListToArray_none_of_single_not_list {cv : CekValue}
    (h : ∀ cs, cv ≠ .VCon (.ConstList cs)) :
    Moist.CEK.evalBuiltin .ListToArray [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | ConstList cs => exact False.elim (h cs rfl)
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Data d => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstArray xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_MkNilData_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .MkNilData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_MkNilPairData_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .MkNilPairData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> rfl

theorem evalBuiltin_MkNilData_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .MkNilData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_MkNilData_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_MkNilPairData_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .MkNilPairData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_MkNilPairData_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_MkNilData_none_of_single_not_unit {cv : CekValue}
    (h : cv ≠ .VCon .Unit) :
    Moist.CEK.evalBuiltin .MkNilData [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Unit => exact False.elim (h rfl)
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Bool b => rfl
      | Data d => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

theorem evalBuiltin_MkNilPairData_none_of_single_not_unit {cv : CekValue}
    (h : cv ≠ .VCon .Unit) :
    Moist.CEK.evalBuiltin .MkNilPairData [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Unit => exact False.elim (h rfl)
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Bool b => rfl
      | Data d => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_LengthOfByteString_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .LengthOfByteString cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> rfl

theorem evalBuiltin_LengthOfByteString_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .LengthOfByteString args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_LengthOfByteString_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_LengthOfByteString_none_of_single_not_bytes {cv : CekValue}
    (h : ∀ bs, cv ≠ .VCon (.ByteString bs)) :
    Moist.CEK.evalBuiltin .LengthOfByteString [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | ByteString bs => exact False.elim (h bs rfl)
      | Integer i => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Data d => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_IData_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .IData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_BData_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .BData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> rfl

theorem evalBuiltin_IData_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .IData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_IData_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_BData_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .BData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_BData_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_IData_none_of_single_not_int {cv : CekValue}
    (h : ∀ i, cv ≠ .VCon (.Integer i)) :
    Moist.CEK.evalBuiltin .IData [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Integer i => exact False.elim (h i rfl)
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Data d => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

theorem evalBuiltin_BData_none_of_single_not_bytes {cv : CekValue}
    (h : ∀ bs, cv ≠ .VCon (.ByteString bs)) :
    Moist.CEK.evalBuiltin .BData [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | ByteString bs => exact False.elim (h bs rfl)
      | Integer i => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Data d => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_MapData_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .MapData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_ListData_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .ListData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> rfl

theorem evalBuiltin_MapData_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .MapData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_MapData_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_ListData_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .ListData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_ListData_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_MapData_none_of_single_not_pair_data_list {cv : CekValue}
    (h : ∀ ps, cv ≠ .VCon (.ConstPairDataList ps)) :
    Moist.CEK.evalBuiltin .MapData [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | ConstPairDataList ps => exact False.elim (h ps rfl)
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Data d => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

theorem evalBuiltin_ListData_none_of_single_not_data_list {cv : CekValue}
    (h : ∀ ds, cv ≠ .VCon (.ConstDataList ds)) :
    Moist.CEK.evalBuiltin .ListData [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | ConstDataList ds => exact False.elim (h ds rfl)
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Data d => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_UnConstrData_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .UnConstrData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> try rfl
          case Data d => cases d <;> cases c2 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_UnMapData_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .UnMapData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> try rfl
          case Data d => cases d <;> cases c2 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_UnListData_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .UnListData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> try rfl
          case Data d => cases d <;> cases c2 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_UnIData_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .UnIData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> try rfl
          case Data d => cases d <;> cases c2 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_UnBData_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .UnBData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> try rfl
          case Data d => cases d <;> cases c2 <;> rfl

theorem evalBuiltin_UnConstrData_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .UnConstrData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_UnConstrData_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_UnMapData_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .UnMapData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_UnMapData_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_UnListData_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .UnListData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_UnListData_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_UnIData_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .UnIData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_UnIData_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_UnBData_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .UnBData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_UnBData_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_SerializeData_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .SerializeData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest2 =>
          cases c <;> rfl

theorem evalBuiltin_SerializeData_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .SerializeData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_SerializeData_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_SerializeData_none_of_single_not_data {cv : CekValue}
    (h : ∀ d, cv ≠ .VCon (.Data d)) :
    Moist.CEK.evalBuiltin .SerializeData [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | Data d => exact False.elim (h d rfl)
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

theorem evalBuiltin_UnConstrData_none_of_single_not_constr {cv : CekValue}
    (h : ∀ tag fields, cv ≠ .VCon (.Data (.Constr tag fields))) :
    Moist.CEK.evalBuiltin .UnConstrData [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Data d =>
          cases d with
          | Constr tag fields => exact False.elim (h tag fields rfl)
          | Map ps => rfl
          | List xs => rfl
          | I i => rfl
          | B bs => rfl
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

theorem evalBuiltin_UnMapData_none_of_single_not_map {cv : CekValue}
    (h : ∀ ps, cv ≠ .VCon (.Data (.Map ps))) :
    Moist.CEK.evalBuiltin .UnMapData [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Data d =>
          cases d with
          | Constr tag fields => rfl
          | Map ps => exact False.elim (h ps rfl)
          | List xs => rfl
          | I i => rfl
          | B bs => rfl
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

theorem evalBuiltin_UnListData_none_of_single_not_list {cv : CekValue}
    (h : ∀ xs, cv ≠ .VCon (.Data (.List xs))) :
    Moist.CEK.evalBuiltin .UnListData [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Data d =>
          cases d with
          | Constr tag fields => rfl
          | Map ps => rfl
          | List xs => exact False.elim (h xs rfl)
          | I i => rfl
          | B bs => rfl
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

theorem evalBuiltin_UnIData_none_of_single_not_i {cv : CekValue}
    (h : ∀ i, cv ≠ .VCon (.Data (.I i))) :
    Moist.CEK.evalBuiltin .UnIData [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Data d =>
          cases d with
          | Constr tag fields => rfl
          | Map ps => rfl
          | List xs => rfl
          | I i => exact False.elim (h i rfl)
          | B bs => rfl
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

theorem evalBuiltin_UnBData_none_of_single_not_b {cv : CekValue}
    (h : ∀ bs, cv ≠ .VCon (.Data (.B bs))) :
    Moist.CEK.evalBuiltin .UnBData [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Data d =>
          cases d with
          | Constr tag fields => rfl
          | Map ps => rfl
          | List xs => rfl
          | I i => rfl
          | B bs => exact False.elim (h bs rfl)
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_AppendString_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .AppendString cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_EqualsString_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .EqualsString cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_AppendString_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .AppendString args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_AppendString_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_EqualsString_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .EqualsString args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_EqualsString_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_EncodeUtf8_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .EncodeUtf8 cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest2 =>
          cases c <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_DecodeUtf8_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .DecodeUtf8 cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest2 =>
          cases c <;> rfl

theorem evalBuiltin_EncodeUtf8_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .EncodeUtf8 args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_EncodeUtf8_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_DecodeUtf8_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .DecodeUtf8 args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_DecodeUtf8_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_EncodeUtf8_none_of_single_not_string {cv : CekValue}
    (h : ∀ s, cv ≠ .VCon (.String s)) :
    Moist.CEK.evalBuiltin .EncodeUtf8 [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => exact False.elim (h s rfl)
      | Unit => rfl
      | Bool b => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | Data d => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_DecodeUtf8_none_of_single_not_bytes {cv : CekValue}
    (h : ∀ bs, cv ≠ .VCon (.ByteString bs)) :
    Moist.CEK.evalBuiltin .DecodeUtf8 [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Integer i => rfl
      | ByteString bs => exact False.elim (h bs rfl)
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | Data d => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_DecodeUtf8_none_of_invalid {bs : ByteArray}
    (h : ¬ String.validateUTF8 bs) :
    Moist.CEK.evalBuiltin .DecodeUtf8 [.VCon (.ByteString bs)] = none := by
  change (match (if h' : String.validateUTF8 bs then
      some (Const.String (String.fromUTF8 bs h')) else none) with
    | some c => some (CekValue.VCon c)
    | none => none) = none
  by_cases hv : String.validateUTF8 bs
  · exact False.elim (h hv)
  · simp [hv]

set_option maxHeartbeats 0 in
theorem evalBuiltin_AppendString_none_of_pair_not_strings {b a : CekValue}
    (h : ∀ sb sa, ¬ (b = .VCon (.String sb) ∧ a = .VCon (.String sa))) :
    Moist.CEK.evalBuiltin .AppendString [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_EqualsString_none_of_pair_not_strings {b a : CekValue}
    (h : ∀ sb sa, ¬ (b = .VCon (.String sb) ∧ a = .VCon (.String sa))) :
    Moist.CEK.evalBuiltin .EqualsString [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_ConstrData_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .ConstrData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_EqualsData_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .EqualsData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_MkPairData_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .MkPairData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_ConstrData_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .ConstrData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_ConstrData_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_EqualsData_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .EqualsData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_EqualsData_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_MkPairData_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .MkPairData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_MkPairData_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_ConstrData_none_of_pair_not_supported {fields tag : CekValue}
    (h : ∀ ds i,
      ¬ (fields = .VCon (.ConstDataList ds) ∧ tag = .VCon (.Integer i))) :
    Moist.CEK.evalBuiltin .ConstrData [fields, tag] = none := by
  cases fields with
  | VCon cfields =>
      cases tag with
      | VCon ctag =>
          cases cfields <;> cases ctag <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cfields <;> rfl
      | VDelay body ρ => cases cfields <;> rfl
      | VConstr ctag cfields' => cases cfields <;> rfl
      | VBuiltin fn args expected => cases cfields <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr ctag cfields' => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_EqualsData_none_of_pair_not_data {b a : CekValue}
    (h : ∀ db da, ¬ (b = .VCon (.Data db) ∧ a = .VCon (.Data da))) :
    Moist.CEK.evalBuiltin .EqualsData [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_MkPairData_none_of_pair_not_data {b a : CekValue}
    (h : ∀ db da, ¬ (b = .VCon (.Data db) ∧ a = .VCon (.Data da))) :
    Moist.CEK.evalBuiltin .MkPairData [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

theorem evalBuiltinConst_IfThenElse_none {cs : List Const} :
    Moist.CEK.evalBuiltinConst .IfThenElse cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => rfl
          | cons c3 rest3 => rfl

theorem evalBuiltinConst_ChooseUnit_none {cs : List Const} :
    Moist.CEK.evalBuiltinConst .ChooseUnit cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => rfl
          | cons c3 rest3 => rfl

theorem evalBuiltinConst_Trace_none {cs : List Const} :
    Moist.CEK.evalBuiltinConst .Trace cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => rfl
          | cons c3 rest3 => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_IfThenElse_none_of_length_ne_three {args : List CekValue}
    (h : args.length ≠ 3) :
    Moist.CEK.evalBuiltin .IfThenElse args = none := by
  have hpass : Moist.CEK.evalBuiltinPassThrough .IfThenElse args = none := by
    cases args with
    | nil => rfl
    | cons elseV rest =>
        cases rest with
        | nil => rfl
        | cons thenV rest2 =>
            cases rest2 with
            | nil => rfl
            | cons cond rest3 =>
                cases rest3 with
                | nil => exact False.elim (h rfl)
                | cons extra rest4 =>
                    simp [Moist.CEK.evalBuiltinPassThrough]
  simp [Moist.CEK.evalBuiltin, hpass]
  cases hconst : Moist.CEK.extractConsts args <;>
    simp [hconst, evalBuiltinConst_IfThenElse_none]

set_option maxHeartbeats 0 in
theorem evalBuiltin_ChooseUnit_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .ChooseUnit args = none := by
  have hpass : Moist.CEK.evalBuiltinPassThrough .ChooseUnit args = none := by
    cases args with
    | nil => rfl
    | cons result rest =>
        cases rest with
        | nil => rfl
        | cons unitV rest2 =>
            cases rest2 with
            | nil => exact False.elim (h rfl)
            | cons extra rest3 =>
                simp [Moist.CEK.evalBuiltinPassThrough]
  simp [Moist.CEK.evalBuiltin, hpass]
  cases hconst : Moist.CEK.extractConsts args <;>
    simp [hconst, evalBuiltinConst_ChooseUnit_none]

set_option maxHeartbeats 0 in
theorem evalBuiltin_Trace_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .Trace args = none := by
  have hpass : Moist.CEK.evalBuiltinPassThrough .Trace args = none := by
    cases args with
    | nil => rfl
    | cons result rest =>
        cases rest with
        | nil => rfl
        | cons msg rest2 =>
            cases rest2 with
            | nil => exact False.elim (h rfl)
            | cons extra rest3 =>
                simp [Moist.CEK.evalBuiltinPassThrough]
  simp [Moist.CEK.evalBuiltin, hpass]
  cases hconst : Moist.CEK.extractConsts args <;>
    simp [hconst, evalBuiltinConst_Trace_none]

set_option maxHeartbeats 0 in
theorem evalBuiltin_IfThenElse_none_of_cond_not_bool {elseV thenV cond : CekValue}
    (h : ∀ b, cond ≠ .VCon (.Bool b)) :
    Moist.CEK.evalBuiltin .IfThenElse [elseV, thenV, cond] = none := by
  have hpass : Moist.CEK.evalBuiltinPassThrough .IfThenElse [elseV, thenV, cond] = none := by
    cases cond with
    | VCon c =>
        cases c with
        | Bool b => exact False.elim (h b rfl)
        | Integer i => rfl
        | ByteString bs => rfl
        | String s => rfl
        | Unit => rfl
        | Data d => rfl
        | Pair p => rfl
        | PairData p => rfl
        | ConstList xs => rfl
        | ConstDataList xs => rfl
        | ConstPairDataList xs => rfl
        | ConstArray xs => rfl
        | Bls12_381_G1_element => rfl
        | Bls12_381_G2_element => rfl
        | Bls12_381_MlResult => rfl
    | VLam body ρ => rfl
    | VDelay body ρ => rfl
    | VConstr tag fields => rfl
    | VBuiltin b args expected => rfl
  simp [Moist.CEK.evalBuiltin, hpass]
  cases hconst : Moist.CEK.extractConsts [elseV, thenV, cond] <;>
    simp [hconst, evalBuiltinConst_IfThenElse_none]

set_option maxHeartbeats 0 in
theorem evalBuiltin_ChooseUnit_none_of_unit_not_unit {result unitV : CekValue}
    (h : unitV ≠ .VCon .Unit) :
    Moist.CEK.evalBuiltin .ChooseUnit [result, unitV] = none := by
  have hpass : Moist.CEK.evalBuiltinPassThrough .ChooseUnit [result, unitV] = none := by
    cases unitV with
    | VCon c =>
        cases c with
        | Unit => exact False.elim (h rfl)
        | Integer i => rfl
        | ByteString bs => rfl
        | String s => rfl
        | Bool b => rfl
        | Data d => rfl
        | Pair p => rfl
        | PairData p => rfl
        | ConstList xs => rfl
        | ConstDataList xs => rfl
        | ConstPairDataList xs => rfl
        | ConstArray xs => rfl
        | Bls12_381_G1_element => rfl
        | Bls12_381_G2_element => rfl
        | Bls12_381_MlResult => rfl
    | VLam body ρ => rfl
    | VDelay body ρ => rfl
    | VConstr tag fields => rfl
    | VBuiltin b args expected => rfl
  simp [Moist.CEK.evalBuiltin, hpass]
  cases hconst : Moist.CEK.extractConsts [result, unitV] <;>
    simp [hconst, evalBuiltinConst_ChooseUnit_none]

set_option maxHeartbeats 0 in
theorem evalBuiltin_Trace_none_of_msg_not_string {result msg : CekValue}
    (h : ∀ s, msg ≠ .VCon (.String s)) :
    Moist.CEK.evalBuiltin .Trace [result, msg] = none := by
  have hpass : Moist.CEK.evalBuiltinPassThrough .Trace [result, msg] = none := by
    cases msg with
    | VCon c =>
        cases c with
        | String s => exact False.elim (h s rfl)
        | Integer i => rfl
        | ByteString bs => rfl
        | Unit => rfl
        | Bool b => rfl
        | Data d => rfl
        | Pair p => rfl
        | PairData p => rfl
        | ConstList xs => rfl
        | ConstDataList xs => rfl
        | ConstPairDataList xs => rfl
        | ConstArray xs => rfl
        | Bls12_381_G1_element => rfl
        | Bls12_381_G2_element => rfl
        | Bls12_381_MlResult => rfl
    | VLam body ρ => rfl
    | VDelay body ρ => rfl
    | VConstr tag fields => rfl
    | VBuiltin b args expected => rfl
  simp [Moist.CEK.evalBuiltin, hpass]
  cases hconst : Moist.CEK.extractConsts [result, msg] <;>
    simp [hconst, evalBuiltinConst_Trace_none]

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_DropList_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .DropList cs = none := by
  cases cs with
  | nil =>
      rfl
  | cons c rest =>
      cases rest with
      | nil =>
          cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_DropList_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .DropList args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_DropList_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_DropList_none_of_pair_not_supported {a b : CekValue}
    (hlist : ∀ cs i, ¬ (a = .VCon (.ConstList cs) ∧ b = .VCon (.Integer i)))
    (hdata : ∀ ds i, ¬ (a = .VCon (.ConstDataList ds) ∧ b = .VCon (.Integer i))) :
    Moist.CEK.evalBuiltin .DropList [a, b] = none := by
  cases a with
  | VCon ca =>
      cases b with
      | VCon cb =>
          cases ca <;> cases cb <;> try rfl
          · exact False.elim (hlist _ _ ⟨rfl, rfl⟩)
          · exact False.elim (hdata _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases ca <;> rfl
      | VDelay body ρ => cases ca <;> rfl
      | VConstr tag fields => cases ca <;> rfl
      | VBuiltin fn args expected => cases ca <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_IndexArray_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .IndexArray cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_IndexArray_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .IndexArray args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_IndexArray_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_IndexArray_none_of_pair_not_supported {a b : CekValue}
    (hshape : ∀ i cs, ¬ (a = .VCon (.Integer i) ∧ b = .VCon (.ConstArray cs))) :
    Moist.CEK.evalBuiltin .IndexArray [a, b] = none := by
  cases a with
  | VCon ca =>
      cases b with
      | VCon cb =>
          cases ca <;> cases cb <;> try rfl
          exact False.elim (hshape _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases ca <;> rfl
      | VDelay body ρ => cases ca <;> rfl
      | VConstr tag fields => cases ca <;> rfl
      | VBuiltin fn args expected => cases ca <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

theorem evalBuiltin_IndexArray_none_of_negative {cs : List Const} {i : Int}
    (hneg : i < 0) :
    Moist.CEK.evalBuiltin .IndexArray [.VCon (.Integer i), .VCon (.ConstArray cs)] = none := by
  change
    (match (if i < 0 then none else cs[i.toNat]?) with
    | some c => some (CekValue.VCon c)
    | none => none) = none
  simp [hneg]

theorem evalBuiltin_IndexArray_none_of_nonnegative_get_none {cs : List Const} {i : Int}
    (hge : 0 ≤ i) (hget : cs[i.toNat]? = none) :
    Moist.CEK.evalBuiltin .IndexArray [.VCon (.Integer i), .VCon (.ConstArray cs)] = none := by
  have hnlt : ¬ i < 0 := (Int.not_lt).mpr hge
  change
    (match (if i < 0 then none else cs[i.toNat]?) with
    | some c => some (CekValue.VCon c)
    | none => none) = none
  simp [hnlt, hget]
axiom evalBuiltinSym_active_ok_InsertCoin : BuiltinOkSound .InsertCoin
axiom evalBuiltinSym_active_ok_LookupCoin : BuiltinOkSound .LookupCoin
axiom evalBuiltinSym_active_ok_ScaleValue : BuiltinOkSound .ScaleValue
axiom evalBuiltinSym_active_ok_UnionValue : BuiltinOkSound .UnionValue
axiom evalBuiltinSym_active_ok_ValueContains : BuiltinOkSound .ValueContains
axiom evalBuiltinSym_active_ok_ValueData : BuiltinOkSound .ValueData
axiom evalBuiltinSym_active_ok_UnValueData : BuiltinOkSound .UnValueData
axiom evalBuiltinSym_active_ok_Bls12_381_G1_multiScalarMul : BuiltinOkSound .Bls12_381_G1_multiScalarMul
axiom evalBuiltinSym_active_ok_Bls12_381_G2_multiScalarMul : BuiltinOkSound .Bls12_381_G2_multiScalarMul
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_AddInteger :
    BuiltinErrorSound .AddInteger := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_AddInteger_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_AddInteger_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_AddInteger_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asInt aSym).guard (asInt bSym).guard)
                  (SymVal.const (SymConst.integer
                    (SExpr.add (asInt aSym).val (asInt bSym).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt aSym).guard (asInt bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ ib ia, cb = .VCon (.Integer ib) ∧ ca = .VCon (.Integer ia)
                  · rcases hshape with ⟨ib, ia, rfl, rfl⟩
                    have hga := asInt_guard_of_cek (m := m) (v := aSym) (i := ia) ha
                    have hgb := asInt_guard_of_cek (m := m) (v := bSym) (i := ib) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asInt aSym).guard (asInt bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asInt aSym).guard (asInt bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_AddInteger_none_of_pair_not_ints (by
                      intro ib ia h
                      exact hshape ⟨ib, ia, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_AddInteger_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_SubtractInteger :
    BuiltinErrorSound .SubtractInteger := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_SubtractInteger_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_SubtractInteger_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_SubtractInteger_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asInt aSym).guard (asInt bSym).guard)
                  (SymVal.const (SymConst.integer
                    (SExpr.sub (asInt aSym).val (asInt bSym).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt aSym).guard (asInt bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ ib ia, cb = .VCon (.Integer ib) ∧ ca = .VCon (.Integer ia)
                  · rcases hshape with ⟨ib, ia, rfl, rfl⟩
                    have hga := asInt_guard_of_cek (m := m) (v := aSym) (i := ia) ha
                    have hgb := asInt_guard_of_cek (m := m) (v := bSym) (i := ib) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asInt aSym).guard (asInt bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asInt aSym).guard (asInt bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_SubtractInteger_none_of_pair_not_ints (by
                      intro ib ia h
                      exact hshape ⟨ib, ia, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_SubtractInteger_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_MultiplyInteger :
    BuiltinErrorSound .MultiplyInteger := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_MultiplyInteger_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_MultiplyInteger_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_MultiplyInteger_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asInt aSym).guard (asInt bSym).guard)
                  (SymVal.const (SymConst.integer
                    (SExpr.mul (asInt aSym).val (asInt bSym).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt aSym).guard (asInt bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ ib ia, cb = .VCon (.Integer ib) ∧ ca = .VCon (.Integer ia)
                  · rcases hshape with ⟨ib, ia, rfl, rfl⟩
                    have hga := asInt_guard_of_cek (m := m) (v := aSym) (i := ia) ha
                    have hgb := asInt_guard_of_cek (m := m) (v := bSym) (i := ib) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asInt aSym).guard (asInt bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asInt aSym).guard (asInt bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_MultiplyInteger_none_of_pair_not_ints (by
                      intro ib ia h
                      exact hshape ⟨ib, ia, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_MultiplyInteger_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_DivideInteger :
    BuiltinErrorSound .DivideInteger := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_DivideInteger_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_DivideInteger_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_DivideInteger_eq bSym aSym] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases checked2_active_error hmem hactive with hinner | hproj
              · rcases hinner with ⟨inner, hinnerMem, hpArgs, hinnerActive⟩
                simp only [List.mem_cons, List.not_mem_nil] at hinnerMem
                rcases hinnerMem with hok | herr
                · subst inner
                  simp [outcomeErrorActive] at hinnerActive
                · rcases herr with herr | hfalse
                  · subst inner
                    have hp :=
                      (Moist.SMT.Semantics.evalBoolIs_and_true m
                        (asInt aSym).guard (asInt bSym).guard).mp hpArgs
                    obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                    obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                    have hz : ib = 0 :=
                      pcHolds_not_ne_int_zero heb
                        (by simpa [outcomeErrorActive, divisionGuard] using hinnerActive)
                    exact evalBuiltin_DivideInteger_none_of_divisor_zero (a := ia) (b := ib) hz
                  · cases hfalse
              · by_cases hshape :
                    ∃ ib ia, cb = .VCon (.Integer ib) ∧ ca = .VCon (.Integer ia)
                · rcases hshape with ⟨ib, ia, rfl, rfl⟩
                  have hga := asInt_guard_of_cek (m := m) (v := aSym) (i := ia) ha
                  have hgb := asInt_guard_of_cek (m := m) (v := bSym) (i := ib) hb
                  have hg :
                      pcHolds m
                        (SExpr.and (asInt aSym).guard (asInt bSym).guard) = true := by
                    simpa [pcHolds] using
                      ((Moist.SMT.Semantics.evalBoolIs_and_true m
                        (asInt aSym).guard (asInt bSym).guard).mpr
                          ⟨by simpa [pcHolds] using hga,
                           by simpa [pcHolds] using hgb⟩)
                  exact False.elim (pcHolds_not_contra hg hproj)
                · exact evalBuiltin_DivideInteger_none_of_pair_not_ints (by
                    intro ib ia h
                    exact hshape ⟨ib, ia, h.1, h.2⟩)
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_DivideInteger_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_QuotientInteger :
    BuiltinErrorSound .QuotientInteger := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_QuotientInteger_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_QuotientInteger_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_QuotientInteger_eq bSym aSym] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases checked2_active_error hmem hactive with hinner | hproj
              · rcases hinner with ⟨inner, hinnerMem, hpArgs, hinnerActive⟩
                simp only [List.mem_cons, List.not_mem_nil] at hinnerMem
                rcases hinnerMem with hok | herr
                · subst inner
                  simp [outcomeErrorActive] at hinnerActive
                · rcases herr with herr | hfalse
                  · subst inner
                    have hp :=
                      (Moist.SMT.Semantics.evalBoolIs_and_true m
                        (asInt aSym).guard (asInt bSym).guard).mp hpArgs
                    obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                    obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                    have hz : ib = 0 :=
                      pcHolds_not_ne_int_zero heb
                        (by simpa [outcomeErrorActive, divisionGuard] using hinnerActive)
                    exact evalBuiltin_QuotientInteger_none_of_divisor_zero (a := ia) (b := ib) hz
                  · cases hfalse
              · by_cases hshape :
                    ∃ ib ia, cb = .VCon (.Integer ib) ∧ ca = .VCon (.Integer ia)
                · rcases hshape with ⟨ib, ia, rfl, rfl⟩
                  have hga := asInt_guard_of_cek (m := m) (v := aSym) (i := ia) ha
                  have hgb := asInt_guard_of_cek (m := m) (v := bSym) (i := ib) hb
                  have hg :
                      pcHolds m
                        (SExpr.and (asInt aSym).guard (asInt bSym).guard) = true := by
                    simpa [pcHolds] using
                      ((Moist.SMT.Semantics.evalBoolIs_and_true m
                        (asInt aSym).guard (asInt bSym).guard).mpr
                          ⟨by simpa [pcHolds] using hga,
                           by simpa [pcHolds] using hgb⟩)
                  exact False.elim (pcHolds_not_contra hg hproj)
                · exact evalBuiltin_QuotientInteger_none_of_pair_not_ints (by
                    intro ib ia h
                    exact hshape ⟨ib, ia, h.1, h.2⟩)
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_QuotientInteger_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_RemainderInteger :
    BuiltinErrorSound .RemainderInteger := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_RemainderInteger_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_RemainderInteger_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_RemainderInteger_eq bSym aSym] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases checked2_active_error hmem hactive with hinner | hproj
              · rcases hinner with ⟨inner, hinnerMem, hpArgs, hinnerActive⟩
                simp only [List.mem_cons, List.not_mem_nil] at hinnerMem
                rcases hinnerMem with hok | herr
                · subst inner
                  simp [outcomeErrorActive] at hinnerActive
                · rcases herr with herr | hfalse
                  · subst inner
                    have hp :=
                      (Moist.SMT.Semantics.evalBoolIs_and_true m
                        (asInt aSym).guard (asInt bSym).guard).mp hpArgs
                    obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                    obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                    have hz : ib = 0 :=
                      pcHolds_not_ne_int_zero heb
                        (by simpa [outcomeErrorActive, divisionGuard] using hinnerActive)
                    exact evalBuiltin_RemainderInteger_none_of_divisor_zero (a := ia) (b := ib) hz
                  · cases hfalse
              · by_cases hshape :
                    ∃ ib ia, cb = .VCon (.Integer ib) ∧ ca = .VCon (.Integer ia)
                · rcases hshape with ⟨ib, ia, rfl, rfl⟩
                  have hga := asInt_guard_of_cek (m := m) (v := aSym) (i := ia) ha
                  have hgb := asInt_guard_of_cek (m := m) (v := bSym) (i := ib) hb
                  have hg :
                      pcHolds m
                        (SExpr.and (asInt aSym).guard (asInt bSym).guard) = true := by
                    simpa [pcHolds] using
                      ((Moist.SMT.Semantics.evalBoolIs_and_true m
                        (asInt aSym).guard (asInt bSym).guard).mpr
                          ⟨by simpa [pcHolds] using hga,
                           by simpa [pcHolds] using hgb⟩)
                  exact False.elim (pcHolds_not_contra hg hproj)
                · exact evalBuiltin_RemainderInteger_none_of_pair_not_ints (by
                    intro ib ia h
                    exact hshape ⟨ib, ia, h.1, h.2⟩)
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_RemainderInteger_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_ModInteger :
    BuiltinErrorSound .ModInteger := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_ModInteger_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_ModInteger_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_ModInteger_eq bSym aSym] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases checked2_active_error hmem hactive with hinner | hproj
              · rcases hinner with ⟨inner, hinnerMem, hpArgs, hinnerActive⟩
                simp only [List.mem_cons, List.not_mem_nil] at hinnerMem
                rcases hinnerMem with hok | herr
                · subst inner
                  simp [outcomeErrorActive] at hinnerActive
                · rcases herr with herr | hfalse
                  · subst inner
                    have hp :=
                      (Moist.SMT.Semantics.evalBoolIs_and_true m
                        (asInt aSym).guard (asInt bSym).guard).mp hpArgs
                    obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                    obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                    have hz : ib = 0 :=
                      pcHolds_not_ne_int_zero heb
                        (by simpa [outcomeErrorActive, divisionGuard] using hinnerActive)
                    exact evalBuiltin_ModInteger_none_of_divisor_zero (a := ia) (b := ib) hz
                  · cases hfalse
              · by_cases hshape :
                    ∃ ib ia, cb = .VCon (.Integer ib) ∧ ca = .VCon (.Integer ia)
                · rcases hshape with ⟨ib, ia, rfl, rfl⟩
                  have hga := asInt_guard_of_cek (m := m) (v := aSym) (i := ia) ha
                  have hgb := asInt_guard_of_cek (m := m) (v := bSym) (i := ib) hb
                  have hg :
                      pcHolds m
                        (SExpr.and (asInt aSym).guard (asInt bSym).guard) = true := by
                    simpa [pcHolds] using
                      ((Moist.SMT.Semantics.evalBoolIs_and_true m
                        (asInt aSym).guard (asInt bSym).guard).mpr
                          ⟨by simpa [pcHolds] using hga,
                           by simpa [pcHolds] using hgb⟩)
                  exact False.elim (pcHolds_not_contra hg hproj)
                · exact evalBuiltin_ModInteger_none_of_pair_not_ints (by
                    intro ib ia h
                    exact hshape ⟨ib, ia, h.1, h.2⟩)
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_ModInteger_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_EqualsInteger :
    BuiltinErrorSound .EqualsInteger := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_EqualsInteger_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_EqualsInteger_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_EqualsInteger_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asInt aSym).guard (asInt bSym).guard)
                  (SymVal.const (SymConst.bool
                    (SExpr.eq (asInt aSym).val (asInt bSym).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt aSym).guard (asInt bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ ib ia, cb = .VCon (.Integer ib) ∧ ca = .VCon (.Integer ia)
                  · rcases hshape with ⟨ib, ia, rfl, rfl⟩
                    have hga := asInt_guard_of_cek (m := m) (v := aSym) (i := ia) ha
                    have hgb := asInt_guard_of_cek (m := m) (v := bSym) (i := ib) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asInt aSym).guard (asInt bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asInt aSym).guard (asInt bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_EqualsInteger_none_of_pair_not_ints (by
                      intro ib ia h
                      exact hshape ⟨ib, ia, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_EqualsInteger_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_LessThanInteger :
    BuiltinErrorSound .LessThanInteger := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_LessThanInteger_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_LessThanInteger_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_LessThanInteger_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asInt aSym).guard (asInt bSym).guard)
                  (SymVal.const (SymConst.bool
                    (SExpr.lt (asInt aSym).val (asInt bSym).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt aSym).guard (asInt bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ ib ia, cb = .VCon (.Integer ib) ∧ ca = .VCon (.Integer ia)
                  · rcases hshape with ⟨ib, ia, rfl, rfl⟩
                    have hga := asInt_guard_of_cek (m := m) (v := aSym) (i := ia) ha
                    have hgb := asInt_guard_of_cek (m := m) (v := bSym) (i := ib) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asInt aSym).guard (asInt bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asInt aSym).guard (asInt bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_LessThanInteger_none_of_pair_not_ints (by
                      intro ib ia h
                      exact hshape ⟨ib, ia, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_LessThanInteger_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_LessThanEqualsInteger :
    BuiltinErrorSound .LessThanEqualsInteger := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_LessThanEqualsInteger_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_LessThanEqualsInteger_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_LessThanEqualsInteger_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asInt aSym).guard (asInt bSym).guard)
                  (SymVal.const (SymConst.bool
                    (SExpr.le (asInt aSym).val (asInt bSym).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt aSym).guard (asInt bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ ib ia, cb = .VCon (.Integer ib) ∧ ca = .VCon (.Integer ia)
                  · rcases hshape with ⟨ib, ia, rfl, rfl⟩
                    have hga := asInt_guard_of_cek (m := m) (v := aSym) (i := ia) ha
                    have hgb := asInt_guard_of_cek (m := m) (v := bSym) (i := ib) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asInt aSym).guard (asInt bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asInt aSym).guard (asInt bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_LessThanEqualsInteger_none_of_pair_not_ints (by
                      intro ib ia h
                      exact hshape ⟨ib, ia, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_LessThanEqualsInteger_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_AppendByteString :
    BuiltinErrorSound .AppendByteString := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_AppendByteString_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_AppendByteString_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_AppendByteString_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asBytes aSym).guard (asBytes bSym).guard)
                  (SymVal.const (SymConst.bytes
                    (SExpr.seqAppend (asBytes aSym).val (asBytes bSym).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asBytes aSym).guard (asBytes bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ bs2 bs1, cb = .VCon (.ByteString bs2) ∧
                        ca = .VCon (.ByteString bs1)
                  · rcases hshape with ⟨bs2, bs1, rfl, rfl⟩
                    have hga := asBytes_guard_of_cek (m := m) (v := aSym) (bs := bs1) ha
                    have hgb := asBytes_guard_of_cek (m := m) (v := bSym) (bs := bs2) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asBytes aSym).guard (asBytes bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asBytes aSym).guard (asBytes bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_AppendByteString_none_of_pair_not_bytes (by
                      intro bs2 bs1 h
                      exact hshape ⟨bs2, bs1, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_AppendByteString_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_ConsByteString :
    BuiltinErrorSound .ConsByteString := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_ConsByteString_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bsSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_ConsByteString_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons nSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_ConsByteString_eq bsSym nSym] at hmem
              obtain ⟨cbs, cn, hbsArg, hnArg, rfl⟩ :=
                symValListToCekList_pair hargs
              have hpath := checked2_active_error hmem hactive
              rcases hpath with hinner | hproj
              · rcases hinner with ⟨inner, hinner, hpArgs, hinnerActive⟩
                change inner ∈
                  (let inByte := SExpr.and (SExpr.ge (asInt nSym).val (.int 0))
                    (SExpr.le (asInt nSym).val (.int 255))
                   [Outcome.ok inByte
                      (SymVal.const (SymConst.bytes
                        (SExpr.seqAppend (SExpr.seqUnit (asInt nSym).val)
                          (asBytes bsSym).val))),
                    Outcome.error (SExpr.not inByte)]) at hinner
                simp only [List.mem_cons, List.not_mem_nil] at hinner
                rcases hinner with hok | herr
                · subst inner
                  simp [outcomeErrorActive] at hinnerActive
                · rcases herr with herr | hfalse
                  · subst inner
                    have hnotRange :
                        pcHolds m
                          (SExpr.not
                            (SExpr.and (SExpr.ge (asInt nSym).val (.int 0))
                              (SExpr.le (asInt nSym).val (.int 255)))) = true := by
                      simpa [outcomeErrorActive] using hinnerActive
                    change pcHolds m
                      (SExpr.and (asInt nSym).guard (asBytes bsSym).guard) = true at hpArgs
                    have hp :=
                      (Moist.SMT.Semantics.evalBoolIs_and_true m
                        (asInt nSym).guard (asBytes bsSym).guard).mp hpArgs
                    obtain ⟨n, rfl, hnEval⟩ := asInt_sound hnArg hp.1
                    obtain ⟨bs, rfl, hbsEval⟩ := asBytes_sound hbsArg hp.2
                    by_cases hbad : n < 0 ∨ 255 < n
                    · exact evalBuiltin_ConsByteString_none_of_byte_out_of_range hbad
                    · have hbad' := not_or.mp hbad
                      have hge : 0 ≤ n := (Int.not_lt).mp hbad'.1
                      have hle : n ≤ 255 := (Int.not_lt).mp hbad'.2
                      have hgePc : pcHolds m
                          (SExpr.ge (asInt nSym).val (.int 0)) = true :=
                        pcHolds_ge_int_intro hnEval
                          (by simp [Moist.SMT.Semantics.eval]) hge
                      have hlePc : pcHolds m
                          (SExpr.le (asInt nSym).val (.int 255)) = true :=
                        pcHolds_le_int_intro hnEval
                          (by simp [Moist.SMT.Semantics.eval]) hle
                      have hrange : pcHolds m
                          (SExpr.and (SExpr.ge (asInt nSym).val (.int 0))
                            (SExpr.le (asInt nSym).val (.int 255))) = true :=
                        pcHolds_and_intro hgePc hlePc
                      exact False.elim (pcHolds_not_contra hrange hnotRange)
                  · cases hfalse
              · by_cases hshape :
                  ∃ bs n, cbs = .VCon (.ByteString bs) ∧ cn = .VCon (.Integer n)
                · rcases hshape with ⟨bs, n, rfl, rfl⟩
                  have hgBs := asBytes_guard_of_cek (m := m)
                    (v := bsSym) (bs := bs) hbsArg
                  have hgN := asInt_guard_of_cek (m := m)
                    (v := nSym) (i := n) hnArg
                  have hprojGuard : pcHolds m
                      (SExpr.and (asInt nSym).guard (asBytes bsSym).guard) = true :=
                    pcHolds_and_intro hgN hgBs
                  exact False.elim (pcHolds_not_contra hprojGuard hproj)
                · exact evalBuiltin_ConsByteString_none_of_pair_not_byte_int
                    (bs := cbs) (n := cn) (by
                      intro bytes i h
                      exact hshape ⟨bytes, i, h⟩)
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_ConsByteString_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_SliceByteString :
    BuiltinErrorSound .SliceByteString := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_SliceByteString_none_of_length_ne_three (by
        intro h3
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bsSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_SliceByteString_none_of_length_ne_three (by
            intro h3
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons lenSym rest2 =>
          cases rest2 with
          | nil =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_SliceByteString_none_of_length_ne_three (by
                intro h3
                have htwo : cargs.length = 2 := by simpa using hlen
                omega)
          | cons startSym rest3 =>
              cases rest3 with
              | nil =>
                  rw [evalBuiltinSym_SliceByteString_eq bsSym lenSym startSym] at hmem
                  change out ∈
                    [Outcome.ok
                      (SExpr.all [(asInt startSym).guard, (asInt lenSym).guard,
                        (asBytes bsSym).guard])
                      (SymVal.const (SymConst.bytes
                        (SExpr.seqExtract (asBytes bsSym).val
                          (SExpr.ite (SExpr.lt (asInt startSym).val (.int 0))
                            (.int 0) (asInt startSym).val)
                          (SExpr.ite (SExpr.lt (asInt lenSym).val (.int 0))
                            (.int 0) (asInt lenSym).val)))),
                     Outcome.error (SExpr.not
                      (SExpr.all [(asInt startSym).guard, (asInt lenSym).guard,
                        (asBytes bsSym).guard]))] at hmem
                  simp only [List.mem_cons, List.not_mem_nil] at hmem
                  obtain ⟨cbs, clen, cstart, hbsArg, hlenArg, hstartArg, rfl⟩ :=
                    symValListToCekList_triple hargs
                  rcases hmem with hok | herr
                  · subst out
                    simp [outcomeErrorActive] at hactive
                  · rcases herr with herr | hfalse
                    · subst out
                      by_cases hshape :
                          ∃ bs len start,
                            cbs = .VCon (.ByteString bs) ∧
                            clen = .VCon (.Integer len) ∧
                            cstart = .VCon (.Integer start)
                      · rcases hshape with ⟨bs, len, start, rfl, rfl, rfl⟩
                        have hgStart := asInt_guard_of_cek (m := m)
                          (v := startSym) (i := start) hstartArg
                        have hgLen := asInt_guard_of_cek (m := m)
                          (v := lenSym) (i := len) hlenArg
                        have hgBs := asBytes_guard_of_cek (m := m)
                          (v := bsSym) (bs := bs) hbsArg
                        have hguard : pcHolds m
                            (SExpr.all [(asInt startSym).guard,
                              (asInt lenSym).guard, (asBytes bsSym).guard]) = true :=
                          pcHolds_all3_intro hgStart hgLen hgBs
                        exact False.elim (pcHolds_not_contra hguard hactive)
                      · exact evalBuiltin_SliceByteString_none_of_triple_not_byte_int_int
                          (bs := cbs) (len := clen) (start := cstart) (by
                            intro bytes len start h
                            exact hshape ⟨bytes, len, start, h⟩)
                    · cases hfalse
              | cons extra rest4 =>
                  have hlen := symValListToCekList_length hargs
                  exact evalBuiltin_SliceByteString_none_of_length_ne_three (by
                    intro h3
                    have hfour : 4 ≤ cargs.length := by
                      rw [hlen]
                      simp
                    omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_LengthOfByteString :
    BuiltinErrorSound .LengthOfByteString := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_LengthOfByteString_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bsSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_LengthOfByteString_eq bsSym] at hmem
          change out ∈
            [Outcome.ok (asBytes bsSym).guard
              (SymVal.const (SymConst.integer (SExpr.seqLen (asBytes bsSym).val))),
             Outcome.error (SExpr.not (asBytes bsSym).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cbs, hbs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              by_cases hshape : ∃ bs, cbs = .VCon (.ByteString bs)
              · rcases hshape with ⟨bs, rfl⟩
                have hg := asBytes_guard_of_cek (m := m) (v := bsSym) (bs := bs) hbs
                exact False.elim (pcHolds_not_contra hg hactive)
              · exact evalBuiltin_LengthOfByteString_none_of_single_not_bytes (by
                  intro bs h
                  exact hshape ⟨bs, h⟩)
            · cases hfalse
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_LengthOfByteString_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_IndexByteString :
    BuiltinErrorSound .IndexByteString := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_IndexByteString_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons idxSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_IndexByteString_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons bsSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_IndexByteString_eq idxSym bsSym] at hmem
              obtain ⟨cidx, cbs, hidxArg, hbsArg, rfl⟩ :=
                symValListToCekList_pair hargs
              have hpath := checked2_active_error hmem hactive
              rcases hpath with hinner | hproj
              · rcases hinner with ⟨inner, hinner, hpArgs, hinnerActive⟩
                change inner ∈
                  (let inRange := SExpr.and (SExpr.ge (asInt idxSym).val (.int 0))
                    (SExpr.lt (asInt idxSym).val (SExpr.seqLen (asBytes bsSym).val))
                   [Outcome.ok inRange
                      (SymVal.const (SymConst.integer
                        (SExpr.seqNth (asBytes bsSym).val (asInt idxSym).val))),
                    Outcome.error (SExpr.not inRange)]) at hinner
                simp only [List.mem_cons, List.not_mem_nil] at hinner
                rcases hinner with hok | herr
                · subst inner
                  simp [outcomeErrorActive] at hinnerActive
                · rcases herr with herr | hfalse
                  · subst inner
                    have hnotRange :
                        pcHolds m
                          (SExpr.not
                            (SExpr.and (SExpr.ge (asInt idxSym).val (.int 0))
                              (SExpr.lt (asInt idxSym).val
                                (SExpr.seqLen (asBytes bsSym).val)))) = true := by
                      simpa [outcomeErrorActive] using hinnerActive
                    change pcHolds m
                      (SExpr.and (asBytes bsSym).guard (asInt idxSym).guard) = true at hpArgs
                    have hp :=
                      (Moist.SMT.Semantics.evalBoolIs_and_true m
                        (asBytes bsSym).guard (asInt idxSym).guard).mp hpArgs
                    obtain ⟨idx, rfl, hidxEval⟩ := asInt_sound hidxArg hp.2
                    obtain ⟨bs, rfl, hbsEval⟩ := asBytes_sound hbsArg hp.1
                    by_cases hneg : idx < 0
                    · exact evalBuiltin_IndexByteString_none_of_negative hneg
                    · have hge : 0 ≤ idx := (Int.not_lt).mp hneg
                      by_cases hout : Int.ofNat bs.size ≤ idx
                      · exact evalBuiltin_IndexByteString_none_of_nonnegative_out_of_range
                          hge hout
                      · have hlt : idx < Int.ofNat bs.size := Int.not_le.mp hout
                        have hlenEval := Moist.SMT.Semantics.eval_seqLen_of
                          (m := m) (a := (asBytes bsSym).val) hbsEval
                        change SmtSem.eval m (SExpr.seqLen (asBytes bsSym).val) =
                          some (Moist.SMT.Semantics.SVal.int (Int.ofNat bs.size)) at hlenEval
                        have hgePc : pcHolds m
                            (SExpr.ge (asInt idxSym).val (.int 0)) = true :=
                          pcHolds_ge_int_intro hidxEval
                            (by simp [Moist.SMT.Semantics.eval]) hge
                        have hltPc : pcHolds m
                            (SExpr.lt (asInt idxSym).val
                              (SExpr.seqLen (asBytes bsSym).val)) = true :=
                          pcHolds_lt_int_intro hidxEval hlenEval hlt
                        have hrange : pcHolds m
                            (SExpr.and (SExpr.ge (asInt idxSym).val (.int 0))
                              (SExpr.lt (asInt idxSym).val
                                (SExpr.seqLen (asBytes bsSym).val))) = true :=
                          pcHolds_and_intro hgePc hltPc
                        exact False.elim (pcHolds_not_contra hrange hnotRange)
                  · cases hfalse
              · by_cases hshape :
                  ∃ idx bs, cidx = .VCon (.Integer idx) ∧
                    cbs = .VCon (.ByteString bs)
                · rcases hshape with ⟨idx, bs, rfl, rfl⟩
                  have hgBs := asBytes_guard_of_cek (m := m)
                    (v := bsSym) (bs := bs) hbsArg
                  have hgIdx := asInt_guard_of_cek (m := m)
                    (v := idxSym) (i := idx) hidxArg
                  have hprojGuard : pcHolds m
                      (SExpr.and (asBytes bsSym).guard (asInt idxSym).guard) = true :=
                    pcHolds_and_intro hgBs hgIdx
                  exact False.elim (pcHolds_not_contra hprojGuard hproj)
                · exact evalBuiltin_IndexByteString_none_of_pair_not_int_byte
                    (idx := cidx) (bs := cbs) (by
                      intro idx bs h
                      exact hshape ⟨idx, bs, h⟩)
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_IndexByteString_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_EqualsByteString :
    BuiltinErrorSound .EqualsByteString := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_EqualsByteString_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_EqualsByteString_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_EqualsByteString_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asBytes aSym).guard (asBytes bSym).guard)
                  (SymVal.const (SymConst.bool
                    (SExpr.eq (asBytes aSym).val (asBytes bSym).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asBytes aSym).guard (asBytes bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ bs2 bs1, cb = .VCon (.ByteString bs2) ∧
                        ca = .VCon (.ByteString bs1)
                  · rcases hshape with ⟨bs2, bs1, rfl, rfl⟩
                    have hga := asBytes_guard_of_cek (m := m) (v := aSym) (bs := bs1) ha
                    have hgb := asBytes_guard_of_cek (m := m) (v := bSym) (bs := bs2) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asBytes aSym).guard (asBytes bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asBytes aSym).guard (asBytes bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_EqualsByteString_none_of_pair_not_bytes (by
                      intro bs2 bs1 h
                      exact hshape ⟨bs2, bs1, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_EqualsByteString_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_LessThanByteString :
    BuiltinErrorSound .LessThanByteString := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_LessThanByteString_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_LessThanByteString_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_LessThanByteString_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asBytes aSym).guard (asBytes bSym).guard)
                  (SymVal.const (SymConst.bool
                    (.app "bytes_lt" [(asBytes aSym).val, (asBytes bSym).val]))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asBytes aSym).guard (asBytes bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ bs2 bs1, cb = .VCon (.ByteString bs2) ∧
                        ca = .VCon (.ByteString bs1)
                  · rcases hshape with ⟨bs2, bs1, rfl, rfl⟩
                    have hga := asBytes_guard_of_cek (m := m) (v := aSym) (bs := bs1) ha
                    have hgb := asBytes_guard_of_cek (m := m) (v := bSym) (bs := bs2) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asBytes aSym).guard (asBytes bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asBytes aSym).guard (asBytes bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_LessThanByteString_none_of_pair_not_bytes (by
                      intro bs2 bs1 h
                      exact hshape ⟨bs2, bs1, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_LessThanByteString_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_LessThanEqualsByteString :
    BuiltinErrorSound .LessThanEqualsByteString := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_LessThanEqualsByteString_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_LessThanEqualsByteString_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_LessThanEqualsByteString_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asBytes aSym).guard (asBytes bSym).guard)
                  (SymVal.const (SymConst.bool
                    (.app "bytes_le" [(asBytes aSym).val, (asBytes bSym).val]))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asBytes aSym).guard (asBytes bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ bs2 bs1, cb = .VCon (.ByteString bs2) ∧
                        ca = .VCon (.ByteString bs1)
                  · rcases hshape with ⟨bs2, bs1, rfl, rfl⟩
                    have hga := asBytes_guard_of_cek (m := m) (v := aSym) (bs := bs1) ha
                    have hgb := asBytes_guard_of_cek (m := m) (v := bSym) (bs := bs2) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asBytes aSym).guard (asBytes bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asBytes aSym).guard (asBytes bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_LessThanEqualsByteString_none_of_pair_not_bytes (by
                      intro bs2 bs1 h
                      exact hshape ⟨bs2, bs1, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_LessThanEqualsByteString_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
axiom evalBuiltinSym_active_error_Sha2_256 : BuiltinErrorSound .Sha2_256
axiom evalBuiltinSym_active_error_Sha3_256 : BuiltinErrorSound .Sha3_256
axiom evalBuiltinSym_active_error_Blake2b_256 : BuiltinErrorSound .Blake2b_256
axiom evalBuiltinSym_active_error_VerifyEd25519Signature : BuiltinErrorSound .VerifyEd25519Signature
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_AppendString :
    BuiltinErrorSound .AppendString := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_AppendString_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_AppendString_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_AppendString_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asString aSym).guard (asString bSym).guard)
                  (SymVal.const (SymConst.string
                    (SExpr.strAppend (asString aSym).val (asString bSym).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asString aSym).guard (asString bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ sb sa, cb = .VCon (.String sb) ∧ ca = .VCon (.String sa)
                  · rcases hshape with ⟨sb, sa, rfl, rfl⟩
                    have hga := asString_guard_of_cek (m := m) (v := aSym) (s := sa) ha
                    have hgb := asString_guard_of_cek (m := m) (v := bSym) (s := sb) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asString aSym).guard (asString bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asString aSym).guard (asString bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_AppendString_none_of_pair_not_strings (by
                      intro sb sa h
                      exact hshape ⟨sb, sa, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_AppendString_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_EqualsString :
    BuiltinErrorSound .EqualsString := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_EqualsString_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_EqualsString_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_EqualsString_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asString aSym).guard (asString bSym).guard)
                  (SymVal.const (SymConst.bool
                    (SExpr.eq (asString aSym).val (asString bSym).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asString aSym).guard (asString bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ sb sa, cb = .VCon (.String sb) ∧ ca = .VCon (.String sa)
                  · rcases hshape with ⟨sb, sa, rfl, rfl⟩
                    have hga := asString_guard_of_cek (m := m) (v := aSym) (s := sa) ha
                    have hgb := asString_guard_of_cek (m := m) (v := bSym) (s := sb) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asString aSym).guard (asString bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asString aSym).guard (asString bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_EqualsString_none_of_pair_not_strings (by
                      intro sb sa h
                      exact hshape ⟨sb, sa, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_EqualsString_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_EncodeUtf8 :
    BuiltinErrorSound .EncodeUtf8 := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_EncodeUtf8_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons sSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_EncodeUtf8_eq sSym] at hmem
          change out ∈
            [Outcome.ok (asString sSym).guard
              (SymVal.const (SymConst.bytes
                (.app "uplc_encodeUtf8" [(asString sSym).val]))),
             Outcome.error (SExpr.not (asString sSym).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cs, hs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              by_cases hshape : ∃ s, cs = .VCon (.String s)
              · rcases hshape with ⟨s, rfl⟩
                have hg := asString_guard_of_cek (m := m) (v := sSym) (s := s) hs
                exact False.elim (pcHolds_not_contra hg hactive)
              · exact evalBuiltin_EncodeUtf8_none_of_single_not_string (by
                  intro s h
                  exact hshape ⟨s, h⟩)
            · cases hfalse
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_EncodeUtf8_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_DecodeUtf8 :
    BuiltinErrorSound .DecodeUtf8 := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_DecodeUtf8_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bsSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_DecodeUtf8_eq bsSym] at hmem
          obtain ⟨cbs, hbs, rfl⟩ := symValListToCekList_singleton hargs
          rcases checked2_active_error hmem hactive with hinner | hproj
          · rcases hinner with ⟨inner, hinnerMem, hguard, hinnerActive⟩
            simp only [List.mem_cons, List.not_mem_nil] at hinnerMem
            rcases hinnerMem with hok | herr
            · subst inner
              simp [outcomeErrorActive] at hinnerActive
            · rcases herr with herr | hfalse
              · subst inner
                by_cases hshape : ∃ bs, cbs = .VCon (.ByteString bs)
                · rcases hshape with ⟨bs, rfl⟩
                  obtain ⟨bs', hcv, hbsEval⟩ := asBytes_sound hbs hguard
                  cases hcv
                  have hfalseValid :
                      SmtSem.evalBoolIs m
                        (.app "valid_utf8" [(asBytes bsSym).val]) false = true :=
                    (Moist.SMT.Semantics.evalBoolIs_not_true m
                      (.app "valid_utf8" [(asBytes bsSym).val])).mp
                      (by simpa [outcomeErrorActive, pcHolds] using hinnerActive)
                  have hnotValid :=
                    Moist.SMT.Semantics.not_validUtf8_of_evalBoolIs_validUtf8_false
                      (m := m) (e := (asBytes bsSym).val) (bs := bs) hbsEval hfalseValid
                  exact evalBuiltin_DecodeUtf8_none_of_invalid hnotValid
                · exact evalBuiltin_DecodeUtf8_none_of_single_not_bytes (by
                    intro bs h
                    exact hshape ⟨bs, h⟩)
              · cases hfalse
          · by_cases hshape : ∃ bs, cbs = .VCon (.ByteString bs)
            · rcases hshape with ⟨bs, rfl⟩
              have hg := asBytes_guard_of_cek (m := m) (v := bsSym) (bs := bs) hbs
              exact False.elim (pcHolds_not_contra hg hproj)
            · exact evalBuiltin_DecodeUtf8_none_of_single_not_bytes (by
                intro bs h
                exact hshape ⟨bs, h⟩)
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_DecodeUtf8_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_IfThenElse :
    BuiltinErrorSound .IfThenElse := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_IfThenElse_none_of_length_ne_three (by
        intro h3
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons elseV rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_IfThenElse_none_of_length_ne_three (by
            intro h3
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons thenV rest2 =>
          cases rest2 with
          | nil =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_IfThenElse_none_of_length_ne_three (by
                intro h3
                have htwo : cargs.length = 2 := by simpa using hlen
                omega)
          | cons cond rest3 =>
              cases rest3 with
              | nil =>
                  rw [evalBuiltinSym_IfThenElse_eq elseV thenV cond] at hmem
                  change out ∈
                    [Outcome.ok (SExpr.and (asBool cond).guard (asBool cond).val) thenV,
                     Outcome.ok (SExpr.and (asBool cond).guard
                      (SExpr.not (asBool cond).val)) elseV,
                     Outcome.error (SExpr.not (asBool cond).guard)] at hmem
                  simp only [List.mem_cons, List.not_mem_nil] at hmem
                  obtain ⟨celse, cthen, ccond, helse, hthen, hcond, rfl⟩ :=
                    symValListToCekList_triple hargs
                  rcases hmem with hthenBranch | hrest
                  · subst out
                    simp [outcomeErrorActive] at hactive
                  · rcases hrest with helseBranch | herr
                    · subst out
                      simp [outcomeErrorActive] at hactive
                    · rcases herr with herr | hfalse
                      · subst out
                        by_cases hshape : ∃ b, ccond = .VCon (.Bool b)
                        · rcases hshape with ⟨b, rfl⟩
                          have hg := asBool_guard_of_cek (m := m) (v := cond) (b := b) hcond
                          exact False.elim (pcHolds_not_contra hg hactive)
                        · exact evalBuiltin_IfThenElse_none_of_cond_not_bool (by
                            intro b h
                            exact hshape ⟨b, h⟩)
                      · cases hfalse
              | cons extra rest4 =>
                  have hlen := symValListToCekList_length hargs
                  exact evalBuiltin_IfThenElse_none_of_length_ne_three (by
                    intro h3
                    have hfour : 4 ≤ cargs.length := by
                      rw [hlen]
                      simp
                    omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_ChooseUnit :
    BuiltinErrorSound .ChooseUnit := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_ChooseUnit_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons result rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_ChooseUnit_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons unitV rest2 =>
          cases rest2 with
          | nil =>
              obtain ⟨cresult, cunit, hresult, hunit, rfl⟩ :=
                symValListToCekList_pair hargs
              cases unitV with
              | const c =>
                  cases c <;>
                    try
                      (change out ∈ err at hmem
                       simp [err] at hmem
                       subst out
                       exact evalBuiltin_ChooseUnit_none_of_unit_not_unit (by
                         intro hcu
                         subst cunit
                         have hc := symConstToCek_unit (by
                           simpa [symValToCek?] using hunit)
                         cases hc))
                  case unit =>
                    change out ∈ ok result at hmem
                    simp [ok] at hmem
                    rcases hmem with ⟨rfl, rfl⟩
                    simp [outcomeErrorActive] at hactive
              | dyn e =>
                  change out ∈
                    [Outcome.ok (SExpr.isCtor "VUnit" e) result,
                     Outcome.error (SExpr.not (SExpr.isCtor "VUnit" e))] at hmem
                  simp only [List.mem_cons, List.not_mem_nil] at hmem
                  rcases hmem with hok | herr
                  · subst out
                    simp [outcomeErrorActive] at hactive
                  · rcases herr with herr | hfalse
                    · subst out
                      by_cases hshape : cunit = .VCon .Unit
                      · subst cunit
                        have hg := unitGuard_complete (m := m) (u := SymVal.dyn e) hunit
                        exact False.elim (pcHolds_not_contra hg hactive)
                      · exact evalBuiltin_ChooseUnit_none_of_unit_not_unit hshape
                    · cases hfalse
              | pair a b =>
                  change out ∈ err at hmem
                  simp [err] at hmem
                  subst out
                  exact evalBuiltin_ChooseUnit_none_of_unit_not_unit (by
                    intro hcu
                    subst cunit
                    simp [symValToCek?] at hunit
                    cases ha : symValToCek? m a <;> simp [ha] at hunit
                    rename_i cva
                    cases hb : symValToCek? m b <;> simp [hb] at hunit
                    rename_i cvb
                    cases cva <;> cases cvb <;> simp at hunit)
              | constr tag fields =>
                  change out ∈ err at hmem
                  simp [err] at hmem
                  subst out
                  exact evalBuiltin_ChooseUnit_none_of_unit_not_unit (by
                    intro hcu
                    subst cunit
                    simp [symValToCek?] at hunit
                    cases htag : SmtSem.eval m tag <;> simp [htag] at hunit
                    rename_i sv
                    cases sv <;> simp [htag] at hunit
                    rename_i i
                    by_cases hneg : i < 0
                    · exact False.elim ((Int.not_le).mpr hneg hunit.1)
                    · cases hfields : symValListToCekList? m fields <;> simp [hfields] at hunit)
              | lam body ρ =>
                  change out ∈ err at hmem
                  simp [err] at hmem
                  subst out
                  exact evalBuiltin_ChooseUnit_none_of_unit_not_unit (by
                    intro hcu
                    subst cunit
                    simp [symValToCek?] at hunit
                    cases henv : symEnvToCek? m ρ <;> simp [henv] at hunit)
              | delay body ρ =>
                  change out ∈ err at hmem
                  simp [err] at hmem
                  subst out
                  exact evalBuiltin_ChooseUnit_none_of_unit_not_unit (by
                    intro hcu
                    subst cunit
                    simp [symValToCek?] at hunit
                    cases henv : symEnvToCek? m ρ <;> simp [henv] at hunit)
              | builtin b bargs ea =>
                  change out ∈ err at hmem
                  simp [err] at hmem
                  subst out
                  exact evalBuiltin_ChooseUnit_none_of_unit_not_unit (by
                    intro hcu
                    subst cunit
                    simp [symValToCek?] at hunit
                    cases hbargs : symValListToCekList? m bargs <;> simp [hbargs] at hunit)
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_ChooseUnit_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_Trace :
    BuiltinErrorSound .Trace := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_Trace_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons result rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_Trace_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons msg rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_Trace_eq result msg] at hmem
              simp [checked2, ok, Outcome.guard] at hmem
              obtain ⟨cresult, cmsg, hresult, hmsg, rfl⟩ :=
                symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · subst out
                by_cases hshape : ∃ s, cmsg = .VCon (.String s)
                · rcases hshape with ⟨s, rfl⟩
                  have hg := asString_guard_of_cek (m := m) (v := msg) (s := s) hmsg
                  exact False.elim (pcHolds_not_contra hg hactive)
                · exact evalBuiltin_Trace_none_of_msg_not_string (by
                    intro s h
                    exact hshape ⟨s, h⟩)
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_Trace_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinConst_FstPair_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .FstPair cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_SndPair_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .SndPair cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> rfl

theorem evalBuiltin_FstPair_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .FstPair args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_FstPair_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_SndPair_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .SndPair args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_SndPair_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_FstPair_none_of_single_not_pair {cv : CekValue}
    (hp : ∀ a b, cv ≠ .VCon (.Pair (a, b)))
    (hpd : ∀ a b, cv ≠ .VCon (.PairData (a, b))) :
    Moist.CEK.evalBuiltin .FstPair [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Pair p =>
          cases p with
          | mk a b => exact False.elim (hp a b rfl)
      | PairData p =>
          cases p with
          | mk a b => exact False.elim (hpd a b rfl)
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Data d => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

theorem evalBuiltin_SndPair_none_of_single_not_pair {cv : CekValue}
    (hp : ∀ a b, cv ≠ .VCon (.Pair (a, b)))
    (hpd : ∀ a b, cv ≠ .VCon (.PairData (a, b))) :
    Moist.CEK.evalBuiltin .SndPair [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Pair p =>
          cases p with
          | mk a b => exact False.elim (hp a b rfl)
      | PairData p =>
          cases p with
          | mk a b => exact False.elim (hpd a b rfl)
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Data d => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_ChooseData_none (cs : List Const) :
    Moist.CEK.evalBuiltinConst .ChooseData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest => cases rest <;> cases c <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_ChooseData_none_of_length_ne_six {args : List CekValue}
    (h : args.length ≠ 6) :
    Moist.CEK.evalBuiltin .ChooseData args = none := by
  have hpass : Moist.CEK.evalBuiltinPassThrough .ChooseData args = none := by
    cases args with
    | nil => rfl
    | cons a r1 =>
        cases r1 with
        | nil => rfl
        | cons b r2 =>
            cases r2 with
            | nil => rfl
            | cons c r3 =>
                cases r3 with
                | nil => rfl
                | cons d r4 =>
                    cases r4 with
                    | nil => rfl
                    | cons e r5 =>
                        cases r5 with
                        | nil => rfl
                        | cons f r6 =>
                            cases r6 with
                            | nil => exact False.elim (h rfl)
                            | cons g r7 =>
                                simp [Moist.CEK.evalBuiltinPassThrough]
  simp [Moist.CEK.evalBuiltin, hpass]
  cases hconst : Moist.CEK.extractConsts args with
  | none => simp
  | some cs =>
      have hnone := evalBuiltinConst_ChooseData_none cs
      simp [hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_ChooseData_none_of_six_not_data
    {cb ci cl cm cc cd : CekValue}
    (h : ∀ d, cd ≠ .VCon (.Data d)) :
    Moist.CEK.evalBuiltin .ChooseData [cb, ci, cl, cm, cc, cd] = none := by
  have hpass :
      Moist.CEK.evalBuiltinPassThrough .ChooseData [cb, ci, cl, cm, cc, cd] =
        none := by
    cases cd with
    | VCon c =>
        cases c with
        | Data d => exact False.elim (h d rfl)
        | Integer i => rfl
        | ByteString bs => rfl
        | String s => rfl
        | Unit => rfl
        | Bool b => rfl
        | Pair p => rfl
        | PairData p => rfl
        | ConstList xs => rfl
        | ConstDataList xs => rfl
        | ConstPairDataList xs => rfl
        | ConstArray xs => rfl
        | Bls12_381_G1_element => rfl
        | Bls12_381_G2_element => rfl
        | Bls12_381_MlResult => rfl
    | VLam body ρ => rfl
    | VDelay body ρ => rfl
    | VConstr tag fields => rfl
    | VBuiltin b args expected => rfl
  simp [Moist.CEK.evalBuiltin, hpass]
  cases hconst : Moist.CEK.extractConsts [cb, ci, cl, cm, cc, cd] with
  | none => simp
  | some cs =>
      have hnone := evalBuiltinConst_ChooseData_none cs
      simp [hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_ChooseList_none (cs : List Const) :
    Moist.CEK.evalBuiltinConst .ChooseList cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest => cases rest <;> cases c <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_ChooseList_none_of_length_ne_three {args : List CekValue}
    (h : args.length ≠ 3) :
    Moist.CEK.evalBuiltin .ChooseList args = none := by
  have hpass : Moist.CEK.evalBuiltinPassThrough .ChooseList args = none := by
    cases args with
    | nil => rfl
    | cons a r1 =>
        cases r1 with
        | nil => rfl
        | cons b r2 =>
            cases r2 with
            | nil => rfl
            | cons c r3 =>
                cases r3 with
                | nil => exact False.elim (h rfl)
                | cons d r4 =>
                    simp [Moist.CEK.evalBuiltinPassThrough]
  simp [Moist.CEK.evalBuiltin, hpass]
  cases hconst : Moist.CEK.extractConsts args with
  | none => simp
  | some cs =>
      have hnone := evalBuiltinConst_ChooseList_none cs
      simp [hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_ChooseList_none_of_triple_not_list
    {consCase nilCase xs : CekValue}
    (hdl : ∀ ds, xs ≠ .VCon (.ConstDataList ds))
    (hvl : ∀ cs, xs ≠ .VCon (.ConstList cs)) :
    Moist.CEK.evalBuiltin .ChooseList [consCase, nilCase, xs] = none := by
  have hpass :
      Moist.CEK.evalBuiltinPassThrough .ChooseList [consCase, nilCase, xs] =
        none := by
    cases xs with
    | VCon c =>
        cases c with
        | ConstDataList ds => exact False.elim (hdl ds rfl)
        | ConstList cs => exact False.elim (hvl cs rfl)
        | Integer i => rfl
        | ByteString bs => rfl
        | String s => rfl
        | Unit => rfl
        | Bool b => rfl
        | Data d => rfl
        | Pair p => rfl
        | PairData p => rfl
        | ConstPairDataList xs => rfl
        | ConstArray xs => rfl
        | Bls12_381_G1_element => rfl
        | Bls12_381_G2_element => rfl
        | Bls12_381_MlResult => rfl
    | VLam body ρ => rfl
    | VDelay body ρ => rfl
    | VConstr tag fields => rfl
    | VBuiltin b args expected => rfl
  simp [Moist.CEK.evalBuiltin, hpass]
  cases hconst : Moist.CEK.extractConsts [consCase, nilCase, xs] with
  | none => simp
  | some cs =>
      have hnone := evalBuiltinConst_ChooseList_none cs
      simp [hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_NullList_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .NullList cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest => cases c <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_NullList_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .NullList args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro h1
        apply h
        omega
      have hnone := evalBuiltinConst_NullList_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_NullList_none_of_single_not_list {xs : CekValue}
    (hdl : ∀ ds, xs ≠ .VCon (.ConstDataList ds))
    (hvl : ∀ cs, xs ≠ .VCon (.ConstList cs)) :
    Moist.CEK.evalBuiltin .NullList [xs] = none := by
  cases xs with
  | VCon c =>
      cases c with
      | ConstDataList ds => exact False.elim (hdl ds rfl)
      | ConstList cs => exact False.elim (hvl cs rfl)
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Data d => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_MkCons_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .MkCons cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> try rfl
              case ConstDataList ds =>
                cases c2 <;> cases c3 <;> cases rest3 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinPassThrough_MkCons_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltinPassThrough .MkCons args = none := by
  cases args with
  | nil => rfl
  | cons a r1 =>
      cases r1 with
      | nil =>
          cases a with
          | VCon c => cases c <;> rfl
          | VLam body ρ => rfl
          | VDelay body ρ => rfl
          | VConstr tag fields => rfl
          | VBuiltin b args expected => rfl
      | cons b r2 =>
          cases r2 with
          | nil => exact False.elim (h rfl)
          | cons c r3 =>
              simp [Moist.CEK.evalBuiltinPassThrough]

set_option maxHeartbeats 0 in
theorem evalBuiltin_MkCons_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .MkCons args = none := by
  have hpass := evalBuiltinPassThrough_MkCons_none_of_length_ne_two h
  simp [Moist.CEK.evalBuiltin, hpass]
  cases hconst : Moist.CEK.extractConsts args with
  | none => simp
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro h2
        apply h
        omega
      have hnone := evalBuiltinConst_MkCons_none_of_length_ne_two hcs
      simp [hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_MkCons_none_of_pair_not_consable {tail head : CekValue}
    (hdata :
      ∀ ds d, ¬(tail = .VCon (.ConstDataList ds) ∧ head = .VCon (.Data d)))
    (hconst :
      ∀ cs c, ¬(tail = .VCon (.ConstList cs) ∧ head = .VCon c)) :
    Moist.CEK.evalBuiltin .MkCons [tail, head] = none := by
  cases tail with
  | VCon tc =>
      cases tc with
      | ConstDataList ds =>
          cases head with
          | VCon hc =>
              cases hc with
              | Data d => exact False.elim (hdata ds d ⟨rfl, rfl⟩)
              | Integer i => rfl
              | ByteString bs => rfl
              | String s => rfl
              | Unit => rfl
              | Bool b => rfl
              | Pair p => rfl
              | PairData p => rfl
              | ConstList xs => rfl
              | ConstDataList xs => rfl
              | ConstPairDataList xs => rfl
              | ConstArray xs => rfl
              | Bls12_381_G1_element => rfl
              | Bls12_381_G2_element => rfl
              | Bls12_381_MlResult => rfl
          | VLam body ρ => rfl
          | VDelay body ρ => rfl
          | VConstr tag fields => rfl
          | VBuiltin b args expected => rfl
      | ConstList cs =>
          cases head with
          | VCon hc => exact False.elim (hconst cs hc ⟨rfl, rfl⟩)
          | VLam body ρ => rfl
          | VDelay body ρ => rfl
          | VConstr tag fields => rfl
          | VBuiltin b args expected => rfl
      | Integer i => cases head <;> rfl
      | ByteString bs => cases head <;> rfl
      | String s => cases head <;> rfl
      | Unit => cases head <;> rfl
      | Bool b => cases head <;> rfl
      | Data d => cases head <;> rfl
      | Pair p => cases head <;> rfl
      | PairData p => cases head <;> rfl
      | ConstPairDataList xs => cases head <;> rfl
      | ConstArray xs => cases head <;> rfl
      | Bls12_381_G1_element => cases head <;> rfl
      | Bls12_381_G2_element => cases head <;> rfl
      | Bls12_381_MlResult => cases head <;> rfl
  | VLam body ρ => cases head <;> rfl
  | VDelay body ρ => cases head <;> rfl
  | VConstr tag fields => cases head <;> rfl
  | VBuiltin b args expected => cases head <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_HeadList_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .HeadList cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> try rfl
          case ConstDataList ds =>
            cases ds <;> cases c2 <;> cases rest <;> rfl
          case ConstList xs =>
            cases xs <;> cases c2 <;> cases rest <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_TailList_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .TailList cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> try rfl
          case ConstDataList ds =>
            cases ds <;> cases c2 <;> cases rest <;> rfl
          case ConstList xs =>
            cases xs <;> cases c2 <;> cases rest <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_HeadList_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .HeadList args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro h1
        apply h
        omega
      have hnone := evalBuiltinConst_HeadList_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_TailList_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .TailList args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro h1
        apply h
        omega
      have hnone := evalBuiltinConst_TailList_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_HeadList_none_of_single_not_nonempty_list {xs : CekValue}
    (hdl : ∀ d ds, xs ≠ .VCon (.ConstDataList (d :: ds)))
    (hvl : ∀ c cs, xs ≠ .VCon (.ConstList (c :: cs))) :
    Moist.CEK.evalBuiltin .HeadList [xs] = none := by
  cases xs with
  | VCon c =>
      cases c with
      | ConstDataList ds =>
          cases ds with
          | nil => rfl
          | cons d ds => exact False.elim (hdl d ds rfl)
      | ConstList cs =>
          cases cs with
          | nil => rfl
          | cons c cs => exact False.elim (hvl c cs rfl)
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Data d => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_TailList_none_of_single_not_nonempty_list {xs : CekValue}
    (hdl : ∀ d ds, xs ≠ .VCon (.ConstDataList (d :: ds)))
    (hvl : ∀ c cs, xs ≠ .VCon (.ConstList (c :: cs))) :
    Moist.CEK.evalBuiltin .TailList [xs] = none := by
  cases xs with
  | VCon c =>
      cases c with
      | ConstDataList ds =>
          cases ds with
          | nil => rfl
          | cons d ds => exact False.elim (hdl d ds rfl)
      | ConstList cs =>
          cases cs with
          | nil => rfl
          | cons c cs => exact False.elim (hvl c cs rfl)
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Data d => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem asDataList_nonempty_guard_of_cek {m : SmtSem.Model} {v : SymVal}
    {d : Moist.Plutus.Data} {ds : List Moist.Plutus.Data}
    (hv : symValToCek? m v = some (.VCon (.ConstDataList (d :: ds)))) :
    pcHolds m
      (SExpr.and (asDataList v).guard
        (SExpr.not (SExpr.isCtor "DNil" (asDataList v).val))) = true := by
  have hg := asDataList_guard_of_cek (m := m) (v := v) (xs := d :: ds) hv
  obtain ⟨xs, hcv, heval⟩ := asDataList_sound hv hg
  injection hcv with hconst
  injection hconst with hxs
  subst xs
  have hfalse := Moist.SMT.Semantics.evalBoolIs_isDNil_false_of_dataList_cons heval
  have hnot :
      pcHolds m (SExpr.not (SExpr.isCtor "DNil" (asDataList v).val)) = true := by
    simpa [pcHolds] using
      (Moist.SMT.Semantics.evalBoolIs_not_true m
        (SExpr.isCtor "DNil" (asDataList v).val)).mpr hfalse
  exact pcHolds_and_intro hg hnot

set_option maxHeartbeats 0 in
theorem asConstList_nonempty_guard_of_cek {m : SmtSem.Model} {v : SymVal}
    {c : Const} {cs : List Const}
    (hv : symValToCek? m v = some (.VCon (.ConstList (c :: cs)))) :
    pcHolds m
      (SExpr.and (asConstList v).guard
        (SExpr.not (SExpr.isCtor "VNil" (asConstList v).val))) = true := by
  have hg := asConstList_guard_of_cek (m := m) (v := v) (cs := c :: cs) hv
  obtain ⟨vals, cs', hcv, heval, hconsts⟩ := asConstList_sound hv hg
  injection hcv with hconst
  injection hconst with hcsEq
  subst cs'
  cases vals with
  | nil =>
      simp [semValListToConstList?] at hconsts
  | cons vh vt =>
      have hfalse := Moist.SMT.Semantics.evalBoolIs_isVNil_false_of_valList_cons heval
      have hnot :
          pcHolds m (SExpr.not (SExpr.isCtor "VNil" (asConstList v).val)) = true := by
        simpa [pcHolds] using
          (Moist.SMT.Semantics.evalBoolIs_not_true m
            (SExpr.isCtor "VNil" (asConstList v).val)).mpr hfalse
      exact pcHolds_and_intro hg hnot

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_FstPair : BuiltinErrorSound .FstPair := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      exact evalBuiltin_FstPair_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by
          simpa using symValListToCekList_length hargs
        omega)
  | cons p rest =>
      cases rest with
      | nil =>
          change out ∈
            (let pp := asPair p
             let pd := asPairData p
             [Outcome.ok pp.guard pp.val.1,
              Outcome.ok pd.guard (.const (.data pd.val.1)),
              Outcome.error (SExpr.not (SExpr.or pp.guard pd.guard))]) at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cp, hp, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hokPair | hokPairData | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              simp [outcomeErrorActive] at hactive
              by_cases hpCek : ∃ a b, cp = .VCon (.Pair (a, b))
              · rcases hpCek with ⟨a, b, rfl⟩
                have hg := asPair_guard_of_cek (m := m) (v := p) (a := a) (b := b) hp
                exact False.elim
                  (pcHolds_not_or_contra_left (m := m)
                    (a := (asPair p).guard) (b := (asPairData p).guard)
                    hg hactive)
              · by_cases hpdCek : ∃ a b, cp = .VCon (.PairData (a, b))
                · rcases hpdCek with ⟨a, b, rfl⟩
                  have hg := asPairData_guard_of_cek (m := m) (v := p) (a := a) (b := b) hp
                  exact False.elim
                    (pcHolds_not_or_contra_right (m := m)
                      (a := (asPair p).guard) (b := (asPairData p).guard)
                      hg hactive)
                · exact evalBuiltin_FstPair_none_of_single_not_pair
                    (cv := cp)
                    (by
                      intro a b h
                      exact hpCek ⟨a, b, h⟩)
                    (by
                      intro a b h
                      exact hpdCek ⟨a, b, h⟩)
            · cases hfalse
      | cons extra rest2 =>
          exact evalBuiltin_FstPair_none_of_length_ne_one (by
            intro h1
            have hlen := symValListToCekList_length hargs
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_SndPair : BuiltinErrorSound .SndPair := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      exact evalBuiltin_SndPair_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by
          simpa using symValListToCekList_length hargs
        omega)
  | cons p rest =>
      cases rest with
      | nil =>
          change out ∈
            (let pp := asPair p
             let pd := asPairData p
             [Outcome.ok pp.guard pp.val.2,
              Outcome.ok pd.guard (.const (.data pd.val.2)),
              Outcome.error (SExpr.not (SExpr.or pp.guard pd.guard))]) at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cp, hp, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hokPair | hokPairData | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              simp [outcomeErrorActive] at hactive
              by_cases hpCek : ∃ a b, cp = .VCon (.Pair (a, b))
              · rcases hpCek with ⟨a, b, rfl⟩
                have hg := asPair_guard_of_cek (m := m) (v := p) (a := a) (b := b) hp
                exact False.elim
                  (pcHolds_not_or_contra_left (m := m)
                    (a := (asPair p).guard) (b := (asPairData p).guard)
                    hg hactive)
              · by_cases hpdCek : ∃ a b, cp = .VCon (.PairData (a, b))
                · rcases hpdCek with ⟨a, b, rfl⟩
                  have hg := asPairData_guard_of_cek (m := m) (v := p) (a := a) (b := b) hp
                  exact False.elim
                    (pcHolds_not_or_contra_right (m := m)
                      (a := (asPair p).guard) (b := (asPairData p).guard)
                      hg hactive)
                · exact evalBuiltin_SndPair_none_of_single_not_pair
                    (cv := cp)
                    (by
                      intro a b h
                      exact hpCek ⟨a, b, h⟩)
                    (by
                      intro a b h
                      exact hpdCek ⟨a, b, h⟩)
            · cases hfalse
      | cons extra rest2 =>
          exact evalBuiltin_SndPair_none_of_length_ne_one (by
            intro h1
            have hlen := symValListToCekList_length hargs
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_ChooseList : BuiltinErrorSound .ChooseList := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_ChooseList_none_of_length_ne_three (by
        intro h3
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons consCase rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_ChooseList_none_of_length_ne_three (by
            intro h3
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons nilCase rest2 =>
          cases rest2 with
          | nil =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_ChooseList_none_of_length_ne_three (by
                intro h3
                have htwo : cargs.length = 2 := by simpa using hlen
                omega)
          | cons xs rest3 =>
              cases rest3 with
              | nil =>
                  change out ∈
                    (let dl := asDataList xs
                     let vl := asConstList xs
                     let dBranches :=
                       [Outcome.ok (SExpr.and dl.guard (SExpr.isCtor "DNil" dl.val))
                          nilCase,
                        Outcome.ok
                          (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val)))
                          consCase]
                     let vBranches :=
                       [Outcome.ok (SExpr.and vl.guard (SExpr.isCtor "VNil" vl.val))
                          nilCase,
                        Outcome.ok
                          (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))
                          consCase]
                     dBranches ++ vBranches ++
                       [Outcome.error (SExpr.not (SExpr.or dl.guard vl.guard))]) at hmem
                  simp only [List.mem_cons, List.not_mem_nil, List.mem_append] at hmem
                  obtain ⟨ccons, cnil, cxs, hcons, hnil, hxs, rfl⟩ :=
                    symValListToCekList_triple hargs
                  rcases hmem with hokBranches | herr
                  · rcases hokBranches with hd | hv
                    · rcases hd with hdNil | hdCons
                      · subst out
                        simp [outcomeErrorActive] at hactive
                      · rcases hdCons with hdCons | hfalse
                        · subst out
                          simp [outcomeErrorActive] at hactive
                        · cases hfalse
                    · rcases hv with hvNil | hvCons
                      · subst out
                        simp [outcomeErrorActive] at hactive
                      · rcases hvCons with hvCons | hfalse
                        · subst out
                          simp [outcomeErrorActive] at hactive
                        · cases hfalse
                  · rcases herr with herr | hfalse
                    · subst out
                      simp [outcomeErrorActive] at hactive
                      by_cases hdl : ∃ ds, cxs = .VCon (.ConstDataList ds)
                      · rcases hdl with ⟨ds, rfl⟩
                        have hg := asDataList_guard_of_cek
                          (m := m) (v := xs) (xs := ds) hxs
                        exact False.elim
                          (pcHolds_not_or_contra_left
                            (m := m) (a := (asDataList xs).guard)
                            (b := (asConstList xs).guard) hg hactive)
                      · by_cases hvl : ∃ cs, cxs = .VCon (.ConstList cs)
                        · rcases hvl with ⟨cs, rfl⟩
                          have hg := asConstList_guard_of_cek
                            (m := m) (v := xs) (cs := cs) hxs
                          exact False.elim
                            (pcHolds_not_or_contra_right
                              (m := m) (a := (asDataList xs).guard)
                              (b := (asConstList xs).guard) hg hactive)
                        · exact evalBuiltin_ChooseList_none_of_triple_not_list
                            (consCase := ccons) (nilCase := cnil) (xs := cxs)
                            (by
                              intro ds h
                              exact hdl ⟨ds, h⟩)
                            (by
                              intro cs h
                              exact hvl ⟨cs, h⟩)
                    · cases hfalse
              | cons extra rest4 =>
                  have hlen := symValListToCekList_length hargs
                  exact evalBuiltin_ChooseList_none_of_length_ne_three (by
                    intro h3
                    have hfour : 4 ≤ cargs.length := by
                      rw [hlen]
                      simp
                    omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_MkCons : BuiltinErrorSound .MkCons := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_MkCons_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons tail rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_MkCons_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons head rest2 =>
          cases rest2 with
          | nil =>
              change out ∈
                (let dl := asDataList tail
                 let hd := asData head
                 let vl := asConstList tail
                 let hv := asConstVal head
                 let dataOk := SExpr.and dl.guard hd.guard
                 let constOk := SExpr.and vl.guard hv.guard
                 [Outcome.ok dataOk (.const (.dataList (.app "DCons" [hd.val, dl.val]))),
                  Outcome.ok constOk (.const (.constList (.app "VCons" [hv.val, vl.val]))),
                  Outcome.error (SExpr.not (SExpr.or dataOk constOk))]) at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨ctail, chead, htail, hhead, rfl⟩ :=
                symValListToCekList_pair hargs
              rcases hmem with hokData | hokConst | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  simp [outcomeErrorActive] at hactive
                  by_cases hdataCek :
                      ∃ ds d,
                        ctail = .VCon (.ConstDataList ds) ∧
                          chead = .VCon (.Data d)
                  · rcases hdataCek with ⟨ds, d, rfl, rfl⟩
                    have hgtail := asDataList_guard_of_cek
                      (m := m) (v := tail) (xs := ds) htail
                    have hghead := asData_guard_of_cek
                      (m := m) (v := head) (d := d) hhead
                    have hg := pcHolds_and_intro hgtail hghead
                    exact False.elim
                      (pcHolds_not_or_contra_left
                        (m := m)
                        (a := SExpr.and (asDataList tail).guard (asData head).guard)
                        (b := SExpr.and (asConstList tail).guard (asConstVal head).guard)
                        hg hactive)
                  · by_cases hconstCek :
                      ∃ cs c,
                        ctail = .VCon (.ConstList cs) ∧ chead = .VCon c
                    · rcases hconstCek with ⟨cs, c, rfl, rfl⟩
                      have hgtail := asConstList_guard_of_cek
                        (m := m) (v := tail) (cs := cs) htail
                      have hghead := asConstVal_guard_of_cek
                        (m := m) (v := head) (c := c) hhead
                      have hg := pcHolds_and_intro hgtail hghead
                      exact False.elim
                        (pcHolds_not_or_contra_right
                          (m := m)
                          (a := SExpr.and (asDataList tail).guard (asData head).guard)
                          (b := SExpr.and (asConstList tail).guard (asConstVal head).guard)
                          hg hactive)
                    · exact evalBuiltin_MkCons_none_of_pair_not_consable
                        (tail := ctail) (head := chead)
                        (by
                          intro ds d h
                          exact hdataCek ⟨ds, d, h⟩)
                        (by
                          intro cs c h
                          exact hconstCek ⟨cs, c, h⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_MkCons_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_HeadList : BuiltinErrorSound .HeadList := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_HeadList_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons xs rest =>
      cases rest with
      | nil =>
          change out ∈
            (let dl := asDataList xs
             let vl := asConstList xs
             [Outcome.ok
                (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val)))
                (.const (.data (.app "dhead" [dl.val]))),
              Outcome.ok
                (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))
                (.dyn (.app "vhead" [vl.val])),
              Outcome.error (SExpr.not
                (SExpr.or
                  (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val)))
                  (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))))]) at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cxs, hxs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hokData | hokConst | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              simp [outcomeErrorActive] at hactive
              by_cases hdl :
                  ∃ d ds, cxs = .VCon (.ConstDataList (d :: ds))
              · rcases hdl with ⟨d, ds, rfl⟩
                have hg := asDataList_nonempty_guard_of_cek
                  (m := m) (v := xs) (d := d) (ds := ds) hxs
                exact False.elim
                  (pcHolds_not_or_contra_left
                    (m := m)
                    (a := SExpr.and (asDataList xs).guard
                      (SExpr.not (SExpr.isCtor "DNil" (asDataList xs).val)))
                    (b := SExpr.and (asConstList xs).guard
                      (SExpr.not (SExpr.isCtor "VNil" (asConstList xs).val)))
                    hg hactive)
              · by_cases hvl :
                  ∃ c cs, cxs = .VCon (.ConstList (c :: cs))
                · rcases hvl with ⟨c, cs, rfl⟩
                  have hg := asConstList_nonempty_guard_of_cek
                    (m := m) (v := xs) (c := c) (cs := cs) hxs
                  exact False.elim
                    (pcHolds_not_or_contra_right
                      (m := m)
                      (a := SExpr.and (asDataList xs).guard
                        (SExpr.not (SExpr.isCtor "DNil" (asDataList xs).val)))
                      (b := SExpr.and (asConstList xs).guard
                        (SExpr.not (SExpr.isCtor "VNil" (asConstList xs).val)))
                      hg hactive)
                · exact evalBuiltin_HeadList_none_of_single_not_nonempty_list
                    (xs := cxs)
                    (by
                      intro d ds h
                      exact hdl ⟨d, ds, h⟩)
                    (by
                      intro c cs h
                      exact hvl ⟨c, cs, h⟩)
            · cases hfalse
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_HeadList_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_TailList : BuiltinErrorSound .TailList := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_TailList_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons xs rest =>
      cases rest with
      | nil =>
          change out ∈
            (let dl := asDataList xs
             let vl := asConstList xs
             [Outcome.ok
                (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val)))
                (.const (.dataList (.app "dtail" [dl.val]))),
              Outcome.ok
                (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))
                (.const (.constList (.app "vtail" [vl.val]))),
              Outcome.error (SExpr.not
                (SExpr.or
                  (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val)))
                  (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))))]) at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cxs, hxs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hokData | hokConst | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              simp [outcomeErrorActive] at hactive
              by_cases hdl :
                  ∃ d ds, cxs = .VCon (.ConstDataList (d :: ds))
              · rcases hdl with ⟨d, ds, rfl⟩
                have hg := asDataList_nonempty_guard_of_cek
                  (m := m) (v := xs) (d := d) (ds := ds) hxs
                exact False.elim
                  (pcHolds_not_or_contra_left
                    (m := m)
                    (a := SExpr.and (asDataList xs).guard
                      (SExpr.not (SExpr.isCtor "DNil" (asDataList xs).val)))
                    (b := SExpr.and (asConstList xs).guard
                      (SExpr.not (SExpr.isCtor "VNil" (asConstList xs).val)))
                    hg hactive)
              · by_cases hvl :
                  ∃ c cs, cxs = .VCon (.ConstList (c :: cs))
                · rcases hvl with ⟨c, cs, rfl⟩
                  have hg := asConstList_nonempty_guard_of_cek
                    (m := m) (v := xs) (c := c) (cs := cs) hxs
                  exact False.elim
                    (pcHolds_not_or_contra_right
                      (m := m)
                      (a := SExpr.and (asDataList xs).guard
                        (SExpr.not (SExpr.isCtor "DNil" (asDataList xs).val)))
                      (b := SExpr.and (asConstList xs).guard
                        (SExpr.not (SExpr.isCtor "VNil" (asConstList xs).val)))
                      hg hactive)
                · exact evalBuiltin_TailList_none_of_single_not_nonempty_list
                    (xs := cxs)
                    (by
                      intro d ds h
                      exact hdl ⟨d, ds, h⟩)
                    (by
                      intro c cs h
                      exact hvl ⟨c, cs, h⟩)
            · cases hfalse
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_TailList_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_NullList : BuiltinErrorSound .NullList := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_NullList_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons xs rest =>
      cases rest with
      | nil =>
          change out ∈
            (let dl := asDataList xs
             let vl := asConstList xs
             [Outcome.ok dl.guard (.const (.bool (SExpr.isCtor "DNil" dl.val))),
              Outcome.ok vl.guard (.const (.bool (SExpr.isCtor "VNil" vl.val))),
              Outcome.error (SExpr.not (SExpr.or dl.guard vl.guard))]) at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cxs, hxs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hd | hv | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              simp [outcomeErrorActive] at hactive
              by_cases hdl : ∃ ds, cxs = .VCon (.ConstDataList ds)
              · rcases hdl with ⟨ds, rfl⟩
                have hg := asDataList_guard_of_cek
                  (m := m) (v := xs) (xs := ds) hxs
                exact False.elim
                  (pcHolds_not_or_contra_left
                    (m := m) (a := (asDataList xs).guard)
                    (b := (asConstList xs).guard) hg hactive)
              · by_cases hvl : ∃ cs, cxs = .VCon (.ConstList cs)
                · rcases hvl with ⟨cs, rfl⟩
                  have hg := asConstList_guard_of_cek
                    (m := m) (v := xs) (cs := cs) hxs
                  exact False.elim
                    (pcHolds_not_or_contra_right
                      (m := m) (a := (asDataList xs).guard)
                      (b := (asConstList xs).guard) hg hactive)
                · exact evalBuiltin_NullList_none_of_single_not_list
                    (xs := cxs)
                    (by
                      intro ds h
                      exact hdl ⟨ds, h⟩)
                    (by
                      intro cs h
                      exact hvl ⟨cs, h⟩)
            · cases hfalse
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_NullList_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_ChooseData : BuiltinErrorSound .ChooseData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_ChooseData_none_of_length_ne_six (by
        intro h6
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bCase rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_ChooseData_none_of_length_ne_six (by
            intro h6
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons iCase rest2 =>
          cases rest2 with
          | nil =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_ChooseData_none_of_length_ne_six (by
                intro h6
                have htwo : cargs.length = 2 := by simpa using hlen
                omega)
          | cons listCase rest3 =>
              cases rest3 with
              | nil =>
                  have hlen := symValListToCekList_length hargs
                  exact evalBuiltin_ChooseData_none_of_length_ne_six (by
                    intro h6
                    have hthree : cargs.length = 3 := by simpa using hlen
                    omega)
              | cons mapCase rest4 =>
                  cases rest4 with
                  | nil =>
                      have hlen := symValListToCekList_length hargs
                      exact evalBuiltin_ChooseData_none_of_length_ne_six (by
                        intro h6
                        have hfour : cargs.length = 4 := by simpa using hlen
                        omega)
                  | cons constrCase rest5 =>
                      cases rest5 with
                      | nil =>
                          have hlen := symValListToCekList_length hargs
                          exact evalBuiltin_ChooseData_none_of_length_ne_six (by
                            intro h6
                            have hfive : cargs.length = 5 := by simpa using hlen
                            omega)
                      | cons dVal rest6 =>
                          cases rest6 with
                          | nil =>
                              change out ∈
                                (let d := asData dVal
                                 [Outcome.ok (SExpr.and d.guard (SExpr.isCtor "DConstr" d.val))
                                    constrCase,
                                  Outcome.ok (SExpr.and d.guard (SExpr.isCtor "DMap" d.val))
                                    mapCase,
                                  Outcome.ok (SExpr.and d.guard (SExpr.isCtor "DList" d.val))
                                    listCase,
                                  Outcome.ok (SExpr.and d.guard (SExpr.isCtor "DI" d.val))
                                    iCase,
                                  Outcome.ok (SExpr.and d.guard (SExpr.isCtor "DB" d.val))
                                    bCase,
                                  Outcome.error (SExpr.not d.guard)]) at hmem
                              simp only [List.mem_cons, List.not_mem_nil] at hmem
                              obtain ⟨cb, ci, cl, cm, cc, cd, hb, hi, hl, hm, hc, hd,
                                  rfl⟩ :=
                                symValListToCekList_six hargs
                              rcases hmem with hConstr | rest
                              · subst out
                                simp [outcomeErrorActive] at hactive
                              · rcases rest with hMap | rest
                                · subst out
                                  simp [outcomeErrorActive] at hactive
                                · rcases rest with hList | rest
                                  · subst out
                                    simp [outcomeErrorActive] at hactive
                                  · rcases rest with hI | rest
                                    · subst out
                                      simp [outcomeErrorActive] at hactive
                                    · rcases rest with hB | herr
                                      · subst out
                                        simp [outcomeErrorActive] at hactive
                                      · rcases herr with herr | hfalse
                                        · subst out
                                          simp [outcomeErrorActive] at hactive
                                          by_cases hdata : ∃ d, cd = .VCon (.Data d)
                                          · rcases hdata with ⟨d, rfl⟩
                                            have hg := asData_guard_of_cek
                                              (m := m) (v := dVal) (d := d) hd
                                            exact False.elim
                                              (pcHolds_not_contra hg hactive)
                                          · exact
                                              evalBuiltin_ChooseData_none_of_six_not_data
                                                (cb := cb) (ci := ci) (cl := cl)
                                                (cm := cm) (cc := cc) (cd := cd)
                                                (by
                                                  intro d hcd
                                                  exact hdata ⟨d, hcd⟩)
                                        · cases hfalse
                          | cons extra rest7 =>
                              have hlen := symValListToCekList_length hargs
                              exact evalBuiltin_ChooseData_none_of_length_ne_six (by
                                intro h6
                                have hseven : 7 ≤ cargs.length := by
                                  rw [hlen]
                                  simp
                                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_ConstrData :
    BuiltinErrorSound .ConstrData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_ConstrData_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons fieldsSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_ConstrData_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons tagSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_ConstrData_eq fieldsSym tagSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asInt tagSym).guard (asDataList fieldsSym).guard)
                  (SymVal.const (SymConst.data
                    (.app "DConstr" [(asInt tagSym).val, (asDataList fieldsSym).val]))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt tagSym).guard (asDataList fieldsSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cfields, ctag, hfields, htag, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ ds i,
                        cfields = .VCon (.ConstDataList ds) ∧
                          ctag = .VCon (.Integer i)
                  · rcases hshape with ⟨ds, i, rfl, rfl⟩
                    have hgf :=
                      asDataList_guard_of_cek (m := m) (v := fieldsSym) (xs := ds) hfields
                    have hgt := asInt_guard_of_cek (m := m) (v := tagSym) (i := i) htag
                    have hg :
                        pcHolds m
                          (SExpr.and (asInt tagSym).guard (asDataList fieldsSym).guard) =
                            true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asInt tagSym).guard (asDataList fieldsSym).guard).mpr
                            ⟨by simpa [pcHolds] using hgt,
                             by simpa [pcHolds] using hgf⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_ConstrData_none_of_pair_not_supported (by
                      intro ds i h
                      exact hshape ⟨ds, i, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_ConstrData_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_MapData :
    BuiltinErrorSound .MapData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_MapData_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons psSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_MapData_eq psSym] at hmem
          change out ∈
            [Outcome.ok (asPairDataList psSym).guard
              (SymVal.const (SymConst.data (.app "DMap" [(asPairDataList psSym).val]))),
             Outcome.error (SExpr.not (asPairDataList psSym).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cps, hps, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              by_cases hshape : ∃ ps, cps = .VCon (.ConstPairDataList ps)
              · rcases hshape with ⟨ps, rfl⟩
                have hg :=
                  asPairDataList_guard_of_cek (m := m) (v := psSym) (xs := ps) hps
                exact False.elim (pcHolds_not_contra hg hactive)
              · exact evalBuiltin_MapData_none_of_single_not_pair_data_list (by
                  intro ps h
                  exact hshape ⟨ps, h⟩)
            · cases hfalse
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_MapData_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_ListData :
    BuiltinErrorSound .ListData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_ListData_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons xsSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_ListData_eq xsSym] at hmem
          change out ∈
            [Outcome.ok (asDataList xsSym).guard
              (SymVal.const (SymConst.data (.app "DList" [(asDataList xsSym).val]))),
             Outcome.error (SExpr.not (asDataList xsSym).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cxs, hxs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              by_cases hshape : ∃ ds, cxs = .VCon (.ConstDataList ds)
              · rcases hshape with ⟨ds, rfl⟩
                have hg :=
                  asDataList_guard_of_cek (m := m) (v := xsSym) (xs := ds) hxs
                exact False.elim (pcHolds_not_contra hg hactive)
              · exact evalBuiltin_ListData_none_of_single_not_data_list (by
                  intro ds h
                  exact hshape ⟨ds, h⟩)
            · cases hfalse
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_ListData_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_IData :
    BuiltinErrorSound .IData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_IData_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons iSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_IData_eq iSym] at hmem
          change out ∈
            [Outcome.ok (asInt iSym).guard
              (SymVal.const (SymConst.data (.app "DI" [(asInt iSym).val]))),
             Outcome.error (SExpr.not (asInt iSym).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨ci, hi, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              by_cases hshape : ∃ i, ci = .VCon (.Integer i)
              · rcases hshape with ⟨i, rfl⟩
                have hg := asInt_guard_of_cek (m := m) (v := iSym) (i := i) hi
                exact False.elim (pcHolds_not_contra hg hactive)
              · exact evalBuiltin_IData_none_of_single_not_int (by
                  intro i h
                  exact hshape ⟨i, h⟩)
            · cases hfalse
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_IData_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_BData :
    BuiltinErrorSound .BData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_BData_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bsSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_BData_eq bsSym] at hmem
          change out ∈
            [Outcome.ok (asBytes bsSym).guard
              (SymVal.const (SymConst.data (.app "DB" [(asBytes bsSym).val]))),
             Outcome.error (SExpr.not (asBytes bsSym).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cbs, hbs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              by_cases hshape : ∃ bs, cbs = .VCon (.ByteString bs)
              · rcases hshape with ⟨bs, rfl⟩
                have hg := asBytes_guard_of_cek (m := m) (v := bsSym) (bs := bs) hbs
                exact False.elim (pcHolds_not_contra hg hactive)
              · exact evalBuiltin_BData_none_of_single_not_bytes (by
                  intro bs h
                  exact hshape ⟨bs, h⟩)
            · cases hfalse
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_BData_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_UnConstrData :
    BuiltinErrorSound .UnConstrData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_UnConstrData_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons dVal rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_UnConstrData_eq dVal] at hmem
          obtain ⟨cd, hd, rfl⟩ := symValListToCekList_singleton hargs
          have hpath := checked2_active_error hmem hactive
          rcases hpath with hinner | hproj
          · rcases hinner with ⟨inner, hinner, hpData, hinnerActive⟩
            change inner ∈
              (let is := SExpr.isCtor "DConstr" (asData dVal).val
               [Outcome.ok is
                  (SymVal.const (SymConst.pairData
                    (.app "DI" [.app "dataConstrTag" [(asData dVal).val]])
                    (.app "DList" [.app "dataConstrFields" [(asData dVal).val]]))),
                Outcome.error (SExpr.not is)]) at hinner
            simp only [List.mem_cons, List.not_mem_nil] at hinner
            rcases hinner with hok | herr
            · subst inner
              simp [outcomeErrorActive] at hinnerActive
            · rcases herr with herr | hfalse
              · subst inner
                by_cases hshape :
                    ∃ tag fields, cd = .VCon (.Data (.Constr tag fields))
                · rcases hshape with ⟨tag, fields, rfl⟩
                  obtain ⟨d, hdCd, hdEval⟩ := asData_sound hd hpData
                  injection hdCd with hdEq
                  injection hdEq with hdDataEq
                  subst d
                  have his := pcHolds_isDConstr_intro (m := m)
                    (e := (asData dVal).val) (tag := tag) (fields := fields) hdEval
                  exact False.elim (pcHolds_not_contra his hinnerActive)
                · exact evalBuiltin_UnConstrData_none_of_single_not_constr (cv := cd) (by
                    intro tag fields h
                    exact hshape ⟨tag, fields, h⟩)
              · cases hfalse
          · by_cases hshape :
              ∃ tag fields, cd = .VCon (.Data (.Constr tag fields))
            · rcases hshape with ⟨tag, fields, rfl⟩
              have hg := asData_guard_of_cek (m := m) (v := dVal)
                (d := .Constr tag fields) hd
              exact False.elim (pcHolds_not_contra hg hproj)
            · exact evalBuiltin_UnConstrData_none_of_single_not_constr (cv := cd) (by
                intro tag fields h
                exact hshape ⟨tag, fields, h⟩)
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_UnConstrData_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_UnMapData :
    BuiltinErrorSound .UnMapData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_UnMapData_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons dVal rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_UnMapData_eq dVal] at hmem
          obtain ⟨cd, hd, rfl⟩ := symValListToCekList_singleton hargs
          have hpath := checked2_active_error hmem hactive
          rcases hpath with hinner | hproj
          · rcases hinner with ⟨inner, hinner, hpData, hinnerActive⟩
            change inner ∈
              (let is := SExpr.isCtor "DMap" (asData dVal).val
               [Outcome.ok is
                  (SymVal.const (SymConst.pairDataList
                    (.app "dataMapEntries" [(asData dVal).val]))),
                Outcome.error (SExpr.not is)]) at hinner
            simp only [List.mem_cons, List.not_mem_nil] at hinner
            rcases hinner with hok | herr
            · subst inner
              simp [outcomeErrorActive] at hinnerActive
            · rcases herr with herr | hfalse
              · subst inner
                by_cases hshape : ∃ ps, cd = .VCon (.Data (.Map ps))
                · rcases hshape with ⟨ps, rfl⟩
                  obtain ⟨d, hdCd, hdEval⟩ := asData_sound hd hpData
                  injection hdCd with hdEq
                  injection hdEq with hdDataEq
                  subst d
                  have his := pcHolds_isDMap_intro (m := m)
                    (e := (asData dVal).val) (ps := ps) hdEval
                  exact False.elim (pcHolds_not_contra his hinnerActive)
                · exact evalBuiltin_UnMapData_none_of_single_not_map (cv := cd) (by
                    intro ps h
                    exact hshape ⟨ps, h⟩)
              · cases hfalse
          · by_cases hshape : ∃ ps, cd = .VCon (.Data (.Map ps))
            · rcases hshape with ⟨ps, rfl⟩
              have hg := asData_guard_of_cek (m := m) (v := dVal)
                (d := .Map ps) hd
              exact False.elim (pcHolds_not_contra hg hproj)
            · exact evalBuiltin_UnMapData_none_of_single_not_map (cv := cd) (by
                intro ps h
                exact hshape ⟨ps, h⟩)
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_UnMapData_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_UnListData :
    BuiltinErrorSound .UnListData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_UnListData_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons dVal rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_UnListData_eq dVal] at hmem
          obtain ⟨cd, hd, rfl⟩ := symValListToCekList_singleton hargs
          have hpath := checked2_active_error hmem hactive
          rcases hpath with hinner | hproj
          · rcases hinner with ⟨inner, hinner, hpData, hinnerActive⟩
            change inner ∈
              (let is := SExpr.isCtor "DList" (asData dVal).val
               [Outcome.ok is
                  (SymVal.const (SymConst.dataList
                    (.app "dataListItems" [(asData dVal).val]))),
                Outcome.error (SExpr.not is)]) at hinner
            simp only [List.mem_cons, List.not_mem_nil] at hinner
            rcases hinner with hok | herr
            · subst inner
              simp [outcomeErrorActive] at hinnerActive
            · rcases herr with herr | hfalse
              · subst inner
                by_cases hshape : ∃ xs, cd = .VCon (.Data (.List xs))
                · rcases hshape with ⟨xs, rfl⟩
                  obtain ⟨d, hdCd, hdEval⟩ := asData_sound hd hpData
                  injection hdCd with hdEq
                  injection hdEq with hdDataEq
                  subst d
                  have his := pcHolds_isDList_intro (m := m)
                    (e := (asData dVal).val) (xs := xs) hdEval
                  exact False.elim (pcHolds_not_contra his hinnerActive)
                · exact evalBuiltin_UnListData_none_of_single_not_list (cv := cd) (by
                    intro xs h
                    exact hshape ⟨xs, h⟩)
              · cases hfalse
          · by_cases hshape : ∃ xs, cd = .VCon (.Data (.List xs))
            · rcases hshape with ⟨xs, rfl⟩
              have hg := asData_guard_of_cek (m := m) (v := dVal)
                (d := .List xs) hd
              exact False.elim (pcHolds_not_contra hg hproj)
            · exact evalBuiltin_UnListData_none_of_single_not_list (cv := cd) (by
                intro xs h
                exact hshape ⟨xs, h⟩)
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_UnListData_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_UnIData :
    BuiltinErrorSound .UnIData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_UnIData_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons dVal rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_UnIData_eq dVal] at hmem
          obtain ⟨cd, hd, rfl⟩ := symValListToCekList_singleton hargs
          have hpath := checked2_active_error hmem hactive
          rcases hpath with hinner | hproj
          · rcases hinner with ⟨inner, hinner, hpData, hinnerActive⟩
            change inner ∈
              (let is := SExpr.isCtor "DI" (asData dVal).val
               [Outcome.ok is
                  (SymVal.const (SymConst.integer
                    (.app "dataInt" [(asData dVal).val]))),
                Outcome.error (SExpr.not is)]) at hinner
            simp only [List.mem_cons, List.not_mem_nil] at hinner
            rcases hinner with hok | herr
            · subst inner
              simp [outcomeErrorActive] at hinnerActive
            · rcases herr with herr | hfalse
              · subst inner
                by_cases hshape : ∃ i, cd = .VCon (.Data (.I i))
                · rcases hshape with ⟨i, rfl⟩
                  obtain ⟨d, hdCd, hdEval⟩ := asData_sound hd hpData
                  injection hdCd with hdEq
                  injection hdEq with hdDataEq
                  subst d
                  have his := pcHolds_isDI_intro (m := m)
                    (e := (asData dVal).val) (i := i) hdEval
                  exact False.elim (pcHolds_not_contra his hinnerActive)
                · exact evalBuiltin_UnIData_none_of_single_not_i (cv := cd) (by
                    intro i h
                    exact hshape ⟨i, h⟩)
              · cases hfalse
          · by_cases hshape : ∃ i, cd = .VCon (.Data (.I i))
            · rcases hshape with ⟨i, rfl⟩
              have hg := asData_guard_of_cek (m := m) (v := dVal)
                (d := .I i) hd
              exact False.elim (pcHolds_not_contra hg hproj)
            · exact evalBuiltin_UnIData_none_of_single_not_i (cv := cd) (by
                intro i h
                exact hshape ⟨i, h⟩)
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_UnIData_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_UnBData :
    BuiltinErrorSound .UnBData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_UnBData_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons dVal rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_UnBData_eq dVal] at hmem
          obtain ⟨cd, hd, rfl⟩ := symValListToCekList_singleton hargs
          have hpath := checked2_active_error hmem hactive
          rcases hpath with hinner | hproj
          · rcases hinner with ⟨inner, hinner, hpData, hinnerActive⟩
            change inner ∈
              (let is := SExpr.isCtor "DB" (asData dVal).val
               [Outcome.ok is
                  (SymVal.const (SymConst.bytes
                    (.app "dataBytes" [(asData dVal).val]))),
                Outcome.error (SExpr.not is)]) at hinner
            simp only [List.mem_cons, List.not_mem_nil] at hinner
            rcases hinner with hok | herr
            · subst inner
              simp [outcomeErrorActive] at hinnerActive
            · rcases herr with herr | hfalse
              · subst inner
                by_cases hshape : ∃ bs, cd = .VCon (.Data (.B bs))
                · rcases hshape with ⟨bs, rfl⟩
                  obtain ⟨d, hdCd, hdEval⟩ := asData_sound hd hpData
                  injection hdCd with hdEq
                  injection hdEq with hdDataEq
                  subst d
                  have his := pcHolds_isDB_intro (m := m)
                    (e := (asData dVal).val) (bs := bs) hdEval
                  exact False.elim (pcHolds_not_contra his hinnerActive)
                · exact evalBuiltin_UnBData_none_of_single_not_b (cv := cd) (by
                    intro bs h
                    exact hshape ⟨bs, h⟩)
              · cases hfalse
          · by_cases hshape : ∃ bs, cd = .VCon (.Data (.B bs))
            · rcases hshape with ⟨bs, rfl⟩
              have hg := asData_guard_of_cek (m := m) (v := dVal)
                (d := .B bs) hd
              exact False.elim (pcHolds_not_contra hg hproj)
            · exact evalBuiltin_UnBData_none_of_single_not_b (cv := cd) (by
                intro bs h
                exact hshape ⟨bs, h⟩)
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_UnBData_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_EqualsData :
    BuiltinErrorSound .EqualsData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_EqualsData_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_EqualsData_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_EqualsData_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asData aSym).guard (asData bSym).guard)
                  (SymVal.const (SymConst.bool
                    (SExpr.eq (asData aSym).val (asData bSym).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asData aSym).guard (asData bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ db da, cb = .VCon (.Data db) ∧ ca = .VCon (.Data da)
                  · rcases hshape with ⟨db, da, rfl, rfl⟩
                    have hga := asData_guard_of_cek (m := m) (v := aSym) (d := da) ha
                    have hgb := asData_guard_of_cek (m := m) (v := bSym) (d := db) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asData aSym).guard (asData bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asData aSym).guard (asData bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_EqualsData_none_of_pair_not_data (by
                      intro db da h
                      exact hshape ⟨db, da, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_EqualsData_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_MkPairData :
    BuiltinErrorSound .MkPairData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_MkPairData_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons bSym rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_MkPairData_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons aSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_MkPairData_eq bSym aSym] at hmem
              change out ∈
                [Outcome.ok (SExpr.and (asData aSym).guard (asData bSym).guard)
                  (SymVal.const (SymConst.pairData (asData aSym).val (asData bSym).val)),
                 Outcome.error (SExpr.not
                  (SExpr.and (asData aSym).guard (asData bSym).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hok | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hshape :
                      ∃ db da, cb = .VCon (.Data db) ∧ ca = .VCon (.Data da)
                  · rcases hshape with ⟨db, da, rfl, rfl⟩
                    have hga := asData_guard_of_cek (m := m) (v := aSym) (d := da) ha
                    have hgb := asData_guard_of_cek (m := m) (v := bSym) (d := db) hb
                    have hg :
                        pcHolds m
                          (SExpr.and (asData aSym).guard (asData bSym).guard) = true := by
                      simpa [pcHolds] using
                        ((Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asData aSym).guard (asData bSym).guard).mpr
                            ⟨by simpa [pcHolds] using hga,
                             by simpa [pcHolds] using hgb⟩)
                    exact False.elim (pcHolds_not_contra hg hactive)
                  · exact evalBuiltin_MkPairData_none_of_pair_not_data (by
                      intro db da h
                      exact hshape ⟨db, da, h.1, h.2⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_MkPairData_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_MkNilData :
    BuiltinErrorSound .MkNilData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_MkNilData_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons u rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_MkNilData_eq u] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cu, hu, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              by_cases hunit : cu = .VCon .Unit
              · subst cu
                have hg := unitGuard_complete (m := m) (u := u) hu
                exact False.elim (pcHolds_not_contra hg hactive)
              · exact evalBuiltin_MkNilData_none_of_single_not_unit hunit
            · cases hfalse
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_MkNilData_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_MkNilPairData :
    BuiltinErrorSound .MkNilPairData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_MkNilPairData_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons u rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_MkNilPairData_eq u] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cu, hu, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              by_cases hunit : cu = .VCon .Unit
              · subst cu
                have hg := unitGuard_complete (m := m) (u := u) hu
                exact False.elim (pcHolds_not_contra hg hactive)
              · exact evalBuiltin_MkNilPairData_none_of_single_not_unit hunit
            · cases hfalse
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_MkNilPairData_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_SerializeData :
    BuiltinErrorSound .SerializeData := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_SerializeData_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons dSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_SerializeData_eq dSym] at hmem
          change out ∈
            [Outcome.ok (asData dSym).guard
              (SymVal.const (SymConst.bytes
                (.app "uplc_serializeData" [(asData dSym).val]))),
             Outcome.error (SExpr.not (asData dSym).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cd, hd, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              by_cases hshape : ∃ d, cd = .VCon (.Data d)
              · rcases hshape with ⟨d, rfl⟩
                have hg := asData_guard_of_cek (m := m) (v := dSym) (d := d) hd
                exact False.elim (pcHolds_not_contra hg hactive)
              · exact evalBuiltin_SerializeData_none_of_single_not_data (by
                  intro d h
                  exact hshape ⟨d, h⟩)
            · cases hfalse
      | cons extra rest2 =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_SerializeData_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
axiom evalBuiltinSym_active_error_VerifyEcdsaSecp256k1Signature : BuiltinErrorSound .VerifyEcdsaSecp256k1Signature
axiom evalBuiltinSym_active_error_VerifySchnorrSecp256k1Signature : BuiltinErrorSound .VerifySchnorrSecp256k1Signature
axiom evalBuiltinSym_active_error_Bls12_381_G1_add : BuiltinErrorSound .Bls12_381_G1_add
axiom evalBuiltinSym_active_error_Bls12_381_G1_neg : BuiltinErrorSound .Bls12_381_G1_neg
axiom evalBuiltinSym_active_error_Bls12_381_G1_scalarMul : BuiltinErrorSound .Bls12_381_G1_scalarMul
axiom evalBuiltinSym_active_error_Bls12_381_G1_equal : BuiltinErrorSound .Bls12_381_G1_equal
axiom evalBuiltinSym_active_error_Bls12_381_G1_hashToGroup : BuiltinErrorSound .Bls12_381_G1_hashToGroup
axiom evalBuiltinSym_active_error_Bls12_381_G1_compress : BuiltinErrorSound .Bls12_381_G1_compress
axiom evalBuiltinSym_active_error_Bls12_381_G1_uncompress : BuiltinErrorSound .Bls12_381_G1_uncompress
axiom evalBuiltinSym_active_error_Bls12_381_G2_add : BuiltinErrorSound .Bls12_381_G2_add
axiom evalBuiltinSym_active_error_Bls12_381_G2_neg : BuiltinErrorSound .Bls12_381_G2_neg
axiom evalBuiltinSym_active_error_Bls12_381_G2_scalarMul : BuiltinErrorSound .Bls12_381_G2_scalarMul
axiom evalBuiltinSym_active_error_Bls12_381_G2_equal : BuiltinErrorSound .Bls12_381_G2_equal
axiom evalBuiltinSym_active_error_Bls12_381_G2_hashToGroup : BuiltinErrorSound .Bls12_381_G2_hashToGroup
axiom evalBuiltinSym_active_error_Bls12_381_G2_compress : BuiltinErrorSound .Bls12_381_G2_compress
axiom evalBuiltinSym_active_error_Bls12_381_G2_uncompress : BuiltinErrorSound .Bls12_381_G2_uncompress
axiom evalBuiltinSym_active_error_Bls12_381_millerLoop : BuiltinErrorSound .Bls12_381_millerLoop
axiom evalBuiltinSym_active_error_Bls12_381_mulMlResult : BuiltinErrorSound .Bls12_381_mulMlResult
axiom evalBuiltinSym_active_error_Bls12_381_finalVerify : BuiltinErrorSound .Bls12_381_finalVerify
axiom evalBuiltinSym_active_error_Keccak_256 : BuiltinErrorSound .Keccak_256
axiom evalBuiltinSym_active_error_Blake2b_224 : BuiltinErrorSound .Blake2b_224
axiom evalBuiltinSym_active_error_IntegerToByteString : BuiltinErrorSound .IntegerToByteString
axiom evalBuiltinSym_active_error_ByteStringToInteger : BuiltinErrorSound .ByteStringToInteger
axiom evalBuiltinSym_active_error_AndByteString : BuiltinErrorSound .AndByteString
axiom evalBuiltinSym_active_error_OrByteString : BuiltinErrorSound .OrByteString
axiom evalBuiltinSym_active_error_XorByteString : BuiltinErrorSound .XorByteString
axiom evalBuiltinSym_active_error_ComplementByteString : BuiltinErrorSound .ComplementByteString
axiom evalBuiltinSym_active_error_ReadBit : BuiltinErrorSound .ReadBit
axiom evalBuiltinSym_active_error_WriteBits : BuiltinErrorSound .WriteBits
axiom evalBuiltinSym_active_error_ReplicateByte : BuiltinErrorSound .ReplicateByte
axiom evalBuiltinSym_active_error_ShiftByteString : BuiltinErrorSound .ShiftByteString
axiom evalBuiltinSym_active_error_RotateByteString : BuiltinErrorSound .RotateByteString
axiom evalBuiltinSym_active_error_CountSetBits : BuiltinErrorSound .CountSetBits
axiom evalBuiltinSym_active_error_FindFirstSetBit : BuiltinErrorSound .FindFirstSetBit
axiom evalBuiltinSym_active_error_Ripemd_160 : BuiltinErrorSound .Ripemd_160
axiom evalBuiltinSym_active_error_ExpModInteger : BuiltinErrorSound .ExpModInteger
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_DropList : BuiltinErrorSound .DropList := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_DropList_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons xs rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_DropList_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons n rest2 =>
          cases rest2 with
          | nil =>
              change out ∈
                (let vl := Proj.map2 (fun n xs => .app "vlist_drop" [n, xs])
                    (asInt n) (asConstList xs)
                 let dl := Proj.map2 (fun n xs => .app "dlist_drop" [n, xs])
                    (asInt n) (asDataList xs)
                 [Outcome.ok vl.guard (.const (.constList vl.val)),
                  Outcome.ok dl.guard (.const (.dataList dl.val)),
                  Outcome.error (SExpr.not (SExpr.or vl.guard dl.guard))]) at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cxs, cn, hxs, hn, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hokVl | hokDl | herr
              · subst out
                simp [outcomeErrorActive] at hactive
              · subst out
                simp [outcomeErrorActive] at hactive
              · rcases herr with herr | hfalse
                · subst out
                  by_cases hlist :
                      ∃ cs i, cxs = .VCon (.ConstList cs) ∧ cn = .VCon (.Integer i)
                  · rcases hlist with ⟨cs, i, rfl, rfl⟩
                    have hgInt := asInt_guard_of_cek (m := m) (v := n) (i := i) hn
                    have hgList := asConstList_guard_of_cek (m := m) (v := xs) (cs := cs) hxs
                    have hvl : pcHolds m
                        (SExpr.and (asInt n).guard (asConstList xs).guard) = true :=
                      pcHolds_all2_intro (m := m) hgInt hgList
                    exact False.elim
                      (pcHolds_not_or_contra_left (m := m)
                        (a := SExpr.and (asInt n).guard (asConstList xs).guard)
                        (b := SExpr.and (asInt n).guard (asDataList xs).guard)
                        hvl hactive)
                  · by_cases hdata :
                      ∃ ds i, cxs = .VCon (.ConstDataList ds) ∧ cn = .VCon (.Integer i)
                    · rcases hdata with ⟨ds, i, rfl, rfl⟩
                      have hgInt := asInt_guard_of_cek (m := m) (v := n) (i := i) hn
                      have hgData :=
                        asDataList_guard_of_cek (m := m) (v := xs) (xs := ds) hxs
                      have hdl : pcHolds m
                          (SExpr.and (asInt n).guard (asDataList xs).guard) = true :=
                        pcHolds_all2_intro (m := m) hgInt hgData
                      exact False.elim
                        (pcHolds_not_or_contra_right (m := m)
                          (a := SExpr.and (asInt n).guard (asConstList xs).guard)
                          (b := SExpr.and (asInt n).guard (asDataList xs).guard)
                          hdl hactive)
                    · exact evalBuiltin_DropList_none_of_pair_not_supported
                        (a := cxs) (b := cn)
                        (by
                          intro cs i h
                          exact hlist ⟨cs, i, h⟩)
                        (by
                          intro ds i h
                          exact hdata ⟨ds, i, h⟩)
                · cases hfalse
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_DropList_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_IndexArray : BuiltinErrorSound .IndexArray := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_IndexArray_none_of_length_ne_two (by
        intro h2
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons idx rest =>
      cases rest with
      | nil =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_IndexArray_none_of_length_ne_two (by
            intro h2
            have hone : cargs.length = 1 := by simpa using hlen
            omega)
      | cons arr rest2 =>
          cases rest2 with
          | nil =>
              change out ∈
                checked2
                  (Proj.map2 (fun arr idx => (arr, idx)) (asArray arr) (asInt idx))
                  (fun (arr, idx) =>
                    let g := SExpr.and (SExpr.ge idx (.int 0))
                      (SExpr.lt idx (.app "vlist_length" [arr]))
                    [Outcome.ok g (.dyn (.app "vlist_index" [idx, arr])),
                     Outcome.error (SExpr.not g)]) at hmem
              obtain ⟨cidx, carr, hidxArg, harrArg, rfl⟩ :=
                symValListToCekList_pair hargs
              have hpath := checked2_active_error hmem hactive
              rcases hpath with hinner | hproj
              · rcases hinner with ⟨inner, hinner, hpArgs, hinnerActive⟩
                change inner ∈
                  (let g := SExpr.and (SExpr.ge (asInt idx).val (.int 0))
                    (SExpr.lt (asInt idx).val
                      (.app "vlist_length" [(asArray arr).val]))
                   [Outcome.ok g (.dyn (.app "vlist_index" [(asInt idx).val,
                     (asArray arr).val])),
                    Outcome.error (SExpr.not g)]) at hinner
                simp only [List.mem_cons, List.not_mem_nil] at hinner
                rcases hinner with hok | herr
                · subst inner
                  simp [outcomeErrorActive] at hinnerActive
                · rcases herr with herr | hfalse
                  · subst inner
                    have hnotRange :
                        pcHolds m
                          (SExpr.not
                            (SExpr.and (SExpr.ge (asInt idx).val (.int 0))
                              (SExpr.lt (asInt idx).val
                                (.app "vlist_length" [(asArray arr).val])))) = true := by
                      simpa [outcomeErrorActive] using hinnerActive
                    change pcHolds m
                      (SExpr.and (asArray arr).guard (asInt idx).guard) = true at hpArgs
                    have hp :=
                      (Moist.SMT.Semantics.evalBoolIs_and_true m
                        (asArray arr).guard (asInt idx).guard).mp hpArgs
                    obtain ⟨i, rfl, hiEval⟩ := asInt_sound hidxArg hp.2
                    obtain ⟨vals, cs, rfl, harrEval, hconsts⟩ :=
                      asArray_sound harrArg hp.1
                    by_cases hneg : i < 0
                    · exact evalBuiltin_IndexArray_none_of_negative (cs := cs) hneg
                    · have hge : 0 ≤ i := (Int.not_lt).mp hneg
                      by_cases hsome : ∃ c, cs[i.toNat]? = some c
                      · rcases hsome with ⟨c, hgetCs⟩
                        have hidxNatLtCs : i.toNat < cs.length := by
                          rcases (List.getElem?_eq_some_iff.mp hgetCs) with ⟨h, _hval⟩
                          exact h
                        have hlenNat : vals.length = cs.length :=
                          semValListToConstList_length hconsts
                        have hidxNatLtVals : i.toNat < vals.length := by
                          rwa [hlenNat]
                        have hlt : i < Int.ofNat vals.length :=
                          (Int.toNat_lt hge).mp hidxNatLtVals
                        have hlenEval := Moist.SMT.Semantics.eval_vlist_length_of
                          (m := m) (e := (asArray arr).val) harrEval
                        have hgePc : pcHolds m
                            (SExpr.ge (asInt idx).val (.int 0)) = true :=
                          pcHolds_ge_int_intro hiEval
                            (by simp [Moist.SMT.Semantics.eval]) hge
                        have hltPc : pcHolds m
                            (SExpr.lt (asInt idx).val
                              (.app "vlist_length" [(asArray arr).val])) = true :=
                          pcHolds_lt_int_intro hiEval hlenEval hlt
                        have hrange : pcHolds m
                            (SExpr.and (SExpr.ge (asInt idx).val (.int 0))
                              (SExpr.lt (asInt idx).val
                                (.app "vlist_length" [(asArray arr).val]))) = true :=
                          pcHolds_and_intro hgePc hltPc
                        exact False.elim (pcHolds_not_contra hrange hnotRange)
                      · have hgetNone : cs[i.toNat]? = none := by
                          cases hget : cs[i.toNat]? with
                          | none => rfl
                          | some c => exact False.elim (hsome ⟨c, hget⟩)
                        exact evalBuiltin_IndexArray_none_of_nonnegative_get_none
                          (cs := cs) hge hgetNone
                  · cases hfalse
              · by_cases hshape :
                  ∃ i cs, cidx = .VCon (.Integer i) ∧ carr = .VCon (.ConstArray cs)
                · rcases hshape with ⟨i, cs, rfl, rfl⟩
                  have hgArr := asArray_guard_of_cek (m := m) (v := arr) (cs := cs) harrArg
                  have hgIdx := asInt_guard_of_cek (m := m) (v := idx) (i := i) hidxArg
                  have hprojGuard : pcHolds m
                      (SExpr.and (asArray arr).guard (asInt idx).guard) = true :=
                    pcHolds_and_intro hgArr hgIdx
                  exact False.elim (pcHolds_not_contra hprojGuard hproj)
                · exact evalBuiltin_IndexArray_none_of_pair_not_supported
                    (a := cidx) (b := carr)
                    (by
                      intro i cs h
                      exact hshape ⟨i, cs, h⟩)
          | cons extra rest3 =>
              have hlen := symValListToCekList_length hargs
              exact evalBuiltin_IndexArray_none_of_length_ne_two (by
                intro h2
                have hthree : 3 ≤ cargs.length := by
                  rw [hlen]
                  simp
                omega)
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_LengthOfArray :
    BuiltinErrorSound .LengthOfArray := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_LengthOfArray_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons arr rest =>
      cases rest with
      | nil =>
          change out ∈
            [Outcome.ok (asArray arr).guard
              (SymVal.const (SymConst.integer
                (.app "vlist_length" [(asArray arr).val]))),
             Outcome.error (SExpr.not (asArray arr).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨carr, harr, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              by_cases hshape : ∃ cs, carr = .VCon (.ConstArray cs)
              · rcases hshape with ⟨cs, rfl⟩
                have hg := asArray_guard_of_cek harr
                exact False.elim (pcHolds_not_contra hg hactive)
              · exact evalBuiltin_LengthOfArray_none_of_single_not_array (by
                  intro cs h
                  exact hshape ⟨cs, h⟩)
            · cases hfalse
      | cons a rest =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_LengthOfArray_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_error_ListToArray :
    BuiltinErrorSound .ListToArray := by
  intro m args cargs out hargs hmem hactive
  cases args with
  | nil =>
      have hlen := symValListToCekList_length hargs
      exact evalBuiltin_ListToArray_none_of_length_ne_one (by
        intro h1
        have hzero : cargs.length = 0 := by simpa using hlen
        omega)
  | cons xs rest =>
      cases rest with
      | nil =>
          change out ∈
            [Outcome.ok (asConstList xs).guard
              (SymVal.const (SymConst.array (asConstList xs).val)),
             Outcome.error (SExpr.not (asConstList xs).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cxs, hxs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · subst out
            simp [outcomeErrorActive] at hactive
          · rcases herr with herr | hfalse
            · subst out
              by_cases hshape : ∃ cs, cxs = .VCon (.ConstList cs)
              · rcases hshape with ⟨cs, rfl⟩
                have hg := asConstList_guard_of_cek hxs
                exact False.elim (pcHolds_not_contra hg hactive)
              · exact evalBuiltin_ListToArray_none_of_single_not_list (by
                  intro cs h
                  exact hshape ⟨cs, h⟩)
            · cases hfalse
      | cons a rest =>
          have hlen := symValListToCekList_length hargs
          exact evalBuiltin_ListToArray_none_of_length_ne_one (by
            intro h1
            have htwo : 2 ≤ cargs.length := by
              rw [hlen]
              simp
            omega)
axiom evalBuiltinSym_active_error_InsertCoin : BuiltinErrorSound .InsertCoin
axiom evalBuiltinSym_active_error_LookupCoin : BuiltinErrorSound .LookupCoin
axiom evalBuiltinSym_active_error_ScaleValue : BuiltinErrorSound .ScaleValue
axiom evalBuiltinSym_active_error_UnionValue : BuiltinErrorSound .UnionValue
axiom evalBuiltinSym_active_error_ValueContains : BuiltinErrorSound .ValueContains
axiom evalBuiltinSym_active_error_ValueData : BuiltinErrorSound .ValueData
axiom evalBuiltinSym_active_error_UnValueData : BuiltinErrorSound .UnValueData
axiom evalBuiltinSym_active_error_Bls12_381_G1_multiScalarMul : BuiltinErrorSound .Bls12_381_G1_multiScalarMul
axiom evalBuiltinSym_active_error_Bls12_381_G2_multiScalarMul : BuiltinErrorSound .Bls12_381_G2_multiScalarMul

def builtinOkSound : (b : BuiltinFun) → BuiltinOkSound b
  | .AddInteger => evalBuiltinSym_active_ok_AddInteger
  | .SubtractInteger => evalBuiltinSym_active_ok_SubtractInteger
  | .MultiplyInteger => evalBuiltinSym_active_ok_MultiplyInteger
  | .DivideInteger => evalBuiltinSym_active_ok_DivideInteger
  | .QuotientInteger => evalBuiltinSym_active_ok_QuotientInteger
  | .RemainderInteger => evalBuiltinSym_active_ok_RemainderInteger
  | .ModInteger => evalBuiltinSym_active_ok_ModInteger
  | .EqualsInteger => evalBuiltinSym_active_ok_EqualsInteger
  | .LessThanInteger => evalBuiltinSym_active_ok_LessThanInteger
  | .LessThanEqualsInteger => evalBuiltinSym_active_ok_LessThanEqualsInteger
  | .AppendByteString => evalBuiltinSym_active_ok_AppendByteString
  | .ConsByteString => evalBuiltinSym_active_ok_ConsByteString
  | .SliceByteString => evalBuiltinSym_active_ok_SliceByteString
  | .LengthOfByteString => evalBuiltinSym_active_ok_LengthOfByteString
  | .IndexByteString => evalBuiltinSym_active_ok_IndexByteString
  | .EqualsByteString => evalBuiltinSym_active_ok_EqualsByteString
  | .LessThanByteString => evalBuiltinSym_active_ok_LessThanByteString
  | .LessThanEqualsByteString => evalBuiltinSym_active_ok_LessThanEqualsByteString
  | .Sha2_256 => evalBuiltinSym_active_ok_Sha2_256
  | .Sha3_256 => evalBuiltinSym_active_ok_Sha3_256
  | .Blake2b_256 => evalBuiltinSym_active_ok_Blake2b_256
  | .VerifyEd25519Signature => evalBuiltinSym_active_ok_VerifyEd25519Signature
  | .AppendString => evalBuiltinSym_active_ok_AppendString
  | .EqualsString => evalBuiltinSym_active_ok_EqualsString
  | .EncodeUtf8 => evalBuiltinSym_active_ok_EncodeUtf8
  | .DecodeUtf8 => evalBuiltinSym_active_ok_DecodeUtf8
  | .IfThenElse => evalBuiltinSym_active_ok_IfThenElse
  | .ChooseUnit => evalBuiltinSym_active_ok_ChooseUnit
  | .Trace => evalBuiltinSym_active_ok_Trace
  | .FstPair => evalBuiltinSym_active_ok_FstPair
  | .SndPair => evalBuiltinSym_active_ok_SndPair
  | .ChooseList => evalBuiltinSym_active_ok_ChooseList
  | .MkCons => evalBuiltinSym_active_ok_MkCons
  | .HeadList => evalBuiltinSym_active_ok_HeadList
  | .TailList => evalBuiltinSym_active_ok_TailList
  | .NullList => evalBuiltinSym_active_ok_NullList
  | .ChooseData => evalBuiltinSym_active_ok_ChooseData
  | .ConstrData => evalBuiltinSym_active_ok_ConstrData
  | .MapData => evalBuiltinSym_active_ok_MapData
  | .ListData => evalBuiltinSym_active_ok_ListData
  | .IData => evalBuiltinSym_active_ok_IData
  | .BData => evalBuiltinSym_active_ok_BData
  | .UnConstrData => evalBuiltinSym_active_ok_UnConstrData
  | .UnMapData => evalBuiltinSym_active_ok_UnMapData
  | .UnListData => evalBuiltinSym_active_ok_UnListData
  | .UnIData => evalBuiltinSym_active_ok_UnIData
  | .UnBData => evalBuiltinSym_active_ok_UnBData
  | .EqualsData => evalBuiltinSym_active_ok_EqualsData
  | .MkPairData => evalBuiltinSym_active_ok_MkPairData
  | .MkNilData => evalBuiltinSym_active_ok_MkNilData
  | .MkNilPairData => evalBuiltinSym_active_ok_MkNilPairData
  | .SerializeData => evalBuiltinSym_active_ok_SerializeData
  | .VerifyEcdsaSecp256k1Signature => evalBuiltinSym_active_ok_VerifyEcdsaSecp256k1Signature
  | .VerifySchnorrSecp256k1Signature => evalBuiltinSym_active_ok_VerifySchnorrSecp256k1Signature
  | .Bls12_381_G1_add => evalBuiltinSym_active_ok_Bls12_381_G1_add
  | .Bls12_381_G1_neg => evalBuiltinSym_active_ok_Bls12_381_G1_neg
  | .Bls12_381_G1_scalarMul => evalBuiltinSym_active_ok_Bls12_381_G1_scalarMul
  | .Bls12_381_G1_equal => evalBuiltinSym_active_ok_Bls12_381_G1_equal
  | .Bls12_381_G1_hashToGroup => evalBuiltinSym_active_ok_Bls12_381_G1_hashToGroup
  | .Bls12_381_G1_compress => evalBuiltinSym_active_ok_Bls12_381_G1_compress
  | .Bls12_381_G1_uncompress => evalBuiltinSym_active_ok_Bls12_381_G1_uncompress
  | .Bls12_381_G2_add => evalBuiltinSym_active_ok_Bls12_381_G2_add
  | .Bls12_381_G2_neg => evalBuiltinSym_active_ok_Bls12_381_G2_neg
  | .Bls12_381_G2_scalarMul => evalBuiltinSym_active_ok_Bls12_381_G2_scalarMul
  | .Bls12_381_G2_equal => evalBuiltinSym_active_ok_Bls12_381_G2_equal
  | .Bls12_381_G2_hashToGroup => evalBuiltinSym_active_ok_Bls12_381_G2_hashToGroup
  | .Bls12_381_G2_compress => evalBuiltinSym_active_ok_Bls12_381_G2_compress
  | .Bls12_381_G2_uncompress => evalBuiltinSym_active_ok_Bls12_381_G2_uncompress
  | .Bls12_381_millerLoop => evalBuiltinSym_active_ok_Bls12_381_millerLoop
  | .Bls12_381_mulMlResult => evalBuiltinSym_active_ok_Bls12_381_mulMlResult
  | .Bls12_381_finalVerify => evalBuiltinSym_active_ok_Bls12_381_finalVerify
  | .Keccak_256 => evalBuiltinSym_active_ok_Keccak_256
  | .Blake2b_224 => evalBuiltinSym_active_ok_Blake2b_224
  | .IntegerToByteString => evalBuiltinSym_active_ok_IntegerToByteString
  | .ByteStringToInteger => evalBuiltinSym_active_ok_ByteStringToInteger
  | .AndByteString => evalBuiltinSym_active_ok_AndByteString
  | .OrByteString => evalBuiltinSym_active_ok_OrByteString
  | .XorByteString => evalBuiltinSym_active_ok_XorByteString
  | .ComplementByteString => evalBuiltinSym_active_ok_ComplementByteString
  | .ReadBit => evalBuiltinSym_active_ok_ReadBit
  | .WriteBits => evalBuiltinSym_active_ok_WriteBits
  | .ReplicateByte => evalBuiltinSym_active_ok_ReplicateByte
  | .ShiftByteString => evalBuiltinSym_active_ok_ShiftByteString
  | .RotateByteString => evalBuiltinSym_active_ok_RotateByteString
  | .CountSetBits => evalBuiltinSym_active_ok_CountSetBits
  | .FindFirstSetBit => evalBuiltinSym_active_ok_FindFirstSetBit
  | .Ripemd_160 => evalBuiltinSym_active_ok_Ripemd_160
  | .ExpModInteger => evalBuiltinSym_active_ok_ExpModInteger
  | .DropList => evalBuiltinSym_active_ok_DropList
  | .IndexArray => evalBuiltinSym_active_ok_IndexArray
  | .LengthOfArray => evalBuiltinSym_active_ok_LengthOfArray
  | .ListToArray => evalBuiltinSym_active_ok_ListToArray
  | .InsertCoin => evalBuiltinSym_active_ok_InsertCoin
  | .LookupCoin => evalBuiltinSym_active_ok_LookupCoin
  | .ScaleValue => evalBuiltinSym_active_ok_ScaleValue
  | .UnionValue => evalBuiltinSym_active_ok_UnionValue
  | .ValueContains => evalBuiltinSym_active_ok_ValueContains
  | .ValueData => evalBuiltinSym_active_ok_ValueData
  | .UnValueData => evalBuiltinSym_active_ok_UnValueData
  | .Bls12_381_G1_multiScalarMul => evalBuiltinSym_active_ok_Bls12_381_G1_multiScalarMul
  | .Bls12_381_G2_multiScalarMul => evalBuiltinSym_active_ok_Bls12_381_G2_multiScalarMul

def builtinErrorSound : (b : BuiltinFun) → BuiltinErrorSound b
  | .AddInteger => evalBuiltinSym_active_error_AddInteger
  | .SubtractInteger => evalBuiltinSym_active_error_SubtractInteger
  | .MultiplyInteger => evalBuiltinSym_active_error_MultiplyInteger
  | .DivideInteger => evalBuiltinSym_active_error_DivideInteger
  | .QuotientInteger => evalBuiltinSym_active_error_QuotientInteger
  | .RemainderInteger => evalBuiltinSym_active_error_RemainderInteger
  | .ModInteger => evalBuiltinSym_active_error_ModInteger
  | .EqualsInteger => evalBuiltinSym_active_error_EqualsInteger
  | .LessThanInteger => evalBuiltinSym_active_error_LessThanInteger
  | .LessThanEqualsInteger => evalBuiltinSym_active_error_LessThanEqualsInteger
  | .AppendByteString => evalBuiltinSym_active_error_AppendByteString
  | .ConsByteString => evalBuiltinSym_active_error_ConsByteString
  | .SliceByteString => evalBuiltinSym_active_error_SliceByteString
  | .LengthOfByteString => evalBuiltinSym_active_error_LengthOfByteString
  | .IndexByteString => evalBuiltinSym_active_error_IndexByteString
  | .EqualsByteString => evalBuiltinSym_active_error_EqualsByteString
  | .LessThanByteString => evalBuiltinSym_active_error_LessThanByteString
  | .LessThanEqualsByteString => evalBuiltinSym_active_error_LessThanEqualsByteString
  | .Sha2_256 => evalBuiltinSym_active_error_Sha2_256
  | .Sha3_256 => evalBuiltinSym_active_error_Sha3_256
  | .Blake2b_256 => evalBuiltinSym_active_error_Blake2b_256
  | .VerifyEd25519Signature => evalBuiltinSym_active_error_VerifyEd25519Signature
  | .AppendString => evalBuiltinSym_active_error_AppendString
  | .EqualsString => evalBuiltinSym_active_error_EqualsString
  | .EncodeUtf8 => evalBuiltinSym_active_error_EncodeUtf8
  | .DecodeUtf8 => evalBuiltinSym_active_error_DecodeUtf8
  | .IfThenElse => evalBuiltinSym_active_error_IfThenElse
  | .ChooseUnit => evalBuiltinSym_active_error_ChooseUnit
  | .Trace => evalBuiltinSym_active_error_Trace
  | .FstPair => evalBuiltinSym_active_error_FstPair
  | .SndPair => evalBuiltinSym_active_error_SndPair
  | .ChooseList => evalBuiltinSym_active_error_ChooseList
  | .MkCons => evalBuiltinSym_active_error_MkCons
  | .HeadList => evalBuiltinSym_active_error_HeadList
  | .TailList => evalBuiltinSym_active_error_TailList
  | .NullList => evalBuiltinSym_active_error_NullList
  | .ChooseData => evalBuiltinSym_active_error_ChooseData
  | .ConstrData => evalBuiltinSym_active_error_ConstrData
  | .MapData => evalBuiltinSym_active_error_MapData
  | .ListData => evalBuiltinSym_active_error_ListData
  | .IData => evalBuiltinSym_active_error_IData
  | .BData => evalBuiltinSym_active_error_BData
  | .UnConstrData => evalBuiltinSym_active_error_UnConstrData
  | .UnMapData => evalBuiltinSym_active_error_UnMapData
  | .UnListData => evalBuiltinSym_active_error_UnListData
  | .UnIData => evalBuiltinSym_active_error_UnIData
  | .UnBData => evalBuiltinSym_active_error_UnBData
  | .EqualsData => evalBuiltinSym_active_error_EqualsData
  | .MkPairData => evalBuiltinSym_active_error_MkPairData
  | .MkNilData => evalBuiltinSym_active_error_MkNilData
  | .MkNilPairData => evalBuiltinSym_active_error_MkNilPairData
  | .SerializeData => evalBuiltinSym_active_error_SerializeData
  | .VerifyEcdsaSecp256k1Signature => evalBuiltinSym_active_error_VerifyEcdsaSecp256k1Signature
  | .VerifySchnorrSecp256k1Signature => evalBuiltinSym_active_error_VerifySchnorrSecp256k1Signature
  | .Bls12_381_G1_add => evalBuiltinSym_active_error_Bls12_381_G1_add
  | .Bls12_381_G1_neg => evalBuiltinSym_active_error_Bls12_381_G1_neg
  | .Bls12_381_G1_scalarMul => evalBuiltinSym_active_error_Bls12_381_G1_scalarMul
  | .Bls12_381_G1_equal => evalBuiltinSym_active_error_Bls12_381_G1_equal
  | .Bls12_381_G1_hashToGroup => evalBuiltinSym_active_error_Bls12_381_G1_hashToGroup
  | .Bls12_381_G1_compress => evalBuiltinSym_active_error_Bls12_381_G1_compress
  | .Bls12_381_G1_uncompress => evalBuiltinSym_active_error_Bls12_381_G1_uncompress
  | .Bls12_381_G2_add => evalBuiltinSym_active_error_Bls12_381_G2_add
  | .Bls12_381_G2_neg => evalBuiltinSym_active_error_Bls12_381_G2_neg
  | .Bls12_381_G2_scalarMul => evalBuiltinSym_active_error_Bls12_381_G2_scalarMul
  | .Bls12_381_G2_equal => evalBuiltinSym_active_error_Bls12_381_G2_equal
  | .Bls12_381_G2_hashToGroup => evalBuiltinSym_active_error_Bls12_381_G2_hashToGroup
  | .Bls12_381_G2_compress => evalBuiltinSym_active_error_Bls12_381_G2_compress
  | .Bls12_381_G2_uncompress => evalBuiltinSym_active_error_Bls12_381_G2_uncompress
  | .Bls12_381_millerLoop => evalBuiltinSym_active_error_Bls12_381_millerLoop
  | .Bls12_381_mulMlResult => evalBuiltinSym_active_error_Bls12_381_mulMlResult
  | .Bls12_381_finalVerify => evalBuiltinSym_active_error_Bls12_381_finalVerify
  | .Keccak_256 => evalBuiltinSym_active_error_Keccak_256
  | .Blake2b_224 => evalBuiltinSym_active_error_Blake2b_224
  | .IntegerToByteString => evalBuiltinSym_active_error_IntegerToByteString
  | .ByteStringToInteger => evalBuiltinSym_active_error_ByteStringToInteger
  | .AndByteString => evalBuiltinSym_active_error_AndByteString
  | .OrByteString => evalBuiltinSym_active_error_OrByteString
  | .XorByteString => evalBuiltinSym_active_error_XorByteString
  | .ComplementByteString => evalBuiltinSym_active_error_ComplementByteString
  | .ReadBit => evalBuiltinSym_active_error_ReadBit
  | .WriteBits => evalBuiltinSym_active_error_WriteBits
  | .ReplicateByte => evalBuiltinSym_active_error_ReplicateByte
  | .ShiftByteString => evalBuiltinSym_active_error_ShiftByteString
  | .RotateByteString => evalBuiltinSym_active_error_RotateByteString
  | .CountSetBits => evalBuiltinSym_active_error_CountSetBits
  | .FindFirstSetBit => evalBuiltinSym_active_error_FindFirstSetBit
  | .Ripemd_160 => evalBuiltinSym_active_error_Ripemd_160
  | .ExpModInteger => evalBuiltinSym_active_error_ExpModInteger
  | .DropList => evalBuiltinSym_active_error_DropList
  | .IndexArray => evalBuiltinSym_active_error_IndexArray
  | .LengthOfArray => evalBuiltinSym_active_error_LengthOfArray
  | .ListToArray => evalBuiltinSym_active_error_ListToArray
  | .InsertCoin => evalBuiltinSym_active_error_InsertCoin
  | .LookupCoin => evalBuiltinSym_active_error_LookupCoin
  | .ScaleValue => evalBuiltinSym_active_error_ScaleValue
  | .UnionValue => evalBuiltinSym_active_error_UnionValue
  | .ValueContains => evalBuiltinSym_active_error_ValueContains
  | .ValueData => evalBuiltinSym_active_error_ValueData
  | .UnValueData => evalBuiltinSym_active_error_UnValueData
  | .Bls12_381_G1_multiScalarMul => evalBuiltinSym_active_error_Bls12_381_G1_multiScalarMul
  | .Bls12_381_G2_multiScalarMul => evalBuiltinSym_active_error_Bls12_381_G2_multiScalarMul

theorem evalBuiltinSym_active_ok {m : SmtSem.Model} {b : BuiltinFun}
    {args : List SymVal} {cargs : List CekValue} {out : Outcome}
    {sv : SymVal} {cv : CekValue}
    (hargs : symValListToCekList? m args = some cargs)
    (hnoArgs : symValsNoOpaqueForSoundness args = true)
    (hmem : out ∈ evalBuiltinSym b args)
    (hok : outcomeOkSym? m out = some (sv, cv)) :
    Moist.CEK.evalBuiltin b cargs = some cv := by
  cases out with
  | ok pc v =>
      have hok' := outcomeOkSym_ok hok
      have hpath := builtinOkSound b hargs hnoArgs hmem hok'.1
      rcases hpath with ⟨cv', hv', _hno, hb⟩
      rw [hok'.2.2] at hv'
      injection hv' with hcv
      subst cv'
      exact hb
  | error pc =>
      simp [outcomeOkSym?] at hok
  | timeout pc =>
      simp [outcomeOkSym?] at hok

theorem evalBuiltinSym_active_error {m : SmtSem.Model} {b : BuiltinFun}
    {args : List SymVal} {cargs : List CekValue} {out : Outcome}
    (hargs : symValListToCekList? m args = some cargs)
    (hmem : out ∈ evalBuiltinSym b args)
    (herr : outcomeErrorActive m out = true) :
    Moist.CEK.evalBuiltin b cargs = none := by
  exact builtinErrorSound b hargs hmem herr

def caseCekResult (fuel : Nat) (env : CekEnv)
    (scrut : CekValue) (alts : List Term) : Option CekValue :=
  match scrut with
  | .VConstr tag fields =>
      match alts[tag]? with
      | some alt =>
          match bigEval fuel env alt with
          | some vAlt => applyValList fuel vAlt fields
          | none => none
      | none => none
  | .VCon c =>
      match Moist.CEK.constToTagAndFields c with
      | some (tag, numCtors, fields) =>
          if numCtors > 0 && alts.length > numCtors then none
          else
            match alts[tag]? with
            | some alt =>
                match bigEval fuel env alt with
                | some vAlt => applyValList fuel vAlt fields
                | none => none
            | none => none
      | none => none
  | _ => none

set_option maxHeartbeats 0

mutual
  theorem evalSym_path_ok_noOpaque {m : SmtSem.Model} {fuel : Nat}
      {ρ : List SymVal} {env : CekEnv} {t : Term} {pc : SExpr} {v : SymVal}
      (henv : symEnvToCek? m ρ = some env)
      (hρno : symEnvNoOpaqueForSoundness ρ = true)
      (hno : termNoOpaqueBuiltinsForSoundness t)
      (hmem : Outcome.ok pc v ∈ evalSym fuel ρ t)
      (hpc : pcHolds m pc = true) :
      ∃ cv, symValToCek? m v = some cv ∧
        symValNoOpaqueForSoundness v = true ∧
        bigEval fuel env t = some cv := by
    cases fuel with
    | zero =>
        simp [evalSym, timeout] at hmem
    | succ n =>
        cases t with
        | Var k =>
            cases hlookup : lookupEnv ρ k with
            | none =>
                simp [evalSym, hlookup, err] at hmem
            | some v0 =>
                simp [evalSym, hlookup, ok] at hmem
                rcases hmem with ⟨rfl, rfl⟩
                obtain ⟨cv, hv, hlookupCek⟩ :=
                  symEnv_lookup_some_exists henv hlookup
                have hnoV := symEnvNoOpaque_lookup hρno hlookup
                exact ⟨cv, hv, hnoV, by simp [bigEval, hlookupCek]⟩
        | Constant cb =>
            obtain ⟨c, ty⟩ := cb
            simp [evalSym, ok] at hmem
            rcases hmem with ⟨rfl, rfl⟩
            exact ⟨.VCon c, constLiteral_sound m c, constLiteral_noOpaque c,
              by simp [bigEval]⟩
        | Builtin b =>
            simp [evalSym, ok] at hmem
            rcases hmem with ⟨rfl, rfl⟩
            have hbAllowed : builtinAllowedForSoundness b = true := by
              simpa [termNoOpaqueBuiltinsForSoundness, termUsesOpaqueBuiltinForSoundness,
                builtinAllowedForSoundness] using hno
            exact ⟨.VBuiltin b [] (expectedArgs b),
              by simp [symValToCek?, symValListToCekList?],
              by simp [symValNoOpaqueForSoundness, hbAllowed, symValsNoOpaqueForSoundness],
              by simp [bigEval]⟩
        | Lam name body =>
            simp [evalSym, ok] at hmem
            rcases hmem with ⟨rfl, rfl⟩
            exact ⟨.VLam body env,
              by simp [symValToCek?, henv],
              by
                simp [symValNoOpaqueForSoundness, hρno]
                simpa [termNoOpaqueBuiltinsForSoundness, termUsesOpaqueBuiltinForSoundness]
                  using hno,
              by simp [bigEval]⟩
        | Delay body =>
            simp [evalSym, ok] at hmem
            rcases hmem with ⟨rfl, rfl⟩
            exact ⟨.VDelay body env,
              by simp [symValToCek?, henv],
              by
                simp [symValNoOpaqueForSoundness, hρno]
                simpa [termNoOpaqueBuiltinsForSoundness, termUsesOpaqueBuiltinForSoundness]
                  using hno,
              by simp [bigEval]⟩
        | Apply f a =>
            have hnoSplit := termNoOpaque_apply hno
            have hbind1 := bindOut_path_ok (m := m)
              (xs := evalSym n ρ f)
              (k := fun vf => bindOut (evalSym n ρ a) fun va => applySym n vf va)
              (hmem := by simpa [evalSym] using hmem) hpc
            rcases hbind1 with
              ⟨pcF, vf, pcRest, hmemF, hmemRest, hpcEq, hpcF, hpcRest⟩
            have hf := evalSym_path_ok_noOpaque (m := m) (fuel := n)
              (ρ := ρ) (env := env) (t := f)
              henv hρno hnoSplit.1 hmemF hpcF
            rcases hf with ⟨cvf, hvf, hnof, hbigF⟩
            have hbind2 := bindOut_path_ok (m := m)
              (xs := evalSym n ρ a) (k := fun va => applySym n vf va)
              hmemRest hpcRest
            rcases hbind2 with
              ⟨pcA, va, pcApp, hmemA, hmemApp, hpcEq2, hpcA, hpcApp⟩
            have ha := evalSym_path_ok_noOpaque (m := m) (fuel := n)
              (ρ := ρ) (env := env) (t := a)
              henv hρno hnoSplit.2 hmemA hpcA
            rcases ha with ⟨cva, hva, hnoa, hbigA⟩
            have happ := applySym_path_ok (m := m) (fuel := n)
              (vf := vf) (va := va) (cvf := cvf) (cva := cva)
              hvf hnof hva hnoa hmemApp hpcApp
            rcases happ with ⟨cv, hv, hnov, happVal⟩
            exact ⟨cv, hv, hnov,
              by simp [bigEval, hbigF, hbigA, happVal]⟩
        | Force body =>
            have hnoBody := termNoOpaque_force hno
            have hbind := bindOut_path_ok (m := m)
              (xs := evalSym n ρ body) (k := fun vt => forceSym n vt)
              (hmem := by simpa [evalSym] using hmem) hpc
            rcases hbind with
              ⟨pcT, vt, pcForce, hmemT, hmemForce, hpcEq, hpcT, hpcForce⟩
            have ht := evalSym_path_ok_noOpaque (m := m) (fuel := n)
              (ρ := ρ) (env := env) (t := body)
              henv hρno hnoBody hmemT hpcT
            rcases ht with ⟨cvt, hvt, hnot, hbigT⟩
            have hf := forceSym_path_ok (m := m) (fuel := n)
              (vt := vt) (cvt := cvt) hvt hnot hmemForce hpcForce
            rcases hf with ⟨cv, hv, hnov, hforceVal⟩
            exact ⟨cv, hv, hnov,
              by simp [bigEval, hbigT, hforceVal]⟩
        | Constr tag fields =>
            have hnoFields := termNoOpaque_constr_fields hno
            have hbind := bindOut_path_ok (m := m)
              (xs := evalListSym n ρ fields)
              (k := fun vals =>
                match vals with
                | .constr (.int (-1)) vs =>
                    ok (.constr (.int (Int.ofNat tag)) vs)
                | _ => err)
              (hmem := by simpa [evalSym] using hmem) hpc
            rcases hbind with
              ⟨pcFields, vals, pcConstr, hmemFields, hmemConstr,
                hpcEq, hpcFields, hpcConstr⟩
            have hfields := evalListSym_path_ok_noOpaque (m := m) (fuel := n)
              (ρ := ρ) (env := env) (ts := fields)
              henv hρno hnoFields hmemFields hpcFields
            rcases hfields with ⟨vs, cvs, hvals, hvs, hnoVs, hbigFields⟩
            subst vals
            have hfinal : Outcome.ok pcConstr v ∈
                ok (.constr (.int (Int.ofNat tag)) vs) := by
              simpa using hmemConstr
            obtain ⟨hpcFinal, hvFinal⟩ := ok_mem_singleton hfinal
            subst v
            exact ⟨.VConstr tag cvs,
              by
                simp [symValToCek?, hvs, Moist.SMT.Semantics.eval]
              ,
              by simp [symValNoOpaqueForSoundness, hnoVs],
              by simp [bigEval, hbigFields]⟩
        | Case scrut alts =>
            have hnoSplit := termNoOpaque_case hno
            have hbind := bindOut_path_ok (m := m)
              (xs := evalSym n ρ scrut)
              (k := fun v => caseSym n ρ v alts)
              (hmem := by simpa [evalSym] using hmem) hpc
            rcases hbind with
              ⟨pcScrut, vScrut, pcCase, hmemScrut, hmemCase,
                hpcEq, hpcScrut, hpcCase⟩
            have hscrut := evalSym_path_ok_noOpaque (m := m) (fuel := n)
              (ρ := ρ) (env := env) (t := scrut)
              henv hρno hnoSplit.1 hmemScrut hpcScrut
            rcases hscrut with ⟨cvScrut, hvScrut, hnoScrut, hbigScrut⟩
            have hcase := caseSym_path_ok_noOpaque (m := m) (fuel := n)
              (ρ := ρ) (env := env) (scrut := vScrut) (alts := alts)
              (cscrut := cvScrut)
              henv hρno hnoSplit.2 hvScrut hnoScrut hmemCase hpcCase
            rcases hcase with ⟨cv, hv, hnov, hcaseVal⟩
            exact ⟨cv, hv, hnov,
              by
                cases cvScrut <;>
                  simpa [bigEval, hbigScrut, Bool.and_eq_true] using hcaseVal⟩
        | Error =>
            simp [evalSym, err] at hmem

  theorem evalListSym_path_ok_noOpaque {m : SmtSem.Model} {fuel : Nat}
      {ρ : List SymVal} {env : CekEnv} {ts : List Term} {pc : SExpr} {v : SymVal}
      (henv : symEnvToCek? m ρ = some env)
      (hρno : symEnvNoOpaqueForSoundness ρ = true)
      (hno : termsUseOpaqueBuiltinForSoundness ts = false)
      (hmem : Outcome.ok pc v ∈ evalListSym fuel ρ ts)
      (hpc : pcHolds m pc = true) :
      ∃ vs cvs,
        v = .constr (.int (-1)) vs ∧
        symValListToCekList? m vs = some cvs ∧
        symValsNoOpaqueForSoundness vs = true ∧
        bigEvalList fuel env ts = some cvs := by
    cases ts with
    | nil =>
        simp [evalListSym, ok] at hmem
        rcases hmem with ⟨rfl, rfl⟩
        exact ⟨[], [], rfl, by simp [symValListToCekList?],
          by simp [symValsNoOpaqueForSoundness], by simp [bigEvalList]⟩
    | cons t ts =>
        have hnoSplit := termsNoOpaque_cons hno
        have hbind1 := bindOut_path_ok (m := m)
          (xs := evalSym fuel ρ t)
          (k := fun v => bindOut (evalListSym fuel ρ ts) fun rest =>
            match rest with
            | .constr (.int (-1)) vs => ok (.constr (.int (-1)) (v :: vs))
            | _ => err)
          (hmem := by simpa [evalListSym] using hmem) hpc
        rcases hbind1 with
          ⟨pcHead, vHead, pcTail, hmemHead, hmemTail, hpcEq, hpcHead, hpcTail⟩
        have hhead := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
          (ρ := ρ) (env := env) (t := t)
          henv hρno hnoSplit.1 hmemHead hpcHead
        rcases hhead with ⟨cvHead, hvHead, hnoHead, hbigHead⟩
        have hbind2 := bindOut_path_ok (m := m)
          (xs := evalListSym fuel ρ ts)
          (k := fun rest =>
            match rest with
            | .constr (.int (-1)) vs => ok (.constr (.int (-1)) (vHead :: vs))
            | _ => err)
          hmemTail hpcTail
        rcases hbind2 with
          ⟨pcRest, vRest, pcFinal, hmemRest, hmemFinal, hpcEq2, hpcRest, hpcFinal⟩
        have hrest := evalListSym_path_ok_noOpaque (m := m) (fuel := fuel)
          (ρ := ρ) (env := env) (ts := ts)
          henv hρno hnoSplit.2 hmemRest hpcRest
        rcases hrest with ⟨vs, cvs, hvRest, hvs, hnoVs, hbigRest⟩
        subst vRest
        have hfinal : Outcome.ok pcFinal v ∈
            ok (.constr (.int (-1)) (vHead :: vs)) := by
          simpa using hmemFinal
        obtain ⟨hpcFinalTrue, hvFinal⟩ := ok_mem_singleton hfinal
        subst v
        exact ⟨vHead :: vs, cvHead :: cvs, rfl,
          symValListToCekList_cons hvHead hvs,
          symValNoOpaqueList_cons hnoHead hnoVs,
          by simp [bigEvalList, hbigHead, hbigRest]⟩

  theorem applySym_path_ok {m : SmtSem.Model} {fuel : Nat}
      {vf va : SymVal} {cvf cva : CekValue} {pc : SExpr} {v : SymVal}
      (hvf : symValToCek? m vf = some cvf)
      (hnof : symValNoOpaqueForSoundness vf = true)
      (hva : symValToCek? m va = some cva)
      (hnoa : symValNoOpaqueForSoundness va = true)
      (hmem : Outcome.ok pc v ∈ applySym fuel vf va)
      (hpc : pcHolds m pc = true) :
      ∃ cv, symValToCek? m v = some cv ∧
        symValNoOpaqueForSoundness v = true ∧
        applyVal fuel cvf cva = some cv := by
    cases fuel with
    | zero =>
        simp [applySym, timeout] at hmem
    | succ n =>
        cases vf with
        | lam body ρ =>
            cases henv0 : symEnvToCek? m ρ <;>
              simp [symValToCek?, henv0] at hvf
            rename_i env0
            subst cvf
            have hsplit : termUsesOpaqueBuiltinForSoundness body = false ∧
                symEnvNoOpaqueForSoundness ρ = true := by
              simpa [symValNoOpaqueForSoundness] using hnof
            have henvExt := symEnvToCek_extend (m := m) (ρ := ρ)
              (env := env0) (v := va) (cv := cva) henv0 hva
            have hnoExt := symEnvNoOpaque_extend (ρ := ρ) (v := va)
              hsplit.2 hnoa
            have hbody := evalSym_path_ok_noOpaque (m := m) (fuel := n)
              (ρ := extendEnv ρ va) (env := env0.extend cva) (t := body)
              henvExt hnoExt (by
                simpa [termNoOpaqueBuiltinsForSoundness] using hsplit.1)
              (by simpa [applySym] using hmem) hpc
            rcases hbody with ⟨cv, hv, hnov, hbig⟩
            exact ⟨cv, hv, hnov, by simp [applyVal, hbig]⟩
        | builtin b args ea =>
            cases hargs : symValListToCekList? m args <;>
              simp [symValToCek?, hargs] at hvf
            rename_i cargs
            subst cvf
            have hnoParts : builtinAllowedForSoundness b = true ∧
                symValsNoOpaqueForSoundness args = true := by
              simpa [symValNoOpaqueForSoundness] using hnof
            cases hea : ea.head <;> simp [applySym, hea] at hmem
            · cases htail : ea.tail with
              | some rest =>
                  simp [htail, ok] at hmem
                  rcases hmem with ⟨rfl, rfl⟩
                  have hargs' := symValListToCekList_cons (m := m)
                    (v := va) (vs := args) (cv := cva) (cvs := cargs) hva hargs
                  have hnoArgs' := symValNoOpaqueList_cons
                    (v := va) (vs := args) hnoa hnoParts.2
                  exact ⟨.VBuiltin b (cva :: cargs) rest,
                    by simp [symValToCek?, hargs'],
                    by simp [symValNoOpaqueForSoundness, hnoParts.1, hnoArgs'],
                    by simp [applyVal, hea, htail]⟩
              | none =>
                  have hargs' := symValListToCekList_cons (m := m)
                    (v := va) (vs := args) (cv := cva) (cvs := cargs) hva hargs
                  have hnoArgs' := symValNoOpaqueList_cons
                    (v := va) (vs := args) hnoa hnoParts.2
                  have hmemBuiltin : Outcome.ok pc v ∈ evalBuiltinSym b (va :: args) := by
                    simpa [applySym, hea, htail] using hmem
                  have hb := builtinOkSound b hargs' hnoArgs' hmemBuiltin hpc
                  rcases hb with ⟨cv, hv, hnov, hb⟩
                  exact ⟨cv, hv, hnov,
                    by simpa [applyVal, hea, htail] using hb⟩
            · simp [applySym, hea, err] at hmem
        | const c =>
            simp [applySym, err] at hmem
        | dyn e =>
            simp [applySym, err] at hmem
        | pair a b =>
            simp [applySym, err] at hmem
        | constr tag fields =>
            simp [applySym, err] at hmem
        | delay body ρ =>
            simp [applySym, err] at hmem

  theorem forceSym_path_ok {m : SmtSem.Model} {fuel : Nat}
      {vt : SymVal} {cvt : CekValue} {pc : SExpr} {v : SymVal}
      (hvt : symValToCek? m vt = some cvt)
      (hnot : symValNoOpaqueForSoundness vt = true)
      (hmem : Outcome.ok pc v ∈ forceSym fuel vt)
      (hpc : pcHolds m pc = true) :
      ∃ cv, symValToCek? m v = some cv ∧
        symValNoOpaqueForSoundness v = true ∧
        forceVal fuel cvt = some cv := by
    cases fuel with
    | zero =>
        simp [forceSym, timeout] at hmem
    | succ n =>
        cases vt with
        | delay body ρ =>
            cases henv0 : symEnvToCek? m ρ <;>
              simp [symValToCek?, henv0] at hvt
            rename_i env0
            subst cvt
            have hsplit : termUsesOpaqueBuiltinForSoundness body = false ∧
                symEnvNoOpaqueForSoundness ρ = true := by
              simpa [symValNoOpaqueForSoundness] using hnot
            have hbody := evalSym_path_ok_noOpaque (m := m) (fuel := n)
              (ρ := ρ) (env := env0) (t := body)
              henv0 hsplit.2 (by
                simpa [termNoOpaqueBuiltinsForSoundness] using hsplit.1)
              (by simpa [forceSym] using hmem) hpc
            rcases hbody with ⟨cv, hv, hnov, hbig⟩
            exact ⟨cv, hv, hnov, by simp [forceVal, hbig]⟩
        | builtin b args ea =>
            cases hargs : symValListToCekList? m args <;>
              simp [symValToCek?, hargs] at hvt
            rename_i cargs
            subst cvt
            have hnoParts : builtinAllowedForSoundness b = true ∧
                symValsNoOpaqueForSoundness args = true := by
              simpa [symValNoOpaqueForSoundness] using hnot
            cases hea : ea.head <;> simp [forceSym, hea] at hmem
            · simp [err] at hmem
            · cases htail : ea.tail with
              | some rest =>
                  simp [htail, ok] at hmem
                  rcases hmem with ⟨rfl, rfl⟩
                  exact ⟨.VBuiltin b cargs rest,
                    by simp [symValToCek?, hargs],
                    by simp [symValNoOpaqueForSoundness, hnoParts.1, hnoParts.2],
                    by simp [forceVal, hea, htail]⟩
              | none =>
                  have hmemBuiltin : Outcome.ok pc v ∈ evalBuiltinSym b args := by
                    simpa [forceSym, hea, htail] using hmem
                  have hb := builtinOkSound b hargs hnoParts.2 hmemBuiltin hpc
                  rcases hb with ⟨cv, hv, hnov, hb⟩
                  exact ⟨cv, hv, hnov,
                    by simpa [forceVal, hea, htail] using hb⟩
        | const c =>
            simp [forceSym, err] at hmem
        | dyn e =>
            simp [forceSym, err] at hmem
        | pair a b =>
            simp [forceSym, err] at hmem
        | constr tag fields =>
            simp [forceSym, err] at hmem
        | lam body ρ =>
            simp [forceSym, err] at hmem

  theorem applyListSym_path_ok {m : SmtSem.Model} {fuel : Nat}
      {vf : SymVal} {args : List SymVal} {cvf : CekValue} {cargs : List CekValue}
      {pc : SExpr} {v : SymVal}
      (hvf : symValToCek? m vf = some cvf)
      (hnof : symValNoOpaqueForSoundness vf = true)
      (hargs : symValListToCekList? m args = some cargs)
      (hnoArgs : symValsNoOpaqueForSoundness args = true)
      (hmem : Outcome.ok pc v ∈ applyListSym fuel vf args)
      (hpc : pcHolds m pc = true) :
      ∃ cv, symValToCek? m v = some cv ∧
        symValNoOpaqueForSoundness v = true ∧
        applyValList fuel cvf cargs = some cv := by
    cases args with
    | nil =>
        simp [symValListToCekList?] at hargs
        subst cargs
        simp [applyListSym, ok] at hmem
        rcases hmem with ⟨rfl, rfl⟩
        exact ⟨cvf, hvf, hnof, by simp [applyValList]⟩
    | cons a as =>
        cases ha : symValToCek? m a <;>
          simp [symValListToCekList?, ha] at hargs
        rename_i ca
        cases has : symValListToCekList? m as <;> simp [has] at hargs
        rename_i cas
        subst cargs
        have hnoSplit : symValNoOpaqueForSoundness a = true ∧
            symValsNoOpaqueForSoundness as = true := by
          simpa [symValsNoOpaqueForSoundness] using hnoArgs
        have hbind := bindOut_path_ok (m := m)
          (xs := applySym fuel vf a)
          (k := fun vf' => applyListSym fuel vf' as)
          (hmem := by simpa [applyListSym] using hmem) hpc
        rcases hbind with
          ⟨outerPc, vf', innerPc, houter, hinner, hpcEq, houterPc, hinnerPc⟩
        have happ := applySym_path_ok (m := m) (fuel := fuel)
          (vf := vf) (va := a) (cvf := cvf) (cva := ca)
          hvf hnof ha hnoSplit.1 houter houterPc
        rcases happ with ⟨cvf', hvf', hnof', happVal⟩
        have hrec := applyListSym_path_ok (m := m) (fuel := fuel)
          (vf := vf') (args := as) (cvf := cvf') (cargs := cas)
          hvf' hnof' has hnoSplit.2 hinner hinnerPc
        rcases hrec with ⟨cv, hv, hnov, hlist⟩
        exact ⟨cv, hv, hnov, by simp [applyValList, happVal, hlist]⟩

  theorem applyValListSym_path_ok {m : SmtSem.Model} {fuel : Nat}
      {vf : SymVal} {fieldsExpr : SExpr} {fields : List SmtSem.Val}
      {cvf : CekValue} {cfields : List CekValue} {pc : SExpr} {v : SymVal}
      (hvf : symValToCek? m vf = some cvf)
      (hnof : symValNoOpaqueForSoundness vf = true)
      (hfieldsEval : SmtSem.eval m fieldsExpr = some (.valList fields))
      (hfields : semValListToCekList? fields = some cfields)
      (hmem : Outcome.ok pc v ∈ applyValListSym fuel vf fieldsExpr)
      (hpc : pcHolds m pc = true) :
      ∃ cv, symValToCek? m v = some cv ∧
        symValNoOpaqueForSoundness v = true ∧
        applyValList fuel cvf cfields = some cv := by
    cases fuel with
    | zero =>
        simp [applyValListSym, timeout] at hmem
    | succ n =>
        cases fields with
        | nil =>
            simp [semValListToCekList?] at hfields
            subst cfields
            have hbranch := branchOutcomes_path_ok (m := m)
              (hmem := by simpa [applyValListSym] using hmem) hpc
            rcases hbranch with ⟨g, os, innerPc, hbr, hinner, hpcEq, hg, hi⟩
            simp at hbr
            rcases hbr with hnil | hcons
            · rcases hnil with ⟨rfl, rfl⟩
              simp [ok] at hinner
              rcases hinner with ⟨rfl, rfl⟩
              exact ⟨cvf, hvf, hnof, by simp [applyValList]⟩
            · rcases hcons with ⟨rfl, rfl⟩
              have htrue :=
                Moist.SMT.Semantics.evalBoolIs_isVNil_true_of_valList_nil hfieldsEval
              have hfalse := (Moist.SMT.Semantics.evalBoolIs_not_true m
                (SExpr.isCtor "VNil" fieldsExpr)).mp hg
              exact False.elim (evalBoolIs_true_false_contra htrue hfalse)
        | cons field fieldsTail =>
            cases hfield : semValToCek? field <;>
              simp [semValListToCekList?, hfield] at hfields
            rename_i cfield
            cases htail : semValListToCekList? fieldsTail <;> simp [htail] at hfields
            rename_i ctail
            subst cfields
            have hbranch := branchOutcomes_path_ok (m := m)
              (hmem := by simpa [applyValListSym] using hmem) hpc
            rcases hbranch with ⟨g, os, innerPc, hbr, hinner, hpcEq, hg, hi⟩
            simp at hbr
            rcases hbr with hnil | hcons
            · rcases hnil with ⟨rfl, rfl⟩
              have hfalse :=
                Moist.SMT.Semantics.evalBoolIs_isVNil_false_of_valList_cons hfieldsEval
              exact False.elim (evalBoolIs_true_false_contra hg hfalse)
            · rcases hcons with ⟨rfl, rfl⟩
              have hheadEval :=
                Moist.SMT.Semantics.eval_vhead_of (m := m) (e := fieldsExpr)
                  (h := field) (t := fieldsTail) hfieldsEval
              have htailEval :=
                Moist.SMT.Semantics.eval_vtail_of (m := m) (e := fieldsExpr)
                  (h := field) (t := fieldsTail) hfieldsEval
              have hheadDecode :
                  symValToCek? m (.dyn (.app "vhead" [fieldsExpr])) = some cfield := by
                simp [symValToCek?, hheadEval, hfield]
              have hbind := bindOut_path_ok (m := m)
                (xs := applySym n vf (.dyn (.app "vhead" [fieldsExpr])))
                (k := fun vf' => applyValListSym n vf' (.app "vtail" [fieldsExpr]))
                hinner hi
              rcases hbind with
                ⟨pcApply, vf', pcRest, hmemApply, hmemRest,
                  hpcEq2, hpcApply, hpcRest⟩
              have happ := applySym_path_ok (m := m) (fuel := n)
                (vf := vf) (va := .dyn (.app "vhead" [fieldsExpr]))
                (cvf := cvf) (cva := cfield)
                hvf hnof hheadDecode (by simp [symValNoOpaqueForSoundness])
                hmemApply hpcApply
              rcases happ with ⟨cvf', hvf', hnof', happVal⟩
              have hrec := applyValListSym_path_ok (m := m) (fuel := n)
                (vf := vf') (fieldsExpr := .app "vtail" [fieldsExpr])
                (fields := fieldsTail) (cvf := cvf') (cfields := ctail)
                hvf' hnof' htailEval htail hmemRest hpcRest
              rcases hrec with ⟨cv, hv, hnov, hlist⟩
              have happVal' := applyVal_mono happVal
              have hlist' := applyValList_mono hlist
              exact ⟨cv, hv, hnov, by simp [applyValList, happVal', hlist']⟩

  theorem caseSym_path_ok_noOpaque {m : SmtSem.Model} {fuel : Nat}
      {ρ : List SymVal} {env : CekEnv} {scrut : SymVal} {alts : List Term}
      {cscrut : CekValue} {pc : SExpr} {v : SymVal}
      (henv : symEnvToCek? m ρ = some env)
      (hρno : symEnvNoOpaqueForSoundness ρ = true)
      (hnoAlts : termsUseOpaqueBuiltinForSoundness alts = false)
      (hscrut : symValToCek? m scrut = some cscrut)
      (hnoScrut : symValNoOpaqueForSoundness scrut = true)
      (hmem : Outcome.ok pc v ∈ caseSym fuel ρ scrut alts)
      (hpc : pcHolds m pc = true) :
      ∃ cv, symValToCek? m v = some cv ∧
        symValNoOpaqueForSoundness v = true ∧
        (match cscrut with
        | .VConstr tag fields =>
            match alts[tag]? with
            | some alt =>
                match bigEval fuel env alt with
                | some vAlt => applyValList fuel vAlt fields
                | none => none
            | none => none
        | .VCon c =>
            match Moist.CEK.constToTagAndFields c with
            | some (tag, numCtors, fields) =>
                if numCtors > 0 && alts.length > numCtors then none
                else match alts[tag]? with
                     | some alt =>
                         match bigEval fuel env alt with
                         | some vAlt => applyValList fuel vAlt fields
                         | none => none
                     | none => none
            | none => none
        | _ => none) = some cv := by
    cases scrut with
    | constr tag fields =>
        cases htagEval : SmtSem.eval m tag with
        | none => simp [symValToCek?, htagEval] at hscrut
        | some tagSv =>
          cases tagSv with
          | int tagInt =>
            by_cases hneg : tagInt < 0
            · simp [symValToCek?, htagEval, hneg] at hscrut
            · cases hfields : symValListToCekList? m fields with
              | none => simp [symValToCek?, htagEval, hneg, hfields] at hscrut
              | some cfields =>
                simp [symValToCek?, htagEval, hneg, hfields] at hscrut
                subst cscrut
                have hnoFields : symValsNoOpaqueForSoundness fields = true := by
                  simpa [symValNoOpaqueForSoundness] using hnoScrut
                have hbranch := branchOutcomes_path_ok (m := m)
                  (hmem := by simpa [caseSym] using hmem) hpc
                rcases hbranch with ⟨g, os, innerPc, hbr, hinner, hpcEq, hg, hi⟩
                simp only [List.mem_map] at hbr
                rcases hbr with ⟨br, henum, hbrEq⟩
                rcases br with ⟨i, alt⟩
                simp at hbrEq
                rcases hbrEq with ⟨rfl, rfl⟩
                have hget : alts[i]? = some alt := enumerate_mem_get? henum
                have htagEq : tagInt = Int.ofNat i :=
                  pcHolds_eq_int htagEval (by simp [Moist.SMT.Semantics.eval]) hg
                have hnoAlt := termsNoOpaque_get? hnoAlts hget
                have hbind := bindOut_path_ok (m := m)
                  (xs := evalSym fuel ρ alt)
                  (k := fun vAlt => applyListSym fuel vAlt fields)
                  hinner hi
                rcases hbind with
                  ⟨pcAlt, vAlt, pcApply, hmemAlt, hmemApply,
                    hpcEq2, hpcAlt, hpcApply⟩
                have halt := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
                  (ρ := ρ) (env := env) (t := alt)
                  henv hρno hnoAlt hmemAlt hpcAlt
                rcases halt with ⟨cvAlt, hvAlt, hnoVAlt, hbigAlt⟩
                have happ := applyListSym_path_ok (m := m) (fuel := fuel)
                  (vf := vAlt) (args := fields) (cvf := cvAlt) (cargs := cfields)
                  hvAlt hnoVAlt hfields hnoFields hmemApply hpcApply
                rcases happ with ⟨cv, hv, hnov, happVal⟩
                refine ⟨cv, hv, hnov, ?_⟩
                subst tagInt
                simp [hget, hbigAlt, happVal]
          | bool b => simp [symValToCek?, htagEval] at hscrut
          | string s => simp [symValToCek?, htagEval] at hscrut
          | bytes bs => simp [symValToCek?, htagEval] at hscrut
          | data d => simp [symValToCek?, htagEval] at hscrut
          | dataList xs => simp [symValToCek?, htagEval] at hscrut
          | dataPairList xs => simp [symValToCek?, htagEval] at hscrut
          | val val => simp [symValToCek?, htagEval] at hscrut
          | valList xs => simp [symValToCek?, htagEval] at hscrut
          | g1 g => simp [symValToCek?, htagEval] at hscrut
          | g2 g => simp [symValToCek?, htagEval] at hscrut
          | ml r => simp [symValToCek?, htagEval] at hscrut
    | const c =>
        cases c with
        | bool be =>
            cases he : SmtSem.eval m be with
            | none => simp [symValToCek?, symConstToCek?, he] at hscrut
            | some sv =>
              cases sv with
              | bool bval =>
                simp [symValToCek?, symConstToCek?, he] at hscrut
                subst cscrut
                by_cases hlen : alts.length > 2
                · simp [caseSym, hlen, err] at hmem
                · have hbranch := branchOutcomes_path_ok (m := m)
                    (hmem := by simpa [caseSym, hlen] using hmem) hpc
                  rcases hbranch with
                    ⟨g, os, innerPc, hbr, hinner, hpcEq, hg, hi⟩
                  simp only [List.mem_map] at hbr
                  rcases hbr with ⟨br, henum, hbrEq⟩
                  rcases br with ⟨i, alt⟩
                  simp at hbrEq
                  rcases hbrEq with ⟨rfl, rfl⟩
                  have hget : alts[i]? = some alt := enumerate_mem_get? henum
                  have htagEval :
                      SmtSem.eval m (SExpr.ite be (.int 1) (.int 0)) =
                        some (.int (if bval then 1 else 0)) := by
                    change SmtSem.eval m (Expr.ite be (.int 1) (.int 0)) =
                      some (.int (if bval then 1 else 0))
                    rw [eval_ite_of_bool (m := m) (c := be)
                      (t := .int 1) (e := .int 0) he]
                    cases bval <;> simp [Moist.SMT.Semantics.eval]
                  have htagEq :
                      (if bval then (1 : Int) else 0) = Int.ofNat i :=
                    pcHolds_eq_int htagEval
                      (by simp [Moist.SMT.Semantics.eval]) hg
                  have hnoAlt := termsNoOpaque_get? hnoAlts hget
                  have halt := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
                    (ρ := ρ) (env := env) (t := alt)
                    henv hρno hnoAlt hinner hi
                  rcases halt with ⟨cv, hv, hnov, hbig⟩
                  refine ⟨cv, hv, hnov, ?_⟩
                  cases bval
                  · have hi0 : i = 0 := intOfNat_eq_zero htagEq
                    subst i
                    simp [Moist.CEK.constToTagAndFields, hlen, hget, hbig,
                      applyValList]
                  · have hi1 : i = 1 := intOfNat_eq_one htagEq
                    subst i
                    simp [Moist.CEK.constToTagAndFields, hlen, hget, hbig,
                      applyValList]
              | int i => simp [symValToCek?, symConstToCek?, he] at hscrut
              | string s => simp [symValToCek?, symConstToCek?, he] at hscrut
              | bytes bs => simp [symValToCek?, symConstToCek?, he] at hscrut
              | data d => simp [symValToCek?, symConstToCek?, he] at hscrut
              | dataList xs => simp [symValToCek?, symConstToCek?, he] at hscrut
              | dataPairList xs => simp [symValToCek?, symConstToCek?, he] at hscrut
              | val val => simp [symValToCek?, symConstToCek?, he] at hscrut
              | valList xs => simp [symValToCek?, symConstToCek?, he] at hscrut
              | g1 g => simp [symValToCek?, symConstToCek?, he] at hscrut
              | g2 g => simp [symValToCek?, symConstToCek?, he] at hscrut
              | ml r => simp [symValToCek?, symConstToCek?, he] at hscrut
        | unit =>
            simp [symValToCek?, symConstToCek?] at hscrut
            subst cscrut
            by_cases hlen : alts.length > 1
            · simp [caseSym, hlen, err] at hmem
            · cases hget : alts[0]? with
              | none => simp [caseSym, hlen, hget, err] at hmem
              | some alt =>
                have hnoAlt := termsNoOpaque_get? hnoAlts hget
                have halt := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
                  (ρ := ρ) (env := env) (t := alt)
                  henv hρno hnoAlt (by simpa [caseSym, hlen, hget] using hmem) hpc
                rcases halt with ⟨cv, hv, hnov, hbig⟩
                exact ⟨cv, hv, hnov,
                  by simp [Moist.CEK.constToTagAndFields, hlen, hget, hbig,
                    applyValList]⟩
        | integer ie =>
            cases he : SmtSem.eval m ie with
            | none => simp [symValToCek?, symConstToCek?, he] at hscrut
            | some sv =>
              cases sv with
              | int ival =>
                simp [symValToCek?, symConstToCek?, he] at hscrut
                subst cscrut
                have hbranch := branchOutcomes_path_ok (m := m)
                  (hmem := by simpa [caseSym] using hmem) hpc
                rcases hbranch with
                  ⟨g, os, innerPc, hbr, hinner, hpcEq, hg, hi⟩
                simp only [List.mem_map] at hbr
                rcases hbr with ⟨br, henum, hbrEq⟩
                rcases br with ⟨i, alt⟩
                simp at hbrEq
                rcases hbrEq with ⟨rfl, rfl⟩
                have hparts :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (nonnegGuard ie) (SExpr.eq ie (.int (Int.ofNat i)))).mp hg
                have hnonneg : 0 ≤ ival := pcHolds_nonneg he hparts.1
                have htagEq : ival = Int.ofNat i :=
                  pcHolds_eq_int he (by simp [Moist.SMT.Semantics.eval]) hparts.2
                have hget : alts[i]? = some alt := enumerate_mem_get? henum
                have hnoAlt := termsNoOpaque_get? hnoAlts hget
                have halt := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
                  (ρ := ρ) (env := env) (t := alt)
                  henv hρno hnoAlt hinner hi
                rcases halt with ⟨cv, hv, hnov, hbig⟩
                refine ⟨cv, hv, hnov, ?_⟩
                subst ival
                simp [Moist.CEK.constToTagAndFields, hget, hbig, applyValList]
              | bool b => simp [symValToCek?, symConstToCek?, he] at hscrut
              | string s => simp [symValToCek?, symConstToCek?, he] at hscrut
              | bytes bs => simp [symValToCek?, symConstToCek?, he] at hscrut
              | data d => simp [symValToCek?, symConstToCek?, he] at hscrut
              | dataList xs => simp [symValToCek?, symConstToCek?, he] at hscrut
              | dataPairList xs => simp [symValToCek?, symConstToCek?, he] at hscrut
              | val val => simp [symValToCek?, symConstToCek?, he] at hscrut
              | valList xs => simp [symValToCek?, symConstToCek?, he] at hscrut
              | g1 g => simp [symValToCek?, symConstToCek?, he] at hscrut
              | g2 g => simp [symValToCek?, symConstToCek?, he] at hscrut
              | ml r => simp [symValToCek?, symConstToCek?, he] at hscrut
        | constList xs =>
            cases hxs : SmtSem.eval m xs with
            | none => simp [symValToCek?, symConstToCek?, hxs] at hscrut
            | some sv =>
              cases sv with
              | valList vals =>
                cases hconsts : semValListToConstList? vals with
                | none => simp [symValToCek?, symConstToCek?, hxs, hconsts] at hscrut
                | some consts =>
                  simp [symValToCek?, symConstToCek?, hxs, hconsts] at hscrut
                  subst cscrut
                  by_cases hlen : alts.length > 2
                  · simp [caseSym, hlen, err] at hmem
                  · have hbranch := branchOutcomes_path_ok (m := m)
                      (hmem := by simpa [caseSym, hlen] using hmem) hpc
                    rcases hbranch with
                      ⟨g, os, innerPc, hbr, hinner, hpcEq, hg, hi⟩
                    cases vals with
                    | nil =>
                      simp [semValListToConstList?] at hconsts
                      subst consts
                      cases h0 : alts[0]? with
                      | none =>
                        cases h1 : alts[1]? with
                        | none =>
                          simp [caseSym, hlen, h0, h1] at hmem
                          simp [branchOutcomes] at hmem
                        | some nilAlt =>
                          simp [caseSym, hlen, h0, h1] at hbr
                          rcases hbr with ⟨rfl, rfl⟩
                          have hnoAlt := termsNoOpaque_get? hnoAlts h1
                          have halt := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
                            (ρ := ρ) (env := env) (t := nilAlt)
                            henv hρno hnoAlt hinner hi
                          rcases halt with ⟨cv, hv, hnov, hbig⟩
                          have hle : alts.length ≤ 2 := by omega
                          exact ⟨cv, hv, hnov,
                            by
                              simp [Moist.CEK.constToTagAndFields, hle, h1, hbig,
                                applyValList]⟩
                      | some consAlt =>
                        cases h1 : alts[1]? with
                        | none =>
                          simp [caseSym, hlen, h0, h1] at hbr
                          rcases hbr with ⟨rfl, rfl⟩
                          have hnil :=
                            Moist.SMT.Semantics.evalBoolIs_isVNil_true_of_valList_nil hxs
                          have hnot :=
                            (Moist.SMT.Semantics.evalBoolIs_not_true m
                              (SExpr.isCtor "VNil" xs)).mp hg
                          exact False.elim (evalBoolIs_true_false_contra hnil hnot)
                        | some nilAlt =>
                          simp [caseSym, hlen, h0, h1] at hbr
                          rcases hbr with hcons | hnilBranch
                          · rcases hcons with ⟨rfl, rfl⟩
                            have hnil :=
                              Moist.SMT.Semantics.evalBoolIs_isVNil_true_of_valList_nil hxs
                            have hnot :=
                              (Moist.SMT.Semantics.evalBoolIs_not_true m
                                (SExpr.isCtor "VNil" xs)).mp hg
                            exact False.elim (evalBoolIs_true_false_contra hnil hnot)
                          · rcases hnilBranch with ⟨rfl, rfl⟩
                            have hnoAlt := termsNoOpaque_get? hnoAlts h1
                            have halt := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
                              (ρ := ρ) (env := env) (t := nilAlt)
                              henv hρno hnoAlt hinner hi
                            rcases halt with ⟨cv, hv, hnov, hbig⟩
                            have hle : alts.length ≤ 2 := by omega
                            exact ⟨cv, hv, hnov,
                              by
                                simp [Moist.CEK.constToTagAndFields, hle, h1, hbig,
                                  applyValList]⟩
                    | cons head tail =>
                      cases hheadConst : semValToConst? head with
                      | none => simp [semValListToConstList?, hheadConst] at hconsts
                      | some headConst =>
                        cases htailConst : semValListToConstList? tail with
                        | none =>
                          simp [semValListToConstList?, hheadConst, htailConst] at hconsts
                        | some tailConst =>
                          simp [semValListToConstList?, hheadConst, htailConst] at hconsts
                          subst consts
                          cases h0 : alts[0]? with
                          | none =>
                            cases h1 : alts[1]? with
                            | none =>
                              simp [caseSym, hlen, h0, h1] at hmem
                              simp [branchOutcomes] at hmem
                            | some nilAlt =>
                              simp [caseSym, hlen, h0, h1] at hbr
                              rcases hbr with ⟨rfl, rfl⟩
                              have hfalse :=
                                Moist.SMT.Semantics.evalBoolIs_isVNil_false_of_valList_cons hxs
                              exact False.elim (evalBoolIs_true_false_contra hg hfalse)
                          | some consAlt =>
                            cases h1 : alts[1]? with
                            | none =>
                              simp [caseSym, hlen, h0, h1] at hbr
                              rcases hbr with ⟨rfl, rfl⟩
                              have hbind := bindOut_path_ok (m := m)
                                (xs := evalSym fuel ρ consAlt)
                                (k := fun vAlt =>
                                  applyListSym fuel vAlt [fieldFromValList xs, tailFromValList xs])
                                hinner hi
                              rcases hbind with
                                ⟨pcAlt, vAlt, pcApply, hmemAlt, hmemApply,
                                  hpcEq2, hpcAlt, hpcApply⟩
                              have hnoAlt := termsNoOpaque_get? hnoAlts h0
                              have halt := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
                                (ρ := ρ) (env := env) (t := consAlt)
                                henv hρno hnoAlt hmemAlt hpcAlt
                              rcases halt with ⟨cvAlt, hvAlt, hnoVAlt, hbigAlt⟩
                              have hheadEval :=
                                Moist.SMT.Semantics.eval_vhead_of (m := m) (e := xs)
                                  (h := head) (t := tail) hxs
                              have htailEval :=
                                Moist.SMT.Semantics.eval_vtail_of (m := m) (e := xs)
                                  (h := head) (t := tail) hxs
                              have hargs :
                                  symValListToCekList? m
                                      [fieldFromValList xs, tailFromValList xs] =
                                    some [.VCon headConst, .VCon (.ConstList tailConst)] := by
                                have hheadCek := semValToCek_of_const hheadConst
                                simp [fieldFromValList, tailFromValList, symValListToCekList?,
                                  symValToCek?, symConstToCek?, hheadEval, htailEval,
                                  hheadCek, htailConst]
                              have hnoArgs :
                                  symValsNoOpaqueForSoundness
                                      [fieldFromValList xs, tailFromValList xs] = true := by
                                simp [fieldFromValList, tailFromValList,
                                  symValsNoOpaqueForSoundness, symValNoOpaqueForSoundness]
                              have happ := applyListSym_path_ok (m := m) (fuel := fuel)
                                (vf := vAlt)
                                (args := [fieldFromValList xs, tailFromValList xs])
                                (cvf := cvAlt)
                                (cargs := [.VCon headConst, .VCon (.ConstList tailConst)])
                                hvAlt hnoVAlt hargs hnoArgs hmemApply hpcApply
                              rcases happ with ⟨cv, hv, hnov, happVal⟩
                              have hle : alts.length ≤ 2 := by omega
                              exact ⟨cv, hv, hnov,
                                by
                                  simp [Moist.CEK.constToTagAndFields, hle, h0,
                                    hbigAlt, happVal]⟩
                            | some nilAlt =>
                              simp [caseSym, hlen, h0, h1] at hbr
                              rcases hbr with hcons | hnilBranch
                              · rcases hcons with ⟨rfl, rfl⟩
                                have hbind := bindOut_path_ok (m := m)
                                  (xs := evalSym fuel ρ consAlt)
                                  (k := fun vAlt =>
                                    applyListSym fuel vAlt [fieldFromValList xs, tailFromValList xs])
                                  hinner hi
                                rcases hbind with
                                  ⟨pcAlt, vAlt, pcApply, hmemAlt, hmemApply,
                                    hpcEq2, hpcAlt, hpcApply⟩
                                have hnoAlt := termsNoOpaque_get? hnoAlts h0
                                have halt := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
                                  (ρ := ρ) (env := env) (t := consAlt)
                                  henv hρno hnoAlt hmemAlt hpcAlt
                                rcases halt with ⟨cvAlt, hvAlt, hnoVAlt, hbigAlt⟩
                                have hheadEval :=
                                  Moist.SMT.Semantics.eval_vhead_of (m := m) (e := xs)
                                    (h := head) (t := tail) hxs
                                have htailEval :=
                                  Moist.SMT.Semantics.eval_vtail_of (m := m) (e := xs)
                                    (h := head) (t := tail) hxs
                                have hargs :
                                    symValListToCekList? m
                                        [fieldFromValList xs, tailFromValList xs] =
                                      some [.VCon headConst, .VCon (.ConstList tailConst)] := by
                                  have hheadCek := semValToCek_of_const hheadConst
                                  simp [fieldFromValList, tailFromValList, symValListToCekList?,
                                    symValToCek?, symConstToCek?, hheadEval, htailEval,
                                    hheadCek, htailConst]
                                have hnoArgs :
                                    symValsNoOpaqueForSoundness
                                        [fieldFromValList xs, tailFromValList xs] = true := by
                                  simp [fieldFromValList, tailFromValList,
                                    symValsNoOpaqueForSoundness, symValNoOpaqueForSoundness]
                                have happ := applyListSym_path_ok (m := m) (fuel := fuel)
                                  (vf := vAlt)
                                  (args := [fieldFromValList xs, tailFromValList xs])
                                  (cvf := cvAlt)
                                  (cargs := [.VCon headConst, .VCon (.ConstList tailConst)])
                                  hvAlt hnoVAlt hargs hnoArgs hmemApply hpcApply
                                rcases happ with ⟨cv, hv, hnov, happVal⟩
                                have hle : alts.length ≤ 2 := by omega
                                exact ⟨cv, hv, hnov,
                                  by
                                    simp [Moist.CEK.constToTagAndFields, hle, h0,
                                      hbigAlt, happVal]⟩
                              · rcases hnilBranch with ⟨rfl, rfl⟩
                                have hfalse :=
                                  Moist.SMT.Semantics.evalBoolIs_isVNil_false_of_valList_cons hxs
                                exact False.elim (evalBoolIs_true_false_contra hg hfalse)
              | bool b => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | int i => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | string s => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | bytes bs => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | data d => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | dataList xs' => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | dataPairList xs' => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | val val => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | g1 g => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | g2 g => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | ml r => simp [symValToCek?, symConstToCek?, hxs] at hscrut
        | dataList xs =>
            cases hxs : SmtSem.eval m xs with
            | none => simp [symValToCek?, symConstToCek?, hxs] at hscrut
            | some sv =>
              cases sv with
              | dataList vals =>
                simp [symValToCek?, symConstToCek?, hxs] at hscrut
                subst cscrut
                by_cases hlen : alts.length > 2
                · simp [caseSym, hlen, err] at hmem
                · have hbranch := branchOutcomes_path_ok (m := m)
                    (hmem := by simpa [caseSym, hlen] using hmem) hpc
                  rcases hbranch with
                    ⟨g, os, innerPc, hbr, hinner, hpcEq, hg, hi⟩
                  cases vals with
                  | nil =>
                    cases h0 : alts[0]? with
                    | none =>
                      cases h1 : alts[1]? with
                      | none =>
                        simp [caseSym, hlen, h0, h1] at hmem
                        simp [branchOutcomes] at hmem
                      | some nilAlt =>
                        simp [caseSym, hlen, h0, h1] at hbr
                        rcases hbr with ⟨rfl, rfl⟩
                        have hnoAlt := termsNoOpaque_get? hnoAlts h1
                        have halt := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
                          (ρ := ρ) (env := env) (t := nilAlt)
                          henv hρno hnoAlt hinner hi
                        rcases halt with ⟨cv, hv, hnov, hbig⟩
                        have hle : alts.length ≤ 2 := by omega
                        exact ⟨cv, hv, hnov,
                          by
                            simp [Moist.CEK.constToTagAndFields, hle, h1, hbig,
                              applyValList]⟩
                    | some consAlt =>
                      cases h1 : alts[1]? with
                      | none =>
                        simp [caseSym, hlen, h0, h1] at hbr
                        rcases hbr with ⟨rfl, rfl⟩
                        have hnil :=
                          Moist.SMT.Semantics.evalBoolIs_isDNil_true_of_dataList_nil hxs
                        have hnot :=
                          (Moist.SMT.Semantics.evalBoolIs_not_true m
                            (SExpr.isCtor "DNil" xs)).mp hg
                        exact False.elim (evalBoolIs_true_false_contra hnil hnot)
                      | some nilAlt =>
                        simp [caseSym, hlen, h0, h1] at hbr
                        rcases hbr with hcons | hnilBranch
                        · rcases hcons with ⟨rfl, rfl⟩
                          have hnil :=
                            Moist.SMT.Semantics.evalBoolIs_isDNil_true_of_dataList_nil hxs
                          have hnot :=
                            (Moist.SMT.Semantics.evalBoolIs_not_true m
                              (SExpr.isCtor "DNil" xs)).mp hg
                          exact False.elim (evalBoolIs_true_false_contra hnil hnot)
                        · rcases hnilBranch with ⟨rfl, rfl⟩
                          have hnoAlt := termsNoOpaque_get? hnoAlts h1
                          have halt := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
                            (ρ := ρ) (env := env) (t := nilAlt)
                            henv hρno hnoAlt hinner hi
                          rcases halt with ⟨cv, hv, hnov, hbig⟩
                          have hle : alts.length ≤ 2 := by omega
                          exact ⟨cv, hv, hnov,
                            by
                              simp [Moist.CEK.constToTagAndFields, hle, h1, hbig,
                                applyValList]⟩
                  | cons head tail =>
                    cases h0 : alts[0]? with
                    | none =>
                      cases h1 : alts[1]? with
                      | none =>
                        simp [caseSym, hlen, h0, h1] at hmem
                        simp [branchOutcomes] at hmem
                      | some nilAlt =>
                        simp [caseSym, hlen, h0, h1] at hbr
                        rcases hbr with ⟨rfl, rfl⟩
                        have hfalse :=
                          Moist.SMT.Semantics.evalBoolIs_isDNil_false_of_dataList_cons hxs
                        exact False.elim (evalBoolIs_true_false_contra hg hfalse)
                    | some consAlt =>
                      cases h1 : alts[1]? with
                      | none =>
                        simp [caseSym, hlen, h0, h1] at hbr
                        rcases hbr with ⟨rfl, rfl⟩
                        have hbind := bindOut_path_ok (m := m)
                          (xs := evalSym fuel ρ consAlt)
                          (k := fun vAlt =>
                            applyListSym fuel vAlt [fieldFromDataList xs, tailFromDataList xs])
                          hinner hi
                        rcases hbind with
                          ⟨pcAlt, vAlt, pcApply, hmemAlt, hmemApply,
                            hpcEq2, hpcAlt, hpcApply⟩
                        have hnoAlt := termsNoOpaque_get? hnoAlts h0
                        have halt := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
                          (ρ := ρ) (env := env) (t := consAlt)
                          henv hρno hnoAlt hmemAlt hpcAlt
                        rcases halt with ⟨cvAlt, hvAlt, hnoVAlt, hbigAlt⟩
                        have hheadEval :=
                          Moist.SMT.Semantics.eval_dhead_of (m := m) (e := xs)
                            (h := head) (t := tail) hxs
                        have htailEval :=
                          Moist.SMT.Semantics.eval_dtail_of (m := m) (e := xs)
                            (h := head) (t := tail) hxs
                        have hargs :
                            symValListToCekList? m
                                [fieldFromDataList xs, tailFromDataList xs] =
                              some [.VCon (.Data head), .VCon (.ConstDataList tail)] := by
                          simp [fieldFromDataList, tailFromDataList, symValListToCekList?,
                            symValToCek?, symConstToCek?, hheadEval, htailEval]
                        have hnoArgs :
                            symValsNoOpaqueForSoundness
                                [fieldFromDataList xs, tailFromDataList xs] = true := by
                          simp [fieldFromDataList, tailFromDataList,
                            symValsNoOpaqueForSoundness, symValNoOpaqueForSoundness]
                        have happ := applyListSym_path_ok (m := m) (fuel := fuel)
                          (vf := vAlt)
                          (args := [fieldFromDataList xs, tailFromDataList xs])
                          (cvf := cvAlt)
                          (cargs := [.VCon (.Data head), .VCon (.ConstDataList tail)])
                          hvAlt hnoVAlt hargs hnoArgs hmemApply hpcApply
                        rcases happ with ⟨cv, hv, hnov, happVal⟩
                        have hle : alts.length ≤ 2 := by omega
                        exact ⟨cv, hv, hnov,
                          by
                            simp [Moist.CEK.constToTagAndFields, hle, h0,
                              hbigAlt, happVal]⟩
                      | some nilAlt =>
                        simp [caseSym, hlen, h0, h1] at hbr
                        rcases hbr with hcons | hnilBranch
                        · rcases hcons with ⟨rfl, rfl⟩
                          have hbind := bindOut_path_ok (m := m)
                            (xs := evalSym fuel ρ consAlt)
                            (k := fun vAlt =>
                              applyListSym fuel vAlt [fieldFromDataList xs, tailFromDataList xs])
                            hinner hi
                          rcases hbind with
                            ⟨pcAlt, vAlt, pcApply, hmemAlt, hmemApply,
                              hpcEq2, hpcAlt, hpcApply⟩
                          have hnoAlt := termsNoOpaque_get? hnoAlts h0
                          have halt := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
                            (ρ := ρ) (env := env) (t := consAlt)
                            henv hρno hnoAlt hmemAlt hpcAlt
                          rcases halt with ⟨cvAlt, hvAlt, hnoVAlt, hbigAlt⟩
                          have hheadEval :=
                            Moist.SMT.Semantics.eval_dhead_of (m := m) (e := xs)
                              (h := head) (t := tail) hxs
                          have htailEval :=
                            Moist.SMT.Semantics.eval_dtail_of (m := m) (e := xs)
                              (h := head) (t := tail) hxs
                          have hargs :
                              symValListToCekList? m
                                  [fieldFromDataList xs, tailFromDataList xs] =
                                some [.VCon (.Data head), .VCon (.ConstDataList tail)] := by
                            simp [fieldFromDataList, tailFromDataList, symValListToCekList?,
                              symValToCek?, symConstToCek?, hheadEval, htailEval]
                          have hnoArgs :
                              symValsNoOpaqueForSoundness
                                  [fieldFromDataList xs, tailFromDataList xs] = true := by
                            simp [fieldFromDataList, tailFromDataList,
                              symValsNoOpaqueForSoundness, symValNoOpaqueForSoundness]
                          have happ := applyListSym_path_ok (m := m) (fuel := fuel)
                            (vf := vAlt)
                            (args := [fieldFromDataList xs, tailFromDataList xs])
                            (cvf := cvAlt)
                            (cargs := [.VCon (.Data head), .VCon (.ConstDataList tail)])
                            hvAlt hnoVAlt hargs hnoArgs hmemApply hpcApply
                          rcases happ with ⟨cv, hv, hnov, happVal⟩
                          have hle : alts.length ≤ 2 := by omega
                          exact ⟨cv, hv, hnov,
                            by
                              simp [Moist.CEK.constToTagAndFields, hle, h0,
                                hbigAlt, happVal]⟩
                        · rcases hnilBranch with ⟨rfl, rfl⟩
                          have hfalse :=
                            Moist.SMT.Semantics.evalBoolIs_isDNil_false_of_dataList_cons hxs
                          exact False.elim (evalBoolIs_true_false_contra hg hfalse)
              | bool b => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | int i => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | string s => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | bytes bs => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | data d => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | dataPairList xs' => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | val val => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | valList xs' => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | g1 g => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | g2 g => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | ml r => simp [symValToCek?, symConstToCek?, hxs] at hscrut
        | pairData a b =>
            cases ha : SmtSem.eval m a with
            | none => simp [symValToCek?, symConstToCek?, ha] at hscrut
            | some sva =>
              cases hb : SmtSem.eval m b with
              | none => simp [symValToCek?, symConstToCek?, ha, hb] at hscrut
              | some svb =>
                cases sva <;> cases svb <;>
                  simp [symValToCek?, symConstToCek?, ha, hb] at hscrut
                rename_i da db
                subst cscrut
                by_cases hlen : alts.length > 1
                · simp [caseSym, hlen, err] at hmem
                · cases hget : alts[0]? with
                  | none => simp [caseSym, hlen, hget, err] at hmem
                  | some alt =>
                    have hbind := bindOut_path_ok (m := m)
                      (xs := evalSym fuel ρ alt)
                      (k := fun vAlt =>
                        applyListSym fuel vAlt [.const (.data a), .const (.data b)])
                      (by simpa [caseSym, hlen, hget] using hmem) hpc
                    rcases hbind with
                      ⟨pcAlt, vAlt, pcApply, hmemAlt, hmemApply,
                        hpcEq, hpcAlt, hpcApply⟩
                    have hnoAlt := termsNoOpaque_get? hnoAlts hget
                    have halt := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
                      (ρ := ρ) (env := env) (t := alt)
                      henv hρno hnoAlt hmemAlt hpcAlt
                    rcases halt with ⟨cvAlt, hvAlt, hnoVAlt, hbigAlt⟩
                    have hargs :
                        symValListToCekList? m [.const (.data a), .const (.data b)] =
                          some [.VCon (.Data da), .VCon (.Data db)] := by
                      simp [symValListToCekList?, symValToCek?, symConstToCek?, ha, hb]
                    have hnoArgs :
                        symValsNoOpaqueForSoundness [.const (.data a), .const (.data b)] =
                          true := by
                      simp [symValsNoOpaqueForSoundness, symValNoOpaqueForSoundness]
                    have happ := applyListSym_path_ok (m := m) (fuel := fuel)
                      (vf := vAlt)
                      (args := [.const (.data a), .const (.data b)])
                      (cvf := cvAlt) (cargs := [.VCon (.Data da), .VCon (.Data db)])
                      hvAlt hnoVAlt hargs hnoArgs hmemApply hpcApply
                    rcases happ with ⟨cv, hv, hnov, happVal⟩
                    exact ⟨cv, hv, hnov,
                      by
                        simp [Moist.CEK.constToTagAndFields, hlen, hget,
                          hbigAlt, happVal]⟩
        | bytes bs =>
            simp [caseSym, err] at hmem
        | string s =>
            simp [caseSym, err] at hmem
        | pairDataList xs =>
            simp [caseSym, err] at hmem
        | data d =>
            simp [caseSym, err] at hmem
        | array xs =>
            simp [caseSym, err] at hmem
        | g1 g =>
            simp [caseSym, err] at hmem
        | g2 g =>
            simp [caseSym, err] at hmem
        | ml r =>
            simp [caseSym, err] at hmem
    | dyn e =>
        cases he : SmtSem.eval m e with
        | none => simp [symValToCek?, he] at hscrut
        | some sv =>
          change Moist.SMT.Semantics.eval m e = some sv at he
          cases sv with
          | val semv =>
            have hbranch := branchOutcomes_path_ok (m := m)
              (hmem := by simpa [caseSym] using hmem) hpc
            rcases hbranch with
              ⟨g, os, innerPc, hbr, hinner, hpcEq, hg, hi⟩
            simp [caseSym] at hbr
            rcases hbr with hbool | hrest
            · rcases hbool with ⟨hlen, i, alt, henum, hgEq, hosEq⟩
              subst g
              subst os
              have hparts := pcHolds_all2 (m := m) hg
              obtain ⟨bval, heBool⟩ :=
                Moist.SMT.Semantics.evalBoolIs_isVBool_true hparts.1
              rw [he] at heBool
              injection heBool with hsv
              injection hsv with hsemv
              subst semv
              simp [symValToCek?, semValToCek?, semValToConst?, he] at hscrut
              subst cscrut
              have hboolTagEval :
                  SmtSem.eval m (SExpr.ite (.app "unVBool" [e]) (.int 1) (.int 0)) =
                    some (.int (if bval then 1 else 0)) := by
                have hun := Moist.SMT.Semantics.eval_unVBool_of (m := m) (e := e) he
                change SmtSem.eval m (Expr.ite (.app "unVBool" [e]) (.int 1) (.int 0)) =
                  some (.int (if bval then 1 else 0))
                rw [eval_ite_of_bool (m := m) (c := .app "unVBool" [e])
                  (t := .int 1) (e := .int 0) hun]
                cases bval <;> simp [Moist.SMT.Semantics.eval]
              have htagEq :
                  (if bval then (1 : Int) else 0) = Int.ofNat i :=
                pcHolds_eq_int hboolTagEval
                  (by simp [Moist.SMT.Semantics.eval]) hparts.2
              have hget : alts[i]? = some alt := enumerate_mem_get? henum
              have hnoAlt := termsNoOpaque_get? hnoAlts hget
              have halt := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
                (ρ := ρ) (env := env) (t := alt)
                henv hρno hnoAlt hinner hi
              rcases halt with ⟨cv, hv, hnov, hbig⟩
              refine ⟨cv, hv, hnov, ?_⟩
              cases bval
              · have hi0 : i = 0 := intOfNat_eq_zero htagEq
                subst i
                simp [Moist.CEK.constToTagAndFields, hlen, hget, hbig,
                  applyValList]
              · have hi1 : i = 1 := intOfNat_eq_one htagEq
                subst i
                simp [Moist.CEK.constToTagAndFields, hlen, hget, hbig,
                  applyValList]
            · rcases hrest with hunit | hrest
              · rcases hunit with ⟨hlen, hunitMem⟩
                cases h0 : alts[0]? with
                | none => simp [h0] at hunitMem
                | some alt =>
                  simp [h0] at hunitMem
                  rcases hunitMem with ⟨rfl, rfl⟩
                  have heUnit := Moist.SMT.Semantics.evalBoolIs_isVUnit_true hg
                  rw [he] at heUnit
                  injection heUnit with hsv
                  injection hsv with hsemv
                  subst semv
                  simp [symValToCek?, semValToCek?, semValToConst?, he] at hscrut
                  subst cscrut
                  have hnoAlt := termsNoOpaque_get? hnoAlts h0
                  have halt := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
                    (ρ := ρ) (env := env) (t := alt)
                    henv hρno hnoAlt hinner hi
                  rcases halt with ⟨cv, hv, hnov, hbig⟩
                  exact ⟨cv, hv, hnov,
                    by
                      simp [Moist.CEK.constToTagAndFields, hlen, h0, hbig,
                        applyValList]⟩
              · rcases hrest with hint | hrest
                · rcases hint with ⟨i, alt, henum, hgEq, hosEq⟩
                  subst g
                  subst os
                  have hparts := pcHolds_all3 (m := m) hg
                  obtain ⟨ival, heInt⟩ :=
                    Moist.SMT.Semantics.evalBoolIs_isVInt_true hparts.1
                  rw [he] at heInt
                  injection heInt with hsv
                  injection hsv with hsemv
                  subst semv
                  simp [symValToCek?, semValToCek?, semValToConst?, he] at hscrut
                  subst cscrut
                  have hun := Moist.SMT.Semantics.eval_unVInt_of (m := m) (e := e) he
                  have hnonneg : 0 ≤ ival := pcHolds_nonneg hun hparts.2.1
                  have htagEq : ival = Int.ofNat i :=
                    pcHolds_eq_int hun (by simp [Moist.SMT.Semantics.eval])
                      hparts.2.2
                  have hget : alts[i]? = some alt := enumerate_mem_get? henum
                  have hnoAlt := termsNoOpaque_get? hnoAlts hget
                  have halt := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
                    (ρ := ρ) (env := env) (t := alt)
                    henv hρno hnoAlt hinner hi
                  rcases halt with ⟨cv, hv, hnov, hbig⟩
                  refine ⟨cv, hv, hnov, ?_⟩
                  subst ival
                  simp [Moist.CEK.constToTagAndFields, hget, hbig, applyValList]
                · rcases hrest with hlist | hrest
                  · rcases hlist with ⟨hlen, hlistMem⟩
                    rcases hlistMem with hcons | hnil
                    · cases h0 : alts[0]? with
                      | none => simp [h0] at hcons
                      | some consAlt =>
                        simp [h0] at hcons
                        rcases hcons with ⟨rfl, rfl⟩
                        have hparts := pcHolds_all2 (m := m) hg
                        obtain ⟨xs, heList⟩ :=
                          Moist.SMT.Semantics.evalBoolIs_isVList_true hparts.1
                        rw [he] at heList
                        injection heList with hsv
                        injection hsv with hsemv
                        subst semv
                        have hxs := Moist.SMT.Semantics.eval_unVList_of (m := m)
                          (e := e) he
                        cases xs with
                        | nil =>
                          have hnil :=
                            Moist.SMT.Semantics.evalBoolIs_isVNil_true_of_valList_nil hxs
                          have hnot :=
                            (Moist.SMT.Semantics.evalBoolIs_not_true m
                              (SExpr.isCtor "VNil" (.app "unVList" [e]))).mp hparts.2
                          exact False.elim (evalBoolIs_true_false_contra hnil hnot)
                        | cons head tail =>
                          cases hheadConst : semValToConst? head with
                          | none =>
                            simp [symValToCek?, semValToCek?, semValToConst?,
                              semValListToConstList?, he, hheadConst] at hscrut
                          | some headConst =>
                            cases htailConst : semValListToConstList? tail with
                            | none =>
                              simp [symValToCek?, semValToCek?, semValToConst?,
                                semValListToConstList?, he, hheadConst, htailConst] at hscrut
                            | some tailConst =>
                              simp [symValToCek?, semValToCek?, semValToConst?,
                                semValListToConstList?, he, hheadConst, htailConst] at hscrut
                              subst cscrut
                              have hbind := bindOut_path_ok (m := m)
                                (xs := evalSym fuel ρ consAlt)
                                (k := fun vAlt =>
                                  applyListSym fuel vAlt
                                    [fieldFromValList (.app "unVList" [e]),
                                      tailFromValList (.app "unVList" [e])])
                                hinner hi
                              rcases hbind with
                                ⟨pcAlt, vAlt, pcApply, hmemAlt, hmemApply,
                                  hpcEq2, hpcAlt, hpcApply⟩
                              have hnoAlt := termsNoOpaque_get? hnoAlts h0
                              have halt := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
                                (ρ := ρ) (env := env) (t := consAlt)
                                henv hρno hnoAlt hmemAlt hpcAlt
                              rcases halt with ⟨cvAlt, hvAlt, hnoVAlt, hbigAlt⟩
                              have hheadEval :=
                                Moist.SMT.Semantics.eval_vhead_of (m := m)
                                  (e := .app "unVList" [e]) (h := head) (t := tail) hxs
                              have htailEval :=
                                Moist.SMT.Semantics.eval_vtail_of (m := m)
                                  (e := .app "unVList" [e]) (h := head) (t := tail) hxs
                              have hargs :
                                  symValListToCekList? m
                                      [fieldFromValList (.app "unVList" [e]),
                                        tailFromValList (.app "unVList" [e])] =
                                    some [.VCon headConst, .VCon (.ConstList tailConst)] := by
                                have hheadCek := semValToCek_of_const hheadConst
                                simp [fieldFromValList, tailFromValList, symValListToCekList?,
                                  symValToCek?, symConstToCek?, hheadEval, htailEval,
                                  hheadCek, htailConst]
                              have hnoArgs :
                                  symValsNoOpaqueForSoundness
                                      [fieldFromValList (.app "unVList" [e]),
                                        tailFromValList (.app "unVList" [e])] = true := by
                                simp [fieldFromValList, tailFromValList,
                                  symValsNoOpaqueForSoundness, symValNoOpaqueForSoundness]
                              have happ := applyListSym_path_ok (m := m) (fuel := fuel)
                                (vf := vAlt)
                                (args := [fieldFromValList (.app "unVList" [e]),
                                  tailFromValList (.app "unVList" [e])])
                                (cvf := cvAlt)
                                (cargs := [.VCon headConst, .VCon (.ConstList tailConst)])
                                hvAlt hnoVAlt hargs hnoArgs hmemApply hpcApply
                              rcases happ with ⟨cv, hv, hnov, happVal⟩
                              exact ⟨cv, hv, hnov,
                                by
                                  simp [Moist.CEK.constToTagAndFields, hlen, h0,
                                    hbigAlt, happVal]⟩
                    · cases h1 : alts[1]? with
                      | none => simp [h1] at hnil
                      | some nilAlt =>
                        simp [h1] at hnil
                        rcases hnil with ⟨rfl, rfl⟩
                        have hparts := pcHolds_all2 (m := m) hg
                        obtain ⟨xs, heList⟩ :=
                          Moist.SMT.Semantics.evalBoolIs_isVList_true hparts.1
                        rw [he] at heList
                        injection heList with hsv
                        injection hsv with hsemv
                        subst semv
                        have hxs := Moist.SMT.Semantics.eval_unVList_of (m := m)
                          (e := e) he
                        cases xs with
                        | nil =>
                          simp [symValToCek?, semValToCek?, semValToConst?,
                            semValListToConstList?, he] at hscrut
                          subst cscrut
                          have hnoAlt := termsNoOpaque_get? hnoAlts h1
                          have halt := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
                            (ρ := ρ) (env := env) (t := nilAlt)
                            henv hρno hnoAlt hinner hi
                          rcases halt with ⟨cv, hv, hnov, hbig⟩
                          exact ⟨cv, hv, hnov,
                            by
                              simp [Moist.CEK.constToTagAndFields, hlen, h1, hbig,
                                applyValList]⟩
                        | cons head tail =>
                          have hfalse :=
                            Moist.SMT.Semantics.evalBoolIs_isVNil_false_of_valList_cons hxs
                          exact False.elim (evalBoolIs_true_false_contra hparts.2 hfalse)
                  · rcases hrest with hdataList | hrest
                    · rcases hdataList with ⟨hlen, hdataMem⟩
                      rcases hdataMem with hcons | hnil
                      · cases h0 : alts[0]? with
                        | none => simp [h0] at hcons
                        | some consAlt =>
                          simp [h0] at hcons
                          rcases hcons with ⟨rfl, rfl⟩
                          have hparts := pcHolds_all2 (m := m) hg
                          obtain ⟨xs, heDataList⟩ :=
                            Moist.SMT.Semantics.evalBoolIs_isVDataList_true hparts.1
                          rw [he] at heDataList
                          injection heDataList with hsv
                          injection hsv with hsemv
                          subst semv
                          have hxs := Moist.SMT.Semantics.eval_unVDataList_of (m := m)
                            (e := e) he
                          cases xs with
                          | nil =>
                            have hnil :=
                              Moist.SMT.Semantics.evalBoolIs_isDNil_true_of_dataList_nil hxs
                            have hnot :=
                              (Moist.SMT.Semantics.evalBoolIs_not_true m
                                (SExpr.isCtor "DNil" (.app "unVDataList" [e]))).mp hparts.2
                            exact False.elim (evalBoolIs_true_false_contra hnil hnot)
                          | cons head tail =>
                            simp [symValToCek?, semValToCek?, semValToConst?, he] at hscrut
                            subst cscrut
                            have hbind := bindOut_path_ok (m := m)
                              (xs := evalSym fuel ρ consAlt)
                              (k := fun vAlt =>
                                applyListSym fuel vAlt
                                  [fieldFromDataList (.app "unVDataList" [e]),
                                    tailFromDataList (.app "unVDataList" [e])])
                              hinner hi
                            rcases hbind with
                              ⟨pcAlt, vAlt, pcApply, hmemAlt, hmemApply,
                                hpcEq2, hpcAlt, hpcApply⟩
                            have hnoAlt := termsNoOpaque_get? hnoAlts h0
                            have halt := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
                              (ρ := ρ) (env := env) (t := consAlt)
                              henv hρno hnoAlt hmemAlt hpcAlt
                            rcases halt with ⟨cvAlt, hvAlt, hnoVAlt, hbigAlt⟩
                            have hheadEval :=
                              Moist.SMT.Semantics.eval_dhead_of (m := m)
                                (e := .app "unVDataList" [e]) (h := head) (t := tail) hxs
                            have htailEval :=
                              Moist.SMT.Semantics.eval_dtail_of (m := m)
                                (e := .app "unVDataList" [e]) (h := head) (t := tail) hxs
                            have hargs :
                                symValListToCekList? m
                                    [fieldFromDataList (.app "unVDataList" [e]),
                                      tailFromDataList (.app "unVDataList" [e])] =
                                  some [.VCon (.Data head), .VCon (.ConstDataList tail)] := by
                              simp [fieldFromDataList, tailFromDataList,
                                symValListToCekList?, symValToCek?, symConstToCek?,
                                hheadEval, htailEval]
                            have hnoArgs :
                                symValsNoOpaqueForSoundness
                                    [fieldFromDataList (.app "unVDataList" [e]),
                                      tailFromDataList (.app "unVDataList" [e])] = true := by
                              simp [fieldFromDataList, tailFromDataList,
                                symValsNoOpaqueForSoundness, symValNoOpaqueForSoundness]
                            have happ := applyListSym_path_ok (m := m) (fuel := fuel)
                              (vf := vAlt)
                              (args := [fieldFromDataList (.app "unVDataList" [e]),
                                tailFromDataList (.app "unVDataList" [e])])
                              (cvf := cvAlt)
                              (cargs := [.VCon (.Data head), .VCon (.ConstDataList tail)])
                              hvAlt hnoVAlt hargs hnoArgs hmemApply hpcApply
                            rcases happ with ⟨cv, hv, hnov, happVal⟩
                            exact ⟨cv, hv, hnov,
                              by
                                simp [Moist.CEK.constToTagAndFields, hlen, h0,
                                  hbigAlt, happVal]⟩
                      · cases h1 : alts[1]? with
                        | none => simp [h1] at hnil
                        | some nilAlt =>
                          simp [h1] at hnil
                          rcases hnil with ⟨rfl, rfl⟩
                          have hparts := pcHolds_all2 (m := m) hg
                          obtain ⟨xs, heDataList⟩ :=
                            Moist.SMT.Semantics.evalBoolIs_isVDataList_true hparts.1
                          rw [he] at heDataList
                          injection heDataList with hsv
                          injection hsv with hsemv
                          subst semv
                          have hxs := Moist.SMT.Semantics.eval_unVDataList_of (m := m)
                            (e := e) he
                          cases xs with
                          | nil =>
                            simp [symValToCek?, semValToCek?, semValToConst?, he] at hscrut
                            subst cscrut
                            have hnoAlt := termsNoOpaque_get? hnoAlts h1
                            have halt := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
                              (ρ := ρ) (env := env) (t := nilAlt)
                              henv hρno hnoAlt hinner hi
                            rcases halt with ⟨cv, hv, hnov, hbig⟩
                            exact ⟨cv, hv, hnov,
                              by
                                simp [Moist.CEK.constToTagAndFields, hlen, h1, hbig,
                                  applyValList]⟩
                          | cons head tail =>
                            have hfalse :=
                              Moist.SMT.Semantics.evalBoolIs_isDNil_false_of_dataList_cons hxs
                            exact False.elim (evalBoolIs_true_false_contra hparts.2 hfalse)
                    · rcases hrest with hpair | hrest
                      · rcases hpair with ⟨hlen, hpairMem⟩
                        cases h0 : alts[0]? with
                        | none => simp [h0] at hpairMem
                        | some alt =>
                          simp [h0] at hpairMem
                          rcases hpairMem with ⟨rfl, rfl⟩
                          obtain ⟨a, b, hePair⟩ :=
                            Moist.SMT.Semantics.evalBoolIs_isVPair_true hg
                          rw [he] at hePair
                          injection hePair with hsv
                          injection hsv with hsemv
                          subst semv
                          cases haConst : semValToConst? a with
                          | none =>
                            simp [symValToCek?, semValToCek?, semValToConst?, he,
                              haConst] at hscrut
                          | some ca =>
                            cases hbConst : semValToConst? b with
                            | none =>
                              simp [symValToCek?, semValToCek?, semValToConst?, he,
                                haConst, hbConst] at hscrut
                            | some cb =>
                              simp [symValToCek?, semValToCek?, semValToConst?, he,
                                haConst, hbConst] at hscrut
                              subst cscrut
                              have hbind := bindOut_path_ok (m := m)
                                (xs := evalSym fuel ρ alt)
                                (k := fun vAlt =>
                                  applyListSym fuel vAlt
                                    [.dyn (.app "vfst" [e]), .dyn (.app "vsnd" [e])])
                                hinner hi
                              rcases hbind with
                                ⟨pcAlt, vAlt, pcApply, hmemAlt, hmemApply,
                                  hpcEq2, hpcAlt, hpcApply⟩
                              have hnoAlt := termsNoOpaque_get? hnoAlts h0
                              have halt := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
                                (ρ := ρ) (env := env) (t := alt)
                                henv hρno hnoAlt hmemAlt hpcAlt
                              rcases halt with ⟨cvAlt, hvAlt, hnoVAlt, hbigAlt⟩
                              have hvfst :=
                                Moist.SMT.Semantics.eval_vfst_of (m := m) (e := e)
                                  (a := a) (b := b) he
                              have hvsnd :=
                                Moist.SMT.Semantics.eval_vsnd_of (m := m) (e := e)
                                  (a := a) (b := b) he
                              have hargs :
                                  symValListToCekList? m
                                      [.dyn (.app "vfst" [e]), .dyn (.app "vsnd" [e])] =
                                    some [.VCon ca, .VCon cb] := by
                                have haCek := semValToCek_of_const haConst
                                have hbCek := semValToCek_of_const hbConst
                                simp [symValListToCekList?, symValToCek?, hvfst, hvsnd,
                                  haCek, hbCek]
                              have hnoArgs :
                                  symValsNoOpaqueForSoundness
                                      [.dyn (.app "vfst" [e]), .dyn (.app "vsnd" [e])] =
                                    true := by
                                simp [symValsNoOpaqueForSoundness, symValNoOpaqueForSoundness]
                              have happ := applyListSym_path_ok (m := m) (fuel := fuel)
                                (vf := vAlt)
                                (args := [.dyn (.app "vfst" [e]), .dyn (.app "vsnd" [e])])
                                (cvf := cvAlt) (cargs := [.VCon ca, .VCon cb])
                                hvAlt hnoVAlt hargs hnoArgs hmemApply hpcApply
                              rcases happ with ⟨cv, hv, hnov, happVal⟩
                              exact ⟨cv, hv, hnov,
                                by
                                  simp [Moist.CEK.constToTagAndFields, hlen, h0,
                                    hbigAlt, happVal]⟩
                      · rcases hrest with hpairData | hconstr
                        · rcases hpairData with ⟨hlen, hpairDataMem⟩
                          cases h0 : alts[0]? with
                          | none => simp [h0] at hpairDataMem
                          | some alt =>
                            simp [h0] at hpairDataMem
                            rcases hpairDataMem with ⟨rfl, rfl⟩
                            obtain ⟨a, b, hePairData⟩ :=
                              Moist.SMT.Semantics.evalBoolIs_isVPairData_true hg
                            rw [he] at hePairData
                            injection hePairData with hsv
                            injection hsv with hsemv
                            subst semv
                            simp [symValToCek?, semValToCek?, semValToConst?, he] at hscrut
                            subst cscrut
                            have hbind := bindOut_path_ok (m := m)
                              (xs := evalSym fuel ρ alt)
                              (k := fun vAlt =>
                                applyListSym fuel vAlt
                                  [.const (.data (.app "pdfst" [e])),
                                    .const (.data (.app "pdsnd" [e]))])
                              hinner hi
                            rcases hbind with
                              ⟨pcAlt, vAlt, pcApply, hmemAlt, hmemApply,
                                hpcEq2, hpcAlt, hpcApply⟩
                            have hnoAlt := termsNoOpaque_get? hnoAlts h0
                            have halt := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
                              (ρ := ρ) (env := env) (t := alt)
                              henv hρno hnoAlt hmemAlt hpcAlt
                            rcases halt with ⟨cvAlt, hvAlt, hnoVAlt, hbigAlt⟩
                            have hfst :=
                              Moist.SMT.Semantics.eval_pdfst_of (m := m) (e := e)
                                (a := a) (b := b) he
                            have hsnd :=
                              Moist.SMT.Semantics.eval_pdsnd_of (m := m) (e := e)
                                (a := a) (b := b) he
                            have hargs :
                                symValListToCekList? m
                                    [.const (.data (.app "pdfst" [e])),
                                      .const (.data (.app "pdsnd" [e]))] =
                                  some [.VCon (.Data a), .VCon (.Data b)] := by
                              simp [symValListToCekList?, symValToCek?, symConstToCek?,
                                hfst, hsnd]
                            have hnoArgs :
                                symValsNoOpaqueForSoundness
                                    [.const (.data (.app "pdfst" [e])),
                                      .const (.data (.app "pdsnd" [e]))] = true := by
                              simp [symValsNoOpaqueForSoundness, symValNoOpaqueForSoundness]
                            have happ := applyListSym_path_ok (m := m) (fuel := fuel)
                              (vf := vAlt)
                              (args := [.const (.data (.app "pdfst" [e])),
                                .const (.data (.app "pdsnd" [e]))])
                              (cvf := cvAlt) (cargs := [.VCon (.Data a), .VCon (.Data b)])
                              hvAlt hnoVAlt hargs hnoArgs hmemApply hpcApply
                            rcases happ with ⟨cv, hv, hnov, happVal⟩
                            exact ⟨cv, hv, hnov,
                              by
                                simp [Moist.CEK.constToTagAndFields, hlen, h0,
                                  hbigAlt, happVal]⟩
                        · rcases hconstr with ⟨i, alt, henum, hgEq, hosEq⟩
                          subst g
                          subst os
                          have hparts := pcHolds_all2 (m := m) hg
                          obtain ⟨tag, fields, heConstr⟩ :=
                            Moist.SMT.Semantics.evalBoolIs_isVConstr_true hparts.1
                          rw [he] at heConstr
                          injection heConstr with hsv
                          injection hsv with hsemv
                          subst semv
                          by_cases hneg : tag < 0
                          · simp [symValToCek?, semValToCek?, he, hneg] at hscrut
                          · cases hfields : semValListToCekList? fields with
                            | none =>
                              simp [symValToCek?, semValToCek?, he, hneg, hfields] at hscrut
                            | some cfields =>
                              simp [symValToCek?, semValToCek?, he, hneg, hfields] at hscrut
                              subst cscrut
                              have htagEval :=
                                Moist.SMT.Semantics.eval_vConstrTag_of (m := m)
                                  (e := e) (tag := tag) (fields := fields) he
                              have hfieldsEval :=
                                Moist.SMT.Semantics.eval_vConstrFields_of (m := m)
                                  (e := e) (tag := tag) (fields := fields) he
                              have htagEq : tag = Int.ofNat i :=
                                pcHolds_eq_int htagEval
                                  (by simp [Moist.SMT.Semantics.eval]) hparts.2
                              have hget : alts[i]? = some alt := enumerate_mem_get? henum
                              have hbind := bindOut_path_ok (m := m)
                                (xs := evalSym fuel ρ alt)
                                (k := fun vAlt =>
                                  applyValListSym fuel vAlt (.app "vConstrFields" [e]))
                                hinner hi
                              rcases hbind with
                                ⟨pcAlt, vAlt, pcApply, hmemAlt, hmemApply,
                                  hpcEq2, hpcAlt, hpcApply⟩
                              have hnoAlt := termsNoOpaque_get? hnoAlts hget
                              have halt := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
                                (ρ := ρ) (env := env) (t := alt)
                                henv hρno hnoAlt hmemAlt hpcAlt
                              rcases halt with ⟨cvAlt, hvAlt, hnoVAlt, hbigAlt⟩
                              have happ := applyValListSym_path_ok (m := m) (fuel := fuel)
                                (vf := vAlt) (fieldsExpr := .app "vConstrFields" [e])
                                (fields := fields) (cvf := cvAlt) (cfields := cfields)
                                hvAlt hnoVAlt hfieldsEval hfields hmemApply hpcApply
                              rcases happ with ⟨cv, hv, hnov, happVal⟩
                              refine ⟨cv, hv, hnov, ?_⟩
                              subst tag
                              simp [hget, hbigAlt, happVal]
          | bool b => simp [symValToCek?, he] at hscrut
            | int i => simp [symValToCek?, he] at hscrut
            | string s => simp [symValToCek?, he] at hscrut
            | bytes bs => simp [symValToCek?, he] at hscrut
            | data d => simp [symValToCek?, he] at hscrut
            | dataList xs => simp [symValToCek?, he] at hscrut
            | dataPairList xs => simp [symValToCek?, he] at hscrut
            | valList xs => simp [symValToCek?, he] at hscrut
            | g1 g => simp [symValToCek?, he] at hscrut
            | g2 g => simp [symValToCek?, he] at hscrut
            | ml r => simp [symValToCek?, he] at hscrut
    | pair a b =>
        cases ha : symValToCek? m a with
        | none => simp [symValToCek?, ha] at hscrut
        | some ca =>
          cases hb : symValToCek? m b with
          | none => simp [symValToCek?, ha, hb] at hscrut
          | some cb =>
            cases ca <;> cases cb <;> simp [symValToCek?, ha, hb] at hscrut
            rename_i caConst cbConst
            subst cscrut
            have hnoAB : symValNoOpaqueForSoundness a = true ∧
                symValNoOpaqueForSoundness b = true := by
              simpa [symValNoOpaqueForSoundness] using hnoScrut
            by_cases hlen : alts.length > 1
            · simp [caseSym, hlen, err] at hmem
            · cases hget : alts[0]? with
              | none => simp [caseSym, hlen, hget, err] at hmem
              | some alt =>
                have hbind := bindOut_path_ok (m := m)
                  (xs := evalSym fuel ρ alt)
                  (k := fun vAlt => applyListSym fuel vAlt [a, b])
                  (by simpa [caseSym, hlen, hget] using hmem) hpc
                rcases hbind with
                  ⟨pcAlt, vAlt, pcApply, hmemAlt, hmemApply,
                    hpcEq, hpcAlt, hpcApply⟩
                have hnoAlt := termsNoOpaque_get? hnoAlts hget
                have halt := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
                  (ρ := ρ) (env := env) (t := alt)
                  henv hρno hnoAlt hmemAlt hpcAlt
                rcases halt with ⟨cvAlt, hvAlt, hnoVAlt, hbigAlt⟩
                have hargs :
                    symValListToCekList? m [a, b] =
                      some [.VCon caConst, .VCon cbConst] := by
                  simp [symValListToCekList?, ha, hb]
                have hnoArgs : symValsNoOpaqueForSoundness [a, b] = true := by
                  simp [symValsNoOpaqueForSoundness, hnoAB.1, hnoAB.2]
                have happ := applyListSym_path_ok (m := m) (fuel := fuel)
                  (vf := vAlt) (args := [a, b]) (cvf := cvAlt)
                  (cargs := [.VCon caConst, .VCon cbConst])
                  hvAlt hnoVAlt hargs hnoArgs hmemApply hpcApply
                rcases happ with ⟨cv, hv, hnov, happVal⟩
                exact ⟨cv, hv, hnov,
                  by
                    simp [Moist.CEK.constToTagAndFields, hlen, hget,
                      hbigAlt, happVal]⟩
    | lam body ρ =>
        simp [caseSym, err] at hmem
    | delay body ρ =>
        simp [caseSym, err] at hmem
    | builtin b args ea =>
        simp [caseSym, err] at hmem
end

mutual
  theorem evalSym_active_error_noOpaque_le {m : SmtSem.Model} {fuel fuel' : Nat}
      {ρ : List SymVal} {env : CekEnv} {t : Term} {out : Outcome}
      (henv : symEnvToCek? m ρ = some env)
      (hρno : symEnvNoOpaqueForSoundness ρ = true)
      (hno : termNoOpaqueBuiltinsForSoundness t)
      (hmem : out ∈ evalSym fuel ρ t)
      (herr : outcomeErrorActive m out = true)
      (hle : fuel ≤ fuel') :
      bigEval fuel' env t = none := by
    cases fuel with
    | zero =>
        cases out <;> simp [evalSym, timeout, outcomeErrorActive] at hmem herr
    | succ n =>
        cases fuel' with
        | zero => omega
        | succ n' =>
          have hle' : n ≤ n' := by omega
          cases t with
          | Var k =>
              cases hlookup : lookupEnv ρ k with
              | none =>
                  have hmemErr : out ∈ err := by
                    simpa [evalSym, hlookup] using hmem
                  cases out with
                  | ok pc v => simp [err] at hmemErr
                  | timeout pc => simp [err] at hmemErr
                  | error pc =>
                      have hpc := err_mem_singleton hmemErr
                      subst pc
                      have hlookupCek := symEnv_lookup_none henv hlookup
                      simp [bigEval, hlookupCek]
              | some v =>
                  have hmemOk : out ∈ ok v := by
                    simpa [evalSym, hlookup] using hmem
                  cases out with
                  | ok pc v => simp [outcomeErrorActive] at herr
                  | error pc => simp [ok] at hmemOk
                  | timeout pc => simp [ok] at hmemOk
          | Constant cb =>
              obtain ⟨c, ty⟩ := cb
              have hmemOk : out ∈ ok (constLiteral c) := by
                simpa [evalSym] using hmem
              cases out with
              | ok pc v => simp [outcomeErrorActive] at herr
              | error pc => simp [ok] at hmemOk
              | timeout pc => simp [ok] at hmemOk
          | Builtin b =>
              have hmemOk : out ∈ ok (.builtin b [] (expectedArgs b)) := by
                simpa [evalSym] using hmem
              cases out with
              | ok pc v => simp [outcomeErrorActive] at herr
              | error pc => simp [ok] at hmemOk
              | timeout pc => simp [ok] at hmemOk
          | Lam name body =>
              have hmemOk : out ∈ ok (.lam body ρ) := by
                simpa [evalSym] using hmem
              cases out with
              | ok pc v => simp [outcomeErrorActive] at herr
              | error pc => simp [ok] at hmemOk
              | timeout pc => simp [ok] at hmemOk
          | Delay body =>
              have hmemOk : out ∈ ok (.delay body ρ) := by
                simpa [evalSym] using hmem
              cases out with
              | ok pc v => simp [outcomeErrorActive] at herr
              | error pc => simp [ok] at hmemOk
              | timeout pc => simp [ok] at hmemOk
          | Apply f a =>
              have hnoSplit := termNoOpaque_apply hno
              have hbind := bindOut_active_error (m := m)
                (xs := evalSym n ρ f)
                (k := fun vf => bindOut (evalSym n ρ a) fun va => applySym n vf va)
                (hmem := by simpa [evalSym] using hmem) herr
              rcases hbind with hfunErr | hrest
              · rcases hfunErr with ⟨pcF, hmemF, hpcF⟩
                have hfNone := evalSym_active_error_noOpaque_le (m := m)
                  (fuel := n) (fuel' := n') (ρ := ρ) (env := env) (t := f)
                  henv hρno hnoSplit.1 hmemF
                  (by simpa [outcomeErrorActive] using hpcF) hle'
                simp [bigEval, hfNone]
              · rcases hrest with
                  ⟨pcF, vf, inner, hmemF, hpcF, hmemInner, herrInner⟩
                have hf := evalSym_path_ok_noOpaque (m := m) (fuel := n)
                  (ρ := ρ) (env := env) (t := f)
                  henv hρno hnoSplit.1 hmemF hpcF
                rcases hf with ⟨cvf, hvf, hnof, hbigF⟩
                have hbigF' := bigEval_mono_le hle' hbigF
                have hbind2 := bindOut_active_error (m := m)
                  (xs := evalSym n ρ a) (k := fun va => applySym n vf va)
                  hmemInner herrInner
                rcases hbind2 with hargErr | happErr
                · rcases hargErr with ⟨pcA, hmemA, hpcA⟩
                  have haNone := evalSym_active_error_noOpaque_le (m := m)
                    (fuel := n) (fuel' := n') (ρ := ρ) (env := env) (t := a)
                    henv hρno hnoSplit.2 hmemA
                    (by simpa [outcomeErrorActive] using hpcA) hle'
                  simp [bigEval, hbigF', haNone]
                · rcases happErr with
                    ⟨pcA, va, innerApp, hmemA, hpcA, hmemApp, herrApp⟩
                  have ha := evalSym_path_ok_noOpaque (m := m) (fuel := n)
                    (ρ := ρ) (env := env) (t := a)
                    henv hρno hnoSplit.2 hmemA hpcA
                  rcases ha with ⟨cva, hva, hnoa, hbigA⟩
                  have hbigA' := bigEval_mono_le hle' hbigA
                  have happNone := applySym_active_error_noOpaque_le (m := m)
                    (fuel := n) (fuel' := n') (vf := vf) (va := va)
                    (cvf := cvf) (cva := cva)
                    hvf hnof hva hnoa hmemApp herrApp hle'
                  simp [bigEval, hbigF', hbigA', happNone]
          | Force body =>
              have hnoBody := termNoOpaque_force hno
              have hbind := bindOut_active_error (m := m)
                (xs := evalSym n ρ body) (k := fun vt => forceSym n vt)
                (hmem := by simpa [evalSym] using hmem) herr
              rcases hbind with hbodyErr | hforceErr
              · rcases hbodyErr with ⟨pcT, hmemT, hpcT⟩
                have htNone := evalSym_active_error_noOpaque_le (m := m)
                  (fuel := n) (fuel' := n') (ρ := ρ) (env := env) (t := body)
                  henv hρno hnoBody hmemT
                  (by simpa [outcomeErrorActive] using hpcT) hle'
                simp [bigEval, htNone]
              · rcases hforceErr with
                  ⟨pcT, vt, inner, hmemT, hpcT, hmemForce, herrForce⟩
                have ht := evalSym_path_ok_noOpaque (m := m) (fuel := n)
                  (ρ := ρ) (env := env) (t := body)
                  henv hρno hnoBody hmemT hpcT
                rcases ht with ⟨cvt, hvt, hnot, hbigT⟩
                have hbigT' := bigEval_mono_le hle' hbigT
                have hforceNone := forceSym_active_error_noOpaque_le (m := m)
                  (fuel := n) (fuel' := n') (vt := vt) (cvt := cvt)
                  hvt hnot hmemForce herrForce hle'
                simp [bigEval, hbigT', hforceNone]
          | Constr tag fields =>
              have hnoFields := termNoOpaque_constr_fields hno
              have hbind := bindOut_active_error (m := m)
                (xs := evalListSym n ρ fields)
                (k := fun vals =>
                  match vals with
                  | .constr (.int (-1)) vs => ok (.constr (.int (Int.ofNat tag)) vs)
                  | _ => err)
                (hmem := by simpa [evalSym] using hmem) herr
              rcases hbind with hfieldsErr | hfinalErr
              · rcases hfieldsErr with ⟨pcFields, hmemFields, hpcFields⟩
                have hfieldsNone := evalListSym_active_error_noOpaque_le (m := m)
                  (fuel := n) (fuel' := n') (ρ := ρ) (env := env) (ts := fields)
                  henv hρno hnoFields hmemFields
                  (by simpa [outcomeErrorActive] using hpcFields) hle'
                simp [bigEval, hfieldsNone]
              · rcases hfinalErr with
                  ⟨pcFields, vals, inner, hmemFields, hpcFields, hmemFinal, herrFinal⟩
                have hfields := evalListSym_path_ok_noOpaque (m := m) (fuel := n)
                  (ρ := ρ) (env := env) (ts := fields)
                  henv hρno hnoFields hmemFields hpcFields
                rcases hfields with ⟨vs, cvs, hvals, hvs, hnoVs, hbigFields⟩
                subst vals
                have hbigFields' := bigEvalList_mono_le hle' hbigFields
                cases inner <;> simp [ok, outcomeErrorActive] at hmemFinal herrFinal
          | Case scrut alts =>
              have hnoSplit := termNoOpaque_case hno
              have hbind := bindOut_active_error (m := m)
                (xs := evalSym n ρ scrut)
                (k := fun v => caseSym n ρ v alts)
                (hmem := by simpa [evalSym] using hmem) herr
              rcases hbind with hscrutErr | hcaseErr
              · rcases hscrutErr with ⟨pcScrut, hmemScrut, hpcScrut⟩
                have hscrutNone := evalSym_active_error_noOpaque_le (m := m)
                  (fuel := n) (fuel' := n') (ρ := ρ) (env := env) (t := scrut)
                  henv hρno hnoSplit.1 hmemScrut
                  (by simpa [outcomeErrorActive] using hpcScrut) hle'
                simp [bigEval, hscrutNone]
              · rcases hcaseErr with
                  ⟨pcScrut, vScrut, inner, hmemScrut, hpcScrut, hmemCase, herrCase⟩
                have hscrut := evalSym_path_ok_noOpaque (m := m) (fuel := n)
                  (ρ := ρ) (env := env) (t := scrut)
                  henv hρno hnoSplit.1 hmemScrut hpcScrut
                rcases hscrut with ⟨cvScrut, hvScrut, hnoScrut, hbigScrut⟩
                have hbigScrut' := bigEval_mono_le hle' hbigScrut
                have hcaseNone := caseSym_active_error_noOpaque_le (m := m)
                  (fuel := n) (fuel' := n') (ρ := ρ) (env := env)
                  (scrut := vScrut) (alts := alts) (cscrut := cvScrut)
                  henv hρno hnoSplit.2 hvScrut hnoScrut hmemCase herrCase hle'
                cases cvScrut <;> simpa [bigEval, hbigScrut', caseCekResult] using hcaseNone
          | Error =>
              simp [bigEval]

  theorem evalListSym_active_error_noOpaque_le {m : SmtSem.Model} {fuel fuel' : Nat}
      {ρ : List SymVal} {env : CekEnv} {ts : List Term} {out : Outcome}
      (henv : symEnvToCek? m ρ = some env)
      (hρno : symEnvNoOpaqueForSoundness ρ = true)
      (hno : termsUseOpaqueBuiltinForSoundness ts = false)
      (hmem : out ∈ evalListSym fuel ρ ts)
      (herr : outcomeErrorActive m out = true)
      (hle : fuel ≤ fuel') :
      bigEvalList fuel' env ts = none := by
    cases ts with
    | nil =>
        have hmemOk : out ∈ ok (.constr (.int (-1)) []) := by
          simpa [evalListSym] using hmem
        cases out with
        | ok pc v => simp [outcomeErrorActive] at herr
        | error pc => simp [ok] at hmemOk
        | timeout pc => simp [ok] at hmemOk
    | cons t ts =>
        have hnoSplit := termsNoOpaque_cons hno
        have hbind1 := bindOut_active_error (m := m)
          (xs := evalSym fuel ρ t)
          (k := fun v => bindOut (evalListSym fuel ρ ts) fun rest =>
            match rest with
            | .constr (.int (-1)) vs => ok (.constr (.int (-1)) (v :: vs))
            | _ => err)
          (hmem := by simpa [evalListSym] using hmem) herr
        rcases hbind1 with hheadErr | htailStage
        · rcases hheadErr with ⟨pcHead, hmemHead, hpcHead⟩
          have hheadNone := evalSym_active_error_noOpaque_le (m := m)
            (fuel := fuel) (fuel' := fuel') (ρ := ρ) (env := env) (t := t)
            henv hρno hnoSplit.1 hmemHead
            (by simpa [outcomeErrorActive] using hpcHead) hle
          simp [bigEvalList, hheadNone]
        · rcases htailStage with
            ⟨pcHead, vHead, inner, hmemHead, hpcHead, hmemTailStage, herrTailStage⟩
          have hhead := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
            (ρ := ρ) (env := env) (t := t)
            henv hρno hnoSplit.1 hmemHead hpcHead
          rcases hhead with ⟨cvHead, hvHead, hnoHead, hbigHead⟩
          have hbigHead' := bigEval_mono_le hle hbigHead
          have hbind2 := bindOut_active_error (m := m)
            (xs := evalListSym fuel ρ ts)
            (k := fun rest =>
              match rest with
              | .constr (.int (-1)) vs => ok (.constr (.int (-1)) (vHead :: vs))
              | _ => err)
            hmemTailStage herrTailStage
          rcases hbind2 with htailErr | hfinalErr
          · rcases htailErr with ⟨pcTail, hmemTail, hpcTail⟩
            have htailNone := evalListSym_active_error_noOpaque_le (m := m)
              (fuel := fuel) (fuel' := fuel') (ρ := ρ) (env := env) (ts := ts)
              henv hρno hnoSplit.2 hmemTail
              (by simpa [outcomeErrorActive] using hpcTail) hle
            simp [bigEvalList, hbigHead', htailNone]
          · rcases hfinalErr with
              ⟨pcTail, vRest, innerFinal, hmemTail, hpcTail, hmemFinal, herrFinal⟩
            have htail := evalListSym_path_ok_noOpaque (m := m) (fuel := fuel)
              (ρ := ρ) (env := env) (ts := ts)
              henv hρno hnoSplit.2 hmemTail hpcTail
            rcases htail with ⟨vs, cvs, hvRest, hvs, hnoVs, hbigTail⟩
            subst vRest
            cases innerFinal <;> simp [ok, outcomeErrorActive] at hmemFinal herrFinal

  theorem applySym_active_error_noOpaque_le {m : SmtSem.Model} {fuel fuel' : Nat}
      {vf va : SymVal} {cvf cva : CekValue} {out : Outcome}
      (hvf : symValToCek? m vf = some cvf)
      (hnof : symValNoOpaqueForSoundness vf = true)
      (hva : symValToCek? m va = some cva)
      (hnoa : symValNoOpaqueForSoundness va = true)
      (hmem : out ∈ applySym fuel vf va)
      (herr : outcomeErrorActive m out = true)
      (hle : fuel ≤ fuel') :
      applyVal fuel' cvf cva = none := by
    cases fuel with
    | zero =>
        cases out <;> simp [applySym, timeout, outcomeErrorActive] at hmem herr
    | succ n =>
        cases fuel' with
        | zero => omega
        | succ n' =>
          have hle' : n ≤ n' := by omega
          cases vf with
          | lam body ρ =>
              cases henv0 : symEnvToCek? m ρ <;>
                simp [symValToCek?, henv0] at hvf
              rename_i env0
              subst cvf
              have hsplit : termUsesOpaqueBuiltinForSoundness body = false ∧
                  symEnvNoOpaqueForSoundness ρ = true := by
                simpa [symValNoOpaqueForSoundness] using hnof
              have henvExt := symEnvToCek_extend (m := m) (ρ := ρ)
                (env := env0) (v := va) (cv := cva) henv0 hva
              have hnoExt := symEnvNoOpaque_extend (ρ := ρ) (v := va)
                hsplit.2 hnoa
              have hbodyNone := evalSym_active_error_noOpaque_le (m := m)
                (fuel := n) (fuel' := n')
                (ρ := extendEnv ρ va) (env := env0.extend cva) (t := body)
                henvExt hnoExt (by
                  simpa [termNoOpaqueBuiltinsForSoundness] using hsplit.1)
                (by simpa [applySym] using hmem) herr hle'
              simp [applyVal, hbodyNone]
          | builtin b args ea =>
              cases hargs : symValListToCekList? m args <;>
                simp [symValToCek?, hargs] at hvf
              rename_i cargs
              subst cvf
              cases hea : ea.head <;> simp [applySym, hea] at hmem
              · cases htail : ea.tail with
                | some rest =>
                    cases out <;> simp [htail, ok, outcomeErrorActive] at hmem herr
                | none =>
                    have hargs' := symValListToCekList_cons (m := m)
                      (v := va) (vs := args) (cv := cva) (cvs := cargs) hva hargs
                    have hb := evalBuiltinSym_active_error (m := m) (b := b)
                      (args := va :: args) (cargs := cva :: cargs)
                      hargs' (by simpa [htail] using hmem) herr
                    simpa [applyVal, hea, htail] using hb
              · have hmemErr : out ∈ err := by
                    simpa [err] using hmem
                cases out <;> simp [err, outcomeErrorActive] at hmemErr herr
                simp [applyVal, hea]
          | const c =>
              cases out <;> simp [applySym, err, outcomeErrorActive] at hmem herr
              obtain ⟨k, rfl⟩ := symConstToCek_vcon (m := m)
                (by simpa [symValToCek?] using hvf)
              simp [applyVal]
          | dyn e =>
              cases out <;> simp [applySym, err, outcomeErrorActive] at hmem herr
              cases he : SmtSem.eval m e <;> simp [symValToCek?, he] at hvf
              rename_i sv
              cases sv <;> simp [symValToCek?, he] at hvf
              case val semv =>
                have hdec : semValToCek? semv = some cvf := by
                  simpa [symValToCek?, he] using hvf
                rcases semValToCek_con_or_constr hdec with hcon | hconstr
                · rcases hcon with ⟨c, rfl⟩
                  simp [applyVal]
                · rcases hconstr with ⟨tag, fields, rfl⟩
                  simp [applyVal]
          | pair a b =>
              cases out <;> simp [applySym, err, outcomeErrorActive] at hmem herr
              cases ha : symValToCek? m a <;> simp [symValToCek?, ha] at hvf
              rename_i ca
              cases hb : symValToCek? m b <;> simp [symValToCek?, ha, hb] at hvf
              rename_i cb
              cases ca <;> cases cb <;> simp at hvf
              subst cvf
              simp [applyVal]
          | constr tag fields =>
              cases out <;> simp [applySym, err, outcomeErrorActive] at hmem herr
              cases htag : SmtSem.eval m tag <;> simp [symValToCek?, htag] at hvf
              rename_i sv
              cases sv <;> simp [symValToCek?, htag] at hvf
              rename_i tagInt
              by_cases hneg : tagInt < 0
              · omega
              · cases hfields : symValListToCekList? m fields <;>
                  simp [hneg, hfields] at hvf
                rcases hvf with ⟨_, hcvf⟩
                subst cvf
                simp [applyVal]
          | delay body ρ =>
              cases out <;> simp [applySym, err, outcomeErrorActive] at hmem herr
              cases henv0 : symEnvToCek? m ρ <;>
                simp [symValToCek?, henv0] at hvf
              subst cvf
              simp [applyVal]

  theorem forceSym_active_error_noOpaque_le {m : SmtSem.Model} {fuel fuel' : Nat}
      {vt : SymVal} {cvt : CekValue} {out : Outcome}
      (hvt : symValToCek? m vt = some cvt)
      (hnot : symValNoOpaqueForSoundness vt = true)
      (hmem : out ∈ forceSym fuel vt)
      (herr : outcomeErrorActive m out = true)
      (hle : fuel ≤ fuel') :
      forceVal fuel' cvt = none := by
    cases fuel with
    | zero =>
        cases out <;> simp [forceSym, timeout, outcomeErrorActive] at hmem herr
    | succ n =>
        cases fuel' with
        | zero => omega
        | succ n' =>
          have hle' : n ≤ n' := by omega
          cases vt with
          | delay body ρ =>
              cases henv0 : symEnvToCek? m ρ <;>
                simp [symValToCek?, henv0] at hvt
              rename_i env0
              subst cvt
              have hsplit : termUsesOpaqueBuiltinForSoundness body = false ∧
                  symEnvNoOpaqueForSoundness ρ = true := by
                simpa [symValNoOpaqueForSoundness] using hnot
              have hbodyNone := evalSym_active_error_noOpaque_le (m := m)
                (fuel := n) (fuel' := n') (ρ := ρ) (env := env0) (t := body)
                henv0 hsplit.2 (by
                  simpa [termNoOpaqueBuiltinsForSoundness] using hsplit.1)
                (by simpa [forceSym] using hmem) herr hle'
              simp [forceVal, hbodyNone]
          | builtin b args ea =>
              cases hargs : symValListToCekList? m args <;>
                simp [symValToCek?, hargs] at hvt
              rename_i cargs
              subst cvt
              cases hea : ea.head <;> simp [forceSym, hea] at hmem
              · have hmemErr : out ∈ err := by
                    simpa [err] using hmem
                cases out <;> simp [err, outcomeErrorActive] at hmemErr herr
                simp [forceVal, hea]
              · cases htail : ea.tail with
                | some rest =>
                    cases out <;> simp [htail, ok, outcomeErrorActive] at hmem herr
                | none =>
                    have hb := evalBuiltinSym_active_error (m := m) (b := b)
                      (args := args) (cargs := cargs)
                      hargs (by simpa [htail] using hmem) herr
                    simpa [forceVal, hea, htail] using hb
          | const c =>
              cases out <;> simp [forceSym, err, outcomeErrorActive] at hmem herr
              obtain ⟨k, rfl⟩ := symConstToCek_vcon (m := m)
                (by simpa [symValToCek?] using hvt)
              simp [forceVal]
          | dyn e =>
              cases out <;> simp [forceSym, err, outcomeErrorActive] at hmem herr
              cases he : SmtSem.eval m e <;> simp [symValToCek?, he] at hvt
              rename_i sv
              cases sv <;> simp [symValToCek?, he] at hvt
              case val semv =>
                have hdec : semValToCek? semv = some cvt := by
                  simpa [symValToCek?, he] using hvt
                rcases semValToCek_con_or_constr hdec with hcon | hconstr
                · rcases hcon with ⟨c, rfl⟩
                  simp [forceVal]
                · rcases hconstr with ⟨tag, fields, rfl⟩
                  simp [forceVal]
          | pair a b =>
              cases out <;> simp [forceSym, err, outcomeErrorActive] at hmem herr
              cases ha : symValToCek? m a <;> simp [symValToCek?, ha] at hvt
              rename_i ca
              cases hb : symValToCek? m b <;> simp [symValToCek?, ha, hb] at hvt
              rename_i cb
              cases ca <;> cases cb <;> simp at hvt
              subst cvt
              simp [forceVal]
          | constr tag fields =>
              cases out <;> simp [forceSym, err, outcomeErrorActive] at hmem herr
              cases htag : SmtSem.eval m tag <;> simp [symValToCek?, htag] at hvt
              rename_i sv
              cases sv <;> simp [symValToCek?, htag] at hvt
              rename_i tagInt
              by_cases hneg : tagInt < 0
              · omega
              · cases hfields : symValListToCekList? m fields <;>
                  simp [hneg, hfields] at hvt
                rcases hvt with ⟨_, hcvt⟩
                subst cvt
                simp [forceVal]
          | lam body ρ =>
              cases out <;> simp [forceSym, err, outcomeErrorActive] at hmem herr
              cases henv0 : symEnvToCek? m ρ <;>
                simp [symValToCek?, henv0] at hvt
              subst cvt
              simp [forceVal]

  theorem applyListSym_active_error_noOpaque_le {m : SmtSem.Model} {fuel fuel' : Nat}
      {vf : SymVal} {args : List SymVal} {cvf : CekValue} {cargs : List CekValue}
      {out : Outcome}
      (hvf : symValToCek? m vf = some cvf)
      (hnof : symValNoOpaqueForSoundness vf = true)
      (hargs : symValListToCekList? m args = some cargs)
      (hnoArgs : symValsNoOpaqueForSoundness args = true)
      (hmem : out ∈ applyListSym fuel vf args)
      (herr : outcomeErrorActive m out = true)
      (hle : fuel ≤ fuel') :
      applyValList fuel' cvf cargs = none := by
    cases args with
    | nil =>
        simp [symValListToCekList?] at hargs
        subst cargs
        cases out <;> simp [applyListSym, ok, outcomeErrorActive] at hmem herr
    | cons a as =>
        cases ha : symValToCek? m a <;>
          simp [symValListToCekList?, ha] at hargs
        rename_i ca
        cases has : symValListToCekList? m as <;> simp [has] at hargs
        rename_i cas
        subst cargs
        have hnoSplit : symValNoOpaqueForSoundness a = true ∧
            symValsNoOpaqueForSoundness as = true := by
          simpa [symValsNoOpaqueForSoundness] using hnoArgs
        have hbind := bindOut_active_error (m := m)
          (xs := applySym fuel vf a)
          (k := fun vf' => applyListSym fuel vf' as)
          (hmem := by simpa [applyListSym] using hmem) herr
        rcases hbind with happErr | hrestErr
        · rcases happErr with ⟨pcApply, hmemApply, hpcApply⟩
          have happNone := applySym_active_error_noOpaque_le (m := m)
            (fuel := fuel) (fuel' := fuel') (vf := vf) (va := a)
            (cvf := cvf) (cva := ca)
            hvf hnof ha hnoSplit.1 hmemApply
            (by simpa [outcomeErrorActive] using hpcApply) hle
          simp [applyValList, happNone]
        · rcases hrestErr with
            ⟨pcApply, vf', inner, hmemApply, hpcApply, hmemRest, herrRest⟩
          have happ := applySym_path_ok (m := m) (fuel := fuel)
            (vf := vf) (va := a) (cvf := cvf) (cva := ca)
            hvf hnof ha hnoSplit.1 hmemApply hpcApply
          rcases happ with ⟨cvf', hvf', hnof', happVal⟩
          have happVal' := applyVal_mono_le hle happVal
          have hrestNone := applyListSym_active_error_noOpaque_le (m := m)
            (fuel := fuel) (fuel' := fuel') (vf := vf') (args := as)
            (cvf := cvf') (cargs := cas)
            hvf' hnof' has hnoSplit.2 hmemRest herrRest hle
          simp [applyValList, happVal', hrestNone]

  theorem applyValListSym_active_error_noOpaque_le {m : SmtSem.Model} {fuel fuel' : Nat}
      {vf : SymVal} {fieldsExpr : SExpr} {fields : List SmtSem.Val}
      {cvf : CekValue} {cfields : List CekValue} {out : Outcome}
      (hvf : symValToCek? m vf = some cvf)
      (hnof : symValNoOpaqueForSoundness vf = true)
      (hfieldsEval : SmtSem.eval m fieldsExpr = some (.valList fields))
      (hfields : semValListToCekList? fields = some cfields)
      (hmem : out ∈ applyValListSym fuel vf fieldsExpr)
      (herr : outcomeErrorActive m out = true)
      (hle : fuel ≤ fuel') :
      applyValList fuel' cvf cfields = none := by
    cases fuel with
    | zero =>
        cases out <;> simp [applyValListSym, timeout, outcomeErrorActive] at hmem herr
    | succ n =>
        cases fields with
        | nil =>
            simp [semValListToCekList?] at hfields
            subst cfields
            have hbranch := branchOutcomes_active_error (m := m)
              (hmem := by simpa [applyValListSym] using hmem) herr
            rcases hbranch with hbr | hextra
            · rcases hbr with ⟨g, os, inner, hbr, hg, hinner, hinnerErr⟩
              simp at hbr
              rcases hbr with hnil | hcons
              · rcases hnil with ⟨rfl, rfl⟩
                cases inner <;> simp [ok, outcomeErrorActive] at hinner hinnerErr
              · rcases hcons with ⟨rfl, rfl⟩
                have htrue :=
                  Moist.SMT.Semantics.evalBoolIs_isVNil_true_of_valList_nil hfieldsEval
                have hfalse := (Moist.SMT.Semantics.evalBoolIs_not_true m
                  (SExpr.isCtor "VNil" fieldsExpr)).mp hg
                exact False.elim (evalBoolIs_true_false_contra htrue hfalse)
            · rcases hextra with ⟨g, hgMem, hg⟩
              simp [branchOutcomes] at hgMem
        | cons field fieldsTail =>
            cases hfield : semValToCek? field <;>
              simp [semValListToCekList?, hfield] at hfields
            rename_i cfield
            cases htail : semValListToCekList? fieldsTail <;> simp [htail] at hfields
            rename_i ctail
            subst cfields
            have hbranch := branchOutcomes_active_error (m := m)
              (hmem := by simpa [applyValListSym] using hmem) herr
            rcases hbranch with hbr | hextra
            · rcases hbr with ⟨g, os, inner, hbr, hg, hinner, hinnerErr⟩
              simp at hbr
              rcases hbr with hnil | hcons
              · rcases hnil with ⟨rfl, rfl⟩
                have hfalse :=
                  Moist.SMT.Semantics.evalBoolIs_isVNil_false_of_valList_cons hfieldsEval
                exact False.elim (evalBoolIs_true_false_contra hg hfalse)
              · rcases hcons with ⟨rfl, rfl⟩
                have hheadEval :=
                  Moist.SMT.Semantics.eval_vhead_of (m := m) (e := fieldsExpr)
                    (h := field) (t := fieldsTail) hfieldsEval
                have htailEval :=
                  Moist.SMT.Semantics.eval_vtail_of (m := m) (e := fieldsExpr)
                    (h := field) (t := fieldsTail) hfieldsEval
                have hheadDecode :
                    symValToCek? m (.dyn (.app "vhead" [fieldsExpr])) = some cfield := by
                  simp [symValToCek?, hheadEval, hfield]
                have hbind := bindOut_active_error (m := m)
                  (xs := applySym n vf (.dyn (.app "vhead" [fieldsExpr])))
                  (k := fun vf' => applyValListSym n vf' (.app "vtail" [fieldsExpr]))
                  hinner hinnerErr
                rcases hbind with happErr | hrestErr
                · rcases happErr with ⟨pcApply, hmemApply, hpcApply⟩
                  have happNone := applySym_active_error_noOpaque_le (m := m)
                    (fuel := n) (fuel' := fuel') (vf := vf)
                    (va := .dyn (.app "vhead" [fieldsExpr]))
                    (cvf := cvf) (cva := cfield)
                    hvf hnof hheadDecode (by simp [symValNoOpaqueForSoundness])
                    hmemApply (by simpa [outcomeErrorActive] using hpcApply)
                    (by omega)
                  simp [applyValList, happNone]
                · rcases hrestErr with
                    ⟨pcApply, vf', innerRest, hmemApply, hpcApply, hmemRest, herrRest⟩
                  have happ := applySym_path_ok (m := m) (fuel := n)
                    (vf := vf) (va := .dyn (.app "vhead" [fieldsExpr]))
                    (cvf := cvf) (cva := cfield)
                    hvf hnof hheadDecode (by simp [symValNoOpaqueForSoundness])
                    hmemApply hpcApply
                  rcases happ with ⟨cvf', hvf', hnof', happVal⟩
                  have happVal' := applyVal_mono_le (by omega : n ≤ fuel') happVal
                  have hrec := applyValListSym_active_error_noOpaque_le (m := m)
                    (fuel := n) (fuel' := fuel') (vf := vf')
                    (fieldsExpr := .app "vtail" [fieldsExpr])
                    (fields := fieldsTail) (cvf := cvf') (cfields := ctail)
                    hvf' hnof' htailEval htail hmemRest herrRest (by omega)
                  simp [applyValList, happVal', hrec]
            · rcases hextra with ⟨g, hgMem, hg⟩
              simp [branchOutcomes] at hgMem

  theorem evalThenApplyListSym_active_error_noOpaque_le {m : SmtSem.Model}
      {fuel fuel' : Nat} {ρ : List SymVal} {env : CekEnv}
      {alt : Term} {args : List SymVal} {cargs : List CekValue} {out : Outcome}
      (henv : symEnvToCek? m ρ = some env)
      (hρno : symEnvNoOpaqueForSoundness ρ = true)
      (hnoAlt : termNoOpaqueBuiltinsForSoundness alt)
      (hargs : symValListToCekList? m args = some cargs)
      (hnoArgs : symValsNoOpaqueForSoundness args = true)
      (hmem : out ∈ bindOut (evalSym fuel ρ alt)
        (fun vAlt => applyListSym fuel vAlt args))
      (herr : outcomeErrorActive m out = true)
      (hle : fuel ≤ fuel') :
      (match bigEval fuel' env alt with
       | some vAlt => applyValList fuel' vAlt cargs
       | none => none) = none := by
    have hbind := bindOut_active_error (m := m)
      (xs := evalSym fuel ρ alt)
      (k := fun vAlt => applyListSym fuel vAlt args) hmem herr
    rcases hbind with haltErr | happErr
    · rcases haltErr with ⟨pcAlt, hmemAlt, hpcAlt⟩
      have hAltNone := evalSym_active_error_noOpaque_le (m := m)
        (fuel := fuel) (fuel' := fuel') (ρ := ρ) (env := env) (t := alt)
        henv hρno hnoAlt hmemAlt
        (by simpa [outcomeErrorActive] using hpcAlt) hle
      simp [hAltNone]
    · rcases happErr with
        ⟨pcAlt, vAlt, inner, hmemAlt, hpcAlt, hmemApply, herrApply⟩
      have halt := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
        (ρ := ρ) (env := env) (t := alt)
        henv hρno hnoAlt hmemAlt hpcAlt
      rcases halt with ⟨cvAlt, hvAlt, hnoVAlt, hbigAlt⟩
      have hbigAlt' := bigEval_mono_le hle hbigAlt
      have happNone := applyListSym_active_error_noOpaque_le (m := m)
        (fuel := fuel) (fuel' := fuel') (vf := vAlt) (args := args)
        (cvf := cvAlt) (cargs := cargs)
        hvAlt hnoVAlt hargs hnoArgs hmemApply herrApply hle
      simp [hbigAlt', happNone]

  theorem evalThenApplyValListSym_active_error_noOpaque_le {m : SmtSem.Model}
      {fuel fuel' : Nat} {ρ : List SymVal} {env : CekEnv}
      {alt : Term} {fieldsExpr : SExpr} {fields : List SmtSem.Val}
      {cfields : List CekValue} {out : Outcome}
      (henv : symEnvToCek? m ρ = some env)
      (hρno : symEnvNoOpaqueForSoundness ρ = true)
      (hnoAlt : termNoOpaqueBuiltinsForSoundness alt)
      (hfieldsEval : SmtSem.eval m fieldsExpr = some (.valList fields))
      (hfields : semValListToCekList? fields = some cfields)
      (hmem : out ∈ bindOut (evalSym fuel ρ alt)
        (fun vAlt => applyValListSym fuel vAlt fieldsExpr))
      (herr : outcomeErrorActive m out = true)
      (hle : fuel ≤ fuel') :
      (match bigEval fuel' env alt with
       | some vAlt => applyValList fuel' vAlt cfields
       | none => none) = none := by
    have hbind := bindOut_active_error (m := m)
      (xs := evalSym fuel ρ alt)
      (k := fun vAlt => applyValListSym fuel vAlt fieldsExpr) hmem herr
    rcases hbind with haltErr | happErr
    · rcases haltErr with ⟨pcAlt, hmemAlt, hpcAlt⟩
      have hAltNone := evalSym_active_error_noOpaque_le (m := m)
        (fuel := fuel) (fuel' := fuel') (ρ := ρ) (env := env) (t := alt)
        henv hρno hnoAlt hmemAlt
        (by simpa [outcomeErrorActive] using hpcAlt) hle
      simp [hAltNone]
    · rcases happErr with
        ⟨pcAlt, vAlt, inner, hmemAlt, hpcAlt, hmemApply, herrApply⟩
      have halt := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
        (ρ := ρ) (env := env) (t := alt)
        henv hρno hnoAlt hmemAlt hpcAlt
      rcases halt with ⟨cvAlt, hvAlt, hnoVAlt, hbigAlt⟩
      have hbigAlt' := bigEval_mono_le hle hbigAlt
      have happNone := applyValListSym_active_error_noOpaque_le (m := m)
        (fuel := fuel) (fuel' := fuel') (vf := vAlt)
        (fieldsExpr := fieldsExpr) (fields := fields)
        (cvf := cvAlt) (cfields := cfields)
        hvAlt hnoVAlt hfieldsEval hfields hmemApply herrApply hle
      simp [hbigAlt', happNone]

  theorem caseSym_active_error_noOpaque_le {m : SmtSem.Model} {fuel fuel' : Nat}
      {ρ : List SymVal} {env : CekEnv} {scrut : SymVal} {alts : List Term}
      {cscrut : CekValue} {out : Outcome}
      (henv : symEnvToCek? m ρ = some env)
      (hρno : symEnvNoOpaqueForSoundness ρ = true)
      (hnoAlts : termsUseOpaqueBuiltinForSoundness alts = false)
      (hscrut : symValToCek? m scrut = some cscrut)
      (hnoScrut : symValNoOpaqueForSoundness scrut = true)
      (hmem : out ∈ caseSym fuel ρ scrut alts)
      (herr : outcomeErrorActive m out = true)
      (hle : fuel ≤ fuel') :
      caseCekResult fuel' env cscrut alts = none := by
    cases scrut with
    | constr tag fields =>
        cases htagEval : SmtSem.eval m tag with
        | none => simp [symValToCek?, htagEval] at hscrut
        | some tagSv =>
          cases tagSv with
          | int tagInt =>
            by_cases hneg : tagInt < 0
            · simp [symValToCek?, htagEval, hneg] at hscrut
            · cases hfields : symValListToCekList? m fields with
              | none => simp [symValToCek?, htagEval, hneg, hfields] at hscrut
              | some cfields =>
                simp [symValToCek?, htagEval, hneg, hfields] at hscrut
                subst cscrut
                have hnoFields : symValsNoOpaqueForSoundness fields = true := by
                  simpa [symValNoOpaqueForSoundness] using hnoScrut
                have hbranch := branchOutcomes_active_error (m := m)
                  (hmem := by simpa [caseSym] using hmem) herr
                rcases hbranch with hbr | hextra
                · rcases hbr with ⟨g, os, inner, hbr, hg, hinner, hinnerErr⟩
                  simp only [List.mem_map] at hbr
                  rcases hbr with ⟨br, henum, hbrEq⟩
                  rcases br with ⟨i, alt⟩
                  simp at hbrEq
                  rcases hbrEq with ⟨rfl, rfl⟩
                  have hget : alts[i]? = some alt := enumerate_mem_get? henum
                  have htagEq : tagInt = Int.ofNat i :=
                    pcHolds_eq_int htagEval (by simp [Moist.SMT.Semantics.eval]) hg
                  have hnoAlt := termsNoOpaque_get? hnoAlts hget
                  have hnone := evalThenApplyListSym_active_error_noOpaque_le (m := m)
                    (fuel := fuel) (fuel' := fuel') (ρ := ρ) (env := env)
                    (alt := alt) (args := fields) (cargs := cfields)
                    henv hρno hnoAlt hfields hnoFields hinner hinnerErr hle
                  subst tagInt
                  simp [caseCekResult, hget, hnone]
                · rcases hextra with ⟨g, hgMem, hg⟩
                  simp [caseSym] at hgMem
                  subst g
                  cases hget : alts[tagInt.toNat]? with
                  | some alt =>
                    have htagNat : tagInt = Int.ofNat tagInt.toNat := by
                      exact (Int.toNat_of_nonneg (by omega : 0 ≤ tagInt)).symm
                    have hcovered := tagCovered_true_of_get (m := m)
                      (alts := alts) (tagExpr := tag) (tagInt := tagInt)
                      (i := tagInt.toNat) (alt := alt) htagEval htagNat hget
                    have hnot := (Moist.SMT.Semantics.evalBoolIs_not_true m
                      (SExpr.any ((enumerate alts).map fun (j, _) =>
                        SExpr.eq tag (.int (Int.ofNat j))))).mp
                        (by simpa [pcHolds] using hg)
                    exact False.elim (evalBoolIs_true_false_contra hcovered hnot)
                  | none =>
                    simp [caseCekResult, hget]
          | bool b => simp [symValToCek?, htagEval] at hscrut
          | string s => simp [symValToCek?, htagEval] at hscrut
          | bytes bs => simp [symValToCek?, htagEval] at hscrut
          | data d => simp [symValToCek?, htagEval] at hscrut
          | dataList xs => simp [symValToCek?, htagEval] at hscrut
          | dataPairList xs => simp [symValToCek?, htagEval] at hscrut
          | val val => simp [symValToCek?, htagEval] at hscrut
          | valList xs => simp [symValToCek?, htagEval] at hscrut
          | g1 g => simp [symValToCek?, htagEval] at hscrut
          | g2 g => simp [symValToCek?, htagEval] at hscrut
          | ml r => simp [symValToCek?, htagEval] at hscrut
    | lam body ρ0 =>
        cases out <;> simp [caseSym, err, outcomeErrorActive] at hmem herr
        cases henv0 : symEnvToCek? m ρ0 <;>
          simp [symValToCek?, henv0] at hscrut
        subst cscrut
        simp [caseCekResult]
    | delay body ρ0 =>
        cases out <;> simp [caseSym, err, outcomeErrorActive] at hmem herr
        cases henv0 : symEnvToCek? m ρ0 <;>
          simp [symValToCek?, henv0] at hscrut
        subst cscrut
        simp [caseCekResult]
    | builtin b args ea =>
        cases out <;> simp [caseSym, err, outcomeErrorActive] at hmem herr
        cases hargs : symValListToCekList? m args <;>
          simp [symValToCek?, hargs] at hscrut
        subst cscrut
        simp [caseCekResult]
    | pair a b =>
        cases ha : symValToCek? m a <;> simp [symValToCek?, ha] at hscrut
        rename_i ca
        cases hb : symValToCek? m b <;> simp [hb] at hscrut
        rename_i cb
        cases ca with
        | VCon caConst =>
          cases cb with
          | VCon cbConst =>
            simp at hscrut
            subst cscrut
            by_cases hlen : alts.length > 1
            · cases out <;> simp [caseSym, hlen, err, outcomeErrorActive] at hmem herr
              simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen]
            · cases hget : alts[0]? with
              | none =>
                  cases out <;> simp [caseSym, hlen, hget, err, outcomeErrorActive] at hmem herr
                  simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen, hget]
              | some alt =>
                  have hnoAlt := termsNoOpaque_get? hnoAlts hget
                  have hargs :
                      symValListToCekList? m [a, b] =
                        some [.VCon caConst, .VCon cbConst] := by
                    simp [symValListToCekList?, ha, hb]
                  have hnoArgs :
                      symValsNoOpaqueForSoundness [a, b] = true := by
                    simpa [symValNoOpaqueForSoundness, symValsNoOpaqueForSoundness]
                      using hnoScrut
                  have hnone := evalThenApplyListSym_active_error_noOpaque_le (m := m)
                    (fuel := fuel) (fuel' := fuel') (ρ := ρ) (env := env)
                    (alt := alt) (args := [a, b])
                    (cargs := [.VCon caConst, .VCon cbConst])
                    henv hρno hnoAlt hargs hnoArgs
                    (by simpa [caseSym, hlen, hget] using hmem) herr hle
                  simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen, hget, hnone]
          | VLam body env0 => simp at hscrut
          | VDelay body env0 => simp at hscrut
          | VBuiltin b cargs ea => simp at hscrut
          | VConstr tag fields => simp at hscrut
        | VLam body env0 => cases cb <;> simp at hscrut
        | VDelay body env0 => cases cb <;> simp at hscrut
        | VBuiltin b cargs ea => cases cb <;> simp at hscrut
        | VConstr tag fields => cases cb <;> simp at hscrut
    | const c =>
        cases c with
        | bool be =>
            cases he : SmtSem.eval m be with
            | none => simp [symValToCek?, symConstToCek?, he] at hscrut
            | some sv =>
              cases sv with
              | bool bval =>
                simp [symValToCek?, symConstToCek?, he] at hscrut
                subst cscrut
                by_cases hlen : alts.length > 2
                · cases out <;> simp [caseSym, hlen, err, outcomeErrorActive] at hmem herr
                  cases bval <;>
                    simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen]
                · have hbranch := branchOutcomes_active_error (m := m)
                    (hmem := by simpa [caseSym, hlen] using hmem) herr
                  rcases hbranch with hbr | hextra
                  · rcases hbr with ⟨g, os, inner, hbr, hg, hinner, hinnerErr⟩
                    simp only [List.mem_map] at hbr
                    rcases hbr with ⟨br, henum, hbrEq⟩
                    rcases br with ⟨i, alt⟩
                    simp at hbrEq
                    rcases hbrEq with ⟨rfl, rfl⟩
                    have hget : alts[i]? = some alt := enumerate_mem_get? henum
                    have htagEval :
                        SmtSem.eval m (SExpr.ite be (.int 1) (.int 0)) =
                          some (.int (if bval then 1 else 0)) := by
                      change SmtSem.eval m (Expr.ite be (.int 1) (.int 0)) =
                        some (.int (if bval then 1 else 0))
                      rw [eval_ite_of_bool (m := m) (c := be)
                        (t := .int 1) (e := .int 0) he]
                      cases bval <;> simp [Moist.SMT.Semantics.eval]
                    have htagEq :
                        (if bval then (1 : Int) else 0) = Int.ofNat i :=
                      pcHolds_eq_int htagEval
                        (by simp [Moist.SMT.Semantics.eval]) hg
                    have hnoAlt := termsNoOpaque_get? hnoAlts hget
                    have hAltNone := evalSym_active_error_noOpaque_le (m := m)
                      (fuel := fuel) (fuel' := fuel') (ρ := ρ) (env := env)
                      (t := alt) henv hρno hnoAlt hinner hinnerErr hle
                    cases bval
                    · have hi0 : i = 0 := intOfNat_eq_zero htagEq
                      subst i
                      simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen,
                        hget, hAltNone, applyValList]
                    · have hi1 : i = 1 := intOfNat_eq_one htagEq
                      subst i
                      simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen,
                        hget, hAltNone, applyValList]
                  · rcases hextra with ⟨g, hgMem, hg⟩
                    simp [caseSym, hlen] at hgMem
                    subst g
                    let tag := SExpr.ite be (.int 1) (.int 0)
                    cases hget : alts[(if bval then 1 else 0)]? with
                    | some alt =>
                      have htagEval :
                          SmtSem.eval m tag =
                            some (.int (if bval then 1 else 0)) := by
                        change SmtSem.eval m (Expr.ite be (.int 1) (.int 0)) =
                          some (.int (if bval then 1 else 0))
                        rw [eval_ite_of_bool (m := m) (c := be)
                          (t := .int 1) (e := .int 0) he]
                        cases bval <;> simp [Moist.SMT.Semantics.eval]
                      have hcovered := tagCovered_true_of_get (m := m)
                        (alts := alts) (tagExpr := tag)
                        (tagInt := (if bval then 1 else 0)) (i := (if bval then 1 else 0))
                        (alt := alt) htagEval (by cases bval <;> simp) hget
                      have hnot := (Moist.SMT.Semantics.evalBoolIs_not_true m
                        (SExpr.any ((enumerate alts).map fun (j, _) =>
                          SExpr.eq tag (.int (Int.ofNat j))))).mp
                          (by simpa [pcHolds] using hg)
                      exact False.elim (evalBoolIs_true_false_contra hcovered hnot)
                    | none =>
                      cases bval
                      · simp at hget
                        subst alts
                        simp [caseCekResult, Moist.CEK.constToTagAndFields]
                      · have hget1 : alts[1]? = none := by
                          cases alts with
                          | nil => simp
                          | cons a rest =>
                            cases rest with
                            | nil => simp
                            | cons b rest =>
                              simp at hget
                        simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen, hget1]
              | int i => simp [symValToCek?, symConstToCek?, he] at hscrut
              | string s => simp [symValToCek?, symConstToCek?, he] at hscrut
              | bytes bs => simp [symValToCek?, symConstToCek?, he] at hscrut
              | data d => simp [symValToCek?, symConstToCek?, he] at hscrut
              | dataList xs => simp [symValToCek?, symConstToCek?, he] at hscrut
              | dataPairList xs => simp [symValToCek?, symConstToCek?, he] at hscrut
              | val val => simp [symValToCek?, symConstToCek?, he] at hscrut
              | valList xs => simp [symValToCek?, symConstToCek?, he] at hscrut
              | g1 g => simp [symValToCek?, symConstToCek?, he] at hscrut
              | g2 g => simp [symValToCek?, symConstToCek?, he] at hscrut
              | ml r => simp [symValToCek?, symConstToCek?, he] at hscrut
        | unit =>
            simp [symValToCek?, symConstToCek?] at hscrut
            subst cscrut
            by_cases hlen : alts.length > 1
            · cases out <;> simp [caseSym, hlen, err, outcomeErrorActive] at hmem herr
              simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen]
            · cases hget : alts[0]? with
              | none =>
                  cases out <;> simp [caseSym, hlen, hget, err, outcomeErrorActive] at hmem herr
                  simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen, hget]
              | some alt =>
                  have hnoAlt := termsNoOpaque_get? hnoAlts hget
                  have hAltNone := evalSym_active_error_noOpaque_le (m := m)
                    (fuel := fuel) (fuel' := fuel') (ρ := ρ) (env := env)
                    (t := alt) henv hρno hnoAlt
                    (by simpa [caseSym, hlen, hget] using hmem) herr hle
                  simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen, hget,
                    hAltNone, applyValList]
        | integer ie =>
            cases he : SmtSem.eval m ie with
            | none => simp [symValToCek?, symConstToCek?, he] at hscrut
            | some sv =>
              cases sv with
              | int ival =>
                simp [symValToCek?, symConstToCek?, he] at hscrut
                subst cscrut
                have hbranch := branchOutcomes_active_error (m := m)
                  (hmem := by simpa [caseSym] using hmem) herr
                rcases hbranch with hbr | hextra
                · rcases hbr with ⟨g, os, inner, hbr, hg, hinner, hinnerErr⟩
                  simp only [List.mem_map] at hbr
                  rcases hbr with ⟨br, henum, hbrEq⟩
                  rcases br with ⟨i, alt⟩
                  simp at hbrEq
                  rcases hbrEq with ⟨rfl, rfl⟩
                  have hparts :=
                    (Moist.SMT.Semantics.evalBoolIs_and_true m
                      (nonnegGuard ie) (SExpr.eq ie (.int (Int.ofNat i)))).mp hg
                  have hnonneg : 0 ≤ ival := pcHolds_nonneg he hparts.1
                  have htagEq : ival = Int.ofNat i :=
                    pcHolds_eq_int he (by simp [Moist.SMT.Semantics.eval]) hparts.2
                  have hget : alts[i]? = some alt := enumerate_mem_get? henum
                  have hnoAlt := termsNoOpaque_get? hnoAlts hget
                  have hAltNone := evalSym_active_error_noOpaque_le (m := m)
                    (fuel := fuel) (fuel' := fuel') (ρ := ρ) (env := env)
                    (t := alt) henv hρno hnoAlt hinner hinnerErr hle
                  subst ival
                  simp [caseCekResult, Moist.CEK.constToTagAndFields, hget,
                    hAltNone, applyValList]
                · rcases hextra with ⟨g, hgMem, hg⟩
                  simp [caseSym] at hgMem
                  subst g
                  by_cases hnonneg : 0 ≤ ival
                  · cases hget : alts[ival.toNat]? with
                    | some alt =>
                      have htagNat : ival = Int.ofNat ival.toNat := by
                        exact (Int.toNat_of_nonneg hnonneg).symm
                      have hcovered := tagCovered_true_of_get (m := m)
                        (alts := alts) (tagExpr := ie) (tagInt := ival)
                        (i := ival.toNat) (alt := alt) he htagNat hget
                      have hnonnegPc : pcHolds m (nonnegGuard ie) = true := by
                        have hgeEval := Moist.SMT.Semantics.eval_ge_of (m := m)
                          (a := ie) (b := .int 0) (x := ival) (y := 0) he
                          (by simp [Moist.SMT.Semantics.eval])
                        have hgeEvalTrue :
                            Moist.SMT.Semantics.eval m (Expr.ge ie (.int 0)) =
                              some (.bool true) := by
                          rw [hgeEval]
                          simp [hnonneg]
                        have hbool : SmtSem.eval m (nonnegGuard ie) =
                            some (.bool true) := by
                          simpa [SmtSem.eval, nonnegGuard] using hgeEvalTrue
                        exact (Moist.SMT.Semantics.evalBoolIs_true_eq m
                          (nonnegGuard ie)).mpr hbool
                      let covered : SExpr :=
                        SExpr.any ((enumerate alts).map fun (j, _) =>
                          SExpr.eq ie (.int (Int.ofNat j)))
                      have hcoveredAnd :
                          pcHolds m (SExpr.and (nonnegGuard ie)
                            (SExpr.any ((enumerate alts).map fun (j, _) =>
                              SExpr.eq ie (.int (Int.ofNat j))))) = true := by
                        have hcoveredAndEval :
                            Moist.SMT.Semantics.evalBoolIs m
                              (SExpr.and (nonnegGuard ie) covered) true = true :=
                          (Moist.SMT.Semantics.evalBoolIs_and_true m
                            (nonnegGuard ie) covered).mpr
                            ⟨by simpa [pcHolds] using hnonnegPc,
                              by simpa [covered, pcHolds] using hcovered⟩
                        simpa [covered, pcHolds] using
                          hcoveredAndEval
                      have hnot := (Moist.SMT.Semantics.evalBoolIs_not_true m
                        (SExpr.and (nonnegGuard ie) covered)).mp
                            (by simpa [covered, pcHolds] using hg)
                      exact False.elim (evalBoolIs_true_false_contra hcoveredAnd hnot)
                    | none =>
                      simp [caseCekResult, Moist.CEK.constToTagAndFields, hnonneg, hget]
                  · have hlt : ival < 0 := by omega
                    simp [caseCekResult, Moist.CEK.constToTagAndFields, hnonneg]
              | bool b => simp [symValToCek?, symConstToCek?, he] at hscrut
              | string s => simp [symValToCek?, symConstToCek?, he] at hscrut
              | bytes bs => simp [symValToCek?, symConstToCek?, he] at hscrut
              | data d => simp [symValToCek?, symConstToCek?, he] at hscrut
              | dataList xs => simp [symValToCek?, symConstToCek?, he] at hscrut
              | dataPairList xs => simp [symValToCek?, symConstToCek?, he] at hscrut
              | val val => simp [symValToCek?, symConstToCek?, he] at hscrut
              | valList xs => simp [symValToCek?, symConstToCek?, he] at hscrut
              | g1 g => simp [symValToCek?, symConstToCek?, he] at hscrut
              | g2 g => simp [symValToCek?, symConstToCek?, he] at hscrut
              | ml r => simp [symValToCek?, symConstToCek?, he] at hscrut
        | bytes bs =>
            cases out <;> simp [caseSym, err, outcomeErrorActive] at hmem herr
            cases hbs : SmtSem.eval m bs with
            | none => simp [symValToCek?, symConstToCek?, hbs] at hscrut
            | some sv =>
              cases sv <;> simp [symValToCek?, symConstToCek?, hbs] at hscrut
              subst cscrut
              simp [caseCekResult, Moist.CEK.constToTagAndFields]
        | string s =>
            cases out <;> simp [caseSym, err, outcomeErrorActive] at hmem herr
            cases hs : SmtSem.eval m s with
            | none => simp [symValToCek?, symConstToCek?, hs] at hscrut
            | some sv =>
              cases sv <;> simp [symValToCek?, symConstToCek?, hs] at hscrut
              subst cscrut
              simp [caseCekResult, Moist.CEK.constToTagAndFields]
        | pairDataList xs =>
            cases out <;> simp [caseSym, err, outcomeErrorActive] at hmem herr
            cases hxs : SmtSem.eval m xs with
            | none => simp [symValToCek?, symConstToCek?, hxs] at hscrut
            | some sv =>
              cases sv <;> simp [symValToCek?, symConstToCek?, hxs] at hscrut
              subst cscrut
              simp [caseCekResult, Moist.CEK.constToTagAndFields]
        | data d =>
            cases out <;> simp [caseSym, err, outcomeErrorActive] at hmem herr
            cases hd : SmtSem.eval m d with
            | none => simp [symValToCek?, symConstToCek?, hd] at hscrut
            | some sv =>
              cases sv <;> simp [symValToCek?, symConstToCek?, hd] at hscrut
              subst cscrut
              simp [caseCekResult, Moist.CEK.constToTagAndFields]
        | array xs =>
            cases out <;> simp [caseSym, err, outcomeErrorActive] at hmem herr
            cases hxs : SmtSem.eval m xs with
            | none => simp [symValToCek?, symConstToCek?, hxs] at hscrut
            | some sv =>
              cases sv <;> simp [symValToCek?, symConstToCek?, hxs] at hscrut
              rename_i vals
              cases hconsts : semValListToConstList? vals <;>
                simp [symValToCek?, symConstToCek?, hxs, hconsts] at hscrut
              subst cscrut
              simp [caseCekResult, Moist.CEK.constToTagAndFields]
        | g1 g =>
            cases out <;> simp [caseSym, err, outcomeErrorActive] at hmem herr
            simp [symValToCek?, symConstToCek?] at hscrut
            cases hg : SmtSem.eval m g <;> simp [hg] at hscrut
            rename_i sv
            cases sv <;> simp [hg] at hscrut
            subst cscrut
            simp [caseCekResult, Moist.CEK.constToTagAndFields]
        | g2 g =>
            cases out <;> simp [caseSym, err, outcomeErrorActive] at hmem herr
            simp [symValToCek?, symConstToCek?] at hscrut
            cases hg : SmtSem.eval m g <;> simp [hg] at hscrut
            rename_i sv
            cases sv <;> simp [hg] at hscrut
            subst cscrut
            simp [caseCekResult, Moist.CEK.constToTagAndFields]
        | ml r =>
            cases out <;> simp [caseSym, err, outcomeErrorActive] at hmem herr
            simp [symValToCek?, symConstToCek?] at hscrut
            cases hr : SmtSem.eval m r <;> simp [hr] at hscrut
            rename_i sv
            cases sv <;> simp [hr] at hscrut
            subst cscrut
            simp [caseCekResult, Moist.CEK.constToTagAndFields]
        | constList xs =>
            cases hxs : SmtSem.eval m xs with
            | none => simp [symValToCek?, symConstToCek?, hxs] at hscrut
            | some sv =>
              cases sv with
              | valList vals =>
                cases hconsts : semValListToConstList? vals with
                | none => simp [symValToCek?, symConstToCek?, hxs, hconsts] at hscrut
                | some consts =>
                  simp [symValToCek?, symConstToCek?, hxs, hconsts] at hscrut
                  subst cscrut
                  by_cases hlen : alts.length > 2
                  · cases out <;> simp [caseSym, hlen, err, outcomeErrorActive] at hmem herr
                    cases consts <;>
                      simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen]
                  · have hbranch := branchOutcomes_active_error (m := m)
                      (hmem := by simpa [caseSym, hlen] using hmem) herr
                    cases vals with
                    | nil =>
                      simp [semValListToConstList?] at hconsts
                      subst consts
                      cases h0 : alts[0]? with
                      | none =>
                        cases h1 : alts[1]? with
                        | none =>
                          simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen, h1]
                        | some nilAlt =>
                          rcases hbranch with hbr | hextra
                          · rcases hbr with ⟨g, os, inner, hbr, hg, hinner, hinnerErr⟩
                            simp [caseSym, hlen, h0, h1] at hbr
                            rcases hbr with ⟨rfl, rfl⟩
                            have hnoAlt := termsNoOpaque_get? hnoAlts h1
                            have hAltNone := evalSym_active_error_noOpaque_le (m := m)
                              (fuel := fuel) (fuel' := fuel') (ρ := ρ) (env := env)
                              (t := nilAlt) henv hρno hnoAlt hinner hinnerErr hle
                            simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen,
                              h1, hAltNone, applyValList]
                          · rcases hextra with ⟨g, hgMem, hg⟩
                            simp [caseSym, hlen, h0, h1] at hgMem
                            subst g
                            have hnil :=
                              Moist.SMT.Semantics.evalBoolIs_isVNil_true_of_valList_nil hxs
                            have hnot :=
                              (Moist.SMT.Semantics.evalBoolIs_not_true m
                                (SExpr.isCtor "VNil" xs)).mp
                                (by simpa [pcHolds] using hg)
                            exact False.elim (evalBoolIs_true_false_contra hnil hnot)
                      | some consAlt =>
                        cases h1 : alts[1]? with
                        | none =>
                          simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen, h1]
                        | some nilAlt =>
                          rcases hbranch with hbr | hextra
                          · rcases hbr with ⟨g, os, inner, hbr, hg, hinner, hinnerErr⟩
                            simp [caseSym, hlen, h0, h1] at hbr
                            rcases hbr with hcons | hnilBranch
                            · rcases hcons with ⟨rfl, rfl⟩
                              have hnil :=
                                Moist.SMT.Semantics.evalBoolIs_isVNil_true_of_valList_nil hxs
                              have hnot :=
                                (Moist.SMT.Semantics.evalBoolIs_not_true m
                                  (SExpr.isCtor "VNil" xs)).mp
                                  (by simpa [pcHolds] using hg)
                              exact False.elim (evalBoolIs_true_false_contra hnil hnot)
                            · rcases hnilBranch with ⟨rfl, rfl⟩
                              have hnoAlt := termsNoOpaque_get? hnoAlts h1
                              have hAltNone := evalSym_active_error_noOpaque_le (m := m)
                                (fuel := fuel) (fuel' := fuel') (ρ := ρ) (env := env)
                                (t := nilAlt) henv hρno hnoAlt hinner hinnerErr hle
                              simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen,
                                h1, hAltNone, applyValList]
                          · rcases hextra with ⟨g, hgMem, hg⟩
                            simp [caseSym, hlen, h0, h1] at hgMem
                            subst g
                            have hnil :=
                              Moist.SMT.Semantics.evalBoolIs_isVNil_true_of_valList_nil hxs
                            have hcovered : pcHolds m (SExpr.any
                                (List.map Prod.fst
                                  ([(SExpr.not (SExpr.isCtor "VNil" xs),
                                      bindOut (evalSym fuel ρ consAlt) fun vAlt =>
                                        applyListSym fuel vAlt
                                          [fieldFromValList xs, tailFromValList xs])] ++
                                    [(SExpr.isCtor "VNil" xs, evalSym fuel ρ nilAlt)]))) = true := by
                              let a := SExpr.isCtor "VNil" xs
                              have ha : SmtSem.eval m a = some (.bool true) :=
                                (Moist.SMT.Semantics.evalBoolIs_true_eq m a).mp
                                  (by simpa [a] using hnil)
                              have hna : SmtSem.eval m (SExpr.not a) = some (.bool false) := by
                                simpa using eval_not_of_bool (m := m) (e := a) (b := true) ha
                              have hor := evalBoolIs_or_true_of_right (m := m)
                                (a := SExpr.not a) (b := a) ⟨false, hna⟩ ha
                              simpa [a, SExpr.any, Moist.SMT.Expr.any, pcHolds] using hor
                            have hnot := (Moist.SMT.Semantics.evalBoolIs_not_true m
                                (SExpr.any
                                  (List.map Prod.fst
                                    ([(SExpr.not (SExpr.isCtor "VNil" xs),
                                        bindOut (evalSym fuel ρ consAlt) fun vAlt =>
                                          applyListSym fuel vAlt
                                            [fieldFromValList xs, tailFromValList xs])] ++
                                      [(SExpr.isCtor "VNil" xs, evalSym fuel ρ nilAlt)])))).mp
                                  (by simpa [pcHolds] using hg)
                            exact False.elim (evalBoolIs_true_false_contra hcovered hnot)
                    | cons head tail =>
                      cases hheadConst : semValToConst? head with
                      | none => simp [semValListToConstList?, hheadConst] at hconsts
                      | some headConst =>
                        cases htailConst : semValListToConstList? tail with
                        | none =>
                          simp [semValListToConstList?, hheadConst, htailConst] at hconsts
                        | some tailConst =>
                          simp [semValListToConstList?, hheadConst, htailConst] at hconsts
                          subst consts
                          cases h0 : alts[0]? with
                          | none =>
                            simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen, h0]
                          | some consAlt =>
                            have hheadEval :=
                              Moist.SMT.Semantics.eval_vhead_of (m := m) (e := xs)
                                (h := head) (t := tail) hxs
                            have htailEval :=
                              Moist.SMT.Semantics.eval_vtail_of (m := m) (e := xs)
                                (h := head) (t := tail) hxs
                            have hargs :
                                symValListToCekList? m
                                    [fieldFromValList xs, tailFromValList xs] =
                                  some [.VCon headConst, .VCon (.ConstList tailConst)] := by
                              have hheadCek := semValToCek_of_const hheadConst
                              simp [fieldFromValList, tailFromValList, symValListToCekList?,
                                symValToCek?, symConstToCek?, hheadEval, htailEval,
                                hheadCek, htailConst]
                            have hnoArgs :
                                symValsNoOpaqueForSoundness
                                    [fieldFromValList xs, tailFromValList xs] = true := by
                              simp [fieldFromValList, tailFromValList,
                                symValsNoOpaqueForSoundness, symValNoOpaqueForSoundness]
                            rcases hbranch with hbr | hextra
                            · rcases hbr with ⟨g, os, inner, hbr, hg, hinner, hinnerErr⟩
                              cases h1 : alts[1]? with
                              | none =>
                                simp [caseSym, hlen, h0, h1] at hbr
                                rcases hbr with ⟨rfl, rfl⟩
                                have hnoAlt := termsNoOpaque_get? hnoAlts h0
                                have hnone := evalThenApplyListSym_active_error_noOpaque_le
                                  (m := m) (fuel := fuel) (fuel' := fuel') (ρ := ρ)
                                  (env := env) (alt := consAlt)
                                  (args := [fieldFromValList xs, tailFromValList xs])
                                  (cargs := [.VCon headConst, .VCon (.ConstList tailConst)])
                                  henv hρno hnoAlt hargs hnoArgs hinner hinnerErr hle
                                simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen,
                                  h0, hnone]
                              | some nilAlt =>
                                simp [caseSym, hlen, h0, h1] at hbr
                                rcases hbr with hcons | hnilBranch
                                · rcases hcons with ⟨rfl, rfl⟩
                                  have hnoAlt := termsNoOpaque_get? hnoAlts h0
                                  have hnone := evalThenApplyListSym_active_error_noOpaque_le
                                    (m := m) (fuel := fuel) (fuel' := fuel') (ρ := ρ)
                                    (env := env) (alt := consAlt)
                                    (args := [fieldFromValList xs, tailFromValList xs])
                                    (cargs := [.VCon headConst, .VCon (.ConstList tailConst)])
                                    henv hρno hnoAlt hargs hnoArgs hinner hinnerErr hle
                                  simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen,
                                    h0, hnone]
                                · rcases hnilBranch with ⟨rfl, rfl⟩
                                  have hfalse :=
                                    Moist.SMT.Semantics.evalBoolIs_isVNil_false_of_valList_cons hxs
                                  exact False.elim (evalBoolIs_true_false_contra hg hfalse)
                            · rcases hextra with ⟨g, hgMem, hg⟩
                              cases h1 : alts[1]? with
                              | none =>
                                simp [caseSym, hlen, h0, h1] at hgMem
                                subst g
                                have hfalse :=
                                  Moist.SMT.Semantics.evalBoolIs_isVNil_false_of_valList_cons hxs
                                have hnotnot :
                                    pcHolds m (SExpr.not (SExpr.isCtor "VNil" xs)) = true :=
                                  (Moist.SMT.Semantics.evalBoolIs_not_true m
                                    (SExpr.isCtor "VNil" xs)).mpr hfalse
                                have hnot := (Moist.SMT.Semantics.evalBoolIs_not_true m
                                    (SExpr.not (SExpr.isCtor "VNil" xs))).mp
                                    (by simpa [pcHolds] using hg)
                                exact False.elim (evalBoolIs_true_false_contra hnotnot hnot)
                              | some nilAlt =>
                                simp [caseSym, hlen, h0, h1] at hgMem
                                subst g
                                have hfalse :=
                                  Moist.SMT.Semantics.evalBoolIs_isVNil_false_of_valList_cons hxs
                                have hnotnot :
                                    pcHolds m (SExpr.not (SExpr.isCtor "VNil" xs)) = true :=
                                  (Moist.SMT.Semantics.evalBoolIs_not_true m
                                    (SExpr.isCtor "VNil" xs)).mpr hfalse
                                have hcovered : pcHolds m (SExpr.any
                                    (List.map Prod.fst
                                      ([(SExpr.not (SExpr.isCtor "VNil" xs),
                                          bindOut (evalSym fuel ρ consAlt) fun vAlt =>
                                            applyListSym fuel vAlt
                                              [fieldFromValList xs, tailFromValList xs])] ++
                                        [(SExpr.isCtor "VNil" xs, evalSym fuel ρ nilAlt)]))) = true := by
                                  let a := SExpr.isCtor "VNil" xs
                                  have hna : SmtSem.eval m (SExpr.not a) = some (.bool true) :=
                                    (Moist.SMT.Semantics.evalBoolIs_true_eq m
                                      (SExpr.not a)).mp (by simpa [a, pcHolds] using hnotnot)
                                  have hor := evalBoolIs_or_true_of_left (m := m)
                                    (a := SExpr.not a) (b := a) hna
                                    (evalBoolIs_has_bool_eval (m := m) (e := a) (b := false)
                                      (by simpa [a] using hfalse))
                                  simpa [a, SExpr.any, Moist.SMT.Expr.any, pcHolds] using hor
                                have hnot := (Moist.SMT.Semantics.evalBoolIs_not_true m
                                    (SExpr.any
                                      (List.map Prod.fst
                                        ([(SExpr.not (SExpr.isCtor "VNil" xs),
                                            bindOut (evalSym fuel ρ consAlt) fun vAlt =>
                                              applyListSym fuel vAlt
                                                [fieldFromValList xs, tailFromValList xs])] ++
                                          [(SExpr.isCtor "VNil" xs, evalSym fuel ρ nilAlt)])))).mp
                                      (by simpa [pcHolds] using hg)
                                exact False.elim (evalBoolIs_true_false_contra hcovered hnot)
              | bool b => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | int i => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | string s => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | bytes bs => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | data d => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | dataList xs' => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | dataPairList xs' => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | val val => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | g1 g => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | g2 g => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | ml r => simp [symValToCek?, symConstToCek?, hxs] at hscrut
        | dataList xs =>
            cases hxs : SmtSem.eval m xs with
            | none => simp [symValToCek?, symConstToCek?, hxs] at hscrut
            | some sv =>
              cases sv with
              | dataList vals =>
                simp [symValToCek?, symConstToCek?, hxs] at hscrut
                subst cscrut
                by_cases hlen : alts.length > 2
                · cases out <;> simp [caseSym, hlen, err, outcomeErrorActive] at hmem herr
                  cases vals <;>
                    simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen]
                · have hbranch := branchOutcomes_active_error (m := m)
                    (hmem := by simpa [caseSym, hlen] using hmem) herr
                  cases vals with
                  | nil =>
                    cases h0 : alts[0]? with
                    | none =>
                      cases h1 : alts[1]? with
                      | none =>
                        simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen, h1]
                      | some nilAlt =>
                        rcases hbranch with hbr | hextra
                        · rcases hbr with ⟨g, os, inner, hbr, hg, hinner, hinnerErr⟩
                          simp [caseSym, hlen, h0, h1] at hbr
                          rcases hbr with ⟨rfl, rfl⟩
                          have hnoAlt := termsNoOpaque_get? hnoAlts h1
                          have hAltNone := evalSym_active_error_noOpaque_le (m := m)
                            (fuel := fuel) (fuel' := fuel') (ρ := ρ) (env := env)
                            (t := nilAlt) henv hρno hnoAlt hinner hinnerErr hle
                          simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen,
                            h1, hAltNone, applyValList]
                        · rcases hextra with ⟨g, hgMem, hg⟩
                          simp [caseSym, hlen, h0, h1] at hgMem
                          subst g
                          have hnil :=
                            Moist.SMT.Semantics.evalBoolIs_isDNil_true_of_dataList_nil hxs
                          have hnot :=
                            (Moist.SMT.Semantics.evalBoolIs_not_true m
                              (SExpr.isCtor "DNil" xs)).mp
                              (by simpa [pcHolds] using hg)
                          exact False.elim (evalBoolIs_true_false_contra hnil hnot)
                    | some consAlt =>
                      cases h1 : alts[1]? with
                      | none =>
                        simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen, h1]
                      | some nilAlt =>
                        rcases hbranch with hbr | hextra
                        · rcases hbr with ⟨g, os, inner, hbr, hg, hinner, hinnerErr⟩
                          simp [caseSym, hlen, h0, h1] at hbr
                          rcases hbr with hcons | hnilBranch
                          · rcases hcons with ⟨rfl, rfl⟩
                            have hnil :=
                              Moist.SMT.Semantics.evalBoolIs_isDNil_true_of_dataList_nil hxs
                            have hnot :=
                              (Moist.SMT.Semantics.evalBoolIs_not_true m
                                (SExpr.isCtor "DNil" xs)).mp
                                (by simpa [pcHolds] using hg)
                            exact False.elim (evalBoolIs_true_false_contra hnil hnot)
                          · rcases hnilBranch with ⟨rfl, rfl⟩
                            have hnoAlt := termsNoOpaque_get? hnoAlts h1
                            have hAltNone := evalSym_active_error_noOpaque_le (m := m)
                              (fuel := fuel) (fuel' := fuel') (ρ := ρ) (env := env)
                              (t := nilAlt) henv hρno hnoAlt hinner hinnerErr hle
                            simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen,
                              h1, hAltNone, applyValList]
                        · rcases hextra with ⟨g, hgMem, hg⟩
                          simp [caseSym, hlen, h0, h1] at hgMem
                          subst g
                          have hnil :=
                            Moist.SMT.Semantics.evalBoolIs_isDNil_true_of_dataList_nil hxs
                          have hcovered : pcHolds m (SExpr.any
                              (List.map Prod.fst
                                ([(SExpr.not (SExpr.isCtor "DNil" xs),
                                    bindOut (evalSym fuel ρ consAlt) fun vAlt =>
                                      applyListSym fuel vAlt
                                        [fieldFromDataList xs, tailFromDataList xs])] ++
                                  [(SExpr.isCtor "DNil" xs, evalSym fuel ρ nilAlt)]))) = true := by
                            let a := SExpr.isCtor "DNil" xs
                            have ha : SmtSem.eval m a = some (.bool true) :=
                              (Moist.SMT.Semantics.evalBoolIs_true_eq m a).mp
                                (by simpa [a] using hnil)
                            have hna : SmtSem.eval m (SExpr.not a) = some (.bool false) := by
                              simpa using eval_not_of_bool (m := m) (e := a) (b := true) ha
                            have hor := evalBoolIs_or_true_of_right (m := m)
                              (a := SExpr.not a) (b := a) ⟨false, hna⟩ ha
                            simpa [a, SExpr.any, Moist.SMT.Expr.any, pcHolds] using hor
                          have hnot := (Moist.SMT.Semantics.evalBoolIs_not_true m
                              (SExpr.any
                                (List.map Prod.fst
                                  ([(SExpr.not (SExpr.isCtor "DNil" xs),
                                      bindOut (evalSym fuel ρ consAlt) fun vAlt =>
                                        applyListSym fuel vAlt
                                          [fieldFromDataList xs, tailFromDataList xs])] ++
                                    [(SExpr.isCtor "DNil" xs, evalSym fuel ρ nilAlt)])))).mp
                                (by simpa [pcHolds] using hg)
                          exact False.elim (evalBoolIs_true_false_contra hcovered hnot)
                  | cons head tail =>
                    cases h0 : alts[0]? with
                    | none =>
                      simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen, h0]
                    | some consAlt =>
                      have hheadEval :=
                        Moist.SMT.Semantics.eval_dhead_of (m := m) (e := xs)
                          (h := head) (t := tail) hxs
                      have htailEval :=
                        Moist.SMT.Semantics.eval_dtail_of (m := m) (e := xs)
                          (h := head) (t := tail) hxs
                      have hargs :
                          symValListToCekList? m
                              [fieldFromDataList xs, tailFromDataList xs] =
                            some [.VCon (.Data head), .VCon (.ConstDataList tail)] := by
                        simp [fieldFromDataList, tailFromDataList, symValListToCekList?,
                          symValToCek?, symConstToCek?, hheadEval, htailEval]
                      have hnoArgs :
                          symValsNoOpaqueForSoundness
                              [fieldFromDataList xs, tailFromDataList xs] = true := by
                        simp [fieldFromDataList, tailFromDataList,
                          symValsNoOpaqueForSoundness, symValNoOpaqueForSoundness]
                      rcases hbranch with hbr | hextra
                      · rcases hbr with ⟨g, os, inner, hbr, hg, hinner, hinnerErr⟩
                        cases h1 : alts[1]? with
                        | none =>
                          simp [caseSym, hlen, h0, h1] at hbr
                          rcases hbr with ⟨rfl, rfl⟩
                          have hnoAlt := termsNoOpaque_get? hnoAlts h0
                          have hnone := evalThenApplyListSym_active_error_noOpaque_le
                            (m := m) (fuel := fuel) (fuel' := fuel') (ρ := ρ)
                            (env := env) (alt := consAlt)
                            (args := [fieldFromDataList xs, tailFromDataList xs])
                            (cargs := [.VCon (.Data head), .VCon (.ConstDataList tail)])
                            henv hρno hnoAlt hargs hnoArgs hinner hinnerErr hle
                          simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen,
                            h0, hnone]
                        | some nilAlt =>
                          simp [caseSym, hlen, h0, h1] at hbr
                          rcases hbr with hcons | hnilBranch
                          · rcases hcons with ⟨rfl, rfl⟩
                            have hnoAlt := termsNoOpaque_get? hnoAlts h0
                            have hnone := evalThenApplyListSym_active_error_noOpaque_le
                              (m := m) (fuel := fuel) (fuel' := fuel') (ρ := ρ)
                              (env := env) (alt := consAlt)
                              (args := [fieldFromDataList xs, tailFromDataList xs])
                              (cargs := [.VCon (.Data head), .VCon (.ConstDataList tail)])
                              henv hρno hnoAlt hargs hnoArgs hinner hinnerErr hle
                            simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen,
                              h0, hnone]
                          · rcases hnilBranch with ⟨rfl, rfl⟩
                            have hfalse :=
                              Moist.SMT.Semantics.evalBoolIs_isDNil_false_of_dataList_cons hxs
                            exact False.elim (evalBoolIs_true_false_contra hg hfalse)
                      · rcases hextra with ⟨g, hgMem, hg⟩
                        cases h1 : alts[1]? with
                        | none =>
                          simp [caseSym, hlen, h0, h1] at hgMem
                          subst g
                          have hfalse :=
                            Moist.SMT.Semantics.evalBoolIs_isDNil_false_of_dataList_cons hxs
                          have hnotnot :
                              pcHolds m (SExpr.not (SExpr.isCtor "DNil" xs)) = true :=
                            (Moist.SMT.Semantics.evalBoolIs_not_true m
                              (SExpr.isCtor "DNil" xs)).mpr hfalse
                          have hnot := (Moist.SMT.Semantics.evalBoolIs_not_true m
                              (SExpr.not (SExpr.isCtor "DNil" xs))).mp
                              (by simpa [pcHolds] using hg)
                          exact False.elim (evalBoolIs_true_false_contra hnotnot hnot)
                        | some nilAlt =>
                          simp [caseSym, hlen, h0, h1] at hgMem
                          subst g
                          have hfalse :=
                            Moist.SMT.Semantics.evalBoolIs_isDNil_false_of_dataList_cons hxs
                          have hnotnot :
                              pcHolds m (SExpr.not (SExpr.isCtor "DNil" xs)) = true :=
                            (Moist.SMT.Semantics.evalBoolIs_not_true m
                              (SExpr.isCtor "DNil" xs)).mpr hfalse
                          have hcovered : pcHolds m (SExpr.any
                              (List.map Prod.fst
                                ([(SExpr.not (SExpr.isCtor "DNil" xs),
                                    bindOut (evalSym fuel ρ consAlt) fun vAlt =>
                                      applyListSym fuel vAlt
                                        [fieldFromDataList xs, tailFromDataList xs])] ++
                                  [(SExpr.isCtor "DNil" xs, evalSym fuel ρ nilAlt)]))) = true := by
                            let a := SExpr.isCtor "DNil" xs
                            have hna : SmtSem.eval m (SExpr.not a) = some (.bool true) :=
                              (Moist.SMT.Semantics.evalBoolIs_true_eq m
                                (SExpr.not a)).mp (by simpa [a, pcHolds] using hnotnot)
                            have hor := evalBoolIs_or_true_of_left (m := m)
                              (a := SExpr.not a) (b := a) hna
                              (evalBoolIs_has_bool_eval (m := m) (e := a) (b := false)
                                (by simpa [a] using hfalse))
                            simpa [a, SExpr.any, Moist.SMT.Expr.any, pcHolds] using hor
                          have hnot := (Moist.SMT.Semantics.evalBoolIs_not_true m
                              (SExpr.any
                                (List.map Prod.fst
                                  ([(SExpr.not (SExpr.isCtor "DNil" xs),
                                      bindOut (evalSym fuel ρ consAlt) fun vAlt =>
                                        applyListSym fuel vAlt
                                          [fieldFromDataList xs, tailFromDataList xs])] ++
                                    [(SExpr.isCtor "DNil" xs, evalSym fuel ρ nilAlt)])))).mp
                                (by simpa [pcHolds] using hg)
                          exact False.elim (evalBoolIs_true_false_contra hcovered hnot)
              | bool b => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | int i => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | string s => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | bytes bs => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | data d => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | dataPairList xs' => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | val val => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | valList xs' => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | g1 g => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | g2 g => simp [symValToCek?, symConstToCek?, hxs] at hscrut
              | ml r => simp [symValToCek?, symConstToCek?, hxs] at hscrut
        | pairData a b =>
            cases ha : SmtSem.eval m a with
            | none => simp [symValToCek?, symConstToCek?, ha] at hscrut
            | some sva =>
              cases hb : SmtSem.eval m b with
              | none => simp [symValToCek?, symConstToCek?, ha, hb] at hscrut
              | some svb =>
                cases sva <;> cases svb <;>
                  simp [symValToCek?, symConstToCek?, ha, hb] at hscrut
                rename_i da db
                subst cscrut
                by_cases hlen : alts.length > 1
                · cases out <;> simp [caseSym, hlen, err, outcomeErrorActive] at hmem herr
                  simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen]
                · cases hget : alts[0]? with
                  | none =>
                      cases out <;>
                        simp [caseSym, hlen, hget, err, outcomeErrorActive] at hmem herr
                      simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen, hget]
                  | some alt =>
                    have hnoAlt := termsNoOpaque_get? hnoAlts hget
                    have hargs :
                        symValListToCekList? m [.const (.data a), .const (.data b)] =
                          some [.VCon (.Data da), .VCon (.Data db)] := by
                      simp [symValListToCekList?, symValToCek?, symConstToCek?, ha, hb]
                    have hnoArgs :
                        symValsNoOpaqueForSoundness [.const (.data a), .const (.data b)] =
                          true := by
                      simp [symValsNoOpaqueForSoundness, symValNoOpaqueForSoundness]
                    have hnone := evalThenApplyListSym_active_error_noOpaque_le (m := m)
                      (fuel := fuel) (fuel' := fuel') (ρ := ρ) (env := env)
                      (alt := alt) (args := [.const (.data a), .const (.data b)])
                      (cargs := [.VCon (.Data da), .VCon (.Data db)])
                      henv hρno hnoAlt hargs hnoArgs
                      (by simpa [caseSym, hlen, hget] using hmem) herr hle
                    simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen, hget, hnone]
    | dyn e =>
        cases he : SmtSem.eval m e with
        | none => simp [symValToCek?, he] at hscrut
        | some sv =>
          change Moist.SMT.Semantics.eval m e = some sv at he
          cases sv with
          | val semv =>
            have hbranch := branchOutcomes_active_error (m := m)
              (hmem := by simpa [caseSym] using hmem) herr
            rcases hbranch with hbr | hextra
            · rcases hbr with ⟨g, os, inner, hbr, hg, hinner, hinnerErr⟩
              simp [caseSym] at hbr
              rcases hbr with hbool | hrest
              · rcases hbool with ⟨hlen, i, alt, henum, hgEq, hosEq⟩
                subst g
                subst os
                have hparts := pcHolds_all2 (m := m) hg
                obtain ⟨bval, heBool⟩ :=
                  Moist.SMT.Semantics.evalBoolIs_isVBool_true hparts.1
                rw [he] at heBool
                injection heBool with hsv
                injection hsv with hsemv
                subst semv
                simp [symValToCek?, semValToCek?, semValToConst?, he] at hscrut
                subst cscrut
                have hboolTagEval :
                    SmtSem.eval m (SExpr.ite (.app "unVBool" [e]) (.int 1) (.int 0)) =
                      some (.int (if bval then 1 else 0)) := by
                  have hun := Moist.SMT.Semantics.eval_unVBool_of (m := m) (e := e) he
                  change SmtSem.eval m (Expr.ite (.app "unVBool" [e]) (.int 1) (.int 0)) =
                    some (.int (if bval then 1 else 0))
                  rw [eval_ite_of_bool (m := m) (c := .app "unVBool" [e])
                    (t := .int 1) (e := .int 0) hun]
                  cases bval <;> simp [Moist.SMT.Semantics.eval]
                have htagEq :
                    (if bval then (1 : Int) else 0) = Int.ofNat i :=
                  pcHolds_eq_int hboolTagEval
                    (by simp [Moist.SMT.Semantics.eval]) hparts.2
                have hget : alts[i]? = some alt := enumerate_mem_get? henum
                have hnoAlt := termsNoOpaque_get? hnoAlts hget
                have hAltNone := evalSym_active_error_noOpaque_le (m := m)
                  (fuel := fuel) (fuel' := fuel') (ρ := ρ) (env := env)
                  (t := alt) henv hρno hnoAlt hinner hinnerErr hle
                cases bval
                · have hi0 : i = 0 := intOfNat_eq_zero htagEq
                  subst i
                  simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen,
                    hget, hAltNone, applyValList]
                · have hi1 : i = 1 := intOfNat_eq_one htagEq
                  subst i
                  simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen,
                    hget, hAltNone, applyValList]
              · rcases hrest with hunit | hrest
                · rcases hunit with ⟨hlen, hunitMem⟩
                  cases h0 : alts[0]? with
                  | none => simp [h0] at hunitMem
                  | some alt =>
                    simp [h0] at hunitMem
                    rcases hunitMem with ⟨rfl, rfl⟩
                    have heUnit := Moist.SMT.Semantics.evalBoolIs_isVUnit_true hg
                    rw [he] at heUnit
                    injection heUnit with hsv
                    injection hsv with hsemv
                    subst semv
                    simp [symValToCek?, semValToCek?, semValToConst?, he] at hscrut
                    subst cscrut
                    have hnoAlt := termsNoOpaque_get? hnoAlts h0
                    have hAltNone := evalSym_active_error_noOpaque_le (m := m)
                      (fuel := fuel) (fuel' := fuel') (ρ := ρ) (env := env)
                      (t := alt) henv hρno hnoAlt hinner hinnerErr hle
                    simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen,
                      h0, hAltNone, applyValList]
                · rcases hrest with hint | hrest
                  · rcases hint with ⟨i, alt, henum, hgEq, hosEq⟩
                    subst g
                    subst os
                    have hparts := pcHolds_all3 (m := m) hg
                    obtain ⟨ival, heInt⟩ :=
                      Moist.SMT.Semantics.evalBoolIs_isVInt_true hparts.1
                    rw [he] at heInt
                    injection heInt with hsv
                    injection hsv with hsemv
                    subst semv
                    simp [symValToCek?, semValToCek?, semValToConst?, he] at hscrut
                    subst cscrut
                    have hun := Moist.SMT.Semantics.eval_unVInt_of (m := m) (e := e) he
                    have hnonneg : 0 ≤ ival := pcHolds_nonneg hun hparts.2.1
                    have htagEq : ival = Int.ofNat i :=
                      pcHolds_eq_int hun (by simp [Moist.SMT.Semantics.eval])
                        hparts.2.2
                    have hget : alts[i]? = some alt := enumerate_mem_get? henum
                    have hnoAlt := termsNoOpaque_get? hnoAlts hget
                    have hAltNone := evalSym_active_error_noOpaque_le (m := m)
                      (fuel := fuel) (fuel' := fuel') (ρ := ρ) (env := env)
                      (t := alt) henv hρno hnoAlt hinner hinnerErr hle
                    subst ival
                    simp [caseCekResult, Moist.CEK.constToTagAndFields, hget,
                      hAltNone, applyValList]
                  · rcases hrest with hlist | hrest
                    · rcases hlist with ⟨hlen, hlistMem⟩
                      rcases hlistMem with hcons | hnil
                      · cases h0 : alts[0]? with
                        | none => simp [h0] at hcons
                        | some consAlt =>
                          simp [h0] at hcons
                          rcases hcons with ⟨rfl, rfl⟩
                          have hparts := pcHolds_all2 (m := m) hg
                          obtain ⟨xs, heList⟩ :=
                            Moist.SMT.Semantics.evalBoolIs_isVList_true hparts.1
                          rw [he] at heList
                          injection heList with hsv
                          injection hsv with hsemv
                          subst semv
                          have hxs := Moist.SMT.Semantics.eval_unVList_of (m := m)
                            (e := e) he
                          cases xs with
                          | nil =>
                            have hnil :=
                              Moist.SMT.Semantics.evalBoolIs_isVNil_true_of_valList_nil hxs
                            have hnot :=
                              (Moist.SMT.Semantics.evalBoolIs_not_true m
                                (SExpr.isCtor "VNil" (.app "unVList" [e]))).mp hparts.2
                            exact False.elim (evalBoolIs_true_false_contra hnil hnot)
                          | cons head tail =>
                            cases hheadConst : semValToConst? head with
                            | none =>
                              simp [symValToCek?, semValToCek?, semValToConst?,
                                semValListToConstList?, he, hheadConst] at hscrut
                            | some headConst =>
                              cases htailConst : semValListToConstList? tail with
                              | none =>
                                simp [symValToCek?, semValToCek?, semValToConst?,
                                  semValListToConstList?, he, hheadConst, htailConst] at hscrut
                              | some tailConst =>
                                simp [symValToCek?, semValToCek?, semValToConst?,
                                  semValListToConstList?, he, hheadConst, htailConst] at hscrut
                                subst cscrut
                                have hheadEval :=
                                  Moist.SMT.Semantics.eval_vhead_of (m := m)
                                    (e := .app "unVList" [e]) (h := head) (t := tail) hxs
                                have htailEval :=
                                  Moist.SMT.Semantics.eval_vtail_of (m := m)
                                    (e := .app "unVList" [e]) (h := head) (t := tail) hxs
                                have hargs :
                                    symValListToCekList? m
                                        [fieldFromValList (.app "unVList" [e]),
                                          tailFromValList (.app "unVList" [e])] =
                                      some [.VCon headConst, .VCon (.ConstList tailConst)] := by
                                  have hheadCek := semValToCek_of_const hheadConst
                                  simp [fieldFromValList, tailFromValList,
                                    symValListToCekList?, symValToCek?, symConstToCek?,
                                    hheadEval, htailEval, hheadCek, htailConst]
                                have hnoArgs :
                                    symValsNoOpaqueForSoundness
                                        [fieldFromValList (.app "unVList" [e]),
                                          tailFromValList (.app "unVList" [e])] = true := by
                                  simp [fieldFromValList, tailFromValList,
                                    symValsNoOpaqueForSoundness, symValNoOpaqueForSoundness]
                                have hnoAlt := termsNoOpaque_get? hnoAlts h0
                                have hnone := evalThenApplyListSym_active_error_noOpaque_le
                                  (m := m) (fuel := fuel) (fuel' := fuel') (ρ := ρ)
                                  (env := env) (alt := consAlt)
                                  (args := [fieldFromValList (.app "unVList" [e]),
                                    tailFromValList (.app "unVList" [e])])
                                  (cargs := [.VCon headConst, .VCon (.ConstList tailConst)])
                                  henv hρno hnoAlt hargs hnoArgs hinner hinnerErr hle
                                simp [caseCekResult, Moist.CEK.constToTagAndFields,
                                  hlen, h0, hnone]
                      · cases h1 : alts[1]? with
                        | none => simp [h1] at hnil
                        | some nilAlt =>
                          simp [h1] at hnil
                          rcases hnil with ⟨rfl, rfl⟩
                          have hparts := pcHolds_all2 (m := m) hg
                          obtain ⟨xs, heList⟩ :=
                            Moist.SMT.Semantics.evalBoolIs_isVList_true hparts.1
                          rw [he] at heList
                          injection heList with hsv
                          injection hsv with hsemv
                          subst semv
                          have hxs := Moist.SMT.Semantics.eval_unVList_of (m := m)
                            (e := e) he
                          cases xs with
                          | nil =>
                            simp [symValToCek?, semValToCek?, semValToConst?,
                              semValListToConstList?, he] at hscrut
                            subst cscrut
                            have hnoAlt := termsNoOpaque_get? hnoAlts h1
                            have hAltNone := evalSym_active_error_noOpaque_le (m := m)
                              (fuel := fuel) (fuel' := fuel') (ρ := ρ) (env := env)
                              (t := nilAlt) henv hρno hnoAlt hinner hinnerErr hle
                            simp [caseCekResult, Moist.CEK.constToTagAndFields,
                              hlen, h1, hAltNone, applyValList]
                          | cons head tail =>
                            have hfalse :=
                              Moist.SMT.Semantics.evalBoolIs_isVNil_false_of_valList_cons hxs
                            exact False.elim (evalBoolIs_true_false_contra hparts.2 hfalse)
                    · rcases hrest with hdataList | hrest
                      · rcases hdataList with ⟨hlen, hdataMem⟩
                        rcases hdataMem with hcons | hnil
                        · cases h0 : alts[0]? with
                          | none => simp [h0] at hcons
                          | some consAlt =>
                            simp [h0] at hcons
                            rcases hcons with ⟨rfl, rfl⟩
                            have hparts := pcHolds_all2 (m := m) hg
                            obtain ⟨xs, heDataList⟩ :=
                              Moist.SMT.Semantics.evalBoolIs_isVDataList_true hparts.1
                            rw [he] at heDataList
                            injection heDataList with hsv
                            injection hsv with hsemv
                            subst semv
                            have hxs := Moist.SMT.Semantics.eval_unVDataList_of (m := m)
                              (e := e) he
                            cases xs with
                            | nil =>
                              have hnil :=
                                Moist.SMT.Semantics.evalBoolIs_isDNil_true_of_dataList_nil hxs
                              have hnot :=
                                (Moist.SMT.Semantics.evalBoolIs_not_true m
                                  (SExpr.isCtor "DNil" (.app "unVDataList" [e]))).mp hparts.2
                              exact False.elim (evalBoolIs_true_false_contra hnil hnot)
                            | cons head tail =>
                              simp [symValToCek?, semValToCek?, semValToConst?, he] at hscrut
                              subst cscrut
                              have hheadEval :=
                                Moist.SMT.Semantics.eval_dhead_of (m := m)
                                  (e := .app "unVDataList" [e]) (h := head) (t := tail) hxs
                              have htailEval :=
                                Moist.SMT.Semantics.eval_dtail_of (m := m)
                                  (e := .app "unVDataList" [e]) (h := head) (t := tail) hxs
                              have hargs :
                                  symValListToCekList? m
                                      [fieldFromDataList (.app "unVDataList" [e]),
                                        tailFromDataList (.app "unVDataList" [e])] =
                                    some [.VCon (.Data head), .VCon (.ConstDataList tail)] := by
                                simp [fieldFromDataList, tailFromDataList,
                                  symValListToCekList?, symValToCek?, symConstToCek?,
                                  hheadEval, htailEval]
                              have hnoArgs :
                                  symValsNoOpaqueForSoundness
                                      [fieldFromDataList (.app "unVDataList" [e]),
                                        tailFromDataList (.app "unVDataList" [e])] = true := by
                                simp [fieldFromDataList, tailFromDataList,
                                  symValsNoOpaqueForSoundness, symValNoOpaqueForSoundness]
                              have hnoAlt := termsNoOpaque_get? hnoAlts h0
                              have hnone := evalThenApplyListSym_active_error_noOpaque_le
                                (m := m) (fuel := fuel) (fuel' := fuel') (ρ := ρ)
                                (env := env) (alt := consAlt)
                                (args := [fieldFromDataList (.app "unVDataList" [e]),
                                  tailFromDataList (.app "unVDataList" [e])])
                                (cargs := [.VCon (.Data head), .VCon (.ConstDataList tail)])
                                henv hρno hnoAlt hargs hnoArgs hinner hinnerErr hle
                              simp [caseCekResult, Moist.CEK.constToTagAndFields,
                                hlen, h0, hnone]
                        · cases h1 : alts[1]? with
                          | none => simp [h1] at hnil
                          | some nilAlt =>
                            simp [h1] at hnil
                            rcases hnil with ⟨rfl, rfl⟩
                            have hparts := pcHolds_all2 (m := m) hg
                            obtain ⟨xs, heDataList⟩ :=
                              Moist.SMT.Semantics.evalBoolIs_isVDataList_true hparts.1
                            rw [he] at heDataList
                            injection heDataList with hsv
                            injection hsv with hsemv
                            subst semv
                            have hxs := Moist.SMT.Semantics.eval_unVDataList_of (m := m)
                              (e := e) he
                            cases xs with
                            | nil =>
                              simp [symValToCek?, semValToCek?, semValToConst?, he] at hscrut
                              subst cscrut
                              have hnoAlt := termsNoOpaque_get? hnoAlts h1
                              have hAltNone := evalSym_active_error_noOpaque_le (m := m)
                                (fuel := fuel) (fuel' := fuel') (ρ := ρ) (env := env)
                                (t := nilAlt) henv hρno hnoAlt hinner hinnerErr hle
                              simp [caseCekResult, Moist.CEK.constToTagAndFields,
                                hlen, h1, hAltNone, applyValList]
                            | cons head tail =>
                              have hfalse :=
                                Moist.SMT.Semantics.evalBoolIs_isDNil_false_of_dataList_cons hxs
                              exact False.elim (evalBoolIs_true_false_contra hparts.2 hfalse)
                      · rcases hrest with hpair | hrest
                        · rcases hpair with ⟨hlen, hpairMem⟩
                          cases h0 : alts[0]? with
                          | none => simp [h0] at hpairMem
                          | some alt =>
                            simp [h0] at hpairMem
                            rcases hpairMem with ⟨rfl, rfl⟩
                            obtain ⟨a, b, hePair⟩ :=
                              Moist.SMT.Semantics.evalBoolIs_isVPair_true hg
                            rw [he] at hePair
                            injection hePair with hsv
                            injection hsv with hsemv
                            subst semv
                            cases haConst : semValToConst? a with
                            | none =>
                              simp [symValToCek?, semValToCek?, semValToConst?, he,
                                haConst] at hscrut
                            | some ca =>
                              cases hbConst : semValToConst? b with
                              | none =>
                                simp [symValToCek?, semValToCek?, semValToConst?, he,
                                  haConst, hbConst] at hscrut
                              | some cb =>
                                simp [symValToCek?, semValToCek?, semValToConst?, he,
                                  haConst, hbConst] at hscrut
                                subst cscrut
                                have hvfst :=
                                  Moist.SMT.Semantics.eval_vfst_of (m := m) (e := e)
                                    (a := a) (b := b) he
                                have hvsnd :=
                                  Moist.SMT.Semantics.eval_vsnd_of (m := m) (e := e)
                                    (a := a) (b := b) he
                                have hargs :
                                    symValListToCekList? m
                                        [.dyn (.app "vfst" [e]), .dyn (.app "vsnd" [e])] =
                                      some [.VCon ca, .VCon cb] := by
                                  have haCek := semValToCek_of_const haConst
                                  have hbCek := semValToCek_of_const hbConst
                                  simp [symValListToCekList?, symValToCek?, hvfst, hvsnd,
                                    haCek, hbCek]
                                have hnoArgs :
                                    symValsNoOpaqueForSoundness
                                        [.dyn (.app "vfst" [e]), .dyn (.app "vsnd" [e])] =
                                      true := by
                                  simp [symValsNoOpaqueForSoundness, symValNoOpaqueForSoundness]
                                have hnoAlt := termsNoOpaque_get? hnoAlts h0
                                have hnone := evalThenApplyListSym_active_error_noOpaque_le
                                  (m := m) (fuel := fuel) (fuel' := fuel') (ρ := ρ)
                                  (env := env) (alt := alt)
                                  (args := [.dyn (.app "vfst" [e]), .dyn (.app "vsnd" [e])])
                                  (cargs := [.VCon ca, .VCon cb])
                                  henv hρno hnoAlt hargs hnoArgs hinner hinnerErr hle
                                simp [caseCekResult, Moist.CEK.constToTagAndFields,
                                  hlen, h0, hnone]
                        · rcases hrest with hpairData | hconstr
                          · rcases hpairData with ⟨hlen, hpairDataMem⟩
                            cases h0 : alts[0]? with
                            | none => simp [h0] at hpairDataMem
                            | some alt =>
                              simp [h0] at hpairDataMem
                              rcases hpairDataMem with ⟨rfl, rfl⟩
                              obtain ⟨a, b, hePairData⟩ :=
                                Moist.SMT.Semantics.evalBoolIs_isVPairData_true hg
                              rw [he] at hePairData
                              injection hePairData with hsv
                              injection hsv with hsemv
                              subst semv
                              simp [symValToCek?, semValToCek?, semValToConst?, he] at hscrut
                              subst cscrut
                              have hfst :=
                                Moist.SMT.Semantics.eval_pdfst_of (m := m) (e := e)
                                  (a := a) (b := b) he
                              have hsnd :=
                                Moist.SMT.Semantics.eval_pdsnd_of (m := m) (e := e)
                                  (a := a) (b := b) he
                              have hargs :
                                  symValListToCekList? m
                                      [.const (.data (.app "pdfst" [e])),
                                        .const (.data (.app "pdsnd" [e]))] =
                                    some [.VCon (.Data a), .VCon (.Data b)] := by
                                simp [symValListToCekList?, symValToCek?, symConstToCek?,
                                  hfst, hsnd]
                              have hnoArgs :
                                  symValsNoOpaqueForSoundness
                                      [.const (.data (.app "pdfst" [e])),
                                        .const (.data (.app "pdsnd" [e]))] = true := by
                                simp [symValsNoOpaqueForSoundness, symValNoOpaqueForSoundness]
                              have hnoAlt := termsNoOpaque_get? hnoAlts h0
                              have hnone := evalThenApplyListSym_active_error_noOpaque_le
                                (m := m) (fuel := fuel) (fuel' := fuel') (ρ := ρ)
                                (env := env) (alt := alt)
                                (args := [.const (.data (.app "pdfst" [e])),
                                  .const (.data (.app "pdsnd" [e]))])
                                (cargs := [.VCon (.Data a), .VCon (.Data b)])
                                henv hρno hnoAlt hargs hnoArgs hinner hinnerErr hle
                              simp [caseCekResult, Moist.CEK.constToTagAndFields,
                                hlen, h0, hnone]
                          · rcases hconstr with ⟨i, alt, henum, hgEq, hosEq⟩
                            subst g
                            subst os
                            have hparts := pcHolds_all2 (m := m) hg
                            obtain ⟨tag, fields, heConstr⟩ :=
                              Moist.SMT.Semantics.evalBoolIs_isVConstr_true hparts.1
                            rw [he] at heConstr
                            injection heConstr with hsv
                            injection hsv with hsemv
                            subst semv
                            by_cases hneg : tag < 0
                            · simp [symValToCek?, semValToCek?, he, hneg] at hscrut
                            · cases hfields : semValListToCekList? fields with
                              | none =>
                                simp [symValToCek?, semValToCek?, he, hneg, hfields] at hscrut
                              | some cfields =>
                                simp [symValToCek?, semValToCek?, he, hneg, hfields] at hscrut
                                subst cscrut
                                have htagEval :=
                                  Moist.SMT.Semantics.eval_vConstrTag_of (m := m)
                                    (e := e) (tag := tag) (fields := fields) he
                                have hfieldsEval :=
                                  Moist.SMT.Semantics.eval_vConstrFields_of (m := m)
                                    (e := e) (tag := tag) (fields := fields) he
                                have htagEq : tag = Int.ofNat i :=
                                  pcHolds_eq_int htagEval
                                    (by simp [Moist.SMT.Semantics.eval]) hparts.2
                                have hget : alts[i]? = some alt := enumerate_mem_get? henum
                                have hnoAlt := termsNoOpaque_get? hnoAlts hget
                                have hnone := evalThenApplyValListSym_active_error_noOpaque_le
                                  (m := m) (fuel := fuel) (fuel' := fuel') (ρ := ρ)
                                  (env := env) (alt := alt)
                                  (fieldsExpr := .app "vConstrFields" [e])
                                  (fields := fields) (cfields := cfields)
                                  henv hρno hnoAlt hfieldsEval hfields hinner hinnerErr hle
                                subst tag
                                simp [caseCekResult, hget, hnone]
            · rcases hextra with ⟨g, hgMem, hg⟩
              simp only [List.mem_cons, List.mem_singleton] at hgMem
              cases semv with
              | bool bval =>
                simp [symValToCek?, semValToCek?, semValToConst?, he] at hscrut
                subst cscrut
                rcases hgMem with hboolErr | hrest
                · rw [hboolErr] at hg
                  by_cases hlen : 2 < alts.length
                  · have htoo : 0 < 2 ∧ 2 < alts.length := ⟨by decide, hlen⟩
                    cases bval <;>
                      simp [caseCekResult, Moist.CEK.constToTagAndFields, htoo]
                  · have hparts :=
                    (Moist.SMT.Semantics.evalBoolIs_and_true m
                      (SExpr.isCtor "VBool" e)
                      (SExpr.not (SExpr.any ((enumerate alts).map fun (j, _) =>
                        SExpr.eq (SExpr.ite (.app "unVBool" [e]) (.int 1) (.int 0))
                          (.int (Int.ofNat j)))))).mp
                      (by simpa [hlen, pcHolds] using hg)
                    let tag := SExpr.ite (.app "unVBool" [e]) (.int 1) (.int 0)
                    cases hget : alts[(if bval then 1 else 0)]? with
                    | some alt =>
                      have htagEval :
                          SmtSem.eval m tag =
                            some (.int (if bval then 1 else 0)) := by
                        have hun := Moist.SMT.Semantics.eval_unVBool_of (m := m) (e := e) he
                        change SmtSem.eval m (Expr.ite (.app "unVBool" [e]) (.int 1) (.int 0)) =
                          some (.int (if bval then 1 else 0))
                        rw [eval_ite_of_bool (m := m) (c := .app "unVBool" [e])
                          (t := .int 1) (e := .int 0) hun]
                        cases bval <;> simp [Moist.SMT.Semantics.eval]
                      have hcovered := tagCovered_true_of_get (m := m)
                        (alts := alts) (tagExpr := tag)
                        (tagInt := (if bval then 1 else 0))
                        (i := (if bval then 1 else 0)) (alt := alt)
                        htagEval (by cases bval <;> simp) hget
                      have hnot := (Moist.SMT.Semantics.evalBoolIs_not_true m
                        (SExpr.any ((enumerate alts).map fun (j, _) =>
                          SExpr.eq tag (.int (Int.ofNat j))))).mp
                        (by simpa [tag, pcHolds] using hparts.2)
                      exact False.elim (evalBoolIs_true_false_contra hcovered hnot)
                    | none =>
                      cases bval
                      · simp [caseCekResult, Moist.CEK.constToTagAndFields] at hget ⊢
                        subst alts
                        simp
                      · simp [caseCekResult, Moist.CEK.constToTagAndFields] at hget ⊢
                        intro _
                        cases alts with
                        | nil => simp
                        | cons a rest =>
                          cases rest with
                          | nil => simp
                          | cons b rest => simp at hget
                · rcases hrest with hunitErr | hrest
                  · rw [hunitErr] at hg
                    by_cases hlenUnit : 1 < alts.length
                    · have heUnit := Moist.SMT.Semantics.evalBoolIs_isVUnit_true
                        (by simpa [pcHolds, hlenUnit] using hg)
                      rw [he] at heUnit
                      cases heUnit
                    · have hpartsUnit :=
                        (Moist.SMT.Semantics.evalBoolIs_and_true m
                          (SExpr.isCtor "VUnit" e)
                          (SExpr.not (SExpr.any (List.map Prod.fst
                            (if 1 < alts.length then []
                            else
                              match alts[0]? with
                              | some alt => [(SExpr.isCtor "VUnit" e, evalSym fuel ρ alt)]
                              | none => []))))).mp
                          (by simpa [pcHolds, hlenUnit] using hg)
                      have heUnit := Moist.SMT.Semantics.evalBoolIs_isVUnit_true hpartsUnit.1
                      rw [he] at heUnit
                      cases heUnit
                  · rcases hrest with hintErr | hrest
                    · rw [hintErr] at hg
                      have hpartsInt :=
                        (Moist.SMT.Semantics.evalBoolIs_and_true m
                          (SExpr.isCtor "VInt" e)
                          (SExpr.not (SExpr.and (nonnegGuard (.app "unVInt" [e]))
                            (SExpr.any ((enumerate alts).map fun (j, _) =>
                              SExpr.eq (.app "unVInt" [e]) (.int (Int.ofNat j))))))).mp
                          (by simpa [pcHolds] using hg)
                      obtain ⟨i, heInt⟩ :=
                        Moist.SMT.Semantics.evalBoolIs_isVInt_true hpartsInt.1
                      rw [he] at heInt
                      cases heInt
                    · rcases hrest with hlistErr | hrest
                      · rw [hlistErr] at hg
                        by_cases hlenList : 2 < alts.length
                        · obtain ⟨xs, heList⟩ :=
                            Moist.SMT.Semantics.evalBoolIs_isVList_true
                              (by simpa [pcHolds, hlenList] using hg)
                          rw [he] at heList
                          cases heList
                        · have hpartsList :=
                            (Moist.SMT.Semantics.evalBoolIs_and_true m
                              (SExpr.isCtor "VList" e)
                              (SExpr.not (SExpr.any (List.map Prod.fst
                                (if 2 < alts.length then []
                                else
                                  (match alts[0]? with
                                  | some alt =>
                                    [(SExpr.all [SExpr.isCtor "VList" e,
                                      (SExpr.isCtor "VNil" (.app "unVList" [e])).not],
                                      bindOut (evalSym fuel ρ alt) fun vAlt =>
                                        applyListSym fuel vAlt
                                          [fieldFromValList (.app "unVList" [e]),
                                            tailFromValList (.app "unVList" [e])])]
                                  | none => []) ++
                                  match alts[1]? with
                                  | some alt =>
                                    [(SExpr.all [SExpr.isCtor "VList" e,
                                      SExpr.isCtor "VNil" (.app "unVList" [e])],
                                      evalSym fuel ρ alt)]
                                  | none => []))))).mp
                              (by simpa [pcHolds, hlenList] using hg)
                          obtain ⟨xs, heList⟩ :=
                            Moist.SMT.Semantics.evalBoolIs_isVList_true hpartsList.1
                          rw [he] at heList
                          cases heList
                      · rcases hrest with hdataListErr | hrest
                        · rw [hdataListErr] at hg
                          by_cases hlenDataList : 2 < alts.length
                          · obtain ⟨xs, heDataList⟩ :=
                              Moist.SMT.Semantics.evalBoolIs_isVDataList_true
                                (by simpa [pcHolds, hlenDataList] using hg)
                            rw [he] at heDataList
                            cases heDataList
                          · have hpartsDataList :=
                              (Moist.SMT.Semantics.evalBoolIs_and_true m
                                (SExpr.isCtor "VDataList" e)
                                (SExpr.not (SExpr.any (List.map Prod.fst
                                  (if 2 < alts.length then []
                                  else
                                    (match alts[0]? with
                                    | some alt =>
                                      [(SExpr.all [SExpr.isCtor "VDataList" e,
                                        (SExpr.isCtor "DNil" (.app "unVDataList" [e])).not],
                                        bindOut (evalSym fuel ρ alt) fun vAlt =>
                                          applyListSym fuel vAlt
                                            [fieldFromDataList (.app "unVDataList" [e]),
                                              tailFromDataList (.app "unVDataList" [e])])]
                                    | none => []) ++
                                    match alts[1]? with
                                    | some alt =>
                                      [(SExpr.all [SExpr.isCtor "VDataList" e,
                                        SExpr.isCtor "DNil" (.app "unVDataList" [e])],
                                        evalSym fuel ρ alt)]
                                    | none => []))))).mp
                                (by simpa [pcHolds, hlenDataList] using hg)
                            obtain ⟨xs, heDataList⟩ :=
                              Moist.SMT.Semantics.evalBoolIs_isVDataList_true hpartsDataList.1
                            rw [he] at heDataList
                            cases heDataList
                        · rcases hrest with hpairErr | hrest
                          · rw [hpairErr] at hg
                            by_cases hlenPair : 1 < alts.length
                            · obtain ⟨a, b, hePair⟩ :=
                                Moist.SMT.Semantics.evalBoolIs_isVPair_true
                                  (by simpa [pcHolds, hlenPair] using hg)
                              rw [he] at hePair
                              cases hePair
                            · have hpartsPair :=
                                (Moist.SMT.Semantics.evalBoolIs_and_true m
                                  (SExpr.isCtor "VPair" e)
                                  (SExpr.not (SExpr.any (List.map Prod.fst
                                    (if 1 < alts.length then []
                                    else
                                      match alts[0]? with
                                      | some alt =>
                                        [(SExpr.isCtor "VPair" e,
                                          bindOut (evalSym fuel ρ alt) fun vAlt =>
                                            applyListSym fuel vAlt
                                              [SymVal.dyn (.app "vfst" [e]),
                                                SymVal.dyn (.app "vsnd" [e])])]
                                      | none => []))))).mp
                                  (by simpa [pcHolds, hlenPair] using hg)
                              obtain ⟨a, b, hePair⟩ :=
                                Moist.SMT.Semantics.evalBoolIs_isVPair_true hpartsPair.1
                              rw [he] at hePair
                              cases hePair
                          · rcases hrest with hpairDataErr | hrest
                            · rw [hpairDataErr] at hg
                              by_cases hlenPairData : 1 < alts.length
                              · obtain ⟨a, b, hePairData⟩ :=
                                  Moist.SMT.Semantics.evalBoolIs_isVPairData_true
                                    (by simpa [pcHolds, hlenPairData] using hg)
                                rw [he] at hePairData
                                cases hePairData
                              · have hpartsPairData :=
                                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                                    (SExpr.isCtor "VPairData" e)
                                    (SExpr.not (SExpr.any (List.map Prod.fst
                                      (if 1 < alts.length then []
                                      else
                                        match alts[0]? with
                                        | some alt =>
                                          [(SExpr.isCtor "VPairData" e,
                                            bindOut (evalSym fuel ρ alt) fun vAlt =>
                                              applyListSym fuel vAlt
                                                [SymVal.const (.data (.app "pdfst" [e])),
                                                  SymVal.const (.data (.app "pdsnd" [e]))])]
                                        | none => []))))).mp
                                    (by simpa [pcHolds, hlenPairData] using hg)
                                obtain ⟨a, b, hePairData⟩ :=
                                  Moist.SMT.Semantics.evalBoolIs_isVPairData_true hpartsPairData.1
                                rw [he] at hePairData
                                cases hePairData
                            · rcases hrest with hconstrErr | hunsupportedErr
                              · rw [hconstrErr] at hg
                                have hpartsConstr :=
                                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                                    (SExpr.isCtor "VConstr" e)
                                    (SExpr.not (SExpr.any ((enumerate alts).map fun (j, _) =>
                                      SExpr.eq (.app "vConstrTag" [e]) (.int (Int.ofNat j)))))).mp
                                    (by simpa [pcHolds] using hg)
                                obtain ⟨tag, fields, heConstr⟩ :=
                                  Moist.SMT.Semantics.evalBoolIs_isVConstr_true hpartsConstr.1
                                rw [he] at heConstr
                                cases heConstr
                              · rcases hunsupportedErr with hunsupportedErr | hnil
                                · rw [hunsupportedErr] at hg
                                  exact False.elim
                                    (unsupportedCaseGuard_false_of_supported
                                      (m := m) (e := e) (semv := .bool bval)
                                      (by simpa [pcHolds, unsupportedCaseGuard] using hg)
                                      he (by simp))
                                · simp at hnil
              | unit =>
                simp [symValToCek?, semValToCek?, semValToConst?, he] at hscrut
                subst cscrut
                rcases hgMem with hboolErr | hrest
                · rw [hboolErr] at hg
                  by_cases hlenBool : 2 < alts.length
                  · obtain ⟨b, heBool⟩ :=
                      Moist.SMT.Semantics.evalBoolIs_isVBool_true
                        (by simpa [pcHolds, hlenBool] using hg)
                    rw [he] at heBool
                    cases heBool
                  · have hpartsBool :=
                      (Moist.SMT.Semantics.evalBoolIs_and_true m
                        (SExpr.isCtor "VBool" e)
                        (SExpr.not (SExpr.any ((enumerate alts).map fun (j, _) =>
                          SExpr.eq (SExpr.ite (.app "unVBool" [e]) (.int 1) (.int 0))
                            (.int (Int.ofNat j)))))).mp
                        (by simpa [pcHolds, hlenBool] using hg)
                    obtain ⟨b, heBool⟩ :=
                      Moist.SMT.Semantics.evalBoolIs_isVBool_true hpartsBool.1
                    rw [he] at heBool
                    cases heBool
                · rcases hrest with hunitErr | hrest
                  · rw [hunitErr] at hg
                    by_cases hlen : 1 < alts.length
                    · simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen]
                    · cases h0 : alts[0]? with
                    | none =>
                      simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen, h0]
                    | some alt =>
                      have hparts :=
                        (Moist.SMT.Semantics.evalBoolIs_and_true m
                          (SExpr.isCtor "VUnit" e)
                          (SExpr.not (SExpr.any (List.map Prod.fst
                            ([(SExpr.isCtor "VUnit" e, evalSym fuel ρ alt)]))))).mp
                          (by simpa [hlen, h0, pcHolds] using hg)
                      have hcovered : pcHolds m (SExpr.any (List.map Prod.fst
                          ([(SExpr.isCtor "VUnit" e, evalSym fuel ρ alt)]))) = true := by
                        simpa [SExpr.any, Moist.SMT.Expr.any, pcHolds] using hparts.1
                      have hnot := (Moist.SMT.Semantics.evalBoolIs_not_true m
                        (SExpr.any (List.map Prod.fst
                          ([(SExpr.isCtor "VUnit" e, evalSym fuel ρ alt)])))).mp
                          (by simpa [pcHolds] using hparts.2)
                      exact False.elim (evalBoolIs_true_false_contra hcovered hnot)
                  · rcases hrest with hintErr | hrest
                    · rw [hintErr] at hg
                      have hparts :=
                        (Moist.SMT.Semantics.evalBoolIs_and_true m
                          (SExpr.isCtor "VInt" e)
                          (SExpr.not (SExpr.and (nonnegGuard (.app "unVInt" [e]))
                            (SExpr.any ((enumerate alts).map fun (j, _) =>
                              SExpr.eq (.app "unVInt" [e]) (.int (Int.ofNat j))))))).mp
                          (by simpa [pcHolds] using hg)
                      obtain ⟨i, heInt⟩ :=
                        Moist.SMT.Semantics.evalBoolIs_isVInt_true hparts.1
                      rw [he] at heInt
                      cases heInt
                    · rcases hrest with hlistErr | hrest
                      · rw [hlistErr] at hg
                        by_cases hlenList : 2 < alts.length
                        · obtain ⟨xs, heList⟩ :=
                            Moist.SMT.Semantics.evalBoolIs_isVList_true
                              (by simpa [pcHolds, hlenList] using hg)
                          rw [he] at heList
                          cases heList
                        · have hparts :=
                            (Moist.SMT.Semantics.evalBoolIs_and_true m
                              (SExpr.isCtor "VList" e)
                              (SExpr.not (SExpr.any (List.map Prod.fst
                                (if 2 < alts.length then []
                                else
                                  (match alts[0]? with
                                  | some alt =>
                                    [(SExpr.all [SExpr.isCtor "VList" e,
                                      (SExpr.isCtor "VNil" (.app "unVList" [e])).not],
                                      bindOut (evalSym fuel ρ alt) fun vAlt =>
                                        applyListSym fuel vAlt
                                          [fieldFromValList (.app "unVList" [e]),
                                            tailFromValList (.app "unVList" [e])])]
                                  | none => []) ++
                                  match alts[1]? with
                                  | some alt =>
                                    [(SExpr.all [SExpr.isCtor "VList" e,
                                      SExpr.isCtor "VNil" (.app "unVList" [e])],
                                      evalSym fuel ρ alt)]
                                  | none => []))))).mp
                              (by simpa [pcHolds, hlenList] using hg)
                          obtain ⟨xs, heList⟩ :=
                            Moist.SMT.Semantics.evalBoolIs_isVList_true hparts.1
                          rw [he] at heList
                          cases heList
                      · rcases hrest with hdataListErr | hrest
                        · rw [hdataListErr] at hg
                          by_cases hlenDataList : 2 < alts.length
                          · obtain ⟨xs, heDataList⟩ :=
                              Moist.SMT.Semantics.evalBoolIs_isVDataList_true
                                (by simpa [pcHolds, hlenDataList] using hg)
                            rw [he] at heDataList
                            cases heDataList
                          · have hparts :=
                              (Moist.SMT.Semantics.evalBoolIs_and_true m
                                (SExpr.isCtor "VDataList" e)
                                (SExpr.not (SExpr.any (List.map Prod.fst
                                  (if 2 < alts.length then []
                                  else
                                    (match alts[0]? with
                                    | some alt =>
                                      [(SExpr.all [SExpr.isCtor "VDataList" e,
                                        (SExpr.isCtor "DNil" (.app "unVDataList" [e])).not],
                                        bindOut (evalSym fuel ρ alt) fun vAlt =>
                                          applyListSym fuel vAlt
                                            [fieldFromDataList (.app "unVDataList" [e]),
                                              tailFromDataList (.app "unVDataList" [e])])]
                                    | none => []) ++
                                    match alts[1]? with
                                    | some alt =>
                                      [(SExpr.all [SExpr.isCtor "VDataList" e,
                                        SExpr.isCtor "DNil" (.app "unVDataList" [e])],
                                        evalSym fuel ρ alt)]
                                    | none => []))))).mp
                                (by simpa [pcHolds, hlenDataList] using hg)
                            obtain ⟨xs, heDataList⟩ :=
                              Moist.SMT.Semantics.evalBoolIs_isVDataList_true hparts.1
                            rw [he] at heDataList
                            cases heDataList
                        · rcases hrest with hpairErr | hrest
                          · rw [hpairErr] at hg
                            by_cases hlenPair : 1 < alts.length
                            · obtain ⟨a, b, hePair⟩ :=
                                Moist.SMT.Semantics.evalBoolIs_isVPair_true
                                  (by simpa [pcHolds, hlenPair] using hg)
                              rw [he] at hePair
                              cases hePair
                            · have hparts :=
                                (Moist.SMT.Semantics.evalBoolIs_and_true m
                                  (SExpr.isCtor "VPair" e)
                                  (SExpr.not (SExpr.any (List.map Prod.fst
                                    (if 1 < alts.length then []
                                    else
                                      match alts[0]? with
                                      | some alt =>
                                        [(SExpr.isCtor "VPair" e,
                                          bindOut (evalSym fuel ρ alt) fun vAlt =>
                                            applyListSym fuel vAlt
                                              [SymVal.dyn (.app "vfst" [e]),
                                                SymVal.dyn (.app "vsnd" [e])])]
                                      | none => []))))).mp
                                  (by simpa [pcHolds, hlenPair] using hg)
                              obtain ⟨a, b, hePair⟩ :=
                                Moist.SMT.Semantics.evalBoolIs_isVPair_true hparts.1
                              rw [he] at hePair
                              cases hePair
                          · rcases hrest with hpairDataErr | hrest
                            · rw [hpairDataErr] at hg
                              by_cases hlenPairData : 1 < alts.length
                              · obtain ⟨a, b, hePairData⟩ :=
                                  Moist.SMT.Semantics.evalBoolIs_isVPairData_true
                                    (by simpa [pcHolds, hlenPairData] using hg)
                                rw [he] at hePairData
                                cases hePairData
                              · have hparts :=
                                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                                    (SExpr.isCtor "VPairData" e)
                                    (SExpr.not (SExpr.any (List.map Prod.fst
                                      (if 1 < alts.length then []
                                      else
                                        match alts[0]? with
                                        | some alt =>
                                          [(SExpr.isCtor "VPairData" e,
                                            bindOut (evalSym fuel ρ alt) fun vAlt =>
                                              applyListSym fuel vAlt
                                                [SymVal.const (.data (.app "pdfst" [e])),
                                                  SymVal.const (.data (.app "pdsnd" [e]))])]
                                        | none => []))))).mp
                                    (by simpa [pcHolds, hlenPairData] using hg)
                                obtain ⟨a, b, hePairData⟩ :=
                                  Moist.SMT.Semantics.evalBoolIs_isVPairData_true hparts.1
                                rw [he] at hePairData
                                cases hePairData
                            · rcases hrest with hconstrErr | hunsupportedErr
                              · rw [hconstrErr] at hg
                                have hparts :=
                                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                                    (SExpr.isCtor "VConstr" e)
                                    (SExpr.not (SExpr.any ((enumerate alts).map fun (j, _) =>
                                      SExpr.eq (.app "vConstrTag" [e]) (.int (Int.ofNat j)))))).mp
                                    (by simpa [pcHolds] using hg)
                                obtain ⟨tag, fields, heConstr⟩ :=
                                  Moist.SMT.Semantics.evalBoolIs_isVConstr_true hparts.1
                                rw [he] at heConstr
                                cases heConstr
                              · rcases hunsupportedErr with hunsupportedErr | hnil
                                · rw [hunsupportedErr] at hg
                                  exact False.elim
                                    (unsupportedCaseGuard_false_of_supported
                                      (m := m) (e := e) (semv := .unit)
                                      (by simpa [pcHolds, unsupportedCaseGuard] using hg)
                                      he (by simp))
                                · simp at hnil
              | int ival =>
                simp [symValToCek?, semValToCek?, semValToConst?, he] at hscrut
                subst cscrut
                rcases hgMem with hboolErr | hrest
                · rw [hboolErr] at hg
                  have hboolPc : pcHolds m (SExpr.isCtor "VBool" e) = true :=
                    pcHolds_if_and_left (m := m) (p := 2 < alts.length)
                      (a := SExpr.isCtor "VBool" e)
                      (b := SExpr.not (SExpr.any ((enumerate alts).map fun (j, _) =>
                        SExpr.eq (SExpr.ite (.app "unVBool" [e]) (.int 1) (.int 0))
                          (.int (Int.ofNat j)))))
                      (by simpa [pcHolds] using hg)
                  obtain ⟨b, heBool⟩ :=
                    Moist.SMT.Semantics.evalBoolIs_isVBool_true hboolPc
                  rw [he] at heBool
                  cases heBool
                · rcases hrest with hunitErr | hrest
                  · rw [hunitErr] at hg
                    have hunitPc : pcHolds m (SExpr.isCtor "VUnit" e) = true :=
                      pcHolds_if_and_left (m := m) (p := 1 < alts.length)
                        (a := SExpr.isCtor "VUnit" e)
                        (b := SExpr.not (SExpr.any (List.map Prod.fst
                          (if 1 < alts.length then []
                          else
                            match alts[0]? with
                            | some alt => [(SExpr.isCtor "VUnit" e, evalSym fuel ρ alt)]
                            | none => []))))
                        (by simpa [pcHolds] using hg)
                    have heUnit :=
                      Moist.SMT.Semantics.evalBoolIs_isVUnit_true hunitPc
                    rw [he] at heUnit
                    cases heUnit
                  · rcases hrest with hintErr | hrest
                    · rw [hintErr] at hg
                      have hparts :=
                        (Moist.SMT.Semantics.evalBoolIs_and_true m
                          (SExpr.isCtor "VInt" e)
                          (SExpr.not (SExpr.and (nonnegGuard (.app "unVInt" [e]))
                            (SExpr.any ((enumerate alts).map fun (j, _) =>
                              SExpr.eq (.app "unVInt" [e]) (.int (Int.ofNat j))))))).mp
                          (by simpa [pcHolds] using hg)
                      by_cases hnonneg : 0 ≤ ival
                      · cases hget : alts[ival.toNat]? with
                        | some alt =>
                          have hun := Moist.SMT.Semantics.eval_unVInt_of (m := m) (e := e) he
                          have htagNat : ival = Int.ofNat ival.toNat :=
                            (Int.toNat_of_nonneg hnonneg).symm
                          have hcovered := tagCovered_true_of_get (m := m)
                            (alts := alts) (tagExpr := .app "unVInt" [e])
                            (tagInt := ival) (i := ival.toNat) (alt := alt)
                            hun htagNat hget
                          have hnonnegPc : pcHolds m (nonnegGuard (.app "unVInt" [e])) = true := by
                            have hgeEval := Moist.SMT.Semantics.eval_ge_of (m := m)
                              (a := .app "unVInt" [e]) (b := .int 0)
                              (x := ival) (y := 0) hun
                              (by simp [Moist.SMT.Semantics.eval])
                            have hgeEvalTrue :
                                Moist.SMT.Semantics.eval m
                                    (Expr.ge (.app "unVInt" [e]) (.int 0)) =
                                  some (.bool true) := by
                              rw [hgeEval]
                              simp [hnonneg]
                            have hbool : SmtSem.eval m (nonnegGuard (.app "unVInt" [e])) =
                                some (.bool true) := by
                              simpa [SmtSem.eval, nonnegGuard] using hgeEvalTrue
                            exact (Moist.SMT.Semantics.evalBoolIs_true_eq m
                              (nonnegGuard (.app "unVInt" [e]))).mpr hbool
                          let covered : SExpr :=
                            SExpr.any ((enumerate alts).map fun (j, _) =>
                              SExpr.eq (.app "unVInt" [e]) (.int (Int.ofNat j)))
                          have hcoveredAnd :
                              pcHolds m (SExpr.and (nonnegGuard (.app "unVInt" [e]))
                                (SExpr.any ((enumerate alts).map fun (j, _) =>
                                  SExpr.eq (.app "unVInt" [e]) (.int (Int.ofNat j))))) = true := by
                            have hcoveredAndEval :
                                Moist.SMT.Semantics.evalBoolIs m
                                  (SExpr.and (nonnegGuard (.app "unVInt" [e])) covered) true = true :=
                              (Moist.SMT.Semantics.evalBoolIs_and_true m
                                (nonnegGuard (.app "unVInt" [e])) covered).mpr
                                ⟨by simpa [pcHolds] using hnonnegPc,
                                  by simpa [covered, pcHolds] using hcovered⟩
                            simpa [covered, pcHolds] using hcoveredAndEval
                          have hnot := (Moist.SMT.Semantics.evalBoolIs_not_true m
                            (SExpr.and (nonnegGuard (.app "unVInt" [e])) covered)).mp
                              (by simpa [covered, pcHolds] using hparts.2)
                          exact False.elim (evalBoolIs_true_false_contra hcoveredAnd hnot)
                        | none =>
                          simp [caseCekResult, Moist.CEK.constToTagAndFields,
                            hnonneg, hget]
                      · simp [caseCekResult, Moist.CEK.constToTagAndFields, hnonneg]
                    · rcases hrest with hlistErr | hrest
                      · rw [hlistErr] at hg
                        have hlistPc : pcHolds m (SExpr.isCtor "VList" e) = true :=
                          pcHolds_if_and_left (m := m) (p := 2 < alts.length)
                            (a := SExpr.isCtor "VList" e)
                            (b := SExpr.not (SExpr.any (List.map Prod.fst
                              (if 2 < alts.length then []
                              else
                                (match alts[0]? with
                                | some alt =>
                                  [(SExpr.all [SExpr.isCtor "VList" e,
                                    (SExpr.isCtor "VNil" (.app "unVList" [e])).not],
                                    bindOut (evalSym fuel ρ alt) fun vAlt =>
                                      applyListSym fuel vAlt
                                        [fieldFromValList (.app "unVList" [e]),
                                          tailFromValList (.app "unVList" [e])])]
                                | none => []) ++
                                match alts[1]? with
                                | some alt =>
                                  [(SExpr.all [SExpr.isCtor "VList" e,
                                    SExpr.isCtor "VNil" (.app "unVList" [e])],
                                    evalSym fuel ρ alt)]
                                | none => []))))
                            (by simpa [pcHolds] using hg)
                        obtain ⟨xs, heList⟩ :=
                          Moist.SMT.Semantics.evalBoolIs_isVList_true hlistPc
                        rw [he] at heList
                        cases heList
                      · rcases hrest with hdataListErr | hrest
                        · rw [hdataListErr] at hg
                          have hdataListPc : pcHolds m (SExpr.isCtor "VDataList" e) = true :=
                            pcHolds_if_and_left (m := m) (p := 2 < alts.length)
                              (a := SExpr.isCtor "VDataList" e)
                              (b := SExpr.not (SExpr.any (List.map Prod.fst
                                (if 2 < alts.length then []
                                else
                                  (match alts[0]? with
                                  | some alt =>
                                    [(SExpr.all [SExpr.isCtor "VDataList" e,
                                      (SExpr.isCtor "DNil" (.app "unVDataList" [e])).not],
                                      bindOut (evalSym fuel ρ alt) fun vAlt =>
                                        applyListSym fuel vAlt
                                          [fieldFromDataList (.app "unVDataList" [e]),
                                            tailFromDataList (.app "unVDataList" [e])])]
                                  | none => []) ++
                                  match alts[1]? with
                                  | some alt =>
                                    [(SExpr.all [SExpr.isCtor "VDataList" e,
                                      SExpr.isCtor "DNil" (.app "unVDataList" [e])],
                                      evalSym fuel ρ alt)]
                                  | none => []))))
                              (by simpa [pcHolds] using hg)
                          obtain ⟨xs, heDataList⟩ :=
                            Moist.SMT.Semantics.evalBoolIs_isVDataList_true hdataListPc
                          rw [he] at heDataList
                          cases heDataList
                        · rcases hrest with hpairErr | hrest
                          · rw [hpairErr] at hg
                            have hpairPc : pcHolds m (SExpr.isCtor "VPair" e) = true :=
                              pcHolds_if_and_left (m := m) (p := 1 < alts.length)
                                (a := SExpr.isCtor "VPair" e)
                                (b := SExpr.not (SExpr.any (List.map Prod.fst
                                  (if 1 < alts.length then []
                                  else
                                    match alts[0]? with
                                    | some alt =>
                                      [(SExpr.isCtor "VPair" e,
                                        bindOut (evalSym fuel ρ alt) fun vAlt =>
                                          applyListSym fuel vAlt
                                            [SymVal.dyn (.app "vfst" [e]),
                                              SymVal.dyn (.app "vsnd" [e])])]
                                    | none => []))))
                                (by simpa [pcHolds] using hg)
                            obtain ⟨a, b, hePair⟩ :=
                              Moist.SMT.Semantics.evalBoolIs_isVPair_true hpairPc
                            rw [he] at hePair
                            cases hePair
                          · rcases hrest with hpairDataErr | hrest
                            · rw [hpairDataErr] at hg
                              have hpairDataPc : pcHolds m (SExpr.isCtor "VPairData" e) = true :=
                                pcHolds_if_and_left (m := m) (p := 1 < alts.length)
                                  (a := SExpr.isCtor "VPairData" e)
                                  (b := SExpr.not (SExpr.any (List.map Prod.fst
                                    (if 1 < alts.length then []
                                    else
                                      match alts[0]? with
                                      | some alt =>
                                        [(SExpr.isCtor "VPairData" e,
                                          bindOut (evalSym fuel ρ alt) fun vAlt =>
                                            applyListSym fuel vAlt
                                              [SymVal.const (.data (.app "pdfst" [e])),
                                                SymVal.const (.data (.app "pdsnd" [e]))])]
                                      | none => []))))
                                  (by simpa [pcHolds] using hg)
                              obtain ⟨a, b, hePairData⟩ :=
                                Moist.SMT.Semantics.evalBoolIs_isVPairData_true hpairDataPc
                              rw [he] at hePairData
                              cases hePairData
                            · rcases hrest with hconstrErr | hunsupportedErr
                              · rw [hconstrErr] at hg
                                have hconstrPc :=
                                  pcHolds_and_left (m := m)
                                    (a := SExpr.isCtor "VConstr" e)
                                    (b := SExpr.not (SExpr.any ((enumerate alts).map fun (j, _) =>
                                      SExpr.eq (.app "vConstrTag" [e]) (.int (Int.ofNat j)))))
                                    (by simpa [pcHolds] using hg)
                                obtain ⟨tag, fields, heConstr⟩ :=
                                  Moist.SMT.Semantics.evalBoolIs_isVConstr_true hconstrPc
                                rw [he] at heConstr
                                cases heConstr
                              · rcases hunsupportedErr with hunsupportedErr | hnil
                                · rw [hunsupportedErr] at hg
                                  exact False.elim
                                    (unsupportedCaseGuard_false_of_supported
                                      (m := m) (e := e) (semv := .int ival)
                                      (by simpa [pcHolds, unsupportedCaseGuard] using hg)
                                      he (by simp))
                                · simp at hnil
              | bytes bs =>
                simp [symValToCek?, semValToCek?, semValToConst?, he] at hscrut
                subst cscrut
                simp [caseCekResult, Moist.CEK.constToTagAndFields]
              | string s =>
                simp [symValToCek?, semValToCek?, semValToConst?, he] at hscrut
                subst cscrut
                simp [caseCekResult, Moist.CEK.constToTagAndFields]
              | data d =>
                simp [symValToCek?, semValToCek?, semValToConst?, he] at hscrut
                subst cscrut
                simp [caseCekResult, Moist.CEK.constToTagAndFields]
              | pairDataList xs =>
                simp [symValToCek?, semValToCek?, semValToConst?, he] at hscrut
                subst cscrut
                simp [caseCekResult, Moist.CEK.constToTagAndFields]
              | array xs =>
                cases hconsts : semValListToConstList? xs with
                | none =>
                  simp [symValToCek?, semValToCek?, semValToConst?, he,
                    hconsts] at hscrut
                | some consts =>
                  simp [symValToCek?, semValToCek?, semValToConst?, he,
                    hconsts] at hscrut
                  subst cscrut
                  simp [caseCekResult, Moist.CEK.constToTagAndFields]
              | g1 g1 =>
                simp [symValToCek?, semValToCek?, semValToConst?, he] at hscrut
                subst cscrut
                simp [caseCekResult, Moist.CEK.constToTagAndFields]
              | g2 g2 =>
                simp [symValToCek?, semValToCek?, semValToConst?, he] at hscrut
                subst cscrut
                simp [caseCekResult, Moist.CEK.constToTagAndFields]
              | ml r =>
                simp [symValToCek?, semValToCek?, semValToConst?, he] at hscrut
                subst cscrut
                simp [caseCekResult, Moist.CEK.constToTagAndFields]
              | list xs =>
                cases hconsts : semValListToConstList? xs with
                | none =>
                  simp [symValToCek?, semValToCek?, semValToConst?, he, hconsts] at hscrut
                | some consts =>
                  simp [symValToCek?, semValToCek?, semValToConst?, he, hconsts] at hscrut
                  subst cscrut
                  have hxsEval :=
                    Moist.SMT.Semantics.eval_unVList_of (m := m) (e := e) he
                  rcases hgMem with hboolErr | hrest
                  · rw [hboolErr] at hg
                    have hboolPc : pcHolds m (SExpr.isCtor "VBool" e) = true :=
                      pcHolds_if_and_left (m := m) (p := 2 < alts.length)
                        (a := SExpr.isCtor "VBool" e)
                        (b := SExpr.not (SExpr.any ((enumerate alts).map fun (j, _) =>
                          SExpr.eq (SExpr.ite (.app "unVBool" [e]) (.int 1) (.int 0))
                            (.int (Int.ofNat j)))))
                        (by simpa [pcHolds] using hg)
                    obtain ⟨b, heBool⟩ :=
                      Moist.SMT.Semantics.evalBoolIs_isVBool_true hboolPc
                    rw [he] at heBool
                    cases heBool
                  · rcases hrest with hunitErr | hrest
                    · rw [hunitErr] at hg
                      have hunitPc : pcHolds m (SExpr.isCtor "VUnit" e) = true :=
                        pcHolds_if_and_left (m := m) (p := 1 < alts.length)
                          (a := SExpr.isCtor "VUnit" e)
                          (b := SExpr.not (SExpr.any (List.map Prod.fst
                            (if 1 < alts.length then []
                            else
                              match alts[0]? with
                              | some alt => [(SExpr.isCtor "VUnit" e, evalSym fuel ρ alt)]
                              | none => []))))
                          (by simpa [pcHolds] using hg)
                      have heUnit :=
                        Moist.SMT.Semantics.evalBoolIs_isVUnit_true hunitPc
                      rw [he] at heUnit
                      cases heUnit
                    · rcases hrest with hintErr | hrest
                      · rw [hintErr] at hg
                        have hintPc :=
                          pcHolds_and_left (m := m)
                            (a := SExpr.isCtor "VInt" e)
                            (b := SExpr.not (SExpr.and (nonnegGuard (.app "unVInt" [e]))
                              (SExpr.any ((enumerate alts).map fun (j, _) =>
                                SExpr.eq (.app "unVInt" [e]) (.int (Int.ofNat j))))))
                            (by simpa [pcHolds] using hg)
                        obtain ⟨i, heInt⟩ :=
                          Moist.SMT.Semantics.evalBoolIs_isVInt_true hintPc
                        rw [he] at heInt
                        cases heInt
                      · rcases hrest with hlistErr | hrest
                        · rw [hlistErr] at hg
                          by_cases hlen : 2 < alts.length
                          · cases consts <;>
                              simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen]
                          · have hparts :=
                              (Moist.SMT.Semantics.evalBoolIs_and_true m
                                (SExpr.isCtor "VList" e)
                                (SExpr.not (SExpr.any (List.map Prod.fst
                                  (if 2 < alts.length then []
                                  else
                                    (match alts[0]? with
                                    | some alt =>
                                      [(SExpr.all [SExpr.isCtor "VList" e,
                                          (SExpr.isCtor "VNil" (.app "unVList" [e])).not],
                                          bindOut (evalSym fuel ρ alt) fun vAlt =>
                                            applyListSym fuel vAlt
                                              [fieldFromValList (.app "unVList" [e]),
                                                tailFromValList (.app "unVList" [e])])]
                                    | none => []) ++
                                    match alts[1]? with
                                    | some alt =>
                                      [(SExpr.all [SExpr.isCtor "VList" e,
                                          SExpr.isCtor "VNil" (.app "unVList" [e])],
                                          evalSym fuel ρ alt)]
                                    | none => []))))).mp
                                (by simpa [hlen, pcHolds] using hg)
                            cases xs with
                            | nil =>
                              simp [semValListToConstList?] at hconsts
                              subst consts
                              cases h0 : alts[0]? with
                              | none =>
                                cases h1 : alts[1]? with
                                | none =>
                                  simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen, h1]
                                | some nilAlt =>
                                  have hnil :=
                                    Moist.SMT.Semantics.evalBoolIs_isVNil_true_of_valList_nil hxsEval
                                  have hnilGuard :
                                      pcHolds m (SExpr.all [SExpr.isCtor "VList" e,
                                        SExpr.isCtor "VNil" (.app "unVList" [e])]) = true :=
                                    pcHolds_all2_intro (m := m) hparts.1 hnil
                                  have hcovered : pcHolds m (SExpr.any
                                      (List.map Prod.fst
                                        ([(SExpr.all [SExpr.isCtor "VList" e,
                                            SExpr.isCtor "VNil" (.app "unVList" [e])],
                                            evalSym fuel ρ nilAlt)]))) = true := by
                                    simpa [SExpr.any, Moist.SMT.Expr.any, pcHolds] using hnilGuard
                                  have hnot := (Moist.SMT.Semantics.evalBoolIs_not_true m
                                      (SExpr.any
                                        (List.map Prod.fst
                                          ([(SExpr.all [SExpr.isCtor "VList" e,
                                              SExpr.isCtor "VNil" (.app "unVList" [e])],
                                              evalSym fuel ρ nilAlt)])))).mp
                                      (by simpa [hlen, h0, h1, pcHolds] using hparts.2)
                                  exact False.elim (evalBoolIs_true_false_contra hcovered hnot)
                              | some consAlt =>
                                cases h1 : alts[1]? with
                                | none =>
                                  simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen, h1]
                                | some nilAlt =>
                                  have hnil :=
                                    Moist.SMT.Semantics.evalBoolIs_isVNil_true_of_valList_nil hxsEval
                                  have hnilGuard :
                                      pcHolds m (SExpr.all [SExpr.isCtor "VList" e,
                                        SExpr.isCtor "VNil" (.app "unVList" [e])]) = true :=
                                    pcHolds_all2_intro (m := m) hparts.1 hnil
                                  have hnilEval :
                                      SmtSem.eval m (SExpr.all [SExpr.isCtor "VList" e,
                                        SExpr.isCtor "VNil" (.app "unVList" [e])]) =
                                        some (.bool true) :=
                                    (Moist.SMT.Semantics.evalBoolIs_true_eq m
                                      (SExpr.all [SExpr.isCtor "VList" e,
                                        SExpr.isCtor "VNil" (.app "unVList" [e])])).mp hnilGuard
                                  have hconsBool :
                                      ∃ b, SmtSem.eval m (SExpr.all [SExpr.isCtor "VList" e,
                                        (SExpr.isCtor "VNil" (.app "unVList" [e])).not]) =
                                        some (.bool b) := by
                                    have hisListEval :
                                        SmtSem.eval m (SExpr.isCtor "VList" e) =
                                          some (.bool true) :=
                                      (Moist.SMT.Semantics.evalBoolIs_true_eq m
                                        (SExpr.isCtor "VList" e)).mp hparts.1
                                    have hnilEval0 :
                                        SmtSem.eval m (SExpr.isCtor "VNil" (.app "unVList" [e])) =
                                          some (.bool true) :=
                                      (Moist.SMT.Semantics.evalBoolIs_true_eq m
                                        (SExpr.isCtor "VNil" (.app "unVList" [e]))).mp hnil
                                    have hnotNilEval :=
                                      eval_not_of_bool (m := m)
                                        (e := SExpr.isCtor "VNil" (.app "unVList" [e]))
                                        (b := true) hnilEval0
                                    exact evalBoolExists_all2 (m := m) hisListEval hnotNilEval
                                  have hcovered : pcHolds m (SExpr.any
                                      (List.map Prod.fst
                                        ([(SExpr.all [SExpr.isCtor "VList" e,
                                            (SExpr.isCtor "VNil" (.app "unVList" [e])).not],
                                            bindOut (evalSym fuel ρ consAlt) fun vAlt =>
                                              applyListSym fuel vAlt
                                                [fieldFromValList (.app "unVList" [e]),
                                                  tailFromValList (.app "unVList" [e])])] ++
                                          [(SExpr.all [SExpr.isCtor "VList" e,
                                              SExpr.isCtor "VNil" (.app "unVList" [e])],
                                              evalSym fuel ρ nilAlt)]))) = true := by
                                    have hor := evalBoolIs_or_true_of_right (m := m)
                                      (a := SExpr.all [SExpr.isCtor "VList" e,
                                        (SExpr.isCtor "VNil" (.app "unVList" [e])).not])
                                      (b := SExpr.all [SExpr.isCtor "VList" e,
                                        SExpr.isCtor "VNil" (.app "unVList" [e])])
                                      hconsBool hnilEval
                                    simpa [SExpr.any, Moist.SMT.Expr.any, pcHolds] using hor
                                  have hnot := (Moist.SMT.Semantics.evalBoolIs_not_true m
                                      (SExpr.any
                                        (List.map Prod.fst
                                          ([(SExpr.all [SExpr.isCtor "VList" e,
                                              (SExpr.isCtor "VNil" (.app "unVList" [e])).not],
                                              bindOut (evalSym fuel ρ consAlt) fun vAlt =>
                                                applyListSym fuel vAlt
                                                  [fieldFromValList (.app "unVList" [e]),
                                                    tailFromValList (.app "unVList" [e])])] ++
                                            [(SExpr.all [SExpr.isCtor "VList" e,
                                                SExpr.isCtor "VNil" (.app "unVList" [e])],
                                                evalSym fuel ρ nilAlt)])))).mp
                                      (by simpa [hlen, h0, h1, pcHolds] using hparts.2)
                                  exact False.elim (evalBoolIs_true_false_contra hcovered hnot)
                            | cons head tail =>
                              cases hheadConst : semValToConst? head with
                              | none =>
                                simp [semValListToConstList?, hheadConst] at hconsts
                              | some headConst =>
                                cases htailConst : semValListToConstList? tail with
                                | none =>
                                  simp [semValListToConstList?, hheadConst, htailConst] at hconsts
                                | some tailConst =>
                                  simp [semValListToConstList?, hheadConst, htailConst] at hconsts
                                  subst consts
                                  cases h0 : alts[0]? with
                                  | none =>
                                    simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen, h0]
                                  | some consAlt =>
                                    have hfalse :=
                                      Moist.SMT.Semantics.evalBoolIs_isVNil_false_of_valList_cons hxsEval
                                    have hnotNil :
                                        pcHolds m (SExpr.not (SExpr.isCtor "VNil"
                                          (.app "unVList" [e]))) = true :=
                                      (Moist.SMT.Semantics.evalBoolIs_not_true m
                                        (SExpr.isCtor "VNil" (.app "unVList" [e]))).mpr hfalse
                                    have hconsGuard :
                                        pcHolds m (SExpr.all [SExpr.isCtor "VList" e,
                                          (SExpr.isCtor "VNil" (.app "unVList" [e])).not]) = true :=
                                      pcHolds_all2_intro (m := m) hparts.1 hnotNil
                                    cases h1 : alts[1]? with
                                    | none =>
                                      have hcovered : pcHolds m (SExpr.any
                                          [SExpr.all [SExpr.isCtor "VList" e,
                                            (SExpr.isCtor "VNil" (.app "unVList" [e])).not]]) = true := by
                                        simpa [SExpr.any, Moist.SMT.Expr.any, pcHolds] using hconsGuard
                                      have hnot := (Moist.SMT.Semantics.evalBoolIs_not_true m
                                          (SExpr.any [SExpr.all [SExpr.isCtor "VList" e,
                                            (SExpr.isCtor "VNil" (.app "unVList" [e])).not]])).mp
                                          (by simpa [hlen, h0, h1, pcHolds] using hparts.2)
                                      exact False.elim (evalBoolIs_true_false_contra hcovered hnot)
                                    | some nilAlt =>
                                      have hconsEval :
                                          SmtSem.eval m (SExpr.all [SExpr.isCtor "VList" e,
                                            (SExpr.isCtor "VNil" (.app "unVList" [e])).not]) =
                                            some (.bool true) :=
                                        (Moist.SMT.Semantics.evalBoolIs_true_eq m
                                          (SExpr.all [SExpr.isCtor "VList" e,
                                            (SExpr.isCtor "VNil" (.app "unVList" [e])).not])).mp hconsGuard
                                      have hnilBool :
                                          ∃ b, SmtSem.eval m (SExpr.all [SExpr.isCtor "VList" e,
                                            SExpr.isCtor "VNil" (.app "unVList" [e])]) =
                                            some (.bool b) := by
                                        have hisListEval :
                                            SmtSem.eval m (SExpr.isCtor "VList" e) =
                                              some (.bool true) :=
                                          (Moist.SMT.Semantics.evalBoolIs_true_eq m
                                            (SExpr.isCtor "VList" e)).mp hparts.1
                                        have hnilEvalFalse :
                                            SmtSem.eval m (SExpr.isCtor "VNil" (.app "unVList" [e])) =
                                              some (.bool false) :=
                                          evalBoolIs_false_eq.mp hfalse
                                        exact evalBoolExists_all2 (m := m) hisListEval hnilEvalFalse
                                      have hcovered : pcHolds m (SExpr.any
                                          (List.map Prod.fst
                                            ([(SExpr.all [SExpr.isCtor "VList" e,
                                                (SExpr.isCtor "VNil" (.app "unVList" [e])).not],
                                                bindOut (evalSym fuel ρ consAlt) fun vAlt =>
                                                  applyListSym fuel vAlt
                                                    [fieldFromValList (.app "unVList" [e]),
                                                      tailFromValList (.app "unVList" [e])])] ++
                                              [(SExpr.all [SExpr.isCtor "VList" e,
                                                  SExpr.isCtor "VNil" (.app "unVList" [e])],
                                                  evalSym fuel ρ nilAlt)]))) = true := by
                                        have hor := evalBoolIs_or_true_of_left (m := m)
                                          (a := SExpr.all [SExpr.isCtor "VList" e,
                                            (SExpr.isCtor "VNil" (.app "unVList" [e])).not])
                                          (b := SExpr.all [SExpr.isCtor "VList" e,
                                            SExpr.isCtor "VNil" (.app "unVList" [e])])
                                          hconsEval hnilBool
                                        simpa [SExpr.any, Moist.SMT.Expr.any, pcHolds] using hor
                                      have hnot := (Moist.SMT.Semantics.evalBoolIs_not_true m
                                          (SExpr.any
                                            (List.map Prod.fst
                                              ([(SExpr.all [SExpr.isCtor "VList" e,
                                                  (SExpr.isCtor "VNil" (.app "unVList" [e])).not],
                                                  bindOut (evalSym fuel ρ consAlt) fun vAlt =>
                                                    applyListSym fuel vAlt
                                                      [fieldFromValList (.app "unVList" [e]),
                                                        tailFromValList (.app "unVList" [e])])] ++
                                                [(SExpr.all [SExpr.isCtor "VList" e,
                                                    SExpr.isCtor "VNil" (.app "unVList" [e])],
                                                    evalSym fuel ρ nilAlt)])))).mp
                                          (by simpa [hlen, h0, h1, pcHolds] using hparts.2)
                                      exact False.elim (evalBoolIs_true_false_contra hcovered hnot)
                        · rcases hrest with hdataListErr | hrest
                          · rw [hdataListErr] at hg
                            have hdataListPc : pcHolds m (SExpr.isCtor "VDataList" e) = true :=
                              pcHolds_if_and_left (m := m) (p := 2 < alts.length)
                                (a := SExpr.isCtor "VDataList" e)
                                (b := SExpr.not (SExpr.any (List.map Prod.fst
                                  (if 2 < alts.length then []
                                  else
                                    (match alts[0]? with
                                    | some alt =>
                                      [(SExpr.all [SExpr.isCtor "VDataList" e,
                                        (SExpr.isCtor "DNil" (.app "unVDataList" [e])).not],
                                        bindOut (evalSym fuel ρ alt) fun vAlt =>
                                          applyListSym fuel vAlt
                                            [fieldFromDataList (.app "unVDataList" [e]),
                                              tailFromDataList (.app "unVDataList" [e])])]
                                    | none => []) ++
                                    match alts[1]? with
                                    | some alt =>
                                      [(SExpr.all [SExpr.isCtor "VDataList" e,
                                        SExpr.isCtor "DNil" (.app "unVDataList" [e])],
                                        evalSym fuel ρ alt)]
                                    | none => []))))
                                (by simpa [pcHolds] using hg)
                            obtain ⟨xsData, heDataList⟩ :=
                              Moist.SMT.Semantics.evalBoolIs_isVDataList_true hdataListPc
                            rw [he] at heDataList
                            cases heDataList
                          · rcases hrest with hpairErr | hrest
                            · rw [hpairErr] at hg
                              have hpairPc : pcHolds m (SExpr.isCtor "VPair" e) = true :=
                                pcHolds_if_and_left (m := m) (p := 1 < alts.length)
                                  (a := SExpr.isCtor "VPair" e)
                                  (b := SExpr.not (SExpr.any (List.map Prod.fst
                                    (if 1 < alts.length then []
                                    else
                                      match alts[0]? with
                                      | some alt =>
                                        [(SExpr.isCtor "VPair" e,
                                          bindOut (evalSym fuel ρ alt) fun vAlt =>
                                            applyListSym fuel vAlt
                                              [SymVal.dyn (.app "vfst" [e]),
                                                SymVal.dyn (.app "vsnd" [e])])]
                                      | none => []))))
                                  (by simpa [pcHolds] using hg)
                              obtain ⟨a, b, hePair⟩ :=
                                Moist.SMT.Semantics.evalBoolIs_isVPair_true hpairPc
                              rw [he] at hePair
                              cases hePair
                            · rcases hrest with hpairDataErr | hrest
                              · rw [hpairDataErr] at hg
                                have hpairDataPc : pcHolds m (SExpr.isCtor "VPairData" e) = true :=
                                  pcHolds_if_and_left (m := m) (p := 1 < alts.length)
                                    (a := SExpr.isCtor "VPairData" e)
                                    (b := SExpr.not (SExpr.any (List.map Prod.fst
                                      (if 1 < alts.length then []
                                      else
                                        match alts[0]? with
                                        | some alt =>
                                          [(SExpr.isCtor "VPairData" e,
                                            bindOut (evalSym fuel ρ alt) fun vAlt =>
                                              applyListSym fuel vAlt
                                                [SymVal.const (.data (.app "pdfst" [e])),
                                                  SymVal.const (.data (.app "pdsnd" [e]))])]
                                        | none => []))))
                                    (by simpa [pcHolds] using hg)
                                obtain ⟨a, b, hePairData⟩ :=
                                  Moist.SMT.Semantics.evalBoolIs_isVPairData_true hpairDataPc
                                rw [he] at hePairData
                                cases hePairData
                              · rcases hrest with hconstrErr | hunsupportedErr
                                · rw [hconstrErr] at hg
                                  have hconstrPc :=
                                    pcHolds_and_left (m := m)
                                      (a := SExpr.isCtor "VConstr" e)
                                      (b := SExpr.not (SExpr.any ((enumerate alts).map fun (j, _) =>
                                        SExpr.eq (.app "vConstrTag" [e]) (.int (Int.ofNat j)))))
                                      (by simpa [pcHolds] using hg)
                                  obtain ⟨tag, fields, heConstr⟩ :=
                                    Moist.SMT.Semantics.evalBoolIs_isVConstr_true hconstrPc
                                  rw [he] at heConstr
                                  cases heConstr
                                · rcases hunsupportedErr with hunsupportedErr | hnil
                                  · rw [hunsupportedErr] at hg
                                    exact False.elim
                                      (unsupportedCaseGuard_false_of_supported
                                        (m := m) (e := e) (semv := .list xs)
                                        (by simpa [pcHolds, unsupportedCaseGuard] using hg)
                                        he (by simp))
                                  · simp at hnil
              | dataList xs =>
                simp [symValToCek?, semValToCek?, semValToConst?, he] at hscrut
                subst cscrut
                have hxsEval :=
                  Moist.SMT.Semantics.eval_unVDataList_of (m := m) (e := e) he
                rcases hgMem with hboolErr | hrest
                · rw [hboolErr] at hg
                  have hboolPc : pcHolds m (SExpr.isCtor "VBool" e) = true :=
                    pcHolds_if_and_left (m := m) (p := 2 < alts.length)
                      (a := SExpr.isCtor "VBool" e)
                      (b := SExpr.not (SExpr.any ((enumerate alts).map fun (j, _) =>
                        SExpr.eq (SExpr.ite (.app "unVBool" [e]) (.int 1) (.int 0))
                          (.int (Int.ofNat j)))))
                      (by simpa [pcHolds] using hg)
                  obtain ⟨b, heBool⟩ :=
                    Moist.SMT.Semantics.evalBoolIs_isVBool_true hboolPc
                  rw [he] at heBool
                  cases heBool
                · rcases hrest with hunitErr | hrest
                  · rw [hunitErr] at hg
                    have hunitPc : pcHolds m (SExpr.isCtor "VUnit" e) = true :=
                      pcHolds_if_and_left (m := m) (p := 1 < alts.length)
                        (a := SExpr.isCtor "VUnit" e)
                        (b := SExpr.not (SExpr.any (List.map Prod.fst
                          (if 1 < alts.length then []
                          else
                            match alts[0]? with
                            | some alt => [(SExpr.isCtor "VUnit" e, evalSym fuel ρ alt)]
                            | none => []))))
                        (by simpa [pcHolds] using hg)
                    have heUnit :=
                      Moist.SMT.Semantics.evalBoolIs_isVUnit_true hunitPc
                    rw [he] at heUnit
                    cases heUnit
                  · rcases hrest with hintErr | hrest
                    · rw [hintErr] at hg
                      have hintPc :=
                        pcHolds_and_left (m := m)
                          (a := SExpr.isCtor "VInt" e)
                          (b := SExpr.not (SExpr.and (nonnegGuard (.app "unVInt" [e]))
                            (SExpr.any ((enumerate alts).map fun (j, _) =>
                              SExpr.eq (.app "unVInt" [e]) (.int (Int.ofNat j))))))
                          (by simpa [pcHolds] using hg)
                      obtain ⟨i, heInt⟩ :=
                        Moist.SMT.Semantics.evalBoolIs_isVInt_true hintPc
                      rw [he] at heInt
                      cases heInt
                    · rcases hrest with hlistErr | hrest
                      · rw [hlistErr] at hg
                        have hlistPc : pcHolds m (SExpr.isCtor "VList" e) = true :=
                          pcHolds_if_and_left (m := m) (p := 2 < alts.length)
                            (a := SExpr.isCtor "VList" e)
                            (b := SExpr.not (SExpr.any (List.map Prod.fst
                              (if 2 < alts.length then []
                              else
                                (match alts[0]? with
                                | some alt =>
                                  [(SExpr.all [SExpr.isCtor "VList" e,
                                    (SExpr.isCtor "VNil" (.app "unVList" [e])).not],
                                    bindOut (evalSym fuel ρ alt) fun vAlt =>
                                      applyListSym fuel vAlt
                                        [fieldFromValList (.app "unVList" [e]),
                                          tailFromValList (.app "unVList" [e])])]
                                | none => []) ++
                                match alts[1]? with
                                | some alt =>
                                  [(SExpr.all [SExpr.isCtor "VList" e,
                                    SExpr.isCtor "VNil" (.app "unVList" [e])],
                                    evalSym fuel ρ alt)]
                                | none => []))))
                            (by simpa [pcHolds] using hg)
                        obtain ⟨vals, heList⟩ :=
                          Moist.SMT.Semantics.evalBoolIs_isVList_true hlistPc
                        rw [he] at heList
                        cases heList
                      · rcases hrest with hdataListErr | hrest
                        · rw [hdataListErr] at hg
                          by_cases hlen : 2 < alts.length
                          · cases xs <;>
                              simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen]
                          · have hparts :=
                              (Moist.SMT.Semantics.evalBoolIs_and_true m
                                (SExpr.isCtor "VDataList" e)
                                (SExpr.not (SExpr.any (List.map Prod.fst
                                  (if 2 < alts.length then []
                                  else
                                    (match alts[0]? with
                                    | some alt =>
                                      [(SExpr.all [SExpr.isCtor "VDataList" e,
                                        (SExpr.isCtor "DNil" (.app "unVDataList" [e])).not],
                                        bindOut (evalSym fuel ρ alt) fun vAlt =>
                                          applyListSym fuel vAlt
                                            [fieldFromDataList (.app "unVDataList" [e]),
                                              tailFromDataList (.app "unVDataList" [e])])]
                                    | none => []) ++
                                    match alts[1]? with
                                    | some alt =>
                                      [(SExpr.all [SExpr.isCtor "VDataList" e,
                                        SExpr.isCtor "DNil" (.app "unVDataList" [e])],
                                        evalSym fuel ρ alt)]
                                    | none => []))))).mp
                                (by simpa [hlen, pcHolds] using hg)
                            cases xs with
                            | nil =>
                              cases h1 : alts[1]? with
                              | none =>
                                simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen, h1]
                              | some nilAlt =>
                                have hnil :=
                                  Moist.SMT.Semantics.evalBoolIs_isDNil_true_of_dataList_nil hxsEval
                                have hnilGuard :
                                    pcHolds m (SExpr.all [SExpr.isCtor "VDataList" e,
                                      SExpr.isCtor "DNil" (.app "unVDataList" [e])]) = true :=
                                  pcHolds_all2_intro (m := m) hparts.1 hnil
                                cases h0 : alts[0]? with
                                | none =>
                                  have hcovered : pcHolds m (SExpr.any
                                      (List.map Prod.fst
                                        ([(SExpr.all [SExpr.isCtor "VDataList" e,
                                            SExpr.isCtor "DNil" (.app "unVDataList" [e])],
                                            evalSym fuel ρ nilAlt)]))) = true := by
                                    simpa [SExpr.any, Moist.SMT.Expr.any, pcHolds] using hnilGuard
                                  have hnot := (Moist.SMT.Semantics.evalBoolIs_not_true m
                                      (SExpr.any
                                        (List.map Prod.fst
                                          ([(SExpr.all [SExpr.isCtor "VDataList" e,
                                              SExpr.isCtor "DNil" (.app "unVDataList" [e])],
                                              evalSym fuel ρ nilAlt)])))).mp
                                      (by simpa [hlen, h0, h1, pcHolds] using hparts.2)
                                  exact False.elim (evalBoolIs_true_false_contra hcovered hnot)
                                | some consAlt =>
                                  have hnilEval :
                                      SmtSem.eval m (SExpr.all [SExpr.isCtor "VDataList" e,
                                        SExpr.isCtor "DNil" (.app "unVDataList" [e])]) =
                                        some (.bool true) :=
                                    (Moist.SMT.Semantics.evalBoolIs_true_eq m
                                      (SExpr.all [SExpr.isCtor "VDataList" e,
                                        SExpr.isCtor "DNil" (.app "unVDataList" [e])])).mp hnilGuard
                                  have hconsBool :
                                      ∃ b, SmtSem.eval m (SExpr.all [SExpr.isCtor "VDataList" e,
                                        (SExpr.isCtor "DNil" (.app "unVDataList" [e])).not]) =
                                        some (.bool b) := by
                                    have hisListEval :
                                        SmtSem.eval m (SExpr.isCtor "VDataList" e) =
                                          some (.bool true) :=
                                      (Moist.SMT.Semantics.evalBoolIs_true_eq m
                                        (SExpr.isCtor "VDataList" e)).mp hparts.1
                                    have hnilEval0 :
                                        SmtSem.eval m (SExpr.isCtor "DNil" (.app "unVDataList" [e])) =
                                          some (.bool true) :=
                                      (Moist.SMT.Semantics.evalBoolIs_true_eq m
                                        (SExpr.isCtor "DNil" (.app "unVDataList" [e]))).mp hnil
                                    have hnotNilEval :=
                                      eval_not_of_bool (m := m)
                                        (e := SExpr.isCtor "DNil" (.app "unVDataList" [e]))
                                        (b := true) hnilEval0
                                    exact evalBoolExists_all2 (m := m) hisListEval hnotNilEval
                                  have hcovered : pcHolds m (SExpr.any
                                      (List.map Prod.fst
                                        ([(SExpr.all [SExpr.isCtor "VDataList" e,
                                            (SExpr.isCtor "DNil" (.app "unVDataList" [e])).not],
                                            bindOut (evalSym fuel ρ consAlt) fun vAlt =>
                                              applyListSym fuel vAlt
                                                [fieldFromDataList (.app "unVDataList" [e]),
                                                  tailFromDataList (.app "unVDataList" [e])])] ++
                                          [(SExpr.all [SExpr.isCtor "VDataList" e,
                                              SExpr.isCtor "DNil" (.app "unVDataList" [e])],
                                              evalSym fuel ρ nilAlt)]))) = true := by
                                    have hor := evalBoolIs_or_true_of_right (m := m)
                                      (a := SExpr.all [SExpr.isCtor "VDataList" e,
                                        (SExpr.isCtor "DNil" (.app "unVDataList" [e])).not])
                                      (b := SExpr.all [SExpr.isCtor "VDataList" e,
                                        SExpr.isCtor "DNil" (.app "unVDataList" [e])])
                                      hconsBool hnilEval
                                    simpa [SExpr.any, Moist.SMT.Expr.any, pcHolds] using hor
                                  have hnot := (Moist.SMT.Semantics.evalBoolIs_not_true m
                                      (SExpr.any
                                        (List.map Prod.fst
                                          ([(SExpr.all [SExpr.isCtor "VDataList" e,
                                              (SExpr.isCtor "DNil" (.app "unVDataList" [e])).not],
                                              bindOut (evalSym fuel ρ consAlt) fun vAlt =>
                                                applyListSym fuel vAlt
                                                  [fieldFromDataList (.app "unVDataList" [e]),
                                                    tailFromDataList (.app "unVDataList" [e])])] ++
                                            [(SExpr.all [SExpr.isCtor "VDataList" e,
                                                SExpr.isCtor "DNil" (.app "unVDataList" [e])],
                                                evalSym fuel ρ nilAlt)])))).mp
                                      (by simpa [hlen, h0, h1, pcHolds] using hparts.2)
                                  exact False.elim (evalBoolIs_true_false_contra hcovered hnot)
                            | cons head tail =>
                              cases h0 : alts[0]? with
                              | none =>
                                simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen, h0]
                              | some consAlt =>
                                have hfalse :=
                                  Moist.SMT.Semantics.evalBoolIs_isDNil_false_of_dataList_cons hxsEval
                                have hnotNil :
                                    pcHolds m (SExpr.not (SExpr.isCtor "DNil"
                                      (.app "unVDataList" [e]))) = true :=
                                  (Moist.SMT.Semantics.evalBoolIs_not_true m
                                    (SExpr.isCtor "DNil" (.app "unVDataList" [e]))).mpr hfalse
                                have hconsGuard :
                                    pcHolds m (SExpr.all [SExpr.isCtor "VDataList" e,
                                      (SExpr.isCtor "DNil" (.app "unVDataList" [e])).not]) = true :=
                                  pcHolds_all2_intro (m := m) hparts.1 hnotNil
                                cases h1 : alts[1]? with
                                | none =>
                                  have hcovered : pcHolds m (SExpr.any
                                      [SExpr.all [SExpr.isCtor "VDataList" e,
                                        (SExpr.isCtor "DNil" (.app "unVDataList" [e])).not]]) = true := by
                                    simpa [SExpr.any, Moist.SMT.Expr.any, pcHolds] using hconsGuard
                                  have hnot := (Moist.SMT.Semantics.evalBoolIs_not_true m
                                      (SExpr.any [SExpr.all [SExpr.isCtor "VDataList" e,
                                        (SExpr.isCtor "DNil" (.app "unVDataList" [e])).not]])).mp
                                      (by simpa [hlen, h0, h1, pcHolds] using hparts.2)
                                  exact False.elim (evalBoolIs_true_false_contra hcovered hnot)
                                | some nilAlt =>
                                  have hconsEval :
                                      SmtSem.eval m (SExpr.all [SExpr.isCtor "VDataList" e,
                                        (SExpr.isCtor "DNil" (.app "unVDataList" [e])).not]) =
                                        some (.bool true) :=
                                    (Moist.SMT.Semantics.evalBoolIs_true_eq m
                                      (SExpr.all [SExpr.isCtor "VDataList" e,
                                        (SExpr.isCtor "DNil" (.app "unVDataList" [e])).not])).mp hconsGuard
                                  have hnilBool :
                                      ∃ b, SmtSem.eval m (SExpr.all [SExpr.isCtor "VDataList" e,
                                        SExpr.isCtor "DNil" (.app "unVDataList" [e])]) =
                                        some (.bool b) := by
                                    have hisListEval :
                                        SmtSem.eval m (SExpr.isCtor "VDataList" e) =
                                          some (.bool true) :=
                                      (Moist.SMT.Semantics.evalBoolIs_true_eq m
                                        (SExpr.isCtor "VDataList" e)).mp hparts.1
                                    have hnilEvalFalse :
                                        SmtSem.eval m (SExpr.isCtor "DNil" (.app "unVDataList" [e])) =
                                          some (.bool false) :=
                                      evalBoolIs_false_eq.mp hfalse
                                    exact evalBoolExists_all2 (m := m) hisListEval hnilEvalFalse
                                  have hcovered : pcHolds m (SExpr.any
                                      (List.map Prod.fst
                                        ([(SExpr.all [SExpr.isCtor "VDataList" e,
                                            (SExpr.isCtor "DNil" (.app "unVDataList" [e])).not],
                                            bindOut (evalSym fuel ρ consAlt) fun vAlt =>
                                              applyListSym fuel vAlt
                                                [fieldFromDataList (.app "unVDataList" [e]),
                                                  tailFromDataList (.app "unVDataList" [e])])] ++
                                          [(SExpr.all [SExpr.isCtor "VDataList" e,
                                              SExpr.isCtor "DNil" (.app "unVDataList" [e])],
                                              evalSym fuel ρ nilAlt)]))) = true := by
                                    have hor := evalBoolIs_or_true_of_left (m := m)
                                      (a := SExpr.all [SExpr.isCtor "VDataList" e,
                                        (SExpr.isCtor "DNil" (.app "unVDataList" [e])).not])
                                      (b := SExpr.all [SExpr.isCtor "VDataList" e,
                                        SExpr.isCtor "DNil" (.app "unVDataList" [e])])
                                      hconsEval hnilBool
                                    simpa [SExpr.any, Moist.SMT.Expr.any, pcHolds] using hor
                                  have hnot := (Moist.SMT.Semantics.evalBoolIs_not_true m
                                      (SExpr.any
                                        (List.map Prod.fst
                                          ([(SExpr.all [SExpr.isCtor "VDataList" e,
                                              (SExpr.isCtor "DNil" (.app "unVDataList" [e])).not],
                                              bindOut (evalSym fuel ρ consAlt) fun vAlt =>
                                                applyListSym fuel vAlt
                                                  [fieldFromDataList (.app "unVDataList" [e]),
                                                    tailFromDataList (.app "unVDataList" [e])])] ++
                                            [(SExpr.all [SExpr.isCtor "VDataList" e,
                                                SExpr.isCtor "DNil" (.app "unVDataList" [e])],
                                                evalSym fuel ρ nilAlt)])))).mp
                                      (by simpa [hlen, h0, h1, pcHolds] using hparts.2)
                                  exact False.elim (evalBoolIs_true_false_contra hcovered hnot)
                        · rcases hrest with hpairErr | hrest
                          · rw [hpairErr] at hg
                            have hpairPc : pcHolds m (SExpr.isCtor "VPair" e) = true :=
                              pcHolds_if_and_left (m := m) (p := 1 < alts.length)
                                (a := SExpr.isCtor "VPair" e)
                                (b := SExpr.not (SExpr.any (List.map Prod.fst
                                  (if 1 < alts.length then []
                                  else
                                    match alts[0]? with
                                    | some alt =>
                                      [(SExpr.isCtor "VPair" e,
                                        bindOut (evalSym fuel ρ alt) fun vAlt =>
                                          applyListSym fuel vAlt
                                            [SymVal.dyn (.app "vfst" [e]),
                                              SymVal.dyn (.app "vsnd" [e])])]
                                    | none => []))))
                                (by simpa [pcHolds] using hg)
                            obtain ⟨a, b, hePair⟩ :=
                              Moist.SMT.Semantics.evalBoolIs_isVPair_true hpairPc
                            rw [he] at hePair
                            cases hePair
                          · rcases hrest with hpairDataErr | hrest
                            · rw [hpairDataErr] at hg
                              have hpairDataPc : pcHolds m (SExpr.isCtor "VPairData" e) = true :=
                                pcHolds_if_and_left (m := m) (p := 1 < alts.length)
                                  (a := SExpr.isCtor "VPairData" e)
                                  (b := SExpr.not (SExpr.any (List.map Prod.fst
                                    (if 1 < alts.length then []
                                    else
                                      match alts[0]? with
                                      | some alt =>
                                        [(SExpr.isCtor "VPairData" e,
                                          bindOut (evalSym fuel ρ alt) fun vAlt =>
                                            applyListSym fuel vAlt
                                              [SymVal.const (.data (.app "pdfst" [e])),
                                                SymVal.const (.data (.app "pdsnd" [e]))])]
                                      | none => []))))
                                  (by simpa [pcHolds] using hg)
                              obtain ⟨a, b, hePairData⟩ :=
                                Moist.SMT.Semantics.evalBoolIs_isVPairData_true hpairDataPc
                              rw [he] at hePairData
                              cases hePairData
                            · rcases hrest with hconstrErr | hunsupportedErr
                              · rw [hconstrErr] at hg
                                have hconstrPc :=
                                  pcHolds_and_left (m := m)
                                    (a := SExpr.isCtor "VConstr" e)
                                    (b := SExpr.not (SExpr.any ((enumerate alts).map fun (j, _) =>
                                      SExpr.eq (.app "vConstrTag" [e]) (.int (Int.ofNat j)))))
                                    (by simpa [pcHolds] using hg)
                                obtain ⟨tag, fields, heConstr⟩ :=
                                  Moist.SMT.Semantics.evalBoolIs_isVConstr_true hconstrPc
                                rw [he] at heConstr
                                cases heConstr
                              · rcases hunsupportedErr with hunsupportedErr | hnil
                                · rw [hunsupportedErr] at hg
                                  exact False.elim
                                    (unsupportedCaseGuard_false_of_supported
                                      (m := m) (e := e) (semv := .dataList xs)
                                      (by simpa [pcHolds, unsupportedCaseGuard] using hg)
                                      he (by simp))
                                · simp at hnil
              | pair a b =>
                cases ha : semValToConst? a with
                | none =>
                  simp [symValToCek?, semValToCek?, semValToConst?, he, ha] at hscrut
                | some ca =>
                  cases hb : semValToConst? b with
                  | none =>
                    simp [symValToCek?, semValToCek?, semValToConst?, he, ha, hb] at hscrut
                  | some cb =>
                    simp [symValToCek?, semValToCek?, semValToConst?, he, ha, hb] at hscrut
                    subst cscrut
                    rcases hgMem with hboolErr | hrest
                    · rw [hboolErr] at hg
                      have hboolPc : pcHolds m (SExpr.isCtor "VBool" e) = true :=
                        pcHolds_if_and_left (m := m) (p := 2 < alts.length)
                          (a := SExpr.isCtor "VBool" e)
                          (b := SExpr.not (SExpr.any ((enumerate alts).map fun (j, _) =>
                            SExpr.eq (SExpr.ite (.app "unVBool" [e]) (.int 1) (.int 0))
                              (.int (Int.ofNat j)))))
                          (by simpa [pcHolds] using hg)
                      obtain ⟨bv, heBool⟩ :=
                        Moist.SMT.Semantics.evalBoolIs_isVBool_true hboolPc
                      rw [he] at heBool
                      cases heBool
                    · rcases hrest with hunitErr | hrest
                      · rw [hunitErr] at hg
                        have hunitPc : pcHolds m (SExpr.isCtor "VUnit" e) = true :=
                          pcHolds_if_and_left (m := m) (p := 1 < alts.length)
                            (a := SExpr.isCtor "VUnit" e)
                            (b := SExpr.not (SExpr.any (List.map Prod.fst
                              (if 1 < alts.length then []
                              else
                                match alts[0]? with
                                | some alt => [(SExpr.isCtor "VUnit" e, evalSym fuel ρ alt)]
                                | none => []))))
                            (by simpa [pcHolds] using hg)
                        have heUnit :=
                          Moist.SMT.Semantics.evalBoolIs_isVUnit_true hunitPc
                        rw [he] at heUnit
                        cases heUnit
                      · rcases hrest with hintErr | hrest
                        · rw [hintErr] at hg
                          have hintPc :=
                            pcHolds_and_left (m := m)
                              (a := SExpr.isCtor "VInt" e)
                              (b := SExpr.not (SExpr.and (nonnegGuard (.app "unVInt" [e]))
                                (SExpr.any ((enumerate alts).map fun (j, _) =>
                                  SExpr.eq (.app "unVInt" [e]) (.int (Int.ofNat j))))))
                              (by simpa [pcHolds] using hg)
                          obtain ⟨i, heInt⟩ :=
                            Moist.SMT.Semantics.evalBoolIs_isVInt_true hintPc
                          rw [he] at heInt
                          cases heInt
                        · rcases hrest with hlistErr | hrest
                          · rw [hlistErr] at hg
                            have hlistPc : pcHolds m (SExpr.isCtor "VList" e) = true :=
                              pcHolds_if_and_left (m := m) (p := 2 < alts.length)
                                (a := SExpr.isCtor "VList" e)
                                (b := SExpr.not (SExpr.any (List.map Prod.fst
                                  (if 2 < alts.length then []
                                  else
                                    (match alts[0]? with
                                    | some alt =>
                                      [(SExpr.all [SExpr.isCtor "VList" e,
                                        (SExpr.isCtor "VNil" (.app "unVList" [e])).not],
                                        bindOut (evalSym fuel ρ alt) fun vAlt =>
                                          applyListSym fuel vAlt
                                            [fieldFromValList (.app "unVList" [e]),
                                              tailFromValList (.app "unVList" [e])])]
                                    | none => []) ++
                                    match alts[1]? with
                                    | some alt =>
                                      [(SExpr.all [SExpr.isCtor "VList" e,
                                        SExpr.isCtor "VNil" (.app "unVList" [e])],
                                        evalSym fuel ρ alt)]
                                    | none => []))))
                                (by simpa [pcHolds] using hg)
                            obtain ⟨vals, heList⟩ :=
                              Moist.SMT.Semantics.evalBoolIs_isVList_true hlistPc
                            rw [he] at heList
                            cases heList
                          · rcases hrest with hdataListErr | hrest
                            · rw [hdataListErr] at hg
                              have hdataListPc : pcHolds m (SExpr.isCtor "VDataList" e) = true :=
                                pcHolds_if_and_left (m := m) (p := 2 < alts.length)
                                  (a := SExpr.isCtor "VDataList" e)
                                  (b := SExpr.not (SExpr.any (List.map Prod.fst
                                    (if 2 < alts.length then []
                                    else
                                      (match alts[0]? with
                                      | some alt =>
                                        [(SExpr.all [SExpr.isCtor "VDataList" e,
                                          (SExpr.isCtor "DNil" (.app "unVDataList" [e])).not],
                                          bindOut (evalSym fuel ρ alt) fun vAlt =>
                                            applyListSym fuel vAlt
                                              [fieldFromDataList (.app "unVDataList" [e]),
                                                tailFromDataList (.app "unVDataList" [e])])]
                                      | none => []) ++
                                      match alts[1]? with
                                      | some alt =>
                                        [(SExpr.all [SExpr.isCtor "VDataList" e,
                                          SExpr.isCtor "DNil" (.app "unVDataList" [e])],
                                          evalSym fuel ρ alt)]
                                      | none => []))))
                                  (by simpa [pcHolds] using hg)
                              obtain ⟨xsData, heDataList⟩ :=
                                Moist.SMT.Semantics.evalBoolIs_isVDataList_true hdataListPc
                              rw [he] at heDataList
                              cases heDataList
                            · rcases hrest with hpairErr | hrest
                              · rw [hpairErr] at hg
                                by_cases hlen : 1 < alts.length
                                · simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen]
                                · have hparts :=
                                    (Moist.SMT.Semantics.evalBoolIs_and_true m
                                      (SExpr.isCtor "VPair" e)
                                      (SExpr.not (SExpr.any (List.map Prod.fst
                                        (if 1 < alts.length then []
                                        else
                                          match alts[0]? with
                                          | some alt =>
                                            [(SExpr.isCtor "VPair" e,
                                              bindOut (evalSym fuel ρ alt) fun vAlt =>
                                                applyListSym fuel vAlt
                                                  [SymVal.dyn (.app "vfst" [e]),
                                                    SymVal.dyn (.app "vsnd" [e])])]
                                          | none => []))))).mp
                                      (by simpa [pcHolds, hlen] using hg)
                                  cases h0 : alts[0]? with
                                  | none =>
                                    simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen, h0]
                                  | some alt =>
                                    have hcovered : pcHolds m (SExpr.any
                                        (List.map Prod.fst
                                          ([(SExpr.isCtor "VPair" e,
                                            bindOut (evalSym fuel ρ alt) fun vAlt =>
                                              applyListSym fuel vAlt
                                                [SymVal.dyn (.app "vfst" [e]),
                                                  SymVal.dyn (.app "vsnd" [e])])]))) = true := by
                                      simpa [SExpr.any, Moist.SMT.Expr.any, pcHolds] using hparts.1
                                    have hnot := (Moist.SMT.Semantics.evalBoolIs_not_true m
                                        (SExpr.any
                                          (List.map Prod.fst
                                            ([(SExpr.isCtor "VPair" e,
                                              bindOut (evalSym fuel ρ alt) fun vAlt =>
                                                applyListSym fuel vAlt
                                                  [SymVal.dyn (.app "vfst" [e]),
                                                    SymVal.dyn (.app "vsnd" [e])])])))).mp
                                        (by simpa [hlen, h0, pcHolds] using hparts.2)
                                    exact False.elim (evalBoolIs_true_false_contra hcovered hnot)
                              · rcases hrest with hpairDataErr | hrest
                                · rw [hpairDataErr] at hg
                                  have hpairDataPc : pcHolds m (SExpr.isCtor "VPairData" e) = true :=
                                    pcHolds_if_and_left (m := m) (p := 1 < alts.length)
                                      (a := SExpr.isCtor "VPairData" e)
                                      (b := SExpr.not (SExpr.any (List.map Prod.fst
                                        (if 1 < alts.length then []
                                        else
                                          match alts[0]? with
                                          | some alt =>
                                            [(SExpr.isCtor "VPairData" e,
                                              bindOut (evalSym fuel ρ alt) fun vAlt =>
                                                applyListSym fuel vAlt
                                                  [SymVal.const (.data (.app "pdfst" [e])),
                                                    SymVal.const (.data (.app "pdsnd" [e]))])]
                                          | none => []))))
                                      (by simpa [pcHolds] using hg)
                                  obtain ⟨da, db, hePairData⟩ :=
                                    Moist.SMT.Semantics.evalBoolIs_isVPairData_true hpairDataPc
                                  rw [he] at hePairData
                                  cases hePairData
                                · rcases hrest with hconstrErr | hunsupportedErr
                                  · rw [hconstrErr] at hg
                                    have hconstrPc :=
                                      pcHolds_and_left (m := m)
                                        (a := SExpr.isCtor "VConstr" e)
                                        (b := SExpr.not (SExpr.any ((enumerate alts).map fun (j, _) =>
                                          SExpr.eq (.app "vConstrTag" [e]) (.int (Int.ofNat j)))))
                                        (by simpa [pcHolds] using hg)
                                    obtain ⟨tag, fields, heConstr⟩ :=
                                      Moist.SMT.Semantics.evalBoolIs_isVConstr_true hconstrPc
                                    rw [he] at heConstr
                                    cases heConstr
                                  · rcases hunsupportedErr with hunsupportedErr | hnil
                                    · rw [hunsupportedErr] at hg
                                      exact False.elim
                                        (unsupportedCaseGuard_false_of_supported
                                          (m := m) (e := e) (semv := .pair a b)
                                          (by simpa [pcHolds, unsupportedCaseGuard] using hg)
                                          he (by simp))
                                    · simp at hnil
              | pairData a b =>
                exact by
                  simp [symValToCek?, semValToCek?, semValToConst?, he] at hscrut
                  subst cscrut
                  rcases hgMem with hboolErr | hrest
                  · rw [hboolErr] at hg
                    have hboolPc : pcHolds m (SExpr.isCtor "VBool" e) = true :=
                      pcHolds_if_and_left (m := m) (p := 2 < alts.length)
                        (a := SExpr.isCtor "VBool" e)
                        (b := SExpr.not (SExpr.any ((enumerate alts).map fun (j, _) =>
                          SExpr.eq (SExpr.ite (.app "unVBool" [e]) (.int 1) (.int 0))
                            (.int (Int.ofNat j)))))
                        (by simpa [pcHolds] using hg)
                    obtain ⟨bv, heBool⟩ :=
                      Moist.SMT.Semantics.evalBoolIs_isVBool_true hboolPc
                    rw [he] at heBool
                    cases heBool
                  · rcases hrest with hunitErr | hrest
                    · rw [hunitErr] at hg
                      have hunitPc : pcHolds m (SExpr.isCtor "VUnit" e) = true :=
                        pcHolds_if_and_left (m := m) (p := 1 < alts.length)
                          (a := SExpr.isCtor "VUnit" e)
                          (b := SExpr.not (SExpr.any (List.map Prod.fst
                            (if 1 < alts.length then []
                            else
                              match alts[0]? with
                              | some alt => [(SExpr.isCtor "VUnit" e, evalSym fuel ρ alt)]
                              | none => []))))
                          (by simpa [pcHolds] using hg)
                      have heUnit :=
                        Moist.SMT.Semantics.evalBoolIs_isVUnit_true hunitPc
                      rw [he] at heUnit
                      cases heUnit
                    · rcases hrest with hintErr | hrest
                      · rw [hintErr] at hg
                        have hintPc :=
                          pcHolds_and_left (m := m)
                            (a := SExpr.isCtor "VInt" e)
                            (b := SExpr.not (SExpr.and (nonnegGuard (.app "unVInt" [e]))
                              (SExpr.any ((enumerate alts).map fun (j, _) =>
                                SExpr.eq (.app "unVInt" [e]) (.int (Int.ofNat j))))))
                            (by simpa [pcHolds] using hg)
                        obtain ⟨i, heInt⟩ :=
                          Moist.SMT.Semantics.evalBoolIs_isVInt_true hintPc
                        rw [he] at heInt
                        cases heInt
                      · rcases hrest with hlistErr | hrest
                        · rw [hlistErr] at hg
                          have hlistPc : pcHolds m (SExpr.isCtor "VList" e) = true :=
                            pcHolds_if_and_left (m := m) (p := 2 < alts.length)
                              (a := SExpr.isCtor "VList" e)
                              (b := SExpr.not (SExpr.any (List.map Prod.fst
                                (if 2 < alts.length then []
                                else
                                  (match alts[0]? with
                                  | some alt =>
                                    [(SExpr.all [SExpr.isCtor "VList" e,
                                      (SExpr.isCtor "VNil" (.app "unVList" [e])).not],
                                      bindOut (evalSym fuel ρ alt) fun vAlt =>
                                        applyListSym fuel vAlt
                                          [fieldFromValList (.app "unVList" [e]),
                                            tailFromValList (.app "unVList" [e])])]
                                  | none => []) ++
                                  match alts[1]? with
                                  | some alt =>
                                    [(SExpr.all [SExpr.isCtor "VList" e,
                                      SExpr.isCtor "VNil" (.app "unVList" [e])],
                                      evalSym fuel ρ alt)]
                                  | none => []))))
                              (by simpa [pcHolds] using hg)
                          obtain ⟨vals, heList⟩ :=
                            Moist.SMT.Semantics.evalBoolIs_isVList_true hlistPc
                          rw [he] at heList
                          cases heList
                        · rcases hrest with hdataListErr | hrest
                          · rw [hdataListErr] at hg
                            have hdataListPc : pcHolds m (SExpr.isCtor "VDataList" e) = true :=
                              pcHolds_if_and_left (m := m) (p := 2 < alts.length)
                                (a := SExpr.isCtor "VDataList" e)
                                (b := SExpr.not (SExpr.any (List.map Prod.fst
                                  (if 2 < alts.length then []
                                  else
                                    (match alts[0]? with
                                    | some alt =>
                                      [(SExpr.all [SExpr.isCtor "VDataList" e,
                                        (SExpr.isCtor "DNil" (.app "unVDataList" [e])).not],
                                        bindOut (evalSym fuel ρ alt) fun vAlt =>
                                          applyListSym fuel vAlt
                                            [fieldFromDataList (.app "unVDataList" [e]),
                                              tailFromDataList (.app "unVDataList" [e])])]
                                    | none => []) ++
                                    match alts[1]? with
                                    | some alt =>
                                      [(SExpr.all [SExpr.isCtor "VDataList" e,
                                        SExpr.isCtor "DNil" (.app "unVDataList" [e])],
                                        evalSym fuel ρ alt)]
                                    | none => []))))
                                (by simpa [pcHolds] using hg)
                            obtain ⟨xsData, heDataList⟩ :=
                              Moist.SMT.Semantics.evalBoolIs_isVDataList_true hdataListPc
                            rw [he] at heDataList
                            cases heDataList
                          · rcases hrest with hpairErr | hrest
                            · rw [hpairErr] at hg
                              have hpairPc : pcHolds m (SExpr.isCtor "VPair" e) = true :=
                                pcHolds_if_and_left (m := m) (p := 1 < alts.length)
                                  (a := SExpr.isCtor "VPair" e)
                                  (b := SExpr.not (SExpr.any (List.map Prod.fst
                                    (if 1 < alts.length then []
                                    else
                                      match alts[0]? with
                                      | some alt =>
                                        [(SExpr.isCtor "VPair" e,
                                          bindOut (evalSym fuel ρ alt) fun vAlt =>
                                            applyListSym fuel vAlt
                                              [SymVal.dyn (.app "vfst" [e]),
                                                SymVal.dyn (.app "vsnd" [e])])]
                                      | none => []))))
                                  (by simpa [pcHolds] using hg)
                              obtain ⟨pa, pb, hePair⟩ :=
                                Moist.SMT.Semantics.evalBoolIs_isVPair_true hpairPc
                              rw [he] at hePair
                              cases hePair
                            · rcases hrest with hpairDataErr | hrest
                              · rw [hpairDataErr] at hg
                                by_cases hlen : 1 < alts.length
                                · simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen]
                                · have hparts :=
                                    (Moist.SMT.Semantics.evalBoolIs_and_true m
                                      (SExpr.isCtor "VPairData" e)
                                      (SExpr.not (SExpr.any (List.map Prod.fst
                                        (if 1 < alts.length then []
                                        else
                                          match alts[0]? with
                                          | some alt =>
                                            [(SExpr.isCtor "VPairData" e,
                                              bindOut (evalSym fuel ρ alt) fun vAlt =>
                                                applyListSym fuel vAlt
                                                  [SymVal.const (.data (.app "pdfst" [e])),
                                                    SymVal.const (.data (.app "pdsnd" [e]))])]
                                          | none => []))))).mp
                                      (by simpa [pcHolds, hlen] using hg)
                                  cases h0 : alts[0]? with
                                  | none =>
                                    simp [caseCekResult, Moist.CEK.constToTagAndFields, hlen, h0]
                                  | some alt =>
                                    have hcovered : pcHolds m (SExpr.any
                                        (List.map Prod.fst
                                          ([(SExpr.isCtor "VPairData" e,
                                            bindOut (evalSym fuel ρ alt) fun vAlt =>
                                              applyListSym fuel vAlt
                                                [SymVal.const (.data (.app "pdfst" [e])),
                                                  SymVal.const (.data (.app "pdsnd" [e]))])]))) = true := by
                                      simpa [SExpr.any, Moist.SMT.Expr.any, pcHolds] using hparts.1
                                    have hnot := (Moist.SMT.Semantics.evalBoolIs_not_true m
                                        (SExpr.any
                                          (List.map Prod.fst
                                            ([(SExpr.isCtor "VPairData" e,
                                              bindOut (evalSym fuel ρ alt) fun vAlt =>
                                                applyListSym fuel vAlt
                                                  [SymVal.const (.data (.app "pdfst" [e])),
                                                    SymVal.const (.data (.app "pdsnd" [e]))])])))).mp
                                        (by simpa [hlen, h0, pcHolds] using hparts.2)
                                    exact False.elim (evalBoolIs_true_false_contra hcovered hnot)
                              · rcases hrest with hconstrErr | hunsupportedErr
                                · rw [hconstrErr] at hg
                                  have hconstrPc :=
                                    pcHolds_and_left (m := m)
                                      (a := SExpr.isCtor "VConstr" e)
                                      (b := SExpr.not (SExpr.any ((enumerate alts).map fun (j, _) =>
                                        SExpr.eq (.app "vConstrTag" [e]) (.int (Int.ofNat j)))))
                                      (by simpa [pcHolds] using hg)
                                  obtain ⟨tag, fields, heConstr⟩ :=
                                    Moist.SMT.Semantics.evalBoolIs_isVConstr_true hconstrPc
                                  rw [he] at heConstr
                                  cases heConstr
                                · rcases hunsupportedErr with hunsupportedErr | hnil
                                  · rw [hunsupportedErr] at hg
                                    exact False.elim
                                      (unsupportedCaseGuard_false_of_supported
                                        (m := m) (e := e) (semv := .pairData a b)
                                        (by simpa [pcHolds, unsupportedCaseGuard] using hg)
                                        he (by simp))
                                  · simp at hnil
              | constr tag fields =>
                exact by
                  by_cases hneg : tag < 0
                  · simp [symValToCek?, semValToCek?, he, hneg] at hscrut
                  · cases hfields : semValListToCekList? fields with
                    | none =>
                      simp [symValToCek?, semValToCek?, he, hneg, hfields] at hscrut
                    | some cfields =>
                      simp [symValToCek?, semValToCek?, he, hneg, hfields] at hscrut
                      subst cscrut
                      rcases hgMem with hboolErr | hrest
                      · rw [hboolErr] at hg
                        have hboolPc : pcHolds m (SExpr.isCtor "VBool" e) = true :=
                          pcHolds_if_and_left (m := m) (p := 2 < alts.length)
                            (a := SExpr.isCtor "VBool" e)
                            (b := SExpr.not (SExpr.any ((enumerate alts).map fun (j, _) =>
                              SExpr.eq (SExpr.ite (.app "unVBool" [e]) (.int 1) (.int 0))
                                (.int (Int.ofNat j)))))
                            (by simpa [pcHolds] using hg)
                        obtain ⟨bv, heBool⟩ :=
                          Moist.SMT.Semantics.evalBoolIs_isVBool_true hboolPc
                        rw [he] at heBool
                        cases heBool
                      · rcases hrest with hunitErr | hrest
                        · rw [hunitErr] at hg
                          have hunitPc : pcHolds m (SExpr.isCtor "VUnit" e) = true :=
                            pcHolds_if_and_left (m := m) (p := 1 < alts.length)
                              (a := SExpr.isCtor "VUnit" e)
                              (b := SExpr.not (SExpr.any (List.map Prod.fst
                                (if 1 < alts.length then []
                                else
                                  match alts[0]? with
                                  | some alt => [(SExpr.isCtor "VUnit" e, evalSym fuel ρ alt)]
                                  | none => []))))
                              (by simpa [pcHolds] using hg)
                          have heUnit :=
                            Moist.SMT.Semantics.evalBoolIs_isVUnit_true hunitPc
                          rw [he] at heUnit
                          cases heUnit
                        · rcases hrest with hintErr | hrest
                          · rw [hintErr] at hg
                            have hintPc :=
                              pcHolds_and_left (m := m)
                                (a := SExpr.isCtor "VInt" e)
                                (b := SExpr.not (SExpr.and (nonnegGuard (.app "unVInt" [e]))
                                  (SExpr.any ((enumerate alts).map fun (j, _) =>
                                    SExpr.eq (.app "unVInt" [e]) (.int (Int.ofNat j))))))
                                (by simpa [pcHolds] using hg)
                            obtain ⟨i, heInt⟩ :=
                              Moist.SMT.Semantics.evalBoolIs_isVInt_true hintPc
                            rw [he] at heInt
                            cases heInt
                          · rcases hrest with hlistErr | hrest
                            · rw [hlistErr] at hg
                              have hlistPc : pcHolds m (SExpr.isCtor "VList" e) = true :=
                                pcHolds_if_and_left (m := m) (p := 2 < alts.length)
                                  (a := SExpr.isCtor "VList" e)
                                  (b := SExpr.not (SExpr.any (List.map Prod.fst
                                    (if 2 < alts.length then []
                                    else
                                      (match alts[0]? with
                                      | some alt =>
                                        [(SExpr.all [SExpr.isCtor "VList" e,
                                          (SExpr.isCtor "VNil" (.app "unVList" [e])).not],
                                          bindOut (evalSym fuel ρ alt) fun vAlt =>
                                            applyListSym fuel vAlt
                                              [fieldFromValList (.app "unVList" [e]),
                                                tailFromValList (.app "unVList" [e])])]
                                      | none => []) ++
                                      match alts[1]? with
                                      | some alt =>
                                        [(SExpr.all [SExpr.isCtor "VList" e,
                                          SExpr.isCtor "VNil" (.app "unVList" [e])],
                                          evalSym fuel ρ alt)]
                                      | none => []))))
                                  (by simpa [pcHolds] using hg)
                              obtain ⟨vals, heList⟩ :=
                                Moist.SMT.Semantics.evalBoolIs_isVList_true hlistPc
                              rw [he] at heList
                              cases heList
                            · rcases hrest with hdataListErr | hrest
                              · rw [hdataListErr] at hg
                                have hdataListPc : pcHolds m (SExpr.isCtor "VDataList" e) = true :=
                                  pcHolds_if_and_left (m := m) (p := 2 < alts.length)
                                    (a := SExpr.isCtor "VDataList" e)
                                    (b := SExpr.not (SExpr.any (List.map Prod.fst
                                      (if 2 < alts.length then []
                                      else
                                        (match alts[0]? with
                                        | some alt =>
                                          [(SExpr.all [SExpr.isCtor "VDataList" e,
                                            (SExpr.isCtor "DNil" (.app "unVDataList" [e])).not],
                                            bindOut (evalSym fuel ρ alt) fun vAlt =>
                                              applyListSym fuel vAlt
                                                [fieldFromDataList (.app "unVDataList" [e]),
                                                  tailFromDataList (.app "unVDataList" [e])])]
                                        | none => []) ++
                                        match alts[1]? with
                                        | some alt =>
                                          [(SExpr.all [SExpr.isCtor "VDataList" e,
                                            SExpr.isCtor "DNil" (.app "unVDataList" [e])],
                                            evalSym fuel ρ alt)]
                                        | none => []))))
                                    (by simpa [pcHolds] using hg)
                                obtain ⟨xsData, heDataList⟩ :=
                                  Moist.SMT.Semantics.evalBoolIs_isVDataList_true hdataListPc
                                rw [he] at heDataList
                                cases heDataList
                              · rcases hrest with hpairErr | hrest
                                · rw [hpairErr] at hg
                                  have hpairPc : pcHolds m (SExpr.isCtor "VPair" e) = true :=
                                    pcHolds_if_and_left (m := m) (p := 1 < alts.length)
                                      (a := SExpr.isCtor "VPair" e)
                                      (b := SExpr.not (SExpr.any (List.map Prod.fst
                                        (if 1 < alts.length then []
                                        else
                                          match alts[0]? with
                                          | some alt =>
                                            [(SExpr.isCtor "VPair" e,
                                              bindOut (evalSym fuel ρ alt) fun vAlt =>
                                                applyListSym fuel vAlt
                                                  [SymVal.dyn (.app "vfst" [e]),
                                                    SymVal.dyn (.app "vsnd" [e])])]
                                          | none => []))))
                                      (by simpa [pcHolds] using hg)
                                  obtain ⟨pa, pb, hePair⟩ :=
                                    Moist.SMT.Semantics.evalBoolIs_isVPair_true hpairPc
                                  rw [he] at hePair
                                  cases hePair
                                · rcases hrest with hpairDataErr | hrest
                                  · rw [hpairDataErr] at hg
                                    have hpairDataPc : pcHolds m (SExpr.isCtor "VPairData" e) = true :=
                                      pcHolds_if_and_left (m := m) (p := 1 < alts.length)
                                        (a := SExpr.isCtor "VPairData" e)
                                        (b := SExpr.not (SExpr.any (List.map Prod.fst
                                          (if 1 < alts.length then []
                                          else
                                            match alts[0]? with
                                            | some alt =>
                                              [(SExpr.isCtor "VPairData" e,
                                                bindOut (evalSym fuel ρ alt) fun vAlt =>
                                                  applyListSym fuel vAlt
                                                    [SymVal.const (.data (.app "pdfst" [e])),
                                                      SymVal.const (.data (.app "pdsnd" [e]))])]
                                            | none => []))))
                                        (by simpa [pcHolds] using hg)
                                    obtain ⟨da, db, hePairData⟩ :=
                                      Moist.SMT.Semantics.evalBoolIs_isVPairData_true hpairDataPc
                                    rw [he] at hePairData
                                    cases hePairData
                                  · rcases hrest with hconstrErr | hunsupportedErr
                                    · rw [hconstrErr] at hg
                                      have hparts :=
                                        (Moist.SMT.Semantics.evalBoolIs_and_true m
                                          (SExpr.isCtor "VConstr" e)
                                          (SExpr.not (SExpr.any ((enumerate alts).map fun (j, _) =>
                                            SExpr.eq (.app "vConstrTag" [e]) (.int (Int.ofNat j)))))).mp
                                          (by simpa [pcHolds] using hg)
                                      have htagEval :=
                                        Moist.SMT.Semantics.eval_vConstrTag_of (m := m)
                                          (e := e) (tag := tag) (fields := fields) he
                                      have hnonneg : 0 ≤ tag := by omega
                                      cases hget : alts[tag.toNat]? with
                                      | some alt =>
                                        have htagNat : tag = Int.ofNat tag.toNat := by
                                          exact (Int.toNat_of_nonneg hnonneg).symm
                                        have hcovered := tagCovered_true_of_get (m := m)
                                          (alts := alts) (tagExpr := .app "vConstrTag" [e])
                                          (tagInt := tag) (i := tag.toNat) (alt := alt)
                                          htagEval htagNat hget
                                        have hnot := (Moist.SMT.Semantics.evalBoolIs_not_true m
                                          (SExpr.any ((enumerate alts).map fun (j, _) =>
                                            SExpr.eq (.app "vConstrTag" [e]) (.int (Int.ofNat j))))).mp
                                          (by simpa [pcHolds] using hparts.2)
                                        exact False.elim (evalBoolIs_true_false_contra hcovered hnot)
                                      | none =>
                                        simp [caseCekResult, hget]
                                    · rcases hunsupportedErr with hunsupportedErr | hnil
                                      · rw [hunsupportedErr] at hg
                                        exact False.elim
                                          (unsupportedCaseGuard_false_of_supported
                                            (m := m) (e := e) (semv := .constr tag fields)
                                            (by simpa [pcHolds, unsupportedCaseGuard] using hg)
                                            he (by simp))
                                      · simp at hnil
          | bool b => simp [symValToCek?, he] at hscrut
          | int i => simp [symValToCek?, he] at hscrut
          | string s => simp [symValToCek?, he] at hscrut
          | bytes bs => simp [symValToCek?, he] at hscrut
          | data d => simp [symValToCek?, he] at hscrut
          | dataList xs => simp [symValToCek?, he] at hscrut
          | dataPairList xs => simp [symValToCek?, he] at hscrut
          | valList xs => simp [symValToCek?, he] at hscrut
          | g1 g => simp [symValToCek?, he] at hscrut
          | g2 g => simp [symValToCek?, he] at hscrut
          | ml r => simp [symValToCek?, he] at hscrut
end

theorem errorCond_eval_true_mem {m : SmtSem.Model} {outs : List Outcome}
    (h : SmtSem.evalBoolIs m (errorCond outs) true = true) :
    ∃ out, out ∈ outs ∧ outcomeErrorActive m out = true := by
  obtain ⟨pc, hpcMem, hpcTrue⟩ := evalBoolIs_any_true (m := m)
    (xs := outs.filterMap fun
      | .error pc => some pc
      | _ => none)
    (by simpa [errorCond] using h)
  simp only [List.mem_filterMap] at hpcMem
  rcases hpcMem with ⟨out, houtMem, hmap⟩
  cases out with
  | ok pc' v => simp at hmap
  | timeout pc' => simp at hmap
  | error pc' =>
      simp at hmap
      subst pc
      exact ⟨Outcome.error pc', houtMem, by simpa [outcomeErrorActive, pcHolds] using hpcTrue⟩

theorem okBoolTrueCond_eval_true_mem {m : SmtSem.Model} {outs : List Outcome}
    (h : SmtSem.evalBoolIs m (okBoolTrueCond outs) true = true) :
    ∃ out sv, out ∈ outs ∧
      outcomeOkSym? m out = some (sv, .VCon (.Bool true)) := by
  obtain ⟨pc, hpcMem, hpcTrue⟩ := evalBoolIs_any_true (m := m)
    (xs := outs.filterMap fun
      | .ok pc v =>
          let b := asBool v
          some (SExpr.all [pc, b.guard, b.val])
      | _ => none)
    (by simpa [okBoolTrueCond] using h)
  simp only [List.mem_filterMap] at hpcMem
  rcases hpcMem with ⟨out, houtMem, hmap⟩
  cases out with
  | error pc0 => simp at hmap
  | timeout pc0 => simp at hmap
  | ok pc0 v =>
      simp at hmap
      subst pc
      have hpair1 :=
        (Moist.SMT.Semantics.evalBoolIs_and_true m
          (SExpr.and pc0 (asBool v).guard) (asBool v).val).mp hpcTrue
      have hpair0 :=
        (Moist.SMT.Semantics.evalBoolIs_and_true m pc0 (asBool v).guard).mp hpair1.1
      have hpc : pcHolds m pc0 = true := by simpa [pcHolds] using hpair0.1
      have hg : pcHolds m (asBool v).guard = true := by simpa [pcHolds] using hpair0.2
      have hv : SmtSem.evalBoolIs m (asBool v).val true = true := hpair1.2
      have hcek := asBool_true_to_cek (m := m) (v := v) hg hv
      exact ⟨Outcome.ok pc0 v, v, houtMem, by simp [outcomeOkSym?, hpc, hcek]⟩

theorem evalSym_errorCond_sound {m : SmtSem.Model} {fuel : Nat} {ρ : List SymVal}
    {env : CekEnv} {t : Term}
    (henv : symEnvToCek? m ρ = some env)
    (hρno : symEnvNoOpaqueForSoundness ρ = true)
    (hno : termNoOpaqueBuiltinsForSoundness t)
    (herror : SmtSem.evalBoolIs m (errorCond (evalSym fuel ρ t)) true = true) :
    bigEval fuel env t = none := by
  obtain ⟨out, hmem, herr⟩ := errorCond_eval_true_mem herror
  exact evalSym_active_error_noOpaque_le (m := m) (fuel := fuel) (fuel' := fuel)
    (ρ := ρ) (env := env) (t := t) henv hρno hno hmem herr (Nat.le_refl fuel)

theorem evalSym_okBoolTrueCond_sound {m : SmtSem.Model} {fuel : Nat} {ρ : List SymVal}
    {env : CekEnv} {t : Term}
    (henv : symEnvToCek? m ρ = some env)
    (hρno : symEnvNoOpaqueForSoundness ρ = true)
    (hno : termNoOpaqueBuiltinsForSoundness t)
    (hokCond : SmtSem.evalBoolIs m (okBoolTrueCond (evalSym fuel ρ t)) true = true) :
    bigEval fuel env t = some (.VCon (.Bool true)) := by
  obtain ⟨out, sv, hmem, hok⟩ := okBoolTrueCond_eval_true_mem hokCond
  cases out with
  | ok pc v =>
      have hok' := outcomeOkSym_ok hok
      have hpath := evalSym_path_ok_noOpaque (m := m) (fuel := fuel)
        (ρ := ρ) (env := env) (t := t)
        henv hρno hno hmem hok'.1
      rcases hpath with ⟨cv, hv, _hnov, hbig⟩
      rw [hok'.2.2] at hv
      injection hv with hcv
      subst cv
      exact hbig
  | error pc =>
      simp [outcomeOkSym?] at hok
  | timeout pc =>
      simp [outcomeOkSym?] at hok

def cekFails (t : Term) : Bool :=
  match bigEval 20 .nil t with
  | none => true
  | some _ => false

def smtBoolTrue (m : SmtSem.Model) (e : SExpr) : Bool :=
  SmtSem.evalBoolIs m e true

theorem sha2Refl_cek_fails :
    cekFails sha2Refl = true := by
  native_decide

theorem sha2Refl_opaque_smt_not_executable_in_internal_semantics :
    smtBoolTrue emptyModel (okBoolTrueCond (evalSym 20 [] sha2Refl)) = false ∧
    smtBoolTrue emptyModel (errorCond (evalSym 20 [] sha2Refl)) = false ∧
    smtBoolTrue emptyModel (timeoutCond (evalSym 20 [] sha2Refl)) = false := by
  native_decide

theorem recursiveSum10_bigEval_55 :
    bigEvalIntEq 100 (envInt 10) recursiveSumTerm 55 = true := by
  native_decide

theorem equalsIntegerAdd_smt_semantics_x5 :
    let outs := evalSym 20 (envOf [symInt "x"]) equalsIntegerAddExample
    SmtSem.evalBoolIs (modelInt "x" 5) (okBoolTrueCond outs) true = true ∧
    anyOkBoolTrue (modelInt "x" 5) outs = true := by
  native_decide

theorem equalsIntegerAdd_cek_x5 :
    bigEvalBoolTrue 20 (envInt 5) equalsIntegerAddExample = true := by
  native_decide

theorem caseInteger_smt_semantics_x2 :
    let outs := evalSym 20 (envOf [symInt "x"]) caseIntegerExample
    SmtSem.evalBoolIs (modelInt "x" 2) (okBoolTrueCond outs) true = true ∧
    anyOkBoolTrue (modelInt "x" 2) outs = true := by
  native_decide

theorem caseInteger_cek_x2 :
    bigEvalBoolTrue 20 (envInt 2) caseIntegerExample = true := by
  native_decide

theorem caseIfConstr_smt_semantics_x10 :
    let outs := evalSym 30 (envOf [symInt "x"]) caseIfConstrExample
    SmtSem.evalBoolIs (modelInt "x" 10) (okBoolTrueCond outs) true = true ∧
    anyOkBoolTrue (modelInt "x" 10) outs = true := by
  native_decide

theorem caseIfConstr_cek_x10 :
    bigEvalBoolTrue 30 (envInt 10) caseIfConstrExample = true := by
  native_decide

theorem caseEmptyConstListMissingNil_smt_error :
    let outs := evalSym 20 [] caseEmptyConstListMissingNilExample
    SmtSem.evalBoolIs emptyModel (errorCond outs) true = true ∧
    anyErrorOutcome emptyModel outs = true := by
  native_decide

theorem caseEmptyConstListMissingNil_cek_fails :
    bigEvalFails 20 .nil caseEmptyConstListMissingNilExample = true := by
  native_decide

theorem mkConsRejectsRuntimeConstr_smt_error :
    let outs := evalSym 20 [] mkConsRejectsRuntimeConstrExample
    SmtSem.evalBoolIs emptyModel (errorCond outs) true = true ∧
    anyErrorOutcome emptyModel outs = true := by
  native_decide

theorem mkConsRejectsRuntimeConstr_cek_fails :
    bigEvalFails 20 .nil mkConsRejectsRuntimeConstrExample = true := by
  native_decide

theorem sha2Refl_uses_opaque_builtin :
    termUsesOpaqueBuiltinForSoundness sha2Refl = true := by
  native_decide

theorem equalsIntegerAdd_no_opaque :
    termNoOpaqueBuiltinsForSoundness equalsIntegerAddExample := by
  unfold termNoOpaqueBuiltinsForSoundness
  native_decide

theorem caseInteger_no_opaque :
    termNoOpaqueBuiltinsForSoundness caseIntegerExample := by
  unfold termNoOpaqueBuiltinsForSoundness
  native_decide

theorem caseIfConstr_no_opaque :
    termNoOpaqueBuiltinsForSoundness caseIfConstrExample := by
  unfold termNoOpaqueBuiltinsForSoundness
  native_decide

end Moist.SMT.UPLC.Soundness
