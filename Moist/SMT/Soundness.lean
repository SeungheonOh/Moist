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
  | .EncodeUtf8 | .DecodeUtf8
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
    | .g1 _ => some (.VCon .Bls12_381_G1_element)
    | .g2 _ => some (.VCon .Bls12_381_G2_element)
    | .ml _ => some (.VCon .Bls12_381_MlResult)

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

theorem evalBoolIs_false_eq {m : SmtSem.Model} {e : SExpr} :
    SmtSem.evalBoolIs m e false = true ↔ SmtSem.eval m e = some (.bool false) := by
  unfold SmtSem.evalBoolIs Moist.SMT.Semantics.evalBoolIs
    Moist.SMT.Semantics.evalBool?
  cases he : SmtSem.eval m e with
  | none =>
      simp [he]
  | some v =>
      cases v <;> simp [he]

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
    (by simp [constLiteral, symValToCek?, symConstToCek?])
    (by simp [constLiteral, symValToCek?, symConstToCek?])
    (by simp [constLiteral, symValToCek?, symConstToCek?])
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
    subst cv
    exact ⟨_, rfl⟩
  case g2 e =>
    subst cv
    exact ⟨_, rfl⟩
  case ml e =>
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

def BuiltinOkSound (b : BuiltinFun) : Prop :=
  ∀ {m : SmtSem.Model} {args : List SymVal} {cargs : List CekValue}
    {pc : SExpr} {v : SymVal},
    symValListToCekList? m args = some cargs →
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

axiom evalBuiltinSym_active_ok_AddInteger : BuiltinOkSound .AddInteger
axiom evalBuiltinSym_active_ok_SubtractInteger : BuiltinOkSound .SubtractInteger
axiom evalBuiltinSym_active_ok_MultiplyInteger : BuiltinOkSound .MultiplyInteger
axiom evalBuiltinSym_active_ok_DivideInteger : BuiltinOkSound .DivideInteger
axiom evalBuiltinSym_active_ok_QuotientInteger : BuiltinOkSound .QuotientInteger
axiom evalBuiltinSym_active_ok_RemainderInteger : BuiltinOkSound .RemainderInteger
axiom evalBuiltinSym_active_ok_ModInteger : BuiltinOkSound .ModInteger
axiom evalBuiltinSym_active_ok_EqualsInteger : BuiltinOkSound .EqualsInteger
axiom evalBuiltinSym_active_ok_LessThanInteger : BuiltinOkSound .LessThanInteger
axiom evalBuiltinSym_active_ok_LessThanEqualsInteger : BuiltinOkSound .LessThanEqualsInteger
axiom evalBuiltinSym_active_ok_AppendByteString : BuiltinOkSound .AppendByteString
axiom evalBuiltinSym_active_ok_ConsByteString : BuiltinOkSound .ConsByteString
axiom evalBuiltinSym_active_ok_SliceByteString : BuiltinOkSound .SliceByteString
axiom evalBuiltinSym_active_ok_LengthOfByteString : BuiltinOkSound .LengthOfByteString
axiom evalBuiltinSym_active_ok_IndexByteString : BuiltinOkSound .IndexByteString
axiom evalBuiltinSym_active_ok_EqualsByteString : BuiltinOkSound .EqualsByteString
axiom evalBuiltinSym_active_ok_LessThanByteString : BuiltinOkSound .LessThanByteString
axiom evalBuiltinSym_active_ok_LessThanEqualsByteString : BuiltinOkSound .LessThanEqualsByteString
axiom evalBuiltinSym_active_ok_Sha2_256 : BuiltinOkSound .Sha2_256
axiom evalBuiltinSym_active_ok_Sha3_256 : BuiltinOkSound .Sha3_256
axiom evalBuiltinSym_active_ok_Blake2b_256 : BuiltinOkSound .Blake2b_256
axiom evalBuiltinSym_active_ok_VerifyEd25519Signature : BuiltinOkSound .VerifyEd25519Signature
axiom evalBuiltinSym_active_ok_AppendString : BuiltinOkSound .AppendString
axiom evalBuiltinSym_active_ok_EqualsString : BuiltinOkSound .EqualsString
axiom evalBuiltinSym_active_ok_EncodeUtf8 : BuiltinOkSound .EncodeUtf8
axiom evalBuiltinSym_active_ok_DecodeUtf8 : BuiltinOkSound .DecodeUtf8
axiom evalBuiltinSym_active_ok_IfThenElse : BuiltinOkSound .IfThenElse
axiom evalBuiltinSym_active_ok_ChooseUnit : BuiltinOkSound .ChooseUnit
axiom evalBuiltinSym_active_ok_Trace : BuiltinOkSound .Trace
axiom evalBuiltinSym_active_ok_FstPair : BuiltinOkSound .FstPair
axiom evalBuiltinSym_active_ok_SndPair : BuiltinOkSound .SndPair
axiom evalBuiltinSym_active_ok_ChooseList : BuiltinOkSound .ChooseList
axiom evalBuiltinSym_active_ok_MkCons : BuiltinOkSound .MkCons
axiom evalBuiltinSym_active_ok_HeadList : BuiltinOkSound .HeadList
axiom evalBuiltinSym_active_ok_TailList : BuiltinOkSound .TailList
axiom evalBuiltinSym_active_ok_NullList : BuiltinOkSound .NullList
axiom evalBuiltinSym_active_ok_ChooseData : BuiltinOkSound .ChooseData
axiom evalBuiltinSym_active_ok_ConstrData : BuiltinOkSound .ConstrData
axiom evalBuiltinSym_active_ok_MapData : BuiltinOkSound .MapData
axiom evalBuiltinSym_active_ok_ListData : BuiltinOkSound .ListData
axiom evalBuiltinSym_active_ok_IData : BuiltinOkSound .IData
axiom evalBuiltinSym_active_ok_BData : BuiltinOkSound .BData
axiom evalBuiltinSym_active_ok_UnConstrData : BuiltinOkSound .UnConstrData
axiom evalBuiltinSym_active_ok_UnMapData : BuiltinOkSound .UnMapData
axiom evalBuiltinSym_active_ok_UnListData : BuiltinOkSound .UnListData
axiom evalBuiltinSym_active_ok_UnIData : BuiltinOkSound .UnIData
axiom evalBuiltinSym_active_ok_UnBData : BuiltinOkSound .UnBData
axiom evalBuiltinSym_active_ok_EqualsData : BuiltinOkSound .EqualsData
axiom evalBuiltinSym_active_ok_MkPairData : BuiltinOkSound .MkPairData
axiom evalBuiltinSym_active_ok_MkNilData : BuiltinOkSound .MkNilData
axiom evalBuiltinSym_active_ok_MkNilPairData : BuiltinOkSound .MkNilPairData
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
axiom evalBuiltinSym_active_ok_DropList : BuiltinOkSound .DropList
axiom evalBuiltinSym_active_ok_IndexArray : BuiltinOkSound .IndexArray
axiom evalBuiltinSym_active_ok_LengthOfArray : BuiltinOkSound .LengthOfArray
axiom evalBuiltinSym_active_ok_ListToArray : BuiltinOkSound .ListToArray
axiom evalBuiltinSym_active_ok_InsertCoin : BuiltinOkSound .InsertCoin
axiom evalBuiltinSym_active_ok_LookupCoin : BuiltinOkSound .LookupCoin
axiom evalBuiltinSym_active_ok_ScaleValue : BuiltinOkSound .ScaleValue
axiom evalBuiltinSym_active_ok_UnionValue : BuiltinOkSound .UnionValue
axiom evalBuiltinSym_active_ok_ValueContains : BuiltinOkSound .ValueContains
axiom evalBuiltinSym_active_ok_ValueData : BuiltinOkSound .ValueData
axiom evalBuiltinSym_active_ok_UnValueData : BuiltinOkSound .UnValueData
axiom evalBuiltinSym_active_ok_Bls12_381_G1_multiScalarMul : BuiltinOkSound .Bls12_381_G1_multiScalarMul
axiom evalBuiltinSym_active_ok_Bls12_381_G2_multiScalarMul : BuiltinOkSound .Bls12_381_G2_multiScalarMul
axiom evalBuiltinSym_active_error_AddInteger : BuiltinErrorSound .AddInteger
axiom evalBuiltinSym_active_error_SubtractInteger : BuiltinErrorSound .SubtractInteger
axiom evalBuiltinSym_active_error_MultiplyInteger : BuiltinErrorSound .MultiplyInteger
axiom evalBuiltinSym_active_error_DivideInteger : BuiltinErrorSound .DivideInteger
axiom evalBuiltinSym_active_error_QuotientInteger : BuiltinErrorSound .QuotientInteger
axiom evalBuiltinSym_active_error_RemainderInteger : BuiltinErrorSound .RemainderInteger
axiom evalBuiltinSym_active_error_ModInteger : BuiltinErrorSound .ModInteger
axiom evalBuiltinSym_active_error_EqualsInteger : BuiltinErrorSound .EqualsInteger
axiom evalBuiltinSym_active_error_LessThanInteger : BuiltinErrorSound .LessThanInteger
axiom evalBuiltinSym_active_error_LessThanEqualsInteger : BuiltinErrorSound .LessThanEqualsInteger
axiom evalBuiltinSym_active_error_AppendByteString : BuiltinErrorSound .AppendByteString
axiom evalBuiltinSym_active_error_ConsByteString : BuiltinErrorSound .ConsByteString
axiom evalBuiltinSym_active_error_SliceByteString : BuiltinErrorSound .SliceByteString
axiom evalBuiltinSym_active_error_LengthOfByteString : BuiltinErrorSound .LengthOfByteString
axiom evalBuiltinSym_active_error_IndexByteString : BuiltinErrorSound .IndexByteString
axiom evalBuiltinSym_active_error_EqualsByteString : BuiltinErrorSound .EqualsByteString
axiom evalBuiltinSym_active_error_LessThanByteString : BuiltinErrorSound .LessThanByteString
axiom evalBuiltinSym_active_error_LessThanEqualsByteString : BuiltinErrorSound .LessThanEqualsByteString
axiom evalBuiltinSym_active_error_Sha2_256 : BuiltinErrorSound .Sha2_256
axiom evalBuiltinSym_active_error_Sha3_256 : BuiltinErrorSound .Sha3_256
axiom evalBuiltinSym_active_error_Blake2b_256 : BuiltinErrorSound .Blake2b_256
axiom evalBuiltinSym_active_error_VerifyEd25519Signature : BuiltinErrorSound .VerifyEd25519Signature
axiom evalBuiltinSym_active_error_AppendString : BuiltinErrorSound .AppendString
axiom evalBuiltinSym_active_error_EqualsString : BuiltinErrorSound .EqualsString
axiom evalBuiltinSym_active_error_EncodeUtf8 : BuiltinErrorSound .EncodeUtf8
axiom evalBuiltinSym_active_error_DecodeUtf8 : BuiltinErrorSound .DecodeUtf8
axiom evalBuiltinSym_active_error_IfThenElse : BuiltinErrorSound .IfThenElse
axiom evalBuiltinSym_active_error_ChooseUnit : BuiltinErrorSound .ChooseUnit
axiom evalBuiltinSym_active_error_Trace : BuiltinErrorSound .Trace
axiom evalBuiltinSym_active_error_FstPair : BuiltinErrorSound .FstPair
axiom evalBuiltinSym_active_error_SndPair : BuiltinErrorSound .SndPair
axiom evalBuiltinSym_active_error_ChooseList : BuiltinErrorSound .ChooseList
axiom evalBuiltinSym_active_error_MkCons : BuiltinErrorSound .MkCons
axiom evalBuiltinSym_active_error_HeadList : BuiltinErrorSound .HeadList
axiom evalBuiltinSym_active_error_TailList : BuiltinErrorSound .TailList
axiom evalBuiltinSym_active_error_NullList : BuiltinErrorSound .NullList
axiom evalBuiltinSym_active_error_ChooseData : BuiltinErrorSound .ChooseData
axiom evalBuiltinSym_active_error_ConstrData : BuiltinErrorSound .ConstrData
axiom evalBuiltinSym_active_error_MapData : BuiltinErrorSound .MapData
axiom evalBuiltinSym_active_error_ListData : BuiltinErrorSound .ListData
axiom evalBuiltinSym_active_error_IData : BuiltinErrorSound .IData
axiom evalBuiltinSym_active_error_BData : BuiltinErrorSound .BData
axiom evalBuiltinSym_active_error_UnConstrData : BuiltinErrorSound .UnConstrData
axiom evalBuiltinSym_active_error_UnMapData : BuiltinErrorSound .UnMapData
axiom evalBuiltinSym_active_error_UnListData : BuiltinErrorSound .UnListData
axiom evalBuiltinSym_active_error_UnIData : BuiltinErrorSound .UnIData
axiom evalBuiltinSym_active_error_UnBData : BuiltinErrorSound .UnBData
axiom evalBuiltinSym_active_error_EqualsData : BuiltinErrorSound .EqualsData
axiom evalBuiltinSym_active_error_MkPairData : BuiltinErrorSound .MkPairData
axiom evalBuiltinSym_active_error_MkNilData : BuiltinErrorSound .MkNilData
axiom evalBuiltinSym_active_error_MkNilPairData : BuiltinErrorSound .MkNilPairData
axiom evalBuiltinSym_active_error_SerializeData : BuiltinErrorSound .SerializeData
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
axiom evalBuiltinSym_active_error_DropList : BuiltinErrorSound .DropList
axiom evalBuiltinSym_active_error_IndexArray : BuiltinErrorSound .IndexArray
axiom evalBuiltinSym_active_error_LengthOfArray : BuiltinErrorSound .LengthOfArray
axiom evalBuiltinSym_active_error_ListToArray : BuiltinErrorSound .ListToArray
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
    (hmem : out ∈ evalBuiltinSym b args)
    (hok : outcomeOkSym? m out = some (sv, cv)) :
    Moist.CEK.evalBuiltin b cargs = some cv := by
  cases out with
  | ok pc v =>
      have hok' := outcomeOkSym_ok hok
      have hpath := builtinOkSound b hargs hmem hok'.1
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
                  have hb := builtinOkSound b hargs' hmemBuiltin hpc
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
                  have hb := builtinOkSound b hargs hmemBuiltin hpc
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
            subst cscrut
            simp [caseCekResult, Moist.CEK.constToTagAndFields]
        | g2 g =>
            cases out <;> simp [caseSym, err, outcomeErrorActive] at hmem herr
            simp [symValToCek?, symConstToCek?] at hscrut
            subst cscrut
            simp [caseCekResult, Moist.CEK.constToTagAndFields]
        | ml r =>
            cases out <;> simp [caseSym, err, outcomeErrorActive] at hmem herr
            simp [symValToCek?, symConstToCek?] at hscrut
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
