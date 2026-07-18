import Moist.SMT.Soundness.Compiler
import Moist.Verified.BigStep

namespace Moist.SMT.UPLC.Soundness

/-! Shared semantic foundations for compiler soundness. -/

open Moist.Plutus.Term
open Moist.Verified.BigStep
open Moist.CEK (ArgKind ExpectedArgs expectedArgs CekEnv CekValue)

namespace SmtSem
abbrev Val := Moist.SMT.Semantics.Val
abbrev SVal := Moist.SMT.Semantics.SVal
abbrev Model := Moist.SMT.Semantics.Model
abbrev eval := Moist.SMT.Semantics.eval
abbrev evalBool? := Moist.SMT.Semantics.evalBool?
abbrev evalBoolIs := Moist.SMT.Semantics.evalBoolIs
abbrev strongOr := Moist.SMT.Semantics.strongOr
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

/-- Length-guided `ChooseList` pruning never creates a new symbolic outcome:
it only removes one of the two exhaustive constant-list alternatives. -/
theorem constListBranches_sublist (hint : Option Nat) (nilOutcome consOutcome : Outcome) :
    List.Sublist (constListBranches hint nilOutcome consOutcome)
      [nilOutcome, consOutcome] := by
  cases hint with
  | none => exact List.Sublist.refl _
  | some n =>
      cases n with
      | zero =>
          exact (List.nil_sublist [consOutcome]).cons₂ nilOutcome
      | succ n =>
          exact (List.Sublist.refl [consOutcome]).cons nilOutcome

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
  | .VerifyEcdsaSecp256k1Signature | .VerifySchnorrSecp256k1Signature
  | .Bls12_381_G1_add | .Bls12_381_G1_neg | .Bls12_381_G1_scalarMul
  | .Bls12_381_G1_equal | .Bls12_381_G1_hashToGroup
  | .Bls12_381_G1_compress | .Bls12_381_G1_uncompress
  | .Bls12_381_G2_add | .Bls12_381_G2_neg | .Bls12_381_G2_scalarMul
  | .Bls12_381_G2_equal | .Bls12_381_G2_hashToGroup
  | .Bls12_381_G2_compress | .Bls12_381_G2_uncompress
  | .Bls12_381_millerLoop | .Bls12_381_mulMlResult | .Bls12_381_finalVerify
  | .Keccak_256 | .Blake2b_224
  | .Ripemd_160
  | .SerializeData | .InsertCoin | .LookupCoin | .ScaleValue | .UnionValue
  | .ValueContains | .ValueData | .UnValueData
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
  Moist.SMT.Semantics.Model.bind Moist.SMT.Semantics.Model.empty
    (Moist.SMT.sanitize name) (.int n)

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
    | .constList e _ =>
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

theorem bindOk_mem {pc : SExpr} {v : SymVal} {k : SymVal → List Outcome}
    {out : Outcome} (h : out ∈ bindOk pc v k) :
    ∃ inner, inner ∈ k v ∧ Outcome.guard pc inner = out := by
  cases pc <;> simp [bindOk] at h ⊢
  all_goals first | exact h | (rename_i b; cases b <;> simp_all)

/-- Every retained carried error has exactly its source path. -/
theorem carryError_mem {outerPc : SExpr} {out : Outcome}
    (h : out ∈ carryError outerPc) :
    out = Outcome.error outerPc := by
  cases outerPc <;> simp [carryError] at h ⊢
  all_goals first | exact h | (rename_i b; cases b <;> simp_all)

/-- Every retained carried timeout has exactly its source path. -/
theorem carryTimeout_mem {outerPc : SExpr} {out : Outcome}
    (h : out ∈ carryTimeout outerPc) :
    out = Outcome.timeout outerPc := by
  cases outerPc <;> simp [carryTimeout] at h ⊢
  all_goals first | exact h | (rename_i b; cases b <;> simp_all)

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

/-- The former left-linear compiler construction, retained only as the
reference specification for the balancing proof. -/
def referenceLinearAny (xs : List SExpr) : SExpr :=
  Moist.SMT.Expr.any xs

theorem evalBoolIs_referenceLinearAny_true {m : SmtSem.Model}
    {xs : List SExpr}
    (h : SmtSem.evalBoolIs m (referenceLinearAny xs) true = true) :
    ∃ x, x ∈ xs ∧ SmtSem.evalBoolIs m x true = true := by
  cases xs with
  | nil =>
      simp [referenceLinearAny, Moist.SMT.Expr.any] at h
  | cons x xs =>
      cases xs with
      | nil =>
          exact ⟨x, by simp,
            by simpa [referenceLinearAny, Moist.SMT.Expr.any] using h⟩
      | cons y ys =>
          have hfold := evalBoolIs_foldl_or_true (m := m)
            (xs := y :: ys) (acc := x)
            (by simpa [referenceLinearAny, Moist.SMT.Expr.any] using h)
          rcases hfold with hx | htail
          · exact ⟨x, by simp, hx⟩
          · rcases htail with ⟨z, hz, hztrue⟩
            exact ⟨z, by simp [hz], hztrue⟩

private theorem evalBoolIs_orPairRound_true {m : SmtSem.Model} :
    ∀ {xs : List SExpr} {merged : SExpr},
      merged ∈ SExpr.orPairRound xs →
      SmtSem.evalBoolIs m merged true = true →
      ∃ source, source ∈ xs ∧
        SmtSem.evalBoolIs m source true = true
  | [], merged, hmem, _ => by
      simp [SExpr.orPairRound] at hmem
  | [single], merged, hmem, htrue => by
      simp only [SExpr.orPairRound, List.mem_cons, List.not_mem_nil,
        or_false] at hmem
      subst merged
      exact ⟨single, by simp, htrue⟩
  | left :: right :: rest, merged, hmem, htrue => by
      simp only [SExpr.orPairRound, List.mem_cons] at hmem
      rcases hmem with hpair | hrest
      · subst merged
        rcases Moist.SMT.Semantics.evalBoolIs_or_true m left right htrue with
          hleft | hright
        · exact ⟨left, by simp, hleft⟩
        · exact ⟨right, by simp, hright⟩
      · obtain ⟨source, hsource, hsourceTrue⟩ :=
          evalBoolIs_orPairRound_true hrest htrue
        exact ⟨source, by simp [hsource], hsourceTrue⟩

/-- A true balanced disjunction is witnessed by one of its original leaves.
This is the semantic preservation fact used by compiler disjunctions. -/
theorem evalBoolIs_anyBalanced_true {m : SmtSem.Model} {xs : List SExpr}
    (h : SmtSem.evalBoolIs m (SExpr.anyBalanced xs) true = true) :
    ∃ x, x ∈ xs ∧ SmtSem.evalBoolIs m x true = true := by
  fun_induction SExpr.anyBalanced xs
  case case1 =>
    simp [SmtSem.evalBoolIs, SExpr.falseE,
      Moist.SMT.Semantics.evalBoolIs,
      Moist.SMT.Semantics.evalBool?, Moist.SMT.Semantics.eval,
      Moist.SMT.Expr.falseE] at h
  case case2 single =>
    exact ⟨single, by simp, h⟩
  case case3 left right rest ih =>
    obtain ⟨middle, hmiddle, hmiddleTrue⟩ := ih h
    have hmiddleRound :
        middle ∈ SExpr.orPairRound (left :: right :: rest) := by
      simpa only [SExpr.orPairRound] using hmiddle
    exact evalBoolIs_orPairRound_true hmiddleRound hmiddleTrue

theorem evalBoolIs_any_true {m : SmtSem.Model} {xs : List SExpr}
    (h : SmtSem.evalBoolIs m (SExpr.any xs) true = true) :
    ∃ x, x ∈ xs ∧ SmtSem.evalBoolIs m x true = true := by
  exact evalBoolIs_anyBalanced_true (by simpa [SExpr.any] using h)

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
  exact Moist.SMT.Semantics.eval_or_false_contra_left m a b haEval
    (by simpa [SExpr.or] using horFalse)

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
  exact Moist.SMT.Semantics.eval_or_false_contra_right m a b hbEval
    (by simpa [SExpr.or] using horFalse)

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
  simpa [SExpr.all, Moist.SMT.Expr.all] using
    (Moist.SMT.Semantics.eval_and_of_bools m a b ba bb ha hb)

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

theorem pcHolds_all4 {m : SmtSem.Model} {a b c d : SExpr}
    (h : pcHolds m (SExpr.all [a, b, c, d]) = true) :
    pcHolds m a = true ∧ pcHolds m b = true ∧
      pcHolds m c = true ∧ pcHolds m d = true := by
  have h' :
      pcHolds m (SExpr.and (SExpr.and (SExpr.and a b) c) d) = true := by
    simpa [SExpr.all, Moist.SMT.Expr.all] using h
  have hd := (Moist.SMT.Semantics.evalBoolIs_and_true m
    (SExpr.and (SExpr.and a b) c) d).mp h'
  have hc := (Moist.SMT.Semantics.evalBoolIs_and_true m
    (SExpr.and a b) c).mp hd.1
  have hab := (Moist.SMT.Semantics.evalBoolIs_and_true m a b).mp hc.1
  exact ⟨hab.1, hab.2, hc.2, hd.2⟩

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
  apply (Moist.SMT.Semantics.evalBoolIs_true_eq m (SExpr.or a b)).mpr
  simpa [SExpr.or] using
    (Moist.SMT.Semantics.eval_or_of_bools m a b true bb ha hb)

theorem evalBoolIs_or_true_of_right {m : SmtSem.Model} {a b : SExpr}
    (ha : ∃ ba, SmtSem.eval m a = some (.bool ba))
    (hb : SmtSem.eval m b = some (.bool true)) :
    SmtSem.evalBoolIs m (SExpr.or a b) true = true := by
  rcases ha with ⟨ba, ha⟩
  apply (Moist.SMT.Semantics.evalBoolIs_true_eq m (SExpr.or a b)).mpr
  simpa [SExpr.or] using
    (Moist.SMT.Semantics.eval_or_of_bools m a b ba true ha hb)

theorem eval_or_bool_of_bool {m : SmtSem.Model} {a b : SExpr}
    (ha : ∃ ba, SmtSem.eval m a = some (.bool ba))
    (hb : ∃ bb, SmtSem.eval m b = some (.bool bb)) :
    ∃ bc, SmtSem.eval m (SExpr.or a b) = some (.bool bc) := by
  rcases ha with ⟨ba, ha⟩
  rcases hb with ⟨bb, hb⟩
  refine ⟨ba || bb, ?_⟩
  simpa [SExpr.or] using
    (Moist.SMT.Semantics.eval_or_of_bools m a b ba bb ha hb)

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

@[simp] private theorem strongOr_false_left (x : Option Bool) :
    SmtSem.strongOr (some false) x = x := by
  cases x with
  | none => rfl
  | some b => cases b <;> rfl

@[simp] private theorem strongOr_false_right (x : Option Bool) :
    SmtSem.strongOr x (some false) = x := by
  cases x with
  | none => rfl
  | some b => cases b <;> rfl

@[simp] private theorem strongOr_true_left (x : Option Bool) :
    SmtSem.strongOr (some true) x = some true := by
  cases x with
  | none => rfl
  | some b => cases b <;> rfl

@[simp] private theorem strongOr_true_right (x : Option Bool) :
    SmtSem.strongOr x (some true) = some true := by
  cases x with
  | none => rfl
  | some b => cases b <;> rfl

private theorem strongOr_assoc (a b c : Option Bool) :
    SmtSem.strongOr (SmtSem.strongOr a b) c =
      SmtSem.strongOr a (SmtSem.strongOr b c) := by
  cases a <;> cases b <;> cases c <;>
    (try cases ‹Bool›) <;> (try cases ‹Bool›) <;>
      (try cases ‹Bool›) <;> rfl

@[simp] private theorem evalBool?_bool
    (m : SmtSem.Model) (b : Bool) :
    SmtSem.evalBool? m (.bool b) = some b := by
  simp [SmtSem.evalBool?, Moist.SMT.Semantics.evalBool?,
    Moist.SMT.Semantics.eval]

private theorem evalBool?_orRight_strong
    (m : SmtSem.Model) (a b : SExpr) :
    SmtSem.evalBool? m (Moist.SMT.Expr.orRight a b) =
      SmtSem.strongOr (SmtSem.evalBool? m a) (SmtSem.evalBool? m b) := by
  cases b <;> simp only [Moist.SMT.Expr.orRight]
  all_goals try cases ‹Bool›
  all_goals first
    | exact Moist.SMT.Semantics.evalBool?_app_or_strong _ _ _
    | simp [Moist.SMT.Expr.trueE, SmtSem.strongOr]

private theorem evalBool?_or_strong (m : SmtSem.Model) (a b : SExpr) :
    SmtSem.evalBool? m (SExpr.or a b) =
      SmtSem.strongOr (SmtSem.evalBool? m a) (SmtSem.evalBool? m b) := by
  cases a <;> simp only [SExpr.or, Moist.SMT.Expr.or]
  all_goals try cases ‹Bool›
  all_goals first
    | exact evalBool?_orRight_strong _ _ _
    | simp [Moist.SMT.Expr.trueE, SmtSem.strongOr]

private def semanticAny (m : SmtSem.Model) (xs : List SExpr) : Option Bool :=
  xs.foldr (fun expression rest =>
    SmtSem.strongOr (SmtSem.evalBool? m expression) rest) (some false)

@[simp] private theorem semanticAny_nil (m : SmtSem.Model) :
    semanticAny m [] = some false := rfl

@[simp] private theorem semanticAny_cons
    (m : SmtSem.Model) (x : SExpr) (xs : List SExpr) :
    semanticAny m (x :: xs) =
      SmtSem.strongOr (SmtSem.evalBool? m x) (semanticAny m xs) := rfl

private theorem semanticAny_orPairRound (m : SmtSem.Model) :
    ∀ xs : List SExpr,
      semanticAny m (SExpr.orPairRound xs) = semanticAny m xs
  | [] => rfl
  | [single] => rfl
  | left :: right :: rest => by
      change SmtSem.strongOr (SmtSem.evalBool? m (SExpr.or left right))
          (semanticAny m (SExpr.orPairRound rest)) =
        SmtSem.strongOr (SmtSem.evalBool? m left)
          (SmtSem.strongOr (SmtSem.evalBool? m right) (semanticAny m rest))
      rw [evalBool?_or_strong, semanticAny_orPairRound m rest]
      exact strongOr_assoc _ _ _

/-- The balanced compiler disjunction denotes a right-associated strong
three-valued disjunction of exactly its input leaves. -/
private theorem evalBool?_anyBalanced_eq_semanticAny (m : SmtSem.Model) :
    ∀ xs : List SExpr,
      SmtSem.evalBool? m (SExpr.anyBalanced xs) = semanticAny m xs := by
  intro xs
  fun_induction SExpr.anyBalanced xs
  case case1 =>
    simp [SExpr.falseE, Moist.SMT.Expr.falseE]
  case case2 single =>
    exact (strongOr_false_right (SmtSem.evalBool? m single)).symm
  case case3 left right rest ih =>
    rw [ih]
    exact semanticAny_orPairRound m (left :: right :: rest)

private theorem evalBool?_foldl_or_eq_semanticAny
    (m : SmtSem.Model) :
    ∀ (xs : List SExpr) (acc : SExpr),
      SmtSem.evalBool? m (xs.foldl SExpr.or acc) =
        SmtSem.strongOr (SmtSem.evalBool? m acc) (semanticAny m xs)
  | [], acc => (strongOr_false_right (SmtSem.evalBool? m acc)).symm
  | x :: xs, acc => by
      simp only [List.foldl_cons]
      rw [evalBool?_foldl_or_eq_semanticAny m xs (SExpr.or acc x),
        evalBool?_or_strong]
      rw [semanticAny_cons]
      exact strongOr_assoc _ _ _

private theorem evalBool?_referenceLinearAny_eq_semanticAny
    (m : SmtSem.Model) (xs : List SExpr) :
    SmtSem.evalBool? m (referenceLinearAny xs) = semanticAny m xs := by
  cases xs with
  | nil =>
      simp [referenceLinearAny, Moist.SMT.Expr.any,
        Moist.SMT.Expr.falseE]
  | cons x xs =>
      cases xs with
      | nil => exact (strongOr_false_right (SmtSem.evalBool? m x)).symm
      | cons y ys =>
          simpa [referenceLinearAny, Moist.SMT.Expr.any] using
            (evalBool?_foldl_or_eq_semanticAny m (y :: ys) x)

/-- Balancing is unconditionally semantics-preserving, including for partial
leaf observations: both constructions have exactly the same strong
three-valued Boolean result. -/
theorem evalBool?_any_eq_referenceLinearAny
    (m : SmtSem.Model) (xs : List SExpr) :
    SmtSem.evalBool? m (SExpr.any xs) =
      SmtSem.evalBool? m (referenceLinearAny xs) := by
  rw [SExpr.any, evalBool?_anyBalanced_eq_semanticAny,
    evalBool?_referenceLinearAny_eq_semanticAny]

theorem evalBoolIs_any_eq_referenceLinearAny
    (m : SmtSem.Model) (xs : List SExpr) (expected : Bool) :
    SmtSem.evalBoolIs m (SExpr.any xs) expected =
      SmtSem.evalBoolIs m (referenceLinearAny xs) expected := by
  have h := evalBool?_any_eq_referenceLinearAny m xs
  exact congrArg (fun observed : Option Bool =>
    match observed with
    | some actual => actual == expected
    | none => false) h

private theorem evalBoolIs_referenceLinearAny_true_of_mem
    {m : SmtSem.Model}
    {x : SExpr} {xs : List SExpr}
    (hmem : x ∈ xs)
    (hx : SmtSem.eval m x = some (.bool true))
    (hall : ∀ y, y ∈ xs → ∃ b, SmtSem.eval m y = some (.bool b)) :
    SmtSem.evalBoolIs m (referenceLinearAny xs) true = true := by
  cases xs with
  | nil => simp at hmem
  | cons y ys =>
      cases ys with
      | nil =>
          simp at hmem
          subst x
          simpa [referenceLinearAny, Moist.SMT.Expr.any] using
            (Moist.SMT.Semantics.evalBoolIs_true_eq m y).mpr hx
      | cons z zs =>
          simp [referenceLinearAny, Moist.SMT.Expr.any]
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

theorem evalBoolIs_any_true_of_mem {m : SmtSem.Model}
    {x : SExpr} {xs : List SExpr}
    (hmem : x ∈ xs)
    (hx : SmtSem.eval m x = some (.bool true))
    (hall : ∀ y, y ∈ xs → ∃ b, SmtSem.eval m y = some (.bool b)) :
    SmtSem.evalBoolIs m (SExpr.any xs) true = true := by
  rw [evalBoolIs_any_eq_referenceLinearAny]
  exact evalBoolIs_referenceLinearAny_true_of_mem hmem hx hall

theorem evalBoolIs_any_true_iff_referenceLinearAny_true
    {m : SmtSem.Model} {xs : List SExpr} :
    SmtSem.evalBoolIs m (SExpr.any xs) true = true ↔
      SmtSem.evalBoolIs m (referenceLinearAny xs) true = true := by
  rw [evalBoolIs_any_eq_referenceLinearAny]

/-- Compatibility corollary for clients that already carry Boolean-totality. -/
theorem evalBoolIs_any_true_iff_referenceLinearAny_true_of_bools
    {m : SmtSem.Model} {xs : List SExpr}
    (_hall : ∀ y, y ∈ xs → ∃ b, SmtSem.eval m y = some (.bool b)) :
    SmtSem.evalBoolIs m (SExpr.any xs) true = true ↔
      SmtSem.evalBoolIs m (referenceLinearAny xs) true = true :=
  evalBoolIs_any_true_iff_referenceLinearAny_true

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

/-! The ground evaluator only recognizes literal SMT syntax.  Recognition is
therefore a proof-producing boundary: every recovered `Const` decodes to the
same CEK constant in every model. -/

set_option maxHeartbeats 0 in
theorem symValLiteral?_sound (m : SmtSem.Model) (v : SymVal) (c : Const)
    (h : symValLiteral? v = some c) :
    symValToCek? m v = some (.VCon c) := by
  cases v with
  | const sc =>
      cases sc with
      | integer e =>
          cases e <;>
            simp_all [symValLiteral?, symValToCek?, symConstToCek?,
              Moist.SMT.Semantics.eval]
      | bytes e =>
          cases e <;>
            simp_all [symValLiteral?, symValToCek?, symConstToCek?,
              Moist.SMT.Semantics.eval]
      | string e =>
          cases e <;>
            simp_all [symValLiteral?, symValToCek?, symConstToCek?,
              Moist.SMT.Semantics.eval]
      | bool e =>
          cases e <;>
            simp_all [symValLiteral?, symValToCek?, symConstToCek?,
              Moist.SMT.Semantics.eval]
      | unit => simpa [symValLiteral?, symValToCek?, symConstToCek?] using h
      | data e =>
          cases e <;>
            simp_all [symValLiteral?, symValToCek?, symConstToCek?,
              Moist.SMT.Semantics.eval]
      | constList e hint =>
          cases e <;>
            simp_all [symValLiteral?, symValToCek?, symConstToCek?,
              Moist.SMT.Semantics.eval, semValListToConstList_constListToVals]
      | dataList e =>
          cases e <;>
            simp_all [symValLiteral?, symValToCek?, symConstToCek?,
              Moist.SMT.Semantics.eval]
      | pairDataList e =>
          cases e <;>
            simp_all [symValLiteral?, symValToCek?, symConstToCek?,
              Moist.SMT.Semantics.eval]
      | pairData a b =>
          cases a <;> cases b <;>
            simp_all [symValLiteral?, symValToCek?, symConstToCek?,
              Moist.SMT.Semantics.eval]
      | array e =>
          cases e <;>
            simp_all [symValLiteral?, symValToCek?, symConstToCek?,
              Moist.SMT.Semantics.eval, semValListToConstList_constListToVals]
      | g1 e => cases e <;> simp_all [symValLiteral?]
      | g2 e => cases e <;> simp_all [symValLiteral?]
      | ml e => cases e <;> simp_all [symValLiteral?]
  | dyn e => simp [symValLiteral?] at h
  | pair a b =>
      cases ha : symValLiteral? a with
      | none => simp [symValLiteral?, ha] at h
      | some ca =>
          cases hb : symValLiteral? b with
          | none => simp [symValLiteral?, ha, hb] at h
          | some cb =>
              simp [symValLiteral?, ha, hb] at h
              subst c
              have hca := symValLiteral?_sound m a ca ha
              have hcb := symValLiteral?_sound m b cb hb
              simp [symValToCek?, hca, hcb]
  | constr tag fields => simp [symValLiteral?] at h
  | lam body env => simp [symValLiteral?] at h
  | delay body env => simp [symValLiteral?] at h
  | builtin b args ea => simp [symValLiteral?] at h
termination_by sizeOf v

set_option maxHeartbeats 0 in
theorem symValListLiteral?_sound (m : SmtSem.Model) : ∀ args constArgs,
    args.mapM symValLiteral? = some constArgs →
    symValListToCekList? m args =
      some (constArgs.map CekValue.VCon) := by
  intro args
  induction args with
  | nil =>
      intro constArgs h
      simp at h
      subst constArgs
      rfl
  | cons v vs ih =>
      intro constArgs h
      cases hv : symValLiteral? v with
      | none => simp [List.mapM_cons, hv] at h
      | some c =>
          cases hvs : vs.mapM symValLiteral? with
          | none => simp [List.mapM_cons, hv, hvs] at h
          | some cs =>
              simp [List.mapM_cons, hv, hvs] at h
              subst constArgs
              have hvSound := symValLiteral?_sound m v c hv
              have hvsSound := ih cs hvs
              simp [symValListToCekList?, hvSound, hvsSound]

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
  | constList e _hint =>
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
  | constList e _hint =>
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
  | constList e _hint =>
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
  | constList e _hint =>
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
  | constList e _hint =>
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
  | constList e _hint =>
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
  | constList e _hint =>
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
    ∃ e hint vals, c = .constList e hint ∧ SmtSem.eval m e = some (.valList vals) ∧
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
  | constList e hint =>
      simp [symConstToCek?] at h
      cases he : SmtSem.eval m e <;> simp [he] at h
      rename_i sv
      cases sv <;> simp [he] at h
      case valList vals =>
        cases hcs : semValListToConstList? vals <;> simp [hcs] at h
        subst cs
        exact ⟨e, hint, vals, rfl, he, hcs⟩
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
  | constList e _hint =>
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
  case constList e _hint =>
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
      obtain ⟨inner, hinner, rfl⟩ := bindOk_mem hout
      have hg := outcomeOkSym_guard hok
      exact ⟨pc, v, inner, houter, hg.1, hinner, hg.2⟩
  | error pc =>
      have hout' := carryError_mem hout
      subst out
      simp [outcomeOkSym?] at hok
  | timeout pc =>
      have hout' := carryTimeout_mem hout
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
      obtain ⟨inner, hinner, rfl⟩ := bindOk_mem hout
      have hg := outcomeErrorActive_guard herr
      exact Or.inr ⟨pc, v, inner, houter, hg.1, hinner, hg.2⟩
  | error pc =>
      have hout' := carryError_mem hout
      subst out
      exact Or.inl ⟨pc, houter,
        by simpa [outcomeErrorActive] using herr⟩
  | timeout pc =>
      have hout' := carryTimeout_mem hout
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
      obtain ⟨inner, hinner, hguard⟩ := bindOk_mem hout
      cases inner with
      | ok innerPc innerV =>
          simp [Outcome.guard] at hguard
          rcases hguard with ⟨rfl, rfl⟩
          have hp := (Moist.SMT.Semantics.evalBoolIs_and_true m outerPc innerPc).mp hpc
          exact ⟨outerPc, outerV, innerPc, houter, hinner, rfl, hp.1, hp.2⟩
      | error innerPc => simp [Outcome.guard] at hguard
      | timeout innerPc => simp [Outcome.guard] at hguard
  | error outerPc =>
      have hout' := carryError_mem hout
      simp at hout'
  | timeout outerPc =>
      have hout' := carryTimeout_mem hout
      simp at hout'

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
      obtain ⟨inner, hinner, hguard⟩ := bindOk_mem hout
      cases inner with
      | ok innerPc innerV => simp [Outcome.guard] at hguard
      | error innerPc =>
          simp [Outcome.guard] at hguard
          subst pc
          have hp := (Moist.SMT.Semantics.evalBoolIs_and_true m outerPc innerPc).mp hpc
          exact Or.inr ⟨outerPc, outerV, innerPc, houter, hinner, rfl, hp.1, hp.2⟩
      | timeout innerPc => simp [Outcome.guard] at hguard
  | error outerPc =>
      have hpath := carryError_mem hout
      simp at hpath
      subst pc
      exact Or.inl ⟨houter, hpc⟩
  | timeout outerPc =>
      have hout' := carryTimeout_mem hout
      simp at hout'

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

theorem asBool_sound {m : SmtSem.Model} {v : SymVal} {cv : CekValue}
    (hv : symValToCek? m v = some cv)
    (hg : pcHolds m (asBool v).guard = true) :
    ∃ b, cv = .VCon (.Bool b) ∧
      SmtSem.eval m (asBool v).val = some (.bool b) := by
  cases v with
  | const c =>
      cases c <;> simp [asBool, valueProj, Proj.pure, Proj.fail, pcHolds,
        symValToCek?, symConstToCek?] at hv hg
      case bool e =>
        cases he : SmtSem.eval m e with
        | none => simp [he] at hv
        | some sv =>
            cases sv <;> simp [he] at hv
            case bool b =>
              subst cv
              exact ⟨b, rfl, by simpa [he]⟩
  | dyn e =>
      simp [asBool, valueProj, pcHolds, symValToCek?] at hv hg
      obtain ⟨b, he⟩ := Moist.SMT.Semantics.evalBoolIs_isVBool_true hg
      have hun := Moist.SMT.Semantics.eval_unVBool_of (m := m) (e := e) he
      simp [he, semValToCek?, semValToConst?] at hv
      subst cv
      exact ⟨b, rfl, hun⟩
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
      | constList e _hint =>
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
      | constList e _hint =>
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
      case constList e _hint =>
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
      obtain ⟨e, _hint, vals, hc, _he, _hcs⟩ :=
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
      | constList e _hint =>
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
  | constList e _hint =>
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

/-! ### Proof-carrying reflexive equality folding

These lemmas are intentionally conditional on successful evaluation at the
expected sort.  `SExpr.reflexiveEq` is used only behind the corresponding
typed projection guard, and these hypotheses are exactly what the builtin
simulation proof obtains from an active successful path.
-/

private theorem byteArray_beq_self (bs : ByteArray) : (bs == bs) = true := by
  change (bs.data == bs.data) = true
  exact beq_self_eq_true bs.data

mutual
  private theorem data_beq_self :
      (d : Moist.Plutus.Data) → Moist.Plutus.eqData d d = true
    | .Constr i fields => by
        change (i == i && Moist.Plutus.eqDataList fields fields) = true
        rw [dataList_beq_self fields]
        simp
    | .Map entries => dataMap_beq_self entries
    | .List xs => dataList_beq_self xs
    | .I i => by
        change (i == i) = true
        simp
    | .B bs => byteArray_beq_self bs

  private theorem dataList_beq_self :
      (xs : List Moist.Plutus.Data) →
        Moist.Plutus.eqDataList xs xs = true
    | [] => rfl
    | x :: xs => by
        change (Moist.Plutus.eqData x x &&
          Moist.Plutus.eqDataList xs xs) = true
        rw [data_beq_self x, dataList_beq_self xs]
        rfl

  private theorem dataMap_beq_self :
      (xs : List (Moist.Plutus.Data × Moist.Plutus.Data)) →
        Moist.Plutus.eqDataMap xs xs = true
    | [] => rfl
    | (x, y) :: xs => by
        change (Moist.Plutus.eqData x x && Moist.Plutus.eqData y y &&
          Moist.Plutus.eqDataMap xs xs) = true
        rw [data_beq_self x, data_beq_self y, dataMap_beq_self xs]
        rfl
end

private theorem eval_reflexiveEq_of_eq_eval {m : SmtSem.Model}
    {a b : SExpr} {result : Bool}
    (heq : SmtSem.eval m (SExpr.eq a b) = some (.bool result))
    (hrefl : a = b → result = true) :
    SmtSem.eval m (SExpr.reflexiveEq a b) = some (.bool result) := by
  cases hcert : SExpr.same? SExpr.reflexiveEqFuel a b with
  | none =>
    rw [SExpr.reflexiveEq, hcert]
    exact heq
  | some cert =>
    have hresult := hrefl cert.eq
    subst result
    simp only [SExpr.reflexiveEq, hcert]
    simp [SExpr.trueE, Moist.SMT.Expr.trueE, Moist.SMT.Semantics.eval]

theorem eval_reflexiveEq_int_of {m : SmtSem.Model} {a b : SExpr} {x y : Int}
    (ha : SmtSem.eval m a = some (.int x))
    (hb : SmtSem.eval m b = some (.int y)) :
    SmtSem.eval m (SExpr.reflexiveEq a b) = some (.bool (x == y)) := by
  apply eval_reflexiveEq_of_eq_eval
    (Moist.SMT.Semantics.eval_eq_int_of ha hb)
  intro hab
  subst b
  rw [ha] at hb
  injection hb with hval
  injection hval with hxy
  subst y
  simp

theorem eval_reflexiveEq_bytes_of {m : SmtSem.Model} {a b : SExpr}
    {x y : ByteArray}
    (ha : SmtSem.eval m a = some (.bytes x))
    (hb : SmtSem.eval m b = some (.bytes y)) :
    SmtSem.eval m (SExpr.reflexiveEq a b) = some (.bool (x == y)) := by
  apply eval_reflexiveEq_of_eq_eval
    (Moist.SMT.Semantics.eval_eq_bytes_of ha hb)
  intro hab
  subst b
  rw [ha] at hb
  injection hb with hval
  injection hval with hxy
  subst y
  exact byteArray_beq_self x

theorem eval_reflexiveEq_string_of {m : SmtSem.Model} {a b : SExpr}
    {x y : String}
    (ha : SmtSem.eval m a = some (.string x))
    (hb : SmtSem.eval m b = some (.string y)) :
    SmtSem.eval m (SExpr.reflexiveEq a b) = some (.bool (x == y)) := by
  apply eval_reflexiveEq_of_eq_eval
    (Moist.SMT.Semantics.eval_eq_string_of ha hb)
  intro hab
  subst b
  rw [ha] at hb
  injection hb with hval
  injection hval with hxy
  subst y
  simp

theorem eval_reflexiveEq_data_of {m : SmtSem.Model} {a b : SExpr}
    {x y : Moist.Plutus.Data}
    (ha : SmtSem.eval m a = some (.data x))
    (hb : SmtSem.eval m b = some (.data y)) :
    SmtSem.eval m (SExpr.reflexiveEq a b) = some (.bool (x == y)) := by
  apply eval_reflexiveEq_of_eq_eval
    (Moist.SMT.Semantics.eval_eq_data_of ha hb)
  intro hab
  subst b
  rw [ha] at hb
  injection hb with hval
  injection hval with hxy
  subst y
  change Moist.Plutus.eqData x x = true
  exact data_beq_self x

end Moist.SMT.UPLC.Soundness
