import Moist.Verified.SmallStep.Determinism
import Moist.Verified.SmallStep.Canon
import Moist.Verified.SmallStep.Adequacy

/-! # An executable, SMT-friendly presentation of small-step reduction

The inductive `Step`/`Steps`/`Value` relations are `Prop`s: an SMT backend such
as Blaster has nothing to unfold or execute on them.  This module gives a
*functional* presentation of exactly the same semantics — total Lean functions
returning `Bool`/`Option`/an `Outcome` datatype — and proves it equivalent to the
relational one.  Blaster can then symbolically execute `evalF` the same way it
executes the CEK `exec`.

The functions:

* `isValue : Term → Bool` — decides `Value` (with `bspine?` recognising partial
  builtin spines, and `isValueList`);
* `stepF : Term → Option Term` — the deterministic one-step reducer (`some` is the
  unique reduct, `none` means value-or-stuck), with `stepFields` handling the
  left-to-right constructor-field strategy;
* `evalF : Nat → Term → Outcome` — the fuel-driven evaluator, analogous to
  `Moist.CEK.exec`.

The bridge theorems (`isValue_iff`, `stepF_some_iff`, `stepF_none_iff`,
`evalF_value_iff`, and the composition with `adequacy_halt` in `evalF_adequacy`)
certify that the executable layer computes exactly the verified relation, so any
property proved on `evalF` transfers to `Step`/`Steps`/the CEK and back.
-/

namespace Moist.Verified.SmallStep

open Moist.Plutus.Term (Term Const BuiltinFun)
open Moist.CEK (ArgKind ExpectedArgs expectedArgs evalBuiltin constToTagAndFields CekValue)
open Moist.Verified (substTerm closedAt)
open Moist.Verified.Equivalence (Reaches steps)

/-! ## Shallow head recognisers

Plain structural functions (they reduce by `rfl`), used to dispatch `stepF`
without large constructor matches and to keep the bridge proofs uniform. -/

def isError : Term → Bool
  | .Error => true
  | _ => false

def lamBody? : Term → Option Term
  | .Lam _ M => some M
  | _ => none

def delayBody? : Term → Option Term
  | .Delay M => some M
  | _ => none

def constrParts? : Term → Option (Nat × List Term)
  | .Constr i vs => some (i, vs)
  | _ => none

def constParts? : Term → Option Const
  | .Constant (c, _) => some c
  | _ => none

@[simp] theorem isError_error : isError Term.Error = true := rfl
@[simp] theorem isError_lam {x : Nat} {M : Term} : isError (Term.Lam x M) = false := rfl
@[simp] theorem isError_delay {M : Term} : isError (Term.Delay M) = false := rfl
@[simp] theorem isError_constr {i : Nat} {vs : List Term} : isError (Term.Constr i vs) = false := rfl
@[simp] theorem isError_constant {cb} : isError (Term.Constant cb) = false := rfl
@[simp] theorem lamBody?_lam {x : Nat} {M : Term} : lamBody? (Term.Lam x M) = some M := rfl
@[simp] theorem delayBody?_delay {M : Term} : delayBody? (Term.Delay M) = some M := rfl
@[simp] theorem constrParts?_constr {i : Nat} {vs : List Term} :
    constrParts? (Term.Constr i vs) = some (i, vs) := rfl
@[simp] theorem constrParts?_constant {cb} : constrParts? (Term.Constant cb) = none := rfl
@[simp] theorem constParts?_constant {c : Const} {bt} :
    constParts? (Term.Constant (c, bt)) = some c := rfl

theorem isError_eq_true {t : Term} : isError t = true ↔ t = .Error := by
  cases t <;> simp [isError]

theorem lamBody?_some {t : Term} {M : Term} (h : lamBody? t = some M) :
    ∃ name, t = .Lam name M := by
  cases t <;> simp [lamBody?] at h; exact ⟨_, by rw [h]⟩

theorem delayBody?_some {t : Term} {M : Term} (h : delayBody? t = some M) : t = .Delay M := by
  cases t <;> simp [delayBody?] at h; rw [h]

theorem constrParts?_some {t : Term} {i : Nat} {vs : List Term}
    (h : constrParts? t = some (i, vs)) : t = .Constr i vs := by
  cases t <;> simp [constrParts?] at h; obtain ⟨h1, h2⟩ := h; rw [h1, h2]

theorem constParts?_some {t : Term} {c : Const} (h : constParts? t = some c) :
    ∃ bt, t = .Constant (c, bt) := by
  cases t with
  | Constant cb =>
    obtain ⟨c', bt⟩ := cb
    simp only [constParts?, Option.some.injEq] at h
    exact ⟨bt, by rw [h]⟩
  | _ => simp [constParts?] at h

/-! ## Decidable value recogniser (mirrors `Value`/`ValueList`/`BSpine`) -/

mutual
  /-- Decides whether `t` is a `Value`. -/
  def isValue : Term → Bool
    | .Constant _ => true
    | .Delay _ => true
    | .Lam _ _ => true
    | .Builtin _ => true
    | .Constr _ fields => isValueList fields
    | .Apply f a =>
      match bspine? f with
      | some (_, _, .more .argV _) => isValue a
      | _ => false
    | .Force t =>
      match bspine? t with
      | some (_, _, .more .argQ _) => true
      | _ => false
    | .Var _ => false
    | .Case _ _ => false
    | .Error => false
  termination_by t => sizeOf t

  /-- Decides whether every element of `fields` is a `Value`. -/
  def isValueList : List Term → Bool
    | [] => true
    | t :: ts => isValue t && isValueList ts
  termination_by ts => sizeOf ts

  /-- Recognises a *partial* builtin spine: returns the builtin, the value
      arguments collected so far (application order), and the remaining
      argument signature.  `none` if `t` is not a well-formed partial spine. -/
  def bspine? : Term → Option (BuiltinFun × List Term × ExpectedArgs)
    | .Builtin b => some (b, [], expectedArgs b)
    | .Apply t v =>
      match bspine? t with
      | some (b, args, .more .argV rest) => if isValue v then some (b, args ++ [v], rest) else none
      | _ => none
    | .Force t =>
      match bspine? t with
      | some (b, args, .more .argQ rest) => some (b, args, rest)
      | _ => none
    | _ => none
  termination_by t => sizeOf t
end

/-! ## The functional one-step reducer -/

/-- Result of scanning a constructor's fields for the active (first non-value)
    position: `stepped fs'` rebuilt the list after one reduction, `erred` found
    a propagating `Error`, `noStep` means all values (a value) or a stuck field. -/
inductive FieldStep where
  | stepped : List Term → FieldStep
  | erred : FieldStep
  | noStep : FieldStep

/-- Step the argument of an application whose function is already a value
    (congruence `congAppR`); `none` propagates a stuck argument. -/
def stepArg (f : Term) : Option Term → Option Term
  | some a' => some (.Apply f a')
  | none => none

/-- The remaining signature is *saturating with a value*: applying one more value
    argument fires the builtin (`satApply`). -/
def isSatV : ExpectedArgs → Bool
  | .one .argV => true
  | _ => false

/-- The remaining signature is *saturating with a force* (`satForce`). -/
def isSatQ : ExpectedArgs → Bool
  | .one .argQ => true
  | _ => false

theorem isSatV_true {ea : ExpectedArgs} : isSatV ea = true ↔ ea = .one .argV := by
  cases ea with
  | one k => cases k <;> simp [isSatV]
  | more k rest => simp [isSatV]

theorem isSatQ_true {ea : ExpectedArgs} : isSatQ ea = true ↔ ea = .one .argQ := by
  cases ea with
  | one k => cases k <;> simp [isSatQ]
  | more k rest => simp [isSatQ]

mutual
  /-- One step of contextual reduction as a total function.  `some t'` is the
      unique reduct; `none` means `t` is a value or stuck. -/
  def stepF : Term → Option Term
    | .Apply f a =>
      if isError f then some .Error                                   -- errAppL
      else if isValue f && isError a then some .Error                 -- errAppR
      else
        match lamBody? f with
        | some M =>
          if isValue a then some (substTerm 1 a M)                    -- betaLam
          else stepArg f (stepF a)                                    -- congAppR
        | none =>
          match bspine? f with
          | some (b, args, ea) =>
            if isSatV ea then
              (if isValue a then
                some (dischargeResult (evalBuiltin b ((reflectList (args ++ [a])).reverse)))  -- satApply
              else stepArg f (stepF a))                               -- congAppR
            else stepArg f (stepF a)                                  -- congAppR (partial spine value)
          | none =>
            if isValue f then stepArg f (stepF a)                     -- congAppR (other value)
            else match stepF f with                                   -- congAppL
              | some f' => some (.Apply f' a)
              | none => none
    | .Force t =>
      if isError t then some .Error                                   -- errForce
      else
        match delayBody? t with
        | some M => some M                                            -- forceDelay
        | none =>
          match bspine? t with
          | some (b, args, ea) =>
            if isSatQ ea then
              some (dischargeResult (evalBuiltin b (reflectList args).reverse))  -- satForce
            else none                                                 -- value / stuck force
          | none =>
            if isValue t then none                                    -- stuck force of a value
            else match stepF t with                                   -- congForce
              | some t' => some (.Force t')
              | none => none
    | .Case s alts =>
      if isError s then some .Error                                   -- errCase
      else
        match constrParts? s with
        | some (i, vs) =>
          if isValueList vs then
            match alts[i]? with
            | some alt => some (mkApps alt vs)                        -- caseConstr
            | none => none
          else match stepF s with                                     -- congCase
            | some s' => some (.Case s' alts)
            | none => none
        | none =>
          match constParts? s with
          | some c =>
            match constToTagAndFields c with
            | some (tag, numCtors, fields) =>
              if numCtors > 0 ∧ alts.length > numCtors then none
              else match alts[tag]? with
                | some alt => some (mkApps alt (fields.map discharge))  -- caseConst
                | none => none
            | none => none
          | none =>
            if isValue s then none                                    -- stuck case of a value
            else match stepF s with                                   -- congCase
              | some s' => some (.Case s' alts)
              | none => none
    | .Constr i fields =>
      match stepFields fields with
      | .stepped fields' => some (.Constr i fields')                  -- congConstr
      | .erred => some .Error                                         -- errConstr
      | .noStep => none
    | _ => none                                                       -- Var/Constant/Builtin/Lam/Delay/Error
  termination_by t => sizeOf t

  /-- Scan a constructor's fields left to right for the first non-value. -/
  def stepFields : List Term → FieldStep
    | [] => .noStep
    | m :: ms =>
      if isValue m then
        match stepFields ms with
        | .stepped ms' => .stepped (m :: ms')
        | .erred => .erred
        | .noStep => .noStep
      else if isError m then .erred
      else match stepF m with
        | some m' => .stepped (m' :: ms)
        | none => .noStep
  termination_by l => sizeOf l
end

/-! ## The fuel-driven evaluator -/

/-- The terminal outcome of bounded evaluation. -/
inductive Outcome where
  | value : Term → Outcome
  | stuck : Term → Outcome
  | timeout : Outcome
deriving Repr

/-- Evaluate by iterating `stepF` up to `fuel` times.  Analogous to
    `Moist.CEK.exec`, but over plain `Term`s (no closures/environments). -/
def evalF : Nat → Term → Outcome
  | 0, _ => .timeout
  | n + 1, t =>
    match stepF t with
    | some t' => evalF n t'
    | none => if isValue t then .value t else .stuck t

/-! ## Bridge, part 1: the value recogniser is exactly `Value`

`isValue`/`isValueList`/`bspine?` decide `Value`/`ValueList`/`BSpine`. -/

mutual
  /-- `isValue` is sound for `Value`. -/
  theorem isValue_sound : ∀ {t : Term}, isValue t = true → Value t
    | .Constant _, _ => Value.constant
    | .Delay _, _ => Value.delay
    | .Lam _ _, _ => Value.lam
    | .Builtin _, _ => Value.builtin BSpine.builtin
    | .Constr _ _, h => by
        simp only [isValue] at h; exact Value.constr (isValueList_sound h)
    | .Apply f a, h => by
        simp only [isValue] at h
        cases hbs : bspine? f with
        | none => rw [hbs] at h; simp at h
        | some y =>
          obtain ⟨b, args, ea⟩ := y
          cases ea with
          | one k => rw [hbs] at h; cases k <;> simp at h
          | more k rest =>
            cases k with
            | argV =>
              rw [hbs] at h
              exact Value.builtin (BSpine.app (bspine?_sound hbs) (isValue_sound h))
            | argQ => rw [hbs] at h; simp at h
    | .Force t, h => by
        simp only [isValue] at h
        cases hbs : bspine? t with
        | none => rw [hbs] at h; simp at h
        | some y =>
          obtain ⟨b, args, ea⟩ := y
          cases ea with
          | one k => rw [hbs] at h; cases k <;> simp at h
          | more k rest =>
            cases k with
            | argQ => exact Value.builtin (BSpine.force (bspine?_sound hbs))
            | argV => rw [hbs] at h; simp at h
    | .Var _, h => by simp [isValue] at h
    | .Case _ _, h => by simp [isValue] at h
    | .Error, h => by simp [isValue] at h
  termination_by t => sizeOf t

  /-- `isValueList` is sound for `ValueList`. -/
  theorem isValueList_sound : ∀ {ts : List Term}, isValueList ts = true → ValueList ts
    | [], _ => ValueList.nil
    | _ :: _, h => by
        simp only [isValueList, Bool.and_eq_true] at h
        exact ValueList.cons (isValue_sound h.1) (isValueList_sound h.2)
  termination_by ts => sizeOf ts

  /-- `bspine?` is sound for `BSpine`. -/
  theorem bspine?_sound : ∀ {t : Term} {b : BuiltinFun} {args : List Term} {ea : ExpectedArgs},
      bspine? t = some (b, args, ea) → BSpine t b args ea
    | .Builtin _, _, _, _, h => by
        simp only [bspine?, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hb, ha, he⟩ := h; subst hb; subst ha; subst he; exact BSpine.builtin
    | .Apply t v, _, _, _, h => by
        simp only [bspine?] at h
        cases hbs : bspine? t with
        | none => rw [hbs] at h; simp at h
        | some y =>
          obtain ⟨b', args', ea'⟩ := y
          cases ea' with
          | one k => rw [hbs] at h; cases k <;> simp at h
          | more k rest =>
            cases k with
            | argV =>
              rw [hbs] at h
              cases hv : isValue v with
              | false => rw [hv] at h; simp at h
              | true =>
                rw [hv] at h; simp only [if_true, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨hb, ha, he⟩ := h; subst hb; subst ha; subst he
                exact BSpine.app (bspine?_sound hbs) (isValue_sound hv)
            | argQ => rw [hbs] at h; simp at h
    | .Force t, _, _, _, h => by
        simp only [bspine?] at h
        cases hbs : bspine? t with
        | none => rw [hbs] at h; simp at h
        | some y =>
          obtain ⟨b', args', ea'⟩ := y
          cases ea' with
          | one k => rw [hbs] at h; cases k <;> simp at h
          | more k rest =>
            cases k with
            | argQ =>
              rw [hbs] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hb, ha, he⟩ := h; subst hb; subst ha; subst he
              exact BSpine.force (bspine?_sound hbs)
            | argV => rw [hbs] at h; simp at h
    | .Var _, _, _, _, h => by simp [bspine?] at h
    | .Constant _, _, _, _, h => by simp [bspine?] at h
    | .Lam _ _, _, _, _, h => by simp [bspine?] at h
    | .Delay _, _, _, _, h => by simp [bspine?] at h
    | .Constr _ _, _, _, _, h => by simp [bspine?] at h
    | .Case _ _, _, _, _, h => by simp [bspine?] at h
    | .Error, _, _, _, h => by simp [bspine?] at h
  termination_by t => sizeOf t
end

mutual
  /-- `isValue` is complete for `Value`. -/
  theorem isValue_complete : ∀ {t : Term}, Value t → isValue t = true
    | _, .constant => by simp only [isValue]
    | _, .delay => by simp only [isValue]
    | _, .lam => by simp only [isValue]
    | _, .constr hvl => by simp only [isValue]; exact isValueList_complete hvl
    | _, .builtin hsp => by
        cases hsp with
        | builtin => simp only [isValue]
        | app hsp' hv => simp only [isValue, bspine?_complete hsp', isValue_complete hv]
        | force hsp' => simp only [isValue, bspine?_complete hsp']
  /-- `isValueList` is complete for `ValueList`. -/
  theorem isValueList_complete : ∀ {ts : List Term}, ValueList ts → isValueList ts = true
    | _, .nil => by simp only [isValueList]
    | _, .cons hv hvl => by
        simp only [isValueList, Bool.and_eq_true]
        exact ⟨isValue_complete hv, isValueList_complete hvl⟩
  /-- `bspine?` is complete for `BSpine`. -/
  theorem bspine?_complete : ∀ {t : Term} {b : BuiltinFun} {args : List Term} {ea : ExpectedArgs},
      BSpine t b args ea → bspine? t = some (b, args, ea)
    | _, _, _, _, .builtin => by simp only [bspine?]
    | _, _, _, _, .app hsp' hv => by
        simp only [bspine?, bspine?_complete hsp', isValue_complete hv, if_true]
    | _, _, _, _, .force hsp' => by simp only [bspine?, bspine?_complete hsp']
end

/-- **Value bridge.** `isValue` decides `Value`. -/
theorem isValue_iff {t : Term} : isValue t = true ↔ Value t :=
  ⟨isValue_sound, isValue_complete⟩

/-! ## Helpers connecting recognisers to `Value`/`Step` -/

theorem isError_false_of_value {v : Term} (hv : Value v) : isError v = false := by
  cases v with
  | Error => exact absurd hv not_value_error
  | _ => rfl

theorem isValue_false_of_not_value {t : Term} (h : ¬ Value t) : isValue t = false := by
  cases ht : isValue t with
  | false => rfl
  | true => exact absurd (isValue_sound ht) h

theorem bspine?_none_of_not_value {t : Term} (h : ¬ Value t) : bspine? t = none := by
  cases ht : bspine? t with
  | none => rfl
  | some y => obtain ⟨b, args, ea⟩ := y; exact absurd (Value.builtin (bspine?_sound ht)) h

theorem lamBody?_none_of_not_value {t : Term} (h : ¬ Value t) : lamBody? t = none := by
  cases t with
  | Lam _ _ => exact absurd Value.lam h
  | _ => rfl

theorem delayBody?_none_of_not_value {t : Term} (h : ¬ Value t) : delayBody? t = none := by
  cases t with
  | Delay _ => exact absurd Value.delay h
  | _ => rfl

theorem lamBody?_none_of_bspine {t : Term} {y} (h : bspine? t = some y) : lamBody? t = none := by
  cases t <;> first | rfl | simp [bspine?] at h

theorem delayBody?_none_of_bspine {t : Term} {y} (h : bspine? t = some y) : delayBody? t = none := by
  cases t <;> first | rfl | simp [bspine?] at h

/-! ## Bridge, part 2: `stepF` is sound for `Step` -/

/-- Field-scan soundness: an `erred` scan exposes a value prefix followed by a
    propagating `Error`. -/
theorem stepFields_erred : ∀ {fs : List Term}, stepFields fs = .erred →
    ∃ lefts rights, ValueList lefts ∧ fs = lefts ++ .Error :: rights
  | [], h => by simp [stepFields] at h
  | m :: ms, h => by
    simp only [stepFields] at h
    split at h
    · next hvm =>
      cases hsm : stepFields ms with
      | stepped ms' => simp [hsm] at h
      | erred =>
        obtain ⟨lefts, rights, hvl, hms⟩ := stepFields_erred hsm
        exact ⟨m :: lefts, rights, ValueList.cons (isValue_sound hvm) hvl, by rw [hms, List.cons_append]⟩
      | noStep => simp [hsm] at h
    · next hvm =>
      split at h
      · next hem =>
        obtain rfl := isError_eq_true.mp hem
        exact ⟨[], ms, ValueList.nil, rfl⟩
      · next hem =>
        cases hsm : stepF m with
        | some m' => simp [hsm] at h
        | none => simp [hsm] at h

mutual
  /-- `stepF` is sound for `Step`: any computed reduct is a genuine step. -/
  theorem stepF_sound : ∀ {t t' : Term}, stepF t = some t' → Step t t'
    | .Apply f a, t', h => by
        simp only [stepF, stepArg] at h
        split at h
        · next hef =>
          obtain rfl := isError_eq_true.mp hef
          simp only [Option.some.injEq] at h; subst h; exact Step.errAppL
        · next hef =>
          split at h
          · next herr =>
            simp only [Bool.and_eq_true] at herr
            obtain ⟨hvf, hea⟩ := herr
            obtain rfl := isError_eq_true.mp hea
            simp only [Option.some.injEq] at h; subst h
            exact Step.errAppR (isValue_sound hvf)
          · next herr =>
            cases hlf : lamBody? f with
            | some M =>
              obtain ⟨name, rfl⟩ := lamBody?_some hlf
              simp only [lamBody?] at h
              split at h
              · next hva =>
                simp only [Option.some.injEq] at h; subst h
                exact Step.betaLam (isValue_sound hva)
              · next hva =>
                cases hsa : stepF a with
                | some a' => simp only [hsa, Option.some.injEq] at h; subst h
                             exact Step.congAppR Value.lam (stepF_sound hsa)
                | none => simp [hsa] at h
            | none =>
              simp only [hlf] at h
              cases hbf : bspine? f with
              | some y =>
                obtain ⟨b, args, ea⟩ := y
                simp only [hbf] at h
                split at h
                · next hsv =>
                  split at h
                  · next hva =>
                    obtain rfl := isSatV_true.mp hsv
                    simp only [Option.some.injEq] at h; subst h
                    exact Step.satApply (bspine?_sound hbf) (isValue_sound hva)
                  · next hva =>
                    cases hsa : stepF a with
                    | some a' => simp only [hsa, Option.some.injEq] at h; subst h
                                 exact Step.congAppR (Value.builtin (bspine?_sound hbf)) (stepF_sound hsa)
                    | none => simp [hsa] at h
                · next hsv =>
                  cases hsa : stepF a with
                  | some a' => simp only [hsa, Option.some.injEq] at h; subst h
                               exact Step.congAppR (Value.builtin (bspine?_sound hbf)) (stepF_sound hsa)
                  | none => simp [hsa] at h
              | none =>
                simp only [hbf] at h
                split at h
                · next hvf =>
                  cases hsa : stepF a with
                  | some a' => simp only [hsa, Option.some.injEq] at h; subst h
                               exact Step.congAppR (isValue_sound hvf) (stepF_sound hsa)
                  | none => simp [hsa] at h
                · next hvf =>
                  cases hsf : stepF f with
                  | some f' => simp only [hsf, Option.some.injEq] at h; subst h
                               exact Step.congAppL (stepF_sound hsf)
                  | none => simp [hsf] at h
    | .Force t, t', h => by
        simp only [stepF] at h
        split at h
        · next het =>
          obtain rfl := isError_eq_true.mp het
          simp only [Option.some.injEq] at h; subst h; exact Step.errForce
        · next het =>
          cases hdl : delayBody? t with
          | some M =>
            obtain rfl := delayBody?_some hdl
            simp only [delayBody?, Option.some.injEq] at h; subst h
            exact Step.forceDelay
          | none =>
            simp only [hdl] at h
            cases hbt : bspine? t with
            | some y =>
              obtain ⟨b, args, ea⟩ := y
              simp only [hbt] at h
              split at h
              · next hsq =>
                obtain rfl := isSatQ_true.mp hsq
                simp only [Option.some.injEq] at h; subst h
                exact Step.satForce (bspine?_sound hbt)
              · next hsq => simp at h
            | none =>
              simp only [hbt] at h
              split at h
              · next hvt => simp at h
              · next hvt =>
                cases hst : stepF t with
                | some t'' => simp only [hst, Option.some.injEq] at h; subst h
                              exact Step.congForce (stepF_sound hst)
                | none => simp [hst] at h
    | .Case s alts, t', h => by
        simp only [stepF] at h
        split at h
        · next hes =>
          obtain rfl := isError_eq_true.mp hes
          simp only [Option.some.injEq] at h; subst h; exact Step.errCase
        · next hes =>
          cases hcp : constrParts? s with
          | some y =>
            obtain ⟨i, vs⟩ := y
            simp only [hcp] at h
            split at h
            · next hvl =>
              cases ha : alts[i]? with
              | some alt => simp only [ha, Option.some.injEq] at h; subst h
                            rw [constrParts?_some hcp]
                            exact Step.caseConstr (isValueList_sound hvl) ha
              | none => simp [ha] at h
            · next hvl =>
              cases hss : stepF s with
              | some s' => simp only [hss, Option.some.injEq] at h; subst h
                           exact Step.congCase (stepF_sound hss)
              | none => simp [hss] at h
          | none =>
            simp only [hcp] at h
            cases hkp : constParts? s with
            | some c =>
              obtain ⟨bt, rfl⟩ := constParts?_some hkp
              simp only [constParts?] at h
              cases hct : constToTagAndFields c with
              | some triple =>
                obtain ⟨tag, numCtors, fields⟩ := triple
                simp only [hct] at h
                split at h
                · next hchk => simp at h
                · next hchk =>
                  cases ha : alts[tag]? with
                  | some alt => simp only [ha, Option.some.injEq] at h; subst h
                                exact Step.caseConst hct hchk ha
                  | none => simp [ha] at h
              | none => simp [hct] at h
            | none =>
              simp only [hkp] at h
              split at h
              · next hvs => simp at h
              · next hvs =>
                cases hss : stepF s with
                | some s' => simp only [hss, Option.some.injEq] at h; subst h
                             exact Step.congCase (stepF_sound hss)
                | none => simp [hss] at h
    | .Constr i fields, t', h => by
        simp only [stepF] at h
        cases hsf : stepFields fields with
        | stepped fields' =>
          simp only [hsf, Option.some.injEq] at h; subst h
          obtain ⟨lefts, m, m', rights, hvl, hstep, hfe, hfe'⟩ := stepFields_sound hsf
          rw [hfe, hfe']
          exact Step.congConstr hvl hstep
        | erred =>
          simp only [hsf, Option.some.injEq] at h; subst h
          obtain ⟨lefts, rights, hvl, hfe⟩ := stepFields_erred hsf
          rw [hfe]
          exact Step.errConstr hvl
        | noStep => simp [hsf] at h
    | .Var _, _, h => by simp [stepF] at h
    | .Constant _, _, h => by simp [stepF] at h
    | .Builtin _, _, h => by simp [stepF] at h
    | .Lam _ _, _, h => by simp [stepF] at h
    | .Delay _, _, h => by simp [stepF] at h
    | .Error, _, h => by simp [stepF] at h
  termination_by t => sizeOf t

  /-- Field-scan soundness: a `stepped` scan exposes a value prefix, the active
      field, its reduct, and the rebuilt list. -/
  theorem stepFields_sound : ∀ {fs fs' : List Term}, stepFields fs = .stepped fs' →
      ∃ lefts m m' rights, ValueList lefts ∧ Step m m' ∧
        fs = lefts ++ m :: rights ∧ fs' = lefts ++ m' :: rights
    | [], _, h => by simp [stepFields] at h
    | m :: ms, fs', h => by
        simp only [stepFields] at h
        split at h
        · next hvm =>
          cases hsm : stepFields ms with
          | stepped ms' =>
            simp only [hsm, FieldStep.stepped.injEq] at h; subst h
            obtain ⟨lefts, mm, mm', rights, hvl, hstep, hms, hms'⟩ := stepFields_sound hsm
            exact ⟨m :: lefts, mm, mm', rights, ValueList.cons (isValue_sound hvm) hvl, hstep,
              by rw [hms, List.cons_append], by rw [hms', List.cons_append]⟩
          | erred => simp [hsm] at h
          | noStep => simp [hsm] at h
        · next hvm =>
          split at h
          · next hem => simp at h
          · next hem =>
            cases hsm : stepF m with
            | some m' =>
              simp only [hsm, FieldStep.stepped.injEq] at h; subst h
              exact ⟨[], m, m', ms, ValueList.nil, stepF_sound hsm, rfl, rfl⟩
            | none => simp [hsm] at h
  termination_by fs => sizeOf fs
end

/-! ## Bridge, part 3: `stepF` is complete for `Step` -/

/-- Field-scan completeness for `errConstr`: a value prefix then `Error` scans to
    `erred`. -/
theorem stepFields_erred_of : ∀ {lefts rights : List Term}, ValueList lefts →
    stepFields (lefts ++ .Error :: rights) = .erred
  | [], rights, _ => by
      simp [stepFields, isValue_false_of_not_value not_value_error, isError]
  | l :: ls, rights, hvl => by
      cases hvl with
      | cons hv hvl' =>
        simp [List.cons_append, stepFields, isValue_complete hv, stepFields_erred_of hvl']

/-- Field-scan completeness for `congConstr`: a value prefix then a reducible
    field scans to `stepped`, reducing exactly that field. -/
theorem stepFields_stepped_of : ∀ {lefts : List Term} {m m' : Term} {rights : List Term},
    ValueList lefts → stepF m = some m' →
    stepFields (lefts ++ m :: rights) = .stepped (lefts ++ m' :: rights)
  | [], m, m', rights, _, hm => by
      have hns : ¬ Value m := step_not_value (stepF_sound hm)
      have hie : isError m = false := by
        cases hem : isError m with
        | false => rfl
        | true => exact absurd (isError_eq_true.mp hem ▸ stepF_sound hm) not_step_error
      simp [stepFields, isValue_false_of_not_value hns, hie, hm]
  | l :: ls, m, m', rights, hvl, hm => by
      cases hvl with
      | cons hv hvl' =>
        simp [List.cons_append, stepFields, isValue_complete hv, stepFields_stepped_of hvl' hm]

/-- When the function of an application is already a value (and the argument is
    neither a value nor `Error`), `stepF` reduces the argument (`congAppR`). -/
theorem stepF_apply_value_arg {f a : Term} (hvf : Value f)
    (hva : isValue a = false) (hea : isError a = false) :
    stepF (.Apply f a) = stepArg f (stepF a) := by
  have hef : isError f = false := isError_false_of_value hvf
  cases hlf : lamBody? f with
  | some M => simp [stepF, stepArg, hef, hea, hva, hlf]
  | none =>
    cases hbf : bspine? f with
    | some y =>
      obtain ⟨b, args, ea⟩ := y
      cases hsv : isSatV ea with
      | true =>
        -- `hva : isValue a = false` routes past the `satApply` branch to `stepArg`
        simp [stepF, stepArg, hef, hea, hva, hlf, hbf, hsv]
      | false => simp [stepF, stepArg, hef, hea, hva, hlf, hbf, hsv]
    | none => simp [stepF, stepArg, hef, hea, hlf, hbf, isValue_complete hvf]

/-- `stepF` is complete for `Step`: every step is computed. -/
theorem stepF_complete {t t' : Term} (hstep : Step t t') : stepF t = some t' := by
  induction hstep with
  | @betaLam x M v hv =>
    simp [stepF, isValue_complete hv, isError_false_of_value hv]
  | forceDelay => simp [stepF]
  | @caseConstr i vs alts alt hvl halt =>
    simp [stepF, isValueList_complete hvl, halt]
  | @caseConst c bt tag numCtors fields alts alt hc hchk halt =>
    simp [stepF, hc, halt, hchk]
  | @satApply f b args v hsp hv =>
    have hvf : Value f := Value.builtin hsp
    have hbf : bspine? f = some (b, args, .one .argV) := bspine?_complete hsp
    simp [stepF, isError_false_of_value hvf, isError_false_of_value hv,
      lamBody?_none_of_bspine hbf, hbf, isSatV, isValue_complete hv]
  | @satForce f b args hsp =>
    have hvf : Value f := Value.builtin hsp
    have hbf : bspine? f = some (b, args, .one .argQ) := bspine?_complete hsp
    simp [stepF, isError_false_of_value hvf, delayBody?_none_of_bspine hbf, hbf, isSatQ]
  | errAppL => simp [stepF]
  | @errAppR v hv =>
    simp [stepF, isError_false_of_value hv, isValue_complete hv]
  | errForce => simp [stepF]
  | errCase => simp [stepF]
  | @errConstr i lefts rights hvl =>
    simp only [stepF, stepFields_erred_of hvl]
  | @congAppL f f' N hstep ih =>
    have hnv : ¬ Value f := step_not_value hstep
    have hef : isError f = false := by
      cases he : isError f with
      | false => rfl
      | true => exact absurd (isError_eq_true.mp he ▸ hstep) not_step_error
    simp [stepF, hef, isValue_false_of_not_value hnv, lamBody?_none_of_not_value hnv,
      bspine?_none_of_not_value hnv, ih]
  | @congAppR v N N' hv hstep ih =>
    have hef : isError N = false := by
      cases he : isError N with
      | false => rfl
      | true => exact absurd (isError_eq_true.mp he ▸ hstep) not_step_error
    rw [stepF_apply_value_arg hv (isValue_false_of_not_value (step_not_value hstep)) hef]
    simp [stepArg, ih]
  | @congForce t t' hstep ih =>
    have hnv : ¬ Value t := step_not_value hstep
    have het : isError t = false := by
      cases he : isError t with
      | false => rfl
      | true => exact absurd (isError_eq_true.mp he ▸ hstep) not_step_error
    simp [stepF, het, delayBody?_none_of_not_value hnv, bspine?_none_of_not_value hnv,
      isValue_false_of_not_value hnv, ih]
  | @congCase s s' alts hstep ih =>
    have hnv : ¬ Value s := step_not_value hstep
    have hes : isError s = false := by
      cases he : isError s with
      | false => rfl
      | true => exact absurd (isError_eq_true.mp he ▸ hstep) not_step_error
    cases hcp : constrParts? s with
    | some y =>
      obtain ⟨i, vs⟩ := y
      have hsv : s = .Constr i vs := constrParts?_some hcp
      have hvl : isValueList vs = false := by
        cases hv : isValueList vs with
        | false => rfl
        | true => exact absurd (hsv ▸ Value.constr (isValueList_sound hv)) hnv
      simp [stepF, hes, hcp, hvl, ih]
    | none =>
      cases hkp : constParts? s with
      | some c =>
        obtain ⟨bt, hsc⟩ := constParts?_some hkp
        exact absurd (hsc ▸ Value.constant) hnv
      | none =>
        simp [stepF, hes, hcp, hkp, isValue_false_of_not_value hnv, ih]
  | @congConstr i lefts m m' rights hvl hstep ih =>
    simp only [stepF, stepFields_stepped_of hvl ih]

/-- **Step bridge.** `stepF` decides one-step reduction. -/
theorem stepF_some_iff {t t' : Term} : stepF t = some t' ↔ Step t t' :=
  ⟨stepF_sound, stepF_complete⟩

/-- **Normal-form bridge.** `stepF` returns `none` exactly on normal forms. -/
theorem stepF_none_iff {t : Term} : stepF t = none ↔ Normal t := by
  constructor
  · intro h
    rintro ⟨t', hs⟩
    rw [stepF_complete hs] at h
    exact Option.noConfusion h
  · intro hn
    cases hst : stepF t with
    | none => rfl
    | some t' => exact absurd ⟨t', stepF_sound hst⟩ hn

/-! ## Bridge, part 4: the fuel-driven evaluator ↔ `Steps` -/

/-- `evalF` soundness: a returned value is reached by `Steps` and is a `Value`. -/
theorem evalF_value_sound : ∀ {n : Nat} {t w : Term}, evalF n t = .value w → Steps t w ∧ Value w
  | 0, t, w, h => by simp [evalF] at h
  | n + 1, t, w, h => by
      simp only [evalF] at h
      cases hst : stepF t with
      | some t' =>
        simp only [hst] at h
        obtain ⟨hsteps, hval⟩ := evalF_value_sound h
        exact ⟨Steps.step (stepF_sound hst) hsteps, hval⟩
      | none =>
        simp only [hst] at h
        by_cases hv : isValue t = true
        · rw [if_pos hv] at h; injection h with ht; subst ht
          exact ⟨Steps.refl, isValue_sound hv⟩
        · rw [if_neg hv] at h; exact absurd h (by simp)
  termination_by n => n

/-- The length-indexed core of `evalF` completeness: `k`-step reduction to a
    value is computed with `k + 1` fuel. -/
theorem evalF_value_complete_aux : ∀ {k : Nat} {t w : Term}, StepsN k t w → Value w →
    evalF (k + 1) t = .value w
  | 0, t, w, hk, hval => by
      cases hk
      simp [evalF, stepF_none_iff.mpr (value_normal hval), isValue_complete hval]
  | _ + 1, t, w, hk, hval => by
      cases hk with
      | step hstep hrest =>
        simp only [evalF, stepF_complete hstep]
        exact evalF_value_complete_aux hrest hval

/-- `evalF` completeness: a value reached by `Steps` is returned for some fuel. -/
theorem evalF_value_complete {t w : Term} (hsteps : Steps t w) (hval : Value w) :
    ∃ n, evalF n t = .value w := by
  obtain ⟨k, hk⟩ := steps_stepsN hsteps
  exact ⟨k + 1, evalF_value_complete_aux hk hval⟩

/-- **Evaluator bridge.** `evalF` returns `value w` (for some fuel) exactly when
    `Steps` reaches the value `w`. -/
theorem evalF_value_iff {t w : Term} :
    (∃ n, evalF n t = .value w) ↔ (Steps t w ∧ Value w) := by
  constructor
  · rintro ⟨n, hn⟩; exact evalF_value_sound hn
  · rintro ⟨hs, hv⟩; exact evalF_value_complete hs hv

/-! ## Bridge, part 5: composition with CEK adequacy

For a closed canonical term, the executable evaluator returns a value exactly
when the CEK machine halts — so a Blaster proof of `evalF N t = .value …`
certifies CEK halting (and vice versa). -/

/-- The executable evaluator halts on a value iff the CEK machine halts. -/
theorem evalF_adequacy {t : Term} (ht : closedAt 0 t = true) (htc : Canonical t) :
    (∃ n w, evalF n t = .value w) ↔ (∃ v, Reaches (init t) (.halt v)) := by
  constructor
  · rintro ⟨n, w, h⟩
    obtain ⟨hs, hv⟩ := evalF_value_sound h
    exact (adequacy_halt ht htc).mpr ⟨w, hs, hv⟩
  · intro h
    obtain ⟨w, hs, hv⟩ := (adequacy_halt ht htc).mp h
    obtain ⟨n, hn⟩ := evalF_value_complete hs hv
    exact ⟨n, w, hn⟩

/-- Exact-value forward bridge: a halting CEK run is mirrored by `evalF`
    returning the discharged value. -/
theorem evalF_value_of_reaches {t : Term} {v : CekValue}
    (ht : closedAt 0 t = true) (htc : Canonical t) (h : Reaches (init t) (.halt v)) :
    ∃ n, evalF n t = .value (discharge v) := by
  obtain ⟨hs, hv⟩ := adequacy_halt_fwd ht htc h
  exact evalF_value_complete hs hv

/-- Exact-value backward bridge: whatever `evalF` returns is the discharge of the
    CEK halt value. -/
theorem reaches_of_evalF_value {t w : Term} {n : Nat}
    (ht : closedAt 0 t = true) (htc : Canonical t) (h : evalF n t = .value w) :
    ∃ v, Reaches (init t) (.halt v) ∧ w = discharge v := by
  obtain ⟨hs, hv⟩ := evalF_value_sound h
  obtain ⟨v, hr⟩ := (adequacy_halt ht htc).mpr ⟨w, hs, hv⟩
  obtain ⟨hs', hv'⟩ := adequacy_halt_fwd ht htc hr
  exact ⟨v, hr, normal_form_unique hs (value_normal hv) hs' (value_normal hv')⟩

end Moist.Verified.SmallStep
