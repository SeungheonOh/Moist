import Moist.Verified.FundamentalRefinesWF
import Moist.Verified.ShapeFacts.Evaluation

variable [sv : Moist.CEK.SemVariant]

/-! # Reflexivity of the well-formedness-guarded relation

Every well-formed value, environment and stack is related to itself by the
`wfGuard` instance of the guarded logical relation. The closure cases use
`ftlr_wf`; the stack cases are the frame lemmas of `Contextual.Guarded`.
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.Verified Moist.Verified.Equivalence
open Moist.Verified.Contextual.Guarded
open Moist.Verified.TermObsRefinesWF
open Moist.Verified.BetaValueRefines

omit sv in
private theorem lookup_extend_succ (ρ : CekEnv) (v : CekValue) (n : Nat) :
    (ρ.extend v).lookup (n + 2) = ρ.lookup (n + 1) := rfl

theorem envRel_extend_of {k d : Nat} {ρ : CekEnv} {a₁ a₂ : CekValue}
    (hρ : EnvWellFormed d ρ) (ha : ValueRel wfGuard k a₁ a₂)
    (refl : ∀ v, ValueWellFormed v → ValueRel wfGuard k v v) :
    EnvRel wfGuard k (d + 1) (ρ.extend a₁) (ρ.extend a₂) := by
  intro n hn hnd
  match n with
  | 0 => omega
  | 1 => exact ⟨a₁, a₂, rfl, rfl, ha⟩
  | m + 2 =>
    obtain ⟨v, hl, hv⟩ := envWellFormed_lookup d hρ (n := m + 1) (by omega) (by omega)
    exact ⟨v, v, by rw [lookup_extend_succ]; exact hl, by rw [lookup_extend_succ]; exact hl,
      refl v hv⟩

theorem envRel_refl_of {k d : Nat} {ρ : CekEnv} (hρ : EnvWellFormed d ρ)
    (refl : ∀ v, ValueWellFormed v → ValueRel wfGuard k v v) :
    EnvRel wfGuard k d ρ ρ := by
  intro n hn hnd
  obtain ⟨v, hl, hv⟩ := envWellFormed_lookup d hρ hn hnd
  exact ⟨v, v, hl, hl, refl v hv⟩

/-- The open relation of `ftlr_wf` as an `Eval` statement. -/
theorem eval_of_openRefinesWF {d k : Nat} {t₁ t₂ : Term} {ρ₁ ρ₂ : CekEnv}
    (h : OpenRefinesWF d t₁ t₂) (henv : EnvRel wfGuard k d ρ₁ ρ₂)
    (hwf₁ : EnvWellFormed d ρ₁) (hlen₁ : d ≤ ρ₁.length)
    (hwf₂ : EnvWellFormed d ρ₂) (hlen₂ : d ≤ ρ₂.length) :
    Eval wfGuard k ρ₁ ρ₂ t₁ t₂ := by
  intro i hi π₁ π₂ hπ _ _
  exact h k k (Nat.le_refl _) ρ₁ ρ₂ henv hwf₁ hlen₁ hwf₂ hlen₂ i hi π₁ π₂ hπ.1 hπ.2.1 hπ.2.2

theorem valueList_refl_of {k : Nat} (refl : ∀ v, ValueWellFormed v → ValueRel wfGuard k v v) :
    ∀ {vs : List CekValue}, ValueListWellFormed vs → ListRel (ValueRel wfGuard k) vs vs
  | [], _ => trivial
  | _ :: _, .cons hv hvs => ⟨refl _ hv, valueList_refl_of refl hvs⟩

/-- Every well-formed value is related to itself at every step index. -/
theorem valueRel_refl : ∀ (k : Nat) (v : CekValue), ValueWellFormed v → ValueRel wfGuard k v v := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro v hv
  cases hv with
  | vcon c => exact valueRel_vcon k c
  | @vlam body ρ m henv hlen hclosed =>
    apply valueRel_lam (W := wfGuard) (ValueWellFormed.vlam henv hlen hclosed)
      (ValueWellFormed.vlam henv hlen hclosed)
    intro j hj a₁ a₂ ha ha₁ ha₂
    exact eval_of_openRefinesWF (FundamentalRefinesWF.ftlr_wf (m + 1) body hclosed)
      (envRel_extend_of henv ha (ih j hj))
      (envWellFormed_extend m henv hlen ha₁) (by simp [CekEnv.extend, CekEnv.length]; omega)
      (envWellFormed_extend m henv hlen ha₂) (by simp [CekEnv.extend, CekEnv.length]; omega)
  | @vdelay body ρ m henv hlen hclosed =>
    apply valueRel_delay (W := wfGuard) (ValueWellFormed.vdelay henv hlen hclosed)
      (ValueWellFormed.vdelay henv hlen hclosed)
    intro j hj
    exact eval_of_openRefinesWF (FundamentalRefinesWF.ftlr_wf m body hclosed)
      (envRel_refl_of henv (ih j hj)) henv hlen henv hlen
  | vconstr tag hfs =>
    cases k with
    | zero => simp only [ValueRel]
    | succ k => simp only [ValueRel]; exact ⟨trivial, valueList_refl_of (ih k (by omega)) hfs⟩
  | vbuiltin b ea hargs =>
    cases k with
    | zero => simp only [ValueRel]; exact ⟨trivial, trivial⟩
    | succ k => simp only [ValueRel]; exact ⟨trivial, trivial, valueList_refl_of (ih k (by omega)) hargs⟩

theorem envRel_refl {k d : Nat} {ρ : CekEnv} (hρ : EnvWellFormed d ρ) :
    EnvRel wfGuard k d ρ ρ :=
  envRel_refl_of hρ (valueRel_refl k)

theorem eval_refl {k d : Nat} {ρ : CekEnv} {t : Term} (hclosed : closedAt d t = true)
    (hρ : EnvWellFormed d ρ) (hlen : d ≤ ρ.length) : Eval wfGuard k ρ ρ t t :=
  eval_of_openRefinesWF (FundamentalRefinesWF.ftlr_wf d t hclosed) (envRel_refl hρ) hρ hlen hρ hlen

private theorem evalList_refl {k d : Nat} {ρ : CekEnv} (hρ : EnvWellFormed d ρ) (hlen : d ≤ ρ.length) :
    ∀ {ts : List Term}, closedAtList d ts = true → ListRel (Eval wfGuard k ρ ρ) ts ts
  | [], _ => trivial
  | t :: ts, h => by
    simp only [closedAtList, Bool.and_eq_true] at h
    exact ⟨eval_refl h.1 hρ hlen, evalList_refl hρ hlen h.2⟩

/-- Every well-formed stack is related to itself at every step index. -/
theorem stackRel_refl (k : Nat) : ∀ {π : Stack}, StackWellFormed π → StackRel wfGuard k π π
  | [], _ => stackRel_nil (W := wfGuard) StackWellFormed.nil k
  | f :: π, hs => by
    have hs' := hs
    cases hs' with
    | cons hf hπ =>
      have ih := stackRel_refl k hπ
      cases hf with
      | force => exact force_stackRel ih
      | @arg t ρ m henv hlen hclosed => exact arg_stackRel (eval_refl hclosed henv hlen) hs hs ih
      | funV hv => exact funV_stackRel (valueRel_refl k _ hv) hv hv ih
      | applyArg hv =>
        exact applyArgs_stackRel (W := wfGuard) (fs₁ := [_]) (fs₂ := [_])
          ⟨valueRel_refl k _ hv, trivial⟩ hs hs ih
      | constrField tag hdone henv hlen hclosed =>
        exact constrField_stackRel (evalList_refl henv hlen hclosed)
          (valueList_refl_of (valueRel_refl k) hdone) hs hs ih
      | caseScrutinee henv hlen hclosed =>
        exact case_stackRel (altsRel_of_listRel (evalList_refl henv hlen hclosed)) hs hs ih

end Moist.Verified.ShapeFacts
