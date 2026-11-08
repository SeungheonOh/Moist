import Moist.Verified.GuardsSoundness.Steps

variable [sv : Moist.CEK.SemVariant]

/-! # Soundness of the termination analysis `chk` -/

namespace Moist.Verified.Guards

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast
open Moist.Verified.KnownLists

/-- Every environment satisfying the invariant runs `t`, applied to fields
    when `alt` holds, to an error or a value of mode `v`. -/
def Good (c : TCtx) (v : VMode) (alt : Bool) (env : List VarId) (t : Term) : Prop :=
  ∀ ρ, Inv c env ρ → ∀ fields, ValueListWellFormed fields → (alt = false → fields = []) →
    Ends v (.compute (fields.map Frame.applyArg) ρ t)

def ChkSound (n : Nat) : Prop :=
  ∀ c v alt e, chk n c v alt e = true → ∀ env t, EnvDistinct env → freshIn env e = true →
    lowerTotalExpr env e = some t → Good c v alt env t

theorem Good.run {c : TCtx} {v : VMode} {env : List VarId} {t : Term} (h : Good c v false env t)
    {ρ : CekEnv} (hρ : Inv c env ρ) : Errs ρ t ∨ ∃ r, Halts ρ t r ∧ ModeV v r :=
  h ρ hρ [] .nil (fun _ => rfl)

theorem Good.term {c : TCtx} {v : VMode} {env : List VarId} {t : Term} (h : Good c v false env t)
    {ρ : CekEnv} (hρ : Inv c env ρ) : Errs ρ t ∨ ∃ r, Halts ρ t r := by
  rcases h.run hρ with he | ⟨r, hr, _⟩
  · exact .inl he
  · exact .inr ⟨r, hr⟩

/-- A computation that ignores the fields: its value must reject them. -/
theorem good_leaf {c : TCtx} {v : VMode} {alt : Bool} {env : List VarId} {t : Term}
    (h : ∀ ρ, Inv c env ρ → Errs ρ t ∨ ∃ r, Halts ρ t r ∧ ModeV (if alt then v.applied else v) r) :
    Good c v alt env t := by
  intro ρ hρ fields _ hf
  rcases h ρ hρ with he | ⟨r, hr, hm⟩
  · exact .inl (errs_on_stack he _)
  refine Ends.of_reaches (halts_on_stack hr _) ?_
  cases alt with
  | false => rw [hf rfl]; exact ends_ret_nil hm
  | true =>
    cases fields with
    | nil => exact ends_ret_nil (VMode.applied_sound hm)
    | cons f fs =>
      exact (ends_ret_fields hm (VMode.applied_ne_term v) (f :: fs)).mono
        (fun w hw => VMode.applied_sound hw)

end Moist.Verified.Guards
