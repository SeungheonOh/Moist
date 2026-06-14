import Moist.Verified.SmallStep.Step

/-! # Basic lemmas about `Step`, `Steps`, `Value`

* `Steps.single`, `Steps.trans` — closure plumbing.
* `bspine_det` — a term determines its builtin spine `(b, args, ea)`.
* `valueList_mem` / `valueList_mid` — membership extraction.
* value inversion helpers + `step_not_value` / `value_normal` — values never reduce.
-/

namespace Moist.Verified.SmallStep

open Moist.Plutus.Term (Term)
open Moist.CEK (ArgKind ExpectedArgs)

/-! ## `Steps` closure -/

theorem Steps.single {a b : Term} (h : Step a b) : Steps a b := .step h .refl

theorem Steps.trans {a b c : Term} (h1 : Steps a b) (h2 : Steps b c) : Steps a c := by
  induction h1 with
  | refl => exact h2
  | step hs _ ih => exact .step hs (ih h2)

/-! ## `BSpine` determinism

`BSpine` is mutually inductive (with `Value`/`ValueList`) so the `induction`
tactic is unavailable; we recurse structurally on the (proof-irrelevant)
derivations.  Cross-constructor cases are impossible because the shared term
index cannot be simultaneously `Builtin`/`Apply`/`Force`. -/

theorem bspine_det : ∀ {t : Term} {b1 b2 : Moist.Plutus.Term.BuiltinFun}
    {a1 a2 : List Term} {e1 e2 : ExpectedArgs},
    BSpine t b1 a1 e1 → BSpine t b2 a2 e2 → b1 = b2 ∧ a1 = a2 ∧ e1 = e2
  | _, _, _, _, _, _, _, .builtin, .builtin => ⟨rfl, rfl, rfl⟩
  | _, _, _, _, _, _, _, .app h1 _, .app h2 _ => by
      obtain ⟨hb, ha, he⟩ := bspine_det h1 h2
      subst hb; subst ha; injection he with _ he'; subst he'; exact ⟨rfl, rfl, rfl⟩
  | _, _, _, _, _, _, _, .force h1, .force h2 => by
      obtain ⟨hb, ha, he⟩ := bspine_det h1 h2
      subst hb; subst ha; injection he with _ he'; subst he'; exact ⟨rfl, rfl, rfl⟩

/-! ## `ValueList` membership -/

theorem valueList_mem : ∀ {ts : List Term}, ValueList ts → ∀ {t : Term}, t ∈ ts → Value t
  | _, .nil, _, hmem => by cases hmem
  | _, .cons hv hrest, _, hmem => by
    cases hmem with
    | head => exact hv
    | tail _ h => exact valueList_mem hrest h

theorem valueList_mid {lefts rights : List Term} {m : Term}
    (h : ValueList (lefts ++ m :: rights)) : Value m :=
  valueList_mem h (by simp)

/-! ## Value inversion helpers

`Value.builtin` is polymorphic in the term, so inverting `Value` on any shape
requires discharging a spurious `builtin`/`BSpine` arm. -/

theorem not_value_error : ¬ Value (.Error) := by
  intro hv; cases hv with | builtin hsp => cases hsp

theorem not_value_case {s : Term} {alts : List Term} : ¬ Value (.Case s alts) := by
  intro hv; cases hv with | builtin hsp => cases hsp

theorem value_apply_inv {f a : Term} (hv : Value (.Apply f a)) :
    ∃ b args rest, BSpine f b args (.more .argV rest) ∧ Value a := by
  cases hv with | builtin hsp => cases hsp with | app hsp' hva => exact ⟨_, _, _, hsp', hva⟩

theorem value_force_inv {u : Term} (hv : Value (.Force u)) :
    ∃ b args rest, BSpine u b args (.more .argQ rest) := by
  cases hv with | builtin hsp => cases hsp with | force hsp' => exact ⟨_, _, _, hsp'⟩

/-! ## Values do not step -/

/-- If a term reduces, it is not a value. -/
theorem step_not_value {t t' : Term} (h : Step t t') : ¬ Value t := by
  induction h with
  | betaLam _ =>
    intro hv; obtain ⟨_, _, _, hsp', _⟩ := value_apply_inv hv; cases hsp'
  | forceDelay =>
    intro hv; obtain ⟨_, _, _, hsp'⟩ := value_force_inv hv; cases hsp'
  | caseConstr _ _ => intro hv; exact not_value_case hv
  | caseConst _ _ _ => intro hv; exact not_value_case hv
  | satApply hsp _ =>
    intro hv
    obtain ⟨_, _, _, hsp2', _⟩ := value_apply_inv hv
    obtain ⟨_, _, he⟩ := bspine_det hsp hsp2'; cases he
  | satForce hsp =>
    intro hv
    obtain ⟨_, _, _, hsp2'⟩ := value_force_inv hv
    obtain ⟨_, _, he⟩ := bspine_det hsp hsp2'; cases he
  | errAppL =>
    intro hv; obtain ⟨_, _, _, hsp', _⟩ := value_apply_inv hv; cases hsp'
  | errAppR _ =>
    intro hv; obtain ⟨_, _, _, _, hva⟩ := value_apply_inv hv; exact not_value_error hva
  | errForce =>
    intro hv; obtain ⟨_, _, _, hsp'⟩ := value_force_inv hv; cases hsp'
  | errCase => intro hv; exact not_value_case hv
  | errConstr _ =>
    intro hv
    cases hv with
    | constr hvl => exact not_value_error (valueList_mid hvl)
    | builtin hsp => cases hsp
  | congAppL _ ih =>
    intro hv; obtain ⟨_, _, _, hsp', _⟩ := value_apply_inv hv; exact ih (.builtin hsp')
  | congAppR _ _ ih =>
    intro hv; obtain ⟨_, _, _, _, hva⟩ := value_apply_inv hv; exact ih hva
  | congForce _ ih =>
    intro hv; obtain ⟨_, _, _, hsp'⟩ := value_force_inv hv; exact ih (.builtin hsp')
  | congCase _ _ => intro hv; exact not_value_case hv
  | congConstr _ _ ih =>
    intro hv
    cases hv with
    | constr hvl => exact ih (valueList_mid hvl)
    | builtin hsp => cases hsp

/-- Values are in normal form. -/
theorem value_normal {t : Term} (hv : Value t) : Normal t :=
  fun ⟨_, hs⟩ => step_not_value hs hv

end Moist.Verified.SmallStep
