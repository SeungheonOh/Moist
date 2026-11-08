import Moist.Verified.GuardsSoundness.PushFresh

variable [sv : Moist.CEK.SemVariant]

/-! # Moving the consumer `if _ then u else error` one layer inwards

`assertT tx u` is the lowering of `force (ifThenElse x (delay u) (delay error))`.
Every lemma here is a same-environment refinement of the consumed term by
the term with the consumer moved one layer inwards.
-/

namespace Moist.Verified.Guards

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast

def assertT (tx : Term) (u : Const × BuiltinType) : Term :=
  .Force (.Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse)) tx) (.Delay (.Constant u))) (.Delay .Error))

def iteFrames (ρ : CekEnv) (u : Const × BuiltinType) : Stack :=
  [.funV (.VBuiltin .IfThenElse [] (.more .argV (.more .argV (.one .argV)))),
    .arg (.Delay (.Constant u)) ρ, .arg (.Delay .Error) ρ, .force]

theorem lower_assertE {env : List VarId} {x : Expr} {tx : Term} {u : Const × BuiltinType}
    (h : lowerTotalExpr env x = some tx) : lowerTotalExpr env (assertE u x) = some (assertT tx u) := by
  obtain ⟨c, ty⟩ := u
  simp only [assertE, iteE, MIR.lowerTotalExpr_force, MIR.lowerTotalExpr_app, MIR.lowerTotalExpr_delay,
    lowerTotalExpr_builtin, lowerTotalExpr_lit, lowerTotalExpr_error, h]
  rfl

theorem lower_assertE_inv {env : List VarId} {x : Expr} {t : Term} {u : Const × BuiltinType}
    (h : lowerTotalExpr env (assertE u x) = some t) :
    ∃ tx, lowerTotalExpr env x = some tx ∧ t = assertT tx u := by
  cases hx : lowerTotalExpr env x with
  | none =>
    obtain ⟨c, ty⟩ := u
    simp [assertE, iteE, MIR.lowerTotalExpr_force, MIR.lowerTotalExpr_app, MIR.lowerTotalExpr_delay,
      lowerTotalExpr_builtin, lowerTotalExpr_lit, lowerTotalExpr_error, hx] at h
  | some tx => rw [lower_assertE hx] at h; cases h; exact ⟨tx, rfl, rfl⟩

theorem assert_start (π : Stack) (ρ : CekEnv) (tx : Term) (u : Const × BuiltinType) :
    Reaches (.compute π ρ (assertT tx u)) (.compute (iteFrames ρ u ++ π) ρ tx) :=
  reaches_of_steps 8 rfl

theorem iteFrames_true (π : Stack) (ρ : CekEnv) (u : Const × BuiltinType) :
    Reaches (.ret (iteFrames ρ u ++ π) (.VCon (.Bool true))) (.ret π (.VCon u.1)) := by
  obtain ⟨c, ty⟩ := u
  exact reaches_of_steps 9 rfl

theorem iteFrames_false (π : Stack) (ρ : CekEnv) (u : Const × BuiltinType) :
    Reaches (.ret (iteFrames ρ u ++ π) (.VCon (.Bool false))) .error :=
  reaches_of_steps 9 rfl

theorem iteFrames_other (π : Stack) (ρ : CekEnv) (u : Const × BuiltinType) {w : CekValue}
    (hw : ∀ b, w ≠ .VCon (.Bool b)) : Reaches (.ret (iteFrames ρ u ++ π) w) .error := by
  cases w with
  | VCon c =>
    cases c with
    | Bool b => exact absurd rfl (hw b)
    | _ => exact reaches_of_steps 7 rfl
  | _ => exact reaches_of_steps 7 rfl

/-- The environment the consumer's delays close over does not matter. -/
theorem iteFrames_env (π : Stack) (ρ₁ ρ₂ : CekEnv) (u : Const × BuiltinType) (w : CekValue) :
    ObsRefines (.ret (iteFrames ρ₁ u ++ π) w) (.ret (iteFrames ρ₂ u ++ π) w) := by
  by_cases hb : ∃ b, w = .VCon (.Bool b)
  · obtain ⟨b, rfl⟩ := hb
    cases b
    · exact obsRefines_of_reaches (iteFrames_false π ρ₁ u) (iteFrames_false π ρ₂ u) (obsRefines_refl _)
    · exact obsRefines_of_reaches (iteFrames_true π ρ₁ u) (iteFrames_true π ρ₂ u) (obsRefines_refl _)
  · have hw : ∀ b, w ≠ .VCon (.Bool b) := fun b h => hb ⟨b, h⟩
    exact obsRefines_of_reaches (iteFrames_other π ρ₁ u hw) (iteFrames_other π ρ₂ u hw) (obsRefines_refl _)

theorem assert_cont (π : Stack) (ρ₁ ρ₂ ρ : CekEnv) (u : Const × BuiltinType) (t : Term) :
    ObsRefines (.compute (iteFrames ρ₁ u ++ π) ρ t) (.compute (iteFrames ρ₂ u ++ π) ρ t) :=
  obsRefines_of_continuation fun w _ => iteFrames_env π ρ₁ ρ₂ u w

/-- The consumer of a computation run in an environment `ρ'`. -/
theorem assert_inside (π : Stack) (ρ ρ' : CekEnv) (u : Const × BuiltinType) (t : Term) :
    ObsRefines (.compute (iteFrames ρ u ++ π) ρ' t) (.compute π ρ' (assertT t u)) :=
  obsRefines_trans (assert_cont π ρ ρ' ρ' u t)
    (obsRefines_of_reaches (reaches_refl _) (assert_start π ρ' t u) (obsRefines_refl _))

/-! ## Layers -/

theorem layer_true {d : Nat} {F : CekEnv → Prop} (u : Const × BuiltinType) (ty : BuiltinType) :
    FactRefines d F (assertT (.Constant (.Bool true, ty)) u) (.Constant u) := by
  intro ρ π _ _ _ _
  refine obsRefines_of_reaches (reaches_trans (assert_start π ρ _ u)
    (reaches_trans (reaches_of_steps 1 rfl) (iteFrames_true π ρ u))) (reaches_of_steps 1 rfl) ?_
  exact obsRefines_refl _

theorem layer_false {d : Nat} {F : CekEnv → Prop} (u : Const × BuiltinType) (ty : BuiltinType) :
    FactRefines d F (assertT (.Constant (.Bool false, ty)) u) .Error := by
  intro ρ π _ _ _ _
  exact obsRefines_of_reaches (reaches_trans (assert_start π ρ _ u)
    (reaches_trans (reaches_of_steps 1 rfl) (iteFrames_false π ρ u))) (reaches_of_steps 1 rfl)
    (obsRefines_refl _)

theorem layer_error {d : Nat} {F : CekEnv → Prop} (u : Const × BuiltinType) :
    FactRefines d F (assertT .Error u) .Error := by
  intro ρ π _ _ _ _
  exact obsRefines_of_reaches (reaches_trans (assert_start π ρ _ u) (reaches_of_steps 1 rfl))
    (reaches_of_steps 1 rfl) (obsRefines_refl _)

theorem layer_let {d : Nat} {F : CekEnv → Prop} (u : Const × BuiltinType) (tb tr : Term) :
    FactRefines d F (assertT (.Apply (.Lam 0 tb) tr) u) (.Apply (.Lam 0 (assertT tb u)) tr) := by
  intro ρ π _ _ _ _
  refine obsRefines_of_reaches (reaches_trans (assert_start π ρ _ u) (reaches_of_steps 3 rfl))
    (reaches_of_steps 3 rfl) ?_
  refine obsRefines_of_continuation fun v _ => ?_
  refine obsRefines_of_reaches (reaches_of_steps 1 rfl) (reaches_of_steps 1 rfl) ?_
  exact assert_inside π ρ (ρ.extend v) u tb

theorem layer_ite {d : Nat} {F : CekEnv → Prop} (u : Const × BuiltinType) (tc ta tb : Term) :
    FactRefines d F
      (assertT (.Force (.Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse)) tc) (.Delay ta)) (.Delay tb))) u)
      (.Force (.Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse)) tc) (.Delay (assertT ta u)))
        (.Delay (assertT tb u)))) := by
  intro ρ π _ _ _ _
  refine obsRefines_of_reaches (reaches_trans (assert_start π ρ _ u) (reaches_of_steps 8 rfl))
    (reaches_of_steps 8 rfl) ?_
  refine obsRefines_of_continuation fun w _ => ?_
  cases w with
  | VCon k =>
    cases k with
    | Bool b =>
      cases b
      · exact obsRefines_of_reaches (reaches_of_steps 8 rfl) (reaches_of_steps 8 rfl)
          (assert_inside π ρ ρ u tb)
      · exact obsRefines_of_reaches (reaches_of_steps 8 rfl) (reaches_of_steps 8 rfl)
          (assert_inside π ρ ρ u ta)
    | _ => exact obsRefines_of_reaches (reaches_of_steps 7 rfl) (reaches_of_steps 7 rfl) (obsRefines_refl _)
  | _ => exact obsRefines_of_reaches (reaches_of_steps 7 rfl) (reaches_of_steps 7 rfl) (obsRefines_refl _)

/-- A Boolean consumed by a case instead of `ifThenElse`. -/
theorem layer_leaf {d : Nat} {F : CekEnv → Prop} (u : Const × BuiltinType) {tx : Term}
    (hb : ∀ ρ, F ρ → EnvWellFormed d ρ → d ≤ ρ.length → ∀ w, Halts ρ tx w → ∃ b, w = .VCon (.Bool b)) :
    FactRefines d F (assertT tx u) (.Case tx [.Error, .Constant u]) := by
  intro ρ π henv hlen _ hF
  refine obsRefines_of_reaches (assert_start π ρ _ u) (reaches_of_steps 1 rfl) ?_
  refine obsRefines_of_continuation fun w hw => ?_
  obtain ⟨b, rfl⟩ := hb ρ hF henv hlen w hw
  obtain ⟨c, ty⟩ := u
  cases b
  · exact obsRefines_of_reaches (iteFrames_false π ρ _) (reaches_of_steps 2 rfl) (obsRefines_refl _)
  · exact obsRefines_of_reaches (iteFrames_true π ρ _) (reaches_of_steps 2 rfl) (obsRefines_refl _)

/-- Alternatives that bind exactly the fields of their tag, with the consumer
    moved below their binders. -/
def Pushed (u : Const × BuiltinType) (k : Nat) (a a' : Term) : Prop :=
  ∃ (bs : List VarId) (tb : Term), bs.length = k ∧ a = lamChain bs tb ∧ a' = lamChain bs (assertT tb u)

theorem layer_case {d : Nat} {F : CekEnv → Prop} (u : Const × BuiltinType) {ts : Term}
    {talts talts' : List Term} (hlen : talts.length = talts'.length)
    (hp : ∀ ρ, F ρ → EnvWellFormed d ρ → d ≤ ρ.length → ∀ w, Halts ρ ts w → ∀ i fs a a',
      tagFields w = some (i, fs) → talts[i]? = some a → talts'[i]? = some a' → Pushed u fs.length a a') :
    FactRefines d F (assertT (.Case ts talts) u) (.Case ts talts') := by
  intro ρ π henv hlen' _ hF
  refine obsRefines_of_reaches (reaches_trans (assert_start π ρ _ u) (reaches_of_steps 1 rfl))
    (reaches_of_steps 1 rfl) ?_
  refine obsRefines_of_continuation fun w hw => ?_
  apply obsRefines_of_step
  rw [step_caseScrutinee, step_caseScrutinee]
  rcases dispatch_same hlen w with ⟨h1, h2⟩ | ⟨i, fs, a, a', htag, ha, ha', h1, h2⟩
  · rw [h1, h2]; exact obsRefines_refl _
  rw [h1, h2]
  simp only
  obtain ⟨bs, tb, hbl, rfl, rfl⟩ := hp ρ hF henv hlen' w hw i fs a a' htag ha ha'
  have r1 := lams_steps bs tb fs ρ (iteFrames ρ u ++ π) hbl.symm
  have r2 := lams_steps bs (assertT tb u) fs ρ π hbl.symm
  refine obsRefines_of_reaches r1 r2 ?_
  exact assert_inside π ρ (extendAll ρ fs) u tb

end Moist.Verified.Guards
