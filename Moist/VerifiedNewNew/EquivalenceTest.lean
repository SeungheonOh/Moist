import Moist.VerifiedNewNew.Equivalence
import Moist.CEK.DecidableEq

/-! # Cross-term OpenEq proofs

  Non-trivial equivalences between syntactically different UPLC terms.
-/

namespace Moist.Verified.Equivalence.Test

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified.Equivalence
open Moist.Verified (closedAt closedAtList)

abbrev int (n : Int) : Term := .Constant (.Integer n, .AtomicType .TypeInteger)
abbrev lam (body : Term) : Term := .Lam 0 body
abbrev letIn (e body : Term) : Term := .Apply (lam body) e
abbrev add (a b : Term) : Term := .Apply (.Apply (.Builtin .AddInteger) a) b

private theorem steps_error_eq : ∀ n, steps n .error = .error := by
  intro n; induction n with
  | zero => rfl
  | succ n ih => simp [steps, step, ih]

private theorem never_halts_compute_error (n : Nat) (v : CekValue) (π : Stack) (ρ : CekEnv) :
    steps n (.compute π ρ .Error) ≠ .halt v := by
  match n with
  | 0 => simp [steps]
  | n + 1 => simp [steps, step]; rw [steps_error_eq]; exact State.noConfusion

private theorem never_halts_let_error (body : Term) (n : Nat) (v : CekValue)
    (π : Stack) (ρ : CekEnv) :
    steps n (.compute π ρ (letIn .Error body)) ≠ .halt v := by
  match n with
  | 0 => simp [steps]
  | 1 => simp [steps, step]
  | 2 => simp [steps, step]
  | 3 => simp [steps, step]
  | n + 4 => simp [steps, step]; rw [steps_error_eq]; exact State.noConfusion

--------------------------------------------------------------------------------
-- 1. Error ≈ let x = Error in body
--------------------------------------------------------------------------------

theorem error_eq_let_error {body : Term} :
    OpenEq 0 .Error (letIn .Error body) := by
  intro k j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  constructor
  · intro v ⟨n, _, hs⟩; exact absurd hs (never_halts_compute_error n v π₁ ρ₁)
  · intro v ⟨n, _, hs⟩; exact absurd hs (never_halts_let_error body n v π₂ ρ₂)

--------------------------------------------------------------------------------
-- 2. let x = Error in body₁ ≈ let x = Error in body₂
--------------------------------------------------------------------------------

theorem let_error_eq {body₁ body₂ : Term} :
    OpenEq 0 (letIn .Error body₁) (letIn .Error body₂) := by
  intro k j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  constructor
  · intro v ⟨n, _, hs⟩; exact absurd hs (never_halts_let_error body₁ n v π₁ ρ₁)
  · intro v ⟨n, _, hs⟩; exact absurd hs (never_halts_let_error body₂ n v π₂ ρ₂)

--------------------------------------------------------------------------------
-- 3. Error ≈ Apply Error t
--------------------------------------------------------------------------------

theorem error_eq_apply_error {t : Term} :
    OpenEq 0 .Error (.Apply .Error t) := by
  intro k j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  constructor
  · intro v ⟨n, _, hs⟩; exact absurd hs (never_halts_compute_error n v π₁ ρ₁)
  · intro v ⟨n, _, hs⟩
    match n with
    | 0 => simp [steps] at hs
    | 1 => simp [steps, step] at hs
    | n + 2 => simp [steps, step] at hs; rw [steps_error_eq] at hs; exact absurd hs State.noConfusion

--------------------------------------------------------------------------------
-- 4. Error ≈ Force Error
--------------------------------------------------------------------------------

theorem error_eq_force_error :
    OpenEq 0 .Error (.Force .Error) := by
  intro k j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  constructor
  · intro v ⟨n, _, hs⟩; exact absurd hs (never_halts_compute_error n v π₁ ρ₁)
  · intro v ⟨n, _, hs⟩
    match n with
    | 0 => simp [steps] at hs
    | 1 => simp [steps, step] at hs
    | n + 2 => simp [steps, step] at hs; rw [steps_error_eq] at hs; exact absurd hs State.noConfusion

--------------------------------------------------------------------------------
-- 5. COUNTEREXAMPLE ATTEMPT: int 2 ~ int 1
--
-- Hypothesis: ObsEqK not comparing halted values allows proving 2 ~ 1.
-- Result: The proof gets STUCK. The biorthogonal closure (StackRelK) provides
-- enough discrimination via case frames + constToTagAndFields, which maps
-- non-negative Integer n to constructor tag n.
--------------------------------------------------------------------------------

/-- Discriminating stack: case-splits the integer value directly.
    constToTagAndFields maps Integer n (n ≥ 0) to tag n.
    Branch 0 → Error, Branch 1 → Error, Branch 2 → Constant Unit (halts). -/
private abbrev discrimStack : Stack :=
  [Frame.caseScrutinee [.Error, .Error, .Constant (.Unit, .AtomicType .TypeUnit)] .nil]

/-- int 2 with discrimStack halts in 4 steps:
    compute→ret (VCon 2)→case tag 2→compute Unit→ret Unit→halt -/
private theorem discrim_halts_on_2 :
    steps 4 (.compute discrimStack .nil (int 2)) = .halt (.VCon .Unit) := by
  native_decide

/-- int 1 with discrimStack errors in 3 steps:
    compute→ret (VCon 1)→case tag 1→Error→error -/
private theorem discrim_errors_on_1 :
    steps 3 (.compute discrimStack .nil (int 1)) = .error := by
  native_decide

/-- PROOF ATTEMPT: int 2 ~ int 1.
    Gets stuck after one reduction step. The goal demands ObsEqK for
    VCon (Integer 2) vs VCon (Integer 1) returned to universally-quantified
    StackRelK-related stacks, but StackRelK only helps for ValueEqK-related
    values — and ValueEqK (k+1) (VCon c₁) (VCon c₂) requires c₁ = c₂.

    The concrete witness `discrimStack` shows the goal is actually FALSE:
    it IS StackRelK-related with itself (same constant → same tag → same branch),
    yet it separates VCon 2 from VCon 1 (one halts, the other errors). -/
theorem two_eq_one : OpenEq 0 (int 2) (int 1) := by
  intro k j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  match i with
  | 0 =>
    -- Vacuously true: both sides are .compute states (non-halt), 0 steps can't reach halt.
    refine ⟨fun v ⟨n, hn, hs⟩ => ?_, fun v ⟨n, hn, hs⟩ => ?_⟩ <;> {
      have : n = 0 := by omega
      subst this; exact absurd hs State.noConfusion
    }
  | i' + 1 =>
    apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
    simp only [step]
    -- STUCK. Goal: ObsEqK i' (.ret π₁ (.VCon (.Integer 2))) (.ret π₂ (.VCon (.Integer 1)))
    --
    -- hπ : StackRelK ValueEqK (i' + 1) π₁ π₂
    -- Using hπ at j' = i' requires: ValueEqK i' (.VCon (.Integer 2)) (.VCon (.Integer 1))
    -- For i' ≥ 1 this reduces to (.Integer 2 = .Integer 1) — FALSE.
    --
    -- Cannot proceed: π₁, π₂ are universally quantified so we cannot step through them,
    -- and StackRelK is the only hypothesis connecting π₁ to π₂.
    --
    -- The discriminating stack `discrimStack` is a concrete countermodel:
    --   • StackRelK ValueEqK i discrimStack discrimStack holds
    --     (ValueEqK-related VCon values have the same constant → same tag → same branch)
    --   • Yet discrim_halts_on_2 shows int 2 halts, discrim_errors_on_1 shows int 1 errors.
    sorry

--------------------------------------------------------------------------------
-- 6. λx. (1+2)+3 ≈ λx. 6   (constant folding)
--
--    Both are closed lambdas. When applied to any argument v:
--    - LHS body `(1+2)+3` evaluates through the AddInteger builtin pipeline
--      to `VCon (Integer 6)` in ~10 steps (independent of v and the env).
--    - RHS body `int 6` evaluates to `VCon (Integer 6)` in 1 step.
--    Both reach `ret π (VCon (Integer 6))`, so the continuation is identical.
--
--    The key computational fact (verified by native_decide on a concrete env):
--------------------------------------------------------------------------------

/-- Evaluating `(1+2)+3` under the empty env yields `VCon (Integer 6)`.
    This is the computational core of the constant folding proof. -/
private theorem int6_eval :
    steps 1 (.compute [] .nil (int 6))
    = .ret [] (.VCon (.Integer 6)) := by rfl

/-- `(1+2)+3` evaluates to `VCon (Integer 6)` in 17 steps. Discharged by
    `native_decide` using `DecidableEq State`. -/
private theorem add_123_eval :
    steps 17 (.compute [] .nil (add (add (int 1) (int 2)) (int 3)))
    = .ret [] (.VCon (.Integer 6)) := by
  native_decide

/-- λx. (1+2)+3 ≈ λx. 6 — constant folding.
    Both lambdas produce closures whose bodies evaluate to VCon (Integer 6).
    Requires: (1) builtin evaluation correctness (add_123_eval),
              (2) closed-term environment independence. -/
theorem lam_add_123_eq_lam_6 :
    OpenEq 0 (lam (add (add (int 1) (int 2)) (int 3))) (lam (int 6)) := by
  sorry -- Requires add_123_eval + env-independence for closed terms

end Moist.Verified.Equivalence.Test
