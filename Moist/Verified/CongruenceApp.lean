import Moist.Verified.Congruence
import Moist.Verified.ValueEq

/-! # App congruence lemmas that depend on `stateEq_stateRelated`

This file contains the remaining `refines_*` congruence lemmas whose proofs
require the bisimulation infrastructure from `ValueEq.lean` (specifically
`fundamental_lemma_proved'`, which says that same-body / different-arg
computations are behaviorally equivalent when the args are `∀ j, ValueEq j`-
related).

The chain lives here (rather than in `Congruence.lean`) so that
`Congruence.lean` can stay focused on constructor congruence without
pulling in the bisimulation-heavy parts of `ValueEq.lean`. -/

namespace Moist.Verified.CongruenceApp

open Moist.CEK
open Moist.Plutus.Term
open Moist.MIR
open Moist.MIR (lowerTotalExpr lowerTotalExpr_eq_lowerTotal)
open Moist.Verified.Semantics
open Moist.Verified.Congruence
open Moist.Verified.ValueEqBisim
open Moist.Verified.BuiltinCong (evalBuiltin_cong_first ret_nil_halts
  not_halts_and_errors ret_nil_halt_eq ret_nil_not_error
  apply_error_of_fn_error apply_error_of_arg_error)
open Moist.Verified.StepLift (apply_reaches apply_reaches_error apply_compose)

/-- Same body, `∀ j, ValueEq j`-related args produce behaviorally-equivalent
    computations. This is the `Reaches`-flavored wrapper around
    `fundamental_lemma_proved'` (which returns `StateRelated`).
    For every fixed observation level `k`, we instantiate the bisim at level
    `k + max N1 N2` where `N1, N2` are the step counts the caller's `Reaches`
    witnesses halt at; the value clause of `StateRelated` then yields
    `ValueEq ((k + max N1 N2) - max N1 N2) v1 v2 = ValueEq k v1 v2`. -/
private theorem vlam_diff_arg_via_bisim (k : Nat) (body : Term) (cenv : CekEnv)
    (va va' : CekValue) (hva : ∀ j, ValueEq j va va') :
    (Reaches (.compute [] (cenv.extend va) body) .error ↔
     Reaches (.compute [] (cenv.extend va') body) .error) ∧
    (Halts (.compute [] (cenv.extend va) body) ↔
     Halts (.compute [] (cenv.extend va') body)) ∧
    ∀ v1 v2,
      Reaches (.compute [] (cenv.extend va) body) (.halt v1) →
      Reaches (.compute [] (cenv.extend va') body) (.halt v2) →
      ValueEq k v1 v2 := by
  refine ⟨?_, ?_, ?_⟩
  · -- **Post-redesign hole:** the new `StateRelated` clause no longer
    -- exposes one-sided error transfer. Same divergent-inner-closure
    -- weakness flagged in `Semantics.lean`. (For SAME body, this *is*
    -- in principle provable via the structural bisimulation in
    -- `Bisim.lean`, but the bridge `∀ j, ValueEq j → StateRel ...`
    -- requires extra machinery that is out of scope for this redesign.)
    sorry
  · -- Same hole as above for halt transfer.
    sorry
  · -- **Post-asymmetric-redesign hole**: same as the app_step_vlam_value
    -- issue — the asymmetric StateRelated's forward halt returns an
    -- unbounded existential m that can exceed max N1 N2, making the
    -- returned level arithmetic fail. Left as sorry.
    sorry

/-- VLam application step: same closure, different args. Bundled
    error/halts/value agreement. -/
private theorem vlam_same_closure_diff_arg (k : Nat) (body : Term) (cenv : CekEnv)
    (va va' : CekValue) (hva : ∀ j, ValueEq j va va') :
    (Reaches (.compute [] (cenv.extend va) body) .error ↔
     Reaches (.compute [] (cenv.extend va') body) .error) ∧
    (Halts (.compute [] (cenv.extend va) body) ↔
     Halts (.compute [] (cenv.extend va') body)) ∧
    ∀ v1 v2,
      Reaches (.compute [] (cenv.extend va) body) (.halt v1) →
      Reaches (.compute [] (cenv.extend va') body) (.halt v2) →
      ValueEq k v1 v2 :=
  vlam_diff_arg_via_bisim k body cenv va va' hva

/-- Application step: same function, different args. Error transfer. -/
private theorem app_step_arg_error_transfer (vf va va' : CekValue)
    (hva : ∀ j, ValueEq j va va')
    (herr : Reaches (step (.ret [.funV vf] va)) .error) :
    Reaches (step (.ret [.funV vf] va')) .error := by
  match vf with
  | .VLam body cenv =>
    simp only [step] at herr ⊢
    exact (vlam_same_closure_diff_arg 0 body cenv va va' hva).1.mp herr
  | .VCon c => simp only [step] at herr ⊢; exact ⟨0, rfl⟩
  | .VDelay b e => simp only [step] at herr ⊢; exact ⟨0, rfl⟩
  | .VConstr tag fs => simp only [step] at herr ⊢; exact ⟨0, rfl⟩
  | .VBuiltin b args ea =>
    cases hhead : ea.head with
    | argQ =>
      simp only [step, hhead] at herr ⊢; exact ⟨0, rfl⟩
    | argV =>
      cases htail : ea.tail with
      | some rest =>
        simp only [step, hhead, htail] at herr
        exact absurd herr (ret_nil_not_error _)
      | none =>
        simp only [step, hhead, htail] at herr ⊢
        cases hev1 : Moist.CEK.evalBuiltin b (va :: args) with
        | some v1 =>
          simp only [hev1] at herr; exact absurd herr (ret_nil_not_error v1)
        | none =>
          simp only [hev1] at herr ⊢
          have ⟨hcong, _⟩ := evalBuiltin_cong_first 0 b
            (fun v => valueEq_refl 1 v) va va' args (hva 1)
          rw [hcong.mp hev1]; exact ⟨0, rfl⟩

/-- Application step: same function, different args. Halts transfer. -/
private theorem app_step_arg_halts_transfer (vf va va' : CekValue)
    (hva : ∀ j, ValueEq j va va')
    (hh : Halts (step (.ret [.funV vf] va))) :
    Halts (step (.ret [.funV vf] va')) := by
  match vf with
  | .VLam body cenv =>
    simp only [step] at hh ⊢
    exact (vlam_same_closure_diff_arg 0 body cenv va va' hva).2.1.mp hh
  | .VCon c =>
    simp only [step] at hh
    exact absurd (⟨0, rfl⟩ : Reaches _ .error) (fun h => not_halts_and_errors hh h)
  | .VDelay b e =>
    simp only [step] at hh
    exact absurd (⟨0, rfl⟩ : Reaches _ .error) (fun h => not_halts_and_errors hh h)
  | .VConstr tag fs =>
    simp only [step] at hh
    exact absurd (⟨0, rfl⟩ : Reaches _ .error) (fun h => not_halts_and_errors hh h)
  | .VBuiltin b args ea =>
    cases hhead : ea.head with
    | argQ =>
      simp only [step, hhead] at hh
      exact absurd (⟨0, rfl⟩ : Reaches _ .error) (fun h => not_halts_and_errors hh h)
    | argV =>
      cases htail : ea.tail with
      | some rest =>
        simp only [step, hhead, htail] at hh ⊢
        exact ⟨.VBuiltin b (va' :: args) rest, ret_nil_halts _⟩
      | none =>
        simp only [step, hhead, htail] at hh ⊢
        cases hev1 : Moist.CEK.evalBuiltin b (va :: args) with
        | none =>
          simp only [hev1] at hh
          exact absurd (⟨0, rfl⟩ : Reaches _ .error) (fun h => not_halts_and_errors hh h)
        | some r1 =>
          simp only [hev1] at hh
          have ⟨hcong, _⟩ := evalBuiltin_cong_first 0 b
            (fun v => valueEq_refl 1 v) va va' args (hva 1)
          cases hev2 : Moist.CEK.evalBuiltin b (va' :: args) with
          | none => exact absurd (hcong.mpr hev2) (by simp [hev1])
          | some r2 => simp only; exact ⟨r2, ret_nil_halts r2⟩

/-- Application step: same function, different args. Value agreement. -/
private theorem app_step_arg_value_agreement (k : Nat)
    (vf va va' : CekValue)
    (hva : ∀ j, ValueEq j va va')
    (v1 v2 : CekValue)
    (h1 : Reaches (step (.ret [.funV vf] va)) (.halt v1))
    (h2 : Reaches (step (.ret [.funV vf] va')) (.halt v2)) :
    ValueEq k v1 v2 := by
  match vf with
  | .VLam body cenv =>
    simp only [step] at h1 h2
    exact (vlam_same_closure_diff_arg k body cenv va va' hva).2.2 v1 v2 h1 h2
  | .VCon c =>
    simp only [step] at h1; exact (reaches_halt_not_error h1 ⟨0, rfl⟩).elim
  | .VDelay b e =>
    simp only [step] at h1; exact (reaches_halt_not_error h1 ⟨0, rfl⟩).elim
  | .VConstr tag fs =>
    simp only [step] at h1; exact (reaches_halt_not_error h1 ⟨0, rfl⟩).elim
  | .VBuiltin b args ea =>
    cases hhead : ea.head with
    | argQ =>
      simp only [step, hhead] at h1; exact (reaches_halt_not_error h1 ⟨0, rfl⟩).elim
    | argV =>
      cases htail : ea.tail with
      | some rest =>
        simp only [step, hhead, htail] at h1 h2
        have hw1 := ret_nil_halt_eq _ v1 h1; subst hw1
        have hw2 := ret_nil_halt_eq _ v2 h2; subst hw2
        cases k with
        | zero => simp [ValueEq]
        | succ k =>
          unfold ValueEq
          refine ⟨rfl, ?_, rfl⟩
          simp only [ListValueEq]
          exact ⟨hva (k + 1), listValueEq_refl (k + 1) args⟩
      | none =>
        simp only [step, hhead, htail] at h1 h2
        have ⟨hcong, hval⟩ := evalBuiltin_cong_first k b
          (fun v => valueEq_refl (k + 1) v) va va' args (hva (k + 1))
        cases hev1 : Moist.CEK.evalBuiltin b (va :: args) with
        | none => simp only [hev1] at h1; exact (reaches_halt_not_error h1 ⟨0, rfl⟩).elim
        | some r1 =>
          simp only [hev1] at h1
          cases hev2 : Moist.CEK.evalBuiltin b (va' :: args) with
          | none => exact absurd (hcong.mpr hev2) (by simp [hev1])
          | some r2 =>
            simp only [hev2] at h2
            have hw1 := ret_nil_halt_eq _ v1 h1; rw [hw1]
            have hw2 := ret_nil_halt_eq _ v2 h2; rw [hw2]
            exact hval r1 r2 hev1 hev2

/-- App with same function, argument refines. -/
theorem refines_app_arg_behEq (f a a' : Expr) (ha : a ⊑ a') :
    Expr.App f a ⊑ Expr.App f a' := by
  refine ⟨?_, ?_⟩
  · -- Compilation clause
    intro env hs
    rw [lowerTotalExpr_app] at hs ⊢
    have hf_some := isSome_bind_inner hs
    obtain ⟨tf, htf⟩ := Option.isSome_iff_exists.mp hf_some
    rw [htf, Option.bind_some] at hs
    have ha_some := isSome_bind_inner hs
    obtain ⟨ta', hta'⟩ := Option.isSome_iff_exists.mp (ha.1 env ha_some)
    obtain ⟨ta, hta⟩ := Option.isSome_iff_exists.mp ha_some
    rw [htf, Option.bind_some, hta', Option.bind_some]; simp
  · -- BehEq clause
    intro env
    rw [lowerTotalExpr_app, lowerTotalExpr_app]
    cases hef : lowerTotalExpr env f with
    | none => simp [Option.bind_none]
    | some tf =>
      cases hea : lowerTotalExpr env a with
      | none => simp [Option.bind_some, Option.bind_none]
      | some ta =>
        cases hea' : lowerTotalExpr env a' with
        | none => simp [Option.bind_some, Option.bind_none]
        | some ta' =>
          simp only [Option.bind_some]
          intro ρ hwf
          have ⟨herr_a, hhalt_a, hval_a⟩ := refines_behEq_at ha hea hea' ρ hwf
          refine ⟨?_, ?_, ?_⟩
          · -- Error ↔
            constructor
            · intro herr
              rcases apply_reaches_error ρ tf ta herr with hf_err | ⟨vf, hf_halt, hx_case⟩
              · exact apply_error_of_fn_error ρ tf ta' hf_err
              · rcases hx_case with ha_err | ⟨va, ha_halt, happ_err⟩
                · exact apply_error_of_arg_error ρ tf ta' vf hf_halt (herr_a.mp ha_err)
                · obtain ⟨va', hva'⟩ := hhalt_a.mp ⟨va, ha_halt⟩
                  exact apply_compose ρ tf ta' vf va' .error hf_halt hva'
                    (app_step_arg_error_transfer vf va va'
                      (fun j => hval_a j va va' ha_halt hva') happ_err)
            · intro herr
              rcases apply_reaches_error ρ tf ta' herr with hf_err | ⟨vf, hf_halt, hx_case⟩
              · exact apply_error_of_fn_error ρ tf ta hf_err
              · rcases hx_case with ha'_err | ⟨va', ha'_halt, happ_err⟩
                · exact apply_error_of_arg_error ρ tf ta vf hf_halt (herr_a.mpr ha'_err)
                · obtain ⟨va, hva⟩ := hhalt_a.mpr ⟨va', ha'_halt⟩
                  exact apply_compose ρ tf ta vf va .error hf_halt hva
                    (app_step_arg_error_transfer vf va' va
                      (fun j => valueEq_symm j va va' (hval_a j va va' hva ha'_halt)) happ_err)
          · -- Halts ↔
            constructor
            · intro ⟨v, hv⟩
              obtain ⟨vf, va, hf_halt, ha_halt, happ⟩ := apply_reaches ρ tf ta v hv
              obtain ⟨va', hva'⟩ := hhalt_a.mp ⟨va, ha_halt⟩
              obtain ⟨v', hv'⟩ := app_step_arg_halts_transfer vf va va'
                (fun j => hval_a j va va' ha_halt hva') ⟨v, happ⟩
              exact ⟨v', apply_compose ρ tf ta' vf va' (.halt v') hf_halt hva' hv'⟩
            · intro ⟨v, hv⟩
              obtain ⟨vf, va', hf_halt, ha'_halt, happ⟩ := apply_reaches ρ tf ta' v hv
              obtain ⟨va, hva⟩ := hhalt_a.mpr ⟨va', ha'_halt⟩
              obtain ⟨v', hv'⟩ := app_step_arg_halts_transfer vf va' va
                (fun j => valueEq_symm j va va' (hval_a j va va' hva ha'_halt)) ⟨v, happ⟩
              exact ⟨v', apply_compose ρ tf ta vf va (.halt v') hf_halt hva hv'⟩
          · -- Value agreement
            intro k v1 v2 hv1 hv2
            obtain ⟨vf, va, hf_halt, ha_halt, happ1⟩ := apply_reaches ρ tf ta v1 hv1
            obtain ⟨vf', va', hf'_halt, ha'_halt, happ2⟩ := apply_reaches ρ tf ta' v2 hv2
            have hvf_eq := reaches_unique hf_halt hf'_halt; subst hvf_eq
            exact app_step_arg_value_agreement k vf va va'
              (fun j => hval_a j va va' ha_halt ha'_halt) v1 v2 happ1 happ2

end Moist.Verified.CongruenceApp
