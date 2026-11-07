import Moist.Verified.ShapeFacts.Decompose

/-! # Evaluations with step counts

`HaltsIn ρ t n v`: `t` halts with `v` in exactly `n` steps from the empty stack.
A computation on a larger stack first runs the inner computation, which
takes no more steps than the whole (`lift_halt`, `counted_sequence`). These
bounds drive the step-indexed reasoning about recursive Boolean summaries.
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.Verified Moist.Verified.Equivalence
open Moist.Verified.StepLift (liftState isActive)

def HaltsIn (ρ : CekEnv) (t : Term) (n : Nat) (v : CekValue) : Prop :=
  steps n (.compute [] ρ t) = .halt v

theorem HaltsIn.halts {ρ : CekEnv} {t : Term} {n : Nat} {v : CekValue} (h : HaltsIn ρ t n v) :
    Halts ρ t v := ⟨n, h⟩

theorem halts_iff_haltsIn {ρ : CekEnv} {t : Term} {v : CekValue} : Halts ρ t v ↔ ∃ n, HaltsIn ρ t n v :=
  Iff.rfl

theorem steps_halt_mono {s : State} {v : CekValue} {m n : Nat} (h : steps m s = .halt v) (hmn : m ≤ n) :
    steps n s = .halt v := by
  rw [show n = m + (n - m) by omega, steps_trans, h, steps_halt]

private theorem steps_vstep (n : Nat) (s : State) : Semantics.steps n s = steps n s := rfl

/-- The part of a computation that runs above a base stack. -/
theorem lift_halt {s : State} {N : Nat} {v : CekValue} (base : Stack) (h : steps N s = .halt v) :
    ∃ K, K ≤ N ∧ steps K (liftState base s) = .ret base v := by
  have inactive : ∃ k, k ≤ N ∧ isActive (Semantics.steps k s) = false :=
    ⟨N, Nat.le_refl _, by rw [steps_vstep, h]; rfl⟩
  obtain ⟨K, hK, hinact, hactive⟩ := StepLift.firstInactive s N inactive
  have hlift : Semantics.steps K (liftState base s) = liftState base (Semantics.steps K s) :=
    StepLift.steps_liftState base K s hactive
  rw [steps_vstep, steps_vstep] at hlift
  rw [steps_vstep] at hinact
  refine ⟨K, hK, ?_⟩
  rw [hlift]
  generalize hsK : steps K s = sK at hinact
  have hrest : steps (N - K) sK = .halt v := by
    rw [← hsK, ← steps_trans, Nat.add_sub_cancel' hK, h]
  match sK, hinact with
  | .halt w, _ =>
    rw [steps_halt] at hrest; cases hrest; rfl
  | .ret [] w, _ =>
    cases hn : N - K with
    | zero => rw [hn] at hrest; cases hrest
    | succ m =>
      rw [hn] at hrest
      change steps m (.halt w) = .halt v at hrest
      rw [steps_halt] at hrest; cases hrest; rfl
  | .error, _ => rw [steps_error] at hrest; cases hrest
  | .compute _ _ _, hi => cases hi
  | .ret (_ :: _) _, hi => cases hi

/-- A halting computation on a stack first evaluates the term on the empty
    stack, in fewer steps. -/
theorem counted_sequence {π : Stack} {ρ : CekEnv} {t : Term} {N : Nat} {v : CekValue}
    (h : steps N (.compute π ρ t) = .halt v) :
    ∃ K w, K < N ∧ HaltsIn ρ t (K + 1) w ∧ steps (N - K) (.ret π w) = .halt v := by
  have inactive : ∃ k, k ≤ N ∧ isActive (Semantics.steps k (.compute [] ρ t)) = false := by
    apply Classical.byContradiction
    intro hno
    have hall : ∀ j, j < N + 1 → isActive (Semantics.steps j (.compute [] ρ t)) = true := by
      intro j hj
      cases hc : isActive (Semantics.steps j (.compute [] ρ t))
      · exact absurd ⟨j, by omega, hc⟩ hno
      · rfl
    have hlift := StepLift.steps_liftState π N (.compute [] ρ t) (fun j hj => hall j (by omega))
    rw [steps_vstep, steps_vstep] at hlift
    change steps N (.compute π ρ t) = _ at hlift
    rw [h] at hlift
    exact StepLift.liftState_ne_halt π _ v hlift.symm
  obtain ⟨K, hK, hinact, hactive⟩ := StepLift.firstInactive _ N inactive
  have hlift : Semantics.steps K (liftState π (.compute [] ρ t)) =
      liftState π (Semantics.steps K (.compute [] ρ t)) :=
    StepLift.steps_liftState π K _ hactive
  rw [steps_vstep, steps_vstep] at hlift
  rw [steps_vstep] at hinact
  change steps K (.compute π ρ t) = _ at hlift
  have hrest : steps (N - K) (steps K (.compute π ρ t)) = .halt v := by
    rw [← steps_trans, Nat.add_sub_cancel' hK, h]
  rw [hlift] at hrest
  generalize hsK : steps K (.compute [] ρ t) = sK at hinact hrest
  match sK, hinact with
  | .halt w, _ =>
    refine ⟨K, w, ?_, ?_, ?_⟩
    · apply Classical.byContradiction
      intro hge
      have : N - K = 0 := by omega
      rw [this] at hrest
      cases hrest
    · show steps (K + 1) _ = _
      rw [steps_trans, hsK]; rfl
    · exact hrest
  | .ret [] w, _ =>
    refine ⟨K, w, ?_, ?_, ?_⟩
    · apply Classical.byContradiction
      intro hge
      have : N - K = 0 := by omega
      rw [this] at hrest
      cases hrest
    · show steps (K + 1) _ = _
      rw [steps_trans, hsK]; rfl
    · exact hrest
  | .error, _ =>
    exfalso
    simp only [liftState, steps_error] at hrest
    cases hrest
  | .compute _ _ _, hi => cases hi
  | .ret (_ :: _) _, hi => cases hi

theorem steps_succ_of {s : State} {n : Nat} {T : State} (h : steps n s = T) (hs : s ≠ T) :
    ∃ m, n = m + 1 ∧ steps m (step s) = T := by
  cases n with
  | zero => exact absurd h hs
  | succ m => exact ⟨m, rfl, h⟩

theorem haltsIn_apply {ρ : CekEnv} {f a : Term} {N : Nat} {v : CekValue}
    (h : HaltsIn ρ (.Apply f a) N v) :
    ∃ Nf wf Na wa Nr, HaltsIn ρ f Nf wf ∧ HaltsIn ρ a Na wa ∧
      steps Nr (.ret [.funV wf] wa) = .halt v ∧ Nf + Na + Nr ≤ N := by
  obtain ⟨m, rfl, hm⟩ := steps_succ_of h (by simp)
  change steps m (.compute [.arg a ρ] ρ f) = _ at hm
  obtain ⟨K₁, wf, hK₁, hf, hrest⟩ := counted_sequence hm
  obtain ⟨m', hm'eq, hm'⟩ := steps_succ_of hrest (by simp)
  change steps m' (.compute [.funV wf] ρ a) = _ at hm'
  obtain ⟨K₂, wa, hK₂, ha, hrest'⟩ := counted_sequence hm'
  exact ⟨K₁ + 1, wf, K₂ + 1, wa, m' - K₂, hf, ha, hrest', by omega⟩

theorem haltsIn_force {ρ : CekEnv} {t : Term} {N : Nat} {v : CekValue}
    (h : HaltsIn ρ (.Force t) N v) :
    ∃ Nt w Nr, HaltsIn ρ t Nt w ∧ steps Nr (.ret [.force] w) = .halt v ∧ Nt + Nr ≤ N := by
  obtain ⟨m, rfl, hm⟩ := steps_succ_of h (by simp)
  change steps m (.compute [.force] ρ t) = _ at hm
  obtain ⟨K, w, hK, ht, hrest⟩ := counted_sequence hm
  exact ⟨K + 1, w, m - K, ht, hrest, by omega⟩

theorem haltsIn_case {ρ : CekEnv} {s : Term} {alts : List Term} {N : Nat} {v : CekValue}
    (h : HaltsIn ρ (.Case s alts) N v) :
    ∃ Ns w Nr, HaltsIn ρ s Ns w ∧ steps Nr (.ret [.caseScrutinee alts ρ] w) = .halt v ∧
      Ns + Nr ≤ N := by
  obtain ⟨m, rfl, hm⟩ := steps_succ_of h (by simp)
  change steps m (.compute [.caseScrutinee alts ρ] ρ s) = _ at hm
  obtain ⟨K, w, hK, hs, hrest⟩ := counted_sequence hm
  exact ⟨K + 1, w, m - K, hs, hrest, by omega⟩

theorem apply_lam_counted {body : Term} {ρ : CekEnv} {w v : CekValue} {N : Nat}
    (h : steps N (.ret [.funV (.VLam body ρ)] w) = .halt v) :
    ∃ M, M < N ∧ HaltsIn (ρ.extend w) body M v := by
  obtain ⟨m, rfl, hm⟩ := steps_succ_of h (by simp)
  exact ⟨m, by omega, hm⟩

theorem haltsIn_let {ρ : CekEnv} {n : Nat} {b r : Term} {N : Nat} {v : CekValue}
    (h : HaltsIn ρ (.Apply (.Lam n b) r) N v) :
    ∃ Nr w Nb, HaltsIn ρ r Nr w ∧ HaltsIn (ρ.extend w) b Nb v ∧ Nr + Nb < N := by
  obtain ⟨Nf, wf, Na, wa, Nr, hf, ha, hrest, hsum⟩ := haltsIn_apply h
  have hwf : wf = .VLam b ρ := halts_lam hf.halts
  subst hwf
  obtain ⟨M, hM, hb⟩ := apply_lam_counted hrest
  have : 0 < Nf := by
    cases Nf with
    | zero => simp [HaltsIn, steps] at hf
    | succ => omega
  exact ⟨Na, wa, M, ha, hb, by omega⟩

/-- An application spine: the head applied to the arguments in order. -/
def applySpineT : Term → List Term → Term
  | head, [] => head
  | head, a :: as => applySpineT (.Apply head a) as

theorem lift_ret {stk : Stack} {w v : CekValue} {N : Nat} (base : Stack)
    (h : steps N (.ret stk w) = .halt v) :
    ∃ K, K ≤ N ∧ steps K (.ret (stk ++ base) w) = .ret base v :=
  lift_halt base h

private theorem step_applyArg_funV (v w : CekValue) (π : Stack) :
    step (.ret (.applyArg v :: π) w) = step (.ret (.funV w :: π) v) := by
  cases w <;> rfl

/-- Evaluating an application spine evaluates the head, then each argument,
    then applies the head value to the argument values in order. -/
theorem haltsIn_spine {ρ : CekEnv} :
    ∀ (args : List Term) (head : Term) {N : Nat} {v : CekValue},
      HaltsIn ρ (applySpineT head args) N v →
      ∃ (Nh : Nat) (wh : CekValue) (vals : List CekValue) (Nc : Nat),
        HaltsIn ρ head Nh wh ∧ vals.length = args.length ∧
        (∀ (i : Nat) (ta : Term) (va : CekValue), args[i]? = some ta → vals[i]? = some va →
          ∃ n, n ≤ N ∧ HaltsIn ρ ta n va) ∧
        steps Nc (.ret (vals.map Frame.applyArg) wh) = .halt v ∧ Nh + Nc ≤ N + 1 := by
  intro args
  induction args with
  | nil =>
    intro head N v h
    exact ⟨N, v, [], 1, h, rfl, fun i _ _ h1 _ => by simp at h1, rfl, by omega⟩
  | cons a as ih =>
    intro head N v h
    obtain ⟨Nh', wh', vals, Nc', hh', hlen, hargs, hchain, hsum'⟩ := ih (.Apply head a) h
    obtain ⟨Nf, wf, Na, wa, Nr, hf, ha, hrest, hsum⟩ := haltsIn_apply hh'
    obtain ⟨K, hK, hlift⟩ := lift_halt (vals.map Frame.applyArg) hrest
    have hNc : 0 < Nc' := by
      cases Nc' with
      | zero => simp [steps] at hchain
      | succ => omega
    refine ⟨Nf, wf, wa :: vals, K + Nc', hf, by simp [hlen], ?_, ?_, by omega⟩
    · intro i ta va hta hva
      cases i with
      | zero =>
        simp at hta hva; subst hta; subst hva
        exact ⟨Na, by omega, ha⟩
      | succ i =>
        simp at hta hva
        exact hargs i ta va hta hva
    · simp only [List.map_cons]
      rw [steps_trans]
      have hK1 : ∃ m, K = m + 1 := by
        cases K with
        | zero => simp [liftState, steps] at hlift
        | succ m => exact ⟨m, rfl⟩
      obtain ⟨m, rfl⟩ := hK1
      have hstep : steps (m + 1) (.ret (.applyArg wa :: vals.map Frame.applyArg) wf) =
          steps (m + 1) (.ret (.funV wf :: vals.map Frame.applyArg) wa) := by
        show steps m (step _) = steps m (step _)
        rw [step_applyArg_funV]
      rw [hstep]
      change steps (m + 1) (liftState (vals.map Frame.applyArg) (.ret [.funV wf] wa)) = _ at hlift
      simp only [liftState, List.cons_append, List.nil_append] at hlift
      rw [hlift]
      exact hchain

end Moist.Verified.ShapeFacts
