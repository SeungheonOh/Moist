import Moist.Verified.FailFastSoundness.Termination
import Moist.Verified.KnownListsSoundness
import Moist.MIR.Optimize.Advanced.Guards

/-! # Results, sizes and calls

The semantic counterparts of the termination analysis `chk`:

* `ModeV m v`: a returned value satisfies the value mode `m`;
* `Ends m s`: the state errors, or halts with a value satisfying `m`;
* `vsize v`: the size of a value; every field a case passes to an
  alternative is smaller than the scrutinee, and so is the tail of a list;
* `CallsOK m Ps f`: applying `f` to arguments satisfying the predicates `Ps`
  terminates, the final result satisfying `m`.
-/

namespace Moist.Verified.Guards

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast

/-! ## Modes -/

def ModeV : VMode → CekValue → Prop
  | .term, _ => True
  | .inert, v => InertV v
  | .bool, v => ∃ b, v = .VCon (.Bool b)
  | .constrs ks, v => ∃ tag fs, v = .VConstr tag fs ∧ ∀ k, ks[tag]? = some k → fs.length = k

theorem modeV_term (v : CekValue) : ModeV .term v := trivial

theorem ModeV.inert : ∀ {m : VMode} {v : CekValue}, m ≠ .term → ModeV m v → InertV v
  | .term, _, h, _ => absurd rfl h
  | .inert, _, _, h => h
  | .bool, _, _, ⟨_, h⟩ => by subst h; trivial
  | .constrs _, _, _, ⟨_, _, h, _⟩ => by subst h; trivial

theorem VMode.covers_sound : ∀ {got want : VMode}, got.covers want = true →
    ∀ {v : CekValue}, ModeV got v → ModeV want v
  | _, .term, _, _, _ => trivial
  | .inert, .inert, _, _, h => h
  | .bool, .inert, _, _, h => ModeV.inert (by decide) h
  | .constrs _, .inert, _, _, h => ModeV.inert (by simp) h
  | .bool, .bool, _, _, h => h
  | .constrs ks, .constrs ks', hc, _, h => by
    simp only [VMode.covers, beq_iff_eq] at hc
    subst hc; exact h
  | .term, .inert, h, _, _ | .term, .bool, h, _, _ | .term, .constrs _, h, _, _
  | .inert, .bool, h, _, _ | .inert, .constrs _, h, _, _ | .bool, .constrs _, h, _, _
  | .constrs _, .bool, h, _, _ => by simp [VMode.covers] at h

theorem VMode.applied_ne_term : ∀ (m : VMode), m.applied ≠ .term
  | .term => by simp [VMode.applied]
  | .inert => by simp [VMode.applied]
  | .bool => by simp [VMode.applied]
  | .constrs _ => by simp [VMode.applied]

theorem VMode.applied_sound : ∀ {m : VMode} {v : CekValue}, ModeV m.applied v → ModeV m v
  | .term, _, _ => trivial
  | .inert, _, h => h
  | .bool, _, h => h
  | .constrs _, _, h => h

/-- Errors, or halts with a value of the mode. -/
def Ends (m : VMode) (s : State) : Prop := Reaches s .error ∨ ∃ r, Reaches s (.halt r) ∧ ModeV m r

theorem Ends.of_reaches {m : VMode} {s s' : State} (h : Reaches s s') (h' : Ends m s') : Ends m s := by
  rcases h' with h' | ⟨r, hr, hm⟩
  · exact .inl (reaches_trans h h')
  · exact .inr ⟨r, reaches_trans h hr, hm⟩

theorem Ends.error (m : VMode) : Ends m .error := .inl (reaches_refl _)

theorem Ends.mono {m m' : VMode} {s : State} (h : Ends m s) (hm : ∀ v, ModeV m v → ModeV m' v) :
    Ends m' s := by
  rcases h with h | ⟨r, hr, hv⟩
  · exact .inl h
  · exact .inr ⟨r, hr, hm r hv⟩

theorem Ends.termState {m : VMode} {s : State} (h : Ends m s) : TermState s := by
  rcases h with h | ⟨r, hr, _⟩
  · exact .inl h
  · exact .inr ⟨r, hr⟩

theorem ends_ret_nil {m : VMode} {v : CekValue} (h : ModeV m v) : Ends m (.ret [] v) :=
  .inr ⟨v, reaches_of_steps 1 rfl, h⟩

/-- A value of a mode other than `term` returned to further fields. -/
theorem ends_ret_fields {m : VMode} {v : CekValue} (h : ModeV m v) (hm : m ≠ .term) :
    ∀ fields : List CekValue, Ends m (.ret (fields.map Frame.applyArg) v)
  | [] => ends_ret_nil h
  | f :: _ => .inl (reaches_of_steps 1 (inert_apply_errors (ModeV.inert hm h) f _))

/-- Evaluate `t`, then continue on the stack. -/
theorem ends_compute {m : VMode} {π : Stack} {ρ : CekEnv} {t : Term}
    (ht : Errs ρ t ∨ ∃ v, Halts ρ t v) (hk : ∀ v, Halts ρ t v → Ends m (.ret π v)) :
    Ends m (.compute π ρ t) := by
  rcases ht with he | ⟨v, hv⟩
  · exact .inl (errs_on_stack he π)
  · exact Ends.of_reaches (halts_on_stack hv π) (hk v hv)

theorem ends_nil_iff {m : VMode} {ρ : CekEnv} {t : Term} :
    Ends m (.compute [] ρ t) ↔ (Errs ρ t ∨ ∃ v, Halts ρ t v ∧ ModeV m v) := Iff.rfl

/-! ## Sizes of values -/

noncomputable section
mutual
  def vsize : CekValue → Nat
    | .VCon c => sizeOf c
    | .VConstr _ fs => 1 + vsizeList fs
    | _ => 0

  def vsizeList : List CekValue → Nat
    | [] => 0
    | v :: vs => vsize v + vsizeList vs
end
end

theorem vsize_le_list : ∀ {fs : List CekValue} {f : CekValue}, f ∈ fs → vsize f ≤ vsizeList fs
  | [], _, h => by cases h
  | g :: gs, f, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp only [vsizeList]; omega
    · have := vsize_le_list h; simp only [vsizeList]; omega

theorem constToTagAndFields_smaller {c : Const} {tag n : Nat} {fs : List CekValue}
    (h : constToTagAndFields c = some (tag, n, fs)) : ∀ f ∈ fs, vsize f < vsize (.VCon c) := by
  intro f hf
  cases c with
  | ConstList l =>
    cases l with
    | nil => simp [constToTagAndFields] at h; obtain ⟨_, _, rfl⟩ := h; cases hf
    | cons a t =>
      simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, rfl⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl <;> simp [vsize] <;> omega
  | ConstDataList l =>
    cases l with
    | nil => simp [constToTagAndFields] at h; obtain ⟨_, _, rfl⟩ := h; cases hf
    | cons a t =>
      simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, rfl⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl <;> simp [vsize] <;> omega
  | ConstPairDataList l =>
    cases l with
    | nil => simp [constToTagAndFields] at h; obtain ⟨_, _, rfl⟩ := h; cases hf
    | cons a t =>
      simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, rfl⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl <;> simp [vsize] <;> omega
  | Pair p =>
    obtain ⟨a, b⟩ := p
    simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, rfl⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> simp [vsize] <;> omega
  | PairData p =>
    obtain ⟨a, b⟩ := p
    simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, rfl⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> simp [vsize] <;> omega
  | Bool b =>
    cases b <;> simp [constToTagAndFields] at h <;> obtain ⟨_, _, rfl⟩ := h <;> cases hf
  | Unit => simp [constToTagAndFields] at h; obtain ⟨_, _, rfl⟩ := h; cases hf
  | Integer i =>
    simp only [constToTagAndFields] at h
    split at h
    · cases h; cases hf
    · cases h
  | _ => simp [constToTagAndFields] at h

/-- Every field a case dispatch passes is smaller than the scrutinee. -/
theorem dispatch_smaller {alts : List Term} {w : CekValue} {alt : Term} {fs : List CekValue}
    (h : dispatch alts w = some (alt, fs)) : ∀ f ∈ fs, vsize f < vsize w := by
  intro f hf
  cases w with
  | VConstr tag gs =>
    simp only [dispatch] at h
    cases hl : alts[tag]? with
    | none => rw [hl] at h; cases h
    | some a =>
      rw [hl] at h; cases h
      have := vsize_le_list hf
      simp only [vsize]; omega
  | VCon c =>
    simp only [dispatch] at h
    cases hc : constToTagAndFields c with
    | none => rw [hc] at h; cases h
    | some r =>
      obtain ⟨tag, n, gs⟩ := r
      rw [hc] at h
      simp only at h
      split at h
      · cases h
      · cases hl : alts[tag]? with
        | none => rw [hl] at h; cases h
        | some a =>
          rw [hl] at h; cases h
          exact constToTagAndFields_smaller hc f hf
  | VLam _ _ => cases h
  | VDelay _ _ => cases h
  | VBuiltin _ _ _ => cases h

/-- The tail of a list is smaller than the list. -/
theorem tailList_smaller {w v : CekValue} (h : evalBuiltin .TailList [w] = some v) :
    vsize v < vsize w := by
  obtain ⟨c, r, rfl, hc, rfl⟩ := evalBuiltin_single (by decide) h
  cases c <;> (try cases hc)
  all_goals (rename_i l; cases l <;> cases hc; simp [vsize]; omega)

/-! ## Calls -/

/-- Applying `f` to arguments satisfying `Ps`, one at a time, terminates;
    the last result satisfies `m`. -/
def CallsOK (m : VMode) : List (CekValue → Prop) → CekValue → Prop
  | [], v => ModeV m v
  | P :: Ps, f => ∀ w, ValueWellFormed w → P w →
      Reaches (.ret [.funV f] w) .error ∨
        ∃ r, Reaches (.ret [.funV f] w) (.halt r) ∧ CallsOK m Ps r

/-! ## Running a computation under a larger stack -/

theorem lift_first_inactive {s s' : State} {n : Nat}
    (reaches : Moist.Verified.Equivalence.steps n s = s')
    (inactive : Moist.Verified.StepLift.isActive s' = false) :
    ∃ K, K ≤ n ∧ Moist.Verified.StepLift.isActive (Moist.Verified.Equivalence.steps K s) = false ∧
      Moist.Verified.Equivalence.steps (n - K) (Moist.Verified.Equivalence.steps K s) = s' ∧
      ∀ base, Moist.Verified.Equivalence.steps K (Moist.Verified.StepLift.liftState base s) =
        Moist.Verified.StepLift.liftState base (Moist.Verified.Equivalence.steps K s) := by
  rw [Moist.Verified.BetaValueRefines.vstep_eq] at reaches
  obtain ⟨K, bound, inactive, active⟩ := Moist.Verified.StepLift.firstInactive _ n
    ⟨n, Nat.le_refl _, by rw [reaches]; exact inactive⟩
  refine ⟨K, bound, by rw [Moist.Verified.BetaValueRefines.vstep_eq]; exact inactive, ?_, ?_⟩
  · rw [← Moist.Verified.Equivalence.steps_trans, Nat.add_sub_cancel' bound,
      Moist.Verified.BetaValueRefines.vstep_eq, reaches]
  · intro base
    rw [Moist.Verified.BetaValueRefines.vstep_eq, Moist.Verified.BetaValueRefines.vstep_eq]
    exact Moist.Verified.StepLift.steps_liftState base K s active

/-- A halt reached from a state is a return to any base stack. -/
theorem reaches_lift_halt {s : State} {r : CekValue} (h : Reaches s (.halt r)) (base : Stack) :
    Reaches (Moist.Verified.StepLift.liftState base s) (.ret base r) := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨K, _, inactive, rest, lift⟩ := lift_first_inactive hn rfl
  refine ⟨K, ?_⟩
  rw [lift base]
  generalize Moist.Verified.Equivalence.steps K s = state at inactive rest
  generalize n - K = fuel at rest
  match state, fuel with
  | .error, _ => rw [Moist.Verified.Equivalence.steps_error] at rest; cases rest
  | .halt _, _ => rw [Moist.Verified.Equivalence.steps_halt] at rest; cases rest; rfl
  | .ret [] _, 0 => cases rest
  | .ret [] _, fuel + 1 =>
    rw [Nat.add_comm, Moist.Verified.Equivalence.steps_trans] at rest
    change Moist.Verified.Equivalence.steps fuel (.halt _) = _ at rest
    rw [Moist.Verified.Equivalence.steps_halt] at rest; cases rest; rfl
  | .ret (_ :: _) _, _ | .compute _ _ _, _ => cases inactive

/-- An error reached from a state is reached under any base stack. -/
theorem reaches_lift_error {s : State} (h : Reaches s .error) (base : Stack) :
    Reaches (Moist.Verified.StepLift.liftState base s) .error := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨K, _, inactive, rest, lift⟩ := lift_first_inactive hn rfl
  refine ⟨K, ?_⟩
  rw [lift base]
  generalize Moist.Verified.Equivalence.steps K s = state at inactive rest
  generalize n - K = fuel at rest
  match state, fuel with
  | .error, _ => rfl
  | .halt _, _ => rw [Moist.Verified.Equivalence.steps_halt] at rest; cases rest
  | .ret [] _, 0 => cases rest
  | .ret [] _, fuel + 1 =>
    rw [Nat.add_comm, Moist.Verified.Equivalence.steps_trans] at rest
    change Moist.Verified.Equivalence.steps fuel (.halt _) = _ at rest
    rw [Moist.Verified.Equivalence.steps_halt] at rest; cases rest
  | .ret (_ :: _) _, _ | .compute _ _ _, _ => cases inactive

theorem ret_lift_halt {π : Stack} {v r : CekValue} (h : Reaches (.ret π v) (.halt r)) (base : Stack) :
    Reaches (.ret (π ++ base) v) (.ret base r) :=
  reaches_lift_halt h base

theorem ret_lift_error {π : Stack} {v : CekValue} (h : Reaches (.ret π v) .error) (base : Stack) :
    Reaches (.ret (π ++ base) v) .error :=
  reaches_lift_error h base

/-! ## Applying to a spine of arguments -/

/-- Arguments evaluated left to right, each applied as soon as it returns. -/
theorem ends_args {m : VMode} {ρ : CekEnv} :
    ∀ (targs : List Term) (Ps : List (CekValue → Prop)) (f : CekValue),
      targs.length = Ps.length →
      (∀ (i : Nat) (ta : Term) (P : CekValue → Prop), targs[i]? = some ta → Ps[i]? = some P →
        Errs ρ ta ∨ ∃ w, Halts ρ ta w ∧ ValueWellFormed w ∧ P w) →
      CallsOK m Ps f →
      Ends m (.ret (targs.map fun ta => Frame.arg ta ρ) f)
  | [], [], f, _, _, hf => ends_ret_nil hf
  | ta :: targs, P :: Ps, f, hlen, hargs, hf => by
    have hlen' : targs.length = Ps.length := by simpa using hlen
    refine Ends.of_reaches (reaches_of_steps 1 rfl) ?_
    rcases hargs 0 ta P rfl rfl with he | ⟨w, hw, hwf, hP⟩
    · exact .inl (errs_on_stack he _)
    refine Ends.of_reaches (halts_on_stack hw _) ?_
    rcases hf w hwf hP with he | ⟨r, hr, hr'⟩
    · exact .inl (by simpa using ret_lift_error he (targs.map fun ta => Frame.arg ta ρ))
    · refine Ends.of_reaches (by simpa using ret_lift_halt hr (targs.map fun ta => Frame.arg ta ρ)) ?_
      exact ends_args targs Ps r hlen' (fun i ta P h1 h2 => hargs (i + 1) ta P h1 h2) hr'
  | [], _ :: _, _, h, _, _ | _ :: _, [], _, h, _, _ => by simp at h

end Moist.Verified.Guards
