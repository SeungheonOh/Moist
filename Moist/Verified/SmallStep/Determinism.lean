import Moist.Verified.SmallStep.StepLemmas

/-! # Determinism of `Step`

The contextual reduction relation is deterministic: every term has at most one
reduct.  This is the formal content of the spec's "always use the first
applicable rule" convention — the value-guarded congruence rules pick out a
*unique* decomposition point.

The non-trivial ingredient is `firstNonValue_unique`: in a constructor field
list the left-to-right strategy reduces the *first* non-value field, and that
position is unique.  `step_constr_inv` inverts a `Constr` reduction without
tripping dependent elimination on the `++`-shaped index.  Everything else
follows by inverting the second derivation against the shape fixed by the first,
using `step_not_value` to rule out reducing an already-evaluated subterm.
-/

namespace Moist.Verified.SmallStep

open Moist.Plutus.Term (Term)

/-! ## Helpers -/

/-- `.Error` does not reduce. -/
theorem not_step_error {t : Term} : ¬ Step .Error t := fun h => by cases h

/-- A constructor field list has a unique "first non-value" split: if two value
    prefixes are followed by non-values and the concatenations agree, the splits
    coincide.  This is what makes the `Constr` congruence deterministic. -/
theorem firstNonValue_unique :
    ∀ {l1 : List Term} {a1 : Term} {r1 : List Term}
      {l2 : List Term} {a2 : Term} {r2 : List Term},
      ValueList l1 → ¬ Value a1 → ValueList l2 → ¬ Value a2 →
      l1 ++ a1 :: r1 = l2 ++ a2 :: r2 →
      l1 = l2 ∧ a1 = a2 ∧ r1 = r2
  | [], _, _, [], _, _, _, _, _, _, h => by
    simp only [List.nil_append, List.cons.injEq] at h
    exact ⟨rfl, h.1, h.2⟩
  | [], a1, _, x :: l2, _, _, _, hna1, hvl2, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    cases hvl2 with
    | cons hvx _ => exact absurd (h.1 ▸ hvx) hna1
  | x :: l1, _, _, [], a2, _, hvl1, _, _, hna2, h => by
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    cases hvl1 with
    | cons hvx _ => exact absurd (h.1 ▸ hvx) hna2
  | x :: l1, a1, r1, y :: l2, a2, r2, hvl1, hna1, hvl2, hna2, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    cases hvl1 with
    | cons _ hvl1' =>
      cases hvl2 with
      | cons _ hvl2' =>
        obtain ⟨hl, ha, hr⟩ := firstNonValue_unique hvl1' hna1 hvl2' hna2 h.2
        exact ⟨by rw [h.1, hl], ha, hr⟩

/-- Inversion for a reduction of a constructor (general field list, to sidestep
    dependent elimination on the `++`-shaped index). -/
theorem step_constr_inv {i : Nat} {fields : List Term} {c : Term}
    (h : Step (.Constr i fields) c) :
    (∃ lefts rights, ValueList lefts ∧ fields = lefts ++ .Error :: rights ∧ c = .Error)
    ∨ (∃ lefts m m' rights, ValueList lefts ∧ Step m m' ∧
        fields = lefts ++ m :: rights ∧ c = .Constr i (lefts ++ m' :: rights)) := by
  cases h with
  | errConstr hvl => exact Or.inl ⟨_, _, hvl, rfl, rfl⟩
  | congConstr hvl hstep => exact Or.inr ⟨_, _, _, _, hvl, hstep, rfl, rfl⟩

/-! ## Determinism -/

/-- `Step` is deterministic: a term reduces to at most one reduct. -/
theorem step_det {a b c : Term} (h1 : Step a b) (h2 : Step a c) : b = c := by
  induction h1 generalizing c with
  | @betaLam x M v hv =>
    cases h2 with
    | betaLam _ => rfl
    | satApply hsp _ => cases hsp
    | errAppR _ => exact absurd hv not_value_error
    | congAppL hstep => exact absurd Value.lam (step_not_value hstep)
    | congAppR _ hstep => exact absurd hv (step_not_value hstep)
  | forceDelay =>
    cases h2 with
    | forceDelay => rfl
    | satForce hsp => cases hsp
    | congForce hstep => exact absurd Value.delay (step_not_value hstep)
  | @caseConstr i vs alts alt hvl halt =>
    cases h2 with
    | caseConstr _ halt2 => rw [halt] at halt2; injection halt2 with h; rw [h]
    | congCase hstep => exact absurd (Value.constr hvl) (step_not_value hstep)
  | @caseConst c bt tag numCtors fields alts alt hc hchk halt =>
    cases h2 with
    | caseConst hc2 _ halt2 =>
      rw [hc] at hc2
      simp only [Option.some.injEq, Prod.mk.injEq] at hc2
      obtain ⟨rfl, _, rfl⟩ := hc2
      rw [halt] at halt2; injection halt2 with h2; rw [h2]
    | congCase hstep => exact absurd Value.constant (step_not_value hstep)
  | @satApply t b args v hsp hv =>
    cases h2 with
    | betaLam _ => cases hsp
    | satApply hsp2 _ =>
      obtain ⟨hb, ha, _⟩ := bspine_det hsp hsp2; subst hb; subst ha; rfl
    | errAppL => cases hsp
    | errAppR _ => exact absurd hv not_value_error
    | congAppL hstep => exact absurd (Value.builtin hsp) (step_not_value hstep)
    | congAppR _ hstep => exact absurd hv (step_not_value hstep)
  | @satForce t b args hsp =>
    cases h2 with
    | forceDelay => cases hsp
    | satForce hsp2 =>
      obtain ⟨hb, ha, _⟩ := bspine_det hsp hsp2; subst hb; subst ha; rfl
    | errForce => cases hsp
    | congForce hstep => exact absurd (Value.builtin hsp) (step_not_value hstep)
  | errAppL =>
    cases h2 with
    | satApply hsp _ => cases hsp
    | errAppL => rfl
    | errAppR hbv => exact absurd hbv not_value_error
    | congAppL hstep => exact absurd hstep not_step_error
    | congAppR hbv _ => exact absurd hbv not_value_error
  | @errAppR v hv =>
    cases h2 with
    | betaLam hbv => exact absurd hbv not_value_error
    | satApply _ hbw => exact absurd hbw not_value_error
    | errAppL => exact absurd hv not_value_error
    | errAppR => rfl
    | congAppL hstep => exact absurd hv (step_not_value hstep)
    | congAppR _ hstep => exact absurd hstep not_step_error
  | errForce =>
    cases h2 with
    | satForce hsp => cases hsp
    | errForce => rfl
    | congForce hstep => exact absurd hstep not_step_error
  | errCase =>
    cases h2 with
    | errCase => rfl
    | congCase hstep => exact absurd hstep not_step_error
  | @errConstr i lefts rights hvl =>
    rcases step_constr_inv h2 with ⟨l2, r2, _, _, hc⟩ | ⟨l2, m2, m2', r2, hvl2, hstep2, heq, _⟩
    · rw [hc]
    · obtain ⟨_, hm, _⟩ := firstNonValue_unique hvl not_value_error hvl2
        (step_not_value hstep2) heq
      subst hm; exact absurd hstep2 not_step_error
  | @congAppL f f' N hstep ih =>
    cases h2 with
    | betaLam _ => exact absurd Value.lam (step_not_value hstep)
    | satApply hsp _ => exact absurd (Value.builtin hsp) (step_not_value hstep)
    | errAppL => exact absurd hstep not_step_error
    | errAppR hbv => exact absurd hbv (step_not_value hstep)
    | congAppL hstep2 => rw [ih hstep2]
    | congAppR hbv _ => exact absurd hbv (step_not_value hstep)
  | @congAppR v N N' hv hstep ih =>
    cases h2 with
    | betaLam hbv => exact absurd hbv (step_not_value hstep)
    | satApply _ hbw => exact absurd hbw (step_not_value hstep)
    | errAppL => exact absurd hv not_value_error
    | errAppR => exact absurd hstep not_step_error
    | congAppL hstep2 => exact absurd hv (step_not_value hstep2)
    | congAppR _ hstep2 => rw [ih hstep2]
  | @congForce t t' hstep ih =>
    cases h2 with
    | forceDelay => exact absurd Value.delay (step_not_value hstep)
    | satForce hsp => exact absurd (Value.builtin hsp) (step_not_value hstep)
    | errForce => exact absurd hstep not_step_error
    | congForce hstep2 => rw [ih hstep2]
  | @congCase s s' alts hstep ih =>
    cases h2 with
    | caseConstr hvl _ => exact absurd (Value.constr hvl) (step_not_value hstep)
    | caseConst _ _ _ => exact absurd Value.constant (step_not_value hstep)
    | errCase => exact absurd hstep not_step_error
    | congCase hstep2 => rw [ih hstep2]
  | @congConstr i lefts m m' rights hvl hstep ih =>
    rcases step_constr_inv h2 with ⟨l2, r2, hvl2, heq, _⟩ | ⟨l2, m2, m2', r2, hvl2, hstep2, heq, hc⟩
    · obtain ⟨_, hm, _⟩ := firstNonValue_unique hvl (step_not_value hstep) hvl2
        not_value_error heq
      subst hm; exact absurd hstep not_step_error
    · obtain ⟨hl, hm, hr⟩ := firstNonValue_unique hvl (step_not_value hstep) hvl2
        (step_not_value hstep2) heq
      subst hl; subst hm; subst hr; subst hc; rw [ih hstep2]

/-! ## Length-indexed reduction and path alignment

The backward adequacy argument needs to bound the CEK by the (finite) length of
the unique small-step path to a normal form.  `StepsN` is the length-indexed
closure; `stepsN_align` is the determinism consequence: any reduction prefix of
length `j` of a path of length `k` (to a normal form) has `j ≤ k`, and the
remaining `k - j` steps continue from where the prefix ended. -/

/-- `n`-step reduction. -/
inductive StepsN : Nat → Term → Term → Prop
  | refl {t} : StepsN 0 t t
  | step {n t u w} : Step t u → StepsN n u w → StepsN (n + 1) t w

theorem stepsN_steps {n : Nat} {a b : Term} (h : StepsN n a b) : Steps a b := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact .step hs ih

theorem steps_stepsN {a b : Term} (h : Steps a b) : ∃ n, StepsN n a b := by
  induction h with
  | refl => exact ⟨0, .refl⟩
  | step hs _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .step hs hn⟩

/-- A length-`j` reduction prefix of a length-`k` reduction to a normal form
    fits inside it: `j ≤ k`, and the leftover `k - j` steps continue from the
    prefix endpoint. -/
theorem stepsN_align {a b w : Term} (hw : Normal w) :
    ∀ {j k : Nat}, StepsN j a b → StepsN k a w → j ≤ k ∧ StepsN (k - j) b w := by
  intro j
  induction j generalizing a with
  | zero =>
    intro k hj hk; cases hj; exact ⟨Nat.zero_le _, hk⟩
  | succ j ih =>
    intro k hj hk
    cases hj with
    | step hs hrest =>
      cases hk with
      | refl => exact absurd ⟨_, hs⟩ hw
      | step hs2 hrest2 =>
        have := step_det hs hs2; subst this
        obtain ⟨hle, htail⟩ := ih hrest hrest2
        exact ⟨by omega, by simpa [Nat.succ_sub_succ] using htail⟩

end Moist.Verified.SmallStep
