import Moist.Verified.SmallStep.StepLemmas

/-! # Discharge lemmas (stage 1): list/env helpers + builtin-spine combinatorics

Foundational equational lemmas about `discharge`/`dischargeList`/`dischargeEnv`
and the builtin-spine reconstruction (`consumedSteps`/`dischargeSpine`), used to
prove `value_discharge` and the forward simulation.
-/

namespace Moist.Verified.SmallStep

open Moist.Plutus.Term (Term)
open Moist.CEK (ArgKind ExpectedArgs expectedArgs CekValue CekEnv)
open Moist.Verified (substTerm)

/-! ## List/env helpers -/

theorem dischargeList_eq_map (vs : List CekValue) :
    dischargeList vs = vs.map discharge := by
  induction vs with
  | nil => simp [dischargeList]
  | cons v vs ih => simp only [dischargeList, List.map, ih]

theorem reflectList_eq_map (ts : List Term) :
    reflectList ts = ts.map reflect := by
  induction ts with
  | nil => simp [reflectList]
  | cons t ts ih => simp only [reflectList, List.map, ih]

/-- Discharging `Error` under any environment yields `Error`. -/
theorem dischargeEnv_error : ∀ (ρ : CekEnv) (d : Nat),
    dischargeEnv ρ d .Error = .Error
  | .nil, d => by simp [dischargeEnv]
  | .cons v rest, d => by
    simp only [dischargeEnv]
    rw [show substTerm (d + 1) (discharge v) Term.Error = Term.Error by simp [substTerm]]
    exact dischargeEnv_error rest d

/-! ## `ExpectedArgs` suffixes -/

/-- `IsSuffix ea full`: `ea` is a structural suffix of `full`. -/
inductive IsSuffix : ExpectedArgs → ExpectedArgs → Prop
  | refl {e} : IsSuffix e e
  | more {ea k rest} : IsSuffix ea rest → IsSuffix ea (.more k rest)

/-- Structural depth of an `ExpectedArgs` (number of `.more` layers). -/
def eaDepth : ExpectedArgs → Nat
  | .one _ => 0
  | .more _ e => eaDepth e + 1

theorem more_ne_self (k : ArgKind) (e : ExpectedArgs) : ExpectedArgs.more k e ≠ e := by
  intro h
  have : eaDepth (ExpectedArgs.more k e) = eaDepth e := by rw [h]
  simp [eaDepth] at this

theorem isSuffix_depth_le {ea full : ExpectedArgs} (h : IsSuffix ea full) :
    eaDepth ea ≤ eaDepth full := by
  induction h with
  | refl => exact Nat.le_refl _
  | more _ ih => simp only [eaDepth]; omega

theorem ne_of_suffix_more {ea full : ExpectedArgs} {k : ArgKind}
    (h : IsSuffix (.more k ea) full) : full ≠ ea := by
  intro heq; subst heq
  have := isSuffix_depth_le h
  simp only [eaDepth] at this; omega

/-! ## `consumedSteps` unfolding -/

theorem consumedSteps_self (e : ExpectedArgs) : consumedSteps e e = [] := by
  unfold consumedSteps; simp

theorem consumedSteps_more_step {k : ArgKind} {full' rem : ExpectedArgs}
    (h : ExpectedArgs.more k full' ≠ rem) :
    consumedSteps (.more k full') rem = k :: consumedSteps full' rem := by
  rw [consumedSteps.eq_def]; simp [h]

/-- Consuming down to `rest` past a `.more k rest` adds one `k` at the end. -/
theorem consumedSteps_more {rest : ExpectedArgs} {k : ArgKind} :
    ∀ {full : ExpectedArgs}, IsSuffix (.more k rest) full →
    consumedSteps full rest = consumedSteps full (.more k rest) ++ [k] := by
  intro full
  induction full with
  | one k' => intro h; cases h
  | more k' full' ih =>
    intro h
    by_cases hfull : (ExpectedArgs.more k' full') = (ExpectedArgs.more k rest)
    · -- full = .more k rest itself
      rw [hfull, consumedSteps_more_step (more_ne_self k rest), consumedSteps_self,
          consumedSteps_self]
      simp
    · -- deeper suffix
      have hsuf' : IsSuffix (.more k rest) full' := by
        cases h with
        | refl => exact absurd rfl hfull
        | more h' => exact h'
      have hne_rest : (ExpectedArgs.more k' full') ≠ rest := by
        intro he
        have hle := isSuffix_depth_le hsuf'
        have : eaDepth (ExpectedArgs.more k' full') = eaDepth rest := by rw [he]
        simp only [eaDepth] at this hle; omega
      rw [consumedSteps_more_step hne_rest, consumedSteps_more_step hfull,
          ih hsuf', List.cons_append]

/-! ## `dischargeSpine` snoc -/

/-- Number of value-argument slots in a consumed-steps list. -/
def numV : List ArgKind → Nat
  | [] => 0
  | .argV :: rest => numV rest + 1
  | .argQ :: rest => numV rest

theorem dischargeSpine_snoc_argV : ∀ {cs : List ArgKind} {dargs : List Term},
    numV cs = dargs.length → ∀ (acc d : Term),
    dischargeSpine acc (cs ++ [.argV]) (dargs ++ [d]) = .Apply (dischargeSpine acc cs dargs) d
  | [], dargs, hlen, acc, d => by
    cases dargs with
    | nil => rfl
    | cons _ _ => simp [numV] at hlen
  | .argQ :: cs, dargs, hlen, acc, d => by
    simp only [numV] at hlen
    show dischargeSpine (.Force acc) (cs ++ [.argV]) (dargs ++ [d])
      = .Apply (dischargeSpine (.Force acc) cs dargs) d
    exact dischargeSpine_snoc_argV hlen (.Force acc) d
  | .argV :: cs, dargs, hlen, acc, d => by
    cases dargs with
    | nil => simp [numV] at hlen
    | cons e dargs =>
      simp only [numV, List.length_cons] at hlen
      show dischargeSpine (.Apply acc e) (cs ++ [.argV]) (dargs ++ [d])
        = .Apply (dischargeSpine (.Apply acc e) cs dargs) d
      exact dischargeSpine_snoc_argV (by omega) (.Apply acc e) d

theorem dischargeSpine_snoc_argQ : ∀ {cs : List ArgKind} {dargs : List Term},
    numV cs = dargs.length → ∀ (acc : Term),
    dischargeSpine acc (cs ++ [.argQ]) dargs = .Force (dischargeSpine acc cs dargs)
  | [], dargs, hlen, acc => by
    cases dargs with
    | nil => rfl
    | cons _ _ => simp [numV] at hlen
  | .argQ :: cs, dargs, hlen, acc => by
    simp only [numV] at hlen
    show dischargeSpine (.Force acc) (cs ++ [.argQ]) dargs
      = .Force (dischargeSpine (.Force acc) cs dargs)
    exact dischargeSpine_snoc_argQ hlen (.Force acc)
  | .argV :: cs, dargs, hlen, acc => by
    cases dargs with
    | nil => simp [numV] at hlen
    | cons e dargs =>
      simp only [numV, List.length_cons] at hlen
      show dischargeSpine (.Apply acc e) (cs ++ [.argQ]) dargs
        = .Force (dischargeSpine (.Apply acc e) cs dargs)
      exact dischargeSpine_snoc_argQ (by omega) (.Apply acc e)

end Moist.Verified.SmallStep
