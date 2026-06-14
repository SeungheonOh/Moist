import Moist.Verified.SmallStep.Subst

/-! # Closedness of CEK values and their discharge

`ClosedValue`/`ClosedEnv` capture the structural closedness invariant the CEK
maintains: every closure body is closed under its captured environment plus its
own binder, and every captured value is itself closed.  The payoff is
`discharge_closed`: a closed CEK value discharges to a closed UPLC term — exactly
the hypothesis the β-step commutation (`beta_discharge`) needs.
-/

namespace Moist.Verified.SmallStep

open Moist.Plutus.Term (Term)
open Moist.CEK (ArgKind CekValue CekEnv)
open Moist.Verified (closedAt closedAtList substTerm)

/-! ## `closedAt` monotonicity and list extraction -/

mutual
  theorem closedAt_mono : ∀ {d d' : Nat} {t : Term}, d ≤ d' → closedAt d t = true →
      closedAt d' t = true
    | _, _, .Var _, hd, h => by simp only [closedAt, decide_eq_true_eq] at h ⊢; omega
    | _, _, .Lam _ body, hd, h => by
      simp only [closedAt] at h ⊢; exact closedAt_mono (by omega) h
    | _, _, .Apply f x, hd, h => by
      simp only [closedAt, Bool.and_eq_true] at h ⊢
      exact ⟨closedAt_mono hd h.1, closedAt_mono hd h.2⟩
    | _, _, .Force e, hd, h => by simp only [closedAt] at h ⊢; exact closedAt_mono hd h
    | _, _, .Delay e, hd, h => by simp only [closedAt] at h ⊢; exact closedAt_mono hd h
    | _, _, .Constr _ args, hd, h => by
      simp only [closedAt] at h ⊢; exact closedAtList_mono hd h
    | _, _, .Case scrut alts, hd, h => by
      simp only [closedAt, Bool.and_eq_true] at h ⊢
      exact ⟨closedAt_mono hd h.1, closedAtList_mono hd h.2⟩
    | _, _, .Constant _, _, _ => by simp [closedAt]
    | _, _, .Builtin _, _, _ => by simp [closedAt]
    | _, _, .Error, _, _ => by simp [closedAt]
  termination_by _ _ t _ _ => sizeOf t

  theorem closedAtList_mono : ∀ {d d' : Nat} {ts : List Term}, d ≤ d' →
      closedAtList d ts = true → closedAtList d' ts = true
    | _, _, [], _, _ => by simp [closedAtList]
    | _, _, t :: ts, hd, h => by
      simp only [closedAtList, Bool.and_eq_true] at h ⊢
      exact ⟨closedAt_mono hd h.1, closedAtList_mono hd h.2⟩
  termination_by _ _ ts _ _ => sizeOf ts
end

theorem closedAtList_forall : ∀ {d : Nat} {ts : List Term}, closedAtList d ts = true →
    ∀ t ∈ ts, closedAt d t = true
  | _, [], _, _, hmem => by cases hmem
  | _, t :: ts, h, u, hmem => by
    simp only [closedAtList, Bool.and_eq_true] at h
    cases hmem with
    | head => exact h.1
    | tail _ h' => exact closedAtList_forall h.2 u h'

/-! ## The closedness predicate -/

mutual
  /-- A CEK value is closed when every closure body is closed under its captured
      environment (plus its own binder, for `VLam`) and every captured value is
      itself closed. -/
  inductive ClosedValue : CekValue → Prop
    | vcon {c} : ClosedValue (.VCon c)
    | vlam {body env} : closedAt (env.length + 1) body = true → ClosedEnv env →
        ClosedValue (.VLam body env)
    | vdelay {body env} : closedAt env.length body = true → ClosedEnv env →
        ClosedValue (.VDelay body env)
    | vconstr {tag fields} : ClosedValueList fields → ClosedValue (.VConstr tag fields)
    | vbuiltin {b args ea} : ClosedValueList args → ClosedValue (.VBuiltin b args ea)

  inductive ClosedValueList : List CekValue → Prop
    | nil : ClosedValueList []
    | cons {v vs} : ClosedValue v → ClosedValueList vs → ClosedValueList (v :: vs)

  inductive ClosedEnv : CekEnv → Prop
    | nil : ClosedEnv .nil
    | cons {v rest} : ClosedValue v → ClosedEnv rest → ClosedEnv (.cons v rest)
end

/-! ## Discharge of a builtin spine is closed -/

theorem dischargeSpine_closed : ∀ {steps : List ArgKind} {dargs : List Term} {acc : Term},
    closedAt 0 acc = true → (∀ t ∈ dargs, closedAt 0 t = true) →
    closedAt 0 (dischargeSpine acc steps dargs) = true
  | [], _, _, hacc, _ => by simpa [dischargeSpine] using hacc
  | .argQ :: rest, dargs, acc, hacc, hd => by
    show closedAt 0 (dischargeSpine (.Force acc) rest dargs) = true
    exact dischargeSpine_closed (by simpa [closedAt] using hacc) hd
  | .argV :: rest, [], acc, hacc, _ => by simpa [dischargeSpine] using hacc
  | .argV :: rest, a :: as, acc, hacc, hd => by
    show closedAt 0 (dischargeSpine (.Apply acc a) rest as) = true
    refine dischargeSpine_closed ?_ (fun t ht => hd t (List.mem_cons_of_mem a ht))
    simp only [closedAt, Bool.and_eq_true]
    exact ⟨hacc, hd a List.mem_cons_self⟩

/-! ## Closed values discharge to closed terms -/

mutual
  /-- A closed CEK value discharges to a closed UPLC term. -/
  theorem discharge_closed : ∀ {v : CekValue}, ClosedValue v → closedAt 0 (discharge v) = true
    | _, .vcon => by simp [discharge, closedAt]
    | _, .vlam hb he => by
      simp only [discharge, closedAt]; exact dischargeEnv_closed 1 he hb
    | _, .vdelay hb he => by
      simp only [discharge, closedAt]; exact dischargeEnv_closed 0 he hb
    | _, .vconstr hf => by
      simp only [discharge, closedAt]; exact dischargeList_closed hf
    | _, .vbuiltin ha => by
      simp only [discharge]
      refine dischargeSpine_closed (by simp [closedAt]) (fun t ht => ?_)
      exact closedAtList_forall (dischargeList_closed ha) t (List.mem_reverse.mp ht)

  /-- A closed list of CEK values discharges to a closed list of terms. -/
  theorem dischargeList_closed : ∀ {vs : List CekValue}, ClosedValueList vs →
      closedAtList 0 (dischargeList vs) = true
    | _, .nil => by simp [dischargeList, closedAtList]
    | _, .cons hv hvs => by
      simp only [dischargeList, closedAtList, Bool.and_eq_true]
      exact ⟨discharge_closed hv, dischargeList_closed hvs⟩

  /-- Discharging a closed environment into a body closed under `env.length + d`
      binders yields a term closed under `d` binders. -/
  theorem dischargeEnv_closed : ∀ (d : Nat) {env : CekEnv} {body : Term}, ClosedEnv env →
      closedAt (env.length + d) body = true → closedAt d (dischargeEnv env d body) = true
    | d, _, body, .nil, hb => by
      simpa [dischargeEnv, CekEnv.length] using hb
    | d, _, body, @ClosedEnv.cons v rest hv hrest, hb => by
      simp only [dischargeEnv]
      refine dischargeEnv_closed d hrest
        (closedAt_substTerm (by omega) (by omega)
          (closedAt_mono (Nat.zero_le _) (discharge_closed hv)) ?_)
      have hlen : (rest.length + d) + 1 = (CekEnv.cons v rest).length + d := by
        simp [CekEnv.length]; omega
      rw [hlen]; exact hb
end

/-! ## Bridge to `EnvDischargeClosed` -/

/-- A closed environment satisfies the per-value closedness used by `beta_discharge`. -/
theorem closedEnv_envDischargeClosed : ∀ {env : CekEnv}, ClosedEnv env → EnvDischargeClosed env
  | _, .nil => trivial
  | _, .cons hv hrest => ⟨discharge_closed hv, closedEnv_envDischargeClosed hrest⟩

end Moist.Verified.SmallStep
