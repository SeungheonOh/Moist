import Moist.Verified.RecordsSoundness.Shapes

variable [sv : Moist.CEK.SemVariant]

/-! # Machine steps of constructors, cases and lambda telescopes

A constructor returns the values of its fields (`halts_constr`). A `case`
selects an alternative by the tag of the scrutinee and applies it to the
fields (`case_dispatch`). An alternative of `n` lambdas applied to `n`
fields evaluates its body with the fields bound (`steps_telescope`).
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.BetaValueRefines

theorem lambdas_eq_lams : ∀ (binders : List VarId) (body : Expr), lambdas binders body = lams binders body
  | [], _ => rfl
  | x :: xs, body => by simp only [lambdas, lams, lambdas_eq_lams xs body]

theorem lower_lambdas {binders : List VarId} {body : Expr} {env : List VarId} {t : Term}
    (h : lowerTotalExpr env (lambdas binders body) = some t) :
    ∃ tb, lowerTotalExpr (binders.reverse ++ env) body = some tb ∧ t = lamsT binders.length tb := by
  rw [lambdas_eq_lams] at h
  exact lower_lams binders body env t h

theorem lowerTotalExpr_lambdas : ∀ (binders : List VarId) (body : Expr) (env : List VarId),
    lowerTotalExpr env (lambdas binders body) =
      (lowerTotalExpr (binders.reverse ++ env) body).map (lamsT binders.length)
  | [], body, env => by
    simp only [lambdas, List.reverse_nil, List.nil_append, List.length_nil]
    cases lowerTotalExpr env body <;> rfl
  | x :: xs, body, env => by
    simp only [lambdas, MIR.lowerTotalExpr_lam, lowerTotalExpr_lambdas xs body (x :: env),
      List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons]
    cases lowerTotalExpr (xs.reverse ++ x :: env) body <;> rfl

theorem fresh_lambdas {binders : List VarId} {body : Expr} {env : List VarId}
    (h : freshIn env (lambdas binders body) = true) (hd : EnvDistinct env) :
    freshIn (binders.reverse ++ env) body = true ∧ EnvDistinct (binders.reverse ++ env) := by
  rw [lambdas_eq_lams] at h
  exact fresh_lams binders body env h hd

theorem freshIn_lambdas : ∀ (binders : List VarId) (body : Expr) (env : List VarId),
    freshIn env (lambdas binders body) = true ↔
      (∀ j x, binders[j]? = some x → (envLookupT ((binders.take j).reverse ++ env) x).isNone = true) ∧
        freshIn (binders.reverse ++ env) body = true
  | [], body, env => by simp [lambdas]
  | x :: xs, body, env => by
    simp only [lambdas, freshIn, Bool.and_eq_true, freshIn_lambdas xs body (x :: env),
      List.reverse_cons, List.append_assoc, List.singleton_append]
    constructor
    · rintro ⟨hx, hall, hb⟩
      refine ⟨?_, hb⟩
      intro j y hy
      cases j with
      | zero => simp at hy; subst hy; simpa using hx
      | succ j =>
        have := hall j y (by simpa using hy)
        simpa [List.take_succ_cons] using this
    · rintro ⟨hall, hb⟩
      refine ⟨by simpa using hall 0 x rfl, ?_, hb⟩
      intro j y hy
      have := hall (j + 1) y (by simpa using hy)
      simpa [List.take_succ_cons] using this

/-! ## Lambda telescopes -/

theorem steps_telescope : ∀ (fields : List CekValue) (π : Stack) (ρ : CekEnv) (t : Term),
    steps (2 * fields.length) (.compute (fields.map Frame.applyArg ++ π) ρ (lamsT fields.length t)) =
      .compute π (extendAll ρ fields) t
  | [], _, _, _ => rfl
  | f :: fs, π, ρ, t => by
    rw [show 2 * (f :: fs).length = 2 + 2 * fs.length by simp; omega, steps_trans]
    have : steps 2 (.compute ((f :: fs).map Frame.applyArg ++ π) ρ (lamsT (f :: fs).length t)) =
        .compute (fs.map Frame.applyArg ++ π) (ρ.extend f) (lamsT fs.length t) := rfl
    rw [this, steps_telescope fs π (ρ.extend f) t]
    rfl

theorem reaches_telescope (fields : List CekValue) (π : Stack) (ρ : CekEnv) (t : Term) :
    Reaches (.compute (fields.map Frame.applyArg ++ π) ρ (lamsT fields.length t))
      (.compute π (extendAll ρ fields) t) :=
  ⟨_, steps_telescope fields π ρ t⟩

theorem extendAll_length : ∀ (ρ : CekEnv) (vals : List CekValue),
    (extendAll ρ vals).length = ρ.length + vals.length
  | ρ, [] => by simp [extendAll]
  | ρ, v :: vs => by
    simp only [extendAll, extendAll_length (ρ.extend v) vs, List.length_cons]
    simp [CekEnv.extend, CekEnv.length]; omega

theorem envWellFormed_extendAll : ∀ (d : Nat) {ρ : CekEnv} (vals : List CekValue),
    EnvWellFormed d ρ → d ≤ ρ.length → ValueListWellFormed vals →
      EnvWellFormed (d + vals.length) (extendAll ρ vals)
  | d, ρ, [], h, _, _ => by simpa [extendAll] using h
  | d, ρ, v :: vs, h, hlen, .cons hv hvs => by
    simp only [extendAll, List.length_cons]
    rw [show d + (vs.length + 1) = d + 1 + vs.length by omega]
    exact envWellFormed_extendAll (d + 1) vs (envWellFormed_extend d h hlen hv)
      (by simp [CekEnv.extend, CekEnv.length]; omega) hvs

/-- The binder `x` of a telescope over as many fields as binders holds its field. -/
theorem lookup_field {binders : List VarId} {x : VarId} {field index : Nat} {ρ : CekEnv}
    {fields : List CekValue} (hlen : fields.length = binders.length)
    (hindex : envLookupT binders.reverse x = some index)
    (hfield : field = binders.length - 1 - index) :
    (extendAll ρ fields).lookup (index + 1) = fields[field]? := by
  have hbound := envLookupT_bound binders.reverse x index hindex
  simp only [List.length_reverse] at hbound
  rw [lookup_extendAll_lt ρ fields index (by omega), List.getElem?_reverse (by omega), hfield, hlen]

/-! ## Constructors -/

theorem constrField_reaches : ∀ (ms : List Term) {tag : Nat} {done : List CekValue} {ρ : CekEnv}
    {w v : CekValue},
    Reaches (.ret [.constrField tag done ms ρ] w) (.halt v) →
      ∃ ws, v = .VConstr tag ((w :: done).reverse ++ ws) ∧ ws.length = ms.length ∧
        ∀ (i : Nat) (m : Term) (u : CekValue), ms[i]? = some m → ws[i]? = some u → Halts ρ m u
  | [], tag, done, ρ, w, v, h => by
    have h1 := reaches_halt_of_step (by simp) h
    simp only [step] at h1
    have h2 := reaches_halt_of_step (by simp) h1
    simp only [step] at h2
    obtain ⟨m, hm⟩ := h2
    rw [steps_halt] at hm; cases hm
    exact ⟨[], by simp, rfl, fun i m u hm _ => by simp at hm⟩
  | m :: ms, tag, done, ρ, w, v, h => by
    have h1 := reaches_halt_of_step (by simp) h
    simp only [step] at h1
    rcases sequence (.inr ⟨v, rfl⟩) h1 with ⟨_, impossible⟩ | ⟨u, hu, rest⟩
    · cases impossible
    · obtain ⟨ws, rfl, hlen, hws⟩ := constrField_reaches ms rest
      refine ⟨u :: ws, by simp, by simp [hlen], ?_⟩
      intro i m' u' hm hu'
      cases i with
      | zero => simp at hm hu'; subst hm hu'; exact hu
      | succ i => exact hws i m' u' (by simpa using hm) (by simpa using hu')

theorem halts_constr {ρ : CekEnv} {tag : Nat} {ms : List Term} {v : CekValue}
    (h : Halts ρ (.Constr tag ms) v) :
    ∃ vs, v = .VConstr tag vs ∧ vs.length = ms.length ∧
      ∀ (i : Nat) (m : Term) (u : CekValue), ms[i]? = some m → vs[i]? = some u → Halts ρ m u := by
  cases ms with
  | nil =>
    have h1 := reaches_halt_of_step (by simp) h
    simp only [step] at h1
    have h2 := reaches_halt_of_step (by simp) h1
    simp only [step] at h2
    obtain ⟨m, hm⟩ := h2
    rw [steps_halt] at hm; cases hm
    exact ⟨[], rfl, rfl, fun i m u hm _ => by simp at hm⟩
  | cons m ms =>
    have h1 := reaches_halt_of_step (by simp) h
    simp only [step] at h1
    rcases sequence (.inr ⟨v, rfl⟩) h1 with ⟨_, impossible⟩ | ⟨u, hu, rest⟩
    · cases impossible
    · obtain ⟨ws, rfl, hlen, hws⟩ := constrField_reaches ms rest
      refine ⟨u :: ws, by simp, by simp [hlen], ?_⟩
      intro i m' u' hm hu'
      cases i with
      | zero => simp at hm hu'; subst hm hu'; exact hu
      | succ i => exact hws i m' u' (by simpa using hm) (by simpa using hu')

/-! ## Case analysis -/

/-- The fields a scrutinee value supplies to the selected alternative. -/
def CaseFields (w : CekValue) (tag : Nat) (fields : List CekValue) : Prop :=
  w = .VConstr tag fields ∨ ∃ c numCtors, w = .VCon c ∧ constToTagAndFields c = some (tag, numCtors, fields)

theorem case_dispatch {talts : List Term} {ρ : CekEnv} {π : Stack} {w : CekValue} {T : State}
    (term : Terminal T) (h : Reaches (.ret (.caseScrutinee talts ρ :: π) w) T) (hT : T ≠ .error) :
    ∃ tag fields talt, talts[tag]? = some talt ∧ CaseFields w tag fields ∧
      Reaches (.compute (fields.map Frame.applyArg ++ π) ρ talt) T := by
  have herr : ¬ Reaches .error T := by
    intro he
    obtain ⟨n, hn⟩ := he
    rw [steps_error] at hn
    exact hT hn.symm
  have h1 := reaches_terminal_after term ⟨1, rfl⟩ h
  cases w with
  | VConstr tag fields =>
    simp only [steps, step] at h1
    cases hget : talts[tag]? with
    | none => rw [hget] at h1; exact absurd h1 herr
    | some talt =>
      rw [hget] at h1
      exact ⟨tag, fields, talt, hget, .inl rfl, h1⟩
  | VCon c =>
    simp only [steps, step] at h1
    cases hc : constToTagAndFields c with
    | none => rw [hc] at h1; exact absurd h1 herr
    | some triple =>
      obtain ⟨tag, numCtors, fields⟩ := triple
      rw [hc] at h1
      simp only at h1
      split at h1
      · exact absurd h1 herr
      · cases hget : talts[tag]? with
        | none => rw [hget] at h1; exact absurd h1 herr
        | some talt =>
          rw [hget] at h1
          exact ⟨tag, fields, talt, hget, .inr ⟨c, numCtors, rfl, hc⟩, h1⟩
  | VLam _ _ | VDelay _ _ | VBuiltin _ _ _ =>
    simp only [steps, step] at h1; exact absurd h1 herr

/-- A constructor value applied to further arguments fails. -/
theorem ret_applyArg_constr {f : CekValue} {π : Stack} {tag : Nat} {vs : List CekValue} {T : State}
    (term : Terminal T) (h : Reaches (.ret (.applyArg f :: π) (.VConstr tag vs)) T) : T = .error := by
  have h1 := reaches_terminal_after term ⟨1, rfl⟩ h
  simp only [steps, step] at h1
  obtain ⟨n, hn⟩ := h1
  rw [steps_error] at hn
  exact hn.symm

end Moist.Verified.ShapeFacts
