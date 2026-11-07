import Moist.Verified.ShapeFacts.Facts

/-! # Decomposing successful evaluations

Inversion lemmas for `Halts` on each term former, and the corresponding
inversions for returning a value to an application or force frame.
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR
open Moist.Verified Moist.Verified.Equivalence

theorem reaches_halt_of_step {s : State} {v : CekValue} (hs : s ≠ .halt v)
    (h : Reaches s (.halt v)) : Reaches (step s) (.halt v) := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => exact absurd hn hs
  | succ n => exact ⟨n, hn⟩

theorem reaches_halt_step {s : State} {v : CekValue}
    (h : Reaches (step s) (.halt v)) : Reaches s (.halt v) :=
  reaches_trans ⟨1, rfl⟩ h

theorem halts_var {ρ : CekEnv} {n : Nat} {v : CekValue} (h : Halts ρ (.Var n) v) :
    ρ.lookup n = some v := by
  have h1 := reaches_halt_of_step (by simp) h
  simp only [step] at h1
  cases hl : ρ.lookup n with
  | none =>
    rw [hl] at h1
    exact absurd h1 (fun he => halt_not_error he ⟨0, rfl⟩)
  | some w =>
    rw [hl] at h1
    have h2 := reaches_halt_of_step (by simp) h1
    simp only [step] at h2
    obtain ⟨m, hm⟩ := h2
    rw [Terminal.steps_fixed (.inr ⟨w, rfl⟩)] at hm
    cases hm; rfl

theorem halts_var_of_lookup {ρ : CekEnv} {n : Nat} {v : CekValue} (h : ρ.lookup n = some v) :
    Halts ρ (.Var n) v := ⟨2, by simp [steps, step, h]⟩

private theorem value_step_halts {s : State} {w v : CekValue}
    (hs : step s = .ret [] w) (h : Reaches s (.halt v)) : v = w := by
  have h1 := reaches_halt_of_step (by intro e; rw [e] at hs; cases hs) h
  rw [hs] at h1
  have h2 := reaches_halt_of_step (by simp) h1
  obtain ⟨m, hm⟩ := h2
  simp only [step] at hm
  rw [Terminal.steps_fixed (.inr ⟨w, rfl⟩)] at hm
  cases hm; rfl

theorem halts_constant {ρ : CekEnv} {c : Const} {ty : BuiltinType} {v : CekValue}
    (h : Halts ρ (.Constant (c, ty)) v) : v = .VCon c :=
  value_step_halts rfl h

theorem halts_constant_of {ρ : CekEnv} (c : Const) (ty : BuiltinType) :
    Halts ρ (.Constant (c, ty)) (.VCon c) := ⟨2, rfl⟩

theorem halts_builtin {ρ : CekEnv} {b : BuiltinFun} {v : CekValue}
    (h : Halts ρ (.Builtin b) v) : v = .VBuiltin b [] (expectedArgs b) :=
  value_step_halts rfl h

theorem halts_lam {ρ : CekEnv} {n : Nat} {body : Term} {v : CekValue}
    (h : Halts ρ (.Lam n body) v) : v = .VLam body ρ :=
  value_step_halts rfl h

theorem halts_delay {ρ : CekEnv} {body : Term} {v : CekValue}
    (h : Halts ρ (.Delay body) v) : v = .VDelay body ρ :=
  value_step_halts rfl h

theorem not_halts_error {ρ : CekEnv} {v : CekValue} : ¬ Halts ρ .Error v := by
  intro h
  have h1 := reaches_halt_of_step (by simp) h
  exact halt_not_error h1 ⟨0, rfl⟩

theorem halts_apply {ρ : CekEnv} {f a : Term} {v : CekValue} (h : Halts ρ (.Apply f a) v) :
    ∃ wf wa, Halts ρ f wf ∧ Halts ρ a wa ∧ Reaches (.ret [.funV wf] wa) (.halt v) := by
  have h1 := reaches_halt_of_step (by simp) h
  change Reaches (.compute [.arg a ρ] ρ f) (.halt v) at h1
  rcases sequence (.inr ⟨v, rfl⟩) h1 with ⟨_, impossible⟩ | ⟨wf, hf, rest⟩
  · cases impossible
  · have h2 := reaches_halt_of_step (by simp) rest
    change Reaches (.compute [.funV wf] ρ a) (.halt v) at h2
    rcases sequence (.inr ⟨v, rfl⟩) h2 with ⟨_, impossible⟩ | ⟨wa, ha, rest'⟩
    · cases impossible
    · exact ⟨wf, wa, hf, ha, rest'⟩

theorem halts_force {ρ : CekEnv} {t : Term} {v : CekValue} (h : Halts ρ (.Force t) v) :
    ∃ w, Halts ρ t w ∧ Reaches (.ret [.force] w) (.halt v) := by
  have h1 := reaches_halt_of_step (by simp) h
  change Reaches (.compute [.force] ρ t) (.halt v) at h1
  rcases sequence (.inr ⟨v, rfl⟩) h1 with ⟨_, impossible⟩ | ⟨w, hw, rest⟩
  · cases impossible
  · exact ⟨w, hw, rest⟩

theorem halts_case {ρ : CekEnv} {s : Term} {alts : List Term} {v : CekValue}
    (h : Halts ρ (.Case s alts) v) :
    ∃ w, Halts ρ s w ∧ Reaches (.ret [.caseScrutinee alts ρ] w) (.halt v) := by
  have h1 := reaches_halt_of_step (by simp) h
  change Reaches (.compute [.caseScrutinee alts ρ] ρ s) (.halt v) at h1
  rcases sequence (.inr ⟨v, rfl⟩) h1 with ⟨_, impossible⟩ | ⟨w, hw, rest⟩
  · cases impossible
  · exact ⟨w, hw, rest⟩

/-- Returning a value to an application frame. -/
theorem apply_reaches {wf wa v : CekValue} (h : Reaches (.ret [.funV wf] wa) (.halt v)) :
    (∃ body ρ, wf = .VLam body ρ ∧ Halts (ρ.extend wa) body v) ∨
    (∃ b args ea, wf = .VBuiltin b args ea ∧ ea.head = .argV ∧
      ((∃ rest, ea.tail = some rest ∧ v = .VBuiltin b (wa :: args) rest) ∨
        (ea.tail = none ∧ evalBuiltin b (wa :: args) = some v))) := by
  have h1 := reaches_halt_of_step (by simp) h
  cases wf with
  | VLam body ρ => exact .inl ⟨body, ρ, rfl, h1⟩
  | VBuiltin b args ea =>
    refine .inr ⟨b, args, ea, rfl, ?_⟩
    simp only [step] at h1
    cases hhead : ea.head with
    | argQ => rw [hhead] at h1; exact absurd h1 (fun he => halt_not_error he ⟨0, rfl⟩)
    | argV =>
      rw [hhead] at h1
      refine ⟨rfl, ?_⟩
      cases htail : ea.tail with
      | some rest =>
        rw [htail] at h1
        refine .inl ⟨rest, rfl, ?_⟩
        have h2 := reaches_halt_of_step (by simp) h1
        obtain ⟨m, hm⟩ := h2
        simp only [step] at hm
        rw [Terminal.steps_fixed (.inr ⟨_, rfl⟩)] at hm
        cases hm; rfl
      | none =>
        rw [htail] at h1
        refine .inr ⟨rfl, ?_⟩
        cases he : evalBuiltin b (wa :: args) with
        | none => rw [he] at h1; exact absurd h1 (fun h => halt_not_error h ⟨0, rfl⟩)
        | some w =>
          rw [he] at h1
          have h2 := reaches_halt_of_step (by simp) h1
          obtain ⟨m, hm⟩ := h2
          simp only [step] at hm
          rw [Terminal.steps_fixed (.inr ⟨_, rfl⟩)] at hm
          cases hm; rfl
  | VCon _ | VDelay _ _ | VConstr _ _ =>
    simp only [step] at h1; exact absurd h1 (fun he => halt_not_error he ⟨0, rfl⟩)

/-- Returning a value to a force frame. -/
theorem force_reaches {w v : CekValue} (h : Reaches (.ret [.force] w) (.halt v)) :
    (∃ body ρ, w = .VDelay body ρ ∧ Halts ρ body v) ∨
    (∃ b args ea, w = .VBuiltin b args ea ∧ ea.head = .argQ ∧
      ((∃ rest, ea.tail = some rest ∧ v = .VBuiltin b args rest) ∨
        (ea.tail = none ∧ evalBuiltin b args = some v))) := by
  have h1 := reaches_halt_of_step (by simp) h
  cases w with
  | VDelay body ρ => exact .inl ⟨body, ρ, rfl, h1⟩
  | VBuiltin b args ea =>
    refine .inr ⟨b, args, ea, rfl, ?_⟩
    simp only [step] at h1
    cases hhead : ea.head with
    | argV => rw [hhead] at h1; exact absurd h1 (fun he => halt_not_error he ⟨0, rfl⟩)
    | argQ =>
      rw [hhead] at h1
      refine ⟨rfl, ?_⟩
      cases htail : ea.tail with
      | some rest =>
        rw [htail] at h1
        refine .inl ⟨rest, rfl, ?_⟩
        have h2 := reaches_halt_of_step (by simp) h1
        obtain ⟨m, hm⟩ := h2
        simp only [step] at hm
        rw [Terminal.steps_fixed (.inr ⟨_, rfl⟩)] at hm
        cases hm; rfl
      | none =>
        rw [htail] at h1
        refine .inr ⟨rfl, ?_⟩
        cases he : evalBuiltin b args with
        | none => rw [he] at h1; exact absurd h1 (fun h => halt_not_error h ⟨0, rfl⟩)
        | some w =>
          rw [he] at h1
          have h2 := reaches_halt_of_step (by simp) h1
          obtain ⟨m, hm⟩ := h2
          simp only [step] at hm
          rw [Terminal.steps_fixed (.inr ⟨_, rfl⟩)] at hm
          cases hm; rfl
  | VCon _ | VLam _ _ | VConstr _ _ =>
    simp only [step] at h1; exact absurd h1 (fun he => halt_not_error he ⟨0, rfl⟩)

/-! ## Lowering of single nodes -/

theorem lowerTotalExpr_var (env : List VarId) (x : VarId) :
    lowerTotalExpr env (.Var x) = (envLookupT env x).map fun i => .Var (i + 1) := by
  simp only [lowerTotalExpr, expandFix, lowerTotal]
  cases envLookupT env x <;> rfl

theorem lowerTotalExpr_lit (env : List VarId) (c : Const) (ty : BuiltinType) :
    lowerTotalExpr env (.Lit (c, ty)) = some (.Constant (c, ty)) := by
  simp only [lowerTotalExpr, expandFix, lowerTotal]

theorem lowerTotalExpr_builtin (env : List VarId) (b : BuiltinFun) :
    lowerTotalExpr env (.Builtin b) = some (.Builtin b) := by
  simp only [lowerTotalExpr, expandFix, lowerTotal]

theorem lowerTotalExpr_error (env : List VarId) :
    lowerTotalExpr env .Error = some .Error := by
  simp only [lowerTotalExpr, expandFix, lowerTotal]

theorem lowerTotalExpr_app_some {env : List VarId} {f a : Expr} {t : Term}
    (h : lowerTotalExpr env (.App f a) = some t) :
    ∃ tf ta, lowerTotalExpr env f = some tf ∧ lowerTotalExpr env a = some ta ∧ t = .Apply tf ta := by
  rw [MIR.lowerTotalExpr_app] at h
  cases hf : lowerTotalExpr env f with
  | none => rw [hf] at h; cases h
  | some tf =>
    cases ha : lowerTotalExpr env a with
    | none => rw [hf, ha] at h; cases h
    | some ta => rw [hf, ha] at h; cases h; exact ⟨tf, ta, rfl, rfl, rfl⟩

theorem lowerTotalExpr_force_some {env : List VarId} {e : Expr} {t : Term}
    (h : lowerTotalExpr env (.Force e) = some t) :
    ∃ te, lowerTotalExpr env e = some te ∧ t = .Force te := by
  rw [MIR.lowerTotalExpr_force] at h
  cases he : lowerTotalExpr env e with
  | none => rw [he] at h; cases h
  | some te => rw [he] at h; cases h; exact ⟨te, rfl, rfl⟩

theorem lowerTotalExpr_delay_some {env : List VarId} {e : Expr} {t : Term}
    (h : lowerTotalExpr env (.Delay e) = some t) :
    ∃ te, lowerTotalExpr env e = some te ∧ t = .Delay te := by
  rw [MIR.lowerTotalExpr_delay] at h
  cases he : lowerTotalExpr env e with
  | none => rw [he] at h; cases h
  | some te => rw [he] at h; cases h; exact ⟨te, rfl, rfl⟩

theorem lowerTotalExpr_lam_some {env : List VarId} {x : VarId} {e : Expr} {t : Term}
    (h : lowerTotalExpr env (.Lam x e) = some t) :
    ∃ te, lowerTotalExpr (x :: env) e = some te ∧ t = .Lam 0 te := by
  rw [MIR.lowerTotalExpr_lam] at h
  cases he : lowerTotalExpr (x :: env) e with
  | none => rw [he] at h; cases h
  | some te => rw [he] at h; cases h; exact ⟨te, rfl, rfl⟩

theorem lowerTotalExpr_var_some {env : List VarId} {x : VarId} {t : Term}
    (h : lowerTotalExpr env (.Var x) = some t) :
    ∃ i, envLookupT env x = some i ∧ t = .Var (i + 1) := by
  rw [lowerTotalExpr_var] at h
  cases hx : envLookupT env x with
  | none => rw [hx] at h; cases h
  | some i => rw [hx] at h; cases h; exact ⟨i, rfl, rfl⟩

theorem lowerTotalExpr_case_some {env : List VarId} {s : Expr} {alts : List Expr} {t : Term}
    (h : lowerTotalExpr env (.Case s alts) = some t) :
    ∃ ts talts, lowerTotalExpr env s = some ts ∧ MIR.lowerTotalExprList env alts = some talts ∧
      t = .Case ts talts := by
  rw [MIR.lowerTotalExpr_case_of_list] at h
  cases hs : lowerTotalExpr env s with
  | none => rw [hs] at h; cases h
  | some ts =>
    cases ha : MIR.lowerTotalExprList env alts with
    | none => rw [hs, ha] at h; cases h
    | some talts => rw [hs, ha] at h; cases h; exact ⟨ts, talts, rfl, rfl, rfl⟩

end Moist.Verified.ShapeFacts
