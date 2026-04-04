import Moist.Verified.Semantics

/-! # Fundamental Lemma & ValueEq Properties

This file contains `valueEq_refl`, `valueEq_symm`, `valueEq_trans` and
the transitivity lemmas for `BehEqClosed`, `BehEq`, and `Refines`.

It is split out of `Semantics.lean` because `valueEq_refl` for VLam
requires the **fundamental lemma** (environment-variation under bounded
steps), whose proof needs CEK step-simulation infrastructure that cannot
live in `Semantics.lean` without creating import cycles. -/

namespace Moist.Verified.Semantics

open Moist.CEK
open Moist.Plutus.Term (Term Const)
open Moist.MIR (Expr lowerTotalExpr lowerTotalExpr_eq_lowerTotal fixCount)

/-! ## Fundamental Lemma for VLam Reflexivity -/

/-- The "fundamental lemma" of the step-indexed logical relation, parameterized
    by `valueEq_refl` at indices `≤ j`.

    Given the same body and closure env, with `ValueEq j`-related extension args,
    bounded computation agrees on error/halt and produces `ValueEq (j - n)`
    results (observation budget decays with computation steps). -/
theorem fundemental_lemma (j : Nat)
    (veq_refl : ∀ i, i ≤ j → ∀ v : CekValue, ValueEq i v v)
    (body : Term) (env : CekEnv)
    (arg1 arg2 : CekValue) (hargs : ValueEq j arg1 arg2)
    (stk1 stk2 : Stack) (hstk : StackEqR (ValueEq j) stk1 stk2)
    (n : Nat) (hn : n ≤ j) :
    (steps n (.compute stk1 (env.extend arg1) body) = .error ↔
     steps n (.compute stk2 (env.extend arg2) body) = .error) ∧
    (∀ v1, steps n (.compute stk1 (env.extend arg1) body) = .halt v1 →
      ∃ v2, steps n (.compute stk2 (env.extend arg2) body) = .halt v2 ∧
        ValueEq (j - n) v1 v2) ∧
    (∀ v2, steps n (.compute stk2 (env.extend arg2) body) = .halt v2 →
      ∃ v1, steps n (.compute stk1 (env.extend arg1) body) = .halt v1 ∧
        ValueEq (j - n) v1 v2) := by
  sorry

/-! ## StackEqR / FrameEqR / EnvEqR helpers -/

private theorem envEqR_symm {R : CekValue → CekValue → Prop}
    (hR : ∀ v₁ v₂, R v₁ v₂ → R v₂ v₁) :
    ∀ e₁ e₂, EnvEqR R e₁ e₂ → EnvEqR R e₂ e₁
  | .nil, .nil, _ => trivial
  | .cons v1 e1, .cons v2 e2, h => ⟨hR v1 v2 h.1, envEqR_symm hR e1 e2 h.2⟩
  | .nil, .cons _ _, h => absurd h (by simp [EnvEqR])
  | .cons _ _, .nil, h => absurd h (by simp [EnvEqR])

private theorem listR_symm {R : CekValue → CekValue → Prop}
    (hR : ∀ v₁ v₂, R v₁ v₂ → R v₂ v₁) :
    ∀ l₁ l₂, ListR R l₁ l₂ → ListR R l₂ l₁
  | [], [], _ => trivial
  | a :: as, b :: bs, h => ⟨hR a b h.1, listR_symm hR as bs h.2⟩
  | [], _ :: _, h => absurd h (by simp [ListR])
  | _ :: _, [], h => absurd h (by simp [ListR])

private theorem frameEqR_symm {R : CekValue → CekValue → Prop}
    (hR : ∀ v₁ v₂, R v₁ v₂ → R v₂ v₁)
    (f₁ f₂ : Frame) (h : FrameEqR R f₁ f₂) : FrameEqR R f₂ f₁ := by
  cases f₁ <;> cases f₂ <;> simp [FrameEqR] at h ⊢
  all_goals (try exact trivial)
  case arg.arg t1 e1 t2 e2 => exact ⟨h.1.symm, envEqR_symm hR e1 e2 h.2⟩
  case funV.funV v1 v2 => exact hR v1 v2 h
  case applyArg.applyArg v1 v2 => exact hR v1 v2 h
  case constrField.constrField tag1 d1 todo1 env1 tag2 d2 todo2 env2 =>
    exact ⟨h.1.symm, h.2.1.symm, listR_symm hR d1 d2 h.2.2.1, envEqR_symm hR env1 env2 h.2.2.2⟩
  case caseScrutinee.caseScrutinee alts1 env1 alts2 env2 =>
    exact ⟨h.1.symm, envEqR_symm hR env1 env2 h.2⟩

private theorem stackEqR_symm {R : CekValue → CekValue → Prop}
    (hR : ∀ v₁ v₂, R v₁ v₂ → R v₂ v₁) :
    ∀ s₁ s₂, StackEqR R s₁ s₂ → StackEqR R s₂ s₁
  | [], [], _ => trivial
  | f1 :: s1, f2 :: s2, h => ⟨frameEqR_symm hR f1 f2 h.1, stackEqR_symm hR s1 s2 h.2⟩
  | [], _ :: _, h => absurd h (by simp [StackEqR])
  | _ :: _, [], h => absurd h (by simp [StackEqR])

private theorem envEqR_refl {R : CekValue → CekValue → Prop}
    (hR : ∀ v, R v v) :
    ∀ e, EnvEqR R e e
  | .nil => trivial
  | .cons v e => ⟨hR v, envEqR_refl hR e⟩

private theorem listR_refl {R : CekValue → CekValue → Prop}
    (hR : ∀ v, R v v) :
    ∀ l, ListR R l l
  | [] => trivial
  | a :: as => ⟨hR a, listR_refl hR as⟩

private theorem frameEqR_refl {R : CekValue → CekValue → Prop}
    (hR : ∀ v, R v v)
    (f : Frame) : FrameEqR R f f := by
  cases f with
  | force => trivial
  | arg t env => exact ⟨rfl, envEqR_refl hR env⟩
  | funV v => exact hR v
  | applyArg v => exact hR v
  | constrField tag done todo env => exact ⟨rfl, rfl, listR_refl hR done, envEqR_refl hR env⟩
  | caseScrutinee alts env => exact ⟨rfl, envEqR_refl hR env⟩

private theorem stackEqR_refl {R : CekValue → CekValue → Prop}
    (hR : ∀ v, R v v) :
    ∀ s, StackEqR R s s
  | [] => trivial
  | f :: s => ⟨frameEqR_refl hR f, stackEqR_refl hR s⟩

/-! ## ValueEq properties -/

mutual
  /-- `ValueEq` is reflexive at every step index. -/
  theorem valueEq_refl : ∀ (k : Nat) (v : CekValue), ValueEq k v v
    | 0, _ => by simp [ValueEq]
    | _ + 1, .VCon _ => by simp [ValueEq]
    | k + 1, .VLam body env => by
      unfold ValueEq; intro j hj arg1 arg2 hargs stk1 stk2 hstk n hn
      exact fundemental_lemma j (fun i hi v => valueEq_refl i v) body env arg1 arg2 hargs stk1 stk2 hstk n hn
    | k + 1, .VDelay _ _ => by
      unfold ValueEq; intro j hj stk1 stk2 hstk n hn
      sorry -- needs bisimulation: same body/env on related stacks
    | _ + 1, .VConstr _ fields => by
      unfold ValueEq; exact ⟨rfl, listValueEq_refl _ fields⟩
    | k + 1, .VBuiltin b args ea => by
      unfold ValueEq; exact ⟨rfl, listValueEq_refl (k + 1) args, rfl⟩
  theorem listValueEq_refl : ∀ (k : Nat) (vs : List CekValue), ListValueEq k vs vs
    | _, [] => by simp [ListValueEq]
    | k, v :: vs => by simp only [ListValueEq]; exact ⟨valueEq_refl k v, listValueEq_refl k vs⟩
  theorem valueEq_symm : ∀ (k : Nat) (v₁ v₂ : CekValue), ValueEq k v₁ v₂ → ValueEq k v₂ v₁
    | 0, _, _, _ => by simp [ValueEq]
    | _ + 1, .VCon _, .VCon _, h => by simp only [ValueEq] at h ⊢; exact h.symm
    | k + 1, .VLam _ _, .VLam _ _, h => by
      unfold ValueEq at h ⊢; intro j hj arg1 arg2 hargs stk1 stk2 hstk n hn
      have hargs' := valueEq_symm j _ _ hargs
      have hstk' := stackEqR_symm (valueEq_symm j) stk1 stk2 hstk
      have ⟨herr, hhalt1, hhalt2⟩ := h j hj arg2 arg1 hargs' stk2 stk1 hstk' n hn
      exact ⟨herr.symm,
             fun v1 hv1 => let ⟨v2, hv2, hve⟩ := hhalt2 v1 hv1; ⟨v2, hv2, valueEq_symm (j - n) _ _ hve⟩,
             fun v2 hv2 => let ⟨v1, hv1, hve⟩ := hhalt1 v2 hv2; ⟨v1, hv1, valueEq_symm (j - n) _ _ hve⟩⟩
    | k + 1, .VDelay _ _, .VDelay _ _, h => by
      unfold ValueEq at h ⊢; intro j hj stk1 stk2 hstk n hn
      have hstk' := stackEqR_symm (valueEq_symm j) stk1 stk2 hstk
      have ⟨herr, hhalt1, hhalt2⟩ := h j hj stk2 stk1 hstk' n hn
      exact ⟨herr.symm,
             fun v1 hv1 => let ⟨v2, hv2, hve⟩ := hhalt2 v1 hv1; ⟨v2, hv2, valueEq_symm (j - n) _ _ hve⟩,
             fun v2 hv2 => let ⟨v1, hv1, hve⟩ := hhalt1 v2 hv2; ⟨v1, hv1, valueEq_symm (j - n) _ _ hve⟩⟩
    | _ + 1, .VConstr _ _, .VConstr _ _, h => by
      unfold ValueEq at h ⊢; exact ⟨h.1.symm, listValueEq_symm _ _ _ h.2⟩
    | k + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, h => by
      unfold ValueEq at h ⊢
      exact ⟨h.1.symm, listValueEq_symm (k + 1) _ _ h.2.1, h.2.2.symm⟩
    | _ + 1, .VCon _, .VLam _ _, h => by simp [ValueEq] at h
    | _ + 1, .VCon _, .VDelay _ _, h => by simp [ValueEq] at h
    | _ + 1, .VCon _, .VConstr _ _, h => by simp [ValueEq] at h
    | _ + 1, .VCon _, .VBuiltin _ _ _, h => by simp [ValueEq] at h
    | _ + 1, .VLam _ _, .VCon _, h => by simp [ValueEq] at h
    | _ + 1, .VLam _ _, .VDelay _ _, h => by simp [ValueEq] at h
    | _ + 1, .VLam _ _, .VConstr _ _, h => by simp [ValueEq] at h
    | _ + 1, .VLam _ _, .VBuiltin _ _ _, h => by simp [ValueEq] at h
    | _ + 1, .VDelay _ _, .VCon _, h => by simp [ValueEq] at h
    | _ + 1, .VDelay _ _, .VLam _ _, h => by simp [ValueEq] at h
    | _ + 1, .VDelay _ _, .VConstr _ _, h => by simp [ValueEq] at h
    | _ + 1, .VDelay _ _, .VBuiltin _ _ _, h => by simp [ValueEq] at h
    | _ + 1, .VConstr _ _, .VCon _, h => by simp [ValueEq] at h
    | _ + 1, .VConstr _ _, .VLam _ _, h => by simp [ValueEq] at h
    | _ + 1, .VConstr _ _, .VDelay _ _, h => by simp [ValueEq] at h
    | _ + 1, .VConstr _ _, .VBuiltin _ _ _, h => by simp [ValueEq] at h
    | _ + 1, .VBuiltin _ _ _, .VCon _, h => by simp [ValueEq] at h
    | _ + 1, .VBuiltin _ _ _, .VLam _ _, h => by simp [ValueEq] at h
    | _ + 1, .VBuiltin _ _ _, .VDelay _ _, h => by simp [ValueEq] at h
    | _ + 1, .VBuiltin _ _ _, .VConstr _ _, h => by simp [ValueEq] at h
  theorem listValueEq_symm : ∀ (k : Nat) (vs₁ vs₂ : List CekValue),
      ListValueEq k vs₁ vs₂ → ListValueEq k vs₂ vs₁
    | _, [], [], _ => by simp [ListValueEq]
    | k, _ :: _, _ :: _, h => by
      simp only [ListValueEq] at h ⊢
      exact ⟨valueEq_symm k _ _ h.1, listValueEq_symm k _ _ h.2⟩
    | _, [], _ :: _, h => by exact absurd h (by simp [ListValueEq])
    | _, _ :: _, [], h => by exact absurd h (by simp [ListValueEq])
  theorem valueEq_trans : ∀ (k : Nat) (v₁ v₂ v₃ : CekValue),
      ValueEq k v₁ v₂ → ValueEq k v₂ v₃ → ValueEq k v₁ v₃
    | 0, _, _, _, _, _ => by simp [ValueEq]
    -- Matching constructors
    | _ + 1, .VCon _, .VCon _, .VCon _, h12, h23 => by
      simp only [ValueEq] at h12 h23 ⊢; exact h12.trans h23
    | k + 1, .VLam _ _, .VLam _ _, .VLam _ _, h12, h23 => by
      unfold ValueEq at h12 h23 ⊢; intro j hj arg1 arg3 hargs13 stk1 stk3 hstk13 n hn
      -- Chain: use arg2 := arg1 and stk2 := stk1 for the middle
      have hstk_refl := stackEqR_refl (valueEq_refl j) stk1
      have h12' := h12 j hj arg1 arg1 (valueEq_refl j arg1) stk1 stk1 hstk_refl n hn
      have h23' := h23 j hj arg1 arg3 hargs13 stk1 stk3 hstk13 n hn
      refine ⟨h12'.1.trans h23'.1, fun v1 hv1 => ?_, fun v3 hv3 => ?_⟩
      · obtain ⟨v2, hv2, hve12⟩ := h12'.2.1 v1 hv1
        obtain ⟨v3, hv3, hve23⟩ := h23'.2.1 v2 hv2
        exact ⟨v3, hv3, valueEq_trans (j - n) _ _ _ hve12 hve23⟩
      · obtain ⟨v2, hv2, hve23⟩ := h23'.2.2 v3 hv3
        obtain ⟨v1, hv1, hve12⟩ := h12'.2.2 v2 hv2
        exact ⟨v1, hv1, valueEq_trans (j - n) _ _ _ hve12 hve23⟩
    | k + 1, .VDelay _ _, .VDelay _ _, .VDelay _ _, h12, h23 => by
      unfold ValueEq at h12 h23 ⊢; intro j hj stk1 stk3 hstk13 n hn
      have hstk_refl := stackEqR_refl (valueEq_refl j) stk1
      have h12' := h12 j hj stk1 stk1 hstk_refl n hn
      have h23' := h23 j hj stk1 stk3 hstk13 n hn
      refine ⟨h12'.1.trans h23'.1, fun v1 hv1 => ?_, fun v3 hv3 => ?_⟩
      · obtain ⟨v2, hv2, hve12⟩ := h12'.2.1 v1 hv1
        obtain ⟨v3, hv3, hve23⟩ := h23'.2.1 v2 hv2
        exact ⟨v3, hv3, valueEq_trans (j - n) _ _ _ hve12 hve23⟩
      · obtain ⟨v2, hv2, hve23⟩ := h23'.2.2 v3 hv3
        obtain ⟨v1, hv1, hve12⟩ := h12'.2.2 v2 hv2
        exact ⟨v1, hv1, valueEq_trans (j - n) _ _ _ hve12 hve23⟩
    | _ + 1, .VConstr _ _, .VConstr _ _, .VConstr _ _, h12, h23 => by
      unfold ValueEq at h12 h23 ⊢
      exact ⟨h12.1.trans h23.1, listValueEq_trans _ _ _ _ h12.2 h23.2⟩
    | k + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, .VBuiltin _ _ _, h12, h23 => by
      unfold ValueEq at h12 h23 ⊢
      exact ⟨h12.1.trans h23.1, listValueEq_trans (k + 1) _ _ _ h12.2.1 h23.2.1,
             h12.2.2.trans h23.2.2⟩
    -- h12 is False (v₁ and v₂ have different constructors)
    | _ + 1, .VCon _, .VLam _ _, _, h, _ | _ + 1, .VCon _, .VDelay _ _, _, h, _
    | _ + 1, .VCon _, .VConstr _ _, _, h, _ | _ + 1, .VCon _, .VBuiltin _ _ _, _, h, _
    | _ + 1, .VLam _ _, .VCon _, _, h, _ | _ + 1, .VLam _ _, .VDelay _ _, _, h, _
    | _ + 1, .VLam _ _, .VConstr _ _, _, h, _ | _ + 1, .VLam _ _, .VBuiltin _ _ _, _, h, _
    | _ + 1, .VDelay _ _, .VCon _, _, h, _ | _ + 1, .VDelay _ _, .VLam _ _, _, h, _
    | _ + 1, .VDelay _ _, .VConstr _ _, _, h, _ | _ + 1, .VDelay _ _, .VBuiltin _ _ _, _, h, _
    | _ + 1, .VConstr _ _, .VCon _, _, h, _ | _ + 1, .VConstr _ _, .VLam _ _, _, h, _
    | _ + 1, .VConstr _ _, .VDelay _ _, _, h, _ | _ + 1, .VConstr _ _, .VBuiltin _ _ _, _, h, _
    | _ + 1, .VBuiltin _ _ _, .VCon _, _, h, _ | _ + 1, .VBuiltin _ _ _, .VLam _ _, _, h, _
    | _ + 1, .VBuiltin _ _ _, .VDelay _ _, _, h, _
    | _ + 1, .VBuiltin _ _ _, .VConstr _ _, _, h, _ => by simp [ValueEq] at h
    -- h23 is False (v₂ and v₃ have different constructors, v₁ matches v₂)
    | _ + 1, .VCon _, .VCon _, .VLam _ _, _, h | _ + 1, .VCon _, .VCon _, .VDelay _ _, _, h
    | _ + 1, .VCon _, .VCon _, .VConstr _ _, _, h | _ + 1, .VCon _, .VCon _, .VBuiltin _ _ _, _, h
    | _ + 1, .VLam _ _, .VLam _ _, .VCon _, _, h | _ + 1, .VLam _ _, .VLam _ _, .VDelay _ _, _, h
    | _ + 1, .VLam _ _, .VLam _ _, .VConstr _ _, _, h
    | _ + 1, .VLam _ _, .VLam _ _, .VBuiltin _ _ _, _, h
    | _ + 1, .VDelay _ _, .VDelay _ _, .VCon _, _, h | _ + 1, .VDelay _ _, .VDelay _ _, .VLam _ _, _, h
    | _ + 1, .VDelay _ _, .VDelay _ _, .VConstr _ _, _, h
    | _ + 1, .VDelay _ _, .VDelay _ _, .VBuiltin _ _ _, _, h
    | _ + 1, .VConstr _ _, .VConstr _ _, .VCon _, _, h
    | _ + 1, .VConstr _ _, .VConstr _ _, .VLam _ _, _, h
    | _ + 1, .VConstr _ _, .VConstr _ _, .VDelay _ _, _, h
    | _ + 1, .VConstr _ _, .VConstr _ _, .VBuiltin _ _ _, _, h
    | _ + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, .VCon _, _, h
    | _ + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, .VLam _ _, _, h
    | _ + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, .VDelay _ _, _, h
    | _ + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, .VConstr _ _, _, h => by simp [ValueEq] at h
  theorem listValueEq_trans : ∀ (k : Nat) (vs₁ vs₂ vs₃ : List CekValue),
      ListValueEq k vs₁ vs₂ → ListValueEq k vs₂ vs₃ → ListValueEq k vs₁ vs₃
    | _, [], [], [], _, _ => by simp [ListValueEq]
    | k, _ :: _, _ :: _, _ :: _, h12, h23 => by
      simp only [ListValueEq] at h12 h23 ⊢
      exact ⟨valueEq_trans k _ _ _ h12.1 h23.1, listValueEq_trans k _ _ _ h12.2 h23.2⟩
    | _, [], _ :: _, _, h, _ | _, _ :: _, [], _, h, _ => by simp [ListValueEq] at h
    | _, [], [], _ :: _, _, h => by simp [ListValueEq] at h
    | _, _ :: _, _ :: _, [], _, h => by simp [ListValueEq] at h
end

/-! ## Transitivity of behavioral equivalence -/

private abbrev emptyEnv : List MIR.VarId := []

private theorem behEqClosed_extract {m1 m2 : Expr} {t1 t2 : Term}
    (h1 : lowerTotalExpr emptyEnv m1 = some t1)
    (h2 : lowerTotalExpr emptyEnv m2 = some t2)
    (h : BehEqClosed m1 m2) :
    (Reaches (.compute [] .nil t1) .error ↔ Reaches (.compute [] .nil t2) .error) ∧
    (Halts (.compute [] .nil t1) ↔ Halts (.compute [] .nil t2)) ∧
    ∀ (k : Nat) (v1 v2 : CekValue),
      Reaches (.compute [] .nil t1) (.halt v1) →
      Reaches (.compute [] .nil t2) (.halt v2) →
      ValueEq k v1 v2 := by
  unfold BehEqClosed at h; rw [h1, h2] at h; exact h

/-- **Transitivity of closed behavioral equivalence.** -/
theorem behEqClosed_trans {a b c : Expr}
    {tb : Term} (hb : lowerTotalExpr emptyEnv b = some tb)
    (h12 : a ≋ᶜ b) (h23 : b ≋ᶜ c) : a ≋ᶜ c := by
  unfold BehEqClosed
  cases ha : lowerTotalExpr emptyEnv a with
  | none => split <;> trivial
  | some ta =>
    cases hc : lowerTotalExpr emptyEnv c with
    | none => split <;> trivial
    | some tc =>
      simp only []
      have ⟨herr12, hh12, hv12⟩ := behEqClosed_extract ha hb h12
      have ⟨herr23, hh23, hv23⟩ := behEqClosed_extract hb hc h23
      refine ⟨herr12.trans herr23, hh12.trans hh23, ?_⟩
      intro k v₁ v₃ hv₁ hv₃
      obtain ⟨v₂, hv₂⟩ := hh12.mp ⟨v₁, hv₁⟩
      exact valueEq_trans k v₁ v₂ v₃ (hv12 k v₁ v₂ hv₁ hv₂) (hv23 k v₂ v₃ hv₂ hv₃)

private theorem behEq_extract {m1 m2 : Expr} {env : List MIR.VarId} {t1 t2 : Term}
    (h1 : lowerTotalExpr env m1 = some t1) (h2 : lowerTotalExpr env m2 = some t2)
    (h : BehEq m1 m2) :
    ∀ ρ : CekEnv, WellSizedEnv env.length ρ →
      (Reaches (.compute [] ρ t1) .error ↔ Reaches (.compute [] ρ t2) .error) ∧
      (Halts (.compute [] ρ t1) ↔ Halts (.compute [] ρ t2)) ∧
      ∀ (k : Nat) (v1 v2 : CekValue),
        Reaches (.compute [] ρ t1) (.halt v1) →
        Reaches (.compute [] ρ t2) (.halt v2) →
        ValueEq k v1 v2 := by
  have := h env; rw [h1, h2] at this; exact this

/-- **Transitivity of behavioral equivalence for open terms.** -/
theorem behEq_trans {a b c : Expr}
    (hlb : ∀ env, (lowerTotalExpr env a).isSome → (lowerTotalExpr env b).isSome)
    (h12 : a ≋ b) (h23 : b ≋ c) : a ≋ c := by
  unfold BehEq; intro env
  cases ha : lowerTotalExpr env a with
  | none => split <;> trivial
  | some ta =>
    obtain ⟨tb, hb⟩ := Option.isSome_iff_exists.mp (hlb env (by simp [ha]))
    cases hc : lowerTotalExpr env c with
    | none => split <;> trivial
    | some tc =>
      simp only []
      have h12' := behEq_extract ha hb h12
      have h23' := behEq_extract hb hc h23
      intro ρ hwf
      have ⟨herr12, hh12, hv12⟩ := h12' ρ hwf
      have ⟨herr23, hh23, hv23⟩ := h23' ρ hwf
      refine ⟨herr12.trans herr23, hh12.trans hh23, ?_⟩
      intro k v₁ v₃ hv₁ hv₃
      obtain ⟨v₂, hv₂⟩ := hh12.mp ⟨v₁, hv₁⟩
      exact valueEq_trans k v₁ v₂ v₃ (hv12 k v₁ v₂ hv₁ hv₂) (hv23 k v₂ v₃ hv₂ hv₃)

/-- **Unconditional transitivity of refinement.** -/
theorem refines_trans {a b c : Expr}
    (h12 : Refines a b) (h23 : Refines b c) : Refines a c :=
  ⟨fun env ha => h23.1 env (h12.1 env ha),
   behEq_trans h12.1 h12.2 h23.2⟩

end Moist.Verified.Semantics
