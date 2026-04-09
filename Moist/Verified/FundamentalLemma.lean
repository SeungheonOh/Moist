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
    (stk1 stk2 : Stack) (hstk : StackEqR (ValueEq j) stk1 stk2) :
    ((∃ n, n ≤ j ∧ steps n (.compute stk1 (env.extend arg1) body) = .error) ↔
     (∃ m, m ≤ j ∧ steps m (.compute stk2 (env.extend arg2) body) = .error)) ∧
    ((∃ n v, n ≤ j ∧ steps n (.compute stk1 (env.extend arg1) body) = .halt v) ↔
     (∃ m v, m ≤ j ∧ steps m (.compute stk2 (env.extend arg2) body) = .halt v)) ∧
    (∀ n m, n ≤ j → m ≤ j → ∀ v1 v2,
      steps n (.compute stk1 (env.extend arg1) body) = .halt v1 →
      steps m (.compute stk2 (env.extend arg2) body) = .halt v2 →
      ValueEq (j - max n m) v1 v2) := by
  sorry

/-- The fundamental lemma for VDelay: same body and env, related stacks.
    Parallel to `fundemental_lemma` but without argument extension. -/
theorem fundemental_lemma_delay (j : Nat)
    (veq_refl : ∀ i, i ≤ j → ∀ v : CekValue, ValueEq i v v)
    (body : Term) (env : CekEnv)
    (stk1 stk2 : Stack) (hstk : StackEqR (ValueEq j) stk1 stk2) :
    ((∃ n, n ≤ j ∧ steps n (.compute stk1 env body) = .error) ↔
     (∃ m, m ≤ j ∧ steps m (.compute stk2 env body) = .error)) ∧
    ((∃ n v, n ≤ j ∧ steps n (.compute stk1 env body) = .halt v) ↔
     (∃ m v, m ≤ j ∧ steps m (.compute stk2 env body) = .halt v)) ∧
    (∀ n m, n ≤ j → m ≤ j → ∀ v1 v2,
      steps n (.compute stk1 env body) = .halt v1 →
      steps m (.compute stk2 env body) = .halt v2 →
      ValueEq (j - max n m) v1 v2) := by
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

/-! ### Relation-implication helpers

Given a pointwise implication `R₁ → R₂` on values, lift it to `EnvEqR`,
`ListR`, `FrameEqR`, and `StackEqR`. Used with `R₁ := ValueEq k`,
`R₂ := ValueEq j` (for `j ≤ k` via `valueEq_mono`) to downgrade
a stack/environment relation to a lower step index. -/

private theorem envEqR_implication {R₁ R₂ : CekValue → CekValue → Prop}
    (h : ∀ v₁ v₂, R₁ v₁ v₂ → R₂ v₁ v₂) :
    ∀ e₁ e₂, EnvEqR R₁ e₁ e₂ → EnvEqR R₂ e₁ e₂
  | .nil, .nil, _ => trivial
  | .cons _ e1, .cons _ e2, hh => ⟨h _ _ hh.1, envEqR_implication h e1 e2 hh.2⟩
  | .nil, .cons _ _, hh => absurd hh (by simp [EnvEqR])
  | .cons _ _, .nil, hh => absurd hh (by simp [EnvEqR])

private theorem listR_implication {R₁ R₂ : CekValue → CekValue → Prop}
    (h : ∀ v₁ v₂, R₁ v₁ v₂ → R₂ v₁ v₂) :
    ∀ l₁ l₂, ListR R₁ l₁ l₂ → ListR R₂ l₁ l₂
  | [], [], _ => trivial
  | _ :: as, _ :: bs, hh => ⟨h _ _ hh.1, listR_implication h as bs hh.2⟩
  | [], _ :: _, hh => absurd hh (by simp [ListR])
  | _ :: _, [], hh => absurd hh (by simp [ListR])

private theorem frameEqR_implication {R₁ R₂ : CekValue → CekValue → Prop}
    (h : ∀ v₁ v₂, R₁ v₁ v₂ → R₂ v₁ v₂)
    (f₁ f₂ : Frame) (hh : FrameEqR R₁ f₁ f₂) : FrameEqR R₂ f₁ f₂ := by
  cases f₁ <;> cases f₂ <;> simp [FrameEqR] at hh ⊢
  all_goals (try exact trivial)
  case arg.arg => exact ⟨hh.1, envEqR_implication h _ _ hh.2⟩
  case funV.funV => exact h _ _ hh
  case applyArg.applyArg => exact h _ _ hh
  case constrField.constrField =>
    exact ⟨hh.1, hh.2.1, listR_implication h _ _ hh.2.2.1,
           envEqR_implication h _ _ hh.2.2.2⟩
  case caseScrutinee.caseScrutinee => exact ⟨hh.1, envEqR_implication h _ _ hh.2⟩

private theorem stackEqR_implication {R₁ R₂ : CekValue → CekValue → Prop}
    (h : ∀ v₁ v₂, R₁ v₁ v₂ → R₂ v₁ v₂) :
    ∀ s₁ s₂, StackEqR R₁ s₁ s₂ → StackEqR R₂ s₁ s₂
  | [], [], _ => trivial
  | f1 :: s1, f2 :: s2, hh =>
      ⟨frameEqR_implication h f1 f2 hh.1, stackEqR_implication h s1 s2 hh.2⟩
  | [], _ :: _, hh => absurd hh (by simp [StackEqR])
  | _ :: _, [], hh => absurd hh (by simp [StackEqR])

/-! ## ValueEq properties -/

mutual
  /-- `ValueEq` is reflexive at every step index. -/
  theorem valueEq_refl : ∀ (k : Nat) (v : CekValue), ValueEq k v v
    | 0, _ => by simp [ValueEq]
    | _ + 1, .VCon _ => by simp [ValueEq]
    | k + 1, .VLam body env => by
      unfold ValueEq; intro j hj arg1 arg2 hargs stk1 stk2 hstk
      exact fundemental_lemma j (fun i hi v => valueEq_refl i v)
        body env arg1 arg2 hargs stk1 stk2 hstk
    | k + 1, .VDelay body env => by
      unfold ValueEq; intro j hj stk1 stk2 hstk
      exact fundemental_lemma_delay j (fun i hi v => valueEq_refl i v)
        body env stk1 stk2 hstk
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
      unfold ValueEq at h ⊢; intro j hj arg1 arg2 hargs stk1 stk2 hstk
      have hargs' := valueEq_symm j _ _ hargs
      have hstk' := stackEqR_symm (valueEq_symm j) stk1 stk2 hstk
      have hswap := h j hj arg2 arg1 hargs' stk2 stk1 hstk'
      refine ⟨hswap.1.symm, hswap.2.1.symm, ?_⟩
      intro n m hn hm v1 v2 hv1 hv2
      have hr := hswap.2.2 m n hm hn v2 v1 hv2 hv1
      have hmax : max m n = max n m := Nat.max_comm m n
      rw [hmax] at hr
      exact valueEq_symm (j - max n m) _ _ hr
    | k + 1, .VDelay _ _, .VDelay _ _, h => by
      unfold ValueEq at h ⊢; intro j hj stk1 stk2 hstk
      have hstk' := stackEqR_symm (valueEq_symm j) stk1 stk2 hstk
      have hswap := h j hj stk2 stk1 hstk'
      refine ⟨hswap.1.symm, hswap.2.1.symm, ?_⟩
      intro n m hn hm v1 v2 hv1 hv2
      have hr := hswap.2.2 m n hm hn v2 v1 hv2 hv1
      have hmax : max m n = max n m := Nat.max_comm m n
      rw [hmax] at hr
      exact valueEq_symm (j - max n m) _ _ hr
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
  theorem valueEq_mono : ∀ (j k : Nat), j ≤ k →
      ∀ (v₁ v₂ : CekValue), ValueEq k v₁ v₂ → ValueEq j v₁ v₂
    | 0, _, _, _, _, _ => by simp [ValueEq]
    | _ + 1, 0, hjk, _, _, _ => absurd hjk (by omega)
    | j + 1, k + 1, hjk, .VCon c₁, .VCon c₂, h => by
      simp only [ValueEq] at h ⊢; exact h
    | j + 1, k + 1, hjk, .VLam b₁ e₁, .VLam b₂ e₂, h => by
      unfold ValueEq at h ⊢; intro i hi arg1 arg2 hargs stk1 stk2 hstk
      exact h i (by omega) arg1 arg2 hargs stk1 stk2 hstk
    | j + 1, k + 1, hjk, .VDelay b₁ e₁, .VDelay b₂ e₂, h => by
      unfold ValueEq at h ⊢; intro i hi stk1 stk2 hstk
      exact h i (by omega) stk1 stk2 hstk
    | j + 1, k + 1, hjk, .VConstr _ _, .VConstr _ _, h => by
      unfold ValueEq at h ⊢
      exact ⟨h.1, listValueEq_mono j k (by omega) _ _ h.2⟩
    | j + 1, k + 1, hjk, .VBuiltin _ _ _, .VBuiltin _ _ _, h => by
      unfold ValueEq at h ⊢
      exact ⟨h.1, listValueEq_mono (j + 1) (k + 1) (by omega) _ _ h.2.1, h.2.2⟩
    | _ + 1, _ + 1, _, .VCon _, .VLam _ _, h => by simp [ValueEq] at h
    | _ + 1, _ + 1, _, .VCon _, .VDelay _ _, h => by simp [ValueEq] at h
    | _ + 1, _ + 1, _, .VCon _, .VConstr _ _, h => by simp [ValueEq] at h
    | _ + 1, _ + 1, _, .VCon _, .VBuiltin _ _ _, h => by simp [ValueEq] at h
    | _ + 1, _ + 1, _, .VLam _ _, .VCon _, h => by simp [ValueEq] at h
    | _ + 1, _ + 1, _, .VLam _ _, .VDelay _ _, h => by simp [ValueEq] at h
    | _ + 1, _ + 1, _, .VLam _ _, .VConstr _ _, h => by simp [ValueEq] at h
    | _ + 1, _ + 1, _, .VLam _ _, .VBuiltin _ _ _, h => by simp [ValueEq] at h
    | _ + 1, _ + 1, _, .VDelay _ _, .VCon _, h => by simp [ValueEq] at h
    | _ + 1, _ + 1, _, .VDelay _ _, .VLam _ _, h => by simp [ValueEq] at h
    | _ + 1, _ + 1, _, .VDelay _ _, .VConstr _ _, h => by simp [ValueEq] at h
    | _ + 1, _ + 1, _, .VDelay _ _, .VBuiltin _ _ _, h => by simp [ValueEq] at h
    | _ + 1, _ + 1, _, .VConstr _ _, .VCon _, h => by simp [ValueEq] at h
    | _ + 1, _ + 1, _, .VConstr _ _, .VLam _ _, h => by simp [ValueEq] at h
    | _ + 1, _ + 1, _, .VConstr _ _, .VDelay _ _, h => by simp [ValueEq] at h
    | _ + 1, _ + 1, _, .VConstr _ _, .VBuiltin _ _ _, h => by simp [ValueEq] at h
    | _ + 1, _ + 1, _, .VBuiltin _ _ _, .VCon _, h => by simp [ValueEq] at h
    | _ + 1, _ + 1, _, .VBuiltin _ _ _, .VLam _ _, h => by simp [ValueEq] at h
    | _ + 1, _ + 1, _, .VBuiltin _ _ _, .VDelay _ _, h => by simp [ValueEq] at h
    | _ + 1, _ + 1, _, .VBuiltin _ _ _, .VConstr _ _, h => by simp [ValueEq] at h
  theorem listValueEq_mono : ∀ (j k : Nat), j ≤ k →
      ∀ (vs₁ vs₂ : List CekValue), ListValueEq k vs₁ vs₂ → ListValueEq j vs₁ vs₂
    | _, _, _, [], [], _ => by simp [ListValueEq]
    | j, k, hjk, _ :: _, _ :: _, h => by
      simp only [ListValueEq] at h ⊢
      exact ⟨valueEq_mono j k hjk _ _ h.1, listValueEq_mono j k hjk _ _ h.2⟩
    | _, _, _, [], _ :: _, h => by exact absurd h (by simp [ListValueEq])
    | _, _, _, _ :: _, [], h => by exact absurd h (by simp [ListValueEq])
end

/-! ## Pointwise transitivity of `ValueEq`

Transitivity of `ValueEq` at a single step index, proved by well-founded
recursion on `(k, sizeOf v₁)`.

The VLam/VDelay cases use a **tight-bound trick**: applying `h12` at the
unfold level `max n m` (instead of `j`) forces its halt iff to produce
a witness `p_B ≤ max n m` (because `n ≤ max n m` is the halt iff bound).
This tight bound keeps the intermediate step count inside `max n m`,
so the resulting `ValueEq (j - max n p_B) v1 w_B` downgrades cleanly to
`ValueEq (j - max n m) v1 w_B` via `valueEq_mono` (since
`max n p_B ≤ max n m`). The symmetric argument on `h23` gives
`ValueEq (j - max n m) w_B v3`, and pointwise recursion at the smaller
level `j - max n m ≤ k` closes the case. -/

mutual
  theorem valueEq_trans : ∀ (k : Nat) (v₁ v₂ v₃ : CekValue),
      ValueEq k v₁ v₂ → ValueEq k v₂ v₃ → ValueEq k v₁ v₃
    | 0, _, _, _, _, _ => by simp [ValueEq]
    | _ + 1, .VCon _, .VCon _, .VCon _, h12, h23 => by
      simp only [ValueEq] at h12 h23 ⊢; exact h12.trans h23
    | k + 1, .VLam body1 env1, .VLam body2 env2, .VLam body3 env3, h12, h23 => by
      unfold ValueEq at h12 h23 ⊢
      intro j hj arg1 arg3 hargs stk1 stk3 hstk
      -- h12 applied at the outer unfold level j with refl args/stacks.
      -- Relates A and B = (body2, env2.extend arg1, stk1).
      have h12_j := h12 j hj arg1 arg1 (valueEq_refl j arg1) stk1 stk1
        (stackEqR_refl (valueEq_refl j) stk1)
      -- h23 applied at level j with actual args and stacks. Relates B and C.
      have h23_j := h23 j hj arg1 arg3 hargs stk1 stk3 hstk
      refine ⟨h12_j.1.trans h23_j.1, h12_j.2.1.trans h23_j.2.1, ?_⟩
      intro n m hn hm v1 v3 hv1 hv3
      -- Pre-compute facts about `max n m`.
      have hn_le_M : n ≤ max n m := Nat.le_max_left n m
      have hm_le_M : m ≤ max n m := Nat.le_max_right n m
      have hM_le_j : max n m ≤ j := Nat.max_le.mpr ⟨hn, hm⟩
      have hM_le_k : max n m ≤ k := Nat.le_trans hM_le_j hj
      -- Apply h12 at unfold level `max n m` to get a tight halt witness
      -- `p_B ≤ max n m`.
      have h12_tight := h12 (max n m) hM_le_k arg1 arg1
        (valueEq_refl (max n m) arg1) stk1 stk1
        (stackEqR_refl (valueEq_refl (max n m)) stk1)
      obtain ⟨p_B, w_B, hp_B_le_M, hw_B⟩ :=
        h12_tight.2.1.mp ⟨n, v1, hn_le_M, hv1⟩
      have hp_B_le_j : p_B ≤ j := Nat.le_trans hp_B_le_M hM_le_j
      -- Value clause from h12 at level j at (n, p_B).
      have hve12 : ValueEq (j - max n p_B) v1 w_B :=
        h12_j.2.2 n p_B hn hp_B_le_j v1 w_B hv1 hw_B
      -- `max n p_B ≤ max n m`, so `j - max n m ≤ j - max n p_B`.
      have hmax_npB_le_M : max n p_B ≤ max n m :=
        Nat.max_le.mpr ⟨hn_le_M, hp_B_le_M⟩
      have hve12' : ValueEq (j - max n m) v1 w_B :=
        valueEq_mono (j - max n m) (j - max n p_B)
          (Nat.sub_le_sub_left hmax_npB_le_M j) _ _ hve12
      -- h23 at unfold level `max n m` (tight) with downgraded hargs, hstk.
      have hargs_tight : ValueEq (max n m) arg1 arg3 :=
        valueEq_mono (max n m) j hM_le_j _ _ hargs
      have hstk_tight : StackEqR (ValueEq (max n m)) stk1 stk3 :=
        stackEqR_implication
          (fun _ _ h' => valueEq_mono (max n m) j hM_le_j _ _ h') _ _ hstk
      have h23_tight := h23 (max n m) hM_le_k arg1 arg3 hargs_tight
        stk1 stk3 hstk_tight
      obtain ⟨p_B', w_B', hp_B'_le_M, hw_B'⟩ :=
        h23_tight.2.1.mpr ⟨m, v3, hm_le_M, hv3⟩
      have hp_B'_le_j : p_B' ≤ j := Nat.le_trans hp_B'_le_M hM_le_j
      -- `w_B' = w_B` by determinism of halting (same state B on both sides).
      have hwB_eq : w_B' = w_B := reaches_unique ⟨p_B', hw_B'⟩ ⟨p_B, hw_B⟩
      rw [hwB_eq] at hw_B'
      -- Value clause from h23 at level j at (p_B', m).
      have hve23 : ValueEq (j - max p_B' m) w_B v3 :=
        h23_j.2.2 p_B' m hp_B'_le_j hm w_B v3 hw_B' hv3
      have hmax_pB'm_le_M : max p_B' m ≤ max n m :=
        Nat.max_le.mpr ⟨hp_B'_le_M, hm_le_M⟩
      have hve23' : ValueEq (j - max n m) w_B v3 :=
        valueEq_mono (j - max n m) (j - max p_B' m)
          (Nat.sub_le_sub_left hmax_pB'm_le_M j) _ _ hve23
      -- Pointwise recursion at the strictly smaller level `j - max n m`.
      exact valueEq_trans (j - max n m) v1 w_B v3 hve12' hve23'
    | k + 1, .VDelay body1 env1, .VDelay body2 env2, .VDelay body3 env3, h12, h23 => by
      unfold ValueEq at h12 h23 ⊢
      intro j hj stk1 stk3 hstk
      have h12_j := h12 j hj stk1 stk1 (stackEqR_refl (valueEq_refl j) stk1)
      have h23_j := h23 j hj stk1 stk3 hstk
      refine ⟨h12_j.1.trans h23_j.1, h12_j.2.1.trans h23_j.2.1, ?_⟩
      intro n m hn hm v1 v3 hv1 hv3
      have hn_le_M : n ≤ max n m := Nat.le_max_left n m
      have hm_le_M : m ≤ max n m := Nat.le_max_right n m
      have hM_le_j : max n m ≤ j := Nat.max_le.mpr ⟨hn, hm⟩
      have hM_le_k : max n m ≤ k := Nat.le_trans hM_le_j hj
      have h12_tight := h12 (max n m) hM_le_k stk1 stk1
        (stackEqR_refl (valueEq_refl (max n m)) stk1)
      obtain ⟨p_B, w_B, hp_B_le_M, hw_B⟩ :=
        h12_tight.2.1.mp ⟨n, v1, hn_le_M, hv1⟩
      have hp_B_le_j : p_B ≤ j := Nat.le_trans hp_B_le_M hM_le_j
      have hve12 : ValueEq (j - max n p_B) v1 w_B :=
        h12_j.2.2 n p_B hn hp_B_le_j v1 w_B hv1 hw_B
      have hmax_npB_le_M : max n p_B ≤ max n m :=
        Nat.max_le.mpr ⟨hn_le_M, hp_B_le_M⟩
      have hve12' : ValueEq (j - max n m) v1 w_B :=
        valueEq_mono (j - max n m) (j - max n p_B)
          (Nat.sub_le_sub_left hmax_npB_le_M j) _ _ hve12
      have hstk_tight : StackEqR (ValueEq (max n m)) stk1 stk3 :=
        stackEqR_implication
          (fun _ _ h' => valueEq_mono (max n m) j hM_le_j _ _ h') _ _ hstk
      have h23_tight := h23 (max n m) hM_le_k stk1 stk3 hstk_tight
      obtain ⟨p_B', w_B', hp_B'_le_M, hw_B'⟩ :=
        h23_tight.2.1.mpr ⟨m, v3, hm_le_M, hv3⟩
      have hp_B'_le_j : p_B' ≤ j := Nat.le_trans hp_B'_le_M hM_le_j
      have hwB_eq : w_B' = w_B := reaches_unique ⟨p_B', hw_B'⟩ ⟨p_B, hw_B⟩
      rw [hwB_eq] at hw_B'
      have hve23 : ValueEq (j - max p_B' m) w_B v3 :=
        h23_j.2.2 p_B' m hp_B'_le_j hm w_B v3 hw_B' hv3
      have hmax_pB'm_le_M : max p_B' m ≤ max n m :=
        Nat.max_le.mpr ⟨hp_B'_le_M, hm_le_M⟩
      have hve23' : ValueEq (j - max n m) w_B v3 :=
        valueEq_mono (j - max n m) (j - max p_B' m)
          (Nat.sub_le_sub_left hmax_pB'm_le_M j) _ _ hve23
      exact valueEq_trans (j - max n m) v1 w_B v3 hve12' hve23'
    | k + 1, .VConstr _ _, .VConstr _ _, .VConstr _ _, h12, h23 => by
      unfold ValueEq at h12 h23 ⊢
      exact ⟨h12.1.trans h23.1, listValueEq_trans k _ _ _ h12.2 h23.2⟩
    | k + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, .VBuiltin _ _ _, h12, h23 => by
      unfold ValueEq at h12 h23 ⊢
      exact ⟨h12.1.trans h23.1,
             listValueEq_trans (k + 1) _ _ _ h12.2.1 h23.2.1,
             h12.2.2.trans h23.2.2⟩
    -- Impossible: v₁, v₂ different constructors
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
    -- Impossible: v₂, v₃ different constructors
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
  termination_by k v _ _ _ _ => (k, sizeOf v)
  theorem listValueEq_trans : ∀ (k : Nat) (vs₁ vs₂ vs₃ : List CekValue),
      ListValueEq k vs₁ vs₂ → ListValueEq k vs₂ vs₃ → ListValueEq k vs₁ vs₃
    | _, [], [], [], _, _ => by simp [ListValueEq]
    | k, _ :: _, _ :: _, _ :: _, h12, h23 => by
      simp only [ListValueEq] at h12 h23 ⊢
      exact ⟨valueEq_trans k _ _ _ h12.1 h23.1,
             listValueEq_trans k _ _ _ h12.2 h23.2⟩
    | _, [], _ :: _, _, h, _ | _, _ :: _, [], _, h, _ => by simp [ListValueEq] at h
    | _, [], [], _ :: _, _, h => by simp [ListValueEq] at h
    | _, _ :: _, _ :: _, [], _, h => by simp [ListValueEq] at h
  termination_by k vs _ _ _ _ => (k, sizeOf vs)
end

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
