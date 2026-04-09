import Moist.Verified.Semantics

/-! # `ValueEq` mono/symm + parametric relation helpers

This file contains the "easy" metatheory of `ValueEq` — monotonicity and
symmetry — plus the parametric helpers over `EnvEqR`, `StackEqR`, `FrameEqR`,
and `ListR` (refl/symm/implication lifts).

Neither mono nor symm depends on reflexivity, so this file has no import
cycle with the downstream `ValueEq.lean` module (which defines
`valueEq_refl`/`valueEq_trans`/`stateEq_stateRelated`).

The reason for the split: `valueEq_refl` for VLam/VDelay requires the
**fundamental lemma** of the logical relation, whose proof needs the full
bisimulation machinery. That infrastructure lives in `ValueEq.lean`, which
imports this file. -/

namespace Moist.Verified.Semantics

open Moist.CEK
open Moist.Plutus.Term (Term Const)

/-! ## Parametric helpers on `EnvEqR`, `StackEqR`, `FrameEqR`, `ListR`

These are generic over the underlying value relation `R`. Instantiated
later with `R := ValueEq k` to derive refl/symm/mono on the concrete
`StackEq k` / `EnvEq k` / `FrameEq k`. -/

theorem envEqR_symm {R : CekValue → CekValue → Prop}
    (hR : ∀ v₁ v₂, R v₁ v₂ → R v₂ v₁) :
    ∀ e₁ e₂, EnvEqR R e₁ e₂ → EnvEqR R e₂ e₁
  | .nil, .nil, _ => trivial
  | .cons v1 e1, .cons v2 e2, h => ⟨hR v1 v2 h.1, envEqR_symm hR e1 e2 h.2⟩
  | .nil, .cons _ _, h => absurd h (by simp [EnvEqR])
  | .cons _ _, .nil, h => absurd h (by simp [EnvEqR])

theorem listR_symm {R : CekValue → CekValue → Prop}
    (hR : ∀ v₁ v₂, R v₁ v₂ → R v₂ v₁) :
    ∀ l₁ l₂, ListR R l₁ l₂ → ListR R l₂ l₁
  | [], [], _ => trivial
  | a :: as, b :: bs, h => ⟨hR a b h.1, listR_symm hR as bs h.2⟩
  | [], _ :: _, h => absurd h (by simp [ListR])
  | _ :: _, [], h => absurd h (by simp [ListR])

theorem frameEqR_symm {R : CekValue → CekValue → Prop}
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

theorem stackEqR_symm {R : CekValue → CekValue → Prop}
    (hR : ∀ v₁ v₂, R v₁ v₂ → R v₂ v₁) :
    ∀ s₁ s₂, StackEqR R s₁ s₂ → StackEqR R s₂ s₁
  | [], [], _ => trivial
  | f1 :: s1, f2 :: s2, h => ⟨frameEqR_symm hR f1 f2 h.1, stackEqR_symm hR s1 s2 h.2⟩
  | [], _ :: _, h => absurd h (by simp [StackEqR])
  | _ :: _, [], h => absurd h (by simp [StackEqR])

theorem envEqR_refl {R : CekValue → CekValue → Prop}
    (hR : ∀ v, R v v) :
    ∀ e, EnvEqR R e e
  | .nil => trivial
  | .cons v e => ⟨hR v, envEqR_refl hR e⟩

theorem listR_refl {R : CekValue → CekValue → Prop}
    (hR : ∀ v, R v v) :
    ∀ l, ListR R l l
  | [] => trivial
  | a :: as => ⟨hR a, listR_refl hR as⟩

theorem frameEqR_refl {R : CekValue → CekValue → Prop}
    (hR : ∀ v, R v v)
    (f : Frame) : FrameEqR R f f := by
  cases f with
  | force => trivial
  | arg t env => exact ⟨rfl, envEqR_refl hR env⟩
  | funV v => exact hR v
  | applyArg v => exact hR v
  | constrField tag done todo env => exact ⟨rfl, rfl, listR_refl hR done, envEqR_refl hR env⟩
  | caseScrutinee alts env => exact ⟨rfl, envEqR_refl hR env⟩

theorem stackEqR_refl {R : CekValue → CekValue → Prop}
    (hR : ∀ v, R v v) :
    ∀ s, StackEqR R s s
  | [] => trivial
  | f :: s => ⟨frameEqR_refl hR f, stackEqR_refl hR s⟩

/-! ### Relation-implication helpers

Given a pointwise implication `R₁ → R₂` on values, lift it to `EnvEqR`,
`ListR`, `FrameEqR`, and `StackEqR`. Used with `R₁ := ValueEq k`,
`R₂ := ValueEq j` (for `j ≤ k` via `valueEq_mono`) to downgrade
a stack/environment relation to a lower step index. -/

theorem envEqR_implication {R₁ R₂ : CekValue → CekValue → Prop}
    (h : ∀ v₁ v₂, R₁ v₁ v₂ → R₂ v₁ v₂) :
    ∀ e₁ e₂, EnvEqR R₁ e₁ e₂ → EnvEqR R₂ e₁ e₂
  | .nil, .nil, _ => trivial
  | .cons _ e1, .cons _ e2, hh => ⟨h _ _ hh.1, envEqR_implication h e1 e2 hh.2⟩
  | .nil, .cons _ _, hh => absurd hh (by simp [EnvEqR])
  | .cons _ _, .nil, hh => absurd hh (by simp [EnvEqR])

theorem listR_implication {R₁ R₂ : CekValue → CekValue → Prop}
    (h : ∀ v₁ v₂, R₁ v₁ v₂ → R₂ v₁ v₂) :
    ∀ l₁ l₂, ListR R₁ l₁ l₂ → ListR R₂ l₁ l₂
  | [], [], _ => trivial
  | _ :: as, _ :: bs, hh => ⟨h _ _ hh.1, listR_implication h as bs hh.2⟩
  | [], _ :: _, hh => absurd hh (by simp [ListR])
  | _ :: _, [], hh => absurd hh (by simp [ListR])

theorem frameEqR_implication {R₁ R₂ : CekValue → CekValue → Prop}
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

theorem stackEqR_implication {R₁ R₂ : CekValue → CekValue → Prop}
    (h : ∀ v₁ v₂, R₁ v₁ v₂ → R₂ v₁ v₂) :
    ∀ s₁ s₂, StackEqR R₁ s₁ s₂ → StackEqR R₂ s₁ s₂
  | [], [], _ => trivial
  | f1 :: s1, f2 :: s2, hh =>
      ⟨frameEqR_implication h f1 f2 hh.1, stackEqR_implication h s1 s2 hh.2⟩
  | [], _ :: _, hh => absurd hh (by simp [StackEqR])
  | _ :: _, [], hh => absurd hh (by simp [StackEqR])

/-! ## Symmetry of `ValueEq` / `ListValueEq`

Does not depend on `valueEq_refl` — just a structural flip of the 3-conjunct
VLam/VDelay clause via `stackEqR_symm` and `Nat.max_comm`. -/

mutual
  theorem valueEq_symm : ∀ (k : Nat) (v₁ v₂ : CekValue), ValueEq k v₁ v₂ → ValueEq k v₂ v₁
    | 0, _, _, _ => by simp [ValueEq]
    | _ + 1, .VCon _, .VCon _, h => by simp only [ValueEq] at h ⊢; exact h.symm
    | k + 1, .VLam _ _, .VLam _ _, h => by
      unfold ValueEq at h ⊢
      intro j hj arg1 arg2 hargs stk1 stk2 hstk n m hn hm
      have hargs' := valueEq_symm j _ _ hargs
      have hstk' := stackEqR_symm (valueEq_symm j) stk1 stk2 hstk
      -- Invoke the swapped clause at (m, n)
      have hswap := h j hj arg2 arg1 hargs' stk2 stk1 hstk' m n hm hn
      refine ⟨?_, ?_, ?_⟩
      · -- ¬(halt side1 ∧ err side2)  ←  ¬(err side1' ∧ halt side2')
        rintro ⟨v, hs1, hs2⟩
        exact hswap.2.1 ⟨hs2, v, hs1⟩
      · -- ¬(err side1 ∧ halt side2)  ←  ¬(halt side1' ∧ err side2')
        rintro ⟨hs1, v, hs2⟩
        exact hswap.1 ⟨v, hs2, hs1⟩
      · intro v1 v2 hv1 hv2
        have hr := hswap.2.2 v2 v1 hv2 hv1
        have hmax : max m n = max n m := Nat.max_comm m n
        rw [hmax] at hr
        exact valueEq_symm (j - max n m) _ _ hr
    | k + 1, .VDelay _ _, .VDelay _ _, h => by
      unfold ValueEq at h ⊢
      intro j hj stk1 stk2 hstk n m hn hm
      have hstk' := stackEqR_symm (valueEq_symm j) stk1 stk2 hstk
      have hswap := h j hj stk2 stk1 hstk' m n hm hn
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨v, hs1, hs2⟩
        exact hswap.2.1 ⟨hs2, v, hs1⟩
      · rintro ⟨hs1, v, hs2⟩
        exact hswap.1 ⟨v, hs2, hs1⟩
      · intro v1 v2 hv1 hv2
        have hr := hswap.2.2 v2 v1 hv2 hv1
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
end

/-! ## Monotonicity of `ValueEq` / `ListValueEq`

`ValueEq` is anti-monotone in the step index: larger observation budget ⇒
stronger relation, so we can always downgrade. -/

mutual
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

end Moist.Verified.Semantics
