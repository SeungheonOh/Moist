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
    (∀ n, n ≤ j →
      steps n (.compute stk1 (env.extend arg1) body) = .error →
      ∃ m, m ≤ j ∧ steps m (.compute stk2 (env.extend arg2) body) = .error) ∧
    (∀ v1 n, n ≤ j →
      steps n (.compute stk1 (env.extend arg1) body) = .halt v1 →
      ∃ v2 m, m ≤ j ∧ steps m (.compute stk2 (env.extend arg2) body) = .halt v2 ∧
        ValueEq (j - n) v1 v2) ∧
    (∀ n, n ≤ j →
      steps n (.compute stk2 (env.extend arg2) body) = .error →
      ∃ m, m ≤ j ∧ steps m (.compute stk1 (env.extend arg1) body) = .error) ∧
    (∀ v2 n, n ≤ j →
      steps n (.compute stk2 (env.extend arg2) body) = .halt v2 →
      ∃ v1 m, m ≤ j ∧ steps m (.compute stk1 (env.extend arg1) body) = .halt v1 ∧
        ValueEq (j - n) v1 v2) := by
  sorry

/-- The fundamental lemma for VDelay: same body and env, related stacks.
    Parallel to `fundemental_lemma` but without argument extension. -/
theorem fundemental_lemma_delay (j : Nat)
    (veq_refl : ∀ i, i ≤ j → ∀ v : CekValue, ValueEq i v v)
    (body : Term) (env : CekEnv)
    (stk1 stk2 : Stack) (hstk : StackEqR (ValueEq j) stk1 stk2) :
    (∀ n, n ≤ j →
      steps n (.compute stk1 env body) = .error →
      ∃ m, m ≤ j ∧ steps m (.compute stk2 env body) = .error) ∧
    (∀ v1 n, n ≤ j →
      steps n (.compute stk1 env body) = .halt v1 →
      ∃ v2 m, m ≤ j ∧ steps m (.compute stk2 env body) = .halt v2 ∧
        ValueEq (j - n) v1 v2) ∧
    (∀ n, n ≤ j →
      steps n (.compute stk2 env body) = .error →
      ∃ m, m ≤ j ∧ steps m (.compute stk1 env body) = .error) ∧
    (∀ v2 n, n ≤ j →
      steps n (.compute stk2 env body) = .halt v2 →
      ∃ v1 m, m ≤ j ∧ steps m (.compute stk1 env body) = .halt v1 ∧
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
      have ⟨hfe, hfh, hbe, hbh⟩ := h j hj arg2 arg1 hargs' stk2 stk1 hstk'
      exact ⟨fun n hn he => let ⟨m, hm, hme⟩ := hbe n hn he; ⟨m, hm, hme⟩,
             fun v1 n hn hv1 => let ⟨v2, m, hm, hv2, hve⟩ := hbh v1 n hn hv1;
               ⟨v2, m, hm, hv2, valueEq_symm (j - n) _ _ hve⟩,
             fun n hn he => let ⟨m, hm, hme⟩ := hfe n hn he; ⟨m, hm, hme⟩,
             fun v2 n hn hv2 => let ⟨v1, m, hm, hv1, hve⟩ := hfh v2 n hn hv2;
               ⟨v1, m, hm, hv1, valueEq_symm (j - n) _ _ hve⟩⟩
    | k + 1, .VDelay _ _, .VDelay _ _, h => by
      unfold ValueEq at h ⊢; intro j hj stk1 stk2 hstk
      have hstk' := stackEqR_symm (valueEq_symm j) stk1 stk2 hstk
      have ⟨hfe, hfh, hbe, hbh⟩ := h j hj stk2 stk1 hstk'
      exact ⟨fun n hn he => let ⟨m, hm, hme⟩ := hbe n hn he; ⟨m, hm, hme⟩,
             fun v1 n hn hv1 => let ⟨v2, m, hm, hv2, hve⟩ := hbh v1 n hn hv1;
               ⟨v2, m, hm, hv2, valueEq_symm (j - n) _ _ hve⟩,
             fun n hn he => let ⟨m, hm, hme⟩ := hfe n hn he; ⟨m, hm, hme⟩,
             fun v2 n hn hv2 => let ⟨v1, m, hm, hv1, hve⟩ := hfh v2 n hn hv2;
               ⟨v1, m, hm, hv1, valueEq_symm (j - n) _ _ hve⟩⟩
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

/-! ## Transitivity under ∀ k

Pointwise `valueEq_trans k` for VLam/VDelay has a level mismatch when
intermediate step counts differ. With `∀ n` on both inputs, we pick
levels high enough: use h12 with actual args to get `w2, m12`, then h23
at level `j-n+m12+2` with refl args to get `ValueEq (j-n) w2 w3`,
identify w3 by `reaches_unique`, and recurse at `j-n < k+1`. -/

mutual
  theorem valueEqAll_trans : ∀ (k : Nat) (v₁ v₂ v₃ : CekValue),
      (∀ n, ValueEq n v₁ v₂) → (∀ n, ValueEq n v₂ v₃) →
      ValueEq k v₁ v₃
    | 0, _, _, _, _, _ => by simp [ValueEq]
    | _ + 1, .VCon _, .VCon _, .VCon _, h12_all, h23_all => by
      have h12 := h12_all 2; have h23 := h23_all 2
      simp only [ValueEq] at h12 h23 ⊢; exact h12.trans h23
    | k + 1, .VLam body1 env1, .VLam body2 env2, .VLam body3 env3, h12_all, h23_all => by
      unfold ValueEq; intro j hj arg1 arg3 hargs13 stk1 stk3 hstk13
      -- h12 with ACTUAL args → middle = compute stk3 (env2.extend arg3) body2
      have h12v := h12_all (j + 2); unfold ValueEq at h12v
      have ⟨hfe12, hfh12, hbe12, hbh12⟩ :=
        h12v j (by omega) arg1 arg3 hargs13 stk1 stk3 hstk13
      -- h23 with REFL args (arg3,arg3) stks (stk3,stk3) at level j+2
      -- → side1 = compute stk3 (env2.extend arg3) body2 (= h12's middle)
      -- → side3 = compute stk3 (env3.extend arg3) body3 (= conclusion's side3)
      have h23v_j := h23_all (j + 2); unfold ValueEq at h23v_j
      have ⟨hfe23, hfh23, hbe23, hbh23⟩ :=
        h23v_j j (by omega) arg3 arg3 (valueEq_refl j arg3)
          stk3 stk3 (stackEqR_refl (valueEq_refl j) stk3)
      refine ⟨fun n hn he => ?_, fun v1 n hn hv1 => ?_,
              fun n hn he => ?_, fun v3 n hn hv3 => ?_⟩
      · -- Forward error: chain h12 → h23
        obtain ⟨m12, hm12, he12⟩ := hfe12 n hn he
        obtain ⟨m23, hm23, he23⟩ := hfe23 m12 hm12 he12
        exact ⟨m23, hm23, he23⟩
      · -- Forward halt: the key case
        obtain ⟨w2, m12, hm12, hw2, hve12⟩ := hfh12 v1 n hn hv1
        -- w3, m23 from h23 at level j (for ∃ m ≤ j witness)
        obtain ⟨w3, m23, hm23, hw3, _⟩ := hfh23 w2 m12 hm12 hw2
        -- ValueEq (j-n) w2 w3 from h23 at HIGH level j-n+m12+2, refl args
        have h23_hi := h23_all (j - n + m12 + 2); unfold ValueEq at h23_hi
        have ⟨_, hfh23_hi, _, _⟩ :=
          h23_hi (j - n + m12) (by omega) arg3 arg3
            (valueEq_refl (j - n + m12) arg3) stk3 stk3
            (stackEqR_refl (valueEq_refl (j - n + m12)) stk3)
        obtain ⟨w3', _, _, hw3', hve23'⟩ := hfh23_hi w2 m12 (by omega) hw2
        have hve23 : ValueEq (j - n) w2 w3 := by
          have := reaches_unique ⟨_, hw3'⟩ ⟨m23, hw3⟩; subst this
          have : j - n + m12 - m12 = j - n := by omega
          rw [this] at hve23'; exact hve23'
        -- Build ∀ K for v1-w2: from h12_all at level K+n+2, actual args
        -- NOTE: sorry for args/StackEqR mono (can't upgrade ValueEq j / StackEqR j to level K+n)
        have hw12_all : ∀ K, ValueEq K v1 w2 := by
          intro K
          have h12K := h12_all (K + n + 2); unfold ValueEq at h12K
          have ⟨_, hfhK, _, _⟩ :=
            h12K (K + n) (by omega) arg1 arg3
              (sorry) -- ValueEq (K+n) arg1 arg3: can't mono up from level j
              stk1 stk3 (sorry) -- StackEqR mono: can't upgrade from level j
          obtain ⟨w2', _, _, hw2', hveK⟩ := hfhK v1 n (by omega) hv1
          have := reaches_unique ⟨_, hw2'⟩ ⟨m12, hw2⟩; subst this
          have hsub : K + n - n = K := by omega
          rw [hsub] at hveK; exact hveK
        -- Build ∀ K for w2-w3: from h23_all at level K+m12+2, refl args
        have hw23_all : ∀ K, ValueEq K w2 w3 := by
          intro K
          have h23K := h23_all (K + m12 + 2); unfold ValueEq at h23K
          have ⟨_, hfhK, _, _⟩ :=
            h23K (K + m12) (by omega) arg3 arg3
              (valueEq_refl (K + m12) arg3) stk3 stk3
              (stackEqR_refl (valueEq_refl (K + m12)) stk3)
          obtain ⟨w3', _, _, hw3', hveK⟩ := hfhK w2 m12 (by omega) hw2
          have := reaches_unique ⟨_, hw3'⟩ ⟨m23, hw3⟩; subst this
          have hsub : K + m12 - m12 = K := by omega
          rw [hsub] at hveK; exact hveK
        -- Recurse at j-n < k+1
        exact ⟨w3, m23, hm23, hw3, valueEqAll_trans (j - n) v1 w2 w3 hw12_all hw23_all⟩
      · -- Backward error: chain h23 → h12
        obtain ⟨m23, hm23, he23⟩ := hbe23 n hn he
        obtain ⟨m12, hm12, he12⟩ := hbe12 m23 hm23 he23
        exact ⟨m12, hm12, he12⟩
      · -- Backward halt: symmetric to forward
        -- Get w2 from h23 backward (refl args): side2=stk3/env3/body3 → side1=stk3/env2/body2
        obtain ⟨w2, m23, hm23, hw2, _⟩ := hbh23 v3 n hn hv3
        -- Get w1 from h12 backward (actual args): side2=stk3/env2/body2 → side1=stk1/env1/body1
        obtain ⟨w1, m12, hm12, hw1, _⟩ := hbh12 w2 m23 hm23 hw2
        -- ValueEq (j-n) w1 w2 from h12 at HIGH level j-n+m23+2, backward, actual args
        have h12_hi := h12_all (j - n + m23 + 2); unfold ValueEq at h12_hi
        have ⟨_, _, _, hbh12_hi⟩ :=
          h12_hi (j - n + m23) (by omega) arg1 arg3
            (sorry) -- args mono: can't mono up from level j
            stk1 stk3 (sorry) -- StackEqR mono
        obtain ⟨w1', _, _, hw1', hve12'⟩ := hbh12_hi w2 m23 (by omega) hw2
        have hve12 : ValueEq (j - n) w1 w2 := by
          have := reaches_unique ⟨_, hw1'⟩ ⟨m12, hw1⟩; subst this
          have : j - n + m23 - m23 = j - n := by omega
          rw [this] at hve12'; exact hve12'
        -- Build ∀ K for w1-w2: h12 backward at level K+m23+2, actual args
        -- NOTE: sorry for args/StackEqR mono (same as forward case)
        have hw12_all : ∀ K, ValueEq K w1 w2 := by
          intro K
          have h12K := h12_all (K + m23 + 2); unfold ValueEq at h12K
          have ⟨_, _, _, hbhK⟩ :=
            h12K (K + m23) (by omega) arg1 arg3
              (sorry) -- ValueEq (K+m23) arg1 arg3: can't mono up from level j
              stk1 stk3 (sorry) -- StackEqR mono: can't upgrade from level j
          obtain ⟨w1', _, _, hw1', hveK⟩ := hbhK w2 m23 (by omega) hw2
          have := reaches_unique ⟨_, hw1'⟩ ⟨m12, hw1⟩; subst this
          have hsub : K + m23 - m23 = K := by omega
          rw [hsub] at hveK; exact hveK
        -- Build ∀ K for w2-v3: h23 backward at level K+n+2, refl args
        have hw23_all : ∀ K, ValueEq K w2 v3 := by
          intro K
          have h23K := h23_all (K + n + 2); unfold ValueEq at h23K
          have ⟨_, _, _, hbhK⟩ :=
            h23K (K + n) (by omega) arg3 arg3
              (valueEq_refl (K + n) arg3) stk3 stk3
              (stackEqR_refl (valueEq_refl (K + n)) stk3)
          obtain ⟨w2', _, _, hw2', hveK⟩ := hbhK v3 n (by omega) hv3
          have := reaches_unique ⟨_, hw2'⟩ ⟨m23, hw2⟩; subst this
          have hsub : K + n - n = K := by omega
          rw [hsub] at hveK; exact hveK
        -- Recurse at j-n < k+1
        exact ⟨w1, m12, hm12, hw1, valueEqAll_trans (j - n) w1 w2 v3 hw12_all hw23_all⟩
    | k + 1, .VDelay body1 env1, .VDelay body2 env2, .VDelay body3 env3, h12_all, h23_all => by
      unfold ValueEq; intro j hj stk1 stk3 hstk13
      -- h12 with actual stks at level j+2
      have h12v := h12_all (j + 2); unfold ValueEq at h12v
      have ⟨hfe12, hfh12, hbe12, hbh12⟩ := h12v j (by omega) stk1 stk3 hstk13
      -- h23 with refl stks (stk3,stk3) at level j+2
      have h23v := h23_all (j + 2); unfold ValueEq at h23v
      have ⟨hfe23, hfh23, hbe23, hbh23⟩ :=
        h23v j (by omega) stk3 stk3 (stackEqR_refl (valueEq_refl j) stk3)
      refine ⟨fun n hn he => ?_, fun v1 n hn hv1 => ?_,
              fun n hn he => ?_, fun v3 n hn hv3 => ?_⟩
      · -- Forward error
        obtain ⟨m12, hm12, he12⟩ := hfe12 n hn he
        obtain ⟨m23, hm23, he23⟩ := hfe23 m12 hm12 he12
        exact ⟨m23, hm23, he23⟩
      · -- Forward halt
        obtain ⟨w2, m12, hm12, hw2, hve12⟩ := hfh12 v1 n hn hv1
        obtain ⟨w3, m23, hm23, hw3, _⟩ := hfh23 w2 m12 hm12 hw2
        -- ValueEq (j-n) w2 w3 from h23 at HIGH level
        have h23_hi := h23_all (j - n + m12 + 2); unfold ValueEq at h23_hi
        have ⟨_, hfh23_hi, _, _⟩ :=
          h23_hi (j - n + m12) (by omega) stk3 stk3
            (stackEqR_refl (valueEq_refl (j - n + m12)) stk3)
        obtain ⟨w3', _, _, hw3', hve23'⟩ := hfh23_hi w2 m12 (by omega) hw2
        have hve23 : ValueEq (j - n) w2 w3 := by
          have := reaches_unique ⟨_, hw3'⟩ ⟨m23, hw3⟩; subst this
          have : j - n + m12 - m12 = j - n := by omega
          rw [this] at hve23'; exact hve23'
        -- Build ∀ K for w1-w2: h12 forward at level K+n+2, actual stks
        -- NOTE: sorry for StackEqR mono (can't upgrade from level j to K+n)
        have hw12_all : ∀ K, ValueEq K v1 w2 := by
          intro K
          have h12K := h12_all (K + n + 2); unfold ValueEq at h12K
          have ⟨_, hfhK, _, _⟩ :=
            h12K (K + n) (by omega)
              stk1 stk3 (sorry) -- StackEqR mono: can't upgrade from level j
          obtain ⟨w2', _, _, hw2', hveK⟩ := hfhK v1 n (by omega) hv1
          have := reaches_unique ⟨_, hw2'⟩ ⟨m12, hw2⟩; subst this
          have hsub : K + n - n = K := by omega
          rw [hsub] at hveK; exact hveK
        -- Build ∀ K for w2-w3: h23 forward at level K+m12+2, refl stks
        have hw23_all : ∀ K, ValueEq K w2 w3 := by
          intro K
          have h23K := h23_all (K + m12 + 2); unfold ValueEq at h23K
          have ⟨_, hfhK, _, _⟩ :=
            h23K (K + m12) (by omega) stk3 stk3
              (stackEqR_refl (valueEq_refl (K + m12)) stk3)
          obtain ⟨w3', _, _, hw3', hveK⟩ := hfhK w2 m12 (by omega) hw2
          have := reaches_unique ⟨_, hw3'⟩ ⟨m23, hw3⟩; subst this
          have hsub : K + m12 - m12 = K := by omega
          rw [hsub] at hveK; exact hveK
        exact ⟨w3, m23, hm23, hw3, valueEqAll_trans (j - n) v1 w2 w3 hw12_all hw23_all⟩
      · -- Backward error
        obtain ⟨m23, hm23, he23⟩ := hbe23 n hn he
        obtain ⟨m12, hm12, he12⟩ := hbe12 m23 hm23 he23
        exact ⟨m12, hm12, he12⟩
      · -- Backward halt
        obtain ⟨w2, m23, hm23, hw2, _⟩ := hbh23 v3 n hn hv3
        obtain ⟨w1, m12, hm12, hw1, _⟩ := hbh12 w2 m23 hm23 hw2
        -- ValueEq (j-n) w1 w2 from h12 at HIGH level, backward
        have h12_hi := h12_all (j - n + m23 + 2); unfold ValueEq at h12_hi
        have ⟨_, _, _, hbh12_hi⟩ :=
          h12_hi (j - n + m23) (by omega)
            stk1 stk3 (sorry) -- StackEqR mono
        obtain ⟨w1', _, _, hw1', hve12'⟩ := hbh12_hi w2 m23 (by omega) hw2
        have hve12 : ValueEq (j - n) w1 w2 := by
          have := reaches_unique ⟨_, hw1'⟩ ⟨m12, hw1⟩; subst this
          have : j - n + m23 - m23 = j - n := by omega
          rw [this] at hve12'; exact hve12'
        -- Build ∀ K for w1-w2: h12 backward at level K+m23+2, actual stks
        have hw12_all : ∀ K, ValueEq K w1 w2 := by
          intro K
          have h12K := h12_all (K + m23 + 2); unfold ValueEq at h12K
          have ⟨_, _, _, hbhK⟩ :=
            h12K (K + m23) (by omega)
              stk1 stk3 (sorry) -- StackEqR mono
          obtain ⟨w1', _, _, hw1', hveK⟩ := hbhK w2 m23 (by omega) hw2
          have := reaches_unique ⟨_, hw1'⟩ ⟨m12, hw1⟩; subst this
          have hsub : K + m23 - m23 = K := by omega
          rw [hsub] at hveK; exact hveK
        -- Build ∀ K for w2-v3: h23 backward at level K+n+2, refl stks
        have hw23_all : ∀ K, ValueEq K w2 v3 := by
          intro K
          have h23K := h23_all (K + n + 2); unfold ValueEq at h23K
          have ⟨_, _, _, hbhK⟩ :=
            h23K (K + n) (by omega) stk3 stk3
              (stackEqR_refl (valueEq_refl (K + n)) stk3)
          obtain ⟨w2', _, _, hw2', hveK⟩ := hbhK v3 n (by omega) hv3
          have := reaches_unique ⟨_, hw2'⟩ ⟨m23, hw2⟩; subst this
          have hsub : K + n - n = K := by omega
          rw [hsub] at hveK; exact hveK
        exact ⟨w1, m12, hm12, hw1, valueEqAll_trans (j - n) w1 w2 v3 hw12_all hw23_all⟩
    | k + 1, .VConstr _ _, .VConstr _ _, .VConstr _ _, h12_all, h23_all => by
      have h12 := h12_all 2; have h23 := h23_all 2
      unfold ValueEq at h12 h23 ⊢
      exact ⟨h12.1.trans h23.1,
        listValueEqAll_trans k _ _ _
          (fun n => by have h := h12_all (n + 1); unfold ValueEq at h; exact h.2)
          (fun n => by have h := h23_all (n + 1); unfold ValueEq at h; exact h.2)⟩
    | k + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, .VBuiltin _ _ _, h12_all, h23_all => by
      have h12 := h12_all 2; have h23 := h23_all 2
      unfold ValueEq at h12 h23 ⊢
      exact ⟨h12.1.trans h23.1,
        listValueEqAll_trans (_ + 1) _ _ _
          (fun n => by
            cases n with
            | zero =>
              have h1 := h12_all 1; unfold ValueEq at h1
              exact listValueEq_mono 0 1 (by omega) _ _ h1.2.1
            | succ n => have h := h12_all (n + 1); unfold ValueEq at h; exact h.2.1)
          (fun n => by
            cases n with
            | zero =>
              have h1 := h23_all 1; unfold ValueEq at h1
              exact listValueEq_mono 0 1 (by omega) _ _ h1.2.1
            | succ n => have h := h23_all (n + 1); unfold ValueEq at h; exact h.2.1),
        h12.2.2.trans h23.2.2⟩
    -- Impossible: v1 v2 different constructors (use h12_all 1)
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
    | _ + 1, .VBuiltin _ _ _, .VConstr _ _, _, h, _ => by
      have := h 1; simp [ValueEq] at this
    -- Impossible: v2 v3 different constructors (use h23_all 1)
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
    | _ + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, .VConstr _ _, _, h => by
      have := h 1; simp [ValueEq] at this
  theorem listValueEqAll_trans : ∀ (k : Nat) (vs₁ vs₂ vs₃ : List CekValue),
      (∀ n, ListValueEq n vs₁ vs₂) → (∀ n, ListValueEq n vs₂ vs₃) →
      ListValueEq k vs₁ vs₃
    | _, [], [], [], _, _ => by simp [ListValueEq]
    | _, [], _ :: _, _, h, _ => by have := h 0; simp [ListValueEq] at this
    | _, _ :: _, [], _, h, _ => by have := h 0; simp [ListValueEq] at this
    | _, [], [], _ :: _, _, h => by have := h 0; simp [ListValueEq] at this
    | _, _ :: _, _ :: _, [], _, h => by have := h 0; simp [ListValueEq] at this
    | k, _ :: _, _ :: _, _ :: _, h12, h23 => by
      simp only [ListValueEq] at h12 h23 ⊢
      exact ⟨valueEqAll_trans k _ _ _ (fun n => (h12 n).1) (fun n => (h23 n).1),
             listValueEqAll_trans k _ _ _ (fun n => (h12 n).2) (fun n => (h23 n).2)⟩
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
      exact valueEqAll_trans k v₁ v₂ v₃ (fun n => hv12 n v₁ v₂ hv₁ hv₂) (fun n => hv23 n v₂ v₃ hv₂ hv₃)

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
      exact valueEqAll_trans k v₁ v₂ v₃ (fun n => hv12 n v₁ v₂ hv₁ hv₂) (fun n => hv23 n v₂ v₃ hv₂ hv₃)

/-- **Unconditional transitivity of refinement.** -/
theorem refines_trans {a b c : Expr}
    (h12 : Refines a b) (h23 : Refines b c) : Refines a c :=
  ⟨fun env ha => h23.1 env (h12.1 env ha),
   behEq_trans h12.1 h12.2 h23.2⟩

end Moist.Verified.Semantics
