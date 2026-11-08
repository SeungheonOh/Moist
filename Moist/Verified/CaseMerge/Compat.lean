import Moist.Verified.CaseMerge.Facts
import Moist.Verified.FundamentalRefinesWF

variable [sv : Moist.CEK.SemVariant]

/-! # Compatibility lemmas for the guarded logical relation

One lemma per term former (`eval_lam`, `eval_apply`, ...), the reflexive
case `eval_refl`, and `atomArgs_stackRel`: values pending as `applyArg`
frames on the left against atomic argument terms pending as `arg` frames on
the right.
-/

namespace Moist.Verified.CaseMerge

open Moist.CEK
open Moist.MIR
open Moist.Plutus.Term (Term)
open Moist.Verified (closedAt closedAtList renameTerm)
open Moist.Verified.Equivalence (steps Reaches steps_trans ListRel ObsRefinesK
  obsRefinesK_of_steps_left obsRefinesK_of_steps_right obsRefinesK_of_step_ret
  obsRefinesK_error_error listRel_mono)
open Moist.Verified.Contextual.Guarded

variable {W : Guard}

theorem envRel_mono {j k d : Nat} {ρ₁ ρ₂ : CekEnv} (hjk : j ≤ k) (h : EnvRel W k d ρ₁ ρ₂) :
    EnvRel W j d ρ₁ ρ₂ := fun n hn hnd =>
  let ⟨v₁, v₂, h₁, h₂, hv⟩ := h n hn hnd; ⟨v₁, v₂, h₁, h₂, valueRel_mono hjk hv⟩

theorem envRel_extend {k d : Nat} {ρ₁ ρ₂ : CekEnv} {a₁ a₂ : CekValue} (h : EnvRel W k d ρ₁ ρ₂)
    (ha : ValueRel W k a₁ a₂) : EnvRel W k (d + 1) (ρ₁.extend a₁) (ρ₂.extend a₂) := by
  intro n hn hnd
  match n with
  | 1 => exact ⟨a₁, a₂, rfl, rfl, ha⟩
  | m + 2 =>
    obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := h (m + 1) (by omega) (by omega)
    exact ⟨v₁, v₂, h₁, h₂, hv⟩

theorem envRel_zero (k : Nat) (ρ₁ ρ₂ : CekEnv) : EnvRel W k 0 ρ₁ ρ₂ :=
  fun _ hn hnd => absurd hnd (by omega)

/-- A closed term is related to itself. -/
theorem eval_refl {k d : Nat} {ρ₁ ρ₂ : CekEnv} {t : Term} (ht : closedAt d t = true)
    (h : EnvRel W k d ρ₁ ρ₂) : Eval W k ρ₁ ρ₂ t t := by
  have := FundamentalRefines.renameRefinesG W id id FundamentalRefines.is0preserving_id
    FundamentalRefines.is0preserving_id d t ht k (FundamentalRefines.renameEnvRef2_id h)
  rwa [Moist.Verified.renameTerm_id] at this

theorem eval_lam {k : Nat} {ρ₁ ρ₂ : CekEnv} {b₁ b₂ : Term} (n₁ n₂ : Nat)
    (h : ∀ j < k, ∀ a₁ a₂, ValueRel W j a₁ a₂ → W.V a₁ → W.V a₂ →
      Eval W j (ρ₁.extend a₁) (ρ₂.extend a₂) b₁ b₂) :
    Eval W k ρ₁ ρ₂ (.Lam n₁ b₁) (.Lam n₂ b₂) :=
  eval_of_step fun j hj _ _ hπ hst₁ hst₂ =>
    ret_obs (valueRel_lam (W.ret.mp hst₁).2 (W.ret.mp hst₂).2
      fun j' hj' a₁ a₂ ha ha₁ ha₂ => h j' (by omega) a₁ a₂ ha ha₁ ha₂) hst₁ hst₂ hπ

theorem eval_delay {k : Nat} {ρ₁ ρ₂ : CekEnv} {b₁ b₂ : Term} (h : Eval W k ρ₁ ρ₂ b₁ b₂) :
    Eval W k ρ₁ ρ₂ (.Delay b₁) (.Delay b₂) :=
  eval_of_step fun j hj _ _ hπ hst₁ hst₂ =>
    ret_obs (valueRel_delay (W.ret.mp hst₁).2 (W.ret.mp hst₂).2
      fun j' hj' => eval_mono (by omega) h) hst₁ hst₂ hπ

theorem eval_apply {k : Nat} {ρ₁ ρ₂ : CekEnv} {f₁ f₂ a₁ a₂ : Term}
    (hf : Eval W k ρ₁ ρ₂ f₁ f₂) (ha : Eval W k ρ₁ ρ₂ a₁ a₂) :
    Eval W k ρ₁ ρ₂ (.Apply f₁ a₁) (.Apply f₂ a₂) :=
  eval_of_step fun j hj _ _ hπ hst₁ hst₂ =>
    hf j (by omega) _ _ (arg_stackRel (eval_mono (by omega) ha) (W.compute hst₁)
      (W.compute hst₂) hπ) hst₁ hst₂

theorem eval_force {k : Nat} {ρ₁ ρ₂ : CekEnv} {e₁ e₂ : Term} (h : Eval W k ρ₁ ρ₂ e₁ e₂) :
    Eval W k ρ₁ ρ₂ (.Force e₁) (.Force e₂) :=
  eval_of_step fun j hj _ _ hπ hst₁ hst₂ =>
    h j (by omega) _ _ (force_stackRel hπ) hst₁ hst₂

theorem eval_constr {k : Nat} {ρ₁ ρ₂ : CekEnv} (tag : Nat) :
    ∀ {ms₁ ms₂ : List Term}, ListRel (Eval W k ρ₁ ρ₂) ms₁ ms₂ →
      Eval W k ρ₁ ρ₂ (.Constr tag ms₁) (.Constr tag ms₂)
  | [], [], _ => eval_of_step fun j _ _ _ hπ hst₁ hst₂ =>
      ret_obs (valueRel_constr (k := j) trivial) hst₁ hst₂ hπ
  | m₁ :: ms₁, m₂ :: ms₂, h => eval_of_step fun j hj _ _ hπ hst₁ hst₂ =>
      h.1 j (by omega) _ _ (constrField_stackRel
        (listRel_mono (fun _ _ h => eval_mono (by omega) h) h.2) trivial
        (W.compute hst₁) (W.compute hst₂) hπ) hst₁ hst₂
  | [], _ :: _, h => absurd h id
  | _ :: _, [], h => absurd h id

theorem eval_case {k : Nat} {ρ₁ ρ₂ : CekEnv} {s₁ s₂ : Term} {alts₁ alts₂ : List Term}
    (hs : Eval W k ρ₁ ρ₂ s₁ s₂) (ha : ListRel (Eval W k ρ₁ ρ₂) alts₁ alts₂) :
    Eval W k ρ₁ ρ₂ (.Case s₁ alts₁) (.Case s₂ alts₂) :=
  eval_of_step fun j hj _ _ hπ hst₁ hst₂ =>
    hs j (by omega) _ _ (case_stackRel (altsRel_of_listRel
        (listRel_mono (fun _ _ h => eval_mono (by omega) h) ha))
      (W.compute hst₁) (W.compute hst₂) hπ) hst₁ hst₂

omit sv in
theorem listRel_getElem? {α : Type} {R : α → α → Prop} :
    ∀ {xs ys : List α}, ListRel R xs ys → ∀ {n : Nat} {x y : α},
      xs[n]? = some x → ys[n]? = some y → R x y
  | a :: as, b :: bs, h, 0, x, y, hx, hy => by
    simp at hx hy; subst hx; subst hy; exact h.1
  | a :: as, b :: bs, h, n + 1, x, y, hx, hy => by
    simp at hx hy; exact listRel_getElem? h.2 hx hy
  | [], [], _, _, _, _, hx, _ => by simp at hx
  | [], _ :: _, h, _, _, _, _, _ => absurd h id
  | _ :: _, [], h, _, _, _, _, _ => absurd h id

omit sv in
theorem listRel_length {α : Type} {R : α → α → Prop} :
    ∀ {xs ys : List α}, ListRel R xs ys → xs.length = ys.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [listRel_length h.2]
  | [], _ :: _, h => absurd h id
  | _ :: _, [], h => absurd h id

/-! ## Pending arguments -/

private theorem step_applyArg' (v w : CekValue) (π : Stack) :
    step (.ret (.applyArg v :: π) w) = step (.ret (.funV w :: π) v) := by
  cases w <;> rfl

/-- Applied values on the left against atomic arguments, evaluated on the
    right in one step each, to related values. -/
theorem atomArgs_stackRel {ρ₂ : CekEnv} :
    ∀ {k : Nat} {vs ws : List CekValue} {ts : List Term} {π₁ π₂ : Stack},
      ListRel (ValueRel W k) vs ws →
      ListRel2 (fun t w => ∀ π, step (.compute π ρ₂ t) = .ret π w) ts ws →
      (∀ w ∈ ws, W.V w) →
      W.S (vs.map Frame.applyArg ++ π₁) → W.S (ts.map (fun t => Frame.arg t ρ₂) ++ π₂) →
      StackRel W k π₁ π₂ →
      StackRel W k (vs.map Frame.applyArg ++ π₁) (ts.map (fun t => Frame.arg t ρ₂) ++ π₂)
  | _, [], [], [], _, _, _, _, _, _, _, hπ => hπ
  | k, v :: vs, w :: ws, t :: ts, π₁, π₂, hvw, hts, hV, hs₁, hs₂, hπ => by
    simp only [List.map_cons, List.cons_append] at hs₁ hs₂ ⊢
    have hrest := atomArgs_stackRel hvw.2 hts.2 (fun u hu => hV u (.tail _ hu))
      (W.tail hs₁) (W.tail hs₂) hπ
    refine ⟨hs₁, hs₂, fun j hj f₁ f₂ hf hf₁ hf₂ => ?_⟩
    match j with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | j + 1 =>
      have hR : steps 2 (.ret (.arg t ρ₂ :: (ts.map (fun t => Frame.arg t ρ₂) ++ π₂)) f₂) =
          .ret (.funV f₂ :: (ts.map (fun t => Frame.arg t ρ₂) ++ π₂)) w := hts.1 _
      refine obsRefinesK_of_steps_right hR (obsRefinesK_of_step_ret ?_)
      rw [step_applyArg']
      exact app_obs hf (valueRel_mono (by omega) hvw.1)
        (W.ret.mpr ⟨W.funV hf₁ (W.tail hs₁), W.applyArg hs₁⟩)
        (W.ret.mpr ⟨W.funV hf₂ (W.tail hs₂), hV w (.head _)⟩)
        (stackRel_mono (by omega) hrest)
  | _, [], _ :: _, _, _, _, h, _, _, _, _, _ => absurd h id
  | _, _ :: _, [], _, _, _, h, _, _, _, _, _ => absurd h id
  | _, [], [], _ :: _, _, _, _, h, _, _, _, _ => absurd h id
  | _, _ :: _, _ :: _, [], _, _, _, h, _, _, _, _ => absurd h id

/-! ## Simple values in related environments -/

theorem atomEval_rel {env : List VarId} {ρ₁ ρ₂ : CekEnv} {k : Nat} {f : Expr} {v₁ : CekValue}
    (h : AtomEval env ρ₁ f v₁) (henv : EnvRel W k env.length ρ₁ ρ₂) :
    ∃ v₂, AtomEval env ρ₂ f v₂ ∧ ValueRel W k v₁ v₂ := by
  obtain ⟨ha, t, ht, hs⟩ := h
  rcases MIR.lowerTotal_atom_isLeafAtom env f t ha ht with ⟨n, hn, rfl⟩ | ⟨ct, rfl⟩ | ⟨b, rfl⟩
  · have hc := Moist.Verified.MIR.lowerTotalExpr_closedAt ht
    simp only [closedAt, decide_eq_true_eq] at hc
    obtain ⟨u₁, u₂, h₁, h₂, hu⟩ := henv n hn hc
    have h' := hs []
    simp only [step, h₁] at h'
    cases h'
    exact ⟨u₂, ⟨ha, _, ht, fun π => by simp only [step, h₂]⟩, hu⟩
  · obtain ⟨c, ty⟩ := ct
    have h' := hs []
    simp only [step] at h'
    cases h'
    exact ⟨_, ⟨ha, _, ht, fun _ => rfl⟩, valueRel_vcon k c⟩
  · have h' := hs []
    simp only [step] at h'
    cases h'
    exact ⟨_, ⟨ha, _, ht, fun _ => rfl⟩, valueRel_builtin (k := k) trivial⟩

theorem atomEvals_rel {env : List VarId} {ρ₁ ρ₂ : CekEnv} {k : Nat} :
    ∀ {fs : List Expr} {vs₁ : List CekValue}, ListRel2 (AtomEval env ρ₁) fs vs₁ →
      EnvRel W k env.length ρ₁ ρ₂ →
      ∃ vs₂, ListRel2 (AtomEval env ρ₂) fs vs₂ ∧ ListRel (ValueRel W k) vs₁ vs₂
  | [], [], _, _ => ⟨[], trivial, trivial⟩
  | f :: fs, v :: vs, h, henv => by
    obtain ⟨w, hw, hvw⟩ := atomEval_rel h.1 henv
    obtain ⟨ws, hws, hvws⟩ := atomEvals_rel h.2 henv
    exact ⟨w :: ws, ⟨hw, hws⟩, ⟨hvw, hvws⟩⟩
  | [], _ :: _, h, _ => absurd h id
  | _ :: _, [], h, _ => absurd h id

/-- The lowered fields step to the values recorded by `AtomEval`. -/
theorem atomEvals_steps {env : List VarId} {ρ : CekEnv} :
    ∀ {fs : List Expr} {vs : List CekValue} {ts : List Term},
      ListRel2 (AtomEval env ρ) fs vs → MIR.lowerTotalExprList env fs = some ts →
      ListRel2 (fun t w => ∀ π, step (.compute π ρ t) = .ret π w) ts vs
  | [], [], ts, _, hl => by rw [MIR.lowerTotalExprList_nil] at hl; cases hl; trivial
  | f :: fs, v :: vs, ts, h, hl => by
    rw [MIR.lowerTotalExprList_cons] at hl
    cases hf : lowerTotalExpr env f <;> cases hfs : MIR.lowerTotalExprList env fs <;>
      simp [hf, hfs] at hl
    subst hl
    obtain ⟨_, t, ht, hs⟩ := h.1
    rw [hf] at ht; cases ht
    exact ⟨hs, atomEvals_steps h.2 hfs⟩
  | [], _ :: _, _, h, _ => absurd h id
  | _ :: _, [], _, h, _ => absurd h id

theorem simpleVal_rel {env : List VarId} {ρ₁ ρ₂ : CekEnv} {k : Nat} {F : Expr} {v₁ : CekValue}
    {tF : Term} (h : SimpleVal env ρ₁ F v₁) (hl : lowerTotalExpr env F = some tF)
    (henv : EnvRel W k env.length ρ₁ ρ₂) :
    ∃ v₂, (∀ π, ∃ n, steps n (.compute π ρ₂ tF) = .ret π v₂) ∧ ValueRel W k v₁ v₂ := by
  rcases h with h | ⟨tag, fs, vs, rfl, rfl, hfs⟩
  · obtain ⟨v₂, ⟨_, t, ht, hs⟩, hv⟩ := atomEval_rel h henv
    rw [hl] at ht; cases ht
    exact ⟨v₂, fun π => ⟨1, hs π⟩, hv⟩
  · obtain ⟨ws, hws, hvws⟩ := atomEvals_rel hfs henv
    rw [MIR.lowerTotalExpr_constr_of_list] at hl
    cases hfl : MIR.lowerTotalExprList env fs with
    | none => rw [hfl] at hl; cases hl
    | some tfs =>
      rw [hfl] at hl; cases hl
      have hsteps := atomEvals_steps hws hfl
      have hret : ListRel2 (fun t v => ∀ π, ∃ n, steps n (.compute π ρ₂ t) = .ret π v) tfs ws := by
        clear hfl hws hvws hfs
        induction tfs generalizing ws with
        | nil => cases ws with
          | nil => trivial
          | cons _ _ => exact absurd hsteps id
        | cons t ts ih => cases ws with
          | nil => exact absurd hsteps id
          | cons w ws => exact ⟨fun π => ⟨1, hsteps.1 π⟩, ih (ws := ws) hsteps.2⟩
      exact ⟨.VConstr tag ws, steps_constr_returns tfs ws hret, valueRel_constr hvws⟩

end Moist.Verified.CaseMerge
