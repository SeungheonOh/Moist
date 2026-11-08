import Moist.Verified.AdvancedRefinement
import Moist.Verified.StepWellFormed
import Moist.Verified.InlineSoundness.StrictOcc
import Moist.Verified.InlineSoundness.Frontier

variable [sv : Moist.CEK.SemVariant]

/-! # Reusing an earlier evaluation

`reuse_ctxRefines` is the UPLC rule behind common sub-expression
elimination: in

    (λ. C[(λ. body) rhs↑]) rhs

where `rhs↑` is `rhs` shifted from the outer binding to the hole of the
context `C`, the second evaluation of `rhs` can be replaced by the variable
bound to the first one, renaming `body`'s own variable to it.

The first evaluation either fails or diverges, and then both sides do, or it
returns a value `a`. From then on the two sides run in the same environment,
and at the hole the left side re-evaluates `rhs↑`: the shift bisimulation
makes that return a value related to `a` (`shifted_returns_rev`), which is
exactly the value the right side reads. -/

namespace Moist.Verified.CSE

open Moist.CEK
open Moist.Plutus.Term (Term)
open Moist.Verified (closedAt closedAtList renameTerm renameTermList liftRename shiftRename)
open Moist.Verified.Equivalence
open Moist.Verified.Contextual
open Moist.Verified.Contextual.SoundnessRefines
open Moist.Verified.Contextual.Guarded
open Moist.Verified.BetaValueRefines
open Moist.Verified.FundamentalRefines

/-! ## Shifted values refine the original -/

theorem renameEnvRef_extend {r : Nat → Nat} (h_r : Is0Preserving r) {k d : Nat}
    {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue} (henv : RenameEnvRef r k d ρ₁ ρ₂)
    (hv : ValueRefinesK k v₁ v₂) :
    RenameEnvRef (liftRename r) k (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) := by
  have h := renameEnvRef2_extend (V := ValueRefinesK) h_r is0preserving_id henv hv
  rwa [Moist.Verified.liftRename_id] at h

private theorem renameEnvRef_of_shiftBisimEnv_rev {σ : Nat → Nat} {j d : Nat} {ρ₁ ρ₂ : CekEnv}
    (conv : ∀ v₁ v₂, ValueWellFormed v₁ → ShiftBisimValue v₁ v₂ → ValueRefinesK j v₂ v₁)
    (hbisim : ShiftBisimEnv σ d ρ₁ ρ₂)
    (hwf_at : ∀ n, 0 < n → n ≤ d → ∀ v, ρ₁.lookup n = some v → ValueWellFormed v) :
    RenameEnvRef σ j d ρ₂ ρ₁ := by
  induction d with
  | zero => intro n hn; omega
  | succ n ih =>
    cases hbisim with
    | @succ _ _ _ _ v₁ v₂ hrest hl₁ hl₂ hbv =>
      intro m hm hmd
      by_cases hm_eq : m = n + 1
      · subst hm_eq
        show match ρ₂.lookup (σ (n + 1)), ρ₁.lookup (n + 1) with
             | some _, some _ => _ | none, none => True | _, _ => False
        rw [hl₁, hl₂]
        exact conv v₁ v₂ (hwf_at (n + 1) (by omega) (Nat.le_refl _) v₁ hl₁) hbv
      · exact ih hrest (fun m' hm' hmd' v hv => hwf_at m' hm' (by omega) v hv) m hm (by omega)

private theorem listRel_of_shiftBisim_rev (k : Nat)
    (conv : ∀ v₁ v₂, ValueWellFormed v₁ → ShiftBisimValue v₁ v₂ → ValueRefinesK k v₂ v₁) :
    ∀ (vs₁ vs₂ : List CekValue), ValueListWellFormed vs₁ → ShiftBisimValueList vs₁ vs₂ →
      ListRel (ValueRefinesK k) vs₂ vs₁
  | [], [], _, .nil => trivial
  | _ :: _, _ :: _, hwf, .cons hv hvs => by
    cases hwf with
    | cons hv_wf hvs_wf =>
      exact ⟨conv _ _ hv_wf hv, listRel_of_shiftBisim_rev k conv _ _ hvs_wf hvs⟩

/-- A shifted copy of a well-formed value refines the value itself. -/
theorem valueRefinesK_of_shiftBisim_rev : ∀ (k : Nat) (v₁ v₂ : CekValue),
    ValueWellFormed v₁ → ShiftBisimValue v₁ v₂ → ValueRefinesK k v₂ v₁ := by
  intro k
  induction k with
  | zero =>
    intro v₁ v₂ _ hbisim
    cases hbisim with
    | vcon => simp [ValueRefinesK]
    | vlam _ _ _ => simp [ValueRefinesK]
    | vdelay _ _ _ => simp [ValueRefinesK]
    | vconstr _ _ => simp [ValueRefinesK]
    | vbuiltin _ _ _ => simp [ValueRefinesK]
  | succ k ih =>
    intro v₁ v₂ hwf hbisim
    cases hbisim with
    | vcon => simp [ValueRefinesK]
    | @vconstr tag fs₁ fs₂ hfs =>
      cases hwf with
      | vconstr _ hwf_fs =>
        simp only [ValueRefinesK]
        exact ⟨trivial, listRel_of_shiftBisim_rev k ih fs₁ fs₂ hwf_fs hfs⟩
    | @vbuiltin b ea args₁ args₂ hargs =>
      cases hwf with
      | vbuiltin _ _ hwf_args =>
        simp only [ValueRefinesK]
        exact ⟨trivial, trivial, listRel_of_shiftBisim_rev k ih args₁ args₂ hwf_args hargs⟩
    | @vlam body ρ₁ ρ₂ σ d hσ henv_bisim hclosed =>
      cases hwf with
      | @vlam _ _ d_wf henv_wf _ hclosed_wf =>
        simp only [ValueRefinesK]
        intro j hj arg₁ arg₂ hargs i hi π₁ π₂ hπ
        by_cases hle : d ≤ d_wf
        · have hwf_at : ∀ n, 0 < n → n ≤ d → ∀ v, ρ₁.lookup n = some v → ValueWellFormed v :=
            fun n hn hnd v hv => by
              obtain ⟨v', hv', hvwf'⟩ := envWellFormed_lookup d_wf henv_wf hn (by omega)
              rw [hv] at hv'; cases hv'; exact hvwf'
          have henvR := renameEnvRef_of_shiftBisimEnv_rev ih henv_bisim hwf_at
          have henvR_ext := renameEnvRef_extend hσ (renameEnvRef_mono hj henvR) hargs
          exact renameRefines _ (is0preserving_lift _) _ body hclosed (k + 1) j (by omega)
            (ρ₂.extend arg₁) (ρ₁.extend arg₂) henvR_ext i hi π₁ π₂ hπ
        · have henv_bisim' := shiftBisimEnv_narrow σ d henv_bisim (show d_wf ≤ d by omega)
          have hwf_at : ∀ n, 0 < n → n ≤ d_wf → ∀ v, ρ₁.lookup n = some v → ValueWellFormed v :=
            fun n hn hnd v hv => by
              obtain ⟨v', hv', hvwf'⟩ := envWellFormed_lookup d_wf henv_wf hn hnd
              rw [hv] at hv'; cases hv'; exact hvwf'
          have henvR := renameEnvRef_of_shiftBisimEnv_rev ih henv_bisim' hwf_at
          have henvR_ext := renameEnvRef_extend hσ (renameEnvRef_mono hj henvR) hargs
          exact renameRefines _ (is0preserving_lift _) _ body hclosed_wf (k + 1) j (by omega)
            (ρ₂.extend arg₁) (ρ₁.extend arg₂) henvR_ext i hi π₁ π₂ hπ
    | @vdelay body ρ₁ ρ₂ σ d hσ henv_bisim hclosed =>
      cases hwf with
      | @vdelay _ _ d_wf henv_wf _ hclosed_wf =>
        simp only [ValueRefinesK]
        intro j hj i hi π₁ π₂ hπ
        by_cases hle : d ≤ d_wf
        · have hwf_at : ∀ n, 0 < n → n ≤ d → ∀ v, ρ₁.lookup n = some v → ValueWellFormed v :=
            fun n hn hnd v hv => by
              obtain ⟨v', hv', hvwf'⟩ := envWellFormed_lookup d_wf henv_wf hn (by omega)
              rw [hv] at hv'; cases hv'; exact hvwf'
          have henvR := renameEnvRef_of_shiftBisimEnv_rev ih henv_bisim hwf_at
          exact renameRefines _ hσ _ body hclosed (k + 1) j (by omega)
            ρ₂ ρ₁ (renameEnvRef_mono hj henvR) i hi π₁ π₂ hπ
        · have henv_bisim' := shiftBisimEnv_narrow σ d henv_bisim (show d_wf ≤ d by omega)
          have hwf_at : ∀ n, 0 < n → n ≤ d_wf → ∀ v, ρ₁.lookup n = some v → ValueWellFormed v :=
            fun n hn hnd v hv => by
              obtain ⟨v', hv', hvwf'⟩ := envWellFormed_lookup d_wf henv_wf hn hnd
              rw [hv] at hv'; cases hv'; exact hvwf'
          have henvR := renameEnvRef_of_shiftBisimEnv_rev ih henv_bisim' hwf_at
          exact renameRefines _ hσ _ body hclosed_wf (k + 1) j (by omega)
            ρ₂ ρ₁ (renameEnvRef_mono hj henvR) i hi π₁ π₂ hπ

/-! ## Re-evaluating a shifted term -/

open Moist.Verified.InlineSoundness.StrictOcc
  (multiShift is0preserving_multiShift iterShift_eq_renameTerm_multiShift ret_on_all_stacks)

omit sv in
private theorem shiftBisimEnv_multiShift {d K : Nat} {ρ ρK : CekEnv}
    (hwf : EnvWellFormed d ρ)
    (h_lookup : ∀ n, 0 < n → n ≤ d → ρK.lookup (n + K) = ρ.lookup n) :
    ShiftBisimEnv (multiShift K) d ρ ρK := by
  induction d with
  | zero => exact ShiftBisimEnv.zero
  | succ n ih =>
    cases hwf with
    | @succ _ _ v hrest _ hlookup_n hvwf =>
      have hrec := ih hrest (fun m hm hmd => h_lookup m hm (by omega))
      have hms : multiShift K (n + 1) = n + 1 + K := by
        simp only [multiShift]; split
        · omega
        · rfl
      have hρK_at : ρK.lookup (n + 1 + K) = some v := by
        rw [h_lookup (n + 1) (by omega) (Nat.le_refl _)]; exact hlookup_n
      refine ShiftBisimEnv.succ (v₁ := v) (v₂ := v) hrec hlookup_n ?_ ?_
      · rw [hms]; exact hρK_at
      · exact shiftBisimValue_refl_id v hvwf

/-- If `t` returns `a` in `ρ`, its shift returns a value refining `a` in any
    environment that extends `ρ` by `K` positions. -/
theorem shifted_returns_rev {t : Term} {a : CekValue} {d K k : Nat} {ρ ρK : CekEnv}
    (hclosed : closedAt d t = true) (henv_wf : EnvWellFormed d ρ)
    (h_ret : ∀ π, ∃ m, steps m (.compute π ρ t) = .ret π a)
    (hawf : ValueWellFormed a)
    (hρK : ∀ n, 0 < n → n ≤ d → ρK.lookup (n + K) = ρ.lookup n) :
    ∀ π, ∃ m b, steps m (.compute π ρK (iterShift K t)) = .ret π b ∧
      ValueRefinesK k b a := by
  intro π
  obtain ⟨m, h_ret_orig⟩ := h_ret []
  have hshift_env : ShiftBisimEnv (multiShift K) d ρ ρK := shiftBisimEnv_multiShift henv_wf hρK
  rw [iterShift_eq_renameTerm_multiShift]
  have h_bisim_state : ShiftBisimState (.compute [] ρ t)
      (.compute [] ρK (renameTerm (multiShift K) t)) :=
    ShiftBisimState.compute (is0preserving_multiShift K) hshift_env hclosed ShiftBisimStack.nil
  have h_after := shiftBisimState_steps_preserves m h_bisim_state
  rw [h_ret_orig] at h_after
  obtain ⟨π'', b, h_shift_steps, h_bisim_v, h_bisim_π⟩ := shiftBisimState_ret_inv h_after
  cases h_bisim_π
  obtain ⟨q, hq⟩ := ret_on_all_stacks h_shift_steps π
  exact ⟨q, b, hq, valueRefinesK_of_shiftBisim_rev k a b hawf h_bisim_v⟩

/-! ## The rewritten terms -/

/-- Position `1` (the reevaluated binding) goes to `i + 1` (the earlier one);
    every other position moves down past the dropped binder. -/
def mergeRename (i : Nat) (n : Nat) : Nat :=
  if n = 0 then 0 else if n = 1 then i + 1 else n - 1

omit sv in
theorem is0preserving_mergeRename (i : Nat) : Is0Preserving (mergeRename i) := by
  refine ⟨rfl, fun n hn => ?_⟩
  simp only [mergeRename]
  split
  · omega
  · split <;> omega

/-- The binding that evaluates `rhs` again, `i` binders below its first evaluation. -/
def reuseSource (rhs body : Term) (i : Nat) : Term :=
  .Apply (.Lam 0 body) (iterShift (i + 1) rhs)

/-- The body reading the earlier binding instead. -/
def reuseTarget (body : Term) (i : Nat) : Term :=
  renameTerm (mergeRename i) body

omit sv in
theorem closedAt_reuseTarget {body : Term} {i d : Nat} (hi : i + 1 ≤ d)
    (h : closedAt (d + 1) body = true) : closedAt d (reuseTarget body i) = true := by
  apply closedAt_rename (mergeRename i) body (d + 1) d h
  intro n hn
  simp only [mergeRename]
  split
  · omega
  · split <;> omega

/-! ## Evaluation under the context -/

section Context

variable {W : Guard}

theorem envRel_mono {j k d : Nat} (hjk : j ≤ k) {ρ₁ ρ₂ : CekEnv}
    (h : EnvRel W k d ρ₁ ρ₂) : EnvRel W j d ρ₁ ρ₂ := by
  intro n hn hnd
  obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := h n hn hnd
  exact ⟨v₁, v₂, h₁, h₂, valueRel_mono hjk hv⟩

theorem envRel_extend {k d : Nat} {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue}
    (h : EnvRel W k d ρ₁ ρ₂) (hv : ValueRel W k v₁ v₂) :
    EnvRel W k (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) := by
  intro n hn hnd
  match n with
  | 1 => exact ⟨v₁, v₂, rfl, rfl, hv⟩
  | n + 2 => exact h (n + 1) (by omega) (by omega)

theorem eval_refl {k d : Nat} {ρ₁ ρ₂ : CekEnv} {t : Term} (ht : closedAt d t = true)
    (h : EnvRel W k d ρ₁ ρ₂) : Eval W k ρ₁ ρ₂ t t := by
  have result := renameRefinesG W id id is0preserving_id is0preserving_id d t ht k
    (renameEnvRef2_id h)
  rwa [Moist.Verified.renameTerm_id] at result

theorem eval_refl_list {k d : Nat} {ρ₁ ρ₂ : CekEnv} {ts : List Term}
    (hts : closedAtList d ts = true) (h : EnvRel W k d ρ₁ ρ₂) :
    ListRel (Eval W k ρ₁ ρ₂) ts ts := by
  have result := renameRefinesGList W id id is0preserving_id is0preserving_id d ts hts k
    (renameEnvRef2_id h)
  rwa [Moist.Verified.renameTermList_id] at result

omit sv in
theorem listRel_around {R : Term → Term → Prop} :
    ∀ (pre post : List Term) {a b : Term}, ListRel R pre pre → R a b → ListRel R post post →
      ListRel R (pre ++ [a] ++ post) (pre ++ [b] ++ post)
  | [], _, _, _, _, hab, hpost => ⟨hab, hpost⟩
  | _ :: pre, post, _, _, hpre, hab, hpost => ⟨hpre.1, listRel_around pre post hpre.2 hab hpost⟩

theorem listRel_eval_mono {j k : Nat} (hjk : j ≤ k) {ρ₁ ρ₂ : CekEnv} :
    ∀ {ts₁ ts₂ : List Term}, ListRel (Eval W k ρ₁ ρ₂) ts₁ ts₂ → ListRel (Eval W j ρ₁ ρ₂) ts₁ ts₂
  | [], [], _ => trivial
  | [], _ :: _, h | _ :: _, [], h => absurd h id
  | _ :: _, _ :: _, h => ⟨eval_mono hjk h.1, listRel_eval_mono hjk h.2⟩

theorem eval_constr {k tag : Nat} {ρ₁ ρ₂ : CekEnv} {ms₁ ms₂ : List Term}
    (h : ListRel (Eval W k ρ₁ ρ₂) ms₁ ms₂) :
    Eval W k ρ₁ ρ₂ (.Constr tag ms₁) (.Constr tag ms₂) := by
  refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
  match ms₁, ms₂, h with
  | [], [], _ => exact ret_obs (valueRel_constr (k := j) trivial) hst₁ hst₂ hπ
  | [], _ :: _, h | _ :: _, [], h => exact absurd h id
  | m₁ :: rest₁, m₂ :: rest₂, h =>
    exact eval_mono (Nat.le_of_lt hj) h.1 j (Nat.le_refl _) _ _
      (constrField_stackRel (listRel_eval_mono (Nat.le_of_lt hj) h.2) trivial
        (W.compute hst₁) (W.compute hst₂) hπ) hst₁ hst₂

theorem eval_case {k : Nat} {ρ₁ ρ₂ : CekEnv} {s₁ s₂ : Term} {as₁ as₂ : List Term}
    (hs : Eval W k ρ₁ ρ₂ s₁ s₂) (has : ListRel (Eval W k ρ₁ ρ₂) as₁ as₂) :
    Eval W k ρ₁ ρ₂ (.Case s₁ as₁) (.Case s₂ as₂) := by
  refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
  exact eval_mono (Nat.le_of_lt hj) hs j (Nat.le_refl _) _ _
    (case_stackRel (altsRel_of_listRel (listRel_eval_mono (Nat.le_of_lt hj) has))
      (W.compute hst₁) (W.compute hst₂) hπ) hst₁ hst₂

theorem eval_apply {k : Nat} {ρ₁ ρ₂ : CekEnv} {f₁ f₂ a₁ a₂ : Term}
    (hf : Eval W k ρ₁ ρ₂ f₁ f₂) (ha : Eval W k ρ₁ ρ₂ a₁ a₂) :
    Eval W k ρ₁ ρ₂ (.Apply f₁ a₁) (.Apply f₂ a₂) := by
  refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
  exact eval_mono (Nat.le_of_lt hj) hf j (Nat.le_refl _) _ _
    (arg_stackRel (eval_mono (Nat.le_of_lt hj) ha) (W.compute hst₁) (W.compute hst₂) hπ)
    hst₁ hst₂

theorem eval_force {k : Nat} {ρ₁ ρ₂ : CekEnv} {e₁ e₂ : Term}
    (he : Eval W k ρ₁ ρ₂ e₁ e₂) :
    Eval W k ρ₁ ρ₂ (.Force e₁) (.Force e₂) := by
  refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
  exact eval_mono (Nat.le_of_lt hj) he j (Nat.le_refl _) _ _ (force_stackRel hπ) hst₁ hst₂

theorem eval_delay {k : Nat} {ρ₁ ρ₂ : CekEnv} {e₁ e₂ : Term}
    (he : ∀ j < k, Eval W j ρ₁ ρ₂ e₁ e₂) :
    Eval W k ρ₁ ρ₂ (.Delay e₁) (.Delay e₂) := by
  refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
  exact ret_obs (valueRel_delay (W.ret.mp hst₁).2 (W.ret.mp hst₂).2
    fun j' hj' => he j' (by omega)) hst₁ hst₂ hπ

theorem eval_lam {k : Nat} {ρ₁ ρ₂ : CekEnv} {x : Nat} {b₁ b₂ : Term}
    (hb : ∀ j < k, ∀ a₁ a₂, ValueRel W j a₁ a₂ → W.V a₁ → W.V a₂ →
      Eval W j (ρ₁.extend a₁) (ρ₂.extend a₂) b₁ b₂) :
    Eval W k ρ₁ ρ₂ (.Lam x b₁) (.Lam x b₂) := by
  refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
  exact ret_obs (valueRel_lam (W.ret.mp hst₁).2 (W.ret.mp hst₂).2
    fun j' hj' a₁ a₂ ha ha₁ ha₂ => hb j' (by omega) a₁ a₂ ha ha₁ ha₂) hst₁ hst₂ hπ

end Context

section Reuse

variable (rhs body : Term) (i depth : Nat) (ρ : CekEnv) (a : CekValue)

/-- Environments below the first evaluation, `m` binders above the hole's
    depth: the left one keeps `ρ` under `m + 1` positions, the right one
    holds the first value `a` at position `m + 1`. -/
def Below (m : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  (∀ n, 0 < n → n ≤ depth → ρ₁.lookup (n + (m + 1)) = ρ.lookup n) ∧
    ρ₂.lookup (m + 1) = some a

omit sv in
theorem Below.extend {m : Nat} {ρ₁ ρ₂ : CekEnv} (h : Below depth ρ a m ρ₁ ρ₂)
    (v₁ v₂ : CekValue) : Below depth ρ a (m + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) := by
  refine ⟨fun n hn hnd => ?_, h.2⟩
  rw [← h.1 n hn hnd]
  show (CekEnv.cons v₁ ρ₁).lookup (n + m + 1 + 1) = ρ₁.lookup (n + m + 1)
  match h' : n + m + 1, (show n + m + 1 ≥ 1 by omega) with
  | k + 1, _ => rfl

theorem reuse_hole (hρ : EnvWellFormed depth ρ) (hrhs : closedAt depth rhs = true)
    (hret : ∀ π, ∃ m, steps m (.compute π ρ rhs) = .ret π a) (ha : ValueWellFormed a)
    (hbody : closedAt (depth + 1 + i + 1) body = true) :
    ∀ k ρ₁ ρ₂, EnvRel Guard.trivial k (depth + 1 + i) ρ₁ ρ₂ → Below depth ρ a i ρ₁ ρ₂ →
      Eval Guard.trivial k ρ₁ ρ₂ (reuseSource rhs body i) (reuseTarget body i) := by
  intro k ρ₁ ρ₂ henv hbelow j hj π₁ π₂ hπ _ _
  obtain ⟨n, b, hsteps, hb⟩ := shifted_returns_rev (K := i + 1) (k := j) hrhs hρ hret ha
    hbelow.1 (.funV (.VLam body ρ₁) :: π₁)
  have hprefix : steps (3 + n + 1) (.compute π₁ ρ₁ (reuseSource rhs body i)) =
      .compute π₁ (ρ₁.extend b) body := by
    rw [steps_trans, steps_trans]
    show steps 1 (steps n (.compute (.funV (.VLam body ρ₁) :: π₁) ρ₁ (iterShift (i + 1) rhs))) = _
    rw [hsteps]
    rfl
  refine obsRefinesK_of_steps_left hprefix ?_
  have henvR : RenameEnvRefR (mergeRename i) j (depth + 1 + i + 1) (ρ₁.extend b) ρ₂ := by
    intro n hn hnd
    by_cases h1 : n = 1
    · subst h1
      show match (ρ₁.extend b).lookup 1, ρ₂.lookup (mergeRename i 1) with
           | some v₁, some v₂ => ValueRefinesK j v₁ v₂ | none, none => True | _, _ => False
      have hm : mergeRename i 1 = i + 1 := by simp [mergeRename]
      rw [hm, hbelow.2]
      exact hb
    · obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := henv (n - 1) (by omega) (by omega)
      have hm : mergeRename i n = n - 1 := by
        simp only [mergeRename, if_neg (show n ≠ 0 by omega), if_neg h1]
      have hl : (ρ₁.extend b).lookup n = ρ₁.lookup (n - 1) := by
        match n, hn, h1 with
        | k + 2, _, _ => rfl
      show match (ρ₁.extend b).lookup n, ρ₂.lookup (mergeRename i n) with
           | some v₁, some v₂ => ValueRefinesK j v₁ v₂ | none, none => True | _, _ => False
      rw [hm, hl, h₁, h₂]
      exact (valueRel_trivial j v₁ v₂).mp (valueRel_mono hj hv)
  exact renameRefinesR (mergeRename i) (is0preserving_mergeRename i) (depth + 1 + i + 1) body
    hbody j j (Nat.le_refl _) (ρ₁.extend b) ρ₂ henvR j (Nat.le_refl _) π₁ π₂
    (stackRefK_iff_stackRel.mpr hπ)

theorem reuse_eval (hρ : EnvWellFormed depth ρ) (hrhs : closedAt depth rhs = true)
    (hret : ∀ π, ∃ m, steps m (.compute π ρ rhs) = .ret π a) (ha : ValueWellFormed a)
    (hbody : closedAt (depth + 1 + i + 1) body = true) :
    ∀ (C : Context) (m : Nat), C.binders + m = i →
      Context.closedAt (depth + 1 + m) C = true →
      ∀ k ρ₁ ρ₂, EnvRel Guard.trivial k (depth + 1 + m) ρ₁ ρ₂ → Below depth ρ a m ρ₁ ρ₂ →
        Eval Guard.trivial k ρ₁ ρ₂ (fill C (reuseSource rhs body i))
          (fill C (reuseTarget body i)) := by
  intro C
  induction C with
  | Hole =>
    intro m hm _ k ρ₁ ρ₂ henv hbelow
    simp only [Context.binders, Nat.zero_add] at hm
    subst hm
    exact reuse_hole rhs body m depth ρ a hρ hrhs hret ha hbody k ρ₁ ρ₂
      (by simpa using henv) hbelow
  | Lam x C ih =>
    intro m hm hC k ρ₁ ρ₂ henv hbelow
    simp only [Context.binders] at hm
    simp only [Context.closedAt] at hC
    exact eval_lam fun j hj a₁ a₂ hv _ _ =>
      ih (m + 1) (by omega) (by simpa [Nat.add_assoc] using hC) j (ρ₁.extend a₁) (ρ₂.extend a₂)
        (by simpa [Nat.add_assoc] using envRel_extend (envRel_mono (Nat.le_of_lt hj) henv) hv)
        (hbelow.extend depth ρ a a₁ a₂)
  | AppLeft C e ih =>
    intro m hm hC k ρ₁ ρ₂ henv hbelow
    simp only [Context.binders] at hm
    simp only [Context.closedAt, Bool.and_eq_true] at hC
    exact eval_apply (ih m hm hC.1 k ρ₁ ρ₂ henv hbelow) (eval_refl hC.2 henv)
  | AppRight e C ih =>
    intro m hm hC k ρ₁ ρ₂ henv hbelow
    simp only [Context.binders] at hm
    simp only [Context.closedAt, Bool.and_eq_true] at hC
    exact eval_apply (eval_refl hC.1 henv) (ih m hm hC.2 k ρ₁ ρ₂ henv hbelow)
  | Delay C ih =>
    intro m hm hC k ρ₁ ρ₂ henv hbelow
    simp only [Context.binders] at hm
    simp only [Context.closedAt] at hC
    exact eval_delay fun j hj =>
      ih m hm hC j ρ₁ ρ₂ (envRel_mono (Nat.le_of_lt hj) henv) hbelow
  | Force C ih =>
    intro m hm hC k ρ₁ ρ₂ henv hbelow
    simp only [Context.binders] at hm
    simp only [Context.closedAt] at hC
    exact eval_force (ih m hm hC k ρ₁ ρ₂ henv hbelow)
  | Constr tag lefts C rights ih =>
    intro m hm hC k ρ₁ ρ₂ henv hbelow
    simp only [Context.binders] at hm
    simp only [Context.closedAt, Bool.and_eq_true] at hC
    exact eval_constr (listRel_around lefts rights (eval_refl_list hC.1.1 henv)
      (ih m hm hC.1.2 k ρ₁ ρ₂ henv hbelow) (eval_refl_list hC.2 henv))
  | Case C alts ih =>
    intro m hm hC k ρ₁ ρ₂ henv hbelow
    simp only [Context.binders] at hm
    simp only [Context.closedAt, Bool.and_eq_true] at hC
    exact eval_case (ih m hm hC.1 k ρ₁ ρ₂ henv hbelow) (eval_refl_list hC.2 henv)
  | CaseAlt scrut lefts C rights ih =>
    intro m hm hC k ρ₁ ρ₂ henv hbelow
    simp only [Context.binders] at hm
    simp only [Context.closedAt, Bool.and_eq_true] at hC
    exact eval_case (eval_refl hC.1.1.1 henv)
      (listRel_around lefts rights (eval_refl_list hC.1.1.2 henv)
        (ih m hm hC.1.2 k ρ₁ ρ₂ henv hbelow) (eval_refl_list hC.2 henv))

end Reuse

/-! ## The contextual rule -/

theorem obsRefines_of_steps_right {n : Nat} {s₁ s₂ s₂' : State}
    (h_steps : steps n s₂ = s₂') (h : ObsRefines s₁ s₂') : ObsRefines s₁ s₂ := by
  refine ⟨fun hv => ?_, fun he => ?_⟩
  · obtain ⟨v, m, hm⟩ := h.halt hv
    exact ⟨v, n + m, by rw [steps_trans, h_steps]; exact hm⟩
  · obtain ⟨m, hm⟩ := h.error he
    exact ⟨n + m, by rw [steps_trans, h_steps]; exact hm⟩

theorem obsRefines_of_obsRefinesK {s₁ s₂ : State} (h : ∀ k, ObsRefinesK k s₁ s₂) :
    ObsRefines s₁ s₂ :=
  ⟨fun ⟨v, n, hn⟩ => (h n).1 v ⟨n, Nat.le_refl _, hn⟩, fun ⟨n, hn⟩ => (h n).2 n (Nat.le_refl _) hn⟩

open Moist.Verified.InlineSoundness.StrictOcc (halt_on_all_stacks error_on_all_stacks
  halt_excludes_error)
open Moist.Verified.InlineSoundness.Frontier (outcome_of_terminal)

omit sv in
private theorem closed_parts {C : Context} {rhs body : Term} {i d : Nat} (hi : C.binders = i)
    (h : closedAt d (.Apply (.Lam 0 (fill C (reuseSource rhs body i))) rhs) = true) :
    Context.closedAt (d + 1) C = true ∧ closedAt (d + 1 + i + 1) body = true ∧
      closedAt d rhs = true := by
  simp only [closedAt, Bool.and_eq_true] at h
  obtain ⟨hC, hX⟩ := (fill_closedAt_iff C _ (d + 1)).mp h.1
  rw [hi] at hX
  simp only [reuseSource, closedAt, Bool.and_eq_true] at hX
  exact ⟨hC, hX.1, h.2⟩

/-- Reusing the value bound by an enclosing evaluation of the same term. -/
theorem reuse_ctxRefines (C : Context) (rhs body : Term) (i depth : Nat) (hi : C.binders = i)
    (hclosed : closedAt depth (.Apply (.Lam 0 (fill C (reuseSource rhs body i))) rhs) = true) :
    CtxRefines (.Apply (.Lam 0 (fill C (reuseSource rhs body i))) rhs)
      (.Apply (.Lam 0 (fill C (reuseTarget body i))) rhs) := by
  apply AdvancedRefinement.contextual_of_wf_refinement hclosed
  · intro d hd
    obtain ⟨hC, hbody, hrhs⟩ := closed_parts hi hd
    simp only [closedAt, Bool.and_eq_true]
    refine ⟨(fill_closedAt_iff C _ (d + 1)).mpr ⟨hC, ?_⟩, hrhs⟩
    rw [hi]
    exact closedAt_reuseTarget (by omega) hbody
  · intro ρ π hρ hlen hπ
    obtain ⟨hC, hbody, hrhs⟩ := closed_parts hi hclosed
    have prefixSource : steps 3 (.compute π ρ (.Apply (.Lam 0 (fill C (reuseSource rhs body i))) rhs)) =
        .compute (.funV (.VLam (fill C (reuseSource rhs body i)) ρ) :: π) ρ rhs := rfl
    have prefixTarget : steps 3 (.compute π ρ (.Apply (.Lam 0 (fill C (reuseTarget body i))) rhs)) =
        .compute (.funV (.VLam (fill C (reuseTarget body i)) ρ) :: π) ρ rhs := rfl
    by_cases halts : ∃ a, Reaches (.compute [] ρ rhs) (.halt a)
    · obtain ⟨a, reach⟩ := halts
      have hret := halt_on_all_stacks reach
      have ha : ValueWellFormed a := by
        obtain ⟨n, hn⟩ := reach
        exact StepWellFormed.halt_value_wf
          (StepWellFormed.StateWellFormed.compute StackWellFormed.nil hρ hlen hrhs) hn
      obtain ⟨m₁, hm₁⟩ := hret (.funV (.VLam (fill C (reuseSource rhs body i)) ρ) :: π)
      obtain ⟨m₂, hm₂⟩ := hret (.funV (.VLam (fill C (reuseTarget body i)) ρ) :: π)
      have stepsSource : steps (3 + m₁ + 1)
          (.compute π ρ (.Apply (.Lam 0 (fill C (reuseSource rhs body i))) rhs)) =
          .compute π (ρ.extend a) (fill C (reuseSource rhs body i)) := by
        rw [steps_trans, steps_trans, prefixSource, hm₁]; rfl
      have stepsTarget : steps (3 + m₂ + 1)
          (.compute π ρ (.Apply (.Lam 0 (fill C (reuseTarget body i))) rhs)) =
          .compute π (ρ.extend a) (fill C (reuseTarget body i)) := by
        rw [steps_trans, steps_trans, prefixTarget, hm₂]; rfl
      refine obsRefines_of_steps_left stepsSource (obsRefines_of_steps_right stepsTarget ?_)
      apply obsRefines_of_obsRefinesK
      intro k
      have henv : EnvRel Guard.trivial k (depth + 1 + 0) (ρ.extend a) (ρ.extend a) := by
        intro n hn hnd
        obtain ⟨v₁, v₂, h₁, h₂, hv⟩ :=
          envRefinesK_refl (k := k) (envWellFormed_extend depth hρ hlen ha) n hn hnd
        exact ⟨v₁, v₂, h₁, h₂, (valueRel_trivial k v₁ v₂).mpr hv⟩
      have hbelow : Below depth ρ a 0 (ρ.extend a) (ρ.extend a) := by
        refine ⟨fun n hn _ => ?_, rfl⟩
        match n, hn with
        | n + 1, _ => rfl
      exact reuse_eval rhs body i depth ρ a hρ hrhs hret ha hbody C 0 (by omega)
        (by simpa using hC) k (ρ.extend a) (ρ.extend a) henv hbelow k (Nat.le_refl _) π π
        (stackRefK_iff_stackRel.mp (stackRefK_refl k π hπ)) trivial trivial
    · have outcome : ∀ {t : Term} {terminal : State},
          (terminal = .error ∨ ∃ v, terminal = .halt v) →
          Reaches (.compute (.funV (.VLam t ρ) :: π) ρ rhs) terminal →
          Reaches (.compute [] ρ rhs) .error := by
        intro t terminal isTerminal reaches
        rcases outcome_of_terminal isTerminal reaches with h | h
        · exact absurd h halts
        · exact h
      refine ⟨fun ⟨v, hv⟩ => ?_, fun he => ?_⟩
      · have hv' := (AdvancedRefinement.reaches_after_prefix 3 rfl).mp hv
        rw [prefixSource] at hv'
        have herr := error_on_all_stacks (outcome (.inr ⟨v, rfl⟩) hv')
          (.funV (.VLam (fill C (reuseSource rhs body i)) ρ) :: π)
        exact absurd (halt_excludes_error hv' herr) id
      · have he' := (AdvancedRefinement.reaches_after_prefix 3 rfl).mp he
        rw [prefixSource] at he'
        have herr := error_on_all_stacks (outcome (.inl rfl) he')
          (.funV (.VLam (fill C (reuseTarget body i)) ρ) :: π)
        apply (AdvancedRefinement.reaches_after_prefix 3 rfl).mpr
        rw [prefixTarget]
        exact herr

end Moist.Verified.CSE
