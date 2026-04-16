import Moist.Verified.MIR
import Moist.Verified.MIR.Congruence
import Moist.Verified.DCESoundness
import Moist.Verified.DeadLet
import Moist.Verified.FundamentalRefines
import Moist.MIR.ANF

/-! # Shared infrastructure for MIR rewrite primitives

Reusable helpers used by every primitive file under `Primitives/`:

* `FreshGt{,List,Binds}` — freshness invariant for ANF normalisation.
* CEK-glue lemmas — `steps_trans`, `obsRefinesK_of_steps_{left,right}`,
  `stackRefK_funV_id_augment_{left,right}`, `envRefinesK_extend`,
  `stackRefK_force_augment`, `wrapLet_cons`.
* `closedAt`-under-`shiftRename` mutuals — `closedAt(List)_renameTerm(List)_shiftRename{,_inv}`.
-/

namespace Moist.Verified.MIR

open Moist.CEK
open Moist.Plutus.Term (Term)
open Moist.MIR
  (Expr VarId anfNormalizeCore anfNormalizeListCore anfNormalizeBindsCore anfAtom anfAtomList
   wrapLet flattenLetBody freeVars maxUidExpr maxUidExprList maxUidExprBinds
   lowerTotalExpr lowerTotal lowerTotalLet)
open Moist.Verified (closedAt closedAtList renameTerm shiftRename)
open Moist.Verified (liftRename liftRename_shiftRename renameTermList renameTermList_getElem renameTermList_length shiftRename_ge shiftRename_lt)
open Moist.Verified.Equivalence (steps_error steps_halt constToTagAndFields_fields_vcon listRel_reverse)
open Moist.Verified.Contextual (closedAtList_append)
open Moist.Verified.FundamentalRefines (envRefinesK_to_renameEnvRef_shift Is0Preserving RenameEnvRef renameRefines_shift1)
open Moist.Verified.Contextual
  (Context fill ObsRefines CtxEq CtxRefines
   ctxEq_refl ctxRefines_refl ctxRefines_trans
   ctxEq_lam ctxEq_app
   ctxRefines_lam ctxRefines_app)
open Moist.Verified.Equivalence
  (ListRel ObsEq ObsRefinesK steps Reaches obsRefinesK_mono
   obsRefinesK_zero_ret listRel_mono)
open Moist.Verified.Contextual.SoundnessRefines
  (EnvRefinesK BehRefinesK ValueRefinesK StackRefK valueRefinesK_mono
   evalBuiltin_compat_refines obsRefinesK_error stackRefK_mono
   listRel_valueRefinesK_mono applyArgFrames_stackRefK
   listRel_refl_vcon_refines)
open Moist.Verified.FundamentalRefines (ftlr renameRefines renameRefinesR renameRefinesR_shift1
  is0preserving_id is0preserving_shiftRename
  RenameEnvRefR envRefinesK_to_renameEnvRefR_shift renameEnvRefR_mono)

/-! ## Freshness predicate

`FreshGt s e` says the next fresh uid `s.next` is strictly greater than every
uid in `e`, so freshly-generated variables can't clash with existing ones. -/

def FreshGt (s : Moist.MIR.FreshState) (e : Expr) : Prop :=
  maxUidExpr e < s.next

def FreshGtList (s : Moist.MIR.FreshState) (es : List Expr) : Prop :=
  maxUidExprList es < s.next

def FreshGtBinds (s : Moist.MIR.FreshState) (bs : List (VarId × Expr × Bool)) : Prop :=
  maxUidExprBinds bs < s.next

/-! ## CEK / ObsRefinesK glue -/

/-- `steps_trans` reproven locally (the original is `private` in `DeadLet`). -/
theorem steps_trans (m n : Nat) (s : State) :
    steps (m + n) s = steps n (steps m s) := by
  induction m generalizing s with
  | zero => simp [steps]
  | succ m ih => simp only [Nat.succ_add, steps]; exact ih (Moist.CEK.step s)

/-- Rightward step propagation: if the right state takes `n` deterministic
    steps to reach a `s₂'` that already Obs-refines from `s₁`, then the
    pre-step state `s₂` also Obs-refines from `s₁`. The intuition: any
    halt/error of `s₂'` is a halt/error of `s₂` `n` steps later. -/
theorem obsRefinesK_of_steps_right {k n : Nat} {s₁ s₂ s₂' : State}
    (h_steps : steps n s₂ = s₂')
    (h : ObsRefinesK k s₁ s₂') : ObsRefinesK k s₁ s₂ := by
  refine ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨v', m, hm⟩ := h.1 v hv
    refine ⟨v', n + m, ?_⟩
    rw [steps_trans n m, h_steps]; exact hm
  · intro n' hn' herr
    obtain ⟨m, hm⟩ := h.2 n' hn' herr
    refine ⟨n + m, ?_⟩
    rw [steps_trans n m, h_steps]; exact hm

/-- Leftward step propagation: if the left state takes `n` deterministic
    steps to reach `s₁'`, and `s₁'` Obs-refines `s₂`, then the pre-step
    `s₁` also Obs-refines `s₂`. The intuition: any halt/error of `s₁` is
    either before step `n` (in which case `steps n s₁ = halt/error`, i.e.
    `s₁' = halt/error`) or at step `m > n` (in which case `s₁'` halts/
    errors at step `m - n ≤ k`). -/
theorem obsRefinesK_of_steps_left {k n : Nat} {s₁ s₁' s₂ : State}
    (h_steps : steps n s₁ = s₁')
    (h : ObsRefinesK k s₁' s₂) : ObsRefinesK k s₁ s₂ := by
  refine ⟨?_, ?_⟩
  · intro v ⟨m, hmk, hsteps_v⟩
    by_cases hmn : m ≤ n
    · -- Case m ≤ n: s₁' = steps n s₁ = halt v
      have hs₁'_halt : s₁' = .halt v := by
        rw [← h_steps]
        have hsplit : n = m + (n - m) := by omega
        rw [hsplit, steps_trans, hsteps_v]
        exact steps_halt (n - m) v
      rw [hs₁'_halt] at h
      exact h.1 v ⟨0, Nat.zero_le _, rfl⟩
    · -- Case m > n: s₁' halts at step m - n
      have h_s₁'_halt : steps (m - n) s₁' = .halt v := by
        have hsplit : m = n + (m - n) := by omega
        rw [← h_steps, ← steps_trans, ← hsplit]
        exact hsteps_v
      have hmn_le : m - n ≤ k := by omega
      exact h.1 v ⟨m - n, hmn_le, h_s₁'_halt⟩
  · intro n' hn' herr
    by_cases hmn : n' ≤ n
    · have hs₁'_err : s₁' = .error := by
        rw [← h_steps]
        have hsplit : n = n' + (n - n') := by omega
        rw [hsplit, steps_trans, herr]
        exact steps_error _
      rw [hs₁'_err] at h
      exact h.2 0 (Nat.zero_le _) rfl
    · have h_s₁'_err : steps (n' - n) s₁' = .error := by
        have hsplit : n' = n + (n' - n) := by omega
        rw [← h_steps, ← steps_trans, ← hsplit]
        exact herr
      have hmn_le : n' - n ≤ k := by omega
      exact h.2 (n' - n) hmn_le h_s₁'_err

/-- A stack with an "identity-funV" frame on top is `StackRefK`-related to
    its underlying stack on the right. The frame `funV (VLam (Var 1) ρ)`
    is transparent: it consumes a returned value via two CEK steps
    (compute the `Var 1` lookup, ret the result), leaving the same
    value at the same depth. -/
theorem stackRefK_funV_id_augment_right {j : Nat} {π₁ π₂ : Stack} {ρ₂ : CekEnv}
    (hπ : StackRefK ValueRefinesK j π₁ π₂) :
    StackRefK ValueRefinesK j π₁ (.funV (.VLam (.Var 1) ρ₂) :: π₂) := by
  intro j' hj' v₁ v₂ hv
  have h_steps :
      steps 2 (State.ret (.funV (.VLam (.Var 1) ρ₂) :: π₂) v₂) = State.ret π₂ v₂ := by
    have hl : (ρ₂.extend v₂).lookup 1 = some v₂ := by cases ρ₂ <;> rfl
    show (match (ρ₂.extend v₂).lookup 1 with
          | some v => State.ret π₂ v
          | none => State.error) = State.ret π₂ v₂
    rw [hl]
  exact obsRefinesK_of_steps_right h_steps (hπ j' hj' v₁ v₂ hv)

/-- Symmetric augmentation: an identity-funV frame on the *left* stack
    is `StackRefK`-related to the underlying right stack. -/
theorem stackRefK_funV_id_augment_left {j : Nat} {π₁ π₂ : Stack} {ρ₁ : CekEnv}
    (hπ : StackRefK ValueRefinesK j π₁ π₂) :
    StackRefK ValueRefinesK j (.funV (.VLam (.Var 1) ρ₁) :: π₁) π₂ := by
  intro j' hj' v₁ v₂ hv
  have h_steps :
      steps 2 (State.ret (.funV (.VLam (.Var 1) ρ₁) :: π₁) v₁) = State.ret π₁ v₁ := by
    have hl : (ρ₁.extend v₁).lookup 1 = some v₁ := by cases ρ₁ <;> rfl
    show (match (ρ₁.extend v₁).lookup 1 with
          | some v => State.ret π₁ v
          | none => State.error) = State.ret π₁ v₁
    rw [hl]
  exact obsRefinesK_of_steps_left h_steps (hπ j' hj' v₁ v₂ hv)

/-- Extending both sides of an `EnvRefinesK`-related env-pair by related
    values produces an `EnvRefinesK`-related env-pair at the bumped depth. -/
theorem envRefinesK_extend {k d : Nat} {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue}
    (henv : EnvRefinesK k d ρ₁ ρ₂) (hv : ValueRefinesK k v₁ v₂) :
    EnvRefinesK k (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) := by
  intro n hn hnd
  match n, hn with
  | 1, _ => exact ⟨v₁, v₂, rfl, rfl, hv⟩
  | m + 2, _ =>
    obtain ⟨w₁, w₂, hl, hr, hw⟩ := henv (m + 1) (by omega) (by omega)
    exact ⟨w₁, w₂, hl, hr, hw⟩

/-- `EnvRefinesK` is antitone in the step-count index. -/
theorem envRefinesK_mono {j k d : Nat} {ρ₁ ρ₂ : CekEnv} (hj : j ≤ k)
    (henv : EnvRefinesK k d ρ₁ ρ₂) : EnvRefinesK j d ρ₁ ρ₂ := fun n hn hnd => by
  obtain ⟨w₁, w₂, hl, hr, hw⟩ := henv n hn hnd
  exact ⟨w₁, w₂, hl, hr, valueRefinesK_mono hj _ _ hw⟩

/-- A `.force` frame on top of related stacks gives a `StackRefK`-related
    pair. The .force frame fires based on the value's shape: VDelay
    continues with the delayed body, VBuiltin steps the builtin's force
    handling, and other shapes error on both sides. -/
theorem stackRefK_force_augment {i : Nat} {π₁ π₂ : Stack}
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i (.force :: π₁) (.force :: π₂) := by
  intro j hj v₁ v₂ hv
  match j with
  | 0 => exact obsRefinesK_zero_ret
  | n + 1 =>
    obsRefinesK_of_step_auto
    match v₁, v₂ with
    | .VDelay body₁ ρ₁', .VDelay body₂ ρ₂' =>
      simp only [Moist.CEK.step, ValueRefinesK] at hv ⊢
      exact hv n (by omega) n (Nat.le_refl _) π₁ π₂
        (stackRefK_mono (by omega) hπ)
    | .VBuiltin b₁ args₁ ea₁, .VBuiltin b₂ args₂ ea₂ =>
      simp only [ValueRefinesK] at hv
      obtain ⟨rfl, rfl, hargs⟩ := hv
      simp only [Moist.CEK.step]
      split
      · split
        · rename_i rest _
          have hval : ValueRefinesK (n + 1)
              (.VBuiltin b₁ args₁ rest) (.VBuiltin b₁ args₂ rest) := by
            simp only [ValueRefinesK]
            exact ⟨trivial, trivial, hargs⟩
          exact obsRefinesK_mono (by omega : n ≤ n + 1)
            (hπ (n + 1) (by omega) _ _ hval)
        · exact evalBuiltin_compat_refines hargs
            (stackRefK_mono (by omega) hπ)
      · exact obsRefinesK_error _
    | .VCon _, .VCon _ | .VLam _ _, .VLam _ _ | .VConstr _ _, .VConstr _ _ =>
      simp only [Moist.CEK.step]; exact obsRefinesK_error _
    | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
    | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
    | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
    | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
    | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
    | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
    | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
    | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
    | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at hv

/-- Helper: `wrapLet bs body` is the same as `.Let bs body` when `bs` is
    nonempty. This avoids needing to pattern-match on `bs` explicitly. -/
theorem wrapLet_cons (b : VarId × Expr × Bool) (bs : List (VarId × Expr × Bool))
    (body : Expr) :
    wrapLet (b :: bs) body = .Let (b :: bs) body := rfl
/-! ## Section 4b. Closedness under `shiftRename`

The forward direction: `closedAt k t → closedAt (k+1) (renameTerm (shiftRename 1) t)`.
The inverse direction is `closedAt_shiftRename_unshift` in `DCESoundness.lean` (private). -/

mutual

theorem closedAt_renameTerm_shiftRename :
    ∀ (t : Term) (k c : Nat), 1 ≤ c → c ≤ k + 1 →
      closedAt k t = true →
      closedAt (k + 1) (renameTerm (shiftRename c) t) = true
  | .Var n, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt, decide_eq_true_eq] at h ⊢
    by_cases hn : n ≥ c
    · rw [shiftRename_ge hn]; omega
    · have hn' : n < c := Nat.not_le.mp hn
      rw [shiftRename_lt hn']; omega
  | .Lam _ body, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt] at h ⊢
    have hlift : liftRename (shiftRename c) =
        shiftRename (c + 1) :=
      liftRename_shiftRename hc1
    rw [hlift]
    exact closedAt_renameTerm_shiftRename body (k + 1) (c + 1) (by omega) (by omega) h
  | .Apply f x, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt, Bool.and_eq_true] at h ⊢
    exact ⟨closedAt_renameTerm_shiftRename f k c hc1 hck h.1,
           closedAt_renameTerm_shiftRename x k c hc1 hck h.2⟩
  | .Force e, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt] at h ⊢
    exact closedAt_renameTerm_shiftRename e k c hc1 hck h
  | .Delay e, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt] at h ⊢
    exact closedAt_renameTerm_shiftRename e k c hc1 hck h
  | .Constr _ args, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt] at h ⊢
    exact closedAtList_renameTermList_shiftRename args k c hc1 hck h
  | .Case scrut alts, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt, Bool.and_eq_true] at h ⊢
    exact ⟨closedAt_renameTerm_shiftRename scrut k c hc1 hck h.1,
           closedAtList_renameTermList_shiftRename alts k c hc1 hck h.2⟩
  | .Constant _, _, _, _, _, _ => by simp [closedAt, renameTerm]
  | .Builtin _, _, _, _, _, _ => by simp [closedAt, renameTerm]
  | .Error, _, _, _, _, _ => by simp [closedAt, renameTerm]
termination_by t _ _ _ _ _ => sizeOf t

theorem closedAtList_renameTermList_shiftRename :
    ∀ (ts : List Term) (k c : Nat), 1 ≤ c → c ≤ k + 1 →
      closedAtList k ts = true →
      closedAtList (k + 1)
        (renameTermList (shiftRename c) ts) = true
  | [], _, _, _, _, _ => by simp [closedAtList, renameTermList]
  | t :: rest, k, c, hc1, hck, h => by
    simp only [closedAtList, renameTermList,
               Bool.and_eq_true] at h ⊢
    exact ⟨closedAt_renameTerm_shiftRename t k c hc1 hck h.1,
           closedAtList_renameTermList_shiftRename rest k c hc1 hck h.2⟩
termination_by ts _ _ _ _ _ => sizeOf ts

end

mutual

/-- Inverse direction: `closedAt (k+1) (shiftRename c applied) → closedAt k t`. -/
theorem closedAt_renameTerm_shiftRename_inv :
    ∀ (t : Term) (k c : Nat), 1 ≤ c → c ≤ k + 1 →
      closedAt (k + 1) (renameTerm (shiftRename c) t) = true →
      closedAt k t = true
  | .Var n, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt, decide_eq_true_eq] at h ⊢
    by_cases hn : n ≥ c
    · rw [shiftRename_ge hn] at h; omega
    · have hn' : n < c := Nat.not_le.mp hn
      rw [shiftRename_lt hn'] at h; omega
  | .Lam _ body, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt] at h ⊢
    have hlift : liftRename (shiftRename c) =
        shiftRename (c + 1) :=
      liftRename_shiftRename hc1
    rw [hlift] at h
    exact closedAt_renameTerm_shiftRename_inv body (k + 1) (c + 1) (by omega) (by omega) h
  | .Apply f x, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt, Bool.and_eq_true] at h ⊢
    exact ⟨closedAt_renameTerm_shiftRename_inv f k c hc1 hck h.1,
           closedAt_renameTerm_shiftRename_inv x k c hc1 hck h.2⟩
  | .Force e, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt] at h ⊢
    exact closedAt_renameTerm_shiftRename_inv e k c hc1 hck h
  | .Delay e, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt] at h ⊢
    exact closedAt_renameTerm_shiftRename_inv e k c hc1 hck h
  | .Constr _ args, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt] at h ⊢
    exact closedAtList_renameTermList_shiftRename_inv args k c hc1 hck h
  | .Case scrut alts, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt, Bool.and_eq_true] at h ⊢
    exact ⟨closedAt_renameTerm_shiftRename_inv scrut k c hc1 hck h.1,
           closedAtList_renameTermList_shiftRename_inv alts k c hc1 hck h.2⟩
  | .Constant _, _, _, _, _, _ => by simp [closedAt]
  | .Builtin _, _, _, _, _, _ => by simp [closedAt]
  | .Error, _, _, _, _, _ => by simp [closedAt]
termination_by t _ _ _ _ _ => sizeOf t

theorem closedAtList_renameTermList_shiftRename_inv :
    ∀ (ts : List Term) (k c : Nat), 1 ≤ c → c ≤ k + 1 →
      closedAtList (k + 1)
        (renameTermList (shiftRename c) ts) = true →
      closedAtList k ts = true
  | [], _, _, _, _, _ => by simp [closedAtList]
  | t :: rest, k, c, hc1, hck, h => by
    simp only [closedAtList, renameTermList,
               Bool.and_eq_true] at h ⊢
    exact ⟨closedAt_renameTerm_shiftRename_inv t k c hc1 hck h.1,
           closedAtList_renameTermList_shiftRename_inv rest k c hc1 hck h.2⟩
termination_by ts _ _ _ _ _ => sizeOf ts

end

end Moist.Verified.MIR
