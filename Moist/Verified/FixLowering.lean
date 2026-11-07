import Moist.Verified.FundamentalRefines
import Moist.Verified.InlineSoundness.StrictOcc
import Moist.Verified.InlineSoundness.Frontier
import Moist.Verified.Contextual.Congruence
import Moist.MIR.Lower

/-! # The two Z-combinator encodings of `Fix`

`lowerTotalExpr` encodes `Fix f (Lam x body)` with an explicit redex,
`fixLamWrapUplc B = (λz. z z) (λs. (λf. λx. B) (λv. s s v))`, while the
production lowering substitutes the self application,
`fixLamWrap B = (λz. z z) (λs. λx. B[f := λv. s s v])`.

The forward refinement is an instance of the halting beta rule. The backward
one needs substitution of a lambda in the other direction:
`substLam_eval` relates a term with a closure substituted at one position to
the same term run in an environment holding that closure. Under binders the
substituted lambda is shifted; its closure is related to the stored one by
the renaming fundamental lemma (`renameRefinesG`). -/

namespace Moist.Verified.FixLowering

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified
open Moist.Verified.Equivalence
open Moist.Verified.Contextual
open Moist.Verified.Contextual.Guarded
open Moist.Verified.FundamentalRefines
open Moist.Verified.BetaValueRefines (iterShift extend_lookup_one extend_lookup_succ)
open Moist.Verified.InlineSoundness.StrictOcc
  (multiShift is0preserving_multiShift iterShift_eq_renameTerm_multiShift)

theorem lookup_zero (ρ : CekEnv) : ρ.lookup 0 = none := by
  cases ρ <;> rfl

/-! ## Closedness -/

mutual
  /-- Substitution can only close a term: the original is closed one level up. -/
  theorem closedAt_of_substTerm :
      ∀ (pos : Nat) (r : Term) (t : Term) (d : Nat), 1 ≤ pos → pos ≤ d + 1 →
        closedAt d (substTerm pos r t) = true → closedAt (d + 1) t = true
    | pos, r, .Var n, d, _, hposd, h => by
      simp only [substTerm] at h
      simp only [closedAt, decide_eq_true_eq]
      by_cases hn : n = pos
      · omega
      · simp only [hn, if_false] at h
        by_cases hgt : n > pos
        · simp only [hgt, if_true, closedAt, decide_eq_true_eq] at h; omega
        · simp only [hgt, if_false, closedAt, decide_eq_true_eq] at h; omega
    | pos, r, .Lam _ body, d, hpos, hposd, h => by
      simp only [substTerm, closedAt] at h ⊢
      exact closedAt_of_substTerm (pos + 1) _ body (d + 1) (by omega) (by omega) h
    | pos, r, .Apply f a, d, hpos, hposd, h => by
      simp only [substTerm, closedAt, Bool.and_eq_true] at h ⊢
      exact ⟨closedAt_of_substTerm pos r f d hpos hposd h.1,
        closedAt_of_substTerm pos r a d hpos hposd h.2⟩
    | pos, r, .Force e, d, hpos, hposd, h => by
      simp only [substTerm, closedAt] at h ⊢
      exact closedAt_of_substTerm pos r e d hpos hposd h
    | pos, r, .Delay e, d, hpos, hposd, h => by
      simp only [substTerm, closedAt] at h ⊢
      exact closedAt_of_substTerm pos r e d hpos hposd h
    | pos, r, .Constr _ args, d, hpos, hposd, h => by
      simp only [substTerm, closedAt] at h ⊢
      exact closedAtList_of_substTermList pos r args d hpos hposd h
    | pos, r, .Case scrut alts, d, hpos, hposd, h => by
      simp only [substTerm, closedAt, Bool.and_eq_true] at h ⊢
      exact ⟨closedAt_of_substTerm pos r scrut d hpos hposd h.1,
        closedAtList_of_substTermList pos r alts d hpos hposd h.2⟩
    | _, _, .Constant _, _, _, _, _ => by simp [closedAt]
    | _, _, .Builtin _, _, _, _, _ => by simp [closedAt]
    | _, _, .Error, _, _, _, _ => by simp [closedAt]
  termination_by _ _ t => sizeOf t

  theorem closedAtList_of_substTermList :
      ∀ (pos : Nat) (r : Term) (ts : List Term) (d : Nat), 1 ≤ pos → pos ≤ d + 1 →
        closedAtList d (substTermList pos r ts) = true → closedAtList (d + 1) ts = true
    | _, _, [], _, _, _, _ => by simp [closedAtList]
    | pos, r, t :: rest, d, hpos, hposd, h => by
      simp only [substTermList, closedAtList, Bool.and_eq_true] at h ⊢
      exact ⟨closedAt_of_substTerm pos r t d hpos hposd h.1,
        closedAtList_of_substTermList pos r rest d hpos hposd h.2⟩
  termination_by _ _ ts => sizeOf ts
end

/-! ## Substituting a lambda against an environment slot -/

/-- `ρ₁` runs the substituted term, `ρ₂` the original one, whose position
    `K + 1` holds the closure `VLam rb ρ₂b`. The substituted copy of the lambda
    is shifted by `K`, and `ρ₁` agrees with its base environment `ρ₁b` at the
    shifted positions. Every other position of `ρ₂` matches `ρ₁` with the slot
    removed. -/
structure SlotRel (W : Guard) (k K d d₀ : Nat) (rb : Term)
    (ρ₁ ρ₂ ρ₁b ρ₂b : CekEnv) : Prop where
  slot : ρ₂.lookup (K + 1) = some (.VLam rb ρ₂b)
  shifted : ∀ n, 0 < n → n ≤ d₀ → ρ₁.lookup (n + K) = ρ₁b.lookup n
  base : EnvRel W k d₀ ρ₁b ρ₂b
  other : ∀ n, 0 < n → n ≤ d → n ≠ K + 1 →
    match ρ₁.lookup (if n < K + 1 then n else n - 1), ρ₂.lookup n with
    | some v₁, some v₂ => ValueRel W k v₁ v₂
    | none, none => True
    | _, _ => False

theorem SlotRel.mono {W : Guard} {j k K d d₀ : Nat} {rb : Term}
    {ρ₁ ρ₂ ρ₁b ρ₂b : CekEnv} (hjk : j ≤ k) (h : SlotRel W k K d d₀ rb ρ₁ ρ₂ ρ₁b ρ₂b) :
    SlotRel W j K d d₀ rb ρ₁ ρ₂ ρ₁b ρ₂b := by
  refine ⟨h.slot, h.shifted, fun n hn hnd => ?_, fun n hn hnd hne => ?_⟩
  · obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := h.base n hn hnd
    exact ⟨v₁, v₂, h₁, h₂, valueRel_mono hjk hv⟩
  · have := h.other n hn hnd hne
    revert this
    cases ρ₁.lookup (if n < K + 1 then n else n - 1) <;> cases ρ₂.lookup n <;>
      first | exact id | exact valueRel_mono hjk

theorem SlotRel.extend {W : Guard} {j k K d d₀ : Nat} {rb : Term}
    {ρ₁ ρ₂ ρ₁b ρ₂b : CekEnv} {a₁ a₂ : CekValue} (hjk : j ≤ k)
    (h : SlotRel W k K d d₀ rb ρ₁ ρ₂ ρ₁b ρ₂b) (ha : ValueRel W j a₁ a₂) :
    SlotRel W j (K + 1) (d + 1) d₀ rb (ρ₁.extend a₁) (ρ₂.extend a₂) ρ₁b ρ₂b := by
  have h' := h.mono hjk
  refine ⟨?_, fun n hn hnd => ?_, h'.base, fun n hn hnd hne => ?_⟩
  · rw [extend_lookup_succ ρ₂ a₂ (K + 1) (by omega)]; exact h.slot
  · rw [show n + (K + 1) = (n + K) + 1 from by omega,
      extend_lookup_succ ρ₁ a₁ (n + K) (by omega)]
    exact h.shifted n hn hnd
  · match n, hn with
    | 1, _ =>
      simp only [show (1 : Nat) < K + 1 + 1 from by omega, if_true]
      rw [extend_lookup_one, extend_lookup_one]
      exact ha
    | m + 2, _ =>
      rw [extend_lookup_succ ρ₂ a₂ (m + 1) (by omega)]
      have hold := h'.other (m + 1) (by omega) (by omega) (by omega)
      by_cases hlt : m + 1 < K + 1
      · simp only [show m + 2 < K + 1 + 1 from by omega, if_true]
        simp only [hlt, if_true] at hold
        rw [extend_lookup_succ ρ₁ a₁ (m + 1) (by omega)]
        exact hold
      · simp only [show ¬ (m + 2 < K + 1 + 1) from by omega, if_false]
        simp only [hlt, if_false] at hold
        rw [show m + 2 - 1 = m + 1 from by omega, extend_lookup_succ ρ₁ a₁ m (by omega)]
        rw [show m + 1 - 1 = m from by omega] at hold
        exact hold

theorem iterShift_lam (K name : Nat) (rb : Term) :
    iterShift K (.Lam name rb) =
      .Lam name (renameTerm (liftRename (multiShift K)) rb) := by
  rw [iterShift_eq_renameTerm_multiShift]; rfl

/-- The substituted closure refines the stored one. -/
theorem slot_valueRel {W : Guard} {k K d d₀ : Nat} {rb : Term} (hrb : closedAt (d₀ + 1) rb = true)
    {ρ₁ ρ₂ ρ₁b ρ₂b : CekEnv} (h : SlotRel W k K d d₀ rb ρ₁ ρ₂ ρ₁b ρ₂b)
    (hv₁ : W.V (.VLam (renameTerm (liftRename (multiShift K)) rb) ρ₁))
    (hv₂ : W.V (.VLam rb ρ₂b)) :
    ValueRel W k (.VLam (renameTerm (liftRename (multiShift K)) rb) ρ₁) (.VLam rb ρ₂b) := by
  refine valueRel_lam hv₁ hv₂ fun j hj a₁ a₂ ha _ _ => ?_
  have henv : RenameEnvRef2 (ValueRel W) (liftRename (multiShift K)) id j (d₀ + 1)
      (ρ₁.extend a₁) (ρ₂b.extend a₂) := by
    intro n hn hnd
    match n, hn with
    | 1, _ =>
      show match (ρ₁.extend a₁).lookup 1, (ρ₂b.extend a₂).lookup 1 with
        | some v₁, some v₂ => ValueRel W j v₁ v₂ | none, none => True | _, _ => False
      rw [extend_lookup_one, extend_lookup_one]; exact ha
    | m + 2, _ =>
      show match (ρ₁.extend a₁).lookup (multiShift K (m + 1) + 1),
          (ρ₂b.extend a₂).lookup (m + 2) with
        | some v₁, some v₂ => ValueRel W j v₁ v₂ | none, none => True | _, _ => False
      have hms : multiShift K (m + 1) = m + 1 + K := by simp [multiShift]
      rw [hms, extend_lookup_succ ρ₁ a₁ (m + 1 + K) (by omega),
        extend_lookup_succ ρ₂b a₂ (m + 1) (by omega), h.shifted (m + 1) (by omega) (by omega)]
      obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := h.base (m + 1) (by omega) (by omega)
      rw [h₁, h₂]
      exact valueRel_mono (by omega) hv
  have := renameRefinesG W (liftRename (multiShift K)) id
    (is0preserving_lift _) is0preserving_id (d₀ + 1) rb hrb j henv
  rwa [renameTerm_id] at this

mutual
  theorem substLam_eval (W : Guard) (name : Nat) (rb : Term) (d₀ : Nat)
      (hrb : closedAt (d₀ + 1) rb = true) :
      ∀ (t : Term) (K d : Nat), closedAt d t = true → K + 1 ≤ d →
      ∀ (k : Nat) {ρ₁ ρ₂ ρ₁b ρ₂b : CekEnv}, SlotRel W k K d d₀ rb ρ₁ ρ₂ ρ₁b ρ₂b →
        Eval W k ρ₁ ρ₂ (substTerm (K + 1) (iterShift K (.Lam name rb)) t) t
    | .Var n, K, d, ht, hKd, k, ρ₁, ρ₂, ρ₁b, ρ₂b, h => by
      simp only [closedAt, decide_eq_true_eq] at ht
      by_cases hslot : n = K + 1
      · subst hslot
        simp only [substTerm, if_true, iterShift_lam]
        refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
        simp only [step, h.slot] at hst₁ hst₂ ⊢
        exact ret_obs (slot_valueRel hrb (h.mono (by omega)) (W.ret.mp hst₁).2
          (W.ret.mp hst₂).2) hst₁ hst₂ hπ
      · by_cases hn : n = 0
        · subst hn
          simp only [substTerm, show ¬ ((0 : Nat) = K + 1) from by omega,
            show ¬ ((0 : Nat) > K + 1) from by omega, if_false]
          refine eval_of_step fun j _ _ _ _ _ _ => ?_
          simp only [step, lookup_zero]
          exact obsRefinesK_error_error j
        · have hidx : substTerm (K + 1) (iterShift K (.Lam name rb)) (.Var n) =
              .Var (if n < K + 1 then n else n - 1) := by
            simp only [substTerm, hslot, if_false]
            by_cases hgt : n > K + 1
            · simp only [hgt, if_true, show ¬ (n < K + 1) from by omega, if_false]
            · simp only [hgt, if_false, show n < K + 1 from by omega, if_true]
          rw [hidx]
          refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
          have hrel := (h.mono (Nat.le_of_lt hj)).other n (by omega) ht hslot
          simp only [step] at hst₁ hst₂ ⊢
          revert hrel hst₁ hst₂
          cases ρ₁.lookup (if n < K + 1 then n else n - 1) <;> cases ρ₂.lookup n <;>
            intro hst₁ hst₂ hrel
          · exact obsRefinesK_error_error j
          · exact absurd hrel id
          · exact absurd hrel id
          · exact ret_obs hrel hst₁ hst₂ hπ
    | .Constant _, _, _, _, _, _, _, _, _, _, _ => by
      simp only [substTerm]
      exact eval_of_step fun j _ _ _ hπ hst₁ hst₂ => ret_obs (valueRel_vcon j _) hst₁ hst₂ hπ
    | .Builtin _, _, _, _, _, _, _, _, _, _, _ => by
      simp only [substTerm]
      exact eval_of_step fun j _ _ _ hπ hst₁ hst₂ =>
        ret_obs (valueRel_builtin (k := j) trivial) hst₁ hst₂ hπ
    | .Error, _, _, _, _, _, _, _, _, _, _ => by
      simp only [substTerm]
      exact eval_of_step fun j _ _ _ _ _ _ => obsRefinesK_error_error j
    | .Lam nm body, K, d, ht, hKd, k, ρ₁, ρ₂, ρ₁b, ρ₂b, h => by
      simp only [closedAt] at ht
      simp only [substTerm]
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      refine ret_obs (valueRel_lam (W.ret.mp hst₁).2 (W.ret.mp hst₂).2
        fun j' hj' a₁ a₂ ha _ _ => ?_) hst₁ hst₂ hπ
      exact substLam_eval W name rb d₀ hrb body (K + 1) (d + 1) ht (by omega) j'
        (h.extend (by omega) ha)
    | .Delay body, K, d, ht, hKd, k, ρ₁, ρ₂, ρ₁b, ρ₂b, h => by
      simp only [closedAt] at ht
      simp only [substTerm]
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      exact ret_obs (valueRel_delay (W.ret.mp hst₁).2 (W.ret.mp hst₂).2
        fun j' hj' => substLam_eval W name rb d₀ hrb body K d ht hKd j'
          (h.mono (by omega))) hst₁ hst₂ hπ
    | .Apply f x, K, d, ht, hKd, k, ρ₁, ρ₂, ρ₁b, ρ₂b, h => by
      simp only [closedAt, Bool.and_eq_true] at ht
      simp only [substTerm]
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      exact substLam_eval W name rb d₀ hrb f K d ht.1 hKd j (h.mono (by omega)) j
        (Nat.le_refl _) _ _
        (arg_stackRel (substLam_eval W name rb d₀ hrb x K d ht.2 hKd j (h.mono (by omega)))
          (W.compute hst₁) (W.compute hst₂) hπ) hst₁ hst₂
    | .Force e, K, d, ht, hKd, k, ρ₁, ρ₂, ρ₁b, ρ₂b, h => by
      simp only [closedAt] at ht
      simp only [substTerm]
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      exact substLam_eval W name rb d₀ hrb e K d ht hKd j (h.mono (by omega)) j
        (Nat.le_refl _) _ _ (force_stackRel hπ) hst₁ hst₂
    | .Constr tag [], _, _, _, _, _, _, _, _, _, _ => by
      simp only [substTerm, substTermList]
      exact eval_of_step fun j _ _ _ hπ hst₁ hst₂ =>
        ret_obs (valueRel_constr (k := j) trivial) hst₁ hst₂ hπ
    | .Constr tag (m :: ms), K, d, ht, hKd, k, ρ₁, ρ₂, ρ₁b, ρ₂b, h => by
      simp only [closedAt, closedAtList, Bool.and_eq_true] at ht
      simp only [substTerm, substTermList]
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      exact substLam_eval W name rb d₀ hrb m K d ht.1 hKd j (h.mono (by omega)) j
        (Nat.le_refl _) _ _
        (constrField_stackRel
          (substLamList_eval W name rb d₀ hrb ms K d ht.2 hKd j (h.mono (by omega)))
          trivial (W.compute hst₁) (W.compute hst₂) hπ) hst₁ hst₂
    | .Case scrut alts, K, d, ht, hKd, k, ρ₁, ρ₂, ρ₁b, ρ₂b, h => by
      simp only [closedAt, Bool.and_eq_true] at ht
      simp only [substTerm]
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      exact substLam_eval W name rb d₀ hrb scrut K d ht.1 hKd j (h.mono (by omega)) j
        (Nat.le_refl _) _ _
        (case_stackRel (altsRel_of_listRel
            (substLamList_eval W name rb d₀ hrb alts K d ht.2 hKd j (h.mono (by omega))))
          (W.compute hst₁) (W.compute hst₂) hπ) hst₁ hst₂
  termination_by t => sizeOf t

  theorem substLamList_eval (W : Guard) (name : Nat) (rb : Term) (d₀ : Nat)
      (hrb : closedAt (d₀ + 1) rb = true) :
      ∀ (ts : List Term) (K d : Nat), closedAtList d ts = true → K + 1 ≤ d →
      ∀ (k : Nat) {ρ₁ ρ₂ ρ₁b ρ₂b : CekEnv}, SlotRel W k K d d₀ rb ρ₁ ρ₂ ρ₁b ρ₂b →
        ListRel (Eval W k ρ₁ ρ₂) (substTermList (K + 1) (iterShift K (.Lam name rb)) ts) ts
    | [], _, _, _, _, _, _, _, _, _, _ => by simp only [substTermList]; exact trivial
    | t :: rest, K, d, hts, hKd, k, ρ₁, ρ₂, ρ₁b, ρ₂b, h => by
      simp only [closedAtList, Bool.and_eq_true] at hts
      simp only [substTermList]
      exact ⟨substLam_eval W name rb d₀ hrb t K d hts.1 hKd k h,
        substLamList_eval W name rb d₀ hrb rest K d hts.2 hKd k h⟩
  termination_by ts => sizeOf ts
end

/-! ## The two encodings of a recursive lambda -/

open Moist.MIR (fixSelfApp fixLamWrap fixLamWrapUplc)

/-- Body of `λv. s s v` directly under `λs.` -/
abbrev selfAppBody : Term := .Apply (.Apply (.Var 2) (.Var 2)) (.Var 1)

theorem iterShift_one_selfApp : iterShift 1 (.Lam 0 selfAppBody) = fixSelfApp := rfl

theorem substTerm_selfApp (B : Term) :
    substTerm 1 (.Lam 0 selfAppBody) (.Lam 0 B) = .Lam 0 (substTerm 2 fixSelfApp B) := by
  simp only [substTerm]; rfl

/-- Lowering's redex form refines the substituted form. -/
theorem fixLamWrap_forward (d : Nat) (B : Term) (hB : closedAt (d + 3) B = true) :
    CtxRefines (fixLamWrapUplc B) (fixLamWrap B) := by
  have hbeta := InlineSoundness.Frontier.beta_ctxRefines_of_halts (depth := d + 1)
    (body := .Lam 0 B) (rhs := .Lam 0 selfAppBody) (by simpa [closedAt] using hB)
    (by simp [closedAt]) (fun _ _ _ => ⟨_, 2, rfl⟩)
  rw [substTerm_selfApp] at hbeta
  exact ctxRefines_app (ctxRefines_refl _) (ctxRefines_lam 0 hbeta)

private theorem inner_eval {d j : Nat} {B : Term} (hB : closedAt (d + 3) B = true)
    {ρ₁ ρ₂ : CekEnv} (henv : EnvRel Guard.trivial j d ρ₁ ρ₂) :
    Eval Guard.trivial j ρ₁ ρ₂ (.Lam 0 (.Lam 0 (substTerm 2 fixSelfApp B)))
      (.Lam 0 (.Apply (.Lam 0 (.Lam 0 B)) (.Lam 0 selfAppBody))) := by
  refine eval_of_step fun j₁ hj₁ π₁ π₂ hπ _ _ => ?_
  refine ret_obs (valueRel_lam trivial trivial fun j₂ hj₂ a₁ a₂ ha _ _ => ?_) trivial trivial hπ
  intro i hi π₁' π₂' hπ' _ _
  refine obsRefinesK_of_steps_right (n := 6)
    (s₂' := .ret π₂' (.VLam B (((ρ₂.extend a₂).extend (.VLam selfAppBody (ρ₂.extend a₂)))))) rfl ?_
  refine obsRefinesK_of_steps_left (n := 1)
    (s₁' := .ret π₁' (.VLam (substTerm 2 fixSelfApp B) (ρ₁.extend a₁))) rfl ?_
  refine hπ'.2.2 i (Nat.le_refl _) _ _ (valueRel_lam trivial trivial
    fun j₃ hj₃ b₁ b₂ hb _ _ => ?_) trivial trivial
  rw [← iterShift_one_selfApp]
  refine substLam_eval Guard.trivial 0 selfAppBody (d + 1) (by simp [closedAt])
    B 1 (d + 3) hB (by omega) j₃ (ρ₁b := ρ₁.extend a₁) (ρ₂b := ρ₂.extend a₂) ?_
  have hbase : EnvRel Guard.trivial j₃ (d + 1) (ρ₁.extend a₁) (ρ₂.extend a₂) := by
    intro n hn hnd
    match n, hn with
    | 1, _ => exact ⟨a₁, a₂, rfl, rfl, valueRel_mono (by omega) ha⟩
    | m + 2, _ =>
      obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := henv (m + 1) (by omega) (by omega)
      exact ⟨v₁, v₂, by rw [extend_lookup_succ ρ₁ a₁ (m + 1) (by omega)]; exact h₁,
        by rw [extend_lookup_succ ρ₂ a₂ (m + 1) (by omega)]; exact h₂,
        valueRel_mono (by omega) hv⟩
  refine ⟨rfl, fun n hn _ => extend_lookup_succ _ _ _ hn, hbase, fun n hn hnd hne => ?_⟩
  match n, hn with
  | 1, _ =>
    simp only [show (1 : Nat) < 1 + 1 from by omega, if_true]
    rw [extend_lookup_one, extend_lookup_one]
    exact hb
  | 2, _ => exact absurd rfl hne
  | m + 3, _ =>
    simp only [show ¬ (m + 3 < 1 + 1) from by omega, if_false]
    rw [show m + 3 - 1 = (m + 1) + 1 from by omega,
      extend_lookup_succ (ρ₁.extend a₁) b₁ (m + 1) (by omega),
      show m + 3 = (m + 2) + 1 from by omega,
      extend_lookup_succ _ b₂ (m + 2) (by omega),
      extend_lookup_succ _ _ (m + 1) (by omega)]
    obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := hbase (m + 1) (by omega) (by omega)
    rw [h₁, h₂]
    exact valueRel_mono (by omega) hv

/-- The substituted form refines lowering's redex form. -/
theorem fixLamWrap_backward (d : Nat) (B : Term) (hB : closedAt (d + 3) B = true) :
    CtxRefines (fixLamWrap B) (fixLamWrapUplc B) := by
  have hinner : CtxRefines (.Lam 0 (.Lam 0 (substTerm 2 fixSelfApp B)))
      (.Lam 0 (.Apply (.Lam 0 (.Lam 0 B)) (.Lam 0 selfAppBody))) := by
    refine Contextual.SoundnessRefines.soundness_of_openRel (W := Guard.trivial) (d := d)
      ?_ (fun _ _ => trivial) trivial trivial ?_
    · intro k j _ ρ₁ ρ₂ henv _ _ _ _ i hi π₁ π₂ _ _ hfn
      exact inner_eval hB henv i hi π₁ π₂ ⟨trivial, trivial, hfn⟩ trivial trivial
    · intro C hC
      rw [fill_closedAt_iff] at hC ⊢
      refine ⟨hC.1, ?_⟩
      have h := hC.2
      simp only [closedAt] at h
      have hB' := closedAt_of_substTerm 2 fixSelfApp B (0 + C.binders + 1 + 1)
        (by omega) (by omega) h
      simp only [closedAt, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hB', ⟨by omega, by omega⟩, by omega⟩
  exact ctxRefines_app (ctxRefines_refl _) hinner

end Moist.Verified.FixLowering
