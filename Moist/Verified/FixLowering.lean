import Moist.Verified.FundamentalRefines
import Moist.Verified.InlineSoundness.StrictOcc
import Moist.Verified.InlineSoundness.Frontier
import Moist.Verified.Contextual.Congruence
import Moist.MIR.Lower

variable [sv : Moist.CEK.SemVariant]

/-! # The two Z-combinator encodings of `Fix`

`lowerTotalExpr` encodes `Fix f (Lam x body)` with an explicit redex,
`fixLamWrapUplc B = (λz. z z) (λs. (λf. λx. B) (λv. s s v))`, while the
production lowering substitutes the self application for `f`,
`fixLamWrap B = (λz. z z) (λs. λx. B[f := s s])`, so that a recursive call
`f a` runs `[[s s] a]` instead of `[(λv. [[s s] v]) a]`.

The two are contextually equivalent (`fixLamWrap_forward`,
`fixLamWrap_backward`) when `B` does not use the slot of `s` directly, which
holds for lowering output. Evaluating `s s` early is sound only because `s` is
always the functional itself: the recursive closures of the two encodings are
related by induction on the step index (`recU_recD`, `recD_recU`).

`substLam_eval` is the general fact for substituting a lambda: a term with a
closure substituted at one position against the same term run in an
environment holding that closure. Under binders the substituted lambda is
shifted; its closure is related to the stored one by the renaming fundamental
lemma (`renameRefinesG`). -/

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
  (multiShift is0preserving_multiShift iterShift_eq_renameTerm_multiShift freeOf freeOfList)
open Moist.Verified.BetaValueRefines (closedAt_substTerm)

omit sv in
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

omit sv in
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

/-! ## The two encodings of a recursive lambda

`fixLamWrapUplc B = (λz. z z) (λs. (λf. λx. B) (λv. s s v))` binds `f` to the
eta closure `λv. s s v`; the production `fixLamWrap B = (λz. z z) (λs. λx.
B[f := s s])` evaluates the self application at every reference to `f`, so a
recursive call `f a` runs `[[s s] a]`.

Both terms evaluate their functional applied to itself: `recU` and `recD` are
the resulting recursive closures. They are related by induction on the step
index. A reference to `f` yields the eta closure `etaU` on one side and
`recD`, four steps later, on the other; applying `etaU` runs straight into
`recU`, so `etaU` and `recD` are related one index below `recU` and `recD`.
Moving `s s` before the argument is sound only because `s` is the functional
itself; the body therefore must not use `s` directly (`freeOf 3 B`, which
lowering guarantees by shadowing that slot). -/

open Moist.MIR (fixSelfCall fixLamWrap fixLamWrapUplc)

/-- Body of `λv. s s v` directly under `λs.` -/
abbrev selfAppBody : Term := .Apply (.Apply (.Var 2) (.Var 2)) (.Var 1)

/-- `s s` with `s` at index `p`. -/
abbrev selfCallAt (p : Nat) : Term := .Apply (.Var p) (.Var p)

omit sv in
theorem substTerm_selfCallAt_lam {p : Nat} (hp : 1 ≤ p) (nm : Nat) (body : Term) :
    substTerm p (selfCallAt p) (.Lam nm body) =
      .Lam nm (substTerm (p + 1) (selfCallAt (p + 1)) body) := by
  have : renameTerm (shiftRename 1) (selfCallAt p) = selfCallAt (p + 1) := by
    simp only [selfCallAt, renameTerm, shiftRename, show p ≥ 1 from hp, if_true]
  simp only [substTerm, this]

/-- The functional of `fixLamWrapUplc B` in `ρ`. -/
def fnU (ρ : CekEnv) (B : Term) : CekValue :=
  .VLam (.Apply (.Lam 0 (.Lam 0 B)) (.Lam 0 selfAppBody)) ρ

/-- The eta closure `λv. s s v` that `fixLamWrapUplc B` binds to `f`. -/
def etaU (ρ : CekEnv) (B : Term) : CekValue := .VLam selfAppBody (ρ.extend (fnU ρ B))

/-- The recursive function `fixLamWrapUplc B` evaluates to. -/
def recU (ρ : CekEnv) (B : Term) : CekValue :=
  .VLam B ((ρ.extend (fnU ρ B)).extend (etaU ρ B))

/-- The functional of `fixLamWrap B` in `ρ`, with `B'` its substituted body. -/
def fnD (ρ : CekEnv) (B' : Term) : CekValue := .VLam (.Lam 0 B') ρ

/-- The recursive function `fixLamWrap B` evaluates to. -/
def recD (ρ : CekEnv) (B' : Term) : CekValue := .VLam B' (ρ.extend (fnD ρ B'))

theorem steps_fixLamWrapUplc (π : Stack) (ρ : CekEnv) (B : Term) :
    steps 16 (.compute π ρ (fixLamWrapUplc B)) = .ret π (recU ρ B) := rfl

theorem steps_fixLamWrap (π : Stack) (ρ : CekEnv) (B : Term) :
    steps 11 (.compute π ρ (fixLamWrap B)) =
      .ret π (recD ρ (substTerm 2 fixSelfCall B)) := rfl

/-- Applying the eta closure: the self application, then the call. -/
theorem steps_etaU (π : Stack) (ρ : CekEnv) (B : Term) (a : CekValue) :
    steps 15 (.compute π ((ρ.extend (fnU ρ B)).extend a) selfAppBody) =
      .compute π (((ρ.extend (fnU ρ B)).extend (etaU ρ B)).extend a) B := rfl

/-- The self application of the production functional. -/
theorem steps_selfCall {π : Stack} {ρ' ρ : CekEnv} {p : Nat} {B' : Term}
    (h : ρ'.lookup p = some (fnD ρ B')) :
    steps 6 (.compute π ρ' (selfCallAt p)) = .ret π (recD ρ B') := by
  simp [steps, step, h, fnD, recD]

theorem steps_var {π : Stack} {ρ : CekEnv} {p : Nat} {v : CekValue}
    (h : ρ.lookup p = some v) : steps 1 (.compute π ρ (.Var p)) = .ret π v := by
  simp [steps, step, h]

/-- The eta closure refines the production closure one index below the
    recursive closures. -/
theorem etaU_recD {j : Nat} {ρU ρD : CekEnv} {B B' : Term}
    (hrec : ∀ i ≤ j, ValueRel Guard.trivial i (recU ρU B) (recD ρD B')) :
    ValueRel Guard.trivial j (etaU ρU B) (recD ρD B') := by
  refine valueRel_lam trivial trivial fun j' hj' a₁ a₂ ha _ _ => ?_
  intro i hi π₁ π₂ hπ _ _
  refine obsRefinesK_of_steps_left (steps_etaU π₁ ρU B a₁) ?_
  have hr := hrec (j' + 1) (by omega)
  simp only [recU, recD, ValueRel] at hr
  exact hr.2.2 j' (Nat.le_refl _) a₁ a₂ ha trivial trivial i hi π₁ π₂ trivial trivial hπ.2.2

/-- The production closure refines the eta closure one index below the
    recursive closures. -/
theorem recD_etaU {j : Nat} {ρU ρD : CekEnv} {B B' : Term}
    (hrec : ∀ i ≤ j, ValueRel Guard.trivial i (recD ρD B') (recU ρU B)) :
    ValueRel Guard.trivial j (recD ρD B') (etaU ρU B) := by
  refine valueRel_lam trivial trivial fun j' hj' a₁ a₂ ha _ _ => ?_
  intro i hi π₁ π₂ hπ _ _
  refine obsRefinesK_of_steps_right (steps_etaU π₂ ρU B a₂) ?_
  have hr := hrec (j' + 1) (by omega)
  simp only [recU, recD, ValueRel] at hr
  exact hr.2.2 j' (Nat.le_refl _) a₁ a₂ ha trivial trivial i hi π₁ π₂ trivial trivial hπ.2.2

/-! ### `fixLamWrapUplc` refines `fixLamWrap` -/

/-- `ρ₁` runs a body of `fixLamWrapUplc`, `ρ₂` its substituted copy, both under
    `K` further binders. Position `K + 2` holds `f` on the left and `s` on the
    right; position `K + 3`, `s` on the left, is unused; the positions above
    are one lower on the right. -/
structure FwdRel (k K d : Nat) (ρU : CekEnv) (B : Term) (ρD : CekEnv) (B' : Term)
    (ρ₁ ρ₂ : CekEnv) : Prop where
  slot₁ : ρ₁.lookup (K + 2) = some (etaU ρU B)
  slot₂ : ρ₂.lookup (K + 2) = some (fnD ρD B')
  recRel : ∀ j ≤ k, ValueRel Guard.trivial j (recU ρU B) (recD ρD B')
  other : ∀ n, 0 < n → n ≤ d → n ≠ K + 2 → n ≠ K + 3 →
    match ρ₁.lookup n, ρ₂.lookup (if n < K + 2 then n else n - 1) with
    | some v₁, some v₂ => ValueRel Guard.trivial k v₁ v₂
    | none, none => True
    | _, _ => False

theorem FwdRel.mono {j k K d : Nat} {ρU ρD ρ₁ ρ₂ : CekEnv} {B B' : Term} (hjk : j ≤ k)
    (h : FwdRel k K d ρU B ρD B' ρ₁ ρ₂) : FwdRel j K d ρU B ρD B' ρ₁ ρ₂ := by
  refine ⟨h.slot₁, h.slot₂, fun i hi => h.recRel i (Nat.le_trans hi hjk),
    fun n hn hnd hne hne' => ?_⟩
  have := h.other n hn hnd hne hne'
  revert this
  cases ρ₁.lookup n <;> cases ρ₂.lookup (if n < K + 2 then n else n - 1) <;>
    first | exact id | exact valueRel_mono hjk

theorem FwdRel.extend {j k K d : Nat} {ρU ρD ρ₁ ρ₂ : CekEnv} {B B' : Term}
    {a₁ a₂ : CekValue} (hjk : j ≤ k) (h : FwdRel k K d ρU B ρD B' ρ₁ ρ₂)
    (ha : ValueRel Guard.trivial j a₁ a₂) :
    FwdRel j (K + 1) (d + 1) ρU B ρD B' (ρ₁.extend a₁) (ρ₂.extend a₂) := by
  have h' := h.mono hjk
  refine ⟨?_, ?_, h'.recRel, fun n hn hnd hne hne' => ?_⟩
  · rw [show K + 1 + 2 = (K + 2) + 1 from by omega, extend_lookup_succ ρ₁ a₁ (K + 2) (by omega)]
    exact h.slot₁
  · rw [show K + 1 + 2 = (K + 2) + 1 from by omega, extend_lookup_succ ρ₂ a₂ (K + 2) (by omega)]
    exact h.slot₂
  · match n, hn with
    | 1, _ =>
      simp only [show (1 : Nat) < K + 1 + 2 from by omega, if_true]
      rw [extend_lookup_one, extend_lookup_one]
      exact ha
    | m + 2, _ =>
      rw [extend_lookup_succ ρ₁ a₁ (m + 1) (by omega)]
      have hold := h'.other (m + 1) (by omega) (by omega) (by omega) (by omega)
      by_cases hlt : m + 1 < K + 2
      · simp only [show m + 2 < K + 1 + 2 from by omega, if_true]
        simp only [hlt, if_true] at hold
        rw [extend_lookup_succ ρ₂ a₂ (m + 1) (by omega)]
        exact hold
      · simp only [show ¬ (m + 2 < K + 1 + 2) from by omega, if_false]
        simp only [hlt, if_false] at hold
        rw [show m + 2 - 1 = m + 1 from by omega, extend_lookup_succ ρ₂ a₂ m (by omega)]
        rw [show m + 1 - 1 = m from by omega] at hold
        exact hold

mutual
  theorem fwd_eval (ρU : CekEnv) (B : Term) (ρD : CekEnv) (B' : Term) :
      ∀ (t : Term) (K d : Nat), closedAt d t = true → freeOf (K + 3) t = true →
      ∀ (k : Nat) {ρ₁ ρ₂ : CekEnv}, FwdRel k K d ρU B ρD B' ρ₁ ρ₂ →
        Eval Guard.trivial k ρ₁ ρ₂ t (substTerm (K + 2) (selfCallAt (K + 2)) t)
    | .Var n, K, d, ht, hfree, k, ρ₁, ρ₂, h => by
      simp only [closedAt, decide_eq_true_eq] at ht
      simp only [freeOf, bne_iff_ne, ne_eq] at hfree
      by_cases hslot : n = K + 2
      · subst hslot
        simp only [substTerm, if_true]
        intro j hj π₁ π₂ hπ _ _
        refine obsRefinesK_of_steps_left (steps_var h.slot₁) ?_
        refine obsRefinesK_of_steps_right (steps_selfCall h.slot₂) ?_
        exact ret_obs (etaU_recD fun i hi => h.recRel i (by omega)) trivial trivial hπ
      · by_cases hn : n = 0
        · subst hn
          simp only [substTerm, show ¬ ((0 : Nat) = K + 2) from by omega,
            show ¬ ((0 : Nat) > K + 2) from by omega, if_false]
          refine eval_of_step fun j _ _ _ _ _ _ => ?_
          simp only [step, lookup_zero]
          exact obsRefinesK_error_error j
        · have hidx : substTerm (K + 2) (selfCallAt (K + 2)) (.Var n) =
              .Var (if n < K + 2 then n else n - 1) := by
            simp only [substTerm, hslot, if_false]
            by_cases hgt : n > K + 2
            · simp only [hgt, if_true, show ¬ (n < K + 2) from by omega, if_false]
            · simp only [hgt, if_false, show n < K + 2 from by omega, if_true]
          rw [hidx]
          refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
          have hrel := (h.mono (Nat.le_of_lt hj)).other n (by omega) ht hslot hfree
          simp only [step] at hst₁ hst₂ ⊢
          revert hrel hst₁ hst₂
          cases ρ₁.lookup n <;> cases ρ₂.lookup (if n < K + 2 then n else n - 1) <;>
            intro hst₁ hst₂ hrel
          · exact obsRefinesK_error_error j
          · exact absurd hrel id
          · exact absurd hrel id
          · exact ret_obs hrel hst₁ hst₂ hπ
    | .Constant _, _, _, _, _, _, _, _, _ => by
      simp only [substTerm]
      exact eval_of_step fun j _ _ _ hπ hst₁ hst₂ => ret_obs (valueRel_vcon j _) hst₁ hst₂ hπ
    | .Builtin _, _, _, _, _, _, _, _, _ => by
      simp only [substTerm]
      exact eval_of_step fun j _ _ _ hπ hst₁ hst₂ =>
        ret_obs (valueRel_builtin (k := j) trivial) hst₁ hst₂ hπ
    | .Error, _, _, _, _, _, _, _, _ => by
      simp only [substTerm]
      exact eval_of_step fun j _ _ _ _ _ _ => obsRefinesK_error_error j
    | .Lam nm body, K, d, ht, hfree, k, ρ₁, ρ₂, h => by
      simp only [closedAt] at ht
      simp only [freeOf] at hfree
      rw [substTerm_selfCallAt_lam (by omega)]
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      refine ret_obs (valueRel_lam trivial trivial
        fun j' hj' a₁ a₂ ha _ _ => ?_) hst₁ hst₂ hπ
      exact fwd_eval ρU B ρD B' body (K + 1) (d + 1) ht hfree j' (h.extend (by omega) ha)
    | .Delay body, K, d, ht, hfree, k, ρ₁, ρ₂, h => by
      simp only [closedAt] at ht
      simp only [freeOf] at hfree
      simp only [substTerm]
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      exact ret_obs (valueRel_delay trivial trivial
        fun j' hj' => fwd_eval ρU B ρD B' body K d ht hfree j'
          (h.mono (by omega))) hst₁ hst₂ hπ
    | .Apply f x, K, d, ht, hfree, k, ρ₁, ρ₂, h => by
      simp only [closedAt, Bool.and_eq_true] at ht
      simp only [freeOf, Bool.and_eq_true] at hfree
      simp only [substTerm]
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      exact fwd_eval ρU B ρD B' f K d ht.1 hfree.1 j (h.mono (by omega)) j
        (Nat.le_refl _) _ _
        (arg_stackRel (fwd_eval ρU B ρD B' x K d ht.2 hfree.2 j (h.mono (by omega)))
          trivial trivial hπ) hst₁ hst₂
    | .Force e, K, d, ht, hfree, k, ρ₁, ρ₂, h => by
      simp only [closedAt] at ht
      simp only [freeOf] at hfree
      simp only [substTerm]
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      exact fwd_eval ρU B ρD B' e K d ht hfree j (h.mono (by omega)) j
        (Nat.le_refl _) _ _ (force_stackRel hπ) hst₁ hst₂
    | .Constr tag [], _, _, _, _, _, _, _, _ => by
      simp only [substTerm, substTermList]
      exact eval_of_step fun j _ _ _ hπ hst₁ hst₂ =>
        ret_obs (valueRel_constr (k := j) trivial) hst₁ hst₂ hπ
    | .Constr tag (m :: ms), K, d, ht, hfree, k, ρ₁, ρ₂, h => by
      simp only [closedAt, closedAtList, Bool.and_eq_true] at ht
      simp only [freeOf, freeOfList, Bool.and_eq_true] at hfree
      simp only [substTerm, substTermList]
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      exact fwd_eval ρU B ρD B' m K d ht.1 hfree.1 j (h.mono (by omega)) j
        (Nat.le_refl _) _ _
        (constrField_stackRel
          (fwdList_eval ρU B ρD B' ms K d ht.2 hfree.2 j (h.mono (by omega)))
          trivial trivial trivial hπ) hst₁ hst₂
    | .Case scrut alts, K, d, ht, hfree, k, ρ₁, ρ₂, h => by
      simp only [closedAt, Bool.and_eq_true] at ht
      simp only [freeOf, Bool.and_eq_true] at hfree
      simp only [substTerm]
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      exact fwd_eval ρU B ρD B' scrut K d ht.1 hfree.1 j (h.mono (by omega)) j
        (Nat.le_refl _) _ _
        (case_stackRel (altsRel_of_listRel
            (fwdList_eval ρU B ρD B' alts K d ht.2 hfree.2 j (h.mono (by omega))))
          trivial trivial hπ) hst₁ hst₂
  termination_by t => sizeOf t

  theorem fwdList_eval (ρU : CekEnv) (B : Term) (ρD : CekEnv) (B' : Term) :
      ∀ (ts : List Term) (K d : Nat), closedAtList d ts = true → freeOfList (K + 3) ts = true →
      ∀ (k : Nat) {ρ₁ ρ₂ : CekEnv}, FwdRel k K d ρU B ρD B' ρ₁ ρ₂ →
        ListRel (Eval Guard.trivial k ρ₁ ρ₂) ts
          (substTermList (K + 2) (selfCallAt (K + 2)) ts)
    | [], _, _, _, _, _, _, _, _ => by simp only [substTermList]; exact trivial
    | t :: rest, K, d, hts, hfree, k, ρ₁, ρ₂, h => by
      simp only [closedAtList, Bool.and_eq_true] at hts
      simp only [freeOfList, Bool.and_eq_true] at hfree
      simp only [substTermList]
      exact ⟨fwd_eval ρU B ρD B' t K d hts.1 hfree.1 k h,
        fwdList_eval ρU B ρD B' rest K d hts.2 hfree.2 k h⟩
  termination_by ts => sizeOf ts
end

theorem envRel_mono_trivial {j k d : Nat} {ρ₁ ρ₂ : CekEnv} (hjk : j ≤ k)
    (h : EnvRel Guard.trivial k d ρ₁ ρ₂) : EnvRel Guard.trivial j d ρ₁ ρ₂ := by
  intro n hn hnd
  obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := h n hn hnd
  exact ⟨v₁, v₂, h₁, h₂, valueRel_mono hjk hv⟩

/-- The recursive closures, by induction on the step index. -/
theorem recU_recD {d : Nat} {B : Term} (hB : closedAt (d + 3) B = true)
    (hfree : freeOf 3 B = true) {ρU ρD : CekEnv} :
    ∀ k, EnvRel Guard.trivial k d ρU ρD →
      ValueRel Guard.trivial k (recU ρU B) (recD ρD (substTerm 2 fixSelfCall B))
  | k, henv => by
    refine valueRel_lam trivial trivial fun j hj a₁ a₂ ha _ _ => ?_
    refine fwd_eval ρU B ρD _ B 0 (d + 3) hB hfree j
      ⟨rfl, rfl, fun i hi => recU_recD hB hfree i (envRel_mono_trivial (by omega) henv),
        fun n hn hnd hne hne' => ?_⟩
    match n, hn with
    | 1, _ => exact ha
    | m + 4, _ =>
      simp only [show ¬ (m + 4 < 0 + 2) from by omega, if_false,
        show m + 4 - 1 = m + 3 from by omega]
      obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := henv (m + 1) (by omega) (by omega)
      show match ρU.lookup (m + 1), ρD.lookup (m + 1) with
        | some v₁, some v₂ => ValueRel Guard.trivial j v₁ v₂
        | none, none => True
        | _, _ => False
      rw [h₁, h₂]
      exact valueRel_mono (by omega) hv
    | 2, _ | 3, _ => omega
  termination_by k => k

/-- Lowering's redex form refines the production form. -/
theorem fixLamWrap_forward (d : Nat) (B : Term) (hB : closedAt (d + 3) B = true)
    (hfree : freeOf 3 B = true) : CtxRefines (fixLamWrapUplc B) (fixLamWrap B) := by
  refine Contextual.SoundnessRefines.soundness_of_openRel (W := Guard.trivial) (d := d)
    ?_ (fun _ _ => trivial) trivial trivial ?_
  · intro k j _ ρ₁ ρ₂ henv _ _ _ _ i hi π₁ π₂ _ _ hfn
    refine obsRefinesK_of_steps_left (steps_fixLamWrapUplc π₁ ρ₁ B) ?_
    refine obsRefinesK_of_steps_right (steps_fixLamWrap π₂ ρ₂ B) ?_
    exact hfn i (Nat.le_refl _) _ _
      (recU_recD hB hfree i (envRel_mono_trivial hi henv)) trivial trivial
  · intro C hC
    rw [fill_closedAt_iff] at hC ⊢
    refine ⟨hC.1, ?_⟩
    have h := hC.2
    simp only [fixLamWrapUplc, closedAt, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [fixLamWrap, closedAt, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨by omega, closedAt_substTerm 2 fixSelfCall B (0 + C.binders + 1 + 1)
      (by omega) (by omega) (by simp [fixSelfCall, closedAt]) h.2.1⟩

/-! ### `fixLamWrap` refines `fixLamWrapUplc` -/

/-- `FwdRel` with the sides exchanged. -/
structure BwdRel (k K d : Nat) (ρU : CekEnv) (B : Term) (ρD : CekEnv) (B' : Term)
    (ρ₁ ρ₂ : CekEnv) : Prop where
  slot₁ : ρ₁.lookup (K + 2) = some (fnD ρD B')
  slot₂ : ρ₂.lookup (K + 2) = some (etaU ρU B)
  recRel : ∀ j ≤ k, ValueRel Guard.trivial j (recD ρD B') (recU ρU B)
  other : ∀ n, 0 < n → n ≤ d → n ≠ K + 2 → n ≠ K + 3 →
    match ρ₁.lookup (if n < K + 2 then n else n - 1), ρ₂.lookup n with
    | some v₁, some v₂ => ValueRel Guard.trivial k v₁ v₂
    | none, none => True
    | _, _ => False

theorem BwdRel.mono {j k K d : Nat} {ρU ρD ρ₁ ρ₂ : CekEnv} {B B' : Term} (hjk : j ≤ k)
    (h : BwdRel k K d ρU B ρD B' ρ₁ ρ₂) : BwdRel j K d ρU B ρD B' ρ₁ ρ₂ := by
  refine ⟨h.slot₁, h.slot₂, fun i hi => h.recRel i (Nat.le_trans hi hjk),
    fun n hn hnd hne hne' => ?_⟩
  have := h.other n hn hnd hne hne'
  revert this
  cases ρ₁.lookup (if n < K + 2 then n else n - 1) <;> cases ρ₂.lookup n <;>
    first | exact id | exact valueRel_mono hjk

theorem BwdRel.extend {j k K d : Nat} {ρU ρD ρ₁ ρ₂ : CekEnv} {B B' : Term}
    {a₁ a₂ : CekValue} (hjk : j ≤ k) (h : BwdRel k K d ρU B ρD B' ρ₁ ρ₂)
    (ha : ValueRel Guard.trivial j a₁ a₂) :
    BwdRel j (K + 1) (d + 1) ρU B ρD B' (ρ₁.extend a₁) (ρ₂.extend a₂) := by
  have h' := h.mono hjk
  refine ⟨?_, ?_, h'.recRel, fun n hn hnd hne hne' => ?_⟩
  · rw [show K + 1 + 2 = (K + 2) + 1 from by omega, extend_lookup_succ ρ₁ a₁ (K + 2) (by omega)]
    exact h.slot₁
  · rw [show K + 1 + 2 = (K + 2) + 1 from by omega, extend_lookup_succ ρ₂ a₂ (K + 2) (by omega)]
    exact h.slot₂
  · match n, hn with
    | 1, _ =>
      simp only [show (1 : Nat) < K + 1 + 2 from by omega, if_true]
      rw [extend_lookup_one, extend_lookup_one]
      exact ha
    | m + 2, _ =>
      rw [extend_lookup_succ ρ₂ a₂ (m + 1) (by omega)]
      have hold := h'.other (m + 1) (by omega) (by omega) (by omega) (by omega)
      by_cases hlt : m + 1 < K + 2
      · simp only [show m + 2 < K + 1 + 2 from by omega, if_true]
        simp only [hlt, if_true] at hold
        rw [extend_lookup_succ ρ₁ a₁ (m + 1) (by omega)]
        exact hold
      · simp only [show ¬ (m + 2 < K + 1 + 2) from by omega, if_false]
        simp only [hlt, if_false] at hold
        rw [show m + 2 - 1 = m + 1 from by omega, extend_lookup_succ ρ₁ a₁ m (by omega)]
        rw [show m + 1 - 1 = m from by omega] at hold
        exact hold

mutual
  theorem bwd_eval (ρU : CekEnv) (B : Term) (ρD : CekEnv) (B' : Term) :
      ∀ (t : Term) (K d : Nat), closedAt d t = true → freeOf (K + 3) t = true →
      ∀ (k : Nat) {ρ₁ ρ₂ : CekEnv}, BwdRel k K d ρU B ρD B' ρ₁ ρ₂ →
        Eval Guard.trivial k ρ₁ ρ₂ (substTerm (K + 2) (selfCallAt (K + 2)) t) t
    | .Var n, K, d, ht, hfree, k, ρ₁, ρ₂, h => by
      simp only [closedAt, decide_eq_true_eq] at ht
      simp only [freeOf, bne_iff_ne, ne_eq] at hfree
      by_cases hslot : n = K + 2
      · subst hslot
        simp only [substTerm, if_true]
        intro j hj π₁ π₂ hπ _ _
        refine obsRefinesK_of_steps_left (steps_selfCall h.slot₁) ?_
        refine obsRefinesK_of_steps_right (steps_var h.slot₂) ?_
        exact ret_obs (recD_etaU fun i hi => h.recRel i (by omega)) trivial trivial hπ
      · by_cases hn : n = 0
        · subst hn
          simp only [substTerm, show ¬ ((0 : Nat) = K + 2) from by omega,
            show ¬ ((0 : Nat) > K + 2) from by omega, if_false]
          refine eval_of_step fun j _ _ _ _ _ _ => ?_
          simp only [step, lookup_zero]
          exact obsRefinesK_error_error j
        · have hidx : substTerm (K + 2) (selfCallAt (K + 2)) (.Var n) =
              .Var (if n < K + 2 then n else n - 1) := by
            simp only [substTerm, hslot, if_false]
            by_cases hgt : n > K + 2
            · simp only [hgt, if_true, show ¬ (n < K + 2) from by omega, if_false]
            · simp only [hgt, if_false, show n < K + 2 from by omega, if_true]
          rw [hidx]
          refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
          have hrel := (h.mono (Nat.le_of_lt hj)).other n (by omega) ht hslot hfree
          simp only [step] at hst₁ hst₂ ⊢
          revert hrel hst₁ hst₂
          cases ρ₁.lookup (if n < K + 2 then n else n - 1) <;> cases ρ₂.lookup n <;>
            intro hst₁ hst₂ hrel
          · exact obsRefinesK_error_error j
          · exact absurd hrel id
          · exact absurd hrel id
          · exact ret_obs hrel hst₁ hst₂ hπ
    | .Constant _, _, _, _, _, _, _, _, _ => by
      simp only [substTerm]
      exact eval_of_step fun j _ _ _ hπ hst₁ hst₂ => ret_obs (valueRel_vcon j _) hst₁ hst₂ hπ
    | .Builtin _, _, _, _, _, _, _, _, _ => by
      simp only [substTerm]
      exact eval_of_step fun j _ _ _ hπ hst₁ hst₂ =>
        ret_obs (valueRel_builtin (k := j) trivial) hst₁ hst₂ hπ
    | .Error, _, _, _, _, _, _, _, _ => by
      simp only [substTerm]
      exact eval_of_step fun j _ _ _ _ _ _ => obsRefinesK_error_error j
    | .Lam nm body, K, d, ht, hfree, k, ρ₁, ρ₂, h => by
      simp only [closedAt] at ht
      simp only [freeOf] at hfree
      rw [substTerm_selfCallAt_lam (by omega)]
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      refine ret_obs (valueRel_lam trivial trivial
        fun j' hj' a₁ a₂ ha _ _ => ?_) hst₁ hst₂ hπ
      exact bwd_eval ρU B ρD B' body (K + 1) (d + 1) ht hfree j' (h.extend (by omega) ha)
    | .Delay body, K, d, ht, hfree, k, ρ₁, ρ₂, h => by
      simp only [closedAt] at ht
      simp only [freeOf] at hfree
      simp only [substTerm]
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      exact ret_obs (valueRel_delay trivial trivial
        fun j' hj' => bwd_eval ρU B ρD B' body K d ht hfree j'
          (h.mono (by omega))) hst₁ hst₂ hπ
    | .Apply f x, K, d, ht, hfree, k, ρ₁, ρ₂, h => by
      simp only [closedAt, Bool.and_eq_true] at ht
      simp only [freeOf, Bool.and_eq_true] at hfree
      simp only [substTerm]
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      exact bwd_eval ρU B ρD B' f K d ht.1 hfree.1 j (h.mono (by omega)) j
        (Nat.le_refl _) _ _
        (arg_stackRel (bwd_eval ρU B ρD B' x K d ht.2 hfree.2 j (h.mono (by omega)))
          trivial trivial hπ) hst₁ hst₂
    | .Force e, K, d, ht, hfree, k, ρ₁, ρ₂, h => by
      simp only [closedAt] at ht
      simp only [freeOf] at hfree
      simp only [substTerm]
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      exact bwd_eval ρU B ρD B' e K d ht hfree j (h.mono (by omega)) j
        (Nat.le_refl _) _ _ (force_stackRel hπ) hst₁ hst₂
    | .Constr tag [], _, _, _, _, _, _, _, _ => by
      simp only [substTerm, substTermList]
      exact eval_of_step fun j _ _ _ hπ hst₁ hst₂ =>
        ret_obs (valueRel_constr (k := j) trivial) hst₁ hst₂ hπ
    | .Constr tag (m :: ms), K, d, ht, hfree, k, ρ₁, ρ₂, h => by
      simp only [closedAt, closedAtList, Bool.and_eq_true] at ht
      simp only [freeOf, freeOfList, Bool.and_eq_true] at hfree
      simp only [substTerm, substTermList]
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      exact bwd_eval ρU B ρD B' m K d ht.1 hfree.1 j (h.mono (by omega)) j
        (Nat.le_refl _) _ _
        (constrField_stackRel
          (bwdList_eval ρU B ρD B' ms K d ht.2 hfree.2 j (h.mono (by omega)))
          trivial trivial trivial hπ) hst₁ hst₂
    | .Case scrut alts, K, d, ht, hfree, k, ρ₁, ρ₂, h => by
      simp only [closedAt, Bool.and_eq_true] at ht
      simp only [freeOf, Bool.and_eq_true] at hfree
      simp only [substTerm]
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      exact bwd_eval ρU B ρD B' scrut K d ht.1 hfree.1 j (h.mono (by omega)) j
        (Nat.le_refl _) _ _
        (case_stackRel (altsRel_of_listRel
            (bwdList_eval ρU B ρD B' alts K d ht.2 hfree.2 j (h.mono (by omega))))
          trivial trivial hπ) hst₁ hst₂
  termination_by t => sizeOf t

  theorem bwdList_eval (ρU : CekEnv) (B : Term) (ρD : CekEnv) (B' : Term) :
      ∀ (ts : List Term) (K d : Nat), closedAtList d ts = true → freeOfList (K + 3) ts = true →
      ∀ (k : Nat) {ρ₁ ρ₂ : CekEnv}, BwdRel k K d ρU B ρD B' ρ₁ ρ₂ →
        ListRel (Eval Guard.trivial k ρ₁ ρ₂)
          (substTermList (K + 2) (selfCallAt (K + 2)) ts) ts
    | [], _, _, _, _, _, _, _, _ => by simp only [substTermList]; exact trivial
    | t :: rest, K, d, hts, hfree, k, ρ₁, ρ₂, h => by
      simp only [closedAtList, Bool.and_eq_true] at hts
      simp only [freeOfList, Bool.and_eq_true] at hfree
      simp only [substTermList]
      exact ⟨bwd_eval ρU B ρD B' t K d hts.1 hfree.1 k h,
        bwdList_eval ρU B ρD B' rest K d hts.2 hfree.2 k h⟩
  termination_by ts => sizeOf ts
end

/-- The recursive closures, by induction on the step index. -/
theorem recD_recU {d : Nat} {B : Term} (hB : closedAt (d + 3) B = true)
    (hfree : freeOf 3 B = true) {ρU ρD : CekEnv} :
    ∀ k, EnvRel Guard.trivial k d ρD ρU →
      ValueRel Guard.trivial k (recD ρD (substTerm 2 fixSelfCall B)) (recU ρU B)
  | k, henv => by
    refine valueRel_lam trivial trivial fun j hj a₁ a₂ ha _ _ => ?_
    refine bwd_eval ρU B ρD _ B 0 (d + 3) hB hfree j
      ⟨rfl, rfl, fun i hi => recD_recU hB hfree i (envRel_mono_trivial (by omega) henv),
        fun n hn hnd hne hne' => ?_⟩
    match n, hn with
    | 1, _ => exact ha
    | m + 4, _ =>
      simp only [show ¬ (m + 4 < 0 + 2) from by omega, if_false,
        show m + 4 - 1 = m + 3 from by omega]
      obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := henv (m + 1) (by omega) (by omega)
      show match ρD.lookup (m + 1), ρU.lookup (m + 1) with
        | some v₁, some v₂ => ValueRel Guard.trivial j v₁ v₂
        | none, none => True
        | _, _ => False
      rw [h₁, h₂]
      exact valueRel_mono (by omega) hv
    | 2, _ | 3, _ => omega
  termination_by k => k

/-- The production form refines lowering's redex form. -/
theorem fixLamWrap_backward (d : Nat) (B : Term) (hB : closedAt (d + 3) B = true)
    (hfree : freeOf 3 B = true) : CtxRefines (fixLamWrap B) (fixLamWrapUplc B) := by
  refine Contextual.SoundnessRefines.soundness_of_openRel (W := Guard.trivial) (d := d)
    ?_ (fun _ _ => trivial) trivial trivial ?_
  · intro k j _ ρ₁ ρ₂ henv _ _ _ _ i hi π₁ π₂ _ _ hfn
    refine obsRefinesK_of_steps_left (steps_fixLamWrap π₁ ρ₁ B) ?_
    refine obsRefinesK_of_steps_right (steps_fixLamWrapUplc π₂ ρ₂ B) ?_
    exact hfn i (Nat.le_refl _) _ _
      (recD_recU hB hfree i (envRel_mono_trivial hi henv)) trivial trivial
  · intro C hC
    rw [fill_closedAt_iff] at hC ⊢
    refine ⟨hC.1, ?_⟩
    have h := hC.2
    simp only [fixLamWrap, closedAt, Bool.and_eq_true, decide_eq_true_eq] at h
    have hB' := closedAt_of_substTerm 2 fixSelfCall B (0 + C.binders + 1 + 1)
      (by omega) (by omega) h.2
    simp only [fixLamWrapUplc, closedAt, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨by omega, hB', ?_⟩
    omega

end Moist.Verified.FixLowering
