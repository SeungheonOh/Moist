import Moist.Verified.AdvancedRefinement
import Moist.Verified.InlineSoundness.StrictOcc
import Moist.Verified.Contextual

/-! # Sharing closed values through outer bindings

`Shared K P d t u` says that `u` is `t` with every variable bound outside the
`d` local binders moved past `K` new outer bindings, and with some closed
subterms replaced by the variable holding their value: `P c p` pins the closed
term `c` to outer position `p`.

`shared_lets_ctxRefines`: when every bound term is closed and halts in every
environment, `t` is refined by `u` placed under the bindings (`mkLets`). Each
pinned occurrence is evaluated ahead of time, once; since the bound term is
closed and halts, a later lookup of its value is indistinguishable from
evaluating it in place. -/

namespace Moist.Verified.SharedLets

open Moist.CEK Moist.Plutus.Term
open Moist.Verified (closedAt closedAtList)
open Moist.Verified.Equivalence
open Moist.Verified.Contextual
open Moist.Verified.Contextual.Guarded
open Moist.Verified.Contextual.SoundnessRefines

/-- Position of variable `n` after `K` outer bindings are inserted below the
    `d` innermost binders. -/
def shareShift (d K n : Nat) : Nat := if n ≤ d then n else n + K

theorem shareShift_zero (d K : Nat) : shareShift d K 0 = 0 := by
  simp [shareShift]

theorem shareShift_succ (d K n : Nat) : shareShift (d + 1) K (n + 1) = shareShift d K n + 1 := by
  unfold shareShift
  by_cases h : n ≤ d
  · simp [h]
  · simp [h]; omega

theorem shareShift_of_le {d K n : Nat} (h : n ≤ d) : shareShift d K n = n := by
  simp [shareShift, h]

mutual
  inductive Shared (K : Nat) (P : Term → Nat → Prop) : Nat → Term → Term → Prop
    | var (d n : Nat) : Shared K P d (.Var n) (.Var (shareShift d K n))
    | pin {d : Nat} {c : Term} {p : Nat} : P c p → Shared K P d c (.Var (p + d))
    | constant (d : Nat) (c : Const × BuiltinType) : Shared K P d (.Constant c) (.Constant c)
    | builtin (d : Nat) (b : BuiltinFun) : Shared K P d (.Builtin b) (.Builtin b)
    | error (d : Nat) : Shared K P d .Error .Error
    | lam {d x₁ x₂ : Nat} {b₁ b₂ : Term} :
        Shared K P (d + 1) b₁ b₂ → Shared K P d (.Lam x₁ b₁) (.Lam x₂ b₂)
    | apply {d : Nat} {f₁ f₂ a₁ a₂ : Term} :
        Shared K P d f₁ f₂ → Shared K P d a₁ a₂ → Shared K P d (.Apply f₁ a₁) (.Apply f₂ a₂)
    | force {d : Nat} {e₁ e₂ : Term} : Shared K P d e₁ e₂ → Shared K P d (.Force e₁) (.Force e₂)
    | delay {d : Nat} {e₁ e₂ : Term} : Shared K P d e₁ e₂ → Shared K P d (.Delay e₁) (.Delay e₂)
    | constr {d tag : Nat} {ms₁ ms₂ : List Term} :
        SharedList K P d ms₁ ms₂ → Shared K P d (.Constr tag ms₁) (.Constr tag ms₂)
    | case {d : Nat} {s₁ s₂ : Term} {as₁ as₂ : List Term} :
        Shared K P d s₁ s₂ → SharedList K P d as₁ as₂ → Shared K P d (.Case s₁ as₁) (.Case s₂ as₂)

  inductive SharedList (K : Nat) (P : Term → Nat → Prop) : Nat → List Term → List Term → Prop
    | nil (d : Nat) : SharedList K P d [] []
    | cons {d : Nat} {t₁ t₂ : Term} {ts₁ ts₂ : List Term} :
        Shared K P d t₁ t₂ → SharedList K P d ts₁ ts₂ → SharedList K P d (t₁ :: ts₁) (t₂ :: ts₂)
end

theorem Shared.var_le {K : Nat} {P : Term → Nat → Prop} {d n : Nat} (h : n ≤ d) :
    Shared K P d (.Var n) (.Var n) := by
  have := Shared.var (K := K) (P := P) d n
  rwa [shareShift_of_le h] at this

/-! ## Closedness -/

mutual
  theorem Shared.closedAt {K : Nat} {P : Term → Nat → Prop}
      (hP : ∀ c p, P c p → p ≤ K) :
      ∀ {d m : Nat} {t₁ t₂ : Term}, Shared K P d t₁ t₂ → d ≤ m →
        closedAt m t₁ = true → closedAt (m + K) t₂ = true
    | _, _, _, _, .var d n, _, h => by
      simp only [Moist.Verified.closedAt, decide_eq_true_eq, shareShift] at h ⊢
      split <;> omega
    | _, _, _, _, .pin hp, hdm, _ => by
      have := hP _ _ hp
      simp only [Moist.Verified.closedAt, decide_eq_true_eq]
      omega
    | _, _, _, _, .constant _ _, _, _ | _, _, _, _, .builtin _ _, _, _
    | _, _, _, _, .error _, _, _ => by simp [Moist.Verified.closedAt]
    | _, m, _, _, .lam hb, hdm, h => by
      simp only [Moist.Verified.closedAt] at h ⊢
      have := Shared.closedAt hP hb (m := m + 1) (by omega) h
      rwa [show m + 1 + K = m + K + 1 by omega] at this
    | _, _, _, _, .apply hf ha, hdm, h => by
      simp only [Moist.Verified.closedAt, Bool.and_eq_true] at h ⊢
      exact ⟨Shared.closedAt hP hf hdm h.1, Shared.closedAt hP ha hdm h.2⟩
    | _, _, _, _, .force he, hdm, h | _, _, _, _, .delay he, hdm, h => by
      simp only [Moist.Verified.closedAt] at h ⊢
      exact Shared.closedAt hP he hdm h
    | _, _, _, _, .constr hms, hdm, h => by
      simp only [Moist.Verified.closedAt] at h ⊢
      exact SharedList.closedAt hP hms hdm h
    | _, _, _, _, .case hs has, hdm, h => by
      simp only [Moist.Verified.closedAt, Bool.and_eq_true] at h ⊢
      exact ⟨Shared.closedAt hP hs hdm h.1, SharedList.closedAt hP has hdm h.2⟩

  theorem SharedList.closedAt {K : Nat} {P : Term → Nat → Prop}
      (hP : ∀ c p, P c p → p ≤ K) :
      ∀ {d m : Nat} {ts₁ ts₂ : List Term}, SharedList K P d ts₁ ts₂ → d ≤ m →
        closedAtList m ts₁ = true → closedAtList (m + K) ts₂ = true
    | _, _, _, _, .nil _, _, _ => by simp [Moist.Verified.closedAtList]
    | _, _, _, _, .cons ht hts, hdm, h => by
      simp only [Moist.Verified.closedAtList, Bool.and_eq_true] at h ⊢
      exact ⟨Shared.closedAt hP ht hdm h.1, SharedList.closedAt hP hts hdm h.2⟩
end

/-! ## Environments -/

/-- `v` behaves like a fresh evaluation of `c` in any environment. -/
def Pinned (c : Term) (v : CekValue) (k : Nat) : Prop :=
  ∀ j ≤ k, ∀ (ρ : CekEnv) (π₁ π₂ : Stack), StackRel Guard.trivial j π₁ π₂ →
    ObsRefinesK j (.compute π₁ ρ c) (.ret π₂ v)

/-- Environments for `Shared` terms: positions `1..m` of the left environment
    reappear at `shareShift d K` on the right, and every pinned term's value
    sits at its pinned position above the `d` local binders. -/
def SharedEnv (K : Nat) (P : Term → Nat → Prop) (k d m : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  (∀ n, 0 < n → n ≤ m → ∃ v₁ v₂, ρ₁.lookup n = some v₁ ∧
      ρ₂.lookup (shareShift d K n) = some v₂ ∧ ValueRel Guard.trivial k v₁ v₂) ∧
  ∀ c p, P c p → ∃ v, ρ₂.lookup (p + d) = some v ∧ Pinned c v k

theorem sharedEnv_mono {K : Nat} {P : Term → Nat → Prop} {j k d m : Nat} {ρ₁ ρ₂ : CekEnv}
    (hjk : j ≤ k) (h : SharedEnv K P k d m ρ₁ ρ₂) : SharedEnv K P j d m ρ₁ ρ₂ := by
  refine ⟨fun n hn hnm => ?_, fun c p hp => ?_⟩
  · obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := h.1 n hn hnm
    exact ⟨v₁, v₂, h₁, h₂, valueRel_mono hjk hv⟩
  · obtain ⟨v, hl, hpin⟩ := h.2 c p hp
    exact ⟨v, hl, fun i hi => hpin i (Nat.le_trans hi hjk)⟩

theorem lookup_zero (ρ : CekEnv) : ρ.lookup 0 = none := by
  cases ρ <;> rfl

theorem lookup_extend_succ (ρ : CekEnv) (v : CekValue) {n : Nat} (hn : 1 ≤ n) :
    (ρ.extend v).lookup (n + 1) = ρ.lookup n := by
  match n, hn with
  | k + 1, _ => rfl

theorem sharedEnv_extend {K : Nat} {P : Term → Nat → Prop} {k d m : Nat} {ρ₁ ρ₂ : CekEnv}
    {a₁ a₂ : CekValue} (hP : ∀ c p, P c p → 1 ≤ p)
    (h : SharedEnv K P k d m ρ₁ ρ₂) (ha : ValueRel Guard.trivial k a₁ a₂) :
    SharedEnv K P k (d + 1) (m + 1) (ρ₁.extend a₁) (ρ₂.extend a₂) := by
  refine ⟨fun n hn hnm => ?_, fun c p hp => ?_⟩
  · match n, hn with
    | 1, _ =>
      refine ⟨a₁, a₂, rfl, ?_, ha⟩
      rw [shareShift_of_le (by omega)]; rfl
    | n' + 2, _ =>
      obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := h.1 (n' + 1) (by omega) (by omega)
      refine ⟨v₁, v₂, ?_, ?_, hv⟩
      · rw [lookup_extend_succ ρ₁ a₁ (by omega)]; exact h₁
      · rw [shareShift_succ, lookup_extend_succ ρ₂ a₂ (by simp [shareShift]; split <;> omega)]
        exact h₂
  · obtain ⟨v, hl, hpin⟩ := h.2 c p hp
    refine ⟨v, ?_, hpin⟩
    have := hP c p hp
    rw [show p + (d + 1) = (p + d) + 1 by omega, lookup_extend_succ ρ₂ a₂ (by omega)]
    exact hl

/-! ## The fundamental lemma for `Shared` -/

mutual
  theorem shared_eval {K : Nat} {P : Term → Nat → Prop}
      (hP : ∀ c p, P c p → 1 ≤ p) :
      ∀ {d m : Nat} {t₁ t₂ : Term}, Shared K P d t₁ t₂ → closedAt m t₁ = true →
        ∀ (k : Nat) {ρ₁ ρ₂ : CekEnv}, SharedEnv K P k d m ρ₁ ρ₂ →
          Eval Guard.trivial k ρ₁ ρ₂ t₁ t₂
    | _, _, _, _, .var d n, ht, k, ρ₁, ρ₂, henv => by
      refine eval_of_step fun j hj π₁ π₂ hπ _ _ => ?_
      simp only [Moist.Verified.closedAt, decide_eq_true_eq] at ht
      by_cases hn : n = 0
      · subst hn
        simp only [step, shareShift_zero, lookup_zero]
        exact obsRefinesK_error_error j
      · obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := henv.1 n (by omega) ht
        simp only [step, h₁, h₂]
        exact ret_obs (valueRel_mono (by omega) hv) trivial trivial hπ
    | _, _, _, _, .pin (c := c) (p := p) hp, _, k, ρ₁, ρ₂, henv => by
      intro j hj π₁ π₂ hπ _ _
      obtain ⟨v, hl, hpin⟩ := henv.2 c p hp
      refine obsRefinesK_of_steps_right (n := 1) ?_ (hpin j hj ρ₁ π₁ π₂ hπ)
      simp [steps, step, hl]
    | _, _, _, _, .constant _ _, _, _, _, _, _ =>
      eval_of_step fun j _ _ _ hπ _ _ => ret_obs (valueRel_vcon j _) trivial trivial hπ
    | _, _, _, _, .builtin _ _, _, _, _, _, _ =>
      eval_of_step fun j _ _ _ hπ _ _ =>
        ret_obs (valueRel_builtin (k := j) trivial) trivial trivial hπ
    | _, _, _, _, .error _, _, _, _, _, _ =>
      eval_of_step fun j _ _ _ _ _ _ => obsRefinesK_error_error j
    | _, _, _, _, .lam hb, ht, k, ρ₁, ρ₂, henv => by
      simp only [Moist.Verified.closedAt] at ht
      refine eval_of_step fun j hj π₁ π₂ hπ _ _ => ?_
      refine ret_obs (valueRel_lam trivial trivial fun j' hj' a₁ a₂ ha _ _ => ?_) trivial trivial hπ
      exact shared_eval hP hb ht j'
        (sharedEnv_extend hP (sharedEnv_mono (by omega) henv) ha)
    | _, _, _, _, .delay hb, ht, k, ρ₁, ρ₂, henv => by
      simp only [Moist.Verified.closedAt] at ht
      refine eval_of_step fun j hj π₁ π₂ hπ _ _ => ?_
      exact ret_obs (valueRel_delay trivial trivial
        fun j' hj' => shared_eval hP hb ht j' (sharedEnv_mono (by omega) henv)) trivial trivial hπ
    | _, _, _, _, .apply hf ha, ht, k, ρ₁, ρ₂, henv => by
      simp only [Moist.Verified.closedAt, Bool.and_eq_true] at ht
      refine eval_of_step fun j hj π₁ π₂ hπ _ _ => ?_
      exact shared_eval hP hf ht.1 j (sharedEnv_mono (by omega) henv) j (Nat.le_refl _) _ _
        (arg_stackRel (shared_eval hP ha ht.2 j (sharedEnv_mono (by omega) henv))
          trivial trivial hπ) trivial trivial
    | _, _, _, _, .force he, ht, k, ρ₁, ρ₂, henv => by
      simp only [Moist.Verified.closedAt] at ht
      refine eval_of_step fun j hj π₁ π₂ hπ _ _ => ?_
      exact shared_eval hP he ht j (sharedEnv_mono (by omega) henv) j (Nat.le_refl _) _ _
        (force_stackRel hπ) trivial trivial
    | _, _, _, _, .constr (.nil _), _, _, _, _, _ =>
      eval_of_step fun j _ _ _ hπ _ _ =>
        ret_obs (valueRel_constr (k := j) trivial) trivial trivial hπ
    | _, _, _, _, .constr (.cons hm hms), ht, k, ρ₁, ρ₂, henv => by
      simp only [Moist.Verified.closedAt, Moist.Verified.closedAtList, Bool.and_eq_true] at ht
      refine eval_of_step fun j hj π₁ π₂ hπ _ _ => ?_
      exact shared_eval hP hm ht.1 j (sharedEnv_mono (by omega) henv) j (Nat.le_refl _) _ _
        (constrField_stackRel (shared_evalList hP hms ht.2 j (sharedEnv_mono (by omega) henv))
          trivial trivial trivial hπ) trivial trivial
    | _, _, _, _, .case hs has, ht, k, ρ₁, ρ₂, henv => by
      simp only [Moist.Verified.closedAt, Bool.and_eq_true] at ht
      refine eval_of_step fun j hj π₁ π₂ hπ _ _ => ?_
      exact shared_eval hP hs ht.1 j (sharedEnv_mono (by omega) henv) j (Nat.le_refl _) _ _
        (case_stackRel (altsRel_of_listRel
            (shared_evalList hP has ht.2 j (sharedEnv_mono (by omega) henv)))
          trivial trivial hπ) trivial trivial

  theorem shared_evalList {K : Nat} {P : Term → Nat → Prop}
      (hP : ∀ c p, P c p → 1 ≤ p) :
      ∀ {d m : Nat} {ts₁ ts₂ : List Term}, SharedList K P d ts₁ ts₂ →
        closedAtList m ts₁ = true →
        ∀ (k : Nat) {ρ₁ ρ₂ : CekEnv}, SharedEnv K P k d m ρ₁ ρ₂ →
          ListRel (Eval Guard.trivial k ρ₁ ρ₂) ts₁ ts₂
    | _, _, _, _, .nil _, _, _, _, _, _ => trivial
    | _, _, _, _, .cons ht hts, h, k, _, _, henv => by
      simp only [Moist.Verified.closedAtList, Bool.and_eq_true] at h
      exact ⟨shared_eval hP ht h.1 k henv, shared_evalList hP hts h.2 k henv⟩
end

/-! ## Evaluating the outer bindings -/

/-- `rhs₁, …, rhsₙ` bound around `body`, the first binding outermost. -/
def mkLets : List Term → Term → Term
  | [], body => body
  | rhs :: rest, body => .Apply (.Lam 0 (mkLets rest body)) rhs

/-- Extend an environment by values, the first one deepest. -/
def extendAll (ρ : CekEnv) : List CekValue → CekEnv
  | [] => ρ
  | v :: vs => extendAll (ρ.extend v) vs

/-- A term returning a value from every environment. -/
def Halts (t : Term) : Prop := ∀ ρ : CekEnv, ∃ v, Reaches (.compute [] ρ t) (.halt v)

theorem mkLets_closedAt {ts : List Term} (hts : ∀ c ∈ ts, closedAt 0 c = true) :
    ∀ {depth : Nat} {body : Term}, closedAt (depth + ts.length) body = true →
      closedAt depth (mkLets ts body) = true := by
  induction ts with
  | nil => intro depth body h; simpa [mkLets] using h
  | cons c rest ih =>
    intro depth body h
    simp only [mkLets, Moist.Verified.closedAt, Bool.and_eq_true]
    refine ⟨ih (fun c' hc' => hts c' (.tail _ hc')) ?_,
      Moist.Verified.Contextual.closedAt_mono (hts c (.head _)) (Nat.zero_le _)⟩
    simpa [Nat.add_assoc, Nat.add_comm 1] using h

theorem extendAll_lookup_shift : ∀ (vals : List CekValue) (ρ : CekEnv) {n : Nat}, 1 ≤ n →
    (extendAll ρ vals).lookup (n + vals.length) = ρ.lookup n
  | [], _, _, _ => rfl
  | v :: vs, ρ, n, hn => by
    simp only [extendAll, List.length_cons]
    rw [show n + (vs.length + 1) = (n + 1) + vs.length by omega,
      extendAll_lookup_shift vs (ρ.extend v) (by omega), lookup_extend_succ ρ v hn]

theorem extendAll_lookup_get : ∀ (vals : List CekValue) (ρ : CekEnv) {j : Nat}
    (hj : j < vals.length), (extendAll ρ vals).lookup (vals.length - j) = some vals[j]
  | [], _, _, hj => absurd hj (Nat.not_lt_zero _)
  | v :: vs, ρ, 0, _ => by
    simp only [extendAll, List.length_cons, Nat.sub_zero, List.getElem_cons_zero]
    rw [show vs.length + 1 = 1 + vs.length by omega, extendAll_lookup_shift vs _ (Nat.le_refl _)]
    rfl
  | v :: vs, ρ, j + 1, hj => by
    simp only [extendAll, List.length_cons, List.getElem_cons_succ]
    rw [show vs.length + 1 - (j + 1) = vs.length - j by omega]
    exact extendAll_lookup_get vs (ρ.extend v) (by simp at hj; omega)

/-- Dropping a prefix of the right run keeps the observation. -/
theorem obsRefinesK_drop_right {k n : Nat} {s₁ s₂ : State}
    (h : ObsRefinesK k s₁ s₂) : ObsRefinesK k s₁ (steps n s₂) := by
  refine ⟨fun v hv => ?_, fun m hm herr => ?_⟩
  · obtain ⟨v', hv'⟩ := h.1 v hv
    exact ⟨v', (AdvancedRefinement.reaches_after_prefix n rfl).mp hv'⟩
  · exact (AdvancedRefinement.reaches_after_prefix n rfl).mp (h.2 m hm herr)

/-- The value of a closed halting term is pinned to it. -/
theorem pinned_of_halts {c : Term} {ρ₀ : CekEnv} {v : CekValue}
    (hc : closedAt 0 c = true) (hv : Reaches (.compute [] ρ₀ c) (.halt v)) (k : Nat) :
    Pinned c v k := by
  intro j _ ρ π₁ π₂ hπ
  have related : ObsRefinesK j (.compute π₁ ρ c) (.compute π₂ ρ₀ c) :=
    FundamentalRefines.ftlr 0 c hc j j (Nat.le_refl _) ρ ρ₀
      (fun n hn hn0 => absurd hn0 (by omega)) j (Nat.le_refl _) π₁ π₂
      (stackRefK_iff_stackRel.mpr hπ)
  obtain ⟨m, hm⟩ := InlineSoundness.StrictOcc.halt_on_all_stacks hv π₂
  rw [← hm]
  exact obsRefinesK_drop_right related

theorem mkLets_steps (body : Term) : ∀ (ts : List Term) (ρ : CekEnv) (π : Stack),
    (∀ c ∈ ts, closedAt 0 c = true ∧ Halts c) →
    ∃ vals : List CekValue, vals.length = ts.length ∧
      (∀ j (h₁ : j < ts.length) (h₂ : j < vals.length) k, Pinned ts[j] vals[j] k) ∧
      ∃ n, steps n (.compute π ρ (mkLets ts body)) = .compute π (extendAll ρ vals) body
  | [], ρ, _, _ => ⟨[], rfl, fun _ h => absurd h (Nat.not_lt_zero _), 0, rfl⟩
  | c :: rest, ρ, π, hts => by
    obtain ⟨hc, hhalts⟩ := hts c (.head _)
    obtain ⟨v, hv⟩ := hhalts ρ
    obtain ⟨m, hm⟩ := InlineSoundness.StrictOcc.halt_on_all_stacks hv
      (.funV (.VLam (mkLets rest body) ρ) :: π)
    obtain ⟨vals, hlen, hpins, n, hn⟩ :=
      mkLets_steps body rest (ρ.extend v) π (fun c' hc' => hts c' (.tail _ hc'))
    refine ⟨v :: vals, by simp [hlen], fun j h₁ h₂ k => ?_, 3 + (m + (1 + n)), ?_⟩
    · cases j with
      | zero => exact pinned_of_halts hc hv k
      | succ j =>
        simp only [List.getElem_cons_succ]
        exact hpins j (by simp at h₁; omega) (by simp at h₂; omega) k
    · rw [steps_trans, show steps 3 (.compute π ρ (mkLets (c :: rest) body)) =
          .compute (.funV (.VLam (mkLets rest body) ρ) :: π) ρ c from rfl,
        steps_trans, hm, steps_trans]
      exact hn

/-! ## Contextual refinement -/

/-- Pins drawn from the bound terms: the `j`-th of `K` bindings sits at outer
    position `K - j`. -/
def BindingPins (ts : List Term) (c : Term) (p : Nat) : Prop :=
  ∃ j, ∃ h : j < ts.length, ts[j] = c ∧ p = ts.length - j

theorem shared_lets_obs {ts : List Term} (hts : ∀ c ∈ ts, closedAt 0 c = true ∧ Halts c)
    {D : Nat} {t u : Term} (ht : closedAt D t = true)
    (hrel : Shared ts.length (BindingPins ts) 0 t u)
    (ρ : CekEnv) (π : Stack) (hρ : BetaValueRefines.EnvWellFormed D ρ)
    (hπ : BetaValueRefines.StackWellFormed π) :
    ObsRefines (.compute π ρ t) (.compute π ρ (mkLets ts u)) := by
  obtain ⟨vals, hlen, hpins, n, hn⟩ := mkLets_steps u ts ρ π hts
  have hP : ∀ c p, BindingPins ts c p → 1 ≤ p := by
    rintro c p ⟨j, hj, _, rfl⟩; omega
  have henv : ∀ k, SharedEnv ts.length (BindingPins ts) k 0 D ρ (extendAll ρ vals) := by
    intro k
    refine ⟨fun m hm hmD => ?_, fun c p hp => ?_⟩
    · obtain ⟨v, hl, hwf⟩ := BetaValueRefines.envWellFormed_lookup D hρ hm hmD
      refine ⟨v, v, hl, ?_, (valueRel_trivial k v v).mpr
        (BetaValueRefines.valueRefinesK_refl k v hwf)⟩
      rw [show shareShift 0 ts.length m = m + vals.length by simp [shareShift, hlen]; omega,
        extendAll_lookup_shift vals ρ hm]
      exact hl
    · obtain ⟨j, hj, rfl, rfl⟩ := hp
      refine ⟨vals[j]'(by omega), ?_, hpins j hj (by omega) k⟩
      rw [Nat.add_zero, ← hlen]
      exact extendAll_lookup_get vals ρ (by omega)
  have hobs : ∀ k, ObsRefinesK k (.compute π ρ t) (.compute π (extendAll ρ vals) u) :=
    fun k => shared_eval hP hrel ht k (henv k) k (Nat.le_refl _) π π
      (stackRefK_iff_stackRel.mp (BetaValueRefines.stackRefK_refl k π hπ)) trivial trivial
  constructor
  · rintro ⟨v, N, hN⟩
    obtain ⟨v', N', hN'⟩ := (hobs N).1 v ⟨N, Nat.le_refl _, hN⟩
    exact ⟨v', n + N', by rw [steps_trans, hn]; exact hN'⟩
  · rintro ⟨N, hN⟩
    obtain ⟨N', hN'⟩ := (hobs N).2 N (Nat.le_refl _) hN
    exact ⟨n + N', by rw [steps_trans, hn]; exact hN'⟩

/-- Closed halting terms bound outside, with pinned occurrences replaced by
    their variables, refine the original term. -/
theorem shared_lets_ctxRefines {ts : List Term} (hts : ∀ c ∈ ts, closedAt 0 c = true ∧ Halts c)
    {D : Nat} {t u : Term} (ht : closedAt D t = true)
    (hrel : Shared ts.length (BindingPins ts) 0 t u) :
    CtxRefines t (mkLets ts u) := by
  have hPK : ∀ c p, BindingPins ts c p → p ≤ ts.length := by
    rintro c p ⟨j, hj, _, rfl⟩; omega
  apply AdvancedRefinement.contextual_of_wf_refinement ht
  · intro depth hdepth
    exact mkLets_closedAt (fun c hc => (hts c hc).1)
      (Shared.closedAt hPK hrel (Nat.zero_le _) hdepth)
  · intro ρ π hρ _ hπ
    exact shared_lets_obs hts ht hrel ρ π hρ hπ

end Moist.Verified.SharedLets
