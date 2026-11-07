import Moist.Verified.FundamentalRefines
import Moist.Verified.Purity
import Moist.Verified.InlineSoundness.StrictOcc
import Moist.Verified.MIR.Hoist
import Moist.MIR.Optimize.Advanced.DelaySharing
import Moist.Verified.AdvancedTraversal
import Moist.Verified.HygieneSoundness
import Moist.Verified.DeadFixSoundness
import Moist.MIR.Optimize.Advanced

/-! # Soundness of delayed-value sharing

`let v = delay d in s` with pure `d` and every use of `v` forced becomes
`let v = d in s'`, where `s'` replaces each `force v` by `v`.

At the UPLC level `ForceShare d p t t'` says that `t'` is `t` with every
`force (var p)` replaced by `var p` and with no other occurrence of `var p`.
`forceShare_eval` is the fundamental property of this relation when position
`p` holds a delay on the left whose forcing refines returning the right value
(`DelayShare`). The left delay is built from `d` in the environment of the
binding, the right value is the result of `d` there; `d` halts because it is
pure, and by determinism re-forcing the delay recomputes that value.
-/

namespace Moist.Verified.DelaySharing

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified (closedAt closedAtList)
open Moist.Verified.Equivalence
open Moist.Verified.Contextual.SoundnessRefines
open Moist.Verified.Contextual.Guarded

/-! ## The term relation -/

mutual
/-- `ForceShare d p t₁ t₂`: `t₂` is `t₁` with `force (var p)` replaced by
    `var p`; `var p` occurs in `t₁` only under such a force. Both terms are
    closed at depth `d`. -/
inductive ForceShare : Nat → Nat → Term → Term → Prop
  | forced {d p : Nat} : 0 < p → p ≤ d → ForceShare d p (.Force (.Var p)) (.Var p)
  | var {d p n : Nat} : 0 < n → n ≤ d → n ≠ p → ForceShare d p (.Var n) (.Var n)
  | constant {d p : Nat} (c : Const × BuiltinType) : ForceShare d p (.Constant c) (.Constant c)
  | builtin {d p : Nat} (b : BuiltinFun) : ForceShare d p (.Builtin b) (.Builtin b)
  | error {d p : Nat} : ForceShare d p .Error .Error
  | lam {d p x : Nat} {b₁ b₂ : Term} :
      ForceShare (d + 1) (p + 1) b₁ b₂ → ForceShare d p (.Lam x b₁) (.Lam x b₂)
  | apply {d p : Nat} {f₁ f₂ a₁ a₂ : Term} :
      ForceShare d p f₁ f₂ → ForceShare d p a₁ a₂ →
      ForceShare d p (.Apply f₁ a₁) (.Apply f₂ a₂)
  | force {d p : Nat} {e₁ e₂ : Term} :
      ForceShare d p e₁ e₂ → ForceShare d p (.Force e₁) (.Force e₂)
  | delay {d p : Nat} {e₁ e₂ : Term} :
      ForceShare d p e₁ e₂ → ForceShare d p (.Delay e₁) (.Delay e₂)
  | constr {d p tag : Nat} {as₁ as₂ : List Term} :
      ForceShareList d p as₁ as₂ → ForceShare d p (.Constr tag as₁) (.Constr tag as₂)
  | case {d p : Nat} {s₁ s₂ : Term} {as₁ as₂ : List Term} :
      ForceShare d p s₁ s₂ → ForceShareList d p as₁ as₂ →
      ForceShare d p (.Case s₁ as₁) (.Case s₂ as₂)

inductive ForceShareList : Nat → Nat → List Term → List Term → Prop
  | nil {d p : Nat} : ForceShareList d p [] []
  | cons {d p : Nat} {a b : Term} {as bs : List Term} :
      ForceShare d p a b → ForceShareList d p as bs → ForceShareList d p (a :: as) (b :: bs)
end

mutual
theorem ForceShare.closedAt_right {d p : Nat} {t₁ t₂ : Term} :
    ForceShare d p t₁ t₂ → ∀ k, closedAt k t₁ = true → closedAt k t₂ = true
  | .forced _ _, k, h => by simpa [closedAt] using h
  | .var _ _ _, _, h => h
  | .constant _, _, h => h
  | .builtin _, _, h => h
  | .error, _, h => h
  | .lam hb, k, h => by
    simp only [closedAt] at h ⊢; exact hb.closedAt_right (k + 1) h
  | .apply hf ha, k, h => by
    simp only [closedAt, Bool.and_eq_true] at h ⊢
    exact ⟨hf.closedAt_right k h.1, ha.closedAt_right k h.2⟩
  | .force he, k, h => by simp only [closedAt] at h ⊢; exact he.closedAt_right k h
  | .delay he, k, h => by simp only [closedAt] at h ⊢; exact he.closedAt_right k h
  | .constr has, k, h => by simp only [closedAt] at h ⊢; exact has.closedAt_right k h
  | .case hs has, k, h => by
    simp only [closedAt, Bool.and_eq_true] at h ⊢
    exact ⟨hs.closedAt_right k h.1, has.closedAt_right k h.2⟩

theorem ForceShareList.closedAt_right {d p : Nat} {l₁ l₂ : List Term} :
    ForceShareList d p l₁ l₂ → ∀ k, closedAtList k l₁ = true → closedAtList k l₂ = true
  | .nil, _, h => h
  | .cons ha has, k, h => by
    simp only [closedAtList, Bool.and_eq_true] at h ⊢
    exact ⟨ha.closedAt_right k h.1, has.closedAt_right k h.2⟩
end

/-! ## The environment relation -/

/-- The left value is a delay whose forcing refines returning the right value. -/
def DelayShare (k : Nat) (v₁ v₂ : CekValue) : Prop :=
  ∃ body ρ, v₁ = .VDelay body ρ ∧
    ∀ j ≤ k, ∀ π₁ π₂, StackRel Guard.trivial j π₁ π₂ →
      ObsRefinesK j (.compute π₁ ρ body) (.ret π₂ v₂)

/-- Positions `1..d` are related; position `p` by `DelayShare`, the others by
    the value relation. -/
def ShareEnv (k d p : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d → ∃ v₁ v₂, ρ₁.lookup n = some v₁ ∧ ρ₂.lookup n = some v₂ ∧
    (n = p → DelayShare k v₁ v₂) ∧ (n ≠ p → ValueRel Guard.trivial k v₁ v₂)

theorem delayShare_mono {j k : Nat} (hjk : j ≤ k) {v₁ v₂ : CekValue}
    (h : DelayShare k v₁ v₂) : DelayShare j v₁ v₂ := by
  obtain ⟨body, ρ, rfl, hrel⟩ := h
  exact ⟨body, ρ, rfl, fun i hi => hrel i (Nat.le_trans hi hjk)⟩

theorem shareEnv_mono {j k d p : Nat} (hjk : j ≤ k) {ρ₁ ρ₂ : CekEnv}
    (h : ShareEnv k d p ρ₁ ρ₂) : ShareEnv j d p ρ₁ ρ₂ := by
  intro n hn hnd
  obtain ⟨v₁, v₂, h₁, h₂, hp, hq⟩ := h n hn hnd
  exact ⟨v₁, v₂, h₁, h₂, fun e => delayShare_mono hjk (hp e), fun e => valueRel_mono hjk (hq e)⟩

private theorem extend_lookup_succ (ρ : CekEnv) (v : CekValue) (m : Nat) (hm : m ≥ 1) :
    (ρ.extend v).lookup (m + 1) = ρ.lookup m := by
  match m, hm with
  | k + 1, _ => rfl

theorem shareEnv_extend {k d p : Nat} (hp : 0 < p) {ρ₁ ρ₂ : CekEnv} {a₁ a₂ : CekValue}
    (h : ShareEnv k d p ρ₁ ρ₂) (ha : ValueRel Guard.trivial k a₁ a₂) :
    ShareEnv k (d + 1) (p + 1) (ρ₁.extend a₁) (ρ₂.extend a₂) := by
  intro n hn hnd
  by_cases h1 : n = 1
  · subst h1
    exact ⟨a₁, a₂, rfl, rfl, fun e => absurd e (by omega), fun _ => ha⟩
  · obtain ⟨v₁, v₂, h₁, h₂, hq, hr⟩ := h (n - 1) (by omega) (by omega)
    have e : n = (n - 1) + 1 := by omega
    refine ⟨v₁, v₂, ?_, ?_, fun e' => hq (by omega), fun e' => hr (by omega)⟩
    · rw [e, extend_lookup_succ _ _ _ (by omega)]; exact h₁
    · rw [e, extend_lookup_succ _ _ _ (by omega)]; exact h₂

/-! ## Fundamental property -/

private theorem forceShareList_listRel {d p : Nat} {R : Term → Term → Prop}
    (h : ∀ {a₁ a₂}, ForceShare d p a₁ a₂ → R a₁ a₂) :
    ∀ {l₁ l₂ : List Term}, ForceShareList d p l₁ l₂ → ListRel R l₁ l₂
  | _, _, .nil => trivial
  | _, _, .cons hh ht => ⟨h hh, forceShareList_listRel h ht⟩

theorem forceShare_eval (k : Nat) :
    ∀ {d p : Nat} {ρ₁ ρ₂ : CekEnv}, 0 < p → ShareEnv k d p ρ₁ ρ₂ →
      ∀ {t₁ t₂ : Term}, ForceShare d p t₁ t₂ → Eval Guard.trivial k ρ₁ ρ₂ t₁ t₂ := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro d p ρ₁ ρ₂ hp hρ t₁ t₂ ht
  have sub : ∀ j < k, ∀ {a₁ a₂}, ForceShare d p a₁ a₂ → Eval Guard.trivial j ρ₁ ρ₂ a₁ a₂ :=
    fun j hj _ _ h => ih j hj hp (shareEnv_mono (by omega) hρ) h
  cases ht with
  | forced hp0 hpd =>
    refine eval_of_step fun j hj π₁ π₂ hπ _ _ => ?_
    obtain ⟨v₁, v₂, h₁, h₂, hdel, _⟩ := hρ p hp0 hpd
    obtain ⟨body, ρ, rfl, hrel⟩ := hdel rfl
    simp only [step, h₂]
    exact obsRefinesK_of_steps_left (n := 2) (by simp [steps, step, h₁])
      (hrel j (by omega) π₁ π₂ hπ)
  | var hn hnd hne =>
    refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
    obtain ⟨v₁, v₂, h₁, h₂, _, hv⟩ := hρ _ hn hnd
    simp only [step, h₁, h₂] at hst₁ hst₂ ⊢
    exact ret_obs (valueRel_mono (by omega) (hv hne)) hst₁ hst₂ hπ
  | constant c =>
    refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
    exact ret_obs (valueRel_vcon j c.1) hst₁ hst₂ hπ
  | builtin b =>
    refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
    exact ret_obs (valueRel_builtin (k := j) trivial) hst₁ hst₂ hπ
  | error =>
    exact eval_of_step fun j _ _ _ _ _ _ => obsRefinesK_error_error j
  | lam hb =>
    refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
    refine ret_obs (valueRel_lam trivial trivial ?_) hst₁ hst₂ hπ
    intro j' hj' a₁ a₂ ha _ _
    exact ih j' (by omega) (by omega) (shareEnv_extend hp (shareEnv_mono (by omega) hρ) ha) hb
  | delay hb =>
    refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
    exact ret_obs (valueRel_delay trivial trivial fun j' hj' => sub j' (by omega) hb)
      hst₁ hst₂ hπ
  | apply hf ha =>
    refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
    exact sub j hj hf j (Nat.le_refl _) _ _
      (arg_stackRel (sub j hj ha) trivial trivial hπ) hst₁ hst₂
  | force he =>
    refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
    exact sub j hj he j (Nat.le_refl _) _ _ (force_stackRel hπ) hst₁ hst₂
  | constr hms =>
    refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
    cases hms with
    | nil => exact ret_obs (valueRel_constr (k := j) trivial) hst₁ hst₂ hπ
    | cons hm hms =>
      exact sub j hj hm j (Nat.le_refl _) _ _
        (constrField_stackRel (forceShareList_listRel (sub j hj) hms) trivial
          trivial trivial hπ) hst₁ hst₂
  | case hs has =>
    refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
    exact sub j hj hs j (Nat.le_refl _) _ _
      (case_stackRel (altsRel_of_listRel (forceShareList_listRel (sub j hj) has))
        trivial trivial hπ) hst₁ hst₂

/-! ## The shared binding -/

private theorem steps_fixed {t : State} (ht : step t = t) : ∀ n, steps n t = t
  | 0 => rfl
  | n + 1 => by simp only [steps, ht]; exact steps_fixed ht n

/-- Running the right state forward preserves refinement: halt and error are
    absorbing and the machine is deterministic. -/
theorem obsRefinesK_forward_right {k n : Nat} {s₁ s₂ s₂' : State}
    (h_steps : steps n s₂ = s₂') (h : ObsRefinesK k s₁ s₂) : ObsRefinesK k s₁ s₂' := by
  have after : ∀ {m : Nat} {t : State}, step t = t → steps m s₂ = t → steps (m - n) s₂' = t := by
    intro m t ht hm
    subst h_steps
    by_cases hmn : m ≤ n
    · rw [Nat.sub_eq_zero_of_le hmn]
      show steps n s₂ = t
      rw [show n = m + (n - m) by omega, steps_trans, hm]; exact steps_fixed ht _
    · rw [← steps_trans, show n + (m - n) = m by omega, hm]
  refine ⟨fun v hv => ?_, fun m hm herr => ?_⟩
  · obtain ⟨v', m, hm⟩ := h.1 v hv
    exact ⟨v', m - n, after rfl hm⟩
  · obtain ⟨m', hm'⟩ := h.2 m hm herr
    exact ⟨m' - n, after rfl hm'⟩

/-- Binding a delay that is only forced refines binding its value, provided
    the delayed term returns a value in every well-sized environment. -/
theorem share_let_openRefines {d : Nat} {S S' D : Term}
    (hS : ForceShare (d + 1) 1 S S') (hD : closedAt d D = true)
    (hhalt : ∀ ρ, (∀ n, 0 < n → n ≤ d → ∃ v, ρ.lookup n = some v) →
      ∃ w, ∀ π, ∃ m, steps m (.compute π ρ D) = .ret π w) :
    OpenRefines d (.Apply (.Lam 0 S) (.Delay D)) (.Apply (.Lam 0 S') D) := by
  intro k j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  obtain ⟨w, hw⟩ := hhalt ρ₂ fun n hn hnd =>
    let ⟨_, v₂, _, h₂, _⟩ := henv n hn hnd; ⟨v₂, h₂⟩
  obtain ⟨m, hm⟩ := hw (.funV (.VLam S' ρ₂) :: π₂)
  have hright : steps (3 + (m + 1)) (.compute π₂ ρ₂ (.Apply (.Lam 0 S') D)) =
      .compute π₂ (ρ₂.extend w) S' := by
    rw [steps_trans, steps_trans]
    have h3 : steps 3 (.compute π₂ ρ₂ (.Apply (.Lam 0 S') D)) =
        .compute (.funV (.VLam S' ρ₂) :: π₂) ρ₂ D := rfl
    rw [h3, hm]; rfl
  have hleft : steps 5 (.compute π₁ ρ₁ (.Apply (.Lam 0 S) (.Delay D))) =
      .compute π₁ (ρ₁.extend (.VDelay D ρ₁)) S := rfl
  refine obsRefinesK_of_steps_left hleft (obsRefinesK_of_steps_right hright ?_)
  have hshare : ShareEnv i (d + 1) 1 (ρ₁.extend (.VDelay D ρ₁)) (ρ₂.extend w) := by
    intro n hn hnd
    by_cases h1 : n = 1
    · subst h1
      refine ⟨_, _, rfl, rfl, fun _ => ?_, fun e => absurd rfl e⟩
      refine ⟨D, ρ₁, rfl, fun j' hj' π₁' π₂' hπ' => ?_⟩
      obtain ⟨m', hm'⟩ := hw π₂'
      exact obsRefinesK_forward_right hm'
        (Moist.Verified.FundamentalRefines.ftlr d D hD j j (Nat.le_refl _) ρ₁ ρ₂ henv j'
          (by omega) π₁' π₂' (stackRefK_iff_stackRel.mpr hπ'))
    · obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := henv (n - 1) (by omega) (by omega)
      have e : n = (n - 1) + 1 := by omega
      refine ⟨v₁, v₂, ?_, ?_, fun e' => absurd e' h1, fun _ => ?_⟩
      · rw [e, extend_lookup_succ _ _ _ (by omega)]; exact h₁
      · rw [e, extend_lookup_succ _ _ _ (by omega)]; exact h₂
      · exact (valueRel_trivial i v₁ v₂).mpr (valueRefinesK_mono hi _ _ hv)
  exact forceShare_eval i (by omega) hshare hS i (Nat.le_refl _) π₁ π₂
    (stackRefK_iff_stackRel.mp hπ) trivial trivial

/-! ## Lowering `removeForces` -/

section Lowering

open Moist.MIR
  (Expr VarId lowerTotal lowerTotalList lowerTotalLet expandFix expandFixList expandFixBinds
   envLookupT fixLamWrapUplc)
open Moist.MIR.Advanced
  (onlyForced onlyForcedList onlyForcedBinds removeForces removeForcesList removeForcesBinds)

/-- `v` is the variable that `env` resolves to position `pos`. -/
def Visible (env : List VarId) (v : VarId) (pos : Nat) : Prop :=
  ∀ y, envLookupT env y = some pos ↔ (v == y) = true

theorem visible_cons {env : List VarId} {v x : VarId} {pos : Nat}
    (hne : (v == x) = false) (h : Visible env v pos) : Visible (x :: env) v (pos + 1) := by
  intro y
  cases hxy : (x == y) with
  | true =>
    have hlook : envLookupT (x :: env) y = some 0 := by
      simp [envLookupT, Moist.MIR.envLookupT.go, hxy]
    rw [hlook]
    constructor
    · intro e; cases e
    · intro hvy
      rw [Moist.MIR.VarId.beq_true_iff] at hvy hxy
      rw [Moist.MIR.VarId.beq_false_iff] at hne
      exfalso; rcases hne with hne | hne
      · exact hne (hvy.1.trans hxy.1.symm)
      · exact hne (hvy.2.trans hxy.2.symm)
  | false =>
    rw [Moist.MIR.envLookupT_cons_neq x y env hxy, ← h y]
    cases envLookupT env y <;> simp

theorem visible_head (env : List VarId) (v : VarId) : Visible (v :: env) v 0 := by
  intro y
  cases hvy : (v == y) with
  | true => simp [envLookupT, Moist.MIR.envLookupT.go, hvy]
  | false =>
    rw [Moist.MIR.envLookupT_cons_neq v y env hvy]
    cases envLookupT env y <;> simp

private theorem ne_of_bne {a b : VarId} (h : (a != b) = true) : (a == b) = false := by
  unfold bne at h; cases hab : (a == b) <;> simp_all

private theorem removeForces_force_of_nonvar (v : VarId) {inner : Expr}
    (h : ∀ x, inner ≠ .Var x) : removeForces v (.Force inner) = .Force (removeForces v inner) := by
  cases inner with
  | Var x => exact absurd rfl (h x)
  | _ => simp [removeForces]

private theorem onlyForced_force_of_nonvar (v : VarId) {inner : Expr}
    (h : ∀ x, inner ≠ .Var x) : onlyForced v (.Force inner) = onlyForced v inner := by
  cases inner with
  | Var x => exact absurd rfl (h x)
  | _ => simp [onlyForced]

private theorem expandFix_nonvar {inner : Expr} (h : ∀ x, inner ≠ .Var x) :
    ∀ x, expandFix inner ≠ .Var x := by
  intro x e
  cases inner with
  | Var y => exact h y rfl
  | Fix f body => cases body <;> simp [expandFix] at e
  | _ => simp [expandFix] at e

mutual
theorem removeForces_lower (v : VarId) (e : Expr) (env : List VarId) (pos : Nat) (t : Term)
    (hvis : Visible env v pos) (honly : onlyForced v e = true)
    (hlow : lowerTotal env (expandFix e) = some t) :
    ∃ t', lowerTotal env (expandFix (removeForces v e)) = some t' ∧
      ForceShare env.length (pos + 1) t t' := by
  match e with
  | .Var x =>
    simp only [onlyForced] at honly
    have hvx := ne_of_bne honly
    simp only [expandFix, lowerTotal] at hlow
    split at hlow
    · rename_i idx hidx
      injection hlow with hlow; subst hlow
      refine ⟨_, by simp only [removeForces, expandFix, lowerTotal, hidx], ForceShare.var
        (by omega) (by have := Moist.MIR.envLookupT_bound env x idx hidx; omega) ?_⟩
      intro e'
      have := (hvis x).mp (by rw [hidx]; congr 1; omega)
      rw [this] at hvx; cases hvx
    · cases hlow
  | .Lit (c, ty) =>
    simp only [expandFix, lowerTotal] at hlow
    injection hlow with hlow; subst hlow
    exact ⟨_, by simp only [removeForces, expandFix, lowerTotal], ForceShare.constant _⟩
  | .Builtin b =>
    simp only [expandFix, lowerTotal] at hlow
    injection hlow with hlow; subst hlow
    exact ⟨_, by simp only [removeForces, expandFix, lowerTotal], ForceShare.builtin _⟩
  | .Error =>
    simp only [expandFix, lowerTotal] at hlow
    injection hlow with hlow; subst hlow
    exact ⟨_, by simp only [removeForces, expandFix, lowerTotal], ForceShare.error⟩
  | .Lam x body =>
    simp only [onlyForced, Bool.and_eq_true] at honly
    simp only [expandFix, lowerTotal, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlow
    obtain ⟨b, hb, heq⟩ := hlow
    injection heq with heq; subst heq
    obtain ⟨b', hb', hrel⟩ := removeForces_lower v body (x :: env) (pos + 1) b
      (visible_cons (ne_of_bne honly.1) hvis) honly.2 hb
    refine ⟨_, by simp only [removeForces, expandFix, lowerTotal, hb', Option.bind_eq_bind,
      Option.bind_some], ForceShare.lam hrel⟩
  | .Fix f body =>
    match body with
    | .Lam x inner =>
      simp only [onlyForced, Bool.and_eq_true] at honly
      let s : VarId := ⟨Moist.MIR.maxUidExpr (expandFix inner) +
        Moist.MIR.maxUidExpr (expandFix (removeForces v inner)) + v.uid + 1, .gen, "s"⟩
      have hs₁ : (Moist.MIR.freeVars (expandFix inner)).contains s = false :=
        Moist.MIR.maxUidExpr_fresh _ _ (by simp only [s]; omega)
      have hs₂ : (Moist.MIR.freeVars (expandFix (removeForces v inner))).contains s = false :=
        Moist.MIR.maxUidExpr_fresh _ _ (by simp only [s]; omega)
      have hvs : (v == s) = false := by
        rw [Moist.MIR.VarId.beq_false_iff]; exact Or.inr (by simp only [s]; omega)
      have hl := Moist.MIR.lowerTotalExpr_fix_lam_with_fresh env f x inner s hs₁
      simp only [Moist.MIR.lowerTotalExpr] at hl
      rw [hl] at hlow
      cases hb : lowerTotal (x :: f :: s :: env) (expandFix inner) with
      | none => rw [hb] at hlow; cases hlow
      | some b =>
        rw [hb] at hlow
        injection hlow with hlow; subst hlow
        have hvis' : Visible (x :: f :: s :: env) v (pos + 3) :=
          visible_cons (ne_of_bne honly.2.1) (visible_cons (ne_of_bne honly.1)
            (visible_cons hvs hvis))
        obtain ⟨b', hb', hrel⟩ := removeForces_lower v inner (x :: f :: s :: env) (pos + 3) b
          hvis' honly.2.2 hb
        have hr := Moist.MIR.lowerTotalExpr_fix_lam_with_fresh env f x
          (removeForces v inner) s hs₂
        simp only [Moist.MIR.lowerTotalExpr] at hr
        refine ⟨fixLamWrapUplc b', ?_, ?_⟩
        · rw [show removeForces v (.Fix f (.Lam x inner)) =
              .Fix f (.Lam x (removeForces v inner)) by simp [removeForces], hr, hb']; rfl
        · simp only [List.length_cons] at hrel
          simp only [fixLamWrapUplc]
          refine .apply (.lam (.apply (.var (by omega) (by omega) (by omega))
            (.var (by omega) (by omega) (by omega)))) (.lam (.apply (.lam (.lam hrel)) ?_))
          exact .lam (.apply (.apply (.var (by omega) (by omega) (by omega))
            (.var (by omega) (by omega) (by omega))) (.var (by omega) (by omega) (by omega)))
    | .Var _ | .Lit _ | .Builtin _ | .Error | .Fix _ _ | .App _ _ | .Force _ | .Delay _
    | .Constr _ _ | .Case _ _ | .Let _ _ =>
      simp [expandFix, lowerTotal] at hlow
  | .App fn arg =>
    simp only [onlyForced, Bool.and_eq_true] at honly
    simp only [expandFix, lowerTotal, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlow
    obtain ⟨tf, hf, ta, ha, heq⟩ := hlow
    injection heq with heq; subst heq
    obtain ⟨tf', hf', rf⟩ := removeForces_lower v fn env pos tf hvis honly.1 hf
    obtain ⟨ta', ha', ra⟩ := removeForces_lower v arg env pos ta hvis honly.2 ha
    exact ⟨_, by simp only [removeForces, expandFix, lowerTotal, hf', ha', Option.bind_eq_bind,
      Option.bind_some], ForceShare.apply rf ra⟩
  | .Force inner =>
    by_cases hvar : ∃ x, inner = .Var x
    · obtain ⟨x, rfl⟩ := hvar
      simp only [expandFix, lowerTotal, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlow
      obtain ⟨ti, hi, heq⟩ := hlow
      injection heq with heq; subst heq
      split at hi
      · rename_i idx hidx
        injection hi with hi; subst hi
        have hbound := Moist.MIR.envLookupT_bound env x idx hidx
        cases hvx : (v == x) with
        | true =>
          have hidx' : idx = pos := by
            have := (hvis x).mpr hvx; rw [hidx] at this; injection this
          subst hidx'
          refine ⟨_, ?_, ForceShare.forced (by omega) (by omega)⟩
          simp [removeForces, hvx, expandFix, lowerTotal, hidx]
        | false =>
          refine ⟨_, ?_, ForceShare.force (ForceShare.var (by omega) (by omega) ?_)⟩
          · simp [removeForces, hvx, expandFix, lowerTotal, hidx]
          · intro e'
            have := (hvis x).mp (by rw [hidx]; congr 1; omega)
            rw [this] at hvx; cases hvx
      · cases hi
    · have hnv : ∀ x, inner ≠ .Var x := fun x e' => hvar ⟨x, e'⟩
      rw [onlyForced_force_of_nonvar v hnv] at honly
      simp only [expandFix, lowerTotal, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlow
      obtain ⟨ti, hi, heq⟩ := hlow
      injection heq with heq; subst heq
      obtain ⟨ti', hi', ri⟩ := removeForces_lower v inner env pos ti hvis honly hi
      refine ⟨_, ?_, ForceShare.force ri⟩
      rw [removeForces_force_of_nonvar v hnv]
      simp only [expandFix, lowerTotal, hi', Option.bind_eq_bind, Option.bind_some]
  | .Delay inner =>
    simp only [onlyForced] at honly
    simp only [expandFix, lowerTotal, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlow
    obtain ⟨ti, hi, heq⟩ := hlow
    injection heq with heq; subst heq
    obtain ⟨ti', hi', ri⟩ := removeForces_lower v inner env pos ti hvis honly hi
    exact ⟨_, by simp only [removeForces, expandFix, lowerTotal, hi', Option.bind_eq_bind,
      Option.bind_some], ForceShare.delay ri⟩
  | .Constr tag fields =>
    simp only [onlyForced] at honly
    simp only [expandFix, lowerTotal, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlow
    obtain ⟨ts, hts, heq⟩ := hlow
    injection heq with heq; subst heq
    obtain ⟨ts', hts', rs⟩ := removeForcesList_lower v fields env pos ts hvis honly hts
    exact ⟨_, by simp only [removeForces, expandFix, lowerTotal, hts', Option.bind_eq_bind,
      Option.bind_some], ForceShare.constr rs⟩
  | .Case scrut alts =>
    simp only [onlyForced, Bool.and_eq_true] at honly
    simp only [expandFix, lowerTotal, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlow
    obtain ⟨ts, hs, tas, has, heq⟩ := hlow
    injection heq with heq; subst heq
    obtain ⟨ts', hs', rs⟩ := removeForces_lower v scrut env pos ts hvis honly.1 hs
    obtain ⟨tas', has', ras⟩ := removeForcesList_lower v alts env pos tas hvis honly.2 has
    exact ⟨_, by simp only [removeForces, expandFix, lowerTotal, hs', has', Option.bind_eq_bind,
      Option.bind_some], ForceShare.case rs ras⟩
  | .Let binds body =>
    simp only [onlyForced, Bool.and_eq_true] at honly
    simp only [expandFix, lowerTotal] at hlow
    obtain ⟨t', ht', rt⟩ := removeForcesBinds_lower v binds body env pos t hvis honly.1 honly.2 hlow
    exact ⟨t', by simp only [removeForces, expandFix, lowerTotal]; exact ht', rt⟩
termination_by sizeOf e

theorem removeForcesList_lower (v : VarId) (es : List Expr) (env : List VarId) (pos : Nat)
    (ts : List Term) (hvis : Visible env v pos) (honly : onlyForcedList v es = true)
    (hlow : lowerTotalList env (expandFixList es) = some ts) :
    ∃ ts', lowerTotalList env (expandFixList (removeForcesList v es)) = some ts' ∧
      ForceShareList env.length (pos + 1) ts ts' := by
  match es with
  | [] =>
    simp only [expandFixList, lowerTotalList] at hlow
    injection hlow with hlow; subst hlow
    exact ⟨[], by simp only [removeForcesList, expandFixList, lowerTotalList], .nil⟩
  | e :: rest =>
    simp only [onlyForcedList, Bool.and_eq_true] at honly
    simp only [expandFixList, lowerTotalList, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at hlow
    obtain ⟨t, ht, ts₀, hts, heq⟩ := hlow
    injection heq with heq; subst heq
    obtain ⟨t', ht', r⟩ := removeForces_lower v e env pos t hvis honly.1 ht
    obtain ⟨ts', hts', rs⟩ := removeForcesList_lower v rest env pos ts₀ hvis honly.2 hts
    exact ⟨_, by simp only [removeForcesList, expandFixList, lowerTotalList, ht', hts',
      Option.bind_eq_bind, Option.bind_some], .cons r rs⟩
termination_by sizeOf es

theorem removeForcesBinds_lower (v : VarId) (binds : List (VarId × Expr × Bool)) (body : Expr)
    (env : List VarId) (pos : Nat) (t : Term) (hvis : Visible env v pos)
    (hbinds : onlyForcedBinds v binds = true) (hbody : onlyForced v body = true)
    (hlow : lowerTotalLet env (expandFixBinds binds) (expandFix body) = some t) :
    ∃ t', lowerTotalLet env (expandFixBinds (removeForcesBinds v binds))
        (expandFix (removeForces v body)) = some t' ∧
      ForceShare env.length (pos + 1) t t' := by
  match binds with
  | [] =>
    simp only [expandFixBinds, lowerTotalLet] at hlow
    obtain ⟨t', ht', r⟩ := removeForces_lower v body env pos t hvis hbody hlow
    exact ⟨t', by simp only [removeForcesBinds, expandFixBinds, lowerTotalLet]; exact ht', r⟩
  | (x, rhs, er) :: rest =>
    simp only [onlyForcedBinds, Bool.and_eq_true] at hbinds
    simp only [expandFixBinds, lowerTotalLet, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at hlow
    obtain ⟨tr, htr, tb, htb, heq⟩ := hlow
    injection heq with heq; subst heq
    obtain ⟨tr', htr', rr⟩ := removeForces_lower v rhs env pos tr hvis hbinds.1.2 htr
    obtain ⟨tb', htb', rb⟩ := removeForcesBinds_lower v rest body (x :: env) (pos + 1) tb
      (visible_cons (ne_of_bne hbinds.1.1) hvis) hbinds.2 hbody htb
    exact ⟨_, by simp only [removeForcesBinds, expandFixBinds, lowerTotalLet, htr', htb',
      Option.bind_eq_bind, Option.bind_some], ForceShare.apply (ForceShare.lam rb) rr⟩
termination_by sizeOf binds + sizeOf body
end

end Lowering

end Moist.Verified.DelaySharing

/-! ## MIR certificates -/

namespace Moist.Verified.MIR

open Moist.MIR (Expr VarId isPure lowerTotal lowerTotalExpr expandFix expandFixBinds lowerTotalLet)
open Moist.MIR.Advanced
  (onlyForced removeForces shareDelayBinding shareDelaysLocal shareDelaysCore shareDelayedValues
   rewriteBottomUp)
open Moist.Verified.DelaySharing

private theorem let_single_lower (env : List VarId) (v : VarId) (rhs body : Expr) (er : Bool) :
    lowerTotalExpr env (.Let [(v, rhs, er)] body) =
      (lowerTotalExpr env rhs).bind fun r =>
        (lowerTotalExpr (v :: env) body).bind fun b => some (.Apply (.Lam 0 b) r) := by
  simp only [lowerTotalExpr, expandFix, expandFixBinds, lowerTotal, lowerTotalLet,
    Option.bind_eq_bind]

/-- One shared binding: a pure delay whose every use is forced is evaluated
    eagerly and its forces are dropped. -/
theorem share_let_refines (v : VarId) (delayed body : Expr) (er : Bool)
    (hpure : isPure delayed = true) (honly : onlyForced v body = true) :
    MIRCtxRefines (.Let [(v, .Delay delayed, er)] body)
      (.Let [(v, delayed, er)] (removeForces v body)) := by
  intro env
  rw [let_single_lower, let_single_lower]
  have hdelay : lowerTotalExpr env (.Delay delayed) = (lowerTotalExpr env delayed).map .Delay := by
    simp only [lowerTotalExpr, expandFix, lowerTotal, Option.bind_eq_bind]
    cases lowerTotal env (expandFix delayed) <;> rfl
  rw [hdelay]
  cases hD : lowerTotalExpr env delayed with
  | none => exact ⟨fun h => by simp at h, trivial⟩
  | some D =>
    cases hS : lowerTotalExpr (v :: env) body with
    | none => exact ⟨fun h => by simp at h, trivial⟩
    | some sl =>
      obtain ⟨sl', hsl', hrel⟩ := removeForces_lower v body (v :: env) 0 sl
        (visible_head env v) honly hS
      have hsl'' : lowerTotalExpr (v :: env) (removeForces v body) = some sl' := hsl'
      simp only [List.length_cons, Nat.zero_add] at hrel
      simp only [Option.map_some, Option.bind_some, hsl'']
      refine ⟨fun _ => rfl, ctxRefines_of_openRefines (d := env.length) ?_ ?_⟩
      · intro k hk
        simp only [closedAt, Bool.and_eq_true] at hk ⊢
        exact ⟨hrel.closedAt_right (k + 1) hk.1, hk.2⟩
      · refine share_let_openRefines hrel (lowerTotalExpr_closedAt hD) fun ρ hwf => ?_
        obtain ⟨w, hw⟩ := Moist.Verified.Purity.isPure_halts (expandFix delayed) D env ρ
          (Moist.Verified.Purity.isPure_expandFix delayed hpure) hD hwf
        exact ⟨w, Moist.Verified.InlineSoundness.StrictOcc.halt_on_all_stacks hw⟩

theorem shareDelayBinding_refines (binding : VarId × Expr × Bool) (suffix : Expr) :
    MIRCtxRefines (.Let [binding] suffix) (shareDelayBinding binding suffix) := by
  obtain ⟨v, rhs, er⟩ := binding
  cases rhs with
  | Delay delayed =>
    simp only [shareDelayBinding]
    split
    · next h =>
      simp only [Bool.and_eq_true] at h
      exact share_let_refines v delayed suffix er h.1 h.2
    · exact mirCtxRefines_refl _
  | _ => simp only [shareDelayBinding]; exact mirCtxRefines_refl _

private theorem let_cons_lowerEq (binding : VarId × Expr × Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) (env : List VarId) :
    lowerTotalExpr env (.Let (binding :: rest) body) =
      lowerTotalExpr env (.Let [binding] (.Let rest body)) := by
  obtain ⟨v, rhs, er⟩ := binding
  simp only [lowerTotalExpr, expandFix, expandFixBinds, lowerTotal, lowerTotalLet]

theorem shareDelayBindings_refines :
    ∀ (bindings : List (VarId × Expr × Bool)) (body : Expr),
      MIRCtxRefines (.Let bindings body) (bindings.foldr shareDelayBinding body)
  | [], _ => mirCtxRefines_let_nil
  | binding :: rest, body =>
    mirCtxRefines_trans (mirCtxRefines_of_lowerEq (let_cons_lowerEq binding rest body))
      (mirCtxRefines_trans (mirCtxRefines_let_body (shareDelayBindings_refines rest body))
        (shareDelayBinding_refines binding _))

theorem shareDelaysLocal_refines (expression : Expr) :
    MIRCtxRefines expression (shareDelaysLocal expression) := by
  cases expression with
  | Let bindings body => exact shareDelayBindings_refines bindings body
  | _ => exact mirCtxRefines_refl _

theorem shareDelaysCore_refines (expression : Expr) :
    MIRCtxRefines expression (shareDelaysCore expression) :=
  rewriteBottomUp_refines shareDelaysLocal shareDelaysLocal_refines (fun _ _ => rfl)
    (Moist.MIR.exprSize expression) expression

/-- Delayed-value sharing is sound. -/
theorem shareDelayedValues_refines (e : Expr) : MIRCtxRefines e (shareDelayedValues e) :=
  mirCtxRefines_trans (Hygiene.uniqueOptimizationBinders_refines e)
    (shareDelaysCore_refines _)

/-- The advanced preparation stage (delay sharing, then dead `Fix` removal) is sound. -/
theorem prepare_refines (e : Expr) : MIRCtxRefines e (Moist.MIR.Advanced.prepare e) :=
  mirCtxRefines_trans (shareDelayedValues_refines e) (eliminateDeadFix_refines _)

end Moist.Verified.MIR
