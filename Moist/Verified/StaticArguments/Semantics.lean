import Moist.Verified.FundamentalRefines
import Moist.MIR.LowerTotal

/-! # Static argument transformation at the UPLC level

The source fixed point `fix (λr. λp. λn. B)` and the target
`λp. fix (λr. λn. B')` are related when `B'` is `B` with every recursive call
`r p` replaced by `r`, and with the environment slots of `p` and `r`
exchanged (`Rel`). Inside the bodies the source environment is
`… n, p, r, s, ρ` and the target environment is `… n, r, s', p, ρ`.

`rel_eval` is the fundamental property of `Rel` for environments whose
recursive slot behaves like the source call (`EnvOK`). `openRefines_static`
ties the knot by induction on the step index.
-/

namespace Moist.Verified.StaticArguments

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified (closedAt closedAtList)
open Moist.Verified.Equivalence
open Moist.Verified.Contextual.SoundnessRefines
open Moist.Verified.Contextual.Guarded

/-! ## The syntactic relation -/

mutual
  /-- `Rel e d t₁ t₂`: `t₂` is `t₁` with the static argument removed, at
      `d` binders below the recursive worker's environment block. -/
  inductive Rel (e : Nat) : Nat → Term → Term → Prop
    | varLow {d i : Nat} : i ≤ d → Rel e d (.Var i) (.Var i)
    | varParam {d : Nat} : Rel e d (.Var (d + 1)) (.Var (d + 3))
    | varHigh {d i : Nat} : d + 3 < i → i ≤ d + 3 + e → Rel e d (.Var i) (.Var i)
    | call {d : Nat} : Rel e d (.Apply (.Var (d + 2)) (.Var (d + 1))) (.Var (d + 1))
    | constant {d : Nat} {c : Const × BuiltinType} : Rel e d (.Constant c) (.Constant c)
    | builtin {d : Nat} {b : BuiltinFun} : Rel e d (.Builtin b) (.Builtin b)
    | error {d : Nat} : Rel e d .Error .Error
    | lam {d x : Nat} {b₁ b₂ : Term} : Rel e (d + 1) b₁ b₂ → Rel e d (.Lam x b₁) (.Lam x b₂)
    | apply {d : Nat} {f₁ f₂ a₁ a₂ : Term} :
        Rel e d f₁ f₂ → Rel e d a₁ a₂ → Rel e d (.Apply f₁ a₁) (.Apply f₂ a₂)
    | force {d : Nat} {t₁ t₂ : Term} : Rel e d t₁ t₂ → Rel e d (.Force t₁) (.Force t₂)
    | delay {d : Nat} {t₁ t₂ : Term} : Rel e d t₁ t₂ → Rel e d (.Delay t₁) (.Delay t₂)
    | constr {d tag : Nat} {ts₁ ts₂ : List Term} :
        RelList e d ts₁ ts₂ → Rel e d (.Constr tag ts₁) (.Constr tag ts₂)
    | case {d : Nat} {s₁ s₂ : Term} {as₁ as₂ : List Term} :
        Rel e d s₁ s₂ → RelList e d as₁ as₂ → Rel e d (.Case s₁ as₁) (.Case s₂ as₂)

  inductive RelList (e : Nat) : Nat → List Term → List Term → Prop
    | nil {d : Nat} : RelList e d [] []
    | cons {d : Nat} {t₁ t₂ : Term} {ts₁ ts₂ : List Term} :
        Rel e d t₁ t₂ → RelList e d ts₁ ts₂ → RelList e d (t₁ :: ts₁) (t₂ :: ts₂)
end

/-! ## Closedness -/

mutual
  theorem Rel.closedAt {e d : Nat} {t₁ t₂ : Term} (h : Rel e d t₁ t₂) (k : Nat)
      (hc : closedAt (d + 3 + k) t₁ = true) : closedAt (d + 3 + k) t₂ = true := by
    match h with
    | .varLow hi => simp only [Moist.Verified.closedAt, decide_eq_true_eq]; omega
    | .varParam => simp only [Moist.Verified.closedAt, decide_eq_true_eq]; omega
    | .varHigh _ _ => exact hc
    | .call => simp only [Moist.Verified.closedAt, decide_eq_true_eq]; omega
    | .constant | .builtin | .error => exact hc
    | .lam hb =>
      simp only [Moist.Verified.closedAt] at hc ⊢
      have := hb.closedAt k (by rw [show d + 1 + 3 + k = d + 3 + k + 1 by omega]; exact hc)
      rwa [show d + 1 + 3 + k = d + 3 + k + 1 by omega] at this
    | .apply hf ha =>
      simp only [Moist.Verified.closedAt, Bool.and_eq_true] at hc ⊢
      exact ⟨hf.closedAt k hc.1, ha.closedAt k hc.2⟩
    | .force ht | .delay ht =>
      simp only [Moist.Verified.closedAt] at hc ⊢
      exact ht.closedAt k hc
    | .constr hts =>
      simp only [Moist.Verified.closedAt] at hc ⊢
      exact hts.closedAt k hc
    | .case hs has =>
      simp only [Moist.Verified.closedAt, Bool.and_eq_true] at hc ⊢
      exact ⟨hs.closedAt k hc.1, has.closedAt k hc.2⟩

  theorem RelList.closedAt {e d : Nat} {ts₁ ts₂ : List Term} (h : RelList e d ts₁ ts₂) (k : Nat)
      (hc : closedAtList (d + 3 + k) ts₁ = true) : closedAtList (d + 3 + k) ts₂ = true := by
    match h with
    | .nil => exact hc
    | .cons ht hts =>
      simp only [Moist.Verified.closedAtList, Bool.and_eq_true] at hc ⊢
      exact ⟨ht.closedAt k hc.1, hts.closedAt k hc.2⟩
end

/-! ## Environments -/

private abbrev VR := ValueRel Guard.trivial

theorem lookup_extend_succ (ρ : CekEnv) (v : CekValue) (n : Nat) (hn : 0 < n) :
    (ρ.extend v).lookup (n + 1) = ρ.lookup n := by
  match n, hn with
  | m + 1, _ => rfl

theorem lookup_zero (ρ : CekEnv) : ρ.lookup 0 = none := by
  cases ρ <;> rfl

/-- Environments for `Rel e d`: the `d` innermost slots are related, the
    parameter slots are related, the recursive slots behave like a call to
    the source worker on the parameter, and the outer `e` slots are related. -/
structure EnvOK (e k d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop where
  low : ∀ n, 0 < n → n ≤ d →
    ∃ v₁ v₂, ρ₁.lookup n = some v₁ ∧ ρ₂.lookup n = some v₂ ∧ VR k v₁ v₂
  param : ∃ v₁ v₂, ρ₁.lookup (d + 1) = some v₁ ∧ ρ₂.lookup (d + 3) = some v₂ ∧ VR k v₁ v₂
  call : ∃ f a g v, ρ₁.lookup (d + 2) = some f ∧ ρ₁.lookup (d + 1) = some a ∧
    ρ₂.lookup (d + 1) = some g ∧
    (∀ π, ∃ m, steps m (.ret (.funV f :: π) a) = .ret π v) ∧ VR k v g
  high : ∀ n, d + 3 < n → n ≤ d + 3 + e →
    ∃ v₁ v₂, ρ₁.lookup n = some v₁ ∧ ρ₂.lookup n = some v₂ ∧ VR k v₁ v₂

theorem EnvOK.mono {e j k d : Nat} {ρ₁ ρ₂ : CekEnv} (hjk : j ≤ k) (h : EnvOK e k d ρ₁ ρ₂) :
    EnvOK e j d ρ₁ ρ₂ := by
  refine ⟨fun n hn hnd => ?_, ?_, ?_, fun n hn hnd => ?_⟩
  · obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := h.low n hn hnd
    exact ⟨v₁, v₂, h₁, h₂, valueRel_mono hjk hv⟩
  · obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := h.param
    exact ⟨v₁, v₂, h₁, h₂, valueRel_mono hjk hv⟩
  · obtain ⟨f, a, g, v, hf, ha, hg, hs, hv⟩ := h.call
    exact ⟨f, a, g, v, hf, ha, hg, hs, valueRel_mono hjk hv⟩
  · obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := h.high n hn hnd
    exact ⟨v₁, v₂, h₁, h₂, valueRel_mono hjk hv⟩

theorem EnvOK.extend {e k d : Nat} {ρ₁ ρ₂ : CekEnv} {w₁ w₂ : CekValue}
    (h : EnvOK e k d ρ₁ ρ₂) (hw : VR k w₁ w₂) :
    EnvOK e k (d + 1) (ρ₁.extend w₁) (ρ₂.extend w₂) := by
  refine ⟨fun n hn hnd => ?_, ?_, ?_, fun n hn hnd => ?_⟩
  · by_cases h1 : n = 1
    · subst h1; exact ⟨w₁, w₂, rfl, rfl, hw⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [lookup_extend_succ _ _ _ (by omega), lookup_extend_succ _ _ _ (by omega)]
      exact h.low m (by omega) (by omega)
  · rw [lookup_extend_succ _ _ _ (by omega), show d + 1 + 3 = d + 3 + 1 by omega,
      lookup_extend_succ _ _ _ (by omega)]
    exact h.param
  · obtain ⟨f, a, g, v, hf, ha, hg, hs, hv⟩ := h.call
    refine ⟨f, a, g, v, ?_, ?_, ?_, hs, hv⟩
    · rw [show d + 1 + 2 = d + 2 + 1 by omega, lookup_extend_succ _ _ _ (by omega)]; exact hf
    · rw [lookup_extend_succ _ _ _ (by omega)]; exact ha
    · rw [lookup_extend_succ _ _ _ (by omega)]; exact hg
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [lookup_extend_succ _ _ _ (by omega), lookup_extend_succ _ _ _ (by omega)]
    exact h.high m (by omega) (by omega)

/-! ## The fundamental property of `Rel` -/

private theorem var_obs {k n m : Nat} {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue}
    (h₁ : ρ₁.lookup n = some v₁) (h₂ : ρ₂.lookup m = some v₂) (hv : VR k v₁ v₂) :
    Eval Guard.trivial k ρ₁ ρ₂ (.Var n) (.Var m) := by
  refine eval_of_step fun j hj π₁ π₂ hπ _ _ => ?_
  simp only [step, h₁, h₂]
  exact ret_obs (valueRel_mono (by omega) hv) trivial trivial hπ

mutual
  theorem rel_eval {e d : Nat} {t₁ t₂ : Term} (h : Rel e d t₁ t₂) {k : Nat} {ρ₁ ρ₂ : CekEnv}
      (henv : EnvOK e k d ρ₁ ρ₂) : Eval Guard.trivial k ρ₁ ρ₂ t₁ t₂ := by
    match h with
    | .varLow (i := i) hi =>
      by_cases hi0 : i = 0
      · subst hi0
        refine eval_of_step fun j _ _ _ _ _ _ => ?_
        simp only [step, lookup_zero]
        exact obsRefinesK_error_error j
      · obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := henv.low i (by omega) hi
        exact var_obs h₁ h₂ hv
    | .varParam =>
      obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := henv.param
      exact var_obs h₁ h₂ hv
    | .varHigh hlo hhi =>
      obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := henv.high _ hlo hhi
      exact var_obs h₁ h₂ hv
    | .call =>
      obtain ⟨f, a, g, v, hf, ha, hg, hs, hv⟩ := henv.call
      intro j hj π₁ π₂ hπ _ _
      obtain ⟨m, hm⟩ := hs π₁
      have h₁ : steps 4 (.compute π₁ ρ₁ (.Apply (.Var (d + 2)) (.Var (d + 1)))) =
          .ret (.funV f :: π₁) a := by
        simp only [steps, step, hf, ha]
      have h₂ : steps 1 (.compute π₂ ρ₂ (.Var (d + 1))) = .ret π₂ g := by
        simp only [steps, step, hg]
      exact obsRefinesK_of_steps_left h₁ (obsRefinesK_of_steps_left hm
        (obsRefinesK_of_steps_right h₂ (ret_obs (valueRel_mono hj hv) trivial trivial hπ)))
    | .constant =>
      exact eval_of_step fun j _ _ _ hπ _ _ => ret_obs (valueRel_vcon j _) trivial trivial hπ
    | .builtin =>
      exact eval_of_step fun j _ _ _ hπ _ _ =>
        ret_obs (valueRel_builtin (k := j) trivial) trivial trivial hπ
    | .error => exact eval_of_step fun j _ _ _ _ _ _ => obsRefinesK_error_error j
    | .lam hb =>
      refine eval_of_step fun j hj π₁ π₂ hπ _ _ => ?_
      refine ret_obs (valueRel_lam trivial trivial fun j' hj' a₁ a₂ ha _ _ => ?_) trivial trivial hπ
      exact rel_eval hb ((henv.mono (by omega)).extend ha)
    | .apply hf ha =>
      refine eval_of_step fun j hj π₁ π₂ hπ _ _ => ?_
      exact rel_eval hf (henv.mono (by omega)) j (Nat.le_refl _) _ _
        (arg_stackRel (rel_eval ha (henv.mono (by omega))) trivial trivial hπ) trivial trivial
    | .force ht =>
      refine eval_of_step fun j hj π₁ π₂ hπ _ _ => ?_
      exact rel_eval ht (henv.mono (by omega)) j (Nat.le_refl _) _ _ (force_stackRel hπ)
        trivial trivial
    | .delay ht =>
      refine eval_of_step fun j hj π₁ π₂ hπ _ _ => ?_
      exact ret_obs (valueRel_delay trivial trivial
        fun j' hj' => rel_eval ht (henv.mono (by omega))) trivial trivial hπ
    | .constr .nil =>
      exact eval_of_step fun j _ _ _ hπ _ _ =>
        ret_obs (valueRel_constr (k := j) trivial) trivial trivial hπ
    | .constr (.cons hm hms) =>
      refine eval_of_step fun j hj π₁ π₂ hπ _ _ => ?_
      exact rel_eval hm (henv.mono (by omega)) j (Nat.le_refl _) _ _
        (constrField_stackRel (relList_eval hms (henv.mono (by omega))) trivial trivial trivial hπ)
        trivial trivial
    | .case hs has =>
      refine eval_of_step fun j hj π₁ π₂ hπ _ _ => ?_
      exact rel_eval hs (henv.mono (by omega)) j (Nat.le_refl _) _ _
        (case_stackRel (altsRel_of_listRel (relList_eval has (henv.mono (by omega))))
          trivial trivial hπ) trivial trivial

  theorem relList_eval {e d : Nat} {ts₁ ts₂ : List Term} (h : RelList e d ts₁ ts₂) {k : Nat}
      {ρ₁ ρ₂ : CekEnv} (henv : EnvOK e k d ρ₁ ρ₂) :
      ListRel (Eval Guard.trivial k ρ₁ ρ₂) ts₁ ts₂ := by
    match h with
    | .nil => exact trivial
    | .cons ht hts => exact ⟨rel_eval ht henv, relList_eval hts henv⟩
end

/-! ## The two fixed points -/

/-- The self-application `λv. s s v` of the fixed-point wrapper. -/
def selfApp : Term := .Apply (.Apply (.Var 2) (.Var 2)) (.Var 1)

section FixedPoints

variable (bodyS bodyT : Term)

/-- Source wrapper value `s` for `fix (λr. λp. λn. bodyS)` in `ρ`. -/
def srcSelf (ρ : CekEnv) : CekValue :=
  .VLam (.Apply (.Lam 0 (.Lam 0 (.Lam 0 bodyS))) (.Lam 0 selfApp)) ρ

/-- Source recursive value bound to `r`. -/
def srcRec (ρ : CekEnv) : CekValue := .VLam selfApp (ρ.extend (srcSelf bodyS ρ))

/-- Source worker `λn. bodyS` after receiving the parameter `a`. -/
def srcInner (ρ : CekEnv) (a : CekValue) : CekValue :=
  .VLam bodyS (((ρ.extend (srcSelf bodyS ρ)).extend (srcRec bodyS ρ)).extend a)

/-- Target wrapper value `s` for `fix (λr. λn. bodyT)` under the parameter `a`. -/
def tgtSelf (ρ : CekEnv) (a : CekValue) : CekValue :=
  .VLam (.Apply (.Lam 0 (.Lam 0 bodyT)) (.Lam 0 selfApp)) (ρ.extend a)

/-- Target recursive value bound to `r`. -/
def tgtRec (ρ : CekEnv) (a : CekValue) : CekValue :=
  .VLam selfApp ((ρ.extend a).extend (tgtSelf bodyT ρ a))

/-- Target worker `λn. bodyT`. -/
def tgtInner (ρ : CekEnv) (a : CekValue) : CekValue :=
  .VLam bodyT (((ρ.extend a).extend (tgtSelf bodyT ρ a)).extend (tgtRec bodyT ρ a))

theorem src_fix_steps (π : Stack) (ρ : CekEnv) :
    steps 16 (.compute π ρ (Moist.MIR.fixLamWrapUplc (.Lam 0 bodyS))) =
      .ret π (.VLam (.Lam 0 bodyS) ((ρ.extend (srcSelf bodyS ρ)).extend (srcRec bodyS ρ))) := rfl

theorem src_call_steps (π : Stack) (ρ : CekEnv) (a : CekValue) :
    steps 17 (.ret (.funV (srcRec bodyS ρ) :: π) a) = .ret π (srcInner bodyS ρ a) := rfl

theorem tgt_fix_steps (π : Stack) (ρ : CekEnv) (a : CekValue) :
    steps 16 (.compute π (ρ.extend a) (Moist.MIR.fixLamWrapUplc bodyT)) =
      .ret π (tgtInner bodyT ρ a) := rfl

theorem tgt_call_steps (π : Stack) (ρ : CekEnv) (a b : CekValue) :
    steps 15 (.compute π (((ρ.extend a).extend (tgtSelf bodyT ρ a)).extend b) selfApp) =
      .compute π ((((ρ.extend a).extend (tgtSelf bodyT ρ a)).extend (tgtRec bodyT ρ a)).extend b)
        bodyT := rfl

end FixedPoints

/-! ## Tying the knot -/

private theorem envRel_mono {e j k : Nat} {ρ₁ ρ₂ : CekEnv} (hjk : j ≤ k)
    (h : EnvRel Guard.trivial k e ρ₁ ρ₂) : EnvRel Guard.trivial j e ρ₁ ρ₂ := by
  intro n hn hnd
  obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := h n hn hnd
  exact ⟨v₁, v₂, h₁, h₂, valueRel_mono hjk hv⟩

private theorem lookup_extend4 (ρ : CekEnv) (v₁ v₂ v₃ v₄ : CekValue) (n : Nat) (hn : 0 < n) :
    ((((ρ.extend v₁).extend v₂).extend v₃).extend v₄).lookup (n + 4) = ρ.lookup n := by
  rw [show n + 4 = n + 3 + 1 by omega, lookup_extend_succ _ _ _ (by omega),
    show n + 3 = n + 2 + 1 by omega, lookup_extend_succ _ _ _ (by omega),
    show n + 2 = n + 1 + 1 by omega, lookup_extend_succ _ _ _ (by omega),
    lookup_extend_succ _ _ _ hn]

private theorem eval_of_steps_right {k m : Nat} {ρ₁ ρ₂ ρ₂' : CekEnv} {t₁ t₂ t₂' : Term}
    (hs : ∀ π, steps m (.compute π ρ₂ t₂) = .compute π ρ₂' t₂')
    (h : Eval Guard.trivial k ρ₁ ρ₂' t₁ t₂') : Eval Guard.trivial k ρ₁ ρ₂ t₁ t₂ :=
  fun j hj π₁ π₂ hπ _ _ => obsRefinesK_of_steps_right (hs π₂) (h j hj π₁ π₂ hπ trivial trivial)

/-- The two worker bodies are related in the environments built by the two
    fixed points, at every step index. -/
theorem body_rel {e : Nat} {bodyS bodyT : Term} (h : Rel e 1 bodyS bodyT) (k : Nat) :
    ∀ {ρ₁ ρ₂ : CekEnv} {a₁ a₂ b₁ b₂ : CekValue},
      EnvRel Guard.trivial k e ρ₁ ρ₂ → VR k a₁ a₂ → VR k b₁ b₂ →
      Eval Guard.trivial k
        ((((ρ₁.extend (srcSelf bodyS ρ₁)).extend (srcRec bodyS ρ₁)).extend a₁).extend b₁)
        ((((ρ₂.extend a₂).extend (tgtSelf bodyT ρ₂ a₂)).extend (tgtRec bodyT ρ₂ a₂)).extend b₂)
        bodyS bodyT := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro ρ₁ ρ₂ a₁ a₂ b₁ b₂ hρ ha hb
  have hrec : VR k (srcInner bodyS ρ₁ a₁) (tgtRec bodyT ρ₂ a₂) :=
    valueRel_lam trivial trivial fun j hj c₁ c₂ hc _ _ =>
      eval_of_steps_right (fun π => tgt_call_steps bodyT π ρ₂ a₂ c₂)
        (ih j hj (envRel_mono (by omega) hρ) (valueRel_mono (by omega) ha) hc)
  apply rel_eval h
  refine ⟨fun n hn hnd => ?_, ⟨a₁, a₂, rfl, rfl, ha⟩,
    ⟨srcRec bodyS ρ₁, a₁, tgtRec bodyT ρ₂ a₂, srcInner bodyS ρ₁ a₁, rfl, rfl, rfl,
      fun π => ⟨17, src_call_steps bodyS π ρ₁ a₁⟩, hrec⟩, fun n hn hnd => ?_⟩
  · have : n = 1 := by omega
    subst this
    exact ⟨b₁, b₂, rfl, rfl, hb⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [lookup_extend4 _ _ _ _ _ _ (by omega), lookup_extend4 _ _ _ _ _ _ (by omega)]
    exact hρ m (by omega) (by omega)

/-- The source fixed point refines the target that binds the static
    parameter outside its fixed point. -/
theorem openRefines_static {e : Nat} {bodyS bodyT : Term} (h : Rel e 1 bodyS bodyT) :
    OpenRefines e (Moist.MIR.fixLamWrapUplc (.Lam 0 bodyS))
      (.Lam 0 (Moist.MIR.fixLamWrapUplc bodyT)) := by
  intro k j _ ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  have hρ : EnvRel Guard.trivial i e ρ₁ ρ₂ := fun n hn hnd => by
    obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := henv n hn hnd
    exact ⟨v₁, v₂, h₁, h₂, valueRel_mono hi ((valueRel_trivial j v₁ v₂).mpr hv)⟩
  have hinner : ∀ {k : Nat} {σ₁ σ₂ : CekEnv} {a₁ a₂ : CekValue},
      EnvRel Guard.trivial k e σ₁ σ₂ → VR k a₁ a₂ →
      VR k (srcInner bodyS σ₁ a₁) (tgtInner bodyT σ₂ a₂) :=
    fun hσ ha => valueRel_lam trivial trivial fun j hj b₁ b₂ hb _ _ =>
      body_rel h j (envRel_mono (by omega) hσ) (valueRel_mono (by omega) ha) hb
  have houter : VR i
      (.VLam (.Lam 0 bodyS) ((ρ₁.extend (srcSelf bodyS ρ₁)).extend (srcRec bodyS ρ₁)))
      (.VLam (Moist.MIR.fixLamWrapUplc bodyT) ρ₂) :=
    valueRel_lam trivial trivial fun j hj a₁ a₂ ha _ _ => by
      intro i' hi' σ₁ σ₂ hσ _ _
      have h₁ : steps 1 (.compute σ₁ (((ρ₁.extend (srcSelf bodyS ρ₁)).extend
          (srcRec bodyS ρ₁)).extend a₁) (.Lam 0 bodyS)) = .ret σ₁ (srcInner bodyS ρ₁ a₁) := rfl
      exact obsRefinesK_of_steps_left h₁ (obsRefinesK_of_steps_right
        (tgt_fix_steps bodyT σ₂ ρ₂ a₂)
        (ret_obs (hinner (envRel_mono (by omega) hρ) (valueRel_mono hi' ha)) trivial trivial hσ))
  have h₂ : steps 1 (.compute π₂ ρ₂ (.Lam 0 (Moist.MIR.fixLamWrapUplc bodyT))) =
      .ret π₂ (.VLam (Moist.MIR.fixLamWrapUplc bodyT) ρ₂) := rfl
  exact obsRefinesK_of_steps_left (src_fix_steps bodyS π₁ ρ₁) (obsRefinesK_of_steps_right h₂
    (ret_obs houter trivial trivial (stackRefK_iff_stackRel.mp hπ)))

end Moist.Verified.StaticArguments
