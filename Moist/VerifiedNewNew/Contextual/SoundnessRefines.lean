import Moist.VerifiedNewNew.Contextual.Soundness
import Moist.VerifiedNewNew.Definitions.StepIndexed

/-! # Unidirectional open-context soundness (`OpenRefines d → CtxRefines`)

Phase 6 `Contextual.Soundness.lean` proves the bidirectional version:

```
theorem soundness_d {d : Nat} (h : OpenEq d t₁ t₂) :
    ∀ C, ObsEq (compute [] .nil (fill C t₁)) (compute [] .nil (fill C t₂))
```

For optimizer refinement proofs (DCE, etc.), we need the **unidirectional**
version: given only `OpenRefines d t₁ t₂` (one direction of `BehEqK`), produce
`CtxRefines t₁ t₂`. The bidirectional version is too strong — e.g. for a
dead-let transformation `Apply (Lam 0 (shift body)) e → body` where `e`
accesses free variables outside `body`'s access set, the reverse direction
fails on non-well-sized environments (e errors while body happily halts).

This file mirrors the bidirectional Phase 6 infrastructure in
`Soundness.lean` with unidirectional analogues:

  * `ObsRefinesK` — one direction of `ObsEqK`.
  * `ValueRefinesK` — `ValueEqK` recast with `ObsRefinesK` outputs.
  * `StackRefK`, `BehRefinesK`, `OpenRefines` — matching stack/behaviour/open
    relations.
  * `TermSubstL` / `TermListSubstL` — `TermSubst` without the `swapInv`
    constructor (symmetric flip). `fill_termSubst` never uses `swapInv`, so
    this is the right shape for soundness proofs that only need the forward
    direction.
  * `term_obsRefines` — the main bridge theorem, mirroring `term_obsEq`.
  * `soundness_refines_d` — the public entry point.
-/

namespace Moist.VerifiedNewNew.Contextual.SoundnessRefines

open Moist.CEK
open Moist.Plutus.Term
open Moist.VerifiedNewNew.Equivalence
open Moist.VerifiedNewNew.Contextual
open Moist.VerifiedNewNew.Contextual.Subst
open Moist.VerifiedNewNew.Contextual.Soundness

--------------------------------------------------------------------------------
-- 1. ObsRefinesK
--
-- We reuse the shared `ObsRefinesK` from Equivalence.lean which now includes
-- error preservation. The `obsRefinesK_of_obsEqK` projection picks either side
-- of an ObsEqK, and local helpers below specialize the Equivalence.lean
-- theorems for use inside `term_obsRefines`.
--------------------------------------------------------------------------------

theorem obsRefinesK_of_obsEqK {k : Nat} {s₁ s₂ : State}
    (h : ObsEqK k s₁ s₂) : ObsRefinesK k s₁ s₂ := h.1

theorem obsRefinesK_halt (k : Nat) (v_l v_r : CekValue) :
    ObsRefinesK k (.halt v_l) (.halt v_r) :=
  obsRefinesK_halt_halt k v_l v_r

theorem obsRefinesK_error (k : Nat) : ObsRefinesK k (.error : State) .error :=
  obsRefinesK_error_error k

--------------------------------------------------------------------------------
-- 2. ValueRefinesK monotonicity
--
-- `ValueRefinesK` itself is defined in
-- `Moist.VerifiedNewNew.Definitions.StepIndexed`. Theorems about it stay here.
--------------------------------------------------------------------------------

private theorem valueRefinesK_mono_le (k : Nat) :
    ∀ j, j ≤ k → ∀ v₁ v₂, ValueRefinesK k v₁ v₂ → ValueRefinesK j v₁ v₂ := by
  induction k with
  | zero =>
    intro j hj v₁ v₂ h
    have : j = 0 := by omega
    subst this; exact h
  | succ k ih =>
    intro j hj v₁ v₂ h
    match j, v₁, v₂ with
    | 0, .VCon _, .VCon _ => simp only [ValueRefinesK] at h ⊢; exact h
    | 0, .VLam _ _, .VLam _ _ => simp only [ValueRefinesK]
    | 0, .VDelay _ _, .VDelay _ _ => simp only [ValueRefinesK]
    | 0, .VConstr _ _, .VConstr _ _ =>
      simp only [ValueRefinesK] at h ⊢; exact h.1
    | 0, .VBuiltin _ _ _, .VBuiltin _ _ _ =>
      simp only [ValueRefinesK] at h ⊢; exact ⟨h.1, h.2.1⟩
    | j' + 1, .VCon _, .VCon _ => simp only [ValueRefinesK] at h ⊢; exact h
    | j' + 1, .VLam _ _, .VLam _ _ =>
      simp only [ValueRefinesK] at h ⊢
      intro j₀ hj₀ arg₁ arg₂ harg i hi π₁ π₂ hstk
      exact h j₀ (by omega) arg₁ arg₂ harg i hi π₁ π₂ hstk
    | j' + 1, .VDelay _ _, .VDelay _ _ =>
      simp only [ValueRefinesK] at h ⊢
      intro j₀ hj₀ i hi π₁ π₂ hstk
      exact h j₀ (by omega) i hi π₁ π₂ hstk
    | j' + 1, .VConstr _ _, .VConstr _ _ =>
      simp only [ValueRefinesK] at h ⊢
      exact ⟨h.1, listRel_mono (fun a b hab => ih j' (by omega) a b hab) h.2⟩
    | j' + 1, .VBuiltin _ _ _, .VBuiltin _ _ _ =>
      simp only [ValueRefinesK] at h ⊢
      exact ⟨h.1, h.2.1, listRel_mono (fun a b hab => ih j' (by omega) a b hab) h.2.2⟩
    | _, .VCon _, .VLam _ _ | _, .VCon _, .VDelay _ _ | _, .VCon _, .VConstr _ _
    | _, .VCon _, .VBuiltin _ _ _ | _, .VLam _ _, .VCon _ | _, .VLam _ _, .VDelay _ _
    | _, .VLam _ _, .VConstr _ _ | _, .VLam _ _, .VBuiltin _ _ _
    | _, .VDelay _ _, .VCon _ | _, .VDelay _ _, .VLam _ _ | _, .VDelay _ _, .VConstr _ _
    | _, .VDelay _ _, .VBuiltin _ _ _ | _, .VConstr _ _, .VCon _
    | _, .VConstr _ _, .VLam _ _ | _, .VConstr _ _, .VDelay _ _
    | _, .VConstr _ _, .VBuiltin _ _ _ | _, .VBuiltin _ _ _, .VCon _
    | _, .VBuiltin _ _ _, .VLam _ _ | _, .VBuiltin _ _ _, .VDelay _ _
    | _, .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at h

theorem valueRefinesK_mono {j k : Nat} (hjk : j ≤ k)
    (v₁ v₂ : CekValue) (h : ValueRefinesK k v₁ v₂) : ValueRefinesK j v₁ v₂ :=
  valueRefinesK_mono_le k j hjk v₁ v₂ h

--------------------------------------------------------------------------------
-- 3. Refines tower: theorems
--
-- `StackRefK`, `BehRefinesK`, `EnvRefinesK`, `OpenRefinesK`, `OpenRefines`
-- are defined in `Moist.VerifiedNewNew.Definitions.StepIndexed`. Theorems
-- about them (and the proof-local `AtLeastEnvRefinesK`) stay in this file.
--------------------------------------------------------------------------------

/-- **Strict** pointwise env relation: both envs have the same length and
    every position `1..length` is a `some` pair of `ValueRefinesK`-related
    values. No `(none, none)` ghost — consistent with the strict `EnvRefinesK`.
    Mirrors `AtLeastEnvEqK` in `Soundness.lean`. -/
def AtLeastEnvRefinesK (k : Nat) (ρ_l ρ_r : CekEnv) : Prop :=
  ρ_l.length = ρ_r.length ∧
  ∀ n, 0 < n → n ≤ ρ_l.length →
    ∃ v_l v_r, ρ_l.lookup n = some v_l ∧ ρ_r.lookup n = some v_r ∧ ValueRefinesK k v_l v_r

theorem atLeastEnvRefinesK_nil (k : Nat) : AtLeastEnvRefinesK k .nil .nil := by
  refine ⟨rfl, ?_⟩
  intro n _ hn_len
  simp [CekEnv.length] at hn_len
  omega

/-- Bridge from the length-indexed pointwise relation to the depth-indexed
    strict relation, given that the depth `d` is within the env length. -/
theorem atLeastEnvRefinesK_to_envRefinesK {k d : Nat} {ρ_l ρ_r : CekEnv}
    (h : AtLeastEnvRefinesK k ρ_l ρ_r) (hd : d ≤ ρ_l.length) : EnvRefinesK k d ρ_l ρ_r := by
  intro n hn hnd
  exact h.2 n hn (Nat.le_trans hnd hd)

theorem atLeastEnvRefinesK_mono {j k : Nat} (hjk : j ≤ k) {ρ_l ρ_r : CekEnv}
    (h : AtLeastEnvRefinesK k ρ_l ρ_r) : AtLeastEnvRefinesK j ρ_l ρ_r := by
  refine ⟨h.1, ?_⟩
  intro n hn hnlen
  obtain ⟨v_l, v_r, hl, hr, hrel⟩ := h.2 n hn hnlen
  exact ⟨v_l, v_r, hl, hr, valueRefinesK_mono hjk _ _ hrel⟩

theorem atLeastEnvRefinesK_extend {k : Nat} {ρ_l ρ_r : CekEnv} {v_l v_r : CekValue}
    (hρ : AtLeastEnvRefinesK k ρ_l ρ_r) (hv : ValueRefinesK k v_l v_r) :
    AtLeastEnvRefinesK k (ρ_l.extend v_l) (ρ_r.extend v_r) := by
  refine ⟨?_, ?_⟩
  · simp [CekEnv.extend, CekEnv.length, hρ.1]
  · intro n hn hnlen
    by_cases h1 : n = 1
    · subst h1
      refine ⟨v_l, v_r, ?_, ?_, hv⟩
      · simp [CekEnv.extend, CekEnv.lookup]
      · simp [CekEnv.extend, CekEnv.lookup]
    · have hn2 : n ≥ 2 := by omega
      have hlen_ext : (ρ_l.extend v_l).length = ρ_l.length + 1 := by
        simp [CekEnv.extend, CekEnv.length]
      rw [hlen_ext] at hnlen
      match n, hn2 with
      | n' + 2, _ =>
        obtain ⟨w_l, w_r, hl, hr, hrel⟩ := hρ.2 (n' + 1) (by omega) (by omega)
        refine ⟨w_l, w_r, ?_, ?_, hrel⟩
        · simp [CekEnv.extend, CekEnv.lookup]; exact hl
        · simp [CekEnv.extend, CekEnv.lookup]; exact hr

--------------------------------------------------------------------------------
-- 4. TermSubstL — TermSubst without the swapInv constructor
--
-- `fill_termSubst` never produces `swapInv`, so the refinement-direction
-- proof can case-analyze on a swap-only variant and skip the bidirectional
-- hypothesis obligations.
--------------------------------------------------------------------------------

mutual
inductive TermSubstL (t₁ t₂ : Term) : Term → Term → Prop
  | swap     : TermSubstL t₁ t₂ t₁ t₂
  | varRefl  (n : Nat) : TermSubstL t₁ t₂ (.Var n) (.Var n)
  | constRefl (c : Const × BuiltinType) : TermSubstL t₁ t₂ (.Constant c) (.Constant c)
  | builtinRefl (b : BuiltinFun) : TermSubstL t₁ t₂ (.Builtin b) (.Builtin b)
  | errorRefl : TermSubstL t₁ t₂ .Error .Error
  | lam {x : Nat} {b₁ b₂ : Term} :
      TermSubstL t₁ t₂ b₁ b₂ → TermSubstL t₁ t₂ (.Lam x b₁) (.Lam x b₂)
  | apply {f₁ f₂ a₁ a₂ : Term} :
      TermSubstL t₁ t₂ f₁ f₂ → TermSubstL t₁ t₂ a₁ a₂ →
      TermSubstL t₁ t₂ (.Apply f₁ a₁) (.Apply f₂ a₂)
  | force {e₁ e₂ : Term} :
      TermSubstL t₁ t₂ e₁ e₂ → TermSubstL t₁ t₂ (.Force e₁) (.Force e₂)
  | delay {e₁ e₂ : Term} :
      TermSubstL t₁ t₂ e₁ e₂ → TermSubstL t₁ t₂ (.Delay e₁) (.Delay e₂)
  | constr {tag : Nat} {as₁ as₂ : List Term} :
      TermListSubstL t₁ t₂ as₁ as₂ →
      TermSubstL t₁ t₂ (.Constr tag as₁) (.Constr tag as₂)
  | case {s₁ s₂ : Term} {as₁ as₂ : List Term} :
      TermSubstL t₁ t₂ s₁ s₂ → TermListSubstL t₁ t₂ as₁ as₂ →
      TermSubstL t₁ t₂ (.Case s₁ as₁) (.Case s₂ as₂)

inductive TermListSubstL (t₁ t₂ : Term) : List Term → List Term → Prop
  | nil  : TermListSubstL t₁ t₂ [] []
  | cons {a b : Term} {as bs : List Term} :
      TermSubstL t₁ t₂ a b → TermListSubstL t₁ t₂ as bs →
      TermListSubstL t₁ t₂ (a :: as) (b :: bs)
end

mutual
def TermSubstL.refl {t₁ t₂ : Term} : ∀ (t : Term), TermSubstL t₁ t₂ t t
  | .Var n => .varRefl n
  | .Constant c => .constRefl c
  | .Builtin b => .builtinRefl b
  | .Error => .errorRefl
  | .Lam _ b => .lam (TermSubstL.refl b)
  | .Apply f a => .apply (TermSubstL.refl f) (TermSubstL.refl a)
  | .Force e => .force (TermSubstL.refl e)
  | .Delay e => .delay (TermSubstL.refl e)
  | .Constr _ as => .constr (TermListSubstL.refl as)
  | .Case s as => .case (TermSubstL.refl s) (TermListSubstL.refl as)

def TermListSubstL.refl {t₁ t₂ : Term} : ∀ (ts : List Term), TermListSubstL t₁ t₂ ts ts
  | [] => .nil
  | t :: rest => .cons (TermSubstL.refl t) (TermListSubstL.refl rest)
end

/-- `fill C` produces `TermSubstL`-related terms — never uses `swapInv`. -/
theorem fill_termSubstL (C : Context) (t₁ t₂ : Term) :
    TermSubstL t₁ t₂ (fill C t₁) (fill C t₂) := by
  induction C with
  | Hole => exact .swap
  | Lam x C ih => exact .lam ih
  | AppLeft C e ih => exact .apply ih (TermSubstL.refl e)
  | AppRight e C ih => exact .apply (TermSubstL.refl e) ih
  | Delay C ih => exact .delay ih
  | Force C ih => exact .force ih
  | Constr tag lefts C rights ih =>
    refine .constr ?_
    show TermListSubstL t₁ t₂
      (lefts ++ [fill C t₁] ++ rights) (lefts ++ [fill C t₂] ++ rights)
    rw [List.append_assoc, List.append_assoc]
    show TermListSubstL t₁ t₂
      (lefts ++ fill C t₁ :: rights) (lefts ++ fill C t₂ :: rights)
    exact termListSubstL_around lefts rights ih
  | Case C alts ih =>
    exact .case ih (TermListSubstL.refl alts)
  | CaseAlt scrut lefts C rights ih =>
    refine .case (TermSubstL.refl scrut) ?_
    show TermListSubstL t₁ t₂
      (lefts ++ [fill C t₁] ++ rights) (lefts ++ [fill C t₂] ++ rights)
    rw [List.append_assoc, List.append_assoc]
    show TermListSubstL t₁ t₂
      (lefts ++ fill C t₁ :: rights) (lefts ++ fill C t₂ :: rights)
    exact termListSubstL_around lefts rights ih
where
  termListSubstL_around : ∀ (pre post : List Term) {a b : Term},
      TermSubstL t₁ t₂ a b →
      TermListSubstL t₁ t₂ (pre ++ a :: post) (pre ++ b :: post)
    | [], post, _, _, hab =>
        .cons hab (TermListSubstL.refl post)
    | p :: ps, post, _, _, hab =>
        .cons (TermSubstL.refl p) (termListSubstL_around ps post hab)

--------------------------------------------------------------------------------
-- 5. Helper lemmas on TermListSubstL
--------------------------------------------------------------------------------

/-- Lookup in a `TermListSubstL`-related list at a specific index returns
    `TermSubstL`-related elements (or both `none`). -/
theorem termListSubstL_getElem? {t₁ t₂ : Term} :
    ∀ {l_l l_r : List Term}, TermListSubstL t₁ t₂ l_l l_r → ∀ (n : Nat),
      (l_l[n]? = none ∧ l_r[n]? = none) ∨
      (∃ a_l a_r, l_l[n]? = some a_l ∧ l_r[n]? = some a_r ∧
        TermSubstL t₁ t₂ a_l a_r)
  | _, _, .nil, _ => .inl ⟨rfl, rfl⟩
  | _, _, .cons (a := al) (b := ar) hh ht, n => by
    cases n with
    | zero => exact .inr ⟨al, ar, by simp, by simp, hh⟩
    | succ k =>
      have ih := termListSubstL_getElem? ht k
      cases ih with
      | inl h => obtain ⟨hl, hr⟩ := h; exact .inl ⟨by simp [hl], by simp [hr]⟩
      | inr h => obtain ⟨a_l, a_r, hl, hr, hab⟩ := h
                 exact .inr ⟨a_l, a_r, by simp [hl], by simp [hr], hab⟩

/-- `TermListSubstL`-related lists have the same length. -/
theorem termListSubstL_length_eq {t₁ t₂ : Term} :
    ∀ {l_l l_r : List Term}, TermListSubstL t₁ t₂ l_l l_r → l_l.length = l_r.length
  | _, _, .nil => rfl
  | _, _, .cons _ ht => by simp [termListSubstL_length_eq ht]

--------------------------------------------------------------------------------
-- 6. StackRefK helpers
--------------------------------------------------------------------------------

theorem stackRefK_mono {V : Nat → CekValue → CekValue → Prop} {i k : Nat}
    (hik : i ≤ k) {π₁ π₂ : Stack}
    (h : StackRefK V k π₁ π₂) : StackRefK V i π₁ π₂ :=
  fun j hj v₁ v₂ hv => h j (Nat.le_trans hj hik) v₁ v₂ hv

/-- The empty stack is `StackRefK`-related to itself. `.ret [] v` halts in one
    step, so `ObsRefinesK j` trivially holds. -/
theorem stackRefK_nil {V : Nat → CekValue → CekValue → Prop} (k : Nat) :
    StackRefK V k [] [] := by
  intro j _ v_l v_r _
  cases j with
  | zero =>
    obsRefinesK_zero_nonhalt_auto
  | succ j' =>
    obsRefinesK_of_step_auto
    simp only [step]
    exact obsRefinesK_halt j' v_l v_r

--------------------------------------------------------------------------------
-- 7. ListRel + ValueRefinesK helpers (mirror of ValueEqK versions)
--------------------------------------------------------------------------------

/-- Monotonicity of `ListRel (ValueRefinesK ·)` over step indices. -/
theorem listRel_valueRefinesK_mono {j k : Nat} (hjk : j ≤ k)
    {l₁ l₂ : List CekValue} (h : ListRel (ValueRefinesK k) l₁ l₂) :
    ListRel (ValueRefinesK j) l₁ l₂ :=
  listRel_mono (fun a b h => valueRefinesK_mono hjk a b h) h

/-- Reflexive `ListRel (ValueRefinesK j)` for a list of VCon values — the
    same reflexivity used by the Case scrutinee dispatch on `constToTagAndFields`. -/
theorem listRel_refl_vcon_refines (j : Nat) (l : List CekValue)
    (h : ∀ v ∈ l, ∃ c, v = .VCon c) : ListRel (ValueRefinesK j) l l := by
  induction l with
  | nil => trivial
  | cons v vs ih =>
    obtain ⟨c, rfl⟩ := h _ (.head _)
    refine ⟨?_, ih (fun w hw => h w (.tail _ hw))⟩
    cases j with
    | zero => simp only [ValueRefinesK]
    | succ => simp [ValueRefinesK]

--------------------------------------------------------------------------------
-- 8. Inversion helpers on ListRel / ValueRefinesK
--------------------------------------------------------------------------------

private theorem listRel_cons_inv {R : α → α → Prop} {a : α} {as : List α} {l₂ : List α}
    (h : ListRel R (a :: as) l₂) : ∃ b bs, l₂ = b :: bs ∧ R a b ∧ ListRel R as bs := by
  cases l₂ with
  | nil => exact absurd h id
  | cons b bs => exact ⟨b, bs, rfl, h.1, h.2⟩

private theorem listRel_nil_inv {R : α → α → Prop} {l₂ : List α}
    (h : ListRel R ([] : List α) l₂) : l₂ = [] := by
  cases l₂ with | nil => rfl | cons => exact absurd h id

private theorem valueRefinesK_vcon_inv {k : Nat} {c : Const} {v : CekValue}
    (h : ValueRefinesK k (.VCon c) v) : v = .VCon c := by
  match k, v with
  | 0, .VCon c' => simp only [ValueRefinesK] at h; cases h; rfl
  | 0, .VLam _ _ | 0, .VDelay _ _ | 0, .VConstr _ _ | 0, .VBuiltin _ _ _ =>
    simp only [ValueRefinesK] at h
  | _ + 1, .VCon c' => simp only [ValueRefinesK] at h; cases h; rfl
  | _ + 1, .VLam _ _ | _ + 1, .VDelay _ _ | _ + 1, .VConstr _ _ | _ + 1, .VBuiltin _ _ _ =>
    simp only [ValueRefinesK] at h

--------------------------------------------------------------------------------
-- 9. extractConsts_eq_refines
--------------------------------------------------------------------------------

private theorem extractConsts_eq_refines {k : Nat} {args₁ args₂ : List CekValue}
    (hargs : ListRel (ValueRefinesK k) args₁ args₂) :
    extractConsts args₁ = extractConsts args₂ := by
  induction args₁ generalizing args₂ with
  | nil => cases args₂ <;> simp_all [ListRel, extractConsts]
  | cons a₁ as₁ ih =>
    cases args₂ with
    | nil => simp [ListRel] at hargs
    | cons a₂ as₂ =>
      simp only [ListRel] at hargs
      obtain ⟨ha, has⟩ := hargs
      match a₁, a₂ with
      | .VCon c₁, .VCon c₂ =>
        have heq : c₁ = c₂ := by
          cases k with
          | zero => simp only [ValueRefinesK] at ha; exact ha
          | succ => simp only [ValueRefinesK] at ha; exact ha
        subst heq
        simp only [extractConsts]; rw [ih has]
      | .VLam _ _, .VLam _ _ => simp [extractConsts]
      | .VDelay _ _, .VDelay _ _ => simp [extractConsts]
      | .VConstr _ _, .VConstr _ _ => simp [extractConsts]
      | .VBuiltin _ _ _, .VBuiltin _ _ _ => simp [extractConsts]
      | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
      | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
      | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
      | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
      | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
      | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
      | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
      | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
      | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at ha

--------------------------------------------------------------------------------
-- 10. evalBuiltinPassThrough_compat_refines
--------------------------------------------------------------------------------

set_option maxHeartbeats 6400000 in
private theorem evalBuiltinPassThrough_compat_refines {k : Nat} {b : BuiltinFun}
    {args₁ args₂ : List CekValue}
    (hargs : ListRel (ValueRefinesK k) args₁ args₂) :
    match evalBuiltinPassThrough b args₁, evalBuiltinPassThrough b args₂ with
    | some v₁, some v₂ => ValueRefinesK k v₁ v₂
    | none, none => True
    | _, _ => False := by
  by_cases hb : b = .IfThenElse ∨ b = .ChooseUnit ∨ b = .Trace ∨
                 b = .ChooseData ∨ b = .ChooseList ∨ b = .MkCons
  · rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · -- IfThenElse
      cases args₁ with
      | nil => rw [listRel_nil_inv hargs]; simp [evalBuiltinPassThrough]
      | cons e₁ r₁ =>
      obtain ⟨e₂, r₂, rfl, he, hr⟩ := listRel_cons_inv hargs; cases r₁ with
      | nil => rw [listRel_nil_inv hr]; simp [evalBuiltinPassThrough]
      | cons t₁ s₁ =>
      obtain ⟨t₂, s₂, rfl, ht, hs⟩ := listRel_cons_inv hr; cases s₁ with
      | nil => rw [listRel_nil_inv hs]; simp [evalBuiltinPassThrough]
      | cons c₁ u₁ =>
      obtain ⟨c₂, u₂, rfl, hc, hu⟩ := listRel_cons_inv hs
      match c₁ with
      | .VCon c_const =>
        rw [valueRefinesK_vcon_inv hc]
        cases u₁ with
        | nil => rw [listRel_nil_inv hu]
                 cases c_const <;> simp [evalBuiltinPassThrough]
                 rename_i bv; cases bv <;> simp <;> assumption
        | cons _ _ =>
          obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hu
          cases c_const <;> simp [evalBuiltinPassThrough]
      | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
        match c₂ with
        | .VCon _ => simp only [ValueRefinesK] at hc
        | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
          cases u₁ with
          | nil => rw [listRel_nil_inv hu]; simp [evalBuiltinPassThrough]
          | cons _ _ =>
            obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hu; simp [evalBuiltinPassThrough]
    · -- ChooseUnit
      cases args₁ with
      | nil => rw [listRel_nil_inv hargs]; simp [evalBuiltinPassThrough]
      | cons r₁ s₁ =>
      obtain ⟨r₂, s₂, rfl, hr, hs⟩ := listRel_cons_inv hargs; cases s₁ with
      | nil => rw [listRel_nil_inv hs]; simp [evalBuiltinPassThrough]
      | cons c₁ u₁ =>
      obtain ⟨c₂, u₂, rfl, hc, hu⟩ := listRel_cons_inv hs
      match c₁ with
      | .VCon c_const =>
        rw [valueRefinesK_vcon_inv hc]
        cases u₁ with
        | nil => rw [listRel_nil_inv hu]
                 cases c_const <;> simp [evalBuiltinPassThrough]
                 exact hr
        | cons _ _ =>
          obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hu
          cases c_const <;> simp [evalBuiltinPassThrough]
      | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
        match c₂ with
        | .VCon _ => simp only [ValueRefinesK] at hc
        | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
          cases u₁ with
          | nil => rw [listRel_nil_inv hu]; simp [evalBuiltinPassThrough]
          | cons _ _ =>
            obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hu; simp [evalBuiltinPassThrough]
    · -- Trace
      cases args₁ with
      | nil => rw [listRel_nil_inv hargs]; simp [evalBuiltinPassThrough]
      | cons r₁ s₁ =>
      obtain ⟨r₂, s₂, rfl, hr, hs⟩ := listRel_cons_inv hargs; cases s₁ with
      | nil => rw [listRel_nil_inv hs]; simp [evalBuiltinPassThrough]
      | cons c₁ u₁ =>
      obtain ⟨c₂, u₂, rfl, hc, hu⟩ := listRel_cons_inv hs
      match c₁ with
      | .VCon c_const =>
        rw [valueRefinesK_vcon_inv hc]
        cases u₁ with
        | nil => rw [listRel_nil_inv hu]
                 cases c_const <;> simp [evalBuiltinPassThrough]
                 exact hr
        | cons _ _ =>
          obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hu
          cases c_const <;> simp [evalBuiltinPassThrough]
      | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
        match c₂ with
        | .VCon _ => simp only [ValueRefinesK] at hc
        | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
          cases u₁ with
          | nil => rw [listRel_nil_inv hu]; simp [evalBuiltinPassThrough]
          | cons _ _ =>
            obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hu; simp [evalBuiltinPassThrough]
    · -- ChooseData
      cases args₁ with
      | nil => rw [listRel_nil_inv hargs]; simp [evalBuiltinPassThrough]
      | cons a₁ r₁ =>
      obtain ⟨a₂, r₂, rfl, ha, hr⟩ := listRel_cons_inv hargs; cases r₁ with
      | nil => rw [listRel_nil_inv hr]; simp [evalBuiltinPassThrough]
      | cons b₁ s₁ =>
      obtain ⟨b₂, s₂, rfl, hb, hs⟩ := listRel_cons_inv hr; cases s₁ with
      | nil => rw [listRel_nil_inv hs]; simp [evalBuiltinPassThrough]
      | cons c₁ t₁ =>
      obtain ⟨c₂, t₂, rfl, hc_val, ht⟩ := listRel_cons_inv hs; cases t₁ with
      | nil => rw [listRel_nil_inv ht]; simp [evalBuiltinPassThrough]
      | cons d₁ u₁ =>
      obtain ⟨d₂, u₂, rfl, hd, hu⟩ := listRel_cons_inv ht; cases u₁ with
      | nil => rw [listRel_nil_inv hu]; simp [evalBuiltinPassThrough]
      | cons e₁ w₁ =>
      obtain ⟨e₂, w₂, rfl, he_val, hw⟩ := listRel_cons_inv hu
      cases w₁ with
      | nil => rw [listRel_nil_inv hw]; simp [evalBuiltinPassThrough]
      | cons f₁ x₁ =>
      obtain ⟨f₂, x₂, rfl, hf, hx⟩ := listRel_cons_inv hw
      match f₁ with
      | .VCon c_const =>
        rw [valueRefinesK_vcon_inv hf]
        cases x₁ with
        | nil => rw [listRel_nil_inv hx]
                 cases c_const <;> simp [evalBuiltinPassThrough]
                 rename_i dat; cases dat <;> simp <;> assumption
        | cons _ _ =>
          obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hx
          cases c_const <;> simp [evalBuiltinPassThrough]
      | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
        match f₂ with
        | .VCon _ => simp only [ValueRefinesK] at hf
        | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
          cases x₁ with
          | nil => rw [listRel_nil_inv hx]; simp [evalBuiltinPassThrough]
          | cons _ _ =>
            obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hx; simp [evalBuiltinPassThrough]
    · -- ChooseList
      cases args₁ with
      | nil => rw [listRel_nil_inv hargs]; simp [evalBuiltinPassThrough]
      | cons r₁ s₁ =>
      obtain ⟨r₂, s₂, rfl, hr, hs⟩ := listRel_cons_inv hargs; cases s₁ with
      | nil => rw [listRel_nil_inv hs]; simp [evalBuiltinPassThrough]
      | cons t₁ u₁ =>
      obtain ⟨t₂, u₂, rfl, ht, hu⟩ := listRel_cons_inv hs; cases u₁ with
      | nil => rw [listRel_nil_inv hu]; simp [evalBuiltinPassThrough]
      | cons c₁ w₁ =>
      obtain ⟨c₂, w₂, rfl, hc, hw⟩ := listRel_cons_inv hu
      match c₁ with
      | .VCon c_const =>
        rw [valueRefinesK_vcon_inv hc]
        cases w₁ with
        | nil => rw [listRel_nil_inv hw]
                 cases c_const <;> simp [evalBuiltinPassThrough]
                 all_goals (split <;> assumption)
        | cons _ _ =>
          obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hw
          cases c_const <;> simp [evalBuiltinPassThrough]
      | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
        match c₂ with
        | .VCon _ => simp only [ValueRefinesK] at hc
        | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
          cases w₁ with
          | nil => rw [listRel_nil_inv hw]; simp [evalBuiltinPassThrough]
          | cons _ _ =>
            obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hw; simp [evalBuiltinPassThrough]
    · -- MkCons
      cases args₁ with
      | nil => rw [listRel_nil_inv hargs]; simp [evalBuiltinPassThrough]
      | cons a₁ r₁ =>
      obtain ⟨a₂, r₂, rfl, ha, hr⟩ := listRel_cons_inv hargs; cases r₁ with
      | nil => rw [listRel_nil_inv hr]; simp [evalBuiltinPassThrough]
      | cons b₁ s₁ =>
      obtain ⟨b₂, s₂, rfl, hb, hs⟩ := listRel_cons_inv hr
      cases s₁ with
      | cons _ _ =>
        obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hs; simp [evalBuiltinPassThrough]
      | nil =>
      rw [listRel_nil_inv hs]
      match a₁ with
      | .VCon c_const =>
        rw [valueRefinesK_vcon_inv ha]
        cases c_const <;> simp [evalBuiltinPassThrough]
        rename_i tail₁
        match b₁, b₂ with
        | .VCon c₁, .VCon c₂ =>
          have hbeq : c₁ = c₂ := by cases k <;> (simp only [ValueRefinesK] at hb; exact hb)
          subst hbeq
          cases k <;> simp [ValueRefinesK]
        | .VLam _ _, .VLam _ _ | .VDelay _ _, .VDelay _ _
        | .VConstr _ _, .VConstr _ _ | .VBuiltin _ _ _, .VBuiltin _ _ _ => trivial
        | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _
        | .VCon _, .VConstr _ _ | .VCon _, .VBuiltin _ _ _
        | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
        | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
        | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _
        | .VDelay _ _, .VConstr _ _ | .VDelay _ _, .VBuiltin _ _ _
        | .VConstr _ _, .VCon _ | .VConstr _ _, .VLam _ _
        | .VConstr _ _, .VDelay _ _ | .VConstr _ _, .VBuiltin _ _ _
        | .VBuiltin _ _ _, .VCon _ | .VBuiltin _ _ _, .VLam _ _
        | .VBuiltin _ _ _, .VDelay _ _ | .VBuiltin _ _ _, .VConstr _ _ =>
          simp only [ValueRefinesK] at hb
      | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
        match a₂ with
        | .VCon _ => simp only [ValueRefinesK] at ha
        | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
          simp [evalBuiltinPassThrough]
  · have hb_not : b ≠ .IfThenElse ∧ b ≠ .ChooseUnit ∧ b ≠ .Trace ∧
                   b ≠ .ChooseData ∧ b ≠ .ChooseList ∧ b ≠ .MkCons :=
      ⟨fun h => hb (h ▸ .inl rfl), fun h => hb (h ▸ .inr (.inl rfl)),
       fun h => hb (h ▸ .inr (.inr (.inl rfl))),
       fun h => hb (h ▸ .inr (.inr (.inr (.inl rfl)))),
       fun h => hb (h ▸ .inr (.inr (.inr (.inr (.inl rfl))))),
       fun h => hb (h ▸ .inr (.inr (.inr (.inr (.inr rfl)))))⟩
    rw [evalBuiltinPassThrough_none_of_not_passthrough b args₁ hb_not,
        evalBuiltinPassThrough_none_of_not_passthrough b args₂ hb_not]; trivial

--------------------------------------------------------------------------------
-- 11. evalBuiltin_rel_refines / evalBuiltin_compat_refines
--------------------------------------------------------------------------------

private theorem evalBuiltin_rel_refines_any {k : Nat} {b : BuiltinFun}
    {args₁ args₂ : List CekValue}
    (hargs : ListRel (ValueRefinesK k) args₁ args₂) :
    match evalBuiltin b args₁, evalBuiltin b args₂ with
    | some v₁, some v₂ => ValueRefinesK k v₁ v₂
    | none, none => True
    | _, _ => False := by
  have h_ext := extractConsts_eq_refines hargs
  have h_pt := evalBuiltinPassThrough_compat_refines (b := b) hargs
  simp only [evalBuiltin]
  revert h_pt
  cases evalBuiltinPassThrough b args₁ <;> cases evalBuiltinPassThrough b args₂ <;> intro h_pt
  · rw [h_ext]; simp only []
    cases extractConsts args₂ with
    | none => simp
    | some consts =>
      simp only []
      cases evalBuiltinConst b consts with
      | none => simp
      | some c => cases k <;> simp [ValueRefinesK]
  · exact absurd h_pt id
  · exact absurd h_pt id
  · exact h_pt

theorem evalBuiltin_compat_refines {k : Nat} {b : BuiltinFun}
    {args₁ args₂ : List CekValue} {π₁ π₂ : Stack}
    (hargs : ListRel (ValueRefinesK k) args₁ args₂)
    (hπ : StackRefK ValueRefinesK k π₁ π₂) :
    ObsRefinesK k
      (match evalBuiltin b args₁ with | some v => State.ret π₁ v | none => .error)
      (match evalBuiltin b args₂ with | some v => State.ret π₂ v | none => .error) := by
  have h_rel := evalBuiltin_rel_refines_any (b := b) hargs
  revert h_rel
  cases evalBuiltin b args₁ <;> cases evalBuiltin b args₂ <;> intro h_rel
  · exact obsRefinesK_error _
  · exact absurd h_rel id
  · exact absurd h_rel id
  · match k with
    | 0 => exact obsRefinesK_zero_ret
    | m + 1 => exact hπ (m+1) (Nat.le_refl _) _ _ h_rel

--------------------------------------------------------------------------------
-- 12. applyArgFrames_stackRefK
--------------------------------------------------------------------------------

theorem applyArgFrames_stackRefK {j : Nat}
    {fields₁ fields₂ : List CekValue} {π₁ π₂ : Stack}
    (hfields : ListRel (ValueRefinesK j) fields₁ fields₂)
    (hπ : StackRefK ValueRefinesK j π₁ π₂) :
    StackRefK ValueRefinesK j (fields₁.map Frame.applyArg ++ π₁)
                               (fields₂.map Frame.applyArg ++ π₂) := by
  induction fields₁ generalizing fields₂ π₁ π₂ with
  | nil =>
    cases fields₂ with
    | nil => simp; exact hπ
    | cons => exact absurd hfields id
  | cons v₁ vs₁ ih =>
    cases fields₂ with
    | nil => exact absurd hfields id
    | cons v₂ vs₂ =>
    have hv := hfields.1; have hvs := hfields.2
    simp [List.map, List.cons_append]
    intro j' hj' w₁ w₂ hw
    match j' with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | n + 1 =>
    obsRefinesK_of_step_auto
    match w₁, w₂ with
    | .VLam body₁ ρ₁', .VLam body₂ ρ₂' =>
      simp only [step, ValueRefinesK] at hw ⊢
      exact hw n (by omega) v₁ v₂ (valueRefinesK_mono (by omega) v₁ v₂ hv)
        n (Nat.le_refl _) _ _
        (stackRefK_mono (by omega)
          (ih (listRel_valueRefinesK_mono (by omega) hvs)
              (stackRefK_mono (by omega) hπ)))
    | .VBuiltin b₁ args₁ ea₁, .VBuiltin b₂ args₂ ea₂ =>
      simp only [ValueRefinesK] at hw; obtain ⟨rfl, rfl, hargs⟩ := hw; simp only [step]
      split
      · split
        · rename_i rest _
          have hval : ValueRefinesK (n + 1)
              (.VBuiltin b₁ (v₁ :: args₁) rest) (.VBuiltin b₁ (v₂ :: args₂) rest) := by
            simp only [ValueRefinesK]; refine ⟨trivial, trivial, ?_⟩
            exact ⟨valueRefinesK_mono (by omega) v₁ v₂ hv,
                   listRel_valueRefinesK_mono (by omega) hargs⟩
          exact obsRefinesK_mono (by omega)
            ((stackRefK_mono (by omega)
              (ih (listRel_valueRefinesK_mono (by omega) hvs)
                   (stackRefK_mono (by omega) hπ))) (n+1) (by omega) _ _ hval)
        · exact evalBuiltin_compat_refines
            ⟨valueRefinesK_mono (by omega) v₁ v₂ hv,
             listRel_valueRefinesK_mono (by omega) hargs⟩
            (stackRefK_mono (by omega)
              (ih (listRel_valueRefinesK_mono (by omega) hvs)
                  (stackRefK_mono (by omega) hπ)))
      · exact obsRefinesK_error _
    | .VCon _, .VCon _ | .VDelay _ _, .VDelay _ _
    | .VConstr _ _, .VConstr _ _ => simp only [step]; exact obsRefinesK_error _
    | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
    | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
    | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
    | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
    | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
    | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
    | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
    | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
    | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at hw

--------------------------------------------------------------------------------
-- 13. constrField_helper_refines
--------------------------------------------------------------------------------

/-- Mirror of `constrField_helper` for the refinement direction. Parameterized
    over a `term_obsRefines` IH that handles the head term evaluation at
    smaller levels. -/
private theorem constrField_helper_refines {d : Nat} {t₁ t₂ : Term}
    (_h_open : OpenRefines d t₁ t₂)
    {tag : Nat} {k : Nat}
    (ih_te : ∀ i ≤ k, ∀ {ρ_l ρ_r : CekEnv} {π_l π_r : Stack} {tm_l tm_r : Term},
      AtLeastEnvRefinesK i ρ_l ρ_r → d ≤ ρ_l.length →
      StackRefK ValueRefinesK i π_l π_r →
      TermSubstL t₁ t₂ tm_l tm_r →
      ObsRefinesK i (.compute π_l ρ_l tm_l) (.compute π_r ρ_r tm_r)) :
    ∀ {ms_l ms_r : List Term}, TermListSubstL t₁ t₂ ms_l ms_r →
    ∀ {j : Nat}, j ≤ k →
      ∀ {done_l done_r : List CekValue} {ρ_l ρ_r : CekEnv} {π_l π_r : Stack},
        AtLeastEnvRefinesK j ρ_l ρ_r →
        d ≤ ρ_l.length →
        ListRel (ValueRefinesK j) done_l done_r →
        StackRefK ValueRefinesK j π_l π_r →
        StackRefK ValueRefinesK j (.constrField tag done_l ms_l ρ_l :: π_l)
                                   (.constrField tag done_r ms_r ρ_r :: π_r) := by
  intro ms_l ms_r hms
  induction ms_l generalizing ms_r with
  | nil =>
    cases hms with
    | nil =>
      intro j _ done_l done_r ρ_l ρ_r π_l π_r _ _ h_done hπ
      intro j' hj'_j v_l v_r hv
      match j' with
      | 0 =>
        obsRefinesK_zero_nonhalt_auto
      | n + 1 =>
        obsRefinesK_of_step_auto
        simp only [step]
        have hrev : ListRel (ValueRefinesK n) ((v_l :: done_l).reverse) ((v_r :: done_r).reverse) := by
          simp only [List.reverse_cons]
          exact listRel_append
            (listRel_reverse
              (listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) h_done))
            ⟨valueRefinesK_mono (by omega) v_l v_r hv, trivial⟩
        have hval : ValueRefinesK (n + 1)
            (.VConstr tag ((v_l :: done_l).reverse))
            (.VConstr tag ((v_r :: done_r).reverse)) := by
          cases n with
          | zero => simp only [ValueRefinesK]; exact ⟨trivial, hrev⟩
          | succ _ => simp only [ValueRefinesK]; exact ⟨trivial, hrev⟩
        exact obsRefinesK_mono (by omega) (hπ (n + 1) (by omega) _ _ hval)
  | cons m ms_l_rest ih_ms =>
    cases hms with
    | cons hm hms_rest =>
      intro j hj_k done_l done_r ρ_l ρ_r π_l π_r hρ hd h_done hπ
      intro j' hj'_j v_l v_r hv
      match j' with
      | 0 =>
        obsRefinesK_zero_nonhalt_auto
      | n + 1 =>
        obsRefinesK_of_step_auto
        simp only [step]
        apply ih_te n (by omega) (atLeastEnvRefinesK_mono (by omega) hρ) hd ?_ hm
        exact ih_ms hms_rest (by omega : n ≤ k) (atLeastEnvRefinesK_mono (by omega) hρ) hd
          (show ListRel (ValueRefinesK n) (v_l :: done_l) (v_r :: done_r) from
            ⟨valueRefinesK_mono (by omega) v_l v_r hv,
             listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) h_done⟩)
          (stackRefK_mono (by omega) hπ)

--------------------------------------------------------------------------------
-- 14. term_obsRefines — the main unidirectional semantic bridge
--
-- Mirror of `term_obsEq` for the refinement direction. Strong induction on
-- step index `k`; dispatch on TermSubstL (no swapInv, since `fill_termSubstL`
-- never produces it). The `swap` case invokes `h_open : OpenRefines d t₁ t₂`
-- directly. Other cases recurse.
--------------------------------------------------------------------------------

theorem term_obsRefines {d : Nat} {t₁ t₂ : Term} (h_open : OpenRefines d t₁ t₂) :
    ∀ (k : Nat) (i : Nat), i ≤ k →
      ∀ {ρ_l ρ_r : CekEnv} {π_l π_r : Stack} {tm_l tm_r : Term},
        AtLeastEnvRefinesK i ρ_l ρ_r →
        d ≤ ρ_l.length →
        StackRefK ValueRefinesK i π_l π_r →
        TermSubstL t₁ t₂ tm_l tm_r →
        ObsRefinesK i (.compute π_l ρ_l tm_l) (.compute π_r ρ_r tm_r) := by
  intro k
  induction k with
  | zero =>
    intro i hi
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    intros _ _ _ _ _ _ _ _ _ _
    obsRefinesK_zero_nonhalt_auto
  | succ m ih =>
    intro i hi
    by_cases hi_m : i ≤ m
    · exact ih i hi_m
    · have hi_eq : i = m + 1 := by omega
      subst hi_eq
      intro hρ hd hπ htm
      rename_i ρ_l ρ_r π_l π_r tm_l tm_r
      cases htm with
      | swap =>
        exact h_open (m+1) (m+1) (Nat.le_refl _) ρ_l ρ_r
          (atLeastEnvRefinesK_to_envRefinesK hρ hd) (m+1) (Nat.le_refl _) π_l π_r hπ
      | varRefl n =>
        obsRefinesK_of_step_auto
        simp only [step]
        by_cases hn : n = 0
        · subst hn
          have hl : ρ_l.lookup 0 = none := by cases ρ_l <;> rfl
          have hr : ρ_r.lookup 0 = none := by cases ρ_r <;> rfl
          rw [hl, hr]
          exact obsRefinesK_error _
        · have hpos : n > 0 := Nat.pos_of_ne_zero hn
          by_cases hnlen : n ≤ ρ_l.length
          · obtain ⟨v_l, v_r, hl, hr, hrel⟩ := hρ.2 n hpos hnlen
            rw [hl, hr]
            exact hπ m (Nat.le_succ m) v_l v_r
              (valueRefinesK_mono (Nat.le_succ m) v_l v_r hrel)
          · have hl : ρ_l.lookup n = none :=
              CekEnv.lookup_none_of_gt_length ρ_l n (by omega)
            have hnr : n > ρ_r.length := by rw [← hρ.1]; omega
            have hr : ρ_r.lookup n = none :=
              CekEnv.lookup_none_of_gt_length ρ_r n hnr
            rw [hl, hr]
            exact obsRefinesK_error _
      | constRefl c =>
        obsRefinesK_of_step_auto
        simp only [step]
        obtain ⟨kc, _⟩ := c
        apply hπ m (Nat.le_succ m) (.VCon kc) (.VCon kc)
        cases m with
        | zero => simp only [ValueRefinesK]
        | succ _ => simp only [ValueRefinesK]
      | builtinRefl b =>
        obsRefinesK_of_step_auto
        simp only [step]
        apply hπ m (Nat.le_succ m) (.VBuiltin b [] (expectedArgs b)) _
        cases m with
        | zero => simp only [ValueRefinesK]; exact ⟨trivial, trivial⟩
        | succ _ => simp only [ValueRefinesK, ListRel]; exact ⟨trivial, trivial, trivial⟩
      | errorRefl =>
        obsRefinesK_of_step_auto
        simp only [step]
        exact obsRefinesK_error _
      | lam hb =>
        obsRefinesK_of_step_auto
        simp only [step]
        apply hπ m (Nat.le_succ m)
        match m with
        | 0 => simp only [ValueRefinesK]
        | m' + 1 =>
          simp only [ValueRefinesK]
          intro j hj_m' arg_l arg_r harg i hi π_l_app π_r_app hπ_app
          apply ih i (by omega)
          · apply atLeastEnvRefinesK_extend
            · exact atLeastEnvRefinesK_mono (by omega) hρ
            · exact valueRefinesK_mono hi _ _ harg
          · show d ≤ (ρ_l.extend arg_l).length
            simp [CekEnv.extend, CekEnv.length]
            omega
          · exact hπ_app
          · exact hb
      | apply hf ha =>
        obsRefinesK_of_step_auto
        simp only [step]
        apply ih m (Nat.le_refl m) (atLeastEnvRefinesK_mono (Nat.le_succ m) hρ) hd ?_ hf
        intro j hj_m vf_l vf_r hvf
        match j with
        | 0 =>
          obsRefinesK_zero_nonhalt_auto
        | j' + 1 =>
          obsRefinesK_of_step_auto
          simp only [step]
          apply ih j' (by omega) (atLeastEnvRefinesK_mono (by omega) hρ) hd ?_ ha
          intro j'' hj''_j' w_l w_r hw
          match j'' with
          | 0 =>
            obsRefinesK_zero_nonhalt_auto
          | j''' + 1 =>
            obsRefinesK_of_step_auto
            match vf_l, vf_r with
            | .VCon _, .VCon _ => simp only [step]; exact obsRefinesK_error _
            | .VDelay _ _, .VDelay _ _ => simp only [step]; exact obsRefinesK_error _
            | .VConstr _ _, .VConstr _ _ => simp only [step]; exact obsRefinesK_error _
            | .VLam b_lv ρ_lv, .VLam b_rv ρ_rv =>
              simp only [step]
              simp only [ValueRefinesK] at hvf
              apply hvf j''' (by omega) w_l w_r
                (valueRefinesK_mono (Nat.le_succ _) _ _ hw)
                j''' (Nat.le_refl _) π_l π_r
              intro i' hi' x_l x_r hx
              exact hπ i' (by omega) x_l x_r hx
            | .VBuiltin b args_l ea, .VBuiltin _ args_r _ =>
              simp only [ValueRefinesK] at hvf
              obtain ⟨rfl, rfl, hargs_rel⟩ := hvf
              simp only [step]
              split
              · split
                · rename_i rest _
                  have hval : ValueRefinesK (j''' + 1)
                      (.VBuiltin b (w_l :: args_l) rest)
                      (.VBuiltin b (w_r :: args_r) rest) := by
                    simp only [ValueRefinesK]
                    refine ⟨trivial, trivial, ?_⟩
                    simp only [ListRel]
                    exact ⟨valueRefinesK_mono (by omega) w_l w_r hw,
                           listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) hargs_rel⟩
                  exact obsRefinesK_mono (by omega : j''' ≤ j''' + 1)
                    (hπ (j''' + 1) (by omega) _ _ hval)
                · exact evalBuiltin_compat_refines
                    (by simp only [ListRel]
                        exact ⟨valueRefinesK_mono (by omega) w_l w_r hw,
                               listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) hargs_rel⟩)
                    (stackRefK_mono (by omega) hπ)
              · exact obsRefinesK_error _
            | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
            | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
            | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
            | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
            | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
            | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
            | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
            | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
            | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at hvf
      | force he =>
        obsRefinesK_of_step_auto
        simp only [step]
        apply ih m (Nat.le_refl m) (atLeastEnvRefinesK_mono (Nat.le_succ m) hρ) hd ?_ he
        intro j hj_m vf_l vf_r hvf
        match j with
        | 0 =>
          obsRefinesK_zero_nonhalt_auto
        | j' + 1 =>
          obsRefinesK_of_step_auto
          match vf_l, vf_r with
          | .VCon _, .VCon _ => simp only [step]; exact obsRefinesK_error _
          | .VLam _ _, .VLam _ _ => simp only [step]; exact obsRefinesK_error _
          | .VConstr _ _, .VConstr _ _ => simp only [step]; exact obsRefinesK_error _
          | .VDelay b_lv ρ_lv, .VDelay b_rv ρ_rv =>
            simp only [step, ValueRefinesK] at hvf ⊢
            apply hvf j' (Nat.le_refl _) j' (Nat.le_refl _) π_l π_r
            intro i' hi' w_l w_r hw
            exact hπ i' (by omega) w_l w_r hw
          | .VBuiltin b args_l ea, .VBuiltin _ args_r _ =>
            simp only [ValueRefinesK] at hvf
            obtain ⟨rfl, rfl, hargs_rel⟩ := hvf
            simp only [step]
            split
            · split
              · rename_i rest _
                have hval : ValueRefinesK (j' + 1)
                    (.VBuiltin b args_l rest) (.VBuiltin b args_r rest) := by
                  simp only [ValueRefinesK]; exact ⟨trivial, trivial, hargs_rel⟩
                exact obsRefinesK_mono (by omega : j' ≤ j' + 1)
                  (hπ (j' + 1) (by omega) _ _ hval)
              · exact evalBuiltin_compat_refines hargs_rel (stackRefK_mono (by omega) hπ)
            · exact obsRefinesK_error _
          | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
          | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
          | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
          | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
          | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
          | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
          | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
          | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
          | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at hvf
      | delay hb =>
        obsRefinesK_of_step_auto
        simp only [step]
        apply hπ m (Nat.le_succ m)
        match m with
        | 0 => simp only [ValueRefinesK]
        | m' + 1 =>
          simp only [ValueRefinesK]
          intro j hj_m' i hi π_l_app π_r_app hπ_app
          apply ih i (by omega)
          · exact atLeastEnvRefinesK_mono (by omega) hρ
          · exact hd
          · exact hπ_app
          · exact hb
      | constr hms =>
        cases hms with
        | nil =>
          obsRefinesK_of_step_auto
          simp only [step]
          apply hπ m (Nat.le_succ m) (.VConstr _ []) (.VConstr _ [])
          cases m with
          | zero => simp only [ValueRefinesK]
          | succ _ => simp only [ValueRefinesK, ListRel]; exact ⟨trivial, trivial⟩
        | cons hm hms_rest =>
          obsRefinesK_of_step_auto
          simp only [step]
          apply ih m (Nat.le_refl m) (atLeastEnvRefinesK_mono (Nat.le_succ m) hρ) hd ?_ hm
          exact constrField_helper_refines h_open ih hms_rest (Nat.le_refl m)
            (atLeastEnvRefinesK_mono (Nat.le_succ m) hρ) hd
            (show ListRel (ValueRefinesK m) [] [] from trivial)
            (stackRefK_mono (Nat.le_succ m) hπ)
      | case hs has =>
        rename_i as_l as_r
        obsRefinesK_of_step_auto
        simp only [step]
        apply ih m (Nat.le_refl m) (atLeastEnvRefinesK_mono (Nat.le_succ m) hρ) hd ?_ hs
        intro j hj_m vf_l vf_r hvf
        match j with
        | 0 =>
          obsRefinesK_zero_nonhalt_auto
        | j' + 1 =>
          obsRefinesK_of_step_auto
          match vf_l, vf_r with
          | .VConstr tag_l fields_l, .VConstr tag_r fields_r =>
            simp only [step]
            simp only [ValueRefinesK] at hvf
            obtain ⟨h_tag, h_fields⟩ := hvf
            subst h_tag
            have h_lk := termListSubstL_getElem? has tag_l
            cases h_lk with
            | inl h =>
              obtain ⟨hl, hr⟩ := h
              rw [hl, hr]
              exact obsRefinesK_error _
            | inr h =>
              obtain ⟨alt_l, alt_r, hl, hr, halt⟩ := h
              rw [hl, hr]
              apply ih j' (by omega) (atLeastEnvRefinesK_mono (by omega) hρ) hd ?_ halt
              exact applyArgFrames_stackRefK h_fields
                (stackRefK_mono (by omega) hπ)
          | .VCon c_l, .VCon c_r =>
            simp only [ValueRefinesK] at hvf
            subst hvf
            simp only [step]
            have hlen := termListSubstL_length_eq has
            rw [show as_r.length = as_l.length from hlen.symm]
            cases h_const : constToTagAndFields c_l with
            | none => exact obsRefinesK_error _
            | some triple =>
              obtain ⟨tag, numCtors, fields⟩ := triple
              dsimp only []
              by_cases hcond : (decide (numCtors > 0) && decide (as_l.length > numCtors)) = true
              · rw [if_pos hcond, if_pos hcond]
                exact obsRefinesK_error _
              · rw [if_neg hcond, if_neg hcond]
                have h_lk := termListSubstL_getElem? has tag
                cases h_lk with
                | inl h =>
                  obtain ⟨hl, hr⟩ := h
                  rw [hl, hr]
                  exact obsRefinesK_error _
                | inr h =>
                  obtain ⟨alt_l, alt_r, hl, hr, halt⟩ := h
                  rw [hl, hr]
                  apply ih j' (by omega) (atLeastEnvRefinesK_mono (by omega) hρ) hd ?_ halt
                  have hfields_vcon := constToTagAndFields_fields_vcon c_l
                  rw [h_const] at hfields_vcon
                  exact applyArgFrames_stackRefK
                    (listRel_refl_vcon_refines j' fields hfields_vcon)
                    (stackRefK_mono (by omega) hπ)
          | .VLam _ _, .VLam _ _ => simp only [step]; exact obsRefinesK_error _
          | .VDelay _ _, .VDelay _ _ => simp only [step]; exact obsRefinesK_error _
          | .VBuiltin _ _ _, .VBuiltin _ _ _ => simp only [step]; exact obsRefinesK_error _
          | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
          | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
          | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
          | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
          | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
          | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
          | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
          | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
          | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at hvf

--------------------------------------------------------------------------------
-- 15. soundness_refines — the public entry point (generalized to ∀ d)
--
-- Reuse: `Soundness.lean` already proved `soundness {d} : OpenEq d → CtxEq`
-- using per-side locality padding (`dummyEnv`, `locality_obsRefinesK`).
-- The Refines version reuses **exactly the same infrastructure** — only the
-- Refines-specific `atLeastEnvRefinesK_dummyEnv` helper is new. The core
-- locality transfer (`locality_obsRefinesK`) is already one-directional, so
-- it works for `ObsRefinesK` without any modification.
--
-- This is the `Refine ↔ Eq` correspondence: the proof of `soundness` (Eq)
-- already internally uses `locality_obsRefinesK` (one-directional locality)
-- as a building block for `locality_obsEqK` (bidirectional). We just hit the
-- same building block directly from the Refines side.
--------------------------------------------------------------------------------

open Moist.VerifiedNewNew.Contextual.Soundness
  (dummyEnv dummyEnv_length locality_obsRefinesK)
open Moist.VerifiedNewNew.Contextual.BisimRef (LocalState LocalEnv LocalStack)

/-- `dummyEnv n` is `AtLeastEnvRefinesK`-related to itself at any level.
    Mirrors `atLeastEnvEqK_dummyEnv` from `Soundness.lean`. The proof is
    identical modulo `ValueEqK` → `ValueRefinesK`, which are both
    reflexive on `VCon .Unit`. -/
theorem atLeastEnvRefinesK_dummyEnv (k n : Nat) :
    AtLeastEnvRefinesK k (dummyEnv n) (dummyEnv n) := by
  induction n with
  | zero =>
    refine ⟨rfl, ?_⟩
    intro m _ hmlen
    simp [dummyEnv, CekEnv.length] at hmlen
    omega
  | succ m ih =>
    refine ⟨rfl, ?_⟩
    intro j hj hjlen
    by_cases h1 : j = 1
    · subst h1
      refine ⟨.VCon .Unit, .VCon .Unit, ?_, ?_, ?_⟩
      · show (CekEnv.cons _ (dummyEnv m)).lookup 1 = some _
        rfl
      · show (CekEnv.cons _ (dummyEnv m)).lookup 1 = some _
        rfl
      · cases k <;> simp only [ValueRefinesK]
    · have hj2 : j ≥ 2 := by omega
      have hlen : (dummyEnv (m + 1)).length = m + 1 := dummyEnv_length (m + 1)
      rw [hlen] at hjlen
      match j, hj2 with
      | j' + 2, _ =>
        have hjlen' : j' + 1 ≤ (dummyEnv m).length := by
          rw [dummyEnv_length m]; omega
        obtain ⟨v_l, v_r, hl, hr, hrel⟩ := ih.2 (j' + 1) (by omega) hjlen'
        refine ⟨v_l, v_r, ?_, ?_, hrel⟩
        · show (CekEnv.cons _ (dummyEnv m)).lookup (j' + 2) = some v_l
          exact hl
        · show (CekEnv.cons _ (dummyEnv m)).lookup (j' + 2) = some v_r
          exact hr

/-- **Unidirectional soundness**: `OpenRefines d` implies `CtxRefines` for
    *any* `d`. Proof reuses everything from `Soundness.lean`:

    * `dummyEnv d` pads the empty env to length `d` with matching
      `VCon .Unit`s.
    * `term_obsRefines` is applied on the padded envs (the `d ≤ length`
      invariant is trivially satisfied).
    * `locality_obsRefinesK` (from `Soundness.lean`) transfers each
      `ObsRefinesK`-at-level-`n` from the padded setting back to the
      unpadded empty-env setting, using `LocalState` locality on states
      that share the `closedAt 0` term.

    The `Refine ↔ Eq` correspondence: `locality_obsRefinesK` is
    unidirectional and already usable here. The Eq version of
    `soundness` packages two calls to `locality_obsRefinesK` into
    `locality_obsEqK`; we use only one of them. -/
theorem soundness_refines {d : Nat} {t₁ t₂ : Term}
    (h_open : OpenRefines d t₁ t₂)
    (h_close_pres : ∀ (C : Context),
      closedAt 0 (fill C t₁) = true → closedAt 0 (fill C t₂) = true) :
    CtxRefines t₁ t₂ := by
  intro C h_c1
  have h_c2 := h_close_pres C h_c1
  refine ⟨h_c2, ?_⟩
  -- LocalState relates (compute [] .nil …) and (compute [] (dummyEnv d) …)
  -- when the term is `closedAt 0`, via the trivial `LocalEnv 0` and
  -- empty-stack relations.
  have hls₁ : LocalState (.compute [] .nil (fill C t₁))
                         (.compute [] (dummyEnv d) (fill C t₁)) :=
    LocalState.compute LocalEnv.zero h_c1 LocalStack.nil
  have hls₂ : LocalState (.compute [] .nil (fill C t₂))
                         (.compute [] (dummyEnv d) (fill C t₂)) :=
    LocalState.compute LocalEnv.zero h_c2 LocalStack.nil
  refine ⟨?_, ?_⟩
  · rintro ⟨v, n, hs⟩
    have h_obs : ObsRefinesK n
        (.compute [] (dummyEnv d) (fill C t₁))
        (.compute [] (dummyEnv d) (fill C t₂)) :=
      term_obsRefines h_open n n (Nat.le_refl _)
        (atLeastEnvRefinesK_dummyEnv n d)
        (by rw [dummyEnv_length]; exact Nat.le_refl _)
        (stackRefK_nil n) (fill_termSubstL C t₁ t₂)
    exact (locality_obsRefinesK n hls₁ hls₂ h_obs).1 v ⟨n, Nat.le_refl _, hs⟩
  · rintro ⟨n, hs⟩
    have h_obs : ObsRefinesK n
        (.compute [] (dummyEnv d) (fill C t₁))
        (.compute [] (dummyEnv d) (fill C t₂)) :=
      term_obsRefines h_open n n (Nat.le_refl _)
        (atLeastEnvRefinesK_dummyEnv n d)
        (by rw [dummyEnv_length]; exact Nat.le_refl _)
        (stackRefK_nil n) (fill_termSubstL C t₁ t₂)
    exact (locality_obsRefinesK n hls₁ hls₂ h_obs).2 n (Nat.le_refl _) hs

/-- `soundness_refines_d` alias — kept under the historical name for
    downstream consumers (notably `MIR.lean`). -/
theorem soundness_refines_d {d : Nat} {t₁ t₂ : Term}
    (h_open : OpenRefines d t₁ t₂)
    (h_close_pres : ∀ (C : Context),
      closedAt 0 (fill C t₁) = true → closedAt 0 (fill C t₂) = true) :
    CtxRefines t₁ t₂ :=
  soundness_refines h_open h_close_pres

/-- Per-context observation form: given `OpenRefines d t₁ t₂` and closedness
    hypotheses on a specific context `C`, produce the `ObsRefines` directly
    without any closedness-preservation packaging. Useful for call sites
    that already have both closednesses in hand (e.g. `MIRCtxRefines`,
    which takes both `hC1` and `hC2` in its observation clause). -/
theorem obsRefines_of_openRefines {d : Nat} {t₁ t₂ : Term}
    (h_open : OpenRefines d t₁ t₂) (C : Context)
    (h_c1 : closedAt 0 (fill C t₁) = true)
    (h_c2 : closedAt 0 (fill C t₂) = true) :
    ObsRefines (.compute [] .nil (fill C t₁)) (.compute [] .nil (fill C t₂)) := by
  have hls₁ : LocalState (.compute [] .nil (fill C t₁))
                         (.compute [] (dummyEnv d) (fill C t₁)) :=
    LocalState.compute LocalEnv.zero h_c1 LocalStack.nil
  have hls₂ : LocalState (.compute [] .nil (fill C t₂))
                         (.compute [] (dummyEnv d) (fill C t₂)) :=
    LocalState.compute LocalEnv.zero h_c2 LocalStack.nil
  refine ⟨?_, ?_⟩
  · rintro ⟨v, n, hs⟩
    have h_obs : ObsRefinesK n
        (.compute [] (dummyEnv d) (fill C t₁))
        (.compute [] (dummyEnv d) (fill C t₂)) :=
      term_obsRefines h_open n n (Nat.le_refl _)
        (atLeastEnvRefinesK_dummyEnv n d)
        (by rw [dummyEnv_length]; exact Nat.le_refl _)
        (stackRefK_nil n) (fill_termSubstL C t₁ t₂)
    exact (locality_obsRefinesK n hls₁ hls₂ h_obs).1 v ⟨n, Nat.le_refl _, hs⟩
  · rintro ⟨n, hs⟩
    have h_obs : ObsRefinesK n
        (.compute [] (dummyEnv d) (fill C t₁))
        (.compute [] (dummyEnv d) (fill C t₂)) :=
      term_obsRefines h_open n n (Nat.le_refl _)
        (atLeastEnvRefinesK_dummyEnv n d)
        (by rw [dummyEnv_length]; exact Nat.le_refl _)
        (stackRefK_nil n) (fill_termSubstL C t₁ t₂)
    exact (locality_obsRefinesK n hls₁ hls₂ h_obs).2 n (Nat.le_refl _) hs

end Moist.VerifiedNewNew.Contextual.SoundnessRefines
