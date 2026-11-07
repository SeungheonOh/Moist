import Moist.Verified.Contextual.BisimRef
import Moist.Verified.Contextual.Guarded

/-! # Open refinement implies contextual refinement

`term_obsRefinesG` is the fundamental property for `TermSubstL`-related terms
(`fill C t₁` vs `fill C t₂`), proved once for any `Guard`; with locality
padding (`dummyEnv`, `locality_obsRefinesK`) it yields `CtxRefines` from open
refinement. `soundness_refines` / `obsRefines_of_openRefines` are the
`Guard.trivial` instances for `ValueRefinesK`; the well-formedness instance is
in `TermObsRefinesWF`.
-/

namespace Moist.Verified.Contextual.Soundness

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified.Equivalence
open Moist.Verified.Contextual

/-! Locality padding: `ObsRefinesK` transfers from padded environments back to
the original states, because closed terms ignore environment contents. -/

open Moist.Verified.Contextual.BisimRef

/-- Dummy environment of length `d` filled with `VCon .Unit` values.
    Used as padding to satisfy the `d ≤ ρ.length` invariant of
    `term_obsEq` while letting locality recover the empty-env result. -/
def dummyEnv : Nat → CekEnv
  | 0 => .nil
  | n + 1 => (dummyEnv n).extend (.VCon .Unit)

theorem dummyEnv_length : ∀ (n : Nat), (dummyEnv n).length = n
  | 0 => rfl
  | n + 1 => by
    show (dummyEnv n).length + 1 = n + 1
    rw [dummyEnv_length n]

/-- Locality transfer for `ObsRefinesK`. If `s₁, s₂` are each `LocalState`-
    related to `s₁', s₂'` respectively (the padded versions), then
    `ObsRefinesK` on the padded states transfers to `ObsRefinesK` on the
    unpadded states — because `LocalState` is preserved under `steps`
    and `.halt`/`.error` outcomes are invariant. -/
theorem locality_obsRefinesK (k : Nat) {s₁ s₂ s₁' s₂' : State}
    (hls₁ : LocalState s₁ s₁') (hls₂ : LocalState s₂ s₂')
    (href' : ObsRefinesK k s₁' s₂') : ObsRefinesK k s₁ s₂ := by
  refine ⟨?_, ?_⟩
  · -- halt: given s₁ halts, show s₂ reaches halt
    rintro v ⟨n, hn_le, hsteps_v⟩
    have hls_n : LocalState (steps n s₁) (steps n s₁') :=
      localState_preserves_steps n hls₁
    rw [hsteps_v] at hls_n
    obtain ⟨v', hs₁'⟩ := localState_halt_inv hls_n
    obtain ⟨v'', m, hm⟩ := href'.1 v' ⟨n, hn_le, hs₁'⟩
    have hls_m : LocalState (steps m s₂) (steps m s₂') :=
      localState_preserves_steps m hls₂
    rw [hm] at hls_m
    obtain ⟨v''', hs₂⟩ := localState_halt_inv' hls_m
    exact ⟨v''', m, hs₂⟩
  · -- error: given s₁ errors, show s₂ reaches error
    intro n hn_le hsteps_err
    have hls_n : LocalState (steps n s₁) (steps n s₁') :=
      localState_preserves_steps n hls₁
    rw [hsteps_err] at hls_n
    have hs₁'_err : steps n s₁' = .error := localState_error_inv hls_n
    obtain ⟨m, hm⟩ := href'.2 n hn_le hs₁'_err
    have hls_m : LocalState (steps m s₂) (steps m s₂') :=
      localState_preserves_steps m hls₂
    rw [hm] at hls_m
    have hs₂_err : steps m s₂ = .error := localState_error_inv' hls_m
    exact ⟨m, hs₂_err⟩

end Moist.Verified.Contextual.Soundness

namespace Moist.Verified.Contextual.SoundnessRefines

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified.Equivalence
open Moist.Verified.Contextual
open Moist.Verified.Contextual.Soundness

--------------------------------------------------------------------------------
-- 1. ObsRefinesK
--
-- We reuse the shared `ObsRefinesK` from Equivalence.lean which now includes
-- error preservation. The `obsRefinesK_of_obsEqK` projection picks either side
-- of an ObsEqK, and local helpers below specialize the Equivalence.lean
-- theorems for use inside `term_obsRefines`.
--------------------------------------------------------------------------------

theorem obsRefinesK_halt (k : Nat) (v_l v_r : CekValue) :
    ObsRefinesK k (.halt v_l) (.halt v_r) :=
  obsRefinesK_halt_halt k v_l v_r

theorem obsRefinesK_error (k : Nat) : ObsRefinesK k (.error : State) .error :=
  obsRefinesK_error_error k

--------------------------------------------------------------------------------
-- 2. ValueRefinesK monotonicity
--
-- `ValueRefinesK` itself is defined in
-- `Moist.Verified.Definitions.StepIndexed`. Theorems about it stay here.
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
-- 8. Builtins: `ValueRefinesK` relates a constant exactly to itself
--------------------------------------------------------------------------------

private theorem valueRefinesK_vcon_left {k : Nat} {c : Const} {v : CekValue}
    (h : ValueRefinesK k (.VCon c) v) : v = .VCon c := by
  cases k <;> cases v <;> simp only [ValueRefinesK] at h <;> rw [h]

private theorem valueRefinesK_vcon_right {k : Nat} {c : Const} {v : CekValue}
    (h : ValueRefinesK k v (.VCon c)) : v = .VCon c := by
  cases k <;> cases v <;> simp only [ValueRefinesK] at h <;> rw [h]

theorem evalBuiltin_compat_refines {k : Nat} {b : BuiltinFun}
    {args₁ args₂ : List CekValue} {π₁ π₂ : Stack}
    (hargs : ListRel (ValueRefinesK k) args₁ args₂)
    (hπ : StackRefK ValueRefinesK k π₁ π₂) :
    ObsRefinesK k
      (match evalBuiltin b args₁ with | some v => State.ret π₁ v | none => .error)
      (match evalBuiltin b args₂ with | some v => State.ret π₂ v | none => .error) := by
  have h_rel := evalBuiltin_rel (b := b) valueRefinesK_vcon_left valueRefinesK_vcon_right
    (fun c => by cases k <;> simp only [ValueRefinesK]) hargs
  revert h_rel
  cases evalBuiltin b args₁ <;> cases evalBuiltin b args₂ <;> intro h_rel
  · exact obsRefinesK_error _
  · exact absurd h_rel id
  · exact absurd h_rel id
  · match k with
    | 0 => exact obsRefinesK_zero_ret
    | m + 1 => exact hπ (m+1) (Nat.le_refl _) _ _ h_rel

--------------------------------------------------------------------------------
-- 9. `Guard.trivial` is `ValueRefinesK`
--------------------------------------------------------------------------------

open Moist.Verified.Contextual.Guarded

private theorem listRel_iff {R S : CekValue → CekValue → Prop} (h : ∀ a b, R a b ↔ S a b) :
    ∀ {l₁ l₂ : List CekValue}, ListRel R l₁ l₂ ↔ ListRel S l₁ l₂
  | [], [] | [], _ :: _ | _ :: _, [] => Iff.rfl
  | _ :: _, _ :: _ => and_congr (h _ _) (listRel_iff h)

theorem valueRel_trivial : ∀ (k : Nat) (v₁ v₂ : CekValue),
    ValueRel Guard.trivial k v₁ v₂ ↔ ValueRefinesK k v₁ v₂ := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro v₁ v₂
  cases k with
  | zero => cases v₁ <;> cases v₂ <;> simp only [ValueRel, ValueRefinesK]
  | succ k =>
    have hl : ∀ l₁ l₂, ListRel (ValueRel Guard.trivial k) l₁ l₂ ↔ ListRel (ValueRefinesK k) l₁ l₂ :=
      fun _ _ => listRel_iff (ih k (Nat.lt_succ_self k))
    cases v₁ <;> cases v₂
    all_goals first | (simp only [ValueRel, ValueRefinesK, hl]; done) | skip
    case VLam.VLam =>
      refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp only [ValueRel, ValueRefinesK] at h ⊢
      · intro j hj a₁ a₂ ha i hi π₁ π₂ hπ
        exact h.2.2 j hj a₁ a₂ ((ih j (by omega) a₁ a₂).mpr ha) trivial trivial i hi π₁ π₂
          trivial trivial fun i' hi' w₁ w₂ hw _ _ => hπ i' hi' w₁ w₂ ((ih i' (by omega) _ _).mp hw)
      · refine ⟨trivial, trivial, fun j hj a₁ a₂ ha _ _ i hi π₁ π₂ _ _ hπ => ?_⟩
        exact h j hj a₁ a₂ ((ih j (by omega) a₁ a₂).mp ha) i hi π₁ π₂
          fun i' hi' w₁ w₂ hw => hπ i' hi' w₁ w₂ ((ih i' (by omega) _ _).mpr hw) trivial trivial
    case VDelay.VDelay =>
      refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp only [ValueRel, ValueRefinesK] at h ⊢
      · intro j hj i hi π₁ π₂ hπ
        exact h j hj i hi π₁ π₂ trivial trivial
          fun i' hi' w₁ w₂ hw _ _ => hπ i' hi' w₁ w₂ ((ih i' (by omega) _ _).mp hw)
      · intro j hj i hi π₁ π₂ _ _ hπ
        exact h j hj i hi π₁ π₂
          fun i' hi' w₁ w₂ hw => hπ i' hi' w₁ w₂ ((ih i' (by omega) _ _).mpr hw) trivial trivial

theorem stackRefK_iff_stackRel {k : Nat} {π₁ π₂ : Stack} :
    StackRefK ValueRefinesK k π₁ π₂ ↔ StackRel Guard.trivial k π₁ π₂ :=
  ⟨fun h => ⟨trivial, trivial, fun j hj v₁ v₂ hv _ _ => h j hj v₁ v₂ ((valueRel_trivial j v₁ v₂).mp hv)⟩,
   fun h j hj v₁ v₂ hv => h.2.2 j hj v₁ v₂ ((valueRel_trivial j v₁ v₂).mpr hv) trivial trivial⟩

theorem openRefines_openRel {d : Nat} {t₁ t₂ : Term} (h : OpenRefines d t₁ t₂) :
    OpenRel Guard.trivial d t₁ t₂ := by
  intro k j hj ρ₁ ρ₂ henv _ _ _ _ i hi π₁ π₂ _ _ hπ
  refine h k j hj ρ₁ ρ₂ (fun n hn hnd => ?_) i hi π₁ π₂ ?_
  · obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := henv n hn hnd
    exact ⟨v₁, v₂, h₁, h₂, (valueRel_trivial j v₁ v₂).mp hv⟩
  · exact stackRefK_iff_stackRel.mpr ⟨trivial, trivial, hπ⟩

theorem applyArgFrames_stackRefK {j : Nat}
    {fields₁ fields₂ : List CekValue} {π₁ π₂ : Stack}
    (hfields : ListRel (ValueRefinesK j) fields₁ fields₂)
    (hπ : StackRefK ValueRefinesK j π₁ π₂) :
    StackRefK ValueRefinesK j (fields₁.map Frame.applyArg ++ π₁)
                               (fields₂.map Frame.applyArg ++ π₂) :=
  stackRefK_iff_stackRel.mpr <| applyArgs_stackRel
    ((listRel_iff (valueRel_trivial j)).mpr hfields) trivial trivial (stackRefK_iff_stackRel.mp hπ)

--------------------------------------------------------------------------------
-- 10. The fundamental property for `TermSubstL`
--------------------------------------------------------------------------------

private theorem termListSubstL_listRel {t₁ t₂ : Term} {R : Term → Term → Prop}
    (h : ∀ {a₁ a₂}, TermSubstL t₁ t₂ a₁ a₂ → R a₁ a₂) :
    ∀ {l₁ l₂ : List Term}, TermListSubstL t₁ t₂ l₁ l₂ → ListRel R l₁ l₂
  | _, _, .nil => trivial
  | _, _, .cons hh ht => ⟨h hh, termListSubstL_listRel h ht⟩

/-- `TermSubstL`-related terms evaluate to related observations, given that
    the substituted terms are open-related. -/
theorem term_obsRefinesG {W : Guard} {d : Nat} {t₁ t₂ : Term}
    (h_open : OpenRel W d t₁ t₂) :
    ∀ (k : Nat) {ρ₁ ρ₂ : CekEnv}, AtLeastEnvRel W k ρ₁ ρ₂ → d ≤ ρ₁.length →
      W.E d ρ₁ → W.E d ρ₂ →
      ∀ {tm₁ tm₂ : Term}, TermSubstL t₁ t₂ tm₁ tm₂ → Eval W k ρ₁ ρ₂ tm₁ tm₂ := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro ρ₁ ρ₂ hρ hd he₁ he₂ tm₁ tm₂ htm
  have hd₂ : d ≤ ρ₂.length := hρ.1 ▸ hd
  have sub : ∀ j < k, ∀ {a₁ a₂}, TermSubstL t₁ t₂ a₁ a₂ → Eval W j ρ₁ ρ₂ a₁ a₂ :=
    fun j hj _ _ h => ih j hj (atLeastEnvRel_mono (by omega) hρ) hd he₁ he₂ h
  cases htm with
  | swap =>
    intro j hj π₁ π₂ hπ _ _
    exact h_open j j (Nat.le_refl _) ρ₁ ρ₂ (atLeastEnvRel_envRel (atLeastEnvRel_mono hj hρ) hd)
      he₁ hd he₂ hd₂ j (Nat.le_refl _) π₁ π₂ hπ.1 hπ.2.1 hπ.2.2
  | varRefl n =>
    refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
    simp only [step] at hst₁ hst₂ ⊢
    rcases atLeastEnvRel_lookup hρ n with ⟨e₁, e₂⟩ | ⟨v₁, v₂, e₁, e₂, hv⟩
    · rw [e₁, e₂]; exact obsRefinesK_error_error j
    · rw [e₁] at hst₁ ⊢; rw [e₂] at hst₂ ⊢
      exact ret_obs (valueRel_mono (by omega) hv) hst₁ hst₂ hπ
  | constRefl c =>
    refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
    exact ret_obs (valueRel_vcon j c.1) hst₁ hst₂ hπ
  | builtinRefl b =>
    refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
    exact ret_obs (valueRel_builtin (k := j) trivial) hst₁ hst₂ hπ
  | errorRefl =>
    exact eval_of_step fun j _ _ _ _ _ _ => obsRefinesK_error_error j
  | lam hb =>
    refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
    refine ret_obs (valueRel_lam (W.ret.mp hst₁).2 (W.ret.mp hst₂).2 ?_) hst₁ hst₂ hπ
    intro j' hj' a₁ a₂ ha ha₁ ha₂
    exact ih j' (by omega) (atLeastEnvRel_extend (atLeastEnvRel_mono (by omega) hρ) ha)
      (by simp [CekEnv.extend, CekEnv.length]; omega)
      (W.extend he₁ hd ha₁) (W.extend he₂ hd₂ ha₂) hb
  | delay hb =>
    refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
    exact ret_obs (valueRel_delay (W.ret.mp hst₁).2 (W.ret.mp hst₂).2
      fun j' hj' => sub j' (by omega) hb) hst₁ hst₂ hπ
  | apply hf ha =>
    refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
    exact sub j hj hf j (Nat.le_refl _) _ _
      (arg_stackRel (sub j hj ha) (W.compute hst₁) (W.compute hst₂) hπ) hst₁ hst₂
  | force he =>
    refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
    exact sub j hj he j (Nat.le_refl _) _ _ (force_stackRel hπ) hst₁ hst₂
  | constr hms =>
    refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
    cases hms with
    | nil => exact ret_obs (valueRel_constr (k := j) trivial) hst₁ hst₂ hπ
    | cons hm hms =>
      exact sub j hj hm j (Nat.le_refl _) _ _
        (constrField_stackRel (termListSubstL_listRel (sub j hj) hms) trivial
          (W.compute hst₁) (W.compute hst₂) hπ) hst₁ hst₂
  | case hs has =>
    refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
    have halts : AltsRel W j ρ₁ ρ₂ _ _ := ⟨termListSubstL_length_eq has, fun n => ?_⟩
    · exact sub j hj hs j (Nat.le_refl _) _ _
        (case_stackRel halts (W.compute hst₁) (W.compute hst₂) hπ) hst₁ hst₂
    · rcases termListSubstL_getElem? has n with h | ⟨a₁, a₂, h₁, h₂, h⟩
      · exact .inl h
      · exact .inr ⟨a₁, a₂, h₁, h₂, sub j hj h⟩

--------------------------------------------------------------------------------
-- 11. Soundness: open refinement implies contextual refinement
--------------------------------------------------------------------------------

open Moist.Verified.Contextual.BisimRef (LocalState LocalEnv LocalStack)

theorem atLeastEnvRel_dummyEnv {W : Guard} (k : Nat) :
    ∀ n, AtLeastEnvRel W k (dummyEnv n) (dummyEnv n)
  | 0 => ⟨rfl, fun m _ hm => by simp [dummyEnv, CekEnv.length] at hm; omega⟩
  | n + 1 => by
    have h := atLeastEnvRel_extend (W := W) (atLeastEnvRel_dummyEnv k n) (valueRel_vcon k .Unit)
    exact h

/-- Per-context form of soundness for any guard whose predicates hold on the
    padded initial states. -/
theorem obsRefines_of_openRel {W : Guard} {d : Nat} {t₁ t₂ : Term}
    (h_open : OpenRel W d t₁ t₂)
    (hinit : ∀ t, closedAt 0 t = true → W.St (.compute [] (dummyEnv d) t))
    (henv : W.E d (dummyEnv d)) (hnil : W.S [])
    (C : Context) (h_c1 : closedAt 0 (fill C t₁) = true)
    (h_c2 : closedAt 0 (fill C t₂) = true) :
    ObsRefines (.compute [] .nil (fill C t₁)) (.compute [] .nil (fill C t₂)) := by
  have hls₁ : LocalState (.compute [] .nil (fill C t₁)) (.compute [] (dummyEnv d) (fill C t₁)) :=
    LocalState.compute LocalEnv.zero h_c1 LocalStack.nil
  have hls₂ : LocalState (.compute [] .nil (fill C t₂)) (.compute [] (dummyEnv d) (fill C t₂)) :=
    LocalState.compute LocalEnv.zero h_c2 LocalStack.nil
  have h_obs : ∀ n, ObsRefinesK n (.compute [] (dummyEnv d) (fill C t₁))
      (.compute [] (dummyEnv d) (fill C t₂)) := fun n =>
    term_obsRefinesG h_open n (atLeastEnvRel_dummyEnv n d) (by rw [dummyEnv_length]; exact Nat.le_refl _)
      henv henv (fill_termSubstL C t₁ t₂) n (Nat.le_refl _) [] [] (stackRel_nil hnil n)
      (hinit _ h_c1) (hinit _ h_c2)
  refine ⟨fun ⟨v, n, hs⟩ => ?_, fun ⟨n, hs⟩ => ?_⟩
  · exact (locality_obsRefinesK n hls₁ hls₂ (h_obs n)).1 v ⟨n, Nat.le_refl _, hs⟩
  · exact (locality_obsRefinesK n hls₁ hls₂ (h_obs n)).2 n (Nat.le_refl _) hs

theorem soundness_of_openRel {W : Guard} {d : Nat} {t₁ t₂ : Term}
    (h_open : OpenRel W d t₁ t₂)
    (hinit : ∀ t, closedAt 0 t = true → W.St (.compute [] (dummyEnv d) t))
    (henv : W.E d (dummyEnv d)) (hnil : W.S [])
    (h_close_pres : ∀ (C : Context),
      closedAt 0 (fill C t₁) = true → closedAt 0 (fill C t₂) = true) :
    CtxRefines t₁ t₂ := fun C h_c1 =>
  ⟨h_close_pres C h_c1,
   obsRefines_of_openRel h_open hinit henv hnil C h_c1 (h_close_pres C h_c1)⟩

/-- Per-context form of `soundness_refines`. -/
theorem obsRefines_of_openRefines {d : Nat} {t₁ t₂ : Term}
    (h_open : OpenRefines d t₁ t₂) (C : Context)
    (h_c1 : closedAt 0 (fill C t₁) = true)
    (h_c2 : closedAt 0 (fill C t₂) = true) :
    ObsRefines (.compute [] .nil (fill C t₁)) (.compute [] .nil (fill C t₂)) :=
  obsRefines_of_openRel (openRefines_openRel h_open) (fun _ _ => trivial) trivial trivial
    C h_c1 h_c2

/-- **Unidirectional soundness**: `OpenRefines d` implies `CtxRefines` for any `d`. -/
theorem soundness_refines {d : Nat} {t₁ t₂ : Term}
    (h_open : OpenRefines d t₁ t₂)
    (h_close_pres : ∀ (C : Context),
      closedAt 0 (fill C t₁) = true → closedAt 0 (fill C t₂) = true) :
    CtxRefines t₁ t₂ :=
  soundness_of_openRel (openRefines_openRel h_open) (fun _ _ => trivial) trivial trivial
    h_close_pres

end Moist.Verified.Contextual.SoundnessRefines
