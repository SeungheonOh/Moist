import Moist.Verified.ShapeFacts.Reflexivity
import Moist.Verified.AdvancedRefinement

variable [sv : Moist.CEK.SemVariant]

/-! # Refinement under environment facts

`FactRefines d F t t'` compares `t` and `t'` in the *same* well-formed
environment and on the *same* well-formed stack, for every environment that
satisfies the predicate `F`. Facts therefore only ever describe the actual
runtime environment, and a binding introduces a fact about the very value its
right-hand side returned (`factRefines_let`).

Closures cross into the step-indexed relation by composing the fundamental
theorem for the source body with the same-environment refinement of the
target body (`factRefines_lam`). With `F` trivially true the relation yields
contextual refinement (`ctxRefines_of_factRefines`).
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.Contextual.Guarded
open Moist.Verified.TermObsRefinesWF
open Moist.Verified.BetaValueRefines

def FactRefines (d : Nat) (F : CekEnv → Prop) (t t' : Term) : Prop :=
  ∀ ρ π, EnvWellFormed d ρ → d ≤ ρ.length → StackWellFormed π → F ρ →
    ObsRefines (.compute π ρ t) (.compute π ρ t')

theorem FactRefines.refl (d : Nat) (F : CekEnv → Prop) (t : Term) : FactRefines d F t t :=
  fun _ _ _ _ _ _ => obsRefines_refl _

theorem FactRefines.trans {d : Nat} {F : CekEnv → Prop} {t₁ t₂ t₃ : Term}
    (h₁ : FactRefines d F t₁ t₂) (h₂ : FactRefines d F t₂ t₃) : FactRefines d F t₁ t₃ :=
  fun ρ π henv hlen hπ hF => obsRefines_trans (h₁ ρ π henv hlen hπ hF) (h₂ ρ π henv hlen hπ hF)

theorem FactRefines.mono {d : Nat} {F G : CekEnv → Prop} {t t' : Term}
    (h : FactRefines d F t t') (hGF : ∀ ρ, G ρ → F ρ) : FactRefines d G t t' :=
  fun ρ π henv hlen hπ hG => h ρ π henv hlen hπ (hGF ρ hG)

theorem FactRefines.of_eq {d : Nat} {F : CekEnv → Prop} {t t' : Term} (h : t = t') :
    FactRefines d F t t' := by
  subst h; exact FactRefines.refl d F t

theorem FactRefines.of_ctxRefines {d : Nat} {F : CekEnv → Prop} {t t' : Term}
    (h : FactRefines d (fun _ => True) t t') : FactRefines d F t t' :=
  h.mono fun _ _ => trivial

/-! ## Contextual refinement -/

theorem ctxRefines_of_factRefines {d : Nat} {t t' : Term}
    (hclosed : closedAt d t = true)
    (hpreserve : ∀ k, closedAt k t = true → closedAt k t' = true)
    (h : FactRefines d (fun _ => True) t t') : CtxRefines t t' :=
  AdvancedRefinement.contextual_of_wf_refinement hclosed hpreserve
    fun ρ π henv hlen hπ => h ρ π henv hlen hπ trivial

/-! ## Values related by the logical relation -/

theorem obsRefines_ret_of_valueRel {π : Stack} {v₁ v₂ : CekValue} (hπ : StackWellFormed π)
    (hv₁ : ValueWellFormed v₁) (hv₂ : ValueWellFormed v₂)
    (h : ∀ k, ValueRel wfGuard k v₁ v₂) : ObsRefines (.ret π v₁) (.ret π v₂) :=
  obsRefines_of_forall_k fun k => (stackRel_refl k hπ).2.2 k (Nat.le_refl _) v₁ v₂ (h k) hv₁ hv₂

/-- A source body evaluated in a related environment, followed by the
    same-environment refinement of the target body. -/
theorem eval_of_factRefines {d j : Nat} {F : CekEnv → Prop} {ρ₁ ρ₂ : CekEnv} {b b' : Term}
    (hclosed : closedAt d b = true) (hb : FactRefines d F b b')
    (henv : EnvRel wfGuard j d ρ₁ ρ₂)
    (hwf₁ : EnvWellFormed d ρ₁) (hlen₁ : d ≤ ρ₁.length)
    (hwf₂ : EnvWellFormed d ρ₂) (hlen₂ : d ≤ ρ₂.length) (hF : F ρ₂) :
    Eval wfGuard j ρ₁ ρ₂ b b' := by
  intro i hi π₁ π₂ hπ hst₁ _
  have source := eval_of_openRefinesWF (FundamentalRefinesWF.ftlr_wf d b hclosed) henv hwf₁ hlen₁ hwf₂ hlen₂
  exact InlineSoundness.SubstRefinesExt.obsRefinesK_compose_obsRefines_right
    (source i hi π₁ π₂ hπ hst₁ (.compute hπ.2.1 hwf₂ hlen₂ hclosed))
    (hb ρ₂ π₂ hwf₂ hlen₂ hπ.2.1 hF)

theorem factRefines_lam {d : Nat} {F G : CekEnv → Prop} {b b' : Term} (n n' : Nat)
    (hclosed : closedAt (d + 1) b = true) (hclosed' : closedAt (d + 1) b' = true)
    (hG : ∀ ρ v, F ρ → G (ρ.extend v)) (hb : FactRefines (d + 1) G b b') :
    FactRefines d F (.Lam n b) (.Lam n' b') := by
  intro ρ π henv hlen hπ hF
  apply obsRefines_of_step
  show ObsRefines (.ret π (.VLam b ρ)) (.ret π (.VLam b' ρ))
  have wf₁ : ValueWellFormed (.VLam b ρ) := .vlam henv hlen hclosed
  have wf₂ : ValueWellFormed (.VLam b' ρ) := .vlam henv hlen hclosed'
  refine obsRefines_ret_of_valueRel hπ wf₁ wf₂ fun k => ?_
  apply valueRel_lam (W := wfGuard) wf₁ wf₂
  intro j _ a₁ a₂ ha ha₁ ha₂
  exact eval_of_factRefines hclosed hb (envRel_extend_of henv ha (valueRel_refl j))
    (envWellFormed_extend d henv hlen ha₁) (by simp [CekEnv.extend, CekEnv.length]; omega)
    (envWellFormed_extend d henv hlen ha₂) (by simp [CekEnv.extend, CekEnv.length]; omega)
    (hG ρ a₂ hF)

theorem factRefines_delay {d : Nat} {F : CekEnv → Prop} {b b' : Term}
    (hclosed : closedAt d b = true) (hclosed' : closedAt d b' = true)
    (hb : FactRefines d F b b') :
    FactRefines d F (.Delay b) (.Delay b') := by
  intro ρ π henv hlen hπ hF
  apply obsRefines_of_step
  show ObsRefines (.ret π (.VDelay b ρ)) (.ret π (.VDelay b' ρ))
  have wf₁ : ValueWellFormed (.VDelay b ρ) := .vdelay henv hlen hclosed
  have wf₂ : ValueWellFormed (.VDelay b' ρ) := .vdelay henv hlen hclosed'
  refine obsRefines_ret_of_valueRel hπ wf₁ wf₂ fun k => ?_
  apply valueRel_delay (W := wfGuard) wf₁ wf₂
  intro j _
  exact eval_of_factRefines hclosed hb (envRel_refl henv) henv hlen henv hlen hF

/-! ## Strict frames -/

theorem factRefines_force {d : Nat} {F : CekEnv → Prop} {t t' : Term}
    (h : FactRefines d F t t') : FactRefines d F (.Force t) (.Force t') := by
  intro ρ π henv hlen hπ hF
  exact obsRefines_of_step (h ρ (.force :: π) henv hlen (.cons .force hπ) hF)

theorem factRefines_apply {d : Nat} {F : CekEnv → Prop} {f f' a a' : Term}
    (hf : FactRefines d F f f') (ha : FactRefines d F a a')
    (closedF' : closedAt d f' = true) (closedA : closedAt d a = true) :
    FactRefines d F (.Apply f a) (.Apply f' a') := by
  intro ρ π henv hlen hπ hF
  apply obsRefines_of_step
  show ObsRefines (.compute (.arg a ρ :: π) ρ f) (.compute (.arg a' ρ :: π) ρ f')
  refine obsRefines_trans (hf ρ _ henv hlen (.cons (.arg henv hlen closedA) hπ) hF) ?_
  apply obsRefines_of_continuation
  intro v hv
  apply obsRefines_of_step
  show ObsRefines (.compute (.funV v :: π) ρ a) (.compute (.funV v :: π) ρ a')
  exact ha ρ _ henv hlen (.cons (.funV (halts_wellFormed henv hlen closedF' hv)) hπ) hF

/-- A binding whose body uses facts about the value the right-hand side
    actually returned. -/
theorem factRefines_let {d : Nat} {F G : CekEnv → Prop} {r b b' : Term} (n n' : Nat)
    (closedR : closedAt d r = true)
    (hG : ∀ ρ v, F ρ → Halts ρ r v → G (ρ.extend v)) (hb : FactRefines (d + 1) G b b') :
    FactRefines d F (.Apply (.Lam n b) r) (.Apply (.Lam n' b') r) := by
  intro ρ π henv hlen hπ hF
  apply obsRefines_of_steps 3 3
  show ObsRefines (.compute (.funV (.VLam b ρ) :: π) ρ r) (.compute (.funV (.VLam b' ρ) :: π) ρ r)
  apply obsRefines_of_continuation
  intro v hv
  apply obsRefines_of_step
  show ObsRefines (.compute π (ρ.extend v) b) (.compute π (ρ.extend v) b')
  have hvwf := halts_wellFormed henv hlen closedR hv
  exact hb (ρ.extend v) π (envWellFormed_extend d henv hlen hvwf)
    (by simp [CekEnv.extend, CekEnv.length]; omega) hπ (hG ρ v hF hv)

theorem factRefines_constrField {d : Nat} {F : CekEnv → Prop} {tag : Nat} {ρ : CekEnv} {π : Stack}
    (henv : EnvWellFormed d ρ) (hlen : d ≤ ρ.length) (hπ : StackWellFormed π) (hF : F ρ) :
    ∀ {ms ms' : List Term} {done : List CekValue},
      ListRel (FactRefines d F) ms ms' → closedAtList d ms = true → closedAtList d ms' = true →
      ValueListWellFormed done → ∀ v, ValueWellFormed v →
      ObsRefines (.ret (.constrField tag done ms ρ :: π) v) (.ret (.constrField tag done ms' ρ :: π) v)
  | [], [], _, _, _, _, _, _, _ => obsRefines_refl _
  | [], _ :: _, _, h, _, _, _, _, _ => absurd h id
  | _ :: _, [], _, h, _, _, _, _, _ => absurd h id
  | m :: ms, m' :: ms', done, h, closed, closed', hdone, v, hv => by
    simp only [closedAtList, Bool.and_eq_true] at closed closed'
    apply obsRefines_of_step
    show ObsRefines (.compute (.constrField tag (v :: done) ms ρ :: π) ρ m)
      (.compute (.constrField tag (v :: done) ms' ρ :: π) ρ m')
    refine obsRefines_trans (h.1 ρ _ henv hlen
      (.cons (.constrField tag (.cons hv hdone) henv hlen closed.2) hπ) hF) ?_
    apply obsRefines_of_continuation
    intro w hw
    exact factRefines_constrField henv hlen hπ hF h.2 closed.2 closed'.2 (.cons hv hdone) w
      (halts_wellFormed henv hlen closed'.1 hw)

theorem factRefines_constr {d : Nat} {F : CekEnv → Prop} {tag : Nat} {ms ms' : List Term}
    (h : ListRel (FactRefines d F) ms ms') (closed : closedAtList d ms = true)
    (closed' : closedAtList d ms' = true) :
    FactRefines d F (.Constr tag ms) (.Constr tag ms') := by
  intro ρ π henv hlen hπ hF
  match ms, ms', h with
  | [], [], _ => exact obsRefines_refl _
  | [], _ :: _, h => exact absurd h id
  | _ :: _, [], h => exact absurd h id
  | m :: ms, m' :: ms', h =>
    simp only [closedAtList, Bool.and_eq_true] at closed closed'
    apply obsRefines_of_step
    show ObsRefines (.compute (.constrField tag [] ms ρ :: π) ρ m)
      (.compute (.constrField tag [] ms' ρ :: π) ρ m')
    refine obsRefines_trans (h.1 ρ _ henv hlen (.cons (.constrField tag .nil henv hlen closed.2) hπ) hF) ?_
    apply obsRefines_of_continuation
    intro w hw
    exact factRefines_constrField henv hlen hπ hF h.2 closed.2 closed'.2 .nil w
      (halts_wellFormed henv hlen closed'.1 hw)

omit sv in
theorem listRel_length {α : Type} {R : α → α → Prop} :
    ∀ {xs ys : List α}, ListRel R xs ys → xs.length = ys.length
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h id
  | _ :: _, [], h => absurd h id
  | _ :: _, _ :: _, h => by simp [listRel_length h.2]

omit sv in
theorem listRel_getElem? {α : Type} {R : α → α → Prop} :
    ∀ {xs ys : List α}, ListRel R xs ys → ∀ n : Nat,
      (xs[n]? = none ∧ ys[n]? = none) ∨ ∃ x y, xs[n]? = some x ∧ ys[n]? = some y ∧ R x y
  | [], [], _, _ => .inl ⟨rfl, rfl⟩
  | [], _ :: _, h, _ => absurd h id
  | _ :: _, [], h, _ => absurd h id
  | x :: _, y :: _, h, 0 => .inr ⟨x, y, rfl, rfl, h.1⟩
  | _ :: _, _ :: _, h, n + 1 => by simpa using listRel_getElem? h.2 n

omit sv in
theorem valueListWellFormed_map_vcon :
    ∀ {fields : List CekValue}, (∀ v ∈ fields, ∃ c, v = .VCon c) → ValueListWellFormed fields
  | [], _ => .nil
  | _ :: _, h => by
    obtain ⟨c, rfl⟩ := h _ (.head _)
    exact .cons (.vcon c) (valueListWellFormed_map_vcon fun w hw => h w (.tail _ hw))

omit sv in
theorem stackWellFormed_applyArgs :
    ∀ {fields : List CekValue} {π : Stack}, ValueListWellFormed fields → StackWellFormed π →
      StackWellFormed (fields.map Frame.applyArg ++ π)
  | [], _, _, hπ => hπ
  | _ :: _, _, .cons hv hvs, hπ => .cons (.applyArg hv) (stackWellFormed_applyArgs hvs hπ)

/-- The scrutinee frame with alternatives related under the same facts. -/
theorem factRefines_caseFrame {d : Nat} {F : CekEnv → Prop} {alts alts' : List Term}
    {ρ : CekEnv} {π : Stack}
    (henv : EnvWellFormed d ρ) (hlen : d ≤ ρ.length) (hπ : StackWellFormed π) (hF : F ρ)
    (h : ListRel (FactRefines d F) alts alts') (v : CekValue) (hv : ValueWellFormed v) :
    ObsRefines (.ret (.caseScrutinee alts ρ :: π) v) (.ret (.caseScrutinee alts' ρ :: π) v) := by
  have hlength := listRel_length h
  have dispatch : ∀ (tag : Nat) (fields : List CekValue), ValueListWellFormed fields →
      ObsRefines
        (match alts[tag]? with
          | some alt => State.compute (fields.map Frame.applyArg ++ π) ρ alt | none => .error)
        (match alts'[tag]? with
          | some alt => State.compute (fields.map Frame.applyArg ++ π) ρ alt | none => .error) := by
    intro tag fields hfields
    rcases listRel_getElem? h tag with ⟨e₁, e₂⟩ | ⟨a, a', e₁, e₂, ha⟩
    · rw [e₁, e₂]; exact obsRefines_refl _
    · rw [e₁, e₂]
      exact ha ρ _ henv hlen (stackWellFormed_applyArgs hfields hπ) hF
  apply obsRefines_of_step
  cases v with
  | VConstr tag fields =>
    cases hv with
    | vconstr _ hfields => exact dispatch tag fields hfields
  | VCon c =>
    simp only [step]
    cases hc : constToTagAndFields c with
    | none => exact obsRefines_refl _
    | some r =>
      obtain ⟨tag, numCtors, fields⟩ := r
      simp only [hlength]
      split
      · exact obsRefines_refl _
      · have hvcon := constToTagAndFields_fields_vcon c
        rw [hc] at hvcon
        exact dispatch tag fields (valueListWellFormed_map_vcon hvcon)
  | VLam _ _ | VDelay _ _ | VBuiltin _ _ _ => exact obsRefines_refl _

theorem factRefines_case {d : Nat} {F : CekEnv → Prop} {s s' : Term} {alts alts' : List Term}
    (hs : FactRefines d F s s') (halts : ListRel (FactRefines d F) alts alts')
    (closedS' : closedAt d s' = true) (closedAlts : closedAtList d alts = true) :
    FactRefines d F (.Case s alts) (.Case s' alts') := by
  intro ρ π henv hlen hπ hF
  apply obsRefines_of_step
  show ObsRefines (.compute (.caseScrutinee alts ρ :: π) ρ s)
    (.compute (.caseScrutinee alts' ρ :: π) ρ s')
  refine obsRefines_trans (hs ρ _ henv hlen (.cons (.caseScrutinee henv hlen closedAlts) hπ) hF) ?_
  apply obsRefines_of_continuation
  intro v hv
  exact factRefines_caseFrame henv hlen hπ hF halts v (halts_wellFormed henv hlen closedS' hv)

/-! ## Shifting under an unused binder -/

omit sv in
theorem shiftBisimEnv_shift {d : Nat} {ρ : CekEnv} (w : CekValue) :
    EnvWellFormed d ρ → ShiftBisimEnv (shiftRename 1) d ρ (ρ.extend w)
  | .zero => .zero
  | .succ (k := k) (v := v) hrest _ hl hv => by
    refine .succ (v₁ := v) (v₂ := v) (shiftBisimEnv_shift w hrest) hl ?_ (shiftBisimValue_refl_id v hv)
    rw [shiftRename_ge (by omega)]
    exact hl

omit sv in
private theorem shiftBisimFrame_refl {f : Frame} (h : FrameWellFormed f) : ShiftBisimFrame f f := by
  cases h with
  | force => exact .force
  | arg henv _ hc =>
    simpa only [renameTerm_id] using
      ShiftBisimFrame.arg FundamentalRefines.is0preserving_id (shiftBisimEnv_refl_id_aux henv) hc
  | funV hv => exact .funV (shiftBisimValue_refl_id _ hv)
  | applyArg hv => exact .applyArg (shiftBisimValue_refl_id _ hv)
  | constrField tag hdone henv _ hc =>
    simpa only [renameTermList_id] using
      ShiftBisimFrame.constrField tag FundamentalRefines.is0preserving_id
        (shiftBisimValueList_refl_id_aux hdone) (shiftBisimEnv_refl_id_aux henv) hc
  | caseScrutinee henv _ hc =>
    simpa only [renameTermList_id] using
      ShiftBisimFrame.caseScrutinee FundamentalRefines.is0preserving_id
        (shiftBisimEnv_refl_id_aux henv) hc

omit sv in
theorem shiftBisimStack_refl : ∀ {π : Stack}, StackWellFormed π → ShiftBisimStack π π
  | [], _ => .nil
  | _ :: _, .cons hf hπ => .cons (shiftBisimFrame_refl hf) (shiftBisimStack_refl hπ)

theorem obsRefines_of_shiftBisim {s₁ s₂ : State} (h : ShiftBisimState s₁ s₂) :
    ObsRefines s₁ s₂ ∧ ObsRefines s₂ s₁ := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨v, n, hn⟩
    have after := shiftBisimState_steps_preserves n h
    rw [hn] at after
    generalize hs : steps n s₂ = r at after
    cases after with
    | halt _ => exact ⟨_, n, hs⟩
  · rintro ⟨n, hn⟩
    have after := shiftBisimState_steps_preserves n h
    rw [hn] at after
    generalize hs : steps n s₂ = r at after
    cases after
    exact ⟨n, hs⟩
  · rintro ⟨v, n, hn⟩
    have after := shiftBisimState_steps_preserves n h
    rw [hn] at after
    generalize hs : steps n s₁ = r at after
    cases after with
    | halt _ => exact ⟨_, n, hs⟩
  · rintro ⟨n, hn⟩
    have after := shiftBisimState_steps_preserves n h
    rw [hn] at after
    generalize hs : steps n s₁ = r at after
    cases after
    exact ⟨n, hs⟩

/-- A term evaluates alike after a binding it does not mention. -/
theorem obsEq_shift {d : Nat} {ρ : CekEnv} {π : Stack} {t : Term} (w : CekValue)
    (henv : EnvWellFormed d ρ) (hπ : StackWellFormed π) (hclosed : closedAt d t = true) :
    ObsRefines (.compute π ρ t) (.compute π (ρ.extend w) (renameTerm (shiftRename 1) t)) ∧
    ObsRefines (.compute π (ρ.extend w) (renameTerm (shiftRename 1) t)) (.compute π ρ t) :=
  obsRefines_of_shiftBisim (.compute (FundamentalRefines.is0preserving_shiftRename (by omega))
    (shiftBisimEnv_shift w henv) hclosed (shiftBisimStack_refl hπ))

/-- Dropping a binding that returns on every path and that the body ignores. -/
theorem factRefines_dead_let {d : Nat} {F : CekEnv → Prop} {r b : Term} (n : Nat)
    (closedB : closedAt d b = true)
    (total : ∀ ρ, F ρ → EnvWellFormed d ρ → d ≤ ρ.length → ∃ v, Halts ρ r v) :
    FactRefines d F (.Apply (.Lam n (renameTerm (shiftRename 1) b)) r) b := by
  intro ρ π henv hlen hπ hF
  obtain ⟨v, hv⟩ := total ρ hF henv hlen
  apply obsRefines_of_reaches (s₁' := .compute π (ρ.extend v) (renameTerm (shiftRename 1) b))
    (s₂' := .compute π ρ b)
  · refine reaches_trans (reaches_of_steps 3 rfl) ?_
    exact reaches_trans (halts_on_stack hv _) (reaches_of_steps 1 rfl)
  · exact reaches_refl _
  · exact (obsEq_shift v henv hπ closedB).2

/-- Evaluating a total right-hand side before a body that ignores it. -/
theorem factRefines_add_let {d : Nat} {F : CekEnv → Prop} {r b : Term} (n : Nat)
    (closedB : closedAt d b = true)
    (total : ∀ ρ, F ρ → EnvWellFormed d ρ → d ≤ ρ.length → ∃ v, Halts ρ r v) :
    FactRefines d F b (.Apply (.Lam n (renameTerm (shiftRename 1) b)) r) := by
  intro ρ π henv hlen hπ hF
  obtain ⟨v, hv⟩ := total ρ hF henv hlen
  apply obsRefines_of_reaches (s₁' := .compute π ρ b)
    (s₂' := .compute π (ρ.extend v) (renameTerm (shiftRename 1) b))
  · exact reaches_refl _
  · refine reaches_trans (reaches_of_steps 3 rfl) ?_
    exact reaches_trans (halts_on_stack hv _) (reaches_of_steps 1 rfl)
  · exact (obsEq_shift v henv hπ closedB).1

end Moist.Verified.ShapeFacts
