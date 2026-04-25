import Moist.Verified.TermObsRefinesWF
import Moist.Verified.FundamentalRefines

/-! # WF-enriched fundamental theorem of the logical relation (self-refinement)

`ftlr_wf` proves that every closed term `t` self-refines under the WF-enriched
value relation (`ValueRefinesKWF`). This is the WF analogue of the reflexive
FTLR (`ftlr` in `FundamentalRefines.lean`), specialized to `r = id`.

The key difference from the non-WF version: stack functions receive
`StackWellFormed` and `ValueWellFormed` witnesses, the value relation is
`ValueRefinesKWF`, and the environment relation is `EnvRefinesKWF`.
-/

namespace Moist.Verified.FundamentalRefinesWF

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified
open Moist.Verified.Equivalence
open Moist.Verified.Contextual.SoundnessRefines
open Moist.Verified.TermObsRefinesWF
open Moist.Verified.BetaValueRefines
open Moist.Verified.StepWellFormed (evalBuiltin_preserves_wf)

/-! ## 1. Environment helpers -/

private theorem envRefinesKWF_mono {j k d : Nat} (hjk : j ≤ k)
    {ρ₁ ρ₂ : CekEnv} (h : EnvRefinesKWF k d ρ₁ ρ₂) :
    EnvRefinesKWF j d ρ₁ ρ₂ := by
  intro n hn hnd
  obtain ⟨v₁, v₂, hl, hr, hrel⟩ := h n hn hnd
  exact ⟨v₁, v₂, hl, hr, valueRefinesKWF_mono hjk _ _ hrel⟩

private theorem envRefinesKWF_extend {k d : Nat} {ρ₁ ρ₂ : CekEnv}
    {v₁ v₂ : CekValue}
    (henv : EnvRefinesKWF k d ρ₁ ρ₂) (hv : ValueRefinesKWF k v₁ v₂) :
    EnvRefinesKWF k (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) := by
  intro n hn hnd
  by_cases hn1 : n = 1
  · subst hn1
    refine ⟨v₁, v₂, ?_, ?_, hv⟩
    · exact Moist.Verified.BetaValueRefines.extend_lookup_one ρ₁ v₁
    · exact Moist.Verified.BetaValueRefines.extend_lookup_one ρ₂ v₂
  · have hn2 : n ≥ 2 := by omega
    match n, hn2 with
    | m + 2, _ =>
      have hm1 : m + 1 ≥ 1 := by omega
      have hmd : m + 1 ≤ d := by omega
      obtain ⟨w₁, w₂, hl, hr, hrel⟩ := henv (m + 1) hm1 hmd
      refine ⟨w₁, w₂, ?_, ?_, hrel⟩
      · show (ρ₁.extend v₁).lookup (m + 1 + 1) = some w₁
        rw [Moist.Verified.BetaValueRefines.extend_lookup_succ ρ₁ v₁ (m + 1) hm1]
        exact hl
      · show (ρ₂.extend v₂).lookup (m + 1 + 1) = some w₂
        rw [Moist.Verified.BetaValueRefines.extend_lookup_succ ρ₂ v₂ (m + 1) hm1]
        exact hr

/-! ## 2. Value list well-formedness helpers -/

private theorem ValueListWellFormed_append
    (vs₁ vs₂ : List CekValue)
    (h₁ : ValueListWellFormed vs₁) (h₂ : ValueListWellFormed vs₂) :
    ValueListWellFormed (vs₁ ++ vs₂) := by
  induction vs₁ with
  | nil => exact h₂
  | cons v rest ih =>
    cases h₁ with
    | cons hv hrest => exact .cons hv (ih hrest)

private theorem ValueListWellFormed_reverse
    (vs : List CekValue) (h : ValueListWellFormed vs) :
    ValueListWellFormed vs.reverse := by
  induction vs with
  | nil => exact .nil
  | cons v rest ih =>
    cases h with
    | cons hv hrest =>
      rw [List.reverse_cons]
      exact ValueListWellFormed_append rest.reverse [v] (ih hrest) (.cons hv .nil)

/-! ## 3. constToTagAndFields well-formedness -/

private theorem constToTagAndFields_fields_wf (c : Const) :
    match constToTagAndFields c with
    | some (_, _, fields) => ValueListWellFormed fields
    | none => True := by
  have h := constToTagAndFields_fields_vcon c
  cases hc : constToTagAndFields c with
  | none => trivial
  | some val =>
    obtain ⟨tag, numCtors, fields⟩ := val; simp [hc] at h
    exact go fields h
where
  go : (fields : List CekValue) → (∀ v ∈ fields, ∃ c, v = .VCon c) → ValueListWellFormed fields
    | [], _ => .nil
    | v :: rest, h =>
      have ⟨cv, hcv⟩ := h v (.head rest)
      hcv ▸ .cons (.vcon cv) (go rest (fun x hx => h x (.tail v hx)))

private theorem listRel_refl_vcon_refinesWF_local (j : Nat) (l : List CekValue)
    (h : ∀ v ∈ l, ∃ c, v = .VCon c) : ListRel (ValueRefinesKWF j) l l := by
  induction l with
  | nil => trivial
  | cons v vs ih =>
    obtain ⟨c, rfl⟩ := h _ (.head _)
    refine ⟨?_, ih (fun w hw => h w (.tail _ hw))⟩
    cases j with | zero => simp only [ValueRefinesKWF] | succ => simp [ValueRefinesKWF]

/-! ## 4. Stack well-formedness and applyArgFrames -/

private theorem stackWellFormed_applyArgFrames {fields : List CekValue} {π : Stack}
    (hfs : ValueListWellFormed fields) (hπ : StackWellFormed π) :
    StackWellFormed (fields.map Frame.applyArg ++ π) := by
  induction fields with
  | nil => exact hπ
  | cons v rest ih =>
    cases hfs with
    | cons hv hrest =>
      exact StackWellFormed.cons (FrameWellFormed.applyArg hv) (ih hrest)

private theorem applyArgFrames_stackFnKWF {j : Nat}
    {fields₁ fields₂ : List CekValue} {π₁ π₂ : Stack}
    (hfields : ListRel (ValueRefinesKWF j) fields₁ fields₂)
    (hwf₁ : ValueListWellFormed fields₁)
    (hwf₂ : ValueListWellFormed fields₂)
    (hwf_π₁ : StackWellFormed π₁) (hwf_π₂ : StackWellFormed π₂)
    (hπ : StackFnKWF j π₁ π₂) :
    StackFnKWF j (fields₁.map Frame.applyArg ++ π₁)
                  (fields₂.map Frame.applyArg ++ π₂) :=
  (Moist.Verified.TermObsRefinesWF.applyArgFrames_stackRefKWF hfields ⟨hwf_π₁, hwf_π₂, hπ⟩ hwf₁ hwf₂).2.2

/-! ## 5. ListRel getElem helper -/

private theorem listRel_getElem_self {R : α → α → Prop}
    {l : List α} (h : ListRel (fun a b => R a b) l l)
    {i : Nat} (hi : i < l.length) :
    R l[i] l[i] := by
  induction l generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons x xs ih =>
    match i with
    | 0 => exact h.1
    | n + 1 => exact ih h.2 (by simp [List.length] at hi ⊢; omega)

/-! ## 6. Constr field frame builder (WF version) -/

private theorem constrFieldWF {d tag k : Nat}
    {ms : List Term} {ρ₁ ρ₂ : CekEnv}
    (hfields : ListRel (fun t₁ t₂ =>
      ∀ j ≤ k, ∀ ρ₁ ρ₂, EnvRefinesKWF j d ρ₁ ρ₂ →
        EnvWellFormed d ρ₁ → d ≤ ρ₁.length →
        EnvWellFormed d ρ₂ → d ≤ ρ₂.length →
        ∀ i ≤ j, ∀ π₁ π₂,
          StackWellFormed π₁ → StackWellFormed π₂ → StackFnKWF i π₁ π₂ →
          ObsRefinesK i (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂)) ms ms) :
    ∀ {j}, j ≤ k → ∀ {done₁ done₂ π₁ π₂},
      EnvRefinesKWF j d ρ₁ ρ₂ →
      EnvWellFormed d ρ₁ → d ≤ ρ₁.length →
      EnvWellFormed d ρ₂ → d ≤ ρ₂.length →
      ListRel (ValueRefinesKWF j) done₁ done₂ →
      ValueListWellFormed done₁ → ValueListWellFormed done₂ →
      closedAtList d ms = true →
      StackWellFormed π₁ → StackWellFormed π₂ → StackFnKWF j π₁ π₂ →
      StackFnKWF j (.constrField tag done₁ ms ρ₁ :: π₁)
                     (.constrField tag done₂ ms ρ₂ :: π₂) := by
  induction ms with
  | nil =>
    intro j hj done₁ done₂ π₁ π₂ henv henv_wf_l hlen_l henv_wf_r hlen_r
      hdone hdone_wf_l hdone_wf_r _hclosed hwf_π₁ hwf_π₂ hπ
    intro j' hj' v₁ v₂ hv hv_wf₁ hv_wf₂
    match j' with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | n + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    have hrev : ListRel (ValueRefinesKWF n) ((v₁ :: done₁).reverse) ((v₂ :: done₂).reverse) := by
      simp only [List.reverse_cons]
      exact listRel_append
        (listRel_reverse
          (listRel_mono (fun a b h => valueRefinesKWF_mono (by omega) a b h) hdone))
        ⟨valueRefinesKWF_mono (by omega) v₁ v₂ hv, trivial⟩
    have hval : ValueRefinesKWF (n + 1)
        (.VConstr tag ((v₁ :: done₁).reverse))
        (.VConstr tag ((v₂ :: done₂).reverse)) := by
      cases n with
      | zero => simp only [ValueRefinesKWF]; exact ⟨trivial, hrev⟩
      | succ m => simp only [ValueRefinesKWF]; exact ⟨trivial, hrev⟩
    have hval_wf₁ : ValueWellFormed (.VConstr tag ((v₁ :: done₁).reverse)) :=
      .vconstr _ (ValueListWellFormed_reverse _ (.cons hv_wf₁ hdone_wf_l))
    have hval_wf₂ : ValueWellFormed (.VConstr tag ((v₂ :: done₂).reverse)) :=
      .vconstr _ (ValueListWellFormed_reverse _ (.cons hv_wf₂ hdone_wf_r))
    exact obsRefinesK_mono (by omega) (hπ (n + 1) (by omega) _ _ hval hval_wf₁ hval_wf₂)
  | cons m₁ ms' ih =>
    intro j hj done₁ done₂ π₁ π₂ henv henv_wf_l hlen_l henv_wf_r hlen_r
      hdone hdone_wf_l hdone_wf_r hclosed hwf_π₁ hwf_π₂ hπ
    have hm := hfields.1
    have hfs := hfields.2
    simp only [closedAtList, Bool.and_eq_true] at hclosed
    intro j' hj' v₁ v₂ hv hv_wf₁ hv_wf₂
    match j' with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | n + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    have hdone' : ListRel (ValueRefinesKWF n) (v₁ :: done₁) (v₂ :: done₂) :=
      ⟨valueRefinesKWF_mono (by omega) v₁ v₂ hv,
       listRel_mono (fun a b h => valueRefinesKWF_mono (by omega) a b h) hdone⟩
    have hdone_wf₁' : ValueListWellFormed (v₁ :: done₁) := .cons hv_wf₁ hdone_wf_l
    have hdone_wf₂' : ValueListWellFormed (v₂ :: done₂) := .cons hv_wf₂ hdone_wf_r
    have hwf_s₁' : StackWellFormed (.constrField tag (v₁ :: done₁) ms' ρ₁ :: π₁) :=
      .cons (.constrField tag hdone_wf₁' henv_wf_l hlen_l hclosed.2) hwf_π₁
    have hwf_s₂' : StackWellFormed (.constrField tag (v₂ :: done₂) ms' ρ₂ :: π₂) :=
      .cons (.constrField tag hdone_wf₂' henv_wf_r hlen_r hclosed.2) hwf_π₂
    apply hm (n + 1) (by omega) ρ₁ ρ₂ (envRefinesKWF_mono (by omega) henv) henv_wf_l hlen_l henv_wf_r hlen_r n (by omega)
      (.constrField tag (v₁ :: done₁) ms' ρ₁ :: π₁) (.constrField tag (v₂ :: done₂) ms' ρ₂ :: π₂)
      hwf_s₁' hwf_s₂'
    exact ih hfs (by omega : n ≤ k) (envRefinesKWF_mono (by omega) henv)
      henv_wf_l hlen_l henv_wf_r hlen_r
      hdone' hdone_wf₁' hdone_wf₂' hclosed.2
      hwf_π₁ hwf_π₂ (fun j₀ hj₀ w₁ w₂ hw hw₁ hw₂ => hπ j₀ (by omega) w₁ w₂ hw hw₁ hw₂)

/-! ## 7. Main theorem -/

set_option maxHeartbeats 1600000 in
mutual

def ftlr_wf (d : Nat) (t : Term) (ht : closedAt d t = true) :
    OpenRefinesWF d t t := by
  intro k j hj ρ₁ ρ₂ henv henv_wf_l hlen_l henv_wf_r hlen_r
  intro i hi π₁ π₂ hwf_π₁ hwf_π₂ hπ
  match t with
  | .Var n =>
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    simp [closedAt] at ht
    by_cases hn : n = 0
    · subst hn
      have h1 : ρ₁.lookup 0 = none := Moist.Verified.BetaValueRefines.lookup_zero ρ₁
      have h2 : ρ₂.lookup 0 = none := Moist.Verified.BetaValueRefines.lookup_zero ρ₂
      rw [h1, h2]
      exact obsRefinesK_error _
    · obtain ⟨v₁, v₂, hl, hr, hrel⟩ := henv n (by omega) ht
      rw [hl, hr]
      have hvwf₁ : ValueWellFormed v₁ := by
        obtain ⟨v, hv_look, hv_wf⟩ := envWellFormed_lookup d henv_wf_l (by omega : 0 < n) ht
        rw [hv_look] at hl; cases hl; exact hv_wf
      have hvwf₂ : ValueWellFormed v₂ := by
        obtain ⟨v, hv_look, hv_wf⟩ := envWellFormed_lookup d henv_wf_r (by omega : 0 < n) ht
        rw [hv_look] at hr; cases hr; exact hv_wf
      exact hπ i' (by omega) _ _
        (valueRefinesKWF_mono (by omega : i' ≤ j) _ _ hrel) hvwf₁ hvwf₂
  | .Constant c' =>
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    exact hπ i' (by omega) _ _
      (by cases i' with
        | zero => simp only [ValueRefinesKWF]
        | succ => simp only [ValueRefinesKWF])
      (.vcon _) (.vcon _)
  | .Builtin b =>
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    exact hπ i' (by omega) _ _
      (by cases i' with
        | zero => simp only [ValueRefinesKWF]; exact ⟨trivial, trivial⟩
        | succ => simp only [ValueRefinesKWF, ListRel]; exact ⟨trivial, trivial, trivial⟩)
      (.vbuiltin _ _ .nil) (.vbuiltin _ _ .nil)
  | .Error =>
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp [step]; exact obsRefinesK_error _
  | .Lam name body =>
    simp [closedAt] at ht
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    have hvlam_wf₁ : ValueWellFormed (.VLam body ρ₁) := .vlam henv_wf_l hlen_l ht
    have hvlam_wf₂ : ValueWellFormed (.VLam body ρ₂) := .vlam henv_wf_r hlen_r ht
    exact hπ i' (by omega) _ _
      (by cases i' with
        | zero => simp only [ValueRefinesKWF]
        | succ m =>
          simp only [ValueRefinesKWF]
          refine ⟨hvlam_wf₁, hvlam_wf₂, ?_⟩
          intro j' hj' arg₁ arg₂ hargs hargs_wf₁ hargs_wf₂ ib hib π₁' π₂' hwf₁' hwf₂' hπ'
          exact ftlr_wf (d + 1) body ht j' j' (Nat.le_refl _)
            (ρ₁.extend arg₁) (ρ₂.extend arg₂)
            (envRefinesKWF_extend (envRefinesKWF_mono (by omega) henv) hargs)
            (envWellFormed_extend d henv_wf_l hlen_l hargs_wf₁)
            (by simp [CekEnv.extend, CekEnv.length]; omega)
            (envWellFormed_extend d henv_wf_r hlen_r hargs_wf₂)
            (by simp [CekEnv.extend, CekEnv.length]; omega)
            ib hib π₁' π₂' hwf₁' hwf₂' hπ')
      hvlam_wf₁ hvlam_wf₂
  | .Delay body =>
    simp [closedAt] at ht
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    have hvdelay_wf₁ : ValueWellFormed (.VDelay body ρ₁) := .vdelay henv_wf_l hlen_l ht
    have hvdelay_wf₂ : ValueWellFormed (.VDelay body ρ₂) := .vdelay henv_wf_r hlen_r ht
    exact hπ i' (by omega) _ _
      (by cases i' with
        | zero => simp only [ValueRefinesKWF]
        | succ m =>
          simp only [ValueRefinesKWF]
          intro j' hj' ib hib π₁' π₂' hwf₁' hwf₂' hπ'
          exact ftlr_wf d body ht j'
            j' (Nat.le_refl _) ρ₁ ρ₂ (envRefinesKWF_mono (by omega) henv)
            henv_wf_l hlen_l henv_wf_r hlen_r
            ib hib π₁' π₂' hwf₁' hwf₂' hπ')
      hvdelay_wf₁ hvdelay_wf₂
  | .Apply f x =>
    simp [closedAt] at ht; obtain ⟨hf, hx⟩ := ht
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    apply ftlr_wf d f hf k (i'+1) (by omega) ρ₁ ρ₂ (envRefinesKWF_mono (by omega) henv)
      henv_wf_l hlen_l henv_wf_r hlen_r i' (by omega)
      (Frame.arg x ρ₁ :: π₁) (Frame.arg x ρ₂ :: π₂)
      (.cons (.arg henv_wf_l hlen_l hx) hwf_π₁) (.cons (.arg henv_wf_r hlen_r hx) hwf_π₂)
    intro i₁ hi₁ v₁ v₂ hv hvwf₁ hvwf₂
    match i₁ with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | m₁ + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    apply ftlr_wf d x hx k (m₁+1) (by omega) ρ₁ ρ₂ (envRefinesKWF_mono (by omega) henv)
      henv_wf_l hlen_l henv_wf_r hlen_r m₁ (by omega)
      (Frame.funV v₁ :: π₁) (Frame.funV v₂ :: π₂)
      (.cons (.funV hvwf₁) hwf_π₁) (.cons (.funV hvwf₂) hwf_π₂)
    intro i₂ hi₂ w₁ w₂ hw hwwf₁ hwwf₂
    match i₂ with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | m₂ + 1 =>
    obsRefinesK_of_step_auto
    match v₁, v₂, hvwf₁, hvwf₂ with
    | .VLam body₁ ρ₁', .VLam body₂ ρ₂', hvwf₁, hvwf₂ =>
      simp only [step, ValueRefinesKWF] at hv ⊢
      obtain ⟨_, _, hv_fn⟩ := hv
      exact hv_fn m₂ (by omega) w₁ w₂ (valueRefinesKWF_mono (by omega) w₁ w₂ hw) hwwf₁ hwwf₂
        m₂ (Nat.le_refl _) π₁ π₂ hwf_π₁ hwf_π₂
        (fun i' hi' x₁ x₂ hx' hx_wf₁ hx_wf₂ => hπ i' (by omega) x₁ x₂ hx' hx_wf₁ hx_wf₂)
    | .VBuiltin b₁ args₁ exp₁, .VBuiltin b₂ args₂ exp₂, hvwf₁, hvwf₂ =>
      simp only [ValueRefinesKWF] at hv; obtain ⟨rfl, rfl, hargs_rel⟩ := hv
      simp only [step]
      split
      · split
        · rename_i rest _
          have hval : ValueRefinesKWF (m₂ + 1)
              (.VBuiltin b₁ (w₁ :: args₁) rest) (.VBuiltin b₁ (w₂ :: args₂) rest) := by
            simp only [ValueRefinesKWF]; refine ⟨trivial, trivial, ?_⟩; simp only [ListRel]
            exact ⟨valueRefinesKWF_mono (by omega) w₁ w₂ hw,
                   listRel_mono (fun a b h => valueRefinesKWF_mono (by omega : m₂ ≤ m₁) a b h) hargs_rel⟩
          have hval_wf₁ : ValueWellFormed (.VBuiltin b₁ (w₁ :: args₁) rest) := by
            cases hvwf₁ with | vbuiltin _ _ ha => exact .vbuiltin _ _ (.cons hwwf₁ ha)
          have hval_wf₂ : ValueWellFormed (.VBuiltin b₁ (w₂ :: args₂) rest) := by
            cases hvwf₂ with | vbuiltin _ _ ha => exact .vbuiltin _ _ (.cons hwwf₂ ha)
          exact obsRefinesK_mono (by omega) (hπ (m₂ + 1) (by omega) _ _ hval hval_wf₁ hval_wf₂)
        · have hwf_args₁ : ValueListWellFormed (w₁ :: args₁) := by
            cases hvwf₁ with | vbuiltin _ _ ha => exact .cons hwwf₁ ha
          have hwf_args₂ : ValueListWellFormed (w₂ :: args₂) := by
            cases hvwf₂ with | vbuiltin _ _ ha => exact .cons hwwf₂ ha
          exact evalBuiltin_compat_refinesWF
            (by simp only [ListRel]
                exact ⟨valueRefinesKWF_mono (by omega) w₁ w₂ hw,
                  listRel_mono (fun a b h => valueRefinesKWF_mono (by omega : m₂ ≤ m₁) a b h) hargs_rel⟩)
            ⟨hwf_π₁, hwf_π₂, fun j₀ hj₀ => hπ j₀ (by omega)⟩
            hwf_args₁ hwf_args₂
      · exact obsRefinesK_error _
    | .VCon _, .VCon _, _, _ => simp only [step]; exact obsRefinesK_error _
    | .VDelay _ _, .VDelay _ _, _, _ => simp only [step]; exact obsRefinesK_error _
    | .VConstr _ _, .VConstr _ _, _, _ => simp only [step]; exact obsRefinesK_error _
    | .VCon _, .VLam _ _, _, _ | .VCon _, .VDelay _ _, _, _
    | .VCon _, .VConstr _ _, _, _ | .VCon _, .VBuiltin _ _ _, _, _
    | .VLam _ _, .VCon _, _, _ | .VLam _ _, .VDelay _ _, _, _
    | .VLam _ _, .VConstr _ _, _, _ | .VLam _ _, .VBuiltin _ _ _, _, _
    | .VDelay _ _, .VCon _, _, _ | .VDelay _ _, .VLam _ _, _, _
    | .VDelay _ _, .VConstr _ _, _, _ | .VDelay _ _, .VBuiltin _ _ _, _, _
    | .VConstr _ _, .VCon _, _, _ | .VConstr _ _, .VLam _ _, _, _
    | .VConstr _ _, .VDelay _ _, _, _ | .VConstr _ _, .VBuiltin _ _ _, _, _
    | .VBuiltin _ _ _, .VCon _, _, _ | .VBuiltin _ _ _, .VLam _ _, _, _
    | .VBuiltin _ _ _, .VDelay _ _, _, _ | .VBuiltin _ _ _, .VConstr _ _, _, _ =>
      simp only [ValueRefinesKWF] at hv
  | .Force e =>
    simp [closedAt] at ht
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    apply ftlr_wf d e ht k (i'+1) (by omega) ρ₁ ρ₂ (envRefinesKWF_mono (by omega) henv)
      henv_wf_l hlen_l henv_wf_r hlen_r i' (by omega)
      (Frame.force :: π₁) (Frame.force :: π₂)
      (.cons .force hwf_π₁) (.cons .force hwf_π₂)
    intro j' hj' v₁ v₂ hv hvwf₁ hvwf₂
    match j' with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | m + 1 =>
    obsRefinesK_of_step_auto
    match v₁, v₂, hvwf₁, hvwf₂ with
    | .VDelay body₁ ρ₁', .VDelay body₂ ρ₂', hvwf₁, hvwf₂ =>
      simp only [step, ValueRefinesKWF] at hv ⊢
      exact hv m (by omega) m (by omega) π₁ π₂ hwf_π₁ hwf_π₂
        (fun i' hi' w₁ w₂ hw' hw₁ hw₂ => hπ i' (by omega) w₁ w₂ hw' hw₁ hw₂)
    | .VBuiltin b₁ args₁ ea₁, .VBuiltin b₂ args₂ ea₂, hvwf₁, hvwf₂ =>
      simp only [ValueRefinesKWF] at hv; obtain ⟨rfl, rfl, hargs_rel⟩ := hv; simp only [step]
      split
      · split
        · rename_i rest _
          have hval : ValueRefinesKWF (m + 1)
              (.VBuiltin b₁ args₁ rest) (.VBuiltin b₁ args₂ rest) := by
            simp only [ValueRefinesKWF]; exact ⟨trivial, trivial, hargs_rel⟩
          have hval_wf₁ : ValueWellFormed (.VBuiltin b₁ args₁ rest) := by
            cases hvwf₁ with | vbuiltin _ _ ha => exact .vbuiltin _ _ ha
          have hval_wf₂ : ValueWellFormed (.VBuiltin b₁ args₂ rest) := by
            cases hvwf₂ with | vbuiltin _ _ ha => exact .vbuiltin _ _ ha
          exact obsRefinesK_mono (by omega) (hπ (m + 1) (by omega) _ _ hval hval_wf₁ hval_wf₂)
        · have hwf_args₁ : ValueListWellFormed args₁ := by
            cases hvwf₁ with | vbuiltin _ _ ha => exact ha
          have hwf_args₂ : ValueListWellFormed args₂ := by
            cases hvwf₂ with | vbuiltin _ _ ha => exact ha
          exact evalBuiltin_compat_refinesWF hargs_rel
            ⟨hwf_π₁, hwf_π₂, fun j₀ hj₀ => hπ j₀ (by omega)⟩
            hwf_args₁ hwf_args₂
      · exact obsRefinesK_error _
    | .VCon _, .VCon _, _, _ => simp only [step]; exact obsRefinesK_error _
    | .VLam _ _, .VLam _ _, _, _ => simp only [step]; exact obsRefinesK_error _
    | .VConstr _ _, .VConstr _ _, _, _ => simp only [step]; exact obsRefinesK_error _
    | .VCon _, .VLam _ _, _, _ | .VCon _, .VDelay _ _, _, _
    | .VCon _, .VConstr _ _, _, _ | .VCon _, .VBuiltin _ _ _, _, _
    | .VLam _ _, .VCon _, _, _ | .VLam _ _, .VDelay _ _, _, _
    | .VLam _ _, .VConstr _ _, _, _ | .VLam _ _, .VBuiltin _ _ _, _, _
    | .VDelay _ _, .VCon _, _, _ | .VDelay _ _, .VLam _ _, _, _
    | .VDelay _ _, .VConstr _ _, _, _ | .VDelay _ _, .VBuiltin _ _ _, _, _
    | .VConstr _ _, .VCon _, _, _ | .VConstr _ _, .VLam _ _, _, _
    | .VConstr _ _, .VDelay _ _, _, _ | .VConstr _ _, .VBuiltin _ _ _, _, _
    | .VBuiltin _ _ _, .VCon _, _, _ | .VBuiltin _ _ _, .VLam _ _, _, _
    | .VBuiltin _ _ _, .VDelay _ _, _, _ | .VBuiltin _ _ _, .VConstr _ _, _, _ =>
      simp only [ValueRefinesKWF] at hv
  | .Constr tag fields =>
    match fields with
    | [] =>
      match i with
      | 0 => obsRefinesK_zero_nonhalt_auto
      | i' + 1 =>
      obsRefinesK_of_step_auto
      simp only [step]
      have : ValueRefinesKWF i' (.VConstr tag []) (.VConstr tag []) := by
        cases i' with
        | zero => simp only [ValueRefinesKWF]
        | succ => simp only [ValueRefinesKWF, ListRel]; exact ⟨trivial, trivial⟩
      exact hπ i' (by omega) _ _ this (.vconstr _ .nil) (.vconstr _ .nil)
    | m :: ms =>
      simp [closedAt] at ht
      have hm : closedAt d m = true := by
        have := ht; simp [closedAtList] at this; exact this.1
      have hms : closedAtList d ms = true := by
        have := ht; simp [closedAtList] at this; exact this.2
      match i with
      | 0 => obsRefinesK_zero_nonhalt_auto
      | i' + 1 =>
      obsRefinesK_of_step_auto
      simp only [step]
      have hwf_stack₁ : StackWellFormed (.constrField tag [] ms ρ₁ :: π₁) :=
        .cons (.constrField tag .nil henv_wf_l hlen_l hms) hwf_π₁
      have hwf_stack₂ : StackWellFormed (.constrField tag [] ms ρ₂ :: π₂) :=
        .cons (.constrField tag .nil henv_wf_r hlen_r hms) hwf_π₂
      apply ftlr_wf d m hm k (i'+1) (by omega) ρ₁ ρ₂ (envRefinesKWF_mono (by omega) henv)
        henv_wf_l hlen_l henv_wf_r hlen_r i' (by omega)
        (.constrField tag [] ms ρ₁ :: π₁) (.constrField tag [] ms ρ₂ :: π₂)
        hwf_stack₁ hwf_stack₂
      exact constrFieldWF (ftlr_wf_list d ms hms (i'+1))
        (by omega) (envRefinesKWF_mono (by omega) henv) henv_wf_l hlen_l henv_wf_r hlen_r
        trivial .nil .nil hms hwf_π₁ hwf_π₂
        (fun j₀ hj₀ w₁ w₂ hw hw₁ hw₂ => hπ j₀ (by omega) w₁ w₂ hw hw₁ hw₂)
  | .Case scrut alts =>
    simp [closedAt] at ht; obtain ⟨hscrut, halts⟩ := ht
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    have hwf_stack₁ : StackWellFormed (.caseScrutinee alts ρ₁ :: π₁) :=
      .cons (.caseScrutinee henv_wf_l hlen_l halts) hwf_π₁
    have hwf_stack₂ : StackWellFormed (.caseScrutinee alts ρ₂ :: π₂) :=
      .cons (.caseScrutinee henv_wf_r hlen_r halts) hwf_π₂
    apply ftlr_wf d scrut hscrut k (i'+1) (by omega) ρ₁ ρ₂ (envRefinesKWF_mono (by omega) henv)
      henv_wf_l hlen_l henv_wf_r hlen_r i' (by omega)
      (.caseScrutinee alts ρ₁ :: π₁) (.caseScrutinee alts ρ₂ :: π₂)
      hwf_stack₁ hwf_stack₂
    intro j' hj' v₁ v₂ hv hvwf₁ hvwf₂
    match j' with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | n + 1 =>
    obsRefinesK_of_step_auto
    match v₁, v₂, hvwf₁, hvwf₂ with
    | .VConstr tag₁ fields₁, .VConstr tag₂ fields₂, hvwf₁, hvwf₂ =>
      simp only [ValueRefinesKWF] at hv; obtain ⟨rfl, hfields_v⟩ := hv
      simp only [step]
      have hwf_fields₁ : ValueListWellFormed fields₁ := by
        cases hvwf₁ with | vconstr _ h => exact h
      have hwf_fields₂ : ValueListWellFormed fields₂ := by
        cases hvwf₂ with | vconstr _ h => exact h
      split
      · rename_i alt₁ halt₁
        have hsome₁ := List.getElem?_eq_some_iff.mp halt₁
        have hi₁ : tag₁ < alts.length := hsome₁.1
        have heq₁ : alt₁ = alts[tag₁] := hsome₁.2.symm
        subst heq₁
        have haltsList := ftlr_wf_list d alts halts (i'+1)
        have halt_at := listRel_getElem_self haltsList hi₁
        apply halt_at (n+1) (by omega) ρ₁ ρ₂ (envRefinesKWF_mono (by omega) henv)
          henv_wf_l hlen_l henv_wf_r hlen_r n (by omega)
          (fields₁.map Frame.applyArg ++ π₁) (fields₂.map Frame.applyArg ++ π₂)
          (stackWellFormed_applyArgFrames hwf_fields₁ hwf_π₁)
          (stackWellFormed_applyArgFrames hwf_fields₂ hwf_π₂)
        exact applyArgFrames_stackFnKWF
          (listRel_mono (fun a b h => valueRefinesKWF_mono (by omega) a b h) hfields_v)
          hwf_fields₁ hwf_fields₂ hwf_π₁ hwf_π₂
          (fun j₀ hj₀ w₁ w₂ hw hw₁ hw₂ => hπ j₀ (by omega) w₁ w₂ hw hw₁ hw₂)
      · exact obsRefinesK_error _
    | .VCon c₁, .VCon c₂, hvwf₁, hvwf₂ =>
      simp only [ValueRefinesKWF] at hv; subst hv
      simp only [step]
      split
      · rename_i tag numCtors fields htag
        split
        · exact obsRefinesK_error _
        · rename_i h_check
          split
          · rename_i alt₁ halt₁
            have hsome₁ := List.getElem?_eq_some_iff.mp halt₁
            have hi₁ : tag < alts.length := hsome₁.1
            have heq₁ : alt₁ = alts[tag] := hsome₁.2.symm
            subst heq₁
            have haltsList := ftlr_wf_list d alts halts (i'+1)
            have halt_at := listRel_getElem_self haltsList hi₁
            have hfields_vcon := constToTagAndFields_fields_vcon c₁
            rw [htag] at hfields_vcon
            have hfields_wf : ValueListWellFormed fields := by
              have := constToTagAndFields_fields_wf c₁; rw [htag] at this; exact this
            apply halt_at (n+1) (by omega) ρ₁ ρ₂ (envRefinesKWF_mono (by omega) henv)
              henv_wf_l hlen_l henv_wf_r hlen_r n (by omega)
              (fields.map Frame.applyArg ++ π₁) (fields.map Frame.applyArg ++ π₂)
              (stackWellFormed_applyArgFrames hfields_wf hwf_π₁)
              (stackWellFormed_applyArgFrames hfields_wf hwf_π₂)
            exact applyArgFrames_stackFnKWF
              (listRel_refl_vcon_refinesWF_local n fields hfields_vcon)
              hfields_wf hfields_wf hwf_π₁ hwf_π₂
              (fun j₀ hj₀ w₁ w₂ hw hw₁ hw₂ => hπ j₀ (by omega) w₁ w₂ hw hw₁ hw₂)
          · exact obsRefinesK_error _
      · exact obsRefinesK_error _
    | .VLam _ _, .VLam _ _, _, _ | .VDelay _ _, .VDelay _ _, _, _
    | .VBuiltin _ _ _, .VBuiltin _ _ _, _, _ => simp only [step]; exact obsRefinesK_error _
    | .VCon _, .VLam _ _, _, _ | .VCon _, .VDelay _ _, _, _
    | .VCon _, .VConstr _ _, _, _ | .VCon _, .VBuiltin _ _ _, _, _
    | .VLam _ _, .VCon _, _, _ | .VLam _ _, .VDelay _ _, _, _
    | .VLam _ _, .VConstr _ _, _, _ | .VLam _ _, .VBuiltin _ _ _, _, _
    | .VDelay _ _, .VCon _, _, _ | .VDelay _ _, .VLam _ _, _, _
    | .VDelay _ _, .VConstr _ _, _, _ | .VDelay _ _, .VBuiltin _ _ _, _, _
    | .VConstr _ _, .VCon _, _, _ | .VConstr _ _, .VLam _ _, _, _
    | .VConstr _ _, .VDelay _ _, _, _ | .VConstr _ _, .VBuiltin _ _ _, _, _
    | .VBuiltin _ _ _, .VCon _, _, _ | .VBuiltin _ _ _, .VLam _ _, _, _
    | .VBuiltin _ _ _, .VDelay _ _, _, _ | .VBuiltin _ _ _, .VConstr _ _, _, _ =>
      simp only [ValueRefinesKWF] at hv
  termination_by sizeOf t

def ftlr_wf_list (d : Nat) (ts : List Term) (hts : closedAtList d ts = true) (k : Nat) :
    ListRel (fun t₁ t₂ =>
      ∀ j ≤ k, ∀ ρ₁ ρ₂, EnvRefinesKWF j d ρ₁ ρ₂ →
        EnvWellFormed d ρ₁ → d ≤ ρ₁.length →
        EnvWellFormed d ρ₂ → d ≤ ρ₂.length →
        ∀ i ≤ j, ∀ π₁ π₂,
          StackWellFormed π₁ → StackWellFormed π₂ → StackFnKWF i π₁ π₂ →
          ObsRefinesK i (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂))
      ts ts := by
  match ts, hts with
  | [], _ => trivial
  | t :: rest, hts =>
    simp [closedAtList] at hts
    exact ⟨ftlr_wf d t hts.1 k, ftlr_wf_list d rest hts.2 k⟩
  termination_by sizeOf ts

end

end Moist.Verified.FundamentalRefinesWF
