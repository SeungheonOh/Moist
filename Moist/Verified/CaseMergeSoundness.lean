import Moist.Verified.CaseMerge.Compat
import Moist.Verified.HygieneSoundness

variable [sv : Moist.CEK.SemVariant]

/-! # Soundness of known-constructor case simplification

`caseMerge Γ e` is related to `e` by the well-formedness-guarded logical
relation in every pair of related environments in which the facts `Γ` hold
of the source environment (`caseMerge_eval`). Facts are only introduced by
`let` bindings whose processed right-hand side is an atom or a constructor of
atoms; `simple_eval` shows the source right-hand side then returns exactly
that value, so the fact holds of the source environment. A case on a fact
variable or literal is matched step by step against the selected alternative
applied to the atomic fields (`atomArgs_stackRel`); a case on a literal
constructor is closed by the same-environment rule `reduce_correct`.

The whole pass is certified by `caseMergePass_refines`.
-/

namespace Moist.Verified.CaseMerge

open Moist.CEK
open Moist.MIR
open Moist.Plutus.Term (Term)
open Moist.Verified (closedAt closedAtList)
open Moist.Verified.Equivalence (steps Reaches steps_trans steps_error ListRel ObsRefinesK
  obsRefinesK_of_steps_left obsRefinesK_of_steps_right)
open Moist.Verified.Contextual (ObsRefines CtxRefines fill fill_closedAt_iff)
open Moist.Verified.Contextual.Guarded
open Moist.Verified.TermObsRefinesWF (wfGuard)
open Moist.Verified.BetaValueRefines (EnvWellFormed StackWellFormed ValueWellFormed
  envWellFormed_lookup envWellFormed_extend)
open Moist.Verified.StepWellFormed (StateWellFormed steps_preserves_wf)
open Moist.Verified.MIR (MIRCtxRefines lowerTotalExprList lowerTotalExprList_nil
  lowerTotalExprList_cons lowerTotalExpr_case_of_list lowerTotalExpr_constr_of_list
  lowerTotalExpr_lam lowerTotalExpr_app lowerTotalExpr_force lowerTotalExpr_delay
  lowerTotalExpr_let_nil_eq lowerTotalExpr_closedAt lowerTotalList_closedAtList
  lowerTotalExpr_atom_valueTerm mirCtxRefines_trans)

/-! ## Environments -/

/-- Related, well-formed run-time environments for the lowering environment `env`. -/
structure EnvOK (k : Nat) (env : List VarId) (ρ₁ ρ₂ : CekEnv) : Prop where
  rel : EnvRel wfGuard k env.length ρ₁ ρ₂
  wf₁ : EnvWellFormed env.length ρ₁
  len₁ : env.length ≤ ρ₁.length
  wf₂ : EnvWellFormed env.length ρ₂
  len₂ : env.length ≤ ρ₂.length

theorem EnvOK.mono {j k : Nat} {env : List VarId} {ρ₁ ρ₂ : CekEnv} (hjk : j ≤ k)
    (h : EnvOK k env ρ₁ ρ₂) : EnvOK j env ρ₁ ρ₂ :=
  ⟨envRel_mono hjk h.rel, h.wf₁, h.len₁, h.wf₂, h.len₂⟩

theorem EnvOK.extend {k : Nat} {env : List VarId} {ρ₁ ρ₂ : CekEnv} (h : EnvOK k env ρ₁ ρ₂)
    (x : VarId) {a₁ a₂ : CekValue} (ha : ValueRel wfGuard k a₁ a₂) (ha₁ : ValueWellFormed a₁)
    (ha₂ : ValueWellFormed a₂) : EnvOK k (x :: env) (ρ₁.extend a₁) (ρ₂.extend a₂) :=
  ⟨by simpa using envRel_extend h.rel ha,
   by simpa using envWellFormed_extend _ h.wf₁ h.len₁ ha₁,
   by simp [CekEnv.extend, CekEnv.length]; exact h.len₁,
   by simpa using envWellFormed_extend _ h.wf₂ h.len₂ ha₂,
   by simp [CekEnv.extend, CekEnv.length]; exact h.len₂⟩

theorem EnvOK.lookup₁ {k : Nat} {env : List VarId} {ρ₁ ρ₂ : CekEnv} (h : EnvOK k env ρ₁ ρ₂) :
    ∀ n, 0 < n → n ≤ env.length → ∃ v, ρ₁.lookup n = some v := fun _ hn hnd =>
  let ⟨v, hv, _⟩ := envWellFormed_lookup _ h.wf₁ hn hnd; ⟨v, hv⟩

theorem fieldsOK_of_factsHold {Γ : KnownCtors} {env : List VarId} {ρ : CekEnv}
    (h : FactsHold Γ env ρ) : FieldsOK Γ env := by
  intro p hp f hf
  obtain ⟨_, _, _, _, vs, _, hl⟩ := h p hp
  obtain ⟨_, _, ha, t, ht, _⟩ := listRel2_mem_left hl f hf
  exact ⟨ha, by rw [ht]; rfl⟩

theorem atomEval_wf {env : List VarId} {ρ : CekEnv} {f : Expr} {w : CekValue}
    (h : AtomEval env ρ f w) (hρ : EnvWellFormed env.length ρ) (hlen : env.length ≤ ρ.length) :
    ValueWellFormed w := by
  obtain ⟨ha, t, ht, hs⟩ := h
  have hv := lowerTotalExpr_atom_valueTerm ha ht
  have := hs []
  rw [isValueTerm_step hρ hv] at this
  cases this
  exact isValueTerm_wf hρ hlen hv

theorem atomEvals_wf {env : List VarId} {ρ : CekEnv} (hρ : EnvWellFormed env.length ρ)
    (hlen : env.length ≤ ρ.length) :
    ∀ {fs : List Expr} {ws : List CekValue}, ListRel2 (AtomEval env ρ) fs ws →
      ∀ w ∈ ws, ValueWellFormed w
  | [], [], _, w, hw => by cases hw
  | f :: fs, v :: vs, h, w, hw => by
    rcases List.mem_cons.mp hw with rfl | hw
    · exact atomEval_wf h.1 hρ hlen
    · exact atomEvals_wf hρ hlen h.2 w hw
  | [], _ :: _, h, _, _ => absurd h id
  | _ :: _, [], h, _, _ => absurd h id

/-! ## Guarded-relation helpers -/

theorem obsRefinesK_error_left {k : Nat} {s : State} (h : Reaches s .error) :
    ObsRefinesK k .error s :=
  ⟨fun v ⟨n, _, hn⟩ => (by rw [steps_error] at hn; cases hn), fun _ _ _ => h⟩

/-- A same-environment refinement of the right side composes with the relation. -/
theorem eval_sameRef_right {k d : Nat} {ρ₁ ρ₂ : CekEnv} {t₁ t₂ t₃ : Term}
    (h : Eval wfGuard k ρ₁ ρ₂ t₁ t₂) (hsame : SameRef d t₂ t₃)
    (hρ : EnvWellFormed d ρ₂) (hlen : d ≤ ρ₂.length) (hc : closedAt d t₂ = true) :
    Eval wfGuard k ρ₁ ρ₂ t₁ t₃ := by
  intro j hj π₁ π₂ hπ hst₁ _
  have hst₂ : wfGuard.St (.compute π₂ ρ₂ t₂) := StateWellFormed.compute hπ.2.1 hρ hlen hc
  exact InlineSoundness.SubstRefinesExt.obsRefinesK_compose_obsRefines_right
    (h j hj π₁ π₂ hπ hst₁ hst₂) (hsame ρ₂ π₂ hρ hlen hπ.2.1)

/-- The Z-combinator wrapper of a recursive function. -/
theorem eval_fixWrap {k : Nat} {ρ₁ ρ₂ : CekEnv} {b₁ b₂ : Term}
    (h : ∀ j < k, ∀ s₁ s₂ f₁ f₂ x₁ x₂,
      ValueRel wfGuard j s₁ s₂ → ValueWellFormed s₁ → ValueWellFormed s₂ →
      ValueRel wfGuard j f₁ f₂ → ValueWellFormed f₁ → ValueWellFormed f₂ →
      ValueRel wfGuard j x₁ x₂ → ValueWellFormed x₁ → ValueWellFormed x₂ →
      Eval wfGuard j (((ρ₁.extend s₁).extend f₁).extend x₁)
        (((ρ₂.extend s₂).extend f₂).extend x₂) b₁ b₂) :
    Eval wfGuard k ρ₁ ρ₂ (fixLamWrapUplc b₁) (fixLamWrapUplc b₂) := by
  unfold fixLamWrapUplc
  refine eval_apply (eval_refl (d := 0) (by simp [closedAt]) (envRel_zero k ρ₁ ρ₂)) ?_
  refine eval_lam 0 0 fun j hj s₁ s₂ hs hs₁ hs₂ => ?_
  refine eval_apply ?_ (eval_refl (d := 1) (by simp [closedAt])
    (by simpa using envRel_extend (envRel_zero j ρ₁ ρ₂) hs))
  refine eval_lam 0 0 fun j' hj' f₁ f₂ hf hf₁ hf₂ => ?_
  refine eval_lam 0 0 fun j'' hj'' x₁ x₂ hx hx₁ hx₂ => ?_
  exact h j'' (by omega) s₁ s₂ f₁ f₂ x₁ x₂ (valueRel_mono (by omega) hs) hs₁ hs₂
    (valueRel_mono (by omega) hf) hf₁ hf₂ hx hx₁ hx₂

omit sv in
theorem bindFact_of_fact {Γ : KnownCtors} {x : VarId} {r : Expr} {info : KnownCtor}
    (hk : knownConstructor Γ r = some info) (hx : (freeVarsList info.fields).contains x = false) :
    bindFact Γ x r = (x, info) :: filterKnown x Γ := by
  simp [bindFact, hk, hx]

omit sv in
theorem bindFact_of_no_fact {Γ : KnownCtors} {x : VarId} {r : Expr}
    (h : ¬ ∃ info, knownConstructor Γ r = some info ∧
      (freeVarsList info.fields).contains x = false) :
    bindFact Γ x r = filterKnown x Γ := by
  unfold bindFact
  cases hk : knownConstructor Γ r with
  | none => rfl
  | some info =>
    simp only []
    cases hc : (freeVarsList info.fields).contains x with
    | true => rfl
    | false => exact absurd ⟨info, hk, hc⟩ h

omit sv in
theorem wf_of_ret {π : Stack} {v : CekValue} (h : StateWellFormed (.ret π v)) :
    ValueWellFormed v := by
  cases h with | ret _ hv => exact hv

/-! ## The fundamental lemma -/

mutual

theorem caseMerge_eval : ∀ (e : Expr) (Γ : KnownCtors) (env : List VarId) (t₁ t₂ : Term),
    lowerTotalExpr env e = some t₁ → lowerTotalExpr env (caseMerge Γ e).1 = some t₂ →
    ∀ (k : Nat) (ρ₁ ρ₂ : CekEnv), EnvOK k env ρ₁ ρ₂ → FactsHold Γ env ρ₁ →
      Eval wfGuard k ρ₁ ρ₂ t₁ t₂
  | .Var x, Γ, env, t₁, t₂, h₁, h₂, k, ρ₁, ρ₂, henv, _ => by
    rw [caseMerge_var, h₁] at h₂; cases h₂
    exact eval_refl (lowerTotalExpr_closedAt h₁) henv.rel
  | .Lit l, Γ, env, t₁, t₂, h₁, h₂, k, ρ₁, ρ₂, henv, _ => by
    rw [caseMerge_lit, h₁] at h₂; cases h₂
    exact eval_refl (lowerTotalExpr_closedAt h₁) henv.rel
  | .Builtin b, Γ, env, t₁, t₂, h₁, h₂, k, ρ₁, ρ₂, henv, _ => by
    rw [caseMerge_builtin, h₁] at h₂; cases h₂
    exact eval_refl (lowerTotalExpr_closedAt h₁) henv.rel
  | .Error, Γ, env, t₁, t₂, h₁, h₂, k, ρ₁, ρ₂, henv, _ => by
    rw [caseMerge_error, h₁] at h₂; cases h₂
    exact eval_refl (lowerTotalExpr_closedAt h₁) henv.rel
  | .Lam x b, Γ, env, t₁, t₂, h₁, h₂, k, ρ₁, ρ₂, henv, hΓ => by
    rw [lowerTotalExpr_lam] at h₁
    rw [caseMerge_lam, lowerTotalExpr_lam] at h₂
    cases hb₁ : lowerTotalExpr (x :: env) b <;> simp [hb₁] at h₁
    cases hb₂ : lowerTotalExpr (x :: env) (caseMerge (filterKnown x Γ) b).1 <;> simp [hb₂] at h₂
    subst h₁; subst h₂
    exact eval_lam 0 0 fun j hj a₁ a₂ ha ha₁ ha₂ =>
      caseMerge_eval b (filterKnown x Γ) (x :: env) _ _ hb₁ hb₂ j _ _
        ((henv.mono (Nat.le_of_lt hj)).extend x ha ha₁ ha₂)
        (factsHold_cons filterKnown_sub' hΓ a₁)
  | .Fix f body, Γ, env, t₁, t₂, h₁, h₂, k, ρ₁, ρ₂, henv, hΓ => by
    cases body with
    | Lam x b =>
      rw [caseMerge_fix, caseMerge_lam] at h₂
      rw [lowerTotalExpr_fix_lam env f x b (caseMerge (filterKnown x (filterKnown f Γ)) b).1 Γ]
        at h₁
      rw [lowerTotalExpr_fix_lam' env f x b (caseMerge (filterKnown x (filterKnown f Γ)) b).1 Γ]
        at h₂
      generalize hs : fixSelf b (caseMerge (filterKnown x (filterKnown f Γ)) b).1 Γ = s at h₁ h₂
      have hsfresh : s.uid > maxUidKnown Γ := hs ▸ fixSelf_freshΓ _ _ Γ
      cases hb₁ : lowerTotalExpr (x :: f :: s :: env) b <;> simp [hb₁] at h₁
      cases hb₂ : lowerTotalExpr (x :: f :: s :: env)
        (caseMerge (filterKnown x (filterKnown f Γ)) b).1 <;> simp [hb₂] at h₂
      subst h₁; subst h₂
      refine eval_fixWrap fun j hj s₁ s₂ f₁ f₂ x₁ x₂ hs' hs₁ hs₂ hf hf₁ hf₂ hx hx₁ hx₂ => ?_
      exact caseMerge_eval b _ (x :: f :: s :: env) _ _ hb₁ hb₂ j _ _
        ((((henv.mono (Nat.le_of_lt hj)).extend s hs' hs₁ hs₂).extend f hf hf₁ hf₂).extend
          x hx hx₁ hx₂)
        (factsHold_cons filterKnown_sub'
          (factsHold_cons filterKnown_sub'
            (factsHold_cons (fresh_sub' hsfresh) hΓ s₁) f₁) x₁)
    | _ => simp [lowerTotalExpr, expandFix, lowerTotal] at h₁
  | .App fn a, Γ, env, t₁, t₂, h₁, h₂, k, ρ₁, ρ₂, henv, hΓ => by
    rw [lowerTotalExpr_app] at h₁
    rw [caseMerge_app, lowerTotalExpr_app] at h₂
    cases hf₁ : lowerTotalExpr env fn <;> cases ha₁ : lowerTotalExpr env a <;>
      simp [hf₁, ha₁] at h₁
    cases hf₂ : lowerTotalExpr env (caseMerge Γ fn).1 <;>
      cases ha₂ : lowerTotalExpr env (caseMerge Γ a).1 <;> simp [hf₂, ha₂] at h₂
    subst h₁; subst h₂
    exact eval_apply (caseMerge_eval fn Γ env _ _ hf₁ hf₂ k ρ₁ ρ₂ henv hΓ)
      (caseMerge_eval a Γ env _ _ ha₁ ha₂ k ρ₁ ρ₂ henv hΓ)
  | .Force e, Γ, env, t₁, t₂, h₁, h₂, k, ρ₁, ρ₂, henv, hΓ => by
    rw [lowerTotalExpr_force] at h₁
    rw [caseMerge_force, lowerTotalExpr_force] at h₂
    cases he₁ : lowerTotalExpr env e <;> simp [he₁] at h₁
    cases he₂ : lowerTotalExpr env (caseMerge Γ e).1 <;> simp [he₂] at h₂
    subst h₁; subst h₂
    exact eval_force (caseMerge_eval e Γ env _ _ he₁ he₂ k ρ₁ ρ₂ henv hΓ)
  | .Delay e, Γ, env, t₁, t₂, h₁, h₂, k, ρ₁, ρ₂, henv, hΓ => by
    rw [lowerTotalExpr_delay] at h₁
    rw [caseMerge_delay, lowerTotalExpr_delay] at h₂
    cases he₁ : lowerTotalExpr env e <;> simp [he₁] at h₁
    cases he₂ : lowerTotalExpr env (caseMerge Γ e).1 <;> simp [he₂] at h₂
    subst h₁; subst h₂
    exact eval_delay (caseMerge_eval e Γ env _ _ he₁ he₂ k ρ₁ ρ₂ henv hΓ)
  | .Constr tag fs, Γ, env, t₁, t₂, h₁, h₂, k, ρ₁, ρ₂, henv, hΓ => by
    rw [lowerTotalExpr_constr_of_list] at h₁
    rw [caseMerge_constr, lowerTotalExpr_constr_of_list] at h₂
    cases hl₁ : lowerTotalExprList env fs <;> simp [hl₁] at h₁
    cases hl₂ : lowerTotalExprList env (caseMergeList Γ fs).1 <;> simp [hl₂] at h₂
    subst h₁; subst h₂
    exact eval_constr tag (caseMergeList_eval fs Γ env _ _ hl₁ hl₂ k ρ₁ ρ₂ henv hΓ)
  | .Case s alts, Γ, env, t₁, t₂, h₁, h₂, k, ρ₁, ρ₂, henv, hΓ => by
    rw [lowerTotalExpr_case_of_list] at h₁
    cases hs₁ : lowerTotalExpr env s <;> cases ha₁ : lowerTotalExprList env alts <;>
      simp [hs₁, ha₁] at h₁
    rename_i ts talts
    subst h₁
    have hok := fieldsOK_of_factsHold hΓ
    obtain ⟨ts', hs₂, _⟩ := caseMerge_lower s Γ env ts hs₁ hok
    obtain ⟨talts', ha₂, _⟩ := caseMergeList_lower alts Γ env talts ha₁ hok
    have IHs := caseMerge_eval s Γ env ts ts' hs₁ hs₂ k ρ₁ ρ₂ henv hΓ
    have IHa := caseMergeList_eval alts Γ env talts talts' ha₁ ha₂ k ρ₁ ρ₂ henv hΓ
    rw [caseMerge_case] at h₂
    rcases caseResult_cases Γ (caseMerge Γ s).1 (caseMergeList Γ alts).1 with
      ⟨tag, fields, hc, hr⟩ | ⟨info, _, hk, _, hr⟩ | hr
    · -- A literal constructor: the same-environment rule on the right.
      rw [hr] at h₂
      have hlow : lowerTotalExpr env (.Case (.Constr tag fields) (caseMergeList Γ alts).1) =
          some (.Case ts' talts') := by
        rw [lowerTotalExpr_case_of_list, ← hc, hs₂, ha₂]; rfl
      obtain ⟨t₂', hl', _, hsame⟩ := reduce_correct tag fields _ env _ hlow
      rw [hl'] at h₂; cases h₂
      exact eval_sameRef_right (eval_case IHs IHa) hsame henv.wf₂ henv.len₂
        (lowerTotalExpr_closedAt hlow)
    · -- A recorded fact: select the alternative and pass the atomic fields.
      rw [hr] at h₂
      obtain ⟨hfok, _⟩ := knownConstructor_fields hk hs₂ hok
      obtain ⟨tf, htf⟩ := lowerTotalExprList_of_forall (fun f hf => (hfok f hf).2)
      rw [lower_selectAlternative htf ha₂] at h₂
      cases h₂
      intro j hj π₁ π₂ hπ hst₁ hst₂
      obtain ⟨v₁, hret, hsv⟩ :=
        simple_eval s Γ env ρ₁ ts hs₁ hΓ henv.lookup₁ (simple_of_known hk)
      obtain ⟨vs₁, hshape, hfields⟩ := factValue_of_simple hk hsv hΓ
      obtain ⟨n₁, hn₁⟩ := hret (.caseScrutinee talts ρ₁ :: π₁)
      have hL : steps (1 + n₁ + 1) (.compute π₁ ρ₁ (.Case ts talts)) =
          step (.ret (.caseScrutinee talts ρ₁ :: π₁) v₁) := by
        rw [steps_trans, steps_trans]
        show steps 1 (steps n₁ (.compute (.caseScrutinee talts ρ₁ :: π₁) ρ₁ ts)) = _
        rw [hn₁]; rfl
      rw [caseStep hshape] at hL
      have hlen : talts.length = talts'.length := by
        rw [lowerTotalExprList_length ha₁, lowerTotalExprList_length ha₂, caseMergeList_length]
      rw [hlen] at hL
      by_cases hcc : (decide (info.constructorCount > 0) &&
          decide (talts'.length > info.constructorCount)) = true
      · have hsel : selectTerm info.tag info.constructorCount tf talts' = .Error := by
          unfold selectTerm; rw [if_pos hcc]
        rw [if_pos hcc] at hL
        rw [hsel]
        exact obsRefinesK_of_steps_left hL (obsRefinesK_error_left ⟨1, rfl⟩)
      · rw [if_neg hcc] at hL
        cases hta : talts[info.tag]? with
        | none =>
          have hta' : talts'[info.tag]? = none := by
            have h₀ := List.getElem?_eq_none_iff.mp hta
            exact List.getElem?_eq_none_iff.mpr (by omega)
          have hsel : selectTerm info.tag info.constructorCount tf talts' = .Error := by
            unfold selectTerm; rw [if_neg hcc, hta']
          simp only [hta] at hL
          rw [hsel]
          exact obsRefinesK_of_steps_left hL (obsRefinesK_error_left ⟨1, rfl⟩)
        | some ta =>
          obtain ⟨ta', hta'⟩ : ∃ ta', talts'[info.tag]? = some ta' := by
            cases h : talts'[info.tag]? with
            | some ta' => exact ⟨ta', rfl⟩
            | none =>
              have h₀ := List.getElem?_eq_none_iff.mp h
              have h₁ : info.tag < talts.length := by
                cases hlt : decide (info.tag < talts.length) with
                | true => exact of_decide_eq_true hlt
                | false =>
                  have := List.getElem?_eq_none_iff.mpr (Nat.le_of_not_lt (of_decide_eq_false hlt))
                  rw [hta] at this; cases this
              omega
          have hsel : selectTerm info.tag info.constructorCount tf talts' = tf.foldl Term.Apply ta' := by
            unfold selectTerm; rw [if_neg hcc, hta']
          simp only [hta] at hL
          rw [hsel] at hst₂ ⊢
          have hwfL := steps_preserves_wf (1 + n₁ + 1) _ hst₁
          rw [hL] at hwfL
          have IHalt := listRel_getElem? IHa hta hta'
          obtain ⟨ws, hws, hvws⟩ := atomEvals_rel hfields (envRel_mono hj henv.rel)
          have hsteps := atomEvals_steps hws htf
          have hR := steps_foldl_apply (ρ := ρ₂) tf ta' π₂
          have hwfR := steps_preserves_wf tf.length _ hst₂
          rw [hR] at hwfR
          refine obsRefinesK_of_steps_left hL (obsRefinesK_of_steps_right hR ?_)
          exact IHalt j hj _ _
            (atomArgs_stackRel hvws hsteps (atomEvals_wf henv.wf₂ henv.len₂ hws)
              (wfGuard.compute hwfL) (wfGuard.compute hwfR) hπ) hwfL hwfR
    · rw [hr, lowerTotalExpr_case_of_list, hs₂, ha₂] at h₂
      cases h₂
      exact eval_case IHs IHa
  | .Let [] body, Γ, env, t₁, t₂, h₁, h₂, k, ρ₁, ρ₂, henv, hΓ => by
    rw [lowerTotalExpr_let_nil_eq] at h₁
    rw [caseMerge_let_nil, lowerTotalExpr_let_nil_eq] at h₂
    exact caseMerge_eval body Γ env t₁ t₂ h₁ h₂ k ρ₁ ρ₂ henv hΓ
  | .Let ((x, r, er) :: rest) body, Γ, env, t₁, t₂, h₁, h₂, k, ρ₁, ρ₂, henv, hΓ => by
    rw [lowerTotalExpr_let_cons] at h₁
    rw [caseMerge_let_cons, lowerTotalExpr_let_cons] at h₂
    cases hr₁ : lowerTotalExpr env r <;>
      cases hb₁ : lowerTotalExpr (x :: env) (.Let rest body) <;> simp [hr₁, hb₁] at h₁
    rename_i tr tb
    subst h₁
    cases hr₂ : lowerTotalExpr env (caseMerge Γ r).1 <;> simp [hr₂] at h₂
    rename_i tr'
    have hb₂ := h₂
    generalize hΓ' : bindFact Γ x (caseMerge Γ r).1 = Γ' at hb₂
    cases hb₂' : lowerTotalExpr (x :: env)
      (.Let (caseMergeBinds Γ' rest).1 (caseMerge (caseMergeBinds Γ' rest).2.1 body).1) <;>
      simp [hb₂'] at hb₂
    rename_i tb'
    subst hb₂
    have hbody : lowerTotalExpr (x :: env) (caseMerge Γ' (.Let rest body)).1 = some tb' := by
      rw [caseMerge_let]; exact hb₂'
    by_cases hfact : ∃ info, knownConstructor Γ (caseMerge Γ r).1 = some info ∧
        (freeVarsList info.fields).contains x = false
    · -- The bound value is a known constructor: both sides evaluate it directly.
      obtain ⟨info, hk, hx⟩ := hfact
      rw [bindFact_of_fact hk hx] at hΓ'
      subst hΓ'
      intro j hj π₁ π₂ hπ hst₁ hst₂
      obtain ⟨v₁, hret₁, hsv⟩ :=
        simple_eval r Γ env ρ₁ tr hr₁ hΓ henv.lookup₁ (simple_of_known hk)
      obtain ⟨v₂, hret₂, hv⟩ := simpleVal_rel hsv hr₂ (envRel_mono hj henv.rel)
      obtain ⟨n₁, hn₁⟩ := hret₁ (.funV (.VLam tb ρ₁) :: π₁)
      obtain ⟨n₂, hn₂⟩ := hret₂ (.funV (.VLam tb' ρ₂) :: π₂)
      have hwfv₁ : ValueWellFormed v₁ := by
        have := steps_preserves_wf (3 + n₁) _ hst₁
        rw [steps_trans] at this
        exact wf_of_ret (hn₁ ▸ this)
      have hwfv₂ : ValueWellFormed v₂ := by
        have := steps_preserves_wf (3 + n₂) _ hst₂
        rw [steps_trans] at this
        exact wf_of_ret (hn₂ ▸ this)
      have hL : steps (3 + n₁ + 1) (.compute π₁ ρ₁ (.Apply (.Lam 0 tb) tr)) =
          .compute π₁ (ρ₁.extend v₁) tb := by
        rw [steps_trans, steps_trans]
        show steps 1 (steps n₁ (.compute (.funV (.VLam tb ρ₁) :: π₁) ρ₁ tr)) = _
        rw [hn₁]; rfl
      have hR : steps (3 + n₂ + 1) (.compute π₂ ρ₂ (.Apply (.Lam 0 tb') tr')) =
          .compute π₂ (ρ₂.extend v₂) tb' := by
        rw [steps_trans, steps_trans]
        show steps 1 (steps n₂ (.compute (.funV (.VLam tb' ρ₂) :: π₂) ρ₂ tr')) = _
        rw [hn₂]; rfl
      have hwfL := steps_preserves_wf (3 + n₁ + 1) _ hst₁
      rw [hL] at hwfL
      have hwfR := steps_preserves_wf (3 + n₂ + 1) _ hst₂
      rw [hR] at hwfR
      have hfacts : FactsHold ((x, info) :: filterKnown x Γ) (x :: env) (ρ₁.extend v₁) := by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨0, v₁, envLookupT_cons_self x env, BetaValueRefines.extend_lookup_one ρ₁ v₁,
            factValue_shift (factValue_of_simple hk hsv hΓ) hx v₁⟩
        · exact factsHold_cons filterKnown_sub' hΓ v₁ p hp
      refine obsRefinesK_of_steps_left hL (obsRefinesK_of_steps_right hR ?_)
      exact caseMerge_eval (.Let rest body) _ (x :: env) tb tb' hb₁ hbody j _ _
        ((henv.mono hj).extend x hv hwfv₁ hwfv₂) hfacts j (Nat.le_refl _) π₁ π₂ hπ hwfL hwfR
    · rw [bindFact_of_no_fact hfact] at hΓ'
      subst hΓ'
      refine eval_apply (eval_lam 0 0 fun j hj a₁ a₂ ha ha₁ ha₂ => ?_)
        (caseMerge_eval r Γ env tr tr' hr₁ hr₂ k ρ₁ ρ₂ henv hΓ)
      exact caseMerge_eval (.Let rest body) _ (x :: env) tb tb' hb₁ hbody j _ _
        ((henv.mono (Nat.le_of_lt hj)).extend x ha ha₁ ha₂)
        (factsHold_cons filterKnown_sub' hΓ a₁)
termination_by e => sizeOf e

theorem caseMergeList_eval : ∀ (es : List Expr) (Γ : KnownCtors) (env : List VarId)
    (ts₁ ts₂ : List Term), lowerTotalExprList env es = some ts₁ →
    lowerTotalExprList env (caseMergeList Γ es).1 = some ts₂ →
    ∀ (k : Nat) (ρ₁ ρ₂ : CekEnv), EnvOK k env ρ₁ ρ₂ → FactsHold Γ env ρ₁ →
      ListRel (Eval wfGuard k ρ₁ ρ₂) ts₁ ts₂
  | [], Γ, env, ts₁, ts₂, h₁, h₂, _, _, _, _, _ => by
    rw [lowerTotalExprList_nil] at h₁
    simp [caseMergeList, lowerTotalExprList_nil] at h₂
    cases h₁; subst h₂; exact trivial
  | e :: es, Γ, env, ts₁, ts₂, h₁, h₂, k, ρ₁, ρ₂, henv, hΓ => by
    have hcons : (caseMergeList Γ (e :: es)).1 = (caseMerge Γ e).1 :: (caseMergeList Γ es).1 := by
      simp [caseMergeList]
    rw [hcons, lowerTotalExprList_cons] at h₂
    rw [lowerTotalExprList_cons] at h₁
    cases he₁ : lowerTotalExpr env e <;> cases hes₁ : lowerTotalExprList env es <;>
      simp [he₁, hes₁] at h₁
    cases he₂ : lowerTotalExpr env (caseMerge Γ e).1 <;>
      cases hes₂ : lowerTotalExprList env (caseMergeList Γ es).1 <;> simp [he₂, hes₂] at h₂
    subst h₁; subst h₂
    exact ⟨caseMerge_eval e Γ env _ _ he₁ he₂ k ρ₁ ρ₂ henv hΓ,
      caseMergeList_eval es Γ env _ _ hes₁ hes₂ k ρ₁ ρ₂ henv hΓ⟩
termination_by es => sizeOf es

end

/-! ## Certificates -/

open Moist.Verified.TermObsRefinesWF (OpenRefinesWF soundness_refinesWF) in
/-- **`caseMerge` with no facts refines its input.** -/
theorem caseMerge_refines (e : Expr) : MIRCtxRefines e (caseMerge [] e).1 := by
  intro env
  cases h₁ : lowerTotalExpr env e with
  | none => exact ⟨by simp, trivial⟩
  | some t₁ =>
    obtain ⟨t₂, h₂, hcl⟩ := caseMerge_lower e [] env t₁ h₁ (fieldsOK_nil env)
    rw [h₂]
    refine ⟨fun _ => rfl, ?_⟩
    show CtxRefines t₁ t₂
    apply soundness_refinesWF (d := env.length)
    · intro k j hj ρ₁ ρ₂ henv hwf₁ hlen₁ hwf₂ hlen₂ i hi π₁ π₂ hπ₁ hπ₂ hπ
      have hc := lowerTotalExpr_closedAt h₁
      have hc₂ := hcl env.length hc (fieldsClosed_nil env _)
      exact caseMerge_eval e [] env t₁ t₂ h₁ h₂ j ρ₁ ρ₂ ⟨henv, hwf₁, hlen₁, hwf₂, hlen₂⟩
        (factsHold_nil env ρ₁) i hi π₁ π₂ ⟨hπ₁, hπ₂, hπ⟩
        (StateWellFormed.compute hπ₁ hwf₁ hlen₁ hc) (StateWellFormed.compute hπ₂ hwf₂ hlen₂ hc₂)
    · intro C hC
      obtain ⟨hC', ht⟩ := (fill_closedAt_iff C t₁ 0).mp hC
      exact (fill_closedAt_iff C t₂ 0).mpr ⟨hC', hcl _ ht (fieldsClosed_nil env _)⟩

/-- **Known-constructor case simplification is sound.** -/
theorem caseMergePass_refines (e : Expr) : MIRCtxRefines e (caseMergePass e).1 := by
  unfold caseMergePass
  exact mirCtxRefines_trans (MIR.Hygiene.uniqueOptimizationBinders_refines e)
    (mirCtxRefines_trans (caseMerge_refines _)
      (MIR.Hygiene.uniqueOptimizationBinders_refines _))

end Moist.Verified.CaseMerge
