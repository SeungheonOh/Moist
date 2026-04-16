import Moist.Verified.MIR.Primitives.Shared
import Moist.Verified.MIR.Primitives.LetHoistAppLeft

namespace Moist.Verified.MIR

open Moist.CEK
open Moist.Plutus.Term (Term)
open Moist.MIR
  (Expr VarId anfNormalizeCore anfNormalizeListCore anfNormalizeBindsCore anfAtom anfAtomList
   wrapLet flattenLetBody freeVars lowerTotalExpr lowerTotal lowerTotalLet envLookupT expandFix
   expandFix_freeVars_not_contains expandFixBinds lowerTotal_prepend_unused
   lowerTotal_prepend_unused_none)
open Moist.Verified
  (closedAt closedAtList renameTerm shiftRename liftRename liftRename_shiftRename renameTermList
   renameTermList_getElem renameTermList_length shiftRename_ge shiftRename_lt)
open Moist.Verified.Equivalence
  (steps_error steps_halt constToTagAndFields_fields_vcon listRel_reverse ListRel ObsEq
   ObsRefinesK steps Reaches obsRefinesK_mono obsRefinesK_zero_ret listRel_mono)
open Moist.Verified.Contextual
  (closedAtList_append Context fill ObsRefines CtxEq CtxRefines ctxEq_refl ctxRefines_refl
   ctxRefines_trans ctxEq_lam ctxEq_app ctxRefines_lam ctxRefines_app)
open Moist.Verified.FundamentalRefines
  (envRefinesK_to_renameEnvRef_shift Is0Preserving RenameEnvRef renameRefines_shift1 ftlr
   renameRefines renameRefinesR renameRefinesR_shift1 is0preserving_id is0preserving_shiftRename
   RenameEnvRefR envRefinesK_to_renameEnvRefR_shift renameEnvRefR_mono)
open Moist.Verified.Contextual.SoundnessRefines
  (EnvRefinesK BehRefinesK ValueRefinesK StackRefK valueRefinesK_mono evalBuiltin_compat_refines
   obsRefinesK_error stackRefK_mono listRel_valueRefinesK_mono applyArgFrames_stackRefK
   listRel_refl_vcon_refines)

/-! ## Section 7. Let-hoist-app-right-atom primitive

`.App g (.Let [(v, rhs, false)] body) ≈ .Let [(v, rhs, false)] (.App g body)`
when `g.isAtom = true ∧ v ∉ freeVars g`. -/

/-- For an atom term `t_g` (a leaf: `.Var n` with `n ≥ 1`, `.Constant`, or
    `.Builtin`), computing `t_g` in any non-empty stack/env takes a single
    CEK step and always succeeds when `closedAt d t_g` holds under a
    related env pair. The Var-case constraint `n ≥ 1` encodes the fact
    that lowered MIR atoms never produce `.Var 0` (the `+1` shift in the
    Var lowering). -/
def isLeafAtomTerm (t : Term) : Prop :=
  (∃ n, n ≥ 1 ∧ t = .Var n) ∨ (∃ ct, t = .Constant ct) ∨ (∃ b, t = .Builtin b)

/-- For atom MIR expressions, the lowering produces a leaf term. -/
theorem lowerTotal_atom_isLeafAtom :
    ∀ (env : List VarId) (g : Expr) (t_g : Term),
      g.isAtom = true →
      lowerTotal env (expandFix g) = some t_g →
      isLeafAtomTerm t_g := by
  intro env g t_g hatom hlow
  cases g with
  | Var x =>
    simp only [expandFix, lowerTotal] at hlow
    cases h : envLookupT env x with
    | none => rw [h] at hlow; simp at hlow
    | some idx =>
      rw [h] at hlow; simp at hlow; subst hlow
      exact .inl ⟨idx + 1, Nat.succ_le_succ (Nat.zero_le _), rfl⟩
  | Lit p =>
    obtain ⟨c, ty⟩ := p
    simp only [expandFix, lowerTotal] at hlow
    cases hlow
    exact .inr (.inl ⟨(c, ty), rfl⟩)
  | Builtin b =>
    simp only [expandFix, lowerTotal] at hlow
    cases hlow
    exact .inr (.inr ⟨b, rfl⟩)
  | _ => simp [Expr.isAtom] at hatom

/-- Lowering shape for `App g (Let v=rhs body)` when both sub-lowerings succeed. -/
private theorem lowerTotalExpr_app_g_let {env : List VarId} (v : VarId)
    {g rhs body : Expr} {t_g t_rhs t_body : Term}
    (h_g : lowerTotalExpr env g = some t_g)
    (h_rhs : lowerTotalExpr env rhs = some t_rhs)
    (h_body : lowerTotalExpr (v :: env) body = some t_body) :
    lowerTotalExpr env (.App g (.Let [(v, rhs, false)] body)) =
      some (.Apply t_g (.Apply (.Lam 0 t_body) t_rhs)) := by
  have h_g' : lowerTotal env (expandFix g) = some t_g := h_g
  have h_rhs' : lowerTotal env (expandFix rhs) = some t_rhs := h_rhs
  have h_body' : lowerTotal (v :: env) (expandFix body) = some t_body := h_body
  show lowerTotal env (expandFix (.App g (.Let [(v, rhs, false)] body))) =
    some (.Apply t_g (.Apply (.Lam 0 t_body) t_rhs))
  simp only [expandFix, expandFixBinds, lowerTotal,
             lowerTotalLet, Option.bind_eq_bind, Option.bind_some,
             h_g', h_rhs', h_body']

/-- Lowering shape for `Let v=rhs (App g body)` using the shifted form of `g`. -/
private theorem lowerTotalExpr_let_app_g {env : List VarId} (v : VarId)
    {g rhs body : Expr} {t_g t_rhs t_body : Term}
    (hfresh : (freeVars g).contains v = false)
    (h_g : lowerTotalExpr env g = some t_g)
    (h_rhs : lowerTotalExpr env rhs = some t_rhs)
    (h_body : lowerTotalExpr (v :: env) body = some t_body) :
    lowerTotalExpr env (.Let [(v, rhs, false)] (.App g body)) =
      some (.Apply (.Lam 0 (.Apply
        (renameTerm (shiftRename 1) t_g) t_body)) t_rhs) := by
  have h_g' : lowerTotal env (expandFix g) = some t_g := h_g
  have h_rhs' : lowerTotal env (expandFix rhs) = some t_rhs := h_rhs
  have h_body' : lowerTotal (v :: env) (expandFix body) = some t_body := h_body
  have hfresh_exp : (freeVars (expandFix g)).contains v = false :=
    expandFix_freeVars_not_contains g v hfresh
  have h_g_shift :
      lowerTotal (v :: env) (expandFix g) =
        some (renameTerm (shiftRename 1) t_g) :=
    lowerTotal_prepend_unused env v _ hfresh_exp t_g h_g'
  show lowerTotal env (expandFix (.Let [(v, rhs, false)] (.App g body))) =
    some (.Apply (.Lam 0 (.Apply
      (renameTerm (shiftRename 1) t_g) t_body)) t_rhs)
  simp only [expandFix, expandFixBinds, lowerTotal,
             lowerTotalLet, Option.bind_eq_bind, Option.bind_some,
             h_g_shift, h_rhs', h_body']

private theorem lowerTotalExpr_app_g_let_isSome (env : List VarId) (v : VarId)
    (g rhs body : Expr) :
    (lowerTotalExpr env (.App g (.Let [(v, rhs, false)] body))).isSome ↔
      (lowerTotalExpr env g).isSome ∧ (lowerTotalExpr env rhs).isSome ∧
      (lowerTotalExpr (v :: env) body).isSome := by
  constructor
  · intro hsome
    have h : (lowerTotal env (expandFix
        (.App g (.Let [(v, rhs, false)] body)))).isSome := hsome
    simp only [expandFix, expandFixBinds, lowerTotal,
               lowerTotalLet, Option.bind_eq_bind] at h
    cases hg : lowerTotal env (expandFix g) with
    | none => rw [hg] at h; simp at h
    | some t_g =>
      rw [hg] at h
      simp only [Option.bind_some] at h
      cases hr : lowerTotal env (expandFix rhs) with
      | none => rw [hr] at h; simp at h
      | some t_r =>
        rw [hr] at h
        simp only [Option.bind_some] at h
        cases hb : lowerTotal (v :: env) (expandFix body) with
        | none => rw [hb] at h; simp at h
        | some t_b =>
          have hg' : lowerTotalExpr env g = some t_g := hg
          have hr' : lowerTotalExpr env rhs = some t_r := hr
          have hb' : lowerTotalExpr (v :: env) body = some t_b := hb
          exact ⟨by rw [hg']; rfl, by rw [hr']; rfl, by rw [hb']; rfl⟩
  · rintro ⟨hg, hr, hb⟩
    cases hg' : lowerTotalExpr env g with
    | none => rw [hg'] at hg; exact absurd hg (by simp)
    | some t_g =>
      cases hr' : lowerTotalExpr env rhs with
      | none => rw [hr'] at hr; exact absurd hr (by simp)
      | some t_r =>
        cases hb' : lowerTotalExpr (v :: env) body with
        | none => rw [hb'] at hb; exact absurd hb (by simp)
        | some t_b =>
          rw [lowerTotalExpr_app_g_let v hg' hr' hb']
          rfl

private theorem lowerTotalExpr_let_app_g_isSome (env : List VarId) (v : VarId)
    (g rhs body : Expr) (hfresh : (freeVars g).contains v = false) :
    (lowerTotalExpr env (.Let [(v, rhs, false)] (.App g body))).isSome ↔
      (lowerTotalExpr env g).isSome ∧ (lowerTotalExpr env rhs).isSome ∧
      (lowerTotalExpr (v :: env) body).isSome := by
  have hfresh_exp : (freeVars (expandFix g)).contains v = false :=
    expandFix_freeVars_not_contains g v hfresh
  constructor
  · intro hsome
    have h : (lowerTotal env (expandFix
        (.Let [(v, rhs, false)] (.App g body)))).isSome := hsome
    simp only [expandFix, expandFixBinds, lowerTotal,
               lowerTotalLet, Option.bind_eq_bind] at h
    cases hr : lowerTotal env (expandFix rhs) with
    | none => rw [hr] at h; simp at h
    | some t_r =>
      rw [hr] at h
      simp only [Option.bind_some] at h
      cases hg_ext : lowerTotal (v :: env) (expandFix g) with
      | none => rw [hg_ext] at h; simp at h
      | some t_g_ext =>
        rw [hg_ext] at h
        simp only [Option.bind_some] at h
        cases hb : lowerTotal (v :: env) (expandFix body) with
        | none => rw [hb] at h; simp at h
        | some t_b =>
          cases hg : lowerTotal env (expandFix g) with
          | none =>
            have := lowerTotal_prepend_unused_none env v _ hfresh_exp hg
            rw [hg_ext] at this; exact absurd this (by simp)
          | some t_g =>
            have hg' : lowerTotalExpr env g = some t_g := hg
            have hr' : lowerTotalExpr env rhs = some t_r := hr
            have hb' : lowerTotalExpr (v :: env) body = some t_b := hb
            exact ⟨by rw [hg']; rfl, by rw [hr']; rfl, by rw [hb']; rfl⟩
  · rintro ⟨hg, hr, hb⟩
    cases hg' : lowerTotalExpr env g with
    | none => rw [hg'] at hg; exact absurd hg (by simp)
    | some t_g =>
      cases hr' : lowerTotalExpr env rhs with
      | none => rw [hr'] at hr; exact absurd hr (by simp)
      | some t_r =>
        cases hb' : lowerTotalExpr (v :: env) body with
        | none => rw [hb'] at hb; exact absurd hb (by simp)
        | some t_b =>
          rw [lowerTotalExpr_let_app_g v hfresh hg' hr' hb']
          rfl

/-! ### Component 3 support: atom value helpers -/

/-- Inner value helper for the let-hoist-app-right-atom proof.
    Given a leaf-atom term `t_g` and an environment-refinement, produces
    a value `v_g` (computed by stepping `t_g` in ρ₁) along with a related
    value on the ρ₂ side, plus explicit step equations. The atom step
    is stack-independent, so this parametrizes over the stack. -/
theorem leafAtomValues {t_g : Term} (h : isLeafAtomTerm t_g)
    {d : Nat} (hclosed : closedAt d t_g = true) :
    ∀ {k : Nat} {ρ₁ ρ₂ : CekEnv}, EnvRefinesK k d ρ₁ ρ₂ →
    ∃ v₁ v₂, ValueRefinesK k v₁ v₂ ∧
      (∀ π, Moist.CEK.step (.compute π ρ₁ t_g) = .ret π v₁) ∧
      (∀ π, Moist.CEK.step (.compute π ρ₂ t_g) = .ret π v₂) := by
  rcases h with ⟨n, hn1, rfl⟩ | ⟨⟨c, ty⟩, rfl⟩ | ⟨b, rfl⟩
  · intro k ρ₁ ρ₂ henv
    simp only [closedAt, decide_eq_true_eq] at hclosed
    obtain ⟨w₁, w₂, hl, hr, hrel⟩ := henv n hn1 hclosed
    refine ⟨w₁, w₂, hrel, ?_, ?_⟩
    · intro π
      show (match ρ₁.lookup n with | some v => State.ret π v | none => State.error) = _
      rw [hl]
    · intro π
      show (match ρ₂.lookup n with | some v => State.ret π v | none => State.error) = _
      rw [hr]
  · intro k _ _ _
    refine ⟨.VCon c, .VCon c, ?_, fun _ => rfl, fun _ => rfl⟩
    cases k with
    | zero => simp [ValueRefinesK]
    | succ _ => simp [ValueRefinesK]
  · intro k _ _ _
    refine ⟨.VBuiltin b [] (Moist.CEK.expectedArgs b),
             .VBuiltin b [] (Moist.CEK.expectedArgs b), ?_, fun _ => rfl, fun _ => rfl⟩
    cases k with
    | zero => simp [ValueRefinesK]
    | succ _ => simp only [ValueRefinesK, ListRel]; exact ⟨trivial, trivial, trivial⟩

/-- For a leaf-atom term and an extended env on one side, the shifted atom
    step produces the same value as the unshifted atom step on the base env. -/
theorem leafAtom_shift_step {t_g : Term} (h : isLeafAtomTerm t_g)
    {d : Nat} (hclosed : closedAt d t_g = true) :
    ∀ {ρ : CekEnv} (v_inner : CekValue) (w : CekValue),
      Moist.CEK.step (.compute [] ρ t_g) = .ret [] w →
      ∀ π, Moist.CEK.step (.compute π (ρ.extend v_inner)
        (renameTerm (shiftRename 1) t_g)) = .ret π w := by
  rcases h with ⟨n, hn1, rfl⟩ | ⟨⟨c, ty⟩, rfl⟩ | ⟨b, rfl⟩
  · intro ρ v_inner w hstep π
    simp only [closedAt, decide_eq_true_eq] at hclosed
    have hlook_some : ρ.lookup n = some w := by
      have hh : Moist.CEK.step (.compute [] ρ (.Var n)) =
          match ρ.lookup n with
          | some v => State.ret [] v
          | none => State.error := rfl
      rw [hh] at hstep
      split at hstep
      · rename_i v hv
        injection hstep with _ hveq
        rw [hv]; congr
      · exact State.noConfusion hstep
    have hsr : shiftRename 1 n = n + 1 := by
      simp [shiftRename]; omega
    have hlook : (ρ.extend v_inner).lookup (n + 1) = ρ.lookup n := by
      show (CekEnv.cons v_inner ρ).lookup (n + 1) = ρ.lookup n
      match n, hn1 with
      | k + 1, _ => rfl
    show (match (ρ.extend v_inner).lookup (shiftRename 1 n) with
          | some v => State.ret π v | none => State.error) = _
    rw [hsr, hlook, hlook_some]
  · intro _ _ w hstep π
    simp only [Moist.CEK.step] at hstep
    injection hstep with _ hweq
    subst hweq
    rfl
  · intro _ _ w hstep π
    simp only [Moist.CEK.step] at hstep
    injection hstep with _ hweq
    subst hweq
    rfl

/-! ### Component 3: let-hoist-app-right-atom primitive -/

/-- Helper: LHS lowers to none when any sub-expression fails to lower. -/
private theorem lowerTotalExpr_app_g_let_eq_none (env : List VarId) (v : VarId)
    (g rhs body : Expr)
    (h : lowerTotalExpr env g = none ∨
         lowerTotalExpr env rhs = none ∨
         lowerTotalExpr (v :: env) body = none) :
    lowerTotalExpr env (.App g (.Let [(v, rhs, false)] body)) = none := by
  cases hlhs : lowerTotalExpr env (.App g (.Let [(v, rhs, false)] body)) with
  | none => rfl
  | some _ =>
    have hs : (lowerTotalExpr env (.App g (.Let [(v, rhs, false)] body))).isSome := by
      rw [hlhs]; rfl
    obtain ⟨hg, hr, hb⟩ := (lowerTotalExpr_app_g_let_isSome env v g rhs body).mp hs
    rcases h with h | h | h
    · rw [h] at hg; exact absurd hg (by simp)
    · rw [h] at hr; exact absurd hr (by simp)
    · rw [h] at hb; exact absurd hb (by simp)

/-- Helper: RHS lowers to none when any sub-expression fails to lower. -/
private theorem lowerTotalExpr_let_app_g_eq_none (env : List VarId) (v : VarId)
    (g rhs body : Expr) (hfresh : (freeVars g).contains v = false)
    (h : lowerTotalExpr env g = none ∨
         lowerTotalExpr env rhs = none ∨
         lowerTotalExpr (v :: env) body = none) :
    lowerTotalExpr env (.Let [(v, rhs, false)] (.App g body)) = none := by
  cases hlhs : lowerTotalExpr env (.Let [(v, rhs, false)] (.App g body)) with
  | none => rfl
  | some _ =>
    have hs : (lowerTotalExpr env (.Let [(v, rhs, false)] (.App g body))).isSome := by
      rw [hlhs]; rfl
    obtain ⟨hg, hr, hb⟩ := (lowerTotalExpr_let_app_g_isSome env v g rhs body hfresh).mp hs
    rcases h with h | h | h
    · rw [h] at hg; exact absurd hg (by simp)
    · rw [h] at hr; exact absurd hr (by simp)
    · rw [h] at hb; exact absurd hb (by simp)

/-- **MIRRefines for let-hoist-app-right-atom (forward)**:
    `.App g (.Let [(v, rhs, false)] body) ⊑ᴹ .Let [(v, rhs, false)] (.App g body)`
    when `g` is an atom and `v ∉ freeVars g`. -/
theorem mirRefines_let_hoist_app_right_atom_fwd (v : VarId) (rhs body g : Expr)
    (hgatom : g.isAtom = true)
    (hfresh : (freeVars g).contains v = false) :
    MIRRefines (.App g (.Let [(v, rhs, false)] body))
               (.Let [(v, rhs, false)] (.App g body)) := by
  refine ⟨fun env hsome =>
    (lowerTotalExpr_let_app_g_isSome env v g rhs body hfresh).mpr
      ((lowerTotalExpr_app_g_let_isSome env v g rhs body).mp hsome), ?_⟩
  intro d k env hlen
  cases hg : lowerTotalExpr env g with
  | none =>
    rw [lowerTotalExpr_app_g_let_eq_none env v g rhs body (.inl hg)]; trivial
  | some t_g =>
    cases hr : lowerTotalExpr env rhs with
    | none =>
      rw [lowerTotalExpr_app_g_let_eq_none env v g rhs body (.inr (.inl hr))]; trivial
    | some t_r =>
      cases hb : lowerTotalExpr (v :: env) body with
      | none =>
        rw [lowerTotalExpr_app_g_let_eq_none env v g rhs body (.inr (.inr hb))]; trivial
      | some t_b =>
          rw [lowerTotalExpr_app_g_let v hg hr hb,
              lowerTotalExpr_let_app_g v hfresh hg hr hb]
          simp only
          intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
          have hgatom_term : isLeafAtomTerm t_g :=
            lowerTotal_atom_isLeafAtom env g t_g hgatom hg
          have hclosed_g : closedAt env.length t_g :=
            lowerTotal_closedAt env _ t_g hg
          have hclosed_r : closedAt env.length t_r :=
            lowerTotal_closedAt env _ t_r hr
          have hclosed_b : closedAt (env.length + 1) t_b := by
            have := lowerTotal_closedAt (v :: env) _ t_b hb
            simpa [List.length_cons] using this
          have hd_eq : d = env.length := hlen.symm
          subst hd_eq
          obtain ⟨v_g₁, v_g₂, hvg_rel, hstep_lhs_any, hstep_rhs_any⟩ :=
            leafAtomValues hgatom_term hclosed_g (k := i)
              (by intro n hn hnd
                  obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv n hn hnd
                  exact ⟨w₁, w₂, hl, hr', valueRefinesK_mono hi _ _ hw⟩)
          have h_steps_lhs :
              steps 6 (State.compute π₁ ρ₁ (.Apply t_g (.Apply (.Lam 0 t_b) t_r))) =
                State.compute (.funV (.VLam t_b ρ₁) :: .funV v_g₁ :: π₁) ρ₁ t_r := by
            show Moist.CEK.step (Moist.CEK.step (Moist.CEK.step (Moist.CEK.step
              (Moist.CEK.step (Moist.CEK.step
                (State.compute π₁ ρ₁ (.Apply t_g (.Apply (.Lam 0 t_b) t_r)))))))) = _
            show Moist.CEK.step (Moist.CEK.step (Moist.CEK.step (Moist.CEK.step
              (Moist.CEK.step (State.compute (.arg (.Apply (.Lam 0 t_b) t_r) ρ₁ :: π₁) ρ₁ t_g))))) = _
            rw [hstep_lhs_any (.arg (.Apply (.Lam 0 t_b) t_r) ρ₁ :: π₁)]
            rfl
          have h_steps_rhs :
              steps 3 (State.compute π₂ ρ₂ (.Apply (.Lam 0 (.Apply
                (renameTerm (shiftRename 1) t_g) t_b)) t_r)) =
                State.compute (.funV (.VLam (.Apply
                  (renameTerm (shiftRename 1) t_g) t_b) ρ₂) :: π₂)
                  ρ₂ t_r := rfl
          apply obsRefinesK_of_steps_left h_steps_lhs
          apply obsRefinesK_of_steps_right h_steps_rhs
          have henv_j : EnvRefinesK j env.length ρ₁ ρ₂ := by
            intro n hn hnd
            obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv n hn hnd
            exact ⟨w₁, w₂, hl, hr', hw⟩
          have hπ_aug : StackRefK ValueRefinesK i
              (.funV (.VLam t_b ρ₁) :: .funV v_g₁ :: π₁)
              (.funV (.VLam (.Apply
                (renameTerm (shiftRename 1) t_g) t_b) ρ₂) :: π₂) := by
            intro j' hj' v₁' v₂' hv'
            have h_lhs_step :
                steps 1 (State.ret (.funV (.VLam t_b ρ₁) :: .funV v_g₁ :: π₁) v₁') =
                  State.compute (.funV v_g₁ :: π₁) (ρ₁.extend v₁') t_b := rfl
            apply obsRefinesK_of_steps_left h_lhs_step
            have hshift_step :
                Moist.CEK.step (.compute (.arg t_b (ρ₂.extend v₂') :: π₂) (ρ₂.extend v₂')
                  (renameTerm (shiftRename 1) t_g)) =
                  .ret (.arg t_b (ρ₂.extend v₂') :: π₂) v_g₂ := by
              have hempty_step : Moist.CEK.step (.compute [] ρ₂ t_g) = .ret [] v_g₂ :=
                hstep_rhs_any []
              exact leafAtom_shift_step hgatom_term hclosed_g v₂' v_g₂
                hempty_step (.arg t_b (ρ₂.extend v₂') :: π₂)
            have h_rhs_step :
                steps 4 (State.ret (.funV (.VLam (.Apply
                  (renameTerm (shiftRename 1) t_g) t_b) ρ₂) :: π₂) v₂') =
                  State.compute (.funV v_g₂ :: π₂) (ρ₂.extend v₂') t_b := by
              show Moist.CEK.step (Moist.CEK.step (Moist.CEK.step (Moist.CEK.step
                (State.ret (.funV (.VLam (.Apply
                  (renameTerm (shiftRename 1) t_g) t_b) ρ₂) :: π₂) v₂')))) = _
              show Moist.CEK.step (Moist.CEK.step
                (State.compute (.arg t_b (ρ₂.extend v₂') :: π₂) (ρ₂.extend v₂')
                  (renameTerm (shiftRename 1) t_g))) = _
              rw [hshift_step]
              rfl
            apply obsRefinesK_of_steps_right h_rhs_step
            have henv_ij : EnvRefinesK j' env.length ρ₁ ρ₂ := by
              intro n hn hnd
              obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv n hn hnd
              exact ⟨w₁, w₂, hl, hr', valueRefinesK_mono (Nat.le_trans hj' hi) _ _ hw⟩
            have henv_ext : EnvRefinesK j' (env.length + 1) (ρ₁.extend v₁') (ρ₂.extend v₂') :=
              envRefinesK_extend henv_ij hv'
            have hvg_rel' : ValueRefinesK j' v_g₁ v_g₂ :=
              valueRefinesK_mono hj' _ _ hvg_rel
            have hπ_j' : StackRefK ValueRefinesK j' π₁ π₂ := stackRefK_mono hj' hπ
            have hπ_funV : StackRefK ValueRefinesK j' (.funV v_g₁ :: π₁) (.funV v_g₂ :: π₂) :=
              stackRefK_funV_top_aug hvg_rel' hπ_j'
            exact ftlr (env.length + 1) t_b hclosed_b j' j' (Nat.le_refl _)
              (ρ₁.extend v₁') (ρ₂.extend v₂') henv_ext j' (Nat.le_refl _) _ _ hπ_funV
          exact ftlr env.length t_r hclosed_r j j (Nat.le_refl _) ρ₁ ρ₂ henv_j i hi _ _ hπ_aug

/-- **MIRRefines for let-hoist-app-right-atom (backward)**: symmetric. -/
theorem mirRefines_let_hoist_app_right_atom_bwd (v : VarId) (rhs body g : Expr)
    (hgatom : g.isAtom = true)
    (hfresh : (freeVars g).contains v = false) :
    MIRRefines (.Let [(v, rhs, false)] (.App g body))
               (.App g (.Let [(v, rhs, false)] body)) := by
  refine ⟨fun env hsome =>
    (lowerTotalExpr_app_g_let_isSome env v g rhs body).mpr
      ((lowerTotalExpr_let_app_g_isSome env v g rhs body hfresh).mp hsome), ?_⟩
  intro d k env hlen
  cases hg : lowerTotalExpr env g with
  | none =>
    rw [lowerTotalExpr_let_app_g_eq_none env v g rhs body hfresh (.inl hg)]; trivial
  | some t_g =>
    cases hr : lowerTotalExpr env rhs with
    | none =>
      rw [lowerTotalExpr_let_app_g_eq_none env v g rhs body hfresh (.inr (.inl hr))]; trivial
    | some t_r =>
      cases hb : lowerTotalExpr (v :: env) body with
      | none =>
        rw [lowerTotalExpr_let_app_g_eq_none env v g rhs body hfresh (.inr (.inr hb))]; trivial
      | some t_b =>
          rw [lowerTotalExpr_let_app_g v hfresh hg hr hb,
              lowerTotalExpr_app_g_let v hg hr hb]
          simp only
          intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
          have hgatom_term : isLeafAtomTerm t_g :=
            lowerTotal_atom_isLeafAtom env g t_g hgatom hg
          have hclosed_g : closedAt env.length t_g :=
            lowerTotal_closedAt env _ t_g hg
          have hclosed_r : closedAt env.length t_r :=
            lowerTotal_closedAt env _ t_r hr
          have hclosed_b : closedAt (env.length + 1) t_b := by
            have := lowerTotal_closedAt (v :: env) _ t_b hb
            simpa [List.length_cons] using this
          have hd_eq : d = env.length := hlen.symm
          subst hd_eq
          obtain ⟨v_g₁, v_g₂, hvg_rel, hstep_lhs_any, hstep_rhs_any⟩ :=
            leafAtomValues hgatom_term hclosed_g (k := i)
              (by intro n hn hnd
                  obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv n hn hnd
                  exact ⟨w₁, w₂, hl, hr', valueRefinesK_mono hi _ _ hw⟩)
          have h_steps_lhs :
              steps 3 (State.compute π₁ ρ₁ (.Apply (.Lam 0 (.Apply
                (renameTerm (shiftRename 1) t_g) t_b)) t_r)) =
                State.compute (.funV (.VLam (.Apply
                  (renameTerm (shiftRename 1) t_g) t_b) ρ₁) :: π₁)
                  ρ₁ t_r := rfl
          have h_steps_rhs :
              steps 6 (State.compute π₂ ρ₂ (.Apply t_g (.Apply (.Lam 0 t_b) t_r))) =
                State.compute (.funV (.VLam t_b ρ₂) :: .funV v_g₂ :: π₂) ρ₂ t_r := by
            show Moist.CEK.step (Moist.CEK.step (Moist.CEK.step (Moist.CEK.step
              (Moist.CEK.step (Moist.CEK.step
                (State.compute π₂ ρ₂ (.Apply t_g (.Apply (.Lam 0 t_b) t_r)))))))) = _
            show Moist.CEK.step (Moist.CEK.step (Moist.CEK.step (Moist.CEK.step
              (Moist.CEK.step (State.compute (.arg (.Apply (.Lam 0 t_b) t_r) ρ₂ :: π₂) ρ₂ t_g))))) = _
            rw [hstep_rhs_any (.arg (.Apply (.Lam 0 t_b) t_r) ρ₂ :: π₂)]
            rfl
          apply obsRefinesK_of_steps_left h_steps_lhs
          apply obsRefinesK_of_steps_right h_steps_rhs
          have henv_j : EnvRefinesK j env.length ρ₁ ρ₂ := by
            intro n hn hnd
            obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv n hn hnd
            exact ⟨w₁, w₂, hl, hr', hw⟩
          have hπ_aug : StackRefK ValueRefinesK i
              (.funV (.VLam (.Apply
                (renameTerm (shiftRename 1) t_g) t_b) ρ₁) :: π₁)
              (.funV (.VLam t_b ρ₂) :: .funV v_g₂ :: π₂) := by
            intro j' hj' v₁' v₂' hv'
            have hshift_step :
                Moist.CEK.step (.compute (.arg t_b (ρ₁.extend v₁') :: π₁) (ρ₁.extend v₁')
                  (renameTerm (shiftRename 1) t_g)) =
                  .ret (.arg t_b (ρ₁.extend v₁') :: π₁) v_g₁ := by
              have hempty_step : Moist.CEK.step (.compute [] ρ₁ t_g) = .ret [] v_g₁ :=
                hstep_lhs_any []
              exact leafAtom_shift_step hgatom_term hclosed_g v₁' v_g₁
                hempty_step (.arg t_b (ρ₁.extend v₁') :: π₁)
            have h_lhs_step :
                steps 4 (State.ret (.funV (.VLam (.Apply
                  (renameTerm (shiftRename 1) t_g) t_b) ρ₁) :: π₁) v₁') =
                  State.compute (.funV v_g₁ :: π₁) (ρ₁.extend v₁') t_b := by
              show Moist.CEK.step (Moist.CEK.step (Moist.CEK.step (Moist.CEK.step
                (State.ret (.funV (.VLam (.Apply
                  (renameTerm (shiftRename 1) t_g) t_b) ρ₁) :: π₁) v₁')))) = _
              show Moist.CEK.step (Moist.CEK.step
                (State.compute (.arg t_b (ρ₁.extend v₁') :: π₁) (ρ₁.extend v₁')
                  (renameTerm (shiftRename 1) t_g))) = _
              rw [hshift_step]
              rfl
            apply obsRefinesK_of_steps_left h_lhs_step
            have h_rhs_step :
                steps 1 (State.ret (.funV (.VLam t_b ρ₂) :: .funV v_g₂ :: π₂) v₂') =
                  State.compute (.funV v_g₂ :: π₂) (ρ₂.extend v₂') t_b := rfl
            apply obsRefinesK_of_steps_right h_rhs_step
            have henv_ij : EnvRefinesK j' env.length ρ₁ ρ₂ := by
              intro n hn hnd
              obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv n hn hnd
              exact ⟨w₁, w₂, hl, hr', valueRefinesK_mono (Nat.le_trans hj' hi) _ _ hw⟩
            have henv_ext : EnvRefinesK j' (env.length + 1) (ρ₁.extend v₁') (ρ₂.extend v₂') :=
              envRefinesK_extend henv_ij hv'
            have hvg_rel' : ValueRefinesK j' v_g₁ v_g₂ :=
              valueRefinesK_mono hj' _ _ hvg_rel
            have hπ_j' : StackRefK ValueRefinesK j' π₁ π₂ := stackRefK_mono hj' hπ
            have hπ_funV : StackRefK ValueRefinesK j' (.funV v_g₁ :: π₁) (.funV v_g₂ :: π₂) :=
              stackRefK_funV_top_aug hvg_rel' hπ_j'
            exact ftlr (env.length + 1) t_b hclosed_b j' j' (Nat.le_refl _)
              (ρ₁.extend v₁') (ρ₂.extend v₂') henv_ext j' (Nat.le_refl _) _ _ hπ_funV
          exact ftlr env.length t_r hclosed_r j j (Nat.le_refl _) ρ₁ ρ₂ henv_j i hi _ _ hπ_aug

/-- Closedness preservation for let-hoist-app-right-atom (forward). -/
private theorem let_hoist_app_right_atom_close_pres_fwd (v : VarId) (rhs body g : Expr)
    (hfresh : (freeVars g).contains v = false) :
    ∀ env k t₁ t₂,
      lowerTotalExpr env (.App g (.Let [(v, rhs, false)] body)) = some t₁ →
      lowerTotalExpr env (.Let [(v, rhs, false)] (.App g body)) = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true := by
  intro env k t₁ t₂ h₁ h₂ hc
  have hsome₁ : (lowerTotalExpr env (.App g (.Let [(v, rhs, false)] body))).isSome := by
    rw [h₁]; exact rfl
  obtain ⟨hg_some, hr_some, hb_some⟩ :=
    (lowerTotalExpr_app_g_let_isSome env v g rhs body).mp hsome₁
  cases hg : lowerTotalExpr env g with
  | none => rw [hg] at hg_some; exact absurd hg_some (by simp)
  | some t_g =>
    cases hr : lowerTotalExpr env rhs with
    | none => rw [hr] at hr_some; exact absurd hr_some (by simp)
    | some t_r =>
      cases hb : lowerTotalExpr (v :: env) body with
      | none => rw [hb] at hb_some; exact absurd hb_some (by simp)
      | some t_b =>
        rw [lowerTotalExpr_app_g_let v hg hr hb] at h₁
        rw [lowerTotalExpr_let_app_g v hfresh hg hr hb] at h₂
        cases h₁; cases h₂
        simp only [closedAt, Bool.and_eq_true] at hc ⊢
        obtain ⟨hg_c, ⟨hb_c, hr_c⟩⟩ := hc
        exact ⟨⟨closedAt_renameTerm_shiftRename t_g k 1 (by omega) (by omega) hg_c, hb_c⟩, hr_c⟩

/-- Closedness preservation for let-hoist-app-right-atom (backward). -/
private theorem let_hoist_app_right_atom_close_pres_bwd (v : VarId) (rhs body g : Expr)
    (hfresh : (freeVars g).contains v = false) :
    ∀ env k t₁ t₂,
      lowerTotalExpr env (.Let [(v, rhs, false)] (.App g body)) = some t₁ →
      lowerTotalExpr env (.App g (.Let [(v, rhs, false)] body)) = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true := by
  intro env k t₁ t₂ h₁ h₂ hc
  have hsome₁ : (lowerTotalExpr env (.Let [(v, rhs, false)] (.App g body))).isSome := by
    rw [h₁]; exact rfl
  obtain ⟨hg_some, hr_some, hb_some⟩ :=
    (lowerTotalExpr_let_app_g_isSome env v g rhs body hfresh).mp hsome₁
  cases hg : lowerTotalExpr env g with
  | none => rw [hg] at hg_some; exact absurd hg_some (by simp)
  | some t_g =>
    cases hr : lowerTotalExpr env rhs with
    | none => rw [hr] at hr_some; exact absurd hr_some (by simp)
    | some t_r =>
      cases hb : lowerTotalExpr (v :: env) body with
      | none => rw [hb] at hb_some; exact absurd hb_some (by simp)
      | some t_b =>
        rw [lowerTotalExpr_let_app_g v hfresh hg hr hb] at h₁
        rw [lowerTotalExpr_app_g_let v hg hr hb] at h₂
        cases h₁; cases h₂
        simp only [closedAt, Bool.and_eq_true] at hc ⊢
        obtain ⟨⟨hshg_c, hb_c⟩, hr_c⟩ := hc
        have hg_c : closedAt k t_g = true :=
          closedAt_renameTerm_shiftRename_inv t_g k 1 (by omega) (by omega) hshg_c
        exact ⟨hg_c, hb_c, hr_c⟩

theorem mirCtxRefines_let_hoist_app_right_atom_fwd (v : VarId) (rhs body g : Expr)
    (hgatom : g.isAtom = true)
    (hfresh : (freeVars g).contains v = false) :
    MIRCtxRefines (.App g (.Let [(v, rhs, false)] body))
                  (.Let [(v, rhs, false)] (.App g body)) :=
  mirRefines_to_mirCtxRefines
    (mirRefines_let_hoist_app_right_atom_fwd v rhs body g hgatom hfresh)
    (let_hoist_app_right_atom_close_pres_fwd v rhs body g hfresh)

theorem mirCtxRefines_let_hoist_app_right_atom_bwd (v : VarId) (rhs body g : Expr)
    (hgatom : g.isAtom = true)
    (hfresh : (freeVars g).contains v = false) :
    MIRCtxRefines (.Let [(v, rhs, false)] (.App g body))
                  (.App g (.Let [(v, rhs, false)] body)) :=
  mirRefines_to_mirCtxRefines
    (mirRefines_let_hoist_app_right_atom_bwd v rhs body g hgatom hfresh)
    (let_hoist_app_right_atom_close_pres_bwd v rhs body g hfresh)
end Moist.Verified.MIR
