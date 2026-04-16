import Moist.Verified.MIR.Primitives.Shared
import Moist.Verified.MIR.Primitives.LetFlattenBody

namespace Moist.Verified.MIR

open Moist.CEK
open Moist.Plutus.Term (Term)
open Moist.MIR
  (Expr VarId anfNormalizeCore anfNormalizeListCore anfNormalizeBindsCore anfAtom anfAtomList
   wrapLet flattenLetBody freeVars lowerTotalExpr lowerTotal lowerTotalLet expandFix
   expandFixBinds expandFixBinds_freeVars_not_contains flattenLetBinds flattenLetBindsStep
   freeVarsLet lowerTotalLet_prepend_unused_gen lowerTotalLet_prepend_unused_none_gen maxUidExpr
   maxUidExprBinds maxUidExprBinds_append VarSet)
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

/-! ## Section 4c-pre. Let-cons split helpers

`.Let (b :: rest) body` is definitionally equivalent to
`.Let [b] (.Let rest body)` at the Term level (both lower via
`lowerTotalLet` identically). Needed by the iterated let-flatten-rhs-head
helpers below. -/

theorem mirCtxRefines_let_cons_split_fwd
    (b : VarId × Expr × Bool) (rest : List (VarId × Expr × Bool)) (body : Expr) :
    MIRCtxRefines (.Let (b :: rest) body) (.Let [b] (.Let rest body)) := by
  intro env
  obtain ⟨v, rhs, er⟩ := b
  have hlow_eq :
      lowerTotalExpr env (.Let ((v, rhs, er) :: rest) body) =
      lowerTotalExpr env (.Let [(v, rhs, er)] (.Let rest body)) := by
    simp only [lowerTotalExpr, expandFix, expandFixBinds,
      lowerTotal, lowerTotalLet]
  rw [hlow_eq]
  refine ⟨id, ?_⟩
  cases h : lowerTotalExpr env (.Let [(v, rhs, er)] (.Let rest body)) with
  | none => trivial
  | some t => exact ctxRefines_refl t

theorem mirCtxRefines_let_cons_split_bwd
    (b : VarId × Expr × Bool) (rest : List (VarId × Expr × Bool)) (body : Expr) :
    MIRCtxRefines (.Let [b] (.Let rest body)) (.Let (b :: rest) body) := by
  intro env
  obtain ⟨v, rhs, er⟩ := b
  have hlow_eq :
      lowerTotalExpr env (.Let ((v, rhs, er) :: rest) body) =
      lowerTotalExpr env (.Let [(v, rhs, er)] (.Let rest body)) := by
    simp only [lowerTotalExpr, expandFix, expandFixBinds,
      lowerTotal, lowerTotalLet]
  rw [← hlow_eq]
  refine ⟨id, ?_⟩
  cases h : lowerTotalExpr env (.Let ((v, rhs, er) :: rest) body) with
  | none => trivial
  | some t => exact ctxRefines_refl t

/-! ## Section 4c. Let-flatten-rhs-head primitive

`.Let ((x, .Let innerBinds innerBody, er) :: rest) body
 ≈ .Let (innerBinds ++ [(x, innerBody, er)] ++ rest) body`

This primitive hoists a nested `.Let` out of a binding's RHS position,
placing its inner bindings directly in the outer bind list. Needed to
prove soundness of `flattenLetBinds`. The single-binding case requires
a `shiftRename 2` argument (the inner binding `y` adds one de Bruijn
slot between the outer binding `x` and the original env), with the
side condition that `y` is fresh in both `rest` and `body`. -/

/-- Empty-innerBinds let-flatten-rhs-head: `.Let ((x, .Let [] innerBody, er) :: rest) body`
    is definitionally equal to `.Let ((x, innerBody, er) :: rest) body` at the Term level. -/
private theorem lowerTotalExpr_let_flatten_rhs_head_nil
    (x : VarId) (innerBody : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) (env : List VarId) :
    lowerTotalExpr env (.Let ((x, .Let [] innerBody, er) :: rest) body) =
      lowerTotalExpr env (.Let ((x, innerBody, er) :: rest) body) := by
  show lowerTotal env (expandFix _) = lowerTotal env (expandFix _)
  simp only [expandFix, expandFixBinds, lowerTotal,
             lowerTotalLet]

theorem mirRefines_let_flatten_rhs_head_nil_fwd
    (x : VarId) (innerBody : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) :
    MIRRefines (.Let ((x, .Let [] innerBody, er) :: rest) body)
               (.Let ((x, innerBody, er) :: rest) body) := by
  refine ⟨?_, ?_⟩
  · intro env hsome
    rw [lowerTotalExpr_let_flatten_rhs_head_nil x innerBody er rest body env] at hsome
    exact hsome
  · intro d k env hlen
    rw [lowerTotalExpr_let_flatten_rhs_head_nil x innerBody er rest body env]
    cases h : lowerTotalExpr env (.Let ((x, innerBody, er) :: rest) body) with
    | none => simp
    | some t =>
      simp only
      intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
      have hclosed : closedAt env.length t :=
        lowerTotal_closedAt env _ t h
      have hd_eq : d = env.length := hlen.symm
      subst hd_eq
      exact ftlr env.length t hclosed j j (Nat.le_refl _) ρ₁ ρ₂ henv i hi π₁ π₂ hπ

theorem mirRefines_let_flatten_rhs_head_nil_bwd
    (x : VarId) (innerBody : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) :
    MIRRefines (.Let ((x, innerBody, er) :: rest) body)
               (.Let ((x, .Let [] innerBody, er) :: rest) body) := by
  refine ⟨?_, ?_⟩
  · intro env hsome
    rw [← lowerTotalExpr_let_flatten_rhs_head_nil x innerBody er rest body env] at hsome
    exact hsome
  · intro d k env hlen
    rw [← lowerTotalExpr_let_flatten_rhs_head_nil x innerBody er rest body env]
    cases h : lowerTotalExpr env (.Let ((x, .Let [] innerBody, er) :: rest) body) with
    | none => simp
    | some t =>
      simp only
      intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
      have hclosed : closedAt env.length t :=
        lowerTotal_closedAt env _ t h
      have hd_eq : d = env.length := hlen.symm
      subst hd_eq
      exact ftlr env.length t hclosed j j (Nat.le_refl _) ρ₁ ρ₂ henv i hi π₁ π₂ hπ

private theorem let_flatten_rhs_head_nil_close_pres
    (x : VarId) (innerBody : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) :
    ∀ env k t₁ t₂,
      lowerTotalExpr env (.Let ((x, .Let [] innerBody, er) :: rest) body) = some t₁ →
      lowerTotalExpr env (.Let ((x, innerBody, er) :: rest) body) = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true := by
  intro env k t₁ t₂ h₁ h₂ hc
  rw [lowerTotalExpr_let_flatten_rhs_head_nil x innerBody er rest body env, h₂] at h₁
  cases h₁
  exact hc

private theorem let_flatten_rhs_head_nil_close_pres_bwd
    (x : VarId) (innerBody : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) :
    ∀ env k t₁ t₂,
      lowerTotalExpr env (.Let ((x, innerBody, er) :: rest) body) = some t₁ →
      lowerTotalExpr env (.Let ((x, .Let [] innerBody, er) :: rest) body) = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true := by
  intro env k t₁ t₂ h₁ h₂ hc
  rw [← lowerTotalExpr_let_flatten_rhs_head_nil x innerBody er rest body env, h₂] at h₁
  cases h₁
  exact hc

theorem mirCtxRefines_let_flatten_rhs_head_nil_fwd
    (x : VarId) (innerBody : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) :
    MIRCtxRefines (.Let ((x, .Let [] innerBody, er) :: rest) body)
                  (.Let ((x, innerBody, er) :: rest) body) :=
  mirRefines_to_mirCtxRefines
    (mirRefines_let_flatten_rhs_head_nil_fwd x innerBody er rest body)
    (let_flatten_rhs_head_nil_close_pres x innerBody er rest body)

theorem mirCtxRefines_let_flatten_rhs_head_nil_bwd
    (x : VarId) (innerBody : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) :
    MIRCtxRefines (.Let ((x, innerBody, er) :: rest) body)
                  (.Let ((x, .Let [] innerBody, er) :: rest) body) :=
  mirRefines_to_mirCtxRefines
    (mirRefines_let_flatten_rhs_head_nil_bwd x innerBody er rest body)
    (let_flatten_rhs_head_nil_close_pres_bwd x innerBody er rest body)

/-! ### Single-binding let-flatten-rhs-head primitive -/

/-- Freshness propagation: if `y` is not free in each RHS of `rest` and not
    free in `body`, then `y` is not free in `freeVarsLet rest body`. -/
private theorem freeVarsLet_not_contains_of_fresh
    (rest : List (VarId × Expr × Bool)) (body : Expr) (y : VarId)
    (hy_fresh_rest : ∀ r ∈ rest, (freeVars r.2.1).contains y = false)
    (hy_fresh_body : (freeVars body).contains y = false) :
    (freeVarsLet rest body).contains y = false := by
  induction rest with
  | nil =>
    rw [freeVarsLet]
    exact hy_fresh_body
  | cons r rest' ih =>
    obtain ⟨z, rhs_z, erz⟩ := r
    rw [freeVarsLet]
    apply VarSet.union_not_contains_fwd
    · exact hy_fresh_rest (z, rhs_z, erz) (List.Mem.head _)
    · apply VarSet.erase_not_contains_fwd
      exact ih (fun r hr => hy_fresh_rest r (List.Mem.tail _ hr))

/-- `expandFix` variant of the freshness propagation helper. -/
private theorem freeVarsLet_expandFix_not_contains_of_fresh
    (rest : List (VarId × Expr × Bool)) (body : Expr) (y : VarId)
    (hy_fresh_rest : ∀ r ∈ rest, (freeVars r.2.1).contains y = false)
    (hy_fresh_body : (freeVars body).contains y = false) :
    (freeVarsLet (expandFixBinds rest)
      (expandFix body)).contains y = false :=
  expandFixBinds_freeVars_not_contains rest body y
    (freeVarsLet_not_contains_of_fresh rest body y hy_fresh_rest hy_fresh_body)

/-- Shape lemma for the LHS of the single-binding flatten primitive. -/
private theorem lowerTotalExpr_let_flatten_rhs_head_single_lhs
    {env : List VarId} (x y : VarId) (e_y : Expr) (er_y : Bool)
    (innerBody : Expr) (er : Bool) (rest : List (VarId × Expr × Bool))
    (body : Expr) {t_ey t_iB t_rest : Term}
    (hey : lowerTotalExpr env e_y = some t_ey)
    (hiB : lowerTotalExpr (y :: env) innerBody = some t_iB)
    (hrest : lowerTotalLet (x :: env) (expandFixBinds rest)
              (expandFix body) = some t_rest) :
    lowerTotalExpr env (.Let ((x, .Let [(y, e_y, er_y)] innerBody, er) :: rest) body) =
      some (.Apply (.Lam 0 t_rest) (.Apply (.Lam 0 t_iB) t_ey)) := by
  have hey' : lowerTotal env (expandFix e_y) = some t_ey := hey
  have hiB' : lowerTotal (y :: env) (expandFix innerBody) = some t_iB := hiB
  show lowerTotal env (expandFix
      (.Let ((x, .Let [(y, e_y, er_y)] innerBody, er) :: rest) body)) =
    some (.Apply (.Lam 0 t_rest) (.Apply (.Lam 0 t_iB) t_ey))
  simp only [expandFix, expandFixBinds, lowerTotal,
             lowerTotalLet, Option.bind_eq_bind, Option.bind_some,
             hey', hiB', hrest]

/-- Shape lemma for the RHS of the single-binding flatten primitive.
    Uses `lowerTotalLet_prepend_unused_gen` to shift `t_rest` by `shiftRename 2`. -/
private theorem lowerTotalExpr_let_flatten_rhs_head_single_rhs
    {env : List VarId} (x y : VarId) (e_y : Expr) (er_y : Bool)
    (innerBody : Expr) (er : Bool) (rest : List (VarId × Expr × Bool))
    (body : Expr)
    (hy_fresh_rest : ∀ r ∈ rest, (freeVars r.2.1).contains y = false)
    (hy_fresh_body : (freeVars body).contains y = false)
    {t_ey t_iB t_rest : Term}
    (hey : lowerTotalExpr env e_y = some t_ey)
    (hiB : lowerTotalExpr (y :: env) innerBody = some t_iB)
    (hrest : lowerTotalLet (x :: env) (expandFixBinds rest)
              (expandFix body) = some t_rest) :
    lowerTotalExpr env (.Let ((y, e_y, er_y) :: (x, innerBody, er) :: rest) body) =
      some (.Apply (.Lam 0 (.Apply (.Lam 0
        (renameTerm (shiftRename 2) t_rest)) t_iB)) t_ey) := by
  have hey' : lowerTotal env (expandFix e_y) = some t_ey := hey
  have hiB' : lowerTotal (y :: env) (expandFix innerBody) = some t_iB := hiB
  have hfresh_exp : (freeVarsLet (expandFixBinds rest)
      (expandFix body)).contains y = false :=
    freeVarsLet_expandFix_not_contains_of_fresh rest body y hy_fresh_rest hy_fresh_body
  have hrest_shift : lowerTotalLet (x :: y :: env)
      (expandFixBinds rest) (expandFix body) =
        some (renameTerm
          (shiftRename 2) t_rest) := by
    have h := lowerTotalLet_prepend_unused_gen [x] env y
      (expandFixBinds rest) (expandFix body)
      (.inl hfresh_exp) t_rest hrest
    simpa using h
  show lowerTotal env (expandFix
      (.Let ((y, e_y, er_y) :: (x, innerBody, er) :: rest) body)) =
    some (.Apply (.Lam 0 (.Apply (.Lam 0
      (renameTerm (shiftRename 2) t_rest)) t_iB)) t_ey)
  simp only [expandFix, expandFixBinds, lowerTotal,
             lowerTotalLet, Option.bind_eq_bind, Option.bind_some,
             hey', hiB', hrest_shift]

/-- isSome characterization of the LHS. -/
private theorem lowerTotalExpr_let_flatten_rhs_head_single_lhs_isSome
    (env : List VarId) (x y : VarId) (e_y : Expr) (er_y : Bool)
    (innerBody : Expr) (er : Bool) (rest : List (VarId × Expr × Bool))
    (body : Expr) :
    (lowerTotalExpr env
      (.Let ((x, .Let [(y, e_y, er_y)] innerBody, er) :: rest) body)).isSome ↔
      (lowerTotalExpr env e_y).isSome ∧
      (lowerTotalExpr (y :: env) innerBody).isSome ∧
      (lowerTotalLet (x :: env) (expandFixBinds rest)
        (expandFix body)).isSome := by
  constructor
  · intro hsome
    have h : (lowerTotal env (expandFix
        (.Let ((x, .Let [(y, e_y, er_y)] innerBody, er) :: rest) body))).isSome := hsome
    simp only [expandFix, expandFixBinds, lowerTotal,
               lowerTotalLet, Option.bind_eq_bind] at h
    cases hey : lowerTotal env (expandFix e_y) with
    | none => rw [hey] at h; simp at h
    | some t_ey =>
      rw [hey] at h
      simp only [Option.bind_some] at h
      cases hiB : lowerTotal (y :: env) (expandFix innerBody) with
      | none => rw [hiB] at h; simp at h
      | some t_iB =>
        rw [hiB] at h
        simp only [Option.bind_some] at h
        cases hrest : lowerTotalLet (x :: env)
            (expandFixBinds rest) (expandFix body) with
        | none => rw [hrest] at h; simp at h
        | some t_rest =>
          refine ⟨?_, ?_, ?_⟩
          · show (lowerTotal env (expandFix e_y)).isSome = true
            rw [hey]; rfl
          · show (lowerTotal (y :: env) (expandFix innerBody)).isSome = true
            rw [hiB]; rfl
          · rfl
  · rintro ⟨hey, hiB, hrest⟩
    cases hey' : lowerTotalExpr env e_y with
    | none => rw [hey'] at hey; exact absurd hey (by simp)
    | some t_ey =>
      cases hiB' : lowerTotalExpr (y :: env) innerBody with
      | none => rw [hiB'] at hiB; exact absurd hiB (by simp)
      | some t_iB =>
        cases hrest' : lowerTotalLet (x :: env)
            (expandFixBinds rest) (expandFix body) with
        | none => rw [hrest'] at hrest; exact absurd hrest (by simp)
        | some t_rest =>
          rw [lowerTotalExpr_let_flatten_rhs_head_single_lhs x y e_y er_y innerBody er
            rest body hey' hiB' hrest']
          rfl

/-- isSome characterization of the RHS. -/
private theorem lowerTotalExpr_let_flatten_rhs_head_single_rhs_isSome
    (env : List VarId) (x y : VarId) (e_y : Expr) (er_y : Bool)
    (innerBody : Expr) (er : Bool) (rest : List (VarId × Expr × Bool))
    (body : Expr)
    (hy_fresh_rest : ∀ r ∈ rest, (freeVars r.2.1).contains y = false)
    (hy_fresh_body : (freeVars body).contains y = false) :
    (lowerTotalExpr env
      (.Let ((y, e_y, er_y) :: (x, innerBody, er) :: rest) body)).isSome ↔
      (lowerTotalExpr env e_y).isSome ∧
      (lowerTotalExpr (y :: env) innerBody).isSome ∧
      (lowerTotalLet (x :: env) (expandFixBinds rest)
        (expandFix body)).isSome := by
  have hfresh_exp : (freeVarsLet (expandFixBinds rest)
      (expandFix body)).contains y = false :=
    freeVarsLet_expandFix_not_contains_of_fresh rest body y hy_fresh_rest hy_fresh_body
  constructor
  · intro hsome
    have h : (lowerTotal env (expandFix
        (.Let ((y, e_y, er_y) :: (x, innerBody, er) :: rest) body))).isSome := hsome
    simp only [expandFix, expandFixBinds, lowerTotal,
               lowerTotalLet, Option.bind_eq_bind] at h
    cases hey : lowerTotal env (expandFix e_y) with
    | none => rw [hey] at h; simp at h
    | some t_ey =>
      rw [hey] at h
      simp only [Option.bind_some] at h
      cases hiB : lowerTotal (y :: env) (expandFix innerBody) with
      | none => rw [hiB] at h; simp at h
      | some t_iB =>
        rw [hiB] at h
        simp only [Option.bind_some] at h
        cases hrest_shift : lowerTotalLet (x :: y :: env)
            (expandFixBinds rest) (expandFix body) with
        | none => rw [hrest_shift] at h; simp at h
        | some t_rest_shift =>
          cases hrest : lowerTotalLet (x :: env)
              (expandFixBinds rest) (expandFix body) with
          | none =>
            have h_none := lowerTotalLet_prepend_unused_none_gen [x] env y
              (expandFixBinds rest) (expandFix body)
              (.inl hfresh_exp) hrest
            have h_none' : lowerTotalLet (x :: y :: env)
                (expandFixBinds rest) (expandFix body) = none := h_none
            rw [h_none'] at hrest_shift; exact absurd hrest_shift (by simp)
          | some t_rest =>
            refine ⟨?_, ?_, ?_⟩
            · show (lowerTotal env (expandFix e_y)).isSome = true
              rw [hey]; rfl
            · show (lowerTotal (y :: env) (expandFix innerBody)).isSome = true
              rw [hiB]; rfl
            · rfl
  · rintro ⟨hey, hiB, hrest⟩
    cases hey' : lowerTotalExpr env e_y with
    | none => rw [hey'] at hey; exact absurd hey (by simp)
    | some t_ey =>
      cases hiB' : lowerTotalExpr (y :: env) innerBody with
      | none => rw [hiB'] at hiB; exact absurd hiB (by simp)
      | some t_iB =>
        cases hrest' : lowerTotalLet (x :: env)
            (expandFixBinds rest) (expandFix body) with
        | none => rw [hrest'] at hrest; exact absurd hrest (by simp)
        | some t_rest =>
          rw [lowerTotalExpr_let_flatten_rhs_head_single_rhs x y e_y er_y innerBody er
            rest body hy_fresh_rest hy_fresh_body hey' hiB' hrest']
          rfl

/-- Helper: build `RenameEnvRefR (shiftRename 2)`-related env pair after the
    LHS is extended once and the RHS is extended twice. -/
private theorem renameEnvRefR_shift2_extend
    {k d : Nat} {ρ₁ ρ₂ : CekEnv} {u₁ u₂ v₂ : Moist.CEK.CekValue}
    (henv : EnvRefinesK k d ρ₁ ρ₂) (hu : ValueRefinesK k u₁ u₂) :
    Moist.Verified.FundamentalRefines.RenameEnvRefR
      (shiftRename 2) k (d + 1)
      (ρ₁.extend u₁) ((ρ₂.extend v₂).extend u₂) := by
  intro n hn hnd
  show match (ρ₁.extend u₁).lookup n,
             ((ρ₂.extend v₂).extend u₂).lookup (shiftRename 2 n) with
       | some v₁', some v₂' => ValueRefinesK k v₁' v₂'
       | none, none => True
       | _, _ => False
  by_cases hn1 : n = 1
  · subst hn1
    have hsr : shiftRename 2 1 = 1 := by
      show (if 1 ≥ 2 then 1 + 1 else 1) = 1
      simp
    rw [hsr]
    have h1 : (ρ₁.extend u₁).lookup 1 = some u₁ := by
      show (Moist.CEK.CekEnv.cons u₁ ρ₁).lookup 1 = some u₁; rfl
    have h2 : ((ρ₂.extend v₂).extend u₂).lookup 1 = some u₂ := by
      show (Moist.CEK.CekEnv.cons u₂ (ρ₂.extend v₂)).lookup 1 = some u₂; rfl
    rw [h1, h2]
    exact hu
  · have hn2 : n ≥ 2 := by omega
    have hsr : shiftRename 2 n = n + 1 := by
      show (if n ≥ 2 then n + 1 else n) = n + 1
      simp [hn2]
    rw [hsr]
    have hn1' : n - 1 ≥ 1 := by omega
    have hnd' : n - 1 ≤ d := by omega
    match n, hn2 with
    | m + 2, _ =>
      show match (Moist.CEK.CekEnv.cons u₁ ρ₁).lookup (m + 2),
                 (Moist.CEK.CekEnv.cons u₂ (ρ₂.extend v₂)).lookup (m + 2 + 1) with
           | some v₁', some v₂' => ValueRefinesK k v₁' v₂'
           | none, none => True
           | _, _ => False
      have h_lhs : (Moist.CEK.CekEnv.cons u₁ ρ₁).lookup (m + 2) = ρ₁.lookup (m + 1) := rfl
      have h_rhs : (Moist.CEK.CekEnv.cons u₂ (ρ₂.extend v₂)).lookup (m + 2 + 1) =
          ρ₂.lookup (m + 1) := by
        show (ρ₂.extend v₂).lookup (m + 2) = ρ₂.lookup (m + 1)
        show (Moist.CEK.CekEnv.cons v₂ ρ₂).lookup (m + 2) = ρ₂.lookup (m + 1)
        rfl
      rw [h_lhs, h_rhs]
      have hm1 : m + 1 ≥ 1 := by omega
      have hmd : m + 1 ≤ d := by
        have : m + 2 ≤ d + 1 := hnd
        omega
      obtain ⟨w₁, w₂, hl, hrg, hrel⟩ := henv (m + 1) hm1 hmd
      rw [hl, hrg]
      exact hrel

/-- Is0Preserving for `shiftRename 2`. -/
private theorem is0preserving_shiftRename2 :
    Is0Preserving (shiftRename 2) :=
  is0preserving_shiftRename (by omega)

theorem mirRefines_let_flatten_rhs_head_single_fwd
    (x : VarId) (y : VarId) (e_y : Expr) (er_y : Bool) (innerBody : Expr)
    (er : Bool) (rest : List (VarId × Expr × Bool)) (body : Expr)
    (hy_fresh_rest : ∀ r ∈ rest, (freeVars r.2.1).contains y = false)
    (hy_fresh_body : (freeVars body).contains y = false) :
    MIRRefines (.Let ((x, .Let [(y, e_y, er_y)] innerBody, er) :: rest) body)
               (.Let ((y, e_y, er_y) :: (x, innerBody, er) :: rest) body) := by
  refine ⟨?_, ?_⟩
  · intro env hsome
    have h := (lowerTotalExpr_let_flatten_rhs_head_single_lhs_isSome env x y e_y er_y
      innerBody er rest body).mp hsome
    exact (lowerTotalExpr_let_flatten_rhs_head_single_rhs_isSome env x y e_y er_y
      innerBody er rest body hy_fresh_rest hy_fresh_body).mpr h
  · intro d k env hlen
    cases hey : lowerTotalExpr env e_y with
    | none =>
      have h_lhs : lowerTotalExpr env
          (.Let ((x, .Let [(y, e_y, er_y)] innerBody, er) :: rest) body) = none := by
        cases h : lowerTotalExpr env
            (.Let ((x, .Let [(y, e_y, er_y)] innerBody, er) :: rest) body) with
        | none => rfl
        | some _ =>
          have hsome : (lowerTotalExpr env
              (.Let ((x, .Let [(y, e_y, er_y)] innerBody, er) :: rest) body)).isSome := by
            rw [h]; rfl
          have := (lowerTotalExpr_let_flatten_rhs_head_single_lhs_isSome env x y e_y
            er_y innerBody er rest body).mp hsome
          rw [hey] at this; exact absurd this.1 (by simp)
      rw [h_lhs]; trivial
    | some t_ey =>
      cases hiB : lowerTotalExpr (y :: env) innerBody with
      | none =>
        have h_lhs : lowerTotalExpr env
            (.Let ((x, .Let [(y, e_y, er_y)] innerBody, er) :: rest) body) = none := by
          cases h : lowerTotalExpr env
              (.Let ((x, .Let [(y, e_y, er_y)] innerBody, er) :: rest) body) with
          | none => rfl
          | some _ =>
            have hsome : (lowerTotalExpr env
                (.Let ((x, .Let [(y, e_y, er_y)] innerBody, er) :: rest) body)).isSome := by
              rw [h]; rfl
            have := (lowerTotalExpr_let_flatten_rhs_head_single_lhs_isSome env x y e_y
              er_y innerBody er rest body).mp hsome
            rw [hiB] at this; exact absurd this.2.1 (by simp)
        rw [h_lhs]; trivial
      | some t_iB =>
        cases hrest : lowerTotalLet (x :: env) (expandFixBinds rest)
            (expandFix body) with
        | none =>
          have h_lhs : lowerTotalExpr env
              (.Let ((x, .Let [(y, e_y, er_y)] innerBody, er) :: rest) body) = none := by
            cases h : lowerTotalExpr env
                (.Let ((x, .Let [(y, e_y, er_y)] innerBody, er) :: rest) body) with
            | none => rfl
            | some _ =>
              have hsome : (lowerTotalExpr env
                  (.Let ((x, .Let [(y, e_y, er_y)] innerBody, er) :: rest) body)).isSome := by
                rw [h]; rfl
              have := (lowerTotalExpr_let_flatten_rhs_head_single_lhs_isSome env x y e_y
                er_y innerBody er rest body).mp hsome
              rw [hrest] at this; exact absurd this.2.2 (by simp)
          rw [h_lhs]; trivial
        | some t_rest =>
          rw [lowerTotalExpr_let_flatten_rhs_head_single_lhs x y e_y er_y innerBody er
              rest body hey hiB hrest,
            lowerTotalExpr_let_flatten_rhs_head_single_rhs x y e_y er_y innerBody er
              rest body hy_fresh_rest hy_fresh_body hey hiB hrest]
          simp only
          intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
          have h_steps_lhs :
              steps 6 (State.compute π₁ ρ₁
                  (.Apply (.Lam 0 t_rest) (.Apply (.Lam 0 t_iB) t_ey))) =
                State.compute
                  (.funV (.VLam t_iB ρ₁) :: .funV (.VLam t_rest ρ₁) :: π₁) ρ₁ t_ey := rfl
          have h_steps_rhs :
              steps 3 (State.compute π₂ ρ₂
                  (.Apply (.Lam 0 (.Apply (.Lam 0
                    (renameTerm
                      (shiftRename 2) t_rest)) t_iB)) t_ey)) =
                State.compute
                  (.funV (.VLam (.Apply (.Lam 0
                    (renameTerm
                      (shiftRename 2) t_rest)) t_iB) ρ₂) :: π₂) ρ₂ t_ey := rfl
          apply obsRefinesK_of_steps_left h_steps_lhs
          apply obsRefinesK_of_steps_right h_steps_rhs
          have hclosed_ey : closedAt env.length t_ey :=
            lowerTotal_closedAt env _ t_ey hey
          have hclosed_iB : closedAt (env.length + 1) t_iB := by
            have := lowerTotal_closedAt (y :: env) _ t_iB hiB
            simpa [List.length_cons] using this
          have hclosed_rest : closedAt (env.length + 1) t_rest := by
            have := lowerTotalLet_closedAt (x :: env) _ _ t_rest hrest
            simpa [List.length_cons] using this
          have hd_eq : d = env.length := hlen.symm
          subst hd_eq
          have henv_j : EnvRefinesK j env.length ρ₁ ρ₂ := by
            intro n hn hnd
            obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv n hn hnd
            exact ⟨w₁, w₂, hl, hr', hw⟩
          have hπ_aug : StackRefK ValueRefinesK i
              (.funV (.VLam t_iB ρ₁) :: .funV (.VLam t_rest ρ₁) :: π₁)
              (.funV (.VLam (.Apply (.Lam 0
                (renameTerm
                  (shiftRename 2) t_rest)) t_iB) ρ₂) :: π₂) := by
            intro j' hj' v₁ v₂ hv
            have h_lhs_v : steps 1 (State.ret
                (.funV (.VLam t_iB ρ₁) :: .funV (.VLam t_rest ρ₁) :: π₁) v₁) =
                  State.compute (.funV (.VLam t_rest ρ₁) :: π₁) (ρ₁.extend v₁) t_iB := rfl
            have h_rhs_v : steps 4 (State.ret
                (.funV (.VLam (.Apply (.Lam 0
                  (renameTerm
                    (shiftRename 2) t_rest)) t_iB) ρ₂) :: π₂) v₂) =
                  State.compute (.funV (.VLam
                    (renameTerm
                      (shiftRename 2) t_rest) (ρ₂.extend v₂)) :: π₂)
                    (ρ₂.extend v₂) t_iB := rfl
            apply obsRefinesK_of_steps_left h_lhs_v
            apply obsRefinesK_of_steps_right h_rhs_v
            have henv_j' : EnvRefinesK j' env.length ρ₁ ρ₂ := by
              intro n hn hnd
              obtain ⟨w₁, w₂, hl, hrg, hw⟩ := henv_j n hn hnd
              exact ⟨w₁, w₂, hl, hrg, valueRefinesK_mono (by omega) _ _ hw⟩
            have henv_ext : EnvRefinesK j' (env.length + 1)
                (ρ₁.extend v₁) (ρ₂.extend v₂) :=
              envRefinesK_extend henv_j' hv
            have hπ_inner : StackRefK ValueRefinesK j'
                (.funV (.VLam t_rest ρ₁) :: π₁)
                (.funV (.VLam (renameTerm
                  (shiftRename 2) t_rest) (ρ₂.extend v₂)) :: π₂) := by
              intro j'' hj'' u₁ u₂ hu
              have h_lhs_u : steps 1 (State.ret
                  (.funV (.VLam t_rest ρ₁) :: π₁) u₁) =
                    State.compute π₁ (ρ₁.extend u₁) t_rest := rfl
              have h_rhs_u : steps 1 (State.ret
                  (.funV (.VLam (renameTerm
                    (shiftRename 2) t_rest) (ρ₂.extend v₂)) :: π₂) u₂) =
                    State.compute π₂ ((ρ₂.extend v₂).extend u₂)
                      (renameTerm
                        (shiftRename 2) t_rest) := rfl
              apply obsRefinesK_of_steps_left h_lhs_u
              apply obsRefinesK_of_steps_right h_rhs_u
              have henv_j'' : EnvRefinesK j'' env.length ρ₁ ρ₂ := by
                intro n hn hnd
                obtain ⟨w₁, w₂, hl, hrg, hw⟩ := henv_j' n hn hnd
                exact ⟨w₁, w₂, hl, hrg, valueRefinesK_mono (by omega) _ _ hw⟩
              have henv_shift2 : Moist.Verified.FundamentalRefines.RenameEnvRefR
                  (shiftRename 2) j'' (env.length + 1)
                  (ρ₁.extend u₁) ((ρ₂.extend v₂).extend u₂) :=
                renameEnvRefR_shift2_extend henv_j'' hu
              exact Moist.Verified.FundamentalRefines.renameRefinesR
                (shiftRename 2) is0preserving_shiftRename2
                (env.length + 1) t_rest hclosed_rest j''
                j'' (Nat.le_refl _) (ρ₁.extend u₁) ((ρ₂.extend v₂).extend u₂)
                henv_shift2 j'' (Nat.le_refl _) π₁ π₂
                (stackRefK_mono
                  (by omega : j'' ≤ i) hπ)
            exact ftlr (env.length + 1) t_iB hclosed_iB j' j' (Nat.le_refl _)
              (ρ₁.extend v₁) (ρ₂.extend v₂) henv_ext j' (Nat.le_refl _) _ _ hπ_inner
          exact ftlr env.length t_ey hclosed_ey j j (Nat.le_refl _) ρ₁ ρ₂ henv_j i hi
            _ _ hπ_aug

theorem mirRefines_let_flatten_rhs_head_single_bwd
    (x : VarId) (y : VarId) (e_y : Expr) (er_y : Bool) (innerBody : Expr)
    (er : Bool) (rest : List (VarId × Expr × Bool)) (body : Expr)
    (hy_fresh_rest : ∀ r ∈ rest, (freeVars r.2.1).contains y = false)
    (hy_fresh_body : (freeVars body).contains y = false) :
    MIRRefines (.Let ((y, e_y, er_y) :: (x, innerBody, er) :: rest) body)
               (.Let ((x, .Let [(y, e_y, er_y)] innerBody, er) :: rest) body) := by
  refine ⟨?_, ?_⟩
  · intro env hsome
    have h := (lowerTotalExpr_let_flatten_rhs_head_single_rhs_isSome env x y e_y er_y
      innerBody er rest body hy_fresh_rest hy_fresh_body).mp hsome
    exact (lowerTotalExpr_let_flatten_rhs_head_single_lhs_isSome env x y e_y er_y
      innerBody er rest body).mpr h
  · intro d k env hlen
    cases hey : lowerTotalExpr env e_y with
    | none =>
      have h_lhs : lowerTotalExpr env
          (.Let ((y, e_y, er_y) :: (x, innerBody, er) :: rest) body) = none := by
        cases h : lowerTotalExpr env
            (.Let ((y, e_y, er_y) :: (x, innerBody, er) :: rest) body) with
        | none => rfl
        | some _ =>
          have hsome : (lowerTotalExpr env
              (.Let ((y, e_y, er_y) :: (x, innerBody, er) :: rest) body)).isSome := by
            rw [h]; rfl
          have := (lowerTotalExpr_let_flatten_rhs_head_single_rhs_isSome env x y e_y
            er_y innerBody er rest body hy_fresh_rest hy_fresh_body).mp hsome
          rw [hey] at this; exact absurd this.1 (by simp)
      rw [h_lhs]; trivial
    | some t_ey =>
      cases hiB : lowerTotalExpr (y :: env) innerBody with
      | none =>
        have h_lhs : lowerTotalExpr env
            (.Let ((y, e_y, er_y) :: (x, innerBody, er) :: rest) body) = none := by
          cases h : lowerTotalExpr env
              (.Let ((y, e_y, er_y) :: (x, innerBody, er) :: rest) body) with
          | none => rfl
          | some _ =>
            have hsome : (lowerTotalExpr env
                (.Let ((y, e_y, er_y) :: (x, innerBody, er) :: rest) body)).isSome := by
              rw [h]; rfl
            have := (lowerTotalExpr_let_flatten_rhs_head_single_rhs_isSome env x y e_y
              er_y innerBody er rest body hy_fresh_rest hy_fresh_body).mp hsome
            rw [hiB] at this; exact absurd this.2.1 (by simp)
        rw [h_lhs]; trivial
      | some t_iB =>
        cases hrest : lowerTotalLet (x :: env) (expandFixBinds rest)
            (expandFix body) with
        | none =>
          have h_lhs : lowerTotalExpr env
              (.Let ((y, e_y, er_y) :: (x, innerBody, er) :: rest) body) = none := by
            cases h : lowerTotalExpr env
                (.Let ((y, e_y, er_y) :: (x, innerBody, er) :: rest) body) with
            | none => rfl
            | some _ =>
              have hsome : (lowerTotalExpr env
                  (.Let ((y, e_y, er_y) :: (x, innerBody, er) :: rest) body)).isSome := by
                rw [h]; rfl
              have := (lowerTotalExpr_let_flatten_rhs_head_single_rhs_isSome env x y e_y
                er_y innerBody er rest body hy_fresh_rest hy_fresh_body).mp hsome
              rw [hrest] at this; exact absurd this.2.2 (by simp)
          rw [h_lhs]; trivial
        | some t_rest =>
          rw [lowerTotalExpr_let_flatten_rhs_head_single_rhs x y e_y er_y innerBody er
              rest body hy_fresh_rest hy_fresh_body hey hiB hrest,
            lowerTotalExpr_let_flatten_rhs_head_single_lhs x y e_y er_y innerBody er
              rest body hey hiB hrest]
          simp only
          intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
          have h_steps_lhs :
              steps 3 (State.compute π₁ ρ₁
                  (.Apply (.Lam 0 (.Apply (.Lam 0
                    (renameTerm
                      (shiftRename 2) t_rest)) t_iB)) t_ey)) =
                State.compute
                  (.funV (.VLam (.Apply (.Lam 0
                    (renameTerm
                      (shiftRename 2) t_rest)) t_iB) ρ₁) :: π₁) ρ₁ t_ey := rfl
          have h_steps_rhs :
              steps 6 (State.compute π₂ ρ₂
                  (.Apply (.Lam 0 t_rest) (.Apply (.Lam 0 t_iB) t_ey))) =
                State.compute
                  (.funV (.VLam t_iB ρ₂) :: .funV (.VLam t_rest ρ₂) :: π₂) ρ₂ t_ey := rfl
          apply obsRefinesK_of_steps_left h_steps_lhs
          apply obsRefinesK_of_steps_right h_steps_rhs
          have hclosed_ey : closedAt env.length t_ey :=
            lowerTotal_closedAt env _ t_ey hey
          have hclosed_iB : closedAt (env.length + 1) t_iB := by
            have := lowerTotal_closedAt (y :: env) _ t_iB hiB
            simpa [List.length_cons] using this
          have hclosed_rest : closedAt (env.length + 1) t_rest := by
            have := lowerTotalLet_closedAt (x :: env) _ _ t_rest hrest
            simpa [List.length_cons] using this
          have hd_eq : d = env.length := hlen.symm
          subst hd_eq
          have henv_j : EnvRefinesK j env.length ρ₁ ρ₂ := by
            intro n hn hnd
            obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv n hn hnd
            exact ⟨w₁, w₂, hl, hr', hw⟩
          have hπ_aug : StackRefK ValueRefinesK i
              (.funV (.VLam (.Apply (.Lam 0
                (renameTerm
                  (shiftRename 2) t_rest)) t_iB) ρ₁) :: π₁)
              (.funV (.VLam t_iB ρ₂) :: .funV (.VLam t_rest ρ₂) :: π₂) := by
            intro j' hj' v₁ v₂ hv
            have h_lhs_v : steps 4 (State.ret
                (.funV (.VLam (.Apply (.Lam 0
                  (renameTerm
                    (shiftRename 2) t_rest)) t_iB) ρ₁) :: π₁) v₁) =
                  State.compute (.funV (.VLam
                    (renameTerm
                      (shiftRename 2) t_rest) (ρ₁.extend v₁)) :: π₁)
                    (ρ₁.extend v₁) t_iB := rfl
            have h_rhs_v : steps 1 (State.ret
                (.funV (.VLam t_iB ρ₂) :: .funV (.VLam t_rest ρ₂) :: π₂) v₂) =
                  State.compute (.funV (.VLam t_rest ρ₂) :: π₂) (ρ₂.extend v₂) t_iB := rfl
            apply obsRefinesK_of_steps_left h_lhs_v
            apply obsRefinesK_of_steps_right h_rhs_v
            have henv_j' : EnvRefinesK j' env.length ρ₁ ρ₂ := by
              intro n hn hnd
              obtain ⟨w₁, w₂, hl, hrg, hw⟩ := henv_j n hn hnd
              exact ⟨w₁, w₂, hl, hrg, valueRefinesK_mono (by omega) _ _ hw⟩
            have henv_ext : EnvRefinesK j' (env.length + 1)
                (ρ₁.extend v₁) (ρ₂.extend v₂) :=
              envRefinesK_extend henv_j' hv
            have hπ_inner : StackRefK ValueRefinesK j'
                (.funV (.VLam (renameTerm
                  (shiftRename 2) t_rest) (ρ₁.extend v₁)) :: π₁)
                (.funV (.VLam t_rest ρ₂) :: π₂) := by
              intro j'' hj'' u₁ u₂ hu
              have h_lhs_u : steps 1 (State.ret
                  (.funV (.VLam (renameTerm
                    (shiftRename 2) t_rest) (ρ₁.extend v₁)) :: π₁) u₁) =
                    State.compute π₁ ((ρ₁.extend v₁).extend u₁)
                      (renameTerm
                        (shiftRename 2) t_rest) := rfl
              have h_rhs_u : steps 1 (State.ret
                  (.funV (.VLam t_rest ρ₂) :: π₂) u₂) =
                    State.compute π₂ (ρ₂.extend u₂) t_rest := rfl
              apply obsRefinesK_of_steps_left h_lhs_u
              apply obsRefinesK_of_steps_right h_rhs_u
              have henv_j'' : EnvRefinesK j'' env.length ρ₁ ρ₂ := by
                intro n hn hnd
                obtain ⟨w₁, w₂, hl, hrg, hw⟩ := henv_j' n hn hnd
                exact ⟨w₁, w₂, hl, hrg, valueRefinesK_mono (by omega) _ _ hw⟩
              have henv_shift2_L : RenameEnvRef
                  (shiftRename 2) j'' (env.length + 1)
                  ((ρ₁.extend v₁).extend u₁) (ρ₂.extend u₂) := by
                intro n hn hnd
                show match ((ρ₁.extend v₁).extend u₁).lookup
                             (shiftRename 2 n),
                           (ρ₂.extend u₂).lookup n with
                     | some v₁', some v₂' => ValueRefinesK j'' v₁' v₂'
                     | none, none => True
                     | _, _ => False
                by_cases hn1 : n = 1
                · subst hn1
                  have hsr : shiftRename 2 1 = 1 := by
                    show (if 1 ≥ 2 then 1 + 1 else 1) = 1
                    simp
                  rw [hsr]
                  have h1 : ((ρ₁.extend v₁).extend u₁).lookup 1 = some u₁ := by
                    show (Moist.CEK.CekEnv.cons u₁ (ρ₁.extend v₁)).lookup 1 = some u₁; rfl
                  have h2 : (ρ₂.extend u₂).lookup 1 = some u₂ := by
                    show (Moist.CEK.CekEnv.cons u₂ ρ₂).lookup 1 = some u₂; rfl
                  rw [h1, h2]
                  exact hu
                · have hn2 : n ≥ 2 := by omega
                  have hsr : shiftRename 2 n = n + 1 := by
                    show (if n ≥ 2 then n + 1 else n) = n + 1
                    simp [hn2]
                  rw [hsr]
                  match n, hn2 with
                  | m + 2, _ =>
                    show match (Moist.CEK.CekEnv.cons u₁ (ρ₁.extend v₁)).lookup (m + 2 + 1),
                               (Moist.CEK.CekEnv.cons u₂ ρ₂).lookup (m + 2) with
                         | some v₁', some v₂' => ValueRefinesK j'' v₁' v₂'
                         | none, none => True
                         | _, _ => False
                    have h_lhs : (Moist.CEK.CekEnv.cons u₁ (ρ₁.extend v₁)).lookup (m + 2 + 1) =
                        ρ₁.lookup (m + 1) := by
                      show (ρ₁.extend v₁).lookup (m + 2) = ρ₁.lookup (m + 1)
                      show (Moist.CEK.CekEnv.cons v₁ ρ₁).lookup (m + 2) = ρ₁.lookup (m + 1)
                      rfl
                    have h_rhs : (Moist.CEK.CekEnv.cons u₂ ρ₂).lookup (m + 2) =
                        ρ₂.lookup (m + 1) := rfl
                    rw [h_lhs, h_rhs]
                    have hm1 : m + 1 ≥ 1 := by omega
                    have hmd : m + 1 ≤ env.length := by
                      have : m + 2 ≤ env.length + 1 := hnd
                      omega
                    obtain ⟨w₁, w₂, hl, hrg, hrel⟩ := henv_j'' (m + 1) hm1 hmd
                    rw [hl, hrg]
                    exact hrel
              exact Moist.Verified.FundamentalRefines.renameRefines
                (shiftRename 2) is0preserving_shiftRename2
                (env.length + 1) t_rest hclosed_rest j''
                j'' (Nat.le_refl _) ((ρ₁.extend v₁).extend u₁) (ρ₂.extend u₂)
                henv_shift2_L j'' (Nat.le_refl _) π₁ π₂
                (stackRefK_mono
                  (by omega : j'' ≤ i) hπ)
            exact ftlr (env.length + 1) t_iB hclosed_iB j' j' (Nat.le_refl _)
              (ρ₁.extend v₁) (ρ₂.extend v₂) henv_ext j' (Nat.le_refl _) _ _ hπ_inner
          exact ftlr env.length t_ey hclosed_ey j j (Nat.le_refl _) ρ₁ ρ₂ henv_j i hi
            _ _ hπ_aug

private theorem let_flatten_rhs_head_single_close_pres_fwd
    (x y : VarId) (e_y : Expr) (er_y : Bool) (innerBody : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr)
    (hy_fresh_rest : ∀ r ∈ rest, (freeVars r.2.1).contains y = false)
    (hy_fresh_body : (freeVars body).contains y = false) :
    ∀ env k t₁ t₂,
      lowerTotalExpr env
        (.Let ((x, .Let [(y, e_y, er_y)] innerBody, er) :: rest) body) = some t₁ →
      lowerTotalExpr env
        (.Let ((y, e_y, er_y) :: (x, innerBody, er) :: rest) body) = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true := by
  intro env k t₁ t₂ h₁ h₂ hc
  have hsome₁ : (lowerTotalExpr env
      (.Let ((x, .Let [(y, e_y, er_y)] innerBody, er) :: rest) body)).isSome := by
    rw [h₁]; exact rfl
  obtain ⟨hey_some, hiB_some, hrest_some⟩ :=
    (lowerTotalExpr_let_flatten_rhs_head_single_lhs_isSome env x y e_y er_y
      innerBody er rest body).mp hsome₁
  cases hey : lowerTotalExpr env e_y with
  | none => rw [hey] at hey_some; exact absurd hey_some (by simp)
  | some t_ey =>
    cases hiB : lowerTotalExpr (y :: env) innerBody with
    | none => rw [hiB] at hiB_some; exact absurd hiB_some (by simp)
    | some t_iB =>
      cases hrest : lowerTotalLet (x :: env) (expandFixBinds rest)
          (expandFix body) with
      | none => rw [hrest] at hrest_some; exact absurd hrest_some (by simp)
      | some t_rest =>
        rw [lowerTotalExpr_let_flatten_rhs_head_single_lhs x y e_y er_y innerBody er
          rest body hey hiB hrest] at h₁
        rw [lowerTotalExpr_let_flatten_rhs_head_single_rhs x y e_y er_y innerBody er
          rest body hy_fresh_rest hy_fresh_body hey hiB hrest] at h₂
        cases h₁
        cases h₂
        simp only [closedAt, Bool.and_eq_true] at hc ⊢
        obtain ⟨hrest_c, hiB_c, hey_c⟩ := hc
        exact ⟨⟨closedAt_renameTerm_shiftRename t_rest (k + 1) 2 (by omega) (by omega) hrest_c,
          hiB_c⟩, hey_c⟩

private theorem let_flatten_rhs_head_single_close_pres_bwd
    (x y : VarId) (e_y : Expr) (er_y : Bool) (innerBody : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr)
    (hy_fresh_rest : ∀ r ∈ rest, (freeVars r.2.1).contains y = false)
    (hy_fresh_body : (freeVars body).contains y = false) :
    ∀ env k t₁ t₂,
      lowerTotalExpr env
        (.Let ((y, e_y, er_y) :: (x, innerBody, er) :: rest) body) = some t₁ →
      lowerTotalExpr env
        (.Let ((x, .Let [(y, e_y, er_y)] innerBody, er) :: rest) body) = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true := by
  intro env k t₁ t₂ h₁ h₂ hc
  have hsome₁ : (lowerTotalExpr env
      (.Let ((y, e_y, er_y) :: (x, innerBody, er) :: rest) body)).isSome := by
    rw [h₁]; exact rfl
  obtain ⟨hey_some, hiB_some, hrest_some⟩ :=
    (lowerTotalExpr_let_flatten_rhs_head_single_rhs_isSome env x y e_y er_y
      innerBody er rest body hy_fresh_rest hy_fresh_body).mp hsome₁
  cases hey : lowerTotalExpr env e_y with
  | none => rw [hey] at hey_some; exact absurd hey_some (by simp)
  | some t_ey =>
    cases hiB : lowerTotalExpr (y :: env) innerBody with
    | none => rw [hiB] at hiB_some; exact absurd hiB_some (by simp)
    | some t_iB =>
      cases hrest : lowerTotalLet (x :: env) (expandFixBinds rest)
          (expandFix body) with
      | none => rw [hrest] at hrest_some; exact absurd hrest_some (by simp)
      | some t_rest =>
        rw [lowerTotalExpr_let_flatten_rhs_head_single_rhs x y e_y er_y innerBody er
          rest body hy_fresh_rest hy_fresh_body hey hiB hrest] at h₁
        rw [lowerTotalExpr_let_flatten_rhs_head_single_lhs x y e_y er_y innerBody er
          rest body hey hiB hrest] at h₂
        cases h₁
        cases h₂
        simp only [closedAt, Bool.and_eq_true] at hc ⊢
        obtain ⟨⟨hrest_sh_c, hiB_c⟩, hey_c⟩ := hc
        exact ⟨closedAt_renameTerm_shiftRename_inv t_rest (k + 1) 2 (by omega) (by omega) hrest_sh_c,
          hiB_c, hey_c⟩

theorem mirCtxRefines_let_flatten_rhs_head_single_fwd
    (x : VarId) (y : VarId) (e_y : Expr) (er_y : Bool) (innerBody : Expr)
    (er : Bool) (rest : List (VarId × Expr × Bool)) (body : Expr)
    (hy_fresh_rest : ∀ r ∈ rest, (freeVars r.2.1).contains y = false)
    (hy_fresh_body : (freeVars body).contains y = false) :
    MIRCtxRefines (.Let ((x, .Let [(y, e_y, er_y)] innerBody, er) :: rest) body)
                  (.Let ((y, e_y, er_y) :: (x, innerBody, er) :: rest) body) :=
  mirRefines_to_mirCtxRefines
    (mirRefines_let_flatten_rhs_head_single_fwd x y e_y er_y innerBody er rest body
      hy_fresh_rest hy_fresh_body)
    (let_flatten_rhs_head_single_close_pres_fwd x y e_y er_y innerBody er rest body
      hy_fresh_rest hy_fresh_body)

theorem mirCtxRefines_let_flatten_rhs_head_single_bwd
    (x : VarId) (y : VarId) (e_y : Expr) (er_y : Bool) (innerBody : Expr)
    (er : Bool) (rest : List (VarId × Expr × Bool)) (body : Expr)
    (hy_fresh_rest : ∀ r ∈ rest, (freeVars r.2.1).contains y = false)
    (hy_fresh_body : (freeVars body).contains y = false) :
    MIRCtxRefines (.Let ((y, e_y, er_y) :: (x, innerBody, er) :: rest) body)
                  (.Let ((x, .Let [(y, e_y, er_y)] innerBody, er) :: rest) body) :=
  mirRefines_to_mirCtxRefines
    (mirRefines_let_flatten_rhs_head_single_bwd x y e_y er_y innerBody er rest body
      hy_fresh_rest hy_fresh_body)
    (let_flatten_rhs_head_single_close_pres_bwd x y e_y er_y innerBody er rest body
      hy_fresh_rest hy_fresh_body)

/-! ### Multi-binding let-flatten-rhs-head helper -/

/-- Iterated let-flatten-rhs-head (forward): given a let binding
    `(x, .Let innerBinds innerBody, er) :: rest`, flatten the inner binds out
    so the outer binds become `innerBinds ++ [(x, innerBody, er)] ++ rest`.
    Proved by induction on `innerBinds` using the single-binding primitive. -/
theorem mirCtxRefines_let_flatten_rhs_head_iter_fwd :
    ∀ (x : VarId) (innerBinds : List (VarId × Expr × Bool)) (innerBody : Expr)
      (er : Bool) (rest : List (VarId × Expr × Bool)) (body : Expr),
      (∀ b ∈ innerBinds, (freeVars body).contains b.1 = false) →
      (∀ b ∈ innerBinds, ∀ r ∈ rest, (freeVars r.2.1).contains b.1 = false) →
      MIRCtxRefines (.Let ((x, .Let innerBinds innerBody, er) :: rest) body)
                    (.Let (innerBinds ++ [(x, innerBody, er)] ++ rest) body)
  | x, [], innerBody, er, rest, body, _, _ => by
    have heq : ([] : List (VarId × Expr × Bool)) ++ [(x, innerBody, er)] ++ rest =
               (x, innerBody, er) :: rest := by simp
    rw [heq]
    exact mirCtxRefines_let_flatten_rhs_head_nil_fwd x innerBody er rest body
  | x, (y, e_y, er_y) :: iB_rest, innerBody, er, rest, body, hfresh_body, hfresh_rest => by
    have hy_fresh_body : (freeVars body).contains y = false :=
      hfresh_body (y, e_y, er_y) (List.Mem.head _)
    have hy_fresh_rest : ∀ r ∈ rest, (freeVars r.2.1).contains y = false :=
      fun r hr => hfresh_rest (y, e_y, er_y) (List.Mem.head _) r hr
    have hiBrest_fresh_body : ∀ b ∈ iB_rest, (freeVars body).contains b.1 = false :=
      fun b hb => hfresh_body b (List.Mem.tail _ hb)
    have hiBrest_fresh_rest : ∀ b ∈ iB_rest, ∀ r ∈ rest,
        (freeVars r.2.1).contains b.1 = false :=
      fun b hb r hr => hfresh_rest b (List.Mem.tail _ hb) r hr
    have hrhs_swap : MIRCtxRefines (.Let ((y, e_y, er_y) :: iB_rest) innerBody)
                                   (.Let [(y, e_y, er_y)] (.Let iB_rest innerBody)) :=
      mirCtxRefines_let_cons_split_fwd _ _ _
    have h1 : MIRCtxRefines (.Let ((x, .Let ((y, e_y, er_y) :: iB_rest) innerBody, er) :: rest) body)
                            (.Let ((x, .Let [(y, e_y, er_y)] (.Let iB_rest innerBody), er) :: rest) body) :=
      mirCtxRefines_let_rhs_head hrhs_swap
    have h2 : MIRCtxRefines (.Let ((x, .Let [(y, e_y, er_y)] (.Let iB_rest innerBody), er) :: rest) body)
          (.Let ((y, e_y, er_y) :: (x, .Let iB_rest innerBody, er) :: rest) body) :=
      mirCtxRefines_let_flatten_rhs_head_single_fwd x y e_y er_y (.Let iB_rest innerBody) er
        rest body hy_fresh_rest hy_fresh_body
    have h3 : MIRCtxRefines (.Let ((y, e_y, er_y) :: (x, .Let iB_rest innerBody, er) :: rest) body)
                            (.Let [(y, e_y, er_y)]
                              (.Let ((x, .Let iB_rest innerBody, er) :: rest) body)) :=
      mirCtxRefines_let_cons_split_fwd _ _ _
    have ih : MIRCtxRefines (.Let ((x, .Let iB_rest innerBody, er) :: rest) body)
                            (.Let (iB_rest ++ [(x, innerBody, er)] ++ rest) body) :=
      mirCtxRefines_let_flatten_rhs_head_iter_fwd x iB_rest innerBody er rest body
        hiBrest_fresh_body hiBrest_fresh_rest
    have h4 : MIRCtxRefines (.Let [(y, e_y, er_y)]
                              (.Let ((x, .Let iB_rest innerBody, er) :: rest) body))
                            (.Let [(y, e_y, er_y)]
                              (.Let (iB_rest ++ [(x, innerBody, er)] ++ rest) body)) :=
      mirCtxRefines_let_body ih
    have h5 : MIRCtxRefines (.Let [(y, e_y, er_y)]
                              (.Let (iB_rest ++ [(x, innerBody, er)] ++ rest) body))
                            (.Let ((y, e_y, er_y) :: (iB_rest ++ [(x, innerBody, er)] ++ rest)) body) :=
      mirCtxRefines_let_cons_split_bwd _ _ _
    have heq : (y, e_y, er_y) :: (iB_rest ++ [(x, innerBody, er)] ++ rest) =
               (y, e_y, er_y) :: iB_rest ++ [(x, innerBody, er)] ++ rest := by simp
    rw [heq] at h5
    exact mirCtxRefines_trans h1 (mirCtxRefines_trans h2
          (mirCtxRefines_trans h3 (mirCtxRefines_trans h4 h5)))
  termination_by _ innerBinds _ _ _ _ _ _ => innerBinds.length

/-- Iterated let-flatten-rhs-head (backward). -/
theorem mirCtxRefines_let_flatten_rhs_head_iter_bwd :
    ∀ (x : VarId) (innerBinds : List (VarId × Expr × Bool)) (innerBody : Expr)
      (er : Bool) (rest : List (VarId × Expr × Bool)) (body : Expr),
      (∀ b ∈ innerBinds, (freeVars body).contains b.1 = false) →
      (∀ b ∈ innerBinds, ∀ r ∈ rest, (freeVars r.2.1).contains b.1 = false) →
      MIRCtxRefines (.Let (innerBinds ++ [(x, innerBody, er)] ++ rest) body)
                    (.Let ((x, .Let innerBinds innerBody, er) :: rest) body)
  | x, [], innerBody, er, rest, body, _, _ => by
    have heq : ([] : List (VarId × Expr × Bool)) ++ [(x, innerBody, er)] ++ rest =
               (x, innerBody, er) :: rest := by simp
    rw [heq]
    exact mirCtxRefines_let_flatten_rhs_head_nil_bwd x innerBody er rest body
  | x, (y, e_y, er_y) :: iB_rest, innerBody, er, rest, body, hfresh_body, hfresh_rest => by
    have hy_fresh_body : (freeVars body).contains y = false :=
      hfresh_body (y, e_y, er_y) (List.Mem.head _)
    have hy_fresh_rest : ∀ r ∈ rest, (freeVars r.2.1).contains y = false :=
      fun r hr => hfresh_rest (y, e_y, er_y) (List.Mem.head _) r hr
    have hiBrest_fresh_body : ∀ b ∈ iB_rest, (freeVars body).contains b.1 = false :=
      fun b hb => hfresh_body b (List.Mem.tail _ hb)
    have hiBrest_fresh_rest : ∀ b ∈ iB_rest, ∀ r ∈ rest,
        (freeVars r.2.1).contains b.1 = false :=
      fun b hb r hr => hfresh_rest b (List.Mem.tail _ hb) r hr
    have heq : (y, e_y, er_y) :: iB_rest ++ [(x, innerBody, er)] ++ rest =
               (y, e_y, er_y) :: (iB_rest ++ [(x, innerBody, er)] ++ rest) := by simp
    rw [heq]
    have h5 : MIRCtxRefines (.Let ((y, e_y, er_y) :: (iB_rest ++ [(x, innerBody, er)] ++ rest)) body)
                            (.Let [(y, e_y, er_y)]
                              (.Let (iB_rest ++ [(x, innerBody, er)] ++ rest) body)) :=
      mirCtxRefines_let_cons_split_fwd _ _ _
    have ih : MIRCtxRefines (.Let (iB_rest ++ [(x, innerBody, er)] ++ rest) body)
                            (.Let ((x, .Let iB_rest innerBody, er) :: rest) body) :=
      mirCtxRefines_let_flatten_rhs_head_iter_bwd x iB_rest innerBody er rest body
        hiBrest_fresh_body hiBrest_fresh_rest
    have h4 : MIRCtxRefines (.Let [(y, e_y, er_y)]
                              (.Let (iB_rest ++ [(x, innerBody, er)] ++ rest) body))
                            (.Let [(y, e_y, er_y)]
                              (.Let ((x, .Let iB_rest innerBody, er) :: rest) body)) :=
      mirCtxRefines_let_body ih
    have h3 : MIRCtxRefines (.Let [(y, e_y, er_y)]
                              (.Let ((x, .Let iB_rest innerBody, er) :: rest) body))
                            (.Let ((y, e_y, er_y) :: (x, .Let iB_rest innerBody, er) :: rest) body) :=
      mirCtxRefines_let_cons_split_bwd _ _ _
    have h2 : MIRCtxRefines (.Let ((y, e_y, er_y) :: (x, .Let iB_rest innerBody, er) :: rest) body)
          (.Let ((x, .Let [(y, e_y, er_y)] (.Let iB_rest innerBody), er) :: rest) body) :=
      mirCtxRefines_let_flatten_rhs_head_single_bwd x y e_y er_y (.Let iB_rest innerBody) er
        rest body hy_fresh_rest hy_fresh_body
    have hrhs_swap : MIRCtxRefines (.Let [(y, e_y, er_y)] (.Let iB_rest innerBody))
                                   (.Let ((y, e_y, er_y) :: iB_rest) innerBody) :=
      mirCtxRefines_let_cons_split_bwd _ _ _
    have h1 : MIRCtxRefines (.Let ((x, .Let [(y, e_y, er_y)] (.Let iB_rest innerBody), er) :: rest) body)
                            (.Let ((x, .Let ((y, e_y, er_y) :: iB_rest) innerBody, er) :: rest) body) :=
      mirCtxRefines_let_rhs_head hrhs_swap
    exact mirCtxRefines_trans h5 (mirCtxRefines_trans h4
          (mirCtxRefines_trans h3 (mirCtxRefines_trans h2 h1)))
  termination_by _ innerBinds _ _ _ _ _ _ => innerBinds.length

/-! ### Full `flattenLetBinds` helper -/

/-- Precondition for `mirCtxRefines_flattenLetBinds_*`: for each entry
    `(_, .Let ibs _, _)` in the binding list, every variable in `ibs` is
    fresh in `body` and in every subsequent entry's RHS. -/
inductive FlattenReady (body : Expr) :
    List (VarId × Expr × Bool) → Prop
  | nil : FlattenReady body []
  | letCons {v : VarId} {ibs : List (VarId × Expr × Bool)} {ibody : Expr}
            {er : Bool} {rest : List (VarId × Expr × Bool)}
      (hbody : ∀ ib ∈ ibs, (freeVars body).contains ib.1 = false)
      (hrest : ∀ ib ∈ ibs, ∀ r ∈ rest,
               (freeVars r.2.1).contains ib.1 = false)
      (hrec : FlattenReady body rest) :
      FlattenReady body ((v, .Let ibs ibody, er) :: rest)
  | nonLetCons {v : VarId} {e' : Expr} {er : Bool}
               {rest : List (VarId × Expr × Bool)}
      (hnotlet : ∀ ibs ibody, e' ≠ .Let ibs ibody)
      (hrec : FlattenReady body rest) :
      FlattenReady body ((v, e', er) :: rest)

/-- Helper that unifies all the non-Let-RHS cases in a single step. -/
private theorem flattenLetBinds_cons_non_let_eq
    (v : VarId) (e' : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool))
    (h_not_let : ∀ ibs ibody, e' ≠ .Let ibs ibody) :
    flattenLetBinds ((v, e', er) :: rest) =
      (v, e', er) :: flattenLetBinds rest := by
  show flattenLetBindsStep (v, e', er)
      (flattenLetBinds rest) =
    (v, e', er) :: flattenLetBinds rest
  unfold flattenLetBindsStep
  cases e' with
  | Var _ => rfl
  | Lit _ => rfl
  | Builtin _ => rfl
  | Error => rfl
  | Lam _ _ => rfl
  | Fix _ _ => rfl
  | App _ _ => rfl
  | Force _ => rfl
  | Delay _ => rfl
  | Case _ _ => rfl
  | Constr _ _ => rfl
  | Let ibs ibody => exact absurd rfl (h_not_let ibs ibody)

/-- `flattenLetBinds` refines forward under `FlattenReady`. -/
theorem mirCtxRefines_flattenLetBinds_fwd (body : Expr) :
    ∀ (binds : List (VarId × Expr × Bool)),
      FlattenReady body binds →
      MIRCtxRefines (.Let binds body)
                    (.Let (flattenLetBinds binds) body) := by
  intro binds hfr
  induction hfr with
  | nil =>
    show MIRCtxRefines (.Let [] body) (.Let [] body)
    exact mirCtxRefines_refl _
  | @letCons v ibs ibody er rest hfresh_body hfresh_rest _ ih =>
    have h1 : MIRCtxRefines (.Let ((v, .Let ibs ibody, er) :: rest) body)
                            (.Let (ibs ++ [(v, ibody, er)] ++ rest) body) :=
      mirCtxRefines_let_flatten_rhs_head_iter_fwd v ibs ibody er rest body
        hfresh_body hfresh_rest
    have heq1 : ibs ++ [(v, ibody, er)] ++ rest =
                (ibs ++ [(v, ibody, er)]) ++ rest := by simp [List.append_assoc]
    rw [heq1] at h1
    have h2 : MIRCtxRefines (.Let ((ibs ++ [(v, ibody, er)]) ++ rest) body)
                            (.Let (ibs ++ [(v, ibody, er)]) (.Let rest body)) :=
      mirCtxRefines_let_flatten_body_bwd _ _ _
    have h3 : MIRCtxRefines (.Let rest body)
                            (.Let (flattenLetBinds rest) body) := ih
    have h4 : MIRCtxRefines (.Let (ibs ++ [(v, ibody, er)]) (.Let rest body))
                            (.Let (ibs ++ [(v, ibody, er)])
                              (.Let (flattenLetBinds rest) body)) :=
      mirCtxRefines_let_body h3
    have h5 : MIRCtxRefines
                (.Let (ibs ++ [(v, ibody, er)])
                  (.Let (flattenLetBinds rest) body))
                (.Let ((ibs ++ [(v, ibody, er)]) ++
                  flattenLetBinds rest) body) :=
      mirCtxRefines_let_flatten_body_fwd _ _ _
    have heq2 : (ibs ++ [(v, ibody, er)]) ++ flattenLetBinds rest =
                ibs ++ (v, ibody, er) :: flattenLetBinds rest := by
      simp [List.append_assoc]
    rw [heq2] at h5
    have heq3 : flattenLetBinds ((v, .Let ibs ibody, er) :: rest) =
                ibs ++ (v, ibody, er) :: flattenLetBinds rest := by
      show flattenLetBindsStep (v, .Let ibs ibody, er)
          (flattenLetBinds rest) =
        ibs ++ (v, ibody, er) :: flattenLetBinds rest
      rfl
    rw [heq3]
    exact mirCtxRefines_trans h1 (mirCtxRefines_trans h2
          (mirCtxRefines_trans h4 h5))
  | @nonLetCons v e' er rest hnotlet _ ih =>
    have h1 : MIRCtxRefines (.Let ((v, e', er) :: rest) body)
                            (.Let [(v, e', er)] (.Let rest body)) :=
      mirCtxRefines_let_cons_split_fwd _ _ _
    have h2 : MIRCtxRefines (.Let rest body)
                            (.Let (flattenLetBinds rest) body) := ih
    have h3 : MIRCtxRefines (.Let [(v, e', er)] (.Let rest body))
                            (.Let [(v, e', er)]
                              (.Let (flattenLetBinds rest) body)) :=
      mirCtxRefines_let_body h2
    have h4 : MIRCtxRefines (.Let [(v, e', er)]
                              (.Let (flattenLetBinds rest) body))
                            (.Let ((v, e', er) ::
                              flattenLetBinds rest) body) :=
      mirCtxRefines_let_cons_split_bwd _ _ _
    have heq : flattenLetBinds ((v, e', er) :: rest) =
               (v, e', er) :: flattenLetBinds rest :=
      flattenLetBinds_cons_non_let_eq v e' er rest hnotlet
    rw [heq]
    exact mirCtxRefines_trans h1 (mirCtxRefines_trans h3 h4)

/-- `flattenLetBinds` refines backward under `FlattenReady`. -/
theorem mirCtxRefines_flattenLetBinds_bwd (body : Expr) :
    ∀ (binds : List (VarId × Expr × Bool)),
      FlattenReady body binds →
      MIRCtxRefines (.Let (flattenLetBinds binds) body)
                    (.Let binds body) := by
  intro binds hfr
  induction hfr with
  | nil =>
    show MIRCtxRefines (.Let [] body) (.Let [] body)
    exact mirCtxRefines_refl _
  | @letCons v ibs ibody er rest hfresh_body hfresh_rest _ ih =>
    have heq3 : flattenLetBinds ((v, .Let ibs ibody, er) :: rest) =
                ibs ++ (v, ibody, er) :: flattenLetBinds rest := by
      show flattenLetBindsStep (v, .Let ibs ibody, er)
          (flattenLetBinds rest) =
        ibs ++ (v, ibody, er) :: flattenLetBinds rest
      rfl
    rw [heq3]
    have heq2 : ibs ++ (v, ibody, er) :: flattenLetBinds rest =
                (ibs ++ [(v, ibody, er)]) ++ flattenLetBinds rest := by
      simp [List.append_assoc]
    rw [heq2]
    have h5 : MIRCtxRefines
                (.Let ((ibs ++ [(v, ibody, er)]) ++
                  flattenLetBinds rest) body)
                (.Let (ibs ++ [(v, ibody, er)])
                  (.Let (flattenLetBinds rest) body)) :=
      mirCtxRefines_let_flatten_body_bwd _ _ _
    have h3 : MIRCtxRefines (.Let (flattenLetBinds rest) body)
                            (.Let rest body) := ih
    have h4 : MIRCtxRefines (.Let (ibs ++ [(v, ibody, er)])
                              (.Let (flattenLetBinds rest) body))
                            (.Let (ibs ++ [(v, ibody, er)]) (.Let rest body)) :=
      mirCtxRefines_let_body h3
    have h2 : MIRCtxRefines (.Let (ibs ++ [(v, ibody, er)]) (.Let rest body))
                            (.Let ((ibs ++ [(v, ibody, er)]) ++ rest) body) :=
      mirCtxRefines_let_flatten_body_fwd _ _ _
    have heq1 : (ibs ++ [(v, ibody, er)]) ++ rest =
                ibs ++ [(v, ibody, er)] ++ rest := by simp [List.append_assoc]
    rw [heq1] at h2
    have h1 : MIRCtxRefines (.Let (ibs ++ [(v, ibody, er)] ++ rest) body)
                            (.Let ((v, .Let ibs ibody, er) :: rest) body) :=
      mirCtxRefines_let_flatten_rhs_head_iter_bwd v ibs ibody er rest body
        hfresh_body hfresh_rest
    exact mirCtxRefines_trans h5 (mirCtxRefines_trans h4
          (mirCtxRefines_trans h2 h1))
  | @nonLetCons v e' er rest hnotlet _ ih =>
    have heq : flattenLetBinds ((v, e', er) :: rest) =
               (v, e', er) :: flattenLetBinds rest :=
      flattenLetBinds_cons_non_let_eq v e' er rest hnotlet
    rw [heq]
    have h4 : MIRCtxRefines (.Let ((v, e', er) ::
                              flattenLetBinds rest) body)
                            (.Let [(v, e', er)]
                              (.Let (flattenLetBinds rest) body)) :=
      mirCtxRefines_let_cons_split_fwd _ _ _
    have h2 : MIRCtxRefines (.Let (flattenLetBinds rest) body)
                            (.Let rest body) := ih
    have h3 : MIRCtxRefines (.Let [(v, e', er)]
                              (.Let (flattenLetBinds rest) body))
                            (.Let [(v, e', er)] (.Let rest body)) :=
      mirCtxRefines_let_body h2
    have h1 : MIRCtxRefines (.Let [(v, e', er)] (.Let rest body))
                            (.Let ((v, e', er) :: rest) body) :=
      mirCtxRefines_let_cons_split_bwd _ _ _
    exact mirCtxRefines_trans h4 (mirCtxRefines_trans h3 h1)

/-- `flattenLetBinds` preserves the `maxUidExprBinds` bound: the flattened
    list has max uid bounded by the original. The variables are redistributed
    but not changed, so uids are preserved exactly. -/
theorem maxUidExprBinds_flattenLetBinds_le :
    ∀ (binds : List (VarId × Expr × Bool)),
      maxUidExprBinds (flattenLetBinds binds) ≤
      maxUidExprBinds binds
  | [] => by simp [flattenLetBinds, maxUidExprBinds]
  | (v, e', er) :: rest => by
    have ih : maxUidExprBinds (flattenLetBinds rest) ≤
              maxUidExprBinds rest :=
      maxUidExprBinds_flattenLetBinds_le rest
    show maxUidExprBinds
      (flattenLetBindsStep (v, e', er) (flattenLetBinds rest)) ≤
      maxUidExprBinds ((v, e', er) :: rest)
    unfold flattenLetBindsStep
    cases e' with
    | Let ibs ibody =>
      have h_append := maxUidExprBinds_append ibs
        ((v, ibody, er) :: flattenLetBinds rest)
      have h_rest_cons : maxUidExprBinds
          ((v, ibody, er) :: flattenLetBinds rest) =
          max v.uid (max (maxUidExpr ibody)
            (maxUidExprBinds (flattenLetBinds rest))) := by
        simp only [maxUidExprBinds]
      rw [h_rest_cons] at h_append
      simp only [maxUidExpr, maxUidExprBinds] at h_append ⊢
      omega
    | Var _ | Lit _ | Builtin _ | Error | Lam _ _ | Fix _ _
    | App _ _ | Force _ | Delay _ | Case _ _ | Constr _ _ =>
      show maxUidExprBinds
        ((v, _, er) :: flattenLetBinds rest) ≤
        maxUidExprBinds ((v, _, er) :: rest)
      simp only [maxUidExprBinds]
      omega
end Moist.Verified.MIR
