import Moist.Verified.MIR.Primitives.Shared
import Moist.Verified.MIR.Primitives.LetHoistAppRightAtom
import Moist.Verified.MIR.Primitives.LetHoistCaseScrut

namespace Moist.Verified.MIR

open Moist.CEK
open Moist.Plutus.Term (Term)
open Moist.MIR
  (Expr VarId anfNormalizeCore anfNormalizeListCore anfNormalizeBindsCore anfAtom anfAtomList
   wrapLet flattenLetBody freeVars lowerTotalExpr lowerTotal lowerTotalLet expandFix
   expandFixBinds expandFixList expandFixList_freeVars_not_contains freeVarsList lowerTotalList
   lowerTotalList_prepend_unused_gen lowerTotalList_prepend_unused_none_gen)
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

/-! ## Section 9. Let-hoist-constr-arg primitive

`.Constr tag (pre ++ [.Let v rhs body] ++ post) ≈ .Let v rhs (.Constr tag (pre ++ [body] ++ post))`
when `pre` are atoms and `v ∉ freeVars (pre ++ post)`. -/

/-- Helper: all terms in a list are leaf atoms. -/
private def allLeafAtoms (ts : List Term) : Prop :=
  ∀ t ∈ ts, isLeafAtomTerm t

private theorem allLeafAtoms_nil : allLeafAtoms [] := by intro _ h; exact absurd h List.not_mem_nil

/-- If all atoms in `pre` (MIR) are atoms, then after lowering each element
    of `t_pre` is a leaf atom term. -/
private theorem lowerTotalList_atoms_allLeafAtoms :
    ∀ (env : List VarId) (as : List Expr) (t_as : List Term),
      (∀ a ∈ as, a.isAtom = true) →
      lowerTotalList env (expandFixList as) = some t_as →
      allLeafAtoms t_as := by
  intro env as
  induction as with
  | nil =>
    intro t_as _ h
    simp only [expandFixList, lowerTotalList] at h
    cases h
    exact allLeafAtoms_nil
  | cons a rest ih =>
    intro t_as hatom h
    simp only [expandFixList, lowerTotalList, Option.bind_eq_bind] at h
    cases ht : lowerTotal env (expandFix a) with
    | none => rw [ht] at h; simp at h
    | some t_a =>
      rw [ht] at h
      simp only [Option.bind_some] at h
      cases htr : lowerTotalList env (expandFixList rest) with
      | none => rw [htr] at h; simp at h
      | some t_rest =>
        rw [htr] at h
        simp only [Option.bind_some] at h
        cases h
        have ha_atom : a.isAtom = true := hatom a (List.Mem.head _)
        have ha_leaf : isLeafAtomTerm t_a := lowerTotal_atom_isLeafAtom env a t_a ha_atom ht
        have hrest_atom : ∀ a' ∈ rest, a'.isAtom = true :=
          fun a' h' => hatom a' (List.Mem.tail _ h')
        have ih_res : allLeafAtoms t_rest := ih t_rest hrest_atom htr
        intro t' ht'
        cases ht' with
        | head => exact ha_leaf
        | tail _ htr' => exact ih_res t' htr'

/-- `expandFixList` distributes over list concatenation. -/
private theorem expandFixList_append (xs ys : List Expr) :
    expandFixList (xs ++ ys) =
      expandFixList xs ++ expandFixList ys := by
  induction xs with
  | nil => simp [expandFixList]
  | cons x xs' ih =>
    show expandFixList (x :: (xs' ++ ys)) = _
    simp only [expandFixList]
    rw [ih]
    rfl

/-- `lowerTotalList env (xs ++ ys)` succeeds with `ts_x ++ ts_y` iff both succeed. -/
private theorem lowerTotalList_append {env : List VarId} (xs ys : List Expr)
    {ts_x ts_y : List Term}
    (hxs : lowerTotalList env xs = some ts_x)
    (hys : lowerTotalList env ys = some ts_y) :
    lowerTotalList env (xs ++ ys) = some (ts_x ++ ts_y) := by
  induction xs generalizing ts_x with
  | nil =>
    simp only [lowerTotalList] at hxs
    cases hxs
    simpa using hys
  | cons x xs' ih =>
    simp only [lowerTotalList, Option.bind_eq_bind] at hxs
    cases hx : lowerTotal env x with
    | none => rw [hx] at hxs; simp at hxs
    | some t_x =>
      rw [hx] at hxs
      simp only [Option.bind_some] at hxs
      cases hxs' : lowerTotalList env xs' with
      | none => rw [hxs'] at hxs; simp at hxs
      | some ts_x' =>
        rw [hxs'] at hxs
        simp only [Option.bind_some] at hxs
        cases hxs
        have h_rec := ih hxs'
        show lowerTotalList env (x :: (xs' ++ ys)) = some (t_x :: ts_x' ++ ts_y)
        simp only [lowerTotalList, Option.bind_eq_bind]
        rw [hx, h_rec]
        rfl

/-- Three-way split for `lowerTotalList`. -/
private theorem lowerTotalList_append3 {env : List VarId}
    (pre : List Expr) (mid : Expr) (post : List Expr)
    {t_pre : List Term} {t_mid : Term} {t_post : List Term}
    (hpre : lowerTotalList env pre = some t_pre)
    (hmid : lowerTotal env mid = some t_mid)
    (hpost : lowerTotalList env post = some t_post) :
    lowerTotalList env (pre ++ [mid] ++ post) =
      some (t_pre ++ [t_mid] ++ t_post) := by
  have hmid' : lowerTotalList env [mid] = some [t_mid] := by
    simp only [lowerTotalList, Option.bind_eq_bind]
    rw [hmid]
    rfl
  have h1 : lowerTotalList env (pre ++ [mid]) = some (t_pre ++ [t_mid]) :=
    lowerTotalList_append pre [mid] hpre hmid'
  exact lowerTotalList_append (pre ++ [mid]) post h1 hpost

/-- General stack helper for constrField with shifted `todo` on the right.
    Mirrors `renameRefinesRConstrField` from FundamentalRefines but specialized
    to `shiftRename 1` with a single extended env slot on the right. -/
private theorem stackRefK_constrField_general_shift_aug_fwd {d tag : Nat}
    (t_todo : List Term) (htodo_closed : closedAtList d t_todo = true) :
    ∀ {i : Nat} {done₁ done₂ : List CekValue} {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv}
      {v₂ : CekValue},
      ListRel (ValueRefinesK i) done₁ done₂ →
      EnvRefinesK i d ρ₁ ρ₂ →
      StackRefK ValueRefinesK i π₁ π₂ →
      StackRefK ValueRefinesK i
        (.constrField tag done₁ t_todo ρ₁ :: π₁)
        (.constrField tag done₂
          (renameTermList (shiftRename 1) t_todo)
          (ρ₂.extend v₂) :: π₂) := by
  induction t_todo with
  | nil =>
    intro i done₁ done₂ π₁ π₂ ρ₁ ρ₂ v₂ hdone henv hπ j hj w₁ w₂ hw
    match j with
    | 0 => exact obsRefinesK_zero_ret
    | n + 1 =>
      obsRefinesK_of_step_auto
      simp only [renameTermList, step]
      have hdone_n : ListRel (ValueRefinesK n) done₁ done₂ :=
        listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) hdone
      have hw_n : ValueRefinesK n w₁ w₂ := valueRefinesK_mono (by omega) _ _ hw
      have hcons : ListRel (ValueRefinesK n) (w₁ :: done₁) (w₂ :: done₂) :=
        ⟨hw_n, hdone_n⟩
      have hrev : ListRel (ValueRefinesK n) ((w₁ :: done₁).reverse) ((w₂ :: done₂).reverse) :=
        listRel_reverse hcons
      have hval : ValueRefinesK (n + 1) (.VConstr tag ((w₁ :: done₁).reverse))
          (.VConstr tag ((w₂ :: done₂).reverse)) := by
        match n with
        | 0 => simp only [ValueRefinesK]; exact ⟨trivial, hrev⟩
        | _ + 1 => simp only [ValueRefinesK]; exact ⟨trivial, hrev⟩
      have hπ_n : StackRefK ValueRefinesK n π₁ π₂ := stackRefK_mono (by omega) hπ
      exact hπ_n n (Nat.le_refl _) _ _ (valueRefinesK_mono (by omega) _ _ hval)
  | cons t_a t_rest ih =>
    have ha_closed : closedAt d t_a = true := by
      simp only [closedAtList, Bool.and_eq_true] at htodo_closed
      exact htodo_closed.1
    have hrest_closed : closedAtList d t_rest = true := by
      simp only [closedAtList, Bool.and_eq_true] at htodo_closed
      exact htodo_closed.2
    intro i done₁ done₂ π₁ π₂ ρ₁ ρ₂ v₂ hdone henv hπ j hj w₁ w₂ hw
    match j with
    | 0 => exact obsRefinesK_zero_ret
    | n + 1 =>
      obsRefinesK_of_step_auto
      simp only [renameTermList, step]
      -- LHS: compute (cF tag (w₁ :: done₁) t_rest ρ₁ :: π₁) ρ₁ t_a
      -- RHS: compute (cF tag (w₂ :: done₂) (shift t_rest) (ρ₂.extend v₂) :: π₂)
      --         (ρ₂.extend v₂) (shift t_a)
      -- Apply renameRefinesR_shift1 for t_a with RenameEnvRefR
      have henv_n : EnvRefinesK n d ρ₁ ρ₂ := by
        intro p hp hpd
        obtain ⟨w₁', w₂', hl, hr, hrel⟩ := henv p hp hpd
        exact ⟨w₁', w₂', hl, hr, valueRefinesK_mono (by omega) _ _ hrel⟩
      have henv_RR : Moist.Verified.FundamentalRefines.RenameEnvRefR
          (shiftRename 1) n d ρ₁ (ρ₂.extend v₂) :=
        Moist.Verified.FundamentalRefines.envRefinesK_to_renameEnvRefR_shift henv_n
      -- Need the stack relation for the inner state (after evaluating t_a).
      have hdone_n : ListRel (ValueRefinesK n) (w₁ :: done₁) (w₂ :: done₂) := by
        refine ⟨valueRefinesK_mono (by omega) _ _ hw, ?_⟩
        exact listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) hdone
      have hπ_n : StackRefK ValueRefinesK n π₁ π₂ := stackRefK_mono (by omega) hπ
      have hih := ih hrest_closed
        (i := n) (done₁ := w₁ :: done₁) (done₂ := w₂ :: done₂)
        (π₁ := π₁) (π₂ := π₂) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (v₂ := v₂) hdone_n henv_n hπ_n
      exact Moist.Verified.FundamentalRefines.renameRefinesR_shift1 d t_a ha_closed n n
        (Nat.le_refl _) ρ₁ (ρ₂.extend v₂) henv_RR n (Nat.le_refl _) _ _ hih

/-- Backward version of the general constrField stack helper. -/
private theorem stackRefK_constrField_general_shift_aug_bwd {d tag : Nat}
    (t_todo : List Term) (htodo_closed : closedAtList d t_todo = true) :
    ∀ {i : Nat} {done₁ done₂ : List CekValue} {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv}
      {v₁ : CekValue},
      ListRel (ValueRefinesK i) done₁ done₂ →
      EnvRefinesK i d ρ₁ ρ₂ →
      StackRefK ValueRefinesK i π₁ π₂ →
      StackRefK ValueRefinesK i
        (.constrField tag done₁
          (renameTermList (shiftRename 1) t_todo)
          (ρ₁.extend v₁) :: π₁)
        (.constrField tag done₂ t_todo ρ₂ :: π₂) := by
  induction t_todo with
  | nil =>
    intro i done₁ done₂ π₁ π₂ ρ₁ ρ₂ v₁ hdone henv hπ j hj w₁ w₂ hw
    match j with
    | 0 => exact obsRefinesK_zero_ret
    | n + 1 =>
      obsRefinesK_of_step_auto
      simp only [renameTermList, step]
      have hdone_n : ListRel (ValueRefinesK n) done₁ done₂ :=
        listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) hdone
      have hw_n : ValueRefinesK n w₁ w₂ := valueRefinesK_mono (by omega) _ _ hw
      have hcons : ListRel (ValueRefinesK n) (w₁ :: done₁) (w₂ :: done₂) :=
        ⟨hw_n, hdone_n⟩
      have hrev : ListRel (ValueRefinesK n) ((w₁ :: done₁).reverse) ((w₂ :: done₂).reverse) :=
        listRel_reverse hcons
      have hval : ValueRefinesK (n + 1) (.VConstr tag ((w₁ :: done₁).reverse))
          (.VConstr tag ((w₂ :: done₂).reverse)) := by
        match n with
        | 0 => simp only [ValueRefinesK]; exact ⟨trivial, hrev⟩
        | _ + 1 => simp only [ValueRefinesK]; exact ⟨trivial, hrev⟩
      have hπ_n : StackRefK ValueRefinesK n π₁ π₂ := stackRefK_mono (by omega) hπ
      exact hπ_n n (Nat.le_refl _) _ _ (valueRefinesK_mono (by omega) _ _ hval)
  | cons t_a t_rest ih =>
    have ha_closed : closedAt d t_a = true := by
      simp only [closedAtList, Bool.and_eq_true] at htodo_closed
      exact htodo_closed.1
    have hrest_closed : closedAtList d t_rest = true := by
      simp only [closedAtList, Bool.and_eq_true] at htodo_closed
      exact htodo_closed.2
    intro i done₁ done₂ π₁ π₂ ρ₁ ρ₂ v₁ hdone henv hπ j hj w₁ w₂ hw
    match j with
    | 0 => exact obsRefinesK_zero_ret
    | n + 1 =>
      obsRefinesK_of_step_auto
      simp only [renameTermList, step]
      have henv_n : EnvRefinesK n d ρ₁ ρ₂ := by
        intro p hp hpd
        obtain ⟨w₁', w₂', hl, hr, hrel⟩ := henv p hp hpd
        exact ⟨w₁', w₂', hl, hr, valueRefinesK_mono (by omega) _ _ hrel⟩
      have henv_RL : RenameEnvRef
          (shiftRename 1) n d (ρ₁.extend v₁) ρ₂ :=
        envRefinesK_to_renameEnvRef_shift henv_n
      have hdone_n : ListRel (ValueRefinesK n) (w₁ :: done₁) (w₂ :: done₂) := by
        refine ⟨valueRefinesK_mono (by omega) _ _ hw, ?_⟩
        exact listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) hdone
      have hπ_n : StackRefK ValueRefinesK n π₁ π₂ := stackRefK_mono (by omega) hπ
      have hih := ih hrest_closed
        (i := n) (done₁ := w₁ :: done₁) (done₂ := w₂ :: done₂)
        (π₁ := π₁) (π₂ := π₂) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (v₁ := v₁) hdone_n henv_n hπ_n
      exact renameRefines_shift1 d t_a ha_closed n n
        (Nat.le_refl _) (ρ₁.extend v₁) ρ₂ henv_RL n (Nat.le_refl _) _ _ hih

private theorem lowerTotalExpr_constr_let {env : List VarId} (tag : Nat) (v : VarId)
    {rhs body : Expr} {pre post : List Expr}
    {t_rhs t_body : Term} {t_pre t_post : List Term}
    (h_rhs : lowerTotalExpr env rhs = some t_rhs)
    (h_body : lowerTotalExpr (v :: env) body = some t_body)
    (h_pre : lowerTotalList env (expandFixList pre) = some t_pre)
    (h_post : lowerTotalList env (expandFixList post) = some t_post) :
    lowerTotalExpr env (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post)) =
      some (.Constr tag (t_pre ++ [.Apply (.Lam 0 t_body) t_rhs] ++ t_post)) := by
  have h_rhs' : lowerTotal env (expandFix rhs) = some t_rhs := h_rhs
  have h_body' : lowerTotal (v :: env) (expandFix body) = some t_body := h_body
  -- The middle element after expansion: .Let [(v, expandFix rhs, false)] (expandFix body)
  -- Lowering it produces .Apply (.Lam 0 t_body) t_rhs
  have h_mid : lowerTotal env (expandFix (.Let [(v, rhs, false)] body)) =
      some (.Apply (.Lam 0 t_body) t_rhs) := by
    show lowerTotal env (expandFix (.Let [(v, rhs, false)] body)) =
      some (.Apply (.Lam 0 t_body) t_rhs)
    simp only [expandFix, expandFixBinds, lowerTotal,
               lowerTotalLet, Option.bind_eq_bind, Option.bind_some,
               h_rhs', h_body']
  -- expandFixList distributes over ++
  have hexpand : expandFixList (pre ++ [.Let [(v, rhs, false)] body] ++ post) =
      expandFixList pre ++ [expandFix (.Let [(v, rhs, false)] body)]
        ++ expandFixList post := by
    rw [expandFixList_append, expandFixList_append]
    simp [expandFixList]
  have h_list := lowerTotalList_append3 (expandFixList pre)
    (expandFix (.Let [(v, rhs, false)] body))
    (expandFixList post) h_pre h_mid h_post
  show lowerTotal env (expandFix
      (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post))) = _
  simp only [expandFix, lowerTotal, Option.bind_eq_bind]
  rw [hexpand, h_list]
  rfl

/-- Shape lemma: `.Let v rhs (.Constr tag (pre ++ [body] ++ post))` lowers to
    `.Apply (.Lam 0 (.Constr tag (shift t_pre ++ [t_body] ++ shift t_post))) t_rhs`. -/
private theorem lowerTotalExpr_let_constr {env : List VarId} (tag : Nat) (v : VarId)
    {rhs body : Expr} {pre post : List Expr}
    {t_rhs t_body : Term} {t_pre t_post : List Term}
    (hpre_fresh : ∀ a ∈ pre, (freeVars a).contains v = false)
    (hpost_fresh : ∀ a ∈ post, (freeVars a).contains v = false)
    (h_rhs : lowerTotalExpr env rhs = some t_rhs)
    (h_body : lowerTotalExpr (v :: env) body = some t_body)
    (h_pre : lowerTotalList env (expandFixList pre) = some t_pre)
    (h_post : lowerTotalList env (expandFixList post) = some t_post) :
    lowerTotalExpr env (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post))) =
      some (.Apply (.Lam 0 (.Constr tag
        (renameTermList (shiftRename 1) t_pre
          ++ [t_body] ++
          renameTermList (shiftRename 1) t_post))) t_rhs) := by
  have h_rhs' : lowerTotal env (expandFix rhs) = some t_rhs := h_rhs
  have h_body' : lowerTotal (v :: env) (expandFix body) = some t_body := h_body
  have hpre_fresh' : (freeVarsList (expandFixList pre)).contains v = false :=
    expandFixList_freeVars_not_contains pre v
      (freeVarsList_not_contains_of_forall v pre hpre_fresh)
  have hpost_fresh' : (freeVarsList (expandFixList post)).contains v = false :=
    expandFixList_freeVars_not_contains post v
      (freeVarsList_not_contains_of_forall v post hpost_fresh)
  have h_pre_shift :
      lowerTotalList (v :: env) (expandFixList pre) =
        some (renameTermList (shiftRename 1) t_pre) := by
    have h := lowerTotalList_prepend_unused_gen [] env v
      (expandFixList pre) (.inl hpre_fresh') t_pre h_pre
    simpa using h
  have h_post_shift :
      lowerTotalList (v :: env) (expandFixList post) =
        some (renameTermList (shiftRename 1) t_post) := by
    have h := lowerTotalList_prepend_unused_gen [] env v
      (expandFixList post) (.inl hpost_fresh') t_post h_post
    simpa using h
  have h_body_list : lowerTotalList (v :: env) [expandFix body] =
      some [t_body] := by
    simp only [lowerTotalList, Option.bind_eq_bind]
    rw [h_body']
    rfl
  have hexpand :
      expandFixList (pre ++ [body] ++ post) =
        expandFixList pre ++ [expandFix body]
          ++ expandFixList post := by
    rw [expandFixList_append, expandFixList_append]
    simp [expandFixList]
  have h_inner_list :
      lowerTotalList (v :: env) (expandFixList (pre ++ [body] ++ post)) =
        some (renameTermList (shiftRename 1) t_pre
          ++ [t_body] ++
          renameTermList (shiftRename 1) t_post) := by
    rw [hexpand]
    exact lowerTotalList_append3 _ _ _ h_pre_shift h_body' h_post_shift
  show lowerTotal env (expandFix
      (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post)))) = _
  simp only [expandFix, expandFixBinds, lowerTotal,
             lowerTotalLet, Option.bind_eq_bind, Option.bind_some, h_rhs']
  rw [h_inner_list]
  rfl

/-! ### General-`pre` let-hoist-constr-arg -/

/-- If `lowerTotalList env xs = none`, then `lowerTotalList env (xs ++ ys) = none`. -/
private theorem lowerTotalList_append_none_left {env : List VarId}
    (xs ys : List Expr)
    (h : lowerTotalList env xs = none) :
    lowerTotalList env (xs ++ ys) = none := by
  induction xs with
  | nil => exact absurd h (by simp [lowerTotalList])
  | cons x xs' ih =>
    simp only [lowerTotalList, Option.bind_eq_bind] at h
    show lowerTotalList env (x :: (xs' ++ ys)) = none
    simp only [lowerTotalList, Option.bind_eq_bind]
    cases hx : lowerTotal env x with
    | none => simp
    | some t_x =>
      rw [hx] at h
      simp only [Option.bind_some] at h
      have hxs_none : lowerTotalList env xs' = none := by
        cases hxs : lowerTotalList env xs' with
        | none => rfl
        | some _ => rw [hxs] at h; simp at h
      have hrec := ih hxs_none
      simp [hrec]

/-- If `lowerTotalList env xs = some ts_x` and `lowerTotalList env ys = none`,
    then `lowerTotalList env (xs ++ ys) = none`. -/
private theorem lowerTotalList_append_none_right {env : List VarId}
    (xs ys : List Expr) {ts_x : List Term}
    (hxs : lowerTotalList env xs = some ts_x)
    (hys : lowerTotalList env ys = none) :
    lowerTotalList env (xs ++ ys) = none := by
  induction xs generalizing ts_x with
  | nil => simpa using hys
  | cons x xs' ih =>
    simp only [lowerTotalList, Option.bind_eq_bind] at hxs
    cases hx : lowerTotal env x with
    | none => rw [hx] at hxs; simp at hxs
    | some t_x =>
      rw [hx] at hxs
      simp only [Option.bind_some] at hxs
      cases hxs' : lowerTotalList env xs' with
      | none => rw [hxs'] at hxs; simp at hxs
      | some ts_x' =>
        have h_rec := ih hxs'
        show lowerTotalList env (x :: (xs' ++ ys)) = none
        simp only [lowerTotalList, Option.bind_eq_bind]
        simp [hx, h_rec]

/-- `isSome` iff lemma for `.Constr tag (pre ++ [.Let v rhs body] ++ post)`. -/
private theorem lowerTotalExpr_constr_let_isSome (env : List VarId) (tag : Nat)
    (pre : List Expr) (v : VarId) (rhs body : Expr) (post : List Expr) :
    (lowerTotalExpr env (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post))).isSome ↔
      (lowerTotalList env (expandFixList pre)).isSome ∧
      (lowerTotalExpr env rhs).isSome ∧
      (lowerTotalExpr (v :: env) body).isSome ∧
      (lowerTotalList env (expandFixList post)).isSome := by
  have hexpand : expandFixList (pre ++ [.Let [(v, rhs, false)] body] ++ post) =
      expandFixList pre ++ [expandFix (.Let [(v, rhs, false)] body)]
        ++ expandFixList post := by
    rw [expandFixList_append, expandFixList_append]
    simp [expandFixList]
  constructor
  · intro hsome
    have h : (lowerTotal env (expandFix
        (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post)))).isSome := hsome
    simp only [expandFix, lowerTotal, Option.bind_eq_bind] at h
    rw [hexpand] at h
    cases hp : lowerTotalList env (expandFixList pre) with
    | none =>
      have hfull : lowerTotalList env
          (expandFixList pre ++
            [expandFix (.Let [(v, rhs, false)] body)] ++
            expandFixList post) = none := by
        rw [List.append_assoc]
        exact lowerTotalList_append_none_left _ _ hp
      rw [hfull] at h; simp at h
    | some t_pre =>
      cases hr : lowerTotal env (expandFix rhs) with
      | none =>
        have hmid_none : lowerTotal env
            (expandFix (.Let [(v, rhs, false)] body)) = none := by
          simp only [expandFix, expandFixBinds, lowerTotal,
                     lowerTotalLet, Option.bind_eq_bind]
          rw [hr]; rfl
        have hmidsingle : lowerTotalList env
            [expandFix (.Let [(v, rhs, false)] body)] = none := by
          simp only [lowerTotalList, Option.bind_eq_bind]
          rw [hmid_none]; rfl
        have hmidplus : lowerTotalList env
            ([expandFix (.Let [(v, rhs, false)] body)] ++
              expandFixList post) = none :=
          lowerTotalList_append_none_left _ _ hmidsingle
        have hfull : lowerTotalList env
            (expandFixList pre ++
              [expandFix (.Let [(v, rhs, false)] body)] ++
              expandFixList post) = none := by
          rw [List.append_assoc]
          exact lowerTotalList_append_none_right _ _ hp hmidplus
        rw [hfull] at h; simp at h
      | some t_r =>
        cases hb : lowerTotal (v :: env) (expandFix body) with
        | none =>
          have hmid_none : lowerTotal env
              (expandFix (.Let [(v, rhs, false)] body)) = none := by
            simp only [expandFix, expandFixBinds, lowerTotal,
                       lowerTotalLet, Option.bind_eq_bind, hr, hb,
                       Option.bind_some, Option.bind_none]
          have hmidsingle : lowerTotalList env
              [expandFix (.Let [(v, rhs, false)] body)] = none := by
            simp only [lowerTotalList, Option.bind_eq_bind]
            rw [hmid_none]; rfl
          have hmidplus : lowerTotalList env
              ([expandFix (.Let [(v, rhs, false)] body)] ++
                expandFixList post) = none :=
            lowerTotalList_append_none_left _ _ hmidsingle
          have hfull : lowerTotalList env
              (expandFixList pre ++
                [expandFix (.Let [(v, rhs, false)] body)] ++
                expandFixList post) = none := by
            rw [List.append_assoc]
            exact lowerTotalList_append_none_right _ _ hp hmidplus
          rw [hfull] at h; simp at h
        | some t_b =>
          cases hpost : lowerTotalList env (expandFixList post) with
          | none =>
            have hmid_some : lowerTotal env
                (expandFix (.Let [(v, rhs, false)] body)) =
                  some (.Apply (.Lam 0 t_b) t_r) := by
              simp only [expandFix, expandFixBinds, lowerTotal,
                         lowerTotalLet, Option.bind_eq_bind]
              rw [hr]; simp only [Option.bind_some]; rw [hb]; rfl
            have hmidsingle : lowerTotalList env
                [expandFix (.Let [(v, rhs, false)] body)] =
                  some [.Apply (.Lam 0 t_b) t_r] := by
              simp only [lowerTotalList, Option.bind_eq_bind]
              rw [hmid_some]; rfl
            have hmidplus : lowerTotalList env
                ([expandFix (.Let [(v, rhs, false)] body)] ++
                  expandFixList post) = none :=
              lowerTotalList_append_none_right _ _ hmidsingle hpost
            have hfull : lowerTotalList env
                (expandFixList pre ++
                  [expandFix (.Let [(v, rhs, false)] body)] ++
                  expandFixList post) = none := by
              rw [List.append_assoc]
              exact lowerTotalList_append_none_right _ _ hp hmidplus
            rw [hfull] at h; simp at h
          | some t_post =>
            exact ⟨rfl, by show (lowerTotal env (expandFix rhs)).isSome = true;
                           rw [hr]; rfl,
                   by show (lowerTotal (v :: env) (expandFix body)).isSome = true;
                      rw [hb]; rfl, rfl⟩
  · rintro ⟨hp, hr, hb, hpost⟩
    cases hp' : lowerTotalList env (expandFixList pre) with
    | none => rw [hp'] at hp; exact absurd hp (by simp)
    | some t_pre =>
      cases hr' : lowerTotalExpr env rhs with
      | none => rw [hr'] at hr; exact absurd hr (by simp)
      | some t_r =>
        cases hb' : lowerTotalExpr (v :: env) body with
        | none => rw [hb'] at hb; exact absurd hb (by simp)
        | some t_b =>
          cases hpost' : lowerTotalList env (expandFixList post) with
          | none => rw [hpost'] at hpost; exact absurd hpost (by simp)
          | some t_post =>
            rw [lowerTotalExpr_constr_let tag v hr' hb' hp' hpost']
            rfl

/-- `isSome` iff for the let-constr form (general pre). -/
private theorem lowerTotalExpr_let_constr_isSome (env : List VarId) (tag : Nat)
    (pre : List Expr) (v : VarId) (rhs body : Expr) (post : List Expr)
    (hpre_fresh : ∀ a ∈ pre, (freeVars a).contains v = false)
    (hpost_fresh : ∀ a ∈ post, (freeVars a).contains v = false) :
    (lowerTotalExpr env (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post)))).isSome ↔
      (lowerTotalList env (expandFixList pre)).isSome ∧
      (lowerTotalExpr env rhs).isSome ∧
      (lowerTotalExpr (v :: env) body).isSome ∧
      (lowerTotalList env (expandFixList post)).isSome := by
  have hpre_fresh' : (freeVarsList (expandFixList pre)).contains v = false :=
    expandFixList_freeVars_not_contains pre v
      (freeVarsList_not_contains_of_forall v pre hpre_fresh)
  have hpost_fresh' : (freeVarsList (expandFixList post)).contains v = false :=
    expandFixList_freeVars_not_contains post v
      (freeVarsList_not_contains_of_forall v post hpost_fresh)
  have hexpand : expandFixList (pre ++ [body] ++ post) =
      expandFixList pre ++ [expandFix body]
        ++ expandFixList post := by
    rw [expandFixList_append, expandFixList_append]
    simp [expandFixList]
  constructor
  · intro hsome
    have h : (lowerTotal env (expandFix
        (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post))))).isSome := hsome
    have hexp_let : expandFix
        (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post))) =
        .Let [(v, expandFix rhs, false)]
          (.Constr tag (expandFixList (pre ++ [body] ++ post))) := by
      simp [expandFix, expandFixBinds]
    rw [hexp_let] at h
    simp only [lowerTotal, lowerTotalLet, Option.bind_eq_bind] at h
    cases hr : lowerTotal env (expandFix rhs) with
    | none => rw [hr] at h; simp at h
    | some t_r =>
      rw [hr] at h
      simp only [Option.bind_some] at h
      rw [hexpand] at h
      -- Case-split on extended lowerings
      cases hp_ext : lowerTotalList (v :: env) (expandFixList pre) with
      | none =>
        have : lowerTotalList (v :: env)
            (expandFixList pre ++
              [expandFix body] ++ expandFixList post) = none := by
          rw [List.append_assoc]
          exact lowerTotalList_append_none_left _ _ hp_ext
        rw [this] at h; simp at h
      | some t_pre_ext =>
        cases hbody_ext : lowerTotal (v :: env) (expandFix body) with
        | none =>
          have hmidsingle : lowerTotalList (v :: env)
              [expandFix body] = none := by
            simp only [lowerTotalList, Option.bind_eq_bind]
            rw [hbody_ext]; rfl
          have hmidplus : lowerTotalList (v :: env)
              ([expandFix body] ++ expandFixList post) = none :=
            lowerTotalList_append_none_left _ _ hmidsingle
          have : lowerTotalList (v :: env)
              (expandFixList pre ++
                [expandFix body] ++ expandFixList post) = none := by
            rw [List.append_assoc]
            exact lowerTotalList_append_none_right _ _ hp_ext hmidplus
          rw [this] at h; simp at h
        | some t_body =>
          cases hpost_ext : lowerTotalList (v :: env) (expandFixList post) with
          | none =>
            have hmidsingle : lowerTotalList (v :: env)
                [expandFix body] = some [t_body] := by
              simp only [lowerTotalList, Option.bind_eq_bind]
              rw [hbody_ext]; rfl
            have hmidplus : lowerTotalList (v :: env)
                ([expandFix body] ++ expandFixList post) = none :=
              lowerTotalList_append_none_right _ _ hmidsingle hpost_ext
            have : lowerTotalList (v :: env)
                (expandFixList pre ++
                  [expandFix body] ++ expandFixList post) = none := by
              rw [List.append_assoc]
              exact lowerTotalList_append_none_right _ _ hp_ext hmidplus
            rw [this] at h; simp at h
          | some t_post_ext =>
            -- Freshness lets us go back to env lowerings
            have hpre_base : (lowerTotalList env (expandFixList pre)).isSome := by
              cases hb : lowerTotalList env (expandFixList pre) with
              | none =>
                have := lowerTotalList_prepend_unused_none_gen [] env v
                  (expandFixList pre) (.inl hpre_fresh') (by simpa using hb)
                have hext_none : lowerTotalList (v :: env)
                    (expandFixList pre) = none := by simpa using this
                rw [hext_none] at hp_ext; exact absurd hp_ext (by simp)
              | some _ => rfl
            have hpost_base : (lowerTotalList env (expandFixList post)).isSome := by
              cases hb : lowerTotalList env (expandFixList post) with
              | none =>
                have := lowerTotalList_prepend_unused_none_gen [] env v
                  (expandFixList post) (.inl hpost_fresh') (by simpa using hb)
                have hext_none : lowerTotalList (v :: env)
                    (expandFixList post) = none := by simpa using this
                rw [hext_none] at hpost_ext; exact absurd hpost_ext (by simp)
              | some _ => rfl
            have hr' : lowerTotalExpr env rhs = some t_r := hr
            have hb' : lowerTotalExpr (v :: env) body = some t_body := hbody_ext
            refine ⟨hpre_base, ?_, ?_, hpost_base⟩
            · rw [hr']; rfl
            · rw [hb']; rfl
  · rintro ⟨hp, hr, hb, hpost⟩
    cases hp' : lowerTotalList env (expandFixList pre) with
    | none => rw [hp'] at hp; exact absurd hp (by simp)
    | some t_pre =>
      cases hr' : lowerTotalExpr env rhs with
      | none => rw [hr'] at hr; exact absurd hr (by simp)
      | some t_r =>
        cases hb' : lowerTotalExpr (v :: env) body with
        | none => rw [hb'] at hb; exact absurd hb (by simp)
        | some t_b =>
          cases hpost' : lowerTotalList env (expandFixList post) with
          | none => rw [hpost'] at hpost; exact absurd hpost (by simp)
          | some t_post =>
            rw [lowerTotalExpr_let_constr tag v hpre_fresh hpost_fresh hr' hb' hp' hpost']
            rfl

/-- Step relation between a pair of atom-lookup sequences:
    `ListStepRel ρ ts vs` holds iff for each `i`, stepping `compute π ρ ts[i]` returns
    the value `vs[i]`. Expressed via `List.Forall₂`-like recursion. -/
private def ListStepsFor (ρ : CekEnv) : List Term → List CekValue → Prop
  | [], [] => True
  | t :: ts, v :: vs =>
    (∀ π, Moist.CEK.step (.compute π ρ t) = .ret π v) ∧ ListStepsFor ρ ts vs
  | _, _ => False

/-- Given a list of leaf atom terms, produces the values they evaluate to in
    `ρ₁` and `ρ₂`, along with pointwise refinement. -/
private theorem leafAtomListValues :
    ∀ (t_pre : List Term), allLeafAtoms t_pre →
    ∀ {d : Nat}, closedAtList d t_pre = true →
    ∀ {k : Nat} {ρ₁ ρ₂ : CekEnv}, EnvRefinesK k d ρ₁ ρ₂ →
    ∃ vs₁ vs₂ : List CekValue,
      ListRel (ValueRefinesK k) vs₁ vs₂ ∧
      ListStepsFor ρ₁ t_pre vs₁ ∧
      ListStepsFor ρ₂ t_pre vs₂ := by
  intro t_pre hpre_leaf d hpre_closed k ρ₁ ρ₂ henv
  induction t_pre with
  | nil =>
    refine ⟨[], [], trivial, ?_, ?_⟩ <;> exact trivial
  | cons t rest ih =>
    have ht_leaf : isLeafAtomTerm t := hpre_leaf t (List.Mem.head _)
    have hrest_leaf : allLeafAtoms rest := fun t' ht' => hpre_leaf t' (List.Mem.tail _ ht')
    have ht_closed : closedAt d t = true := by
      simp only [closedAtList, Bool.and_eq_true] at hpre_closed
      exact hpre_closed.1
    have hrest_closed : closedAtList d rest = true := by
      simp only [closedAtList, Bool.and_eq_true] at hpre_closed
      exact hpre_closed.2
    obtain ⟨v₁, v₂, hv_rel, hstep₁, hstep₂⟩ :=
      leafAtomValues ht_leaf ht_closed henv
    obtain ⟨vs₁, vs₂, hvs_rel, hstep_list₁, hstep_list₂⟩ :=
      ih hrest_leaf hrest_closed
    refine ⟨v₁ :: vs₁, v₂ :: vs₂, ⟨hv_rel, hvs_rel⟩, ?_, ?_⟩
    · exact ⟨hstep₁, hstep_list₁⟩
    · exact ⟨hstep₂, hstep_list₂⟩

/-- Inside-cF iterative admin-steps helper (forward). Given a cF-compute state
    processing `t_pre_left` remaining atoms followed by the `.Apply` middle and `t_post`,
    advance `2 * |t_pre_left| + 3` steps to reach the state ready to compute `t_r`. -/
private theorem steps_lhs_cf_aux_fwd
    (tag : Nat) (t_b t_r : Term) (t_post : List Term) :
    ∀ (t_pre_left : List Term) (done : List CekValue) (ρ : CekEnv) (π : Stack)
      (vs_left : List CekValue),
      ListStepsFor ρ t_pre_left vs_left →
      steps (2 * t_pre_left.length + 3)
        (match t_pre_left with
          | [] => State.compute (.constrField tag done t_post ρ :: π) ρ (.Apply (.Lam 0 t_b) t_r)
          | a :: rest => State.compute
              (.constrField tag done (rest ++ [.Apply (.Lam 0 t_b) t_r] ++ t_post) ρ :: π) ρ a) =
        State.compute (.funV (.VLam t_b ρ) ::
          .constrField tag (vs_left.reverse ++ done) t_post ρ :: π) ρ t_r := by
  intro t_pre_left
  induction t_pre_left with
  | nil =>
    intro done ρ π vs_left hstep
    match vs_left, hstep with
    | [], _ =>
      simp only [List.reverse_nil, List.nil_append]
      rfl
  | cons a rest ih =>
    intro done ρ π vs_left hstep
    match vs_left, hstep with
    | v :: vs_rest, ⟨hstep_a, hstep_rest⟩ =>
      show steps (2 * (rest.length + 1) + 3) _ = _
      have heq : 2 * (rest.length + 1) + 3 = 2 + (2 * rest.length + 3) := by omega
      rw [heq, steps_trans]
      -- 2 LHS admin steps for atom `a`
      have hstep_2 :
          steps 2
            (State.compute (.constrField tag done
              (rest ++ [.Apply (.Lam 0 t_b) t_r] ++ t_post) ρ :: π) ρ a) =
            (match rest with
              | [] => State.compute (.constrField tag (v :: done)
                  t_post ρ :: π) ρ (.Apply (.Lam 0 t_b) t_r)
              | b :: rest' => State.compute (.constrField tag (v :: done)
                  (rest' ++ [.Apply (.Lam 0 t_b) t_r] ++ t_post) ρ :: π) ρ b) := by
        show Moist.CEK.step (Moist.CEK.step _) = _
        have ha_step :=
          hstep_a (.constrField tag done (rest ++ [.Apply (.Lam 0 t_b) t_r] ++ t_post) ρ :: π)
        rw [ha_step]
        cases rest with
        | nil => rfl
        | cons b rest' => rfl
      rw [hstep_2]
      have ihres := ih (v :: done) ρ π vs_rest hstep_rest
      have hrev : (v :: vs_rest).reverse ++ done = vs_rest.reverse ++ (v :: done) := by
        simp [List.reverse_cons, List.append_assoc]
      rw [hrev]
      cases rest with
      | nil => simpa using ihres
      | cons b rest' => simpa using ihres

/-- LHS admin-steps equation for `.Constr tag (t_pre ++ [.Apply (.Lam 0 t_b) t_r] ++ t_post)`.
    After `1 + 2 * |t_pre| + 3` steps, we reach the state ready to compute `t_r`.
    The `done` list in the cF frame contains the values from `t_pre`, reversed. -/
private theorem steps_lhs_constr_apply_lam_fwd
    (tag : Nat) (t_b t_r : Term) :
    ∀ (t_pre : List Term) (t_post : List Term)
      (ρ : CekEnv) (π : Stack) (vs : List CekValue),
      ListStepsFor ρ t_pre vs →
      steps (1 + 2 * t_pre.length + 3)
        (State.compute π ρ
          (.Constr tag (t_pre ++ [.Apply (.Lam 0 t_b) t_r] ++ t_post))) =
        State.compute (.funV (.VLam t_b ρ) ::
          .constrField tag vs.reverse t_post ρ :: π) ρ t_r := by
  intro t_pre t_post ρ π vs hstep
  show steps (1 + 2 * t_pre.length + 3) _ = _
  have heq : 1 + 2 * t_pre.length + 3 = 1 + (2 * t_pre.length + 3) := by omega
  rw [heq, steps_trans]
  have haux := steps_lhs_cf_aux_fwd tag t_b t_r t_post t_pre [] ρ π vs hstep
  cases t_pre with
  | nil =>
    have h1 : steps 1 (State.compute π ρ
        (.Constr tag ([] ++ [.Apply (.Lam 0 t_b) t_r] ++ t_post))) =
        State.compute (.constrField tag [] t_post ρ :: π) ρ (.Apply (.Lam 0 t_b) t_r) := rfl
    rw [h1]
    simpa using haux
  | cons a rest =>
    have h1 : steps 1 (State.compute π ρ
        (.Constr tag ((a :: rest) ++ [.Apply (.Lam 0 t_b) t_r] ++ t_post))) =
        State.compute (.constrField tag []
          (rest ++ [.Apply (.Lam 0 t_b) t_r] ++ t_post) ρ :: π) ρ a := rfl
    rw [h1]
    simpa using haux

/-- Inside-hπ_aug RHS admin helper: after funV VLam (.Constr tag ...) fires with
    v_r₂, process the shifted pre atoms. Total steps: `2 + 2 * |t_pre|`. -/
private theorem steps_rhs_hpi_aug_fwd
    (tag : Nat) (t_b : Term) (t_post : List Term) :
    ∀ (t_pre : List Term) (ρ₂ : CekEnv) (v_r₂ : CekValue) (π₂ : Stack)
      (vs₂ : List CekValue),
      ListStepsFor (ρ₂.extend v_r₂) (renameTermList
        (shiftRename 1) t_pre) vs₂ →
      steps (2 + 2 * t_pre.length)
        (State.ret (.funV (.VLam (.Constr tag
          (renameTermList (shiftRename 1) t_pre ++ [t_b] ++
           renameTermList (shiftRename 1) t_post)) ρ₂) :: π₂) v_r₂) =
        State.compute (.constrField tag vs₂.reverse
          (renameTermList (shiftRename 1) t_post)
          (ρ₂.extend v_r₂) :: π₂) (ρ₂.extend v_r₂) t_b := by
  intro t_pre ρ₂ v_r₂ π₂ vs₂ hstep
  -- 2 top-level admin steps: funV-pop (compute .Constr ...) then constr-push.
  have h_2 :
      steps 2 (State.ret (.funV (.VLam (.Constr tag
        (renameTermList (shiftRename 1) t_pre ++ [t_b] ++
         renameTermList (shiftRename 1) t_post)) ρ₂) :: π₂) v_r₂) =
        (match renameTermList (shiftRename 1) t_pre with
          | [] => State.compute (.constrField tag []
              (renameTermList (shiftRename 1) t_post)
              (ρ₂.extend v_r₂) :: π₂) (ρ₂.extend v_r₂) t_b
          | a :: rest => State.compute (.constrField tag []
              (rest ++ [t_b] ++ renameTermList (shiftRename 1) t_post)
              (ρ₂.extend v_r₂) :: π₂) (ρ₂.extend v_r₂) a) := by
    show Moist.CEK.step (Moist.CEK.step _) = _
    show Moist.CEK.step (State.compute π₂ (ρ₂.extend v_r₂)
      (.Constr tag (renameTermList (shiftRename 1) t_pre ++
        [t_b] ++ renameTermList (shiftRename 1) t_post))) = _
    cases renameTermList (shiftRename 1) t_pre with
    | nil => rfl
    | cons b rest' => rfl
  show steps (2 + 2 * t_pre.length) _ = _
  rw [steps_trans, h_2]
  -- Now apply the inside-cF helper-like reasoning, but without the .Apply middle.
  -- Use steps_rhs_cf_atoms_fwd (we'll define this for just atom processing).
  -- We reuse: we have t_pre_shifted = renameTermList ... t_pre
  -- Processing each atom takes 2 steps.
  -- Total additional: 2 * t_pre.length.
  -- Let's use a simpler helper: just iterate through atoms with no middle term.
  have haux : ∀ (t_pre_left : List Term) (done : List CekValue) (vs_left : List CekValue),
      ListStepsFor (ρ₂.extend v_r₂) t_pre_left vs_left →
      steps (2 * t_pre_left.length)
        (match t_pre_left with
          | [] => State.compute (.constrField tag done
              (renameTermList (shiftRename 1) t_post)
              (ρ₂.extend v_r₂) :: π₂) (ρ₂.extend v_r₂) t_b
          | a :: rest => State.compute (.constrField tag done
              (rest ++ [t_b] ++ renameTermList (shiftRename 1) t_post)
              (ρ₂.extend v_r₂) :: π₂) (ρ₂.extend v_r₂) a) =
        State.compute (.constrField tag (vs_left.reverse ++ done)
          (renameTermList (shiftRename 1) t_post)
          (ρ₂.extend v_r₂) :: π₂) (ρ₂.extend v_r₂) t_b := by
    intro t_pre_left
    induction t_pre_left with
    | nil =>
      intro done vs_left hstep_l
      match vs_left, hstep_l with
      | [], _ => simp only [List.reverse_nil, List.nil_append]; rfl
    | cons a rest ih =>
      intro done vs_left hstep_l
      match vs_left, hstep_l with
      | v :: vs_rest, ⟨hstep_a, hstep_rest⟩ =>
        show steps (2 * (rest.length + 1)) _ = _
        have heq : 2 * (rest.length + 1) = 2 + 2 * rest.length := by omega
        rw [heq, steps_trans]
        have hstep_2 :
            steps 2
              (State.compute (.constrField tag done
                (rest ++ [t_b] ++ renameTermList (shiftRename 1) t_post)
                (ρ₂.extend v_r₂) :: π₂) (ρ₂.extend v_r₂) a) =
              (match rest with
                | [] => State.compute (.constrField tag (v :: done)
                    (renameTermList (shiftRename 1) t_post)
                    (ρ₂.extend v_r₂) :: π₂) (ρ₂.extend v_r₂) t_b
                | b :: rest' => State.compute (.constrField tag (v :: done)
                    (rest' ++ [t_b] ++ renameTermList (shiftRename 1) t_post)
                    (ρ₂.extend v_r₂) :: π₂) (ρ₂.extend v_r₂) b) := by
          show Moist.CEK.step (Moist.CEK.step _) = _
          have ha_step := hstep_a (.constrField tag done
            (rest ++ [t_b] ++ renameTermList (shiftRename 1) t_post)
            (ρ₂.extend v_r₂) :: π₂)
          rw [ha_step]
          cases rest with
          | nil => rfl
          | cons b rest' => rfl
        rw [hstep_2]
        have ihres := ih (v :: done) vs_rest hstep_rest
        have hrev : (v :: vs_rest).reverse ++ done = vs_rest.reverse ++ (v :: done) := by
          simp [List.reverse_cons, List.append_assoc]
        rw [hrev]
        cases rest with
        | nil => simpa using ihres
        | cons b rest' => simpa using ihres
  have hlen_shift : ∀ (ts : List Term),
      (renameTermList (shiftRename 1) ts).length = ts.length := by
    intro ts
    induction ts with
    | nil => rfl
    | cons t rest ih =>
      show ((renameTerm (shiftRename 1) t ::
        renameTermList (shiftRename 1) rest)).length = _
      rw [List.length_cons, List.length_cons, ih]
  rw [← hlen_shift t_pre]
  cases hpre : renameTermList (shiftRename 1) t_pre with
  | nil =>
    rw [hpre] at hstep
    -- vs₂ must be empty
    match vs₂, hstep with
    | [], _ =>
      have := haux [] [] [] trivial
      simpa using this
  | cons b rest' =>
    rw [hpre] at hstep
    have := haux (b :: rest') [] vs₂ hstep
    simpa using this

/-- If a list of leaf atoms steps to `vs` in env `ρ`, then the shifted version
    steps to the same `vs` in the extended env `ρ.extend v_inner`. -/
private theorem listStepsFor_shift {t_pre : List Term}
    (hpre_leaf : allLeafAtoms t_pre)
    {d : Nat} (hpre_closed : closedAtList d t_pre = true)
    {ρ : CekEnv} {vs : List CekValue} (v_inner : CekValue)
    (hstep : ListStepsFor ρ t_pre vs) :
    ListStepsFor (ρ.extend v_inner)
      (renameTermList (shiftRename 1) t_pre) vs := by
  induction t_pre generalizing vs with
  | nil =>
    match vs with
    | [] => exact trivial
    | _ :: _ => cases hstep
  | cons t rest ih =>
    match vs, hstep with
    | v :: vs_rest, ⟨hstep_t, hstep_rest⟩ =>
      have ht_leaf : isLeafAtomTerm t := hpre_leaf t (List.Mem.head _)
      have hrest_leaf : allLeafAtoms rest := fun t' ht' => hpre_leaf t' (List.Mem.tail _ ht')
      have ht_closed : closedAt d t = true := by
        simp only [closedAtList, Bool.and_eq_true] at hpre_closed
        exact hpre_closed.1
      have hrest_closed : closedAtList d rest = true := by
        simp only [closedAtList, Bool.and_eq_true] at hpre_closed
        exact hpre_closed.2
      show ListStepsFor (ρ.extend v_inner)
        (renameTerm (shiftRename 1) t ::
         renameTermList (shiftRename 1) rest) (v :: vs_rest)
      refine ⟨?_, ih hrest_leaf hrest_closed hstep_rest⟩
      intro π
      have hempty : Moist.CEK.step (.compute [] ρ t) = .ret [] v := hstep_t []
      exact leafAtom_shift_step ht_leaf ht_closed v_inner v hempty π

/-- Helper: LHS constr-let lowers to none when any sub-expression fails to lower. -/
private theorem lowerTotalExpr_constr_let_eq_none (env : List VarId) (tag : Nat)
    (pre : List Expr) (v : VarId) (rhs body : Expr) (post : List Expr)
    (h : lowerTotalList env (expandFixList pre) = none ∨
         lowerTotalExpr env rhs = none ∨
         lowerTotalExpr (v :: env) body = none ∨
         lowerTotalList env (expandFixList post) = none) :
    lowerTotalExpr env (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post)) = none := by
  cases hlhs : lowerTotalExpr env (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post)) with
  | none => rfl
  | some _ =>
    have hs : (lowerTotalExpr env
        (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post))).isSome := by
      rw [hlhs]; rfl
    obtain ⟨hp, hr, hb, hpost⟩ :=
      (lowerTotalExpr_constr_let_isSome env tag pre v rhs body post).mp hs
    rcases h with h | h | h | h
    · rw [h] at hp; exact absurd hp (by simp)
    · rw [h] at hr; exact absurd hr (by simp)
    · rw [h] at hb; exact absurd hb (by simp)
    · rw [h] at hpost; exact absurd hpost (by simp)

/-- Helper: RHS let-constr lowers to none when any sub-expression fails to lower. -/
private theorem lowerTotalExpr_let_constr_eq_none (env : List VarId) (tag : Nat)
    (pre : List Expr) (v : VarId) (rhs body : Expr) (post : List Expr)
    (hpre_fresh : ∀ a ∈ pre, (freeVars a).contains v = false)
    (hpost_fresh : ∀ a ∈ post, (freeVars a).contains v = false)
    (h : lowerTotalList env (expandFixList pre) = none ∨
         lowerTotalExpr env rhs = none ∨
         lowerTotalExpr (v :: env) body = none ∨
         lowerTotalList env (expandFixList post) = none) :
    lowerTotalExpr env (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post))) = none := by
  cases hlhs : lowerTotalExpr env (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post))) with
  | none => rfl
  | some _ =>
    have hs : (lowerTotalExpr env
        (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post)))).isSome := by
      rw [hlhs]; rfl
    obtain ⟨hp, hr, hb, hpost⟩ :=
      (lowerTotalExpr_let_constr_isSome env tag pre v rhs body post hpre_fresh hpost_fresh).mp hs
    rcases h with h | h | h | h
    · rw [h] at hp; exact absurd hp (by simp)
    · rw [h] at hr; exact absurd hr (by simp)
    · rw [h] at hb; exact absurd hb (by simp)
    · rw [h] at hpost; exact absurd hpost (by simp)

/-- **MIRRefines for let-hoist-constr-arg (forward, general `pre` case)**. -/
theorem mirRefines_let_hoist_constr_arg_fwd (tag : Nat) (pre : List Expr)
    (v : VarId) (rhs body : Expr) (post : List Expr)
    (hpre_atom : ∀ a ∈ pre, a.isAtom = true)
    (hpre_fresh : ∀ a ∈ pre, (freeVars a).contains v = false)
    (hpost_fresh : ∀ a ∈ post, (freeVars a).contains v = false) :
    MIRRefines (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post))
               (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post))) := by
  refine ⟨fun env hsome =>
    (lowerTotalExpr_let_constr_isSome env tag pre v rhs body post hpre_fresh hpost_fresh).mpr
      ((lowerTotalExpr_constr_let_isSome env tag pre v rhs body post).mp hsome), ?_⟩
  intro d k env hlen
  cases hp : lowerTotalList env (expandFixList pre) with
  | none =>
    rw [lowerTotalExpr_constr_let_eq_none env tag pre v rhs body post (.inl hp)]; trivial
  | some t_pre =>
    cases hr : lowerTotalExpr env rhs with
    | none =>
      rw [lowerTotalExpr_constr_let_eq_none env tag pre v rhs body post (.inr (.inl hr))]
      trivial
    | some t_r =>
      cases hb : lowerTotalExpr (v :: env) body with
      | none =>
        rw [lowerTotalExpr_constr_let_eq_none env tag pre v rhs body post
          (.inr (.inr (.inl hb)))]
        trivial
      | some t_b =>
        cases hpost : lowerTotalList env (expandFixList post) with
        | none =>
          rw [lowerTotalExpr_constr_let_eq_none env tag pre v rhs body post
            (.inr (.inr (.inr hpost)))]
          trivial
        | some t_post =>
            rw [lowerTotalExpr_constr_let tag v hr hb hp hpost]
            rw [lowerTotalExpr_let_constr tag v hpre_fresh hpost_fresh hr hb hp hpost]
            simp only
            intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
            -- Get closedness hypotheses
            have hclosed_r : closedAt env.length t_r :=
              lowerTotal_closedAt env _ t_r hr
            have hclosed_b : closedAt (env.length + 1) t_b := by
              have := lowerTotal_closedAt (v :: env) _ t_b hb
              simpa [List.length_cons] using this
            have hclosed_pre : closedAtList env.length t_pre :=
              lowerTotalList_closedAtList env _ t_pre hp
            have hclosed_post : closedAtList env.length t_post :=
              lowerTotalList_closedAtList env _ t_post hpost
            have hpre_leaf : allLeafAtoms t_pre :=
              lowerTotalList_atoms_allLeafAtoms env pre t_pre hpre_atom hp
            have hd_eq : d = env.length := hlen.symm
            subst hd_eq
            have henv_j : EnvRefinesK j env.length ρ₁ ρ₂ := henv
            -- Get the pre-atom values via leafAtomListValues
            obtain ⟨vs₁, vs₂, hvs_rel, hstep_list₁, hstep_list₂⟩ :=
              leafAtomListValues t_pre hpre_leaf hclosed_pre (k := j) henv_j
            -- Advance LHS admin: 1 + 2 * |t_pre| + 3 steps
            have h_steps_lhs := steps_lhs_constr_apply_lam_fwd tag t_b t_r
              t_pre t_post ρ₁ π₁ vs₁ hstep_list₁
            -- Advance RHS admin: 3 steps
            have h_steps_rhs :
                steps 3 (State.compute π₂ ρ₂
                  (.Apply (.Lam 0 (.Constr tag
                    (renameTermList (shiftRename 1) t_pre ++ [t_b] ++
                     renameTermList (shiftRename 1) t_post))) t_r)) =
                  State.compute (.funV (.VLam (.Constr tag
                    (renameTermList (shiftRename 1) t_pre ++ [t_b] ++
                     renameTermList (shiftRename 1) t_post)) ρ₂) :: π₂)
                    ρ₂ t_r := rfl
            apply obsRefinesK_of_steps_left h_steps_lhs
            apply obsRefinesK_of_steps_right h_steps_rhs
            -- Now both sides are computing t_r with augmented stacks.
            -- Build the augmented stack relation.
            have hπ_aug : StackRefK ValueRefinesK i
                (.funV (.VLam t_b ρ₁) :: .constrField tag vs₁.reverse t_post ρ₁ :: π₁)
                (.funV (.VLam (.Constr tag
                  (renameTermList (shiftRename 1) t_pre ++ [t_b] ++
                   renameTermList (shiftRename 1) t_post)) ρ₂) :: π₂) := by
              intro j' hj' v₁' v₂' hv'
              -- LHS: 1 step (pop funV, compute t_b in extended env)
              have h_lhs_inner :
                  steps 1 (State.ret (.funV (.VLam t_b ρ₁) ::
                    .constrField tag vs₁.reverse t_post ρ₁ :: π₁) v₁') =
                    State.compute (.constrField tag vs₁.reverse t_post ρ₁ :: π₁)
                      (ρ₁.extend v₁') t_b := rfl
              apply obsRefinesK_of_steps_left h_lhs_inner
              -- RHS: 2 + 2 * |t_pre| steps (funV-pop, compute constr, process shifted atoms)
              have henv_j' : EnvRefinesK j' env.length ρ₁ ρ₂ := by
                intro n hn hnd
                obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv n hn hnd
                exact ⟨w₁, w₂, hl, hr', valueRefinesK_mono (by omega) _ _ hw⟩
              obtain ⟨vs₁', vs₂', hvs_rel', hstep_list₁', hstep_list₂'⟩ :=
                leafAtomListValues t_pre hpre_leaf hclosed_pre (k := j') henv_j'
              -- The RHS uses the shifted version with extended env. Apply listStepsFor_shift.
              have hstep_shift := listStepsFor_shift hpre_leaf hclosed_pre v₂' hstep_list₂'
              have h_rhs_inner := steps_rhs_hpi_aug_fwd tag t_b t_post t_pre ρ₂ v₂' π₂ vs₂'
                hstep_shift
              apply obsRefinesK_of_steps_right h_rhs_inner
              -- Now apply stackRefK_constrField_general_shift_aug_fwd to relate the two cF frames
              -- with done lists being vs₁.reverse (LHS) and vs₂'.reverse (RHS).
              have henv_ext : EnvRefinesK j' (env.length + 1) (ρ₁.extend v₁') (ρ₂.extend v₂') :=
                envRefinesK_extend henv_j' hv'
              have hπ_j' : StackRefK ValueRefinesK j' π₁ π₂ :=
                stackRefK_mono (by omega) hπ
              -- Get the list relation between vs₁.reverse and vs₂'.reverse
              -- vs₁ ≈ vs₂ (from original leafAtomListValues at step j)
              -- vs₁' ≈ vs₂' (from second leafAtomListValues at step j')
              -- Actually we need: done₁ ≈ done₂. Use vs₁ or vs₁' as LHS done — pick vs₁' since we use it.
              -- But h_steps_lhs uses vs₁, not vs₁'. Mismatch!
              -- Actually we need done₁ on LHS = vs₁.reverse, and done₂ on RHS = vs₂'.reverse.
              -- We need ListRel (ValueRefinesK j') vs₁.reverse vs₂'.reverse.
              -- For that, vs₁ values are from leafAtomListValues at step j, and vs₂'
              -- values are from leafAtomListValues at step j'. They're different existentials.
              -- But since leafAtomValues uses env.lookup, and the env lookup is deterministic,
              -- the values vs₁ and vs₁' should actually be the same! Let me use this.
              -- Actually, we can use the fact that atom steps are deterministic. Let me prove
              -- that vs₁ = vs₁' (they come from the same ρ₁ and the same t_pre).
              have listStepsFor_det : ∀ (t_p : List Term) (ws₁ ws₁' : List CekValue),
                  ListStepsFor ρ₁ t_p ws₁ → ListStepsFor ρ₁ t_p ws₁' → ws₁ = ws₁' := by
                intro t_p
                induction t_p with
                | nil =>
                  intro ws₁ ws₁' hs hs'
                  match ws₁, ws₁', hs, hs' with
                  | [], [], _, _ => rfl
                | cons t rest ih =>
                  intro ws₁ ws₁' hs hs'
                  match ws₁, ws₁', hs, hs' with
                  | w₁ :: ws_rest, w₁' :: ws_rest', ⟨hst, hsr⟩, ⟨hst', hsr'⟩ =>
                    have h1 := hst ([] : Stack)
                    have h2 := hst' ([] : Stack)
                    rw [h1] at h2
                    have heq : w₁ = w₁' := by injection h2
                    have hrec : ws_rest = ws_rest' := ih ws_rest ws_rest' hsr hsr'
                    subst heq
                    subst hrec
                    rfl
              have hvs_eq : vs₁ = vs₁' := listStepsFor_det t_pre vs₁ vs₁' hstep_list₁ hstep_list₁'
              subst hvs_eq
              -- Now we have vs₁ ≈ vs₂' (at j'), take reverse for the list relation.
              have hvs_rel_j' : ListRel (ValueRefinesK j') vs₁.reverse vs₂'.reverse :=
                listRel_reverse hvs_rel'
              have hπ_cf : StackRefK ValueRefinesK j'
                  (.constrField tag vs₁.reverse t_post ρ₁ :: π₁)
                  (.constrField tag vs₂'.reverse
                    (renameTermList (shiftRename 1) t_post)
                    (ρ₂.extend v₂') :: π₂) :=
                stackRefK_constrField_general_shift_aug_fwd t_post hclosed_post
                  hvs_rel_j' henv_j' hπ_j'
              exact ftlr (env.length + 1) t_b hclosed_b j' j' (Nat.le_refl _)
                (ρ₁.extend v₁') (ρ₂.extend v₂') henv_ext j' (Nat.le_refl _) _ _ hπ_cf
            exact ftlr env.length t_r hclosed_r j j (Nat.le_refl _) ρ₁ ρ₂ henv_j i hi
              _ _ hπ_aug

/-- Backward admin-steps for `.Constr tag (t_pre ++ [.Apply (.Lam 0 t_b) t_r] ++ t_post)`. -/
private theorem steps_rhs_constr_apply_lam_bwd
    (tag : Nat) (t_b t_r : Term) :
    ∀ (t_pre : List Term) (t_post : List Term)
      (ρ : CekEnv) (π : Stack) (vs : List CekValue),
      ListStepsFor ρ t_pre vs →
      steps (1 + 2 * t_pre.length + 3)
        (State.compute π ρ
          (.Constr tag (t_pre ++ [.Apply (.Lam 0 t_b) t_r] ++ t_post))) =
        State.compute (.funV (.VLam t_b ρ) ::
          .constrField tag vs.reverse t_post ρ :: π) ρ t_r :=
  steps_lhs_constr_apply_lam_fwd tag t_b t_r

/-- Backward hπ_aug helper: mirrors `steps_rhs_hpi_aug_fwd` but with LHS/RHS swapped
    — this is the LHS side in the bwd case. -/
private theorem steps_lhs_hpi_aug_bwd
    (tag : Nat) (t_b : Term) (t_post : List Term) :
    ∀ (t_pre : List Term) (ρ₁ : CekEnv) (v_r₁ : CekValue) (π₁ : Stack)
      (vs₁ : List CekValue),
      ListStepsFor (ρ₁.extend v_r₁) (renameTermList
        (shiftRename 1) t_pre) vs₁ →
      steps (2 + 2 * t_pre.length)
        (State.ret (.funV (.VLam (.Constr tag
          (renameTermList (shiftRename 1) t_pre ++ [t_b] ++
           renameTermList (shiftRename 1) t_post)) ρ₁) :: π₁) v_r₁) =
        State.compute (.constrField tag vs₁.reverse
          (renameTermList (shiftRename 1) t_post)
          (ρ₁.extend v_r₁) :: π₁) (ρ₁.extend v_r₁) t_b :=
  steps_rhs_hpi_aug_fwd tag t_b t_post

/-- **MIRRefines for let-hoist-constr-arg (backward, general `pre` case)**. -/
theorem mirRefines_let_hoist_constr_arg_bwd (tag : Nat) (pre : List Expr)
    (v : VarId) (rhs body : Expr) (post : List Expr)
    (hpre_atom : ∀ a ∈ pre, a.isAtom = true)
    (hpre_fresh : ∀ a ∈ pre, (freeVars a).contains v = false)
    (hpost_fresh : ∀ a ∈ post, (freeVars a).contains v = false) :
    MIRRefines (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post)))
               (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post)) := by
  refine ⟨fun env hsome =>
    (lowerTotalExpr_constr_let_isSome env tag pre v rhs body post).mpr
      ((lowerTotalExpr_let_constr_isSome env tag pre v rhs body post
        hpre_fresh hpost_fresh).mp hsome), ?_⟩
  intro d k env hlen
  cases hp : lowerTotalList env (expandFixList pre) with
  | none =>
    rw [lowerTotalExpr_let_constr_eq_none env tag pre v rhs body post
      hpre_fresh hpost_fresh (.inl hp)]
    trivial
  | some t_pre =>
    cases hr : lowerTotalExpr env rhs with
    | none =>
      rw [lowerTotalExpr_let_constr_eq_none env tag pre v rhs body post
        hpre_fresh hpost_fresh (.inr (.inl hr))]
      trivial
    | some t_r =>
      cases hb : lowerTotalExpr (v :: env) body with
      | none =>
        rw [lowerTotalExpr_let_constr_eq_none env tag pre v rhs body post
          hpre_fresh hpost_fresh (.inr (.inr (.inl hb)))]
        trivial
      | some t_b =>
        cases hpost : lowerTotalList env (expandFixList post) with
        | none =>
          rw [lowerTotalExpr_let_constr_eq_none env tag pre v rhs body post
            hpre_fresh hpost_fresh (.inr (.inr (.inr hpost)))]
          trivial
        | some t_post =>
            rw [lowerTotalExpr_let_constr tag v hpre_fresh hpost_fresh hr hb hp hpost]
            rw [lowerTotalExpr_constr_let tag v hr hb hp hpost]
            simp only
            intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
            have hclosed_r : closedAt env.length t_r :=
              lowerTotal_closedAt env _ t_r hr
            have hclosed_b : closedAt (env.length + 1) t_b := by
              have := lowerTotal_closedAt (v :: env) _ t_b hb
              simpa [List.length_cons] using this
            have hclosed_pre : closedAtList env.length t_pre :=
              lowerTotalList_closedAtList env _ t_pre hp
            have hclosed_post : closedAtList env.length t_post :=
              lowerTotalList_closedAtList env _ t_post hpost
            have hpre_leaf : allLeafAtoms t_pre :=
              lowerTotalList_atoms_allLeafAtoms env pre t_pre hpre_atom hp
            have hd_eq : d = env.length := hlen.symm
            subst hd_eq
            have henv_j : EnvRefinesK j env.length ρ₁ ρ₂ := henv
            -- Get pre-atom values via leafAtomListValues
            obtain ⟨vs₁, vs₂, hvs_rel, hstep_list₁, hstep_list₂⟩ :=
              leafAtomListValues t_pre hpre_leaf hclosed_pre (k := j) henv_j
            -- Advance LHS admin: 3 steps
            have h_steps_lhs :
                steps 3 (State.compute π₁ ρ₁
                  (.Apply (.Lam 0 (.Constr tag
                    (renameTermList (shiftRename 1) t_pre ++ [t_b] ++
                     renameTermList (shiftRename 1) t_post))) t_r)) =
                  State.compute (.funV (.VLam (.Constr tag
                    (renameTermList (shiftRename 1) t_pre ++ [t_b] ++
                     renameTermList (shiftRename 1) t_post)) ρ₁) :: π₁)
                    ρ₁ t_r := rfl
            -- Advance RHS admin: 1 + 2 * |t_pre| + 3 steps
            have h_steps_rhs := steps_rhs_constr_apply_lam_bwd tag t_b t_r
              t_pre t_post ρ₂ π₂ vs₂ hstep_list₂
            apply obsRefinesK_of_steps_left h_steps_lhs
            apply obsRefinesK_of_steps_right h_steps_rhs
            -- Build the augmented stack relation
            have hπ_aug : StackRefK ValueRefinesK i
                (.funV (.VLam (.Constr tag
                  (renameTermList (shiftRename 1) t_pre ++ [t_b] ++
                   renameTermList (shiftRename 1) t_post)) ρ₁) :: π₁)
                (.funV (.VLam t_b ρ₂) :: .constrField tag vs₂.reverse t_post ρ₂ :: π₂) := by
              intro j' hj' v₁' v₂' hv'
              -- RHS: 1 step (pop funV, compute t_b in extended env)
              have h_rhs_inner :
                  steps 1 (State.ret (.funV (.VLam t_b ρ₂) ::
                    .constrField tag vs₂.reverse t_post ρ₂ :: π₂) v₂') =
                    State.compute (.constrField tag vs₂.reverse t_post ρ₂ :: π₂)
                      (ρ₂.extend v₂') t_b := rfl
              apply obsRefinesK_of_steps_right h_rhs_inner
              -- LHS: 2 + 2 * |t_pre| steps (funV-pop, compute constr, process shifted atoms)
              have henv_j' : EnvRefinesK j' env.length ρ₁ ρ₂ := by
                intro n hn hnd
                obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv n hn hnd
                exact ⟨w₁, w₂, hl, hr', valueRefinesK_mono (by omega) _ _ hw⟩
              obtain ⟨vs₁', vs₂', hvs_rel', hstep_list₁', hstep_list₂'⟩ :=
                leafAtomListValues t_pre hpre_leaf hclosed_pre (k := j') henv_j'
              have hstep_shift := listStepsFor_shift hpre_leaf hclosed_pre v₁' hstep_list₁'
              -- Wait: in bwd case, the LHS is the Let form (apply-lam-constr), so the LHS env
              -- is ρ₁ and we need to compute shift t_pre in (ρ₁.extend v₁'). ✓
              have h_lhs_inner := steps_lhs_hpi_aug_bwd tag t_b t_post t_pre ρ₁ v₁' π₁ vs₁'
                hstep_shift
              apply obsRefinesK_of_steps_left h_lhs_inner
              -- Now apply stackRefK_constrField_general_shift_aug_bwd
              have henv_ext : EnvRefinesK j' (env.length + 1) (ρ₁.extend v₁') (ρ₂.extend v₂') :=
                envRefinesK_extend henv_j' hv'
              have hπ_j' : StackRefK ValueRefinesK j' π₁ π₂ :=
                stackRefK_mono (by omega) hπ
              -- vs₂ and vs₂' should be equal by determinism of atom steps in ρ₂
              have listStepsFor_det : ∀ (t_p : List Term) (ws₁ ws₁' : List CekValue),
                  ListStepsFor ρ₂ t_p ws₁ → ListStepsFor ρ₂ t_p ws₁' → ws₁ = ws₁' := by
                intro t_p
                induction t_p with
                | nil =>
                  intro ws₁ ws₁' hs hs'
                  match ws₁, ws₁', hs, hs' with
                  | [], [], _, _ => rfl
                | cons t rest ih =>
                  intro ws₁ ws₁' hs hs'
                  match ws₁, ws₁', hs, hs' with
                  | w₁ :: ws_rest, w₁' :: ws_rest', ⟨hst, hsr⟩, ⟨hst', hsr'⟩ =>
                    have h1 := hst ([] : Stack)
                    have h2 := hst' ([] : Stack)
                    rw [h1] at h2
                    have heq : w₁ = w₁' := by injection h2
                    have hrec : ws_rest = ws_rest' := ih ws_rest ws_rest' hsr hsr'
                    subst heq
                    subst hrec
                    rfl
              have hvs_eq : vs₂ = vs₂' := listStepsFor_det t_pre vs₂ vs₂' hstep_list₂ hstep_list₂'
              subst hvs_eq
              have hvs_rel_j' : ListRel (ValueRefinesK j') vs₁'.reverse vs₂.reverse :=
                listRel_reverse hvs_rel'
              have hπ_cf : StackRefK ValueRefinesK j'
                  (.constrField tag vs₁'.reverse
                    (renameTermList (shiftRename 1) t_post)
                    (ρ₁.extend v₁') :: π₁)
                  (.constrField tag vs₂.reverse t_post ρ₂ :: π₂) :=
                stackRefK_constrField_general_shift_aug_bwd t_post hclosed_post
                  hvs_rel_j' henv_j' hπ_j'
              exact ftlr (env.length + 1) t_b hclosed_b j' j' (Nat.le_refl _)
                (ρ₁.extend v₁') (ρ₂.extend v₂') henv_ext j' (Nat.le_refl _) _ _ hπ_cf
            exact ftlr env.length t_r hclosed_r j j (Nat.le_refl _) ρ₁ ρ₂ henv_j i hi
              _ _ hπ_aug

/-- Closedness preservation (forward). -/
private theorem let_hoist_constr_arg_close_pres_fwd (tag : Nat) (pre : List Expr)
    (v : VarId) (rhs body : Expr) (post : List Expr)
    (_hpre_atom : ∀ a ∈ pre, a.isAtom = true)
    (hpre_fresh : ∀ a ∈ pre, (freeVars a).contains v = false)
    (hpost_fresh : ∀ a ∈ post, (freeVars a).contains v = false) :
    ∀ env k t₁ t₂,
      lowerTotalExpr env (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post)) = some t₁ →
      lowerTotalExpr env (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post))) = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true := by
  intro env k t₁ t₂ h₁ h₂ hc
  have hsome₁ :
      (lowerTotalExpr env (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post))).isSome := by
    rw [h₁]; exact rfl
  obtain ⟨hp_some, hr_some, hb_some, hpost_some⟩ :=
    (lowerTotalExpr_constr_let_isSome env tag pre v rhs body post).mp hsome₁
  cases hp : lowerTotalList env (expandFixList pre) with
  | none => rw [hp] at hp_some; exact absurd hp_some (by simp)
  | some t_pre =>
    cases hr : lowerTotalExpr env rhs with
    | none => rw [hr] at hr_some; exact absurd hr_some (by simp)
    | some t_r =>
      cases hb : lowerTotalExpr (v :: env) body with
      | none => rw [hb] at hb_some; exact absurd hb_some (by simp)
      | some t_b =>
        cases hpost : lowerTotalList env (expandFixList post) with
        | none => rw [hpost] at hpost_some; exact absurd hpost_some (by simp)
        | some t_post =>
          rw [lowerTotalExpr_constr_let tag v hr hb hp hpost] at h₁
          rw [lowerTotalExpr_let_constr tag v hpre_fresh hpost_fresh hr hb hp hpost] at h₂
          cases h₁
          cases h₂
          -- LHS closedness structure:
          --   closedAt k (.Constr tag (t_pre ++ [.Apply (.Lam 0 t_b) t_r] ++ t_post))
          -- = closedAtList k (t_pre ++ [.Apply (.Lam 0 t_b) t_r] ++ t_post)
          -- which expands via two appends.
          have hpre_c : closedAtList k t_pre = true := by
            have h := hc
            simp only [closedAt] at h
            have := ((closedAtList_append k
              (t_pre ++ [.Apply (.Lam 0 t_b) t_r]) t_post).mp h).1
            exact ((closedAtList_append k
              t_pre [.Apply (.Lam 0 t_b) t_r]).mp this).1
          have hmid_c : closedAt k (.Apply (.Lam 0 t_b) t_r) = true := by
            have h := hc
            simp only [closedAt] at h
            have := ((closedAtList_append k
              (t_pre ++ [.Apply (.Lam 0 t_b) t_r]) t_post).mp h).1
            have := ((closedAtList_append k
              t_pre [.Apply (.Lam 0 t_b) t_r]).mp this).2
            simp only [closedAtList, Bool.and_eq_true] at this
            exact this.1
          have hpost_c : closedAtList k t_post = true := by
            have h := hc
            simp only [closedAt] at h
            exact ((closedAtList_append k
              (t_pre ++ [.Apply (.Lam 0 t_b) t_r]) t_post).mp h).2
          have hb_c : closedAt (k + 1) t_b := by
            simp only [closedAt, Bool.and_eq_true] at hmid_c
            exact hmid_c.1
          have hr_c : closedAt k t_r := by
            simp only [closedAt, Bool.and_eq_true] at hmid_c
            exact hmid_c.2
          -- RHS closedness structure:
          --   closedAt k (.Apply (.Lam 0 (.Constr tag (shift t_pre ++ [t_b] ++ shift t_post))) t_r)
          -- = closedAt (k+1) (.Constr tag ...) ∧ closedAt k t_r
          -- = closedAtList (k+1) (shift t_pre ++ [t_b] ++ shift t_post) ∧ closedAt k t_r
          have hpre_sh : closedAtList (k + 1)
              (renameTermList (shiftRename 1) t_pre) = true :=
            closedAtList_renameTermList_shiftRename t_pre k 1 (by omega) (by omega) hpre_c
          have hpost_sh : closedAtList (k + 1)
              (renameTermList (shiftRename 1) t_post) = true :=
            closedAtList_renameTermList_shiftRename t_post k 1 (by omega) (by omega) hpost_c
          show closedAt k (.Apply (.Lam 0 (.Constr tag _)) t_r) = true
          have hmid_list : closedAtList (k + 1)
              [t_b] = true := by
            simp only [closedAtList, Bool.and_eq_true]
            exact ⟨hb_c, trivial⟩
          have h_step1 : closedAtList (k + 1)
              (renameTermList (shiftRename 1) t_pre ++ [t_b]) = true :=
            (closedAtList_append (k + 1) _ _).mpr ⟨hpre_sh, hmid_list⟩
          have h_full : closedAtList (k + 1)
              (renameTermList (shiftRename 1) t_pre ++ [t_b] ++
               renameTermList (shiftRename 1) t_post) = true :=
            (closedAtList_append (k + 1) _ _).mpr ⟨h_step1, hpost_sh⟩
          simp only [closedAt, Bool.and_eq_true]
          exact ⟨h_full, hr_c⟩

/-- Closedness preservation (backward). -/
private theorem let_hoist_constr_arg_close_pres_bwd (tag : Nat) (pre : List Expr)
    (v : VarId) (rhs body : Expr) (post : List Expr)
    (_hpre_atom : ∀ a ∈ pre, a.isAtom = true)
    (hpre_fresh : ∀ a ∈ pre, (freeVars a).contains v = false)
    (hpost_fresh : ∀ a ∈ post, (freeVars a).contains v = false) :
    ∀ env k t₁ t₂,
      lowerTotalExpr env (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post))) = some t₁ →
      lowerTotalExpr env (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post)) = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true := by
  intro env k t₁ t₂ h₁ h₂ hc
  have hsome₁ :
      (lowerTotalExpr env (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post)))).isSome := by
    rw [h₁]; exact rfl
  obtain ⟨hp_some, hr_some, hb_some, hpost_some⟩ :=
    (lowerTotalExpr_let_constr_isSome env tag pre v rhs body post hpre_fresh hpost_fresh).mp hsome₁
  cases hp : lowerTotalList env (expandFixList pre) with
  | none => rw [hp] at hp_some; exact absurd hp_some (by simp)
  | some t_pre =>
    cases hr : lowerTotalExpr env rhs with
    | none => rw [hr] at hr_some; exact absurd hr_some (by simp)
    | some t_r =>
      cases hb : lowerTotalExpr (v :: env) body with
      | none => rw [hb] at hb_some; exact absurd hb_some (by simp)
      | some t_b =>
        cases hpost : lowerTotalList env (expandFixList post) with
        | none => rw [hpost] at hpost_some; exact absurd hpost_some (by simp)
        | some t_post =>
          rw [lowerTotalExpr_let_constr tag v hpre_fresh hpost_fresh hr hb hp hpost] at h₁
          rw [lowerTotalExpr_constr_let tag v hr hb hp hpost] at h₂
          cases h₁
          cases h₂
          -- LHS: closedAt k (.Apply (.Lam 0 (.Constr tag (shift t_pre ++ [t_b] ++ shift t_post))) t_r)
          have hr_c : closedAt k t_r := by
            have h := hc
            simp only [closedAt, Bool.and_eq_true] at h
            exact h.2
          have hinner_list : closedAtList (k + 1)
              (renameTermList (shiftRename 1) t_pre ++ [t_b] ++
               renameTermList (shiftRename 1) t_post) = true := by
            have h := hc
            simp only [closedAt, Bool.and_eq_true] at h
            exact h.1
          have hpre_sh_c := ((closedAtList_append (k + 1) _ _).mp
            ((closedAtList_append (k + 1) _ _).mp hinner_list).1).1
          have hbsingle_c := ((closedAtList_append (k + 1) _ _).mp
            ((closedAtList_append (k + 1) _ _).mp hinner_list).1).2
          have hpost_sh_c := ((closedAtList_append (k + 1) _ _).mp hinner_list).2
          have hb_c : closedAt (k + 1) t_b := by
            simp only [closedAtList, Bool.and_eq_true] at hbsingle_c
            exact hbsingle_c.1
          have hpre_c : closedAtList k t_pre = true :=
            closedAtList_renameTermList_shiftRename_inv t_pre k 1 (by omega) (by omega) hpre_sh_c
          have hpost_c : closedAtList k t_post = true :=
            closedAtList_renameTermList_shiftRename_inv t_post k 1 (by omega) (by omega) hpost_sh_c
          -- Goal: closedAt k (.Constr tag (t_pre ++ [.Apply (.Lam 0 t_b) t_r] ++ t_post))
          show closedAt k (.Constr tag _) = true
          simp only [closedAt]
          have hmid_list : closedAtList k
              [.Apply (.Lam 0 t_b) t_r] = true := by
            simp only [closedAtList, closedAt, Bool.and_eq_true]
            exact ⟨⟨hb_c, hr_c⟩, trivial⟩
          have h_step1 : closedAtList k
              (t_pre ++ [.Apply (.Lam 0 t_b) t_r]) = true :=
            (closedAtList_append k _ _).mpr ⟨hpre_c, hmid_list⟩
          exact (closedAtList_append k _ _).mpr ⟨h_step1, hpost_c⟩

theorem mirCtxRefines_let_hoist_constr_arg_fwd (tag : Nat) (pre : List Expr)
    (v : VarId) (rhs body : Expr) (post : List Expr)
    (hpre_atom : ∀ a ∈ pre, a.isAtom = true)
    (hpre_fresh : ∀ a ∈ pre, (freeVars a).contains v = false)
    (hpost_fresh : ∀ a ∈ post, (freeVars a).contains v = false) :
    MIRCtxRefines (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post))
                  (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post))) :=
  mirRefines_to_mirCtxRefines
    (mirRefines_let_hoist_constr_arg_fwd tag pre v rhs body post hpre_atom hpre_fresh hpost_fresh)
    (let_hoist_constr_arg_close_pres_fwd tag pre v rhs body post hpre_atom hpre_fresh hpost_fresh)

theorem mirCtxRefines_let_hoist_constr_arg_bwd (tag : Nat) (pre : List Expr)
    (v : VarId) (rhs body : Expr) (post : List Expr)
    (hpre_atom : ∀ a ∈ pre, a.isAtom = true)
    (hpre_fresh : ∀ a ∈ pre, (freeVars a).contains v = false)
    (hpost_fresh : ∀ a ∈ post, (freeVars a).contains v = false) :
    MIRCtxRefines (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post)))
                  (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post)) :=
  mirRefines_to_mirCtxRefines
    (mirRefines_let_hoist_constr_arg_bwd tag pre v rhs body post hpre_atom hpre_fresh hpost_fresh)
    (let_hoist_constr_arg_close_pres_bwd tag pre v rhs body post hpre_atom hpre_fresh hpost_fresh)

end Moist.Verified.MIR
