import Moist.Verified.MIR.Primitives.Shared
import Moist.Verified.MIR.Primitives.Atomize
import Moist.Verified.MIR.Primitives.LetFlattenBody
import Moist.Verified.MIR.Primitives.LetFlattenRhsHead
import Moist.Verified.MIR.Primitives.LetHoistForce
import Moist.Verified.MIR.Primitives.LetHoistAppLeft
import Moist.Verified.MIR.Primitives.LetHoistAppRightAtom
import Moist.Verified.MIR.Primitives.LetHoistCaseScrut
import Moist.Verified.MIR.Primitives.LetHoistConstrArg

namespace Moist.Verified.MIR

open Moist.CEK
open Moist.Plutus.Term (Term)
open Moist.MIR
  (Expr VarId anfNormalizeCore anfNormalizeListCore anfNormalizeBindsCore anfAtom anfAtomList
   wrapLet flattenLetBody freeVars lowerTotalExpr lowerTotal lowerTotalLet expandFix
   expandFixBinds freeVarsList)
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

/-- Underlying shape lemma: `.Let [] body` and `body` lower identically. -/
private theorem lowerTotalExpr_let_nil_body_eq (body : Expr) (env : List VarId) :
    lowerTotalExpr env (.Let [] body) = lowerTotalExpr env body := by
  show lowerTotal env (expandFix (.Let [] body)) = lowerTotal env (expandFix body)
  simp [expandFix, expandFixBinds, lowerTotal, lowerTotalLet]

/-- A helper: `.Let [] body` is equivalent to `body` under MIRCtxRefines. -/
theorem mirCtxRefines_let_nil_body (body : Expr) :
    MIRCtxRefines (.Let [] body) body := fun env => by
  rw [lowerTotalExpr_let_nil_body_eq body env]
  refine ⟨id, ?_⟩
  cases h : lowerTotalExpr env body with
  | none => trivial
  | some t => exact ctxRefines_refl t

theorem mirCtxRefines_let_nil_body_bwd (body : Expr) :
    MIRCtxRefines body (.Let [] body) := fun env => by
  rw [← lowerTotalExpr_let_nil_body_eq body env]
  refine ⟨id, ?_⟩
  cases h : lowerTotalExpr env (.Let [] body) with
  | none => trivial
  | some t => exact ctxRefines_refl t

/-! ### Section 12b-bis. Single-binding `er`-flag normalization

The `er` flag in `.Let` bindings is dropped at the lowering level (see
`lowerTotalLet`), so it doesn't affect `MIRCtxRefines`. For single-binding
`.Let [(v, rhs, er)] body`, this is easy to prove: both sides lower
identically. -/

private theorem lowerTotalExpr_let_cons_er_eq (v : VarId) (rhs : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) (env : List VarId) :
    lowerTotalExpr env (.Let ((v, rhs, er) :: rest) body) =
      lowerTotalExpr env (.Let ((v, rhs, false) :: rest) body) := by
  show lowerTotal env (expandFix _) = lowerTotal env (expandFix _)
  simp only [expandFix, expandFixBinds, lowerTotal, lowerTotalLet]

theorem mirCtxRefines_let_cons_er_normalize_fwd
    (v : VarId) (rhs : Expr) (er : Bool) (rest : List (VarId × Expr × Bool)) (body : Expr) :
    MIRCtxRefines (.Let ((v, rhs, er) :: rest) body)
                  (.Let ((v, rhs, false) :: rest) body) := fun env => by
  rw [lowerTotalExpr_let_cons_er_eq v rhs er rest body env]
  refine ⟨id, ?_⟩
  cases h : lowerTotalExpr env (.Let ((v, rhs, false) :: rest) body) with
  | none => trivial
  | some t => exact ctxRefines_refl t

theorem mirCtxRefines_let_cons_er_normalize_bwd
    (v : VarId) (rhs : Expr) (er : Bool) (rest : List (VarId × Expr × Bool)) (body : Expr) :
    MIRCtxRefines (.Let ((v, rhs, false) :: rest) body)
                  (.Let ((v, rhs, er) :: rest) body) := fun env => by
  rw [← lowerTotalExpr_let_cons_er_eq v rhs er rest body env]
  refine ⟨id, ?_⟩
  cases h : lowerTotalExpr env (.Let ((v, rhs, er) :: rest) body) with
  | none => trivial
  | some t => exact ctxRefines_refl t

/-! ### Section 12d. Iterated hoist helpers

These prove that multi-binding hoisting works by iterating the single-binding
primitive with a reshape via `mirCtxRefines_let_cons_split_*`. -/

/-- Helper: `wrapLet binds e = .Let binds e` when `binds ≠ []`; equals `e`
    otherwise. As an `MIRCtxRefines` equivalence. -/
theorem mirCtxRefines_wrapLet_eq_fwd (binds : List (VarId × Expr × Bool))
    (body : Expr) :
    MIRCtxRefines (wrapLet binds body) (.Let binds body) := by
  cases binds with
  | nil =>
    show MIRCtxRefines body (.Let [] body)
    exact mirCtxRefines_let_nil_body_bwd body
  | cons b rest =>
    rw [wrapLet_cons]
    exact mirCtxRefines_refl _

theorem mirCtxRefines_wrapLet_eq_bwd (binds : List (VarId × Expr × Bool))
    (body : Expr) :
    MIRCtxRefines (.Let binds body) (wrapLet binds body) := by
  cases binds with
  | nil =>
    show MIRCtxRefines (.Let [] body) body
    exact mirCtxRefines_let_nil_body body
  | cons b rest =>
    rw [wrapLet_cons]
    exact mirCtxRefines_refl _

/-- Iterated App-left hoist (forward): `.App (.Let binds body) xArg ≈
    .Let binds (.App body xArg)`, when every bind's name is fresh in `xArg`.
    Proved by induction on `binds`. -/
theorem mirCtxRefines_let_hoist_app_left_iter_fwd :
    ∀ (binds : List (VarId × Expr × Bool)) (body xArg : Expr),
      (∀ b ∈ binds, (freeVars xArg).contains b.1 = false) →
      MIRCtxRefines (.App (.Let binds body) xArg) (.Let binds (.App body xArg))
  | [], body, xArg, _ =>
    mirCtxRefines_trans
      (mirCtxRefines_app (mirCtxRefines_let_nil_body body) (mirCtxRefines_refl _))
      (mirCtxRefines_let_nil_body_bwd _)
  | (v, rhs, er) :: rest, body, xArg, hfresh => by
    have hv_fresh := hfresh (v, rhs, er) (List.Mem.head _)
    have hrest_fresh := fun b hb => hfresh b (List.Mem.tail _ hb)
    refine mirCtxRefines_trans
      (mirCtxRefines_app (mirCtxRefines_let_cons_er_normalize_fwd v rhs er rest body)
        (mirCtxRefines_refl _)) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_app (mirCtxRefines_let_cons_split_fwd _ _ _) (mirCtxRefines_refl _)) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_let_hoist_app_left_fwd v rhs (.Let rest body) xArg hv_fresh) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_let_body
        (mirCtxRefines_let_hoist_app_left_iter_fwd rest body xArg hrest_fresh)) ?_
    refine mirCtxRefines_trans (mirCtxRefines_let_cons_split_bwd _ _ _) ?_
    exact mirCtxRefines_let_cons_er_normalize_bwd v rhs er rest (.App body xArg)
  termination_by binds _ _ _ => binds.length

/-- Iterated App-left hoist (backward). -/
theorem mirCtxRefines_let_hoist_app_left_iter_bwd :
    ∀ (binds : List (VarId × Expr × Bool)) (body xArg : Expr),
      (∀ b ∈ binds, (freeVars xArg).contains b.1 = false) →
      MIRCtxRefines (.Let binds (.App body xArg)) (.App (.Let binds body) xArg)
  | [], body, xArg, _ =>
    mirCtxRefines_trans (mirCtxRefines_let_nil_body _)
      (mirCtxRefines_app (mirCtxRefines_let_nil_body_bwd body) (mirCtxRefines_refl _))
  | (v, rhs, er) :: rest, body, xArg, hfresh => by
    have hv_fresh := hfresh (v, rhs, er) (List.Mem.head _)
    have hrest_fresh := fun b hb => hfresh b (List.Mem.tail _ hb)
    refine mirCtxRefines_trans
      (mirCtxRefines_let_cons_er_normalize_fwd v rhs er rest (.App body xArg)) ?_
    refine mirCtxRefines_trans (mirCtxRefines_let_cons_split_fwd _ _ _) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_let_body
        (mirCtxRefines_let_hoist_app_left_iter_bwd rest body xArg hrest_fresh)) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_let_hoist_app_left_bwd v rhs (.Let rest body) xArg hv_fresh) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_app (mirCtxRefines_let_cons_split_bwd _ _ _) (mirCtxRefines_refl _)) ?_
    exact mirCtxRefines_app
      (mirCtxRefines_let_cons_er_normalize_bwd v rhs er rest body) (mirCtxRefines_refl _)
  termination_by binds _ _ _ => binds.length

/-- Iterated App-right-atom hoist (forward). -/
theorem mirCtxRefines_let_hoist_app_right_atom_iter_fwd :
    ∀ (binds : List (VarId × Expr × Bool)) (g body : Expr),
      g.isAtom = true →
      (∀ b ∈ binds, (freeVars g).contains b.1 = false) →
      MIRCtxRefines (.App g (.Let binds body)) (.Let binds (.App g body))
  | [], g, body, _, _ =>
    mirCtxRefines_trans
      (mirCtxRefines_app (mirCtxRefines_refl _) (mirCtxRefines_let_nil_body body))
      (mirCtxRefines_let_nil_body_bwd _)
  | (v, rhs, er) :: rest, g, body, hg, hfresh => by
    have hv_fresh := hfresh (v, rhs, er) (List.Mem.head _)
    have hrest_fresh := fun b hb => hfresh b (List.Mem.tail _ hb)
    refine mirCtxRefines_trans
      (mirCtxRefines_app (mirCtxRefines_refl _)
        (mirCtxRefines_let_cons_er_normalize_fwd v rhs er rest body)) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_app (mirCtxRefines_refl _) (mirCtxRefines_let_cons_split_fwd _ _ _)) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_let_hoist_app_right_atom_fwd v rhs (.Let rest body) g hg hv_fresh) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_let_body
        (mirCtxRefines_let_hoist_app_right_atom_iter_fwd rest g body hg hrest_fresh)) ?_
    refine mirCtxRefines_trans (mirCtxRefines_let_cons_split_bwd _ _ _) ?_
    exact mirCtxRefines_let_cons_er_normalize_bwd v rhs er rest (.App g body)
  termination_by binds _ _ _ _ => binds.length

/-- Iterated App-right-atom hoist (backward). -/
theorem mirCtxRefines_let_hoist_app_right_atom_iter_bwd :
    ∀ (binds : List (VarId × Expr × Bool)) (g body : Expr),
      g.isAtom = true →
      (∀ b ∈ binds, (freeVars g).contains b.1 = false) →
      MIRCtxRefines (.Let binds (.App g body)) (.App g (.Let binds body))
  | [], g, body, _, _ =>
    mirCtxRefines_trans (mirCtxRefines_let_nil_body _)
      (mirCtxRefines_app (mirCtxRefines_refl _) (mirCtxRefines_let_nil_body_bwd body))
  | (v, rhs, er) :: rest, g, body, hg, hfresh => by
    have hv_fresh := hfresh (v, rhs, er) (List.Mem.head _)
    have hrest_fresh := fun b hb => hfresh b (List.Mem.tail _ hb)
    refine mirCtxRefines_trans
      (mirCtxRefines_let_cons_er_normalize_fwd v rhs er rest (.App g body)) ?_
    refine mirCtxRefines_trans (mirCtxRefines_let_cons_split_fwd _ _ _) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_let_body
        (mirCtxRefines_let_hoist_app_right_atom_iter_bwd rest g body hg hrest_fresh)) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_let_hoist_app_right_atom_bwd v rhs (.Let rest body) g hg hv_fresh) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_app (mirCtxRefines_refl _) (mirCtxRefines_let_cons_split_bwd _ _ _)) ?_
    exact mirCtxRefines_app (mirCtxRefines_refl _)
      (mirCtxRefines_let_cons_er_normalize_bwd v rhs er rest body)
  termination_by binds _ _ _ _ => binds.length

/-- Iterated Force hoist (forward). No freshness needed. -/
theorem mirCtxRefines_let_hoist_force_iter_fwd :
    ∀ (binds : List (VarId × Expr × Bool)) (body : Expr),
      MIRCtxRefines (.Force (.Let binds body)) (.Let binds (.Force body))
  | [], body =>
    mirCtxRefines_trans
      (mirCtxRefines_force (mirCtxRefines_let_nil_body body))
      (mirCtxRefines_let_nil_body_bwd _)
  | (v, rhs, er) :: rest, body => by
    refine mirCtxRefines_trans
      (mirCtxRefines_force (mirCtxRefines_let_cons_er_normalize_fwd v rhs er rest body)) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_force (mirCtxRefines_let_cons_split_fwd _ _ _)) ?_
    refine mirCtxRefines_trans (mirCtxRefines_let_hoist_force_fwd v rhs (.Let rest body)) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_let_body (mirCtxRefines_let_hoist_force_iter_fwd rest body)) ?_
    refine mirCtxRefines_trans (mirCtxRefines_let_cons_split_bwd _ _ _) ?_
    exact mirCtxRefines_let_cons_er_normalize_bwd v rhs er rest (.Force body)
  termination_by binds _ => binds.length

/-- Iterated Force hoist (backward). -/
theorem mirCtxRefines_let_hoist_force_iter_bwd :
    ∀ (binds : List (VarId × Expr × Bool)) (body : Expr),
      MIRCtxRefines (.Let binds (.Force body)) (.Force (.Let binds body))
  | [], body =>
    mirCtxRefines_trans (mirCtxRefines_let_nil_body _)
      (mirCtxRefines_force (mirCtxRefines_let_nil_body_bwd body))
  | (v, rhs, er) :: rest, body => by
    refine mirCtxRefines_trans
      (mirCtxRefines_let_cons_er_normalize_fwd v rhs er rest (.Force body)) ?_
    refine mirCtxRefines_trans (mirCtxRefines_let_cons_split_fwd _ _ _) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_let_body (mirCtxRefines_let_hoist_force_iter_bwd rest body)) ?_
    refine mirCtxRefines_trans (mirCtxRefines_let_hoist_force_bwd v rhs (.Let rest body)) ?_
    refine mirCtxRefines_trans (mirCtxRefines_force (mirCtxRefines_let_cons_split_bwd _ _ _)) ?_
    exact mirCtxRefines_force (mirCtxRefines_let_cons_er_normalize_bwd v rhs er rest body)
  termination_by binds _ => binds.length

/-- `ListRel MIRCtxRefines` reflexivity. -/
theorem listRel_mirCtxRefines_refl : ∀ (l : List Expr), ListRel MIRCtxRefines l l
  | [] => True.intro
  | e :: rest => ⟨mirCtxRefines_refl e, listRel_mirCtxRefines_refl rest⟩

/-- `.Case (.Let [] body) alts ≈ .Case body alts` (let-nil reduces inside Case scrut). -/
theorem mirCtxRefines_case_let_nil_scrut (body : Expr) (alts : List Expr) :
    MIRCtxRefines (.Case (.Let [] body) alts) (.Case body alts) := by
  intro env
  have h : lowerTotalExpr env (.Case (.Let [] body) alts) =
           lowerTotalExpr env (.Case body alts) := by
    simp only [lowerTotalExpr, expandFix, expandFixBinds,
      lowerTotal, lowerTotalLet]
  rw [h]
  refine ⟨id, ?_⟩
  cases hl : lowerTotalExpr env (.Case body alts) with
  | none => trivial
  | some t => exact ctxRefines_refl t

theorem mirCtxRefines_case_let_nil_scrut_bwd (body : Expr) (alts : List Expr) :
    MIRCtxRefines (.Case body alts) (.Case (.Let [] body) alts) := by
  intro env
  have h : lowerTotalExpr env (.Case (.Let [] body) alts) =
           lowerTotalExpr env (.Case body alts) := by
    simp only [lowerTotalExpr, expandFix, expandFixBinds,
      lowerTotal, lowerTotalLet]
  rw [← h]
  refine ⟨id, ?_⟩
  cases hl : lowerTotalExpr env (.Case (.Let [] body) alts) with
  | none => trivial
  | some t => exact ctxRefines_refl t

/-- Iterated Case-scrutinee hoist (forward). -/
theorem mirCtxRefines_let_hoist_case_scrut_iter_fwd :
    ∀ (binds : List (VarId × Expr × Bool)) (body : Expr) (alts : List Expr),
      (∀ b ∈ binds, (freeVarsList alts).contains b.1 = false) →
      MIRCtxRefines (.Case (.Let binds body) alts) (.Let binds (.Case body alts))
  | [], body, alts, _ =>
    mirCtxRefines_trans (mirCtxRefines_case_let_nil_scrut body alts)
      (mirCtxRefines_let_nil_body_bwd _)
  | (v, rhs, er) :: rest, body, alts, hfresh => by
    have hv_fresh := hfresh (v, rhs, er) (List.Mem.head _)
    have hrest_fresh := fun b hb => hfresh b (List.Mem.tail _ hb)
    refine mirCtxRefines_trans
      (mirCtxRefines_case (mirCtxRefines_let_cons_er_normalize_fwd v rhs er rest body)
        (listRel_mirCtxRefines_refl alts)) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_case (mirCtxRefines_let_cons_split_fwd _ _ _)
        (listRel_mirCtxRefines_refl alts)) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_let_hoist_case_scrut_fwd v rhs (.Let rest body) alts hv_fresh) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_let_body
        (mirCtxRefines_let_hoist_case_scrut_iter_fwd rest body alts hrest_fresh)) ?_
    refine mirCtxRefines_trans (mirCtxRefines_let_cons_split_bwd _ _ _) ?_
    exact mirCtxRefines_let_cons_er_normalize_bwd v rhs er rest (.Case body alts)
  termination_by binds _ _ _ => binds.length

/-- Iterated Case-scrutinee hoist (backward). -/
theorem mirCtxRefines_let_hoist_case_scrut_iter_bwd :
    ∀ (binds : List (VarId × Expr × Bool)) (body : Expr) (alts : List Expr),
      (∀ b ∈ binds, (freeVarsList alts).contains b.1 = false) →
      MIRCtxRefines (.Let binds (.Case body alts)) (.Case (.Let binds body) alts)
  | [], body, alts, _ =>
    mirCtxRefines_trans (mirCtxRefines_let_nil_body _)
      (mirCtxRefines_case_let_nil_scrut_bwd body alts)
  | (v, rhs, er) :: rest, body, alts, hfresh => by
    have hv_fresh := hfresh (v, rhs, er) (List.Mem.head _)
    have hrest_fresh := fun b hb => hfresh b (List.Mem.tail _ hb)
    refine mirCtxRefines_trans
      (mirCtxRefines_let_cons_er_normalize_fwd v rhs er rest (.Case body alts)) ?_
    refine mirCtxRefines_trans (mirCtxRefines_let_cons_split_fwd _ _ _) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_let_body
        (mirCtxRefines_let_hoist_case_scrut_iter_bwd rest body alts hrest_fresh)) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_let_hoist_case_scrut_bwd v rhs (.Let rest body) alts hv_fresh) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_case (mirCtxRefines_let_cons_split_bwd _ _ _)
        (listRel_mirCtxRefines_refl alts)) ?_
    exact mirCtxRefines_case
      (mirCtxRefines_let_cons_er_normalize_bwd v rhs er rest body)
      (listRel_mirCtxRefines_refl alts)
  termination_by binds _ _ _ => binds.length

/-- `ListRel` preserved under append when the middle element is related and
    the prefix/suffix are equal. -/
theorem listRel_app_of_refl_mid {α : Type} {R : α → α → Prop}
    (hR_refl : ∀ a, R a a)
    {pre post : List α} {a b : α} (hab : R a b) :
    ListRel R (pre ++ [a] ++ post) (pre ++ [b] ++ post) := by
  induction pre with
  | nil =>
    show ListRel R (a :: post) (b :: post)
    refine ⟨hab, ?_⟩
    induction post with
    | nil => exact True.intro
    | cons p ps ih => exact ⟨hR_refl p, ih⟩
  | cons p ps ih =>
    show ListRel R (p :: (ps ++ [a] ++ post)) (p :: (ps ++ [b] ++ post))
    exact ⟨hR_refl p, ih⟩

/-- Simpler version specialized to `MIRCtxRefines` without the explicit refl
    argument. -/
theorem listRel_app_of_refl_mid_mirCtxRefines
    {pre post : List Expr} {a b : Expr} (hab : MIRCtxRefines a b) :
    ListRel MIRCtxRefines (pre ++ [a] ++ post) (pre ++ [b] ++ post) :=
  listRel_app_of_refl_mid mirCtxRefines_refl hab

/-- Constr congruence taking a `ListRel` on the argument list directly.
    This uses `mirCtxRefines_constr` but handles the nil arg case explicitly. -/
theorem mirCtxRefines_constr_of_listRel (tag : Nat) {args₁ args₂ : List Expr}
    (h : ListRel MIRCtxRefines args₁ args₂) :
    MIRCtxRefines (.Constr tag args₁) (.Constr tag args₂) := by
  cases args₁ with
  | nil =>
    cases args₂ with
    | nil => exact mirCtxRefines_refl _
    | cons _ _ => simp [ListRel] at h
  | cons a rest =>
    cases args₂ with
    | nil => simp [ListRel] at h
    | cons b rest' =>
      obtain ⟨hab, hrest⟩ := h
      exact mirCtxRefines_constr hab hrest

/-- Iterated Constr-arg hoist (forward). -/
theorem mirCtxRefines_let_hoist_constr_arg_iter_fwd :
    ∀ (binds : List (VarId × Expr × Bool)) (tag : Nat) (pre : List Expr) (body : Expr)
      (post : List Expr),
      (∀ a ∈ pre, a.isAtom = true) →
      (∀ a ∈ pre, ∀ b ∈ binds, (freeVars a).contains b.1 = false) →
      (∀ a ∈ post, ∀ b ∈ binds, (freeVars a).contains b.1 = false) →
      MIRCtxRefines (.Constr tag (pre ++ [.Let binds body] ++ post))
                    (.Let binds (.Constr tag (pre ++ [body] ++ post)))
  | [], tag, pre, body, post, _, _, _ => by
    have hmid : MIRCtxRefines (.Let [] body) body := mirCtxRefines_let_nil_body body
    have hrel : ListRel MIRCtxRefines (pre ++ [.Let [] body] ++ post)
                                      (pre ++ [body] ++ post) :=
      listRel_app_of_refl_mid (R := MIRCtxRefines) mirCtxRefines_refl hmid
    have h1 : MIRCtxRefines (.Constr tag (pre ++ [.Let [] body] ++ post))
                            (.Constr tag (pre ++ [body] ++ post)) :=
      mirCtxRefines_constr_of_listRel tag hrel
    have h2 : MIRCtxRefines (.Constr tag (pre ++ [body] ++ post))
                            (.Let [] (.Constr tag (pre ++ [body] ++ post))) :=
      mirCtxRefines_let_nil_body_bwd _
    exact mirCtxRefines_trans h1 h2
  | (v, rhs, er) :: rest, tag, pre, body, post, hpre_atom, hpre_fresh, hpost_fresh => by
    have hv_pre_fresh := fun a ha => hpre_fresh a ha (v, rhs, er) (List.Mem.head _)
    have hv_post_fresh := fun a ha => hpost_fresh a ha (v, rhs, er) (List.Mem.head _)
    have hrest_pre_fresh := fun a ha b hb => hpre_fresh a ha b (List.Mem.tail _ hb)
    have hrest_post_fresh := fun a ha b hb => hpost_fresh a ha b (List.Mem.tail _ hb)
    refine mirCtxRefines_trans
      (mirCtxRefines_constr_of_listRel tag
        (listRel_app_of_refl_mid_mirCtxRefines
          (mirCtxRefines_let_cons_er_normalize_fwd v rhs er rest body))) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_constr_of_listRel tag
        (listRel_app_of_refl_mid_mirCtxRefines
          (mirCtxRefines_let_cons_split_fwd _ _ _))) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_let_hoist_constr_arg_fwd tag pre v rhs (.Let rest body) post
        hpre_atom hv_pre_fresh hv_post_fresh) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_let_body
        (mirCtxRefines_let_hoist_constr_arg_iter_fwd rest tag pre body post
          hpre_atom hrest_pre_fresh hrest_post_fresh)) ?_
    refine mirCtxRefines_trans (mirCtxRefines_let_cons_split_bwd _ _ _) ?_
    exact mirCtxRefines_let_cons_er_normalize_bwd v rhs er rest _
  termination_by binds _ _ _ _ _ _ _ => binds.length

/-- Iterated Constr-arg hoist (backward). -/
theorem mirCtxRefines_let_hoist_constr_arg_iter_bwd :
    ∀ (binds : List (VarId × Expr × Bool)) (tag : Nat) (pre : List Expr) (body : Expr)
      (post : List Expr),
      (∀ a ∈ pre, a.isAtom = true) →
      (∀ a ∈ pre, ∀ b ∈ binds, (freeVars a).contains b.1 = false) →
      (∀ a ∈ post, ∀ b ∈ binds, (freeVars a).contains b.1 = false) →
      MIRCtxRefines (.Let binds (.Constr tag (pre ++ [body] ++ post)))
                    (.Constr tag (pre ++ [.Let binds body] ++ post))
  | [], tag, pre, body, post, _, _, _ => by
    have h1 : MIRCtxRefines (.Let [] (.Constr tag (pre ++ [body] ++ post)))
                            (.Constr tag (pre ++ [body] ++ post)) :=
      mirCtxRefines_let_nil_body _
    have hmid : MIRCtxRefines body (.Let [] body) := mirCtxRefines_let_nil_body_bwd body
    have hrel : ListRel MIRCtxRefines (pre ++ [body] ++ post)
                                      (pre ++ [.Let [] body] ++ post) :=
      listRel_app_of_refl_mid (R := MIRCtxRefines) mirCtxRefines_refl hmid
    have h2 : MIRCtxRefines (.Constr tag (pre ++ [body] ++ post))
                            (.Constr tag (pre ++ [.Let [] body] ++ post)) :=
      mirCtxRefines_constr_of_listRel tag hrel
    exact mirCtxRefines_trans h1 h2
  | (v, rhs, er) :: rest, tag, pre, body, post, hpre_atom, hpre_fresh, hpost_fresh => by
    have hv_pre_fresh := fun a ha => hpre_fresh a ha (v, rhs, er) (List.Mem.head _)
    have hv_post_fresh := fun a ha => hpost_fresh a ha (v, rhs, er) (List.Mem.head _)
    have hrest_pre_fresh := fun a ha b hb => hpre_fresh a ha b (List.Mem.tail _ hb)
    have hrest_post_fresh := fun a ha b hb => hpost_fresh a ha b (List.Mem.tail _ hb)
    refine mirCtxRefines_trans
      (mirCtxRefines_let_cons_er_normalize_fwd v rhs er rest _) ?_
    refine mirCtxRefines_trans (mirCtxRefines_let_cons_split_fwd _ _ _) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_let_body
        (mirCtxRefines_let_hoist_constr_arg_iter_bwd rest tag pre body post
          hpre_atom hrest_pre_fresh hrest_post_fresh)) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_let_hoist_constr_arg_bwd tag pre v rhs (.Let rest body) post
        hpre_atom hv_pre_fresh hv_post_fresh) ?_
    refine mirCtxRefines_trans
      (mirCtxRefines_constr_of_listRel tag
        (listRel_app_of_refl_mid_mirCtxRefines (mirCtxRefines_let_cons_split_bwd _ _ _))) ?_
    exact mirCtxRefines_constr_of_listRel tag
      (listRel_app_of_refl_mid_mirCtxRefines
        (mirCtxRefines_let_cons_er_normalize_bwd v rhs er rest body))
  termination_by binds _ _ _ _ _ _ _ => binds.length

/-! ### Section 12e-bis. Fix-non-Lam vacuous refinement helpers

For `.Fix f body` where `body` is not a `.Lam`, the lowering always returns
`none`, so any refinement with such a Fix on either side is vacuous. -/

theorem lowerTotalExpr_fix_nonlam_none' (env : List VarId) (f : VarId) (body : Expr)
    (h : ∀ (x : VarId) (inner : Expr), body ≠ .Lam x inner) :
    lowerTotalExpr env (.Fix f body) = none := by
  cases body <;>
    first
    | exact absurd rfl (h _ _)
    | simp only [lowerTotalExpr, expandFix, lowerTotal]

theorem mirCtxRefines_of_lhs_none' {m₁ m₂ : Expr}
    (h : ∀ env, lowerTotalExpr env m₁ = none) :
    MIRCtxRefines m₁ m₂ := by
  intro env
  refine ⟨?_, ?_⟩
  · intro hsome; rw [h env] at hsome; exact absurd hsome (by simp)
  · rw [h env]; trivial

/-- Specific version: Fix with non-Lam body on the LHS. -/
theorem mirCtxRefines_fix_nonlam_lhs {f : VarId} {body : Expr} {target : Expr}
    (h : ∀ (x : VarId) (inner : Expr), body ≠ .Lam x inner) :
    MIRCtxRefines (.Fix f body) target :=
  mirCtxRefines_of_lhs_none' (fun env => lowerTotalExpr_fix_nonlam_none' env f body h)

/-- Specific version: Fix with non-Lam body on the RHS. This requires showing
    the source also lowers to none (i.e., source has no halts/errors observable).
    For our use case, the source is itself a Fix with non-Lam body, so it
    also lowers to none. -/
theorem mirCtxRefines_fix_nonlam_both {f₁ f₂ : VarId} {body₁ body₂ : Expr}
    (h₁ : ∀ (x : VarId) (inner : Expr), body₁ ≠ .Lam x inner)
    (h₂ : ∀ (x : VarId) (inner : Expr), body₂ ≠ .Lam x inner) :
    MIRCtxRefines (.Fix f₁ body₁) (.Fix f₂ body₂) := by
  intro env
  have h1 : lowerTotalExpr env (.Fix f₁ body₁) = none :=
    lowerTotalExpr_fix_nonlam_none' env f₁ body₁ h₁
  have h2 : lowerTotalExpr env (.Fix f₂ body₂) = none :=
    lowerTotalExpr_fix_nonlam_none' env f₂ body₂ h₂
  rw [h1, h2]
  refine ⟨id, trivial⟩

end Moist.Verified.MIR
