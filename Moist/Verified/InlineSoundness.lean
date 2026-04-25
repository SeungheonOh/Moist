import Moist.Verified.MIR
import Moist.Verified.MIR.Congruence
import Moist.Verified.MIR.Primitives.Iterated
import Moist.Verified.DCESoundness
import Moist.Verified.DeadLet
import Moist.MIR.Canonicalize
import Moist.MIR.Optimize.Inline
import Moist.Verified.InlineSoundness.SubstCommute
import Moist.Verified.InlineSoundness.OccBridge
import Moist.Verified.InlineSoundness.WellScoped
import Moist.Verified.InlineSoundness.Preservation

/-! # Soundness of MIR Inlining Pass

Proves `inline_soundness : MIRCtxRefines e (inlinePass e s).1.1` for every
MIR expression `e` and every fresh-variable state `s`.

## Overview

The inlining pass walks the AST bottom-up and performs:

1. **Recursive descent** into sub-expressions (IH cases).
2. **Let-binding inlining** via `inlineLetBindings`: for each
   `let v = rhs in body`, decides to substitute the RHS into the body
   (and remaining RHS's) per `shouldInline`.
3. **Beta reduction** via `betaReduce`: applies
   `(.App (.Lam x body) arg) → subst x arg body` when `arg.isAtom`.

## Proof Strategy

* **Structural / congruence cases** (`Var`, `Lit`, `Builtin`, `Error`, `Lam`,
  `Fix`, `Force`, `Delay`, `Constr`, `Case`): compose through the matching
  `mirCtxRefines_*` congruence lemma from `Verified/MIR/Congruence.lean` and
  `Verified/DCESoundness.lean`.
* **App case**: `mirCtxRefines_app` + `betaReduce_soundness` helper.
* **Let case**: `mirCtxRefines_let_binds_congr` + `mirCtxRefines_let_body`
  + `inlineLetBindings_soundness` helper.

## Proof Architecture

This file is sorry-free. All preservation obligations are delegated to
`Moist.Verified.InlineSoundness.Preservation`, which provides:

* **`PairwiseNC`** — the inlineLetGo loop invariant, derivable from
  `wellScoped` and preservable through substitution.
* **`substInBindings_cross_nc`** — cross-binding NC preservation.
* **`inlinePass_pairwiseNC_cross`** — PairwiseNC preservation through
  the full inline pass (depends on `freeVars_nonincreasing` and
  `inlinePass_nc`, which are sorry'd in Preservation.lean). -/

namespace Moist.Verified.MIR

open Moist.CEK
open Moist.Plutus.Term (Term)
open Moist.MIR
  (Expr VarId VarSet inlinePass inlinePassList inlineBindings
   inlineLetBindings inlineLetGo betaReduce substInBindings
   shouldInline countOccurrences occursUnderFix
   lowerTotalExpr lowerTotal freeVars freeVarsList freeVarsLet
   subst substList substLet expandFix
   canonicalize wellScoped)
open Moist.Verified.InlineSoundness.SubstCommute
  (noCaptureFrom noCaptureFromList noCaptureFromLet
   noCaptureFrom_lam noCaptureFrom_fix noCaptureFrom_app
   noCaptureFrom_force noCaptureFrom_delay noCaptureFrom_constr
   noCaptureFrom_case noCaptureFrom_let
   noCaptureFromList_cons noCaptureFromLet_cons)
open Moist.Verified.InlineSoundness.WellScoped
open Moist.Verified.Contextual
  (Context fill ObsRefines CtxRefines
   ctxRefines_refl ctxRefines_trans)
open Moist.Verified.Equivalence (ListRel)

private def vs_union_l := @Moist.MIR.VarSet.contains_union_left
private def vs_union_r := @Moist.MIR.VarSet.contains_union_right
private def vs_union_split := @Moist.MIR.VarSet.union_not_contains'
private def vs_erase_split := @Moist.MIR.VarSet.erase_not_contains_imp'
private def vs_erase_ne := @Moist.MIR.VarSet.contains_erase_ne
private def efv := @Moist.MIR.expandFix_freeVars_not_contains
private def fv_subst_nc := @Moist.Verified.InlineSoundness.SubstCommute.freeVars_subst_not_contains

--------------------------------------------------------------------------------
-- 1. Definitional unfolding equations for `inlinePass` (on the `.1.1` projection)
--
-- The mutual `inlinePass` definition uses a catch-all for leaf cases
-- (Var/Lit/Builtin/Error), which can't be unfolded with `simp only
-- [inlinePass.eq_N]` directly — we use the catch-all `eq_9` with
-- proofs that the input is not a composite form.
--------------------------------------------------------------------------------

/-- Catch-all unfolding: for a leaf expression `e` (not Let/Lam/Fix/App/
    Force/Delay/Constr/Case), `inlinePass e s = ((e, false), s)`. -/
private theorem inlinePass_leaf {e : Expr}
    (hlet : ∀ bs b, e ≠ .Let bs b)
    (hlam : ∀ x b, e ≠ .Lam x b)
    (hfix : ∀ f b, e ≠ .Fix f b)
    (happ : ∀ f x, e ≠ .App f x)
    (hforce : ∀ inner, e ≠ .Force inner)
    (hdelay : ∀ inner, e ≠ .Delay inner)
    (hconstr : ∀ t args, e ≠ .Constr t args)
    (hcase : ∀ sc alts, e ≠ .Case sc alts)
    (s : Moist.MIR.FreshState) :
    inlinePass e s = ((e, false), s) := by
  rw [Moist.MIR.inlinePass.eq_9 e
        (fun bs b heq => hlet bs b heq)
        (fun x b heq => hlam x b heq)
        (fun f b heq => hfix f b heq)
        (fun f x heq => happ f x heq)
        (fun inner heq => hforce inner heq)
        (fun inner heq => hdelay inner heq)
        (fun t args heq => hconstr t args heq)
        (fun sc alts heq => hcase sc alts heq)]
  rfl

private theorem inlinePass_var_eq (v : VarId) (s : Moist.MIR.FreshState) :
    inlinePass (.Var v) s = ((.Var v, false), s) :=
  inlinePass_leaf
    (by intros; intro h; cases h) (by intros; intro h; cases h)
    (by intros; intro h; cases h) (by intros; intro h; cases h)
    (by intros; intro h; cases h) (by intros; intro h; cases h)
    (by intros; intro h; cases h) (by intros; intro h; cases h) s

private theorem inlinePass_lit_eq (c) (s : Moist.MIR.FreshState) :
    inlinePass (.Lit c) s = ((.Lit c, false), s) :=
  inlinePass_leaf
    (by intros; intro h; cases h) (by intros; intro h; cases h)
    (by intros; intro h; cases h) (by intros; intro h; cases h)
    (by intros; intro h; cases h) (by intros; intro h; cases h)
    (by intros; intro h; cases h) (by intros; intro h; cases h) s

private theorem inlinePass_builtin_eq (b) (s : Moist.MIR.FreshState) :
    inlinePass (.Builtin b) s = ((.Builtin b, false), s) :=
  inlinePass_leaf
    (by intros; intro h; cases h) (by intros; intro h; cases h)
    (by intros; intro h; cases h) (by intros; intro h; cases h)
    (by intros; intro h; cases h) (by intros; intro h; cases h)
    (by intros; intro h; cases h) (by intros; intro h; cases h) s

private theorem inlinePass_error_eq (s : Moist.MIR.FreshState) :
    inlinePass .Error s = ((.Error, false), s) :=
  inlinePass_leaf
    (by intros; intro h; cases h) (by intros; intro h; cases h)
    (by intros; intro h; cases h) (by intros; intro h; cases h)
    (by intros; intro h; cases h) (by intros; intro h; cases h)
    (by intros; intro h; cases h) (by intros; intro h; cases h) s

/-- Simplified projection: for a leaf expression, the result is unchanged. -/
private theorem inlinePass_var (v : VarId) (s : Moist.MIR.FreshState) :
    (inlinePass (.Var v) s).1.1 = .Var v := by
  rw [inlinePass_var_eq]

private theorem inlinePass_lit (c) (s : Moist.MIR.FreshState) :
    (inlinePass (.Lit c) s).1.1 = .Lit c := by
  rw [inlinePass_lit_eq]

private theorem inlinePass_builtin (b) (s : Moist.MIR.FreshState) :
    (inlinePass (.Builtin b) s).1.1 = .Builtin b := by
  rw [inlinePass_builtin_eq]

private theorem inlinePass_error (s : Moist.MIR.FreshState) :
    (inlinePass .Error s).1.1 = .Error := by
  rw [inlinePass_error_eq]

private theorem inlinePass_lam (x : VarId) (body : Expr) (s : Moist.MIR.FreshState) :
    (inlinePass (.Lam x body) s).1.1 = .Lam x (inlinePass body s).1.1 := by
  simp only [Moist.MIR.inlinePass.eq_2]
  rfl

private theorem inlinePass_fix (f : VarId) (body : Expr) (s : Moist.MIR.FreshState) :
    (inlinePass (.Fix f body) s).1.1 = .Fix f (inlinePass body s).1.1 := by
  simp only [Moist.MIR.inlinePass.eq_3]
  rfl

private theorem inlinePass_force (e : Expr) (s : Moist.MIR.FreshState) :
    (inlinePass (.Force e) s).1.1 = .Force (inlinePass e s).1.1 := by
  simp only [Moist.MIR.inlinePass.eq_5]
  rfl

private theorem inlinePass_delay (e : Expr) (s : Moist.MIR.FreshState) :
    (inlinePass (.Delay e) s).1.1 = .Delay (inlinePass e s).1.1 := by
  simp only [Moist.MIR.inlinePass.eq_6]
  rfl

private theorem inlinePass_constr (tag : Nat) (args : List Expr)
    (s : Moist.MIR.FreshState) :
    (inlinePass (.Constr tag args) s).1.1 = .Constr tag (inlinePassList args s).1.1 := by
  simp only [Moist.MIR.inlinePass.eq_7]
  rfl

private theorem inlinePass_case (scrut : Expr) (alts : List Expr)
    (s : Moist.MIR.FreshState) :
    (inlinePass (.Case scrut alts) s).1.1 =
      .Case (inlinePass scrut s).1.1
            (inlinePassList alts (inlinePass scrut s).2).1.1 := by
  simp only [Moist.MIR.inlinePass.eq_8]
  rfl

private theorem inlinePass_app (f x : Expr) (s : Moist.MIR.FreshState) :
    (inlinePass (.App f x) s).1.1 =
      (betaReduce (inlinePass f s).1.1
        (inlinePass x (inlinePass f s).2).1.1
        (inlinePass x (inlinePass f s).2).2).1.1 := by
  simp only [Moist.MIR.inlinePass.eq_4]
  rfl

private theorem inlinePass_let (binds : List (VarId × Expr × Bool)) (body : Expr)
    (s : Moist.MIR.FreshState) :
    (inlinePass (.Let binds body) s).1.1 =
      (inlineLetBindings (inlineBindings binds s).1.1
        (inlinePass body (inlineBindings binds s).2).1.1
        (inlinePass body (inlineBindings binds s).2).2).1.1 := by
  simp only [Moist.MIR.inlinePass.eq_1]
  rfl

-- inlinePassList unfolding

private theorem inlinePassList_nil (s : Moist.MIR.FreshState) :
    (inlinePassList ([] : List Expr) s).1.1 = [] := by
  rw [Moist.MIR.inlinePassList.eq_1]; rfl

private theorem inlinePassList_cons_eq (e : Expr) (rest : List Expr)
    (s : Moist.MIR.FreshState) :
    (inlinePassList (e :: rest) s).1.1 =
      (inlinePass e s).1.1 ::
        (inlinePassList rest (inlinePass e s).2).1.1 := by
  simp only [Moist.MIR.inlinePassList.eq_2]
  rfl

-- inlineBindings unfolding

private theorem inlineBindings_nil (s : Moist.MIR.FreshState) :
    (inlineBindings ([] : List (VarId × Expr × Bool)) s).1.1 = [] := by
  rw [Moist.MIR.inlineBindings.eq_1]; rfl

private theorem inlineBindings_cons_eq (v : VarId) (rhs : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (s : Moist.MIR.FreshState) :
    (inlineBindings ((v, rhs, er) :: rest) s).1.1 =
      (v, (inlinePass rhs s).1.1, er) ::
        (inlineBindings rest (inlinePass rhs s).2).1.1 := by
  simp only [Moist.MIR.inlineBindings.eq_2]
  rfl

--------------------------------------------------------------------------------
-- 1b. Utility: MIRCtxRefines from universal lowerTotalExpr equality
--------------------------------------------------------------------------------

/-- If two MIR expressions have the same lowering in every environment,
    they are `MIRCtxRefines`-equivalent (both directions). -/
private theorem mirCtxRefines_of_lowerEq {m₁ m₂ : Expr}
    (h : ∀ env, lowerTotalExpr env m₁ = lowerTotalExpr env m₂) :
    MIRCtxRefines m₁ m₂ := by
  intro env
  rw [h env]
  refine ⟨id, ?_⟩
  cases hlow : lowerTotalExpr env m₂ with
  | none => trivial
  | some t => exact ctxRefines_refl t

/-- Shorthand: the `shouldInline` condition that the inline pass checks
    before substituting `rhs` for `v` in `body` and `rest`. This gates
    the substitution on one of the four `shouldInline` branches (atom /
    small value/pure / single-use value/pure / single-use impure strict). -/
def InlineGate (v : VarId) (rhs body : Expr)
    (rest : List (VarId × Expr × Bool)) : Bool :=
  Moist.MIR.shouldInline rhs
    (Moist.MIR.countOccurrences v body +
      rest.foldl (fun n (_, e, _) => n + Moist.MIR.countOccurrences v e) 0)
    (Moist.MIR.occursUnderFix v body ||
      rest.any (fun (_, e, _) => Moist.MIR.occursUnderFix v e))
    (Moist.MIR.occursInDeferred v body ||
      rest.any (fun (_, e, _) => Moist.MIR.occursInDeferred v e))

/-- Core substitution-inline sub-theorem (unified form). For every
    `let ((v, rhs, er) :: rest) in body`, the split-substitution form
    that `inlineLetGo` produces (substituting `rhs` into `body` directly
    and into each `rest` RHS via `substInBindings`) is contextually
    refined by the let form.

    This is the direction used by the inlining pass: the original let is
    refined by its substituted form. Under call-by-value, this is sound
    exactly when `shouldInline` returns true (atomic / small value/pure /
    single-use value/pure / single-use impure strict) — hence the
    `InlineGate` hypothesis. See the prior scope analysis above for why
    the unconditional form is unsound (counterexample: `rhs = .Error`
    with `v` unused in `body`).

    The special case with `rest = []` handles the beta-reduction case
    in `betaReduce_soundness`: when `rest = []`, `substInBindings v rhs []`
    returns `([], rfl)` and the let reduces to just the body substitution. -/
theorem substInBindings_body_inline_mirCtxRefines (v : VarId) (rhs body : Expr)
    (er : Bool) (rest : List (VarId × Expr × Bool))
    (s : Moist.MIR.FreshState)
    (hgate : InlineGate v rhs body rest = true)
    (distinct_binders : Moist.MIR.distinctBinders ((v, rhs, er) :: rest) = true)
    (h_nc_body : Moist.Verified.InlineSoundness.SubstCommute.noCaptureFrom
                   (Moist.MIR.freeVars rhs) body = true)
    (h_nc_rest : rest.all (fun b => Moist.Verified.InlineSoundness.SubstCommute.noCaptureFrom
                                      (Moist.MIR.freeVars rhs) b.2.1) = true)
    (h_binders_fresh : rest.all
        (fun b => !(Moist.MIR.freeVars (Moist.MIR.expandFix rhs)).contains b.1) = true) :
    MIRCtxRefines
      (.Let ((v, rhs, er) :: rest) body)
      (.Let (Moist.MIR.substInBindings v rhs rest
              (Moist.MIR.subst v rhs body s).2).1.val
            (Moist.MIR.subst v rhs body s).1) := by
  open Moist.Verified.InlineSoundness.SubstCommute in
  open Moist.MIR (lowerTotal lowerTotalLet expandFix expandFixBinds lowerTotalExpr
    shouldInline countOccurrences occursUnderFix occursInDeferred) in
  open Moist.Verified.MIR (lowerTotal_closedAt lowerTotalLet_closedAt
    lowerTotal_atom_isLeafAtom isLeafAtomTerm) in
  intro env
  refine ⟨subst_compile_preservation v rhs body er rest s env distinct_binders
            h_nc_body h_nc_rest h_binders_fresh, ?ctx⟩
  case ctx =>
    cases h_lhs : lowerTotalExpr env (.Let ((v, rhs, er) :: rest) body) with
    | none => trivial
    | some t_lhs =>
      cases h_rhs_low : lowerTotalExpr env
          (.Let (Moist.MIR.substInBindings v rhs rest
            (Moist.MIR.subst v rhs body s).2).1.val
            (Moist.MIR.subst v rhs body s).1) with
      | none => trivial
      | some t_rhs_lowered =>
        -- Decompose LHS compilation into t_rhs (compiled rhs) and t_rest (compiled rest+body)
        have hlhs_unfold : lowerTotalExpr env (.Let ((v, rhs, er) :: rest) body) =
            (do let rhs' ← lowerTotal env (expandFix rhs)
                let rest' ← lowerTotalLet (v :: env) (expandFixBinds rest) (expandFix body)
                some (.Apply (.Lam 0 rest') rhs')) := by
          simp only [lowerTotalExpr, expandFix, expandFixBinds, lowerTotal, lowerTotalLet]
        rw [hlhs_unfold] at h_lhs
        have h_rhs_some : ∃ t_rhs, lowerTotal env (expandFix rhs) = some t_rhs := by
          revert h_lhs; cases lowerTotal env (expandFix rhs) <;> simp
        obtain ⟨t_rhs, ht_rhs⟩ := h_rhs_some
        rw [ht_rhs] at h_lhs; simp at h_lhs
        have h_rest_some : ∃ t_rest,
            lowerTotalLet (v :: env) (expandFixBinds rest) (expandFix body) = some t_rest := by
          revert h_lhs
          cases lowerTotalLet (v :: env) (expandFixBinds rest) (expandFix body) <;> simp
        obtain ⟨t_rest, ht_rest⟩ := h_rest_some
        rw [ht_rest] at h_lhs; simp at h_lhs; subst h_lhs
        -- RHS compiles to substTerm 1 t_rhs t_rest (by commutation)
        have hcomm := substInBindings_lowerTotalLet_comm v rhs rest body er env s t_rest t_rhs distinct_binders
          h_nc_body h_nc_rest h_binders_fresh ht_rest ht_rhs
        have hrhs_unfold : lowerTotalExpr env
            (.Let (Moist.MIR.substInBindings v rhs rest
              (Moist.MIR.subst v rhs body s).2).1.val
              (Moist.MIR.subst v rhs body s).1) =
            lowerTotalLet env
              (expandFixBinds (Moist.MIR.substInBindings v rhs rest
                (Moist.MIR.subst v rhs body s).2).1.val)
              (expandFix (Moist.MIR.subst v rhs body s).1) := by
          simp only [lowerTotalExpr, expandFix, lowerTotal]
        rw [hrhs_unfold, hcomm] at h_rhs_low; injection h_rhs_low with h_rhs_eq
        rw [← h_rhs_eq]
        -- Closedness from compilation
        have hclosed_rhs : closedAt env.length t_rhs = true :=
          lowerTotal_closedAt env _ t_rhs ht_rhs
        have hclosed_rest : closedAt (env.length + 1) t_rest = true := by
          have := lowerTotalLet_closedAt (v :: env) _ _ t_rest ht_rest
          simpa [List.length] using this
        -- Dispatch: all branches of shouldInline yield
        -- CtxRefines (.Apply (.Lam 0 t_rest) t_rhs) (substTerm 1 t_rhs t_rest)
        unfold InlineGate at hgate
        let occ := countOccurrences v body +
          rest.foldl (fun n (_, e, _) => n + countOccurrences v e) 0
        let uf := Moist.MIR.occursUnderFix v body ||
          rest.any (fun (_, e, _) => Moist.MIR.occursUnderFix v e)
        let id := Moist.MIR.occursInDeferred v body ||
          rest.any (fun (_, e, _) => Moist.MIR.occursInDeferred v e)
        change shouldInline rhs occ uf id = true at hgate
        unfold shouldInline at hgate
        split at hgate
        · -- Branch A: atom — case split on compiled atom shape
          rename_i hatom
          have h_leaf := lowerTotal_atom_isLeafAtom env rhs t_rhs hatom ht_rhs
          rcases h_leaf with ⟨n, hn, rfl⟩ | ⟨ct, rfl⟩ | ⟨b, rfl⟩
          · -- Var n (n ≥ 1): substitution equals renaming
            have hnd : n ≤ env.length := by
              change closedAt env.length (.Var n) = true at hclosed_rhs
              simp only [Moist.Verified.closedAt] at hclosed_rhs
              exact of_decide_eq_true hclosed_rhs
            exact uplc_beta_var_openRefines hclosed_rest hn hnd
          · exact uplc_beta_constant_ctxRefines hclosed_rest
          · exact uplc_beta_builtin_ctxRefines hclosed_rest
        · split at hgate
          · -- Branch B: value/pure — case split on occ=1 availability
            by_cases hocc_uf : (occ == 1 && !uf) = true
            · rw [Bool.and_eq_true] at hocc_uf
              have hocc : occ = 1 := by
                have := hocc_uf.1; simp [BEq.beq] at this; exact this
              by_cases hid : id = false
              · exact uplc_beta_impure_strict_openRefines hclosed_rest hclosed_rhs
                  (Moist.Verified.InlineSoundness.OccBridge.lowerTotalLet_strictSingleOcc_of_inlineGate
                    v env rest body t_rest ht_rest hocc hid distinct_binders)
              · -- occ=1, occurrence in deferred position
                have h_single := Moist.Verified.InlineSoundness.OccBridge.lowerTotalLet_singleOcc_of_occ_one
                  v env rest body t_rest ht_rest hocc distinct_binders
                by_cases hpure : (Moist.MIR.isPure rhs) = true
                · exact uplc_beta_single_pure_openRefines hclosed_rest hclosed_rhs h_single
                    (fun ρ hwf π =>
                      Moist.Verified.DeadLet.dead_let_pure_stack_poly env
                        (Moist.MIR.expandFix rhs)
                        (Moist.Verified.Purity.isPure_expandFix rhs hpure)
                        ht_rhs hwf π)
                · -- isValue but not isPure: must be Fix f (Lam x inner).
                  -- Extract Fix shape from ht_rhs (lowerTotal on non-Lam Fix = none → contradiction)
                  rename_i hval_or
                  have hval : Moist.MIR.Expr.isValue rhs = true := by
                    rcases Bool.or_eq_true_iff.mp hval_or with h | h
                    · exact h
                    · exact absurd h hpure
                  have h_canon : ∃ body_l, t_rhs = Moist.MIR.fixLamWrapUplc body_l := by
                    cases rhs with
                    | Var _ | Lit _ | Builtin _ => simp [Moist.MIR.Expr.isAtom] at *
                    | Lam _ _ | Delay _ => simp [Moist.MIR.isPure] at hpure
                    | Fix f_id fix_body =>
                      cases fix_body with
                      | Lam x_id inner =>
                        have := Moist.MIR.lowerTotalExpr_fix_lam_canonical env f_id x_id inner
                        rw [show Moist.MIR.lowerTotalExpr env (.Fix f_id (.Lam x_id inner)) =
                          lowerTotal env (Moist.MIR.expandFix (.Fix f_id (.Lam x_id inner))) from rfl,
                          ht_rhs] at this
                        revert this
                        cases lowerTotal _ (Moist.MIR.expandFix inner) with
                        | none => simp
                        | some bl => simp; intro h; exact ⟨bl, h⟩
                      | _ => exfalso; revert ht_rhs
                             simp [Moist.MIR.expandFix, lowerTotal]
                    | _ => simp [Moist.MIR.Expr.isValue] at hval
                  obtain ⟨body_l, rfl⟩ := h_canon
                  exact uplc_beta_single_pure_openRefines hclosed_rest hclosed_rhs h_single
                    (fun ρ _hwf π => fixLamWrapUplc_halts body_l ρ π)
            · -- exprSize ≤ inlineThreshold (small value/pure, occ may be > 1).
              rename_i hval_or
              by_cases hpure2 : (Moist.MIR.isPure rhs) = true
              · exact uplc_beta_multi_pure_openRefines hclosed_rest hclosed_rhs
                  (fun ρ hwf π =>
                    Moist.Verified.DeadLet.dead_let_pure_stack_poly env
                      (Moist.MIR.expandFix rhs)
                      (Moist.Verified.Purity.isPure_expandFix rhs hpure2)
                      ht_rhs hwf π)
              · -- Fix case (isValue, ¬isPure, small)
                have hval : Moist.MIR.Expr.isValue rhs = true := by
                  rcases Bool.or_eq_true_iff.mp hval_or with h | h
                  · exact h
                  · exact absurd h hpure2
                have h_canon : ∃ body_l, t_rhs = Moist.MIR.fixLamWrapUplc body_l := by
                  cases rhs with
                  | Var _ | Lit _ | Builtin _ => simp [Moist.MIR.Expr.isAtom] at *
                  | Lam _ _ | Delay _ => simp [Moist.MIR.isPure] at hpure2
                  | Fix f_id fix_body =>
                    cases fix_body with
                    | Lam x_id inner =>
                      have := Moist.MIR.lowerTotalExpr_fix_lam_canonical env f_id x_id inner
                      rw [show Moist.MIR.lowerTotalExpr env (.Fix f_id (.Lam x_id inner)) =
                        lowerTotal env (Moist.MIR.expandFix (.Fix f_id (.Lam x_id inner))) from rfl,
                        ht_rhs] at this
                      revert this
                      cases lowerTotal _ (Moist.MIR.expandFix inner) with
                      | none => simp
                      | some bl => simp; intro h; exact ⟨bl, h⟩
                    | _ => exfalso; revert ht_rhs; simp [Moist.MIR.expandFix, lowerTotal]
                  | _ => simp [Moist.MIR.Expr.isValue] at hval
                obtain ⟨body_l, rfl⟩ := h_canon
                exact uplc_beta_multi_pure_openRefines hclosed_rest hclosed_rhs
                  (fun ρ _hwf π => fixLamWrapUplc_halts body_l ρ π)
          · -- Branch C: impure strict — extract conditions from InlineGate
            rw [Bool.and_eq_true] at hgate
            have hocc : occ = 1 := by
              have := hgate.1; simp [BEq.beq] at this; exact this
            have hnotid : id = false := by
              have := hgate.2; revert this; cases h : id <;> simp
            exact uplc_beta_impure_strict_openRefines hclosed_rest hclosed_rhs
              (Moist.Verified.InlineSoundness.OccBridge.lowerTotalLet_strictSingleOcc_of_inlineGate
                v env rest body t_rest ht_rest hocc hnotid
                distinct_binders)

/-- Atoms always satisfy `InlineGate`: `shouldInline` for an atom expression
    returns `true` unconditionally (atoms are free to duplicate). -/
private theorem InlineGate_of_atom (v : VarId) (rhs body : Expr)
    (rest : List (VarId × Expr × Bool)) (hatom : rhs.isAtom = true) :
    InlineGate v rhs body rest = true := by
  unfold InlineGate
  unfold Moist.MIR.shouldInline
  simp [hatom]

/-- Specialization: when `rest = []`, the inline form reduces to just
    the body substitution. Requires `InlineGate` to hold. -/
private theorem subst_body_inline_mirCtxRefines (v : VarId) (rhs body : Expr)
    (er : Bool) (s : Moist.MIR.FreshState)
    (hgate : InlineGate v rhs body [] = true)
    (distinct_binders : Moist.MIR.distinctBinders [(v, rhs, er)] = true)
    (h_nc_body : Moist.Verified.InlineSoundness.SubstCommute.noCaptureFrom
                   (Moist.MIR.freeVars rhs) body = true) :
    MIRCtxRefines (.Let [(v, rhs, er)] body) (Moist.MIR.subst v rhs body s).1 := by
  have h := substInBindings_body_inline_mirCtxRefines v rhs body er [] s hgate
              distinct_binders h_nc_body (by rfl) (by rfl)
  -- substInBindings v rhs [] = pure ⟨[], rfl⟩, so the result is .Let [] body'
  -- where body' = (subst v rhs body s).1. This is MIRCtxRefines to body' via
  -- mirCtxRefines_let_nil.
  have heq : (Moist.MIR.substInBindings v rhs []
              (Moist.MIR.subst v rhs body s).2).1.val = ([] : List (VarId × Expr × Bool)) := by
    -- substInBindings v rhs [] s = pure ⟨[], rfl⟩
    show (Moist.MIR.substInBindings v rhs [] _).1.val = _
    rfl
  rw [heq] at h
  -- h : MIRCtxRefines (.Let [(v, rhs, er)] body) (.Let [] (subst v rhs body s).1)
  exact mirCtxRefines_trans h mirCtxRefines_let_nil

/-- Equivalence between `.App (.Lam p body) x` and `.Let [(p, x, false)] body`
    at the `MIRCtxRefines` level: they have *identical* lowerings (both
    reduce to `.Apply (.Lam 0 body_lowered) x_lowered`), modulo the order
    of bindings in the `do`-notation. -/
private theorem mirCtxRefines_app_lam_to_let (p : VarId) (body x : Expr) :
    MIRCtxRefines (.App (.Lam p body) x) (.Let [(p, x, false)] body) := by
  intro env
  have heq : lowerTotalExpr env (.App (.Lam p body) x) =
             lowerTotalExpr env (.Let [(p, x, false)] body) := by
    -- Both sides expand to the same UPLC term via expandFix + lowerTotal,
    -- but the do-bindings have different orders; unfold fully and case-split.
    simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.expandFixBinds,
      Moist.MIR.lowerTotal, Moist.MIR.lowerTotalLet]
    cases h_body : Moist.MIR.lowerTotal (p :: env) (Moist.MIR.expandFix body) with
    | none => simp
    | some body' =>
      cases h_x : Moist.MIR.lowerTotal env (Moist.MIR.expandFix x) with
      | none => simp
      | some x' => simp
  rw [heq]
  refine ⟨id, ?_⟩
  cases h : lowerTotalExpr env (.Let [(p, x, false)] body) with
  | none => trivial
  | some t => exact ctxRefines_refl t

--------------------------------------------------------------------------------
-- 3. `betaReduce_soundness`: soundness of the beta-reduction step
--------------------------------------------------------------------------------

/-- Soundness of `betaReduce`: when `f` is a lambda and `x` is an atom,
    `.App f x` contextually refines the beta-reduced substitution.
    Otherwise the result is structurally the same — reflexivity.

    The `Lam + atom` case composes `mirCtxRefines_app_lam_to_let`
    (equivalence of `.App (.Lam p body) x` with
    `.Let [(p, x, false)] body`) with the substitution-inline sub-theorem
    `subst_inline_mirCtxRefines`. -/
theorem betaReduce_soundness (f x : Expr) (s : Moist.MIR.FreshState)
    (hncf : ∀ (p : VarId) (b : Expr), f = .Lam p b →
            Moist.Verified.InlineSoundness.SubstCommute.noCaptureFrom
              (Moist.MIR.freeVars x) b = true) :
    MIRCtxRefines (.App f x) (betaReduce f x s).1.1 := by
  cases f with
  | Lam param body =>
    by_cases hxa : x.isAtom = true
    · -- betaReduce returns (subst param x body, true)
      -- compose: .App (.Lam param body) x ≈ .Let [(param, x, false)] body ⊑ subst
      have heq : (betaReduce (.Lam param body) x s).1.1 = (subst param x body s).1 := by
        show ((match (Expr.Lam param body : Expr) with
              | .Lam p b =>
                if x.isAtom then do
                  let result ← subst p x b
                  pure (result, true)
                else
                  pure (.App (.Lam p b) x, false)
              | _ => pure (.App (.Lam param body) x, false)) s).1.1 = _
        simp only [hxa, ↓reduceIte]
        rfl
      rw [heq]
      have hgate : InlineGate param x body [] = true :=
        InlineGate_of_atom param x body [] hxa
      exact mirCtxRefines_trans
        (mirCtxRefines_app_lam_to_let param body x)
        (subst_body_inline_mirCtxRefines param x body false s hgate
          (by simp [Moist.MIR.distinctBinders])
          (hncf param body rfl))
    · -- betaReduce returns (.App (.Lam param body) x, false) unchanged
      have hxa' : x.isAtom = false := by
        cases hh : x.isAtom with
        | true => exact absurd hh hxa
        | false => rfl
      have heq : (betaReduce (.Lam param body) x s).1.1 = .App (.Lam param body) x := by
        show ((match (Expr.Lam param body : Expr) with
              | .Lam p b =>
                if x.isAtom then do
                  let result ← subst p x b
                  pure (result, true)
                else
                  pure (.App (.Lam p b) x, false)
              | _ => pure (.App (.Lam param body) x, false)) s).1.1 = _
        simp only [hxa', Bool.false_eq_true, ↓reduceIte]
        rfl
      rw [heq]
      exact mirCtxRefines_refl _
  | Var v =>
    have heq : (betaReduce (.Var v) x s).1.1 = .App (.Var v) x := rfl
    rw [heq]; exact mirCtxRefines_refl _
  | Lit c =>
    have heq : (betaReduce (.Lit c) x s).1.1 = .App (.Lit c) x := rfl
    rw [heq]; exact mirCtxRefines_refl _
  | Builtin b =>
    have heq : (betaReduce (.Builtin b) x s).1.1 = .App (.Builtin b) x := rfl
    rw [heq]; exact mirCtxRefines_refl _
  | Error =>
    have heq : (betaReduce .Error x s).1.1 = .App .Error x := rfl
    rw [heq]; exact mirCtxRefines_refl _
  | Fix g body =>
    have heq : (betaReduce (.Fix g body) x s).1.1 = .App (.Fix g body) x := rfl
    rw [heq]; exact mirCtxRefines_refl _
  | App fn arg =>
    have heq : (betaReduce (.App fn arg) x s).1.1 = .App (.App fn arg) x := rfl
    rw [heq]; exact mirCtxRefines_refl _
  | Force e =>
    have heq : (betaReduce (.Force e) x s).1.1 = .App (.Force e) x := rfl
    rw [heq]; exact mirCtxRefines_refl _
  | Delay e =>
    have heq : (betaReduce (.Delay e) x s).1.1 = .App (.Delay e) x := rfl
    rw [heq]; exact mirCtxRefines_refl _
  | Constr tag args =>
    have heq : (betaReduce (.Constr tag args) x s).1.1 = .App (.Constr tag args) x := rfl
    rw [heq]; exact mirCtxRefines_refl _
  | Case scrut alts =>
    have heq : (betaReduce (.Case scrut alts) x s).1.1 = .App (.Case scrut alts) x := rfl
    rw [heq]; exact mirCtxRefines_refl _
  | Let binds body =>
    have heq : (betaReduce (.Let binds body) x s).1.1 = .App (.Let binds body) x := rfl
    rw [heq]; exact mirCtxRefines_refl _

--------------------------------------------------------------------------------
-- 3. `inlineLetBindings_soundness`: soundness of the let-inlining decision loop
--------------------------------------------------------------------------------

/-! ### Helper lemmas: structural rearrangement of nested lets -/

/-- Nested-let equality for `lowerTotalLet`: `.Let (A ++ B) body` unfolds
    to the same term as `.Let A (.Let B body)` at any env. Proved by
    induction on `A`. -/
private theorem lowerTotalLet_append (env : List VarId)
    (A B : List (VarId × Expr × Bool)) (body' : Expr) :
    Moist.MIR.lowerTotalLet env (A ++ B) body' =
    Moist.MIR.lowerTotalLet env A (.Let B body') := by
  induction A generalizing env with
  | nil =>
    simp only [List.nil_append, Moist.MIR.lowerTotalLet, Moist.MIR.lowerTotal]
  | cons bh rest_A ih =>
    obtain ⟨v, rhs, er⟩ := bh
    simp only [List.cons_append, Moist.MIR.lowerTotalLet, Option.bind_eq_bind]
    cases hrhs : Moist.MIR.lowerTotal env rhs with
    | none => simp
    | some r =>
      simp only [Option.bind_some]
      exact congrArg
        (fun t => Option.bind t (fun rest' =>
          some (Moist.Plutus.Term.Term.Apply (Moist.Plutus.Term.Term.Lam 0 rest') r)))
        (ih (v :: env))

private theorem lowerTotalExpr_let_split (env : List VarId)
    (binds1 binds2 : List (VarId × Expr × Bool)) (body : Expr) :
    lowerTotalExpr env (.Let (binds1 ++ binds2) body) =
    lowerTotalExpr env (.Let binds1 (.Let binds2 body)) := by
  -- Both sides unfold through `expandFix` and `lowerTotalLet`. Induct on binds1.
  have hexp_split :
      Moist.MIR.expandFixBinds (binds1 ++ binds2) =
      Moist.MIR.expandFixBinds binds1 ++ Moist.MIR.expandFixBinds binds2 := by
    induction binds1 with
    | nil => simp [Moist.MIR.expandFixBinds]
    | cons b rest ih =>
      obtain ⟨v, rhs, er⟩ := b
      simp [Moist.MIR.expandFixBinds, ih]
  simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.lowerTotal,
    hexp_split]
  exact lowerTotalLet_append env _ _ _

/-! ### Generalized soundness of the inlining decision loop

The inlining decision loop has the shape:
  inlineLetGo (head :: rest) acc body changed s
    = if shouldInline ... then recurse on (rest', acc, body') after substitution
      else recurse on (rest, head :: acc, body, changed)

We generalize over the accumulator: for every `(binds, acc, body, changed, s)`,
`.Let (acc.reverse ++ binds) body ⊑ (inlineLetGo binds acc body changed s).1.1`.

The inline step is the semantically non-trivial one; it requires the shared
`subst_inline_mirCtxRefines` lemma. -/

/-- Inline-step helper: relate `.Let ((v, rhs, er) :: rest) body` to the
    post-substitution form that appears inside `inlineLetGo`. This is a
    direct use of `substInBindings_body_inline_mirCtxRefines`, which
    requires the `InlineGate` precondition witnessing that `shouldInline`
    returned `true` at this binding. -/
private theorem inline_step_mirCtxRefines
    (v : VarId) (rhs : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr)
    (s : Moist.MIR.FreshState)
    (hgate : InlineGate v rhs body rest = true)
    (hdist : Moist.MIR.distinctBinders ((v, rhs, er) :: rest) = true)
    (h_nc_body : Moist.Verified.InlineSoundness.SubstCommute.noCaptureFrom
                   (Moist.MIR.freeVars rhs) body = true)
    (h_nc_rest : rest.all (fun b => Moist.Verified.InlineSoundness.SubstCommute.noCaptureFrom
                                      (Moist.MIR.freeVars rhs) b.2.1) = true)
    (h_binders_fresh : rest.all
        (fun b => !(Moist.MIR.freeVars (Moist.MIR.expandFix rhs)).contains b.1) = true) :
    MIRCtxRefines (.Let ((v, rhs, er) :: rest) body)
      (.Let (Moist.MIR.substInBindings v rhs rest (Moist.MIR.subst v rhs body s).2).1.val
            (Moist.MIR.subst v rhs body s).1) :=
  substInBindings_body_inline_mirCtxRefines v rhs body er rest s hgate hdist
    h_nc_body h_nc_rest h_binders_fresh

private theorem distinctBinders_of_map_fst_eq
    {binds binds' : List (VarId × Expr × Bool)}
    (heq : binds'.map (·.1) = binds.map (·.1))
    (hd : Moist.MIR.distinctBinders binds = true) :
    Moist.MIR.distinctBinders binds' = true := by
  induction binds generalizing binds' with
  | nil =>
    match binds' with
    | [] => rfl
    | _ :: _ => simp [List.map] at heq
  | cons b rest ih =>
    obtain ⟨w, e, er⟩ := b
    match binds' with
    | [] => simp [List.map] at heq
    | (w', e', er') :: rest' =>
      simp only [List.map, List.cons.injEq] at heq
      simp only [Moist.MIR.distinctBinders, Bool.and_eq_true, List.all_eq_true] at hd ⊢
      refine ⟨fun b hmem => ?_, ih heq.2 hd.2⟩
      have hb_in : b.1 ∈ rest'.map (·.1) := List.mem_map.mpr ⟨b, hmem, rfl⟩
      rw [heq.2] at hb_in
      obtain ⟨b', hmem'', hb_eq⟩ := List.mem_map.mp hb_in
      have := hd.1 b' hmem''
      simp only [Bool.not_eq_true'] at this ⊢
      rw [show w' = w from heq.1, show b.1 = b'.1 from hb_eq.symm]; exact this

private theorem substInBindings_map_fst (v : VarId) (repl : Expr)
    (binds : List (VarId × Expr × Bool)) (s : Moist.MIR.FreshState) :
    (Moist.MIR.substInBindings v repl binds s).1.val.map (·.1) = binds.map (·.1) := by
  induction binds generalizing s with
  | nil => simp [Moist.MIR.substInBindings, pure, StateT.pure]
  | cons b rest ih =>
    obtain ⟨w, e, er⟩ := b
    simp only [Moist.MIR.substInBindings, bind, StateT.bind, List.map]
    exact congrArg (w :: ·) (ih (Moist.MIR.subst v repl e s).2)

theorem inlineBindings_map_fst
    (binds : List (VarId × Expr × Bool)) (s : Moist.MIR.FreshState) :
    (inlineBindings binds s).1.1.map (·.1) = binds.map (·.1) := by
  induction binds generalizing s with
  | nil => simp [inlineBindings, pure, StateT.pure]
  | cons b rest ih =>
    obtain ⟨w, e, er⟩ := b
    simp only [inlineBindings, bind, StateT.bind, List.map]
    exact congrArg (w :: ·) (ih (inlinePass e s).2)

theorem inlineBindings_preserves_distinctBinders
    (binds : List (VarId × Expr × Bool)) (s : Moist.MIR.FreshState)
    (hd : Moist.MIR.distinctBinders binds = true) :
    Moist.MIR.distinctBinders (inlineBindings binds s).1.1 = true :=
  distinctBinders_of_map_fst_eq (inlineBindings_map_fst binds s) hd

private def pc := @Moist.Verified.InlineSoundness.Preservation.PairwiseNC
private def pc_tail := @Moist.Verified.InlineSoundness.Preservation.pairwiseNC_tail
private def pc_ws := @Moist.Verified.InlineSoundness.Preservation.pairwiseNC_of_wellScoped
private def pc_subst := @Moist.Verified.InlineSoundness.Preservation.pairwiseNC_subst
private def sb_nc := @Moist.Verified.InlineSoundness.Preservation.substInBindings_nc_names
private def ib_names := @Moist.Verified.InlineSoundness.Preservation.inlineBindings_names
private def ip_nc := @Moist.Verified.InlineSoundness.Preservation.inlinePass_nc
private def ib_nc := @Moist.Verified.InlineSoundness.Preservation.inlineBindings_nc
private def ip_fvsub := @Moist.Verified.InlineSoundness.Preservation.inlinePass_fvsub
private def ncl_body := @Moist.Verified.InlineSoundness.Preservation.noCaptureFromLet_implies_body
private def ncl_rhss := @Moist.Verified.InlineSoundness.Preservation.noCaptureFromLet_implies_rhss
private def ncl_names := @Moist.Verified.InlineSoundness.Preservation.noCaptureFromLet_implies_names
private def nc_ws_app := @Moist.Verified.InlineSoundness.Preservation.nc_wellScoped_app
private def fvs_app_r := @Moist.Verified.InlineSoundness.Preservation.fvSub_app_right
private def sb_cross := @Moist.Verified.InlineSoundness.Preservation.substInBindings_cross_nc
private def ip_pc_cross := @Moist.Verified.InlineSoundness.Preservation.inlinePass_pairwiseNC_cross

private theorem inlineLetGo_soundness :
    ∀ (binds : List (VarId × Expr × Bool)) (acc : List (VarId × Expr × Bool))
      (body : Expr) (changed : Bool) (s : Moist.MIR.FreshState)
      (fv : VarSet)
      (_hdist : Moist.MIR.distinctBinders binds = true)
      (_hnc_body : noCaptureFrom fv body = true)
      (_hnc_binds : ∀ b ∈ binds, noCaptureFrom fv b.2.1 = true)
      (_hnc_acc : ∀ b ∈ acc, noCaptureFrom fv b.2.1 = true)
      (_hnames_binds : ∀ b ∈ binds, fv.contains b.1 = false)
      (_hnames_acc : ∀ b ∈ acc, fv.contains b.1 = false)
      (_hpc : pc binds body)
      (_h_nc_rhs_self : ∀ b ∈ binds, noCaptureFrom (freeVars b.2.1) b.2.1 = true)
      (_h_nc_rhs_rev : ∀ b₁ ∈ binds, ∀ b₂ ∈ binds,
        noCaptureFrom (freeVars b₁.2.1) b₂.2.1 = true),
      MIRCtxRefines (.Let (acc.reverse ++ binds) body)
                    (Moist.MIR.inlineLetGo binds acc body changed s).1.1
  | [], acc, body, changed, s, _, _, _, _, _, _, _, _, _, _ => by
    rw [Moist.MIR.inlineLetGo.eq_1]
    simp only [List.append_nil]
    cases hacc : acc.reverse with
    | nil =>
      simp only [pure, StateT.pure]
      exact mirCtxRefines_let_nil
    | cons s' rest' =>
      simp only [pure, StateT.pure]
      exact mirCtxRefines_refl _
  | (v, rhs, er) :: rest, acc, body, changed, s, fv, hdist,
    hnc_body, hnc_binds, hnc_acc, hnames_binds, hnames_acc,
    hpc, h_nc_rhs_self, h_nc_rhs_rev => by
    rw [Moist.MIR.inlineLetGo.eq_2]
    by_cases hinline :
        (Moist.MIR.shouldInline rhs
          (Moist.MIR.countOccurrences v body +
            rest.foldl (fun n (_, e, _) => n + Moist.MIR.countOccurrences v e) 0)
          (Moist.MIR.occursUnderFix v body ||
            rest.any (fun (_, e, _) => Moist.MIR.occursUnderFix v e))
          (Moist.MIR.occursInDeferred v body ||
            rest.any (fun (_, e, _) => Moist.MIR.occursInDeferred v e))) = true
    · simp only [hinline, ↓reduceIte]
      let p_body := Moist.MIR.subst v rhs body s
      let body' := p_body.1
      let s_body := p_body.2
      let p_rest := Moist.MIR.substInBindings v rhs rest s_body
      let rest' := p_rest.1.val
      let s_rest := p_rest.2
      have hlen : rest'.length = rest.length := p_rest.1.property
      have hdec : rest'.length < ((v, rhs, er) :: rest).length := by
        simp only [List.length_cons, hlen]; omega
      have hdist_rest : Moist.MIR.distinctBinders rest = true := by
        simp only [Moist.MIR.distinctBinders, Bool.and_eq_true] at hdist; exact hdist.2
      have hdist_rest' : Moist.MIR.distinctBinders rest' = true :=
        distinctBinders_of_map_fst_eq (substInBindings_map_fst v rhs rest s_body) hdist_rest
      have hnc_rhs := hnc_binds (v, rhs, er) (List.mem_cons_self ..)
      have hnc_rest : ∀ b ∈ rest, noCaptureFrom fv b.2.1 = true :=
        fun b hb => hnc_binds b (List.mem_cons_of_mem _ hb)
      have hnames_rest : ∀ b ∈ rest, fv.contains b.1 = false :=
        fun b hb => hnames_binds b (List.mem_cons_of_mem _ hb)
      have hnr_body := hpc.1
      have hnr_rest_all := hpc.2.1
      have h_binders_fresh := Moist.Verified.InlineSoundness.Preservation.pairwiseNC_expandFix hpc
      have hnr_rest : ∀ b ∈ rest, noCaptureFrom (freeVars rhs) b.2.1 = true := by
        rw [List.all_eq_true] at hnr_rest_all; exact fun b hb => hnr_rest_all b hb
      have hnc_body' :=
        noCaptureFrom_subst fv v rhs body s hnc_body hnc_rhs hnr_body
      have ⟨hnc_rest', hnames_rest'⟩ :=
        sb_nc fv v rhs rest s_body hnc_rhs hnc_rest hnames_rest hnr_rest
      have h_nc_self_rhs := h_nc_rhs_self (v, rhs, er) (List.mem_cons_self ..)
      have h_nc_rev_rest : ∀ b ∈ rest, noCaptureFrom (freeVars b.2.1) rhs = true :=
        fun b hb => h_nc_rhs_rev b (List.mem_cons_of_mem _ hb) (v, rhs, er) (List.mem_cons_self ..)
      have hpc_rest' := pc_subst v rhs er rest body s s_body hpc h_nc_self_rhs h_nc_rev_rest
      have h_cross_rest' := sb_cross v rhs rest s_body
        (fun b₁ hb₁ b₂ hb₂ => h_nc_rhs_rev b₁ (List.mem_cons_of_mem _ hb₁)
                                              b₂ (List.mem_cons_of_mem _ hb₂))
        h_nc_self_rhs hnr_rest h_nc_rev_rest
      have ih := inlineLetGo_soundness rest' acc body' true s_rest fv hdist_rest'
        hnc_body' hnc_rest' hnc_acc hnames_rest' hnames_acc hpc_rest'
        (fun b hb => h_cross_rest' b hb b hb)
        h_cross_rest'
      have h_split :
          MIRCtxRefines
            (.Let (acc.reverse ++ (v, rhs, er) :: rest) body)
            (.Let acc.reverse (.Let ((v, rhs, er) :: rest) body)) :=
        mirCtxRefines_of_lowerEq
          (lowerTotalExpr_let_split · acc.reverse ((v, rhs, er) :: rest) body)
      have hgate : InlineGate v rhs body rest = true := hinline
      have h_nc2 : rest.all (fun b => noCaptureFrom (freeVars rhs) b.2.1) = true := hnr_rest_all
      have h_step :
          MIRCtxRefines
            (.Let ((v, rhs, er) :: rest) body)
            (.Let rest' body') :=
        inline_step_mirCtxRefines v rhs er rest body s hgate hdist hnr_body h_nc2 h_binders_fresh
      have h_wrap := mirCtxRefines_let_body (binds := acc.reverse) h_step
      have h_unsplit :=
        mirCtxRefines_of_lowerEq
          (fun env => (lowerTotalExpr_let_split env acc.reverse rest' body').symm)
      exact mirCtxRefines_trans h_split
        (mirCtxRefines_trans h_wrap (mirCtxRefines_trans h_unsplit ih))
    · have hinline' :
          (Moist.MIR.shouldInline rhs
            (Moist.MIR.countOccurrences v body +
              rest.foldl (fun n (_, e, _) => n + Moist.MIR.countOccurrences v e) 0)
            (Moist.MIR.occursUnderFix v body ||
              rest.any (fun (_, e, _) => Moist.MIR.occursUnderFix v e))
            (Moist.MIR.occursInDeferred v body ||
              rest.any (fun (_, e, _) => Moist.MIR.occursInDeferred v e))) = false := by
        cases h : Moist.MIR.shouldInline rhs _ _ _ with
        | true => exact absurd h hinline
        | false => rfl
      simp only [hinline', Bool.false_eq_true, ↓reduceIte]
      have hdist_rest : Moist.MIR.distinctBinders rest = true := by
        simp only [Moist.MIR.distinctBinders, Bool.and_eq_true] at hdist; exact hdist.2
      have hnc_acc' : ∀ b ∈ (v, rhs, er) :: acc, noCaptureFrom fv b.2.1 = true := fun b hb => by
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact hnc_binds (v, rhs, er) (List.mem_cons_self ..)
        · exact hnc_acc b hb
      have hnames_acc' : ∀ b ∈ (v, rhs, er) :: acc, fv.contains b.1 = false := fun b hb => by
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact hnames_binds (v, rhs, er) (List.mem_cons_self ..)
        · exact hnames_acc b hb
      have ih := inlineLetGo_soundness rest ((v, rhs, er) :: acc) body changed s fv hdist_rest
        hnc_body
        (fun b hb => hnc_binds b (List.mem_cons_of_mem _ hb))
        hnc_acc'
        (fun b hb => hnames_binds b (List.mem_cons_of_mem _ hb))
        hnames_acc'
        (pc_tail hpc)
        (fun b hb => h_nc_rhs_self b (List.mem_cons_of_mem _ hb))
        (fun b1 hb1 b2 hb2 => h_nc_rhs_rev b1 (List.mem_cons_of_mem _ hb1)
          b2 (List.mem_cons_of_mem _ hb2))
      have hrev : ((v, rhs, er) :: acc).reverse = acc.reverse ++ [(v, rhs, er)] := by
        simp [List.reverse_cons]
      rw [hrev] at ih
      have hlist_eq : acc.reverse ++ [(v, rhs, er)] ++ rest =
                      acc.reverse ++ (v, rhs, er) :: rest := by
        simp [List.append_assoc]
      rw [hlist_eq] at ih
      exact ih
termination_by binds => binds.length

theorem inlineLetBindings_soundness (binds : List (VarId × Expr × Bool)) (body : Expr)
    (s : Moist.MIR.FreshState)
    (fv : VarSet)
    (hdist : Moist.MIR.distinctBinders binds = true)
    (hnc_body : noCaptureFrom fv body = true)
    (hnc_binds : ∀ b ∈ binds, noCaptureFrom fv b.2.1 = true)
    (hnames : ∀ b ∈ binds, fv.contains b.1 = false)
    (hpc : pc binds body)
    (h_nc_rhs_self : ∀ b ∈ binds, noCaptureFrom (freeVars b.2.1) b.2.1 = true)
    (h_nc_rhs_rev : ∀ b₁ ∈ binds, ∀ b₂ ∈ binds,
      noCaptureFrom (freeVars b₁.2.1) b₂.2.1 = true) :
    MIRCtxRefines (.Let binds body) (inlineLetBindings binds body s).1.1 := by
  unfold inlineLetBindings
  have h := inlineLetGo_soundness binds [] body false s fv hdist
    hnc_body hnc_binds (fun b hb => absurd hb (by simp))
    hnames (fun b hb => absurd hb (by simp)) hpc h_nc_rhs_self h_nc_rhs_rev
  simp only [List.reverse_nil, List.nil_append] at h
  exact h

--------------------------------------------------------------------------------
-- 4. Main theorem: `inline_soundness`
--------------------------------------------------------------------------------

mutual

theorem inline_soundness_aux : (e : Expr) → (s : Moist.MIR.FreshState) →
    (hws : wellScoped e = true) →
    MIRCtxRefines e (inlinePass e s).1.1
  | .Var v, s, _ => by
    rw [inlinePass_var]; exact mirCtxRefines_refl _
  | .Lit c, s, _ => by
    rw [inlinePass_lit]; exact mirCtxRefines_refl _
  | .Builtin b, s, _ => by
    rw [inlinePass_builtin]; exact mirCtxRefines_refl _
  | .Error, s, _ => by
    rw [inlinePass_error]; exact mirCtxRefines_refl _
  | .Lam x body, s, hws => by
    rw [inlinePass_lam]
    exact mirCtxRefines_lam (inline_soundness_aux body s (wellScoped_sub_lam hws))
  | .Fix f body, s, hws => by
    rw [inlinePass_fix]
    have hws_body := wellScoped_sub_fix hws
    cases body with
    | Lam x inner =>
      rw [inlinePass_lam]
      exact mirCtxRefines_fix_lam (inline_soundness_aux inner s (wellScoped_sub_lam hws_body))
    | Var v => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Lit c => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Builtin b => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Error => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Fix _ _ => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | App _ _ => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Force _ => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Delay _ => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Constr _ _ => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Case _ _ => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Let _ _ => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
  | .App f x, s, hws => by
    rw [inlinePass_app]
    have ⟨hws_f, hws_x⟩ := wellScoped_sub_app hws
    have h_f := inline_soundness_aux f s hws_f
    have h_x := inline_soundness_aux x (inlinePass f s).2 hws_x
    have h_app := mirCtxRefines_app h_f h_x
    have h_beta := betaReduce_soundness (inlinePass f s).1.1
      (inlinePass x (inlinePass f s).2).1.1 (inlinePass x (inlinePass f s).2).2
      (fun p b hfp => by
        have fv_eq := Moist.MIR.freeVars
        have ⟨hnc_f_fv, hnc_x_fv⟩ := nc_ws_app f x hws
        have hfv_x := fvs_app_r f x
        have h_nc_f' := ip_nc (freeVars (.App f x)) f s hnc_f_fv hws_f
        have h_fv_x' := ip_fvsub (freeVars (.App f x)) x (inlinePass f s).2 hfv_x
        have ⟨_, hnc_b⟩ := noCaptureFrom_lam (hfp ▸ h_nc_f')
        exact noCaptureFrom_mono (freeVars (.App f x)) _ b hnc_b h_fv_x')
    exact mirCtxRefines_trans h_app h_beta
  | .Force e, s, hws => by
    rw [inlinePass_force]
    exact mirCtxRefines_force (inline_soundness_aux e s (wellScoped_sub_force hws))
  | .Delay e, s, hws => by
    rw [inlinePass_delay]
    exact mirCtxRefines_delay (inline_soundness_aux e s (wellScoped_sub_delay hws))
  | .Constr tag args, s, hws => by
    rw [inlinePass_constr]
    have ⟨_, hws_args⟩ := wellScoped_sub_constr hws
    cases args with
    | nil =>
      rw [inlinePassList_nil]
      exact mirCtxRefines_refl _
    | cons e rest =>
      rw [inlinePassList_cons_eq]
      refine mirCtxRefines_constr ?_ ?_
      · exact inline_soundness_aux e s (hws_args e (List.mem_cons_self ..))
      · exact inlinePassList_listRel rest _
          (fun e' he' => hws_args e' (List.mem_cons_of_mem _ he'))
  | .Case scrut alts, s, hws => by
    rw [inlinePass_case]
    have ⟨hws_scrut, _, hws_alts⟩ := wellScoped_sub_case hws
    refine mirCtxRefines_case ?_ ?_
    · exact inline_soundness_aux scrut s hws_scrut
    · exact inlinePassList_listRel alts (inlinePass scrut s).2 hws_alts
  | .Let binds body, s, hws => by
    rw [inlinePass_let]
    have ⟨hws_body, _, hws_binds⟩ := wellScoped_sub_let hws
    have h_binds := inlineBindings_listRel binds s hws_binds
    have h_step1 := mirCtxRefines_let_binds_congr binds (inlineBindings binds s).1.1 body h_binds
    have h_body := inline_soundness_aux body (inlineBindings binds s).2 hws_body
    have h_step2 := mirCtxRefines_let_body (binds := (inlineBindings binds s).1.1) h_body
    let fv : VarSet := freeVarsLet binds body
    have hdist_ws := wellScoped_distinctBinders hws
    have hnc_ws := wellScoped_noCaptureFrom hws
    have hnc_let := noCaptureFrom_let hnc_ws
    simp only [Moist.MIR.freeVars] at hnc_let
    have hnc_body_ws :=
      ncl_body fv binds body hnc_let
    have hnc_binds_ws :=
      ncl_rhss fv binds body hnc_let
    have hnames_ws :=
      ncl_names fv binds body hnc_let
    have hnc_binds' := ib_nc fv binds s hnc_binds_ws hws_binds
    have hnames' := ib_names fv binds s hnames_ws
    have hnc_body' := ip_nc fv body (inlineBindings binds s).2 hnc_body_ws hws_body
    have hdist' := inlineBindings_preserves_distinctBinders binds s hdist_ws
    have ⟨hpc_pass, hcross_pass⟩ := ip_pc_cross binds body s hws
    have h_step3 := inlineLetBindings_soundness
      (inlineBindings binds s).1.1
      (inlinePass body (inlineBindings binds s).2).1.1
      (inlinePass body (inlineBindings binds s).2).2
      fv hdist' hnc_body' hnc_binds' hnames'
      hpc_pass
      (fun b hb => hcross_pass b hb b hb)
      hcross_pass
    exact mirCtxRefines_trans h_step1 (mirCtxRefines_trans h_step2 h_step3)

theorem inlinePassList_listRel : (es : List Expr) → (s : Moist.MIR.FreshState) →
    (hws : ∀ e ∈ es, wellScoped e = true) →
    ListRel MIRCtxRefines es (inlinePassList es s).1.1
  | [], s, _ => by
    rw [inlinePassList_nil]; exact True.intro
  | e :: rest, s, hws => by
    rw [inlinePassList_cons_eq]
    refine ⟨inline_soundness_aux e s (hws e (List.mem_cons_self ..)), ?_⟩
    exact inlinePassList_listRel rest _ (fun e' he' => hws e' (List.mem_cons_of_mem _ he'))

theorem inlineBindings_listRel : (binds : List (VarId × Expr × Bool)) →
    (s : Moist.MIR.FreshState) →
    (hws : ∀ b ∈ binds, wellScoped b.2.1 = true) →
    ListRel (fun b₁ b₂ => b₁.1 = b₂.1 ∧ b₁.2.2 = b₂.2.2 ∧
                          MIRCtxRefines b₁.2.1 b₂.2.1)
            binds (inlineBindings binds s).1.1
  | [], s, _ => by
    rw [inlineBindings_nil]; exact True.intro
  | (v, rhs, er) :: rest, s, hws => by
    rw [inlineBindings_cons_eq]
    refine ⟨⟨rfl, rfl, ?_⟩, ?_⟩
    · exact inline_soundness_aux rhs s (hws (v, rhs, er) (List.mem_cons_self ..))
    · exact inlineBindings_listRel rest _
        (fun b hb => hws b (List.mem_cons_of_mem _ hb))

end

theorem inline_soundness (e : Expr) (s : Moist.MIR.FreshState) :
    MIRCtxRefines e (Moist.MIR.inlinePassWithCanon e s).1.1 := by
  show MIRCtxRefines e (inlinePass (canonicalize e) s).1.1
  exact mirCtxRefines_trans
    (mirCtxRefines_of_lowerEq (fun env =>
      (Moist.MIR.lowerTotalExpr_canonicalize env e).symm))
    (inline_soundness_aux (canonicalize e) s (wellScoped_canonicalize e))

end Moist.Verified.MIR
