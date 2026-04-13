import Moist.VerifiedNewNew.Rename
import Moist.MIR.Analysis
import Moist.MIR.LowerTotal
import Moist.MIR.Optimize.Purity

/-! # Dead Let Lowering Helpers

Supporting definitions and helpers for dead-let elimination, used by the
unidirectional refinement proof in `DeadLetRefines.lean`.

* `extend_lookup_shift` — basic CEK lookup identity used when the left
  environment has an extra leading entry.
* `lowerTotal_closedAt` — bridges `lowerTotal` success with
  `VerifiedNewNew.closedAt` on the resulting term, used to obtain the
  closedness hypothesis demanded by `uplc_dead_let_refines`.
-/

namespace Moist.VerifiedNewNew.DeadLet

open Moist.CEK
open Moist.MIR (Expr VarId lowerTotalExpr lowerTotal lowerTotalLet freeVars)
open Moist.Plutus.Term (Term)
open Moist.VerifiedNewNew (closedAt closedAtList)

--------------------------------------------------------------------------------
-- 1. Shift-extend lookup
--------------------------------------------------------------------------------

theorem extend_lookup_shift (ρ : CekEnv) (v : CekValue) (n : Nat) :
    (ρ.extend v).lookup (Moist.Verified.shiftRename 1 n) = ρ.lookup n := by
  cases n with
  | zero =>
    simp [Moist.Verified.shiftRename, CekEnv.extend, CekEnv.lookup]; cases ρ <;> rfl
  | succ m => simp [Moist.Verified.shiftRename, CekEnv.extend, CekEnv.lookup]

--------------------------------------------------------------------------------
-- 3. Bridge: `lowerTotal` success ⇒ `closedAt` on the lowered term
--------------------------------------------------------------------------------

open Moist.MIR (envLookupT_bound lowerTotalList) in
mutual
  theorem lowerTotal_closedAt (env : List VarId) (e : Expr) (t : Term)
      (h : lowerTotal env e = some t) : closedAt env.length t = true := by
    match e with
    | .Var x =>
      simp only [lowerTotal.eq_1] at h; split at h
      · rename_i idx hlook; injection h with h; subst h; simp [closedAt]
        have := envLookupT_bound env x idx hlook; omega
      · injection h
    | .Lit (c, ty) =>
      simp only [lowerTotal.eq_2] at h; injection h with h; subst h; simp [closedAt]
    | .Builtin b =>
      simp only [lowerTotal.eq_3] at h; injection h with h; subst h; simp [closedAt]
    | .Error =>
      simp only [lowerTotal.eq_4] at h; injection h with h; subst h; simp [closedAt]
    | .Lam x body =>
      simp only [lowerTotal.eq_5, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨body', hbody, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt]; have := lowerTotal_closedAt (x :: env) body body' hbody
      simp at this; exact this
    | .App f x =>
      simp only [lowerTotal.eq_6, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨f', hf, x', hx, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt, Bool.and_eq_true]
      exact ⟨lowerTotal_closedAt env f f' hf, lowerTotal_closedAt env x x' hx⟩
    | .Force inner =>
      simp only [lowerTotal.eq_7, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨inner', hinner, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt]; exact lowerTotal_closedAt env inner inner' hinner
    | .Delay inner =>
      simp only [lowerTotal.eq_8, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨inner', hinner, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt]; exact lowerTotal_closedAt env inner inner' hinner
    | .Constr tag args =>
      simp only [lowerTotal.eq_9, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨args', hargs, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt]; exact lowerTotalList_closedAtList env args args' hargs
    | .Case scrut alts =>
      simp only [lowerTotal.eq_10, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨scrut', hscrut, alts', halts, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt, Bool.and_eq_true]
      exact ⟨lowerTotal_closedAt env scrut scrut' hscrut,
             lowerTotalList_closedAtList env alts alts' halts⟩
    | .Let binds body =>
      simp only [lowerTotal.eq_11] at h; exact lowerTotalLet_closedAt env binds body t h
    | .Fix _ _ => simp only [lowerTotal.eq_12] at h; injection h
  termination_by sizeOf e

  theorem lowerTotalList_closedAtList (env : List VarId) (es : List Expr)
      (ts : List Term) (h : lowerTotalList env es = some ts) :
      closedAtList env.length ts = true := by
    match es with
    | [] => simp only [lowerTotalList.eq_1] at h; injection h with h; subst h; simp [closedAtList]
    | e :: rest =>
      simp only [lowerTotalList.eq_2, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨t, ht, ts', hts, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAtList, Bool.and_eq_true]
      exact ⟨lowerTotal_closedAt env e t ht, lowerTotalList_closedAtList env rest ts' hts⟩
  termination_by sizeOf es

  theorem lowerTotalLet_closedAt (env : List VarId)
      (binds : List (VarId × Expr × Bool)) (body : Expr) (t : Term)
      (h : Moist.MIR.lowerTotalLet env binds body = some t) :
      closedAt env.length t = true := by
    match binds with
    | [] => simp only [Moist.MIR.lowerTotalLet.eq_1] at h; exact lowerTotal_closedAt env body t h
    | (x, rhs, _) :: rest =>
      simp only [Moist.MIR.lowerTotalLet.eq_2, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨rhs', hrhs, rest', hrest, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt, Bool.and_eq_true]
      have := lowerTotalLet_closedAt (x :: env) rest body rest' hrest
      simp at this; exact ⟨this, lowerTotal_closedAt env rhs rhs' hrhs⟩
  termination_by sizeOf binds + sizeOf body
end

end Moist.VerifiedNewNew.DeadLet
