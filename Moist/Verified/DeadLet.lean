import Moist.Verified.Semantics
import Moist.Verified.StepLift
import Moist.MIR.LowerTotal
import Moist.Plutus.DecidableEq
import Moist.Verified.Bisim
import Moist.Verified.Rename

set_option linter.unusedSimpArgs false

namespace Moist.Verified.DeadLet

open Moist.CEK
open Moist.Plutus.Term
open Moist.MIR
open Moist.Verified.Semantics
open Moist.Verified
open Moist.Verified.StepLift (beta_reaches beta_reaches_error beta_apply_from_inner)
open Moist.Verified.Bisim (bisim_reaches_error bisim_halts bisim_halts_rev steps_preserves)
open Moist.Verified (renameTerm liftRename renameTerm_id)

/-! # Dead Let Elimination -- Semantic Correctness

This module proves that removing an unused `let` binding is semantics-preserving:

    `let x = e in body`  ≡  `body`    (when `x ∉ FV(body)` and `e` is pure)

The key insight is that after lowering to UPLC, the LHS becomes
`Apply (Lam 0 body') e'`, which beta-reduces into
`compute [] (cons ve nil) body'` — the body runs in an environment with one
extra (unused) binding. The RHS runs `body'` in the empty environment `nil`.
Since `body'` is `closedAt 0` (it uses no variables from the `let`), the
extra binding is unobservable: `EnvRelV 0 (cons ve nil) nil` holds vacuously
(there are no positions in the range `1..0` to check), so the bisimulation
gives `ValueRelV`-related results, which `closedAt_envRelV_valueEq` bridges
to `ValueEq` at every step index.

The purity side-condition (`isAtomicPure e`) is essential: a binding like
`let x = error in body` evaluates `error` before `body`, but dropping it
changes observable behavior. `isAtomicPure` restricts the RHS to literals,
builtins, lambdas, and delays — forms that always halt in exactly 2 CEK
steps and never error.
-/

/-! ## lowerTotal produces closed terms

`lowerTotal` translates MIR expressions to UPLC terms. This section proves
that the output term is always `closedAt env.length` — every variable in the
output has an index within the environment that produced it. This is the
bridge between the MIR world (named variables) and the UPLC world (de Bruijn
indices), and is needed to apply the bisimulation machinery. -/

mutual
  /-- If `lowerTotal env e = some t`, then `closedAt env.length t = true`.
      Structural induction on `e`, matching each MIR constructor to its
      UPLC lowering. -/
  theorem lowerTotal_closedAt (env : List VarId) (e : Expr) (t : Term)
      (h : lowerTotal env e = some t) : closedAt env.length t = true := by
    match e with
    | .Var x =>
      simp only [lowerTotal.eq_1] at h; split at h
      · rename_i idx hlook; injection h with h; subst h; simp only [closedAt]
        exact decide_eq_true (by have := envLookupT_bound env x idx hlook; omega)
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

  /-- List version: `lowerTotalList env es = some ts` implies
      `closedAtList env.length ts = true`. -/
  theorem lowerTotalList_closedAtList (env : List VarId) (es : List Expr) (ts : List Term)
      (h : lowerTotalList env es = some ts) : closedAtList env.length ts = true := by
    match es with
    | [] => simp only [lowerTotalList.eq_1] at h; injection h with h; subst h; simp [closedAtList]
    | e :: rest =>
      simp only [lowerTotalList.eq_2, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨t, ht, ts', hts, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAtList, Bool.and_eq_true]
      exact ⟨lowerTotal_closedAt env e t ht, lowerTotalList_closedAtList env rest ts' hts⟩
  termination_by sizeOf es

  /-- Let-binding version: `lowerTotalLet env binds body = some t` implies
      `closedAt env.length t = true`. Each binding extends the environment
      by one position. -/
  theorem lowerTotalLet_closedAt (env : List VarId) (binds : List (VarId × Expr × Bool))
      (body : Expr) (t : Term)
      (h : lowerTotalLet env binds body = some t) : closedAt env.length t = true := by
    match binds with
    | [] => simp only [lowerTotalLet.eq_1] at h; exact lowerTotal_closedAt env body t h
    | (x, rhs, _) :: rest =>
      simp only [lowerTotalLet.eq_2, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨rhs', hrhs, rest', hrest, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt, Bool.and_eq_true]
      have := lowerTotalLet_closedAt (x :: env) rest body rest' hrest
      simp at this; exact ⟨this, lowerTotal_closedAt env rhs rhs' hrhs⟩
  termination_by sizeOf binds + sizeOf body
end

/-! ## (step-counting replaced by StepLift.beta_reaches) -/

/-! ## MIRDeadLetCond -/

/-- An expression is "atomic pure" — a value form that the CEK machine can
    evaluate in exactly 2 steps (compute → ret → halt) without ever
    reaching `error`. Covers literals, builtins, lambdas, and delays.
    Application, force, variables, and error are excluded. -/
def isAtomicPure : Expr → Bool
  | .Lit _ | .Builtin _ | .Lam _ _ | .Delay _ => true
  | _ => false

/-- **Precondition for dead let elimination.**

    `MIRDeadLetCond x e body` asserts two things:
    1. `unused`: variable `x` does not appear free in `body`.
    2. `safe`: the RHS `e` is atomic-pure (cannot error or diverge).

    Both conditions are decidable and are discharged by `native_decide`
    in concrete applications (see `Example.lean`).

    The purity condition is essential: `let x = error in foo` errors
    before reaching `foo`, but dropping the binding makes `foo` succeed.
    Without `safe`, the optimization changes observable error behavior. -/
structure MIRDeadLetCond (x : VarId) (e body : Expr) : Prop where
  unused : (freeVars body).contains x = false
  safe : isAtomicPure e = true

/-! ## Core semantic lemma: closedAt + EnvRelV → ValueEq

This is the central bridge between the structural relation (`ValueRelV`,
from the bisimulation) and the observational relation (`ValueEq`, from
the behavioral equivalence definition).

For any `closedAt d t` term evaluated in two `EnvRelV d`-related
environments, if both computations halt, the results are `ValueEq k` for
every step index `k`.

The proof is a mutual induction on `k` with three components:
- **(A) `closed_eval_eq`**: closed term + related envs + both halt → `ValueEq k`.
  Simple terms (Var, Constant, Builtin, Error, Lam, Delay) are handled
  directly. Compound terms (Apply, Force, Constr, Case) delegate to
  `Bisim.bisim_reaches` to get `ValueRelV`, then use (B).
- **(B) `relV_to_eq`**: `ValueRelV v₁ v₂ → ValueEq k v₁ v₂`.
  Case-splits on the `ValueRelV` constructor; `vlam` and `vdelay` use
  (A) at the previous index.
- **(C) `listRelV_to_eq`**: list version of (B). -/

/-! ### ListValueRelV → ListValueEq bridge -/

private theorem listRelV_to_listEq_zero {vs₁ vs₂ : List CekValue}
    (h : ListValueRelV vs₁ vs₂) : ListValueEq 0 vs₁ vs₂ := by
  match h with
  | .nil => simp [ListValueEq]
  | .cons _ htl =>
    simp only [ListValueEq]; exact ⟨by simp [ValueEq], listRelV_to_listEq_zero htl⟩

private theorem listRelV_to_listEq_succ {k : Nat}
    (ih : ∀ v₁ v₂, ValueRelV v₁ v₂ → ValueEq (k + 1) v₁ v₂)
    {vs₁ vs₂ : List CekValue}
    (h : ListValueRelV vs₁ vs₂) : ListValueEq (k + 1) vs₁ vs₂ := by
  match h with
  | .nil => simp [ListValueEq]
  | .cons hd htl =>
    simp only [ListValueEq]; exact ⟨ih _ _ hd, listRelV_to_listEq_succ ih htl⟩

/-! ### Unreachable-halt helper

Several `Var`/`Error` cases need "this state can't halt" — factor it out. -/

private theorem compute_error_cant_halt {env : CekEnv} {t : Term} {v : CekValue}
    (h : Reaches (.compute [] env t) (.halt v))
    (herr : ∀ N, steps (N + 1) (.compute [] env t) = .error) : False := by
  obtain ⟨N, hN⟩ := h; cases N with
  | zero => simp [steps] at hN
  | succ N' => rw [herr N'] at hN; simp at hN

/-! ### Step 1: ValueRelV → ValueEq at successor index

Given that (A) and (C) hold at index `k`, derive (B) at index `k+1`.
Case-splits on the `ValueRelV` constructor:
- `vlam`/`vdelay`: apply (A @ k) to the closure body.
- `vconstr`/`vbuiltin`: apply (C @ k) to the fields/args.
- `vcon`/`refl`: direct. -/

private theorem relV_implies_valueEq_succ (k : Nat)
    (ihA : ∀ d t env₁ env₂ v₁ v₂,
      closedAt d t = true → ∀ σ, EnvRelV σ d env₁ env₂ →
      Reaches (.compute [] env₁ t) (.halt v₁) →
      Reaches (.compute [] env₂ (renameTerm σ t)) (.halt v₂) →
      ValueEq k v₁ v₂)
    (ihC : ∀ vs₁ vs₂, ListValueRelV vs₁ vs₂ → ListValueEq k vs₁ vs₂)
    (v₁ v₂ : CekValue) (hr : ValueRelV v₁ v₂) : ValueEq (k + 1) v₁ v₂ := by
  cases hr with
  | vcon => simp [ValueEq]
  | vlam σ d hcl henv =>
    unfold ValueEq; intro arg
    have hext := envRelV_extend σ d _ _ arg arg henv .refl
    have hsr := StateRel.compute .nil (liftRename σ) (d + 1) hext hcl
    exact ⟨⟨bisim_halts hsr, bisim_halts_rev hsr⟩,
           fun w₁ w₂ hw₁ hw₂ => ihA (d + 1) _ _ _ w₁ w₂ hcl (liftRename σ) hext hw₁ hw₂⟩
  | vdelay σ d hcl henv =>
    unfold ValueEq
    have hsr := StateRel.compute .nil σ d henv hcl
    exact ⟨⟨bisim_halts hsr, bisim_halts_rev hsr⟩,
           fun w₁ w₂ hw₁ hw₂ => ihA d _ _ _ w₁ w₂ hcl σ henv hw₁ hw₂⟩
  | vconstr htag hfs => subst htag; unfold ValueEq; exact ⟨rfl, ihC _ _ hfs⟩
  | vbuiltin hb hargs hea => subst hb; subst hea; unfold ValueEq; exact ⟨rfl, ihC _ _ hargs, rfl⟩
  | refl => exact valueEq_refl _ _

/-! ### Step 2: closedAt + EnvRelV + both halt → ValueEq at successor index

Given that (A) holds at index `k` and (B) holds at index `k+1`, derive
(A) at index `k+1`. Case-splits on the UPLC term:
- `Var 0` / `Error`: computation always errors, so halting is absurd.
- `Var (m+1)`: use `EnvRelV` to get matching lookups, then (B @ k+1).
- `Constant` / `Builtin`: both halt in 2 steps with identical values.
- `Lam` / `Delay`: both halt in 2 steps; use (A @ k) on the body.
- `Apply` / `Force` / `Constr` / `Case`: delegate to `bisim_reaches`
  for `ValueRelV`, then apply (B @ k+1). -/

private theorem closed_eval_valueEq_succ (k : Nat)
    (ihA : ∀ d t env₁ env₂ v₁ v₂,
      closedAt d t = true → ∀ σ, EnvRelV σ d env₁ env₂ →
      Reaches (.compute [] env₁ t) (.halt v₁) →
      Reaches (.compute [] env₂ (renameTerm σ t)) (.halt v₂) →
      ValueEq k v₁ v₂)
    (relV_to_eq : ∀ v₁ v₂, ValueRelV v₁ v₂ → ValueEq (k + 1) v₁ v₂)
    (σ : Nat → Nat) (d : Nat) (t : Term) (env₁ env₂ : CekEnv) (v₁ v₂ : CekValue)
    (hcl : closedAt d t = true) (hrel : EnvRelV σ d env₁ env₂)
    (h₁ : Reaches (.compute [] env₁ t) (.halt v₁))
    (h₂ : Reaches (.compute [] env₂ (renameTerm σ t)) (.halt v₂)) :
    ValueEq (k + 1) v₁ v₂ := by
  match t with
  | .Var 0 =>
    exact absurd h₁ fun ⟨N, hN⟩ => by
      cases N with | zero => simp [steps] at hN | succ => simp [steps, step, steps_error] at hN
  | .Var (.succ m) =>
    have hle := closedAt_var hcl
    have hlr := envRelV_elim hrel (by omega) hle
    cases hn₁ : env₁.lookup (m + 1) with
    | none =>
      exact absurd h₁ fun ⟨N, hN⟩ => by
        cases N with | zero => simp [steps] at hN | succ => simp [steps, step, hn₁, steps_error] at hN
    | some w₁ =>
      rw [hn₁] at hlr
      generalize hn₂ : env₂.lookup (σ (m + 1)) = r₂ at hlr
      cases hlr with
      | bothSome hv =>
        have hreach₁ : Reaches (.compute [] env₁ (.Var (m+1))) (.halt w₁) :=
          ⟨2, by simp [steps, step, hn₁]⟩
        rename_i w₂
        have hreach₂ : Reaches (.compute [] env₂ (.Var (σ (m+1)))) (.halt w₂) :=
          ⟨2, by simp [steps, step, hn₂]⟩
        have hv₁ := reaches_unique h₁ hreach₁
        -- h₂ is about renameTerm σ (.Var (m+1)) = .Var (σ (m+1))
        have hv₂ := reaches_unique h₂ (by show Reaches (.compute [] env₂ (renameTerm σ (.Var (m+1)))) (.halt w₂); simp [renameTerm]; exact hreach₂)
        subst hv₁; subst hv₂; exact relV_to_eq _ _ hv
  | .Constant (c, _) =>
    have := reaches_unique h₁ ⟨2, rfl⟩; subst this
    have := reaches_unique h₂ (by show Reaches (.compute [] env₂ (renameTerm σ (.Constant (c, _)))) (.halt _); simp [renameTerm]; exact ⟨2, rfl⟩); subst this
    simp [ValueEq]
  | .Builtin b =>
    have := reaches_unique h₁ (⟨2, rfl⟩ : Reaches _ (.halt _)); subst this
    have := reaches_unique h₂ (by show Reaches (.compute [] env₂ (renameTerm σ (.Builtin b))) (.halt _); simp [renameTerm]; exact ⟨2, rfl⟩); subst this
    simp [ValueEq, ListValueEq]
  | .Error =>
    simp only [renameTerm] at h₂
    exact absurd h₁ fun ⟨N, hN⟩ => by
      cases N with | zero => simp [steps] at hN | succ => simp [steps, step, steps_error] at hN
  | .Lam m body =>
    have := reaches_unique h₁ (⟨2, rfl⟩ : Reaches _ (.halt _)); subst this
    simp only [renameTerm] at h₂
    have := reaches_unique h₂ (⟨2, rfl⟩ : Reaches _ (.halt _)); subst this
    unfold ValueEq; intro arg
    have hext := envRelV_extend σ d env₁ env₂ arg arg hrel .refl
    have hsr := StateRel.compute .nil (liftRename σ) (d + 1) hext (closedAt_lam hcl)
    exact ⟨⟨bisim_halts hsr, bisim_halts_rev hsr⟩,
           fun w₁ w₂ hw₁ hw₂ => ihA (d + 1) body _ _ w₁ w₂
             (closedAt_lam hcl) (liftRename σ) hext hw₁ hw₂⟩
  | .Delay body =>
    have := reaches_unique h₁ (⟨2, rfl⟩ : Reaches _ (.halt _)); subst this
    simp only [renameTerm] at h₂
    have := reaches_unique h₂ (⟨2, rfl⟩ : Reaches _ (.halt _)); subst this
    unfold ValueEq
    have hsr := StateRel.compute .nil σ d hrel (closedAt_delay hcl)
    exact ⟨⟨bisim_halts hsr, bisim_halts_rev hsr⟩,
           fun w₁ w₂ hw₁ hw₂ => ihA d body env₁ env₂ w₁ w₂ (closedAt_delay hcl) σ hrel hw₁ hw₂⟩
  | .Apply _ _ | .Force _ | .Constr _ _ | .Case _ _ =>
    exact relV_to_eq v₁ v₂ (Bisim.bisim_reaches (.compute .nil σ d hrel hcl) h₁ h₂)

/-! ### Step 3: tie the knot by induction on k -/

private theorem env_rel_bundle_aux (k : Nat) :
    (∀ d t env₁ env₂ v₁ v₂,
      closedAt d t = true → ∀ σ, EnvRelV σ d env₁ env₂ →
      Reaches (.compute [] env₁ t) (.halt v₁) →
      Reaches (.compute [] env₂ (renameTerm σ t)) (.halt v₂) →
      ValueEq k v₁ v₂) ∧
    (∀ v₁ v₂, ValueRelV v₁ v₂ → ValueEq k v₁ v₂) ∧
    (∀ vs₁ vs₂, ListValueRelV vs₁ vs₂ → ListValueEq k vs₁ vs₂) := by
  induction k with
  | zero =>
    exact ⟨fun _ _ _ _ _ _ _ _ _ _ _ => by simp [ValueEq],
           fun _ _ _ => by simp [ValueEq],
           fun _ _ h => listRelV_to_listEq_zero h⟩
  | succ k ihk =>
    obtain ⟨ihA, _, ihC⟩ := ihk
    have relV_to_eq := relV_implies_valueEq_succ k ihA ihC
    exact ⟨fun d t e1 e2 v1 v2 hcl σ hrel h1 h2 => closed_eval_valueEq_succ k ihA relV_to_eq σ d t e1 e2 v1 v2 hcl hrel h1 h2,
           relV_to_eq,
           fun _ _ h => listRelV_to_listEq_succ relV_to_eq h⟩

/-! ### Public API -/

/-- **Main bridge theorem**: for a `closedAt d` term under `EnvRelV d`-related
    environments, if both computations halt, the results are `ValueEq k`
    for any `k`. This is the theorem that `dead_let_sound_closed` invokes
    to conclude value equivalence. -/
theorem closedAt_envRelV_valueEq (k d : Nat) (σ : Nat → Nat) (t : Term) (env₁ env₂ : CekEnv)
    (hclosed : closedAt d t = true) (hrel : EnvRelV σ d env₁ env₂)
    (v₁ v₂ : CekValue)
    (h₁ : Reaches (.compute [] env₁ t) (.halt v₁))
    (h₂ : Reaches (.compute [] env₂ (renameTerm σ t)) (.halt v₂)) :
    ValueEq k v₁ v₂ :=
  (env_rel_bundle_aux k).1 d t env₁ env₂ v₁ v₂ hclosed σ hrel h₁ h₂

/-- Corollary: `ValueRelV` (structural relation) implies `ValueEq`
    (observational relation) at every step index. -/
theorem ValueRelV.toValueEq (k : Nat) {v₁ v₂ : CekValue}
    (h : ValueRelV v₁ v₂) : ValueEq k v₁ v₂ :=
  (env_rel_bundle_aux k).2.1 v₁ v₂ h

/-- `ListValueRelV` implies `ListValueEq` at every step index. -/
theorem ListValueRelV.toListValueEq (k : Nat) {vs₁ vs₂ : List CekValue}
    (h : ListValueRelV vs₁ vs₂) : ListValueEq k vs₁ vs₂ :=
  (env_rel_bundle_aux k).2.2 vs₁ vs₂ h


/-! ## Atomic purity helpers

These lemmas establish that atomic-pure expressions (literals, builtins,
lambdas, delays) are harmless: they always halt in exactly 2 CEK steps
and never error, regardless of the environment. -/

/-- An atomic-pure expression halts in 2 steps in any environment.
    The proof case-splits on the four `isAtomicPure` forms and verifies
    `steps 2 (compute [] env t) = halt v` by `rfl`.
    The MIR-level environment `mir_env` is used only during lowering;
    the CEK-level environment `env` is the runtime environment. -/
private theorem atomicPure_halts (e : Expr) (t : Term) (env : CekEnv)
    (hpure : isAtomicPure e = true) (mir_env : List VarId)
    (hlower : lowerTotal mir_env e = some t) :
    ∃ ve, Reaches (.compute [] env t) (.halt ve) := by
  match e with
  | .Lit (c, ty) =>
    simp [lowerTotal] at hlower; subst hlower; exact ⟨.VCon c, 2, rfl⟩
  | .Builtin b =>
    simp [lowerTotal] at hlower; subst hlower
    exact ⟨.VBuiltin b [] (expectedArgs b), 2, rfl⟩
  | .Lam x body_e =>
    simp [lowerTotal, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlower
    obtain ⟨body', _, heq⟩ := hlower; subst heq
    exact ⟨.VLam body' env, 2, rfl⟩
  | .Delay inner =>
    simp [lowerTotal, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlower
    obtain ⟨inner', _, heq⟩ := hlower; subst heq
    exact ⟨.VDelay inner' env, 2, rfl⟩
  | .Var _ | .Error | .App _ _ | .Force _ | .Constr _ _ | .Case _ _ | .Let _ _ | .Fix _ _ =>
    simp [isAtomicPure] at hpure

/-- Contrapositive of `atomicPure_halts` + `reaches_halt_not_error`:
    an atomic-pure expression can never reach `error`. -/
private theorem atomicPure_never_error (e : Expr) (t : Term) (env : CekEnv)
    (hpure : isAtomicPure e = true) (mir_env : List VarId)
    (hlower : lowerTotal mir_env e = some t) :
    ¬ Reaches (.compute [] env t) .error := by
  intro herr
  have ⟨ve, hve⟩ := atomicPure_halts e t env hpure mir_env hlower
  exact reaches_halt_not_error hve herr

/-- For `closedAt 0` terms, error reachability is environment-independent.
    Since `EnvRelV 0` holds vacuously between any two environments (there are
    no positions to check), `bisim_reaches_error` transfers the error. -/
private theorem closedAt_zero_error_env_irrel (t : Term) (env₁ env₂ : CekEnv)
    (hclosed : closedAt 0 t = true) :
    Reaches (.compute [] env₁ t) .error → Reaches (.compute [] env₂ t) .error := by
  intro herr
  have hrel : EnvRelV id 0 env₁ env₂ :=
    .mk (fun n hn hle => absurd (Nat.lt_of_lt_of_le hn hle) (Nat.lt_irrefl 0))
        (fun n hn hle => absurd (Nat.lt_of_lt_of_le hn hle) (Nat.lt_irrefl 0))
        rfl
  have h := Bisim.bisim_reaches_error (.compute .nil id 0 hrel hclosed) herr
  simp [renameTerm_id] at h; exact h

/-- For `closedAt 0` terms, halting is environment-independent. -/
private theorem closedAt_zero_halts_env_irrel (t : Term) (env₁ env₂ : CekEnv)
    (hclosed : closedAt 0 t = true)
    (h : Halts (.compute [] env₁ t)) : Halts (.compute [] env₂ t) := by
  have hrel : EnvRelV id 0 env₁ env₂ :=
    .mk (fun n hn hle => absurd (Nat.lt_of_lt_of_le hn hle) (Nat.lt_irrefl 0))
        (fun n hn hle => absurd (Nat.lt_of_lt_of_le hn hle) (Nat.lt_irrefl 0))
        rfl
  have h' := bisim_halts (.compute .nil id 0 hrel hclosed) h
  simp [renameTerm_id] at h'; exact h'

/-- Reverse direction of `bisim_reaches_error`: if the *second* state
    reaches `error`, so does the *first*.

    The proof mirrors `bisim_reaches_error` — after `n` steps,
    `StateRel` is preserved, and the only `StateRel` constructor with
    `.error` on the right-hand side is `.error` itself, so the left-hand
    side must also be `.error`. -/
private theorem bisim_reaches_error_rev {s₁ s₂ : State}
    (hrel : StateRel s₁ s₂)
    (h₂ : Reaches s₂ .error) : Reaches s₁ .error := by
  obtain ⟨n, hn⟩ := h₂
  have hr := Bisim.steps_preserves n hrel
  rw [hn] at hr
  -- hr : StateRel (steps n s₁) .error — the only matching constructor is .error
  generalize h_eq : steps n s₁ = s1f at hr
  cases s1f with
  | error => exact ⟨n, h_eq⟩
  | halt _ => cases hr
  | compute _ _ _ => cases hr
  | ret _ _ => cases hr

/-! ## Main theorem -/

/-- **Dead let elimination is semantics-preserving.**

    Given `MIRDeadLetCond x e body` (i.e. `x ∉ FV(body)` and `e` is pure),
    we have `Let [(x, e, false)] body ≋ᶜ body`.

    **Proof outline:**
    1. Lower both sides. The LHS becomes `Apply (Lam 0 body') e'`;
       the RHS becomes `body'` directly.
    2. **Error ↔ error**:
       - LHS errors → `beta_reaches_error` splits into `e'` erroring
         (impossible by `atomicPure_never_error`) or `body'` erroring
         in extended env → `closedAt_zero_error_env_irrel` transfers to nil env.
       - RHS errors → `atomicPure_halts` gives `ve`, transfer error to
         extended env, compose via `beta_apply_from_inner`.
    3. **Value equivalence**: `beta_reaches` decomposes the LHS halt into
       `e'` halting and `body'` halting in extended env. Then
       `closedAt_envRelV_valueEq` with `EnvRelV 0 (cons ve nil) nil`
       (vacuously true) gives `ValueEq k` for all `k`. -/
theorem dead_let_sound_closed (x : VarId) (e body : Expr)
    (hsc : MIRDeadLetCond x e body) :
    .Let [(x, e, false)] body ≋ᶜ body := by
  unfold BehEqClosed
  have hlower_let : lowerTotal [] (.Let [(x, e, false)] body) =
      (do let e' ← lowerTotal [] e
          let b' ← lowerTotal [] body
          some (Term.Apply (Term.Lam 0 b') e')) := by
    rw [lowerTotal.eq_11, lowerTotalLet.eq_2, lowerTotalLet.eq_1,
        lowerTotal_closed_env_irrel x body hsc.unused]
  cases hb : lowerTotal [] body with
  | none =>
    -- body doesn't lower → second component is none → `| _, _ => True`
    split <;> trivial
  | some body' =>
    cases he : lowerTotal [] e with
    | none =>
      have hlhs : lowerTotal [] (.Let [(x, e, false)] body) = none := by
        rw [hlower_let]; simp [he]
      rw [hlhs]; split <;> trivial
    | some e' =>
      simp [hlower_let, he, hb]
      have hclosed : closedAt 0 body' = true := by
        have := lowerTotal_closedAt [] body body' hb; simp at this; exact this
      refine ⟨?_, ?_, ?_⟩
      -- Error equivalence: Apply (Lam 0 body') e' errors ↔ body' errors
      · constructor
        · intro herr
          rcases beta_reaches_error .nil body' e' 0 herr with he_err | ⟨ve, _, hbody_err⟩
          · exact absurd he_err (atomicPure_never_error e e' .nil hsc.safe (mir_env := []) he)
          · exact closedAt_zero_error_env_irrel body' (.cons ve .nil) .nil hclosed hbody_err
        · intro herr
          obtain ⟨ve, hve⟩ := atomicPure_halts e e' .nil hsc.safe (mir_env := []) he
          have hbody_err := closedAt_zero_error_env_irrel body' .nil (.cons ve .nil) hclosed herr
          exact beta_apply_from_inner .nil body' e' 0 ve .error hve hbody_err
      -- Halts equivalence
      · constructor
        · intro ⟨v, hv⟩
          obtain ⟨ve, _, hbody_reach⟩ := beta_reaches .nil body' e' 0 v hv
          exact closedAt_zero_halts_env_irrel body' (.cons ve .nil) .nil hclosed ⟨v, hbody_reach⟩
        · intro ⟨v, hv⟩
          obtain ⟨ve, hve⟩ := atomicPure_halts e e' .nil hsc.safe (mir_env := []) he
          obtain ⟨v', hv'⟩ := closedAt_zero_halts_env_irrel body' .nil (.cons ve .nil) hclosed ⟨v, hv⟩
          exact ⟨v', beta_apply_from_inner .nil body' e' 0 ve (.halt v') hve hv'⟩
      -- Value equivalence
      · intro k v₁ v₂ hv₁ hv₂
        obtain ⟨ve, _, hbody_reach⟩ := beta_reaches .nil body' e' 0 v₁ hv₁
        have hrel : EnvRelV id 0 (.cons ve .nil) .nil :=
          .mk (fun n hn hle => absurd (Nat.lt_of_lt_of_le hn hle) (Nat.lt_irrefl 0))
              (fun n hn hle => absurd (Nat.lt_of_lt_of_le hn hle) (Nat.lt_irrefl 0))
              rfl
        have hv₂' : Reaches (.compute [] .nil (renameTerm id body')) (.halt v₂) := by
          rw [renameTerm_id]; exact hv₂
        exact closedAt_envRelV_valueEq k 0 id body' (.cons ve .nil) .nil hclosed hrel v₁ v₂ hbody_reach hv₂'

/-! ## Generalized dead let elimination for open terms -/

open Moist.Verified (shiftRename closedAt_rename)
open Moist.MIR (lowerTotal_prepend_unused lowerTotal_prepend_unused_none)

/-- `EnvRelV (shiftRename 1) d ρ (ρ.extend ve)`:
    `ρ.lookup n` relates to `(ρ.extend ve).lookup (n+1) = ρ.lookup n`.
    This is the correct orientation for the dead-let proof:
    env1=ρ evaluates the original body, env2=ρ.extend ve evaluates the
    shifted body (renameTerm (shiftRename 1) body). -/
private theorem envRelV_shift_into_extend (d : Nat) (ρ : CekEnv) (ve : CekValue) :
    EnvRelV (shiftRename 1) d ρ (ρ.extend ve) := by
  constructor
  · intro n hn hle
    have hsr : shiftRename 1 n = n + 1 := by simp [shiftRename]; omega
    rw [hsr]
    -- (ρ.extend ve).lookup (n+1) = ρ.lookup n  (since n+1 ≥ 2, skips ve)
    show LookupRelV (ρ.lookup n) ((CekEnv.cons ve ρ).lookup (n + 1))
    -- .cons _ rest .lookup (n+1) = rest.lookup n when n ≥ 1
    cases n with
    | zero => omega
    | succ m =>
      show LookupRelV (ρ.lookup (m + 1)) (ρ.lookup (m + 1))
      match h : ρ.lookup (m + 1) with
      | none => exact h ▸ .bothNone
      | some v => exact h ▸ .bothSome .refl
  · intro n hn _; show 0 < shiftRename 1 n
    have : shiftRename 1 n = n + 1 := by simp [shiftRename]; omega
    omega
  · simp [shiftRename]

/-- **Dead let elimination for open terms.**

    Given `MIRDeadLetCond x e body`, `body` refines `Let [(x,e,false)] body`:
    it compiles wherever the let-expression does, and they are behaviorally
    equivalent. -/
theorem dead_let_sound (x : VarId) (e body : Expr)
    (hsc : MIRDeadLetCond x e body) :
    .Let [(x, e, false)] body ⊑ body := by
  constructor
  · -- Compilation: if the let lowers, body also lowers
    intro env h_let
    -- Case split on body lowering
    cases hb : lowerTotal env body with
    | some _ => simp [hb]
    | none =>
      -- body doesn't lower → lowerTotal (x :: env) body also doesn't lower
      -- (by lowerTotal_prepend_unused contrapositive) → the let doesn't lower
      exfalso
      have hlower_let : lowerTotal env (.Let [(x, e, false)] body) =
          (do let e' ← lowerTotal env e
              let b' ← lowerTotal (x :: env) body
              some (Term.Apply (Term.Lam 0 b') e')) := by
        rw [lowerTotal.eq_11, lowerTotalLet.eq_2, lowerTotalLet.eq_1]
      -- Since lowerTotal env body = none and x unused in body,
      -- lowerTotal (x :: env) body = none
      have hxb : lowerTotal (x :: env) body = none :=
        lowerTotal_prepend_unused_none env x body hsc.unused hb
      have : lowerTotal env (.Let [(x, e, false)] body) = none := by
        rw [hlower_let]; simp [hxb]
      rw [this] at h_let; simp at h_let
  · -- BehEq: behavioral equivalence
    unfold BehEq; intro env
    -- Lower the let: lowerTotal env (Let [(x,e,false)] body) = Apply (Lam 0 body_x) e'
    -- where body_x = lowerTotal (x :: env) body
    have hlower_let : lowerTotal env (.Let [(x, e, false)] body) =
        (do let e' ← lowerTotal env e
            let b' ← lowerTotal (x :: env) body
            some (Term.Apply (Term.Lam 0 b') e')) := by
      rw [lowerTotal.eq_11, lowerTotalLet.eq_2, lowerTotalLet.eq_1]
    cases hb : lowerTotal env body with
    | none =>
      -- body doesn't lower → second component is none → `| _, _ => True`
      split <;> trivial
    | some body' =>
      -- body_x = renameTerm (shiftRename 1) body'
      have hbx := lowerTotal_prepend_unused env x body hsc.unused body' hb
      cases he : lowerTotal env e with
      | none =>
        -- e doesn't lower → let doesn't lower → `| _, _ => True`
        have hlhs : lowerTotal env (.Let [(x, e, false)] body) = none := by
          rw [hlower_let]; simp [he]
        rw [hlhs]; split <;> trivial
      | some e' =>
        simp [hlower_let, he, hbx, hb]
        have hclosed : closedAt env.length body' = true := by
          have := lowerTotal_closedAt env body body' hb; simp at this; exact this
        refine ⟨?_, ?_, ?_⟩
        -- Error equivalence
        · intro ρ; constructor
          · intro herr
            rcases beta_reaches_error ρ (renameTerm (shiftRename 1) body') e' 0 herr with
              he_err | ⟨ve, _, hbody_err⟩
            · exact absurd he_err (atomicPure_never_error e e' ρ hsc.safe (mir_env := env) he)
            · have hrel := envRelV_shift_into_extend env.length ρ ve
              exact bisim_reaches_error_rev
                (.compute .nil (shiftRename 1) env.length hrel hclosed) hbody_err
          · intro herr
            obtain ⟨ve, hve⟩ := atomicPure_halts e e' ρ hsc.safe (mir_env := env) he
            have hrel := envRelV_shift_into_extend env.length ρ ve
            have hbody_err := Bisim.bisim_reaches_error
              (.compute .nil (shiftRename 1) env.length hrel hclosed) herr
            exact beta_apply_from_inner ρ (renameTerm (shiftRename 1) body') e' 0 ve .error hve hbody_err
        -- Halts equivalence
        · intro ρ; constructor
          · intro ⟨v, hv⟩
            obtain ⟨ve, _, hbody_reach⟩ := beta_reaches ρ (renameTerm (shiftRename 1) body') e' 0 v hv
            have hrel := envRelV_shift_into_extend env.length ρ ve
            exact bisim_halts_rev (.compute .nil (shiftRename 1) env.length hrel hclosed) ⟨v, hbody_reach⟩
          · intro ⟨v, hv⟩
            obtain ⟨ve, hve⟩ := atomicPure_halts e e' ρ hsc.safe (mir_env := env) he
            have hrel := envRelV_shift_into_extend env.length ρ ve
            obtain ⟨v', hv'⟩ := bisim_halts (.compute .nil (shiftRename 1) env.length hrel hclosed) ⟨v, hv⟩
            exact ⟨v', beta_apply_from_inner ρ (renameTerm (shiftRename 1) body') e' 0 ve (.halt v') hve hv'⟩
        -- Value equivalence
        · intro k ρ v₁ v₂ hv₁ hv₂
          obtain ⟨ve, _, hbody_reach⟩ := beta_reaches ρ (renameTerm (shiftRename 1) body') e' 0 v₁ hv₁
          have hrel := envRelV_shift_into_extend env.length ρ ve
          exact valueEq_symm k _ _ (closedAt_envRelV_valueEq k env.length (shiftRename 1) body'
            ρ (ρ.extend ve) hclosed hrel v₂ v₁ hv₂ hbody_reach)

end Moist.Verified.DeadLet
