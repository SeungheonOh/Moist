import Moist.Verified.MIR
import Moist.Verified.MIR.Congruence
import Moist.Verified.DCESoundness
import Moist.Verified.DeadLet
import Moist.Verified.FundamentalRefines
import Moist.MIR.ANF

/-! # MIR rewrite primitives (general — reusable across compiler passes)

This module proves a library of `MIRCtxRefines` rewrites at the
expression level, generally useful for any optimisation pass that
needs to manipulate `.Let`, `.Apply`, `.Force`, `.Case`, or `.Constr`
nodes. Each primitive comes in `_fwd` / `_bwd` forms so it can be
applied in either direction.

## Reusable contents (alphabetical, by `mirCtxRefines_*` family)

* **`atomize`** — `e ≈ .Let [(x, e, false)] (.Var x)`. Lift any
  expression into a fresh let-binding then refer to it by name.
  Useful for any pass that wants to extract sub-expressions to
  named bindings (ANF, CSE, …).

* **`let_flatten_body`** — `.Let bs₁ (.Let bs₂ body) ≈ .Let (bs₁ ++ bs₂) body`.
  Concatenate two let-blocks. Useful for any pass that combines
  binding scopes.

* **`let_hoist_force`** — `.Force (.Let bs body) ≈ .Let bs (.Force body)`.
  Float a let outside a `.Force`. No freshness side condition.

* **`let_hoist_app_left`** — `(.Let bs body) x ≈ .Let bs (body x)`,
  when `x` is fresh w.r.t. each binding's name.

* **`let_hoist_app_right_atom`** — `g (.Let bs body) ≈ .Let bs (g body)`,
  when `g` is an atom and the binding names are fresh in `g`.

* **`let_hoist_case_scrut`** — Float a let out of the scrutinee of
  a `.Case` (alts must be fresh w.r.t. binding names).

* **`let_hoist_constr_arg`** — Float a let out of one argument
  position of a `.Constr` (the leftmost arguments must be atoms,
  and the binding names must be fresh in pre/post).

## Reusable infrastructure (lower-level)

* **CEK glue helpers** (`steps_trans`, `obsRefinesK_of_steps_*`,
  `stackRefK_funV_id_augment_*`, `envRefinesK_extend`,
  `stackRefK_force_augment`) — used by the primitive proofs but
  reusable by any pass proving `MIRRefines` via CEK admin-step
  counting.

* **`closedAt` under `shiftRename` lemmas** — needed by primitives
  that shift indices when crossing a binder.

## Proof structure

Each primitive is proved in three layers:

1. `lowerTotalExpr_*` shape lemmas pin down what the lowered UPLC
   term looks like.
2. `mirRefines_*_fwd` / `_bwd` does the CEK admin-step counting,
   closing via `ftlr`.
3. `mirCtxRefines_*_fwd` / `_bwd` bridges via
   `mirRefines_to_mirCtxRefines` with a `_close_pres_*` argument.

(Both `MIRRefines` and `_close_pres_*` are intermediate; clients
should use the top-level `mirCtxRefines_*_fwd` / `_bwd` API.)
-/

namespace Moist.Verified.MIR

open Moist.CEK
open Moist.Plutus.Term (Term)
open Moist.MIR
  (Expr VarId anfNormalizeCore anfNormalizeListCore anfNormalizeBindsCore anfAtom anfAtomList
   wrapLet flattenLetBody freeVars
   lowerTotalExpr lowerTotal lowerTotalLet)
open Moist.Verified (closedAt closedAtList renameTerm shiftRename)
open Moist.Verified.Contextual
  (Context fill ObsRefines CtxEq CtxRefines
   ctxEq_refl ctxRefines_refl ctxRefines_trans
   ctxEq_lam ctxEq_app
   ctxRefines_lam ctxRefines_app)
open Moist.Verified.Equivalence
  (ListRel ObsEq ObsRefinesK steps Reaches obsRefinesK_mono
   obsRefinesK_zero_ret listRel_mono)
open Moist.Verified.Contextual.SoundnessRefines
  (EnvRefinesK BehRefinesK ValueRefinesK StackRefK valueRefinesK_mono
   evalBuiltin_compat_refines obsRefinesK_error stackRefK_mono
   listRel_valueRefinesK_mono applyArgFrames_stackRefK
   listRel_refl_vcon_refines)
open Moist.Verified.FundamentalRefines (ftlr renameRefines renameRefinesR renameRefinesR_shift1
  is0preserving_id is0preserving_shiftRename
  RenameEnvRefR envRefinesK_to_renameEnvRefR_shift renameEnvRefR_mono)

/-! ## Freshness predicate for the main induction

`FreshGt s e` says: the next fresh uid `s.next` is strictly greater than
every uid appearing in `e`. This is the invariant needed to ensure
freshly-generated variables don't clash with existing variables in the
expression being normalized. -/

def FreshGt (s : Moist.MIR.FreshState) (e : Expr) : Prop :=
  Moist.MIR.maxUidExpr e < s.next

def FreshGtList (s : Moist.MIR.FreshState) (es : List Expr) : Prop :=
  Moist.MIR.maxUidExprList es < s.next

def FreshGtBinds (s : Moist.MIR.FreshState) (bs : List (VarId × Expr × Bool)) : Prop :=
  Moist.MIR.maxUidExprBinds bs < s.next

/-! ## Section 1. Generic ObsRefinesK / StackRefK helpers -/

/-- `steps_trans` reproven locally (the original is `private` in `DeadLet`). -/
private theorem steps_trans (m n : Nat) (s : State) :
    steps (m + n) s = steps n (steps m s) := by
  induction m generalizing s with
  | zero => simp [steps]
  | succ m ih => simp only [Nat.succ_add, steps]; exact ih (Moist.CEK.step s)

/-- Rightward step propagation: if the right state takes `n` deterministic
    steps to reach a `s₂'` that already Obs-refines from `s₁`, then the
    pre-step state `s₂` also Obs-refines from `s₁`. The intuition: any
    halt/error of `s₂'` is a halt/error of `s₂` `n` steps later. -/
theorem obsRefinesK_of_steps_right {k n : Nat} {s₁ s₂ s₂' : State}
    (h_steps : steps n s₂ = s₂')
    (h : ObsRefinesK k s₁ s₂') : ObsRefinesK k s₁ s₂ := by
  refine ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨v', m, hm⟩ := h.1 v hv
    refine ⟨v', n + m, ?_⟩
    rw [steps_trans n m, h_steps]; exact hm
  · intro n' hn' herr
    obtain ⟨m, hm⟩ := h.2 n' hn' herr
    refine ⟨n + m, ?_⟩
    rw [steps_trans n m, h_steps]; exact hm

/-- Leftward step propagation: if the left state takes `n` deterministic
    steps to reach `s₁'`, and `s₁'` Obs-refines `s₂`, then the pre-step
    `s₁` also Obs-refines `s₂`. The intuition: any halt/error of `s₁` is
    either before step `n` (in which case `steps n s₁ = halt/error`, i.e.
    `s₁' = halt/error`) or at step `m > n` (in which case `s₁'` halts/
    errors at step `m - n ≤ k`). -/
theorem obsRefinesK_of_steps_left {k n : Nat} {s₁ s₁' s₂ : State}
    (h_steps : steps n s₁ = s₁')
    (h : ObsRefinesK k s₁' s₂) : ObsRefinesK k s₁ s₂ := by
  refine ⟨?_, ?_⟩
  · intro v ⟨m, hmk, hsteps_v⟩
    by_cases hmn : m ≤ n
    · -- Case m ≤ n: s₁' = steps n s₁ = halt v
      have hs₁'_halt : s₁' = .halt v := by
        rw [← h_steps]
        have hsplit : n = m + (n - m) := by omega
        rw [hsplit, steps_trans, hsteps_v]
        exact Moist.Verified.Equivalence.steps_halt (n - m) v
      rw [hs₁'_halt] at h
      exact h.1 v ⟨0, Nat.zero_le _, rfl⟩
    · -- Case m > n: s₁' halts at step m - n
      have h_s₁'_halt : steps (m - n) s₁' = .halt v := by
        have hsplit : m = n + (m - n) := by omega
        rw [← h_steps, ← steps_trans, ← hsplit]
        exact hsteps_v
      have hmn_le : m - n ≤ k := by omega
      exact h.1 v ⟨m - n, hmn_le, h_s₁'_halt⟩
  · intro n' hn' herr
    by_cases hmn : n' ≤ n
    · have hs₁'_err : s₁' = .error := by
        rw [← h_steps]
        have hsplit : n = n' + (n - n') := by omega
        rw [hsplit, steps_trans, herr]
        exact Moist.Verified.Equivalence.steps_error _
      rw [hs₁'_err] at h
      exact h.2 0 (Nat.zero_le _) rfl
    · have h_s₁'_err : steps (n' - n) s₁' = .error := by
        have hsplit : n' = n + (n' - n) := by omega
        rw [← h_steps, ← steps_trans, ← hsplit]
        exact herr
      have hmn_le : n' - n ≤ k := by omega
      exact h.2 (n' - n) hmn_le h_s₁'_err

/-- A stack with an "identity-funV" frame on top is `StackRefK`-related to
    its underlying stack on the right. The frame `funV (VLam (Var 1) ρ)`
    is transparent: it consumes a returned value via two CEK steps
    (compute the `Var 1` lookup, ret the result), leaving the same
    value at the same depth. -/
theorem stackRefK_funV_id_augment_right {j : Nat} {π₁ π₂ : Stack} {ρ₂ : CekEnv}
    (hπ : StackRefK ValueRefinesK j π₁ π₂) :
    StackRefK ValueRefinesK j π₁ (.funV (.VLam (.Var 1) ρ₂) :: π₂) := by
  intro j' hj' v₁ v₂ hv
  -- Two right-side steps consume the funV frame and resolve the Var 1 lookup.
  have h_steps :
      steps 2 (State.ret (.funV (.VLam (.Var 1) ρ₂) :: π₂) v₂) = State.ret π₂ v₂ := by
    show Moist.CEK.step (Moist.CEK.step
      (State.ret (.funV (.VLam (.Var 1) ρ₂) :: π₂) v₂)) = State.ret π₂ v₂
    show Moist.CEK.step (State.compute π₂ (ρ₂.extend v₂) (.Var 1)) = State.ret π₂ v₂
    show (match (ρ₂.extend v₂).lookup 1 with
          | some v => State.ret π₂ v
          | none => State.error) = State.ret π₂ v₂
    have hl : (ρ₂.extend v₂).lookup 1 = some v₂ := by
      cases ρ₂ <;> rfl
    rw [hl]
  exact obsRefinesK_of_steps_right h_steps (hπ j' hj' v₁ v₂ hv)

/-- Symmetric augmentation: an identity-funV frame on the *left* stack
    is `StackRefK`-related to the underlying right stack. -/
theorem stackRefK_funV_id_augment_left {j : Nat} {π₁ π₂ : Stack} {ρ₁ : CekEnv}
    (hπ : StackRefK ValueRefinesK j π₁ π₂) :
    StackRefK ValueRefinesK j (.funV (.VLam (.Var 1) ρ₁) :: π₁) π₂ := by
  intro j' hj' v₁ v₂ hv
  have h_steps :
      steps 2 (State.ret (.funV (.VLam (.Var 1) ρ₁) :: π₁) v₁) = State.ret π₁ v₁ := by
    show Moist.CEK.step (Moist.CEK.step
      (State.ret (.funV (.VLam (.Var 1) ρ₁) :: π₁) v₁)) = State.ret π₁ v₁
    show Moist.CEK.step (State.compute π₁ (ρ₁.extend v₁) (.Var 1)) = State.ret π₁ v₁
    show (match (ρ₁.extend v₁).lookup 1 with
          | some v => State.ret π₁ v
          | none => State.error) = State.ret π₁ v₁
    have hl : (ρ₁.extend v₁).lookup 1 = some v₁ := by
      cases ρ₁ <;> rfl
    rw [hl]
  exact obsRefinesK_of_steps_left h_steps (hπ j' hj' v₁ v₂ hv)

/-- Extending both sides of an `EnvRefinesK`-related env-pair by related
    values produces an `EnvRefinesK`-related env-pair at the bumped depth. -/
theorem envRefinesK_extend {k d : Nat} {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue}
    (henv : EnvRefinesK k d ρ₁ ρ₂) (hv : ValueRefinesK k v₁ v₂) :
    EnvRefinesK k (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) := by
  intro n hn hnd
  match n, hn with
  | 1, _ =>
    refine ⟨v₁, v₂, ?_, ?_, hv⟩
    · show (CekEnv.cons v₁ ρ₁).lookup 1 = some v₁; rfl
    · show (CekEnv.cons v₂ ρ₂).lookup 1 = some v₂; rfl
  | m + 2, _ =>
    have hm1 : m + 1 ≥ 1 := by omega
    have hmd : m + 1 ≤ d := by omega
    obtain ⟨w₁, w₂, hl, hr, hw⟩ := henv (m + 1) hm1 hmd
    refine ⟨w₁, w₂, ?_, ?_, hw⟩
    · show (CekEnv.cons v₁ ρ₁).lookup (m + 2) = some w₁
      show ρ₁.lookup (m + 1) = some w₁
      exact hl
    · show (CekEnv.cons v₂ ρ₂).lookup (m + 2) = some w₂
      show ρ₂.lookup (m + 1) = some w₂
      exact hr

/-- A `.force` frame on top of related stacks gives a `StackRefK`-related
    pair. The .force frame fires based on the value's shape: VDelay
    continues with the delayed body, VBuiltin steps the builtin's force
    handling, and other shapes error on both sides. -/
theorem stackRefK_force_augment {i : Nat} {π₁ π₂ : Stack}
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i (.force :: π₁) (.force :: π₂) := by
  intro j hj v₁ v₂ hv
  match j with
  | 0 => exact obsRefinesK_zero_ret
  | n + 1 =>
    obsRefinesK_of_step_auto
    match v₁, v₂ with
    | .VDelay body₁ ρ₁', .VDelay body₂ ρ₂' =>
      simp only [Moist.CEK.step, ValueRefinesK] at hv ⊢
      exact hv n (by omega) n (Nat.le_refl _) π₁ π₂
        (Moist.Verified.Contextual.SoundnessRefines.stackRefK_mono (by omega) hπ)
    | .VBuiltin b₁ args₁ ea₁, .VBuiltin b₂ args₂ ea₂ =>
      simp only [ValueRefinesK] at hv
      obtain ⟨rfl, rfl, hargs⟩ := hv
      simp only [Moist.CEK.step]
      split
      · split
        · rename_i rest _
          have hval : ValueRefinesK (n + 1)
              (.VBuiltin b₁ args₁ rest) (.VBuiltin b₁ args₂ rest) := by
            simp only [ValueRefinesK]
            exact ⟨trivial, trivial, hargs⟩
          exact obsRefinesK_mono (by omega : n ≤ n + 1)
            (hπ (n + 1) (by omega) _ _ hval)
        · exact evalBuiltin_compat_refines hargs
            (Moist.Verified.Contextual.SoundnessRefines.stackRefK_mono (by omega) hπ)
      · exact obsRefinesK_error _
    | .VCon _, .VCon _ => simp only [Moist.CEK.step]; exact obsRefinesK_error _
    | .VLam _ _, .VLam _ _ => simp only [Moist.CEK.step]; exact obsRefinesK_error _
    | .VConstr _ _, .VConstr _ _ => simp only [Moist.CEK.step]; exact obsRefinesK_error _
    | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
    | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
    | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
    | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
    | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
    | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
    | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
    | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
    | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at hv

/-- Helper: `wrapLet bs body` is the same as `.Let bs body` when `bs` is
    nonempty. This avoids needing to pattern-match on `bs` explicitly. -/
theorem wrapLet_cons (b : VarId × Expr × Bool) (bs : List (VarId × Expr × Bool))
    (body : Expr) :
    Moist.MIR.wrapLet (b :: bs) body = .Let (b :: bs) body := rfl


/-! ## Section 2. Lowering shape lemmas

`lowerTotalExpr` decomposition for the shapes appearing in ANF primitives.
These pin down exactly what each `.Let`/`.Force`/`.App`/`.Case`/`.Constr`
node lowers to so that the MIRRefines proofs have concrete UPLC terms to
work with. -/

/-- Specialized form: when `e` lowers to `t` in `env`, then
    `let x = e in Var x` lowers to `Apply (Lam 0 (Var 1)) t`. -/
private theorem lowerTotalExpr_let_var_self_some
    {env : List VarId} (x : VarId) {e : Expr} {t : Term}
    (h : lowerTotalExpr env e = some t) :
    lowerTotalExpr env (.Let [(x, e, false)] (.Var x)) =
      some (.Apply (.Lam 0 (.Var 1)) t) := by
  have hexp : lowerTotal env (Moist.MIR.expandFix e) = some t := h
  show lowerTotal env (Moist.MIR.expandFix (.Let [(x, e, false)] (.Var x))) =
       some (.Apply (.Lam 0 (.Var 1)) t)
  simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds,
             Moist.MIR.lowerTotal, Moist.MIR.lowerTotalLet,
             Moist.MIR.envLookupT_cons_self, Option.bind_eq_bind,
             Option.bind_some, hexp]

/-- Specialized form: when `e` does *not* lower in `env`, neither does
    `let x = e in Var x`. -/
private theorem lowerTotalExpr_let_var_self_none
    {env : List VarId} (x : VarId) {e : Expr}
    (h : lowerTotalExpr env e = none) :
    lowerTotalExpr env (.Let [(x, e, false)] (.Var x)) = none := by
  have hexp : lowerTotal env (Moist.MIR.expandFix e) = none := h
  show lowerTotal env (Moist.MIR.expandFix (.Let [(x, e, false)] (.Var x))) = none
  simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds,
             Moist.MIR.lowerTotal, Moist.MIR.lowerTotalLet,
             Option.bind_eq_bind, hexp, Option.bind_none]

/-- Unified form: `lowerTotalExpr` of `.Let [(x, e, false)] (.Var x)` is
    the identity-application wrapper of `lowerTotalExpr` of `e`. -/
private theorem lowerTotalExpr_let_var_self
    (env : List VarId) (x : VarId) (e : Expr) :
    lowerTotalExpr env (.Let [(x, e, false)] (.Var x)) =
      (lowerTotalExpr env e).map (fun t => .Apply (.Lam 0 (.Var 1)) t) := by
  cases h : lowerTotalExpr env e with
  | none => rw [lowerTotalExpr_let_var_self_none x h]; rfl
  | some t => rw [lowerTotalExpr_let_var_self_some x h]; rfl

/-! ## Section 3. Atomize primitive (e ≈ let x = e in Var x) -/

/-- Closedness preservation for atomize: the wrapped form `Apply (Lam 0 (Var 1)) t`
    is closed at `k` iff `t` is. -/
private theorem closedAt_atomize_iff (k : Nat) (t : Term) :
    closedAt k (.Apply (.Lam 0 (.Var 1)) t) = closedAt k t := by
  simp only [closedAt]
  -- After simp: (decide (1 ≤ k + 1) && closedAt k t) = closedAt k t
  have h1 : decide ((1 : Nat) ≤ k + 1) = true := decide_eq_true (by omega)
  rw [h1, Bool.true_and]

/-- **MIRRefines for atomize (forward direction)**: `e ⊑ᴹ let x = e in Var x`.

    The let form lowers to `Apply (Lam 0 (Var 1)) t` where `t` is the
    lowering of `e`. After 3 admin steps, the right-hand side reaches
    `compute (funV (VLam (Var 1) ρ₂) :: π₂) ρ₂ t`, which differs from
    the left-hand state only in the funV frame on the stack. The funV
    frame is absorbed via `stackRefK_funV_id_augment`, then `ftlr`
    closes the goal: same `t` in related envs and stacks. -/
theorem mirRefines_atomize_fwd (e : Expr) (x : VarId) :
    MIRRefines e (.Let [(x, e, false)] (.Var x)) := by
  refine ⟨?_, ?_⟩
  · -- isSome direction: if e lowers, the let lowers
    intro env hsome
    rw [lowerTotalExpr_let_var_self env x e]
    simp only [Option.isSome_map]
    exact hsome
  · -- semantic part: ∀ d, MIROpenRef d
    intro d k env hlen
    show match lowerTotalExpr env e, lowerTotalExpr env (.Let [(x, e, false)] (.Var x)) with
         | some t₁, some t₂ =>
           ∀ j ≤ k, ∀ ρ₁ ρ₂, EnvRefinesK j d ρ₁ ρ₂ →
             BehRefinesK ValueRefinesK j ρ₁ ρ₂ t₁ t₂
         | _, _ => True
    cases ht : lowerTotalExpr env e with
    | none =>
      have hnone : lowerTotalExpr env (.Let [(x, e, false)] (.Var x)) = none :=
        lowerTotalExpr_let_var_self_none x ht
      rw [hnone]; trivial
    | some t₁ =>
      rw [lowerTotalExpr_let_var_self_some x ht]
      simp only
      intro j hj ρ₁ ρ₂ henv
      intro i hi π₁ π₂ hπ
      -- Goal: ObsRefinesK i (compute π₁ ρ₁ t₁) (compute π₂ ρ₂ (Apply (Lam 0 (Var 1)) t₁))
      -- Step the RHS forward 3 admin steps.
      have h_steps :
          steps 3 (State.compute π₂ ρ₂ (.Apply (.Lam 0 (.Var 1)) t₁)) =
            State.compute (.funV (.VLam (.Var 1) ρ₂) :: π₂) ρ₂ t₁ := by
        show Moist.CEK.step (Moist.CEK.step (Moist.CEK.step
          (State.compute π₂ ρ₂ (.Apply (.Lam 0 (.Var 1)) t₁)))) = _
        rfl
      apply obsRefinesK_of_steps_right h_steps
      -- Now apply FTLR with the augmented stack.
      have hclosed : closedAt env.length t₁ :=
        Moist.Verified.MIR.lowerTotal_closedAt env (Moist.MIR.expandFix e) t₁ ht
      have hπ_aug : StackRefK ValueRefinesK i π₁
          (.funV (.VLam (.Var 1) ρ₂) :: π₂) :=
        stackRefK_funV_id_augment_right hπ
      have hd_eq : d = env.length := hlen.symm
      subst hd_eq
      exact ftlr env.length t₁ hclosed j j (Nat.le_refl _) ρ₁ ρ₂ henv i hi
        π₁ (.funV (.VLam (.Var 1) ρ₂) :: π₂) hπ_aug

/-- **MIRRefines for atomize (backward direction)**: `let x = e in Var x ⊑ᴹ e`.

    Symmetric to the forward direction: the LHS takes 3 admin steps to
    reach `compute (funV ... :: π₁) ρ₁ t`, and we need this to refine
    `compute π₂ ρ₂ t`. We do this by showing the funV frame is also
    transparent on the *left* — so the goal reduces to `t in extended
    stack ⊑ t in plain stack`, again via FTLR with a stack relation. -/
theorem mirRefines_atomize_bwd (e : Expr) (x : VarId) :
    MIRRefines (.Let [(x, e, false)] (.Var x)) e := by
  refine ⟨?_, ?_⟩
  · intro env hsome
    rw [lowerTotalExpr_let_var_self env x e, Option.isSome_map] at hsome
    exact hsome
  · intro d k env hlen
    cases ht : lowerTotalExpr env e with
    | none =>
      have hnone : lowerTotalExpr env (.Let [(x, e, false)] (.Var x)) = none :=
        lowerTotalExpr_let_var_self_none x ht
      rw [hnone]; trivial
    | some t₁ =>
      rw [lowerTotalExpr_let_var_self_some x ht]
      simp only
      intro j hj ρ₁ ρ₂ henv
      intro i hi π₁ π₂ hπ
      -- Goal: ObsRefinesK i (compute π₁ ρ₁ (Apply (Lam 0 (Var 1)) t₁)) (compute π₂ ρ₂ t₁)
      -- Step LHS forward 3 admin steps to reach compute (funV :: π₁) ρ₁ t₁.
      have h_3steps :
          steps 3 (State.compute π₁ ρ₁ (.Apply (.Lam 0 (.Var 1)) t₁)) =
            State.compute (.funV (.VLam (.Var 1) ρ₁) :: π₁) ρ₁ t₁ := by
        show Moist.CEK.step (Moist.CEK.step (Moist.CEK.step
          (State.compute π₁ ρ₁ (.Apply (.Lam 0 (.Var 1)) t₁)))) = _
        rfl
      apply obsRefinesK_of_steps_left h_3steps
      -- Now need: ObsRefinesK i (compute (funV ... :: π₁) ρ₁ t₁) (compute π₂ ρ₂ t₁)
      -- Apply FTLR with the augmented LEFT stack.
      have hclosed : closedAt env.length t₁ :=
        Moist.Verified.MIR.lowerTotal_closedAt env (Moist.MIR.expandFix e) t₁ ht
      have hπ_aug : StackRefK ValueRefinesK i (.funV (.VLam (.Var 1) ρ₁) :: π₁) π₂ :=
        stackRefK_funV_id_augment_left hπ
      have hd_eq : d = env.length := hlen.symm
      subst hd_eq
      exact ftlr env.length t₁ hclosed j j (Nat.le_refl _) ρ₁ ρ₂ henv i hi
        (.funV (.VLam (.Var 1) ρ₁) :: π₁) π₂ hπ_aug

/-- Closedness preservation suffices for the atomize direction
    `e ↦ let x = e in Var x`: the wrapper is closed iff the body is. -/
private theorem atomize_close_pres_fwd (e : Expr) (x : VarId) :
    ∀ env k t₁ t₂,
      lowerTotalExpr env e = some t₁ →
      lowerTotalExpr env (.Let [(x, e, false)] (.Var x)) = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true := by
  intro env k t₁ t₂ h₁ h₂ hc
  rw [lowerTotalExpr_let_var_self env x e, h₁] at h₂
  injection h₂ with h₂
  subst h₂
  rw [closedAt_atomize_iff]
  exact hc

private theorem atomize_close_pres_bwd (e : Expr) (x : VarId) :
    ∀ env k t₁ t₂,
      lowerTotalExpr env (.Let [(x, e, false)] (.Var x)) = some t₁ →
      lowerTotalExpr env e = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true := by
  intro env k t₁ t₂ h₁ h₂ hc
  rw [lowerTotalExpr_let_var_self env x e, h₂] at h₁
  injection h₁ with h₁
  subst h₁
  rw [closedAt_atomize_iff] at hc
  exact hc

/-- **MIRCtxRefines for atomize**, both directions. -/
theorem mirCtxRefines_atomize_fwd (e : Expr) (x : VarId) :
    MIRCtxRefines e (.Let [(x, e, false)] (.Var x)) :=
  mirRefines_to_mirCtxRefines (mirRefines_atomize_fwd e x) (atomize_close_pres_fwd e x)

theorem mirCtxRefines_atomize_bwd (e : Expr) (x : VarId) :
    MIRCtxRefines (.Let [(x, e, false)] (.Var x)) e :=
  mirRefines_to_mirCtxRefines (mirRefines_atomize_bwd e x) (atomize_close_pres_bwd e x)

/-! ## Section 4. Let-flatten primitive (definitional) -/

/-- `expandFixBinds` distributes over list append. -/
private theorem expandFixBinds_append :
    ∀ (b₁ b₂ : List (VarId × Expr × Bool)),
      Moist.MIR.expandFixBinds (b₁ ++ b₂) =
        Moist.MIR.expandFixBinds b₁ ++ Moist.MIR.expandFixBinds b₂
  | [], _ => by simp [Moist.MIR.expandFixBinds]
  | (v, rhs, er) :: rest, b₂ => by
    simp only [List.cons_append, Moist.MIR.expandFixBinds, expandFixBinds_append rest b₂]

/-- `lowerTotalLet` of an appended bind list equals running the prefix
    against an inner `.Let`-wrapped body. -/
private theorem lowerTotalLet_append_eq :
    ∀ (b₁ b₂ : List (VarId × Expr × Bool)) (env : List VarId) (body : Expr),
      lowerTotalLet env (b₁ ++ b₂) body = lowerTotalLet env b₁ (.Let b₂ body)
  | [], b₂, env, body => by
    simp only [List.nil_append, lowerTotalLet, Moist.MIR.lowerTotal]
  | (x, rhs, er) :: rest, b₂, env, body => by
    simp only [List.cons_append, lowerTotalLet]
    rw [lowerTotalLet_append_eq rest b₂ (x :: env) body]

/-- **Let-flatten (body side)**: nested let in body equals appended bindings. -/
private theorem lowerTotalExpr_let_flatten_body
    (binds₁ binds₂ : List (VarId × Expr × Bool)) (body : Expr) (env : List VarId) :
    lowerTotalExpr env (.Let binds₁ (.Let binds₂ body)) =
      lowerTotalExpr env (.Let (binds₁ ++ binds₂) body) := by
  rw [lowerTotalExpr_let env binds₁ (.Let binds₂ body),
      lowerTotalExpr_let env (binds₁ ++ binds₂) body]
  have h1 : Moist.MIR.expandFix (.Let binds₂ body) =
            .Let (Moist.MIR.expandFixBinds binds₂) (Moist.MIR.expandFix body) := by
    simp only [Moist.MIR.expandFix]
  rw [h1, expandFixBinds_append binds₁ binds₂,
      lowerTotalLet_append_eq (Moist.MIR.expandFixBinds binds₁)
        (Moist.MIR.expandFixBinds binds₂) env (Moist.MIR.expandFix body)]

/-- **MIRRefines for let-flatten-body (forward)**: definitional via identical lowerings. -/
theorem mirRefines_let_flatten_body_fwd
    (binds₁ binds₂ : List (VarId × Expr × Bool)) (body : Expr) :
    MIRRefines (.Let binds₁ (.Let binds₂ body)) (.Let (binds₁ ++ binds₂) body) := by
  refine ⟨?_, ?_⟩
  · intro env hsome
    rw [lowerTotalExpr_let_flatten_body binds₁ binds₂ body env] at hsome
    exact hsome
  · intro d k env hlen
    rw [lowerTotalExpr_let_flatten_body binds₁ binds₂ body env]
    cases h : lowerTotalExpr env (.Let (binds₁ ++ binds₂) body) with
    | none => simp
    | some t =>
      simp only
      intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
      -- Apply FTLR (reflexivity case): same term in related envs/stacks
      have hclosed : closedAt env.length t :=
        Moist.Verified.MIR.lowerTotal_closedAt env _ t h
      have hd_eq : d = env.length := hlen.symm
      subst hd_eq
      exact ftlr env.length t hclosed j j (Nat.le_refl _) ρ₁ ρ₂ henv i hi π₁ π₂ hπ

/-- Symmetric (backward) direction. -/
theorem mirRefines_let_flatten_body_bwd
    (binds₁ binds₂ : List (VarId × Expr × Bool)) (body : Expr) :
    MIRRefines (.Let (binds₁ ++ binds₂) body) (.Let binds₁ (.Let binds₂ body)) := by
  refine ⟨?_, ?_⟩
  · intro env hsome
    rw [← lowerTotalExpr_let_flatten_body binds₁ binds₂ body env] at hsome
    exact hsome
  · intro d k env hlen
    rw [← lowerTotalExpr_let_flatten_body binds₁ binds₂ body env]
    cases h : lowerTotalExpr env (.Let binds₁ (.Let binds₂ body)) with
    | none => simp
    | some t =>
      simp only
      intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
      have hclosed : closedAt env.length t :=
        Moist.Verified.MIR.lowerTotal_closedAt env _ t h
      have hd_eq : d = env.length := hlen.symm
      subst hd_eq
      exact ftlr env.length t hclosed j j (Nat.le_refl _) ρ₁ ρ₂ henv i hi π₁ π₂ hπ

/-- Closedness preservation for let-flatten-body (both directions equivalent). -/
private theorem let_flatten_body_close_pres
    (binds₁ binds₂ : List (VarId × Expr × Bool)) (body : Expr) :
    ∀ env k t₁ t₂,
      lowerTotalExpr env (.Let binds₁ (.Let binds₂ body)) = some t₁ →
      lowerTotalExpr env (.Let (binds₁ ++ binds₂) body) = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true := by
  intro env k t₁ t₂ h₁ h₂ hc
  rw [lowerTotalExpr_let_flatten_body binds₁ binds₂ body env, h₂] at h₁
  injection h₁ with h₁
  subst h₁
  exact hc

private theorem let_flatten_body_close_pres_bwd
    (binds₁ binds₂ : List (VarId × Expr × Bool)) (body : Expr) :
    ∀ env k t₁ t₂,
      lowerTotalExpr env (.Let (binds₁ ++ binds₂) body) = some t₁ →
      lowerTotalExpr env (.Let binds₁ (.Let binds₂ body)) = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true := by
  intro env k t₁ t₂ h₁ h₂ hc
  rw [← lowerTotalExpr_let_flatten_body binds₁ binds₂ body env, h₂] at h₁
  injection h₁ with h₁
  subst h₁
  exact hc

theorem mirCtxRefines_let_flatten_body_fwd
    (binds₁ binds₂ : List (VarId × Expr × Bool)) (body : Expr) :
    MIRCtxRefines (.Let binds₁ (.Let binds₂ body)) (.Let (binds₁ ++ binds₂) body) :=
  mirRefines_to_mirCtxRefines
    (mirRefines_let_flatten_body_fwd binds₁ binds₂ body)
    (let_flatten_body_close_pres binds₁ binds₂ body)

theorem mirCtxRefines_let_flatten_body_bwd
    (binds₁ binds₂ : List (VarId × Expr × Bool)) (body : Expr) :
    MIRCtxRefines (.Let (binds₁ ++ binds₂) body) (.Let binds₁ (.Let binds₂ body)) :=
  mirRefines_to_mirCtxRefines
    (mirRefines_let_flatten_body_bwd binds₁ binds₂ body)
    (let_flatten_body_close_pres_bwd binds₁ binds₂ body)

/-! ## Section 4b. Closedness under `shiftRename`

The forward direction: `closedAt k t → closedAt (k+1) (renameTerm (shiftRename 1) t)`.
The inverse direction is `closedAt_shiftRename_unshift` in `DCESoundness.lean` (private). -/

mutual

private theorem closedAt_renameTerm_shiftRename :
    ∀ (t : Term) (k c : Nat), 1 ≤ c → c ≤ k + 1 →
      closedAt k t = true →
      closedAt (k + 1) (Moist.Verified.renameTerm (Moist.Verified.shiftRename c) t) = true
  | .Var n, k, c, hc1, hck, h => by
    simp only [Moist.Verified.renameTerm, closedAt, decide_eq_true_eq] at h ⊢
    by_cases hn : n ≥ c
    · rw [Moist.Verified.shiftRename_ge hn]; omega
    · have hn' : n < c := Nat.not_le.mp hn
      rw [Moist.Verified.shiftRename_lt hn']; omega
  | .Lam _ body, k, c, hc1, hck, h => by
    simp only [Moist.Verified.renameTerm, closedAt] at h ⊢
    have hlift : Moist.Verified.liftRename (Moist.Verified.shiftRename c) =
        Moist.Verified.shiftRename (c + 1) :=
      Moist.Verified.liftRename_shiftRename hc1
    rw [hlift]
    exact closedAt_renameTerm_shiftRename body (k + 1) (c + 1) (by omega) (by omega) h
  | .Apply f x, k, c, hc1, hck, h => by
    simp only [Moist.Verified.renameTerm, closedAt, Bool.and_eq_true] at h ⊢
    exact ⟨closedAt_renameTerm_shiftRename f k c hc1 hck h.1,
           closedAt_renameTerm_shiftRename x k c hc1 hck h.2⟩
  | .Force e, k, c, hc1, hck, h => by
    simp only [Moist.Verified.renameTerm, closedAt] at h ⊢
    exact closedAt_renameTerm_shiftRename e k c hc1 hck h
  | .Delay e, k, c, hc1, hck, h => by
    simp only [Moist.Verified.renameTerm, closedAt] at h ⊢
    exact closedAt_renameTerm_shiftRename e k c hc1 hck h
  | .Constr _ args, k, c, hc1, hck, h => by
    simp only [Moist.Verified.renameTerm, closedAt] at h ⊢
    exact closedAtList_renameTermList_shiftRename args k c hc1 hck h
  | .Case scrut alts, k, c, hc1, hck, h => by
    simp only [Moist.Verified.renameTerm, closedAt, Bool.and_eq_true] at h ⊢
    exact ⟨closedAt_renameTerm_shiftRename scrut k c hc1 hck h.1,
           closedAtList_renameTermList_shiftRename alts k c hc1 hck h.2⟩
  | .Constant _, _, _, _, _, _ => by simp [closedAt, Moist.Verified.renameTerm]
  | .Builtin _, _, _, _, _, _ => by simp [closedAt, Moist.Verified.renameTerm]
  | .Error, _, _, _, _, _ => by simp [closedAt, Moist.Verified.renameTerm]
termination_by t _ _ _ _ _ => sizeOf t

private theorem closedAtList_renameTermList_shiftRename :
    ∀ (ts : List Term) (k c : Nat), 1 ≤ c → c ≤ k + 1 →
      Moist.Verified.closedAtList k ts = true →
      Moist.Verified.closedAtList (k + 1)
        (Moist.Verified.renameTermList (Moist.Verified.shiftRename c) ts) = true
  | [], _, _, _, _, _ => by simp [Moist.Verified.closedAtList, Moist.Verified.renameTermList]
  | t :: rest, k, c, hc1, hck, h => by
    simp only [Moist.Verified.closedAtList, Moist.Verified.renameTermList,
               Bool.and_eq_true] at h ⊢
    exact ⟨closedAt_renameTerm_shiftRename t k c hc1 hck h.1,
           closedAtList_renameTermList_shiftRename rest k c hc1 hck h.2⟩
termination_by ts _ _ _ _ _ => sizeOf ts

end

mutual

/-- Inverse direction: `closedAt (k+1) (shiftRename c applied) → closedAt k t`. -/
private theorem closedAt_renameTerm_shiftRename_inv :
    ∀ (t : Term) (k c : Nat), 1 ≤ c → c ≤ k + 1 →
      closedAt (k + 1) (Moist.Verified.renameTerm (Moist.Verified.shiftRename c) t) = true →
      closedAt k t = true
  | .Var n, k, c, hc1, hck, h => by
    simp only [Moist.Verified.renameTerm, closedAt, decide_eq_true_eq] at h ⊢
    by_cases hn : n ≥ c
    · rw [Moist.Verified.shiftRename_ge hn] at h; omega
    · have hn' : n < c := Nat.not_le.mp hn
      rw [Moist.Verified.shiftRename_lt hn'] at h; omega
  | .Lam _ body, k, c, hc1, hck, h => by
    simp only [Moist.Verified.renameTerm, closedAt] at h ⊢
    have hlift : Moist.Verified.liftRename (Moist.Verified.shiftRename c) =
        Moist.Verified.shiftRename (c + 1) :=
      Moist.Verified.liftRename_shiftRename hc1
    rw [hlift] at h
    exact closedAt_renameTerm_shiftRename_inv body (k + 1) (c + 1) (by omega) (by omega) h
  | .Apply f x, k, c, hc1, hck, h => by
    simp only [Moist.Verified.renameTerm, closedAt, Bool.and_eq_true] at h ⊢
    exact ⟨closedAt_renameTerm_shiftRename_inv f k c hc1 hck h.1,
           closedAt_renameTerm_shiftRename_inv x k c hc1 hck h.2⟩
  | .Force e, k, c, hc1, hck, h => by
    simp only [Moist.Verified.renameTerm, closedAt] at h ⊢
    exact closedAt_renameTerm_shiftRename_inv e k c hc1 hck h
  | .Delay e, k, c, hc1, hck, h => by
    simp only [Moist.Verified.renameTerm, closedAt] at h ⊢
    exact closedAt_renameTerm_shiftRename_inv e k c hc1 hck h
  | .Constr _ args, k, c, hc1, hck, h => by
    simp only [Moist.Verified.renameTerm, closedAt] at h ⊢
    exact closedAtList_renameTermList_shiftRename_inv args k c hc1 hck h
  | .Case scrut alts, k, c, hc1, hck, h => by
    simp only [Moist.Verified.renameTerm, closedAt, Bool.and_eq_true] at h ⊢
    exact ⟨closedAt_renameTerm_shiftRename_inv scrut k c hc1 hck h.1,
           closedAtList_renameTermList_shiftRename_inv alts k c hc1 hck h.2⟩
  | .Constant _, _, _, _, _, _ => by simp [closedAt]
  | .Builtin _, _, _, _, _, _ => by simp [closedAt]
  | .Error, _, _, _, _, _ => by simp [closedAt]
termination_by t _ _ _ _ _ => sizeOf t

private theorem closedAtList_renameTermList_shiftRename_inv :
    ∀ (ts : List Term) (k c : Nat), 1 ≤ c → c ≤ k + 1 →
      Moist.Verified.closedAtList (k + 1)
        (Moist.Verified.renameTermList (Moist.Verified.shiftRename c) ts) = true →
      Moist.Verified.closedAtList k ts = true
  | [], _, _, _, _, _ => by simp [Moist.Verified.closedAtList]
  | t :: rest, k, c, hc1, hck, h => by
    simp only [Moist.Verified.closedAtList, Moist.Verified.renameTermList,
               Bool.and_eq_true] at h ⊢
    exact ⟨closedAt_renameTerm_shiftRename_inv t k c hc1 hck h.1,
           closedAtList_renameTermList_shiftRename_inv rest k c hc1 hck h.2⟩
termination_by ts _ _ _ _ _ => sizeOf ts

end

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
    simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.expandFixBinds,
      Moist.MIR.lowerTotal, Moist.MIR.lowerTotalLet]
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
    simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.expandFixBinds,
      Moist.MIR.lowerTotal, Moist.MIR.lowerTotalLet]
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
  show lowerTotal env (Moist.MIR.expandFix _) = lowerTotal env (Moist.MIR.expandFix _)
  simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
             Moist.MIR.lowerTotalLet]

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
        Moist.Verified.MIR.lowerTotal_closedAt env _ t h
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
        Moist.Verified.MIR.lowerTotal_closedAt env _ t h
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
  injection h₁ with h₁
  subst h₁
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
  injection h₁ with h₁
  subst h₁
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
    (hy_fresh_rest : ∀ r ∈ rest, (Moist.MIR.freeVars r.2.1).contains y = false)
    (hy_fresh_body : (Moist.MIR.freeVars body).contains y = false) :
    (Moist.MIR.freeVarsLet rest body).contains y = false := by
  induction rest with
  | nil =>
    rw [Moist.MIR.freeVarsLet]
    exact hy_fresh_body
  | cons r rest' ih =>
    obtain ⟨z, rhs_z, erz⟩ := r
    rw [Moist.MIR.freeVarsLet]
    apply Moist.MIR.VarSet.union_not_contains_fwd
    · exact hy_fresh_rest (z, rhs_z, erz) (List.Mem.head _)
    · apply Moist.MIR.VarSet.erase_not_contains_fwd
      exact ih (fun r hr => hy_fresh_rest r (List.Mem.tail _ hr))

/-- `expandFix` variant of the freshness propagation helper. -/
private theorem freeVarsLet_expandFix_not_contains_of_fresh
    (rest : List (VarId × Expr × Bool)) (body : Expr) (y : VarId)
    (hy_fresh_rest : ∀ r ∈ rest, (Moist.MIR.freeVars r.2.1).contains y = false)
    (hy_fresh_body : (Moist.MIR.freeVars body).contains y = false) :
    (Moist.MIR.freeVarsLet (Moist.MIR.expandFixBinds rest)
      (Moist.MIR.expandFix body)).contains y = false :=
  Moist.MIR.expandFixBinds_freeVars_not_contains rest body y
    (freeVarsLet_not_contains_of_fresh rest body y hy_fresh_rest hy_fresh_body)

/-- Shape lemma for the LHS of the single-binding flatten primitive. -/
private theorem lowerTotalExpr_let_flatten_rhs_head_single_lhs
    {env : List VarId} (x y : VarId) (e_y : Expr) (er_y : Bool)
    (innerBody : Expr) (er : Bool) (rest : List (VarId × Expr × Bool))
    (body : Expr) {t_ey t_iB t_rest : Term}
    (hey : lowerTotalExpr env e_y = some t_ey)
    (hiB : lowerTotalExpr (y :: env) innerBody = some t_iB)
    (hrest : Moist.MIR.lowerTotalLet (x :: env) (Moist.MIR.expandFixBinds rest)
              (Moist.MIR.expandFix body) = some t_rest) :
    lowerTotalExpr env (.Let ((x, .Let [(y, e_y, er_y)] innerBody, er) :: rest) body) =
      some (.Apply (.Lam 0 t_rest) (.Apply (.Lam 0 t_iB) t_ey)) := by
  have hey' : lowerTotal env (Moist.MIR.expandFix e_y) = some t_ey := hey
  have hiB' : lowerTotal (y :: env) (Moist.MIR.expandFix innerBody) = some t_iB := hiB
  show lowerTotal env (Moist.MIR.expandFix
      (.Let ((x, .Let [(y, e_y, er_y)] innerBody, er) :: rest) body)) =
    some (.Apply (.Lam 0 t_rest) (.Apply (.Lam 0 t_iB) t_ey))
  simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
             Moist.MIR.lowerTotalLet, Option.bind_eq_bind, Option.bind_some,
             hey', hiB', hrest]

/-- Shape lemma for the RHS of the single-binding flatten primitive.
    Uses `lowerTotalLet_prepend_unused_gen` to shift `t_rest` by `shiftRename 2`. -/
private theorem lowerTotalExpr_let_flatten_rhs_head_single_rhs
    {env : List VarId} (x y : VarId) (e_y : Expr) (er_y : Bool)
    (innerBody : Expr) (er : Bool) (rest : List (VarId × Expr × Bool))
    (body : Expr)
    (hy_fresh_rest : ∀ r ∈ rest, (Moist.MIR.freeVars r.2.1).contains y = false)
    (hy_fresh_body : (Moist.MIR.freeVars body).contains y = false)
    {t_ey t_iB t_rest : Term}
    (hey : lowerTotalExpr env e_y = some t_ey)
    (hiB : lowerTotalExpr (y :: env) innerBody = some t_iB)
    (hrest : Moist.MIR.lowerTotalLet (x :: env) (Moist.MIR.expandFixBinds rest)
              (Moist.MIR.expandFix body) = some t_rest) :
    lowerTotalExpr env (.Let ((y, e_y, er_y) :: (x, innerBody, er) :: rest) body) =
      some (.Apply (.Lam 0 (.Apply (.Lam 0
        (Moist.Verified.renameTerm (Moist.Verified.shiftRename 2) t_rest)) t_iB)) t_ey) := by
  have hey' : lowerTotal env (Moist.MIR.expandFix e_y) = some t_ey := hey
  have hiB' : lowerTotal (y :: env) (Moist.MIR.expandFix innerBody) = some t_iB := hiB
  have hfresh_exp : (Moist.MIR.freeVarsLet (Moist.MIR.expandFixBinds rest)
      (Moist.MIR.expandFix body)).contains y = false :=
    freeVarsLet_expandFix_not_contains_of_fresh rest body y hy_fresh_rest hy_fresh_body
  have hrest_shift : Moist.MIR.lowerTotalLet (x :: y :: env)
      (Moist.MIR.expandFixBinds rest) (Moist.MIR.expandFix body) =
        some (Moist.Verified.renameTerm
          (Moist.Verified.shiftRename 2) t_rest) := by
    have h := Moist.MIR.lowerTotalLet_prepend_unused_gen [x] env y
      (Moist.MIR.expandFixBinds rest) (Moist.MIR.expandFix body)
      (.inl hfresh_exp) t_rest hrest
    simpa using h
  show lowerTotal env (Moist.MIR.expandFix
      (.Let ((y, e_y, er_y) :: (x, innerBody, er) :: rest) body)) =
    some (.Apply (.Lam 0 (.Apply (.Lam 0
      (Moist.Verified.renameTerm (Moist.Verified.shiftRename 2) t_rest)) t_iB)) t_ey)
  simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
             Moist.MIR.lowerTotalLet, Option.bind_eq_bind, Option.bind_some,
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
      (Moist.MIR.lowerTotalLet (x :: env) (Moist.MIR.expandFixBinds rest)
        (Moist.MIR.expandFix body)).isSome := by
  constructor
  · intro hsome
    have h : (lowerTotal env (Moist.MIR.expandFix
        (.Let ((x, .Let [(y, e_y, er_y)] innerBody, er) :: rest) body))).isSome := hsome
    simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
               Moist.MIR.lowerTotalLet, Option.bind_eq_bind] at h
    cases hey : lowerTotal env (Moist.MIR.expandFix e_y) with
    | none => rw [hey] at h; simp at h
    | some t_ey =>
      rw [hey] at h
      simp only [Option.bind_some] at h
      cases hiB : lowerTotal (y :: env) (Moist.MIR.expandFix innerBody) with
      | none => rw [hiB] at h; simp at h
      | some t_iB =>
        rw [hiB] at h
        simp only [Option.bind_some] at h
        cases hrest : Moist.MIR.lowerTotalLet (x :: env)
            (Moist.MIR.expandFixBinds rest) (Moist.MIR.expandFix body) with
        | none => rw [hrest] at h; simp at h
        | some t_rest =>
          refine ⟨?_, ?_, ?_⟩
          · show (lowerTotal env (Moist.MIR.expandFix e_y)).isSome = true
            rw [hey]; rfl
          · show (lowerTotal (y :: env) (Moist.MIR.expandFix innerBody)).isSome = true
            rw [hiB]; rfl
          · rfl
  · rintro ⟨hey, hiB, hrest⟩
    cases hey' : lowerTotalExpr env e_y with
    | none => rw [hey'] at hey; exact absurd hey (by simp)
    | some t_ey =>
      cases hiB' : lowerTotalExpr (y :: env) innerBody with
      | none => rw [hiB'] at hiB; exact absurd hiB (by simp)
      | some t_iB =>
        cases hrest' : Moist.MIR.lowerTotalLet (x :: env)
            (Moist.MIR.expandFixBinds rest) (Moist.MIR.expandFix body) with
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
    (hy_fresh_rest : ∀ r ∈ rest, (Moist.MIR.freeVars r.2.1).contains y = false)
    (hy_fresh_body : (Moist.MIR.freeVars body).contains y = false) :
    (lowerTotalExpr env
      (.Let ((y, e_y, er_y) :: (x, innerBody, er) :: rest) body)).isSome ↔
      (lowerTotalExpr env e_y).isSome ∧
      (lowerTotalExpr (y :: env) innerBody).isSome ∧
      (Moist.MIR.lowerTotalLet (x :: env) (Moist.MIR.expandFixBinds rest)
        (Moist.MIR.expandFix body)).isSome := by
  have hfresh_exp : (Moist.MIR.freeVarsLet (Moist.MIR.expandFixBinds rest)
      (Moist.MIR.expandFix body)).contains y = false :=
    freeVarsLet_expandFix_not_contains_of_fresh rest body y hy_fresh_rest hy_fresh_body
  constructor
  · intro hsome
    have h : (lowerTotal env (Moist.MIR.expandFix
        (.Let ((y, e_y, er_y) :: (x, innerBody, er) :: rest) body))).isSome := hsome
    simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
               Moist.MIR.lowerTotalLet, Option.bind_eq_bind] at h
    cases hey : lowerTotal env (Moist.MIR.expandFix e_y) with
    | none => rw [hey] at h; simp at h
    | some t_ey =>
      rw [hey] at h
      simp only [Option.bind_some] at h
      cases hiB : lowerTotal (y :: env) (Moist.MIR.expandFix innerBody) with
      | none => rw [hiB] at h; simp at h
      | some t_iB =>
        rw [hiB] at h
        simp only [Option.bind_some] at h
        cases hrest_shift : Moist.MIR.lowerTotalLet (x :: y :: env)
            (Moist.MIR.expandFixBinds rest) (Moist.MIR.expandFix body) with
        | none => rw [hrest_shift] at h; simp at h
        | some t_rest_shift =>
          cases hrest : Moist.MIR.lowerTotalLet (x :: env)
              (Moist.MIR.expandFixBinds rest) (Moist.MIR.expandFix body) with
          | none =>
            have h_none := Moist.MIR.lowerTotalLet_prepend_unused_none_gen [x] env y
              (Moist.MIR.expandFixBinds rest) (Moist.MIR.expandFix body)
              (.inl hfresh_exp) hrest
            have h_none' : Moist.MIR.lowerTotalLet (x :: y :: env)
                (Moist.MIR.expandFixBinds rest) (Moist.MIR.expandFix body) = none := h_none
            rw [h_none'] at hrest_shift; exact absurd hrest_shift (by simp)
          | some t_rest =>
            refine ⟨?_, ?_, ?_⟩
            · show (lowerTotal env (Moist.MIR.expandFix e_y)).isSome = true
              rw [hey]; rfl
            · show (lowerTotal (y :: env) (Moist.MIR.expandFix innerBody)).isSome = true
              rw [hiB]; rfl
            · rfl
  · rintro ⟨hey, hiB, hrest⟩
    cases hey' : lowerTotalExpr env e_y with
    | none => rw [hey'] at hey; exact absurd hey (by simp)
    | some t_ey =>
      cases hiB' : lowerTotalExpr (y :: env) innerBody with
      | none => rw [hiB'] at hiB; exact absurd hiB (by simp)
      | some t_iB =>
        cases hrest' : Moist.MIR.lowerTotalLet (x :: env)
            (Moist.MIR.expandFixBinds rest) (Moist.MIR.expandFix body) with
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
      (Moist.Verified.shiftRename 2) k (d + 1)
      (ρ₁.extend u₁) ((ρ₂.extend v₂).extend u₂) := by
  intro n hn hnd
  show match (ρ₁.extend u₁).lookup n,
             ((ρ₂.extend v₂).extend u₂).lookup (Moist.Verified.shiftRename 2 n) with
       | some v₁', some v₂' => ValueRefinesK k v₁' v₂'
       | none, none => True
       | _, _ => False
  by_cases hn1 : n = 1
  · subst hn1
    have hsr : Moist.Verified.shiftRename 2 1 = 1 := by
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
    have hsr : Moist.Verified.shiftRename 2 n = n + 1 := by
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
    Moist.Verified.FundamentalRefines.Is0Preserving (Moist.Verified.shiftRename 2) :=
  is0preserving_shiftRename (by omega)

theorem mirRefines_let_flatten_rhs_head_single_fwd
    (x : VarId) (y : VarId) (e_y : Expr) (er_y : Bool) (innerBody : Expr)
    (er : Bool) (rest : List (VarId × Expr × Bool)) (body : Expr)
    (hy_fresh_rest : ∀ r ∈ rest, (Moist.MIR.freeVars r.2.1).contains y = false)
    (hy_fresh_body : (Moist.MIR.freeVars body).contains y = false) :
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
        cases hrest : Moist.MIR.lowerTotalLet (x :: env) (Moist.MIR.expandFixBinds rest)
            (Moist.MIR.expandFix body) with
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
                  (.funV (.VLam t_iB ρ₁) :: .funV (.VLam t_rest ρ₁) :: π₁) ρ₁ t_ey := by rfl
          have h_steps_rhs :
              steps 3 (State.compute π₂ ρ₂
                  (.Apply (.Lam 0 (.Apply (.Lam 0
                    (Moist.Verified.renameTerm
                      (Moist.Verified.shiftRename 2) t_rest)) t_iB)) t_ey)) =
                State.compute
                  (.funV (.VLam (.Apply (.Lam 0
                    (Moist.Verified.renameTerm
                      (Moist.Verified.shiftRename 2) t_rest)) t_iB) ρ₂) :: π₂) ρ₂ t_ey := by rfl
          apply obsRefinesK_of_steps_left h_steps_lhs
          apply obsRefinesK_of_steps_right h_steps_rhs
          have hclosed_ey : closedAt env.length t_ey :=
            Moist.Verified.MIR.lowerTotal_closedAt env _ t_ey hey
          have hclosed_iB : closedAt (env.length + 1) t_iB := by
            have := Moist.Verified.MIR.lowerTotal_closedAt (y :: env) _ t_iB hiB
            simpa [List.length_cons] using this
          have hclosed_rest : closedAt (env.length + 1) t_rest := by
            have := Moist.Verified.MIR.lowerTotalLet_closedAt (x :: env) _ _ t_rest hrest
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
                (Moist.Verified.renameTerm
                  (Moist.Verified.shiftRename 2) t_rest)) t_iB) ρ₂) :: π₂) := by
            intro j' hj' v₁ v₂ hv
            have h_lhs_v : steps 1 (State.ret
                (.funV (.VLam t_iB ρ₁) :: .funV (.VLam t_rest ρ₁) :: π₁) v₁) =
                  State.compute (.funV (.VLam t_rest ρ₁) :: π₁) (ρ₁.extend v₁) t_iB := by rfl
            have h_rhs_v : steps 4 (State.ret
                (.funV (.VLam (.Apply (.Lam 0
                  (Moist.Verified.renameTerm
                    (Moist.Verified.shiftRename 2) t_rest)) t_iB) ρ₂) :: π₂) v₂) =
                  State.compute (.funV (.VLam
                    (Moist.Verified.renameTerm
                      (Moist.Verified.shiftRename 2) t_rest) (ρ₂.extend v₂)) :: π₂)
                    (ρ₂.extend v₂) t_iB := by rfl
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
                (.funV (.VLam (Moist.Verified.renameTerm
                  (Moist.Verified.shiftRename 2) t_rest) (ρ₂.extend v₂)) :: π₂) := by
              intro j'' hj'' u₁ u₂ hu
              have h_lhs_u : steps 1 (State.ret
                  (.funV (.VLam t_rest ρ₁) :: π₁) u₁) =
                    State.compute π₁ (ρ₁.extend u₁) t_rest := by rfl
              have h_rhs_u : steps 1 (State.ret
                  (.funV (.VLam (Moist.Verified.renameTerm
                    (Moist.Verified.shiftRename 2) t_rest) (ρ₂.extend v₂)) :: π₂) u₂) =
                    State.compute π₂ ((ρ₂.extend v₂).extend u₂)
                      (Moist.Verified.renameTerm
                        (Moist.Verified.shiftRename 2) t_rest) := by rfl
              apply obsRefinesK_of_steps_left h_lhs_u
              apply obsRefinesK_of_steps_right h_rhs_u
              have henv_j'' : EnvRefinesK j'' env.length ρ₁ ρ₂ := by
                intro n hn hnd
                obtain ⟨w₁, w₂, hl, hrg, hw⟩ := henv_j' n hn hnd
                exact ⟨w₁, w₂, hl, hrg, valueRefinesK_mono (by omega) _ _ hw⟩
              have henv_shift2 : Moist.Verified.FundamentalRefines.RenameEnvRefR
                  (Moist.Verified.shiftRename 2) j'' (env.length + 1)
                  (ρ₁.extend u₁) ((ρ₂.extend v₂).extend u₂) :=
                renameEnvRefR_shift2_extend henv_j'' hu
              exact Moist.Verified.FundamentalRefines.renameRefinesR
                (Moist.Verified.shiftRename 2) is0preserving_shiftRename2
                (env.length + 1) t_rest hclosed_rest j''
                j'' (Nat.le_refl _) (ρ₁.extend u₁) ((ρ₂.extend v₂).extend u₂)
                henv_shift2 j'' (Nat.le_refl _) π₁ π₂
                (Moist.Verified.Contextual.SoundnessRefines.stackRefK_mono
                  (by omega : j'' ≤ i) hπ)
            exact ftlr (env.length + 1) t_iB hclosed_iB j' j' (Nat.le_refl _)
              (ρ₁.extend v₁) (ρ₂.extend v₂) henv_ext j' (Nat.le_refl _) _ _ hπ_inner
          exact ftlr env.length t_ey hclosed_ey j j (Nat.le_refl _) ρ₁ ρ₂ henv_j i hi
            _ _ hπ_aug

theorem mirRefines_let_flatten_rhs_head_single_bwd
    (x : VarId) (y : VarId) (e_y : Expr) (er_y : Bool) (innerBody : Expr)
    (er : Bool) (rest : List (VarId × Expr × Bool)) (body : Expr)
    (hy_fresh_rest : ∀ r ∈ rest, (Moist.MIR.freeVars r.2.1).contains y = false)
    (hy_fresh_body : (Moist.MIR.freeVars body).contains y = false) :
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
        cases hrest : Moist.MIR.lowerTotalLet (x :: env) (Moist.MIR.expandFixBinds rest)
            (Moist.MIR.expandFix body) with
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
                    (Moist.Verified.renameTerm
                      (Moist.Verified.shiftRename 2) t_rest)) t_iB)) t_ey)) =
                State.compute
                  (.funV (.VLam (.Apply (.Lam 0
                    (Moist.Verified.renameTerm
                      (Moist.Verified.shiftRename 2) t_rest)) t_iB) ρ₁) :: π₁) ρ₁ t_ey := by rfl
          have h_steps_rhs :
              steps 6 (State.compute π₂ ρ₂
                  (.Apply (.Lam 0 t_rest) (.Apply (.Lam 0 t_iB) t_ey))) =
                State.compute
                  (.funV (.VLam t_iB ρ₂) :: .funV (.VLam t_rest ρ₂) :: π₂) ρ₂ t_ey := by rfl
          apply obsRefinesK_of_steps_left h_steps_lhs
          apply obsRefinesK_of_steps_right h_steps_rhs
          have hclosed_ey : closedAt env.length t_ey :=
            Moist.Verified.MIR.lowerTotal_closedAt env _ t_ey hey
          have hclosed_iB : closedAt (env.length + 1) t_iB := by
            have := Moist.Verified.MIR.lowerTotal_closedAt (y :: env) _ t_iB hiB
            simpa [List.length_cons] using this
          have hclosed_rest : closedAt (env.length + 1) t_rest := by
            have := Moist.Verified.MIR.lowerTotalLet_closedAt (x :: env) _ _ t_rest hrest
            simpa [List.length_cons] using this
          have hd_eq : d = env.length := hlen.symm
          subst hd_eq
          have henv_j : EnvRefinesK j env.length ρ₁ ρ₂ := by
            intro n hn hnd
            obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv n hn hnd
            exact ⟨w₁, w₂, hl, hr', hw⟩
          have hπ_aug : StackRefK ValueRefinesK i
              (.funV (.VLam (.Apply (.Lam 0
                (Moist.Verified.renameTerm
                  (Moist.Verified.shiftRename 2) t_rest)) t_iB) ρ₁) :: π₁)
              (.funV (.VLam t_iB ρ₂) :: .funV (.VLam t_rest ρ₂) :: π₂) := by
            intro j' hj' v₁ v₂ hv
            have h_lhs_v : steps 4 (State.ret
                (.funV (.VLam (.Apply (.Lam 0
                  (Moist.Verified.renameTerm
                    (Moist.Verified.shiftRename 2) t_rest)) t_iB) ρ₁) :: π₁) v₁) =
                  State.compute (.funV (.VLam
                    (Moist.Verified.renameTerm
                      (Moist.Verified.shiftRename 2) t_rest) (ρ₁.extend v₁)) :: π₁)
                    (ρ₁.extend v₁) t_iB := by rfl
            have h_rhs_v : steps 1 (State.ret
                (.funV (.VLam t_iB ρ₂) :: .funV (.VLam t_rest ρ₂) :: π₂) v₂) =
                  State.compute (.funV (.VLam t_rest ρ₂) :: π₂) (ρ₂.extend v₂) t_iB := by rfl
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
                (.funV (.VLam (Moist.Verified.renameTerm
                  (Moist.Verified.shiftRename 2) t_rest) (ρ₁.extend v₁)) :: π₁)
                (.funV (.VLam t_rest ρ₂) :: π₂) := by
              intro j'' hj'' u₁ u₂ hu
              have h_lhs_u : steps 1 (State.ret
                  (.funV (.VLam (Moist.Verified.renameTerm
                    (Moist.Verified.shiftRename 2) t_rest) (ρ₁.extend v₁)) :: π₁) u₁) =
                    State.compute π₁ ((ρ₁.extend v₁).extend u₁)
                      (Moist.Verified.renameTerm
                        (Moist.Verified.shiftRename 2) t_rest) := by rfl
              have h_rhs_u : steps 1 (State.ret
                  (.funV (.VLam t_rest ρ₂) :: π₂) u₂) =
                    State.compute π₂ (ρ₂.extend u₂) t_rest := by rfl
              apply obsRefinesK_of_steps_left h_lhs_u
              apply obsRefinesK_of_steps_right h_rhs_u
              have henv_j'' : EnvRefinesK j'' env.length ρ₁ ρ₂ := by
                intro n hn hnd
                obtain ⟨w₁, w₂, hl, hrg, hw⟩ := henv_j' n hn hnd
                exact ⟨w₁, w₂, hl, hrg, valueRefinesK_mono (by omega) _ _ hw⟩
              have henv_shift2_L : Moist.Verified.FundamentalRefines.RenameEnvRef
                  (Moist.Verified.shiftRename 2) j'' (env.length + 1)
                  ((ρ₁.extend v₁).extend u₁) (ρ₂.extend u₂) := by
                intro n hn hnd
                show match ((ρ₁.extend v₁).extend u₁).lookup
                             (Moist.Verified.shiftRename 2 n),
                           (ρ₂.extend u₂).lookup n with
                     | some v₁', some v₂' => ValueRefinesK j'' v₁' v₂'
                     | none, none => True
                     | _, _ => False
                by_cases hn1 : n = 1
                · subst hn1
                  have hsr : Moist.Verified.shiftRename 2 1 = 1 := by
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
                  have hsr : Moist.Verified.shiftRename 2 n = n + 1 := by
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
                (Moist.Verified.shiftRename 2) is0preserving_shiftRename2
                (env.length + 1) t_rest hclosed_rest j''
                j'' (Nat.le_refl _) ((ρ₁.extend v₁).extend u₁) (ρ₂.extend u₂)
                henv_shift2_L j'' (Nat.le_refl _) π₁ π₂
                (Moist.Verified.Contextual.SoundnessRefines.stackRefK_mono
                  (by omega : j'' ≤ i) hπ)
            exact ftlr (env.length + 1) t_iB hclosed_iB j' j' (Nat.le_refl _)
              (ρ₁.extend v₁) (ρ₂.extend v₂) henv_ext j' (Nat.le_refl _) _ _ hπ_inner
          exact ftlr env.length t_ey hclosed_ey j j (Nat.le_refl _) ρ₁ ρ₂ henv_j i hi
            _ _ hπ_aug

private theorem let_flatten_rhs_head_single_close_pres_fwd
    (x y : VarId) (e_y : Expr) (er_y : Bool) (innerBody : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr)
    (hy_fresh_rest : ∀ r ∈ rest, (Moist.MIR.freeVars r.2.1).contains y = false)
    (hy_fresh_body : (Moist.MIR.freeVars body).contains y = false) :
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
      cases hrest : Moist.MIR.lowerTotalLet (x :: env) (Moist.MIR.expandFixBinds rest)
          (Moist.MIR.expandFix body) with
      | none => rw [hrest] at hrest_some; exact absurd hrest_some (by simp)
      | some t_rest =>
        rw [lowerTotalExpr_let_flatten_rhs_head_single_lhs x y e_y er_y innerBody er
          rest body hey hiB hrest] at h₁
        rw [lowerTotalExpr_let_flatten_rhs_head_single_rhs x y e_y er_y innerBody er
          rest body hy_fresh_rest hy_fresh_body hey hiB hrest] at h₂
        injection h₁ with h₁; subst h₁
        injection h₂ with h₂; subst h₂
        simp only [closedAt, Bool.and_eq_true] at hc ⊢
        obtain ⟨hrest_c, hiB_c, hey_c⟩ := hc
        refine ⟨⟨?_, hiB_c⟩, hey_c⟩
        by_cases hk : k = 0
        · subst hk
          exact closedAt_renameTerm_shiftRename t_rest 1 2 (by omega) (by omega) hrest_c
        · have hkp : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk
          exact closedAt_renameTerm_shiftRename t_rest (k + 1) 2 (by omega) (by omega) hrest_c

private theorem let_flatten_rhs_head_single_close_pres_bwd
    (x y : VarId) (e_y : Expr) (er_y : Bool) (innerBody : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr)
    (hy_fresh_rest : ∀ r ∈ rest, (Moist.MIR.freeVars r.2.1).contains y = false)
    (hy_fresh_body : (Moist.MIR.freeVars body).contains y = false) :
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
      cases hrest : Moist.MIR.lowerTotalLet (x :: env) (Moist.MIR.expandFixBinds rest)
          (Moist.MIR.expandFix body) with
      | none => rw [hrest] at hrest_some; exact absurd hrest_some (by simp)
      | some t_rest =>
        rw [lowerTotalExpr_let_flatten_rhs_head_single_rhs x y e_y er_y innerBody er
          rest body hy_fresh_rest hy_fresh_body hey hiB hrest] at h₁
        rw [lowerTotalExpr_let_flatten_rhs_head_single_lhs x y e_y er_y innerBody er
          rest body hey hiB hrest] at h₂
        injection h₁ with h₁; subst h₁
        injection h₂ with h₂; subst h₂
        simp only [closedAt, Bool.and_eq_true] at hc ⊢
        obtain ⟨⟨hrest_sh_c, hiB_c⟩, hey_c⟩ := hc
        refine ⟨?_, hiB_c, hey_c⟩
        by_cases hk : k = 0
        · subst hk
          exact closedAt_renameTerm_shiftRename_inv t_rest 1 2 (by omega) (by omega) hrest_sh_c
        · have hkp : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk
          exact closedAt_renameTerm_shiftRename_inv t_rest (k + 1) 2 (by omega) (by omega) hrest_sh_c

theorem mirCtxRefines_let_flatten_rhs_head_single_fwd
    (x : VarId) (y : VarId) (e_y : Expr) (er_y : Bool) (innerBody : Expr)
    (er : Bool) (rest : List (VarId × Expr × Bool)) (body : Expr)
    (hy_fresh_rest : ∀ r ∈ rest, (Moist.MIR.freeVars r.2.1).contains y = false)
    (hy_fresh_body : (Moist.MIR.freeVars body).contains y = false) :
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
    (hy_fresh_rest : ∀ r ∈ rest, (Moist.MIR.freeVars r.2.1).contains y = false)
    (hy_fresh_body : (Moist.MIR.freeVars body).contains y = false) :
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
      (∀ b ∈ innerBinds, (Moist.MIR.freeVars body).contains b.1 = false) →
      (∀ b ∈ innerBinds, ∀ r ∈ rest, (Moist.MIR.freeVars r.2.1).contains b.1 = false) →
      MIRCtxRefines (.Let ((x, .Let innerBinds innerBody, er) :: rest) body)
                    (.Let (innerBinds ++ [(x, innerBody, er)] ++ rest) body)
  | x, [], innerBody, er, rest, body, _, _ => by
    have heq : ([] : List (VarId × Expr × Bool)) ++ [(x, innerBody, er)] ++ rest =
               (x, innerBody, er) :: rest := by simp
    rw [heq]
    exact mirCtxRefines_let_flatten_rhs_head_nil_fwd x innerBody er rest body
  | x, (y, e_y, er_y) :: iB_rest, innerBody, er, rest, body, hfresh_body, hfresh_rest => by
    have hy_fresh_body : (Moist.MIR.freeVars body).contains y = false :=
      hfresh_body (y, e_y, er_y) (List.Mem.head _)
    have hy_fresh_rest : ∀ r ∈ rest, (Moist.MIR.freeVars r.2.1).contains y = false :=
      fun r hr => hfresh_rest (y, e_y, er_y) (List.Mem.head _) r hr
    have hiBrest_fresh_body : ∀ b ∈ iB_rest, (Moist.MIR.freeVars body).contains b.1 = false :=
      fun b hb => hfresh_body b (List.Mem.tail _ hb)
    have hiBrest_fresh_rest : ∀ b ∈ iB_rest, ∀ r ∈ rest,
        (Moist.MIR.freeVars r.2.1).contains b.1 = false :=
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
      (∀ b ∈ innerBinds, (Moist.MIR.freeVars body).contains b.1 = false) →
      (∀ b ∈ innerBinds, ∀ r ∈ rest, (Moist.MIR.freeVars r.2.1).contains b.1 = false) →
      MIRCtxRefines (.Let (innerBinds ++ [(x, innerBody, er)] ++ rest) body)
                    (.Let ((x, .Let innerBinds innerBody, er) :: rest) body)
  | x, [], innerBody, er, rest, body, _, _ => by
    have heq : ([] : List (VarId × Expr × Bool)) ++ [(x, innerBody, er)] ++ rest =
               (x, innerBody, er) :: rest := by simp
    rw [heq]
    exact mirCtxRefines_let_flatten_rhs_head_nil_bwd x innerBody er rest body
  | x, (y, e_y, er_y) :: iB_rest, innerBody, er, rest, body, hfresh_body, hfresh_rest => by
    have hy_fresh_body : (Moist.MIR.freeVars body).contains y = false :=
      hfresh_body (y, e_y, er_y) (List.Mem.head _)
    have hy_fresh_rest : ∀ r ∈ rest, (Moist.MIR.freeVars r.2.1).contains y = false :=
      fun r hr => hfresh_rest (y, e_y, er_y) (List.Mem.head _) r hr
    have hiBrest_fresh_body : ∀ b ∈ iB_rest, (Moist.MIR.freeVars body).contains b.1 = false :=
      fun b hb => hfresh_body b (List.Mem.tail _ hb)
    have hiBrest_fresh_rest : ∀ b ∈ iB_rest, ∀ r ∈ rest,
        (Moist.MIR.freeVars r.2.1).contains b.1 = false :=
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
      (hbody : ∀ ib ∈ ibs, (Moist.MIR.freeVars body).contains ib.1 = false)
      (hrest : ∀ ib ∈ ibs, ∀ r ∈ rest,
               (Moist.MIR.freeVars r.2.1).contains ib.1 = false)
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
    Moist.MIR.flattenLetBinds ((v, e', er) :: rest) =
      (v, e', er) :: Moist.MIR.flattenLetBinds rest := by
  show Moist.MIR.flattenLetBindsStep (v, e', er)
      (Moist.MIR.flattenLetBinds rest) =
    (v, e', er) :: Moist.MIR.flattenLetBinds rest
  unfold Moist.MIR.flattenLetBindsStep
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
                    (.Let (Moist.MIR.flattenLetBinds binds) body) := by
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
                            (.Let (Moist.MIR.flattenLetBinds rest) body) := ih
    have h4 : MIRCtxRefines (.Let (ibs ++ [(v, ibody, er)]) (.Let rest body))
                            (.Let (ibs ++ [(v, ibody, er)])
                              (.Let (Moist.MIR.flattenLetBinds rest) body)) :=
      mirCtxRefines_let_body h3
    have h5 : MIRCtxRefines
                (.Let (ibs ++ [(v, ibody, er)])
                  (.Let (Moist.MIR.flattenLetBinds rest) body))
                (.Let ((ibs ++ [(v, ibody, er)]) ++
                  Moist.MIR.flattenLetBinds rest) body) :=
      mirCtxRefines_let_flatten_body_fwd _ _ _
    have heq2 : (ibs ++ [(v, ibody, er)]) ++ Moist.MIR.flattenLetBinds rest =
                ibs ++ (v, ibody, er) :: Moist.MIR.flattenLetBinds rest := by
      simp [List.append_assoc]
    rw [heq2] at h5
    have heq3 : Moist.MIR.flattenLetBinds ((v, .Let ibs ibody, er) :: rest) =
                ibs ++ (v, ibody, er) :: Moist.MIR.flattenLetBinds rest := by
      show Moist.MIR.flattenLetBindsStep (v, .Let ibs ibody, er)
          (Moist.MIR.flattenLetBinds rest) =
        ibs ++ (v, ibody, er) :: Moist.MIR.flattenLetBinds rest
      rfl
    rw [heq3]
    exact mirCtxRefines_trans h1 (mirCtxRefines_trans h2
          (mirCtxRefines_trans h4 h5))
  | @nonLetCons v e' er rest hnotlet _ ih =>
    have h1 : MIRCtxRefines (.Let ((v, e', er) :: rest) body)
                            (.Let [(v, e', er)] (.Let rest body)) :=
      mirCtxRefines_let_cons_split_fwd _ _ _
    have h2 : MIRCtxRefines (.Let rest body)
                            (.Let (Moist.MIR.flattenLetBinds rest) body) := ih
    have h3 : MIRCtxRefines (.Let [(v, e', er)] (.Let rest body))
                            (.Let [(v, e', er)]
                              (.Let (Moist.MIR.flattenLetBinds rest) body)) :=
      mirCtxRefines_let_body h2
    have h4 : MIRCtxRefines (.Let [(v, e', er)]
                              (.Let (Moist.MIR.flattenLetBinds rest) body))
                            (.Let ((v, e', er) ::
                              Moist.MIR.flattenLetBinds rest) body) :=
      mirCtxRefines_let_cons_split_bwd _ _ _
    have heq : Moist.MIR.flattenLetBinds ((v, e', er) :: rest) =
               (v, e', er) :: Moist.MIR.flattenLetBinds rest :=
      flattenLetBinds_cons_non_let_eq v e' er rest hnotlet
    rw [heq]
    exact mirCtxRefines_trans h1 (mirCtxRefines_trans h3 h4)

/-- `flattenLetBinds` refines backward under `FlattenReady`. -/
theorem mirCtxRefines_flattenLetBinds_bwd (body : Expr) :
    ∀ (binds : List (VarId × Expr × Bool)),
      FlattenReady body binds →
      MIRCtxRefines (.Let (Moist.MIR.flattenLetBinds binds) body)
                    (.Let binds body) := by
  intro binds hfr
  induction hfr with
  | nil =>
    show MIRCtxRefines (.Let [] body) (.Let [] body)
    exact mirCtxRefines_refl _
  | @letCons v ibs ibody er rest hfresh_body hfresh_rest _ ih =>
    have heq3 : Moist.MIR.flattenLetBinds ((v, .Let ibs ibody, er) :: rest) =
                ibs ++ (v, ibody, er) :: Moist.MIR.flattenLetBinds rest := by
      show Moist.MIR.flattenLetBindsStep (v, .Let ibs ibody, er)
          (Moist.MIR.flattenLetBinds rest) =
        ibs ++ (v, ibody, er) :: Moist.MIR.flattenLetBinds rest
      rfl
    rw [heq3]
    have heq2 : ibs ++ (v, ibody, er) :: Moist.MIR.flattenLetBinds rest =
                (ibs ++ [(v, ibody, er)]) ++ Moist.MIR.flattenLetBinds rest := by
      simp [List.append_assoc]
    rw [heq2]
    have h5 : MIRCtxRefines
                (.Let ((ibs ++ [(v, ibody, er)]) ++
                  Moist.MIR.flattenLetBinds rest) body)
                (.Let (ibs ++ [(v, ibody, er)])
                  (.Let (Moist.MIR.flattenLetBinds rest) body)) :=
      mirCtxRefines_let_flatten_body_bwd _ _ _
    have h3 : MIRCtxRefines (.Let (Moist.MIR.flattenLetBinds rest) body)
                            (.Let rest body) := ih
    have h4 : MIRCtxRefines (.Let (ibs ++ [(v, ibody, er)])
                              (.Let (Moist.MIR.flattenLetBinds rest) body))
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
    have heq : Moist.MIR.flattenLetBinds ((v, e', er) :: rest) =
               (v, e', er) :: Moist.MIR.flattenLetBinds rest :=
      flattenLetBinds_cons_non_let_eq v e' er rest hnotlet
    rw [heq]
    have h4 : MIRCtxRefines (.Let ((v, e', er) ::
                              Moist.MIR.flattenLetBinds rest) body)
                            (.Let [(v, e', er)]
                              (.Let (Moist.MIR.flattenLetBinds rest) body)) :=
      mirCtxRefines_let_cons_split_fwd _ _ _
    have h2 : MIRCtxRefines (.Let (Moist.MIR.flattenLetBinds rest) body)
                            (.Let rest body) := ih
    have h3 : MIRCtxRefines (.Let [(v, e', er)]
                              (.Let (Moist.MIR.flattenLetBinds rest) body))
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
      Moist.MIR.maxUidExprBinds (Moist.MIR.flattenLetBinds binds) ≤
      Moist.MIR.maxUidExprBinds binds
  | [] => by simp [Moist.MIR.flattenLetBinds, Moist.MIR.maxUidExprBinds]
  | (v, e', er) :: rest => by
    have ih : Moist.MIR.maxUidExprBinds (Moist.MIR.flattenLetBinds rest) ≤
              Moist.MIR.maxUidExprBinds rest :=
      maxUidExprBinds_flattenLetBinds_le rest
    show Moist.MIR.maxUidExprBinds
      (Moist.MIR.flattenLetBindsStep (v, e', er) (Moist.MIR.flattenLetBinds rest)) ≤
      Moist.MIR.maxUidExprBinds ((v, e', er) :: rest)
    unfold Moist.MIR.flattenLetBindsStep
    cases e' with
    | Let ibs ibody =>
      have h_append := Moist.MIR.maxUidExprBinds_append ibs
        ((v, ibody, er) :: Moist.MIR.flattenLetBinds rest)
      have h_rest_cons : Moist.MIR.maxUidExprBinds
          ((v, ibody, er) :: Moist.MIR.flattenLetBinds rest) =
          max v.uid (max (Moist.MIR.maxUidExpr ibody)
            (Moist.MIR.maxUidExprBinds (Moist.MIR.flattenLetBinds rest))) := by
        simp only [Moist.MIR.maxUidExprBinds]
      rw [h_rest_cons] at h_append
      simp only [Moist.MIR.maxUidExpr, Moist.MIR.maxUidExprBinds] at h_append ⊢
      omega
    | Var _ | Lit _ | Builtin _ | Error | Lam _ _ | Fix _ _
    | App _ _ | Force _ | Delay _ | Case _ _ | Constr _ _ =>
      show Moist.MIR.maxUidExprBinds
        ((v, _, er) :: Moist.MIR.flattenLetBinds rest) ≤
        Moist.MIR.maxUidExprBinds ((v, _, er) :: rest)
      simp only [Moist.MIR.maxUidExprBinds]
      omega

/-! ## Section 5. Let-hoist-force primitive

`.Force (.Let [(v, rhs, false)] body) ≈ .Let [(v, rhs, false)] (.Force body)`.

The non-trivial direction is the stack-frame helper that bridges the
asymmetry: the LHS has a `funV (VLam body' ρ) :: force :: π` stack, while
the RHS has a `funV (VLam (.Force body') ρ) :: π` stack. Both fire on a
value to land in `compute (.force :: π_i) (ρ_i.extend v_i) body'`. -/

/-- Stack-frame helper for the let-hoist-force primitive. The two `funV`
    frames are *not* identical — the LHS body is `body'` with a `.force`
    frame underneath, while the RHS body is `.Force body'` with no extra
    frame underneath. They both fire to `compute (.force :: π_i)
    (ρ_i.extend v_i) body'`. -/
private theorem stackRefK_funV_force_body {i d : Nat} {body : Term}
    {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv}
    (hclosed : closedAt (d + 1) body = true)
    (henv : EnvRefinesK i d ρ₁ ρ₂)
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i
      (.funV (.VLam body ρ₁) :: .force :: π₁)
      (.funV (.VLam (.Force body) ρ₂) :: π₂) := by
  intro j hj v₁ v₂ hv
  -- LHS: 1 step to compute (.force :: π₁) (ρ₁.extend v₁) body
  have h_lhs :
      steps 1 (State.ret (.funV (.VLam body ρ₁) :: .force :: π₁) v₁) =
        State.compute (.force :: π₁) (ρ₁.extend v₁) body := by rfl
  -- RHS: 2 steps to compute (.force :: π₂) (ρ₂.extend v₂) body
  have h_rhs :
      steps 2 (State.ret (.funV (.VLam (.Force body) ρ₂) :: π₂) v₂) =
        State.compute (.force :: π₂) (ρ₂.extend v₂) body := by rfl
  apply obsRefinesK_of_steps_left h_lhs
  apply obsRefinesK_of_steps_right h_rhs
  have henv' : EnvRefinesK j d ρ₁ ρ₂ := by
    intro n hn hnd
    obtain ⟨w₁, w₂, hl, hr, hw⟩ := henv n hn hnd
    exact ⟨w₁, w₂, hl, hr, valueRefinesK_mono hj _ _ hw⟩
  have henv_ext : EnvRefinesK j (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) :=
    envRefinesK_extend henv' hv
  have hπ' : StackRefK ValueRefinesK j (.force :: π₁) (.force :: π₂) :=
    stackRefK_force_augment (stackRefK_mono hj hπ)
  exact ftlr (d + 1) body hclosed j j (Nat.le_refl _) (ρ₁.extend v₁) (ρ₂.extend v₂)
    henv_ext j (Nat.le_refl _) (.force :: π₁) (.force :: π₂) hπ'

/-- Symmetric: `funV (VLam (.Force body) ρ₁) :: π₁` on the left related to
    `funV (VLam body ρ₂) :: force :: π₂` on the right. -/
private theorem stackRefK_funV_body_force {i d : Nat} {body : Term}
    {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv}
    (hclosed : closedAt (d + 1) body = true)
    (henv : EnvRefinesK i d ρ₁ ρ₂)
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i
      (.funV (.VLam (.Force body) ρ₁) :: π₁)
      (.funV (.VLam body ρ₂) :: .force :: π₂) := by
  intro j hj v₁ v₂ hv
  have h_lhs :
      steps 2 (State.ret (.funV (.VLam (.Force body) ρ₁) :: π₁) v₁) =
        State.compute (.force :: π₁) (ρ₁.extend v₁) body := by rfl
  have h_rhs :
      steps 1 (State.ret (.funV (.VLam body ρ₂) :: .force :: π₂) v₂) =
        State.compute (.force :: π₂) (ρ₂.extend v₂) body := by rfl
  apply obsRefinesK_of_steps_left h_lhs
  apply obsRefinesK_of_steps_right h_rhs
  have henv' : EnvRefinesK j d ρ₁ ρ₂ := by
    intro n hn hnd
    obtain ⟨w₁, w₂, hl, hr, hw⟩ := henv n hn hnd
    exact ⟨w₁, w₂, hl, hr, valueRefinesK_mono hj _ _ hw⟩
  have henv_ext : EnvRefinesK j (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) :=
    envRefinesK_extend henv' hv
  have hπ' : StackRefK ValueRefinesK j (.force :: π₁) (.force :: π₂) :=
    stackRefK_force_augment (stackRefK_mono hj hπ)
  exact ftlr (d + 1) body hclosed j j (Nat.le_refl _) (ρ₁.extend v₁) (ρ₂.extend v₂)
    henv_ext j (Nat.le_refl _) (.force :: π₁) (.force :: π₂) hπ'

/-- Lowering shape lemma: `.Force (.Let [(v, rhs, false)] body)` lowers
    iff both `rhs` and `body` lower, and the result is
    `.Force (.Apply (.Lam 0 t_body) t_rhs)`. -/
private theorem lowerTotalExpr_force_let {env : List VarId} (v : VarId)
    {rhs body : Expr} {t_rhs t_body : Term}
    (h_rhs : lowerTotalExpr env rhs = some t_rhs)
    (h_body : lowerTotalExpr (v :: env) body = some t_body) :
    lowerTotalExpr env (.Force (.Let [(v, rhs, false)] body)) =
      some (.Force (.Apply (.Lam 0 t_body) t_rhs)) := by
  have h_rhs' : lowerTotal env (Moist.MIR.expandFix rhs) = some t_rhs := h_rhs
  have h_body' : lowerTotal (v :: env) (Moist.MIR.expandFix body) = some t_body := h_body
  show lowerTotal env (Moist.MIR.expandFix (.Force (.Let [(v, rhs, false)] body))) =
    some (.Force (.Apply (.Lam 0 t_body) t_rhs))
  simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
             Moist.MIR.lowerTotalLet, Option.bind_eq_bind, Option.bind_some,
             h_rhs', h_body']

/-- Lowering shape lemma: `.Let [(v, rhs, false)] (.Force body)` lowers
    to `.Apply (.Lam 0 (.Force t_body)) t_rhs` when both lower. -/
private theorem lowerTotalExpr_let_force {env : List VarId} (v : VarId)
    {rhs body : Expr} {t_rhs t_body : Term}
    (h_rhs : lowerTotalExpr env rhs = some t_rhs)
    (h_body : lowerTotalExpr (v :: env) body = some t_body) :
    lowerTotalExpr env (.Let [(v, rhs, false)] (.Force body)) =
      some (.Apply (.Lam 0 (.Force t_body)) t_rhs) := by
  have h_rhs' : lowerTotal env (Moist.MIR.expandFix rhs) = some t_rhs := h_rhs
  have h_body' : lowerTotal (v :: env) (Moist.MIR.expandFix body) = some t_body := h_body
  show lowerTotal env (Moist.MIR.expandFix (.Let [(v, rhs, false)] (.Force body))) =
    some (.Apply (.Lam 0 (.Force t_body)) t_rhs)
  simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
             Moist.MIR.lowerTotalLet, Option.bind_eq_bind, Option.bind_some,
             h_rhs', h_body']

/-- The `.Force (.Let ...)` lowering succeeds iff both rhs and body lower. -/
private theorem lowerTotalExpr_force_let_isSome (env : List VarId) (v : VarId)
    (rhs body : Expr) :
    (lowerTotalExpr env (.Force (.Let [(v, rhs, false)] body))).isSome ↔
      (lowerTotalExpr env rhs).isSome ∧
      (lowerTotalExpr (v :: env) body).isSome := by
  constructor
  · intro hsome
    have h : (lowerTotal env (Moist.MIR.expandFix
        (.Force (.Let [(v, rhs, false)] body)))).isSome := hsome
    simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
               Moist.MIR.lowerTotalLet, Option.bind_eq_bind] at h
    cases hr : lowerTotal env (Moist.MIR.expandFix rhs) with
    | none => rw [hr] at h; simp at h
    | some t_r =>
      rw [hr] at h
      simp only [Option.bind_some] at h
      cases hb : lowerTotal (v :: env) (Moist.MIR.expandFix body) with
      | none => rw [hb] at h; simp at h
      | some t_b =>
        have hr' : lowerTotalExpr env rhs = some t_r := hr
        have hb' : lowerTotalExpr (v :: env) body = some t_b := hb
        exact ⟨by rw [hr']; rfl, by rw [hb']; rfl⟩
  · rintro ⟨hr, hb⟩
    cases hr' : lowerTotalExpr env rhs with
    | none => rw [hr'] at hr; exact absurd hr (by simp)
    | some t_r =>
      cases hb' : lowerTotalExpr (v :: env) body with
      | none => rw [hb'] at hb; exact absurd hb (by simp)
      | some t_b =>
        rw [lowerTotalExpr_force_let v hr' hb']
        rfl

/-- The `.Let ... (.Force ...)` lowering succeeds iff both rhs and body lower. -/
private theorem lowerTotalExpr_let_force_isSome (env : List VarId) (v : VarId)
    (rhs body : Expr) :
    (lowerTotalExpr env (.Let [(v, rhs, false)] (.Force body))).isSome ↔
      (lowerTotalExpr env rhs).isSome ∧
      (lowerTotalExpr (v :: env) body).isSome := by
  constructor
  · intro hsome
    have h : (lowerTotal env (Moist.MIR.expandFix
        (.Let [(v, rhs, false)] (.Force body)))).isSome := hsome
    simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
               Moist.MIR.lowerTotalLet, Option.bind_eq_bind] at h
    cases hr : lowerTotal env (Moist.MIR.expandFix rhs) with
    | none => rw [hr] at h; simp at h
    | some t_r =>
      rw [hr] at h
      simp only [Option.bind_some] at h
      cases hb : lowerTotal (v :: env) (Moist.MIR.expandFix body) with
      | none => rw [hb] at h; simp at h
      | some t_b =>
        have hr' : lowerTotalExpr env rhs = some t_r := hr
        have hb' : lowerTotalExpr (v :: env) body = some t_b := hb
        exact ⟨by rw [hr']; rfl, by rw [hb']; rfl⟩
  · rintro ⟨hr, hb⟩
    cases hr' : lowerTotalExpr env rhs with
    | none => rw [hr'] at hr; exact absurd hr (by simp)
    | some t_r =>
      cases hb' : lowerTotalExpr (v :: env) body with
      | none => rw [hb'] at hb; exact absurd hb (by simp)
      | some t_b =>
        rw [lowerTotalExpr_let_force v hr' hb']
        rfl

/-- **MIRRefines for let-hoist-force (forward)**:
    `.Force (.Let [(v, rhs, false)] body) ⊑ᴹ .Let [(v, rhs, false)] (.Force body)`. -/
theorem mirRefines_let_hoist_force_fwd (v : VarId) (rhs body : Expr) :
    MIRRefines (.Force (.Let [(v, rhs, false)] body))
               (.Let [(v, rhs, false)] (.Force body)) := by
  refine ⟨?_, ?_⟩
  · intro env hsome
    rw [(lowerTotalExpr_force_let_isSome env v rhs body).mp hsome |>
        (lowerTotalExpr_let_force_isSome env v rhs body).mpr]
  · intro d k env hlen
    cases hr : lowerTotalExpr env rhs with
    | none =>
      have h_lhs : lowerTotalExpr env (.Force (.Let [(v, rhs, false)] body)) = none := by
        cases h : lowerTotalExpr env (.Force (.Let [(v, rhs, false)] body)) with
        | none => rfl
        | some _ =>
          have hsome : (lowerTotalExpr env (.Force (.Let [(v, rhs, false)] body))).isSome := by
            rw [h]; rfl
          have := (lowerTotalExpr_force_let_isSome env v rhs body).mp hsome
          rw [hr] at this; exact absurd this.1 (by simp)
      rw [h_lhs]; trivial
    | some t_r =>
      cases hb : lowerTotalExpr (v :: env) body with
      | none =>
        have h_lhs : lowerTotalExpr env (.Force (.Let [(v, rhs, false)] body)) = none := by
          cases h : lowerTotalExpr env (.Force (.Let [(v, rhs, false)] body)) with
          | none => rfl
          | some _ =>
            have hsome : (lowerTotalExpr env (.Force (.Let [(v, rhs, false)] body))).isSome := by
              rw [h]; rfl
            have := (lowerTotalExpr_force_let_isSome env v rhs body).mp hsome
            rw [hb] at this; exact absurd this.2 (by simp)
        rw [h_lhs]; trivial
      | some t_b =>
        rw [lowerTotalExpr_force_let v hr hb, lowerTotalExpr_let_force v hr hb]
        simp only
        intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
        -- LHS state: compute π₁ ρ₁ (.Force (.Apply (.Lam 0 t_b) t_r))
        -- 4 admin steps → compute (funV (VLam t_b ρ₁) :: force :: π₁) ρ₁ t_r
        have h_steps_lhs :
            steps 4 (State.compute π₁ ρ₁ (.Force (.Apply (.Lam 0 t_b) t_r))) =
              State.compute (.funV (.VLam t_b ρ₁) :: .force :: π₁) ρ₁ t_r := by rfl
        -- RHS state: compute π₂ ρ₂ (.Apply (.Lam 0 (.Force t_b)) t_r)
        -- 3 admin steps → compute (funV (VLam (.Force t_b) ρ₂) :: π₂) ρ₂ t_r
        have h_steps_rhs :
            steps 3 (State.compute π₂ ρ₂ (.Apply (.Lam 0 (.Force t_b)) t_r)) =
              State.compute (.funV (.VLam (.Force t_b) ρ₂) :: π₂) ρ₂ t_r := by rfl
        apply obsRefinesK_of_steps_left h_steps_lhs
        apply obsRefinesK_of_steps_right h_steps_rhs
        have hclosed_r : closedAt env.length t_r :=
          Moist.Verified.MIR.lowerTotal_closedAt env _ t_r hr
        have hclosed_b : closedAt (env.length + 1) t_b := by
          have := Moist.Verified.MIR.lowerTotal_closedAt (v :: env) _ t_b hb
          simpa [List.length_cons] using this
        have hd_eq : d = env.length := hlen.symm
        subst hd_eq
        have henv_j : EnvRefinesK j env.length ρ₁ ρ₂ := by
          intro n hn hnd
          obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv n hn hnd
          exact ⟨w₁, w₂, hl, hr', hw⟩
        have hπ_aug : StackRefK ValueRefinesK i
            (.funV (.VLam t_b ρ₁) :: .force :: π₁)
            (.funV (.VLam (.Force t_b) ρ₂) :: π₂) := by
          have henv_i : EnvRefinesK i env.length ρ₁ ρ₂ := by
            intro n hn hnd
            obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv_j n hn hnd
            exact ⟨w₁, w₂, hl, hr', valueRefinesK_mono hi _ _ hw⟩
          exact stackRefK_funV_force_body hclosed_b henv_i hπ
        exact ftlr env.length t_r hclosed_r j j (Nat.le_refl _) ρ₁ ρ₂ henv_j i hi
          (.funV (.VLam t_b ρ₁) :: .force :: π₁)
          (.funV (.VLam (.Force t_b) ρ₂) :: π₂) hπ_aug

/-- **MIRRefines for let-hoist-force (backward)**:
    `.Let [(v, rhs, false)] (.Force body) ⊑ᴹ .Force (.Let [(v, rhs, false)] body)`. -/
theorem mirRefines_let_hoist_force_bwd (v : VarId) (rhs body : Expr) :
    MIRRefines (.Let [(v, rhs, false)] (.Force body))
               (.Force (.Let [(v, rhs, false)] body)) := by
  refine ⟨?_, ?_⟩
  · intro env hsome
    rw [(lowerTotalExpr_let_force_isSome env v rhs body).mp hsome |>
        (lowerTotalExpr_force_let_isSome env v rhs body).mpr]
  · intro d k env hlen
    cases hr : lowerTotalExpr env rhs with
    | none =>
      have h_lhs : lowerTotalExpr env (.Let [(v, rhs, false)] (.Force body)) = none := by
        cases h : lowerTotalExpr env (.Let [(v, rhs, false)] (.Force body)) with
        | none => rfl
        | some _ =>
          have hsome : (lowerTotalExpr env (.Let [(v, rhs, false)] (.Force body))).isSome := by
            rw [h]; rfl
          have := (lowerTotalExpr_let_force_isSome env v rhs body).mp hsome
          rw [hr] at this; exact absurd this.1 (by simp)
      rw [h_lhs]; trivial
    | some t_r =>
      cases hb : lowerTotalExpr (v :: env) body with
      | none =>
        have h_lhs : lowerTotalExpr env (.Let [(v, rhs, false)] (.Force body)) = none := by
          cases h : lowerTotalExpr env (.Let [(v, rhs, false)] (.Force body)) with
          | none => rfl
          | some _ =>
            have hsome : (lowerTotalExpr env (.Let [(v, rhs, false)] (.Force body))).isSome := by
              rw [h]; rfl
            have := (lowerTotalExpr_let_force_isSome env v rhs body).mp hsome
            rw [hb] at this; exact absurd this.2 (by simp)
        rw [h_lhs]; trivial
      | some t_b =>
        rw [lowerTotalExpr_let_force v hr hb, lowerTotalExpr_force_let v hr hb]
        simp only
        intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
        have h_steps_lhs :
            steps 3 (State.compute π₁ ρ₁ (.Apply (.Lam 0 (.Force t_b)) t_r)) =
              State.compute (.funV (.VLam (.Force t_b) ρ₁) :: π₁) ρ₁ t_r := by rfl
        have h_steps_rhs :
            steps 4 (State.compute π₂ ρ₂ (.Force (.Apply (.Lam 0 t_b) t_r))) =
              State.compute (.funV (.VLam t_b ρ₂) :: .force :: π₂) ρ₂ t_r := by rfl
        apply obsRefinesK_of_steps_left h_steps_lhs
        apply obsRefinesK_of_steps_right h_steps_rhs
        have hclosed_r : closedAt env.length t_r :=
          Moist.Verified.MIR.lowerTotal_closedAt env _ t_r hr
        have hclosed_b : closedAt (env.length + 1) t_b := by
          have := Moist.Verified.MIR.lowerTotal_closedAt (v :: env) _ t_b hb
          simpa [List.length_cons] using this
        have hd_eq : d = env.length := hlen.symm
        subst hd_eq
        have henv_j : EnvRefinesK j env.length ρ₁ ρ₂ := by
          intro n hn hnd
          obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv n hn hnd
          exact ⟨w₁, w₂, hl, hr', hw⟩
        have hπ_aug : StackRefK ValueRefinesK i
            (.funV (.VLam (.Force t_b) ρ₁) :: π₁)
            (.funV (.VLam t_b ρ₂) :: .force :: π₂) := by
          have henv_i : EnvRefinesK i env.length ρ₁ ρ₂ := by
            intro n hn hnd
            obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv_j n hn hnd
            exact ⟨w₁, w₂, hl, hr', valueRefinesK_mono hi _ _ hw⟩
          exact stackRefK_funV_body_force hclosed_b henv_i hπ
        exact ftlr env.length t_r hclosed_r j j (Nat.le_refl _) ρ₁ ρ₂ henv_j i hi
          (.funV (.VLam (.Force t_b) ρ₁) :: π₁)
          (.funV (.VLam t_b ρ₂) :: .force :: π₂) hπ_aug

private theorem let_hoist_force_close_pres_fwd (v : VarId) (rhs body : Expr) :
    ∀ env k t₁ t₂,
      lowerTotalExpr env (.Force (.Let [(v, rhs, false)] body)) = some t₁ →
      lowerTotalExpr env (.Let [(v, rhs, false)] (.Force body)) = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true := by
  intro env k t₁ t₂ h₁ h₂ hc
  have hsome₁ : (lowerTotalExpr env (.Force (.Let [(v, rhs, false)] body))).isSome := by
    rw [h₁]; exact rfl
  obtain ⟨hr_some, hb_some⟩ :=
    (lowerTotalExpr_force_let_isSome env v rhs body).mp hsome₁
  cases hr : lowerTotalExpr env rhs with
  | none => rw [hr] at hr_some; exact absurd hr_some (by simp)
  | some t_r =>
    cases hb : lowerTotalExpr (v :: env) body with
    | none => rw [hb] at hb_some; exact absurd hb_some (by simp)
    | some t_b =>
      rw [lowerTotalExpr_force_let v hr hb] at h₁
      rw [lowerTotalExpr_let_force v hr hb] at h₂
      injection h₁ with h₁; subst h₁
      injection h₂ with h₂; subst h₂
      -- Both forms have closedAt k = closedAt (k+1) t_b && closedAt k t_r
      simp only [closedAt, Bool.and_eq_true] at hc ⊢
      exact ⟨hc.1, hc.2⟩

private theorem let_hoist_force_close_pres_bwd (v : VarId) (rhs body : Expr) :
    ∀ env k t₁ t₂,
      lowerTotalExpr env (.Let [(v, rhs, false)] (.Force body)) = some t₁ →
      lowerTotalExpr env (.Force (.Let [(v, rhs, false)] body)) = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true := by
  intro env k t₁ t₂ h₁ h₂ hc
  have hsome₁ : (lowerTotalExpr env (.Let [(v, rhs, false)] (.Force body))).isSome := by
    rw [h₁]; exact rfl
  obtain ⟨hr_some, hb_some⟩ :=
    (lowerTotalExpr_let_force_isSome env v rhs body).mp hsome₁
  cases hr : lowerTotalExpr env rhs with
  | none => rw [hr] at hr_some; exact absurd hr_some (by simp)
  | some t_r =>
    cases hb : lowerTotalExpr (v :: env) body with
    | none => rw [hb] at hb_some; exact absurd hb_some (by simp)
    | some t_b =>
      rw [lowerTotalExpr_let_force v hr hb] at h₁
      rw [lowerTotalExpr_force_let v hr hb] at h₂
      injection h₁ with h₁; subst h₁
      injection h₂ with h₂; subst h₂
      simp only [closedAt, Bool.and_eq_true] at hc ⊢
      exact ⟨hc.1, hc.2⟩

theorem mirCtxRefines_let_hoist_force_fwd (v : VarId) (rhs body : Expr) :
    MIRCtxRefines (.Force (.Let [(v, rhs, false)] body))
                  (.Let [(v, rhs, false)] (.Force body)) :=
  mirRefines_to_mirCtxRefines (mirRefines_let_hoist_force_fwd v rhs body)
    (let_hoist_force_close_pres_fwd v rhs body)

theorem mirCtxRefines_let_hoist_force_bwd (v : VarId) (rhs body : Expr) :
    MIRCtxRefines (.Let [(v, rhs, false)] (.Force body))
                  (.Force (.Let [(v, rhs, false)] body)) :=
  mirRefines_to_mirCtxRefines (mirRefines_let_hoist_force_bwd v rhs body)
    (let_hoist_force_close_pres_bwd v rhs body)

/-! ## Section 6. Let-hoist-app-left primitive

`.App (.Let [(v, rhs, false)] body) xArg ≈ .Let [(v, rhs, false)] (.App body xArg)`
when `v ∉ freeVars xArg`.

The crux: the RHS lowers `xArg` under an extended env (since it's now under
the let binder), which by `lowerTotal_prepend_unused` produces the **shifted**
lowering of `xArg`. The forward direction needs `renameRefinesR (shiftRename 1)`
to relate the LHS's plain `xArg` lowering to the RHS's shifted form. -/

/-- Builds a `funV :: π` stack from a value relation and a stack relation. -/
private theorem stackRefK_funV_top_aug {i : Nat} {vf₁ vf₂ : CekValue}
    {π₁ π₂ : Stack} (hvf : ValueRefinesK i vf₁ vf₂)
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i (.funV vf₁ :: π₁) (.funV vf₂ :: π₂) := by
  intro j hj w₁ w₂ hw
  match j with
  | 0 => exact obsRefinesK_zero_ret
  | n + 1 =>
    obsRefinesK_of_step_auto
    -- Demote hvf to index n+1 to get useful structure
    have hvf' : ValueRefinesK (n + 1) vf₁ vf₂ := valueRefinesK_mono hj _ _ hvf
    match vf₁, vf₂, hvf' with
    | .VLam body₁ ρ₁', .VLam body₂ ρ₂', hvf' =>
      simp only [step]
      simp only [ValueRefinesK] at hvf'
      exact hvf' n (by omega) w₁ w₂ (valueRefinesK_mono (by omega) w₁ w₂ hw)
        n (Nat.le_refl _) π₁ π₂
        (Moist.Verified.Contextual.SoundnessRefines.stackRefK_mono (by omega) hπ)
    | .VBuiltin b₁ args₁ ea₁, .VBuiltin b₂ args₂ ea₂, hvf' =>
      simp only [ValueRefinesK] at hvf'
      obtain ⟨rfl, rfl, hargs⟩ := hvf'
      simp only [step]
      split
      · split
        · rename_i rest _
          have hval : ValueRefinesK (n + 1)
              (.VBuiltin b₁ (w₁ :: args₁) rest) (.VBuiltin b₁ (w₂ :: args₂) rest) := by
            simp only [ValueRefinesK]
            refine ⟨trivial, trivial, ?_⟩
            exact ⟨valueRefinesK_mono (by omega) w₁ w₂ hw,
                   listRel_valueRefinesK_mono (by omega) hargs⟩
          exact obsRefinesK_mono (by omega : n ≤ n + 1)
            (Moist.Verified.Contextual.SoundnessRefines.stackRefK_mono (by omega) hπ
              (n + 1) (by omega) _ _ hval)
        · exact evalBuiltin_compat_refines
            ⟨valueRefinesK_mono (by omega) w₁ w₂ hw,
             listRel_valueRefinesK_mono (by omega) hargs⟩
            (Moist.Verified.Contextual.SoundnessRefines.stackRefK_mono (by omega) hπ)
      · exact obsRefinesK_error _
    | .VCon _, .VCon _, _ => simp only [step]; exact obsRefinesK_error _
    | .VDelay _ _, .VDelay _ _, _ => simp only [step]; exact obsRefinesK_error _
    | .VConstr _ _, .VConstr _ _, _ => simp only [step]; exact obsRefinesK_error _
    | .VCon _, .VLam _ _, hvf' | .VCon _, .VDelay _ _, hvf'
    | .VCon _, .VConstr _ _, hvf' | .VCon _, .VBuiltin _ _ _, hvf'
    | .VLam _ _, .VCon _, hvf' | .VLam _ _, .VDelay _ _, hvf'
    | .VLam _ _, .VConstr _ _, hvf' | .VLam _ _, .VBuiltin _ _ _, hvf'
    | .VDelay _ _, .VCon _, hvf' | .VDelay _ _, .VLam _ _, hvf'
    | .VDelay _ _, .VConstr _ _, hvf' | .VDelay _ _, .VBuiltin _ _ _, hvf'
    | .VConstr _ _, .VCon _, hvf' | .VConstr _ _, .VLam _ _, hvf'
    | .VConstr _ _, .VDelay _ _, hvf' | .VConstr _ _, .VBuiltin _ _ _, hvf'
    | .VBuiltin _ _ _, .VCon _, hvf' | .VBuiltin _ _ _, .VLam _ _, hvf'
    | .VBuiltin _ _ _, .VDelay _ _, hvf' | .VBuiltin _ _ _, .VConstr _ _, hvf' =>
      simp only [ValueRefinesK] at hvf'

/-- Forward stack-frame helper: relates the augmented stacks at the
    `arg`-frame layer (after the funVs fire). -/
private theorem stackRefK_arg_shift_fwd {i d : Nat}
    {t_x : Term} {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv} {v₂ : CekValue}
    (hclosed_x : closedAt d t_x = true)
    (henv : EnvRefinesK i d ρ₁ ρ₂)
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i
      (.arg t_x ρ₁ :: π₁)
      (.arg (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_x)
            (ρ₂.extend v₂) :: π₂) := by
  intro j hj vf₁ vf₂ hvf
  -- LHS step 1: arg fires → funV vf₁ :: π₁, compute ρ₁ t_x
  have h_lhs : steps 1 (State.ret (.arg t_x ρ₁ :: π₁) vf₁) =
               State.compute (.funV vf₁ :: π₁) ρ₁ t_x := by rfl
  have h_rhs : steps 1 (State.ret (.arg (Moist.Verified.renameTerm
                          (Moist.Verified.shiftRename 1) t_x) (ρ₂.extend v₂) :: π₂) vf₂) =
               State.compute (.funV vf₂ :: π₂) (ρ₂.extend v₂)
                 (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_x) := by rfl
  apply obsRefinesK_of_steps_left h_lhs
  apply obsRefinesK_of_steps_right h_rhs
  -- Augment the stack with the new funV frames (which are vf-related).
  have hπ_funV : StackRefK ValueRefinesK j (.funV vf₁ :: π₁) (.funV vf₂ :: π₂) :=
    stackRefK_funV_top_aug hvf (Moist.Verified.Contextual.SoundnessRefines.stackRefK_mono hj hπ)
  -- Now apply renameRefinesR for t_x with ρ₁ and ρ₂.extend v₂
  have henv_j : EnvRefinesK j d ρ₁ ρ₂ := by
    intro n hn hnd
    obtain ⟨w₁, w₂, hl, hr, hw⟩ := henv n hn hnd
    exact ⟨w₁, w₂, hl, hr, valueRefinesK_mono hj _ _ hw⟩
  have henv_R : RenameEnvRefR (Moist.Verified.shiftRename 1) j d ρ₁ (ρ₂.extend v₂) :=
    envRefinesK_to_renameEnvRefR_shift henv_j
  exact renameRefinesR_shift1 d t_x hclosed_x j j (Nat.le_refl _) ρ₁ (ρ₂.extend v₂)
    henv_R j (Nat.le_refl _) (.funV vf₁ :: π₁) (.funV vf₂ :: π₂) hπ_funV

/-- Forward augmented stack helper for the let-hoist-app-left primitive
    at the funV-on-top layer. -/
private theorem stackRefK_letHoistAppLeft_fwd {i d : Nat}
    {t_b t_x : Term} {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv}
    (hclosed_b : closedAt (d + 1) t_b = true)
    (hclosed_x : closedAt d t_x = true)
    (henv : EnvRefinesK i d ρ₁ ρ₂)
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i
      (.funV (.VLam t_b ρ₁) :: .arg t_x ρ₁ :: π₁)
      (.funV (.VLam (.Apply t_b
        (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_x)) ρ₂) :: π₂) := by
  intro j hj v₁ v₂ hv
  -- LHS: funV fires (1 step) → compute (.arg t_x ρ₁ :: π₁) (ρ₁.extend v₁) t_b
  have h_lhs : steps 1 (State.ret (.funV (.VLam t_b ρ₁) :: .arg t_x ρ₁ :: π₁) v₁) =
               State.compute (.arg t_x ρ₁ :: π₁) (ρ₁.extend v₁) t_b := by rfl
  -- RHS: funV fires (1 step) then Apply unfolds (1 step) → arg shifted_x :: π₂, compute t_b
  have h_rhs : steps 2 (State.ret (.funV (.VLam (.Apply t_b
                  (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_x)) ρ₂) :: π₂) v₂) =
               State.compute (.arg (Moist.Verified.renameTerm
                  (Moist.Verified.shiftRename 1) t_x) (ρ₂.extend v₂) :: π₂)
                 (ρ₂.extend v₂) t_b := by rfl
  apply obsRefinesK_of_steps_left h_lhs
  apply obsRefinesK_of_steps_right h_rhs
  -- Both compute t_b. Apply ftlr with augmented arg-stacks.
  have henv_j : EnvRefinesK j d ρ₁ ρ₂ := by
    intro n hn hnd
    obtain ⟨w₁, w₂, hl, hr, hw⟩ := henv n hn hnd
    exact ⟨w₁, w₂, hl, hr, valueRefinesK_mono hj _ _ hw⟩
  have henv_ext : EnvRefinesK j (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) :=
    envRefinesK_extend henv_j hv
  have hπ_arg : StackRefK ValueRefinesK j
      (.arg t_x ρ₁ :: π₁)
      (.arg (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_x) (ρ₂.extend v₂) :: π₂) :=
    stackRefK_arg_shift_fwd hclosed_x henv_j (stackRefK_mono hj hπ)
  exact ftlr (d + 1) t_b hclosed_b j j (Nat.le_refl _) (ρ₁.extend v₁) (ρ₂.extend v₂)
    henv_ext j (Nat.le_refl _) _ _ hπ_arg

/-- Backward stack-frame helper: relates the augmented stacks at the
    `arg`-frame layer for the backward direction. The shift is now on the LHS. -/
private theorem stackRefK_arg_shift_bwd {i d : Nat}
    {t_x : Term} {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv} {v₁ : CekValue}
    (hclosed_x : closedAt d t_x = true)
    (henv : EnvRefinesK i d ρ₁ ρ₂)
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i
      (.arg (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_x)
            (ρ₁.extend v₁) :: π₁)
      (.arg t_x ρ₂ :: π₂) := by
  intro j hj vf₁ vf₂ hvf
  have h_lhs : steps 1 (State.ret (.arg (Moist.Verified.renameTerm
                          (Moist.Verified.shiftRename 1) t_x) (ρ₁.extend v₁) :: π₁) vf₁) =
               State.compute (.funV vf₁ :: π₁) (ρ₁.extend v₁)
                 (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_x) := by rfl
  have h_rhs : steps 1 (State.ret (.arg t_x ρ₂ :: π₂) vf₂) =
               State.compute (.funV vf₂ :: π₂) ρ₂ t_x := by rfl
  apply obsRefinesK_of_steps_left h_lhs
  apply obsRefinesK_of_steps_right h_rhs
  have hπ_funV : StackRefK ValueRefinesK j (.funV vf₁ :: π₁) (.funV vf₂ :: π₂) :=
    stackRefK_funV_top_aug hvf (Moist.Verified.Contextual.SoundnessRefines.stackRefK_mono hj hπ)
  -- Apply renameRefines (shiftRename 1) — backward direction places shift on LHS
  have henv_j : EnvRefinesK j d ρ₁ ρ₂ := by
    intro n hn hnd
    obtain ⟨w₁, w₂, hl, hr, hw⟩ := henv n hn hnd
    exact ⟨w₁, w₂, hl, hr, valueRefinesK_mono hj _ _ hw⟩
  have henv_RL : Moist.Verified.FundamentalRefines.RenameEnvRef
      (Moist.Verified.shiftRename 1) j d (ρ₁.extend v₁) ρ₂ :=
    Moist.Verified.FundamentalRefines.envRefinesK_to_renameEnvRef_shift henv_j
  exact Moist.Verified.FundamentalRefines.renameRefines_shift1 d t_x hclosed_x j j
    (Nat.le_refl _) (ρ₁.extend v₁) ρ₂ henv_RL j (Nat.le_refl _)
    (.funV vf₁ :: π₁) (.funV vf₂ :: π₂) hπ_funV

/-- Backward augmented stack helper for the let-hoist-app-left primitive. -/
private theorem stackRefK_letHoistAppLeft_bwd {i d : Nat}
    {t_b t_x : Term} {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv}
    (hclosed_b : closedAt (d + 1) t_b = true)
    (hclosed_x : closedAt d t_x = true)
    (henv : EnvRefinesK i d ρ₁ ρ₂)
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i
      (.funV (.VLam (.Apply t_b
        (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_x)) ρ₁) :: π₁)
      (.funV (.VLam t_b ρ₂) :: .arg t_x ρ₂ :: π₂) := by
  intro j hj v₁ v₂ hv
  have h_lhs : steps 2 (State.ret (.funV (.VLam (.Apply t_b
                  (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_x)) ρ₁) :: π₁) v₁) =
               State.compute (.arg (Moist.Verified.renameTerm
                  (Moist.Verified.shiftRename 1) t_x) (ρ₁.extend v₁) :: π₁)
                 (ρ₁.extend v₁) t_b := by rfl
  have h_rhs : steps 1 (State.ret (.funV (.VLam t_b ρ₂) :: .arg t_x ρ₂ :: π₂) v₂) =
               State.compute (.arg t_x ρ₂ :: π₂) (ρ₂.extend v₂) t_b := by rfl
  apply obsRefinesK_of_steps_left h_lhs
  apply obsRefinesK_of_steps_right h_rhs
  have henv_j : EnvRefinesK j d ρ₁ ρ₂ := by
    intro n hn hnd
    obtain ⟨w₁, w₂, hl, hr, hw⟩ := henv n hn hnd
    exact ⟨w₁, w₂, hl, hr, valueRefinesK_mono hj _ _ hw⟩
  have henv_ext : EnvRefinesK j (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) :=
    envRefinesK_extend henv_j hv
  have hπ_arg : StackRefK ValueRefinesK j
      (.arg (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_x) (ρ₁.extend v₁) :: π₁)
      (.arg t_x ρ₂ :: π₂) :=
    stackRefK_arg_shift_bwd hclosed_x henv_j (stackRefK_mono hj hπ)
  exact ftlr (d + 1) t_b hclosed_b j j (Nat.le_refl _) (ρ₁.extend v₁) (ρ₂.extend v₂)
    henv_ext j (Nat.le_refl _) _ _ hπ_arg

/-- Lowering shape lemma: `App (Let [(v, rhs, false)] body) xArg` lowers
    to `Apply (Apply (Lam 0 t_body) t_rhs) t_xArg`. -/
private theorem lowerTotalExpr_app_let {env : List VarId} (v : VarId)
    {rhs body xArg : Expr} {t_rhs t_body t_xArg : Term}
    (h_rhs : lowerTotalExpr env rhs = some t_rhs)
    (h_body : lowerTotalExpr (v :: env) body = some t_body)
    (h_xArg : lowerTotalExpr env xArg = some t_xArg) :
    lowerTotalExpr env (.App (.Let [(v, rhs, false)] body) xArg) =
      some (.Apply (.Apply (.Lam 0 t_body) t_rhs) t_xArg) := by
  have h_rhs' : lowerTotal env (Moist.MIR.expandFix rhs) = some t_rhs := h_rhs
  have h_body' : lowerTotal (v :: env) (Moist.MIR.expandFix body) = some t_body := h_body
  have h_xArg' : lowerTotal env (Moist.MIR.expandFix xArg) = some t_xArg := h_xArg
  show lowerTotal env (Moist.MIR.expandFix (.App (.Let [(v, rhs, false)] body) xArg)) =
    some (.Apply (.Apply (.Lam 0 t_body) t_rhs) t_xArg)
  simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
             Moist.MIR.lowerTotalLet, Option.bind_eq_bind, Option.bind_some,
             h_rhs', h_body', h_xArg']

/-- Lowering shape lemma for the RHS form `Let [(v, rhs, false)] (App body xArg)`,
    using the shifted xArg from `lowerTotal_prepend_unused`. -/
private theorem lowerTotalExpr_let_app {env : List VarId} (v : VarId)
    {rhs body xArg : Expr} {t_rhs t_body t_xArg : Term}
    (hfresh : (Moist.MIR.freeVars xArg).contains v = false)
    (h_rhs : lowerTotalExpr env rhs = some t_rhs)
    (h_body : lowerTotalExpr (v :: env) body = some t_body)
    (h_xArg : lowerTotalExpr env xArg = some t_xArg) :
    lowerTotalExpr env (.Let [(v, rhs, false)] (.App body xArg)) =
      some (.Apply (.Lam 0 (.Apply t_body
        (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_xArg))) t_rhs) := by
  have h_rhs' : lowerTotal env (Moist.MIR.expandFix rhs) = some t_rhs := h_rhs
  have h_body' : lowerTotal (v :: env) (Moist.MIR.expandFix body) = some t_body := h_body
  have h_xArg' : lowerTotal env (Moist.MIR.expandFix xArg) = some t_xArg := h_xArg
  -- Use lowerTotal_prepend_unused to relate lowerTotal (v :: env) xArg to shifted t_xArg.
  have hfresh_exp : (Moist.MIR.freeVars (Moist.MIR.expandFix xArg)).contains v = false :=
    Moist.MIR.expandFix_freeVars_not_contains xArg v hfresh
  have h_xArg_shift :
      lowerTotal (v :: env) (Moist.MIR.expandFix xArg) =
        some (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_xArg) :=
    Moist.MIR.lowerTotal_prepend_unused env v _ hfresh_exp t_xArg h_xArg'
  show lowerTotal env (Moist.MIR.expandFix (.Let [(v, rhs, false)] (.App body xArg))) =
    some (.Apply (.Lam 0 (.Apply t_body
      (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_xArg))) t_rhs)
  simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
             Moist.MIR.lowerTotalLet, Option.bind_eq_bind, Option.bind_some,
             h_rhs', h_body', h_xArg_shift]

private theorem lowerTotalExpr_app_let_isSome (env : List VarId) (v : VarId)
    (rhs body xArg : Expr) :
    (lowerTotalExpr env (.App (.Let [(v, rhs, false)] body) xArg)).isSome ↔
      (lowerTotalExpr env rhs).isSome ∧
      (lowerTotalExpr (v :: env) body).isSome ∧
      (lowerTotalExpr env xArg).isSome := by
  constructor
  · intro hsome
    have h : (lowerTotal env (Moist.MIR.expandFix
        (.App (.Let [(v, rhs, false)] body) xArg))).isSome := hsome
    simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
               Moist.MIR.lowerTotalLet, Option.bind_eq_bind] at h
    cases hr : lowerTotal env (Moist.MIR.expandFix rhs) with
    | none => rw [hr] at h; simp at h
    | some t_r =>
      rw [hr] at h
      simp only [Option.bind_some] at h
      cases hb : lowerTotal (v :: env) (Moist.MIR.expandFix body) with
      | none => rw [hb] at h; simp at h
      | some t_b =>
        rw [hb] at h
        simp only [Option.bind_some] at h
        cases hx : lowerTotal env (Moist.MIR.expandFix xArg) with
        | none => rw [hx] at h; simp at h
        | some t_x =>
          have hr' : lowerTotalExpr env rhs = some t_r := hr
          have hb' : lowerTotalExpr (v :: env) body = some t_b := hb
          have hx' : lowerTotalExpr env xArg = some t_x := hx
          exact ⟨by rw [hr']; rfl, by rw [hb']; rfl, by rw [hx']; rfl⟩
  · rintro ⟨hr, hb, hx⟩
    cases hr' : lowerTotalExpr env rhs with
    | none => rw [hr'] at hr; exact absurd hr (by simp)
    | some t_r =>
      cases hb' : lowerTotalExpr (v :: env) body with
      | none => rw [hb'] at hb; exact absurd hb (by simp)
      | some t_b =>
        cases hx' : lowerTotalExpr env xArg with
        | none => rw [hx'] at hx; exact absurd hx (by simp)
        | some t_x =>
          rw [lowerTotalExpr_app_let v hr' hb' hx']
          rfl

private theorem lowerTotalExpr_let_app_isSome (env : List VarId) (v : VarId)
    (rhs body xArg : Expr) (hfresh : (Moist.MIR.freeVars xArg).contains v = false) :
    (lowerTotalExpr env (.Let [(v, rhs, false)] (.App body xArg))).isSome ↔
      (lowerTotalExpr env rhs).isSome ∧
      (lowerTotalExpr (v :: env) body).isSome ∧
      (lowerTotalExpr env xArg).isSome := by
  have hfresh_exp : (Moist.MIR.freeVars (Moist.MIR.expandFix xArg)).contains v = false :=
    Moist.MIR.expandFix_freeVars_not_contains xArg v hfresh
  constructor
  · intro hsome
    have h : (lowerTotal env (Moist.MIR.expandFix
        (.Let [(v, rhs, false)] (.App body xArg)))).isSome := hsome
    simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
               Moist.MIR.lowerTotalLet, Option.bind_eq_bind] at h
    cases hr : lowerTotal env (Moist.MIR.expandFix rhs) with
    | none => rw [hr] at h; simp at h
    | some t_r =>
      rw [hr] at h
      simp only [Option.bind_some] at h
      cases hb : lowerTotal (v :: env) (Moist.MIR.expandFix body) with
      | none => rw [hb] at h; simp at h
      | some t_b =>
        rw [hb] at h
        simp only [Option.bind_some] at h
        cases hx_ext : lowerTotal (v :: env) (Moist.MIR.expandFix xArg) with
        | none => rw [hx_ext] at h; simp at h
        | some t_x_ext =>
          -- Use prepend_unused to go from extended to non-extended (reverse via none case)
          cases hx : lowerTotal env (Moist.MIR.expandFix xArg) with
          | none =>
            -- If extended succeeds but base fails, that's a contradiction via the none version
            have := Moist.MIR.lowerTotal_prepend_unused_none env v _ hfresh_exp hx
            rw [hx_ext] at this; exact absurd this (by simp)
          | some t_x =>
            have hr' : lowerTotalExpr env rhs = some t_r := hr
            have hb' : lowerTotalExpr (v :: env) body = some t_b := hb
            have hx' : lowerTotalExpr env xArg = some t_x := hx
            exact ⟨by rw [hr']; rfl, by rw [hb']; rfl, by rw [hx']; rfl⟩
  · rintro ⟨hr, hb, hx⟩
    cases hr' : lowerTotalExpr env rhs with
    | none => rw [hr'] at hr; exact absurd hr (by simp)
    | some t_r =>
      cases hb' : lowerTotalExpr (v :: env) body with
      | none => rw [hb'] at hb; exact absurd hb (by simp)
      | some t_b =>
        cases hx' : lowerTotalExpr env xArg with
        | none => rw [hx'] at hx; exact absurd hx (by simp)
        | some t_x =>
          rw [lowerTotalExpr_let_app v hfresh hr' hb' hx']
          rfl

theorem mirRefines_let_hoist_app_left_fwd (v : VarId) (rhs body xArg : Expr)
    (hfresh : (Moist.MIR.freeVars xArg).contains v = false) :
    MIRRefines (.App (.Let [(v, rhs, false)] body) xArg)
               (.Let [(v, rhs, false)] (.App body xArg)) := by
  refine ⟨?_, ?_⟩
  · intro env hsome
    have h := (lowerTotalExpr_app_let_isSome env v rhs body xArg).mp hsome
    exact (lowerTotalExpr_let_app_isSome env v rhs body xArg hfresh).mpr h
  · intro d k env hlen
    cases hr : lowerTotalExpr env rhs with
    | none =>
      have h_lhs : lowerTotalExpr env (.App (.Let [(v, rhs, false)] body) xArg) = none := by
        cases h : lowerTotalExpr env (.App (.Let [(v, rhs, false)] body) xArg) with
        | none => rfl
        | some _ =>
          have hsome : (lowerTotalExpr env (.App (.Let [(v, rhs, false)] body) xArg)).isSome := by
            rw [h]; rfl
          have := (lowerTotalExpr_app_let_isSome env v rhs body xArg).mp hsome
          rw [hr] at this; exact absurd this.1 (by simp)
      rw [h_lhs]; trivial
    | some t_r =>
      cases hb : lowerTotalExpr (v :: env) body with
      | none =>
        have h_lhs : lowerTotalExpr env (.App (.Let [(v, rhs, false)] body) xArg) = none := by
          cases h : lowerTotalExpr env (.App (.Let [(v, rhs, false)] body) xArg) with
          | none => rfl
          | some _ =>
            have hsome : (lowerTotalExpr env (.App (.Let [(v, rhs, false)] body) xArg)).isSome := by
              rw [h]; rfl
            have := (lowerTotalExpr_app_let_isSome env v rhs body xArg).mp hsome
            rw [hb] at this; exact absurd this.2.1 (by simp)
        rw [h_lhs]; trivial
      | some t_b =>
        cases hx : lowerTotalExpr env xArg with
        | none =>
          have h_lhs : lowerTotalExpr env (.App (.Let [(v, rhs, false)] body) xArg) = none := by
            cases h : lowerTotalExpr env (.App (.Let [(v, rhs, false)] body) xArg) with
            | none => rfl
            | some _ =>
              have hsome : (lowerTotalExpr env (.App (.Let [(v, rhs, false)] body) xArg)).isSome := by
                rw [h]; rfl
              have := (lowerTotalExpr_app_let_isSome env v rhs body xArg).mp hsome
              rw [hx] at this; exact absurd this.2.2 (by simp)
          rw [h_lhs]; trivial
        | some t_x =>
          rw [lowerTotalExpr_app_let v hr hb hx, lowerTotalExpr_let_app v hfresh hr hb hx]
          simp only
          intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
          -- LHS state: compute π₁ ρ₁ (.Apply (.Apply (.Lam 0 t_b) t_r) t_x)
          -- 4 admin steps → compute (funV (VLam t_b ρ₁) :: arg t_x ρ₁ :: π₁) ρ₁ t_r
          have h_steps_lhs :
              steps 4 (State.compute π₁ ρ₁ (.Apply (.Apply (.Lam 0 t_b) t_r) t_x)) =
                State.compute (.funV (.VLam t_b ρ₁) :: .arg t_x ρ₁ :: π₁) ρ₁ t_r := by rfl
          -- RHS state: compute π₂ ρ₂ (.Apply (.Lam 0 (.Apply t_b shifted)) t_r)
          -- 3 admin steps → compute (funV (VLam (.Apply t_b shifted) ρ₂) :: π₂) ρ₂ t_r
          have h_steps_rhs :
              steps 3 (State.compute π₂ ρ₂ (.Apply (.Lam 0 (.Apply t_b
                (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_x))) t_r)) =
                State.compute (.funV (.VLam (.Apply t_b
                  (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_x)) ρ₂) :: π₂)
                  ρ₂ t_r := by rfl
          apply obsRefinesK_of_steps_left h_steps_lhs
          apply obsRefinesK_of_steps_right h_steps_rhs
          have hclosed_r : closedAt env.length t_r :=
            Moist.Verified.MIR.lowerTotal_closedAt env _ t_r hr
          have hclosed_b : closedAt (env.length + 1) t_b := by
            have := Moist.Verified.MIR.lowerTotal_closedAt (v :: env) _ t_b hb
            simpa [List.length_cons] using this
          have hclosed_x : closedAt env.length t_x :=
            Moist.Verified.MIR.lowerTotal_closedAt env _ t_x hx
          have hd_eq : d = env.length := hlen.symm
          subst hd_eq
          have henv_j : EnvRefinesK j env.length ρ₁ ρ₂ := by
            intro n hn hnd
            obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv n hn hnd
            exact ⟨w₁, w₂, hl, hr', hw⟩
          have henv_i : EnvRefinesK i env.length ρ₁ ρ₂ := by
            intro n hn hnd
            obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv_j n hn hnd
            exact ⟨w₁, w₂, hl, hr', valueRefinesK_mono hi _ _ hw⟩
          have hπ_aug : StackRefK ValueRefinesK i
              (.funV (.VLam t_b ρ₁) :: .arg t_x ρ₁ :: π₁)
              (.funV (.VLam (.Apply t_b
                (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_x)) ρ₂) :: π₂) :=
            stackRefK_letHoistAppLeft_fwd hclosed_b hclosed_x henv_i hπ
          exact ftlr env.length t_r hclosed_r j j (Nat.le_refl _) ρ₁ ρ₂ henv_j i hi
            _ _ hπ_aug

theorem mirRefines_let_hoist_app_left_bwd (v : VarId) (rhs body xArg : Expr)
    (hfresh : (Moist.MIR.freeVars xArg).contains v = false) :
    MIRRefines (.Let [(v, rhs, false)] (.App body xArg))
               (.App (.Let [(v, rhs, false)] body) xArg) := by
  refine ⟨?_, ?_⟩
  · intro env hsome
    have h := (lowerTotalExpr_let_app_isSome env v rhs body xArg hfresh).mp hsome
    exact (lowerTotalExpr_app_let_isSome env v rhs body xArg).mpr h
  · intro d k env hlen
    cases hr : lowerTotalExpr env rhs with
    | none =>
      have h_lhs : lowerTotalExpr env (.Let [(v, rhs, false)] (.App body xArg)) = none := by
        cases h : lowerTotalExpr env (.Let [(v, rhs, false)] (.App body xArg)) with
        | none => rfl
        | some _ =>
          have hsome : (lowerTotalExpr env (.Let [(v, rhs, false)] (.App body xArg))).isSome := by
            rw [h]; rfl
          have := (lowerTotalExpr_let_app_isSome env v rhs body xArg hfresh).mp hsome
          rw [hr] at this; exact absurd this.1 (by simp)
      rw [h_lhs]; trivial
    | some t_r =>
      cases hb : lowerTotalExpr (v :: env) body with
      | none =>
        have h_lhs : lowerTotalExpr env (.Let [(v, rhs, false)] (.App body xArg)) = none := by
          cases h : lowerTotalExpr env (.Let [(v, rhs, false)] (.App body xArg)) with
          | none => rfl
          | some _ =>
            have hsome : (lowerTotalExpr env (.Let [(v, rhs, false)] (.App body xArg))).isSome := by
              rw [h]; rfl
            have := (lowerTotalExpr_let_app_isSome env v rhs body xArg hfresh).mp hsome
            rw [hb] at this; exact absurd this.2.1 (by simp)
        rw [h_lhs]; trivial
      | some t_b =>
        cases hx : lowerTotalExpr env xArg with
        | none =>
          have h_lhs : lowerTotalExpr env (.Let [(v, rhs, false)] (.App body xArg)) = none := by
            cases h : lowerTotalExpr env (.Let [(v, rhs, false)] (.App body xArg)) with
            | none => rfl
            | some _ =>
              have hsome : (lowerTotalExpr env (.Let [(v, rhs, false)] (.App body xArg))).isSome := by
                rw [h]; rfl
              have := (lowerTotalExpr_let_app_isSome env v rhs body xArg hfresh).mp hsome
              rw [hx] at this; exact absurd this.2.2 (by simp)
          rw [h_lhs]; trivial
        | some t_x =>
          rw [lowerTotalExpr_let_app v hfresh hr hb hx, lowerTotalExpr_app_let v hr hb hx]
          simp only
          intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
          have h_steps_lhs :
              steps 3 (State.compute π₁ ρ₁ (.Apply (.Lam 0 (.Apply t_b
                (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_x))) t_r)) =
                State.compute (.funV (.VLam (.Apply t_b
                  (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_x)) ρ₁) :: π₁)
                  ρ₁ t_r := by rfl
          have h_steps_rhs :
              steps 4 (State.compute π₂ ρ₂ (.Apply (.Apply (.Lam 0 t_b) t_r) t_x)) =
                State.compute (.funV (.VLam t_b ρ₂) :: .arg t_x ρ₂ :: π₂) ρ₂ t_r := by rfl
          apply obsRefinesK_of_steps_left h_steps_lhs
          apply obsRefinesK_of_steps_right h_steps_rhs
          have hclosed_r : closedAt env.length t_r :=
            Moist.Verified.MIR.lowerTotal_closedAt env _ t_r hr
          have hclosed_b : closedAt (env.length + 1) t_b := by
            have := Moist.Verified.MIR.lowerTotal_closedAt (v :: env) _ t_b hb
            simpa [List.length_cons] using this
          have hclosed_x : closedAt env.length t_x :=
            Moist.Verified.MIR.lowerTotal_closedAt env _ t_x hx
          have hd_eq : d = env.length := hlen.symm
          subst hd_eq
          have henv_j : EnvRefinesK j env.length ρ₁ ρ₂ := by
            intro n hn hnd
            obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv n hn hnd
            exact ⟨w₁, w₂, hl, hr', hw⟩
          have henv_i : EnvRefinesK i env.length ρ₁ ρ₂ := by
            intro n hn hnd
            obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv_j n hn hnd
            exact ⟨w₁, w₂, hl, hr', valueRefinesK_mono hi _ _ hw⟩
          have hπ_aug : StackRefK ValueRefinesK i
              (.funV (.VLam (.Apply t_b
                (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_x)) ρ₁) :: π₁)
              (.funV (.VLam t_b ρ₂) :: .arg t_x ρ₂ :: π₂) :=
            stackRefK_letHoistAppLeft_bwd hclosed_b hclosed_x henv_i hπ
          exact ftlr env.length t_r hclosed_r j j (Nat.le_refl _) ρ₁ ρ₂ henv_j i hi
            _ _ hπ_aug

private theorem let_hoist_app_left_close_pres_fwd (v : VarId) (rhs body xArg : Expr)
    (hfresh : (Moist.MIR.freeVars xArg).contains v = false) :
    ∀ env k t₁ t₂,
      lowerTotalExpr env (.App (.Let [(v, rhs, false)] body) xArg) = some t₁ →
      lowerTotalExpr env (.Let [(v, rhs, false)] (.App body xArg)) = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true := by
  intro env k t₁ t₂ h₁ h₂ hc
  have hsome₁ : (lowerTotalExpr env (.App (.Let [(v, rhs, false)] body) xArg)).isSome := by
    rw [h₁]; exact rfl
  obtain ⟨hr_some, hb_some, hx_some⟩ :=
    (lowerTotalExpr_app_let_isSome env v rhs body xArg).mp hsome₁
  cases hr : lowerTotalExpr env rhs with
  | none => rw [hr] at hr_some; exact absurd hr_some (by simp)
  | some t_r =>
    cases hb : lowerTotalExpr (v :: env) body with
    | none => rw [hb] at hb_some; exact absurd hb_some (by simp)
    | some t_b =>
      cases hx : lowerTotalExpr env xArg with
      | none => rw [hx] at hx_some; exact absurd hx_some (by simp)
      | some t_x =>
        rw [lowerTotalExpr_app_let v hr hb hx] at h₁
        rw [lowerTotalExpr_let_app v hfresh hr hb hx] at h₂
        injection h₁ with h₁; subst h₁
        injection h₂ with h₂; subst h₂
        -- LHS closedAt: closedAt k (.Apply (.Apply (.Lam 0 t_b) t_r) t_x)
        --             = (closedAt (k+1) t_b ∧ closedAt k t_r) ∧ closedAt k t_x
        -- RHS closedAt: closedAt k (.Apply (.Lam 0 (.Apply t_b shifted_x)) t_r)
        --             = (closedAt (k+1) t_b ∧ closedAt (k+1) shifted_x) ∧ closedAt k t_r
        simp only [closedAt, Bool.and_eq_true] at hc ⊢
        obtain ⟨⟨hb_c, hr_c⟩, hx_c⟩ := hc
        refine ⟨⟨hb_c, ?_⟩, hr_c⟩
        -- Need: closedAt (k+1) (renameTerm (shiftRename 1) t_x) given closedAt k t_x
        -- For the case k = 0: closedAt 0 t_x means t_x is closed (no free variables),
        -- so the shifted version is closed at 1, which is closedAt (0+1).
        by_cases hk : k = 0
        · subst hk
          -- closedAt 0 t_x → closedAt 1 (shifted t_x)
          have h1 : closedAt 1 (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_x) :=
            closedAt_renameTerm_shiftRename t_x 0 1 (by omega) (by omega) hx_c
          exact h1
        · have hkp : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk
          exact closedAt_renameTerm_shiftRename t_x k 1 (by omega) (by omega) hx_c

private theorem let_hoist_app_left_close_pres_bwd (v : VarId) (rhs body xArg : Expr)
    (hfresh : (Moist.MIR.freeVars xArg).contains v = false) :
    ∀ env k t₁ t₂,
      lowerTotalExpr env (.Let [(v, rhs, false)] (.App body xArg)) = some t₁ →
      lowerTotalExpr env (.App (.Let [(v, rhs, false)] body) xArg) = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true := by
  intro env k t₁ t₂ h₁ h₂ hc
  have hsome₁ : (lowerTotalExpr env (.Let [(v, rhs, false)] (.App body xArg))).isSome := by
    rw [h₁]; exact rfl
  obtain ⟨hr_some, hb_some, hx_some⟩ :=
    (lowerTotalExpr_let_app_isSome env v rhs body xArg hfresh).mp hsome₁
  cases hr : lowerTotalExpr env rhs with
  | none => rw [hr] at hr_some; exact absurd hr_some (by simp)
  | some t_r =>
    cases hb : lowerTotalExpr (v :: env) body with
    | none => rw [hb] at hb_some; exact absurd hb_some (by simp)
    | some t_b =>
      cases hx : lowerTotalExpr env xArg with
      | none => rw [hx] at hx_some; exact absurd hx_some (by simp)
      | some t_x =>
        rw [lowerTotalExpr_let_app v hfresh hr hb hx] at h₁
        rw [lowerTotalExpr_app_let v hr hb hx] at h₂
        injection h₁ with h₁; subst h₁
        injection h₂ with h₂; subst h₂
        simp only [closedAt, Bool.and_eq_true] at hc ⊢
        obtain ⟨⟨hb_c, hsh_c⟩, hr_c⟩ := hc
        have hx_c : closedAt k t_x = true := by
          by_cases hk : k = 0
          · subst hk
            exact closedAt_renameTerm_shiftRename_inv t_x 0 1 (by omega) (by omega) hsh_c
          · have hkp : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk
            exact closedAt_renameTerm_shiftRename_inv t_x k 1 (by omega) (by omega) hsh_c
        exact ⟨⟨hb_c, hr_c⟩, hx_c⟩

theorem mirCtxRefines_let_hoist_app_left_fwd (v : VarId) (rhs body xArg : Expr)
    (hfresh : (Moist.MIR.freeVars xArg).contains v = false) :
    MIRCtxRefines (.App (.Let [(v, rhs, false)] body) xArg)
                  (.Let [(v, rhs, false)] (.App body xArg)) :=
  mirRefines_to_mirCtxRefines (mirRefines_let_hoist_app_left_fwd v rhs body xArg hfresh)
    (let_hoist_app_left_close_pres_fwd v rhs body xArg hfresh)

theorem mirCtxRefines_let_hoist_app_left_bwd (v : VarId) (rhs body xArg : Expr)
    (hfresh : (Moist.MIR.freeVars xArg).contains v = false) :
    MIRCtxRefines (.Let [(v, rhs, false)] (.App body xArg))
                  (.App (.Let [(v, rhs, false)] body) xArg) :=
  mirRefines_to_mirCtxRefines (mirRefines_let_hoist_app_left_bwd v rhs body xArg hfresh)
    (let_hoist_app_left_close_pres_bwd v rhs body xArg hfresh)

/-! ## Section 7. Let-hoist-app-right-atom primitive

`.App g (.Let [(v, rhs, false)] body) ≈ .Let [(v, rhs, false)] (.App g body)`
when `g.isAtom = true ∧ v ∉ freeVars g`. -/

/-- For an atom term `t_g` (a leaf: `.Var n` with `n ≥ 1`, `.Constant`, or
    `.Builtin`), computing `t_g` in any non-empty stack/env takes a single
    CEK step and always succeeds when `closedAt d t_g` holds under a
    related env pair. The Var-case constraint `n ≥ 1` encodes the fact
    that lowered MIR atoms never produce `.Var 0` (the `+1` shift in the
    Var lowering). -/
private def isLeafAtomTerm (t : Term) : Prop :=
  (∃ n, n ≥ 1 ∧ t = .Var n) ∨ (∃ ct, t = .Constant ct) ∨ (∃ b, t = .Builtin b)

/-- For atom MIR expressions, the lowering produces a leaf term. -/
private theorem lowerTotal_atom_isLeafAtom :
    ∀ (env : List VarId) (g : Expr) (t_g : Term),
      g.isAtom = true →
      Moist.MIR.lowerTotal env (Moist.MIR.expandFix g) = some t_g →
      isLeafAtomTerm t_g := by
  intro env g t_g hatom hlow
  cases g with
  | Var x =>
    simp only [Moist.MIR.expandFix, Moist.MIR.lowerTotal] at hlow
    cases h : Moist.MIR.envLookupT env x with
    | none => rw [h] at hlow; simp at hlow
    | some idx =>
      rw [h] at hlow; simp at hlow; subst hlow
      exact .inl ⟨idx + 1, Nat.succ_le_succ (Nat.zero_le _), rfl⟩
  | Lit p =>
    obtain ⟨c, ty⟩ := p
    simp only [Moist.MIR.expandFix, Moist.MIR.lowerTotal] at hlow
    injection hlow with hlow; subst hlow
    exact .inr (.inl ⟨(c, ty), rfl⟩)
  | Builtin b =>
    simp only [Moist.MIR.expandFix, Moist.MIR.lowerTotal] at hlow
    injection hlow with hlow; subst hlow
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
  have h_g' : lowerTotal env (Moist.MIR.expandFix g) = some t_g := h_g
  have h_rhs' : lowerTotal env (Moist.MIR.expandFix rhs) = some t_rhs := h_rhs
  have h_body' : lowerTotal (v :: env) (Moist.MIR.expandFix body) = some t_body := h_body
  show lowerTotal env (Moist.MIR.expandFix (.App g (.Let [(v, rhs, false)] body))) =
    some (.Apply t_g (.Apply (.Lam 0 t_body) t_rhs))
  simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
             Moist.MIR.lowerTotalLet, Option.bind_eq_bind, Option.bind_some,
             h_g', h_rhs', h_body']

/-- Lowering shape for `Let v=rhs (App g body)` using the shifted form of `g`. -/
private theorem lowerTotalExpr_let_app_g {env : List VarId} (v : VarId)
    {g rhs body : Expr} {t_g t_rhs t_body : Term}
    (hfresh : (Moist.MIR.freeVars g).contains v = false)
    (h_g : lowerTotalExpr env g = some t_g)
    (h_rhs : lowerTotalExpr env rhs = some t_rhs)
    (h_body : lowerTotalExpr (v :: env) body = some t_body) :
    lowerTotalExpr env (.Let [(v, rhs, false)] (.App g body)) =
      some (.Apply (.Lam 0 (.Apply
        (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_g) t_body)) t_rhs) := by
  have h_g' : lowerTotal env (Moist.MIR.expandFix g) = some t_g := h_g
  have h_rhs' : lowerTotal env (Moist.MIR.expandFix rhs) = some t_rhs := h_rhs
  have h_body' : lowerTotal (v :: env) (Moist.MIR.expandFix body) = some t_body := h_body
  have hfresh_exp : (Moist.MIR.freeVars (Moist.MIR.expandFix g)).contains v = false :=
    Moist.MIR.expandFix_freeVars_not_contains g v hfresh
  have h_g_shift :
      lowerTotal (v :: env) (Moist.MIR.expandFix g) =
        some (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_g) :=
    Moist.MIR.lowerTotal_prepend_unused env v _ hfresh_exp t_g h_g'
  show lowerTotal env (Moist.MIR.expandFix (.Let [(v, rhs, false)] (.App g body))) =
    some (.Apply (.Lam 0 (.Apply
      (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_g) t_body)) t_rhs)
  simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
             Moist.MIR.lowerTotalLet, Option.bind_eq_bind, Option.bind_some,
             h_g_shift, h_rhs', h_body']

private theorem lowerTotalExpr_app_g_let_isSome (env : List VarId) (v : VarId)
    (g rhs body : Expr) :
    (lowerTotalExpr env (.App g (.Let [(v, rhs, false)] body))).isSome ↔
      (lowerTotalExpr env g).isSome ∧ (lowerTotalExpr env rhs).isSome ∧
      (lowerTotalExpr (v :: env) body).isSome := by
  constructor
  · intro hsome
    have h : (lowerTotal env (Moist.MIR.expandFix
        (.App g (.Let [(v, rhs, false)] body)))).isSome := hsome
    simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
               Moist.MIR.lowerTotalLet, Option.bind_eq_bind] at h
    cases hg : lowerTotal env (Moist.MIR.expandFix g) with
    | none => rw [hg] at h; simp at h
    | some t_g =>
      rw [hg] at h
      simp only [Option.bind_some] at h
      cases hr : lowerTotal env (Moist.MIR.expandFix rhs) with
      | none => rw [hr] at h; simp at h
      | some t_r =>
        rw [hr] at h
        simp only [Option.bind_some] at h
        cases hb : lowerTotal (v :: env) (Moist.MIR.expandFix body) with
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
    (g rhs body : Expr) (hfresh : (Moist.MIR.freeVars g).contains v = false) :
    (lowerTotalExpr env (.Let [(v, rhs, false)] (.App g body))).isSome ↔
      (lowerTotalExpr env g).isSome ∧ (lowerTotalExpr env rhs).isSome ∧
      (lowerTotalExpr (v :: env) body).isSome := by
  have hfresh_exp : (Moist.MIR.freeVars (Moist.MIR.expandFix g)).contains v = false :=
    Moist.MIR.expandFix_freeVars_not_contains g v hfresh
  constructor
  · intro hsome
    have h : (lowerTotal env (Moist.MIR.expandFix
        (.Let [(v, rhs, false)] (.App g body)))).isSome := hsome
    simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
               Moist.MIR.lowerTotalLet, Option.bind_eq_bind] at h
    cases hr : lowerTotal env (Moist.MIR.expandFix rhs) with
    | none => rw [hr] at h; simp at h
    | some t_r =>
      rw [hr] at h
      simp only [Option.bind_some] at h
      cases hg_ext : lowerTotal (v :: env) (Moist.MIR.expandFix g) with
      | none => rw [hg_ext] at h; simp at h
      | some t_g_ext =>
        rw [hg_ext] at h
        simp only [Option.bind_some] at h
        cases hb : lowerTotal (v :: env) (Moist.MIR.expandFix body) with
        | none => rw [hb] at h; simp at h
        | some t_b =>
          cases hg : lowerTotal env (Moist.MIR.expandFix g) with
          | none =>
            have := Moist.MIR.lowerTotal_prepend_unused_none env v _ hfresh_exp hg
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
private theorem leafAtomValues {t_g : Term} (h : isLeafAtomTerm t_g)
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
private theorem leafAtom_shift_step {t_g : Term} (h : isLeafAtomTerm t_g)
    {d : Nat} (hclosed : closedAt d t_g = true) :
    ∀ {ρ : CekEnv} (v_inner : CekValue) (w : CekValue),
      Moist.CEK.step (.compute [] ρ t_g) = .ret [] w →
      ∀ π, Moist.CEK.step (.compute π (ρ.extend v_inner)
        (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_g)) = .ret π w := by
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
    have hsr : Moist.Verified.shiftRename 1 n = n + 1 := by
      simp [Moist.Verified.shiftRename]; omega
    have hlook : (ρ.extend v_inner).lookup (n + 1) = ρ.lookup n := by
      show (CekEnv.cons v_inner ρ).lookup (n + 1) = ρ.lookup n
      match n, hn1 with
      | k + 1, _ => rfl
    show (match (ρ.extend v_inner).lookup (Moist.Verified.shiftRename 1 n) with
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

/-- **MIRRefines for let-hoist-app-right-atom (forward)**:
    `.App g (.Let [(v, rhs, false)] body) ⊑ᴹ .Let [(v, rhs, false)] (.App g body)`
    when `g` is an atom and `v ∉ freeVars g`. -/
theorem mirRefines_let_hoist_app_right_atom_fwd (v : VarId) (rhs body g : Expr)
    (hgatom : g.isAtom = true)
    (hfresh : (Moist.MIR.freeVars g).contains v = false) :
    MIRRefines (.App g (.Let [(v, rhs, false)] body))
               (.Let [(v, rhs, false)] (.App g body)) := by
  refine ⟨?_, ?_⟩
  · intro env hsome
    have h := (lowerTotalExpr_app_g_let_isSome env v g rhs body).mp hsome
    exact (lowerTotalExpr_let_app_g_isSome env v g rhs body hfresh).mpr h
  · intro d k env hlen
    cases hg : lowerTotalExpr env g with
    | none =>
      have h_lhs : lowerTotalExpr env (.App g (.Let [(v, rhs, false)] body)) = none := by
        cases h : lowerTotalExpr env (.App g (.Let [(v, rhs, false)] body)) with
        | none => rfl
        | some _ =>
          have hsome : (lowerTotalExpr env (.App g (.Let [(v, rhs, false)] body))).isSome := by
            rw [h]; rfl
          have := (lowerTotalExpr_app_g_let_isSome env v g rhs body).mp hsome
          rw [hg] at this; exact absurd this.1 (by simp)
      rw [h_lhs]; trivial
    | some t_g =>
      cases hr : lowerTotalExpr env rhs with
      | none =>
        have h_lhs : lowerTotalExpr env (.App g (.Let [(v, rhs, false)] body)) = none := by
          cases h : lowerTotalExpr env (.App g (.Let [(v, rhs, false)] body)) with
          | none => rfl
          | some _ =>
            have hsome : (lowerTotalExpr env (.App g (.Let [(v, rhs, false)] body))).isSome := by
              rw [h]; rfl
            have := (lowerTotalExpr_app_g_let_isSome env v g rhs body).mp hsome
            rw [hr] at this; exact absurd this.2.1 (by simp)
        rw [h_lhs]; trivial
      | some t_r =>
        cases hb : lowerTotalExpr (v :: env) body with
        | none =>
          have h_lhs : lowerTotalExpr env (.App g (.Let [(v, rhs, false)] body)) = none := by
            cases h : lowerTotalExpr env (.App g (.Let [(v, rhs, false)] body)) with
            | none => rfl
            | some _ =>
              have hsome : (lowerTotalExpr env (.App g (.Let [(v, rhs, false)] body))).isSome := by
                rw [h]; rfl
              have := (lowerTotalExpr_app_g_let_isSome env v g rhs body).mp hsome
              rw [hb] at this; exact absurd this.2.2 (by simp)
          rw [h_lhs]; trivial
        | some t_b =>
          rw [lowerTotalExpr_app_g_let v hg hr hb,
              lowerTotalExpr_let_app_g v hfresh hg hr hb]
          simp only
          intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
          have hgatom_term : isLeafAtomTerm t_g :=
            lowerTotal_atom_isLeafAtom env g t_g hgatom hg
          have hclosed_g : closedAt env.length t_g :=
            Moist.Verified.MIR.lowerTotal_closedAt env _ t_g hg
          have hclosed_r : closedAt env.length t_r :=
            Moist.Verified.MIR.lowerTotal_closedAt env _ t_r hr
          have hclosed_b : closedAt (env.length + 1) t_b := by
            have := Moist.Verified.MIR.lowerTotal_closedAt (v :: env) _ t_b hb
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
                (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_g) t_b)) t_r)) =
                State.compute (.funV (.VLam (.Apply
                  (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_g) t_b) ρ₂) :: π₂)
                  ρ₂ t_r := by rfl
          apply obsRefinesK_of_steps_left h_steps_lhs
          apply obsRefinesK_of_steps_right h_steps_rhs
          have henv_j : EnvRefinesK j env.length ρ₁ ρ₂ := by
            intro n hn hnd
            obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv n hn hnd
            exact ⟨w₁, w₂, hl, hr', hw⟩
          have hπ_aug : StackRefK ValueRefinesK i
              (.funV (.VLam t_b ρ₁) :: .funV v_g₁ :: π₁)
              (.funV (.VLam (.Apply
                (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_g) t_b) ρ₂) :: π₂) := by
            intro j' hj' v₁' v₂' hv'
            have h_lhs_step :
                steps 1 (State.ret (.funV (.VLam t_b ρ₁) :: .funV v_g₁ :: π₁) v₁') =
                  State.compute (.funV v_g₁ :: π₁) (ρ₁.extend v₁') t_b := by rfl
            apply obsRefinesK_of_steps_left h_lhs_step
            have hshift_step :
                Moist.CEK.step (.compute (.arg t_b (ρ₂.extend v₂') :: π₂) (ρ₂.extend v₂')
                  (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_g)) =
                  .ret (.arg t_b (ρ₂.extend v₂') :: π₂) v_g₂ := by
              have hempty_step : Moist.CEK.step (.compute [] ρ₂ t_g) = .ret [] v_g₂ :=
                hstep_rhs_any []
              exact leafAtom_shift_step hgatom_term hclosed_g v₂' v_g₂
                hempty_step (.arg t_b (ρ₂.extend v₂') :: π₂)
            have h_rhs_step :
                steps 4 (State.ret (.funV (.VLam (.Apply
                  (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_g) t_b) ρ₂) :: π₂) v₂') =
                  State.compute (.funV v_g₂ :: π₂) (ρ₂.extend v₂') t_b := by
              show Moist.CEK.step (Moist.CEK.step (Moist.CEK.step (Moist.CEK.step
                (State.ret (.funV (.VLam (.Apply
                  (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_g) t_b) ρ₂) :: π₂) v₂')))) = _
              show Moist.CEK.step (Moist.CEK.step
                (State.compute (.arg t_b (ρ₂.extend v₂') :: π₂) (ρ₂.extend v₂')
                  (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_g))) = _
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
    (hfresh : (Moist.MIR.freeVars g).contains v = false) :
    MIRRefines (.Let [(v, rhs, false)] (.App g body))
               (.App g (.Let [(v, rhs, false)] body)) := by
  refine ⟨?_, ?_⟩
  · intro env hsome
    have h := (lowerTotalExpr_let_app_g_isSome env v g rhs body hfresh).mp hsome
    exact (lowerTotalExpr_app_g_let_isSome env v g rhs body).mpr h
  · intro d k env hlen
    cases hg : lowerTotalExpr env g with
    | none =>
      have h_lhs : lowerTotalExpr env (.Let [(v, rhs, false)] (.App g body)) = none := by
        cases h : lowerTotalExpr env (.Let [(v, rhs, false)] (.App g body)) with
        | none => rfl
        | some _ =>
          have hsome : (lowerTotalExpr env (.Let [(v, rhs, false)] (.App g body))).isSome := by
            rw [h]; rfl
          have := (lowerTotalExpr_let_app_g_isSome env v g rhs body hfresh).mp hsome
          rw [hg] at this; exact absurd this.1 (by simp)
      rw [h_lhs]; trivial
    | some t_g =>
      cases hr : lowerTotalExpr env rhs with
      | none =>
        have h_lhs : lowerTotalExpr env (.Let [(v, rhs, false)] (.App g body)) = none := by
          cases h : lowerTotalExpr env (.Let [(v, rhs, false)] (.App g body)) with
          | none => rfl
          | some _ =>
            have hsome : (lowerTotalExpr env (.Let [(v, rhs, false)] (.App g body))).isSome := by
              rw [h]; rfl
            have := (lowerTotalExpr_let_app_g_isSome env v g rhs body hfresh).mp hsome
            rw [hr] at this; exact absurd this.2.1 (by simp)
        rw [h_lhs]; trivial
      | some t_r =>
        cases hb : lowerTotalExpr (v :: env) body with
        | none =>
          have h_lhs : lowerTotalExpr env (.Let [(v, rhs, false)] (.App g body)) = none := by
            cases h : lowerTotalExpr env (.Let [(v, rhs, false)] (.App g body)) with
            | none => rfl
            | some _ =>
              have hsome : (lowerTotalExpr env (.Let [(v, rhs, false)] (.App g body))).isSome := by
                rw [h]; rfl
              have := (lowerTotalExpr_let_app_g_isSome env v g rhs body hfresh).mp hsome
              rw [hb] at this; exact absurd this.2.2 (by simp)
          rw [h_lhs]; trivial
        | some t_b =>
          rw [lowerTotalExpr_let_app_g v hfresh hg hr hb,
              lowerTotalExpr_app_g_let v hg hr hb]
          simp only
          intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
          have hgatom_term : isLeafAtomTerm t_g :=
            lowerTotal_atom_isLeafAtom env g t_g hgatom hg
          have hclosed_g : closedAt env.length t_g :=
            Moist.Verified.MIR.lowerTotal_closedAt env _ t_g hg
          have hclosed_r : closedAt env.length t_r :=
            Moist.Verified.MIR.lowerTotal_closedAt env _ t_r hr
          have hclosed_b : closedAt (env.length + 1) t_b := by
            have := Moist.Verified.MIR.lowerTotal_closedAt (v :: env) _ t_b hb
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
                (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_g) t_b)) t_r)) =
                State.compute (.funV (.VLam (.Apply
                  (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_g) t_b) ρ₁) :: π₁)
                  ρ₁ t_r := by rfl
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
                (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_g) t_b) ρ₁) :: π₁)
              (.funV (.VLam t_b ρ₂) :: .funV v_g₂ :: π₂) := by
            intro j' hj' v₁' v₂' hv'
            have hshift_step :
                Moist.CEK.step (.compute (.arg t_b (ρ₁.extend v₁') :: π₁) (ρ₁.extend v₁')
                  (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_g)) =
                  .ret (.arg t_b (ρ₁.extend v₁') :: π₁) v_g₁ := by
              have hempty_step : Moist.CEK.step (.compute [] ρ₁ t_g) = .ret [] v_g₁ :=
                hstep_lhs_any []
              exact leafAtom_shift_step hgatom_term hclosed_g v₁' v_g₁
                hempty_step (.arg t_b (ρ₁.extend v₁') :: π₁)
            have h_lhs_step :
                steps 4 (State.ret (.funV (.VLam (.Apply
                  (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_g) t_b) ρ₁) :: π₁) v₁') =
                  State.compute (.funV v_g₁ :: π₁) (ρ₁.extend v₁') t_b := by
              show Moist.CEK.step (Moist.CEK.step (Moist.CEK.step (Moist.CEK.step
                (State.ret (.funV (.VLam (.Apply
                  (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_g) t_b) ρ₁) :: π₁) v₁')))) = _
              show Moist.CEK.step (Moist.CEK.step
                (State.compute (.arg t_b (ρ₁.extend v₁') :: π₁) (ρ₁.extend v₁')
                  (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_g))) = _
              rw [hshift_step]
              rfl
            apply obsRefinesK_of_steps_left h_lhs_step
            have h_rhs_step :
                steps 1 (State.ret (.funV (.VLam t_b ρ₂) :: .funV v_g₂ :: π₂) v₂') =
                  State.compute (.funV v_g₂ :: π₂) (ρ₂.extend v₂') t_b := by rfl
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
    (hfresh : (Moist.MIR.freeVars g).contains v = false) :
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
        injection h₁ with h₁; subst h₁
        injection h₂ with h₂; subst h₂
        -- LHS closedAt: closedAt k (Apply t_g (Apply (Lam 0 t_b) t_r))
        --   = t_g_c ∧ (t_b_c(k+1) ∧ t_r_c)
        -- RHS closedAt: closedAt k (Apply (Lam 0 (Apply shifted_g t_b)) t_r)
        --   = ((shifted_g_c(k+1) ∧ t_b_c(k+1)) ∧ t_r_c)
        simp only [closedAt, Bool.and_eq_true] at hc ⊢
        obtain ⟨hg_c, ⟨hb_c, hr_c⟩⟩ := hc
        refine ⟨⟨?_, hb_c⟩, hr_c⟩
        by_cases hk : k = 0
        · subst hk
          exact closedAt_renameTerm_shiftRename t_g 0 1 (by omega) (by omega) hg_c
        · have hkp : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk
          exact closedAt_renameTerm_shiftRename t_g k 1 (by omega) (by omega) hg_c

/-- Closedness preservation for let-hoist-app-right-atom (backward). -/
private theorem let_hoist_app_right_atom_close_pres_bwd (v : VarId) (rhs body g : Expr)
    (hfresh : (Moist.MIR.freeVars g).contains v = false) :
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
        injection h₁ with h₁; subst h₁
        injection h₂ with h₂; subst h₂
        simp only [closedAt, Bool.and_eq_true] at hc ⊢
        obtain ⟨⟨hshg_c, hb_c⟩, hr_c⟩ := hc
        have hg_c : closedAt k t_g = true := by
          by_cases hk : k = 0
          · subst hk
            exact closedAt_renameTerm_shiftRename_inv t_g 0 1 (by omega) (by omega) hshg_c
          · have hkp : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk
            exact closedAt_renameTerm_shiftRename_inv t_g k 1 (by omega) (by omega) hshg_c
        exact ⟨hg_c, hb_c, hr_c⟩

theorem mirCtxRefines_let_hoist_app_right_atom_fwd (v : VarId) (rhs body g : Expr)
    (hgatom : g.isAtom = true)
    (hfresh : (Moist.MIR.freeVars g).contains v = false) :
    MIRCtxRefines (.App g (.Let [(v, rhs, false)] body))
                  (.Let [(v, rhs, false)] (.App g body)) :=
  mirRefines_to_mirCtxRefines
    (mirRefines_let_hoist_app_right_atom_fwd v rhs body g hgatom hfresh)
    (let_hoist_app_right_atom_close_pres_fwd v rhs body g hfresh)

theorem mirCtxRefines_let_hoist_app_right_atom_bwd (v : VarId) (rhs body g : Expr)
    (hgatom : g.isAtom = true)
    (hfresh : (Moist.MIR.freeVars g).contains v = false) :
    MIRCtxRefines (.Let [(v, rhs, false)] (.App g body))
                  (.App g (.Let [(v, rhs, false)] body)) :=
  mirRefines_to_mirCtxRefines
    (mirRefines_let_hoist_app_right_atom_bwd v rhs body g hgatom hfresh)
    (let_hoist_app_right_atom_close_pres_bwd v rhs body g hfresh)

/-! ## Section 8. Let-hoist-case-scrut primitive

`.Case (.Let [(v, rhs, false)] body) alts ≈ .Let [(v, rhs, false)] (.Case body alts)`
when no alt references `v`.

The lowerings:
* LHS lowers to `.Case (.Apply (.Lam 0 t_body) t_rhs) t_alts`.
* RHS lowers to `.Apply (.Lam 0 (.Case t_body (shift t_alts))) t_rhs`,
  where each alt has been shifted via `shiftRename 1` because the alts
  are now evaluated under an extra let binder.

The forward CEK trace:
* LHS: 4 admin steps produce
  `compute (funV (VLam t_body ρ₁) :: caseScrutinee t_alts ρ₁ :: π₁) ρ₁ t_rhs`.
* RHS: 3 admin steps produce
  `compute (funV (VLam (.Case t_body (shift t_alts)) ρ₂) :: π₂) ρ₂ t_rhs`.

Both sides now evaluate the same `t_rhs`, so `ftlr` bridges via an
augmented-stack helper. After the returned value fires the funV on both
sides, the LHS lands in a `.caseScrutinee` frame with the *unextended*
`ρ₁`, while the RHS evaluates `(.Case t_body (shift t_alts))` which
pushes a `.caseScrutinee` frame with the *extended* `ρ₂.extend v₂`.
`stackRefK_caseScrutinee_shift_aug_fwd` handles this asymmetry. -/

/-- Converts a `∀ alt ∈ alts, ...` freeness hypothesis into the
    list-level `freeVarsList` form. -/
private theorem freeVarsList_not_contains_of_forall (v : VarId) (alts : List Expr)
    (hfresh : ∀ alt ∈ alts, (Moist.MIR.freeVars alt).contains v = false) :
    (Moist.MIR.freeVarsList alts).contains v = false := by
  induction alts with
  | nil =>
    rw [Moist.MIR.freeVarsList.eq_1]
    exact Moist.MIR.VarSet.empty_not_contains v
  | cons a rest ih =>
    rw [Moist.MIR.freeVarsList.eq_2]
    apply Moist.MIR.VarSet.union_not_contains_fwd
    · exact hfresh a (List.mem_cons_self)
    · exact ih (fun alt halt => hfresh alt (List.mem_cons_of_mem _ halt))

/-- Stack-frame helper for the forward direction of let-hoist-case-scrut.
    The LHS has a `.caseScrutinee t_alts ρ₁` frame with the original env;
    the RHS has a `.caseScrutinee (shift t_alts) (ρ₂.extend v₂)` frame
    with the extended env. Both fire on a returned value by dispatching
    on its shape; `renameRefinesR (shiftRename 1)` bridges the alt
    evaluation. -/
private theorem stackRefK_caseScrutinee_shift_aug_fwd {i d : Nat}
    {t_alts : List Term} {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv} {v₂ : CekValue}
    (halts : Moist.Verified.closedAtList d t_alts = true)
    (henv : EnvRefinesK i d ρ₁ ρ₂)
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i
      (.caseScrutinee t_alts ρ₁ :: π₁)
      (.caseScrutinee (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_alts)
          (ρ₂.extend v₂) :: π₂) := by
  intro j hj w₁ w₂ hw
  match j with
  | 0 => exact obsRefinesK_zero_ret
  | n + 1 =>
    obsRefinesK_of_step_auto
    have halts_j : Moist.Verified.closedAtList d t_alts = true := halts
    have henv_j : EnvRefinesK (n + 1) d ρ₁ ρ₂ := by
      intro p hp hpd
      obtain ⟨w₁', w₂', hl, hr, hrel⟩ := henv p hp hpd
      exact ⟨w₁', w₂', hl, hr, valueRefinesK_mono hj _ _ hrel⟩
    match w₁, w₂ with
    | .VConstr tag₁ fields₁, .VConstr tag₂ fields₂ =>
      simp only [ValueRefinesK] at hw; obtain ⟨rfl, hfields_v⟩ := hw
      simp only [step]
      have hlen_eq : (Moist.Verified.renameTermList
          (Moist.Verified.shiftRename 1) t_alts).length = t_alts.length :=
        Moist.Verified.renameTermList_length _ _
      split
      · rename_i alt_val halt_case
        have hsome₁ := List.getElem?_eq_some_iff.mp halt_case
        have hi₁ : tag₁ < t_alts.length := hsome₁.1
        have hi₂ : tag₁ < (Moist.Verified.renameTermList
            (Moist.Verified.shiftRename 1) t_alts).length := by omega
        have halt₂ : (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_alts)[tag₁]? =
            some ((Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_alts)[tag₁]) :=
          List.getElem?_eq_some_iff.mpr ⟨hi₂, rfl⟩
        rw [halt₂]; simp only []
        have hidx : (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_alts)[tag₁]'hi₂
            = Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) (t_alts[tag₁]) :=
          Moist.Verified.renameTermList_getElem _ _ _ hi₁
        have halt_closed : closedAt d (t_alts[tag₁]) = true :=
          Moist.Verified.Contextual.BisimRef.closedAtList_get d t_alts _ _ halts_j
            (List.getElem?_eq_some_iff.mpr ⟨hi₁, rfl⟩)
        have henv_R : RenameEnvRefR (Moist.Verified.shiftRename 1) (n + 1) d
            ρ₁ (ρ₂.extend v₂) := envRefinesK_to_renameEnvRefR_shift henv_j
        have heq_alt : alt_val = t_alts[tag₁] := hsome₁.2.symm
        subst heq_alt
        rw [hidx]
        exact renameRefinesR_shift1 d (t_alts[tag₁]) halt_closed (n + 1) (n + 1)
          (Nat.le_refl _) ρ₁ (ρ₂.extend v₂) henv_R n (by omega)
          ((fields₁.map Frame.applyArg) ++ π₁)
          ((fields₂.map Frame.applyArg) ++ π₂)
          (applyArgFrames_stackRefK
            (listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) hfields_v)
            (stackRefK_mono (by omega) hπ))
      · rename_i hnone₁
        have hnone₂ : (Moist.Verified.renameTermList
            (Moist.Verified.shiftRename 1) t_alts)[tag₁]? = none := by
          rw [List.getElem?_eq_none_iff] at hnone₁ ⊢; omega
        rw [hnone₂]; simp only []; exact obsRefinesK_error _
    | .VCon c₁, .VCon c₂ =>
      simp only [ValueRefinesK] at hw; subst hw
      simp only [step]
      have hlen_eq : (Moist.Verified.renameTermList
          (Moist.Verified.shiftRename 1) t_alts).length = t_alts.length :=
        Moist.Verified.renameTermList_length _ _
      split
      · rename_i tag numCtors fields hconst
        have hif_eq : (decide (numCtors > 0) && decide (t_alts.length > numCtors)) =
            (decide (numCtors > 0) && decide ((Moist.Verified.renameTermList
              (Moist.Verified.shiftRename 1) t_alts).length > numCtors)) := by
          rw [hlen_eq]
        split
        · rename_i h_check
          rw [hif_eq] at h_check; simp [h_check]; exact obsRefinesK_error _
        · rename_i h_check
          rw [hif_eq] at h_check; simp [h_check]
          split
          · rename_i alt_val halt_case
            have hsome₁ := List.getElem?_eq_some_iff.mp halt_case
            have hi₁ : tag < t_alts.length := hsome₁.1
            have hi₂ : tag < (Moist.Verified.renameTermList
                (Moist.Verified.shiftRename 1) t_alts).length := by omega
            have halt₂ : (Moist.Verified.renameTermList
                (Moist.Verified.shiftRename 1) t_alts)[tag]? =
                some ((Moist.Verified.renameTermList
                  (Moist.Verified.shiftRename 1) t_alts)[tag]) :=
              List.getElem?_eq_some_iff.mpr ⟨hi₂, rfl⟩
            rw [halt₂]; simp only []
            have hidx : (Moist.Verified.renameTermList
                (Moist.Verified.shiftRename 1) t_alts)[tag]'hi₂ =
                Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) (t_alts[tag]) :=
              Moist.Verified.renameTermList_getElem _ _ _ hi₁
            have halt_closed : closedAt d (t_alts[tag]) = true :=
              Moist.Verified.Contextual.BisimRef.closedAtList_get d t_alts _ _ halts_j
                (List.getElem?_eq_some_iff.mpr ⟨hi₁, rfl⟩)
            have henv_R : RenameEnvRefR (Moist.Verified.shiftRename 1) (n + 1) d
                ρ₁ (ρ₂.extend v₂) := envRefinesK_to_renameEnvRefR_shift henv_j
            have heq_alt : alt_val = t_alts[tag] := hsome₁.2.symm
            subst heq_alt
            rw [hidx]
            have hfields_vcon :=
              Moist.Verified.Equivalence.constToTagAndFields_fields_vcon c₁
            rw [hconst] at hfields_vcon
            exact renameRefinesR_shift1 d (t_alts[tag]) halt_closed (n + 1) (n + 1)
              (Nat.le_refl _) ρ₁ (ρ₂.extend v₂) henv_R n (by omega)
              ((fields.map Frame.applyArg) ++ π₁)
              ((fields.map Frame.applyArg) ++ π₂)
              (applyArgFrames_stackRefK
                (Moist.Verified.Contextual.SoundnessRefines.listRel_refl_vcon_refines n
                  fields hfields_vcon)
                (stackRefK_mono (by omega) hπ))
          · rename_i hnone₁
            have hnone₂ : (Moist.Verified.renameTermList
                (Moist.Verified.shiftRename 1) t_alts)[tag]? = none := by
              rw [List.getElem?_eq_none_iff] at hnone₁ ⊢; omega
            rw [hnone₂]; simp only []; exact obsRefinesK_error _
      · exact obsRefinesK_error _
    | .VLam _ _, .VLam _ _ | .VDelay _ _, .VDelay _ _
    | .VBuiltin _ _ _, .VBuiltin _ _ _ => simp only [step]; exact obsRefinesK_error _
    | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
    | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
    | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
    | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
    | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
    | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
    | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
    | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
    | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at hw

/-- Backward version of `stackRefK_caseScrutinee_shift_aug_fwd`. LHS has the
    `extend`-ed env with shifted alts; RHS has the original env. -/
private theorem stackRefK_caseScrutinee_shift_aug_bwd {i d : Nat}
    {t_alts : List Term} {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv} {v₁ : CekValue}
    (halts : Moist.Verified.closedAtList d t_alts = true)
    (henv : EnvRefinesK i d ρ₁ ρ₂)
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i
      (.caseScrutinee (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_alts)
          (ρ₁.extend v₁) :: π₁)
      (.caseScrutinee t_alts ρ₂ :: π₂) := by
  intro j hj w₁ w₂ hw
  match j with
  | 0 => exact obsRefinesK_zero_ret
  | n + 1 =>
    obsRefinesK_of_step_auto
    have halts_j : Moist.Verified.closedAtList d t_alts = true := halts
    have henv_j : EnvRefinesK (n + 1) d ρ₁ ρ₂ := by
      intro p hp hpd
      obtain ⟨w₁', w₂', hl, hr, hrel⟩ := henv p hp hpd
      exact ⟨w₁', w₂', hl, hr, valueRefinesK_mono hj _ _ hrel⟩
    match w₁, w₂ with
    | .VConstr tag₁ fields₁, .VConstr tag₂ fields₂ =>
      simp only [ValueRefinesK] at hw; obtain ⟨rfl, hfields_v⟩ := hw
      simp only [step]
      have hlen_eq : (Moist.Verified.renameTermList
          (Moist.Verified.shiftRename 1) t_alts).length = t_alts.length :=
        Moist.Verified.renameTermList_length _ _
      split
      · rename_i alt_val halt_case
        have hsome₁ := List.getElem?_eq_some_iff.mp halt_case
        have hi₁s : tag₁ < (Moist.Verified.renameTermList
            (Moist.Verified.shiftRename 1) t_alts).length := hsome₁.1
        have hi₁ : tag₁ < t_alts.length := by omega
        have halt₂ : t_alts[tag₁]? = some (t_alts[tag₁]) :=
          List.getElem?_eq_some_iff.mpr ⟨hi₁, rfl⟩
        rw [halt₂]; simp only []
        have hidx : (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_alts)[tag₁]'hi₁s
            = Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) (t_alts[tag₁]) :=
          Moist.Verified.renameTermList_getElem _ _ _ hi₁
        have halt_closed : closedAt d (t_alts[tag₁]) = true :=
          Moist.Verified.Contextual.BisimRef.closedAtList_get d t_alts _ _ halts_j
            (List.getElem?_eq_some_iff.mpr ⟨hi₁, rfl⟩)
        have heq_alt : alt_val = (Moist.Verified.renameTermList
            (Moist.Verified.shiftRename 1) t_alts)[tag₁] := hsome₁.2.symm
        subst heq_alt
        rw [hidx]
        have henv_RL : Moist.Verified.FundamentalRefines.RenameEnvRef
            (Moist.Verified.shiftRename 1) (n + 1) d (ρ₁.extend v₁) ρ₂ :=
          Moist.Verified.FundamentalRefines.envRefinesK_to_renameEnvRef_shift henv_j
        exact Moist.Verified.FundamentalRefines.renameRefines_shift1 d (t_alts[tag₁]) halt_closed
          (n + 1) (n + 1) (Nat.le_refl _) (ρ₁.extend v₁) ρ₂ henv_RL n (by omega)
          ((fields₁.map Frame.applyArg) ++ π₁)
          ((fields₂.map Frame.applyArg) ++ π₂)
          (applyArgFrames_stackRefK
            (listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) hfields_v)
            (stackRefK_mono (by omega) hπ))
      · rename_i hnone₁
        have hnone₂ : t_alts[tag₁]? = none := by
          rw [List.getElem?_eq_none_iff] at hnone₁ ⊢; omega
        rw [hnone₂]; simp only []; exact obsRefinesK_error _
    | .VCon c₁, .VCon c₂ =>
      simp only [ValueRefinesK] at hw; subst hw
      simp only [step]
      have hlen_eq : (Moist.Verified.renameTermList
          (Moist.Verified.shiftRename 1) t_alts).length = t_alts.length :=
        Moist.Verified.renameTermList_length _ _
      split
      · rename_i tag numCtors fields hconst
        have hif_eq : (decide (numCtors > 0) && decide ((Moist.Verified.renameTermList
              (Moist.Verified.shiftRename 1) t_alts).length > numCtors)) =
            (decide (numCtors > 0) && decide (t_alts.length > numCtors)) := by
          rw [hlen_eq]
        split
        · rename_i h_check
          rw [hif_eq] at h_check; simp [h_check]; exact obsRefinesK_error _
        · rename_i h_check
          rw [hif_eq] at h_check; simp [h_check]
          split
          · rename_i alt_val halt_case
            have hsome₁ := List.getElem?_eq_some_iff.mp halt_case
            have hi₁s : tag < (Moist.Verified.renameTermList
                (Moist.Verified.shiftRename 1) t_alts).length := hsome₁.1
            have hi₁ : tag < t_alts.length := by omega
            have halt₂ : t_alts[tag]? = some (t_alts[tag]) :=
              List.getElem?_eq_some_iff.mpr ⟨hi₁, rfl⟩
            rw [halt₂]; simp only []
            have hidx : (Moist.Verified.renameTermList
                (Moist.Verified.shiftRename 1) t_alts)[tag]'hi₁s =
                Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) (t_alts[tag]) :=
              Moist.Verified.renameTermList_getElem _ _ _ hi₁
            have halt_closed : closedAt d (t_alts[tag]) = true :=
              Moist.Verified.Contextual.BisimRef.closedAtList_get d t_alts _ _ halts_j
                (List.getElem?_eq_some_iff.mpr ⟨hi₁, rfl⟩)
            have heq_alt : alt_val = (Moist.Verified.renameTermList
                (Moist.Verified.shiftRename 1) t_alts)[tag] := hsome₁.2.symm
            subst heq_alt
            rw [hidx]
            have hfields_vcon :=
              Moist.Verified.Equivalence.constToTagAndFields_fields_vcon c₁
            rw [hconst] at hfields_vcon
            have henv_RL : Moist.Verified.FundamentalRefines.RenameEnvRef
                (Moist.Verified.shiftRename 1) (n + 1) d (ρ₁.extend v₁) ρ₂ :=
              Moist.Verified.FundamentalRefines.envRefinesK_to_renameEnvRef_shift henv_j
            exact Moist.Verified.FundamentalRefines.renameRefines_shift1 d (t_alts[tag]) halt_closed
              (n + 1) (n + 1) (Nat.le_refl _) (ρ₁.extend v₁) ρ₂ henv_RL n (by omega)
              ((fields.map Frame.applyArg) ++ π₁)
              ((fields.map Frame.applyArg) ++ π₂)
              (applyArgFrames_stackRefK
                (Moist.Verified.Contextual.SoundnessRefines.listRel_refl_vcon_refines n
                  fields hfields_vcon)
                (stackRefK_mono (by omega) hπ))
          · rename_i hnone₁
            have hnone₂ : t_alts[tag]? = none := by
              rw [List.getElem?_eq_none_iff] at hnone₁ ⊢; omega
            rw [hnone₂]; simp only []; exact obsRefinesK_error _
      · exact obsRefinesK_error _
    | .VLam _ _, .VLam _ _ | .VDelay _ _, .VDelay _ _
    | .VBuiltin _ _ _, .VBuiltin _ _ _ => simp only [step]; exact obsRefinesK_error _
    | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
    | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
    | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
    | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
    | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
    | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
    | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
    | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
    | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at hw

/-- Forward augmented stack helper for let-hoist-case-scrut, one layer above
    `stackRefK_caseScrutinee_shift_aug_fwd`. LHS has `funV (VLam t_body ρ₁)
    :: caseScrutinee t_alts ρ₁ :: π₁`; RHS has `funV (VLam (.Case t_body
    (shift t_alts)) ρ₂) :: π₂`. -/
private theorem stackRefK_funV_caseScrut_shift_fwd {i d : Nat}
    {t_body : Term} {t_alts : List Term} {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv}
    (hclosed_body : closedAt (d + 1) t_body = true)
    (hclosed_alts : Moist.Verified.closedAtList d t_alts = true)
    (henv : EnvRefinesK i d ρ₁ ρ₂)
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i
      (.funV (.VLam t_body ρ₁) :: .caseScrutinee t_alts ρ₁ :: π₁)
      (.funV (.VLam (.Case t_body
        (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_alts)) ρ₂) :: π₂) := by
  intro j hj v₁ v₂ hv
  -- LHS: funV fires → compute (caseScrutinee t_alts ρ₁ :: π₁) (ρ₁.extend v₁) t_body
  have h_lhs :
      steps 1 (State.ret (.funV (.VLam t_body ρ₁) :: .caseScrutinee t_alts ρ₁ :: π₁) v₁) =
        State.compute (.caseScrutinee t_alts ρ₁ :: π₁) (ρ₁.extend v₁) t_body := by rfl
  -- RHS: funV fires → compute π₂ (ρ₂.extend v₂) (.Case t_body (shift t_alts))
  --        → compute (caseScrutinee (shift t_alts) (ρ₂.extend v₂) :: π₂) (ρ₂.extend v₂) t_body
  have h_rhs :
      steps 2 (State.ret (.funV (.VLam (.Case t_body
          (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_alts)) ρ₂) :: π₂) v₂) =
        State.compute (.caseScrutinee
          (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_alts)
          (ρ₂.extend v₂) :: π₂) (ρ₂.extend v₂) t_body := by rfl
  apply obsRefinesK_of_steps_left h_lhs
  apply obsRefinesK_of_steps_right h_rhs
  have henv_j : EnvRefinesK j d ρ₁ ρ₂ := by
    intro n hn hnd
    obtain ⟨w₁, w₂, hl, hr, hw⟩ := henv n hn hnd
    exact ⟨w₁, w₂, hl, hr, valueRefinesK_mono hj _ _ hw⟩
  have henv_ext : EnvRefinesK j (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) :=
    envRefinesK_extend henv_j hv
  have hπ_case : StackRefK ValueRefinesK j
      (.caseScrutinee t_alts ρ₁ :: π₁)
      (.caseScrutinee (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_alts)
          (ρ₂.extend v₂) :: π₂) :=
    stackRefK_caseScrutinee_shift_aug_fwd hclosed_alts henv_j (stackRefK_mono hj hπ)
  exact ftlr (d + 1) t_body hclosed_body j j (Nat.le_refl _) (ρ₁.extend v₁) (ρ₂.extend v₂)
    henv_ext j (Nat.le_refl _) _ _ hπ_case

/-- Backward augmented stack helper for let-hoist-case-scrut. LHS has `funV
    (VLam (.Case t_body (shift t_alts)) ρ₁) :: π₁`; RHS has `funV (VLam
    t_body ρ₂) :: caseScrutinee t_alts ρ₂ :: π₂`. -/
private theorem stackRefK_funV_caseScrut_shift_bwd {i d : Nat}
    {t_body : Term} {t_alts : List Term} {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv}
    (hclosed_body : closedAt (d + 1) t_body = true)
    (hclosed_alts : Moist.Verified.closedAtList d t_alts = true)
    (henv : EnvRefinesK i d ρ₁ ρ₂)
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i
      (.funV (.VLam (.Case t_body
        (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_alts)) ρ₁) :: π₁)
      (.funV (.VLam t_body ρ₂) :: .caseScrutinee t_alts ρ₂ :: π₂) := by
  intro j hj v₁ v₂ hv
  have h_lhs :
      steps 2 (State.ret (.funV (.VLam (.Case t_body
          (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_alts)) ρ₁) :: π₁) v₁) =
        State.compute (.caseScrutinee
          (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_alts)
          (ρ₁.extend v₁) :: π₁) (ρ₁.extend v₁) t_body := by rfl
  have h_rhs :
      steps 1 (State.ret (.funV (.VLam t_body ρ₂) :: .caseScrutinee t_alts ρ₂ :: π₂) v₂) =
        State.compute (.caseScrutinee t_alts ρ₂ :: π₂) (ρ₂.extend v₂) t_body := by rfl
  apply obsRefinesK_of_steps_left h_lhs
  apply obsRefinesK_of_steps_right h_rhs
  have henv_j : EnvRefinesK j d ρ₁ ρ₂ := by
    intro n hn hnd
    obtain ⟨w₁, w₂, hl, hr, hw⟩ := henv n hn hnd
    exact ⟨w₁, w₂, hl, hr, valueRefinesK_mono hj _ _ hw⟩
  have henv_ext : EnvRefinesK j (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) :=
    envRefinesK_extend henv_j hv
  have hπ_case : StackRefK ValueRefinesK j
      (.caseScrutinee (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_alts)
          (ρ₁.extend v₁) :: π₁)
      (.caseScrutinee t_alts ρ₂ :: π₂) :=
    stackRefK_caseScrutinee_shift_aug_bwd hclosed_alts henv_j (stackRefK_mono hj hπ)
  exact ftlr (d + 1) t_body hclosed_body j j (Nat.le_refl _) (ρ₁.extend v₁) (ρ₂.extend v₂)
    henv_ext j (Nat.le_refl _) _ _ hπ_case

/-- Lowering shape lemma: `.Case (.Let [(v, rhs, false)] body) alts` lowers
    to `.Case (.Apply (.Lam 0 t_body) t_rhs) t_alts`. -/
private theorem lowerTotalExpr_case_let {env : List VarId} (v : VarId)
    {rhs body : Expr} {alts : List Expr} {t_rhs t_body : Term} {t_alts : List Term}
    (h_rhs : lowerTotalExpr env rhs = some t_rhs)
    (h_body : lowerTotalExpr (v :: env) body = some t_body)
    (h_alts : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList alts) = some t_alts) :
    lowerTotalExpr env (.Case (.Let [(v, rhs, false)] body) alts) =
      some (.Case (.Apply (.Lam 0 t_body) t_rhs) t_alts) := by
  have h_rhs' : lowerTotal env (Moist.MIR.expandFix rhs) = some t_rhs := h_rhs
  have h_body' : lowerTotal (v :: env) (Moist.MIR.expandFix body) = some t_body := h_body
  show lowerTotal env (Moist.MIR.expandFix (.Case (.Let [(v, rhs, false)] body) alts)) =
    some (.Case (.Apply (.Lam 0 t_body) t_rhs) t_alts)
  simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
             Moist.MIR.lowerTotalLet, Option.bind_eq_bind, Option.bind_some,
             h_rhs', h_body', h_alts]

/-- Lowering shape lemma: `.Let [(v, rhs, false)] (.Case body alts)` lowers
    to `.Apply (.Lam 0 (.Case t_body (shifted t_alts))) t_rhs` when `v` is
    fresh in `alts`. -/
private theorem lowerTotalExpr_let_case_fresh {env : List VarId} (v : VarId)
    {rhs body : Expr} {alts : List Expr} {t_rhs t_body : Term} {t_alts : List Term}
    (hfresh : (Moist.MIR.freeVarsList alts).contains v = false)
    (h_rhs : lowerTotalExpr env rhs = some t_rhs)
    (h_body : lowerTotalExpr (v :: env) body = some t_body)
    (h_alts : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList alts) = some t_alts) :
    lowerTotalExpr env (.Let [(v, rhs, false)] (.Case body alts)) =
      some (.Apply (.Lam 0 (.Case t_body
        (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_alts))) t_rhs) := by
  have h_rhs' : lowerTotal env (Moist.MIR.expandFix rhs) = some t_rhs := h_rhs
  have h_body' : lowerTotal (v :: env) (Moist.MIR.expandFix body) = some t_body := h_body
  have hfresh_exp : (Moist.MIR.freeVarsList (Moist.MIR.expandFixList alts)).contains v = false :=
    Moist.MIR.expandFixList_freeVars_not_contains alts v hfresh
  have h_alts_shift :
      Moist.MIR.lowerTotalList (v :: env) (Moist.MIR.expandFixList alts) =
        some (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_alts) := by
    have h := Moist.MIR.lowerTotalList_prepend_unused_gen [] env v
      (Moist.MIR.expandFixList alts) (.inl hfresh_exp) t_alts h_alts
    simpa using h
  show lowerTotal env (Moist.MIR.expandFix (.Let [(v, rhs, false)] (.Case body alts))) =
    some (.Apply (.Lam 0 (.Case t_body
      (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_alts))) t_rhs)
  simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
             Moist.MIR.lowerTotalLet, Option.bind_eq_bind, Option.bind_some,
             h_rhs', h_body', h_alts_shift]

private theorem lowerTotalExpr_case_let_isSome (env : List VarId) (v : VarId)
    (rhs body : Expr) (alts : List Expr) :
    (lowerTotalExpr env (.Case (.Let [(v, rhs, false)] body) alts)).isSome ↔
      (lowerTotalExpr env rhs).isSome ∧
      (lowerTotalExpr (v :: env) body).isSome ∧
      (Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList alts)).isSome := by
  constructor
  · intro hsome
    have h : (lowerTotal env (Moist.MIR.expandFix
        (.Case (.Let [(v, rhs, false)] body) alts))).isSome := hsome
    simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
               Moist.MIR.lowerTotalLet, Option.bind_eq_bind] at h
    cases hr : lowerTotal env (Moist.MIR.expandFix rhs) with
    | none => rw [hr] at h; simp at h
    | some t_r =>
      rw [hr] at h
      simp only [Option.bind_some] at h
      cases hb : lowerTotal (v :: env) (Moist.MIR.expandFix body) with
      | none => rw [hb] at h; simp at h
      | some t_b =>
        rw [hb] at h
        simp only [Option.bind_some] at h
        cases ha : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList alts) with
        | none => rw [ha] at h; simp at h
        | some t_a =>
          have hr' : lowerTotalExpr env rhs = some t_r := hr
          have hb' : lowerTotalExpr (v :: env) body = some t_b := hb
          refine ⟨?_, ?_, ?_⟩
          · rw [hr']; rfl
          · rw [hb']; rfl
          · rfl
  · rintro ⟨hr, hb, ha⟩
    cases hr' : lowerTotalExpr env rhs with
    | none => rw [hr'] at hr; exact absurd hr (by simp)
    | some t_r =>
      cases hb' : lowerTotalExpr (v :: env) body with
      | none => rw [hb'] at hb; exact absurd hb (by simp)
      | some t_b =>
        cases ha' : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList alts) with
        | none => rw [ha'] at ha; exact absurd ha (by simp)
        | some t_a =>
          rw [lowerTotalExpr_case_let v hr' hb' ha']
          rfl

private theorem lowerTotalExpr_let_case_isSome (env : List VarId) (v : VarId)
    (rhs body : Expr) (alts : List Expr)
    (hfresh : (Moist.MIR.freeVarsList alts).contains v = false) :
    (lowerTotalExpr env (.Let [(v, rhs, false)] (.Case body alts))).isSome ↔
      (lowerTotalExpr env rhs).isSome ∧
      (lowerTotalExpr (v :: env) body).isSome ∧
      (Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList alts)).isSome := by
  have hfresh_exp : (Moist.MIR.freeVarsList (Moist.MIR.expandFixList alts)).contains v = false :=
    Moist.MIR.expandFixList_freeVars_not_contains alts v hfresh
  constructor
  · intro hsome
    have h : (lowerTotal env (Moist.MIR.expandFix
        (.Let [(v, rhs, false)] (.Case body alts)))).isSome := hsome
    simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
               Moist.MIR.lowerTotalLet, Option.bind_eq_bind] at h
    cases hr : lowerTotal env (Moist.MIR.expandFix rhs) with
    | none => rw [hr] at h; simp at h
    | some t_r =>
      rw [hr] at h
      simp only [Option.bind_some] at h
      cases hb : lowerTotal (v :: env) (Moist.MIR.expandFix body) with
      | none => rw [hb] at h; simp at h
      | some t_b =>
        rw [hb] at h
        simp only [Option.bind_some] at h
        cases ha_ext : Moist.MIR.lowerTotalList (v :: env) (Moist.MIR.expandFixList alts) with
        | none => rw [ha_ext] at h; simp at h
        | some t_a_ext =>
          cases ha : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList alts) with
          | none =>
            have := Moist.MIR.lowerTotalList_prepend_unused_none_gen [] env v
              (Moist.MIR.expandFixList alts) (.inl hfresh_exp) (by simpa using ha)
            have hext : Moist.MIR.lowerTotalList (v :: env) (Moist.MIR.expandFixList alts) = none := by
              simpa using this
            rw [hext] at ha_ext; exact absurd ha_ext (by simp)
          | some t_a =>
            have hr' : lowerTotalExpr env rhs = some t_r := hr
            have hb' : lowerTotalExpr (v :: env) body = some t_b := hb
            refine ⟨?_, ?_, ?_⟩
            · rw [hr']; rfl
            · rw [hb']; rfl
            · rfl
  · rintro ⟨hr, hb, ha⟩
    cases hr' : lowerTotalExpr env rhs with
    | none => rw [hr'] at hr; exact absurd hr (by simp)
    | some t_r =>
      cases hb' : lowerTotalExpr (v :: env) body with
      | none => rw [hb'] at hb; exact absurd hb (by simp)
      | some t_b =>
        cases ha' : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList alts) with
        | none => rw [ha'] at ha; exact absurd ha (by simp)
        | some t_a =>
          rw [lowerTotalExpr_let_case_fresh v hfresh hr' hb' ha']
          rfl

theorem mirRefines_let_hoist_case_scrut_fwd (v : VarId) (rhs body : Expr) (alts : List Expr)
    (hfresh : (Moist.MIR.freeVarsList alts).contains v = false) :
    MIRRefines (.Case (.Let [(v, rhs, false)] body) alts)
               (.Let [(v, rhs, false)] (.Case body alts)) := by
  refine ⟨?_, ?_⟩
  · intro env hsome
    have h := (lowerTotalExpr_case_let_isSome env v rhs body alts).mp hsome
    exact (lowerTotalExpr_let_case_isSome env v rhs body alts hfresh).mpr h
  · intro d k env hlen
    cases hr : lowerTotalExpr env rhs with
    | none =>
      have h_lhs : lowerTotalExpr env (.Case (.Let [(v, rhs, false)] body) alts) = none := by
        cases h : lowerTotalExpr env (.Case (.Let [(v, rhs, false)] body) alts) with
        | none => rfl
        | some _ =>
          have hsome : (lowerTotalExpr env (.Case (.Let [(v, rhs, false)] body) alts)).isSome := by
            rw [h]; rfl
          have := (lowerTotalExpr_case_let_isSome env v rhs body alts).mp hsome
          rw [hr] at this; exact absurd this.1 (by simp)
      rw [h_lhs]; trivial
    | some t_r =>
      cases hb : lowerTotalExpr (v :: env) body with
      | none =>
        have h_lhs : lowerTotalExpr env (.Case (.Let [(v, rhs, false)] body) alts) = none := by
          cases h : lowerTotalExpr env (.Case (.Let [(v, rhs, false)] body) alts) with
          | none => rfl
          | some _ =>
            have hsome : (lowerTotalExpr env (.Case (.Let [(v, rhs, false)] body) alts)).isSome := by
              rw [h]; rfl
            have := (lowerTotalExpr_case_let_isSome env v rhs body alts).mp hsome
            rw [hb] at this; exact absurd this.2.1 (by simp)
        rw [h_lhs]; trivial
      | some t_b =>
        cases ha : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList alts) with
        | none =>
          have h_lhs : lowerTotalExpr env (.Case (.Let [(v, rhs, false)] body) alts) = none := by
            cases h : lowerTotalExpr env (.Case (.Let [(v, rhs, false)] body) alts) with
            | none => rfl
            | some _ =>
              have hsome : (lowerTotalExpr env (.Case (.Let [(v, rhs, false)] body) alts)).isSome := by
                rw [h]; rfl
              have := (lowerTotalExpr_case_let_isSome env v rhs body alts).mp hsome
              rw [ha] at this; exact absurd this.2.2 (by simp)
          rw [h_lhs]; trivial
        | some t_a =>
          rw [lowerTotalExpr_case_let v hr hb ha, lowerTotalExpr_let_case_fresh v hfresh hr hb ha]
          simp only
          intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
          -- LHS: compute π₁ ρ₁ (.Case (.Apply (.Lam 0 t_b) t_r) t_a)
          -- 1 step: compute (caseScrutinee t_a ρ₁ :: π₁) ρ₁ (.Apply (.Lam 0 t_b) t_r)
          -- then 3 more: compute (funV (VLam t_b ρ₁) :: caseScrutinee t_a ρ₁ :: π₁) ρ₁ t_r
          have h_steps_lhs :
              steps 4 (State.compute π₁ ρ₁ (.Case (.Apply (.Lam 0 t_b) t_r) t_a)) =
                State.compute (.funV (.VLam t_b ρ₁) :: .caseScrutinee t_a ρ₁ :: π₁) ρ₁ t_r := by rfl
          -- RHS: compute π₂ ρ₂ (.Apply (.Lam 0 (.Case t_b (shift t_a))) t_r)
          -- 3 steps → compute (funV (VLam (.Case t_b (shift t_a)) ρ₂) :: π₂) ρ₂ t_r
          have h_steps_rhs :
              steps 3 (State.compute π₂ ρ₂ (.Apply (.Lam 0 (.Case t_b
                (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_a))) t_r)) =
                State.compute (.funV (.VLam (.Case t_b
                  (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_a)) ρ₂) :: π₂)
                  ρ₂ t_r := by rfl
          apply obsRefinesK_of_steps_left h_steps_lhs
          apply obsRefinesK_of_steps_right h_steps_rhs
          have hclosed_r : closedAt env.length t_r :=
            Moist.Verified.MIR.lowerTotal_closedAt env _ t_r hr
          have hclosed_b : closedAt (env.length + 1) t_b := by
            have := Moist.Verified.MIR.lowerTotal_closedAt (v :: env) _ t_b hb
            simpa [List.length_cons] using this
          have hclosed_a : Moist.Verified.closedAtList env.length t_a :=
            Moist.Verified.MIR.lowerTotalList_closedAtList env _ t_a ha
          have hd_eq : d = env.length := hlen.symm
          subst hd_eq
          have henv_j : EnvRefinesK j env.length ρ₁ ρ₂ := by
            intro n hn hnd
            obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv n hn hnd
            exact ⟨w₁, w₂, hl, hr', hw⟩
          have henv_i : EnvRefinesK i env.length ρ₁ ρ₂ := by
            intro n hn hnd
            obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv_j n hn hnd
            exact ⟨w₁, w₂, hl, hr', valueRefinesK_mono hi _ _ hw⟩
          have hπ_aug : StackRefK ValueRefinesK i
              (.funV (.VLam t_b ρ₁) :: .caseScrutinee t_a ρ₁ :: π₁)
              (.funV (.VLam (.Case t_b
                (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_a)) ρ₂) :: π₂) :=
            stackRefK_funV_caseScrut_shift_fwd hclosed_b hclosed_a henv_i hπ
          exact ftlr env.length t_r hclosed_r j j (Nat.le_refl _) ρ₁ ρ₂ henv_j i hi
            _ _ hπ_aug

theorem mirRefines_let_hoist_case_scrut_bwd (v : VarId) (rhs body : Expr) (alts : List Expr)
    (hfresh : (Moist.MIR.freeVarsList alts).contains v = false) :
    MIRRefines (.Let [(v, rhs, false)] (.Case body alts))
               (.Case (.Let [(v, rhs, false)] body) alts) := by
  refine ⟨?_, ?_⟩
  · intro env hsome
    have h := (lowerTotalExpr_let_case_isSome env v rhs body alts hfresh).mp hsome
    exact (lowerTotalExpr_case_let_isSome env v rhs body alts).mpr h
  · intro d k env hlen
    cases hr : lowerTotalExpr env rhs with
    | none =>
      have h_lhs : lowerTotalExpr env (.Let [(v, rhs, false)] (.Case body alts)) = none := by
        cases h : lowerTotalExpr env (.Let [(v, rhs, false)] (.Case body alts)) with
        | none => rfl
        | some _ =>
          have hsome : (lowerTotalExpr env (.Let [(v, rhs, false)] (.Case body alts))).isSome := by
            rw [h]; rfl
          have := (lowerTotalExpr_let_case_isSome env v rhs body alts hfresh).mp hsome
          rw [hr] at this; exact absurd this.1 (by simp)
      rw [h_lhs]; trivial
    | some t_r =>
      cases hb : lowerTotalExpr (v :: env) body with
      | none =>
        have h_lhs : lowerTotalExpr env (.Let [(v, rhs, false)] (.Case body alts)) = none := by
          cases h : lowerTotalExpr env (.Let [(v, rhs, false)] (.Case body alts)) with
          | none => rfl
          | some _ =>
            have hsome : (lowerTotalExpr env (.Let [(v, rhs, false)] (.Case body alts))).isSome := by
              rw [h]; rfl
            have := (lowerTotalExpr_let_case_isSome env v rhs body alts hfresh).mp hsome
            rw [hb] at this; exact absurd this.2.1 (by simp)
        rw [h_lhs]; trivial
      | some t_b =>
        cases ha : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList alts) with
        | none =>
          have h_lhs : lowerTotalExpr env (.Let [(v, rhs, false)] (.Case body alts)) = none := by
            cases h : lowerTotalExpr env (.Let [(v, rhs, false)] (.Case body alts)) with
            | none => rfl
            | some _ =>
              have hsome : (lowerTotalExpr env (.Let [(v, rhs, false)] (.Case body alts))).isSome := by
                rw [h]; rfl
              have := (lowerTotalExpr_let_case_isSome env v rhs body alts hfresh).mp hsome
              rw [ha] at this; exact absurd this.2.2 (by simp)
          rw [h_lhs]; trivial
        | some t_a =>
          rw [lowerTotalExpr_let_case_fresh v hfresh hr hb ha, lowerTotalExpr_case_let v hr hb ha]
          simp only
          intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
          have h_steps_lhs :
              steps 3 (State.compute π₁ ρ₁ (.Apply (.Lam 0 (.Case t_b
                (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_a))) t_r)) =
                State.compute (.funV (.VLam (.Case t_b
                  (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_a)) ρ₁) :: π₁)
                  ρ₁ t_r := by rfl
          have h_steps_rhs :
              steps 4 (State.compute π₂ ρ₂ (.Case (.Apply (.Lam 0 t_b) t_r) t_a)) =
                State.compute (.funV (.VLam t_b ρ₂) :: .caseScrutinee t_a ρ₂ :: π₂) ρ₂ t_r := by rfl
          apply obsRefinesK_of_steps_left h_steps_lhs
          apply obsRefinesK_of_steps_right h_steps_rhs
          have hclosed_r : closedAt env.length t_r :=
            Moist.Verified.MIR.lowerTotal_closedAt env _ t_r hr
          have hclosed_b : closedAt (env.length + 1) t_b := by
            have := Moist.Verified.MIR.lowerTotal_closedAt (v :: env) _ t_b hb
            simpa [List.length_cons] using this
          have hclosed_a : Moist.Verified.closedAtList env.length t_a :=
            Moist.Verified.MIR.lowerTotalList_closedAtList env _ t_a ha
          have hd_eq : d = env.length := hlen.symm
          subst hd_eq
          have henv_j : EnvRefinesK j env.length ρ₁ ρ₂ := by
            intro n hn hnd
            obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv n hn hnd
            exact ⟨w₁, w₂, hl, hr', hw⟩
          have henv_i : EnvRefinesK i env.length ρ₁ ρ₂ := by
            intro n hn hnd
            obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv_j n hn hnd
            exact ⟨w₁, w₂, hl, hr', valueRefinesK_mono hi _ _ hw⟩
          have hπ_aug : StackRefK ValueRefinesK i
              (.funV (.VLam (.Case t_b
                (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_a)) ρ₁) :: π₁)
              (.funV (.VLam t_b ρ₂) :: .caseScrutinee t_a ρ₂ :: π₂) :=
            stackRefK_funV_caseScrut_shift_bwd hclosed_b hclosed_a henv_i hπ
          exact ftlr env.length t_r hclosed_r j j (Nat.le_refl _) ρ₁ ρ₂ henv_j i hi
            _ _ hπ_aug

private theorem let_hoist_case_scrut_close_pres_fwd (v : VarId) (rhs body : Expr)
    (alts : List Expr) (hfresh : (Moist.MIR.freeVarsList alts).contains v = false) :
    ∀ env k t₁ t₂,
      lowerTotalExpr env (.Case (.Let [(v, rhs, false)] body) alts) = some t₁ →
      lowerTotalExpr env (.Let [(v, rhs, false)] (.Case body alts)) = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true := by
  intro env k t₁ t₂ h₁ h₂ hc
  have hsome₁ : (lowerTotalExpr env (.Case (.Let [(v, rhs, false)] body) alts)).isSome := by
    rw [h₁]; exact rfl
  obtain ⟨hr_some, hb_some, ha_some⟩ :=
    (lowerTotalExpr_case_let_isSome env v rhs body alts).mp hsome₁
  cases hr : lowerTotalExpr env rhs with
  | none => rw [hr] at hr_some; exact absurd hr_some (by simp)
  | some t_r =>
    cases hb : lowerTotalExpr (v :: env) body with
    | none => rw [hb] at hb_some; exact absurd hb_some (by simp)
    | some t_b =>
      cases ha : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList alts) with
      | none => rw [ha] at ha_some; exact absurd ha_some (by simp)
      | some t_a =>
        rw [lowerTotalExpr_case_let v hr hb ha] at h₁
        rw [lowerTotalExpr_let_case_fresh v hfresh hr hb ha] at h₂
        injection h₁ with h₁; subst h₁
        injection h₂ with h₂; subst h₂
        simp only [closedAt, Bool.and_eq_true] at hc ⊢
        obtain ⟨⟨hb_c, hr_c⟩, ha_c⟩ := hc
        refine ⟨⟨hb_c, ?_⟩, hr_c⟩
        by_cases hk : k = 0
        · subst hk
          exact closedAtList_renameTermList_shiftRename t_a 0 1 (by omega) (by omega) ha_c
        · have hkp : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk
          exact closedAtList_renameTermList_shiftRename t_a k 1 (by omega) (by omega) ha_c

private theorem let_hoist_case_scrut_close_pres_bwd (v : VarId) (rhs body : Expr)
    (alts : List Expr) (hfresh : (Moist.MIR.freeVarsList alts).contains v = false) :
    ∀ env k t₁ t₂,
      lowerTotalExpr env (.Let [(v, rhs, false)] (.Case body alts)) = some t₁ →
      lowerTotalExpr env (.Case (.Let [(v, rhs, false)] body) alts) = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true := by
  intro env k t₁ t₂ h₁ h₂ hc
  have hsome₁ : (lowerTotalExpr env (.Let [(v, rhs, false)] (.Case body alts))).isSome := by
    rw [h₁]; exact rfl
  obtain ⟨hr_some, hb_some, ha_some⟩ :=
    (lowerTotalExpr_let_case_isSome env v rhs body alts hfresh).mp hsome₁
  cases hr : lowerTotalExpr env rhs with
  | none => rw [hr] at hr_some; exact absurd hr_some (by simp)
  | some t_r =>
    cases hb : lowerTotalExpr (v :: env) body with
    | none => rw [hb] at hb_some; exact absurd hb_some (by simp)
    | some t_b =>
      cases ha : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList alts) with
      | none => rw [ha] at ha_some; exact absurd ha_some (by simp)
      | some t_a =>
        rw [lowerTotalExpr_let_case_fresh v hfresh hr hb ha] at h₁
        rw [lowerTotalExpr_case_let v hr hb ha] at h₂
        injection h₁ with h₁; subst h₁
        injection h₂ with h₂; subst h₂
        simp only [closedAt, Bool.and_eq_true] at hc ⊢
        obtain ⟨⟨hb_c, ha_sh_c⟩, hr_c⟩ := hc
        have ha_c : Moist.Verified.closedAtList k t_a = true := by
          by_cases hk : k = 0
          · subst hk
            exact closedAtList_renameTermList_shiftRename_inv t_a 0 1 (by omega) (by omega) ha_sh_c
          · have hkp : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk
            exact closedAtList_renameTermList_shiftRename_inv t_a k 1 (by omega) (by omega) ha_sh_c
        exact ⟨⟨hb_c, hr_c⟩, ha_c⟩

theorem mirCtxRefines_let_hoist_case_scrut_fwd (v : VarId) (rhs body : Expr) (alts : List Expr)
    (hfresh : (Moist.MIR.freeVarsList alts).contains v = false) :
    MIRCtxRefines (.Case (.Let [(v, rhs, false)] body) alts)
                  (.Let [(v, rhs, false)] (.Case body alts)) :=
  mirRefines_to_mirCtxRefines
    (mirRefines_let_hoist_case_scrut_fwd v rhs body alts hfresh)
    (let_hoist_case_scrut_close_pres_fwd v rhs body alts hfresh)

theorem mirCtxRefines_let_hoist_case_scrut_bwd (v : VarId) (rhs body : Expr) (alts : List Expr)
    (hfresh : (Moist.MIR.freeVarsList alts).contains v = false) :
    MIRCtxRefines (.Let [(v, rhs, false)] (.Case body alts))
                  (.Case (.Let [(v, rhs, false)] body) alts) :=
  mirRefines_to_mirCtxRefines
    (mirRefines_let_hoist_case_scrut_bwd v rhs body alts hfresh)
    (let_hoist_case_scrut_close_pres_bwd v rhs body alts hfresh)

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
      Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList as) = some t_as →
      allLeafAtoms t_as := by
  intro env as
  induction as with
  | nil =>
    intro t_as _ h
    simp only [Moist.MIR.expandFixList, Moist.MIR.lowerTotalList] at h
    injection h with h; subst h
    exact allLeafAtoms_nil
  | cons a rest ih =>
    intro t_as hatom h
    simp only [Moist.MIR.expandFixList, Moist.MIR.lowerTotalList, Option.bind_eq_bind] at h
    cases ht : Moist.MIR.lowerTotal env (Moist.MIR.expandFix a) with
    | none => rw [ht] at h; simp at h
    | some t_a =>
      rw [ht] at h
      simp only [Option.bind_some] at h
      cases htr : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList rest) with
      | none => rw [htr] at h; simp at h
      | some t_rest =>
        rw [htr] at h
        simp only [Option.bind_some] at h
        injection h with h; subst h
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
    Moist.MIR.expandFixList (xs ++ ys) =
      Moist.MIR.expandFixList xs ++ Moist.MIR.expandFixList ys := by
  induction xs with
  | nil => simp [Moist.MIR.expandFixList]
  | cons x xs' ih =>
    show Moist.MIR.expandFixList (x :: (xs' ++ ys)) = _
    simp only [Moist.MIR.expandFixList]
    rw [ih]
    rfl

/-- `lowerTotalList env (xs ++ ys)` succeeds with `ts_x ++ ts_y` iff both succeed. -/
private theorem lowerTotalList_append {env : List VarId} (xs ys : List Expr)
    {ts_x ts_y : List Term}
    (hxs : Moist.MIR.lowerTotalList env xs = some ts_x)
    (hys : Moist.MIR.lowerTotalList env ys = some ts_y) :
    Moist.MIR.lowerTotalList env (xs ++ ys) = some (ts_x ++ ts_y) := by
  induction xs generalizing ts_x with
  | nil =>
    simp only [Moist.MIR.lowerTotalList] at hxs
    injection hxs with hxs; subst hxs
    simpa using hys
  | cons x xs' ih =>
    simp only [Moist.MIR.lowerTotalList, Option.bind_eq_bind] at hxs
    cases hx : Moist.MIR.lowerTotal env x with
    | none => rw [hx] at hxs; simp at hxs
    | some t_x =>
      rw [hx] at hxs
      simp only [Option.bind_some] at hxs
      cases hxs' : Moist.MIR.lowerTotalList env xs' with
      | none => rw [hxs'] at hxs; simp at hxs
      | some ts_x' =>
        rw [hxs'] at hxs
        simp only [Option.bind_some] at hxs
        injection hxs with hxs; subst hxs
        have h_rec := ih hxs'
        show Moist.MIR.lowerTotalList env (x :: (xs' ++ ys)) = some (t_x :: ts_x' ++ ts_y)
        simp only [Moist.MIR.lowerTotalList, Option.bind_eq_bind]
        rw [hx, h_rec]
        rfl

/-- Three-way split for `lowerTotalList`. -/
private theorem lowerTotalList_append3 {env : List VarId}
    (pre : List Expr) (mid : Expr) (post : List Expr)
    {t_pre : List Term} {t_mid : Term} {t_post : List Term}
    (hpre : Moist.MIR.lowerTotalList env pre = some t_pre)
    (hmid : Moist.MIR.lowerTotal env mid = some t_mid)
    (hpost : Moist.MIR.lowerTotalList env post = some t_post) :
    Moist.MIR.lowerTotalList env (pre ++ [mid] ++ post) =
      some (t_pre ++ [t_mid] ++ t_post) := by
  have hmid' : Moist.MIR.lowerTotalList env [mid] = some [t_mid] := by
    simp only [Moist.MIR.lowerTotalList, Option.bind_eq_bind]
    rw [hmid]
    rfl
  have h1 : Moist.MIR.lowerTotalList env (pre ++ [mid]) = some (t_pre ++ [t_mid]) :=
    lowerTotalList_append pre [mid] hpre hmid'
  exact lowerTotalList_append (pre ++ [mid]) post h1 hpost

/-- General stack helper for constrField with shifted `todo` on the right.
    Mirrors `renameRefinesRConstrField` from FundamentalRefines but specialized
    to `shiftRename 1` with a single extended env slot on the right. -/
private theorem stackRefK_constrField_general_shift_aug_fwd {d tag : Nat}
    (t_todo : List Term) (htodo_closed : Moist.Verified.closedAtList d t_todo = true) :
    ∀ {i : Nat} {done₁ done₂ : List CekValue} {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv}
      {v₂ : CekValue},
      ListRel (ValueRefinesK i) done₁ done₂ →
      EnvRefinesK i d ρ₁ ρ₂ →
      StackRefK ValueRefinesK i π₁ π₂ →
      StackRefK ValueRefinesK i
        (.constrField tag done₁ t_todo ρ₁ :: π₁)
        (.constrField tag done₂
          (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_todo)
          (ρ₂.extend v₂) :: π₂) := by
  induction t_todo with
  | nil =>
    intro i done₁ done₂ π₁ π₂ ρ₁ ρ₂ v₂ hdone henv hπ j hj w₁ w₂ hw
    match j with
    | 0 => exact obsRefinesK_zero_ret
    | n + 1 =>
      obsRefinesK_of_step_auto
      simp only [Moist.Verified.renameTermList, step]
      have hdone_n : ListRel (ValueRefinesK n) done₁ done₂ :=
        listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) hdone
      have hw_n : ValueRefinesK n w₁ w₂ := valueRefinesK_mono (by omega) _ _ hw
      have hcons : ListRel (ValueRefinesK n) (w₁ :: done₁) (w₂ :: done₂) :=
        ⟨hw_n, hdone_n⟩
      have hrev : ListRel (ValueRefinesK n) ((w₁ :: done₁).reverse) ((w₂ :: done₂).reverse) :=
        Moist.Verified.Equivalence.listRel_reverse hcons
      have hval : ValueRefinesK (n + 1) (.VConstr tag ((w₁ :: done₁).reverse))
          (.VConstr tag ((w₂ :: done₂).reverse)) := by
        match n with
        | 0 => simp only [ValueRefinesK]; exact ⟨trivial, hrev⟩
        | _ + 1 => simp only [ValueRefinesK]; exact ⟨trivial, hrev⟩
      have hπ_n : StackRefK ValueRefinesK n π₁ π₂ := stackRefK_mono (by omega) hπ
      exact hπ_n n (Nat.le_refl _) _ _ (valueRefinesK_mono (by omega) _ _ hval)
  | cons t_a t_rest ih =>
    have ha_closed : closedAt d t_a = true := by
      simp only [Moist.Verified.closedAtList, Bool.and_eq_true] at htodo_closed
      exact htodo_closed.1
    have hrest_closed : Moist.Verified.closedAtList d t_rest = true := by
      simp only [Moist.Verified.closedAtList, Bool.and_eq_true] at htodo_closed
      exact htodo_closed.2
    intro i done₁ done₂ π₁ π₂ ρ₁ ρ₂ v₂ hdone henv hπ j hj w₁ w₂ hw
    match j with
    | 0 => exact obsRefinesK_zero_ret
    | n + 1 =>
      obsRefinesK_of_step_auto
      simp only [Moist.Verified.renameTermList, step]
      -- LHS: compute (cF tag (w₁ :: done₁) t_rest ρ₁ :: π₁) ρ₁ t_a
      -- RHS: compute (cF tag (w₂ :: done₂) (shift t_rest) (ρ₂.extend v₂) :: π₂)
      --         (ρ₂.extend v₂) (shift t_a)
      -- Apply renameRefinesR_shift1 for t_a with RenameEnvRefR
      have henv_n : EnvRefinesK n d ρ₁ ρ₂ := by
        intro p hp hpd
        obtain ⟨w₁', w₂', hl, hr, hrel⟩ := henv p hp hpd
        exact ⟨w₁', w₂', hl, hr, valueRefinesK_mono (by omega) _ _ hrel⟩
      have henv_RR : Moist.Verified.FundamentalRefines.RenameEnvRefR
          (Moist.Verified.shiftRename 1) n d ρ₁ (ρ₂.extend v₂) :=
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
    (t_todo : List Term) (htodo_closed : Moist.Verified.closedAtList d t_todo = true) :
    ∀ {i : Nat} {done₁ done₂ : List CekValue} {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv}
      {v₁ : CekValue},
      ListRel (ValueRefinesK i) done₁ done₂ →
      EnvRefinesK i d ρ₁ ρ₂ →
      StackRefK ValueRefinesK i π₁ π₂ →
      StackRefK ValueRefinesK i
        (.constrField tag done₁
          (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_todo)
          (ρ₁.extend v₁) :: π₁)
        (.constrField tag done₂ t_todo ρ₂ :: π₂) := by
  induction t_todo with
  | nil =>
    intro i done₁ done₂ π₁ π₂ ρ₁ ρ₂ v₁ hdone henv hπ j hj w₁ w₂ hw
    match j with
    | 0 => exact obsRefinesK_zero_ret
    | n + 1 =>
      obsRefinesK_of_step_auto
      simp only [Moist.Verified.renameTermList, step]
      have hdone_n : ListRel (ValueRefinesK n) done₁ done₂ :=
        listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) hdone
      have hw_n : ValueRefinesK n w₁ w₂ := valueRefinesK_mono (by omega) _ _ hw
      have hcons : ListRel (ValueRefinesK n) (w₁ :: done₁) (w₂ :: done₂) :=
        ⟨hw_n, hdone_n⟩
      have hrev : ListRel (ValueRefinesK n) ((w₁ :: done₁).reverse) ((w₂ :: done₂).reverse) :=
        Moist.Verified.Equivalence.listRel_reverse hcons
      have hval : ValueRefinesK (n + 1) (.VConstr tag ((w₁ :: done₁).reverse))
          (.VConstr tag ((w₂ :: done₂).reverse)) := by
        match n with
        | 0 => simp only [ValueRefinesK]; exact ⟨trivial, hrev⟩
        | _ + 1 => simp only [ValueRefinesK]; exact ⟨trivial, hrev⟩
      have hπ_n : StackRefK ValueRefinesK n π₁ π₂ := stackRefK_mono (by omega) hπ
      exact hπ_n n (Nat.le_refl _) _ _ (valueRefinesK_mono (by omega) _ _ hval)
  | cons t_a t_rest ih =>
    have ha_closed : closedAt d t_a = true := by
      simp only [Moist.Verified.closedAtList, Bool.and_eq_true] at htodo_closed
      exact htodo_closed.1
    have hrest_closed : Moist.Verified.closedAtList d t_rest = true := by
      simp only [Moist.Verified.closedAtList, Bool.and_eq_true] at htodo_closed
      exact htodo_closed.2
    intro i done₁ done₂ π₁ π₂ ρ₁ ρ₂ v₁ hdone henv hπ j hj w₁ w₂ hw
    match j with
    | 0 => exact obsRefinesK_zero_ret
    | n + 1 =>
      obsRefinesK_of_step_auto
      simp only [Moist.Verified.renameTermList, step]
      have henv_n : EnvRefinesK n d ρ₁ ρ₂ := by
        intro p hp hpd
        obtain ⟨w₁', w₂', hl, hr, hrel⟩ := henv p hp hpd
        exact ⟨w₁', w₂', hl, hr, valueRefinesK_mono (by omega) _ _ hrel⟩
      have henv_RL : Moist.Verified.FundamentalRefines.RenameEnvRef
          (Moist.Verified.shiftRename 1) n d (ρ₁.extend v₁) ρ₂ :=
        Moist.Verified.FundamentalRefines.envRefinesK_to_renameEnvRef_shift henv_n
      have hdone_n : ListRel (ValueRefinesK n) (w₁ :: done₁) (w₂ :: done₂) := by
        refine ⟨valueRefinesK_mono (by omega) _ _ hw, ?_⟩
        exact listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) hdone
      have hπ_n : StackRefK ValueRefinesK n π₁ π₂ := stackRefK_mono (by omega) hπ
      have hih := ih hrest_closed
        (i := n) (done₁ := w₁ :: done₁) (done₂ := w₂ :: done₂)
        (π₁ := π₁) (π₂ := π₂) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (v₁ := v₁) hdone_n henv_n hπ_n
      exact Moist.Verified.FundamentalRefines.renameRefines_shift1 d t_a ha_closed n n
        (Nat.le_refl _) (ρ₁.extend v₁) ρ₂ henv_RL n (Nat.le_refl _) _ _ hih

private theorem lowerTotalExpr_constr_let {env : List VarId} (tag : Nat) (v : VarId)
    {rhs body : Expr} {pre post : List Expr}
    {t_rhs t_body : Term} {t_pre t_post : List Term}
    (h_rhs : lowerTotalExpr env rhs = some t_rhs)
    (h_body : lowerTotalExpr (v :: env) body = some t_body)
    (h_pre : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList pre) = some t_pre)
    (h_post : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList post) = some t_post) :
    lowerTotalExpr env (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post)) =
      some (.Constr tag (t_pre ++ [.Apply (.Lam 0 t_body) t_rhs] ++ t_post)) := by
  have h_rhs' : lowerTotal env (Moist.MIR.expandFix rhs) = some t_rhs := h_rhs
  have h_body' : lowerTotal (v :: env) (Moist.MIR.expandFix body) = some t_body := h_body
  -- The middle element after expansion: .Let [(v, expandFix rhs, false)] (expandFix body)
  -- Lowering it produces .Apply (.Lam 0 t_body) t_rhs
  have h_mid : lowerTotal env (Moist.MIR.expandFix (.Let [(v, rhs, false)] body)) =
      some (.Apply (.Lam 0 t_body) t_rhs) := by
    show lowerTotal env (Moist.MIR.expandFix (.Let [(v, rhs, false)] body)) =
      some (.Apply (.Lam 0 t_body) t_rhs)
    simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
               Moist.MIR.lowerTotalLet, Option.bind_eq_bind, Option.bind_some,
               h_rhs', h_body']
  -- expandFixList distributes over ++
  have hexpand : Moist.MIR.expandFixList (pre ++ [.Let [(v, rhs, false)] body] ++ post) =
      Moist.MIR.expandFixList pre ++ [Moist.MIR.expandFix (.Let [(v, rhs, false)] body)]
        ++ Moist.MIR.expandFixList post := by
    rw [expandFixList_append, expandFixList_append]
    simp [Moist.MIR.expandFixList]
  have h_list := lowerTotalList_append3 (Moist.MIR.expandFixList pre)
    (Moist.MIR.expandFix (.Let [(v, rhs, false)] body))
    (Moist.MIR.expandFixList post) h_pre h_mid h_post
  show lowerTotal env (Moist.MIR.expandFix
      (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post))) = _
  simp only [Moist.MIR.expandFix, Moist.MIR.lowerTotal, Option.bind_eq_bind]
  rw [hexpand, h_list]
  rfl

/-- Shape lemma: `.Let v rhs (.Constr tag (pre ++ [body] ++ post))` lowers to
    `.Apply (.Lam 0 (.Constr tag (shift t_pre ++ [t_body] ++ shift t_post))) t_rhs`. -/
private theorem lowerTotalExpr_let_constr {env : List VarId} (tag : Nat) (v : VarId)
    {rhs body : Expr} {pre post : List Expr}
    {t_rhs t_body : Term} {t_pre t_post : List Term}
    (hpre_fresh : ∀ a ∈ pre, (Moist.MIR.freeVars a).contains v = false)
    (hpost_fresh : ∀ a ∈ post, (Moist.MIR.freeVars a).contains v = false)
    (h_rhs : lowerTotalExpr env rhs = some t_rhs)
    (h_body : lowerTotalExpr (v :: env) body = some t_body)
    (h_pre : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList pre) = some t_pre)
    (h_post : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList post) = some t_post) :
    lowerTotalExpr env (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post))) =
      some (.Apply (.Lam 0 (.Constr tag
        (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_pre
          ++ [t_body] ++
          Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post))) t_rhs) := by
  have h_rhs' : lowerTotal env (Moist.MIR.expandFix rhs) = some t_rhs := h_rhs
  have h_body' : lowerTotal (v :: env) (Moist.MIR.expandFix body) = some t_body := h_body
  have hpre_fresh' : (Moist.MIR.freeVarsList (Moist.MIR.expandFixList pre)).contains v = false :=
    Moist.MIR.expandFixList_freeVars_not_contains pre v
      (freeVarsList_not_contains_of_forall v pre hpre_fresh)
  have hpost_fresh' : (Moist.MIR.freeVarsList (Moist.MIR.expandFixList post)).contains v = false :=
    Moist.MIR.expandFixList_freeVars_not_contains post v
      (freeVarsList_not_contains_of_forall v post hpost_fresh)
  have h_pre_shift :
      Moist.MIR.lowerTotalList (v :: env) (Moist.MIR.expandFixList pre) =
        some (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_pre) := by
    have h := Moist.MIR.lowerTotalList_prepend_unused_gen [] env v
      (Moist.MIR.expandFixList pre) (.inl hpre_fresh') t_pre h_pre
    simpa using h
  have h_post_shift :
      Moist.MIR.lowerTotalList (v :: env) (Moist.MIR.expandFixList post) =
        some (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post) := by
    have h := Moist.MIR.lowerTotalList_prepend_unused_gen [] env v
      (Moist.MIR.expandFixList post) (.inl hpost_fresh') t_post h_post
    simpa using h
  have h_body_list : Moist.MIR.lowerTotalList (v :: env) [Moist.MIR.expandFix body] =
      some [t_body] := by
    simp only [Moist.MIR.lowerTotalList, Option.bind_eq_bind]
    rw [h_body']
    rfl
  have hexpand :
      Moist.MIR.expandFixList (pre ++ [body] ++ post) =
        Moist.MIR.expandFixList pre ++ [Moist.MIR.expandFix body]
          ++ Moist.MIR.expandFixList post := by
    rw [expandFixList_append, expandFixList_append]
    simp [Moist.MIR.expandFixList]
  have h_inner_list :
      Moist.MIR.lowerTotalList (v :: env) (Moist.MIR.expandFixList (pre ++ [body] ++ post)) =
        some (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_pre
          ++ [t_body] ++
          Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post) := by
    rw [hexpand]
    exact lowerTotalList_append3 _ _ _ h_pre_shift h_body' h_post_shift
  show lowerTotal env (Moist.MIR.expandFix
      (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post)))) = _
  simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
             Moist.MIR.lowerTotalLet, Option.bind_eq_bind, Option.bind_some, h_rhs']
  rw [h_inner_list]
  rfl

/-! ### General-`pre` let-hoist-constr-arg -/

/-- If `lowerTotalList env xs = none`, then `lowerTotalList env (xs ++ ys) = none`. -/
private theorem lowerTotalList_append_none_left {env : List VarId}
    (xs ys : List Expr)
    (h : Moist.MIR.lowerTotalList env xs = none) :
    Moist.MIR.lowerTotalList env (xs ++ ys) = none := by
  induction xs with
  | nil => exact absurd h (by simp [Moist.MIR.lowerTotalList])
  | cons x xs' ih =>
    simp only [Moist.MIR.lowerTotalList, Option.bind_eq_bind] at h
    show Moist.MIR.lowerTotalList env (x :: (xs' ++ ys)) = none
    simp only [Moist.MIR.lowerTotalList, Option.bind_eq_bind]
    cases hx : Moist.MIR.lowerTotal env x with
    | none => simp
    | some t_x =>
      rw [hx] at h
      simp only [Option.bind_some] at h
      have hxs_none : Moist.MIR.lowerTotalList env xs' = none := by
        cases hxs : Moist.MIR.lowerTotalList env xs' with
        | none => rfl
        | some _ => rw [hxs] at h; simp at h
      have hrec := ih hxs_none
      simp [hrec]

/-- If `lowerTotalList env xs = some ts_x` and `lowerTotalList env ys = none`,
    then `lowerTotalList env (xs ++ ys) = none`. -/
private theorem lowerTotalList_append_none_right {env : List VarId}
    (xs ys : List Expr) {ts_x : List Term}
    (hxs : Moist.MIR.lowerTotalList env xs = some ts_x)
    (hys : Moist.MIR.lowerTotalList env ys = none) :
    Moist.MIR.lowerTotalList env (xs ++ ys) = none := by
  induction xs generalizing ts_x with
  | nil => simpa using hys
  | cons x xs' ih =>
    simp only [Moist.MIR.lowerTotalList, Option.bind_eq_bind] at hxs
    cases hx : Moist.MIR.lowerTotal env x with
    | none => rw [hx] at hxs; simp at hxs
    | some t_x =>
      rw [hx] at hxs
      simp only [Option.bind_some] at hxs
      cases hxs' : Moist.MIR.lowerTotalList env xs' with
      | none => rw [hxs'] at hxs; simp at hxs
      | some ts_x' =>
        have h_rec := ih hxs'
        show Moist.MIR.lowerTotalList env (x :: (xs' ++ ys)) = none
        simp only [Moist.MIR.lowerTotalList, Option.bind_eq_bind]
        simp [hx, h_rec]

/-- `isSome` iff lemma for `.Constr tag (pre ++ [.Let v rhs body] ++ post)`. -/
private theorem lowerTotalExpr_constr_let_isSome (env : List VarId) (tag : Nat)
    (pre : List Expr) (v : VarId) (rhs body : Expr) (post : List Expr) :
    (lowerTotalExpr env (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post))).isSome ↔
      (Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList pre)).isSome ∧
      (lowerTotalExpr env rhs).isSome ∧
      (lowerTotalExpr (v :: env) body).isSome ∧
      (Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList post)).isSome := by
  have hexpand : Moist.MIR.expandFixList (pre ++ [.Let [(v, rhs, false)] body] ++ post) =
      Moist.MIR.expandFixList pre ++ [Moist.MIR.expandFix (.Let [(v, rhs, false)] body)]
        ++ Moist.MIR.expandFixList post := by
    rw [expandFixList_append, expandFixList_append]
    simp [Moist.MIR.expandFixList]
  constructor
  · intro hsome
    have h : (lowerTotal env (Moist.MIR.expandFix
        (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post)))).isSome := hsome
    simp only [Moist.MIR.expandFix, Moist.MIR.lowerTotal, Option.bind_eq_bind] at h
    rw [hexpand] at h
    cases hp : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList pre) with
    | none =>
      have hfull : Moist.MIR.lowerTotalList env
          (Moist.MIR.expandFixList pre ++
            [Moist.MIR.expandFix (.Let [(v, rhs, false)] body)] ++
            Moist.MIR.expandFixList post) = none := by
        rw [List.append_assoc]
        exact lowerTotalList_append_none_left _ _ hp
      rw [hfull] at h; simp at h
    | some t_pre =>
      cases hr : Moist.MIR.lowerTotal env (Moist.MIR.expandFix rhs) with
      | none =>
        have hmid_none : Moist.MIR.lowerTotal env
            (Moist.MIR.expandFix (.Let [(v, rhs, false)] body)) = none := by
          simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
                     Moist.MIR.lowerTotalLet, Option.bind_eq_bind]
          rw [hr]; rfl
        have hmidsingle : Moist.MIR.lowerTotalList env
            [Moist.MIR.expandFix (.Let [(v, rhs, false)] body)] = none := by
          simp only [Moist.MIR.lowerTotalList, Option.bind_eq_bind]
          rw [hmid_none]; rfl
        have hmidplus : Moist.MIR.lowerTotalList env
            ([Moist.MIR.expandFix (.Let [(v, rhs, false)] body)] ++
              Moist.MIR.expandFixList post) = none :=
          lowerTotalList_append_none_left _ _ hmidsingle
        have hfull : Moist.MIR.lowerTotalList env
            (Moist.MIR.expandFixList pre ++
              [Moist.MIR.expandFix (.Let [(v, rhs, false)] body)] ++
              Moist.MIR.expandFixList post) = none := by
          rw [List.append_assoc]
          exact lowerTotalList_append_none_right _ _ hp hmidplus
        rw [hfull] at h; simp at h
      | some t_r =>
        cases hb : Moist.MIR.lowerTotal (v :: env) (Moist.MIR.expandFix body) with
        | none =>
          have hmid_none : Moist.MIR.lowerTotal env
              (Moist.MIR.expandFix (.Let [(v, rhs, false)] body)) = none := by
            simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
                       Moist.MIR.lowerTotalLet, Option.bind_eq_bind, hr, hb,
                       Option.bind_some, Option.bind_none]
          have hmidsingle : Moist.MIR.lowerTotalList env
              [Moist.MIR.expandFix (.Let [(v, rhs, false)] body)] = none := by
            simp only [Moist.MIR.lowerTotalList, Option.bind_eq_bind]
            rw [hmid_none]; rfl
          have hmidplus : Moist.MIR.lowerTotalList env
              ([Moist.MIR.expandFix (.Let [(v, rhs, false)] body)] ++
                Moist.MIR.expandFixList post) = none :=
            lowerTotalList_append_none_left _ _ hmidsingle
          have hfull : Moist.MIR.lowerTotalList env
              (Moist.MIR.expandFixList pre ++
                [Moist.MIR.expandFix (.Let [(v, rhs, false)] body)] ++
                Moist.MIR.expandFixList post) = none := by
            rw [List.append_assoc]
            exact lowerTotalList_append_none_right _ _ hp hmidplus
          rw [hfull] at h; simp at h
        | some t_b =>
          cases hpost : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList post) with
          | none =>
            have hmid_some : Moist.MIR.lowerTotal env
                (Moist.MIR.expandFix (.Let [(v, rhs, false)] body)) =
                  some (.Apply (.Lam 0 t_b) t_r) := by
              simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
                         Moist.MIR.lowerTotalLet, Option.bind_eq_bind]
              rw [hr]; simp only [Option.bind_some]; rw [hb]; rfl
            have hmidsingle : Moist.MIR.lowerTotalList env
                [Moist.MIR.expandFix (.Let [(v, rhs, false)] body)] =
                  some [.Apply (.Lam 0 t_b) t_r] := by
              simp only [Moist.MIR.lowerTotalList, Option.bind_eq_bind]
              rw [hmid_some]; rfl
            have hmidplus : Moist.MIR.lowerTotalList env
                ([Moist.MIR.expandFix (.Let [(v, rhs, false)] body)] ++
                  Moist.MIR.expandFixList post) = none :=
              lowerTotalList_append_none_right _ _ hmidsingle hpost
            have hfull : Moist.MIR.lowerTotalList env
                (Moist.MIR.expandFixList pre ++
                  [Moist.MIR.expandFix (.Let [(v, rhs, false)] body)] ++
                  Moist.MIR.expandFixList post) = none := by
              rw [List.append_assoc]
              exact lowerTotalList_append_none_right _ _ hp hmidplus
            rw [hfull] at h; simp at h
          | some t_post =>
            exact ⟨rfl, by show (lowerTotal env (Moist.MIR.expandFix rhs)).isSome = true;
                           rw [hr]; rfl,
                   by show (lowerTotal (v :: env) (Moist.MIR.expandFix body)).isSome = true;
                      rw [hb]; rfl, rfl⟩
  · rintro ⟨hp, hr, hb, hpost⟩
    cases hp' : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList pre) with
    | none => rw [hp'] at hp; exact absurd hp (by simp)
    | some t_pre =>
      cases hr' : lowerTotalExpr env rhs with
      | none => rw [hr'] at hr; exact absurd hr (by simp)
      | some t_r =>
        cases hb' : lowerTotalExpr (v :: env) body with
        | none => rw [hb'] at hb; exact absurd hb (by simp)
        | some t_b =>
          cases hpost' : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList post) with
          | none => rw [hpost'] at hpost; exact absurd hpost (by simp)
          | some t_post =>
            rw [lowerTotalExpr_constr_let tag v hr' hb' hp' hpost']
            rfl

/-- `isSome` iff for the let-constr form (general pre). -/
private theorem lowerTotalExpr_let_constr_isSome (env : List VarId) (tag : Nat)
    (pre : List Expr) (v : VarId) (rhs body : Expr) (post : List Expr)
    (hpre_fresh : ∀ a ∈ pre, (Moist.MIR.freeVars a).contains v = false)
    (hpost_fresh : ∀ a ∈ post, (Moist.MIR.freeVars a).contains v = false) :
    (lowerTotalExpr env (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post)))).isSome ↔
      (Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList pre)).isSome ∧
      (lowerTotalExpr env rhs).isSome ∧
      (lowerTotalExpr (v :: env) body).isSome ∧
      (Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList post)).isSome := by
  have hpre_fresh' : (Moist.MIR.freeVarsList (Moist.MIR.expandFixList pre)).contains v = false :=
    Moist.MIR.expandFixList_freeVars_not_contains pre v
      (freeVarsList_not_contains_of_forall v pre hpre_fresh)
  have hpost_fresh' : (Moist.MIR.freeVarsList (Moist.MIR.expandFixList post)).contains v = false :=
    Moist.MIR.expandFixList_freeVars_not_contains post v
      (freeVarsList_not_contains_of_forall v post hpost_fresh)
  have hexpand : Moist.MIR.expandFixList (pre ++ [body] ++ post) =
      Moist.MIR.expandFixList pre ++ [Moist.MIR.expandFix body]
        ++ Moist.MIR.expandFixList post := by
    rw [expandFixList_append, expandFixList_append]
    simp [Moist.MIR.expandFixList]
  constructor
  · intro hsome
    have h : (lowerTotal env (Moist.MIR.expandFix
        (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post))))).isSome := hsome
    have hexp_let : Moist.MIR.expandFix
        (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post))) =
        .Let [(v, Moist.MIR.expandFix rhs, false)]
          (.Constr tag (Moist.MIR.expandFixList (pre ++ [body] ++ post))) := by
      simp [Moist.MIR.expandFix, Moist.MIR.expandFixBinds]
    rw [hexp_let] at h
    simp only [Moist.MIR.lowerTotal, Moist.MIR.lowerTotalLet, Option.bind_eq_bind] at h
    cases hr : Moist.MIR.lowerTotal env (Moist.MIR.expandFix rhs) with
    | none => rw [hr] at h; simp at h
    | some t_r =>
      rw [hr] at h
      simp only [Option.bind_some] at h
      rw [hexpand] at h
      -- Case-split on extended lowerings
      cases hp_ext : Moist.MIR.lowerTotalList (v :: env) (Moist.MIR.expandFixList pre) with
      | none =>
        have : Moist.MIR.lowerTotalList (v :: env)
            (Moist.MIR.expandFixList pre ++
              [Moist.MIR.expandFix body] ++ Moist.MIR.expandFixList post) = none := by
          rw [List.append_assoc]
          exact lowerTotalList_append_none_left _ _ hp_ext
        rw [this] at h; simp at h
      | some t_pre_ext =>
        cases hbody_ext : Moist.MIR.lowerTotal (v :: env) (Moist.MIR.expandFix body) with
        | none =>
          have hmidsingle : Moist.MIR.lowerTotalList (v :: env)
              [Moist.MIR.expandFix body] = none := by
            simp only [Moist.MIR.lowerTotalList, Option.bind_eq_bind]
            rw [hbody_ext]; rfl
          have hmidplus : Moist.MIR.lowerTotalList (v :: env)
              ([Moist.MIR.expandFix body] ++ Moist.MIR.expandFixList post) = none :=
            lowerTotalList_append_none_left _ _ hmidsingle
          have : Moist.MIR.lowerTotalList (v :: env)
              (Moist.MIR.expandFixList pre ++
                [Moist.MIR.expandFix body] ++ Moist.MIR.expandFixList post) = none := by
            rw [List.append_assoc]
            exact lowerTotalList_append_none_right _ _ hp_ext hmidplus
          rw [this] at h; simp at h
        | some t_body =>
          cases hpost_ext : Moist.MIR.lowerTotalList (v :: env) (Moist.MIR.expandFixList post) with
          | none =>
            have hmidsingle : Moist.MIR.lowerTotalList (v :: env)
                [Moist.MIR.expandFix body] = some [t_body] := by
              simp only [Moist.MIR.lowerTotalList, Option.bind_eq_bind]
              rw [hbody_ext]; rfl
            have hmidplus : Moist.MIR.lowerTotalList (v :: env)
                ([Moist.MIR.expandFix body] ++ Moist.MIR.expandFixList post) = none :=
              lowerTotalList_append_none_right _ _ hmidsingle hpost_ext
            have : Moist.MIR.lowerTotalList (v :: env)
                (Moist.MIR.expandFixList pre ++
                  [Moist.MIR.expandFix body] ++ Moist.MIR.expandFixList post) = none := by
              rw [List.append_assoc]
              exact lowerTotalList_append_none_right _ _ hp_ext hmidplus
            rw [this] at h; simp at h
          | some t_post_ext =>
            -- Freshness lets us go back to env lowerings
            have hpre_base : (Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList pre)).isSome := by
              cases hb : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList pre) with
              | none =>
                have := Moist.MIR.lowerTotalList_prepend_unused_none_gen [] env v
                  (Moist.MIR.expandFixList pre) (.inl hpre_fresh') (by simpa using hb)
                have hext_none : Moist.MIR.lowerTotalList (v :: env)
                    (Moist.MIR.expandFixList pre) = none := by simpa using this
                rw [hext_none] at hp_ext; exact absurd hp_ext (by simp)
              | some _ => rfl
            have hpost_base : (Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList post)).isSome := by
              cases hb : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList post) with
              | none =>
                have := Moist.MIR.lowerTotalList_prepend_unused_none_gen [] env v
                  (Moist.MIR.expandFixList post) (.inl hpost_fresh') (by simpa using hb)
                have hext_none : Moist.MIR.lowerTotalList (v :: env)
                    (Moist.MIR.expandFixList post) = none := by simpa using this
                rw [hext_none] at hpost_ext; exact absurd hpost_ext (by simp)
              | some _ => rfl
            have hr' : lowerTotalExpr env rhs = some t_r := hr
            have hb' : lowerTotalExpr (v :: env) body = some t_body := hbody_ext
            refine ⟨hpre_base, ?_, ?_, hpost_base⟩
            · rw [hr']; rfl
            · rw [hb']; rfl
  · rintro ⟨hp, hr, hb, hpost⟩
    cases hp' : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList pre) with
    | none => rw [hp'] at hp; exact absurd hp (by simp)
    | some t_pre =>
      cases hr' : lowerTotalExpr env rhs with
      | none => rw [hr'] at hr; exact absurd hr (by simp)
      | some t_r =>
        cases hb' : lowerTotalExpr (v :: env) body with
        | none => rw [hb'] at hb; exact absurd hb (by simp)
        | some t_b =>
          cases hpost' : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList post) with
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
    ∀ {d : Nat}, Moist.Verified.closedAtList d t_pre = true →
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
      simp only [Moist.Verified.closedAtList, Bool.and_eq_true] at hpre_closed
      exact hpre_closed.1
    have hrest_closed : Moist.Verified.closedAtList d rest = true := by
      simp only [Moist.Verified.closedAtList, Bool.and_eq_true] at hpre_closed
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
        State.compute (.constrField tag [] t_post ρ :: π) ρ (.Apply (.Lam 0 t_b) t_r) := by rfl
    rw [h1]
    simpa using haux
  | cons a rest =>
    have h1 : steps 1 (State.compute π ρ
        (.Constr tag ((a :: rest) ++ [.Apply (.Lam 0 t_b) t_r] ++ t_post))) =
        State.compute (.constrField tag []
          (rest ++ [.Apply (.Lam 0 t_b) t_r] ++ t_post) ρ :: π) ρ a := by rfl
    rw [h1]
    simpa using haux

/-- Inside-hπ_aug RHS admin helper: after funV VLam (.Constr tag ...) fires with
    v_r₂, process the shifted pre atoms. Total steps: `2 + 2 * |t_pre|`. -/
private theorem steps_rhs_hpi_aug_fwd
    (tag : Nat) (t_b : Term) (t_post : List Term) :
    ∀ (t_pre : List Term) (ρ₂ : CekEnv) (v_r₂ : CekValue) (π₂ : Stack)
      (vs₂ : List CekValue),
      ListStepsFor (ρ₂.extend v_r₂) (Moist.Verified.renameTermList
        (Moist.Verified.shiftRename 1) t_pre) vs₂ →
      steps (2 + 2 * t_pre.length)
        (State.ret (.funV (.VLam (.Constr tag
          (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_pre ++ [t_b] ++
           Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post)) ρ₂) :: π₂) v_r₂) =
        State.compute (.constrField tag vs₂.reverse
          (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post)
          (ρ₂.extend v_r₂) :: π₂) (ρ₂.extend v_r₂) t_b := by
  intro t_pre ρ₂ v_r₂ π₂ vs₂ hstep
  -- 2 top-level admin steps: funV-pop (compute .Constr ...) then constr-push.
  have h_2 :
      steps 2 (State.ret (.funV (.VLam (.Constr tag
        (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_pre ++ [t_b] ++
         Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post)) ρ₂) :: π₂) v_r₂) =
        (match Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_pre with
          | [] => State.compute (.constrField tag []
              (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post)
              (ρ₂.extend v_r₂) :: π₂) (ρ₂.extend v_r₂) t_b
          | a :: rest => State.compute (.constrField tag []
              (rest ++ [t_b] ++ Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post)
              (ρ₂.extend v_r₂) :: π₂) (ρ₂.extend v_r₂) a) := by
    show Moist.CEK.step (Moist.CEK.step _) = _
    show Moist.CEK.step (State.compute π₂ (ρ₂.extend v_r₂)
      (.Constr tag (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_pre ++
        [t_b] ++ Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post))) = _
    cases Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_pre with
    | nil => rfl
    | cons b rest' => rfl
  show steps (2 + 2 * t_pre.length) _ = _
  rw [steps_trans, h_2]
  -- Now apply the inside-cF helper-like reasoning, but without the .Apply middle.
  -- Use steps_rhs_cf_atoms_fwd (we'll define this for just atom processing).
  -- We reuse: we have t_pre_shifted = Moist.Verified.renameTermList ... t_pre
  -- Processing each atom takes 2 steps.
  -- Total additional: 2 * t_pre.length.
  -- Let's use a simpler helper: just iterate through atoms with no middle term.
  have haux : ∀ (t_pre_left : List Term) (done : List CekValue) (vs_left : List CekValue),
      ListStepsFor (ρ₂.extend v_r₂) t_pre_left vs_left →
      steps (2 * t_pre_left.length)
        (match t_pre_left with
          | [] => State.compute (.constrField tag done
              (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post)
              (ρ₂.extend v_r₂) :: π₂) (ρ₂.extend v_r₂) t_b
          | a :: rest => State.compute (.constrField tag done
              (rest ++ [t_b] ++ Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post)
              (ρ₂.extend v_r₂) :: π₂) (ρ₂.extend v_r₂) a) =
        State.compute (.constrField tag (vs_left.reverse ++ done)
          (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post)
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
                (rest ++ [t_b] ++ Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post)
                (ρ₂.extend v_r₂) :: π₂) (ρ₂.extend v_r₂) a) =
              (match rest with
                | [] => State.compute (.constrField tag (v :: done)
                    (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post)
                    (ρ₂.extend v_r₂) :: π₂) (ρ₂.extend v_r₂) t_b
                | b :: rest' => State.compute (.constrField tag (v :: done)
                    (rest' ++ [t_b] ++ Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post)
                    (ρ₂.extend v_r₂) :: π₂) (ρ₂.extend v_r₂) b) := by
          show Moist.CEK.step (Moist.CEK.step _) = _
          have ha_step := hstep_a (.constrField tag done
            (rest ++ [t_b] ++ Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post)
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
      (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) ts).length = ts.length := by
    intro ts
    induction ts with
    | nil => rfl
    | cons t rest ih =>
      show ((Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t ::
        Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) rest)).length = _
      rw [List.length_cons, List.length_cons, ih]
  rw [← hlen_shift t_pre]
  cases hpre : Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_pre with
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
    {d : Nat} (hpre_closed : Moist.Verified.closedAtList d t_pre = true)
    {ρ : CekEnv} {vs : List CekValue} (v_inner : CekValue)
    (hstep : ListStepsFor ρ t_pre vs) :
    ListStepsFor (ρ.extend v_inner)
      (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_pre) vs := by
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
        simp only [Moist.Verified.closedAtList, Bool.and_eq_true] at hpre_closed
        exact hpre_closed.1
      have hrest_closed : Moist.Verified.closedAtList d rest = true := by
        simp only [Moist.Verified.closedAtList, Bool.and_eq_true] at hpre_closed
        exact hpre_closed.2
      show ListStepsFor (ρ.extend v_inner)
        (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t ::
         Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) rest) (v :: vs_rest)
      refine ⟨?_, ih hrest_leaf hrest_closed hstep_rest⟩
      intro π
      have hempty : Moist.CEK.step (.compute [] ρ t) = .ret [] v := hstep_t []
      exact leafAtom_shift_step ht_leaf ht_closed v_inner v hempty π

/-- **MIRRefines for let-hoist-constr-arg (forward, general `pre` case)**. -/
theorem mirRefines_let_hoist_constr_arg_fwd (tag : Nat) (pre : List Expr)
    (v : VarId) (rhs body : Expr) (post : List Expr)
    (hpre_atom : ∀ a ∈ pre, a.isAtom = true)
    (hpre_fresh : ∀ a ∈ pre, (Moist.MIR.freeVars a).contains v = false)
    (hpost_fresh : ∀ a ∈ post, (Moist.MIR.freeVars a).contains v = false) :
    MIRRefines (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post))
               (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post))) := by
  refine ⟨?_, ?_⟩
  · intro env hsome
    have h := (lowerTotalExpr_constr_let_isSome env tag pre v rhs body post).mp hsome
    exact (lowerTotalExpr_let_constr_isSome env tag pre v rhs body post hpre_fresh hpost_fresh).mpr h
  · intro d k env hlen
    cases hp : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList pre) with
    | none =>
      have h_lhs : lowerTotalExpr env (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post)) = none := by
        cases h : lowerTotalExpr env (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post)) with
        | none => rfl
        | some _ =>
          have hsome : (lowerTotalExpr env (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post))).isSome := by
            rw [h]; rfl
          have := (lowerTotalExpr_constr_let_isSome env tag pre v rhs body post).mp hsome
          rw [hp] at this; exact absurd this.1 (by simp)
      rw [h_lhs]; trivial
    | some t_pre =>
      cases hr : lowerTotalExpr env rhs with
      | none =>
        have h_lhs : lowerTotalExpr env (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post)) = none := by
          cases h : lowerTotalExpr env (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post)) with
          | none => rfl
          | some _ =>
            have hsome : (lowerTotalExpr env (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post))).isSome := by
              rw [h]; rfl
            have := (lowerTotalExpr_constr_let_isSome env tag pre v rhs body post).mp hsome
            rw [hr] at this; exact absurd this.2.1 (by simp)
        rw [h_lhs]; trivial
      | some t_r =>
        cases hb : lowerTotalExpr (v :: env) body with
        | none =>
          have h_lhs : lowerTotalExpr env (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post)) = none := by
            cases h : lowerTotalExpr env (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post)) with
            | none => rfl
            | some _ =>
              have hsome : (lowerTotalExpr env (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post))).isSome := by
                rw [h]; rfl
              have := (lowerTotalExpr_constr_let_isSome env tag pre v rhs body post).mp hsome
              rw [hb] at this; exact absurd this.2.2.1 (by simp)
          rw [h_lhs]; trivial
        | some t_b =>
          cases hpost : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList post) with
          | none =>
            have h_lhs : lowerTotalExpr env (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post)) = none := by
              cases h : lowerTotalExpr env (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post)) with
              | none => rfl
              | some _ =>
                have hsome : (lowerTotalExpr env (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post))).isSome := by
                  rw [h]; rfl
                have := (lowerTotalExpr_constr_let_isSome env tag pre v rhs body post).mp hsome
                rw [hpost] at this; exact absurd this.2.2.2 (by simp)
            rw [h_lhs]; trivial
          | some t_post =>
            rw [lowerTotalExpr_constr_let tag v hr hb hp hpost]
            rw [lowerTotalExpr_let_constr tag v hpre_fresh hpost_fresh hr hb hp hpost]
            simp only
            intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
            -- Get closedness hypotheses
            have hclosed_r : closedAt env.length t_r :=
              Moist.Verified.MIR.lowerTotal_closedAt env _ t_r hr
            have hclosed_b : closedAt (env.length + 1) t_b := by
              have := Moist.Verified.MIR.lowerTotal_closedAt (v :: env) _ t_b hb
              simpa [List.length_cons] using this
            have hclosed_pre : Moist.Verified.closedAtList env.length t_pre :=
              Moist.Verified.MIR.lowerTotalList_closedAtList env _ t_pre hp
            have hclosed_post : Moist.Verified.closedAtList env.length t_post :=
              Moist.Verified.MIR.lowerTotalList_closedAtList env _ t_post hpost
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
                    (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_pre ++ [t_b] ++
                     Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post))) t_r)) =
                  State.compute (.funV (.VLam (.Constr tag
                    (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_pre ++ [t_b] ++
                     Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post)) ρ₂) :: π₂)
                    ρ₂ t_r := by rfl
            apply obsRefinesK_of_steps_left h_steps_lhs
            apply obsRefinesK_of_steps_right h_steps_rhs
            -- Now both sides are computing t_r with augmented stacks.
            -- Build the augmented stack relation.
            have hπ_aug : StackRefK ValueRefinesK i
                (.funV (.VLam t_b ρ₁) :: .constrField tag vs₁.reverse t_post ρ₁ :: π₁)
                (.funV (.VLam (.Constr tag
                  (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_pre ++ [t_b] ++
                   Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post)) ρ₂) :: π₂) := by
              intro j' hj' v₁' v₂' hv'
              -- LHS: 1 step (pop funV, compute t_b in extended env)
              have h_lhs_inner :
                  steps 1 (State.ret (.funV (.VLam t_b ρ₁) ::
                    .constrField tag vs₁.reverse t_post ρ₁ :: π₁) v₁') =
                    State.compute (.constrField tag vs₁.reverse t_post ρ₁ :: π₁)
                      (ρ₁.extend v₁') t_b := by rfl
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
                Moist.Verified.Equivalence.listRel_reverse hvs_rel'
              have hπ_cf : StackRefK ValueRefinesK j'
                  (.constrField tag vs₁.reverse t_post ρ₁ :: π₁)
                  (.constrField tag vs₂'.reverse
                    (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post)
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
      ListStepsFor (ρ₁.extend v_r₁) (Moist.Verified.renameTermList
        (Moist.Verified.shiftRename 1) t_pre) vs₁ →
      steps (2 + 2 * t_pre.length)
        (State.ret (.funV (.VLam (.Constr tag
          (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_pre ++ [t_b] ++
           Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post)) ρ₁) :: π₁) v_r₁) =
        State.compute (.constrField tag vs₁.reverse
          (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post)
          (ρ₁.extend v_r₁) :: π₁) (ρ₁.extend v_r₁) t_b :=
  steps_rhs_hpi_aug_fwd tag t_b t_post

/-- **MIRRefines for let-hoist-constr-arg (backward, general `pre` case)**. -/
theorem mirRefines_let_hoist_constr_arg_bwd (tag : Nat) (pre : List Expr)
    (v : VarId) (rhs body : Expr) (post : List Expr)
    (hpre_atom : ∀ a ∈ pre, a.isAtom = true)
    (hpre_fresh : ∀ a ∈ pre, (Moist.MIR.freeVars a).contains v = false)
    (hpost_fresh : ∀ a ∈ post, (Moist.MIR.freeVars a).contains v = false) :
    MIRRefines (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post)))
               (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post)) := by
  refine ⟨?_, ?_⟩
  · intro env hsome
    have h := (lowerTotalExpr_let_constr_isSome env tag pre v rhs body post hpre_fresh hpost_fresh).mp hsome
    exact (lowerTotalExpr_constr_let_isSome env tag pre v rhs body post).mpr h
  · intro d k env hlen
    cases hp : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList pre) with
    | none =>
      have h_lhs : lowerTotalExpr env (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post))) = none := by
        cases h : lowerTotalExpr env (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post))) with
        | none => rfl
        | some _ =>
          have hsome : (lowerTotalExpr env (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post)))).isSome := by
            rw [h]; rfl
          have := (lowerTotalExpr_let_constr_isSome env tag pre v rhs body post hpre_fresh hpost_fresh).mp hsome
          rw [hp] at this; exact absurd this.1 (by simp)
      rw [h_lhs]; trivial
    | some t_pre =>
      cases hr : lowerTotalExpr env rhs with
      | none =>
        have h_lhs : lowerTotalExpr env (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post))) = none := by
          cases h : lowerTotalExpr env (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post))) with
          | none => rfl
          | some _ =>
            have hsome : (lowerTotalExpr env (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post)))).isSome := by
              rw [h]; rfl
            have := (lowerTotalExpr_let_constr_isSome env tag pre v rhs body post hpre_fresh hpost_fresh).mp hsome
            rw [hr] at this; exact absurd this.2.1 (by simp)
        rw [h_lhs]; trivial
      | some t_r =>
        cases hb : lowerTotalExpr (v :: env) body with
        | none =>
          have h_lhs : lowerTotalExpr env (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post))) = none := by
            cases h : lowerTotalExpr env (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post))) with
            | none => rfl
            | some _ =>
              have hsome : (lowerTotalExpr env (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post)))).isSome := by
                rw [h]; rfl
              have := (lowerTotalExpr_let_constr_isSome env tag pre v rhs body post hpre_fresh hpost_fresh).mp hsome
              rw [hb] at this; exact absurd this.2.2.1 (by simp)
          rw [h_lhs]; trivial
        | some t_b =>
          cases hpost : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList post) with
          | none =>
            have h_lhs : lowerTotalExpr env (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post))) = none := by
              cases h : lowerTotalExpr env (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post))) with
              | none => rfl
              | some _ =>
                have hsome : (lowerTotalExpr env (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post)))).isSome := by
                  rw [h]; rfl
                have := (lowerTotalExpr_let_constr_isSome env tag pre v rhs body post hpre_fresh hpost_fresh).mp hsome
                rw [hpost] at this; exact absurd this.2.2.2 (by simp)
            rw [h_lhs]; trivial
          | some t_post =>
            rw [lowerTotalExpr_let_constr tag v hpre_fresh hpost_fresh hr hb hp hpost]
            rw [lowerTotalExpr_constr_let tag v hr hb hp hpost]
            simp only
            intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
            have hclosed_r : closedAt env.length t_r :=
              Moist.Verified.MIR.lowerTotal_closedAt env _ t_r hr
            have hclosed_b : closedAt (env.length + 1) t_b := by
              have := Moist.Verified.MIR.lowerTotal_closedAt (v :: env) _ t_b hb
              simpa [List.length_cons] using this
            have hclosed_pre : Moist.Verified.closedAtList env.length t_pre :=
              Moist.Verified.MIR.lowerTotalList_closedAtList env _ t_pre hp
            have hclosed_post : Moist.Verified.closedAtList env.length t_post :=
              Moist.Verified.MIR.lowerTotalList_closedAtList env _ t_post hpost
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
                    (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_pre ++ [t_b] ++
                     Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post))) t_r)) =
                  State.compute (.funV (.VLam (.Constr tag
                    (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_pre ++ [t_b] ++
                     Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post)) ρ₁) :: π₁)
                    ρ₁ t_r := by rfl
            -- Advance RHS admin: 1 + 2 * |t_pre| + 3 steps
            have h_steps_rhs := steps_rhs_constr_apply_lam_bwd tag t_b t_r
              t_pre t_post ρ₂ π₂ vs₂ hstep_list₂
            apply obsRefinesK_of_steps_left h_steps_lhs
            apply obsRefinesK_of_steps_right h_steps_rhs
            -- Build the augmented stack relation
            have hπ_aug : StackRefK ValueRefinesK i
                (.funV (.VLam (.Constr tag
                  (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_pre ++ [t_b] ++
                   Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post)) ρ₁) :: π₁)
                (.funV (.VLam t_b ρ₂) :: .constrField tag vs₂.reverse t_post ρ₂ :: π₂) := by
              intro j' hj' v₁' v₂' hv'
              -- RHS: 1 step (pop funV, compute t_b in extended env)
              have h_rhs_inner :
                  steps 1 (State.ret (.funV (.VLam t_b ρ₂) ::
                    .constrField tag vs₂.reverse t_post ρ₂ :: π₂) v₂') =
                    State.compute (.constrField tag vs₂.reverse t_post ρ₂ :: π₂)
                      (ρ₂.extend v₂') t_b := by rfl
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
                Moist.Verified.Equivalence.listRel_reverse hvs_rel'
              have hπ_cf : StackRefK ValueRefinesK j'
                  (.constrField tag vs₁'.reverse
                    (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post)
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
    (hpre_fresh : ∀ a ∈ pre, (Moist.MIR.freeVars a).contains v = false)
    (hpost_fresh : ∀ a ∈ post, (Moist.MIR.freeVars a).contains v = false) :
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
  cases hp : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList pre) with
  | none => rw [hp] at hp_some; exact absurd hp_some (by simp)
  | some t_pre =>
    cases hr : lowerTotalExpr env rhs with
    | none => rw [hr] at hr_some; exact absurd hr_some (by simp)
    | some t_r =>
      cases hb : lowerTotalExpr (v :: env) body with
      | none => rw [hb] at hb_some; exact absurd hb_some (by simp)
      | some t_b =>
        cases hpost : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList post) with
        | none => rw [hpost] at hpost_some; exact absurd hpost_some (by simp)
        | some t_post =>
          rw [lowerTotalExpr_constr_let tag v hr hb hp hpost] at h₁
          rw [lowerTotalExpr_let_constr tag v hpre_fresh hpost_fresh hr hb hp hpost] at h₂
          injection h₁ with h₁; subst h₁
          injection h₂ with h₂; subst h₂
          -- LHS closedness structure:
          --   closedAt k (.Constr tag (t_pre ++ [.Apply (.Lam 0 t_b) t_r] ++ t_post))
          -- = closedAtList k (t_pre ++ [.Apply (.Lam 0 t_b) t_r] ++ t_post)
          -- which expands via two appends.
          have hpre_c : Moist.Verified.closedAtList k t_pre = true := by
            have h := hc
            simp only [closedAt] at h
            have := ((Moist.Verified.Contextual.closedAtList_append k
              (t_pre ++ [.Apply (.Lam 0 t_b) t_r]) t_post).mp h).1
            exact ((Moist.Verified.Contextual.closedAtList_append k
              t_pre [.Apply (.Lam 0 t_b) t_r]).mp this).1
          have hmid_c : closedAt k (.Apply (.Lam 0 t_b) t_r) = true := by
            have h := hc
            simp only [closedAt] at h
            have := ((Moist.Verified.Contextual.closedAtList_append k
              (t_pre ++ [.Apply (.Lam 0 t_b) t_r]) t_post).mp h).1
            have := ((Moist.Verified.Contextual.closedAtList_append k
              t_pre [.Apply (.Lam 0 t_b) t_r]).mp this).2
            simp only [Moist.Verified.closedAtList, Bool.and_eq_true] at this
            exact this.1
          have hpost_c : Moist.Verified.closedAtList k t_post = true := by
            have h := hc
            simp only [closedAt] at h
            exact ((Moist.Verified.Contextual.closedAtList_append k
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
          have hpre_sh : Moist.Verified.closedAtList (k + 1)
              (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_pre) = true := by
            by_cases hk : k = 0
            · subst hk
              exact closedAtList_renameTermList_shiftRename t_pre 0 1 (by omega) (by omega) hpre_c
            · have hkp : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk
              exact closedAtList_renameTermList_shiftRename t_pre k 1 (by omega) (by omega) hpre_c
          have hpost_sh : Moist.Verified.closedAtList (k + 1)
              (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post) = true := by
            by_cases hk : k = 0
            · subst hk
              exact closedAtList_renameTermList_shiftRename t_post 0 1 (by omega) (by omega) hpost_c
            · have hkp : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk
              exact closedAtList_renameTermList_shiftRename t_post k 1 (by omega) (by omega) hpost_c
          show closedAt k (.Apply (.Lam 0 (.Constr tag _)) t_r) = true
          have hmid_list : Moist.Verified.closedAtList (k + 1)
              [t_b] = true := by
            simp only [Moist.Verified.closedAtList, Bool.and_eq_true]
            exact ⟨hb_c, trivial⟩
          have h_step1 : Moist.Verified.closedAtList (k + 1)
              (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_pre ++ [t_b]) = true :=
            (Moist.Verified.Contextual.closedAtList_append (k + 1) _ _).mpr ⟨hpre_sh, hmid_list⟩
          have h_full : Moist.Verified.closedAtList (k + 1)
              (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_pre ++ [t_b] ++
               Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post) = true :=
            (Moist.Verified.Contextual.closedAtList_append (k + 1) _ _).mpr ⟨h_step1, hpost_sh⟩
          simp only [closedAt, Bool.and_eq_true]
          exact ⟨h_full, hr_c⟩

/-- Closedness preservation (backward). -/
private theorem let_hoist_constr_arg_close_pres_bwd (tag : Nat) (pre : List Expr)
    (v : VarId) (rhs body : Expr) (post : List Expr)
    (_hpre_atom : ∀ a ∈ pre, a.isAtom = true)
    (hpre_fresh : ∀ a ∈ pre, (Moist.MIR.freeVars a).contains v = false)
    (hpost_fresh : ∀ a ∈ post, (Moist.MIR.freeVars a).contains v = false) :
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
  cases hp : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList pre) with
  | none => rw [hp] at hp_some; exact absurd hp_some (by simp)
  | some t_pre =>
    cases hr : lowerTotalExpr env rhs with
    | none => rw [hr] at hr_some; exact absurd hr_some (by simp)
    | some t_r =>
      cases hb : lowerTotalExpr (v :: env) body with
      | none => rw [hb] at hb_some; exact absurd hb_some (by simp)
      | some t_b =>
        cases hpost : Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList post) with
        | none => rw [hpost] at hpost_some; exact absurd hpost_some (by simp)
        | some t_post =>
          rw [lowerTotalExpr_let_constr tag v hpre_fresh hpost_fresh hr hb hp hpost] at h₁
          rw [lowerTotalExpr_constr_let tag v hr hb hp hpost] at h₂
          injection h₁ with h₁; subst h₁
          injection h₂ with h₂; subst h₂
          -- LHS: closedAt k (.Apply (.Lam 0 (.Constr tag (shift t_pre ++ [t_b] ++ shift t_post))) t_r)
          have hr_c : closedAt k t_r := by
            have h := hc
            simp only [closedAt, Bool.and_eq_true] at h
            exact h.2
          have hinner_list : Moist.Verified.closedAtList (k + 1)
              (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_pre ++ [t_b] ++
               Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) t_post) = true := by
            have h := hc
            simp only [closedAt, Bool.and_eq_true] at h
            exact h.1
          have hpre_sh_c := ((Moist.Verified.Contextual.closedAtList_append (k + 1) _ _).mp
            ((Moist.Verified.Contextual.closedAtList_append (k + 1) _ _).mp hinner_list).1).1
          have hbsingle_c := ((Moist.Verified.Contextual.closedAtList_append (k + 1) _ _).mp
            ((Moist.Verified.Contextual.closedAtList_append (k + 1) _ _).mp hinner_list).1).2
          have hpost_sh_c := ((Moist.Verified.Contextual.closedAtList_append (k + 1) _ _).mp hinner_list).2
          have hb_c : closedAt (k + 1) t_b := by
            simp only [Moist.Verified.closedAtList, Bool.and_eq_true] at hbsingle_c
            exact hbsingle_c.1
          have hpre_c : Moist.Verified.closedAtList k t_pre = true := by
            by_cases hk : k = 0
            · subst hk
              exact closedAtList_renameTermList_shiftRename_inv t_pre 0 1 (by omega) (by omega) hpre_sh_c
            · have hkp : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk
              exact closedAtList_renameTermList_shiftRename_inv t_pre k 1 (by omega) (by omega) hpre_sh_c
          have hpost_c : Moist.Verified.closedAtList k t_post = true := by
            by_cases hk : k = 0
            · subst hk
              exact closedAtList_renameTermList_shiftRename_inv t_post 0 1 (by omega) (by omega) hpost_sh_c
            · have hkp : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk
              exact closedAtList_renameTermList_shiftRename_inv t_post k 1 (by omega) (by omega) hpost_sh_c
          -- Goal: closedAt k (.Constr tag (t_pre ++ [.Apply (.Lam 0 t_b) t_r] ++ t_post))
          show closedAt k (.Constr tag _) = true
          simp only [closedAt]
          have hmid_list : Moist.Verified.closedAtList k
              [.Apply (.Lam 0 t_b) t_r] = true := by
            simp only [Moist.Verified.closedAtList, closedAt, Bool.and_eq_true]
            exact ⟨⟨hb_c, hr_c⟩, trivial⟩
          have h_step1 : Moist.Verified.closedAtList k
              (t_pre ++ [.Apply (.Lam 0 t_b) t_r]) = true :=
            (Moist.Verified.Contextual.closedAtList_append k _ _).mpr ⟨hpre_c, hmid_list⟩
          exact (Moist.Verified.Contextual.closedAtList_append k _ _).mpr ⟨h_step1, hpost_c⟩

theorem mirCtxRefines_let_hoist_constr_arg_fwd (tag : Nat) (pre : List Expr)
    (v : VarId) (rhs body : Expr) (post : List Expr)
    (hpre_atom : ∀ a ∈ pre, a.isAtom = true)
    (hpre_fresh : ∀ a ∈ pre, (Moist.MIR.freeVars a).contains v = false)
    (hpost_fresh : ∀ a ∈ post, (Moist.MIR.freeVars a).contains v = false) :
    MIRCtxRefines (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post))
                  (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post))) :=
  mirRefines_to_mirCtxRefines
    (mirRefines_let_hoist_constr_arg_fwd tag pre v rhs body post hpre_atom hpre_fresh hpost_fresh)
    (let_hoist_constr_arg_close_pres_fwd tag pre v rhs body post hpre_atom hpre_fresh hpost_fresh)

theorem mirCtxRefines_let_hoist_constr_arg_bwd (tag : Nat) (pre : List Expr)
    (v : VarId) (rhs body : Expr) (post : List Expr)
    (hpre_atom : ∀ a ∈ pre, a.isAtom = true)
    (hpre_fresh : ∀ a ∈ pre, (Moist.MIR.freeVars a).contains v = false)
    (hpost_fresh : ∀ a ∈ post, (Moist.MIR.freeVars a).contains v = false) :
    MIRCtxRefines (.Let [(v, rhs, false)] (.Constr tag (pre ++ [body] ++ post)))
                  (.Constr tag (pre ++ [.Let [(v, rhs, false)] body] ++ post)) :=
  mirRefines_to_mirCtxRefines
    (mirRefines_let_hoist_constr_arg_bwd tag pre v rhs body post hpre_atom hpre_fresh hpost_fresh)
    (let_hoist_constr_arg_close_pres_bwd tag pre v rhs body post hpre_atom hpre_fresh hpost_fresh)



/-- A helper: `.Let [] body` is equivalent to `body` under MIRCtxRefines. -/
theorem mirCtxRefines_let_nil_body (body : Expr) :
    MIRCtxRefines (.Let [] body) body := by
  intro env
  have heq : lowerTotalExpr env (.Let [] body) = lowerTotalExpr env body := by
    show lowerTotal env (Moist.MIR.expandFix (.Let [] body)) =
      lowerTotal env (Moist.MIR.expandFix body)
    simp [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
          Moist.MIR.lowerTotalLet]
  refine ⟨?_, ?_⟩
  · intro hsome; rw [heq] at hsome; exact hsome
  · rw [heq]
    cases h : lowerTotalExpr env body with
    | none => trivial
    | some t => exact ctxRefines_refl t

theorem mirCtxRefines_let_nil_body_bwd (body : Expr) :
    MIRCtxRefines body (.Let [] body) := by
  intro env
  have heq : lowerTotalExpr env (.Let [] body) = lowerTotalExpr env body := by
    show lowerTotal env (Moist.MIR.expandFix (.Let [] body)) =
      lowerTotal env (Moist.MIR.expandFix body)
    simp [Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
          Moist.MIR.lowerTotalLet]
  refine ⟨?_, ?_⟩
  · intro hsome; rw [← heq] at hsome; exact hsome
  · rw [← heq]
    cases h : lowerTotalExpr env (.Let [] body) with
    | none => trivial
    | some t => exact ctxRefines_refl t

/-! ### Section 12b-bis. Single-binding `er`-flag normalization

The `er` flag in `.Let` bindings is dropped at the lowering level (see
`lowerTotalLet`), so it doesn't affect `MIRCtxRefines`. For single-binding
`.Let [(v, rhs, er)] body`, this is easy to prove: both sides lower
identically. -/

theorem mirCtxRefines_let_cons_er_normalize_fwd
    (v : VarId) (rhs : Expr) (er : Bool) (rest : List (VarId × Expr × Bool)) (body : Expr) :
    MIRCtxRefines (.Let ((v, rhs, er) :: rest) body) (.Let ((v, rhs, false) :: rest) body) := by
  intro env
  have heq : lowerTotalExpr env (.Let ((v, rhs, er) :: rest) body) =
             lowerTotalExpr env (.Let ((v, rhs, false) :: rest) body) := by
    show lowerTotal env (Moist.MIR.expandFix _) =
      lowerTotal env (Moist.MIR.expandFix _)
    simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds,
      Moist.MIR.lowerTotal, Moist.MIR.lowerTotalLet]
  rw [heq]
  refine ⟨id, ?_⟩
  cases h : lowerTotalExpr env (.Let ((v, rhs, false) :: rest) body) with
  | none => trivial
  | some t => exact ctxRefines_refl t

theorem mirCtxRefines_let_cons_er_normalize_bwd
    (v : VarId) (rhs : Expr) (er : Bool) (rest : List (VarId × Expr × Bool)) (body : Expr) :
    MIRCtxRefines (.Let ((v, rhs, false) :: rest) body) (.Let ((v, rhs, er) :: rest) body) := by
  intro env
  have heq : lowerTotalExpr env (.Let ((v, rhs, er) :: rest) body) =
             lowerTotalExpr env (.Let ((v, rhs, false) :: rest) body) := by
    show lowerTotal env (Moist.MIR.expandFix _) =
      lowerTotal env (Moist.MIR.expandFix _)
    simp only [Moist.MIR.expandFix, Moist.MIR.expandFixBinds,
      Moist.MIR.lowerTotal, Moist.MIR.lowerTotalLet]
  rw [← heq]
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
    MIRCtxRefines (Moist.MIR.wrapLet binds body) (.Let binds body) := by
  cases binds with
  | nil =>
    show MIRCtxRefines body (.Let [] body)
    exact mirCtxRefines_let_nil_body_bwd body
  | cons b rest =>
    rw [wrapLet_cons]
    exact mirCtxRefines_refl _

theorem mirCtxRefines_wrapLet_eq_bwd (binds : List (VarId × Expr × Bool))
    (body : Expr) :
    MIRCtxRefines (.Let binds body) (Moist.MIR.wrapLet binds body) := by
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
      (∀ b ∈ binds, (Moist.MIR.freeVars xArg).contains b.1 = false) →
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
      (∀ b ∈ binds, (Moist.MIR.freeVars xArg).contains b.1 = false) →
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
      (∀ b ∈ binds, (Moist.MIR.freeVars g).contains b.1 = false) →
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
      (∀ b ∈ binds, (Moist.MIR.freeVars g).contains b.1 = false) →
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
    simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.expandFixBinds,
      Moist.MIR.lowerTotal, Moist.MIR.lowerTotalLet]
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
    simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.expandFixBinds,
      Moist.MIR.lowerTotal, Moist.MIR.lowerTotalLet]
  rw [← h]
  refine ⟨id, ?_⟩
  cases hl : lowerTotalExpr env (.Case (.Let [] body) alts) with
  | none => trivial
  | some t => exact ctxRefines_refl t

/-- Iterated Case-scrutinee hoist (forward). -/
theorem mirCtxRefines_let_hoist_case_scrut_iter_fwd :
    ∀ (binds : List (VarId × Expr × Bool)) (body : Expr) (alts : List Expr),
      (∀ b ∈ binds, (Moist.MIR.freeVarsList alts).contains b.1 = false) →
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
      (∀ b ∈ binds, (Moist.MIR.freeVarsList alts).contains b.1 = false) →
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
      (∀ a ∈ pre, ∀ b ∈ binds, (Moist.MIR.freeVars a).contains b.1 = false) →
      (∀ a ∈ post, ∀ b ∈ binds, (Moist.MIR.freeVars a).contains b.1 = false) →
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
      (∀ a ∈ pre, ∀ b ∈ binds, (Moist.MIR.freeVars a).contains b.1 = false) →
      (∀ a ∈ post, ∀ b ∈ binds, (Moist.MIR.freeVars a).contains b.1 = false) →
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
    | simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.lowerTotal]

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
