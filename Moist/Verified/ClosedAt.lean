import Moist.CEK.Machine
import Moist.Verified.Semantics

namespace Moist.Verified

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified.Semantics

/-! # closedAt, ValueRelV, EnvRelV — shared definitions for bisimulation proofs

This module provides the structural vocabulary for the bisimulation and
dead-let-elimination proofs. The three main concepts are:

1. **`closedAt d t`** — a decidable predicate asserting that every de Bruijn
   variable in term `t` is bound within depth `d`. This is the UPLC analogue
   of "all free variables have indices ≤ d".

2. **`ValueRelV` / `ListValueRelV`** — an inductive structural relation on
   CEK values. Two values are related when they share the same term but may
   live in different (but `EnvRelV`-related) environments. This captures the
   idea that "same code, similar environments ⇒ similar values".

3. **`EnvRelV d env1 env2`** — a per-position relation on CEK environments.
   For each index in `1..d`, either both lookups fail or both succeed with
   `ValueRelV`-related values.

Together these let us state and prove that stepping two `StateRel`-related
states produces `StateRel`-related successors (the bisimulation invariant
in `Bisim.lean`).
-/

/-! ## closedAt: de Bruijn depth-bounded closed term predicate

`closedAt d t` checks that every `Var n` node in `t` satisfies `n ≤ d`.
In a CEK machine, a term that is `closedAt d` can be evaluated in any
environment that binds at least positions `1..d`. -/

mutual
  /-- Returns `true` when every variable in `t` has index at most `d`.
      Recurses structurally on the term; `Lam` increments the depth by 1.
      Constants, builtins, and `Error` are trivially closed. -/
  def closedAt (d : Nat) (t : Term) : Bool := match t with
    | .Var n => decide (n ≤ d)
    | .Lam _ body => closedAt (d + 1) body
    | .Apply f x => closedAt d f && closedAt d x
    | .Force e | .Delay e => closedAt d e
    | .Constr _ args => closedAtList d args
    | .Case scrut alts => closedAt d scrut && closedAtList d alts
    | .Constant _ | .Builtin _ | .Error => true
  termination_by sizeOf t
  /-- Pointwise `closedAt` for a list of terms (constructor args, case alts). -/
  def closedAtList (d : Nat) (ts : List Term) : Bool := match ts with
    | [] => true
    | t :: rest => closedAt d t && closedAtList d rest
  termination_by sizeOf ts
end

/-! ## closedAt equation helpers

These theorems invert `closedAt` for each term constructor, extracting the
sub-obligations. They are the primary interface for case-splitting on
`closedAt` hypotheses in the bisimulation proof. -/

/-- If `Var n` is closed at depth `d`, then `n ≤ d`. -/
theorem closedAt_var {d n} (h : closedAt d (.Var n) = true) : n ≤ d := by
  rw [closedAt.eq_1] at h; exact of_decide_eq_true h

/-- Application: both the function and argument must be closed at `d`. -/
theorem closedAt_apply {d f x} (h : closedAt d (.Apply f x) = true) :
    closedAt d f = true ∧ closedAt d x = true := by
  rw [closedAt.eq_3] at h; exact Bool.and_eq_true_iff.mp h

/-- Force: the inner expression must be closed at `d`. -/
theorem closedAt_force {d e} (h : closedAt d (.Force e) = true) :
    closedAt d e = true := by rw [closedAt.eq_4] at h; exact h

/-- Delay: the inner expression must be closed at `d`. -/
theorem closedAt_delay {d e} (h : closedAt d (.Delay e) = true) :
    closedAt d e = true := by rw [closedAt.eq_5] at h; exact h

/-- Lambda: the body is closed at `d + 1` (the binder adds one level). -/
theorem closedAt_lam {d n body} (h : closedAt d (.Lam n body) = true) :
    closedAt (d + 1) body = true := by rw [closedAt.eq_2] at h; exact h

/-- Constructor: all arguments must be closed at `d`. -/
theorem closedAt_constr {d tag args} (h : closedAt d (.Constr tag args) = true) :
    closedAtList d args = true := by rw [closedAt.eq_6] at h; exact h

/-- Cons case for `closedAtList`: head and tail both closed. -/
theorem closedAt_constr_cons {d m ms} (h : closedAtList d (m :: ms) = true) :
    closedAt d m = true ∧ closedAtList d ms = true := by
  rw [closedAtList.eq_2] at h; exact Bool.and_eq_true_iff.mp h

/-- Case: both the scrutinee and all alternatives must be closed at `d`. -/
theorem closedAt_case {d scrut alts} (h : closedAt d (.Case scrut alts) = true) :
    closedAt d scrut = true ∧ closedAtList d alts = true := by
  rw [closedAt.eq_7] at h; exact Bool.and_eq_true_iff.mp h

/-! ## closedAt monotonicity

If a term is closed at depth `d`, it is also closed at any greater depth `d'`.
This is used pervasively: when a lambda body is closed at `d+1`, we can
also use it at any `d' ≥ d+1` that arises from environment extension. -/

mutual
  /-- Monotonicity of `closedAt`: increasing the depth bound preserves closure.
      Structural induction on the term; the `Lam` case shifts both bounds. -/
  theorem closedAt_mono {d d' : Nat} {t : Term} (h : closedAt d t = true) (hle : d ≤ d') :
      closedAt d' t = true := by
    cases t with
    | Var n =>
      rw [closedAt.eq_1] at h ⊢; exact decide_eq_true (Nat.le_trans (of_decide_eq_true h) hle)
    | Lam _ body =>
      rw [closedAt.eq_2] at h ⊢; exact closedAt_mono h (by omega)
    | Apply f x =>
      rw [closedAt.eq_3] at h ⊢; have ⟨hf, hx⟩ := Bool.and_eq_true_iff.mp h
      exact Bool.and_eq_true_iff.mpr ⟨closedAt_mono hf hle, closedAt_mono hx hle⟩
    | Force e =>
      rw [closedAt.eq_4] at h ⊢; exact closedAt_mono h hle
    | Delay e =>
      rw [closedAt.eq_5] at h ⊢; exact closedAt_mono h hle
    | Constr _ args =>
      rw [closedAt.eq_6] at h ⊢; exact closedAtList_mono h hle
    | Case scrut alts =>
      rw [closedAt.eq_7] at h ⊢; have ⟨hs, ha⟩ := Bool.and_eq_true_iff.mp h
      exact Bool.and_eq_true_iff.mpr ⟨closedAt_mono hs hle, closedAtList_mono ha hle⟩
    | Constant _ => simp [closedAt]
    | Builtin _ => simp [closedAt]
    | Error => simp [closedAt]
  termination_by sizeOf t
  theorem closedAtList_mono {d d' : Nat} {ts : List Term}
      (h : closedAtList d ts = true) (hle : d ≤ d') :
      closedAtList d' ts = true := by
    cases ts with
    | nil => simp [closedAtList]
    | cons t rest =>
      rw [closedAtList.eq_2] at h ⊢; have ⟨ht, hr⟩ := Bool.and_eq_true_iff.mp h
      exact Bool.and_eq_true_iff.mpr ⟨closedAt_mono ht hle, closedAtList_mono hr hle⟩
  termination_by sizeOf ts
end

/-! ## closedAt existence: every term is closed at some depth

Every UPLC term is closed at some finite depth (the maximum variable index
it contains). This is used in the bisimulation proof's `refl` cases: when
`ValueRelV.refl` gives us an identical value on both sides, we need to
produce a depth witness for the contained term, even though no environment
relation was given to us. -/

mutual
  /-- Every term has a finite closure depth. For variables it is `n` itself;
      for compound terms it is the max of the sub-term depths. -/
  theorem closedAt_exists (t : Term) : ∃ d, closedAt d t = true := by
    cases t with
    | Var n => exact ⟨n, by rw [closedAt.eq_1]; exact decide_eq_true (Nat.le_refl n)⟩
    | Lam _ body =>
      have ⟨d, hd⟩ := closedAt_exists body
      exact ⟨d, by rw [closedAt.eq_2]; exact closedAt_mono hd (by omega)⟩
    | Apply f x =>
      have ⟨df, hf⟩ := closedAt_exists f; have ⟨dx, hx⟩ := closedAt_exists x
      refine ⟨max df dx, ?_⟩
      rw [closedAt.eq_3]
      exact Bool.and_eq_true_iff.mpr
        ⟨closedAt_mono hf (Nat.le_max_left df dx), closedAt_mono hx (Nat.le_max_right df dx)⟩
    | Force e =>
      have ⟨d, hd⟩ := closedAt_exists e; exact ⟨d, by rw [closedAt.eq_4]; exact hd⟩
    | Delay e =>
      have ⟨d, hd⟩ := closedAt_exists e; exact ⟨d, by rw [closedAt.eq_5]; exact hd⟩
    | Constr _ args =>
      have ⟨d, hd⟩ := closedAtList_exists args
      exact ⟨d, by rw [closedAt.eq_6]; exact hd⟩
    | Case scrut alts =>
      have ⟨ds, hs⟩ := closedAt_exists scrut
      have ⟨da, ha⟩ := closedAtList_exists alts
      refine ⟨max ds da, ?_⟩
      rw [closedAt.eq_7]
      exact Bool.and_eq_true_iff.mpr
        ⟨closedAt_mono hs (Nat.le_max_left ds da), closedAtList_mono ha (Nat.le_max_right ds da)⟩
    | Constant _ => exact ⟨0, by simp [closedAt]⟩
    | Builtin _ => exact ⟨0, by simp [closedAt]⟩
    | Error => exact ⟨0, by simp [closedAt]⟩
  termination_by sizeOf t
  theorem closedAtList_exists (ts : List Term) : ∃ d, closedAtList d ts = true := by
    cases ts with
    | nil => exact ⟨0, by simp [closedAtList]⟩
    | cons t rest =>
      have ⟨dt, ht⟩ := closedAt_exists t
      have ⟨dr, hr⟩ := closedAtList_exists rest
      refine ⟨max dt dr, ?_⟩
      rw [closedAtList.eq_2]
      exact Bool.and_eq_true_iff.mpr
        ⟨closedAt_mono ht (Nat.le_max_left dt dr), closedAtList_mono hr (Nat.le_max_right dt dr)⟩
  termination_by sizeOf ts
end

/-! ## closedAtList element access -/

/-- If a list of terms is closed at depth `d`, then each individual element
    at index `i` is also closed at `d`. Used when the CEK machine selects
    a case alternative by index. -/
theorem closedAtList_getElem {d : Nat} {ts : List Term} {i : Nat}
    (h : closedAtList d ts = true) (hi : i < ts.length) :
    closedAt d (ts[i]) = true := by
  induction ts generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons t rest ih =>
    have ⟨ht, hr⟩ := closedAt_constr_cons h
    cases i with
    | zero => simp; exact ht
    | succ j =>
      simp
      exact ih hr (by simp at hi; omega)

/-! ## ValueRelV, ListValueRelV, EnvRelV: mutual structural relations

These four mutually inductive types form the "structural simulation relation"
that the bisimulation proof maintains as an invariant across CEK steps.

The key design choice is that `ValueRelV` relates values that share the
**same term** but may have different environments — as long as those
environments agree on the positions the term actually uses (`closedAt`
witnesses). This is strictly weaker than equality and is exactly what
dead-let elimination needs: the optimized program evaluates the same body
in a smaller environment.

`EnvRelV d env1 env2` says that for positions `1..d`, either both lookups
fail or both succeed with `ValueRelV`-related values. This is weaker than
literal equality and is preserved when extending envs with
`ValueRelV`-related argument values during lambda application
(see `envRelV_extend`). -/

mutual
  /-- Structural value relation. Two CEK values are related when:
      - `vcon`: both are the same constant.
      - `vlam`: both are lambdas over the same body, with environments
        related up to the body's free-variable depth.
      - `vdelay`: same as `vlam` but for delayed computations.
      - `vconstr`: same tag, pointwise-related fields.
      - `vbuiltin`: same builtin, pointwise-related partial args, same arity.
      - `refl`: any value is related to itself (reflexivity). -/
  inductive ValueRelV : CekValue → CekValue → Prop where
    | vcon : ValueRelV (.VCon c) (.VCon c)
    | vlam (d : Nat) (hclosed : closedAt (d + 1) body = true)
        (henv : EnvRelV d env1 env2) :
        ValueRelV (.VLam body env1) (.VLam body env2)
    | vdelay (d : Nat) (hclosed : closedAt d body = true)
        (henv : EnvRelV d env1 env2) :
        ValueRelV (.VDelay body env1) (.VDelay body env2)
    | vconstr (htag : tag1 = tag2) (hfs : ListValueRelV fs1 fs2) :
        ValueRelV (.VConstr tag1 fs1) (.VConstr tag2 fs2)
    | vbuiltin (hb : b1 = b2) (hargs : ListValueRelV args1 args2) (hea : ea1 = ea2) :
        ValueRelV (.VBuiltin b1 args1 ea1) (.VBuiltin b2 args2 ea2)
    | refl : ValueRelV v v
  /-- Pointwise `ValueRelV` on lists: nil-nil or cons with matching heads. -/
  inductive ListValueRelV : List CekValue → List CekValue → Prop where
    | nil : ListValueRelV [] []
    | cons (hv : ValueRelV v1 v2) (hrs : ListValueRelV rest1 rest2) :
        ListValueRelV (v1 :: rest1) (v2 :: rest2)
  /-- Per-position lookup relation on optional values: either both fail
      (`none`/`none`) or both succeed with `ValueRelV`-related values. -/
  inductive LookupRelV : Option CekValue → Option CekValue → Prop where
    | bothNone : LookupRelV none none
    | bothSome (hv : ValueRelV v1 v2) : LookupRelV (some v1) (some v2)
  /-- Environment relation up to depth `d`. For every position `n` with
      `0 < n ≤ d`, the lookups in `env1` and `env2` are `LookupRelV`-related.
      Position 0 is excluded because the CEK environment uses 1-based indexing
      (lookup 0 always returns `none`). -/
  inductive EnvRelV : Nat → CekEnv → CekEnv → Prop where
    | mk : (∀ n, 0 < n → n ≤ d →
              LookupRelV (env1.lookup n) (env2.lookup n)) →
            EnvRelV d env1 env2
end

/-! ## EnvRelV lemmas -/

/-- Elimination form for `EnvRelV`: extract the lookup relation at a
    specific position `n` with `0 < n ≤ d`. -/
theorem envRelV_elim {d : Nat} {env1 env2 : CekEnv} (h : EnvRelV d env1 env2)
    {n : Nat} (hn : 0 < n) (hle : n ≤ d) :
    LookupRelV (env1.lookup n) (env2.lookup n) :=
  match h with | .mk f => f n hn hle

/-- Any environment is related to itself at any depth. -/
theorem envRelV_refl (d : Nat) (env : CekEnv) : EnvRelV d env env := by
  exact .mk fun n _ _ =>
    match h : env.lookup n with
    | none => h ▸ .bothNone
    | some v => h ▸ .bothSome .refl

/-- **Extension lemma**: if `EnvRelV d env1 env2` and `ValueRelV v1 v2`,
    then `EnvRelV (d+1) (env1.extend v1) (env2.extend v2)`. The new
    position (`d+1`, which maps to index 1 after extending) gets the
    new value pair, and all previous positions shift by 1 and inherit
    the old relation. This is the crucial lemma for lambda application
    in the bisimulation: when the CEK machine extends the environment
    with the argument, the relation is preserved at the incremented depth. -/
theorem envRelV_extend (d : Nat) (env1 env2 : CekEnv) (v1 v2 : CekValue)
    (henv : EnvRelV d env1 env2) (hv : ValueRelV v1 v2) :
    EnvRelV (d + 1) (env1.extend v1) (env2.extend v2) := by
  constructor; intro n hn hle
  cases n with
  | zero => omega
  | succ m =>
    cases m with
    | zero =>
      show LookupRelV (some v1) (some v2)
      exact .bothSome hv
    | succ m' =>
      show LookupRelV (env1.lookup (m' + 1)) (env2.lookup (m' + 1))
      exact envRelV_elim henv (by omega) (by omega)

/-! ## Frame, Stack, State relations

These lift the value/environment relations to the full CEK machine state.

`FrameRel` and `StackRel` are **depth-independent**: each frame that
carries an environment bundles its own depth witness `d`. This is essential
because a single continuation stack can contain closures captured at
different depths (e.g. a `funV` from an outer scope and an `arg` from an
inner scope).

`StateRel` combines stack, environment, and term/value relations into a
single invariant on machine states. The bisimulation theorem
(`Bisim.step_preserves`) shows that `StateRel` is preserved by `step`. -/

/-- Structural relation on continuation frames. Each frame variant that
    carries an environment (`arg`, `constrField`, `caseScrutinee`) bundles
    its own depth `d` and `EnvRelV d` witness. Frames without environments
    (`force`) or carrying only values (`funV`, `applyArg`) use `ValueRelV`
    directly. -/
inductive FrameRel : Frame → Frame → Prop where
  | force : FrameRel .force .force
  | arg (d : Nat) (t : Term) (henv : EnvRelV d env1 env2) (hclosed : closedAt d t = true) :
      FrameRel (.arg t env1) (.arg t env2)
  | funV (hv : ValueRelV v1 v2) : FrameRel (.funV v1) (.funV v2)
  | applyArg (hv : ValueRelV v1 v2) : FrameRel (.applyArg v1) (.applyArg v2)
  | constrField (d : Nat) (tag : Nat) (hdone : ListValueRelV done1 done2)
      (todo : List Term) (htodo : closedAtList d todo = true)
      (henv : EnvRelV d env1 env2) :
      FrameRel (.constrField tag done1 todo env1) (.constrField tag done2 todo env2)
  | caseScrutinee (d : Nat) (alts : List Term) (halts : closedAtList d alts = true)
      (henv : EnvRelV d env1 env2) :
      FrameRel (.caseScrutinee alts env1) (.caseScrutinee alts env2)

/-- Pointwise `FrameRel` on stacks: nil-nil or cons with matching frames. -/
inductive StackRel : Stack → Stack → Prop where
  | nil : StackRel [] []
  | cons (hf : FrameRel f1 f2) (hrs : StackRel s1 s2) :
      StackRel (f1 :: s1) (f2 :: s2)

/-- Full machine-state relation. A `compute` state carries a stack relation,
    an environment relation at some depth `d`, and a `closedAt d t` witness
    for the current term. A `ret` state carries a stack relation and a value
    relation. `error` relates only to `error`, and `halt` relates values
    via `ValueRelV`. -/
inductive StateRel : State → State → Prop where
  | compute (hs : StackRel s1 s2) (d : Nat) (henv : EnvRelV d env1 env2)
      (ht : closedAt d t = true) :
      StateRel (.compute s1 env1 t) (.compute s2 env2 t)
  | ret (hs : StackRel s1 s2) (hv : ValueRelV v1 v2) :
      StateRel (.ret s1 v1) (.ret s2 v2)
  | error : StateRel .error .error
  | halt (hv : ValueRelV v1 v2) :
      StateRel (.halt v1) (.halt v2)

end Moist.Verified
