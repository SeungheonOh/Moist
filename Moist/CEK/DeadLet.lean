import Moist.MIR.Semantics
import Moist.MIR.LowerTotal
import Moist.MIR.Optimize.Purity
import Moist.Plutus.DecidableEq
import Moist.CEK.Bisim

set_option linter.unusedSimpArgs false

namespace Moist.CEK.DeadLet

open Moist.CEK
open Moist.Plutus.Term
open Moist.MIR
open Moist.MIR.Semantics

/-! # Dead Let Elimination -- Semantic Correctness

Removes a dead let binding preserving BehEqClosed. The lowered LHS is
`Apply (Lam 0 body') e'` which beta-reduces into `compute [] (cons ve nil) body'`,
while the RHS evaluates `body'` in nil. Since closedAt 0 body', the env is
irrelevant and both produce ValueEq k results for all k.
-/

/-! ## lowerTotal produces closed terms -/

mutual
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

/-! ## Helpers -/

@[simp] theorem CekEnv.lookup_zero (env : CekEnv) : env.lookup 0 = none := by
  cases env <;> rfl

theorem steps_error (n : Nat) : steps n .error = .error := by
  induction n with | zero => rfl | succ n ih => simp [steps, step_error, ih]

theorem steps_trans (m n : Nat) (s : State) : steps (m + n) s = steps n (steps m s) := by
  induction m generalizing s with
  | zero => simp [steps]
  | succ m ih => simp only [Nat.succ_add, steps]; exact ih (step s)

/-! ## Value characterization -/

private theorem val_of (env : CekEnv) (t : Term) (expected : CekValue)
    (hstep : steps 2 (.compute [] env t) = .halt expected) (v : CekValue)
    (h : Reaches (.compute [] env t) v) : v = expected :=
  reaches_unique h ⟨2, hstep⟩

/-! ## Stack frame decomposition via liftState

We prove that the step function commutes with prepending extra frames to
the stack. This lets us decompose Apply (Lam n body) e' by peeling off the
funV frame and reasoning about the inner e' evaluation separately. -/

/-- Prepend a base stack to every stack inside a state. halt v maps to ret base v. -/
def liftState (base : Stack) : State → State
  | .compute s env t => .compute (s ++ base) env t
  | .ret s v => .ret (s ++ base) v
  | .halt v => .ret base v
  | .error => .error

/-- Predicate: a state is "active" (not halt, not error, not ret-with-empty-stack). -/
private def isActive : State → Prop
  | .compute _ _ _ => True
  | .ret (_ :: _) _ => True
  | _ => False

private theorem step_liftState_active (base : Stack) (s : State) (h : isActive s) :
    step (liftState base s) = liftState base (step s) := by
  match s with
  | .compute stk env t =>
    simp only [liftState]
    cases t with
    | Var n => simp [step]; cases env.lookup n <;> simp [liftState]
    | Constant p => obtain ⟨c, ty⟩ := p; simp [step, liftState]
    | Builtin b => simp [step, liftState]
    | Lam n body => simp [step, liftState]
    | Delay body => simp [step, liftState]
    | Force e => simp [step, liftState, List.cons_append]
    | Apply f x => simp [step, liftState, List.cons_append]
    | Constr tag args => cases args with
      | nil => simp [step, liftState]
      | cons m ms => simp [step, liftState, List.cons_append]
    | Case scrut alts => simp [step, liftState, List.cons_append]
    | Error => simp [step, liftState]
  | .ret (f :: stk) v =>
    simp only [liftState, List.cons_append]
    cases f with
    | force => cases v with
      | VDelay body env => simp [step, liftState]
      | VBuiltin b args ea =>
        simp only [step]; cases ea.head <;> (try simp [liftState]) <;>
        cases ea.tail <;> (try simp [liftState]) <;>
        cases evalBuiltin b args <;> simp [liftState]
      | _ => simp [step, liftState]
    | arg m env => simp [step, liftState, List.cons_append]
    | funV vf => cases vf with
      | VLam body env => simp [step, liftState]
      | VBuiltin b args ea =>
        simp only [step]; cases ea.head <;> (try simp [liftState]) <;>
        cases ea.tail <;> (try simp [liftState]) <;>
        cases evalBuiltin b (_ :: args) <;> simp [liftState]
      | _ => simp [step, liftState]
    | constrField tag done todo env => cases todo with
      | nil => simp [step, liftState]
      | cons m ms => simp [step, liftState, List.cons_append]
    | applyArg vx => cases v with
      | VLam body env => simp [step, liftState]
      | VBuiltin b args ea =>
        simp only [step]; cases ea.head <;> (try simp [liftState]) <;>
        cases ea.tail <;> (try simp [liftState]) <;>
        cases evalBuiltin b (_ :: args) <;> simp [liftState]
      | _ => simp [step, liftState]
    | caseScrutinee alts env => cases v with
      | VConstr tag fields =>
        simp only [step]; cases alts[tag]? <;> simp [liftState, List.append_assoc]
      | VCon c =>
        simp only [step, constToTagAndFields, liftState, List.cons_append]
        split <;> try rfl
        · split <;> try rfl
          split <;> simp [liftState, List.append_assoc]
      | _ => simp [step, liftState]
  | .ret [] _ => exact absurd h (by simp [isActive])
  | .halt _ => exact absurd h (by simp [isActive])
  | .error => exact absurd h (by simp [isActive])

/-- Iterated step commutes with liftState for active prefixes. -/
private theorem steps_liftState (base : Stack) :
    ∀ (n : Nat) (s : State),
    (∀ j, j < n → isActive (steps j s)) →
    steps n (liftState base s) = liftState base (steps n s)
  | 0, _, _ => by simp [steps]
  | n + 1, s, hact => by
    simp only [steps]
    rw [step_liftState_active base s (hact 0 (Nat.zero_lt_succ n))]
    exact steps_liftState base n (step s) (fun j hj => by
      have := hact (j + 1) (by omega); simp only [steps] at this; exact this)

-- Helper: steps preserves error
private theorem steps_error_eq (n : Nat) : steps n .error = .error := by
  induction n with
  | zero => rfl
  | succ n ih => simp [steps, step, ih]

/-- Predicate: a UPLC term is a "value term" -- it evaluates in one step to a value
without needing further computation. These are exactly the terms for which
`Apply (Lam n body) e'` beta-reduces in exactly 5 CEK steps. -/
inductive IsValueTerm : Term → Prop where
  | constant : ∀ c ty, IsValueTerm (.Constant (c, ty))
  | builtin  : ∀ b, IsValueTerm (.Builtin b)
  | lam      : ∀ n body, IsValueTerm (.Lam n body)
  | delay    : ∀ body, IsValueTerm (.Delay body)

/-- Helper: if steps k reaches a known state and the full trace halts after N steps,
we can decompose the remaining N - k steps. -/
private theorem decompose_after (body e' : Term) (env : CekEnv) (n k : Nat)
    (target : State) (v_final : CekValue) (N : Nat)
    (hk : steps k (.compute [] env (.Apply (.Lam n body) e')) = target)
    (hN : steps N (.compute [] env (.Apply (.Lam n body) e')) = .halt v_final)
    (hN_ge : N ≥ k) :
    steps (N - k) target = .halt v_final := by
  rw [show N = k + (N - k) by omega, steps_trans, hk] at hN; exact hN

/-- The value that a value term produces when evaluated in a given environment. -/
private def valueTermResult (env : CekEnv) : Term → CekValue
  | .Constant (c, _) => .VCon c
  | .Builtin b       => .VBuiltin b [] (expectedArgs b)
  | .Lam _ body      => .VLam body env
  | .Delay body      => .VDelay body env
  | _                => .VCon (.Unit)  -- unreachable for IsValueTerm

/-- For any value term e', Apply (Lam n body) e' takes exactly 5 CEK steps to
reach `compute [] (env.extend ve) body` where ve is the value of e'. -/
private theorem steps5_value (env : CekEnv) (body : Term) (n : Nat) (e' : Term)
    (hval : IsValueTerm e') :
    steps 5 (.compute [] env (.Apply (.Lam n body) e')) =
    .compute [] (env.extend (valueTermResult env e')) body := by
  cases hval with
  | constant c ty =>
    simp only [valueTermResult]
    unfold steps; rw [show step (.compute [] env (.Apply (.Lam n body) (.Constant (c, ty)))) =
      .compute [.arg (.Constant (c, ty)) env] env (.Lam n body) from rfl]
    unfold steps; rw [show step (.compute [.arg (.Constant (c, ty)) env] env (.Lam n body)) =
      .ret [.arg (.Constant (c, ty)) env] (.VLam body env) from rfl]
    unfold steps; rw [show step (.ret [.arg (.Constant (c, ty)) env] (.VLam body env)) =
      .compute [.funV (.VLam body env)] env (.Constant (c, ty)) from rfl]
    unfold steps; rw [show step (.compute [.funV (.VLam body env)] env (.Constant (c, ty))) =
      .ret [.funV (.VLam body env)] (.VCon c) from rfl]
    unfold steps; rw [show step (.ret [.funV (.VLam body env)] (.VCon c)) =
      .compute [] (env.extend (.VCon c)) body from rfl]
    simp [steps]
  | builtin b =>
    simp only [valueTermResult]
    unfold steps; rw [show step (.compute [] env (.Apply (.Lam n body) (.Builtin b))) =
      .compute [.arg (.Builtin b) env] env (.Lam n body) from rfl]
    unfold steps; rw [show step (.compute [.arg (.Builtin b) env] env (.Lam n body)) =
      .ret [.arg (.Builtin b) env] (.VLam body env) from rfl]
    unfold steps; rw [show step (.ret [.arg (.Builtin b) env] (.VLam body env)) =
      .compute [.funV (.VLam body env)] env (.Builtin b) from rfl]
    unfold steps; rw [show step (.compute [.funV (.VLam body env)] env (.Builtin b)) =
      .ret [.funV (.VLam body env)] (.VBuiltin b [] (expectedArgs b)) from rfl]
    unfold steps; rw [show step (.ret [.funV (.VLam body env)] (.VBuiltin b [] (expectedArgs b))) =
      .compute [] (env.extend (.VBuiltin b [] (expectedArgs b))) body from rfl]
    simp [steps]
  | lam n' body' =>
    simp only [valueTermResult]
    unfold steps; rw [show step (.compute [] env (.Apply (.Lam n body) (.Lam n' body'))) =
      .compute [.arg (.Lam n' body') env] env (.Lam n body) from rfl]
    unfold steps; rw [show step (.compute [.arg (.Lam n' body') env] env (.Lam n body)) =
      .ret [.arg (.Lam n' body') env] (.VLam body env) from rfl]
    unfold steps; rw [show step (.ret [.arg (.Lam n' body') env] (.VLam body env)) =
      .compute [.funV (.VLam body env)] env (.Lam n' body') from rfl]
    unfold steps; rw [show step (.compute [.funV (.VLam body env)] env (.Lam n' body')) =
      .ret [.funV (.VLam body env)] (.VLam body' env) from rfl]
    unfold steps; rw [show step (.ret [.funV (.VLam body env)] (.VLam body' env)) =
      .compute [] (env.extend (.VLam body' env)) body from rfl]
    simp [steps]
  | delay body' =>
    simp only [valueTermResult]
    unfold steps; rw [show step (.compute [] env (.Apply (.Lam n body) (.Delay body'))) =
      .compute [.arg (.Delay body') env] env (.Lam n body) from rfl]
    unfold steps; rw [show step (.compute [.arg (.Delay body') env] env (.Lam n body)) =
      .ret [.arg (.Delay body') env] (.VLam body env) from rfl]
    unfold steps; rw [show step (.ret [.arg (.Delay body') env] (.VLam body env)) =
      .compute [.funV (.VLam body env)] env (.Delay body') from rfl]
    unfold steps; rw [show step (.compute [.funV (.VLam body env)] env (.Delay body')) =
      .ret [.funV (.VLam body env)] (.VDelay body' env) from rfl]
    unfold steps; rw [show step (.ret [.funV (.VLam body env)] (.VDelay body' env)) =
      .compute [] (env.extend (.VDelay body' env)) body from rfl]
    simp [steps]

/-- Steps 0..4 of Apply (Lam n body) (Constant (c,ty)) are not halt. -/
private theorem not_halt_const (env : CekEnv) (body : Term) (n : Nat)
    (c : Const) (ty : BuiltinType) (v : CekValue) (N : Nat) (hlt : N < 5)
    (hN : steps N (.compute [] env (.Apply (.Lam n body) (.Constant (c, ty)))) = .halt v) :
    False := by
  have h0 : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 := by omega
  rcases h0 with rfl | rfl | rfl | rfl | rfl <;> simp [steps, step] at hN

/-- Steps 0..4 of Apply (Lam n body) (Builtin b) are not halt. -/
private theorem not_halt_builtin (env : CekEnv) (body : Term) (n : Nat)
    (b : BuiltinFun) (v : CekValue) (N : Nat) (hlt : N < 5)
    (hN : steps N (.compute [] env (.Apply (.Lam n body) (.Builtin b))) = .halt v) :
    False := by
  have h0 : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 := by omega
  rcases h0 with rfl | rfl | rfl | rfl | rfl <;> simp [steps, step] at hN

/-- Steps 0..4 of Apply (Lam n body) (Lam n' body') are not halt. -/
private theorem not_halt_lam (env : CekEnv) (body : Term) (n n' : Nat) (body' : Term)
    (v : CekValue) (N : Nat) (hlt : N < 5)
    (hN : steps N (.compute [] env (.Apply (.Lam n body) (.Lam n' body'))) = .halt v) :
    False := by
  have h0 : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 := by omega
  rcases h0 with rfl | rfl | rfl | rfl | rfl <;> simp [steps, step] at hN

/-- Steps 0..4 of Apply (Lam n body) (Delay body') are not halt. -/
private theorem not_halt_delay (env : CekEnv) (body : Term) (n : Nat) (body' : Term)
    (v : CekValue) (N : Nat) (hlt : N < 5)
    (hN : steps N (.compute [] env (.Apply (.Lam n body) (.Delay body'))) = .halt v) :
    False := by
  have h0 : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 := by omega
  rcases h0 with rfl | rfl | rfl | rfl | rfl <;> simp [steps, step] at hN

/-- For a value term, if Apply (Lam n body) e' halts, then N >= 5. -/
private theorem apply_lam_value_N_ge_5 (env : CekEnv) (body : Term) (n : Nat) (e' : Term)
    (hval : IsValueTerm e') (v_final : CekValue) (N : Nat)
    (hN : steps N (.compute [] env (.Apply (.Lam n body) e')) = .halt v_final) :
    N ≥ 5 := by
  cases hval with
  | constant c ty =>
    exact Nat.le_of_not_lt fun hlt =>
      not_halt_const env body n c ty v_final N hlt hN
  | builtin b =>
    exact Nat.le_of_not_lt fun hlt =>
      not_halt_builtin env body n b v_final N hlt hN
  | lam n' body' =>
    exact Nat.le_of_not_lt fun hlt =>
      not_halt_lam env body n n' body' v_final N hlt hN
  | delay body' =>
    exact Nat.le_of_not_lt fun hlt =>
      not_halt_delay env body n body' v_final N hlt hN

/-- Main decomposition: for a value term e', if Apply (Lam n body) e' reaches v_final,
then body evaluated in the extended environment also reaches v_final.
Returns the intermediate value ve and the proof. -/
theorem apply_lam_decompose (env : CekEnv) (body : Term) (e' : Term) (n : Nat)
    (v_final : CekValue)
    (hval : IsValueTerm e')
    (hreach : Reaches (.compute [] env (.Apply (.Lam n body) e')) v_final) :
    ∃ ve : CekValue, Reaches (.compute [] (env.extend ve) body) v_final := by
  obtain ⟨N, hN⟩ := hreach
  have hge := apply_lam_value_N_ge_5 env body n e' hval v_final N hN
  have h5 := steps5_value env body n e' hval
  exact ⟨valueTermResult env e', N - 5, decompose_after body e' env n 5 _ v_final N h5 hN hge⟩

/-! ## ValueEq properties -/

mutual
  theorem valueEq_refl : ∀ (k : Nat) (v : CekValue), ValueEq k v v
    | 0, _ => by simp [ValueEq]
    | _ + 1, .VCon _ => by simp [ValueEq]
    | k + 1, .VLam _ _ => by
      simp only [ValueEq]; intro arg v1 v2 h1 h2
      exact reaches_unique h1 h2 ▸ valueEq_refl k v1
    | k + 1, .VDelay _ _ => by
      simp only [ValueEq]; intro v1 v2 h1 h2
      exact reaches_unique h1 h2 ▸ valueEq_refl k v1
    | _ + 1, .VConstr _ fields => by
      unfold ValueEq; exact ⟨rfl, listValueEq_refl _ fields⟩
    | k + 1, .VBuiltin b args ea => by
      unfold ValueEq; exact ⟨rfl, listValueEq_refl k args, rfl⟩
  theorem listValueEq_refl : ∀ (k : Nat) (vs : List CekValue), ListValueEq k vs vs
    | _, [] => by simp [ListValueEq]
    | k, v :: vs => by simp only [ListValueEq]; exact ⟨valueEq_refl k v, listValueEq_refl k vs⟩
end

/-! ## MIRDeadLetCond -/

/-- An expression is "atomic pure" if it is a simple value form that lowers
to a UPLC value term (Constant, Builtin, Lam, Delay). Unlike `isPure` (which
is partial and handles App/Constr/etc.), this is total and sufficient for
the dead-let proof which needs `IsValueTerm` on the lowered term. -/
def isAtomicPure : Expr → Bool
  | .Lit _ | .Builtin _ | .Lam _ _ | .Delay _ => true
  | _ => false

structure MIRDeadLetCond (x : VarId) (e body : Expr) : Prop where
  unused : (freeVars body).contains x = false
  safe : isAtomicPure e = true

/-! ## Core semantic lemma: closedAt + EnvRelV implies ValueEq

For closedAt d t with EnvRelV d env1 env2 (from Moist.CEK.ClosedAt),
evaluating t from empty stack in both envs produces ValueEq k results
for all k. The composite cases (Apply, Force, Constr, Case) delegate
to Bisim.bisim_reaches which provides ValueRelV results directly. -/

/-! ### Helper: ListValueRelV -> ListValueEq -/

private theorem listValueRelV_implies_listValueEq_zero
    {vs1 vs2 : List CekValue}
    (h : ListValueRelV vs1 vs2) : ListValueEq 0 vs1 vs2 := by
  match h with
  | .nil => simp [ListValueEq]
  | .cons _ htl =>
    simp only [ListValueEq]; exact ⟨show ValueEq 0 _ _ by simp [ValueEq],
      listValueRelV_implies_listValueEq_zero htl⟩

private theorem listValueRelV_implies_listValueEq_succ {k : Nat}
    (partB : ∀ v1 v2, ValueRelV v1 v2 → ValueEq (k + 1) v1 v2)
    {vs1 vs2 : List CekValue}
    (h : ListValueRelV vs1 vs2) : ListValueEq (k + 1) vs1 vs2 := by
  match h with
  | .nil => simp [ListValueEq]
  | .cons hd htl =>
    simp only [ListValueEq]
    exact ⟨partB _ _ hd, listValueRelV_implies_listValueEq_succ partB htl⟩

/-! ### The env_rel_bundle: ValueRelV -> ValueEq at all depths -/

private theorem env_rel_bundle :
    ∀ (k : Nat),
    (∀ d t env1 env2 v1 v2,
      closedAt d t = true → EnvRelV d env1 env2 →
      Reaches (.compute [] env1 t) v1 → Reaches (.compute [] env2 t) v2 →
      ValueEq k v1 v2) ∧
    (∀ v1 v2, ValueRelV v1 v2 → ValueEq k v1 v2) ∧
    (∀ vs1 vs2, ListValueRelV vs1 vs2 → ListValueEq k vs1 vs2) := by
  intro k; induction k with
  | zero =>
    refine ⟨fun _ _ _ _ _ _ _ _ _ _ => ?_, fun _ _ _ => ?_,
            fun _ _ h => listValueRelV_implies_listValueEq_zero h⟩
    · simp [ValueEq]
    · simp [ValueEq]
  | succ k ihk =>
    obtain ⟨ihA, ihB, ihC⟩ := ihk
    have partB : ∀ v1 v2, ValueRelV v1 v2 → ValueEq (k + 1) v1 v2 := by
      intro v1 v2 hr
      cases hr with
      | vcon => simp [ValueEq]
      | vlam d hclosed henv =>
        simp only [ValueEq]; intro arg w1 w2 hw1 hw2
        exact ihA (d + 1) _ _ _ w1 w2 hclosed (envRelV_extend d _ _ arg arg henv (.refl)) hw1 hw2
      | vdelay d hclosed henv =>
        simp only [ValueEq]; intro w1 w2 hw1 hw2
        exact ihA d _ _ _ w1 w2 hclosed henv hw1 hw2
      | vconstr htag hfs =>
        subst htag; unfold ValueEq; exact ⟨rfl, ihC _ _ hfs⟩
      | vbuiltin hb hargs hea =>
        subst hb; subst hea; unfold ValueEq; exact ⟨rfl, ihC _ _ hargs, rfl⟩
      | refl => exact valueEq_refl _ _
    have partC : ∀ vs1 vs2, ListValueRelV vs1 vs2 → ListValueEq (k + 1) vs1 vs2 :=
      fun _ _ h => listValueRelV_implies_listValueEq_succ partB h
    have partA : ∀ d t env1 env2 v1 v2,
        closedAt d t = true → EnvRelV d env1 env2 →
        Reaches (.compute [] env1 t) v1 → Reaches (.compute [] env2 t) v2 →
        ValueEq (k + 1) v1 v2 := by
      intro d t env1 env2 v1 v2 hclosed hrel h1 h2
      match t with
      | .Var n =>
        simp only [closedAt] at hclosed
        have hle : n ≤ d := of_decide_eq_true hclosed
        cases n with
        | zero =>
          exfalso; obtain ⟨N, hN⟩ := h1; cases N with
          | zero => simp [steps] at hN
          | succ N' => simp [steps, step, steps_error] at hN
        | succ m =>
          have hlookup : LookupRelV (env1.lookup (m+1)) (env2.lookup (m+1)) :=
            envRelV_elim hrel (by omega) hle
          cases hn1 : env1.lookup (m+1) with
          | none =>
            -- Both lookups none (by LookupRelV)
            exfalso; obtain ⟨N, hN⟩ := h1; cases N with
            | zero => simp [steps] at hN
            | succ N' => simp [steps, step, hn1, steps_error] at hN
          | some w1 =>
            -- env1 returns some w1. By LookupRelV, env2 also returns some.
            have hlookup' := hlookup; rw [hn1] at hlookup'
            -- hlookup' : LookupRelV (some w1) (env2.lookup (m+1))
            -- LookupRelV (some _) X can only be .bothSome, so X = some w2
            generalize hn2 : env2.lookup (m+1) = r2 at hlookup'
            cases hlookup' with
            | bothSome hv =>
              have hv1 : v1 = w1 := by
                obtain ⟨N, hN⟩ := h1; cases N with
                | zero => simp [steps] at hN
                | succ N' => simp [steps, step, hn1] at hN; exact reaches_unique ⟨N', hN⟩ ⟨1, rfl⟩
              rename_i w2
              have hv2 : v2 = w2 := by
                obtain ⟨N, hN⟩ := h2; cases N with
                | zero => simp [steps] at hN
                | succ N' => simp [steps, step, hn2] at hN; exact reaches_unique ⟨N', hN⟩ ⟨1, rfl⟩
              subst hv1; subst hv2; exact partB _ _ hv
      | .Constant p =>
        obtain ⟨c, ty⟩ := p
        have hv1 : v1 = .VCon c := reaches_unique h1 ⟨2, rfl⟩
        have hv2 : v2 = .VCon c := reaches_unique h2 ⟨2, rfl⟩
        subst hv1; subst hv2; simp [ValueEq]
      | .Builtin b =>
        have hv1 := reaches_unique h1 (⟨2, rfl⟩ : Reaches (.compute [] env1 (.Builtin b)) _)
        have hv2 := reaches_unique h2 (⟨2, rfl⟩ : Reaches (.compute [] env2 (.Builtin b)) _)
        subst hv1; subst hv2; simp [ValueEq, ListValueEq]
      | .Error =>
        exfalso; obtain ⟨N, hN⟩ := h1; cases N with
        | zero => simp [steps] at hN
        | succ N' => simp [steps, step, steps_error] at hN
      | .Lam m body =>
        have hv1 := reaches_unique h1 (⟨2, rfl⟩ : Reaches (.compute [] env1 (.Lam m body)) _)
        have hv2 := reaches_unique h2 (⟨2, rfl⟩ : Reaches (.compute [] env2 (.Lam m body)) _)
        subst hv1; subst hv2; simp only [ValueEq]
        intro arg w1 w2 hw1 hw2
        exact ihA (d+1) body (env1.extend arg) (env2.extend arg) w1 w2
          (by simp only [closedAt] at hclosed; exact hclosed)
          (envRelV_extend d env1 env2 arg arg hrel (.refl)) hw1 hw2
      | .Delay body =>
        have hv1 := reaches_unique h1 (⟨2, rfl⟩ : Reaches (.compute [] env1 (.Delay body)) _)
        have hv2 := reaches_unique h2 (⟨2, rfl⟩ : Reaches (.compute [] env2 (.Delay body)) _)
        subst hv1; subst hv2; simp only [ValueEq]
        intro w1 w2 hw1 hw2
        exact ihA d body env1 env2 w1 w2
          (by simp only [closedAt] at hclosed; exact hclosed) hrel hw1 hw2
      | .Apply _ _ =>
        exact partB v1 v2 (Bisim.bisim_reaches (.compute .nil d hrel hclosed) h1 h2)
      | .Force _ =>
        exact partB v1 v2 (Bisim.bisim_reaches (.compute .nil d hrel hclosed) h1 h2)
      | .Constr _ _ =>
        exact partB v1 v2 (Bisim.bisim_reaches (.compute .nil d hrel hclosed) h1 h2)
      | .Case _ _ =>
        exact partB v1 v2 (Bisim.bisim_reaches (.compute .nil d hrel hclosed) h1 h2)
    exact ⟨partA, partB, partC⟩

theorem closed_env_valueEq (k d : Nat) (t : Term) (env1 env2 : CekEnv)
    (hclosed : closedAt d t = true) (hrel : EnvRelV d env1 env2)
    (v1 v2 : CekValue)
    (h1 : Reaches (.compute [] env1 t) v1) (h2 : Reaches (.compute [] env2 t) v2) :
    ValueEq k v1 v2 :=
  (env_rel_bundle k).1 d t env1 env2 v1 v2 hclosed hrel h1 h2

/-! ## Bridge: isAtomicPure + lowerTotal [] implies IsValueTerm -/

theorem lowerTotal_nil_atomic_isValueTerm (e : Expr) (e' : Term)
    (hlower : lowerTotal [] e = some e') (hpure : isAtomicPure e = true) :
    IsValueTerm e' := by
  match e with
  | .Lit (c, ty) =>
    simp only [lowerTotal.eq_2] at hlower; injection hlower with hlower; subst hlower
    exact .constant c ty
  | .Builtin b =>
    simp only [lowerTotal.eq_3] at hlower; injection hlower with hlower; subst hlower
    exact .builtin b
  | .Lam x body_e =>
    simp only [lowerTotal.eq_5, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlower
    obtain ⟨body', _, heq⟩ := hlower; injection heq with heq; subst heq
    exact .lam 0 body'
  | .Delay inner =>
    simp only [lowerTotal.eq_8, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlower
    obtain ⟨inner', _, heq⟩ := hlower; injection heq with heq; subst heq
    exact .delay inner'
  | .Var _ => simp [isAtomicPure] at hpure
  | .Error => simp [isAtomicPure] at hpure
  | .App _ _ => simp [isAtomicPure] at hpure
  | .Force _ => simp [isAtomicPure] at hpure
  | .Constr _ _ => simp [isAtomicPure] at hpure
  | .Case _ _ => simp [isAtomicPure] at hpure
  | .Let _ _ => simp [isAtomicPure] at hpure
  | .Fix _ _ => simp [isAtomicPure] at hpure

/-! ## Main theorem -/

theorem dead_let_sound_closed (x : VarId) (e body : Expr)
    (hsc : MIRDeadLetCond x e body) :
    BehEqClosed (.Let [(x, e, false)] body) body := by
  unfold BehEqClosed
  have hlower_let : lowerTotal [] (.Let [(x, e, false)] body) =
      (do let e' ← lowerTotal [] e
          let b' ← lowerTotal [] body
          some (Term.Apply (Term.Lam 0 b') e')) := by
    rw [lowerTotal.eq_11, lowerTotalLet.eq_2, lowerTotalLet.eq_1,
        lowerTotal_closed_env_irrel x body hsc.unused]
  cases hb : lowerTotal [] body with
  | none => simp [hb, hlower_let]
  | some body' =>
    cases he : lowerTotal [] e with
    | none => simp [hlower_let, he, hb]
    | some e' =>
      simp [hlower_let, he, hb]
      intro k v1 v2 hv1 hv2
      -- e' is a value term because e is atomic pure
      have hval : IsValueTerm e' := lowerTotal_nil_atomic_isValueTerm e e' he hsc.safe
      -- Decompose the Apply (Lam 0 body') e' computation
      obtain ⟨ve, hbody_reach⟩ := apply_lam_decompose .nil body' e' 0 v1 hval hv1
      have hclosed : closedAt 0 body' = true := by
        have := lowerTotal_closedAt [] body body' hb; simp at this; exact this
      -- EnvRelV 0 is vacuously true for any two envs
      have hrel : EnvRelV 0 (.cons ve .nil) .nil :=
        .mk fun n hn hle => absurd (Nat.lt_of_lt_of_le hn hle) (Nat.lt_irrefl 0)
      exact closed_env_valueEq k 0 body' (.cons ve .nil) .nil hclosed hrel v1 v2 hbody_reach hv2

end Moist.CEK.DeadLet
