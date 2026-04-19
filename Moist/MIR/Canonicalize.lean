import Moist.MIR.Expr
import Moist.MIR.Analysis
import Moist.MIR.LowerTotal

namespace Moist.MIR

/-! # Canonicalize

Rewrites every bound-variable binder to a canonical positional uid
(`origin = .gen`, `uid = binder depth`). Free variables retain their
original identity. After canonicalization, alpha-equivalence of closed
terms reduces to syntactic `=`.

Design: `canonicalizeAux env d` maintains the invariant `env.length = d`
by construction. The env records the original binders currently in
scope, head = innermost. For a lookup at index `i`, the canonical uid
is `d - 1 - i`, giving the innermost binder uid `d - 1` (i.e., index 0
↦ uid d-1) and the outermost uid 0.
-/

private def canonBinder (d : Nat) (hint : String) : VarId :=
  { uid := d, origin := .gen, hint := hint }

mutual
  def canonicalizeAux (env : List VarId) (d : Nat) : Expr → Expr
    | .Var x =>
      match env.findIdx? (· == x) with
      | some i => .Var (canonBinder (d - 1 - i) x.hint)
      | none   => .Var x
    | .Lit c        => .Lit c
    | .Builtin b    => .Builtin b
    | .Error        => .Error
    | .Lam x body   =>
      let x' := canonBinder d x.hint
      .Lam x' (canonicalizeAux (x :: env) (d + 1) body)
    | .Fix f body   =>
      let f' := canonBinder d f.hint
      .Fix f' (canonicalizeAux (f :: env) (d + 1) body)
    | .App f x      =>
      .App (canonicalizeAux env d f) (canonicalizeAux env d x)
    | .Force e      => .Force (canonicalizeAux env d e)
    | .Delay e      => .Delay (canonicalizeAux env d e)
    | .Constr t as  => .Constr t (canonicalizeList env d as)
    | .Case s alts  =>
      .Case (canonicalizeAux env d s) (canonicalizeList env d alts)
    | .Let binds body => canonicalizeLet env d binds body
  termination_by e => sizeOf e

  def canonicalizeList (env : List VarId) (d : Nat) : List Expr → List Expr
    | []       => []
    | e :: es  => canonicalizeAux env d e :: canonicalizeList env d es
  termination_by es => sizeOf es

  def canonicalizeLet (env : List VarId) (d : Nat)
      : List (VarId × Expr × Bool) → Expr → Expr
    | [], body => canonicalizeAux env d body
    | (x, rhs, er) :: rest, body =>
      let rhs' := canonicalizeAux env d rhs
      let x'   := canonBinder d x.hint
      .Let [(x', rhs', er)]
           (canonicalizeLet (x :: env) (d + 1) rest body)
  termination_by bs body => sizeOf bs + sizeOf body
end

def canonicalize (e : Expr) : Expr := canonicalizeAux [] 0 e

/-! ### Unfold equations for canonicalizeAux -/

private theorem canonAux_var (env : List VarId) (d : Nat) (x : VarId) :
    canonicalizeAux env d (.Var x)
      = match env.findIdx? (· == x) with
        | some i => .Var (canonBinder (d - 1 - i) x.hint)
        | none   => .Var x := by
  rw [canonicalizeAux]

private theorem canonAux_lit (env : List VarId) (d : Nat) (c) :
    canonicalizeAux env d (.Lit c) = .Lit c := by
  rw [canonicalizeAux]

private theorem canonAux_builtin (env : List VarId) (d : Nat) (b) :
    canonicalizeAux env d (.Builtin b) = .Builtin b := by
  rw [canonicalizeAux]

private theorem canonAux_error (env : List VarId) (d : Nat) :
    canonicalizeAux env d .Error = .Error := by
  rw [canonicalizeAux]

private theorem canonAux_lam (env : List VarId) (d : Nat) (x : VarId) (body : Expr) :
    canonicalizeAux env d (.Lam x body)
      = .Lam (canonBinder d x.hint) (canonicalizeAux (x :: env) (d + 1) body) := by
  rw [canonicalizeAux]

private theorem canonAux_fix (env : List VarId) (d : Nat) (f : VarId) (body : Expr) :
    canonicalizeAux env d (.Fix f body)
      = .Fix (canonBinder d f.hint) (canonicalizeAux (f :: env) (d + 1) body) := by
  rw [canonicalizeAux]

private theorem canonAux_app (env : List VarId) (d : Nat) (f x : Expr) :
    canonicalizeAux env d (.App f x)
      = .App (canonicalizeAux env d f) (canonicalizeAux env d x) := by
  rw [canonicalizeAux]

private theorem canonAux_force (env : List VarId) (d : Nat) (e : Expr) :
    canonicalizeAux env d (.Force e) = .Force (canonicalizeAux env d e) := by
  rw [canonicalizeAux]

private theorem canonAux_delay (env : List VarId) (d : Nat) (e : Expr) :
    canonicalizeAux env d (.Delay e) = .Delay (canonicalizeAux env d e) := by
  rw [canonicalizeAux]

private theorem canonAux_constr (env : List VarId) (d : Nat) (t : Nat) (as : List Expr) :
    canonicalizeAux env d (.Constr t as) = .Constr t (canonicalizeList env d as) := by
  rw [canonicalizeAux]

private theorem canonAux_case (env : List VarId) (d : Nat) (s : Expr) (alts : List Expr) :
    canonicalizeAux env d (.Case s alts)
      = .Case (canonicalizeAux env d s) (canonicalizeList env d alts) := by
  rw [canonicalizeAux]

private theorem canonAux_let (env : List VarId) (d : Nat)
    (binds : List (VarId × Expr × Bool)) (body : Expr) :
    canonicalizeAux env d (.Let binds body) = canonicalizeLet env d binds body := by
  rw [canonicalizeAux]

private theorem canonList_nil (env : List VarId) (d : Nat) :
    canonicalizeList env d [] = [] := by
  rw [canonicalizeList]

private theorem canonList_cons (env : List VarId) (d : Nat) (e : Expr) (es : List Expr) :
    canonicalizeList env d (e :: es)
      = canonicalizeAux env d e :: canonicalizeList env d es := by
  rw [canonicalizeList]

private theorem canonLet_nil (env : List VarId) (d : Nat) (body : Expr) :
    canonicalizeLet env d [] body = canonicalizeAux env d body := by
  rw [canonicalizeLet]

private theorem canonLet_cons (env : List VarId) (d : Nat) (x : VarId) (rhs : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) :
    canonicalizeLet env d ((x, rhs, er) :: rest) body
      = .Let [(canonBinder d x.hint, canonicalizeAux env d rhs, er)]
             (canonicalizeLet (x :: env) (d + 1) rest body) := by
  rw [canonicalizeLet]

/-! ## Idempotency

The proof strategy: define `canonEnvFrom top env` recursively, with the
invariant that position `i` gets uid `top - i`. The main mutual induction
shows that for an expression `e'` obtained by one pass of
`canonicalizeAux env d`, applying the same pass with the canonicalized
env (`canonEnv d env`) yields `e'` back.
-/

/-- canonEnvFrom top env: position 0 gets uid `top`, position 1 gets
`top - 1`, etc. -/
private def canonEnvFrom : Nat → List VarId → List VarId
  | _,   []      => []
  | top, v :: vs => canonBinder top v.hint :: canonEnvFrom (top - 1) vs

@[simp]
private theorem canonEnvFrom_nil (top : Nat) : canonEnvFrom top [] = [] := rfl

@[simp]
private theorem canonEnvFrom_cons (top : Nat) (v : VarId) (vs : List VarId) :
    canonEnvFrom top (v :: vs)
      = canonBinder top v.hint :: canonEnvFrom (top - 1) vs := rfl

@[simp]
private theorem canonEnvFrom_length (top : Nat) (env : List VarId) :
    (canonEnvFrom top env).length = env.length := by
  induction env generalizing top with
  | nil => rfl
  | cons v vs ih =>
    simp [canonEnvFrom_cons, List.length_cons, ih]

/-- The canonEnv at depth d is canonEnvFrom (d - 1). -/
private def canonEnv (d : Nat) (env : List VarId) : List VarId :=
  canonEnvFrom (d - 1) env

@[simp]
private theorem canonEnv_nil (d : Nat) : canonEnv d [] = [] := rfl

/-- canonEnv (d+1) (x :: env) = canonBinder d x.hint :: canonEnv d env. -/
private theorem canonEnv_succ_cons (d : Nat) (x : VarId) (env : List VarId) :
    canonEnv (d + 1) (x :: env) = canonBinder d x.hint :: canonEnv d env := by
  simp [canonEnv, canonEnvFrom_cons]

@[simp]
private theorem canonEnv_length (d : Nat) (env : List VarId) :
    (canonEnv d env).length = env.length := by
  simp [canonEnv]

/-! ### Var lookup properties -/

/-- BEq on VarId equals iff origin and uid match (hint ignored). -/
private theorem varid_beq_iff {a b : VarId} :
    (a == b) = true ↔ a.origin = b.origin ∧ a.uid = b.uid := by
  constructor
  · intro h
    have h' : (a.origin == b.origin && a.uid == b.uid) = true := h
    rw [Bool.and_eq_true] at h'
    obtain ⟨ho, hu⟩ := h'
    refine ⟨?_, beq_iff_eq.mp hu⟩
    generalize hka : a.origin = ka at ho
    generalize hkb : b.origin = kb at ho
    cases ka <;> cases kb
    · rfl
    · cases ho
    · cases ho
    · rfl
  · intro ⟨ho, hu⟩
    show (a.origin == b.origin && a.uid == b.uid) = true
    rw [Bool.and_eq_true]
    refine ⟨?_, beq_iff_eq.mpr hu⟩
    rw [ho]
    cases b.origin <;> rfl

/-- Two canonBinders are BEq iff they have the same uid (hints ignored). -/
private theorem canonBinder_beq_canonBinder (d1 d2 : Nat) (h1 h2 : String) :
    (canonBinder d1 h1 == canonBinder d2 h2) = true ↔ d1 = d2 := by
  rw [varid_beq_iff]
  simp [canonBinder]

/-- A VarId y matches canonBinder top h iff y has .gen origin and uid = top. -/
private theorem canonBinder_beq_varid (top : Nat) (h : String) (y : VarId) :
    (canonBinder top h == y) = true ↔ y.origin = .gen ∧ y.uid = top := by
  rw [varid_beq_iff]
  simp [canonBinder]
  constructor
  · intro ⟨ho, hu⟩; exact ⟨ho.symm, hu.symm⟩
  · intro ⟨ho, hu⟩; exact ⟨ho.symm, hu.symm⟩

/-- If `vs.findIdx? (· == x) = some i` with `vs.length ≤ top + 1`, then
`(canonEnvFrom top vs).findIdx? (· == canonBinder (top - i) hint) = some i`.
(Hint is ignored by BEq.) -/
private theorem findIdx_canonEnvFrom_some_of_findIdx
    (vs : List VarId) (top : Nat) (x : VarId) (i : Nat) (hint : String)
    (hlen : vs.length ≤ top + 1)
    (h : vs.findIdx? (· == x) = some i) :
    (canonEnvFrom top vs).findIdx? (· == canonBinder (top - i) hint) = some i := by
  induction vs generalizing i top with
  | nil =>
    simp [List.findIdx?_nil] at h
  | cons v vs' ih =>
    rw [List.length_cons] at hlen
    rw [List.findIdx?_cons] at h
    rw [canonEnvFrom_cons, List.findIdx?_cons]
    by_cases hv : (v == x) = true
    · simp [hv] at h
      subst h
      -- Need (canonBinder top v.hint == canonBinder (top - 0) hint) = true
      rw [Nat.sub_zero]
      have : (canonBinder top v.hint == canonBinder top hint) = true := by
        rw [canonBinder_beq_canonBinder]
      rw [this]
      rfl
    · simp [hv] at h
      obtain ⟨j, hj, hji⟩ := h
      subst hji
      have hjlt : j < vs'.length :=
        (List.findIdx?_eq_some_iff_findIdx_eq.mp hj).1
      have htop : vs'.length ≤ top := by omega
      have hne : top ≠ top - (j + 1) := by omega
      have hmatch : (canonBinder top v.hint == canonBinder (top - (j + 1)) hint) = false := by
        rw [Bool.eq_false_iff]
        intro habs
        have := (canonBinder_beq_canonBinder _ _ _ _).mp habs
        exact hne this
      rw [hmatch]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hlen' : vs'.length ≤ (top - 1) + 1 := by omega
      have ih_applied := ih (top := top - 1) (i := j) hlen' hj
      have heq : (top - 1) - j = top - (j + 1) := by omega
      rw [heq] at ih_applied
      rw [ih_applied]
      rfl

/-- Specialized for canonEnv d. -/
private theorem findIdx_canonEnv_some_of_findIdx
    (env : List VarId) (d : Nat) (x : VarId) (i : Nat)
    (hlen : env.length ≤ d)
    (h : env.findIdx? (· == x) = some i) :
    (canonEnv d env).findIdx? (· == canonBinder (d - 1 - i) x.hint) = some i := by
  unfold canonEnv
  have hlen' : env.length ≤ (d - 1) + 1 := by
    cases env with
    | nil => simp [List.findIdx?_nil] at h
    | cons =>
      rw [List.length_cons]
      rw [List.length_cons] at hlen
      omega
  exact findIdx_canonEnvFrom_some_of_findIdx env (d - 1) x i x.hint hlen' h

/-- If findIdx? finds a match in canonEnvFrom at position j, then the VarId
has .gen origin, uid = top - j, and j < vs.length. -/
private theorem findIdx_canonEnvFrom_gen_uid
    (vs : List VarId) (top : Nat) (y : VarId) (j : Nat)
    (h : (canonEnvFrom top vs).findIdx? (· == y) = some j) :
    y.origin = .gen ∧ y.uid = top - j ∧ j < vs.length := by
  induction vs generalizing j top with
  | nil =>
    simp at h
  | cons v vs' ih =>
    rw [canonEnvFrom_cons, List.findIdx?_cons] at h
    by_cases hb : (canonBinder top v.hint == y) = true
    · simp [hb] at h
      subst h
      have ⟨horig, huid⟩ := (canonBinder_beq_varid _ _ _).mp hb
      refine ⟨horig, ?_, ?_⟩
      · -- y.uid = top, goal is y.uid = top - 0
        rw [huid, Nat.sub_zero]
      · simp [List.length_cons]
    · simp [hb] at h
      obtain ⟨k, hk, hkj⟩ := h
      subst hkj
      have ⟨horig, huid, hklt⟩ := ih (top := top - 1) (j := k) hk
      refine ⟨horig, ?_, ?_⟩
      · rw [huid]; omega
      · rw [List.length_cons]; omega

/-- Specialized for canonEnv. -/
private theorem findIdx_canonEnv_gen_uid
    (env : List VarId) (d : Nat) (y : VarId) (j : Nat)
    (h : (canonEnv d env).findIdx? (· == y) = some j) :
    y.origin = .gen ∧ y.uid = d - 1 - j ∧ j < env.length := by
  unfold canonEnv at h
  exact findIdx_canonEnvFrom_gen_uid env (d - 1) y j h

/-! ### Idempotency: main mutual induction -/

/-- Mutual induction predicates. -/
private def IdemExpr (e : Expr) : Prop :=
  ∀ (env : List VarId) (d : Nat), env.length = d →
    canonicalizeAux (canonEnv d env) d (canonicalizeAux env d e)
      = canonicalizeAux env d e

private def IdemList (es : List Expr) : Prop :=
  ∀ (env : List VarId) (d : Nat), env.length = d →
    canonicalizeList (canonEnv d env) d (canonicalizeList env d es)
      = canonicalizeList env d es

private def IdemLet (binds : List (VarId × Expr × Bool)) (body : Expr) : Prop :=
  ∀ (env : List VarId) (d : Nat), env.length = d →
    canonicalizeAux (canonEnv d env) d (canonicalizeLet env d binds body)
      = canonicalizeLet env d binds body

/-- Key lemma for Var: idempotency under any (env, d) with env.length = d. -/
private theorem idem_var (x : VarId) : IdemExpr (.Var x) := by
  intro env d hlen
  -- canonicalizeAux env d (.Var x) = match env.findIdx? ... with | some i => ... | none => .Var x
  rw [canonAux_var]
  cases hfi : env.findIdx? (· == x) with
  | some i =>
    -- Simplify the LHS inner match
    simp only
    -- Now LHS = canonicalizeAux (canonEnv d env) d (.Var (canonBinder (d-1-i) x.hint))
    rw [canonAux_var]
    have hlen' : env.length ≤ d := by omega
    have hfind := findIdx_canonEnv_some_of_findIdx env d x i hlen' hfi
    rw [hfind]
    -- LHS = .Var (canonBinder (d - 1 - i) (canonBinder (d - 1 - i) x.hint).hint)
    -- hint is x.hint, so LHS = .Var (canonBinder (d-1-i) x.hint) = RHS
    rfl
  | none =>
    simp only
    -- LHS = canonicalizeAux (canonEnv d env) d (.Var x)
    rw [canonAux_var]
    -- LHS = match (canonEnv d env).findIdx? ... with | some j => ... | none => .Var x
    cases hfi2 : (canonEnv d env).findIdx? (· == x) with
    | none =>
      simp only
    | some j =>
      simp only
      have ⟨horig, huid, _⟩ := findIdx_canonEnv_gen_uid env d x j hfi2
      have heq : canonBinder (d - 1 - j) x.hint = x := by
        cases x with
        | mk xuid xorigin xhint =>
          simp only [canonBinder] at horig huid ⊢
          rcases huid with rfl
          rcases horig with rfl
          rfl
      rw [heq]

/-- Main mutual induction by strong induction on size. -/
private theorem canonicalize_idem_main :
    (∀ e : Expr, IdemExpr e) ∧
    (∀ es : List Expr, IdemList es) ∧
    (∀ binds body, IdemLet binds body) := by
  suffices h : ∀ n : Nat,
      (∀ e : Expr, sizeOf e ≤ n → IdemExpr e) ∧
      (∀ es : List Expr, sizeOf es ≤ n → IdemList es) ∧
      (∀ binds body, sizeOf binds + sizeOf body ≤ n → IdemLet binds body) by
    refine ⟨?_, ?_, ?_⟩
    · intro e; exact (h (sizeOf e)).1 e (Nat.le_refl _)
    · intro es; exact (h (sizeOf es)).2.1 es (Nat.le_refl _)
    · intro binds body; exact (h (sizeOf binds + sizeOf body)).2.2 binds body (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro e hsz
      cases e <;> simp at hsz
    · intro es hsz
      cases es with
      | nil =>
        intro env d _hlen
        rw [canonList_nil, canonList_nil]
      | cons _ _ => simp at hsz
    · intro binds body hsz
      -- sizeOf binds + sizeOf body ≤ 0 is impossible since sizeOf body ≥ 1
      exfalso
      have : sizeOf body ≥ 1 := by cases body <;> simp <;> omega
      omega
  | succ n ih =>
    obtain ⟨ihExpr, ihList, ihLet⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · -- ∀ e, sizeOf e ≤ n+1 → IdemExpr e
      intro e hsz
      cases e with
      | Var x => exact idem_var x
      | Lit c =>
        intro env d _hlen
        rw [canonAux_lit, canonAux_lit]
      | Builtin b =>
        intro env d _hlen
        rw [canonAux_builtin, canonAux_builtin]
      | Error =>
        intro env d _hlen
        rw [canonAux_error, canonAux_error]
      | Lam x body =>
        intro env d hlen
        rw [canonAux_lam]
        -- LHS: canonicalizeAux (canonEnv d env) d (.Lam (canonBinder d x.hint) body')
        rw [canonAux_lam]
        -- = .Lam (canonBinder d (canonBinder d x.hint).hint) (canonicalizeAux ((canonBinder d x.hint) :: canonEnv d env) (d+1) body')
        have hhint : (canonBinder d x.hint).hint = x.hint := rfl
        rw [hhint]
        congr 1
        rw [← canonEnv_succ_cons]
        have hbsz : sizeOf body ≤ n := by
          have : sizeOf (Expr.Lam x body) = 1 + sizeOf x + sizeOf body := by simp
          omega
        have ihbody := ihExpr body hbsz
        have hbody_hyp : (x :: env).length = d + 1 := by
          rw [List.length_cons]; omega
        exact ihbody (x :: env) (d + 1) hbody_hyp
      | Fix f body =>
        intro env d hlen
        rw [canonAux_fix]
        rw [canonAux_fix]
        have hhint : (canonBinder d f.hint).hint = f.hint := rfl
        rw [hhint]
        congr 1
        rw [← canonEnv_succ_cons]
        have hbsz : sizeOf body ≤ n := by
          have : sizeOf (Expr.Fix f body) = 1 + sizeOf f + sizeOf body := by simp
          omega
        have ihbody := ihExpr body hbsz
        have hbody_hyp : (f :: env).length = d + 1 := by
          rw [List.length_cons]; omega
        exact ihbody (f :: env) (d + 1) hbody_hyp
      | App f x =>
        intro env d hlen
        rw [canonAux_app]
        rw [canonAux_app]
        have hfsz : sizeOf f ≤ n := by
          have : sizeOf (Expr.App f x) = 1 + sizeOf f + sizeOf x := by simp
          omega
        have hxsz : sizeOf x ≤ n := by
          have : sizeOf (Expr.App f x) = 1 + sizeOf f + sizeOf x := by simp
          omega
        congr 1
        · exact ihExpr f hfsz env d hlen
        · exact ihExpr x hxsz env d hlen
      | Force e =>
        intro env d hlen
        rw [canonAux_force]
        rw [canonAux_force]
        have hesz : sizeOf e ≤ n := by
          have : sizeOf (Expr.Force e) = 1 + sizeOf e := by simp
          omega
        congr 1
        exact ihExpr e hesz env d hlen
      | Delay e =>
        intro env d hlen
        rw [canonAux_delay]
        rw [canonAux_delay]
        have hesz : sizeOf e ≤ n := by
          have : sizeOf (Expr.Delay e) = 1 + sizeOf e := by simp
          omega
        congr 1
        exact ihExpr e hesz env d hlen
      | Constr t as =>
        intro env d hlen
        rw [canonAux_constr]
        rw [canonAux_constr]
        have hsz' : sizeOf as ≤ n := by
          have : sizeOf (Expr.Constr t as) = 1 + sizeOf t + sizeOf as := by simp
          omega
        congr 1
        exact ihList as hsz' env d hlen
      | Case s alts =>
        intro env d hlen
        rw [canonAux_case]
        rw [canonAux_case]
        have hssz : sizeOf s ≤ n := by
          have : sizeOf (Expr.Case s alts) = 1 + sizeOf s + sizeOf alts := by simp
          omega
        have haltsz : sizeOf alts ≤ n := by
          have : sizeOf (Expr.Case s alts) = 1 + sizeOf s + sizeOf alts := by simp
          omega
        congr 1
        · exact ihExpr s hssz env d hlen
        · exact ihList alts haltsz env d hlen
      | Let binds body =>
        intro env d hlen
        rw [canonAux_let]
        have hsz' : sizeOf binds + sizeOf body ≤ n := by
          have : sizeOf (Expr.Let binds body) = 1 + sizeOf binds + sizeOf body := by simp
          omega
        exact ihLet binds body hsz' env d hlen
    · -- List
      intro es hsz
      cases es with
      | nil =>
        intro env d _hlen
        rw [canonList_nil, canonList_nil]
      | cons e es' =>
        intro env d hlen
        rw [canonList_cons]
        rw [canonList_cons]
        have hesz : sizeOf e ≤ n := by
          have : sizeOf (e :: es') = 1 + sizeOf e + sizeOf es' := by simp
          omega
        have hes'sz : sizeOf es' ≤ n := by
          have : sizeOf (e :: es') = 1 + sizeOf e + sizeOf es' := by simp
          omega
        congr 1
        · exact ihExpr e hesz env d hlen
        · exact ihList es' hes'sz env d hlen
    · -- Let
      intro binds body hsz
      cases binds with
      | nil =>
        intro env d hlen
        rw [canonLet_nil]
        have hbsz : sizeOf body ≤ n := by
          have : sizeOf (([] : List (VarId × Expr × Bool))) + sizeOf body
              = 1 + sizeOf body := by simp
          omega
        exact ihExpr body hbsz env d hlen
      | cons head rest =>
        intro env d hlen
        obtain ⟨x, rhs, er⟩ := head
        rw [canonLet_cons]
        rw [canonAux_let]
        rw [canonLet_cons]
        rw [canonLet_nil]
        have hhint : (canonBinder d x.hint).hint = x.hint := rfl
        rw [hhint]
        have hrsz : sizeOf rhs ≤ n := by
          have hhead : sizeOf ((x, rhs, er) :: rest) + sizeOf body
              = 1 + sizeOf (x, rhs, er) + sizeOf rest + sizeOf body := by simp
          have hprod : sizeOf (x, rhs, er) = 1 + sizeOf x + (1 + sizeOf rhs + sizeOf er) := by simp
          omega
        have hrest_sz : sizeOf rest + sizeOf body ≤ n := by
          have hhead : sizeOf ((x, rhs, er) :: rest) + sizeOf body
              = 1 + sizeOf (x, rhs, er) + sizeOf rest + sizeOf body := by simp
          omega
        have hlen_ext : (x :: env).length = d + 1 := by
          rw [List.length_cons]; omega
        have hrhs := ihExpr rhs hrsz env d hlen
        have hsub := ihLet rest body hrest_sz (x :: env) (d + 1) hlen_ext
        -- Target: .Let [(canonBinder d x.hint, canonicalizeAux (canonEnv d env) d (canonicalizeAux env d rhs), er)]
        --             (canonicalizeAux ((canonBinder d x.hint) :: canonEnv d env) (d + 1) ...)
        --        = .Let [(canonBinder d x.hint, canonicalizeAux env d rhs, er)]
        --             (canonicalizeLet (x :: env) (d + 1) rest body)
        rw [hrhs]
        rw [← canonEnv_succ_cons]
        rw [hsub]

/-- Main idempotency theorem. -/
theorem canonicalize_idempotent (e : Expr) :
    canonicalize (canonicalize e) = canonicalize e := by
  have := canonicalize_idem_main.1 e [] 0 (by simp)
  have hnil : canonEnv 0 ([] : List VarId) = [] := rfl
  rw [hnil] at this
  unfold canonicalize
  exact this

/-! # Source-only invariant and `lowerTotal_canonicalize` preservation

We prove that `canonicalize` preserves `lowerTotal` behavior for expressions
whose free variables are all `.source`-origin. This is the "source-only
invariant": user-written / elaborator-produced expressions have `.source`
free variables, and `.gen` origin is only introduced by internal passes
(such as `canonicalize` itself or `expandFix`) to name fresh bound binders.

Because BEq treats `.gen` and `.source` as distinct, the `.gen` canon
binders introduced inside `canonicalize e` never accidentally match free
(`.source`) variables in the outer env, and the free variables themselves
pass through canonicalization unchanged.
-/

/-- All free variables of `e` have `.source` origin. -/
def allFreeVarsSource (e : Expr) : Prop :=
  ∀ y : VarId, (freeVars e).contains y = true → y.origin = .source

/-- All free variables of `es` (as a list) have `.source` origin. -/
def allFreeVarsSourceList (es : List Expr) : Prop :=
  ∀ y : VarId, (freeVarsList es).contains y = true → y.origin = .source

/-- All free variables of the Let-chain `binds body` have `.source` origin. -/
def allFreeVarsSourceLet (binds : List (VarId × Expr × Bool)) (body : Expr) : Prop :=
  ∀ y : VarId, (freeVarsLet binds body).contains y = true → y.origin = .source

/-! ### `envLookupT.go` append lemmas -/

/-- If `v` is not found in `env` (starting from offset `n`), then looking up
`v` in `env ++ env'` behaves like looking up in `env'` with the shifted offset. -/
private theorem envLookupT.go_append_none (v : VarId) (env env' : List VarId) (n : Nat)
    (h : envLookupT.go v env n = none) :
    envLookupT.go v (env ++ env') n = envLookupT.go v env' (n + env.length) := by
  induction env generalizing n with
  | nil => simp [envLookupT.go] at h ⊢
  | cons y rest ih =>
    rw [List.cons_append]
    simp only [envLookupT.go] at h ⊢
    by_cases hyv : (y == v) = true
    · rw [show (y == v) = true from hyv] at h
      exact absurd h (by simp)
    · have hyv' : (y == v) = false := by
        cases hh : (y == v); rfl; exact absurd hh hyv
      rw [show (y == v) = false from hyv']
      rw [show (y == v) = false from hyv'] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      have := ih (n + 1) h
      rw [this, List.length_cons]
      have heq : n + 1 + rest.length = n + (rest.length + 1) := by omega
      rw [heq]

/-- If `v` is found in `env` at offset `n+i`, lookup in `env ++ env'` gives
the same result. -/
private theorem envLookupT.go_append_some (v : VarId) (env env' : List VarId)
    (n idx : Nat) (h : envLookupT.go v env n = some idx) :
    envLookupT.go v (env ++ env') n = some idx := by
  induction env generalizing n with
  | nil => simp [envLookupT.go] at h
  | cons y rest ih =>
    rw [List.cons_append]
    simp only [envLookupT.go] at h ⊢
    by_cases hyv : (y == v) = true
    · rw [show (y == v) = true from hyv] at h
      rw [show (y == v) = true from hyv]
      simp only at h ⊢
      exact h
    · have hyv' : (y == v) = false := by
        cases hh : (y == v); rfl; exact absurd hh hyv
      rw [show (y == v) = false from hyv'] at h
      rw [show (y == v) = false from hyv']
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact ih (n + 1) h

/-- `envLookupT.go v env 0 = env.findIdx? (· == v)`. Both walk the list and
return the first index matching `· == v`. -/
private theorem envLookupT.go_eq_findIdx? (v : VarId) (env : List VarId) :
    envLookupT.go v env 0 = env.findIdx? (· == v) := by
  have key : ∀ (env : List VarId) (n : Nat),
      envLookupT.go v env n = (env.findIdx? (· == v)).map (· + n) := by
    intro env
    induction env with
    | nil => intro n; simp [envLookupT.go, List.findIdx?_nil]
    | cons y rest ih =>
      intro n
      simp only [envLookupT.go, List.findIdx?_cons]
      by_cases hyv : (y == v) = true
      · simp [hyv]
      · have hyv' : (y == v) = false := by
          cases hh : (y == v)
          · rfl
          · exact absurd hh hyv
        simp only [hyv']
        rw [ih (n + 1)]
        simp only [ite_false, Bool.false_eq_true]
        cases hfi : rest.findIdx? (· == v) with
        | none => simp
        | some j =>
          simp only [Option.map]
          congr 1
          omega
  rw [key]
  cases h : env.findIdx? (· == v) <;> simp

/-- Reformulation: `envLookupT env v = env.findIdx? (· == v)`. -/
private theorem envLookupT_eq_findIdx? (env : List VarId) (v : VarId) :
    envLookupT env v = env.findIdx? (· == v) := by
  unfold envLookupT
  exact envLookupT.go_eq_findIdx? v env

/-! ### VarSet union/insert helpers (forward direction) -/

/-- BEq transitivity lifted to List.any. (Local copy — the same lemma is
private in `LowerTotal`.) -/
private theorem list_any_beq_varid_trans (xs : List VarId) (v x : VarId)
    (hvx : (v == x) = true) (hv : xs.any (· == v) = true) : xs.any (· == x) = true := by
  induction xs with
  | nil => simp at hv
  | cons h t ih =>
    simp only [List.any_cons, Bool.or_eq_true] at *
    cases hv with
    | inl hl =>
      left
      rw [varid_beq_iff] at hvx hl ⊢
      exact ⟨hl.1.trans hvx.1, hl.2.trans hvx.2⟩
    | inr hr => exact .inr (ih hr)

/-- `insert` preserves `contains`-true: if `s.contains y = true`, then
`(s.insert v).contains y = true`. -/
private theorem VarSet.insert_contains_of_contains (s : VarSet) (v y : VarId)
    (h : s.contains y = true) :
    (s.insert v).contains y = true := by
  unfold VarSet.insert
  split
  · exact h
  · -- Array push case
    unfold VarSet.contains
    rw [← Array.any_toList, Array.toList_push, List.any_append,
        List.any_cons, List.any_nil, Bool.or_false]
    unfold VarSet.contains at h
    rw [← Array.any_toList] at h
    simp [h]

/-- For folded insert, `contains` persists through the fold. -/
private theorem VarSet.foldl_list_insert_contains_of_contains_left :
    ∀ (elems : List VarId) (acc : VarSet) (y : VarId),
      acc.contains y = true →
      (elems.foldl (fun a v => a.insert v) acc).contains y = true
  | [], _, _, h => h
  | v :: rest, acc, y, h => by
    simp only [List.foldl_cons]
    exact VarSet.foldl_list_insert_contains_of_contains_left rest _ y
      (VarSet.insert_contains_of_contains acc v y h)

/-- If `y` matches some element of `elems`, then folded insert contains `y`. -/
private theorem VarSet.foldl_list_insert_contains_of_mem :
    ∀ (elems : List VarId) (acc : VarSet) (y : VarId),
      elems.any (· == y) = true →
      (elems.foldl (fun a v => a.insert v) acc).contains y = true
  | [], _, _, h => by simp at h
  | v :: rest, acc, y, h => by
    simp only [List.foldl_cons]
    simp only [List.any_cons, Bool.or_eq_true] at h
    cases h with
    | inl hv =>
      -- v == y, so v is inserted; then fold preserves contains y
      apply VarSet.foldl_list_insert_contains_of_contains_left
      -- (acc.insert v).contains y = true when (v == y) = true
      unfold VarSet.insert
      split
      · rename_i hsv
        unfold VarSet.contains at hsv
        rw [← Array.any_toList] at hsv
        unfold VarSet.contains
        rw [← Array.any_toList]
        exact list_any_beq_varid_trans acc.data.toList v y hv hsv
      · unfold VarSet.contains
        rw [← Array.any_toList, Array.toList_push, List.any_append,
            List.any_cons, List.any_nil, Bool.or_false]
        simp [hv]
    | inr hrest =>
      exact VarSet.foldl_list_insert_contains_of_mem rest _ y hrest

/-- If `s2` contains `y`, the union `s1.union s2` also contains `y`. -/
private theorem VarSet.union_contains_of_contains_right (s1 s2 : VarSet) (y : VarId)
    (h : s2.contains y = true) :
    (s1.union s2).contains y = true := by
  unfold VarSet.union
  rw [← Array.foldl_toList]
  apply VarSet.foldl_list_insert_contains_of_mem
  unfold VarSet.contains at h
  rwa [← Array.any_toList] at h

/-- If `s1` contains `y`, the union `s1.union s2` also contains `y`. -/
private theorem VarSet.union_contains_of_contains_left (s1 s2 : VarSet) (y : VarId)
    (h : s1.contains y = true) :
    (s1.union s2).contains y = true := by
  unfold VarSet.union
  rw [← Array.foldl_toList]
  exact VarSet.foldl_list_insert_contains_of_contains_left s2.data.toList s1 y h

/-- Core list-level: if `L.any (· == y) = true` and `(x == y) = false`,
then `(L.filter (· != x)).any (· == y) = true`. -/
private theorem list_any_filter_other (L : List VarId) (x y : VarId)
    (hcontains : L.any (· == y) = true) (hxy : (x == y) = false) :
    (L.filter (· != x)).any (· == y) = true := by
  induction L with
  | nil => exact absurd hcontains (by simp)
  | cons w rest ih =>
    simp only [List.any_cons, Bool.or_eq_true] at hcontains
    simp only [List.filter_cons]
    by_cases hwy : (w == y) = true
    · -- w matches y; we need w kept by filter. Show w != x.
      have hwx : (w != x) = true := by
        simp only [bne, Bool.not_eq_true']
        cases hwx2 : (w == x) with
        | false => rfl
        | true =>
          exfalso
          -- Contradiction: w == x and w == y would give x == y.
          have h1 : (x == y) = true := by
            rw [varid_beq_iff] at hwx2 hwy
            rw [varid_beq_iff]
            exact ⟨hwx2.1.symm.trans hwy.1, hwx2.2.symm.trans hwy.2⟩
          rw [h1] at hxy; exact Bool.noConfusion hxy
      rw [show (w != x) = true from hwx]; simp only [ite_true, List.any_cons]
      simp [hwy]
    · -- w doesn't match y; premise is in rest; recurse
      have hwy_f : (w == y) = false := by
        cases hh : (w == y); rfl; exact absurd hh hwy
      have hrest : rest.any (· == y) = true := by
        cases hcontains with
        | inl h => exact absurd h hwy
        | inr h => exact h
      by_cases hwx : (w != x) = true
      · simp only [hwx, ite_true, List.any_cons, hwy_f, Bool.false_or]
        exact ih hrest
      · simp only [show (w != x) = false from by cases hh : (w != x); rfl; exact absurd hh hwx]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ih hrest

/-- If `s` contains `y` and `y ≠ x` (in BEq), then `(s.erase x)` still contains `y`. -/
private theorem VarSet.erase_other_contains (s : VarSet) (x y : VarId)
    (hcontains : s.contains y = true) (hxy : (x == y) = false) :
    (s.erase x).contains y = true := by
  unfold VarSet.erase VarSet.contains
  rw [← Array.any_toList, Array.toList_filter]
  unfold VarSet.contains at hcontains
  rw [← Array.any_toList] at hcontains
  exact list_any_filter_other s.data.toList x y hcontains hxy

/-! ### canonEnv never matches a `.source` VarId -/

/-- Every element of `canonEnvFrom top env` has `.gen` origin. -/
private theorem canonEnvFrom_elements_gen (top : Nat) (env : List VarId)
    (y : VarId) (h : y ∈ canonEnvFrom top env) : y.origin = .gen := by
  induction env generalizing top with
  | nil => simp [canonEnvFrom_nil] at h
  | cons v vs ih =>
    rw [canonEnvFrom_cons] at h
    cases h with
    | head _ => rfl
    | tail _ htl => exact ih (top - 1) htl

/-- Every element of `canonEnv d env` has `.gen` origin. -/
private theorem canonEnv_elements_gen (d : Nat) (env : List VarId)
    (y : VarId) (h : y ∈ canonEnv d env) : y.origin = .gen := by
  unfold canonEnv at h
  exact canonEnvFrom_elements_gen (d - 1) env y h

/-- If `x.origin = .source`, then `x` is not found in `canonEnv d env`. -/
private theorem findIdx_canonEnv_none_of_source (env : List VarId) (d : Nat)
    (x : VarId) (hx : x.origin = .source) :
    (canonEnv d env).findIdx? (· == x) = none := by
  induction env generalizing d with
  | nil => simp [canonEnv, canonEnvFrom_nil, List.findIdx?_nil]
  | cons v vs ih =>
    rw [canonEnv, canonEnvFrom_cons, List.findIdx?_cons]
    have hne : (canonBinder (d - 1) v.hint == x) = false := by
      rw [Bool.eq_false_iff]
      intro habs
      have := (canonBinder_beq_varid _ _ _).mp habs
      rw [hx] at this
      exact VarOrigin.noConfusion this.1
    rw [hne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have ih' := ih (d := d - 1)
    rw [canonEnv] at ih'
    cases hfi : canonEnvFrom (d - 1 - 1) vs |>.findIdx? (· == x) with
    | none => simp
    | some j =>
      rw [hfi] at ih'
      exact absurd ih' (by simp)

/-! ### Free-var source-hypothesis preservation under binder descent -/

/-- If `(freeVars e).contains y → env.findIdx? = none → y.origin = .source`,
then for body of `.Lam x body`, the same property holds with env = `x :: env`. -/
private theorem hfv_descend_lam (env : List VarId) (x : VarId) (body : Expr)
    (hfv : ∀ y, (freeVars (.Lam x body)).contains y = true →
              env.findIdx? (· == y) = none → y.origin = .source) :
    ∀ y, (freeVars body).contains y = true →
        (x :: env).findIdx? (· == y) = none → y.origin = .source := by
  intro y hy hfi
  rw [List.findIdx?_cons] at hfi
  have hxy : (x == y) = false := by
    cases hxy : (x == y) with
    | true => rw [hxy] at hfi; simp at hfi
    | false => rfl
  rw [hxy] at hfi
  simp only [Bool.false_eq_true, ↓reduceIte] at hfi
  have henv : env.findIdx? (· == y) = none := by
    cases hfi' : env.findIdx? (· == y) with
    | none => rfl
    | some j =>
      rw [hfi'] at hfi
      simp at hfi
  -- Show y in freeVars (.Lam x body), which = (freeVars body).erase x
  apply hfv
  · rw [freeVars.eq_5]
    exact VarSet.erase_other_contains _ _ _ hy hxy
  · exact henv

-- Helper: mirror for .Fix
private theorem hfv_descend_fix (env : List VarId) (f : VarId) (body : Expr)
    (hfv : ∀ y, (freeVars (.Fix f body)).contains y = true →
              env.findIdx? (· == y) = none → y.origin = .source) :
    ∀ y, (freeVars body).contains y = true →
        (f :: env).findIdx? (· == y) = none → y.origin = .source := by
  intro y hy hfi
  rw [List.findIdx?_cons] at hfi
  have hfy : (f == y) = false := by
    cases hfy : (f == y) with
    | true => rw [hfy] at hfi; simp at hfi
    | false => rfl
  rw [hfy] at hfi
  simp only [Bool.false_eq_true, ↓reduceIte] at hfi
  have henv : env.findIdx? (· == y) = none := by
    cases hfi' : env.findIdx? (· == y) with
    | none => rfl
    | some j =>
      rw [hfi'] at hfi
      simp at hfi
  apply hfv
  · rw [freeVars.eq_6]
    exact VarSet.erase_other_contains _ _ _ hy hfy
  · exact henv

/-! ### Main theorem: `lowerTotal_canonicalize` via mutual induction -/

/-- Predicate: for fixed env_orig/d, the canonicalize-eq statement holds. -/
private def LowerCanon (e : Expr) : Prop :=
  ∀ (env_outer env_orig : List VarId) (d : Nat),
    env_orig.length = d →
    (∀ y, (freeVars e).contains y = true →
        env_orig.findIdx? (· == y) = none → y.origin = .source) →
    lowerTotal (canonEnv d env_orig ++ env_outer) (canonicalizeAux env_orig d e)
      = lowerTotal (env_orig ++ env_outer) e

private def LowerCanonList (es : List Expr) : Prop :=
  ∀ (env_outer env_orig : List VarId) (d : Nat),
    env_orig.length = d →
    (∀ y, (freeVarsList es).contains y = true →
        env_orig.findIdx? (· == y) = none → y.origin = .source) →
    lowerTotalList (canonEnv d env_orig ++ env_outer) (canonicalizeList env_orig d es)
      = lowerTotalList (env_orig ++ env_outer) es

private def LowerCanonLet (binds : List (VarId × Expr × Bool)) (body : Expr) : Prop :=
  ∀ (env_outer env_orig : List VarId) (d : Nat),
    env_orig.length = d →
    (∀ y, (freeVarsLet binds body).contains y = true →
        env_orig.findIdx? (· == y) = none → y.origin = .source) →
    lowerTotal (canonEnv d env_orig ++ env_outer) (canonicalizeLet env_orig d binds body)
      = lowerTotalLet (env_orig ++ env_outer) binds body

/-- Var case. -/
private theorem lowerCanon_var (x : VarId) : LowerCanon (.Var x) := by
  intro env_outer env_orig d hlen hfv
  rw [canonAux_var]
  cases hfi : env_orig.findIdx? (· == x) with
  | some i =>
    -- Bound case: canonicalizeAux produces .Var (canonBinder (d-1-i) x.hint)
    simp only
    rw [lowerTotal.eq_1, lowerTotal.eq_1]
    have hi : i < env_orig.length := by
      have := List.findIdx?_eq_some_iff_findIdx_eq.mp hfi
      exact this.1
    have hlen_le : env_orig.length ≤ d := by omega
    have hcanon_find : (canonEnv d env_orig).findIdx? (· == canonBinder (d - 1 - i) x.hint) = some i :=
      findIdx_canonEnv_some_of_findIdx env_orig d x i hlen_le hfi
    -- Convert findIdx? to envLookupT.go 0
    have hcanon_go : envLookupT.go (canonBinder (d - 1 - i) x.hint) (canonEnv d env_orig) 0 = some i := by
      rw [envLookupT.go_eq_findIdx?]
      exact hcanon_find
    have hcanon_full : envLookupT (canonEnv d env_orig ++ env_outer) (canonBinder (d - 1 - i) x.hint) = some i := by
      unfold envLookupT
      exact envLookupT.go_append_some _ _ _ _ _ hcanon_go
    rw [hcanon_full]
    -- RHS: lookup x in env_orig ++ env_outer
    have horig_go : envLookupT.go x env_orig 0 = some i := by
      rw [envLookupT.go_eq_findIdx?]
      exact hfi
    have horig_full : envLookupT (env_orig ++ env_outer) x = some i := by
      unfold envLookupT
      exact envLookupT.go_append_some _ _ _ _ _ horig_go
    rw [horig_full]
  | none =>
    -- Free case: x is not in env_orig; canonicalizeAux returns .Var x
    simp only
    rw [lowerTotal.eq_1, lowerTotal.eq_1]
    have hx_src : x.origin = .source := by
      apply hfv x
      · rw [freeVars.eq_1, VarSet.singleton_contains']
        show (x == x) = true
        rw [varid_beq_iff]; exact ⟨rfl, rfl⟩
      · exact hfi
    -- LHS lookup: goes through canonEnv (none) then env_outer
    have hcanon_none : envLookupT.go x (canonEnv d env_orig) 0 = none := by
      rw [envLookupT.go_eq_findIdx?]
      exact findIdx_canonEnv_none_of_source env_orig d x hx_src
    have hcanon_full : envLookupT (canonEnv d env_orig ++ env_outer) x
        = envLookupT.go x env_outer (0 + (canonEnv d env_orig).length) := by
      unfold envLookupT
      exact envLookupT.go_append_none _ _ _ _ hcanon_none
    -- RHS lookup: goes through env_orig (none) then env_outer
    have horig_none : envLookupT.go x env_orig 0 = none := by
      rw [envLookupT.go_eq_findIdx?]
      exact hfi
    have horig_full : envLookupT (env_orig ++ env_outer) x
        = envLookupT.go x env_outer (0 + env_orig.length) := by
      unfold envLookupT
      exact envLookupT.go_append_none _ _ _ _ horig_none
    rw [hcanon_full, horig_full]
    -- (canonEnv d env_orig).length = env_orig.length
    rw [canonEnv_length]

/-- Lit case (trivial). -/
private theorem lowerCanon_lit (c : Moist.Plutus.Term.Const × Moist.Plutus.Term.BuiltinType) :
    LowerCanon (.Lit c) := by
  intro env_outer env_orig d _ _
  rw [canonAux_lit]
  obtain ⟨c1, ty⟩ := c
  simp only [lowerTotal.eq_2]

/-- Builtin case (trivial). -/
private theorem lowerCanon_builtin (b : Moist.Plutus.Term.BuiltinFun) :
    LowerCanon (.Builtin b) := by
  intro env_outer env_orig d _ _
  rw [canonAux_builtin]
  simp only [lowerTotal.eq_3]

/-- Error case (trivial). -/
private theorem lowerCanon_error : LowerCanon (Expr.Error) := by
  intro env_outer env_orig d _ _
  rw [canonAux_error]
  simp only [lowerTotal.eq_4]

/-- Fix case: both sides reduce to none. -/
private theorem lowerCanon_fix (f : VarId) (body : Expr) : LowerCanon (.Fix f body) := by
  intro env_outer env_orig d _ _
  rw [canonAux_fix]
  simp only [lowerTotal.eq_12]

/-- Lam case: descend into body with extended env. -/
private theorem lowerCanon_lam (x : VarId) (body : Expr) (ih : LowerCanon body) :
    LowerCanon (.Lam x body) := by
  intro env_outer env_orig d hlen hfv
  rw [canonAux_lam]
  rw [lowerTotal.eq_5, lowerTotal.eq_5]
  -- Apply IH with env_orig' = x :: env_orig, d' = d + 1.
  have hlen' : (x :: env_orig).length = d + 1 := by
    rw [List.length_cons]; omega
  have hfv' : ∀ y, (freeVars body).contains y = true →
                  (x :: env_orig).findIdx? (· == y) = none → y.origin = .source :=
    hfv_descend_lam env_orig x body hfv
  have ih_applied := ih env_outer (x :: env_orig) (d + 1) hlen' hfv'
  -- canonEnv (d+1) (x :: env_orig) = canonBinder d x.hint :: canonEnv d env_orig
  rw [canonEnv_succ_cons] at ih_applied
  -- Normalize: `a :: b ++ c = (a :: b) ++ c = a :: (b ++ c)` via List.cons_append.
  rw [List.cons_append] at ih_applied
  rw [List.cons_append] at ih_applied
  rw [ih_applied]

/-- Force case. -/
private theorem lowerCanon_force (e : Expr) (ih : LowerCanon e) :
    LowerCanon (.Force e) := by
  intro env_outer env_orig d hlen hfv
  rw [canonAux_force]
  rw [lowerTotal.eq_7, lowerTotal.eq_7]
  have hfv' : ∀ y, (freeVars e).contains y = true →
                  env_orig.findIdx? (· == y) = none → y.origin = .source := by
    intro y hy hfi
    apply hfv y
    · rw [freeVars.eq_8]; exact hy
    · exact hfi
  rw [ih env_outer env_orig d hlen hfv']

/-- Delay case. -/
private theorem lowerCanon_delay (e : Expr) (ih : LowerCanon e) :
    LowerCanon (.Delay e) := by
  intro env_outer env_orig d hlen hfv
  rw [canonAux_delay]
  rw [lowerTotal.eq_8, lowerTotal.eq_8]
  have hfv' : ∀ y, (freeVars e).contains y = true →
                  env_orig.findIdx? (· == y) = none → y.origin = .source := by
    intro y hy hfi
    apply hfv y
    · rw [freeVars.eq_9]; exact hy
    · exact hfi
  rw [ih env_outer env_orig d hlen hfv']

/-- App case. -/
private theorem lowerCanon_app (f a : Expr) (ihf : LowerCanon f) (iha : LowerCanon a) :
    LowerCanon (.App f a) := by
  intro env_outer env_orig d hlen hfv
  rw [canonAux_app]
  rw [lowerTotal.eq_6, lowerTotal.eq_6]
  have hff : ∀ y, (freeVars f).contains y = true →
                 env_orig.findIdx? (· == y) = none → y.origin = .source := by
    intro y hy hfi
    apply hfv y
    · rw [freeVars.eq_7]
      exact VarSet.union_contains_of_contains_left _ _ _ hy
    · exact hfi
  have hfa : ∀ y, (freeVars a).contains y = true →
                 env_orig.findIdx? (· == y) = none → y.origin = .source := by
    intro y hy hfi
    apply hfv y
    · rw [freeVars.eq_7]
      exact VarSet.union_contains_of_contains_right _ _ _ hy
    · exact hfi
  rw [ihf env_outer env_orig d hlen hff, iha env_outer env_orig d hlen hfa]

/-- Constr case. Uses list induction. -/
private theorem lowerCanon_constr (t : Nat) (as : List Expr) (ih : LowerCanonList as) :
    LowerCanon (.Constr t as) := by
  intro env_outer env_orig d hlen hfv
  rw [canonAux_constr]
  rw [lowerTotal.eq_9, lowerTotal.eq_9]
  have hfv' : ∀ y, (freeVarsList as).contains y = true →
                  env_orig.findIdx? (· == y) = none → y.origin = .source := by
    intro y hy hfi
    apply hfv y
    · rw [freeVars.eq_10]; exact hy
    · exact hfi
  rw [ih env_outer env_orig d hlen hfv']

/-- Case case (scrutinee + alts). -/
private theorem lowerCanon_case (s : Expr) (alts : List Expr)
    (ihs : LowerCanon s) (iha : LowerCanonList alts) :
    LowerCanon (.Case s alts) := by
  intro env_outer env_orig d hlen hfv
  rw [canonAux_case]
  rw [lowerTotal.eq_10, lowerTotal.eq_10]
  have hfvs : ∀ y, (freeVars s).contains y = true →
                  env_orig.findIdx? (· == y) = none → y.origin = .source := by
    intro y hy hfi
    apply hfv y
    · rw [freeVars.eq_11]
      exact VarSet.union_contains_of_contains_left _ _ _ hy
    · exact hfi
  have hfva : ∀ y, (freeVarsList alts).contains y = true →
                  env_orig.findIdx? (· == y) = none → y.origin = .source := by
    intro y hy hfi
    apply hfv y
    · rw [freeVars.eq_11]
      exact VarSet.union_contains_of_contains_right _ _ _ hy
    · exact hfi
  rw [ihs env_outer env_orig d hlen hfvs, iha env_outer env_orig d hlen hfva]

/-- Let case (dispatches to Let-specific lemma). -/
private theorem lowerCanon_let (binds : List (VarId × Expr × Bool)) (body : Expr)
    (ih : LowerCanonLet binds body) : LowerCanon (.Let binds body) := by
  intro env_outer env_orig d hlen hfv
  rw [canonAux_let]
  rw [lowerTotal.eq_11]
  have hfv' : ∀ y, (freeVarsLet binds body).contains y = true →
                  env_orig.findIdx? (· == y) = none → y.origin = .source := by
    intro y hy hfi
    apply hfv y
    · rw [freeVars.eq_12]; exact hy
    · exact hfi
  exact ih env_outer env_orig d hlen hfv'

/-! ### List-level and Let-level cases -/

/-- List nil. -/
private theorem lowerCanonList_nil : LowerCanonList [] := by
  intro env_outer env_orig d _ _
  rw [canonList_nil]
  simp only [lowerTotalList.eq_1]

/-- List cons. -/
private theorem lowerCanonList_cons (e : Expr) (es : List Expr)
    (ihe : LowerCanon e) (ihes : LowerCanonList es) : LowerCanonList (e :: es) := by
  intro env_outer env_orig d hlen hfv
  rw [canonList_cons]
  rw [lowerTotalList.eq_2, lowerTotalList.eq_2]
  have hfve : ∀ y, (freeVars e).contains y = true →
                  env_orig.findIdx? (· == y) = none → y.origin = .source := by
    intro y hy hfi
    apply hfv y
    · rw [freeVarsList.eq_2]
      exact VarSet.union_contains_of_contains_left _ _ _ hy
    · exact hfi
  have hfves : ∀ y, (freeVarsList es).contains y = true →
                   env_orig.findIdx? (· == y) = none → y.origin = .source := by
    intro y hy hfi
    apply hfv y
    · rw [freeVarsList.eq_2]
      exact VarSet.union_contains_of_contains_right _ _ _ hy
    · exact hfi
  rw [ihe env_outer env_orig d hlen hfve, ihes env_outer env_orig d hlen hfves]

/-- Let nil: defers to the body expression. -/
private theorem lowerCanonLet_nil (body : Expr) (ih : LowerCanon body) :
    LowerCanonLet [] body := by
  intro env_outer env_orig d hlen hfv
  rw [canonLet_nil]
  rw [lowerTotalLet.eq_1]
  have hfv' : ∀ y, (freeVars body).contains y = true →
                  env_orig.findIdx? (· == y) = none → y.origin = .source := by
    intro y hy hfi
    apply hfv y
    · rw [freeVarsLet.eq_1]; exact hy
    · exact hfi
  exact ih env_outer env_orig d hlen hfv'

/-- Let cons: pulls out the first binding, descends into the rest. -/
private theorem lowerCanonLet_cons (x : VarId) (rhs : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr)
    (ihrhs : LowerCanon rhs) (ihrest : LowerCanonLet rest body) :
    LowerCanonLet ((x, rhs, er) :: rest) body := by
  intro env_outer env_orig d hlen hfv
  rw [canonLet_cons]
  rw [lowerTotal.eq_11]
  rw [lowerTotalLet.eq_2, lowerTotalLet.eq_2]
  -- IH for rhs
  have hfvrhs : ∀ y, (freeVars rhs).contains y = true →
                    env_orig.findIdx? (· == y) = none → y.origin = .source := by
    intro y hy hfi
    apply hfv y
    · rw [freeVarsLet.eq_2]
      exact VarSet.union_contains_of_contains_left _ _ _ hy
    · exact hfi
  -- IH for rest with env_orig' = x :: env_orig
  have hlen' : (x :: env_orig).length = d + 1 := by
    rw [List.length_cons]; omega
  have hfvrest : ∀ y, (freeVarsLet rest body).contains y = true →
                      (x :: env_orig).findIdx? (· == y) = none → y.origin = .source := by
    intro y hy hfi
    -- findIdx? on (x :: env_orig) = none means x != y and findIdx? env_orig = none
    rw [List.findIdx?_cons] at hfi
    have hxy : (x == y) = false := by
      cases hxy : (x == y) with
      | true => rw [hxy] at hfi; simp at hfi
      | false => rfl
    rw [hxy] at hfi
    simp only [Bool.false_eq_true, ↓reduceIte] at hfi
    have henv : env_orig.findIdx? (· == y) = none := by
      cases hfi' : env_orig.findIdx? (· == y) with
      | none => rfl
      | some j =>
        rw [hfi'] at hfi
        simp at hfi
    -- Show y in freeVarsLet ((x,rhs,er) :: rest) body
    apply hfv
    · rw [freeVarsLet.eq_2]
      apply VarSet.union_contains_of_contains_right
      exact VarSet.erase_other_contains _ _ _ hy hxy
    · exact henv
  have ih_rhs := ihrhs env_outer env_orig d hlen hfvrhs
  have ih_rest := ihrest env_outer (x :: env_orig) (d + 1) hlen' hfvrest
  -- ih_rest: lowerTotal (canonEnv (d+1) (x :: env_orig) ++ env_outer) ... = lowerTotalLet (x :: env_orig ++ env_outer) rest body
  rw [canonEnv_succ_cons] at ih_rest
  rw [List.cons_append] at ih_rest
  rw [List.cons_append] at ih_rest
  -- Goal:
  -- (do rhs' ← lowerTotal env_canon (canonicalizeAux env_orig d rhs);
  --     rest' ← lowerTotalLet (canonBinder d x.hint :: env_canon) [] (canonicalizeLet (x :: env_orig) (d+1) rest body);
  --     some (.Apply (.Lam 0 rest') rhs'))
  -- = (do rhs' ← lowerTotal env_orig++env_outer rhs;
  --       rest' ← lowerTotalLet (x :: env_orig ++ env_outer) rest body;
  --       some (.Apply (.Lam 0 rest') rhs'))
  rw [ih_rhs]
  -- Now for the rest: lowerTotalLet with empty list unfolds to lowerTotal
  rw [lowerTotalLet.eq_1]
  -- Now we have lowerTotal ((canonBinder d x.hint) :: (canonEnv d env_orig ++ env_outer))
  --                        (canonicalizeLet (x :: env_orig) (d+1) rest body)
  -- which equals ih_rest LHS by associativity
  rw [ih_rest]

/-! ### Main mutual induction via strong induction on size -/

/-- Combined mutual statement for `LowerCanon`, `LowerCanonList`, `LowerCanonLet`. -/
private theorem lowerCanon_mutual :
    (∀ e : Expr, LowerCanon e) ∧
    (∀ es : List Expr, LowerCanonList es) ∧
    (∀ binds body, LowerCanonLet binds body) := by
  suffices h : ∀ n : Nat,
      (∀ e : Expr, sizeOf e ≤ n → LowerCanon e) ∧
      (∀ es : List Expr, sizeOf es ≤ n → LowerCanonList es) ∧
      (∀ binds body, sizeOf binds + sizeOf body ≤ n → LowerCanonLet binds body) by
    refine ⟨?_, ?_, ?_⟩
    · intro e; exact (h (sizeOf e)).1 e (Nat.le_refl _)
    · intro es; exact (h (sizeOf es)).2.1 es (Nat.le_refl _)
    · intro binds body; exact (h (sizeOf binds + sizeOf body)).2.2 binds body (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro e hsz; cases e <;> simp at hsz
    · intro es hsz
      cases es with
      | nil => exact lowerCanonList_nil
      | cons _ _ => simp at hsz
    · intro binds body hsz
      exfalso
      have : sizeOf body ≥ 1 := by cases body <;> simp <;> omega
      omega
  | succ n ih =>
    obtain ⟨ihExpr, ihList, ihLet⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · -- Expr case
      intro e hsz
      cases e with
      | Var x => exact lowerCanon_var x
      | Lit c => exact lowerCanon_lit c
      | Builtin b => exact lowerCanon_builtin b
      | Error => exact lowerCanon_error
      | Fix f body => exact lowerCanon_fix f body
      | Lam x body =>
        have hbsz : sizeOf body ≤ n := by
          have : sizeOf (Expr.Lam x body) = 1 + sizeOf x + sizeOf body := by simp
          omega
        exact lowerCanon_lam x body (ihExpr body hbsz)
      | App f a =>
        have hfsz : sizeOf f ≤ n := by
          have : sizeOf (Expr.App f a) = 1 + sizeOf f + sizeOf a := by simp
          omega
        have hasz : sizeOf a ≤ n := by
          have : sizeOf (Expr.App f a) = 1 + sizeOf f + sizeOf a := by simp
          omega
        exact lowerCanon_app f a (ihExpr f hfsz) (ihExpr a hasz)
      | Force e' =>
        have hesz : sizeOf e' ≤ n := by
          have : sizeOf (Expr.Force e') = 1 + sizeOf e' := by simp
          omega
        exact lowerCanon_force e' (ihExpr e' hesz)
      | Delay e' =>
        have hesz : sizeOf e' ≤ n := by
          have : sizeOf (Expr.Delay e') = 1 + sizeOf e' := by simp
          omega
        exact lowerCanon_delay e' (ihExpr e' hesz)
      | Constr t as =>
        have hsz' : sizeOf as ≤ n := by
          have : sizeOf (Expr.Constr t as) = 1 + sizeOf t + sizeOf as := by simp
          omega
        exact lowerCanon_constr t as (ihList as hsz')
      | Case s alts =>
        have hssz : sizeOf s ≤ n := by
          have : sizeOf (Expr.Case s alts) = 1 + sizeOf s + sizeOf alts := by simp
          omega
        have haltsz : sizeOf alts ≤ n := by
          have : sizeOf (Expr.Case s alts) = 1 + sizeOf s + sizeOf alts := by simp
          omega
        exact lowerCanon_case s alts (ihExpr s hssz) (ihList alts haltsz)
      | Let binds body =>
        have hsz' : sizeOf binds + sizeOf body ≤ n := by
          have : sizeOf (Expr.Let binds body) = 1 + sizeOf binds + sizeOf body := by simp
          omega
        exact lowerCanon_let binds body (ihLet binds body hsz')
    · -- List case
      intro es hsz
      cases es with
      | nil => exact lowerCanonList_nil
      | cons e es' =>
        have hesz : sizeOf e ≤ n := by
          have : sizeOf (e :: es') = 1 + sizeOf e + sizeOf es' := by simp
          omega
        have hes'sz : sizeOf es' ≤ n := by
          have : sizeOf (e :: es') = 1 + sizeOf e + sizeOf es' := by simp
          omega
        exact lowerCanonList_cons e es' (ihExpr e hesz) (ihList es' hes'sz)
    · -- Let case
      intro binds body hsz
      cases binds with
      | nil =>
        have hbsz : sizeOf body ≤ n := by
          have : sizeOf (([] : List (VarId × Expr × Bool))) + sizeOf body
              = 1 + sizeOf body := by simp
          omega
        exact lowerCanonLet_nil body (ihExpr body hbsz)
      | cons head rest =>
        obtain ⟨x, rhs, er⟩ := head
        have hrsz : sizeOf rhs ≤ n := by
          have hhead : sizeOf ((x, rhs, er) :: rest) + sizeOf body
              = 1 + sizeOf (x, rhs, er) + sizeOf rest + sizeOf body := by simp
          have hprod : sizeOf (x, rhs, er) = 1 + sizeOf x + (1 + sizeOf rhs + sizeOf er) := by simp
          omega
        have hrest_sz : sizeOf rest + sizeOf body ≤ n := by
          have hhead : sizeOf ((x, rhs, er) :: rest) + sizeOf body
              = 1 + sizeOf (x, rhs, er) + sizeOf rest + sizeOf body := by simp
          omega
        exact lowerCanonLet_cons x rhs er rest body (ihExpr rhs hrsz) (ihLet rest body hrest_sz)

/-! ### User-facing theorems -/

/-- Main theorem: canonicalize preserves `lowerTotal` for source-only expressions. -/
theorem lowerTotal_canonicalize (env : List VarId) (e : Expr)
    (hs : allFreeVarsSource e) :
    lowerTotal env (canonicalize e) = lowerTotal env e := by
  have hmain := lowerCanon_mutual.1 e env [] 0 (by simp)
  -- hmain : lowerTotal (canonEnv 0 [] ++ env) (canonicalizeAux [] 0 e) = lowerTotal ([] ++ env) e
  -- The hypothesis: ∀ y, (freeVars e).contains y = true → [].findIdx? (· == y) = none → y.origin = .source.
  -- Since [].findIdx? is always none, this is just allFreeVarsSource e.
  have hhyp : ∀ y, (freeVars e).contains y = true →
                 ([] : List VarId).findIdx? (· == y) = none → y.origin = .source := by
    intro y hy _
    exact hs y hy
  have := hmain hhyp
  have hnil1 : canonEnv 0 ([] : List VarId) = [] := rfl
  rw [hnil1] at this
  simp only [List.nil_append] at this
  unfold canonicalize
  exact this

/-- Closed version: with empty env. -/
theorem lowerTotal_canonicalize_closed (e : Expr) (hs : allFreeVarsSource e) :
    lowerTotal [] (canonicalize e) = lowerTotal [] e :=
  lowerTotal_canonicalize [] e hs

/-! ### Corollaries for expandFix composition -/

/-- `expandFix` preserves `allFreeVarsSource`: if all free vars of `e` are
`.source`, then all free vars of `expandFix e` are `.source` too. This
follows because `expandFix` only introduces `.gen` binders for bound
variables (Z-combinator expansion), and any free variable of the result
was also free in the input. -/
theorem allFreeVarsSource_expandFix (e : Expr) (hs : allFreeVarsSource e) :
    allFreeVarsSource (expandFix e) := by
  intro y hy
  -- Contrapositive: if y is free in expandFix e, then y was free in e.
  -- expandFix_freeVars_not_contains: (freeVars e).contains y = false → (freeVars (expandFix e)).contains y = false.
  -- So contrapositive: (freeVars (expandFix e)).contains y = true → (freeVars e).contains y = true.
  have : (freeVars e).contains y = true := by
    cases hy' : (freeVars e).contains y with
    | true => rfl
    | false =>
      have := expandFix_freeVars_not_contains e y hy'
      rw [this] at hy
      exact absurd hy (by simp)
  exact hs y this

/-- Wire canonicalize with expandFix: for source-only expressions,
`canonicalize (expandFix e)` has the same lowering as `expandFix e`. -/
theorem lowerTotal_canonicalize_expandFix (env : List VarId) (e : Expr)
    (hs : allFreeVarsSource e) :
    lowerTotal env (canonicalize (expandFix e)) = lowerTotal env (expandFix e) :=
  lowerTotal_canonicalize env (expandFix e) (allFreeVarsSource_expandFix e hs)

end Moist.MIR
