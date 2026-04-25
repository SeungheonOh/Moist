import Moist.MIR.Expr
import Moist.MIR.Analysis
import Moist.Verified.RenameBase

namespace Moist.MIR

open Moist.Plutus.Term (Term Const BuiltinType BuiltinFun)

/-! # Total MIR → UPLC Lowering -/

def envLookupT.go (v : VarId) : List VarId → Nat → Option Nat
  | [], _ => none
  | x :: xs, n => if x == v then some n else envLookupT.go v xs (n + 1)

def envLookupT (env : List VarId) (v : VarId) : Option Nat :=
  envLookupT.go v env 0

/-! ## Max VarId helpers (for deterministic fresh variable generation) -/

mutual
  def maxUidExpr (e : Expr) : Nat :=
    match e with
    | .Var x => x.uid
    | .Lit _ | .Builtin _ | .Error => 0
    | .Lam x body => max x.uid (maxUidExpr body)
    | .Fix f body => max f.uid (maxUidExpr body)
    | .App f a => max (maxUidExpr f) (maxUidExpr a)
    | .Force e | .Delay e => maxUidExpr e
    | .Constr _ args => maxUidExprList args
    | .Case s alts => max (maxUidExpr s) (maxUidExprList alts)
    | .Let binds body => max (maxUidExprBinds binds) (maxUidExpr body)
  termination_by sizeOf e

  def maxUidExprList (es : List Expr) : Nat :=
    match es with
    | [] => 0
    | e :: rest => max (maxUidExpr e) (maxUidExprList rest)
  termination_by sizeOf es

  def maxUidExprBinds (binds : List (VarId × Expr × Bool)) : Nat :=
    match binds with
    | [] => 0
    | (v, rhs, _) :: rest => max v.uid (max (maxUidExpr rhs) (maxUidExprBinds rest))
  termination_by sizeOf binds
end

mutual
  def lowerTotal (env : List VarId) (e : Expr) : Option Term :=
    match e with
    | .Var x => match envLookupT env x with
      | some idx => some (.Var (idx + 1))
      | none => none
    | .Lit (c, ty) => some (.Constant (c, ty))
    | .Builtin b => some (.Builtin b)
    | .Error => some .Error
    | .Lam x body => do let body' ← lowerTotal (x :: env) body; some (.Lam 0 body')
    | .App f x => do let f' ← lowerTotal env f; let x' ← lowerTotal env x; some (.Apply f' x')
    | .Force inner => do let inner' ← lowerTotal env inner; some (.Force inner')
    | .Delay inner => do let inner' ← lowerTotal env inner; some (.Delay inner')
    | .Constr tag args => do let args' ← lowerTotalList env args; some (.Constr tag args')
    | .Case scrut alts => do
      let scrut' ← lowerTotal env scrut; let alts' ← lowerTotalList env alts
      some (.Case scrut' alts')
    | .Let binds body => lowerTotalLet env binds body
    | .Fix _ _ => none
  termination_by sizeOf e

  def lowerTotalList (env : List VarId) (es : List Expr) : Option (List Term) :=
    match es with
    | [] => some []
    | e :: rest => do
      let t ← lowerTotal env e; let ts ← lowerTotalList env rest; some (t :: ts)
  termination_by sizeOf es

  def lowerTotalLet (env : List VarId) (binds : List (VarId × Expr × Bool))
      (body : Expr) : Option Term :=
    match binds with
    | [] => lowerTotal env body
    | (x, rhs, _) :: rest => do
      let rhs' ← lowerTotal env rhs; let rest' ← lowerTotalLet (x :: env) rest body
      some (.Apply (.Lam 0 rest') rhs')
  termination_by sizeOf binds + sizeOf body
end

/-! ## envLookupT lemmas -/

theorem VarOrigin.beq_true_iff (a b : VarOrigin) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> simp [BEq.beq]

theorem VarId.beq_true_iff (a b : VarId) :
    (a == b) = true ↔ a.origin = b.origin ∧ a.uid = b.uid := by
  show (a.origin == b.origin && a.uid == b.uid) = true ↔ _
  rw [Bool.and_eq_true, VarOrigin.beq_true_iff, beq_iff_eq]

theorem VarId.beq_false_iff (a b : VarId) :
    (a == b) = false ↔ a.origin ≠ b.origin ∨ a.uid ≠ b.uid := by
  constructor
  · intro hb
    by_cases ho : a.origin = b.origin
    · by_cases hu : a.uid = b.uid
      · exfalso
        have htrue := (VarId.beq_true_iff a b).mpr ⟨ho, hu⟩
        rw [htrue] at hb; exact Bool.noConfusion hb
      · exact Or.inr hu
    · exact Or.inl ho
  · intro h
    cases hb : (a == b)
    · rfl
    · exfalso
      have ⟨ho, hu⟩ := (VarId.beq_true_iff a b).mp hb
      cases h with
      | inl h' => exact h' ho
      | inr h' => exact h' hu

theorem envLookupT.go_shift (v : VarId) (env : List VarId) (n m : Nat) :
    envLookupT.go v env (n + m) = (envLookupT.go v env n).map (· + m) := by
  induction env generalizing n with
  | nil => simp [envLookupT.go, Option.map]
  | cons y rest ih =>
    simp only [envLookupT.go]; split
    · simp [Option.map]
    · show envLookupT.go v rest (n + m + 1) = _
      rw [show n + m + 1 = n + 1 + m from by omega]; exact ih (n + 1)

theorem envLookupT_agree_cons (y : VarId) (env1 env2 : List VarId)
    (h : ∀ v, envLookupT env1 v = envLookupT env2 v) :
    ∀ v, envLookupT (y :: env1) v = envLookupT (y :: env2) v := by
  intro v; simp only [envLookupT, envLookupT.go]; split
  · rfl
  · have h0 := h v; simp only [envLookupT] at h0
    rw [envLookupT.go_shift v env1 0 1, envLookupT.go_shift v env2 0 1]; simp [h0]

set_option linter.unusedSimpArgs false in
theorem envLookupT.go_append_neq (v x : VarId) (env : List VarId) (n : Nat)
    (hne : (x == v) = false) :
    envLookupT.go v (env ++ [x]) n = envLookupT.go v env n := by
  induction env generalizing n with
  | nil => simp [envLookupT.go, hne]
  | cons y rest ih =>
    simp only [List.cons_append, envLookupT.go]; split
    · rfl
    · exact ih (n+1)

theorem envLookupT.go_append_shadow (v x : VarId) (env : List VarId) (n : Nat)
    (hshadow : ∃ y ∈ env, (y == x) = true) :
    envLookupT.go v (env ++ [x]) n = envLookupT.go v env n := by
  induction env generalizing n with
  | nil => obtain ⟨_, hm, _⟩ := hshadow; exact absurd hm List.not_mem_nil
  | cons w rest ih =>
    simp only [List.cons_append, envLookupT.go]; split
    · rfl
    · rename_i hwv; obtain ⟨y, hy, hyx⟩ := hshadow
      cases hy with
      | head =>
        have : (x == v) = false := by
          cases h : (x == v); rfl
          exact absurd (by
            rw [VarId.beq_true_iff] at hyx h ⊢
            exact ⟨hyx.1.trans h.1, hyx.2.trans h.2⟩
            : (w == v) = true) hwv
        exact envLookupT.go_append_neq v x rest (n + 1) this
      | tail _ hrest => exact ih (n + 1) ⟨y, hrest, hyx⟩

theorem envLookupT.go_bound (v : VarId) (env : List VarId) (n idx : Nat)
    (h : envLookupT.go v env n = some idx) :
    n ≤ idx ∧ idx < n + env.length := by
  induction env generalizing n with
  | nil => simp [envLookupT.go] at h
  | cons y rest ih =>
    simp only [envLookupT.go] at h; split at h
    · injection h with h; subst h; exact ⟨Nat.le_refl _, by simp⟩
    · have ⟨hl, hr⟩ := ih (n + 1) h; exact ⟨by omega, by simp at hr ⊢; omega⟩

theorem envLookupT_bound (env : List VarId) (v : VarId) (idx : Nat)
    (h : envLookupT env v = some idx) : idx < env.length := by
  unfold envLookupT at h; have ⟨_, hr⟩ := envLookupT.go_bound v env 0 idx h; omega

theorem envLookupT_cons_neq (x v : VarId) (env : List VarId) (hne : (x == v) = false) :
    envLookupT (x :: env) v = (envLookupT env v).map (· + 1) := by
  unfold envLookupT; simp only [envLookupT.go, hne]
  exact envLookupT.go_shift v env 0 1

/-! ## lowerTotal env agreement -/

mutual
  theorem lowerTotal_env_agree (env1 env2 : List VarId) (e : Expr)
      (h : ∀ v, envLookupT env1 v = envLookupT env2 v) :
      lowerTotal env1 e = lowerTotal env2 e := by
    match e with
    | .Var v => simp only [lowerTotal.eq_1, h]
    | .Lit (c, ty) => simp only [lowerTotal.eq_2]
    | .Builtin b => simp only [lowerTotal.eq_3]
    | .Error => simp only [lowerTotal.eq_4]
    | .Lam y body =>
      simp only [lowerTotal.eq_5,
        lowerTotal_env_agree (y::env1) (y::env2) body (envLookupT_agree_cons y env1 env2 h)]
    | .App f a =>
      simp only [lowerTotal.eq_6,
        lowerTotal_env_agree env1 env2 f h, lowerTotal_env_agree env1 env2 a h]
    | .Force inner => simp only [lowerTotal.eq_7, lowerTotal_env_agree env1 env2 inner h]
    | .Delay inner => simp only [lowerTotal.eq_8, lowerTotal_env_agree env1 env2 inner h]
    | .Constr _ args =>
      simp only [lowerTotal.eq_9, lowerTotalList_env_agree env1 env2 args h]
    | .Case scrut alts =>
      simp only [lowerTotal.eq_10,
        lowerTotal_env_agree env1 env2 scrut h, lowerTotalList_env_agree env1 env2 alts h]
    | .Let binds body =>
      simp only [lowerTotal.eq_11, lowerTotalLet_env_agree env1 env2 binds body h]
    | .Fix _ _ => simp only [lowerTotal.eq_12]
  termination_by sizeOf e

  theorem lowerTotalList_env_agree (env1 env2 : List VarId) (es : List Expr)
      (h : ∀ v, envLookupT env1 v = envLookupT env2 v) :
      lowerTotalList env1 es = lowerTotalList env2 es := by
    match es with
    | [] => simp [lowerTotalList.eq_1]
    | e :: rest =>
      simp only [lowerTotalList.eq_2,
        lowerTotal_env_agree env1 env2 e h, lowerTotalList_env_agree env1 env2 rest h]
  termination_by sizeOf es

  theorem lowerTotalLet_env_agree (env1 env2 : List VarId)
      (binds : List (VarId × Expr × Bool)) (body : Expr)
      (h : ∀ v, envLookupT env1 v = envLookupT env2 v) :
      lowerTotalLet env1 binds body = lowerTotalLet env2 binds body := by
    match binds with
    | [] => simp only [lowerTotalLet.eq_1, lowerTotal_env_agree env1 env2 body h]
    | (y, rhs, _) :: rest =>
      simp only [lowerTotalLet.eq_2, lowerTotal_env_agree env1 env2 rhs h,
        lowerTotalLet_env_agree (y::env1) (y::env2) rest body (envLookupT_agree_cons y env1 env2 h)]
  termination_by sizeOf binds + sizeOf body
end

/-! ## VarSet lemmas -/

theorem VarId.beq_trans (a b c : VarId)
    (h1 : (a == b) = true) (h2 : (b == c) = true) : (a == c) = true := by
  rw [VarId.beq_true_iff] at *
  exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem List.any_beq_varid_trans (xs : List VarId) (v x : VarId)
    (hvx : (v == x) = true) (hv : xs.any (· == v) = true) : xs.any (· == x) = true := by
  induction xs with
  | nil => simp at hv
  | cons h t ih =>
    simp only [List.any_cons, Bool.or_eq_true_iff] at *
    exact hv.elim (fun hl => .inl (VarId.beq_trans h v x hl hvx)) (fun hr => .inr (ih hr))

theorem VarSet.singleton_contains' (v x : VarId) :
    (VarSet.singleton v).contains x = (v == x) := by
  unfold VarSet.singleton VarSet.contains; rw [← Array.any_toList]; simp [List.any]

theorem VarSet.insert_not_contains (s : VarSet) (v x : VarId)
    (h : (s.insert v).contains x = false) : s.contains x = false ∧ (v == x) = false := by
  unfold VarSet.insert at h; split at h
  · rename_i hcv
    refine ⟨h, ?_⟩
    cases hvx : (v == x)
    · rfl
    · exfalso
      unfold VarSet.contains at hcv h; rw [← Array.any_toList] at hcv h
      have := List.any_beq_varid_trans s.data.toList v x hvx hcv
      rw [this] at h; exact Bool.noConfusion h
  · unfold VarSet.contains at h; rw [← Array.any_toList, Array.toList_push,
      List.any_append, List.any_cons, List.any_nil] at h
    simp only [Bool.or_false, Bool.or_eq_false_iff] at h
    exact ⟨by unfold VarSet.contains; rw [← Array.any_toList]; exact h.1, h.2⟩

theorem foldl_insert_not_contains (acc : VarSet) (elems : List VarId) (x : VarId)
    (h : (elems.foldl (fun a v => a.insert v) acc).contains x = false) :
    acc.contains x = false := by
  induction elems generalizing acc with
  | nil => exact h
  | cons v rest ih => exact (VarSet.insert_not_contains _ v x (ih _ (by simpa using h))).1

theorem foldl_insert_elems_not_match (acc : VarSet) (elems : List VarId) (x : VarId)
    (h : (elems.foldl (fun a v => a.insert v) acc).contains x = false) :
    elems.any (· == x) = false := by
  induction elems generalizing acc with
  | nil => simp
  | cons v rest ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff]
    exact ⟨(VarSet.insert_not_contains _ v x (foldl_insert_not_contains _ rest x h)).2, ih _ h⟩

theorem VarSet.union_not_contains' (s1 s2 : VarSet) (x : VarId)
    (h : (s1.union s2).contains x = false) :
    s1.contains x = false ∧ s2.contains x = false := by
  unfold VarSet.union at h
  have h' := by rwa [← Array.foldl_toList] at h
  exact ⟨foldl_insert_not_contains s1 s2.data.toList x h',
    by unfold VarSet.contains; rw [← Array.any_toList]
       exact foldl_insert_elems_not_match s1 s2.data.toList x h'⟩

theorem list_filter_any_false {xs : List VarId} {x y : VarId}
    (hf : (xs.filter (· != y)).any (· == x) = false) (hyx : (y == x) = false) :
    xs.any (· == x) = false := by
  induction xs with
  | nil => rfl
  | cons w rest ih =>
    simp only [List.filter_cons] at hf; simp only [List.any_cons, Bool.or_eq_false_iff]
    cases hwny : (w != y)
    · simp only [hwny] at hf
      refine ⟨?_, ih hf⟩
      cases hwx : (w == x)
      · rfl
      · exfalso
        have hwy : (w == y) = true := by simp [bne] at hwny; exact hwny
        have := VarId.beq_trans y w x (by
          rw [VarId.beq_true_iff] at hwy ⊢
          exact ⟨hwy.1.symm, hwy.2.symm⟩) hwx
        rw [this] at hyx; exact Bool.noConfusion hyx
    · simp only [hwny, ite_true, List.any_cons, Bool.or_eq_false_iff] at hf; exact ⟨hf.1, ih hf.2⟩

theorem VarSet.erase_not_contains_imp' (s : VarSet) (y x : VarId)
    (h : (s.erase y).contains x = false) : s.contains x = false ∨ (y == x) = true := by
  cases hyx : (y == x)
  · left; unfold VarSet.erase VarSet.contains at h; rw [← Array.any_toList, Array.toList_filter] at h
    unfold VarSet.contains; rw [← Array.any_toList]; exact list_filter_any_false h hyx
  · right; rfl

/-! ## VarSet forward (construction) lemmas for freshness -/

theorem VarSet.insert_not_contains_fwd (s : VarSet) (v x : VarId)
    (hs : s.contains x = false) (hv : (v == x) = false) :
    (s.insert v).contains x = false := by
  unfold VarSet.insert
  split
  · exact hs
  · unfold VarSet.contains
    rw [← Array.any_toList, Array.toList_push, List.any_append,
        List.any_cons, List.any_nil, Bool.or_false]
    unfold VarSet.contains at hs
    rw [← Array.any_toList] at hs
    rw [hs, Bool.false_or]; exact hv

theorem VarSet.foldl_list_insert_not_contains_fwd :
    ∀ (elems : List VarId) (acc : VarSet) (x : VarId),
      acc.contains x = false → elems.any (· == x) = false →
      (elems.foldl (fun a v => a.insert v) acc).contains x = false
  | [], acc, _, hacc, _ => hacc
  | v :: rest, acc, x, hacc, helems => by
    simp only [List.foldl_cons]
    simp only [List.any_cons, Bool.or_eq_false_iff] at helems
    have hnext := VarSet.insert_not_contains_fwd acc v x hacc helems.1
    exact VarSet.foldl_list_insert_not_contains_fwd rest _ x hnext helems.2

theorem VarSet.union_not_contains_fwd (s1 s2 : VarSet) (x : VarId)
    (h1 : s1.contains x = false) (h2 : s2.contains x = false) :
    (s1.union s2).contains x = false := by
  unfold VarSet.union
  rw [← Array.foldl_toList]
  apply VarSet.foldl_list_insert_not_contains_fwd _ _ _ h1
  unfold VarSet.contains at h2
  rwa [← Array.any_toList] at h2

theorem List.filter_any_false_of_any_false {xs : List VarId} {x : VarId} {p : VarId → Bool}
    (h : xs.any (· == x) = false) : (xs.filter p).any (· == x) = false := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    simp only [List.filter_cons]
    by_cases hpy : p y = true
    · simp only [hpy, ite_true, List.any_cons, Bool.or_eq_false_iff]
      exact ⟨h.1, ih h.2⟩
    · simp only [show p y = false from by cases hpyb : p y; rfl; exact absurd hpyb hpy]
      exact ih h.2

theorem VarSet.erase_not_contains_fwd (s : VarSet) (y x : VarId)
    (hs : s.contains x = false) :
    (s.erase y).contains x = false := by
  unfold VarSet.erase VarSet.contains
  rw [← Array.any_toList, Array.toList_filter]
  unfold VarSet.contains at hs
  rw [← Array.any_toList] at hs
  exact List.filter_any_false_of_any_false hs

theorem VarSet.empty_not_contains (x : VarId) : VarSet.empty.contains x = false := rfl

/-! ## maxUidExpr freshness lemma

Any variable whose uid strictly exceeds `maxUidExpr e` is not in `freeVars e`.
This is the correctness statement for the "fresh variable from maxUid"
construction used by `expandFix`. -/

mutual
  theorem maxUidExpr_fresh (e : Expr) (v : VarId) (h : v.uid > maxUidExpr e) :
      (freeVars e).contains v = false := by
    match e with
    | .Var y =>
      rw [freeVars]
      rw [VarSet.singleton_contains']
      show (y == v) = false
      simp only [maxUidExpr] at h
      rw [VarId.beq_false_iff]
      exact Or.inr (by omega)
    | .Lit _ => rw [freeVars]; rfl
    | .Builtin _ => rw [freeVars]; rfl
    | .Error => rw [freeVars]; rfl
    | .Lam x body =>
      simp only [maxUidExpr] at h
      have hbody : v.uid > maxUidExpr body := by omega
      rw [freeVars]
      exact VarSet.erase_not_contains_fwd _ _ _ (maxUidExpr_fresh body v hbody)
    | .Fix f body =>
      simp only [maxUidExpr] at h
      have hbody : v.uid > maxUidExpr body := by omega
      rw [freeVars]
      exact VarSet.erase_not_contains_fwd _ _ _ (maxUidExpr_fresh body v hbody)
    | .App f a =>
      simp only [maxUidExpr] at h
      have hf : v.uid > maxUidExpr f := by omega
      have ha : v.uid > maxUidExpr a := by omega
      rw [freeVars]
      exact VarSet.union_not_contains_fwd _ _ _
        (maxUidExpr_fresh f v hf) (maxUidExpr_fresh a v ha)
    | .Force inner =>
      simp only [maxUidExpr] at h
      rw [freeVars]
      exact maxUidExpr_fresh inner v h
    | .Delay inner =>
      simp only [maxUidExpr] at h
      rw [freeVars]
      exact maxUidExpr_fresh inner v h
    | .Constr tag args =>
      simp only [maxUidExpr] at h
      rw [freeVars]
      exact maxUidExprList_fresh args v h
    | .Case scrut alts =>
      simp only [maxUidExpr] at h
      have hs : v.uid > maxUidExpr scrut := by omega
      have ha : v.uid > maxUidExprList alts := by omega
      rw [freeVars]
      exact VarSet.union_not_contains_fwd _ _ _
        (maxUidExpr_fresh scrut v hs) (maxUidExprList_fresh alts v ha)
    | .Let binds body =>
      simp only [maxUidExpr] at h
      have hbinds : v.uid > maxUidExprBinds binds := by omega
      have hbody : v.uid > maxUidExpr body := by omega
      rw [freeVars]
      exact maxUidExprLet_fresh binds body v hbinds hbody
  termination_by sizeOf e

  theorem maxUidExprList_fresh (es : List Expr) (v : VarId)
      (h : v.uid > maxUidExprList es) :
      (freeVarsList es).contains v = false := by
    match es with
    | [] => rw [freeVarsList]; rfl
    | e :: rest =>
      simp only [maxUidExprList] at h
      have he : v.uid > maxUidExpr e := by omega
      have hrest : v.uid > maxUidExprList rest := by omega
      rw [freeVarsList]
      exact VarSet.union_not_contains_fwd _ _ _
        (maxUidExpr_fresh e v he) (maxUidExprList_fresh rest v hrest)
  termination_by sizeOf es

  theorem maxUidExprLet_fresh (binds : List (VarId × Expr × Bool)) (body : Expr) (v : VarId)
      (hbinds : v.uid > maxUidExprBinds binds) (hbody : v.uid > maxUidExpr body) :
      (freeVarsLet binds body).contains v = false := by
    match binds with
    | [] =>
      rw [freeVarsLet]
      exact maxUidExpr_fresh body v hbody
    | (x, rhs, er) :: rest =>
      simp only [maxUidExprBinds] at hbinds
      have hrhs : v.uid > maxUidExpr rhs := by omega
      have hrest : v.uid > maxUidExprBinds rest := by omega
      rw [freeVarsLet]
      apply VarSet.union_not_contains_fwd _ _ _ (maxUidExpr_fresh rhs v hrhs)
      exact VarSet.erase_not_contains_fwd _ _ _
        (maxUidExprLet_fresh rest body v hrest hbody)
  termination_by sizeOf binds + sizeOf body
end

/-! ## maxUid arithmetic helpers (generally reusable for any pass) -/

theorem maxUidExpr_le_maxUidExprList_of_mem {x : Expr} {es : List Expr}
    (h : x ∈ es) : maxUidExpr x ≤ maxUidExprList es := by
  induction es with
  | nil => exact absurd h (by simp)
  | cons e rest ih =>
    simp only [maxUidExprList]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem maxUidExprBinds_append (xs ys : List (VarId × Expr × Bool)) :
    maxUidExprBinds (xs ++ ys) ≤ max (maxUidExprBinds xs) (maxUidExprBinds ys) := by
  induction xs with
  | nil => simp [maxUidExprBinds]
  | cons b rest ih =>
    obtain ⟨v, rhs, er⟩ := b
    show maxUidExprBinds ((v, rhs, er) :: (rest ++ ys)) ≤ _
    simp only [maxUidExprBinds]; omega

theorem maxUidExprList_append (xs ys : List Expr) :
    maxUidExprList (xs ++ ys) ≤ max (maxUidExprList xs) (maxUidExprList ys) := by
  induction xs with
  | nil => simp [maxUidExprList]
  | cons x rest ih =>
    show maxUidExprList (x :: (rest ++ ys)) ≤ _
    simp only [maxUidExprList]; omega

/-! ## lowerTotal append unused -/

-- Helper: env agreement for shadow case
theorem envLookupT_shadow_agree (env : List VarId) (x y : VarId)
    (heq : (y == x) = true) :
    ∀ v, envLookupT (y :: (env ++ [x])) v = envLookupT (y :: env) v := by
  intro v
  have : envLookupT ((y :: env) ++ [x]) v = envLookupT (y :: env) v :=
    by unfold envLookupT; exact envLookupT.go_append_shadow v x (y :: env) 0
         ⟨y, .head _, heq⟩
  rwa [List.cons_append] at this

mutual
  theorem lowerTotal_append_unused (env : List VarId) (x : VarId) (e : Expr)
      (hunused : (freeVars e).contains x = false) :
      lowerTotal (env ++ [x]) e = lowerTotal env e := by
    match e with
    | .Var v =>
      simp only [lowerTotal.eq_1]; congr 1
      rw [freeVars.eq_1, VarSet.singleton_contains'] at hunused
      unfold envLookupT
      exact envLookupT.go_append_neq v x env 0 (by
        cases h : (x == v)
        · rfl
        · exfalso; rw [VarId.beq_true_iff] at h
          have : (v == x) = true := by rw [VarId.beq_true_iff]; exact ⟨h.1.symm, h.2.symm⟩
          rw [this] at hunused; exact Bool.noConfusion hunused)
    | .Lit (c, ty) => simp only [lowerTotal.eq_2]
    | .Builtin b => simp only [lowerTotal.eq_3]
    | .Error => simp only [lowerTotal.eq_4]
    | .Lam y body =>
      rw [freeVars.eq_5] at hunused
      cases VarSet.erase_not_contains_imp' (freeVars body) y x hunused with
      | inl hfv =>
        have ih := lowerTotal_append_unused (y :: env) x body hfv
        rw [List.cons_append] at ih
        simp only [lowerTotal.eq_5, ih]
      | inr heq =>
        simp only [lowerTotal.eq_5,
          lowerTotal_env_agree _ _ body (envLookupT_shadow_agree env x y heq)]
    | .App f a =>
      rw [freeVars.eq_7] at hunused; have ⟨hf, ha⟩ := VarSet.union_not_contains' _ _ _ hunused
      simp only [lowerTotal.eq_6,
        lowerTotal_append_unused env x f hf, lowerTotal_append_unused env x a ha]
    | .Force inner =>
      rw [freeVars.eq_8] at hunused
      simp only [lowerTotal.eq_7, lowerTotal_append_unused env x inner hunused]
    | .Delay inner =>
      rw [freeVars.eq_9] at hunused
      simp only [lowerTotal.eq_8, lowerTotal_append_unused env x inner hunused]
    | .Constr _ args =>
      rw [freeVars.eq_10] at hunused
      simp only [lowerTotal.eq_9, lowerTotalList_append_unused env x args hunused]
    | .Case scrut alts =>
      rw [freeVars.eq_11] at hunused; have ⟨hs, ha⟩ := VarSet.union_not_contains' _ _ _ hunused
      simp only [lowerTotal.eq_10,
        lowerTotal_append_unused env x scrut hs, lowerTotalList_append_unused env x alts ha]
    | .Let binds body =>
      rw [freeVars.eq_12] at hunused
      simp only [lowerTotal.eq_11, lowerTotalLet_append_unused env x binds body hunused]
    | .Fix _ _ => simp only [lowerTotal.eq_12]
  termination_by sizeOf e

  theorem lowerTotalList_append_unused (env : List VarId) (x : VarId) (es : List Expr)
      (hunused : (freeVarsList es).contains x = false) :
      lowerTotalList (env ++ [x]) es = lowerTotalList env es := by
    match es with
    | [] => simp [lowerTotalList.eq_1]
    | e :: rest =>
      rw [freeVarsList.eq_2] at hunused; have ⟨he, hr⟩ := VarSet.union_not_contains' _ _ _ hunused
      simp only [lowerTotalList.eq_2,
        lowerTotal_append_unused env x e he, lowerTotalList_append_unused env x rest hr]
  termination_by sizeOf es

  theorem lowerTotalLet_append_unused (env : List VarId) (x : VarId)
      (binds : List (VarId × Expr × Bool)) (body : Expr)
      (hunused : (freeVarsLet binds body).contains x = false) :
      lowerTotalLet (env ++ [x]) binds body = lowerTotalLet env binds body := by
    match binds with
    | [] =>
      rw [freeVarsLet.eq_1] at hunused
      simp only [lowerTotalLet.eq_1, lowerTotal_append_unused env x body hunused]
    | (y, rhs, _) :: rest =>
      rw [freeVarsLet.eq_2] at hunused
      have ⟨hrhs, hre⟩ := VarSet.union_not_contains' _ _ _ hunused
      cases VarSet.erase_not_contains_imp' _ y x hre with
      | inl hfvl =>
        have ih := lowerTotalLet_append_unused (y :: env) x rest body hfvl
        rw [List.cons_append] at ih
        simp only [lowerTotalLet.eq_2, lowerTotal_append_unused env x rhs hrhs, ih]
      | inr heq =>
        simp only [lowerTotalLet.eq_2, lowerTotal_append_unused env x rhs hrhs,
          lowerTotalLet_env_agree _ _ rest body (envLookupT_shadow_agree env x y heq)]
  termination_by sizeOf binds + sizeOf body
end

theorem lowerTotal_closed_env_irrel (x : VarId) (body : Expr)
    (hunused : (freeVars body).contains x = false) :
    lowerTotal [x] body = lowerTotal [] body := by
  have : [x] = ([] : List VarId) ++ [x] := by simp
  rw [this]; exact lowerTotal_append_unused [] x body hunused

/-! ## lowerTotal prepend unused: isSome reverse direction

If `x` is unused in `e` and `lowerTotal (prefix_env ++ x :: env) e` succeeds,
then `lowerTotal (prefix_env ++ env) e` also succeeds. This is the reverse
of what `lowerTotal_prepend_unused_gen` provides (which only goes from
success in `prefix_env ++ env` to success in `prefix_env ++ x :: env`). -/

theorem envLookupT_go_insert_isSome (v x : VarId) (pre post : List VarId) (n : Nat)
    (h : (x == v) = false ∨ (∃ y ∈ pre, (y == x) = true)) :
    (envLookupT.go v (pre ++ x :: post) n).isSome →
    (envLookupT.go v (pre ++ post) n).isSome := by
  induction pre generalizing n with
  | nil =>
    simp only [List.nil_append]
    simp only [envLookupT.go]
    cases h with
    | inl hne =>
      rw [hne]
      rw [envLookupT.go_shift v post n 1]
      cases envLookupT.go v post n with
      | none => simp [Option.map]
      | some _ => simp [Option.map]
    | inr hshadow => obtain ⟨_, hm, _⟩ := hshadow; exact absurd hm List.not_mem_nil
  | cons w pre' ih =>
    simp only [List.cons_append, envLookupT.go]
    split
    · -- w == v: found at position n in both
      simp
    · -- w ≠ v: recurse
      have hcond' : (x == v) = false ∨ (∃ y ∈ pre', (y == x) = true) := by
        cases h with
        | inl hne => exact .inl hne
        | inr hshadow =>
          obtain ⟨y, hy, hyx⟩ := hshadow
          cases hy with
          | head =>
            -- y = w, w == x = true. Need x == v = false.
            rename_i hwv
            cases hxv : (x == v)
            · exact .inl rfl
            · exfalso
              rw [VarId.beq_true_iff] at hyx hxv
              exact hwv (by
                rw [VarId.beq_true_iff]
                exact ⟨hyx.1.trans hxv.1, hyx.2.trans hxv.2⟩)
          | tail _ hrest => exact .inr ⟨y, hrest, hyx⟩
      exact ih (n + 1) hcond'

theorem envLookupT_insert_isSome (prefix_env env : List VarId) (x v : VarId)
    (h : (x == v) = false ∨ (∃ y ∈ prefix_env, (y == x) = true)) :
    (envLookupT (prefix_env ++ x :: env) v).isSome →
    (envLookupT (prefix_env ++ env) v).isSome := by
  unfold envLookupT
  exact envLookupT_go_insert_isSome v x prefix_env env 0 h

-- Helper: freeVars (Var v) not containing x implies x ≠ v (as beq)
theorem freeVars_var_unused_neq' (v x : VarId)
    (h : (freeVars (.Var v)).contains x = false) : (x == v) = false := by
  rw [freeVars.eq_1, VarSet.singleton_contains'] at h
  cases hxv : (x == v)
  · rfl
  · exfalso; rw [VarId.beq_true_iff] at hxv
    have : (v == x) = true := by rw [VarId.beq_true_iff]; exact ⟨hxv.1.symm, hxv.2.symm⟩
    rw [this] at h; exact Bool.noConfusion h

-- Helper: convert option isSome to exists
theorem Option.bind_none_right {α β : Type} (f : α → Option β) :
    (none : Option α).bind f = none := rfl

theorem Option.bind_eq_none_of_inner {α β : Type} {oa : Option α} {f : α → Option β}
    (h : oa = none) : oa.bind f = none := by rw [h]; rfl

mutual
  /-- If `lowerTotal (prefix_env ++ env) e = none` and `x` is unused in `e`
      (or shadowed by a prefix variable), then `lowerTotal (prefix_env ++ x :: env) e = none`. -/
  theorem lowerTotal_prepend_unused_none_gen (prefix_env env : List VarId) (x : VarId) (e : Expr)
      (hunused : (freeVars e).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true))
      (hnone : lowerTotal (prefix_env ++ env) e = none) :
      lowerTotal (prefix_env ++ x :: env) e = none := by
    match e with
    | .Var v =>
      have hv : (x == v) = false ∨ (∃ y ∈ prefix_env, (y == x) = true) := by
        cases hunused with
        | inl hfv => exact .inl (freeVars_var_unused_neq' v x hfv)
        | inr hshadow => exact .inr hshadow
      simp only [lowerTotal.eq_1] at hnone ⊢
      -- hnone tells us envLookupT (prefix_env ++ env) v = none (otherwise lowerTotal would return some)
      cases hlu : envLookupT (prefix_env ++ env) v with
      | none =>
        -- Need: envLookupT (prefix_env ++ x :: env) v either gives none, or if some, we get rfl
        cases hlu2 : envLookupT (prefix_env ++ x :: env) v with
        | none => rfl
        | some idx =>
          exfalso; have := envLookupT_insert_isSome prefix_env env x v hv (by simp [hlu2])
          simp [hlu] at this
      | some _ => simp [hlu] at hnone
    | .Lit (c, ty) => exact absurd hnone (by simp [lowerTotal])
    | .Builtin b => exact absurd hnone (by simp [lowerTotal])
    | .Error => exact absurd hnone (by simp [lowerTotal])
    | .Lam y body =>
      have hcond : (freeVars body).contains x = false ∨ (∃ z ∈ y :: prefix_env, (z == x) = true) := by
        cases hunused with
        | inl hfv =>
          rw [freeVars.eq_5] at hfv
          cases VarSet.erase_not_contains_imp' (freeVars body) y x hfv with
          | inl hfvb => exact .inl hfvb
          | inr heq => exact .inr ⟨y, List.Mem.head _, heq⟩
        | inr hshadow =>
          obtain ⟨z, hz, hzx⟩ := hshadow
          exact .inr ⟨z, List.Mem.tail _ hz, hzx⟩
      simp only [lowerTotal.eq_5, Option.bind_eq_bind] at hnone ⊢
      cases hb : lowerTotal (y :: prefix_env ++ env) body with
      | none =>
        have ih := lowerTotal_prepend_unused_none_gen (y :: prefix_env) env x body hcond hb
        exact Option.bind_eq_none_of_inner ih
      | some bv =>
        have : (lowerTotal (y :: prefix_env ++ env) body).bind (fun body' => some (Term.Lam 0 body')) = none := hnone
        rw [hb] at this; simp at this
    | .App f a =>
      have hcf : (freeVars f).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true) := by
        cases hunused with
        | inl hfv =>
          rw [freeVars.eq_7] at hfv; exact .inl (VarSet.union_not_contains' _ _ _ hfv).1
        | inr h => exact .inr h
      have hca : (freeVars a).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true) := by
        cases hunused with
        | inl hfv =>
          rw [freeVars.eq_7] at hfv; exact .inl (VarSet.union_not_contains' _ _ _ hfv).2
        | inr h => exact .inr h
      simp only [lowerTotal.eq_6, Option.bind_eq_bind] at hnone ⊢
      cases hf : lowerTotal (prefix_env ++ env) f with
      | none =>
        exact Option.bind_eq_none_of_inner (lowerTotal_prepend_unused_none_gen prefix_env env x f hcf hf)
      | some fv =>
        rw [hf, Option.bind_some] at hnone
        -- hnone : (lowerTotal ... a).bind ... = none
        have ha_none : lowerTotal (prefix_env ++ env) a = none := by
          cases ha : lowerTotal (prefix_env ++ env) a with
          | none => rfl
          | some _ => rw [ha, Option.bind_some] at hnone; exact absurd hnone (by simp)
        have iha := lowerTotal_prepend_unused_none_gen prefix_env env x a hca ha_none
        cases hf2 : lowerTotal (prefix_env ++ x :: env) f with
        | none => rfl
        | some _ =>
          show (some _).bind (fun _ => (lowerTotal (prefix_env ++ x :: env) a).bind _) = none
          rw [Option.bind_some, iha]; rfl
    | .Force inner =>
      have hc : (freeVars inner).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true) := by
        cases hunused with
        | inl hfv => rw [freeVars.eq_8] at hfv; exact .inl hfv
        | inr h => exact .inr h
      simp only [lowerTotal.eq_7, Option.bind_eq_bind] at hnone ⊢
      cases hi : lowerTotal (prefix_env ++ env) inner with
      | none =>
        exact Option.bind_eq_none_of_inner (lowerTotal_prepend_unused_none_gen prefix_env env x inner hc hi)
      | some _ => rw [hi, Option.bind_some] at hnone; exact absurd hnone (by simp)
    | .Delay inner =>
      have hc : (freeVars inner).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true) := by
        cases hunused with
        | inl hfv => rw [freeVars.eq_9] at hfv; exact .inl hfv
        | inr h => exact .inr h
      simp only [lowerTotal.eq_8, Option.bind_eq_bind] at hnone ⊢
      cases hi : lowerTotal (prefix_env ++ env) inner with
      | none =>
        exact Option.bind_eq_none_of_inner (lowerTotal_prepend_unused_none_gen prefix_env env x inner hc hi)
      | some _ => rw [hi, Option.bind_some] at hnone; exact absurd hnone (by simp)
    | .Constr tag args =>
      have hc : (freeVarsList args).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true) := by
        cases hunused with
        | inl hfv => rw [freeVars.eq_10] at hfv; exact .inl hfv
        | inr h => exact .inr h
      simp only [lowerTotal.eq_9, Option.bind_eq_bind] at hnone ⊢
      cases ha : lowerTotalList (prefix_env ++ env) args with
      | none =>
        exact Option.bind_eq_none_of_inner (lowerTotalList_prepend_unused_none_gen prefix_env env x args hc ha)
      | some _ => rw [ha, Option.bind_some] at hnone; exact absurd hnone (by simp)
    | .Case scrut alts =>
      have hcs : (freeVars scrut).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true) := by
        cases hunused with
        | inl hfv =>
          rw [freeVars.eq_11] at hfv; exact .inl (VarSet.union_not_contains' _ _ _ hfv).1
        | inr h => exact .inr h
      have hca : (freeVarsList alts).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true) := by
        cases hunused with
        | inl hfv =>
          rw [freeVars.eq_11] at hfv; exact .inl (VarSet.union_not_contains' _ _ _ hfv).2
        | inr h => exact .inr h
      simp only [lowerTotal.eq_10, Option.bind_eq_bind] at hnone ⊢
      cases hs : lowerTotal (prefix_env ++ env) scrut with
      | none =>
        exact Option.bind_eq_none_of_inner (lowerTotal_prepend_unused_none_gen prefix_env env x scrut hcs hs)
      | some sv =>
        rw [hs, Option.bind_some] at hnone
        have ha_none : lowerTotalList (prefix_env ++ env) alts = none := by
          cases ha : lowerTotalList (prefix_env ++ env) alts with
          | none => rfl
          | some _ => rw [ha, Option.bind_some] at hnone; exact absurd hnone (by simp)
        have iha := lowerTotalList_prepend_unused_none_gen prefix_env env x alts hca ha_none
        cases hs2 : lowerTotal (prefix_env ++ x :: env) scrut with
        | none => rfl
        | some _ =>
          show (some _).bind (fun _ => (lowerTotalList (prefix_env ++ x :: env) alts).bind _) = none
          rw [Option.bind_some, iha]; rfl
    | .Let binds body =>
      simp only [lowerTotal.eq_11] at hnone ⊢
      have hunused' : (freeVarsLet binds body).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true) :=
        hunused.imp (fun h => by rw [freeVars.eq_12] at h; exact h) id
      exact lowerTotalLet_prepend_unused_none_gen prefix_env env x binds body hunused' hnone
    | .Fix _ _ => simp only [lowerTotal.eq_12]
  termination_by sizeOf e

  theorem lowerTotalList_prepend_unused_none_gen (prefix_env env : List VarId) (x : VarId)
      (es : List Expr)
      (hunused : (freeVarsList es).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true))
      (hnone : lowerTotalList (prefix_env ++ env) es = none) :
      lowerTotalList (prefix_env ++ x :: env) es = none := by
    match es with
    | [] => exact absurd hnone (by simp [lowerTotalList])
    | e :: rest =>
      have hce : (freeVars e).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true) := by
        cases hunused with
        | inl hfv =>
          rw [freeVarsList.eq_2] at hfv; exact .inl (VarSet.union_not_contains' _ _ _ hfv).1
        | inr h => exact .inr h
      have hcr : (freeVarsList rest).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true) := by
        cases hunused with
        | inl hfv =>
          rw [freeVarsList.eq_2] at hfv; exact .inl (VarSet.union_not_contains' _ _ _ hfv).2
        | inr h => exact .inr h
      simp only [lowerTotalList.eq_2, Option.bind_eq_bind] at hnone ⊢
      cases ht : lowerTotal (prefix_env ++ env) e with
      | none =>
        exact Option.bind_eq_none_of_inner (lowerTotal_prepend_unused_none_gen prefix_env env x e hce ht)
      | some tv =>
        rw [ht, Option.bind_some] at hnone
        have hts_none : lowerTotalList (prefix_env ++ env) rest = none := by
          cases hts : lowerTotalList (prefix_env ++ env) rest with
          | none => rfl
          | some _ => rw [hts, Option.bind_some] at hnone; exact absurd hnone (by simp)
        have ihts := lowerTotalList_prepend_unused_none_gen prefix_env env x rest hcr hts_none
        cases ht2 : lowerTotal (prefix_env ++ x :: env) e with
        | none => rfl
        | some _ =>
          show (some _).bind (fun _ => (lowerTotalList (prefix_env ++ x :: env) rest).bind _) = none
          rw [Option.bind_some, ihts]; rfl
  termination_by sizeOf es

  theorem lowerTotalLet_prepend_unused_none_gen (prefix_env env : List VarId) (x : VarId)
      (binds : List (VarId × Expr × Bool)) (body : Expr)
      (hunused : (freeVarsLet binds body).contains x = false ∨
          (∃ y ∈ prefix_env, (y == x) = true))
      (hnone : lowerTotalLet (prefix_env ++ env) binds body = none) :
      lowerTotalLet (prefix_env ++ x :: env) binds body = none := by
    match binds with
    | [] =>
      simp only [lowerTotalLet.eq_1] at hnone ⊢
      have hc : (freeVars body).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true) := by
        cases hunused with
        | inl hfv => rw [freeVarsLet.eq_1] at hfv; exact .inl hfv
        | inr h => exact .inr h
      exact lowerTotal_prepend_unused_none_gen prefix_env env x body hc hnone
    | (y, rhs, _) :: rest =>
      have hcrhs : (freeVars rhs).contains x = false ∨ (∃ z ∈ prefix_env, (z == x) = true) := by
        cases hunused with
        | inl hfv =>
          rw [freeVarsLet.eq_2] at hfv
          exact .inl (VarSet.union_not_contains' _ _ _ hfv).1
        | inr h => exact .inr h
      have hcrest : (freeVarsLet rest body).contains x = false ∨
          (∃ z ∈ y :: prefix_env, (z == x) = true) := by
        cases hunused with
        | inl hfv =>
          rw [freeVarsLet.eq_2] at hfv
          have hre := (VarSet.union_not_contains' _ _ _ hfv).2
          cases VarSet.erase_not_contains_imp' _ y x hre with
          | inl hfvl => exact .inl hfvl
          | inr heq => exact .inr ⟨y, List.Mem.head _, heq⟩
        | inr hshadow =>
          obtain ⟨z, hz, hzx⟩ := hshadow
          exact .inr ⟨z, List.Mem.tail _ hz, hzx⟩
      simp only [lowerTotalLet.eq_2, Option.bind_eq_bind] at hnone ⊢
      cases hr : lowerTotal (prefix_env ++ env) rhs with
      | none =>
        exact Option.bind_eq_none_of_inner (lowerTotal_prepend_unused_none_gen prefix_env env x rhs hcrhs hr)
      | some rv =>
        rw [hr, Option.bind_some] at hnone
        have hrest_none : lowerTotalLet (y :: prefix_env ++ env) rest body = none := by
          have hnone' : (lowerTotalLet (y :: prefix_env ++ env) rest body).bind
            (fun rest' => some (Term.Apply (Term.Lam 0 rest') rv)) = none := hnone
          cases hrest : lowerTotalLet (y :: prefix_env ++ env) rest body with
          | none => rfl
          | some _ => rw [hrest, Option.bind_some] at hnone'; exact absurd hnone' (by simp)
        have ihrest := lowerTotalLet_prepend_unused_none_gen (y :: prefix_env) env x rest body hcrest hrest_none
        cases hr2 : lowerTotal (prefix_env ++ x :: env) rhs with
        | none => rfl
        | some _ =>
          show (some _).bind (fun _ => (lowerTotalLet (y :: prefix_env ++ x :: env) rest body).bind _) = none
          rw [Option.bind_some, ihrest]; rfl
  termination_by sizeOf binds + sizeOf body
end

/-- If `lowerTotal env e = none` and `x` is unused in `e`, then
    `lowerTotal (x :: env) e = none`. -/
theorem lowerTotal_prepend_unused_none (env : List VarId) (x : VarId) (e : Expr)
    (hunused : (freeVars e).contains x = false)
    (hnone : lowerTotal env e = none) :
    lowerTotal (x :: env) e = none := by
  have h := lowerTotal_prepend_unused_none_gen [] env x e (.inl hunused) hnone
  simpa using h

/-! ## lowerTotal prepend unused: shift renaming -/

open Moist.Verified in
theorem envLookupT_go_insert_shift_neq (v x : VarId) (pre post : List VarId) (n : Nat)
    (hne : (x == v) = false) :
    envLookupT.go v (pre ++ x :: post) n =
      (envLookupT.go v (pre ++ post) n).map
        (fun idx => if idx ≥ n + pre.length then idx + 1 else idx) := by
  induction pre generalizing n with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.add_zero]
    simp only [envLookupT.go, hne]
    -- LHS: envLookupT.go v post (n + 1)
    -- RHS: (envLookupT.go v post n).map (fun idx => if idx ≥ n then idx + 1 else idx)
    rw [envLookupT.go_shift v post n 1]
    -- LHS now: (envLookupT.go v post n).map (· + 1)
    cases h : envLookupT.go v post n with
    | none => simp [Option.map]
    | some idx =>
      simp only [Option.map]
      have hbound := envLookupT.go_bound v post n idx h
      have : idx ≥ n := hbound.1
      simp [this]
  | cons w pre' ih =>
    simp only [List.cons_append, envLookupT.go]
    split
    · -- w == v: found at position n in both
      simp only [Option.map]
      have : ¬ (n ≥ n + (pre'.length + 1)) := by omega
      simp [this]
    · -- w ≠ v: recurse
      rw [ih (n + 1)]
      cases envLookupT.go v (pre' ++ post) (n + 1) with
      | none => simp [Option.map]
      | some idx =>
        simp only [Option.map, List.length_cons]
        congr 1
        have : (n + 1 + pre'.length) = (n + (pre'.length + 1)) := by omega
        rw [this]

open Moist.Verified in
theorem envLookupT_go_insert_shift_shadow (v x : VarId) (pre post : List VarId) (n : Nat)
    (hshadow : ∃ y ∈ pre, (y == x) = true) :
    envLookupT.go v (pre ++ x :: post) n =
      (envLookupT.go v (pre ++ post) n).map
        (fun idx => if idx ≥ n + pre.length then idx + 1 else idx) := by
  induction pre generalizing n with
  | nil => obtain ⟨_, hm, _⟩ := hshadow; exact absurd hm List.not_mem_nil
  | cons w pre' ih =>
    simp only [List.cons_append, envLookupT.go]
    split
    · -- w == v: found at position n in both
      simp only [Option.map]
      have : ¬ (n ≥ n + (pre'.length + 1)) := by omega
      simp [this]
    · -- w ≠ v: recurse
      rename_i hwv
      obtain ⟨y, hy, hyx⟩ := hshadow
      cases hy with
      | head =>
        -- y = w, so w == x. Combined with w ≠ v, we get x ≠ v
        have hxv : (x == v) = false := by
          cases h : (x == v)
          · rfl
          · exfalso
            rw [VarId.beq_true_iff] at hyx h
            exact hwv (by
              rw [VarId.beq_true_iff]
              exact ⟨hyx.1.trans h.1, hyx.2.trans h.2⟩)
        rw [envLookupT_go_insert_shift_neq v x pre' post (n + 1) hxv]
        cases envLookupT.go v (pre' ++ post) (n + 1) with
        | none => simp [Option.map]
        | some idx =>
          simp only [Option.map, List.length_cons]
          simp only [show n + 1 + pre'.length = n + (pre'.length + 1) from by omega]
      | tail _ hrest =>
        rw [ih (n + 1) ⟨y, hrest, hyx⟩]
        cases envLookupT.go v (pre' ++ post) (n + 1) with
        | none => simp [Option.map]
        | some idx =>
          simp only [Option.map, List.length_cons]
          simp only [show n + 1 + pre'.length = n + (pre'.length + 1) from by omega]

open Moist.Verified in
theorem envLookupT_go_insert_shift (v x : VarId) (pre post : List VarId) (n : Nat)
    (h : (x == v) = false ∨ (∃ y ∈ pre, (y == x) = true)) :
    envLookupT.go v (pre ++ x :: post) n =
      (envLookupT.go v (pre ++ post) n).map
        (fun idx => if idx ≥ n + pre.length then idx + 1 else idx) := by
  cases h with
  | inl hne => exact envLookupT_go_insert_shift_neq v x pre post n hne
  | inr hshadow => exact envLookupT_go_insert_shift_shadow v x pre post n hshadow

-- The `freeVars` condition on `Var v` with unused `x` implies `x ≠ v`
theorem freeVars_var_unused_neq (v x : VarId)
    (h : (freeVars (.Var v)).contains x = false) : (x == v) = false := by
  rw [freeVars.eq_1, VarSet.singleton_contains'] at h
  cases hxv : (x == v)
  · rfl
  · exfalso; rw [VarId.beq_true_iff] at hxv
    have : (v == x) = true := by rw [VarId.beq_true_iff]; exact ⟨hxv.1.symm, hxv.2.symm⟩
    rw [this] at h; exact Bool.noConfusion h

-- freeVars condition on list implies condition on each element
theorem freeVarsList_union_left (e : Expr) (rest : List Expr) (x : VarId)
    (h : (freeVarsList (e :: rest)).contains x = false) :
    (freeVars e).contains x = false := by
  rw [freeVarsList.eq_2] at h; exact (VarSet.union_not_contains' _ _ _ h).1

theorem freeVarsList_union_right (e : Expr) (rest : List Expr) (x : VarId)
    (h : (freeVarsList (e :: rest)).contains x = false) :
    (freeVarsList rest).contains x = false := by
  rw [freeVarsList.eq_2] at h; exact (VarSet.union_not_contains' _ _ _ h).2

theorem option_bind_some_eq {α β : Type} {f : α → Option β} {a : α} {oa : Option α}
    {b : β} (hoa : oa = some a) (hf : f a = some b) :
    oa.bind f = some b := by subst hoa; exact hf

mutual
  /-- Generalized prepend-unused: inserting `x` after `prefix_env` in the environment
      shifts all lowered de Bruijn indices past the prefix by 1. -/
  theorem lowerTotal_prepend_unused_gen (prefix_env env : List VarId) (x : VarId) (e : Expr)
      (hunused : (freeVars e).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true)) :
      ∀ t, lowerTotal (prefix_env ++ env) e = some t →
        lowerTotal (prefix_env ++ x :: env) e =
          some (Moist.Verified.renameTerm (Moist.Verified.shiftRename (prefix_env.length + 1)) t) := by
    intro t hlower
    match e with
    | .Var v =>
      simp only [lowerTotal.eq_1] at hlower ⊢
      cases hlu : envLookupT (prefix_env ++ env) v with
      | none => simp [hlu] at hlower
      | some idx =>
        simp [hlu] at hlower; subst hlower
        have hv : (x == v) = false ∨ (∃ y ∈ prefix_env, (y == x) = true) := by
          cases hunused with
          | inl hfv => exact .inl (freeVars_var_unused_neq v x hfv)
          | inr hshadow => exact .inr hshadow
        unfold envLookupT at hlu ⊢
        rw [envLookupT_go_insert_shift v x prefix_env env 0 hv, hlu]
        simp only [Option.map, Moist.Verified.renameTerm, Moist.Verified.shiftRename]
        -- Goal: Var ((if idx ≥ prefix_env.length then idx + 1 else idx) + 1) =
        --       Var (if idx + 1 ≥ prefix_env.length + 1 then idx + 1 + 1 else idx + 1)
        congr 1; congr 1
        -- Need: (if idx ≥ 0 + prefix_env.length then idx + 1 else idx) + 1 =
        --       if idx + 1 ≥ prefix_env.length + 1 then idx + 1 + 1 else idx + 1
        split
        · rename_i h; simp only [show idx + 1 ≥ prefix_env.length + 1 from by omega, ite_true]
        · rename_i h; simp only [show ¬(idx + 1 ≥ prefix_env.length + 1) from by omega, ite_false]
    | .Lit (c, ty) =>
      simp only [lowerTotal.eq_2] at hlower ⊢
      injection hlower with hlower; subst hlower
      simp [Moist.Verified.renameTerm]
    | .Builtin b =>
      simp only [lowerTotal.eq_3] at hlower ⊢
      injection hlower with hlower; subst hlower
      simp [Moist.Verified.renameTerm]
    | .Error =>
      simp only [lowerTotal.eq_4] at hlower ⊢
      injection hlower with hlower; subst hlower
      simp [Moist.Verified.renameTerm]
    | .Lam y body =>
      simp only [lowerTotal.eq_5] at hlower ⊢
      -- Extract body' from hlower by case-splitting the option
      match hbody : lowerTotal (y :: (prefix_env ++ env)) body with
      | none => rw [hbody] at hlower; simp at hlower
      | some body' =>
        rw [hbody] at hlower; simp at hlower; subst hlower
        -- Build the IH condition
        have hcond : (freeVars body).contains x = false ∨ (∃ z ∈ y :: prefix_env, (z == x) = true) := by
          cases hunused with
          | inl hfv =>
            rw [freeVars.eq_5] at hfv
            cases VarSet.erase_not_contains_imp' (freeVars body) y x hfv with
            | inl hfvb => exact .inl hfvb
            | inr heq => exact .inr ⟨y, List.Mem.head _, heq⟩
          | inr hshadow =>
            obtain ⟨z, hz, hzx⟩ := hshadow
            exact .inr ⟨z, List.Mem.tail _ hz, hzx⟩
        -- Apply IH: (y :: prefix_env) ++ env = y :: (prefix_env ++ env) definitionally
        have ih := lowerTotal_prepend_unused_gen (y :: prefix_env) env x body hcond body' hbody
        -- ih : lowerTotal ((y :: prefix_env) ++ x :: env) body = some (renameTerm (shiftRename ...) body')
        -- The goal has (do let body' ← lowerTotal (y :: (prefix_env ++ x :: env)) body; some (.Lam 0 body'))
        -- = some (renameTerm (shiftRename (prefix_env.length + 1)) (.Lam 0 body'))
        -- ih says lowerTotal (y :: prefix_env ++ x :: env) body = some (renameTerm ... body')
        -- The goal has the .bind form with lowerTotal (y :: (prefix_env ++ x :: env)) body
        -- These are definitionally equal, so we can rewrite
        show (lowerTotal (y :: prefix_env ++ x :: env) body).bind (fun body' => some (.Lam 0 body')) =
          some (Moist.Verified.renameTerm (Moist.Verified.shiftRename (prefix_env.length + 1))
            (.Lam 0 body'))
        rw [ih]
        simp only [Option.bind_some, Moist.Verified.renameTerm,
          Moist.Verified.liftRename_shiftRename (by omega : prefix_env.length + 1 ≥ 1),
          List.length_cons]
    | .App f a =>
      simp only [lowerTotal.eq_6] at hlower ⊢
      match hf : lowerTotal (prefix_env ++ env) f with
      | none => rw [hf] at hlower; simp at hlower
      | some f' =>
        match ha : lowerTotal (prefix_env ++ env) a with
        | none => rw [hf, ha] at hlower; simp at hlower
        | some a' =>
          rw [hf, ha] at hlower; simp at hlower; subst hlower
          have hcf : (freeVars f).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true) := by
            cases hunused with
            | inl hfv =>
              rw [freeVars.eq_7] at hfv; exact .inl (VarSet.union_not_contains' _ _ _ hfv).1
            | inr h => exact .inr h
          have hca : (freeVars a).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true) := by
            cases hunused with
            | inl hfv =>
              rw [freeVars.eq_7] at hfv; exact .inl (VarSet.union_not_contains' _ _ _ hfv).2
            | inr h => exact .inr h
          simp only [lowerTotal_prepend_unused_gen prefix_env env x f hcf f' hf,
              lowerTotal_prepend_unused_gen prefix_env env x a hca a' ha,
              Option.bind_eq_bind, Option.bind_some]
          simp [Moist.Verified.renameTerm]
    | .Force inner =>
      simp only [lowerTotal.eq_7] at hlower ⊢
      match hi : lowerTotal (prefix_env ++ env) inner with
      | none => rw [hi] at hlower; simp at hlower
      | some inner' =>
        rw [hi] at hlower; simp at hlower; subst hlower
        have hc : (freeVars inner).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true) := by
          cases hunused with
          | inl hfv => rw [freeVars.eq_8] at hfv; exact .inl hfv
          | inr h => exact .inr h
        simp only [lowerTotal_prepend_unused_gen prefix_env env x inner hc inner' hi,
            Option.bind_eq_bind, Option.bind_some]
        simp [Moist.Verified.renameTerm]
    | .Delay inner =>
      simp only [lowerTotal.eq_8] at hlower ⊢
      match hi : lowerTotal (prefix_env ++ env) inner with
      | none => rw [hi] at hlower; simp at hlower
      | some inner' =>
        rw [hi] at hlower; simp at hlower; subst hlower
        have hc : (freeVars inner).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true) := by
          cases hunused with
          | inl hfv => rw [freeVars.eq_9] at hfv; exact .inl hfv
          | inr h => exact .inr h
        simp only [lowerTotal_prepend_unused_gen prefix_env env x inner hc inner' hi,
            Option.bind_eq_bind, Option.bind_some]
        simp [Moist.Verified.renameTerm]
    | .Constr tag args =>
      simp only [lowerTotal.eq_9] at hlower ⊢
      match hargs : lowerTotalList (prefix_env ++ env) args with
      | none => rw [hargs] at hlower; simp at hlower
      | some args' =>
        rw [hargs] at hlower; simp at hlower; subst hlower
        have hc : (freeVarsList args).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true) := by
          cases hunused with
          | inl hfv => rw [freeVars.eq_10] at hfv; exact .inl hfv
          | inr h => exact .inr h
        simp only [lowerTotalList_prepend_unused_gen prefix_env env x args hc args' hargs,
            Option.bind_eq_bind, Option.bind_some]
        simp [Moist.Verified.renameTerm]
    | .Case scrut alts =>
      simp only [lowerTotal.eq_10] at hlower ⊢
      match hs : lowerTotal (prefix_env ++ env) scrut with
      | none => rw [hs] at hlower; simp at hlower
      | some scrut' =>
        match ha : lowerTotalList (prefix_env ++ env) alts with
        | none => rw [hs, ha] at hlower; simp at hlower
        | some alts' =>
          rw [hs, ha] at hlower; simp at hlower; subst hlower
          have hcs : (freeVars scrut).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true) := by
            cases hunused with
            | inl hfv =>
              rw [freeVars.eq_11] at hfv; exact .inl (VarSet.union_not_contains' _ _ _ hfv).1
            | inr h => exact .inr h
          have hca : (freeVarsList alts).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true) := by
            cases hunused with
            | inl hfv =>
              rw [freeVars.eq_11] at hfv; exact .inl (VarSet.union_not_contains' _ _ _ hfv).2
            | inr h => exact .inr h
          simp only [lowerTotal_prepend_unused_gen prefix_env env x scrut hcs scrut' hs,
              lowerTotalList_prepend_unused_gen prefix_env env x alts hca alts' ha,
              Option.bind_eq_bind, Option.bind_some]
          simp [Moist.Verified.renameTerm]
    | .Let binds body =>
      simp only [lowerTotal.eq_11] at hlower ⊢
      have hunused' : (freeVarsLet binds body).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true) :=
        hunused.imp (fun h => by rw [freeVars.eq_12] at h; exact h) id
      exact lowerTotalLet_prepend_unused_gen prefix_env env x binds body hunused' t hlower
    | .Fix _ _ =>
      simp only [lowerTotal.eq_12] at hlower; exact absurd hlower (by simp)
  termination_by sizeOf e

  theorem lowerTotalList_prepend_unused_gen (prefix_env env : List VarId) (x : VarId)
      (es : List Expr)
      (hunused : (freeVarsList es).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true)) :
      ∀ ts, lowerTotalList (prefix_env ++ env) es = some ts →
        lowerTotalList (prefix_env ++ x :: env) es =
          some (Moist.Verified.renameTermList (Moist.Verified.shiftRename (prefix_env.length + 1)) ts) := by
    intro ts hlower
    match es with
    | [] =>
      simp only [lowerTotalList.eq_1] at hlower ⊢
      injection hlower with hlower; subst hlower
      rfl
    | e :: rest =>
      simp only [lowerTotalList.eq_2] at hlower ⊢
      match ht : lowerTotal (prefix_env ++ env) e with
      | none => rw [ht] at hlower; simp at hlower
      | some t =>
        match hts : lowerTotalList (prefix_env ++ env) rest with
        | none => rw [ht, hts] at hlower; simp at hlower
        | some ts' =>
          rw [ht, hts] at hlower; simp at hlower; subst hlower
          have hce : (freeVars e).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true) := by
            cases hunused with
            | inl hfv =>
              rw [freeVarsList.eq_2] at hfv; exact .inl (VarSet.union_not_contains' _ _ _ hfv).1
            | inr h => exact .inr h
          have hcr : (freeVarsList rest).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true) := by
            cases hunused with
            | inl hfv =>
              rw [freeVarsList.eq_2] at hfv; exact .inl (VarSet.union_not_contains' _ _ _ hfv).2
            | inr h => exact .inr h
          simp only [lowerTotal_prepend_unused_gen prefix_env env x e hce t ht,
              lowerTotalList_prepend_unused_gen prefix_env env x rest hcr ts' hts,
              Option.bind_eq_bind, Option.bind_some]
          simp [Moist.Verified.renameTermList]
  termination_by sizeOf es

  theorem lowerTotalLet_prepend_unused_gen (prefix_env env : List VarId) (x : VarId)
      (binds : List (VarId × Expr × Bool)) (body : Expr)
      (hunused : (freeVarsLet binds body).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true)) :
      ∀ t, lowerTotalLet (prefix_env ++ env) binds body = some t →
        lowerTotalLet (prefix_env ++ x :: env) binds body =
          some (Moist.Verified.renameTerm (Moist.Verified.shiftRename (prefix_env.length + 1)) t) := by
    intro t hlower
    match binds with
    | [] =>
      simp only [lowerTotalLet.eq_1] at hlower ⊢
      have hc : (freeVars body).contains x = false ∨ (∃ y ∈ prefix_env, (y == x) = true) := by
        cases hunused with
        | inl hfv => rw [freeVarsLet.eq_1] at hfv; exact .inl hfv
        | inr h => exact .inr h
      exact lowerTotal_prepend_unused_gen prefix_env env x body hc t hlower
    | (y, rhs, er) :: rest =>
      simp only [lowerTotalLet.eq_2] at hlower ⊢
      match hrhs : lowerTotal (prefix_env ++ env) rhs with
      | none => rw [hrhs] at hlower; simp at hlower
      | some rhs' =>
        match hrest : lowerTotalLet (y :: (prefix_env ++ env)) rest body with
        | none => rw [hrhs, hrest] at hlower; simp at hlower
        | some rest' =>
          rw [hrhs, hrest] at hlower; simp at hlower; subst hlower
          have hcrhs : (freeVars rhs).contains x = false ∨ (∃ z ∈ prefix_env, (z == x) = true) := by
            cases hunused with
            | inl hfv =>
              rw [freeVarsLet.eq_2] at hfv
              exact .inl (VarSet.union_not_contains' _ _ _ hfv).1
            | inr h => exact .inr h
          have hcrest : (freeVarsLet rest body).contains x = false ∨
              (∃ z ∈ y :: prefix_env, (z == x) = true) := by
            cases hunused with
            | inl hfv =>
              rw [freeVarsLet.eq_2] at hfv
              have hre := (VarSet.union_not_contains' _ _ _ hfv).2
              cases VarSet.erase_not_contains_imp' _ y x hre with
              | inl hfvl => exact .inl hfvl
              | inr heq => exact .inr ⟨y, List.Mem.head _, heq⟩
            | inr hshadow =>
              obtain ⟨z, hz, hzx⟩ := hshadow
              exact .inr ⟨z, List.Mem.tail _ hz, hzx⟩
          -- (y :: prefix_env) ++ env = y :: (prefix_env ++ env) definitionally
          have ih := lowerTotalLet_prepend_unused_gen (y :: prefix_env) env x rest body hcrest rest' hrest
          -- ih : lowerTotalLet ((y :: prefix_env) ++ x :: env) rest body =
          --        some (renameTerm (shiftRename ((y :: prefix_env).length + 1)) rest')
          -- (y :: prefix_env) ++ x :: env = y :: (prefix_env ++ x :: env) definitionally
          -- Use show to normalize the env representation
          show (do let rhs' ← lowerTotal (prefix_env ++ x :: env) rhs
                   let rest' ← lowerTotalLet (y :: prefix_env ++ x :: env) rest body
                   some (.Apply (.Lam 0 rest') rhs')) =
            some (Moist.Verified.renameTerm (Moist.Verified.shiftRename (prefix_env.length + 1))
              (.Apply (.Lam 0 rest') rhs'))
          -- Instead of rw which leaves a do block, use show + exact
          have ihrhs := lowerTotal_prepend_unused_gen prefix_env env x rhs hcrhs rhs' hrhs
          have ihrest := ih
          show (do let rhs' ← lowerTotal (prefix_env ++ x :: env) rhs
                   let rest' ← lowerTotalLet (y :: prefix_env ++ x :: env) rest body
                   some (.Apply (.Lam 0 rest') rhs')) =
            some (Moist.Verified.renameTerm (Moist.Verified.shiftRename (prefix_env.length + 1))
              (.Apply (.Lam 0 rest') rhs'))
          rw [ihrhs, ihrest]
          -- Now the do block has some values; reduce the bind
          simp only [bind, Option.bind, List.length_cons]
          -- Goal: some (...) = some (renameTerm ... (.Apply (.Lam 0 rest') rhs'))
          -- renameTerm for Apply is definitional
          -- renameTerm for Lam introduces liftRename
          -- Use congr to peel off some, Apply, and get to the Lam body
          congr 1  -- strip some
          congr 1  -- strip Apply's second arg (rhs)
          -- Goal should be about the Lam part
          -- Lam 0 (renameTerm (shiftRename (p+1+1)) rest') = renameTerm (shiftRename (p+1)) (Lam 0 rest')
          -- The RHS reduces definitionally to Lam 0 (renameTerm (liftRename (shiftRename (p+1))) rest')
          -- Use show to make the RHS explicit
          change Term.Lam 0 (Moist.Verified.renameTerm (Moist.Verified.shiftRename (prefix_env.length + 1 + 1)) rest') = Term.Lam 0 (Moist.Verified.renameTerm (Moist.Verified.liftRename (Moist.Verified.shiftRename (prefix_env.length + 1))) rest')
          congr 1; congr 1
          exact (Moist.Verified.liftRename_shiftRename (by omega : prefix_env.length + 1 ≥ 1)).symm
  termination_by sizeOf binds + sizeOf body
end

/-- Prepending an unused variable `x` to the MIR env shifts all de Bruijn
    indices in the lowered UPLC term by `shiftRename 1`. -/
theorem lowerTotal_prepend_unused (env : List VarId) (x : VarId) (e : Expr)
    (hunused : (freeVars e).contains x = false) :
    ∀ t, lowerTotal env e = some t →
      lowerTotal (x :: env) e =
        some (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t) := by
  have h := lowerTotal_prepend_unused_gen [] env x e (.inl hunused)
  simpa using h

/-- Swapping an unused variable in the middle of the environment leaves
    `lowerTotal` unchanged. Both `y₁` and `y₂` are free in `e`, so they
    simply occupy the same shift position without being referenced. -/
theorem lowerTotal_env_swap_unused (prefix_env env : List VarId) (y₁ y₂ : VarId) (e : Expr)
    (hy1 : (freeVars e).contains y₁ = false)
    (hy2 : (freeVars e).contains y₂ = false) :
    lowerTotal (prefix_env ++ y₁ :: env) e = lowerTotal (prefix_env ++ y₂ :: env) e := by
  cases h : lowerTotal (prefix_env ++ env) e with
  | none =>
    rw [lowerTotal_prepend_unused_none_gen prefix_env env y₁ e (.inl hy1) h,
        lowerTotal_prepend_unused_none_gen prefix_env env y₂ e (.inl hy2) h]
  | some t =>
    rw [lowerTotal_prepend_unused_gen prefix_env env y₁ e (.inl hy1) t h,
        lowerTotal_prepend_unused_gen prefix_env env y₂ e (.inl hy2) t h]

/-! ## Fix counting (total) -/

mutual
  def fixCount (e : Expr) : Nat :=
    match e with
    | .Fix _ body => 1 + fixCount body
    | .Lam _ body => fixCount body
    | .App f x => fixCount f + fixCount x
    | .Force e | .Delay e => fixCount e
    | .Constr _ args => fixCountList args
    | .Case scrut alts => fixCount scrut + fixCountList alts
    | .Let binds body => fixCountBinds binds + fixCount body
    | _ => 0
  termination_by sizeOf e

  def fixCountList (es : List Expr) : Nat :=
    match es with
    | [] => 0
    | e :: rest => fixCount e + fixCountList rest
  termination_by sizeOf es

  def fixCountBinds (binds : List (VarId × Expr × Bool)) : Nat :=
    match binds with
    | [] => 0
    | (_, rhs, _) :: rest => fixCount rhs + fixCountBinds rest
  termination_by sizeOf binds
end

/-! ## Fix expansion (total, single bottom-up pass, compositional)

Expands every `Fix f (Lam x e)` to its Z combinator encoding at the MIR
level. The pass is bottom-up: children are expanded first, so by the time
we reach a Fix node its body is already Fix-free. Since `subst` with a
Fix-free replacement (`λv. s s v`) cannot introduce Fix nodes, the output
of a single pass is guaranteed Fix-free. No fuel required.

Fresh variables are generated from `maxUidExpr` of the already-expanded
body, so no counter is threaded between sibling sub-expressions. This
makes `expandFix` fully compositional.
-/

mutual
  /-- Expand all Fix nodes bottom-up. Compositional: no counter threaded.

      The Z combinator transformation produces:
        (λz. z z) (λs. (λf. λx. body') (λv. s s v))
      The body `f` is kept as an explicit `Lam f`, applied to `selfApp =
      λv. s s v`. This is operationally equivalent to inlining the
      substitution (the Apply-Lam β-reduces to the substituted form), but
      keeps the structure compositional w.r.t. `body'`. The compositional
      form makes `mirCtxRefines_fix` provable as a direct application of
      `App`/`Lam` congruences. -/
  def expandFix (e : Expr) : Expr :=
    match e with
    | .Fix f (.Lam x body) =>
      -- Bottom-up: expand children first so body' is Fix-free
      let body' := expandFix body
      let base := maxUidExpr body' + 1
      -- Z combinator: (λz. z z) (λs. (λf. λx. body') (λv. s s v))
      -- The s/v/z binders are `.gen` origin: they partition away from any
      -- `.source` VarId and are thus immune to `rename old new_` with
      -- `.source`-origin `old`/`new_`.
      let s : VarId := { uid := base, origin := .gen, hint := "s" }
      let v : VarId := { uid := base + 1, origin := .gen, hint := "v" }
      let selfApp := Expr.Lam v (.App (.App (.Var s) (.Var s)) (.Var v))
      let z : VarId := { uid := base + 2, origin := .gen, hint := "z" }
      .App (.Lam z (.App (.Var z) (.Var z)))
           (.Lam s (.App (.Lam f (.Lam x body')) selfApp))
    | .Fix f body =>
      let body' := expandFix body; .Fix f body'
    | .Lam x body =>
      let body' := expandFix body; .Lam x body'
    | .App f x =>
      let f' := expandFix f
      let x' := expandFix x; .App f' x'
    | .Let binds body =>
      let binds' := expandFixBinds binds
      let body' := expandFix body; .Let binds' body'
    | .Force e => .Force (expandFix e)
    | .Delay e => .Delay (expandFix e)
    | .Constr tag args =>
      .Constr tag (expandFixList args)
    | .Case scrut alts =>
      .Case (expandFix scrut) (expandFixList alts)
    | e => e
  termination_by sizeOf e

  def expandFixList (es : List Expr) : List Expr :=
    match es with
    | [] => []
    | e :: rest =>
      expandFix e :: expandFixList rest
  termination_by sizeOf es

  def expandFixBinds (binds : List (VarId × Expr × Bool))
      : List (VarId × Expr × Bool) :=
    match binds with
    | [] => []
    | (v, rhs, er) :: rest =>
      (v, expandFix rhs, er) :: expandFixBinds rest
  termination_by sizeOf binds
end

/-! ## expandFix is identity on Fix-free expressions -/

mutual
  theorem expandFix_id (e : Expr) (h : fixCount e = 0) :
      expandFix e = e := by
    match e with
    | .Var _ | .Lit _ | .Builtin _ | .Error => simp [expandFix]
    | .Fix _ (.Lam _ _) => simp only [fixCount] at h; omega
    | .Fix _ _ => simp only [fixCount] at h; omega
    | .Lam _ body =>
      simp only [fixCount] at h; simp only [expandFix]
      rw [expandFix_id body h]
    | .App f x =>
      simp only [fixCount] at h; simp only [expandFix]
      have hf : fixCount f = 0 := by omega
      have hx : fixCount x = 0 := by omega
      rw [expandFix_id f hf, expandFix_id x hx]
    | .Force e' => simp only [fixCount] at h; simp only [expandFix]; rw [expandFix_id e' h]
    | .Delay e' => simp only [fixCount] at h; simp only [expandFix]; rw [expandFix_id e' h]
    | .Constr _ args =>
      simp only [fixCount] at h; simp only [expandFix]; rw [expandFixList_id args h]
    | .Case scrut alts =>
      simp only [fixCount] at h; simp only [expandFix]
      have hs : fixCount scrut = 0 := by omega
      have ha : fixCountList alts = 0 := by omega
      rw [expandFix_id scrut hs, expandFixList_id alts ha]
    | .Let binds body =>
      simp only [fixCount] at h; simp only [expandFix]
      have hb : fixCountBinds binds = 0 := by omega
      have hd : fixCount body = 0 := by omega
      rw [expandFixBinds_id binds hb, expandFix_id body hd]
  termination_by sizeOf e

  theorem expandFixList_id (es : List Expr) (h : fixCountList es = 0) :
      expandFixList es = es := by
    match es with
    | [] => simp [expandFixList]
    | e :: rest =>
      simp only [fixCountList] at h; simp only [expandFixList]
      have he : fixCount e = 0 := by omega
      have hr : fixCountList rest = 0 := by omega
      rw [expandFix_id e he, expandFixList_id rest hr]
  termination_by sizeOf es

  theorem expandFixBinds_id (binds : List (VarId × Expr × Bool))
      (h : fixCountBinds binds = 0) : expandFixBinds binds = binds := by
    match binds with
    | [] => simp [expandFixBinds]
    | (_, rhs, _) :: rest =>
      simp only [fixCountBinds] at h; simp only [expandFixBinds]
      have hr : fixCount rhs = 0 := by omega
      have hrest : fixCountBinds rest = 0 := by omega
      rw [expandFix_id rhs hr, expandFixBinds_id rest hrest]
  termination_by sizeOf binds
end

/-! ## Forward VarSet helpers for freshness preservation -/

theorem VarSet.erase_self_not_contains (s : VarSet) (y x : VarId)
    (h : (y == x) = true) : (s.erase y).contains x = false := by
  unfold VarSet.erase VarSet.contains
  rw [← Array.any_toList, Array.toList_filter]
  induction s.data.toList with
  | nil => rfl
  | cons w rest ih =>
    simp only [List.filter_cons]
    by_cases hwy : (w != y) = true
    · simp only [hwy, ite_true, List.any_cons, Bool.or_eq_false_iff]
      refine ⟨?_, ih⟩
      show (w == x) = false
      simp only [bne, Bool.not_eq_true'] at hwy
      -- hwy : (w == y) = false, h : (y == x) = true.
      rw [VarId.beq_false_iff] at hwy
      rw [VarId.beq_true_iff] at h
      rw [VarId.beq_false_iff]
      cases hwy with
      | inl ho => exact Or.inl (fun heq => ho (heq.trans h.1.symm))
      | inr hu => exact Or.inr (fun heq => hu (heq.trans h.2.symm))
    · simp only [show (w != y) = false from by cases hh : (w != y); rfl; exact absurd hh hwy]
      exact ih

theorem VarSet.erase_of_inner_not_contains_or_match (s : VarSet) (y x : VarId)
    (h : s.contains x = false ∨ (y == x) = true) :
    (s.erase y).contains x = false := by
  cases h with
  | inl hs => exact VarSet.erase_not_contains_fwd _ _ _ hs
  | inr hyx => exact VarSet.erase_self_not_contains _ _ _ hyx

/-! ## expandFix preserves freeVars not-contains

This preservation is proven via mutual recursion mirroring `expandFix`
with two helper clauses:
- `expandFix_fix_lam_freeVars_not_contains` handles the Z-combinator
  unfolding when the Fix body is a Lam.
- `expandFix_fix_nonlam_freeVars_not_contains` handles all other Fix body
  shapes by structural recursion on the inner body.

The main theorem `expandFix_freeVars_not_contains` dispatches on the top-level
constructor and uses `Expr.isLam` style `match` to route Fix nodes to the
correct helper. -/

/-- Build a 3-way disjunction for the Fix-Lam case from the `not contains`
    hypothesis on `((freeVars inner).erase x).erase f`. -/
theorem erase_erase_decompose (s : VarSet) (x f v : VarId)
    (h : ((s.erase x).erase f).contains v = false) :
    s.contains v = false ∨ (x == v) = true ∨ (f == v) = true := by
  cases VarSet.erase_not_contains_imp' _ f v h with
  | inr hfv => exact .inr (.inr hfv)
  | inl h' =>
    cases VarSet.erase_not_contains_imp' _ x v h' with
    | inr hxv => exact .inr (.inl hxv)
    | inl h'' => exact .inl h''

/-- Core Fix-Lam fresh preservation: if `v` is absent from `freeVars inner'`
    (or is matched by `x` or `f`), then the freeVars of the fully expanded
    Z combinator wrapper don't contain `v`. -/
theorem expandFix_fix_lam_freeVars_not_contains
    (f x : VarId) (inner_expanded : Expr) (v : VarId)
    (hinner : (freeVars inner_expanded).contains v = false ∨
              (x == v) = true ∨ (f == v) = true) :
    let base := maxUidExpr inner_expanded + 1
    let s_c : VarId := ⟨base, .gen, "s"⟩
    let v_c : VarId := ⟨base + 1, .gen, "v"⟩
    let z_c : VarId := ⟨base + 2, .gen, "z"⟩
    (freeVars
      ((Expr.Lam z_c ((Expr.Var z_c).App (Expr.Var z_c))).App
        (Expr.Lam s_c
          ((Expr.Lam f (Expr.Lam x inner_expanded)).App
            (Expr.Lam v_c (((Expr.Var s_c).App (Expr.Var s_c)).App
              (Expr.Var v_c))))))).contains v = false := by
  intro base s_c v_c z_c
  rw [freeVars]
  apply VarSet.union_not_contains_fwd
  · -- Lam z_c (App z_c z_c)
    rw [freeVars]
    by_cases hzv : (z_c == v) = true
    · exact VarSet.erase_self_not_contains _ _ _ hzv
    · have hzv' : (z_c == v) = false := by cases hz : (z_c == v); rfl; exact absurd hz hzv
      apply VarSet.erase_not_contains_fwd
      rw [freeVars]
      apply VarSet.union_not_contains_fwd <;>
        (rw [freeVars]; rw [VarSet.singleton_contains']; exact hzv')
  · -- Lam s_c (App (Lam f (Lam x inner)) (Lam v_c (...)))
    rw [freeVars]
    by_cases hsv : (s_c == v) = true
    · exact VarSet.erase_self_not_contains _ _ _ hsv
    · have hsv' : (s_c == v) = false := by cases hs : (s_c == v); rfl; exact absurd hs hsv
      apply VarSet.erase_not_contains_fwd
      rw [freeVars]
      apply VarSet.union_not_contains_fwd
      · -- (Lam f (Lam x inner_expanded))
        rw [freeVars]
        rcases hinner with h1 | hxv | hfv
        · apply VarSet.erase_not_contains_fwd
          rw [freeVars]
          apply VarSet.erase_not_contains_fwd
          exact h1
        · apply VarSet.erase_not_contains_fwd
          rw [freeVars]
          exact VarSet.erase_self_not_contains _ _ _ hxv
        · exact VarSet.erase_self_not_contains _ _ _ hfv
      · -- (Lam v_c (App (App s_c s_c) v_c))
        rw [freeVars]
        by_cases hvv : (v_c == v) = true
        · exact VarSet.erase_self_not_contains _ _ _ hvv
        · have hvv' : (v_c == v) = false := by cases hv : (v_c == v); rfl; exact absurd hv hvv
          apply VarSet.erase_not_contains_fwd
          rw [freeVars]
          apply VarSet.union_not_contains_fwd
          · rw [freeVars]
            apply VarSet.union_not_contains_fwd <;>
              (rw [freeVars]; rw [VarSet.singleton_contains']; exact hsv')
          · rw [freeVars]
            rw [VarSet.singleton_contains']
            exact hvv'

/-- Helper for the Fix-Lam case. Takes the inner freshness as a ready-made
    disjunction so the preservation proof can be structured without nested
    pattern matching. -/
theorem expandFix_fix_lam_free_from_disj
    (f : VarId) (x : VarId) (inner : Expr) (v : VarId)
    (hdisj : (freeVars (expandFix inner)).contains v = false ∨
              (x == v) = true ∨ (f == v) = true) :
    (freeVars (expandFix (.Fix f (.Lam x inner)))).contains v = false := by
  simp only [expandFix]
  exact expandFix_fix_lam_freeVars_not_contains f x (expandFix inner) v hdisj

/-- Helper for the non-Lam Fix case: if `body` is Fix but not `.Fix f (.Lam _ _)`
    at the top, `expandFix` reduces to `.Fix f (expandFix body)`. -/
theorem expandFix_nonlam_fix_unfold (f : VarId) (body : Expr) :
    expandFix (.Fix f body) = .Fix f (expandFix body) ∨
    ∃ x inner, body = .Lam x inner := by
  cases body with
  | Var _ => left; simp only [expandFix]
  | Lit _ => left; simp only [expandFix]
  | Builtin _ => left; simp only [expandFix]
  | Error => left; simp only [expandFix]
  | Lam x inner => right; exact ⟨x, inner, rfl⟩
  | Fix _ _ => left; simp only [expandFix]
  | App _ _ => left; simp only [expandFix]
  | Force _ => left; simp only [expandFix]
  | Delay _ => left; simp only [expandFix]
  | Constr _ _ => left; simp only [expandFix]
  | Case _ _ => left; simp only [expandFix]
  | Let _ _ => left; simp only [expandFix]

mutual
  /-- Main preservation theorem: if `v` is not free in `e`, it's not free in
      `expandFix e` either. -/
  theorem expandFix_freeVars_not_contains (e : Expr) (v : VarId)
      (h : (freeVars e).contains v = false) :
      (freeVars (expandFix e)).contains v = false := by
    cases e with
    | Var _ => simp only [expandFix]; exact h
    | Lit _ => simp only [expandFix]; exact h
    | Builtin _ => simp only [expandFix]; exact h
    | Error => simp only [expandFix]; exact h
    | Lam y body =>
      rw [freeVars] at h
      simp only [expandFix, freeVars]
      cases VarSet.erase_not_contains_imp' _ y v h with
      | inl hb =>
        exact VarSet.erase_not_contains_fwd _ _ _
          (expandFix_freeVars_not_contains body v hb)
      | inr hyv => exact VarSet.erase_self_not_contains _ _ _ hyv
    | Fix f body =>
      cases expandFix_nonlam_fix_unfold f body with
      | inl heq =>
        rw [heq, freeVars]
        rw [freeVars] at h
        cases VarSet.erase_not_contains_imp' _ f v h with
        | inl hb =>
          exact VarSet.erase_not_contains_fwd _ _ _
            (expandFix_freeVars_not_contains body v hb)
        | inr hfv => exact VarSet.erase_self_not_contains _ _ _ hfv
      | inr hex =>
        obtain ⟨x, inner, hbody⟩ := hex
        subst hbody
        rw [freeVars, freeVars] at h
        have hdecomp := erase_erase_decompose _ x f v h
        have hdisj : (freeVars (expandFix inner)).contains v = false ∨
                      (x == v) = true ∨ (f == v) = true := by
          rcases hdecomp with hi | hxv | hfv
          · exact .inl (expandFix_freeVars_not_contains inner v hi)
          · exact .inr (.inl hxv)
          · exact .inr (.inr hfv)
        exact expandFix_fix_lam_free_from_disj f x inner v hdisj
    | App f a =>
      rw [freeVars] at h
      simp only [expandFix, freeVars]
      have ⟨hf, ha⟩ := VarSet.union_not_contains' _ _ _ h
      exact VarSet.union_not_contains_fwd _ _ _
        (expandFix_freeVars_not_contains f v hf)
        (expandFix_freeVars_not_contains a v ha)
    | Force inner =>
      rw [freeVars] at h
      simp only [expandFix, freeVars]
      exact expandFix_freeVars_not_contains inner v h
    | Delay inner =>
      rw [freeVars] at h
      simp only [expandFix, freeVars]
      exact expandFix_freeVars_not_contains inner v h
    | Constr tag args =>
      rw [freeVars] at h
      simp only [expandFix, freeVars]
      exact expandFixList_freeVars_not_contains args v h
    | Case scrut alts =>
      rw [freeVars] at h
      simp only [expandFix, freeVars]
      have ⟨hs, ha⟩ := VarSet.union_not_contains' _ _ _ h
      exact VarSet.union_not_contains_fwd _ _ _
        (expandFix_freeVars_not_contains scrut v hs)
        (expandFixList_freeVars_not_contains alts v ha)
    | Let binds body =>
      rw [freeVars] at h
      simp only [expandFix, freeVars]
      exact expandFixBinds_freeVars_not_contains binds body v h
  termination_by sizeOf e

  theorem expandFixList_freeVars_not_contains (es : List Expr) (v : VarId)
      (h : (freeVarsList es).contains v = false) :
      (freeVarsList (expandFixList es)).contains v = false := by
    cases es with
    | nil => simp only [expandFixList]; exact h
    | cons e rest =>
      rw [freeVarsList] at h
      simp only [expandFixList, freeVarsList]
      have ⟨he, hr⟩ := VarSet.union_not_contains' _ _ _ h
      exact VarSet.union_not_contains_fwd _ _ _
        (expandFix_freeVars_not_contains e v he)
        (expandFixList_freeVars_not_contains rest v hr)
  termination_by sizeOf es

  theorem expandFixBinds_freeVars_not_contains (binds : List (VarId × Expr × Bool))
      (body : Expr) (v : VarId)
      (h : (freeVarsLet binds body).contains v = false) :
      (freeVarsLet (expandFixBinds binds) (expandFix body)).contains v = false := by
    match binds with
    | [] =>
      rw [freeVarsLet] at h
      simp only [expandFixBinds, freeVarsLet]
      exact expandFix_freeVars_not_contains body v h
    | (x, rhs, er) :: rest =>
      rw [freeVarsLet] at h
      simp only [expandFixBinds, freeVarsLet]
      have ⟨hrhs, hre⟩ := VarSet.union_not_contains' _ _ _ h
      apply VarSet.union_not_contains_fwd _ _ _
        (expandFix_freeVars_not_contains rhs v hrhs)
      cases VarSet.erase_not_contains_imp' _ x v hre with
      | inl hr_inner =>
        exact VarSet.erase_not_contains_fwd _ _ _
          (expandFixBinds_freeVars_not_contains rest body v hr_inner)
      | inr hxv => exact VarSet.erase_self_not_contains _ _ _ hxv
  termination_by sizeOf binds + sizeOf body
end

/-! ## lowerTotalExpr: lowerTotal + Fix expansion -/

/-- Lower an MIR expression to UPLC, handling Fix nodes by expanding them
    to Z combinator encodings before lowering. Fully compositional: no
    fresh counter threaded between sibling sub-expressions. -/
def lowerTotalExpr (env : List VarId) (e : Expr) : Option Term :=
  lowerTotal env (expandFix e)

/-- For Fix-free expressions, `lowerTotalExpr` equals `lowerTotal`. -/
theorem lowerTotalExpr_eq_lowerTotal (env : List VarId) (e : Expr)
    (h : fixCount e = 0) : lowerTotalExpr env e = lowerTotal env e := by
  simp only [lowerTotalExpr, expandFix_id e h]

/-! ## Fix-Lam canonical form

The Z combinator expansion of `Fix f (Lam x body)` lowers to a fixed UPLC
wrapper around the lowered body. `fixLamWrapUplc` is that UPLC wrapper
expressed as a function of the inner lowered body.
-/

/-- UPLC-level wrapper produced by lowering `expandFix (Fix f (Lam x body))`.
    Takes the body's UPLC lowering (computed under `x :: f :: s :: env` where
    `s` is the canonical fresh variable) and emits the full Z combinator form. -/
def fixLamWrapUplc (body_l : Moist.Plutus.Term.Term) : Moist.Plutus.Term.Term :=
  .Apply
    (.Lam 0 (.Apply (.Var 1) (.Var 1)))
    (.Lam 0 (.Apply (.Lam 0 (.Lam 0 body_l))
                    (.Lam 0 (.Apply (.Apply (.Var 2) (.Var 2)) (.Var 1)))))

/-- Small helper: `envLookupT (v :: env) v = some 0`. -/
theorem envLookupT_cons_self (v : VarId) (env : List VarId) :
    envLookupT (v :: env) v = some 0 := by
  unfold envLookupT envLookupT.go
  have : (v == v) = true := by rw [VarId.beq_true_iff]; exact ⟨rfl, rfl⟩
  simp [this]

/-- `envLookupT (y :: z :: env) z = some 1` when `y ≠ z`. -/
theorem envLookupT_cons_second (y z : VarId) (env : List VarId)
    (hne : (y == z) = false) :
    envLookupT (y :: z :: env) z = some 1 := by
  unfold envLookupT envLookupT.go
  simp [hne]
  show envLookupT.go z (z :: env) (0 + 1) = some 1
  rw [envLookupT.go_shift z (z :: env) 0 1]
  have : envLookupT.go z (z :: env) 0 = some 0 := envLookupT_cons_self z env
  rw [this]; rfl

/-- `lowerTotalExpr` on `Fix f (Lam x body)` decomposes into a map over the
    inner body's lowering under the canonical fresh `s` variable. -/
theorem lowerTotalExpr_fix_lam_canonical (env : List VarId) (f x : VarId) (body : Expr) :
    lowerTotalExpr env (.Fix f (.Lam x body)) =
      (lowerTotal (x :: f :: ⟨maxUidExpr (expandFix body) + 1, .gen, "s"⟩ :: env)
          (expandFix body)).map fixLamWrapUplc := by
  -- Unfold lowerTotalExpr and expandFix on the LHS
  have hunfold : lowerTotalExpr env (.Fix f (.Lam x body)) = lowerTotal env
      ((Expr.Lam ⟨maxUidExpr (expandFix body) + 1 + 2, .gen, "z"⟩
          ((Expr.Var ⟨maxUidExpr (expandFix body) + 1 + 2, .gen, "z"⟩).App
            (Expr.Var ⟨maxUidExpr (expandFix body) + 1 + 2, .gen, "z"⟩))).App
        (Expr.Lam ⟨maxUidExpr (expandFix body) + 1, .gen, "s"⟩
          ((Expr.Lam f (Expr.Lam x (expandFix body))).App
            (Expr.Lam ⟨maxUidExpr (expandFix body) + 1 + 1, .gen, "v"⟩
              (((Expr.Var ⟨maxUidExpr (expandFix body) + 1, .gen, "s"⟩).App
                  (Expr.Var ⟨maxUidExpr (expandFix body) + 1, .gen, "s"⟩)).App
                (Expr.Var ⟨maxUidExpr (expandFix body) + 1 + 1, .gen, "v"⟩)))))) := by
    simp only [lowerTotalExpr, expandFix]
  rw [hunfold]
  -- Introduce abbreviations
  let body' := expandFix body
  let base : Nat := maxUidExpr body' + 1
  let s_c : VarId := ⟨base, .gen, "s"⟩
  let v_c : VarId := ⟨base + 1, .gen, "v"⟩
  let z_c : VarId := ⟨base + 2, .gen, "z"⟩
  have hvs_ne : (v_c == s_c) = false := by
    rw [VarId.beq_false_iff]
    exact Or.inr (show base + 1 ≠ base from by omega)
  change lowerTotal env
      ((Expr.Lam z_c ((Expr.Var z_c).App (Expr.Var z_c))).App
        (Expr.Lam s_c
          ((Expr.Lam f (Expr.Lam x body')).App
            (Expr.Lam v_c (((Expr.Var s_c).App (Expr.Var s_c)).App (Expr.Var v_c))))))
    = (lowerTotal (x :: f :: s_c :: env) body').map fixLamWrapUplc
  -- Cases on the inner body lowering
  cases hbinner : lowerTotal (x :: f :: s_c :: env) body' with
  | none =>
    simp only [Option.map_none]
    simp only [lowerTotal, Option.bind_eq_bind,
               envLookupT_cons_self, envLookupT_cons_second _ _ env hvs_ne,
               hbinner, Option.bind_none, Option.bind_some]
  | some bv =>
    simp only [Option.map_some]
    simp only [lowerTotal, Option.bind_eq_bind,
               envLookupT_cons_self, envLookupT_cons_second _ _ env hvs_ne,
               hbinner, Option.bind_some]
    rfl

/-- Version of `lowerTotalExpr_fix_lam_canonical` parameterized by any fresh
    `s` variable (not just the canonical one from `maxUidExpr`). Uses
    `lowerTotal_env_swap_unused` to switch between fresh variables. -/
theorem lowerTotalExpr_fix_lam_with_fresh (env : List VarId) (f x : VarId) (body : Expr)
    (s_pick : VarId) (hs : (freeVars (expandFix body)).contains s_pick = false) :
    lowerTotalExpr env (.Fix f (.Lam x body)) =
      (lowerTotal (x :: f :: s_pick :: env) (expandFix body)).map fixLamWrapUplc := by
  rw [lowerTotalExpr_fix_lam_canonical]
  have hs_c : (freeVars (expandFix body)).contains
      ⟨maxUidExpr (expandFix body) + 1, .gen, "s"⟩ = false :=
    maxUidExpr_fresh _ _ (show maxUidExpr (expandFix body) + 1 > maxUidExpr (expandFix body)
      from Nat.lt_succ_self _)
  -- By env_swap, we can replace s_canonical with s_pick
  have := lowerTotal_env_swap_unused [x, f] env
    ⟨maxUidExpr (expandFix body) + 1, .gen, "s"⟩ s_pick (expandFix body) hs_c hs
  rw [show (x :: f :: (⟨maxUidExpr (expandFix body) + 1, .gen, "s"⟩ : VarId) :: env) =
        [x, f] ++ (⟨maxUidExpr (expandFix body) + 1, .gen, "s"⟩ : VarId) :: env from rfl]
  rw [show (x :: f :: s_pick :: env) = [x, f] ++ s_pick :: env from rfl]
  rw [this]

/-! ## `lowerTotal` succeeds only on Fix-free expressions

If `lowerTotal env e` returns `some _`, then `e` has no Fix nodes. This is
straightforward structural induction: every Fix node makes `lowerTotal`
return `none`, and `none` propagates through every other constructor's
`do`-block.
-/

mutual
  theorem lowerTotal_some_fixCount_zero (env : List VarId) (e : Expr) (t : Term)
      (h : lowerTotal env e = some t) : fixCount e = 0 := by
    match e with
    | .Var _ => simp [fixCount]
    | .Lit _ => simp [fixCount]
    | .Builtin _ => simp [fixCount]
    | .Error => simp [fixCount]
    | .Lam x body =>
      simp only [lowerTotal, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨body', hbody, _⟩ := h
      simp only [fixCount]
      exact lowerTotal_some_fixCount_zero (x :: env) body body' hbody
    | .App f x =>
      simp only [lowerTotal, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨f', hf, x', hx, _⟩ := h
      simp only [fixCount]
      have := lowerTotal_some_fixCount_zero env f f' hf
      have := lowerTotal_some_fixCount_zero env x x' hx
      omega
    | .Force inner =>
      simp only [lowerTotal, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨inner', hinner, _⟩ := h
      simp only [fixCount]
      exact lowerTotal_some_fixCount_zero env inner inner' hinner
    | .Delay inner =>
      simp only [lowerTotal, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨inner', hinner, _⟩ := h
      simp only [fixCount]
      exact lowerTotal_some_fixCount_zero env inner inner' hinner
    | .Constr _ args =>
      simp only [lowerTotal, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨args', hargs, _⟩ := h
      simp only [fixCount]
      exact lowerTotalList_some_fixCountList_zero env args args' hargs
    | .Case scrut alts =>
      simp only [lowerTotal, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨scrut', hscrut, alts', halts, _⟩ := h
      simp only [fixCount]
      have := lowerTotal_some_fixCount_zero env scrut scrut' hscrut
      have := lowerTotalList_some_fixCountList_zero env alts alts' halts
      omega
    | .Let binds body =>
      simp only [lowerTotal] at h
      simp only [fixCount]
      exact lowerTotalLet_some_fixCount_zero env binds body t h
    | .Fix _ _ => simp only [lowerTotal] at h; injection h
  termination_by sizeOf e

  theorem lowerTotalList_some_fixCountList_zero (env : List VarId) (es : List Expr)
      (ts : List Term) (h : lowerTotalList env es = some ts) :
      fixCountList es = 0 := by
    match es with
    | [] => simp [fixCountList]
    | e :: rest =>
      simp only [lowerTotalList, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨t, ht, ts', hts, _⟩ := h
      simp only [fixCountList]
      have := lowerTotal_some_fixCount_zero env e t ht
      have := lowerTotalList_some_fixCountList_zero env rest ts' hts
      omega
  termination_by sizeOf es

  theorem lowerTotalLet_some_fixCount_zero (env : List VarId)
      (binds : List (VarId × Expr × Bool)) (body : Expr) (t : Term)
      (h : lowerTotalLet env binds body = some t) :
      fixCountBinds binds + fixCount body = 0 := by
    match binds with
    | [] =>
      simp only [lowerTotalLet] at h
      simp only [fixCountBinds, Nat.zero_add]
      exact lowerTotal_some_fixCount_zero env body t h
    | (x, rhs, _) :: rest =>
      simp only [lowerTotalLet, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨rhs', hrhs, rest', hrest, _⟩ := h
      simp only [fixCountBinds]
      have := lowerTotal_some_fixCount_zero env rhs rhs' hrhs
      have := lowerTotalLet_some_fixCount_zero (x :: env) rest body rest' hrest
      omega
  termination_by sizeOf binds + sizeOf body
end

end Moist.MIR
