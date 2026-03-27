import Moist.MIR.Expr
import Moist.MIR.Analysis

namespace Moist.MIR

open Moist.Plutus.Term (Term Const BuiltinType BuiltinFun)

/-! # Total MIR → UPLC Lowering -/

def envLookupT.go (v : VarId) : List VarId → Nat → Option Nat
  | [], _ => none
  | x :: xs, n => if x == v then some n else envLookupT.go v xs (n + 1)

def envLookupT (env : List VarId) (v : VarId) : Option Nat :=
  envLookupT.go v env 0

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

private theorem VarId.beq_true_iff (a b : VarId) : (a == b) = true ↔ a.uid = b.uid :=
  ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩

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
          exact absurd (by rw [VarId.beq_true_iff] at hyx h ⊢; omega : (w == v) = true) hwv
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

private theorem VarId.beq_trans (a b c : VarId)
    (h1 : (a == b) = true) (h2 : (b == c) = true) : (a == c) = true := by
  rw [VarId.beq_true_iff] at *; omega

private theorem List.any_beq_varid_trans (xs : List VarId) (v x : VarId)
    (hvx : (v == x) = true) (hv : xs.any (· == v) = true) : xs.any (· == x) = true := by
  induction xs with
  | nil => simp at hv
  | cons h t ih =>
    simp only [List.any_cons, Bool.or_eq_true_iff] at *
    exact hv.elim (fun hl => .inl (VarId.beq_trans h v x hl hvx)) (fun hr => .inr (ih hr))

theorem VarSet.singleton_contains' (v x : VarId) :
    (VarSet.singleton v).contains x = (v == x) := by
  unfold VarSet.singleton VarSet.contains; rw [← Array.any_toList]; simp [List.any]

private theorem VarSet.insert_not_contains (s : VarSet) (v x : VarId)
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

private theorem foldl_insert_not_contains (acc : VarSet) (elems : List VarId) (x : VarId)
    (h : (elems.foldl (fun a v => a.insert v) acc).contains x = false) :
    acc.contains x = false := by
  induction elems generalizing acc with
  | nil => exact h
  | cons v rest ih => exact (VarSet.insert_not_contains _ v x (ih _ (by simpa using h))).1

private theorem foldl_insert_elems_not_match (acc : VarSet) (elems : List VarId) (x : VarId)
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

private theorem list_filter_any_false {xs : List VarId} {x y : VarId}
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
        have := VarId.beq_trans y w x (by rw [VarId.beq_true_iff] at hwy ⊢; omega) hwx
        rw [this] at hyx; exact Bool.noConfusion hyx
    · simp only [hwny, ite_true, List.any_cons, Bool.or_eq_false_iff] at hf; exact ⟨hf.1, ih hf.2⟩

theorem VarSet.erase_not_contains_imp' (s : VarSet) (y x : VarId)
    (h : (s.erase y).contains x = false) : s.contains x = false ∨ (y == x) = true := by
  cases hyx : (y == x)
  · left; unfold VarSet.erase VarSet.contains at h; rw [← Array.any_toList, Array.toList_filter] at h
    unfold VarSet.contains; rw [← Array.any_toList]; exact list_filter_any_false h hyx
  · right; rfl

/-! ## lowerTotal append unused -/

-- Helper: env agreement for shadow case
private theorem envLookupT_shadow_agree (env : List VarId) (x y : VarId)
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
          have : (v == x) = true := by rw [VarId.beq_true_iff]; omega
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
    | .Fix _ _ => simp [lowerTotal.eq_12]
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

/-! ## Fix expansion -/

partial def fixCount : Expr → Nat
  | .Fix _ body => 1 + fixCount body
  | .Lam _ body => fixCount body
  | .App f x => fixCount f + fixCount x
  | .Force e | .Delay e => fixCount e
  | .Constr _ args => args.foldl (fun acc e => acc + fixCount e) 0
  | .Case scrut alts =>
    fixCount scrut + alts.foldl (fun acc e => acc + fixCount e) 0
  | .Let binds body =>
    binds.foldl (fun acc (_, rhs, _) => acc + fixCount rhs) 0 + fixCount body
  | _ => 0

partial def expandFixOnce (fresh : Nat) : Expr → Expr × Nat
  | .Fix f (.Lam x e) =>
    let s : VarId := ⟨fresh, "s"⟩; let v : VarId := ⟨fresh + 1, "v"⟩
    let selfApp := Expr.Lam v (.App (.App (.Var s) (.Var s)) (.Var v))
    let z : VarId := ⟨fresh + 2, "z"⟩
    let e' := (subst f selfApp e).run ⟨fresh + 3⟩ |>.1
    (.App (.Lam z (.App (.Var z) (.Var z))) (.Lam s (.Lam x e')), fresh + 100)
  | .Fix f body => let (b, f') := expandFixOnce fresh body; (.Fix f b, f')
  | .Lam x body => let (b, f') := expandFixOnce fresh body; (.Lam x b, f')
  | .App f x =>
    let (f', fr1) := expandFixOnce fresh f; let (x', fr2) := expandFixOnce fr1 x; (.App f' x', fr2)
  | .Let binds body =>
    let (bs, fr1) := binds.foldl (fun (acc, fr) (v, rhs, er) =>
      let (r, f') := expandFixOnce fr rhs; (acc ++ [(v, r, er)], f')) ([], fresh)
    let (b, fr2) := expandFixOnce fr1 body; (.Let bs b, fr2)
  | .Force e => let (e', f) := expandFixOnce fresh e; (.Force e', f)
  | .Delay e => let (e', f) := expandFixOnce fresh e; (.Delay e', f)
  | .Constr tag args =>
    let (as, fr) := args.foldl (fun (acc, fr) e =>
      let (e', f') := expandFixOnce fr e; (acc ++ [e'], f')) ([], fresh)
    (.Constr tag as, fr)
  | .Case scrut alts =>
    let (s, fr1) := expandFixOnce fresh scrut
    let (as, fr2) := alts.foldl (fun (acc, fr) e =>
      let (e', f') := expandFixOnce fr e; (acc ++ [e'], f')) ([], fr1)
    (.Case s as, fr2)
  | e => (e, fresh)

def expandAllFix (fuel : Nat) (fresh : Nat) (e : Expr) : Expr :=
  match fuel with
  | 0 => e
  | n + 1 =>
    let (e', fresh') := expandFixOnce fresh e
    if fixCount e' == 0 then e' else expandAllFix n fresh' e'

def lowerTotalExpr (e : Expr) : Option Term :=
  let expanded := expandAllFix 100 10000 e
  lowerTotal [] expanded

end Moist.MIR
