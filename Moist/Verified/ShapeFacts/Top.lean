import Moist.Verified.ShapeFacts.Lift
import Moist.Verified.MIR

/-! # From fact refinement to contextual refinement

With no recorded facts, `FactRel` on a well-scoped program yields
`MIRCtxRefines` (`mirCtxRefines_of_factRel`). Lowering only depends on the
positions of free variables, so any lowering environment can be replaced by
a distinct one that keeps the first occurrence of every free variable of the
program and uses fresh names elsewhere (`canonEnv`).
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR
open Moist.Verified Moist.Verified.MIR Moist.Verified.Contextual

/-! ## Free variables of lowered expressions -/

theorem varSet_contains_congr (s : VarSet) {x y : VarId} (h : (x == y) = true) :
    s.contains x = s.contains y := by
  simp only [VarSet.contains]
  congr 1; funext a
  have h1 := (VarId.beq_true_iff x y).mp h
  show (a.origin == x.origin && a.uid == x.uid) = (a.origin == y.origin && a.uid == y.uid)
  rw [h1.1, h1.2]

theorem varSet_contains_of_erase {s : VarSet} {y v : VarId} (h : (s.erase y).contains v = true) :
    s.contains v = true ∧ (y == v) = false := by
  constructor
  · cases hs : s.contains v
    · rw [VarSet.erase_not_contains_fwd s y v hs] at h; cases h
    · rfl
  · cases hyv : (y == v)
    · rfl
    · rw [← varSet_contains_congr _ hyv, VarSet.contains_erase_self] at h; cases h

theorem varSet_contains_union {s₁ s₂ : VarSet} {v : VarId} (h : (s₁.union s₂).contains v = true) :
    s₁.contains v = true ∨ s₂.contains v = true := by
  cases h₁ : s₁.contains v
  · cases h₂ : s₂.contains v
    · rw [VarSet.union_not_contains_fwd s₁ s₂ v h₁ h₂] at h; cases h
    · exact .inr rfl
  · exact .inl rfl

/-- Agreement of two environments on the free variables of an expression. -/
def AgreeOn (s : VarSet) (env₁ env₂ : List VarId) : Prop :=
  ∀ v, s.contains v = true → envLookupT env₁ v = envLookupT env₂ v

theorem AgreeOn.cons {s : VarSet} {env₁ env₂ : List VarId} (y : VarId)
    (h : AgreeOn (s.erase y) env₁ env₂) : AgreeOn s (y :: env₁) (y :: env₂) := by
  intro v hv
  rw [envLookupT_cons, envLookupT_cons]
  split
  · rfl
  · rename_i hyv
    rw [h v (VarSet.contains_erase_ne s y v (by simpa using hyv) hv)]

theorem AgreeOn.mono {s t : VarSet} {env₁ env₂ : List VarId} (h : AgreeOn s env₁ env₂)
    (hst : ∀ v, t.contains v = true → s.contains v = true) : AgreeOn t env₁ env₂ :=
  fun v hv => h v (hst v hv)

mutual
  theorem lowerTotal_agree (env₁ env₂ : List VarId) (e : Expr)
      (h : AgreeOn (freeVars e) env₁ env₂) : lowerTotal env₁ e = lowerTotal env₂ e := by
    match e with
    | .Var v =>
      have := h v (by simp only [freeVars]; exact VarSet.contains_singleton_self v)
      simp only [lowerTotal.eq_1, this]
    | .Lit (c, ty) => simp only [lowerTotal.eq_2]
    | .Builtin b => simp only [lowerTotal.eq_3]
    | .Error => simp only [lowerTotal.eq_4]
    | .Lam y body =>
      simp only [lowerTotal.eq_5,
        lowerTotal_agree (y :: env₁) (y :: env₂) body (AgreeOn.cons y (by simpa [freeVars] using h))]
    | .App f a =>
      simp only [freeVars] at h
      simp only [lowerTotal.eq_6,
        lowerTotal_agree env₁ env₂ f (h.mono fun v hv => VarSet.contains_union_left _ _ v hv),
        lowerTotal_agree env₁ env₂ a (h.mono fun v hv => VarSet.contains_union_right _ _ v hv)]
    | .Force inner =>
      simp only [lowerTotal.eq_7, lowerTotal_agree env₁ env₂ inner (by simpa [freeVars] using h)]
    | .Delay inner =>
      simp only [lowerTotal.eq_8, lowerTotal_agree env₁ env₂ inner (by simpa [freeVars] using h)]
    | .Constr _ args =>
      simp only [lowerTotal.eq_9, lowerTotalList_agree env₁ env₂ args (by simpa [freeVars] using h)]
    | .Case scrut alts =>
      simp only [freeVars] at h
      simp only [lowerTotal.eq_10,
        lowerTotal_agree env₁ env₂ scrut (h.mono fun v hv => VarSet.contains_union_left _ _ v hv),
        lowerTotalList_agree env₁ env₂ alts (h.mono fun v hv => VarSet.contains_union_right _ _ v hv)]
    | .Let binds body =>
      simp only [lowerTotal.eq_11, lowerTotalLet_agree env₁ env₂ binds body (by simpa [freeVars] using h)]
    | .Fix _ _ => simp only [lowerTotal.eq_12]
  termination_by sizeOf e

  theorem lowerTotalList_agree (env₁ env₂ : List VarId) (es : List Expr)
      (h : AgreeOn (freeVarsList es) env₁ env₂) : lowerTotalList env₁ es = lowerTotalList env₂ es := by
    match es with
    | [] => simp [lowerTotalList.eq_1]
    | e :: rest =>
      simp only [freeVarsList] at h
      simp only [lowerTotalList.eq_2,
        lowerTotal_agree env₁ env₂ e (h.mono fun v hv => VarSet.contains_union_left _ _ v hv),
        lowerTotalList_agree env₁ env₂ rest (h.mono fun v hv => VarSet.contains_union_right _ _ v hv)]
  termination_by sizeOf es

  theorem lowerTotalLet_agree (env₁ env₂ : List VarId) (binds : List (VarId × Expr × Bool))
      (body : Expr) (h : AgreeOn (freeVarsLet binds body) env₁ env₂) :
      lowerTotalLet env₁ binds body = lowerTotalLet env₂ binds body := by
    match binds with
    | [] => simp only [lowerTotalLet.eq_1, lowerTotal_agree env₁ env₂ body (by simpa [freeVarsLet] using h)]
    | (y, rhs, _) :: rest =>
      simp only [freeVarsLet] at h
      simp only [lowerTotalLet.eq_2,
        lowerTotal_agree env₁ env₂ rhs (h.mono fun v hv => VarSet.contains_union_left _ _ v hv),
        lowerTotalLet_agree (y :: env₁) (y :: env₂) rest body
          (AgreeOn.cons y (h.mono fun v hv => VarSet.contains_union_right _ _ v hv))]
  termination_by sizeOf binds + sizeOf body
end

theorem lowerTotalExpr_agree {env₁ env₂ : List VarId} {e : Expr} (h : AgreeOn (freeVars e) env₁ env₂) :
    lowerTotalExpr env₁ e = lowerTotalExpr env₂ e := by
  simp only [lowerTotalExpr]
  apply lowerTotal_agree
  intro v hv
  apply h v
  cases hc : (freeVars e).contains v
  · rw [expandFix_freeVars_not_contains e v hc] at hv; cases hv
  · rfl

mutual
  theorem lowerTotal_bound (env : List VarId) (e : Expr) (t : Term)
      (h : lowerTotal env e = some t) :
      ∀ v, (freeVars e).contains v = true → (envLookupT env v).isSome = true := by
    intro v hv
    match e with
    | .Var x =>
      simp only [freeVars, VarSet.singleton_contains'] at hv
      simp only [lowerTotal.eq_1] at h
      rw [← envLookupT_congr hv]
      cases hx : envLookupT env x with
      | none => rw [hx] at h; cases h
      | some _ => rfl
    | .Lit _ | .Builtin _ | .Error => simp [freeVars] at hv
    | .Lam y body =>
      simp only [freeVars] at hv
      obtain ⟨hv, hyv⟩ := varSet_contains_of_erase hv
      simp only [lowerTotal.eq_5, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨tb, htb, _⟩ := h
      have := lowerTotal_bound (y :: env) body tb htb v hv
      rw [envLookupT_cons_neq y v env hyv] at this
      simpa using this
    | .App f a =>
      simp only [freeVars] at hv
      simp only [lowerTotal.eq_6, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨tf, htf, ta, hta, _⟩ := h
      rcases varSet_contains_union hv with hv | hv
      · exact lowerTotal_bound env f tf htf v hv
      · exact lowerTotal_bound env a ta hta v hv
    | .Force inner =>
      simp only [freeVars] at hv
      simp only [lowerTotal.eq_7, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ti, hti, _⟩ := h
      exact lowerTotal_bound env inner ti hti v hv
    | .Delay inner =>
      simp only [freeVars] at hv
      simp only [lowerTotal.eq_8, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ti, hti, _⟩ := h
      exact lowerTotal_bound env inner ti hti v hv
    | .Constr _ args =>
      simp only [freeVars] at hv
      simp only [lowerTotal.eq_9, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ts, hts, _⟩ := h
      exact lowerTotalList_bound env args ts hts v hv
    | .Case scrut alts =>
      simp only [freeVars] at hv
      simp only [lowerTotal.eq_10, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ts, hts, talts, htalts, _⟩ := h
      rcases varSet_contains_union hv with hv | hv
      · exact lowerTotal_bound env scrut ts hts v hv
      · exact lowerTotalList_bound env alts talts htalts v hv
    | .Let binds body =>
      simp only [freeVars] at hv
      simp only [lowerTotal.eq_11] at h
      exact lowerTotalLet_bound env binds body t h v hv
    | .Fix _ _ => simp only [lowerTotal.eq_12] at h; cases h
  termination_by sizeOf e

  theorem lowerTotalList_bound (env : List VarId) (es : List Expr) (ts : List Term)
      (h : lowerTotalList env es = some ts) :
      ∀ v, (freeVarsList es).contains v = true → (envLookupT env v).isSome = true := by
    intro v hv
    match es with
    | [] => simp [freeVarsList] at hv
    | e :: rest =>
      simp only [freeVarsList] at hv
      simp only [lowerTotalList.eq_2, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨te, hte, trest, htrest, _⟩ := h
      rcases varSet_contains_union hv with hv | hv
      · exact lowerTotal_bound env e te hte v hv
      · exact lowerTotalList_bound env rest trest htrest v hv
  termination_by sizeOf es

  theorem lowerTotalLet_bound (env : List VarId) (binds : List (VarId × Expr × Bool)) (body : Expr)
      (t : Term) (h : lowerTotalLet env binds body = some t) :
      ∀ v, (freeVarsLet binds body).contains v = true → (envLookupT env v).isSome = true := by
    intro v hv
    match binds with
    | [] =>
      simp only [freeVarsLet] at hv
      simp only [lowerTotalLet.eq_1] at h
      exact lowerTotal_bound env body t h v hv
    | (y, rhs, _) :: rest =>
      simp only [freeVarsLet] at hv
      simp only [lowerTotalLet.eq_2, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨tr, htr, trest, htrest, _⟩ := h
      rcases varSet_contains_union hv with hv | hv
      · exact lowerTotal_bound env rhs tr htr v hv
      · obtain ⟨hv, hyv⟩ := varSet_contains_of_erase hv
        have := lowerTotalLet_bound (y :: env) rest body trest htrest v hv
        rw [envLookupT_cons_neq y v env hyv] at this
        simpa using this
  termination_by sizeOf binds + sizeOf body
end

/-! ## Truncating the environment of a closed lowering -/

theorem envLookupT_take {env : List VarId} {x : VarId} {i k : Nat} (h : envLookupT env x = some i)
    (hik : i < k) : envLookupT (env.take k) x = some i := by
  induction env generalizing i k with
  | nil => simp [envLookupT, envLookupT.go] at h
  | cons y ys ih =>
    cases k with
    | zero => omega
    | succ k =>
      simp only [List.take_succ_cons]
      rw [envLookupT_cons] at h ⊢
      split
      · rename_i hyx; simp [hyx] at h; subst h; rfl
      · rename_i hyx
        simp only [hyx, Bool.false_eq_true, if_false] at h ⊢
        cases hl : envLookupT ys x with
        | none => rw [hl] at h; cases h
        | some j =>
          rw [hl] at h; simp at h; subst h
          rw [ih hl (by omega)]; rfl

mutual
  theorem lowerTotal_take (env : List VarId) (e : Expr) (t : Term) (k : Nat)
      (h : lowerTotal env e = some t) (hc : closedAt k t = true) :
      lowerTotal (env.take k) e = some t := by
    match e with
    | .Var x =>
      simp only [lowerTotal.eq_1] at h ⊢
      cases hx : envLookupT env x with
      | none => rw [hx] at h; cases h
      | some i =>
        rw [hx] at h; cases h
        simp only [closedAt, decide_eq_true_eq] at hc
        rw [envLookupT_take hx (by omega)]
    | .Lit (c, ty) => simpa only [lowerTotal.eq_2] using h
    | .Builtin b => simpa only [lowerTotal.eq_3] using h
    | .Error => simpa only [lowerTotal.eq_4] using h
    | .Lam y body =>
      simp only [lowerTotal.eq_5, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨tb, htb, heq⟩ := h
      cases heq
      simp only [closedAt] at hc
      have := lowerTotal_take (y :: env) body tb (k + 1) htb hc
      simp only [List.take_succ_cons] at this
      exact ⟨tb, this, rfl⟩
    | .App f a =>
      simp only [lowerTotal.eq_6, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨tf, htf, ta, hta, heq⟩ := h
      cases heq
      simp only [closedAt, Bool.and_eq_true] at hc
      exact ⟨tf, lowerTotal_take env f tf k htf hc.1, ta, lowerTotal_take env a ta k hta hc.2, rfl⟩
    | .Force inner =>
      simp only [lowerTotal.eq_7, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨ti, hti, heq⟩ := h
      cases heq
      simp only [closedAt] at hc
      exact ⟨ti, lowerTotal_take env inner ti k hti hc, rfl⟩
    | .Delay inner =>
      simp only [lowerTotal.eq_8, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨ti, hti, heq⟩ := h
      cases heq
      simp only [closedAt] at hc
      exact ⟨ti, lowerTotal_take env inner ti k hti hc, rfl⟩
    | .Constr _ args =>
      simp only [lowerTotal.eq_9, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨ts, hts, heq⟩ := h
      cases heq
      simp only [closedAt] at hc
      exact ⟨ts, lowerTotalList_take env args ts k hts hc, rfl⟩
    | .Case scrut alts =>
      simp only [lowerTotal.eq_10, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨ts, hts, talts, htalts, heq⟩ := h
      cases heq
      simp only [closedAt, Bool.and_eq_true] at hc
      exact ⟨ts, lowerTotal_take env scrut ts k hts hc.1, talts,
        lowerTotalList_take env alts talts k htalts hc.2, rfl⟩
    | .Let binds body =>
      simp only [lowerTotal.eq_11] at h ⊢
      exact lowerTotalLet_take env binds body t k h hc
    | .Fix _ _ => simp only [lowerTotal.eq_12] at h; cases h
  termination_by sizeOf e

  theorem lowerTotalList_take (env : List VarId) (es : List Expr) (ts : List Term) (k : Nat)
      (h : lowerTotalList env es = some ts) (hc : closedAtList k ts = true) :
      lowerTotalList (env.take k) es = some ts := by
    match es with
    | [] => simpa only [lowerTotalList.eq_1] using h
    | e :: rest =>
      simp only [lowerTotalList.eq_2, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨te, hte, trest, htrest, heq⟩ := h
      cases heq
      simp only [closedAtList, Bool.and_eq_true] at hc
      exact ⟨te, lowerTotal_take env e te k hte hc.1, trest,
        lowerTotalList_take env rest trest k htrest hc.2, rfl⟩
  termination_by sizeOf es

  theorem lowerTotalLet_take (env : List VarId) (binds : List (VarId × Expr × Bool)) (body : Expr)
      (t : Term) (k : Nat) (h : lowerTotalLet env binds body = some t) (hc : closedAt k t = true) :
      lowerTotalLet (env.take k) binds body = some t := by
    match binds with
    | [] =>
      simp only [lowerTotalLet.eq_1] at h ⊢
      exact lowerTotal_take env body t k h hc
    | (y, rhs, _) :: rest =>
      simp only [lowerTotalLet.eq_2, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨tr, htr, trest, htrest, heq⟩ := h
      cases heq
      simp only [closedAt, Bool.and_eq_true] at hc
      have := lowerTotalLet_take (y :: env) rest body trest (k + 1) htrest hc.1
      simp only [List.take_succ_cons] at this
      exact ⟨tr, lowerTotal_take env rhs tr k htr hc.2, trest, this, rfl⟩
  termination_by sizeOf binds + sizeOf body
end

theorem envLookupT_append_of_some {env more : List VarId} {x : VarId} {i : Nat}
    (h : envLookupT env x = some i) : envLookupT (env ++ more) x = some i := by
  induction env generalizing i with
  | nil => simp [envLookupT, envLookupT.go] at h
  | cons y ys ih =>
    rw [List.cons_append, envLookupT_cons]
    rw [envLookupT_cons] at h
    split
    · rename_i hyx; simp [hyx] at h; subst h; rfl
    · rename_i hyx
      simp only [hyx, Bool.false_eq_true, if_false] at h ⊢
      cases hl : envLookupT ys x with
      | none => rw [hl] at h; cases h
      | some j => rw [hl] at h; rw [ih hl]; exact h

theorem lowerTotal_append_of_some {env more : List VarId} {e : Expr} {t : Term}
    (h : lowerTotal env e = some t) : lowerTotal (env ++ more) e = some t := by
  rw [← h]
  apply lowerTotal_agree
  intro v hv
  have hb := lowerTotal_bound env e t h v hv
  cases hl : envLookupT env v with
  | none => rw [hl] at hb; cases hb
  | some i => simp [envLookupT_append_of_some hl]

/-! ## Canonical environments -/

/-- Keep the first occurrence of every kept name and use fresh names elsewhere. -/
def canonEnv (keep : VarId → Bool) (D : Nat) : List VarId → List VarId → Nat → List VarId
  | _, [], _ => []
  | seen, y :: ys, i =>
    (if keep y && (envLookupT seen y).isNone then y else ⟨D + i, .source, ""⟩) ::
      canonEnv keep D (y :: seen) ys (i + 1)

theorem canonEnv_length (keep : VarId → Bool) (D : Nat) :
    ∀ (seen env : List VarId) (i : Nat), (canonEnv keep D seen env i).length = env.length
  | _, [], _ => rfl
  | seen, y :: ys, i => by simp [canonEnv, canonEnv_length keep D (y :: seen) ys (i + 1)]

theorem keep_congr_of {keep : VarId → Bool}
    (hkeep : ∀ x y, (x == y) = true → keep x = keep y) {x y : VarId} (h : (x == y) = true) :
    keep x = keep y := hkeep x y h

/-- Names found in a canonical environment are kept names not seen before, or
    fresh names. -/
theorem canonEnv_found (keep : VarId → Bool) (D : Nat)
    (hkeep : ∀ x y, (x == y) = true → keep x = keep y) :
    ∀ (seen env : List VarId) (i : Nat) (y : VarId),
      (envLookupT (canonEnv keep D seen env i) y).isSome = true →
      (keep y = true ∧ envLookupT seen y = none) ∨ D + i ≤ y.uid
  | _, [], _, y, h => by simp [canonEnv, envLookupT, envLookupT.go] at h
  | seen, z :: zs, i, y, h => by
    simp only [canonEnv] at h
    have rest : (envLookupT (canonEnv keep D (z :: seen) zs (i + 1)) y).isSome = true →
        (keep y = true ∧ envLookupT seen y = none) ∨ D + i ≤ y.uid := by
      intro h'
      rcases canonEnv_found keep D hkeep (z :: seen) zs (i + 1) y h' with ⟨hk, hs⟩ | hu
      · left
        refine ⟨hk, ?_⟩
        rw [envLookupT_cons] at hs
        split at hs
        · cases hs
        · cases hl : envLookupT seen y with
          | none => rfl
          | some _ => rw [hl] at hs; cases hs
      · right; omega
    by_cases hk : (keep z && (envLookupT seen z).isNone) = true
    · rw [if_pos hk, envLookupT_cons] at h
      split at h
      · rename_i hzy
        simp only [Bool.and_eq_true] at hk
        left
        refine ⟨by rw [← hkeep z y hzy]; exact hk.1, ?_⟩
        rw [← envLookupT_congr hzy]; simpa using hk.2
      · exact rest (by simpa using h)
    · rw [if_neg hk, envLookupT_cons] at h
      split at h
      · rename_i hzy
        right
        have := (VarId.beq_true_iff _ y).mp hzy
        simp at this; omega
      · exact rest (by simpa using h)

theorem canonEnv_distinct (keep : VarId → Bool) (D : Nat)
    (hkeep : ∀ x y, (x == y) = true → keep x = keep y) (hD : ∀ y, keep y = true → y.uid < D) :
    ∀ (seen env : List VarId) (i : Nat), EnvDistinct (canonEnv keep D seen env i)
  | _, [], _ => trivial
  | seen, z :: zs, i => by
    refine ⟨?_, canonEnv_distinct keep D hkeep hD (z :: seen) zs (i + 1)⟩
    cases hc : envLookupT (canonEnv keep D (z :: seen) zs (i + 1))
        (if keep z && (envLookupT seen z).isNone then z else ⟨D + i, .source, ""⟩) with
    | none => rfl
    | some _ =>
      exfalso
      have found := canonEnv_found keep D hkeep (z :: seen) zs (i + 1) _ (by rw [hc]; rfl)
      split at found
      · rename_i hk
        simp only [Bool.and_eq_true] at hk
        rcases found with ⟨_, hs⟩ | hu
        · rw [envLookupT_cons] at hs; simp [varId_beq_self] at hs
        · have := hD z hk.1; omega
      · rcases found with ⟨hk, _⟩ | hu
        · have := hD _ hk; simp at this; omega
        · simp at hu; omega

theorem canonEnv_lookup (keep : VarId → Bool) (D : Nat)
    (hkeep : ∀ x y, (x == y) = true → keep x = keep y) (hD : ∀ y, keep y = true → y.uid < D) :
    ∀ (seen env : List VarId) (i : Nat) (y : VarId), keep y = true → envLookupT seen y = none →
      envLookupT (canonEnv keep D seen env i) y = envLookupT env y
  | _, [], _, y, _, _ => rfl
  | seen, z :: zs, i, y, hk, hs => by
    simp only [canonEnv]
    rw [envLookupT_cons, envLookupT_cons]
    by_cases hzy : (z == y) = true
    · have hkz : keep z = true := by rw [hkeep z y hzy]; exact hk
      have hsz : (envLookupT seen z).isNone = true := by rw [envLookupT_congr hzy]; simp [hs]
      simp [hkz, hsz, hzy]
    · have hzy' : (z == y) = false := by simpa using hzy
      have hc : ((if keep z && (envLookupT seen z).isNone then z else
          (⟨D + i, .source, ""⟩ : VarId)) == y) = false := by
        split
        · exact hzy'
        · rw [VarId.beq_false_iff]; right; have := hD y hk; simp; omega
      simp only [hc, hzy', Bool.false_eq_true, if_false]
      rw [canonEnv_lookup keep D hkeep hD (z :: seen) zs (i + 1) y hk (by
        rw [envLookupT_cons_neq z y seen hzy', hs]; rfl)]

/-! ## Well-scoped programs avoid every name they do not bind -/

def AvoidOK (seen fv : VarSet) (bound : Nat) (avoid : List VarId) : Prop :=
  ∀ y, (envLookupT avoid y).isSome = true → seen.contains y = true ∨ fv.contains y = true ∨ bound < y.uid

theorem AvoidOK.mono {seen seen' fv : VarSet} {b b' : Nat} {avoid : List VarId}
    (h : AvoidOK seen fv b avoid) (hs : ∀ y, seen.contains y = true → seen'.contains y = true)
    (hb : b' ≤ b) : AvoidOK seen' fv b' avoid := by
  intro y hy
  rcases h y hy with h | h | h
  · exact .inl (hs y h)
  · exact .inr (.inl h)
  · exact .inr (.inr (by omega))

theorem AvoidOK.cons {seen fv : VarSet} {b : Nat} {avoid : List VarId} (x : VarId)
    (h : AvoidOK seen fv b avoid) : AvoidOK (seen.insert x) fv b (x :: avoid) := by
  intro y hy
  rw [envLookupT_cons] at hy
  split at hy
  · rename_i hxy; exact .inl ((VarSet.contains_insert_elim _ _ _).mpr (.inr hxy))
  · simp only [Option.isSome_map] at hy
    rcases h y hy with h | h | h
    · exact .inl ((VarSet.contains_insert_elim _ _ _).mpr (.inl h))
    · exact .inr (.inl h)
    · exact .inr (.inr h)

theorem AvoidOK.not_mem {seen fv : VarSet} {b : Nat} {avoid : List VarId} {x : VarId}
    (h : AvoidOK seen fv b avoid) (hseen : seen.contains x = false) (hfv : fv.contains x = false)
    (hb : x.uid ≤ b) : (envLookupT avoid x).isNone = true := by
  cases hl : envLookupT avoid x with
  | none => rfl
  | some _ =>
    rcases h x (by simp [hl]) with h | h | h
    · rw [hseen] at h; cases h
    · rw [hfv] at h; cases h
    · omega

mutual
  theorem freshIn_of_wellScopedAux (seen fv : VarSet) (e : Expr) (seen' : VarSet)
      (h : wellScopedAux seen fv e = some seen') (avoid : List VarId)
      (havoid : AvoidOK seen fv (maxUidExpr e) avoid) :
      freshIn avoid e = true ∧ ∀ y, seen.contains y = true → seen'.contains y = true := by
    match e with
    | .Var _ | .Lit _ | .Builtin _ | .Error =>
      simp only [wellScopedAux, Option.some.injEq] at h; subst h
      exact ⟨by simp [freshIn], fun _ h => h⟩
    | .Lam x body =>
      simp only [wellScopedAux] at h
      split at h
      · cases h
      · rename_i hx
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hx
        obtain ⟨hf, hmono⟩ := freshIn_of_wellScopedAux (seen.insert x) fv body seen' h (x :: avoid)
          ((havoid.mono (fun _ h => h) (by simp only [maxUidExpr]; omega)).cons x)
        refine ⟨?_, fun y hy => hmono y ((VarSet.contains_insert_elim _ _ _).mpr (.inl hy))⟩
        simp only [freshIn, Bool.and_eq_true]
        exact ⟨havoid.not_mem hx.1 hx.2 (by simp only [maxUidExpr]; omega), hf⟩
    | .Fix x body =>
      simp only [wellScopedAux] at h
      split at h
      · cases h
      · rename_i hx
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hx
        obtain ⟨hf, hmono⟩ := freshIn_of_wellScopedAux (seen.insert x) fv body seen' h (x :: avoid)
          ((havoid.mono (fun _ h => h) (by simp only [maxUidExpr]; omega)).cons x)
        refine ⟨?_, fun y hy => hmono y ((VarSet.contains_insert_elim _ _ _).mpr (.inl hy))⟩
        simp only [freshIn, Bool.and_eq_true]
        exact ⟨havoid.not_mem hx.1 hx.2 (by simp only [maxUidExpr]; omega), hf⟩
    | .App f a =>
      simp only [wellScopedAux, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨seen₁, h₁, h₂⟩ := h
      obtain ⟨hf, hm₁⟩ := freshIn_of_wellScopedAux seen fv f seen₁ h₁ avoid
        (havoid.mono (fun _ h => h) (by simp only [maxUidExpr]; omega))
      obtain ⟨ha, hm₂⟩ := freshIn_of_wellScopedAux seen₁ fv a seen' h₂ avoid
        (havoid.mono hm₁ (by simp only [maxUidExpr]; omega))
      exact ⟨by simp [freshIn, hf, ha], fun y hy => hm₂ y (hm₁ y hy)⟩
    | .Force inner =>
      simp only [wellScopedAux] at h
      obtain ⟨hf, hm⟩ := freshIn_of_wellScopedAux seen fv inner seen' h avoid
        (havoid.mono (fun _ h => h) (by simp only [maxUidExpr]; omega))
      exact ⟨by simp [freshIn, hf], hm⟩
    | .Delay inner =>
      simp only [wellScopedAux] at h
      obtain ⟨hf, hm⟩ := freshIn_of_wellScopedAux seen fv inner seen' h avoid
        (havoid.mono (fun _ h => h) (by simp only [maxUidExpr]; omega))
      exact ⟨by simp [freshIn, hf], hm⟩
    | .Constr _ args =>
      simp only [wellScopedAux] at h
      obtain ⟨hf, hm⟩ := freshInList_of_wellScopedListAux seen fv args seen' h avoid
        (havoid.mono (fun _ h => h) (by simp only [maxUidExpr]; omega))
      exact ⟨by simp [freshIn, hf], hm⟩
    | .Case scrut alts =>
      simp only [wellScopedAux, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨seen₁, h₁, h₂⟩ := h
      obtain ⟨hf, hm₁⟩ := freshIn_of_wellScopedAux seen fv scrut seen₁ h₁ avoid
        (havoid.mono (fun _ h => h) (by simp only [maxUidExpr]; omega))
      obtain ⟨ha, hm₂⟩ := freshInList_of_wellScopedListAux seen₁ fv alts seen' h₂ avoid
        (havoid.mono hm₁ (by simp only [maxUidExpr]; omega))
      exact ⟨by simp [freshIn, hf, ha], fun y hy => hm₂ y (hm₁ y hy)⟩
    | .Let binds body =>
      simp only [wellScopedAux] at h
      obtain ⟨hf, hm⟩ := freshInLet_of_wellScopedLetAux seen fv binds body seen' h avoid
        (havoid.mono (fun _ h => h) (by simp only [maxUidExpr]; omega))
      exact ⟨by simp [freshIn, hf], hm⟩
  termination_by sizeOf e

  theorem freshInList_of_wellScopedListAux (seen fv : VarSet) (es : List Expr) (seen' : VarSet)
      (h : wellScopedListAux seen fv es = some seen') (avoid : List VarId)
      (havoid : AvoidOK seen fv (maxUidExprList es) avoid) :
      freshInList avoid es = true ∧ ∀ y, seen.contains y = true → seen'.contains y = true := by
    match es with
    | [] =>
      simp only [wellScopedListAux, Option.some.injEq] at h; subst h
      exact ⟨by simp [freshInList], fun _ h => h⟩
    | e :: rest =>
      simp only [wellScopedListAux, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨seen₁, h₁, h₂⟩ := h
      obtain ⟨hf, hm₁⟩ := freshIn_of_wellScopedAux seen fv e seen₁ h₁ avoid
        (havoid.mono (fun _ h => h) (by simp only [maxUidExprList]; omega))
      obtain ⟨ha, hm₂⟩ := freshInList_of_wellScopedListAux seen₁ fv rest seen' h₂ avoid
        (havoid.mono hm₁ (by simp only [maxUidExprList]; omega))
      exact ⟨by simp [freshInList, hf, ha], fun y hy => hm₂ y (hm₁ y hy)⟩
  termination_by sizeOf es

  theorem freshInLet_of_wellScopedLetAux (seen fv : VarSet) (binds : List (VarId × Expr × Bool))
      (body : Expr) (seen' : VarSet) (h : wellScopedLetAux seen fv binds body = some seen')
      (avoid : List VarId)
      (havoid : AvoidOK seen fv (max (maxUidExprBinds binds) (maxUidExpr body)) avoid) :
      freshInLet avoid binds body = true ∧ ∀ y, seen.contains y = true → seen'.contains y = true := by
    match binds with
    | [] =>
      simp only [wellScopedLetAux] at h
      obtain ⟨hf, hm⟩ := freshIn_of_wellScopedAux seen fv body seen' h avoid
        (havoid.mono (fun _ h => h) (by simp only [maxUidExprBinds]; omega))
      exact ⟨by simp [freshInLet, hf], hm⟩
    | (x, rhs, er) :: rest =>
      simp only [wellScopedLetAux, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨seen₁, h₁, h₂⟩ := h
      obtain ⟨hf, hm₁⟩ := freshIn_of_wellScopedAux seen fv rhs seen₁ h₁ avoid
        (havoid.mono (fun _ h => h) (by simp only [maxUidExprBinds]; omega))
      split at h₂
      · cases h₂
      · rename_i hx
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hx
        obtain ⟨hl, hm₂⟩ := freshInLet_of_wellScopedLetAux (seen₁.insert x) fv rest body seen' h₂
          (x :: avoid) ((havoid.mono (b' := max (maxUidExprBinds rest) (maxUidExpr body)) hm₁
            (by simp only [maxUidExprBinds]; omega)).cons x)
        refine ⟨?_, fun y hy => hm₂ y ((VarSet.contains_insert_elim _ _ _).mpr (.inl (hm₁ y hy)))⟩
        simp only [freshInLet, Bool.and_eq_true]
        exact ⟨⟨hf, (havoid.mono hm₁ (Nat.le_refl _)).not_mem hx.1 hx.2
          (by simp only [maxUidExprBinds]; omega)⟩, hl⟩
  termination_by sizeOf binds + sizeOf body
end

theorem freshIn_of_wellScoped {e : Expr} (h : wellScoped e = true) {avoid : List VarId}
    (havoid : ∀ y, (envLookupT avoid y).isSome = true →
      (freeVars e).contains y = true ∨ maxUidExpr e < y.uid) : freshIn avoid e = true := by
  simp only [wellScoped] at h
  cases hw : wellScopedAux VarSet.empty (freeVars e) e with
  | none => rw [hw] at h; cases h
  | some seen' =>
    refine (freshIn_of_wellScopedAux _ _ e seen' hw avoid ?_).1
    intro y hy
    rcases havoid y hy with h | h
    · exact .inr (.inl h)
    · exact .inr (.inr h)

theorem freeVars_uid_lt {e : Expr} {y : VarId} (h : (freeVars e).contains y = true) :
    y.uid ≤ maxUidExpr e := by
  apply Classical.byContradiction
  intro hlt
  rw [maxUidExpr_fresh e y (by omega)] at h
  cases h

/-! ## The bridge -/

/-- Refinement under no facts in canonical environments gives lowerings that
    refine in every environment. -/
theorem lower_of_factRel {P : List VarId → CekEnv → Expr → CekValue → Prop} {E E' : Expr}
    (hws : wellScoped E = true) (h : FactRel P [] E E') :
    ∀ env t, lowerTotalExpr env E = some t →
      ∃ t', lowerTotalExpr env E' = some t' ∧ FactRefines env.length (fun _ => True) t t' := by
  intro env t hlow
  let keep : VarId → Bool := fun y => (freeVars E).contains y
  let D := maxUidExpr E + maxUidExpr (expandFix E') + 1
  have hkeep : ∀ x y, (x == y) = true → keep x = keep y := fun x y hxy =>
    varSet_contains_congr _ hxy
  have hD : ∀ y, keep y = true → y.uid < D := by
    intro y hy
    have := freeVars_uid_lt hy
    simp only [D]; omega
  let env' := canonEnv keep D [] env 0
  have hlen : env'.length = env.length := canonEnv_length keep D [] env 0
  have hagree : ∀ v, keep v = true → envLookupT env' v = envLookupT env v := fun v hv =>
    canonEnv_lookup keep D hkeep hD [] env 0 v hv rfl
  have hlowE : lowerTotalExpr env' E = some t := by
    rw [← hlow]
    exact lowerTotalExpr_agree fun v hv => hagree v hv
  have hfresh : freshIn env' E = true := by
    apply freshIn_of_wellScoped hws
    intro y hy
    rcases canonEnv_found keep D hkeep [] env 0 y hy with ⟨hk, _⟩ | hu
    · exact .inl hk
    · right; simp only [D] at hu; omega
  obtain ⟨t', ht', hr⟩ := h env' t (canonEnv_distinct keep D hkeep hD [] env 0) hfresh
    (by intro _ hm; cases hm) (by intro x entry i hf; simp at hf) hlowE
  refine ⟨t', ?_, ?_⟩
  · rw [← ht']
    simp only [lowerTotalExpr] at ht' ⊢
    apply lowerTotal_agree
    intro v hv
    have hb := lowerTotal_bound env' _ t' ht' v hv
    rcases canonEnv_found keep D hkeep [] env 0 v hb with ⟨hk, _⟩ | hu
    · exact (hagree v hk).symm
    · have := freeVars_uid_lt hv
      simp only [D] at hu; omega
  · rw [← hlen]
    exact hr.mono fun ρ _ => FactsHold.nil P env' ρ

theorem mirCtxRefines_of_factRel {P : List VarId → CekEnv → Expr → CekValue → Prop} {E E' : Expr}
    (hws : wellScoped E = true) (h : FactRel P [] E E') : MIRCtxRefines E E' := by
  intro env
  have hmain := lower_of_factRel hws h
  refine ⟨fun hs => ?_, ?_⟩
  · cases hl : lowerTotalExpr env E with
    | none => rw [hl] at hs; cases hs
    | some t =>
      obtain ⟨t', ht', _⟩ := hmain env t hl
      rw [ht']; rfl
  · cases hl : lowerTotalExpr env E with
    | none => trivial
    | some t =>
      obtain ⟨t', ht', hr⟩ := hmain env t hl
      rw [ht']
      apply ctxRefines_of_factRefines (MIR.lowerTotalExpr_closedAt hl) _ hr
      intro k hk
      have htake : lowerTotalExpr (env.take k) E = some t := by
        simp only [lowerTotalExpr] at hl ⊢
        exact lowerTotal_take env _ t k hl hk
      obtain ⟨t'', ht'', _⟩ := hmain (env.take k) t htake
      have hext : lowerTotalExpr (env.take k ++ env.drop k) E' = some t'' := by
        simp only [lowerTotalExpr] at ht'' ⊢
        exact lowerTotal_append_of_some ht''
      rw [List.take_append_drop, ht'] at hext
      cases hext
      have hc := MIR.lowerTotalExpr_closedAt ht''
      exact closedAt_mono hc (by simp; omega)

end Moist.Verified.ShapeFacts
