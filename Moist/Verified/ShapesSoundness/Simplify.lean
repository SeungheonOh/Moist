import Moist.Verified.ShapesSoundness.Integers

/-! # The fact-driven simplifier

`simplifyWalk` refines its input under the facts it records (`simplifyWalk_factRel`).
The checked shape simplifications `shapeDCE` and `simplifyChoices`, and the
advanced simplification pipeline, refine their inputs contextually.
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines

/-! ## Data round trips -/

theorem checkedRoundTrip_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {x y : Expr}
    (h : checkedRoundTrip Γ x = some y) : FactRel G PF Γ x y := by
  unfold checkedRoundTrip at h
  split at h
  · rename_i outer checked
    split at h
    · rename_i inner original hres
      split at h
      · simp at h; subst h; exact roundTrip_factRel hres rfl rfl roundTrip_IData
      · simp at h; subst h; exact roundTrip_factRel hres rfl rfl roundTrip_UnIData
      · simp at h; subst h; exact roundTrip_factRel hres rfl rfl roundTrip_BData
      · simp at h; subst h; exact roundTrip_factRel hres rfl rfl roundTrip_UnBData
      · simp at h; subst h; exact roundTrip_factRel hres rfl rfl roundTrip_ListData
      · simp at h; subst h; exact roundTrip_factRel hres rfl rfl roundTrip_MapData
      · simp at h
    · cases h
  · cases h

theorem checkedRoundTrip_fresh {Γ : List (VarId × Expr)} {x y : Expr} {env : List VarId}
    (h : checkedRoundTrip Γ x = some y) : freshIn env y = true := by
  unfold checkedRoundTrip at h
  split at h
  · split at h
    · split at h <;> simp at h <;> subst h <;> simp [freshIn]
    · cases h
  · cases h

/-! ## Rewrites after the children -/

theorem stage1_factRel {G : VarId → Prop} (useShapes : Bool) (Γ : List (VarId × Expr)) (x : Expr) :
    FactRel G PF Γ x (if useShapes then (checkedRoundTrip Γ x).getD x else x) := by
  split
  · cases hc : checkedRoundTrip Γ x with
    | none => exact FactRel.refl _ _ _ _
    | some y => exact checkedRoundTrip_factRel hc
  · exact FactRel.refl _ _ _ _

theorem stage1_fresh (useShapes : Bool) (Γ : List (VarId × Expr)) {x : Expr} {env : List VarId}
    (hx : freshIn env x = true) :
    freshIn env (if useShapes then (checkedRoundTrip Γ x).getD x else x) = true := by
  split
  · cases hc : checkedRoundTrip Γ x with
    | none => exact hx
    | some y => exact checkedRoundTrip_fresh hc
  · exact hx

theorem stage2_factRel {G : VarId → Prop} (useShapes : Bool) (base : Nat) (Γ : List (VarId × Expr))
    (x : Expr) : FactRel G PF Γ x (if useShapes then (integerIdentity base Γ x).getD x else x) := by
  split
  · cases hc : integerIdentity base Γ x with
    | none => exact FactRel.refl _ _ _ _
    | some y => exact integerIdentity_factRel hc
  · exact FactRel.refl _ _ _ _

theorem stage2_fresh (useShapes : Bool) (base : Nat) (Γ : List (VarId × Expr)) {x : Expr}
    {env : List VarId} (hG : ∀ y ∈ env, GenSafe base y) (hx : freshIn env x = true) :
    freshIn env (if useShapes then (integerIdentity base Γ x).getD x else x) = true := by
  split
  · cases hc : integerIdentity base Γ x with
    | none => exact hx
    | some y => exact integerIdentity_fresh hG hx hc
  · exact hx

theorem shapeRewrite_factRel (useShapes : Bool) (base : Nat) (Γ : List (VarId × Expr)) (x : Expr) :
    FactRel (GenSafe base) PF Γ x (shapeRewrite useShapes base Γ x) := by
  unfold shapeRewrite
  simp only []
  generalize hr₁ : (if useShapes = true then (checkedRoundTrip Γ x).getD x else x) = r₁
  generalize hr₂ : (if useShapes = true then (integerIdentity base Γ r₁).getD r₁ else r₁) = r₂
  have s₁ : FactRel (GenSafe base) PF Γ x r₁ := hr₁ ▸ stage1_factRel useShapes Γ x
  have s₂ : FactRel (GenSafe base) PF Γ r₁ r₂ := hr₂ ▸ stage2_factRel useShapes base Γ r₁
  have f₁ : ∀ env, (∀ y ∈ env, GenSafe base y) → freshIn env x = true → freshIn env r₁ = true :=
    fun env _ hx => hr₁ ▸ stage1_fresh useShapes Γ hx
  have f₂ : ∀ env, (∀ y ∈ env, GenSafe base y) → freshIn env r₁ = true → freshIn env r₂ = true :=
    fun env hG hx => hr₂ ▸ stage2_fresh useShapes base Γ hG hx
  refine (s₁.trans s₂ f₁).trans ?_ (fun env hG hx => f₂ env hG (f₁ env hG hx))
  clear s₁ s₂ f₁ f₂ hr₂
  split
  · split
    · rename_i cond wt wf hcond
      simp only [Bool.and_eq_true] at hcond
      exact ite_case_factRel hcond.1.1 hcond.1.2 hcond.2
    · exact FactRel.refl _ _ _ _
  · split
    · rename_i hknown
      split
      · rename_i bodies hb
        exact force_case_factRel hknown hb
      · exact FactRel.refl _ _ _ _
    · exact FactRel.refl _ _ _ _
  · split
    · rename_i scrut first second hcond
      simp only [Bool.and_eq_true] at hcond
      split
      · rename_i htotal
        exact case_alpha_total_factRel hcond.2 htotal hcond.1.2
      · exact case_alpha_checked_factRel _ hcond.2 hcond.1.2
          (by simp only [maxUidExpr, maxUidExprList]; omega)
    · exact FactRel.refl _ _ _ _
  · exact FactRel.refl _ _ _ _

theorem freshInList_map_delay {env : List VarId} :
    ∀ (bodies : List Expr), freshInList env (bodies.map .Delay) = freshInList env bodies
  | [] => rfl
  | b :: bs => by simp only [List.map_cons, freshInList, freshIn, freshInList_map_delay bs]

theorem shapeRewrite_fresh (useShapes : Bool) (base : Nat) (Γ : List (VarId × Expr)) {x : Expr}
    {env : List VarId} (hG : ∀ y ∈ env, GenSafe base y) (hx : freshIn env x = true) :
    freshIn env (shapeRewrite useShapes base Γ x) = true := by
  unfold shapeRewrite
  simp only []
  generalize hr₁ : (if useShapes = true then (checkedRoundTrip Γ x).getD x else x) = r₁
  generalize hr₂ : (if useShapes = true then (integerIdentity base Γ r₁).getD r₁ else r₁) = r₂
  have f₁ : freshIn env r₁ = true := hr₁ ▸ stage1_fresh useShapes Γ hx
  have f₂ : freshIn env r₂ = true := hr₂ ▸ stage2_fresh useShapes base Γ hG f₁
  clear hr₂
  split
  · split
    · simp only [freshIn, freshInList, Bool.and_eq_true] at f₂ ⊢
      exact ⟨f₂.1.1.2, f₂.2, f₂.1.2, trivial⟩
    · exact f₂
  · split
    · split
      · rename_i bodies hb
        have := mapM_delayBody hb
        subst this
        simp only [freshIn, Bool.and_eq_true, freshInList_map_delay] at f₂ ⊢
        exact f₂
      · exact f₂
    · exact f₂
  · split
    · split
      · simp only [freshIn, freshInList, Bool.and_eq_true] at f₂; exact f₂.2.1
      · rename_i scrut first second _ _
        simp only [freshIn, freshInList, Bool.and_eq_true] at f₂
        rw [freshIn_let_single]
        simp only [Bool.and_eq_true]
        refine ⟨⟨f₂.1, ?_⟩, ?_⟩
        · rw [lookup_none_of_not_G hG (not_genSafe (Nat.le_max_left _ _) rfl)]; rfl
        · exact freshIn_cons_of_big f₂.2.1 (by simp only [maxUidExpr, maxUidExprList]; omega)
    · exact f₂
  · exact f₂

/-! ## Freshness of the walk -/

theorem avoids_drop_head (x : VarId) (env : List VarId) (bound : Nat) : Avoids (x :: env) env bound := by
  intro y hy
  left
  rw [envLookupT_cons]
  split
  · rfl
  · simp only [Option.isSome_map]; exact hy

theorem maxUidExprBinds_mem : ∀ {b : VarId × Expr × Bool} {bs : List (VarId × Expr × Bool)}, b ∈ bs →
    b.1.uid ≤ maxUidExprBinds bs ∧ maxUidExpr b.2.1 ≤ maxUidExprBinds bs
  | _, (x, r, er) :: rest, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp only [maxUidExprBinds]; omega
    · have := maxUidExprBinds_mem h
      simp only [maxUidExprBinds]; omega

theorem bindings_fresh (useShapes : Bool) (base : Nat) (body : Expr)
    (hb : ∀ (Γ : List (VarId × Expr)) (env : List VarId), (∀ y ∈ env, GenSafe base y) →
      freshIn env body = true → freshIn env (simplifyWalk useShapes base Γ body) = true) :
    ∀ (bindings : List (VarId × Expr × Bool)),
      (∀ b ∈ bindings, b.1.uid < base) →
      (∀ b ∈ bindings, ∀ (Γ : List (VarId × Expr)) (env : List VarId), (∀ y ∈ env, GenSafe base y) →
        freshIn env b.2.1 = true → freshIn env (simplifyWalk useShapes base Γ b.2.1) = true) →
      ∀ (Γ : List (VarId × Expr)) (env : List VarId), (∀ y ∈ env, GenSafe base y) →
        freshIn env (.Let bindings body) = true →
        freshIn env (.Let (retainBindings (simplifyWalk useShapes base (simplifyBindings useShapes base Γ bindings).2 body)
          (simplifyBindings useShapes base Γ bindings).1)
          (simplifyWalk useShapes base (simplifyBindings useShapes base Γ bindings).2 body)) = true
  | [], _, _, Γ, env, hG, hf => by
    rw [simplifyBindings.eq_1]
    simp only [retainBindings]
    rw [freshIn_let_nil] at hf ⊢
    exact hb Γ env hG hf
  | (x, r, er) :: rest, hx, hr, Γ, env, hG, hf => by
    rw [simplifyBindings.eq_2]
    simp only []
    rw [freshIn_let_cons, freshIn_let_single] at hf
    simp only [Bool.and_eq_true] at hf
    obtain ⟨⟨hfr, hxe⟩, hfrest⟩ := hf
    have ih := bindings_fresh useShapes base body hb rest (fun b hb' => hx b (.tail _ hb'))
      (fun b hb' => hr b (.tail _ hb')) ((x, simplifyWalk useShapes base Γ r) :: Γ) (x :: env)
      (allG_cons (.inl (hx _ (.head _))) hG) hfrest
    rw [retainBindings.eq_2]
    split
    · exact freshIn_avoids _ ih (avoids_drop_head x env _)
    · rw [freshIn_let_cons, freshIn_let_single]
      simp only [Bool.and_eq_true]
      exact ⟨⟨hr _ (.head _) Γ env hG hfr, hxe⟩, ih⟩

theorem simplifyWalk_fresh (useShapes : Bool) (base : Nat) :
    ∀ (e : Expr) (Γ : List (VarId × Expr)) (env : List VarId), (∀ y ∈ env, GenSafe base y) →
      maxUidExpr e < base → freshIn env e = true →
      freshIn env (simplifyWalk useShapes base Γ e) = true
  | .Let bindings body, Γ, env, hG, hmax, hf => by
    rw [simplifyWalk.eq_2]
    simp only [maxUidExpr] at hmax
    have hbinds := bindings_fresh useShapes base body
      (fun Γ' env' hG' hf' => simplifyWalk_fresh useShapes base body Γ' env' hG' (by omega) hf')
      bindings (fun b hb => by have := (maxUidExprBinds_mem hb).1; omega)
      (fun b hb Γ' env' hG' hf' => simplifyWalk_fresh useShapes base b.2.1 Γ' env' hG'
        (by have := (maxUidExprBinds_mem hb).2; omega) hf') Γ env hG hf
    split
    · rename_i hempty
      simp only [List.isEmpty_iff] at hempty
      rw [hempty, freshIn_let_nil] at hbinds
      exact hbinds
    · exact hbinds
  | .Lam x b, Γ, env, hG, hmax, hf => by
    rw [simplifyWalk.eq_3]
    simp only [maxUidExpr] at hmax
    simp only [freshIn, Bool.and_eq_true] at hf ⊢
    exact ⟨hf.1, simplifyWalk_fresh useShapes base b Γ (x :: env) (allG_cons (.inl (by omega)) hG)
      (by omega) hf.2⟩
  | .Fix x b, Γ, env, hG, hmax, hf => by
    rw [simplifyWalk.eq_4]
    simp only [maxUidExpr] at hmax
    simp only [freshIn, Bool.and_eq_true] at hf ⊢
    exact ⟨hf.1, simplifyWalk_fresh useShapes base b Γ (x :: env) (allG_cons (.inl (by omega)) hG)
      (by omega) hf.2⟩
  | .App f a, Γ, env, hG, hmax, hf => by
    rw [simplifyWalk.eq_5]
    simp only [maxUidExpr] at hmax
    apply shapeRewrite_fresh useShapes base Γ hG
    simp only [freshIn, Bool.and_eq_true] at hf ⊢
    exact ⟨simplifyWalk_fresh useShapes base f Γ env hG (by omega) hf.1,
      simplifyWalk_fresh useShapes base a Γ env hG (by omega) hf.2⟩
  | .Force b, Γ, env, hG, hmax, hf => by
    rw [simplifyWalk.eq_6]
    simp only [maxUidExpr] at hmax
    apply shapeRewrite_fresh useShapes base Γ hG
    simp only [freshIn] at hf ⊢
    exact simplifyWalk_fresh useShapes base b Γ env hG (by omega) hf
  | .Delay b, Γ, env, hG, hmax, hf => by
    rw [simplifyWalk.eq_7]
    simp only [maxUidExpr] at hmax
    apply shapeRewrite_fresh useShapes base Γ hG
    simp only [freshIn] at hf ⊢
    exact simplifyWalk_fresh useShapes base b Γ env hG (by omega) hf
  | .Constr tag fields, Γ, env, hG, hmax, hf => by
    rw [simplifyWalk.eq_8]
    simp only [maxUidExpr] at hmax
    apply shapeRewrite_fresh useShapes base Γ hG
    simp only [freshIn] at hf ⊢
    rw [freshInList_iff] at hf ⊢
    intro y hy
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    have := maxUidExpr_le_maxUidExprList_of_mem hc
    exact simplifyWalk_fresh useShapes base c Γ env hG (by omega) (hf c hc)
  | .Case scrut alts, Γ, env, hG, hmax, hf => by
    simp only [maxUidExpr] at hmax
    by_cases hv : ∃ b f s, scrut = .Var b ∧ alts = [f, s]
    · obtain ⟨b, f, s, rfl, rfl⟩ := hv
      rw [simplifyWalk.eq_1]
      simp only [freshIn, freshInList, Bool.and_eq_true] at hf
      obtain ⟨_, hff, hfs, _⟩ := hf
      simp only [maxUidExprList] at hmax
      have ihf := fun Γ' => simplifyWalk_fresh useShapes base f Γ' env hG (by omega) hff
      have ihs := fun Γ' => simplifyWalk_fresh useShapes base s Γ' env hG (by omega) hfs
      split
      · split
        · split
          · exact ihs Γ
          · exact ihf Γ
        · simp only []
          split
          · exact ihf _
          · simp [freshIn, freshInList, ihf, ihs]
      · simp [freshIn, freshInList, ihf, ihs]
    · rw [simplifyWalk.eq_9 _ _ _ _ _ (fun b f s h1 h2 => hv ⟨b, f, s, h1, h2⟩)]
      apply shapeRewrite_fresh useShapes base Γ hG
      simp only [freshIn, Bool.and_eq_true] at hf ⊢
      refine ⟨simplifyWalk_fresh useShapes base scrut Γ env hG (by omega) hf.1, ?_⟩
      have hf2 := hf.2
      rw [freshInList_iff] at hf2 ⊢
      intro y hy
      simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hy
      obtain ⟨c, hc, rfl⟩ := hy
      have := maxUidExpr_le_maxUidExprList_of_mem hc
      exact simplifyWalk_fresh useShapes base c Γ env hG (by omega) (hf2 c hc)
  | .Var _, Γ, env, hG, _, hf => by
    rw [simplifyWalk.eq_10]; exact shapeRewrite_fresh useShapes base Γ hG hf
  | .Lit _, Γ, env, hG, _, hf => by
    rw [simplifyWalk.eq_11]; exact shapeRewrite_fresh useShapes base Γ hG hf
  | .Builtin _, Γ, env, hG, _, hf => by
    rw [simplifyWalk.eq_12]; exact shapeRewrite_fresh useShapes base Γ hG hf
  | .Error, Γ, env, hG, _, hf => by
    rw [simplifyWalk.eq_13]; exact shapeRewrite_fresh useShapes base Γ hG hf
termination_by e => exprSize e
decreasing_by
  all_goals first
    | (subst_vars; simp only [exprSize, exprSizeList]; omega)
    | (simp only [exprSize]; have := exprSize_pos body; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)
    | (have := exprSizeBinds_mem_lt (by assumption); simp only [exprSize]; have := exprSize_pos body; omega)

/-! ## Refinement by the walk -/

/-- A binding that returns on every path and that the body ignores. -/
theorem dead_let_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {x : VarId} {r B : Expr} {er : Bool}
    (htotal : totalWithFacts 64 Γ r = true) (hunused : (freeVars B).contains x = false) :
    FactRel G PF Γ (.Let [(x, r, er)] B) B := by
  intro env t hG hd hfresh hk hsc hlow
  rw [freshIn_let_single] at hfresh
  simp only [Bool.and_eq_true] at hfresh
  obtain ⟨⟨hfr, _⟩, _⟩ := hfresh
  obtain ⟨tr, tb, htr, htb, rfl⟩ := lowerTotalExpr_let_single_some hlow
  rw [MIR.lowerTotalExpr_prepend_unused env x B hunused] at htb
  cases hB : lowerTotalExpr env B with
  | none => rw [hB] at htb; cases htb
  | some tB =>
    rw [hB] at htb; cases htb
    refine ⟨tB, rfl, ?_⟩
    exact factRefines_dead_let 0 (MIR.lowerTotalExpr_closedAt hB)
      (fun ρ hF henv _ => totalWithFacts_sound PF_hP 64 Γ r htotal hF hd hfr
        (wellSized_of_wellFormed henv) htr)

theorem bindings_factRel (useShapes : Bool) (base : Nat) (body : Expr)
    (hb : ∀ Γ : List (VarId × Expr), FactRel (GenSafe base) PF Γ body (simplifyWalk useShapes base Γ body))
    (hbf : ∀ (Γ : List (VarId × Expr)) (env : List VarId), (∀ y ∈ env, GenSafe base y) →
      freshIn env body = true → freshIn env (simplifyWalk useShapes base Γ body) = true) :
    ∀ (bindings : List (VarId × Expr × Bool)),
      (∀ b ∈ bindings, b.1.uid < base) →
      (∀ b ∈ bindings, ∀ Γ : List (VarId × Expr),
        FactRel (GenSafe base) PF Γ b.2.1 (simplifyWalk useShapes base Γ b.2.1)) →
      (∀ b ∈ bindings, ∀ (Γ : List (VarId × Expr)) (env : List VarId), (∀ y ∈ env, GenSafe base y) →
        freshIn env b.2.1 = true → freshIn env (simplifyWalk useShapes base Γ b.2.1) = true) →
      ∀ Γ : List (VarId × Expr),
        FactRel (GenSafe base) PF Γ (.Let bindings body)
          (.Let (retainBindings (simplifyWalk useShapes base (simplifyBindings useShapes base Γ bindings).2 body)
            (simplifyBindings useShapes base Γ bindings).1)
            (simplifyWalk useShapes base (simplifyBindings useShapes base Γ bindings).2 body))
  | [], _, _, _, Γ => by
    rw [simplifyBindings.eq_1]
    simp only [retainBindings]
    exact ((hb Γ).congr_left (fun env => lowerTotalExpr_let_nil env body)
      (fun avoid => freshIn_let_nil avoid body)).congr_right
      (fun env => lowerTotalExpr_let_nil env _)
  | (x, r, er) :: rest, hx, hr, hrf, Γ => by
    rw [simplifyBindings.eq_2]
    simp only []
    have ih := bindings_factRel useShapes base body hb hbf rest (fun b hb' => hx b (.tail _ hb'))
      (fun b hb' => hr b (.tail _ hb')) (fun b hb' => hrf b (.tail _ hb'))
      ((x, simplifyWalk useShapes base Γ r) :: Γ)
    have hkeep := (FactRel.let_single (er := er) (simplifyWalk useShapes base Γ r) (.inl (hx _ (.head _)))
      (.inr rfl) (hr _ (.head _) Γ) ih
      (fun env ρ v hG _ hfr hp => ⟨hp, hrf _ (.head _) Γ env hG hfr⟩)).congr_left
      (fun env => lowerTotalExpr_let_cons env _ _ _) (fun avoid => freshIn_let_cons avoid _ _ _)
    rw [retainBindings.eq_2]
    split
    · rename_i hdrop
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hdrop
      obtain ⟨htotal, hunused⟩ := hdrop
      refine hkeep.trans (dead_let_factRel htotal.2 hunused) ?_
      intro env hG hf
      rw [freshIn_let_cons, freshIn_let_single] at hf
      simp only [Bool.and_eq_true] at hf
      obtain ⟨⟨hfr, hxe⟩, hfrest⟩ := hf
      rw [freshIn_let_single]
      simp only [Bool.and_eq_true]
      exact ⟨⟨hrf _ (.head _) Γ env hG hfr, hxe⟩,
        bindings_fresh useShapes base body hbf rest (fun b hb' => hx b (.tail _ hb'))
          (fun b hb' => hrf b (.tail _ hb')) _ (x :: env) (allG_cons (.inl (hx _ (.head _))) hG) hfrest⟩
    · exact hkeep.congr_right (fun env => lowerTotalExpr_let_cons env _ _ _)

theorem simplifyWalk_factRel (useShapes : Bool) (base : Nat) :
    ∀ (e : Expr) (Γ : List (VarId × Expr)), maxUidExpr e < base →
      FactRel (GenSafe base) PF Γ e (simplifyWalk useShapes base Γ e)
  | .Let bindings body, Γ, hmax => by
    rw [simplifyWalk.eq_2]
    simp only [maxUidExpr] at hmax
    have hbinds := bindings_factRel useShapes base body
      (fun Γ' => simplifyWalk_factRel useShapes base body Γ' (by omega))
      (fun Γ' env' hG' hf' => simplifyWalk_fresh useShapes base body Γ' env' hG' (by omega) hf')
      bindings (fun b hb => by have := (maxUidExprBinds_mem hb).1; omega)
      (fun b hb Γ' => simplifyWalk_factRel useShapes base b.2.1 Γ'
        (by have := (maxUidExprBinds_mem hb).2; omega))
      (fun b hb Γ' env' hG' hf' => simplifyWalk_fresh useShapes base b.2.1 Γ' env' hG'
        (by have := (maxUidExprBinds_mem hb).2; omega) hf') Γ
    split
    · rename_i hempty
      simp only [List.isEmpty_iff] at hempty
      rw [hempty] at hbinds
      exact hbinds.congr_right (fun env => (lowerTotalExpr_let_nil env _).symm)
    · exact hbinds
  | .Lam x b, Γ, hmax => by
    rw [simplifyWalk.eq_3]
    simp only [maxUidExpr] at hmax
    exact (simplifyWalk_factRel useShapes base b Γ (by omega)).lam (.inl (by omega))
  | .Fix f b, Γ, hmax => by
    rw [simplifyWalk.eq_4]
    simp only [maxUidExpr] at hmax
    cases b with
    | Lam x inner =>
      rw [simplifyWalk.eq_3]
      simp only [maxUidExpr] at hmax
      exact (simplifyWalk_factRel useShapes base inner Γ (by omega)).fix_lam (.inl (by omega))
        (.inl (by omega)) (fun y hy => .inr (by rw [hy]; simp))
    | _ =>
      intro env t _ _ _ _ _ hlow
      rw [MIR.lowerTotalExpr_fix_nonlam_none env f _ (by intros; simp)] at hlow
      cases hlow
  | .App f a, Γ, hmax => by
    rw [simplifyWalk.eq_5]
    simp only [maxUidExpr] at hmax
    refine ((simplifyWalk_factRel useShapes base f Γ (by omega)).app
      (simplifyWalk_factRel useShapes base a Γ (by omega))).trans (shapeRewrite_factRel _ _ _ _) ?_
    intro env hG hf
    simp only [freshIn, Bool.and_eq_true] at hf ⊢
    exact ⟨simplifyWalk_fresh useShapes base f Γ env hG (by omega) hf.1,
      simplifyWalk_fresh useShapes base a Γ env hG (by omega) hf.2⟩
  | .Force b, Γ, hmax => by
    rw [simplifyWalk.eq_6]
    simp only [maxUidExpr] at hmax
    refine (simplifyWalk_factRel useShapes base b Γ (by omega)).force.trans (shapeRewrite_factRel _ _ _ _) ?_
    intro env hG hf
    simp only [freshIn] at hf ⊢
    exact simplifyWalk_fresh useShapes base b Γ env hG (by omega) hf
  | .Delay b, Γ, hmax => by
    rw [simplifyWalk.eq_7]
    simp only [maxUidExpr] at hmax
    refine (simplifyWalk_factRel useShapes base b Γ (by omega)).delay.trans (shapeRewrite_factRel _ _ _ _) ?_
    intro env hG hf
    simp only [freshIn] at hf ⊢
    exact simplifyWalk_fresh useShapes base b Γ env hG (by omega) hf
  | .Constr tag fields, Γ, hmax => by
    rw [simplifyWalk.eq_8]
    simp only [maxUidExpr] at hmax
    refine (FactRel.constr (listRel_attach_map fields _ fun c hc => simplifyWalk_factRel useShapes base c Γ
      (by have := maxUidExpr_le_maxUidExprList_of_mem hc; omega))).trans (shapeRewrite_factRel _ _ _ _) ?_
    intro env hG hf
    simp only [freshIn] at hf ⊢
    rw [freshInList_iff] at hf ⊢
    intro y hy
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    have := maxUidExpr_le_maxUidExprList_of_mem hc
    exact simplifyWalk_fresh useShapes base c Γ env hG (by omega) (hf c hc)
  | .Case scrut alts, Γ, hmax => by
    simp only [maxUidExpr] at hmax
    by_cases hv : ∃ b f s, scrut = .Var b ∧ alts = [f, s]
    · obtain ⟨b, f, s, rfl, rfl⟩ := hv
      rw [simplifyWalk.eq_1]
      simp only [maxUidExprList] at hmax
      have ihf := fun Γ' => simplifyWalk_factRel useShapes base f Γ' (by omega)
      have ihs := fun Γ' => simplifyWalk_factRel useShapes base s Γ' (by omega)
      have freshf : ∀ env, (∀ y ∈ env, GenSafe base y) → freshIn env (.Case (.Var b) [f, s]) = true →
          freshIn env f = true := by
        intro env _ hf
        simp only [freshIn, freshInList, Bool.and_eq_true] at hf
        exact hf.2.1
      have freshs : ∀ env, (∀ y ∈ env, GenSafe base y) → freshIn env (.Case (.Var b) [f, s]) = true →
          freshIn env s = true := by
        intro env _ hf
        simp only [freshIn, freshInList, Bool.and_eq_true] at hf
        exact hf.2.2.1
      split
      · rename_i hcond
        simp only [Bool.and_eq_true] at hcond
        split
        · rename_i value hres
          have hl := case_var_literal_factRel (G := GenSafe base) (first := f) (second := s) hres
          cases value
          · simp only [Bool.false_eq_true, ↓reduceIte] at hl ⊢
            exact hl.trans (ihf Γ) freshf
          · simp only [↓reduceIte] at hl ⊢
            exact hl.trans (ihs Γ) freshs
        · simp only []
          split
          · rename_i halpha
            exact case_var_merge_factRel hcond.2 (ihf _) (ihs _) halpha
          · exact case_var_factRel hcond.2 (ihf _) (ihs _)
      · exact FactRel.case (FactRel.refl _ _ _ _) ⟨ihf Γ, ihs Γ, trivial⟩
    · rw [simplifyWalk.eq_9 _ _ _ _ _ (fun b f s h1 h2 => hv ⟨b, f, s, h1, h2⟩)]
      have ihalts : ∀ c ∈ alts, FactRel (GenSafe base) PF Γ c (simplifyWalk useShapes base Γ c) :=
        fun c hc => simplifyWalk_factRel useShapes base c Γ
          (by have := maxUidExpr_le_maxUidExprList_of_mem hc; omega)
      refine (FactRel.case (simplifyWalk_factRel useShapes base scrut Γ (by omega))
        (listRel_attach_map alts _ ihalts)).trans (shapeRewrite_factRel _ _ _ _) ?_
      intro env hG hf
      simp only [freshIn, Bool.and_eq_true] at hf ⊢
      refine ⟨simplifyWalk_fresh useShapes base scrut Γ env hG (by omega) hf.1, ?_⟩
      have hf2 := hf.2
      rw [freshInList_iff] at hf2 ⊢
      intro y hy
      simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hy
      obtain ⟨c, hc, rfl⟩ := hy
      have := maxUidExpr_le_maxUidExprList_of_mem hc
      exact simplifyWalk_fresh useShapes base c Γ env hG (by omega) (hf2 c hc)
  | .Var _, Γ, _ => by rw [simplifyWalk.eq_10]; exact shapeRewrite_factRel _ _ _ _
  | .Lit _, Γ, _ => by rw [simplifyWalk.eq_11]; exact shapeRewrite_factRel _ _ _ _
  | .Builtin _, Γ, _ => by rw [simplifyWalk.eq_12]; exact shapeRewrite_factRel _ _ _ _
  | .Error, Γ, _ => by rw [simplifyWalk.eq_13]; exact shapeRewrite_factRel _ _ _ _
termination_by e => exprSize e
decreasing_by
  all_goals first
    | (subst_vars; simp only [exprSize, exprSizeList]; omega)
    | (simp only [exprSize]; have := exprSize_pos body; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)
    | (have := exprSizeBinds_mem_lt (by assumption); simp only [exprSize]; have := exprSize_pos body; omega)

end Moist.Verified.ShapeFacts

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced Moist.Verified.ShapeFacts

theorem simplifyWithFacts_refines (useShapes : Bool) (e : Expr) :
    MIRCtxRefines e (simplifyWithFacts useShapes e) := by
  unfold simplifyWithFacts
  simp only
  split
  · rename_i hws
    refine mirCtxRefines_trans (Hygiene.uniqueOptimizationBinders_refines e)
      (mirCtxRefines_trans ?_ (Hygiene.uniqueOptimizationBinders_refines _))
    exact mirCtxRefines_of_factRel hws
      (fun y hy => .inl (by have := freeVars_uid_lt hy; omega))
      (fun y hy => .inr (by rw [hy]; simp))
      (simplifyWalk_factRel _ _ _ [] (by omega))
  · exact Hygiene.uniqueOptimizationBinders_refines e

/-- Shape-driven dead code elimination refines its input. -/
theorem shapeDCE_refines (e : Expr) : MIRCtxRefines e (shapeDCE e) :=
  simplifyWithFacts_refines true e

/-- Choice simplification refines its input. -/
theorem simplifyChoices_refines (e : Expr) : MIRCtxRefines e (simplifyChoices e) :=
  simplifyWithFacts_refines false e

end Moist.Verified.MIR
