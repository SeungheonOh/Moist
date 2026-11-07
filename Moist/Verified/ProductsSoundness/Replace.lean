import Moist.Verified.ProductsSoundness.Values

/-! # Replacing pair projections

Inside the scope of fresh binders recorded as holding `fstPair x` and
`sndPair x`, every projection of `x` can be replaced by the corresponding
binder (`replaceProjections_factRel`). When every occurrence of `x` is a
projection, `x` is no longer free afterwards (`replaceProjections_not_free`).
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines

/-- A unary builtin application on a variable refines the binder recorded as
    holding the same application. -/
theorem unaryProjection_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {b l h : VarId}
    {g : Expr} {builtin : BuiltinFun} {entry : VarId × Expr}
    (hb : forcedBuiltin g = some (builtin, .one .argV))
    (hbl : (b == l) = true) (hfind : Γ.find? (fun e => e.1 == h) = some entry)
    (hentry : entry.2 = .App g (.Var l)) :
    FactRel G Produces Γ (.App g (.Var b)) (.Var h) := by
  intro env t _ hd _ hk hs hlow
  have hmem := List.mem_of_find?_eq_some hfind
  have hkey : (entry.1 == h) = true := by simpa using List.find?_some hfind
  have hhb := hk entry hmem
  rw [envLookupT_congr hkey] at hhb
  obtain ⟨ih, hih⟩ := Option.isSome_iff_exists.mp hhb
  obtain ⟨tf, ta, _, hta, rfl⟩ := lowerTotalExpr_app_some hlow
  obtain ⟨ib, hib, rfl⟩ := lowerTotalExpr_var_some hta
  refine ⟨.Var (ih + 1), by rw [lowerTotalExpr_var, hih]; rfl, ?_⟩
  intro ρ π henv hlen hπ hF
  obtain ⟨vh, k, hik, hk', hvh, trhs, htrhs, hhalt⟩ := hF h entry ih hfind hih
  rw [hentry] at htrhs
  have hbound := resolveHead_app_var_bound 0 Γ (.App g (.Var l))
    (env := env.drop k) rfl (FactsScoped.ofFactsHold (hF.drop hd k)) (hd.drop k) (by simp [htrhs])
  obtain ⟨jl, hjl⟩ := Option.isSome_iff_exists.mp hbound
  have hlb : envLookupT env b = some (jl + k) := by
    rw [envLookupT_congr hbl]; exact hd.drop_lookup k hjl
  rw [hib] at hlb; cases hlb
  have hib_lt := envLookupT_bound env b _ hib
  obtain ⟨vl, hvl, _⟩ := envWellFormed_lookup env.length henv (n := jl + k + 1) (by omega) (by omega)
  have hvl_ctx : (dropEnv k ρ).lookup (jl + 1) = some vl := by
    rw [dropEnv_lookup k ρ _ (by omega), show jl + 1 + k = jl + k + 1 by omega]; exact hvl
  obtain ⟨hiff_ctx, _⟩ := resolveHead_unary 0 Γ _ rfl hb (hF.drop hd k) (hd.drop k) htrhs hjl hvl_ctx
  have heval := (hiff_ctx vh).mp hhalt
  obtain ⟨hiff, _⟩ := resolveHead_unary 0 Γ (.App g (.Var b)) rfl hb hF hd hlow hib hvl
  have hsrc := (hiff vh).mpr heval
  exact obsRefines_of_reaches (halts_on_stack hsrc π) (halts_on_stack (halts_var_of_lookup hvh) π)
    (obsRefines_refl _)

def fstApp (x : VarId) : Expr := .App (.Force (.Force (.Builtin .FstPair))) (.Var x)
def sndApp (x : VarId) : Expr := .App (.Force (.Force (.Builtin .SndPair))) (.Var x)

theorem replaceProjections_let (x f s : VarId) (bs : List (VarId × Expr × Bool)) (body : Expr) :
    replaceProjections x f s (.Let bs body) =
      .Let (bs.map fun (y, rhs, er) => (y, replaceProjections x f s rhs, er))
        (replaceProjections x f s body) := by
  rw [replaceProjections, binds_attach_map]

/-- Projections of `x` replaced by the binders recorded as holding them. -/
theorem replaceProjections_factRel (x f s : VarId) (fstEntry sndEntry : VarId × Expr)
    (hfst : fstEntry.2 = fstApp x) (hsnd : sndEntry.2 = sndApp x) (X : Expr)
    (Γ : List (VarId × Expr)) (hX : maxUidExpr X < f.uid ∧ maxUidExpr X < s.uid)
    (hff : Γ.find? (fun e => e.1 == f) = some fstEntry)
    (hfs : Γ.find? (fun e => e.1 == s) = some sndEntry) :
    FactRel (fun _ => True) Produces Γ X (replaceProjections x f s X) := by
  unfold replaceProjections
  split
  · rename_i b
    split
    · rename_i hxb
      exact unaryProjection_factRel rfl (varId_beq_symm hxb) hff hfst
    · exact FactRel.refl _ _ _ _
  · rename_i b
    split
    · rename_i hxb
      exact unaryProjection_factRel rfl (varId_beq_symm hxb) hfs hsnd
    · exact FactRel.refl _ _ _ _
  · rename_i g a _ _
    simp only [maxUidExpr] at hX
    exact (replaceProjections_factRel x f s fstEntry sndEntry hfst hsnd g Γ (by omega) hff hfs).app
      (replaceProjections_factRel x f s fstEntry sndEntry hfst hsnd a Γ (by omega) hff hfs)
  · rename_i y b
    simp only [maxUidExpr] at hX
    exact (replaceProjections_factRel x f s fstEntry sndEntry hfst hsnd b Γ (by omega) hff hfs).lam
      trivial
  · rename_i y b
    cases b with
    | Lam z inner =>
      rw [replaceProjections.eq_4]
      simp only [maxUidExpr] at hX
      exact (replaceProjections_factRel x f s fstEntry sndEntry hfst hsnd inner Γ (by omega) hff
        hfs).fix_lam trivial trivial (fun _ _ => trivial)
    | _ =>
      intro env t _ _ _ _ _ hlow
      rw [MIR.lowerTotalExpr_fix_nonlam_none env y _ (by intros; simp)] at hlow
      cases hlow
  · rename_i b
    simp only [maxUidExpr] at hX
    exact (replaceProjections_factRel x f s fstEntry sndEntry hfst hsnd b Γ (by omega) hff hfs).force
  · rename_i b
    simp only [maxUidExpr] at hX
    exact (replaceProjections_factRel x f s fstEntry sndEntry hfst hsnd b Γ (by omega) hff hfs).delay
  · rename_i tag fields
    apply FactRel.constr
    apply listRel_attach_map
    intro c hc
    have := maxUidExpr_le_maxUidExprList_of_mem hc
    simp only [maxUidExpr] at hX
    exact replaceProjections_factRel x f s fstEntry sndEntry hfst hsnd c Γ (by omega) hff hfs
  · rename_i scrutinee alternatives
    simp only [maxUidExpr] at hX
    apply FactRel.case (replaceProjections_factRel x f s fstEntry sndEntry hfst hsnd scrutinee Γ
      (by omega) hff hfs)
    apply listRel_attach_map
    intro c hc
    have := maxUidExpr_le_maxUidExprList_of_mem hc
    exact replaceProjections_factRel x f s fstEntry sndEntry hfst hsnd c Γ (by omega) hff hfs
  · rename_i bindings body
    rw [binds_attach_map]
    cases bindings with
    | nil =>
      simp only [maxUidExpr, maxUidExprBinds] at hX
      refine ((replaceProjections_factRel x f s fstEntry sndEntry hfst hsnd body Γ
        (by omega) hff hfs).congr_left (fun env => lowerTotalExpr_let_nil env body)
        (fun avoid => freshIn_let_nil avoid body)).congr_right ?_
      intro env; exact lowerTotalExpr_let_nil env _
    | cons binding rest =>
      simp only [maxUidExpr, maxUidExprBinds_cons'] at hX
      have hxf : (binding.1 == f) = false := beq_false_of_uid_lt (by omega)
      have hxs : (binding.1 == s) = false := beq_false_of_uid_lt (by omega)
      have ihr := replaceProjections_factRel x f s fstEntry sndEntry hfst hsnd binding.2.1 Γ
        (by omega) hff hfs
      have ihrest := replaceProjections_factRel x f s fstEntry sndEntry hfst hsnd
        (.Let rest body) ((binding.1, binding.2.1) :: Γ) (by simp only [maxUidExpr]; omega)
        (by rw [find?_cons_of_ne hxf]; exact hff) (by rw [find?_cons_of_ne hxs]; exact hfs)
      rw [replaceProjections_let] at ihrest
      refine ((FactRel.let_single (er := binding.2.2) binding.2.1 trivial (.inl rfl) ihr ihrest
        (fun _ _ _ _ _ _ hp => hp)).congr_left (fun env => lowerTotalExpr_let_cons env _ _ _)
        (fun avoid => freshIn_let_cons avoid _ _ _)).congr_right ?_
      intro env
      simp only [List.map_cons]
      exact lowerTotalExpr_let_cons env _ _ _
  all_goals exact FactRel.refl _ _ _ _
termination_by exprSize X
decreasing_by
  all_goals first
    | (subst_vars; simp only [exprSize, exprSizeBinds]; omega)
    | (subst_vars; exact let_rest_lt _ _ _)
    | (subst_vars; exact let_rhs_lt _ _ _)
    | (subst_vars; have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)

theorem freshIn_replaceProjections (x f s : VarId) (X : Expr) :
    ∀ avoid, freshIn avoid (replaceProjections x f s X) = freshIn avoid X := by
  intro avoid
  unfold replaceProjections
  split
  · split <;> simp [freshIn]
  · split <;> simp [freshIn]
  · rename_i g a _ _
    simp only [freshIn, freshIn_replaceProjections x f s g, freshIn_replaceProjections x f s a]
  · rename_i y b
    simp only [freshIn, freshIn_replaceProjections x f s b]
  · rename_i y b
    simp only [freshIn, freshIn_replaceProjections x f s b]
  · rename_i b
    simp only [freshIn, freshIn_replaceProjections x f s b]
  · rename_i b
    simp only [freshIn, freshIn_replaceProjections x f s b]
  · rename_i tag fields
    simp only [freshIn]
    exact freshInList_attach_map fields _ fun y _ => freshIn_replaceProjections x f s y avoid
  · rename_i scrutinee alternatives
    simp only [freshIn, freshIn_replaceProjections x f s scrutinee]
    rw [freshInList_attach_map alternatives _ fun y _ => freshIn_replaceProjections x f s y avoid]
  · rename_i bindings body
    simp only [freshIn]
    rw [binds_attach_map]
    exact freshInLet_map _ bindings body avoid
      (fun b _ avoid => freshIn_replaceProjections x f s b.2.1 avoid)
      (fun avoid => freshIn_replaceProjections x f s body avoid)
  all_goals rfl
termination_by exprSize X
decreasing_by
  all_goals first
    | (subst_vars; simp only [exprSize, exprSizeBinds]; omega)
    | (subst_vars; have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)
    | (subst_vars; have := exprSizeBinds_mem_lt (by assumption); simp only [exprSize]; omega)

/-! ## Identifiers after replacement -/

theorem maxUidExprList_map_le (M : Nat) (g : Expr → Expr) :
    ∀ (xs : List Expr), (∀ y ∈ xs, maxUidExpr (g y) ≤ max (maxUidExpr y) M) →
      maxUidExprList (xs.map g) ≤ max (maxUidExprList xs) M
  | [], _ => by simp [maxUidExprList]
  | y :: ys, h => by
    have hy := h y (.head _)
    have hys := maxUidExprList_map_le M g ys fun z hz => h z (.tail _ hz)
    simp only [List.map_cons, maxUidExprList]
    omega

theorem maxUidExprBinds_map_le (M : Nat) (g : Expr → Expr) :
    ∀ (bs : List (VarId × Expr × Bool)), (∀ b ∈ bs, maxUidExpr (g b.2.1) ≤ max (maxUidExpr b.2.1) M) →
      maxUidExprBinds (bs.map fun (y, rhs, er) => (y, g rhs, er)) ≤ max (maxUidExprBinds bs) M
  | [], _ => by simp [maxUidExprBinds]
  | (y, r, er) :: bs, h => by
    have hy := h (y, r, er) (.head _)
    have hbs := maxUidExprBinds_map_le M g bs fun z hz => h z (.tail _ hz)
    simp only [List.map_cons, maxUidExprBinds] at hy hbs ⊢
    omega

theorem maxUidExpr_replaceProjections (x f s : VarId) (X : Expr) :
    maxUidExpr (replaceProjections x f s X) ≤ max (maxUidExpr X) (max f.uid s.uid) := by
  unfold replaceProjections
  split
  · split <;> simp [maxUidExpr] <;> omega
  · split <;> simp [maxUidExpr] <;> omega
  · rename_i g a _ _
    have := maxUidExpr_replaceProjections x f s g
    have := maxUidExpr_replaceProjections x f s a
    simp only [maxUidExpr]; omega
  · rename_i y b
    have := maxUidExpr_replaceProjections x f s b
    simp only [maxUidExpr]; omega
  · rename_i y b
    have := maxUidExpr_replaceProjections x f s b
    simp only [maxUidExpr]; omega
  · rename_i b
    have := maxUidExpr_replaceProjections x f s b
    simp only [maxUidExpr]; omega
  · rename_i b
    have := maxUidExpr_replaceProjections x f s b
    simp only [maxUidExpr]; omega
  · rename_i tag fields
    rw [attach_map_eq_map]
    have := maxUidExprList_map_le (max f.uid s.uid) (replaceProjections x f s) fields
      fun y _ => maxUidExpr_replaceProjections x f s y
    simp only [maxUidExpr]; omega
  · rename_i scrutinee alternatives
    rw [attach_map_eq_map]
    have := maxUidExpr_replaceProjections x f s scrutinee
    have := maxUidExprList_map_le (max f.uid s.uid) (replaceProjections x f s) alternatives
      fun y _ => maxUidExpr_replaceProjections x f s y
    simp only [maxUidExpr]; omega
  · rename_i bindings body
    rw [binds_attach_map]
    have := maxUidExpr_replaceProjections x f s body
    have := maxUidExprBinds_map_le (max f.uid s.uid) (replaceProjections x f s) bindings
      fun b _ => maxUidExpr_replaceProjections x f s b.2.1
    simp only [maxUidExpr] at *; omega
  all_goals omega
termination_by exprSize X
decreasing_by
  all_goals first
    | (subst_vars; simp only [exprSize]; omega)
    | (subst_vars; have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)
    | (subst_vars; have := exprSizeBinds_mem_lt (by assumption); simp only [exprSize]; omega)

/-! ## The replaced binder is no longer free -/

theorem freeVarsList_not_contains {x : VarId} :
    ∀ (es : List Expr), (∀ e ∈ es, (freeVars e).contains x = false) →
      (freeVarsList es).contains x = false
  | [], _ => by rw [freeVarsList]; rfl
  | e :: es, h => by
    rw [freeVarsList]
    exact VarSet.union_not_contains_fwd _ _ _ (h e (.head _))
      (freeVarsList_not_contains es fun e' he' => h e' (.tail _ he'))

theorem freeVarsLet_not_contains {x : VarId} {body : Expr}
    (hbody : (freeVars body).contains x = false) :
    ∀ (bs : List (VarId × Expr × Bool)), (∀ b ∈ bs, (freeVars b.2.1).contains x = false) →
      (freeVarsLet bs body).contains x = false
  | [], _ => by rw [freeVarsLet]; exact hbody
  | (y, r, er) :: bs, h => by
    rw [freeVarsLet]
    exact VarSet.union_not_contains_fwd _ _ _ (h (y, r, er) (.head _))
      (VarSet.erase_not_contains_fwd _ _ _
        (freeVarsLet_not_contains hbody bs fun b hb => h b (.tail _ hb)))

theorem all_attach_true {p : Expr → Bool} {xs : List Expr}
    (h : (xs.attach.all fun ⟨y, _⟩ => p y) = true) : ∀ y ∈ xs, p y = true := by
  intro y hy
  rw [List.all_eq_true] at h
  exact h ⟨y, hy⟩ (List.mem_attach _ _)

theorem all_attach_binds_true {p : Expr → Bool} {bs : List (VarId × Expr × Bool)}
    (h : (bs.attach.all fun ⟨(_, rhs, _), _⟩ => p rhs) = true) : ∀ b ∈ bs, p b.2.1 = true := by
  intro b hb
  rw [List.all_eq_true] at h
  exact h ⟨b, hb⟩ (List.mem_attach _ _)

theorem projectionOnly_app {x : VarId} {g a : Expr} (h : projectionOnly x (.App g a) = true)
    (h₁ : ∀ o, g = .Force (.Force (.Builtin .FstPair)) → a = .Var o → False)
    (h₂ : ∀ o, g = .Force (.Force (.Builtin .SndPair)) → a = .Var o → False) :
    projectionOnly x g = true ∧ projectionOnly x a = true := by
  rw [projectionOnly] at h
  · simpa using h
  · exact h₁
  · exact h₂

theorem replaceProjections_not_free (x f s : VarId) (hf : (f == x) = false) (hs : (s == x) = false)
    (X : Expr) (h : projectionOnly x X = true) :
    (freeVars (replaceProjections x f s X)).contains x = false := by
  unfold replaceProjections
  split
  · rename_i o
    split
    · rw [freeVars, VarSet.singleton_contains']; exact hf
    · rename_i hxo
      simp only [freeVars]
      refine VarSet.union_not_contains_fwd _ _ _ rfl ?_
      rw [VarSet.singleton_contains']
      cases hc : (o == x)
      · rfl
      · exact absurd (varId_beq_symm hc) hxo
  · rename_i o
    split
    · rw [freeVars, VarSet.singleton_contains']; exact hs
    · rename_i hxo
      simp only [freeVars]
      refine VarSet.union_not_contains_fwd _ _ _ rfl ?_
      rw [VarSet.singleton_contains']
      cases hc : (o == x)
      · rfl
      · exact absurd (varId_beq_symm hc) hxo
  · rename_i g a h₁ h₂
    obtain ⟨hg, ha⟩ := projectionOnly_app h h₁ h₂
    rw [freeVars]
    exact VarSet.union_not_contains_fwd _ _ _ (replaceProjections_not_free x f s hf hs g hg)
      (replaceProjections_not_free x f s hf hs a ha)
  · rename_i y b
    rw [projectionOnly] at h
    rw [freeVars]
    exact VarSet.erase_not_contains_fwd _ _ _ (replaceProjections_not_free x f s hf hs b h)
  · rename_i y b
    rw [projectionOnly] at h
    rw [freeVars]
    exact VarSet.erase_not_contains_fwd _ _ _ (replaceProjections_not_free x f s hf hs b h)
  · rename_i b
    rw [projectionOnly] at h
    rw [freeVars]
    exact replaceProjections_not_free x f s hf hs b h
  · rename_i b
    rw [projectionOnly] at h
    rw [freeVars]
    exact replaceProjections_not_free x f s hf hs b h
  · rename_i tag fields
    rw [projectionOnly] at h
    rw [freeVars, attach_map_eq_map]
    refine freeVarsList_not_contains _ ?_
    intro e he
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp he
    exact replaceProjections_not_free x f s hf hs y (all_attach_true h y hy)
  · rename_i scrutinee alternatives
    rw [projectionOnly] at h
    simp only [Bool.and_eq_true] at h
    rw [freeVars, attach_map_eq_map]
    refine VarSet.union_not_contains_fwd _ _ _
      (replaceProjections_not_free x f s hf hs scrutinee h.1) (freeVarsList_not_contains _ ?_)
    intro e he
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp he
    exact replaceProjections_not_free x f s hf hs y (all_attach_true h.2 y hy)
  · rename_i bindings body
    rw [projectionOnly] at h
    simp only [Bool.and_eq_true] at h
    rw [freeVars, binds_attach_map]
    refine freeVarsLet_not_contains (replaceProjections_not_free x f s hf hs body h.2) _ ?_
    intro b hb
    obtain ⟨⟨y, r, er⟩, hmem, rfl⟩ := List.mem_map.mp hb
    exact replaceProjections_not_free x f s hf hs r (all_attach_binds_true h.1 _ hmem)
  · rename_i o
    rw [projectionOnly] at h
    rw [freeVars, VarSet.singleton_contains']
    cases hc : (o == x)
    · rfl
    · rw [bne, varId_beq_symm hc] at h; cases h
  all_goals (rw [freeVars]; rfl)
termination_by exprSize X
decreasing_by
  all_goals first
    | (subst_vars; simp only [exprSize]; omega)
    | (subst_vars; have := exprSize_lt_of_mem hy; simp only [exprSize]; omega)
    | (subst_vars; have := exprSizeBinds_mem_lt hmem; simp only [exprSize] at *; omega)

end Moist.Verified.ShapeFacts
