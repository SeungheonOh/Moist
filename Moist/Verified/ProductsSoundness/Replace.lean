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

/-- An application whose head resolves to a forced unary builtin on `l`
    refines the binder recorded as holding an application that resolves to the
    same builtin on the same variable. -/
theorem resolvedProjection_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {h l l' : VarId}
    {e gs ge : Expr} {builtin : BuiltinFun} {entry : VarId × Expr} {n m : Nat}
    (hsrc : resolveHead n Γ e = .App gs (.Var l)) (hbs : forcedBuiltin gs = some (builtin, .one .argV))
    (hfind : Γ.find? (fun e => e.1 == h) = some entry)
    (hentry : resolveHead m Γ entry.2 = .App ge (.Var l'))
    (hbe : forcedBuiltin ge = some (builtin, .one .argV)) (hll : (l == l') = true) :
    FactRel G Produces Γ e (.Var h) := by
  intro env t _ hd _ hk hs hlow
  have hmem := List.mem_of_find?_eq_some hfind
  have hkey : (entry.1 == h) = true := by simpa using List.find?_some hfind
  have hhb := hk entry hmem
  rw [envLookupT_congr hkey] at hhb
  obtain ⟨ih, hih⟩ := Option.isSome_iff_exists.mp hhb
  refine ⟨.Var (ih + 1), by rw [lowerTotalExpr_var, hih]; rfl, ?_⟩
  intro ρ π henv hlen hπ hF
  obtain ⟨vh, k, hik, hk', hvh, trhs, htrhs, hhalt⟩ := hF h entry ih hfind hih
  have hbound := resolveHead_app_var_bound m Γ entry.2
    (env := env.drop k) hentry (FactsScoped.ofFactsHold (hF.drop hd k)) (hd.drop k) (by simp [htrhs])
  obtain ⟨jl, hjl⟩ := Option.isSome_iff_exists.mp hbound
  have hlb : envLookupT env l = some (jl + k) := by
    rw [envLookupT_congr hll]; exact hd.drop_lookup k hjl
  have hib_lt := envLookupT_bound env l _ hlb
  obtain ⟨vl, hvl, _⟩ := envWellFormed_lookup env.length henv (n := jl + k + 1) (by omega) (by omega)
  have hvl_ctx : (dropEnv k ρ).lookup (jl + 1) = some vl := by
    rw [dropEnv_lookup k ρ _ (by omega), show jl + 1 + k = jl + k + 1 by omega]; exact hvl
  obtain ⟨hiff_ctx, _⟩ := resolveHead_unary m Γ _ hentry hbe (hF.drop hd k) (hd.drop k) htrhs hjl hvl_ctx
  have heval := (hiff_ctx vh).mp hhalt
  obtain ⟨hiff, _⟩ := resolveHead_unary n Γ e hsrc hbs hF hd hlow hlb hvl
  have hsrc' := (hiff vh).mpr heval
  exact obsRefines_of_reaches (halts_on_stack hsrc' π) (halts_on_stack (halts_var_of_lookup hvh) π)
    (obsRefines_refl _)

theorem projectionKind_some {Γ : List (VarId × Expr)} {fn : Expr} {k : Bool}
    (h : projectionKind Γ fn = some k) :
    resolveHead 64 Γ fn = .Force (.Force (.Builtin (if k then .FstPair else .SndPair))) := by
  unfold projectionKind at h
  split at h
  · rename_i heq; cases h; exact heq
  · rename_i heq; cases h; exact heq
  · cases h

theorem projectsBinder_true {Γ : List (VarId × Expr)} {x : VarId} {fn a : Expr}
    (h : projectsBinder Γ x fn a = true) :
    ∃ o k, a = .Var o ∧ (o == x) = true ∧ projectionKind Γ fn = some k := by
  unfold projectsBinder at h
  split at h
  · rename_i o
    simp only [Bool.and_eq_true, Option.isSome_iff_exists] at h
    obtain ⟨hox, k, hk⟩ := h
    exact ⟨o, k, rfl, hox, hk⟩
  · cases h

theorem lowerTotalExpr_consLet (env : List VarId) (binding : VarId × Expr × Bool) (e : Expr) :
    lowerTotalExpr env (consLet binding e) = lowerTotalExpr env (.Let [binding] e) := by
  unfold consLet
  split
  · exact lowerTotalExpr_let_cons env _ _ _
  · rfl

theorem freshIn_consLet (avoid : List VarId) (binding : VarId × Expr × Bool) (e : Expr) :
    freshIn avoid (consLet binding e) = freshIn avoid (.Let [binding] e) := by
  unfold consLet
  split
  · exact freshIn_let_cons avoid _ _ _
  · rfl

theorem freeVars_consLet (binding : VarId × Expr × Bool) (e : Expr) :
    freeVars (consLet binding e) = freeVars (.Let [binding] e) := by
  obtain ⟨y, r, er⟩ := binding
  unfold consLet
  split
  · rename_i bindings body
    simp only [freeVars, freeVarsLet]
  · rfl

theorem maxUidExpr_consLet (binding : VarId × Expr × Bool) (e : Expr) :
    maxUidExpr (consLet binding e) = maxUidExpr (.Let [binding] e) := by
  obtain ⟨y, r, er⟩ := binding
  unfold consLet
  split
  · simp only [maxUidExpr, maxUidExprBinds]; omega
  · rfl

/-- Projections of `x` replaced by the binders recorded as holding them. -/
theorem replaceProjections_factRel (x f s : VarId) (fstEntry sndEntry : VarId × Expr)
    (hfst : fstEntry.2 = fstApp x) (hsnd : sndEntry.2 = sndApp x) (X : Expr)
    (Γ : List (VarId × Expr)) (hX : maxUidExpr X < f.uid ∧ maxUidExpr X < s.uid)
    (hff : Γ.find? (fun e => e.1 == f) = some fstEntry)
    (hfs : Γ.find? (fun e => e.1 == s) = some sndEntry) :
    FactRel (fun _ => True) Produces Γ X (replaceProjections Γ x f s X) := by
  unfold replaceProjections
  split
  · rename_i g a
    split
    · rename_i hproj
      obtain ⟨o, k, rfl, hox, hk⟩ := projectsBinder_true hproj
      have hres := projectionKind_some hk
      have hsrc : resolveHead 65 Γ (.App g (.Var o)) =
          .App (.Force (.Force (.Builtin (if k then .FstPair else .SndPair)))) (.Var o) := by
        rw [resolveHead_app, hres]
      rw [hk]
      cases k
      · exact resolvedProjection_factRel (m := 0) hsrc rfl hfs (by rw [resolveHead_zero, hsnd]; rfl)
          rfl hox
      · exact resolvedProjection_factRel (m := 0) hsrc rfl hff (by rw [resolveHead_zero, hfst]; rfl)
          rfl hox
    · simp only [maxUidExpr] at hX
      exact (replaceProjections_factRel x f s fstEntry sndEntry hfst hsnd g Γ (by omega) hff hfs).app
        (replaceProjections_factRel x f s fstEntry sndEntry hfst hsnd a Γ (by omega) hff hfs)
  · rename_i y b
    simp only [maxUidExpr] at hX
    exact (replaceProjections_factRel x f s fstEntry sndEntry hfst hsnd b Γ (by omega) hff hfs).lam
      trivial
  · rename_i y b
    cases b with
    | Lam z inner =>
      rw [replaceProjections.eq_def]
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
  · rename_i body
    simp only [maxUidExpr, maxUidExprBinds] at hX
    refine ((replaceProjections_factRel x f s fstEntry sndEntry hfst hsnd body Γ
      (by omega) hff hfs).congr_left (fun env => lowerTotalExpr_let_nil env body)
      (fun avoid => freshIn_let_nil avoid body)).congr_right ?_
    intro env; exact lowerTotalExpr_let_nil env _
  · rename_i name rhs erased rest body
    simp only [maxUidExpr, maxUidExprBinds] at hX
    have hxf : (name == f) = false := beq_false_of_uid_lt (by omega)
    have hxs : (name == s) = false := beq_false_of_uid_lt (by omega)
    have hpos := exprSize_pos rhs
    have ihr := replaceProjections_factRel x f s fstEntry sndEntry hfst hsnd rhs Γ
      (by omega) hff hfs
    have ihrest := replaceProjections_factRel x f s fstEntry sndEntry hfst hsnd
      (.Let rest body) ((name, rhs) :: Γ) (by simp only [maxUidExpr]; omega)
      (by rw [find?_cons_of_ne hxf]; exact hff) (by rw [find?_cons_of_ne hxs]; exact hfs)
    refine ((FactRel.let_single (er := erased) rhs trivial (.inl rfl) ihr ihrest
      (fun _ _ _ _ _ _ hp => hp)).congr_left (fun env => lowerTotalExpr_let_cons env _ _ _)
      (fun avoid => freshIn_let_cons avoid _ _ _)).congr_right ?_
    intro env
    exact lowerTotalExpr_consLet env _ _
  all_goals exact FactRel.refl _ _ _ _
termination_by exprSize X
decreasing_by
  all_goals first
    | (subst_vars; simp only [exprSize, exprSizeBinds]; omega)
    | (subst_vars; have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)

theorem freshInList_map_of {avoid : List VarId} {g : Expr → Expr} :
    ∀ (xs : List Expr), freshInList avoid xs = true →
      (∀ y ∈ xs, freshIn avoid y = true → freshIn avoid (g y) = true) →
      freshInList avoid (xs.map g) = true
  | [], _, _ => by simp [freshInList]
  | y :: ys, hxs, h => by
    simp only [freshInList, List.map_cons, Bool.and_eq_true] at hxs ⊢
    exact ⟨h y (.head _) hxs.1, freshInList_map_of ys hxs.2 fun z hz => h z (.tail _ hz)⟩

theorem freshIn_replaceProjections (Γ : List (VarId × Expr)) (x f s : VarId) (X : Expr) :
    ∀ avoid, freshIn avoid X = true → freshIn avoid (replaceProjections Γ x f s X) = true := by
  intro avoid hX
  unfold replaceProjections
  split
  · rename_i g a
    split
    · split <;> simp [freshIn]
    · simp only [freshIn, Bool.and_eq_true] at hX ⊢
      exact ⟨freshIn_replaceProjections Γ x f s g avoid hX.1,
        freshIn_replaceProjections Γ x f s a avoid hX.2⟩
  · rename_i y b
    simp only [freshIn, Bool.and_eq_true] at hX ⊢
    exact ⟨hX.1, freshIn_replaceProjections Γ x f s b _ hX.2⟩
  · rename_i y b
    simp only [freshIn, Bool.and_eq_true] at hX ⊢
    exact ⟨hX.1, freshIn_replaceProjections Γ x f s b _ hX.2⟩
  · rename_i b
    simp only [freshIn] at hX ⊢
    exact freshIn_replaceProjections Γ x f s b _ hX
  · rename_i b
    simp only [freshIn] at hX ⊢
    exact freshIn_replaceProjections Γ x f s b _ hX
  · rename_i tag fields
    simp only [freshIn] at hX ⊢
    rw [attach_map_eq_map]
    exact freshInList_map_of fields hX fun y _ hy => freshIn_replaceProjections Γ x f s y avoid hy
  · rename_i scrutinee alternatives
    simp only [freshIn, Bool.and_eq_true] at hX ⊢
    rw [attach_map_eq_map]
    exact ⟨freshIn_replaceProjections Γ x f s scrutinee avoid hX.1,
      freshInList_map_of alternatives hX.2 fun y _ hy => freshIn_replaceProjections Γ x f s y avoid hy⟩
  · rename_i body
    rw [freshIn_let_nil] at hX ⊢
    exact freshIn_replaceProjections Γ x f s body avoid hX
  · rename_i name rhs erased rest body
    have hpos := exprSize_pos rhs
    rw [freshIn_let_cons, freshIn_let_single] at hX
    rw [freshIn_consLet, freshIn_let_single]
    simp only [Bool.and_eq_true] at hX ⊢
    exact ⟨⟨freshIn_replaceProjections Γ x f s rhs avoid hX.1.1, hX.1.2⟩,
      freshIn_replaceProjections ((name, rhs) :: Γ) x f s (.Let rest body) _ hX.2⟩
  all_goals exact hX
termination_by exprSize X
decreasing_by
  all_goals first
    | (subst_vars; simp only [exprSize, exprSizeBinds]; omega)
    | (subst_vars; have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)

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

theorem maxUidExpr_replaceProjections (Γ : List (VarId × Expr)) (x f s : VarId) (X : Expr) :
    maxUidExpr (replaceProjections Γ x f s X) ≤ max (maxUidExpr X) (max f.uid s.uid) := by
  unfold replaceProjections
  split
  · rename_i g a
    split
    · split <;> simp [maxUidExpr] <;> omega
    · have := maxUidExpr_replaceProjections Γ x f s g
      have := maxUidExpr_replaceProjections Γ x f s a
      simp only [maxUidExpr]; omega
  · rename_i y b
    have := maxUidExpr_replaceProjections Γ x f s b
    simp only [maxUidExpr]; omega
  · rename_i y b
    have := maxUidExpr_replaceProjections Γ x f s b
    simp only [maxUidExpr]; omega
  · rename_i b
    have := maxUidExpr_replaceProjections Γ x f s b
    simp only [maxUidExpr]; omega
  · rename_i b
    have := maxUidExpr_replaceProjections Γ x f s b
    simp only [maxUidExpr]; omega
  · rename_i tag fields
    rw [attach_map_eq_map]
    have := maxUidExprList_map_le (max f.uid s.uid) (replaceProjections Γ x f s) fields
      fun y _ => maxUidExpr_replaceProjections Γ x f s y
    simp only [maxUidExpr]; omega
  · rename_i scrutinee alternatives
    rw [attach_map_eq_map]
    have := maxUidExpr_replaceProjections Γ x f s scrutinee
    have := maxUidExprList_map_le (max f.uid s.uid) (replaceProjections Γ x f s) alternatives
      fun y _ => maxUidExpr_replaceProjections Γ x f s y
    simp only [maxUidExpr]; omega
  · rename_i body
    have := maxUidExpr_replaceProjections Γ x f s body
    simp only [maxUidExpr, maxUidExprBinds] at *; omega
  · rename_i name rhs erased rest body
    have hpos := exprSize_pos rhs
    have := maxUidExpr_replaceProjections Γ x f s rhs
    have := maxUidExpr_replaceProjections ((name, rhs) :: Γ) x f s (.Let rest body)
    rw [maxUidExpr_consLet]
    simp only [maxUidExpr, maxUidExprBinds] at *; omega
  all_goals omega
termination_by exprSize X
decreasing_by
  all_goals first
    | (subst_vars; simp only [exprSize, exprSizeBinds]; omega)
    | (subst_vars; have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)

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

theorem replaceProjections_not_free (Γ : List (VarId × Expr)) (x f s : VarId) (hf : (f == x) = false)
    (hs : (s == x) = false) (X : Expr) (h : projectionOnly Γ x X = true) :
    (freeVars (replaceProjections Γ x f s X)).contains x = false := by
  unfold replaceProjections
  split
  · rename_i g a
    split
    · split
      · rw [freeVars, VarSet.singleton_contains']; exact hf
      · rw [freeVars, VarSet.singleton_contains']; exact hs
    · rename_i hproj
      have hfalse : projectsBinder Γ x g a = false := by simpa using hproj
      rw [projectionOnly, hfalse, Bool.false_or, Bool.and_eq_true] at h
      rw [freeVars]
      exact VarSet.union_not_contains_fwd _ _ _ (replaceProjections_not_free Γ x f s hf hs g h.1)
        (replaceProjections_not_free Γ x f s hf hs a h.2)
  · rename_i y b
    rw [projectionOnly] at h
    rw [freeVars]
    exact VarSet.erase_not_contains_fwd _ _ _ (replaceProjections_not_free Γ x f s hf hs b h)
  · rename_i y b
    rw [projectionOnly] at h
    rw [freeVars]
    exact VarSet.erase_not_contains_fwd _ _ _ (replaceProjections_not_free Γ x f s hf hs b h)
  · rename_i b
    rw [projectionOnly] at h
    rw [freeVars]
    exact replaceProjections_not_free Γ x f s hf hs b h
  · rename_i b
    rw [projectionOnly] at h
    rw [freeVars]
    exact replaceProjections_not_free Γ x f s hf hs b h
  · rename_i tag fields
    rw [projectionOnly] at h
    rw [freeVars, attach_map_eq_map]
    refine freeVarsList_not_contains _ ?_
    intro e he
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp he
    exact replaceProjections_not_free Γ x f s hf hs y (all_attach_true h y hy)
  · rename_i scrutinee alternatives
    rw [projectionOnly] at h
    simp only [Bool.and_eq_true] at h
    rw [freeVars, attach_map_eq_map]
    refine VarSet.union_not_contains_fwd _ _ _
      (replaceProjections_not_free Γ x f s hf hs scrutinee h.1) (freeVarsList_not_contains _ ?_)
    intro e he
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp he
    exact replaceProjections_not_free Γ x f s hf hs y (all_attach_true h.2 y hy)
  · rename_i body
    rw [projectionOnly] at h
    rw [freeVars]
    exact freeVarsLet_not_contains (replaceProjections_not_free Γ x f s hf hs body h) [] (by simp)
  · rename_i name rhs erased rest body
    have hpos := exprSize_pos rhs
    rw [projectionOnly] at h
    simp only [Bool.and_eq_true] at h
    rw [freeVars_consLet, freeVars]
    refine freeVarsLet_not_contains
      (replaceProjections_not_free ((name, rhs) :: Γ) x f s hf hs (.Let rest body) h.2) _ ?_
    intro b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact replaceProjections_not_free Γ x f s hf hs rhs h.1
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
    | (subst_vars; simp only [exprSize, exprSizeBinds]; omega)
    | (subst_vars; have := exprSize_lt_of_mem hy; simp only [exprSize]; omega)

end Moist.Verified.ShapeFacts
