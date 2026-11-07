import Moist.Verified.ShapesSoundness.Destructors

/-! # List choice fusion

`case nullList l [nonempty, empty]` becomes
`case l [λh t. nonempty[headList l := h, tailList l := t], empty]` when `l` is
known to be a list. In the non-empty branch the fresh binders hold exactly the
head and the tail of `l`, which justifies replacing the projections
(`replaceListProjections_factRel`).
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines

/-- A projection of `l` refines the binder recorded as holding it. -/
theorem projection_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {b l h : VarId}
    {builtin : BuiltinFun} {entry : VarId × Expr}
    (hb : forcedBuiltin (.Force (.Builtin builtin)) = some (builtin, .one .argV))
    (hbl : (b == l) = true) (hfind : Γ.find? (fun e => e.1 == h) = some entry)
    (hentry : entry.2 = .App (.Force (.Builtin builtin)) (.Var l)) :
    FactRel G Produces Γ (.App (.Force (.Builtin builtin)) (.Var b)) (.Var h) := by
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
  have hbound := resolveHead_app_var_bound 0 Γ (.App (.Force (.Builtin builtin)) (.Var l))
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
  obtain ⟨hiff, _⟩ := resolveHead_unary 0 Γ (.App (.Force (.Builtin builtin)) (.Var b)) rfl hb hF hd
    hlow hib hvl
  have hsrc := (hiff vh).mpr heval
  exact obsRefines_of_reaches (halts_on_stack hsrc π) (halts_on_stack (halts_var_of_lookup hvh) π)
    (obsRefines_refl _)

theorem maxUidExpr_lt_lam {x : VarId} {b : Expr} {u : Nat} (h : maxUidExpr (.Lam x b) < u) :
    x.uid < u ∧ maxUidExpr b < u := by simp only [maxUidExpr] at h; omega

theorem binds_attach_map (f : Expr → Expr) (bs : List (VarId × Expr × Bool)) :
    (bs.attach.map fun ⟨(y, rhs, er), _⟩ => (y, f rhs, er)) =
      bs.map fun (y, rhs, er) => (y, f rhs, er) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨y, rhs, er⟩ := b
    simp only [List.attach_cons, List.map_cons, List.map_map]
    congr 1

theorem replaceListProjections_let (l h t : VarId) (bs : List (VarId × Expr × Bool)) (body : Expr) :
    replaceListProjections l h t (.Let bs body) =
      .Let (bs.map fun (y, rhs, er) => (y, replaceListProjections l h t rhs, er))
        (replaceListProjections l h t body) := by
  rw [replaceListProjections, binds_attach_map]

theorem maxUidExprBinds_cons' (b : VarId × Expr × Bool) (rest : List (VarId × Expr × Bool)) :
    maxUidExprBinds (b :: rest) = max b.1.uid (max (maxUidExpr b.2.1) (maxUidExprBinds rest)) := by
  obtain ⟨x, r, er⟩ := b; simp [maxUidExprBinds]

theorem exprSizeBinds_cons' (b : VarId × Expr × Bool) (rest : List (VarId × Expr × Bool)) :
    exprSizeBinds (b :: rest) = exprSize b.2.1 + exprSizeBinds rest := by
  obtain ⟨x, r, er⟩ := b; simp [exprSizeBinds]

theorem let_rest_lt (b : VarId × Expr × Bool) (rest : List (VarId × Expr × Bool)) (body : Expr) :
    exprSize (.Let rest body) < exprSize (.Let (b :: rest) body) := by
  have := exprSize_pos b.2.1
  simp only [exprSize, exprSizeBinds_cons']; omega

theorem let_rhs_lt (b : VarId × Expr × Bool) (rest : List (VarId × Expr × Bool)) (body : Expr) :
    exprSize b.2.1 < exprSize (.Let (b :: rest) body) := by
  simp only [exprSize, exprSizeBinds_cons']; omega

def headApp (l : VarId) : Expr := .App (.Force (.Builtin .HeadList)) (.Var l)
def tailApp (l : VarId) : Expr := .App (.Force (.Builtin .TailList)) (.Var l)

theorem find?_cons_of_ne {Γ : List (VarId × Expr)} {x y : VarId} {r : Expr} (hxy : (x == y) = false) :
    ((x, r) :: Γ).find? (fun e => e.1 == y) = Γ.find? (fun e => e.1 == y) := by
  simp [hxy]

theorem beq_false_of_uid_lt {x y : VarId} (h : x.uid < y.uid) : (x == y) = false := by
  rw [VarId.beq_false_iff]; right; omega

/-- Projections replaced by the binders recorded as holding the head and the
    tail of `l`. -/
theorem replaceListProjections_factRel (l h t : VarId) (headEntry tailEntry : VarId × Expr)
    (hhead : headEntry.2 = headApp l) (htail : tailEntry.2 = tailApp l) (X : Expr)
    (Γ : List (VarId × Expr)) (hX : maxUidExpr X < h.uid ∧ maxUidExpr X < t.uid)
    (hfh : Γ.find? (fun e => e.1 == h) = some headEntry)
    (hft : Γ.find? (fun e => e.1 == t) = some tailEntry) :
    FactRel (fun _ => True) Produces Γ X (replaceListProjections l h t X) := by
  unfold replaceListProjections
  split
  · rename_i b
    split
    · rename_i hbl
      exact projection_factRel rfl hbl hfh hhead
    · exact FactRel.refl _ _ _ _
  · rename_i b
    split
    · rename_i hbl
      exact projection_factRel rfl hbl hft htail
    · exact FactRel.refl _ _ _ _
  · rename_i f a _ _
    simp only [maxUidExpr] at hX
    exact (replaceListProjections_factRel l h t headEntry tailEntry hhead htail f Γ (by omega) hfh hft).app
      (replaceListProjections_factRel l h t headEntry tailEntry hhead htail a Γ (by omega) hfh hft)
  · rename_i y b
    simp only [maxUidExpr] at hX
    exact (replaceListProjections_factRel l h t headEntry tailEntry hhead htail b Γ (by omega) hfh hft).lam
      trivial
  · rename_i y b
    cases b with
    | Lam x inner =>
      rw [replaceListProjections.eq_4]
      simp only [maxUidExpr] at hX
      exact (replaceListProjections_factRel l h t headEntry tailEntry hhead htail inner Γ (by omega) hfh
        hft).fix_lam trivial trivial (fun _ _ => trivial)
    | _ =>
      intro env t _ _ _ _ _ hlow
      rw [MIR.lowerTotalExpr_fix_nonlam_none env y _ (by intros; simp)] at hlow
      cases hlow
  · rename_i b
    simp only [maxUidExpr] at hX
    exact (replaceListProjections_factRel l h t headEntry tailEntry hhead htail b Γ (by omega) hfh hft).force
  · rename_i b
    simp only [maxUidExpr] at hX
    exact (replaceListProjections_factRel l h t headEntry tailEntry hhead htail b Γ (by omega) hfh hft).delay
  · rename_i tag fields
    apply FactRel.constr
    apply listRel_attach_map
    intro c hc
    have := maxUidExpr_le_maxUidExprList_of_mem hc
    simp only [maxUidExpr] at hX
    exact replaceListProjections_factRel l h t headEntry tailEntry hhead htail c Γ (by omega) hfh hft
  · rename_i scrutinee alternatives
    simp only [maxUidExpr] at hX
    apply FactRel.case (replaceListProjections_factRel l h t headEntry tailEntry hhead htail scrutinee Γ
      (by omega) hfh hft)
    apply listRel_attach_map
    intro c hc
    have := maxUidExpr_le_maxUidExprList_of_mem hc
    exact replaceListProjections_factRel l h t headEntry tailEntry hhead htail c Γ (by omega) hfh hft
  · rename_i bindings body
    rw [binds_attach_map]
    cases bindings with
    | nil =>
      simp only [maxUidExpr, maxUidExprBinds] at hX
      refine ((replaceListProjections_factRel l h t headEntry tailEntry hhead htail body Γ
        (by omega) hfh hft).congr_left (fun env => lowerTotalExpr_let_nil env body)
        (fun avoid => freshIn_let_nil avoid body)).congr_right ?_
      intro env; exact lowerTotalExpr_let_nil env _
    | cons binding rest =>
      simp only [maxUidExpr, maxUidExprBinds_cons'] at hX
      have hxh : (binding.1 == h) = false := beq_false_of_uid_lt (by omega)
      have hxt : (binding.1 == t) = false := beq_false_of_uid_lt (by omega)
      have ihr := replaceListProjections_factRel l h t headEntry tailEntry hhead htail binding.2.1 Γ
        (by omega) hfh hft
      have ihrest := replaceListProjections_factRel l h t headEntry tailEntry hhead htail
        (.Let rest body) ((binding.1, binding.2.1) :: Γ) (by simp only [maxUidExpr]; omega)
        (by rw [find?_cons_of_ne hxh]; exact hfh) (by rw [find?_cons_of_ne hxt]; exact hft)
      rw [replaceListProjections_let] at ihrest
      refine ((FactRel.let_single (er := binding.2.2) binding.2.1 trivial (.inl rfl) ihr ihrest
        (fun _ _ _ _ _ hp => hp)).congr_left (fun env => lowerTotalExpr_let_cons env _ _ _)
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

/-! ## The choice -/

theorem builtin_app_reaches {ρ : CekEnv} {tf : Term} {n : Nat} {b : BuiltinFun} {vl : CekValue}
    {T : State} (hf : Halts ρ tf (.VBuiltin b [] (.one .argV))) (hvl : ρ.lookup n = some vl)
    (hT : Reaches (.ret [.funV (.VBuiltin b [] (.one .argV))] vl) T) :
    Reaches (.compute [] ρ (.Apply tf (.Var n))) T := by
  refine reaches_trans (reaches_of_steps 1 rfl) ?_
  refine reaches_trans (halts_on_stack hf _) ?_
  refine reaches_trans (reaches_of_steps 1 rfl) ?_
  exact reaches_trans (halts_on_stack (halts_var_of_lookup hvl) _) hT

theorem builtin_app_halts {ρ : CekEnv} {tf : Term} {n : Nat} {b : BuiltinFun} {vl w : CekValue}
    (hf : Halts ρ tf (.VBuiltin b [] (.one .argV))) (hvl : ρ.lookup n = some vl)
    (heval : evalBuiltin b [vl] = some w) : Halts ρ (.Apply tf (.Var n)) w :=
  builtin_app_reaches hf hvl ⟨2, by simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, heval]⟩

theorem builtin_app_errs {ρ : CekEnv} {tf : Term} {n : Nat} {b : BuiltinFun} {vl : CekValue}
    (hf : Halts ρ tf (.VBuiltin b [] (.one .argV))) (hvl : ρ.lookup n = some vl)
    (heval : evalBuiltin b [vl] = none) : Errs ρ (.Apply tf (.Var n)) :=
  builtin_app_reaches hf hvl ⟨1, by simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, heval]⟩

theorem case_bool_steps {ρ : CekEnv} {π : Stack} {s a₀ a₁ : Term} {b : Bool}
    (hs : Halts ρ s (.VCon (.Bool b))) :
    Reaches (.compute π ρ (.Case s [a₀, a₁])) (.compute π ρ (if b then a₁ else a₀)) := by
  refine reaches_trans (reaches_of_steps 1 rfl) ?_
  refine reaches_trans (halts_on_stack hs _) ?_
  refine ⟨1, ?_⟩
  cases b <;> rfl

theorem case_errs_of_scrutinee {ρ : CekEnv} {π : Stack} {s : Term} {alts : List Term}
    (hs : Errs ρ s) : Reaches (.compute π ρ (.Case s alts)) .error :=
  reaches_trans (reaches_of_steps 1 rfl) (errs_on_stack hs _)

theorem envLookupT_mem {env : List VarId} {x : VarId} {i : Nat} (h : envLookupT env x = some i) :
    ∃ y ∈ env, (y == x) = true := by
  induction env generalizing i with
  | nil => simp [envLookupT, envLookupT.go] at h
  | cons z zs ih =>
    rw [envLookupT_cons] at h
    split at h
    · rename_i hzx; exact ⟨z, .head _, hzx⟩
    · cases hl : envLookupT zs x with
      | none => rw [hl] at h; cases h
      | some j => obtain ⟨y, hy, hyx⟩ := ih hl; exact ⟨y, .tail _ hy, hyx⟩

theorem lookup_none_of_not_G {G : VarId → Prop} {env : List VarId} {x : VarId}
    (hG : ∀ y ∈ env, G y) (hx : ∀ y, (y == x) = true → ¬ G y) : envLookupT env x = none := by
  cases hl : envLookupT env x with
  | none => rfl
  | some i =>
    obtain ⟨y, hy, hyx⟩ := envLookupT_mem hl
    exact absurd (hG y hy) (hx y hyx)

theorem lowerTotalExpr_choice {env : List VarId} {l h t : VarId} {X em : Expr} {il : Nat}
    {tX tem : Term} (hil : envLookupT env l = some il)
    (htX : lowerTotalExpr (t :: h :: env) X = some tX) (htem : lowerTotalExpr env em = some tem) :
    lowerTotalExpr env (.Case (.Var l) [.Lam h (.Lam t X), em]) =
      some (.Case (.Var (il + 1)) [.Lam 0 (.Lam 0 tX), tem]) := by
  rw [MIR.lowerTotalExpr_case_of_list, lowerTotalExpr_var, hil]
  simp only [Option.map_some]
  rw [MIR.lowerTotalExprList_cons, MIR.lowerTotalExpr_lam, MIR.lowerTotalExpr_lam, htX]
  simp only [Option.map_some]
  rw [MIR.lowerTotalExprList_cons, htem, MIR.lowerTotalExprList_nil]
  rfl

theorem lowerTotalExpr_case2_some {env : List VarId} {s ne em : Expr} {t : Term}
    (h : lowerTotalExpr env (.Case s [ne, em]) = some t) :
    ∃ ts tne tem, lowerTotalExpr env s = some ts ∧ lowerTotalExpr env ne = some tne ∧
      lowerTotalExpr env em = some tem ∧ t = .Case ts [tne, tem] := by
  obtain ⟨ts, talts, hts, htalts, rfl⟩ := lowerTotalExpr_case_some h
  cases hne : lowerTotalExpr env ne with
  | none =>
    simp [MIR.lowerTotalExprList_cons, hne] at htalts
  | some tne =>
    cases hem : lowerTotalExpr env em with
    | none => simp [MIR.lowerTotalExprList_cons, hne, hem] at htalts
    | some tem =>
      simp [MIR.lowerTotalExprList_cons, MIR.lowerTotalExprList_nil, hne, hem] at htalts
      subst htalts
      exact ⟨ts, tne, tem, hts, rfl, rfl, rfl⟩

theorem choice_case_cons {ρ : CekEnv} {π : Stack} {n : Nat} {vl : CekValue} {b e : Term}
    (hvl : ρ.lookup n = some vl) :
    ∀ hv tv, (∃ c cs, vl = .VCon (.ConstList (c :: cs)) ∧ hv = .VCon c ∧ tv = .VCon (.ConstList cs)) ∨
      (∃ d ds, vl = .VCon (.ConstDataList (d :: ds)) ∧ hv = .VCon (.Data d) ∧
        tv = .VCon (.ConstDataList ds)) →
    Reaches (.compute π ρ (.Case (.Var n) [.Lam 0 (.Lam 0 b), e]))
      (.compute π ((ρ.extend hv).extend tv) b) := by
  intro hv tv h
  rcases h with ⟨c, cs, rfl, rfl, rfl⟩ | ⟨d, ds, rfl, rfl, rfl⟩
  · exact ⟨7, by simp [steps, step, hvl, constToTagAndFields, CekEnv.extend]⟩
  · exact ⟨7, by simp [steps, step, hvl, constToTagAndFields, CekEnv.extend]⟩

theorem choice_case_nil {ρ : CekEnv} {π : Stack} {n : Nat} {vl : CekValue} {a e : Term}
    (hvl : ρ.lookup n = some vl)
    (hnil : vl = .VCon (.ConstList []) ∨ vl = .VCon (.ConstDataList [])) :
    Reaches (.compute π ρ (.Case (.Var n) [a, e])) (.compute π ρ e) := by
  rcases hnil with rfl | rfl
  · exact ⟨3, by simp [steps, step, hvl, constToTagAndFields]⟩
  · exact ⟨3, by simp [steps, step, hvl, constToTagAndFields]⟩

theorem choice_case_pairs {ρ : CekEnv} {π : Stack} {n : Nat} {ps : List (Moist.Plutus.Data × Moist.Plutus.Data)}
    {a e : Term} (hvl : ρ.lookup n = some (.VCon (.ConstPairDataList ps))) :
    Reaches (.compute π ρ (.Case (.Var n) [a, e])) .error :=
  ⟨3, by simp [steps, step, hvl, constToTagAndFields]⟩

theorem forced_builtin_halts (ρ : CekEnv) (b : BuiltinFun) {rest : ExpectedArgs}
    (hb : expectedArgs b = .more .argQ rest) :
    Halts ρ (.Force (.Builtin b)) (.VBuiltin b [] rest) :=
  ⟨4, by simp [steps, step, hb, ExpectedArgs.head, ExpectedArgs.tail]⟩

/-- The list choice rewrite under the facts of the walk. -/
theorem choice_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {s f' ne em ne' em' : Expr}
    {l h t : VarId}
    (hs : FactRel G Produces Γ s (.App f' (.Var l)))
    (hne : FactRel G Produces Γ ne ne') (hem : FactRel G Produces Γ em em')
    (hnull : resolveHead 64 Γ f' = .Force (.Builtin .NullList))
    (hknown : knownList 64 Γ (.Var l) = true)
    (hh : ∀ y, (y == h) = true → ¬ G y) (ht : ∀ y, (y == t) = true → ¬ G y)
    (hht : (h == t) = false)
    (hbig : maxUidExpr ne' < h.uid ∧ maxUidExpr ne' < t.uid)
    (hfresh' : ∀ env, (∀ y ∈ env, G y) → freshIn env ne = true → freshIn env ne' = true) :
    FactRel G Produces Γ (.Case s [ne, em])
      (.Case (.Var l) [.Lam h (.Lam t (replaceListProjections l h t ne')), em']) := by
  intro env t₀ hG hd hfresh hk hsc hlow
  simp only [freshIn, freshInList, Bool.and_eq_true] at hfresh
  obtain ⟨hfs, hfne, hfem, _⟩ := hfresh
  obtain ⟨ts, tne, tem, hts, htne, htem, rfl⟩ := lowerTotalExpr_case2_some hlow
  obtain ⟨ts', hts', hrs⟩ := hs env ts hG hd hfs hk hsc hts
  obtain ⟨tne', htne', hrne⟩ := hne env tne hG hd hfne hk hsc htne
  obtain ⟨tem', htem', hrem⟩ := hem env tem hG hd hfem hk hsc htem
  obtain ⟨tf', tl, htf', htl, rfl⟩ := lowerTotalExpr_app_some hts'
  obtain ⟨il, hil, rfl⟩ := lowerTotalExpr_var_some htl
  have hhenv := lookup_none_of_not_G hG hh
  have htenv : envLookupT (h :: env) t = none := by
    rw [envLookupT_cons_neq h t env hht, lookup_none_of_not_G hG ht]; rfl
  have hfne' := hfresh' env hG hfne
  have hne_h : (freeVars ne').contains h = false := maxUidExpr_fresh _ _ (by omega)
  have hne_t : (freeVars ne').contains t = false := maxUidExpr_fresh _ _ (by omega)
  have hlow_h : lowerTotalExpr (h :: env) ne' = some (renameTerm (shiftRename 1) tne') := by
    rw [MIR.lowerTotalExpr_prepend_unused env h ne' hne_h, htne']; rfl
  have hlow_th : lowerTotalExpr (t :: h :: env) ne' =
      some (renameTerm (shiftRename 1) (renameTerm (shiftRename 1) tne')) := by
    rw [MIR.lowerTotalExpr_prepend_unused (h :: env) t ne' hne_t, hlow_h]; rfl
  -- the facts recorded for the fresh binders
  let Γ'' : List (VarId × Expr) := (t, tailApp l) :: (h, headApp l) :: Γ
  have hdist : EnvDistinct (t :: h :: env) := (hd.cons (by simp [hhenv])).cons (by simp [htenv])
  have hfresh'' : freshIn (t :: h :: env) ne' = true := by
    refine freshIn_avoids ne' hfne' ?_
    intro y hy
    rw [envLookupT_cons] at hy
    split at hy
    · rename_i hty; right; rw [VarId.beq_true_iff] at hty; omega
    · rw [envLookupT_cons] at hy
      simp only [Option.isSome_map] at hy
      split at hy
      · rename_i hhy; right; rw [VarId.beq_true_iff] at hhy; omega
      · left; simpa using hy
  have hlheadApp : lowerTotalExpr env (headApp l) =
      some (.Apply (.Force (.Builtin .HeadList)) (.Var (il + 1))) := by
    simp only [headApp, MIR.lowerTotalExpr_app, MIR.lowerTotalExpr_force, lowerTotalExpr_builtin,
      lowerTotalExpr_var, hil]; rfl
  have hl_h : envLookupT (h :: env) l = some (il + 1) := by
    rw [envLookupT_cons_neq h l env (by
      cases hc : (h == l)
      · rfl
      · rw [envLookupT_congr hc, hil] at hhenv; cases hhenv)]
    rw [hil]; rfl
  have hltailApp : lowerTotalExpr (h :: env) (tailApp l) =
      some (.Apply (.Force (.Builtin .TailList)) (.Var (il + 1 + 1))) := by
    simp only [tailApp, MIR.lowerTotalExpr_app, MIR.lowerTotalExpr_force, lowerTotalExpr_builtin,
      lowerTotalExpr_var, hl_h]; rfl
  have hk'' : KeysBound Γ'' (t :: h :: env) := by
    intro entry hmem
    simp only [Γ'', List.mem_cons] at hmem
    rcases hmem with rfl | rfl | hmem
    · simp [envLookupT_cons, varId_beq_self]
    · rw [envLookupT_cons]; split
      · rfl
      · simp [envLookupT_cons, varId_beq_self]
    · exact (hk.cons h).cons t entry hmem
  have hs'' : FactsScoped Γ'' (t :: h :: env) :=
    (hsc.push (x := h) (by simp [hlheadApp])).push (by simp [hltailApp])
  have hfh : Γ''.find? (fun e => e.1 == h) = some (h, headApp l) := by
    simp [Γ'', List.find?_cons, varId_beq_self, show (t == h) = false from by
      cases hc : (t == h)
      · rfl
      · exact absurd (varId_beq_symm hc) (by simp [hht])]
  have hft : Γ''.find? (fun e => e.1 == t) = some (t, tailApp l) := by
    simp [Γ'', List.find?_cons, varId_beq_self]
  obtain ⟨tX, htX, hrX⟩ := replaceListProjections_factRel l h t (h, headApp l) (t, tailApp l) rfl rfl
    ne' Γ'' hbig hfh hft (t :: h :: env) _ (fun _ _ => trivial) hdist hfresh'' hk'' hs'' hlow_th
  refine ⟨_, lowerTotalExpr_choice hil htX htem', ?_⟩
  have hlistrel : ListRel (FactRefines env.length (FactsHold Produces Γ env)) [tne, tem] [tne', tem'] :=
    ⟨hrne, hrem, trivial⟩
  refine FactRefines.trans (factRefines_case hrs hlistrel
    (MIR.lowerTotalExpr_closedAt hts') (lowerTotalExprList_closedAtList (by
      rw [MIR.lowerTotalExprList_cons, htne, MIR.lowerTotalExprList_cons, htem,
        MIR.lowerTotalExprList_nil]; rfl))) ?_
  intro ρ π henv hlen hπ hF
  have hil_lt := envLookupT_bound env l il hil
  obtain ⟨vl, hvl, _⟩ := envWellFormed_lookup env.length henv (n := il + 1) (by omega) (by omega)
  have hlist : ListValue vl :=
    knownList_sound produces_hP 64 Γ (.Var l) hknown hF hd
      (by rw [lowerTotalExpr_var, hil]; rfl) (halts_var_of_lookup hvl)
  have hfnull := resolveHead_forced_halts 64 Γ f' hnull rfl hF hd htf'
  have nonempty : ∀ hv tv : CekValue,
      ((∃ c cs, vl = .VCon (.ConstList (c :: cs)) ∧ hv = .VCon c ∧ tv = .VCon (.ConstList cs)) ∨
        (∃ d ds, vl = .VCon (.ConstDataList (d :: ds)) ∧ hv = .VCon (.Data d) ∧
          tv = .VCon (.ConstDataList ds))) →
      ObsRefines (.compute π ρ (.Case (.Apply tf' (.Var (il + 1))) [tne', tem']))
        (.compute π ρ (.Case (.Var (il + 1)) [.Lam 0 (.Lam 0 tX), tem'])) := by
    intro hv tv hshape
    have hnull_eval : evalBuiltin .NullList [vl] = some (.VCon (.Bool false)) := by
      rcases hshape with ⟨c, cs, rfl, rfl, rfl⟩ | ⟨d, ds, rfl, rfl, rfl⟩ <;> rfl
    have hhead_eval : evalBuiltin .HeadList [vl] = some hv := by
      rcases hshape with ⟨c, cs, rfl, rfl, rfl⟩ | ⟨d, ds, rfl, rfl, rfl⟩ <;> rfl
    have htail_eval : evalBuiltin .TailList [vl] = some tv := by
      rcases hshape with ⟨c, cs, rfl, rfl, rfl⟩ | ⟨d, ds, rfl, rfl, rfl⟩ <;> rfl
    have hvcon : ValueWellFormed hv ∧ ValueWellFormed tv := by
      rcases hshape with ⟨c, cs, rfl, rfl, rfl⟩ | ⟨d, ds, rfl, rfl, rfl⟩
      · exact ⟨.vcon _, .vcon _⟩
      · exact ⟨.vcon _, .vcon _⟩
    have hscrut := builtin_app_halts hfnull hvl hnull_eval
    have hhead_halts : Halts ρ (.Apply (.Force (.Builtin .HeadList)) (.Var (il + 1))) hv :=
      builtin_app_halts (forced_builtin_halts ρ .HeadList rfl) hvl hhead_eval
    have htail_halts : Halts (ρ.extend hv) (.Apply (.Force (.Builtin .TailList)) (.Var (il + 1 + 1))) tv :=
      builtin_app_halts (forced_builtin_halts _ .TailList rfl) (by simpa using hvl) htail_eval
    have henv₁ := envWellFormed_extend env.length henv hlen hvcon.1
    have hlen₁ : env.length + 1 ≤ (ρ.extend hv).length := by
      simp [CekEnv.extend, CekEnv.length]; omega
    have henv₂ := envWellFormed_extend (env.length + 1) henv₁ hlen₁ hvcon.2
    have hlen₂ : env.length + 1 + 1 ≤ ((ρ.extend hv).extend tv).length := by
      simp [CekEnv.extend, CekEnv.length]; omega
    have hF'' : FactsHold Produces Γ'' (t :: h :: env) ((ρ.extend hv).extend tv) :=
      (hF.push ⟨_, hlheadApp, hhead_halts⟩).push ⟨_, hltailApp, htail_halts⟩
    have closedNe := MIR.lowerTotalExpr_closedAt htne'
    have closedNe₁ := MIR.lowerTotalExpr_closedAt hlow_h
    refine obsRefines_of_reaches (case_bool_steps hscrut) (choice_case_cons hvl hv tv hshape) ?_
    simp only [Bool.false_eq_true, if_false]
    refine obsRefines_trans (obsEq_shift hv henv hπ closedNe).1 ?_
    refine obsRefines_trans (obsEq_shift tv henv₁ hπ (by simpa using closedNe₁)).1 ?_
    exact hrX _ π henv₂ (by simpa using hlen₂) hπ hF''
  cases vl with
  | VCon c =>
    cases c with
    | ConstList xs =>
      cases xs with
      | nil =>
        have hscrut := builtin_app_halts hfnull hvl (show evalBuiltin .NullList [.VCon (.ConstList [])] =
          some (.VCon (.Bool true)) from rfl)
        exact obsRefines_of_reaches (case_bool_steps hscrut) (choice_case_nil hvl (.inl rfl))
          (obsRefines_refl _)
      | cons c cs => exact nonempty _ _ (.inl ⟨c, cs, rfl, rfl, rfl⟩)
    | ConstDataList xs =>
      cases xs with
      | nil =>
        have hscrut := builtin_app_halts hfnull hvl (show evalBuiltin .NullList [.VCon (.ConstDataList [])] =
          some (.VCon (.Bool true)) from rfl)
        exact obsRefines_of_reaches (case_bool_steps hscrut) (choice_case_nil hvl (.inr rfl))
          (obsRefines_refl _)
      | cons d ds => exact nonempty _ _ (.inr ⟨d, ds, rfl, rfl, rfl⟩)
    | ConstPairDataList ps =>
      exact obsRefines_of_errors (case_errs_of_scrutinee (builtin_app_errs hfnull hvl rfl))
        (choice_case_pairs hvl)
    | _ => exact absurd hlist id
  | _ => exact absurd hlist id

/-! ## Freshness of the walk -/

theorem beq_force_nullList {x : Expr} (h : (x == Expr.Force (.Builtin .NullList)) = true) :
    x = .Force (.Builtin .NullList) := by
  cases x with
  | Force e =>
    cases e with
    | Builtin b' =>
      have : (b' == BuiltinFun.NullList) = true := h
      cases b' <;> first | rfl | cases this
    | _ => cases h
  | _ => cases h

theorem freshInList_attach_map {avoid : List VarId} (xs : List Expr) (f : Expr → Expr)
    (h : ∀ x ∈ xs, freshIn avoid (f x) = freshIn avoid x) :
    freshInList avoid (xs.attach.map fun ⟨x, _⟩ => f x) = freshInList avoid xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.attach_cons, List.map_cons, List.map_map, freshInList]
    rw [h x (.head _)]
    congr 1
    rw [← ih (fun y hy => h y (.tail _ hy))]
    simp [Function.comp_def]

theorem freshInLet_map (f : Expr → Expr) :
    ∀ (bs : List (VarId × Expr × Bool)) (body : Expr) (avoid : List VarId),
      (∀ b ∈ bs, ∀ avoid, freshIn avoid (f b.2.1) = freshIn avoid b.2.1) →
      (∀ avoid, freshIn avoid (f body) = freshIn avoid body) →
      freshInLet avoid (bs.map fun (y, rhs, er) => (y, f rhs, er)) (f body) = freshInLet avoid bs body
  | [], body, avoid, _, hbody => by simp [freshInLet, hbody]
  | (y, r, er) :: rest, body, avoid, hbs, hbody => by
    simp only [List.map_cons, freshInLet]
    rw [hbs (y, r, er) (.head _), freshInLet_map f rest body (y :: avoid)
      (fun b hb => hbs b (.tail _ hb)) hbody]

theorem freshIn_replaceListProjections (l h t : VarId) (X : Expr) :
    ∀ avoid, freshIn avoid (replaceListProjections l h t X) = freshIn avoid X := by
  intro avoid
  unfold replaceListProjections
  split
  · split <;> simp [freshIn]
  · split <;> simp [freshIn]
  · rename_i f a _ _
    simp only [freshIn, freshIn_replaceListProjections l h t f, freshIn_replaceListProjections l h t a]
  · rename_i y b
    simp only [freshIn, freshIn_replaceListProjections l h t b]
  · rename_i y b
    simp only [freshIn, freshIn_replaceListProjections l h t b]
  · rename_i b
    simp only [freshIn, freshIn_replaceListProjections l h t b]
  · rename_i b
    simp only [freshIn, freshIn_replaceListProjections l h t b]
  · rename_i tag fields
    simp only [freshIn]
    exact freshInList_attach_map fields _ fun x _ => freshIn_replaceListProjections l h t x avoid
  · rename_i scrutinee alternatives
    simp only [freshIn, freshIn_replaceListProjections l h t scrutinee]
    rw [freshInList_attach_map alternatives _ fun x _ => freshIn_replaceListProjections l h t x avoid]
  · rename_i bindings body
    simp only [freshIn]
    rw [binds_attach_map]
    exact freshInLet_map _ bindings body avoid
      (fun b _ avoid => freshIn_replaceListProjections l h t b.2.1 avoid)
      (fun avoid => freshIn_replaceListProjections l h t body avoid)
  all_goals rfl
termination_by exprSize X
decreasing_by
  all_goals first
    | (subst_vars; simp only [exprSize, exprSizeBinds]; omega)
    | (subst_vars; have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)
    | (subst_vars; have := exprSizeBinds_mem_lt (by assumption); simp only [exprSize]; omega)

/-- Names that cannot be binders generated above `base`. -/
def GenSafe (base : Nat) (y : VarId) : Prop := y.uid < base ∨ y.origin ≠ .gen

theorem not_genSafe {base : Nat} {x : VarId} (hx : base ≤ x.uid) (hgen : x.origin = .gen) :
    ∀ y, (y == x) = true → ¬ GenSafe base y := by
  intro y hy hsafe
  rw [VarId.beq_true_iff] at hy
  rcases hsafe with h | h
  · omega
  · exact h (hy.1.trans hgen)

theorem freshIn_cons_of_big {env : List VarId} {X : Expr} {y : VarId} (hX : freshIn env X = true)
    (hy : maxUidExpr X < y.uid) : freshIn (y :: env) X = true := by
  refine freshIn_avoids X hX ?_
  intro z hz
  rw [envLookupT_cons] at hz
  split at hz
  · rename_i hyz; right; rw [VarId.beq_true_iff] at hyz; omega
  · left; simpa using hz

theorem listChoiceRewrite_fresh {base : Nat} {Γ : List (VarId × Expr)} {result : Expr}
    {env : List VarId} (hG : ∀ y ∈ env, GenSafe base y) (h : freshIn env result = true) :
    freshIn env (listChoiceRewrite base Γ result) = true := by
  unfold listChoiceRewrite
  split
  · rename_i function l ne em
    split
    · simp only [freshIn, freshInList, Bool.and_eq_true] at h
      obtain ⟨_, hne, hem, _⟩ := h
      have hbig : maxUidExpr ne < max base (maxUidExpr (.Case (.App function (.Var l)) [ne, em]) + 1) := by
        simp only [maxUidExpr, maxUidExprList]; omega
      have hhenv := lookup_none_of_not_G hG (not_genSafe (x :=
        { uid := max base (maxUidExpr (.Case (.App function (.Var l)) [ne, em]) + 1), origin := .gen,
          hint := "head" }) (Nat.le_max_left _ _) rfl)
      have htenv := lookup_none_of_not_G hG (not_genSafe (x :=
        { uid := max base (maxUidExpr (.Case (.App function (.Var l)) [ne, em]) + 1) + 1, origin := .gen,
          hint := "tail" }) (by simp; omega) rfl)
      simp only [freshIn, freshInList, Bool.and_eq_true, Bool.and_true]
      refine ⟨trivial, ⟨by simp [hhenv], by
          rw [envLookupT_cons_neq _ _ _ (beq_false_of_uid_lt (by simp)), htenv]; rfl, ?_⟩, hem⟩
      rw [freshIn_replaceListProjections]
      exact freshIn_cons_of_big (freshIn_cons_of_big hne hbig) (by simp; omega)
    · exact h
  · exact h

theorem listChoiceWalk_fresh (base : Nat) (e : Expr) (Γ : List (VarId × Expr)) (env : List VarId)
    (hG : ∀ y ∈ env, GenSafe base y) (hmax : maxUidExpr e < base) (hf : freshIn env e = true) :
    freshIn env (listChoiceWalk base Γ e) = true := by
  match e with
  | .Let [] body =>
    rw [listChoiceWalk]
    simp only [maxUidExpr, maxUidExprBinds] at hmax
    rw [freshIn_let_nil] at hf
    exact listChoiceWalk_fresh base body Γ env hG (by omega) hf
  | .Let ((x, r, er) :: rest) body =>
    rw [listChoiceWalk]
    simp only [maxUidExpr, maxUidExprBinds] at hmax
    rw [freshIn_let_cons, freshIn_let_single] at hf
    simp only [Bool.and_eq_true] at hf
    rw [freshIn_let_single]
    simp only [Bool.and_eq_true]
    refine ⟨⟨listChoiceWalk_fresh base r Γ env hG (by omega) hf.1.1, hf.1.2⟩, ?_⟩
    exact listChoiceWalk_fresh base (.Let rest body) _ (x :: env)
      (allG_cons (.inl (by omega)) hG) (by simp only [maxUidExpr]; omega) hf.2
  | .Lam x b =>
    rw [listChoiceWalk]
    apply listChoiceRewrite_fresh hG
    simp only [maxUidExpr] at hmax
    simp only [freshIn, Bool.and_eq_true] at hf ⊢
    exact ⟨hf.1, listChoiceWalk_fresh base b Γ (x :: env) (allG_cons (.inl (by omega)) hG) (by omega) hf.2⟩
  | .Fix x b =>
    rw [listChoiceWalk]
    apply listChoiceRewrite_fresh hG
    simp only [maxUidExpr] at hmax
    simp only [freshIn, Bool.and_eq_true] at hf ⊢
    exact ⟨hf.1, listChoiceWalk_fresh base b Γ (x :: env) (allG_cons (.inl (by omega)) hG) (by omega) hf.2⟩
  | .App f a =>
    rw [listChoiceWalk]
    apply listChoiceRewrite_fresh hG
    simp only [maxUidExpr] at hmax
    simp only [freshIn, Bool.and_eq_true] at hf ⊢
    exact ⟨listChoiceWalk_fresh base f Γ env hG (by omega) hf.1,
      listChoiceWalk_fresh base a Γ env hG (by omega) hf.2⟩
  | .Force b =>
    rw [listChoiceWalk]
    apply listChoiceRewrite_fresh hG
    simp only [maxUidExpr] at hmax
    simp only [freshIn] at hf ⊢
    exact listChoiceWalk_fresh base b Γ env hG (by omega) hf
  | .Delay b =>
    rw [listChoiceWalk]
    apply listChoiceRewrite_fresh hG
    simp only [maxUidExpr] at hmax
    simp only [freshIn] at hf ⊢
    exact listChoiceWalk_fresh base b Γ env hG (by omega) hf
  | .Constr tag fields =>
    rw [listChoiceWalk]
    apply listChoiceRewrite_fresh hG
    simp only [maxUidExpr] at hmax
    simp only [freshIn] at hf ⊢
    rw [freshInList_iff] at hf ⊢
    intro x hx
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    have := maxUidExpr_le_maxUidExprList_of_mem hc
    exact listChoiceWalk_fresh base c Γ env hG (by omega) (hf c hc)
  | .Case scrutinee alternatives =>
    rw [listChoiceWalk]
    apply listChoiceRewrite_fresh hG
    simp only [maxUidExpr] at hmax
    simp only [freshIn, Bool.and_eq_true] at hf ⊢
    refine ⟨listChoiceWalk_fresh base scrutinee Γ env hG (by omega) hf.1, ?_⟩
    have hf2 := hf.2
    rw [freshInList_iff] at hf2 ⊢
    intro x hx
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    have := maxUidExpr_le_maxUidExprList_of_mem hc
    exact listChoiceWalk_fresh base c Γ env hG (by omega) (hf2 c hc)
  | .Var _ | .Lit _ | .Builtin _ | .Error =>
    rw [listChoiceWalk]; exact listChoiceRewrite_fresh hG hf
termination_by exprSize e
decreasing_by
  all_goals first
    | (simp only [exprSize, exprSizeBinds]; omega)
    | (simp only [exprSize, exprSizeBinds]; have := exprSize_pos r; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)

/-! ## The walk -/

theorem attach_map_eq_map (xs : List Expr) (f : Expr → Expr) :
    (xs.attach.map fun ⟨x, _⟩ => f x) = xs.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.attach_cons, List.map_cons, List.map_map]
    congr 1

theorem listChoiceWalk_factRel (base : Nat) (e : Expr) (Γ : List (VarId × Expr))
    (hmax : maxUidExpr e < base) :
    FactRel (GenSafe base) Produces Γ e (listChoiceWalk base Γ e) := by
  match e with
  | .Let [] body =>
    rw [listChoiceWalk]
    simp only [maxUidExpr, maxUidExprBinds] at hmax
    exact (listChoiceWalk_factRel base body Γ (by omega)).congr_left
      (fun env => lowerTotalExpr_let_nil env body) (fun avoid => freshIn_let_nil avoid body)
  | .Let ((x, r, er) :: rest) body =>
    rw [listChoiceWalk]
    simp only [maxUidExpr, maxUidExprBinds] at hmax
    exact (FactRel.let_single (listChoiceWalk base Γ r) (.inl (by omega)) (.inr rfl)
      (listChoiceWalk_factRel base r Γ (by omega))
      (listChoiceWalk_factRel base (.Let rest body) _ (by simp only [maxUidExpr]; omega))
      (fun _ _ _ _ _ hp => hp)).congr_left (fun env => lowerTotalExpr_let_cons env _ _ _)
      (fun avoid => freshIn_let_cons avoid _ _ _)
  | .Lam x b =>
    rw [listChoiceWalk]
    simp only [maxUidExpr] at hmax
    exact (listChoiceWalk_factRel base b Γ (by omega)).lam (.inl (by omega))
  | .Fix f b =>
    rw [listChoiceWalk]
    simp only [maxUidExpr] at hmax
    cases b with
    | Lam x inner =>
      rw [listChoiceWalk]
      simp only [maxUidExpr] at hmax
      exact (listChoiceWalk_factRel base inner Γ (by omega)).fix_lam (.inl (by omega))
        (.inl (by omega)) (fun y hy => .inr (by rw [hy]; simp))
    | _ =>
      intro env t _ _ _ _ _ hlow
      rw [MIR.lowerTotalExpr_fix_nonlam_none env f _ (by intros; simp)] at hlow
      cases hlow
  | .App f a =>
    rw [listChoiceWalk]
    simp only [maxUidExpr] at hmax
    exact (listChoiceWalk_factRel base f Γ (by omega)).app (listChoiceWalk_factRel base a Γ (by omega))
  | .Force b =>
    rw [listChoiceWalk]
    simp only [maxUidExpr] at hmax
    exact (listChoiceWalk_factRel base b Γ (by omega)).force
  | .Delay b =>
    rw [listChoiceWalk]
    simp only [maxUidExpr] at hmax
    exact (listChoiceWalk_factRel base b Γ (by omega)).delay
  | .Constr tag fields =>
    rw [listChoiceWalk]
    simp only [maxUidExpr] at hmax
    exact FactRel.constr (listRel_attach_map fields _ fun c hc => listChoiceWalk_factRel base c Γ
      (by have := maxUidExpr_le_maxUidExprList_of_mem hc; omega))
  | .Case scrutinee alternatives =>
    rw [listChoiceWalk]
    simp only [maxUidExpr] at hmax
    have ihs := listChoiceWalk_factRel base scrutinee Γ (by omega)
    have ihalts : ∀ c ∈ alternatives, FactRel (GenSafe base) Produces Γ c (listChoiceWalk base Γ c) :=
      fun c hc => listChoiceWalk_factRel base c Γ
        (by have := maxUidExpr_le_maxUidExprList_of_mem hc; omega)
    have congruence := FactRel.case ihs (listRel_attach_map alternatives _ ihalts)
    unfold listChoiceRewrite
    split
    · rename_i function l ne' em' hresult
      have hresult' := hresult
      injection hresult with hs heqalts
      rw [attach_map_eq_map] at heqalts
      match alternatives, heqalts, ihalts, hmax, hresult', congruence with
      | [ne, em], heqalts, ihalts, hmax, hresult', congruence =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq] at heqalts
        obtain ⟨hne, hem, -⟩ := heqalts
        simp only [maxUidExprList] at hmax
        split
        · rename_i hcond
          simp only [Bool.and_eq_true] at hcond
          have hnull := beq_force_nullList hcond.1
          rw [hs] at ihs
          have ihne := ihalts ne (.head _)
          have ihem := ihalts em (.tail _ (.head _))
          rw [hne] at ihne
          rw [hem] at ihem
          rw [hresult']
          refine choice_factRel ihs ihne ihem hnull hcond.2 (not_genSafe (Nat.le_max_left _ _) rfl)
            (not_genSafe (by simp; omega) rfl) (beq_false_of_uid_lt (by simp))
            ⟨by simp only [maxUidExpr, maxUidExprList]; omega, by simp only [maxUidExpr, maxUidExprList]; omega⟩
            ?_
          intro env hG hf
          rw [← hne]
          exact listChoiceWalk_fresh base ne Γ env hG (by omega) hf
        · exact congruence
    · exact congruence
  | .Var _ | .Lit _ | .Builtin _ | .Error => rw [listChoiceWalk]; exact FactRel.refl _ _ _ _
termination_by exprSize e
decreasing_by
  all_goals first
    | (subst_vars; simp only [exprSize, exprSizeBinds]; omega)
    | (simp only [exprSize, exprSizeBinds]; have := exprSize_pos r; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)

end Moist.Verified.ShapeFacts

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced Moist.Verified.ShapeFacts

/-- List choice fusion refines its input. -/
theorem fuseListChoices_refines (e : Expr) : MIRCtxRefines e (fuseListChoices e) := by
  unfold fuseListChoices
  simp only
  split
  · rename_i hws
    refine mirCtxRefines_trans (Hygiene.uniqueOptimizationBinders_refines e)
      (mirCtxRefines_trans ?_ (Hygiene.uniqueOptimizationBinders_refines _))
    exact mirCtxRefines_of_factRel hws
      (fun y hy => .inl (by have := freeVars_uid_lt hy; omega))
      (fun y hy => .inr (by rw [hy]; simp))
      (listChoiceWalk_factRel _ _ [] (by omega))
  · exact Hygiene.uniqueOptimizationBinders_refines e

end Moist.Verified.MIR
