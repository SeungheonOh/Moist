import Moist.Verified.ShapeFacts.Unary
import Moist.Verified.ShapeFacts.Top
import Moist.Verified.HygieneSoundness

/-! # List destructor fusion

`let h = headList l; let t = tailList l; body` becomes
`case l [λh t. body, error]` when `l` is known to be a list. On a non-empty
list both forms bind the head and the tail; on an empty list, or a list the
model cannot destructure, both fail.
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines

theorem obsRefines_of_errors {s₁ s₂ : State} (h₁ : Reaches s₁ .error) (h₂ : Reaches s₂ .error) :
    ObsRefines s₁ s₂ :=
  ⟨fun ⟨_, hv⟩ => absurd (halt_not_error hv h₁) id, fun _ => h₂⟩

theorem let_errors {ρ : CekEnv} {π : Stack} {r b : Term} (h : Errs ρ r) :
    Reaches (.compute π ρ (.Apply (.Lam 0 b) r)) .error :=
  reaches_trans (reaches_of_steps 3 rfl) (errs_on_stack h _)

theorem let_steps {ρ : CekEnv} {π : Stack} {r b : Term} {v : CekValue} (h : Halts ρ r v) :
    Reaches (.compute π ρ (.Apply (.Lam 0 b) r)) (.compute π (ρ.extend v) b) :=
  reaches_trans (reaches_of_steps 3 rfl) (reaches_trans (halts_on_stack h _) (reaches_of_steps 1 rfl))

/-- The fused form on a list value. -/
theorem fused_case_steps {ρ : CekEnv} {π : Stack} {n : Nat} {vl : CekValue} {b : Term}
    (hvl : ρ.lookup n = some vl) :
    ∀ hv tv, (∃ c cs, vl = .VCon (.ConstList (c :: cs)) ∧ hv = .VCon c ∧ tv = .VCon (.ConstList cs)) ∨
      (∃ d ds, vl = .VCon (.ConstDataList (d :: ds)) ∧ hv = .VCon (.Data d) ∧
        tv = .VCon (.ConstDataList ds)) →
    Reaches (.compute π ρ (.Case (.Var n) [.Lam 0 (.Lam 0 b), .Error]))
      (.compute π ((ρ.extend hv).extend tv) b) := by
  intro hv tv h
  rcases h with ⟨c, cs, rfl, rfl, rfl⟩ | ⟨d, ds, rfl, rfl, rfl⟩
  · exact ⟨7, by simp [steps, step, hvl, constToTagAndFields, CekEnv.extend]⟩
  · exact ⟨7, by simp [steps, step, hvl, constToTagAndFields, CekEnv.extend]⟩

theorem fused_case_errors {ρ : CekEnv} {π : Stack} {n : Nat} {vl : CekValue} {b : Term}
    (hvl : ρ.lookup n = some vl)
    (hempty : vl = .VCon (.ConstList []) ∨ vl = .VCon (.ConstDataList []) ∨
      ∃ ps, vl = .VCon (.ConstPairDataList ps)) :
    Reaches (.compute π ρ (.Case (.Var n) [.Lam 0 (.Lam 0 b), .Error])) .error := by
  rcases hempty with rfl | rfl | ⟨ps, rfl⟩
  · exact ⟨5, by simp [steps, step, hvl, constToTagAndFields]⟩
  · exact ⟨5, by simp [steps, step, hvl, constToTagAndFields]⟩
  · exact ⟨4, by simp [steps, step, hvl, constToTagAndFields]⟩

theorem produces_hP : ∀ (env : List VarId) (ρ : CekEnv) (rhs : Expr) (v : CekValue),
    Produces env ρ rhs v → Produces env ρ rhs v := fun _ _ _ _ h => h

theorem lowerTotalExpr_fused {env : List VarId} {l h t : VarId} {B' : Expr} {il : Nat} {tB' : Term}
    (hil : envLookupT env l = some il) (htB' : lowerTotalExpr (t :: h :: env) B' = some tB') :
    lowerTotalExpr env (.Case (.Var l) [.Lam h (.Lam t B'), .Error]) =
      some (.Case (.Var (il + 1)) [.Lam 0 (.Lam 0 tB'), .Error]) := by
  rw [MIR.lowerTotalExpr_case_of_list, lowerTotalExpr_var, hil]
  simp only [Option.map_some]
  rw [MIR.lowerTotalExprList_cons, MIR.lowerTotalExpr_lam, MIR.lowerTotalExpr_lam, htB']
  simp only [Option.map_some]
  rw [MIR.lowerTotalExprList_cons, lowerTotalExpr_error, MIR.lowerTotalExprList_nil]
  rfl

theorem fusion_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {h t : VarId}
    {hr tr B B' : Expr} {he te : Bool} {l l' : VarId} (hGh : G h) (hGt : G t)
    (hhead : resolveHead 64 Γ hr = .App (.Force (.Builtin .HeadList)) (.Var l))
    (htail : resolveHead 64 Γ tr = .App (.Force (.Builtin .TailList)) (.Var l'))
    (hl : (l == l') = true) (hknown : knownList 64 Γ (.Var l) = true)
    (hB : FactRel G Produces ((t, tr) :: (h, hr) :: Γ) B B') :
    FactRel G Produces Γ (.Let [(h, hr, he)] (.Let [(t, tr, te)] B))
      (.Case (.Var l) [.Lam h (.Lam t B'), .Error]) := by
  intro env t₀ hG hd hfresh hk hs hlow
  rw [freshIn_let_single] at hfresh
  simp only [Bool.and_eq_true] at hfresh
  obtain ⟨⟨hfhr, hh⟩, hfrest⟩ := hfresh
  rw [freshIn_let_single] at hfrest
  simp only [Bool.and_eq_true] at hfrest
  obtain ⟨⟨hftr, ht⟩, hfB⟩ := hfrest
  obtain ⟨thr, tX, hthr, htX, rfl⟩ := lowerTotalExpr_let_single_some hlow
  obtain ⟨ttr, tB, httr, htB, rfl⟩ := lowerTotalExpr_let_single_some htX
  have hlb := resolveHead_app_var_bound 64 Γ hr hhead hs hd (by simp [hthr])
  obtain ⟨il, hil⟩ : ∃ il, envLookupT env l = some il := Option.isSome_iff_exists.mp hlb
  have hnh := find?_none_of_unbound hk hh
  have hd₁ := hd.cons hh
  have hk₁ := hk.cons h
  have hnt := find?_none_of_unbound hk₁ ht
  have hd₂ := hd₁.cons ht
  have hk₂ : KeysBound ((t, tr) :: (h, hr) :: Γ) (t :: h :: env) := by
    intro entry hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | rfl | hmem
    · simp [envLookupT_cons, varId_beq_self]
    · rw [envLookupT_cons]; split
      · rfl
      · simp [envLookupT_cons, varId_beq_self]
    · exact hk₁.cons t entry hmem
  have hs₂ : FactsScoped ((t, tr) :: (h, hr) :: Γ) (t :: h :: env) :=
    (hs.push (x := h) (by simp [hthr])).push (by simp [httr])
  obtain ⟨tB', htB', hrB⟩ := hB (t :: h :: env) tB (allG_cons hGt (allG_cons hGh hG)) hd₂ hfB hk₂ hs₂ htB
  refine ⟨_, lowerTotalExpr_fused hil htB', ?_⟩
  intro ρ π henv hlen hπ hF
  have hil_lt := envLookupT_bound env l il hil
  obtain ⟨vl, hvl, hvlwf⟩ := envWellFormed_lookup env.length henv (n := il + 1) (by omega) (by omega)
  have hlist : ListValue vl :=
    knownList_sound produces_hP 64 Γ (.Var l) hknown hF hd
      (by rw [lowerTotalExpr_var, hil]; rfl) (halts_var_of_lookup hvl)
  obtain ⟨hiffH, herrH⟩ := resolveHead_unary 64 Γ hr hhead rfl hF hd hthr hil hvl
  have hl' : envLookupT (h :: env) l' = some (il + 1) := by
    rw [← envLookupT_congr hl, envLookupT_cons]
    have hhl : (h == l) = false := by
      cases hc : (h == l)
      · rfl
      · rw [envLookupT_congr hc] at hh; simp [hil] at hh
    simp [hhl, hil]
  have nonempty : ∀ hv tv : CekValue,
      ((∃ c cs, vl = .VCon (.ConstList (c :: cs)) ∧ hv = .VCon c ∧ tv = .VCon (.ConstList cs)) ∨
        (∃ d ds, vl = .VCon (.ConstDataList (d :: ds)) ∧ hv = .VCon (.Data d) ∧
          tv = .VCon (.ConstDataList ds))) →
      ObsRefines (.compute π ρ (.Apply (.Lam 0 (.Apply (.Lam 0 tB) ttr)) thr))
        (.compute π ρ (.Case (.Var (il + 1)) [.Lam 0 (.Lam 0 tB'), .Error])) := by
    intro hv tv hshape
    have hhead_eval : evalBuiltin .HeadList [vl] = some hv := by
      rcases hshape with ⟨c, cs, rfl, rfl, rfl⟩ | ⟨d, ds, rfl, rfl, rfl⟩ <;> rfl
    have htail_eval : evalBuiltin .TailList [vl] = some tv := by
      rcases hshape with ⟨c, cs, rfl, rfl, rfl⟩ | ⟨d, ds, rfl, rfl, rfl⟩ <;> rfl
    have hthr_halts : Halts ρ thr hv := (hiffH hv).mpr hhead_eval
    have hvwf := halts_wellFormed henv hlen (MIR.lowerTotalExpr_closedAt hthr) hthr_halts
    have hF₁ : FactsHold Produces Γ (h :: env) (ρ.extend hv) := FactsHold.extend hv hF hnh
    obtain ⟨hiffT, _⟩ := resolveHead_unary 64 Γ tr htail rfl hF₁ hd₁ httr hl' (by simpa using hvl)
    have httr_halts : Halts (ρ.extend hv) ttr tv := (hiffT tv).mpr htail_eval
    have henv₁ := envWellFormed_extend env.length henv hlen hvwf
    have hlen₁ : env.length + 1 ≤ (ρ.extend hv).length := by
      simp [CekEnv.extend, CekEnv.length]; omega
    have htvwf := halts_wellFormed henv₁ hlen₁ (by simpa using MIR.lowerTotalExpr_closedAt httr) httr_halts
    have hF₂ : FactsHold Produces ((t, tr) :: (h, hr) :: Γ) (t :: h :: env) ((ρ.extend hv).extend tv) :=
      (hF.push ⟨thr, hthr, hthr_halts⟩).push ⟨ttr, httr, httr_halts⟩
    refine obsRefines_of_reaches (reaches_trans (let_steps hthr_halts) (let_steps httr_halts))
      (fused_case_steps hvl hv tv hshape) ?_
    exact hrB _ π (envWellFormed_extend (env.length + 1) henv₁ hlen₁ htvwf)
      (by simp [CekEnv.extend, CekEnv.length]; omega) hπ hF₂
  have empty : (vl = .VCon (.ConstList []) ∨ vl = .VCon (.ConstDataList []) ∨
      ∃ ps, vl = .VCon (.ConstPairDataList ps)) →
      ObsRefines (.compute π ρ (.Apply (.Lam 0 (.Apply (.Lam 0 tB) ttr)) thr))
        (.compute π ρ (.Case (.Var (il + 1)) [.Lam 0 (.Lam 0 tB'), .Error])) := by
    intro hshape
    have hnone : evalBuiltin .HeadList [vl] = none := by
      rcases hshape with rfl | rfl | ⟨ps, rfl⟩ <;> rfl
    exact obsRefines_of_errors (let_errors (herrH hnone)) (fused_case_errors hvl hshape)
  cases vl with
  | VCon c =>
    cases c with
    | ConstList xs =>
      cases xs with
      | nil => exact empty (.inl rfl)
      | cons c cs => exact nonempty _ _ (.inl ⟨c, cs, rfl, rfl, rfl⟩)
    | ConstDataList xs =>
      cases xs with
      | nil => exact empty (.inr (.inl rfl))
      | cons d ds => exact nonempty _ _ (.inr ⟨d, ds, rfl, rfl, rfl⟩)
    | ConstPairDataList ps => exact empty (.inr (.inr ⟨ps, rfl⟩))
    | _ => exact absurd hlist id
  | _ => exact absurd hlist id

/-! ## Flattened bindings -/

theorem lowerTotalExpr_let_append : ∀ (bs more : List (VarId × Expr × Bool)) (s : Expr)
    (env : List VarId),
    lowerTotalExpr env (.Let (bs ++ more) s) = lowerTotalExpr env (.Let bs (.Let more s))
  | [], more, s, env => by rw [List.nil_append, lowerTotalExpr_let_nil]
  | (x, r, er) :: bs, more, s, env => by
    rw [List.cons_append, lowerTotalExpr_let_cons env (x, r, er) (bs ++ more),
      lowerTotalExpr_let_cons env (x, r, er) bs,
      lowerTotalExpr_let_single, lowerTotalExpr_let_single, lowerTotalExpr_let_append bs more s]

theorem freshIn_let_append : ∀ (bs more : List (VarId × Expr × Bool)) (s : Expr)
    (avoid : List VarId),
    freshIn avoid (.Let (bs ++ more) s) = freshIn avoid (.Let bs (.Let more s))
  | [], more, s, avoid => by rw [List.nil_append, freshIn_let_nil]
  | (x, r, er) :: bs, more, s, avoid => by
    rw [List.cons_append, freshIn_let_cons avoid (x, r, er) (bs ++ more),
      freshIn_let_cons avoid (x, r, er) bs, freshIn_let_single, freshIn_let_single,
      freshIn_let_append bs more s]

theorem flattenBindings_lower (bs : List (VarId × Expr × Bool)) (body : Expr) (env : List VarId) :
    lowerTotalExpr env (.Let (flattenBindings bs body).1 (flattenBindings bs body).2) =
      lowerTotalExpr env (.Let bs body) := by
  match body with
  | .Let more suffix =>
    rw [flattenBindings, flattenBindings_lower (bs ++ more) suffix, lowerTotalExpr_let_append]
  | .Var _ | .Lit _ | .Builtin _ | .Error | .Lam _ _ | .Fix _ _ | .App _ _ | .Force _
  | .Delay _ | .Constr _ _ | .Case _ _ => simp [flattenBindings]
termination_by exprSize body
decreasing_by simp [exprSize]; omega

theorem flattenBindings_fresh (bs : List (VarId × Expr × Bool)) (body : Expr) (avoid : List VarId) :
    freshIn avoid (.Let (flattenBindings bs body).1 (flattenBindings bs body).2) =
      freshIn avoid (.Let bs body) := by
  match body with
  | .Let more suffix =>
    rw [flattenBindings, flattenBindings_fresh (bs ++ more) suffix, freshIn_let_append]
  | .Var _ | .Lit _ | .Builtin _ | .Error | .Lam _ _ | .Fix _ _ | .App _ _ | .Force _
  | .Delay _ | .Constr _ _ | .Case _ _ => simp [flattenBindings]
termination_by exprSize body
decreasing_by simp [exprSize]; omega

theorem FactRel.of_flatten {G : VarId → Prop} {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} {bs flat : List (VarId × Expr × Bool)} {body inner e' : Expr}
    (hflat : flattenBindings bs body = (flat, inner)) (h : FactRel G P Γ (.Let flat inner) e') :
    FactRel G P Γ (.Let bs body) e' := by
  apply h.congr_left
  · intro env; rw [← flattenBindings_lower bs body env, hflat]
  · intro avoid; rw [← flattenBindings_fresh bs body avoid, hflat]

/-! ## The walk -/

theorem flatten_two_lt {bs rest : List (VarId × Expr × Bool)} {body inner hr tr : Expr}
    {h t : VarId} {he te : Bool}
    (hf : flattenBindings bs body = ((h, hr, he) :: (t, tr, te) :: rest, inner)) :
    exprSize hr < exprSize (.Let bs body) ∧
      exprSize (.Let ((t, tr, te) :: rest) inner) < exprSize (.Let bs body) ∧
      exprSize (.Let rest inner) < exprSize (.Let bs body) := by
  have bound := exprSize_flattenBindings bs body
  rw [hf] at bound
  simp only [exprSize, exprSizeBinds] at bound ⊢
  have := exprSize_pos hr
  have := exprSize_pos tr
  omega

theorem flatten_one_lt {bs : List (VarId × Expr × Bool)} {body inner r : Expr} {x : VarId} {er : Bool}
    (hf : flattenBindings bs body = ([(x, r, er)], inner)) :
    exprSize r < exprSize (.Let bs body) ∧ exprSize inner < exprSize (.Let bs body) := by
  have bound := exprSize_flattenBindings bs body
  rw [hf] at bound
  simp only [exprSize, exprSizeBinds] at bound ⊢
  omega

theorem flatten_nil_lt {bs : List (VarId × Expr × Bool)} {body inner : Expr}
    (hf : flattenBindings bs body = ([], inner)) : exprSize inner < exprSize (.Let bs body) := by
  have bound := exprSize_flattenBindings bs body
  rw [hf] at bound
  simp only [exprSize, exprSizeBinds] at bound ⊢
  omega

theorem listRel_attach_map {G : VarId → Prop} {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} (children : List Expr) (f : Expr → Expr)
    (h : ∀ c ∈ children, FactRel G P Γ c (f c)) :
    ListRel (FactRel G P Γ) children (children.attach.map fun ⟨c, _⟩ => f c) := by
  induction children with
  | nil => trivial
  | cons c cs ih =>
    simp only [List.attach_cons, List.map_cons, List.map_map]
    refine ⟨h c (.head _), ?_⟩
    have := ih (fun c' hc' => h c' (.tail _ hc'))
    simpa [Function.comp_def] using this

theorem fuseListWalk_factRel (e : Expr) (Γ : List (VarId × Expr)) :
    FactRel (fun _ => True) Produces Γ e (fuseListWalk Γ e) := by
  match e with
  | .Let bs body =>
    rw [fuseListWalk]
    split
    · rename_i h hr he t tr te remaining inner hflat
      apply FactRel.of_flatten hflat
      have ihhr := fuseListWalk_factRel hr Γ
      have ihrest := fuseListWalk_factRel (.Let ((t, tr, te) :: remaining) inner) ((h, hr) :: Γ)
      have fallback : FactRel (fun _ => True) Produces Γ (.Let ((h, hr, he) :: (t, tr, te) :: remaining) inner)
          (.Let [(h, fuseListWalk Γ hr, he)]
            (fuseListWalk ((h, hr) :: Γ) (.Let ((t, tr, te) :: remaining) inner))) :=
        (FactRel.let_single hr trivial (.inl rfl) ihhr ihrest
          (fun _ _ _ _ _ hp => hp)).congr_left
          (fun env => lowerTotalExpr_let_cons env _ _ _) (fun avoid => freshIn_let_cons avoid _ _ _)
      split
      · rename_i l l' hhead htail
        split
        · rename_i hcond
          simp only [Bool.and_eq_true] at hcond
          have ihsuffix := fuseListWalk_factRel (.Let remaining inner) ((t, tr) :: (h, hr) :: Γ)
          refine (fusion_factRel (he := he) (te := te) trivial trivial hhead htail hcond.1 hcond.2 ihsuffix).congr_left ?_ ?_
          · intro env
            rw [lowerTotalExpr_let_cons env (h, hr, he), lowerTotalExpr_let_single,
              lowerTotalExpr_let_single, lowerTotalExpr_let_cons (h :: env) (t, tr, te)]
          · intro avoid
            rw [freshIn_let_cons avoid (h, hr, he), freshIn_let_single, freshIn_let_single,
              freshIn_let_cons (h :: avoid) (t, tr, te)]
        · exact fallback
      · exact fallback
    · rename_i x r er inner hflat
      apply FactRel.of_flatten hflat
      exact FactRel.let_single r trivial (.inl rfl) (fuseListWalk_factRel r Γ)
        (fuseListWalk_factRel inner ((x, r) :: Γ)) (fun _ _ _ _ _ hp => hp)
    · rename_i inner hflat
      apply FactRel.of_flatten hflat
      exact (fuseListWalk_factRel inner Γ).congr_left (fun env => lowerTotalExpr_let_nil env inner)
        (fun avoid => freshIn_let_nil avoid inner)
  | .Lam x b => rw [fuseListWalk]; exact (fuseListWalk_factRel b Γ).lam trivial
  | .Fix f b =>
    rw [fuseListWalk]
    cases b with
    | Lam x inner =>
      have ih := fuseListWalk_factRel (.Lam x inner) Γ
      rw [fuseListWalk] at ih ⊢
      exact (fuseListWalk_factRel inner Γ).fix_lam trivial trivial (fun _ _ => trivial)
    | _ =>
      intro env t _ _ _ _ _ hlow
      rw [MIR.lowerTotalExpr_fix_nonlam_none env f _ (by intros; simp)] at hlow
      cases hlow
  | .App f a => rw [fuseListWalk]; exact (fuseListWalk_factRel f Γ).app (fuseListWalk_factRel a Γ)
  | .Force b => rw [fuseListWalk]; exact (fuseListWalk_factRel b Γ).force
  | .Delay b => rw [fuseListWalk]; exact (fuseListWalk_factRel b Γ).delay
  | .Constr tag fields =>
    rw [fuseListWalk]
    exact FactRel.constr (listRel_attach_map fields _ fun c _ => fuseListWalk_factRel c Γ)
  | .Case scrutinee alternatives =>
    rw [fuseListWalk]
    exact FactRel.case (fuseListWalk_factRel scrutinee Γ)
      (listRel_attach_map alternatives _ fun c _ => fuseListWalk_factRel c Γ)
  | .Var _ | .Lit _ | .Builtin _ | .Error => rw [fuseListWalk]; exact FactRel.refl _ _ _ _
termination_by exprSize e
decreasing_by
  all_goals first
    | (simp only [exprSize]; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)
    | exact (flatten_two_lt (by assumption)).1
    | exact (flatten_two_lt (by assumption)).2.1
    | exact (flatten_two_lt (by assumption)).2.2
    | exact (flatten_one_lt (by assumption)).1
    | exact (flatten_one_lt (by assumption)).2
    | exact flatten_nil_lt (by assumption)

end Moist.Verified.ShapeFacts

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced Moist.Verified.ShapeFacts

/-- List destructor fusion refines its input. -/
theorem fuseListDestructors_refines (e : Expr) : MIRCtxRefines e (fuseListDestructors e) := by
  unfold fuseListDestructors
  simp only
  split
  · exact mirCtxRefines_trans (Hygiene.uniqueOptimizationBinders_refines e)
      (mirCtxRefines_of_factRel (by assumption) (fun _ _ => trivial) (fun _ _ => trivial)
        (fuseListWalk_factRel _ []))
  · exact Hygiene.uniqueOptimizationBinders_refines e

end Moist.Verified.MIR
