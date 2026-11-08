import Moist.Verified.GuardsSoundness.PushLayers

/-! # `pushWalk` and `pushAssert` refine their input -/

namespace Moist.Verified.Guards

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast

/-! ## Composing walk steps -/

theorem FactRel.layer {G : VarId → Prop} {Γ : List (VarId × Expr)} {src tgt : Expr}
    (h : ∀ env t, EnvDistinct env → lowerTotalExpr env src = some t →
      ∃ t', lowerTotalExpr env tgt = some t' ∧ FactRefines env.length (FactsHold PF Γ env) t t') :
    FactRel G PF Γ src tgt :=
  fun env t _ hd _ _ _ hlow => h env t hd hlow

theorem FactRel.trans' {G : VarId → Prop} {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} {a b c : Expr} (h₁ : FactRel G P Γ a b) (h₂ : FactRel G P Γ b c)
    (hf : ∀ env, freshIn env a = true → freshIn env b = true) : FactRel G P Γ a c := by
  intro env t hG hd hfa hk hs hlow
  obtain ⟨t₁, hl₁, r₁⟩ := h₁ env t hG hd hfa hk hs hlow
  obtain ⟨t₂, hl₂, r₂⟩ := h₂ env t₁ hG hd (hf env hfa) hk hs hl₁
  exact ⟨t₂, hl₂, r₁.trans r₂⟩

theorem FactRel.assertE' {G : VarId → Prop} {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} (u : Const × BuiltinType) {x x' : Expr} (h : FactRel G P Γ x x') :
    FactRel G P Γ (assertE u x) (assertE u x') := by
  unfold Advanced.assertE iteE
  exact .force (.app (.app (.app (FactRel.refl _ _ _ _) h) (FactRel.refl _ _ _ _)) (FactRel.refl _ _ _ _))

theorem listRel_of_forall {R : Expr → Expr → Prop} {g : Expr → Expr} :
    ∀ {es : List Expr}, (∀ e ∈ es, R e (g e)) → ListRel R es (es.map g)
  | [], _ => trivial
  | e :: _, h => ⟨h e (.head _), listRel_of_forall fun e' he' => h e' (.tail _ he')⟩

theorem listRel_map_map {R : Expr → Expr → Prop} {f g : Expr → Expr} :
    ∀ {es : List Expr}, (∀ e ∈ es, R (f e) (g e)) → ListRel R (es.map f) (es.map g)
  | [], _ => trivial
  | e :: _, h => ⟨h e (.head _), listRel_map_map fun e' he' => h e' (.tail _ he')⟩

theorem listRel_refl {R : Expr → Expr → Prop} (hR : ∀ e, R e e) : ∀ (es : List Expr), ListRel R es es
  | [] => trivial
  | e :: es => ⟨hR e, listRel_refl hR es⟩

theorem lowerList_map_assert {env : List VarId} {u : Const × BuiltinType} :
    ∀ {es : List Expr} {ts : List Term}, MIR.lowerTotalExprList env es = some ts →
      MIR.lowerTotalExprList env (es.map (Advanced.assertE u)) = some (ts.map (assertT · u))
  | [], ts, h => by
    rw [MIR.lowerTotalExprList_nil] at h; cases h; simp [MIR.lowerTotalExprList_nil]
  | e :: es, ts, h => by
    rw [MIR.lowerTotalExprList_cons] at h
    cases he : lowerTotalExpr env e with
    | none => rw [he] at h; cases h
    | some te =>
      cases hes : MIR.lowerTotalExprList env es with
      | none => rw [he, hes] at h; cases h
      | some tes =>
        rw [he, hes] at h; cases h
        rw [List.map_cons, MIR.lowerTotalExprList_cons, lower_assertE he, lowerList_map_assert hes]
        rfl

theorem freshInList_map_assert {avoid : List VarId} {u : Const × BuiltinType} {es : List Expr}
    (h : freshInList avoid es = true) : freshInList avoid (es.map (Advanced.assertE u)) = true := by
  rw [freshInList_iff] at h ⊢
  intro e he
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  rw [freshIn_assertE]; exact h a ha

/-! ## Shapes of the selected fields -/

theorem inv_of_facts {Γ : List (VarId × Expr)} {env : List VarId} {ρ : CekEnv}
    (henv : EnvWellFormed env.length ρ) (hlen : env.length ≤ ρ.length) (hF : FactsHold PF Γ env ρ) :
    Inv ⟨Γ, [], []⟩ env ρ :=
  ⟨henv, hlen, hF, fun _ h _ _ => by simp at h, fun _ h => by cases h⟩

theorem kind_of_facts {Γ : List (VarId × Expr)} {env : List VarId} {ρ : CekEnv} {s : Expr} {ts : Term}
    {w : CekValue} (henv : EnvWellFormed env.length ρ) (hlen : env.length ≤ ρ.length)
    (hF : FactsHold PF Γ env ρ) (hd : EnvDistinct env) (hts : lowerTotalExpr env s = some ts)
    (hw : Halts ρ ts w) : KindV (scrutineeKind Γ [] s) w := by
  have h0 := scrutineeKind_sound (c := ⟨Γ, [], []⟩) (inv_of_facts henv hlen hF) hd hts hw
  simpa only using h0

theorem tagFields_nullary {k : Kind} (hk : k = .bool ∨ k = .int) {w : CekValue} (hkv : KindV k w)
    {i : Nat} {fs : List CekValue} (ht : tagFields w = some (i, fs)) : fs = [] := by
  rcases hk with rfl | rfl
  · obtain ⟨b, rfl⟩ := hkv
    cases b <;> simp [tagFields, constToTagAndFields] at ht <;> exact ht.2
  · obtain ⟨n, rfl⟩ := hkv
    simp only [tagFields, constToTagAndFields] at ht
    split at ht
    · simp at ht; exact ht.2
    · simp at ht

theorem tagFields_list {w : CekValue} (hkv : ListValue w) {i : Nat} {fs : List CekValue}
    (ht : tagFields w = some (i, fs)) : (i = 0 ∧ fs.length = 2) ∨ (i = 1 ∧ fs = []) := by
  cases w with
  | VCon c =>
    cases c <;> simp only [ListValue] at hkv
    all_goals
      rename_i l
      cases l <;> simp [tagFields, constToTagAndFields] at ht <;> obtain ⟨rfl, rfl⟩ := ht <;> simp
  | _ => simp [ListValue] at hkv

theorem tagFields_pair {w : CekValue} (hkv : PairValue w) {i : Nat} {fs : List CekValue}
    (ht : tagFields w = some (i, fs)) : i = 0 ∧ fs.length = 2 := by
  obtain ⟨n, xs, rfl⟩ := hkv
  simp [tagFields, constToTagAndFields] at ht
  obtain ⟨rfl, rfl⟩ := ht
  simp

/-! ## The walks -/

theorem pf_push : ∀ (env : List VarId) (ρ : CekEnv) (r : Expr) (v : CekValue),
    (∀ y ∈ env, AnyName y) → EnvDistinct env → freshIn env r = true → Produces env ρ r v → PF env ρ r v :=
  fun _ _ _ _ _ _ hf hp => ⟨hp, hf⟩

theorem lower_case_of {env : List VarId} {s : Expr} {alts : List Expr} {ts : Term} {talts : List Term}
    (hs : lowerTotalExpr env s = some ts) (ha : MIR.lowerTotalExprList env alts = some talts) :
    lowerTotalExpr env (.Case s alts) = some (.Case ts talts) := by
  rw [MIR.lowerTotalExpr_case_of_list, hs, ha]; rfl

/-- The consumer moved into the alternatives of a list case. -/
theorem layer_list_case {Γ : List (VarId × Expr)} {u : Const × BuiltinType} {s b a1 : Expr}
    {h t : VarId} {rest : List Expr} (hk : scrutineeKind Γ [] s = .list) :
    FactRel AnyName PF Γ (Advanced.assertE u (.Case s (.Lam h (.Lam t b) :: a1 :: rest)))
      (.Case s (.Lam h (.Lam t (Advanced.assertE u b)) :: Advanced.assertE u a1 :: rest)) := by
  refine FactRel.layer fun env tt hd hlow => ?_
  obtain ⟨tx, hx, rfl⟩ := lower_assertE_inv hlow
  obtain ⟨ts, talts, hts, htalts, rfl⟩ := lowerTotalExpr_case_some hx
  rw [MIR.lowerTotalExprList_cons, MIR.lowerTotalExprList_cons] at htalts
  cases hA : lowerTotalExpr env (.Lam h (.Lam t b)) with
  | none => rw [hA] at htalts; cases htalts
  | some tA =>
  cases hA1 : lowerTotalExpr env a1 with
  | none => rw [hA, hA1] at htalts; cases htalts
  | some tA1 =>
  cases hR : MIR.lowerTotalExprList env rest with
  | none => rw [hA, hA1, hR] at htalts; cases htalts
  | some tR =>
  rw [hA, hA1, hR] at htalts; cases htalts
  obtain ⟨tb, htb, rfl⟩ := lowerTotalExpr_consAlt hA
  refine ⟨.Case ts (.Lam 0 (.Lam 0 (assertT tb u)) :: assertT tA1 u :: tR), ?_, ?_⟩
  · rw [lower_case_of hts (by
      rw [MIR.lowerTotalExprList_cons, MIR.lowerTotalExprList_cons,
        lowerTotalExpr_consAlt_of (lower_assertE htb), lower_assertE hA1, hR]; rfl)]
  refine layer_case u (by simp) fun ρ hF henv hlen w hw i fs a a' htag ha ha' => ?_
  have hkv := kind_of_facts henv hlen hF hd hts hw
  rw [hk] at hkv
  rcases tagFields_list hkv htag with ⟨rfl, h2⟩ | ⟨rfl, rfl⟩
  · simp at ha ha'; subst ha; subst ha'
    exact ⟨[h, t], tb, h2.symm, rfl, rfl⟩
  · simp at ha ha'; subst ha; subst ha'
    exact ⟨[], tA1, rfl, rfl, rfl⟩

theorem layer_pair_case {Γ : List (VarId × Expr)} {u : Const × BuiltinType} {s b : Expr}
    {h t : VarId} (hk : scrutineeKind Γ [] s = .pair) :
    FactRel AnyName PF Γ (Advanced.assertE u (.Case s [.Lam h (.Lam t b)]))
      (.Case s [.Lam h (.Lam t (Advanced.assertE u b))]) := by
  refine FactRel.layer fun env tt hd hlow => ?_
  obtain ⟨tx, hx, rfl⟩ := lower_assertE_inv hlow
  obtain ⟨ts, talts, hts, htalts, rfl⟩ := lowerTotalExpr_case_some hx
  rw [MIR.lowerTotalExprList_cons, MIR.lowerTotalExprList_nil] at htalts
  cases hA : lowerTotalExpr env (.Lam h (.Lam t b)) with
  | none => rw [hA] at htalts; cases htalts
  | some tA =>
  rw [hA] at htalts; cases htalts
  obtain ⟨tb, htb, rfl⟩ := lowerTotalExpr_consAlt hA
  refine ⟨.Case ts [.Lam 0 (.Lam 0 (assertT tb u))], ?_, ?_⟩
  · rw [lower_case_of hts (by
      rw [MIR.lowerTotalExprList_cons, MIR.lowerTotalExprList_nil,
        lowerTotalExpr_consAlt_of (lower_assertE htb)]; rfl)]
  refine layer_case u (by simp) fun ρ hF henv hlen w hw i fs a a' htag ha ha' => ?_
  have hkv := kind_of_facts henv hlen hF hd hts hw
  rw [hk] at hkv
  obtain ⟨rfl, h2⟩ := tagFields_pair hkv htag
  simp at ha ha'; subst ha; subst ha'
  exact ⟨[h, t], tb, h2.symm, rfl, rfl⟩

theorem layer_nullary_case {Γ : List (VarId × Expr)} {u : Const × BuiltinType} {s : Expr}
    {alts : List Expr} (hk : scrutineeKind Γ [] s = .bool ∨ scrutineeKind Γ [] s = .int) :
    FactRel AnyName PF Γ (Advanced.assertE u (.Case s alts)) (.Case s (alts.map (Advanced.assertE u))) := by
  refine FactRel.layer fun env tt hd hlow => ?_
  obtain ⟨tx, hx, rfl⟩ := lower_assertE_inv hlow
  obtain ⟨ts, talts, hts, htalts, rfl⟩ := lowerTotalExpr_case_some hx
  refine ⟨.Case ts (talts.map (assertT · u)), lower_case_of hts (lowerList_map_assert htalts), ?_⟩
  refine layer_case u (by simp) fun ρ hF henv hlen w hw i fs a a' htag ha ha' => ?_
  have hkv := kind_of_facts henv hlen hF hd hts hw
  have hfs : fs = [] := by
    rcases hk with hk | hk
    · rw [hk] at hkv; exact tagFields_nullary (.inl rfl) hkv htag
    · rw [hk] at hkv; exact tagFields_nullary (.inr rfl) hkv htag
  subst hfs
  rw [List.getElem?_map, ha] at ha'
  simp at ha'; subst ha'
  exact ⟨[], a, rfl, rfl, rfl⟩

theorem layer_leaf_rel {Γ : List (VarId × Expr)} (u : Const × BuiltinType) (x : Expr) :
    FactRel AnyName PF Γ (Advanced.assertE u x) (assertLeaf Γ u x) := by
  unfold assertLeaf
  split
  · rename_i hb
    refine FactRel.layer fun env tt hd hlow => ?_
    obtain ⟨tx, hx, rfl⟩ := lower_assertE_inv hlow
    have hl : MIR.lowerTotalExprList env [.Error, .Lit u] = some [.Error, .Constant u] := by
      obtain ⟨c, ty⟩ := u
      simp [MIR.lowerTotalExprList_cons, MIR.lowerTotalExprList_nil, lowerTotalExpr_error, lowerTotalExpr_lit]
    refine ⟨.Case tx [.Error, .Constant u], lower_case_of hx hl, ?_⟩
    refine layer_leaf u fun ρ hF henv hlen w hw => ?_
    obtain ⟨b, hb'⟩ := knownBooleanLocal_sound pf_produces _ _ _ hb hF hd hx hw
    exact ⟨b, hb'⟩
  · exact FactRel.refl _ _ _ _

theorem push_rel : ∀ N : Nat,
    (∀ (e : Expr) (Γ : List (VarId × Expr)), exprSize e < N → FactRel AnyName PF Γ e (pushWalk Γ e)) ∧
    (∀ (x : Expr) (Γ : List (VarId × Expr)) (u : Const × BuiltinType), exprSize x < N →
      FactRel AnyName PF Γ (Advanced.assertE u x) (pushAssert Γ u x)) := by
  intro N
  induction N with
  | zero => exact ⟨fun _ _ h => by omega, fun _ _ _ h => by omega⟩
  | succ N ih =>
  obtain ⟨ihw, iha⟩ := ih
  have walk : ∀ (e : Expr) (Γ : List (VarId × Expr)), exprSize e < N + 1 →
      FactRel AnyName PF Γ e (pushWalk Γ e) := by
    intro e Γ hs
    unfold pushWalk
    split
    · rename_i body
      simp only [exprSize, exprSizeBinds] at hs
      exact (ihw body Γ (by omega)).congr_left (fun env => lowerTotalExpr_let_nil env body)
        (fun avoid => freshIn_let_nil avoid body)
    · rename_i x r er rest body
      simp only [exprSize, exprSizeBinds] at hs
      have hlet := (FactRel.let_single (er := er) r trivial (.inl rfl) (ihw r Γ (by omega))
        (ihw (.Let rest body) ((x, r) :: Γ) (by have := exprSize_pos r; simp only [exprSize]; omega))
        (fun env ρ v hG hd hf hp => pf_push env ρ r v hG hd hf hp)).congr_left (fun env => lowerTotalExpr_let_cons env _ _ _)
        (fun avoid => freshIn_let_cons avoid _ _ _)
      exact hlet.congr_right fun env => lowerTotalExpr_consLet' env _ _
    · rename_i x b
      simp only [exprSize] at hs
      exact (ihw b Γ (by omega)).lam trivial
    · rename_i f b
      simp only [exprSize] at hs
      cases b with
      | Lam x inner =>
        unfold pushWalk
        simp only [exprSize] at hs
        exact (ihw inner Γ (by omega)).fix_lam trivial trivial (fun _ _ => trivial)
      | _ =>
        intro env t _ _ _ _ _ hlow
        rw [MIR.lowerTotalExpr_fix_nonlam_none env f _ (by intros; simp)] at hlow
        cases hlow
    · rename_i f a
      simp only [exprSize] at hs
      exact (ihw f Γ (by omega)).app (ihw a Γ (by omega))
    · rename_i b
      simp only [exprSize] at hs
      exact (ihw b Γ (by omega)).delay
    · rename_i tag fields
      simp only [exprSize] at hs
      rw [productList_attach_map]
      exact FactRel.constr (listRel_of_forall fun a ha => ihw a Γ (by have := exprSize_lt_of_mem ha; omega))
    · rename_i s h t b rest
      simp only [exprSize, exprSizeList] at hs
      rw [productList_attach_map]
      have step₁ : FactRel AnyName PF Γ (.Case s (.Lam h (.Lam t b) :: rest))
          (.Case (pushWalk Γ s) (.Lam h (.Lam t b) :: rest)) :=
        FactRel.case (ihw s Γ (by omega)) (listRel_refl (fun e => FactRel.refl _ _ _ e) _)
      have step₂ := FactRel.caseBind (s := pushWalk Γ s) (h := h) (t := t) (rest := rest) trivial trivial
        (ihw b (altFacts Γ (pushWalk Γ s) h t) (by omega))
        (listRel_of_forall fun a ha => ihw a Γ (by have := exprSize_lt_of_mem ha; omega))
      refine FactRel.trans' step₁ step₂ fun env hf => ?_
      simp only [freshIn, Bool.and_eq_true] at hf ⊢
      exact ⟨pushWalk_fresh hf.1, hf.2⟩
    · rename_i s alts _
      simp only [exprSize] at hs
      rw [productList_attach_map]
      exact FactRel.case (ihw s Γ (by omega))
        (listRel_of_forall fun a ha => ihw a Γ (by have := exprSize_lt_of_mem ha; omega))
    · rename_i x u
      simp only [exprSize] at hs
      exact iha x Γ u (by omega)
    · rename_i inner _
      simp only [exprSize] at hs
      exact (ihw inner Γ (by omega)).force
    all_goals exact FactRel.refl _ _ _ _
  refine ⟨walk, ?_⟩
  intro x Γ u hs
  -- the leaf: walk, then consume
  have leaf : ∀ x', x' = x → FactRel AnyName PF Γ (Advanced.assertE u x) (assertLeaf Γ u (pushWalk Γ x')) := by
    intro x' hx; subst hx
    refine FactRel.trans' (FactRel.assertE' u (walk x' Γ hs)) (layer_leaf_rel u _) fun env hf => ?_
    rw [freshIn_assertE] at hf ⊢; exact pushWalk_fresh hf
  unfold pushAssert
  split
  · rename_i ty
    refine FactRel.layer fun env tt _ hlow => ?_
    obtain ⟨tx, hx, rfl⟩ := lower_assertE_inv hlow
    rw [lowerTotalExpr_lit] at hx; cases hx
    exact ⟨_, by obtain ⟨c, ty'⟩ := u; rw [lowerTotalExpr_lit], layer_true u ty⟩
  · rename_i ty
    refine FactRel.layer fun env tt _ hlow => ?_
    obtain ⟨tx, hx, rfl⟩ := lower_assertE_inv hlow
    rw [lowerTotalExpr_lit] at hx; cases hx
    exact ⟨_, lowerTotalExpr_error env, layer_false u ty⟩
  · refine FactRel.layer fun env tt _ hlow => ?_
    obtain ⟨tx, hx, rfl⟩ := lower_assertE_inv hlow
    rw [lowerTotalExpr_error] at hx; cases hx
    exact ⟨_, lowerTotalExpr_error env, layer_error u⟩
  · rename_i body
    simp only [exprSize, exprSizeBinds] at hs
    refine (iha body Γ u (by omega)).congr_left (fun env => ?_) (fun avoid => ?_)
    · simp only [Advanced.assertE, iteE, MIR.lowerTotalExpr_force, MIR.lowerTotalExpr_app,
        lowerTotalExpr_let_nil]
    · rw [freshIn_assertE, freshIn_assertE, freshIn_let_nil]
  · rename_i y r er rest body
    simp only [exprSize, exprSizeBinds] at hs
    have layer : FactRel AnyName PF Γ (Advanced.assertE u (.Let ((y, r, er) :: rest) body))
        (.Let [(y, r, er)] (Advanced.assertE u (.Let rest body))) := by
      refine FactRel.layer fun env tt _ hlow => ?_
      obtain ⟨tx, hx, rfl⟩ := lower_assertE_inv hlow
      rw [lowerTotalExpr_let_cons] at hx
      obtain ⟨tr, tb, htr, htb, rfl⟩ := lowerTotalExpr_let_single_some hx
      refine ⟨.Apply (.Lam 0 (assertT tb u)) tr, ?_, layer_let u tb tr⟩
      rw [lowerTotalExpr_let_single, htr, lower_assertE htb]; rfl
    have body' := (FactRel.let_single (er := er) r trivial (.inl rfl) (ihw r Γ (by omega))
      (iha (.Let rest body) ((y, r) :: Γ) u (by have := exprSize_pos r; simp only [exprSize]; omega))
      (fun env ρ v hG hd hf hp => pf_push env ρ r v hG hd hf hp)).congr_right fun env => lowerTotalExpr_consLet' env _ _
    refine FactRel.trans' layer body' fun env hf => ?_
    rw [freshIn_assertE, freshIn_let_cons] at hf
    rw [freshIn_let_single] at hf ⊢
    rw [freshIn_assertE]; exact hf
  · rename_i s alts
    have nullary : (scrutineeKind Γ [] s = .bool ∨ scrutineeKind Γ [] s = .int) →
        FactRel AnyName PF Γ (Advanced.assertE u (.Case s alts))
          (.Case (pushWalk Γ s) (alts.attach.map fun ⟨a, _⟩ => pushAssert Γ u a)) := by
      intro hk
      simp only [exprSize] at hs
      rw [productList_attach_map]
      refine FactRel.trans' (layer_nullary_case (alts := alts) (u := u) hk)
        (FactRel.case (ihw s Γ (by omega))
          (listRel_map_map fun a ha => iha a Γ u (by have := exprSize_lt_of_mem ha; omega)))
        fun env hf => ?_
      rw [freshIn_assertE] at hf
      simp only [freshIn, Bool.and_eq_true] at hf ⊢
      exact ⟨hf.1, freshInList_map_assert hf.2⟩
    split
    · rename_i hk; exact nullary (.inl hk)
    · rename_i hk; exact nullary (.inr hk)
    · rename_i hk
      split
      · rename_i h t b a1 rest
        simp only [exprSize, exprSizeList] at hs
        rw [productList_attach_map]
        have step₁ : FactRel AnyName PF Γ
            (.Case s (.Lam h (.Lam t (Advanced.assertE u b)) :: Advanced.assertE u a1 :: rest))
            (.Case (pushWalk Γ s) (.Lam h (.Lam t (Advanced.assertE u b)) :: Advanced.assertE u a1 :: rest)) :=
          FactRel.case (ihw s Γ (by omega)) (listRel_refl (fun e => FactRel.refl _ _ _ e) _)
        have step₂ := FactRel.caseBind (s := pushWalk Γ s) (h := h) (t := t)
          (b := Advanced.assertE u b) (rest := Advanced.assertE u a1 :: rest)
          (rest' := pushAssert Γ u a1 :: rest.map (pushWalk Γ)) trivial trivial
          (iha b (altFacts Γ (pushWalk Γ s) h t) u (by omega))
          ⟨iha a1 Γ u (by omega), listRel_of_forall fun a ha => ihw a Γ (by have := exprSize_lt_of_mem ha; omega)⟩
        refine FactRel.trans' (layer_list_case hk) (FactRel.trans' step₁ step₂ fun env hf => ?_) fun env hf => ?_
        · simp only [freshIn, Bool.and_eq_true] at hf ⊢
          exact ⟨pushWalk_fresh hf.1, hf.2⟩
        · rw [freshIn_assertE] at hf
          simp only [freshIn, freshInList, Bool.and_eq_true] at hf ⊢
          obtain ⟨hfs, ⟨hh, ht, hfb⟩, hfa1, hfr⟩ := hf
          exact ⟨hfs, ⟨hh, ht, by rw [freshIn_assertE]; exact hfb⟩, by rw [freshIn_assertE]; exact hfa1, hfr⟩
      · exact leaf _ rfl
    · rename_i hk
      split
      · rename_i a b body
        simp only [exprSize, exprSizeList] at hs
        have step₁ : FactRel AnyName PF Γ (.Case s [.Lam a (.Lam b (Advanced.assertE u body))])
            (.Case (pushWalk Γ s) [.Lam a (.Lam b (Advanced.assertE u body))]) :=
          FactRel.case (ihw s Γ (by omega)) (listRel_refl (fun e => FactRel.refl _ _ _ e) _)
        have step₂ := FactRel.caseBind (s := pushWalk Γ s) (h := a) (t := b)
          (b := Advanced.assertE u body) (rest := []) (rest' := []) trivial trivial
          (iha body (altFacts Γ (pushWalk Γ s) a b) u (by omega)) trivial
        refine FactRel.trans' (layer_pair_case hk) (FactRel.trans' step₁ step₂ fun env hf => ?_) fun env hf => ?_
        · simp only [freshIn, Bool.and_eq_true] at hf ⊢
          exact ⟨pushWalk_fresh hf.1, hf.2⟩
        · rw [freshIn_assertE] at hf
          simp only [freshIn, freshInList, Bool.and_eq_true] at hf ⊢
          obtain ⟨hfs, ⟨ha, hb, hfb⟩, _⟩ := hf
          exact ⟨hfs, ⟨ha, hb, by rw [freshIn_assertE]; exact hfb⟩, trivial⟩
      · exact leaf _ rfl
    · exact leaf _ rfl
  · rename_i c a b
    simp only [exprSize] at hs
    have layer : FactRel AnyName PF Γ
        (Advanced.assertE u (.Force (.App (.App (.App (.Force (.Builtin .IfThenElse)) c) (.Delay a)) (.Delay b))))
        (.Force (iteE c (.Delay (Advanced.assertE u a)) (.Delay (Advanced.assertE u b)))) := by
      refine FactRel.layer fun env tt _ hlow => ?_
      obtain ⟨tx, hx, rfl⟩ := lower_assertE_inv hlow
      obtain ⟨t1, ht1, rfl⟩ := lowerTotalExpr_force_some hx
      obtain ⟨t2, tbD, ht2, htbD, rfl⟩ := lowerTotalExpr_app_some ht1
      obtain ⟨t3, taD, ht3, htaD, rfl⟩ := lowerTotalExpr_app_some ht2
      obtain ⟨tite, tc, htite, htc, rfl⟩ := lowerTotalExpr_app_some ht3
      obtain ⟨tB, htB, rfl⟩ := lowerTotalExpr_force_some htite
      rw [lowerTotalExpr_builtin] at htB; cases htB
      obtain ⟨tb, htb, rfl⟩ := lowerTotalExpr_delay_some htbD
      obtain ⟨ta, hta, rfl⟩ := lowerTotalExpr_delay_some htaD
      refine ⟨_, ?_, layer_ite u tc ta tb⟩
      simp only [iteE, MIR.lowerTotalExpr_force, MIR.lowerTotalExpr_app, MIR.lowerTotalExpr_delay,
        lowerTotalExpr_builtin, htc, lower_assertE hta, lower_assertE htb]
      rfl
    have cong : FactRel AnyName PF Γ (.Force (iteE c (.Delay (Advanced.assertE u a)) (.Delay (Advanced.assertE u b))))
        (.Force (iteE (pushWalk Γ c) (.Delay (pushAssert Γ u a)) (.Delay (pushAssert Γ u b)))) := by
      unfold iteE
      exact .force (.app (.app (.app (FactRel.refl _ _ _ _) (ihw c Γ (by omega)))
        (iha a Γ u (by omega)).delay) (iha b Γ u (by omega)).delay)
    refine FactRel.trans' layer cong fun env hf => ?_
    rw [freshIn_assertE] at hf
    have hf' : freshIn env (.Force (iteE c (.Delay a) (.Delay b))) = true := hf
    rw [freshIn_ite] at hf' ⊢
    simp only [Bool.and_eq_true] at hf' ⊢
    exact ⟨⟨hf'.1.1, by rw [freshIn_assertE]; exact hf'.1.2⟩, by rw [freshIn_assertE]; exact hf'.2⟩
  · exact leaf _ rfl

end Moist.Verified.Guards

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced Moist.Verified.ShapeFacts Moist.Verified.Guards

/-- Pushing `if _ then u else error` consumers inwards refines the input. -/
theorem pushAsserts_refines (e : Expr) : MIRCtxRefines e (Advanced.pushAsserts e) := by
  unfold Advanced.pushAsserts
  simp only
  refine mirCtxRefines_trans (Hygiene.uniqueOptimizationBinders_refines e) ?_
  split
  · rename_i hws
    exact mirCtxRefines_of_factRel hws (fun _ _ => trivial) (fun _ _ => trivial)
      ((push_rel _).1 _ [] (Nat.lt_succ_self _))
  · exact mirCtxRefines_refl _

end Moist.Verified.MIR
