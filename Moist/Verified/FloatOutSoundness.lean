import Moist.Verified.FloatOut.Steps
import Moist.Verified.HygieneSoundness
import Moist.MIR.Optimize.FloatOut

/-! # Soundness of let float-out

`floatOut_refines`: for every MIR expression `e`, `e ⊑Ctxᴹ (floatOut e).1`.

The traversal is certified node by node. A float out of a `Lam`/`Fix` first
reorders the binding block so that the floated bindings come first
(`mirCtxRefines_reorder`, built from `mirCtxRefines_letSwap`), then moves
them out one at a time (`mirCtxRefines_floatLam`, `mirCtxRefines_floatFix`).
A float out of a `Case` reorders inside each alternative and then hoists
every floated binding before the case (`mirCtxRefines_floatCaseAlt`). The
capture conditions are exactly the checks `floatsPast` and `caseFloatSafe`
perform. -/

namespace Moist.Verified.FloatOut

open Moist.MIR
open Moist.Verified.MIR (MIRCtxRefines mirCtxRefines_refl mirCtxRefines_trans
  mirCtxRefines_of_lowerEq mirCtxRefines_lam mirCtxRefines_app mirCtxRefines_force
  mirCtxRefines_delay mirCtxRefines_constr mirCtxRefines_case mirCtxRefines_fix_lam
  mirCtxRefines_fix_nonlam_lhs mirCtxRefines_let_body mirCtxRefines_let_binds_congr
  lowerTotalExprList_append lowerTotalExprList_cons lowerTotalExpr_case_of_list
  lowerTotalExpr_let_single lowerTotalExpr_let_flatten_body freeVarsLet_not_contains_of_fresh)
open Moist.Verified.Equivalence (ListRel)
open Moist.Verified.InlineSoundness.Rename (lowerTotalExpr_let_nil lowerTotalExpr_let_cons beq_comm)

abbrev Binding := VarId × Expr × Bool

/-! ## Lowering of the helper shapes -/

theorem lowerTotalExpr_let_congr {M₁ M₂ : Expr}
    (h : ∀ env, lowerTotalExpr env M₁ = lowerTotalExpr env M₂) :
    ∀ (bs : List Binding) (env : List VarId),
      lowerTotalExpr env (.Let bs M₁) = lowerTotalExpr env (.Let bs M₂)
  | [], env => by rw [lowerTotalExpr_let_nil, lowerTotalExpr_let_nil, h]
  | (x, rhs, er) :: rest, env => by
    rw [lowerTotalExpr_let_cons, lowerTotalExpr_let_cons, lowerTotalExpr_let_congr h rest]

theorem lowerTotalExpr_mkLet (env : List VarId) (bs : List Binding) (body : Expr) :
    lowerTotalExpr env (mkLet bs body) = lowerTotalExpr env (.Let bs body) := by
  cases bs with
  | nil => rw [mkLet, lowerTotalExpr_let_nil]
  | cons _ _ => rfl

theorem lowerTotalExpr_mkLet_append (env : List VarId) (bs cs : List Binding) (body : Expr) :
    lowerTotalExpr env (mkLet bs (mkLet cs body)) =
      lowerTotalExpr env (mkLet (bs ++ cs) body) := by
  rw [lowerTotalExpr_mkLet, lowerTotalExpr_mkLet,
    lowerTotalExpr_let_congr (fun env => lowerTotalExpr_mkLet env cs body) bs env,
    lowerTotalExpr_let_flatten_body]

theorem mirCtxRefines_mkLet_body {bs : List Binding} {b₁ b₂ : Expr}
    (h : MIRCtxRefines b₁ b₂) : MIRCtxRefines (mkLet bs b₁) (mkLet bs b₂) := by
  cases bs with
  | nil => exact h
  | cons _ _ => exact mirCtxRefines_let_body h

theorem mirCtxRefines_let_cons_tail {b : Binding} {bs₁ bs₂ : List Binding} {B : Expr}
    (h : MIRCtxRefines (.Let bs₁ B) (.Let bs₂ B)) :
    MIRCtxRefines (.Let (b :: bs₁) B) (.Let (b :: bs₂) B) :=
  mirCtxRefines_trans
    (mirCtxRefines_of_lowerEq fun env => (lowerTotalExpr_let_flatten_body [b] bs₁ B env).symm)
    (mirCtxRefines_trans (mirCtxRefines_let_body h)
      (mirCtxRefines_of_lowerEq fun env => lowerTotalExpr_let_flatten_body [b] bs₂ B env))

/-! ## Partitioning -/

/-- What `floatsPast` guarantees about a floated binding. -/
def FloatOK (binders stays : List VarId) (blocked : VarSet) (b : Binding) : Prop :=
  isPure b.2.1 = true ∧ (∀ y ∈ binders, (freeVars b.2.1).contains y = false) ∧
    (∀ y ∈ stays, (freeVars b.2.1).contains y = false) ∧ (∀ y ∈ binders, (b.1 == y) = false) ∧
    blocked.contains b.1 = false

theorem floatsPast_spec {binders stays : List VarId} {blocked : VarSet} {x : VarId}
    {rhs : Expr} {er : Bool} (h : floatsPast binders stays blocked x rhs = true) :
    FloatOK binders stays blocked (x, rhs, er) := by
  simp only [floatsPast, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at h
  obtain ⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩ := h
  exact ⟨h₁, fun y hy => by simpa using h₂ y hy, fun y hy => by simpa using h₃ y hy,
    fun y hy => by rw [beq_comm]; simpa using h₄ y hy, h₅⟩

theorem partitionFrom_floats (binders : List VarId) :
    ∀ (binds : List Binding) (stays : List VarId) (blocked : VarSet),
      ∀ b ∈ (partitionFrom binders stays blocked binds).1, FloatOK binders stays blocked b
  | [], _, _ => by simp [partitionFrom]
  | (x, rhs, er) :: rest, stays, blocked => by
    intro b hb
    by_cases hf : floatsPast binders stays blocked x rhs = true
    · simp only [partitionFrom, hf, if_true] at hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact floatsPast_spec hf
      · exact partitionFrom_floats binders rest stays blocked b hb
    · simp only [partitionFrom, hf, Bool.false_eq_true, if_false] at hb
      obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := partitionFrom_floats binders rest _ _ b hb
      refine ⟨h₁, h₂, fun y hy => h₃ y (.tail _ hy), h₄, ?_⟩
      cases hc : blocked.contains b.1
      · rfl
      · rw [VarSet.contains_insert_of_contains _ x _
          (VarSet.contains_union_left _ (freeVars rhs) _ hc)] at h₅
        cases h₅

/-- A binding moves past the bindings that may float before it. -/
theorem mirCtxRefines_bubble (sv : VarId) (se : Expr) (ser : Bool) (B : Expr) :
    ∀ (F rest : List Binding),
      (∀ f ∈ F, isPure f.2.1 = true ∧ (freeVars f.2.1).contains sv = false ∧
        (freeVars se).contains f.1 = false ∧ (f.1 == sv) = false) →
      MIRCtxRefines (.Let ((sv, se, ser) :: (F ++ rest)) B) (.Let (F ++ (sv, se, ser) :: rest) B)
  | [], _, _ => mirCtxRefines_refl _
  | (fv, fe, fer) :: F, rest, h => by
    obtain ⟨hp, hfs, hsf, hne⟩ := h _ (.head _)
    exact mirCtxRefines_trans (mirCtxRefines_letSwap hp hfs hsf hne)
      (mirCtxRefines_let_cons_tail
        (mirCtxRefines_bubble sv se ser B F rest fun g hg => h g (.tail _ hg)))

/-- Reordering a binding block so that the floated bindings come first. -/
theorem mirCtxRefines_reorder (binders : List VarId) (B : Expr) :
    ∀ (binds : List Binding) (stays : List VarId) (blocked : VarSet),
      MIRCtxRefines (.Let binds B)
        (.Let ((partitionFrom binders stays blocked binds).1 ++
          (partitionFrom binders stays blocked binds).2) B)
  | [], _, _ => mirCtxRefines_refl _
  | (x, rhs, er) :: rest, stays, blocked => by
    by_cases hf : floatsPast binders stays blocked x rhs = true
    · simp only [partitionFrom, hf, if_true, List.cons_append]
      exact mirCtxRefines_let_cons_tail (mirCtxRefines_reorder binders B rest stays blocked)
    · simp only [partitionFrom, hf, Bool.false_eq_true, if_false]
      refine mirCtxRefines_trans (mirCtxRefines_let_cons_tail
        (mirCtxRefines_reorder binders B rest (x :: stays)
          ((blocked.union (freeVars rhs)).insert x))) ?_
      refine mirCtxRefines_bubble x rhs er B _ _ fun f hf => ?_
      obtain ⟨h₁, -, h₃, -, h₅⟩ := partitionFrom_floats binders rest _ _ f hf
      obtain ⟨hu, hxf⟩ := VarSet.insert_not_contains _ _ _ h₅
      refine ⟨h₁, h₃ x (.head _), ?_, by rw [beq_comm]; exact hxf⟩
      cases hc : (freeVars rhs).contains f.1
      · rfl
      · rw [VarSet.contains_union_right _ _ _ hc] at hu; cases hu

/-! ## Floating out of `Lam` and `Fix` -/

private theorem lowerTotalExpr_let_mkLet_cons (env : List VarId) (b : Binding)
    (F : List Binding) (M : Expr) :
    lowerTotalExpr env (.Let [b] (mkLet F M)) = lowerTotalExpr env (mkLet (b :: F) M) := by
  rw [lowerTotalExpr_let_congr (fun env => lowerTotalExpr_mkLet env F M) [b] env,
    lowerTotalExpr_let_flatten_body, lowerTotalExpr_mkLet]; rfl

theorem mirCtxRefines_floatLamAll (x : VarId) (S : List Binding) (inner : Expr) :
    ∀ F : List Binding,
      (∀ f ∈ F, isPure f.2.1 = true ∧ (freeVars f.2.1).contains x = false ∧ (f.1 == x) = false) →
      MIRCtxRefines (.Lam x (.Let (F ++ S) inner)) (mkLet F (.Lam x (mkLet S inner)))
  | [], _ => mirCtxRefines_lam (mirCtxRefines_of_lowerEq fun env =>
      (lowerTotalExpr_mkLet env S inner).symm)
  | (v, p, er) :: F, h => by
    obtain ⟨hp, hx, hvx⟩ := h _ (.head _)
    refine mirCtxRefines_trans (mirCtxRefines_floatLam hp hx hvx) ?_
    refine mirCtxRefines_trans (mirCtxRefines_let_body
      (mirCtxRefines_floatLamAll x S inner F fun f hf => h f (.tail _ hf))) ?_
    exact mirCtxRefines_of_lowerEq fun env => lowerTotalExpr_let_mkLet_cons env _ F _

theorem mirCtxRefines_floatFixAll (g x : VarId) (S : List Binding) (inner : Expr) :
    ∀ F : List Binding,
      (∀ f ∈ F, isPure f.2.1 = true ∧ (freeVars f.2.1).contains g = false ∧
        (freeVars f.2.1).contains x = false ∧ (f.1 == g) = false ∧ (f.1 == x) = false) →
      MIRCtxRefines (.Fix g (.Lam x (.Let (F ++ S) inner)))
        (mkLet F (.Fix g (.Lam x (mkLet S inner))))
  | [], _ => mirCtxRefines_fix_lam (mirCtxRefines_of_lowerEq fun env =>
      (lowerTotalExpr_mkLet env S inner).symm)
  | (v, p, er) :: F, h => by
    obtain ⟨hp, hg, hx, hvg, hvx⟩ := h _ (.head _)
    refine mirCtxRefines_trans (mirCtxRefines_floatFix hp hg hx hvg hvx) ?_
    refine mirCtxRefines_trans (mirCtxRefines_let_body
      (mirCtxRefines_floatFixAll g x S inner F fun f hf => h f (.tail _ hf))) ?_
    exact mirCtxRefines_of_lowerEq fun env => lowerTotalExpr_let_mkLet_cons env _ F _

theorem tryFloat_lam (x : VarId) (body : Expr) (r : Expr × Bool)
    (h : MIRCtxRefines body r.1) : MIRCtxRefines (.Lam x body) (tryFloat [x] (.Lam x) r).1 := by
  refine mirCtxRefines_trans (mirCtxRefines_lam h) ?_
  obtain ⟨e, c⟩ := r
  unfold tryFloat
  split
  · rename_i binds inner heq
    dsimp only at heq ⊢
    subst heq
    rcases hpart : partitionBindings [x] binds with ⟨F, S⟩
    dsimp only
    split
    · exact mirCtxRefines_refl _
    · have hpart' : partitionFrom [x] [] VarSet.empty binds = (F, S) := hpart
      have hre := mirCtxRefines_reorder [x] inner binds [] VarSet.empty
      rw [hpart'] at hre
      refine mirCtxRefines_trans (mirCtxRefines_lam hre) (mirCtxRefines_floatLamAll x S inner F ?_)
      intro f hf
      obtain ⟨h₁, h₂, -, h₄, -⟩ := partitionFrom_floats [x] binds [] VarSet.empty f
        (by rw [hpart']; exact hf)
      exact ⟨h₁, h₂ x (.head _), h₄ x (.head _)⟩
  · exact mirCtxRefines_refl _

theorem tryFloat_fix (g x : VarId) (body : Expr) (r : Expr × Bool)
    (h : MIRCtxRefines body r.1) :
    MIRCtxRefines (.Fix g (.Lam x body))
      (tryFloat [g, x] (fun inner => .Fix g (.Lam x inner)) r).1 := by
  refine mirCtxRefines_trans (mirCtxRefines_fix_lam h) ?_
  obtain ⟨e, c⟩ := r
  unfold tryFloat
  split
  · rename_i binds inner heq
    dsimp only at heq ⊢
    subst heq
    rcases hpart : partitionBindings [g, x] binds with ⟨F, S⟩
    dsimp only
    split
    · exact mirCtxRefines_refl _
    · have hpart' : partitionFrom [g, x] [] VarSet.empty binds = (F, S) := hpart
      have hre := mirCtxRefines_reorder [g, x] inner binds [] VarSet.empty
      rw [hpart'] at hre
      refine mirCtxRefines_trans (mirCtxRefines_fix_lam hre)
        (mirCtxRefines_floatFixAll g x S inner F ?_)
      intro f hf
      obtain ⟨h₁, h₂, -, h₄, -⟩ := partitionFrom_floats [g, x] binds [] VarSet.empty f
        (by rw [hpart']; exact hf)
      exact ⟨h₁, h₂ g (.head _), h₂ x (.tail _ (.head _)), h₄ g (.head _),
        h₄ x (.tail _ (.head _))⟩
  · exact mirCtxRefines_refl _

/-! ## Floating out of `Case` -/

theorem lowerTotalExpr_flattenLets (env : List VarId) :
    ∀ (acc : List Binding) (e : Expr),
      lowerTotalExpr env (.Let (flattenLets acc e).1 (flattenLets acc e).2) =
        lowerTotalExpr env (.Let acc e)
  | acc, .Let binds body => by
    rw [flattenLets, lowerTotalExpr_flattenLets env (acc ++ binds) body,
      lowerTotalExpr_let_flatten_body]
  | _, .Var _ | _, .Lit _ | _, .Builtin _ | _, .Error | _, .Lam _ _ | _, .Fix _ _
  | _, .App _ _ | _, .Force _ | _, .Delay _ | _, .Constr _ _ | _, .Case _ _ => rfl

theorem floatAlt_refines (alt : Expr) :
    MIRCtxRefines alt (mkLet (floatAlt alt).1 (floatAlt alt).2) := by
  unfold floatAlt
  split
  · rename_i binds body
    rcases hfl : flattenLets binds body with ⟨all, inner⟩
    rcases hpart : partitionBindings [] all with ⟨F, S⟩
    dsimp only
    have hpart' : partitionFrom [] [] VarSet.empty all = (F, S) := hpart
    have hre := mirCtxRefines_reorder [] inner all [] VarSet.empty
    rw [hpart'] at hre
    refine mirCtxRefines_trans (mirCtxRefines_of_lowerEq fun env => ?_)
      (mirCtxRefines_trans hre (mirCtxRefines_of_lowerEq fun env => ?_))
    · have := lowerTotalExpr_flattenLets env binds body
      rw [hfl] at this; exact this.symm
    · rw [lowerTotalExpr_mkLet_append, lowerTotalExpr_mkLet, hpart]
  · exact mirCtxRefines_refl _

theorem floatAlt_pure (alt : Expr) : ∀ b ∈ (floatAlt alt).1, isPure b.2.1 = true := by
  unfold floatAlt
  split
  · rename_i binds body
    rcases flattenLets binds body with ⟨all, inner⟩
    rcases hpart : partitionBindings [] all with ⟨F, S⟩
    dsimp only
    intro b hb
    have hpart' : partitionFrom [] [] VarSet.empty all = (F, S) := hpart
    rw [hpart] at hb
    exact (partitionFrom_floats [] all [] VarSet.empty b (by rw [hpart']; exact hb)).1
  · intro b hb; cases hb

theorem freeVars_mkLet_not_contains {bs : List Binding} {body : Expr} {y : VarId}
    (hbs : ∀ r ∈ bs, (freeVars r.2.1).contains y = false)
    (hb : (freeVars body).contains y = false) : (freeVars (mkLet bs body)).contains y = false := by
  cases bs with
  | nil => exact hb
  | cons r rs =>
    show (freeVars (.Let (r :: rs) body)).contains y = false
    rw [freeVars]
    exact freeVarsLet_not_contains_of_fresh _ body y hbs hb

private theorem lowerTotalExpr_case_mid (env : List VarId) (scrut : Expr) (pre post : List Expr)
    {a b : Expr} (h : lowerTotalExpr env a = lowerTotalExpr env b) :
    lowerTotalExpr env (.Case scrut (pre ++ a :: post)) =
      lowerTotalExpr env (.Case scrut (pre ++ b :: post)) := by
  rw [lowerTotalExpr_case_of_list, lowerTotalExpr_case_of_list, lowerTotalExprList_append,
    lowerTotalExprList_append, lowerTotalExprList_cons, lowerTotalExprList_cons, h]

/-- Hoisting the floated bindings of one alternative before the case. -/
theorem mirCtxRefines_hoistAlt (scrut : Expr) (pre post : List Expr) (R : Expr) :
    ∀ F : List Binding,
      (∀ b ∈ F, isPure b.2.1 = true ∧ (freeVars scrut).contains b.1 = false ∧
        (∀ a ∈ pre, (freeVars a).contains b.1 = false) ∧
        (∀ a ∈ post, (freeVars a).contains b.1 = false)) →
      MIRCtxRefines (.Case scrut (pre ++ mkLet F R :: post))
        (mkLet F (.Case scrut (pre ++ R :: post)))
  | [], _ => mirCtxRefines_refl _
  | (v, p, er) :: F, h => by
    obtain ⟨hp, hs, hpre, hpost⟩ := h _ (.head _)
    refine mirCtxRefines_trans (mirCtxRefines_of_lowerEq fun env =>
      lowerTotalExpr_case_mid env scrut pre post
        (lowerTotalExpr_let_mkLet_cons env (v, p, er) F R).symm) ?_
    refine mirCtxRefines_trans (mirCtxRefines_floatCaseAlt hp hs hpre hpost) ?_
    refine mirCtxRefines_trans (mirCtxRefines_let_body
      (mirCtxRefines_hoistAlt scrut pre post R F fun b hb => h b (.tail _ hb))) ?_
    exact mirCtxRefines_of_lowerEq fun env => lowerTotalExpr_let_mkLet_cons env _ F _

/-- Hoisting the floated bindings of every remaining alternative. -/
theorem mirCtxRefines_hoistAlts (scrut : Expr) :
    ∀ (done : List Expr) (todo : List (List Binding × Expr)),
      (∀ t ∈ todo, ∀ b ∈ t.1, isPure b.2.1 = true) →
      caseFloatSafe (freeVars scrut) done todo = true →
      MIRCtxRefines (.Case scrut (done ++ todo.map fun t => mkLet t.1 t.2))
        (mkLet (todo.map Prod.fst).flatten (.Case scrut (done ++ todo.map Prod.snd)))
  | done, [], _, _ => mirCtxRefines_refl _
  | done, (F, R) :: todo, hpure, hsafe => by
    simp only [caseFloatSafe, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hsafe
    obtain ⟨hF, hrest⟩ := hsafe
    have h₁ := mirCtxRefines_hoistAlt scrut done (todo.map fun t => mkLet t.1 t.2) R F
      fun b hb => by
        obtain ⟨⟨hs, hdone⟩, htodo⟩ := hF b hb
        refine ⟨hpure _ (.head _) b hb, hs, hdone, fun a ha => ?_⟩
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
        obtain ⟨hR, hbs⟩ := htodo t ht
        exact freeVars_mkLet_not_contains hbs hR
    have h₂ := mirCtxRefines_hoistAlts scrut (done ++ [R]) todo
      (fun t ht => hpure t (.tail _ ht)) hrest
    simp only [List.append_assoc, List.singleton_append] at h₂
    simp only [List.map_cons, List.flatten_cons]
    exact mirCtxRefines_trans h₁ (mirCtxRefines_trans (mirCtxRefines_mkLet_body h₂)
      (mirCtxRefines_of_lowerEq fun env => lowerTotalExpr_mkLet_append env _ _ _))

theorem caseFloatSafe_of_nil (scrutFV : VarSet) :
    ∀ (done : List Expr) (todo : List (List Binding × Expr)), (∀ t ∈ todo, t.1 = []) →
      caseFloatSafe scrutFV done todo = true
  | _, [], _ => rfl
  | done, (F, R) :: todo, h => by
    have hF : F = [] := h _ (.head _)
    subst hF
    simp only [caseFloatSafe, List.all_nil, Bool.true_and]
    exact caseFloatSafe_of_nil scrutFV _ todo fun t ht => h t (.tail _ ht)

theorem floatCase_refines (scrut : Expr) (alts : List Expr) (c : Bool) :
    MIRCtxRefines (.Case scrut alts) (floatCase scrut alts c).1 := by
  have hparts : ListRel MIRCtxRefines alts
      ((alts.map floatAlt).map fun t => mkLet t.1 t.2) := by
    clear c
    induction alts with
    | nil => trivial
    | cons a as ih => exact ⟨floatAlt_refines a, ih⟩
  have hpure : ∀ t ∈ alts.map floatAlt, ∀ b ∈ t.1, isPure b.2.1 = true := by
    intro t ht
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp ht
    exact floatAlt_pure a
  have hoist := fun hsafe => mirCtxRefines_trans
    (mirCtxRefines_case (mirCtxRefines_refl scrut) hparts)
    (mirCtxRefines_hoistAlts scrut [] (alts.map floatAlt) hpure hsafe)
  simp only [List.nil_append] at hoist
  unfold floatCase
  dsimp only
  split
  · rename_i hempty
    have hnil : ((alts.map floatAlt).map Prod.fst).flatten = [] := by
      simpa using hempty
    have h := hoist (caseFloatSafe_of_nil _ [] _ fun t ht => by
      have := List.flatten_eq_nil_iff.mp hnil t.1 (List.mem_map.mpr ⟨t, ht, rfl⟩)
      exact this)
    rw [hnil] at h
    exact h
  · split
    · rename_i hsafe
      exact hoist hsafe
    · exact mirCtxRefines_refl _

/-! ## The traversal -/

mutual
  theorem floatOutGo_refines : ∀ e : Expr, MIRCtxRefines e (floatOutGo e).1
    | .Var _ | .Lit _ | .Builtin _ | .Error => by
      unfold floatOutGo; exact mirCtxRefines_refl _
    | .Lam x body => by
      unfold floatOutGo; exact tryFloat_lam x body _ (floatOutGo_refines body)
    | .Fix g body => by
      cases body with
      | Lam x inner =>
        unfold floatOutGo; exact tryFloat_fix g x inner _ (floatOutGo_refines inner)
      | _ => exact mirCtxRefines_fix_nonlam_lhs fun _ _ h => Expr.noConfusion h
    | .App f a => by
      unfold floatOutGo
      exact mirCtxRefines_app (floatOutGo_refines f) (floatOutGo_refines a)
    | .Force e => by unfold floatOutGo; exact mirCtxRefines_force (floatOutGo_refines e)
    | .Delay e => by unfold floatOutGo; exact mirCtxRefines_delay (floatOutGo_refines e)
    | .Constr tag args => by
      cases args with
      | nil => unfold floatOutGo floatOutGoList; exact mirCtxRefines_refl _
      | cons m ms =>
        unfold floatOutGo floatOutGoList
        exact mirCtxRefines_constr (floatOutGo_refines m) (floatOutGoList_refines ms)
    | .Case scrut alts => by
      unfold floatOutGo
      exact mirCtxRefines_trans
        (mirCtxRefines_case (floatOutGo_refines scrut) (floatOutGoList_refines alts))
        (floatCase_refines _ _ _)
    | .Let binds body => by
      unfold floatOutGo
      dsimp only
      refine mirCtxRefines_trans (mirCtxRefines_let_binds_congr _ _ body
        (floatOutGoBinds_refines binds)) ?_
      refine mirCtxRefines_trans (mirCtxRefines_let_body (floatOutGo_refines body)) ?_
      refine mirCtxRefines_trans (mirCtxRefines_let_body (mirCtxRefines_of_lowerEq fun env => ?_))
        (mirCtxRefines_of_lowerEq fun env => lowerTotalExpr_let_flatten_body _ _ _ env)
      rw [lowerTotalExpr_flattenLets, lowerTotalExpr_let_nil]
  termination_by e => sizeOf e

  theorem floatOutGoList_refines : ∀ es : List Expr,
      ListRel MIRCtxRefines es (floatOutGoList es).1
    | [] => by unfold floatOutGoList; trivial
    | e :: es => by
      unfold floatOutGoList
      exact ⟨floatOutGo_refines e, floatOutGoList_refines es⟩
  termination_by es => sizeOf es

  theorem floatOutGoBinds_refines : ∀ bs : List Binding,
      ListRel (fun b₁ b₂ => b₁.1 = b₂.1 ∧ b₁.2.2 = b₂.2.2 ∧ MIRCtxRefines b₁.2.1 b₂.2.1)
        bs (floatOutGoBinds bs).1
    | [] => by unfold floatOutGoBinds; trivial
    | (v, rhs, er) :: rest => by
      unfold floatOutGoBinds
      exact ⟨⟨rfl, rfl, floatOutGo_refines rhs⟩, floatOutGoBinds_refines rest⟩
  termination_by bs => sizeOf bs
end

/-- **Let float-out is sound**: every MIR expression is contextually refined
    by its float-out. -/
theorem floatOut_refines (e : Expr) : MIRCtxRefines e (floatOut e).1 :=
  mirCtxRefines_trans (Moist.Verified.MIR.Hygiene.uniqueOptimizationBinders_refines e)
    (floatOutGo_refines _)

end Moist.Verified.FloatOut
