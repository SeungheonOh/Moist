import Moist.Verified.PairListsSoundness.Unbox
import Moist.Verified.PreLowerSoundness

variable [sv : Moist.CEK.SemVariant]

/-! # The pair-list walk

`pairListWalk` keeps the shape of every node (congruence), transforms
recursive functions applied to lists of data pairs under list facts for their
parameters (`KnownRel.fixApp`, `KnownRel.letFix` with `pairKnowledge`),
records the tail of a `case` on a known pair list (`KnownRel.listCaseOf`)
and destructures its head when the alternative carries the prepared component
bindings (`KnownRel.pairEntryCase`). The walk introduces no binder
(`pairListWalk_fresh`). `destructurePairEntries` refines its input.
-/

namespace Moist.Verified.KnownLists

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.ShapeFacts

omit sv in
theorem preparedHead_spec {Γ : List (VarId × Expr)} {h a b : VarId} {body inner : Expr}
    (hp : preparedHead Γ h body = some (a, b, inner)) :
    ∃ h₁ h₂ e1 e2, body = .Let [(a, .Var h₁, e1)] (.Let [(b, .Var h₂, e2)] inner) ∧
      (h₁ == h) = true ∧ (h₂ == h) = true ∧ (b == a) = false ∧ (a == h) = false ∧
      maxUidExpr inner < a.uid ∧ maxUidExpr inner < b.uid := by
  unfold preparedHead at hp
  split at hp
  · rename_i a' h₁ e1 b' h₂ e2 inner'
    split at hp
    · rename_i hc
      cases hp
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, _⟩, h6⟩, h7⟩, _⟩ := hc
      exact ⟨h₁, h₂, e1, e2, rfl, h1, h2, h3, h4, h6, h7⟩
    · cases hp
  · cases hp

omit sv in
theorem freshIn_lambdaWrap_of {e e' : Expr} (h : ∀ avoid, freshIn avoid e = true → freshIn avoid e' = true) :
    ∀ (xs : List VarId) (avoid : List VarId), freshIn avoid (Advanced.lambdaWrap xs e) = true →
      freshIn avoid (Advanced.lambdaWrap xs e') = true
  | [], avoid, hf => h avoid hf
  | x :: xs, avoid, hf => by
    simp only [Advanced.lambdaWrap, freshIn, Bool.and_eq_true] at hf ⊢
    exact ⟨hf.1, freshIn_lambdaWrap_of h xs (x :: avoid) hf.2⟩

omit sv in
theorem freshInList_attach_map_of {es : List Expr} {f : Expr → Expr}
    (h : ∀ c ∈ es, ∀ avoid, freshIn avoid c = true → freshIn avoid (f c) = true) (avoid : List VarId)
    (hf : freshInList avoid es = true) :
    freshInList avoid (es.attach.map fun ⟨c, _⟩ => f c) = true := by
  rw [freshInList_iff] at hf ⊢
  intro y hy
  simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hy
  obtain ⟨c, hc, rfl⟩ := hy
  exact h c hc avoid (hf c hc)

omit sv in
theorem pairListWalk_fresh (e : Expr) (Γ : List (VarId × Expr)) (L : List VarId) :
    ∀ avoid, freshIn avoid e = true → freshIn avoid (pairListWalk Γ L e) = true := by
  intro avoid hf
  match e with
  | .App function argument =>
    rw [pairListWalk.eq_1]
    split
    · rename_i recursive parameter body arguments hfix
      have heq : Expr.App function argument = Advanced.applyAll (.Fix recursive
          (Advanced.lambdaWrap (parameter :: (lambdaChain body).1) (lambdaChain body).2)) arguments := by
        have := fixApplication_eq _ [] hfix
        simp only [Advanced.applyAll] at this
        rw [this, Advanced.lambdaWrap, lambdaChain_wrap]
      rw [heq, freshIn_applyAll, Bool.and_eq_true] at hf
      simp only []
      rw [freshIn_applyAll, Bool.and_eq_true]
      refine ⟨?_, freshInList_attach_map_of (fun c _ avoid h => pairListWalk_fresh c Γ L avoid h) avoid hf.2⟩
      simp only [freshIn, Bool.and_eq_true] at hf ⊢
      exact ⟨hf.1.1, freshIn_lambdaWrap_of (fun avoid h => pairListWalk_fresh _ Γ _ avoid h) _ _ hf.1.2⟩
    · simp only [freshIn, Bool.and_eq_true] at hf ⊢
      exact ⟨pairListWalk_fresh function Γ L avoid hf.1, pairListWalk_fresh argument Γ L avoid hf.2⟩
  | .Case scrutinee alternatives =>
    by_cases hB : ∃ l h t body rest, scrutinee = .Var l ∧
        alternatives = .Lam h (.Lam t body) :: rest
    · obtain ⟨l, h, t, body, rest, rfl, rfl⟩ := hB
      rw [pairListWalk.eq_2]
      have hf₀ := hf
      simp only [freshIn, freshInList, Bool.and_eq_true] at hf
      obtain ⟨_, ⟨hh, ht, hfb⟩, hfrest⟩ := hf
      have hfb' := pairListWalk_fresh body Γ (t :: L) _ hfb
      have hfrest' := freshInList_attach_map_of (fun c _ avoid h => pairListWalk_fresh c Γ L avoid h) avoid hfrest
      split
      · dsimp only
        split
        · rename_i a b inner hp
          obtain ⟨h₁, h₂, e1, e2, hbody, _, _, _, _, _, _⟩ := preparedHead_spec hp
          rw [hbody] at hfb'
          rw [freshIn_let_single] at hfb'
          simp only [Bool.and_eq_true] at hfb'
          obtain ⟨⟨_, ha⟩, hfb₂⟩ := hfb'
          rw [freshIn_let_single] at hfb₂
          simp only [Bool.and_eq_true] at hfb₂
          obtain ⟨⟨_, hb⟩, hfi⟩ := hfb₂
          simp only [freshIn, freshInList, Bool.and_eq_true, Bool.and_true]
          exact ⟨trivial, ⟨hh, ht, trivial, ha, hb,
            freshIn_replaceProjections _ _ _ _ inner _ hfi⟩, hfrest'⟩
        · simp only [freshIn, freshInList, Bool.and_eq_true]
          exact ⟨trivial, ⟨hh, ht, hfb'⟩, hfrest'⟩
      · simp only [freshIn, Bool.and_eq_true] at hf₀ ⊢
        rw [pairListWalk.eq_12]
        exact ⟨by simp [freshIn], freshInList_attach_map_of (fun c _ avoid h => pairListWalk_fresh c Γ L avoid h) avoid hf₀.2⟩
    · rw [pairListWalk.eq_3 _ _ _ _ (fun l h t body rest h₁ h₂ => hB ⟨l, h, t, body, rest, h₁, h₂⟩)]
      simp only [freshIn, Bool.and_eq_true] at hf ⊢
      exact ⟨pairListWalk_fresh scrutinee Γ L avoid hf.1,
        freshInList_attach_map_of (fun c _ avoid h => pairListWalk_fresh c Γ L avoid h) avoid hf.2⟩
  | .Let [] body =>
    rw [pairListWalk.eq_4]
    rw [freshIn_let_nil] at hf
    exact pairListWalk_fresh body Γ L avoid hf
  | .Let ((x, r, er) :: rest) body =>
    rw [freshIn_let_cons, freshIn_let_single] at hf
    simp only [Bool.and_eq_true] at hf
    obtain ⟨⟨hfr, hx⟩, hfb⟩ := hf
    by_cases hr : ∃ recursive parameter fixBody, r = .Fix recursive (.Lam parameter fixBody)
    · obtain ⟨recursive, parameter, fixBody, rfl⟩ := hr
      rw [pairListWalk.eq_5]
      split
      · rw [freshIn_let_single]
        simp only [Bool.and_eq_true]
        exact ⟨⟨pairListWalk_fresh _ Γ L avoid hfr, hx⟩, pairListWalk_fresh _ _ L _ hfb⟩
      · rw [freshIn_let_single]
        simp only [Bool.and_eq_true]
        refine ⟨⟨?_, hx⟩, pairListWalk_fresh _ _ L _ hfb⟩
        have hwrap : Expr.Fix recursive (.Lam parameter fixBody) = .Fix recursive
            (Advanced.lambdaWrap (parameter :: (lambdaChain fixBody).1) (lambdaChain fixBody).2) := by
          rw [Advanced.lambdaWrap, lambdaChain_wrap]
        rw [hwrap] at hfr
        simp only [freshIn, Bool.and_eq_true] at hfr ⊢
        exact ⟨hfr.1, freshIn_lambdaWrap_of (fun avoid h => pairListWalk_fresh _ Γ _ avoid h) _ _ hfr.2⟩
    · rw [pairListWalk.eq_6 _ _ _ _ _ _ _ (fun a b c h => hr ⟨a, b, c, h⟩)]
      rw [freshIn_let_single]
      simp only [Bool.and_eq_true]
      exact ⟨⟨pairListWalk_fresh r Γ L avoid hfr, hx⟩, pairListWalk_fresh _ _ L _ hfb⟩
  | .Lam x b =>
    rw [pairListWalk.eq_7]
    simp only [freshIn, Bool.and_eq_true] at hf ⊢
    exact ⟨hf.1, pairListWalk_fresh b Γ L _ hf.2⟩
  | .Fix f b =>
    rw [pairListWalk.eq_8]
    simp only [freshIn, Bool.and_eq_true] at hf ⊢
    exact ⟨hf.1, pairListWalk_fresh b Γ L _ hf.2⟩
  | .Force b =>
    rw [pairListWalk.eq_9]
    simp only [freshIn] at hf ⊢
    exact pairListWalk_fresh b Γ L _ hf
  | .Delay b =>
    rw [pairListWalk.eq_10]
    simp only [freshIn] at hf ⊢
    exact pairListWalk_fresh b Γ L _ hf
  | .Constr tag fields =>
    rw [pairListWalk.eq_11]
    simp only [freshIn] at hf ⊢
    exact freshInList_attach_map_of (fun c _ avoid h => pairListWalk_fresh c Γ L avoid h) avoid hf
  | .Var _ => rw [pairListWalk.eq_12]; exact hf
  | .Lit _ => rw [pairListWalk.eq_13]; exact hf
  | .Builtin _ => rw [pairListWalk.eq_14]; exact hf
  | .Error => rw [pairListWalk.eq_15]; exact hf
termination_by exprSize e
decreasing_by
  all_goals first
    | (have := fixApplication_inner_size (by assumption); simp only [exprSize] at *; omega)
    | (subst_vars; simp only [exprSize, exprSizeList] at *; omega)
    | (subst_vars; have := exprSize_lt_of_mem (by assumption); simp only [exprSize, exprSizeList] at *; omega)
    | (have bound := fixApplication_size _ _ (by assumption)
       have := bound.2.2 _ (by assumption)
       simp only [exprSize, exprSizeList] at *; omega)
    | (simp only [exprSize]; omega)
    | (simp only [exprSize, exprSizeBinds]; omega)
    | (simp only [exprSize, exprSizeBinds]; have := exprSize_pos r; omega)
    | (have := exprSize_lambdaChain fixBody; simp only [exprSize, exprSizeBinds]; omega)
    | (subst_vars; have := exprSize_lambdaChain fixBody; simp only [exprSize, exprSizeBinds] at *; omega)
    | (subst_vars; simp only [exprSize, exprSizeBinds]; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize, exprSizeList] at *; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)

theorem pairListWalk_rel (e : Expr) (Γ : List (VarId × Expr)) (L : List VarId) :
    KnownRel pairFamily Γ L e (pairListWalk Γ L e) := by
  match e with
  | .App function argument =>
    rw [pairListWalk.eq_1]
    split
    · rename_i recursive parameter body arguments hfix
      simp only
      have heq : Expr.App function argument = Advanced.applyAll (.Fix recursive
          (Advanced.lambdaWrap (parameter :: (lambdaChain body).1) (lambdaChain body).2)) arguments := by
        have := fixApplication_eq _ [] hfix
        simp only [Advanced.applyAll] at this
        rw [this, Advanced.lambdaWrap, lambdaChain_wrap]
      rw [heq]
      have hargs : ListRel (KnownRel pairFamily Γ L) arguments
          (arguments.attach.map fun ⟨a, _⟩ => pairListWalk Γ L a) :=
        listRel_known_attach_map arguments (pairListWalk Γ L) fun a _ => pairListWalk_rel a Γ L
      by_cases hP : pairListPositions Γ L recursive (parameter :: (lambdaChain body).1) arguments
          (lambdaChain body).2 = []
      · rw [hP, listedParameters_nil, List.nil_append]
        refine KnownRel.applyAll ?_ hargs
        simp only [Advanced.lambdaWrap]
        exact (KnownRel.lambdaWrap _ (pairListWalk_rel (lambdaChain body).2 Γ L)).fix_lam
      · obtain ⟨hlen, hpos, hcheck⟩ := pairListPositions_spec hP
        exact KnownRel.fixApp (K := pairKnowledge) (by simp) hlen hargs hpos hcheck
          (pairListWalk_rel (lambdaChain body).2 Γ _)
    · exact (pairListWalk_rel function Γ L).app (pairListWalk_rel argument Γ L)
  | .Case scrutinee alternatives =>
    by_cases hB : ∃ l h t body rest, scrutinee = .Var l ∧
        alternatives = .Lam h (.Lam t body) :: rest
    · obtain ⟨l, h, t, body, rest, rfl, rfl⟩ := hB
      rw [pairListWalk.eq_2]
      have hrest := listRel_known_attach_map rest (pairListWalk Γ L) fun a _ => pairListWalk_rel a Γ L
      split
      · rename_i hl
        dsimp only
        split
        · rename_i a b inner hp
          obtain ⟨h₁, h₂, e1, e2, hbody, hh₁, hh₂, hba, hah, hua, hub⟩ := preparedHead_spec hp
          have hC := pairListWalk_rel body Γ (t :: L)
          rw [hbody] at hC
          exact KnownRel.pairEntryCase hl hC
            (fun E hE => hbody ▸ pairListWalk_fresh body Γ (t :: L) E hE) hrest hh₁ hh₂ hba hah hua hub
        · exact KnownRel.listCaseOf (fun hF hd hil henv => pairKnowledge.var hl hF hd hil henv)
            (pairListWalk_rel body Γ (t :: L)) hrest
      · exact KnownRel.case (pairListWalk_rel _ Γ L)
          (listRel_known_attach_map _ (pairListWalk Γ L) fun a _ => pairListWalk_rel a Γ L)
    · rw [pairListWalk.eq_3 _ _ _ _ (fun l h t body rest h₁ h₂ => hB ⟨l, h, t, body, rest, h₁, h₂⟩)]
      exact KnownRel.case (pairListWalk_rel scrutinee Γ L)
        (listRel_known_attach_map alternatives (pairListWalk Γ L) fun a _ => pairListWalk_rel a Γ L)
  | .Let [] body =>
    rw [pairListWalk.eq_4]
    exact (pairListWalk_rel body Γ L).congr_left (fun env => lowerTotalExpr_let_nil env body)
      (fun avoid => freshIn_let_nil avoid body)
  | .Let ((x, r, er) :: rest) body =>
    by_cases hr : ∃ recursive parameter fixBody, r = .Fix recursive (.Lam parameter fixBody)
    · obtain ⟨recursive, parameter, fixBody, rfl⟩ := hr
      rw [pairListWalk.eq_5]
      split
      · exact (KnownRel.let_single _ (.inr rfl) (pairListWalk_rel _ Γ L)
          (pairListWalk_rel (.Let rest body) _ L)).congr_left
          (fun env => lowerTotalExpr_let_cons env _ _ _) (fun avoid => freshIn_let_cons avoid _ _ _)
      · rename_i hne
        simp only
        have hP : letFixPairPositions Γ L x recursive (parameter :: (lambdaChain fixBody).1)
            (lambdaChain fixBody).2 (.Let rest body) ≠ [] := by
          intro h; rw [h] at hne; exact hne rfl
        obtain ⟨hcheck, hcheckBody⟩ := letFixPairPositions_spec hP
        have hwrap : Expr.Fix recursive (.Lam parameter fixBody) = .Fix recursive
            (Advanced.lambdaWrap (parameter :: (lambdaChain fixBody).1) (lambdaChain fixBody).2) := by
          rw [Advanced.lambdaWrap, lambdaChain_wrap]
        rw [hwrap]
        exact (KnownRel.letFix (K := pairKnowledge) (by simp) hcheck
          (pairListWalk_rel (lambdaChain fixBody).2 Γ _)
          hcheckBody (fun y hy => environmentPairLists_known hy)
          (pairListWalk_rel (.Let rest body) _ L)).congr_left
          (fun env => lowerTotalExpr_let_cons env _ _ _) (fun avoid => freshIn_let_cons avoid _ _ _)
    · rw [pairListWalk.eq_6 _ _ _ _ _ _ _ (fun a b c h => hr ⟨a, b, c, h⟩)]
      exact (KnownRel.let_single (pairListWalk Γ L r) (.inr rfl) (pairListWalk_rel r Γ L)
        (pairListWalk_rel (.Let rest body) _ L)).congr_left
        (fun env => lowerTotalExpr_let_cons env _ _ _) (fun avoid => freshIn_let_cons avoid _ _ _)
  | .Lam x b => rw [pairListWalk.eq_7]; exact (pairListWalk_rel b Γ L).lam
  | .Fix f b =>
    rw [pairListWalk.eq_8]
    cases b with
    | Lam x inner =>
      rw [pairListWalk.eq_7]
      exact (pairListWalk_rel inner Γ L).fix_lam
    | _ =>
      intro env t _ _ _ _ _ hlow
      rw [Moist.Verified.MIR.lowerTotalExpr_fix_nonlam_none env f _ (by intros; simp)] at hlow
      cases hlow
  | .Force b => rw [pairListWalk.eq_9]; exact (pairListWalk_rel b Γ L).force
  | .Delay b => rw [pairListWalk.eq_10]; exact (pairListWalk_rel b Γ L).delay
  | .Constr tag fields =>
    rw [pairListWalk.eq_11]
    exact KnownRel.constr
      (listRel_known_attach_map fields (pairListWalk Γ L) fun a _ => pairListWalk_rel a Γ L)
  | .Var _ => rw [pairListWalk.eq_12]; exact KnownRel.refl _ _ _
  | .Lit _ => rw [pairListWalk.eq_13]; exact KnownRel.refl _ _ _
  | .Builtin _ => rw [pairListWalk.eq_14]; exact KnownRel.refl _ _ _
  | .Error => rw [pairListWalk.eq_15]; exact KnownRel.refl _ _ _
termination_by exprSize e
decreasing_by
  all_goals first
    | (have := fixApplication_inner_size (by assumption); simp only [exprSize] at *; omega)
    | (subst_vars; simp only [exprSize, exprSizeList] at *; omega)
    | (subst_vars; have := exprSize_lt_of_mem (by assumption); simp only [exprSize, exprSizeList] at *; omega)
    | (have bound := fixApplication_size _ _ (by assumption)
       have := bound.2.2 _ (by assumption)
       simp only [exprSize, exprSizeList] at *; omega)
    | (simp only [exprSize]; omega)
    | (simp only [exprSize, exprSizeBinds]; omega)
    | (simp only [exprSize, exprSizeBinds]; have := exprSize_pos r; omega)
    | (have := exprSize_lambdaChain fixBody; simp only [exprSize, exprSizeBinds]; omega)
    | (subst_vars; have := exprSize_lambdaChain fixBody; simp only [exprSize, exprSizeBinds] at *; omega)
    | (subst_vars; simp only [exprSize, exprSizeBinds]; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize, exprSizeList] at *; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)

end Moist.Verified.KnownLists

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced Moist.Verified.ShapeFacts

/-- Destructuring the entries of lists of data pairs refines its input. -/
theorem destructurePairEntries_refines (e : Expr) :
    MIRCtxRefines e (Advanced.destructurePairEntries e) := by
  unfold Advanced.destructurePairEntries
  simp only
  refine mirCtxRefines_trans (prepareHeads_refines e)
    (mirCtxRefines_trans ?_ (PreLower.preLowerInlineExpr_refines _ _))
  split
  · exact mirCtxRefines_of_factRel (by assumption) (fun _ _ => trivial) (fun _ _ => trivial)
      (Moist.Verified.KnownLists.pairListWalk_rel _ [] []).to_factRel
  · exact mirCtxRefines_refl _

end Moist.Verified.MIR
