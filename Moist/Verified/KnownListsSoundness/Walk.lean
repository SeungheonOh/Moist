import Moist.Verified.KnownListsSoundness.FixApp

/-! # The known-list walk

Every node of `knownListWalk` keeps its shape (congruence), fuses a
`nullList` discriminator into a list `case` on a known list
(`KnownRel.nullFuse`), records the tail of a `case` on a known list
(`KnownRel.listCase`), or transforms a recursive function applied to known
lists under list facts for its parameters (`KnownRel.fixApp`).
-/

namespace Moist.Verified.KnownLists

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.ShapeFacts

/-! ## Recursive applications -/

theorem fixApplication_eq : ∀ (e : Expr) (acc : List Expr) {f x : VarId} {body : Expr}
    {args : List Expr}, fixApplication e acc = some (f, x, body, args) →
      Advanced.applyAll e acc = Advanced.applyAll (.Fix f (.Lam x body)) args
  | .App g a, acc, f, x, body, args, h => by
    simp only [fixApplication] at h
    rw [← fixApplication_eq g (a :: acc) h]; rfl
  | .Fix f' (.Lam x' body'), acc, f, x, body, args, h => by
    simp only [fixApplication] at h
    split at h
    · cases h
    · cases h; rfl
  | .Var _, _, _, _, _, _, h | .Lit _, _, _, _, _, _, h | .Builtin _, _, _, _, _, _, h
  | .Error, _, _, _, _, _, h | .Lam _ _, _, _, _, _, _, h | .Force _, _, _, _, _, _, h
  | .Delay _, _, _, _, _, _, h | .Constr _ _, _, _, _, _, _, h | .Case _ _, _, _, _, _, _, h
  | .Let _ _, _, _, _, _, _, h => by simp [fixApplication] at h
  | .Fix _ (.Var _), _, _, _, _, _, h | .Fix _ (.Lit _), _, _, _, _, _, h
  | .Fix _ (.Builtin _), _, _, _, _, _, h | .Fix _ .Error, _, _, _, _, _, h
  | .Fix _ (.Fix _ _), _, _, _, _, _, h | .Fix _ (.App _ _), _, _, _, _, _, h
  | .Fix _ (.Force _), _, _, _, _, _, h | .Fix _ (.Delay _), _, _, _, _, _, h
  | .Fix _ (.Constr _ _), _, _, _, _, _, h | .Fix _ (.Case _ _), _, _, _, _, _, h
  | .Fix _ (.Let _ _), _, _, _, _, _, h => by simp [fixApplication] at h

theorem fixApplication_args_ne : ∀ (e : Expr) (acc : List Expr) {f x : VarId} {body : Expr}
    {args : List Expr}, fixApplication e acc = some (f, x, body, args) → args ≠ []
  | .App g a, acc, f, x, body, args, h => by
    simp only [fixApplication] at h
    exact fixApplication_args_ne g (a :: acc) h
  | .Fix f' (.Lam x' body'), acc, f, x, body, args, h => by
    simp only [fixApplication] at h
    split at h
    · cases h
    · cases h
      rename_i hne
      simpa using hne
  | .Var _, _, _, _, _, _, h | .Lit _, _, _, _, _, _, h | .Builtin _, _, _, _, _, _, h
  | .Error, _, _, _, _, _, h | .Lam _ _, _, _, _, _, _, h | .Force _, _, _, _, _, _, h
  | .Delay _, _, _, _, _, _, h | .Constr _ _, _, _, _, _, _, h | .Case _ _, _, _, _, _, _, h
  | .Let _ _, _, _, _, _, _, h => by simp [fixApplication] at h
  | .Fix _ (.Var _), _, _, _, _, _, h | .Fix _ (.Lit _), _, _, _, _, _, h
  | .Fix _ (.Builtin _), _, _, _, _, _, h | .Fix _ .Error, _, _, _, _, _, h
  | .Fix _ (.Fix _ _), _, _, _, _, _, h | .Fix _ (.App _ _), _, _, _, _, _, h
  | .Fix _ (.Force _), _, _, _, _, _, h | .Fix _ (.Delay _), _, _, _, _, _, h
  | .Fix _ (.Constr _ _), _, _, _, _, _, h | .Fix _ (.Case _ _), _, _, _, _, _, h
  | .Fix _ (.Let _ _), _, _, _, _, _, h => by simp [fixApplication] at h

theorem stable_spec (lists : List VarId) (f : VarId) (params : List VarId) (body : Expr) :
    ∀ (fuel : Nat) (ps : List Nat),
      listPositions.stable lists f params body fuel ps = [] ∨
        ((∀ p ∈ listPositions.stable lists f params body fuel ps, p ∈ ps) ∧
          listCallsOK f params.length (listPositions.stable lists f params body fuel ps)
            (listedParameters params (listPositions.stable lists f params body fuel ps) ++ lists)
            body = true)
  | 0, ps => .inl (by simp [listPositions.stable])
  | fuel + 1, ps => by
    simp only [listPositions.stable]
    split
    · exact .inl rfl
    · split
      · split
        · rename_i h
          exact .inr ⟨fun p hp => hp, h⟩
        · exact .inl rfl
      · rcases stable_spec lists f params body fuel _ with h | ⟨hsub, hcheck⟩
        · exact .inl h
        · refine .inr ⟨fun p hp => ?_, hcheck⟩
          exact (List.mem_filter.mp (hsub p hp)).1

theorem listPositions_spec {env : List (VarId × Expr)} {lists : List VarId} {f : VarId}
    {params : List VarId} {args : List Expr} {body : Expr}
    (hne : listPositions env lists f params args body ≠ []) :
    params.length ≤ args.length ∧
      (∀ p ∈ listPositions env lists f params args body,
        ∃ a, args[p]? = some a ∧ listKnown env lists a = true) ∧
      listCallsOK f params.length (listPositions env lists f params args body)
        (listedParameters params (listPositions env lists f params args body) ++ lists) body = true := by
  unfold listPositions at hne ⊢
  split
  · rename_i h; simp [h] at hne
  · rename_i h
    simp only [h, if_false] at hne
    refine ⟨by omega, ?_⟩
    rcases stable_spec lists f params body _ _ with h' | ⟨hsub, hcheck⟩
    · exact absurd h' hne
    · refine ⟨fun p hp => ?_, hcheck⟩
      have := (List.mem_filter.mp (hsub p hp)).2
      revert this
      cases ha : args[p]? with
      | none => simp
      | some a => intro hk; exact ⟨a, rfl, by simpa using hk⟩

theorem beq_nullList {x : Expr} (h : (x == Expr.Force (.Builtin .NullList)) = true) :
    x = .Force (.Builtin .NullList) := by
  cases x with
  | Force e =>
    cases e with
    | Builtin b' =>
      have : (b' == BuiltinFun.NullList) = true := h
      cases b' <;> first | rfl | cases this
    | _ => cases h
  | _ => cases h

theorem listedParameters_nil (params : List VarId) : listedParameters params [] = [] := rfl

theorem knownListWalk_rel (e : Expr) (Γ : List (VarId × Expr)) (L : List VarId) :
    KnownRel Γ L e (knownListWalk Γ L e) := by
  match e with
  | .App function argument =>
    rw [knownListWalk.eq_1]
    split
    · rename_i recursive parameter body arguments hfix
      simp only
      have heq : Expr.App function argument = Advanced.applyAll (.Fix recursive
          (Advanced.lambdaWrap (parameter :: (lambdaChain body).1) (lambdaChain body).2)) arguments := by
        have := fixApplication_eq _ [] hfix
        simp only [Advanced.applyAll] at this
        rw [this, Advanced.lambdaWrap, lambdaChain_wrap]
      rw [heq]
      have hargs : ListRel (KnownRel Γ L) arguments
          (arguments.attach.map fun ⟨a, _⟩ => knownListWalk Γ L a) :=
        listRel_known_attach_map arguments (knownListWalk Γ L) fun a _ => knownListWalk_rel a Γ L
      by_cases hP : listPositions Γ L recursive (parameter :: (lambdaChain body).1) arguments
          (lambdaChain body).2 = []
      · rw [hP, listedParameters_nil, List.nil_append]
        refine KnownRel.applyAll ?_ hargs
        simp only [Advanced.lambdaWrap]
        exact (KnownRel.lambdaWrap _ (knownListWalk_rel (lambdaChain body).2 Γ L)).fix_lam
      · obtain ⟨hlen, hpos, hcheck⟩ := listPositions_spec hP
        exact KnownRel.fixApp (by simp) hlen hargs hpos hcheck
          (knownListWalk_rel (lambdaChain body).2 Γ _)
    · exact (knownListWalk_rel function Γ L).app (knownListWalk_rel argument Γ L)
  | .Case scrutinee alternatives =>
    by_cases hA : ∃ sel l ne em, scrutinee = .App sel (.Var l) ∧ alternatives = [ne, em]
    · obtain ⟨sel, l, ne, em, rfl, rfl⟩ := hA
      by_cases hN : ∃ inner hd tl body rest, ne = .Case (.Var inner) (.Lam hd (.Lam tl body) :: rest)
      · obtain ⟨inner, hd, tl, body, rest, rfl⟩ := hN
        rw [knownListWalk.eq_2]
        split
        · rename_i hcond
          simp only [Bool.and_eq_true] at hcond
          split
          · rename_i hcond'
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond'
            exact KnownRel.nullFuse (beq_nullList hcond.1) hcond.2 hcond'.1 hcond'.2
              (knownListWalk_rel body Γ (tl :: L)) (knownListWalk_rel em Γ L)
          · exact KnownRel.case (knownListWalk_rel _ Γ L)
              ⟨knownListWalk_rel _ Γ L, knownListWalk_rel em Γ L, trivial⟩
        · exact KnownRel.case (knownListWalk_rel _ Γ L)
            ⟨knownListWalk_rel _ Γ L, knownListWalk_rel em Γ L, trivial⟩
      · rw [knownListWalk.eq_3 _ _ _ _ _ _ (fun inner hd tl body rest _ h _ =>
          hN ⟨inner, hd, tl, body, rest, h⟩)]
        split
        · exact KnownRel.case (knownListWalk_rel _ Γ L)
            ⟨knownListWalk_rel ne Γ L, knownListWalk_rel em Γ L, trivial⟩
        · exact KnownRel.case (knownListWalk_rel _ Γ L)
            ⟨knownListWalk_rel ne Γ L, knownListWalk_rel em Γ L, trivial⟩
    · by_cases hB : ∃ l hd tl body rest, scrutinee = .Var l ∧
          alternatives = .Lam hd (.Lam tl body) :: rest
      · obtain ⟨l, hd, tl, body, rest, rfl, rfl⟩ := hB
        rw [knownListWalk.eq_4]
        split
        · rename_i hl
          exact KnownRel.listCase hl (knownListWalk_rel body Γ (tl :: L))
            (listRel_known_attach_map rest (knownListWalk Γ L) fun a _ => knownListWalk_rel a Γ L)
        · exact KnownRel.case (knownListWalk_rel _ Γ L)
            (listRel_known_attach_map _ (knownListWalk Γ L) fun a _ => knownListWalk_rel a Γ L)
      · rw [knownListWalk.eq_5 _ _ _ _ (fun sel l ne em h₁ h₂ => hA ⟨sel, l, ne, em, h₁, h₂⟩)
          (fun l hd tl body rest h₁ h₂ => hB ⟨l, hd, tl, body, rest, h₁, h₂⟩)]
        exact KnownRel.case (knownListWalk_rel scrutinee Γ L)
          (listRel_known_attach_map alternatives (knownListWalk Γ L) fun a _ => knownListWalk_rel a Γ L)
  | .Let [] body =>
    rw [knownListWalk.eq_6]
    exact (knownListWalk_rel body Γ L).congr_left (fun env => lowerTotalExpr_let_nil env body)
      (fun avoid => freshIn_let_nil avoid body)
  | .Let ((x, r, er) :: rest) body =>
    rw [knownListWalk.eq_7]
    exact (KnownRel.let_single (knownListWalk Γ L r) (.inr rfl) (knownListWalk_rel r Γ L)
      (knownListWalk_rel (.Let rest body) _ L)).congr_left
      (fun env => lowerTotalExpr_let_cons env _ _ _) (fun avoid => freshIn_let_cons avoid _ _ _)
  | .Lam x b => rw [knownListWalk.eq_8]; exact (knownListWalk_rel b Γ L).lam
  | .Fix f b =>
    rw [knownListWalk.eq_9]
    cases b with
    | Lam x inner =>
      rw [knownListWalk.eq_8]
      exact (knownListWalk_rel inner Γ L).fix_lam
    | _ =>
      intro env t _ _ _ _ _ hlow
      rw [Moist.Verified.MIR.lowerTotalExpr_fix_nonlam_none env f _ (by intros; simp)] at hlow
      cases hlow
  | .Force b => rw [knownListWalk.eq_10]; exact (knownListWalk_rel b Γ L).force
  | .Delay b => rw [knownListWalk.eq_11]; exact (knownListWalk_rel b Γ L).delay
  | .Constr tag fields =>
    rw [knownListWalk.eq_12]
    exact KnownRel.constr
      (listRel_known_attach_map fields (knownListWalk Γ L) fun a _ => knownListWalk_rel a Γ L)
  | .Var _ => rw [knownListWalk.eq_13]; exact KnownRel.refl _ _ _
  | .Lit _ => rw [knownListWalk.eq_14]; exact KnownRel.refl _ _ _
  | .Builtin _ => rw [knownListWalk.eq_15]; exact KnownRel.refl _ _ _
  | .Error => rw [knownListWalk.eq_16]; exact KnownRel.refl _ _ _
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
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize, exprSizeList] at *; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)

/-- Fusing `nullList` discriminators of known lists refines its input. -/
theorem fuseKnownListCases_factRel {e : Expr} :
    KnownRel [] [] e (knownListWalk [] [] e) := knownListWalk_rel e [] []

end Moist.Verified.KnownLists
