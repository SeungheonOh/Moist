import Moist.Verified.RecordsSoundness.Alternatives
import Moist.Verified.ProductsSoundness

variable [sv : Moist.CEK.SemVariant]

/-! # Record unpacking

`unpackRecords` replaces the field reads of a record whose recorded shape is
constructor `0` with `n` fields by the binders of one `case` placed at the
lowest node holding all of them. The walk numbers its field binders from a
counter above every identifier of the program; every binder it has not
generated yet is fresh for the environment it runs in (`GenSafe`). Its facts
are the right-hand sides of the bindings it has entered, the projections of
alternative binders whose scrutinee has a known arity, and the field facts of
the records it has unpacked; all of them are sound under `PF`.
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence

theorem PF_push : ∀ env ρ rhs v, Produces env ρ rhs v → freshIn env rhs = true → PF env ρ rhs v :=
  fun _ _ _ _ hp hf => ⟨hp, hf⟩

/-! ## Identifiers -/

omit sv in
theorem maxUidExpr_lambdas_binder : ∀ (binders : List VarId) (body : Expr) (x : VarId), x ∈ binders →
    x.uid ≤ maxUidExpr (lambdas binders body)
  | [], _, _, h => by cases h
  | y :: ys, body, x, h => by
    simp only [lambdas, maxUidExpr]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := maxUidExpr_lambdas_binder ys body x h; omega

omit sv in
theorem maxUidExpr_lambdas_body : ∀ (binders : List VarId) (body : Expr),
    maxUidExpr body ≤ maxUidExpr (lambdas binders body)
  | [], _ => by simp [lambdas]
  | y :: ys, body => by
    simp only [lambdas, maxUidExpr]
    have := maxUidExpr_lambdas_body ys body; omega

omit sv in
theorem maxUidExpr_replaceReads (record : VarId) (fields : List VarId) (M : Nat)
    (hM : ∀ y ∈ fields, y.uid ≤ M) (X : Expr) :
    maxUidExpr (replaceReads record fields X) ≤ max (maxUidExpr X) M := by
  unfold replaceReads
  split
  · rename_i scrutinee alternatives
    split
    · rename_i field hfield
      obtain ⟨w, alt, heq, hw, _⟩ := readOf_spec hfield
      cases heq
      have hwr : w.uid = record.uid := ((VarId.beq_true_iff w record).mp hw).2
      have hy : (fields.getD field record).uid ≤ max record.uid M := by
        rw [List.getD_eq_getElem?_getD]
        cases hf : fields[field]? with
        | none => simp only [Option.getD_none]; omega
        | some y =>
          have := hM y (List.mem_of_getElem? hf)
          simp only [Option.getD_some]; omega
      simp only [maxUidExpr]
      omega
    · rw [attach_map_eq_map]
      have := maxUidExpr_replaceReads record fields M hM scrutinee
      have := maxUidExprList_map_le M (replaceReads record fields) alternatives
        fun y _ => maxUidExpr_replaceReads record fields M hM y
      simp only [maxUidExpr]; omega
  · rename_i y b
    have := maxUidExpr_replaceReads record fields M hM b
    simp only [maxUidExpr]; omega
  · rename_i y b
    have := maxUidExpr_replaceReads record fields M hM b
    simp only [maxUidExpr]; omega
  · rename_i b
    have := maxUidExpr_replaceReads record fields M hM b
    simp only [maxUidExpr]; omega
  · rename_i b
    have := maxUidExpr_replaceReads record fields M hM b
    simp only [maxUidExpr]; omega
  · rename_i f a
    have := maxUidExpr_replaceReads record fields M hM f
    have := maxUidExpr_replaceReads record fields M hM a
    simp only [maxUidExpr]; omega
  · rename_i tag fieldExprs
    rw [attach_map_eq_map]
    have := maxUidExprList_map_le M (replaceReads record fields) fieldExprs
      fun y _ => maxUidExpr_replaceReads record fields M hM y
    simp only [maxUidExpr]; omega
  · rename_i bindings body
    rw [binds_attach_map]
    have := maxUidExpr_replaceReads record fields M hM body
    have := maxUidExprBinds_map_le M (replaceReads record fields) bindings
      fun b _ => maxUidExpr_replaceReads record fields M hM b.2.1
    simp only [maxUidExpr] at *; omega
  all_goals omega
termination_by exprSize X
decreasing_by
  all_goals first
    | (subst_vars; simp only [exprSize]; omega)
    | (subst_vars; have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)
    | (subst_vars; have := exprSizeBinds_mem_lt (by assumption); simp only [exprSize]; omega)

/-! ## Weakening the alternatives -/

theorem AltRel.weaken {G G' : VarId → Prop} {Γ : List (VarId × Expr)} {scrut alt alt' : Expr}
    {tag : Nat} (h : AltRel G PF Γ scrut tag alt alt') (hGG : ∀ y, G' y → G y)
    (hbind : ∀ x : VarId, x.uid ≤ maxUidExpr alt → G' x) : AltRel G' PF Γ scrut tag alt alt' := by
  rcases h with h | ⟨shapes, binders, body, body', hs, hlen, rfl, rfl, _, hb⟩
  · exact .inl (h.weaken hGG)
  · exact .inr ⟨shapes, binders, body, body', hs, hlen, rfl, rfl,
      fun x hx => hbind x (maxUidExpr_lambdas_binder binders body x hx), hb.weaken hGG⟩

theorem AltsRel.weaken {G G' : VarId → Prop} {Γ : List (VarId × Expr)} {scrut : Expr}
    (hGG : ∀ y, G' y → G y) :
    ∀ {tag : Nat} {alts alts' : List Expr}, (∀ x : VarId, x.uid ≤ maxUidExprList alts → G' x) →
      AltsRel G PF Γ scrut tag alts alts' → AltsRel G' PF Γ scrut tag alts alts'
  | _, [], [], _, _ => trivial
  | _, a :: as, b :: bs, hbind, h => by
    refine ⟨h.1.weaken hGG fun x hx => hbind x (by simp only [maxUidExprList]; omega),
      AltsRel.weaken hGG (fun x hx => hbind x (by simp only [maxUidExprList]; omega)) h.2⟩
  | _, [], _ :: _, _, h => by simp [AltsRel] at h
  | _, _ :: _, [], _, h => by simp [AltsRel] at h

/-! ## The walk -/

omit sv in
theorem splitsAt_lam (x : VarId) (inner : Expr) (candidate : VarId × Nat) :
    splitsAt (.Lam x inner) candidate = false := by
  unfold splitsAt
  simp only [readChildren, decide_eq_false_iff_not, Nat.not_le]
  apply Nat.lt_of_le_of_lt (List.length_filter_le _ _)
  simp

omit sv in
/-- The walk never unpacks at a lambda: its reads all lie in its body. -/
theorem recordWalk_lam (Γ : List (VarId × Expr)) (candidates : List (VarId × Nat)) (x : VarId)
    (inner : Expr) (next : Nat) :
    recordWalk Γ candidates (.Lam x inner) next =
      (.Lam x (recordWalk Γ (keepFor (candidates.filter fun c => !splitsAt (.Lam x inner) c) inner)
        inner next).1,
       (recordWalk Γ (keepFor (candidates.filter fun c => !splitsAt (.Lam x inner) c) inner)
        inner next).2) := by
  rw [recordWalk]
  have hnone : candidates.filter (splitsAt (.Lam x inner)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro c _
    simp [splitsAt_lam]
  rw [hnone, recordUnpack, recordDescend]

mutual
  theorem recordWalk_factRel (Γ : List (VarId × Expr)) (candidates : List (VarId × Nat)) (e : Expr)
      (next : Nat) (hmax : maxUidExpr e < next) :
      FactRel (GenSafe next) PF Γ e (recordWalk Γ candidates e next).1 ∧
        next ≤ (recordWalk Γ candidates e next).2 := by
    rw [recordWalk]
    exact recordUnpack_factRel Γ _ _ e next hmax
  termination_by (exprSize e, 2, 0)
  decreasing_by exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))

  theorem recordUnpack_factRel (Γ : List (VarId × Expr)) (todo candidates : List (VarId × Nat))
      (e : Expr) (next : Nat) (hmax : maxUidExpr e < next) :
      FactRel (GenSafe next) PF Γ e (recordUnpack Γ todo candidates e next).1 ∧
        next ≤ (recordUnpack Γ todo candidates e next).2 := by
    match todo with
    | [] =>
      rw [recordUnpack]
      exact recordDescend_factRel Γ candidates e next hmax
    | (record, arity) :: rest =>
      rw [recordUnpack]
      split
      · rename_i hknown
        have hmem : ∀ y ∈ freshFields next arity, next ≤ y.uid ∧ y.uid < next + arity ∧ y.origin = .gen :=
          fun y hy => freshFields_mem hy
        have hX := maxUidExpr_replaceReads record (freshFields next arity) (next + arity - 1)
          (fun y hy => by have := hmem y hy; omega) e
        have ih := recordUnpack_factRel (fieldFacts record (freshFields next arity) ++ Γ) rest
          candidates (replaceReads record (freshFields next arity) e) (next + arity) (by omega)
        refine ⟨unpack_factRel PF_hP PF_push (genSafe_mono (by omega))
          (fun y hy => .inl (hmem y hy).2.1)
          (fun y hy => not_genSafe (hmem y hy).1 (hmem y hy).2.2)
          (freshFields_distinct next arity) (fun y hy => by have := hmem y hy; omega)
          (by rw [freshFields_length]; exact hknown) ih.1, ?_⟩
        dsimp only
        omega
      · exact recordUnpack_factRel Γ rest candidates e next hmax
  termination_by (exprSize e, 1, todo.length)
  decreasing_by
    all_goals first
      | (have := exprSize_replaceReads record (freshFields next arity) e
         rcases Nat.lt_or_eq_of_le this with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (Prod.Lex.right _ (by simp)))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by simp))
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))

  theorem recordDescend_factRel (Γ : List (VarId × Expr)) (candidates : List (VarId × Nat)) (e : Expr)
      (next : Nat) (hmax : maxUidExpr e < next) :
      FactRel (GenSafe next) PF Γ e (recordDescend Γ candidates e next).1 ∧
        next ≤ (recordDescend Γ candidates e next).2 := by
    match e with
    | .Let [] body =>
      rw [recordDescend]
      simp only [maxUidExpr, maxUidExprBinds] at hmax
      have ih := recordWalk_factRel Γ (keepFor candidates body) body next (by omega)
      exact ⟨ih.1.congr_left (fun env => lowerTotalExpr_let_nil env body)
        (fun avoid => freshIn_let_nil avoid body), ih.2⟩
    | .Let ((x, r, er) :: rest) body =>
      have hrpos := exprSize_pos r
      rw [recordDescend]
      simp only [maxUidExpr, maxUidExprBinds] at hmax
      have ihr := recordWalk_factRel Γ (keepFor candidates r) r next (by omega)
      have ihrest := recordWalk_factRel ((x, r) :: Γ)
        (recordCandidate ((x, r) :: Γ) x (.Let rest body) ++ keepFor candidates (.Let rest body))
        (.Let rest body) (recordWalk Γ (keepFor candidates r) r next).2
        (by simp only [maxUidExpr]; omega)
      refine ⟨(FactRel.let_single (er := er) r (.inl (by omega)) (.inl rfl) ihr.1
        (ihrest.1.weaken (genSafe_mono ihr.2))
        (fun env ρ v _ _ hfr hp => PF_push env ρ r v hp hfr)).congr_left
        (fun env => lowerTotalExpr_let_cons env _ _ _) (fun avoid => freshIn_let_cons avoid _ _ _), ?_⟩
      dsimp only
      omega
    | .Lam x b =>
      rw [recordDescend]
      simp only [maxUidExpr] at hmax
      have ih := recordWalk_factRel Γ (keepFor candidates b) b next (by omega)
      exact ⟨ih.1.lam (.inl (by omega)), ih.2⟩
    | .Fix f b =>
      rw [recordDescend]
      simp only [maxUidExpr] at hmax
      have ih := recordWalk_factRel Γ (keepFor candidates b) b next (by omega)
      refine ⟨?_, ih.2⟩
      cases hb : b with
      | Lam x inner =>
        subst hb
        simp only [maxUidExpr] at hmax
        rw [recordWalk_lam]
        have ihi := recordWalk_factRel Γ (keepFor ((keepFor candidates (.Lam x inner)).filter
          fun c => !splitsAt (.Lam x inner) c) inner) inner next (by omega)
        exact ihi.1.fix_lam (.inl (by omega)) (.inl (by omega)) (fun y hy => .inr (by rw [hy]; simp))
      | _ =>
        intro env t _ _ _ _ _ hlow
        rw [MIR.lowerTotalExpr_fix_nonlam_none env f _ (by intros; simp)] at hlow
        cases hlow
    | .App fn a =>
      rw [recordDescend]
      simp only [maxUidExpr] at hmax
      have ihf := recordWalk_factRel Γ (keepFor candidates fn) fn next (by omega)
      have iha := recordWalk_factRel Γ (keepFor candidates a) a
        (recordWalk Γ (keepFor candidates fn) fn next).2 (by omega)
      exact ⟨ihf.1.app (iha.1.weaken (genSafe_mono ihf.2)), by dsimp only; omega⟩
    | .Force b =>
      rw [recordDescend]
      simp only [maxUidExpr] at hmax
      have ih := recordWalk_factRel Γ (keepFor candidates b) b next (by omega)
      exact ⟨ih.1.force, ih.2⟩
    | .Delay b =>
      rw [recordDescend]
      simp only [maxUidExpr] at hmax
      have ih := recordWalk_factRel Γ (keepFor candidates b) b next (by omega)
      exact ⟨ih.1.delay, ih.2⟩
    | .Constr tag fields =>
      rw [recordDescend]
      simp only [maxUidExpr] at hmax
      have ih := recordWalkList_factRel Γ candidates fields next (by omega)
      exact ⟨FactRel.constr ih.1, ih.2⟩
    | .Case scrutinee alternatives =>
      rw [recordDescend]
      simp only [maxUidExpr] at hmax
      have ihs := recordWalk_factRel Γ (keepFor candidates scrutinee) scrutinee next (by omega)
      have iha := recordAlternatives_factRel Γ candidates scrutinee
        (shapeOf recordFuel recordDepth Γ scrutinee) rfl 0 alternatives
        (recordWalk Γ (keepFor candidates scrutinee) scrutinee next).2 (by omega)
      exact ⟨FactRel.case_alternatives PF_hP PF_push ihs.1
        (AltsRel.weaken (genSafe_mono ihs.2) (fun x hx => .inl (by omega)) iha.1), by dsimp only; omega⟩
    | .Var _ | .Lit _ | .Builtin _ | .Error =>
      rw [recordDescend]; exact ⟨FactRel.refl _ _ _ _, Nat.le_refl _⟩
  termination_by (exprSize e, 0, 0)
  decreasing_by
    all_goals first
      | (apply Prod.Lex.left; simp only [exprSize, exprSizeBinds]; omega)
      | (apply Prod.Lex.left; subst_vars; simp only [exprSize]; omega)

  theorem recordWalkList_factRel (Γ : List (VarId × Expr)) (candidates : List (VarId × Nat))
      (es : List Expr) (next : Nat) (hmax : maxUidExprList es < next) :
      ListRel (FactRel (GenSafe next) PF Γ) es (recordWalkList Γ candidates es next).1 ∧
        next ≤ (recordWalkList Γ candidates es next).2 := by
    match es with
    | [] => rw [recordWalkList]; exact ⟨trivial, Nat.le_refl _⟩
    | e :: rest =>
      have hsize : exprSize e ≤ exprSizeList (e :: rest) := by simp only [exprSizeList]; omega
      have hrest : exprSizeList rest < exprSizeList (e :: rest) := by
        simp only [exprSizeList]; have := exprSize_pos e; omega
      rw [recordWalkList]
      simp only [maxUidExprList] at hmax
      have ihe := recordWalk_factRel Γ (keepFor candidates e) e next (by omega)
      have ihr := recordWalkList_factRel Γ candidates rest
        (recordWalk Γ (keepFor candidates e) e next).2 (by omega)
      exact ⟨⟨ihe.1, listRel_weaken (genSafe_mono ihe.2) ihr.1⟩, by dsimp only; omega⟩
  termination_by (exprSizeList es, 3, 0)
  decreasing_by
    all_goals first
      | exact Prod.Lex.left _ _ hrest
      | (rcases Nat.lt_or_eq_of_le hsize with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega)))

  theorem recordAlternatives_factRel (Γ : List (VarId × Expr)) (candidates : List (VarId × Nat))
      (scrutinee : Expr) (shape : Shape) (hshape : shape = shapeOf recordFuel recordDepth Γ scrutinee)
      (tag : Nat) (alternatives : List Expr) (next : Nat) (hmax : maxUidExprList alternatives < next) :
      AltsRel (GenSafe next) PF Γ scrutinee tag alternatives
          (recordAlternatives Γ candidates scrutinee shape tag alternatives next).1 ∧
        next ≤ (recordAlternatives Γ candidates scrutinee shape tag alternatives next).2 := by
    match alternatives with
    | [] => rw [recordAlternatives]; exact ⟨trivial, Nat.le_refl _⟩
    | alternative :: rest =>
      have hsize : exprSize alternative ≤ exprSizeList (alternative :: rest) := by
        simp only [exprSizeList]; omega
      have hrest : exprSizeList rest < exprSizeList (alternative :: rest) := by
        simp only [exprSizeList]; have := exprSize_pos alternative; omega
      rw [recordAlternatives]
      simp only [maxUidExprList] at hmax
      have iha := recordAlternative_factRel Γ candidates scrutinee shape hshape tag alternative next
        (by omega)
      have ihr := recordAlternatives_factRel Γ candidates scrutinee shape hshape (tag + 1) rest
        (recordAlternative Γ candidates scrutinee shape tag alternative next).2 (by omega)
      exact ⟨⟨iha.1, AltsRel.weaken (genSafe_mono iha.2) (fun x hx => .inl (by omega)) ihr.1⟩,
        by dsimp only; omega⟩
  termination_by (exprSizeList alternatives, 4, 0)
  decreasing_by
    all_goals first
      | exact Prod.Lex.left _ _ hrest
      | (rcases Nat.lt_or_eq_of_le hsize with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega)))

  theorem recordAlternative_factRel (Γ : List (VarId × Expr)) (candidates : List (VarId × Nat))
      (scrutinee : Expr) (shape : Shape) (hshape : shape = shapeOf recordFuel recordDepth Γ scrutinee)
      (tag : Nat) (alternative : Expr) (next : Nat) (hmax : maxUidExpr alternative < next) :
      AltRel (GenSafe next) PF Γ scrutinee tag alternative
          (recordAlternative Γ candidates scrutinee shape tag alternative next).1 ∧
        next ≤ (recordAlternative Γ candidates scrutinee shape tag alternative next).2 := by
    rw [recordAlternative]
    split
    · rename_i shapes hat
      split
      · rename_i binders body hstrip
        obtain ⟨hshape', hblen⟩ := stripLams_spec _ _ _ _ hstrip
        split
        · have hbody : maxUidExpr body < next := by
            have := maxUidExpr_lambdas_body binders body
            rw [← hshape'] at this; omega
          have ih := recordWalk_factRel (alternativeFacts scrutinee tag binders ++ Γ)
            (recordCandidates (alternativeFacts scrutinee tag binders ++ Γ) binders body ++
              keepFor candidates body) body next hbody
          refine ⟨.inr ⟨shapes, binders, body, _, by rw [← hshape]; exact hat, hblen, hshape', rfl,
            fun x hx => .inl (by
              have := maxUidExpr_lambdas_binder binders body x hx
              rw [← hshape'] at this; omega), ih.1⟩, ih.2⟩
        · have ih := recordWalk_factRel Γ (keepFor candidates alternative) alternative next hmax
          exact ⟨.inl ih.1, ih.2⟩
      · have ih := recordWalk_factRel Γ (keepFor candidates alternative) alternative next hmax
        exact ⟨.inl ih.1, ih.2⟩
    · have ih := recordWalk_factRel Γ (keepFor candidates alternative) alternative next hmax
      exact ⟨.inl ih.1, ih.2⟩
  termination_by (exprSize alternative, 3, 0)
  decreasing_by
    all_goals first
      | (apply Prod.Lex.left
         obtain ⟨_, h⟩ := stripLams_size _ _ _ _ (by assumption)
         omega)
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
end

end Moist.Verified.ShapeFacts

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced Moist.Verified.ShapeFacts

/-- Record unpacking refines its input. -/
theorem unpackRecords_refines (e : Expr) : MIRCtxRefines e (Advanced.unpackRecords e) := by
  unfold Advanced.unpackRecords
  simp only
  refine mirCtxRefines_trans (Hygiene.uniqueOptimizationBinders_refines e)
    (mirCtxRefines_trans ?_ (PreLower.preLowerInlineExpr_refines _ _))
  split
  · rename_i hws
    exact mirCtxRefines_of_factRel hws
      (fun y hy => .inl (by have := freeVars_uid_lt hy; omega))
      (fun y hy => .inr (by rw [hy]; simp))
      (recordWalk_factRel [] [] _ _ (by omega)).1
  · exact mirCtxRefines_refl _

end Moist.Verified.MIR
