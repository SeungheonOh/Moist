import Moist.Verified.RecordsSoundness.Binders

/-! # Unpacking a record once

When the recorded shape of `record` is constructor `0` with `n` fields,
`e` refines `case record [λy₁…yₙ. e']` for every `e'` that refines `e` with
its reads replaced by the field binders under the field facts
(`unpack_factRel`). The record is a constructor with exactly `n` fields, so
the unpacking case binds them without failing, after which the original
term runs unchanged in the extended environment.

The binders of a `case` alternative may also be entered with facts: when
the shape of the scrutinee fixes the number of fields at the tag of the
alternative, each binder holds the corresponding field, recorded as a
projection of the scrutinee (`FactRel.case_alternatives`).
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.BetaValueRefines
open Moist.Verified.Contextual

variable {P : List VarId → CekEnv → Expr → CekValue → Prop}

/-! ## Freshness and lowering after new binders -/

theorem freshInList_map_of {avoid : List VarId} (f : Expr → Expr) :
    ∀ (xs : List Expr), (∀ x ∈ xs, freshIn avoid x = true → freshIn avoid (f x) = true) →
      freshInList avoid xs = true → freshInList avoid (xs.map f) = true
  | [], _, _ => by simp [freshInList]
  | x :: xs, h, hx => by
    simp only [freshInList, Bool.and_eq_true, List.map_cons] at hx ⊢
    exact ⟨h x (.head _) hx.1, freshInList_map_of f xs (fun y hy => h y (.tail _ hy)) hx.2⟩

theorem freshInLet_map_of (f : Expr → Expr) :
    ∀ (bs : List (VarId × Expr × Bool)) (body : Expr) (avoid : List VarId),
      (∀ b ∈ bs, ∀ avoid, freshIn avoid b.2.1 = true → freshIn avoid (f b.2.1) = true) →
      (∀ avoid, freshIn avoid body = true → freshIn avoid (f body) = true) →
      freshInLet avoid bs body = true →
      freshInLet avoid (bs.map fun (y, rhs, er) => (y, f rhs, er)) (f body) = true
  | [], body, avoid, _, hbody, h => by
    simp only [List.map_nil, freshInLet] at h ⊢; exact hbody avoid h
  | (y, r, er) :: rest, body, avoid, hbs, hbody, h => by
    simp only [List.map_cons, freshInLet, Bool.and_eq_true] at h ⊢
    exact ⟨⟨hbs (y, r, er) (.head _) avoid h.1.1, h.1.2⟩,
      freshInLet_map_of f rest body (y :: avoid) (fun b hb => hbs b (.tail _ hb)) hbody h.2⟩

theorem freshIn_replaceReads (record : VarId) (fields : List VarId) (X : Expr) :
    ∀ avoid, freshIn avoid X = true → freshIn avoid (replaceReads record fields X) = true := by
  intro avoid h
  unfold replaceReads
  split
  · rename_i scrutinee alternatives
    split
    · simp [freshIn]
    · simp only [freshIn, Bool.and_eq_true] at h ⊢
      rw [attach_map_eq_map]
      exact ⟨freshIn_replaceReads record fields scrutinee avoid h.1,
        freshInList_map_of _ alternatives (fun c _ hc => freshIn_replaceReads record fields c avoid hc) h.2⟩
  · rename_i y b
    simp only [freshIn, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, freshIn_replaceReads record fields b _ h.2⟩
  · rename_i y b
    simp only [freshIn, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, freshIn_replaceReads record fields b _ h.2⟩
  · rename_i b
    simp only [freshIn] at h ⊢
    exact freshIn_replaceReads record fields b _ h
  · rename_i b
    simp only [freshIn] at h ⊢
    exact freshIn_replaceReads record fields b _ h
  · rename_i f a
    simp only [freshIn, Bool.and_eq_true] at h ⊢
    exact ⟨freshIn_replaceReads record fields f _ h.1, freshIn_replaceReads record fields a _ h.2⟩
  · rename_i tag fieldExprs
    simp only [freshIn] at h ⊢
    rw [attach_map_eq_map]
    exact freshInList_map_of _ fieldExprs (fun c _ hc => freshIn_replaceReads record fields c avoid hc) h
  · rename_i bindings body
    simp only [freshIn] at h ⊢
    rw [binds_attach_map]
    exact freshInLet_map_of _ bindings body avoid
      (fun b _ avoid hb => freshIn_replaceReads record fields b.2.1 avoid hb)
      (fun avoid hb => freshIn_replaceReads record fields body avoid hb) h
  all_goals exact h
termination_by exprSize X
decreasing_by
  all_goals first
    | (subst_vars; simp only [exprSize]; omega)
    | (subst_vars; have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)
    | (subst_vars; have := exprSizeBinds_mem_lt (by assumption); simp only [exprSize] at *; omega)

theorem freshIn_append_big {env : List VarId} {X : Expr} (hX : freshIn env X = true) :
    ∀ (names : List VarId), (∀ y ∈ names, maxUidExpr X < y.uid) → freshIn (names ++ env) X = true
  | [], _ => by simpa using hX
  | y :: ys, h => by
    rw [List.cons_append]
    exact freshIn_cons_of_big (freshIn_append_big hX ys fun z hz => h z (.tail _ hz)) (h y (.head _))

theorem lowerTotalExpr_append_unused {env : List VarId} {e : Expr} {t : Term}
    (ht : lowerTotalExpr env e = some t) :
    ∀ (names : List VarId), (∀ y ∈ names, (freeVars e).contains y = false) →
      ∃ t', lowerTotalExpr (names ++ env) e = some t'
  | [], _ => ⟨t, by simpa using ht⟩
  | y :: ys, h => by
    obtain ⟨t', ht'⟩ := lowerTotalExpr_append_unused ht ys fun z hz => h z (.tail _ hz)
    refine ⟨renameTerm (shiftRename 1) t', ?_⟩
    rw [List.cons_append, MIR.lowerTotalExpr_prepend_unused _ y e (h y (.head _)), ht']; rfl

/-! ## The field facts -/

theorem fieldFacts_eq (record : VarId) (fields : List VarId) :
    fieldFacts record fields =
      fields.reverse.zip (fields.reverse.map (fieldProjection record fields)) := by
  rw [fieldFacts, zip_map_self]

theorem freshIn_fieldProjection {env : List VarId} {record y : VarId} {fields : List VarId}
    (hdistinct : NamesDistinct fields) (hout : ∀ z ∈ fields, envLookupT env z = none) (hy : y ∈ fields) :
    freshIn env (fieldProjection record fields y) = true := by
  have h1 : freshIn env (lambdas fields (.Constr 0 [.Var y])) = true :=
    freshIn_lambdas_of hdistinct hout (by simp [freshIn, freshInList])
  have h2 : (envLookupT env y).isNone = true := by rw [hout y hy]; rfl
  unfold fieldProjection
  simp [freshIn, freshInList, h1, h2]

theorem fieldFacts_find {record : VarId} {fields : List VarId} (hdistinct : NamesDistinct fields)
    (Γ : List (VarId × Expr)) {y : VarId} (hy : y ∈ fields) :
    ∃ entry, (fieldFacts record fields ++ Γ).find? (fun e => e.1 == y) = some entry ∧
      entry.2 = fieldProjection record fields y := by
  rw [List.find?_append]
  have hmem : y ∈ fields.reverse := List.mem_reverse.mpr hy
  obtain ⟨j, hj, hjy⟩ := List.mem_iff_getElem.mp hmem
  have hlook : envLookupT fields.reverse y = some j :=
    envLookupT_getElem hdistinct.reverse (by rw [List.getElem?_eq_getElem hj, hjy])
  cases hz : (fieldFacts record fields).find? (fun e => e.1 == y) with
  | none =>
    exfalso
    rw [fieldFacts_eq] at hz
    have := find?_zip_none fields.reverse _ (by simp) hz
    rw [hlook] at this; cases this
  | some e =>
    refine ⟨e, by simp, ?_⟩
    rw [fieldFacts_eq] at hz
    obtain ⟨j', hj', hb⟩ := find?_zip_lookup fields.reverse _ (by simp) e hz
    rw [hlook] at hj'; cases hj'
    rw [List.getElem?_map, List.getElem?_eq_getElem hj, hjy] at hb
    simp only [Option.map_some, Option.some.injEq] at hb
    exact hb.symm

/-! ## Unpacking -/

theorem unpack_factRel
    (hP : ∀ env ρ rhs v, P env ρ rhs v → Produces env ρ rhs v ∧ freshIn env rhs = true)
    (hPush : ∀ env ρ rhs v, Produces env ρ rhs v → freshIn env rhs = true → P env ρ rhs v)
    {G G' : VarId → Prop} {Γ : List (VarId × Expr)} {record : VarId} {fields : List VarId}
    {e e' : Expr}
    (hGG : ∀ y, G y → G' y) (hGf : ∀ y ∈ fields, G' y)
    (hnotG : ∀ y ∈ fields, ∀ z, (z == y) = true → ¬ G z)
    (hdistinct : NamesDistinct fields) (hbig : ∀ y ∈ fields, maxUidExpr e < y.uid)
    (hknown : knownRecord Γ record fields.length = true)
    (hS : FactRel G' P (fieldFacts record fields ++ Γ) (replaceReads record fields e) e') :
    FactRel G P Γ e (.Case (.Var record) [lambdas fields e']) := by
  intro env t hG hd hfresh hk hsc hlow
  unfold knownRecord at hknown
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hknown
  obtain ⟨_, hrec⟩ := hknown
  -- the record has a recorded fact, so it is bound
  obtain ⟨entry, hf⟩ : ∃ entry, Γ.find? (fun e => e.1 == record) = some entry := by
    cases hf : Γ.find? (fun e => e.1 == record) with
    | none =>
      simp only [recordFuel, shapeOf, hf] at hrec
      simp [Shape.isRecord, Shape.tagZeroOnly] at hrec
    | some entry => exact ⟨entry, rfl⟩
  have hmem := List.mem_of_find?_eq_some hf
  have hkey : (entry.1 == record) = true := by simpa using List.find?_some hf
  have hrb := hk entry hmem
  rw [envLookupT_congr hkey] at hrb
  obtain ⟨ir, hir⟩ := Option.isSome_iff_exists.mp hrb
  -- the environment with the field binders
  have hout : ∀ y ∈ fields, envLookupT env y = none := fun y hy => lookup_none_of_not_G hG (hnotG y hy)
  have hd' : EnvDistinct (fields.reverse ++ env) :=
    EnvDistinct.append hdistinct.reverse hd fun y hy => hout y (List.mem_reverse.mp hy)
  have hlowP : ∀ y ∈ fields, ∃ tp, lowerTotalExpr env (fieldProjection record fields y) = some tp := by
    intro y hy
    obtain ⟨j, hj, hjy⟩ := List.mem_iff_getElem.mp (List.mem_reverse.mpr hy)
    have hq : envLookupT fields.reverse y = some j :=
      envLookupT_getElem hdistinct.reverse (by rw [List.getElem?_eq_getElem hj, hjy])
    exact ⟨_, lowerTotalExpr_fieldProjection hir hq⟩
  have hk' : KeysBound (fieldFacts record fields ++ Γ) (fields.reverse ++ env) := by
    rw [fieldFacts_eq]; exact KeysBound.bind _ _ hk
  have hsc' : FactsScoped (fieldFacts record fields ++ Γ) (fields.reverse ++ env) := by
    rw [fieldFacts_eq]
    refine FactsScoped.bind _ _ hsc (by simp) ?_
    intro b hb
    rw [List.mem_map] at hb
    obtain ⟨y, hy, rfl⟩ := hb
    obtain ⟨tp, htp⟩ := hlowP y (List.mem_reverse.mp hy)
    rw [htp]; rfl
  -- the source after the field binders
  have hfree : ∀ y ∈ fields.reverse, (freeVars e).contains y = false :=
    fun y hy => maxUidExpr_fresh _ _ (hbig y (List.mem_reverse.mp hy))
  obtain ⟨tX, htX⟩ := lowerTotalExpr_append_unused hlow fields.reverse hfree
  have hfreshX : freshIn (fields.reverse ++ env) e = true :=
    freshIn_append_big hfresh fields.reverse fun y hy => hbig y (List.mem_reverse.mp hy)
  obtain ⟨tR, htR, hrR⟩ := replaceReads_factRel (fun _ _ _ _ h => (hP _ _ _ _ h).1) hPush record fields
    hdistinct e (fieldFacts record fields ++ Γ) hbig (fun y hy => fieldFacts_find hdistinct Γ hy)
    (fields.reverse ++ env) tX (fun _ _ => trivial) hd' hfreshX hk' hsc' htX
  have hGenv : ∀ y ∈ fields.reverse ++ env, G' y := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hGf y (List.mem_reverse.mp hy)
    · exact hGG y (hG y hy)
  obtain ⟨t'', ht'', hr''⟩ := hS (fields.reverse ++ env) tR hGenv hd'
    (freshIn_replaceReads record fields e _ hfreshX) hk' hsc' htR
  refine ⟨.Case (.Var (ir + 1)) [lamsT fields.length t''], ?_, ?_⟩
  · rw [MIR.lowerTotalExpr_case_of_list, lowerTotalExpr_var, hir, MIR.lowerTotalExprList_cons,
      lowerTotalExpr_lambdas, ht'', MIR.lowerTotalExprList_nil]
    rfl
  intro ρ π henv hlen hπ hF
  -- the record value
  have hirlt := envLookupT_bound env record ir hir
  obtain ⟨W, hW, hWwf⟩ := envWellFormed_lookup env.length henv (n := ir + 1) (by omega) (by omega)
  have hshape := shapeOf_sound hP hPush recordFuel recordDepth Γ (.Var record) hF hd
    (by simp [freshIn]) (by rw [lowerTotalExpr_var, hir]; rfl) (halts_var_of_lookup hW)
  obtain ⟨fs, rfl, hfslen⟩ := isRecord_holds hrec hshape
  have hfswf : ValueListWellFormed fs := by cases hWwf; assumption
  -- the facts of the field binders
  have hF' : FactsHold P (fieldFacts record fields ++ Γ) (fields.reverse ++ env) (extendAll ρ fs) := by
    rw [fieldFacts_eq]
    refine FactsHold.bind fields.reverse _ fs.reverse hF (by simp) (by simp; omega)
      (fun j hj => lookup_extendAll_lt ρ fs j (by simp at hj; omega))
      (by rw [List.length_reverse, ← hfslen]; exact dropEnv_extendAll ρ fs) ?_
    intro j a u ha hu
    rw [List.getElem?_map] at ha
    cases hy : fields.reverse[j]? with
    | none => rw [hy] at ha; cases ha
    | some y =>
      rw [hy] at ha
      simp only [Option.map_some, Option.some.injEq] at ha
      subst ha
      have hq : envLookupT fields.reverse y = some j := envLookupT_getElem hdistinct.reverse hy
      have hymem : y ∈ fields := List.mem_reverse.mp (List.mem_of_getElem? hy)
      refine hPush _ _ _ _ ⟨_, lowerTotalExpr_fieldProjection hir hq,
        fieldProjection_of_fields hW (.inl rfl) hfslen hu⟩
        (freshIn_fieldProjection hdistinct hout hymem)
  have henv' := envWellFormed_extendAll env.length fs henv hlen hfswf
  have hlen' : (fields.reverse ++ env).length ≤ (extendAll ρ fs).length := by
    rw [extendAll_length]; simp; omega
  have henv'' : EnvWellFormed (fields.reverse ++ env).length (extendAll ρ fs) := by
    simpa [hfslen, Nat.add_comm] using henv'
  -- the target binds the fields and continues
  have htarget : Reaches (.compute π ρ (.Case (.Var (ir + 1)) [lamsT fields.length t'']))
      (.compute π (extendAll ρ fs) t'') := by
    refine reaches_trans (s₂ := .ret (.caseScrutinee [lamsT fields.length t''] ρ :: π) (.VConstr 0 fs))
      ⟨2, by simp [steps, step, hW]⟩ ?_
    refine reaches_trans ⟨1, by simp only [steps]; rw [step_case_single (.inl rfl)]⟩ ?_
    rw [← hfslen]
    exact reaches_telescope fs π ρ t''
  refine obsRefines_of_reaches (reaches_refl _) htarget ?_
  refine obsRefines_trans (obsRefines_bind_unused fields fs hfslen
    (fun y hy => maxUidExpr_fresh _ _ (hbig y hy)) hlow htX henv hlen hfswf hπ) ?_
  refine obsRefines_trans (hrR (extendAll ρ fs) π henv'' hlen' hπ hF') ?_
  exact hr'' (extendAll ρ fs) π henv'' hlen' hπ hF'

end Moist.Verified.ShapeFacts
