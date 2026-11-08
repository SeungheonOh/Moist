import Moist.Verified.RecordsSoundness.Unpack

variable [sv : Moist.CEK.SemVariant]

/-! # Alternatives with field facts

When the shape of the scrutinee fixes the number of fields at the tag of an
alternative `λx₁…xₘ. body`, the body can be related under the facts that
each `xᵢ` holds the `i`-th field, recorded as the projection
`case scrutinee [error, …, λx₁…xₘ. xᵢ]` (`FactRel.case_alternatives`).
The alternatives are related first, over the values of the source
scrutinee, whose shape `shapeOf` describes; the scrutinee is related
afterwards.
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.BetaValueRefines
open Moist.Verified.Contextual

variable {P : List VarId → CekEnv → Expr → CekValue → Prop}

/-- How the walk relates one alternative: by congruence, or by entering its
    binders with field facts. -/
def AltRel (G : VarId → Prop) (P : List VarId → CekEnv → Expr → CekValue → Prop)
    (Γ : List (VarId × Expr)) (scrut : Expr) (tag : Nat) (alt alt' : Expr) : Prop :=
  FactRel G P Γ alt alt' ∨
    ∃ shapes binders body body', (shapeOf recordFuel recordDepth Γ scrut).atTag tag = .fields shapes ∧
      binders.length = shapes.length ∧ alt = lambdas binders body ∧ alt' = lambdas binders body' ∧
      (∀ x ∈ binders, G x) ∧ FactRel G P (alternativeFacts scrut tag binders ++ Γ) body body'

def AltsRel (G : VarId → Prop) (P : List VarId → CekEnv → Expr → CekValue → Prop)
    (Γ : List (VarId × Expr)) (scrut : Expr) : Nat → List Expr → List Expr → Prop
  | _, [], [] => True
  | tag, alt :: alts, alt' :: alts' => AltRel G P Γ scrut tag alt alt' ∧ AltsRel G P Γ scrut (tag + 1) alts alts'
  | _, _, _ => False

/-- The lowered form of `AltRel`. -/
def TermAltRel (P : List VarId → CekEnv → Expr → CekValue → Prop) (Γ : List (VarId × Expr))
    (env : List VarId) (scrut : Expr) (tag : Nat) (talt talt' : Term) : Prop :=
  FactRefines env.length (FactsHold P Γ env) talt talt' ∨
    ∃ shapes binders tb tb', (shapeOf recordFuel recordDepth Γ scrut).atTag tag = .fields shapes ∧
      binders.length = shapes.length ∧ talt = lamsT binders.length tb ∧
      talt' = lamsT binders.length tb' ∧ NamesDistinct binders ∧
      (∀ x ∈ binders, envLookupT env x = none) ∧
      FactRefines (binders.reverse ++ env).length
        (FactsHold P (alternativeFacts scrut tag binders ++ Γ) (binders.reverse ++ env)) tb tb'

def TermAltsRel (P : List VarId → CekEnv → Expr → CekValue → Prop) (Γ : List (VarId × Expr))
    (env : List VarId) (scrut : Expr) : Nat → List Term → List Term → Prop
  | _, [], [] => True
  | tag, a :: as, b :: bs => TermAltRel P Γ env scrut tag a b ∧ TermAltsRel P Γ env scrut (tag + 1) as bs
  | _, _, _ => False

theorem termAltsRel_length {Γ : List (VarId × Expr)} {env : List VarId} {scrut : Expr} :
    ∀ {base : Nat} {as bs : List Term}, TermAltsRel P Γ env scrut base as bs → as.length = bs.length
  | _, [], [], _ => rfl
  | _, _ :: _, _ :: _, h => by simp [termAltsRel_length h.2]
  | _, [], _ :: _, h => by simp [TermAltsRel] at h
  | _, _ :: _, [], h => by simp [TermAltsRel] at h

theorem termAltsRel_get {Γ : List (VarId × Expr)} {env : List VarId} {scrut : Expr} :
    ∀ {base : Nat} {as bs : List Term}, TermAltsRel P Γ env scrut base as bs → ∀ j,
      (as[j]? = none ∧ bs[j]? = none) ∨
        ∃ a b, as[j]? = some a ∧ bs[j]? = some b ∧ TermAltRel P Γ env scrut (base + j) a b
  | _, [], [], _, _ => .inl ⟨rfl, rfl⟩
  | base, a :: as, b :: bs, h, 0 => .inr ⟨a, b, rfl, rfl, by simpa using h.1⟩
  | base, a :: as, b :: bs, h, j + 1 => by
    rcases termAltsRel_get h.2 j with hn | ⟨x, y, hx, hy, hr⟩
    · exact .inl (by simpa using hn)
    · exact .inr ⟨x, y, by simpa using hx, by simpa using hy, by
        rw [show base + (j + 1) = base + 1 + j by omega]; exact hr⟩
  | _, [], _ :: _, h, _ => by simp [TermAltsRel] at h
  | _, _ :: _, [], h, _ => by simp [TermAltsRel] at h

/-! ## The facts of an alternative -/

theorem alternativeFacts_eq (scrut : Expr) (tag : Nat) (binders : List VarId) :
    alternativeFacts scrut tag binders =
      binders.reverse.zip (binders.reverse.map (alternativeProjection scrut tag binders)) := by
  rw [alternativeFacts, zip_map_self]

theorem lowerTotalExprList_replicate_error (env : List VarId) (tag : Nat) (rest : List Expr) :
    MIR.lowerTotalExprList env (List.replicate tag .Error ++ rest) =
      (MIR.lowerTotalExprList env rest).map (List.replicate tag .Error ++ ·) := by
  induction tag with
  | zero => cases h : MIR.lowerTotalExprList env rest <;> simp [h]
  | succ tag ih =>
    rw [List.replicate_succ, List.cons_append, MIR.lowerTotalExprList_cons, lowerTotalExpr_error, ih]
    cases MIR.lowerTotalExprList env rest <;> rfl

theorem lowerTotalExpr_alternativeProjection {env : List VarId} {scrut : Expr} {ts : Term} {tag : Nat}
    {binders : List VarId} {x : VarId} {index : Nat} (hts : lowerTotalExpr env scrut = some ts)
    (hx : envLookupT binders.reverse x = some index) :
    lowerTotalExpr env (alternativeProjection scrut tag binders x) =
      some (.Case ts (List.replicate tag .Error ++ [lamsT binders.length (.Var (index + 1))])) := by
  have hv : lowerTotalExpr (binders.reverse ++ env) (.Var x) = some (.Var (index + 1)) := by
    rw [lowerTotalExpr_var, envLookupT_append_of_some hx]; rfl
  unfold alternativeProjection
  rw [MIR.lowerTotalExpr_case_of_list, hts, lowerTotalExprList_replicate_error,
    MIR.lowerTotalExprList_cons, lowerTotalExpr_lambdas, hv, MIR.lowerTotalExprList_nil]
  rfl

theorem freshIn_alternativeProjection {env : List VarId} {scrut : Expr} {tag : Nat}
    {binders : List VarId} {x : VarId} (hfs : freshIn env scrut = true) (hdistinct : NamesDistinct binders)
    (hout : ∀ z ∈ binders, envLookupT env z = none) :
    freshIn env (alternativeProjection scrut tag binders x) = true := by
  have hl : freshIn env (lambdas binders (.Var x)) = true :=
    freshIn_lambdas_of hdistinct hout (by simp [freshIn])
  have hrep : ∀ (n : Nat) (rest : List Expr), freshInList env rest = true →
      freshInList env (List.replicate n .Error ++ rest) = true := by
    intro n rest hr
    induction n with
    | zero => simpa using hr
    | succ n ih => simp [List.replicate_succ, freshInList, freshIn, ih]
  unfold alternativeProjection
  simp only [freshIn, Bool.and_eq_true]
  exact ⟨hfs, hrep tag _ (by simp [freshInList, hl])⟩

/-- The projection recorded for an alternative binder returns its field. -/
theorem alternativeProjection_halts {ρ : CekEnv} {ts : Term} {w : CekValue} {tag index : Nat}
    {fields : List CekValue} {u : CekValue} (hw : Halts ρ ts w) (hwv : w = .VConstr tag fields)
    (hu : fields.reverse[index]? = some u) :
    Halts ρ (.Case ts (List.replicate tag .Error ++ [lamsT fields.length (.Var (index + 1))])) u := by
  subst hwv
  have hindex : index < fields.length := by
    have := (List.getElem?_eq_some_iff.mp hu).1; simpa using this
  have hget : (List.replicate tag Term.Error ++ [lamsT fields.length (.Var (index + 1))])[tag]? =
      some (lamsT fields.length (.Var (index + 1))) := by
    rw [List.getElem?_append_right (by simp)]; simp
  unfold Halts
  refine reaches_trans ⟨1, rfl⟩ ?_
  refine reaches_trans (halts_on_stack hw _) ?_
  refine reaches_trans (s₂ := .compute (fields.map Frame.applyArg ++ []) ρ
    (lamsT fields.length (.Var (index + 1)))) ⟨1, by simp only [steps, step, hget]⟩ ?_
  refine reaches_trans (reaches_telescope fields [] ρ _) ⟨2, ?_⟩
  simp only [steps, step]
  rw [lookup_extendAll_lt ρ fields index hindex, hu]


/-! ## Lowering related alternatives -/

theorem altsRel_lower
    {G : VarId → Prop} {Γ : List (VarId × Expr)} {scrut : Expr} {env : List VarId}
    (hG : ∀ y ∈ env, G y) (hd : EnvDistinct env) (hk : KeysBound Γ env) (hsc : FactsScoped Γ env)
    {ts : Term} (hts : lowerTotalExpr env scrut = some ts) :
    ∀ {base : Nat} {alts alts' : List Expr} {talts : List Term}, AltsRel G P Γ scrut base alts alts' →
      freshInList env alts = true → MIR.lowerTotalExprList env alts = some talts →
      ∃ talts', MIR.lowerTotalExprList env alts' = some talts' ∧
        TermAltsRel P Γ env scrut base talts talts'
  | _, [], [], talts, _, _, htalts => by
    rw [MIR.lowerTotalExprList_nil] at htalts; cases htalts
    exact ⟨[], MIR.lowerTotalExprList_nil env, trivial⟩
  | base, alt :: alts, alt' :: alts', talts, hrel, hfresh, htalts => by
    simp only [freshInList, Bool.and_eq_true] at hfresh
    rw [MIR.lowerTotalExprList_cons] at htalts
    cases htalt : lowerTotalExpr env alt with
    | none => rw [htalt] at htalts; cases htalts
    | some talt =>
      cases hrest : MIR.lowerTotalExprList env alts with
      | none => rw [htalt, hrest] at htalts; cases htalts
      | some trest =>
        rw [htalt, hrest] at htalts; cases htalts
        obtain ⟨trest', htrest', hrrest⟩ := altsRel_lower hG hd hk hsc hts hrel.2 hfresh.2 hrest
        have hone : ∃ talt', lowerTotalExpr env alt' = some talt' ∧
            TermAltRel P Γ env scrut base talt talt' := by
          rcases hrel.1 with hplain | ⟨shapes, binders, body, body', hshape, hblen, rfl, rfl, hGb, hbody⟩
          · obtain ⟨talt', htalt', hr⟩ := hplain env talt hG hd hfresh.1 hk hsc htalt
            exact ⟨talt', htalt', .inl hr⟩
          · obtain ⟨tb, htb, rfl⟩ := lower_lambdas htalt
            obtain ⟨hfb, hdb⟩ := fresh_lambdas hfresh.1 hd
            have hdistinct := lambdas_distinct hfresh.1
            have hout := lambdas_outside hfresh.1
            have hk' : KeysBound (alternativeFacts scrut base binders ++ Γ) (binders.reverse ++ env) := by
              rw [alternativeFacts_eq]; exact KeysBound.bind _ _ hk
            have hsc' : FactsScoped (alternativeFacts scrut base binders ++ Γ) (binders.reverse ++ env) := by
              rw [alternativeFacts_eq]
              refine FactsScoped.bind _ _ hsc (by simp) ?_
              intro b hb
              rw [List.mem_map] at hb
              obtain ⟨x, hx, rfl⟩ := hb
              obtain ⟨j, hj, hjx⟩ := List.mem_iff_getElem.mp hx
              have hidx : envLookupT binders.reverse x = some j :=
                envLookupT_getElem hdistinct.reverse (by rw [List.getElem?_eq_getElem hj, hjx])
              rw [lowerTotalExpr_alternativeProjection hts hidx]; rfl
            have hGenv : ∀ y ∈ binders.reverse ++ env, G y := by
              intro y hy
              rcases List.mem_append.mp hy with hy | hy
              · exact hGb y (List.mem_reverse.mp hy)
              · exact hG y hy
            obtain ⟨tb', htb', hr⟩ := hbody (binders.reverse ++ env) tb hGenv hdb hfb hk' hsc' htb
            refine ⟨lamsT binders.length tb', by rw [lowerTotalExpr_lambdas, htb']; rfl,
              .inr ⟨shapes, binders, tb, tb', hshape, hblen, rfl, rfl, hdistinct, hout, hr⟩⟩
        obtain ⟨talt', htalt', hr⟩ := hone
        exact ⟨talt' :: trest', by rw [MIR.lowerTotalExprList_cons, htalt', htrest']; rfl, hr, hrrest⟩
  | _, [], _ :: _, _, h, _, _ => by simp [AltsRel] at h
  | _, _ :: _, [], _, h, _, _ => by simp [AltsRel] at h

/-! ## Dispatching on a value of the scrutinee -/

theorem dispatch_alternatives
    (hPush : ∀ env ρ rhs v, Produces env ρ rhs v → freshIn env rhs = true → P env ρ rhs v)
    {Γ : List (VarId × Expr)} {scrut : Expr} {env : List VarId} {ts : Term}
    {talts talts' : List Term} {ρ : CekEnv} {π : Stack} {w : CekValue}
    (hrel : TermAltsRel P Γ env scrut 0 talts talts') (hts : lowerTotalExpr env scrut = some ts)
    (hfs : freshIn env scrut = true)
    (henv : EnvWellFormed env.length ρ) (hlen : env.length ≤ ρ.length) (hπ : StackWellFormed π)
    (hF : FactsHold P Γ env ρ) (hw : Halts ρ ts w)
    (hshape : ShapeHolds (shapeOf recordFuel recordDepth Γ scrut) w)
    (tag : Nat) (fields : List CekValue) (hcf : CaseFields w tag fields) (hfields : ValueListWellFormed fields) :
    ObsRefines
      (match talts[tag]? with
        | some alt => State.compute (fields.map Frame.applyArg ++ π) ρ alt | none => .error)
      (match talts'[tag]? with
        | some alt => State.compute (fields.map Frame.applyArg ++ π) ρ alt | none => .error) := by
  rcases termAltsRel_get hrel tag with ⟨e₁, e₂⟩ | ⟨a, a', e₁, e₂, ha⟩
  · rw [e₁, e₂]; exact obsRefines_refl _
  · rw [e₁, e₂]
    simp only [Nat.zero_add] at ha
    rcases ha with hplain | ⟨shapes, binders, tb, tb', hshapeAt, hblen, rfl, rfl, hdistinct, hout, hr⟩
    · exact hplain ρ _ henv hlen (stackWellFormed_applyArgs hfields hπ) hF
    · -- the scrutinee is a constructor with exactly as many fields as binders
      obtain ⟨rfl, hflen⟩ : w = .VConstr tag fields ∧ fields.length = binders.length := by
        rcases hcf with rfl | ⟨c, numCtors, rfl, _⟩
        · rcases atTag_constr _ hshape with hu | ⟨shapes', hs', hf⟩
          · rw [hu] at hshapeAt; cases hshapeAt
          · rw [hs'] at hshapeAt; cases hshapeAt
            exact ⟨rfl, by rw [← fieldsHold_length hf, hblen]⟩
        · rw [atTag_other _ hshape (fun _ _ h => by cases h) tag] at hshapeAt; cases hshapeAt
      have hreach : ∀ body, Reaches (.compute (fields.map Frame.applyArg ++ π) ρ (lamsT binders.length body))
          (.compute π (extendAll ρ fields) body) := by
        intro body; rw [← hflen]; exact reaches_telescope fields π ρ body
      refine obsRefines_of_reaches (hreach tb) (hreach tb') ?_
      have hF' : FactsHold P (alternativeFacts scrut tag binders ++ Γ) (binders.reverse ++ env)
          (extendAll ρ fields) := by
        rw [alternativeFacts_eq]
        refine FactsHold.bind binders.reverse _ fields.reverse hF (by simp) (by simp; omega)
          (fun j hj => lookup_extendAll_lt ρ fields j (by simp at hj; omega))
          (by rw [List.length_reverse, ← hflen]; exact dropEnv_extendAll ρ fields) ?_
        intro j a u ha hu
        rw [List.getElem?_map] at ha
        cases hx : binders.reverse[j]? with
        | none => rw [hx] at ha; cases ha
        | some x =>
          rw [hx] at ha
          simp only [Option.map_some, Option.some.injEq] at ha
          subst ha
          have hidx : envLookupT binders.reverse x = some j := envLookupT_getElem hdistinct.reverse hx
          refine hPush _ _ _ _ ⟨_, lowerTotalExpr_alternativeProjection hts hidx, ?_⟩
            (freshIn_alternativeProjection hfs hdistinct hout)
          rw [← hflen]
          exact alternativeProjection_halts hw rfl hu
      have henv' := envWellFormed_extendAll env.length fields henv hlen hfields
      refine hr (extendAll ρ fields) π (by simpa [hflen, Nat.add_comm] using henv')
        (by rw [extendAll_length]; simp; omega) hπ hF'

/-- A `case` whose alternatives are related by `AltsRel` and whose scrutinee
    is related by congruence. -/
theorem FactRel.case_alternatives
    (hP : ∀ env ρ rhs v, P env ρ rhs v → Produces env ρ rhs v ∧ freshIn env rhs = true)
    (hPush : ∀ env ρ rhs v, Produces env ρ rhs v → freshIn env rhs = true → P env ρ rhs v)
    {G : VarId → Prop} {Γ : List (VarId × Expr)} {s s' : Expr} {alts alts' : List Expr}
    (hs : FactRel G P Γ s s') (halts : AltsRel G P Γ s 0 alts alts') :
    FactRel G P Γ (.Case s alts) (.Case s' alts') := by
  intro env t hG hd hfresh hk hsc hlow
  simp only [freshIn, Bool.and_eq_true] at hfresh
  obtain ⟨ts, talts, hts, htalts, rfl⟩ := lowerTotalExpr_case_some hlow
  obtain ⟨ts', hts', hrs⟩ := hs env ts hG hd hfresh.1 hk hsc hts
  obtain ⟨talts', htalts', hrel⟩ := altsRel_lower hG hd hk hsc hts halts hfresh.2 htalts
  refine ⟨.Case ts' talts', by rw [MIR.lowerTotalExpr_case_of_list, hts', htalts']; rfl, ?_⟩
  intro ρ π henv hlen hπ hF
  have closedTs := MIR.lowerTotalExpr_closedAt hts
  have closedAlts := lowerTotalExprList_closedAtList htalts
  have closedAlts' := lowerTotalExprList_closedAtList htalts'
  refine obsRefines_trans (s₂ := .compute π ρ (.Case ts talts')) ?_ ?_
  · apply obsRefines_of_step
    show ObsRefines (.compute (.caseScrutinee talts ρ :: π) ρ ts)
      (.compute (.caseScrutinee talts' ρ :: π) ρ ts)
    apply obsRefines_of_continuation
    intro w hw
    have hshape := shapeOf_sound hP hPush recordFuel recordDepth Γ s hF hd hfresh.1 hts hw
    have hwwf := halts_wellFormed henv hlen closedTs hw
    have hlength := termAltsRel_length hrel
    have dispatch := dispatch_alternatives hPush hrel hts hfresh.1 henv hlen hπ hF hw hshape
    apply obsRefines_of_step
    cases w with
    | VConstr tag fields =>
      cases hwwf with
      | vconstr _ hfields => exact dispatch tag fields (.inl rfl) hfields
    | VCon c =>
      simp only [step]
      cases hc : constToTagAndFields c with
      | none => exact obsRefines_refl _
      | some r =>
        obtain ⟨tag, numCtors, fields⟩ := r
        simp only [hlength]
        split
        · exact obsRefines_refl _
        · have hvcon := constToTagAndFields_fields_vcon c
          rw [hc] at hvcon
          exact dispatch tag fields (.inr ⟨c, numCtors, rfl, hc⟩) (valueListWellFormed_map_vcon hvcon)
    | VLam _ _ | VDelay _ _ | VBuiltin _ _ _ => exact obsRefines_refl _
  · apply obsRefines_of_step
    show ObsRefines (.compute (.caseScrutinee talts' ρ :: π) ρ ts)
      (.compute (.caseScrutinee talts' ρ :: π) ρ ts')
    exact hrs ρ _ henv hlen (.cons (.caseScrutinee henv hlen closedAlts') hπ) hF

end Moist.Verified.ShapeFacts
