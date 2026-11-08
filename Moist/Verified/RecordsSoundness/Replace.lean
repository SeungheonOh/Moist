import Moist.Verified.RecordsSoundness.Fields

variable [sv : Moist.CEK.SemVariant]

/-! # Replacing field reads by field binders

Inside the scope of field binders recorded with `fieldProjection`, every
field read of the record at the same arity can be replaced by the binder of
the field it reads (`replaceReads_factRel`). The recorded expression only
returns when the record supplies exactly as many fields as there are
binders, so the read returns the same field.
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence

variable {P : List VarId → CekEnv → Expr → CekValue → Prop}

/-- No two positions of the list hold equal names. -/
def NamesDistinct (names : List VarId) : Prop :=
  ∀ (i j : Nat) (a b : VarId), names[i]? = some a → names[j]? = some b → (a == b) = true → i = j

omit sv in
theorem NamesDistinct.tail {x : VarId} {xs : List VarId} (h : NamesDistinct (x :: xs)) :
    NamesDistinct xs := by
  intro i j a b ha hb hab
  have := h (i + 1) (j + 1) a b (by simpa using ha) (by simpa using hb) hab
  omega

omit sv in
theorem NamesDistinct.reverse {names : List VarId} (h : NamesDistinct names) :
    NamesDistinct names.reverse := by
  intro i j a b ha hb hab
  have hi := (List.getElem?_eq_some_iff.mp ha).1
  have hj := (List.getElem?_eq_some_iff.mp hb).1
  simp only [List.length_reverse] at hi hj
  rw [List.getElem?_reverse hi] at ha
  rw [List.getElem?_reverse hj] at hb
  have := h _ _ a b ha hb hab
  omega

omit sv in
theorem envLookupT_getElem : ∀ {names : List VarId} {i : Nat} {x : VarId}, NamesDistinct names →
    names[i]? = some x → envLookupT names x = some i
  | [], _, _, _, h => by simp at h
  | y :: ys, 0, x, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rw [envLookupT_cons, if_pos (varId_beq_self y)]
  | y :: ys, i + 1, x, hd, h => by
    rw [envLookupT_cons]
    have hyx : (y == x) = false := by
      cases hc : (y == x) with
      | false => rfl
      | true =>
        have := hd 0 (i + 1) y x rfl (by simpa using h) hc
        omega
    rw [if_neg (by simp [hyx]), envLookupT_getElem hd.tail (by simpa using h)]
    rfl

omit sv in
theorem freshFields_length (next count : Nat) : (freshFields next count).length = count := by
  simp [freshFields]

omit sv in
theorem freshFields_getElem {next count i : Nat} {y : VarId} (h : (freshFields next count)[i]? = some y) :
    y = { uid := next + i, origin := .gen, hint := "field" } ∧ i < count := by
  have hi : i < count := by
    have := (List.getElem?_eq_some_iff.mp h).1
    simpa [freshFields_length] using this
  simp only [freshFields, List.getElem?_map, List.getElem?_eq_getElem (by simpa using hi : i < (List.range count).length),
    List.getElem_range, Option.map_some, Option.some.injEq] at h
  exact ⟨h.symm, hi⟩

omit sv in
theorem freshFields_distinct (next count : Nat) : NamesDistinct (freshFields next count) := by
  intro i j a b ha hb hab
  obtain ⟨rfl, _⟩ := freshFields_getElem ha
  obtain ⟨rfl, _⟩ := freshFields_getElem hb
  rw [VarId.beq_true_iff] at hab
  simp at hab
  omega

omit sv in
theorem freshFields_mem {next count : Nat} {y : VarId} (h : y ∈ freshFields next count) :
    next ≤ y.uid ∧ y.uid < next + count ∧ y.origin = .gen := by
  simp only [freshFields, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  simp; omega

/-! ## A single read -/

omit sv in
theorem fieldRead_spec {w : VarId} {alt : Expr} {record : VarId} {arity field : Nat}
    (h : fieldRead (.Case (.Var w) [alt]) = some (record, arity, field)) :
    ∃ binders x index, alt = lams binders (.Var x) ∧ binders.length = arity ∧ record = w ∧
      envLookupT binders.reverse x = some index ∧ field = arity - 1 - index := by
  simp only [fieldRead] at h
  have hlams := lams_resultParameters alt
  generalize hrp : resultParameters alt = rp at h hlams
  obtain ⟨binders, body⟩ := rp
  simp only at h hlams
  cases body with
  | Var x =>
    simp only at h
    split at h
    · cases h
    · unfold fieldOf at h
      cases hidx : envLookupT binders.reverse x with
      | none => rw [hidx] at h; cases h
      | some index =>
        rw [hidx] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨binders, x, index, hlams.symm, rfl, rfl, hidx, rfl⟩
  | _ => simp at h

omit sv in
theorem fieldRead_shape {e : Expr} {r : VarId × Nat × Nat} (h : fieldRead e = some r) :
    ∃ w alt, e = .Case (.Var w) [alt] := by
  unfold fieldRead at h
  split at h
  · rename_i w alt; exact ⟨w, alt, rfl⟩
  · cases h

omit sv in
theorem readOf_spec {record : VarId} {arity field : Nat} {e : Expr}
    (h : readOf record arity e = some field) :
    ∃ w alt, e = .Case (.Var w) [alt] ∧ (w == record) = true ∧
      fieldRead (.Case (.Var w) [alt]) = some (w, arity, field) := by
  unfold readOf at h
  cases hr : fieldRead e with
  | none => rw [hr] at h; cases h
  | some r =>
    obtain ⟨other, count, f⟩ := r
    rw [hr] at h
    simp only at h
    split at h
    · rename_i hcond
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      simp only [Option.some.injEq] at h
      obtain ⟨hother, rfl⟩ := hcond
      subst h
      -- the read has the shape of a single-alternative case on a variable
      obtain ⟨w, alt, rfl⟩ := fieldRead_shape hr
      obtain ⟨_, _, _, _, _, hrec, _, _⟩ := fieldRead_spec hr
      subst hrec
      exact ⟨other, alt, rfl, hother, hr⟩
    · cases h

omit sv in
theorem lowerTotalExpr_fieldProjection {env : List VarId} {record y : VarId} {fields : List VarId}
    {ir q : Nat} (hir : envLookupT env record = some ir) (hq : envLookupT fields.reverse y = some q) :
    lowerTotalExpr env (fieldProjection record fields y) =
      some (.Case (.Case (.Var (ir + 1)) [lamsT fields.length (.Constr 0 [.Var (q + 1)])])
        [.Lam 0 (.Var 1)]) := by
  have hy : lowerTotalExpr (fields.reverse ++ env) (.Var y) = some (.Var (q + 1)) := by
    rw [lowerTotalExpr_var, envLookupT_append_of_some hq]; rfl
  have hc : lowerTotalExpr (fields.reverse ++ env) (.Constr 0 [.Var y]) =
      some (.Constr 0 [.Var (q + 1)]) := by
    rw [MIR.lowerTotalExpr_constr_of_list, MIR.lowerTotalExprList_cons, hy,
      MIR.lowerTotalExprList_nil]; rfl
  unfold fieldProjection
  rw [MIR.lowerTotalExpr_case_of_list, MIR.lowerTotalExpr_case_of_list, lowerTotalExpr_var, hir,
    MIR.lowerTotalExprList_cons, lowerTotalExpr_lambdas, hc, MIR.lowerTotalExprList_nil,
    MIR.lowerTotalExprList_cons, MIR.lowerTotalExpr_lam, lowerTotalExpr_var,
    envLookupT_cons, if_pos (varId_beq_self y), MIR.lowerTotalExprList_nil]
  rfl

/-- A read of the record is the field binder recorded for the field it reads. -/
theorem read_factRel (hP : ∀ env ρ rhs v, P env ρ rhs v → Produces env ρ rhs v) {G : VarId → Prop}
    {Γ : List (VarId × Expr)} {record w : VarId} {fields : List VarId} {alt : Expr} {field : Nat}
    {entry : VarId × Expr} (hdistinct : NamesDistinct fields) (hw : (w == record) = true)
    (hread : fieldRead (.Case (.Var w) [alt]) = some (w, fields.length, field))
    (hfind : Γ.find? (fun e => e.1 == fields.getD field record) = some entry)
    (hentry : entry.2 = fieldProjection record fields (fields.getD field record)) :
    FactRel G P Γ (.Case (.Var w) [alt]) (.Var (fields.getD field record)) := by
  obtain ⟨binders, x, index, rfl, hblen, _, hidx, hfield⟩ := fieldRead_spec hread
  have hindex := envLookupT_bound binders.reverse x index hidx
  simp only [List.length_reverse] at hindex
  have hfieldlt : field < fields.length := by omega
  obtain ⟨y, hy⟩ : ∃ y, fields[field]? = some y := by
    cases h : fields[field]? with
    | none => rw [List.getElem?_eq_none_iff] at h; omega
    | some y => exact ⟨y, rfl⟩
  have hgetD : fields.getD field record = y := by
    rw [List.getD_eq_getElem?_getD, hy]; rfl
  rw [hgetD] at hfind hentry ⊢
  -- the field binder sits at the same position from the end as the read binder
  have hq : envLookupT fields.reverse y = some index := by
    have hrev : fields.reverse[fields.length - 1 - field]? = some y := by
      rw [List.getElem?_reverse (by omega), show fields.length - 1 - (fields.length - 1 - field) = field by
        omega]
      exact hy
    rw [envLookupT_getElem hdistinct.reverse hrev]
    congr 1; omega
  intro env t _ hd _ hk _ hlow
  have hmem := List.mem_of_find?_eq_some hfind
  have hkey : (entry.1 == y) = true := by simpa using List.find?_some hfind
  have hybound := hk entry hmem
  rw [envLookupT_congr hkey] at hybound
  obtain ⟨iy, hiy⟩ := Option.isSome_iff_exists.mp hybound
  refine ⟨.Var (iy + 1), by rw [lowerTotalExpr_var, hiy]; rfl, ?_⟩
  obtain ⟨ts, talts, hts, htalts, rfl⟩ := lowerTotalExpr_case_some hlow
  obtain ⟨iw, hiw, rfl⟩ := lowerTotalExpr_var_some hts
  rw [MIR.lowerTotalExprList_cons, MIR.lowerTotalExprList_nil] at htalts
  cases htalt : lowerTotalExpr env (lams binders (.Var x)) with
  | none => rw [htalt] at htalts; cases htalts
  | some talt =>
    rw [htalt] at htalts
    cases htalts
    obtain ⟨tb, htb, rfl⟩ := lower_lams binders (.Var x) env talt htalt
    rw [lowerTotalExpr_var, envLookupT_append_of_some hidx] at htb
    cases htb
    intro ρ π henv hlen hπ hF
    obtain ⟨u, k, hik, hk', hu, hp⟩ := hF y entry iy hfind hiy
    obtain ⟨tp, htp, hhalt⟩ := hP _ _ _ _ hp
    rw [hentry] at htp
    -- the record is bound in the older environment where the field was recorded
    have hrecord : (envLookupT (env.drop k) record).isSome = true := by
      unfold fieldProjection at htp
      rw [MIR.lowerTotalExpr_case_of_list, MIR.lowerTotalExpr_case_of_list, lowerTotalExpr_var] at htp
      cases h : envLookupT (env.drop k) record with
      | none => rw [h] at htp; simp at htp
      | some _ => rfl
    obtain ⟨ir, hir⟩ := Option.isSome_iff_exists.mp hrecord
    rw [lowerTotalExpr_fieldProjection hir hq] at htp
    cases htp
    obtain ⟨W, fs, hW, hcf, hfslen, hfu⟩ := fieldProjection_halts (by omega) hhalt
    have hiw' : iw = ir + k := by
      have := hd.drop_lookup k hir
      rw [← envLookupT_congr hw] at this
      rw [hiw] at this; cases this; rfl
    have hWρ : ρ.lookup (iw + 1) = some W := by
      rw [hiw', show ir + k + 1 = ir + 1 + k by omega, ← dropEnv_lookup k ρ (ir + 1) (by omega)]
      exact hW
    refine obsRefines_of_reaches (read_reaches hWρ hcf (by omega) hfu)
      (halts_on_stack (halts_var_of_lookup hu) π) (obsRefines_refl _)

/-! ## Every read -/

omit sv in
theorem replaceReads_case (record : VarId) (fields : List VarId) (scrutinee : Expr)
    (alternatives : List Expr) (h : readOf record fields.length (.Case scrutinee alternatives) = none) :
    replaceReads record fields (.Case scrutinee alternatives) =
      .Case (replaceReads record fields scrutinee) (alternatives.map (replaceReads record fields)) := by
  rw [replaceReads]
  simp only [h]
  rw [attach_map_eq_map]

omit sv in
theorem replaceReads_let (record : VarId) (fields : List VarId) (bs : List (VarId × Expr × Bool))
    (body : Expr) :
    replaceReads record fields (.Let bs body) =
      .Let (bs.map fun (y, rhs, er) => (y, replaceReads record fields rhs, er))
        (replaceReads record fields body) := by
  rw [replaceReads, binds_attach_map]

/-- Reads of `record` replaced by the field binders recorded as holding them. -/
theorem replaceReads_factRel (hP : ∀ env ρ rhs v, P env ρ rhs v → Produces env ρ rhs v)
    (hPush : ∀ env ρ rhs v, Produces env ρ rhs v → freshIn env rhs = true → P env ρ rhs v)
    (record : VarId) (fields : List VarId) (hdistinct : NamesDistinct fields) (X : Expr)
    (Γ : List (VarId × Expr)) (hX : ∀ y ∈ fields, maxUidExpr X < y.uid)
    (hfacts : ∀ y ∈ fields, ∃ entry, Γ.find? (fun e => e.1 == y) = some entry ∧
      entry.2 = fieldProjection record fields y) :
    FactRel (fun _ => True) P Γ X (replaceReads record fields X) := by
  unfold replaceReads
  split
  · rename_i scrutinee alternatives
    split
    · rename_i field hfield
      obtain ⟨w, alt, heq, hw, hread⟩ := readOf_spec hfield
      cases heq
      obtain ⟨binders, x, index, _, hblen, _, hidx, hf⟩ := fieldRead_spec hread
      have hindex := envLookupT_bound binders.reverse x index hidx
      simp only [List.length_reverse] at hindex
      have hlt : field < fields.length := by omega
      have hmem : fields.getD field record ∈ fields := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
        exact List.getElem_mem hlt
      obtain ⟨entry, hfind, hentry⟩ := hfacts _ hmem
      exact read_factRel hP hdistinct hw hread hfind hentry
    · simp only [maxUidExpr] at hX
      apply FactRel.case (replaceReads_factRel hP hPush record fields hdistinct scrutinee Γ
        (fun y hy => by have := hX y hy; omega) hfacts)
      apply listRel_attach_map
      intro c hc
      have := maxUidExpr_le_maxUidExprList_of_mem hc
      exact replaceReads_factRel hP hPush record fields hdistinct c Γ
        (fun y hy => by have := hX y hy; omega) hfacts
  · rename_i y b
    simp only [maxUidExpr] at hX
    exact (replaceReads_factRel hP hPush record fields hdistinct b Γ
      (fun z hz => by have := hX z hz; omega) hfacts).lam trivial
  · rename_i y b
    cases b with
    | Lam z inner =>
      rw [replaceReads.eq_def]
      simp only [maxUidExpr] at hX
      exact (replaceReads_factRel hP hPush record fields hdistinct inner Γ
        (fun w hw => by have := hX w hw; omega) hfacts).fix_lam trivial trivial (fun _ _ => trivial)
    | _ =>
      intro env t _ _ _ _ _ hlow
      rw [MIR.lowerTotalExpr_fix_nonlam_none env y _ (by intros; simp)] at hlow
      cases hlow
  · rename_i b
    simp only [maxUidExpr] at hX
    exact (replaceReads_factRel hP hPush record fields hdistinct b Γ
      (fun z hz => by have := hX z hz; omega) hfacts).force
  · rename_i b
    simp only [maxUidExpr] at hX
    exact (replaceReads_factRel hP hPush record fields hdistinct b Γ
      (fun z hz => by have := hX z hz; omega) hfacts).delay
  · rename_i f a
    simp only [maxUidExpr] at hX
    exact (replaceReads_factRel hP hPush record fields hdistinct f Γ
      (fun z hz => by have := hX z hz; omega) hfacts).app
      (replaceReads_factRel hP hPush record fields hdistinct a Γ
        (fun z hz => by have := hX z hz; omega) hfacts)
  · rename_i tag fieldExprs
    apply FactRel.constr
    apply listRel_attach_map
    intro c hc
    have := maxUidExpr_le_maxUidExprList_of_mem hc
    simp only [maxUidExpr] at hX
    exact replaceReads_factRel hP hPush record fields hdistinct c Γ
      (fun z hz => by have := hX z hz; omega) hfacts
  · rename_i bindings body
    rw [binds_attach_map]
    cases bindings with
    | nil =>
      simp only [maxUidExpr, maxUidExprBinds] at hX
      refine ((replaceReads_factRel hP hPush record fields hdistinct body Γ
        (fun z hz => by have := hX z hz; omega) hfacts).congr_left
        (fun env => lowerTotalExpr_let_nil env body)
        (fun avoid => freshIn_let_nil avoid body)).congr_right ?_
      intro env; exact lowerTotalExpr_let_nil env _
    | cons binding rest =>
      simp only [maxUidExpr, maxUidExprBinds_cons'] at hX
      have hfresh : ∀ y ∈ fields, (binding.1 == y) = false := fun y hy =>
        beq_false_of_uid_lt (by have := hX y hy; omega)
      have ihr := replaceReads_factRel hP hPush record fields hdistinct binding.2.1 Γ
        (fun z hz => by have := hX z hz; omega) hfacts
      have ihrest := replaceReads_factRel hP hPush record fields hdistinct
        (.Let rest body) ((binding.1, binding.2.1) :: Γ)
        (fun z hz => by have := hX z hz; simp only [maxUidExpr]; omega)
        (fun y hy => by
          obtain ⟨entry, hf, he⟩ := hfacts y hy
          exact ⟨entry, by rw [find?_cons_of_ne (hfresh y hy)]; exact hf, he⟩)
      rw [replaceReads_let] at ihrest
      refine ((FactRel.let_single (er := binding.2.2) binding.2.1 trivial (.inl rfl) ihr ihrest
        (fun env ρ v _ _ hfr hp => hPush env ρ _ v hp hfr)).congr_left
        (fun env => lowerTotalExpr_let_cons env _ _ _)
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

end Moist.Verified.ShapeFacts
