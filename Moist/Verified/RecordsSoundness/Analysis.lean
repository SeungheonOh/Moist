import Moist.Verified.RecordsSoundness.Steps

/-! # Soundness of `shapeOf`

Under realized facts, whatever an expression returns has the shape that
`shapeOf` computes for it (`shapeOf_sound`). Bindings are entered with the
fact that their right-hand side produced the bound value; the binders of an
alternative are entered without facts, after hiding older facts about the
same names.
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence

variable {P : List VarId → CekEnv → Expr → CekValue → Prop}

/-- The soundness statement of `shapeOf` at a given fuel. -/
def ShapeSound (P : List VarId → CekEnv → Expr → CekValue → Prop) (fuel : Nat) : Prop :=
  ∀ (depth : Nat) (Γ : List (VarId × Expr)) (e : Expr) {env : List VarId} {ρ : CekEnv} {t : Term}
    {v : CekValue}, FactsHold P Γ env ρ → EnvDistinct env → freshIn env e = true →
    lowerTotalExpr env e = some t → Halts ρ t v → ShapeHolds (shapeOf fuel depth Γ e) v

theorem stripLams_spec : ∀ (count : Nat) (expression : Expr) (binders : List VarId) (body : Expr),
    stripLams count expression = some (binders, body) →
      expression = lambdas binders body ∧ binders.length = count
  | 0, expression, binders, body, h => by
    simp only [stripLams, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | count + 1, .Lam binder inner, binders, body, h => by
    simp only [stripLams] at h
    cases hs : stripLams count inner with
    | none => rw [hs] at h; cases h
    | some result =>
      obtain ⟨binders', body'⟩ := result
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, hlen⟩ := stripLams_spec count inner binders' body' hs
      exact ⟨rfl, by simp [hlen]⟩
  | _ + 1, .Var _, _, _, h | _ + 1, .Lit _, _, _, h | _ + 1, .Builtin _, _, _, h
  | _ + 1, .Error, _, _, h | _ + 1, .Fix _ _, _, _, h | _ + 1, .App _ _, _, _, h
  | _ + 1, .Force _, _, _, h | _ + 1, .Delay _, _, _, h | _ + 1, .Constr _ _, _, _, h
  | _ + 1, .Case _ _, _, _, h | _ + 1, .Let _ _, _, _, h => by simp [stripLams] at h

theorem stripLams_zero (expression : Expr) : stripLams 0 expression = some ([], expression) := rfl

/-- Facts survive entering binders after hiding the facts about them. -/
theorem FactsHold.hide {Γ : List (VarId × Expr)} {env : List VarId} {ρ : CekEnv}
    (h : FactsHold P Γ env ρ) (binders : List VarId) (fields : List CekValue)
    (hlen : fields.length = binders.length) :
    FactsHold P (hideBinders binders Γ) (binders.reverse ++ env) (extendAll ρ fields) := by
  apply FactsHold.append_fresh binders.reverse
    (h.filter (fun key => !binders.contains key) fun x y hxy => by
      show (!binders.contains x) = (!binders.contains y); rw [contains_congr hxy])
  · intro entry hmem
    have hkeep := not_contains_of_filter hmem
    simp only [Bool.not_eq_true'] at hkeep
    apply envLookupT_none_of_contains
    rw [Bool.eq_false_iff] at hkeep ⊢
    intro hc
    apply hkeep
    rw [List.contains_iff_exists_mem_beq] at hc ⊢
    obtain ⟨z, hz, hzb⟩ := hc
    exact ⟨z, List.mem_reverse.mp hz, hzb⟩
  · rw [List.length_reverse, ← hlen]; exact dropEnv_extendAll ρ fields

/-- An alternative that is not a lambda returns its own value, unless the
    scrutinee supplies fields to a constructor. -/
theorem plain_sound {fuel depth : Nat} (ih : ShapeSound P fuel) {Γ : List (VarId × Expr)} {alt : Expr}
    {env : List VarId} {ρ : CekEnv} {talt : Term} {fields : List CekValue} {v : CekValue}
    (hfacts : FactsHold P Γ env ρ) (hd : EnvDistinct env) (hfa : freshIn env alt = true)
    (hta : lowerTotalExpr env alt = some talt)
    (hrun : Reaches (.compute (fields.map Frame.applyArg) ρ talt) (.halt v)) :
    ShapeHolds (plainAlternativeShape (shapeOf fuel depth) Γ alt) v := by
  unfold plainAlternativeShape
  split
  · trivial
  · rcases sequence (.inr ⟨v, rfl⟩) hrun with ⟨_, impossible⟩ | ⟨a, ha, rest⟩
    · cases impossible
    · have hshape := ih depth Γ alt hfacts hd hfa hta ha
      cases fields with
      | nil =>
        have h1 := reaches_halt_of_step (by simp) rest
        simp only [List.map_nil, step] at h1
        obtain ⟨m, hm⟩ := h1
        rw [steps_halt] at hm; cases hm
        exact hshape
      | cons f fs =>
        rcases holds_constr_or_any _ hshape with ⟨tag, vs, rfl⟩ | hall
        · have := ret_applyArg_constr (.inr ⟨v, rfl⟩) rest
          cases this
        · exact hall v

theorem alternative_sound {fuel depth : Nat} (hP : ∀ env ρ rhs v, P env ρ rhs v → Produces env ρ rhs v ∧ freshIn env rhs = true)
    (ih : ShapeSound P fuel) {Γ : List (VarId × Expr)}
    {scrut alt : Expr} {env : List VarId} {ρ : CekEnv} {ts talt : Term} {w v : CekValue} {tag : Nat}
    {fields : List CekValue}
    (hfacts : FactsHold P Γ env ρ) (hd : EnvDistinct env) (hfs : freshIn env scrut = true)
    (hfa : freshIn env alt = true) (hts : lowerTotalExpr env scrut = some ts)
    (hta : lowerTotalExpr env alt = some talt) (hw : Halts ρ ts w) (hcf : CaseFields w tag fields)
    (hrun : Reaches (.compute (fields.map Frame.applyArg) ρ talt) (.halt v)) :
    ShapeHolds (alternativeShape (shapeOf fuel depth) (knownList fuel Γ scrut) Γ
      (shapeOf fuel depth Γ scrut) tag alt) v := by
  have hscrut := ih depth Γ scrut hfacts hd hfs hts hw
  -- the tag fields recorded by the scrutinee shape
  have hknown : ∀ shapes, (shapeOf fuel depth Γ scrut).atTag tag = .fields shapes →
      FieldsHold shapes fields := by
    intro shapes hs
    rcases hcf with rfl | ⟨c, numCtors, rfl, _⟩
    · rcases atTag_constr _ hscrut with hu | ⟨shapes', hs', hf⟩
      · rw [hu] at hs; cases hs
      · rw [hs'] at hs; cases hs; exact hf
    · rw [atTag_other _ hscrut (fun _ _ h => by cases h) tag] at hs; cases hs
  have hunreach : (shapeOf fuel depth Γ scrut).atTag tag ≠ .unreachable := by
    intro hs
    rcases hcf with rfl | ⟨c, numCtors, rfl, _⟩
    · rcases atTag_constr _ hscrut with hu | ⟨shapes', hs', _⟩
      · rw [hu] at hs; cases hs
      · rw [hs'] at hs; cases hs
    · rw [atTag_other _ hscrut (fun _ _ h => by cases h) tag] at hs; cases hs
  unfold alternativeShape
  split
  · rename_i hs; exact absurd hs hunreach
  · rename_i shapes hs
    have hfields := hknown shapes hs
    have hlen := fieldsHold_length hfields
    split
    · rename_i binders body hstrip
      obtain ⟨rfl, hblen⟩ := stripLams_spec _ _ _ _ hstrip
      obtain ⟨tb, htb, rfl⟩ := lower_lambdas hta
      have hbody : Halts (extendAll ρ fields) tb v := by
        have hreach := reaches_telescope fields [] ρ tb
        rw [List.append_nil, show fields.length = binders.length by omega] at hreach
        exact reaches_terminal_after (.inr ⟨v, rfl⟩) hreach hrun
      have hrecur : ShapeHolds (shapeOf fuel depth (hideBinders binders Γ) body) v := by
        obtain ⟨hfb, hdb⟩ := fresh_lambdas hfa hd
        exact ih depth _ body (hfacts.hide binders fields (by omega)) hdb hfb htb hbody
      split
      · rename_i x
        split
        · rename_i field hfield
          unfold fieldOf at hfield
          cases hidx : envLookupT binders.reverse x with
          | none => rw [hidx] at hfield; cases hfield
          | some index =>
            rw [hidx] at hfield
            simp only [Option.map_some, Option.some.injEq] at hfield
            have hlow : lowerTotalExpr (binders.reverse ++ env) (.Var x) = some (.Var (index + 1)) := by
              rw [lowerTotalExpr_var, envLookupT_append_of_some hidx]; rfl
            rw [htb] at hlow; cases hlow
            have hlook := lookup_field (ρ := ρ) (fields := fields) (by omega) hidx hfield.symm
            have hv := halts_var hbody
            rw [hlook] at hv
            have hbound := envLookupT_bound binders.reverse x index hidx
            simp only [List.length_reverse] at hbound
            obtain ⟨s, hs'⟩ : ∃ s, shapes[field]? = some s := by
              cases h : shapes[field]? with
              | none => rw [List.getElem?_eq_none_iff] at h; omega
              | some s => exact ⟨s, rfl⟩
            have hget : shapes.getD field .any = s := by
              rw [List.getD_eq_getElem?_getD, hs']; rfl
            rw [hget]
            exact fieldsHold_get hfields field s v hs' hv
        · exact hrecur
      · exact hrecur
    · exact plain_sound ih hfacts hd hfa hta hrun
  · rename_i hs
    split
    · rename_i head tail body
      split
      · rename_i hlist
        simp only [Bool.and_eq_true, beq_iff_eq] at hlist
        obtain ⟨hlist, rfl⟩ := hlist
        have hlistValue := knownList_sound (fun _ _ _ _ h => (hP _ _ _ _ h).1) fuel Γ scrut hlist
          hfacts hd hts hw
        obtain ⟨c, numCtors, rfl, hc⟩ : ∃ c numCtors, w = .VCon c ∧
            constToTagAndFields c = some (0, numCtors, fields) := by
          rcases hcf with rfl | hcon
          · simp [ListShape.ListValue] at hlistValue
          · exact hcon
        have hfl : fields.length = 2 := by
          cases c <;> simp [ListShape.ListValue] at hlistValue <;>
            simp [constToTagAndFields] at hc
          all_goals
            first
              | (rename_i l; cases l <;> simp at hc; obtain ⟨_, _, rfl⟩ := hc; rfl)
        obtain ⟨tb, htb, rfl⟩ := lower_lambdas (binders := [head, tail]) (body := body) hta
        have hbody : Halts (extendAll ρ fields) tb v := by
          have hreach := reaches_telescope fields [] ρ tb
          rw [List.append_nil, hfl] at hreach
          exact reaches_terminal_after (.inr ⟨v, rfl⟩) hreach hrun
        obtain ⟨hfb, hdb⟩ := fresh_lambdas (binders := [head, tail]) hfa hd
        exact ih depth _ body (hfacts.hide [head, tail] fields (by simp [hfl])) hdb hfb htb hbody
      · trivial
    · exact plain_sound ih hfacts hd hfa hta hrun

theorem alternativesShape_holds (recur : List (VarId × Expr) → Expr → Shape) (listScrutinee : Bool)
    (Γ : List (VarId × Expr)) (scrutinee : Shape) :
    ∀ (base : Nat) (alts : List Expr) (j : Nat) (alt : Expr) (v : CekValue), alts[j]? = some alt →
      ShapeHolds (alternativeShape recur listScrutinee Γ scrutinee (base + j) alt) v →
      ShapeHolds (alternativesShape recur listScrutinee Γ scrutinee base alts) v
  | _, [], _, _, _, h, _ => by simp at h
  | base, a :: rest, 0, alt, v, h, hv => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [alternativesShape, ShapeHolds]
    exact .inl hv
  | base, a :: rest, j + 1, alt, v, h, hv => by
    simp only [alternativesShape, ShapeHolds]
    right
    exact alternativesShape_holds recur listScrutinee Γ scrutinee (base + 1) rest j alt v
      (by simpa using h) (by rw [show base + 1 + j = base + (j + 1) by omega]; exact hv)

/-! ## Bindings -/

theorem let_sound {fuel depth : Nat} (hP : ∀ env ρ rhs v, P env ρ rhs v → Produces env ρ rhs v ∧ freshIn env rhs = true)
    (hPush : ∀ env ρ rhs v, Produces env ρ rhs v → freshIn env rhs = true → P env ρ rhs v)
    (ih : ShapeSound P fuel) (body : Expr) :
    ∀ (bindings : List (VarId × Expr × Bool)) (Γ₀ : List (VarId × Expr)) {env : List VarId}
      {ρ : CekEnv} {t : Term} {v : CekValue},
      FactsHold P Γ₀ env ρ → EnvDistinct env → freshIn env (.Let bindings body) = true →
      lowerTotalExpr env (.Let bindings body) = some t → Halts ρ t v →
      ShapeHolds (shapeOf fuel depth
        (bindings.foldl (fun available (binder, rhs, _) => (binder, rhs) :: available) Γ₀) body) v
  | [], Γ₀, env, ρ, t, v, hfacts, hd, hfresh, hlow, hv => by
    rw [freshIn_let_nil] at hfresh
    rw [lowerTotalExpr_let_nil] at hlow
    exact ih depth Γ₀ body hfacts hd hfresh hlow hv
  | (x, r, er) :: rest, Γ₀, env, ρ, t, v, hfacts, hd, hfresh, hlow, hv => by
    rw [freshIn_let_cons] at hfresh
    simp only [freshIn, freshInLet, Bool.and_eq_true] at hfresh
    obtain ⟨⟨hfr, hx⟩, hrest⟩ := hfresh
    rw [lowerTotalExpr_let_cons] at hlow
    obtain ⟨tr, tb, htr, htb, rfl⟩ := lowerTotalExpr_let_single_some hlow
    obtain ⟨wf, wa, hwf, hwa, happ⟩ := halts_apply hv
    rw [halts_lam hwf] at happ
    rcases apply_reaches happ with ⟨body', ρ', heq, hb⟩ | ⟨_, _, _, heq, _⟩
    · injection heq with hb₁ hρ₁
      subst hb₁ hρ₁
      exact let_sound hP hPush ih body rest ((x, r) :: Γ₀) (env := x :: env)
        (hfacts.push (hPush env ρ r wa ⟨tr, htr, hwa⟩ hfr)) (hd.cons hx)
        (by simpa [freshIn] using hrest) htb hb
    · cases heq

/-! ## Soundness -/

theorem shapeOf_sound (hP : ∀ env ρ rhs v, P env ρ rhs v → Produces env ρ rhs v ∧ freshIn env rhs = true)
    (hPush : ∀ env ρ rhs v, Produces env ρ rhs v → freshIn env rhs = true → P env ρ rhs v) :
    ∀ fuel, ShapeSound P fuel := by
  intro fuel
  induction fuel with
  | zero => intro depth Γ e env ρ t v _ _ _ _ _; simp only [shapeOf]; trivial
  | succ fuel ih =>
    intro depth Γ e env ρ t v hfacts hd hfresh hlow hv
    cases e with
    | Error =>
      rw [lowerTotalExpr_error] at hlow; cases hlow
      exact absurd hv not_halts_error
    | Constr tag fields =>
      rw [MIR.lowerTotalExpr_constr_of_list] at hlow
      cases hts : MIR.lowerTotalExprList env fields with
      | none => rw [hts] at hlow; cases hlow
      | some ts =>
        rw [hts] at hlow; cases hlow
        obtain ⟨vs, rfl, hvlen, hvs⟩ := halts_constr hv
        obtain ⟨htlen, hidx⟩ := lowerTotalExprList_index hts
        simp only [freshIn] at hfresh
        cases depth with
        | zero =>
          simp only [shapeOf, ShapeHolds]
          exact ⟨vs, rfl, fieldsHold_map_any fields vs (by omega)⟩
        | succ depth =>
          simp only [shapeOf, ShapeHolds]
          refine ⟨vs, rfl, fieldsHold_of_get (by simp; omega) ?_⟩
          intro k s u hs hu
          rw [List.getElem?_map] at hs
          cases hfk : fields[k]? with
          | none => rw [hfk] at hs; cases hs
          | some field =>
            rw [hfk] at hs; cases hs
            obtain ⟨tk, htk⟩ : ∃ tk, ts[k]? = some tk := by
              cases h : ts[k]? with
              | none =>
                rw [List.getElem?_eq_none_iff] at h
                have := (List.getElem?_eq_some_iff.mp hfk).1; omega
              | some tk => exact ⟨tk, rfl⟩
            exact ih depth Γ field hfacts hd
              (freshInList_iff.mp hfresh field (List.mem_of_getElem? hfk))
              (hidx k field tk hfk htk) (hvs k tk u htk hu)
    | Var x =>
      simp only [shapeOf]
      split
      · rename_i entry hf
        obtain ⟨k, _, hp, hfacts', hd'⟩ := fact_of_var hfacts hd hf hlow hv
        obtain ⟨⟨t', ht', hv'⟩, hfr'⟩ := hP _ _ _ _ hp
        exact ih depth Γ entry.2 hfacts' hd' hfr' ht' hv'
      · trivial
    | Let bindings body =>
      simp only [shapeOf]
      exact let_sound hP hPush ih body bindings Γ hfacts hd hfresh hlow hv
    | Case scrut alts =>
      simp only [shapeOf]
      obtain ⟨ts, talts, hts, htalts, rfl⟩ := lowerTotalExpr_case_some hlow
      simp only [freshIn, Bool.and_eq_true] at hfresh
      obtain ⟨w, hw, hrest⟩ := halts_case hv
      obtain ⟨tag, fields, talt, hget, hcf, hrun⟩ :=
        case_dispatch (.inr ⟨v, rfl⟩) hrest (by simp)
      rw [List.append_nil] at hrun
      obtain ⟨htlen, hidx⟩ := lowerTotalExprList_index htalts
      obtain ⟨alt, halt⟩ : ∃ alt, alts[tag]? = some alt := by
        cases h : alts[tag]? with
        | none =>
          rw [List.getElem?_eq_none_iff] at h
          have := (List.getElem?_eq_some_iff.mp hget).1; omega
        | some alt => exact ⟨alt, rfl⟩
      apply alternativesShape_holds _ _ _ _ 0 alts tag alt v halt
      rw [Nat.zero_add]
      exact alternative_sound hP ih hfacts hd hfresh.1
        (freshInList_iff.mp hfresh.2 alt (List.mem_of_getElem? halt)) hts
        (hidx tag alt talt halt hget) hw hcf hrun
    | Force body =>
      simp only [shapeOf]
      obtain ⟨tb, htb, rfl⟩ := lowerTotalExpr_force_some hlow
      obtain ⟨w, hw, hr⟩ := halts_force hv
      simp only [freshIn] at hfresh
      have force_suspension : ∀ {d : Expr}, SuspensionOf P Γ env ρ d w →
          ShapeHolds (shapeOf fuel depth Γ d) v := by
        intro d hsusp
        obtain ⟨k, dt, _, hdt, rfl, hfd, hfacts', hd'⟩ := hsusp
        have h1 := reaches_halt_of_step (by simp) hr
        simp only [step] at h1
        exact ih depth Γ d hfacts' hd' hfd hdt h1
      split
      · rename_i delayed heq
        exact force_suspension (resolveHead_delay hP fuel Γ body heq hfacts hd hfresh htb hw)
      · rename_i selector _ first second heq
        split
        · rename_i hsel
          rcases resolveHead_select hP fuel Γ body heq (beq_selector hsel) hfacts hd hfresh htb hw
            with hs | hs
          · exact .inl (force_suspension hs)
          · exact .inr (force_suspension hs)
        · trivial
      · trivial
    | Lit _ | Builtin _ | Lam _ _ | Fix _ _ | App _ _ | Delay _ =>
      simp only [shapeOf]; trivial

end Moist.Verified.ShapeFacts
