import Moist.Verified.ShapesSoundness.Rewrites

variable [sv : Moist.CEK.SemVariant]

/-! # Boolean case rewrites

`booleanCaseRewrite` moves a case with small alternatives into the branches
of a Boolean case tree (`pushBooleanCase`) and removes the identity case
`case b [False, True]` on a known Boolean. Each step refines its input under
the facts of the walk:

* a case on a known Boolean passes no fields to its alternatives, so an outer
  case may run inside each of them (`case_of_case_factRel`);
* a `let` scrutinee moves out of a case whose alternatives do not mention its
  binder (`case_let_hoist_factRel`);
* cases on Boolean literals and on `error` are resolved directly.
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines

/-! ## Small alternatives -/

theorem smallAlternative_freshIn {a : Expr} (h : smallAlternative a = true) (env : List VarId) :
    freshIn env a = true := by
  cases a <;> simp_all [smallAlternative, freshIn]

theorem freshInList_small : ∀ {outer : List Expr}, (∀ a ∈ outer, smallAlternative a = true) →
    ∀ env, freshInList env outer = true
  | [], _, _ => by simp [freshInList]
  | a :: as, h, env => by
    simp only [freshInList, Bool.and_eq_true]
    exact ⟨smallAlternative_freshIn (h a (.head _)) env,
      freshInList_small (fun b hb => h b (.tail _ hb)) env⟩

theorem walkBinder_genSafe {base : Nat} {x : VarId} (h : walkBinder base x = true) : GenSafe base x := by
  unfold walkBinder at h
  cases hx : x.origin with
  | gen => rw [hx] at h; exact .inl (by simpa using h)
  | source => exact .inr (by rw [hx]; simp)

/-! ## Lowering of mapped alternatives -/

theorem lowerTotalExprList_map_case (env : List VarId) (outer : List Expr) (touter : List Term)
    (houter : MIR.lowerTotalExprList env outer = some touter) :
    ∀ (alts : List Expr) (talts : List Term), MIR.lowerTotalExprList env alts = some talts →
      MIR.lowerTotalExprList env (alts.map fun a => .Case a outer) =
        some (talts.map fun ta => .Case ta touter)
  | [], talts, h => by
    rw [MIR.lowerTotalExprList_nil] at h; cases h
    simp [MIR.lowerTotalExprList_nil]
  | a :: as, talts, h => by
    rw [MIR.lowerTotalExprList_cons] at h
    cases ha : lowerTotalExpr env a with
    | none => rw [ha] at h; cases h
    | some ta =>
      cases has : MIR.lowerTotalExprList env as with
      | none => rw [ha, has] at h; cases h
      | some tas =>
        rw [ha, has] at h; cases h
        rw [List.map_cons, MIR.lowerTotalExprList_cons, MIR.lowerTotalExpr_case_of_list, ha, houter,
          lowerTotalExprList_map_case env outer touter houter as tas has]
        rfl

theorem listRel_map_of {α : Type} {R : α → α → Prop} {f g : α → α} (h : ∀ a, R (f a) (g a)) :
    ∀ (xs : List α), ListRel R (xs.map f) (xs.map g)
  | [] => trivial
  | x :: xs => ⟨h x, listRel_map_of h xs⟩

/-! ## Local steps -/

theorem case_error_factRel {G : VarId → Prop} {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} (outer : List Expr) : FactRel G P Γ (.Case .Error outer) .Error := by
  intro env t _ _ _ _ _ hlow
  obtain ⟨ts, talts, hts, _, rfl⟩ := lowerTotalExpr_case_some hlow
  rw [lowerTotalExpr_error] at hts; cases hts
  refine ⟨.Error, lowerTotalExpr_error env, ?_⟩
  intro ρ π _ _ _ _
  exact obsRefines_of_reaches (reaches_of_steps 2 rfl) (reaches_of_steps 1 rfl) (obsRefines_refl _)

theorem case_litBool_factRel {G : VarId → Prop} {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} (c : Bool) (whenFalse whenTrue : Expr) :
    FactRel G P Γ (.Case (litBool c) [whenFalse, whenTrue]) (if c then whenTrue else whenFalse) := by
  intro env t _ _ _ _ _ hlow
  obtain ⟨tsc, tf, tt, hsc, htf, htt, rfl⟩ := lowerTotalExpr_case2_some hlow
  rw [lowerTotalExpr_litBool] at hsc; cases hsc
  refine ⟨if c then tt else tf, by cases c <;> simpa, ?_⟩
  intro ρ π _ _ _ _
  exact obsRefines_of_reaches (case_bool_steps (halts_constant_of _ _)) (reaches_refl _) (obsRefines_refl _)

/-- A `let` scrutinee moves outside a case whose alternatives do not mention
    its binder. -/
theorem case_let_hoist_factRel {G : VarId → Prop} {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} (x : VarId) (r body : Expr) (er : Bool) (outer : List Expr)
    (hx : ∀ a ∈ outer, (freeVars a).contains x = false) :
    FactRel G P Γ (.Case (.Let [(x, r, er)] body) outer) (.Let [(x, r, er)] (.Case body outer)) := by
  intro env t _ _ _ _ _ hlow
  obtain ⟨ts, talts, hts, htalts, rfl⟩ := lowerTotalExpr_case_some hlow
  obtain ⟨tr, tb, htr, htb, rfl⟩ := lowerTotalExpr_let_single_some hts
  have hshift : MIR.lowerTotalExprList (x :: env) outer =
      some (renameTermList (shiftRename 1) talts) := by
    rw [MIR.lowerTotalExprList_prepend_unused env x outer hx, htalts]; rfl
  refine ⟨.Apply (.Lam 0 (.Case tb (renameTermList (shiftRename 1) talts))) tr, ?_, ?_⟩
  · rw [lowerTotalExpr_let_single, htr, MIR.lowerTotalExpr_case_of_list, htb, hshift]; rfl
  · intro ρ π henv hlen hπ _
    have closedR := MIR.lowerTotalExpr_closedAt htr
    have closedB := MIR.lowerTotalExpr_closedAt htb
    have closedAlts := lowerTotalExprList_closedAtList htalts
    simp only [List.length_cons] at closedB
    refine obsRefines_of_reaches (reaches_of_steps 4 rfl) (reaches_of_steps 3 rfl) ?_
    refine obsRefines_of_continuation ?_
    intro w hw
    have hwf := halts_wellFormed henv hlen closedR hw
    refine obsRefines_of_reaches (reaches_of_steps 1 rfl) (reaches_of_steps 2 rfl) ?_
    have henv' := envWellFormed_extend env.length henv hlen hwf
    have hbisim : ShiftBisimState (.compute (.caseScrutinee talts ρ :: π) (ρ.extend w) tb)
        (.compute (.caseScrutinee (renameTermList (shiftRename 1) talts) (ρ.extend w) :: π) (ρ.extend w)
          (renameTerm id tb)) :=
      .compute FundamentalRefines.is0preserving_id (shiftBisimEnv_refl_id_aux henv') closedB
        (.cons (.caseScrutinee (FundamentalRefines.is0preserving_shiftRename (by omega))
          (shiftBisimEnv_shift w henv) closedAlts) (shiftBisimStack_refl hπ))
    rw [renameTerm_id] at hbisim
    exact (obsRefines_of_shiftBisim hbisim).1

/-- A case on a known Boolean passes no fields to its alternatives, so an
    outer case can run inside each of them. -/
theorem case_of_case_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {inner : Expr}
    {alts outer : List Expr} (hknown : knownBoolean 64 Γ inner = true) :
    FactRel G PF Γ (.Case (.Case inner alts) outer) (.Case inner (alts.map fun a => .Case a outer)) := by
  intro env t _ hd hfresh _ _ hlow
  simp only [freshIn, Bool.and_eq_true] at hfresh
  obtain ⟨tc, touter, htc, houter, rfl⟩ := lowerTotalExpr_case_some hlow
  obtain ⟨ti, talts, hti, htalts, rfl⟩ := lowerTotalExpr_case_some htc
  have hmap := lowerTotalExprList_map_case env outer touter houter alts talts htalts
  refine ⟨.Case ti (talts.map fun ta => .Case ta touter), by
    rw [MIR.lowerTotalExpr_case_of_list, hti, hmap]; rfl, ?_⟩
  intro ρ π henv hlen hπ hF
  refine obsRefines_of_reaches (reaches_of_steps 2 rfl) (reaches_of_steps 1 rfl) ?_
  refine obsRefines_of_continuation ?_
  intro v hv
  obtain ⟨c, rfl⟩ := knownBoolean_sound PF_hP 64 Γ inner hknown hF hd hfresh.1.1 hti hv
  have hlen' : (talts.map fun ta => Term.Case ta touter).length = talts.length := List.length_map _
  rcases bool_case_frames talts ρ (.caseScrutinee touter ρ :: π) c with
    ⟨hl, hs⟩ | ⟨hl, hget, hs⟩ | ⟨alt, hl, hget, hs⟩
  · rcases bool_case_frames (talts.map fun ta => Term.Case ta touter) ρ π c with
      ⟨_, ht⟩ | ⟨hl', _, _⟩ | ⟨_, hl', _, _⟩
    · exact obsRefines_of_reaches (reaches_of_steps 1 hs) (reaches_of_steps 1 ht) (obsRefines_refl _)
    · exact absurd (by rw [hlen']; exact hl) hl'
    · exact absurd (by rw [hlen']; exact hl) hl'
  · rcases bool_case_frames (talts.map fun ta => Term.Case ta touter) ρ π c with
      ⟨hl', _⟩ | ⟨_, _, ht⟩ | ⟨_, _, hget', _⟩
    · exact absurd (by rw [← hlen']; exact hl') hl
    · exact obsRefines_of_reaches (reaches_of_steps 1 hs) (reaches_of_steps 1 ht) (obsRefines_refl _)
    · rw [List.getElem?_map, hget] at hget'; cases hget'
  · rcases bool_case_frames (talts.map fun ta => Term.Case ta touter) ρ π c with
      ⟨hl', _⟩ | ⟨_, hget', _⟩ | ⟨alt', _, hget', ht⟩
    · exact absurd (by rw [← hlen']; exact hl') hl
    · rw [List.getElem?_map, hget] at hget'; cases hget'
    · rw [List.getElem?_map, hget] at hget'
      cases hget'
      exact obsRefines_of_reaches (reaches_of_steps 1 hs)
        (reaches_trans (reaches_of_steps 1 ht) (reaches_of_steps 1 rfl)) (obsRefines_refl _)

/-- A case on a known Boolean with alternatives `[False, True]` returns its
    scrutinee. -/
theorem case_identity_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {s : Expr}
    (hknown : knownBoolean 64 Γ s = true) :
    FactRel G PF Γ (.Case s [litBool false, litBool true]) s := by
  intro env t _ hd hfresh _ _ hlow
  simp only [freshIn, Bool.and_eq_true] at hfresh
  obtain ⟨ts, tf, tt, hts, htf, htt, rfl⟩ := lowerTotalExpr_case2_some hlow
  rw [lowerTotalExpr_litBool] at htf htt
  cases htf; cases htt
  refine ⟨ts, hts, ?_⟩
  intro ρ π henv hlen hπ hF
  refine obsRefines_of_reaches (reaches_of_steps 1 rfl) (reaches_refl _) ?_
  refine obsRefines_of_continuation ?_
  intro v hv
  obtain ⟨c, rfl⟩ := knownBoolean_sound PF_hP 64 Γ s hknown hF hd hfresh.1 hts hv
  exact obsRefines_of_reaches (reaches_of_steps 2 (by cases c <;> rfl)) (reaches_refl _)
    (obsRefines_refl _)

end Moist.Verified.ShapeFacts

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence

/-! ## Moving a case into a Boolean case tree -/

theorem case_let_cons_lower (outer : List Expr) (b : VarId × Expr × Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) (env : List VarId) :
    lowerTotalExpr env (.Case (.Let (b :: rest) body) outer) =
      lowerTotalExpr env (.Case (.Let [b] (.Let rest body)) outer) := by
  rw [MIR.lowerTotalExpr_case_of_list, MIR.lowerTotalExpr_case_of_list, lowerTotalExpr_let_cons]

theorem case_let_cons_fresh (outer : List Expr) (b : VarId × Expr × Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) (avoid : List VarId) :
    freshIn avoid (.Case (.Let (b :: rest) body) outer) =
      freshIn avoid (.Case (.Let [b] (.Let rest body)) outer) := by
  obtain ⟨x, r, er⟩ := b
  simp only [freshIn, freshInLet]

theorem case_let_nil_lower (outer : List Expr) (body : Expr) (env : List VarId) :
    lowerTotalExpr env (.Case (.Let [] body) outer) = lowerTotalExpr env (.Case body outer) := by
  rw [MIR.lowerTotalExpr_case_of_list, MIR.lowerTotalExpr_case_of_list, lowerTotalExpr_let_nil]

theorem case_let_nil_fresh (outer : List Expr) (body : Expr) (avoid : List VarId) :
    freshIn avoid (.Case (.Let [] body) outer) = freshIn avoid (.Case body outer) := by
  simp only [freshIn, freshInLet]

theorem pushBooleanCase_fresh (base : Nat) :
    ∀ (fuel : Nat) (Γ : List (VarId × Expr)) (s : Expr) (outer : List Expr) (env : List VarId),
      (∀ a ∈ outer, smallAlternative a = true) → freshIn env (.Case s outer) = true →
      freshIn env (pushBooleanCase base fuel Γ s outer) = true
  | 0, _, _, _, _, _, h => by simpa [pushBooleanCase] using h
  | fuel + 1, Γ, s, outer, env, hsmall, h => by
    unfold pushBooleanCase
    split
    · exact smallAlternative_freshIn (hsmall _ (.head _)) env
    · exact smallAlternative_freshIn (hsmall _ (.tail _ (.head _))) env
    · simp [freshIn]
    · rename_i _ body
      exact pushBooleanCase_fresh base fuel Γ body outer env hsmall (by rwa [case_let_nil_fresh] at h)
    · rename_i binder rhs erased rest body
      split
      · rw [case_let_cons_fresh] at h
        simp only [freshIn, freshInLet, Bool.and_eq_true] at h ⊢
        obtain ⟨⟨⟨hr, hx⟩, hb⟩, _⟩ := h
        refine ⟨⟨hr, hx⟩, ?_⟩
        refine pushBooleanCase_fresh base fuel _ _ outer _ hsmall ?_
        simp only [freshIn, Bool.and_eq_true]
        exact ⟨by simpa [freshIn, freshInLet] using hb, freshInList_small hsmall _⟩
      · exact h
    · rename_i inner alternatives
      split
      · simp only [freshIn, Bool.and_eq_true] at h ⊢
        obtain ⟨⟨hi, ha⟩, ho⟩ := h
        refine ⟨hi, ?_⟩
        rw [freshInList_iff] at ha ⊢
        intro a hmem
        obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp hmem
        exact pushBooleanCase_fresh base fuel Γ a₀ outer env hsmall
          (by simp only [freshIn, Bool.and_eq_true]; exact ⟨ha a₀ ha₀, ho⟩)
      · exact h
    · exact h

theorem pushBooleanCase_factRel (base : Nat) :
    ∀ (fuel : Nat) (Γ : List (VarId × Expr)) (s : Expr) (outer : List Expr),
      (∀ a ∈ outer, smallAlternative a = true) →
      FactRel (GenSafe base) PF Γ (.Case s outer) (pushBooleanCase base fuel Γ s outer)
  | 0, Γ, s, outer, _ => by simpa [pushBooleanCase] using FactRel.refl (GenSafe base) PF Γ (.Case s outer)
  | fuel + 1, Γ, s, outer, hsmall => by
    unfold pushBooleanCase
    split
    · exact case_litBool_factRel false _ _
    · exact case_litBool_factRel true _ _
    · exact case_error_factRel _
    · rename_i _ body
      exact (pushBooleanCase_factRel base fuel Γ body outer hsmall).congr_left
        (case_let_nil_lower outer body) (case_let_nil_fresh outer body)
    · rename_i binder rhs erased rest body
      split
      · rename_i hcond
        simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hcond
        obtain ⟨hwb, hfv⟩ := hcond
        have hoist := (case_let_hoist_factRel (G := GenSafe base) (P := PF) (Γ := Γ) binder rhs
          (.Let rest body) erased outer hfv).congr_left (case_let_cons_lower outer _ rest body)
          (case_let_cons_fresh outer _ rest body)
        refine hoist.trans (FactRel.let_single rhs (walkBinder_genSafe hwb) (.inl rfl)
          (FactRel.refl _ _ _ _)
          (pushBooleanCase_factRel base fuel ((binder, rhs) :: Γ) (.Let rest body) outer hsmall)
          (fun _ _ _ _ _ hfr hp => ⟨hp, hfr⟩)) ?_
        intro env _ h
        rw [case_let_cons_fresh] at h
        simp only [freshIn, freshInLet, Bool.and_eq_true] at h ⊢
        obtain ⟨⟨⟨hr, hx⟩, hb⟩, _⟩ := h
        exact ⟨⟨hr, hx⟩, by simpa [freshIn, freshInLet] using hb, freshInList_small hsmall _⟩
      · exact FactRel.refl _ _ _ _
    · rename_i inner alternatives
      split
      · rename_i hknown
        refine (case_of_case_factRel hknown).trans
          (FactRel.case (FactRel.refl _ _ _ _)
            (listRel_map_of (fun a => pushBooleanCase_factRel base fuel Γ a outer hsmall) alternatives)) ?_
        intro env _ h
        simp only [freshIn, Bool.and_eq_true] at h ⊢
        obtain ⟨⟨hi, ha⟩, ho⟩ := h
        refine ⟨hi, ?_⟩
        rw [freshInList_iff] at ha ⊢
        intro a hmem
        obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp hmem
        simp only [freshIn, Bool.and_eq_true]
        exact ⟨ha a₀ ha₀, ho⟩
      · exact FactRel.refl _ _ _ _
    · exact FactRel.refl _ _ _ _

/-! ## The Boolean case rewrite -/

theorem booleanCaseRewrite_factRel (useShapes : Bool) (base : Nat) (Γ : List (VarId × Expr)) (x : Expr) :
    FactRel (GenSafe base) PF Γ x (booleanCaseRewrite useShapes base Γ x) := by
  unfold booleanCaseRewrite
  split
  · exact FactRel.refl _ _ _ _
  · split
    · rename_i inner innerAlternatives outer
      split
      · rename_i hcond
        simp only [Bool.and_eq_true, List.all_eq_true] at hcond
        exact pushBooleanCase_factRel base 32 Γ _ outer hcond.1.1.2
      · exact FactRel.refl _ _ _ _
    · split
      · rename_i scrutinee hknown
        exact case_identity_factRel hknown
      · exact FactRel.refl _ _ _ _
    · exact FactRel.refl _ _ _ _

theorem booleanCaseRewrite_fresh (useShapes : Bool) (base : Nat) (Γ : List (VarId × Expr)) {x : Expr}
    {env : List VarId} (hx : freshIn env x = true) :
    freshIn env (booleanCaseRewrite useShapes base Γ x) = true := by
  unfold booleanCaseRewrite
  split
  · exact hx
  · split
    · rename_i inner innerAlternatives outer
      split
      · rename_i hcond
        simp only [Bool.and_eq_true, List.all_eq_true] at hcond
        exact pushBooleanCase_fresh base 32 Γ _ outer env hcond.1.1.2 hx
      · exact hx
    · split
      · simp only [freshIn, Bool.and_eq_true] at hx; exact hx.1
      · exact hx
    · exact hx

end Moist.Verified.ShapeFacts
