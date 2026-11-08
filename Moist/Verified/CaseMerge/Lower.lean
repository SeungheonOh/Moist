import Moist.Verified.CaseMerge.Reduce

variable [sv : Moist.CEK.SemVariant]

/-! # Lowering and closedness of the case-merge result

`caseMerge_lower`: whenever the source lowers, so does the result, and every
de Bruijn depth at which the source is closed also closes the result. Fact
fields are atoms whose lowerings are tracked by `FieldsOK` / `FieldsClosed`.
-/

namespace Moist.Verified.CaseMerge

open Moist.CEK
open Moist.MIR
open Moist.Plutus.Term (Term)
open Moist.Verified (closedAt closedAtList renameTerm renameTermList shiftRename)
open Moist.Verified.Equivalence (ListRel)
open Moist.Verified.MIR (lowerTotalExprList lowerTotalExprList_nil lowerTotalExprList_cons
  lowerTotalExpr_case_of_list lowerTotalExpr_constr_of_list lowerTotalExpr_lam lowerTotalExpr_app
  lowerTotalExpr_force lowerTotalExpr_delay lowerTotalExpr_let_nil_eq lowerTotalExpr_prepend_unused
  lowerTotalExpr_closedAt lowerTotalList_closedAtList)

/-! ## Facts produced by `knownConstructor` -/

/-- Pointwise relation between lists of possibly different element types. -/
def ListRel2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ ListRel2 R as bs
  | _, _ => False

/-- A literal fact field and the constant value it denotes. -/
def LitField (f : Expr) (v : CekValue) : Prop := ∃ c ty, f = .Lit (c, ty) ∧ v = .VCon c

omit sv in
theorem mapM_lit_fields {g : CekValue × Moist.Plutus.Term.BuiltinType → Option Expr}
    (hg : ∀ v ty f, g (v, ty) = some f → ∃ c, v = .VCon c ∧ f = .Lit (c, ty)) :
    ∀ (vs : List CekValue) (tys : List Moist.Plutus.Term.BuiltinType) (fields : List Expr),
      vs.length = tys.length → (vs.zip tys).mapM g = some fields →
      ListRel2 LitField fields vs
  | [], [], fields, _, h => by simp at h; subst h; exact trivial
  | v :: vs, ty :: tys, fields, hl, h => by
    simp only [List.zip_cons_cons, List.mapM_cons, Option.bind_eq_bind] at h
    cases hgv : g (v, ty) with
    | none => simp [hgv] at h
    | some f =>
      cases hm : (vs.zip tys).mapM g with
      | none => simp [hgv, hm] at h
      | some fs =>
        simp [hgv, hm] at h
        subst h
        obtain ⟨c, rfl, rfl⟩ := hg v ty f hgv
        exact ⟨⟨c, ty, rfl, rfl⟩, mapM_lit_fields hg vs tys fs (by simpa using hl) hm⟩
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl

omit sv in
theorem knownConstructor_lit {Γ : KnownCtors} {c : Moist.Plutus.Term.Const}
    {ty : Moist.Plutus.Term.BuiltinType} {info : KnownCtor}
    (h : knownConstructor Γ (.Lit (c, ty)) = some info) :
    ∃ values, constToTagAndFields c = some (info.tag, info.constructorCount, values) ∧
      ListRel2 LitField info.fields values := by
  simp only [knownConstructor] at h
  cases hc : constToTagAndFields c with
  | none => simp [hc] at h
  | some r =>
    obtain ⟨tag, cc, vs⟩ := r
    simp only [hc, Option.bind_eq_bind, Option.bind_some] at h
    have hg : ∀ v ty' f, (fun (x : CekValue × Moist.Plutus.Term.BuiltinType) =>
        match x with
        | (CekValue.VCon field, fieldType) => some (Expr.Lit (field, fieldType))
        | _ => none) (v, ty') = some f → ∃ c, v = .VCon c ∧ f = .Lit (c, ty') := by
      intro v ty' f hv
      cases v <;> simp at hv
      subst hv; exact ⟨_, rfl, rfl⟩
    split at h
    all_goals
      first
      | (simp at h; done)
      | (simp only [Option.pure_def] at h
         obtain ⟨fs, hm, hinfo⟩ := Option.bind_eq_some_iff.mp h
         cases hinfo
         exact ⟨_, rfl, mapM_lit_fields hg _ _ fs (by simp) hm⟩)

omit sv in
theorem knownConstructor_var {Γ : KnownCtors} {y : VarId} {info : KnownCtor}
    (h : knownConstructor Γ (.Var y) = some info) :
    ∃ p ∈ Γ, (p.1 == y) = true ∧ p.2 = info := by
  simp only [knownConstructor, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  exact ⟨p, List.mem_of_find?_eq_some hp, by simpa using List.find?_some hp, rfl⟩

omit sv in
theorem knownConstructor_constr {Γ : KnownCtors} {tag : Nat} {fields : List Expr}
    {info : KnownCtor} (h : knownConstructor Γ (.Constr tag fields) = some info) :
    info = ⟨tag, 0, fields, false⟩ ∧ ∀ f ∈ fields, f.isAtom = true := by
  simp only [knownConstructor] at h
  split at h
  · rename_i hall
    cases h
    exact ⟨rfl, fun f hf => List.all_eq_true.mp hall f hf⟩
  · cases h

omit sv in
theorem knownConstructor_cases {Γ : KnownCtors} {e : Expr} {info : KnownCtor}
    (h : knownConstructor Γ e = some info) :
    (∃ y, e = .Var y ∧ ∃ p ∈ Γ, (p.1 == y) = true ∧ p.2 = info) ∨
    (∃ tag fields, e = .Constr tag fields ∧ info = ⟨tag, 0, fields, false⟩ ∧
      ∀ f ∈ fields, f.isAtom = true) ∨
    (∃ c ty, e = .Lit (c, ty) ∧ ∃ values,
      constToTagAndFields c = some (info.tag, info.constructorCount, values) ∧
      ListRel2 LitField info.fields values) := by
  cases e with
  | Var y => exact .inl ⟨y, rfl, knownConstructor_var h⟩
  | Constr tag fields => exact .inr (.inl ⟨tag, fields, rfl, knownConstructor_constr h⟩)
  | Lit l =>
    obtain ⟨c, ty⟩ := l
    exact .inr (.inr ⟨c, ty, rfl, knownConstructor_lit h⟩)
  | _ => simp [knownConstructor] at h

omit sv in
theorem listRel2_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, ListRel2 R xs ys → ∀ x ∈ xs, ∃ y ∈ ys, R x y
  | [], [], _, x, hx => by cases hx
  | a :: as, b :: bs, h, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, .head _, h.1⟩
    · obtain ⟨y, hy, hr⟩ := listRel2_mem_left h.2 x hx
      exact ⟨y, .tail _ hy, hr⟩
  | [], _ :: _, h, _, _ => absurd h id
  | _ :: _, [], h, _, _ => absurd h id

/-! ## Field invariants -/

/-- Every fact field is an atom that lowers in `env`. -/
def FieldsOK (Γ : KnownCtors) (env : List VarId) : Prop :=
  ∀ p ∈ Γ, ∀ f ∈ p.2.fields, f.isAtom = true ∧ (lowerTotalExpr env f).isSome

/-- Every fact field lowers to a term closed at `k`. -/
def FieldsClosed (Γ : KnownCtors) (env : List VarId) (k : Nat) : Prop :=
  ∀ p ∈ Γ, ∀ f ∈ p.2.fields, ∀ t, lowerTotalExpr env f = some t → closedAt k t = true

omit sv in
theorem fieldsOK_nil (env : List VarId) : FieldsOK [] env := fun _ h => by cases h

omit sv in
theorem fieldsClosed_nil (env : List VarId) (k : Nat) : FieldsClosed [] env k :=
  fun _ h => by cases h

omit sv in
theorem lowerTotalExpr_lit (env : List VarId) (c : Moist.Plutus.Term.Const)
    (ty : Moist.Plutus.Term.BuiltinType) :
    lowerTotalExpr env (.Lit (c, ty)) = some (.Constant (c, ty)) := by
  simp [lowerTotalExpr, expandFix, lowerTotal]

omit sv in
/-- A sub-environment whose fields avoid `x` keeps its invariants under `x`. -/
theorem fieldsOK_cons {Γ Γ' : KnownCtors} {env : List VarId} {x : VarId}
    (hsub : ∀ p ∈ Γ', p ∈ Γ ∧ (freeVarsList p.2.fields).contains x = false)
    (h : FieldsOK Γ env) : FieldsOK Γ' (x :: env) := by
  intro p hp f hf
  obtain ⟨hm, hx⟩ := hsub p hp
  obtain ⟨ha, hs⟩ := h p hm f hf
  refine ⟨ha, ?_⟩
  rw [lowerTotalExpr_prepend_unused env x f (freeVarsList_not_contains_mem hx f hf)]
  simpa using hs

omit sv in
theorem fieldsClosed_cons {Γ Γ' : KnownCtors} {env : List VarId} {x : VarId} {k : Nat}
    (hsub : ∀ p ∈ Γ', p ∈ Γ ∧ (freeVarsList p.2.fields).contains x = false)
    (h : FieldsClosed Γ env k) : FieldsClosed Γ' (x :: env) (k + 1) := by
  intro p hp f hf t ht
  obtain ⟨hm, hx⟩ := hsub p hp
  rw [lowerTotalExpr_prepend_unused env x f (freeVarsList_not_contains_mem hx f hf)] at ht
  cases hl : lowerTotalExpr env f with
  | none => rw [hl] at ht; cases ht
  | some t₀ =>
    rw [hl] at ht; cases ht
    exact Moist.Verified.closedAt_renameTerm_shiftRename t₀ k 1 (Nat.le_refl _) (by omega)
      (h p hm f hf t₀ hl)

omit sv in
theorem filterKnown_sub {x : VarId} {Γ : KnownCtors} :
    ∀ p ∈ filterKnown x Γ, p ∈ Γ ∧ (freeVarsList p.2.fields).contains x = false :=
  fun _ hp => let h := mem_filterKnown.mp hp; ⟨h.1, h.2.2⟩

omit sv in
theorem fresh_sub {Γ : KnownCtors} {s : VarId} (hs : s.uid > maxUidKnown Γ) :
    ∀ p ∈ Γ, p ∈ Γ ∧ (freeVarsList p.2.fields).contains s = false :=
  fun p hp => ⟨hp, (fresh_known hs p hp).2⟩

omit sv in
/-- The fields of a recorded fact lower, closed wherever the bound expression is. -/
theorem knownConstructor_fields {Γ : KnownCtors} {env : List VarId} {e : Expr} {te : Term}
    {info : KnownCtor} (hk : knownConstructor Γ e = some info)
    (he : lowerTotalExpr env e = some te) (hΓ : FieldsOK Γ env) :
    (∀ f ∈ info.fields, f.isAtom = true ∧ (lowerTotalExpr env f).isSome) ∧
    ∀ k, closedAt k te = true → FieldsClosed Γ env k →
      ∀ f ∈ info.fields, ∀ t, lowerTotalExpr env f = some t → closedAt k t = true := by
  rcases knownConstructor_cases hk with ⟨y, rfl, p, hp, _, rfl⟩ |
      ⟨tag, fields, rfl, rfl, hatoms⟩ | ⟨c, ty, rfl, values, _, hrel⟩
  · exact ⟨hΓ p hp, fun k _ hc => hc p hp⟩
  · rw [lowerTotalExpr_constr_of_list] at he
    cases hl : lowerTotalExprList env fields with
    | none => rw [hl] at he; cases he
    | some tfs =>
      rw [hl] at he; cases he
      refine ⟨fun f hf => ⟨hatoms f hf, ?_⟩, fun k hk _ f hf t ht => ?_⟩
      · obtain ⟨t, _, ht⟩ := lowerTotalExprList_mem hl f hf
        rw [ht]; rfl
      · obtain ⟨t', ht', hl'⟩ := lowerTotalExprList_mem hl f hf
        rw [hl'] at ht; cases ht
        simp only [closedAt] at hk
        exact BetaValueRefines.closedAt_of_mem hk ht'
  · refine ⟨fun f hf => ?_, fun k _ _ f hf t ht => ?_⟩
    · obtain ⟨_, _, c', ty', rfl, _⟩ := listRel2_mem_left hrel f hf
      exact ⟨rfl, by rw [lowerTotalExpr_lit]; rfl⟩
    · obtain ⟨_, _, c', ty', rfl, _⟩ := listRel2_mem_left hrel f hf
      rw [lowerTotalExpr_lit] at ht; cases ht; simp [closedAt]

omit sv in
theorem bindFact_fieldsOK {Γ : KnownCtors} {env : List VarId} {x : VarId} {r : Expr} {tr : Term}
    (hΓ : FieldsOK Γ env) (hr : lowerTotalExpr env r = some tr) :
    FieldsOK (bindFact Γ x r) (x :: env) := by
  intro p hp f hf
  rcases mem_bindFact hp with hp | ⟨_, hk, hx⟩
  · exact fieldsOK_cons filterKnown_sub hΓ p hp f hf
  · obtain ⟨ha, hs⟩ := (knownConstructor_fields hk hr hΓ).1 f hf
    refine ⟨ha, ?_⟩
    rw [lowerTotalExpr_prepend_unused env x f (freeVarsList_not_contains_mem hx f hf)]
    simpa using hs

omit sv in
theorem bindFact_fieldsClosed {Γ : KnownCtors} {env : List VarId} {x : VarId} {r : Expr}
    {tr : Term} {k : Nat} (hΓ : FieldsOK Γ env) (hc : FieldsClosed Γ env k)
    (hr : lowerTotalExpr env r = some tr) (hcr : closedAt k tr = true) :
    FieldsClosed (bindFact Γ x r) (x :: env) (k + 1) := by
  intro p hp f hf t ht
  rcases mem_bindFact hp with hp | ⟨_, hk, hx⟩
  · exact fieldsClosed_cons filterKnown_sub hc p hp f hf t ht
  · rw [lowerTotalExpr_prepend_unused env x f (freeVarsList_not_contains_mem hx f hf)] at ht
    cases hl : lowerTotalExpr env f with
    | none => rw [hl] at ht; cases ht
    | some t₀ =>
      rw [hl] at ht; cases ht
      exact Moist.Verified.closedAt_renameTerm_shiftRename t₀ k 1 (Nat.le_refl _) (by omega)
        ((knownConstructor_fields hk hr hΓ).2 k hcr hc f hf t₀ hl)

/-! ## Selecting an alternative -/

/-- The lowering of `selectAlternative`. -/
def selectTerm (tag constructorCount : Nat) (fields alternatives : List Term) : Term :=
  if constructorCount > 0 && alternatives.length > constructorCount then .Error
  else match alternatives[tag]? with
    | some a => fields.foldl Term.Apply a
    | none => .Error

omit sv in
theorem lower_selectAlternative {env : List VarId} {tag cc : Nat} {fields alts : List Expr}
    {tf ta : List Term} (hf : lowerTotalExprList env fields = some tf)
    (ha : lowerTotalExprList env alts = some ta) :
    lowerTotalExpr env (selectAlternative tag cc fields alts) = some (selectTerm tag cc tf ta) := by
  unfold selectAlternative selectTerm
  rw [lowerTotalExprList_length ha]
  split
  · exact lowerTotalExpr_error env
  · rcases lowerTotalExprList_getElem? ha tag with ⟨e, t, he, ht, hl⟩ | ⟨he, ht⟩
    · rw [he, ht]
      simp only []
      rw [lowerTotalExpr_foldl_app, hl, hf]; rfl
    · rw [he, ht]; exact lowerTotalExpr_error env

omit sv in
theorem closedAt_selectTerm {k tag cc : Nat} {tf ta : List Term}
    (hf : closedAtList k tf = true) (ha : closedAtList k ta = true) :
    closedAt k (selectTerm tag cc tf ta) = true := by
  unfold selectTerm
  split
  · simp [closedAt]
  · exact closedAt_select hf ha

omit sv in
theorem closedAtList_of_fields {env : List VarId} {k : Nat} :
    ∀ {fields : List Expr} {tf : List Term}, lowerTotalExprList env fields = some tf →
      (∀ f ∈ fields, ∀ t, lowerTotalExpr env f = some t → closedAt k t = true) →
      closedAtList k tf = true
  | [], tf, h, _ => by rw [lowerTotalExprList_nil] at h; cases h; simp [closedAtList]
  | f :: fs, tf, h, hcl => by
    rw [lowerTotalExprList_cons] at h
    cases hf : lowerTotalExpr env f <;> cases hfs : lowerTotalExprList env fs <;>
      simp [hf, hfs] at h
    subst h
    simp only [closedAtList, Bool.and_eq_true]
    exact ⟨hcl f (.head _) _ hf, closedAtList_of_fields hfs (fun g hg => hcl g (.tail _ hg))⟩

/-! ## Recursive functions under a fresh self variable -/

omit sv in
theorem closedAt_fixLamWrapUplc (k : Nat) (b : Term) :
    closedAt k (fixLamWrapUplc b) = closedAt (k + 3) b := by
  simp [fixLamWrapUplc, closedAt]

/-- A self variable fresh for both bodies and for the fact environment. -/
def fixSelf (b₁ b₂ : Expr) (Γ : KnownCtors) : VarId :=
  ⟨max (maxUidExpr (expandFix b₁)) (max (maxUidExpr (expandFix b₂)) (maxUidKnown Γ)) + 1, .gen, "s"⟩

omit sv in
theorem fixSelf_fresh₁ (b₁ b₂ : Expr) (Γ : KnownCtors) :
    (freeVars (expandFix b₁)).contains (fixSelf b₁ b₂ Γ) = false :=
  maxUidExpr_fresh _ _ (by simp only [fixSelf]; omega)

omit sv in
theorem fixSelf_fresh₂ (b₁ b₂ : Expr) (Γ : KnownCtors) :
    (freeVars (expandFix b₂)).contains (fixSelf b₁ b₂ Γ) = false :=
  maxUidExpr_fresh _ _ (by simp only [fixSelf]; omega)

omit sv in
theorem fixSelf_freshΓ (b₁ b₂ : Expr) (Γ : KnownCtors) :
    (fixSelf b₁ b₂ Γ).uid > maxUidKnown Γ := by
  simp only [fixSelf]; omega

omit sv in
theorem lowerTotalExpr_fix_lam (env : List VarId) (f x : VarId) (b₁ b₂ : Expr) (Γ : KnownCtors) :
    lowerTotalExpr env (.Fix f (.Lam x b₁)) =
      (lowerTotalExpr (x :: f :: fixSelf b₁ b₂ Γ :: env) b₁).map fixLamWrapUplc :=
  lowerTotalExpr_fix_lam_with_fresh env f x b₁ _ (fixSelf_fresh₁ b₁ b₂ Γ)

omit sv in
theorem lowerTotalExpr_fix_lam' (env : List VarId) (f x : VarId) (b₁ b₂ : Expr) (Γ : KnownCtors) :
    lowerTotalExpr env (.Fix f (.Lam x b₂)) =
      (lowerTotalExpr (x :: f :: fixSelf b₁ b₂ Γ :: env) b₂).map fixLamWrapUplc :=
  lowerTotalExpr_fix_lam_with_fresh env f x b₂ _ (fixSelf_fresh₂ b₁ b₂ Γ)

/-! ## Lowering of the result -/

mutual

theorem caseMerge_lower : ∀ (e : Expr) (Γ : KnownCtors) (env : List VarId) (t₁ : Term),
    lowerTotalExpr env e = some t₁ → FieldsOK Γ env →
    ∃ t₂, lowerTotalExpr env (caseMerge Γ e).1 = some t₂ ∧
      ∀ k, closedAt k t₁ = true → FieldsClosed Γ env k → closedAt k t₂ = true
  | .Var x, Γ, env, t₁, h, _ => ⟨t₁, by rw [caseMerge_var]; exact h, fun _ hk _ => hk⟩
  | .Lit l, Γ, env, t₁, h, _ => ⟨t₁, by rw [caseMerge_lit]; exact h, fun _ hk _ => hk⟩
  | .Builtin b, Γ, env, t₁, h, _ => ⟨t₁, by rw [caseMerge_builtin]; exact h, fun _ hk _ => hk⟩
  | .Error, Γ, env, t₁, h, _ => ⟨t₁, by rw [caseMerge_error]; exact h, fun _ hk _ => hk⟩
  | .Lam x b, Γ, env, t₁, h, hΓ => by
    rw [lowerTotalExpr_lam] at h
    cases hb : lowerTotalExpr (x :: env) b with
    | none => rw [hb] at h; cases h
    | some tb =>
      rw [hb] at h; cases h
      obtain ⟨tb', hl, hc⟩ := caseMerge_lower b (filterKnown x Γ) (x :: env) tb hb
        (fieldsOK_cons filterKnown_sub hΓ)
      refine ⟨.Lam 0 tb', by rw [caseMerge_lam, lowerTotalExpr_lam, hl]; rfl, fun k hk hfc => ?_⟩
      simp only [closedAt] at hk ⊢
      exact hc (k + 1) hk (fieldsClosed_cons filterKnown_sub hfc)
  | .Fix f body, Γ, env, t₁, h, hΓ => by
    cases body with
    | Lam x b =>
      rw [caseMerge_fix, caseMerge_lam]
      let Γ' := filterKnown x (filterKnown f Γ)
      let b' := (caseMerge Γ' b).1
      let s := fixSelf b b' Γ
      rw [lowerTotalExpr_fix_lam env f x b b' Γ] at h
      cases hb : lowerTotalExpr (x :: f :: s :: env) b with
      | none => rw [hb] at h; cases h
      | some tb =>
        rw [hb] at h; cases h
        have hsub₃ : ∀ p ∈ Γ', p ∈ Γ ∧ (freeVarsList p.2.fields).contains s = false ∧
            (freeVarsList p.2.fields).contains f = false ∧
            (freeVarsList p.2.fields).contains x = false := by
          intro p hp
          obtain ⟨hp₁, -, hx⟩ := mem_filterKnown.mp hp
          obtain ⟨hp₂, -, hf⟩ := mem_filterKnown.mp hp₁
          exact ⟨hp₂, (fresh_known (fixSelf_freshΓ b b' Γ) p hp₂).2, hf, hx⟩
        have hok : FieldsOK Γ' (x :: f :: s :: env) :=
          fieldsOK_cons (Γ := filterKnown f Γ) filterKnown_sub
            (fieldsOK_cons (Γ := Γ) filterKnown_sub
              (fieldsOK_cons (fresh_sub (fixSelf_freshΓ b b' Γ)) hΓ))
        obtain ⟨tb', hl, hc⟩ := caseMerge_lower b Γ' (x :: f :: s :: env) tb hb hok
        refine ⟨fixLamWrapUplc tb', ?_, fun k hk hfc => ?_⟩
        · rw [lowerTotalExpr_fix_lam' env f x b b' Γ, hl]; rfl
        · rw [closedAt_fixLamWrapUplc] at hk ⊢
          exact hc (k + 3) hk
            (fieldsClosed_cons (Γ := filterKnown f Γ) filterKnown_sub
              (fieldsClosed_cons (Γ := Γ) filterKnown_sub
                (fieldsClosed_cons (fresh_sub (fixSelf_freshΓ b b' Γ)) hfc)))
    | _ => simp [lowerTotalExpr, expandFix, lowerTotal] at h
  | .App fn a, Γ, env, t₁, h, hΓ => by
    rw [lowerTotalExpr_app] at h
    cases hf : lowerTotalExpr env fn <;> cases ha : lowerTotalExpr env a <;> simp [hf, ha] at h
    rename_i tf ta
    subst h
    obtain ⟨tf', hlf, hcf⟩ := caseMerge_lower fn Γ env tf hf hΓ
    obtain ⟨ta', hla, hca⟩ := caseMerge_lower a Γ env ta ha hΓ
    refine ⟨.Apply tf' ta', by rw [caseMerge_app, lowerTotalExpr_app, hlf, hla]; rfl,
      fun k hk hfc => ?_⟩
    simp only [closedAt, Bool.and_eq_true] at hk ⊢
    exact ⟨hcf k hk.1 hfc, hca k hk.2 hfc⟩
  | .Force e, Γ, env, t₁, h, hΓ => by
    rw [lowerTotalExpr_force] at h
    cases he : lowerTotalExpr env e with
    | none => rw [he] at h; cases h
    | some te =>
      rw [he] at h; cases h
      obtain ⟨te', hl, hc⟩ := caseMerge_lower e Γ env te he hΓ
      exact ⟨.Force te', by rw [caseMerge_force, lowerTotalExpr_force, hl]; rfl,
        fun k hk hfc => by simp only [closedAt] at hk ⊢; exact hc k hk hfc⟩
  | .Delay e, Γ, env, t₁, h, hΓ => by
    rw [lowerTotalExpr_delay] at h
    cases he : lowerTotalExpr env e with
    | none => rw [he] at h; cases h
    | some te =>
      rw [he] at h; cases h
      obtain ⟨te', hl, hc⟩ := caseMerge_lower e Γ env te he hΓ
      exact ⟨.Delay te', by rw [caseMerge_delay, lowerTotalExpr_delay, hl]; rfl,
        fun k hk hfc => by simp only [closedAt] at hk ⊢; exact hc k hk hfc⟩
  | .Constr tag fs, Γ, env, t₁, h, hΓ => by
    rw [lowerTotalExpr_constr_of_list] at h
    cases hl : lowerTotalExprList env fs with
    | none => rw [hl] at h; cases h
    | some tfs =>
      rw [hl] at h; cases h
      obtain ⟨tfs', hl', hc⟩ := caseMergeList_lower fs Γ env tfs hl hΓ
      exact ⟨.Constr tag tfs', by rw [caseMerge_constr, lowerTotalExpr_constr_of_list, hl']; rfl,
        fun k hk hfc => by simp only [closedAt] at hk ⊢; exact hc k hk hfc⟩
  | .Case s alts, Γ, env, t₁, h, hΓ => by
    rw [lowerTotalExpr_case_of_list] at h
    cases hs : lowerTotalExpr env s <;> cases ha : lowerTotalExprList env alts <;>
      simp [hs, ha] at h
    rename_i ts talts
    subst h
    obtain ⟨ts', hls, hcs⟩ := caseMerge_lower s Γ env ts hs hΓ
    obtain ⟨talts', hla, hca⟩ := caseMergeList_lower alts Γ env talts ha hΓ
    rw [caseMerge_case]
    have hcl : ∀ k, closedAt k (.Case ts talts) = true → FieldsClosed Γ env k →
        closedAt k ts' = true ∧ closedAtList k talts' = true := by
      intro k hk hfc
      simp only [closedAt, Bool.and_eq_true] at hk
      exact ⟨hcs k hk.1 hfc, hca k hk.2 hfc⟩
    rcases caseResult_cases Γ (caseMerge Γ s).1 (caseMergeList Γ alts).1 with
      ⟨tag, fields, hc, hr⟩ | ⟨info, _, hk, _, hr⟩ | hr
    · rw [hr]
      have hlow : lowerTotalExpr env (.Case (.Constr tag fields) (caseMergeList Γ alts).1) =
          some (.Case ts' talts') := by
        rw [lowerTotalExpr_case_of_list, ← hc, hls, hla]; rfl
      obtain ⟨t₂, hl₂, hc₂, _⟩ := reduce_correct tag fields _ env _ hlow
      refine ⟨t₂, hl₂, fun k hk hfc => hc₂ k ?_⟩
      have := hcl k hk hfc
      simp only [closedAt, Bool.and_eq_true]; exact this
    · rw [hr]
      obtain ⟨hok, hfcl⟩ := knownConstructor_fields hk hls hΓ
      obtain ⟨tf, htf⟩ := lowerTotalExprList_of_forall (fun f hf => (hok f hf).2)
      exact ⟨_, lower_selectAlternative htf hla, fun k hk hfc => by
        obtain ⟨hcs', hca'⟩ := hcl k hk hfc
        exact closedAt_selectTerm (closedAtList_of_fields htf (hfcl k hcs' hfc)) hca'⟩
    · rw [hr]
      refine ⟨.Case ts' talts', by rw [lowerTotalExpr_case_of_list, hls, hla]; rfl,
        fun k hk hfc => ?_⟩
      have := hcl k hk hfc
      simp only [closedAt, Bool.and_eq_true]; exact this
  | .Let [] body, Γ, env, t₁, h, hΓ => by
    rw [lowerTotalExpr_let_nil_eq] at h
    obtain ⟨t₂, hl, hc⟩ := caseMerge_lower body Γ env t₁ h hΓ
    exact ⟨t₂, by rw [caseMerge_let_nil, lowerTotalExpr_let_nil_eq, hl], hc⟩
  | .Let ((x, r, er) :: rest) body, Γ, env, t₁, h, hΓ => by
    rw [lowerTotalExpr_let_cons] at h
    cases hr : lowerTotalExpr env r <;> cases hb : lowerTotalExpr (x :: env) (.Let rest body) <;>
      simp [hr, hb] at h
    rename_i tr tb
    subst h
    obtain ⟨tr', hlr, hcr⟩ := caseMerge_lower r Γ env tr hr hΓ
    let Γ' := bindFact Γ x (caseMerge Γ r).1
    obtain ⟨tb', hlb, hcb⟩ := caseMerge_lower (.Let rest body) Γ' (x :: env) tb hb
      (bindFact_fieldsOK hΓ hlr)
    rw [caseMerge_let] at hlb
    refine ⟨.Apply (.Lam 0 tb') tr', ?_, fun k hk hfc => ?_⟩
    · rw [caseMerge_let_cons, lowerTotalExpr_let_cons, hlr]
      simp only [Option.bind_some]
      rw [hlb]; rfl
    · simp only [closedAt, Bool.and_eq_true] at hk ⊢
      have hcr' := hcr k hk.2 hfc
      exact ⟨hcb (k + 1) hk.1 (bindFact_fieldsClosed hΓ hfc hlr hcr'), hcr'⟩
termination_by e => sizeOf e

theorem caseMergeList_lower : ∀ (es : List Expr) (Γ : KnownCtors) (env : List VarId)
    (ts₁ : List Term), lowerTotalExprList env es = some ts₁ → FieldsOK Γ env →
    ∃ ts₂, lowerTotalExprList env (caseMergeList Γ es).1 = some ts₂ ∧
      ∀ k, closedAtList k ts₁ = true → FieldsClosed Γ env k → closedAtList k ts₂ = true
  | [], Γ, env, ts₁, h, _ => by
    rw [lowerTotalExprList_nil] at h; cases h
    exact ⟨[], by simp [caseMergeList, lowerTotalExprList_nil], fun _ _ _ => by simp [closedAtList]⟩
  | e :: es, Γ, env, ts₁, h, hΓ => by
    rw [lowerTotalExprList_cons] at h
    cases he : lowerTotalExpr env e <;> cases hes : lowerTotalExprList env es <;>
      simp [he, hes] at h
    rename_i te tes
    subst h
    obtain ⟨te', hl, hc⟩ := caseMerge_lower e Γ env te he hΓ
    obtain ⟨tes', hls, hcs⟩ := caseMergeList_lower es Γ env tes hes hΓ
    refine ⟨te' :: tes', ?_, fun k hk hfc => ?_⟩
    · have : (caseMergeList Γ (e :: es)).1 = (caseMerge Γ e).1 :: (caseMergeList Γ es).1 := by
        simp [caseMergeList]
      rw [this, lowerTotalExprList_cons, hl, hls]; rfl
    · simp only [closedAtList, Bool.and_eq_true] at hk ⊢
      exact ⟨hc k hk.1 hfc, hcs k hk.2 hfc⟩
termination_by es => sizeOf es

end

end Moist.Verified.CaseMerge
