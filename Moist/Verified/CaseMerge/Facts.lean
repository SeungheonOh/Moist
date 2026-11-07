import Moist.Verified.CaseMerge.Lower

/-! # Constructor facts at run time

`FactsHold Γ env ρ`: every variable recorded in `Γ` is bound in `ρ` to a
value that a `case` treats as constructor `tag` with the current values of
the recorded atomic fields (`FactValue`). `simple_eval` is the exact
evaluation lemma: when the pass turns `r` into an atom or a constructor of
atoms, `r` itself returns that expression's value.
-/

namespace Moist.Verified.CaseMerge

open Moist.CEK
open Moist.MIR
open Moist.Plutus.Term (Term)
open Moist.Verified (closedAt closedAtList renameTerm renameTermList shiftRename)
open Moist.Verified.Equivalence (steps Reaches steps_trans ListRel)
open Moist.Verified.MIR (lowerTotalExprList lowerTotalExprList_nil lowerTotalExprList_cons
  lowerTotalExpr_case_of_list lowerTotalExpr_constr_of_list lowerTotalExpr_prepend_unused
  isLeafAtomTerm lowerTotal_atom_isLeafAtom)

/-! ## Definitions -/

/-- An atom whose lowering returns `v` in one step. -/
def AtomEval (env : List VarId) (ρ : CekEnv) (f : Expr) (v : CekValue) : Prop :=
  f.isAtom = true ∧ ∃ t, lowerTotalExpr env f = some t ∧ ∀ π, step (.compute π ρ t) = .ret π v

/-- How a `case` sees a value: constructor `tag` of a type with `cc` constructors
    (`0` when unknown) carrying the fields `vs`. -/
def ShapeOf (v : CekValue) (tag cc : Nat) (vs : List CekValue) : Prop :=
  (v = .VConstr tag vs ∧ cc = 0) ∨
    ∃ c, v = .VCon c ∧ constToTagAndFields c = some (tag, cc, vs)

def FactValue (env : List VarId) (ρ : CekEnv) (info : KnownCtor) (v : CekValue) : Prop :=
  ∃ vs, ShapeOf v info.tag info.constructorCount vs ∧ ListRel2 (AtomEval env ρ) info.fields vs

/-- Every fact of `Γ` is true of the run-time environment `ρ`. -/
def FactsHold (Γ : KnownCtors) (env : List VarId) (ρ : CekEnv) : Prop :=
  ∀ p ∈ Γ, ∃ i v, envLookupT env p.1 = some i ∧ ρ.lookup (i + 1) = some v ∧
    FactValue env ρ p.2 v

/-- Atoms and constructors of atoms. -/
def Simple (F : Expr) : Prop :=
  F.isAtom = true ∨ ∃ tag fs, F = .Constr tag fs ∧ ∀ f ∈ fs, f.isAtom = true

/-- The value of a simple expression. -/
def SimpleVal (env : List VarId) (ρ : CekEnv) (F : Expr) (v : CekValue) : Prop :=
  AtomEval env ρ F v ∨
    ∃ tag fs vs, F = .Constr tag fs ∧ v = .VConstr tag vs ∧ ListRel2 (AtomEval env ρ) fs vs

theorem factsHold_nil (env : List VarId) (ρ : CekEnv) : FactsHold [] env ρ :=
  fun _ h => by cases h

/-! ## The case step -/

theorem caseStep {v : CekValue} {tag cc : Nat} {vs : List CekValue} (h : ShapeOf v tag cc vs)
    (alts : List Term) (ρ : CekEnv) (π : Stack) :
    step (.ret (.caseScrutinee alts ρ :: π) v) =
      if cc > 0 && alts.length > cc then .error
      else match alts[tag]? with
        | some alt => .compute (vs.map Frame.applyArg ++ π) ρ alt
        | none => .error := by
  rcases h with ⟨rfl, rfl⟩ | ⟨c, rfl, hc⟩
  · simp only [step, Nat.lt_irrefl, decide_false, Bool.false_and, Bool.false_eq_true, if_false]
    cases alts[tag]? <;> rfl
  · simp only [step, hc]
    rfl

/-! ## Shifting under a binder -/

theorem leafAtom_step_shift {t : Term} (ht : isLeafAtomTerm t) {ρ : CekEnv} {v : CekValue}
    (h : ∀ π, step (.compute π ρ t) = .ret π v) (w : CekValue) :
    ∀ π, step (.compute π (ρ.extend w) (renameTerm (shiftRename 1) t)) = .ret π v := by
  intro π
  rcases ht with ⟨n, hn, rfl⟩ | ⟨ct, rfl⟩ | ⟨b, rfl⟩
  · have hπ := h π
    simp only [renameTerm, Moist.Verified.shiftRename_ge hn, step] at hπ ⊢
    rw [BetaValueRefines.extend_lookup_succ ρ w n hn]
    exact hπ
  · exact h π
  · exact h π

theorem atomEval_shift {env : List VarId} {ρ : CekEnv} {f : Expr} {v : CekValue} {x : VarId}
    (h : AtomEval env ρ f v) (hx : (freeVars f).contains x = false) (w : CekValue) :
    AtomEval (x :: env) (ρ.extend w) f v := by
  obtain ⟨ha, t, ht, hs⟩ := h
  refine ⟨ha, renameTerm (shiftRename 1) t, ?_, ?_⟩
  · rw [lowerTotalExpr_prepend_unused env x f hx, ht]; rfl
  · exact leafAtom_step_shift (lowerTotal_atom_isLeafAtom env f t ha ht) hs w

theorem listRel2_atomEval_shift {env : List VarId} {ρ : CekEnv} {x : VarId} {w : CekValue} :
    ∀ {fs : List Expr} {vs : List CekValue}, ListRel2 (AtomEval env ρ) fs vs →
      (freeVarsList fs).contains x = false → ListRel2 (AtomEval (x :: env) (ρ.extend w)) fs vs
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, h, hx =>
    ⟨atomEval_shift h.1 (freeVarsList_union_left _ _ _ hx) w,
      listRel2_atomEval_shift h.2 (freeVarsList_union_right _ _ _ hx)⟩
  | [], _ :: _, h, _ => absurd h id
  | _ :: _, [], h, _ => absurd h id

theorem factValue_shift {env : List VarId} {ρ : CekEnv} {info : KnownCtor} {v : CekValue}
    {x : VarId} (h : FactValue env ρ info v) (hx : (freeVarsList info.fields).contains x = false)
    (w : CekValue) : FactValue (x :: env) (ρ.extend w) info v :=
  let ⟨vs, hs, hl⟩ := h; ⟨vs, hs, listRel2_atomEval_shift hl hx⟩

theorem beq_symm_false {a b : VarId} (h : (a == b) = false) : (b == a) = false := by
  rw [VarId.beq_false_iff] at h ⊢
  rcases h with h | h
  · exact .inl (Ne.symm h)
  · exact .inr (Ne.symm h)

/-- Facts that avoid `x` survive binding `x`. -/
theorem factsHold_cons {Γ Γ' : KnownCtors} {env : List VarId} {ρ : CekEnv} {x : VarId}
    (hsub : ∀ p ∈ Γ', p ∈ Γ ∧ (p.1 == x) = false ∧ (freeVarsList p.2.fields).contains x = false)
    (h : FactsHold Γ env ρ) (w : CekValue) : FactsHold Γ' (x :: env) (ρ.extend w) := by
  intro p hp
  obtain ⟨hm, hk, hx⟩ := hsub p hp
  obtain ⟨i, v, hi, hv, hf⟩ := h p hm
  refine ⟨i + 1, v, ?_, ?_, factValue_shift hf hx w⟩
  · rw [envLookupT_cons_neq x p.1 env (beq_symm_false hk), hi]; rfl
  · rw [BetaValueRefines.extend_lookup_succ ρ w (i + 1) (by omega)]; exact hv

theorem filterKnown_sub' {x : VarId} {Γ : KnownCtors} :
    ∀ p ∈ filterKnown x Γ, p ∈ Γ ∧ (p.1 == x) = false ∧
      (freeVarsList p.2.fields).contains x = false :=
  fun _ hp => mem_filterKnown.mp hp

theorem fresh_sub' {Γ : KnownCtors} {s : VarId} (hs : s.uid > maxUidKnown Γ) :
    ∀ p ∈ Γ, p ∈ Γ ∧ (p.1 == s) = false ∧ (freeVarsList p.2.fields).contains s = false :=
  fun p hp => ⟨hp, fresh_known hs p hp⟩

/-! ## Simple expressions -/

theorem simple_of_known {Γ : KnownCtors} {F : Expr} {info : KnownCtor}
    (h : knownConstructor Γ F = some info) : Simple F := by
  rcases knownConstructor_cases h with ⟨y, rfl, -⟩ | ⟨tag, fs, rfl, -, hat⟩ | ⟨c, ty, rfl, -⟩
  · exact .inl rfl
  · exact .inr ⟨tag, fs, rfl, hat⟩
  · exact .inl rfl

theorem atomEval_var {env : List VarId} {ρ : CekEnv} {y : VarId} {v : CekValue}
    (h : AtomEval env ρ (.Var y) v) :
    ∃ i, envLookupT env y = some i ∧ ρ.lookup (i + 1) = some v := by
  obtain ⟨_, t, ht, hs⟩ := h
  simp only [lowerTotalExpr, expandFix, lowerTotal] at ht
  cases hi : envLookupT env y with
  | none => rw [hi] at ht; cases ht
  | some i =>
    rw [hi] at ht; cases ht
    refine ⟨i, rfl, ?_⟩
    have := hs []
    simp only [step] at this
    cases hl : ρ.lookup (i + 1) with
    | none => rw [hl] at this; cases this
    | some u => rw [hl] at this; cases this; rfl

theorem atomEval_lit {env : List VarId} {ρ : CekEnv} {c : Moist.Plutus.Term.Const}
    {ty : Moist.Plutus.Term.BuiltinType} {v : CekValue}
    (h : AtomEval env ρ (.Lit (c, ty)) v) : v = .VCon c := by
  obtain ⟨_, t, ht, hs⟩ := h
  rw [lowerTotalExpr_lit] at ht; cases ht
  have := hs []
  simp only [step] at this
  cases this; rfl

theorem atomEval_of_lit (env : List VarId) (ρ : CekEnv) (c : Moist.Plutus.Term.Const)
    (ty : Moist.Plutus.Term.BuiltinType) : AtomEval env ρ (.Lit (c, ty)) (.VCon c) :=
  ⟨rfl, _, lowerTotalExpr_lit env c ty, fun _ => rfl⟩

theorem listRel2_litField_atomEval {env : List VarId} {ρ : CekEnv} :
    ∀ {fs : List Expr} {vs : List CekValue}, ListRel2 LitField fs vs → ListRel2 (AtomEval env ρ) fs vs
  | [], [], _ => trivial
  | f :: fs, v :: vs, h => by
    obtain ⟨⟨c, ty, rfl, rfl⟩, hr⟩ := h
    exact ⟨atomEval_of_lit env ρ c ty, listRel2_litField_atomEval hr⟩
  | [], _ :: _, h => absurd h id
  | _ :: _, [], h => absurd h id

/-- The value of a simple expression with a recorded fact satisfies that fact. -/
theorem factValue_of_simple {Γ : KnownCtors} {env : List VarId} {ρ : CekEnv} {F : Expr}
    {info : KnownCtor} {v : CekValue} (hk : knownConstructor Γ F = some info)
    (hv : SimpleVal env ρ F v) (hΓ : FactsHold Γ env ρ) : FactValue env ρ info v := by
  rcases knownConstructor_cases hk with ⟨y, rfl, p, hp, hpy, rfl⟩ |
      ⟨tag, fs, rfl, rfl, hat⟩ | ⟨c, ty, rfl, values, hc, hrel⟩
  · rcases hv with hv | ⟨_, _, _, h, _⟩
    · obtain ⟨i, hi, hl⟩ := atomEval_var hv
      obtain ⟨i', v', hi', hl', hf⟩ := hΓ p hp
      rw [envLookupT_congr hpy, hi] at hi'
      cases hi'
      rw [hl] at hl'; cases hl'
      exact hf
    · cases h
  · rcases hv with ⟨h, _⟩ | ⟨tag', fs', vs, h, rfl, hl⟩
    · simp [Expr.isAtom] at h
    · cases h
      exact ⟨vs, .inl ⟨rfl, rfl⟩, hl⟩
  · rcases hv with hv | ⟨_, _, _, h, _⟩
    · rw [atomEval_lit hv]
      exact ⟨values, .inr ⟨c, rfl, hc⟩, listRel2_litField_atomEval hrel⟩
    · cases h

/-! ## Evaluating constructors -/

theorem steps_constrField_returns {tag : Nat} {ρ : CekEnv} :
    ∀ (ts : List Term) (vs : List CekValue),
      ListRel2 (fun t v => ∀ π, ∃ n, steps n (.compute π ρ t) = .ret π v) ts vs →
      ∀ (done : List CekValue) (v : CekValue) (π : Stack),
        ∃ n, steps n (.ret (.constrField tag done ts ρ :: π) v) =
          .ret π (.VConstr tag ((v :: done).reverse ++ vs))
  | [], [], _, done, v, π => ⟨1, by simp [steps, step]⟩
  | t :: ts, u :: vs, h, done, v, π => by
    obtain ⟨n₁, h₁⟩ := h.1 (.constrField tag (v :: done) ts ρ :: π)
    obtain ⟨n₂, h₂⟩ := steps_constrField_returns ts vs h.2 (v :: done) u π
    refine ⟨1 + n₁ + n₂, ?_⟩
    rw [steps_trans, steps_trans]
    show steps n₂ (steps n₁ (.compute (.constrField tag (v :: done) ts ρ :: π) ρ t)) = _
    rw [h₁, h₂]
    simp
  | [], _ :: _, h, _, _, _ => absurd h id
  | _ :: _, [], h, _, _, _ => absurd h id

theorem steps_constr_returns {tag : Nat} {ρ : CekEnv} :
    ∀ (ts : List Term) (vs : List CekValue),
      ListRel2 (fun t v => ∀ π, ∃ n, steps n (.compute π ρ t) = .ret π v) ts vs →
      ∀ π, ∃ n, steps n (.compute π ρ (.Constr tag ts)) = .ret π (.VConstr tag vs)
  | [], [], _, π => ⟨1, rfl⟩
  | t :: ts, u :: vs, h, π => by
    obtain ⟨n₁, h₁⟩ := h.1 (.constrField tag [] ts ρ :: π)
    obtain ⟨n₂, h₂⟩ := steps_constrField_returns ts vs h.2 [] u π
    refine ⟨1 + n₁ + n₂, ?_⟩
    rw [steps_trans, steps_trans]
    show steps n₂ (steps n₁ (.compute (.constrField tag [] ts ρ :: π) ρ t)) = _
    rw [h₁, h₂]
    simp
  | [], _ :: _, h, _ => absurd h id
  | _ :: _, [], h, _ => absurd h id

/-! ## Shapes of simple results -/

theorem foldl_app_simple {a : Expr} :
    ∀ {args : List Expr}, Simple (args.foldl Expr.App a) → args = [] ∧ Simple a
  | [], h => ⟨rfl, h⟩
  | x :: xs, h => by
    have := (foldl_app_simple (args := xs) (a := .App a x) h).2
    rcases this with h | ⟨_, _, h, _⟩
    · simp [Expr.isAtom] at h
    · cases h

theorem selectAlternative_simple {tag cc : Nat} {fields alts : List Expr}
    (h : Simple (selectAlternative tag cc fields alts)) :
    (cc > 0 && alts.length > cc) = false ∧ fields = [] ∧
      ∃ a, alts[tag]? = some a ∧ selectAlternative tag cc fields alts = a ∧ Simple a := by
  have herr : ¬ Simple Expr.Error := by
    rintro (h | ⟨_, _, h, _⟩)
    · simp [Expr.isAtom] at h
    · cases h
  unfold selectAlternative at h ⊢
  split at h
  · exact absurd h herr
  · rename_i hc
    refine ⟨by simpa using hc, ?_⟩
    simp only [hc, Bool.false_eq_true, if_false]
    cases ha : alts[tag]? with
    | none => rw [ha] at h; exact absurd h herr
    | some a =>
      rw [ha] at h
      obtain ⟨rfl, hs⟩ := foldl_app_simple h
      exact ⟨rfl, a, rfl, rfl, hs⟩

theorem caseFieldBindings_nil {next : Nat} :
    ∀ {fields : List Expr} {args : List Expr},
      caseFieldBindings next fields = ([], args) → args = fields
  | [], args, h => by simp [caseFieldBindings] at h; exact h
  | f :: fs, args, h => by
    cases hf : f.isAtom with
    | true =>
      rw [caseFieldBindings_atom fs hf] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h₁, h₂⟩ := h
      have : (caseFieldBindings next fs) = ([], (caseFieldBindings next fs).2) := by
        rw [← h₁]
      rw [← h₂, caseFieldBindings_nil this]
    | false =>
      rw [caseFieldBindings_nonatom fs hf] at h
      simp at h

theorem reduce_simple {tag : Nat} {fields alts : List Expr}
    (h : Simple (reduceConstructorCase tag fields alts)) :
    fields = [] ∧ ∃ a, alts[tag]? = some a ∧ reduceConstructorCase tag fields alts = a ∧ Simple a := by
  unfold reduceConstructorCase at h ⊢
  generalize hcb : caseFieldBindings (maxUidExpr (.Case (.Constr tag fields) alts) + 1) fields = r at h ⊢
  obtain ⟨bs, args⟩ := r
  cases bs with
  | cons b bs =>
    rcases h with h | ⟨_, _, h, _⟩
    · simp [Expr.isAtom] at h
    · simp at h
  | nil =>
    have hargs := caseFieldBindings_nil hcb
    subst hargs
    simp only [List.isEmpty_nil, if_true] at h ⊢
    obtain ⟨_, hnil, a, ha, he, hs⟩ := selectAlternative_simple h
    exact ⟨hnil, a, ha, he, hs⟩

/-! ## Exact evaluation of simplified expressions -/

mutual

/-- When the pass turns `r` into a simple expression, `r` returns its value. -/
theorem simple_eval : ∀ (r : Expr) (Γ : KnownCtors) (env : List VarId) (ρ : CekEnv) (t : Term),
    lowerTotalExpr env r = some t → FactsHold Γ env ρ →
    (∀ n, 0 < n → n ≤ env.length → ∃ v, ρ.lookup n = some v) →
    Simple (caseMerge Γ r).1 →
    ∃ v, (∀ π, ∃ n, steps n (.compute π ρ t) = .ret π v) ∧ SimpleVal env ρ (caseMerge Γ r).1 v
  | .Var y, Γ, env, ρ, t, h, _, hlook, _ => by
    rw [caseMerge_var]
    simp only [lowerTotalExpr, expandFix, lowerTotal] at h
    cases hi : envLookupT env y with
    | none => rw [hi] at h; cases h
    | some i =>
      rw [hi] at h; cases h
      obtain ⟨v, hv⟩ := hlook (i + 1) (by omega) (by have := envLookupT_bound env y i hi; omega)
      have hs : ∀ π, step (.compute π ρ (.Var (i + 1))) = .ret π v := by
        intro π; simp only [step, hv]
      refine ⟨v, fun π => ⟨1, hs π⟩, .inl ⟨rfl, _, ?_, hs⟩⟩
      simp [lowerTotalExpr, expandFix, lowerTotal, hi]
  | .Lit (c, ty), Γ, env, ρ, t, h, _, _, _ => by
    rw [caseMerge_lit]
    rw [lowerTotalExpr_lit] at h; cases h
    exact ⟨.VCon c, fun π => ⟨1, rfl⟩, .inl (atomEval_of_lit env ρ c ty)⟩
  | .Builtin b, Γ, env, ρ, t, h, _, _, _ => by
    rw [caseMerge_builtin]
    simp only [lowerTotalExpr, expandFix, lowerTotal] at h; cases h
    exact ⟨_, fun π => ⟨1, rfl⟩, .inl ⟨rfl, .Builtin b,
      by simp [lowerTotalExpr, expandFix, lowerTotal], fun _ => rfl⟩⟩
  | .Error, Γ, _, _, _, _, _, _, hs => by
    rw [caseMerge_error] at hs
    rcases hs with h | ⟨_, _, h, _⟩
    · simp [Expr.isAtom] at h
    · cases h
  | .Lam x b, Γ, _, _, _, _, _, _, hs => by
    rw [caseMerge_lam] at hs
    rcases hs with h | ⟨_, _, h, _⟩
    · simp [Expr.isAtom] at h
    · cases h
  | .Fix x b, Γ, _, _, _, _, _, _, hs => by
    rw [caseMerge_fix] at hs
    rcases hs with h | ⟨_, _, h, _⟩
    · simp [Expr.isAtom] at h
    · cases h
  | .App f a, Γ, _, _, _, _, _, _, hs => by
    rw [caseMerge_app] at hs
    rcases hs with h | ⟨_, _, h, _⟩
    · simp [Expr.isAtom] at h
    · cases h
  | .Force e, Γ, _, _, _, _, _, _, hs => by
    rw [caseMerge_force] at hs
    rcases hs with h | ⟨_, _, h, _⟩
    · simp [Expr.isAtom] at h
    · cases h
  | .Delay e, Γ, _, _, _, _, _, _, hs => by
    rw [caseMerge_delay] at hs
    rcases hs with h | ⟨_, _, h, _⟩
    · simp [Expr.isAtom] at h
    · cases h
  | .Let bs body, Γ, _, _, _, _, _, _, hs => by
    rw [caseMerge_let] at hs
    rcases hs with h | ⟨_, _, h, _⟩
    · simp [Expr.isAtom] at h
    · cases h
  | .Constr tag fs, Γ, env, ρ, t, h, hΓ, hlook, hs => by
    rw [caseMerge_constr] at hs ⊢
    rcases hs with h' | ⟨tag', fs', h', hat⟩
    · simp [Expr.isAtom] at h'
    · cases h'
      rw [lowerTotalExpr_constr_of_list] at h
      cases hl : lowerTotalExprList env fs with
      | none => rw [hl] at h; cases h
      | some ts =>
        rw [hl] at h; cases h
        obtain ⟨vs, hret, hev⟩ := simple_eval_list fs Γ env ρ ts hl hΓ hlook hat
        exact ⟨.VConstr tag vs, steps_constr_returns ts vs hret,
          .inr ⟨tag, _, vs, rfl, rfl, hev⟩⟩
  | .Case s alts, Γ, env, ρ, t, h, hΓ, hlook, hs => by
    rw [caseMerge_case] at hs ⊢
    rw [lowerTotalExpr_case_of_list] at h
    cases hsl : lowerTotalExpr env s <;> cases hal : lowerTotalExprList env alts <;>
      simp [hsl, hal] at h
    rename_i ts talts
    subst h
    -- The selected alternative of the source.
    have select : ∀ (tag : Nat) (a : Expr), (caseMergeList Γ alts).1[tag]? = some a →
        ∃ alt ta, alts[tag]? = some alt ∧ talts[tag]? = some ta ∧
          lowerTotalExpr env alt = some ta ∧ (caseMerge Γ alt).1 = a := by
      intro tag a ha
      rw [caseMergeList_getElem?] at ha
      cases hx : alts[tag]? with
      | none => rw [hx] at ha; cases ha
      | some alt =>
        rw [hx] at ha; cases ha
        rcases lowerTotalExprList_getElem? hal tag with ⟨e, t', he, ht, hl⟩ | ⟨he, _⟩
        · rw [hx] at he; cases he
          exact ⟨alt, t', rfl, ht, hl, rfl⟩
        · rw [hx] at he; cases he
    rcases caseResult_cases Γ (caseMerge Γ s).1 (caseMergeList Γ alts).1 with
      ⟨tag, fields, hc, hr⟩ | ⟨info, hnc, hk, hl, hr⟩ | hr
    · rw [hr] at hs ⊢
      obtain ⟨rfl, a, ha, he, hsa⟩ := reduce_simple hs
      rw [he]
      obtain ⟨alt, ta, halt, hta, hlalt, rfl⟩ := select tag a ha
      have : sizeOf alt < 1 + sizeOf s + sizeOf alts := by
        have := List.sizeOf_lt_of_mem (List.mem_of_getElem? halt); omega
      have hsimple : Simple (caseMerge Γ s).1 := by rw [hc]; exact .inr ⟨tag, [], rfl, by simp⟩
      obtain ⟨vs, hrs, hvs⟩ := simple_eval s Γ env ρ ts hsl hΓ hlook hsimple
      have hvs' : vs = .VConstr tag [] := by
        rw [hc] at hvs
        rcases hvs with ⟨h, _⟩ | ⟨tag', fs', vs', h, rfl, hl'⟩
        · simp [Expr.isAtom] at h
        · cases h; cases vs' with
          | nil => rfl
          | cons _ _ => exact absurd hl' id
      subst hvs'
      obtain ⟨v, hra, hva⟩ := simple_eval alt Γ env ρ ta hlalt hΓ hlook hsa
      refine ⟨v, fun π => ?_, hva⟩
      obtain ⟨n₁, h₁⟩ := hrs (.caseScrutinee talts ρ :: π)
      obtain ⟨n₂, h₂⟩ := hra π
      refine ⟨1 + n₁ + 1 + n₂, ?_⟩
      rw [steps_trans, steps_trans, steps_trans]
      show steps n₂ (steps 1 (steps n₁ (.compute (.caseScrutinee talts ρ :: π) ρ ts))) = _
      rw [h₁]
      rw [show ∀ x, steps 1 x = step x from fun _ => rfl]
      simp only [step, hta, List.map_nil, List.nil_append]
      exact h₂
    · rw [hr] at hs ⊢
      obtain ⟨hcc, hnil, a, ha, he, hsa⟩ := selectAlternative_simple hs
      rw [he]
      obtain ⟨alt, ta, halt, hta, hlalt, rfl⟩ := select info.tag a ha
      have : sizeOf alt < 1 + sizeOf s + sizeOf alts := by
        have := List.sizeOf_lt_of_mem (List.mem_of_getElem? halt); omega
      obtain ⟨vs, hrs, hvs⟩ := simple_eval s Γ env ρ ts hsl hΓ hlook (simple_of_known hk)
      obtain ⟨fvs, hshape, hfl⟩ := factValue_of_simple hk hvs hΓ
      rw [hnil] at hfl
      cases fvs with
      | cons _ _ => exact absurd hfl id
      | nil =>
      obtain ⟨v, hra, hva⟩ := simple_eval alt Γ env ρ ta hlalt hΓ hlook hsa
      refine ⟨v, fun π => ?_, hva⟩
      obtain ⟨n₁, h₁⟩ := hrs (.caseScrutinee talts ρ :: π)
      obtain ⟨n₂, h₂⟩ := hra π
      refine ⟨1 + n₁ + 1 + n₂, ?_⟩
      rw [steps_trans, steps_trans, steps_trans]
      show steps n₂ (steps 1 (steps n₁ (.compute (.caseScrutinee talts ρ :: π) ρ ts))) = _
      rw [h₁]
      rw [show ∀ x, steps 1 x = step x from fun _ => rfl]
      rw [caseStep hshape talts ρ π, lowerTotalExprList_length hal, ← caseMergeList_length Γ alts, hcc]
      simp only [Bool.false_eq_true, if_false, hta, List.map_nil, List.nil_append]
      exact h₂
    · rw [hr] at hs
      rcases hs with h | ⟨_, _, h, _⟩
      · simp [Expr.isAtom] at h
      · cases h
termination_by r => sizeOf r

theorem simple_eval_list : ∀ (rs : List Expr) (Γ : KnownCtors) (env : List VarId) (ρ : CekEnv)
    (ts : List Term), lowerTotalExprList env rs = some ts → FactsHold Γ env ρ →
    (∀ n, 0 < n → n ≤ env.length → ∃ v, ρ.lookup n = some v) →
    (∀ f ∈ (caseMergeList Γ rs).1, f.isAtom = true) →
    ∃ vs, ListRel2 (fun t v => ∀ π, ∃ n, steps n (.compute π ρ t) = .ret π v) ts vs ∧
      ListRel2 (AtomEval env ρ) (caseMergeList Γ rs).1 vs
  | [], Γ, env, ρ, ts, h, _, _, _ => by
    rw [lowerTotalExprList_nil] at h; cases h
    exact ⟨[], trivial, by simp [caseMergeList, ListRel2]⟩
  | r :: rs, Γ, env, ρ, ts, h, hΓ, hlook, hat => by
    have hcons : (caseMergeList Γ (r :: rs)).1 = (caseMerge Γ r).1 :: (caseMergeList Γ rs).1 := by
      simp [caseMergeList]
    rw [hcons] at hat ⊢
    rw [lowerTotalExprList_cons] at h
    cases hr : lowerTotalExpr env r <;> cases hrs : lowerTotalExprList env rs <;>
      simp [hr, hrs] at h
    rename_i tr trs
    subst h
    obtain ⟨v, hv, hsv⟩ := simple_eval r Γ env ρ tr hr hΓ hlook (.inl (hat _ (.head _)))
    obtain ⟨vs, hvs, hsvs⟩ := simple_eval_list rs Γ env ρ trs hrs hΓ hlook
      (fun f hf => hat f (.tail _ hf))
    have hatom : AtomEval env ρ (caseMerge Γ r).1 v := by
      rcases hsv with h | ⟨_, _, _, h, _⟩
      · exact h
      · have := hat _ (.head _); rw [h] at this; simp [Expr.isAtom] at this
    exact ⟨v :: vs, ⟨hv, hvs⟩, ⟨hatom, hsvs⟩⟩
termination_by rs => sizeOf rs

end

end Moist.Verified.CaseMerge
