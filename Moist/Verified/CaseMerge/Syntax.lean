import Moist.MIR.Optimize.CaseMerge
import Moist.Verified.MIR.Hoist

/-! # Known-constructor case simplification: syntactic facts

Unfolding equations for `caseMerge`, membership in filtered fact
environments, freshness of the fact environment, and the lowering of the
shapes the pass produces (`let` chains, application spines).
-/

namespace Moist.Verified.CaseMerge

open Moist.MIR
open Moist.Plutus.Term (Term)
open Moist.Verified (closedAt closedAtList renameTerm renameTermList shiftRename)
open Moist.Verified.MIR (lowerTotalExprList lowerTotalExprList_nil lowerTotalExprList_cons
  lowerTotalExpr_app)

/-! ## Unfolding -/

/-- The result of a `Case` node from its processed scrutinee and alternatives. -/
def caseResult (Γ : KnownCtors) (scrutinee : Expr) (alternatives : List Expr) : Expr :=
  match scrutinee with
  | .Constr tag fields => reduceConstructorCase tag fields alternatives
  | _ => match knownConstructor Γ scrutinee with
    | some info =>
      if info.listValue && alternatives.length > 2 then .Case scrutinee alternatives
      else selectAlternative info.tag info.constructorCount info.fields alternatives
    | none => .Case scrutinee alternatives

/-- The fact environment after binding `x` to the processed right-hand side `rhs`. -/
def bindFact (Γ : KnownCtors) (x : VarId) (rhs : Expr) : KnownCtors :=
  match knownConstructor Γ rhs with
  | some info =>
    if (freeVarsList info.fields).contains x then filterKnown x Γ
    else (x, info) :: filterKnown x Γ
  | none => filterKnown x Γ

theorem caseMerge_lam (Γ : KnownCtors) (x : VarId) (body : Expr) :
    (caseMerge Γ (.Lam x body)).1 = .Lam x (caseMerge (filterKnown x Γ) body).1 := by
  simp [caseMerge]

theorem caseMerge_fix (Γ : KnownCtors) (x : VarId) (body : Expr) :
    (caseMerge Γ (.Fix x body)).1 = .Fix x (caseMerge (filterKnown x Γ) body).1 := by
  simp [caseMerge]

theorem caseMerge_app (Γ : KnownCtors) (f a : Expr) :
    (caseMerge Γ (.App f a)).1 = .App (caseMerge Γ f).1 (caseMerge Γ a).1 := by
  simp [caseMerge]

theorem caseMerge_force (Γ : KnownCtors) (e : Expr) :
    (caseMerge Γ (.Force e)).1 = .Force (caseMerge Γ e).1 := by
  simp [caseMerge]

theorem caseMerge_delay (Γ : KnownCtors) (e : Expr) :
    (caseMerge Γ (.Delay e)).1 = .Delay (caseMerge Γ e).1 := by
  simp [caseMerge]

theorem caseMerge_constr (Γ : KnownCtors) (tag : Nat) (fields : List Expr) :
    (caseMerge Γ (.Constr tag fields)).1 = .Constr tag (caseMergeList Γ fields).1 := by
  simp [caseMerge]

theorem caseMerge_var (Γ : KnownCtors) (x : VarId) : (caseMerge Γ (.Var x)).1 = .Var x := by
  simp [caseMerge]

theorem caseMerge_lit (Γ : KnownCtors) (l : Moist.Plutus.Term.Const × Moist.Plutus.Term.BuiltinType) :
    (caseMerge Γ (.Lit l)).1 = .Lit l := by
  simp [caseMerge]

theorem caseMerge_builtin (Γ : KnownCtors) (b : Moist.Plutus.Term.BuiltinFun) :
    (caseMerge Γ (.Builtin b)).1 = .Builtin b := by
  simp [caseMerge]

theorem caseMerge_error (Γ : KnownCtors) : (caseMerge Γ .Error).1 = .Error := by
  simp [caseMerge]

theorem caseMerge_case (Γ : KnownCtors) (s : Expr) (alts : List Expr) :
    (caseMerge Γ (.Case s alts)).1 =
      caseResult Γ (caseMerge Γ s).1 (caseMergeList Γ alts).1 := by
  rw [caseMerge]
  generalize caseMerge Γ s = rs
  generalize caseMergeList Γ alts = ra
  obtain ⟨s', cs⟩ := rs
  obtain ⟨a', ca⟩ := ra
  cases s' <;> simp only [caseResult] <;>
    (try (cases knownConstructor Γ _ <;> simp only [] <;> (try split) <;> rfl))

theorem caseMerge_let (Γ : KnownCtors) (bs : List (VarId × Expr × Bool)) (body : Expr) :
    (caseMerge Γ (.Let bs body)).1 =
      .Let (caseMergeBinds Γ bs).1 (caseMerge (caseMergeBinds Γ bs).2.1 body).1 := by
  simp [caseMerge]

theorem caseMergeBinds_nil (Γ : KnownCtors) :
    (caseMergeBinds Γ []).1 = [] ∧ (caseMergeBinds Γ []).2.1 = Γ := by
  simp [caseMergeBinds]

theorem caseMergeBinds_cons (Γ : KnownCtors) (x : VarId) (r : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) :
    (caseMergeBinds Γ ((x, r, er) :: rest)).1 =
        (x, (caseMerge Γ r).1, er) ::
          (caseMergeBinds (bindFact Γ x (caseMerge Γ r).1) rest).1 ∧
      (caseMergeBinds Γ ((x, r, er) :: rest)).2.1 =
        (caseMergeBinds (bindFact Γ x (caseMerge Γ r).1) rest).2.1 := by
  simp only [caseMergeBinds, bindFact]
  constructor <;> rfl

/-- Unfolding of a non-empty `let` through `caseMerge`. -/
theorem caseMerge_let_cons (Γ : KnownCtors) (x : VarId) (r : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) :
    (caseMerge Γ (.Let ((x, r, er) :: rest) body)).1 =
      .Let ((x, (caseMerge Γ r).1, er) ::
        (caseMergeBinds (bindFact Γ x (caseMerge Γ r).1) rest).1)
        (caseMerge (caseMergeBinds (bindFact Γ x (caseMerge Γ r).1) rest).2.1 body).1 := by
  rw [caseMerge_let, (caseMergeBinds_cons Γ x r er rest).1,
    (caseMergeBinds_cons Γ x r er rest).2]

theorem caseMerge_let_nil (Γ : KnownCtors) (body : Expr) :
    (caseMerge Γ (.Let [] body)).1 = .Let [] (caseMerge Γ body).1 := by
  rw [caseMerge_let, (caseMergeBinds_nil Γ).1, (caseMergeBinds_nil Γ).2]

theorem caseMergeList_eq_map (Γ : KnownCtors) :
    ∀ (es : List Expr), (caseMergeList Γ es).1 = es.map (fun e => (caseMerge Γ e).1)
  | [] => by simp [caseMergeList]
  | e :: es => by
    have ih := caseMergeList_eq_map Γ es
    simp only [caseMergeList, List.map_cons] at ih ⊢
    rw [ih]

theorem caseMergeList_length (Γ : KnownCtors) (es : List Expr) :
    (caseMergeList Γ es).1.length = es.length := by
  rw [caseMergeList_eq_map, List.length_map]

theorem caseMergeList_getElem? (Γ : KnownCtors) (es : List Expr) (n : Nat) :
    (caseMergeList Γ es).1[n]? = es[n]?.map (fun e => (caseMerge Γ e).1) := by
  rw [caseMergeList_eq_map, List.getElem?_map]

/-! ## Shapes of `caseResult` -/

theorem caseResult_cases (Γ : KnownCtors) (s : Expr) (alts : List Expr) :
    (∃ tag fields, s = .Constr tag fields ∧
        caseResult Γ s alts = reduceConstructorCase tag fields alts) ∨
    (∃ info, (∀ tag fields, s ≠ .Constr tag fields) ∧ knownConstructor Γ s = some info ∧
        ¬ (info.listValue = true ∧ alts.length > 2) ∧
        caseResult Γ s alts =
          selectAlternative info.tag info.constructorCount info.fields alts) ∨
    caseResult Γ s alts = .Case s alts := by
  cases s with
  | Constr tag fields => exact .inl ⟨tag, fields, rfl, rfl⟩
  | _ =>
    simp only [caseResult]
    first
    | (cases hk : knownConstructor Γ _ with
        | none => exact .inr (.inr rfl)
        | some info =>
          by_cases hl : info.listValue = true ∧ alts.length > 2
          · refine .inr (.inr ?_)
            simp only [hl.1, hl.2, decide_true, Bool.and_self, if_true]
          · refine .inr (.inl ⟨info, ?_, rfl, hl, ?_⟩)
            · intro _ _ h; exact Expr.noConfusion h
            have : (info.listValue && decide (alts.length > 2)) = false := by
              cases hv : info.listValue <;> simp_all
            simp only [this, Bool.false_eq_true, if_false])

/-! ## Filtered fact environments -/

theorem mem_filterKnown {x : VarId} {Γ : KnownCtors} {p : VarId × KnownCtor} :
    p ∈ filterKnown x Γ ↔
      p ∈ Γ ∧ (p.1 == x) = false ∧ (freeVarsList p.2.fields).contains x = false := by
  obtain ⟨y, info⟩ := p
  simp only [filterKnown, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨hm, hne, hc⟩
    exact ⟨hm, by simpa [bne] using hne, hc⟩
  · rintro ⟨hm, hne, hc⟩
    exact ⟨hm, by simp [bne, hne], hc⟩

theorem mem_bindFact {Γ : KnownCtors} {x : VarId} {rhs : Expr} {p : VarId × KnownCtor} :
    p ∈ bindFact Γ x rhs →
      p ∈ filterKnown x Γ ∨
        (p = (x, p.2) ∧ knownConstructor Γ rhs = some p.2 ∧
          (freeVarsList p.2.fields).contains x = false) := by
  unfold bindFact
  cases hk : knownConstructor Γ rhs with
  | none => exact .inl
  | some info =>
    simp only []
    split
    · exact .inl
    · rename_i hc
      intro hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact .inr ⟨rfl, rfl, by simpa using hc⟩
      · exact .inl hp

/-! ## Freshness -/

/-- An upper bound on every uid occurring in a fact environment. -/
def maxUidKnown : KnownCtors → Nat
  | [] => 0
  | (x, info) :: rest => max (max x.uid (maxUidExprList info.fields)) (maxUidKnown rest)

theorem maxUidKnown_mem : ∀ {Γ : KnownCtors} {p : VarId × KnownCtor}, p ∈ Γ →
    p.1.uid ≤ maxUidKnown Γ ∧ maxUidExprList p.2.fields ≤ maxUidKnown Γ
  | (x, info) :: rest, p, hp => by
    simp only [maxUidKnown]
    rcases List.mem_cons.mp hp with rfl | hp
    · simp only []; omega
    · have := maxUidKnown_mem hp; omega

/-- Every key and field of the fact environment avoids a variable above its uids. -/
theorem fresh_known {Γ : KnownCtors} {s : VarId} (hs : s.uid > maxUidKnown Γ) :
    ∀ p ∈ Γ, (p.1 == s) = false ∧ (freeVarsList p.2.fields).contains s = false := by
  intro p hp
  obtain ⟨h1, h2⟩ := maxUidKnown_mem hp
  refine ⟨?_, maxUidExprList_fresh _ _ (by omega)⟩
  rw [VarId.beq_false_iff]; exact .inr (by omega)

/-! ## Variables and lookups -/

theorem envLookupT_congr {env : List VarId} {a b : VarId} (h : (a == b) = true) :
    envLookupT env a = envLookupT env b := by
  have hab := (VarId.beq_true_iff a b).mp h
  unfold envLookupT
  generalize 0 = n
  induction env generalizing n with
  | nil => rfl
  | cons y ys ih =>
    simp only [envLookupT.go]
    have : (y == a) = (y == b) := by
      cases h1 : (y == a) <;> cases h2 : (y == b) <;> try rfl
      · rw [VarId.beq_true_iff] at h2; rw [VarId.beq_false_iff] at h1
        rcases h1 with h1 | h1
        · exact absurd (h2.1.trans hab.1.symm) h1
        · exact absurd (h2.2.trans hab.2.symm) h1
      · rw [VarId.beq_true_iff] at h1; rw [VarId.beq_false_iff] at h2
        rcases h2 with h2 | h2
        · exact absurd (h1.1.trans hab.1) h2
        · exact absurd (h1.2.trans hab.2) h2
    rw [this]
    split
    · rfl
    · exact ih (n + 1)

theorem freeVarsList_not_contains_mem {fields : List Expr} {x : VarId}
    (h : (freeVarsList fields).contains x = false) :
    ∀ f ∈ fields, (freeVars f).contains x = false := by
  induction fields with
  | nil => intro f hf; cases hf
  | cons e rest ih =>
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact freeVarsList_union_left _ _ _ h
    · exact ih (freeVarsList_union_right _ _ _ h) f hf

theorem freeVars_var_not_contains {z x : VarId} (h : (freeVars (.Var z)).contains x = false) :
    (z == x) = false := by
  rw [freeVars, VarSet.singleton_contains'] at h; exact h

/-! ## Lowering of produced shapes -/

theorem lowerTotalExpr_let_cons (env : List VarId) (x : VarId) (r : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) :
    lowerTotalExpr env (.Let ((x, r, er) :: rest) body) =
      (lowerTotalExpr env r).bind fun tr =>
        (lowerTotalExpr (x :: env) (.Let rest body)).map fun tb => .Apply (.Lam 0 tb) tr := by
  simp only [lowerTotalExpr, expandFix, expandFixBinds, lowerTotal, lowerTotalLet]
  cases lowerTotal env (expandFix r) <;>
    cases lowerTotalLet (x :: env) (expandFixBinds rest) (expandFix body) <;> rfl

/-- Lowering of a left-nested application spine. -/
theorem lowerTotalExpr_foldl_app (env : List VarId) :
    ∀ (args : List Expr) (f : Expr),
      lowerTotalExpr env (args.foldl Expr.App f) =
        (lowerTotalExpr env f).bind fun tf =>
          (lowerTotalExprList env args).map fun targs => targs.foldl Term.Apply tf
  | [], f => by
    rw [lowerTotalExprList_nil, List.foldl_nil]; cases lowerTotalExpr env f <;> rfl
  | a :: args, f => by
    rw [List.foldl_cons, lowerTotalExpr_foldl_app env args, lowerTotalExpr_app,
      lowerTotalExprList_cons]
    cases lowerTotalExpr env f <;> cases lowerTotalExpr env a <;>
      cases lowerTotalExprList env args <;> rfl

theorem closedAt_foldl_apply (d : Nat) :
    ∀ (args : List Term) (f : Term),
      closedAt d (args.foldl Term.Apply f) = (closedAt d f && closedAtList d args)
  | [], f => by simp [closedAtList]
  | a :: args, f => by
    rw [List.foldl_cons, closedAt_foldl_apply d args]
    simp only [closedAt, closedAtList, Bool.and_assoc]

theorem lowerTotalExprList_length {env : List VarId} :
    ∀ {es : List Expr} {ts : List Term}, lowerTotalExprList env es = some ts → ts.length = es.length
  | [], ts, h => by rw [lowerTotalExprList_nil] at h; cases h; rfl
  | e :: es, ts, h => by
    rw [lowerTotalExprList_cons] at h
    cases he : lowerTotalExpr env e <;> cases hes : lowerTotalExprList env es <;>
      simp [he, hes] at h
    subst h
    simp [lowerTotalExprList_length hes]

theorem lowerTotalExprList_getElem? {env : List VarId} :
    ∀ {es : List Expr} {ts : List Term}, lowerTotalExprList env es = some ts →
      ∀ n : Nat, (∃ e t, es[n]? = some e ∧ ts[n]? = some t ∧ lowerTotalExpr env e = some t) ∨
        (es[n]? = none ∧ ts[n]? = none)
  | [], ts, h, n => by rw [lowerTotalExprList_nil] at h; cases h; exact .inr ⟨rfl, rfl⟩
  | e :: es, ts, h, n => by
    rw [lowerTotalExprList_cons] at h
    cases he : lowerTotalExpr env e <;> cases hes : lowerTotalExprList env es <;>
      simp [he, hes] at h
    subst h
    cases n with
    | zero => exact .inl ⟨e, _, rfl, rfl, he⟩
    | succ n => simpa using lowerTotalExprList_getElem? hes n

theorem lowerTotalExprList_of_forall {env : List VarId} :
    ∀ {es : List Expr}, (∀ e ∈ es, (lowerTotalExpr env e).isSome) →
      ∃ ts, lowerTotalExprList env es = some ts
  | [], _ => ⟨[], lowerTotalExprList_nil env⟩
  | e :: es, h => by
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (h e (.head _))
    obtain ⟨ts, hts⟩ := lowerTotalExprList_of_forall (fun e' he' => h e' (.tail _ he'))
    exact ⟨t :: ts, by rw [lowerTotalExprList_cons, ht, hts]; rfl⟩

theorem lowerTotalExprList_mem {env : List VarId} :
    ∀ {es : List Expr} {ts : List Term}, lowerTotalExprList env es = some ts →
      ∀ e ∈ es, ∃ t ∈ ts, lowerTotalExpr env e = some t
  | [], ts, h, e, he => by cases he
  | e :: es, ts, h, e', he' => by
    rw [lowerTotalExprList_cons] at h
    cases he : lowerTotalExpr env e <;> cases hes : lowerTotalExprList env es <;>
      simp [he, hes] at h
    subst h
    rcases List.mem_cons.mp he' with rfl | he'
    · exact ⟨_, .head _, he⟩
    · obtain ⟨t, ht, hl⟩ := lowerTotalExprList_mem hes e' he'
      exact ⟨t, .tail _ ht, hl⟩

end Moist.Verified.CaseMerge
