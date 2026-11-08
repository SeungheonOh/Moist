import Moist.Verified.TagChainsSoundness.Tests
import Moist.Verified.ShapesSoundness.Destructors

variable [sv : Moist.CEK.SemVariant]

/-! # Tag tests as integer cases

`TagRewrites Γ e e'` is refinement of lowerings in one environment that
realizes the facts `Γ`. Each rule of `tagCaseRule` is such a refinement:

* the integer case rules (`integerCaseRule_rewrites`): a test selects its
  alternative exactly for its literal, and the integer case selects the
  alternative at the tag's index, failing for negative tags and tags without
  an alternative; padding alternatives fail like the error default;
* the range rule (`rangeRule_rewrites`): a chain of failing tests over a
  contiguous range fails exactly when the two comparisons place the tag in
  that range, and otherwise continues with the same expression.
-/

namespace Moist.Verified.TagChains

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.ShapeFacts
open Moist.Verified.BetaValueRefines Moist.Verified.Contextual

/-- Refinement of lowerings in every environment realizing the facts. -/
def TagRewrites (Γ : List (VarId × Expr)) (e e' : Expr) : Prop :=
  ∀ env t, EnvDistinct env → FactsScoped Γ env → lowerTotalExpr env e = some t →
    ∃ t', lowerTotalExpr env e' = some t' ∧ FactRefines env.length (FactsHold Produces Γ env) t t'

theorem TagRewrites.refl (Γ : List (VarId × Expr)) (e : Expr) : TagRewrites Γ e e :=
  fun _ t _ _ h => ⟨t, h, FactRefines.refl _ _ _⟩

theorem TagRewrites.trans {Γ : List (VarId × Expr)} {a b c : Expr} (h₁ : TagRewrites Γ a b)
    (h₂ : TagRewrites Γ b c) : TagRewrites Γ a c := by
  intro env t hd hs hlow
  obtain ⟨t', hl', r₁⟩ := h₁ env t hd hs hlow
  obtain ⟨t'', hl'', r₂⟩ := h₂ env t' hd hs hl'
  exact ⟨t'', hl'', r₁.trans r₂⟩

/-- A walk step followed by a rewrite of its result. -/
theorem FactRel.post {Γ : List (VarId × Expr)} {e e' e'' : Expr}
    (h : FactRel (fun _ => True) Produces Γ e e') (hpost : TagRewrites Γ e' e'') :
    FactRel (fun _ => True) Produces Γ e e'' := by
  intro env t hG hd hf hk hs hlow
  obtain ⟨t', hl', r₁⟩ := h env t hG hd hf hk hs hlow
  obtain ⟨t'', hl'', r₂⟩ := hpost env t' hd hs hl'
  exact ⟨t'', hl'', r₁.trans r₂⟩

/-! ## Bound tags -/

/-- The variable of a resolved partial application is bound. -/
theorem resolveHead_app2_var_bound :
    ∀ (n : Nat) (Γ : List (VarId × Expr)) (e : Expr) {g Y : Expr} {l : VarId} {env : List VarId},
      resolveHead n Γ e = .App (.App g (.Var l)) Y → FactsScoped Γ env → EnvDistinct env →
      (lowerTotalExpr env e).isSome = true → (envLookupT env l).isSome = true := by
  intro n
  induction n with
  | zero =>
    intro Γ e g Y l env hres _ _ hlow
    rw [resolveHead_zero] at hres; subst hres
    cases h : lowerTotalExpr env (.App (.App g (.Var l)) Y) with
    | none => rw [h] at hlow; cases hlow
    | some t =>
      obtain ⟨tf, _, htf, _, _⟩ := lowerTotalExpr_app_some h
      obtain ⟨_, ta, _, hta, _⟩ := lowerTotalExpr_app_some htf
      obtain ⟨i, hi, _⟩ := lowerTotalExpr_var_some hta
      simp [hi]
  | succ n ih =>
    intro Γ e g Y l env hres hs hd hlow
    cases e with
    | Var x =>
      rw [resolveHead_var] at hres
      cases hf : Γ.find? (fun entry => entry.1 == x) with
      | none => rw [hf] at hres; cases hres
      | some entry =>
        obtain ⟨y, rhs⟩ := entry
        rw [hf] at hres
        rw [lowerTotalExpr_var] at hlow
        cases hi : envLookupT env x with
        | none => rw [hi] at hlow; simp at hlow
        | some i =>
          obtain ⟨k, hik, hk, hrhs⟩ := hs x (y, rhs) i hf hi
          have hin := ih Γ rhs hres (hs.drop hd k) (hd.drop k) hrhs
          cases hl : envLookupT (env.drop k) l with
          | none => rw [hl] at hin; simp at hin
          | some j => rw [hd.drop_lookup k hl]; rfl
    | App f a =>
      rw [resolveHead_app] at hres
      simp only [Expr.App.injEq] at hres
      obtain ⟨hf, rfl⟩ := hres
      cases h : lowerTotalExpr env (.App f a) with
      | none => rw [h] at hlow; cases hlow
      | some t =>
        obtain ⟨tf, _, htf, _, _⟩ := lowerTotalExpr_app_some h
        exact resolveHead_app_var_bound n Γ f hf hs hd (by simp [htf])
    | Force _ => rw [resolveHead_force] at hres; cases hres
    | Lit _ | Error | Lam _ _ | Fix _ _ | Delay _ | Constr _ _ | Case _ _ | Let _ _ | Builtin _ =>
      simp only [resolveHead] at hres; cases hres

theorem resolvedTagTest_bound {Γ : List (VarId × Expr)} {s : Expr} {t : VarId} {c : Int}
    {env : List VarId} (h : resolvedTagTest Γ s = some (t, c)) (hs : FactsScoped Γ env)
    (hd : EnvDistinct env) (hlow : (lowerTotalExpr env s).isSome = true) :
    (envLookupT env t).isSome = true := by
  unfold resolvedTagTest at h
  split at h
  · rename_i subject value ty hres
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact resolveHead_app2_var_bound 64 Γ s hres hs hd hlow
    · cases h
  · rename_i value ty subject hres
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact resolveHead_app_var_bound 64 Γ s hres hs hd hlow
    · cases h
  · cases h

theorem knownInteger_values {Γ : List (VarId × Expr)} {e : Expr} {env : List VarId} {ρ : CekEnv}
    {t : Term} (hint : knownInteger 64 Γ e = true) (hfacts : FactsHold Produces Γ env ρ)
    (hd : EnvDistinct env) (hlow : lowerTotalExpr env e = some t) :
    ∀ v, Halts ρ t v → ∃ n : Int, v = .VCon (.Integer n) := fun _ hv =>
  knownInteger_sound (fun _ _ _ _ h => h) 64 Γ e hint hfacts hd hlow hv

/-- Every tag test evaluates its tag and then selects by `tag = c`. -/
theorem tagTest_sem {Γ : List (VarId × Expr)} {s subject : Expr} {c : Int} {env : List VarId}
    {ts : Term} (h : tagTest Γ s = some (subject, c)) (hs : FactsScoped Γ env)
    (hd : EnvDistinct env) (hlow : lowerTotalExpr env s = some ts) :
    ∃ tX, lowerTotalExpr env subject = some tX ∧
      ∀ ρ, FactsHold Produces Γ env ρ → EnvWellFormed env.length ρ → TestSem ρ ts tX c := by
  unfold tagTest at h
  split at h
  · rename_i t value hres
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (resolvedTagTest_bound hres hs hd (by simp [hlow]))
    refine ⟨.Var (i + 1), by rw [lowerTotalExpr_var, hi]; rfl, fun ρ hF henv => ?_⟩
    obtain ⟨i', n, hi', hn, hv⟩ := resolvedTagTest_sound hres hF hd henv hlow
    rw [hi] at hi'; cases hi'
    exact testSem_var hn hv
  · unfold directTagTest at h
    split at h
    · rename_i subject' value ty
      split at h
      · rename_i hint
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨tf, tc, htf, htc, rfl⟩ := lowerTotalExpr_app_some hlow
        obtain ⟨tb, tX, htb, htX, rfl⟩ := lowerTotalExpr_app_some htf
        rw [lowerTotalExpr_builtin] at htb; cases htb
        rw [lowerTotalExpr_lit] at htc; cases htc
        exact ⟨tX, htX, fun ρ hF _ => testSem_direct_left (knownInteger_values hint hF hd htX)⟩
      · cases h
    · rename_i value ty subject'
      split at h
      · rename_i hint
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨tf, tX, htf, htX, rfl⟩ := lowerTotalExpr_app_some hlow
        obtain ⟨tb, tc, htb, htc, rfl⟩ := lowerTotalExpr_app_some htf
        rw [lowerTotalExpr_builtin] at htb; cases htb
        rw [lowerTotalExpr_lit] at htc; cases htc
        exact ⟨tX, htX, fun ρ hF _ => testSem_direct_right (knownInteger_values hint hF hd htX)⟩
      · cases h
    · cases h

/-! ## Integer cases -/

def intSelect (alts : List Term) (n : Int) : Option Term :=
  if 0 ≤ n then alts[n.toNat]? else none

def selected (π : Stack) (ρ : CekEnv) : Option Term → State
  | some alt => .compute π ρ alt
  | none => .error

theorem error_reaches (π : Stack) (ρ : CekEnv) : Reaches (.compute π ρ .Error) .error := ⟨1, rfl⟩

def placeTerm (alts : List Term) (index : Nat) (alt : Term) : List Term :=
  if index < alts.length then alts.set index alt
  else alts ++ List.replicate (index - alts.length) .Error ++ [alt]

theorem lowerTotalExprList_append (env : List VarId) :
    ∀ {xs ys : List Expr} {txs tys : List Term}, MIR.lowerTotalExprList env xs = some txs →
      MIR.lowerTotalExprList env ys = some tys →
      MIR.lowerTotalExprList env (xs ++ ys) = some (txs ++ tys)
  | [], _, txs, tys, hx, hy => by
    rw [MIR.lowerTotalExprList_nil] at hx; cases hx; simpa using hy
  | x :: xs, ys, txs, tys, hx, hy => by
    rw [MIR.lowerTotalExprList_cons] at hx
    cases h₁ : lowerTotalExpr env x with
    | none => rw [h₁] at hx; cases hx
    | some tx =>
      cases h₂ : MIR.lowerTotalExprList env xs with
      | none => rw [h₁, h₂] at hx; cases hx
      | some txs' =>
        rw [h₁, h₂] at hx; cases hx
        rw [List.cons_append, MIR.lowerTotalExprList_cons, h₁, lowerTotalExprList_append env h₂ hy]
        rfl

theorem lowerTotalExprList_errors (env : List VarId) :
    ∀ n, MIR.lowerTotalExprList env (errorAlternatives n) = some (List.replicate n .Error)
  | 0 => MIR.lowerTotalExprList_nil env
  | n + 1 => by
    simp only [errorAlternatives, List.replicate_succ]
    rw [MIR.lowerTotalExprList_cons, lowerTotalExpr_error]
    have := lowerTotalExprList_errors env n
    simp only [errorAlternatives] at this
    rw [this]; rfl

theorem lowerTotalExprList_set (env : List VarId) :
    ∀ {xs : List Expr} {txs : List Term} {a : Expr} {ta : Term} (i : Nat),
      MIR.lowerTotalExprList env xs = some txs → lowerTotalExpr env a = some ta →
      MIR.lowerTotalExprList env (xs.set i a) = some (txs.set i ta)
  | [], txs, a, ta, i, hx, _ => by
    rw [MIR.lowerTotalExprList_nil] at hx; cases hx
    simp only [List.set_nil]; exact MIR.lowerTotalExprList_nil env
  | x :: xs, txs, a, ta, i, hx, ha => by
    rw [MIR.lowerTotalExprList_cons] at hx
    cases h₁ : lowerTotalExpr env x with
    | none => rw [h₁] at hx; cases hx
    | some tx =>
      cases h₂ : MIR.lowerTotalExprList env xs with
      | none => rw [h₁, h₂] at hx; cases hx
      | some txs' =>
        rw [h₁, h₂] at hx; cases hx
        cases i with
        | zero =>
          simp only [List.set_cons_zero]
          rw [MIR.lowerTotalExprList_cons, ha, h₂]; rfl
        | succ i =>
          simp only [List.set_cons_succ]
          rw [MIR.lowerTotalExprList_cons, h₁, lowerTotalExprList_set env i h₂ ha]; rfl

theorem lowerTotalExprList_length {env : List VarId} :
    ∀ {xs : List Expr} {txs : List Term}, MIR.lowerTotalExprList env xs = some txs →
      txs.length = xs.length
  | [], txs, hx => by rw [MIR.lowerTotalExprList_nil] at hx; cases hx; rfl
  | x :: xs, txs, hx => by
    rw [MIR.lowerTotalExprList_cons] at hx
    cases h₁ : lowerTotalExpr env x with
    | none => rw [h₁] at hx; cases hx
    | some tx =>
      cases h₂ : MIR.lowerTotalExprList env xs with
      | none => rw [h₁, h₂] at hx; cases hx
      | some txs' =>
        rw [h₁, h₂] at hx; cases hx
        simp [lowerTotalExprList_length h₂]

theorem lowerTotalExprList_place {env : List VarId} {xs : List Expr} {txs : List Term}
    {a : Expr} {ta : Term} (i : Nat) (hx : MIR.lowerTotalExprList env xs = some txs)
    (ha : lowerTotalExpr env a = some ta) :
    MIR.lowerTotalExprList env (placeAlternative xs i a) = some (placeTerm txs i ta) := by
  unfold placeAlternative placeTerm
  rw [lowerTotalExprList_length hx]
  split
  · exact lowerTotalExprList_set env i hx ha
  · refine lowerTotalExprList_append env (lowerTotalExprList_append env hx
      (lowerTotalExprList_errors env _)) ?_
    rw [MIR.lowerTotalExprList_cons, ha, MIR.lowerTotalExprList_nil]; rfl

/-- The placed alternative is selected for its index; every other index
    selects the same alternative as before, or a padding `error` where
    there was none. -/
theorem intSelect_place (talts : List Term) (c : Nat) (ta : Term) (n : Int) :
    (n = c → intSelect (placeTerm talts c ta) n = some ta) ∧
    (n ≠ c → intSelect (placeTerm talts c ta) n = intSelect talts n ∨
      (intSelect talts n = none ∧ intSelect (placeTerm talts c ta) n = some .Error)) := by
  unfold intSelect placeTerm
  constructor
  · intro hn; subst hn
    simp only [Int.natCast_nonneg, if_true, Int.toNat_natCast]
    split
    · rename_i hlt; simp [hlt]
    · rename_i hge
      rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_append, List.length_replicate]
      rw [show c - (talts.length + (c - talts.length)) = 0 by omega]; rfl
  · intro hn
    by_cases h0 : 0 ≤ n
    · simp only [h0, if_true]
      have hk : n.toNat ≠ c := by omega
      split
      · left; simp [hk.symm]
      · rename_i hge
        by_cases hlt : n.toNat < talts.length
        · left; rw [List.append_assoc, List.getElem?_append_left hlt]
        · by_cases hpad : n.toNat - talts.length < c - talts.length
          · right
            refine ⟨by simp; omega, ?_⟩
            rw [List.append_assoc, List.getElem?_append_right (by omega)]
            rw [List.getElem?_append_left (by simpa using hpad)]; simp [hpad]
          · left
            rw [List.append_assoc, List.getElem?_append_right (by omega),
              List.getElem?_append_right (by simp; omega)]
            have h1 : talts[n.toNat]? = none := List.getElem?_eq_none (by omega)
            rw [h1]
            simp only [List.length_replicate]
            apply List.getElem?_eq_none
            simp; omega
    · left; simp [h0]

theorem obsRefines_error_compute (π : Stack) (ρ : CekEnv) :
    ObsRefines .error (.compute π ρ .Error) :=
  obsRefines_of_reaches (reaches_refl _) (error_reaches π ρ) (obsRefines_refl _)

theorem int_case_reaches {ρ : CekEnv} {π : Stack} {tX : Term} {n : Int} (talts : List Term)
    (h : Halts ρ tX (.VCon (.Integer n))) :
    Reaches (.compute π ρ (.Case tX talts)) (selected π ρ (intSelect talts n)) := by
  refine reaches_trans (reaches_of_steps 1 rfl) (reaches_trans (halts_on_stack h _) ?_)
  unfold intSelect
  by_cases hn : 0 ≤ n
  · simp only [hn, if_true]
    cases ha : talts[n.toNat]? with
    | none => exact ⟨1, by simp [steps, step, constToTagAndFields, hn, ha, selected]⟩
    | some alt => exact ⟨1, by simp [steps, step, constToTagAndFields, hn, ha, selected]⟩
  · simp only [hn, if_false]
    exact ⟨1, by simp [steps, step, constToTagAndFields, hn, selected]⟩

/-- A test refines a computation that evaluates the tag first, when it does
    for every integer the tag returns and fails when the tag fails. -/
theorem test_obs {ρ : CekEnv} {π : Stack} {ts tX tE tA target : Term} {c : Int}
    (hsem : TestSem ρ ts tX c)
    (hval : ∀ n : Int, Halts ρ tX (.VCon (.Integer n)) →
      ObsRefines (.compute π ρ (if n == c then tA else tE)) (.compute π ρ target))
    (herr : Errs ρ tX → Reaches (.compute π ρ target) .error) :
    ObsRefines (.compute π ρ (.Case ts [tE, tA])) (.compute π ρ target) := by
  constructor
  · rintro ⟨w, hw⟩
    rcases hsem.2.2 π tE tA _ (.inr ⟨w, rfl⟩) hw with ⟨_, impossible⟩ | ⟨n, hn, hr⟩
    · cases impossible
    · exact (hval n hn).halt ⟨w, hr⟩
  · intro he
    rcases hsem.2.2 π tE tA _ (.inl rfl) he with ⟨herrs, _⟩ | ⟨n, hn, hr⟩
    · exact herr herrs
    · exact (hval n hn).error hr

/-- A test of the tag against `c` followed by `tO` refines the integer case
    with the test's alternative placed at index `c`, whenever `tO` refines the
    selection of the remaining alternatives for every other tag. -/
theorem tag_case_obs {ρ : CekEnv} {π : Stack} {ts tX tO tM : Term} {c : Nat}
    {talts : List Term} (hsem : TestSem ρ ts tX (c : Int))
    (hother : ∀ n : Int, Halts ρ tX (.VCon (.Integer n)) → n ≠ c →
      ObsRefines (.compute π ρ tO) (selected π ρ (intSelect talts n))) :
    ObsRefines (.compute π ρ (.Case ts [tO, tM]))
      (.compute π ρ (.Case tX (placeTerm talts c tM))) := by
  refine test_obs hsem (fun n hn => ?_) (fun he => case_errs_of_scrutinee he)
  refine obsRefines_of_reaches (reaches_refl _) (int_case_reaches _ hn) ?_
  obtain ⟨hsame, hdiff⟩ := intSelect_place talts c tM n
  by_cases hnc : n = c
  · rw [hsame hnc]
    have : (n == (c : Int)) = true := by simp [hnc]
    rw [this]; exact obsRefines_refl _
  · have : (n == (c : Int)) = false := by simp [hnc]
    rw [this]
    simp only [Bool.false_eq_true, if_false]
    rcases hdiff hnc with heq | ⟨hnone, hpad⟩
    · rw [heq]; exact hother n hn hnc
    · rw [hpad]
      have h := hother n hn hnc
      rw [hnone] at h
      exact obsRefines_trans h (obsRefines_error_compute π ρ)

theorem lowerTotalExpr_case_subject {env : List VarId} {subject : Expr} {tX : Term}
    {alts : List Expr} {talts : List Term} (hX : lowerTotalExpr env subject = some tX)
    (halts : MIR.lowerTotalExprList env alts = some talts) :
    lowerTotalExpr env (.Case subject alts) = some (.Case tX talts) := by
  rw [MIR.lowerTotalExpr_case_of_list, hX, halts]; rfl

theorem integerCaseRule_rewrites {Γ : List (VarId × Expr)} {scrutinee otherwise matched out : Expr}
    {subject : Expr} {c : Int} (htest : tagTest Γ scrutinee = some (subject, c))
    (hrule : integerCaseRule subject c otherwise matched = some out) :
    TagRewrites Γ (.Case scrutinee [otherwise, matched]) out := by
  intro env te hd hs hlow
  obtain ⟨ts, tO, tM, hts, htO, htM, rfl⟩ := lowerTotalExpr_case2_some hlow
  obtain ⟨tX, htX, hsem⟩ := tagTest_sem htest hs hd hts
  unfold integerCaseRule at hrule
  split at hrule
  · cases hrule
  · rename_i hc
    have hcast : c = ((c.toNat : Nat) : Int) := by omega
    rw [hcast] at hsem
    split at hrule
    · split at hrule
      · cases hrule
        rw [lowerTotalExpr_error] at htO; cases htO
        refine ⟨_, lowerTotalExpr_case_subject htX
          (lowerTotalExprList_place c.toNat (MIR.lowerTotalExprList_nil env) htM), ?_⟩
        intro ρ π henv _ _ hF
        refine tag_case_obs (hsem ρ hF henv) fun n _ _ => ?_
        have : intSelect [] n = none := by unfold intSelect; split <;> simp
        rw [this]
        exact obsRefines_of_reaches (error_reaches π ρ) (reaches_refl _) (obsRefines_refl _)
      · cases hrule
    · rename_i tested alternatives
      split at hrule
      · rename_i hcond
        cases hrule
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        obtain ⟨htested, _⟩ := hcond
        obtain ⟨tsO, talts, htsO, htalts, rfl⟩ := lowerTotalExpr_case_some htO
        rw [MIR.alphaEq_lowerTotalExpr_eq htested, htX] at htsO
        cases htsO
        refine ⟨_, lowerTotalExpr_case_subject htX (lowerTotalExprList_place c.toNat htalts htM), ?_⟩
        intro ρ π henv _ _ hF
        exact tag_case_obs (hsem ρ hF henv) fun n hn _ =>
          obsRefines_of_reaches (int_case_reaches _ hn) (reaches_refl _) (obsRefines_refl _)
      · cases hrule
    · cases hrule

/-! ## Ranges of failing tests -/

theorem evalBuiltin_lessThanEqualsInteger (x y : Int) :
    evalBuiltin .LessThanEqualsInteger [.VCon (.Integer y), .VCon (.Integer x)] =
      some (.VCon (.Bool (decide (x ≤ y)))) := rfl

theorem lessEqual_halts {ρ : CekEnv} {tx ty : Term} {x y : Int} (hx : Halts ρ tx (.VCon (.Integer x)))
    (hy : Halts ρ ty (.VCon (.Integer y))) :
    Halts ρ (.Apply (.Apply (.Builtin .LessThanEqualsInteger) tx) ty) (.VCon (.Bool (decide (x ≤ y)))) :=
  halts_apply_intro (halts_apply_intro ⟨2, rfl⟩ hx (builtin_partial_reaches rfl rfl)) hy
    (builtin_final_reaches rfl rfl (evalBuiltin_lessThanEqualsInteger x y))

theorem case_bool_halts {ρ : CekEnv} {s a₀ a₁ : Term} {b : Bool} {v : CekValue}
    (hs : Halts ρ s (.VCon (.Bool b))) (ha : Halts ρ (if b then a₁ else a₀) v) :
    Halts ρ (.Case s [a₀, a₁]) v :=
  reaches_trans (case_bool_steps hs) ha

/-- Lowered range test. -/
def rangeTerm (j : Nat) (low high : Int) (ty₁ ty₂ ty₃ : BuiltinType) (tD : Term) : Term :=
  .Case (.Case (.Apply (.Apply (.Builtin .LessThanEqualsInteger) (.Constant (.Integer low, ty₁)))
      (.Var j))
    [.Constant (.Bool false, ty₂),
     .Apply (.Apply (.Builtin .LessThanEqualsInteger) (.Var j)) (.Constant (.Integer high, ty₃))])
    [tD, .Error]

theorem rangeTerm_reaches {ρ : CekEnv} {π : Stack} {j : Nat} {n low high : Int}
    {ty₁ ty₂ ty₃ : BuiltinType} {tD : Term} (hn : ρ.lookup j = some (.VCon (.Integer n))) :
    (low ≤ n ∧ n ≤ high → Reaches (.compute π ρ (rangeTerm j low high ty₁ ty₂ ty₃ tD)) .error) ∧
    (¬ (low ≤ n ∧ n ≤ high) →
      Reaches (.compute π ρ (rangeTerm j low high ty₁ ty₂ ty₃ tD)) (.compute π ρ tD)) := by
  have hvar := halts_var_of_lookup hn
  have hlow := lessEqual_halts (halts_constant_of (.Integer low) ty₁) hvar
  have hhigh := lessEqual_halts hvar (halts_constant_of (.Integer high) ty₃)
  have inner : Halts ρ (.Case (.Apply (.Apply (.Builtin .LessThanEqualsInteger)
      (.Constant (.Integer low, ty₁))) (.Var j)) [.Constant (.Bool false, ty₂),
      .Apply (.Apply (.Builtin .LessThanEqualsInteger) (.Var j)) (.Constant (.Integer high, ty₃))])
      (.VCon (.Bool (decide (low ≤ n) && decide (n ≤ high)))) := by
    refine case_bool_halts hlow ?_
    by_cases h₁ : low ≤ n
    · simp only [h₁, decide_true, if_true, Bool.true_and]; exact hhigh
    · simp only [h₁, decide_false, Bool.false_eq_true, if_false, Bool.false_and]
      exact halts_constant_of _ _
  have outer := case_bool_steps (π := π) (a₀ := tD) (a₁ := .Error) inner
  constructor
  · intro h
    have : (decide (low ≤ n) && decide (n ≤ high)) = true := by simp [h.1, h.2]
    rw [this] at outer
    exact reaches_trans outer (error_reaches π ρ)
  · intro h
    have : (decide (low ≤ n) && decide (n ≤ high)) = false := by
      by_cases h₁ : low ≤ n
      · have h₂ : ¬ n ≤ high := fun h₂ => h ⟨h₁, h₂⟩
        simp [h₂]
      · simp [h₁]
    rw [this] at outer
    exact outer

theorem lowerTotalExpr_lessEqual (env : List VarId) (x y : Expr) :
    lowerTotalExpr env (lessEqualInteger x y) =
      (do let tx ← lowerTotalExpr env x
          let ty ← lowerTotalExpr env y
          some (.Apply (.Apply (.Builtin .LessThanEqualsInteger) tx) ty)) := by
  unfold lessEqualInteger
  rw [MIR.lowerTotalExpr_app, MIR.lowerTotalExpr_app, lowerTotalExpr_builtin]
  cases lowerTotalExpr env x <;> cases lowerTotalExpr env y <;> rfl

theorem lowerTotalExpr_rangeCase {env : List VarId} {t : VarId} {i : Nat} {low high : Int}
    {D : Expr} {tD : Term} (hi : envLookupT env t = some i) (hD : lowerTotalExpr env D = some tD) :
    lowerTotalExpr env (rangeCase t low high D) =
      some (rangeTerm (i + 1) low high (.AtomicType .TypeInteger) (.AtomicType .TypeBool)
        (.AtomicType .TypeInteger) tD) := by
  unfold rangeCase
  rw [MIR.lowerTotalExpr_case_of_list, MIR.lowerTotalExpr_case_of_list, lowerTotalExpr_lessEqual,
    lowerTotalExpr_lit, lowerTotalExpr_var, hi]
  simp only [Option.map_some]
  rw [MIR.lowerTotalExprList_cons, lowerTotalExpr_lit, MIR.lowerTotalExprList_cons,
    lowerTotalExpr_lessEqual, lowerTotalExpr_var, hi, lowerTotalExpr_lit,
    MIR.lowerTotalExprList_nil, MIR.lowerTotalExprList_cons, hD, MIR.lowerTotalExprList_cons,
    lowerTotalExpr_error, MIR.lowerTotalExprList_nil]
  rfl

def rangeExpr (first second : VarId) (low high : Int) (ty₁ ty₂ ty₃ : BuiltinType) (D : Expr) : Expr :=
  .Case (.Case (.App (.App (.Builtin .LessThanEqualsInteger) (.Lit (.Integer low, ty₁))) (.Var first))
      [.Lit (.Bool false, ty₂),
       .App (.App (.Builtin .LessThanEqualsInteger) (.Var second)) (.Lit (.Integer high, ty₃))])
    [D, .Error]

theorem lowerTotalExpr_rangeExpr {env : List VarId} {first second : VarId} {i : Nat}
    {low high : Int} {ty₁ ty₂ ty₃ : BuiltinType} {D : Expr}
    (h₁ : envLookupT env first = some i) (h₂ : envLookupT env second = some i) :
    lowerTotalExpr env (rangeExpr first second low high ty₁ ty₂ ty₃ D) =
      (lowerTotalExpr env D).map (rangeTerm (i + 1) low high ty₁ ty₂ ty₃) := by
  unfold rangeExpr
  rw [MIR.lowerTotalExpr_case_of_list, MIR.lowerTotalExpr_case_of_list, MIR.lowerTotalExpr_app,
    MIR.lowerTotalExpr_app, lowerTotalExpr_builtin, lowerTotalExpr_lit, lowerTotalExpr_var, h₁]
  simp only [Option.map_some]
  rw [MIR.lowerTotalExprList_cons, lowerTotalExpr_lit, MIR.lowerTotalExprList_cons,
    MIR.lowerTotalExpr_app, MIR.lowerTotalExpr_app, lowerTotalExpr_builtin, lowerTotalExpr_var, h₂,
    lowerTotalExpr_lit, MIR.lowerTotalExprList_nil, MIR.lowerTotalExprList_cons]
  cases lowerTotalExpr env D with
  | none => rfl
  | some tD =>
    rw [MIR.lowerTotalExprList_cons, lowerTotalExpr_error, MIR.lowerTotalExprList_nil]
    rfl

theorem rangeCase_eq (t : VarId) (low high : Int) (D : Expr) :
    rangeCase t low high D =
      rangeExpr t t low high (.AtomicType .TypeInteger) (.AtomicType .TypeBool)
        (.AtomicType .TypeInteger) D := rfl

theorem rangeOf_some {t : VarId} {e : Expr} {low high : Int} {D : Expr}
    (h : rangeOf t e = some (low, high, D)) :
    ∃ first second ty₁ ty₂ ty₃, (first == t) = true ∧ (second == t) = true ∧
      e = rangeExpr first second low high ty₁ ty₂ ty₃ D := by
  unfold rangeOf at h
  split at h
  · rename_i low' ty₁ first ty₂ second high' ty₃ outside
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [Bool.and_eq_true] at hc
      exact ⟨first, second, ty₁, ty₂, ty₃, hc.1, hc.2, rfl⟩
    · cases h
  · cases h

/-- A chain of failing tests of `t` fails exactly for its tags and otherwise
    continues with what follows it. -/
theorem errorSpine_sound (Γ : List (VarId × Expr)) (t : VarId) (e : Expr) {env : List VarId}
    {te : Term} {i : Nat} (hd : EnvDistinct env) (hs : FactsScoped Γ env)
    (hi : envLookupT env t = some i) (hlow : lowerTotalExpr env e = some te) :
    ∃ tD, lowerTotalExpr env (errorSpine Γ t e).2 = some tD ∧
      ∀ ρ π (n : Int), FactsHold Produces Γ env ρ → EnvWellFormed env.length ρ →
        ρ.lookup (i + 1) = some (.VCon (.Integer n)) →
        (n ∈ (errorSpine Γ t e).1 → Reaches (.compute π ρ te) .error) ∧
        (n ∉ (errorSpine Γ t e).1 → Reaches (.compute π ρ te) (.compute π ρ tD)) := by
  have trivial_case : ∃ tD, lowerTotalExpr env e = some tD ∧
      ∀ ρ π (n : Int), FactsHold Produces Γ env ρ → EnvWellFormed env.length ρ →
        ρ.lookup (i + 1) = some (.VCon (.Integer n)) →
        (n ∈ ([] : List Int) → Reaches (.compute π ρ te) .error) ∧
        (n ∉ ([] : List Int) → Reaches (.compute π ρ te) (.compute π ρ tD)) :=
    ⟨te, hlow, fun _ _ _ _ _ _ => ⟨fun h => absurd h (by simp), fun _ => reaches_refl _⟩⟩
  by_cases hshape : ∃ scrutinee next, e = .Case scrutinee [next, .Error]
  · obtain ⟨scrutinee, next, rfl⟩ := hshape
    rw [errorSpine.eq_1]
    split
    · rename_i tested value htest
      split
      · rename_i htested
        obtain ⟨tS, tN, tE, htS, htN, htE, rfl⟩ := lowerTotalExpr_case2_some hlow
        rw [lowerTotalExpr_error] at htE; cases htE
        obtain ⟨tD, htD, hsem⟩ := errorSpine_sound Γ t next hd hs hi htN
        refine ⟨tD, htD, fun ρ π n hF henv hn => ?_⟩
        obtain ⟨i', n', hi', hn', hv⟩ := resolvedTagTest_sound htest hF hd henv htS
        rw [envLookupT_congr htested, hi] at hi'; cases hi'
        rw [hn] at hn'; cases hn'
        have step := case_bool_steps (π := π) (a₀ := tN) (a₁ := .Error) hv
        obtain ⟨hin, hout⟩ := hsem ρ π n hF henv hn
        constructor
        · intro hmem
          by_cases hnv : n = value
          · have : (n == value) = true := by simp [hnv]
            rw [this] at step
            exact reaches_trans step (error_reaches π ρ)
          · have : (n == value) = false := by simp [hnv]
            rw [this] at step
            simp only [Bool.false_eq_true, if_false] at step
            exact reaches_trans step (hin (by simpa [hnv] using hmem))
        · intro hmem
          have hnv : n ≠ value := fun h => hmem (by simp [h])
          have : (n == value) = false := by simp [hnv]
          rw [this] at step
          simp only [Bool.false_eq_true, if_false] at step
          exact reaches_trans step (hout (by simpa [hnv] using hmem))
      · exact trivial_case
    · exact trivial_case
  · rw [errorSpine.eq_2 _ _ _ (fun s n h => hshape ⟨s, n, h⟩)]
    exact trivial_case
termination_by exprSize e
decreasing_by subst_vars; simp only [exprSize, exprSizeList]; omega

theorem foldl_min_le : ∀ (vs : List Int) (a : Int),
    vs.foldl min a ≤ a ∧ ∀ x ∈ vs, vs.foldl min a ≤ x
  | [], a => ⟨Int.le_refl a, by simp⟩
  | v :: vs, a => by
    obtain ⟨h₁, h₂⟩ := foldl_min_le vs (min a v)
    simp only [List.foldl_cons, List.mem_cons]
    refine ⟨by omega, fun x hx => ?_⟩
    rcases hx with rfl | hx
    · omega
    · exact h₂ x hx

theorem le_foldl_max : ∀ (vs : List Int) (a : Int),
    a ≤ vs.foldl max a ∧ ∀ x ∈ vs, x ≤ vs.foldl max a
  | [], a => ⟨Int.le_refl a, by simp⟩
  | v :: vs, a => by
    obtain ⟨h₁, h₂⟩ := le_foldl_max vs (max a v)
    simp only [List.foldl_cons, List.mem_cons]
    refine ⟨by omega, fun x hx => ?_⟩
    rcases hx with rfl | hx
    · omega
    · exact h₂ x hx

theorem coversRange_mem {values : List Int} {low high n : Int} (h : coversRange values low high = true)
    (h₁ : low ≤ n) (h₂ : n ≤ high) : n ∈ values := by
  unfold coversRange at h
  rw [List.all_eq_true] at h
  have hm := h (n - low).toNat (List.mem_range.mpr (by omega))
  rw [show low + ((n - low).toNat : Int) = n by omega] at hm
  simpa using hm

theorem int_min_cases (a b : Int) : min a b ≤ a ∧ min a b ≤ b ∧ (min a b = a ∨ min a b = b) := by
  refine ⟨Int.min_le_left a b, Int.min_le_right a b, ?_⟩
  rw [Int.min_def]; split <;> simp

theorem int_max_cases (a b : Int) : a ≤ max a b ∧ b ≤ max a b ∧ (max a b = a ∨ max a b = b) := by
  refine ⟨Int.le_max_left a b, Int.le_max_right a b, ?_⟩
  rw [Int.max_def]; split <;> simp

theorem rangeRule_rewrites {Γ : List (VarId × Expr)} {scrutinee otherwise out : Expr}
    {t : VarId} {c : Int} (htest : resolvedTagTest Γ scrutinee = some (t, c))
    (hrule : rangeRule Γ t c otherwise = some out) :
    TagRewrites Γ (.Case scrutinee [otherwise, .Error]) out := by
  intro env te hd hs hlow
  obtain ⟨ts, tO, tE, hts, htO, htE, rfl⟩ := lowerTotalExpr_case2_some hlow
  rw [lowerTotalExpr_error] at htE; cases htE
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (resolvedTagTest_bound htest hs hd (by simp [hts]))
  have value : ∀ ρ, FactsHold Produces Γ env ρ → EnvWellFormed env.length ρ →
      ∃ n : Int, ρ.lookup (i + 1) = some (.VCon (.Integer n)) ∧ Halts ρ ts (.VCon (.Bool (n == c))) := by
    intro ρ hF henv
    obtain ⟨i', n, hi', hn, hv⟩ := resolvedTagTest_sound htest hF hd henv hts
    rw [hi] at hi'; cases hi'
    exact ⟨n, hn, hv⟩
  unfold rangeRule at hrule
  split at hrule
  · rename_i low high D hrange
    split at hrule
    · rename_i hcond
      cases hrule
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨first, second, ty₁, ty₂, ty₃, hf, hs', rfl⟩ := rangeOf_some hrange
      rw [lowerTotalExpr_rangeExpr (by rw [envLookupT_congr hf, hi])
        (by rw [envLookupT_congr hs', hi])] at htO
      cases hD : lowerTotalExpr env D with
      | none => rw [hD] at htO; cases htO
      | some tD =>
        rw [hD] at htO; cases htO
        refine ⟨_, by rw [rangeCase_eq, lowerTotalExpr_rangeExpr hi hi, hD]; rfl, ?_⟩
        intro ρ π henv _ _ hF
        obtain ⟨n, hn, hv⟩ := value ρ hF henv
        have step := case_bool_steps (π := π) (a₀ := rangeTerm (i + 1) low high ty₁ ty₂ ty₃ tD)
          (a₁ := .Error) hv
        obtain ⟨hin, hout⟩ := rangeTerm_reaches (π := π) (low := low) (high := high)
          (ty₁ := ty₁) (ty₂ := ty₂) (ty₃ := ty₃) (tD := tD) hn
        obtain ⟨hin', hout'⟩ := rangeTerm_reaches (π := π) (low := min low c) (high := max high c)
          (ty₁ := .AtomicType .TypeInteger) (ty₂ := .AtomicType .TypeBool)
          (ty₃ := .AtomicType .TypeInteger) (tD := tD) hn
        have hmin := int_min_cases low c
        have hmax := int_max_cases high c
        generalize min low c = low' at hin' hout' hmin ⊢
        generalize max high c = high' at hin' hout' hmax ⊢
        by_cases hnc : n = c
        · have : (n == c) = true := by simp [hnc]
          rw [this] at step
          exact obsRefines_of_errors (reaches_trans step (error_reaches π ρ)) (hin' (by omega))
        · have : (n == c) = false := by simp [hnc]
          rw [this] at step
          simp only [Bool.false_eq_true, if_false] at step
          by_cases hr : low ≤ n ∧ n ≤ high
          · exact obsRefines_of_errors (reaches_trans step (hin hr)) (hin' (by omega))
          · exact obsRefines_of_reaches (reaches_trans step (hout hr)) (hout' (by omega))
              (obsRefines_refl _)
    · cases hrule
  · dsimp only at hrule
    split at hrule
    · rename_i hcond
      cases hrule
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨hwide, hcover⟩ := hcond
      obtain ⟨tD, htD, hsem⟩ := errorSpine_sound Γ t otherwise hd hs hi htO
      refine ⟨_, lowerTotalExpr_rangeCase hi htD, ?_⟩
      intro ρ π henv _ _ hF
      obtain ⟨n, hn, hv⟩ := value ρ hF henv
      obtain ⟨hin, hout⟩ := hsem ρ π n hF henv hn
      have step := case_bool_steps (π := π) (a₀ := tO) (a₁ := .Error) hv
      obtain ⟨hin', hout'⟩ := rangeTerm_reaches (π := π)
        (low := (errorSpine Γ t otherwise).1.foldl min c)
        (high := (errorSpine Γ t otherwise).1.foldl max c)
        (ty₁ := .AtomicType .TypeInteger) (ty₂ := .AtomicType .TypeBool)
        (ty₃ := .AtomicType .TypeInteger) (tD := tD) hn
      have hmin := foldl_min_le (errorSpine Γ t otherwise).1 c
      have hmax := le_foldl_max (errorSpine Γ t otherwise).1 c
      by_cases hnc : n = c
      · have : (n == c) = true := by simp [hnc]
        rw [this] at step
        exact obsRefines_of_errors (reaches_trans step (error_reaches π ρ))
          (hin' ⟨by omega, by omega⟩)
      · have : (n == c) = false := by simp [hnc]
        rw [this] at step
        simp only [Bool.false_eq_true, if_false] at step
        by_cases hm : n ∈ (errorSpine Γ t otherwise).1
        · exact obsRefines_of_errors (reaches_trans step (hin hm))
            (hin' ⟨hmin.2 n hm, hmax.2 n hm⟩)
        · refine obsRefines_of_reaches (reaches_trans step (hout hm)) (hout' fun hr => ?_)
            (obsRefines_refl _)
          have := coversRange_mem hcover hr.1 hr.2
          simp only [List.mem_cons] at this
          rcases this with h | h
          · exact hnc h
          · exact hm h
    · cases hrule

theorem tagCaseRule_rewrites {Γ : List (VarId × Expr)} {scrutinee out : Expr}
    {alternatives : List Expr} (h : tagCaseRule Γ scrutinee alternatives = some out) :
    TagRewrites Γ (.Case scrutinee alternatives) out := by
  unfold tagCaseRule at h
  split at h
  · rename_i otherwise matched
    split at h
    · rename_i subject value htest
      split at h
      · rename_i result hint
        cases h
        exact integerCaseRule_rewrites htest hint
      · split at h
        · exact rangeRule_rewrites (by assumption) h
        · cases h
    · cases h
  · cases h

theorem tagCaseRule_getD_rewrites (Γ : List (VarId × Expr)) (scrutinee : Expr)
    (alternatives : List Expr) :
    TagRewrites Γ (.Case scrutinee alternatives)
      ((tagCaseRule Γ scrutinee alternatives).getD (.Case scrutinee alternatives)) := by
  cases h : tagCaseRule Γ scrutinee alternatives with
  | none => exact TagRewrites.refl _ _
  | some out => exact tagCaseRule_rewrites h

/-! ## Congruence -/

theorem TagRewrites.list {Γ : List (VarId × Expr)} :
    ∀ {es es' : List Expr}, ListRel (TagRewrites Γ) es es' →
      ∀ env ts, EnvDistinct env → FactsScoped Γ env → MIR.lowerTotalExprList env es = some ts →
        ∃ ts', MIR.lowerTotalExprList env es' = some ts' ∧
          ListRel (FactRefines env.length (FactsHold Produces Γ env)) ts ts'
  | [], [], _, env, ts, _, _, h => by
    rw [MIR.lowerTotalExprList_nil] at h; cases h
    exact ⟨[], MIR.lowerTotalExprList_nil env, trivial⟩
  | [], _ :: _, h, _, _, _, _, _ => absurd h id
  | _ :: _, [], h, _, _, _, _, _ => absurd h id
  | e :: es, e' :: es', h, env, ts, hd, hs, hlow => by
    rw [MIR.lowerTotalExprList_cons] at hlow
    cases he : lowerTotalExpr env e with
    | none => rw [he] at hlow; cases hlow
    | some te =>
      cases hes : MIR.lowerTotalExprList env es with
      | none => rw [he, hes] at hlow; cases hlow
      | some tes =>
        rw [he, hes] at hlow; cases hlow
        obtain ⟨te', hte', hr⟩ := h.1 env te hd hs he
        obtain ⟨tes', htes', hrs⟩ := TagRewrites.list h.2 env tes hd hs hes
        exact ⟨te' :: tes', by rw [MIR.lowerTotalExprList_cons, hte', htes']; rfl, hr, hrs⟩

theorem TagRewrites.case_alternatives {Γ : List (VarId × Expr)} {s : Expr} {alts alts' : List Expr}
    (h : ListRel (TagRewrites Γ) alts alts') : TagRewrites Γ (.Case s alts) (.Case s alts') := by
  intro env t hd hs hlow
  obtain ⟨ts, talts, hts, htalts, rfl⟩ := lowerTotalExpr_case_some hlow
  obtain ⟨talts', htalts', hr⟩ := TagRewrites.list h env talts hd hs htalts
  refine ⟨.Case ts talts', by rw [MIR.lowerTotalExpr_case_of_list, hts, htalts']; rfl, ?_⟩
  exact factRefines_case (FactRefines.refl _ _ _) hr (MIR.lowerTotalExpr_closedAt hts)
    (lowerTotalExprList_closedAtList htalts)

end Moist.Verified.TagChains
