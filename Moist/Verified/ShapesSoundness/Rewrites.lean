import Moist.Verified.ShapesSoundness.Choices
import Moist.Verified.ShapeFacts.Results
import Moist.Verified.ShapeFacts.Total
import Moist.Verified.MIR.AlphaEqBool

variable [sv : Moist.CEK.SemVariant]

/-! # Local rewrites of the fact-driven simplifier

Each rewrite of `simplifyWalk` and `shapeRewrite` refines its input under the
facts of the walk. Facts record expressions that produced the bound values and
that are fresh for the environment where they were evaluated (`PF`).
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines

/-- Facts of the simplifier: the recorded expression produced the value and
    is fresh for the environment it was evaluated in. -/
def PF (env : List VarId) (ρ : CekEnv) (rhs : Expr) (v : CekValue) : Prop :=
  Produces env ρ rhs v ∧ freshIn env rhs = true

theorem PF_hP : ∀ env ρ rhs v, PF env ρ rhs v → Produces env ρ rhs v ∧ freshIn env rhs = true :=
  fun _ _ _ _ h => h

theorem PF_produces : ∀ env ρ rhs v, PF env ρ rhs v → Produces env ρ rhs v :=
  fun _ _ _ _ h => h.1

theorem FactRel.trans {G : VarId → Prop} {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} {a b c : Expr} (h₁ : FactRel G P Γ a b) (h₂ : FactRel G P Γ b c)
    (hfr : ∀ env, (∀ y ∈ env, G y) → freshIn env a = true → freshIn env b = true) :
    FactRel G P Γ a c := by
  intro env t hG hd hf hk hsc hlow
  obtain ⟨t', hl', r₁⟩ := h₁ env t hG hd hf hk hsc hlow
  obtain ⟨t'', hl'', r₂⟩ := h₂ env t' hG hd (hfr env hG hf) hk hsc hl'
  exact ⟨t'', hl'', r₁.trans r₂⟩

theorem wellSized_of_wellFormed {d : Nat} {ρ : CekEnv} (h : EnvWellFormed d ρ) :
    Semantics.WellSizedEnv d ρ := by
  intro n hn hle
  obtain ⟨v, hv, _⟩ := envWellFormed_lookup d h hn hle
  exact ⟨v, hv⟩

def litBool (value : Bool) : Expr := .Lit (.Bool value, .AtomicType .TypeBool)

theorem lowerTotalExpr_litBool (env : List VarId) (value : Bool) :
    lowerTotalExpr env (litBool value) = some (.Constant (.Bool value, .AtomicType .TypeBool)) :=
  lowerTotalExpr_lit env _ _

theorem PF_litBool (env : List VarId) (ρ : CekEnv) (value : Bool) :
    PF env ρ (litBool value) (.VCon (.Bool value)) :=
  ⟨⟨_, lowerTotalExpr_litBool env value, halts_constant_of _ _⟩, by simp [litBool, freshIn]⟩

/-! ## Case analysis of a Boolean variable -/

/-- The value of a variable that the facts know to be Boolean. -/
theorem var_bool_value {Γ : List (VarId × Expr)} {b : VarId} {env : List VarId} {ρ : CekEnv}
    {i : Nat} (hknown : knownBoolean 64 Γ (.Var b) = true) (hfacts : FactsHold PF Γ env ρ)
    (hd : EnvDistinct env) (hi : envLookupT env b = some i) (henv : EnvWellFormed env.length ρ) :
    ∃ c, ρ.lookup (i + 1) = some (.VCon (.Bool c)) := by
  obtain ⟨w, hw, _⟩ := envWellFormed_lookup env.length henv (n := i + 1) (by omega)
    (by have := envLookupT_bound env b i hi; omega)
  obtain ⟨c, rfl⟩ := knownBoolean_sound PF_hP 64 Γ (.Var b) hknown hfacts hd (by simp [freshIn])
    (by rw [lowerTotalExpr_var, hi]; rfl) (halts_var_of_lookup hw)
  exact ⟨c, hw⟩

/-- In a branch of a case on a Boolean variable the variable holds the branch's
    Boolean. -/
theorem branch_facts {Γ : List (VarId × Expr)} {b : VarId} {env : List VarId} {ρ : CekEnv}
    {i : Nat} {c : Bool} (hfacts : FactsHold PF Γ env ρ) (hi : envLookupT env b = some i)
    (hc : ρ.lookup (i + 1) = some (.VCon (.Bool c))) :
    FactsHold PF ((b, litBool c) :: Γ) env ρ :=
  FactsHold.push_bool hfacts (fun j hj => by rw [hi] at hj; cases hj; exact hc)
    (fun env ρ => PF_litBool env ρ c)

theorem branch_keys {Γ : List (VarId × Expr)} {b : VarId} {env : List VarId} {i : Nat} {c : Bool}
    (hk : KeysBound Γ env) (hi : envLookupT env b = some i) : KeysBound ((b, litBool c) :: Γ) env := by
  intro entry hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · simp [hi]
  · exact hk entry hmem

theorem branch_scoped {Γ : List (VarId × Expr)} {b : VarId} {env : List VarId} {c : Bool}
    (hs : FactsScoped Γ env) : FactsScoped ((b, litBool c) :: Γ) env := by
  intro y entry i hf hl
  by_cases hby : (b == y) = true
  · simp only [List.find?_cons, hby] at hf
    cases hf
    refine ⟨i + 1, by omega, by have := envLookupT_bound env y i hl; omega, ?_⟩
    simp [lowerTotalExpr_litBool]
  · simp only [List.find?_cons, Bool.not_eq_true] at hby hf
    simp only [hby] at hf
    exact hs y entry i hf hl

theorem lowerTotalExpr_case_var {env : List VarId} {b : VarId} {first second : Expr} {t : Term}
    (h : lowerTotalExpr env (.Case (.Var b) [first, second]) = some t) :
    ∃ i tf ts, envLookupT env b = some i ∧ lowerTotalExpr env first = some tf ∧
      lowerTotalExpr env second = some ts ∧ t = .Case (.Var (i + 1)) [tf, ts] := by
  obtain ⟨tsc, tf, ts, hsc, htf, hts, rfl⟩ := lowerTotalExpr_case2_some h
  obtain ⟨i, hi, rfl⟩ := lowerTotalExpr_var_some hsc
  exact ⟨i, tf, ts, hi, htf, hts, rfl⟩

theorem case_var_reaches {ρ : CekEnv} {π : Stack} {i : Nat} {c : Bool} {tf ts : Term}
    (hc : ρ.lookup (i + 1) = some (.VCon (.Bool c))) :
    Reaches (.compute π ρ (.Case (.Var (i + 1)) [tf, ts])) (.compute π ρ (if c then ts else tf)) :=
  case_bool_steps (halts_var_of_lookup hc)

/-- Each branch of a case on a Boolean variable may use the Boolean it
    selects. -/
theorem case_var_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {b : VarId}
    {first second first' second' : Expr} (hknown : knownBoolean 64 Γ (.Var b) = true)
    (h₀ : FactRel G PF ((b, litBool false) :: Γ) first first')
    (h₁ : FactRel G PF ((b, litBool true) :: Γ) second second') :
    FactRel G PF Γ (.Case (.Var b) [first, second]) (.Case (.Var b) [first', second']) := by
  intro env t hG hd hfresh hk hsc hlow
  simp only [freshIn, freshInList, Bool.and_eq_true] at hfresh
  obtain ⟨_, hff, hfs, _⟩ := hfresh
  obtain ⟨i, tf, ts, hi, htf, hts, rfl⟩ := lowerTotalExpr_case_var hlow
  obtain ⟨tf', htf', hrf⟩ := h₀ env tf hG hd hff (branch_keys hk hi) (branch_scoped hsc) htf
  obtain ⟨ts', hts', hrs⟩ := h₁ env ts hG hd hfs (branch_keys hk hi) (branch_scoped hsc) hts
  refine ⟨.Case (.Var (i + 1)) [tf', ts'], ?_, ?_⟩
  · rw [MIR.lowerTotalExpr_case_of_list, lowerTotalExpr_var, hi]
    simp [MIR.lowerTotalExprList_cons, MIR.lowerTotalExprList_nil, htf', hts']
  · intro ρ π henv hlen hπ hF
    obtain ⟨c, hc⟩ := var_bool_value hknown hF hd hi henv
    refine obsRefines_of_reaches (case_var_reaches hc) (case_var_reaches hc) ?_
    cases c
    · exact hrf ρ π henv hlen hπ (branch_facts hF hi hc)
    · exact hrs ρ π henv hlen hπ (branch_facts hF hi hc)

/-- Branches that agree after simplification merge. -/
theorem case_var_merge_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {b : VarId}
    {first second first' second' : Expr} (hknown : knownBoolean 64 Γ (.Var b) = true)
    (h₀ : FactRel G PF ((b, litBool false) :: Γ) first first')
    (h₁ : FactRel G PF ((b, litBool true) :: Γ) second second')
    (halpha : alphaEq first' second' = true) :
    FactRel G PF Γ (.Case (.Var b) [first, second]) first' := by
  intro env t hG hd hfresh hk hsc hlow
  simp only [freshIn, freshInList, Bool.and_eq_true] at hfresh
  obtain ⟨_, hff, hfs, _⟩ := hfresh
  obtain ⟨i, tf, ts, hi, htf, hts, rfl⟩ := lowerTotalExpr_case_var hlow
  obtain ⟨tf', htf', hrf⟩ := h₀ env tf hG hd hff (branch_keys hk hi) (branch_scoped hsc) htf
  obtain ⟨ts', hts', hrs⟩ := h₁ env ts hG hd hfs (branch_keys hk hi) (branch_scoped hsc) hts
  have heq : ts' = tf' := by
    rw [← MIR.alphaEq_lowerTotalExpr_eq halpha env, htf'] at hts'
    cases hts'; rfl
  subst heq
  refine ⟨ts', htf', ?_⟩
  intro ρ π henv hlen hπ hF
  obtain ⟨c, hc⟩ := var_bool_value hknown hF hd hi henv
  refine obsRefines_of_reaches (case_var_reaches hc) (reaches_refl _) ?_
  cases c
  · exact hrf ρ π henv hlen hπ (branch_facts hF hi hc)
  · exact hrs ρ π henv hlen hπ (branch_facts hF hi hc)

/-- A case on a variable whose facts resolve to a Boolean literal selects its
    branch. -/
theorem case_var_literal_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {b : VarId}
    {first second : Expr} {value : Bool}
    (hres : resolveHead 64 Γ (.Var b) = .Lit (.Bool value, .AtomicType .TypeBool)) :
    FactRel G PF Γ (.Case (.Var b) [first, second]) (if value then second else first) := by
  intro env t hG hd hfresh hk hsc hlow
  obtain ⟨i, tf, ts, hi, htf, hts, rfl⟩ := lowerTotalExpr_case_var hlow
  refine ⟨if value then ts else tf, by cases value <;> simp [htf, hts], ?_⟩
  intro ρ π henv hlen hπ hF
  obtain ⟨w, hw, _⟩ := envWellFormed_lookup env.length henv (n := i + 1) (by omega)
    (by have := envLookupT_bound env b i hi; omega)
  have hval := resolveHead_bool PF_produces 64 Γ (.Var b) hres hF hd (by rw [lowerTotalExpr_var, hi]; rfl)
    (halts_var_of_lookup hw)
  subst hval
  exact obsRefines_of_reaches (case_var_reaches hw) (reaches_refl _) (obsRefines_refl _)

/-! ## Cases on Booleans -/

/-- `ifThenElse` on a known Boolean between two pure branches is a case. -/
theorem ite_case_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {cond wt wf : Expr}
    (hknown : knownBoolean 64 Γ cond = true) (hpt : isPure wt = true) (hpf : isPure wf = true) :
    FactRel G PF Γ (.App (.App (.App (.Force (.Builtin .IfThenElse)) cond) wt) wf)
      (.Case cond [wf, wt]) := by
  intro env t hG hd hfresh hk hsc hlow
  simp only [freshIn, Bool.and_eq_true] at hfresh
  obtain ⟨⟨⟨_, hfc⟩, _⟩, _⟩ := hfresh
  obtain ⟨t₁, ttf, ht₁, httf, rfl⟩ := lowerTotalExpr_app_some hlow
  obtain ⟨t₂, ttt, ht₂, httt, rfl⟩ := lowerTotalExpr_app_some ht₁
  obtain ⟨t₃, ttc, ht₃, httc, rfl⟩ := lowerTotalExpr_app_some ht₂
  obtain ⟨t₄, ht₄, rfl⟩ := lowerTotalExpr_force_some ht₃
  rw [lowerTotalExpr_builtin] at ht₄; cases ht₄
  refine ⟨.Case ttc [ttf, ttt], ?_, ?_⟩
  · rw [MIR.lowerTotalExpr_case_of_list, httc]
    simp [MIR.lowerTotalExprList_cons, MIR.lowerTotalExprList_nil, httf, httt]
  · intro ρ π henv hlen hπ hF
    have hws := wellSized_of_wellFormed henv
    obtain ⟨vt, hvt⟩ := Purity.isPure_halts (expandFix wt) ttt env ρ (Purity.isPure_expandFix wt hpt) httt hws
    obtain ⟨vf, hvf⟩ := Purity.isPure_halts (expandFix wf) ttf env ρ (Purity.isPure_expandFix wf hpf) httf hws
    refine obsRefines_of_reaches (reaches_of_steps 7 rfl) (reaches_of_steps 1 rfl) ?_
    refine obsRefines_of_continuation ?_
    intro v hv
    obtain ⟨c, rfl⟩ := knownBoolean_sound PF_hP 64 Γ cond hknown hF hd hfc httc hv
    have hsrc : Reaches (.ret (.funV (.VBuiltin .IfThenElse [] (.more .argV (.more .argV (.one .argV)))) ::
        .arg ttt ρ :: .arg ttf ρ :: π) (.VCon (.Bool c))) (.ret π (if c then vt else vf)) := by
      refine reaches_trans (reaches_of_steps 2 rfl) ?_
      refine reaches_trans (halts_on_stack hvt _) ?_
      refine reaches_trans (reaches_of_steps 2 rfl) ?_
      refine reaches_trans (halts_on_stack hvf _) ?_
      refine ⟨1, ?_⟩
      cases c <;> rfl
    have htgt : Reaches (.ret (.caseScrutinee [ttf, ttt] ρ :: π) (.VCon (.Bool c)))
        (.ret π (if c then vt else vf)) := by
      cases c
      · exact reaches_trans (reaches_of_steps 1 rfl) (halts_on_stack hvf π)
      · exact reaches_trans (reaches_of_steps 1 rfl) (halts_on_stack hvt π)
    exact obsRefines_of_reaches hsrc htgt (obsRefines_refl _)

theorem mapM_delayBody : ∀ {alts bodies : List Expr}, alts.mapM delayBody = some bodies →
    alts = bodies.map .Delay
  | [], bodies, h => by simp at h; subst h; rfl
  | a :: as, bodies, h => by
    rw [List.mapM_cons] at h
    cases ha : delayBody a with
    | none => simp [ha] at h
    | some b =>
      cases has : as.mapM delayBody with
      | none => simp [ha, has] at h
      | some bs =>
        simp [ha, has] at h
        subst h
        have : a = .Delay b := by
          cases a <;> simp [delayBody] at ha
          subst ha; rfl
        rw [this, mapM_delayBody has]; rfl

theorem lowerTotalExprList_map_delay (env : List VarId) : ∀ (bodies : List Expr),
    MIR.lowerTotalExprList env (bodies.map .Delay) =
      (MIR.lowerTotalExprList env bodies).map (·.map .Delay)
  | [] => by simp [MIR.lowerTotalExprList_nil]
  | b :: bs => by
    simp only [List.map_cons, MIR.lowerTotalExprList_cons, MIR.lowerTotalExpr_delay,
      lowerTotalExprList_map_delay env bs]
    cases lowerTotalExpr env b <;> cases MIR.lowerTotalExprList env bs <;> rfl

theorem bool_case_frames (L : List Term) (ρ : CekEnv) (s : Stack) (c : Bool) :
    (2 < L.length ∧ step (.ret (.caseScrutinee L ρ :: s) (.VCon (.Bool c))) = .error) ∨
    (¬ 2 < L.length ∧ L[if c then 1 else 0]? = none ∧
      step (.ret (.caseScrutinee L ρ :: s) (.VCon (.Bool c))) = .error) ∨
    (∃ alt, ¬ 2 < L.length ∧ L[if c then 1 else 0]? = some alt ∧
      step (.ret (.caseScrutinee L ρ :: s) (.VCon (.Bool c))) = .compute s ρ alt) := by
  by_cases hl : 2 < L.length
  · left; refine ⟨hl, ?_⟩
    cases c <;> simp [step, constToTagAndFields, hl]
  · right
    cases hget : L[if c then 1 else 0]? with
    | none =>
      left; refine ⟨hl, rfl, ?_⟩
      cases c <;> simp_all [step, constToTagAndFields]
    | some alt =>
      right; refine ⟨alt, hl, rfl, ?_⟩
      cases c <;> simp_all [step, constToTagAndFields]

/-- Forcing a case on a known Boolean whose branches are all delayed is a case
    on the delayed bodies. -/
theorem force_case_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {scrut : Expr}
    {alts bodies : List Expr} (hknown : knownBoolean 64 Γ scrut = true)
    (hbodies : alts.mapM delayBody = some bodies) :
    FactRel G PF Γ (.Force (.Case scrut alts)) (.Case scrut bodies) := by
  have halts := mapM_delayBody hbodies
  subst halts
  intro env t hG hd hfresh hk hsc hlow
  simp only [freshIn, Bool.and_eq_true] at hfresh
  obtain ⟨tc, htc, rfl⟩ := lowerTotalExpr_force_some hlow
  obtain ⟨ts, talts, hts, htalts, rfl⟩ := lowerTotalExpr_case_some htc
  rw [lowerTotalExprList_map_delay] at htalts
  cases htbs : MIR.lowerTotalExprList env bodies with
  | none => rw [htbs] at htalts; cases htalts
  | some tbs =>
    rw [htbs] at htalts; cases htalts
    refine ⟨.Case ts tbs, by rw [MIR.lowerTotalExpr_case_of_list, hts, htbs]; rfl, ?_⟩
    intro ρ π henv hlen hπ hF
    refine obsRefines_of_reaches (reaches_of_steps 2 rfl) (reaches_of_steps 1 rfl) ?_
    refine obsRefines_of_continuation ?_
    intro v hv
    obtain ⟨c, rfl⟩ := knownBoolean_sound PF_hP 64 Γ scrut hknown hF hd hfresh.1 hts hv
    have hlen' : (tbs.map Term.Delay).length = tbs.length := List.length_map _
    rcases bool_case_frames tbs ρ π c with ⟨hl, ht⟩ | ⟨hl, hget, ht⟩ | ⟨alt, hl, hget, ht⟩
    · rcases bool_case_frames (tbs.map Term.Delay) ρ (.force :: π) c with
        ⟨_, hs⟩ | ⟨hl', _, _⟩ | ⟨_, hl', _, _⟩
      · exact obsRefines_of_reaches (reaches_of_steps 1 hs) (reaches_of_steps 1 ht) (obsRefines_refl _)
      · exact absurd (by rw [hlen']; exact hl) hl'
      · exact absurd (by rw [hlen']; exact hl) hl'
    · rcases bool_case_frames (tbs.map Term.Delay) ρ (.force :: π) c with
        ⟨hl', _⟩ | ⟨_, _, hs⟩ | ⟨_, _, hget', _⟩
      · exact absurd (by rw [← hlen']; exact hl') hl
      · exact obsRefines_of_reaches (reaches_of_steps 1 hs) (reaches_of_steps 1 ht) (obsRefines_refl _)
      · rw [List.getElem?_map, hget] at hget'; cases hget'
    · rcases bool_case_frames (tbs.map Term.Delay) ρ (.force :: π) c with
        ⟨hl', _⟩ | ⟨_, hget', _⟩ | ⟨alt', _, hget', hs⟩
      · exact absurd (by rw [← hlen']; exact hl') hl
      · rw [List.getElem?_map, hget] at hget'; cases hget'
      · rw [List.getElem?_map, hget] at hget'
        cases hget'
        refine obsRefines_of_reaches (reaches_trans (reaches_of_steps 1 hs) (reaches_of_steps 2 rfl))
          (reaches_of_steps 1 ht) (obsRefines_refl _)

theorem bool_case_same {ρ : CekEnv} {π : Stack} {tf : Term} (c : Bool) :
    step (.ret (.caseScrutinee [tf, tf] ρ :: π) (.VCon (.Bool c))) = .compute π ρ tf := by
  rcases bool_case_frames [tf, tf] ρ π c with ⟨hl, _⟩ | ⟨_, hget, _⟩ | ⟨alt, _, hget, ht⟩
  · simp at hl
  · cases c <;> simp at hget
  · cases c <;> simp at hget <;> subst hget <;> exact ht

theorem lowerTotalExpr_case_alpha {env : List VarId} {scrut first second : Expr} {t : Term}
    (halpha : alphaEq first second = true)
    (h : lowerTotalExpr env (.Case scrut [first, second]) = some t) :
    ∃ ts tf, lowerTotalExpr env scrut = some ts ∧ lowerTotalExpr env first = some tf ∧
      t = .Case ts [tf, tf] := by
  obtain ⟨ts, tf, tsd, hts, htf, htsd, rfl⟩ := lowerTotalExpr_case2_some h
  rw [← MIR.alphaEq_lowerTotalExpr_eq halpha env, htf] at htsd
  cases htsd
  exact ⟨ts, tf, hts, htf, rfl⟩

/-- A case on a known Boolean whose branches agree, with a scrutinee that
    returns, is its first branch. -/
theorem case_alpha_total_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {scrut first second : Expr}
    (hknown : knownBoolean 64 Γ scrut = true) (htotal : totalWithFacts 64 Γ scrut = true)
    (halpha : alphaEq first second = true) :
    FactRel G PF Γ (.Case scrut [first, second]) first := by
  intro env t hG hd hfresh hk hsc hlow
  simp only [freshIn, Bool.and_eq_true] at hfresh
  obtain ⟨ts, tf, hts, htf, rfl⟩ := lowerTotalExpr_case_alpha halpha hlow
  refine ⟨tf, htf, ?_⟩
  intro ρ π henv hlen hπ hF
  obtain ⟨v, hv⟩ := totalWithFacts_sound PF_hP 64 Γ scrut htotal hF hd hfresh.1
    (wellSized_of_wellFormed henv) hts
  obtain ⟨c, rfl⟩ := knownBoolean_sound PF_hP 64 Γ scrut hknown hF hd hfresh.1 hts hv
  refine obsRefines_of_reaches ?_ (reaches_refl _) (obsRefines_refl _)
  exact reaches_trans (reaches_of_steps 1 rfl)
    (reaches_trans (halts_on_stack hv _) (reaches_of_steps 1 (bool_case_same c)))

/-- A case on a known Boolean whose branches agree evaluates the scrutinee
    and then its first branch. -/
theorem case_alpha_checked_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)}
    {scrut first second : Expr} (checked : VarId)
    (hknown : knownBoolean 64 Γ scrut = true) (halpha : alphaEq first second = true)
    (hbig : maxUidExpr first < checked.uid) :
    FactRel G PF Γ (.Case scrut [first, second]) (.Let [(checked, scrut, false)] first) := by
  intro env t hG hd hfresh hk hsc hlow
  simp only [freshIn, Bool.and_eq_true] at hfresh
  obtain ⟨ts, tf, hts, htf, rfl⟩ := lowerTotalExpr_case_alpha halpha hlow
  have hunused : (freeVars first).contains checked = false := maxUidExpr_fresh _ _ hbig
  have htfs : lowerTotalExpr (checked :: env) first = some (renameTerm (shiftRename 1) tf) := by
    rw [MIR.lowerTotalExpr_prepend_unused env checked first hunused, htf]; rfl
  refine ⟨.Apply (.Lam 0 (renameTerm (shiftRename 1) tf)) ts, ?_, ?_⟩
  · rw [lowerTotalExpr_let_single, hts, htfs]; rfl
  · intro ρ π henv hlen hπ hF
    have closed := MIR.lowerTotalExpr_closedAt htf
    refine obsRefines_of_reaches (reaches_of_steps 1 rfl) (reaches_of_steps 3 rfl) ?_
    refine obsRefines_of_continuation ?_
    intro v hv
    obtain ⟨c, rfl⟩ := knownBoolean_sound PF_hP 64 Γ scrut hknown hF hd hfresh.1 hts hv
    exact obsRefines_of_reaches (reaches_of_steps 1 (bool_case_same c)) (reaches_of_steps 1 rfl)
      (obsEq_shift _ henv hπ closed).1

/-! ## Data round trips -/

/-- A builtin undoing the conversion that produced a checked value returns the
    original value. -/
def RoundTrip (outer inner : BuiltinFun) : Prop :=
  ∀ vo wc, evalBuiltin inner [vo] = some wc → evalBuiltin outer [wc] = some vo

theorem roundTrip_IData : RoundTrip .IData .UnIData := by
  intro vo wc h
  obtain ⟨c, r, rfl, hc, rfl⟩ := evalBuiltin_single (by decide) h
  cases c <;> (try cases hc)
  rename_i d
  cases d <;> cases hc
  rfl

theorem roundTrip_UnIData : RoundTrip .UnIData .IData := by
  intro vo wc h
  obtain ⟨c, r, rfl, hc, rfl⟩ := evalBuiltin_single (by decide) h
  cases c <;> (try cases hc)
  rfl

theorem roundTrip_BData : RoundTrip .BData .UnBData := by
  intro vo wc h
  obtain ⟨c, r, rfl, hc, rfl⟩ := evalBuiltin_single (by decide) h
  cases c <;> (try cases hc)
  rename_i d
  cases d <;> cases hc
  rfl

theorem roundTrip_UnBData : RoundTrip .UnBData .BData := by
  intro vo wc h
  obtain ⟨c, r, rfl, hc, rfl⟩ := evalBuiltin_single (by decide) h
  cases c <;> (try cases hc)
  rfl

theorem roundTrip_ListData : RoundTrip .ListData .UnListData := by
  intro vo wc h
  obtain ⟨c, r, rfl, hc, rfl⟩ := evalBuiltin_single (by decide) h
  cases c <;> (try cases hc)
  rename_i d
  cases d <;> cases hc
  rfl

theorem roundTrip_MapData : RoundTrip .MapData .UnMapData := by
  intro vo wc h
  obtain ⟨c, r, rfl, hc, rfl⟩ := evalBuiltin_single (by decide) h
  cases c <;> (try cases hc)
  rename_i d
  cases d <;> cases hc
  rfl

theorem roundTrip_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {outer inner : BuiltinFun}
    {c o : VarId} (hres : resolveHead 64 Γ (.Var c) = .App (.Builtin inner) (.Var o))
    (hinner : expectedArgs inner = .one .argV) (houter : expectedArgs outer = .one .argV)
    (hrt : RoundTrip outer inner) :
    FactRel G PF Γ (.App (.Builtin outer) (.Var c)) (.Var o) := by
  intro env t hG hd hfresh hk hsc hlow
  obtain ⟨tb, tc, htb, htc, rfl⟩ := lowerTotalExpr_app_some hlow
  rw [lowerTotalExpr_builtin] at htb; cases htb
  obtain ⟨ic, hic, rfl⟩ := lowerTotalExpr_var_some htc
  have hob := resolveHead_app_var_bound 64 Γ (.Var c) hres hsc hd (by rw [htc]; rfl)
  obtain ⟨io, hio⟩ := Option.isSome_iff_exists.mp hob
  refine ⟨.Var (io + 1), by rw [lowerTotalExpr_var, hio]; rfl, ?_⟩
  intro ρ π henv hlen hπ hF
  obtain ⟨wc, hwc, _⟩ := envWellFormed_lookup env.length henv (n := ic + 1) (by omega)
    (by have := envLookupT_bound env c ic hic; omega)
  obtain ⟨vo, hvo, _⟩ := envWellFormed_lookup env.length henv (n := io + 1) (by omega)
    (by have := envLookupT_bound env o io hio; omega)
  have hun := (resolveHead_unary 64 Γ (.Var c) hres (b := inner) (by simp [forcedBuiltin, hinner])
    (hF.mono PF_produces) hd htc hio hvo).1 wc
  have heval := hrt vo wc (hun.mp (halts_var_of_lookup hwc))
  have hsrc : Reaches (.compute π ρ (.Apply (.Builtin outer) (.Var (ic + 1)))) (.ret π vo) := by
    have h4 : steps 4 (.compute π ρ (.Apply (.Builtin outer) (.Var (ic + 1)))) =
        .ret (.funV (.VBuiltin outer [] (expectedArgs outer)) :: π) wc := by
      simp [steps, step, hwc]
    refine reaches_trans (reaches_of_steps 4 h4) ⟨1, ?_⟩
    simp [steps, step, houter, heval, ExpectedArgs.head, ExpectedArgs.tail]
  exact obsRefines_of_reaches hsrc (reaches_of_steps 1 (by simp [steps, step, hvo]))
    (obsRefines_refl _)

end Moist.Verified.ShapeFacts
