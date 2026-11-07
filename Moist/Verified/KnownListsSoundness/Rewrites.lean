import Moist.Verified.KnownListsSoundness.Relation
import Moist.Verified.KnownListsSoundness.Calls
import Moist.Verified.CheckedBranchesSoundness.Builtins

/-! # Known lists and list `case`s

`knownListValue` is sound: under realized facts, an accepted expression
returns, whenever it halts, a plain, data or data-pair list. On such a value
a `nullList` discriminator followed by a one-alternative list `case` selects
the same alternative as a single two-alternative list `case`
(`KnownRel.nullFuse`), and the tail bound by a `case` on a known list is a
list (`KnownRel.listCase`).
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines

theorem unMapData_result {vs : List CekValue} {v : CekValue} (hlen : vs.length = 1)
    (h : evalBuiltin .UnMapData vs = some v) : ListValue v := by
  obtain ⟨w, rfl⟩ := single_of_length hlen
  obtain ⟨c, r, rfl, hc, rfl⟩ := evalBuiltin_single (by decide) h
  cases c <;> (try cases hc)
  rename_i d
  cases d <;> cases hc
  trivial

theorem knownListValue_sound :
    ∀ (n : Nat) (Γ : List (VarId × Expr)) (L : List VarId) (e : Expr) {env : List VarId}
      {ρ : CekEnv} {t : Term} {v : CekValue},
      knownListValue n Γ L e = true → FactsHold Produces Γ env ρ → ListsHold L env ρ →
      EnvDistinct env → lowerTotalExpr env e = some t → Halts ρ t v → ListValue v := by
  intro n
  induction n with
  | zero => intro Γ L e env ρ t v h; simp [knownListValue] at h
  | succ n ih =>
    intro Γ L e env ρ t v h hfacts hlists hd hlow hv
    cases e with
    | Var x =>
      simp only [knownListValue, Bool.or_eq_true] at h
      rcases h with hx | h
      · obtain ⟨i, hi, rfl⟩ := lowerTotalExpr_var_some hlow
        obtain ⟨w, hw, hlw⟩ := hlists x hx i hi
        have := halts_var hv
        rw [hw] at this; cases this
        exact hlw
      · cases hf : Γ.find? (fun entry => entry.1 == x) with
        | none => rw [hf] at h; cases h
        | some entry =>
          rw [hf] at h
          obtain ⟨k, _, hp, hfacts', hd'⟩ := fact_of_var hfacts hd hf hlow hv
          obtain ⟨t', ht', hv'⟩ := hp
          exact ih Γ L entry.2 (by simpa using h) hfacts' (hlists.drop hd k) hd' ht' hv'
    | Lit lit =>
      obtain ⟨c, ty⟩ := lit
      rw [lowerTotalExpr_lit] at hlow; cases hlow
      rw [halts_constant hv]
      cases c <;> try trivial
      all_goals cases ty <;> simp_all [knownListValue]
    | App f a =>
      simp only [knownListValue] at h
      obtain ⟨tf, ta, htf, hta, rfl⟩ := lowerTotalExpr_app_some hlow
      obtain ⟨wf, wa, hwf, hwa, rest⟩ := halts_apply hv
      split at h
      · rename_i hhead
        have hstate := resolveHead_protocol (fun _ _ _ _ h => h) n Γ f (b := .UnListData)
          (by rw [hhead]; rfl) hfacts hd htf hwf
        obtain ⟨args, hlen, heval⟩ := saturated_apply hstate rest
        exact unListData_result hlen heval
      · rename_i hhead
        have hstate := resolveHead_protocol (fun _ _ _ _ h => h) n Γ f (b := .UnMapData)
          (by rw [hhead]; rfl) hfacts hd htf hwf
        obtain ⟨args, hlen, heval⟩ := saturated_apply hstate rest
        exact unMapData_result hlen heval
      · rename_i hhead
        have hstate := resolveHead_protocol (fun _ _ _ _ h => h) n Γ f (b := .TailList)
          (by rw [hhead]; rfl) hfacts hd htf hwf
        obtain ⟨args, hlen, heval⟩ := saturated_apply hstate rest
        exact tailList_result hlen heval
      · rename_i hhead
        have hstate := resolveHead_protocol (fun _ _ _ _ h => h) n Γ f (b := .SndPair)
          (by rw [hhead]; rfl) hfacts hd htf hwf
        obtain ⟨args, hlen, heval⟩ := saturated_apply hstate rest
        have hpair := constructorPair_sound (fun _ _ _ _ h => h) n Γ a h hfacts hd hta hwa
        have h1 : valueArity (expectedArgs .SndPair) = 1 := rfl
        rw [h1] at hlen
        have hargs : args = [] := by
          cases args with
          | nil => rfl
          | cons _ _ => simp at hlen
        subst hargs
        exact sndPair_result hlen (by simpa using hpair) heval
      · cases h
    | _ => simp [knownListValue] at h

theorem listKnown_sound {Γ : List (VarId × Expr)} {L : List VarId} {e : Expr} {env : List VarId}
    {ρ : CekEnv} {t : Term} {v : CekValue} (h : listKnown Γ L e = true)
    (hF : KnownFacts Γ L env ρ) (hd : EnvDistinct env) (hlow : lowerTotalExpr env e = some t)
    (hv : Halts ρ t v) : ListValue v :=
  knownListValue_sound 64 Γ L e h hF.1 hF.2 hd hlow hv

/-- The value of a variable accepted by `listKnown` is a list. -/
theorem listKnown_var {Γ : List (VarId × Expr)} {L : List VarId} {l : VarId} {env : List VarId}
    {ρ : CekEnv} {il : Nat} (h : listKnown Γ L (.Var l) = true) (hF : KnownFacts Γ L env ρ)
    (hd : EnvDistinct env) (hil : envLookupT env l = some il) (henv : EnvWellFormed env.length ρ) :
    ∃ v, ρ.lookup (il + 1) = some v ∧ ListValue v := by
  have hil_lt := Moist.MIR.envLookupT_bound env l il hil
  obtain ⟨v, hv, _⟩ := envWellFormed_lookup env.length henv (n := il + 1) (by omega) (by omega)
  exact ⟨v, hv, listKnown_sound h hF hd (by rw [lowerTotalExpr_var, hil]; rfl) (halts_var_of_lookup hv)⟩

/-! ## List `case`s on known lists -/

open Moist.Verified.KnownLists (listCase_dispatch listValue_vcon)

/-- The cons alternative of a list `case` binds a head and a list tail. -/
theorem consAlt_facts {Γ : List (VarId × Expr)} {L env : List VarId} {ρ : CekEnv} {h t : VarId}
    {c : Const} {tl : CekValue} (hF : KnownFacts Γ L env ρ) (hn : NamesBound L env)
    (hk : KeysBound Γ env) (hh : (envLookupT env h).isNone = true)
    (ht : (envLookupT (h :: env) t).isNone = true) (htl : ListValue tl) :
    KnownFacts Γ (t :: L) (t :: h :: env) ((ρ.extend (.VCon c)).extend tl) := by
  have hnh := find?_none_of_unbound hk hh
  have hnt := find?_none_of_unbound (hk.cons h) ht
  have h₁ := hF.extend (.VCon c) hn hh hnh
  refine ⟨(h₁.extend tl (hn.cons h) ht hnt).1, ?_⟩
  exact h₁.2.push (hn.cons h) ht htl

theorem consAlt_env {env : List VarId} {ρ : CekEnv} {c : Const} {tl : CekValue}
    (henv : EnvWellFormed env.length ρ) (hlen : env.length ≤ ρ.length) (htl : ListValue tl) :
    EnvWellFormed (env.length + 2) ((ρ.extend (.VCon c)).extend tl) ∧
      env.length + 2 ≤ ((ρ.extend (.VCon c)).extend tl).length := by
  obtain ⟨c', rfl⟩ := listValue_vcon htl
  have h₁ := envWellFormed_extend env.length henv hlen (.vcon c)
  have hlen₁ : env.length + 1 ≤ (ρ.extend (.VCon c)).length := by
    simp [CekEnv.extend, CekEnv.length]; omega
  refine ⟨envWellFormed_extend (env.length + 1) h₁ hlen₁ (.vcon c'), ?_⟩
  simp [CekEnv.extend, CekEnv.length]; omega

theorem case_var_steps {π : Stack} {ρ : CekEnv} {n : Nat} {v : CekValue} (hv : ρ.lookup n = some v)
    (alts : List Term) :
    steps 2 (.compute π ρ (.Case (.Var n) alts)) = .ret (.caseScrutinee alts ρ :: π) v := by
  simp [steps, step, hv]

theorem consAlt_steps (π : Stack) (ρ : CekEnv) (hv tv : CekValue) (b : Term) :
    steps 4 (.compute ([Frame.applyArg hv, Frame.applyArg tv] ++ π) ρ (.Lam 0 (.Lam 0 b))) =
      .compute π ((ρ.extend hv).extend tv) b := by
  cases hv <;> cases tv <;> rfl

theorem lowerTotalExpr_consAlt {env : List VarId} {h t : VarId} {C : Expr} {tA : Term}
    (hA : lowerTotalExpr env (.Lam h (.Lam t C)) = some tA) :
    ∃ tC, lowerTotalExpr (t :: h :: env) C = some tC ∧ tA = .Lam 0 (.Lam 0 tC) := by
  obtain ⟨tX, htX, rfl⟩ := lowerTotalExpr_lam_some hA
  obtain ⟨tC, htC, rfl⟩ := lowerTotalExpr_lam_some htX
  exact ⟨tC, htC, rfl⟩

theorem lowerTotalExpr_consAlt_of {env : List VarId} {h t : VarId} {C : Expr} {tC : Term}
    (htC : lowerTotalExpr (t :: h :: env) C = some tC) :
    lowerTotalExpr env (.Lam h (.Lam t C)) = some (.Lam 0 (.Lam 0 tC)) := by
  rw [MIR.lowerTotalExpr_lam, MIR.lowerTotalExpr_lam, htC]; rfl

/-- The cons alternative under list facts for the tail. -/
theorem consAlt_rel {Γ : List (VarId × Expr)} {L : List VarId} {h t : VarId} {C C' : Expr}
    (hC : KnownRel Γ (t :: L) C C') {env : List VarId} {tC : Term} (hd : EnvDistinct env)
    (hk : KeysBound Γ env) (hs : FactsScoped Γ env) (hn : NamesBound L env)
    (hh : (envLookupT env h).isNone = true) (ht : (envLookupT (h :: env) t).isNone = true)
    (hfC : freshIn (t :: h :: env) C = true) (htC : lowerTotalExpr (t :: h :: env) C = some tC) :
    ∃ tC', lowerTotalExpr (t :: h :: env) C' = some tC' ∧
      FactRefines (env.length + 2) (KnownFacts Γ (t :: L) (t :: h :: env)) tC tC' := by
  obtain ⟨hd₁, hk₁, hs₁, _⟩ := enter_binder hd hk hs hh
  obtain ⟨hd₂, hk₂, hs₂, _⟩ := enter_binder hd₁ hk₁ hs₁ ht
  have hn₂ : NamesBound (t :: L) (t :: h :: env) :=
    ((hn.cons h).cons t).add (by simp [envLookupT_cons, varId_beq_self])
  obtain ⟨tC', htC', hr⟩ := hC (t :: h :: env) tC hd₂ hfC hk₂ hs₂ hn₂ htC
  exact ⟨tC', htC', by simpa using hr⟩

theorem reaches_self (s : State) : Reaches s s := ⟨0, rfl⟩

theorem lowerList_length {env : List VarId} :
    ∀ {es : List Expr} {ts : List Term}, MIR.lowerTotalExprList env es = some ts →
      ts.length = es.length
  | [], ts, h => by rw [MIR.lowerTotalExprList_nil] at h; cases h; rfl
  | e :: es, ts, h => by
    rw [MIR.lowerTotalExprList_cons] at h
    cases he : lowerTotalExpr env e with
    | none => rw [he] at h; cases h
    | some te =>
      cases hes : MIR.lowerTotalExprList env es with
      | none => rw [he, hes] at h; cases h
      | some tes =>
        rw [he, hes] at h; cases h
        simp [lowerList_length hes]

/-- A list either is non-empty, `nullList` returns `false` and a `case`
    passes a head and a list tail to its first alternative, or it is empty,
    `nullList` returns `true` and a `case` selects the second alternative. -/
theorem listShape {v : CekValue} (hv : ListValue v) :
    (∃ c tl, ListValue tl ∧ nullResult v = some false ∧ ∀ (π : Stack) (ρ : CekEnv) (alts : List Term),
      step (.ret (.caseScrutinee alts ρ :: π) v) =
        if alts.length > 2 then .error else
          match alts[0]? with
          | some alt => .compute ([Frame.applyArg (.VCon c), Frame.applyArg tl] ++ π) ρ alt
          | none => .error) ∨
    (nullResult v = some true ∧ ∀ (π : Stack) (ρ : CekEnv) (alts : List Term),
      step (.ret (.caseScrutinee alts ρ :: π) v) =
        if alts.length > 2 then .error else
          match alts[1]? with
          | some alt => .compute π ρ alt
          | none => .error) := by
  rcases listCase_dispatch hv with ⟨c, tl, htl, hd⟩ | hd
  · refine .inl ⟨c, tl, htl, ?_, hd⟩
    obtain ⟨c', rfl⟩ := listValue_vcon hv
    have := hd [] .nil [.Error]
    cases c' with
    | ConstList xs => cases xs <;> simp_all [step, constToTagAndFields, nullResult]
    | ConstDataList xs => cases xs <;> simp_all [step, constToTagAndFields, nullResult]
    | ConstPairDataList xs => cases xs <;> simp_all [step, constToTagAndFields, nullResult]
    | _ => exact absurd hv id
  · refine .inr ⟨?_, hd⟩
    obtain ⟨c', rfl⟩ := listValue_vcon hv
    have := hd [] .nil [.Error, .Error]
    cases c' with
    | ConstList xs => cases xs <;> simp_all [step, constToTagAndFields, nullResult]
    | ConstDataList xs => cases xs <;> simp_all [step, constToTagAndFields, nullResult]
    | ConstPairDataList xs => cases xs <;> simp_all [step, constToTagAndFields, nullResult]
    | _ => exact absurd hv id

theorem KnownRel.listCase {Γ : List (VarId × Expr)} {L : List VarId} {l h t : VarId}
    {C C' : Expr} {rest rest' : List Expr}
    (hl : listKnown Γ L (.Var l) = true) (hC : KnownRel Γ (t :: L) C C')
    (hrest : ListRel (KnownRel Γ L) rest rest') :
    KnownRel Γ L (.Case (.Var l) (.Lam h (.Lam t C) :: rest))
      (.Case (.Var l) (.Lam h (.Lam t C') :: rest')) := by
  intro env t₀ hd hfresh hk hs hn hlow
  simp only [freshIn, freshInList, Bool.and_eq_true] at hfresh
  obtain ⟨_, ⟨hh, ht, hfC⟩, hfrest⟩ := hfresh
  obtain ⟨ts, talts, hts, htalts, rfl⟩ := lowerTotalExpr_case_some hlow
  obtain ⟨il, hil, rfl⟩ := lowerTotalExpr_var_some hts
  rw [MIR.lowerTotalExprList_cons] at htalts
  cases hA : lowerTotalExpr env (.Lam h (.Lam t C)) with
  | none => rw [hA] at htalts; cases htalts
  | some tA =>
  cases hR : MIR.lowerTotalExprList env rest with
  | none => rw [hA, hR] at htalts; cases htalts
  | some tR =>
  rw [hA, hR] at htalts; cases htalts
  obtain ⟨tC, htC, rfl⟩ := lowerTotalExpr_consAlt hA
  obtain ⟨tC', htC', hrC⟩ := consAlt_rel hC hd hk hs hn hh ht hfC htC
  obtain ⟨tR', htR', hrR⟩ := KnownRel.list hrest env tR hd hfrest hk hs hn hR
  refine ⟨.Case (.Var (il + 1)) (.Lam 0 (.Lam 0 tC') :: tR'), ?_, ?_⟩
  · rw [MIR.lowerTotalExpr_case_of_list, lowerTotalExpr_var, hil, MIR.lowerTotalExprList_cons,
      lowerTotalExpr_consAlt_of htC', htR']
    rfl
  intro ρ π henv hlen hπ hF
  obtain ⟨vl, hvl, hlv⟩ := listKnown_var hl hF hd hil henv
  have hlenR := listRel_length hrR
  refine obsRefines_of_steps 3 3 ?_
  rw [steps_trans 2 1, steps_trans 2 1, case_var_steps hvl, case_var_steps hvl]
  simp only [steps]
  rcases listCase_dispatch hlv with ⟨c, tl, htl, hdisp⟩ | hdisp
  · rw [hdisp, hdisp]
    simp only [List.length_cons, hlenR, List.getElem?_cons_zero]
    split
    · exact obsRefines_refl _
    · refine obsRefines_of_steps 4 4 ?_
      rw [consAlt_steps, consAlt_steps]
      obtain ⟨henv₂, hlen₂⟩ := consAlt_env (c := c) henv hlen htl
      exact hrC _ π henv₂ hlen₂ hπ (consAlt_facts hF hn hk hh ht htl)
  · rw [hdisp, hdisp]
    simp only [List.length_cons, hlenR, List.getElem?_cons_succ]
    split
    · exact obsRefines_refl _
    · rcases listRel_getElem? hrR 0 with ⟨e₁, e₂⟩ | ⟨x, y, e₁, e₂, hxy⟩
      · rw [e₁, e₂]; exact obsRefines_refl _
      · rw [e₁, e₂]; exact hxy ρ π henv hlen hπ hF

theorem KnownRel.nullFuse {Γ : List (VarId × Expr)} {L : List VarId} {sel : Expr} {l l' h t : VarId}
    {C C' em em' : Expr} {inner : List Expr}
    (hsel : resolveHead 64 Γ sel = .Force (.Builtin .NullList))
    (hl : listKnown Γ L (.Var l) = true) (hll : (l' == l) = true) (hinner : inner.length ≤ 1)
    (hC : KnownRel Γ (t :: L) C C') (hem : KnownRel Γ L em em') :
    KnownRel Γ L (.Case (.App sel (.Var l)) [.Case (.Var l') (.Lam h (.Lam t C) :: inner), em])
      (.Case (.Var l) [.Lam h (.Lam t C'), em']) := by
  intro env t₀ hd hfresh hk hs hn hlow
  simp only [freshIn, freshInList, Bool.and_eq_true] at hfresh
  obtain ⟨_, ⟨⟨_, ⟨hh, ht, hfC⟩, _⟩, hfem, _⟩⟩ := hfresh
  obtain ⟨ts, talts, hts, htalts, rfl⟩ := lowerTotalExpr_case_some hlow
  obtain ⟨tsel, tl₀, htsel, htl₀, rfl⟩ := lowerTotalExpr_app_some hts
  obtain ⟨il, hil, rfl⟩ := lowerTotalExpr_var_some htl₀
  rw [MIR.lowerTotalExprList_cons, MIR.lowerTotalExprList_cons, MIR.lowerTotalExprList_nil] at htalts
  cases hX : lowerTotalExpr env (.Case (.Var l') (.Lam h (.Lam t C) :: inner)) with
  | none => rw [hX] at htalts; cases htalts
  | some tX =>
  cases hE : lowerTotalExpr env em with
  | none => rw [hX, hE] at htalts; cases htalts
  | some tE =>
  rw [hX, hE] at htalts; cases htalts
  obtain ⟨tsX, taltsX, htsX, htaltsX, rfl⟩ := lowerTotalExpr_case_some hX
  obtain ⟨il', hil', rfl⟩ := lowerTotalExpr_var_some htsX
  have hil'' : il = il' := by
    rw [envLookupT_congr hll, hil] at hil'; cases hil'; rfl
  subst hil''
  rw [MIR.lowerTotalExprList_cons] at htaltsX
  cases hA : lowerTotalExpr env (.Lam h (.Lam t C)) with
  | none => rw [hA] at htaltsX; cases htaltsX
  | some tA =>
  cases hI : MIR.lowerTotalExprList env inner with
  | none => rw [hA, hI] at htaltsX; cases htaltsX
  | some tI =>
  rw [hA, hI] at htaltsX; cases htaltsX
  have hlenI : tI.length ≤ 1 := by rw [lowerList_length hI]; exact hinner
  obtain ⟨tC, htC, rfl⟩ := lowerTotalExpr_consAlt hA
  obtain ⟨tC', htC', hrC⟩ := consAlt_rel hC hd hk hs hn hh ht hfC htC
  obtain ⟨tE', htE', hrE⟩ := hem env tE hd hfem hk hs hn hE
  refine ⟨.Case (.Var (il + 1)) [.Lam 0 (.Lam 0 tC'), tE'], ?_, ?_⟩
  · rw [MIR.lowerTotalExpr_case_of_list, lowerTotalExpr_var, hil, MIR.lowerTotalExprList_cons,
      lowerTotalExpr_consAlt_of htC', MIR.lowerTotalExprList_cons, htE', MIR.lowerTotalExprList_nil]
    rfl
  intro ρ π henv hlen hπ hF
  obtain ⟨vl, hvl, hlv⟩ := listKnown_var hl hF hd hil henv
  have hres : resolveHead 65 Γ (.App sel (.Var l)) = .App (.Force (.Builtin .NullList)) (.Var l) := by
    rw [resolveHead_app, hsel]
  obtain ⟨hiff, _⟩ := resolveHead_unary 65 Γ (.App sel (.Var l)) hres rfl hF.1 hd hts hil hvl
  have hnull : ∀ b, nullResult vl = some b →
      Reaches (.compute π ρ (.Case (.Apply tsel (.Var (il + 1)))
        [.Case (.Var (il + 1)) (.Lam 0 (.Lam 0 tC) :: tI), tE]))
        (.ret (.caseScrutinee [.Case (.Var (il + 1)) (.Lam 0 (.Lam 0 tC) :: tI), tE] ρ :: π)
          (.VCon (.Bool b))) := by
    intro b hb
    have hh' : Halts ρ (.Apply tsel (.Var (il + 1))) (.VCon (.Bool b)) := by
      apply (hiff _).mpr
      rw [nullList_eval, hb]; rfl
    exact reaches_trans ⟨1, rfl⟩ (halts_on_stack hh' _)
  rcases listShape hlv with ⟨c, tl, htl, hb, hdisp⟩ | ⟨hb, hdisp⟩
  · -- non-empty list
    refine obsRefines_of_reaches (hnull false hb) (reaches_self _) ?_
    refine obsRefines_of_steps 4 3 ?_
    have h3 : steps 3 (.ret (.caseScrutinee [.Case (.Var (il + 1)) (.Lam 0 (.Lam 0 tC) :: tI), tE] ρ :: π)
        (.VCon (.Bool false))) = .ret (.caseScrutinee (.Lam 0 (.Lam 0 tC) :: tI) ρ :: π) vl := by
      simp [steps, step, constToTagAndFields, hvl]
    have hL : steps 4 (.ret (.caseScrutinee [.Case (.Var (il + 1)) (.Lam 0 (.Lam 0 tC) :: tI), tE] ρ :: π)
        (.VCon (.Bool false))) = step (.ret (.caseScrutinee (.Lam 0 (.Lam 0 tC) :: tI) ρ :: π) vl) := by
      rw [show 4 = 3 + 1 from rfl, steps_trans, h3]; rfl
    have hR : steps 3 (.compute π ρ (.Case (.Var (il + 1)) [.Lam 0 (.Lam 0 tC'), tE'])) =
        step (.ret (.caseScrutinee [.Lam 0 (.Lam 0 tC'), tE'] ρ :: π) vl) := by
      rw [show 3 = 2 + 1 from rfl, steps_trans, case_var_steps hvl]; rfl
    rw [hL, hR, hdisp, hdisp]
    simp only [List.length_cons, List.getElem?_cons_zero, List.length_nil]
    have hle : ¬ (tI.length + 1 > 2) := by omega
    rw [if_neg hle, if_neg (by decide : ¬ (0 + 1 + 1 > 2))]
    refine obsRefines_of_steps 4 4 ?_
    rw [consAlt_steps, consAlt_steps]
    obtain ⟨henv₂, hlen₂⟩ := consAlt_env (c := c) henv hlen htl
    exact hrC _ π henv₂ hlen₂ hπ (consAlt_facts hF hn hk hh ht htl)
  · -- empty list
    refine obsRefines_of_reaches (hnull true hb) (reaches_self _) ?_
    refine obsRefines_of_steps 1 3 ?_
    have hR : steps 3 (.compute π ρ (.Case (.Var (il + 1)) [.Lam 0 (.Lam 0 tC'), tE'])) =
        step (.ret (.caseScrutinee [.Lam 0 (.Lam 0 tC'), tE'] ρ :: π) vl) := by
      rw [show 3 = 2 + 1 from rfl, steps_trans, case_var_steps hvl]; rfl
    rw [hR, hdisp]
    simp [steps, step, constToTagAndFields]
    exact hrE ρ π henv hlen hπ hF

end Moist.Verified.ShapeFacts
