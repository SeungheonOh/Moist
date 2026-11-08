import Moist.Verified.GuardsSoundness.Sound

/-! # Facts about the fields a list or pair case binds

The first alternative `λh t. b` of a case on a list receives the head and
the tail of the list, and of a case on a decoded constructor its tag and
fields. Inside `b` they are recorded as the facts `h = headList s`,
`t = tailList s` (or `fstPair s`, `sndPair s`), whose right-hand sides
are evaluated in the environment of the case (`FactRel.caseBind`).
-/

namespace Moist.Verified.Guards

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast
open Moist.Verified.KnownLists

/-- Two binders recorded with right-hand sides of the environment below both. -/
theorem FactsHold.push2 {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} {env : List VarId} {ρ : CekEnv} {h t : VarId} {r₁ r₂ : Expr}
    {v₁ v₂ : CekValue} (hF : FactsHold P Γ env ρ) (h₁ : P env ρ r₁ v₁) (h₂ : P env ρ r₂ v₂) :
    FactsHold P ((t, r₂) :: (h, r₁) :: Γ) (t :: h :: env) ((ρ.extend v₁).extend v₂) := by
  intro y entry i hf hl
  by_cases hty : (t == y) = true
  · simp only [List.find?_cons, hty] at hf
    cases hf
    rw [MIR.envLookupT_cons_of_beq hty] at hl
    cases hl
    exact ⟨v₂, 2, by omega, by simp, rfl, h₂⟩
  · have hty' : (t == y) = false := by simpa using hty
    simp only [List.find?_cons, hty'] at hf
    rw [envLookupT_cons_neq t y _ hty'] at hl
    by_cases hhy : (h == y) = true
    · simp only [hhy] at hf
      cases hf
      rw [MIR.envLookupT_cons_of_beq hhy] at hl
      cases hl
      exact ⟨v₁, 2, by simp, by simp, rfl, h₁⟩
    · have hhy' : (h == y) = false := by simpa using hhy
      simp only [hhy'] at hf
      rw [envLookupT_cons_neq h y _ hhy'] at hl
      cases hl' : envLookupT env y with
      | none => rw [hl'] at hl; cases hl
      | some i' =>
        rw [hl'] at hl; simp at hl; subst hl
        obtain ⟨v, k, hik, hk, hv, hp⟩ := hF y entry i' hf hl'
        exact ⟨v, k + 2, by omega, by simp; omega, hv, by simpa using hp⟩

/-! ## Projections of a scrutinee -/

theorem halts_force1_app {ρ : CekEnv} {b : BuiltinFun} {ts : Term} {w r : CekValue}
    (hea : expectedArgs b = .more .argQ (.one .argV)) (hw : Halts ρ ts w)
    (hev : evalBuiltin b [w] = some r) : Halts ρ (.Apply (.Force (.Builtin b)) ts) r := by
  have h1 : Reaches (.compute [] ρ (.Apply (.Force (.Builtin b)) ts))
      (.compute [.funV (.VBuiltin b [] (.one .argV))] ρ ts) := by
    refine reaches_of_steps 5 ?_
    simp [steps, step, hea, ExpectedArgs.head, ExpectedArgs.tail]
  refine reaches_trans h1 (reaches_trans (halts_on_stack hw _) (reaches_of_steps 2 ?_))
  simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, hev]

theorem halts_force2_app {ρ : CekEnv} {b : BuiltinFun} {ts : Term} {w r : CekValue}
    (hea : expectedArgs b = .more .argQ (.more .argQ (.one .argV))) (hw : Halts ρ ts w)
    (hev : evalBuiltin b [w] = some r) : Halts ρ (.Apply (.Force (.Force (.Builtin b))) ts) r := by
  have h1 : Reaches (.compute [] ρ (.Apply (.Force (.Force (.Builtin b))) ts))
      (.compute [.funV (.VBuiltin b [] (.one .argV))] ρ ts) := by
    refine reaches_of_steps 7 ?_
    simp [steps, step, hea, ExpectedArgs.head, ExpectedArgs.tail]
  refine reaches_trans h1 (reaches_trans (halts_on_stack hw _) (reaches_of_steps 2 ?_))
  simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, hev]

/-- The two fields of a list cell are its head and its tail. -/
theorem list_projections {ρ : CekEnv} {ts : Term} {w : CekValue} (hw : Halts ρ ts w) (hlv : ListValue w)
    {talts : List Term} {alt : Term} {fs : List CekValue} (hdisp : dispatch talts w = some (alt, fs))
    (hlen : fs.length = 2) :
    ∃ a b, fs = [a, b] ∧ Halts ρ (.Apply (.Force (.Builtin .HeadList)) ts) a ∧
      Halts ρ (.Apply (.Force (.Builtin .TailList)) ts) b := by
  cases w with
  | VCon c =>
    cases c <;> simp only [ListValue] at hlv
    all_goals
      rename_i l
      cases l with
      | nil =>
        obtain ⟨_, he⟩ := dispatch_vcon (by rfl) hdisp
        subst he; simp at hlen
      | cons x rest =>
        obtain ⟨_, he⟩ := dispatch_vcon (by rfl) hdisp
        subst he
        exact ⟨_, _, rfl, halts_force1_app rfl hw rfl, halts_force1_app rfl hw rfl⟩
  | _ => simp [ListValue] at hlv

theorem pair_projections {ρ : CekEnv} {ts : Term} {w : CekValue} (hw : Halts ρ ts w) (hpv : PairValue w)
    {talts : List Term} {alt : Term} {fs : List CekValue} (hdisp : dispatch talts w = some (alt, fs)) :
    ∃ a b, fs = [a, b] ∧ Halts ρ (.Apply (.Force (.Force (.Builtin .FstPair))) ts) a ∧
      Halts ρ (.Apply (.Force (.Force (.Builtin .SndPair))) ts) b := by
  obtain ⟨i, xs, rfl⟩ := hpv
  obtain ⟨_, he⟩ := dispatch_vcon (by rfl) hdisp
  cases he
  exact ⟨_, _, rfl, halts_force2_app rfl hw rfl, halts_force2_app rfl hw rfl⟩

/-! ## Dispatch on two alternative lists of the same length -/

def tagFields : CekValue → Option (Nat × List CekValue)
  | .VConstr tag fs => some (tag, fs)
  | .VCon c => (constToTagAndFields c).map fun r => (r.1, r.2.2)
  | _ => none

theorem dispatch_same {talts talts' : List Term} (hl : talts.length = talts'.length) (w : CekValue) :
    (dispatch talts w = none ∧ dispatch talts' w = none) ∨
      ∃ i fs a a', tagFields w = some (i, fs) ∧ talts[i]? = some a ∧ talts'[i]? = some a' ∧
        dispatch talts w = some (a, fs) ∧ dispatch talts' w = some (a', fs) := by
  have pick : ∀ i : Nat, (talts[i]? = none ∧ talts'[i]? = none) ∨ ∃ a a', talts[i]? = some a ∧ talts'[i]? = some a' := by
    intro i
    by_cases hi : i < talts.length
    · exact .inr ⟨_, _, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (by omega)⟩
    · exact .inl ⟨List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)⟩
  cases w with
  | VConstr tag fs =>
    rcases pick tag with ⟨h1, h2⟩ | ⟨a, a', h1, h2⟩
    · exact .inl ⟨by simp [dispatch, h1], by simp [dispatch, h2]⟩
    · exact .inr ⟨tag, fs, a, a', rfl, h1, h2, by simp [dispatch, h1], by simp [dispatch, h2]⟩
  | VCon c =>
    cases hc : constToTagAndFields c with
    | none => exact .inl ⟨by simp [dispatch, hc], by simp [dispatch, hc]⟩
    | some r =>
      obtain ⟨tag, n, fs⟩ := r
      by_cases hg : n > 0 && talts.length > n
      · have hg' : (n > 0 && talts'.length > n) = true := by rw [← hl]; exact hg
        exact .inl ⟨by simp [dispatch, hc, hg], by simp [dispatch, hc, hg']⟩
      · have hg' : ¬ (n > 0 && talts'.length > n) = true := by rw [← hl]; exact hg
        rcases pick tag with ⟨h1, h2⟩ | ⟨a, a', h1, h2⟩
        · exact .inl ⟨by simp [dispatch, hc, hg, h1], by simp [dispatch, hc, hg', h2]⟩
        · exact .inr ⟨tag, fs, a, a', by simp [tagFields, hc], h1, h2,
            by simp [dispatch, hc, hg, h1], by simp [dispatch, hc, hg', h2]⟩
  | VLam _ _ => exact .inl ⟨rfl, rfl⟩
  | VDelay _ _ => exact .inl ⟨rfl, rfl⟩
  | VBuiltin _ _ _ => exact .inl ⟨rfl, rfl⟩

/-- The first constructor of a list or a decoded constructor carries two fields. -/
theorem tag0_two {k : Kind} (hk : k = .list ∨ k = .pair) {w : CekValue} (hkv : KindV k w)
    {fs : List CekValue} (ht : tagFields w = some (0, fs)) : fs.length = 2 := by
  rcases hk with rfl | rfl
  · cases w with
    | VCon c =>
      cases c <;> simp only [KindV, ListValue] at hkv
      all_goals
        rename_i l
        cases l <;> simp [tagFields, constToTagAndFields] at ht <;> (subst ht; rfl)
    | _ => simp [KindV, ListValue] at hkv
  · obtain ⟨i, xs, rfl⟩ := hkv
    simp [tagFields, constToTagAndFields] at ht
    subst ht; rfl

theorem FactsScoped.push2 {Γ : List (VarId × Expr)} {env : List VarId} {h t : VarId} {r₁ r₂ : Expr}
    (hs : FactsScoped Γ env) (h₁ : (lowerTotalExpr env r₁).isSome = true)
    (h₂ : (lowerTotalExpr env r₂).isSome = true) :
    FactsScoped ((t, r₂) :: (h, r₁) :: Γ) (t :: h :: env) := by
  intro y entry i hf hl
  by_cases hty : (t == y) = true
  · simp only [List.find?_cons, hty] at hf
    cases hf
    rw [MIR.envLookupT_cons_of_beq hty] at hl
    cases hl
    exact ⟨2, by omega, by simp, by simpa using h₂⟩
  · have hty' : (t == y) = false := by simpa using hty
    simp only [List.find?_cons, hty'] at hf
    rw [envLookupT_cons_neq t y _ hty'] at hl
    by_cases hhy : (h == y) = true
    · simp only [hhy] at hf
      cases hf
      rw [MIR.envLookupT_cons_of_beq hhy] at hl
      cases hl
      exact ⟨2, by simp, by simp, by simpa using h₁⟩
    · have hhy' : (h == y) = false := by simpa using hhy
      simp only [hhy'] at hf
      rw [envLookupT_cons_neq h y _ hhy'] at hl
      cases hl' : envLookupT env y with
      | none => rw [hl'] at hl; cases hl
      | some i' =>
        rw [hl'] at hl; simp at hl; subst hl
        obtain ⟨k, hik, hk, hsc⟩ := hs y entry i' hf hl'
        exact ⟨k + 2, by omega, by simp; omega, by simpa using hsc⟩

theorem KeysBound.push2 {Γ : List (VarId × Expr)} {env : List VarId} {h t : VarId} {r₁ r₂ : Expr}
    (hk : KeysBound Γ env) : KeysBound ((t, r₂) :: (h, r₁) :: Γ) (t :: h :: env) := by
  intro entry hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · simp [envLookupT_cons, varId_beq_self]
  rcases List.mem_cons.mp hmem with rfl | hmem
  · rw [envLookupT_cons]
    split
    · rfl
    · simp [envLookupT_cons, varId_beq_self]
  · exact (hk.cons h).cons t entry hmem

theorem lower_proj1 {env : List VarId} {s : Expr} {ts : Term} (b : BuiltinFun)
    (hs : lowerTotalExpr env s = some ts) :
    lowerTotalExpr env (.App (.Force (.Builtin b)) s) = some (.Apply (.Force (.Builtin b)) ts) := by
  rw [MIR.lowerTotalExpr_app, MIR.lowerTotalExpr_force, lowerTotalExpr_builtin, hs]; rfl

theorem lower_proj2 {env : List VarId} {s : Expr} {ts : Term} (b : BuiltinFun)
    (hs : lowerTotalExpr env s = some ts) :
    lowerTotalExpr env (.App (.Force (.Force (.Builtin b))) s) =
      some (.Apply (.Force (.Force (.Builtin b))) ts) := by
  rw [MIR.lowerTotalExpr_app, MIR.lowerTotalExpr_force, MIR.lowerTotalExpr_force, lowerTotalExpr_builtin, hs]
  rfl

/-- What the binder facts of a list or pair case record. -/
theorem binderFacts_spec {k : Kind} (hkl : k = .list ∨ k = .pair) (s : Expr) (h t : VarId)
    (Γ : List (VarId × Expr)) :
    ∃ r₁ r₂, binderFacts k s h t Γ = (t, r₂) :: (h, r₁) :: Γ ∧
      (∀ env ts, lowerTotalExpr env s = some ts →
        (lowerTotalExpr env r₁).isSome = true ∧ (lowerTotalExpr env r₂).isSome = true) ∧
      (∀ env, freshIn env s = true → freshIn env r₁ = true ∧ freshIn env r₂ = true) ∧
      (∀ env ρ ts w (talts : List Term) alt fs, lowerTotalExpr env s = some ts → Halts ρ ts w →
        KindV k w → dispatch talts w = some (alt, fs) → fs.length = 2 →
        ∃ f₁ f₂, fs = [f₁, f₂] ∧ Produces env ρ r₁ f₁ ∧ Produces env ρ r₂ f₂) := by
  rcases hkl with rfl | rfl
  · refine ⟨headListE s, tailListE s, rfl, fun env ts hs => ?_, fun env hf => ?_, ?_⟩
    · simp [headListE, tailListE, lower_proj1 _ hs]
    · simp [headListE, tailListE, freshIn, hf]
    · intro env ρ ts w talts alt fs hs hw hkv hd h2
      obtain ⟨f₁, f₂, rfl, hh₁, hh₂⟩ := list_projections hw hkv hd h2
      exact ⟨f₁, f₂, rfl, ⟨_, lower_proj1 _ hs, hh₁⟩, ⟨_, lower_proj1 _ hs, hh₂⟩⟩
  · refine ⟨fstPairE s, sndPairE s, rfl, fun env ts hs => ?_, fun env hf => ?_, ?_⟩
    · simp [fstPairE, sndPairE, lower_proj2 _ hs]
    · simp [fstPairE, sndPairE, freshIn, hf]
    · intro env ρ ts w talts alt fs hs hw hkv hd _
      obtain ⟨f₁, f₂, rfl, hh₁, hh₂⟩ := pair_projections hw hkv hd
      exact ⟨f₁, f₂, rfl, ⟨_, lower_proj2 _ hs, hh₁⟩, ⟨_, lower_proj2 _ hs, hh₂⟩⟩

/-- The first alternative of a case on a list or a decoded constructor, with
    facts for its two binders. -/
theorem FactRel.caseBind {G : VarId → Prop} {Γ : List (VarId × Expr)} {s : Expr} {h t : VarId}
    {b b' : Expr} {rest rest' : List Expr} (hGh : G h) (hGt : G t)
    (hb : FactRel G PF (altFacts Γ s h t) b b') (hrest : ListRel (FactRel G PF Γ) rest rest') :
    FactRel G PF Γ (.Case s (.Lam h (.Lam t b) :: rest)) (.Case s (.Lam h (.Lam t b') :: rest')) := by
  unfold altFacts at hb
  generalize hk : scrutineeKind Γ [] s = k at hb
  have generic : FactRel G PF Γ b b' →
      FactRel G PF Γ (.Case s (.Lam h (.Lam t b) :: rest)) (.Case s (.Lam h (.Lam t b') :: rest')) :=
    fun hb => FactRel.case (FactRel.refl _ _ _ _) ⟨(hb.lam hGt).lam hGh, hrest⟩
  have known : (k = .list ∨ k = .pair) →
      FactRel G PF (binderFacts k s h t Γ) b b' →
      FactRel G PF Γ (.Case s (.Lam h (.Lam t b) :: rest)) (.Case s (.Lam h (.Lam t b') :: rest')) := by
    intro hkl hb
    intro env t₀ hG hd hfresh hkb hsc hlow
    simp only [freshIn, freshInList, Bool.and_eq_true] at hfresh
    obtain ⟨hfs, ⟨hh, ht, hfb⟩, hfrest⟩ := hfresh
    obtain ⟨ts, talts, hts, htalts, rfl⟩ := lowerTotalExpr_case_some hlow
    rw [MIR.lowerTotalExprList_cons] at htalts
    cases hA : lowerTotalExpr env (.Lam h (.Lam t b)) with
    | none => rw [hA] at htalts; cases htalts
    | some tA =>
    cases hR : MIR.lowerTotalExprList env rest with
    | none => rw [hA, hR] at htalts; cases htalts
    | some tR =>
    rw [hA, hR] at htalts; cases htalts
    obtain ⟨tb, htb, rfl⟩ := lowerTotalExpr_consAlt hA
    obtain ⟨r₁, r₂, hbf, hlowr, hfreshr, hprod⟩ := binderFacts_spec hkl s h t Γ
    rw [hbf] at hb
    obtain ⟨hlow₁, hlow₂⟩ := hlowr env ts hts
    obtain ⟨hfresh₁, hfresh₂⟩ := hfreshr env hfs
    have hd₂ : EnvDistinct (t :: h :: env) := (hd.cons hh).cons ht
    obtain ⟨tb', htb', hrb⟩ := hb (t :: h :: env) tb (allG_cons hGt (allG_cons hGh hG)) hd₂ hfb
      (KeysBound.push2 hkb) (FactsScoped.push2 hsc hlow₁ hlow₂) htb
    obtain ⟨tR', htR', hrR⟩ := FactRel.list hrest env tR hG hd hfrest hkb hsc hR
    refine ⟨.Case ts (.Lam 0 (.Lam 0 tb') :: tR'), ?_, ?_⟩
    · rw [MIR.lowerTotalExpr_case_of_list, hts, MIR.lowerTotalExprList_cons,
        lowerTotalExpr_consAlt_of htb', htR']
      rfl
    intro ρ π henv hlen hπ hF
    apply obsRefines_of_step
    show ObsRefines (.compute (.caseScrutinee _ ρ :: π) ρ ts) (.compute (.caseScrutinee _ ρ :: π) ρ ts)
    apply obsRefines_of_continuation
    intro w hw
    have hρ : Inv ⟨Γ, [], []⟩ env ρ := ⟨henv, hlen, hF, fun _ h _ _ => by simp at h, fun _ h => by cases h⟩
    have hkv : KindV k w := by
      have h0 := scrutineeKind_sound (c := ⟨Γ, [], []⟩) hρ hd hts hw
      simp only at h0
      rw [hk] at h0; exact h0
    have hwwf := halts_wellFormed henv hlen (MIR.lowerTotalExpr_closedAt hts) hw
    have hlR := listRel_length hrR
    apply obsRefines_of_step
    rw [step_caseScrutinee, step_caseScrutinee]
    rcases dispatch_same (talts := .Lam 0 (.Lam 0 tb) :: tR) (talts' := .Lam 0 (.Lam 0 tb') :: tR')
      (by simp [hlR]) w with ⟨h1, h2⟩ | ⟨i, fs, a, a', htag, ha, ha', h1, h2⟩
    · rw [h1, h2]; exact obsRefines_refl _
    rw [h1, h2]
    simp only
    have hfswf := (dispatch_spec h1 hwwf).2
    cases i with
    | zero =>
      simp at ha ha'
      subst ha; subst ha'
      have h2f := tag0_two hkl hkv htag
      obtain ⟨f₁, f₂, hfs, hp₁, hp₂⟩ := hprod env ρ ts w _ _ fs hts hw hkv h1 h2f
      subst hfs
      cases hfswf with
      | cons hw₁ hrest₁ =>
      cases hrest₁ with
      | cons hw₂ _ =>
      refine obsRefines_of_steps 4 4 ?_
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      rw [show Frame.applyArg f₁ :: Frame.applyArg f₂ :: π = [Frame.applyArg f₁, Frame.applyArg f₂] ++ π from rfl,
        consAlt_steps, consAlt_steps]
      have henv₁ := envWellFormed_extend env.length henv hlen hw₁
      have hlen₁ : env.length + 1 ≤ (ρ.extend f₁).length := by simp [CekEnv.extend, CekEnv.length]; omega
      have henv₂ := envWellFormed_extend (env.length + 1) henv₁ hlen₁ hw₂
      have hlen₂ : env.length + 1 + 1 ≤ ((ρ.extend f₁).extend f₂).length := by
        simp [CekEnv.extend, CekEnv.length]; omega
      exact hrb _ π (by simpa using henv₂) (by simpa using hlen₂) hπ
        (FactsHold.push2 hF ⟨hp₁, hfresh₁⟩ ⟨hp₂, hfresh₂⟩)
    | succ i =>
      simp at ha ha'
      rcases listRel_getElem? hrR i with ⟨e₁, _⟩ | ⟨x, y, e₁, e₂, hxy⟩
      · rw [e₁] at ha; cases ha
      · rw [e₁] at ha; rw [e₂] at ha'; cases ha; cases ha'
        exact hxy ρ _ henv hlen (stackWellFormed_applyArgs hfswf hπ) hF
  rcases k with _ | _ | _ | _ | _ | _
  · exact generic hb
  · exact generic hb
  · exact known (.inl rfl) hb
  · exact known (.inr rfl) hb
  · exact generic hb
  · exact generic hb

end Moist.Verified.Guards
