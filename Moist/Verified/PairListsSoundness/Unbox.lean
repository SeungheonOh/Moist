import Moist.Verified.PairListsSoundness.Family
import Moist.Verified.PairListsSoundness.Prepare

variable [sv : Moist.CEK.SemVariant]

/-! # Destructuring the head of a list of data pairs

In the cons alternative of a `case` on a list of data pairs the head `h` holds
a pair of data. The two prepared bindings `a = h`, `b = h` (unused by the
body) are replaced by a native `case` on `h` binding its components, and the
projections of `h` in the body by the components (`KnownRel.pairEntryCase`):
the projections return the components (`replaceProjections_factRel`) and the
body ignores the names `a` and `b` otherwise.
-/

namespace Moist.Verified.KnownLists

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts

/-- The prepared bindings of a pair head, below the head and tail binders. -/
theorem lower_prepared {E : List VarId} {h h₁ h₂ a b : VarId} {e1 e2 : Bool} {inner : Expr} {t : Term}
    (hh : envLookupT E h = some 1) (hah : (a == h) = false) (hh₁ : (h₁ == h) = true) (hh₂ : (h₂ == h) = true)
    (hfa : (freeVars inner).contains a = false) (hfb : (freeVars inner).contains b = false)
    (hlow : lowerTotalExpr E (.Let [(a, .Var h₁, e1)] (.Let [(b, .Var h₂, e2)] inner)) = some t) :
    ∃ t₀, lowerTotalExpr E inner = some t₀ ∧
      lowerTotalExpr (b :: a :: E) inner = some (renameTerm (shiftRename 1) (renameTerm (shiftRename 1) t₀)) ∧
      t = .Apply (.Lam 0 (.Apply (.Lam 0 (renameTerm (shiftRename 1) (renameTerm (shiftRename 1) t₀)))
        (.Var 3))) (.Var 2) := by
  obtain ⟨tr, tb, htr, htb, rfl⟩ := lowerTotalExpr_let_single_some hlow
  obtain ⟨tr₂, tb₂, htr₂, htb₂, rfl⟩ := lowerTotalExpr_let_single_some htb
  rw [lowerTotalExpr_var, envLookupT_congr hh₁, hh] at htr; cases htr
  rw [lowerTotalExpr_var, envLookupT_congr hh₂, envLookupT_cons_neq a h E hah, hh] at htr₂; cases htr₂
  rw [MIR.lowerTotalExpr_prepend_unused _ b inner hfb, MIR.lowerTotalExpr_prepend_unused _ a inner hfa] at htb₂
  cases h₀ : lowerTotalExpr E inner with
  | none => rw [h₀] at htb₂; cases htb₂
  | some t₀ =>
    rw [h₀] at htb₂; cases htb₂
    refine ⟨t₀, rfl, ?_, rfl⟩
    rw [MIR.lowerTotalExpr_prepend_unused _ b inner hfb, MIR.lowerTotalExpr_prepend_unused _ a inner hfa, h₀]
    rfl

/-- Unused bindings and the destructuring of a pair agree on a body that
    reads only components through the facts. -/
theorem unbox_obs {d : Nat} {ρ : CekEnv} {π : Stack} {t₀ tR : Term} {x y : Moist.Plutus.Data}
    (henv : EnvWellFormed d ρ) (hlen : d ≤ ρ.length) (hπ : StackWellFormed π)
    (hh : ρ.lookup 2 = some (.VCon (.Pair (.Data x, .Data y))))
    (ht₀ : closedAt d t₀ = true)
    (hR : ObsRefines
      (.compute π ((ρ.extend (.VCon (.Data x))).extend (.VCon (.Data y)))
        (renameTerm (shiftRename 1) (renameTerm (shiftRename 1) t₀)))
      (.compute π ((ρ.extend (.VCon (.Data x))).extend (.VCon (.Data y))) tR)) :
    ObsRefines
      (.compute π ρ (.Apply (.Lam 0 (.Apply (.Lam 0 (renameTerm (shiftRename 1) (renameTerm (shiftRename 1) t₀)))
        (.Var 3))) (.Var 2)))
      (.compute π ρ (.Case (.Var 2) [.Lam 0 (.Lam 0 tR)])) := by
  have wfx : ValueWellFormed (.VCon (.Data x)) := .vcon _
  have wfh : ValueWellFormed (.VCon (.Pair (.Data x, .Data y))) := .vcon _
  have henv₁ : ∀ w, ValueWellFormed w → EnvWellFormed (d + 1) (ρ.extend w) :=
    fun w hw => envWellFormed_extend d henv hlen hw
  have c₁ := closedAt_shift ht₀
  have h3 : ∀ w, (ρ.extend w).lookup 3 = some (.VCon (.Pair (.Data x, .Data y))) := by
    intro w; simpa [CekEnv.extend, CekEnv.lookup] using hh
  refine obsRefines_of_reaches
    (s₁' := .compute π (((ρ.extend (.VCon (.Pair (.Data x, .Data y)))).extend
      (.VCon (.Pair (.Data x, .Data y))))) (renameTerm (shiftRename 1) (renameTerm (shiftRename 1) t₀)))
    (s₂' := .compute π ((ρ.extend (.VCon (.Data x))).extend (.VCon (.Data y))) tR)
    (reaches_trans (reaches_of_steps 3 rfl) (reaches_trans (halts_on_stack (halts_var_of_lookup hh) _)
      (reaches_trans (reaches_of_steps 1 rfl) (reaches_trans (reaches_of_steps 3 rfl)
        (reaches_trans (halts_on_stack (halts_var_of_lookup (h3 _)) _) (reaches_of_steps 1 rfl))))))
    ⟨7, by simp [steps, step, hh, constToTagAndFields, CekEnv.extend]⟩ ?_
  refine obsRefines_trans (obsEq_shift _ (henv₁ _ wfh) hπ c₁).2 ?_
  refine obsRefines_trans (obsEq_shift _ henv hπ ht₀).2 ?_
  refine obsRefines_trans (obsEq_shift (.VCon (.Data x)) henv hπ ht₀).1 ?_
  exact obsRefines_trans (obsEq_shift _ (henv₁ _ wfx) hπ c₁).1 hR

end Moist.Verified.KnownLists

namespace Moist.Verified.KnownLists

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts

/-- Facts of the components of the head, below the head and tail binders. -/
theorem component_facts {Γ : List (VarId × Expr)} {env : List VarId} {ρ : CekEnv} {h t a b : VarId}
    {x y : Moist.Plutus.Data} {tl : CekValue}
    (hF : FactsHold Produces Γ (t :: h :: env) ((ρ.extend (.VCon (.Pair (.Data x, .Data y)))).extend tl))
    (hth : (t == h) = false) (hah : (a == h) = false) :
    FactsHold Produces (componentFacts Γ h a b) (b :: a :: t :: h :: env)
      ((((ρ.extend (.VCon (.Pair (.Data x, .Data y)))).extend tl).extend (.VCon (.Data x))).extend
        (.VCon (.Data y))) := by
  have hh₂ : envLookupT (t :: h :: env) h = some 1 := by
    rw [envLookupT_cons_neq t h _ hth, envLookupT_cons]; simp [varId_beq_self]
  have hh₃ : envLookupT (a :: t :: h :: env) h = some 2 := by
    rw [envLookupT_cons_neq a h _ hah, hh₂]; rfl
  have hfst : Produces (t :: h :: env) ((ρ.extend (.VCon (.Pair (.Data x, .Data y)))).extend tl) (fstApp h)
      (.VCon (.Data x)) := by
    refine ⟨.Apply (.Force (.Force (.Builtin .FstPair))) (.Var 2), ?_, ?_⟩
    · simp [fstApp, MIR.lowerTotalExpr_app, MIR.lowerTotalExpr_force, lowerTotalExpr_builtin,
        lowerTotalExpr_var, hh₂]
    · exact halts_apply_intro (forced_pair_halts _ (.inl rfl)) (halts_var_of_lookup rfl)
        (builtin_final_reaches rfl rfl rfl)
  have hsnd : Produces (a :: t :: h :: env)
      (((ρ.extend (.VCon (.Pair (.Data x, .Data y)))).extend tl).extend (.VCon (.Data x))) (sndApp h)
      (.VCon (.Data y)) := by
    refine ⟨.Apply (.Force (.Force (.Builtin .SndPair))) (.Var 3), ?_, ?_⟩
    · simp [sndApp, MIR.lowerTotalExpr_app, MIR.lowerTotalExpr_force, lowerTotalExpr_builtin,
        lowerTotalExpr_var, hh₃]
    · exact halts_apply_intro (forced_pair_halts _ (.inr rfl)) (halts_var_of_lookup rfl)
        (builtin_final_reaches rfl rfl rfl)
  exact (hF.push hfst).push hsnd

end Moist.Verified.KnownLists

namespace Moist.Verified.KnownLists

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts

/-- A `case` on a list of data pairs whose cons alternative carries the
    prepared component bindings destructures the head. -/
theorem KnownRel.pairEntryCase {Γ : List (VarId × Expr)} {L : List VarId} {l h h₁ h₂ t a b : VarId}
    {e1' e2' : Bool} {C inner : Expr} {rest rest' : List Expr}
    (hl : pairListKnown Γ L (.Var l) = true)
    (hC : KnownRel pairFamily Γ (t :: L) C (.Let [(a, .Var h₁, e1')] (.Let [(b, .Var h₂, e2')] inner)))
    (hfreshC : ∀ E, freshIn E C = true →
      freshIn E (.Let [(a, .Var h₁, e1')] (.Let [(b, .Var h₂, e2')] inner)) = true)
    (hrest : ListRel (KnownRel pairFamily Γ L) rest rest')
    (hh₁ : (h₁ == h) = true) (hh₂ : (h₂ == h) = true)
    (hba : (b == a) = false) (hah : (a == h) = false)
    (hua : maxUidExpr inner < a.uid) (hub : maxUidExpr inner < b.uid) :
    KnownRel pairFamily Γ L
      (.Case (.Var l) (.Lam h (.Lam t C) :: rest))
      (.Case (.Var l) (.Lam h (.Lam t (.Case (.Var h)
        [.Lam a (.Lam b (replaceProjections (componentFacts Γ h a b) h a b inner))])) :: rest')) := by
  intro env t₀ hd hfr hk hs hn hlow
  simp only [freshIn, freshInList, Bool.and_eq_true] at hfr
  obtain ⟨_, ⟨hh, ht, hfC₀⟩, hfrest⟩ := hfr
  have hfC : freshIn (t :: h :: env) C = true := hfC₀
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
  -- names below the alternative binders
  have hth : (t == h) = false := by
    cases hc : (t == h)
    · rfl
    · rw [envLookupT_cons, varId_beq_symm hc] at ht; simp at ht
  have hh₂' := hh₂
  have hh₂ : envLookupT (t :: h :: env) h = some 1 := by
    rw [envLookupT_cons_neq t h _ hth, envLookupT_cons]; simp [varId_beq_self]
  have hfa : (freeVars inner).contains a = false := maxUidExpr_fresh _ _ hua
  have hfb : (freeVars inner).contains b = false := maxUidExpr_fresh _ _ hub
  obtain ⟨t₀', ht₀', hbin, rfl⟩ := lower_prepared hh₂ hah hh₁ hh₂' hfa hfb htC'
  -- the source binders `a` and `b` are fresh below the alternative binders
  have hfC₁ := hfreshC _ hfC
  rw [freshIn_let_single] at hfC₁
  simp only [Bool.and_eq_true] at hfC₁
  obtain ⟨⟨_, ha⟩, hfC₂⟩ := hfC₁
  rw [freshIn_let_single] at hfC₂
  simp only [Bool.and_eq_true] at hfC₂
  obtain ⟨⟨_, hb⟩, hfI⟩ := hfC₂
  obtain ⟨hd₁, hk₁, hs₁, _⟩ := enter_binder hd hk hs hh
  obtain ⟨hd₂, hk₂, hs₂, _⟩ := enter_binder hd₁ hk₁ hs₁ ht
  obtain ⟨hd₃, hk₃, hs₃, _⟩ := enter_binder hd₂ hk₂ hs₂ ha
  obtain ⟨hd₄, hk₄, hs₄, _⟩ := enter_binder hd₃ hk₃ hs₃ hb
  -- the facts of the components
  have hkc : KeysBound (componentFacts Γ h a b) (b :: a :: t :: h :: env) := by
    intro entry hmem
    simp only [componentFacts, List.mem_cons] at hmem
    rcases hmem with rfl | rfl | hmem
    · simp [envLookupT_cons, varId_beq_self]
    · rw [envLookupT_cons_neq b a _ hba, envLookupT_cons]; simp [varId_beq_self]
    · exact hk₄ entry hmem
  have hsc : FactsScoped (componentFacts Γ h a b) (b :: a :: t :: h :: env) := by
    refine (hs₂.push ?_).push ?_
    · simp [fstApp, MIR.lowerTotalExpr_app, MIR.lowerTotalExpr_force, lowerTotalExpr_builtin,
        lowerTotalExpr_var, hh₂]
    · simp [sndApp, MIR.lowerTotalExpr_app, MIR.lowerTotalExpr_force, lowerTotalExpr_builtin,
        lowerTotalExpr_var, envLookupT_cons_neq a h _ hah, hh₂]
  have hfind_a : (componentFacts Γ h a b).find? (fun e => e.1 == a) = some (a, fstApp h) := by
    simp [componentFacts, hba, varId_beq_self]
  have hfind_b : (componentFacts Γ h a b).find? (fun e => e.1 == b) = some (b, sndApp h) := by
    simp [componentFacts, varId_beq_self]
  obtain ⟨tRp, htRp, hrRp⟩ := replaceProjections_factRel h a b (a, fstApp h) (b, sndApp h) rfl rfl inner
    (componentFacts Γ h a b) ⟨hua, hub⟩ hfind_a hfind_b (b :: a :: t :: h :: env) _ (fun _ _ => trivial)
    hd₄ hfI hkc hsc hbin
  have closed₀ := MIR.lowerTotalExpr_closedAt ht₀'
  simp only [List.length_cons] at closed₀
  refine ⟨.Case (.Var (il + 1)) (.Lam 0 (.Lam 0 (.Case (.Var 2) [.Lam 0 (.Lam 0 tRp)])) :: tR'), ?_, ?_⟩
  · rw [MIR.lowerTotalExpr_case_of_list, lowerTotalExpr_var, hil, MIR.lowerTotalExprList_cons, htR']
    rw [lowerTotalExpr_consAlt_of (C := .Case (.Var h) [.Lam a (.Lam b
      (replaceProjections (componentFacts Γ h a b) h a b inner))]) (tC := .Case (.Var 2) [.Lam 0 (.Lam 0 tRp)])]
    · rfl
    · rw [MIR.lowerTotalExpr_case_of_list, lowerTotalExpr_var, hh₂, MIR.lowerTotalExprList_cons,
        MIR.lowerTotalExprList_nil, MIR.lowerTotalExpr_lam, MIR.lowerTotalExpr_lam, htRp]
      rfl
  intro ρ π henv hlen hπ hF
  obtain ⟨vl, hvl, ⟨ps, rfl⟩⟩ := pairKnowledge.var hl hF hd hil henv
  have hlenR := listRel_length hrR
  refine obsRefines_of_steps 3 3 ?_
  rw [steps_trans 2 1, steps_trans 2 1, case_var_steps hvl, case_var_steps hvl]
  simp only [steps]
  cases ps with
  | nil =>
    have hdisp : ∀ (π : Stack) (ρ : CekEnv) (alts : List Term),
        step (.ret (.caseScrutinee alts ρ :: π) (.VCon (Const.pairDataList []))) =
          if alts.length > 2 then .error else
            match alts[1]? with
            | some alt => .compute π ρ alt
            | none => .error := by
      intro π ρ alts
      cases e : alts[1]? <;> simp [step, constToTagAndFields, Const.pairDataList, e]
    rw [hdisp, hdisp]
    simp only [List.length_cons, hlenR, List.getElem?_cons_succ]
    split
    · exact obsRefines_refl _
    · rcases listRel_getElem? hrR 0 with ⟨e₁, e₂⟩ | ⟨x, y, e₁, e₂, hxy⟩
      · rw [e₁, e₂]; exact obsRefines_refl _
      · rw [e₁, e₂]; exact hxy ρ π henv hlen hπ hF
  | cons p ps' =>
    have hdisp : ∀ (π : Stack) (ρ : CekEnv) (alts : List Term),
        step (.ret (.caseScrutinee alts ρ :: π) (.VCon (Const.pairDataList (p :: ps')))) =
          if alts.length > 2 then .error else
            match alts[0]? with
            | some alt => .compute ([Frame.applyArg (.VCon (Const.pairData p)),
                Frame.applyArg (.VCon (Const.pairDataList ps'))] ++ π) ρ alt
            | none => .error := by
      intro π ρ alts
      cases e : alts[0]? <;> simp [step, constToTagAndFields, Const.pairDataList, e]
    rw [hdisp, hdisp]
    simp only [List.length_cons, hlenR, List.getElem?_cons_zero]
    split
    · exact obsRefines_refl _
    · refine obsRefines_of_steps 4 4 ?_
      rw [consAlt_steps, consAlt_steps]
      have htl : pairFamily.mem (.VCon (Const.pairDataList ps')) := ⟨ps', rfl⟩
      obtain ⟨henv₂, hlen₂⟩ := consAlt_env (c := Const.pairData p) henv hlen (pairFamily.list htl)
      have hF₂ := consAlt_facts (c := Const.pairData p) hF hn hk hh ht htl
      refine obsRefines_trans (hrC _ π henv₂ hlen₂ hπ hF₂) ?_
      have hhead : ((ρ.extend (.VCon (Const.pairData p))).extend (.VCon (Const.pairDataList ps'))).lookup 2 =
          some (.VCon (.Pair (.Data p.1, .Data p.2))) := rfl
      refine unbox_obs henv₂ hlen₂ hπ hhead (by simpa [Nat.add_assoc] using closed₀) ?_
      have wfx : ValueWellFormed (.VCon (.Data p.1)) := .vcon _
      have wfy : ValueWellFormed (.VCon (.Data p.2)) := .vcon _
      have henv₃ := envWellFormed_extend _ henv₂ hlen₂ wfx
      have hlen₃ : env.length + 2 + 1 ≤ (((ρ.extend (.VCon (Const.pairData p))).extend
          (.VCon (Const.pairDataList ps'))).extend (.VCon (.Data p.1))).length := by
        simp [CekEnv.extend, CekEnv.length] at hlen₂ ⊢; omega
      have henv₄ := envWellFormed_extend _ henv₃ hlen₃ wfy
      have hlen₄ : env.length + 2 + 1 + 1 ≤ ((((ρ.extend (.VCon (Const.pairData p))).extend
          (.VCon (Const.pairDataList ps'))).extend (.VCon (.Data p.1))).extend (.VCon (.Data p.2))).length := by
        simp [CekEnv.extend, CekEnv.length] at hlen₂ ⊢; omega
      have hfacts := component_facts (b := b) (x := p.1) (y := p.2) hF₂.1 hth hah
      simp only [List.length_cons] at hrRp
      exact hrRp _ π (by simpa [Nat.add_assoc] using henv₄) (by simpa [Nat.add_assoc] using hlen₄) hπ hfacts

end Moist.Verified.KnownLists
