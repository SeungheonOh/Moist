import Moist.Verified.CheckedBranchesSoundness.Relation
import Moist.Verified.ShapeFacts

/-! # Branches of list discriminators

* `chooseList l e (delay n)`: the suspension of `n` escapes only as the result
  of a successful `chooseList` on a non-empty list, so its body may assume
  that `l` is non-empty (`CheckedRel.choose`). The closure is created before
  the builtin runs, hence the fact is attached to the returned suspension, not
  to the environment in which the delay is evaluated.
* `case (nullList l) [n, e]`: the first alternative runs only after
  `nullList l` returned `false` (`CheckedRel.nullCase`).
* `let h = headList l; t = tailList l; b` becomes `case l [λh t. b]` when `l`
  is known to be non-empty (`CheckedRel.fusion`).
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines Moist.Verified.Contextual.Guarded Moist.Verified.TermObsRefinesWF

/-! ## The suspended non-empty branch of `chooseList` -/

/-- Supplying the non-empty branch to a `chooseList` state. The branch body
    is compared under the facts that hold once the builtin selected it. -/
theorem chooseDelay_factRefines {d : Nat} {F F' : CekEnv → Prop} {X tn tn' : Term}
    (closedN : closedAt d tn = true) (closedN' : closedAt d tn' = true)
    (hX : ∀ ρ w, F ρ → Halts ρ X w →
      ∃ ve vl, w = .VBuiltin .ChooseList [ve, vl] (.one .argV) ∧ (NonemptyList vl → F' ρ))
    (hn : FactRefines d F' tn tn') :
    FactRefines d F (.Apply X (.Delay tn)) (.Apply X (.Delay tn')) := by
  intro ρ π henv hlen hπ hF
  apply obsRefines_of_step
  show ObsRefines (.compute (.arg (.Delay tn) ρ :: π) ρ X) (.compute (.arg (.Delay tn') ρ :: π) ρ X)
  apply obsRefines_of_continuation
  intro w hw
  obtain ⟨ve, vl, rfl, hne⟩ := hX ρ w hF hw
  have hc := chooseList_eval tn ρ ve vl
  have hc' := chooseList_eval tn' ρ ve vl
  cases hnull : nullResult vl with
  | none =>
    rw [chooseResult_none hnull] at hc hc'
    exact obsRefines_of_errors
      ⟨3, by simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, hc]⟩
      ⟨3, by simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, hc']⟩
  | some b =>
    rw [chooseResult_of_null hnull] at hc hc'
    cases b with
    | true =>
      exact obsRefines_of_reaches (s₁' := .ret π ve) (s₂' := .ret π ve)
        ⟨3, by simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, hc]⟩
        ⟨3, by simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, hc']⟩
        (obsRefines_refl _)
    | false =>
      have hF' := hne (nonempty_of_null hnull)
      refine obsRefines_of_reaches (s₁' := .ret π (.VDelay tn ρ)) (s₂' := .ret π (.VDelay tn' ρ))
        ⟨3, by simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, hc]⟩
        ⟨3, by simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, hc']⟩ ?_
      have wf₁ : ValueWellFormed (.VDelay tn ρ) := .vdelay henv hlen closedN
      have wf₂ : ValueWellFormed (.VDelay tn' ρ) := .vdelay henv hlen closedN'
      refine obsRefines_ret_of_valueRel hπ wf₁ wf₂ fun k => ?_
      apply valueRel_delay (W := wfGuard) wf₁ wf₂
      intro j _
      exact eval_of_factRefines closedN hn (envRel_refl henv) henv hlen henv hlen hF'

theorem closedAt_var_of_lookup {env : List VarId} {l : VarId} {il : Nat}
    (hil : envLookupT env l = some il) : closedAt env.length (.Var (il + 1)) = true := by
  have := Moist.MIR.envLookupT_bound env l il hil
  simp [closedAt]; omega

theorem CheckedRel.choose {Γ : List (VarId × Expr)} {N : List VarId} {sel em em' ne ne' : Expr}
    {l : VarId} (hsel : resolveHead 64 Γ sel = .Force (.Force (.Builtin .ChooseList)))
    (hem : CheckedRel Γ N em em') (hne : CheckedRel Γ (l :: N) ne ne') :
    CheckedRel Γ N (.App (.App (.App sel (.Var l)) em) (.Delay ne))
      (.App (.App (.App sel (.Var l)) em') (.Delay ne')) := by
  intro env t hd hfresh hk hs hn hlow
  simp only [freshIn, Bool.and_eq_true] at hfresh
  obtain ⟨⟨_, hfem⟩, hfne⟩ := hfresh
  obtain ⟨ta, tdn, hta, htdn, rfl⟩ := lowerTotalExpr_app_some hlow
  obtain ⟨tne, htne, rfl⟩ := lowerTotalExpr_delay_some htdn
  obtain ⟨tb, tem, htb, htem, rfl⟩ := lowerTotalExpr_app_some hta
  obtain ⟨ts, tl, hts, htl, rfl⟩ := lowerTotalExpr_app_some htb
  obtain ⟨il, hil, rfl⟩ := lowerTotalExpr_var_some htl
  obtain ⟨tem', htem', hrem⟩ := hem env tem hd hfem hk hs hn htem
  have hn' : NamesBound (l :: N) env := hn.add (by simp [hil])
  obtain ⟨tne', htne', hrne⟩ := hne env tne hd hfne hk hs hn' htne
  refine ⟨.Apply (.Apply (.Apply ts (.Var (il + 1))) tem') (.Delay tne'), ?_, ?_⟩
  · rw [MIR.lowerTotalExpr_app, MIR.lowerTotalExpr_app, MIR.lowerTotalExpr_app, hts,
      lowerTotalExpr_var, hil, htem', MIR.lowerTotalExpr_delay, htne']
    rfl
  · have closedTs := MIR.lowerTotalExpr_closedAt hts
    have closedL := closedAt_var_of_lookup hil
    have closedTem := MIR.lowerTotalExpr_closedAt htem
    have closedTem' := MIR.lowerTotalExpr_closedAt htem'
    have closedTne := MIR.lowerTotalExpr_closedAt htne
    have closedTne' := MIR.lowerTotalExpr_closedAt htne'
    refine FactRefines.trans (t₂ := .Apply (.Apply (.Apply ts (.Var (il + 1))) tem') (.Delay tne)) ?_ ?_
    · exact factRefines_apply (factRefines_apply (FactRefines.refl _ _ _) hrem
        (by simp [closedAt, closedTs, closedL]) closedTem) (FactRefines.refl _ _ _)
        (by simp [closedAt, closedTs, closedL, closedTem']) (by simp [closedAt, closedTne])
    · apply chooseDelay_factRefines closedTne closedTne' _ hrne
      intro ρ w hF hw
      obtain ⟨wf, wa, hwf, _, happ⟩ := halts_apply hw
      obtain ⟨wf₀, wl, hwf₀, hwl, happ₀⟩ := halts_apply hwf
      have hselh := resolveHead_forced_halts 64 Γ sel hsel rfl hF.1 hd hts
      rw [halts_unique hwf₀ hselh] at happ₀
      have h₁ := apply_partial rfl happ₀
      subst h₁
      have h₂ := apply_partial rfl happ
      subst h₂
      refine ⟨wa, wl, rfl, fun hne => ⟨hF.1, hF.2.add ?_⟩⟩
      intro i hi
      rw [hil] at hi; cases hi
      exact ⟨wl, halts_var hwl, hne⟩

/-! ## The non-empty alternative of a `nullList` discriminator -/

theorem CheckedRel.nullCase {Γ : List (VarId × Expr)} {N : List VarId} {sel ne ne' em em' : Expr}
    {l : VarId} (hsel : resolveHead 64 Γ sel = .Force (.Builtin .NullList))
    (hne : CheckedRel Γ (l :: N) ne ne') (hem : CheckedRel Γ N em em') :
    CheckedRel Γ N (.Case (.App sel (.Var l)) [ne, em]) (.Case (.App sel (.Var l)) [ne', em']) := by
  intro env t hd hfresh hk hs hn hlow
  simp only [freshIn, freshInList, Bool.and_eq_true] at hfresh
  obtain ⟨_, hfne, hfem, _⟩ := hfresh
  obtain ⟨ts, tne, tem, hts, htne, htem, rfl⟩ := lowerTotalExpr_case2_some hlow
  obtain ⟨tsel, tl, htsel, htl, rfl⟩ := lowerTotalExpr_app_some hts
  obtain ⟨il, hil, rfl⟩ := lowerTotalExpr_var_some htl
  have hn' : NamesBound (l :: N) env := hn.add (by simp [hil])
  obtain ⟨tne', htne', hrne⟩ := hne env tne hd hfne hk hs hn' htne
  obtain ⟨tem', htem', hrem⟩ := hem env tem hd hfem hk hs hn htem
  refine ⟨.Case (.Apply tsel (.Var (il + 1))) [tne', tem'], ?_, ?_⟩
  · rw [MIR.lowerTotalExpr_case_of_list, hts, MIR.lowerTotalExprList_cons, htne',
      MIR.lowerTotalExprList_cons, htem', MIR.lowerTotalExprList_nil]
    rfl
  · intro ρ π henv hlen hπ hF
    apply obsRefines_of_step
    show ObsRefines (.compute (.caseScrutinee [tne, tem] ρ :: π) ρ (.Apply tsel (.Var (il + 1))))
      (.compute (.caseScrutinee [tne', tem'] ρ :: π) ρ (.Apply tsel (.Var (il + 1))))
    apply obsRefines_of_continuation
    intro v hv
    have hil_lt := Moist.MIR.envLookupT_bound env l il hil
    obtain ⟨vl, hvl, _⟩ := envWellFormed_lookup env.length henv (n := il + 1) (by omega) (by omega)
    have hres : resolveHead 65 Γ (.App sel (.Var l)) = .App (.Force (.Builtin .NullList)) (.Var l) := by
      rw [resolveHead_app, hsel]
    obtain ⟨hiff, _⟩ := resolveHead_unary 65 Γ (.App sel (.Var l)) hres rfl hF.1 hd hts hil hvl
    have heval := (hiff v).mp hv
    rw [nullList_eval] at heval
    cases hnull : nullResult vl with
    | none => rw [hnull] at heval; cases heval
    | some b =>
      rw [hnull] at heval
      simp only [Option.map_some, Option.some.injEq] at heval
      subst heval
      cases b with
      | true =>
        apply obsRefines_of_step
        simp only [step, constToTagAndFields]
        exact hrem ρ π henv hlen hπ hF
      | false =>
        apply obsRefines_of_step
        simp only [step, constToTagAndFields]
        refine hrne ρ π henv hlen hπ ⟨hF.1, hF.2.add ?_⟩
        intro i hi
        rw [hil] at hi; cases hi
        exact ⟨vl, hvl, nonempty_of_null hnull⟩

/-! ## Head and tail of a non-empty list -/

theorem lowerTotalExpr_fusedNonempty {env : List VarId} {l h t : VarId} {B' : Expr} {il : Nat}
    {tB' : Term} (hil : envLookupT env l = some il)
    (htB' : lowerTotalExpr (t :: h :: env) B' = some tB') :
    lowerTotalExpr env (.Case (.Var l) [.Lam h (.Lam t B')]) =
      some (.Case (.Var (il + 1)) [.Lam 0 (.Lam 0 tB')]) := by
  rw [MIR.lowerTotalExpr_case_of_list, lowerTotalExpr_var, hil]
  simp only [Option.map_some]
  rw [MIR.lowerTotalExprList_cons, MIR.lowerTotalExpr_lam, MIR.lowerTotalExpr_lam, htB']
  simp only [Option.map_some]
  rw [MIR.lowerTotalExprList_nil]
  rfl

theorem fusedNonempty_steps {ρ : CekEnv} {π : Stack} {n : Nat} {vl : CekValue} {b : Term}
    (hvl : ρ.lookup n = some vl) :
    ∀ hv tv, (∃ c cs, vl = .VCon (.ConstList (c :: cs)) ∧ hv = .VCon c ∧ tv = .VCon (.ConstList cs)) ∨
      (∃ d ds, vl = .VCon (.ConstDataList (d :: ds)) ∧ hv = .VCon (.Data d) ∧
        tv = .VCon (.ConstDataList ds)) →
    Reaches (.compute π ρ (.Case (.Var n) [.Lam 0 (.Lam 0 b)]))
      (.compute π ((ρ.extend hv).extend tv) b) := by
  intro hv tv h
  rcases h with ⟨c, cs, rfl, rfl, rfl⟩ | ⟨d, ds, rfl, rfl, rfl⟩
  · exact ⟨7, by simp [steps, step, hvl, constToTagAndFields, CekEnv.extend]⟩
  · exact ⟨7, by simp [steps, step, hvl, constToTagAndFields, CekEnv.extend]⟩

theorem CheckedRel.fusion {Γ : List (VarId × Expr)} {N : List VarId} {h t : VarId}
    {hr tr B B' : Expr} {he te : Bool} {l l' : VarId}
    (hhead : resolveHead 64 Γ hr = .App (.Force (.Builtin .HeadList)) (.Var l))
    (htail : resolveHead 64 Γ tr = .App (.Force (.Builtin .TailList)) (.Var l'))
    (hl : (l == l') = true) (hnon : N.contains l = true)
    (hB : CheckedRel ((t, tr) :: (h, hr) :: Γ) N B B') :
    CheckedRel Γ N (.Let [(h, hr, he)] (.Let [(t, tr, te)] B)) (.Case (.Var l) [.Lam h (.Lam t B')]) := by
  intro env t₀ hd hfresh hk hs hn hlow
  rw [freshIn_let_single] at hfresh
  simp only [Bool.and_eq_true] at hfresh
  obtain ⟨⟨_, hh⟩, hfrest⟩ := hfresh
  rw [freshIn_let_single] at hfrest
  simp only [Bool.and_eq_true] at hfrest
  obtain ⟨⟨_, ht⟩, hfB⟩ := hfrest
  obtain ⟨thr, tX, hthr, htX, rfl⟩ := lowerTotalExpr_let_single_some hlow
  obtain ⟨ttr, tB, httr, htB, rfl⟩ := lowerTotalExpr_let_single_some htX
  have hlb := resolveHead_app_var_bound 64 Γ hr hhead hs hd (by simp [hthr])
  obtain ⟨il, hil⟩ : ∃ il, envLookupT env l = some il := Option.isSome_iff_exists.mp hlb
  have hnh := find?_none_of_unbound hk hh
  have hd₁ := hd.cons hh
  have hk₁ := hk.cons h
  have hnt := find?_none_of_unbound hk₁ ht
  have hd₂ := hd₁.cons ht
  have hk₂ : KeysBound ((t, tr) :: (h, hr) :: Γ) (t :: h :: env) := by
    intro entry hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | rfl | hmem
    · simp [envLookupT_cons, varId_beq_self]
    · rw [envLookupT_cons]; split
      · rfl
      · simp [envLookupT_cons, varId_beq_self]
    · exact hk₁.cons t entry hmem
  have hs₂ : FactsScoped ((t, tr) :: (h, hr) :: Γ) (t :: h :: env) :=
    (hs.push (x := h) (by simp [hthr])).push (by simp [httr])
  have hn₁ := hn.cons h
  have hn₂ := hn₁.cons t
  obtain ⟨tB', htB', hrB⟩ := hB (t :: h :: env) tB hd₂ hfB hk₂ hs₂ hn₂ htB
  refine ⟨_, lowerTotalExpr_fusedNonempty hil htB', ?_⟩
  intro ρ π henv hlen hπ hF
  obtain ⟨vl, hvl, hvne⟩ := hF.2 l hnon il hil
  obtain ⟨hiffH, _⟩ := resolveHead_unary 64 Γ hr hhead rfl hF.1 hd hthr hil hvl
  have hl' : envLookupT (h :: env) l' = some (il + 1) := by
    rw [← envLookupT_congr hl, envLookupT_cons]
    have hhl : (h == l) = false := by
      cases hc : (h == l)
      · rfl
      · rw [envLookupT_congr hc] at hh; simp [hil] at hh
    simp [hhl, hil]
  have nonempty : ∀ hv tv : CekValue,
      ((∃ c cs, vl = .VCon (.ConstList (c :: cs)) ∧ hv = .VCon c ∧ tv = .VCon (.ConstList cs)) ∨
        (∃ d ds, vl = .VCon (.ConstDataList (d :: ds)) ∧ hv = .VCon (.Data d) ∧
          tv = .VCon (.ConstDataList ds))) →
      ObsRefines (.compute π ρ (.Apply (.Lam 0 (.Apply (.Lam 0 tB) ttr)) thr))
        (.compute π ρ (.Case (.Var (il + 1)) [.Lam 0 (.Lam 0 tB')])) := by
    intro hv tv hshape
    have hhead_eval : evalBuiltin .HeadList [vl] = some hv := by
      rcases hshape with ⟨c, cs, rfl, rfl, rfl⟩ | ⟨d, ds, rfl, rfl, rfl⟩ <;> rfl
    have htail_eval : evalBuiltin .TailList [vl] = some tv := by
      rcases hshape with ⟨c, cs, rfl, rfl, rfl⟩ | ⟨d, ds, rfl, rfl, rfl⟩ <;> rfl
    have hthr_halts : Halts ρ thr hv := (hiffH hv).mpr hhead_eval
    have hvwf := halts_wellFormed henv hlen (MIR.lowerTotalExpr_closedAt hthr) hthr_halts
    have hF₁ : FactsHold Produces Γ (h :: env) (ρ.extend hv) := FactsHold.extend hv hF.1 hnh
    obtain ⟨hiffT, _⟩ := resolveHead_unary 64 Γ tr htail rfl hF₁ hd₁ httr hl' (by simpa using hvl)
    have httr_halts : Halts (ρ.extend hv) ttr tv := (hiffT tv).mpr htail_eval
    have henv₁ := envWellFormed_extend env.length henv hlen hvwf
    have hlen₁ : env.length + 1 ≤ (ρ.extend hv).length := by
      simp [CekEnv.extend, CekEnv.length]; omega
    have htvwf := halts_wellFormed henv₁ hlen₁ (by simpa using MIR.lowerTotalExpr_closedAt httr)
      httr_halts
    have hF₂ : CheckedFacts ((t, tr) :: (h, hr) :: Γ) N (t :: h :: env) ((ρ.extend hv).extend tv) :=
      ⟨(hF.1.push ⟨thr, hthr, hthr_halts⟩).push ⟨ttr, httr, httr_halts⟩,
        (hF.2.extend hv hn hh).extend tv hn₁ ht⟩
    refine obsRefines_of_reaches (reaches_trans (let_steps hthr_halts) (let_steps httr_halts))
      (fusedNonempty_steps hvl hv tv hshape) ?_
    exact hrB _ π (envWellFormed_extend (env.length + 1) henv₁ hlen₁ htvwf)
      (by simp [CekEnv.extend, CekEnv.length]; omega) hπ hF₂
  cases vl with
  | VCon c =>
    cases c with
    | ConstList xs =>
      cases xs with
      | nil => exact absurd hvne id
      | cons c cs => exact nonempty _ _ (.inl ⟨c, cs, rfl, rfl, rfl⟩)
    | ConstDataList xs =>
      cases xs with
      | nil => exact absurd hvne id
      | cons d ds => exact nonempty _ _ (.inr ⟨d, ds, rfl, rfl, rfl⟩)
    | _ => exact absurd hvne id
  | _ => exact absurd hvne id

end Moist.Verified.ShapeFacts
