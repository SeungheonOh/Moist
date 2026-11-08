import Moist.Verified.GuardsSoundness.Simple

variable [sv : Moist.CEK.SemVariant]

/-! # `chk` on names, constants, builtin applications and constructors -/

namespace Moist.Verified.Guards

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast
open Moist.Verified.KnownLists

omit sv in
theorem KindV.inert : ∀ {k : Kind} {w : CekValue}, k ≠ .unknown → KindV k w → InertV w
  | .bool, _, _, ⟨_, h⟩ => by subst h; trivial
  | .int, _, _, ⟨_, h⟩ => by subst h; trivial
  | .list, w, _, h => by
    cases w with
    | VCon _ => trivial
    | _ => simp [KindV, ListValue] at h
  | .pair, _, _, ⟨_, _, h⟩ => by subst h; trivial
  | .constrs _, _, _, ⟨_, _, h, _⟩ => by subst h; trivial
  | .unknown, _, h, _ => absurd rfl h

theorem good_var {n : Nat} {c : TCtx} {v : VMode} {alt : Bool} {x : VarId}
    (h : chk (n + 1) c v alt (.Var x) = true) {env : List VarId} {t : Term}
    (hd : EnvDistinct env) (hlow : lowerTotalExpr env (.Var x) = some t) : Good c v alt env t := by
  simp only [chk] at h
  apply good_leaf
  intro ρ hρ
  obtain ⟨i, hi, rfl⟩ := lowerTotalExpr_var_some hlow
  obtain ⟨w, hw⟩ := halts_var_wf hρ.wf (envLookupT_lt hi)
  refine .inr ⟨w, hw, ?_⟩
  have hk := scrutineeKind_sound hρ hd hlow hw
  generalize (if alt = true then v.applied else v) = m at h ⊢
  cases m with
  | term => trivial
  | inert =>
    simp only [bne_iff_ne, ne_eq] at h
    exact KindV.inert h hk
  | bool =>
    simp only [beq_iff_eq] at h
    rw [h] at hk; exact hk
  | constrs _ => cases h

theorem good_lit {n : Nat} {c : TCtx} {v : VMode} {alt : Bool} {k : Const} {ty : BuiltinType}
    (h : chk (n + 1) c v alt (.Lit (k, ty)) = true) {env : List VarId} {t : Term}
    (hlow : lowerTotalExpr env (.Lit (k, ty)) = some t) : Good c v alt env t := by
  rw [lowerTotalExpr_lit] at hlow; cases hlow
  apply good_leaf
  intro ρ _
  refine .inr ⟨.VCon k, halts_constant_of k ty, ?_⟩
  cases alt <;> cases v <;> cases k <;> simp_all [chk, VMode.applied, ModeV, InertV]

theorem good_error {c : TCtx} {v : VMode} {alt : Bool} {env : List VarId} :
    Good c v alt env .Error := by
  intro ρ _ fields _ _
  exact .inl (reaches_of_steps 1 rfl)

theorem good_value {c : TCtx} {v : VMode} {alt : Bool} {env : List VarId} {t : Term}
    (hm : (if alt = true then v.applied else v) = .term)
    (h : ∀ ρ, Inv c env ρ → ∃ w, Halts ρ t w) : Good c v alt env t := by
  apply good_leaf
  intro ρ hρ
  obtain ⟨w, hw⟩ := h ρ hρ
  exact .inr ⟨w, hw, by rw [hm]; trivial⟩

theorem good_builtin {n : Nat} {c : TCtx} {v : VMode} {alt : Bool} {b : BuiltinFun}
    (h : chk (n + 1) c v alt (.Builtin b) = true) {env : List VarId} {t : Term}
    (hlow : lowerTotalExpr env (.Builtin b) = some t) : Good c v alt env t := by
  simp only [chk, beq_iff_eq] at h
  rw [lowerTotalExpr_builtin] at hlow; cases hlow
  exact good_value h fun _ _ => ⟨_, reaches_of_steps 2 rfl⟩

theorem good_delay {n : Nat} {c : TCtx} {v : VMode} {alt : Bool} {b : Expr}
    (h : chk (n + 1) c v alt (.Delay b) = true) {env : List VarId} {t : Term}
    (hlow : lowerTotalExpr env (.Delay b) = some t) : Good c v alt env t := by
  simp only [chk, beq_iff_eq] at h
  obtain ⟨tb, _, rfl⟩ := lowerTotalExpr_delay_some hlow
  exact good_value h fun _ _ => ⟨_, reaches_of_steps 2 rfl⟩

theorem good_fix {n : Nat} {c : TCtx} {v : VMode} {alt : Bool} {f : VarId} {b : Expr}
    (h : chk (n + 1) c v alt (.Fix f b) = true) {env : List VarId} {t : Term}
    (hlow : lowerTotalExpr env (.Fix f b) = some t) : Good c v alt env t := by
  cases b with
  | Lam x body =>
    simp only [chk, beq_iff_eq] at h
    rw [lowerTotalExpr_fix_lam_canonical] at hlow
    cases hb : lowerTotal _ (expandFix body) with
    | none => rw [hb] at hlow; cases hlow
    | some tb =>
      rw [hb] at hlow; cases hlow
      exact good_value h fun ρ _ => ⟨_, reaches_trans ⟨16, fix_steps tb [] ρ⟩ (reaches_of_steps 1 rfl)⟩
  | _ =>
    rw [MIR.lowerTotalExpr_fix_nonlam_none env f _ (by intros; simp)] at hlow
    cases hlow

theorem good_constr {n : Nat} (IH : ChkSound n) {c : TCtx} {v : VMode} {alt : Bool} {tag : Nat}
    {fs : List Expr} (h : chk (n + 1) c v alt (.Constr tag fs) = true) {env : List VarId} {t : Term}
    (hd : EnvDistinct env) (hfr : freshIn env (.Constr tag fs) = true)
    (hlow : lowerTotalExpr env (.Constr tag fs) = some t) : Good c v alt env t := by
  simp only [chk, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hm, hfs⟩ := h
  simp only [freshIn] at hfr
  rw [MIR.lowerTotalExpr_constr_of_list] at hlow
  cases hts : MIR.lowerTotalExprList env fs with
  | none => rw [hts] at hlow; cases hlow
  | some ts =>
    rw [hts] at hlow; cases hlow
    apply good_leaf
    intro ρ hρ
    have hall : ∀ tf ∈ ts, Errs ρ tf ∨ ∃ w, Halts ρ tf w := by
      intro tf htf
      obtain ⟨i, hi⟩ := List.getElem?_of_mem htf
      obtain ⟨e, he, hle⟩ := lowerList_elem hts hi
      exact (IH c .term false e (hfs e (List.mem_of_getElem? he)) env tf hd
        (freshInList_get hfr he) hle).term hρ
    rcases constr_ends hall with he | ⟨vs, hvs, hl⟩
    · exact .inl he
    refine .inr ⟨_, hvs, ?_⟩
    generalize (if alt = true then v.applied else v) = m at hm ⊢
    cases m with
    | term => trivial
    | inert => trivial
    | bool => simp at hm
    | constrs ks =>
      refine ⟨tag, vs, rfl, fun k hk => ?_⟩
      simp only [hk, beq_iff_eq] at hm
      rw [hl, lowerList_len hts, hm]

/-! ## Builtin applications -/

theorem good_builtin_app {n : Nat} (IH : ChkSound n) {c : TCtx} {v : VMode} {alt : Bool}
    {f a : Expr} {b : BuiltinFun} {rem : ExpectedArgs}
    (hp : builtinProtocolAfterSuccess (resolveHead kindFuel c.facts f) = some (b, rem))
    (hh : rem.head = .argV) (hf : chk n c .term false f = true) (ha : chk n c .term false a = true)
    (hm : (if alt = true then v.applied else v) = .term ∨
      (rem.isFinal = true ∧ builtinCovers b (if alt = true then v.applied else v) = true))
    {env : List VarId} {t : Term} (hd : EnvDistinct env) (hfr : freshIn env (.App f a) = true)
    (hlow : lowerTotalExpr env (.App f a) = some t) : Good c v alt env t := by
  obtain ⟨tf, ta, htf, hta, rfl⟩ := lowerTotalExpr_app_some hlow
  simp only [freshIn, Bool.and_eq_true] at hfr
  apply good_leaf
  intro ρ hρ
  have hstart : Reaches (.compute [] ρ (.Apply tf ta)) (.compute [.arg ta ρ] ρ tf) :=
    reaches_of_steps 1 rfl
  rcases (IH c .term false f hf env tf hd hfr.1 htf).term hρ with he | ⟨wf, hwf⟩
  · exact .inl (reaches_trans hstart (errs_on_stack he _))
  have hstate := resolveHead_protocol pf_produces _ _ _ hp hρ.facts hd htf hwf
  have h2 := reaches_trans hstart (reaches_trans (halts_on_stack hwf _) (reaches_of_steps 1 rfl))
  rcases (IH c .term false a ha env ta hd hfr.2 hta).term hρ with he | ⟨wa, hwa⟩
  · exact .inl (reaches_trans h2 (errs_on_stack he _))
  have h3 := reaches_trans h2 (halts_on_stack hwa _)
  rcases apply_state_ends (wa := wa) hstate hh hm with he | ⟨r, hr, hmr⟩
  · exact .inl (reaches_trans h3 he)
  · exact .inr ⟨r, reaches_trans h3 hr, hmr⟩

theorem good_builtin_force {n : Nat} (IH : ChkSound n) {c : TCtx} {v : VMode} {alt : Bool}
    {e : Expr} {b : BuiltinFun} {rem : ExpectedArgs}
    (hp : builtinProtocolAfterSuccess (resolveHead kindFuel c.facts e) = some (b, rem))
    (hh : rem.head = .argQ) (he : chk n c .term false e = true)
    (hm : (if alt = true then v.applied else v) = .term ∨
      (rem.isFinal = true ∧ builtinCovers b (if alt = true then v.applied else v) = true))
    {env : List VarId} {t : Term} (hd : EnvDistinct env) (hfr : freshIn env (.Force e) = true)
    (hlow : lowerTotalExpr env (.Force e) = some t) : Good c v alt env t := by
  obtain ⟨te, hte, rfl⟩ := lowerTotalExpr_force_some hlow
  simp only [freshIn] at hfr
  apply good_leaf
  intro ρ hρ
  have hstart : Reaches (.compute [] ρ (.Force te)) (.compute [.force] ρ te) := reaches_of_steps 1 rfl
  rcases (IH c .term false e he env te hd hfr hte).term hρ with herr | ⟨w, hw⟩
  · exact .inl (reaches_trans hstart (errs_on_stack herr _))
  have hstate := resolveHead_protocol pf_produces _ _ _ hp hρ.facts hd hte hw
  have h2 := reaches_trans hstart (halts_on_stack hw _)
  rcases force_state_ends hstate hh hm with herr | ⟨r, hr, hmr⟩
  · exact .inl (reaches_trans h2 herr)
  · exact .inr ⟨r, reaches_trans h2 hr, hmr⟩

end Moist.Verified.Guards
