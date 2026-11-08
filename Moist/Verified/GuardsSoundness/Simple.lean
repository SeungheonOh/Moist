import Moist.Verified.GuardsSoundness.Analysis
import Moist.Verified.GuardsSoundness.Kinds

variable [sv : Moist.CEK.SemVariant]

/-! # `chk` on lambdas, bindings, delays, constants and constructors -/

namespace Moist.Verified.Guards

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast
open Moist.Verified.KnownLists

/-! ## Lowered lists -/

omit sv in
theorem lowerList_get {env : List VarId} :
    ∀ {es : List Expr} {ts : List Term}, MIR.lowerTotalExprList env es = some ts →
      ∀ n : Nat, (∃ e t, es[n]? = some e ∧ ts[n]? = some t ∧ lowerTotalExpr env e = some t) ∨
        (es[n]? = none ∧ ts[n]? = none)
  | [], ts, h, n => by rw [MIR.lowerTotalExprList_nil] at h; cases h; exact .inr ⟨rfl, rfl⟩
  | e :: es, ts, h, n => by
    rw [MIR.lowerTotalExprList_cons] at h
    cases he : lowerTotalExpr env e <;> cases hes : MIR.lowerTotalExprList env es <;>
      simp [he, hes] at h
    subst h
    cases n with
    | zero => exact .inl ⟨e, _, rfl, rfl, he⟩
    | succ n => simpa using lowerList_get hes n

omit sv in
theorem lowerList_len {env : List VarId} :
    ∀ {es : List Expr} {ts : List Term}, MIR.lowerTotalExprList env es = some ts → ts.length = es.length
  | [], ts, h => by rw [MIR.lowerTotalExprList_nil] at h; cases h; rfl
  | a :: as, ts, h => by
    rw [MIR.lowerTotalExprList_cons] at h
    cases ha : lowerTotalExpr env a with
    | none => rw [ha] at h; cases h
    | some ta =>
      cases has : MIR.lowerTotalExprList env as with
      | none => rw [ha, has] at h; cases h
      | some tas =>
        rw [ha, has] at h; cases h
        simp [lowerList_len has]

omit sv in
/-- The source element lowered to a target element. -/
theorem lowerList_elem {env : List VarId} {es : List Expr} {ts : List Term}
    (h : MIR.lowerTotalExprList env es = some ts) {i : Nat} {t : Term} (ht : ts[i]? = some t) :
    ∃ e, es[i]? = some e ∧ lowerTotalExpr env e = some t := by
  rcases lowerList_get h i with ⟨e, t', he, ht', hl⟩ | ⟨_, hn⟩
  · rw [ht] at ht'; cases ht'; exact ⟨e, he, hl⟩
  · rw [ht] at hn; cases hn

omit sv in
theorem freshInList_get {avoid : List VarId} {es : List Expr} (h : freshInList avoid es = true)
    {i : Nat} {e : Expr} (he : es[i]? = some e) : freshIn avoid e = true :=
  freshInList_iff.mp h e (List.mem_of_getElem? he)

/-! ## Lambdas -/

theorem good_lam {n : Nat} (IH : ChkSound n) {c : TCtx} {v : VMode} {alt : Bool} {x : VarId}
    {b : Expr} (h : chk (n + 1) c v alt (.Lam x b) = true) {env : List VarId} {t : Term}
    (hd : EnvDistinct env) (hfr : freshIn env (.Lam x b) = true)
    (hlow : lowerTotalExpr env (.Lam x b) = some t) : Good c v alt env t := by
  simp only [chk, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨rfl, hrest⟩ := h
  obtain ⟨tb, htb, rfl⟩ := lowerTotalExpr_lam_some hlow
  simp only [freshIn, Bool.and_eq_true] at hfr
  intro ρ hρ fields hfs hf
  cases fields with
  | nil => exact .inr ⟨_, reaches_of_steps 2 rfl, trivial⟩
  | cons f fs =>
    cases alt with
    | false => cases hf rfl
    | true =>
      rcases hrest with h | ⟨hx, hb⟩
      · cases h
      cases hfs with
      | cons hfw hfs' =>
      refine Ends.of_reaches (reaches_of_steps 2 rfl) ?_
      exact IH c .term true b hb (x :: env) tb (hd.cons hfr.1) hfr.2 htb _ (hρ.extend hx hfw) fs hfs'
        (fun h => by cases h)

/-! ## Strict bindings -/

theorem good_let {n : Nat} (IH : ChkSound n) {c : TCtx} {v : VMode} {alt : Bool} {x : VarId}
    {r : Expr} {er : Bool} {rest : List (VarId × Expr × Bool)} {body : Expr}
    (h : chk (n + 1) c v alt (.Let ((x, r, er) :: rest) body) = true) {env : List VarId} {t : Term}
    (hd : EnvDistinct env) (hfr : freshIn env (.Let ((x, r, er) :: rest) body) = true)
    (hlow : lowerTotalExpr env (.Let ((x, r, er) :: rest) body) = some t) : Good c v alt env t := by
  simp only [chk, Bool.and_eq_true] at h
  obtain ⟨⟨hx, hr⟩, hb⟩ := h
  rw [lowerTotalExpr_let_cons] at hlow
  rw [freshIn_let_cons, freshIn_let_single] at hfr
  simp only [Bool.and_eq_true] at hfr
  obtain ⟨⟨hfr, hxe⟩, hfb⟩ := hfr
  obtain ⟨tr, tb, htr, htb, rfl⟩ := lowerTotalExpr_let_single_some hlow
  intro ρ hρ fields hfs hf
  refine Ends.of_reaches (reaches_of_steps 3 rfl) ?_
  rcases (IH c .term false r hr env tr hd hfr htr).term hρ with he | ⟨w, hw⟩
  · exact .inl (errs_on_stack he _)
  refine Ends.of_reaches (reaches_trans (halts_on_stack hw _) (reaches_of_steps 1 rfl)) ?_
  have hwf := halts_wellFormed hρ.wf hρ.len (MIR.lowerTotalExpr_closedAt htr) hw
  exact IH _ v alt _ hb (x :: env) tb (hd.cons hxe) hfb htb _
    (hρ.push hx hwf ⟨⟨tr, htr, hw⟩, hfr⟩) fields hfs hf

/-! ## Forcing -/

theorem good_force_delay {c : TCtx} {v : VMode} {alt : Bool} {env : List VarId} {tb : Term}
    (h : Good c v alt env tb) : Good c v alt env (.Force (.Delay tb)) := by
  intro ρ hρ fields hfs hf
  exact Ends.of_reaches (reaches_of_steps 3 rfl) (h ρ hρ fields hfs hf)

theorem good_ite {c : TCtx} {v : VMode} {alt : Bool} {env : List VarId} {tc ta tb : Term}
    (hc : Good c .term false env tc) (ha : Good c v alt env ta) (hb : Good c v alt env tb) :
    Good c v alt env
      (.Force (.Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse)) tc) (.Delay ta)) (.Delay tb))) := by
  intro ρ hρ fields hfs hf
  refine Ends.of_reaches (reaches_of_steps 8 rfl) ?_
  rcases hc.term hρ with he | ⟨w, hw⟩
  · exact .inl (errs_on_stack he _)
  refine Ends.of_reaches (halts_on_stack hw _) ?_
  cases w with
  | VCon k =>
    cases k with
    | Bool bv =>
      cases bv
      · exact Ends.of_reaches (reaches_of_steps 8 rfl) (hb ρ hρ fields hfs hf)
      · exact Ends.of_reaches (reaches_of_steps 8 rfl) (ha ρ hρ fields hfs hf)
    | _ => exact .inl (reaches_of_steps 7 rfl)
  | _ => exact .inl (reaches_of_steps 7 rfl)

/-! ## Constructors -/

theorem constrField_ends {ρ : CekEnv} {tag : Nat} :
    ∀ (ms : List Term) (m : Term) (done : List CekValue),
      (Errs ρ m ∨ ∃ w, Halts ρ m w) → (∀ t ∈ ms, Errs ρ t ∨ ∃ w, Halts ρ t w) →
      Reaches (.compute [.constrField tag done ms ρ] ρ m) .error ∨
        ∃ vs, Reaches (.compute [.constrField tag done ms ρ] ρ m) (.halt (.VConstr tag vs)) ∧
          vs.length = done.length + ms.length + 1
  | [], m, done, hm, _ => by
    rcases hm with he | ⟨w, hw⟩
    · exact .inl (errs_on_stack he _)
    · exact .inr ⟨(w :: done).reverse, reaches_trans (halts_on_stack hw _) (reaches_of_steps 2 rfl),
        by simp⟩
  | m' :: ms, m, done, hm, hms => by
    rcases hm with he | ⟨w, hw⟩
    · exact .inl (errs_on_stack he _)
    have h1 := reaches_trans (halts_on_stack hw _)
      (reaches_of_steps 1 rfl : Reaches (.ret [.constrField tag done (m' :: ms) ρ] w)
        (.compute [.constrField tag (w :: done) ms ρ] ρ m'))
    rcases constrField_ends ms m' (w :: done) (hms m' (.head _)) (fun t ht => hms t (.tail _ ht)) with
      he | ⟨vs, hvs, hl⟩
    · exact .inl (reaches_trans h1 he)
    · exact .inr ⟨vs, reaches_trans h1 hvs, by simp at hl ⊢; omega⟩

theorem constr_ends {ρ : CekEnv} {tag : Nat} {ts : List Term}
    (h : ∀ t ∈ ts, Errs ρ t ∨ ∃ w, Halts ρ t w) :
    Errs ρ (.Constr tag ts) ∨ ∃ vs, Halts ρ (.Constr tag ts) (.VConstr tag vs) ∧ vs.length = ts.length := by
  cases ts with
  | nil => exact .inr ⟨[], reaches_of_steps 2 rfl, rfl⟩
  | cons m ms =>
    rcases constrField_ends ms m [] (h m (.head _)) (fun t ht => h t (.tail _ ht)) with he | ⟨vs, hvs, hl⟩
    · exact .inl (reaches_trans (reaches_of_steps 1 rfl) he)
    · exact .inr ⟨vs, reaches_trans (reaches_of_steps 1 rfl) hvs, by simp at hl ⊢; omega⟩

end Moist.Verified.Guards
