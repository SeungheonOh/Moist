import Moist.Verified.GuardsSoundness.CallSound

/-! # `chk` is sound

`chk_sound`: when `chk n c v alt e` holds, the lowering of `e` in any
environment satisfying the invariant of `c` errors or returns a value of
mode `v`, also after being applied to fields when `alt` holds. In
particular `terminatesWith facts e` guarantees that `e` halts or errors in
every environment where the facts hold.
-/

namespace Moist.Verified.Guards

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast
open Moist.Verified.KnownLists

theorem delayBody_some {e b : Expr} (h : delayBody e = some b) : e = .Delay b := by
  unfold delayBody at h
  split at h
  · cases h; rfl
  · cases h

theorem good_force {n : Nat} (IH : ChkSound n) {c : TCtx} {v : VMode} {alt : Bool} {inner : Expr}
    (h : chk (n + 1) c v alt (.Force inner) = true) {env : List VarId} {t : Term}
    (hd : EnvDistinct env) (hfr : freshIn env (.Force inner) = true)
    (hlow : lowerTotalExpr env (.Force inner) = some t) : Good c v alt env t := by
  simp only [chk] at h
  split at h
  · rename_i body hb
    have := delayBody_some hb
    subst this
    obtain ⟨te, hte, rfl⟩ := lowerTotalExpr_force_some hlow
    obtain ⟨tb, htb, rfl⟩ := lowerTotalExpr_delay_some hte
    simp only [freshIn] at hfr
    exact good_force_delay (IH c v alt body h env tb hd hfr htb)
  · split at h
    · rename_i cnd a b hite
      have := iteView_some hite
      subst this
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hc, ha⟩, hb⟩ := h
      obtain ⟨te, hte, rfl⟩ := lowerTotalExpr_force_some hlow
      obtain ⟨t1, tbD, ht1, htbD, rfl⟩ := lowerTotalExpr_app_some hte
      obtain ⟨t2, taD, ht2, htaD, rfl⟩ := lowerTotalExpr_app_some ht1
      obtain ⟨tite, tc, htite, htc, rfl⟩ := lowerTotalExpr_app_some ht2
      obtain ⟨tB, htB, rfl⟩ := lowerTotalExpr_force_some htite
      rw [lowerTotalExpr_builtin] at htB; cases htB
      obtain ⟨tb, htb, rfl⟩ := lowerTotalExpr_delay_some htbD
      obtain ⟨ta, hta, rfl⟩ := lowerTotalExpr_delay_some htaD
      simp only [freshIn, Bool.and_eq_true] at hfr
      exact good_ite (IH c .term false cnd hc env tc hd hfr.1.1.2 htc)
        (IH c v alt a ha env ta hd hfr.1.2 hta) (IH c v alt b hb env tb hd hfr.2 htb)
    · split at h
      · rename_i b rem hp
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
        obtain ⟨⟨hh, he⟩, hm⟩ := h
        exact good_builtin_force IH hp (by revert hh; cases rem.head <;> decide) he hm hd hfr hlow
      · cases h

theorem good_app {n : Nat} (IH : ChkSound n) {c : TCtx} {v : VMode} {alt : Bool} {f a : Expr}
    (h : chk (n + 1) c v alt (.App f a) = true) {env : List VarId} {t : Term}
    (hd : EnvDistinct env) (hfr : freshIn env (.App f a) = true)
    (hlow : lowerTotalExpr env (.App f a) = some t) : Good c v alt env t := by
  simp only [chk] at h
  split at h
  · rename_i b rem hp
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hh, hf⟩, ha⟩, hm⟩ := h
    exact good_builtin_app IH hp (by revert hh; cases rem.head <;> decide) hf ha hm hd hfr hlow
  · simp only [Bool.and_eq_true] at h
    obtain ⟨hargs, hcall⟩ := h
    apply good_leaf
    intro ρ hρ
    exact callOK_sound IH hcall hargs hd hfr hlow hρ

theorem chk_sound : ∀ n, ChkSound n
  | 0 => fun _ _ _ _ h => by simp [chk] at h
  | n + 1 => by
    have IH := chk_sound n
    intro c v alt e h env t hd hfr hlow
    match e with
    | .Lam x b => exact good_lam IH h hd hfr hlow
    | .Let [] body =>
      simp only [chk] at h
      rw [lowerTotalExpr_let_nil] at hlow
      rw [freshIn_let_nil] at hfr
      exact IH c v alt body h env t hd hfr hlow
    | .Let ((x, r, er) :: rest) body => exact good_let IH h hd hfr hlow
    | .Case s alts => exact good_case IH h hd hfr hlow
    | .Force inner => exact good_force IH h hd hfr hlow
    | .App f a => exact good_app IH h hd hfr hlow
    | .Var x => exact good_var h hd hlow
    | .Lit (k, ty) => exact good_lit h hlow
    | .Error =>
      rw [lowerTotalExpr_error] at hlow; cases hlow
      exact good_error
    | .Builtin b => exact good_builtin h hlow
    | .Delay b => exact good_delay h hlow
    | .Fix f b => exact good_fix h hlow
    | .Constr tag fs => exact good_constr IH h hd hfr hlow

/-- `terminatesWith` is sound: the expression halts or errors wherever its facts hold. -/
theorem terminatesWith_sound {facts : List (VarId × Expr)} {e : Expr} (h : terminatesWith facts e = true)
    {env : List VarId} {t : Term} (hd : EnvDistinct env) (hfr : freshIn env e = true)
    (hlow : lowerTotalExpr env e = some t) {ρ : CekEnv} (hwf : EnvWellFormed env.length ρ)
    (hlen : env.length ≤ ρ.length) (hfacts : FactsHold PF facts env ρ) :
    Errs ρ t ∨ ∃ v, Halts ρ t v :=
  (chk_sound chkFuel _ _ _ _ h env t hd hfr hlow).term
    ⟨hwf, hlen, hfacts, fun _ h _ _ => by simp at h, fun _ h => by cases h⟩

end Moist.Verified.Guards
