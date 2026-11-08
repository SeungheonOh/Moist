import Moist.Verified.GuardsSoundness.Cases

/-! # Calls: spines, lambda chains and the size bound of a recursive function -/

namespace Moist.Verified.Guards

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast
open Moist.Verified.KnownLists

/-! ## Application spines -/

theorem appSpine_app (f a : Expr) : appSpine (.App f a) = ((appSpine f).1, (appSpine f).2 ++ [a]) := rfl

theorem appSpine_lower : ∀ (e : Expr) {env : List VarId} {t : Term}, lowerTotalExpr env e = some t →
    ∃ th targs, lowerTotalExpr env (appSpine e).1 = some th ∧
      MIR.lowerTotalExprList env (appSpine e).2 = some targs ∧
      ∀ ρ π, Reaches (.compute π ρ t) (.compute (targs.map (fun ta => Frame.arg ta ρ) ++ π) ρ th)
  | .App f a, env, t, h => by
    obtain ⟨tf, ta, htf, hta, rfl⟩ := lowerTotalExpr_app_some h
    obtain ⟨th, targs, hth, htargs, hr⟩ := appSpine_lower f htf
    refine ⟨th, targs ++ [ta], by rw [appSpine_app]; exact hth, ?_, fun ρ π => ?_⟩
    · rw [appSpine_app]
      exact lowerList_append htargs hta
    · refine reaches_trans (reaches_of_steps 1 rfl) ?_
      simpa using hr ρ (.arg ta ρ :: π)
  | .Var _, _, t, h | .Lit _, _, t, h | .Builtin _, _, t, h | .Error, _, t, h | .Lam _ _, _, t, h
  | .Fix _ _, _, t, h | .Force _, _, t, h | .Delay _, _, t, h | .Constr _ _, _, t, h
  | .Case _ _, _, t, h | .Let _ _, _, t, h =>
    ⟨t, [], h, by simp [appSpine, MIR.lowerTotalExprList_nil], fun _ _ => by simpa using reaches_refl _⟩
where
  lowerList_append {env : List VarId} : ∀ {es : List Expr} {ts : List Term} {a : Expr} {ta : Term},
      MIR.lowerTotalExprList env es = some ts → lowerTotalExpr env a = some ta →
      MIR.lowerTotalExprList env (es ++ [a]) = some (ts ++ [ta])
    | [], ts, a, ta, h, ha => by
      rw [MIR.lowerTotalExprList_nil] at h; cases h
      simp [MIR.lowerTotalExprList_cons, MIR.lowerTotalExprList_nil, ha]
    | e :: es, ts, a, ta, h, ha => by
      rw [MIR.lowerTotalExprList_cons] at h
      cases he : lowerTotalExpr env e with
      | none => rw [he] at h; cases h
      | some te =>
        cases hes : MIR.lowerTotalExprList env es with
        | none => rw [he, hes] at h; cases h
        | some tes =>
          rw [he, hes] at h; cases h
          rw [List.cons_append, MIR.lowerTotalExprList_cons, he, lowerList_append hes ha]
          rfl

theorem appSpine_fresh : ∀ (e : Expr) {env : List VarId}, freshIn env e = true →
    freshIn env (appSpine e).1 = true ∧ ∀ a ∈ (appSpine e).2, freshIn env a = true
  | .App f a, env, h => by
    simp only [freshIn, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := appSpine_fresh f h.1
    rw [appSpine_app]
    refine ⟨h1, fun b hb => ?_⟩
    rcases List.mem_append.mp hb with hb | hb
    · exact h2 b hb
    · simp at hb; subst hb; exact h.2
  | .Var _, _, h | .Lit _, _, h | .Builtin _, _, h | .Error, _, h | .Lam _ _, _, h
  | .Fix _ _, _, h | .Force _, _, h | .Delay _, _, h | .Constr _ _, _, h
  | .Case _ _, _, h | .Let _ _, _, h => ⟨h, fun _ hb => by simp [appSpine] at hb⟩

/-- Evaluating a call whose head returns a function with known calls. -/
theorem call_ends {ρ : CekEnv}
    {t th : Term} {targs : List Term} {f : CekValue} {v : VMode} {Ps : List (CekValue → Prop)}
    (hreach : Reaches (.compute [] ρ t) (.compute (targs.map (fun ta => Frame.arg ta ρ)) ρ th))
    (hf : Halts ρ th f) (hcalls : CallsOK v Ps f) (hlen : targs.length = Ps.length)
    (hargs : ∀ (i : Nat) (ta : Term) (P : CekValue → Prop), targs[i]? = some ta → Ps[i]? = some P →
      Errs ρ ta ∨ ∃ w, Halts ρ ta w ∧ ValueWellFormed w ∧ P w) :
    Errs ρ t ∨ ∃ r, Halts ρ t r ∧ ModeV v r := by
  have := ends_args (m := v) targs Ps f hlen hargs hcalls
  rcases Ends.of_reaches (reaches_trans hreach (halts_on_stack hf _)) this with he | ⟨r, hr, hm⟩
  · exact .inl he
  · exact .inr ⟨r, hr, hm⟩

/-! ## Lambda chains -/

def lamChain (bs : List VarId) (tb : Term) : Term := (bs.map fun _ => ()).foldr (fun _ acc => .Lam 0 acc) tb

theorem lamChain_cons (b : VarId) (bs : List VarId) (tb : Term) :
    lamChain (b :: bs) tb = .Lam 0 (lamChain bs tb) := rfl

/-- A closure over a chain of lambdas: applying it to one argument per
    lambda runs the body in the extended environment. -/
theorem callsOK_lams {v : VMode} : ∀ (bs : List VarId) (Ps : List (CekValue → Prop)) (tb : Term)
    (ρ : CekEnv), Ps.length = bs.length + 1 →
    (∀ ws, ws.length = Ps.length → ValueListWellFormed ws →
      (∀ (i : Nat) (w : CekValue) (P : CekValue → Prop), ws[i]? = some w → Ps[i]? = some P → P w) →
      Ends v (.compute [] (extendAll ρ ws) tb)) →
    CallsOK v Ps (.VLam (lamChain bs tb) ρ)
  | [], [P], tb, ρ, _, h => by
    intro w hw hP
    have := h [w] rfl (.cons hw .nil) (fun i w' P' h1 h2 => by
      cases i with
      | zero => simp at h1 h2; subst h1; subst h2; exact hP
      | succ i => simp at h1)
    exact Ends.of_reaches (reaches_of_steps 1 rfl) this
  | _ :: bs, P :: Ps, tb, ρ, hlen, h => by
    intro w hw hP
    refine .inr ⟨_, reaches_of_steps 3 rfl, ?_⟩
    exact callsOK_lams bs Ps tb (ρ.extend w) (by simpa using hlen) fun ws hl hws hP' =>
      h (w :: ws) (by simp [hl]) (.cons hw hws) fun i w' P' h1 h2 => by
        cases i with
        | zero => simp at h1 h2; subst h1; subst h2; exact hP
        | succ i => exact hP' i w' P' (by simpa using h1) (by simpa using h2)
  | [], [], _, _, h, _ | [], _ :: _ :: _, _, _, h, _ | _ :: _, [], _, _, h, _ => by
    simp at h

/-! ## Calls with an unbounded size -/

theorem callsOK_relax {v : VMode} : ∀ (Qs : List (CekValue → Prop)) (Ps : Nat → List (CekValue → Prop))
    (f : CekValue), (∀ m, (Ps m).length = Qs.length) →
    (∀ (i : Nat) (Q : CekValue → Prop), Qs[i]? = some Q → ∀ w, Q w →
      ∃ m₀, ∀ m, m₀ ≤ m → ∀ P, (Ps m)[i]? = some P → P w) →
    (∀ m, CallsOK v (Ps m) f) → CallsOK v Qs f
  | [], Ps, f, hlen, _, h => by
    have := h 0
    have h0 := hlen 0
    cases hP : Ps 0 with
    | nil => rw [hP] at this; exact this
    | cons _ _ => rw [hP] at h0; simp at h0
  | Q :: Qs, Ps, f, hlen, hQ, h => by
    intro w hw hq
    obtain ⟨m₀, hm₀⟩ := hQ 0 Q rfl w hq
    have step : ∀ m, m₀ ≤ m → Reaches (.ret [.funV f] w) .error ∨
        ∃ r, Reaches (.ret [.funV f] w) (.halt r) ∧ CallsOK v (Ps m).tail r := by
      intro m hm
      have hl := hlen m
      have hc := h m
      cases hPs : Ps m with
      | nil => rw [hPs] at hl; simp at hl
      | cons P Ps' =>
        rw [hPs] at hc
        exact hc w hw (hm₀ m hm P (by rw [hPs]; rfl))
    rcases step m₀ (Nat.le_refl _) with he | ⟨r, hr, _⟩
    · exact .inl he
    refine .inr ⟨r, hr, ?_⟩
    refine callsOK_relax Qs (fun m => (Ps (m + m₀)).tail) r (fun m => by simp [hlen]) ?_ ?_
    · intro i Q' hi w' hq'
      obtain ⟨m₁, hm₁⟩ := hQ (i + 1) Q' (by simpa using hi) w' hq'
      refine ⟨m₁, fun m hm P hP => hm₁ (m + m₀) (by omega) P ?_⟩
      rw [← List.getElem?_tail] ; exact hP
    · intro m
      rcases step (m + m₀) (by omega) with he | ⟨r', hr', hc⟩
      · exact absurd hr (fun h' => halt_not_error h' he)
      · have : r' = r := by
          have := terminal_unique (.inr ⟨r', rfl⟩) (.inr ⟨r, rfl⟩) hr' hr
          cases this; rfl
        subst this; exact hc

/-- Functions that step to the same state on every argument have the same calls. -/
theorem callsOK_transfer {v : VMode} {f g : CekValue} {P : CekValue → Prop} {Ps : List (CekValue → Prop)}
    (hfg : ∀ w, ∃ s, Reaches (.ret [.funV g] w) s ∧ Reaches (.ret [.funV f] w) s ∧
      ∀ T, Terminal T → (Reaches (.ret [.funV f] w) T → Reaches s T))
    (h : CallsOK v (P :: Ps) f) : CallsOK v (P :: Ps) g := by
  intro w hw hp
  obtain ⟨s, hgs, hfs, hT⟩ := hfg w
  rcases h w hw hp with he | ⟨r, hr, hc⟩
  · exact .inl (reaches_trans hgs (hT _ (.inl rfl) he))
  · exact .inr ⟨r, reaches_trans hgs (hT _ (.inr ⟨r, rfl⟩) hr), hc⟩

end Moist.Verified.Guards
