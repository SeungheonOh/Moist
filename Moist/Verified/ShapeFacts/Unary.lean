import Moist.Verified.ShapeFacts.Known
import Moist.Verified.ShapeFacts.Lift

variable [sv : Moist.CEK.SemVariant]

/-! # Resolved unary builtin applications

When `resolveHead` turns an expression into a builtin, possibly forced, applied
to a variable `l`, the expression behaves exactly like that builtin applied to
the current value of `l`: it returns `w` iff the builtin returns `w`, and it
fails when the builtin fails (`resolveHead_unary`). The variable is bound in
the current environment (`resolveHead_app_var_bound`), so a rewrite may refer
to it directly.
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.BetaValueRefines

omit sv in
theorem FactsScoped.drop {Γ : List (VarId × Expr)} {env : List VarId}
    (h : FactsScoped Γ env) (hd : EnvDistinct env) (j : Nat) : FactsScoped Γ (env.drop j) := by
  intro y entry i hf hl
  obtain ⟨k, hik, hk, hs⟩ := h y entry (i + j) hf (hd.drop_lookup j hl)
  refine ⟨k - j, by omega, by simp; omega, ?_⟩
  rw [List.drop_drop, show j + (k - j) = k by omega]; exact hs

theorem FactsScoped.ofFactsHold {Γ : List (VarId × Expr)} {env : List VarId} {ρ : CekEnv}
    (h : FactsHold Produces Γ env ρ) : FactsScoped Γ env := by
  intro y entry i hf hl
  obtain ⟨v, k, hik, hk, _, t, ht, _⟩ := h y entry i hf hl
  exact ⟨k, hik, hk, by simp [ht]⟩

/-- Builtins, possibly forced. -/
def forcedBuiltin : Expr → Option (BuiltinFun × ExpectedArgs)
  | .Builtin b => some (b, expectedArgs b)
  | .Force e => do
    let (b, rem) ← forcedBuiltin e
    if rem.head = .argQ then (rem.tail).map (b, ·) else none
  | _ => none

omit sv in
theorem forcedBuiltin_force {e : Expr} {b : BuiltinFun} {rem : ExpectedArgs}
    (h : forcedBuiltin (.Force e) = some (b, rem)) :
    ∃ rem', forcedBuiltin e = some (b, rem') ∧ rem'.head = .argQ ∧ rem'.tail = some rem := by
  rw [forcedBuiltin] at h
  cases he : forcedBuiltin e with
  | none => rw [he] at h; cases h
  | some r =>
    obtain ⟨b', rem'⟩ := r
    rw [he] at h
    change (if rem'.head = .argQ then (rem'.tail).map (b', ·) else none) = some (b, rem) at h
    split at h
    · rename_i hq
      cases ht : rem'.tail with
      | none => rw [ht] at h; cases h
      | some rest => rw [ht] at h; cases h; exact ⟨rem', rfl, hq, ht⟩
    · cases h

/-- A resolved forced builtin is a returned builtin state. -/
theorem resolveHead_forced_halts :
    ∀ (n : Nat) (Γ : List (VarId × Expr)) (e : Expr) {h : Expr} {b : BuiltinFun}
      {rem : ExpectedArgs} {env : List VarId} {ρ : CekEnv} {t : Term},
      resolveHead n Γ e = h → forcedBuiltin h = some (b, rem) →
      FactsHold Produces Γ env ρ → EnvDistinct env →
      lowerTotalExpr env e = some t → Halts ρ t (.VBuiltin b [] rem) := by
  intro n
  induction n with
  | zero =>
    intro Γ e h b rem env ρ t hres hfb hfacts hd hlow
    rw [resolveHead_zero] at hres; subst hres
    exact forced_raw e hfb hlow
  | succ n ih =>
    intro Γ e h b rem env ρ t hres hfb hfacts hd hlow
    cases e with
    | Var x =>
      rw [resolveHead_var] at hres
      cases hf : Γ.find? (fun entry => entry.1 == x) with
      | none => rw [hf] at hres; subst hres; simp [forcedBuiltin] at hfb
      | some entry =>
        obtain ⟨y, rhs⟩ := entry
        rw [hf] at hres
        obtain ⟨i, hi, rfl⟩ := lowerTotalExpr_var_some hlow
        obtain ⟨v, k, hik, hk, hv, ⟨trhs, htrhs, hhalt⟩⟩ := hfacts x (y, rhs) i hf hi
        have hw := ih Γ rhs hres hfb (hfacts.drop hd k) (hd.drop k) htrhs
        rw [halts_unique hhalt hw] at hv
        exact halts_var_of_lookup hv
    | Force e =>
      rw [resolveHead_force] at hres; subst hres
      obtain ⟨rem', hfb', hq, ht⟩ := forcedBuiltin_force hfb
      obtain ⟨te, hte, rfl⟩ := lowerTotalExpr_force_some hlow
      have hw := ih Γ e rfl hfb' hfacts hd hte
      refine reaches_trans (reaches_of_steps 1 rfl) ?_
      refine reaches_trans (halts_on_stack hw [.force]) ?_
      refine ⟨2, ?_⟩
      simp [steps, step, hq, ht]
    | Builtin b' => rw [show resolveHead (n + 1) Γ (.Builtin b') = .Builtin b' from rfl] at hres
                    subst hres; exact forced_raw _ hfb hlow
    | App _ _ => rw [resolveHead_app] at hres; subst hres; simp [forcedBuiltin] at hfb
    | Lit _ | Error | Lam _ _ | Fix _ _ | Delay _ | Constr _ _ | Case _ _ | Let _ _ =>
      simp only [resolveHead] at hres; subst hres; simp [forcedBuiltin] at hfb
where
  forced_raw : ∀ (e : Expr) {b : BuiltinFun} {rem : ExpectedArgs} {env : List VarId}
      {ρ : CekEnv} {t : Term},
      forcedBuiltin e = some (b, rem) → lowerTotalExpr env e = some t →
      Halts ρ t (.VBuiltin b [] rem)
    | .Builtin b', b, rem, env, ρ, t, hfb, hlow => by
      simp only [forcedBuiltin, Option.some.injEq, Prod.mk.injEq] at hfb
      obtain ⟨rfl, rfl⟩ := hfb
      rw [lowerTotalExpr_builtin] at hlow; cases hlow
      exact ⟨2, rfl⟩
    | .Force e, b, rem, env, ρ, t, hfb, hlow => by
      obtain ⟨rem', hfb', hq, ht⟩ := forcedBuiltin_force hfb
      obtain ⟨te, hte, rfl⟩ := lowerTotalExpr_force_some hlow
      have hw := forced_raw e (ρ := ρ) hfb' hte
      refine reaches_trans (reaches_of_steps 1 rfl) ?_
      refine reaches_trans (halts_on_stack hw [.force]) ?_
      refine ⟨2, ?_⟩
      simp [steps, step, hq, ht]
    | .Var _, _, _, _, _, _, hfb, _ | .Lit _, _, _, _, _, _, hfb, _
    | .Error, _, _, _, _, _, hfb, _ | .Lam _ _, _, _, _, _, _, hfb, _
    | .Fix _ _, _, _, _, _, _, hfb, _ | .Delay _, _, _, _, _, _, hfb, _
    | .Constr _ _, _, _, _, _, _, hfb, _ | .Case _ _, _, _, _, _, _, hfb, _
    | .Let _ _, _, _, _, _, _, hfb, _ | .App _ _, _, _, _, _, _, hfb, _ => by
      simp [forcedBuiltin] at hfb

omit sv in
/-- The argument variable of a resolved application is bound. -/
theorem resolveHead_app_var_bound :
    ∀ (n : Nat) (Γ : List (VarId × Expr)) (e : Expr) {g : Expr} {l : VarId} {env : List VarId},
      resolveHead n Γ e = .App g (.Var l) → FactsScoped Γ env → EnvDistinct env →
      (lowerTotalExpr env e).isSome = true → (envLookupT env l).isSome = true := by
  intro n
  induction n with
  | zero =>
    intro Γ e g l env hres _ _ hlow
    rw [resolveHead_zero] at hres; subst hres
    rw [MIR.lowerTotalExpr_app] at hlow
    cases hg : lowerTotalExpr env g with
    | none => rw [hg] at hlow; simp at hlow
    | some _ =>
      rw [hg] at hlow
      rw [lowerTotalExpr_var] at hlow
      cases hl : envLookupT env l with
      | none => rw [hl] at hlow; simp at hlow
      | some _ => rfl
  | succ n ih =>
    intro Γ e g l env hres hs hd hlow
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
      cases hres
      rw [MIR.lowerTotalExpr_app] at hlow
      cases hf : lowerTotalExpr env f with
      | none => rw [hf] at hlow; simp at hlow
      | some _ =>
        rw [hf] at hlow
        rw [lowerTotalExpr_var] at hlow
        cases hl : envLookupT env l with
        | none => rw [hl] at hlow; simp at hlow
        | some _ => rfl
    | Force _ => rw [resolveHead_force] at hres; cases hres
    | Lit _ | Error | Lam _ _ | Fix _ _ | Delay _ | Constr _ _ | Case _ _ | Let _ _ | Builtin _ =>
      simp only [resolveHead] at hres; cases hres

/-- A resolved unary builtin application behaves as the builtin applied to the
    current value of its argument. -/
theorem resolveHead_unary :
    ∀ (n : Nat) (Γ : List (VarId × Expr)) (e : Expr) {g : Expr} {l : VarId} {b : BuiltinFun}
      {env : List VarId} {ρ : CekEnv} {t : Term} {il : Nat} {vl : CekValue},
      resolveHead n Γ e = .App g (.Var l) → forcedBuiltin g = some (b, .one .argV) →
      FactsHold Produces Γ env ρ → EnvDistinct env →
      lowerTotalExpr env e = some t → envLookupT env l = some il → ρ.lookup (il + 1) = some vl →
      (∀ w, Halts ρ t w ↔ evalBuiltin b [vl] = some w) ∧ (evalBuiltin b [vl] = none → Errs ρ t) := by
  intro n
  induction n with
  | zero =>
    intro Γ e g l b env ρ t il vl hres hfb hfacts hd hlow hil hvl
    rw [resolveHead_zero] at hres; subst hres
    exact apply_case Γ hfb hfacts hd (resolveHead_zero Γ g) hlow hil hvl
  | succ n ih =>
    intro Γ e g l b env ρ t il vl hres hfb hfacts hd hlow hil hvl
    cases e with
    | Var x =>
      rw [resolveHead_var] at hres
      cases hf : Γ.find? (fun entry => entry.1 == x) with
      | none => rw [hf] at hres; cases hres
      | some entry =>
        obtain ⟨y, rhs⟩ := entry
        rw [hf] at hres
        obtain ⟨i, hi, rfl⟩ := lowerTotalExpr_var_some hlow
        obtain ⟨vx, k, hik, hk, hvx, ⟨trhs, htrhs, hhalt⟩⟩ := hfacts x (y, rhs) i hf hi
        have hbound := resolveHead_app_var_bound n Γ rhs (env := env.drop k) hres
          (FactsScoped.ofFactsHold (hfacts.drop hd k)) (hd.drop k) (by simp [htrhs])
        cases hl : envLookupT (env.drop k) l with
        | none => rw [hl] at hbound; simp at hbound
        | some j =>
          have hj := hd.drop_lookup k hl
          rw [hil] at hj; cases hj
          have hvl' : (dropEnv k ρ).lookup (j + 1) = some vl := by
            rw [dropEnv_lookup k ρ _ (by omega), show j + 1 + k = j + k + 1 by omega]; exact hvl
          obtain ⟨hiff, _⟩ := ih Γ rhs hres hfb (hfacts.drop hd k) (hd.drop k) htrhs hl hvl'
          have heval := (hiff vx).mp hhalt
          refine ⟨fun w => ⟨fun hw => ?_, fun hw => ?_⟩, fun hnone => ?_⟩
          · have hlook := halts_var hw
            rw [hvx] at hlook; cases hlook
            exact heval
          · rw [heval] at hw; cases hw
            exact halts_var_of_lookup hvx
          · rw [heval] at hnone; cases hnone
    | App f a =>
      rw [resolveHead_app] at hres
      cases hres
      exact apply_case Γ hfb hfacts hd rfl hlow hil hvl
    | Force _ => rw [resolveHead_force] at hres; cases hres
    | Lit _ | Error | Lam _ _ | Fix _ _ | Delay _ | Constr _ _ | Case _ _ | Let _ _ | Builtin _ =>
      simp only [resolveHead] at hres; cases hres
where
  apply_case {n : Nat} (Γ : List (VarId × Expr)) {f g : Expr} {l : VarId} {b : BuiltinFun}
      {env : List VarId} {ρ : CekEnv} {t : Term} {il : Nat} {vl : CekValue}
      (hfb : forcedBuiltin g = some (b, .one .argV)) (hfacts : FactsHold Produces Γ env ρ)
      (hd : EnvDistinct env) (hres : resolveHead n Γ f = g)
      (hlow : lowerTotalExpr env (.App f (.Var l)) = some t) (hil : envLookupT env l = some il)
      (hvl : ρ.lookup (il + 1) = some vl) :
      (∀ w, Halts ρ t w ↔ evalBuiltin b [vl] = some w) ∧ (evalBuiltin b [vl] = none → Errs ρ t) := by
    obtain ⟨tf, ta, htf, hta, rfl⟩ := lowerTotalExpr_app_some hlow
    rw [lowerTotalExpr_var, hil] at hta; cases hta
    have hwf := resolveHead_forced_halts n Γ f hres hfb hfacts hd htf
    have run : ∀ T, Reaches (.ret [.funV (.VBuiltin b [] (.one .argV))] vl) T →
        Reaches (.compute [] ρ (.Apply tf (.Var (il + 1)))) T := by
      intro T hT
      refine reaches_trans (reaches_of_steps 1 rfl) ?_
      refine reaches_trans (halts_on_stack hwf _) ?_
      refine reaches_trans (reaches_of_steps 1 rfl) ?_
      refine reaches_trans (halts_on_stack (halts_var_of_lookup hvl) _) hT
    refine ⟨fun w => ⟨fun hw => ?_, fun hw => ?_⟩, fun hnone => ?_⟩
    · obtain ⟨wf', wa, hwf', hwa, rest⟩ := halts_apply hw
      rw [halts_unique hwf' hwf] at rest
      rw [halts_unique hwa (halts_var_of_lookup hvl)] at rest
      rcases apply_reaches rest with ⟨_, _, impossible, _⟩ | ⟨_, _, _, heq, _, hres⟩
      · cases impossible
      · cases heq
        rcases hres with ⟨_, ht, _⟩ | ⟨_, heval⟩
        · cases ht
        · exact heval
    · apply run
      refine ⟨2, ?_⟩
      simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, hw]
    · apply run
      refine ⟨1, ?_⟩
      simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, hnone]

end Moist.Verified.ShapeFacts
