import Moist.Verified.ShapeFacts.Decompose

/-! # Resolved application heads

`resolveHead` replaces variables by the right-hand sides recorded for them.
Under realized facts, the resolved head describes the value the original
expression returns: a builtin protocol accepted by
`builtinProtocolAfterSuccess` is the protocol of the returned builtin state
(`resolveHead_protocol`), and a resolved Boolean literal is the bound value
(`resolveHead_bool`). Every recorded right-hand side is interpreted in the
suffix of the environment where it was evaluated (`fact_of_var`).
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence

variable {P : List VarId → CekEnv → Expr → CekValue → Prop}

/-- Number of value arguments a builtin protocol still expects. -/
def valueArity : ExpectedArgs → Nat
  | .one k => if k = .argV then 1 else 0
  | .more k rest => (if k = .argV then 1 else 0) + valueArity rest

theorem valueArity_tail {rem rest : ExpectedArgs} (h : rem.tail = some rest) :
    valueArity rem = (if rem.head = .argV then 1 else 0) + valueArity rest := by
  cases rem with
  | one k => cases h
  | more k r => cases h; rfl

/-- A builtin state that has received the value arguments of a prefix of its
    protocol. -/
def BuiltinState (b : BuiltinFun) (rem : ExpectedArgs) (w : CekValue) : Prop :=
  ∃ args, w = .VBuiltin b args rem ∧ args.length + valueArity rem = valueArity (expectedArgs b)

/-- Looking up a recorded binder yields the right-hand side that produced its
    value, together with the facts of the older suffix. -/
theorem fact_of_var {Γ : List (VarId × Expr)} {env : List VarId} {ρ : CekEnv} {x : VarId}
    {entry : VarId × Expr} {t : Term} {v : CekValue}
    (hfacts : FactsHold P Γ env ρ) (hd : EnvDistinct env)
    (hf : Γ.find? (fun e => e.1 == x) = some entry)
    (hlow : lowerTotalExpr env (.Var x) = some t) (hv : Halts ρ t v) :
    ∃ k, k ≤ env.length ∧ P (env.drop k) (dropEnv k ρ) entry.2 v ∧
      FactsHold P Γ (env.drop k) (dropEnv k ρ) ∧ EnvDistinct (env.drop k) := by
  obtain ⟨i, hi, rfl⟩ := lowerTotalExpr_var_some hlow
  obtain ⟨w, k, _, hk, hw, hp⟩ := hfacts x entry i hf hi
  have := halts_var hv
  rw [hw] at this; cases this
  exact ⟨k, hk, hp, hfacts.drop hd k, hd.drop k⟩

theorem protocol_force {e : Expr} {b : BuiltinFun} {rem : ExpectedArgs}
    (h : builtinProtocolAfterSuccess (.Force e) = some (b, rem)) :
    ∃ rem', builtinProtocolAfterSuccess e = some (b, rem') ∧ rem'.head = .argQ ∧ rem'.tail = some rem := by
  rw [builtinProtocolAfterSuccess] at h
  cases he : builtinProtocolAfterSuccess e with
  | none => simp [he] at h
  | some r =>
    obtain ⟨b', rem'⟩ := r
    simp only [he] at h
    refine ⟨rem', ?_⟩
    cases hh : rem'.head <;> cases ht : rem'.tail <;> simp_all <;> exact absurd h.1 (by decide)
theorem protocol_app {f a : Expr} {b : BuiltinFun} {rem : ExpectedArgs}
    (h : builtinProtocolAfterSuccess (.App f a) = some (b, rem)) :
    ∃ rem', builtinProtocolAfterSuccess f = some (b, rem') ∧ rem'.head = .argV ∧ rem'.tail = some rem := by
  rw [builtinProtocolAfterSuccess] at h
  cases he : builtinProtocolAfterSuccess f with
  | none => simp [he] at h
  | some r =>
    obtain ⟨b', rem'⟩ := r
    simp only [he] at h
    refine ⟨rem', ?_⟩
    cases hh : rem'.head <;> cases ht : rem'.tail <;> simp_all <;> exact absurd h.1 (by decide)

/-- Successful application of a builtin state that still expects arguments. -/
theorem apply_builtin_state {wf wa v : CekValue} {b : BuiltinFun} {rem rest : ExpectedArgs}
    (hwf : BuiltinState b rem wf) (htail : rem.tail = some rest)
    (h : Reaches (.ret [.funV wf] wa) (.halt v)) : BuiltinState b rest v := by
  obtain ⟨args, rfl, hlen⟩ := hwf
  rcases apply_reaches h with ⟨_, _, impossible, _⟩ | ⟨b', args', ea, heq, hhead, hres⟩
  · cases impossible
  · cases heq
    rcases hres with ⟨rest', ht, rfl⟩ | ⟨ht, _⟩
    · rw [htail] at ht; cases ht
      refine ⟨_, rfl, ?_⟩
      rw [valueArity_tail htail, hhead] at hlen
      simp at hlen ⊢; omega
    · rw [htail] at ht; cases ht

theorem force_builtin_state {w v : CekValue} {b : BuiltinFun} {rem rest : ExpectedArgs}
    (hw : BuiltinState b rem w) (htail : rem.tail = some rest)
    (h : Reaches (.ret [.force] w) (.halt v)) : BuiltinState b rest v := by
  obtain ⟨args, rfl, hlen⟩ := hw
  rcases force_reaches h with ⟨_, _, impossible, _⟩ | ⟨b', args', ea, heq, hhead, hres⟩
  · cases impossible
  · cases heq
    rcases hres with ⟨rest', ht, rfl⟩ | ⟨ht, _⟩
    · rw [htail] at ht; cases ht
      refine ⟨_, rfl, ?_⟩
      rw [valueArity_tail htail, hhead] at hlen
      simp at hlen ⊢; omega
    · rw [htail] at ht; cases ht

theorem protocol_raw : ∀ (e : Expr) {b : BuiltinFun} {rem : ExpectedArgs} {env : List VarId}
    {ρ : CekEnv} {t : Term} {w : CekValue},
    builtinProtocolAfterSuccess e = some (b, rem) → lowerTotalExpr env e = some t → Halts ρ t w →
    BuiltinState b rem w
  | .Builtin b', b, rem, env, ρ, t, w, h, hlow, hw => by
    simp only [builtinProtocolAfterSuccess, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [lowerTotalExpr_builtin] at hlow; cases hlow
    exact ⟨[], halts_builtin hw, by simp⟩
  | .Force e, b, rem, env, ρ, t, w, h, hlow, hw => by
    obtain ⟨rem', hp, hq, ht⟩ := protocol_force h
    obtain ⟨te, hte, rfl⟩ := lowerTotalExpr_force_some hlow
    obtain ⟨w', hw', rest⟩ := halts_force hw
    exact force_builtin_state (protocol_raw e hp hte hw') ht rest
  | .App f a, b, rem, env, ρ, t, w, h, hlow, hw => by
    obtain ⟨rem', hp, hq, ht⟩ := protocol_app h
    obtain ⟨tf, ta, htf, _, rfl⟩ := lowerTotalExpr_app_some hlow
    obtain ⟨wf, wa, hwf, _, rest⟩ := halts_apply hw
    exact apply_builtin_state (protocol_raw f hp htf hwf) ht rest
  | .Var _, _, _, _, _, _, _, h, _, _ | .Lit _, _, _, _, _, _, _, h, _, _
  | .Error, _, _, _, _, _, _, h, _, _ | .Lam _ _, _, _, _, _, _, _, h, _, _
  | .Fix _ _, _, _, _, _, _, _, h, _, _ | .Delay _, _, _, _, _, _, _, h, _, _
  | .Constr _ _, _, _, _, _, _, _, h, _, _ | .Case _ _, _, _, _, _, _, _, h, _, _
  | .Let _ _, _, _, _, _, _, _, h, _, _ => by simp [builtinProtocolAfterSuccess] at h

theorem resolveHead_zero (Γ : List (VarId × Expr)) (e : Expr) : resolveHead 0 Γ e = e := by
  cases e <;> rfl

theorem resolveHead_var (n : Nat) (Γ : List (VarId × Expr)) (x : VarId) :
    resolveHead (n + 1) Γ (.Var x) =
      match Γ.find? (fun entry => entry.1 == x) with
      | some (_, rhs) => resolveHead n Γ rhs
      | none => .Var x := rfl

theorem resolveHead_app (n : Nat) (Γ : List (VarId × Expr)) (f a : Expr) :
    resolveHead (n + 1) Γ (.App f a) = .App (resolveHead n Γ f) a := rfl

theorem resolveHead_force (n : Nat) (Γ : List (VarId × Expr)) (e : Expr) :
    resolveHead (n + 1) Γ (.Force e) = .Force (resolveHead n Γ e) := rfl

theorem resolveHead_other (n : Nat) (Γ : List (VarId × Expr)) (e : Expr)
    (hvar : ∀ x, e ≠ .Var x) (happ : ∀ f a, e ≠ .App f a) (hforce : ∀ b, e ≠ .Force b) :
    resolveHead n Γ e = e := by
  cases n with
  | zero => exact resolveHead_zero Γ e
  | succ n =>
    cases e with
    | Var x => exact absurd rfl (hvar x)
    | App f a => exact absurd rfl (happ f a)
    | Force b => exact absurd rfl (hforce b)
    | _ => rfl

/-- Cases of a resolved head. -/
theorem resolveHead_cases (n : Nat) (Γ : List (VarId × Expr)) (e : Expr) :
    (n = 0 ∧ resolveHead n Γ e = e) ∨
    (∃ m x, n = m + 1 ∧ e = .Var x ∧
      ((∃ entry, Γ.find? (fun entry => entry.1 == x) = some entry ∧
          resolveHead n Γ e = resolveHead m Γ entry.2) ∨
        (Γ.find? (fun entry => entry.1 == x) = none ∧ resolveHead n Γ e = .Var x))) ∨
    (∃ m f a, n = m + 1 ∧ e = .App f a ∧ resolveHead n Γ e = .App (resolveHead m Γ f) a) ∨
    (∃ m b, n = m + 1 ∧ e = .Force b ∧ resolveHead n Γ e = .Force (resolveHead m Γ b)) ∨
    ((∀ x, e ≠ .Var x) ∧ (∀ f a, e ≠ .App f a) ∧ (∀ b, e ≠ .Force b) ∧ resolveHead n Γ e = e) := by
  cases n with
  | zero => exact .inl ⟨rfl, resolveHead_zero Γ e⟩
  | succ m =>
    cases e with
    | Var x =>
      refine .inr (.inl ⟨m, x, rfl, rfl, ?_⟩)
      cases hf : Γ.find? (fun entry => entry.1 == x) with
      | none => exact .inr ⟨rfl, by rw [resolveHead_var, hf]⟩
      | some entry =>
        obtain ⟨y, rhs⟩ := entry
        exact .inl ⟨(y, rhs), rfl, by rw [resolveHead_var, hf]⟩
    | App f a => exact .inr (.inr (.inl ⟨m, f, a, rfl, rfl, rfl⟩))
    | Force b => exact .inr (.inr (.inr (.inl ⟨m, b, rfl, rfl, rfl⟩)))
    | _ => exact .inr (.inr (.inr (.inr ⟨by simp, by simp, by simp, rfl⟩)))

/-- An accepted builtin protocol describes the returned builtin state. -/
theorem resolveHead_protocol (hP : ∀ env ρ rhs v, P env ρ rhs v → Produces env ρ rhs v) :
    ∀ (n : Nat) (Γ : List (VarId × Expr)) (e : Expr) {b : BuiltinFun} {rem : ExpectedArgs}
      {env : List VarId} {ρ : CekEnv} {t : Term} {w : CekValue},
      builtinProtocolAfterSuccess (resolveHead n Γ e) = some (b, rem) →
      FactsHold P Γ env ρ → EnvDistinct env →
      lowerTotalExpr env e = some t → Halts ρ t w → BuiltinState b rem w := by
  intro n
  induction n with
  | zero =>
    intro Γ e b rem env ρ t w h _ _ hlow hw
    rw [resolveHead_zero] at h
    exact protocol_raw e h hlow hw
  | succ n ih =>
    intro Γ e b rem env ρ t w h hfacts hd hlow hw
    cases e with
    | Var x =>
      rw [resolveHead_var] at h
      cases hf : Γ.find? (fun entry => entry.1 == x) with
      | none => rw [hf] at h; simp [builtinProtocolAfterSuccess] at h
      | some entry =>
        obtain ⟨y, rhs⟩ := entry
        rw [hf] at h
        obtain ⟨k, _, hp, hfacts', hd'⟩ := fact_of_var hfacts hd hf hlow hw
        obtain ⟨t', ht', hw'⟩ := hP _ _ _ _ hp
        exact ih Γ rhs h hfacts' hd' ht' hw'
    | App f a =>
      rw [resolveHead_app] at h
      obtain ⟨rem', hp, hq, ht⟩ := protocol_app h
      obtain ⟨tf, ta, htf, _, rfl⟩ := lowerTotalExpr_app_some hlow
      obtain ⟨wf, wa, hwf, _, rest⟩ := halts_apply hw
      exact apply_builtin_state (ih Γ f hp hfacts hd htf hwf) ht rest
    | Force e =>
      rw [resolveHead_force] at h
      obtain ⟨rem', hp, hq, ht⟩ := protocol_force h
      obtain ⟨te, hte, rfl⟩ := lowerTotalExpr_force_some hlow
      obtain ⟨w', hw', rest⟩ := halts_force hw
      exact force_builtin_state (ih Γ e hp hfacts hd hte hw') ht rest
    | Builtin b' => exact protocol_raw (.Builtin b') h hlow hw
    | Lit _ | Error | Lam _ _ | Fix _ _ | Delay _ | Constr _ _ | Case _ _ | Let _ _ =>
      simp [resolveHead, builtinProtocolAfterSuccess] at h

/-- A head resolved to a Boolean literal is that Boolean. -/
theorem resolveHead_bool (hP : ∀ env ρ rhs v, P env ρ rhs v → Produces env ρ rhs v) :
    ∀ (n : Nat) (Γ : List (VarId × Expr)) (e : Expr) {c : Bool} {ty : BuiltinType}
      {env : List VarId} {ρ : CekEnv} {t : Term} {w : CekValue},
      resolveHead n Γ e = .Lit (.Bool c, ty) →
      FactsHold P Γ env ρ → EnvDistinct env →
      lowerTotalExpr env e = some t → Halts ρ t w → w = .VCon (.Bool c) := by
  intro n
  induction n with
  | zero =>
    intro Γ e c ty env ρ t w h _ _ hlow hw
    rw [resolveHead_zero] at h; subst h
    rw [lowerTotalExpr_lit] at hlow; cases hlow
    exact halts_constant hw
  | succ n ih =>
    intro Γ e c ty env ρ t w h hfacts hd hlow hw
    cases e with
    | Var x =>
      rw [resolveHead_var] at h
      cases hf : Γ.find? (fun entry => entry.1 == x) with
      | none => rw [hf] at h; cases h
      | some entry =>
        obtain ⟨y, rhs⟩ := entry
        rw [hf] at h
        obtain ⟨k, _, hp, hfacts', hd'⟩ := fact_of_var hfacts hd hf hlow hw
        obtain ⟨t', ht', hw'⟩ := hP _ _ _ _ hp
        exact ih Γ rhs h hfacts' hd' ht' hw'
    | Lit l =>
      simp only [resolveHead] at h; cases h
      rw [lowerTotalExpr_lit] at hlow; cases hlow
      exact halts_constant hw
    | App _ _ | Force _ => simp [resolveHead] at h
    | Error | Lam _ _ | Fix _ _ | Delay _ | Constr _ _ | Case _ _ | Let _ _ | Builtin _ =>
      simp [resolveHead] at h

end Moist.Verified.ShapeFacts
