import Moist.Verified.ShapeFacts.Unary
import Moist.Verified.ShapeFacts.Counted

/-! # Resolved delayed computations

A head resolved to `delay d` returns a suspension of `d` in an older suffix of
the environment (`resolveHead_delay`). A head resolved to an `ifThenElse` or
`chooseList` selection between two delayed computations returns one of the two
suspensions (`resolveHead_select`).
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence

variable {P : List VarId → CekEnv → Expr → CekValue → Prop}

/-- A suspension of `d` created in a suffix of the environment where the
    facts still hold. -/
def SuspensionOf (P : List VarId → CekEnv → Expr → CekValue → Prop) (Γ : List (VarId × Expr))
    (env : List VarId) (ρ : CekEnv) (d : Expr) (w : CekValue) : Prop :=
  ∃ k dt, k ≤ env.length ∧ lowerTotalExpr (env.drop k) d = some dt ∧ w = .VDelay dt (dropEnv k ρ) ∧
    freshIn (env.drop k) d = true ∧ FactsHold P Γ (env.drop k) (dropEnv k ρ) ∧
    EnvDistinct (env.drop k)

theorem SuspensionOf.drop {Γ : List (VarId × Expr)} {env : List VarId} {ρ : CekEnv} {d : Expr}
    {w : CekValue} (j : Nat) (hj : j ≤ env.length) (h : SuspensionOf P Γ (env.drop j) (dropEnv j ρ) d w) :
    SuspensionOf P Γ env ρ d w := by
  obtain ⟨k, dt, hk, hdt, hw, hf, hfacts, hd⟩ := h
  refine ⟨j + k, dt, by simp at hk; omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← List.drop_drop]; exact hdt
  · rw [← dropEnv_add]; exact hw
  · rw [← List.drop_drop]; exact hf
  · rw [← List.drop_drop, ← dropEnv_add]; exact hfacts
  · rw [← List.drop_drop]; exact hd

/-- A head resolved to a delayed computation returns its suspension. -/
theorem resolveHead_delay
    (hP : ∀ env ρ rhs v, P env ρ rhs v → Produces env ρ rhs v ∧ freshIn env rhs = true) :
    ∀ (n : Nat) (Γ : List (VarId × Expr)) (e : Expr) {d : Expr} {env : List VarId} {ρ : CekEnv}
      {t : Term} {w : CekValue},
      resolveHead n Γ e = .Delay d → FactsHold P Γ env ρ → EnvDistinct env →
      freshIn env e = true → lowerTotalExpr env e = some t → Halts ρ t w →
      SuspensionOf P Γ env ρ d w := by
  intro n
  induction n with
  | zero =>
    intro Γ e d env ρ t w hres hfacts hd hfresh hlow hw
    rw [resolveHead_zero] at hres; subst hres
    obtain ⟨dt, hdt, rfl⟩ := lowerTotalExpr_delay_some hlow
    exact ⟨0, dt, by omega, by simpa using hdt, by simpa using halts_delay hw,
      by simpa [freshIn] using hfresh, by simpa using hfacts, by simpa using hd⟩
  | succ n ih =>
    intro Γ e d env ρ t w hres hfacts hd hfresh hlow hw
    cases e with
    | Var x =>
      rw [resolveHead_var] at hres
      cases hf : Γ.find? (fun entry => entry.1 == x) with
      | none => rw [hf] at hres; cases hres
      | some entry =>
        obtain ⟨y, rhs⟩ := entry
        rw [hf] at hres
        obtain ⟨i, hi, rfl⟩ := lowerTotalExpr_var_some hlow
        obtain ⟨v, k, hik, hk, hv, hp⟩ := hfacts x (y, rhs) i hf hi
        obtain ⟨⟨trhs, htrhs, hhalt⟩, hfr⟩ := hP _ _ _ _ hp
        have := halts_var hw
        rw [hv] at this; cases this
        exact SuspensionOf.drop k hk
          (ih Γ rhs hres (hfacts.drop hd k) (hd.drop k) hfr htrhs hhalt)
    | Delay body =>
      simp only [resolveHead] at hres; cases hres
      obtain ⟨dt, hdt, rfl⟩ := lowerTotalExpr_delay_some hlow
      exact ⟨0, dt, by omega, by simpa using hdt, by simpa using halts_delay hw,
        by simpa [freshIn] using hfresh, by simpa using hfacts, by simpa using hd⟩
    | App _ _ => rw [resolveHead_app] at hres; cases hres
    | Force _ => rw [resolveHead_force] at hres; cases hres
    | Lit _ | Error | Lam _ _ | Fix _ _ | Constr _ _ | Case _ _ | Let _ _ | Builtin _ =>
      simp only [resolveHead] at hres; cases hres

/-- A head resolved to an application is an application evaluated in an older
    suffix of the environment. -/
theorem resolveHead_app_unfold
    (hP : ∀ env ρ rhs v, P env ρ rhs v → Produces env ρ rhs v ∧ freshIn env rhs = true) :
    ∀ (n : Nat) (Γ : List (VarId × Expr)) (e : Expr) {g a : Expr} {env : List VarId} {ρ : CekEnv}
      {t : Term} {w : CekValue},
      resolveHead n Γ e = .App g a → FactsHold P Γ env ρ → EnvDistinct env →
      freshIn env e = true → lowerTotalExpr env e = some t → Halts ρ t w →
      ∃ k m e₁ t₁ ta wf wa, k ≤ env.length ∧ m ≤ n ∧ resolveHead m Γ e₁ = g ∧
        lowerTotalExpr (env.drop k) e₁ = some t₁ ∧ lowerTotalExpr (env.drop k) a = some ta ∧
        Halts (dropEnv k ρ) t₁ wf ∧ Halts (dropEnv k ρ) ta wa ∧
        Reaches (.ret [.funV wf] wa) (.halt w) ∧
        freshIn (env.drop k) e₁ = true ∧ freshIn (env.drop k) a = true ∧
        FactsHold P Γ (env.drop k) (dropEnv k ρ) ∧ EnvDistinct (env.drop k) := by
  intro n
  induction n with
  | zero =>
    intro Γ e g a env ρ t w hres hfacts hd hfresh hlow hw
    rw [resolveHead_zero] at hres; subst hres
    obtain ⟨t₁, ta, ht₁, hta, rfl⟩ := lowerTotalExpr_app_some hlow
    obtain ⟨wf, wa, hwf, hwa, happ⟩ := halts_apply hw
    simp only [freshIn, Bool.and_eq_true] at hfresh
    exact ⟨0, 0, g, t₁, ta, wf, wa, by omega, by omega, resolveHead_zero Γ g, by simpa using ht₁,
      by simpa using hta, by simpa using hwf, by simpa using hwa, happ, by simpa using hfresh.1,
      by simpa using hfresh.2, by simpa using hfacts, by simpa using hd⟩
  | succ n ih =>
    intro Γ e g a env ρ t w hres hfacts hd hfresh hlow hw
    cases e with
    | Var x =>
      rw [resolveHead_var] at hres
      cases hf : Γ.find? (fun entry => entry.1 == x) with
      | none => rw [hf] at hres; cases hres
      | some entry =>
        obtain ⟨y, rhs⟩ := entry
        rw [hf] at hres
        obtain ⟨i, hi, rfl⟩ := lowerTotalExpr_var_some hlow
        obtain ⟨v, k, hik, hk, hv, hp⟩ := hfacts x (y, rhs) i hf hi
        obtain ⟨⟨trhs, htrhs, hhalt⟩, hfr⟩ := hP _ _ _ _ hp
        have := halts_var hw
        rw [hv] at this; cases this
        obtain ⟨k', m, e₁, t₁, ta, wf, wa, hk', hm, hres₁, ht₁, hta, hwf, hwa, happ, hfe, hfa, hfacts', hd'⟩ :=
          ih Γ rhs hres (hfacts.drop hd k) (hd.drop k) hfr htrhs hhalt
        refine ⟨k + k', m, e₁, t₁, ta, wf, wa, by simp at hk'; omega, by omega, hres₁, ?_, ?_, ?_, ?_, happ,
          ?_, ?_, ?_, ?_⟩
        · rw [← List.drop_drop]; exact ht₁
        · rw [← List.drop_drop]; exact hta
        · rw [← dropEnv_add]; exact hwf
        · rw [← dropEnv_add]; exact hwa
        · rw [← List.drop_drop]; exact hfe
        · rw [← List.drop_drop]; exact hfa
        · rw [← List.drop_drop, ← dropEnv_add]; exact hfacts'
        · rw [← List.drop_drop]; exact hd'
    | App e₁ a' =>
      rw [resolveHead_app] at hres; cases hres
      obtain ⟨t₁, ta, ht₁, hta, rfl⟩ := lowerTotalExpr_app_some hlow
      obtain ⟨wf, wa, hwf, hwa, happ⟩ := halts_apply hw
      simp only [freshIn, Bool.and_eq_true] at hfresh
      exact ⟨0, n, e₁, t₁, ta, wf, wa, by omega, by omega, rfl, by simpa using ht₁, by simpa using hta,
        by simpa using hwf, by simpa using hwa, happ, by simpa using hfresh.1, by simpa using hfresh.2,
        by simpa using hfacts, by simpa using hd⟩
    | Force _ => rw [resolveHead_force] at hres; cases hres
    | Lit _ | Error | Lam _ _ | Fix _ _ | Delay _ | Constr _ _ | Case _ _ | Let _ _ | Builtin _ =>
      simp only [resolveHead] at hres; cases hres

theorem beq_selector {x : Expr}
    (h : (x == Expr.Force (.Builtin .IfThenElse) || x == Expr.Force (.Force (.Builtin .ChooseList))) = true) :
    x = .Force (.Builtin .IfThenElse) ∨ x = .Force (.Force (.Builtin .ChooseList)) := by
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · left
    cases x with
    | Force e =>
      cases e with
      | Builtin b' =>
        have : (b' == BuiltinFun.IfThenElse) = true := h
        cases b' <;> first | rfl | cases this
      | _ => cases h
    | _ => cases h
  · right
    cases x with
    | Force e =>
      cases e with
      | Force e' =>
        cases e' with
        | Builtin b' =>
          have : (b' == BuiltinFun.ChooseList) = true := h
          cases b' <;> first | rfl | cases this
        | _ => cases h
      | _ => cases h
    | _ => cases h

theorem evalBuiltin_select {b : BuiltinFun} {d₁ d₂ : Term} {ρ₁ ρ₂ : CekEnv} {c v : CekValue}
    (hb : b = .IfThenElse ∨ b = .ChooseList)
    (h : evalBuiltin b [.VDelay d₂ ρ₂, .VDelay d₁ ρ₁, c] = some v) :
    v = .VDelay d₂ ρ₂ ∨ v = .VDelay d₁ ρ₁ := by
  have hx : extractConsts [CekValue.VDelay d₂ ρ₂, .VDelay d₁ ρ₁, c] = none := rfl
  rcases hb with rfl | rfl
  · unfold evalBuiltin at h
    cases hp : evalBuiltinPassThrough .IfThenElse [.VDelay d₂ ρ₂, .VDelay d₁ ρ₁, c] with
    | none => rw [hp, hx] at h; cases h
    | some r =>
      rw [hp] at h; cases h
      cases c with
      | VCon k =>
        cases k with
        | Bool cond =>
          simp only [evalBuiltinPassThrough, Option.some.injEq] at hp
          subst hp; cases cond <;> simp
        | _ => simp [evalBuiltinPassThrough] at hp
      | _ => simp [evalBuiltinPassThrough] at hp
  · unfold evalBuiltin at h
    cases hp : evalBuiltinPassThrough .ChooseList [.VDelay d₂ ρ₂, .VDelay d₁ ρ₁, c] with
    | none => rw [hp, hx] at h; cases h
    | some r =>
      rw [hp] at h; cases h
      cases c with
      | VCon k =>
        cases k with
        | ConstDataList l =>
          simp only [evalBuiltinPassThrough, Option.some.injEq] at hp
          subst hp; cases l.isEmpty <;> simp
        | ConstList l =>
          simp only [evalBuiltinPassThrough, Option.some.injEq] at hp
          subst hp; cases l.isEmpty <;> simp
        | _ => simp [evalBuiltinPassThrough] at hp
      | _ => simp [evalBuiltinPassThrough] at hp

/-- Applying a builtin state that still expects more arguments. -/
theorem apply_partial {b : BuiltinFun} {args : List CekValue} {ea rest : ExpectedArgs} {wa v : CekValue}
    (htail : ea.tail = some rest) (h : Reaches (.ret [.funV (.VBuiltin b args ea)] wa) (.halt v)) :
    v = .VBuiltin b (wa :: args) rest := by
  rcases apply_reaches h with ⟨_, _, impossible, _⟩ | ⟨b', args', ea', heq, _, hres⟩
  · cases impossible
  · cases heq
    rcases hres with ⟨rest', ht, hv⟩ | ⟨ht, _⟩
    · rw [htail] at ht; cases ht; exact hv
    · rw [htail] at ht; cases ht

/-- Applying a builtin state that expects exactly one more argument. -/
theorem apply_final {b : BuiltinFun} {args : List CekValue} {ea : ExpectedArgs} {wa v : CekValue}
    (htail : ea.tail = none) (h : Reaches (.ret [.funV (.VBuiltin b args ea)] wa) (.halt v)) :
    evalBuiltin b (wa :: args) = some v := by
  rcases apply_reaches h with ⟨_, _, impossible, _⟩ | ⟨b', args', ea', heq, _, hres⟩
  · cases impossible
  · cases heq
    rcases hres with ⟨rest', ht, _⟩ | ⟨_, hv⟩
    · rw [htail] at ht; cases ht
    · exact hv

/-- A head resolved to an `ifThenElse` or `chooseList` selection between two
    delayed computations returns one of the two suspensions. -/
theorem resolveHead_select
    (hP : ∀ env ρ rhs v, P env ρ rhs v → Produces env ρ rhs v ∧ freshIn env rhs = true)
    (n : Nat) (Γ : List (VarId × Expr)) (e : Expr) {sel c first second : Expr} {env : List VarId}
    {ρ : CekEnv} {t : Term} {w : CekValue}
    (hres : resolveHead n Γ e = .App (.App (.App sel c) (.Delay first)) (.Delay second))
    (hsel : sel = .Force (.Builtin .IfThenElse) ∨ sel = .Force (.Force (.Builtin .ChooseList)))
    (hfacts : FactsHold P Γ env ρ) (hd : EnvDistinct env) (hfresh : freshIn env e = true)
    (hlow : lowerTotalExpr env e = some t) (hw : Halts ρ t w) :
    SuspensionOf P Γ env ρ first w ∨ SuspensionOf P Γ env ρ second w := by
  obtain ⟨k₁, m₁, e₁, t₁, ta₁, wf₁, wa₁, hk₁, _, hres₁, ht₁, hta₁, hwf₁, hwa₁, happ₁, hfe₁, hfa₁,
    hfacts₁, hd₁⟩ := resolveHead_app_unfold hP n Γ e hres hfacts hd hfresh hlow hw
  obtain ⟨k₂, m₂, e₂, t₂, ta₂, wf₂, wa₂, hk₂, _, hres₂, ht₂, hta₂, hwf₂, hwa₂, happ₂, hfe₂, hfa₂,
    hfacts₂, hd₂⟩ := resolveHead_app_unfold hP m₁ Γ e₁ hres₁ hfacts₁ hd₁ hfe₁ ht₁ hwf₁
  obtain ⟨k₃, m₃, e₃, t₃, ta₃, wf₃, wa₃, hk₃, _, hres₃, ht₃, hta₃, hwf₃, hwa₃, happ₃, hfe₃, hfa₃,
    hfacts₃, hd₃⟩ := resolveHead_app_unfold hP m₂ Γ e₂ hres₂ hfacts₂ hd₂ hfe₂ ht₂ hwf₂
  have hsecond : SuspensionOf P Γ env ρ second wa₁ :=
    SuspensionOf.drop k₁ hk₁ (resolveHead_delay hP 0 Γ (.Delay second) rfl hfacts₁ hd₁ hfa₁ hta₁ hwa₁)
  have hfirst : SuspensionOf P Γ env ρ first wa₂ :=
    SuspensionOf.drop k₁ hk₁ (SuspensionOf.drop k₂ hk₂
      (resolveHead_delay hP 0 Γ (.Delay first) rfl hfacts₂ hd₂ hfa₂ hta₂ hwa₂))
  have hProd : FactsHold Produces Γ ((env.drop k₁).drop k₂ |>.drop k₃)
      (dropEnv k₃ (dropEnv k₂ (dropEnv k₁ ρ))) := hfacts₃.mono (fun _ _ _ _ h => (hP _ _ _ _ h).1)
  obtain ⟨b, hb, hforced⟩ : ∃ b, (b = .IfThenElse ∨ b = .ChooseList) ∧
      forcedBuiltin sel = some (b, .more .argV (.more .argV (.one .argV))) := by
    rcases hsel with rfl | rfl
    · exact ⟨.IfThenElse, .inl rfl, rfl⟩
    · exact ⟨.ChooseList, .inr rfl, rfl⟩
  have hsel₃ := resolveHead_forced_halts m₃ Γ e₃ hres₃ hforced hProd hd₃ ht₃
  have := halts_unique hwf₃ hsel₃
  subst this
  have h₂ := apply_partial rfl happ₃
  subst h₂
  have h₁ := apply_partial rfl happ₂
  subst h₁
  have hev := apply_final rfl happ₁
  obtain ⟨j₁, dt₁, -, -, hwa₁', -⟩ := id hsecond
  obtain ⟨j₂, dt₂, -, -, hwa₂', -⟩ := id hfirst
  subst hwa₁' hwa₂'
  rcases evalBuiltin_select hb hev with rfl | rfl
  · exact .inr hsecond
  · exact .inl hfirst

end Moist.Verified.ShapeFacts
