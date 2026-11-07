import Moist.Verified.ShapeFacts.Total
import Moist.Verified.ShapesSoundness.Choices
import Moist.MIR.Optimize.Advanced.TagChains

/-! # Tag tests under facts

A tag test `tagTest Γ s = some (t, c)` resolves, through the recorded
bindings, to `equalsInteger` applied to the known integer variable `t` and
the literal `c`. Under realized facts it returns `t = c` without failing
(`tagTest_halts`): the recorded right-hand sides that build the partial
application were evaluated in older suffixes of the environment, and an
older suffix binds `t` to its current value (`halts_var_drop`).
-/

namespace Moist.Verified.TagChains

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.ShapeFacts
open Moist.Verified.BetaValueRefines

/-! ## Variables of older suffixes -/

theorem halts_var_drop {env : List VarId} {ρ : CekEnv} {k : Nat} {x : VarId} {tx : Term}
    {w : CekValue} (hd : EnvDistinct env)
    (hlow : lowerTotalExpr (env.drop k) (.Var x) = some tx) (hw : Halts (dropEnv k ρ) tx w) :
    ∃ i, envLookupT env x = some i ∧ ρ.lookup (i + 1) = some w := by
  obtain ⟨i, hi, rfl⟩ := lowerTotalExpr_var_some hlow
  refine ⟨i + k, hd.drop_lookup k hi, ?_⟩
  have h := halts_var hw
  rw [dropEnv_lookup k ρ _ (by omega)] at h
  rw [show i + k + 1 = i + 1 + k by omega]; exact h

theorem envWellFormed_drop {env : List VarId} {ρ : CekEnv} (henv : EnvWellFormed env.length ρ)
    (k : Nat) : EnvWellFormed (env.drop k).length (dropEnv k ρ) := by
  have := envWellFormed_dropEnv henv k
  simpa using this

/-- Variables and literals return in a well-formed environment. -/
def Atomic (e : Expr) : Prop := (∃ x, e = .Var x) ∨ (∃ c, e = .Lit c)

theorem atomic_halts {e : Expr} (ha : Atomic e) {env : List VarId} {ρ : CekEnv} {t : Term}
    (henv : EnvWellFormed env.length ρ) (hlow : lowerTotalExpr env e = some t) :
    ∃ v, Halts ρ t v := by
  rcases ha with ⟨x, rfl⟩ | ⟨⟨c, ty⟩, rfl⟩
  · obtain ⟨i, hi, rfl⟩ := lowerTotalExpr_var_some hlow
    obtain ⟨v, hv, _⟩ := envWellFormed_lookup env.length henv (n := i + 1) (by omega)
      (by have := envLookupT_bound env x i hi; omega)
    exact ⟨v, halts_var_of_lookup hv⟩
  · rw [lowerTotalExpr_lit] at hlow; cases hlow
    exact ⟨_, halts_constant_of c ty⟩

/-! ## Resolved partial and saturated binary applications -/

def Binary (b : BuiltinFun) : Prop := expectedArgs b = .more .argV (.one .argV)

/-- A head resolved to a binary builtin applied to an atomic argument returns
    the builtin holding the value of that argument in an older suffix. -/
theorem resolve_partial {b : BuiltinFun} (hb : Binary b) :
    ∀ (n : Nat) (Γ : List (VarId × Expr)) (f : Expr) {X : Expr} {env : List VarId} {ρ : CekEnv}
      {tf : Term}, resolveHead n Γ f = .App (.Builtin b) X → Atomic X →
      FactsHold Produces Γ env ρ → EnvDistinct env → EnvWellFormed env.length ρ →
      lowerTotalExpr env f = some tf →
      ∃ k tX vX, k ≤ env.length ∧ lowerTotalExpr (env.drop k) X = some tX ∧
        Halts (dropEnv k ρ) tX vX ∧ Halts ρ tf (.VBuiltin b [vX] (.one .argV)) := by
  have apply_builtin : ∀ {ρ : CekEnv} {tg tX : Term} {vX : CekValue},
      Halts ρ tg (.VBuiltin b [] (expectedArgs b)) → Halts ρ tX vX →
      Halts ρ (.Apply tg tX) (.VBuiltin b [vX] (.one .argV)) := by
    intro ρ tg tX vX hg hX
    refine halts_apply_intro hg hX ?_
    rw [hb]
    exact builtin_partial_reaches rfl rfl
  intro n
  induction n with
  | zero =>
    intro Γ f X env ρ tf hres hX hfacts hd henv hlow
    rw [resolveHead_zero] at hres; subst hres
    obtain ⟨tg, tX, htg, htX, rfl⟩ := lowerTotalExpr_app_some hlow
    rw [lowerTotalExpr_builtin] at htg; cases htg
    obtain ⟨vX, hvX⟩ := atomic_halts hX henv htX
    exact ⟨0, tX, vX, by omega, by simpa using htX, by simpa using hvX,
      apply_builtin ⟨2, rfl⟩ hvX⟩
  | succ n ih =>
    intro Γ f X env ρ tf hres hX hfacts hd henv hlow
    cases f with
    | Var x =>
      rw [resolveHead_var] at hres
      cases hf : Γ.find? (fun entry => entry.1 == x) with
      | none => rw [hf] at hres; cases hres
      | some entry =>
        obtain ⟨y, rhs⟩ := entry
        rw [hf] at hres
        obtain ⟨i, hi, rfl⟩ := lowerTotalExpr_var_some hlow
        obtain ⟨vx, k, hik, hk, hvx, ⟨trhs, htrhs, hhalt⟩⟩ := hfacts x (y, rhs) i hf hi
        obtain ⟨k', tX, vX, hk', htX, hvX, hrhs⟩ :=
          ih Γ rhs hres hX (hfacts.drop hd k) (hd.drop k) (envWellFormed_drop henv k) htrhs
        rw [halts_unique hhalt hrhs] at hvx
        refine ⟨k + k', tX, vX, by simp at hk'; omega, ?_, ?_, halts_var_of_lookup hvx⟩
        · rw [← List.drop_drop]; exact htX
        · rw [← dropEnv_add]; exact hvX
    | App g X' =>
      rw [resolveHead_app] at hres
      simp only [Expr.App.injEq] at hres
      obtain ⟨hg, rfl⟩ := hres
      obtain ⟨tg, tX, htg, htX, rfl⟩ := lowerTotalExpr_app_some hlow
      have hgb := resolveHead_forced_halts n Γ g hg (b := b) (rem := expectedArgs b) rfl
        hfacts hd htg
      obtain ⟨vX, hvX⟩ := atomic_halts hX henv htX
      exact ⟨0, tX, vX, by omega, by simpa using htX, by simpa using hvX, apply_builtin hgb hvX⟩
    | Force _ => rw [resolveHead_force] at hres; cases hres
    | Lit _ | Error | Lam _ _ | Fix _ _ | Delay _ | Constr _ _ | Case _ _ | Let _ _ | Builtin _ =>
      simp only [resolveHead] at hres; cases hres

/-- A resolved saturated binary builtin application with atomic arguments
    returns the builtin's result on the values its arguments had where they
    were evaluated. -/
theorem resolve_saturated {b : BuiltinFun} (hb : Binary b) :
    ∀ (n : Nat) (Γ : List (VarId × Expr)) (s : Expr) {X Y : Expr} {env : List VarId} {ρ : CekEnv}
      {ts : Term}, resolveHead n Γ s = .App (.App (.Builtin b) X) Y → Atomic X → Atomic Y →
      FactsHold Produces Γ env ρ → EnvDistinct env → EnvWellFormed env.length ρ →
      lowerTotalExpr env s = some ts →
      ∃ kX tX vX kY tY vY, kX ≤ env.length ∧ kY ≤ env.length ∧
        lowerTotalExpr (env.drop kX) X = some tX ∧ Halts (dropEnv kX ρ) tX vX ∧
        lowerTotalExpr (env.drop kY) Y = some tY ∧ Halts (dropEnv kY ρ) tY vY ∧
        ∀ r, evalBuiltin b [vY, vX] = some r → Halts ρ ts r := by
  intro n
  induction n with
  | zero =>
    intro Γ s X Y env ρ ts hres hX hY hfacts hd henv hlow
    rw [resolveHead_zero] at hres; subst hres
    obtain ⟨tf, tY, htf, htY, rfl⟩ := lowerTotalExpr_app_some hlow
    obtain ⟨k, tX, vX, hk, htX, hvX, hf⟩ :=
      resolve_partial hb 0 Γ (.App (.Builtin b) X) (resolveHead_zero Γ _) hX hfacts hd henv htf
    obtain ⟨vY, hvY⟩ := atomic_halts hY henv htY
    exact ⟨k, tX, vX, 0, tY, vY, hk, by omega, htX, hvX, by simpa using htY, by simpa using hvY,
      fun r hr => halts_apply_intro hf hvY (builtin_final_reaches rfl rfl hr)⟩
  | succ n ih =>
    intro Γ s X Y env ρ ts hres hX hY hfacts hd henv hlow
    cases s with
    | Var x =>
      rw [resolveHead_var] at hres
      cases hf : Γ.find? (fun entry => entry.1 == x) with
      | none => rw [hf] at hres; cases hres
      | some entry =>
        obtain ⟨y, rhs⟩ := entry
        rw [hf] at hres
        obtain ⟨i, hi, rfl⟩ := lowerTotalExpr_var_some hlow
        obtain ⟨vx, k, hik, hk, hvx, ⟨trhs, htrhs, hhalt⟩⟩ := hfacts x (y, rhs) i hf hi
        obtain ⟨kX, tX, vX, kY, tY, vY, hkX, hkY, htX, hvX, htY, hvY, hr⟩ :=
          ih Γ rhs hres hX hY (hfacts.drop hd k) (hd.drop k) (envWellFormed_drop henv k) htrhs
        refine ⟨k + kX, tX, vX, k + kY, tY, vY, by simp at hkX; omega, by simp at hkY; omega,
          ?_, ?_, ?_, ?_, fun r heval => ?_⟩
        · rw [← List.drop_drop]; exact htX
        · rw [← dropEnv_add]; exact hvX
        · rw [← List.drop_drop]; exact htY
        · rw [← dropEnv_add]; exact hvY
        · rw [halts_unique hhalt (hr r heval)] at hvx
          exact halts_var_of_lookup hvx
    | App f a =>
      rw [resolveHead_app] at hres
      simp only [Expr.App.injEq] at hres
      obtain ⟨hf, rfl⟩ := hres
      obtain ⟨tf, tY, htf, htY, rfl⟩ := lowerTotalExpr_app_some hlow
      obtain ⟨k, tX, vX, hk, htX, hvX, hfv⟩ := resolve_partial hb n Γ f hf hX hfacts hd henv htf
      obtain ⟨vY, hvY⟩ := atomic_halts hY henv htY
      exact ⟨k, tX, vX, 0, tY, vY, hk, by omega, htX, hvX, by simpa using htY, by simpa using hvY,
        fun r hr => halts_apply_intro hfv hvY (builtin_final_reaches rfl rfl hr)⟩
    | Force _ => rw [resolveHead_force] at hres; cases hres
    | Lit _ | Error | Lam _ _ | Fix _ _ | Delay _ | Constr _ _ | Case _ _ | Let _ _ | Builtin _ =>
      simp only [resolveHead] at hres; cases hres

/-! ## Tag tests -/

theorem evalBuiltin_equalsInteger (x y : Int) :
    evalBuiltin .EqualsInteger [.VCon (.Integer y), .VCon (.Integer x)] =
      some (.VCon (.Bool (x == y))) := rfl

theorem int_beq_comm (a b : Int) : (a == b) = (b == a) := by
  rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]; exact eq_comm

/-- The current value of a known integer variable. -/
theorem knownInteger_var {Γ : List (VarId × Expr)} {t : VarId} {env : List VarId} {ρ : CekEnv}
    {i : Nat} {v : CekValue} (hint : knownInteger 64 Γ (.Var t) = true)
    (hfacts : FactsHold Produces Γ env ρ) (hd : EnvDistinct env) (hi : envLookupT env t = some i)
    (hv : ρ.lookup (i + 1) = some v) : ∃ n, v = .VCon (.Integer n) :=
  knownInteger_sound (fun _ _ _ _ h => h) 64 Γ (.Var t) hint hfacts hd
    (by rw [lowerTotalExpr_var, hi]; rfl) (halts_var_of_lookup hv)

/-- A tag test returns whether the current value of its tag is its literal. -/
theorem tagTest_sound {Γ : List (VarId × Expr)} {s : Expr} {t : VarId} {c : Int}
    {env : List VarId} {ρ : CekEnv} {ts : Term}
    (h : tagTest Γ s = some (t, c)) (hfacts : FactsHold Produces Γ env ρ) (hd : EnvDistinct env)
    (henv : EnvWellFormed env.length ρ) (hlow : lowerTotalExpr env s = some ts) :
    ∃ i n, envLookupT env t = some i ∧ ρ.lookup (i + 1) = some (.VCon (.Integer n)) ∧
      Halts ρ ts (.VCon (.Bool (n == c))) := by
  have hb : Binary .EqualsInteger := rfl
  unfold tagTest at h
  split at h
  · rename_i subject value ty hres
    split at h
    · rename_i hint
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨kX, tX, vX, kY, tY, vY, _, _, htX, hvX, htY, hvY, hr⟩ :=
        resolve_saturated hb 64 Γ s hres (.inl ⟨_, rfl⟩) (.inr ⟨_, rfl⟩) hfacts hd henv hlow
      obtain ⟨i, hi, hlook⟩ := halts_var_drop hd htX hvX
      obtain ⟨n, rfl⟩ := knownInteger_var hint hfacts hd hi hlook
      rw [lowerTotalExpr_lit] at htY; cases htY
      rw [halts_constant hvY] at hr
      exact ⟨i, n, hi, hlook, hr _ (evalBuiltin_equalsInteger n value)⟩
    · cases h
  · rename_i value ty subject hres
    split at h
    · rename_i hint
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨kX, tX, vX, kY, tY, vY, _, _, htX, hvX, htY, hvY, hr⟩ :=
        resolve_saturated hb 64 Γ s hres (.inr ⟨_, rfl⟩) (.inl ⟨_, rfl⟩) hfacts hd henv hlow
      obtain ⟨i, hi, hlook⟩ := halts_var_drop hd htY hvY
      obtain ⟨n, rfl⟩ := knownInteger_var hint hfacts hd hi hlook
      rw [lowerTotalExpr_lit] at htX; cases htX
      rw [halts_constant hvX] at hr
      have := hr _ (evalBuiltin_equalsInteger value n)
      rw [int_beq_comm value n] at this
      exact ⟨i, n, hi, hlook, this⟩
    · cases h
  · cases h

/-! ## Bindings that return -/

theorem binary_of_comparison {b : BuiltinFun}
    (h : (b == .EqualsInteger || b == .LessThanInteger || b == .LessThanEqualsInteger) = true) :
    Binary b := by
  cases b <;> first | exact rfl | exact absurd h (by decide)

theorem tagReturns_halts {Γ : List (VarId × Expr)} {e : Expr} {env : List VarId} {ρ : CekEnv}
    {te : Term} (h : tagReturns Γ e = true) (hfacts : FactsHold Produces Γ env ρ)
    (hd : EnvDistinct env) (henv : EnvWellFormed env.length ρ)
    (hlow : lowerTotalExpr env e = some te) : ∃ v, Halts ρ te v := by
  unfold tagReturns at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨⟨t, c⟩, htest⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨_, _, _, _, hv⟩ := tagTest_sound htest hfacts hd henv hlow
    exact ⟨_, hv⟩
  · cases e with
    | App f a =>
      simp only at h
      split at h
      · rename_i b hres
        simp only [Bool.and_eq_true] at h
        obtain ⟨hb, ha⟩ := h
        have hbin := binary_of_comparison hb
        have hatom : Atomic a := by
          cases a <;> simp at ha
          · exact .inl ⟨_, rfl⟩
          · exact .inr ⟨_, rfl⟩
        obtain ⟨tf, ta, htf, hta, rfl⟩ := lowerTotalExpr_app_some hlow
        have hf := resolveHead_forced_halts 64 Γ f hres (b := b) (rem := expectedArgs b) rfl
          hfacts hd htf
        obtain ⟨va, hva⟩ := atomic_halts hatom henv hta
        refine ⟨.VBuiltin b [va] (.one .argV), halts_apply_intro hf hva ?_⟩
        rw [hbin]
        exact builtin_partial_reaches rfl rfl
      · cases h
    | _ => simp at h

end Moist.Verified.TagChains
