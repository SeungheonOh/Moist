import Moist.MIR.Optimize.Advanced.DataShapes
import Moist.Verified.ShapesSoundness.Simplify
import Moist.Verified.AdvancedTraversal

variable [sv : Moist.CEK.SemVariant]

/-! # Kind guards

`specializeDataChecks` replaces a kind guard

```
force (ifThenElse (chooseData x c₀ … c₄) (delay x) (delay error))
```

whose single `True` branch selects one `Data` kind by `let _ = unK x in x`, where
`unK` is the unData builtin of that kind: both fail unless `x` is a `Data`
value of that kind and otherwise return `x` (`specializeDataChecks_refines`).
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines Moist.Verified.MIR

/-! ## Evaluation of a kind guard -/

theorem errs_apply_fun {ρ : CekEnv} {tf ta : Term} (hf : Errs ρ tf) : Errs ρ (.Apply tf ta) :=
  reaches_trans (reaches_of_steps 1 rfl) (errs_on_stack hf _)

theorem errs_force {ρ : CekEnv} {t : Term} (h : Errs ρ t) : Errs ρ (.Force t) :=
  reaches_trans (reaches_of_steps 1 rfl) (errs_on_stack h _)

def kindOf : Moist.Plutus.Data → Nat
  | .Constr _ _ => 0
  | .Map _ => 1
  | .List _ => 2
  | .I _ => 3
  | .B _ => 4

def selectKind (bs : List Bool) (d : Moist.Plutus.Data) : Bool := bs.getD (kindOf d) false

theorem chooseData_bools (b₀ b₁ b₂ b₃ b₄ : Bool) (d : Moist.Plutus.Data) :
    evalBuiltin .ChooseData [.VCon (.Bool b₄), .VCon (.Bool b₃), .VCon (.Bool b₂),
      .VCon (.Bool b₁), .VCon (.Bool b₀), .VCon (.Data d)] =
      some (.VCon (.Bool (selectKind [b₀, b₁, b₂, b₃, b₄] d))) := by
  cases d <;> rfl

theorem chooseData_bools_none (b₀ b₁ b₂ b₃ b₄ : Bool) {vx : CekValue}
    (h : ∀ d, vx ≠ .VCon (.Data d)) :
    evalBuiltin .ChooseData [.VCon (.Bool b₄), .VCon (.Bool b₃), .VCon (.Bool b₂),
      .VCon (.Bool b₁), .VCon (.Bool b₀), vx] = none := by
  cases vx with
  | VCon c =>
    cases c
    all_goals first | (exact absurd rfl (h _)) | rfl
  | _ => rfl

/-- The unData builtin of the selected kind succeeds exactly on that kind. -/
theorem kindChecker_spec {b₀ b₁ b₂ b₃ b₄ : Bool} {checker : BuiltinFun}
    (h : kindChecker [b₀, b₁, b₂, b₃, b₄] = some checker) :
    expectedArgs checker = .one .argV ∧
      (∀ d, selectKind [b₀, b₁, b₂, b₃, b₄] d = true →
        ∃ r, evalBuiltin checker [.VCon (.Data d)] = some r) ∧
      (∀ d, selectKind [b₀, b₁, b₂, b₃, b₄] d = false →
        evalBuiltin checker [.VCon (.Data d)] = none) ∧
      (∀ vx, (∀ d, vx ≠ .VCon (.Data d)) → evalBuiltin checker [vx] = none) := by
  cases b₀ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;> simp [kindChecker] at h <;> subst h
  all_goals refine ⟨rfl, fun d hd => ?_, fun d hd => ?_, fun vx hvx => ?_⟩
  all_goals first
    | (cases d <;> first | exact ⟨_, rfl⟩ | rfl | (exfalso; simp [selectKind, kindOf] at hd))
    | (cases vx with
       | VCon c =>
         cases c
         all_goals first | (exact absurd rfl (hvx _)) | rfl
       | _ => rfl)

omit sv in
theorem kindGuard_spec {condition : Expr} {y : VarId} {checker : BuiltinFun}
    (h : kindGuard condition = some (y, checker)) :
    ∃ b₀ b₁ b₂ b₃ b₄ t₀ t₁ t₂ t₃ t₄,
      condition = .App (.App (.App (.App (.App (.App (.Force (.Builtin .ChooseData)) (.Var y))
        (.Lit (.Bool b₀, t₀))) (.Lit (.Bool b₁, t₁))) (.Lit (.Bool b₂, t₂))) (.Lit (.Bool b₃, t₃)))
        (.Lit (.Bool b₄, t₄)) ∧
      kindChecker [b₀, b₁, b₂, b₃, b₄] = some checker := by
  unfold kindGuard at h
  split at h
  · rename_i x c₀ c₁ c₂ c₃ c₄
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨b₀, h₀, b₁, h₁, b₂, h₂, b₃, h₃, b₄, h₄, k, hk, rfl, rfl⟩ := h
    cases c₀ <;> simp [boolLiteral?] at h₀
    cases c₁ <;> simp [boolLiteral?] at h₁
    cases c₂ <;> simp [boolLiteral?] at h₂
    cases c₃ <;> simp [boolLiteral?] at h₃
    cases c₄ <;> simp [boolLiteral?] at h₄
    rename_i l₀ l₁ l₂ l₃ l₄
    obtain ⟨c₀, t₀⟩ := l₀; obtain ⟨c₁, t₁⟩ := l₁; obtain ⟨c₂, t₂⟩ := l₂
    obtain ⟨c₃, t₃⟩ := l₃; obtain ⟨c₄, t₄⟩ := l₄
    cases c₀ <;> simp at h₀
    cases c₁ <;> simp at h₁
    cases c₂ <;> simp at h₂
    cases c₃ <;> simp at h₃
    cases c₄ <;> simp at h₄
    subst h₀ h₁ h₂ h₃ h₄
    exact ⟨_, _, _, _, _, t₀, t₁, t₂, t₃, t₄, rfl, hk⟩
  · cases h

theorem halts_delay_of {ρ : CekEnv} (body : Term) : Halts ρ (.Delay body) (.VDelay body ρ) :=
  ⟨2, rfl⟩

def guardTerm (ix : Nat) (b₀ b₁ b₂ b₃ b₄ : Bool) (t₀ t₁ t₂ t₃ t₄ : BuiltinType) : Term :=
  .Force (.Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse))
    (.Apply (.Apply (.Apply (.Apply (.Apply (.Apply (.Force (.Builtin .ChooseData)) (.Var (ix + 1)))
      (.Constant (.Bool b₀, t₀))) (.Constant (.Bool b₁, t₁))) (.Constant (.Bool b₂, t₂)))
      (.Constant (.Bool b₃, t₃))) (.Constant (.Bool b₄, t₄))))
    (.Delay (.Var (ix + 1)))) (.Delay .Error))

def checkTerm (ix : Nat) (checker : BuiltinFun) : Term :=
  .Apply (.Lam 0 (.Var (ix + 2))) (.Apply (.Builtin checker) (.Var (ix + 1)))

theorem guard_obs {ρ : CekEnv} {π : Stack} {ix : Nat} {vx : CekValue}
    {b₀ b₁ b₂ b₃ b₄ : Bool} {t₀ t₁ t₂ t₃ t₄ : BuiltinType} {checker : BuiltinFun}
    (hk : kindChecker [b₀, b₁, b₂, b₃, b₄] = some checker)
    (hvx : ρ.lookup (ix + 1) = some vx) :
    ObsRefines (.compute π ρ (guardTerm ix b₀ b₁ b₂ b₃ b₄ t₀ t₁ t₂ t₃ t₄))
      (.compute π ρ (checkTerm ix checker)) := by
  obtain ⟨hargs, hsome, hnone, hother⟩ := kindChecker_spec hk
  have hx := halts_var_of_lookup (ρ := ρ) hvx
  have hc : ∀ (b : Bool) (t : BuiltinType), Halts ρ (.Constant (.Bool b, t)) (.VCon (.Bool b)) :=
    fun b t => halts_constant_of _ _
  have hite : Halts ρ (.Force (.Builtin .IfThenElse))
      (.VBuiltin .IfThenElse [] (.more .argV (.more .argV (.one .argV)))) := ⟨4, rfl⟩
  have hpart := halts_choose_partial hx (hc b₀ t₀) (hc b₁ t₁) (hc b₂ t₂) (hc b₃ t₃)
  have hlam : Halts ρ (.Lam 0 (.Var (ix + 2))) (.VLam (.Var (ix + 2)) ρ) := ⟨2, rfl⟩
  by_cases hdata : ∃ d, vx = .VCon (.Data d)
  · obtain ⟨d, rfl⟩ := hdata
    have hcond := halts_apply_intro hpart (hc b₄ t₄)
      (builtin_final_reaches rfl rfl (chooseData_bools b₀ b₁ b₂ b₃ b₄ d))
    generalize hsel : selectKind [b₀, b₁, b₂, b₃, b₄] d = sel at hcond
    have hinner := halts_apply_intro (halts_apply_intro
      (halts_apply_intro hite hcond (builtin_partial_reaches rfl rfl))
      (halts_delay_of (ρ := ρ) (.Var (ix + 1))) (builtin_partial_reaches rfl rfl))
      (halts_delay_of (ρ := ρ) .Error)
      (builtin_final_reaches (args := [.VDelay (.Var (ix + 1)) ρ, .VCon (.Bool sel)]) rfl rfl rfl)
    have hsrc : Reaches (.compute π ρ (guardTerm ix b₀ b₁ b₂ b₃ b₄ t₀ t₁ t₂ t₃ t₄))
        (.compute π ρ (if sel then .Var (ix + 1) else .Error)) := by
      refine reaches_trans (reaches_of_steps 1 rfl) (reaches_trans (halts_on_stack hinner _) ?_)
      refine reaches_of_steps 1 ?_
      cases sel <;> rfl
    cases sel
    · refine obsRefines_of_reaches (reaches_trans hsrc ⟨1, rfl⟩) (errs_on_stack ?_ π)
        (obsRefines_refl _)
      exact errs_apply_arg hlam (errs_apply_intro (halts_builtin_of ρ _) hx
        (builtin_final_errs (by rw [hargs]; rfl) (by rw [hargs]; rfl) (hnone d hsel)))
    · obtain ⟨r, hr⟩ := hsome d hsel
      refine obsRefines_of_reaches (reaches_trans hsrc (halts_on_stack hx π)) (halts_on_stack ?_ π)
        (obsRefines_refl _)
      refine halts_apply_intro hlam (halts_apply_intro (halts_builtin_of ρ _) hx
        (builtin_final_reaches (by rw [hargs]; rfl) (by rw [hargs]; rfl) hr)) ?_
      refine ⟨3, ?_⟩
      show step (step (step (.ret [.funV (.VLam (.Var (ix + 2)) ρ)] r))) = _
      simp [step, CekEnv.extend, CekEnv.lookup, hvx]
  · have hnot : ∀ d, vx ≠ .VCon (.Data d) := fun d h => hdata ⟨d, h⟩
    have hcond : Errs ρ _ := errs_apply_intro hpart (hc b₄ t₄)
      (builtin_final_errs rfl rfl (chooseData_bools_none b₀ b₁ b₂ b₃ b₄ hnot))
    refine obsRefines_of_reaches (errs_on_stack ?_ π) (errs_on_stack ?_ π) (obsRefines_refl _)
    · exact errs_force (errs_apply_fun (errs_apply_fun (errs_apply_arg hite hcond)))
    · exact errs_apply_arg hlam (errs_apply_intro (halts_builtin_of ρ _) hx
        (builtin_final_errs (by rw [hargs]; rfl) (by rw [hargs]; rfl) (hother vx hnot)))

omit sv in
theorem checkedBinder_ne (x : VarId) : (checkedBinder x == x) = false := by
  cases h : (checkedBinder x == x)
  · rfl
  · rw [VarId.beq_true_iff] at h
    simp [checkedBinder] at h

theorem kindGuard_refines {condition : Expr} {x y : VarId} {checker : BuiltinFun}
    (hg : kindGuard condition = some (y, checker)) (hxy : (y == x) = true) :
    MIRCtxRefines
      (.Force (.App (.App (.App (.Force (.Builtin .IfThenElse)) condition) (.Delay (.Var x)))
        (.Delay .Error)))
      (.Let [(checkedBinder x, .App (.Builtin checker) (.Var x), false)] (.Var x)) := by
  obtain ⟨b₀, b₁, b₂, b₃, b₄, t₀, t₁, t₂, t₃, t₄, rfl, hk⟩ := kindGuard_spec hg
  intro env
  have hyx := envLookupT_congr hxy env
  cases hx : envLookupT env x with
  | none =>
    have : lowerTotalExpr env (.Force (.App (.App (.App (.Force (.Builtin .IfThenElse))
        (.App (.App (.App (.App (.App (.App (.Force (.Builtin .ChooseData)) (.Var y))
          (.Lit (.Bool b₀, t₀))) (.Lit (.Bool b₁, t₁))) (.Lit (.Bool b₂, t₂))) (.Lit (.Bool b₃, t₃)))
          (.Lit (.Bool b₄, t₄)))) (.Delay (.Var x))) (.Delay .Error))) = none := by
      simp [MIR.lowerTotalExpr_app, MIR.lowerTotalExpr_force, MIR.lowerTotalExpr_delay,
        lowerTotalExpr_var, lowerTotalExpr_builtin, lowerTotalExpr_lit, hyx, hx]
    rw [this]
    refine ⟨fun h => ?_, ?_⟩
    · simp at h
    · simp
  | some ix =>
    have hsrc : lowerTotalExpr env (.Force (.App (.App (.App (.Force (.Builtin .IfThenElse))
        (.App (.App (.App (.App (.App (.App (.Force (.Builtin .ChooseData)) (.Var y))
          (.Lit (.Bool b₀, t₀))) (.Lit (.Bool b₁, t₁))) (.Lit (.Bool b₂, t₂))) (.Lit (.Bool b₃, t₃)))
          (.Lit (.Bool b₄, t₄)))) (.Delay (.Var x))) (.Delay .Error))) =
        some (guardTerm ix b₀ b₁ b₂ b₃ b₄ t₀ t₁ t₂ t₃ t₄) := by
      simp [guardTerm, MIR.lowerTotalExpr_app, MIR.lowerTotalExpr_force, MIR.lowerTotalExpr_delay,
        lowerTotalExpr_var, lowerTotalExpr_builtin, lowerTotalExpr_lit, lowerTotalExpr_error, hyx, hx]
    have htgt : lowerTotalExpr env
        (.Let [(checkedBinder x, .App (.Builtin checker) (.Var x), false)] (.Var x)) =
        some (checkTerm ix checker) := by
      rw [lowerTotalExpr_let_single]
      simp [checkTerm, MIR.lowerTotalExpr_app, lowerTotalExpr_var, lowerTotalExpr_builtin, hx,
        envLookupT_cons_neq _ _ _ (checkedBinder_ne x)]
    rw [hsrc, htgt]
    refine ⟨fun _ => rfl, ?_⟩
    have hclosed := MIR.lowerTotalExpr_closedAt hsrc
    apply ctxRefines_of_factRefines hclosed
    · intro k hk'
      simp [guardTerm, closedAt] at hk'
      simp [checkTerm, closedAt]
      omega
    · intro ρ π henv _ _ _
      have hbound := envLookupT_bound env x ix hx
      obtain ⟨vx, hvx, _⟩ := envWellFormed_lookup env.length henv (n := ix + 1) (by omega) (by omega)
      exact guard_obs hk hvx

theorem dataCheckRewrite_refines (e : Expr) : MIRCtxRefines e (dataCheckRewrite e) := by
  unfold dataCheckRewrite
  split
  · rename_i condition x
    split
    · rename_i y checker hg
      split
      · rename_i hxy
        exact kindGuard_refines hg hxy
      · exact mirCtxRefines_refl _
    · exact mirCtxRefines_refl _
  · exact mirCtxRefines_refl _

end Moist.Verified.ShapeFacts

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced

theorem specializeDataChecks_refines (e : Expr) : MIRCtxRefines e (specializeDataChecks e) := by
  unfold specializeDataChecks
  apply rewriteBottomUp_refines dataCheckRewrite ShapeFacts.dataCheckRewrite_refines
  intro binder body
  simp [dataCheckRewrite]

end Moist.Verified.MIR
