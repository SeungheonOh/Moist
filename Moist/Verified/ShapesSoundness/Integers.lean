import Moist.Verified.ShapesSoundness.Rewrites

variable [sv : Moist.CEK.SemVariant]

/-! # Integer identities

Arithmetic with a neutral or absorbing literal, and comparisons of a known
integer with itself, are replaced by the operand or by a constant. An
absorbed operand is still evaluated unless the facts show that it returns.
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines

/-! ## Builtin results -/

def binaryInteger (b : BuiltinFun) : Prop := expectedArgs b = .more .argV (.one .argV)

theorem eval_add_zero_left (y : Int) :
    evalBuiltin .AddInteger [.VCon (.Integer y), .VCon (.Integer 0)] = some (.VCon (.Integer y)) := by
  have : evalBuiltin .AddInteger [.VCon (.Integer y), .VCon (.Integer 0)] =
      some (.VCon (.Integer (0 + y))) := rfl
  rw [this]; simp

theorem eval_add_zero_right (x : Int) :
    evalBuiltin .AddInteger [.VCon (.Integer 0), .VCon (.Integer x)] = some (.VCon (.Integer x)) := by
  have : evalBuiltin .AddInteger [.VCon (.Integer 0), .VCon (.Integer x)] =
      some (.VCon (.Integer (x + 0))) := rfl
  rw [this]; simp

theorem eval_sub_zero_right (x : Int) :
    evalBuiltin .SubtractInteger [.VCon (.Integer 0), .VCon (.Integer x)] = some (.VCon (.Integer x)) := by
  have : evalBuiltin .SubtractInteger [.VCon (.Integer 0), .VCon (.Integer x)] =
      some (.VCon (.Integer (x - 0))) := rfl
  rw [this]; simp

theorem eval_sub_self (x : Int) :
    evalBuiltin .SubtractInteger [.VCon (.Integer x), .VCon (.Integer x)] = some (.VCon (.Integer 0)) := by
  have : evalBuiltin .SubtractInteger [.VCon (.Integer x), .VCon (.Integer x)] =
      some (.VCon (.Integer (x - x))) := rfl
  rw [this]; simp

theorem eval_mul_one_left (y : Int) :
    evalBuiltin .MultiplyInteger [.VCon (.Integer y), .VCon (.Integer 1)] = some (.VCon (.Integer y)) := by
  have : evalBuiltin .MultiplyInteger [.VCon (.Integer y), .VCon (.Integer 1)] =
      some (.VCon (.Integer (1 * y))) := rfl
  rw [this]; simp

theorem eval_mul_one_right (x : Int) :
    evalBuiltin .MultiplyInteger [.VCon (.Integer 1), .VCon (.Integer x)] = some (.VCon (.Integer x)) := by
  have : evalBuiltin .MultiplyInteger [.VCon (.Integer 1), .VCon (.Integer x)] =
      some (.VCon (.Integer (x * 1))) := rfl
  rw [this]; simp

theorem eval_mul_zero_left (y : Int) :
    evalBuiltin .MultiplyInteger [.VCon (.Integer y), .VCon (.Integer 0)] = some (.VCon (.Integer 0)) := by
  have : evalBuiltin .MultiplyInteger [.VCon (.Integer y), .VCon (.Integer 0)] =
      some (.VCon (.Integer (0 * y))) := rfl
  rw [this]; simp

theorem eval_mul_zero_right (x : Int) :
    evalBuiltin .MultiplyInteger [.VCon (.Integer 0), .VCon (.Integer x)] = some (.VCon (.Integer 0)) := by
  have : evalBuiltin .MultiplyInteger [.VCon (.Integer 0), .VCon (.Integer x)] =
      some (.VCon (.Integer (x * 0))) := rfl
  rw [this]; simp

theorem eval_div_one (x : Int) :
    evalBuiltin .DivideInteger [.VCon (.Integer 1), .VCon (.Integer x)] = some (.VCon (.Integer x)) := by
  have : evalBuiltin .DivideInteger [.VCon (.Integer 1), .VCon (.Integer x)] =
      some (.VCon (.Integer (if x.tmod 1 == 0 || (x >= 0) == ((1:Int) >= 0) then x.tdiv 1
        else x.tdiv 1 - 1))) := rfl
  rw [this]; simp

theorem eval_quot_one (x : Int) :
    evalBuiltin .QuotientInteger [.VCon (.Integer 1), .VCon (.Integer x)] = some (.VCon (.Integer x)) := by
  have : evalBuiltin .QuotientInteger [.VCon (.Integer 1), .VCon (.Integer x)] =
      some (.VCon (.Integer (x.tdiv 1))) := rfl
  rw [this]; simp

theorem eval_rem_one (x : Int) :
    evalBuiltin .RemainderInteger [.VCon (.Integer 1), .VCon (.Integer x)] = some (.VCon (.Integer 0)) := by
  have : evalBuiltin .RemainderInteger [.VCon (.Integer 1), .VCon (.Integer x)] =
      some (.VCon (.Integer (x.tmod 1))) := rfl
  rw [this]; simp

theorem eval_mod_one (x : Int) :
    evalBuiltin .ModInteger [.VCon (.Integer 1), .VCon (.Integer x)] = some (.VCon (.Integer 0)) := by
  have : evalBuiltin .ModInteger [.VCon (.Integer 1), .VCon (.Integer x)] =
      some (.VCon (.Integer (x - 1 * (if x.tmod 1 == 0 || (x >= 0) == ((1:Int) >= 0) then x.tdiv 1
        else x.tdiv 1 - 1)))) := rfl
  rw [this]; simp

theorem eval_equals_self (x : Int) :
    evalBuiltin .EqualsInteger [.VCon (.Integer x), .VCon (.Integer x)] = some (.VCon (.Bool true)) := by
  have : evalBuiltin .EqualsInteger [.VCon (.Integer x), .VCon (.Integer x)] =
      some (.VCon (.Bool (x == x))) := rfl
  rw [this]; simp

theorem eval_lessThan_self (x : Int) :
    evalBuiltin .LessThanInteger [.VCon (.Integer x), .VCon (.Integer x)] = some (.VCon (.Bool false)) := by
  have : evalBuiltin .LessThanInteger [.VCon (.Integer x), .VCon (.Integer x)] =
      some (.VCon (.Bool (decide (x < x)))) := rfl
  rw [this]; simp

theorem eval_lessThanEquals_self (x : Int) :
    evalBuiltin .LessThanEqualsInteger [.VCon (.Integer x), .VCon (.Integer x)] =
      some (.VCon (.Bool true)) := by
  have : evalBuiltin .LessThanEqualsInteger [.VCon (.Integer x), .VCon (.Integer x)] =
      some (.VCon (.Bool (decide (x ≤ x)))) := rfl
  rw [this]; simp

/-! ## Machine steps of a binary builtin application -/

theorem bin_head (b : BuiltinFun) (π : Stack) (ρ : CekEnv) (tf ta : Term) :
    steps 4 (.compute π ρ (.Apply (.Apply (.Builtin b) tf) ta)) =
      .compute (.funV (.VBuiltin b [] (expectedArgs b)) :: .arg ta ρ :: π) ρ tf := rfl

theorem bin_mid {b : BuiltinFun} (hb : binaryInteger b) (π : Stack) (ρ : CekEnv) (ta : Term)
    (vf : CekValue) :
    steps 2 (.ret (.funV (.VBuiltin b [] (expectedArgs b)) :: .arg ta ρ :: π) vf) =
      .compute (.funV (.VBuiltin b [vf] (.one .argV)) :: π) ρ ta := by
  unfold binaryInteger at hb
  simp [steps, step, hb, ExpectedArgs.head, ExpectedArgs.tail]

theorem bin_final {b : BuiltinFun} {π : Stack} {va vf r : CekValue}
    (h : evalBuiltin b [va, vf] = some r) :
    steps 1 (.ret (.funV (.VBuiltin b [vf] (.one .argV)) :: π) va) = .ret π r := by
  simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, h]

theorem lowerTotalExpr_binary {env : List VarId} {b : BuiltinFun} {e₁ e₂ : Expr} {t : Term}
    (h : lowerTotalExpr env (.App (.App (.Builtin b) e₁) e₂) = some t) :
    ∃ t₁ t₂, lowerTotalExpr env e₁ = some t₁ ∧ lowerTotalExpr env e₂ = some t₂ ∧
      t = .Apply (.Apply (.Builtin b) t₁) t₂ := by
  obtain ⟨tf, t₂, htf, ht₂, rfl⟩ := lowerTotalExpr_app_some h
  obtain ⟨tb, t₁, htb, ht₁, rfl⟩ := lowerTotalExpr_app_some htf
  rw [lowerTotalExpr_builtin] at htb; cases htb
  exact ⟨t₁, t₂, ht₁, ht₂, rfl⟩

def intLit (k : Int) : Expr := .Lit (.Integer k, .AtomicType .TypeInteger)

theorem lowerTotalExpr_intLit (env : List VarId) (k : Int) :
    lowerTotalExpr env (intLit k) = some (.Constant (.Integer k, .AtomicType .TypeInteger)) :=
  lowerTotalExpr_lit env _ _

/-- The source reaches the evaluation of its right operand once the literal
    left operand is in place. -/
theorem left_literal_reaches {b : BuiltinFun} (hb : binaryInteger b) (π : Stack) (ρ : CekEnv) (k : Int)
    (t₂ : Term) :
    Reaches (.compute π ρ (.Apply (.Apply (.Builtin b) (.Constant (.Integer k, .AtomicType .TypeInteger))) t₂))
      (.compute (.funV (.VBuiltin b [.VCon (.Integer k)] (.one .argV)) :: π) ρ t₂) :=
  reaches_trans (reaches_of_steps 4 (bin_head b π ρ _ t₂))
    (reaches_trans (halts_on_stack (halts_constant_of _ _) _) (reaches_of_steps 2 (bin_mid hb π ρ t₂ _)))

theorem right_literal_finish {b : BuiltinFun} (hb : binaryInteger b) {π : Stack} {ρ : CekEnv} {k : Int}
    {vf r : CekValue} (h : evalBuiltin b [.VCon (.Integer k), vf] = some r) :
    Reaches (.ret (.funV (.VBuiltin b [] (expectedArgs b)) ::
        .arg (.Constant (.Integer k, .AtomicType .TypeInteger)) ρ :: π) vf) (.ret π r) :=
  reaches_trans (reaches_of_steps 2 (bin_mid hb π ρ _ vf))
    (reaches_trans (halts_on_stack (halts_constant_of _ _) _) (reaches_of_steps 1 (bin_final h)))

/-! ## Identities -/

/-- A neutral literal on the left. -/
theorem left_neutral_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {b : BuiltinFun} {k : Int}
    {e₂ : Expr} (hb : binaryInteger b) (hknown : knownInteger 64 Γ e₂ = true)
    (hop : ∀ y, evalBuiltin b [.VCon (.Integer y), .VCon (.Integer k)] = some (.VCon (.Integer y))) :
    FactRel G PF Γ (.App (.App (.Builtin b) (intLit k)) e₂) e₂ := by
  intro env t hG hd hfresh hk hsc hlow
  obtain ⟨t₁, t₂, ht₁, ht₂, rfl⟩ := lowerTotalExpr_binary hlow
  rw [lowerTotalExpr_intLit] at ht₁; cases ht₁
  refine ⟨t₂, ht₂, ?_⟩
  intro ρ π henv hlen hπ hF
  refine obsRefines_of_reaches (left_literal_reaches hb π ρ k t₂) (reaches_refl _) ?_
  refine obsRefines_of_continuation ?_
  intro v hv
  obtain ⟨y, rfl⟩ := knownInteger_sound PF_produces 64 Γ e₂ hknown hF hd ht₂ hv
  exact obsRefines_of_reaches (reaches_of_steps 1 (bin_final (hop y))) (reaches_refl _) (obsRefines_refl _)

/-- A neutral literal on the right. -/
theorem right_neutral_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {b : BuiltinFun} {k : Int}
    {e₁ : Expr} (hb : binaryInteger b) (hknown : knownInteger 64 Γ e₁ = true)
    (hop : ∀ x, evalBuiltin b [.VCon (.Integer k), .VCon (.Integer x)] = some (.VCon (.Integer x))) :
    FactRel G PF Γ (.App (.App (.Builtin b) e₁) (intLit k)) e₁ := by
  intro env t hG hd hfresh hk hsc hlow
  obtain ⟨t₁, t₂, ht₁, ht₂, rfl⟩ := lowerTotalExpr_binary hlow
  rw [lowerTotalExpr_intLit] at ht₂; cases ht₂
  refine ⟨t₁, ht₁, ?_⟩
  intro ρ π henv hlen hπ hF
  refine obsRefines_of_reaches (reaches_of_steps 4 (bin_head b π ρ t₁ _)) (reaches_refl _) ?_
  refine obsRefines_of_continuation ?_
  intro v hv
  obtain ⟨x, rfl⟩ := knownInteger_sound PF_produces 64 Γ e₁ hknown hF hd ht₁ hv
  exact obsRefines_of_reaches (right_literal_finish hb (hop x)) (reaches_refl _) (obsRefines_refl _)

/-- A comparison or difference of a known integer variable with itself. -/
theorem self_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {b : BuiltinFun} {l r : VarId}
    {c : Const} {ty : BuiltinType} (hb : binaryInteger b) (hlr : (l == r) = true)
    (hknown : knownInteger 64 Γ (.Var l) = true)
    (hop : ∀ x, evalBuiltin b [.VCon (.Integer x), .VCon (.Integer x)] = some (.VCon c)) :
    FactRel G PF Γ (.App (.App (.Builtin b) (.Var l)) (.Var r)) (.Lit (c, ty)) := by
  intro env t hG hd hfresh hk hsc hlow
  obtain ⟨t₁, t₂, ht₁, ht₂, rfl⟩ := lowerTotalExpr_binary hlow
  obtain ⟨i, hi, rfl⟩ := lowerTotalExpr_var_some ht₁
  rw [lowerTotalExpr_var, ← envLookupT_congr hlr, hi] at ht₂; cases ht₂
  refine ⟨.Constant (c, ty), lowerTotalExpr_lit env c ty, ?_⟩
  intro ρ π henv hlen hπ hF
  obtain ⟨w, hw, _⟩ := envWellFormed_lookup env.length henv (n := i + 1) (by omega)
    (by have := envLookupT_bound env l i hi; omega)
  obtain ⟨x, rfl⟩ := knownInteger_sound PF_produces 64 Γ (.Var l) hknown hF hd ht₁ (halts_var_of_lookup hw)
  have hsrc : Reaches (.compute π ρ (.Apply (.Apply (.Builtin b) (.Var (i + 1))) (.Var (i + 1))))
      (.ret π (.VCon c)) :=
    reaches_trans (reaches_of_steps 4 (bin_head b π ρ _ _))
      (reaches_trans (halts_on_stack (halts_var_of_lookup hw) _)
        (reaches_trans (reaches_of_steps 2 (bin_mid hb π ρ _ _))
          (reaches_trans (halts_on_stack (halts_var_of_lookup hw) _) (reaches_of_steps 1 (bin_final (hop x))))))
  exact obsRefines_of_reaches hsrc (halts_on_stack (halts_constant_of _ _) _) (obsRefines_refl _)

/-! ## Absorbing literals -/

theorem lowerTotalExpr_retain_let {env : List VarId} {u : VarId} {e : Expr} {c : Const} {ty : BuiltinType}
    {t : Term} (h : lowerTotalExpr env e = some t) :
    lowerTotalExpr env (.Let [(u, e, false)] (.Lit (c, ty))) =
      some (.Apply (.Lam 0 (.Constant (c, ty))) t) := by
  rw [lowerTotalExpr_let_single, h, lowerTotalExpr_lit]; rfl

/-- An absorbing literal on the left: the result is the constant, after the
    other operand has been evaluated unless it is known to return. -/
theorem left_absorbing_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {b : BuiltinFun} {k : Int}
    {e₂ : Expr} {c : Const} {ty : BuiltinType} (base : Nat) (hb : binaryInteger b)
    (hknown : knownInteger 64 Γ e₂ = true)
    (hop : ∀ y, evalBuiltin b [.VCon (.Integer y), .VCon (.Integer k)] = some (.VCon c)) :
    FactRel G PF Γ (.App (.App (.Builtin b) (intLit k)) e₂) (retainEvaluation base Γ e₂ (.Lit (c, ty))) := by
  intro env t hG hd hfresh hk hsc hlow
  simp only [freshIn, Bool.and_eq_true] at hfresh
  obtain ⟨t₁, t₂, ht₁, ht₂, rfl⟩ := lowerTotalExpr_binary hlow
  rw [lowerTotalExpr_intLit] at ht₁; cases ht₁
  unfold retainEvaluation
  split
  · rename_i htotal
    refine ⟨.Constant (c, ty), lowerTotalExpr_lit env c ty, ?_⟩
    intro ρ π henv hlen hπ hF
    obtain ⟨v, hv⟩ := totalWithFacts_sound PF_hP 64 Γ e₂ htotal hF hd hfresh.2
      (wellSized_of_wellFormed henv) ht₂
    obtain ⟨y, rfl⟩ := knownInteger_sound PF_produces 64 Γ e₂ hknown hF hd ht₂ hv
    refine obsRefines_of_reaches ?_ (halts_on_stack (halts_constant_of _ _) _) (obsRefines_refl _)
    exact reaches_trans (left_literal_reaches hb π ρ k t₂)
      (reaches_trans (halts_on_stack hv _) (reaches_of_steps 1 (bin_final (hop y))))
  · refine ⟨_, lowerTotalExpr_retain_let ht₂, ?_⟩
    intro ρ π henv hlen hπ hF
    refine obsRefines_of_reaches (left_literal_reaches hb π ρ k t₂) (reaches_of_steps 3 rfl) ?_
    refine obsRefines_of_continuation ?_
    intro v hv
    obtain ⟨y, rfl⟩ := knownInteger_sound PF_produces 64 Γ e₂ hknown hF hd ht₂ hv
    exact obsRefines_of_reaches (reaches_of_steps 1 (bin_final (hop y))) (reaches_of_steps 2 rfl)
      (obsRefines_refl _)

/-- An absorbing literal on the right. -/
theorem right_absorbing_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {b : BuiltinFun} {k : Int}
    {e₁ : Expr} {c : Const} {ty : BuiltinType} (base : Nat) (hb : binaryInteger b)
    (hknown : knownInteger 64 Γ e₁ = true)
    (hop : ∀ x, evalBuiltin b [.VCon (.Integer k), .VCon (.Integer x)] = some (.VCon c)) :
    FactRel G PF Γ (.App (.App (.Builtin b) e₁) (intLit k)) (retainEvaluation base Γ e₁ (.Lit (c, ty))) := by
  intro env t hG hd hfresh hk hsc hlow
  simp only [freshIn, Bool.and_eq_true] at hfresh
  obtain ⟨t₁, t₂, ht₁, ht₂, rfl⟩ := lowerTotalExpr_binary hlow
  rw [lowerTotalExpr_intLit] at ht₂; cases ht₂
  unfold retainEvaluation
  split
  · rename_i htotal
    refine ⟨.Constant (c, ty), lowerTotalExpr_lit env c ty, ?_⟩
    intro ρ π henv hlen hπ hF
    obtain ⟨v, hv⟩ := totalWithFacts_sound PF_hP 64 Γ e₁ htotal hF hd hfresh.1.2
      (wellSized_of_wellFormed henv) ht₁
    obtain ⟨x, rfl⟩ := knownInteger_sound PF_produces 64 Γ e₁ hknown hF hd ht₁ hv
    refine obsRefines_of_reaches ?_ (halts_on_stack (halts_constant_of _ _) _) (obsRefines_refl _)
    exact reaches_trans (reaches_of_steps 4 (bin_head b π ρ t₁ _))
      (reaches_trans (halts_on_stack hv _) (right_literal_finish hb (hop x)))
  · refine ⟨_, lowerTotalExpr_retain_let ht₁, ?_⟩
    intro ρ π henv hlen hπ hF
    refine obsRefines_of_reaches (reaches_of_steps 4 (bin_head b π ρ t₁ _)) (reaches_of_steps 3 rfl) ?_
    refine obsRefines_of_continuation ?_
    intro v hv
    obtain ⟨x, rfl⟩ := knownInteger_sound PF_produces 64 Γ e₁ hknown hF hd ht₁ hv
    exact obsRefines_of_reaches (right_literal_finish hb (hop x)) (reaches_of_steps 2 rfl)
      (obsRefines_refl _)

/-! ## The identity rewrite -/

theorem isIntegerLiteral_eq {e : Expr} {k : Int} (h : isIntegerLiteral e k = true) : e = intLit k := by
  unfold isIntegerLiteral at h
  split at h
  · rename_i actual
    have : actual = k := by simpa using h
    subst this; rfl
  · cases h

theorem integerIdentity_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {base : Nat} {x y : Expr}
    (h : integerIdentity base Γ x = some y) : FactRel G PF Γ x y := by
  unfold integerIdentity at h
  split at h
  · rename_i b first second
    split at h
    · cases h
    · rename_i hkn
      simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hkn
      obtain ⟨hk₁, hk₂⟩ := hkn
      split at h
      · -- addition
        split at h
        · rename_i hl; cases h; rw [isIntegerLiteral_eq hl]
          exact left_neutral_factRel rfl hk₂ eval_add_zero_left
        · split at h
          · rename_i _ hl; cases h; rw [isIntegerLiteral_eq hl]
            exact right_neutral_factRel rfl hk₁ eval_add_zero_right
          · cases h
      · -- subtraction
        split at h
        · rename_i hl; cases h; rw [isIntegerLiteral_eq hl]
          exact right_neutral_factRel rfl hk₁ eval_sub_zero_right
        · split at h
          · rename_i l r
            split at h
            · rename_i hlr; cases h
              exact self_factRel rfl hlr hk₁ eval_sub_self
            · cases h
          · cases h
      · -- multiplication
        split at h
        · rename_i hl; cases h; rw [isIntegerLiteral_eq hl]
          exact left_neutral_factRel rfl hk₂ eval_mul_one_left
        · split at h
          · rename_i _ hl; cases h; rw [isIntegerLiteral_eq hl]
            exact right_neutral_factRel rfl hk₁ eval_mul_one_right
          · split at h
            · rename_i _ _ hl; cases h; rw [isIntegerLiteral_eq hl]
              exact left_absorbing_factRel base rfl hk₂ eval_mul_zero_left
            · split at h
              · rename_i _ _ _ hl; cases h; rw [isIntegerLiteral_eq hl]
                exact right_absorbing_factRel base rfl hk₁ eval_mul_zero_right
              · cases h
      · -- floor division
        split at h
        · rename_i hl; cases h; rw [isIntegerLiteral_eq hl]
          exact right_neutral_factRel rfl hk₁ eval_div_one
        · cases h
      · -- truncated division
        split at h
        · rename_i hl; cases h; rw [isIntegerLiteral_eq hl]
          exact right_neutral_factRel rfl hk₁ eval_quot_one
        · cases h
      · -- remainder
        split at h
        · rename_i hl; cases h; rw [isIntegerLiteral_eq hl]
          exact right_absorbing_factRel base rfl hk₁ eval_rem_one
        · cases h
      · -- modulus
        split at h
        · rename_i hl; cases h; rw [isIntegerLiteral_eq hl]
          exact right_absorbing_factRel base rfl hk₁ eval_mod_one
        · cases h
      · split at h
        · rename_i l r
          split at h
          · rename_i hlr; cases h
            exact self_factRel rfl hlr hk₁ (fun x => by rw [eval_equals_self]; rfl)
          · cases h
        · cases h
      · split at h
        · rename_i l r
          split at h
          · rename_i hlr; cases h
            exact self_factRel rfl hlr hk₁ (fun x => by rw [eval_lessThan_self]; rfl)
          · cases h
        · cases h
      · split at h
        · rename_i l r
          split at h
          · rename_i hlr; cases h
            exact self_factRel rfl hlr hk₁ (fun x => by rw [eval_lessThanEquals_self]; rfl)
          · cases h
        · cases h
      · cases h
  · cases h

/-! ## Freshness of the identity rewrite -/

theorem retainEvaluation_fresh {base : Nat} {Γ : List (VarId × Expr)} {e : Expr} {c : Const}
    {ty : BuiltinType} {env : List VarId} (hG : ∀ y ∈ env, GenSafe base y) (h : freshIn env e = true) :
    freshIn env (retainEvaluation base Γ e (.Lit (c, ty))) = true := by
  unfold retainEvaluation
  split
  · simp [freshIn]
  · rw [freshIn_let_single]
    simp only [Bool.and_eq_true]
    refine ⟨⟨h, ?_⟩, by simp [freshIn]⟩
    rw [lookup_none_of_not_G hG (not_genSafe (Nat.le_max_left _ _) rfl)]; rfl

theorem integerIdentity_fresh {Γ : List (VarId × Expr)} {base : Nat} {x y : Expr} {env : List VarId}
    (hG : ∀ y ∈ env, GenSafe base y) (hx : freshIn env x = true)
    (h : integerIdentity base Γ x = some y) : freshIn env y = true := by
  unfold integerIdentity at h
  split at h
  · rename_i b first second
    simp only [freshIn, Bool.and_eq_true] at hx
    obtain ⟨⟨_, hf₁⟩, hf₂⟩ := hx
    have hlit : ∀ c, freshIn env (.Lit c) = true := fun _ => by simp [freshIn]
    split at h
    · cases h
    · split at h
      · split at h
        · cases h; exact hf₂
        · split at h
          · cases h; exact hf₁
          · cases h
      · split at h
        · cases h; exact hf₁
        · split at h
          · split at h
            · cases h; exact hlit _
            · cases h
          · cases h
      · split at h
        · cases h; exact hf₂
        · split at h
          · cases h; exact hf₁
          · split at h
            · cases h; exact retainEvaluation_fresh hG hf₂
            · split at h
              · cases h; exact retainEvaluation_fresh hG hf₁
              · cases h
      · split at h
        · cases h; exact hf₁
        · cases h
      · split at h
        · cases h; exact hf₁
        · cases h
      · split at h
        · cases h; exact retainEvaluation_fresh hG hf₁
        · cases h
      · split at h
        · cases h; exact retainEvaluation_fresh hG hf₁
        · cases h
      · split at h
        · split at h
          · cases h; exact hlit _
          · cases h
        · cases h
      · split at h
        · split at h
          · cases h; exact hlit _
          · cases h
        · cases h
      · split at h
        · split at h
          · cases h; exact hlit _
          · cases h
        · cases h
      · cases h
  · cases h

end Moist.Verified.ShapeFacts
