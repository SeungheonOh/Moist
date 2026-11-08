import Moist.Verified.ShapeFacts.Delays
import Moist.Verified.ShapeFacts.Known
import Moist.Verified.Purity

variable [sv : Moist.CEK.SemVariant]

/-! # Totality under facts

`totalWithFacts` accepts pure expressions, integer arithmetic on known
integers, and pair projections of constructor pairs. Such expressions return
in every environment where the facts hold.
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence

variable {P : List VarId → CekEnv → Expr → CekValue → Prop}

theorem halts_apply_intro {ρ : CekEnv} {tf ta : Term} {wf wa v : CekValue} (hf : Halts ρ tf wf)
    (ha : Halts ρ ta wa) (h : Reaches (.ret [.funV wf] wa) (.halt v)) : Halts ρ (.Apply tf ta) v :=
  reaches_trans (reaches_of_steps 1 rfl) (reaches_trans (halts_on_stack hf _)
    (reaches_trans (reaches_of_steps 1 rfl) (reaches_trans (halts_on_stack ha _) h)))

theorem builtin_partial_reaches {b : BuiltinFun} {args : List CekValue} {ea rest : ExpectedArgs}
    {wa : CekValue} (hhead : ea.head = .argV) (htail : ea.tail = some rest) :
    Reaches (.ret [.funV (.VBuiltin b args ea)] wa) (.halt (.VBuiltin b (wa :: args) rest)) := by
  refine ⟨2, ?_⟩
  show step (step (.ret [.funV (.VBuiltin b args ea)] wa)) = _
  simp only [step, hhead, htail]

theorem builtin_final_reaches {b : BuiltinFun} {args : List CekValue} {ea : ExpectedArgs}
    {wa r : CekValue} (hhead : ea.head = .argV) (htail : ea.tail = none)
    (h : evalBuiltin b (wa :: args) = some r) :
    Reaches (.ret [.funV (.VBuiltin b args ea)] wa) (.halt r) := by
  refine ⟨2, ?_⟩
  show step (step (.ret [.funV (.VBuiltin b args ea)] wa)) = _
  simp only [step, hhead, htail, h]

def integerOperation : BuiltinFun → Bool
  | .AddInteger | .SubtractInteger | .MultiplyInteger | .EqualsInteger
  | .LessThanInteger | .LessThanEqualsInteger => true
  | _ => false

omit sv in
theorem integerOperation_args {b : BuiltinFun} (h : integerOperation b = true) :
    expectedArgs b = .more .argV (.one .argV) := by
  cases b <;> simp [integerOperation] at h <;> rfl

/-- Integer operations succeed on integers below `2^64` in magnitude under every variant;
    `equalsInteger` succeeds on every pair of integers. -/
theorem integerOperation_eval {b : BuiltinFun} (h : integerOperation b = true) (x y : Int)
    (hbound : b = .EqualsInteger ∨ (x.natAbs < 2 ^ 64 ∧ y.natAbs < 2 ^ 64)) :
    ∃ r, evalBuiltin b [.VCon (.Integer y), .VCon (.Integer x)] = some r := by
  rw [show [CekValue.VCon (.Integer y), .VCon (.Integer x)] =
    [Const.Integer y, .Integer x].map CekValue.VCon from rfl]
  cases b <;> simp [integerOperation] at h
  all_goals first
    | exact ⟨_, rfl⟩
    | (obtain ⟨hx, hy⟩ := hbound.resolve_left (by decide)
       have ox := cIntegerOk_of_natAbs_lt sv x hx
       have oy := cIntegerOk_of_natAbs_lt sv y hy
       rw [evalBuiltin_consts _ _ rfl]
       have hk : ∀ (a : Const), (if (cIntegerOk sv x && cIntegerOk sv y) = true then some a
           else none) = some a := by
         intro a; rw [ox, oy]; rfl
       exact ⟨_, congrArg (Option.map CekValue.VCon) (hk _)⟩)

/-- A head resolved to a builtin applied to a known integer returns a builtin
    state holding that integer. -/
theorem partial_integer_head
    (hP : ∀ env ρ rhs v, P env ρ rhs v → Produces env ρ rhs v ∧ freshIn env rhs = true)
    {n : Nat} {Γ : List (VarId × Expr)} {f first : Expr} {b : BuiltinFun} {env : List VarId}
    {ρ : CekEnv} {tf : Term} {wf : CekValue}
    (hres : resolveHead n Γ f = .App (.Builtin b) first) (hb : integerOperation b = true)
    (hint : knownInteger 64 Γ first = true)
    (hfacts : FactsHold P Γ env ρ) (hd : EnvDistinct env) (hfresh : freshIn env f = true)
    (hlow : lowerTotalExpr env f = some tf) (hf : Halts ρ tf wf) :
    ∃ wa, wf = .VBuiltin b [wa] (.one .argV) ∧ IntegerValue wa ∧
      (boundedInteger 64 Γ first = true → ∃ i, wa = .VCon (.Integer i) ∧ i.natAbs < 2 ^ 64) := by
  obtain ⟨k, m, e₁, t₁, ta, w₁, wa, _, _, hres₁, ht₁, hta, hw₁, hwa, happ, _, _, hfacts', hd'⟩ :=
    resolveHead_app_unfold hP n Γ f hres hfacts hd hfresh hlow hf
  have hProd := hfacts'.mono (fun _ _ _ _ h => (hP _ _ _ _ h).1)
  have hb₁ := resolveHead_forced_halts m Γ e₁ hres₁ (b := b) (rem := expectedArgs b) rfl hProd hd' ht₁
  have := halts_unique hw₁ hb₁
  subst this
  rw [integerOperation_args hb] at happ
  refine ⟨wa, apply_partial rfl happ, ?_, fun hbounded => ?_⟩
  · exact knownInteger_sound (fun _ _ _ _ h => (hP _ _ _ _ h).1) 64 Γ first hint hfacts' hd' hta hwa
  · exact boundedInteger_sound (fun _ _ _ _ h => (hP _ _ _ _ h).1) 64 Γ first hbounded hfacts' hd'
      hta hwa

theorem totalWithFacts_sound
    (hP : ∀ env ρ rhs v, P env ρ rhs v → Produces env ρ rhs v ∧ freshIn env rhs = true) :
    ∀ (fuel : Nat) (Γ : List (VarId × Expr)) (e : Expr) {env : List VarId} {ρ : CekEnv} {t : Term},
      totalWithFacts fuel Γ e = true → FactsHold P Γ env ρ → EnvDistinct env →
      freshIn env e = true → Semantics.WellSizedEnv env.length ρ →
      lowerTotalExpr env e = some t → ∃ v, Halts ρ t v := by
  have hProd : ∀ env ρ rhs v, P env ρ rhs v → Produces env ρ rhs v := fun _ _ _ _ h => (hP _ _ _ _ h).1
  have pure : ∀ (e : Expr) {env : List VarId} {ρ : CekEnv} {t : Term}, isPure e = true →
      Semantics.WellSizedEnv env.length ρ → lowerTotalExpr env e = some t → ∃ v, Halts ρ t v :=
    fun e env ρ t hp hw hl =>
      Purity.isPure_halts (expandFix e) t env ρ (Purity.isPure_expandFix e hp) hl hw
  intro fuel
  induction fuel with
  | zero => intro Γ e env ρ t h _ _ _ hw hl; exact pure e (by simpa [totalWithFacts] using h) hw hl
  | succ fuel ih =>
    intro Γ e env ρ t h hfacts hd hfresh hw hlow
    simp only [totalWithFacts, Bool.or_eq_true] at h
    rcases h with h | h
    · exact pure e h hw hlow
    · cases e with
      | App f a =>
        simp only at h
        obtain ⟨tf, ta, htf, hta, rfl⟩ := lowerTotalExpr_app_some hlow
        simp only [freshIn, Bool.and_eq_true] at hfresh
        split at h
        · rename_i b first hres
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨⟨⟨⟨hb, hif⟩, hia⟩, hbounded⟩, htf'⟩, hta'⟩ := h
          have hb' : integerOperation b = true := by
            revert hb; cases b <;> simp [integerOperation]
          -- the head returns
          obtain ⟨wf, hwf⟩ : ∃ wf, Halts ρ tf wf := by
            cases f with
            | Var x =>
              obtain ⟨i, hi, rfl⟩ := lowerTotalExpr_var_some htf
              obtain ⟨w, hlk⟩ := hw (i + 1) (by omega) (by
                have := envLookupT_bound env x i hi; omega)
              exact ⟨w, halts_var_of_lookup hlk⟩
            | App g first' =>
              rw [show (64 : Nat) = 63 + 1 from rfl, resolveHead_app] at hres
              simp only [Expr.App.injEq] at hres
              obtain ⟨hg, rfl⟩ := hres
              obtain ⟨tg, tfirst, htg, htfirst, rfl⟩ := lowerTotalExpr_app_some htf
              simp only [freshIn, Bool.and_eq_true] at hfresh
              have hgb := resolveHead_forced_halts 63 Γ g hg (b := b) (rem := expectedArgs b) rfl
                (hfacts.mono hProd) hd htg
              obtain ⟨wfirst, hwfirst⟩ := ih Γ _ htf' hfacts hd hfresh.1.2 hw htfirst
              have hpr : Reaches (.ret [.funV (.VBuiltin b [] (expectedArgs b))] wfirst)
                  (.halt (.VBuiltin b [wfirst] (.one .argV))) := by
                rw [integerOperation_args hb']
                exact builtin_partial_reaches rfl rfl
              exact ⟨_, halts_apply_intro hgb hwfirst hpr⟩
            | Force _ => rw [show (64 : Nat) = 63 + 1 from rfl, resolveHead_force] at hres; cases hres
            | _ => simp [resolveHead] at hres
          obtain ⟨wa, rfl, hwa, hwaBound⟩ :=
            partial_integer_head hP hres hb' hif hfacts hd hfresh.1 htf hwf
          obtain ⟨va, hva⟩ := ih Γ a hta' hfacts hd hfresh.2 hw hta
          obtain ⟨x, rfl⟩ := hwa
          obtain ⟨y, rfl⟩ := knownInteger_sound hProd 64 Γ a hia hfacts hd hta hva
          have hbound : b = .EqualsInteger ∨ (x.natAbs < 2 ^ 64 ∧ y.natAbs < 2 ^ 64) := by
            simp only [Bool.or_eq_true, Bool.and_eq_true] at hbounded
            rcases hbounded with heq | ⟨hbf, hba⟩
            · exact .inl (by revert heq; cases b <;> decide)
            · obtain ⟨y', hy', hyb⟩ := boundedInteger_sound hProd 64 Γ a hba hfacts hd hta hva
              cases hy'
              obtain ⟨x', hx', hxb⟩ := hwaBound hbf
              cases hx'
              exact .inr ⟨hxb, hyb⟩
          obtain ⟨r, hr⟩ := integerOperation_eval hb' x y hbound
          exact ⟨r, halts_apply_intro hwf hva (builtin_final_reaches rfl rfl hr)⟩
        · rename_i b hres
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hb, hpair⟩, hta'⟩ := h
          have hb' : b = .FstPair ∨ b = .SndPair := by
            cases b <;> first | exact .inl rfl | exact .inr rfl |
              (simp only [Bool.or_eq_true] at hb; rcases hb with hb | hb <;> cases hb)
          obtain ⟨va, hva⟩ := ih Γ a hta' hfacts hd hfresh.2 hw hta
          obtain ⟨i, fields, rfl⟩ := constructorPair_sound hProd 64 Γ a hpair hfacts hd hta hva
          rcases hb' with rfl | rfl
          · have hfb := resolveHead_forced_halts 64 Γ f hres (b := .FstPair) (rem := .one .argV) rfl
              (hfacts.mono hProd) hd htf
            exact ⟨_, halts_apply_intro hfb hva (builtin_final_reaches rfl rfl rfl)⟩
          · have hfb := resolveHead_forced_halts 64 Γ f hres (b := .SndPair) (rem := .one .argV) rfl
              (hfacts.mono hProd) hd htf
            exact ⟨_, halts_apply_intro hfb hva (builtin_final_reaches rfl rfl rfl)⟩
        · cases h
      | _ => simp at h

end Moist.Verified.ShapeFacts
