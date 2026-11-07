import Moist.Verified.ShapesSoundness.Choices
import Moist.MIR.Optimize.Advanced.Products

/-! # Known builtin pairs

`knownProduct` resolves an expression to an application of `unConstrData` or
`mkPairData`. Under realized facts, whatever such an expression returns is a
builtin pair constant (`knownProduct_sound`), so native `case` destructures it
into the same components that `fstPair` and `sndPair` return
(`product_components`).
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence

/-- A builtin pair constant. -/
def ProductValue (v : CekValue) : Prop :=
  (∃ a b, v = .VCon (.Pair (a, b))) ∨ (∃ a b, v = .VCon (.PairData (a, b)))

theorem mkPairData_const {c₁ c₂ r : Const} (h : evalBuiltinConst .MkPairData [c₁, c₂] = some r) :
    ∃ a b, r = .PairData (a, b) := by
  cases c₁ <;> cases c₂ <;> (try cases h) <;> exact ⟨_, _, rfl⟩

theorem mkPairData_result {vs : List CekValue} {v : CekValue} (hlen : vs.length = 2)
    (h : evalBuiltin .MkPairData vs = some v) : ProductValue v := by
  match vs, hlen with
  | [w₁, w₂], _ =>
    simp only [evalBuiltin, evalBuiltinPassThrough_none_of_not_passthrough .MkPairData _
      (by simp)] at h
    cases w₁ <;> cases w₂ <;> simp [extractConsts] at h
    rename_i c₁ c₂ _
    cases hc : evalBuiltinConst .MkPairData [c₁, c₂] with
    | none => rw [hc] at h; cases h
    | some r =>
      rw [hc] at h; cases h
      obtain ⟨a, b, rfl⟩ := mkPairData_const hc
      exact .inr ⟨_, _, rfl⟩

/-- Resolved pair producers return pairs. -/
theorem resolveHead_product :
    ∀ (n : Nat) (Γ : List (VarId × Expr)) (e : Expr) {env : List VarId} {ρ : CekEnv} {t : Term}
      {v : CekValue},
      ((∃ a, resolveHead n Γ e = .App (.Builtin .UnConstrData) a) ∨
        (∃ a b, resolveHead n Γ e = .App (.App (.Builtin .MkPairData) a) b)) →
      FactsHold Produces Γ env ρ → EnvDistinct env →
      lowerTotalExpr env e = some t → Halts ρ t v → ProductValue v := by
  have app : ∀ (k : Nat) (Γ : List (VarId × Expr)) (f a : Expr) {env : List VarId} {ρ : CekEnv}
      {t : Term} {v : CekValue},
      (resolveHead k Γ f = .Builtin .UnConstrData ∨ ∃ b, resolveHead k Γ f = .App (.Builtin .MkPairData) b) →
      FactsHold Produces Γ env ρ → EnvDistinct env →
      lowerTotalExpr env (.App f a) = some t → Halts ρ t v → ProductValue v := by
    intro k Γ f a env ρ t v hf hfacts hd hlow hv
    obtain ⟨tf, ta, htf, _, rfl⟩ := lowerTotalExpr_app_some hlow
    obtain ⟨wf, wa, hwf, _, rest⟩ := halts_apply hv
    rcases hf with hf | ⟨b, hf⟩
    · have hstate := resolveHead_protocol produces_hP k Γ f (by rw [hf]; rfl) hfacts hd htf hwf
      obtain ⟨args, hlen, heval⟩ := saturated_apply hstate rest
      obtain ⟨i, fields, rfl⟩ := unConstrData_result hlen heval
      exact .inl ⟨_, _, rfl⟩
    · have hstate := resolveHead_protocol produces_hP k Γ f (by rw [hf]; rfl) hfacts hd htf hwf
      obtain ⟨args, hlen, heval⟩ := saturated_apply hstate rest
      exact mkPairData_result hlen heval
  intro n
  induction n with
  | zero =>
    intro Γ e env ρ t v h hfacts hd hlow hv
    simp only [resolveHead_zero] at h
    rcases h with ⟨a, rfl⟩ | ⟨a, b, rfl⟩
    · exact app 0 Γ _ a (.inl rfl) hfacts hd hlow hv
    · exact app 0 Γ _ b (.inr ⟨a, rfl⟩) hfacts hd hlow hv
  | succ n ih =>
    intro Γ e env ρ t v h hfacts hd hlow hv
    cases e with
    | Var x =>
      simp only [resolveHead_var] at h
      cases hf : Γ.find? (fun entry => entry.1 == x) with
      | none => rw [hf] at h; simp at h
      | some entry =>
        obtain ⟨y, rhs⟩ := entry
        rw [hf] at h
        obtain ⟨k, _, hp, hfacts', hd'⟩ := fact_of_var hfacts hd hf hlow hv
        obtain ⟨t', ht', hv'⟩ := hp
        exact ih Γ rhs h hfacts' hd' ht' hv'
    | App f a =>
      simp only [resolveHead_app] at h
      rcases h with ⟨_, h⟩ | ⟨_, _, h⟩
      · injection h with hf
        exact app n Γ f a (.inl hf) hfacts hd hlow hv
      · injection h with hf
        exact app n Γ f a (.inr ⟨_, hf⟩) hfacts hd hlow hv
    | Force e => simp [resolveHead_force] at h
    | Lit _ | Error | Lam _ _ | Fix _ _ | Delay _ | Constr _ _ | Case _ _ | Let _ _ | Builtin _ =>
      simp [resolveHead] at h

theorem knownProduct_sound {Γ : List (VarId × Expr)} {e : Expr} {env : List VarId} {ρ : CekEnv}
    {t : Term} {v : CekValue} (hknown : knownProduct Γ e = true)
    (hfacts : FactsHold Produces Γ env ρ) (hd : EnvDistinct env)
    (hlow : lowerTotalExpr env e = some t) (hv : Halts ρ t v) : ProductValue v := by
  unfold knownProduct at hknown
  split at hknown
  · rename_i a h
    exact resolveHead_product 64 Γ e (.inl ⟨a, h⟩) hfacts hd hlow hv
  · rename_i a b h
    exact resolveHead_product 64 Γ e (.inr ⟨a, b, h⟩) hfacts hd hlow hv
  · cases hknown

/-! ## Components -/

theorem forced_pair_halts (ρ : CekEnv) {b : BuiltinFun} (hb : b = .FstPair ∨ b = .SndPair) :
    Halts ρ (.Force (.Force (.Builtin b))) (.VBuiltin b [] (.one .argV)) := by
  rcases hb with rfl | rfl
  · exact ⟨6, rfl⟩
  · exact ⟨6, rfl⟩

/-- Native `case` on a pair binds the components returned by the projections. -/
theorem product_components {v : CekValue} (h : ProductValue v) :
    ∃ a b : Const,
      (∀ (π : Stack) (ρ : CekEnv) (body : Term),
        Reaches (.ret (.caseScrutinee [.Lam 0 (.Lam 0 body)] ρ :: π) v)
          (.compute π ((ρ.extend (.VCon a)).extend (.VCon b)) body)) ∧
      evalBuiltin .FstPair [v] = some (.VCon a) ∧ evalBuiltin .SndPair [v] = some (.VCon b) := by
  rcases h with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩
  · exact ⟨a, b, fun π ρ body => ⟨5, by simp [steps, step, constToTagAndFields, CekEnv.extend]⟩,
      rfl, rfl⟩
  · exact ⟨.Data a, .Data b,
      fun π ρ body => ⟨5, by simp [steps, step, constToTagAndFields, CekEnv.extend]⟩, rfl, rfl⟩

end Moist.Verified.ShapeFacts
