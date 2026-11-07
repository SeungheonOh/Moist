import Moist.Verified.ShapeFacts.Values

/-! # Soundness of the shape analyses

Under realized facts, an expression accepted by `knownList`,
`constructorPair`, `knownInteger` or `knownBooleanLocal` returns, whenever it
halts, a value of the corresponding shape. These are post-success facts:
nothing is claimed about expressions that fail or diverge.
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence

variable {P : List VarId → CekEnv → Expr → CekValue → Prop}

theorem lowerTotalExprList_mem {env : List VarId} :
    ∀ {alts : List Expr} {talts : List Term}, MIR.lowerTotalExprList env alts = some talts →
      ∀ alt ∈ talts, ∃ a ∈ alts, lowerTotalExpr env a = some alt
  | [], talts, h, alt, hmem => by
    rw [MIR.lowerTotalExprList_nil] at h; cases h; cases hmem
  | a :: as, talts, h, alt, hmem => by
    rw [MIR.lowerTotalExprList_cons] at h
    cases ha : lowerTotalExpr env a with
    | none => rw [ha] at h; cases h
    | some ta =>
      cases has : MIR.lowerTotalExprList env as with
      | none => rw [ha, has] at h; cases h
      | some tas =>
        rw [ha, has] at h; cases h
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact ⟨a, .head _, ha⟩
        · obtain ⟨b, hb, hlow⟩ := lowerTotalExprList_mem has alt hmem
          exact ⟨b, .tail _ hb, hlow⟩

private theorem alternative_result {ρ : CekEnv} {alt : Term} {fields : List CekValue} {v : CekValue}
    (Q : CekValue → Prop) (halt : ∀ w, Halts ρ alt w → ∃ c, w = .VCon c ∧ Q (.VCon c))
    (h : Reaches (.compute (fields.map Frame.applyArg ++ []) ρ alt) (.halt v)) : Q v := by
  rcases sequence (.inr ⟨v, rfl⟩) h with ⟨_, impossible⟩ | ⟨w, hw, rest⟩
  · cases impossible
  · obtain ⟨c, rfl, hq⟩ := halt w hw
    cases fields with
    | nil =>
      have r := reaches_halt_of_step (by simp) rest
      obtain ⟨n, hn⟩ := r
      simp only [List.map_nil, List.nil_append, step] at hn
      rw [Terminal.steps_fixed (.inr ⟨_, rfl⟩)] at hn
      cases hn; exact hq
    | cons f fs =>
      have r := reaches_halt_of_step (by simp) rest
      simp only [List.map_cons, List.cons_append, step] at r
      exact absurd r (fun he => halt_not_error he ⟨0, rfl⟩)

/-- A case whose alternatives all return constants of some shape returns a
    constant of that shape. -/
theorem case_result {ρ : CekEnv} {s : Term} {talts : List Term} {v : CekValue}
    (Q : CekValue → Prop) (h : Halts ρ (.Case s talts) v)
    (halt : ∀ alt ∈ talts, ∀ w, Halts ρ alt w → ∃ c, w = .VCon c ∧ Q (.VCon c)) : Q v := by
  obtain ⟨w, _, rest⟩ := halts_case h
  have r := reaches_halt_of_step (by simp) rest
  cases w with
  | VConstr tag fields =>
    simp only [step] at r
    cases hget : talts[tag]? with
    | none => rw [hget] at r; exact absurd r (fun he => halt_not_error he ⟨0, rfl⟩)
    | some alt =>
      rw [hget] at r
      exact alternative_result Q (halt alt (List.mem_of_getElem? hget)) r
  | VCon c =>
    simp only [step] at r
    cases hc : constToTagAndFields c with
    | none => rw [hc] at r; exact absurd r (fun he => halt_not_error he ⟨0, rfl⟩)
    | some triple =>
      obtain ⟨tag, numCtors, fields⟩ := triple
      rw [hc] at r
      simp only at r
      split at r
      · exact absurd r (fun he => halt_not_error he ⟨0, rfl⟩)
      · cases hget : talts[tag]? with
        | none => rw [hget] at r; exact absurd r (fun he => halt_not_error he ⟨0, rfl⟩)
        | some alt =>
          rw [hget] at r
          exact alternative_result Q (halt alt (List.mem_of_getElem? hget)) r
  | VLam _ _ | VDelay _ _ | VBuiltin _ _ _ =>
    simp only [step] at r; exact absurd r (fun he => halt_not_error he ⟨0, rfl⟩)

theorem protocol_builtin (b : BuiltinFun) :
    builtinProtocolAfterSuccess (.Builtin b) = some (b, expectedArgs b) := rfl

theorem constructorPair_sound (hP : ∀ env ρ rhs v, P env ρ rhs v → Produces env ρ rhs v) :
    ∀ (n : Nat) (Γ : List (VarId × Expr)) (e : Expr) {env : List VarId} {ρ : CekEnv}
      {t : Term} {v : CekValue},
      constructorPair n Γ e = true → FactsHold P Γ env ρ → EnvDistinct env →
      lowerTotalExpr env e = some t → Halts ρ t v → PairValue v := by
  intro n
  induction n with
  | zero => intro Γ e env ρ t v h; simp [constructorPair] at h
  | succ n ih =>
    intro Γ e env ρ t v h hfacts hd hlow hv
    cases e with
    | Var x =>
      simp only [constructorPair] at h
      cases hf : Γ.find? (fun entry => entry.1 == x) with
      | none => rw [hf] at h; cases h
      | some entry =>
        rw [hf] at h
        obtain ⟨k, _, hp, hfacts', hd'⟩ := fact_of_var hfacts hd hf hlow hv
        obtain ⟨t', ht', hv'⟩ := hP _ _ _ _ hp
        exact ih Γ entry.2 (by simpa using h) hfacts' hd' ht' hv'
    | App f a =>
      simp only [constructorPair] at h
      split at h
      · rename_i hhead
        obtain ⟨tf, ta, htf, _, rfl⟩ := lowerTotalExpr_app_some hlow
        obtain ⟨wf, wa, hwf, _, rest⟩ := halts_apply hv
        have hstate := resolveHead_protocol hP n Γ f (by rw [hhead]; rfl) hfacts hd htf hwf
        obtain ⟨args, hlen, heval⟩ := saturated_apply hstate rest
        exact unConstrData_result hlen heval
      · cases h
    | _ => simp [constructorPair] at h

theorem knownList_sound (hP : ∀ env ρ rhs v, P env ρ rhs v → Produces env ρ rhs v) :
    ∀ (n : Nat) (Γ : List (VarId × Expr)) (e : Expr) {env : List VarId} {ρ : CekEnv}
      {t : Term} {v : CekValue},
      knownList n Γ e = true → FactsHold P Γ env ρ → EnvDistinct env →
      lowerTotalExpr env e = some t → Halts ρ t v → ListValue v := by
  intro n
  induction n with
  | zero => intro Γ e env ρ t v h; simp [knownList] at h
  | succ n ih =>
    intro Γ e env ρ t v h hfacts hd hlow hv
    cases e with
    | Var x =>
      simp only [knownList] at h
      cases hf : Γ.find? (fun entry => entry.1 == x) with
      | none => rw [hf] at h; cases h
      | some entry =>
        rw [hf] at h
        obtain ⟨k, _, hp, hfacts', hd'⟩ := fact_of_var hfacts hd hf hlow hv
        obtain ⟨t', ht', hv'⟩ := hP _ _ _ _ hp
        exact ih Γ entry.2 (by simpa using h) hfacts' hd' ht' hv'
    | Lit lit =>
      obtain ⟨c, ty⟩ := lit
      rw [lowerTotalExpr_lit] at hlow; cases hlow
      rw [halts_constant hv]
      exact ListShape.knownList_literal (n + 1) Γ (c, ty) h
    | App f a =>
      simp only [knownList] at h
      obtain ⟨tf, ta, htf, hta, rfl⟩ := lowerTotalExpr_app_some hlow
      obtain ⟨wf, wa, hwf, hwa, rest⟩ := halts_apply hv
      split at h
      · rename_i hhead
        have hstate := resolveHead_protocol hP n Γ f (b := .UnListData) (by rw [hhead]; rfl)
          hfacts hd htf hwf
        obtain ⟨args, hlen, heval⟩ := saturated_apply hstate rest
        exact unListData_result hlen heval
      · rename_i hhead
        have hstate := resolveHead_protocol hP n Γ f (b := .TailList) (by rw [hhead]; rfl)
          hfacts hd htf hwf
        obtain ⟨args, hlen, heval⟩ := saturated_apply hstate rest
        exact tailList_result hlen heval
      · rename_i hhead
        have hstate := resolveHead_protocol hP n Γ f (b := .SndPair) (by rw [hhead]; rfl)
          hfacts hd htf hwf
        obtain ⟨args, hlen, heval⟩ := saturated_apply hstate rest
        have hpair := constructorPair_sound hP n Γ a h hfacts hd hta hwa
        have h1 : valueArity (expectedArgs .SndPair) = 1 := rfl
        rw [h1] at hlen
        have hargs : args = [] := by
          cases args with
          | nil => rfl
          | cons _ _ => simp at hlen
        subst hargs
        exact sndPair_result hlen (by simpa using hpair) heval
      · cases h
    | _ => simp [knownList] at h

theorem knownInteger_sound (hP : ∀ env ρ rhs v, P env ρ rhs v → Produces env ρ rhs v) :
    ∀ (n : Nat) (Γ : List (VarId × Expr)) (e : Expr) {env : List VarId} {ρ : CekEnv}
      {t : Term} {v : CekValue},
      knownInteger n Γ e = true → FactsHold P Γ env ρ → EnvDistinct env →
      lowerTotalExpr env e = some t → Halts ρ t v → IntegerValue v := by
  intro n
  induction n with
  | zero => intro Γ e env ρ t v h; simp [knownInteger] at h
  | succ n ih =>
    intro Γ e env ρ t v h hfacts hd hlow hv
    cases e with
    | Var x =>
      simp only [knownInteger] at h
      cases hf : Γ.find? (fun entry => entry.1 == x) with
      | none => rw [hf] at h; cases h
      | some entry =>
        rw [hf] at h
        obtain ⟨k, _, hp, hfacts', hd'⟩ := fact_of_var hfacts hd hf hlow hv
        obtain ⟨t', ht', hv'⟩ := hP _ _ _ _ hp
        exact ih Γ entry.2 (by simpa using h) hfacts' hd' ht' hv'
    | Lit lit =>
      obtain ⟨c, ty⟩ := lit
      rw [lowerTotalExpr_lit] at hlow; cases hlow
      rw [halts_constant hv]
      cases c <;> simp [knownInteger] at h
      exact ⟨_, rfl⟩
    | App f a =>
      simp only [knownInteger] at h
      obtain ⟨tf, ta, htf, hta, rfl⟩ := lowerTotalExpr_app_some hlow
      obtain ⟨wf, wa, hwf, hwa, rest⟩ := halts_apply hv
      split at h
      · rename_i hhead
        have hstate := resolveHead_protocol hP n Γ f (b := .FstPair) (by rw [hhead]; rfl)
          hfacts hd htf hwf
        obtain ⟨args, hlen, heval⟩ := saturated_apply hstate rest
        have hpair := constructorPair_sound hP n Γ a h hfacts hd hta hwa
        have h1 : valueArity (expectedArgs .FstPair) = 1 := rfl
        rw [h1] at hlen
        have hargs : args = [] := by
          cases args with
          | nil => rfl
          | cons _ _ => simp at hlen
        subst hargs
        exact fstPair_result hlen (by simpa using hpair) heval
      · cases hp : builtinProtocolAfterSuccess (resolveHead n Γ f) with
        | none => rw [hp] at h; cases h
        | some pr =>
          obtain ⟨b, rem⟩ := pr
          rw [hp] at h
          simp only [Option.any_some, Bool.and_eq_true] at h
          obtain ⟨⟨hhead, hfinal⟩, hb⟩ := h
          have hrem : rem = .one .argV := by
            cases rem with
            | one k =>
            simp only [ExpectedArgs.head] at hhead
            cases k
            · rfl
            · exact absurd hhead (by decide)
            | more _ _ => simp [ExpectedArgs.isFinal] at hfinal
          subst hrem
          have hstate := resolveHead_protocol hP n Γ f hp hfacts hd htf hwf
          obtain ⟨args, hlen, heval⟩ := saturated_apply hstate rest
          refine integerBuiltin_result ?_ hlen heval
          cases b <;> simp_all [integerBuiltin]
    | _ => simp [knownInteger] at h

theorem knownBooleanLocal_sound (hP : ∀ env ρ rhs v, P env ρ rhs v → Produces env ρ rhs v) :
    ∀ (n : Nat) (Γ : List (VarId × Expr)) (e : Expr) {env : List VarId} {ρ : CekEnv}
      {t : Term} {v : CekValue},
      knownBooleanLocal n Γ e = true → FactsHold P Γ env ρ → EnvDistinct env →
      lowerTotalExpr env e = some t → Halts ρ t v → BoolValue v := by
  intro n
  induction n with
  | zero => intro Γ e env ρ t v h; simp [knownBooleanLocal] at h
  | succ n ih =>
    intro Γ e env ρ t v h hfacts hd hlow hv
    cases e with
    | Var x =>
      simp only [knownBooleanLocal] at h
      cases hf : Γ.find? (fun entry => entry.1 == x) with
      | none => rw [hf] at h; cases h
      | some entry =>
        rw [hf] at h
        obtain ⟨k, _, hp, hfacts', hd'⟩ := fact_of_var hfacts hd hf hlow hv
        obtain ⟨t', ht', hv'⟩ := hP _ _ _ _ hp
        exact ih Γ entry.2 (by simpa using h) hfacts' hd' ht' hv'
    | Lit lit =>
      obtain ⟨c, ty⟩ := lit
      rw [lowerTotalExpr_lit] at hlow; cases hlow
      rw [halts_constant hv]
      cases c <;> simp [knownBooleanLocal] at h
      exact ⟨_, rfl⟩
    | App f a =>
      simp only [knownBooleanLocal] at h
      obtain ⟨tf, ta, htf, hta, rfl⟩ := lowerTotalExpr_app_some hlow
      obtain ⟨wf, wa, hwf, hwa, rest⟩ := halts_apply hv
      cases hp : builtinProtocolAfterSuccess (resolveHead n Γ f) with
      | none => rw [hp] at h; cases h
      | some pr =>
        obtain ⟨b, rem⟩ := pr
        rw [hp] at h
        simp only [Option.any_some, Bool.and_eq_true] at h
        obtain ⟨⟨hhead, hfinal⟩, hb⟩ := h
        have hrem : rem = .one .argV := by
          cases rem with
          | one k =>
            simp only [ExpectedArgs.head] at hhead
            cases k
            · rfl
            · exact absurd hhead (by decide)
          | more _ _ => simp [ExpectedArgs.isFinal] at hfinal
        subst hrem
        have hstate := resolveHead_protocol hP n Γ f hp hfacts hd htf hwf
        obtain ⟨args, hlen, heval⟩ := saturated_apply hstate rest
        exact booleanBuiltin_result hb hlen heval
    | Case s alts =>
      simp only [knownBooleanLocal, Bool.and_eq_true, List.all_eq_true] at h
      obtain ⟨_, hall⟩ := h
      obtain ⟨ts, talts, _, htalts, rfl⟩ := lowerTotalExpr_case_some hlow
      refine case_result BoolValue hv ?_
      intro alt hmem w hw
      obtain ⟨a, ha, hlowa⟩ := lowerTotalExprList_mem htalts alt hmem
      obtain ⟨c, rfl⟩ := ih Γ a (hall a ha) hfacts hd hlowa hw
      exact ⟨_, rfl, ⟨c, rfl⟩⟩
    | _ => simp [knownBooleanLocal] at h

end Moist.Verified.ShapeFacts
