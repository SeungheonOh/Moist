import Moist.SMT.Soundness

/-!
# CEK endpoints for flexible UPLC assertion results

These lemmas connect the proof-free assertion result conditions to the actual
CEK transition relation.  Successful evaluation means an active `.ok` outcome;
it is deliberately not encoded as the negation of `errorCond`, because that
would accept symbolic fuel exhaustion.
-/

namespace Moist.SMT.UPLC.Soundness

open Moist.Plutus.Term
open Moist.CEK (CekEnv CekValue)

/-- A true general-success condition contains an active successful outcome. -/
theorem okCond_eval_true_mem {m : SmtSem.Model} {outs : List Outcome}
    (h : SmtSem.evalBoolIs m (okCond outs) true = true) :
    ∃ pc value,
      Outcome.ok pc value ∈ outs ∧ pcHolds m pc = true := by
  obtain ⟨candidate, hcandidate, htrue⟩ :=
    evalBoolIs_any_true (m := m)
      (xs := outs.filterMap fun
        | .ok pc _ => some pc
        | _ => none)
      (by simpa [okCond] using h)
  simp only [List.mem_filterMap] at hcandidate
  rcases hcandidate with ⟨outcome, houtcome, hmapped⟩
  cases outcome with
  | error pc => simp at hmapped
  | timeout pc => simp at hmapped
  | ok pc value =>
      simp at hmapped
      subst candidate
      exact ⟨pc, value, houtcome, by simpa [pcHolds] using htrue⟩

/-- A true success condition proves that the actual CEK machine halts with
some exact decoded value. -/
theorem evalSym_okCond_sound {m : SmtSem.Model} {fuel : Nat}
    {ρ : List SymVal} {env : CekEnv} {term : Term}
    (henv : symEnvToCek? m ρ = some env)
    (hρno : symEnvNoOpaqueForSoundness ρ = true)
    (hno : termNoOpaqueBuiltinsForSoundness term)
    (hcondition : SmtSem.evalBoolIs m
      (okCond (evalSym fuel ρ term)) true = true) :
    ∃ value, CekHaltsValue env term value := by
  obtain ⟨pc, symbolicValue, hmember, hpc⟩ :=
    okCond_eval_true_mem hcondition
  obtain ⟨value, _hdecoded, hcek⟩ :=
    evalSym_activeOk_sound henv hρno hno hmember hpc
  exact ⟨value, hcek⟩

/-- The false-Boolean branch contains an active successful outcome which
decodes to exactly `Bool false`. -/
theorem okBoolFalseCond_eval_true_mem {m : SmtSem.Model}
    {outs : List Outcome}
    (h : SmtSem.evalBoolIs m (okBoolEqCond outs false) true = true) :
    ∃ pc value,
      Outcome.ok pc value ∈ outs ∧
      pcHolds m pc = true ∧
      symValToCek? m value = some (.VCon (.Bool false)) := by
  obtain ⟨candidate, hcandidate, htrue⟩ :=
    evalBoolIs_any_true (m := m)
      (xs := outs.filterMap fun
        | .ok pc value =>
            let boolean := asBool value
            some (SExpr.all
              [pc, boolean.guard, SExpr.not boolean.val])
        | _ => none)
      (by simpa [okBoolEqCond] using h)
  simp only [List.mem_filterMap] at hcandidate
  rcases hcandidate with ⟨outcome, houtcome, hmapped⟩
  cases outcome with
  | error pc => simp at hmapped
  | timeout pc => simp at hmapped
  | ok pc value =>
      simp at hmapped
      subst candidate
      have houter :=
        (Moist.SMT.Semantics.evalBoolIs_and_true m
          (SExpr.and pc (asBool value).guard)
          (SExpr.not (asBool value).val)).mp htrue
      have hinner :=
        (Moist.SMT.Semantics.evalBoolIs_and_true m
          pc (asBool value).guard).mp houter.1
      have hpc : pcHolds m pc = true := by
        simpa [pcHolds] using hinner.1
      have hguard : pcHolds m (asBool value).guard = true := by
        simpa [pcHolds] using hinner.2
      have hfalse : SmtSem.evalBoolIs m
          (asBool value).val false = true :=
        (Moist.SMT.Semantics.evalBoolIs_not_true m
          (asBool value).val).mp houter.2
      exact ⟨pc, value, houtcome, hpc,
        asBool_false_to_cek hguard hfalse⟩

/-- Requiring an exact Boolean proves the identical CEK return value. -/
theorem evalSym_okBoolEqCond_sound {m : SmtSem.Model} {fuel : Nat}
    {ρ : List SymVal} {env : CekEnv} {term : Term} (expected : Bool)
    (henv : symEnvToCek? m ρ = some env)
    (hρno : symEnvNoOpaqueForSoundness ρ = true)
    (hno : termNoOpaqueBuiltinsForSoundness term)
    (hcondition : SmtSem.evalBoolIs m
      (okBoolEqCond (evalSym fuel ρ term) expected) true = true) :
    CekHaltsValue env term (.VCon (.Bool expected)) := by
  cases expected with
  | true =>
      apply evalSym_okBoolTrueCond_sound henv hρno hno
      simpa [okBoolEqCond] using hcondition
  | false =>
      obtain ⟨pc, symbolicValue, hmember, hpc, hdecoded⟩ :=
        okBoolFalseCond_eval_true_mem hcondition
      obtain ⟨value, hvalue, hcek⟩ :=
        evalSym_activeOk_sound henv hρno hno hmember hpc
      rw [hdecoded] at hvalue
      injection hvalue with hvalue
      subst value
      exact hcek

end Moist.SMT.UPLC.Soundness
