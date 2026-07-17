import Moist.Verified.BigStep

/-!
# Error-aware big-step semantics

`BigStep.bigEval` intentionally uses `Option`, so `none` represents both a real
CEK runtime error and exhaustion of the definitional evaluator's fuel.  That is
adequate for its success equivalence, but it is not an adequate public witness
for compiler-generated error assertions.

This module keeps those cases distinct.  `Result.error` means an actual dynamic
failure; `Result.timeout` means only that the structural fuel reached zero.  The
forward simulation below proves that every `Result.error` is finite reachability
of the actual CEK machine's `.error` state.
-/

namespace Moist.Verified.ExactBigStep

open Moist.Plutus.Term (Term Const BuiltinType BuiltinFun)
open Moist.CEK
open Moist.Verified.Equivalence (Reaches)
open Moist.Verified.Equivalence (steps)
open Moist.Verified.BigStep (reaches_refl reaches_trans one_step)

/-- The observable result of a fuelled big-step computation. -/
inductive Result (α : Type) where
  | ok (value : α)
  | error
  | timeout
deriving DecidableEq, Repr

namespace Result

/-- Monadic sequencing that preserves the distinction between error and timeout. -/
def bind (r : Result α) (k : α → Result β) : Result β :=
  match r with
  | .ok value => k value
  | .error => .error
  | .timeout => .timeout

/-- Forget whether absence was a runtime error or a fuel timeout. -/
def toOption : Result α → Option α
  | .ok value => some value
  | .error => none
  | .timeout => none

@[simp] theorem toOption_bind (r : Result α) (k : α → Result β) :
    (r.bind k).toOption = r.toOption.bind (fun value => (k value).toOption) := by
  cases r <;> rfl

@[simp] theorem bind_assoc (r : Result α) (f : α → Result β)
    (g : β → Result γ) :
    (r.bind f).bind g = r.bind (fun value => (f value).bind g) := by
  cases r <;> rfl

/-- State-level meaning used by the forward simulation.  A timeout makes no
claim; successful and failing executions must reach their corresponding CEK
state in finitely many transitions. -/
def ReachesAs (start : State) (finish : α → State) : Result α → Prop
  | .ok value => Reaches start (finish value)
  | .error => Reaches start .error
  | .timeout => True

/-- Prefix a realized result by an already completed CEK execution. -/
theorem ReachesAs.prepend {start middle : State} {finish : α → State}
    {result : Result α} (hprefix : Reaches start middle)
    (suffix : ReachesAs middle finish result) :
    ReachesAs start finish result := by
  cases result with
  | ok value => exact reaches_trans hprefix suffix
  | error => exact reaches_trans hprefix suffix
  | timeout => trivial

/-- Map a successful result while preserving its already-proved CEK behavior. -/
theorem ReachesAs.bind_ok {start : State} {finish : β → State}
    {result : Result α} {f : α → β}
    (h : ReachesAs start (fun value => finish (f value)) result) :
    ReachesAs start finish (result.bind fun value => .ok (f value)) := by
  cases result <;> simp_all [ReachesAs, bind]

end Result

/-- Remove the first transition from a non-reflexive reachability witness. -/
theorem reaches_tail_of_ne {start finish : State}
    (hreach : Reaches start finish) (hne : start ≠ finish) :
    Reaches (step start) finish := by
  obtain ⟨count, hcount⟩ := hreach
  cases count with
  | zero =>
      simp [steps] at hcount
      exact (hne hcount).elim
  | succ count =>
      exact ⟨count, by simpa [steps] using hcount⟩

mutual
  /-- Error-aware evaluation of a UPLC term. -/
  def eval : Nat → CekEnv → Term → Result CekValue
    | 0, _, _ => .timeout
    | _ + 1, ρ, .Var k =>
        match ρ.lookup k with
        | some value => .ok value
        | none => .error
    | _ + 1, _, .Constant (constant, _) => .ok (.VCon constant)
    | _ + 1, _, .Builtin builtin =>
        .ok (.VBuiltin builtin [] (expectedArgs builtin))
    | _ + 1, ρ, .Lam _ body => .ok (.VLam body ρ)
    | _ + 1, ρ, .Delay body => .ok (.VDelay body ρ)
    | fuel + 1, ρ, .Apply function argument =>
        (eval fuel ρ function).bind fun functionValue =>
          (eval fuel ρ argument).bind fun argumentValue =>
            apply fuel functionValue argumentValue
    | fuel + 1, ρ, .Force term =>
        (eval fuel ρ term).bind fun value => force fuel value
    | fuel + 1, ρ, .Constr tag fields =>
        (evalList fuel ρ fields).bind fun values => .ok (.VConstr tag values)
    | fuel + 1, ρ, .Case scrutinee alternatives =>
        (eval fuel ρ scrutinee).bind fun value =>
          match value with
          | .VConstr tag fields =>
              match alternatives[tag]? with
              | some alternative =>
                  (eval fuel ρ alternative).bind fun alternativeValue =>
                    applyList fuel alternativeValue fields
              | none => .error
          | .VCon constant =>
              match constToTagAndFields constant with
              | some (tag, constructorCount, fields) =>
                  if constructorCount > 0 && alternatives.length > constructorCount then
                    .error
                  else
                    match alternatives[tag]? with
                    | some alternative =>
                        (eval fuel ρ alternative).bind fun alternativeValue =>
                          applyList fuel alternativeValue fields
                    | none => .error
              | none => .error
          | _ => .error
    | _ + 1, _, .Error => .error
  termination_by fuel _ term => (fuel, sizeOf term)

  /-- Error-aware application of an already evaluated function. -/
  def apply : Nat → CekValue → CekValue → Result CekValue
    | 0, _, _ => .timeout
    | fuel + 1, .VLam body ρ, argument => eval fuel (ρ.extend argument) body
    | _ + 1, .VBuiltin builtin arguments expected, argument =>
        match expected.head with
        | .argV =>
            match expected.tail with
            | some rest => .ok (.VBuiltin builtin (argument :: arguments) rest)
            | none =>
                match evalBuiltin builtin (argument :: arguments) with
                | some value => .ok value
                | none => .error
        | .argQ => .error
    | _ + 1, _, _ => .error
  termination_by fuel _ _ => (fuel, 0)

  /-- Error-aware forcing of an already evaluated value. -/
  def force : Nat → CekValue → Result CekValue
    | 0, _ => .timeout
    | fuel + 1, .VDelay body ρ => eval fuel ρ body
    | _ + 1, .VBuiltin builtin arguments expected =>
        match expected.head with
        | .argQ =>
            match expected.tail with
            | some rest => .ok (.VBuiltin builtin arguments rest)
            | none =>
                match evalBuiltin builtin arguments with
                | some value => .ok value
                | none => .error
        | .argV => .error
    | _ + 1, _ => .error
  termination_by fuel _ => (fuel, 0)

  /-- Error-aware, left-to-right constructor-field evaluation. -/
  def evalList : Nat → CekEnv → List Term → Result (List CekValue)
    | _, _, [] => .ok []
    | fuel, ρ, term :: terms =>
        (eval fuel ρ term).bind fun value =>
          (evalList fuel ρ terms).bind fun values => .ok (value :: values)
  termination_by fuel _ terms => (fuel, sizeOf terms)

  /-- Error-aware application to a list of values. -/
  def applyList : Nat → CekValue → List CekValue → Result CekValue
    | _, function, [] => .ok function
    | fuel, function, argument :: arguments =>
        (apply fuel function argument).bind fun next =>
          applyList fuel next arguments
  termination_by fuel _ arguments => (fuel, sizeOf arguments)
end

/-! ## Compatibility with successful `BigStep` computations -/

mutual
  theorem eval_ok_of_bigEval : ∀ {fuel : Nat} {ρ : CekEnv} {term : Term}
      {value : CekValue},
      Moist.Verified.BigStep.bigEval fuel ρ term = some value →
        eval fuel ρ term = .ok value
    | 0, _, _, _, h => by simp [Moist.Verified.BigStep.bigEval] at h
    | fuel + 1, ρ, .Var index, value, h => by
        have hlookup : ρ.lookup index = some value := by
          simpa [Moist.Verified.BigStep.bigEval] using h
        simp [eval, hlookup]
    | fuel + 1, ρ, .Constant (constant, builtinType), value, h => by
        have hvalue : CekValue.VCon constant = value := by
          simpa [Moist.Verified.BigStep.bigEval] using h
        subst value
        simp [eval]
    | fuel + 1, ρ, .Builtin builtin, value, h => by
        have hvalue : CekValue.VBuiltin builtin [] (expectedArgs builtin) = value := by
          simpa [Moist.Verified.BigStep.bigEval] using h
        subst value
        simp [eval]
    | fuel + 1, ρ, .Lam name body, value, h => by
        have hvalue : CekValue.VLam body ρ = value := by
          simpa [Moist.Verified.BigStep.bigEval] using h
        subst value
        simp [eval]
    | fuel + 1, ρ, .Delay body, value, h => by
        have hvalue : CekValue.VDelay body ρ = value := by
          simpa [Moist.Verified.BigStep.bigEval] using h
        subst value
        simp [eval]
    | fuel + 1, ρ, .Apply function argument, value, h => by
        cases hfunction : Moist.Verified.BigStep.bigEval fuel ρ function with
        | none => simp [Moist.Verified.BigStep.bigEval, hfunction] at h
        | some functionValue =>
            cases hargument : Moist.Verified.BigStep.bigEval fuel ρ argument with
            | none =>
                simp [Moist.Verified.BigStep.bigEval, hfunction, hargument] at h
            | some argumentValue =>
                have hfunctionExact := eval_ok_of_bigEval hfunction
                have hargumentExact := eval_ok_of_bigEval hargument
                have happlyBig :
                    Moist.Verified.BigStep.applyVal fuel functionValue argumentValue =
                      some value := by
                  simpa [Moist.Verified.BigStep.bigEval, hfunction, hargument] using h
                have happlyExact := apply_ok_of_applyVal happlyBig
                simp [eval, hfunctionExact, hargumentExact, happlyExact, Result.bind]
    | fuel + 1, ρ, .Force term, value, h => by
        cases hterm : Moist.Verified.BigStep.bigEval fuel ρ term with
        | none => simp [Moist.Verified.BigStep.bigEval, hterm] at h
        | some input =>
            have htermExact := eval_ok_of_bigEval hterm
            have hforceBig : Moist.Verified.BigStep.forceVal fuel input = some value := by
              simpa [Moist.Verified.BigStep.bigEval, hterm] using h
            have hforceExact := force_ok_of_forceVal hforceBig
            simp [eval, htermExact, hforceExact, Result.bind]
    | fuel + 1, ρ, .Constr tag fields, value, h => by
        cases hfields : Moist.Verified.BigStep.bigEvalList fuel ρ fields with
        | none => simp [Moist.Verified.BigStep.bigEval, hfields] at h
        | some values =>
            have hvalue : CekValue.VConstr tag values = value := by
              simpa [Moist.Verified.BigStep.bigEval, hfields] using h
            subst value
            have hfieldsExact := evalList_ok_of_bigEvalList hfields
            simp [eval, hfieldsExact, Result.bind]
    | fuel + 1, ρ, .Case scrutinee alternatives, value, h => by
        cases hscrutinee : Moist.Verified.BigStep.bigEval fuel ρ scrutinee with
        | none => simp [Moist.Verified.BigStep.bigEval, hscrutinee] at h
        | some scrutineeValue =>
            have hscrutineeExact := eval_ok_of_bigEval hscrutinee
            cases scrutineeValue with
            | VConstr tag fields =>
                cases halternative : alternatives[tag]? with
                | none =>
                    simp [Moist.Verified.BigStep.bigEval, hscrutinee, halternative] at h
                | some alternative =>
                    cases halt : Moist.Verified.BigStep.bigEval fuel ρ alternative with
                    | none =>
                        simp [Moist.Verified.BigStep.bigEval, hscrutinee,
                          halternative, halt] at h
                    | some alternativeValue =>
                        have haltExact := eval_ok_of_bigEval halt
                        have happlyBig :
                            Moist.Verified.BigStep.applyValList fuel alternativeValue fields =
                              some value := by
                          simpa [Moist.Verified.BigStep.bigEval, hscrutinee,
                            halternative, halt] using h
                        have happlyExact := applyList_ok_of_applyValList happlyBig
                        simp [eval, hscrutineeExact, halternative, haltExact,
                          happlyExact, Result.bind]
            | VCon constant =>
                cases hconstant : constToTagAndFields constant with
                | none =>
                    simp [Moist.Verified.BigStep.bigEval, hscrutinee, hconstant] at h
                | some parts =>
                    obtain ⟨tag, constructorCount, fields⟩ := parts
                    by_cases htooMany :
                        (constructorCount > 0 && alternatives.length > constructorCount) = true
                    · simp [Moist.Verified.BigStep.bigEval, hscrutinee,
                        hconstant, htooMany] at h
                    · cases halternative : alternatives[tag]? with
                      | none =>
                          simp [Moist.Verified.BigStep.bigEval, hscrutinee,
                            hconstant, htooMany, halternative] at h
                      | some alternative =>
                          cases halt : Moist.Verified.BigStep.bigEval fuel ρ alternative with
                          | none =>
                              simp [Moist.Verified.BigStep.bigEval, hscrutinee,
                                hconstant, htooMany, halternative, halt] at h
                          | some alternativeValue =>
                              have haltExact := eval_ok_of_bigEval halt
                              have happlyBig :
                                  Moist.Verified.BigStep.applyValList fuel alternativeValue fields =
                                    some value := by
                                simpa [Moist.Verified.BigStep.bigEval, hscrutinee,
                                  hconstant, htooMany, halternative, halt] using h
                              have happlyExact := applyList_ok_of_applyValList happlyBig
                              simp [eval, hscrutineeExact, hconstant, htooMany,
                                halternative, haltExact, happlyExact, Result.bind]
            | VLam _ _ => simp [Moist.Verified.BigStep.bigEval, hscrutinee] at h
            | VDelay _ _ => simp [Moist.Verified.BigStep.bigEval, hscrutinee] at h
            | VBuiltin _ _ _ => simp [Moist.Verified.BigStep.bigEval, hscrutinee] at h
    | fuel + 1, ρ, .Error, value, h => by
        simp [Moist.Verified.BigStep.bigEval] at h
  termination_by fuel _ term => (fuel, sizeOf term)

  theorem apply_ok_of_applyVal : ∀ {fuel : Nat} {function argument value : CekValue},
      Moist.Verified.BigStep.applyVal fuel function argument = some value →
        apply fuel function argument = .ok value
    | 0, _, _, _, h => by simp [Moist.Verified.BigStep.applyVal] at h
    | fuel + 1, function, argument, value, h => by
        cases function with
        | VLam body ρ =>
            have hbodyBig :
                Moist.Verified.BigStep.bigEval fuel (ρ.extend argument) body =
                  some value := by
              simpa [Moist.Verified.BigStep.applyVal] using h
            have hbody := eval_ok_of_bigEval hbodyBig
            simpa [apply] using hbody
        | VBuiltin builtin arguments expected =>
            cases expected with
            | one kind =>
                cases kind with
                | argV =>
                    have hresult : evalBuiltin builtin (argument :: arguments) =
                        some value := by
                      simpa [Moist.Verified.BigStep.applyVal,
                        ExpectedArgs.head, ExpectedArgs.tail] using h
                    simp [apply, ExpectedArgs.head, ExpectedArgs.tail, hresult]
                | argQ =>
                    simp [Moist.Verified.BigStep.applyVal, ExpectedArgs.head] at h
            | more kind rest =>
                cases kind with
                | argV =>
                    simpa [apply, Moist.Verified.BigStep.applyVal,
                      ExpectedArgs.head, ExpectedArgs.tail] using h
                | argQ =>
                    simp [Moist.Verified.BigStep.applyVal, ExpectedArgs.head] at h
        | VCon _ => simp [Moist.Verified.BigStep.applyVal] at h
        | VDelay _ _ => simp [Moist.Verified.BigStep.applyVal] at h
        | VConstr _ _ => simp [Moist.Verified.BigStep.applyVal] at h
  termination_by fuel _ _ => (fuel, 0)

  theorem force_ok_of_forceVal : ∀ {fuel : Nat} {input value : CekValue},
      Moist.Verified.BigStep.forceVal fuel input = some value →
        force fuel input = .ok value
    | 0, _, _, h => by simp [Moist.Verified.BigStep.forceVal] at h
    | fuel + 1, input, value, h => by
        cases input with
        | VDelay body ρ =>
            have hbodyBig : Moist.Verified.BigStep.bigEval fuel ρ body = some value := by
              simpa [Moist.Verified.BigStep.forceVal] using h
            have hbody := eval_ok_of_bigEval hbodyBig
            simpa [force] using hbody
        | VBuiltin builtin arguments expected =>
            cases expected with
            | one kind =>
                cases kind with
                | argQ =>
                    have hresult : evalBuiltin builtin arguments = some value := by
                      simpa [Moist.Verified.BigStep.forceVal,
                        ExpectedArgs.head, ExpectedArgs.tail] using h
                    simp [force, ExpectedArgs.head, ExpectedArgs.tail, hresult]
                | argV =>
                    simp [Moist.Verified.BigStep.forceVal, ExpectedArgs.head] at h
            | more kind rest =>
                cases kind with
                | argQ =>
                    simpa [force, Moist.Verified.BigStep.forceVal,
                      ExpectedArgs.head, ExpectedArgs.tail] using h
                | argV =>
                    simp [Moist.Verified.BigStep.forceVal, ExpectedArgs.head] at h
        | VCon _ => simp [Moist.Verified.BigStep.forceVal] at h
        | VLam _ _ => simp [Moist.Verified.BigStep.forceVal] at h
        | VConstr _ _ => simp [Moist.Verified.BigStep.forceVal] at h
  termination_by fuel _ => (fuel, 0)

  theorem evalList_ok_of_bigEvalList : ∀ {fuel : Nat} {ρ : CekEnv}
      {terms : List Term} {values : List CekValue},
      Moist.Verified.BigStep.bigEvalList fuel ρ terms = some values →
        evalList fuel ρ terms = .ok values
    | _, _, [], values, h => by
        have hvalues : values = [] := by
          simpa [Moist.Verified.BigStep.bigEvalList] using h.symm
        subst values
        simp [evalList]
    | fuel, ρ, term :: terms, values, h => by
        cases hterm : Moist.Verified.BigStep.bigEval fuel ρ term with
        | none => simp [Moist.Verified.BigStep.bigEvalList, hterm] at h
        | some value =>
            cases hterms : Moist.Verified.BigStep.bigEvalList fuel ρ terms with
            | none =>
                simp [Moist.Verified.BigStep.bigEvalList, hterm, hterms] at h
            | some rest =>
                have hvalues : values = value :: rest := by
                  simpa [Moist.Verified.BigStep.bigEvalList, hterm, hterms] using h.symm
                subst values
                have htermExact := eval_ok_of_bigEval hterm
                have htermsExact := evalList_ok_of_bigEvalList hterms
                simp [evalList, htermExact, htermsExact, Result.bind]
  termination_by fuel _ terms => (fuel, sizeOf terms)

  theorem applyList_ok_of_applyValList : ∀ {fuel : Nat} {function : CekValue}
      {arguments : List CekValue} {value : CekValue},
      Moist.Verified.BigStep.applyValList fuel function arguments = some value →
        applyList fuel function arguments = .ok value
    | _, function, [], value, h => by
        have hvalue : function = value := by
          simpa [Moist.Verified.BigStep.applyValList] using h
        subst value
        simp [applyList]
    | fuel, function, argument :: arguments, value, h => by
        cases happly : Moist.Verified.BigStep.applyVal fuel function argument with
        | none => simp [Moist.Verified.BigStep.applyValList, happly] at h
        | some next =>
            have happlyExact := apply_ok_of_applyVal happly
            have hrestBig :
                Moist.Verified.BigStep.applyValList fuel next arguments = some value := by
              simpa [Moist.Verified.BigStep.applyValList, happly] using h
            have hrest := applyList_ok_of_applyValList hrestBig
            simp [applyList, happlyExact, hrest, Result.bind]
  termination_by fuel _ arguments => (fuel, sizeOf arguments)
end

/-! ## Forward simulation to the actual CEK transition system -/

mutual
  /-- Every non-timeout result of `eval` is realized by the CEK under any
  continuation stack. -/
  theorem eval_fwd : ∀ (fuel : Nat) (ρ : CekEnv) (term : Term) (stack : Stack),
      Result.ReachesAs (.compute stack ρ term) (fun value => .ret stack value)
        (eval fuel ρ term)
    | 0, _, _, _ => by simp [eval, Result.ReachesAs]
    | fuel + 1, ρ, .Var index, stack => by
        cases hlookup : ρ.lookup index with
        | none =>
            simpa [eval, hlookup, Result.ReachesAs] using
              (one_step (show step (.compute stack ρ (.Var index)) = .error by
                simp [step, hlookup]))
        | some value =>
            simpa [eval, hlookup, Result.ReachesAs] using
              (one_step (show step (.compute stack ρ (.Var index)) = .ret stack value by
                simp [step, hlookup]))
    | fuel + 1, ρ, .Constant (constant, builtinType), stack => by
        simpa [eval, Result.ReachesAs] using
          (one_step (show
            step (.compute stack ρ (.Constant (constant, builtinType))) =
              .ret stack (.VCon constant) by rfl))
    | fuel + 1, ρ, .Builtin builtin, stack => by
        simpa [eval, Result.ReachesAs] using
          (one_step (show step (.compute stack ρ (.Builtin builtin)) =
            .ret stack (.VBuiltin builtin [] (expectedArgs builtin)) by rfl))
    | fuel + 1, ρ, .Lam name body, stack => by
        simpa [eval, Result.ReachesAs] using
          (one_step (show step (.compute stack ρ (.Lam name body)) =
            .ret stack (.VLam body ρ) by rfl))
    | fuel + 1, ρ, .Delay body, stack => by
        simpa [eval, Result.ReachesAs] using
          (one_step (show step (.compute stack ρ (.Delay body)) =
            .ret stack (.VDelay body ρ) by rfl))
    | fuel + 1, ρ, .Apply function argument, stack => by
        cases hfunction : eval fuel ρ function with
        | timeout => simp [eval, hfunction, Result.bind, Result.ReachesAs]
        | error =>
            have hfunctionCek := eval_fwd fuel ρ function (.arg argument ρ :: stack)
            simp [hfunction, Result.ReachesAs] at hfunctionCek
            simpa [eval, hfunction, Result.bind, Result.ReachesAs] using
              reaches_trans
                (one_step (show
                  step (.compute stack ρ (.Apply function argument)) =
                    .compute (.arg argument ρ :: stack) ρ function by rfl))
                hfunctionCek
        | ok functionValue =>
            have hfunctionCek := eval_fwd fuel ρ function (.arg argument ρ :: stack)
            simp [hfunction, Result.ReachesAs] at hfunctionCek
            cases hargument : eval fuel ρ argument with
            | timeout => simp [eval, hfunction, hargument, Result.bind, Result.ReachesAs]
            | error =>
                have hargumentCek := eval_fwd fuel ρ argument (.funV functionValue :: stack)
                simp [hargument, Result.ReachesAs] at hargumentCek
                simpa [eval, hfunction, hargument, Result.bind, Result.ReachesAs] using
                  reaches_trans
                    (one_step (show
                      step (.compute stack ρ (.Apply function argument)) =
                        .compute (.arg argument ρ :: stack) ρ function by rfl))
                    (reaches_trans hfunctionCek
                      (reaches_trans
                        (one_step (show
                          step (.ret (.arg argument ρ :: stack) functionValue) =
                            .compute (.funV functionValue :: stack) ρ argument by rfl))
                        hargumentCek))
            | ok argumentValue =>
                have hargumentCek := eval_fwd fuel ρ argument (.funV functionValue :: stack)
                simp [hargument, Result.ReachesAs] at hargumentCek
                have happly := apply_fwd fuel functionValue argumentValue stack
                simpa [eval, hfunction, hargument, Result.bind] using
                  Result.ReachesAs.prepend
                    (reaches_trans
                      (one_step (show
                        step (.compute stack ρ (.Apply function argument)) =
                          .compute (.arg argument ρ :: stack) ρ function by rfl))
                      (reaches_trans hfunctionCek
                        (reaches_trans
                          (one_step (show
                            step (.ret (.arg argument ρ :: stack) functionValue) =
                              .compute (.funV functionValue :: stack) ρ argument by rfl))
                          hargumentCek))) happly
    | fuel + 1, ρ, .Force term, stack => by
        cases hterm : eval fuel ρ term with
        | timeout => simp [eval, hterm, Result.bind, Result.ReachesAs]
        | error =>
            have htermCek := eval_fwd fuel ρ term (.force :: stack)
            simp [hterm, Result.ReachesAs] at htermCek
            simpa [eval, hterm, Result.bind, Result.ReachesAs] using
              reaches_trans
                (one_step (show step (.compute stack ρ (.Force term)) =
                  .compute (.force :: stack) ρ term by rfl)) htermCek
        | ok value =>
            have htermCek := eval_fwd fuel ρ term (.force :: stack)
            simp [hterm, Result.ReachesAs] at htermCek
            have hforce := force_fwd fuel value stack
            simpa [eval, hterm, Result.bind] using
              Result.ReachesAs.prepend
                (reaches_trans
                  (one_step (show step (.compute stack ρ (.Force term)) =
                    .compute (.force :: stack) ρ term by rfl)) htermCek) hforce
    | fuel + 1, ρ, .Constr tag fields, stack => by
        cases fields with
        | nil =>
            simpa [eval, evalList, Result.bind, Result.ReachesAs] using
              (one_step (show step (.compute stack ρ (.Constr tag [])) =
                .ret stack (.VConstr tag []) by rfl))
        | cons field fields =>
            cases hfield : eval fuel ρ field with
            | timeout =>
                simp [eval, evalList, hfield, Result.bind, Result.ReachesAs]
            | error =>
                have hfieldCek :=
                  eval_fwd fuel ρ field (.constrField tag [] fields ρ :: stack)
                simp [hfield, Result.ReachesAs] at hfieldCek
                simpa [eval, evalList, hfield, Result.bind, Result.ReachesAs] using
                  reaches_trans
                    (one_step (show
                      step (.compute stack ρ (.Constr tag (field :: fields))) =
                        .compute (.constrField tag [] fields ρ :: stack) ρ field by rfl))
                    hfieldCek
            | ok value =>
                have hfieldCek :=
                  eval_fwd fuel ρ field (.constrField tag [] fields ρ :: stack)
                simp [hfield, Result.ReachesAs] at hfieldCek
                have hrest := constr_fwd fuel ρ fields tag [] stack value
                have hcomposed := Result.ReachesAs.prepend
                    (reaches_trans
                      (one_step (show
                        step (.compute stack ρ (.Constr tag (field :: fields))) =
                          .compute (.constrField tag [] fields ρ :: stack) ρ field by rfl))
                      hfieldCek) hrest
                have hmapped := Result.ReachesAs.bind_ok
                  (f := fun values => CekValue.VConstr tag (value :: values)) hcomposed
                simpa [eval, evalList, hfield, Result.bind_assoc] using hmapped
    | fuel + 1, ρ, .Case scrutinee alternatives, stack => by
        cases hscrutinee : eval fuel ρ scrutinee with
        | timeout => simp [eval, hscrutinee, Result.bind, Result.ReachesAs]
        | error =>
            have hscrutineeCek :=
              eval_fwd fuel ρ scrutinee (.caseScrutinee alternatives ρ :: stack)
            simp [hscrutinee, Result.ReachesAs] at hscrutineeCek
            simpa [eval, hscrutinee, Result.bind, Result.ReachesAs] using
              reaches_trans
                (one_step (show
                  step (.compute stack ρ (.Case scrutinee alternatives)) =
                    .compute (.caseScrutinee alternatives ρ :: stack) ρ scrutinee by rfl))
                hscrutineeCek
        | ok value =>
            have hscrutineeCek :=
              eval_fwd fuel ρ scrutinee (.caseScrutinee alternatives ρ :: stack)
            simp [hscrutinee, Result.ReachesAs] at hscrutineeCek
            simpa [eval, hscrutinee, Result.bind] using
              Result.ReachesAs.prepend
                (reaches_trans
                  (one_step (show
                    step (.compute stack ρ (.Case scrutinee alternatives)) =
                      .compute (.caseScrutinee alternatives ρ :: stack) ρ scrutinee by rfl))
                  hscrutineeCek)
                (case_fwd fuel ρ alternatives stack value)
    | fuel + 1, ρ, .Error, stack => by
        simpa [eval, Result.ReachesAs] using
          (one_step (show step (.compute stack ρ .Error) = .error by rfl))
  termination_by fuel _ term _ => (fuel, sizeOf term, 0)

  /-- Forward simulation for application through a `funV` continuation. -/
  theorem apply_fwd : ∀ (fuel : Nat) (function argument : CekValue) (stack : Stack),
      Result.ReachesAs (.ret (.funV function :: stack) argument)
        (fun value => .ret stack value) (apply fuel function argument)
    | 0, _, _, _ => by simp [apply, Result.ReachesAs]
    | fuel + 1, function, argument, stack => by
        cases function with
        | VLam body ρ =>
            simpa [apply] using
              Result.ReachesAs.prepend
                (one_step (show
                  step (.ret (.funV (.VLam body ρ) :: stack) argument) =
                    .compute stack (ρ.extend argument) body by rfl))
                (eval_fwd fuel (ρ.extend argument) body stack)
        | VBuiltin builtin arguments expected =>
            cases expected with
            | one kind =>
                cases kind with
                | argV =>
                    cases hresult : evalBuiltin builtin (argument :: arguments) with
                    | none =>
                        simpa [apply, ExpectedArgs.head, ExpectedArgs.tail, hresult,
                          Result.ReachesAs] using
                          (one_step (show
                            step (.ret (.funV (.VBuiltin builtin arguments (.one .argV)) :: stack)
                              argument) = .error by
                              simp [step, ExpectedArgs.head, ExpectedArgs.tail, hresult]))
                    | some value =>
                        simpa [apply, ExpectedArgs.head, ExpectedArgs.tail, hresult,
                          Result.ReachesAs] using
                          (one_step (show
                            step (.ret (.funV (.VBuiltin builtin arguments (.one .argV)) :: stack)
                              argument) = .ret stack value by
                              simp [step, ExpectedArgs.head, ExpectedArgs.tail, hresult]))
                | argQ =>
                    simpa [apply, ExpectedArgs.head, Result.ReachesAs] using
                      (one_step (show
                        step (.ret (.funV (.VBuiltin builtin arguments (.one .argQ)) :: stack)
                          argument) = .error by simp [step, ExpectedArgs.head]))
            | more kind rest =>
                cases kind with
                | argV =>
                    simpa [apply, ExpectedArgs.head, ExpectedArgs.tail,
                      Result.ReachesAs] using
                      (one_step (show
                        step (.ret
                          (.funV (.VBuiltin builtin arguments (.more .argV rest)) :: stack)
                          argument) =
                            .ret stack (.VBuiltin builtin (argument :: arguments) rest) by
                          simp [step, ExpectedArgs.head, ExpectedArgs.tail]))
                | argQ =>
                    simpa [apply, ExpectedArgs.head, Result.ReachesAs] using
                      (one_step (show
                        step (.ret
                          (.funV (.VBuiltin builtin arguments (.more .argQ rest)) :: stack)
                          argument) = .error by simp [step, ExpectedArgs.head]))
        | VCon constant =>
            simpa [apply, Result.ReachesAs] using
              (one_step (show
                step (.ret (.funV (.VCon constant) :: stack) argument) = .error by rfl))
        | VDelay body ρ =>
            simpa [apply, Result.ReachesAs] using
              (one_step (show
                step (.ret (.funV (.VDelay body ρ) :: stack) argument) = .error by rfl))
        | VConstr tag fields =>
            simpa [apply, Result.ReachesAs] using
              (one_step (show
                step (.ret (.funV (.VConstr tag fields) :: stack) argument) = .error by rfl))
  termination_by fuel _ _ _ => (fuel, 0, 0)

  /-- Forward simulation for forcing. -/
  theorem force_fwd : ∀ (fuel : Nat) (value : CekValue) (stack : Stack),
      Result.ReachesAs (.ret (.force :: stack) value)
        (fun result => .ret stack result) (force fuel value)
    | 0, _, _ => by simp [force, Result.ReachesAs]
    | fuel + 1, value, stack => by
        cases value with
        | VDelay body ρ =>
            simpa [force] using
              Result.ReachesAs.prepend
                (one_step (show
                  step (.ret (.force :: stack) (.VDelay body ρ)) =
                    .compute stack ρ body by rfl))
                (eval_fwd fuel ρ body stack)
        | VBuiltin builtin arguments expected =>
            cases expected with
            | one kind =>
                cases kind with
                | argQ =>
                    cases hresult : evalBuiltin builtin arguments with
                    | none =>
                        simpa [force, ExpectedArgs.head, ExpectedArgs.tail, hresult,
                          Result.ReachesAs] using
                          (one_step (show
                            step (.ret (.force :: stack)
                              (.VBuiltin builtin arguments (.one .argQ))) = .error by
                              simp [step, ExpectedArgs.head, ExpectedArgs.tail, hresult]))
                    | some result =>
                        simpa [force, ExpectedArgs.head, ExpectedArgs.tail, hresult,
                          Result.ReachesAs] using
                          (one_step (show
                            step (.ret (.force :: stack)
                              (.VBuiltin builtin arguments (.one .argQ))) = .ret stack result by
                              simp [step, ExpectedArgs.head, ExpectedArgs.tail, hresult]))
                | argV =>
                    simpa [force, ExpectedArgs.head, Result.ReachesAs] using
                      (one_step (show step (.ret (.force :: stack)
                        (.VBuiltin builtin arguments (.one .argV))) = .error by
                        simp [step, ExpectedArgs.head]))
            | more kind rest =>
                cases kind with
                | argQ =>
                    simpa [force, ExpectedArgs.head, ExpectedArgs.tail,
                      Result.ReachesAs] using
                      (one_step (show step (.ret (.force :: stack)
                        (.VBuiltin builtin arguments (.more .argQ rest))) =
                          .ret stack (.VBuiltin builtin arguments rest) by
                        simp [step, ExpectedArgs.head, ExpectedArgs.tail]))
                | argV =>
                    simpa [force, ExpectedArgs.head, Result.ReachesAs] using
                      (one_step (show step (.ret (.force :: stack)
                        (.VBuiltin builtin arguments (.more .argV rest))) = .error by
                        simp [step, ExpectedArgs.head]))
        | VCon constant =>
            simpa [force, Result.ReachesAs] using
              (one_step (show step (.ret (.force :: stack) (.VCon constant)) = .error by rfl))
        | VLam body ρ =>
            simpa [force, Result.ReachesAs] using
              (one_step (show step (.ret (.force :: stack) (.VLam body ρ)) = .error by rfl))
        | VConstr tag fields =>
            simpa [force, Result.ReachesAs] using
              (one_step (show step (.ret (.force :: stack) (.VConstr tag fields)) = .error by rfl))
  termination_by fuel _ _ => (fuel, 0, 0)

  /-- Forward simulation for the constructor-field continuation. -/
  theorem constr_fwd : ∀ (fuel : Nat) (ρ : CekEnv) (remaining : List Term)
      (tag : Nat) (done : List CekValue) (stack : Stack) (value : CekValue),
      Result.ReachesAs
        (.ret (.constrField tag done remaining ρ :: stack) value)
        (fun values => .ret stack (.VConstr tag ((value :: done).reverse ++ values)))
        (evalList fuel ρ remaining)
    | fuel, ρ, [], tag, done, stack, value => by
        simpa [evalList, Result.ReachesAs] using
          (one_step (show
            step (.ret (.constrField tag done [] ρ :: stack) value) =
              .ret stack (.VConstr tag (value :: done).reverse) by rfl))
    | fuel, ρ, term :: terms, tag, done, stack, value => by
        cases hterm : eval fuel ρ term with
        | timeout => simp [evalList, hterm, Result.bind, Result.ReachesAs]
        | error =>
            have htermCek :=
              eval_fwd fuel ρ term (.constrField tag (value :: done) terms ρ :: stack)
            simp [hterm, Result.ReachesAs] at htermCek
            simpa [evalList, hterm, Result.bind, Result.ReachesAs] using
              reaches_trans
                (one_step (show
                  step (.ret (.constrField tag done (term :: terms) ρ :: stack) value) =
                    .compute (.constrField tag (value :: done) terms ρ :: stack) ρ term by
                  rfl)) htermCek
        | ok next =>
            have htermCek :=
              eval_fwd fuel ρ term (.constrField tag (value :: done) terms ρ :: stack)
            simp [hterm, Result.ReachesAs] at htermCek
            have hrest := constr_fwd fuel ρ terms tag (value :: done) stack next
            have hcomposed := Result.ReachesAs.prepend
                (reaches_trans
                  (one_step (show
                    step (.ret (.constrField tag done (term :: terms) ρ :: stack) value) =
                      .compute (.constrField tag (value :: done) terms ρ :: stack) ρ term by
                    rfl)) htermCek) hrest
            have hcomposed' :
                Result.ReachesAs
                  (.ret (.constrField tag done (term :: terms) ρ :: stack) value)
                  (fun values => .ret stack
                    (.VConstr tag ((value :: done).reverse ++ (next :: values))))
                  (evalList fuel ρ terms) := by
              simpa [List.reverse_cons, List.append_assoc] using hcomposed
            have hmapped := Result.ReachesAs.bind_ok
              (finish := fun values => .ret stack
                (.VConstr tag ((value :: done).reverse ++ values)))
              (f := fun values => next :: values) hcomposed'
            simpa [evalList, hterm, List.reverse_cons, List.append_assoc] using hmapped
  termination_by fuel _ remaining _ _ _ _ => (fuel, sizeOf remaining, 0)

  /-- Forward simulation for application through an `applyArg` continuation. -/
  theorem applyArg_fwd : ∀ (fuel : Nat) (function argument : CekValue) (stack : Stack),
      Result.ReachesAs (.ret (.applyArg argument :: stack) function)
        (fun value => .ret stack value) (apply fuel function argument)
    | fuel, function, argument, stack => by
        have hstep :
            step (.ret (.applyArg argument :: stack) function) =
              step (.ret (.funV function :: stack) argument) := by
          cases function with
          | VBuiltin builtin arguments expected =>
              cases expected with
              | one kind => cases kind <;> rfl
              | more kind rest => cases kind <;> rfl
          | _ => rfl
        have hfun := apply_fwd fuel function argument stack
        cases hresult : apply fuel function argument with
        | timeout => simp [Result.ReachesAs]
        | error =>
            rw [hresult] at hfun
            exact reaches_trans (one_step hstep)
              (reaches_tail_of_ne hfun (by simp))
        | ok value =>
            rw [hresult] at hfun
            exact reaches_trans (one_step hstep)
              (reaches_tail_of_ne hfun (by simp))
  termination_by fuel _ _ _ => (fuel, 0, 1)

  /-- Forward simulation for a sequence of `applyArg` continuations. -/
  theorem applyList_fwd : ∀ (fuel : Nat) (function : CekValue)
      (arguments : List CekValue) (stack : Stack),
      Result.ReachesAs (.ret (arguments.map Frame.applyArg ++ stack) function)
        (fun value => .ret stack value) (applyList fuel function arguments)
    | fuel, function, [], stack => by
        simpa [applyList, Result.ReachesAs] using
          reaches_refl (.ret stack function)
    | fuel, function, argument :: arguments, stack => by
        cases happly : apply fuel function argument with
        | timeout => simp [applyList, happly, Result.bind, Result.ReachesAs]
        | error =>
            have happlyCek :=
              applyArg_fwd fuel function argument (arguments.map Frame.applyArg ++ stack)
            simp [happly, Result.ReachesAs] at happlyCek
            simpa [applyList, happly, Result.bind, Result.ReachesAs] using happlyCek
        | ok next =>
            have happlyCek :=
              applyArg_fwd fuel function argument (arguments.map Frame.applyArg ++ stack)
            simp [happly, Result.ReachesAs] at happlyCek
            have hrest := applyList_fwd fuel next arguments stack
            simpa [applyList, happly, Result.bind] using
              Result.ReachesAs.prepend happlyCek hrest
  termination_by fuel _ arguments _ => (fuel, sizeOf arguments, 0)

  /-- Forward simulation for the value-specific part of a `Case`. -/
  theorem case_fwd : ∀ (fuel : Nat) (ρ : CekEnv) (alternatives : List Term)
      (stack : Stack) (scrutinee : CekValue),
      Result.ReachesAs (.ret (.caseScrutinee alternatives ρ :: stack) scrutinee)
        (fun value => .ret stack value)
        (match scrutinee with
         | .VConstr tag fields =>
             match alternatives[tag]? with
             | some alternative =>
                 (eval fuel ρ alternative).bind fun alternativeValue =>
                   applyList fuel alternativeValue fields
             | none => .error
         | .VCon constant =>
             match constToTagAndFields constant with
             | some (tag, constructorCount, fields) =>
                 if constructorCount > 0 && alternatives.length > constructorCount then .error
                 else
                   match alternatives[tag]? with
                   | some alternative =>
                       (eval fuel ρ alternative).bind fun alternativeValue =>
                         applyList fuel alternativeValue fields
                   | none => .error
             | none => .error
         | _ => .error)
    | fuel, ρ, alternatives, stack, scrutinee => by
        cases scrutinee with
        | VConstr tag fields =>
            cases halternative : alternatives[tag]? with
            | none =>
                simpa [halternative, Result.ReachesAs] using
                  (one_step (show
                    step (.ret (.caseScrutinee alternatives ρ :: stack)
                      (.VConstr tag fields)) = .error by simp [step, halternative]))
            | some alternative =>
                cases heval : eval fuel ρ alternative with
                | timeout =>
                    simp [halternative, heval, Result.bind, Result.ReachesAs]
                | error =>
                    have hevalCek :=
                      eval_fwd fuel ρ alternative (fields.map Frame.applyArg ++ stack)
                    simp [heval, Result.ReachesAs] at hevalCek
                    simpa [halternative, heval, Result.bind, Result.ReachesAs] using
                      reaches_trans
                        (one_step (show
                          step (.ret (.caseScrutinee alternatives ρ :: stack)
                            (.VConstr tag fields)) =
                              .compute (fields.map Frame.applyArg ++ stack) ρ alternative by
                            simp [step, halternative])) hevalCek
                | ok alternativeValue =>
                    have hevalCek :=
                      eval_fwd fuel ρ alternative (fields.map Frame.applyArg ++ stack)
                    simp [heval, Result.ReachesAs] at hevalCek
                    simpa [halternative, heval, Result.bind] using
                      Result.ReachesAs.prepend
                        (reaches_trans
                          (one_step (show
                            step (.ret (.caseScrutinee alternatives ρ :: stack)
                              (.VConstr tag fields)) =
                                .compute (fields.map Frame.applyArg ++ stack) ρ alternative by
                              simp [step, halternative])) hevalCek)
                        (applyList_fwd fuel alternativeValue fields stack)
        | VCon constant =>
            cases hconstant : constToTagAndFields constant with
            | none =>
                simpa [hconstant, Result.ReachesAs] using
                  (one_step (show
                    step (.ret (.caseScrutinee alternatives ρ :: stack) (.VCon constant)) =
                      .error by simp [step, hconstant]))
            | some value =>
                obtain ⟨tag, constructorCount, fields⟩ := value
                by_cases htooMany :
                    (constructorCount > 0 && alternatives.length > constructorCount) = true
                · simpa [hconstant, htooMany, Result.ReachesAs] using
                    (one_step (show
                      step (.ret (.caseScrutinee alternatives ρ :: stack) (.VCon constant)) =
                        .error by simp [step, hconstant, htooMany]))
                · cases halternative : alternatives[tag]? with
                  | none =>
                      simpa [hconstant, htooMany, halternative, Result.ReachesAs] using
                        (one_step (show
                          step (.ret (.caseScrutinee alternatives ρ :: stack)
                            (.VCon constant)) = .error by
                            simp [step, hconstant, htooMany, halternative]))
                  | some alternative =>
                      cases heval : eval fuel ρ alternative with
                      | timeout =>
                          simp [hconstant, htooMany, halternative, heval,
                            Result.bind, Result.ReachesAs]
                      | error =>
                          have hevalCek :=
                            eval_fwd fuel ρ alternative
                              (fields.map Frame.applyArg ++ stack)
                          simp [heval, Result.ReachesAs] at hevalCek
                          simpa [hconstant, htooMany, halternative, heval,
                            Result.bind, Result.ReachesAs] using
                            reaches_trans
                              (one_step (show
                                step (.ret (.caseScrutinee alternatives ρ :: stack)
                                  (.VCon constant)) =
                                    .compute (fields.map Frame.applyArg ++ stack) ρ alternative by
                                  simp [step, hconstant, htooMany, halternative])) hevalCek
                      | ok alternativeValue =>
                          have hevalCek :=
                            eval_fwd fuel ρ alternative
                              (fields.map Frame.applyArg ++ stack)
                          simp [heval, Result.ReachesAs] at hevalCek
                          simpa [hconstant, htooMany, halternative, heval,
                            Result.bind] using
                            Result.ReachesAs.prepend
                              (reaches_trans
                                (one_step (show
                                  step (.ret (.caseScrutinee alternatives ρ :: stack)
                                    (.VCon constant)) =
                                      .compute (fields.map Frame.applyArg ++ stack) ρ alternative by
                                    simp [step, hconstant, htooMany, halternative])) hevalCek)
                              (applyList_fwd fuel alternativeValue fields stack)
        | VLam body closure =>
            simpa [Result.ReachesAs] using
              (one_step (show step (.ret (.caseScrutinee alternatives ρ :: stack)
                (.VLam body closure)) = .error by rfl))
        | VDelay body closure =>
            simpa [Result.ReachesAs] using
              (one_step (show step (.ret (.caseScrutinee alternatives ρ :: stack)
                (.VDelay body closure)) = .error by rfl))
        | VBuiltin builtin arguments expected =>
            simpa [Result.ReachesAs] using
              (one_step (show step (.ret (.caseScrutinee alternatives ρ :: stack)
                (.VBuiltin builtin arguments expected)) = .error by rfl))
  termination_by fuel _ _ _ _ => (fuel + 1, 0, 0)
end

end Moist.Verified.ExactBigStep
