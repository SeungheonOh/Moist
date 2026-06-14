import Moist.Verified.SmallStep.ValueDischarge

/-! # Discharging CEK stacks/states + the evaluation-context lemmas

`dischargeStack π t` plugs `t` into the evaluation context represented by the
CEK stack `π`; `dischargeState s` discharges a whole machine state.  Under a
well-formedness invariant (`WFStack`), the discharged stack is a genuine
small-step evaluation context: reduction propagates through it
(`dischargeStack_cong`) and `Error` bubbles up to `Error`
(`dischargeStack_error`).
-/

namespace Moist.Verified.SmallStep

open Moist.Plutus.Term (Term)
open Moist.CEK (CekValue CekEnv Frame Stack State)

/-! ## `ValueList` on reverse -/

theorem valueList_mem_iff {l : List Term} : ValueList l ↔ ∀ x ∈ l, Value x := by
  constructor
  · intro h x hx; exact valueList_mem h hx
  · intro h
    induction l with
    | nil => exact .nil
    | cons a as ih =>
      exact .cons (h a List.mem_cons_self)
        (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))

theorem valueList_reverse {l : List Term} (h : ValueList l) : ValueList l.reverse := by
  rw [valueList_mem_iff] at h ⊢
  intro x hx; exact h x (by simpa using hx)

/-! ## Discharging stacks and states -/

/-- A single CEK frame as a small-step evaluation context (hole = `t`). -/
def frameCtx : Frame → Term → Term
  | .force, t => .Force t
  | .arg M ρ, t => .Apply t (dischargeEnv ρ 0 M)
  | .funV vf, t => .Apply (discharge vf) t
  | .applyArg vx, t => .Apply t (discharge vx)
  | .constrField tag done todo ρ, t =>
      .Constr tag ((dischargeList done).reverse ++ t :: todo.map (fun m => dischargeEnv ρ 0 m))
  | .caseScrutinee alts ρ, t => .Case t (alts.map (fun m => dischargeEnv ρ 0 m))

/-- Plug a term into the evaluation context represented by a CEK stack. -/
def dischargeStack : Stack → Term → Term
  | [], t => t
  | f :: π, t => dischargeStack π (frameCtx f t)

/-- Discharge a whole CEK state into the UPLC term it represents. -/
def dischargeState : State → Term
  | .compute π ρ M => dischargeStack π (dischargeEnv ρ 0 M)
  | .ret π v => dischargeStack π (discharge v)
  | .halt v => discharge v
  | .error => .Error

theorem dischargeState_init (t : Term) : dischargeState (init t) = t := by
  simp only [init, dischargeState, dischargeStack, dischargeEnv]

/-! ## Well-formedness invariant -/

/-- A frame is well-formed when its stored values are well-formed. -/
def WFFrame : Frame → Prop
  | .force => True
  | .arg _ _ => True
  | .funV vf => WFValue vf
  | .applyArg vx => WFValue vx
  | .constrField _ done _ _ => WFValueList done
  | .caseScrutinee _ _ => True

/-- Every frame on the stack is well-formed. -/
def WFStack (π : Stack) : Prop := ∀ f ∈ π, WFFrame f

theorem wfStack_nil : WFStack [] := fun _ h => by cases h

theorem wfStack_tail {f : Frame} {π : Stack} (h : WFStack (f :: π)) : WFStack π :=
  fun g hg => h g (List.mem_cons_of_mem f hg)

theorem wfStack_head {f : Frame} {π : Stack} (h : WFStack (f :: π)) : WFFrame f :=
  h f List.mem_cons_self

theorem wfStack_cons {f : Frame} {π : Stack} (hf : WFFrame f) (hπ : WFStack π) :
    WFStack (f :: π) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact hf
  · exact hπ g hg

/-! ## The evaluation-context lemmas -/

/-- A well-formed frame is an evaluation context: reduction propagates. -/
theorem frameCtx_cong {a b : Term} (f : Frame) (hf : WFFrame f) (h : Step a b) :
    Step (frameCtx f a) (frameCtx f b) := by
  cases f with
  | force => exact .congForce h
  | arg M ρ => exact .congAppL h
  | funV vf => exact .congAppR (value_discharge hf) h
  | applyArg vx => exact .congAppL h
  | constrField tag done todo ρ =>
      exact .congConstr (valueList_reverse (valueList_discharge hf)) h
  | caseScrutinee alts ρ => exact .congCase h

/-- `Error` reaches `Error` through a well-formed frame. -/
theorem frameCtx_error (f : Frame) (hf : WFFrame f) : Step (frameCtx f .Error) .Error := by
  cases f with
  | force => exact .errForce
  | arg M ρ => exact .errAppL
  | funV vf => exact .errAppR (value_discharge hf)
  | applyArg vx => exact .errAppL
  | constrField tag done todo ρ =>
      exact .errConstr (valueList_reverse (valueList_discharge hf))
  | caseScrutinee alts ρ => exact .errCase

/-- Reduction propagates through a discharged well-formed stack. -/
theorem dischargeStack_cong : ∀ {π : Stack}, WFStack π → ∀ {a b : Term}, Step a b →
    Step (dischargeStack π a) (dischargeStack π b)
  | [], _, _, _, h => h
  | f :: _, hπ, _, _, h =>
      dischargeStack_cong (wfStack_tail hπ) (frameCtx_cong f (wfStack_head hπ) h)

/-- `Error` bubbles up to `Error` through a discharged well-formed stack. -/
theorem dischargeStack_error : ∀ {π : Stack}, WFStack π → Steps (dischargeStack π .Error) .Error
  | [], _ => .refl
  | f :: _, hπ =>
      .step (dischargeStack_cong (wfStack_tail hπ) (frameCtx_error f (wfStack_head hπ)))
        (dischargeStack_error (wfStack_tail hπ))

end Moist.Verified.SmallStep
