import Moist.Verified.ShapeFacts.Heads
import Moist.Verified.ListShapeSoundness

variable [sv : Moist.CEK.SemVariant]

/-! # Shapes of builtin results

Value predicates used by the shape analyses and the result shapes of the
saturated builtins they accept. A saturated application of an accepted
protocol evaluates the builtin on exactly as many values as it expects
(`saturated_apply`).
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence

def BoolValue (v : CekValue) : Prop := ∃ c, v = .VCon (.Bool c)

def IntegerValue (v : CekValue) : Prop := ∃ i, v = .VCon (.Integer i)

/-- The result of `UnConstrData`. -/
def PairValue (v : CekValue) : Prop :=
  ∃ i fields, v = .VCon (.Pair (.Integer i, .dataList fields))

export Moist.Verified.ListShape (ListValue)

/-- A saturating application of a builtin state expecting one last value. -/
theorem saturated_apply {wf wa v : CekValue} {b : BuiltinFun}
    (hwf : BuiltinState b (.one .argV) wf) (h : Reaches (.ret [.funV wf] wa) (.halt v)) :
    ∃ args, (wa :: args).length = valueArity (expectedArgs b) ∧ evalBuiltin b (wa :: args) = some v := by
  obtain ⟨args, rfl, hlen⟩ := hwf
  rcases apply_reaches h with ⟨_, _, impossible, _⟩ | ⟨b', args', ea, heq, _, hres⟩
  · cases impossible
  · cases heq
    rcases hres with ⟨rest, ht, _⟩ | ⟨_, heval⟩
    · cases ht
    · refine ⟨args, ?_, heval⟩
      simp [valueArity] at hlen ⊢; omega

/-- A saturating force of a builtin state expecting one last type argument. -/
theorem saturated_force {w v : CekValue} {b : BuiltinFun}
    (hw : BuiltinState b (.one .argQ) w) (h : Reaches (.ret [.force] w) (.halt v)) :
    ∃ vs, vs.length = valueArity (expectedArgs b) ∧ evalBuiltin b vs = some v := by
  obtain ⟨args, rfl, hlen⟩ := hw
  rcases force_reaches h with ⟨_, _, impossible, _⟩ | ⟨b', args', ea, heq, _, hres⟩
  · cases impossible
  · cases heq
    rcases hres with ⟨rest, ht, _⟩ | ⟨_, heval⟩
    · cases ht
    · exact ⟨args, by simp [valueArity] at hlen ⊢; omega, heval⟩

omit sv in
theorem extractConsts_length : ∀ {vs : List CekValue} {cs : List Const},
    extractConsts vs = some cs → cs.length = vs.length
  | [], cs, h => by simp [extractConsts] at h; subst h; rfl
  | .VCon c :: vs, cs, h => by
    simp only [extractConsts] at h
    cases hr : extractConsts vs with
    | none => rw [hr] at h; cases h
    | some rest =>
      rw [hr] at h; simp at h; subst h
      simp [extractConsts_length hr]
  | .VLam _ _ :: _, _, h | .VDelay _ _ :: _, _, h | .VConstr _ _ :: _, _, h
  | .VBuiltin _ _ _ :: _, _, h => by simp [extractConsts] at h

/-- Builtins that never pass a value through return a constant computed by
    `evalBuiltinConst`. -/
theorem evalBuiltin_const {b : BuiltinFun} {vs : List CekValue} {v : CekValue}
    (hb : b ≠ .IfThenElse ∧ b ≠ .ChooseUnit ∧ b ≠ .Trace ∧ b ≠ .ChooseData ∧
      b ≠ .ChooseList ∧ b ≠ .MkCons)
    (h : evalBuiltin b vs = some v) :
    ∃ cs c, cs.length = vs.length ∧ evalBuiltinConst b cs = some c ∧ v = .VCon c := by
  simp only [evalBuiltin, evalBuiltinPassThrough_none_of_not_passthrough b vs hb] at h
  cases hc : extractConsts vs with
  | none => rw [hc] at h; cases h
  | some cs =>
    rw [hc] at h
    simp only at h
    cases he : evalBuiltinConst b cs with
    | none => rw [he] at h; cases h
    | some c =>
      rw [he] at h; cases h
      exact ⟨cs, c, extractConsts_length hc, he, rfl⟩

theorem booleanBuiltin_result {b : BuiltinFun} (hb : booleanBuiltin b = true)
    {vs : List CekValue} {v : CekValue} (hlen : vs.length = valueArity (expectedArgs b))
    (h : evalBuiltin b vs = some v) : BoolValue v := by
  have np : b ≠ .IfThenElse ∧ b ≠ .ChooseUnit ∧ b ≠ .Trace ∧ b ≠ .ChooseData ∧
      b ≠ .ChooseList ∧ b ≠ .MkCons := by
    cases b <;> simp [booleanBuiltin] at hb <;> decide
  obtain ⟨cs, c, hcs, hc, rfl⟩ := evalBuiltin_const np h
  rw [← hcs] at hlen
  suffices ∃ x, c = .Bool x by obtain ⟨x, rfl⟩ := this; exact ⟨x, rfl⟩
  cases b <;> simp [booleanBuiltin] at hb <;> simp [expectedArgs, valueArity] at hlen
  all_goals
    rcases cs with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, rest⟩⟩⟩⟩ <;> simp at hlen
  all_goals first
    | (cases hc; done)
    | (cases x <;> (try cases hc) <;> exact ⟨_, rfl⟩)
    | (cases x <;> (try cases hc) <;> cases y <;> (try cases hc) <;>
        first | exact ⟨_, rfl⟩ | (obtain rfl := eq_of_ite_some hc; exact ⟨_, rfl⟩))

/-- The integer-valued builtins accepted by `knownInteger`. -/
def integerBuiltin : BuiltinFun → Bool
  | .AddInteger | .SubtractInteger | .MultiplyInteger | .DivideInteger
  | .QuotientInteger | .RemainderInteger | .ModInteger | .UnIData
  | .LengthOfByteString | .IndexByteString => true
  | _ => false

theorem integerBuiltin_result {b : BuiltinFun} (hb : integerBuiltin b = true)
    {vs : List CekValue} {v : CekValue} (hlen : vs.length = valueArity (expectedArgs b))
    (h : evalBuiltin b vs = some v) : IntegerValue v := by
  have np : b ≠ .IfThenElse ∧ b ≠ .ChooseUnit ∧ b ≠ .Trace ∧ b ≠ .ChooseData ∧
      b ≠ .ChooseList ∧ b ≠ .MkCons := by
    cases b <;> simp [integerBuiltin] at hb <;> decide
  obtain ⟨cs, c, hcs, hc, rfl⟩ := evalBuiltin_const np h
  rw [← hcs] at hlen
  suffices ∃ x, c = .Integer x by obtain ⟨x, rfl⟩ := this; exact ⟨x, rfl⟩
  cases b <;> simp [integerBuiltin] at hb <;> simp [expectedArgs, valueArity] at hlen
  all_goals
    rcases cs with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, rest⟩⟩⟩⟩ <;> simp at hlen
  all_goals first
    | (cases hc; done)
    | (cases x <;> (try cases hc) <;> exact ⟨_, rfl⟩)
    | (cases x <;> (try cases hc) <;> cases y <;> (try cases hc) <;> exact ⟨_, rfl⟩)
    | (cases x <;> (try cases hc) <;> rename_i d <;> cases d <;> (try cases hc) <;> exact ⟨_, rfl⟩)
    | (cases x <;> (try cases hc) <;> cases y <;> (try cases hc)
       all_goals
         first
           | (obtain rfl := eq_of_ite_some hc; exact ⟨_, rfl⟩)
           | (have hc' := hc
              change (if _ then _ else none) = some c at hc'
              split at hc'
              · first | (cases hc'; exact ⟨_, rfl⟩) | (obtain rfl := eq_of_ite_some hc'; exact ⟨_, rfl⟩)
              · cases hc'))

theorem evalBuiltin_single {b : BuiltinFun} {w v : CekValue}
    (hb : b ≠ .IfThenElse ∧ b ≠ .ChooseUnit ∧ b ≠ .Trace ∧ b ≠ .ChooseData ∧
      b ≠ .ChooseList ∧ b ≠ .MkCons)
    (h : evalBuiltin b [w] = some v) :
    ∃ c r, w = .VCon c ∧ evalBuiltinConst b [c] = some r ∧ v = .VCon r := by
  simp only [evalBuiltin, evalBuiltinPassThrough_none_of_not_passthrough b _ hb] at h
  cases w with
  | VCon c =>
    change (match evalBuiltinConst b [c] with
      | some c => some (CekValue.VCon c) | none => none) = some v at h
    cases he : evalBuiltinConst b [c] with
    | none => rw [he] at h; cases h
    | some r => rw [he] at h; cases h; exact ⟨c, r, rfl, he, rfl⟩
  | _ => simp [extractConsts] at h

omit sv in
theorem single_of_length {α : Type} {xs : List α} (h : xs.length = 1) : ∃ x, xs = [x] := by
  match xs, h with
  | [x], _ => exact ⟨x, rfl⟩

theorem unConstrData_result {vs : List CekValue} {v : CekValue} (hlen : vs.length = 1)
    (h : evalBuiltin .UnConstrData vs = some v) : PairValue v := by
  obtain ⟨w, rfl⟩ := single_of_length hlen
  obtain ⟨c, r, rfl, hc, rfl⟩ := evalBuiltin_single (by decide) h
  cases c <;> (try cases hc)
  rename_i d
  cases d <;> cases hc
  exact ⟨_, _, rfl⟩

theorem unListData_result {vs : List CekValue} {v : CekValue} (hlen : vs.length = 1)
    (h : evalBuiltin .UnListData vs = some v) : ListValue v := by
  obtain ⟨w, rfl⟩ := single_of_length hlen
  obtain ⟨c, r, rfl, hc, rfl⟩ := evalBuiltin_single (by decide) h
  cases c <;> (try cases hc)
  rename_i d
  cases d <;> cases hc
  trivial

theorem tailList_result {vs : List CekValue} {v : CekValue} (hlen : vs.length = 1)
    (h : evalBuiltin .TailList vs = some v) : ListValue v := by
  obtain ⟨w, rfl⟩ := single_of_length hlen
  obtain ⟨c, r, rfl, hc, rfl⟩ := evalBuiltin_single (by decide) h
  cases c <;> (try cases hc)
  all_goals (rename_i l; cases l <;> cases hc; trivial)

theorem sndPair_result {vs : List CekValue} {v : CekValue} (hlen : vs.length = 1)
    (hpair : ∀ w ∈ vs, PairValue w) (h : evalBuiltin .SndPair vs = some v) : ListValue v := by
  obtain ⟨w, rfl⟩ := single_of_length hlen
  obtain ⟨i, fields, rfl⟩ := hpair w (.head _)
  obtain ⟨c, r, hc', hc, rfl⟩ := evalBuiltin_single (by decide) h
  cases hc'
  cases hc
  trivial

theorem fstPair_result {vs : List CekValue} {v : CekValue} (hlen : vs.length = 1)
    (hpair : ∀ w ∈ vs, PairValue w) (h : evalBuiltin .FstPair vs = some v) : IntegerValue v := by
  obtain ⟨w, rfl⟩ := single_of_length hlen
  obtain ⟨i, fields, rfl⟩ := hpair w (.head _)
  obtain ⟨c, r, hc', hc, rfl⟩ := evalBuiltin_single (by decide) h
  cases hc'
  cases hc
  exact ⟨i, rfl⟩

end Moist.Verified.ShapeFacts
