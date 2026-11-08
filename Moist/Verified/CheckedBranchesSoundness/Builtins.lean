import Moist.Verified.ShapesSoundness.Choices

variable [sv : Moist.CEK.SemVariant]

/-! # List discriminators on runtime values

`chooseList` and `nullList` accept exactly the same values: both reject every
value that is not a list constant (of any element type), and on a list `chooseList` returns
its second argument when `nullList` says the list is empty.
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term

/-- Non-empty list constants. -/
def NonemptyList : CekValue → Prop
  | .VCon (.ConstList _ (_ :: _)) => True
  | _ => False

/-- The result of `chooseList` on a value: `none` for non-lists. -/
def chooseResult (cons nil : CekValue) : CekValue → Option CekValue
  | .VCon (.ConstList _ l) => some (if l.isEmpty then nil else cons)
  | _ => none

/-- The result of `nullList` on a value: `none` for non-lists. -/
def nullResult : CekValue → Option Bool
  | .VCon (.ConstList _ l) => some l.isEmpty
  | _ => none

theorem chooseList_eval (d : Term) (ρ : CekEnv) (nil vl : CekValue) :
    evalBuiltin .ChooseList [.VDelay d ρ, nil, vl] = chooseResult (.VDelay d ρ) nil vl := by
  cases vl with
  | VCon c =>
    cases c <;> simp [evalBuiltin, evalBuiltinPassThrough, extractConsts, chooseResult]
  | _ => simp [evalBuiltin, evalBuiltinPassThrough, extractConsts, chooseResult]

theorem nullList_eval (vl : CekValue) :
    evalBuiltin .NullList [vl] = (nullResult vl).map fun b => .VCon (.Bool b) := by
  cases vl with
  | VCon c =>
    cases c <;> rfl
  | _ => rfl

omit sv in
theorem chooseResult_of_null {cons nil vl : CekValue} {b : Bool} (h : nullResult vl = some b) :
    chooseResult cons nil vl = some (if b then nil else cons) := by
  cases vl with
  | VCon c =>
    cases c <;> simp_all [nullResult, chooseResult]
  | _ => simp [nullResult] at h

omit sv in
theorem chooseResult_none {cons nil vl : CekValue} (h : nullResult vl = none) :
    chooseResult cons nil vl = none := by
  cases vl with
  | VCon c =>
    cases c <;> simp_all [nullResult, chooseResult]
  | _ => rfl

omit sv in
theorem nonempty_of_null {vl : CekValue} (h : nullResult vl = some false) : NonemptyList vl := by
  cases vl with
  | VCon c =>
    cases c with
    | ConstList _ l => cases l <;> simp_all [nullResult, NonemptyList]
    | _ => simp [nullResult] at h
  | _ => simp [nullResult] at h

end Moist.Verified.ShapeFacts
