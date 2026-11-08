import Moist.Verified.ShapesSoundness.Choices

variable [sv : Moist.CEK.SemVariant]

/-! # List discriminators on runtime values

`chooseList` and `nullList` accept exactly the same values: both reject every
value that is not a (plain, data or data-pair) list, and on a list `chooseList` returns
its second argument when `nullList` says the list is empty.
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term

/-- Non-empty plain, data or data-pair lists. -/
def NonemptyList : CekValue → Prop
  | .VCon (.ConstList (_ :: _)) => True
  | .VCon (.ConstDataList (_ :: _)) => True
  | .VCon (.ConstPairDataList (_ :: _)) => True
  | _ => False

/-- The result of `chooseList` on a value: `none` for non-lists. -/
def chooseResult (cons nil : CekValue) : CekValue → Option CekValue
  | .VCon (.ConstList l) => some (if l.isEmpty then nil else cons)
  | .VCon (.ConstDataList l) => some (if l.isEmpty then nil else cons)
  | .VCon (.ConstPairDataList l) => some (if l.isEmpty then nil else cons)
  | _ => none

/-- The result of `nullList` on a value: `none` for non-lists. -/
def nullResult : CekValue → Option Bool
  | .VCon (.ConstList l) => some l.isEmpty
  | .VCon (.ConstDataList l) => some l.isEmpty
  | .VCon (.ConstPairDataList l) => some l.isEmpty
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

theorem chooseResult_of_null {cons nil vl : CekValue} {b : Bool} (h : nullResult vl = some b) :
    chooseResult cons nil vl = some (if b then nil else cons) := by
  cases vl with
  | VCon c =>
    cases c <;> simp_all [nullResult, chooseResult]
  | _ => simp [nullResult] at h

theorem chooseResult_none {cons nil vl : CekValue} (h : nullResult vl = none) :
    chooseResult cons nil vl = none := by
  cases vl with
  | VCon c =>
    cases c <;> simp_all [nullResult, chooseResult]
  | _ => rfl

theorem nonempty_of_null {vl : CekValue} (h : nullResult vl = some false) : NonemptyList vl := by
  cases vl with
  | VCon c =>
    cases c with
    | ConstList l => cases l <;> simp_all [nullResult, NonemptyList]
    | ConstDataList l => cases l <;> simp_all [nullResult, NonemptyList]
    | ConstPairDataList l => cases l <;> simp_all [nullResult, NonemptyList]
    | _ => simp [nullResult] at h
  | _ => simp [nullResult] at h

end Moist.Verified.ShapeFacts
