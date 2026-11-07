import Moist.MIR.Optimize.Advanced.Shapes

namespace Moist.MIR.Advanced

/-! Constructor-tag test chains as integer cases.

A match on `@[plutus_data]` constructors tests the tag with a chain of
`equalsInteger tag c` Boolean cases. When the tag is a known integer, the
tests become one integer `case`:

* `case (tag = c) [error, A]` becomes `case tag [error, …, error, A]` (`A` at
  index `c`). An integer case selects alternative `n` for `0 ≤ n` below the
  number of alternatives and fails otherwise, exactly like the error default.
* `case (tag = c) [case tag alts, A]` puts `A` at index `c` of `alts`,
  padding with `error`. The outer test runs first, so it wins over an inner
  alternative for the same tag.
* A chain whose tests all fail (`case (tag = c) [next, error]`) for a
  contiguous range of at least three tags becomes the two comparisons
  `case (case (lo ≤ tag) [False, tag ≤ hi]) [rest, error]`. An integer case is
  not used there: it would also fail for tags outside the range.

Chains are rewritten bottom-up, so the innermost test with the error default
starts the integer case and every enclosing test of the same tag joins it.
A test bound by a single-use `let` directly before the case that consumes it
is moved into the case scrutinee first; the binding is evaluated at the same
point either way. An application `T y` of a tree `T` of Boolean or integer
cases to a variable is pushed into the leaves when the pushed tree becomes an
integer case: the scrutinees carry no fields, so each leaf is applied to `y`
after the same selection, and `error y` and `(λx. error) y` fail. Bindings of
tag tests and of partially applied integer builtins that become unused are
dropped: both return without failing on known integers. -/

open Moist.Plutus.Term

/-- `equalsInteger tag c` (either argument order, through aliases) with `tag`
    a known integer variable. -/
def tagTest (environment : List (VarId × Expr)) (scrutinee : Expr) : Option (VarId × Int) :=
  match resolveHead 64 environment scrutinee with
  | .App (.App (.Builtin .EqualsInteger) (.Var subject)) (.Lit (.Integer value, _)) =>
    if knownInteger 64 environment (.Var subject) then some (subject, value) else none
  | .App (.App (.Builtin .EqualsInteger) (.Lit (.Integer value, _))) (.Var subject) =>
    if knownInteger 64 environment (.Var subject) then some (subject, value) else none
  | _ => none

/-- Largest number of error alternatives added in front of a tag. -/
def tagCaseGap : Nat := 16

def errorAlternatives (count : Nat) : List Expr := List.replicate count .Error

/-- `alternatives` with `alternative` at `index`, padding with `error`. -/
def placeAlternative (alternatives : List Expr) (index : Nat) (alternative : Expr) : List Expr :=
  if index < alternatives.length then alternatives.set index alternative
  else alternatives ++ errorAlternatives (index - alternatives.length) ++ [alternative]

def lessEqualInteger (left right : Expr) : Expr :=
  .App (.App (.Builtin .LessThanEqualsInteger) left) right

/-- `case (case (low ≤ subject) [False, subject ≤ high]) [outside, error]`. -/
def rangeCase (subject : VarId) (low high : Int) (outside : Expr) : Expr :=
  .Case (.Case (lessEqualInteger (.Lit (.Integer low, .AtomicType .TypeInteger)) (.Var subject))
      [.Lit (.Bool false, .AtomicType .TypeBool),
       lessEqualInteger (.Var subject) (.Lit (.Integer high, .AtomicType .TypeInteger))])
    [outside, .Error]

/-- Recognizes a `rangeCase` on `subject`. -/
def rangeOf (subject : VarId) (expression : Expr) : Option (Int × Int × Expr) :=
  match expression with
  | .Case (.Case (.App (.App (.Builtin .LessThanEqualsInteger) (.Lit (.Integer low, _))) (.Var first))
      [.Lit (.Bool false, _),
       .App (.App (.Builtin .LessThanEqualsInteger) (.Var second)) (.Lit (.Integer high, _))])
      [outside, .Error] =>
    if first == subject && second == subject then some (low, high, outside) else none
  | _ => none

/-- The tags of a chain of failing tests of `subject`, and what follows them. -/
def errorSpine (environment : List (VarId × Expr)) (subject : VarId) (expression : Expr) :
    List Int × Expr :=
  match expression with
  | .Case scrutinee [next, .Error] =>
    match tagTest environment scrutinee with
    | some (tested, value) =>
      if tested == subject then
        let rest := errorSpine environment subject next
        (value :: rest.1, rest.2)
      else ([], expression)
    | none => ([], expression)
  | _ => ([], expression)
termination_by exprSize expression
decreasing_by simp only [exprSize, exprSizeList]; omega

def coversRange (values : List Int) (low high : Int) : Bool :=
  (List.range (high - low + 1).toNat).all fun offset => values.contains (low + offset)

/-- Failing tests of a contiguous range of at least three tags. -/
def rangeRule (environment : List (VarId × Expr)) (subject : VarId) (value : Int)
    (otherwise : Expr) : Option Expr :=
  match rangeOf subject otherwise with
  | some (low, high, outside) =>
    if low ≤ value + 1 && value ≤ high + 1 then
      some (rangeCase subject (min low value) (max high value) outside)
    else none
  | none =>
    let spine := errorSpine environment subject otherwise
    let low := spine.1.foldl min value
    let high := spine.1.foldl max value
    if 2 ≤ high - low && coversRange (value :: spine.1) low high then
      some (rangeCase subject low high spine.2)
    else none

/-- A test whose default fails, or which joins an integer case of its tag. -/
def integerCaseRule (subject : VarId) (value : Int) (otherwise matched : Expr) : Option Expr :=
  if value < 0 then none
  else
    match otherwise with
    | .Error =>
      if value.toNat ≤ tagCaseGap then
        some (.Case (.Var subject) (placeAlternative [] value.toNat matched))
      else none
    | .Case (.Var tested) alternatives =>
      if tested == subject && value.toNat ≤ alternatives.length + tagCaseGap then
        some (.Case (.Var subject) (placeAlternative alternatives value.toNat matched))
      else none
    | _ => none

def tagCaseRule (environment : List (VarId × Expr)) (scrutinee : Expr)
    (alternatives : List Expr) : Option Expr :=
  match alternatives with
  | [otherwise, matched] =>
    match tagTest environment scrutinee with
    | some (subject, value) =>
      match integerCaseRule subject value otherwise matched with
      | some result => some result
      | none =>
        match matched with
        | .Error => rangeRule environment subject value otherwise
        | _ => none
    | none => none
  | _ => none

/-- Scrutinees whose values carry no fields. -/
def fieldlessScrutinee (environment : List (VarId × Expr)) (scrutinee : Expr) : Bool :=
  knownBooleanLocal 64 environment scrutinee || knownInteger 64 environment scrutinee

/-- Apply every leaf of a tree of field-less cases to `argument`. -/
def pushArgument (environment : List (VarId × Expr)) (argument : VarId) (expression : Expr) :
    Expr :=
  match expression with
  | .Case scrutinee alternatives =>
    if fieldlessScrutinee environment scrutinee then
      let pushed := alternatives.attach.map fun ⟨alternative, _⟩ =>
        pushArgument environment argument alternative
      (tagCaseRule environment scrutinee pushed).getD (.Case scrutinee pushed)
    else .App expression (.Var argument)
  | .Error => .Error
  | .Lam _ .Error => .Error
  | _ => .App expression (.Var argument)
termination_by exprSize expression
decreasing_by have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega

def isTagCase : Expr → Bool
  | .Case (.Var _) _ => true
  | .Case (.Case (.App (.App (.Builtin .LessThanEqualsInteger) _) _) _) [_, .Error] => true
  | _ => false

def tagApplication (environment : List (VarId × Expr)) (function argument : Expr) : Expr :=
  match function, argument with
  | .Case _ _, .Var argumentBinder =>
    let pushed := pushArgument environment argumentBinder function
    if isTagCase pushed then pushed else .App function argument
  | _, _ => .App function argument

/-- A partially applied two-argument integer builtin, or a tag test: both
    return without failing. -/
def tagReturns (environment : List (VarId × Expr)) (expression : Expr) : Bool :=
  (tagTest environment expression).isSome ||
    match expression with
    | .App function argument =>
      match resolveHead 64 environment function with
      | .Builtin builtin =>
        (builtin == .EqualsInteger || builtin == .LessThanInteger ||
          builtin == .LessThanEqualsInteger) &&
        match argument with
        | .Var _ | .Lit _ => true
        | _ => false
      | _ => false
    | _ => false

/-- Drop a binding that the body ignores and whose right-hand side returns. -/
def dropTagBinding (environment : List (VarId × Expr)) (binder : VarId) (rhs : Expr)
    (erased : Bool) (body : Expr) : Expr :=
  if !(freeVars body).contains binder && tagReturns environment rhs then body
  else .Let [(binder, rhs, erased)] body

def tagBinding (environment : List (VarId × Expr)) (binder : VarId) (rhs : Expr) (erased : Bool)
    (body : Expr) : Expr :=
  match body with
  | .Case (.Var scrutinee) alternatives =>
    if scrutinee == binder && !(freeVarsList alternatives).contains binder &&
        (tagTest environment rhs).isSome then
      (tagCaseRule environment rhs alternatives).getD (.Case rhs alternatives)
    else dropTagBinding environment binder rhs erased body
  | .App (.Var function) (.Var argument) =>
    if function == binder && !(argument == binder) then
      match rhs with
      | .Case _ _ =>
        if isTagCase (pushArgument environment argument rhs) then pushArgument environment argument rhs
        else dropTagBinding environment binder rhs erased body
      | _ => dropTagBinding environment binder rhs erased body
    else dropTagBinding environment binder rhs erased body
  | _ => dropTagBinding environment binder rhs erased body

def tagChainWalk (environment : List (VarId × Expr)) (expression : Expr) : Expr :=
  match expression with
  | .Case scrutinee alternatives =>
    let scrutinee' := tagChainWalk environment scrutinee
    let alternatives' := alternatives.attach.map fun ⟨alternative, _⟩ =>
      tagChainWalk environment alternative
    (tagCaseRule environment scrutinee' alternatives').getD (.Case scrutinee' alternatives')
  | .App function argument =>
    tagApplication environment (tagChainWalk environment function)
      (tagChainWalk environment argument)
  | .Let [] body => tagChainWalk environment body
  | .Let ((binder, rhs, erased) :: rest) body =>
    tagBinding environment binder (tagChainWalk environment rhs) erased
      (tagChainWalk ((binder, rhs) :: environment) (.Let rest body))
  | .Lam binder body => .Lam binder (tagChainWalk environment body)
  | .Fix binder body => .Fix binder (tagChainWalk environment body)
  | .Force body => .Force (tagChainWalk environment body)
  | .Delay body => .Delay (tagChainWalk environment body)
  | .Constr tag fields =>
    .Constr tag (fields.attach.map fun ⟨field, _⟩ => tagChainWalk environment field)
  | .Var _ | .Lit _ | .Builtin _ | .Error => expression
termination_by exprSize expression
decreasing_by
  all_goals first
    | (simp only [exprSize, exprSizeBinds]; omega)
    | (simp only [exprSize, exprSizeBinds]; have := exprSize_pos rhs; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)

def caseTagChains (expression : Expr) : Expr :=
  let unique := uniqueOptimizationBinders expression
  if wellScoped unique then tagChainWalk [] unique else unique

end Moist.MIR.Advanced
