import Moist.MIR.Optimize.Advanced.Sharing
import Moist.MIR.LowerTotal
import Moist.Plutus.Encode
import Std.Data.HashMap

namespace Moist.MIR.Advanced

/-! # Sharing closed values at their lowest dominating node

`shareLow` binds repeated closed subterms once, at the deepest node that
encloses every occurrence and that runs at most once per run, instead of at the
top of the program. Candidates are closed values (lambdas, including case
alternatives, delays and lifted Z-combinator fixed points, or else their
functionals), constants of at least 32 bytes and forced builtins with at least
three uses. Unforced builtins are never shared: a variable is not smaller.

Placement descends through let right-hand sides and bodies, application
functions and arguments, `force`, constructor fields, case scrutinees, the
bodies of case alternatives below their field lambdas and the branches of a
lazy `ifThenElse`. It never enters another lambda body or `delay`, which may
run many times. The parameters of the script are bound once, so its body is the
root placement node.

Per-run cost: a binding adds two machine steps plus the evaluation of its
right-hand side on every path through its node. A use saves the evaluation
steps of the term minus one variable lookup: one step for a forced builtin,
two for a doubly forced one, seven for a fixed point, none for lambdas, delays
and constants. `chooseBindings` keeps a binding only while `planNet`, a lower
bound on the steps saved over every successful run, stays non-negative, so no
successful run gets slower.

The plan is a heuristic. `placeShared` applies `shareClosed`'s binding step at
the planned nodes only, and it binds only closed terms that evaluate to a value
without failing, so every plan is sound (`placeShared_refines`).
-/

open Moist.Plutus.Term

/-- The lifted Z combinator `[(λz [z z]) (λs λx. e)]`. -/
def isFixValue : Expr → Bool
  | .Let [(z, .Lam _ (.Lam _ _), _)] (.App (.Var a) (.Var b)) => a == z && b == z
  | _ => false

def isValueCandidate : Expr → Bool
  | .Lam _ _ | .Delay _ => true
  | expression => isFixValue expression

def isClosedExpr (expression : Expr) : Bool := (freeVars expression).data.isEmpty

def isLitExpr : Expr → Bool
  | .Lit _ => true
  | _ => false

/-- Closed terms that evaluate to a value without failing. -/
def isShareable (expression : Expr) : Bool :=
  isClosedExpr expression &&
    (isValueCandidate expression || isLitExpr expression ||
      (builtinRemainder expression).isSome)

/-! ## Placement -/

/-- Rebuild the field lambdas of a case alternative around a transformed body. -/
def mapPeeled (transform : Expr → Expr) : Expr → Expr
  | .Lam binder body => .Lam binder (mapPeeled transform body)
  | expression => transform expression

/-- Transform the children of a node; child `i` of a case is alternative
    `i - 1` below its field lambdas, child `n` of a let with `n` bindings is
    its body. The planner never places a binding in a lambda body, and in a
    `delay` only for the branches of a lazy conditional. -/
def descendPlaced (transform : Nat → Expr → Expr) : Expr → Expr
  | .Lam binder body => .Lam binder (transform 0 body)
  | .Delay inner => .Delay (transform 0 inner)
  | .App function argument => .App (transform 0 function) (transform 1 argument)
  | .Force inner => .Force (transform 0 inner)
  | .Constr tag fields => .Constr tag (fields.mapIdx transform)
  | .Case scrutinee alternatives =>
    .Case (transform 0 scrutinee)
      (alternatives.mapIdx fun index alternative => mapPeeled (transform (index + 1)) alternative)
  | .Let bindings body =>
    .Let (bindings.mapIdx fun index (binder, rhs, erased) => (binder, transform index rhs, erased))
      (transform bindings.length body)
  | expression => expression

/-- A placement plan: paths of child indices from the current node, each
    with a representative of the terms to bind there. -/
abbrev Plan := List (List Nat × Expr)

def Plan.here (plan : Plan) : List Expr :=
  plan.filterMap fun (path, candidate) => if path.isEmpty then some candidate else none

def Plan.child (plan : Plan) (index : Nat) : Plan :=
  plan.filterMap fun (path, candidate) => match path with
    | next :: rest => if next == index then some (rest, candidate) else none
    | [] => none

/-- Bind the planned candidates at the planned nodes. -/
def placeShared : Nat → Plan → Expr → Expr
  | 0, _, expression => expression
  | fuel + 1, plan, expression =>
    if plan.isEmpty then expression else
    let here := plan.here
    let replacements := shareReplacements
      (fun candidate => here.any (fun planned => alphaEq planned candidate) && isShareable candidate)
      2 expression
    let replaced := if replacements.isEmpty then expression
      else replaceMatches replacements expression
    let body := descendPlaced (fun index => placeShared fuel (plan.child index)) replaced
    if replacements.isEmpty then body
    else .Let (replacements.map fun (rhs, binder) => (binder, rhs, false)) body

/-! ## Planning -/

/-- What a planning round shares. -/
inductive ShareRound where
  | values
  | constants
  | builtins
  deriving BEq, Repr

structure LowOptions where
  /-- Smallest flat size of a pooled constant, in bytes. -/
  minimumConstantBytes : Nat := 32
  /-- Smallest number of occurrences of a shared forced builtin. -/
  minimumBuiltinUses : Nat := 3
  /-- Smallest size saving of a shared term, in bits. -/
  minimumSavingBits : Nat := 1
  /-- Share closed lambdas, delays and fixed points. -/
  values : Bool := true
  /-- Share constants of at least `minimumConstantBytes`. -/
  constants : Bool := true
  /-- Share forced builtin states. -/
  builtins : Bool := true
  /-- Keep only bindings that make no successful run slower. -/
  guardPaths : Bool := true
  /-- Steps a successful run may lose to the bindings. -/
  slackSteps : Int := 0
  deriving Repr

def literalBytes (literal : Const × BuiltinType) : Nat :=
  (Moist.Plutus.Encode.encode_program
    (.Program (.Version 1 1 0) (.Constant literal))).toByteList.length

def isForcedBuiltin : Expr → Bool
  | expression@(.Force _) => (builtinRemainder expression).isSome
  | _ => false

def roundAccepts (options : LowOptions) : ShareRound → Expr → Bool
  | .values, expression => isValueCandidate expression
  | .constants, .Lit literal => literalBytes literal >= options.minimumConstantBytes
  | .builtins, expression => isForcedBuiltin expression
  | _, _ => false

/-- The lazy conditional `force [[[ifThenElse c] (delay t)] (delay f)]`. -/
def lazyConditional : Expr → Option (Expr × Expr × Expr × Expr)
  | .Force (.App (.App (.App head condition) (.Delay onTrue)) (.Delay onFalse)) =>
    match head with
    | .Force (.Builtin .IfThenElse) => some (head, condition, onTrue, onFalse)
    | _ => none
  | _ => none

/-- An occurrence and the reversed path of the deepest placement node above
    or at it. -/
structure Occurrence where
  term : Expr
  place : List Nat

mutual
  /-- Occurrences of accepted closed terms, outermost first as in
      `collectMatches`. `path` is the reversed path of the current node,
      `place` that of the deepest placement node seen so far, and `allowed`
      whether the current node is a placement node. `peeled` marks the field
      lambdas of a case alternative, which are not placement nodes; the body
      below them is. `fuel` bounds the depth; `exprSize` is enough. -/
  def collectOccurrences (fuel : Nat) (accept : Expr → Bool) (path place : List Nat)
      (allowed peeled : Bool) (expression : Expr) (found : Array Occurrence) :
      Array Occurrence :=
    match fuel with
    | 0 => found
    | fuel + 1 =>
    let hit := accept expression && isClosedExpr expression
    let peeledLambda := peeled && match expression with
      | .Lam _ _ => true
      | _ => false
    if peeledLambda then
      match expression with
      | .Lam _ body =>
        if hit then found.push ⟨expression, place⟩
        else collectOccurrences fuel accept path place allowed true body found
      | _ => found
    else
    let place := if allowed then path else place
    if hit then found.push ⟨expression, place⟩
    else match expression with
      | .Lam _ body | .Delay body | .Fix _ body =>
        collectOccurrences fuel accept (0 :: path) place false false body found
      | .Force inner =>
        match lazyConditional expression with
        | some parts => collectConditional fuel accept path place allowed parts found
        | none => collectOccurrences fuel accept (0 :: path) place allowed false inner found
      | .App function argument =>
        collectOccurrences fuel accept (1 :: path) place allowed false argument
          (collectOccurrences fuel accept (0 :: path) place allowed false function found)
      | .Constr _ fields => collectOccurrencesList fuel accept path place allowed 0 fields found
      | .Case scrutinee alternatives =>
        collectAlternatives fuel accept path place allowed 1 alternatives
          (collectOccurrences fuel accept (0 :: path) place allowed false scrutinee found)
      | .Let bindings body =>
        collectOccurrences fuel accept (bindings.length :: path) place allowed false body
          (collectOccurrencesBinds fuel accept path place allowed 0 bindings found)
      | _ => found

  /-- `force [[[head c] (delay t)] (delay f)]`: the branch bodies run at most
      once, so they are placement nodes. -/
  def collectConditional (fuel : Nat) (accept : Expr → Bool) (path place : List Nat)
      (allowed : Bool) (parts : Expr × Expr × Expr × Expr) (found : Array Occurrence) :
      Array Occurrence :=
    match fuel with
    | 0 => found
    | fuel + 1 =>
      let app3 := 0 :: path
      let app2 := 0 :: app3
      let app1 := 0 :: app2
      let inner := if allowed then app1 else place
      collectOccurrences fuel accept (0 :: 1 :: app3) inner allowed false parts.2.2.2
        (collectOccurrences fuel accept (0 :: 1 :: app2) inner allowed false parts.2.2.1
          (collectOccurrences fuel accept (1 :: app1) inner allowed false parts.2.1
            (collectOccurrences fuel accept (0 :: app1) inner allowed false parts.1 found)))

  def collectOccurrencesList (fuel : Nat) (accept : Expr → Bool) (path place : List Nat)
      (allowed : Bool) (index : Nat) (expressions : List Expr) (found : Array Occurrence) :
      Array Occurrence :=
    match fuel with
    | 0 => found
    | fuel + 1 =>
      match expressions with
      | [] => found
      | expression :: rest =>
        collectOccurrencesList fuel accept path place allowed (index + 1) rest
          (collectOccurrences fuel accept (index :: path) place allowed false expression found)

  def collectOccurrencesBinds (fuel : Nat) (accept : Expr → Bool) (path place : List Nat)
      (allowed : Bool) (index : Nat) (bindings : List (VarId × Expr × Bool))
      (found : Array Occurrence) : Array Occurrence :=
    match fuel with
    | 0 => found
    | fuel + 1 =>
      match bindings with
      | [] => found
      | (_, rhs, _) :: rest =>
        collectOccurrencesBinds fuel accept path place allowed (index + 1) rest
          (collectOccurrences fuel accept (index :: path) place allowed false rhs found)

  def collectAlternatives (fuel : Nat) (accept : Expr → Bool) (path place : List Nat)
      (allowed : Bool) (index : Nat) (alternatives : List Expr) (found : Array Occurrence) :
      Array Occurrence :=
    match fuel with
    | 0 => found
    | fuel + 1 =>
      match alternatives with
      | [] => found
      | alternative :: rest =>
        collectAlternatives fuel accept path place allowed (index + 1) rest
          (collectOccurrences fuel accept (index :: path) (if allowed then path else place)
            allowed true alternative found)
end

/-- Occurrences in a whole expression. -/
def occurrencesOf (accept : Expr → Bool) (expression : Expr) : Array Occurrence :=
  collectOccurrences (2 * exprSize expression + 2) accept [] [] true false expression #[]


/-- Flat size of a closed term, in bits. -/
def closedBits (expression : Expr) : Nat :=
  match lowerTotalExpr [] expression with
  | some term => (Moist.Plutus.Encode.ℰ_term Moist.Plutus.BitBuffer.empty term).length
  | none => 0

structure Group where
  representative : Expr
  places : List (List Nat)
  deriving Inhabited

/-- Group alpha-equivalent occurrences. -/
def groupOccurrences (occurrences : Array Occurrence) : Array Group := Id.run do
  let mut buckets : Std.HashMap Nat (Array Nat) := {}
  let mut groups : Array Group := #[]
  for occurrence in occurrences do
    let key := exprSize occurrence.term
    let bucket := buckets.getD key #[]
    match bucket.find? (fun index => alphaEq groups[index]!.representative occurrence.term) with
    | some index =>
      groups := groups.modify index fun group =>
        { group with places := occurrence.place :: group.places }
    | none =>
      buckets := buckets.insert key (bucket.push groups.size)
      groups := groups.push ⟨occurrence.term, [occurrence.place]⟩
  return groups

def commonPrefix : List Nat → List Nat → List Nat
  | first :: rest, other :: more => if first == other then first :: commonPrefix rest more else []
  | _, _ => []

/-- The deepest placement node enclosing every occurrence. -/
def lowestPlace (places : List (List Nat)) : List Nat :=
  match places.map List.reverse with
  | [] => []
  | first :: rest => rest.foldl commonPrefix first

/-- Machine steps saved by each run of a use of a shared term. -/
def stepsSavedPerUse : Expr → Nat
  | .Force (.Force _) => 2
  | .Force _ => 1
  | expression => if isFixValue expression then 7 else 0

/-- Machine steps of a binding: application, binder, value. -/
def bindingSteps (candidate : Expr) : Nat := 3 + stepsSavedPerUse candidate

/-! ## Path costs

A plan changes the machine steps of a run by the steps saved at each use that
runs, minus the steps of each binding that runs. `pathNet` bounds this change
from below over every successful run, so a plan whose bound is not negative
makes no successful run slower. Failing runs are not bounded: they stop with an
error, and the benchmark charges their machine steps only in blocks of 200.

Results are split by the Boolean literal a run returns, so that a case or a
lazy `ifThenElse` on a Boolean only continues paths that select the branch.
A call of a known lambda or fixed point with enough arguments runs its body
once; any other lambda or delay body counts as not running. -/

structure PathNet where
  onFalse : Option Int := none
  onTrue : Option Int := none
  other : Option Int := none
  deriving Inhabited

def minOption : Option Int → Option Int → Option Int
  | some first, some second => some (min first second)
  | some first, none => some first
  | none, second => second

namespace PathNet

def value (net : Int) : PathNet := { other := some net }

def shift (offset : Int) (paths : PathNet) : PathNet :=
  { onFalse := paths.onFalse.map (· + offset), onTrue := paths.onTrue.map (· + offset),
    other := paths.other.map (· + offset) }

def least (paths : PathNet) : Option Int :=
  minOption paths.onFalse (minOption paths.onTrue paths.other)

def seq (first second : PathNet) : PathNet :=
  match first.least with
  | some net => second.shift net
  | none => {}

def branch (first second : PathNet) : PathNet :=
  { onFalse := minOption first.onFalse second.onFalse,
    onTrue := minOption first.onTrue second.onTrue,
    other := minOption first.other second.other }

/-- Select `onFalse`/`onTrue` by the Boolean result of `scrutinee`; any other
    result may select either. -/
def select (scrutinee onFalse onTrue : PathNet) : PathNet :=
  let falsePaths := match scrutinee.onFalse with
    | some net => onFalse.shift net
    | none => {}
  let truePaths := match scrutinee.onTrue with
    | some net => onTrue.shift net
    | none => {}
  let otherPaths := match scrutinee.other with
    | some net => (branch onFalse onTrue).shift net
    | none => {}
  branch falsePaths (branch truePaths otherPaths)

end PathNet

/-- Known functions: binder, number of parameters, paths of one call. -/
abbrev Known := List (VarId × Nat × PathNet)

def lambdaArity : Expr → Nat
  | .Lam _ body => lambdaArity body + 1
  | _ => 0

def lambdaBody : Expr → Expr
  | .Lam _ body => lambdaBody body
  | expression => expression

/-- Parameters and body of a lambda or lifted fixed point. -/
def functionShape : Expr → Option (Nat × Expr)
  | .Let [(_, .Lam _ (.Lam parameter body), _)] (.App (.Var _) (.Var _)) =>
    some (lambdaArity (.Lam parameter body), lambdaBody body)
  | .Lam parameter body => some (lambdaArity (.Lam parameter body), lambdaBody body)
  | _ => none

/-- A planned binding: its node, its term and the steps it saves per use. -/
structure Binding where
  place : List Nat
  term : Expr
  deriving Inhabited

/-- Steps of the bindings planned at the current node. -/
def planCost (plan : Plan) : Int :=
  (plan.here.map fun term => (bindingSteps term : Int)).sum

mutual
  /-- Net steps saved on the paths through `expression`. `plan` holds the
      bindings below the current node, `shared` every planned term. `fuel`
      bounds the depth; `exprSize` is enough. -/
  def pathNet (fuel : Nat) (shared : List Expr) (known : Known) (plan : Plan) (peeled : Bool)
      (expression : Expr) : PathNet :=
    match fuel with
    | 0 => PathNet.value 0
    | fuel + 1 =>
      let cost := planCost plan
      let paths := pathNetNode fuel shared known plan peeled expression
      if cost == 0 then paths else paths.shift (-cost)

  def pathNetNode (fuel : Nat) (shared : List Expr) (known : Known) (plan : Plan) (peeled : Bool)
      (expression : Expr) : PathNet :=
    match fuel with
    | 0 => PathNet.value 0
    | fuel + 1 =>
    if peeled then
      match expression with
      | .Lam _ body => pathNetNode fuel shared known plan true body
      | _ => pathNetNode fuel shared known plan false expression
    else if shared.any (alphaEq · expression) then
      PathNet.value (stepsSavedPerUse expression)
    else match expression with
    | .Error => {}
    | .Lit (.Bool false, _) => { onFalse := some 0 }
    | .Lit (.Bool true, _) => { onTrue := some 0 }
    | .Lam _ _ | .Delay _ | .Fix _ _ | .Lit _ | .Builtin _ | .Var _ => PathNet.value 0
    | .Force inner =>
      match lazyConditional expression with
      | some (head, condition, onTrue, onFalse) =>
        -- force → [[[head c] (delay t)] (delay f)], as `collectOccurrences`
        let app3 := plan.child 0
        let app2 := app3.child 0
        let app1 := app2.child 0
        let delayTrue := app2.child 1
        let delayFalse := app3.child 1
        let start := ((pathNet fuel shared known (app1.child 0) false head).seq
          (pathNet fuel shared known (app1.child 1) false condition)).shift
            (-(planCost app3 + planCost app2 + planCost app1 + planCost delayTrue +
              planCost delayFalse))
        PathNet.select start (pathNet fuel shared known (delayFalse.child 0) false onFalse)
          (pathNet fuel shared known (delayTrue.child 0) false onTrue)
      | none => pathNet fuel shared known (plan.child 0) false inner
    | .App function argument =>
      let (head, arguments) := applicationSpine (.App function argument)
      let paths := ((spineNet fuel shared known (plan.child 0) function).seq
        (pathNet fuel shared known (plan.child 1) false argument))
      paths.seq (callNet fuel shared known head arguments.length)
    | .Constr _ fields => fieldsNet fuel shared known plan 0 (PathNet.value 0) fields
    | .Case scrutinee alternatives =>
      let known' := match scrutinee, alternatives with
        | .Constr _ fields, [alternative] => bindFields fuel shared known fields alternative
        | _, _ => known
      let scrutineePaths := pathNet fuel shared known (plan.child 0) false scrutinee
      let alternativePaths := alternativesNet fuel shared known' plan 1 alternatives
      let called := match scrutinee, alternatives with
        | .Constr _ fields, [.Var function] =>
          callNet fuel shared known (.Var function) fields.length
        | _, _ => PathNet.value 0
      let selected := match alternativePaths with
        | [onFalse, onTrue] => PathNet.select scrutineePaths onFalse onTrue
        | _ => scrutineePaths.seq (alternativePaths.foldl PathNet.branch {})
      selected.seq called
    | .Let bindings body => letNet fuel shared known plan 0 (PathNet.value 0) bindings body

  /-- The function part of an application spine, with the bindings planned at
      its inner application nodes. -/
  def spineNet (fuel : Nat) (shared : List Expr) (known : Known) (plan : Plan)
      (expression : Expr) : PathNet :=
    match fuel with
    | 0 => PathNet.value 0
    | fuel + 1 =>
      match expression with
      | .App function argument =>
        ((spineNet fuel shared known (plan.child 0) function).seq
          (pathNet fuel shared known (plan.child 1) false argument)).shift (-(planCost plan))
      | head => pathNet fuel shared known plan false head

  def fieldsNet (fuel : Nat) (shared : List Expr) (known : Known) (plan : Plan) (index : Nat)
      (paths : PathNet) (fields : List Expr) : PathNet :=
    match fuel with
    | 0 => paths
    | fuel + 1 =>
      match fields with
      | [] => paths
      | field :: rest =>
        fieldsNet fuel shared known plan (index + 1)
          (paths.seq (pathNet fuel shared known (plan.child index) false field)) rest

  def alternativesNet (fuel : Nat) (shared : List Expr) (known : Known) (plan : Plan)
      (index : Nat) (alternatives : List Expr) : List PathNet :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      match alternatives with
      | [] => []
      | alternative :: rest =>
        pathNet fuel shared known (plan.child index) true alternative ::
          alternativesNet fuel shared known plan (index + 1) rest

  def letNet (fuel : Nat) (shared : List Expr) (known : Known) (plan : Plan) (index : Nat)
      (paths : PathNet) (bindings : List (VarId × Expr × Bool)) (body : Expr) : PathNet :=
    match fuel with
    | 0 => paths
    | fuel + 1 =>
      match bindings with
      | [] => paths.seq (pathNet fuel shared known (plan.child index) false body)
      | (binder, rhs, _) :: rest =>
        letNet fuel shared (bindKnown fuel shared known binder rhs) plan (index + 1)
          (paths.seq (pathNet fuel shared known (plan.child index) false rhs)) rest body

  /-- Paths of calling `head` with `count` arguments. -/
  def callNet (fuel : Nat) (shared : List Expr) (known : Known) (head : Expr) (count : Nat) :
      PathNet :=
    match fuel with
    | 0 => PathNet.value 0
    | fuel + 1 =>
      match head with
      | .Var function =>
        match known.find? (·.1 == function) with
        | some (_, arity, paths) => if arity <= count then paths else PathNet.value 0
        | none => PathNet.value 0
      | _ =>
        match functionShape head with
        | some (arity, body) =>
          if arity <= count then pathNet fuel shared known [] false body else PathNet.value 0
        | none => PathNet.value 0

  /-- Record a let-bound function. -/
  def bindKnown (fuel : Nat) (shared : List Expr) (known : Known) (binder : VarId)
      (rhs : Expr) : Known :=
    match fuel with
    | 0 => known
    | fuel + 1 =>
      match functionShape rhs with
      | some (arity, body) => (binder, arity, pathNet fuel shared known [] false body) :: known
      | none => known

  /-- Record functions passed as fields of a packed application. -/
  def bindFields (fuel : Nat) (shared : List Expr) (known : Known) (fields : List Expr)
      (alternative : Expr) : Known :=
    match fuel with
    | 0 => known
    | fuel + 1 =>
      match fields, alternative with
      | field :: rest, .Lam binder body =>
        bindFields fuel shared (bindKnown fuel shared known binder field) rest body
      | _, _ => known
end


/-- The least net steps saved by `bindings` over the successful runs of
    `expression`. -/
def planNet (bindings : List Binding) (expression : Expr) : Int :=
  let plan : Plan := bindings.map fun binding => (binding.place, binding.term)
  ((pathNet (4 * exprSize expression + 4) (bindings.map (·.term)) [] plan false expression).least).getD 0

/-- Every closed accepted subterm, including those nested in others. -/
def allClosed (accept : Expr → Bool) : Expr → Array Expr → Array Expr
  | expression, found =>
    let found := if accept expression && isClosedExpr expression then found.push expression
      else found
    match expression with
    | .Lam _ body | .Delay body | .Fix _ body | .Force body => allClosed accept body found
    | .App function argument => allClosed accept argument (allClosed accept function found)
    | .Constr _ fields => allClosedList accept fields found
    | .Case scrutinee alternatives =>
      allClosedList accept alternatives (allClosed accept scrutinee found)
    | .Let bindings body => allClosed accept body (allClosedBinds accept bindings found)
    | _ => found
where
  allClosedList (accept : Expr → Bool) : List Expr → Array Expr → Array Expr
    | [], found => found
    | expression :: rest, found => allClosedList accept rest (allClosed accept expression found)
  allClosedBinds (accept : Expr → Bool) : List (VarId × Expr × Bool) → Array Expr → Array Expr
    | [], found => found
    | (_, rhs, _) :: rest, found => allClosedBinds accept rest (allClosed accept rhs found)

/-- Representatives of the accepted closed subterms that occur at least twice,
    bucketed by size. -/
def repeatedTerms (accept : Expr → Bool) (expression : Expr) : Std.HashMap Nat (Array Expr) :=
  let groups := groupOccurrences ((allClosed accept expression #[]).map fun term => ⟨term, []⟩)
  groups.foldl (fun buckets group =>
    if group.places.length >= 2 then
      buckets.insert (exprSize group.representative)
        ((buckets.getD (exprSize group.representative) #[]).push group.representative)
    else buckets) {}

/-- A shared term with its lowest placement, its number of maximal uses and
    the flat bits it saves. -/
structure Proposal where
  binding : Binding
  uses : Nat
  savedBits : Int
  deriving Inhabited

def savedBitsOf (term : Expr) (uses : Nat) : Int :=
  let bits : Int := closedBits term
  (bits - 12) * uses - (bits + 8)

/-- The functional `λs λx. e` of a lifted fixed point. -/
def fixFunctional : Expr → Option Expr
  | .Let [(_, functional, _)] _ => some functional
  | _ => none

def proposeRound (options : LowOptions) (round : ShareRound) (expression : Expr) :
    List Proposal :=
  let accept := roundAccepts options round
  let repeated := repeatedTerms accept expression
  let acceptRepeated := fun candidate => accept candidate &&
    ((repeated.getD (exprSize candidate) #[]).any fun term => alphaEq term candidate)
  let occurrences := occurrencesOf acceptRepeated expression
  let groups := groupOccurrences occurrences
  groups.toList.filterMap fun group =>
    let uses := group.places.length
    let minimumUses := if round == .builtins then max 2 options.minimumBuiltinUses else 2
    if uses < minimumUses then none else
    let savedBits := savedBitsOf group.representative uses
    if savedBits < options.minimumSavingBits then none else
    some ⟨⟨lowestPlace group.places, group.representative⟩, uses, savedBits⟩

def roundOf (term : Expr) : ShareRound :=
  if isValueCandidate term then .values else if isLitExpr term then .constants else .builtins

/-- Choose the proposals to bind: builtins by uses, then fixed points, then the
    other terms by size saved, each kept only while no successful run gets
    slower (`planNet`). A fixed point that does not pay for its binding is
    replaced by its functional, whose binding costs fewer steps. A second pass
    retries proposals that later bindings now pay for. -/
def chooseBindings (options : LowOptions) (expression : Expr) : List Expr :=
  let values := if options.values then proposeRound options .values expression else []
  let constants := if options.constants then proposeRound options .constants expression else []
  let builtins := if options.builtins then proposeRound options .builtins expression else []
  let ordered :=
    (builtins.mergeSort fun first second => first.uses >= second.uses) ++
    ((values ++ constants).mergeSort fun first second =>
      (stepsSavedPerUse first.binding.term > stepsSavedPerUse second.binding.term) ||
      (stepsSavedPerUse first.binding.term == stepsSavedPerUse second.binding.term &&
        first.savedBits >= second.savedBits))
  if !options.guardPaths then ordered.map (·.binding.term) else
  let accepts := fun (chosen : List Binding) (binding : Binding) =>
    planNet (chosen ++ [binding]) expression >= -options.slackSteps
  let step := fun (chosen : List Binding) (proposal : Proposal) =>
    if chosen.any (fun binding => alphaEq binding.term proposal.binding.term ||
        fixFunctional proposal.binding.term == some binding.term) then chosen
    else if accepts chosen proposal.binding then chosen ++ [proposal.binding] else
    match fixFunctional proposal.binding.term with
    | some functional =>
      if isFixValue proposal.binding.term &&
          savedBitsOf functional proposal.uses >= options.minimumSavingBits then
        let fallback : Binding := { proposal.binding with term := functional }
        if accepts chosen fallback then chosen ++ [fallback] else chosen
      else chosen
    | none => chosen
  -- A second pass retries proposals that later bindings now pay for.
  let chosen := ordered.foldl step (ordered.foldl step [])
  chosen.map (·.term)

/-- Plan one round for the chosen terms at their current lowest placement. -/
def planChosen (round : ShareRound) (chosen : List Expr) (expression : Expr) : Plan :=
  let terms := chosen.filter fun term => roundOf term == round
  if terms.isEmpty then [] else
  let accept := fun candidate => terms.any (alphaEq · candidate)
  let groups := groupOccurrences (occurrencesOf accept expression)
  groups.toList.filterMap fun group =>
    if group.places.length >= 2 then some (lowestPlace group.places, group.representative)
    else none

def shareChosen (round : ShareRound) (chosen : List Expr) (expression : Expr) : Expr :=
  placeShared (exprSize expression + 1) (planChosen round chosen expression) expression

/-- Values first, so that lambdas are still closed; then constants, then
    builtins. -/
def shareLowBody (options : LowOptions := {}) (expression : Expr) : Expr :=
  let chosen := chooseBindings options expression
  let values := shareChosen .values chosen expression
  let constants := shareChosen .constants chosen values
  shareChosen .builtins chosen constants

/-- The parameters of a script are bound once, by its single application, so
    the body below them is a placement node. -/
def shareLow (options : LowOptions := {}) (expression : Expr) : Expr :=
  mapPeeled (shareLowBody options) expression

end Moist.MIR.Advanced
