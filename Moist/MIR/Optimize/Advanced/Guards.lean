import Moist.MIR.Optimize.Advanced.FailFast
import Moist.MIR.Optimize.Advanced.KnownLists

namespace Moist.MIR.Advanced

open Moist.Plutus.Term

/-! # Checks before work

A validator that answers `if X then () else error` pays for every binding
that `X` evaluates before its first failing check, even on reject paths that
never use those bindings. Three steps move such work behind the checks:

* `pushAsserts` turns `force (ifThenElse X (delay u) (delay error))` with a
  constant `u` into `X` with every Boolean result replaced: `true` becomes
  `u`, `false` becomes `error`, and the consumer moves into lets, into the
  alternatives of cases whose scrutinee shape fixes the number of fields of
  each alternative, and into both branches of `ifThenElse`. Every check of
  `X` then has a local `error` alternative.
* `splitChecks` names the argument of a builtin scrutinee when that argument
  itself contains a check, so that the destructuring can move without the
  check.
* `sinkUnits` moves a strict step (a binding, a case with a single continuing
  alternative, or a check) below the strict steps that follow it, when it is
  not needed by them, as long as it then ends up below at least one check.
  Every step it passes must halt or fail in every environment where its facts
  hold (`chk`), since the target evaluates it first.

`chk` is a termination analysis that knows the values of bound names
(the recorded right-hand sides), the names known to hold builtin lists, and
the recursive functions whose calls shrink one argument. A call of a
recursive function terminates by induction on the size of that argument.
-/

/-! ## Scrutinee shapes -/

inductive Kind where
  | bool | int | list | pair | constrs (arities : List Nat) | unknown
  deriving DecidableEq, Repr

def kindFuel : Nat := 64

def scrutineeKind (facts : List (VarId × Expr)) (lists : List VarId) (s : Expr) : Kind :=
  if knownBooleanLocal kindFuel facts s then .bool
  else if knownInteger kindFuel facts s then .int
  else if knownListValue kindFuel facts lists s then .list
  else if constructorPair kindFuel facts s then .pair
  else .unknown

def headListE (s : Expr) : Expr := .App (.Force (.Builtin .HeadList)) s
def tailListE (s : Expr) : Expr := .App (.Force (.Builtin .TailList)) s
def fstPairE (s : Expr) : Expr := .App (.Force (.Force (.Builtin .FstPair))) s
def sndPairE (s : Expr) : Expr := .App (.Force (.Force (.Builtin .SndPair))) s

/-- Facts for the binders of the first alternative of a list or pair case. -/
def binderFacts (kind : Kind) (s : Expr) (first second : VarId) (facts : List (VarId × Expr)) :
    List (VarId × Expr) :=
  match kind with
  | .list => (second, tailListE s) :: (first, headListE s) :: facts
  | .pair => (second, sndPairE s) :: (first, fstPairE s) :: facts
  | _ => facts

/-! ## Termination with facts and recursion -/

/-- What a computation is known to do: halt or fail (`term`); fail or
    return a constant or a constructor (`inert`); fail or return a Boolean
    constant (`bool`). -/
inductive VMode where
  | term | inert | bool
  /-- Fail, or return a constructor whose tag `i` carries `arities[i]` fields. -/
  | constrs (arities : List Nat)
  deriving DecidableEq, Repr

/-- The mode that also makes applying the result to more arguments fail. -/
def VMode.applied : VMode → VMode
  | .term => .inert
  | m => m

/-- `have` provides what `want` asks for. -/
def VMode.covers : VMode → VMode → Bool
  | _, .term => true
  | .inert, .inert | .bool, .inert | .constrs _, .inert => true
  | .bool, .bool => true
  | .constrs ks, .constrs ks' => ks == ks'
  | _, _ => false

/-- A recursive function whose calls shrink the argument at `index`. -/
structure Role where
  fn : VarId
  arity : Nat
  index : Nat
  base : VarId
  small : List VarId
  lists : List Nat
  result : VMode
  deriving Repr

structure TCtx where
  facts : List (VarId × Expr)
  lists : List VarId
  roles : List Role

/-- `x` is mentioned by no fact, list or role of the context. -/
def TCtx.fresh (c : TCtx) (x : VarId) : Bool :=
  !(c.facts.any fun entry => entry.1 == x) && !c.lists.contains x &&
    c.roles.all fun r => !(r.fn == x) && !(r.base == x) && !r.small.contains x

def TCtx.pushFact (c : TCtx) (x : VarId) (r : Expr) : TCtx :=
  { c with facts := (x, r) :: c.facts }

def TCtx.addLists (c : TCtx) (xs : List VarId) : TCtx :=
  { c with lists := xs ++ c.lists }

/-- The binders of a case on `z` are smaller than `z`. -/
def Role.descend (z : VarId) (binders : List VarId) (r : Role) : Role :=
  if z == r.base || r.small.contains z then { r with small := binders ++ r.small } else r

def TCtx.descend (c : TCtx) (s : Expr) (binders : List VarId) : TCtx :=
  match s with
  | .Var z => { c with roles := c.roles.map (Role.descend z binders) }
  | _ => c

/-- The argument of a successful `nullList` is a list. -/
def TCtx.nullFlow (c : TCtx) (s : Expr) : TCtx :=
  match s with
  | .App f (.Var x) =>
    match resolveHead kindFuel c.facts f with
    | .Force (.Builtin .NullList) => c.addLists [x]
    | _ => c
  | _ => c

/-- What a saturated builtin returns. -/
def builtinCovers (b : BuiltinFun) : VMode → Bool
  | .term => true
  | .inert => !passThroughBuiltin b || b == .MkCons
  | .bool => booleanBuiltin b
  | .constrs _ => false

def appSpine : Expr → Expr × List Expr
  | .App f a => let (h, args) := appSpine f; (h, args ++ [a])
  | e => (e, [])

def lamSpine : Expr → List VarId × Expr
  | .Lam x b => let (xs, body) := lamSpine b; (x :: xs, body)
  | e => ([], e)

/-- Peel exactly `k` leading lambdas. -/
def peelLams : Nat → Expr → Option (List VarId × Expr)
  | 0, e => some ([], e)
  | k + 1, .Lam x b => (peelLams k b).map fun (xs, body) => (x :: xs, body)
  | _ + 1, _ => none

def Role.shrinks (facts : List (VarId × Expr)) (r : Role) (arg : Expr) : Bool :=
  match arg with
  | .Var y => r.small.contains y
  | .App f (.Var z) =>
    (match resolveHead kindFuel facts f with
      | .Force (.Builtin .TailList) => true
      | _ => false) && (z == r.base || r.small.contains z)
  | _ => false

def argListPositions (c : TCtx) (args : List Expr) : List Nat :=
  (List.range args.length).filter fun i =>
    match args[i]? with
    | some a => knownListValue kindFuel c.facts c.lists a
    | none => false

def argListParams (positions : List Nat) (params : List VarId) : List VarId :=
  positions.filterMap fun i => params[i]?

/-- Fields carried by each tag of a scrutinee of this shape. -/
def Kind.fields : Kind → Nat → Option Nat
  | .bool, _ | .int, _ => some 0
  | .list, 0 => some 2
  | .list, _ => some 0
  | .pair, 0 => some 2
  | .constrs ks, i => ks[i]?
  | _, _ => none

/-- Shape facts gained by the binders of alternative `i`. -/
def kindLists (kind : Kind) (i : Nat) (binders : List VarId) : List VarId :=
  match kind, i, binders with
  | .list, 0, [_, t] => [t]
  | .pair, 0, [_, t] => [t]
  | _, _, _ => []

def chkFuel : Nat := 400

/-- The analysis below, given its recursive call. -/
abbrev Chk := TCtx → VMode → Bool → Expr → Bool

/-- The alternatives of a non-applied case whose scrutinee has the given shape. -/
def caseAlts (rec : Chk) (c c' : TCtx) (v : VMode) (s : Expr) (kind : Kind) (alts : List Expr) : Bool :=
  (alts.zipIdx).all fun (a, i) =>
    match kind.fields i with
    | some k =>
      match peelLams k a with
      | some (binders, body) =>
        binders.all c.fresh &&
          rec ((c'.descend s binders).addLists (kindLists kind i binders)) v false body
      | none =>
        let (binders, body) := lamSpine a
        binders.all c.fresh && rec (c'.descend s binders) v true body
    | none =>
      if kind == .unknown then
        let (binders, body) := lamSpine a
        (v == .term || binders.isEmpty) && binders.all c.fresh && rec (c'.descend s binders) v true body
      else true

/-- The shape of a scrutinee: syntactic, or a Boolean or constructor result. -/
def caseKind (rec : Chk) (c : TCtx) (s : Expr) (alts : List Expr) : Kind :=
  let kind₀ := scrutineeKind c.facts c.lists s
  let arities := alts.map fun a => (lamSpine a).1.length
  if kind₀ != .unknown then kind₀
  else if rec c .bool false s then Kind.bool
  else if rec c (.constrs arities) false s then Kind.constrs arities
  else kind₀

/-- A call of a recursive function: some parameter shrinks at every recursive call. -/
def fixOK (rec : Chk) (c : TCtx) (roles : List Role) (v : VMode) (f p : VarId) (body : Expr)
    (args : List Expr) : Bool :=
  let (ps, inner) := lamSpine body
  let params := p :: ps
  let inferred := listPositions c.facts c.lists f params args inner
  params.length == args.length && c.fresh f && params.all c.fresh &&
    [inferred, []].any fun positions =>
      positions.all (fun i => match args[i]? with
        | some a => knownListValue kindFuel c.facts c.lists a
        | none => false) &&
      (List.range params.length).any fun j =>
        (v :: [VMode.bool, .inert, .term]).any fun result =>
          result.covers v &&
            match params[j]? with
            | some base =>
              rec { facts := c.facts, lists := argListParams positions params ++ c.lists,
                    roles := ⟨f, params.length, j, base, [], positions, result⟩ :: roles }
                result false inner
            | none => false

/-- A call of `h` with `args`, whose arguments have been checked. -/
def callOK (rec : Chk) (c : TCtx) (v : VMode) (h : Expr) (args : List Expr) : Bool :=
  match h with
  | .Var x =>
    match c.roles.find? (fun r => r.fn == x) with
    | some r =>
      args.length == r.arity &&
        (match args[r.index]? with
          | some a => r.shrinks c.facts a
          | none => false) &&
        r.lists.all (fun i => match args[i]? with
          | some a => knownListValue kindFuel c.facts c.lists a
          | none => false) &&
        r.result.covers v
    | none =>
      match c.facts.find? (fun entry => entry.1 == x) with
      | some (_, rhs) =>
        match rhs with
        | .Fix f (.Lam p body) => fixOK rec c [] v f p body args
        | _ =>
          let (params, body) := lamSpine rhs
          params.length == args.length && 0 < params.length && params.all c.fresh &&
            rec (({ c with roles := [] }).addLists
              (argListParams (argListPositions c args) params)) v false body
      | none => false
  | .Fix f (.Lam p body) => fixOK rec c c.roles v f p body args
  | _ => false

def chk : Nat → TCtx → VMode → Bool → Expr → Bool
  | 0, _, _, _, _ => false
  | n + 1, c, v, alt, e =>
    match e with
    | .Lam x b => v == .term && (!alt || (c.fresh x && chk n c .term true b))
    | .Let [] body => chk n c v alt body
    | .Let ((x, r, _) :: rest) body =>
      c.fresh x && chk n c .term false r && chk n (c.pushFact x r) v alt (.Let rest body)
    | .Case s alts =>
      chk n c .term false s &&
      if alt then alts.all (chk n c v true) else
        caseAlts (chk n) c (c.nullFlow s) v s (caseKind (chk n) c s alts) alts
    | .Force inner =>
      match delayBody inner with
      | some body => chk n c v alt body
      | none =>
        match iteView inner with
        | some (cnd, a, b) => chk n c .term false cnd && chk n c v alt a && chk n c v alt b
        | none =>
          let v' := if alt then v.applied else v
          match builtinProtocolAfterSuccess (resolveHead kindFuel c.facts inner) with
          | some (b, rem) =>
            rem.head == .argQ && chk n c .term false inner &&
              (v' == .term || (rem.isFinal && builtinCovers b v'))
          | none => false
    | _ =>
      let v' := if alt then v.applied else v
      match e with
      | .Var _ =>
        match v' with
        | .term => true
        | .inert => scrutineeKind c.facts c.lists e != .unknown
        | .bool => scrutineeKind c.facts c.lists e == .bool
        | .constrs _ => false
      | .Lit (k, _) =>
        match v', k with
        | .bool, .Bool _ => true
        | .bool, _ | .constrs _, _ => false
        | _, _ => true
      | .Error => true
      | .Builtin _ | .Delay _ => v' == .term
      | .Fix _ (.Lam _ _) => v' == .term
      | .Constr tag fields =>
        (match v' with
          | .bool => false
          | .constrs ks => match ks[tag]? with
            | some k => k == fields.length
            | none => true
          | _ => true) && fields.all (chk n c .term false)
      | .App f a =>
        match builtinProtocolAfterSuccess (resolveHead kindFuel c.facts f) with
        | some (b, rem) =>
          rem.head == .argV && chk n c .term false f && chk n c .term false a &&
            (v' == .term || (rem.isFinal && builtinCovers b v'))
        | none =>
          (appSpine e).2.all (chk n c .term false) && callOK (chk n) c v' (appSpine e).1 (appSpine e).2
      | _ => false

def terminatesWith (facts : List (VarId × Expr)) (e : Expr) : Bool :=
  chk chkFuel ⟨facts, [], []⟩ .term false e

/-! ## Pushing the consumer `if _ then u else error` into a computation -/

def iteE (c a b : Expr) : Expr := .App (.App (.App (.Force (.Builtin .IfThenElse)) c) a) b

def assertE (u : Const × BuiltinType) (x : Expr) : Expr :=
  .Force (iteE x (.Delay (.Lit u)) (.Delay .Error))

def assertLeaf (facts : List (VarId × Expr)) (u : Const × BuiltinType) (x : Expr) : Expr :=
  if knownBooleanLocal kindFuel facts x then .Case x [.Error, .Lit u] else assertE u x

def assertInto (facts : List (VarId × Expr)) (u : Const × BuiltinType) : Nat → Expr → Expr
  | 0, x => assertE u x
  | n + 1, x =>
    match x with
    | .Lit (.Bool true, _) => .Lit u
    | .Lit (.Bool false, _) | .Error => .Error
    | .Let [] body => assertInto facts u n body
    | .Let ((y, r, er) :: rest) body => consLet (y, r, er) (assertInto ((y, r) :: facts) u n (.Let rest body))
    | .Case s alts =>
      match scrutineeKind facts [] s with
      | .bool | .int => .Case s (alts.map (assertInto facts u n))
      | .list =>
        match alts with
        | (.Lam h (.Lam t b)) :: a1 :: rest =>
          .Case s (.Lam h (.Lam t (assertInto (binderFacts .list s h t facts) u n b)) ::
            assertInto facts u n a1 :: rest)
        | _ => assertLeaf facts u x
      | .pair =>
        match alts with
        | [.Lam a (.Lam b body)] =>
          .Case s [.Lam a (.Lam b (assertInto (binderFacts .pair s a b facts) u n body))]
        | _ => assertLeaf facts u x
      | _ => assertLeaf facts u x
    | .Force inner =>
      match iteView inner with
      | some (cnd, a, b) =>
        .Force (iteE cnd (.Delay (assertInto facts u n a)) (.Delay (assertInto facts u n b)))
      | none => assertLeaf facts u x
    | _ => assertLeaf facts u x

def assertFuel : Nat := 4096

/-- The constant `u` of `force (ifThenElse x (delay u) (delay error))`. -/
def assertView : Expr → Option (Expr × (Const × BuiltinType))
  | .Force (.App (.App (.App (.Force (.Builtin .IfThenElse)) x) (.Delay (.Lit u))) (.Delay .Error)) =>
    some (x, u)
  | _ => none

/-- Facts for the binders of the first alternative of a case on `s`. -/
def altFacts (facts : List (VarId × Expr)) (s : Expr) (h t : VarId) : List (VarId × Expr) :=
  match scrutineeKind facts [] s with
  | .list => binderFacts .list s h t facts
  | .pair => binderFacts .pair s h t facts
  | _ => facts

def pushWalk (facts : List (VarId × Expr)) (e : Expr) : Expr :=
  match e with
  | .Let [] body => pushWalk facts body
  | .Let ((x, r, er) :: rest) body =>
    consLet (x, pushWalk facts r, er) (pushWalk ((x, r) :: facts) (.Let rest body))
  | .Lam x b => .Lam x (pushWalk facts b)
  | .Fix f b => .Fix f (pushWalk facts b)
  | .App f a => .App (pushWalk facts f) (pushWalk facts a)
  | .Delay b => .Delay (pushWalk facts b)
  | .Constr tag fields => .Constr tag (fields.attach.map fun ⟨field, _⟩ => pushWalk facts field)
  | .Case s ((.Lam h (.Lam t b)) :: rest) =>
    .Case (pushWalk facts s) (.Lam h (.Lam t (pushWalk (altFacts facts s h t) b)) ::
      rest.attach.map fun ⟨alt, _⟩ => pushWalk facts alt)
  | .Case s alts => .Case (pushWalk facts s) (alts.attach.map fun ⟨alt, _⟩ => pushWalk facts alt)
  | .Force (.App (.App (.App (.Force (.Builtin .IfThenElse)) x) (.Delay (.Lit u))) (.Delay .Error)) =>
    assertInto facts u assertFuel (pushWalk facts x)
  | .Force inner => .Force (pushWalk facts inner)
  | .Var _ | .Lit _ | .Builtin _ | .Error => e
termination_by exprSize e
decreasing_by
  all_goals first
    | (simp only [exprSize, exprSizeList]; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize, exprSizeList]; omega)
    | (simp only [exprSize, exprSizeBinds]; have := exprSize_pos r; omega)

def pushAsserts (e : Expr) : Expr :=
  let prepared := uniqueOptimizationBinders e
  if wellScoped prepared then pushWalk [] prepared else prepared

/-! ## Naming the argument that carries a check -/

/-- An `error` or a case with an `error` alternative outside any lambda or delay. -/
def hasStrictCheck : Expr → Bool
  | .Error => true
  | .Var _ | .Lit _ | .Builtin _ | .Lam _ _ | .Delay _ | .Fix _ _ => false
  | .App f a => hasStrictCheck f || hasStrictCheck a
  | .Force b => hasStrictCheck b
  | .Constr _ fields => fields.attach.any fun ⟨field, _⟩ => hasStrictCheck field
  | .Case s alts => alts.any (fun a => isErrorExpr (lamSpine a).2) || hasStrictCheck s ||
      alts.attach.any fun ⟨alt, _⟩ => hasStrictCheck alt
  | .Let bs body => (bs.attach.any fun ⟨(_, r, _), _⟩ => hasStrictCheck r) || hasStrictCheck body
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem (by assumption); omega)
    | (rename_i h; have := List.sizeOf_lt_of_mem h; simp at this; omega)

/-- Heads whose evaluation returns at once. -/
def pureHead : Expr → Bool
  | .Var _ | .Builtin _ => true
  | _ => false

/-- `h₁ (h₂ (… (hₖ x)))` with pure heads, `x` replaced by `d`. -/
def checkArgument (d : VarId) : Expr → Option (Expr × Expr)
  | .App f a =>
    if pureHead f then
      match a with
      | .Var _ | .Lit _ => none
      | _ =>
        match checkArgument d a with
        | some (x, a') => some (x, .App f a')
        | none => if hasStrictCheck a then some (a, .App f (.Var d)) else none
    else none
  | _ => none

theorem checkArgument_size {d : VarId} : ∀ {s x s' : Expr}, checkArgument d s = some (x, s') →
    exprSize x < exprSize s
  | .App f a, x, s', h => by
    unfold checkArgument at h
    split at h
    · split at h
      · cases h
      · cases h
      · split at h
        · rename_i x' a' ha
          cases h
          have := checkArgument_size ha
          simp only [exprSize]; omega
        · split at h
          · cases h; simp only [exprSize]; omega
          · cases h
    · cases h
  | .Var _, _, _, h | .Lit _, _, _, h | .Builtin _, _, _, h | .Error, _, _, h
  | .Lam _ _, _, _, h | .Fix _ _, _, _, h | .Force _, _, _, h | .Delay _, _, _, h
  | .Constr _ _, _, _, h | .Case _ _, _, _, h | .Let _ _, _, _, h => by simp [checkArgument] at h

def splitWalk (d : VarId) (e : Expr) : Expr :=
  match e with
  | .Let [] body => splitWalk d body
  | .Let ((x, r, er) :: rest) body => consLet (x, splitWalk d r, er) (splitWalk d (.Let rest body))
  | .Lam x b => .Lam x (splitWalk d b)
  | .Fix f b => .Fix f (splitWalk d b)
  | .App f a => .App (splitWalk d f) (splitWalk d a)
  | .Force b => .Force (splitWalk d b)
  | .Delay b => .Delay (splitWalk d b)
  | .Constr tag fields => .Constr tag (fields.attach.map fun ⟨field, _⟩ => splitWalk d field)
  | .Case s alts =>
    let alts' := alts.attach.map fun ⟨alt, _⟩ => splitWalk d alt
    match hcheck : checkArgument d s with
    | some (x, s') =>
      if alts.any isErrorExpr && (alts.filter fun a => !isErrorExpr a).length == 1 then
        .Let [(d, splitWalk d x, false)] (.Case s' alts')
      else .Case (splitWalk d s) alts'
    | none => .Case (splitWalk d s) alts'
  | .Var _ | .Lit _ | .Builtin _ | .Error => e
termination_by exprSize e
decreasing_by
  all_goals first
    | (simp only [exprSize, exprSizeList]; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize, exprSizeList]; omega)
    | (simp only [exprSize, exprSizeBinds]; have := exprSize_pos r; omega)
    | (have := checkArgument_size hcheck; simp only [exprSize]; omega)

def splitChecks (e : Expr) : Expr :=
  let d : VarId := ⟨maxUidExpr e + 1, .gen, "checked"⟩
  splitWalk d e

/-! ## Moving strict steps below checks -/

/-- An alternative that fails once applied to its fields. -/
def isErrorAlt (a : Expr) : Bool := isErrorExpr (lamSpine a).2

/-- A strict step with a single continuation. -/
inductive GUnit where
  | bind (x : VarId) (r : Expr) (er : Bool)
  /-- `case s (before ++ [λ binders. □] ++ after)`, `before` and `after` all `error`. -/
  | cases (s : Expr) (before after : List Expr) (binders : List VarId)
  | ite (c : Expr)

def lams : List VarId → Expr → Expr
  | [], b => b
  | x :: xs, b => .Lam x (lams xs b)

def GUnit.plug : GUnit → Expr → Expr
  | .bind x r er, b => .Let [(x, r, er)] b
  | .cases s before after binders, b => .Case s (before ++ [lams binders b] ++ after)
  | .ite c, b => .Force (iteE c (.Delay b) (.Delay .Error))

def GUnit.expr : GUnit → Expr
  | .bind _ r _ => r
  | .cases s _ _ _ => s
  | .ite c => c

def GUnit.binders : GUnit → List VarId
  | .bind x _ _ => [x]
  | .cases _ _ _ binders => binders
  | .ite _ => []

def GUnit.guard : GUnit → Bool
  | .bind _ _ _ => false
  | .cases _ before after _ => !before.isEmpty || !after.isEmpty
  | .ite _ => true

def GUnit.facts (u : GUnit) (facts : List (VarId × Expr)) : List (VarId × Expr) :=
  match u with
  | .bind x r _ => (x, r) :: facts
  | .cases s _ _ [h, t] => altFacts facts s h t
  | _ => facts

/-- The continuing alternative, with the number of fields its tag carries. -/
def continuing (kind : Kind) (before : List Expr) (alt : Expr) : Option (List VarId × Expr) :=
  match kind, before.length, alt with
  | .bool, _, a | .int, _, a => some ([], a)
  | .list, 0, .Lam h (.Lam t b) => some ([h, t], b)
  | .list, 1, a => some ([], a)
  | .pair, 0, .Lam h (.Lam t b) => some ([h, t], b)
  | _, _, _ => none

def unitView (facts : List (VarId × Expr)) : Expr → Option (GUnit × Expr)
  | .Let [(x, r, er)] body => some (.bind x r er, body)
  | .Let ((x, r, er) :: rest) body => some (.bind x r er, .Let rest body)
  | .Case s alts =>
    match alts.findIdx? (fun a => !isErrorAlt a) with
    | none => none
    | some k =>
      let before := alts.take k
      let after := alts.drop (k + 1)
      if after.all isErrorAlt then
        match alts[k]? with
        | some alt =>
          match continuing (scrutineeKind facts [] s) before alt with
          | some (binders, body) => some (.cases s before after binders, body)
          | none => none
        | none => none
      else none
  | .Force (.App (.App (.App (.Force (.Builtin .IfThenElse)) c) (.Delay body)) (.Delay .Error)) =>
    some (.ite c, body)
  | _ => none

def disjoint (xs : List VarId) (vars : VarSet) : Bool := xs.all fun x => !vars.contains x

def canSwap (facts : List (VarId × Expr)) (a b : GUnit) : Bool :=
  disjoint a.binders (freeVars b.expr) && disjoint b.binders (freeVars a.expr) &&
    traceFree a.expr && traceFree b.expr && terminatesWith facts b.expr

/-- Move `a` below the steps of `body`, ending below a check. -/
def sinkPast : Nat → List (VarId × Expr) → GUnit → Expr → Option Expr
  | 0, _, _, _ => none
  | n + 1, facts, a, body =>
    match unitView facts body with
    | some (b, inner) =>
      if canSwap facts a b then
        match sinkPast n (b.facts facts) a inner with
        | some inner' => some (b.plug inner')
        | none => if b.guard then some (b.plug (a.plug inner)) else none
      else none
    | none => none

def sinkFuel : Nat := 256

/-- Bindings and list or pair destructuring move; checks stay in place. -/
def movable (facts : List (VarId × Expr)) (a : GUnit) : Bool :=
  !hasStrictCheck a.expr &&
    match a with
    | .bind _ _ _ => true
    | .cases s _ _ _ =>
      match scrutineeKind facts [] s with
      | .list | .pair => true
      | _ => false
    | .ite _ => false

def trySink (facts : List (VarId × Expr)) (e : Expr) : Expr :=
  match unitView facts e with
  | some (a, body) =>
    if movable facts a then (sinkPast sinkFuel facts a body).getD e else e
  | none => e

def sinkWalk (facts : List (VarId × Expr)) (e : Expr) : Expr :=
  match e with
  | .Let [] body => sinkWalk facts body
  | .Let ((x, r, er) :: rest) body =>
    trySink facts (consLet (x, sinkWalk facts r, er) (sinkWalk ((x, r) :: facts) (.Let rest body)))
  | .Lam x b => .Lam x (sinkWalk facts b)
  | .Fix f b => .Fix f (sinkWalk facts b)
  | .App f a => .App (sinkWalk facts f) (sinkWalk facts a)
  | .Delay b => .Delay (sinkWalk facts b)
  | .Constr tag fields => .Constr tag (fields.attach.map fun ⟨field, _⟩ => sinkWalk facts field)
  | .Case s ((.Lam h (.Lam t b)) :: rest) =>
    trySink facts (.Case (sinkWalk facts s) (.Lam h (.Lam t (sinkWalk (altFacts facts s h t) b)) ::
      rest.attach.map fun ⟨alt, _⟩ => sinkWalk facts alt))
  | .Case s alts =>
    trySink facts (.Case (sinkWalk facts s) (alts.attach.map fun ⟨alt, _⟩ => sinkWalk facts alt))
  | .Force inner => trySink facts (.Force (sinkWalk facts inner))
  | .Var _ | .Lit _ | .Builtin _ | .Error => e
termination_by exprSize e
decreasing_by
  all_goals first
    | (simp only [exprSize, exprSizeList]; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize, exprSizeList]; omega)
    | (simp only [exprSize, exprSizeBinds]; have := exprSize_pos r; omega)

def sinkUnits (e : Expr) : Expr :=
  let prepared := uniqueOptimizationBinders e
  if wellScoped prepared then sinkWalk [] prepared else prepared

/-- Checks before work. -/
def checksFirst (e : Expr) : Expr := sinkUnits (splitChecks (pushAsserts e))

end Moist.MIR.Advanced
