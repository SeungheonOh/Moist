import Moist.MIR.Expr
import Moist.MIR.Analysis
import Moist.MIR.Optimize.Purity
import Moist.MIR.Optimize.Safety

namespace Moist.MIR

/-! # Let-Binding Float-Out

Moves let bindings outward past Lam/Fix boundaries so that pure
bindings are evaluated once at the definition site rather than
once per call at each application site.

## Motivation

Consider:

```
Lam x →
  Let a = <pure expr not mentioning x>
  Let b = App (Var a) (Var x)
  ...
```

Every time this lambda is applied, `a` is recomputed even though its value
never depends on `x`. By floating `a` outside the lambda we get:

```
Let a = <pure expr not mentioning x>
Lam x →
  Let b = App (Var a) (Var x)
  ...
```

Now `a` is computed once and shared across all calls.

## Algorithm

The pass works **bottom-up**: sub-expressions are processed first so that
deeply nested bindings bubble outward one level at a time across repeated
applications of the pass.

At each `Lam x body`, or valid `Fix f (Lam x body)`, whose inner body
is a `Let binds innerBody`:

1. **Partition** bindings into a *float set* and a *stay set*.
2. A binding `(v, rhs)` **floats** when ALL of the following hold:
   - `isPure rhs` -- impure bindings must stay in place.
   - Neither crossed binder (`x`, and also `f` for Fix) is in `freeVars rhs`.
   - None of the *stay* variables encountered so far appear in
     `freeVars rhs` (sequential scoping rule).
   - `v` is not a crossed binder, not the name of an earlier stay binding,
     and not free in an earlier stay binding's RHS, so moving it ahead of
     them and out of the Lam/Fix captures nothing.
3. Otherwise the binding **stays**.
4. Reconstruct the expression:
   - Wrap the Lam/Fix with the floated bindings on the outside, retaining
     the mandatory outer lambda of a Fix body.
   - Keep the stayed bindings inside the Lam/Fix body.
   - If one of the two sets is empty, skip the corresponding Let wrapper.

### What we float out of Case alternatives

Pure bindings at the head of case alternatives are floated before the Case
node. Case introduces no implicit named binders: alternatives receive fields
through application, with explicit lambdas introducing their parameters.
Lambda traversal checks parameter dependencies before exposing a binding at
an alternative's head. A floated binder must not be free in the scrutinee or
in any other alternative (`caseFloatSafe`); otherwise the Case is left as is.
Globally unique binders (established by `uniqueOptimizationBinders`) make
these capture checks always succeed in practice.

The cost is evaluating a pure expression even when the branch is not taken.
The benefit is that duplicate computations across branches (e.g.
`force headList`) become visible to CSE once they share a common scope.

### What we do NOT float out of

- **Delay** -- floating would change lazy evaluation to eager evaluation,
  altering semantics.

### Sequential scoping

Bindings in a Let block are scoped left-to-right: a later binding may
reference an earlier one. We process bindings in order and maintain a
set of "stay" variable names. If a binding's RHS mentions any stay
variable, the binding itself must stay (even if it is otherwise pure
and independent of the Lam binder), because its dependency is trapped
inside the Lam/Fix.

## Examples

### Binding floats out of a lambda

```
Lam x →                          Let a = Lit 1
  Let a = Lit 1                   Lam x →
      b = App (Var a) (Var x)       Let b = App (Var a) (Var x)
  in body                           in body
```

`a = Lit 1` is pure and does not mention `x`, so it floats.
`b = App (Var a) (Var x)` mentions `x`, so it stays.

### Binding stays because it depends on the lambda parameter

```
Lam x →
  Let c = App (Var x) (Var x)     -- c mentions x → stays
  in body
```

No transformation is applied.

### Binding stays because of sequential scoping dependency

```
Lam x →
  Let a = App (Var x) (Var x)    -- a mentions x → stays
      b = Lam y (Var a)          -- b is pure, doesn't mention x,
                                 -- BUT depends on stay-var a → stays
  in body
```

Even though `b` is pure and doesn't mention `x`, it references `a`
which is in the stay set, so `b` must also stay.

### Nested lambdas: bindings float to different levels

After two applications of floatOut:

```
Lam x →                          Let a = Lit 1
  Lam y →                        Lam x →
    Let a = Lit 1                   Let b = Lam z (Var x)
        b = Lam z (Var x)          Lam y →
        c = App (Var y) (Var b)       Let c = App (Var y) (Var b)
    in body                           in body
```

- `a` mentions neither `x` nor `y` -- floats out of both lambdas.
- `b` mentions `x` but not `y` -- floats out of the inner lambda only.
- `c` mentions `y` -- stays in the innermost scope.
-/

/-! ## Internal helpers -/

/-- Whether binding `(x, rhs)` may float. It must be pure, must not mention a
crossed binder or a binding that stays (`stays`), and must neither share a
name with a crossed binder nor be named by or free in a staying binding
(`blocked` holds the names and free variables of the staying bindings), so
that moving it before them captures nothing. -/
def floatsPast (binders stays : List VarId) (blocked : VarSet) (x : VarId) (rhs : Expr) : Bool :=
  let rhsFV := freeVars rhs
  isPure rhs && !binders.any rhsFV.contains && !stays.any rhsFV.contains &&
    !binders.any (· == x) && !blocked.contains x

/-- Partition let bindings into (float, stay), left to right, given the
names (`stays`) and the names and free variables (`blocked`) of the bindings
that already stay. -/
def partitionFrom (binders : List VarId) (stays : List VarId) (blocked : VarSet) :
    List (VarId × Expr × Bool) → List (VarId × Expr × Bool) × List (VarId × Expr × Bool)
  | [] => ([], [])
  | (x, rhs, er) :: rest =>
    if floatsPast binders stays blocked x rhs then
      let r := partitionFrom binders stays blocked rest
      ((x, rhs, er) :: r.1, r.2)
    else
      let r := partitionFrom binders (x :: stays) ((blocked.union (freeVars rhs)).insert x) rest
      (r.1, (x, rhs, er) :: r.2)

/-- Partition let bindings into (float, stay) relative to the crossed
binders (none for a case alternative). -/
def partitionBindings (binders : List VarId) (binds : List (VarId × Expr × Bool))
    : List (VarId × Expr × Bool) × List (VarId × Expr × Bool) :=
  partitionFrom binders [] VarSet.empty binds

/-- Wrap an expression in a Let block, or return it unchanged when the
binding list is empty. -/
def mkLet (binds : List (VarId × Expr × Bool)) (body : Expr) : Expr :=
  match binds with
  | [] => body
  | _ => .Let binds body

/-- Flatten nested Let expressions into a single binding list + body. -/
def flattenLets : List (VarId × Expr × Bool) → Expr
    → List (VarId × Expr × Bool) × Expr
  | acc, .Let binds body => flattenLets (acc ++ binds) body
  | acc, e => (acc, e)

/-- Split the head bindings of a case alternative into the ones that float
and the alternative that remains. Nested Lets are flattened first so that
pure bindings created by inner case floating are visible. -/
def floatAlt (alt : Expr) : List (VarId × Expr × Bool) × Expr :=
  match alt with
  | .Let binds body =>
    let (allBinds, innerBody) := flattenLets binds body
    let (floatBinds, stayBinds) := partitionBindings [] allBinds
    (floatBinds, mkLet stayBinds innerBody)
  | _ => ([], alt)

/-- Floated bindings of one alternative must not be named by a free variable
of the scrutinee, of an earlier remaining alternative (`done`), or of a later
alternative (`todo`), so that hoisting them before the case captures nothing. -/
def caseFloatSafe (scrutFV : VarSet) :
    List Expr → List (List (VarId × Expr × Bool) × Expr) → Bool
  | _, [] => true
  | done, (floats, alt) :: todo =>
    floats.all (fun b =>
        !scrutFV.contains b.1 && done.all (fun r => !(freeVars r).contains b.1) &&
        todo.all (fun t => !(freeVars t.2).contains b.1 &&
          t.1.all (fun c => !(freeVars c.2.1).contains b.1))) &&
      caseFloatSafe scrutFV (done ++ [alt]) todo

/-- Try to float bindings out of a Lam or Fix node whose body has already
been processed. `binders` are the variables bound by the Lam/Fix and
`mkWrapper` reconstructs it around a new body. -/
def tryFloat (binders : List VarId) (mkWrapper : Expr → Expr) (result : Expr × Bool) :
    Expr × Bool :=
  match result.1 with
  | .Let binds innerBody =>
    let (floatBinds, stayBinds) := partitionBindings binders binds
    if floatBinds.isEmpty then
      (mkWrapper result.1, result.2)
    else
      (mkLet floatBinds (mkWrapper (mkLet stayBinds innerBody)), true)
  | _ => (mkWrapper result.1, result.2)

/-- Float pure bindings at the head of the (already processed) alternatives
before the case. -/
def floatCase (scrut : Expr) (alts : List Expr) (changed : Bool) : Expr × Bool :=
  let parts := alts.map floatAlt
  let floatedBinds := (parts.map Prod.fst).flatten
  let alts' := parts.map Prod.snd
  if floatedBinds.isEmpty then
    (.Case scrut alts', changed)
  else if caseFloatSafe (freeVars scrut) [] parts then
    (mkLet floatedBinds (.Case scrut alts'), true)
  else
    (.Case scrut alts, changed)

/-! ## Core pass -/

mutual
  /-- Main recursive traversal. -/
  def floatOutGo : Expr → Expr × Bool
    | .Var v        => (.Var v, false)
    | .Lit c        => (.Lit c, false)
    | .Builtin b    => (.Builtin b, false)
    | .Error        => (.Error, false)

    | .Lam x body   => tryFloat [x] (.Lam x) (floatOutGo body)
    | .Fix f (.Lam parameter body) =>
      tryFloat [f, parameter] (fun inner => .Fix f (.Lam parameter inner)) (floatOutGo body)
    | .Fix f body =>
      let r := floatOutGo body
      (.Fix f r.1, r.2)

    | .App f x =>
      let r₁ := floatOutGo f
      let r₂ := floatOutGo x
      (.App r₁.1 r₂.1, r₁.2 || r₂.2)

    | .Force e =>
      let r := floatOutGo e
      (.Force r.1, r.2)

    -- Do NOT float out of Delay bodies; still process sub-expressions so
    -- deeper lambdas benefit.
    | .Delay e =>
      let r := floatOutGo e
      (.Delay r.1, r.2)

    | .Constr tag args =>
      let r := floatOutGoList args
      (.Constr tag r.1, r.2)

    -- Float pure let bindings out of Case alternatives.
    | .Case scrut alts =>
      let r₁ := floatOutGo scrut
      let r₂ := floatOutGoList alts
      floatCase r₁.1 r₂.1 (r₁.2 || r₂.2)

    | .Let binds body =>
      let r₁ := floatOutGoBinds binds
      let r₂ := floatOutGo body
      -- Flatten nested Lets so that bindings floated from case alternatives
      -- merge into the surrounding Let block, enabling CSE across scopes.
      let flat := flattenLets [] r₂.1
      (.Let (r₁.1 ++ flat.1) flat.2, r₁.2 || r₂.2)
  termination_by e => sizeOf e

  /-- Process a list of expressions, collecting the changed flag. -/
  def floatOutGoList : List Expr → List Expr × Bool
    | [] => ([], false)
    | e :: es =>
      let r₁ := floatOutGo e
      let r₂ := floatOutGoList es
      (r₁.1 :: r₂.1, r₁.2 || r₂.2)
  termination_by es => sizeOf es

  /-- Process let bindings (RHS only). -/
  def floatOutGoBinds : List (VarId × Expr × Bool) → List (VarId × Expr × Bool) × Bool
    | [] => ([], false)
    | (v, rhs, er) :: rest =>
      let r₁ := floatOutGo rhs
      let r₂ := floatOutGoBinds rest
      ((v, r₁.1, er) :: r₂.1, r₁.2 || r₂.2)
  termination_by bs => sizeOf bs
end

/-- Bottom-up let-float-out pass. Returns the transformed expression
together with a flag indicating whether any binding was moved.

See the module-level documentation for a full description of the algorithm,
invariants, and worked examples. -/
def floatOut (expression : Expr) : Expr × Bool :=
  floatOutGo (uniqueOptimizationBinders expression)

end Moist.MIR
