# MIR Implementation Plan

## 1. The Type

```lean
namespace Moist.MIR

structure VarId where
  uid  : Nat
  hint : String := ""
deriving BEq, Hashable, Repr, Inhabited

inductive Expr
  -- Atoms (trivial, duplicable, no side effects)
  | Var     : VarId → Expr
  | Lit     : Const × BuiltinType → Expr
  | Builtin : BuiltinFun → Expr

  -- Sequential let binding (each binding is in scope for subsequent RHS and body)
  -- Constraint: no binding may reference itself (use Fix for recursion)
  | Let     : List (VarId × Expr) → Expr → Expr

  -- Fixed point (f is self-referential in body, body is typically a Lam)
  | Fix     : VarId → Expr → Expr

  -- Lambda & application
  | Lam     : VarId → Expr → Expr
  | App     : Expr → Expr → Expr

  -- Plutus-specific
  | Force   : Expr → Expr
  | Delay   : Expr → Expr
  | Constr  : Nat → List Expr → Expr
  | Case    : Expr → List Expr → Expr

  -- Bottom
  | Error   : Expr
deriving Repr, BEq
```

### 1.1 Design Rationale

**No separate Atom type.** `Var`, `Lit`, `Builtin` live directly on `Expr`. The ANF invariant (arguments to `App`, `Force`, `Constr`, `Case` should be trivial) is enforced via a decidable predicate and subtype (Section 2), not by splitting into separate types. Pattern matching stays flat.

**Let is sequential, non-self-recursive.** `Let binds body` introduces a sequence of bindings where each binding is in scope for all subsequent RHS and the body. This is equivalent to nested single-binding Lets but avoids artificial tree depth.

```
let a = foo
    b = a + 1
    c = a + b
in body
```

is equivalent to:

```
let a = foo in
let b = a + 1 in
let c = a + b in
body
```

The one constraint: **no binding may reference itself**. `let a = a + 1` is nonsensical in a strict language — self-reference is what `Fix` is for. This constraint is checked as part of the `isANF` well-formedness predicate (Section 2) and carried as proof in the `ANFExpr` subtype.

Scoping rules for `Let [(x₁, e₁), (x₂, e₂), (x₃, e₃)] body`:
- `e₁` sees the enclosing scope only
- `e₂` sees the enclosing scope + `{x₁}`
- `e₃` sees the enclosing scope + `{x₁, x₂}`
- `body` sees the enclosing scope + `{x₁, x₂, x₃}`

**Fix is a separate value node.** `Fix f body` is a value expression — the recursive function itself. `f` is bound as a self-reference within `body` (which should be a `Lam`). This is distinct from `Let` because:

- Fix is a *value* you can inline, substitute, move around. Inlining a Fix at a call site is just substitution — the self-reference is self-contained.
- Let is a *binding form* that introduces names into a scope.
- A recursive function definition is `Let [(g, Fix f (Lam x body))] rest`. Inlining `g` means substituting the Fix value. Simple.
- Lowering Fix to UPLC produces the Z combinator. The choice of encoding strategy (compact/standard/inline) is made at lowering time, per-Fix, based on context.

**App/Force/Constr/Case take Expr, not atoms.** Raw MIR from the DSL may have non-atomic arguments. The ANF normalization pass (Section 5) inserts Let bindings to make them atomic. After normalization, the `isANF` predicate holds, and the expression is wrapped in a subtype `ANFExpr` that carries this proof.

### 1.2 Predicates

```lean
def Expr.isAtom : Expr → Bool
  | .Var _ | .Lit _ | .Builtin _ => true
  | _ => false

def Expr.isValue : Expr → Bool
  | .Var _ | .Lit _ | .Builtin _ => true
  | .Lam _ _ => true
  | .Delay _ => true
  | .Fix _ _ => true
  | _ => false
```

Values are safe to inline regardless of use count — no duplicated work, no duplicated effects. Note that `Fix` is a value (it's a recursive function, already "computed").

### 1.3 What We Deliberately Omit

- **Hoisting nodes**: Hoisting is a lowering concern. The lowering pass identifies shared closed subterms and extracts them.
- **Type annotations on Expr**: MIR targets untyped UPLC. Types live in the PTerm layer. If we later need type info during optimization, we add optional metadata.
- **Multi-arg App**: Keep binary. A helper `uncurryApp` recovers the spine for analysis (e.g., detecting saturated builtin calls).
- **LetRec / mutual recursion**: Deferred. Single recursion via Fix covers the vast majority of Plutus use cases. Mutual recursion can be added as a `LetRec` node later.

---

## 2. ANF and Basic Let Validity: Type-Level Enforcement

We use a decidable `Bool`-valued predicate and Lean's subtype to distinguish raw MIR from validated ANF MIR at the type level. The predicate checks:
- the ANF invariant (atomic arguments), and
- one local Let invariant: no binding references itself.

This is intentionally weaker than full scope validation. In particular, `isANF` does **not** prove that every variable occurrence is in scope or that an early binding does not reference a later binding in the same Let chain. Those are separate structural checks if we choose to add a full MIR validator later.

### 2.1 No-Self-Reference Check

```lean
/-- Check that no binding in a sequential Let references itself.
    This is only a local recursion check, not full scope validation.
    Earlier bindings referencing later ones is also illegal (they're not in scope),
    but this function does not detect that. -/
def noSelfRef (binds : List (VarId × Expr)) : Bool :=
  binds.all fun (x, rhs) => !(freeVars rhs).contains x
```

### 2.2 The Combined Predicate

```lean
/-- Check that an expression is in A-Normal Form and satisfies the
    basic Let validity invariant:
    1. All argument positions in App, Force, Constr, Case hold atomic expressions
    2. No Let binding references itself -/
partial def Expr.isANF : Expr → Bool
  | .Var _ | .Lit _ | .Builtin _ | .Error => true
  | .Lam _ body => body.isANF
  | .Fix _ body => body.isANF
  | .Delay e => e.isANF
  | .Let binds body =>
      noSelfRef binds                       -- no self-referential bindings
      && binds.all (fun (_, rhs) => rhs.isANF)  -- all RHS are ANF
      && body.isANF                              -- body is ANF
  | .App f x => f.isAtom && x.isAtom
  | .Force e => e.isAtom
  | .Constr _ args => args.all (·.isAtom)
  | .Case scrut alts => scrut.isAtom && alts.all (·.isANF)
```

### 2.3 The Subtype

```lean
/-- An expression that satisfies the ANF invariant plus the
    "no self-referential Let binding" check. -/
abbrev ANFExpr := { e : Expr // e.isANF = true }

/-- Try to wrap a raw Expr as ANFExpr, checking the invariant. -/
def Expr.toANF? (e : Expr) : Option ANFExpr :=
  if h : e.isANF then some ⟨e, h⟩ else none

/-- Unwrap to raw Expr (for passes that don't preserve ANF). -/
def ANFExpr.toExpr (e : ANFExpr) : Expr := e.val
```

`ANFExpr` should therefore be read as "ANF + basic local Let sanity", not "globally scope-validated MIR". If we later want a stronger guarantee, add a separate `isWellScoped : Expr → Bool` (or `validate : Expr → Bool`) and define a stronger subtype on top.

### 2.4 Pipeline Usage

```lean
-- DSL produces raw Expr
def compilePTerm : PTerm a → Expr

-- ANF normalization: raw → ANF (proof produced here)
def anfNormalize : Expr → FreshM ANFExpr

-- Optimization passes work on raw Expr (no proof obligation per pass)
def optimize : Expr → Expr

-- Lowering requires ANF
def lower : ANFExpr → Option Term

-- Pipeline:
-- 1. compilePTerm t           → Expr (raw)
-- 2. anfNormalize raw         → ANFExpr (proven)
-- 3. optimize anf.toExpr      → Expr (raw, ANF might be disturbed)
-- 4. anfNormalize optimized   → ANFExpr (re-proven, cheap on already-ANF input)
-- 5. lower reanf              → Option Term
```

Optimization passes drop the proof, work on bare `Expr`, and we re-validate after. The re-normalization is cheap — on already-ANF input it's essentially a no-op traversal. This avoids burdening every optimization pass with proof obligations while still guaranteeing `lower` receives valid ANF.

If a pass is known to preserve ANF and we want to prove it, we can give it the type `ANFExpr → FreshM ANFExpr` — but this is opt-in, not required.

---

## 3. Fresh Variable Supply

```lean
structure FreshState where
  next : Nat := 0

abbrev FreshM := StateM FreshState

def freshVar (hint : String := "") : FreshM VarId := do
  let s ← get
  set { s with next := s.next + 1 }
  pure ⟨s.next, hint⟩

def runFresh (m : FreshM α) (start : Nat := 0) : α :=
  (m.run ⟨start⟩).1
```

Used by ANF normalization, DSL compilation, and any pass that introduces new bindings.

---

## 4. Analysis Functions

Building blocks for optimization passes. Implement first, test thoroughly.

### 4.1 Free Variables

```lean
/-- Set of free (unbound) variable IDs in an expression. -/
partial def freeVars : Expr → HashSet VarId
```

Key cases:
- `Var x` → `{x}`
- `Lit _` / `Builtin _` / `Error` → `{}`
- `Lam x body` → `freeVars(body) \ {x}`
- `Fix f body` → `freeVars(body) \ {f}`
- `Let binds body` → sequential scoping:
  - Fold over bindings left-to-right, accumulating bound vars
  - For binding `(xᵢ, eᵢ)`: free vars of `eᵢ` minus vars bound by `x₁...xᵢ₋₁`
  - Free vars of `body` minus all bound vars `{x₁...xₙ}`
  - Union everything
- `App f x` → `freeVars(f) ∪ freeVars(x)`
- `Case scrut alts` → `freeVars(scrut) ∪ ⋃ freeVars(alt_i)`

### 4.2 Occurrence Counting

```lean
/-- Count how many times variable v appears free in an expression. -/
partial def countOccurrences (v : VarId) : Expr → Nat
```

Drives inlining: 0 uses → dead code. 1 use → safe to inline. Many uses → only inline values.

Must respect Let scoping: if `v` is shadowed by a Let binding, occurrences under that binding don't count.

### 4.3 Substitution

```lean
/-- Capture-avoiding substitution: replace free occurrences of v with replacement. -/
partial def subst (v : VarId) (replacement : Expr) : Expr → FreshM Expr
```

Since we use unique IDs, capture is rare — but the implementation must alpha-rename binders when a collision is possible. `FreshM` provides new names.

Must respect Let scoping: if a Let binding shadows `v`, don't substitute under it.

### 4.4 Expression Size

```lean
/-- Node count. Used for inlining heuristics. -/
partial def exprSize : Expr → Nat
```

### 4.5 Alpha-Equivalence

```lean
/-- Are two expressions equal up to consistent variable renaming? -/
def alphaEq : Expr → Expr → Bool
```

Needed for CSE. Implementation: convert both to a canonical form (e.g., sequentially numbered de Bruijn) and compare structurally.

### 4.6 Helpers

```lean
/-- Peel nested App into (head, [args]).
    uncurryApp (App (App f a) b) = (f, [a, b]) -/
def uncurryApp : Expr → Expr × List Expr

/-- Is this a closed expression (no free variables)? -/
def isClosed (e : Expr) : Bool

/-- Does a Fix actually use its self-reference?
    If not, it can be simplified to just the body. -/
def fixIsRecursive (f : VarId) (body : Expr) : Bool
```

---

## 5. ANF Normalization

Transforms arbitrary MIR into A-Normal Form by inserting Let bindings for non-atomic sub-expressions in argument positions.

### 5.1 Core Helper

```lean
/-- If e is atomic, return it unchanged.
    Otherwise, let-bind it and return the fresh variable. -/
def anfAtom (e : Expr) : FreshM (Expr × (Expr → Expr)) := do
  if e.isAtom then
    pure (e, id)
  else
    let v ← freshVar "anf"
    pure (Expr.Var v, fun body => Expr.Let [(v, e)] body)
```

### 5.2 The Normalizer

```lean
partial def anfNormalize : Expr → FreshM Expr
  | Expr.App f x => do
    let f' ← anfNormalize f
    let x' ← anfNormalize x
    let (fAtom, fWrap) ← anfAtom f'
    let (xAtom, xWrap) ← anfAtom x'
    pure (fWrap (xWrap (Expr.App fAtom xAtom)))

  | Expr.Force e => do
    let e' ← anfNormalize e
    let (atom, wrap) ← anfAtom e'
    pure (wrap (Expr.Force atom))

  | Expr.Case scrut alts => do
    let scrut' ← anfNormalize scrut
    let (atom, wrap) ← anfAtom scrut'
    let alts' ← alts.mapM anfNormalize
    pure (wrap (Expr.Case atom alts'))

  | Expr.Constr tag args => do
    let args' ← args.mapM anfNormalize
    let results ← args'.mapM anfAtom
    let atoms := results.map Prod.fst
    let wraps := results.map Prod.snd
    let inner := Expr.Constr tag atoms
    pure (wraps.foldr (· ·) inner)

  | Expr.Let binds body => do
    let binds' ← binds.mapM fun (v, e) => do
      let e' ← anfNormalize e
      pure (v, e')
    let body' ← anfNormalize body
    pure (Expr.Let binds' body')

  | Expr.Fix f body => do
    let body' ← anfNormalize body
    pure (Expr.Fix f body')

  | Expr.Lam x body => do
    let body' ← anfNormalize body
    pure (Expr.Lam x body')

  | Expr.Delay e => do
    let e' ← anfNormalize e
    pure (Expr.Delay e')

  -- Atoms and Error are already normal
  | e => pure e
```

### 5.3 Proof-Producing Wrapper

```lean
/-- Normalize to ANF and produce the subtype with proof. -/
def anfNormalizeProof (e : Expr) : FreshM ANFExpr := do
  let normalized ← anfNormalize e
  -- The proof obligation: anfNormalize produces ANF output.
  -- This can be proven as a theorem about anfNormalize,
  -- or checked at runtime as a fallback:
  match normalized.toANF? with
  | some anf => pure anf
  | none => panic! "anfNormalize bug: output is not ANF"
```

The ideal endgame is a theorem `anfNormalize_isANF : ∀ e, (anfNormalize e).isANF = true`, eliminating the runtime check. This can be done incrementally — start with the runtime check, prove the theorem later.

---

## 6. Pretty Printer

Essential for debugging. Implement early.

### 6.1 Example Output

```
-- Sequential let:
let a = foo
    b = add a 1
    c = add a b
in
mul b c

-- Fix:
fix fac = λn.
  let isZero = eq n 0
  in
  force (ifThenElse isZero
    (delay 1)
    (delay
      let n1 = sub n 1
          facN1 = fac n1
      in
      mul n facN1))

-- Recursive function bound and applied:
let fac = fix self = λn. ...
in
fac 10
```

### 6.2 Implementation

```lean
/-- Render an Expr as a human-readable string. -/
def pretty : Expr → String

/-- Render with indentation. -/
def prettyIndent (indent : Nat) : Expr → String
```

Rules:
- Variables: use `hint` if non-empty, else `v{uid}`
- Builtins: short name (e.g., `add`, `mul`, `eq`, `ifThenElse`)
- Constants: `42`, `true`, `#deadbeef`, `"hello"`
- Let groups: align bindings, show all on separate lines
- Fix: `fix f = body`
- Lam: `λx. body`
- Nested Apps: `f a b c` (uncurried for readability)

---

## 7. MIR → UPLC Lowering

### 7.1 Core Translation

```lean
/-- Lowering environment: stack of bound VarIds.
    Head = innermost binding = de Bruijn index 0 (UPLC is 1-indexed). -/
partial def lower (env : List VarId) : Expr → Option Term
```

| MIR | UPLC | Notes |
|---|---|---|
| `Var x` | `Term.Var (indexOf x env + 1)` | 1-indexed |
| `Lit c` | `Term.Constant c` | Direct |
| `Builtin b` | `Term.Builtin b` | Direct |
| `Lam x body` | `Term.Lam 0 (lower (x :: env) body)` | Push x |
| `App f x` | `Term.Apply f' x'` | Lower both |
| `Force e` | `Term.Force e'` | Direct |
| `Delay e` | `Term.Delay e'` | Direct |
| `Constr tag args` | `Term.Constr tag args'` | Lower all |
| `Case scrut alts` | `Term.Case scrut' alts'` | Lower all |
| `Error` | `Term.Error` | Direct |
| `Let binds body` | Nested let-as-application | See 7.2 |
| `Fix f body` | Z combinator | See 7.3 |

### 7.2 Let Lowering

`Let [(x₁, e₁), (x₂, e₂), (x₃, e₃)] body` lowers as sequential nested applications:

```
(λx₁. (λx₂. (λx₃. body') e₃') e₂') e₁'
```

Each binding becomes a `(λxᵢ. rest) eᵢ` wrapping. Lowered left-to-right: `x₁` is outermost, bound first. This matches the sequential scoping — `e₂` can reference `x₁`, `e₃` can reference `x₁` and `x₂`.

The important implementation detail is the environment used for each RHS:
- `e₁` is lowered under `env`
- `e₂` is lowered under `x₁ :: env`
- `e₃` is lowered under `x₂ :: x₁ :: env`
- `body` is lowered under `x₃ :: x₂ :: x₁ :: env`

So while the final syntax is a right-nested chain of applications, the lowering logic should conceptually walk the bindings left-to-right, extending the environment after each binder for subsequent RHSs.

One clean implementation is:

```lean
partial def lowerLet (env : List VarId) : List (VarId × Expr) → Expr → Option Term
  | [], body => lower env body
  | (x, rhs) :: rest, body => do
      let rhs'  ← lower env rhs
      let rest' ← lowerLet (x :: env) rest body
      pure (Term.Apply (Term.Lam 0 rest') rhs')
```

This avoids a subtle bug: a naive "lower every RHS first, then fold right" implementation would lose the fact that later RHSs see earlier binders.

### 7.3 Fix Lowering

`Fix f (Lam x e)` lowers to the Z combinator (strict/call-by-value safe):

```
(λs. e'[f := λv. s s v]) (λs. e'[f := λv. s s v])
```

Steps:
1. Introduce a fresh variable `s` for the self-application parameter
2. In the body `e`, replace occurrences of `f` with `λv. s s v` (eta-expanded self-application)
3. Wrap in `λs. ...`
4. Self-apply: `(λs. ...) (λs. ...)`

The eta-expansion `λv. s s v` (instead of bare `s s`) is essential for call-by-value: it prevents infinite self-application from being evaluated eagerly.

When `Fix f body` where `body` is not a `Lam` (unusual but possible — e.g., `Fix f (Delay ...)`), fall back to the general encoding: `(λf. f) ((λs. body'[f := s s]) (λs. body'[f := s s]))`.

### 7.4 Future: Multiple Fix Strategies

Later, we can select encoding per-Fix:

| Strategy | Code | Tradeoff |
|---|---|---|
| Z standard | `(λs. e'[f:=λv. s s v]) (λs. e'[f:=λv. s s v])` | Balanced |
| Z compact | `(λr. r r) (λr. e'[f:=λv. r r v])` | Smaller, extra redex |
| Z inline | `(λs. e'[f:=λv. s s v]) (λs. e'[f:=λv. s s v])` with `e'` inlined | Faster, larger |

For now, Z standard is the default.

---

## 8. File Structure

```
Moist/
└── MIR/
    ├── Expr.lean       -- VarId, Expr, FreshM, isAtom, isValue, isANF, ANFExpr
    ├── Analysis.lean   -- freeVars, countOccurrences, subst, exprSize, alphaEq, helpers
    ├── ANF.lean        -- anfNormalize, anfAtom, anfNormalizeProof
    ├── Pretty.lean     -- pretty printer
    ├── Lower.lean      -- MIR → UPLC Term (including Fix/Z combinator lowering)
    └── Test.lean       -- tests for all of the above
```

---

## 9. Implementation Order

### Step 1: `Expr.lean` — Core Types

Define:
- `VarId` with `BEq`, `Hashable`, `Repr`
- `Expr` inductive
- `FreshState`, `FreshM`, `freshVar`, `runFresh`
- `isAtom`, `isValue`

Note: `isANF` depends on `freeVars` (for the `noSelfRef` check), so it lives in `Analysis.lean` or is forward-declared. Alternatively, `isANF` can initially omit the `noSelfRef` check and add it once `Analysis.lean` exists. Full scope validation, if added later, should remain separate from `isANF`.

Depends only on `Moist.Plutus.Term` (for `Const`, `BuiltinType`, `BuiltinFun`).

**Deliverable:** Types compile. We can construct MIR expressions by hand.

### Step 2: `Pretty.lean` — Pretty Printer

Implement `pretty` / `prettyIndent`. Builtin name mapping. Constant rendering.

**Deliverable:** `#eval pretty expr` shows readable output.

### Step 3: `Analysis.lean` — Core Analysis

Implement in order:
1. `freeVars` (respecting sequential Let scoping)
2. `noSelfRef` (using `freeVars`)
3. `countOccurrences` (respecting Let scoping)
4. `exprSize`
5. `subst` (capture-avoiding, respecting Let scoping)
6. `alphaEq`
7. Helpers: `uncurryApp`, `isClosed`, `fixIsRecursive`
8. `isANF` and `ANFExpr` (now that `freeVars` / `noSelfRef` are available)
9. Optional later: `isWellScoped` / `validate` for full scope checking

Each function gets inline `#eval` tests on hand-built expressions.

**Deliverable:** Can analyze, substitute, compare MIR expressions. `ANFExpr` subtype is usable.

### Step 4: `ANF.lean` — A-Normalization

Implement `anfAtom`, `anfNormalize`, `anfNormalizeProof`.

Test:
- Non-ANF input → ANF output (verify `isANF = true`)
- Already-ANF input → unchanged (idempotent)
- Verify no self-referential bindings are introduced
- Verify semantics preserved (same structure modulo let insertion)

**Deliverable:** Raw MIR → ANFExpr with proof.

### Step 5: `Lower.lean` — MIR → UPLC

Implement `lower` incrementally:
1. Atoms: Var (de Bruijn lookup), Lit, Builtin
2. Lam, App
3. Force, Delay
4. Constr, Case
5. Error
6. Let: sequential desugaring to nested lambda-application
7. Fix: Z combinator lowering

Test: hand-build MIR programs, lower to UPLC, encode via `encode_program`, compare hex with known-good values from `Encode.lean`.

**Deliverable:** End-to-end MIR → hex. Validates correctness of the full chain.

### Step 6: `Test.lean` — Consolidated Tests

- MIR → lower → encode → hex round-trips against known programs
- ANF normalization: idempotency, `isANF` holds, no self-ref introduced
- Free variable correctness on sequential Let chains
- Substitution capture-avoidance
- Pretty printer smoke tests

---

## 10. Example: Factorial in MIR

```lean
def factorialMIR : Expr :=
  let fac  := VarId.mk 0 "fac"
  let n    := VarId.mk 1 "n"
  let t0   := VarId.mk 2 "isZero"
  let t1   := VarId.mk 3 "n1"
  let t2   := VarId.mk 4 "facN1"
  -- let fac = fix fac = λn.
  --   let isZero = equalsInteger n 0
  --       -- (isZero doesn't reference itself ✓)
  --   in
  --   force (ifThenElse isZero
  --     (delay 1)
  --     (delay
  --       let n1    = subtractInteger n 1
  --           facN1 = fac n1
  --           -- n1 doesn't reference itself ✓
  --           -- facN1 references n1 (earlier binding, fine) but not itself ✓
  --       in multiplyInteger n facN1))
  -- in fac 10
  Expr.Let
    [(fac,
      Expr.Fix fac
        (Expr.Lam n
          (Expr.Let
            [(t0, Expr.App (Expr.App (Expr.Builtin .EqualsInteger) (Expr.Var n))
                           (Expr.Lit (.Integer 0, .AtomicType .TypeInteger)))]
            (Expr.Force
              (Expr.App
                (Expr.App
                  (Expr.App (Expr.Builtin .IfThenElse) (Expr.Var t0))
                  (Expr.Delay (Expr.Lit (.Integer 1, .AtomicType .TypeInteger))))
                (Expr.Delay
                  (Expr.Let
                    [(t1, Expr.App (Expr.App (Expr.Builtin .SubtractInteger) (Expr.Var n))
                                   (Expr.Lit (.Integer 1, .AtomicType .TypeInteger))),
                     (t2, Expr.App (Expr.Var fac) (Expr.Var t1))]
                    (Expr.App (Expr.App (Expr.Builtin .MultiplyInteger) (Expr.Var n))
                              (Expr.Var t2)))))))))]
    (Expr.App (Expr.Var fac) (Expr.Lit (.Integer 10, .AtomicType .TypeInteger)))
```

Note the inner Let: `[(t1, sub n 1), (t2, fac t1)]`. Here `t2`'s RHS references `t1` (an earlier binding — allowed by sequential scoping). Neither `t1` nor `t2` references itself (the no-self-ref constraint holds). This is valid.

Pretty-printed:
```
let fac = fix fac = λn.
            let isZero = eq n 0
            in
            force (ifThenElse isZero
              (delay 1)
              (delay
                let n1    = sub n 1
                    facN1 = fac n1
                in
                mul n facN1))
in
fac 10
```

---

## 11. Open Questions

1. **Should Let bindings carry inline hints?**
   A small metadata field letting the DSL communicate "always inline" / "never inline" / "default". Useful for sharing guarantees. Low cost, easy to add later if needed.

2. **Lam arity: always single-arg?**
   Yes. Multi-arg lambdas are nested single-arg Lams. Arity merging (collapsing `Lam x (Lam y (Lam z body))` into a single multi-arg UPLC lambda) can happen during lowering. Keeps MIR simple.
