# Proposal: a verified UPLC→SMT-LIB denotational compiler

**Stance.** This design is optimized to (a) reuse the existing `bigEval ≡ CEK` result as
the operational anchor, (b) keep the new correctness proof a *simulation* rather than a
from-scratch denotational-adequacy / logical-relation argument, and (c) ship in stages
where each stage is independently useful and provable. The trust compromise is fixed:
**trust z3's verdict, verify everything up to it.**

---

## 0. Goal and trust model

**Goal.** A Lean function `compile : Term → SmtExpr` plus a proof that the SMT it emits
faithfully represents the *real* (CEK) behaviour of the UPLC term, so that an `unsat` from
z3 on the negated property is a genuine theorem about the CEK.

**Trusted Computing Base (small and explicit):**
1. The Lean kernel.
2. **`z3_sound`** — one axiom: `z3_says_unsat e → Unsat e` (z3's verdict matches our Lean
   *meaning* of the formula). This is the accepted compromise.
3. The serializer `toSMTLIB : SmtExpr → String` and the claim that our `evalSmt` matches the
   SMT-LIB standard for the fragment we emit. Small, auditable, and differential-tested (§9).

**Proven (out of TCB):** `compile` adequacy, `bigEval ≡ CEK`, the property encoding,
fuel-sufficiency obligations.

Everything in §6 exists to discharge gap-1 (translation). Gap-2 (verdict) is `z3_sound`.
Gap-3 (printer/semantics match) is minimized + tested.

---

## 1. Pipeline

```
UPLC Term ──compile──▶ SymVal (symbolic value, carries SmtExpr) ──extract──▶ SmtExpr (a Bool)
                                                                       │
                  encodeProperty (∀ inputs. … = ok true) ─────────────┤
                                                                       ▼
                                                          toSMTLIB ─▶ z3 ─▶ unsat / sat+model
```

- `compile`/`symEval` is **`bigEval` with a symbolic value domain** (the load-bearing
  decision — §2).
- The result is reflected back to a Lean statement about the CEK via the adequacy theorem
  (§6) composed with `bigEval_iff_halt`.
- z3's `unsat` ⟹ (via `z3_sound`) the property holds for all inputs.

---

## 2. The five design decisions that make it tractable

1. **`symEval` mirrors `bigEval` structurally.** Same recursion, same fuel, same cases —
   only the *value domain* changes (`SmtExpr` constants instead of concrete `Const`). ⟹
   adequacy is a tight **simulation** (fuel induction + structural value relation), not a
   generic denotational adequacy proof.

2. **Defunctionalized closures.** `SymVal` keeps `VLam`-style `(Term, SymEnv)` closures,
   exactly like `CekValue`. ⟹ **no higher-order logical relation** is needed; the value
   relation is structural. Functions are *applied by the evaluator*, never by Lean, and
   never appear in the final SMT.

3. **Result-as-definedness.** Partiality (UPLC errors) is threaded as an SMT `Bool`
   "definedness" formula alongside the value, not a nested `Result` ADT. ⟹ the final query
   is `defined ∧ value = true`, which stays in base sorts and is SMT-friendly.

4. **Concrete control flow, first-order symbolic data.** Higher-order control (β,
   `Force`/`Delay`, `Case` on *statically-known* constructors) runs concretely in the
   compiler, *exactly* like `bigEval`. Only when symbolic data reaches a first-order
   observation (a comparison, `unConstrData`, a `Case` on a symbolic tag) does it become an
   SMT `match`/`ite`. **Symbolic choice of a *function* is refused at compile time**
   (returns `none`/"unsupported"). This is the precise supported fragment and it covers real
   validators.

5. **Bounded by fuel; unbounded symbolic recursion is refused, not mis-compiled.** `compile`
   carries a fuel bound (like `bigEval`). For static-control validators it fully resolves; if
   it would exceed fuel it returns `none` (so we never emit an unsound under-approximation).

---

## 3. The SMT domain

### 3.1 Syntax (`Moist/Smt/Syntax.lean`)

```lean
inductive SmtSort | int | bool | bytes | data        -- extend later
inductive SmtExpr
  | var   : String → SmtSort → SmtExpr
  | litI  : Int → SmtExpr      | litB : Bool → SmtExpr
  | bin   : BinOp → SmtExpr → SmtExpr → SmtExpr        -- +,-,*,fdiv,fmod,tdiv,tmod,≤,<,=
  | ite   : SmtExpr → SmtExpr → SmtExpr → SmtExpr
  | and_ | or_ | not_ : …                              -- Bool
  | dCon  : Int → List SmtExpr → SmtExpr               -- Data constructor (symbolic tag allowed)
  | dTag  : SmtExpr → SmtExpr                          -- Data → Int (tag selector)
  | dArg  : SmtExpr → Nat → SmtExpr                    -- field selector
  | dIsI | dIsConstr | … : SmtExpr → SmtExpr           -- testers
  | uf    : String → List SmtExpr → SmtExpr            -- uninterpreted (hashes, sigs)
```
`Data` is emitted as a recursive SMT-LIB datatype (z3/cvc5 support these). Keep the AST
**well-sorted by construction** where feasible (or carry a `sortOf` + a `WellSorted` predicate).

### 3.2 Semantics (`Moist/Smt/Semantics.lean`) — the Lean *meaning* of `SmtExpr`

The small `evalSmt` required for a deep embedding. It maps into a Lean model domain, not
into z3:

```lean
inductive SVal | I : Int → SVal | B : Bool → SVal | D : Plutus.Data → SVal   -- mirrors UPLC Const
abbrev Model := String → SVal                       -- assignment to free SMT vars
def evalSmt : SmtExpr → Model → Option SVal         -- Option = ill-sorted/partial (not on compiled exprs)
def Unsat (e : SmtExpr) : Prop := ∀ σ, evalSmt e σ ≠ some (.B true)
```
`evalSmt` is structural, and is the artifact whose fidelity to SMT-LIB is validated by
differential testing (§9). It is *the* definition `z3_sound` is stated against.

---

## 4. The compiler (`Moist/Compile/`)

### 4.1 Symbolic values — mirror of `CekValue`

```lean
inductive SymVal
  | sCon    : SmtExpr → SymVal                 -- a (possibly symbolic) constant
  | sLam    : Term → SymEnv → SymVal           -- closure, defunctionalized (= VLam)
  | sDelay  : Term → SymEnv → SymVal
  | sConstr : Int → List SymVal → SymVal       -- statically-known constructor
  | sBuiltin: BuiltinFun → List SymVal → ExpectedArgs → SymVal
abbrev SymEnv := List SymVal
structure SymOut where value : SymVal; defined : SmtExpr     -- definedness (error) flag
```

### 4.2 `symEval` — `bigEval` over `SymVal`

```lean
def symEval : Nat → SymEnv → Term → Option SymOut
```
Case-by-case it is `bigEval` with three deltas:
- **constants/builtins** produce `sCon (SmtExpr …)` and conjoin guards into `defined`
  (e.g. `divideInteger` adds `y ≠ 0`);
- **`Case`/destructors** dispatch *concretely* on `sConstr` (identical to `bigEval`), but on
  `sCon` of `data` sort emit an SMT `match`/`ite` over `dTag`/`dArg` and require first-order
  branch results (else `none`);
- **`Force`/`Delay`/`Apply`/`Lam`** are identical to `bigEval` (defunctionalized closures),
  so all higher-order structure is eliminated by compile time.

`extract : SymOut → Option SmtExpr` pulls the top-level `defined ∧ valueAsBool` for a
validator (whose result is a `Bool`).

### 4.3 Builtins (`Moist/Compile/Builtins.lean`)

A table `smtBuiltin : BuiltinFun → List SmtExpr → Option (SmtExpr × SmtExpr /-guard-/)`:
- Int arithmetic/comparison → native `bin`;
- `divide/mod/quot/rem` → `fdiv/fmod/tdiv/tmod` + `y ≠ 0` guard (exact denotations already
  established: `evalBuiltin_divideInteger` etc.);
- `ifThenElse` → `ite`; `chooseData/unConstrData/...` → tester/selector + guards;
- `equalsData` → SMT `=` on the `Data` datatype;
- bytestring/crypto → `uf` + optional axioms (v2).

Each entry comes with the **agreement lemma** used in §6.

---

## 5. Property encoding (`Moist/Compile/Reflect.lean`)

A validator `v` applied to symbolic inputs `x₁…xₙ` (fresh `var`s of the right sort,
including `data`). The proof obligation "always validates under precondition `P`":

```
assert (not (=> P  (and defined (= value true))))     -- z3 unsat ⟹ holds for all inputs
```
Bug-finding is the same without the `not` (sat ⟹ z3 hands a model = a concrete exploit,
**self-checked** against `bigEval`/CEK, so z3 is untrusted in that direction).

---

## 6. Correctness proof — the core

### 6.1 Concretization (turn symbolic into concrete *at a model* σ)

```lean
def γ  (σ : Model) : SymVal → Option CekValue      -- sCon e ↦ VCon (evalSmt e σ); sLam b ρ̂ ↦ VLam b (γE …); …
def γE (σ : Model) : SymEnv → Option CekEnv
```

### 6.2 The adequacy theorem (the deliverable)

State it as an **equation up to concretization**, so the proof is an induction, not a
relation-juggling exercise:

```lean
theorem symEval_adequate (σ : Model) :
    ∀ f ρ̂ t,
      (symEval f ρ̂ t).bind
        (fun o => guard (evalSmt o.defined σ = some (.B true)) *> γ σ o.value)
      = bigEval f (γE σ ρ̂) t
```
i.e. *"compile, then interpret at σ (taking the defined branch), equals `bigEval` on the
σ-concretized inputs."* Prove by **induction on fuel `f`**, then `cases t` — mirroring
`bigEval`'s own structure (so every case lines up 1:1). Sub-obligations:

- **Constants / `Var` / `Lam` / `Delay`:** `γ`/`evalSmt` commute with the constructor; immediate.
- **Builtins (per-builtin agreement lemma):**
  `evalSmt (smtBuiltin op …) σ = evalBuiltin op (γ-args …)` under the guard — the
  `evalBuiltin_*` facts, used as rewrite steps (ideally *proven*, not axiom'd; Risk R3).
- **`Apply` / `Force`:** β and force mirror `applyVal`/`forceVal` exactly (defunctionalized)
  — structural, reusing the closure relation implicitly via `γ`.
- **`Constr`:** field list — `bigEvalList`/`applyValList` analogues.
- **`Case` — the one genuinely new case:**
  - *concrete scrutinee* (`sConstr`): identical to `bigEval`'s dispatch.
  - *symbolic scrutinee* (`sCon` of `data`): the emitted `match` at σ selects the branch σ's
    tag determines; the lemma is `evalSmt (matchExpr) σ = evalSmt (branch_{tag σ}) σ`, and
    `bigEval` at σ takes that same branch. Needs `dTag/dArg` selectors to mirror
    `constToTagAndFields`/`alts[tag]?`. The first-order-result restriction is what keeps both
    sides in `sCon`.
- **Partiality:** `defined σ = false` ⟺ `bigEval` errors — reuses the error-correspondence
  reasoning from the failure corollaries.

### 6.3 Composition to the CEK (reuses existing work)

```lean
theorem compile_iff_cek (σ) :
    evalSmt (extract (symEval F ρ̂_inputs v)) σ = some (.B true)
      ↔ Reaches (init (apply v (γ-inputs σ))) (.halt (.VCon (.Bool true)))
```
by `symEval_adequate` ▸ `bigEval_iff_halt`. The failure side (`bigEval_fail_of_error` etc.)
gives the error/divergence correspondence for free.

### 6.4 End-to-end soundness (the usable theorem)

```lean
theorem validator_sound
    (hz3 : z3_says_unsat (toSMTLIB (encodeProperty v P)))      -- the trusted input
    : ∀ inputs, P inputs → Reaches (init (apply v inputs)) (.halt (.VCon (.Bool true))) := by
  have : Unsat … := z3_sound hz3                               -- the ONE axiom
  intro inputs hP; …                                          -- compile_iff_cek + this
```
TCB = `z3_sound` + printer/semantics-match + kernel. Everything else is a Lean proof.

### 6.5 Fuel obligation

For soundness we additionally need `symEval F … ≠ none` (it resolved). Either prove
`compile_total_of_staticControl : StaticControl v → ∃ F, symEval F … ≠ none` for the
supported fragment, or expose a runtime check ("compiled with fuel to spare") and make
`validator_sound` take it as a hypothesis (discharged per-validator by `decide`/`rfl`).
Pragmatic default: the latter.

---

## 7. Serialization + solver (`Moist/Smt/Print.lean`)

`toSMTLIB : SmtExpr → String` emitting the `Data` datatype decl,
`define-fun @Int.fdiv/@Int.fmod`, uninterpreted decls, and the assertion. Reuse the
z3-via-`IO.Process` plumbing already working in the benchmark harness (nix `z3`, parse
`unsat`/`sat`+model). No need to touch Blaster; this replaces Blaster's symbolic-execution
phase with our denotational compile.

---

## 8. Develop "prove first, emit second"

Internally, `symEval` is the proven object; the `SmtExpr` it carries is the deep embedding.
This means the whole compiler can be developed and tested against `bigEval` (in-Lean,
`#eval`) before any of the proof is done, and before z3 is in the loop. That de-risks
everything.

---

## 9. Validation strategy (continuous, not at the end)

1. **Differential test `symEval` vs `bigEval`:** random closed terms × random models σ;
   assert `(symEval … |>.interp σ) = bigEval … (γE σ …)`. Finds compiler bugs *and*
   `evalSmt`/printer bugs before proof effort is spent. (Same `#eval` technique used to
   validate the builtin denotations.)
2. **Validate `evalSmt` vs z3 on ground instances:** for closed (variable-free) `SmtExpr`,
   check `evalSmt e _ = (z3's evaluation of e)`. Empirically defends the printer/
   semantics-match TCB item.
3. **Cross-check residual vs Blaster:** the benchmark showed Blaster computes the same
   denotation; the emitted formula should be z3-equivalent to Blaster's. A regression oracle.
4. **Counterexample replay:** every `sat` model → run through verified `bigEval` to confirm
   the exploit (this path needs no trust at all).

---

## 10. Staged roadmap

| Stage | Scope | Proof |
|---|---|---|
| **v0** | λ + builtins + `Int`/`Bool`, **concrete control flow** (covers the arithmetic validators benchmarked) | `symEval_adequate` for this fragment (pure simulation, no symbolic dispatch) |
| **v1** | `Data` as SMT datatype + **symbolic `Case`/destructors** (first-order results) | the symbolic-dispatch cases (§6.2) |
| **v2** | bytestrings (`Seq`/`BitVec`) + crypto as `uf`+axioms | weaker/uninterpreted; modeling-heavy |
| **v3** | bounded recursion unrolling (+ optional k-induction / invariants) | unrolling adequacy; invariants out of v3 scope |

v0 already gives a *fully verified* path for the straight-line / arithmetic validator class,
end to end, with only `z3_sound` trusted.

---

## 11. Risks and explicit scope cuts

- **R1 — Symbolic higher-order branching.** Choosing a *function* by symbolic data is
  unsupported; `symEval` returns `none` (sound: refuses rather than mis-compiles). Mitigation:
  rare in validators; document and detect.
- **R2 — Unbounded symbolic recursion** (folds over attacker-sized lists). Out of scope
  through v3; refuse at compile time. Real fix is invariants / k-induction — a separate effort.
- **R3 — Builtin agreement as axioms.** Today `evalBuiltin_*` are axioms (the monolith won't
  reduce). For *end-to-end* verification these should be **proven**, which argues for
  refactoring `evalBuiltin` into per-builtin functions with `rfl` lemmas (one-time cleanup,
  helps everything else). Until then they are a small, `#eval`-validated TCB item.
- **R4 — Bytestrings.** SMT `Seq`/`BitVec` reasoning is weak; keep them uninterpreted-with-
  length where possible; do not over-promise crypto.
- **R5 — `evalSmt` ≠ SMT-LIB standard.** Minimized to a small structural function and
  defended by §9.2; this is the irreducible printer/semantics gap of the "trust z3"
  compromise.

---

## 12. Deliverables / module layout

```
Moist/Smt/Syntax.lean        -- SmtExpr, SmtSort, datatype decls
Moist/Smt/Semantics.lean     -- evalSmt, Unsat, z3_sound (the one axiom)
Moist/Smt/Print.lean         -- toSMTLIB + z3 IO (reuse benchmark harness)
Moist/Compile/SymValue.lean  -- SymVal, SymEnv, SymOut
Moist/Compile/Builtins.lean  -- smtBuiltin table + agreement lemmas
Moist/Compile/Compile.lean   -- symEval, extract
Moist/Compile/Adequacy.lean  -- γ, symEval_adequate, compile_iff_cek    ← the core proof
Moist/Compile/Reflect.lean   -- encodeProperty, validator_sound          ← the product
Test/Compile/Diff.lean       -- differential tests (symEval vs bigEval)
docs/uplc-smt/PLAN.md        -- this proposal
```

**Critical path:** `Syntax` + `Semantics` + `SymValue` + `Compile` (buildable +
`#eval`-testable) → `Diff` (catch bugs early) → `Builtins` lemmas → `Adequacy` (the bulk)
→ `Reflect` + `Print` → end-to-end on the benchmark validators.

---

## Summary

Build `symEval` as **`bigEval` over a symbolic value domain that carries `SmtExpr`**; keep
closures defunctionalized and control flow concrete so the only genuinely new proof
obligation is symbolic `Data` dispatch; prove `symEval` adequate to `bigEval` by
**fuel-induction simulation** and compose with the existing `bigEval ≡ CEK` theorem; emit
`SmtExpr` to z3 and trust only its `unsat` (one axiom `z3_sound`), with the small
`evalSmt`/printer gap defended by differential testing. v0 (arithmetic, concrete control) is
fully verified end to end; `Data` / symbolic-`Case` follow in v1.
