# Continued MIR optimization audit

The later non-arithmetic pass work is documented in `MIR-Structural-Optimization.md`:
pair/list deconstruction, call-state cleanup, frozen validator baselines, and
external ablations. The counts below describe this earlier checkpoint.

## Result

Three additional optimization families are active in the CPU/memory-oriented
pipeline: checked arithmetic identities, checked Data round trips, and
branch-local Boolean propagation. Size-oriented controls remain separate.

The audit also reproduced and fixed a compilation-validation bug: dead-code
elimination could hide unbound variables or invalid Fix bodies before lowering
checked them. This is a compiler input-validation defect, not a claim of a
ledger exploit or changed behavior of well-formed closed programs.

Validation now reports **431 full-suite tests and 49 focused audit tests passing**.
The 129,024 generated comparisons and previous 18,432 comparisons still pass.
There are **5,004 new native result/error comparisons and 5,004 corresponding
Lean trace comparisons**, with runtime inputs withheld from optimization.
Seven additional kernel-checked local rewrite schemas bring that total to 13.

No global optimality, whole-pipeline formal certificate, or universal budget
non-increase is claimed. The legacy invalid `budget_exhaustion` axiom remains
unresolved and is not used by any of these 13 local proofs.

## Audit context and guards

These records extend `MIR-Optimization-Context.md`. They inherit its A1–A5:
finite expressions; lexical values for bound variables; origin-aware VarIds;
sequential nonrecursive Lets; and strict left-to-right evaluation. Source type
annotations on function parameters are not runtime validation evidence.

Shared external-boundary risks remain: the Lean CEK loses some constant type
annotations; the pinned native evaluator is not every ledger era; and equal
unbounded results/traces do not imply equal behavior at an arbitrary finite
budget. Native tests and local machine joins address different parts of this
boundary rather than replacing each other.

### Successful builtin state analysis

**Purpose:** `builtinStateAfterSuccess` separates result-shape evidence from
totality. A builtin may guarantee an Integer result after successful evaluation
even when evaluating its arguments logs or fails.

**Inputs and assumptions:** MIR expressions, including untrusted operand
expressions; A1–A5; builtin force/application signatures from the pinned CEK.
This helper is private to the shape analysis, not a replacement for purity.

**Blocks:** Builtin nodes introduce their required protocol. Force and App
consume only matching type/value slots; saturation or a wrong slot returns no
remaining state. Why ignore argument purity here? Successful evaluation has
already evaluated the argument, but this says nothing about whether doing so
can be skipped. The Integer/Boolean whitelist is consulted only at the final
value argument, and `totalWithFacts` separately checks operand totality.

**Outputs and invariants:** an optional unsaturated protocol; no evaluation or
mutation; no promise of totality; no acceptance of invalid force order. The
existing `builtinRemainder` used by allocation/eta safety remains unchanged.

**Dependencies:** `Shapes.lean:29`, `knownInteger`, `knownBoolean`, and CEK
`expectedArgs`. Evidence flows into guarded rewrites, not into general purity.

### Checked conversion round trips

**Purpose:** `checkedRoundTrip` removes conversion work whose inverse already
succeeded in a dominating binding. It reuses the original evaluated value
without removing the validation that establishes the relationship.

**Inputs and assumptions:** lexical binding facts and an application of an
exact unary builtin to a Var; A1–A5; globally unique optimization binders.

**Blocks:** Resolve only the dominating variable and builtin-head aliases.
Recognize a paired conversion whose original operand is also a Var. Return
that original Var for IData/UnIData and BData/UnBData in both directions, or
ListData after UnListData and MapData after UnMapData. Why not arbitrary operand
expressions? Reconstructing one could duplicate effects or computation. Why
keep the producer? Its success is the runtime type check, including on invalid
inputs. The prefix-based dead-binding analysis still rejects deleting an
unproven validating producer.

**Outputs and invariants:** no extra evaluation; original lexical identity is
retained; no validation elision; no generic list element-type inference.

**Dependencies:** `Shapes.lean:175`, `resolveHead`, `uniqueOptimizationBinders`,
and the existing prefix-totality DCE. List/map unwrap-after-wrap elimination is
not added by this rule; it needs a separate typed-constant representation check.

### Integer identities and strict evaluation

**Purpose:** `integerIdentity` removes neutral or redundant arithmetic on
runtime-proven Integers. `retainEvaluation` preserves operand evaluation when
the arithmetic result becomes a constant.

**Inputs and assumptions:** direct binary builtin syntax; A1–A5; positive
Integer-result facts; correctly annotated literal identities. An arbitrary
source-typed parameter is insufficient evidence.

**Blocks:** Require both operands to produce Integers on success. Reduce +0,
-0, multiplication by 1, and division/quotient by 1. For multiplication by 0
and remainder/modulo by 1, retain an operand in a strict Let unless its totality
is independently established. For subtraction and comparisons of the same
already-evaluated variable, return the corresponding literal. Why restrict the
binary syntax? Expanding an aliased partial application could re-evaluate its
captured argument. Why exclude x/x? Zero still fails. Why keep an impure
Integer-producing operand? Result-shape evidence does not erase its Trace,
failure, or possible divergence.

**Outputs and invariants:** each retained operand runs once; original failures
and trace order persist; no division-by-zero cancellation; final binder
freshening prevents collisions from introduced strict Lets.

**Dependencies:** `Shapes.lean:196`, `Shapes.lean:206`, `knownInteger`,
`totalWithFacts`, and the existing hygienic simplification traversal.

### Branch-local Boolean facts

**Purpose:** repeated Case checks of an already-validated Boolean are redundant
inside a selected alternative. The traversal specializes those checks without
exporting a branch's assumption to a sibling or continuation.

**Inputs and assumptions:** a two-alternative Case of a Var; A1–A5; positive
Boolean-result evidence and unique binders.

**Blocks:** If the current environment already fixes the Boolean, visit only
the selected alternative. Otherwise visit the false and true alternatives
under separate immutable fact environments, then remove equal alternatives.
Why restrict to known Booleans? Native constructors, integer cases, and other
constant cases have different field and arity rules. How is scope retained?
Facts are passed down one alternative only; lambda shadowing has distinct
identities before the traversal starts.

**Outputs and invariants:** no sibling fact leakage; no source-type assumption;
the original validating producer remains strict; branch effects remain lazy.

**Dependencies:** `Shapes.lean:248`, `knownBoolean`, `resolveHead`, alpha equality,
and binder preparation. Existing optimizer iterations expose additional cases
created by lowering builtin Boolean choices.

## Confirmed validation defect

Before the repair, both of these failed regression groups were reproduced:

- `let unused = missing in 7`: raw lowering rejects the unbound variable,
  but optimization deleted the binding and compilation returned a program.
- An invalid `Fix self 7` in an unselected alternative or discarded delay
  was removed before the lowerer's required-outer-lambda check.

`Moist/MIR/Compile.lean:11` now performs a lightweight input traversal before
optimization. Its environment extends after each Let RHS, inside Lam bodies,
and inside structurally valid Fix bodies. Every alternative and delayed body
is validated regardless of reachability. It rejects missing variables, forward
references, self-references in nonrecursive Lets, and non-lambda Fix bodies.
It does not reject legal shadowing or require runtime argument typing.

Why validate here rather than weaken DCE? Optimization may legitimately erase
unused values when variables denote lexical values. The closed compilation API
must establish that precondition before invoking it. This preserves the
optimizer's usefulness on open terms while preventing invalid input from being
silently accepted by either Onchain or Ptah compilation.

The traversal returns only success or a descriptive compilation error; it
allocates no lowered program and performs no evaluation. Its invariants are
sequential scope, origin-aware identity, and validation of all Fix bodies.
It depends on VarId equality and mirrors `lower`'s structural scope rules.

## Verification

Commands completed successfully:

```sh
lake build Moist tests mir_audit ptah_test mir_opportunity_bench \
  Test.MIR.Opt.AdvancedAxioms Moist.Verified.VerifiedOptimize
.lake/build/bin/tests
.lake/build/bin/mir_audit
.lake/build/bin/ptah_test
.lake/build/bin/mir_opportunity_bench
git diff --check
```

- 431 full-suite tests; 49 focused audit tests; all nine Ptah smoke checks.
- The new runtime-input matrix compiles each script before applying any input.
  It covers all eight allocation-option combinations plus the isolated checked
  rewrite, wrong runtime types, large signed Integers, aliasing, shadowing,
  strict Trace order, and unselected failing branches.
- Six scalar/conversion/branch test groups also enforce actual simplification
  or measured CPU/memory/size reductions, rather than equivalence alone.
- Existing goldens pass without updates in this continuation.
- The seven new local CEK joins cover add-zero, multiply-one, checked Integer,
  ByteString, list and map reconstruction, and repeated Boolean Case. Arbitrary
  continuation stacks are retained; the data lemmas explicitly assume the
  correlated checked/original values in their environments.
- All 13 local lemmas depend only on `propext` and `Quot.sound`, with no
  `sorryAx`, compiler-trust axiom, or legacy budget axiom. These remain local
  schemas, not proofs of the entire fact analysis, traversal, or pipeline.

## Native measurements

`docs/benchmarks/mir-followup-native.csv` preserves all **990 rows** from 21
scripts, 45 input cases, and 22 configurations. Runtime inputs are excluded
from the compiled script. The new synthetic baselines are raw MIR lowering;
existing frontend-generated fixtures already contain earlier optimizations.
Do not treat these numbers as measured gains over the previous production
compiler on arbitrary real validators.

| New fixture, successful input | CPU baseline → default | Memory baseline → default | Flat bytes baseline → default |
| --- | --- | --- | --- |
| Checked arithmetic | 485,005 → 116,844 | 1,836 → 732 | 19 → 7 |
| Checked Data round trip | 212,143 → 164,844 | 1,264 → 1,032 | 12 → 10 |
| Repeated Boolean Case | 292,433 → 212,433 | 1,601 → 1,101 | 24 → 16 |

Both successful inputs for each fixture improve all three measurements. Their
wrong-type rejection inputs retain the measured baseline CPU and memory costs.
These are pinned native evaluator units, not a claim about current network
cost parameters. Historical CSVs remain untouched.
