# Checked list branches: further general MIR optimizations

A subsequent [soundness audit](MIR-New-Passes-Soundness-Audit.md) found and fixed
an interacting known-constructor case bug. The checked-branch passes and all
benchmark numbers below remain unchanged.

## Execution budgets

These are additional improvements over the production default **after** the
static-argument and recursive Boolean-result optimizations. Before scripts are
frozen in `benchmarks/checked-branches-baseline/`; the older real-validator and
general-recursion benchmark artifacts remain unchanged. No validator names,
ledger field numbers, token values, or benchmark arguments occur in the passes.
Scripts are compiled before their benchmark arguments are supplied.

Both passes now run by default. CPU and memory are the primary criteria;
size-oriented builtin sharing and constant pooling remain separately selectable.
Before and after use the same native Plutuz evaluator, cost model, arguments,
and resource limits.

| Workload | CPU before → after | CPU saved | Memory before → after | Memory saved |
|---|---:|---:|---:|---:|
| Voting: multiple inputs | 15,072,549 → 12,681,744 | 15.86% | 36,530 → 29,946 | 18.02% |
| Voting: eighth input matches | 41,091,279 → 33,556,620 | 18.34% | 105,200 → 84,648 | 19.54% |
| Vesting: full withdrawal | 33,572,726 → 28,695,116 | 14.53% | 100,136 → 86,368 | 13.75% |
| Vesting: midpoint withdrawal | 46,507,689 → 39,915,461 | 14.17% | 127,797 → 109,373 | 14.42% |

Certifying is unchanged: it has no applicable traversal pattern. All 63 existing
validator scenarios and 36 accepting generated Voting workloads preserve their
outcome without increasing CPU or memory. Failure paths are included as
regression checks, not as a ranking of rejection performance. Resource dominance
outside these workloads is not claimed.

Size also falls: Voting **207 → 180** raw Flat bytes and Vesting **917 → 804**;
Certifying stays **343**. These numbers exclude CBOR wrapping.
The resulting unapplied scripts are archived in `benchmarks/checked-branches-current/`.

## 1. Reuse branch knowledge for deconstruction

The remaining validator loops repeatedly selected a nonempty list branch and
then separately called `HeadList` and `TailList` on that same list. Even when an
unknown helper parameter cannot be assumed to be a list, a successful runtime
discriminator supplies that evidence for its selected branch.

```text
nonempty branch of checked xs:
  let head = HeadList xs
  let tail = TailList xs
  body
             ↓
nonempty branch of checked xs:
  Case xs [λhead. λtail. body]
```

`fuseCheckedListBranches` recognizes adjacent projections on the same bound
variable inside the nonempty branch of `Case (NullList xs)` or inside a literal
delayed nonempty argument of `ChooseList`. It retains the original discriminator
and its runtime type check. Native case deconstruction supplies both fields
without separate projection builtins and their intermediate applications.

Safety conditions:

- Facts belong only to the selected nonempty branch. Empty branches retain
  their original errors. Unknown parameters gain no facts from Lean annotations.
- ChooseList arguments are strict. Its nonempty fact applies **inside a literal
  delay**, never to an eager expression used to compute that argument.
- Both projections must be adjacent, head then tail, on the same already-bound
  list. Intervening effects and arbitrary producers are not reordered.
- Binder uniqueness is established before traversal. Shadowed identifiers and
  differing identifier origins cannot inherit the wrong fact. Captured facts
  refer to immutable values; rebinding another worker parameter is not evidence.
- Previously evaluated selector/projection aliases may resolve to genuine
  builtin heads. Resolution is bounded; unresolved or malformed protocols are
  left alone. Original strict bindings are retained.

## 2. Remove delayed selector overhead, not validation

`lowerDelayedListChoices` applies this general selection rewrite:

```text
Force (ChooseList xs (Delay empty) (Delay nonempty))
             ↓
Case (NullList xs) [nonempty, empty]
```

The source must have exactly the two builtin forces, three arguments, an outer
force, and two literal delayed branches. The input is still evaluated exactly
once before the chosen branch. Both builtins reject non-list inputs, including
integers, Booleans, pairs, constructors, functions, and data-encoded lists that
are not builtin lists. Unlike replacing the selector with `Case xs` directly,
the new discriminator does not accidentally accept those other runtime shapes.
Removed delays are values; their allocation cannot emit a trace, fail, or force
the unselected branch. Partial applications and eager branch arguments do not
match this rewrite.

The resulting NullList branch feeds the first pass. The combined driver runs
late in `Advanced.structural`, after existing structural rewrites and before
Fix lowering and final allocation packing, so earlier inlining cannot undo the
deconstruction improvement.

## Independent attribution

`benchmarks/mir-checked-branches.csv` records frozen default, fusion-only,
selector-only, and both passes. For Voting with multiple inputs:

| Profile | CPU | Memory |
|---|---:|---:|
| Frozen previous default | 15,072,549 | 36,530 |
| Branch deconstruction only | 13,315,671 | 31,346 |
| Delayed selector only | 14,438,622 | 35,130 |
| Both, production default | 12,681,744 | 29,946 |

The companion scaling CSV has the same four profiles for 36 generated accepting
searches. The runner checks each profile's result and both resource budgets
against the frozen script. It additionally requires byte identity between its
reconstructed pre-pass baseline and the immutable baseline, and between its
combined candidate and the actual production compiler. A future pipeline
change that invalidates either attribution fails explicitly instead of silently
changing what “before” or “combined” means.

`mir-checked-branches-fusion-only.csv` preserves the first isolated experiment.
`real-validator-checked-branches-current.csv` records current default, unoptimized,
size-oriented and reported upstream profiles. As in the preceding reports,
upstream Plutarch/Plinth costs use a different model configuration; those rows
are not evidence of an apples-to-apples cross-language CPU ranking. The local
before/after and ablation comparisons do use the same model.

## Soundness evidence and limits

Final validation: **460 full-suite tests passed, zero failed**; all nine Ptah
smoke checks passed. The verified optimizer and the 21-lemma axiom audit build
successfully. Re-running both ablation benchmarks reproduces the archived CSVs
byte-for-byte, and all archived checksums validate.

The new differential suite checks standalone passes and full production/size
compilation against unoptimized execution. It covers data, integer and pair
lists; malformed runtime shapes; empty-list projection errors; eager arguments;
incorrect force protocols; evaluation/trace order; aliases and shadowing;
captured delays; partial selectors; recursive sums over lengths 0–32; and
selected versus unselected divergence. Native results and Lean CEK trace/result
observations are compared separately. This is differential evidence, not a
proof that the two evaluators agree on every runtime representation.

Four additional kernel-checked CEK join lemmas cover delayed selection on
data/generic lists, selection for an arbitrary CEK value (including rejection of
non-lists), and nonempty generic-list deconstruction, with arbitrary environments
and continuation stacks. All 21 local advanced-redex lemmas depend
only on `propext` and `Quot.sound`, not `sorryAx` or new axioms. They prove local
schemas, **not** branch-fact analysis, alias resolution, traversal, lowering or
the complete pipeline. The pre-existing legacy budget-exhaustion axiom remains
outside this local proof module; no whole-compiler formal verification claim is
made.

The existing validator differential tests also retain 309 validation scenarios
and 2,280 malformed-context comparisons across compilation profiles. A new
resource regression test freezes this immediate preceding default for all 99
measured workloads.

## Reproduce

Run from the repository root with the existing pinned toolchain and native FFI:

```sh
lake build tests checked_branch_bench validator_comparison ptah_test \
  Moist.Verified.VerifiedOptimize Test.MIR.Opt.AdvancedAxioms
.lake/build/bin/tests mir/opt/unit/checked-branches
.lake/build/bin/checked_branch_bench
.lake/build/bin/checked_branch_bench --scaling
.lake/build/bin/tests
.lake/build/bin/ptah_test
.lake/build/bin/validator_comparison
shasum -a 256 -c docs/benchmarks/mir-checked-branches.sha256
```

Native evaluator: Plutuz `33b812dbcf88f6851286e54cb93a4a443353f94c`,
variant C/default costs; comparison sources remain the unchanged checkout at
`e21532661107f5d4feb380f9b1dcdf3ddb3b023f`. No historical benchmark snapshot was
regenerated in place.
