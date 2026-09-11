# General optimizations found in real validators

This is the static-argument/result-summary checkpoint. Additional production
improvements are measured separately in [Checked list branches](MIR-Checked-Branch-Optimization.md);
the benchmark numbers and frozen scripts in this report remain historical.

## Execution budgets first

These changes optimize general MIR patterns, not particular validator names,
currencies, datums, signatures, inputs or benchmark constants. They run by default.
Optional sharing/pooling remains separate; no size-oriented option was enabled
to obtain the results below.

**Before and after use exactly the same native evaluator, cost model, script
arguments and budget limits.** Before means the frozen production scripts from
the preceding real-validator comparison, not unoptimized MIR. Thus these are
additional gains beyond the optimization work already measured there.

| Real workload | CPU before → after | CPU reduction | Memory before → after | Memory reduction |
|---|---:|---:|---:|---:|
| Voting: NFT in pubkey input | 11,448,192 → 10,736,094 | 6.22% | 28,587 → 25,085 | 12.25% |
| Voting: multiple inputs | 16,260,696 → 15,072,549 | 7.31% | 42,533 → 36,530 | 14.11% |
| Certifying: register | 3,361,377 → 3,173,328 | 5.59% | 11,854 → 11,153 | 5.91% |
| Certifying: unregister | 7,491,645 → 7,303,596 | 2.51% | 23,491 → 22,790 | 2.98% |
| Certifying: delegate | 5,390,296 → 5,202,247 | 3.49% | 18,316 → 17,615 | 3.83% |
| Certifying: register and delegate | 5,506,629 → 5,318,580 | 3.41% | 18,717 → 18,016 | 3.75% |
| Vesting: full withdrawal | 34,064,775 → 33,572,726 | 1.44% | 102,737 → 100,136 | 2.53% |
| Vesting: partial midpoint | 47,191,738 → 46,507,689 | 1.45% | 131,598 → 127,797 | 2.89% |
| Vesting: multiple beneficiary outputs | 38,875,401 → 38,335,352 | 1.39% | 118,005 → 115,104 | 2.46% |

All 63 existing real-validator scenarios preserve their result and do not
increase either CPU or memory compared with the frozen default. This includes
failure paths as a regression guard, not a ranking of rejection performance.
Scripts are compiled without applying any benchmark arguments.

Size is secondary, but also improves: raw Flat bytes are Voting **237 → 207**,
Certifying **347 → 343**, Vesting **945 → 917**. No universal resource-dominance
claim is made outside the tested workloads.

## 1. Remove invariant recursive arguments

The Voting loops repeatedly passed currency/token values unchanged. Vesting's
searches, filters and folds likewise passed unchanged beneficiary, address or
reference arguments. The compiler lowered each to curried recursive calls with
avoidable application and parameter-binding work on every iteration.

The general transformation is:

```text
fix search = λkey. λitems. ... search key remaining ...
             ↓
λkey. fix worker = λitems. ... worker remaining ...
```

`Moist/MIR/Optimize/Advanced/Recursion.lean` moves each invariant leading
parameter outside the recursive worker. It recognizes no ledger types or
builtins. This is a conservative call-by-value form of the established
[static argument transformation](https://downloads.haskell.org/ghc/9.10.1/docs/users_guide/using-optimisation.html#ghc-flag-fstatic-argument-transformation).

Guards:

- Every recursive occurrence must be a direct call whose first argument is
  exactly that bound parameter. Changed constants, equivalent-looking
  expressions, traced arguments, aliases and escaped recursive functions are
  not accepted as evidence.
- At least one worker lambda remains. Moving the parameter must not force the
  function body when only a partial application is evaluated.
- Unique binders are established before analysis, including origin-aware
  identifiers and shadowing. Removed arguments are already-evaluated variables;
  the original caller still evaluates the initial argument, including errors
  and traces.
- Multiple invariant leading parameters can be removed, but non-leading
  invariant parameters are not reordered across dynamic arguments.

The compiler applies this before ANF obscures recursive application spines.
`#show_opt_trace` now displays the step explicitly.

## 2. Infer successful Boolean results across functions

The earlier optimizer knew comparisons return Boolean but lost this information
through recursive searches and local bindings. As a result, nested conditionals
retained `ifThenElse`, forcing and delay allocation even when the condition's
successful result could only be Boolean.

`Moist/MIR/Optimize/Advanced/Results.lean` provides bounded, conservative
post-success summaries for builtin protocols, sequential bindings, conditionals,
direct lambda applications and recursive functions. Existing checked Boolean
simplification then replaces the unnecessary selection/delay machinery.

The important distinction is **result type, not totality**. The entire condition
producer remains evaluated. A function which logs, fails or diverges must still
log, fail or diverge. Failed inference leaves the original code in place.

Recursive inference checks the function body assuming only that fully saturated
recursive calls return Boolean *if they succeed*. Every nonrecursive successful
exit must independently establish that result type. This is justified by
induction over a finite successful call tree, not by assuming termination.
Formal parameters are unknown, and shadowed outer facts are removed: knowing one
call receives Boolean is not enough if recursion can change that parameter's
type. Partial and over-applied recursive calls do not receive the summary.

The analysis is useful beyond recursion: Certifying's locally bound Boolean
decision also benefits, although it has no invariant recursive parameter to
remove. The pass is not a rewrite specific to NFT lookup or certificate tags.

## Attribution and verification

Final validation: **453 full-suite tests passed, zero failed** on the final
code; all nine Ptah smoke checks passed. The verified optimizer and existing
advanced-redex axiom-audit modules still build. All 99 measured workloads
preserve outcomes with non-increasing CPU and memory. Both historical and new
benchmark integrity manifests verify successfully.

The benchmark isolates the two optimizations:

- `mir-static-arguments-only.csv`: initial isolated static-argument experiment,
  compared with the then-current production default, before result summaries.
- `mir-general-recursion.csv`: frozen default, result summaries alone, both
  together. The runner checks that the combined program is byte-identical to
  the current production default, avoiding a hidden benchmark-only pipeline.
- `mir-general-recursion-scaling.csv`: the same Voting validator across 36
  accepting search-position/length cases, with runtime inputs withheld during
compilation.

The eight-input search with the NFT last costs **45,135,720 → 41,091,279 CPU**
and **126,209 → 105,200 memory** (8.96% and 16.65% reductions). All 36 scaling
cases also preserve the result without increasing either resource budget.

For Voting with multiple inputs, the isolated static-argument pass reduces CPU
by 624,000 and memory by 3,900. Summaries alone reduce CPU by 564,147 and memory
by 2,103; together they save 1,188,147 CPU and 6,003 memory. Certifying's gains
come from result summaries, not recursion removal.

Tests include effect ordering, initial argument evaluation, partial/over-
application, escaped recursion, identifier-origin collisions, shadowing,
changing argument types, incorrect recursive arities, and divergent workers.
432 generated recursive return-shape programs exercise Boolean, integer, Data,
constructor, delay, function and failing results with changing recursive state.
Each is checked with both the native evaluator and the Lean trace evaluator,
against standalone and combined transformations. The real-validator tests retain
their generated inputs, malformed-context checks and Unit-return requirement,
and now also assert non-increasing budgets against the frozen real scripts.

These analyses are not full formal proofs. The existing kernel-checked Boolean
selection join supplies a local rewrite lemma, but it does not prove the new
result-summary inference or the static-argument transformation. No new axioms,
proof placeholders or weakened purity predicates were introduced.

The historical Plinth/Plutarch results still use a different evaluator/cost
variant. They are not used to attribute these gains or tune individual cases.

## Further general opportunities

- **List-shape propagation through call boundaries:** helpers currently lose
  positive list evidence supplied by `unListData`/`unMapData`. Preserving that
  evidence could enable list-choice/deconstruction fusion inside workers.
  Unknown parameters must not simply be treated as lists: native Case also
  accepts other runtime types, unlike list builtins.
- **Loop-invariant worker allocation:** nested recursive helpers are still
  rebuilt in some loops. Hoisting could save allocations, but must respect
  captures, partial application and evaluation frontiers, and avoid charging
  unused branches. Broad unconditional hoisting is not justified by these data.
- **Non-leading static arguments:** the current safe prefix rule misses some
  accumulator-first APIs. A wrapper could expose invariant later arguments,
  provided its initial-call overhead pays off and strict argument order remains
  unchanged. No validator-specific threshold is introduced here.

## Reproduction

```sh
lake build tests recursion_bench validator_comparison
.lake/build/bin/tests mir/opt/unit/recursion mir/eval/comparison
.lake/build/bin/recursion_bench > /tmp/mir-general-recursion.csv
.lake/build/bin/recursion_bench --scaling > /tmp/mir-general-recursion-scaling.csv
.lake/build/bin/validator_comparison /tmp/general-validator-scripts > /tmp/current-validator-comparison.csv
.lake/build/bin/tests
```

Do not overwrite `docs/benchmarks/real-validators/`: those scripts and inputs are
the immutable before-snapshot. The initial comparison report remains historical.
