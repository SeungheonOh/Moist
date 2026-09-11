# Production MIR optimization implementation

Historical implementation checkpoint. For the maintained schedule and current
proof inventory, see [MIR optimization maintenance](MIR-Optimization.md).

The subsequent audit is recorded in `MIR-Optimization-Followup.md`: three more
rewrite families, input-validation repairs, 431 tests, and 13 local proofs.
The measurements and counts below describe the initial integration checkpoint.

## Status

The ten pass families from the timed investigation are implemented in production
modules. Both Onchain `compile!` and Ptah compilation use the same pipeline.
Defaults prioritize CPU/memory as requested; script-size pooling and speculative
builtin-state sharing remain separately selectable.

**Verification is substantial but not a whole-pipeline formal certificate:**
424 tests pass, 129,024 additional generated comparisons pass, and six local
CEK rewrite schemas have kernel-checked proofs. The legacy false
`budget_exhaustion` axiom remains outside those new proofs. No claim of universal
resource non-increase or globally optimal UPLC is made.

Work remains in `/Users/sho/fun/moist-mir-audit`, based on `cc23952`, with all
previous audit repairs preserved. The original checkout is untouched. No push
or unsigned-commit fallback is performed.

## Production paths

| Module | Responsibility |
| --- | --- |
| `Moist/MIR/Optimize/Advanced/Constants.lean` | Guarded scalar folding and typed Data-constructor folding |
| `Moist/MIR/Optimize/Advanced/Shapes.lean` | Boolean Case lowering, force/case/delay cancellation, dominating shape facts, totality-based DCE, equal-branch removal, list head/tail fusion |
| `Moist/MIR/Optimize/Advanced/Allocations.lean` | Delayed-value sharing, nonrecursive Fix removal, safe application packing, closed builtin-state sharing, large-constant pooling |
| `Moist/MIR/Optimize/Advanced.lean` | Pass scheduling and allocation options |
| `Moist/MIR/Compile.lean` | Shared optimization, checked pre-lowering cleanup, lowering, and final allocation stage |
| `Moist/Onchain/Compile.lean` | Onchain entry points and `set_option` controls |
| `Moist/Ptah/Compile.lean` | Ptah entry point and explicit option forwarding |

The earlier test prototype now delegates to production implementations; there
is no separate optimizer copy for the benchmark to accidentally test instead.

### Ordering

1. Establish binding hygiene, share safe delayed values, and eliminate Fix nodes
   whose recursive binder is unused.
2. Run the existing float/beta/ANF pipeline with checked shapes, bounded folding,
   and list fusion before CSE/DCE/inlining.
3. Perform checked pre-lowering cleanup, stopping at alpha-equivalence or four
   rounds. Preserve strict validation even when its result becomes unused.
4. Lower Fix and all ordinary MIR to UPLC.
5. If requested, lift that closed result for final safe packing, builtin sharing,
   and constant pooling, then lower directly. Do not run inverse CaseMerge or
   atom inlining after this stage.

Fresh supplies account for the entire prepared expression. The debug optimizer
trace follows the actual production scheduling; generated tests compare its
last expression with the normal optimizer.

## Defaults and controls

| Setting | Default | Reason |
| --- | --- | --- |
| Checked shapes/folding/fusion/delay sharing/dead Fix | Enabled | Guarded semantic simplification |
| Final application packing | Enabled | CPU/memory-oriented representation for safe spines of at least three arguments |
| Closed builtin-state sharing | Disabled | Can regress short or rejecting paths; select after profiling |
| Large-constant pooling | Disabled | Trades lookup/allocation cost for smaller scripts |
| Minimum builtin occurrences when sharing | 2 | Explicitly configurable in the API |
| Minimum encoded constant size for pooling | 32 bytes | Uses Flat size rather than one-node AST size |

Onchain controls work with both `compile! validator` and `validator.compile!`:

```lean
set_option moist.optimize.poolConstants true in
def smallerValidator := compile! validator
```

Other Boolean controls are `moist.optimize.packApplications` and
`moist.optimize.shareBuiltinStates`. Per-declaration `set_option ... in` avoids
changing unrelated compilations.

Explicit API controls:

```lean
Moist.MIR.compileOptimized mir
  (options := { packApplications := true, poolConstants := true })

Moist.Ptah.compile term
  (options := { shareBuiltinStates := true, minimumBuiltinUses := 3 })
```

`Moist.Onchain.compileToUPLC` and `compileExprToUPLC` also accept the same
options explicitly. `prepareForLowering` exposes the optimized MIR before
lowering. Callers manually chaining `optimizeExpr` and `lowerExpr` should use
`compileOptimized` to receive the final allocation stage as well.

These are semantic-preservation options, not proofs that a selected profile is
cheaper for every possible input. In particular, packing can evaluate safe
arguments before an earlier failure; sharing can allocate before an unselected
branch. Both preserve unbounded behavior but can change resource consumption.

## Guard obligations

| Transformation | Conditions retained in production |
| --- | --- |
| Scalar folding | Whitelist; literal type agreement; correct force/argument protocol; successful evaluation; bounded operands and intermediate/result values; no Trace or cryptographic folding |
| Data folding | Explicit Data/list-Data annotations; valid bounded constructor tags; bounded serialized output; no generic empty-list type guessing |
| Boolean Case / force-case-delay | Positive Boolean result evidence; pure eager alternatives; no assumption that an external source-typed argument is a valid runtime Bool |
| Shape-based DCE | Facts from dominating evaluated bindings; totality checked against each binding's prefix, not the final environment; retain validating producers and effectful scrutinees |
| List fusion | Adjacent matching HeadList/TailList uses of the same already evaluated, proven-list variable; cons binds exactly two fields; nil still fails |
| Delay sharing | Every use is through Force; delayed body is total/effect-free; unique binders before scope-sensitive replacement |
| Dead Fix | Required outer lambda remains valid; recursive identifier genuinely absent from its free variables; shadowing respected |
| Application packing | At least three arguments; all arguments total/effect-free; no reordering of logging/failing argument expressions |
| Builtin-state sharing | Closed expressions; valid force/value protocol; still unsaturated; fresh binding identities; explicit profitability choice |
| Constant pooling | Literal type participates in equality; actual encoded-size threshold; fresh bindings; no subsequent pass that reinlines the constants |

Supported semantics are those of the pinned repository evaluator and UPLC 1.1.0
path, including its constant-case behavior. This is not a claim of compatibility
with every ledger era or independently fetched current network cost parameters.

## Additional correctness repairs found during integration

### Data projection model

`UnConstrData` incorrectly returned `PairData (Data.I tag, Data.List fields)`.
It now returns a pair containing an actual Integer and Data list. FstPair and
SndPair therefore expose the correct runtime shapes. Native/model projection
agreement is now an assertion, not the previous diagnostic warning.

The CEK also accepts the generic Data-element list representation used by the
decoder for `ConstrData` and `ListData`. `constType` now derives generic pair
component types and correctly describes ConstPairDataList as a list of pairs.

This is not a complete redesign of typed CEK constants: VCon still does not
retain every literal type annotation, particularly for arbitrary empty generic
lists. Native conformance checks therefore remain essential, and general
polymorphic constant folding remains deliberately excluded.

### Fix parameter shadowing

Raw lowering substituted the recursive name after removing the outer lambda
from `Fix f (Lam x body)`. When x and f were the same variable, it substituted
references actually bound by the lambda parameter. Applying the supposed
identity returned a recursive closure instead of its argument.

Lowering now skips that substitution when the parameter shadows the recursive
binder. Tests check the raw unoptimized result, every compilation profile, and
ordinary recursive countdown behavior. This was a real lowering bug exposed by
the nonrecursive-Fix pass, not a reason to weaken the new test.

### Composite literal types in CaseMerge

Known-constructor specialization reconstructed list/pair fields using
`constType`, which cannot recover an empty generic list's element type. A tail
of list Integer could therefore become a list Data literal during optimization.

The pass now projects field type witnesses from the original literal annotation:
list element/original list type, or the pair's declared component types. Tests
cover nonempty and empty integer tails, nested empty lists, and pair fields.

## Verification evidence

Commands run:

```sh
lake build Moist
lake build tests mir_audit mir_opportunity_bench ptah_test \
  Moist.Verified.VerifiedOptimize Test.MIR.Opt.AdvancedAxioms
.lake/build/bin/tests
.lake/build/bin/mir_audit
.lake/build/bin/ptah_test
.lake/build/bin/mir_opportunity_bench
git diff --check
```

- **424 passed, 0 failed** in the complete MIR suite.
- **42 passed, 0 failed** in the focused audit/production suite.
- All nine Ptah runtime smoke checks pass, including recursive list summation.
- **129,024** generated result/error/trace comparisons: 1,024 deterministic
  programs, six observing contexts, 21 individual/composed configurations.
- The existing **18,432** comparisons remain enabled separately.
- **144** targeted argument-order, scope, eager-effect, and delayed-value checks.
- **490** integer, **120** byte/string, **96** Data-guard, and **624** malformed
  policy-shape native comparisons.
- Every combination of packing, builtin sharing, and constant pooling is tested
  on checked Data consumers, invalid inputs, recursive/shadowed functions, typed
  composites, and Trace-bearing programs.
- Frontend tests prove option forwarding reaches final lowering: enabling
  pooling actually reduces serialized bytes through both `compile!` and Ptah,
  while results remain equal.
- Unbound variables remain compilation errors. Genuine recursive divergence
  remains budget exhaustion in bounded native checks, rather than becoming an
  explicit error or a returned value. This bounded check is not a divergence
  theorem.

### Kernel-checked scope

`Moist/Verified/AdvancedRedexes.lean` proves six local CEK state joins for:
force/case/delay, delayed Boolean choice, cons fusion, nil fusion,
three-literal-argument packing, and successful binary-builtin folding.

The environment and continuation stack are arbitrary. Each lemma reaches the
same machine state on both sides, rather than merely checking a sample return
value. The axiom audit reports only `propext` and `Quot.sound`, with no
`budget_exhaustion`, `sorryAx`, or compiler-trust axiom.

These are rewrite-schema lemmas, **not** proofs of the whole MIR traversal,
abstract facts, inliner, lowering composition, trace instrumentation, all
constant typing, or all allocation profiles. The production pipeline remains
outside the certified subset. The legacy false axiom in verified inlining is
still explicitly unresolved; compiling that older theorem is not evidence
discharging it. The new proofs do not depend on it.

## Measured integration results

`docs/benchmarks/mir-production-golden-costs.csv` records the 32 changed native
evaluation fixtures relative to the corrected pre-integration compiler. Every
returned result/error section is unchanged. Only CPU/memory sections change.
One structural lowering snapshot and two structural unit expectations were
updated for the newly simplified representation; existing tests were retained.

| Fixture | CPU before → after | Memory before → after |
| --- | --- | --- |
| factorial(10) | 8,501,912 → 6,433,373 | 32,462 → 24,751 |
| NFT success | 2,929,814 → 2,343,773 | 10,584 → 8,251 |
| NFT spending rejection | 1,786,297 → 1,271,972 | 6,358 → 4,325 |
| redeemer success | 1,874,191 → 1,476,199 | 6,322 → 4,690 |
| SOP access fixture | 4,588,702 → 2,547,112 | 16,594 → 7,918 |
| constant payment | 549,573 → 16,100 | 2,460 → 200 |

These integration fixtures compile their argument-producing source definitions
too; improvements such as SOP access include cheaper argument construction.
Do not interpret those numbers as isolated receiver-only optimization savings.

`docs/benchmarks/mir-production-native.csv` contains the current benchmark run:
18 scripts, 36 input cases, baseline plus 21 variants, **792 rows**. Production
profile rows call the real `compileOptimized` backend, including post-Fix
lowering. Optimization receives the script without the runtime arguments.
Its baseline is the now-integrated compiler's output, not the older compiler;
retain the historical opportunity CSVs separately rather than comparing unlike
baselines silently. CPU/memory are pinned evaluator budget units; bytes are Flat
script bytes, excluding runtime inputs and transaction envelopes.

## Integration groups

The changes separate into model/literal/lowering correctness repairs;
production pass modules and shared compiler; frontend controls; standalone
redex proofs; regression suites and fixture updates; benchmark/documentation
artifacts. Commit signing was previously canceled and has not been bypassed.
