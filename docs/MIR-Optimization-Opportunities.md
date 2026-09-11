# MIR optimization opportunities: additional timed investigation

**Historical experiment:** these prototypes have since been promoted to
production. See `docs/MIR-Optimization-Implementation.md:1` for current defaults,
verification, additional correctness repairs, and remaining proof limitations.
The measurements and prototype-status descriptions below record the earlier run.

## Scope and conclusion

This extends the correctness audit with a 30-minute investigation started at
2026-09-08 00:26:26 UTC. The checkout remains the isolated audit worktree based
on `cc23952564d9e58b50bfea068d26d84e01597735`; the earlier repairs and original
working checkout are preserved.

**There are substantial remaining optimizations.** Ten experimental pass
families and sixteen individual/composed configurations are implemented in
`Test/MIR/Opt/Opportunities.lean`. They are deliberately not connected to the
production compiler. `Test/MIR/OpportunityBench.lean` measures and checks them.

The strongest immediate candidates are checked-value shape propagation,
Boolean case lowering, bounded typed constant construction, and destructor
fusion. Allocation sharing and final application packing also help, but their
profitability depends on the script and execution path.

“Maximally optimal” needs an objective: CPU, execution memory, serialized size,
and compilation time are different quantities. Keep a Pareto frontier rather
than silently choosing one. A pass can preserve values and traces while making
a low-budget execution fail. Arbitrary recursive MIR does not admit a general
algorithm guaranteeing the globally cheapest equivalent program; the practical
target is the best certified candidate within an explicit rewrite family,
target semantics, and cost objective.

## Measured results

Native fixture measurements use the corrected compiler's already-generated
UPLC, lifted back into MIR. Transformations receive the script **without its
runtime arguments**. Inputs are applied only after optimization and lowering.
Consequently, the factorial and validator improvements are not obtained by
constant-folding the benchmark inputs.

Synthetic fixtures directly exercise individual MIR patterns. The payment and
nested-construction fixtures are genuinely closed constant-producing programs;
their large percentage savings must not be extrapolated to arbitrary validators.

CPU/memory are the pinned Plutuz FFI's execution-budget units, not wall-clock
time or host RAM. Plutuz is pinned at
`33b812dbcf88f6851286e54cb93a4a443353f94c`. Scripts are serialized as Flat UPLC
1.1.0. These are not measurements against independently fetched current ledger
cost parameters. Size excludes runtime arguments, CBOR-envelope overhead, and
transaction overhead.

The harness explicitly supplies the repository's declared CPU and memory
limits separately; it does not rely on evalTerm's shared default argument,
which otherwise supplies the CPU limit as the memory limit too.

| Fixture / candidate | CPU before → after | Memory before → after | Flat bytes before → after |
| --- | --- | --- | --- |
| factorial(10), Boolean case | 8,501,912 → 6,433,373 (-24.33%) | 32,462 → 24,751 | 39 → 35 |
| redeemer policy, shape cleanup | 1,874,191 → 1,476,199 (-21.24%) | 6,322 → 4,690 | 81 → 42 |
| NFT success, shape cleanup | 2,929,814 → 2,343,773 (-20.00%) | 10,584 → 8,251 | 111 → 68 |
| constant payment, typed Data folding + cleanup | 549,573 → 16,100 (-97.07%) | 2,460 → 200 | 29 → 21 |
| constant nested value, typed Data folding + cleanup | 1,203,408 → 356,764 (-70.35%) | 5,052 → 1,696 | 51 → 37 |
| synthetic list head/tail fusion | 558,846 → 266,033 (-52.40%) | 2,496 → 1,632 | 23 → 17 |
| synthetic unused recursive binder | 325,308 → 229,308 (-29.51%) | 1,502 → 902 | 15 → 10 |
| synthetic shared delayed closure | 389,308 → 325,308 (-16.44%) | 1,902 → 1,502 | 19 → 17 |

The complete native/synthetic table is
`docs/benchmarks/mir-opportunity-native.csv`: 18 scripts, 36 input cases,
baseline plus 16 candidates, 612 rows. Twelve scripts have a candidate that
strictly improves at least one metric without worsening CPU, memory, or bytes
on **any of their tested inputs**. This includes seven of the twelve existing
compiler/validator scripts. It is empirical dominance, not a universal bound.

Negative results are equally important:

- Unconditional repeated-builtin hoisting makes SOP access worse:
  4,588,702 → 4,604,702 CPU; 61 → 66 bytes.
- On NFT's spending rejection path, the initial `combined` configuration costs
  1,882,297 CPU versus baseline 1,786,297. Shape cleanup instead costs 1,271,972.
  Concatenating individually plausible passes is not an optimization strategy.
- Pooling a duplicated 128-character string reduces 275 → 147 bytes but raises
  CPU 212,433 → 260,433 and memory 1,101 → 1,401. In this particular fixture,
  identical-branch simplification is an even better size-oriented candidate;
  pooling is not the best implementation of that example.
- Six rounds of shape/Data cleanup do not improve the native suite beyond one
  round. More iteration is not evidence of greater optimality.
- No measured improvement was found for SOP access, lovelace/time extraction,
  action matching, or the always policy in this candidate set.

Policy fixtures include success, rejection, malformed redeemers, and malformed
context shapes. Their minimal TxInfo is unused by these policies; this is not
a comprehensive benchmark of ledger-context processing.

### External cross-check

`docs/benchmarks/mir-opportunity-external.csv` records six completed auction
fixtures from the existing local `llvm-uplc/benchmarks` corpus: **four unique
Flat files**, because two filenames duplicate earlier files byte-for-byte.
The SHA-256 manifest is `docs/benchmarks/mir-opportunity-external.sha256`.
This is a narrow cross-check, not six independent validator designs or a full
corpus survey. Incomplete fixtures from the time-bounded batch are excluded.

This batch used the fifteen-candidate configuration before list fusion was
added: 96 rows including baselines. It evaluates the supplied programs as-is,
without additional runtime inputs, against their lifted/re-lowered UPLC 1.1.0
baseline. These are not improvements over Moist-generated scripts, nor a
measurement of the original Flat file's bytes. The batch's default memory
allowance was generous; all recorded executions nevertheless consumed less
than the subsequently explicit repository memory limit.

For `auction_1-1.flat`, the initial combined candidate changes CPU
185,243,960 → 157,931,764, memory 831,092 → 662,288, and bytes 3,834 → 3,222.
Application packing alone changes CPU 185,243,960 → 183,419,960 but increases
bytes 3,834 → 3,846. Builtin sharing is profitable here despite regressing
some native fixtures. Thus neither “always hoist” nor “never hoist” is adequate.

For `auction_1-2.flat`, delayed-value sharing alone changes CPU
628,192,291 → 609,760,291, memory 3,455,036 → 3,339,836, and bytes 9,015 → 8,867.
This supplies an existing-program example beyond the synthetic delay fixture.

## Implemented experimental pass families

### 1. Boolean-result specialization and force/case/delay cancellation

Recognize successful Boolean-producing builtin applications, including their
dominating aliases. Replace strictly evaluated `ifThenElse` alternatives with
native Boolean Case only when both alternatives are safe values. Cancel Force
over Case-of-Delay only when the scrutinee is positively known to be Boolean,
which guarantees zero supplied fields and the same two alternatives.

An unknown source argument annotated Bool is not evidence: malformed UPLC can
pass a constructor instead. Eager alternative errors/logs must remain eager.
Upstream has a corresponding ForceCaseDelay transformation, but its stated
well-formed-program assumptions cannot simply be imported into arbitrary MIR.
[Upstream ForceCaseDelay](https://raw.githubusercontent.com/IntersectMBO/plutus/master/plutus-core/untyped-plutus-core/src/UntypedPlutusCore/Transform/ForceCaseDelay.hs)

### 2. Dominating shape facts, totality, and redundant-check removal

After successful `UnConstrData`, its pair has an Integer first field and a list
second field. Use facts from already evaluated bindings to prove later integer
comparisons and projections total. Remove unused total bindings and collapse
equal Boolean branches. If the Boolean computation may still fail or log,
retain its strict evaluation in a Let.

Totality is stamped while visiting each binding using only its prefix
environment. Using the final environment could circularly justify removing the
very validation that establishes a fact. Binder hygiene is mandatory. Division
is not classified as total merely because its arguments are integers.

### 3. Bounded scalar folding

Fold correctly forced/saturated scalar arithmetic, comparisons, byte/string
operations, and UTF-8 conversion using the existing evaluator. Require matching
literal type annotations. Leave failed evaluations unchanged. Cap scalar inputs
and intermediate/output values: integers below 256 bits in magnitude and
strings/bytes at 1,024 bytes. Exclude Trace, cryptography, and unsupported
constant representations.

### 4. Typed Data-constructor folding

Directly fold `IData`, `BData`, `MkNilData`, Data-list `MkCons`, `ListData`, and
bounded valid-tag `ConstrData`. Preserve the actual list element type and only
reify bounded encoded results. This is separate from blindly evaluating every
builtin through the Lean CEK; the model discrepancy below makes that unsafe.

Generic empty lists, arrays, pairs, and maps need explicit type witnesses.
`constType` cannot reconstruct all of them correctly. Extending this pass must
not erase the element type of an empty list or serialize a list of pairs as a
single pair.

### 5. Checked list-destructor fusion

Fuse adjacent `headList xs` and `tailList xs` bindings into one native list Case,
with two binders for the cons branch and Error for the nil branch. Require a
positively known list from a literal or successful checked producer; merely
being a source list variable is insufficient. Preserve the original validating
producer and use the already evaluated list variable.

The prototype deliberately does not commute unrelated operations. Extensions
worth implementing are pair projection fusion, longer list-unpacking chains,
and fusion through dominated aliases where intervening work is proven total.

### 6. Safe final application packing

Encode application spines of at least three arguments as
`Case (Constr 0 [arguments]) [function]`, only when every argument is total and
effect-free. This reduces application-machine overhead on eligible programs.
Leave it until after case simplification, which otherwise immediately reverses
the encoding. Upstream likewise places application packing last.
[Upstream ApplyToCase](https://raw.githubusercontent.com/IntersectMBO/plutus/master/plutus-core/untyped-plutus-core/src/UntypedPlutusCore/Transform/ApplyToCase.hs)

The argument guard is essential: ordinary CBV may execute a function body
between successive arguments. Blind packing evaluates all arguments first and
can reverse Trace messages. The guard suite includes an actual counterexample
whose traces change from `call, argument` to `argument, call` without the guard.

### 7. Share delayed values without copying their bodies

For a delay binding used only through Force, bind its body instead when that
body is total and effect-free, replacing Force uses with the new value. This
avoids repeated force/closure work without duplicating the delayed body. Retain
the original binding when it escapes as a delay or contains logging/failure.
This should run before a copying force-delay pass destroys the opportunity.

### 8. Eliminate nonrecursive Fix

Replace `Fix f (Lam x body)` by the lambda if f is not free in it. This avoids
lowering an unnecessary Z-combinator allocation and self-application. Respect
lexical shadowing and retain genuine recursion. This is a pre-lowering MIR
opportunity; lifting already lowered UPLC cannot recover the original Fix node.

### 9. Profitability-aware builtin-state sharing

Recognize closed, correctly forced and unsaturated builtin states. Compare
hoisting repeated states versus all states. Repeated states often benefit loops
but static occurrence count alone does not predict dynamic profitability.

The present production inliner considers every literal/builtin atom size one
and inlines sufficiently small pure values regardless of repeated use. That
can undo sharing. Introduce an explicit preserve-sharing decision or perform
profitability extraction late, rather than changing semantic purity to force a
particular cost result. Upstream separates polymorphic-builtin hoisting from
its ordinary simplification loop.
[Upstream PolyBuiltin](https://raw.githubusercontent.com/IntersectMBO/plutus/master/plutus-core/untyped-plutus-core/src/UntypedPlutusCore/Transform/PolyBuiltin.hs)

### 10. Serialized-size-aware constant pooling

Pool sufficiently large repeated literals using actual Flat size, not AST node
count. Include literal type in equality, and use fresh binders. Extra binding
and lookup costs mean this belongs to a size objective or a Pareto portfolio,
not unconditional CPU optimization. Plinth explicitly exposes growth limits and
constant-inlining choices rather than treating these as one universal setting.
[Plinth compiler options](https://plutus.cardano.intersectmbo.org/docs/delve-deeper/plinth-compiler-options)

## A newly confirmed prerequisite: evaluator agreement

For the same lowered expression:

```text
fstPair (unConstrData (Data.Constr 0 []))
Lean CEK:   (con data (I 0))
Native FFI: (con integer 0)
```

`Moist/CEK/Builtins.lean:480` constructs a PairData whose components are Data.I
and Data.List. FstPair then returns Data instead of Integer. The actual runtime
uses an Integer/list pair. The benchmark reproduces and reports the discrepancy.
The same representation path affects SndPair. Separately,
`Moist/Plutus/Term.lean:297` maps ConstPairDataList to a pair type instead of a
list-of-pairs type; generic ConstList defaults to list Data regardless of its
actual element type.

Do not generalize CEK-based folding, or claim target-level certification of
shape rewrites, until the model, constant typing/readback, and native semantics
agree. The Data-constructor prototype avoids those incorrect projection/type
paths; native tests check its real serialized results. This finding is recorded,
not silently repaired as a broad evaluator/proof API change during the timed
optimization experiment. The earlier false `budget_exhaustion` axiom also
remains unresolved; successful Lean builds do not make it sound.

## Integration order and further work

1. Align builtin semantics, constant type witnesses, and the proof model with
   the selected ledger version. Keep scalar/data/trace/native conformance tests.
2. Add an explicit analysis domain: known shape, totality, possible logging,
   builtin protocol state, and dynamic allocation multiplicity.
3. Run semantic simplification: checked shape propagation, constant folding,
   branch cleanup, destructor fusion, nonrecursive Fix removal, and delay sharing.
4. Perform cost-aware sharing/inlining extraction. Keep the baseline and
   nondominated alternatives, accounting for de Bruijn index widths and actual
   serialized constants. Do not infer worst-case bounds from a few sample inputs.
5. Lower Fix, perform final UPLC packing, and avoid a subsequent inverse
   case-reduction pass. Validate against the target evaluator and cost model.

Further concrete opportunities beyond the prototypes:

- **Pair/list destructuring and demand analysis:** combine checked projections;
  avoid constructing/reading fields the continuation never consumes.
- **Integer identities with runtime shape evidence:** `x + 0`, `x * 1`, and
  repeated comparisons become safe only after preserving their type checks and
  strict operand evaluations. Arbitrary untyped algebra is unsound.
- **Dense tag dispatch:** replace long integer-comparison chains with native
  integer Case only after proving range bounds or retaining the original
  out-of-range/negative fallback. Source constructor counts alone are unsafe.
- **Case-of-case and branch-local CSE:** share identical continuations without
  speculating eager constructor fields or duplicating costly alternatives.
  [Upstream CaseOfCase](https://raw.githubusercontent.com/IntersectMBO/plutus/master/plutus-core/untyped-plutus-core/src/UntypedPlutusCore/Transform/CaseOfCase.hs)
- **Loop invariants and invariant-argument specialization:** hoist safe partial
  builtin applications and specialize recursive workers; cap cloned code and
  measure the Z-combinator/self-application costs after lowering.
- **Equality saturation in pure, typed regions:** retain equivalent candidates
  until extraction instead of committing prematurely to one rewrite order.
  The extracted optimum is relative to the represented equivalences and cost
  function, not all possible programs. Binder-aware and sharing-aware extraction
  are required. [egg background](https://egraphs-good.github.io/egg/egg/tutorials/_01_background/index.html)
- **Compiler scalability:** incremental liveness, indexed alpha-aware CSE,
  cached shape facts, and elimination of ANF/inlining oscillation. These reduce
  compilation work but do not themselves guarantee a cheaper output script.

## Reproduction and validation

```sh
lake build tests mir_audit mir_opportunity_bench Moist.Verified.VerifiedOptimize
.lake/build/bin/tests
.lake/build/bin/mir_audit
.lake/build/bin/mir_opportunity_bench > native.csv
.lake/build/bin/mir_opportunity_bench --validate-only
.lake/build/bin/mir_opportunity_bench --external /path/to/flat/corpus 3 > external.csv
```

Current validation:

- Existing complete suite: **411 passed, 0 failed**.
- Focused correctness audit: **29 passed, 0 failed**, including the original
  18,432 differential comparisons and the independent false-axiom counterexample.
- Experimental configurations: **98,304 result/error/trace comparisons** from
  1,024 deterministic generated programs, six observing contexts, 16 candidates.
- **144 adversarial comparisons**, including eager errors/logs, malformed
  Boolean cases, shadowing, failed validation, delay escape, and packing order.
- **490 integer**, **120 byte/string**, **96 Data-guard**, and **624 malformed
  policy-shape** comparisons against the native FFI.
- **576 transformed fixture/input comparisons** against native baselines, with
  separate CPU/memory/size measurements. Out-of-budget and encoding failures
  abort rather than being treated as successful equivalence checks.

All 612 native table rows were reproduced after explicitly supplying separate
CPU/memory limits, with identical results and CPU/memory/byte measurements.

This is bounded testing, not exhaustive equivalence proof. Generated terms do
not cover arbitrary recursive programs, all builtins, or all literal types.
Native checks compare successful returned values and failure status; they do
not equate error diagnostics or independently record Trace. Trace order is
checked by the separate Lean step instrumentation, whose Data limitations are
explicitly described above. Compile milliseconds include transformation,
lowering, and script-size encoding, but exclude input evaluation.

No production pass is enabled by this research, no remote push occurs, and the
previously canceled commit-signing decision is not bypassed.
