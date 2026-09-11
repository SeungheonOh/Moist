# Real validator comparison

This report records the initial porting baseline. Subsequent general compiler
improvements and same-evaluator execution-budget comparisons are documented in
`MIR-General-Recursion-Optimization.md`; the original artifacts remain frozen.

## Scope and provenance

Three complete validator ports from
[plinth-plutarch-comparison](https://github.com/SeungheonOh/plinth-plutarch-comparison/tree/e21532661107f5d4feb380f9b1dcdf3ddb3b023f)
are implemented in `Test/Comparison/Validators.lean`, not arithmetic stand-ins:

- **Voting:** voting-purpose restriction; input traversal; nested currency/token
  map search; first matching entry must have quantity exactly one.
- **Certifying:** certifying-purpose restriction; registration; deregistration
  strictly after expiration with inclusive/exclusive and infinity handling;
  delegation and registration/delegation only to `DelegVote DRepAlwaysAbstain`;
  rejection of all other certificate kinds. Expiration is decoded eagerly,
  including on registration, following the source's strict entry point.
- **Vesting:** spending purpose and present datum; beneficiary signature; own
  input lookup; linear vesting with integer division; declared release amount;
  beneficiary input/output sums and transaction fee; full withdrawal or exactly
  one continuing output at the same address with matching inline datum.

These use ordinary Lean definitions compiled through the existing onchain
translator and MIR optimizer. Voting and Vesting use builtin Data projections
and recursive list helpers; Certifying uses the typed V3 ledger structures.
All have the source's Data parameter ABI and return builtin Unit, not Boolean.
No optimizer or production-default settings were changed for this experiment.

Pinned reference sources:

- `src/{Voting,Certifying,Vesting}/Contracts/*Plinth.hs`, plus their Plutarch peers.
- `test/{Voting,Certifying,Vesting}/Test/*.hs` and the shared ScriptContext builder.
- `app/BenchScripts.hs` and the README's recorded benchmark tables.
- Plinth/plutus-core **1.65.0.0**, Plutarch **1.12.0**, GHC **9.6.6**;
  Plutarch compatibility fork `011f6e18a2da94920cd009ce1970b43b18b70698`.
- Moist base `cc23952564d9e58b50bfea068d26d84e01597735` plus this audit worktree;
  Lean **4.24.0**, Zig **0.15.2**, Plutuz
  `33b812dbcf88f6851286e54cb93a4a443353f94c`.

## Comparability: important qualification

**Moist numbers are newly measured; Plinth/Plutarch numbers are reported by the
source repository, not rerun here. This is not a same-evaluator league table.**

The upstream fork's `Plutarch.Internal.Evaluate` uses
`defaultCekParametersForTesting`. In the pinned plutus-core release this selects
**variant E**. Moist's FFI selects Plutuz **semantics C and its default costs**.
The upstream C/E JSON models share machine-step costs but differ in
`equalsByteString`, integer division/modulo/quotient/remainder costing. Vesting
uses byte equality and division, so its cross-language CPU comparison is
indicative, not cost-model-normalized. Runtime implementations and their memory
accounting have not been cross-certified either. CPU means budget units, not
wall-clock time; memory means cumulative execution-budget units, not peak RSS.

The model distinction was checked against the pinned
[evaluation defaults](https://github.com/IntersectMBO/plutus/blob/b2db512618df08bd696e8d9c4229effcede01169/plutus-core/plutus-core/src/PlutusCore/Evaluation/Machine/ExBudgetingDefaults.hs),
[C builtin costs](https://github.com/IntersectMBO/plutus/blob/b2db512618df08bd696e8d9c4229effcede01169/plutus-core/cost-model/data/builtinCostModelC.json), and
[E builtin costs](https://github.com/IntersectMBO/plutus/blob/b2db512618df08bd696e8d9c4229effcede01169/plutus-core/cost-model/data/builtinCostModelE.json).
The reference CEK also supports builtin-value casing; that feature is not an
unacknowledged difference from its evaluator. None of these measurements
establish availability or costs under a live ledger's protocol parameters.

The 19 accepting benchmark scenarios mirror all reported scenarios for these
three validators: 4 Voting, 4 Certifying, 11 Vesting. Context construction retains
the V3 field layout, datum/redeemer encodings, source parameter values, outputs,
fees and traversal order. The reference builder reverses its sorted inputs;
the Voting multi-input fixture and Vesting inputs preserve that order.
Explicit BuiltinByteString string literals remain ASCII bytes, not hex-decoded
hashes; overloaded TxId literals are hex-decoded. No reference-program exports
were present in the repository, and the reconstructed contexts were not
byte-for-byte checked against a Haskell export. Exported local inputs make that
follow-up comparison possible without recreating the fixtures.

Scripts are compiled **before** applying parameters or context. No benchmark
input is folded into a validator. Unapplied script sizes exclude all arguments.
Upstream measures CBOR-wrapped Flat; both raw Flat and its single CBOR bytestring
wrapper size are recorded locally. Tables below use the comparable CBOR size.

## Script sizes

| Validator | Moist raw | Moist default | Moist sharing/pooling | Plutarch reported | Plinth reported |
|---|---:|---:|---:|---:|---:|
| Voting | 298 | 239 | 241 | 272 | 244 |
| Certifying | 589 | 350 | 346 | 317 | 381 |
| Vesting | 1,325 | 948 | 929 | 1,219 | 1,184 |

The optional `size-options` profile enables builtin sharing and constant pooling;
it is **not** guaranteed to minimize size or resource use. Voting gets slightly
larger. Certifying registration spends more CPU and memory with those options.
It remains separate from the CPU/memory-oriented production defaults.

## Execution results

Each cell is **CPU / memory**. The qualification about different evaluators and
cost variants applies to every cross-language comparison.

| Scenario | Moist default measured | Plutarch reported | Plinth reported |
|---|---:|---:|---:|
| Voting: NFT in pubkey input | 11,448,192 / 28,587 | 12,244,560 / 30,755 | 11,461,062 / 27,727 |
| Voting: NFT among multiple inputs | 16,260,696 / 42,533 | 17,129,982 / 44,166 | 15,661,615 / 37,374 |
| Certifying: register | 3,361,377 / 11,854 | 3,281,634 / 11,753 | 3,235,577 / 11,084 |
| Certifying: unregister after expiration | 7,491,645 / 23,491 | 7,886,843 / 24,094 | 8,633,363 / 26,629 |
| Certifying: delegate to abstain | 5,390,296 / 18,316 | 5,907,816 / 18,612 | 5,528,026 / 17,948 |
| Certifying: register and delegate | 5,506,629 / 18,717 | 6,386,093 / 19,946 | 5,832,408 / 19,050 |
| Vesting: full withdrawal after vesting | 34,064,775 / 102,737 | 38,909,388 / 112,264 | 35,340,687 / 101,467 |
| Vesting: partial withdrawal midpoint | 47,191,738 / 131,598 | 66,088,455 / 183,674 | 56,291,830 / 157,014 |
| Vesting: multiple beneficiary outputs | 38,875,401 / 118,005 | 43,484,191 / 126,070 | 39,313,502 / 113,109 |

The unoptimized/default comparison **does** use the same evaluator, cost model,
source and inputs. For these representative scenarios:

- Voting multi-input: **16.3% CPU / 27.9% memory reduction**.
- Certifying unregister: **31.5% CPU / 42.3% memory reduction**.
- Vesting midpoint: **25.2% CPU / 36.1% memory reduction**.

The results are mixed against the reported peers: Moist's default is smaller
than both Vesting peers and both Voting peers, but not Plutarch Certifying.
Voting multi-input traversal and Certifying registration remain optimization
targets; Moist does not dominate Plinth on either CPU or memory there. Vesting
full withdrawal also uses more memory than the reported Plinth result. The
optional sharing/pooling profile improves Vesting further but is not a universal
replacement for defaults. These are workload measurements, not an optimality
claim or a reason to specialize the compiler to these fixtures.

## Verification and semantic boundaries

`Test/Comparison/Tests.lean` is registered in the normal test suite:

**Final validation: 447 tests passed, zero failed**, including all six new
comparison groups (7,814 native evaluations). The benchmark executable completed
all 63 scenarios across three profiles. All 38 reported CPU/memory pairs were
also checked against the pinned README; the artifact integrity manifest passes.

- 309 explicit/generated cases across raw, default and sharing/pooling profiles.
  This includes 180 input-search cases and 54 vesting state/rounding cases.
- 2,280 malformed-context differential cases across the same three profiles,
  replacing whole contexts, context fields and transaction-info fields.
- Invalid expiration parameters must fail even for registration.
- Every success must return builtin Unit. Resource exhaustion, serialization
  failures and unbound variables invalidate a measurement, rather than counting
  as expected validator rejection.
- All 19 accepting reference scenarios assert default CPU and memory do not
  exceed the corresponding unoptimized Moist script.

These are native regression tests, not a whole-pipeline formal proof and not
cross-language differential execution. Malformed-data tests establish parity
between the Moist profiles, not identical failure order with both Haskell
implementations. Generated off-ledger states deliberately include negative or
zero amounts; they test contract arithmetic, not transaction phase-one validity.

Ports intentionally retain the upstream Vesting rules: ADA is read from the
first nested value-map entry; infinite lower bounds map to time zero; closure
is ignored for vesting; a zero claim before the start can pass; a partial
continuation's value is not checked by this validator. Tests lock in these
behaviors instead of silently strengthening the source contract. These examples
are comparison fixtures, **not audited production deployment recommendations**.

## Reproduction and artifacts

From the Moist audit worktree:

```sh
lake build validator_comparison tests
.lake/build/bin/tests mir/eval/comparison
.lake/build/bin/validator_comparison /tmp/real-validator-exports > /tmp/real-validator-comparison.csv
.lake/build/bin/tests
```

- `docs/benchmarks/real-validator-comparison.csv`: 227 measurement/reference rows;
  rejecting costs are retained only for local debugging, not peer rankings.
- `docs/benchmarks/real-validators/`: nine unapplied scripts as Flat hex and all
  309 explicit/generated argument sets, with expected acceptance.
- `real-validators/inputs.csv` arguments are semicolon-separated Flat programs,
  each containing one Data constant. Apply them in order to the named script.
- `real-validators.sha256`: integrity manifest of these reproducible artifacts.

The runner requires no Haskell toolchain or network access. The independently
cloned reference repository is unmodified. Prior optimization benchmark snapshots
are unchanged.
