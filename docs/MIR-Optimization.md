# Maintaining MIR optimization

## Entry points and scheduling

Use `Moist.MIR.compileOptimized` for production compilation. It validates
lexical scope and the required `Fix` lambda before optimization, then lowers
to UPLC. Onchain and Ptah compilation both call this entry point.
`optimizeExpr` is only the core MIR optimizer, not the complete compiler.

The schedule is defined in `Moist/MIR/Compile.lean`,
`Moist/MIR/Optimize.lean`, and `Moist/MIR/Optimize/Advanced.lean`:

1. Move invariant arguments outside recursive workers before ANF.
2. Prepare delayed values/nonrecursive functions, float out, beta-reduce,
   normalize to ANF, and float out again.
3. Iterate checked simplification, CSE, DCE, inlining, beta, eta, and
   force/delay cleanup, with preparation and ANF at each iteration.
4. Perform pre-lowering cleanup and structural list/product rewrites.
5. Lower recursive functions, then perform final application packing and
   optional sharing on the lifted UPLC. Do not run inverse case/inlining
   transformations after final allocation.

Defaults enable application packing at three arguments. Builtin-state sharing
and constant pooling are opt-in through `Advanced.Options` or the
`moist.optimize.shareBuiltinStates` and `moist.optimize.poolConstants` Lean
options. CPU, memory, and encoded size must be measured independently;
neither the defaults nor the iteration bound imply global optimality.

## Analysis boundaries

- `Optimize/Safety.lean` owns binder hygiene, fresh-name reservation,
  repeatability, callable-value checks, and the evaluation-frontier guard.
- `Advanced/Traversal.lean` owns immediate-child traversal, application-spine
  extraction, nested-let flattening, and fuel-bounded bottom-up rewriting.
- `Advanced/Facts.lean` owns shared head-alias resolution, Boolean builtin
  classification, and the builtin protocol after successful evaluation.
  Resolution follows aliases in the supplied dominating environment and only
  descends through function heads and forces; it does not rewrite arguments.
- **Post-success facts are not totality proofs.**
  `builtinProtocolAfterSuccess` does not check argument effects;
  `builtinRemainder` does. Keep these analyses separate. Likewise, facts from
  a producer or selected branch must not justify discarding its validation.
- Public scope-moving passes establish unique binders. Internal workers may
  rely on that invariant; do not expose them as arbitrary-input entry points.

Scalar folding, Data folding, and dead-Fix elimination use the common total
bottom-up traversal. Application packing retains its spine-specific traversal
because packing individual application nodes would change the transformation.
The production fuel bounds are covered by completeness/irrelevance proofs;
do not replace them with arbitrary recursion limits.

## Verification

The [whole-pass coverage table](MIR-Remaining-Pass-Proofs.md#current-whole-pass-coverage)
is the proof inventory. The contract is contextual halting/error refinement
through `lowerTotalExpr`. It does not certify native CEK correspondence,
trace equivalence, resource-cap preservation, or the entire production pipeline.
Local rewrite lemmas and differential tests are not whole-pass certificates.

The ordinary test build imports `Test.MIR.Opt.FormalAxioms`. Its allowlist
rejects dependencies outside `propext`, `Classical.choice`, and `Quot.sound`
for the listed certificates. The false legacy `budget_exhaustion` axiom still
exists for older proof APIs; the checked certificates must not depend on it.

With the repository's Lean toolchain and Zig 0.15.2 available:

```sh
lake build tests mir_audit mir_opportunity_bench checked_branch_bench ptah_test
lake test
.lake/build/bin/ptah_test
.lake/build/bin/mir_opportunity_bench --validate-only
.lake/build/bin/checked_branch_bench
.lake/build/bin/checked_branch_bench --scaling
```

Benchmark candidates carry an explicit MIR-to-UPLC compilation function;
their display names do not select behavior. Production profiles call the
real compiler for both measurement and semantic validation. Structural
ablation profiles deliberately omit stages and are not production defaults.

## Historical evidence

The other `MIR-*` audit reports and files under `docs/audits/` and
`docs/benchmarks/` record dated checkpoints. Their counts, source line numbers,
and intermediate proof gaps are historical, not a current API specification.
Keep frozen benchmark inputs and earlier measurements intact when comparing
changes. The [packing and hygiene report](MIR-Packing-Hygiene-Proofs.md)
describes the most recent proof additions before the maintenance cleanup.
