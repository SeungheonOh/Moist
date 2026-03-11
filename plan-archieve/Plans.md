# Moist Expansion Plan

## Reference Snapshots

### Plutarch (`plutarch-plutus/`)
- `Plutarch/Internal/Term.hs` implements the hoisted DAG-based term representation, compilation, hoisting, tracing config, and script emission used across the DSL.
- `Plutarch/Internal/PlutusType.hs`, `Internal/PLam.hs`, `Internal/TryFrom.hs`, and friends provide the typed eDSL layer (`Term s a`, `(:-->)`, `plam`, pattern matching, and coercions) that power the user-facing combinators surfaced through `Plutarch/Prelude.hs`.
- Modules under `Plutarch/Builtin/`, `Plutarch/List.hs`, `Plutarch/Maybe.hs`, `Plutarch/DataRepr`, etc., supply batteries-included encoders/decoders, list/maybe/pair abstractions, numerical classes, Scott encodings, and extensive `IsData`/`PlutusType` deriving support.
- `Plutarch/Script.hs`, `Plutarch/Internal/Evaluate.hs`, and `plutarch-testlib/` show how compiled terms are evaluated, benchmarked, and golden-tested against UPLC, while `plutarch-ledger-api/` brings ledger-specific types and helpers.
- Tooling files (`plutarch.cabal`, `cabal.project`, documentation in `plutarch-docs/`, etc.) wire everything into cabal/nix workflows and provide guides for contributors.

### Moist (`Moist/`)
- `Moist/Plutus/Term.lean`, `Encode.lean`, and `Decode.lean` define the Plutus Core AST, bit-level encoding/decoding (flat + CBOR), and list of builtins, giving us spec-level serialization coverage but no executable DSL.
- `Moist/Plutus/BitBuffer.lean` and `CBOR.lean` provide reusable utilities for bit/byte manipulation and CBOR emission.
- `Moist/Plutus/Moist.lean` sketches the beginnings of a typed term DSL (`PTerm`, `PlutusType`, experimental `plam` elaborator), yet lacks concrete type instances, builtin plumbing, or compilation to scripts.
- `Main.lean` and `Moist/Basic.lean` are placeholders; there is no CLI, no regression suite (`Moist/Plutus/Test.lean` is empty), and no linkage to the LaTeX spec beyond shared data types.

The plan below lists the milestones required to grow Moist from today’s serialization prototype into a feature-complete Plutarch alternative.

## Milestones

### 1. Solidify the Core Term & Encoding Layer
- **Audit + extend AST**: ensure `Moist/Plutus/Term.lean` covers every constructor Plutarch touches (e.g., placeholders, hoisted references, annotations) and document invariants next to the inductive definitions.
- **Complete CBOR/data round-trips**: finish unimplemented decoders (e.g., `decodeData` in `Decode.lean`) and add proofs/tests that `encode_program` ∘ `decodeProgramFromHexString` is identity on golden scripts from `plutarch-testlib`.
- **BitBuffer reliability**: add QuickCheck-style property tests (Lean `example`s under `Moist/Plutus/Test.lean`) for padding, chunking, zig-zag, etc., mirroring Plutarch’s `Internal.Evaluate`.
- **Deliverables**: spec-aligned encode/decode with tests, documentation in `spec/` referencing the Lean implementations.

### 2. Define the Lean `Term` DSL Abstractions
- **Type-indexed term kernel**: redesign `PTerm`/`PlutusType` in `Moist/Plutus/Moist.lean` to mirror `Plutarch.Internal.Term`’s `Term s a` / `(:-->)` separation, including delayed terms, hoisted wrappers, and coercions (`punsafeCoerce`, `phoistAcyclic` equivalents).
- **Lean elaborator support**: finish the `plam` macro so it produces nested lambdas with type inference + `PTerm` checking, and add `#`, `#$`, `papp`, `plet`, etc., following the ergonomics in `Plutarch/Internal/PLam.hs`.
- **Executable compilation**: expose `(PTerm α).compile : Option Term.Program` plus script serialisation (`BitBuffer.toHexString`) via `lake exe moist`, matching the flow in `Plutarch.Script`.
- **Deliverables**: enriched `Moist.Plutus.Moist` + CLI demos that build simple validators end-to-end.

### 3. Implement Builtin Types & Prelude Modules
- **Builtin surface area**: port the functionality of `Plutarch/Builtin` modules (Bool, Integer, ByteString, Data, Unit, String, Array, Opaque) into Lean namespaces under `Moist/Plutus/Builtin/…`, each providing constructors, eliminators, and helper combinators.
- **Boolean + control**: implement `pif`, `pand`, `por`, `ptrace` wrappers, ensuring they emit builtin calls defined in `Term.Builtin`.
- **ByteString/Data helpers**: mirror encoding helpers (slice, cons, map data) and ensure they typecheck with the Lean DSL.
- **Deliverables**: a `Moist.Plutus.Prelude` module analogous to `Plutarch/Prelude.hs`, re-exporting the core combinators for users.

### 4. Data Representation, Deriving, and Typeclass Machinery
- **`PlutusType` derivation**: port concepts from `Plutarch/Internal/PlutusType.hs` and `Plutarch/DataRepr` to Lean—i.e., support Scott-encoded sums/products, `PInner`, and automatic instance generation for custom validators.
- **`IsData` / lifting**: implement Lean analogues of `Plutarch.Internal.IsData`, `Internal.Lift`, `Internal.TryFrom` so users can convert between on-chain `Data` and Lean-level types safely.
- **Generic deriving helpers**: design Lean macros/tactics that auto-derive `PlutusType`/`IsData` for records (cf. `DerivePlutusType`), integrating with `spec/` proofs where possible.
- **Deliverables**: tutorials + tests showing round-tripping custom data types through `Data`, plus docs referencing `Moist/Plutus/Lemma.lean` results.

### 5. Collections, Numeric Hierarchy, and Utility Combinators
- **List/maybe/pair ops**: reimplement `Plutarch/List.hs`, `Maybe.hs`, `Pair.hs` features (map, fold, zipWith, `pmaybe`, etc.) as Lean functions over `PTerm`, ensuring termination proofs where necessary.
- **Numeric classes**: add Lean typeclasses mirroring `Plutarch/Internal/Numeric.hs` (additive/multiplicative groups, `pquot`, `pmod`, `pnatural`) to enable arithmetic-rich scripts.
- **Term-level monads/continuations**: provide `TermCont`/`tcont` infrastructure (from `Plutarch/TermCont.hs`) for CPS-style validators, plus error/tracing combinators.
- **Deliverables**: a comprehensive prelude test suite comparing semantics with Plutarch via shared golden outputs.

### 6. Optimisation, Hoisting, and Evaluation Pipeline
- **Hoisting DAG**: implement hoisting caches/`HoistedTerm` equivalents so repeated subterms only compile once, with Lean theorems ensuring no dangling references.
- **Optimisers**: port `optimizeTerm`, constant-folding, and dead-code elimination strategies from `Plutarch/Internal/Term.hs`, exposing toggles similar to `Config`/`InternalConfig`.
- **Evaluation backends**: wrap the Haskell Plutus evaluator (or Lean bindings) to allow `lake exe moist --eval script.json`, replicating `Plutarch.Internal.Evaluate`.
- **Deliverables**: benchmarking harness comparing Moist output vs Plutarch for representative validators.

### 7. Ledger API Integration and Higher-Level Packages
- **Ledger types**: translate the modules in `plutarch-ledger-api/` (TxInfo, Value, Credentials, MintingPolicy) into Lean structures + DSL helpers, keeping CBOR/Data compatibility proofs in `spec/`.
- **Orphanage/testlib parity**: add Lean analogues of `plutarch-orphanage` (extra instances) and `plutarch-testlib` (golden tests, property suites) to exercise ledger scripts end-to-end.
- **CLIs & artifacts**: extend `Main.lean` so `lake exe moist` can (1) display validator hex, (2) pretty-print decompiled terms, (3) run ledger-context simulations akin to Plutarch’s `pscript`.
- **Deliverables**: demo contracts (spending, minting, staking) authored in Moist and validated against the ledger models.

### 8. Documentation, Spec Sync, and CI Tooling
- **Docs**: mirror `plutarch-docs` by building `docs/` (Lean + Markdown) that introduce Moist, include API references, and show migration guides for Plutarch users.
- **Spec linkage**: update chapters under `spec/` to cite Lean proofs/implementations, and regenerate PDFs via `make -C spec` for every milestone.
- **CI/build**: configure Lake + GitHub workflows analogous to `cabal`/`nix` pipelines (linting, `lake build`, `lake exe moist smoke`, PDF builds). Provide reproducible scripts so artifacts (hex, pdf) can be attached to PRs per repo guidelines.
- **Deliverables**: automated checks gating contributions, contributor guide referencing `AGENTS.md`, and published documentation site.

## Suggested Ordering & Dependencies
1. Milestones 1–2 lay the runtime + DSL foundation.
2. Milestones 3–5 build user-facing ergonomics; they can progress in parallel once milestone 2 lands.
3. Milestone 6 depends on the DSL & utilities for meaningful benchmarks.
4. Milestone 7 requires stable data representations (milestone 4) and utility coverage (milestone 5).
5. Milestone 8 spans the full effort but should have initial scaffolding (docs + CI) established after milestone 2, then enriched as new features appear.

Tracking progress via this plan (update `Plans.md` as milestones close) will ensure Moist converges toward feature parity with Plutarch while staying reproducible per the repo guidelines.

