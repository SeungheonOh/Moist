# Typed ledger values

`Moist.Cardano.V3` defines the V3 ledger datatypes and their Data encodings. Use
`ScriptContext`, `TxInfo`, `TxInInfo`, `TxOut`, `Value`, `Address`, `Credential`,
`ScriptInfo`, and the certificate/governance datatypes directly. Contract code
should project named fields and match constructors, not count fields in raw Data.

Define application datums and redeemers with `@[plutus_data]`. Keep Data at the
external script boundary and in genuinely opaque ledger fields such as `Datum`,
`Redeemer`, and `ChangedParameters`; decode these to application types where used.
`PlutusData.unsafeFromData` compiles primitive decoders and collection codecs as
well as Data-backed structures. `PlutusData.fromData` remains a native Lean API;
using it on-chain is rejected rather than emitting an invalid Data case expression.
Unsafe decoding is not a complete input-schema validation layer.

## Encoding details

- `PubKeyHash`, `CurrencySymbol`, `TokenName`, `TxId`, `Lovelace`, and `POSIXTime`
  retain their transparent byte-string/integer wire representations.
- `Constitution` is **not** transparent: it encodes as constructor 0 containing
  the optional script hash. This matches upstream's indexed Data instance.
- Lists of primitive values decode their elements to native UPLC values; nested
  lists retain the corresponding builtin element types, including empty lists.
- `AssocMap` stays a builtin list of Data/Data pairs on-chain. Encoding does not
  encode its keys or values a second time.

## Typed maps

Import `Moist.Onchain` or `Moist.Onchain.AssocMap`. The latter provides typed
`lookup`, `delete`, `insert`, `foldl`, `foldr`, `firstValue?`, `hasMultiple`, `empty`, and
`singleton` operations. Keys and values are decoded at the operation boundary;
contract callers do not manipulate raw map entries.

`lookup` selects the first matching key. `delete` removes its first occurrence.
`insert` updates the first occurrence in place, or appends a new key. Unrelated
entry order and subsequent duplicate entries are preserved, matching the
upstream Data-backed map operations. These functions do not sort or deduplicate
maps. Ledger-valid maps should satisfy the ledger's ordering/uniqueness rules.

Native Lean code can use `AssocMap.toList` and construct maps from native lists.
On-chain, literal map entries are encoded by the compiler, but a dynamic native
list of unboxed typed pairs cannot be substituted for encoded map entries.
`toList`, pattern extraction, and dynamic-list construction are rejected when
their key/value representations differ. Use the typed map operations instead.
Raw Data/Data maps keep their native builtin pair representation.
An unresolved `PlutusData` specialization is rejected as well; recursive helpers
that need codecs should use concrete domain types rather than erased dictionaries.

## Recursive application datatypes

`@[plutus_data]` derives native codecs for non-indexed, monomorphic, non-mutual
recursive datatypes, including direct children and lists of children. Generated
encoders and decoders are total Lean definitions with checked termination proofs;
derivation fails if those proofs cannot be completed. Recursive map fields and
other unsupported recursive containers are rejected, not silently approximated.
On-chain values retain their Data representation; traversal matches the declared
constructors and decodes named fields. Well-founded list traversal erases Lean's
proof-only `Subtype`/`List.attach` wrappers.

`List.map` preserves builtin result element types, including empty lists.
Native `Prod` construction requires Data-backed fields because UPLC's dynamic
pair constructor takes Data/Data arguments. Use an explicit `@[plutus_sop]`
structure for internal state containing native integers, lists, or other values.

## Verification

`lake exe tests mir/eval/constitution_encoding` checks native and compiled
Constitution encodings. `lake exe tests mir/eval/collection_encoding` exercises
primitive/nested-list codecs, nested maps, map operations, malformed entries,
and unsupported-representation diagnostics through the native CEK evaluator.
`lake exe tests mir/eval/recursive_encoding` checks direct/list recursion, native
codec roundtrips and malformed-child rejection, and raw/default compiled traversal.
These are executable regression checks, not formal proofs of the frontend.

Encoding references: [V3 Contexts](https://github.com/IntersectMBO/plutus/blob/b2db512618df08bd696e8d9c4229effcede01169/plutus-ledger-api/src/PlutusLedgerApi/V3/Contexts.hs)
and [Data-backed AssocMap](https://github.com/IntersectMBO/plutus/blob/b2db512618df08bd696e8d9c4229effcede01169/plutus-tx/src/PlutusTx/Data/AssocMap.hs).
