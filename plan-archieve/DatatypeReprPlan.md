# Datatype Representation Resolution Plan

## Goal

Make datatype lowering systematic enough that `@[plutus_data]` really means:

- the runtime representation of the type is `Data`
- every stored field is either already `Data` or can be explicitly converted to `Data`
- incompatible fields fail during elaboration instead of silently generating invalid MIR

This should reject cases like:

```lean
@[plutus_sop]
inductive Foo where
  | mk : Foo

@[plutus_data]
inductive Bar where
  | hi : Foo -> Bar
```

and accept cases like:

```lean
@[plutus_data]
inductive Baz where
  | xs : List Int -> Baz

@[plutus_data]
inductive Qux where
  | inner : Baz -> Qux
```

## Current Problem

The current translator does not actually resolve field representation. It uses ad hoc wrappers in [`Moist/Onchain/Translate.lean`](/Users/sho/fun/moist/Moist/Onchain/Translate.lean):

- `toDataWrapper` only knows about `Int`, `ByteString`, `Data`, `@[plutus_data]` names, and exactly `List Data`
- `fromDataWrapper` has the same limitation
- everything else falls through to `none`, which `wrapToData`/`wrapFromData` interpret as identity

That means unsupported field types are currently treated as if they were already `Data`.

Concrete bad outcomes already present in the tree:

- `List TxInInfo`, `List TxOut`, `List TxCert`, `List ProposalProcedure`, etc. in [`Moist/Cardano/V3.lean`](/Users/sho/fun/moist/Moist/Cardano/V3.lean) are not actually handled by the current `List Data` special case.
- `Bool` fields in `LowerBound` and `UpperBound` are also not handled, but currently pass through as if `Bool ~ Data`.
- an `@[plutus_sop]` value can currently be stored inside an `@[plutus_data]` type if it reaches the translator in a shape the wrapper logic does not understand.

So the flaw is deeper than missing a few cases. The design is currently using "unknown means maybe already `Data`", but it needs "unknown means elaboration failure".

## Desired Semantics

We need two related but distinct notions:

### 1. Runtime representation of a type

At minimum:

- `Int` -> builtin integer
- `ByteString` -> builtin bytestring
- `Data` -> builtin data
- `List α` -> builtin list of `α`
- `@[plutus_sop]` or default inductive -> SOP
- `@[plutus_data]` inductive -> `Data`
- `abbrev`/transparent aliases -> same representation as the target

### 2. Data compatibility of a type

A type should be classified as one of:

- `alreadyData`
  - `Data`
  - any `@[plutus_data]` type
  - transparent aliases to the above
- `wrappedToData codec`
  - `Int` via `IData`/`UnIData`
  - `ByteString` via `BData`/`UnBData`
  - `List α` if `α` itself is data-compatible
  - later: maps/pairs if you add typed support
- `notDataCompatible reason`
  - SOP types
  - functions
  - propositions/erased fields can be skipped before this point
  - unknown applications that do not have a registered codec

This is the key separation: a type can have a valid runtime representation without being embeddable inside `Data`.

## Recommended Model

Instead of returning `Option BuiltinFun`, introduce a total resolution step that produces an explicit plan.

### A. Represent runtime shape

Something in this direction:

```lean
inductive RuntimeRepr
  | int
  | byteString
  | data
  | list (elem : RuntimeRepr)
  | sop (typeName : Name)
  | opaque (typeName : Name)
```

This does not need to be perfect on day 1. It just needs to stop pretending that unknown types are `Data`.

### B. Represent how a value enters/leaves `Data`

```lean
inductive DataCodecPlan
  | identity
  | iData
  | bData
  | list (elem : DataCodecPlan)
```

Then expose:

```lean
resolveRuntimeRepr : Environment -> Expr -> MetaM RuntimeRepr
resolveDataCodec?  : Environment -> Expr -> MetaM (Except DataCompatError DataCodecPlan)
```

`resolveDataCodec?` should recurse structurally:

- `Int` -> `.ok .iData`
- `ByteString` -> `.ok .bData`
- `Data` -> `.ok .identity`
- `@[plutus_data]` type -> `.ok .identity`
- `List α` -> recurse on `α`; if successful, return `.list elemCodec`
- `@[plutus_sop]` type -> `.error ...`
- anything unknown -> `.error ...`

This gives you one source of truth for both constructor encoding and match decoding.

## How Translation Would Change

### Constructor lowering for `@[plutus_data]`

Current code builds:

- `ConstrData tag [wrapToData field0, wrapToData field1, ...]`

but `wrapToData` is too weak. Replace it with something like:

```lean
encodeFieldToData : Environment -> Expr -> MIR.Expr -> TranslateM MIR.Expr
```

which first calls `resolveDataCodec?`. If resolution fails, throw an elaboration error immediately.

For a list field:

- if the field type is `List α`
- and `α` resolves to a valid `DataCodecPlan`
- generate a MIR map-like traversal that converts each element to `Data`
- then wrap the resulting `List Data` with `ListData`

The important consequence is that `List Int` works, `List TxOutRef` works when `TxOutRef` is `@[plutus_data]`, and `List Foo` fails when `Foo` is SOP.

### Match lowering for `@[plutus_data]`

Field extraction should mirror the same plan:

- `Data` / `@[plutus_data]` fields: pass through directly
- `Int`: `UnIData`
- `ByteString`: `UnBData`
- `List α`: `UnListData` plus recursive decode of elements

This means the constructor path and match path share exactly one compatibility decision.

## Important Design Choice: Validate Early

Do not wait until a constructor or pattern match is translated.

Better behavior:

1. When an inductive is marked `@[plutus_data]`, inspect all constructor field types.
2. For each non-erased field, run `resolveDataCodec?`.
3. Cache the result or fail the declaration immediately.

This gives the behavior the user expects:

- `Bar` above fails at declaration time
- not later when some unrelated `compile!` touches it

In Lean terms, there are two viable places for this:

- inside the attribute handler for `@[plutus_data]`
- in a dedicated environment extension populated by a command/elaboration hook

Even if immediate declaration-time rejection is awkward to wire initially, the compatibility check should still be implemented as a reusable pass so it can later be moved earlier without redesign.

## Suggested Implementation Directions

## Option 1: Minimal, translator-local fix

Scope:

- replace `toDataWrapper` / `fromDataWrapper`
- introduce `resolveDataCodec?`
- make unknown/incompatible types hard fail
- add recursive support for `List α`

Pros:

- smallest diff
- fixes the unsoundness quickly
- directly supports the examples in the request

Cons:

- failure happens during `compile!`, not at datatype declaration
- representation knowledge stays trapped inside `Translate.lean`

This is the fastest safe fix, but not the cleanest end state.

## Option 2: Recommended next step

Scope:

- keep surface attributes `@[plutus_sop]` and `@[plutus_data]`
- add a dedicated representation/data-compatibility resolver module
- validate every `@[plutus_data]` inductive once and record per-field codec plans in an environment extension
- translator consumes the cached plans

Pros:

- one source of truth
- declaration-time rejection becomes possible
- constructor lowering and match lowering become symmetric
- future support for `Map`, pairs, transparent newtypes, etc. has a natural home

Cons:

- more plumbing than option 1

This is the best fit for the problem as described.

## Option 3: Full representation framework

Scope:

- replace the two tag attributes with a single parametric repr attribute internally
- track runtime representation and `Data` compatibility separately
- possibly expose user-facing deriving/registration hooks for custom codecs

Pros:

- most systematic
- aligns with the way Plutarch treats representation as a type-level property

Cons:

- more redesign than you need to solve the immediate bug

I would not start here unless you already want a larger deriving overhaul.

## Recommended Staging

### Stage 1

Build `resolveDataCodec?` and make unsupported field types fail hard.

This alone fixes the core unsoundness:

- no more silent identity fallback
- no more SOP-inside-Data
- `List α` becomes recursive instead of hardcoded to `List Data`

### Stage 2

Move compatibility checking to datatype elaboration time for `@[plutus_data]`.

Cache per-constructor/per-field plans so translation does not need to rediscover them.

### Stage 3

Add more data-compatible families as needed:

- `Bool` if you decide its `Data` representation is supported
- map-like containers
- transparent single-field wrappers/newtypes

Do not add these before the compatibility framework exists, otherwise you will just grow the current ad hoc table.

## Bool Decision

This needs an explicit policy before implementation.

Two coherent choices:

### Policy A: strict builtins only

Allow only:

- `Int`
- `ByteString`
- `Data`
- `List α` where `α` is data-compatible
- other `@[plutus_data]` types

Under this policy, `Bool` inside `@[plutus_data]` is rejected.

This is the simplest and most defensible first version.

### Policy B: treat `Bool` as a data-encoded ADT

Encode:

- `true` as `ConstrData 0 []`
- `false` as `ConstrData 1 []`

This is reasonable, but it means `Bool` needs an explicit codec plan just like a tiny `@[plutus_data]` type. It should not be left as an implicit fallback.

My recommendation is Policy A first, then add Policy B intentionally if needed.

## Validation Matrix

These should be the first regression tests once implementation starts:

- `@[plutus_data] inductive Bar | hi : Foo -> Bar` where `Foo` is SOP -> must fail
- `@[plutus_data] inductive Bar | hi : List Foo -> Bar` where `Foo` is SOP -> must fail
- `@[plutus_data] inductive Bar | hi : List Int -> Bar` -> must succeed
- `@[plutus_data] inductive Bar | hi : List ByteString -> Bar` -> must succeed
- `@[plutus_data] inductive Bar | hi : List Baz -> Bar` where `Baz` is `@[plutus_data]` -> must succeed
- `@[plutus_data] inductive Bar | hi : Data -> Bar` -> must succeed
- `@[plutus_data] inductive Bar | hi : Bool -> Bar` -> fail or succeed according to the chosen policy, but never silently

Also re-check existing ledger types in [`Moist/Cardano/V3.lean`](/Users/sho/fun/moist/Moist/Cardano/V3.lean), because that file is currently the best stress test for nested `@[plutus_data]` fields.

## Short Recommendation

The central mistake is using wrapper lookup as a proxy for representation checking.

The fix is:

1. resolve the representation/data-compatibility of every field type explicitly
2. make `@[plutus_data]` require successful field-by-field `Data` compatibility
3. use the resulting codec plan for both constructor encoding and match decoding
4. reject unknown or SOP-only field types instead of treating them as identity

If we implement only one thing next, it should be a recursive `resolveDataCodec?` with hard failure on unsupported types.
