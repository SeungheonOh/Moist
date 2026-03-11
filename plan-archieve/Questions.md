# Open Questions and Decisions

Questions encountered during implementation of Phases 1-6.

## Architecture Decisions Made

1. **ifThenElse as def, not axiom**: Changed from axiom to `noncomputable def` with a `match` body. This lets it unfold to `Bool.casesOn` → `Case` in MIR, avoiding the Force/Delay wrapping that the UPLC `IfThenElse` builtin requires.

2. **SOP as default encoding**: All inductives use SOP (Constr/Case) by default. Only types marked `@[plutus_data]` use Data encoding (ConstrData/UnConstrData). This matches PlutusV3 capabilities.

3. **WellFounded.fix for recursion**: Lean's equation compiler produces `WellFounded.fix` for recursive definitions. We intercept this before whnf and extract the body function, producing a `Fix` MIR node that lowers to the Z combinator.

4. **Proof stripping in recursive calls**: Inside WellFounded.fix, the recursive function takes `(value, proof)` but we strip the proof argument, keeping only the value.

## Open Questions

### Type System

1. **Structural recursion**: Currently only WellFounded.fix (well-founded recursion) is handled. Lean's `*.rec`/`*.recOn` for structural recursion on inductives is not yet supported. Should we add this?

2. **Mutual recursion**: Not implemented. Should we support it? Plutus doesn't have native mutual recursion, so it would require lambda-lifting or defunctionalization.

3. **Polymorphic types at runtime**: Currently all type parameters are erased. This is correct for monomorphic usage but could cause issues if a polymorphic function is partially applied and the type parameter affects runtime behavior.

### Data Encoding

4. **Bool in @[plutus_data] fields**: Currently Bool fields in `@[plutus_data]` types are not specially handled. Should Bool be encoded as `ConstrData 0/1 []` when used as a Data field? Or should `@[plutus_data]` types only contain Int/ByteString/Data/other-@[plutus_data] fields?

5. **Nested @[plutus_data] field wrapping**: When a `@[plutus_data]` type has a field of another `@[plutus_data]` type, the inner value is assumed to already be Data. Is this correct, or do we need explicit wrapping?

6. **List fields in Data**: `List Data` fields use `ListData`/`UnListData`. But what about `List Int` or `List (SomeType)`? Should we auto-derive list encoding?

### ScriptContext

7. **TxInfo field access**: TxInfo has ~15 fields in PlutusV3. Currently it's an opaque `Data` alias. Should we generate field accessor functions, or let users manually destructure with Data operations?

8. **Redeemer/Datum typing**: In PlutusV3, the redeemer is passed as `Data`. Should `compile!` automatically insert `fromData` conversion based on the validator's type signature?

### Optimization

9. **Case-of-known-constructor**: Not yet implemented in the optimizer. When `Case (Constr tag args) alts` appears, we should reduce to `alts[tag] applied to args`. This would significantly improve code that constructs and immediately matches.

10. **Data encoding optimization**: The Data encoding generates many intermediate let bindings (pair, tag, fields). The optimizer should be able to inline these when they're used once.

### Tooling

11. **Error messages**: Translation errors currently show raw Lean.Expr fragments. Should we add source location tracking to provide better error messages?

12. **pError handling**: `pError` is declared as an axiom but has no BuiltinFun mapping. Should it lower to UPLC `Error` directly?

13. **Script serialization**: The pipeline currently produces UPLC `Term`. The last step to deploy on-chain is CBOR serialization. The PlutusCore package has encoding support — should `compile!` also produce the serialized form?
