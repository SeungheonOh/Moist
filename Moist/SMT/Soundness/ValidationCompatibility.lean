import Moist.SMT.Compiler.Validation

/-!
# Legacy validation names for proof modules

Executable validation is owned exclusively by `Moist.SMT.Compiler.Validation`.
This proof-side module preserves the historical unqualified names used inside
`Moist.SMT.UPLC.Soundness` without making the portable compiler facade create
or depend on a soundness namespace.
-/

namespace Moist.SMT.UPLC.Soundness

export Moist.SMT.Compiler.Validation
  ( builtinAllowedForSoundness
    builtinOpaqueForSoundness
    termUsesOpaqueBuiltinForSoundness
    termsUseOpaqueBuiltinForSoundness
    termNoOpaqueBuiltinsForSoundness
    symValNoOpaqueForSoundness
    symValsNoOpaqueForSoundness
    symEnvNoOpaqueForSoundness
    sanitizedNameTailChar
    declarationNameRendererSafe
    simpleSymbolCharRendererSafe
    simpleSymbolRendererSafe
    indexedTesterHeads
    applicationHeadRendererSafe
    nullaryApplicationHeads
    symbolAtomRendererSafe
    expressionRendererSafe
    expressionsRendererSafe
    ApplicationSignature
    applicationSignatures
    testerSignature?
    applicationResultSort?
    declarationSort?
    expressionSort?
    expressionSorts?
    expressionHasSort
    symConstSortSafe
    symValSortSafe
    symValsSortSafe
    symDeclSortSafe
    declarationsSortSafe
    totalApplicationHeads
    expressionTotalitySafe
    expressionsTotalitySafe
    directValSymbol
    nonnegativeLiteral
    inputSymConstSafe
    inputConstSymValSafe
    inputSymValSafe
    inputSymValsSafe
    requiredAssumptionMatches
    requiredAssumptionsPresent
    symDeclRequiredAssumptionsPresent
    symDeclInputSafe
    declarationsInputSafe
    declarationNamesDistinct
    symConstRendererSafe
    symValRendererSafe
    symValsRendererSafe
    symDeclRendererSafe
    declarationsRendererSafe
    matchesFixedPreludeCommand
    fixedPreludeCommand
    checkedDeclarationCommand
    generatedCommandSafe
    generatedCommandsSafe
    solverControlCommand
    generatedSolverControlSafe
    generatedAssertionsRendererSafe
    generatedAssertionsSortSafe )

end Moist.SMT.UPLC.Soundness
