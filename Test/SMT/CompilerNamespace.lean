import Moist.SMT.Compiler

/-!
# Executable compiler namespace boundary

The canonical validation API belongs to `Moist.SMT.Compiler.Validation`.
The old proof-namespace spelling remains a source-compatibility export of the
same declaration, rather than a second executable implementation.
-/

namespace Test.SMT.CompilerNamespace

open Moist.Plutus.Term

example (builtin : BuiltinFun) :
    Moist.SMT.Compiler.Validation.builtinAllowedForSoundness builtin =
      Moist.SMT.UPLC.Soundness.builtinAllowedForSoundness builtin := rfl

example :
    Moist.SMT.Compiler.Validation.ApplicationSignature =
      Moist.SMT.UPLC.Soundness.ApplicationSignature := rfl

end Test.SMT.CompilerNamespace
