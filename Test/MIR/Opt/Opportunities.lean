import Moist.MIR.Compile

/-! Benchmark configurations for the production optimization implementations. -/

namespace Test.MIR.Opt.Opportunities

open Moist.MIR

abbrev constantFold := Advanced.constantFold
abbrev foldDataConstructors := Advanced.foldDataConstructors
abbrev simplifyChoices := Advanced.simplifyChoices
abbrev shapeDCE := Advanced.shapeDCE
abbrev fuseListDestructors := Advanced.fuseListDestructors
abbrev packApplications (minimum : Nat := 3) := Advanced.packApplications minimum
abbrev shareDelayedValues := Advanced.shareDelayedValues
abbrev eliminateDeadFix := Advanced.eliminateDeadFix
abbrev hoistBuiltinStates (minimumUses : Nat := 2) := Advanced.hoistBuiltinStates minimumUses
abbrev poolConstants (minimumBytes : Nat := 32) := Advanced.poolConstants minimumBytes

def cleanup (expression : Expr) : Expr :=
  preLowerInlineExpr (caseMergePass (constantFold (simplifyChoices expression))).1

def shapeDataCleanup (expression : Expr) : Expr :=
  foldDataConstructors (preLowerInlineExpr (shapeDCE (cleanup expression)))

def candidates : List (String × (Expr → Expr)) :=
  [("constant-fold", constantFold),
   ("data-fold", foldDataConstructors),
   ("boolean-case", simplifyChoices),
   ("shape-dce", shapeDCE),
   ("list-fusion", fuseListDestructors),
   ("pack-app3", packApplications 3),
   ("delay-share", shareDelayedValues),
   ("dead-fix", eliminateDeadFix),
   ("builtin-share2", hoistBuiltinStates 2),
   ("builtin-share1", hoistBuiltinStates 1),
   ("constant-pool", poolConstants 32),
   ("cleanup", cleanup),
   ("shape-cleanup", fun expression => preLowerInlineExpr (shapeDCE (cleanup expression))),
   ("data-cleanup", shapeDataCleanup),
   ("shape-data6", fun expression => (List.range 6).foldl
     (fun current _ => shapeDataCleanup current) expression),
   ("combined", fun expression =>
     poolConstants 32 (hoistBuiltinStates 2 (packApplications 3 (cleanup expression))))]

def production (options : Advanced.Options := {}) (expression : Expr)
    : Except String Moist.Plutus.Term.Term :=
  compileOptimized expression 1000 5000 options

def productionProfiles : List (String × Advanced.Options) :=
  [("production-default", {}),
   ("production-unpacked", { packApplications := false }),
   ("production-shared", { shareBuiltinStates := true }),
   ("production-size", { poolConstants := true }),
   ("production-all", {
     packApplications := true, shareBuiltinStates := true, poolConstants := true })]

def productionCandidates : List (String × (Expr → Except String Moist.Plutus.Term.Term)) :=
  candidates.map (fun (name, transform) => (name, fun expression => lowerExpr (transform expression))) ++
    productionProfiles.map (fun (name, options) => (name, production options))

end Test.MIR.Opt.Opportunities
