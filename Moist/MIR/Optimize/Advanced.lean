import Moist.MIR.Optimize.Advanced.Constants
import Moist.MIR.Optimize.Advanced.Shapes
import Moist.MIR.Optimize.Advanced.DataShapes
import Moist.MIR.Optimize.Advanced.Allocations
import Moist.MIR.Optimize.Advanced.Sharing
import Moist.MIR.Optimize.Advanced.Placement
import Moist.MIR.Optimize.Advanced.Products
import Moist.MIR.Optimize.Advanced.Records
import Moist.MIR.Optimize.Advanced.Recursion
import Moist.MIR.Optimize.Advanced.CheckedBranches
import Moist.MIR.Optimize.Advanced.TagChains
import Moist.MIR.Optimize.Advanced.KnownLists
import Moist.MIR.Optimize.Advanced.FailFast
import Moist.MIR.Optimize.Advanced.TagGuard
import Moist.MIR.Optimize.Advanced.Guards
import Moist.MIR.Optimize.CaseMerge
import Moist.MIR.Optimize.PreLower

namespace Moist.MIR.Advanced

/-! Checked-value simplification and explicitly selected allocation trade-offs.

The intended contract preserves values, failure, divergence, and Trace order,
not exact resource usage. Whole-pass proofs cover only the subset listed in
docs/MIR-Remaining-Pass-Proofs.md and use contextual halting/error refinement
through lowerTotalExpr, not native CEK or trace equivalence.
Cost-sensitive sharing and packing are kept separate from the simplification
loop so inlining cannot undo them.
Structural list and pair deconstruction runs after checked pre-lowering, while
its original builtin provenance is still available and before final allocation.
-/

structure Options where
  packApplications : Bool := true
  /-- Share repeated closed values, large constants and forced builtins at
      their lowest dominating node, keeping only bindings that make no
      successful run slower (`shareLow`). -/
  shareLow : Bool := true
  lowSharing : LowOptions := {}
  shareBuiltinStates : Bool := false
  poolConstants : Bool := false
  minimumBuiltinUses : Nat := 2
  minimumConstantBytes : Nat := 32
  deriving Repr

def prepare (expression : Expr) : Expr :=
  eliminateDeadFix (shareDelayedValues expression)

def structural (expression : Expr) : Expr :=
  checksFirst (failFast (tagGuards (fuseKnownListCases (unpackRecords (optimizeCheckedBranches
    (destructureProducts (fuseListChoices expression)))))))

def simplify (expression : Expr) : Expr :=
  caseTagChains (shapeDCE (specializeDataChecks
    (foldDataConstructors (constantFold (fuseListDestructors expression)))))

def preLower (expression : Expr) : Expr :=
  go 4 expression
where
  go : Nat → Expr → Expr
    | 0, current => current
    | fuel + 1, current =>
      let next := preLowerInlineExpr ((caseMergePass (simplify current)).1)
      if alphaEq current next then next else go fuel next

def finish (expression : Expr) (options : Options := {}) : Expr :=
  let packed := if options.packApplications then packApplications 3 expression else expression
  let low := if options.shareLow then shareLow options.lowSharing packed else packed
  let shared := if options.shareBuiltinStates then
    hoistBuiltinStates (max 1 options.minimumBuiltinUses) low else low
  if options.poolConstants then poolConstants options.minimumConstantBytes shared else shared

end Moist.MIR.Advanced
