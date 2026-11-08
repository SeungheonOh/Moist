import Test.Comparison.Validators
import Test.Comparison.Cross.Sample
import Test.Comparison.Cross.Constitution
import Test.Comparison.Cross.Crowdfund
import Test.Comparison.Cross.Settings
import Test.Comparison.Cross.Hydra
import Test.Comparison.Cross.ProgrammableLogicGlobal
import Test.Comparison.Edge.ListSum
import Test.Comparison.Edge.MapFilterCount
import Test.Comparison.Edge.WideRecord
import Test.Comparison.Edge.ValueLookup
import Test.Comparison.Edge.EnumDispatch
import Test.Comparison.Edge.GuardOrder
import Test.Comparison.Edge.ByteSearch
import Test.Comparison.Edge.NestedLists
import Test.Comparison.Edge.Horner
import Test.Comparison.Edge.AllAny
import Moist.Onchain.ToExpr
import Moist.Onchain.Translate
import Moist.Plutus.CBOR
import Lean.ToExpr

/-! # The cross-language validators as MIR

`mir! name` translates an `@[onchain]` definition to MIR at elaboration time
and reflects the MIR itself (not its UPLC), so the differential runner can
compile it without optimization, through every stage, and with every option. -/

namespace Test.MIR.FuzzReal.Validators

open Moist.MIR
open Moist.Onchain.ToExprInstances

deriving instance Lean.ToExpr for VarOrigin
deriving instance Lean.ToExpr for VarId
deriving instance Lean.ToExpr for Expr

open Lean Elab Term in
elab "mir! " target:ident : term => do
  let name ← resolveGlobalConstNoOverload target
  let info ← getConstInfo name
  let some body := info.value? | throwError "Expected a definition"
  let expression ← Moist.Onchain.translateDefByName name body
  return toExpr expression

set_option maxRecDepth 100000

def voting : Expr := mir! Test.Comparison.Validators.voting
def certifying : Expr := mir! Test.Comparison.Validators.certifying
def vesting : Expr := mir! Test.Comparison.Validators.vesting
def sample : Expr := mir! Test.Comparison.Cross.Sample.netWithdraw
def constitution : Expr := mir! Test.Comparison.Cross.Constitution.constitution
def crowdfund : Expr := mir! Test.Comparison.Cross.Crowdfund.crowdfund
def settings : Expr := mir! Test.Comparison.Cross.Settings.settings
def hydra : Expr := mir! Test.Comparison.Cross.Hydra.hydraHead
def programmableLogicGlobal : Expr :=
  mir! Test.Comparison.Cross.ProgrammableLogicGlobal.programmableLogicGlobal
def listSum : Expr := mir! Test.Comparison.Edge.ListSum.listSum
def mapFilterCount : Expr := mir! Test.Comparison.Edge.MapFilterCount.mapFilterCount
def wideRecord : Expr := mir! Test.Comparison.Edge.WideRecord.wideRecord
def valueLookup : Expr := mir! Test.Comparison.Edge.ValueLookup.valueLookup
def enumDispatch : Expr := mir! Test.Comparison.Edge.EnumDispatch.enumDispatch
def guardOrder : Expr := mir! Test.Comparison.Edge.GuardOrder.guardOrder
def byteSearch : Expr := mir! Test.Comparison.Edge.ByteSearch.byteSearch
def nestedLists : Expr := mir! Test.Comparison.Edge.NestedLists.nestedLists
def horner : Expr := mir! Test.Comparison.Edge.Horner.horner
def allAny : Expr := mir! Test.Comparison.Edge.AllAny.allAny

/-- `(validator, MIR)`, named as in the cross-bench data directory. -/
def registry : List (String × Expr) := [
  ("Voting", voting), ("Certifying", certifying), ("Vesting", vesting), ("Sample", sample),
  ("Constitution", constitution), ("Crowdfund", crowdfund), ("Settings", settings),
  ("Hydra", hydra), ("ProgrammableLogicGlobal", programmableLogicGlobal),
  ("EdgeListSum", listSum), ("EdgeMapFilterCount", mapFilterCount),
  ("EdgeWideRecord", wideRecord), ("EdgeValueLookup", valueLookup),
  ("EdgeEnumDispatch", enumDispatch), ("EdgeGuardOrder", guardOrder),
  ("EdgeByteSearch", byteSearch), ("EdgeNestedLists", nestedLists), ("EdgeHorner", horner),
  ("EdgeAllAny", allAny)]

/-- The scripts `cross_bench_export` writes: `(validator, default, size options)`. -/
def exported : List (String × Moist.Plutus.Term.Term × Moist.Plutus.Term.Term) := [
  ("Voting", Test.Comparison.Validators.votingScript, Test.Comparison.Validators.votingSize),
  ("Certifying", Test.Comparison.Validators.certifyingScript, Test.Comparison.Validators.certifyingSize),
  ("Vesting", Test.Comparison.Validators.vestingScript, Test.Comparison.Validators.vestingSize),
  ("Sample", Test.Comparison.Cross.Sample.script, Test.Comparison.Cross.Sample.scriptSize),
  ("Constitution", Test.Comparison.Cross.Constitution.script, Test.Comparison.Cross.Constitution.scriptSize),
  ("Crowdfund", Test.Comparison.Cross.Crowdfund.script, Test.Comparison.Cross.Crowdfund.scriptSize),
  ("Settings", Test.Comparison.Cross.Settings.script, Test.Comparison.Cross.Settings.scriptSize),
  ("Hydra", Test.Comparison.Cross.Hydra.script, Test.Comparison.Cross.Hydra.scriptSize),
  ("ProgrammableLogicGlobal", Test.Comparison.Cross.ProgrammableLogicGlobal.script, Test.Comparison.Cross.ProgrammableLogicGlobal.scriptSize),
  ("EdgeListSum", Test.Comparison.Edge.ListSum.script, Test.Comparison.Edge.ListSum.scriptSize),
  ("EdgeMapFilterCount", Test.Comparison.Edge.MapFilterCount.script, Test.Comparison.Edge.MapFilterCount.scriptSize),
  ("EdgeWideRecord", Test.Comparison.Edge.WideRecord.script, Test.Comparison.Edge.WideRecord.scriptSize),
  ("EdgeValueLookup", Test.Comparison.Edge.ValueLookup.script, Test.Comparison.Edge.ValueLookup.scriptSize),
  ("EdgeEnumDispatch", Test.Comparison.Edge.EnumDispatch.script, Test.Comparison.Edge.EnumDispatch.scriptSize),
  ("EdgeGuardOrder", Test.Comparison.Edge.GuardOrder.script, Test.Comparison.Edge.GuardOrder.scriptSize),
  ("EdgeByteSearch", Test.Comparison.Edge.ByteSearch.script, Test.Comparison.Edge.ByteSearch.scriptSize),
  ("EdgeNestedLists", Test.Comparison.Edge.NestedLists.script, Test.Comparison.Edge.NestedLists.scriptSize),
  ("EdgeHorner", Test.Comparison.Edge.Horner.script, Test.Comparison.Edge.Horner.scriptSize),
  ("EdgeAllAny", Test.Comparison.Edge.AllAny.script, Test.Comparison.Edge.AllAny.scriptSize)]

end Test.MIR.FuzzReal.Validators
