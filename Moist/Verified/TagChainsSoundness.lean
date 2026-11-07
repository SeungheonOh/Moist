import Moist.Verified.TagChainsSoundness.Tests
import Moist.Verified.TagChainsSoundness.Rules
import Moist.Verified.TagChainsSoundness.Push
import Moist.Verified.TagChainsSoundness.Binding
import Moist.Verified.TagChainsSoundness.Walk

/-! # Constructor-tag test chains as integer cases

`caseTagChains` turns chains of `equalsInteger tag c` tests of a known integer
tag into integer cases and failing ranges into two comparisons
(`tagCaseRule_rewrites`), pushes applications into trees of field-less cases
(`pushArgument_rewrites`), moves single-use tests into the case they decide
(`unanfCase_rewrites`) and drops returning bindings that become unused
(`deadTag_rewrites`). The walk refines its input under the facts recorded for
its bindings (`tagChainWalk_factRel`), so the pass refines contextually
(`caseTagChains_refines`).
-/
