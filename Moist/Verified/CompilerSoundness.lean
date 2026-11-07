import Moist.Verified.PipelineSoundness
import Moist.Verified.BetaReduceSoundness
import Moist.Verified.ForceDelaySoundness
import Moist.Verified.DelaySharingSoundness
import Moist.Verified.CaseMergeSoundness
import Moist.Verified.CSESoundness
import Moist.Verified.StaticArgumentsSoundness
import Moist.Verified.AllocationFinishSoundness
import Moist.Verified.EtaReduceSoundness
import Moist.Verified.PreLowerSoundness
import Moist.Verified.FloatOutSoundness
import Moist.Verified.ShapesSoundness
import Moist.Verified.ProductsSoundness
import Moist.Verified.RecordsSoundness
import Moist.Verified.CheckedBranchesSoundness

/-! # Soundness of `compileOptimized`

Every optimizer stage is certified for every MIR expression, so the stage
hypotheses of `compileOptimized_refines_of` are discharged here. The final
theorems hold for every input, fresh-name start and `Advanced.Options` value:
a successful compilation emits UPLC that contextually refines the certified
lowering of the source, and compilation fails only on input rejected by
`validateCompilationInput`. -/

namespace Moist.Verified.Pipeline

open Moist.MIR
open Moist.Plutus.Term (Term)
open Moist.Verified.Contextual (CtxRefines)
open Moist.Verified.MIR (MIRCtxRefines)

theorem structural_refines (e : Expr) : MIRCtxRefines e (Advanced.structural e) :=
  structural_refines_of Moist.Verified.MIR.fuseListChoices_refines
    Moist.Verified.MIR.destructureProducts_refines
    Moist.Verified.MIR.optimizeCheckedBranches_refines
    Moist.Verified.MIR.unpackRecords_refines e

theorem stageCertificates : StageCertificates where
  staticArguments := Moist.Verified.MIR.staticArguments_refines
  prepare := Moist.Verified.MIR.prepare_refines
  floatOut := Moist.Verified.FloatOut.floatOut_refines
  betaReduce := Moist.Verified.MIR.BetaReduce.betaReducePass_refines
  caseMerge := Moist.Verified.CaseMerge.caseMergePass_refines
  simplify := Moist.Verified.MIR.simplify_refines
  cse := Moist.Verified.MIR.cse_refines
  etaReduce := Moist.Verified.MIR.etaReduce_refines
  forceDelay := Moist.Verified.ForceDelaySoundness.forceDelay_refines
  preLowerInline := Moist.Verified.MIR.PreLower.preLowerInlineExpr_refines
  structural := structural_refines

theorem preLower_refines' (e : Expr) : MIRCtxRefines e (Advanced.preLower e) :=
  preLower_refines stageCertificates e

/-- **End-to-end soundness of the production compiler.** If `compileOptimized`
    succeeds, the source lowers through `lowerTotalExpr` and the emitted UPLC
    refines it in every closing context: the output stays closed, and whenever
    the source halts (resp. errors) in that context, so does the output. -/
theorem compileOptimized_refines {e : Expr} {optFresh lowerFresh : Nat}
    {options : Advanced.Options} {t : Term}
    (h : compileOptimized e optFresh lowerFresh options = .ok t) :
    ∃ t₀, lowerTotalExpr [] e = some t₀ ∧ CtxRefines t₀ t :=
  compileOptimized_refines_of_certificates stageCertificates
    (Moist.Verified.MIR.finish_refines · options) h

/-- `compileOptimized` fails only with the input validator's error. -/
theorem compileOptimized_error {e : Expr} {optFresh lowerFresh : Nat}
    {options : Advanced.Options} {msg : String}
    (h : compileOptimized e optFresh lowerFresh options = .error msg) :
    validateCompilationInput [] e = .error msg :=
  compileOptimized_error_of_certificates stageCertificates
    (Moist.Verified.MIR.finish_refines · options) h

end Moist.Verified.Pipeline
