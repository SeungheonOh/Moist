import Moist.Verified.LoweringSoundness
import Moist.Verified.ANFSoundness
import Moist.Verified.DCESoundness
import Moist.Verified.InlineSoundness
import Moist.Verified.HygieneSoundness
import Moist.Verified.DeadFixSoundness
import Moist.Verified.ConstantFoldingSoundness
import Moist.Verified.DataFoldingSoundness
import Moist.Verified.AllocationFinishSoundness
import Moist.MIR.Compile

/-! # Soundness of the production compiler

`compileOptimized_refines_of`: if `compileOptimized` succeeds, the source
lowers through `lowerTotalExpr` and the emitted UPLC contextually refines it.
The certificates of the passes that are not yet proved are hypotheses; every
hypothesis is quantified over all expressions (and fresh states, options and
fresh starts where the pass takes them). ANF, binder hygiene, DCE and inlining
are used directly.

Fresh-name states are threaded through `Post`: a property of the result of a
state computation that holds from every initial state. -/

namespace Moist.Verified.Pipeline

open Moist.MIR
open Moist.Plutus.Term (Term)
open Moist.Verified.Contextual (CtxRefines ctxRefines_trans)
open Moist.Verified.MIR (MIRCtxRefines mirCtxRefines_refl mirCtxRefines_trans)
open Moist.Verified.LoweringSoundness

/-! ## Results of state computations -/

/-- `P` holds of the result of `m` from every initial state. -/
def Post {σ α : Type} (m : StateM σ α) (P : α → Prop) : Prop := ∀ s, P (m.run s).1

theorem Post.pure {σ α : Type} {a : α} {P : α → Prop} (h : P a) :
    Post (σ := σ) (Pure.pure a) P := fun _ => h

theorem Post.bind {σ α β : Type} {m : StateM σ α} {k : α → StateM σ β}
    {P : α → Prop} {Q : β → Prop} (hm : Post m P) (hk : ∀ a, P a → Post (k a) Q) :
    Post (m >>= k) Q := fun s => hk _ (hm s) _

theorem Post.unit {σ β : Type} {m : StateM σ Unit} {k : Unit → StateM σ β} {Q : β → Prop}
    (hk : Post (k ()) Q) : Post (m >>= k) Q := fun _ => hk _

theorem Post.mono {σ α : Type} {m : StateM σ α} {P Q : α → Prop} (h : Post m P)
    (hPQ : ∀ a, P a → Q a) : Post m Q := fun s => hPQ _ (h s)

/-! ## Stage certificates -/

/-- Certificates of the optimizer stages that are not proved in this module's
    imports. Each is a whole-pass statement over every expression. -/
structure StageCertificates : Prop where
  staticArguments : ∀ e, MIRCtxRefines e (Advanced.staticArguments e)
  prepare : ∀ e, MIRCtxRefines e (Advanced.prepare e)
  floatOut : ∀ e, MIRCtxRefines e (floatOut e).1
  betaReduce : ∀ e s, MIRCtxRefines e (betaReducePass e s).1.1
  caseMerge : ∀ e, MIRCtxRefines e (caseMergePass e).1
  simplify : ∀ e, MIRCtxRefines e (Advanced.simplify e)
  cse : ∀ e, MIRCtxRefines e (cse [] e).1
  etaReduce : ∀ e, MIRCtxRefines e (etaReduce e).1
  forceDelay : ∀ e, MIRCtxRefines e (forceDelay e).1
  preLowerInline : ∀ e n, MIRCtxRefines e (preLowerInlineExpr e n)
  structural : ∀ e, MIRCtxRefines e (Advanced.structural e)

theorem simplifyOnce_refines (C : StageCertificates) (e : Expr) :
    Post (simplifyOnce e) (MIRCtxRefines e) := by
  unfold simplifyOnce
  dsimp only
  refine Post.unit ?_
  dsimp only
  refine Post.bind (P := MIRCtxRefines e) (fun s => mirCtxRefines_trans (C.prepare e)
    (mirCtxRefines_trans (Moist.Verified.MIR.Hygiene.uniqueOptimizationBinders_refines _)
      (Moist.Verified.MIR.anfNormalize_refines _ s))) fun e0 h0 => ?_
  have h1 : MIRCtxRefines e (cse [] (Advanced.simplify (caseMergePass e0).1)).1 :=
    mirCtxRefines_trans h0 (mirCtxRefines_trans (C.caseMerge e0)
      (mirCtxRefines_trans (C.simplify _) (C.cse _)))
  have h2 := mirCtxRefines_trans h1 (Moist.Verified.MIR.dce_refines _)
  refine Post.unit ?_
  dsimp only
  refine Post.bind (P := fun p => MIRCtxRefines e p.1)
    (fun s => mirCtxRefines_trans h2 (Moist.Verified.MIR.inline_refines _ s)) fun p hp => ?_
  refine Post.bind (P := fun p => MIRCtxRefines e p.1)
    (fun s => mirCtxRefines_trans hp (C.betaReduce _ s)) fun q hq => ?_
  exact Post.pure (mirCtxRefines_trans hq
    (mirCtxRefines_trans (C.etaReduce _) (C.forceDelay _)))

theorem simplifyLoop_refines (C : StageCertificates) :
    ∀ (fuel : Nat) (e : Expr), Post (simplifyLoop e fuel) (MIRCtxRefines e)
  | 0, e => by simp only [simplifyLoop]; exact Post.pure (mirCtxRefines_refl e)
  | fuel + 1, e => by
    simp only [simplifyLoop]
    refine Post.bind (simplifyOnce_refines C e) fun e' h => ?_
    split
    · exact Post.pure (mirCtxRefines_refl e)
    · exact (simplifyLoop_refines C fuel e').mono fun _ h' => mirCtxRefines_trans h h'

theorem optimize_refines (C : StageCertificates) (e : Expr) :
    Post (optimize e) (MIRCtxRefines e) := by
  unfold optimize
  dsimp only
  refine Post.unit ?_
  dsimp only
  have h1 := mirCtxRefines_trans (C.prepare e) (C.floatOut (Advanced.prepare e))
  refine Post.bind (P := fun p => MIRCtxRefines e p.1)
    (fun s => mirCtxRefines_trans h1 (C.betaReduce _ s)) fun p hp => ?_
  refine Post.bind (P := MIRCtxRefines e)
    (fun s => mirCtxRefines_trans hp (Moist.Verified.MIR.anfNormalize_refines _ s))
    fun e3 h3 => ?_
  exact (simplifyLoop_refines C _ _).mono fun _ h =>
    mirCtxRefines_trans (mirCtxRefines_trans h3 (C.floatOut e3)) h

theorem optimizeExpr_refines (C : StageCertificates) (e : Expr) (freshStart : Nat) :
    MIRCtxRefines e (optimizeExpr e freshStart) :=
  optimize_refines C e ⟨freshStart⟩

/-- The pre-lowering fixed-point loop, from its stage certificates. -/
theorem preLower_go_refines (C : StageCertificates) :
    ∀ (fuel : Nat) (e : Expr), MIRCtxRefines e (Advanced.preLower.go fuel e)
  | 0, e => by simp only [Advanced.preLower.go]; exact mirCtxRefines_refl e
  | fuel + 1, e => by
    simp only [Advanced.preLower.go]
    have step := mirCtxRefines_trans (C.simplify e)
      (mirCtxRefines_trans (C.caseMerge _) (C.preLowerInline _ 5000))
    split
    · exact step
    · exact mirCtxRefines_trans step (preLower_go_refines C fuel _)

theorem preLower_refines (C : StageCertificates) (e : Expr) :
    MIRCtxRefines e (Advanced.preLower e) := preLower_go_refines C 4 e

theorem prepareForLowering_refines (C : StageCertificates) (e : Expr) (optFresh lowerFresh : Nat) :
    MIRCtxRefines e (prepareForLowering e optFresh lowerFresh) := by
  unfold prepareForLowering
  exact mirCtxRefines_trans (C.staticArguments e)
    (mirCtxRefines_trans (optimizeExpr_refines C _ optFresh)
      (mirCtxRefines_trans (C.preLowerInline _ lowerFresh)
        (mirCtxRefines_trans (preLower_refines C _) (C.structural _))))

/-! ## The production compiler -/

theorem compileOptimized_refines_of_certificates (C : StageCertificates)
    {options : Advanced.Options}
    (hFinish : ∀ e, MIRCtxRefines e (Advanced.finish e options)) {e : Expr}
    {optFresh lowerFresh : Nat} {t : Term}
    (h : compileOptimized e optFresh lowerFresh options = .ok t) :
    ∃ t₀, lowerTotalExpr [] e = some t₀ ∧ CtxRefines t₀ t := by
  unfold compileOptimized at h
  cases hv : validateCompilationInput [] e with
  | error m => simp [hv, bind, Except.bind] at h
  | ok u =>
    obtain ⟨t₀, ht₀⟩ := validate_ok_lowerTotalExpr (by cases u; exact hv)
    simp only [hv, bind, Except.bind] at h
    cases hl : lowerExpr (prepareForLowering e optFresh lowerFresh) (lowerFresh + 1000) with
    | error m => simp [hl] at h
    | ok term =>
      simp only [hl] at h
      have hP := (prepareForLowering_refines C e optFresh lowerFresh []).2
      obtain ⟨tP, htP, hPt, _⟩ := lowerExpr_sound hl
      rw [ht₀, htP] at hP
      have h₁ : CtxRefines t₀ term := ctxRefines_trans hP hPt
      split at h
      · have hF := (hFinish (liftUPLC term) []).2
        obtain ⟨tF, htF, hFt, _⟩ := lowerExpr_sound h
        rw [liftUPLC_lowerExpr hl 1, htF] at hF
        exact ⟨t₀, ht₀, ctxRefines_trans h₁ (ctxRefines_trans hF hFt)⟩
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact ⟨t₀, ht₀, h₁⟩

/-- **(d)** End-to-end soundness of `compileOptimized`, parameterized by the
    certificates of the stages proved elsewhere. ANF normalization, binder
    hygiene, DCE and inlining are certified in the imports; the pre-lowering
    loop `Advanced.preLower` is derived from its stages. If compilation
    succeeds, the source lowers and the emitted UPLC refines it in every
    context. -/
theorem compileOptimized_refines_of
    (hStatic : ∀ e, MIRCtxRefines e (Advanced.staticArguments e))
    (hPrepare : ∀ e, MIRCtxRefines e (Advanced.prepare e))
    (hFloat : ∀ e, MIRCtxRefines e (floatOut e).1)
    (hBeta : ∀ e s, MIRCtxRefines e (betaReducePass e s).1.1)
    (hCaseMerge : ∀ e, MIRCtxRefines e (caseMergePass e).1)
    (hSimplify : ∀ e, MIRCtxRefines e (Advanced.simplify e))
    (hCse : ∀ e, MIRCtxRefines e (cse [] e).1)
    (hEta : ∀ e, MIRCtxRefines e (etaReduce e).1)
    (hForceDelay : ∀ e, MIRCtxRefines e (forceDelay e).1)
    (hPreLowerInline : ∀ e n, MIRCtxRefines e (preLowerInlineExpr e n))
    (hStructural : ∀ e, MIRCtxRefines e (Advanced.structural e))
    (hFinish : ∀ e options, MIRCtxRefines e (Advanced.finish e options))
    {e : Expr} {optFresh lowerFresh : Nat} {options : Advanced.Options} {t : Term}
    (h : compileOptimized e optFresh lowerFresh options = .ok t) :
    ∃ t₀, lowerTotalExpr [] e = some t₀ ∧ CtxRefines t₀ t :=
  compileOptimized_refines_of_certificates
    ⟨hStatic, hPrepare, hFloat, hBeta, hCaseMerge, hSimplify, hCse, hEta, hForceDelay,
      hPreLowerInline, hStructural⟩ (hFinish · options) h

/-- Without builtin sharing and constant pooling the final allocation stage is
    already certified (`finish_without_sharing_refines`). -/
theorem compileOptimized_refines_of_without_sharing
    (hStatic : ∀ e, MIRCtxRefines e (Advanced.staticArguments e))
    (hPrepare : ∀ e, MIRCtxRefines e (Advanced.prepare e))
    (hFloat : ∀ e, MIRCtxRefines e (floatOut e).1)
    (hBeta : ∀ e s, MIRCtxRefines e (betaReducePass e s).1.1)
    (hCaseMerge : ∀ e, MIRCtxRefines e (caseMergePass e).1)
    (hSimplify : ∀ e, MIRCtxRefines e (Advanced.simplify e))
    (hCse : ∀ e, MIRCtxRefines e (cse [] e).1)
    (hEta : ∀ e, MIRCtxRefines e (etaReduce e).1)
    (hForceDelay : ∀ e, MIRCtxRefines e (forceDelay e).1)
    (hPreLowerInline : ∀ e n, MIRCtxRefines e (preLowerInlineExpr e n))
    (hStructural : ∀ e, MIRCtxRefines e (Advanced.structural e))
    {e : Expr} {optFresh lowerFresh : Nat} {options : Advanced.Options} {t : Term}
    (builtinSharing : options.shareBuiltinStates = false)
    (constantPooling : options.poolConstants = false)
    (h : compileOptimized e optFresh lowerFresh options = .ok t) :
    ∃ t₀, lowerTotalExpr [] e = some t₀ ∧ CtxRefines t₀ t :=
  compileOptimized_refines_of_certificates
    ⟨hStatic, hPrepare, hFloat, hBeta, hCaseMerge, hSimplify, hCse, hEta, hForceDelay,
      hPreLowerInline, hStructural⟩
    (fun e => Moist.Verified.MIR.finish_without_sharing_refines e options builtinSharing
      constantPooling) h

/-! ## Compilation fails only on invalid input -/

theorem compileOptimized_error_of_certificates (C : StageCertificates)
    {options : Advanced.Options}
    (hFinish : ∀ e, MIRCtxRefines e (Advanced.finish e options)) {e : Expr}
    {optFresh lowerFresh : Nat} {msg : String}
    (h : compileOptimized e optFresh lowerFresh options = .error msg) :
    validateCompilationInput [] e = .error msg := by
  unfold compileOptimized at h
  cases hv : validateCompilationInput [] e with
  | error m => simpa [hv, bind, Except.bind] using h
  | ok u =>
    exfalso
    obtain ⟨t₀, ht₀⟩ := validate_ok_lowerTotalExpr (by cases u; exact hv)
    simp only [hv, bind, Except.bind] at h
    have hP := (prepareForLowering_refines C e optFresh lowerFresh []).1
    rw [ht₀] at hP
    obtain ⟨tP, htP⟩ := Option.isSome_iff_exists.mp (hP rfl)
    obtain ⟨term, hl, _⟩ := lowerExpr_complete htP (lowerFresh + 1000)
    simp only [hl] at h
    split at h
    · have hF := (hFinish (liftUPLC term) []).1
      rw [liftUPLC_lowerExpr hl 1] at hF
      obtain ⟨tF, htF⟩ := Option.isSome_iff_exists.mp (hF rfl)
      obtain ⟨t, ht, _⟩ := lowerExpr_complete htF (lowerFresh + 1000)
      rw [ht] at h
      cases h
    · simp [pure, Except.pure] at h

theorem compileOptimized_error_of
    (hStatic : ∀ e, MIRCtxRefines e (Advanced.staticArguments e))
    (hPrepare : ∀ e, MIRCtxRefines e (Advanced.prepare e))
    (hFloat : ∀ e, MIRCtxRefines e (floatOut e).1)
    (hBeta : ∀ e s, MIRCtxRefines e (betaReducePass e s).1.1)
    (hCaseMerge : ∀ e, MIRCtxRefines e (caseMergePass e).1)
    (hSimplify : ∀ e, MIRCtxRefines e (Advanced.simplify e))
    (hCse : ∀ e, MIRCtxRefines e (cse [] e).1)
    (hEta : ∀ e, MIRCtxRefines e (etaReduce e).1)
    (hForceDelay : ∀ e, MIRCtxRefines e (forceDelay e).1)
    (hPreLowerInline : ∀ e n, MIRCtxRefines e (preLowerInlineExpr e n))
    (hStructural : ∀ e, MIRCtxRefines e (Advanced.structural e))
    (hFinish : ∀ e options, MIRCtxRefines e (Advanced.finish e options))
    {e : Expr} {optFresh lowerFresh : Nat} {options : Advanced.Options} {msg : String}
    (h : compileOptimized e optFresh lowerFresh options = .error msg) :
    validateCompilationInput [] e = .error msg :=
  compileOptimized_error_of_certificates
    ⟨hStatic, hPrepare, hFloat, hBeta, hCaseMerge, hSimplify, hCse, hEta, hForceDelay,
      hPreLowerInline, hStructural⟩ (hFinish · options) h

/-! ## Composite stages from their passes

The composite `Advanced` stages are sequences of individually certified
passes; these lemmas discharge the already certified ones. -/

theorem prepare_refines_of
    (hShare : ∀ e, MIRCtxRefines e (Advanced.shareDelayedValues e)) (e : Expr) :
    MIRCtxRefines e (Advanced.prepare e) :=
  mirCtxRefines_trans (hShare e) (Moist.Verified.MIR.eliminateDeadFix_refines _)

theorem simplify_refines_of
    (hFuse : ∀ e, MIRCtxRefines e (Advanced.fuseListDestructors e))
    (hShape : ∀ e, MIRCtxRefines e (Advanced.shapeDCE e))
    (hTags : ∀ e, MIRCtxRefines e (Advanced.caseTagChains e)) (e : Expr) :
    MIRCtxRefines e (Advanced.simplify e) :=
  mirCtxRefines_trans (hFuse e)
    (mirCtxRefines_trans (Moist.Verified.MIR.constantFold_refines _)
      (mirCtxRefines_trans (Moist.Verified.MIR.foldDataConstructors_refines _)
        (mirCtxRefines_trans (hShape _) (hTags _))))

theorem structural_refines_of
    (hChoices : ∀ e, MIRCtxRefines e (Advanced.fuseListChoices e))
    (hProducts : ∀ e, MIRCtxRefines e (Advanced.destructureProducts e))
    (hBranches : ∀ e, MIRCtxRefines e (Advanced.optimizeCheckedBranches e))
    (hRecords : ∀ e, MIRCtxRefines e (Advanced.unpackRecords e)) (e : Expr) :
    MIRCtxRefines e (Advanced.structural e) :=
  mirCtxRefines_trans (hChoices e)
    (mirCtxRefines_trans (hProducts _) (mirCtxRefines_trans (hBranches _) (hRecords _)))

theorem finish_refines_of
    (hLow : ∀ o e, MIRCtxRefines e (Advanced.shareLow o e))
    (hHoist : ∀ k e, MIRCtxRefines e (Advanced.hoistBuiltinStates k e))
    (hPool : ∀ k e, MIRCtxRefines e (Advanced.poolConstants k e))
    (e : Expr) (options : Advanced.Options) :
    MIRCtxRefines e (Advanced.finish e options) := by
  unfold Advanced.finish
  have hPack : MIRCtxRefines e
      (if options.packApplications then Advanced.packApplications 3 e else e) := by
    split
    · exact Moist.Verified.MIR.packApplications_refines 3 e
    · exact mirCtxRefines_refl e
  have hLowered : ∀ p, MIRCtxRefines e p → MIRCtxRefines e
      (if options.shareLow then Advanced.shareLow options.lowSharing p else p) := by
    intro p hp
    split
    · exact mirCtxRefines_trans hp (hLow _ _)
    · exact hp
  have hShared : ∀ p, MIRCtxRefines e p → MIRCtxRefines e
      (if options.shareBuiltinStates then
        Advanced.hoistBuiltinStates (max 1 options.minimumBuiltinUses) p else p) := by
    intro p hp
    split
    · exact mirCtxRefines_trans hp (hHoist _ _)
    · exact hp
  have hPooled : ∀ p, MIRCtxRefines e p → MIRCtxRefines e
      (if options.poolConstants then Advanced.poolConstants options.minimumConstantBytes p
       else p) := by
    intro p hp
    split
    · exact mirCtxRefines_trans hp (hPool _ _)
    · exact hp
  exact hPooled _ (hShared _ (hLowered _ hPack))

end Moist.Verified.Pipeline
