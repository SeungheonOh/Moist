import Moist.SMT.Soundness.SolverInput
import Moist.SMT.Compiler.OutputAnalysis

/-!
# Sharing-aware output-analysis correctness

The symbolic evaluator constructs substantially larger expressions than its
inputs.  The executable fused analysis and its cache live in
`Moist.SMT.Compiler.OutputAnalysis`; this module proves that analysis exactly
equals the transparent renderer-safety and sort validators.

The contract is deliberately about the typed `Script` AST before either the
transparent renderer or the pointer-based DAG renderer runs.  A successful
check certifies that the command stream contains only the fixed raw prelude,
checked declarations, assertions, the fixed solver tactic, and the final
model request.  It also certifies that every logical assertion belongs to the
reviewed renderer grammar and has SMT sort `Bool` under exactly the query
declarations.

This is not a replacement for symbolic-execution soundness.  Datatype
selectors and several UPLC operations are intentionally partial in the Lean
observation semantics and total-but-unspecified outside their domains in Z3.
Their path-sensitive guards are covered by the simulation proofs; a
context-free syntax checker cannot establish that stronger property.
-/

namespace Moist.SMT.UPLC.Soundness

open Moist.SMT.Compiler.OutputAnalysis

namespace OutputAnalysis

private def cacheValid (declarations : List SymDecl)
    (cache : ExpressionOutputCache) : Prop :=
  ∀ entry, entry ∈ cache.entries →
    entry.analysis =
      referenceExpressionOutputAnalysis declarations entry.expression

private theorem outputAnalysesRendererSafe_map_reference
    (declarations : List SymDecl) (expressions : List SExpr) :
    outputAnalysesRendererSafe
        (expressions.map (referenceExpressionOutputAnalysis declarations)) =
      expressionsRendererSafe expressions := by
  induction expressions with
  | nil => simp [outputAnalysesRendererSafe, expressionsRendererSafe]
  | cons expression expressions ih =>
      simp [outputAnalysesRendererSafe, referenceExpressionOutputAnalysis,
        expressionsRendererSafe, ih]

private theorem outputAnalysisSorts_map_reference
    (declarations : List SymDecl) (expressions : List SExpr) :
    outputAnalysisSorts?
        (expressions.map (referenceExpressionOutputAnalysis declarations)) =
      expressionSorts? declarations expressions := by
  induction expressions with
  | nil => simp [outputAnalysisSorts?, expressionSorts?]
  | cons expression expressions ih =>
      simp [outputAnalysisSorts?, referenceExpressionOutputAnalysis,
        expressionSorts?, ih]

private theorem applicationOutputAnalysis_map_reference
    (declarations : List SymDecl) (name : String)
    (arguments : List SExpr) :
    applicationOutputAnalysis name
        (arguments.map (referenceExpressionOutputAnalysis declarations)) =
      referenceExpressionOutputAnalysis declarations (.app name arguments) := by
  cases arguments with
  | nil =>
      simp [applicationOutputAnalysis, referenceExpressionOutputAnalysis,
        expressionRendererSafe, expressionSort?, expressionSorts?,
        outputAnalysisSorts?]
  | cons first rest =>
      cases rest with
      | nil =>
          simp [applicationOutputAnalysis, referenceExpressionOutputAnalysis,
            expressionRendererSafe, expressionSort?, expressionSorts?,
            outputAnalysesRendererSafe, expressionsRendererSafe,
            outputAnalysisSorts?]
      | cons second rest =>
          cases rest with
          | nil =>
              by_cases hname : name = "="
              · subst name
                simp [applicationOutputAnalysis,
                  referenceExpressionOutputAnalysis,
                  expressionRendererSafe, expressionSort?,
                  outputAnalysesRendererSafe, expressionsRendererSafe]
              · simp [applicationOutputAnalysis,
                  referenceExpressionOutputAnalysis,
                  expressionRendererSafe, expressionSort?, expressionSorts?,
                  outputAnalysesRendererSafe, expressionsRendererSafe,
                  outputAnalysisSorts?, hname]
          | cons third rest =>
              simp [applicationOutputAnalysis,
                referenceExpressionOutputAnalysis,
                expressionRendererSafe, expressionSort?, expressionSorts?,
                outputAnalysesRendererSafe, expressionsRendererSafe,
                outputAnalysisSorts?,
                outputAnalysesRendererSafe_map_reference,
                outputAnalysisSorts_map_reference]

private theorem iteOutputAnalysis_reference (declarations : List SymDecl)
    (condition thenBranch elseBranch : SExpr) :
    iteOutputAnalysis
        (referenceExpressionOutputAnalysis declarations condition)
        (referenceExpressionOutputAnalysis declarations thenBranch)
        (referenceExpressionOutputAnalysis declarations elseBranch) =
      referenceExpressionOutputAnalysis declarations
        (Moist.SMT.Expr.ite condition thenBranch elseBranch) := by
  simp [iteOutputAnalysis, referenceExpressionOutputAnalysis,
    expressionRendererSafe, expressionSort?]

private theorem expressionOutputEq_eq_true {left right : SExpr}
    (equal : expressionOutputEq left right = true) : left = right := by
  cases decision : Moist.SMT.Compiler.ExpressionIdentity.decEq left right with
  | isTrue proposition => exact proposition
  | isFalse notProposition =>
      simp [expressionOutputEq, decision] at equal

private theorem findCachedExpressionOutputAnalysis?_sound
    (declarations : List SymDecl) (expression : SExpr)
    (cache : ExpressionOutputCache) (analysis : ExpressionOutputAnalysis)
    (hvalid : cacheValid declarations cache)
    (hfind : findCachedExpressionOutputAnalysis? expression cache =
      some analysis) :
    analysis = referenceExpressionOutputAnalysis declarations expression := by
  unfold findCachedExpressionOutputAnalysis? at hfind
  generalize expressionOutputFingerprint 2 expression = fingerprint at hfind
  have findSound : ∀ entries : List CachedExpressionOutputAnalysis,
      (∀ entry, entry ∈ entries →
        entry.analysis =
          referenceExpressionOutputAnalysis declarations entry.expression) →
      findCachedExpressionOutputAnalysisWithFingerprint? expression
          fingerprint entries = some analysis →
        analysis =
          referenceExpressionOutputAnalysis declarations expression := by
    intro entries hentries
    induction entries with
    | nil => simp [findCachedExpressionOutputAnalysisWithFingerprint?]
    | cons entry entries ih =>
        simp only [findCachedExpressionOutputAnalysisWithFingerprint?]
        split
        · split
          · intro hresult
            cases hresult
            have hequal : expression = entry.expression :=
              expressionOutputEq_eq_true (by assumption)
            rw [hequal]
            exact hentries entry (by simp)
          · apply ih
            intro cached hmember
            exact hentries cached (by simp [hmember])
        · apply ih
          intro cached hmember
          exact hentries cached (by simp [hmember])
  exact findSound cache.entries hvalid hfind

private theorem cacheExpressionOutputAnalysis_valid
    (declarations : List SymDecl) (expression : SExpr)
    (analysis : ExpressionOutputAnalysis) (cache : ExpressionOutputCache)
    (hanalysis : analysis =
      referenceExpressionOutputAnalysis declarations expression)
    (hvalid : cacheValid declarations cache) :
    cacheValid declarations
      (cacheExpressionOutputAnalysis expression analysis cache) := by
  intro entry hmember
  unfold cacheExpressionOutputAnalysis at hmember
  dsimp only at hmember
  by_cases hsize : cache.size < expressionOutputCacheLimit
  · simp only [hsize, ↓reduceIte, List.mem_cons] at hmember
    rcases hmember with hentry | hentry
    · cases hentry
      exact hanalysis
    · exact hvalid entry hentry
  · simp only [hsize, ↓reduceIte, List.mem_cons] at hmember
    rcases hmember with hentry | hentry
    · cases hentry
      exact hanalysis
    · exact hvalid entry (List.mem_of_mem_take hentry)

mutual
  private theorem expressionOutputAnalysisAux_sound
      (declarations : List SymDecl) (cache : ExpressionOutputCache)
      (expression : SExpr) (hvalid : cacheValid declarations cache) :
      let result := expressionOutputAnalysisAux declarations cache expression
      result.1 = referenceExpressionOutputAnalysis declarations expression ∧
        cacheValid declarations result.2 := by
    cases expression with
    | app name arguments =>
        cases hfind : findCachedExpressionOutputAnalysis?
            (.app name arguments) cache with
        | some analysis =>
            have hsound := findCachedExpressionOutputAnalysis?_sound
              declarations (.app name arguments) cache analysis hvalid hfind
            simp only [expressionOutputAnalysisAux]
            rw [hfind]
            exact And.intro hsound hvalid
        | none =>
            cases hchildrenResult :
                expressionOutputAnalysesAux declarations cache arguments with
            | mk analyses childCache =>
                have hchildren :=
                  expressionOutputAnalysesAux_sound declarations cache
                    arguments hvalid
                rw [hchildrenResult] at hchildren
                simp only at hchildren
                rcases hchildren with ⟨hanalyses, hchildCache⟩
                have hcombined :
                    applicationOutputAnalysis name analyses =
                      referenceExpressionOutputAnalysis declarations
                        (.app name arguments) := by
                  rw [hanalyses]
                  exact applicationOutputAnalysis_map_reference declarations
                    name arguments
                have hcache :=
                  cacheExpressionOutputAnalysis_valid declarations
                    (.app name arguments)
                    (applicationOutputAnalysis name analyses) childCache
                    hcombined hchildCache
                simpa only [expressionOutputAnalysisAux, hfind,
                  hchildrenResult] using And.intro hcombined hcache
    | ite condition thenBranch elseBranch =>
        cases hfind : findCachedExpressionOutputAnalysis?
            (Moist.SMT.Expr.ite condition thenBranch elseBranch) cache with
        | some analysis =>
            have hsound := findCachedExpressionOutputAnalysis?_sound
              declarations (Moist.SMT.Expr.ite condition thenBranch elseBranch)
                cache
                analysis hvalid hfind
            simp only [expressionOutputAnalysisAux]
            rw [hfind]
            exact And.intro hsound hvalid
        | none =>
            cases hconditionResult :
                expressionOutputAnalysisAux declarations cache condition with
            | mk conditionAnalysis conditionCache =>
                have hcondition := expressionOutputAnalysisAux_sound
                  declarations cache condition hvalid
                rw [hconditionResult] at hcondition
                simp only at hcondition
                rcases hcondition with
                  ⟨hconditionAnalysis, hconditionCache⟩
                cases hthenResult : expressionOutputAnalysisAux declarations
                    conditionCache thenBranch with
                | mk thenAnalysis thenCache =>
                    have hthen := expressionOutputAnalysisAux_sound declarations
                      conditionCache thenBranch hconditionCache
                    rw [hthenResult] at hthen
                    simp only at hthen
                    rcases hthen with ⟨hthenAnalysis, hthenCache⟩
                    cases helseResult : expressionOutputAnalysisAux declarations
                        thenCache elseBranch with
                    | mk elseAnalysis elseCache =>
                        have helse := expressionOutputAnalysisAux_sound
                          declarations thenCache elseBranch hthenCache
                        rw [helseResult] at helse
                        simp only at helse
                        rcases helse with ⟨helseAnalysis, helseCache⟩
                        have hcombined :
                            iteOutputAnalysis conditionAnalysis thenAnalysis
                                elseAnalysis =
                              referenceExpressionOutputAnalysis declarations
                                (Moist.SMT.Expr.ite condition thenBranch
                                  elseBranch) := by
                          rw [hconditionAnalysis, hthenAnalysis, helseAnalysis]
                          exact iteOutputAnalysis_reference declarations
                            condition thenBranch elseBranch
                        have hcache :=
                          cacheExpressionOutputAnalysis_valid declarations
                            (Moist.SMT.Expr.ite condition thenBranch elseBranch)
                            (iteOutputAnalysis conditionAnalysis thenAnalysis
                              elseAnalysis) elseCache hcombined helseCache
                        simp only [expressionOutputAnalysisAux]
                        rw [hfind, hconditionResult, hthenResult, helseResult]
                        exact And.intro hcombined hcache
    | sym name => exact ⟨rfl, hvalid⟩
    | int value => exact ⟨rfl, hvalid⟩
    | bytes value => exact ⟨rfl, hvalid⟩
    | dataLit value => exact ⟨rfl, hvalid⟩
    | dataListLit value => exact ⟨rfl, hvalid⟩
    | dataPairListLit value => exact ⟨rfl, hvalid⟩
    | constListLit value => exact ⟨rfl, hvalid⟩
    | bool value => exact ⟨rfl, hvalid⟩
    | str value => exact ⟨rfl, hvalid⟩

  private theorem expressionOutputAnalysesAux_sound
      (declarations : List SymDecl) (cache : ExpressionOutputCache)
      (expressions : List SExpr) (hvalid : cacheValid declarations cache) :
      let result := expressionOutputAnalysesAux declarations cache expressions
      result.1 =
          expressions.map (referenceExpressionOutputAnalysis declarations) ∧
        cacheValid declarations result.2 := by
    cases expressions with
    | nil => exact ⟨rfl, hvalid⟩
    | cons expression expressions =>
        cases hheadResult :
            expressionOutputAnalysisAux declarations cache expression with
        | mk analysis headCache =>
            have hhead := expressionOutputAnalysisAux_sound declarations cache
              expression hvalid
            rw [hheadResult] at hhead
            simp only at hhead
            rcases hhead with ⟨hanalysis, hheadCache⟩
            cases htailResult : expressionOutputAnalysesAux declarations
                headCache expressions with
            | mk analyses tailCache =>
                have htail := expressionOutputAnalysesAux_sound declarations
                  headCache expressions hheadCache
                rw [htailResult] at htail
                simp only at htail
                rcases htail with ⟨hanalyses, htailCache⟩
                have hanalysisList :
                    analysis :: analyses =
                      (expression :: expressions).map
                        (referenceExpressionOutputAnalysis declarations) := by
                  simp only [List.map_cons, List.cons.injEq]
                  exact ⟨hanalysis, hanalyses⟩
                simpa only [expressionOutputAnalysesAux, hheadResult,
                  htailResult] using And.intro hanalysisList htailCache
end

private theorem expressionOutputAnalyses_eq_reference
    (declarations : List SymDecl) (expressions : List SExpr) :
    expressionOutputAnalyses declarations expressions =
      expressions.map (referenceExpressionOutputAnalysis declarations) := by
  exact (expressionOutputAnalysesAux_sound declarations .empty expressions
    (by simp [ExpressionOutputCache.empty, cacheValid])).1

private theorem referenceAnalyses_all (declarations : List SymDecl) :
    ∀ expressions : List SExpr,
      (expressions.map
        (referenceExpressionOutputAnalysis declarations)).all
          (fun analysis =>
            analysis.rendererSafe && analysis.sort? == some .bool) =
        (expressionsRendererSafe expressions &&
          expressions.all (fun expression =>
            expressionHasSort declarations expression .bool))
  | [] => by simp [expressionsRendererSafe]
  | expression :: expressions => by
      simp only [List.map_cons, List.all_cons,
        referenceExpressionOutputAnalysis, expressionHasSort,
        expressionsRendererSafe]
      rw [referenceAnalyses_all declarations expressions]
      simp only [expressionHasSort]
      generalize expressionRendererSafe expression = renderer
      generalize
        (expressionSort? declarations expression == some .bool) = sort
      generalize expressionsRendererSafe expressions = renderers
      generalize expressions.all
        (fun expression =>
          expressionSort? declarations expression == some .bool) =
          sorts
      cases renderer <;> cases sort <;> cases renderers <;> cases sorts <;> rfl

/-- The sharing-aware executable check is exactly the original pair of
transparent structural validators. -/
theorem generatedAssertionsOutputSafe_eq (declarations : List SymDecl)
    (script : Moist.SMT.Script) :
    generatedAssertionsOutputSafe declarations script =
      (generatedAssertionsRendererSafe script &&
        generatedAssertionsSortSafe declarations script) := by
  simp only [generatedAssertionsOutputSafe,
    expressionOutputAnalyses_eq_reference,
    referenceAnalyses_all, generatedAssertionsRendererSafe,
    generatedAssertionsSortSafe]

end OutputAnalysis

end Moist.SMT.UPLC.Soundness
