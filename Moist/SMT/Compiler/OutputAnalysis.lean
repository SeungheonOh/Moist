import Moist.SMT.Compiler.Validation
import Moist.SMT.Compiler.ExpressionIdentity

/-!
# Sharing-aware generated-output analysis

This module contains the executable post-generation analysis used by the
production compiler.  It is deliberately separate from both the general input
validators and the soundness proof.  The analysis fuses renderer-safety and
sort checking, then memoizes immutable compound expressions so a shared SMT
expression DAG is not repeatedly interpreted as an exponentially larger tree.

Cache identity has an ordinary structural specification.  The Lean
implementation delegates exact equality to `Compiler.ExpressionIdentity`,
which may use a safe runtime pointer shortcut for shared immutable nodes.
That shortcut is optional for ports: fingerprints only filter cache
candidates, and every candidate must still be checked for exact structural
equality before its analysis can be reused.

`Moist.SMT.Soundness.OutputAnalysis` proves that the exported Boolean is
exactly the conjunction of the transparent validators in
`Moist.SMT.Compiler.Validation`.
-/

namespace Moist.SMT.Compiler.OutputAnalysis

open Moist.SMT.UPLC
open Moist.SMT.Compiler.Validation

/-- The two facts needed for one expression at the generated-output boundary. -/
structure ExpressionOutputAnalysis where
  rendererSafe : Bool
  sort? : Option Moist.SMT.SSort
deriving Repr, BEq

/-- Transparent specification of the fused analysis.  The memoized
implementation invokes it only for leaves. -/
def referenceExpressionOutputAnalysis (declarations : List SymDecl)
    (expression : SExpr) : ExpressionOutputAnalysis :=
  { rendererSafe := expressionRendererSafe expression
  , sort? := expressionSort? declarations expression }

def outputAnalysesRendererSafe : List ExpressionOutputAnalysis → Bool
  | [] => true
  | analysis :: analyses =>
      analysis.rendererSafe && outputAnalysesRendererSafe analyses

def outputAnalysisSorts? :
    List ExpressionOutputAnalysis → Option (List Moist.SMT.SSort)
  | [] => some []
  | analysis :: analyses => do
      let sort ← analysis.sort?
      let sorts ← outputAnalysisSorts? analyses
      pure (sort :: sorts)

/-- Combine already-analyzed application children without revisiting their
expressions.  The internal traversal always supplies exactly one analysis per
argument. -/
def applicationOutputAnalysis (name : String)
    (analyses : List ExpressionOutputAnalysis) : ExpressionOutputAnalysis :=
  let rendererSafe :=
    match analyses with
    | [] => nullaryApplicationHeads.contains name
    | _ :: _ =>
        applicationHeadRendererSafe name &&
          outputAnalysesRendererSafe analyses
  let sort? :=
    match name, analyses with
    | "=", [left, right] => do
        let leftSort ← left.sort?
        let rightSort ← right.sort?
        guard (leftSort == rightSort)
        pure .bool
    | _, _ => do
        let argumentSorts ← outputAnalysisSorts? analyses
        applicationResultSort? name argumentSorts
  { rendererSafe, sort? }

/-- Combine the three already-analyzed children of an `ite`. -/
def iteOutputAnalysis (condition thenBranch elseBranch :
    ExpressionOutputAnalysis) : ExpressionOutputAnalysis :=
  let sort? := do
    guard (condition.sort? == some .bool)
    let thenSort ← thenBranch.sort?
    let elseSort ← elseBranch.sort?
    guard (thenSort == elseSort)
    pure thenSort
  { rendererSafe := condition.rendererSafe &&
      thenBranch.rendererSafe && elseBranch.rendererSafe
  , sort? }

/-- A shallow structural fingerprint for filtering cache candidates.

Common atomic payloads are included because omitting them makes every
comparison or `ite` of the same shape collide.  Complex literal payloads use a
conservative constructor/length fingerprint; collisions remain harmless
because exact structural equality is always checked afterward. -/
def expressionOutputFingerprint : Nat → SExpr → UInt64
  | 0, .sym name => mixHash 0 (hash name)
  | 0, .int value => mixHash 1 (hash value)
  | 0, .bytes value => mixHash 2 (hash value)
  | 0, .dataLit _ => 3
  | 0, .dataListLit values => mixHash 4 (hash values.length)
  | 0, .dataPairListLit values => mixHash 5 (hash values.length)
  | 0, .constListLit values => mixHash 6 (hash values.length)
  | 0, .bool value => mixHash 7 (hash value)
  | 0, .str value => mixHash 8 (hash value)
  | 0, .app name arguments =>
      mixHash 9 (mixHash (hash name) (hash arguments.length))
  | 0, .ite _ _ _ => 10
  | depth + 1, .app name arguments =>
      arguments.foldl
        (fun fingerprint argument =>
          mixHash fingerprint (expressionOutputFingerprint depth argument))
        (mixHash 9 (mixHash (hash name) (hash arguments.length)))
  | depth + 1, .ite condition thenBranch elseBranch =>
      mixHash 10
        (mixHash (expressionOutputFingerprint depth condition)
          (mixHash (expressionOutputFingerprint depth thenBranch)
            (expressionOutputFingerprint depth elseBranch)))
  | _ + 1, expression => expressionOutputFingerprint 0 expression

/-- Boolean facade for the exact, recursively sharing-aware comparator. -/
@[inline] def expressionOutputEq (left right : SExpr) : Bool :=
  match ExpressionIdentity.decEq left right with
  | .isTrue _ => true
  | .isFalse _ => false

structure CachedExpressionOutputAnalysis where
  expression : SExpr
  fingerprint : UInt64
  analysis : ExpressionOutputAnalysis

/-- Bounded recent-node cache.  `size` is operational metadata only; it does
not participate in cache identity or any soundness premise. -/
structure ExpressionOutputCache where
  entries : List CachedExpressionOutputAnalysis
  size : Nat

def ExpressionOutputCache.empty : ExpressionOutputCache := ⟨[], 0⟩

def expressionOutputCacheLimit : Nat := 512

def findCachedExpressionOutputAnalysisWithFingerprint? (expression : SExpr)
    (fingerprint : UInt64) :
    List CachedExpressionOutputAnalysis → Option ExpressionOutputAnalysis
  | [] => none
  | entry :: entries =>
      if entry.fingerprint == fingerprint then
        if expressionOutputEq expression entry.expression then
          some entry.analysis
        else
          findCachedExpressionOutputAnalysisWithFingerprint? expression
            fingerprint entries
      else
        findCachedExpressionOutputAnalysisWithFingerprint? expression
          fingerprint entries

def findCachedExpressionOutputAnalysis? (expression : SExpr)
    (cache : ExpressionOutputCache) : Option ExpressionOutputAnalysis :=
  findCachedExpressionOutputAnalysisWithFingerprint? expression
    (expressionOutputFingerprint 2 expression) cache.entries

/-- Insert into a bounded recency window.  Once full, retain the 511 most
recent prior entries instead of clearing the cache at an arbitrary boundary.
The `take` is bounded by `expressionOutputCacheLimit`; no semantic property
depends on `size` being accurate. -/
def cacheExpressionOutputAnalysis (expression : SExpr)
    (analysis : ExpressionOutputAnalysis) (cache : ExpressionOutputCache) :
    ExpressionOutputCache :=
  let entry :=
    { expression
    , fingerprint := expressionOutputFingerprint 2 expression
    , analysis }
  if cache.size < expressionOutputCacheLimit then
    { entries := entry :: cache.entries, size := cache.size + 1 }
  else
    { entries := entry :: cache.entries.take
        (expressionOutputCacheLimit - 1)
    , size := expressionOutputCacheLimit }

mutual
  /-- Analyze one expression while reusing exact, recently visited compound
  nodes.  Leaves are inexpensive and are not retained. -/
  def expressionOutputAnalysisAux (declarations : List SymDecl)
      (cache : ExpressionOutputCache) (expression : SExpr) :
      ExpressionOutputAnalysis × ExpressionOutputCache :=
    match expression with
    | .app name arguments =>
        match findCachedExpressionOutputAnalysis? expression cache with
        | some analysis => (analysis, cache)
        | none =>
            let (analyses, cache) :=
              expressionOutputAnalysesAux declarations cache arguments
            let analysis := applicationOutputAnalysis name analyses
            (analysis, cacheExpressionOutputAnalysis expression analysis cache)
    | .ite condition thenBranch elseBranch =>
        match findCachedExpressionOutputAnalysis? expression cache with
        | some analysis => (analysis, cache)
        | none =>
            let (conditionAnalysis, cache) :=
              expressionOutputAnalysisAux declarations cache condition
            let (thenAnalysis, cache) :=
              expressionOutputAnalysisAux declarations cache thenBranch
            let (elseAnalysis, cache) :=
              expressionOutputAnalysisAux declarations cache elseBranch
            let analysis := iteOutputAnalysis conditionAnalysis thenAnalysis
              elseAnalysis
            (analysis, cacheExpressionOutputAnalysis expression analysis cache)
    | expression =>
        (referenceExpressionOutputAnalysis declarations expression, cache)

  /-- Analyze a list left-to-right, threading one cache across every child and
  every generated assertion. -/
  def expressionOutputAnalysesAux (declarations : List SymDecl)
      (cache : ExpressionOutputCache) :
      List SExpr → List ExpressionOutputAnalysis × ExpressionOutputCache
    | [] => ([], cache)
    | expression :: expressions =>
        let (analysis, cache) :=
          expressionOutputAnalysisAux declarations cache expression
        let (analyses, cache) :=
          expressionOutputAnalysesAux declarations cache expressions
        (analysis :: analyses, cache)
end

def expressionOutputAnalysis (declarations : List SymDecl)
    (expression : SExpr) : ExpressionOutputAnalysis :=
  (expressionOutputAnalysisAux declarations .empty expression).1

def expressionOutputAnalyses (declarations : List SymDecl)
    (expressions : List SExpr) : List ExpressionOutputAnalysis :=
  (expressionOutputAnalysesAux declarations .empty expressions).1

/-- Fused, sharing-aware Boolean used by the proof-carrying output contract. -/
def generatedAssertionsOutputSafe (declarations : List SymDecl)
    (script : Moist.SMT.Script) : Bool :=
  (expressionOutputAnalyses declarations script.assertions).all fun analysis =>
    analysis.rendererSafe && analysis.sort? == some .bool

end Moist.SMT.Compiler.OutputAnalysis
