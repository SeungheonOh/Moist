import Moist.MIR.Compile
import Moist.Plutus.Encode

namespace Moist.MIR

open Moist.Plutus.Term (Term)

structure OptimizationProfile where
  name : String
  options : Advanced.Options

/-- Search all depths from zero through `maxDepth`, subject to an inclusive Flat size limit. -/
structure PeelSearch where
  maxDepth : Nat
  maxScriptBytes : Nat

/-- Keep allocation choices fixed. Try shallower depths first so exact score ties favor less peeling. -/
def peelProfiles (search : PeelSearch) (profiles : List OptimizationProfile) : List OptimizationProfile :=
  (List.range (search.maxDepth + 1)).flatMap fun depth =>
    profiles.map fun profile => {
      name := s!"{profile.name}-peel-{depth}"
      options := { profile.options with recursionPeelDepth := depth } }

/-- Raw Flat bytes, including the UPLC 1.1.0 version header and Flat padding. -/
def flatProgramBytes (term : Term) : Nat :=
  (Moist.Plutus.Encode.encode_program (.Program (.Version 1 1 0) term)).toByteList.length

def fitsPeelSize (search : PeelSearch) (term : Term) : Bool :=
  decide (flatProgramBytes term ≤ search.maxScriptBytes)

/-- Default tuning varies peel depth over the ordinary compiler options. -/
def defaultOptimizationProfile : OptimizationProfile := ⟨"default", {}⟩

/-- An output from the normal compiler for the given allocation profile. -/
structure CompiledProfile (expression : Expr) (optFresh lowerFresh : Nat) where
  profile : OptimizationProfile
  term : Term
  compiled : compileOptimized expression optFresh lowerFresh profile.options = .ok term

private def noAllocation : Advanced.Options := { packApplications := false, shareLow := false }

private theorem compileFromBase {expression : Expr} {optFresh lowerFresh : Nat}
    {base term : Term} {options : Advanced.Options}
    (original : compileOptimized expression optFresh lowerFresh noAllocation = .ok base)
    (finished : finishCompilation base (lowerFresh + 1000) options = .ok term) :
    compileOptimized expression optFresh lowerFresh options = .ok term := by
  unfold compileOptimized at original ⊢
  cases valid : validateCompilationInput [] expression with
  | error _ => simp [valid, bind, Except.bind] at original
  | ok _ =>
    simp only [valid, bind, Except.bind] at original ⊢
    cases lowered : lowerExpr (prepareForLowering expression optFresh lowerFresh)
        (lowerFresh + 1000) with
    | error _ => simp [lowered] at original
    | ok loweredTerm =>
      have same : loweredTerm = base := by
        simpa [lowered, finishCompilation, finishAllocation, noAllocation,
          bind, Except.bind, pure, Except.pure] using original
      simpa [lowered, same] using finished

/-- Prepare and lower once, then compile each requested allocation profile. -/
def compileVariants (expression : Expr)
    (profiles : List OptimizationProfile := [defaultOptimizationProfile])
    (optFresh : Nat := 1000) (lowerFresh : Nat := 5000) :
    Except String (List (CompiledProfile expression optFresh lowerFresh)) :=
  match original : compileOptimized expression optFresh lowerFresh noAllocation with
  | .error message => .error message
  | .ok base => profiles.mapM fun profile =>
    match finished : finishCompilation base (lowerFresh + 1000) profile.options with
    | .error message => .error message
    | .ok term => .ok ⟨profile, term, compileFromBase original finished⟩

/-- Build candidates through the normal compiler and apply the size limit before scoring. -/
def tuningCandidates (expression : Expr) (profiles : List OptimizationProfile)
    (optFresh lowerFresh : Nat) (peeling : Option PeelSearch) :
    Except String (List (CompiledProfile expression optFresh lowerFresh)) := do
  match peeling with
  | none => compileVariants expression profiles optFresh lowerFresh
  | some search =>
    let compiled ← compileVariants expression (peelProfiles search profiles) optFresh lowerFresh
    let eligible := compiled.filter fun candidate => fitsPeelSize search candidate.term
    if eligible.isEmpty then
      throw s!"no optimization profile fits the {search.maxScriptBytes}-byte Flat limit"
    else pure eligible

/-- Keep the first entry with the lowest available score. -/
def selectBest [Ord score] (scored : List (α × Option score)) : Option α :=
  (scored.foldl updateBest none).map Prod.fst
where
  updateBest (best : Option (α × score)) (entry : α × Option score) : Option (α × score) :=
    match entry.2 with
    | none => best
    | some cost =>
      match best with
      | none => some (entry.1, cost)
      | some (_, bestCost) =>
        if compare cost bestCost == .lt then some (entry.1, cost) else best

/-- Choose the lowest measured score using a scorer that can run an external evaluator.
    `none` excludes a candidate. When enabled, peeling varies only the depth of
    each requested profile. Every candidate is a certified compiler output. -/
def compileTunedM [Monad m] [Ord score] (expression : Expr) (measure : Term → m (Option score))
    (profiles : List OptimizationProfile := [defaultOptimizationProfile]) (optFresh : Nat := 1000)
    (lowerFresh : Nat := 5000) (peeling : Option PeelSearch := none) :
    m (Except String (CompiledProfile expression optFresh lowerFresh)) := do
  match tuningCandidates expression profiles optFresh lowerFresh peeling with
  | .error message => pure (.error message)
  | .ok candidates =>
    let scored ← candidates.mapM fun candidate => do
      let score ← measure candidate.term
      pure (candidate, score)
    match selectBest scored with
    | none => pure (.error "no optimization profile produced a score")
    | some candidate => pure (.ok candidate)

/-- Pure scoring uses the same bounded search as external-evaluator scoring. -/
def compileTuned [Ord score] (expression : Expr) (measure : Term → Option score)
    (profiles : List OptimizationProfile := [defaultOptimizationProfile]) (optFresh : Nat := 1000)
    (lowerFresh : Nat := 5000) (peeling : Option PeelSearch := none) :
    Except String (CompiledProfile expression optFresh lowerFresh) :=
  Id.run (compileTunedM expression measure profiles optFresh lowerFresh peeling)

end Moist.MIR
