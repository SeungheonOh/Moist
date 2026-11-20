import Moist.MIR.Tune
import Moist.Verified.CompilerSoundness

namespace Moist.Verified.Pipeline

open Moist.MIR
open Moist.Plutus.Term (Term)
open Moist.Verified.Contextual (CtxRefines)

/-- Selecting a candidate by score retains the ordinary compiler's contextual refinement. -/
theorem compiledProfile_refines [Moist.CEK.SemVariant] {expression : Expr}
    {optFresh lowerFresh : Nat} (candidate : CompiledProfile expression optFresh lowerFresh) :
    ∃ original, lowerTotalExpr [] expression = some original ∧ CtxRefines original candidate.term :=
  compileOptimized_refines candidate.compiled

private theorem mapM_projection {α β : Type} (build : α → Except String β) (project : β → α)
    (projects : ∀ source candidate, build source = .ok candidate → project candidate = source)
    {inputs : List α} {outputs : List β} (built : inputs.mapM build = .ok outputs) :
    outputs.map project = inputs := by
  induction inputs generalizing outputs with
  | nil =>
    simp [pure, Except.pure] at built
    subst outputs
    rfl
  | cons input inputs ih =>
    rw [List.mapM_cons] at built
    cases head : build input with
    | error _ => simp [head, bind, Except.bind] at built
    | ok output =>
      cases tail : inputs.mapM build with
      | error _ => simp [head, tail, bind, Except.bind] at built
      | ok outputs' =>
        simp [head, tail, bind, Except.bind, pure, Except.pure] at built
        subst outputs
        simp [projects input output head, ih tail]

/-- Every compiled variant keeps the requested profile that produced it. -/
theorem compileVariants_profiles {expression : Expr} {profiles : List OptimizationProfile}
    {optFresh lowerFresh : Nat} {candidates : List (CompiledProfile expression optFresh lowerFresh)}
    (built : compileVariants expression profiles optFresh lowerFresh = .ok candidates) :
    candidates.map CompiledProfile.profile = profiles := by
  unfold compileVariants at built
  split at built
  · contradiction
  · apply mapM_projection _ CompiledProfile.profile _ built
    intro source candidate h
    split at h
    · contradiction
    · cases h
      rfl

/-- Profile expansion changes only the name and recursion peel depth. -/
theorem peelProfiles_effective {search : PeelSearch} {profiles : List OptimizationProfile}
    {effective : OptimizationProfile} (member : effective ∈ peelProfiles search profiles) :
    ∃ profile ∈ profiles,
      let depth := effective.options.recursionPeelDepth
      depth ≤ search.maxDepth ∧
        effective.options = { profile.options with recursionPeelDepth := depth } ∧
        effective.name = s!"{profile.name}-peel-{depth}" := by
  simp only [peelProfiles, List.mem_flatMap, List.mem_map, List.mem_range] at member
  obtain ⟨depth, depthBound, profile, requested, rfl⟩ := member
  exact ⟨profile, requested, Nat.lt_succ_iff.mp depthBound, rfl, rfl⟩

/-- Every bounded-search candidate respects the requested depth and absolute Flat byte limits. -/
theorem tuningCandidates_respectsPeelSearch {expression : Expr} {profiles : List OptimizationProfile}
    {optFresh lowerFresh : Nat} {search : PeelSearch}
    {candidates : List (CompiledProfile expression optFresh lowerFresh)}
    (built : tuningCandidates expression profiles optFresh lowerFresh (some search) = .ok candidates)
    {candidate : CompiledProfile expression optFresh lowerFresh} (member : candidate ∈ candidates) :
    candidate.profile ∈ peelProfiles search profiles ∧
      candidate.profile.options.recursionPeelDepth ≤ search.maxDepth ∧
      flatProgramBytes candidate.term ≤ search.maxScriptBytes := by
  unfold tuningCandidates at built
  cases compiled : compileVariants expression (peelProfiles search profiles) optFresh lowerFresh with
  | error message => simp [compiled, bind, Except.bind] at built
  | ok variants =>
    simp only [compiled, bind, Except.bind] at built
    split at built
    · contradiction
    · simp [pure, Except.pure] at built
      subst candidates
      have ⟨occurs, fits⟩ := List.mem_filter.mp member
      have profileOccurs : candidate.profile ∈ peelProfiles search profiles := by
        rw [← compileVariants_profiles compiled]
        exact List.mem_map.mpr ⟨candidate, occurs, rfl⟩
      obtain ⟨_, _, depthBound, _, _⟩ := peelProfiles_effective profileOccurs
      exact ⟨profileOccurs, depthBound, of_decide_eq_true fits⟩

private theorem updateBest_member {α score : Type} [Ord score] (previous : Option (α × score))
    (entry : α × Option score) {candidate : α} {cost : score}
    (chosen : selectBest.updateBest previous entry = some (candidate, cost)) :
    (candidate, some cost) = entry ∨ previous = some (candidate, cost) := by
  obtain ⟨current, price⟩ := entry
  cases price with
  | none => exact Or.inr chosen
  | some price =>
    cases previous with
    | none =>
      change some (current, price) = some (candidate, cost) at chosen
      cases chosen
      exact Or.inl rfl
    | some incumbent =>
      obtain ⟨incumbent, incumbentPrice⟩ := incumbent
      change (if compare price incumbentPrice == .lt then some (current, price)
        else some (incumbent, incumbentPrice)) = some (candidate, cost) at chosen
      split at chosen
      · cases chosen
        exact Or.inl rfl
      · exact Or.inr chosen

private theorem selectFold_member {α score : Type} [Ord score] (scored : List (α × Option score))
    (previous : Option (α × score)) {candidate : α} {cost : score}
    (chosen : scored.foldl selectBest.updateBest previous = some (candidate, cost)) :
    (candidate, some cost) ∈ scored ∨ previous = some (candidate, cost) := by
  induction scored generalizing previous with
  | nil => exact Or.inr chosen
  | cons entry rest ih =>
    rcases ih (selectBest.updateBest previous entry) chosen with occurs | updated
    · exact Or.inl (List.mem_cons_of_mem _ occurs)
    · rcases updateBest_member previous entry updated with selected | kept
      · exact Or.inl (List.mem_cons.mpr (Or.inl selected))
      · exact Or.inr kept

/-- The selector returns an input candidate whose measurement succeeded. -/
theorem selectBest_wasScored {α score : Type} [Ord score] {scored : List (α × Option score)}
    {candidate : α} (chosen : selectBest scored = some candidate) :
    ∃ cost, (candidate, some cost) ∈ scored := by
  unfold selectBest at chosen
  cases folded : scored.foldl selectBest.updateBest none with
  | none => simp [folded] at chosen
  | some result =>
    obtain ⟨winner, cost⟩ := result
    simp [folded] at chosen
    subst candidate
    rcases selectFold_member scored none folded with occurs | impossible
    · exact ⟨cost, occurs⟩
    · contradiction

/-- The pure tuner returns a scored member of the filtered candidate list. -/
theorem compileTuned_wasScored {score : Type} [Ord score] {expression : Expr}
    {measure : Term → Option score} {profiles : List OptimizationProfile} {optFresh lowerFresh : Nat}
    {peeling : Option PeelSearch} {candidate : CompiledProfile expression optFresh lowerFresh}
    (chosen : compileTuned expression measure profiles optFresh lowerFresh peeling = .ok candidate) :
    ∃ candidates cost,
      tuningCandidates expression profiles optFresh lowerFresh peeling = .ok candidates ∧
      candidate ∈ candidates ∧ measure candidate.term = some cost := by
  unfold compileTuned compileTunedM at chosen
  cases generated : tuningCandidates expression profiles optFresh lowerFresh peeling with
  | error message => simp [generated, pure, Id.run] at chosen
  | ok candidates =>
    have result : selectBest (candidates.map fun profile => (profile, measure profile.term)) =
        some candidate := by
      simp only [generated] at chosen
      change (match selectBest ((candidates.mapM (m := Id) fun profile => (profile, measure profile.term)).run) with
        | none => Except.error _
        | some winner => Except.ok winner) = Except.ok candidate at chosen
      rw [List.idRun_mapM] at chosen
      split at chosen
      · contradiction
      · cases chosen
        assumption
    obtain ⟨cost, scored⟩ := selectBest_wasScored result
    obtain ⟨profile, member, same⟩ := List.mem_map.mp scored
    obtain ⟨rfl, costFound⟩ := Prod.mk.inj same
    exact ⟨candidates, cost, rfl, member, costFound⟩

/-- A pure tuner success under bounded peeling respects both limits and identifies its effective profile. -/
theorem compileTuned_respectsPeelSearch {score : Type} [Ord score] {expression : Expr}
    {measure : Term → Option score} {profiles : List OptimizationProfile} {optFresh lowerFresh : Nat}
    {search : PeelSearch} {candidate : CompiledProfile expression optFresh lowerFresh}
    (chosen : compileTuned expression measure profiles optFresh lowerFresh (some search) = .ok candidate) :
    candidate.profile ∈ peelProfiles search profiles ∧
      candidate.profile.options.recursionPeelDepth ≤ search.maxDepth ∧
      flatProgramBytes candidate.term ≤ search.maxScriptBytes := by
  obtain ⟨_, _, generated, member, _⟩ := compileTuned_wasScored chosen
  exact tuningCandidates_respectsPeelSearch generated member

/-- A successful pure tuner invocation emits a certified contextual refinement. -/
theorem compileTuned_refines [Moist.CEK.SemVariant] {score : Type} [Ord score] {expression : Expr}
    {measure : Term → Option score} {profiles : List OptimizationProfile} {optFresh lowerFresh : Nat}
    {peeling : Option PeelSearch} {candidate : CompiledProfile expression optFresh lowerFresh}
    (_chosen : compileTuned expression measure profiles optFresh lowerFresh peeling = .ok candidate) :
    ∃ original, lowerTotalExpr [] expression = some original ∧ CtxRefines original candidate.term :=
  compiledProfile_refines candidate

end Moist.Verified.Pipeline
