import Moist.MIR.Analysis
import Moist.MIR.Canonicalize

namespace Moist.MIR.WellScoped

open Moist.MIR (Expr VarId VarSet freeVars wellScoped wellScopedAux
  wellScopedListAux wellScopedLetAux canonicalize canonicalizeAux maxUidExpr)

private theorem isSome_iff {α} {x : Option α} : x.isSome = true ↔ ∃ a, x = some a := by
  cases x <;> simp [Option.isSome]

private theorem hcheck_extract {seen fv : VarSet} {b : VarId} {s : VarSet} {body : Expr}
    (h : (if (seen.contains b || fv.contains b) = true then none
          else wellScopedAux (seen.insert b) fv body) = some s) :
    (seen.contains b || fv.contains b) = false ∧
    wellScopedAux (seen.insert b) fv body = some s := by
  cases hc : (seen.contains b || fv.contains b) <;> simp [hc] at h ⊢; exact h

private theorem barrier_insert (seen₁ seen₂ fv₁ fv₂ : VarSet) (b : VarId)
    (hbar : ∀ v, seen₂.contains v = true ∨ fv₂.contains v = true →
                 seen₁.contains v = true ∨ fv₁.contains v = true) :
    ∀ v, (seen₂.insert b).contains v = true ∨ fv₂.contains v = true →
         (seen₁.insert b).contains v = true ∨ fv₁.contains v = true := by
  intro v hv; rcases hv with hv | hv
  · rw [VarSet.contains_insert_elim] at hv; rcases hv with hv | hv
    · rcases hbar v (Or.inl hv) with h | h
      · exact Or.inl (VarSet.contains_insert_of_contains _ _ _ h)
      · exact Or.inr h
    · exact Or.inl (VarSet.contains_insert_elim .. |>.mpr (Or.inr hv))
  · rcases hbar v (Or.inr hv) with h | h
    · exact Or.inl (VarSet.contains_insert_of_contains _ _ _ h)
    · exact Or.inr h

private theorem check_false_of_barrier {seen₁ seen₂ fv₁ fv₂ : VarSet} {b : VarId}
    (hbar : ∀ v, seen₂.contains v = true ∨ fv₂.contains v = true →
                 seen₁.contains v = true ∨ fv₁.contains v = true)
    (hcheck : (seen₁.contains b || fv₁.contains b) = false) :
    (seen₂.contains b || fv₂.contains b) = false := by
  cases hs : seen₂.contains b <;> cases hf : fv₂.contains b <;> simp
  · rcases hbar b (Or.inr hf) with h | h <;> simp only [Bool.or_eq_false_iff] at hcheck <;>
      simp [hcheck.1, hcheck.2] at h
  · rcases hbar b (Or.inl hs) with h | h <;> simp only [Bool.or_eq_false_iff] at hcheck <;>
      simp [hcheck.1, hcheck.2] at h
  · rcases hbar b (Or.inl hs) with h | h <;> simp only [Bool.or_eq_false_iff] at hcheck <;>
      simp [hcheck.1, hcheck.2] at h

private theorem sizeOf_rhs_lt (b : VarId × Expr × Bool) (rest : List (VarId × Expr × Bool))
    (body : Expr) : sizeOf b.2.1 < sizeOf (b :: rest) + sizeOf body := by
  have : sizeOf b.2.1 < sizeOf b := by
    cases b with | mk a p => cases p with | mk e c => simp_wf; omega
  have : sizeOf b < sizeOf (b :: rest) := by simp_wf; omega
  omega

/-! ## Anti-monotonicity with full barrier tracking -/

mutual
private theorem wellScopedAux_weaken (seen₁ seen₂ fv₁ fv₂ : VarSet) (e : Expr)
    (hbar : ∀ v, seen₂.contains v = true ∨ fv₂.contains v = true →
                 seen₁.contains v = true ∨ fv₁.contains v = true)
    (s₁ : VarSet) (h : wellScopedAux seen₁ fv₁ e = some s₁) :
    ∃ s₂, wellScopedAux seen₂ fv₂ e = some s₂ ∧
           (∀ v, s₂.contains v = true ∨ fv₂.contains v = true →
                 s₁.contains v = true ∨ fv₁.contains v = true) := by
  cases e with
  | Var _ | Lit _ | Builtin _ | Error =>
    unfold wellScopedAux at h ⊢; injection h with h; subst h; exact ⟨seen₂, rfl, hbar⟩
  | Force inner | Delay inner =>
    unfold wellScopedAux at h ⊢
    exact wellScopedAux_weaken seen₁ seen₂ fv₁ fv₂ inner hbar s₁ h
  | Lam x body =>
    unfold wellScopedAux at h ⊢; have ⟨hc₁, h⟩ := hcheck_extract h
    have hc₂ := check_false_of_barrier hbar hc₁
    simp only [hc₂]
    exact wellScopedAux_weaken _ _ fv₁ fv₂ body (barrier_insert seen₁ seen₂ fv₁ fv₂ x hbar) s₁ h
  | Fix f body =>
    unfold wellScopedAux at h ⊢; have ⟨hc₁, h⟩ := hcheck_extract h
    have hc₂ := check_false_of_barrier hbar hc₁
    simp only [hc₂]
    exact wellScopedAux_weaken _ _ fv₁ fv₂ body (barrier_insert seen₁ seen₂ fv₁ fv₂ f hbar) s₁ h
  | App f x =>
    unfold wellScopedAux at h ⊢; simp only [bind, Option.bind] at h ⊢
    split at h
    · simp at h
    · rename_i mid₁ hmid₁
      have ⟨mid₂, hmid₂, hbar'⟩ := wellScopedAux_weaken seen₁ seen₂ fv₁ fv₂ f hbar mid₁ hmid₁
      rw [hmid₂]
      exact wellScopedAux_weaken mid₁ mid₂ fv₁ fv₂ x hbar' s₁ h
  | Constr _ args =>
    unfold wellScopedAux at h ⊢
    exact wellScopedListAux_weaken seen₁ seen₂ fv₁ fv₂ args hbar s₁ h
  | Case scrut alts =>
    unfold wellScopedAux at h ⊢; simp only [bind, Option.bind] at h ⊢
    split at h
    · simp at h
    · rename_i mid₁ hmid₁
      have ⟨mid₂, hmid₂, hbar'⟩ := wellScopedAux_weaken seen₁ seen₂ fv₁ fv₂ scrut hbar mid₁ hmid₁
      rw [hmid₂]
      exact wellScopedListAux_weaken mid₁ mid₂ fv₁ fv₂ alts hbar' s₁ h
  | Let binds body =>
    unfold wellScopedAux at h ⊢
    exact wellScopedLetAux_weaken seen₁ seen₂ fv₁ fv₂ binds body hbar s₁ h
termination_by sizeOf e

private theorem wellScopedListAux_weaken (seen₁ seen₂ fv₁ fv₂ : VarSet) (es : List Expr)
    (hbar : ∀ v, seen₂.contains v = true ∨ fv₂.contains v = true →
                 seen₁.contains v = true ∨ fv₁.contains v = true)
    (s₁ : VarSet) (h : wellScopedListAux seen₁ fv₁ es = some s₁) :
    ∃ s₂, wellScopedListAux seen₂ fv₂ es = some s₂ ∧
           (∀ v, s₂.contains v = true ∨ fv₂.contains v = true →
                 s₁.contains v = true ∨ fv₁.contains v = true) := by
  cases es with
  | nil => unfold wellScopedListAux at h ⊢; injection h with h; subst h; exact ⟨seen₂, rfl, hbar⟩
  | cons e rest =>
    unfold wellScopedListAux at h ⊢; simp only [bind, Option.bind] at h ⊢
    split at h
    · simp at h
    · rename_i mid₁ hmid₁
      have ⟨mid₂, hmid₂, hbar'⟩ := wellScopedAux_weaken seen₁ seen₂ fv₁ fv₂ e hbar mid₁ hmid₁
      rw [hmid₂]
      exact wellScopedListAux_weaken mid₁ mid₂ fv₁ fv₂ rest hbar' s₁ h
termination_by sizeOf es

private theorem wellScopedLetAux_weaken (seen₁ seen₂ fv₁ fv₂ : VarSet)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (hbar : ∀ v, seen₂.contains v = true ∨ fv₂.contains v = true →
                 seen₁.contains v = true ∨ fv₁.contains v = true)
    (s₁ : VarSet) (h : wellScopedLetAux seen₁ fv₁ binds body = some s₁) :
    ∃ s₂, wellScopedLetAux seen₂ fv₂ binds body = some s₂ ∧
           (∀ v, s₂.contains v = true ∨ fv₂.contains v = true →
                 s₁.contains v = true ∨ fv₁.contains v = true) := by
  cases binds with
  | nil => unfold wellScopedLetAux at h ⊢
           exact wellScopedAux_weaken seen₁ seen₂ fv₁ fv₂ body hbar s₁ h
  | cons b rest =>
    have := sizeOf_rhs_lt b rest body
    unfold wellScopedLetAux at h ⊢; simp only [bind, Option.bind] at h ⊢
    split at h
    · simp at h
    · rename_i mid₁ hmid₁
      have ⟨mid₂, hmid₂, hbar'⟩ := wellScopedAux_weaken seen₁ seen₂ fv₁ fv₂ b.2.1 hbar mid₁ hmid₁
      rw [hmid₂]
      have hc₁ : (mid₁.contains b.1 || fv₁.contains b.1) = false := by
        cases hc : (mid₁.contains b.1 || fv₁.contains b.1) <;> simp [hc] at h ⊢
      simp only [hc₁] at h
      have hc₂ := check_false_of_barrier hbar' hc₁
      simp only [hc₂]
      exact wellScopedLetAux_weaken _ _ fv₁ fv₂ rest body
        (barrier_insert mid₁ mid₂ fv₁ fv₂ b.1 hbar') s₁ h
termination_by sizeOf binds + sizeOf body
end

/-! ## wellScoped_canonicalize -/

theorem wellScoped_canonicalize (e : Expr) :
    wellScoped (canonicalize e) = true := by
  unfold wellScoped canonicalize
  have ⟨s, hs⟩ := Moist.MIR.wellScopedAux_canonicalize_with_freeVars e
  have ⟨s₂, hs₂, _⟩ := wellScopedAux_weaken VarSet.empty VarSet.empty (freeVars e)
    (freeVars (canonicalizeAux [] (maxUidExpr e + 1) e).1)
    (canonicalizeAux [] (maxUidExpr e + 1) e).1
    (fun v hv => hv.elim Or.inl
      (fun h => Or.inr (Moist.MIR.freeVars_canonicalize_sub e v h)))
    s hs
  rw [isSome_iff]; exact ⟨s₂, hs₂⟩

end Moist.MIR.WellScoped
