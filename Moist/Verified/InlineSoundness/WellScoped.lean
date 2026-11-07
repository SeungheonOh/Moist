import Moist.MIR.Analysis
import Moist.MIR.Canonicalize
import Moist.MIR.LowerTotal
import Moist.MIR.Optimize.Inline
import Moist.MIR.WellScoped

/-! # Consequences of `wellScoped`

Subterms of a well-scoped term are well scoped, and the binders of a
well-scoped let are distinct and not free in it. -/

namespace Moist.Verified.InlineSoundness.WellScoped

open Moist.MIR (Expr VarId VarSet freeVars freeVarsList freeVarsLet wellScoped
  wellScopedAux wellScopedListAux wellScopedLetAux
  distinctBinders allDistinctBinders allDistinctBindersList
  allDistinctBindersBinds expandFix canonicalize
  expandFix_freeVars_not_contains)

private theorem isSome_iff {α} {x : Option α} : x.isSome = true ↔ ∃ a, x = some a := by
  cases x <;> simp [Option.isSome]

/-! ## Anti-monotonicity helpers -/

private theorem barrier_insert (seen₁ seen₂ fv₁ fv₂ : VarSet) (b : VarId)
    (hbar : ∀ v, seen₂.contains v = true ∨ fv₂.contains v = true →
                 seen₁.contains v = true ∨ fv₁.contains v = true) :
    ∀ v, (seen₂.insert b).contains v = true ∨ fv₂.contains v = true →
         (seen₁.insert b).contains v = true ∨ fv₁.contains v = true := by
  intro v hv
  rcases hv with hv | hv
  · rw [VarSet.contains_insert_elim] at hv
    rcases hv with hv | hv
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

private theorem hcheck_extract {seen fv : VarSet} {b : VarId} {s : VarSet} {body : Expr}
    (h : (if (seen.contains b || fv.contains b) = true then none
          else wellScopedAux (seen.insert b) fv body) = some s) :
    (seen.contains b || fv.contains b) = false ∧
    wellScopedAux (seen.insert b) fv body = some s := by
  cases hc : (seen.contains b || fv.contains b) <;> simp [hc] at h ⊢
  exact h

private theorem sizeOf_rhs_lt (b : VarId × Expr × Bool) (rest : List (VarId × Expr × Bool))
    (body : Expr) : sizeOf b.2.1 < sizeOf (b :: rest) + sizeOf body := by
  have : sizeOf b.2.1 < sizeOf b := by
    cases b with | mk a p => cases p with | mk e c => simp_wf; omega
  have : sizeOf b < sizeOf (b :: rest) := by simp_wf; omega
  omega

/-! ## Anti-monotonicity of wellScopedAux -/

mutual
theorem wellScopedAux_weaken (seen₁ seen₂ fv₁ fv₂ : VarSet) (e : Expr)
    (hbar : ∀ v, seen₂.contains v = true ∨ fv₂.contains v = true →
                 seen₁.contains v = true ∨ fv₁.contains v = true)
    (s₁ : VarSet) (h : wellScopedAux seen₁ fv₁ e = some s₁) :
    ∃ s₂, wellScopedAux seen₂ fv₂ e = some s₂ ∧
           (∀ v, s₂.contains v = true ∨ fv₂.contains v = true →
                 s₁.contains v = true ∨ fv₁.contains v = true) := by
  cases e with
  | Var _ | Lit _ | Builtin _ | Error =>
    unfold wellScopedAux at h ⊢; injection h with h; subst h; exact ⟨seen₂, rfl, hbar⟩
  | Force inner =>
    unfold wellScopedAux at h ⊢
    exact wellScopedAux_weaken seen₁ seen₂ fv₁ fv₂ inner hbar s₁ h
  | Delay inner =>
    unfold wellScopedAux at h ⊢
    exact wellScopedAux_weaken seen₁ seen₂ fv₁ fv₂ inner hbar s₁ h
  | Lam x body =>
    unfold wellScopedAux at h ⊢
    have ⟨hc₁, h⟩ := hcheck_extract h
    have hc₂ := check_false_of_barrier hbar hc₁
    simp only [hc₂]
    exact wellScopedAux_weaken _ _ fv₁ fv₂ body (barrier_insert seen₁ seen₂ fv₁ fv₂ x hbar) s₁ h
  | Fix f body =>
    unfold wellScopedAux at h ⊢
    have ⟨hc₁, h⟩ := hcheck_extract h
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

theorem wellScopedListAux_weaken (seen₁ seen₂ fv₁ fv₂ : VarSet) (es : List Expr)
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

theorem wellScopedLetAux_weaken (seen₁ seen₂ fv₁ fv₂ : VarSet)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (hbar : ∀ v, seen₂.contains v = true ∨ fv₂.contains v = true →
                 seen₁.contains v = true ∨ fv₁.contains v = true)
    (s₁ : VarSet) (h : wellScopedLetAux seen₁ fv₁ binds body = some s₁) :
    ∃ s₂, wellScopedLetAux seen₂ fv₂ binds body = some s₂ ∧
           (∀ v, s₂.contains v = true ∨ fv₂.contains v = true →
                 s₁.contains v = true ∨ fv₁.contains v = true) := by
  cases binds with
  | nil =>
    unfold wellScopedLetAux at h ⊢
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

private theorem wellScopedAux_weaken' (seen₁ seen₂ fv₁ fv₂ : VarSet) (e : Expr)
    (hbar : ∀ v, seen₂.contains v = true ∨ fv₂.contains v = true →
                 seen₁.contains v = true ∨ fv₁.contains v = true)
    (h : (wellScopedAux seen₁ fv₁ e).isSome = true) :
    (wellScopedAux seen₂ fv₂ e).isSome = true := by
  rw [isSome_iff] at h; obtain ⟨s₁, hs₁⟩ := h
  have ⟨s₂, hs₂, _⟩ := wellScopedAux_weaken seen₁ seen₂ fv₁ fv₂ e hbar s₁ hs₁
  rw [isSome_iff]; exact ⟨s₂, hs₂⟩

/-! ## seen-monotonicity: wellScopedAux preserves seen membership -/

mutual
private theorem wellScopedAux_seen_mono (seen fv : VarSet) (e : Expr) (s : VarSet)
    (h : wellScopedAux seen fv e = some s) (v : VarId)
    (hv : seen.contains v = true) : s.contains v = true := by
  cases e with
  | Var _ | Lit _ | Builtin _ | Error =>
    unfold wellScopedAux at h; injection h with h; subst h; exact hv
  | Force inner | Delay inner =>
    unfold wellScopedAux at h; exact wellScopedAux_seen_mono seen fv inner s h v hv
  | Lam x body =>
    unfold wellScopedAux at h; have ⟨_, h⟩ := hcheck_extract h
    exact wellScopedAux_seen_mono _ fv body s h v (VarSet.contains_insert_of_contains _ _ _ hv)
  | Fix f body =>
    unfold wellScopedAux at h; have ⟨_, h⟩ := hcheck_extract h
    exact wellScopedAux_seen_mono _ fv body s h v (VarSet.contains_insert_of_contains _ _ _ hv)
  | App f x =>
    unfold wellScopedAux at h; simp only [bind, Option.bind] at h
    split at h
    · simp at h
    · rename_i mid hmid
      exact wellScopedAux_seen_mono mid fv x s h v
        (wellScopedAux_seen_mono seen fv f mid hmid v hv)
  | Constr _ args =>
    unfold wellScopedAux at h; exact wellScopedListAux_seen_mono seen fv args s h v hv
  | Case scrut alts =>
    unfold wellScopedAux at h; simp only [bind, Option.bind] at h
    split at h
    · simp at h
    · rename_i mid hmid
      exact wellScopedListAux_seen_mono mid fv alts s h v
        (wellScopedAux_seen_mono seen fv scrut mid hmid v hv)
  | Let binds body =>
    unfold wellScopedAux at h; exact wellScopedLetAux_seen_mono seen fv binds body s h v hv
termination_by sizeOf e

private theorem wellScopedListAux_seen_mono (seen fv : VarSet) (es : List Expr) (s : VarSet)
    (h : wellScopedListAux seen fv es = some s) (v : VarId)
    (hv : seen.contains v = true) : s.contains v = true := by
  cases es with
  | nil => unfold wellScopedListAux at h; injection h with h; subst h; exact hv
  | cons e rest =>
    unfold wellScopedListAux at h; simp only [bind, Option.bind] at h
    split at h
    · simp at h
    · rename_i mid hmid
      exact wellScopedListAux_seen_mono mid fv rest s h v
        (wellScopedAux_seen_mono seen fv e mid hmid v hv)
termination_by sizeOf es

private theorem wellScopedLetAux_seen_mono (seen fv : VarSet)
    (binds : List (VarId × Expr × Bool)) (body : Expr) (s : VarSet)
    (h : wellScopedLetAux seen fv binds body = some s) (v : VarId)
    (hv : seen.contains v = true) : s.contains v = true := by
  cases binds with
  | nil => unfold wellScopedLetAux at h; exact wellScopedAux_seen_mono seen fv body s h v hv
  | cons b rest =>
    have := sizeOf_rhs_lt b rest body
    unfold wellScopedLetAux at h; simp only [bind, Option.bind] at h
    split at h
    · simp at h
    · rename_i mid hmid
      have hc₁ : (mid.contains b.1 || fv.contains b.1) = false := by
        cases hc : (mid.contains b.1 || fv.contains b.1) <;> simp [hc] at h ⊢
      simp only [hc₁] at h
      exact wellScopedLetAux_seen_mono _ fv rest body s h v
        (VarSet.contains_insert_of_contains _ _ _
          (wellScopedAux_seen_mono seen fv b.2.1 mid hmid v hv))
termination_by sizeOf binds + sizeOf body
end

/-! ## Sub-expression lemmas -/

private theorem barrier_lam_fv (x : VarId) (body : Expr) :
    ∀ v, VarSet.empty.contains v = true ∨ (Moist.MIR.freeVars body).contains v = true →
         (VarSet.empty.insert x).contains v = true ∨
         ((Moist.MIR.freeVars body).erase x).contains v = true := by
  intro v hv
  rcases hv with hv | hv
  · simp [VarSet.contains_empty] at hv
  · by_cases hxv : (x == v) = true
    · left; exact VarSet.contains_insert_elim .. |>.mpr (Or.inr hxv)
    · right; simp only [Bool.not_eq_true] at hxv
      exact VarSet.contains_erase_ne _ x v hxv hv

theorem wellScoped_sub_lam {x : VarId} {body : Expr}
    (h : wellScoped (.Lam x body) = true) : wellScoped body = true := by
  unfold wellScoped at h ⊢; unfold wellScopedAux at h; unfold Moist.MIR.freeVars at h
  have hcheck : (VarSet.empty.contains x || ((Moist.MIR.freeVars body).erase x).contains x) = false := by
    rw [VarSet.contains_empty, Bool.false_or, VarSet.contains_erase_self]
  simp only [hcheck] at h
  exact wellScopedAux_weaken' (VarSet.empty.insert x) VarSet.empty
    ((Moist.MIR.freeVars body).erase x) (Moist.MIR.freeVars body) body
    (barrier_lam_fv x body) h

theorem wellScoped_sub_fix {f : VarId} {body : Expr}
    (h : wellScoped (.Fix f body) = true) : wellScoped body = true := by
  unfold wellScoped at h ⊢; unfold wellScopedAux at h; unfold Moist.MIR.freeVars at h
  have hcheck : (VarSet.empty.contains f || ((Moist.MIR.freeVars body).erase f).contains f) = false := by
    rw [VarSet.contains_empty, Bool.false_or, VarSet.contains_erase_self]
  simp only [hcheck] at h
  exact wellScopedAux_weaken' (VarSet.empty.insert f) VarSet.empty
    ((Moist.MIR.freeVars body).erase f) (Moist.MIR.freeVars body) body
    (barrier_lam_fv f body) h

theorem wellScoped_sub_app {f x : Expr}
    (h : wellScoped (.App f x) = true) :
    wellScoped f = true ∧ wellScoped x = true := by
  unfold wellScoped at h ⊢; unfold wellScopedAux at h; unfold Moist.MIR.freeVars at h
  rw [isSome_iff] at h; obtain ⟨s, hs⟩ := h
  simp only [bind, Option.bind] at hs
  split at hs
  · simp at hs
  · rename_i mid hmid
    exact ⟨isSome_iff.mpr (wellScopedAux_weaken VarSet.empty VarSet.empty
        ((Moist.MIR.freeVars f).union (Moist.MIR.freeVars x)) (Moist.MIR.freeVars f) f
        (fun v hv => hv.elim Or.inl (fun h => Or.inr (VarSet.contains_union_left _ _ _ h)))
        mid hmid |>.choose_spec.1 ▸ ⟨_, rfl⟩),
      isSome_iff.mpr (wellScopedAux_weaken mid VarSet.empty
        ((Moist.MIR.freeVars f).union (Moist.MIR.freeVars x)) (Moist.MIR.freeVars x) x
        (fun v hv => hv.elim (fun h => absurd h (by simp [VarSet.contains_empty])) (fun h => Or.inr (VarSet.contains_union_right _ _ _ h)))
        s hs |>.choose_spec.1 ▸ ⟨_, rfl⟩)⟩

theorem wellScoped_sub_force {e : Expr}
    (h : wellScoped (.Force e) = true) : wellScoped e = true := by
  unfold wellScoped at h ⊢; unfold wellScopedAux at h; unfold freeVars at h; exact h
theorem wellScoped_sub_delay {e : Expr}
    (h : wellScoped (.Delay e) = true) : wellScoped e = true := by
  unfold wellScoped at h ⊢; unfold wellScopedAux at h; unfold freeVars at h; exact h

/-! ## Binder not in fv: wellScopedLetAux checks -/

private theorem wellScopedLetAux_binders_not_in_fv (seen fv : VarSet)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (s : VarSet) (h : wellScopedLetAux seen fv binds body = some s) :
    binds.all (fun b => !fv.contains b.1) = true := by
  cases binds with
  | nil => simp [List.all]
  | cons b rest =>
    have := sizeOf_rhs_lt b rest body
    unfold wellScopedLetAux at h; simp only [bind, Option.bind] at h
    split at h
    · simp at h
    · rename_i mid hmid
      have hc₁ : (mid.contains b.1 || fv.contains b.1) = false := by
        cases hc : (mid.contains b.1 || fv.contains b.1) <;> simp [hc] at h ⊢
      simp only [hc₁] at h
      simp only [Bool.or_eq_false_iff] at hc₁
      simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true', hc₁.2, true_and]
      exact wellScopedLetAux_binders_not_in_fv _ fv rest body s h
termination_by sizeOf binds + sizeOf body

private theorem wellScopedLetAux_binders_not_in_seen (seen fv : VarSet)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (s : VarSet) (h : wellScopedLetAux seen fv binds body = some s) :
    binds.all (fun b => !seen.contains b.1) = true := by
  cases binds with
  | nil => simp [List.all]
  | cons b rest =>
    have := sizeOf_rhs_lt b rest body
    unfold wellScopedLetAux at h; simp only [bind, Option.bind] at h
    split at h
    · simp at h
    · rename_i mid hmid
      have hc₁ : (mid.contains b.1 || fv.contains b.1) = false := by
        cases hc : (mid.contains b.1 || fv.contains b.1) <;> simp [hc] at h ⊢
      simp only [hc₁] at h
      simp only [Bool.or_eq_false_iff] at hc₁
      have hmid_b : mid.contains b.1 = false := hc₁.1
      have hseen_b : seen.contains b.1 = false := by
        cases hs : seen.contains b.1
        · rfl
        · exact absurd (wellScopedAux_seen_mono seen fv b.2.1 mid hmid b.1 hs) (by simp [hmid_b])
      simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true', hseen_b, true_and]
      have hrest := wellScopedLetAux_binders_not_in_seen (mid.insert b.1) fv rest body s h
      rw [List.all_eq_true] at hrest ⊢
      intro c hc
      have := hrest c hc
      simp only [Bool.not_eq_true'] at this ⊢
      cases hsc : seen.contains c.1
      · rfl
      · have hins := VarSet.contains_insert_of_contains mid b.1 c.1
            (wellScopedAux_seen_mono seen fv b.2.1 mid hmid c.1 hsc)
        rw [this] at hins; simp at hins
termination_by sizeOf binds + sizeOf body

/-- The binders of a let checked by `wellScopedLetAux` are distinct. -/
private theorem wellScopedLetAux_distinct (seen fv : VarSet)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (s : VarSet) (h : wellScopedLetAux seen fv binds body = some s) :
    distinctBinders binds = true := by
  cases binds with
  | nil => rfl
  | cons b rest =>
    have := sizeOf_rhs_lt b rest body
    unfold wellScopedLetAux at h; simp only [bind, Option.bind] at h
    split at h
    · simp at h
    · rename_i mid hmid
      have hc₁ : (mid.contains b.1 || fv.contains b.1) = false := by
        cases hc : (mid.contains b.1 || fv.contains b.1) <;> simp [hc] at h ⊢
      simp only [hc₁] at h
      have notSeen := wellScopedLetAux_binders_not_in_seen _ fv rest body s h
      simp only [distinctBinders, Bool.and_eq_true, List.all_eq_true] at notSeen ⊢
      refine ⟨fun c hc => ?_, wellScopedLetAux_distinct _ fv rest body s h⟩
      have := notSeen c hc
      cases hcb : (c.1 == b.1)
      · rfl
      · have hbc : (b.1 == c.1) = true :=
          let ⟨o, u⟩ := (Moist.MIR.VarId.beq_true_iff _ _).mp hcb
          (Moist.MIR.VarId.beq_true_iff _ _).mpr ⟨o.symm, u.symm⟩
        have := VarSet.contains_insert_elim mid b.1 c.1 |>.mpr (.inr hbc)
        simp_all
termination_by sizeOf binds + sizeOf body

/-! ## wellScoped for list sub-expressions -/

private theorem wellScoped_of_wellScopedAux_fv_sub (seen fv : VarSet) (e : Expr)
    (s : VarSet) (h : wellScopedAux seen fv e = some s)
    (hfv : ∀ v, (Moist.MIR.freeVars e).contains v = true → fv.contains v = true) :
    wellScoped e = true := by
  unfold wellScoped
  exact wellScopedAux_weaken' seen VarSet.empty fv (Moist.MIR.freeVars e) e
    (fun v hv => hv.elim (fun h => absurd h (by simp [VarSet.contains_empty]))
      (fun h => Or.inr (hfv v h)))
    (isSome_iff.mpr ⟨s, h⟩)

private theorem wellScopedListAux_each_wellScoped (seen fv : VarSet) (es : List Expr)
    (s : VarSet) (h : wellScopedListAux seen fv es = some s)
    (hfv : ∀ e, e ∈ es → ∀ v, (Moist.MIR.freeVars e).contains v = true → fv.contains v = true) :
    ∀ e, e ∈ es → wellScoped e = true := by
  cases es with
  | nil => intro e he; simp at he
  | cons hd rest =>
    unfold wellScopedListAux at h; simp only [bind, Option.bind] at h
    split at h
    · simp at h
    · rename_i mid hmid
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact wellScoped_of_wellScopedAux_fv_sub seen fv e mid hmid
          (hfv e (List.mem_cons_self ..))
      · exact wellScopedListAux_each_wellScoped mid fv rest s h
          (fun e' he' v hv => hfv e' (List.mem_cons_of_mem _ he') v hv)
          e he

private theorem freeVars_mem_sub_freeVarsList (es : List Expr) (e : Expr) (he : e ∈ es)
    (v : VarId) (hv : (Moist.MIR.freeVars e).contains v = true) :
    (Moist.MIR.freeVarsList es).contains v = true := by
  induction es with
  | nil => simp at he
  | cons hd rest ih =>
    unfold Moist.MIR.freeVarsList
    rcases List.mem_cons.mp he with rfl | he
    · exact VarSet.contains_union_left _ _ _ hv
    · exact VarSet.contains_union_right _ _ _ (ih he)

/-! ## wellScoped for Let sub-expressions -/

/-! ## freeVars subset lemmas for Let -/

/-! ## Main theorems -/

theorem wellScoped_sub_constr {tag : Nat} {args : List Expr}
    (h : wellScoped (.Constr tag args) = true) : ∀ e ∈ args, wellScoped e = true := by
  unfold wellScoped at h; unfold wellScopedAux at h; unfold Moist.MIR.freeVars at h
  rw [isSome_iff] at h; obtain ⟨s, hs⟩ := h
  exact wellScopedListAux_each_wellScoped _ _ args s hs
    (fun e he v hv => freeVars_mem_sub_freeVarsList args e he v hv)

theorem wellScoped_sub_case {scrut : Expr} {alts : List Expr}
    (h : wellScoped (.Case scrut alts) = true) :
    wellScoped scrut = true ∧ ∀ e ∈ alts, wellScoped e = true := by
  unfold wellScoped at h; unfold wellScopedAux at h; unfold Moist.MIR.freeVars at h
  rw [isSome_iff] at h; obtain ⟨s, hs⟩ := h
  simp only [bind, Option.bind] at hs
  split at hs
  · simp at hs
  · rename_i mid hmid
    refine ⟨?_, ?_⟩
    · exact wellScoped_of_wellScopedAux_fv_sub _ _ scrut mid hmid
        (fun v hv => VarSet.contains_union_left _ _ _ hv)
    · exact wellScopedListAux_each_wellScoped _ _ alts s hs
        (fun e he v hv => VarSet.contains_union_right _ _ _
          (freeVars_mem_sub_freeVarsList alts e he v hv))

theorem wellScoped_let_peel {v : VarId} {rhs : Expr} {er : Bool}
    {rest : List (VarId × Expr × Bool)} {body : Expr}
    (h : wellScoped (.Let ((v, rhs, er) :: rest) body) = true) :
    wellScoped rhs = true ∧ wellScoped (.Let rest body) = true := by
  unfold wellScoped at h; unfold wellScopedAux at h; unfold Moist.MIR.freeVars at h
  rw [isSome_iff] at h; obtain ⟨s, hs⟩ := h
  unfold wellScopedLetAux at hs; simp only [bind, Option.bind] at hs
  split at hs
  · simp at hs
  · rename_i mid hmid
    have hc₁ : (mid.contains v || (Moist.MIR.freeVarsLet ((v, rhs, er) :: rest) body).contains v) = false := by
      cases hc : (mid.contains v || (Moist.MIR.freeVarsLet ((v, rhs, er) :: rest) body).contains v) <;> simp [hc] at hs ⊢
    simp only [hc₁] at hs
    constructor
    · exact wellScoped_of_wellScopedAux_fv_sub _ _ rhs mid hmid
        (fun w hw => by unfold Moist.MIR.freeVarsLet; exact VarSet.contains_union_left _ _ _ hw)
    · unfold wellScoped wellScopedAux Moist.MIR.freeVars; rw [isSome_iff]
      have ⟨s₂, hs₂, _⟩ := wellScopedLetAux_weaken (mid.insert v) VarSet.empty
        (Moist.MIR.freeVarsLet ((v, rhs, er) :: rest) body) (Moist.MIR.freeVarsLet rest body) rest body
        (fun w hw => by
          rcases hw with hw | hw
          · simp [VarSet.contains_empty] at hw
          · by_cases hvw : (v == w) = true
            · exact Or.inl (VarSet.contains_insert_elim .. |>.mpr (Or.inr hvw))
            · simp only [Bool.not_eq_true] at hvw
              exact Or.inr (by unfold Moist.MIR.freeVarsLet; exact VarSet.contains_union_right _ _ _ (VarSet.contains_erase_ne _ v w hvw hw)))
        s hs
      exact ⟨s₂, hs₂⟩

theorem wellScoped_sub_let {binds : List (VarId × Expr × Bool)} {body : Expr}
    (h : wellScoped (.Let binds body) = true) :
    wellScoped body = true ∧ ∀ b ∈ binds, wellScoped b.2.1 = true := by
  induction binds with
  | nil =>
    unfold wellScoped at h; unfold wellScopedAux at h; unfold Moist.MIR.freeVars at h
    unfold wellScopedLetAux at h; unfold Moist.MIR.freeVarsLet at h
    rw [isSome_iff] at h; obtain ⟨s, hs⟩ := h
    refine ⟨?_, fun b hb => absurd hb (by simp)⟩
    unfold wellScoped; rw [isSome_iff]; exact ⟨s, hs⟩
  | cons bd rest ih =>
    obtain ⟨v, rhs, er⟩ := bd
    have ⟨hrs, hrest⟩ := wellScoped_let_peel h
    have ⟨hbody, hbinds_elem⟩ := ih hrest
    refine ⟨hbody, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hrs
    · exact hbinds_elem b hb

theorem wellScoped_distinctBinders {binds : List (VarId × Expr × Bool)}
    {body : Expr} (h : wellScoped (.Let binds body) = true) :
    distinctBinders binds = true := by
  unfold wellScoped at h; unfold wellScopedAux at h; unfold Moist.MIR.freeVars at h
  rw [isSome_iff] at h; obtain ⟨s, hs⟩ := h
  exact wellScopedLetAux_distinct _ _ binds body s hs

theorem wellScoped_canonicalize (e : Expr) :
    wellScoped (canonicalize e) = true :=
  Moist.MIR.WellScoped.wellScoped_canonicalize e

/-- The binders of a well-scoped let are not free in it. -/
theorem wellScoped_let_names {binds : List (VarId × Expr × Bool)} {body : Expr}
    (h : wellScoped (.Let binds body) = true) :
    ∀ b ∈ binds, (freeVarsLet binds body).contains b.1 = false := by
  unfold wellScoped at h; unfold wellScopedAux at h; unfold Moist.MIR.freeVars at h
  rw [isSome_iff] at h; obtain ⟨s, hs⟩ := h
  have := wellScopedLetAux_binders_not_in_fv _ _ binds body s hs
  rw [List.all_eq_true] at this
  intro b hb; simpa using this b hb

end Moist.Verified.InlineSoundness.WellScoped
