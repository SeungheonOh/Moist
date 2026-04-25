import Moist.MIR.Analysis
import Moist.MIR.Canonicalize
import Moist.MIR.LowerTotal
import Moist.MIR.Optimize.Inline
import Moist.MIR.WellScoped
import Moist.Verified.InlineSoundness.SubstCommute

namespace Moist.Verified.InlineSoundness.WellScoped

open Moist.MIR (Expr VarId VarSet freeVars freeVarsList freeVarsLet wellScoped
  wellScopedAux wellScopedListAux wellScopedLetAux
  distinctBinders allDistinctBinders allDistinctBindersList
  allDistinctBindersBinds expandFix canonicalize
  expandFix_freeVars_not_contains)
open Moist.Verified.InlineSoundness.SubstCommute
  (noCaptureFrom noCaptureFromList noCaptureFromLet
   noCaptureFrom_lam noCaptureFrom_fix noCaptureFrom_app
   noCaptureFrom_force noCaptureFrom_delay noCaptureFrom_constr
   noCaptureFrom_case noCaptureFrom_let
   noCaptureFromList_cons noCaptureFromLet_cons noCaptureFromLet_nil_body)

private theorem isSome_iff {α} {x : Option α} : x.isSome = true ↔ ∃ a, x = some a := by
  cases x <;> simp [Option.isSome]

private theorem contains_of_beq (s : VarSet) {v w : VarId}
    (hvw : (v == w) = true) (h : s.contains v = true) : s.contains w = true := by
  simp only [VarSet.contains] at h ⊢
  rw [← Array.any_toList] at h ⊢
  exact Moist.MIR.List.any_beq_varid_trans _ _ _ hvw h


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

private theorem wellScopedAux_seen_equiv (seen₁ seen₂ fv : VarSet) (e : Expr)
    (hbar : ∀ v, seen₂.contains v = true → seen₁.contains v = true)
    (h : (wellScopedAux seen₁ fv e).isSome = true) :
    (wellScopedAux seen₂ fv e).isSome = true := by
  exact wellScopedAux_weaken' seen₁ seen₂ fv fv e
    (fun v hv => hv.elim (fun h => Or.inl (hbar v h)) Or.inr) h

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

mutual
private theorem wellScopedAux_noBinderFromFinalAbsence
    (seen fv : VarSet) (e : Expr) (s : VarSet)
    (h : wellScopedAux seen fv e = some s) (x : VarId)
    (hs : s.contains x = false) :
    noCaptureFrom (VarSet.singleton x) e = true := by
  cases e with
  | Var _ | Lit _ | Builtin _ | Error =>
    unfold noCaptureFrom
    rfl
  | Force inner | Delay inner =>
    unfold noCaptureFrom
    unfold wellScopedAux at h
    exact wellScopedAux_noBinderFromFinalAbsence seen fv inner s h x hs
  | Lam y body =>
    unfold noCaptureFrom
    unfold wellScopedAux at h
    have ⟨hc, hbody⟩ := hcheck_extract h
    have hy_body : s.contains y = true :=
      wellScopedAux_seen_mono (seen.insert y) fv body s hbody y
        (VarSet.contains_insert_self seen y)
    have hy_not : (VarSet.singleton x).contains y = false := by
      cases hxy : (VarSet.singleton x).contains y
      · rfl
      · have hxy' : (x == y) = true := by
          simpa [VarSet.singleton_contains'] using hxy
        have hyx : (y == x) = true := by
          rw [Moist.MIR.VarId.beq_true_iff] at hxy' ⊢
          rcases hxy' with ⟨ho, hu⟩
          exact ⟨ho.symm, hu.symm⟩
        have hx_true : s.contains x = true := contains_of_beq s hyx hy_body
        simp [hs] at hx_true
    simp only [hy_not, Bool.not_false, Bool.true_and]
    exact wellScopedAux_noBinderFromFinalAbsence (seen.insert y) fv body s hbody x hs
  | Fix f body =>
    unfold noCaptureFrom
    unfold wellScopedAux at h
    have ⟨hc, hbody⟩ := hcheck_extract h
    have hf_body : s.contains f = true :=
      wellScopedAux_seen_mono (seen.insert f) fv body s hbody f
        (VarSet.contains_insert_self seen f)
    have hf_not : (VarSet.singleton x).contains f = false := by
      cases hxf : (VarSet.singleton x).contains f
      · rfl
      · have hxf' : (x == f) = true := by
          simpa [VarSet.singleton_contains'] using hxf
        have hfx : (f == x) = true := by
          rw [Moist.MIR.VarId.beq_true_iff] at hxf' ⊢
          rcases hxf' with ⟨ho, hu⟩
          exact ⟨ho.symm, hu.symm⟩
        have hx_true : s.contains x = true := contains_of_beq s hfx hf_body
        simp [hs] at hx_true
    simp only [hf_not, Bool.not_false, Bool.true_and]
    exact wellScopedAux_noBinderFromFinalAbsence (seen.insert f) fv body s hbody x hs
  | App f a =>
    unfold noCaptureFrom
    unfold wellScopedAux at h
    simp only [bind, Option.bind, Bool.and_eq_true] at h ⊢
    split at h
    · simp at h
    · rename_i mid hmid
      have hmid_x : mid.contains x = false := by
        cases hm : mid.contains x
        · rfl
        · have hx_true : s.contains x = true := wellScopedAux_seen_mono mid fv a s h x hm
          simp [hs] at hx_true
      exact ⟨wellScopedAux_noBinderFromFinalAbsence seen fv f mid hmid x hmid_x,
             wellScopedAux_noBinderFromFinalAbsence mid fv a s h x hs⟩
  | Constr _ args =>
    unfold noCaptureFrom
    unfold wellScopedAux at h
    exact wellScopedListAux_noBinderFromFinalAbsence seen fv args s h x hs
  | Case scrut alts =>
    unfold noCaptureFrom
    unfold wellScopedAux at h
    simp only [bind, Option.bind, Bool.and_eq_true] at h ⊢
    split at h
    · simp at h
    · rename_i mid hmid
      have hmid_x : mid.contains x = false := by
        cases hm : mid.contains x
        · rfl
        · have hx_true : s.contains x = true := wellScopedListAux_seen_mono mid fv alts s h x hm
          simp [hs] at hx_true
      exact ⟨wellScopedAux_noBinderFromFinalAbsence seen fv scrut mid hmid x hmid_x,
             wellScopedListAux_noBinderFromFinalAbsence mid fv alts s h x hs⟩
  | Let binds body =>
    unfold noCaptureFrom
    unfold wellScopedAux at h
    exact wellScopedLetAux_noBinderFromFinalAbsence seen fv binds body s h x hs
termination_by sizeOf e

private theorem wellScopedListAux_noBinderFromFinalAbsence
    (seen fv : VarSet) (es : List Expr) (s : VarSet)
    (h : wellScopedListAux seen fv es = some s) (x : VarId)
    (hs : s.contains x = false) :
    noCaptureFromList (VarSet.singleton x) es = true := by
  cases es with
  | nil =>
    unfold noCaptureFromList
    rfl
  | cons e rest =>
    unfold noCaptureFromList
    unfold wellScopedListAux at h
    simp only [bind, Option.bind, Bool.and_eq_true] at h ⊢
    split at h
    · simp at h
    · rename_i mid hmid
      have hmid_x : mid.contains x = false := by
        cases hm : mid.contains x
        · rfl
        · have hx_true : s.contains x = true := wellScopedListAux_seen_mono mid fv rest s h x hm
          simp [hs] at hx_true
      exact ⟨wellScopedAux_noBinderFromFinalAbsence seen fv e mid hmid x hmid_x,
             wellScopedListAux_noBinderFromFinalAbsence mid fv rest s h x hs⟩
termination_by sizeOf es

private theorem wellScopedLetAux_noBinderFromFinalAbsence
    (seen fv : VarSet) (binds : List (VarId × Expr × Bool)) (body : Expr) (s : VarSet)
    (h : wellScopedLetAux seen fv binds body = some s) (x : VarId)
    (hs : s.contains x = false) :
    noCaptureFromLet (VarSet.singleton x) binds body = true := by
  cases binds with
  | nil =>
    unfold noCaptureFromLet
    unfold wellScopedLetAux at h
    exact wellScopedAux_noBinderFromFinalAbsence seen fv body s h x hs
  | cons b rest =>
    have := sizeOf_rhs_lt b rest body
    unfold noCaptureFromLet
    unfold wellScopedLetAux at h
    simp only [bind, Option.bind] at h
    split at h
    · simp at h
    · rename_i mid hmid
      have hc₁ : (mid.contains b.1 || fv.contains b.1) = false := by
        cases hc : (mid.contains b.1 || fv.contains b.1) <;> simp [hc] at h ⊢
      simp only [hc₁] at h
      have hmid_x : mid.contains x = false := by
        cases hm : mid.contains x
        · rfl
        · have hmx : (mid.insert b.1).contains x = true :=
            VarSet.contains_insert_of_contains mid b.1 x hm
          have hx_true : s.contains x = true :=
            wellScopedLetAux_seen_mono (mid.insert b.1) fv rest body s h x hmx
          simp [hs] at hx_true
      have hb_not : (VarSet.singleton x).contains b.1 = false := by
        cases hbx : (VarSet.singleton x).contains b.1
        · rfl
        · have hxb : (x == b.1) = true := by
            simpa [VarSet.singleton_contains'] using hbx
          have hbx' : (b.1 == x) = true := by
            rw [Moist.MIR.VarId.beq_true_iff] at hxb ⊢
            rcases hxb with ⟨ho, hu⟩
            exact ⟨ho.symm, hu.symm⟩
          have hs_b : s.contains b.1 = true :=
            wellScopedLetAux_seen_mono (mid.insert b.1) fv rest body s h b.1
              (VarSet.contains_insert_self mid b.1)
          have hx_true : s.contains x = true := contains_of_beq s hbx' hs_b
          simp [hs] at hx_true
      simp only [hb_not, Bool.not_false, Bool.true_and, Bool.and_eq_true]
      exact ⟨wellScopedAux_noBinderFromFinalAbsence seen fv b.2.1 mid hmid x hmid_x,
             wellScopedLetAux_noBinderFromFinalAbsence (mid.insert b.1) fv rest body s h x hs⟩
termination_by sizeOf binds + sizeOf body
end

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

/-! ## noCaptureFrom from wellScopedAux (fv' ⊆ fv condition) -/

mutual
theorem wellScopedAux_noCaptureFrom (seen fv fv' : VarSet) (e : Expr)
    (hfv : ∀ v, fv'.contains v = true → fv.contains v = true)
    (s : VarSet) (h : wellScopedAux seen fv e = some s) :
    noCaptureFrom fv' e = true := by
  cases e with
  | Var _ | Lit _ | Builtin _ | Error => unfold noCaptureFrom; rfl
  | Force inner | Delay inner =>
    unfold noCaptureFrom; unfold wellScopedAux at h
    exact wellScopedAux_noCaptureFrom seen fv fv' inner hfv s h
  | Lam x body =>
    unfold noCaptureFrom; unfold wellScopedAux at h
    have ⟨hc, h⟩ := hcheck_extract h
    have : fv'.contains x = false := by
      cases hx : fv'.contains x
      · rfl
      · exfalso; simp only [Bool.or_eq_false_iff] at hc; exact absurd (hfv x hx) (by simp [hc.2])
    simp only [this, Bool.not_false, Bool.true_and]
    exact wellScopedAux_noCaptureFrom _ fv fv' body hfv s h
  | Fix f body =>
    unfold noCaptureFrom; unfold wellScopedAux at h
    have ⟨hc, h⟩ := hcheck_extract h
    have : fv'.contains f = false := by
      cases hx : fv'.contains f
      · rfl
      · exfalso; simp only [Bool.or_eq_false_iff] at hc; exact absurd (hfv f hx) (by simp [hc.2])
    simp only [this, Bool.not_false, Bool.true_and]
    exact wellScopedAux_noCaptureFrom _ fv fv' body hfv s h
  | App f x =>
    unfold noCaptureFrom; unfold wellScopedAux at h
    simp only [bind, Option.bind] at h; simp only [Bool.and_eq_true]
    split at h
    · simp at h
    · rename_i mid hmid
      exact ⟨wellScopedAux_noCaptureFrom seen fv fv' f hfv mid hmid,
             wellScopedAux_noCaptureFrom mid fv fv' x hfv s h⟩
  | Constr _ args =>
    unfold noCaptureFrom; unfold wellScopedAux at h
    exact wellScopedListAux_noCaptureFrom seen fv fv' args hfv s h
  | Case scrut alts =>
    unfold noCaptureFrom; unfold wellScopedAux at h
    simp only [bind, Option.bind] at h; simp only [Bool.and_eq_true]
    split at h
    · simp at h
    · rename_i mid hmid
      exact ⟨wellScopedAux_noCaptureFrom seen fv fv' scrut hfv mid hmid,
             wellScopedListAux_noCaptureFrom mid fv fv' alts hfv s h⟩
  | Let binds body =>
    unfold noCaptureFrom; unfold wellScopedAux at h
    exact wellScopedLetAux_noCaptureFrom seen fv fv' binds body hfv s h
termination_by sizeOf e

theorem wellScopedListAux_noCaptureFrom (seen fv fv' : VarSet) (es : List Expr)
    (hfv : ∀ v, fv'.contains v = true → fv.contains v = true)
    (s : VarSet) (h : wellScopedListAux seen fv es = some s) :
    noCaptureFromList fv' es = true := by
  cases es with
  | nil => unfold noCaptureFromList; rfl
  | cons e rest =>
    unfold noCaptureFromList; unfold wellScopedListAux at h
    simp only [bind, Option.bind] at h; simp only [Bool.and_eq_true]
    split at h
    · simp at h
    · rename_i mid hmid
      exact ⟨wellScopedAux_noCaptureFrom seen fv fv' e hfv mid hmid,
             wellScopedListAux_noCaptureFrom mid fv fv' rest hfv s h⟩
termination_by sizeOf es

theorem wellScopedLetAux_noCaptureFrom (seen fv fv' : VarSet)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (hfv : ∀ v, fv'.contains v = true → fv.contains v = true)
    (s : VarSet) (h : wellScopedLetAux seen fv binds body = some s) :
    noCaptureFromLet fv' binds body = true := by
  cases binds with
  | nil =>
    unfold noCaptureFromLet; unfold wellScopedLetAux at h
    exact wellScopedAux_noCaptureFrom seen fv fv' body hfv s h
  | cons b rest =>
    have := sizeOf_rhs_lt b rest body
    unfold noCaptureFromLet; unfold wellScopedLetAux at h
    simp only [bind, Option.bind] at h
    split at h
    · simp at h
    · rename_i mid hmid
      have hc₁ : (mid.contains b.1 || fv.contains b.1) = false := by
        cases hc : (mid.contains b.1 || fv.contains b.1) <;> simp [hc] at h ⊢
      simp only [hc₁] at h
      have : fv'.contains b.1 = false := by
        cases hx : fv'.contains b.1
        · rfl
        · exfalso; simp only [Bool.or_eq_false_iff] at hc₁; exact absurd (hfv b.1 hx) (by simp [hc₁.2])
      simp only [this, Bool.not_false, Bool.true_and, Bool.and_eq_true]
      exact ⟨wellScopedAux_noCaptureFrom seen fv fv' b.2.1 hfv mid hmid,
             wellScopedLetAux_noCaptureFrom _ fv fv' rest body hfv s h⟩
termination_by sizeOf binds + sizeOf body
end

/-! ## noCaptureFromLet implies noCaptureFrom on body -/

private theorem noCaptureFromLet_body (fv' : VarSet)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (h : noCaptureFromLet fv' binds body = true) :
    noCaptureFrom fv' body = true := by
  induction binds with
  | nil => unfold noCaptureFromLet at h; exact h
  | cons b rest ih =>
    unfold noCaptureFromLet at h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ih h.2

private theorem noCaptureFromLet_binds (fv' : VarSet)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (h : noCaptureFromLet fv' binds body = true) :
    binds.all (fun b => noCaptureFrom fv' b.2.1) = true := by
  induction binds with
  | nil => simp [List.all]
  | cons b rest ih =>
    unfold noCaptureFromLet at h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨h.1.2, ih h.2⟩

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

/-! ## allDistinctBinders from wellScopedAux -/

mutual
theorem wellScopedAux_allDistinctBinders (seen fv : VarSet) (e : Expr)
    (s : VarSet) (h : wellScopedAux seen fv e = some s) :
    allDistinctBinders e = true := by
  cases e with
  | Var _ | Lit _ | Builtin _ | Error => unfold allDistinctBinders; rfl
  | Force inner | Delay inner =>
    unfold allDistinctBinders; unfold wellScopedAux at h
    exact wellScopedAux_allDistinctBinders seen fv inner s h
  | Lam _ body =>
    unfold allDistinctBinders; unfold wellScopedAux at h
    have ⟨_, h⟩ := hcheck_extract h
    exact wellScopedAux_allDistinctBinders _ fv body s h
  | Fix _ body =>
    unfold allDistinctBinders; unfold wellScopedAux at h
    have ⟨_, h⟩ := hcheck_extract h
    exact wellScopedAux_allDistinctBinders _ fv body s h
  | App f x =>
    unfold allDistinctBinders; unfold wellScopedAux at h
    simp only [bind, Option.bind] at h; simp only [Bool.and_eq_true]
    split at h
    · simp at h
    · rename_i mid hmid
      exact ⟨wellScopedAux_allDistinctBinders seen fv f mid hmid,
             wellScopedAux_allDistinctBinders mid fv x s h⟩
  | Constr _ args =>
    unfold allDistinctBinders; unfold wellScopedAux at h
    exact wellScopedListAux_allDistinctBinders seen fv args s h
  | Case scrut alts =>
    unfold allDistinctBinders; unfold wellScopedAux at h
    simp only [bind, Option.bind] at h; simp only [Bool.and_eq_true]
    split at h
    · simp at h
    · rename_i mid hmid
      exact ⟨wellScopedAux_allDistinctBinders seen fv scrut mid hmid,
             wellScopedListAux_allDistinctBinders mid fv alts s h⟩
  | Let binds body =>
    unfold allDistinctBinders; unfold wellScopedAux at h
    have ⟨hd, hb, ha⟩ := wellScopedLetAux_allDistinctBinders seen fv binds body s h
    simp only [Bool.and_eq_true]; exact ⟨⟨hd, hb⟩, ha⟩
termination_by sizeOf e

theorem wellScopedListAux_allDistinctBinders (seen fv : VarSet) (es : List Expr)
    (s : VarSet) (h : wellScopedListAux seen fv es = some s) :
    allDistinctBindersList es = true := by
  cases es with
  | nil => unfold allDistinctBindersList; rfl
  | cons e rest =>
    unfold allDistinctBindersList; unfold wellScopedListAux at h
    simp only [bind, Option.bind] at h; simp only [Bool.and_eq_true]
    split at h
    · simp at h
    · rename_i mid hmid
      exact ⟨wellScopedAux_allDistinctBinders seen fv e mid hmid,
             wellScopedListAux_allDistinctBinders mid fv rest s h⟩
termination_by sizeOf es

theorem wellScopedLetAux_allDistinctBinders (seen fv : VarSet)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (s : VarSet) (h : wellScopedLetAux seen fv binds body = some s) :
    distinctBinders binds = true ∧ allDistinctBindersBinds binds = true ∧
    allDistinctBinders body = true := by
  cases binds with
  | nil =>
    unfold distinctBinders allDistinctBindersBinds wellScopedLetAux at *
    exact ⟨rfl, rfl, wellScopedAux_allDistinctBinders seen fv body s h⟩
  | cons b rest =>
    have := sizeOf_rhs_lt b rest body
    unfold wellScopedLetAux at h; simp only [bind, Option.bind] at h
    split at h
    · simp at h
    · rename_i mid hmid
      have hc₁ : (mid.contains b.1 || fv.contains b.1) = false := by
        cases hc : (mid.contains b.1 || fv.contains b.1) <;> simp [hc] at h ⊢
      simp only [hc₁] at h
      have ⟨hdist_rest, hbinds_rest, hbody⟩ :=
        wellScopedLetAux_allDistinctBinders (mid.insert b.1) fv rest body s h
      refine ⟨?_, ?_, hbody⟩
      · unfold distinctBinders; simp only [Bool.and_eq_true]
        constructor
        · have hbnot := wellScopedLetAux_binders_not_in_seen (mid.insert b.1) fv rest body s h
          rw [List.all_eq_true] at hbnot ⊢
          intro c hc
          have hc_not_ins := hbnot c hc
          simp only [Bool.not_eq_true'] at hc_not_ins
          cases hcb : (c.1 == b.1)
          · simp
          · exfalso
            have hbeq_sym : (b.1 == c.1) = true := by
              simp only [BEq.beq, Bool.and_eq_true] at hcb ⊢
              obtain ⟨ho, hu⟩ := hcb
              simp only [decide_eq_true_eq] at hu
              refine ⟨?_, by simp only [decide_eq_true_eq]; exact hu.symm⟩
              revert ho; cases c.1.origin <;> cases b.1.origin <;> intro h <;> first | exact h | exact absurd h (by decide)
            have := VarSet.contains_insert_elim mid b.1 c.1 |>.mpr (Or.inr hbeq_sym)
            rw [hc_not_ins] at this; simp at this
        · exact hdist_rest
      · unfold allDistinctBindersBinds; simp only [Bool.and_eq_true]
        exact ⟨wellScopedAux_allDistinctBinders seen fv b.2.1 mid hmid, hbinds_rest⟩
termination_by sizeOf binds + sizeOf body
end

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

private theorem wellScopedLetAux_body_wellScoped (seen fv : VarSet)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (s : VarSet) (h : wellScopedLetAux seen fv binds body = some s)
    (hfv : ∀ v, (Moist.MIR.freeVars body).contains v = true → fv.contains v = true) :
    wellScoped body = true := by
  cases binds with
  | nil =>
    unfold wellScopedLetAux at h
    exact wellScoped_of_wellScopedAux_fv_sub seen fv body s h hfv
  | cons b rest =>
    have := sizeOf_rhs_lt b rest body
    unfold wellScopedLetAux at h; simp only [bind, Option.bind] at h
    split at h
    · simp at h
    · rename_i mid hmid
      have hc₁ : (mid.contains b.1 || fv.contains b.1) = false := by
        cases hc : (mid.contains b.1 || fv.contains b.1) <;> simp [hc] at h ⊢
      simp only [hc₁] at h
      exact wellScopedLetAux_body_wellScoped _ fv rest body s h hfv
termination_by sizeOf binds + sizeOf body

private theorem wellScopedLetAux_each_bind_wellScoped (seen fv : VarSet)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (s : VarSet) (h : wellScopedLetAux seen fv binds body = some s)
    (hfv : ∀ b, b ∈ binds → ∀ v, (Moist.MIR.freeVars b.2.1).contains v = true → fv.contains v = true) :
    ∀ b, b ∈ binds → wellScoped b.2.1 = true := by
  cases binds with
  | nil => intro b hb; simp at hb
  | cons bd rest =>
    have := sizeOf_rhs_lt bd rest body
    unfold wellScopedLetAux at h; simp only [bind, Option.bind] at h
    split at h
    · simp at h
    · rename_i mid hmid
      have hc₁ : (mid.contains bd.1 || fv.contains bd.1) = false := by
        cases hc : (mid.contains bd.1 || fv.contains bd.1) <;> simp [hc] at h ⊢
      simp only [hc₁] at h
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact wellScoped_of_wellScopedAux_fv_sub seen fv b.2.1 mid hmid
          (hfv b (List.mem_cons_self ..))
      · exact wellScopedLetAux_each_bind_wellScoped _ fv rest body s h
          (fun b' hb' v hv => hfv b' (List.mem_cons_of_mem _ hb') v hv)
          b hb
termination_by sizeOf binds + sizeOf body

/-! ## freeVars subset lemmas for Let -/

private theorem freeVars_rhs_sub_freeVarsLet (b : VarId × Expr × Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) (v : VarId)
    (hv : (Moist.MIR.freeVars b.2.1).contains v = true) :
    (Moist.MIR.freeVarsLet (b :: rest) body).contains v = true := by
  unfold Moist.MIR.freeVarsLet
  exact VarSet.contains_union_left _ _ _ hv

/-! ## Main theorems -/

theorem wellScoped_sub_constr {tag : Nat} {args : List Expr}
    (h : wellScoped (.Constr tag args) = true) :
    allDistinctBindersList args = true ∧
    ∀ e ∈ args, wellScoped e = true := by
  unfold wellScoped at h; unfold wellScopedAux at h; unfold Moist.MIR.freeVars at h
  rw [isSome_iff] at h; obtain ⟨s, hs⟩ := h
  exact ⟨wellScopedListAux_allDistinctBinders _ _ args s hs,
         wellScopedListAux_each_wellScoped _ _ args s hs
           (fun e he v hv => freeVars_mem_sub_freeVarsList args e he v hv)⟩

theorem wellScoped_sub_case {scrut : Expr} {alts : List Expr}
    (h : wellScoped (.Case scrut alts) = true) :
    wellScoped scrut = true ∧ allDistinctBindersList alts = true ∧
    ∀ e ∈ alts, wellScoped e = true := by
  unfold wellScoped at h; unfold wellScopedAux at h; unfold Moist.MIR.freeVars at h
  rw [isSome_iff] at h; obtain ⟨s, hs⟩ := h
  simp only [bind, Option.bind] at hs
  split at hs
  · simp at hs
  · rename_i mid hmid
    refine ⟨?_, wellScopedListAux_allDistinctBinders _ _ alts s hs, ?_⟩
    · exact wellScoped_of_wellScopedAux_fv_sub _ _ scrut mid hmid
        (fun v hv => VarSet.contains_union_left _ _ _ hv)
    · exact wellScopedListAux_each_wellScoped _ _ alts s hs
        (fun e he v hv => VarSet.contains_union_right _ _ _
          (freeVars_mem_sub_freeVarsList alts e he v hv))

theorem wellScoped_allDistinctBinders {e : Expr}
    (h : wellScoped e = true) : allDistinctBinders e = true := by
  unfold wellScoped at h
  rw [isSome_iff] at h; obtain ⟨s, hs⟩ := h
  exact wellScopedAux_allDistinctBinders _ _ e s hs

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

theorem wellScoped_let_drop_prefix
    (pref binds : List (VarId × Expr × Bool)) (body : Expr)
    (h : wellScoped (.Let (pref ++ binds) body) = true) :
    wellScoped (.Let binds body) = true := by
  induction pref generalizing binds body with
  | nil =>
    simpa using h
  | cons b pref ih =>
    obtain ⟨v, rhs, er⟩ := b
    simp only [List.cons_append] at h
    exact ih _ _ (wellScoped_let_peel h).2

theorem wellScoped_sub_let {binds : List (VarId × Expr × Bool)} {body : Expr}
    (h : wellScoped (.Let binds body) = true) :
    wellScoped body = true ∧ allDistinctBindersBinds binds = true ∧
    ∀ b ∈ binds, wellScoped b.2.1 = true := by
  induction binds with
  | nil =>
    unfold wellScoped at h; unfold wellScopedAux at h; unfold Moist.MIR.freeVars at h
    unfold wellScopedLetAux at h; unfold Moist.MIR.freeVarsLet at h
    rw [isSome_iff] at h; obtain ⟨s, hs⟩ := h
    refine ⟨?_, by unfold allDistinctBindersBinds; rfl, fun b hb => absurd hb (by simp)⟩
    unfold wellScoped; rw [isSome_iff]; exact ⟨s, hs⟩
  | cons bd rest ih =>
    obtain ⟨v, rhs, er⟩ := bd
    have ⟨hrs, hrest⟩ := wellScoped_let_peel h
    have ⟨hbody, hbinds_rest, hbinds_elem⟩ := ih hrest
    refine ⟨hbody, ?_, ?_⟩
    · unfold allDistinctBindersBinds; simp only [Bool.and_eq_true]
      exact ⟨wellScoped_allDistinctBinders hrs, hbinds_rest⟩
    · intro b hb; rcases List.mem_cons.mp hb with rfl | hb
      · exact hrs
      · exact hbinds_elem b hb

theorem wellScoped_distinctBinders {binds : List (VarId × Expr × Bool)}
    {body : Expr} (h : wellScoped (.Let binds body) = true) :
    distinctBinders binds = true := by
  unfold wellScoped at h; unfold wellScopedAux at h; unfold Moist.MIR.freeVars at h
  rw [isSome_iff] at h; obtain ⟨s, hs⟩ := h
  exact (wellScopedLetAux_allDistinctBinders _ _ binds body s hs).1

theorem wellScoped_app_lam_noCaptureFrom {param : VarId} {body x : Expr}
    (h : wellScoped (.App (.Lam param body) x) = true) :
    noCaptureFrom (freeVars x) body = true := by
  unfold wellScoped at h; unfold wellScopedAux at h; unfold Moist.MIR.freeVars at h
  rw [isSome_iff] at h; obtain ⟨s, hs⟩ := h
  simp only [bind, Option.bind] at hs
  split at hs
  · simp at hs
  · rename_i mid hmid
    unfold wellScopedAux at hmid
    have ⟨_, hmid⟩ := hcheck_extract hmid
    exact wellScopedAux_noCaptureFrom _ _ (Moist.MIR.freeVars x) body
      (fun v hv => VarSet.contains_union_right _ _ _ hv)
      mid hmid

theorem wellScoped_let_noCaptureFrom {v : VarId} {rhs : Expr} {er : Bool}
    {rest : List (VarId × Expr × Bool)} {body : Expr}
    (h : wellScoped (.Let ((v, rhs, er) :: rest) body) = true) :
    noCaptureFrom (freeVars rhs) body = true ∧
    rest.all (fun b => noCaptureFrom (freeVars rhs) b.2.1) = true ∧
    rest.all (fun b => !(freeVars (expandFix rhs)).contains b.1) = true := by
  unfold wellScoped at h; unfold wellScopedAux at h; unfold Moist.MIR.freeVars at h
  rw [isSome_iff] at h; obtain ⟨s, hs⟩ := h
  unfold wellScopedLetAux at hs; simp only [bind, Option.bind] at hs
  split at hs
  · simp at hs
  · rename_i mid hmid
    have hc₁ : (mid.contains v || (Moist.MIR.freeVarsLet ((v, rhs, er) :: rest) body).contains v) = false := by
      cases hc : (mid.contains v || (Moist.MIR.freeVarsLet ((v, rhs, er) :: rest) body).contains v) <;>
        simp [hc] at hs ⊢
    simp only [hc₁] at hs
    have hfv_rhs : ∀ w, (Moist.MIR.freeVars rhs).contains w = true →
        (Moist.MIR.freeVarsLet ((v, rhs, er) :: rest) body).contains w = true := by
      intro w hw; unfold Moist.MIR.freeVarsLet; exact VarSet.contains_union_left _ _ _ hw
    have hncl := wellScopedLetAux_noCaptureFrom _ _ (Moist.MIR.freeVars rhs) rest body hfv_rhs s hs
    refine ⟨noCaptureFromLet_body _ rest body hncl, ?_, ?_⟩
    · exact noCaptureFromLet_binds _ rest body hncl
    · have hbnot := wellScopedLetAux_binders_not_in_fv (mid.insert v)
        (Moist.MIR.freeVarsLet ((v, rhs, er) :: rest) body) rest body s hs
      rw [List.all_eq_true] at hbnot ⊢
      intro b hb; simp only [Bool.not_eq_true']
      have hbnot_b := hbnot b hb; simp only [Bool.not_eq_true'] at hbnot_b
      exact expandFix_freeVars_not_contains rhs b.1 (by
        cases hx : (Moist.MIR.freeVars rhs).contains b.1
        · rfl
        · exact absurd (hfv_rhs b.1 hx) (by simp [hbnot_b]))

theorem wellScoped_canonicalize (e : Expr) :
    wellScoped (canonicalize e) = true :=
  Moist.MIR.WellScoped.wellScoped_canonicalize e

theorem wellScoped_noCaptureFrom {e : Expr}
    (h : wellScoped e = true) :
    noCaptureFrom (freeVars e) e = true := by
  unfold wellScoped at h
  rw [isSome_iff] at h; obtain ⟨s, hs⟩ := h
  exact wellScopedAux_noCaptureFrom _ _ _ e (fun v hv => hv) s hs



/-! ## noCaptureFrom monotonicity: smaller fv → still no capture -/

private theorem contains_false_of_sub {fv fv' : VarSet} {x : VarId}
    (h : fv.contains x = false)
    (hsub : ∀ v, fv'.contains v = true → fv.contains v = true) :
    fv'.contains x = false := by
  cases hx : fv'.contains x
  · rfl
  · exact absurd (hsub x hx) (by simp [h])

mutual
theorem noCaptureFrom_mono (fv fv' : VarSet) (e : Expr)
    (h : noCaptureFrom fv e = true)
    (hsub : ∀ v, fv'.contains v = true → fv.contains v = true) :
    noCaptureFrom fv' e = true := by
  cases e with
  | Var _ | Lit _ | Builtin _ | Error => unfold noCaptureFrom; rfl
  | Force inner | Delay inner =>
    unfold noCaptureFrom at h ⊢
    exact noCaptureFrom_mono fv fv' inner h hsub
  | Lam x body =>
    have ⟨hx, hb⟩ := noCaptureFrom_lam h
    unfold noCaptureFrom; simp only [Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨contains_false_of_sub hx hsub,
           noCaptureFrom_mono fv fv' body hb hsub⟩
  | Fix f body =>
    have ⟨hf, hb⟩ := noCaptureFrom_fix h
    unfold noCaptureFrom; simp only [Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨contains_false_of_sub hf hsub,
           noCaptureFrom_mono fv fv' body hb hsub⟩
  | App f x =>
    have ⟨hf, hx⟩ := noCaptureFrom_app h
    unfold noCaptureFrom; simp only [Bool.and_eq_true]
    exact ⟨noCaptureFrom_mono fv fv' f hf hsub,
           noCaptureFrom_mono fv fv' x hx hsub⟩
  | Constr _ args =>
    unfold noCaptureFrom at h ⊢
    exact noCaptureFromList_mono fv fv' args h hsub
  | Case scrut alts =>
    have ⟨hs, ha⟩ := noCaptureFrom_case h
    unfold noCaptureFrom; simp only [Bool.and_eq_true]
    exact ⟨noCaptureFrom_mono fv fv' scrut hs hsub,
           noCaptureFromList_mono fv fv' alts ha hsub⟩
  | Let binds body =>
    unfold noCaptureFrom at h ⊢
    exact noCaptureFromLet_mono fv fv' binds body h hsub
termination_by sizeOf e

theorem noCaptureFromList_mono (fv fv' : VarSet) (es : List Expr)
    (h : noCaptureFromList fv es = true)
    (hsub : ∀ v, fv'.contains v = true → fv.contains v = true) :
    noCaptureFromList fv' es = true := by
  cases es with
  | nil => unfold noCaptureFromList; rfl
  | cons e rest =>
    have ⟨he, hr⟩ := noCaptureFromList_cons h
    unfold noCaptureFromList; simp only [Bool.and_eq_true]
    exact ⟨noCaptureFrom_mono fv fv' e he hsub,
           noCaptureFromList_mono fv fv' rest hr hsub⟩
termination_by sizeOf es

theorem noCaptureFromLet_mono (fv fv' : VarSet)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (h : noCaptureFromLet fv binds body = true)
    (hsub : ∀ v, fv'.contains v = true → fv.contains v = true) :
    noCaptureFromLet fv' binds body = true := by
  cases binds with
  | nil => unfold noCaptureFromLet at h ⊢; exact noCaptureFrom_mono fv fv' body h hsub
  | cons b rest =>
    have := sizeOf_rhs_lt b rest body
    have ⟨hbname, hbrhs, htail⟩ := noCaptureFromLet_cons h
    unfold noCaptureFromLet; simp only [Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨⟨contains_false_of_sub hbname hsub,
            noCaptureFrom_mono fv fv' b.2.1 hbrhs hsub⟩,
           noCaptureFromLet_mono fv fv' rest body htail hsub⟩
termination_by sizeOf binds + sizeOf body
end

/-! ## noCaptureFrom preserved by subst (when no alpha-renaming needed) -/

mutual
theorem noCaptureFrom_subst (fv : VarSet) (v : VarId) (rhs body : Expr)
    (s : Moist.MIR.FreshState)
    (hnc_body : noCaptureFrom fv body = true)
    (hnc_rhs : noCaptureFrom fv rhs = true)
    (h_no_rename : noCaptureFrom (Moist.MIR.freeVars rhs) body = true) :
    noCaptureFrom fv (Moist.MIR.subst v rhs body s).1 = true := by
  cases body with
  | Var x =>
    simp only [Moist.MIR.subst, pure, StateT.pure]
    by_cases hxv : (x == v) = true
    · simp only [hxv, if_true]; exact hnc_rhs
    · simp only [hxv]; unfold noCaptureFrom; rfl
  | Lit _ | Builtin _ | Error =>
    simp only [Moist.MIR.subst, pure, StateT.pure]; unfold noCaptureFrom; rfl
  | Lam x inner =>
    have ⟨h_nc_x, h_nc_inner⟩ := noCaptureFrom_lam hnc_body
    have ⟨h_nr_x, h_nr_inner⟩ := noCaptureFrom_lam h_no_rename
    by_cases hxv : (x == v) = true
    · simp only [Moist.MIR.subst, hxv, if_true, pure, StateT.pure]; exact hnc_body
    · have hne : (x == v) = false := by cases h : (x == v); rfl; exact absurd h hxv
      have h_sub : (Moist.MIR.subst v rhs (.Lam x inner) s).1 =
          .Lam x (Moist.MIR.subst v rhs inner s).1 := by
        simp only [Moist.MIR.subst, hne, h_nr_x, bind, pure]; rfl
      rw [h_sub]; unfold noCaptureFrom
      simp only [Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨h_nc_x, noCaptureFrom_subst fv v rhs inner s h_nc_inner hnc_rhs h_nr_inner⟩
  | Fix f inner =>
    have ⟨h_nc_f, h_nc_inner⟩ := noCaptureFrom_fix hnc_body
    have ⟨h_nr_f, h_nr_inner⟩ := noCaptureFrom_fix h_no_rename
    by_cases hfv : (f == v) = true
    · simp only [Moist.MIR.subst, hfv, if_true, pure, StateT.pure]; exact hnc_body
    · have hne : (f == v) = false := by cases h : (f == v); rfl; exact absurd h hfv
      have h_sub : (Moist.MIR.subst v rhs (.Fix f inner) s).1 =
          .Fix f (Moist.MIR.subst v rhs inner s).1 := by
        simp only [Moist.MIR.subst, hne, h_nr_f, bind, pure]; rfl
      rw [h_sub]; unfold noCaptureFrom
      simp only [Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨h_nc_f, noCaptureFrom_subst fv v rhs inner s h_nc_inner hnc_rhs h_nr_inner⟩
  | App f x =>
    have ⟨h_nc_f, h_nc_x⟩ := noCaptureFrom_app hnc_body
    have ⟨h_nr_f, h_nr_x⟩ := noCaptureFrom_app h_no_rename
    have h_sub : (Moist.MIR.subst v rhs (.App f x) s).1 =
        .App (Moist.MIR.subst v rhs f s).1
             (Moist.MIR.subst v rhs x (Moist.MIR.subst v rhs f s).2).1 := by
      simp only [Moist.MIR.subst, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub]; unfold noCaptureFrom; simp only [Bool.and_eq_true]
    exact ⟨noCaptureFrom_subst fv v rhs f s h_nc_f hnc_rhs h_nr_f,
           noCaptureFrom_subst fv v rhs x _ h_nc_x hnc_rhs h_nr_x⟩
  | Force inner =>
    have h_nc := noCaptureFrom_force hnc_body
    have h_nr := noCaptureFrom_force h_no_rename
    have h_sub : (Moist.MIR.subst v rhs (.Force inner) s).1 =
        .Force (Moist.MIR.subst v rhs inner s).1 := by
      simp only [Moist.MIR.subst, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub]; unfold noCaptureFrom
    exact noCaptureFrom_subst fv v rhs inner s h_nc hnc_rhs h_nr
  | Delay inner =>
    have h_nc := noCaptureFrom_delay hnc_body
    have h_nr := noCaptureFrom_delay h_no_rename
    have h_sub : (Moist.MIR.subst v rhs (.Delay inner) s).1 =
        .Delay (Moist.MIR.subst v rhs inner s).1 := by
      simp only [Moist.MIR.subst, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub]; unfold noCaptureFrom
    exact noCaptureFrom_subst fv v rhs inner s h_nc hnc_rhs h_nr
  | Constr tag args =>
    have h_nc := noCaptureFrom_constr hnc_body
    have h_nr := noCaptureFrom_constr h_no_rename
    have h_sub : (Moist.MIR.subst v rhs (.Constr tag args) s).1 =
        .Constr tag (Moist.MIR.substList v rhs args s).1 := by
      simp only [Moist.MIR.subst, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub]; unfold noCaptureFrom
    exact noCaptureFromList_substList fv v rhs args s h_nc hnc_rhs h_nr
  | Case scrut alts =>
    have ⟨h_nc_s, h_nc_a⟩ := noCaptureFrom_case hnc_body
    have ⟨h_nr_s, h_nr_a⟩ := noCaptureFrom_case h_no_rename
    have h_sub : (Moist.MIR.subst v rhs (.Case scrut alts) s).1 =
        .Case (Moist.MIR.subst v rhs scrut s).1
              (Moist.MIR.substList v rhs alts (Moist.MIR.subst v rhs scrut s).2).1 := by
      simp only [Moist.MIR.subst, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub]; unfold noCaptureFrom; simp only [Bool.and_eq_true]
    exact ⟨noCaptureFrom_subst fv v rhs scrut s h_nc_s hnc_rhs h_nr_s,
           noCaptureFromList_substList fv v rhs alts _ h_nc_a hnc_rhs h_nr_a⟩
  | Let binds inner =>
    have h_nc := noCaptureFrom_let hnc_body
    have h_nr := noCaptureFrom_let h_no_rename
    have h_sub : (Moist.MIR.subst v rhs (.Let binds inner) s).1 =
        .Let (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs) binds inner s).1.1
             (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs) binds inner s).1.2 := by
      simp only [Moist.MIR.subst, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub]; unfold noCaptureFrom
    exact noCaptureFromLet_substLet fv v rhs binds inner s h_nc hnc_rhs h_nr
termination_by sizeOf body

theorem noCaptureFromList_substList (fv : VarSet) (v : VarId) (rhs : Expr)
    (es : List Expr) (s : Moist.MIR.FreshState)
    (hnc : noCaptureFromList fv es = true)
    (hnc_rhs : noCaptureFrom fv rhs = true)
    (h_nr : noCaptureFromList (Moist.MIR.freeVars rhs) es = true) :
    noCaptureFromList fv (Moist.MIR.substList v rhs es s).1 = true := by
  cases es with
  | nil =>
    simp only [Moist.MIR.substList, pure, StateT.pure]; unfold noCaptureFromList; rfl
  | cons e rest =>
    have ⟨h_nc_e, h_nc_rest⟩ := noCaptureFromList_cons hnc
    have ⟨h_nr_e, h_nr_rest⟩ := noCaptureFromList_cons h_nr
    have h_sub : (Moist.MIR.substList v rhs (e :: rest) s).1 =
        (Moist.MIR.subst v rhs e s).1 ::
        (Moist.MIR.substList v rhs rest (Moist.MIR.subst v rhs e s).2).1 := by
      simp only [Moist.MIR.substList, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub]; unfold noCaptureFromList; simp only [Bool.and_eq_true]
    exact ⟨noCaptureFrom_subst fv v rhs e s h_nc_e hnc_rhs h_nr_e,
           noCaptureFromList_substList fv v rhs rest _ h_nc_rest hnc_rhs h_nr_rest⟩
termination_by sizeOf es

theorem noCaptureFromLet_substLet (fv : VarSet) (v : VarId) (rhs : Expr)
    (binds : List (VarId × Expr × Bool)) (body : Expr) (s : Moist.MIR.FreshState)
    (hnc : noCaptureFromLet fv binds body = true)
    (hnc_rhs : noCaptureFrom fv rhs = true)
    (h_nr : noCaptureFromLet (Moist.MIR.freeVars rhs) binds body = true) :
    noCaptureFromLet fv
      (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs) binds body s).1.1
      (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs) binds body s).1.2 = true := by
  cases binds with
  | nil =>
    simp only [Moist.MIR.substLet, bind, StateT.bind, pure, StateT.pure]
    unfold noCaptureFromLet
    exact noCaptureFrom_subst fv v rhs body s
      (noCaptureFromLet_nil_body hnc) hnc_rhs (noCaptureFromLet_nil_body h_nr)
  | cons b rest =>
    have := sizeOf_rhs_lt b rest body
    have ⟨h_nc_bname, h_nc_brhs, h_nc_tail⟩ := noCaptureFromLet_cons hnc
    have ⟨h_nr_bname, h_nr_brhs, h_nr_tail⟩ := noCaptureFromLet_cons h_nr
    have h_rhs_subst := noCaptureFrom_subst fv v rhs b.2.1 s h_nc_brhs hnc_rhs h_nr_brhs
    by_cases hbv : (b.1 == v) = true
    · have h_form : (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs)
            ((b.1, b.2.1, b.2.2) :: rest) body s).1 =
          ((b.1, (Moist.MIR.subst v rhs b.2.1 s).1, b.2.2) :: rest, body) := by
        simp only [Moist.MIR.substLet, hbv, if_true, bind, StateT.bind, pure, StateT.pure]; rfl
      rw [show (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs)
                  (b :: rest) body s).1.1 =
               (b.1, (Moist.MIR.subst v rhs b.2.1 s).1, b.2.2) :: rest
              from by rw [show b = (b.1, b.2.1, b.2.2) from by simp]; exact congrArg Prod.fst h_form,
          show (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs)
                  (b :: rest) body s).1.2 = body
              from by rw [show b = (b.1, b.2.1, b.2.2) from by simp]; exact congrArg Prod.snd h_form]
      unfold noCaptureFromLet; simp only [Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨⟨h_nc_bname, h_rhs_subst⟩, h_nc_tail⟩
    · have hne : (b.1 == v) = false := by cases h : (b.1 == v); rfl; exact absurd h hbv
      have h1 : (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs)
                  (b :: rest) body s).1.1 =
          (b.1, (Moist.MIR.subst v rhs b.2.1 s).1, b.2.2) ::
          (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs) rest body
             (Moist.MIR.subst v rhs b.2.1 s).2).1.1 := by
        rw [show b = (b.1, b.2.1, b.2.2) from by simp]
        simp only [Moist.MIR.substLet, hne, h_nr_bname, bind, StateT.bind, pure, StateT.pure,
                   Bool.false_eq_true, ↓reduceIte]; rfl
      have h2 : (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs)
                  (b :: rest) body s).1.2 =
          (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs) rest body
             (Moist.MIR.subst v rhs b.2.1 s).2).1.2 := by
        rw [show b = (b.1, b.2.1, b.2.2) from by simp]
        simp only [Moist.MIR.substLet, hne, h_nr_bname, bind, StateT.bind, pure, StateT.pure,
                   Bool.false_eq_true, ↓reduceIte]; rfl
      rw [h1, h2]
      unfold noCaptureFromLet; simp only [Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨⟨h_nc_bname, h_rhs_subst⟩,
             noCaptureFromLet_substLet fv v rhs rest body _ h_nc_tail hnc_rhs h_nr_tail⟩
termination_by sizeOf binds + sizeOf body
end

end Moist.Verified.InlineSoundness.WellScoped
