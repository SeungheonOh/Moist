import Moist.MIR.Optimize.Inline
import Moist.Verified.InlineSoundness.SubstCommute

/-! # Invariants the inlining pass maintains

* Free variables never increase (`freeVars_nonincreasing`), and substitution
  only adds the replacement's (`freeVars_subst_tight`).
* `NamesFresh`: no let binder is free in an earlier right-hand side; this
  is what keeps the remaining binders from capturing an inlined right-hand
  side.
* Every uid stays below the fresh-name counter (`inlinePass_fresh`). -/

namespace Moist.Verified.InlineSoundness.Preservation

open Moist.MIR (Expr VarId VarSet freeVars freeVarsList freeVarsLet
  inlinePass inlinePassList inlineBindings inlineLetBindings inlineLetGo
  betaReduce substInBindings subst substList substLet expandFix
  shouldInline countOccurrences wellScoped
  rename renameList renameLet renameBinds freshVar)
open Moist.MIR.VarSet (contains_union_left contains_union_right)

--------------------------------------------------------------------------------
-- Free variables never increase through inlinePass
--------------------------------------------------------------------------------

-- Local helper: union-contains elimination
private theorem contains_union_elim {s₁ s₂ : Moist.MIR.VarSet} {w : VarId}
    (h : (s₁.union s₂).contains w = true) :
    s₁.contains w = true ∨ s₂.contains w = true := by
  cases h₁ : s₁.contains w
  · cases h₂ : s₂.contains w
    · exact absurd h (by rw [Moist.MIR.VarSet.union_not_contains_fwd s₁ s₂ w h₁ h₂]; decide)
    · exact Or.inr rfl
  · exact Or.inl rfl

-- Local helper: erase preserves membership (monotone backward)
private theorem contains_of_contains_erase {s : Moist.MIR.VarSet} {v w : VarId}
    (h : (s.erase v).contains w = true) : s.contains w = true := by
  cases hsx : s.contains w
  · exact absurd h (by rw [Moist.MIR.VarSet.erase_not_contains_fwd s v w hsx]; decide)
  · rfl

-- Local VarId beq helpers
private theorem varid_beq_symm {a b : VarId} (h : (a == b) = true) : (b == a) = true := by
  rw [Moist.MIR.VarId.beq_true_iff] at h ⊢
  exact ⟨h.1.symm, h.2.symm⟩

private theorem varid_beq_trans {a b c : VarId}
    (h1 : (a == b) = true) (h2 : (b == c) = true) : (a == c) = true := by
  rw [Moist.MIR.VarId.beq_true_iff] at h1 h2 ⊢
  exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

-- Local helper: if v == w then (s.erase v).contains w = false
private theorem erase_contains_beq_false (s : Moist.MIR.VarSet) (v w : VarId)
    (hvw : (v == w) = true) : (s.erase v).contains w = false := by
  cases hcw : (s.erase v).contains w with
  | false => rfl
  | true =>
    -- (s.erase v).contains w = true means there exists a ∈ s.data with a != v and a == w
    -- but v == w, so a == w and w == v (by beq_symm) gives a == v (by beq_trans), contradiction
    have h_self := Moist.MIR.VarSet.contains_erase_self s v
    -- w == v by symmetry
    have hwv := varid_beq_symm hvw
    -- s.erase v contains w, and w == v, so s.erase v contains v by contains_of_beq-like reasoning
    -- But contains_erase_self says it doesn't. Contradiction.
    simp only [Moist.MIR.VarSet.erase, Moist.MIR.VarSet.contains, Array.any_filter] at hcw h_self
    rw [Array.any_eq_true] at hcw
    obtain ⟨i, hi, hprop⟩ := hcw
    rw [Bool.and_eq_true] at hprop
    obtain ⟨hne_v, haw⟩ := hprop
    -- haw: s.data[i] == w = true, hvw: v == w = true
    -- so s.data[i] == v = true by transitivity with beq_symm
    have h_av : (s.data[i] == v) = true := varid_beq_trans haw (varid_beq_symm hvw)
    -- but hne_v: s.data[i] != v = true, i.e. !(s.data[i] == v) = true
    simp [bne] at hne_v
    rw [h_av] at hne_v; exact Bool.noConfusion hne_v

-- Local helper: erase is monotone
private theorem erase_mono {s₁ s₂ : Moist.MIR.VarSet} {v : VarId}
    (hmono : ∀ w, s₁.contains w = true → s₂.contains w = true)
    (w : VarId) (h : (s₁.erase v).contains w = true) :
    (s₂.erase v).contains w = true := by
  have hw : s₁.contains w = true := contains_of_contains_erase h
  have hne : (v == w) = false := by
    cases hvw : (v == w) with
    | false => rfl
    | true =>
      rw [erase_contains_beq_false s₁ v w hvw] at h
      exact Bool.noConfusion h
  exact Moist.MIR.VarSet.contains_erase_ne s₂ v w hne (hmono w hw)

-- Local helper: union is monotone
private theorem union_mono {s₁ s₂ t₁ t₂ : Moist.MIR.VarSet}
    (h₁ : ∀ w, s₁.contains w = true → t₁.contains w = true)
    (h₂ : ∀ w, s₂.contains w = true → t₂.contains w = true)
    (w : VarId) (h : (s₁.union s₂).contains w = true) :
    (t₁.union t₂).contains w = true := by
  rcases contains_union_elim h with h | h
  · exact contains_union_left _ _ _ (h₁ w h)
  · exact contains_union_right _ _ _ (h₂ w h)

--------------------------------------------------------------------------------
-- freeVars(rename old new e) ⊆ (freeVars e \ {old}) ∪ {new}
-- Auxiliary: w ∈ freeVars e → (old == w) = false → w ∈ (freeVars e).erase old
--------------------------------------------------------------------------------

private theorem erase_contains_ne_of_contains {s : Moist.MIR.VarSet} {v w : VarId}
    (h : s.contains w = true) (hne : (v == w) = false) : (s.erase v).contains w = true :=
  Moist.MIR.VarSet.contains_erase_ne s v w hne h

mutual
private theorem freeVars_rename_bound_core (old new_ : VarId) (e : Expr) (w : VarId)
    (hw : (freeVars (rename old new_ e)).contains w = true) :
    ((freeVars e).erase old).contains w = true ∨ (w == new_) = true := by
  match e with
  | .Var x =>
    have h_ren : rename old new_ (.Var x) = if x == old then .Var new_ else .Var x := by
      simp only [rename]
    rw [h_ren] at hw
    split at hw
    · -- x == old: result = .Var new_
      rw [Moist.MIR.freeVars.eq_1, Moist.MIR.VarSet.singleton_contains'] at hw
      exact Or.inr (varid_beq_symm hw)
    · -- x != old: result = .Var x
      rename_i hxo
      rw [Moist.MIR.freeVars.eq_1, Moist.MIR.VarSet.singleton_contains'] at hw
      have hne_ow : (old == w) = false := by
        cases h : (old == w); rfl
        exact absurd (varid_beq_trans hw (varid_beq_symm h)) hxo
      exact Or.inl (erase_contains_ne_of_contains
        (by rw [Moist.MIR.freeVars.eq_1, Moist.MIR.VarSet.singleton_contains']; exact hw) hne_ow)
  | .Lit _ | .Builtin _ | .Error =>
    simp only [rename, freeVars] at hw
    exact absurd hw (by simp [Moist.MIR.VarSet.contains_empty])
  | .Lam x body =>
    have h_ren : rename old new_ (.Lam x body) =
        if x == old then .Lam x body else .Lam x (rename old new_ body) := by
      simp only [rename]
    rw [h_ren] at hw
    split at hw
    · -- x == old: body untouched
      rename_i hxo
      -- hw : (freeVars (.Lam x body)).contains w = true
      -- = ((freeVars body).erase x).contains w = true
      -- Need: ((freeVars body).erase x).erase old .contains w
      -- Since x == old, erase x already does what erase old would do
      rw [Moist.MIR.freeVars.eq_5] at hw ⊢
      have hne : (old == w) = false := by
        cases h' : (old == w); rfl
        rw [erase_contains_beq_false _ x w (varid_beq_trans hxo h')] at hw
        exact Bool.noConfusion hw
      exact Or.inl (erase_contains_ne_of_contains hw hne)
    · -- x != old
      rw [Moist.MIR.freeVars.eq_5] at hw ⊢
      have hw_body := contains_of_contains_erase hw
      have hne_xw : (x == w) = false := by
        cases h : (x == w); rfl
        rw [erase_contains_beq_false _ x w h] at hw; exact Bool.noConfusion hw
      rcases freeVars_rename_bound_core old new_ body w hw_body with h | h
      · -- h : ((freeVars body).erase old).contains w = true
        -- Need: ((freeVars body).erase x).erase old .contains w
        -- From h: (freeVars body).contains w and (old == w) = false
        have hne_ow : (old == w) = false := by
          cases h' : (old == w); rfl
          rw [erase_contains_beq_false _ old w h'] at h; exact Bool.noConfusion h
        exact Or.inl (erase_contains_ne_of_contains
          (erase_contains_ne_of_contains (contains_of_contains_erase h) hne_xw) hne_ow)
      · exact Or.inr h
  | .Fix f body =>
    have h_ren : rename old new_ (.Fix f body) =
        if f == old then .Fix f body else .Fix f (rename old new_ body) := by
      simp only [rename]
    rw [h_ren] at hw
    split at hw
    · rename_i hfo
      rw [Moist.MIR.freeVars.eq_6] at hw ⊢
      have hne : (old == w) = false := by
        cases h' : (old == w); rfl
        rw [erase_contains_beq_false _ f w (varid_beq_trans hfo h')] at hw
        exact Bool.noConfusion hw
      exact Or.inl (erase_contains_ne_of_contains hw hne)
    · rw [Moist.MIR.freeVars.eq_6] at hw ⊢
      have hw_body := contains_of_contains_erase hw
      have hne_fw : (f == w) = false := by
        cases h : (f == w); rfl
        rw [erase_contains_beq_false _ f w h] at hw; exact Bool.noConfusion hw
      rcases freeVars_rename_bound_core old new_ body w hw_body with h | h
      · have hne_ow : (old == w) = false := by
          cases h' : (old == w); rfl
          rw [erase_contains_beq_false _ old w h'] at h; exact Bool.noConfusion h
        exact Or.inl (erase_contains_ne_of_contains
          (erase_contains_ne_of_contains (contains_of_contains_erase h) hne_fw) hne_ow)
      · exact Or.inr h
  | .App f x =>
    have h_ren : rename old new_ (.App f x) =
        .App (rename old new_ f) (rename old new_ x) := by simp only [rename]
    rw [h_ren, Moist.MIR.freeVars.eq_7] at hw; rw [Moist.MIR.freeVars.eq_7]
    rcases contains_union_elim hw with h | h
    · rcases freeVars_rename_bound_core old new_ f w h with h | h
      · exact Or.inl (erase_mono (fun w h => contains_union_left _ _ _ h) w h)
      · exact Or.inr h
    · rcases freeVars_rename_bound_core old new_ x w h with h | h
      · exact Or.inl (erase_mono (fun w h => contains_union_right _ _ _ h) w h)
      · exact Or.inr h
  | .Force e' =>
    have h_ren : rename old new_ (.Force e') = .Force (rename old new_ e') := by
      simp only [rename]
    rw [h_ren, Moist.MIR.freeVars.eq_8] at hw; rw [Moist.MIR.freeVars.eq_8]
    exact freeVars_rename_bound_core old new_ e' w hw
  | .Delay e' =>
    have h_ren : rename old new_ (.Delay e') = .Delay (rename old new_ e') := by
      simp only [rename]
    rw [h_ren, Moist.MIR.freeVars.eq_9] at hw; rw [Moist.MIR.freeVars.eq_9]
    exact freeVars_rename_bound_core old new_ e' w hw
  | .Constr tag args =>
    have h_ren : rename old new_ (.Constr tag args) = .Constr tag (renameList old new_ args) := by
      simp only [rename]
    rw [h_ren, Moist.MIR.freeVars.eq_10] at hw; rw [Moist.MIR.freeVars.eq_10]
    exact freeVarsList_rename_bound_core old new_ args w hw
  | .Case scrut alts =>
    have h_ren : rename old new_ (.Case scrut alts) =
        .Case (rename old new_ scrut) (renameList old new_ alts) := by
      simp only [rename]
    rw [h_ren, Moist.MIR.freeVars.eq_11] at hw; rw [Moist.MIR.freeVars.eq_11]
    rcases contains_union_elim hw with h | h
    · rcases freeVars_rename_bound_core old new_ scrut w h with h | h
      · exact Or.inl (erase_mono (fun w h => contains_union_left _ _ _ h) w h)
      · exact Or.inr h
    · rcases freeVarsList_rename_bound_core old new_ alts w h with h | h
      · exact Or.inl (erase_mono (fun w h => contains_union_right _ _ _ h) w h)
      · exact Or.inr h
  | .Let binds body =>
    rw [show rename old new_ (.Let binds body) =
        .Let (renameLet old new_ binds body).1 (renameLet old new_ binds body).2 from by
      unfold rename; exact Prod.casesOn (renameLet old new_ binds body) (fun _ _ => rfl),
      Moist.MIR.freeVars.eq_12] at hw; rw [Moist.MIR.freeVars.eq_12]
    exact freeVarsLet_rename_bound_core old new_ binds body w hw
termination_by sizeOf e

private theorem freeVarsList_rename_bound_core (old new_ : VarId) (es : List Expr) (w : VarId)
    (hw : (freeVarsList (renameList old new_ es)).contains w = true) :
    ((freeVarsList es).erase old).contains w = true ∨ (w == new_) = true := by
  match es with
  | [] =>
    have : renameList old new_ [] = [] := by simp only [renameList]
    rw [this, Moist.MIR.freeVarsList.eq_1] at hw
    exact absurd hw (by simp [Moist.MIR.VarSet.contains_empty])
  | e :: rest =>
    have h_ren : renameList old new_ (e :: rest) =
        rename old new_ e :: renameList old new_ rest := by simp only [renameList]
    rw [h_ren, Moist.MIR.freeVarsList.eq_2] at hw; rw [Moist.MIR.freeVarsList.eq_2]
    rcases contains_union_elim hw with h | h
    · rcases freeVars_rename_bound_core old new_ e w h with h | h
      · exact Or.inl (erase_mono (fun w h => contains_union_left _ _ _ h) w h)
      · exact Or.inr h
    · rcases freeVarsList_rename_bound_core old new_ rest w h with h | h
      · exact Or.inl (erase_mono (fun w h => contains_union_right _ _ _ h) w h)
      · exact Or.inr h
termination_by sizeOf es

private theorem freeVarsLet_rename_bound_core (old new_ : VarId)
    (binds : List (VarId × Expr × Bool)) (body : Expr) (w : VarId)
    (hw : (freeVarsLet (renameLet old new_ binds body).1
                       (renameLet old new_ binds body).2).contains w = true) :
    ((freeVarsLet binds body).erase old).contains w = true ∨ (w == new_) = true := by
  match binds with
  | [] =>
    have : renameLet old new_ [] body = ([], rename old new_ body) := by simp only [renameLet]
    rw [show (renameLet old new_ [] body).1 = [] from congrArg Prod.fst this,
        show (renameLet old new_ [] body).2 = rename old new_ body from congrArg Prod.snd this] at hw
    rw [Moist.MIR.freeVarsLet.eq_1] at hw ⊢
    exact freeVars_rename_bound_core old new_ body w hw
  | (x, rhs, er) :: rest =>
    by_cases hxo : (x == old) = true
    · -- x == old: rename stops
      have h_rl : (renameLet old new_ ((x, rhs, er) :: rest) body).1 =
          (x, rename old new_ rhs, er) :: rest := by
        simp only [renameLet, hxo, if_true]
      have h_rl2 : (renameLet old new_ ((x, rhs, er) :: rest) body).2 = body := by
        simp only [renameLet, hxo, if_true]
      rw [h_rl, h_rl2] at hw
      rw [Moist.MIR.freeVarsLet.eq_2] at hw ⊢
      rcases contains_union_elim hw with h | h
      · rcases freeVars_rename_bound_core old new_ rhs w h with h | h
        · exact Or.inl (erase_mono (fun w h => contains_union_left _ _ _ h) w h)
        · exact Or.inr h
      · -- w ∈ (freeVarsLet rest body).erase x, and x == old
        have hne : (old == w) = false := by
          cases h' : (old == w); rfl
          rw [erase_contains_beq_false _ x w (varid_beq_trans hxo h')] at h
          exact Bool.noConfusion h
        exact Or.inl (erase_contains_ne_of_contains (contains_union_right _ _ _ h) hne)
    · -- x != old
      have hne_xo : (x == old) = false := by
        cases h : (x == old); rfl; exact absurd h hxo
      have h_rl : (renameLet old new_ ((x, rhs, er) :: rest) body).1 =
          (x, rename old new_ rhs, er) :: (renameLet old new_ rest body).1 := by
        simp only [renameLet, hne_xo]; rfl
      have h_rl2 : (renameLet old new_ ((x, rhs, er) :: rest) body).2 =
          (renameLet old new_ rest body).2 := by
        simp only [renameLet, hne_xo]; rfl
      rw [h_rl, h_rl2] at hw
      rw [Moist.MIR.freeVarsLet.eq_2] at hw ⊢
      rcases contains_union_elim hw with h | h
      · rcases freeVars_rename_bound_core old new_ rhs w h with h | h
        · exact Or.inl (erase_mono (fun w h => contains_union_left _ _ _ h) w h)
        · exact Or.inr h
      · have hw_inner := contains_of_contains_erase h
        have hne_xw : (x == w) = false := by
          cases h' : (x == w); rfl
          rw [erase_contains_beq_false _ x w h'] at h; exact Bool.noConfusion h
        rcases freeVarsLet_rename_bound_core old new_ rest body w hw_inner with h' | h'
        · exact Or.inl (erase_contains_ne_of_contains
            (contains_union_right _ _ _ (erase_contains_ne_of_contains
              (contains_of_contains_erase h') hne_xw))
            (by cases h'' : (old == w); rfl
                rw [erase_contains_beq_false _ old w h''] at h'; exact Bool.noConfusion h'))
        · exact Or.inr h'
termination_by sizeOf binds + sizeOf body
end

--------------------------------------------------------------------------------
-- freeVars(renameBinds old new bs) + freeVars(rename old new body) bound
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Free variables of subst are bounded by (freeVars e \ {v}) ∪ freeVars rhs.
--------------------------------------------------------------------------------

mutual
theorem freeVars_subst_tight (v : VarId) (rhs e : Expr)
    (s : Moist.MIR.FreshState) (w : VarId)
    (hw : (freeVars (subst v rhs e s).1).contains w = true) :
    ((freeVars e).erase v).contains w = true ∨ (freeVars rhs).contains w = true := by
  match e with
  | .Var x =>
    simp only [subst, pure, StateT.pure] at hw
    split at hw
    · exact Or.inr hw
    · rename_i hxv
      -- x != v, result = .Var x
      rw [Moist.MIR.freeVars.eq_1, Moist.MIR.VarSet.singleton_contains'] at hw
      have hne_vw : (v == w) = false := by
        cases h : (v == w); rfl
        exact absurd (varid_beq_trans hw (varid_beq_symm h)) hxv
      exact Or.inl (Moist.MIR.VarSet.contains_erase_ne _ v w hne_vw
        (by rw [Moist.MIR.freeVars.eq_1, Moist.MIR.VarSet.singleton_contains']; exact hw))
  | .Lit _ =>
    simp only [subst, pure, StateT.pure, freeVars] at hw
    exact absurd hw (by simp [Moist.MIR.VarSet.contains_empty])
  | .Builtin _ =>
    simp only [subst, pure, StateT.pure, freeVars] at hw
    exact absurd hw (by simp [Moist.MIR.VarSet.contains_empty])
  | .Error =>
    simp only [subst, pure, StateT.pure, freeVars] at hw
    exact absurd hw (by simp [Moist.MIR.VarSet.contains_empty])
  | .Lam x body =>
    by_cases hxv : (x == v) = true
    · -- x == v: identity, result = .Lam x body
      have h_sub : (subst v rhs (.Lam x body) s).1 = .Lam x body := by
        simp only [subst, hxv, if_true, pure, StateT.pure]
      rw [h_sub] at hw; rw [Moist.MIR.freeVars.eq_5] at hw ⊢
      have hne : (v == w) = false := by
        cases h : (v == w); rfl
        rw [erase_contains_beq_false _ x w (varid_beq_trans hxv h)] at hw
        exact Bool.noConfusion hw
      exact Or.inl (erase_contains_ne_of_contains hw hne)
    · have hne_xv : (x == v) = false := by
        cases h : (x == v); rfl; exact absurd h hxv
      by_cases hfv : (freeVars rhs).contains x = true
      · -- alpha-rename case
        have h_sub : (subst v rhs (.Lam x body) s).1 =
            .Lam (freshVar x.hint s).1
              (subst v rhs (rename x (freshVar x.hint s).1 body) (freshVar x.hint s).2).1 := by
          simp only [subst, hne_xv, hfv, if_true, bind, pure]; rfl
        rw [h_sub, Moist.MIR.freeVars.eq_5] at hw; rw [Moist.MIR.freeVars.eq_5]
        have hw_inner := contains_of_contains_erase hw
        have hne_x'w : ((freshVar x.hint s).1 == w) = false := by
          cases h : ((freshVar x.hint s).1 == w); rfl
          rw [erase_contains_beq_false _ (freshVar x.hint s).1 w h] at hw
          exact Bool.noConfusion hw
        rcases freeVars_subst_tight v rhs (rename x (freshVar x.hint s).1 body)
            (freshVar x.hint s).2 w hw_inner with h_ren | h_rhs
        · have hw_ren_inner := contains_of_contains_erase h_ren
          have hne_vw : (v == w) = false := by
            cases h : (v == w); rfl
            rw [erase_contains_beq_false _ v w h] at h_ren; exact Bool.noConfusion h_ren
          rcases freeVars_rename_bound_core x (freshVar x.hint s).1 body w hw_ren_inner
              with h_body | h_eq
          · exact Or.inl (erase_contains_ne_of_contains h_body hne_vw)
          · exact absurd (varid_beq_symm h_eq) (by simp [hne_x'w])
        · exact Or.inr h_rhs
      · -- simple case: no alpha-rename
        have hfv_f : (freeVars rhs).contains x = false := by
          cases h : (freeVars rhs).contains x; rfl; exact absurd h hfv
        have h_sub : (subst v rhs (.Lam x body) s).1 =
            .Lam x (subst v rhs body s).1 := by
          simp only [subst, hne_xv, hfv_f, bind, pure]; rfl
        rw [h_sub, Moist.MIR.freeVars.eq_5] at hw; rw [Moist.MIR.freeVars.eq_5]
        have hw_inner := contains_of_contains_erase hw
        have hne_xw : (x == w) = false := by
          cases h : (x == w); rfl
          rw [erase_contains_beq_false _ x w h] at hw; exact Bool.noConfusion hw
        rcases freeVars_subst_tight v rhs body _ w hw_inner with h | h
        · have hne_vw : (v == w) = false := by
            cases h' : (v == w); rfl
            rw [erase_contains_beq_false _ v w h'] at h; exact Bool.noConfusion h
          exact Or.inl (erase_contains_ne_of_contains
            (erase_contains_ne_of_contains (contains_of_contains_erase h) hne_xw) hne_vw)
        · exact Or.inr h
  | .Fix f body =>
    by_cases hfv : (f == v) = true
    · -- f == v: identity
      have h_sub : (subst v rhs (.Fix f body) s).1 = .Fix f body := by
        simp only [subst, hfv, if_true, pure, StateT.pure]
      rw [h_sub, Moist.MIR.freeVars.eq_6] at hw; rw [Moist.MIR.freeVars.eq_6]
      have hne : (v == w) = false := by
        cases h : (v == w); rfl
        rw [erase_contains_beq_false _ f w (varid_beq_trans hfv h)] at hw
        exact Bool.noConfusion hw
      exact Or.inl (erase_contains_ne_of_contains hw hne)
    · have hne_fv : (f == v) = false := by
        cases h : (f == v); rfl; exact absurd h hfv
      by_cases hfv_rhs : (freeVars rhs).contains f = true
      · -- alpha-rename case
        have h_sub : (subst v rhs (.Fix f body) s).1 =
            .Fix (freshVar f.hint s).1
              (subst v rhs (rename f (freshVar f.hint s).1 body) (freshVar f.hint s).2).1 := by
          simp only [subst, hne_fv, hfv_rhs, if_true, bind, pure]; rfl
        rw [h_sub, Moist.MIR.freeVars.eq_6] at hw; rw [Moist.MIR.freeVars.eq_6]
        have hw_inner := contains_of_contains_erase hw
        have hne_f'w : ((freshVar f.hint s).1 == w) = false := by
          cases h : ((freshVar f.hint s).1 == w); rfl
          rw [erase_contains_beq_false _ (freshVar f.hint s).1 w h] at hw
          exact Bool.noConfusion hw
        rcases freeVars_subst_tight v rhs (rename f (freshVar f.hint s).1 body)
            (freshVar f.hint s).2 w hw_inner with h_ren | h_rhs
        · have hw_ren_inner := contains_of_contains_erase h_ren
          have hne_vw : (v == w) = false := by
            cases h : (v == w); rfl
            rw [erase_contains_beq_false _ v w h] at h_ren; exact Bool.noConfusion h_ren
          rcases freeVars_rename_bound_core f (freshVar f.hint s).1 body w hw_ren_inner
              with h_body | h_eq
          · exact Or.inl (erase_contains_ne_of_contains h_body hne_vw)
          · exact absurd (varid_beq_symm h_eq) (by simp [hne_f'w])
        · exact Or.inr h_rhs
      · -- simple case
        have hfv_f : (freeVars rhs).contains f = false := by
          cases h : (freeVars rhs).contains f; rfl; exact absurd h hfv_rhs
        have h_sub : (subst v rhs (.Fix f body) s).1 =
            .Fix f (subst v rhs body s).1 := by
          simp only [subst, hne_fv, hfv_f, bind, pure]; rfl
        rw [h_sub, Moist.MIR.freeVars.eq_6] at hw; rw [Moist.MIR.freeVars.eq_6]
        have hw_inner := contains_of_contains_erase hw
        have hne_fw : (f == w) = false := by
          cases h : (f == w); rfl
          rw [erase_contains_beq_false _ f w h] at hw; exact Bool.noConfusion hw
        rcases freeVars_subst_tight v rhs body _ w hw_inner with h | h
        · have hne_vw : (v == w) = false := by
            cases h' : (v == w); rfl
            rw [erase_contains_beq_false _ v w h'] at h; exact Bool.noConfusion h
          exact Or.inl (erase_contains_ne_of_contains
            (erase_contains_ne_of_contains (contains_of_contains_erase h) hne_fw) hne_vw)
        · exact Or.inr h
  | .App f x =>
    have h_sub : (subst v rhs (.App f x) s).1 =
        .App (subst v rhs f s).1 (subst v rhs x (subst v rhs f s).2).1 := by
      simp only [subst, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub] at hw; simp only [freeVars] at hw ⊢
    rcases contains_union_elim hw with h | h
    · rcases freeVars_subst_tight v rhs f s w h with h | h
      · exact Or.inl (erase_mono (fun w h => contains_union_left _ _ _ h) w h)
      · exact Or.inr h
    · rcases freeVars_subst_tight v rhs x _ w h with h | h
      · exact Or.inl (erase_mono (fun w h => contains_union_right _ _ _ h) w h)
      · exact Or.inr h
  | .Force e' =>
    have h_sub : (subst v rhs (.Force e') s).1 = .Force (subst v rhs e' s).1 := by
      simp only [subst, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub] at hw; simp only [freeVars] at hw ⊢
    exact freeVars_subst_tight v rhs e' s w hw
  | .Delay e' =>
    have h_sub : (subst v rhs (.Delay e') s).1 = .Delay (subst v rhs e' s).1 := by
      simp only [subst, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub] at hw; simp only [freeVars] at hw ⊢
    exact freeVars_subst_tight v rhs e' s w hw
  | .Constr tag args =>
    have h_sub : (subst v rhs (.Constr tag args) s).1 =
        .Constr tag (substList v rhs args s).1 := by
      simp only [subst, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub] at hw; simp only [freeVars] at hw ⊢
    exact freeVarsList_substList_tight v rhs args s w hw
  | .Case scrut alts =>
    have h_sub : (subst v rhs (.Case scrut alts) s).1 =
        .Case (subst v rhs scrut s).1 (substList v rhs alts (subst v rhs scrut s).2).1 := by
      simp only [subst, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub] at hw; simp only [freeVars] at hw ⊢
    rcases contains_union_elim hw with h | h
    · rcases freeVars_subst_tight v rhs scrut s w h with h | h
      · exact Or.inl (erase_mono (fun w h => contains_union_left _ _ _ h) w h)
      · exact Or.inr h
    · rcases freeVarsList_substList_tight v rhs alts _ w h with h | h
      · exact Or.inl (erase_mono (fun w h => contains_union_right _ _ _ h) w h)
      · exact Or.inr h
  | .Let binds body =>
    have h_sub : (subst v rhs (.Let binds body) s).1 =
        .Let (substLet v rhs (freeVars rhs) binds body s).1.1
             (substLet v rhs (freeVars rhs) binds body s).1.2 := by
      simp only [subst, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub] at hw; simp only [freeVars] at hw ⊢
    exact freeVarsLet_substLet_tight v rhs binds body s w hw
termination_by e.nodes

private theorem freeVarsList_substList_tight (v : VarId) (rhs : Expr) (es : List Expr)
    (s : Moist.MIR.FreshState) (w : VarId)
    (hw : (freeVarsList (substList v rhs es s).1).contains w = true) :
    ((freeVarsList es).erase v).contains w = true ∨ (freeVars rhs).contains w = true := by
  match es with
  | [] =>
    simp only [substList, pure, StateT.pure, freeVarsList] at hw
    exact absurd hw (by simp [Moist.MIR.VarSet.contains_empty])
  | e :: rest =>
    have h_sub : (substList v rhs (e :: rest) s).1 =
        (subst v rhs e s).1 :: (substList v rhs rest (subst v rhs e s).2).1 := by
      simp only [substList, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub] at hw; simp only [freeVarsList] at hw ⊢
    rcases contains_union_elim hw with h | h
    · rcases freeVars_subst_tight v rhs e s w h with h | h
      · exact Or.inl (erase_mono (fun w h => contains_union_left _ _ _ h) w h)
      · exact Or.inr h
    · rcases freeVarsList_substList_tight v rhs rest _ w h with h | h
      · exact Or.inl (erase_mono (fun w h => contains_union_right _ _ _ h) w h)
      · exact Or.inr h
termination_by Moist.MIR.Expr.nodesList es

private theorem freeVarsLet_substLet_tight (v : VarId) (rhs : Expr)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (s : Moist.MIR.FreshState) (w : VarId)
    (hw : (freeVarsLet (substLet v rhs (freeVars rhs) binds body s).1.1
                       (substLet v rhs (freeVars rhs) binds body s).1.2).contains w = true) :
    ((freeVarsLet binds body).erase v).contains w = true ∨ (freeVars rhs).contains w = true := by
  match binds with
  | [] =>
    have h_form : (substLet v rhs (freeVars rhs) [] body s).1 =
        ([], (subst v rhs body s).1) := by
      simp only [substLet, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [show (substLet v rhs (freeVars rhs) [] body s).1.1 = []
            from congrArg Prod.fst h_form,
        show (substLet v rhs (freeVars rhs) [] body s).1.2 = (subst v rhs body s).1
            from congrArg Prod.snd h_form] at hw
    simp only [freeVarsLet] at hw ⊢
    exact freeVars_subst_tight v rhs body s w hw
  | (x, rhs_h, er) :: rest =>
    by_cases hxv : (x == v) = true
    · have h_form : (substLet v rhs (freeVars rhs) ((x, rhs_h, er) :: rest) body s).1 =
          ((x, (subst v rhs rhs_h s).1, er) :: rest, body) := by
        simp only [substLet, hxv, if_true, bind, StateT.bind, pure, StateT.pure]; rfl
      rw [show (substLet v rhs (freeVars rhs) ((x, rhs_h, er) :: rest) body s).1.1 =
               (x, (subst v rhs rhs_h s).1, er) :: rest from congrArg Prod.fst h_form,
          show (substLet v rhs (freeVars rhs) ((x, rhs_h, er) :: rest) body s).1.2 = body
              from congrArg Prod.snd h_form] at hw
      simp only [freeVarsLet] at hw ⊢
      rcases contains_union_elim hw with h | h
      · rcases freeVars_subst_tight v rhs rhs_h s w h with h | h
        · exact Or.inl (erase_mono (fun w h => contains_union_left _ _ _ h) w h)
        · exact Or.inr h
      · have hne : (v == w) = false := by
          cases h' : (v == w); rfl
          rw [erase_contains_beq_false _ x w (varid_beq_trans hxv h')] at h
          exact Bool.noConfusion h
        exact Or.inl (erase_contains_ne_of_contains (contains_union_right _ _ _ h) hne)
    · have hne : (x == v) = false := by cases h : (x == v); rfl; exact absurd h hxv
      by_cases hfv : (freeVars rhs).contains x = true
      · -- alpha-rename case for Let binder
        -- Abbreviations for the fresh variable and post-state
        -- x' = (freshVar x.hint (subst v rhs rhs_h s).2).1
        -- s1 = (freshVar x.hint (subst v rhs rhs_h s).2).2
        have h_form1 : (substLet v rhs (freeVars rhs) ((x, rhs_h, er) :: rest) body s).1.1 =
            ((freshVar x.hint (subst v rhs rhs_h s).2).1, (subst v rhs rhs_h s).1, er) ::
            (substLet v rhs (freeVars rhs)
              (renameLet x (freshVar x.hint (subst v rhs rhs_h s).2).1 rest body).1
              (renameLet x (freshVar x.hint (subst v rhs rhs_h s).2).1 rest body).2
              (freshVar x.hint (subst v rhs rhs_h s).2).2).1.1 := by
          simp only [substLet, hne, hfv, if_true, bind, pure]; rfl
        have h_form2 : (substLet v rhs (freeVars rhs) ((x, rhs_h, er) :: rest) body s).1.2 =
            (substLet v rhs (freeVars rhs)
              (renameLet x (freshVar x.hint (subst v rhs rhs_h s).2).1 rest body).1
              (renameLet x (freshVar x.hint (subst v rhs rhs_h s).2).1 rest body).2
              (freshVar x.hint (subst v rhs rhs_h s).2).2).1.2 := by
          simp only [substLet, hne, hfv, if_true, bind, pure]; rfl
        rw [h_form1, h_form2, Moist.MIR.freeVarsLet.eq_2] at hw
        rw [Moist.MIR.freeVarsLet.eq_2]
        rcases contains_union_elim hw with h | h
        · rcases freeVars_subst_tight v rhs rhs_h s w h with h | h
          · exact Or.inl (erase_mono (fun w h => contains_union_left _ _ _ h) w h)
          · exact Or.inr h
        · have hw_inner := contains_of_contains_erase h
          have hne_x'w : ((freshVar x.hint (subst v rhs rhs_h s).2).1 == w) = false := by
            cases h' : ((freshVar x.hint (subst v rhs rhs_h s).2).1 == w); rfl
            rw [erase_contains_beq_false _ _ w h'] at h; exact Bool.noConfusion h
          rcases freeVarsLet_substLet_tight v rhs
              (renameLet x (freshVar x.hint (subst v rhs rhs_h s).2).1 rest body).1
              (renameLet x (freshVar x.hint (subst v rhs rhs_h s).2).1 rest body).2
              (freshVar x.hint (subst v rhs rhs_h s).2).2 w hw_inner with h' | h'
          · have hw_rl := contains_of_contains_erase h'
            have hne_vw : (v == w) = false := by
              cases h'' : (v == w); rfl
              rw [erase_contains_beq_false _ v w h''] at h'; exact Bool.noConfusion h'
            rcases freeVarsLet_rename_bound_core x
                (freshVar x.hint (subst v rhs rhs_h s).2).1 rest body w hw_rl with h_orig | h_eq
            · exact Or.inl (erase_contains_ne_of_contains
                (contains_union_right _ _ _ h_orig) hne_vw)
            · exact absurd (varid_beq_symm h_eq) (by simp [hne_x'w])
          · exact Or.inr h'
      · -- simple case
        have hfv_f : (freeVars rhs).contains x = false := by
          cases h : (freeVars rhs).contains x; rfl; exact absurd h hfv
        have h1 : (substLet v rhs (freeVars rhs) ((x, rhs_h, er) :: rest) body s).1.1 =
            (x, (subst v rhs rhs_h s).1, er) ::
            (substLet v rhs (freeVars rhs) rest body (subst v rhs rhs_h s).2).1.1 := by
          simp only [substLet, hne, hfv_f, bind, StateT.bind, pure, StateT.pure,
                     Bool.false_eq_true, ↓reduceIte]; rfl
        have h2 : (substLet v rhs (freeVars rhs) ((x, rhs_h, er) :: rest) body s).1.2 =
            (substLet v rhs (freeVars rhs) rest body (subst v rhs rhs_h s).2).1.2 := by
          simp only [substLet, hne, hfv_f, bind, StateT.bind, pure, StateT.pure,
                     Bool.false_eq_true, ↓reduceIte]; rfl
        rw [h1, h2] at hw
        simp only [freeVarsLet] at hw ⊢
        rcases contains_union_elim hw with h | h
        · rcases freeVars_subst_tight v rhs rhs_h s w h with h | h
          · exact Or.inl (erase_mono (fun w h => contains_union_left _ _ _ h) w h)
          · exact Or.inr h
        · have hw_inner := contains_of_contains_erase h
          have hne_xw : (x == w) = false := by
            cases h' : (x == w); rfl
            rw [erase_contains_beq_false _ x w h'] at h; exact Bool.noConfusion h
          rcases freeVarsLet_substLet_tight v rhs rest body _ w hw_inner with h' | h'
          · have hne_vw : (v == w) = false := by
              cases h'' : (v == w); rfl
              rw [erase_contains_beq_false _ v w h''] at h'; exact Bool.noConfusion h'
            exact Or.inl (erase_contains_ne_of_contains
              (contains_union_right _ _ _ (erase_contains_ne_of_contains
                (contains_of_contains_erase h') hne_xw)) hne_vw)
          · exact Or.inr h'
termination_by Moist.MIR.Expr.nodesBinds binds + body.nodes
end

-- Inlining equations (local copies from InlineSoundness)
private theorem inlinePass_leaf_eq {e : Expr}
    (hlet : ∀ bs b, e ≠ .Let bs b)
    (hlam : ∀ x b, e ≠ .Lam x b)
    (hfix : ∀ f b, e ≠ .Fix f b)
    (happ : ∀ f x, e ≠ .App f x)
    (hforce : ∀ inner, e ≠ .Force inner)
    (hdelay : ∀ inner, e ≠ .Delay inner)
    (hconstr : ∀ t args, e ≠ .Constr t args)
    (hcase : ∀ sc alts, e ≠ .Case sc alts)
    (s : Moist.MIR.FreshState) :
    inlinePass e s = ((e, false), s) := by
  rw [Moist.MIR.inlinePass.eq_9 e
        (fun bs b heq => hlet bs b heq)
        (fun x b heq => hlam x b heq)
        (fun f b heq => hfix f b heq)
        (fun f x heq => happ f x heq)
        (fun inner heq => hforce inner heq)
        (fun inner heq => hdelay inner heq)
        (fun t args heq => hconstr t args heq)
        (fun sc alts heq => hcase sc alts heq)]
  rfl

-- betaReduce freeVars bound
private theorem betaReduce_fv_sub (f' x' : Expr) (s : Moist.MIR.FreshState) (w : VarId)
    (h : (freeVars (Moist.MIR.betaReduce f' x' s).1.1).contains w = true) :
    (freeVars (.App f' x')).contains w = true := by
  unfold Moist.MIR.betaReduce at h
  match f' with
  | .Lam param body =>
    simp only at h
    split at h
    · -- x'.isAtom = true, beta case: result = subst param x' body
      rename_i hatom
      simp only [pure, StateT.pure, bind, StateT.bind] at h
      rcases freeVars_subst_tight param x' body s w h with h_body | h_x'
      · rw [Moist.MIR.freeVars.eq_7]
        have : freeVars (.Lam param body) = (freeVars body).erase param := by
          simp only [freeVars]
        exact contains_union_left _ _ _ (this ▸ h_body)
      · rw [Moist.MIR.freeVars.eq_7]
        exact contains_union_right _ _ _ h_x'
    · -- non-atom case: result = App f' x'
      simp only [pure, StateT.pure] at h; exact h
  | .Var _ | .Lit _ | .Builtin _ | .Error | .Fix _ _ | .App _ _ | .Force _ |
    .Delay _ | .Constr _ _ | .Case _ _ | .Let _ _ =>
    simp only [pure, StateT.pure] at h; exact h

--------------------------------------------------------------------------------
-- Helper: erase commutativity
--------------------------------------------------------------------------------

private theorem erase_erase_comm (s : Moist.MIR.VarSet) (v w x : VarId)
    (h : ((s.erase v).erase w).contains x = true) :
    ((s.erase w).erase v).contains x = true := by
  -- x ∈ s.erase(v).erase(w) means x ∈ s, x != v, x != w
  have hx_s : s.contains x = true := contains_of_contains_erase (contains_of_contains_erase h)
  have hne_wx : (w == x) = false := by
    cases hc : (w == x); rfl
    rw [erase_contains_beq_false _ w x hc] at h; exact Bool.noConfusion h
  have hne_vx : (v == x) = false := by
    have h' := contains_of_contains_erase h
    cases hc : (v == x); rfl
    rw [erase_contains_beq_false _ v x hc] at h'; exact Bool.noConfusion h'
  exact Moist.MIR.VarSet.contains_erase_ne _ v x hne_vx
    (Moist.MIR.VarSet.contains_erase_ne _ w x hne_wx hx_s)

--------------------------------------------------------------------------------
-- Helper: union-erase subset bound
-- (A.erase v ∪ B) contains w → (A ∪ B).erase v contains w ∨ B contains w
-- Actually we just need: if w ∈ A.erase v, then w ∈ (A ∪ C).erase v
--------------------------------------------------------------------------------

private theorem erase_union_left_mono (a c : Moist.MIR.VarSet) (v w : VarId)
    (h : (a.erase v).contains w = true) :
    ((a.union c).erase v).contains w = true := by
  have hne : (v == w) = false := by
    cases hc : (v == w); rfl
    rw [erase_contains_beq_false _ v w hc] at h; exact Bool.noConfusion h
  exact Moist.MIR.VarSet.contains_erase_ne _ v w hne
    (contains_union_left _ _ _ (contains_of_contains_erase h))

private theorem erase_union_right_mono (a c : Moist.MIR.VarSet) (v w : VarId)
    (h : (c.erase v).contains w = true) :
    ((a.union c).erase v).contains w = true := by
  have hne : (v == w) = false := by
    cases hc : (v == w); rfl
    rw [erase_contains_beq_false _ v w hc] at h; exact Bool.noConfusion h
  exact Moist.MIR.VarSet.contains_erase_ne _ v w hne
    (contains_union_right _ _ _ (contains_of_contains_erase h))

--------------------------------------------------------------------------------
-- substInline_freeVarsLet_bound:
-- After inlining v→rhs in rest and body,
-- freeVarsLet rest' body' ⊆ freeVars rhs ∪ (freeVarsLet rest body).erase v
--------------------------------------------------------------------------------

private theorem substInline_freeVarsLet_bound
    (v : VarId) (rhs : Expr) (rest : List (VarId × Expr × Bool))
    (body : Expr) (s_body s_rest : Moist.MIR.FreshState) (w : VarId)
    (hw : (freeVarsLet (substInBindings v rhs rest s_rest).1.val
                       (subst v rhs body s_body).1).contains w = true) :
    ((freeVars rhs).union ((freeVarsLet rest body).erase v)).contains w = true := by
  induction rest generalizing s_rest body s_body with
  | nil =>
    simp only [substInBindings, pure, StateT.pure] at hw
    -- freeVarsLet [] (subst v rhs body s_body).1 = freeVars (subst v rhs body s_body).1
    rw [Moist.MIR.freeVarsLet.eq_1] at hw
    rcases freeVars_subst_tight v rhs body s_body w hw with h | h
    · -- w ∈ (freeVars body).erase v
      rw [Moist.MIR.freeVarsLet.eq_1]
      exact contains_union_right _ _ _ h
    · -- w ∈ freeVars rhs
      exact contains_union_left _ _ _ h
  | cons bd rest_tail ih =>
    obtain ⟨x, e_x, er_x⟩ := bd
    -- Unfold substInBindings: result = (x, (subst v rhs e_x s_rest).1, er_x) :: tail
    have h_form : (substInBindings v rhs ((x, e_x, er_x) :: rest_tail) s_rest).1.val =
        (x, (subst v rhs e_x s_rest).1, er_x) ::
        (substInBindings v rhs rest_tail (subst v rhs e_x s_rest).2).1.val := by
      simp only [substInBindings, bind, StateT.bind]; rfl
    rw [h_form, Moist.MIR.freeVarsLet.eq_2] at hw
    rcases contains_union_elim hw with h_rhs_part | h_inner_part
    · -- w ∈ freeVars (subst v rhs e_x s_rest).1
      rcases freeVars_subst_tight v rhs e_x s_rest w h_rhs_part with h | h
      · -- w ∈ (freeVars e_x).erase v → w ∈ (freeVarsLet rest body).erase v
        rw [Moist.MIR.freeVarsLet.eq_2]
        exact contains_union_right _ _ _
          (erase_union_left_mono _ _ v w h)
      · -- w ∈ freeVars rhs
        exact contains_union_left _ _ _ h
    · -- w ∈ (freeVarsLet rest_tail' body').erase x
      have hw_inner := contains_of_contains_erase h_inner_part
      have hne_xw : (x == w) = false := by
        cases hc : (x == w); rfl
        rw [erase_contains_beq_false _ x w hc] at h_inner_part
        exact Bool.noConfusion h_inner_part
      -- By IH: w ∈ freeVars rhs ∪ (freeVarsLet rest_tail body).erase v
      have ih_result := ih body s_body (subst v rhs e_x s_rest).2 hw_inner
      rcases contains_union_elim ih_result with h | h
      · -- w ∈ freeVars rhs
        exact contains_union_left _ _ _ h
      · -- w ∈ (freeVarsLet rest_tail body).erase v
        -- Need: w ∈ (freeVarsLet (x,e_x,er_x)::rest_tail body).erase v
        -- = ((freeVars e_x).union ((freeVarsLet rest_tail body).erase x)).erase v
        rw [Moist.MIR.freeVarsLet.eq_2]
        exact contains_union_right _ _ _
          (erase_union_right_mono _ _ v w
            (erase_erase_comm _ v x w
              (Moist.MIR.VarSet.contains_erase_ne _ x w hne_xw h)))

--------------------------------------------------------------------------------
-- freeVarsLet_suffix_mono: monotonicity of freeVarsLet in its suffix
-- If freeVarsLet b1 body1 ⊆ freeVarsLet b2 body2,
-- then freeVarsLet (a ++ b1) body1 ⊆ freeVarsLet (a ++ b2) body2
--------------------------------------------------------------------------------

private theorem freeVarsLet_suffix_mono
    (a b1 b2 : List (VarId × Expr × Bool)) (body1 body2 : Expr)
    (h : ∀ w, (freeVarsLet b1 body1).contains w = true →
              (freeVarsLet b2 body2).contains w = true) :
    ∀ w, (freeVarsLet (a ++ b1) body1).contains w = true →
         (freeVarsLet (a ++ b2) body2).contains w = true := by
  induction a with
  | nil => simp only [List.nil_append]; exact h
  | cons bd a_tail ih =>
    obtain ⟨x, rhs_a, er_a⟩ := bd
    intro w hw
    rw [List.cons_append] at hw ⊢
    rw [Moist.MIR.freeVarsLet.eq_2] at hw ⊢
    exact union_mono (fun w h => h) (fun w h => erase_mono ih w h) w hw

--------------------------------------------------------------------------------
-- inlineLetGo_fv_bound:
-- freeVars (inlineLetGo binds acc body changed s).1.1 ⊆
--   freeVarsLet (acc.reverse ++ binds) body
--------------------------------------------------------------------------------

private theorem inlineLetGo_fv_bound
    (binds : List (VarId × Expr × Bool))
    (acc : List (VarId × Expr × Bool))
    (body : Expr) (changed : Bool) (s : Moist.MIR.FreshState) (w : VarId)
    (hw : (freeVars (inlineLetGo binds acc body changed s).1.1).contains w = true) :
    (freeVarsLet (acc.reverse ++ binds) body).contains w = true := by
  match binds with
  | [] =>
    rw [Moist.MIR.inlineLetGo.eq_1] at hw
    simp only [List.append_nil]
    cases hacc : acc.reverse with
    | nil =>
      rw [hacc] at hw; simp only [pure, StateT.pure] at hw
      rw [Moist.MIR.freeVarsLet.eq_1]; exact hw
    | cons s' rest' =>
      rw [hacc] at hw; simp only [pure, StateT.pure] at hw
      rw [Moist.MIR.freeVars.eq_12] at hw; exact hw
  | (v, rhs, er) :: rest =>
    rw [Moist.MIR.inlineLetGo.eq_2] at hw
    simp only [bind, StateT.bind] at hw
    by_cases hinline : (shouldInline rhs
        (countOccurrences v body +
          rest.foldl (fun n (_, e, _) => n + countOccurrences v e) 0)
        (Moist.MIR.occursUnderFix v body ||
          rest.any (fun (_, e, _) => Moist.MIR.occursUnderFix v e))
        (Moist.MIR.occursInDeferred v body ||
          rest.any (fun (_, e, _) => Moist.MIR.occursInDeferred v e) ||
          !Moist.MIR.firstEvaluationUse v (.Let rest body))) = true
    · -- Inline case
      simp only [hinline, ↓reduceIte] at hw
      -- body' = (subst v rhs body s).1
      -- rest' = (substInBindings v rhs rest (subst v rhs body s).2).1.val
      have hdec : (substInBindings v rhs rest (subst v rhs body s).2).1.val.length <
          ((v, rhs, er) :: rest).length := by
        simp only [List.length_cons,
          (substInBindings v rhs rest (subst v rhs body s).2).1.property]; omega
      -- IH: freeVars result ⊆ freeVarsLet (acc.rev ++ rest') body'
      have ih := inlineLetGo_fv_bound
        (substInBindings v rhs rest (subst v rhs body s).2).1.val
        acc
        (subst v rhs body s).1
        true
        (substInBindings v rhs rest (subst v rhs body s).2).2
        w hw
      -- Now chain: acc.rev ++ rest' ⊆ acc.rev ++ (v,rhs,er)::rest
      -- via substInline_freeVarsLet_bound
      apply freeVarsLet_suffix_mono acc.reverse _ _ _ _ _ w ih
      intro w' hw'
      -- Need: freeVarsLet rest' body' ⊆ freeVarsLet ((v,rhs,er)::rest) body
      rw [Moist.MIR.freeVarsLet.eq_2]
      exact substInline_freeVarsLet_bound v rhs rest body s
        (subst v rhs body s).2 w' hw'
    · -- Keep case
      have hinline' : (shouldInline rhs
          (countOccurrences v body +
            rest.foldl (fun n (_, e, _) => n + countOccurrences v e) 0)
          (Moist.MIR.occursUnderFix v body ||
            rest.any (fun (_, e, _) => Moist.MIR.occursUnderFix v e))
          (Moist.MIR.occursInDeferred v body ||
            rest.any (fun (_, e, _) => Moist.MIR.occursInDeferred v e) ||
            !Moist.MIR.firstEvaluationUse v (.Let rest body))) = false := by
        cases h : shouldInline rhs _ _ _ with | true => exact absurd h hinline | false => rfl
      simp only [hinline', Bool.false_eq_true, ↓reduceIte] at hw
      -- IH: freeVars result ⊆ freeVarsLet (((v,rhs,er)::acc).rev ++ rest) body
      have ih := inlineLetGo_fv_bound rest ((v, rhs, er) :: acc) body changed s w hw
      -- ((v,rhs,er)::acc).reverse ++ rest = acc.reverse ++ [(v,rhs,er)] ++ rest
      --   = acc.reverse ++ (v,rhs,er)::rest
      rw [List.reverse_cons, List.append_assoc] at ih
      exact ih
  termination_by binds.length

--------------------------------------------------------------------------------
-- inlineLetBindings_fv_bound: specialization with acc = []
--------------------------------------------------------------------------------

private theorem inlineLetBindings_fv_bound
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (s : Moist.MIR.FreshState) (w : VarId)
    (hw : (freeVars (inlineLetBindings binds body s).1.1).contains w = true) :
    (freeVarsLet binds body).contains w = true := by
  unfold inlineLetBindings at hw
  have := inlineLetGo_fv_bound binds [] body false s w hw
  simpa using this

mutual
theorem freeVars_nonincreasing (e : Expr) (s : Moist.MIR.FreshState) :
    ∀ w, (freeVars (inlinePass e s).1.1).contains w = true →
         (freeVars e).contains w = true := by
  intro w hw
  match e with
  | .Var v =>
    rw [inlinePass_leaf_eq (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)] at hw
    exact hw
  | .Lit c =>
    rw [inlinePass_leaf_eq (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)] at hw
    exact hw
  | .Builtin b =>
    rw [inlinePass_leaf_eq (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)] at hw
    exact hw
  | .Error =>
    rw [inlinePass_leaf_eq (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)] at hw
    exact hw
  | .Lam x body =>
    have heq : (inlinePass (.Lam x body) s).1.1 = .Lam x (inlinePass body s).1.1 := by
      simp only [Moist.MIR.inlinePass.eq_2]; rfl
    rw [heq] at hw; rw [Moist.MIR.freeVars.eq_5] at hw; rw [Moist.MIR.freeVars.eq_5]
    exact erase_mono (freeVars_nonincreasing body s) w hw
  | .Fix f body =>
    have heq : (inlinePass (.Fix f body) s).1.1 = .Fix f (inlinePass body s).1.1 := by
      simp only [Moist.MIR.inlinePass.eq_3]; rfl
    rw [heq] at hw; rw [Moist.MIR.freeVars.eq_6] at hw; rw [Moist.MIR.freeVars.eq_6]
    exact erase_mono (freeVars_nonincreasing body s) w hw
  | .Force inner =>
    have heq : (inlinePass (.Force inner) s).1.1 = .Force (inlinePass inner s).1.1 := by
      simp only [Moist.MIR.inlinePass.eq_5]; rfl
    rw [heq] at hw; rw [Moist.MIR.freeVars.eq_8] at hw; rw [Moist.MIR.freeVars.eq_8]
    exact freeVars_nonincreasing inner s w hw
  | .Delay inner =>
    have heq : (inlinePass (.Delay inner) s).1.1 = .Delay (inlinePass inner s).1.1 := by
      simp only [Moist.MIR.inlinePass.eq_6]; rfl
    rw [heq] at hw; rw [Moist.MIR.freeVars.eq_9] at hw; rw [Moist.MIR.freeVars.eq_9]
    exact freeVars_nonincreasing inner s w hw
  | .Constr tag args =>
    have heq : (inlinePass (.Constr tag args) s).1.1 = .Constr tag (inlinePassList args s).1.1 := by
      simp only [Moist.MIR.inlinePass.eq_7]; rfl
    rw [heq] at hw; rw [Moist.MIR.freeVars.eq_10] at hw; rw [Moist.MIR.freeVars.eq_10]
    exact freeVarsList_nonincreasing args s w hw
  | .Case scrut alts =>
    have heq : (inlinePass (.Case scrut alts) s).1.1 =
      .Case (inlinePass scrut s).1.1
            (inlinePassList alts (inlinePass scrut s).2).1.1 := by
      simp only [Moist.MIR.inlinePass.eq_8]; rfl
    rw [heq] at hw
    rw [Moist.MIR.freeVars.eq_11] at hw
    rw [Moist.MIR.freeVars.eq_11]
    exact union_mono
      (freeVars_nonincreasing scrut s)
      (freeVarsList_nonincreasing alts (inlinePass scrut s).2)
      w hw
  | .App f x =>
    have heq : (inlinePass (.App f x) s).1.1 =
      (Moist.MIR.betaReduce (inlinePass f s).1.1
        (inlinePass x (inlinePass f s).2).1.1
        (inlinePass x (inlinePass f s).2).2).1.1 := by
      simp only [Moist.MIR.inlinePass.eq_4]; rfl
    rw [heq] at hw
    rw [Moist.MIR.freeVars.eq_7]
    have hbeta := betaReduce_fv_sub
      (inlinePass f s).1.1
      (inlinePass x (inlinePass f s).2).1.1
      (inlinePass x (inlinePass f s).2).2
      w hw
    rw [Moist.MIR.freeVars.eq_7] at hbeta
    exact union_mono
      (freeVars_nonincreasing f s)
      (freeVars_nonincreasing x (inlinePass f s).2)
      w hbeta
  | .Let binds body =>
    have heq : (inlinePass (.Let binds body) s).1.1 =
      (Moist.MIR.inlineLetBindings (inlineBindings binds s).1.1
        (inlinePass body (inlineBindings binds s).2).1.1
        (inlinePass body (inlineBindings binds s).2).2).1.1 := by
      simp only [Moist.MIR.inlinePass.eq_1]; rfl
    rw [heq] at hw
    -- Goal: w ∈ freeVars (.Let binds body)
    -- hw: w ∈ freeVars (inlineLetBindings binds' body' s')
    -- Strategy: freeVars result ⊆ freeVarsLet binds' body' ⊆ freeVarsLet binds body
    -- Step 2: freeVarsLet binds' body' ⊆ freeVarsLet binds body
    -- This follows from IH on body + IH on each binding RHS
    have h_body_mono := freeVars_nonincreasing body (inlineBindings binds s).2
    -- Step 1: freeVars (inlineLetBindings ...) ⊆ freeVarsLet binds' body'
    have h_step1 := inlineLetBindings_fv_bound
      (inlineBindings binds s).1.1
      (inlinePass body (inlineBindings binds s).2).1.1
      (inlinePass body (inlineBindings binds s).2).2
      w hw
    -- Step 2: freeVarsLet binds' body' ⊆ freeVarsLet binds body (via mutual IH)
    rw [Moist.MIR.freeVars.eq_12]
    exact inlineBindings_freeVarsLet_mono binds s
      (inlinePass body (inlineBindings binds s).2).1.1 body h_body_mono w h_step1
termination_by sizeOf e

theorem freeVarsList_nonincreasing (es : List Expr) (s : Moist.MIR.FreshState) :
    ∀ w, (freeVarsList (inlinePassList es s).1.1).contains w = true →
         (freeVarsList es).contains w = true := by
  intro w hw
  match es with
  | [] =>
    rw [Moist.MIR.inlinePassList.eq_1] at hw; exact hw
  | e :: rest =>
    have heq : (inlinePassList (e :: rest) s).1.1 =
      (inlinePass e s).1.1 :: (inlinePassList rest (inlinePass e s).2).1.1 := by
      simp only [Moist.MIR.inlinePassList.eq_2]; rfl
    rw [heq] at hw
    rw [Moist.MIR.freeVarsList.eq_2] at hw
    rw [Moist.MIR.freeVarsList.eq_2]
    exact union_mono
      (freeVars_nonincreasing e s)
      (freeVarsList_nonincreasing rest (inlinePass e s).2)
      w hw
termination_by sizeOf es

theorem inlineBindings_freeVarsLet_mono (binds : List (VarId × Expr × Bool))
    (s : Moist.MIR.FreshState) (body' body : Expr)
    (h_body : ∀ w, (freeVars body').contains w = true → (freeVars body).contains w = true) :
    ∀ w, (freeVarsLet (inlineBindings binds s).1.1 body').contains w = true →
         (freeVarsLet binds body).contains w = true := by
  match binds with
  | [] =>
    intro w hw
    have heq : (inlineBindings ([] : List (VarId × Expr × Bool)) s).1.1 = [] := by
      rw [Moist.MIR.inlineBindings.eq_1]; rfl
    rw [heq, Moist.MIR.freeVarsLet.eq_1] at hw
    rw [Moist.MIR.freeVarsLet.eq_1]
    exact h_body w hw
  | (v, rhs, er) :: rest =>
    intro w hw
    have heq : (inlineBindings ((v, rhs, er) :: rest) s).1.1 =
      (v, (inlinePass rhs s).1.1, er) :: (inlineBindings rest (inlinePass rhs s).2).1.1 := by
      simp only [Moist.MIR.inlineBindings.eq_2]; rfl
    rw [heq, Moist.MIR.freeVarsLet.eq_2] at hw
    rw [Moist.MIR.freeVarsLet.eq_2]
    exact union_mono
      (freeVars_nonincreasing rhs s)
      (fun w h => erase_mono
        (inlineBindings_freeVarsLet_mono rest (inlinePass rhs s).2 body' body h_body) w h)
      w hw
termination_by sizeOf binds
end


/-! ## The let-binding decision -/
end Moist.Verified.InlineSoundness.Preservation

namespace Moist.Verified.MIR

/-- The `shouldInline` condition that `inlineLetGo` checks before
    substituting `rhs` for `v` in `body` and `rest`. -/
def InlineGate (v : Moist.MIR.VarId) (rhs body : Moist.MIR.Expr)
    (rest : List (Moist.MIR.VarId × Moist.MIR.Expr × Bool)) : Bool :=
  Moist.MIR.shouldInline rhs
    (Moist.MIR.countOccurrences v body +
      rest.foldl (fun n (_, e, _) => n + Moist.MIR.countOccurrences v e) 0)
    (Moist.MIR.occursUnderFix v body ||
      rest.any (fun (_, e, _) => Moist.MIR.occursUnderFix v e))
    (Moist.MIR.occursInDeferred v body ||
      rest.any (fun (_, e, _) => Moist.MIR.occursInDeferred v e) ||
      !Moist.MIR.firstEvaluationUse v (.Let rest body))

end Moist.Verified.MIR

namespace Moist.Verified.InlineSoundness.Preservation

open Moist.MIR (Expr VarId VarSet freeVars freeVarsList freeVarsLet
  inlinePass inlinePassList inlineBindings inlineLetBindings inlineLetGo
  betaReduce substInBindings subst substList substLet expandFix)
open Moist.MIR (FreshState maxUidExpr maxUidExprList maxUidExprBinds distinctBinders)
open Moist.Verified.MIR (InlineGate)
open Moist.Verified.InlineSoundness.SubstCommute (subst_fresh substInBindings_fresh
  substInBindings_cons_val substInBindings_nil)
open Moist.Verified.InlineSoundness.Rename (maxUid_let_cons maxUid_list_cons)

theorem inlineLetGo_nil (acc : List (VarId × Expr × Bool)) (body : Expr) (changed : Bool)
    (s : FreshState) :
    inlineLetGo [] acc body changed s =
      ((match acc.reverse with | [] => body | kept => .Let kept body, changed), s) := by
  rw [Moist.MIR.inlineLetGo.eq_1]
  generalize acc.reverse = kept
  cases kept <;> rfl

theorem inlineLetGo_cons (v : VarId) (rhs : Expr) (er : Bool)
    (rest acc : List (VarId × Expr × Bool)) (body : Expr) (changed : Bool) (s : FreshState) :
    inlineLetGo ((v, rhs, er) :: rest) acc body changed s =
      if InlineGate v rhs body rest then
        inlineLetGo (substInBindings v rhs rest (subst v rhs body s).2).1.val acc
          (subst v rhs body s).1 true (substInBindings v rhs rest (subst v rhs body s).2).2
      else inlineLetGo rest ((v, rhs, er) :: acc) body changed s := by
  rw [Moist.MIR.inlineLetGo.eq_2]
  unfold InlineGate
  split <;> rfl

/-! ## Equations of the pass -/

section Equations
variable (s : FreshState)

theorem inlinePass_leaf (e : Expr)
    (leaf : match e with | .Var _ | .Lit _ | .Builtin _ | .Error => True | _ => False) :
    inlinePass e s = ((e, false), s) := by
  cases e <;> first | exact leaf.elim | (rw [Moist.MIR.inlinePass.eq_9] <;> first | rfl | (intros; simp_all))

theorem inlinePass_lam (x : VarId) (b : Expr) :
    (inlinePass (.Lam x b) s).1.1 = .Lam x (inlinePass b s).1.1 ∧
      (inlinePass (.Lam x b) s).2 = (inlinePass b s).2 := by
  rw [Moist.MIR.inlinePass.eq_2]; exact ⟨rfl, rfl⟩

theorem inlinePass_fix (f : VarId) (b : Expr) :
    (inlinePass (.Fix f b) s).1.1 = .Fix f (inlinePass b s).1.1 ∧
      (inlinePass (.Fix f b) s).2 = (inlinePass b s).2 := by
  rw [Moist.MIR.inlinePass.eq_3]; exact ⟨rfl, rfl⟩

theorem inlinePass_app (f x : Expr) :
    (inlinePass (.App f x) s).1.1 =
        (betaReduce (inlinePass f s).1.1 (inlinePass x (inlinePass f s).2).1.1
          (inlinePass x (inlinePass f s).2).2).1.1 ∧
      (inlinePass (.App f x) s).2 =
        (betaReduce (inlinePass f s).1.1 (inlinePass x (inlinePass f s).2).1.1
          (inlinePass x (inlinePass f s).2).2).2 := by
  rw [Moist.MIR.inlinePass.eq_4]; exact ⟨rfl, rfl⟩

theorem inlinePass_force (e : Expr) :
    (inlinePass (.Force e) s).1.1 = .Force (inlinePass e s).1.1 ∧
      (inlinePass (.Force e) s).2 = (inlinePass e s).2 := by
  rw [Moist.MIR.inlinePass.eq_5]; exact ⟨rfl, rfl⟩

theorem inlinePass_delay (e : Expr) :
    (inlinePass (.Delay e) s).1.1 = .Delay (inlinePass e s).1.1 ∧
      (inlinePass (.Delay e) s).2 = (inlinePass e s).2 := by
  rw [Moist.MIR.inlinePass.eq_6]; exact ⟨rfl, rfl⟩

theorem inlinePass_constr (tag : Nat) (args : List Expr) :
    (inlinePass (.Constr tag args) s).1.1 = .Constr tag (inlinePassList args s).1.1 ∧
      (inlinePass (.Constr tag args) s).2 = (inlinePassList args s).2 := by
  rw [Moist.MIR.inlinePass.eq_7]; exact ⟨rfl, rfl⟩

theorem inlinePass_case (scrut : Expr) (alts : List Expr) :
    (inlinePass (.Case scrut alts) s).1.1 =
        .Case (inlinePass scrut s).1.1 (inlinePassList alts (inlinePass scrut s).2).1.1 ∧
      (inlinePass (.Case scrut alts) s).2 = (inlinePassList alts (inlinePass scrut s).2).2 := by
  rw [Moist.MIR.inlinePass.eq_8]; exact ⟨rfl, rfl⟩

theorem inlinePass_let (binds : List (VarId × Expr × Bool)) (body : Expr) :
    (inlinePass (.Let binds body) s).1.1 =
        (inlineLetBindings (inlineBindings binds s).1.1 (inlinePass body (inlineBindings binds s).2).1.1
          (inlinePass body (inlineBindings binds s).2).2).1.1 ∧
      (inlinePass (.Let binds body) s).2 =
        (inlineLetBindings (inlineBindings binds s).1.1 (inlinePass body (inlineBindings binds s).2).1.1
          (inlinePass body (inlineBindings binds s).2).2).2 := by
  rw [Moist.MIR.inlinePass.eq_1]; exact ⟨rfl, rfl⟩

theorem inlinePassList_nil : inlinePassList [] s = (([], false), s) := by
  rw [Moist.MIR.inlinePassList.eq_1]; rfl

theorem inlinePassList_cons (e : Expr) (rest : List Expr) :
    (inlinePassList (e :: rest) s).1.1 =
        (inlinePass e s).1.1 :: (inlinePassList rest (inlinePass e s).2).1.1 ∧
      (inlinePassList (e :: rest) s).2 = (inlinePassList rest (inlinePass e s).2).2 := by
  rw [Moist.MIR.inlinePassList.eq_2]; exact ⟨rfl, rfl⟩

theorem inlineBindings_nil : inlineBindings [] s = (([], false), s) := by
  rw [Moist.MIR.inlineBindings.eq_1]; rfl

theorem inlineBindings_cons (v : VarId) (rhs : Expr) (er : Bool) (rest : List (VarId × Expr × Bool)) :
    (inlineBindings ((v, rhs, er) :: rest) s).1.1 =
        (v, (inlinePass rhs s).1.1, er) :: (inlineBindings rest (inlinePass rhs s).2).1.1 ∧
      (inlineBindings ((v, rhs, er) :: rest) s).2 = (inlineBindings rest (inlinePass rhs s).2).2 := by
  rw [Moist.MIR.inlineBindings.eq_2]; exact ⟨rfl, rfl⟩

end Equations

/-! ## Let binders never capture an earlier right-hand side -/

/-- No let binder is free in the right-hand side of an earlier binding. -/
def NamesFresh : List (VarId × Expr × Bool) → Prop
  | [] => True
  | (_, rhs, _) :: rest => (∀ b ∈ rest, (freeVars rhs).contains b.1 = false) ∧ NamesFresh rest

/-- Binders that are distinct and not free in the whole let are fresh for
    every earlier right-hand side. -/
theorem namesFresh_of_distinct : ∀ (binds : List (VarId × Expr × Bool)) (body : Expr),
    distinctBinders binds = true →
    (∀ b ∈ binds, (freeVarsLet binds body).contains b.1 = false) → NamesFresh binds
  | [], _, _, _ => trivial
  | (x, rhs, er) :: rest, body, hd, hfv => by
    simp only [distinctBinders, Bool.and_eq_true, List.all_eq_true] at hd
    have split : ∀ b ∈ rest, (freeVars rhs).contains b.1 = false ∧
        (freeVarsLet rest body).contains b.1 = false := fun b hb => by
      have := hfv b (.tail _ hb)
      rw [Moist.MIR.freeVarsLet.eq_2] at this
      obtain ⟨hr, he⟩ := Moist.MIR.VarSet.union_not_contains' _ _ _ this
      refine ⟨hr, ?_⟩
      rcases Moist.MIR.VarSet.erase_not_contains_imp' _ _ _ he with h | h
      · exact h
      · have := hd.1 b hb
        rw [Moist.Verified.InlineSoundness.Rename.beq_comm] at h
        simp [h] at this
    exact ⟨fun b hb => (split b hb).1, namesFresh_of_distinct rest body hd.2 fun b hb => (split b hb).2⟩

private theorem listRel_mem {R : α → α → Prop} : ∀ {xs ys : List α} {y : α},
    Moist.Verified.Equivalence.ListRel R xs ys → y ∈ ys → ∃ x ∈ xs, R x y
  | [], [], _, _, hy => by cases hy
  | _ :: _, [], _, h, _ => h.elim
  | [], _ :: _, _, h, _ => h.elim
  | x :: xs, y' :: ys, y, ⟨hr, hrest⟩, hy => by
    cases hy with
    | head => exact ⟨x, .head _, hr⟩
    | tail _ hy =>
      obtain ⟨x', hx', h⟩ := listRel_mem hrest hy
      exact ⟨x', .tail _ hx', h⟩

/-- `NamesFresh` survives replacing right-hand sides by ones whose free
    variables are old ones or `extra` names that are no binder. -/
theorem namesFresh_mono (extra : VarId → Prop) : ∀ (binds binds' : List (VarId × Expr × Bool)),
    Moist.Verified.Equivalence.ListRel (fun b b' => b.1 = b'.1 ∧
      ∀ w, (freeVars b'.2.1).contains w = true → (freeVars b.2.1).contains w = true ∨ extra w)
      binds binds' →
    (∀ b ∈ binds, ¬ extra b.1) → NamesFresh binds → NamesFresh binds'
  | [], [], _, _, _ => trivial
  | _ :: _, [], h, _, _ => h.elim
  | [], _ :: _, h, _, _ => h.elim
  | (x, e, er) :: bs, (x', e', er') :: bs', ⟨⟨_, hfv⟩, hrel⟩, hext, ⟨head, tail⟩ => by
    refine ⟨fun c' hc' => ?_, namesFresh_mono extra bs bs' hrel (fun c hc => hext c (.tail _ hc)) tail⟩
    obtain ⟨c, hc, hcname, _⟩ := listRel_mem hrel hc'
    cases h : (freeVars e').contains c'.1
    · rfl
    · rcases hfv _ h with h' | h'
      · rw [← hcname, head c hc] at h'; cases h'
      · exact absurd (hcname ▸ h') (hext c (.tail _ hc))

theorem namesFresh_inlineBindings (binds : List (VarId × Expr × Bool)) (s : FreshState)
    (h : NamesFresh binds) : NamesFresh (inlineBindings binds s).1.1 := by
  refine namesFresh_mono (fun _ => False) binds _ ?_ (fun _ _ h => h) h
  clear h
  induction binds generalizing s with
  | nil => rw [inlineBindings_nil]; trivial
  | cons b rest ih =>
    obtain ⟨v, rhs, er⟩ := b
    rw [(inlineBindings_cons s v rhs er rest).1]
    exact ⟨⟨rfl, fun w hw => .inl (freeVars_nonincreasing rhs s w hw)⟩, ih _⟩

theorem namesFresh_substInBindings (v : VarId) (rhs : Expr) (rest : List (VarId × Expr × Bool))
    (s : FreshState) (names : ∀ b ∈ rest, (freeVars rhs).contains b.1 = false)
    (h : NamesFresh rest) : NamesFresh (substInBindings v rhs rest s).1.val := by
  refine namesFresh_mono (fun w => (freeVars rhs).contains w = true) rest _ ?_
    (fun b hb hc => absurd hc (by simp [names b hb])) h
  clear h
  induction rest generalizing s with
  | nil => rw [substInBindings_nil]; trivial
  | cons b rest ih =>
    obtain ⟨y, e, er⟩ := b
    rw [substInBindings_cons_val]
    refine ⟨⟨rfl, fun w hw => ?_⟩, ih _ fun b hb => names b (.tail _ hb)⟩
    rcases freeVars_subst_tight v rhs e s w hw with h | h
    · exact .inl (contains_of_contains_erase h)
    · exact .inr h

/-! ## Every uid stays below the counter -/

private theorem maxUidBinds_reverse : ∀ (xs : List (VarId × Expr × Bool)),
    maxUidExprBinds xs.reverse ≤ maxUidExprBinds xs
  | [] => Nat.le_refl _
  | (v, rhs, er) :: rest => by
    have := maxUidBinds_reverse rest
    have := Moist.MIR.maxUidExprBinds_append rest.reverse [(v, rhs, er)]
    simp only [List.reverse_cons, maxUidExprBinds] at *; omega

theorem betaReduce_lam (p : VarId) (b x : Expr) (s : FreshState) :
    betaReduce (.Lam p b) x s =
      if x.isAtom then (((subst p x b s).1, true), (subst p x b s).2)
      else ((.App (.Lam p b) x, false), s) := by
  simp only [betaReduce]; split <;> rfl

theorem betaReduce_other (f x : Expr) (s : FreshState) (h : ∀ p b, f ≠ .Lam p b) :
    betaReduce f x s = ((.App f x, false), s) := by
  cases f <;> first | rfl | exact absurd rfl (h _ _)

private theorem betaReduce_fresh (f x : Expr) (s : FreshState) (hf : maxUidExpr f < s.next)
    (hx : maxUidExpr x < s.next) :
    maxUidExpr (betaReduce f x s).1.1 < (betaReduce f x s).2.next ∧
      s.next ≤ (betaReduce f x s).2.next := by
  cases f with
  | Lam p b =>
    rw [betaReduce_lam]
    split
    · simp only [maxUidExpr] at hf
      exact subst_fresh p x b s (by omega) hx
    · simp only [maxUidExpr] at hf ⊢; omega
  | _ => rw [betaReduce_other _ _ _ (by intros; simp)]; simp only [maxUidExpr] at hf ⊢; omega

private theorem inlineLetGo_fresh : ∀ (binds acc : List (VarId × Expr × Bool)) (body : Expr)
    (changed : Bool) (s : FreshState),
    maxUidExpr (.Let binds body) < s.next → maxUidExprBinds acc < s.next →
    maxUidExpr (inlineLetGo binds acc body changed s).1.1 < (inlineLetGo binds acc body changed s).2.next ∧
      s.next ≤ (inlineLetGo binds acc body changed s).2.next
  | [], acc, body, changed, s, fe, fa => by
    rw [inlineLetGo_nil]
    simp only [maxUidExpr, maxUidExprBinds] at fe
    have := maxUidBinds_reverse acc
    generalize acc.reverse = kept at this
    cases kept <;> simp only [maxUidExpr] <;> omega
  | (v, rhs, er) :: rest, acc, body, changed, s, fe, fa => by
    rw [maxUid_let_cons] at fe
    simp only [maxUidExpr] at fe
    rw [inlineLetGo_cons]
    split
    · obtain ⟨h₁, s₁⟩ := subst_fresh v rhs body s (by omega) (by omega)
      obtain ⟨h₂, s₂⟩ := substInBindings_fresh v rhs rest (subst v rhs body s).2 (by omega) (by omega)
      have := (substInBindings v rhs rest (subst v rhs body s).2).1.property
      have ih := inlineLetGo_fresh (substInBindings v rhs rest (subst v rhs body s).2).1.val acc
        (subst v rhs body s).1 true (substInBindings v rhs rest (subst v rhs body s).2).2
        (by simp only [maxUidExpr]; omega) (by omega)
      omega
    · have ih := inlineLetGo_fresh rest ((v, rhs, er) :: acc) body changed s
        (by simp only [maxUidExpr]; omega) (by simp only [maxUidExprBinds]; omega)
      exact ih
  termination_by binds => binds.length
  decreasing_by all_goals simp_wf; all_goals omega

mutual
  theorem inlinePass_fresh : ∀ (e : Expr) (s : FreshState), maxUidExpr e < s.next →
      maxUidExpr (inlinePass e s).1.1 < (inlinePass e s).2.next ∧ s.next ≤ (inlinePass e s).2.next
    | .Var _, s, fe | .Lit _, s, fe | .Builtin _, s, fe | .Error, s, fe => by
      rw [inlinePass_leaf s _ trivial]; exact ⟨fe, Nat.le_refl _⟩
    | .Lam x b, s, fe => by
      obtain ⟨h₁, h₂⟩ := inlinePass_lam s x b
      simp only [maxUidExpr] at fe
      have := inlinePass_fresh b s (by omega)
      rw [h₁, h₂]; simp only [maxUidExpr]; omega
    | .Fix f b, s, fe => by
      obtain ⟨h₁, h₂⟩ := inlinePass_fix s f b
      simp only [maxUidExpr] at fe
      have := inlinePass_fresh b s (by omega)
      rw [h₁, h₂]; simp only [maxUidExpr]; omega
    | .App f x, s, fe => by
      obtain ⟨h₁, h₂⟩ := inlinePass_app s f x
      simp only [maxUidExpr] at fe
      have hf := inlinePass_fresh f s (by omega)
      have hx := inlinePass_fresh x (inlinePass f s).2 (by omega)
      have := betaReduce_fresh (inlinePass f s).1.1 (inlinePass x (inlinePass f s).2).1.1
        (inlinePass x (inlinePass f s).2).2 (by omega) hx.1
      rw [h₁, h₂]; omega
    | .Force e, s, fe => by
      obtain ⟨h₁, h₂⟩ := inlinePass_force s e
      simp only [maxUidExpr] at fe
      have := inlinePass_fresh e s fe
      rw [h₁, h₂]; simp only [maxUidExpr]; omega
    | .Delay e, s, fe => by
      obtain ⟨h₁, h₂⟩ := inlinePass_delay s e
      simp only [maxUidExpr] at fe
      have := inlinePass_fresh e s fe
      rw [h₁, h₂]; simp only [maxUidExpr]; omega
    | .Constr tag args, s, fe => by
      obtain ⟨h₁, h₂⟩ := inlinePass_constr s tag args
      simp only [maxUidExpr] at fe
      have := inlinePassList_fresh args s fe
      rw [h₁, h₂]; simp only [maxUidExpr]; omega
    | .Case scrut alts, s, fe => by
      obtain ⟨h₁, h₂⟩ := inlinePass_case s scrut alts
      simp only [maxUidExpr] at fe
      have hs := inlinePass_fresh scrut s (by omega)
      have := inlinePassList_fresh alts (inlinePass scrut s).2 (by omega)
      rw [h₁, h₂]; simp only [maxUidExpr]; omega
    | .Let binds body, s, fe => by
      obtain ⟨h₁, h₂⟩ := inlinePass_let s binds body
      simp only [maxUidExpr] at fe
      have hb := inlineBindings_fresh binds s (by omega)
      have hbody := inlinePass_fresh body (inlineBindings binds s).2 (by omega)
      have := inlineLetGo_fresh (inlineBindings binds s).1.1 [] (inlinePass body (inlineBindings binds s).2).1.1
        false (inlinePass body (inlineBindings binds s).2).2
        (by simp only [maxUidExpr]; omega) (by simp only [maxUidExprBinds]; omega)
      rw [h₁, h₂]; unfold inlineLetBindings; omega
  termination_by e => sizeOf e

  theorem inlinePassList_fresh : ∀ (es : List Expr) (s : FreshState), maxUidExprList es < s.next →
      maxUidExprList (inlinePassList es s).1.1 < (inlinePassList es s).2.next ∧
        s.next ≤ (inlinePassList es s).2.next
    | [], s, fe => by rw [inlinePassList_nil]; exact ⟨fe, Nat.le_refl _⟩
    | e :: rest, s, fe => by
      obtain ⟨h₁, h₂⟩ := inlinePassList_cons s e rest
      rw [maxUid_list_cons] at fe
      have he := inlinePass_fresh e s (by omega)
      have := inlinePassList_fresh rest (inlinePass e s).2 (by omega)
      rw [h₁, h₂, maxUid_list_cons]; omega
  termination_by es => sizeOf es

  theorem inlineBindings_fresh : ∀ (binds : List (VarId × Expr × Bool)) (s : FreshState),
      maxUidExprBinds binds < s.next →
      maxUidExprBinds (inlineBindings binds s).1.1 < (inlineBindings binds s).2.next ∧
        s.next ≤ (inlineBindings binds s).2.next
    | [], s, fe => by rw [inlineBindings_nil]; exact ⟨fe, Nat.le_refl _⟩
    | (v, rhs, er) :: rest, s, fe => by
      obtain ⟨h₁, h₂⟩ := inlineBindings_cons s v rhs er rest
      simp only [maxUidExprBinds] at fe
      have hr := inlinePass_fresh rhs s (by omega)
      have := inlineBindings_fresh rest (inlinePass rhs s).2 (by omega)
      rw [h₁, h₂]; simp only [maxUidExprBinds]; omega
  termination_by binds => sizeOf binds
end

end Moist.Verified.InlineSoundness.Preservation
