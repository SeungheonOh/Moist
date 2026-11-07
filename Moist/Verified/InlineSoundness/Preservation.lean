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
open Moist.MIR (FreshState maxUidExpr maxUidExprList maxUidExprBinds distinctBinders
  rename renameList renameLet)
open Moist.MIR.VarSet (contains_union_left contains_union_right)
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

theorem betaReduce_lam (p : VarId) (b x : Expr) (s : FreshState) :
    betaReduce (.Lam p b) x s =
      if x.isAtom then (((subst p x b s).1, true), (subst p x b s).2)
      else ((.App (.Lam p b) x, false), s) := by
  simp only [betaReduce]; split <;> rfl

theorem betaReduce_other (f x : Expr) (s : FreshState) (h : ∀ p b, f ≠ .Lam p b) :
    betaReduce f x s = ((.App f x, false), s) := by
  cases f <;> first | rfl | exact absurd rfl (h _ _)

--------------------------------------------------------------------------------
-- Free variables
--------------------------------------------------------------------------------

open Moist.Verified.InlineSoundness.Rename (beq_comm beq_false_of_beq)
open Moist.Verified.InlineSoundness.SubstCommute (binderStep binderStepLet binderStepLet_eq
  subst_var subst_lit subst_builtin subst_error subst_app subst_force subst_delay subst_constr
  subst_case subst_let subst_lam subst_lam_shadow subst_fix subst_fix_shadow substList_nil
  substList_cons substLet_nil substLet_shadow substLet_cons substInBindings_nil
  substInBindings_cons_val)

private theorem mem_union {s₁ s₂ : VarSet} {w : VarId} :
    (s₁.union s₂).contains w = true ↔ s₁.contains w = true ∨ s₂.contains w = true := by
  refine ⟨fun h => ?_, fun h => h.elim (contains_union_left _ _ _) (contains_union_right _ _ _)⟩
  cases h₁ : s₁.contains w
  · cases h₂ : s₂.contains w
    · rw [Moist.MIR.VarSet.union_not_contains_fwd s₁ s₂ w h₁ h₂] at h; cases h
    · exact .inr rfl
  · exact .inl rfl

private theorem erase_contains_beq_false (s : VarSet) (v w : VarId) (hvw : (v == w) = true) :
    (s.erase v).contains w = false := by
  cases hcw : (s.erase v).contains w with
  | false => rfl
  | true =>
    simp only [Moist.MIR.VarSet.erase, Moist.MIR.VarSet.contains, Array.any_filter] at hcw
    rw [Array.any_eq_true] at hcw
    obtain ⟨i, _, hprop⟩ := hcw
    rw [Bool.and_eq_true] at hprop
    have h_av : (s.data[i] == v) = true :=
      VarId.beq_trans _ w v hprop.2 (by rw [beq_comm]; exact hvw)
    simp [bne, h_av] at hprop

private theorem mem_erase {s : VarSet} {v w : VarId} :
    (s.erase v).contains w = true ↔ s.contains w = true ∧ (v == w) = false := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => Moist.MIR.VarSet.contains_erase_ne s v w h.2 h.1⟩
  · cases hs : s.contains w
    · rw [Moist.MIR.VarSet.erase_not_contains_fwd s v w hs] at h; cases h
    · rfl
  · cases hvw : (v == w)
    · rfl
    · rw [erase_contains_beq_false s v w hvw] at h; cases h

private theorem mem_var {x w : VarId} : (freeVars (.Var x)).contains w = true ↔ (x == w) = true := by
  rw [Moist.MIR.freeVars.eq_1, Moist.MIR.VarSet.singleton_contains']

mutual
  /-- Renaming `x` to `x'` frees only what was free besides `x`, and `x'`. -/
  theorem fv_rename (x x' : VarId) : ∀ (e : Expr) (w : VarId),
      (freeVars (rename x x' e)).contains w = true →
      ((freeVars e).contains w = true ∧ (x == w) = false) ∨ (x' == w) = true
    | .Var z, w, hw => by
      simp only [rename] at hw
      split at hw
      · exact .inr (mem_var.mp hw)
      · rename_i hzx
        refine .inl ⟨hw, ?_⟩
        rw [beq_comm]
        exact beq_false_of_beq (mem_var.mp hw) (by simpa using hzx)
    | .Lit _, w, hw | .Builtin _, w, hw | .Error, w, hw => by
      simp only [rename] at hw; simp [Moist.MIR.freeVars] at hw
    | .Lam y b, w, hw | .Fix y b, w, hw => by
      simp only [rename] at hw
      first | rw [Moist.MIR.freeVars.eq_5] | rw [Moist.MIR.freeVars.eq_6]
      split at hw
      · rename_i hyx
        first | rw [Moist.MIR.freeVars.eq_5] at hw | rw [Moist.MIR.freeVars.eq_6] at hw
        refine .inl ⟨hw, ?_⟩
        exact beq_false_of_beq hyx (mem_erase.mp hw).2
      · first | rw [Moist.MIR.freeVars.eq_5] at hw | rw [Moist.MIR.freeVars.eq_6] at hw
        obtain ⟨hw, hyw⟩ := mem_erase.mp hw
        rcases fv_rename x x' b w hw with ⟨h, hxw⟩ | h
        · exact .inl ⟨mem_erase.mpr ⟨h, hyw⟩, hxw⟩
        · exact .inr h
    | .App f a, w, hw => by
      simp only [rename, Moist.MIR.freeVars.eq_7, mem_union] at hw ⊢
      rcases hw with hw | hw
      · rcases fv_rename x x' f w hw with ⟨h, h'⟩ | h
        · exact .inl ⟨.inl h, h'⟩
        · exact .inr h
      · rcases fv_rename x x' a w hw with ⟨h, h'⟩ | h
        · exact .inl ⟨.inr h, h'⟩
        · exact .inr h
    | .Force e, w, hw | .Delay e, w, hw => by
      simp only [rename, Moist.MIR.freeVars] at hw ⊢
      exact fv_rename x x' e w hw
    | .Constr _ args, w, hw => by
      simp only [rename, Moist.MIR.freeVars.eq_10] at hw ⊢
      exact fvList_rename x x' args w hw
    | .Case scrut alts, w, hw => by
      simp only [rename, Moist.MIR.freeVars.eq_11, mem_union] at hw ⊢
      rcases hw with hw | hw
      · rcases fv_rename x x' scrut w hw with ⟨h, h'⟩ | h
        · exact .inl ⟨.inl h, h'⟩
        · exact .inr h
      · rcases fvList_rename x x' alts w hw with ⟨h, h'⟩ | h
        · exact .inl ⟨.inr h, h'⟩
        · exact .inr h
    | .Let binds body, w, hw => by
      simp only [rename, Moist.MIR.freeVars.eq_12] at hw ⊢
      exact fvLet_rename x x' binds body w hw
  termination_by e => sizeOf e

  theorem fvList_rename (x x' : VarId) : ∀ (es : List Expr) (w : VarId),
      (freeVarsList (renameList x x' es)).contains w = true →
      ((freeVarsList es).contains w = true ∧ (x == w) = false) ∨ (x' == w) = true
    | [], w, hw => by simp [renameList, Moist.MIR.freeVarsList] at hw
    | e :: es, w, hw => by
      simp only [renameList, Moist.MIR.freeVarsList.eq_2, mem_union] at hw ⊢
      rcases hw with hw | hw
      · rcases fv_rename x x' e w hw with ⟨h, h'⟩ | h
        · exact .inl ⟨.inl h, h'⟩
        · exact .inr h
      · rcases fvList_rename x x' es w hw with ⟨h, h'⟩ | h
        · exact .inl ⟨.inr h, h'⟩
        · exact .inr h
  termination_by es => sizeOf es

  theorem fvLet_rename (x x' : VarId) : ∀ (binds : List (VarId × Expr × Bool)) (body : Expr) (w : VarId),
      (freeVarsLet (renameLet x x' binds body).1 (renameLet x x' binds body).2).contains w = true →
      ((freeVarsLet binds body).contains w = true ∧ (x == w) = false) ∨ (x' == w) = true
    | [], body, w, hw => by
      simp only [renameLet, Moist.MIR.freeVarsLet.eq_1] at hw ⊢
      exact fv_rename x x' body w hw
    | (y, rhs, er) :: rest, body, w, hw => by
      rw [Moist.MIR.freeVarsLet.eq_2, mem_union]
      simp only [renameLet] at hw
      split at hw
      · rename_i hyx
        simp only [Moist.MIR.freeVarsLet.eq_2, mem_union] at hw
        rcases hw with hw | hw
        · rcases fv_rename x x' rhs w hw with ⟨h, h'⟩ | h
          · exact .inl ⟨.inl h, h'⟩
          · exact .inr h
        · refine .inl ⟨.inr hw, ?_⟩
          exact beq_false_of_beq hyx (mem_erase.mp hw).2
      · simp only [Moist.MIR.freeVarsLet.eq_2, mem_union] at hw
        rcases hw with hw | hw
        · rcases fv_rename x x' rhs w hw with ⟨h, h'⟩ | h
          · exact .inl ⟨.inl h, h'⟩
          · exact .inr h
        · obtain ⟨hw, hyw⟩ := mem_erase.mp hw
          rcases fvLet_rename x x' rest body w hw with ⟨h, h'⟩ | h
          · exact .inl ⟨.inr (mem_erase.mpr ⟨h, hyw⟩), h'⟩
          · exact .inr h
  termination_by binds body => sizeOf binds + sizeOf body
end

/-- What a binder step keeps free: names other than the new binder were free
    under the old one. -/
private theorem binderStep_fv (repl : Expr) (x : VarId) (b : Expr) (s : FreshState) (w : VarId)
    (hw : (freeVars (binderStep repl x b s).2.1).contains w = true)
    (hne : ((binderStep repl x b s).1 == w) = false) :
    (freeVars b).contains w = true ∧ (x == w) = false := by
  unfold binderStep at hw hne
  split at hw <;> rename_i h <;> simp only [h, ↓reduceIte] at hne
  · rcases fv_rename x _ b w hw with h' | h'
    · exact h'
    · rw [h'] at hne; cases hne
  · exact ⟨hw, hne⟩

mutual
  /-- Substitution frees only what was free besides `v`, and the replacement's. -/
  theorem freeVars_subst_tight (v : VarId) (r : Expr) : ∀ (e : Expr) (s : FreshState) (w : VarId),
      (freeVars (subst v r e s).1).contains w = true →
      ((freeVars e).contains w = true ∧ (v == w) = false) ∨ (freeVars r).contains w = true
    | .Var x, s, w, hw => by
      rw [subst_var] at hw
      split at hw
      · exact .inr hw
      · rename_i hxv
        refine .inl ⟨hw, ?_⟩
        rw [beq_comm]
        exact beq_false_of_beq (mem_var.mp hw) (by simpa using hxv)
    | .Lit _, s, w, hw => by rw [subst_lit] at hw; simp [Moist.MIR.freeVars] at hw
    | .Builtin _, s, w, hw => by rw [subst_builtin] at hw; simp [Moist.MIR.freeVars] at hw
    | .Error, s, w, hw => by rw [subst_error] at hw; simp [Moist.MIR.freeVars] at hw
    | .Lam x b, s, w, hw => by
      rw [Moist.MIR.freeVars.eq_5]
      cases hxv : (x == v)
      · rw [subst_lam v r s x b hxv, Moist.MIR.freeVars.eq_5] at hw
        obtain ⟨hw, hxw⟩ := mem_erase.mp hw
        rcases freeVars_subst_tight v r _ _ w hw with ⟨h, hvw⟩ | h
        · obtain ⟨h, hxw⟩ := binderStep_fv r x b s w h hxw
          exact .inl ⟨mem_erase.mpr ⟨h, hxw⟩, hvw⟩
        · exact .inr h
      · rw [subst_lam_shadow v r s x b hxv, Moist.MIR.freeVars.eq_5] at hw
        refine .inl ⟨hw, ?_⟩
        exact beq_false_of_beq hxv (mem_erase.mp hw).2
    | .Fix x b, s, w, hw => by
      rw [Moist.MIR.freeVars.eq_6]
      cases hxv : (x == v)
      · rw [subst_fix v r s x b hxv, Moist.MIR.freeVars.eq_6] at hw
        obtain ⟨hw, hxw⟩ := mem_erase.mp hw
        rcases freeVars_subst_tight v r _ _ w hw with ⟨h, hvw⟩ | h
        · obtain ⟨h, hxw⟩ := binderStep_fv r x b s w h hxw
          exact .inl ⟨mem_erase.mpr ⟨h, hxw⟩, hvw⟩
        · exact .inr h
      · rw [subst_fix_shadow v r s x b hxv, Moist.MIR.freeVars.eq_6] at hw
        refine .inl ⟨hw, ?_⟩
        exact beq_false_of_beq hxv (mem_erase.mp hw).2
    | .App f a, s, w, hw => by
      rw [subst_app] at hw
      simp only [Moist.MIR.freeVars.eq_7, mem_union] at hw ⊢
      rcases hw with hw | hw
      · rcases freeVars_subst_tight v r f s w hw with ⟨h, h'⟩ | h
        · exact .inl ⟨.inl h, h'⟩
        · exact .inr h
      · rcases freeVars_subst_tight v r a _ w hw with ⟨h, h'⟩ | h
        · exact .inl ⟨.inr h, h'⟩
        · exact .inr h
    | .Force e, s, w, hw => by
      rw [subst_force] at hw; simp only [Moist.MIR.freeVars] at hw ⊢
      exact freeVars_subst_tight v r e s w hw
    | .Delay e, s, w, hw => by
      rw [subst_delay] at hw; simp only [Moist.MIR.freeVars] at hw ⊢
      exact freeVars_subst_tight v r e s w hw
    | .Constr _ args, s, w, hw => by
      rw [subst_constr] at hw; simp only [Moist.MIR.freeVars.eq_10] at hw ⊢
      exact freeVarsList_subst_tight v r args s w hw
    | .Case scrut alts, s, w, hw => by
      rw [subst_case] at hw
      simp only [Moist.MIR.freeVars.eq_11, mem_union] at hw ⊢
      rcases hw with hw | hw
      · rcases freeVars_subst_tight v r scrut s w hw with ⟨h, h'⟩ | h
        · exact .inl ⟨.inl h, h'⟩
        · exact .inr h
      · rcases freeVarsList_subst_tight v r alts _ w hw with ⟨h, h'⟩ | h
        · exact .inl ⟨.inr h, h'⟩
        · exact .inr h
    | .Let binds body, s, w, hw => by
      rw [subst_let] at hw; simp only [Moist.MIR.freeVars.eq_12] at hw ⊢
      exact freeVarsLet_subst_tight v r binds body s w hw
  termination_by e => e.nodes
  decreasing_by all_goals (simp_wf; all_goals first | omega | (simp; done) | (simp; omega))

  theorem freeVarsList_subst_tight (v : VarId) (r : Expr) : ∀ (es : List Expr) (s : FreshState)
      (w : VarId), (freeVarsList (substList v r es s).1).contains w = true →
      ((freeVarsList es).contains w = true ∧ (v == w) = false) ∨ (freeVars r).contains w = true
    | [], s, w, hw => by rw [substList_nil] at hw; simp [Moist.MIR.freeVarsList] at hw
    | e :: es, s, w, hw => by
      rw [substList_cons] at hw
      simp only [Moist.MIR.freeVarsList.eq_2, mem_union] at hw ⊢
      rcases hw with hw | hw
      · rcases freeVars_subst_tight v r e s w hw with ⟨h, h'⟩ | h
        · exact .inl ⟨.inl h, h'⟩
        · exact .inr h
      · rcases freeVarsList_subst_tight v r es _ w hw with ⟨h, h'⟩ | h
        · exact .inl ⟨.inr h, h'⟩
        · exact .inr h
  termination_by es => Expr.nodesList es
  decreasing_by all_goals (simp_wf; all_goals first | omega | (simp; done) | (simp; omega))

  theorem freeVarsLet_subst_tight (v : VarId) (r : Expr) : ∀ (binds : List (VarId × Expr × Bool))
      (body : Expr) (s : FreshState) (w : VarId),
      (freeVarsLet (substLet v r (freeVars r) binds body s).1.1
        (substLet v r (freeVars r) binds body s).1.2).contains w = true →
      ((freeVarsLet binds body).contains w = true ∧ (v == w) = false) ∨ (freeVars r).contains w = true
    | [], body, s, w, hw => by
      rw [substLet_nil] at hw; simp only [Moist.MIR.freeVarsLet.eq_1] at hw ⊢
      exact freeVars_subst_tight v r body s w hw
    | (x, rhs, er) :: rest, body, s, w, hw => by
      rw [Moist.MIR.freeVarsLet.eq_2, mem_union]
      cases hxv : (x == v)
      · rw [substLet_cons v r s x rhs er rest body hxv] at hw
        simp only [Moist.MIR.freeVarsLet.eq_2, mem_union] at hw
        rcases hw with hw | hw
        · rcases freeVars_subst_tight v r rhs s w hw with ⟨h, h'⟩ | h
          · exact .inl ⟨.inl h, h'⟩
          · exact .inr h
        · obtain ⟨hw, hxw⟩ := mem_erase.mp hw
          rcases freeVarsLet_subst_tight v r _ _ _ w hw with ⟨h, hvw⟩ | h
          · have step := binderStep_fv r x (.Let rest body) (subst v r rhs s).2 w
            rw [binderStepLet_eq] at step
            simp only [Moist.MIR.freeVars.eq_12] at step
            obtain ⟨h, hxw⟩ := step h hxw
            exact .inl ⟨.inr (mem_erase.mpr ⟨h, hxw⟩), hvw⟩
          · exact .inr h
      · rw [substLet_shadow v r s x rhs er rest body hxv] at hw
        simp only [Moist.MIR.freeVarsLet.eq_2, mem_union] at hw
        rcases hw with hw | hw
        · rcases freeVars_subst_tight v r rhs s w hw with ⟨h, h'⟩ | h
          · exact .inl ⟨.inl h, h'⟩
          · exact .inr h
        · refine .inl ⟨.inr hw, ?_⟩
          exact beq_false_of_beq hxv (mem_erase.mp hw).2
  termination_by binds body => Expr.nodesBinds binds + body.nodes
  decreasing_by all_goals (simp_wf; all_goals first | omega | (simp; done) | (simp; omega))
end

/-- Substituting into the remaining bindings and the body of a let frees
    only the replacement's variables and what the let after `v` frees. -/
private theorem freeVars_substInBindings (v : VarId) (r body : Expr) (sb : FreshState) :
    ∀ (rest : List (VarId × Expr × Bool)) (s : FreshState) (w : VarId),
      (freeVarsLet (substInBindings v r rest s).1.val (subst v r body sb).1).contains w = true →
      (freeVars r).contains w = true ∨ ((freeVarsLet rest body).contains w = true ∧ (v == w) = false)
  | [], s, w, hw => by
    rw [substInBindings_nil] at hw; simp only [Moist.MIR.freeVarsLet.eq_1] at hw ⊢
    exact (freeVars_subst_tight v r body sb w hw).symm
  | (y, e, er) :: rest, s, w, hw => by
    rw [substInBindings_cons_val] at hw
    simp only [Moist.MIR.freeVarsLet.eq_2, mem_union] at hw ⊢
    rcases hw with hw | hw
    · rcases freeVars_subst_tight v r e s w hw with ⟨h, h'⟩ | h
      · exact .inr ⟨.inl h, h'⟩
      · exact .inl h
    · obtain ⟨hw, hyw⟩ := mem_erase.mp hw
      rcases freeVars_substInBindings v r body sb rest _ w hw with h | ⟨h, h'⟩
      · exact .inl h
      · exact .inr ⟨.inr (mem_erase.mpr ⟨h, hyw⟩), h'⟩

private theorem freeVarsLet_append_mono (A : List (VarId × Expr × Bool)) {B C : List (VarId × Expr × Bool)}
    {b c : Expr} (h : ∀ w, (freeVarsLet B b).contains w = true → (freeVarsLet C c).contains w = true)
    (w : VarId) (hw : (freeVarsLet (A ++ B) b).contains w = true) :
    (freeVarsLet (A ++ C) c).contains w = true := by
  induction A generalizing w with
  | nil => exact h w hw
  | cons a A ih =>
    obtain ⟨y, e, er⟩ := a
    simp only [List.cons_append, Moist.MIR.freeVarsLet.eq_2, mem_union, mem_erase] at hw ⊢
    exact hw.imp id fun ⟨hw, hyw⟩ => ⟨ih w hw, hyw⟩

private theorem freeVars_inlineLetGo : ∀ (binds acc : List (VarId × Expr × Bool)) (body : Expr)
    (changed : Bool) (s : FreshState) (w : VarId),
    (freeVars (inlineLetGo binds acc body changed s).1.1).contains w = true →
    (freeVarsLet (acc.reverse ++ binds) body).contains w = true
  | [], acc, body, changed, s, w, hw => by
    rw [inlineLetGo_nil] at hw
    simp only [List.append_nil]
    generalize acc.reverse = kept at hw ⊢
    cases kept with
    | nil => simpa [Moist.MIR.freeVarsLet.eq_1] using hw
    | cons _ _ => simpa [Moist.MIR.freeVars.eq_12] using hw
  | (v, rhs, er) :: rest, acc, body, changed, s, w, hw => by
    rw [inlineLetGo_cons] at hw
    split at hw
    · have := (substInBindings v rhs rest (subst v rhs body s).2).1.property
      refine freeVarsLet_append_mono acc.reverse (fun w hw => ?_) w
        (freeVars_inlineLetGo _ acc _ true _ w hw)
      rw [Moist.MIR.freeVarsLet.eq_2, mem_union, mem_erase]
      rcases freeVars_substInBindings v rhs body s rest _ w hw with h | ⟨h, h'⟩
      · exact .inl h
      · exact .inr ⟨h, h'⟩
    · have := freeVars_inlineLetGo rest ((v, rhs, er) :: acc) body changed s w hw
      rwa [List.reverse_cons, List.append_assoc, List.singleton_append] at this
  termination_by binds => binds.length
  decreasing_by all_goals simp_wf; all_goals omega

private theorem freeVars_betaReduce (f x : Expr) (s : FreshState) (w : VarId)
    (hw : (freeVars (betaReduce f x s).1.1).contains w = true) :
    (freeVars (.App f x)).contains w = true := by
  cases f with
  | Lam p b =>
    rw [betaReduce_lam] at hw
    split at hw
    · simp only [Moist.MIR.freeVars.eq_7, Moist.MIR.freeVars.eq_5, mem_union, mem_erase]
      rcases freeVars_subst_tight p x b s w hw with ⟨h, h'⟩ | h
      · exact .inl ⟨h, h'⟩
      · exact .inr h
    · exact hw
  | _ => rwa [betaReduce_other _ _ _ (by intros; simp)] at hw

/-- `freeVarsLet` grows with the free variables of its parts. -/
private theorem freeVarsLet_mono : ∀ (binds binds' : List (VarId × Expr × Bool)) (body body' : Expr),
    Moist.Verified.Equivalence.ListRel (fun b b' => b.1 = b'.1 ∧
      ∀ w, (freeVars b'.2.1).contains w = true → (freeVars b.2.1).contains w = true) binds binds' →
    (∀ w, (freeVars body').contains w = true → (freeVars body).contains w = true) →
    ∀ w, (freeVarsLet binds' body').contains w = true → (freeVarsLet binds body).contains w = true
  | [], [], _, _, _, hb, w, hw => by simpa [Moist.MIR.freeVarsLet.eq_1] using hb w (by simpa [Moist.MIR.freeVarsLet.eq_1] using hw)
  | _ :: _, [], _, _, h, _, _, _ => h.elim
  | [], _ :: _, _, _, h, _, _, _ => h.elim
  | (x, e, er) :: bs, (x', e', er') :: bs', body, body', ⟨⟨hx, he⟩, hrel⟩, hb, w, hw => by
    simp only at hx
    subst hx
    simp only [Moist.MIR.freeVarsLet.eq_2, mem_union, mem_erase] at hw ⊢
    exact hw.imp (he w) fun ⟨h, h'⟩ => ⟨freeVarsLet_mono bs bs' body body' hrel hb w h, h'⟩

mutual
  /-- The pass never introduces free variables. -/
  theorem freeVars_nonincreasing : ∀ (e : Expr) (s : FreshState) (w : VarId),
      (freeVars (inlinePass e s).1.1).contains w = true → (freeVars e).contains w = true
    | .Var _, s, w, hw | .Lit _, s, w, hw | .Builtin _, s, w, hw | .Error, s, w, hw => by
      rwa [inlinePass_leaf s _ trivial] at hw
    | .Lam x b, s, w, hw => by
      rw [(inlinePass_lam s x b).1] at hw
      simp only [Moist.MIR.freeVars.eq_5, mem_erase] at hw ⊢
      exact ⟨freeVars_nonincreasing b s w hw.1, hw.2⟩
    | .Fix x b, s, w, hw => by
      rw [(inlinePass_fix s x b).1] at hw
      simp only [Moist.MIR.freeVars.eq_6, mem_erase] at hw ⊢
      exact ⟨freeVars_nonincreasing b s w hw.1, hw.2⟩
    | .App f x, s, w, hw => by
      rw [(inlinePass_app s f x).1] at hw
      have := freeVars_betaReduce _ _ _ w hw
      simp only [Moist.MIR.freeVars.eq_7, mem_union] at this ⊢
      exact this.imp (freeVars_nonincreasing f s w) (freeVars_nonincreasing x _ w)
    | .Force e, s, w, hw => by
      rw [(inlinePass_force s e).1] at hw; simp only [Moist.MIR.freeVars] at hw ⊢
      exact freeVars_nonincreasing e s w hw
    | .Delay e, s, w, hw => by
      rw [(inlinePass_delay s e).1] at hw; simp only [Moist.MIR.freeVars] at hw ⊢
      exact freeVars_nonincreasing e s w hw
    | .Constr tag args, s, w, hw => by
      rw [(inlinePass_constr s tag args).1] at hw; simp only [Moist.MIR.freeVars.eq_10] at hw ⊢
      exact freeVarsList_nonincreasing args s w hw
    | .Case scrut alts, s, w, hw => by
      rw [(inlinePass_case s scrut alts).1] at hw
      simp only [Moist.MIR.freeVars.eq_11, mem_union] at hw ⊢
      exact hw.imp (freeVars_nonincreasing scrut s w) (freeVarsList_nonincreasing alts _ w)
    | .Let binds body, s, w, hw => by
      rw [(inlinePass_let s binds body).1] at hw
      unfold inlineLetBindings at hw
      have := freeVars_inlineLetGo _ [] _ false _ w hw
      simp only [List.reverse_nil, List.nil_append] at this
      simp only [Moist.MIR.freeVars.eq_12]
      exact freeVarsLet_mono binds _ body _ (inlineBindings_fv binds s)
        (freeVars_nonincreasing body _) w this
  termination_by e => sizeOf e

  theorem freeVarsList_nonincreasing : ∀ (es : List Expr) (s : FreshState) (w : VarId),
      (freeVarsList (inlinePassList es s).1.1).contains w = true → (freeVarsList es).contains w = true
    | [], s, w, hw => by rwa [inlinePassList_nil] at hw
    | e :: es, s, w, hw => by
      rw [(inlinePassList_cons s e es).1] at hw
      simp only [Moist.MIR.freeVarsList.eq_2, mem_union] at hw ⊢
      exact hw.imp (freeVars_nonincreasing e s w) (freeVarsList_nonincreasing es _ w)
  termination_by es => sizeOf es

  theorem inlineBindings_fv : ∀ (binds : List (VarId × Expr × Bool)) (s : FreshState),
      Moist.Verified.Equivalence.ListRel (fun b b' => b.1 = b'.1 ∧
        ∀ w, (freeVars b'.2.1).contains w = true → (freeVars b.2.1).contains w = true)
        binds (inlineBindings binds s).1.1
    | [], s => by rw [inlineBindings_nil]; trivial
    | (v, rhs, er) :: rest, s => by
      rw [(inlineBindings_cons s v rhs er rest).1]
      exact ⟨⟨rfl, freeVars_nonincreasing rhs s⟩, inlineBindings_fv rest _⟩
  termination_by binds => sizeOf binds
end

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
    · exact .inl h.1
    · exact .inr h

/-! ## Every uid stays below the counter -/

private theorem maxUidBinds_reverse : ∀ (xs : List (VarId × Expr × Bool)),
    maxUidExprBinds xs.reverse ≤ maxUidExprBinds xs
  | [] => Nat.le_refl _
  | (v, rhs, er) :: rest => by
    have := maxUidBinds_reverse rest
    have := Moist.MIR.maxUidExprBinds_append rest.reverse [(v, rhs, er)]
    simp only [List.reverse_cons, maxUidExprBinds] at *; omega

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
