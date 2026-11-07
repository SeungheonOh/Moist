import Moist.Verified.SharingSoundness
import Moist.Verified.MIR.Primitives.Iterated
import Moist.Verified.MIR.AlphaEqBool
import Moist.MIR.Optimize.Advanced.Placement

/-! # Soundness of sharing at the lowest dominating node

`placeShared` applies `shareClosed`'s binding step at the nodes of an arbitrary
plan and recurses into children through congruence, so it refines its input
for every plan (`placeShared_refines`). The binding step only accepts
`isShareable` terms: closed lambdas, delays, lifted Z-combinator fixed points,
literals and builtin states, all of which evaluate to a value without failing
(`isShareable_shareable`). `shareLow` composes three placement rounds below
the parameters of the program (`shareLow_refines`).

Certificates: `placeShared_refines`, `shareLow_refines`. -/

namespace Moist.Verified.Placement

open Moist.MIR Moist.MIR.Advanced
open Moist.Plutus.Term (Term)
open Moist.Verified.Equivalence (ListRel)
open Moist.Verified.MIR (MIRCtxRefines mirCtxRefines_refl mirCtxRefines_trans
  mirCtxRefines_lam mirCtxRefines_delay mirCtxRefines_force mirCtxRefines_app
  mirCtxRefines_case mirCtxRefines_constr_of_listRel mirCtxRefines_let_body
  mirCtxRefines_let_binds_congr lowerTotalExpr_lam lowerTotalExpr_delay lowerTotalExpr_app)
open Moist.Verified.Sharing (Shareable Closed closed_of_isEmpty)
open Moist.Verified.SharedLets (Halts)

/-! ## Shareable terms -/

theorem halts_lam (x : VarId) (body : Expr) :
    ∀ t, lowerTotalExpr [] (.Lam x body) = some t → Halts t := by
  intro t ht ρ
  rw [lowerTotalExpr_lam] at ht
  cases hb : lowerTotalExpr [x] body with
  | none => simp [hb] at ht
  | some tb =>
    simp only [hb, Option.map_some, Option.some.injEq] at ht
    subst ht
    exact ⟨_, 2, rfl⟩

theorem halts_delay (body : Expr) :
    ∀ t, lowerTotalExpr [] (.Delay body) = some t → Halts t := by
  intro t ht ρ
  rw [lowerTotalExpr_delay] at ht
  cases hb : lowerTotalExpr [] body with
  | none => simp [hb] at ht
  | some tb =>
    simp only [hb, Option.map_some, Option.some.injEq] at ht
    subst ht
    exact ⟨_, 2, rfl⟩

theorem beq_symm_true {a b : VarId} (h : (a == b) = true) : (b == a) = true := by
  rw [VarId.beq_true_iff] at h ⊢
  exact ⟨h.1.symm, h.2.symm⟩

/-- The lifted Z combinator `[(λz [z z]) (λs λx. e)]` reaches `λx. e` without
    failing. -/
theorem halts_fixValue {e : Expr} (h : isFixValue e = true) :
    ∀ t, lowerTotalExpr [] e = some t → Halts t := by
  intro t ht ρ
  match e, h with
  | .Let [(z, .Lam s (.Lam x body), er)] (.App (.Var a) (.Var b)), h =>
    simp only [isFixValue, Bool.and_eq_true] at h
    obtain ⟨ha, hb⟩ := h
    rw [Moist.Verified.InlineSoundness.Rename.lowerTotalExpr_let_cons] at ht
    rw [lowerTotalExpr_lam, lowerTotalExpr_lam] at ht
    cases hbody : lowerTotalExpr [x, s] body with
    | none => simp [hbody] at ht
    | some tb =>
      rw [Moist.Verified.InlineSoundness.Rename.lowerTotalExpr_let_nil, lowerTotalExpr_app,
        Moist.Verified.InlineSoundness.Rename.lowerTotalExpr_var,
        Moist.Verified.InlineSoundness.Rename.lowerTotalExpr_var,
        Moist.Verified.MIR.envLookupT_cons_of_beq (beq_symm_true ha),
        Moist.Verified.MIR.envLookupT_cons_of_beq (beq_symm_true hb)] at ht
      simp only [hbody, Option.map_some, Option.bind_eq_bind, Option.bind_some,
        Option.some.injEq] at ht
      subst ht
      exact ⟨_, 12, rfl⟩

theorem isShareable_shareable {c : Expr} (h : isShareable c = true) : Shareable c := by
  simp only [isShareable, Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨hclosed, hkind⟩ := h
  refine ⟨closed_of_isEmpty hclosed, ?_⟩
  rcases hkind with (hvalue | hlit) | hrem
  · cases c with
    | Lam x body => exact halts_lam x body
    | Delay body => exact halts_delay body
    | _ => exact halts_fixValue (by simpa [isValueCandidate] using hvalue)
  · cases c with
    | Lit literal =>
      obtain ⟨constant, type⟩ := literal
      intro t ht ρ
      simp only [lowerTotalExpr, expandFix, lowerTotal, Option.some.injEq] at ht
      subst ht
      exact ⟨_, 2, rfl⟩
    | _ => simp [isLitExpr] at hlit
  · obtain ⟨remaining, hr⟩ := Option.isSome_iff_exists.mp hrem
    intro t ht ρ
    exact Moist.Verified.BuiltinState.builtinRemainder_halts (expandFix c) [] t remaining
      (Moist.Verified.BuiltinState.builtinRemainder_expandFix c remaining hr) ht ρ
      (fun n hn hle => absurd hle (by simp; omega))

/-! ## One binding step -/

theorem shareReplacements_refines (predicate : Expr → Bool) (minimumUses : Nat) (e : Expr)
    (hpred : ∀ c, predicate c = true → Shareable c)
    (hne : (shareReplacements predicate minimumUses e).isEmpty = false) :
    MIRCtxRefines e
      (.Let ((shareReplacements predicate minimumUses e).map fun (rhs, binder) =>
          (binder, rhs, false))
        (replaceMatches (shareReplacements predicate minimumUses e) e)) := by
  have h := Moist.Verified.Sharing.shareClosed_refines predicate minimumUses e hpred
  unfold shareClosed at h
  simp only [hne, Bool.false_eq_true, if_false] at h
  exact h

/-! ## Congruence through the placement traversal -/

theorem mapPeeled_refines (transform : Expr → Expr)
    (sound : ∀ e, MIRCtxRefines e (transform e)) :
    ∀ e, MIRCtxRefines e (mapPeeled transform e)
  | .Lam binder body => by
    simp only [mapPeeled]
    exact mirCtxRefines_lam (mapPeeled_refines transform sound body)
  | .Var _ | .Lit _ | .Builtin _ | .Error | .Fix _ _ | .App _ _ | .Force _ | .Delay _
  | .Constr _ _ | .Case _ _ | .Let _ _ => by
    simp only [mapPeeled]
    exact sound _

theorem listRel_mapIdx (transform : Nat → Expr → Expr)
    (sound : ∀ i e, MIRCtxRefines e (transform i e)) :
    ∀ (es : List Expr), ListRel MIRCtxRefines es (es.mapIdx transform) := by
  intro es
  induction es generalizing transform with
  | nil => trivial
  | cons e rest ih =>
    rw [List.mapIdx_cons]
    exact ⟨sound 0 e, ih (fun i => transform (i + 1)) (fun i => sound (i + 1))⟩

theorem bindsRel_mapIdx (transform : Nat → Expr → Expr)
    (sound : ∀ i e, MIRCtxRefines e (transform i e)) :
    ∀ (bindings : List (VarId × Expr × Bool)),
      ListRel (fun b₁ b₂ => b₁.1 = b₂.1 ∧ b₁.2.2 = b₂.2.2 ∧ MIRCtxRefines b₁.2.1 b₂.2.1)
        bindings (bindings.mapIdx fun index (binder, rhs, erased) =>
          (binder, transform index rhs, erased)) := by
  intro bindings
  induction bindings generalizing transform with
  | nil => trivial
  | cons binding rest ih =>
    obtain ⟨binder, rhs, erased⟩ := binding
    rw [List.mapIdx_cons]
    exact ⟨⟨rfl, rfl, sound 0 rhs⟩, ih (fun i => transform (i + 1)) (fun i => sound (i + 1))⟩

theorem descendPlaced_refines (transform : Nat → Expr → Expr)
    (sound : ∀ i e, MIRCtxRefines e (transform i e)) :
    ∀ e, MIRCtxRefines e (descendPlaced transform e)
  | .Lam _ body => mirCtxRefines_lam (sound 0 body)
  | .Delay inner => mirCtxRefines_delay (sound 0 inner)
  | .App function argument => mirCtxRefines_app (sound 0 function) (sound 1 argument)
  | .Force inner => mirCtxRefines_force (sound 0 inner)
  | .Constr tag fields =>
    mirCtxRefines_constr_of_listRel tag (listRel_mapIdx transform sound fields)
  | .Case scrutinee alternatives =>
    mirCtxRefines_case (sound 0 scrutinee)
      (listRel_mapIdx (fun index => mapPeeled (transform (index + 1)))
        (fun index => mapPeeled_refines _ (sound (index + 1))) alternatives)
  | .Let bindings body =>
    mirCtxRefines_trans
      (mirCtxRefines_let_binds_congr bindings _ body (bindsRel_mapIdx transform sound bindings))
      (mirCtxRefines_let_body (sound bindings.length body))
  | .Var _ | .Lit _ | .Builtin _ | .Error | .Fix _ _ => mirCtxRefines_refl _

/-! ## Placement -/

/-- Binding planned terms at the planned nodes refines, for every plan. -/
theorem placeShared_refines : ∀ (fuel : Nat) (plan : Plan) (e : Expr),
    MIRCtxRefines e (placeShared fuel plan e)
  | 0, _, e => by simp only [placeShared]; exact mirCtxRefines_refl e
  | fuel + 1, plan, e => by
    simp only [placeShared]
    split
    · exact mirCtxRefines_refl e
    · have hpred : ∀ c, (plan.here.any (fun planned => alphaEq planned c) && isShareable c) =
          true → Shareable c := fun c hc => by
        simp only [Bool.and_eq_true] at hc
        exact isShareable_shareable hc.2
      have hdescend : ∀ x, MIRCtxRefines x
          (descendPlaced (fun index => placeShared fuel (plan.child index)) x) :=
        descendPlaced_refines _ (fun index y => placeShared_refines fuel (plan.child index) y)
      by_cases hR : (shareReplacements
          (fun c => plan.here.any (fun planned => alphaEq planned c) && isShareable c) 2 e).isEmpty
      · simp only [hR, if_true]
        exact hdescend e
      · simp only [hR, Bool.false_eq_true, if_false]
        exact mirCtxRefines_trans
          (shareReplacements_refines _ 2 e hpred (by simpa using hR))
          (mirCtxRefines_let_body (hdescend _))

theorem shareChosen_refines (round : ShareRound) (chosen : List Expr) (e : Expr) :
    MIRCtxRefines e (shareChosen round chosen e) :=
  placeShared_refines _ _ e

theorem shareLowBody_refines (options : LowOptions) (e : Expr) :
    MIRCtxRefines e (shareLowBody options e) := by
  unfold shareLowBody
  exact mirCtxRefines_trans (shareChosen_refines _ _ _)
    (mirCtxRefines_trans (shareChosen_refines _ _ _) (shareChosen_refines _ _ _))

/-- **Low sharing refines its input** for every option set. -/
theorem shareLow_refines (options : LowOptions) (e : Expr) :
    MIRCtxRefines e (shareLow options e) :=
  mapPeeled_refines _ (shareLowBody_refines options) e

end Moist.Verified.Placement
