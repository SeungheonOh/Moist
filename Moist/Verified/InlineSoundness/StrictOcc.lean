import Moist.Verified.RenameBase
import Moist.Verified.ClosedAt
import Moist.Verified.FundamentalRefines
import Moist.Verified.Definitions.BudgetExhaustion
import Moist.Verified.BetaValueRefines
import Moist.Verified.StepWellFormed
import Moist.Verified.SubstRefines
import Moist.Verified.InlineSoundness.Beta

/-! # Strict single-occurrence predicates for UPLC terms

Predicates capturing "variable at de Bruijn position `pos` occurs exactly
once, and that occurrence is in a strict (always-evaluated) position."

Strict positions: Apply arguments, Force body, Constr args, Case scrutinee.
Deferred positions: Lam body, Delay body, Case alternatives.

These mirror the MIR-level `countOccurrences == 1 && !occursInDeferred`
conditions from `shouldInline` branch C. -/

namespace Moist.Verified.InlineSoundness.StrictOcc

open Moist.Plutus.Term (Term)
open Moist.Verified (closedAt substTerm substTermList renameTerm renameTermList
  liftRename shiftRename)
open Moist.Verified.FundamentalRefines (Is0Preserving)

/-! ## FreeOf: variable does not occur -/

mutual
  def freeOf (pos : Nat) : Term → Bool
    | .Var n => n != pos
    | .Lam _ body => freeOf (pos + 1) body
    | .Apply f x => freeOf pos f && freeOf pos x
    | .Force e | .Delay e => freeOf pos e
    | .Constr _ args => freeOfList pos args
    | .Case scrut alts => freeOf pos scrut && freeOfList pos alts
    | .Constant _ | .Builtin _ | .Error => true
  termination_by t => sizeOf t

  def freeOfList (pos : Nat) : List Term → Bool
    | [] => true
    | t :: ts => freeOf pos t && freeOfList pos ts
  termination_by ts => sizeOf ts
end

/-! ## StrictSingleOcc: exactly one occurrence in strict position -/

mutual
  inductive StrictSingleOcc : Nat → Term → Prop where
    | var : StrictSingleOcc pos (.Var pos)
    | apply_l : StrictSingleOcc pos f → freeOf pos x = true →
        StrictSingleOcc pos (.Apply f x)
    | apply_r : freeOf pos f = true → StrictSingleOcc pos x →
        StrictSingleOcc pos (.Apply f x)
    | force : StrictSingleOcc pos e → StrictSingleOcc pos (.Force e)
    | constr : StrictSingleOccList pos args →
        StrictSingleOcc pos (.Constr tag args)
    | case_scrut : StrictSingleOcc pos scrut →
        freeOfList pos alts = true →
        StrictSingleOcc pos (.Case scrut alts)
    | let_body : StrictSingleOcc (pos + 1) body → freeOf pos rhs = true →
        StrictSingleOcc pos (.Apply (.Lam 0 body) rhs)

  inductive StrictSingleOccList : Nat → List Term → Prop where
    | head : StrictSingleOcc pos t → freeOfList pos ts = true →
        StrictSingleOccList pos (t :: ts)
    | tail : freeOf pos t = true → StrictSingleOccList pos ts →
        StrictSingleOccList pos (t :: ts)
end

/-! ## SingleOcc: extends StrictSingleOcc with deferred-position constructors -/

mutual
  inductive SingleOcc : Nat → Term → Prop where
    | var : SingleOcc pos (.Var pos)
    | apply_l : SingleOcc pos f → freeOf pos x = true →
        SingleOcc pos (.Apply f x)
    | apply_r : freeOf pos f = true → SingleOcc pos x →
        SingleOcc pos (.Apply f x)
    | force : SingleOcc pos e → SingleOcc pos (.Force e)
    | constr : SingleOccList pos args →
        SingleOcc pos (.Constr tag args)
    | case_scrut : SingleOcc pos scrut →
        freeOfList pos alts = true →
        SingleOcc pos (.Case scrut alts)
    | let_body : SingleOcc (pos + 1) body → freeOf pos rhs = true →
        SingleOcc pos (.Apply (.Lam 0 body) rhs)
    | lam : SingleOcc (pos + 1) body →
        SingleOcc pos (.Lam name body)
    | delay : SingleOcc pos body →
        SingleOcc pos (.Delay body)
    | case_alt : freeOf pos scrut = true →
        SingleOccList pos alts →
        SingleOcc pos (.Case scrut alts)

  inductive SingleOccList : Nat → List Term → Prop where
    | head : SingleOcc pos t → freeOfList pos ts = true →
        SingleOccList pos (t :: ts)
    | tail : freeOf pos t = true → SingleOccList pos ts →
        SingleOccList pos (t :: ts)
end

mutual
theorem StrictSingleOcc.toSingleOcc : StrictSingleOcc pos t → SingleOcc pos t
  | .var => .var
  | .apply_l hf hfree => .apply_l hf.toSingleOcc hfree
  | .apply_r hfree hx => .apply_r hfree hx.toSingleOcc
  | .force he => .force he.toSingleOcc
  | .constr ha => .constr ha.toSingleOccList
  | .case_scrut hs hfree => .case_scrut hs.toSingleOcc hfree
  | .let_body hb hfree => .let_body hb.toSingleOcc hfree

theorem StrictSingleOccList.toSingleOccList : StrictSingleOccList pos ts → SingleOccList pos ts
  | .head ht hfree => .head ht.toSingleOcc hfree
  | .tail hfree hts => .tail hfree hts.toSingleOccList
end

/-! ## UnshiftRename: the renaming that substTerm applies to FreeOf terms

For a FreeOf term, `substTerm pos r t` doesn't insert `r` anywhere —
it just decrements variable indices above `pos`. This matches
`renameTerm (unshiftRename pos) t`. -/

def unshiftRename (pos : Nat) (n : Nat) : Nat :=
  if n > pos then n - 1 else n

theorem unshiftRename_zero (pos : Nat) : unshiftRename pos 0 = 0 := by
  simp [unshiftRename]

theorem unshiftRename_ge1 {pos n : Nat} (hpos : pos ≥ 1) (hn : n ≥ 1) :
    unshiftRename pos n ≥ 1 := by
  simp only [unshiftRename]
  split
  · omega
  · exact hn

theorem is0preserving_unshiftRename {pos : Nat} (hpos : pos ≥ 1) :
    Is0Preserving (unshiftRename pos) :=
  ⟨unshiftRename_zero pos, fun _ hn => unshiftRename_ge1 hpos hn⟩

theorem liftRename_unshiftRename {pos : Nat} (hpos : pos ≥ 1) :
    liftRename (unshiftRename pos) = unshiftRename (pos + 1) := by
  funext n
  cases n with
  | zero => simp [liftRename, unshiftRename]
  | succ m =>
    cases m with
    | zero =>
      simp only [liftRename, unshiftRename]
      simp [show ¬((0 : Nat) + 1 > pos + 1) by omega]
    | succ k =>
      simp only [liftRename, unshiftRename]
      by_cases h1 : k + 1 > pos
      · simp [show k + 1 > pos from h1, show k + 1 + 1 > pos + 1 by omega]
      · simp [show ¬(k + 1 > pos) from h1, show ¬(k + 1 + 1 > pos + 1) by omega]

/-! ## Key bridge: substTerm on FreeOf terms equals renameTerm -/

mutual
  theorem freeOf_substTerm_eq_renameTerm {pos : Nat} {t : Term} {r : Term}
      (hpos : pos ≥ 1) (hfree : freeOf pos t = true) :
      substTerm pos r t = renameTerm (unshiftRename pos) t := by
    match t with
    | .Var n =>
      simp [freeOf, bne_iff_ne] at hfree
      simp only [substTerm, renameTerm, unshiftRename]
      split
      · next heq => exact absurd heq hfree
      · next hne =>
        by_cases hgt : n > pos
        · simp [show pos < n by omega]
        · simp [show ¬(pos < n) by omega]
    | .Constant _ => simp [substTerm, renameTerm]
    | .Builtin _ => simp [substTerm, renameTerm]
    | .Error => simp [substTerm, renameTerm]
    | .Lam name body =>
      simp [freeOf] at hfree
      simp only [substTerm, renameTerm]
      congr 1
      rw [freeOf_substTerm_eq_renameTerm (by omega) hfree,
          liftRename_unshiftRename hpos]
    | .Apply f x =>
      simp [freeOf] at hfree
      simp only [substTerm, renameTerm]
      congr 1
      · exact freeOf_substTerm_eq_renameTerm hpos hfree.1
      · exact freeOf_substTerm_eq_renameTerm hpos hfree.2
    | .Force e =>
      simp [freeOf] at hfree
      simp only [substTerm, renameTerm]
      congr 1
      exact freeOf_substTerm_eq_renameTerm hpos hfree
    | .Delay e =>
      simp [freeOf] at hfree
      simp only [substTerm, renameTerm]
      congr 1
      exact freeOf_substTerm_eq_renameTerm hpos hfree
    | .Constr tag args =>
      simp [freeOf] at hfree
      simp only [substTerm, renameTerm]
      congr 1
      exact freeOfList_substTermList_eq_renameTermList hpos hfree
    | .Case scrut alts =>
      simp [freeOf] at hfree
      simp only [substTerm, renameTerm]
      congr 1
      · exact freeOf_substTerm_eq_renameTerm hpos hfree.1
      · exact freeOfList_substTermList_eq_renameTermList hpos hfree.2
  termination_by sizeOf t

  theorem freeOfList_substTermList_eq_renameTermList
      {pos : Nat} {ts : List Term} {r : Term}
      (hpos : pos ≥ 1) (hfree : freeOfList pos ts = true) :
      substTermList pos r ts = renameTermList (unshiftRename pos) ts := by
    match ts with
    | [] => simp [substTermList, renameTermList]
    | t :: rest =>
      simp [freeOfList] at hfree
      simp only [substTermList, renameTermList]
      congr 1
      · exact freeOf_substTerm_eq_renameTerm hpos hfree.1
      · exact freeOfList_substTermList_eq_renameTermList hpos hfree.2
  termination_by sizeOf ts
end

/-! ## Shift-unshift roundtrip for FreeOf terms

`renameTerm (shiftRename pos) (substTerm pos r t) = t` when `freeOf pos t`. -/

private theorem shift_unshift_var {pos n : Nat} (hpos : pos ≥ 1) (hne : n ≠ pos) :
    shiftRename pos (unshiftRename pos n) = n := by
  simp only [unshiftRename, shiftRename]
  by_cases hgt : n > pos
  · simp [if_pos hgt, show n - 1 ≥ pos by omega]; omega
  · have hlt : n < pos := by omega
    simp [if_neg hgt, show ¬(n ≥ pos) by omega]

mutual
  theorem freeOf_shift_substTerm {pos : Nat} {t : Term} {r : Term}
      (hpos : pos ≥ 1) (hfree : freeOf pos t = true) :
      renameTerm (shiftRename pos) (substTerm pos r t) = t := by
    match t with
    | .Var n =>
      simp [freeOf, bne_iff_ne] at hfree
      simp only [substTerm]
      split
      · next heq => exact absurd heq hfree
      · next hne =>
        by_cases hgt : n > pos
        · simp [if_pos (show pos < n by omega), renameTerm, shiftRename,
            show n - 1 ≥ pos by omega]; omega
        · simp [if_neg (show ¬(pos < n) by omega), renameTerm, shiftRename,
            show ¬(n ≥ pos) by omega]
    | .Constant _ | .Builtin _ | .Error => simp [substTerm, renameTerm]
    | .Lam name body =>
      simp [freeOf] at hfree
      simp only [substTerm, renameTerm,
        Moist.Verified.liftRename_shiftRename (by omega : pos ≥ 1)]
      exact congrArg (Term.Lam name) (freeOf_shift_substTerm (by omega) hfree)
    | .Apply f x =>
      simp [freeOf] at hfree
      simp only [substTerm, renameTerm]
      congr 1
      · exact freeOf_shift_substTerm hpos hfree.1
      · exact freeOf_shift_substTerm hpos hfree.2
    | .Force e =>
      simp [freeOf] at hfree
      simp only [substTerm, renameTerm]
      exact congrArg Term.Force (freeOf_shift_substTerm hpos hfree)
    | .Delay e =>
      simp [freeOf] at hfree
      simp only [substTerm, renameTerm]
      exact congrArg Term.Delay (freeOf_shift_substTerm hpos hfree)
    | .Constr tag args =>
      simp [freeOf] at hfree
      simp only [substTerm, renameTerm]
      exact congrArg (Term.Constr tag) (freeOfList_shift_substTermList hpos hfree)
    | .Case scrut alts =>
      simp [freeOf] at hfree
      simp only [substTerm, renameTerm]
      congr 1
      · exact freeOf_shift_substTerm hpos hfree.1
      · exact freeOfList_shift_substTermList hpos hfree.2
  termination_by sizeOf t

  theorem freeOfList_shift_substTermList {pos : Nat} {ts : List Term} {r : Term}
      (hpos : pos ≥ 1) (hfree : freeOfList pos ts = true) :
      renameTermList (shiftRename pos) (substTermList pos r ts) = ts := by
    match ts with
    | [] => simp [substTermList, renameTermList]
    | t :: rest =>
      simp [freeOfList] at hfree
      simp only [substTermList, renameTermList]
      congr 1
      · exact freeOf_shift_substTerm hpos hfree.1
      · exact freeOfList_shift_substTermList hpos hfree.2
  termination_by sizeOf ts
end

/-! ## closedAt for substTerm of FreeOf terms -/

theorem freeOf_closedAt_substTerm {pos d : Nat} {t r : Term}
    (hpos : pos ≥ 1) (hposd : pos ≤ d + 1) (_hfree : freeOf pos t = true)
    (hclosed_t : closedAt (d + 1) t = true) (hclosed_r : closedAt d r = true) :
    closedAt d (substTerm pos r t) = true :=
  Moist.Verified.BetaValueRefines.closedAt_substTerm pos r t d hpos hposd hclosed_r hclosed_t

/-! ## Strict evaluation order: error propagation

If `t_rhs` errors in env `ρ` on all stacks, and `t_rhs` occurs once in
strict position in `t_body`, then `substTerm pos t_rhs t_body` also errors. -/

section ErrorPropagation

open Moist.CEK (State CekEnv CekValue Stack Frame step)
open Moist.Verified.Equivalence (Reaches steps)
open Moist.Verified (halt_or_error)
open Moist.Verified.BetaValueRefines (steps_trans steps_error_fixed
  steps_halt_fixed)

private theorem reaches_halt_not_error {s : State} {v : CekValue}
    (hv : Reaches s (.halt v)) (he : Reaches s .error) : False := by
  obtain ⟨m, hm⟩ := hv; obtain ⟨n, hn⟩ := he
  have h1 : steps (m + n) s = .halt v := by rw [steps_trans, hm, steps_halt_fixed]
  have h2 : steps (n + m) s = .error := by rw [steps_trans, hn, steps_error_fixed]
  rw [show m + n = n + m from Nat.add_comm m n] at h1; rw [h1] at h2
  exact State.noConfusion h2

private theorem reaches_error_of_step {s s' : State}
    (hstep : step s = s') (h : Reaches s' .error) : Reaches s .error := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by rw [show n + 1 = 1 + n by omega, steps_trans]; simp [steps]; rw [hstep, hn]⟩

private theorem error_of_halt_then_error {s : State} {n m : Nat} {v : CekValue}
    (h_halt : steps n s = .halt v) (h_err : steps m s = .error) : False := by
  by_cases hle : n ≤ m
  · have : m = n + (m - n) := by omega
    rw [this, steps_trans, h_halt, steps_halt_fixed] at h_err
    exact State.noConfusion h_err
  · have : n = m + (n - m) := by omega
    rw [this, steps_trans, h_err, steps_error_fixed] at h_halt
    exact State.noConfusion h_halt

private theorem apply_step (π : Stack) (ρ : CekEnv) (f x : Term) :
    step (.compute π ρ (.Apply f x)) =
      .compute (Frame.arg x ρ :: π) ρ f := by rfl

private theorem force_step (π : Stack) (ρ : CekEnv) (e : Term) :
    step (.compute π ρ (.Force e)) =
      .compute (Frame.force :: π) ρ e := by rfl

private theorem case_step (π : Stack) (ρ : CekEnv) (scrut : Term) (alts : List Term) :
    step (.compute π ρ (.Case scrut alts)) =
      .compute (Frame.caseScrutinee alts ρ :: π) ρ scrut := by rfl

private theorem constr_cons_step (π : Stack) (ρ : CekEnv) (tag : Nat) (m : Term) (ms : List Term) :
    step (.compute π ρ (.Constr tag (m :: ms))) =
      .compute (Frame.constrField tag [] ms ρ :: π) ρ m := by rfl

private theorem constrField_list_reaches_error {pos d : Nat} {t_rhs : Term}
    {ρ : CekEnv} {tag : Nat} {done : List CekValue}
    {t : Term} {ts : List Term} {bound : Nat}
    (h_occ : StrictSingleOccList pos (t :: ts))
    (h_rhs_err : ∀ π, Reaches (.compute π ρ t_rhs) .error)
    (hclosed_list : Moist.Verified.closedAtList (d + 1) (t :: ts) = true)
    (ih : ∀ {u : Term}, StrictSingleOcc pos u →
      Moist.Verified.closedAt (d + 1) u = true → sizeOf u < bound →
      ∀ π, Reaches (.compute π ρ (substTerm pos t_rhs u)) .error)
    (h_list_bound : 1 + sizeOf t + sizeOf ts ≤ bound) :
    ∀ π, Reaches
      (.compute (Frame.constrField tag done (substTermList pos t_rhs ts) ρ :: π) ρ
        (substTerm pos t_rhs t)) .error := by
  intro π
  have hclosed_t : Moist.Verified.closedAt (d + 1) t = true := by
    simp [Moist.Verified.closedAtList] at hclosed_list; exact hclosed_list.1
  have hclosed_ts : Moist.Verified.closedAtList (d + 1) ts = true := by
    simp [Moist.Verified.closedAtList] at hclosed_list; exact hclosed_list.2
  match h_occ with
  | .head h_t _ => exact ih h_t hclosed_t (by omega) _
  | .tail h_free_t h_rest =>
    apply Moist.Verified.budget_exhaustion
    intro v ⟨n, hn⟩
    have h_suffix : Moist.Verified.BetaValueRefines.hasSuffix
        (Frame.constrField tag done (substTermList pos t_rhs ts) ρ :: π)
        (.compute (Frame.constrField tag done (substTermList pos t_rhs ts) ρ :: π) ρ
          (substTerm pos t_rhs t)) := ⟨[], rfl⟩
    obtain ⟨m₁, _, v_t, hm₁⟩ :=
      Moist.Verified.BetaValueRefines.halt_descends_to_baseπ n _ v hn h_suffix
    match ts, h_rest, h_list_bound, hclosed_ts with
    | u :: us, h_rest', h_lb, hclosed_us =>
      have h_cf_step : step (.ret
          (Frame.constrField tag done
            (substTerm pos t_rhs u :: substTermList pos t_rhs us) ρ :: π) v_t) =
          .compute (Frame.constrField tag (v_t :: done)
            (substTermList pos t_rhs us) ρ :: π) ρ
            (substTerm pos t_rhs u) := rfl
      have h_list_sizeof : sizeOf (u :: us) = 1 + sizeOf u + sizeOf us := by
        simp
      have h_next_err := @constrField_list_reaches_error pos d t_rhs ρ tag (v_t :: done)
        u us bound h_rest' h_rhs_err hclosed_us ih (by omega) π
      obtain ⟨q, hq⟩ := h_next_err
      have h_subst_cons : substTermList pos t_rhs (u :: us) =
          substTerm pos t_rhs u :: substTermList pos t_rhs us := by
        simp [substTermList]
      rw [h_subst_cons] at hm₁ hn
      have h_err_at : steps (m₁ + 1 + q)
          (.compute (Frame.constrField tag done
            (substTerm pos t_rhs u :: substTermList pos t_rhs us) ρ :: π) ρ
            (substTerm pos t_rhs t)) = .error := by
        rw [show m₁ + 1 + q = m₁ + (1 + q) by omega, steps_trans, hm₁,
            show 1 + q = 1 + q from rfl, steps_trans]
        simp [steps, h_cf_step]; exact hq
      exact error_of_halt_then_error hn h_err_at

private theorem apply_r_error_propagation {pos : Nat} {f x t_rhs : Term}
    {ρ : CekEnv}
    (_h_free_f : freeOf pos f = true)
    (_h_x : StrictSingleOcc pos x)
    (_h_rhs_err : ∀ π, Reaches (.compute π ρ t_rhs) .error)
    (ih_x : ∀ π, Reaches (.compute π ρ (substTerm pos t_rhs x)) .error) :
    ∀ π, Reaches
      (.compute π ρ (.Apply (substTerm pos t_rhs f) (substTerm pos t_rhs x))) .error := by
  intro π
  let subst_x := substTerm pos t_rhs x
  let subst_f := substTerm pos t_rhs f
  apply Moist.Verified.budget_exhaustion
  intro v ⟨n, hn⟩
  have h1 : step (.compute π ρ (.Apply subst_f subst_x)) =
      .compute (Frame.arg subst_x ρ :: π) ρ subst_f := rfl
  have hn' : n ≥ 1 := by
    match n with
    | 0 => simp [steps] at hn
    | n' + 1 => omega
  have h_after_step : steps (n - 1) (.compute (Frame.arg subst_x ρ :: π) ρ subst_f) = .halt v := by
    have : n = 1 + (n - 1) := by omega
    rw [this, steps_trans] at hn; simp [steps] at hn; exact hn
  have h_suffix : Moist.Verified.BetaValueRefines.hasSuffix (Frame.arg subst_x ρ :: π)
      (.compute (Frame.arg subst_x ρ :: π) ρ subst_f) := ⟨[], rfl⟩
  obtain ⟨m₁, _, v_f, hm₁⟩ :=
    Moist.Verified.BetaValueRefines.halt_descends_to_baseπ (n - 1)
      (.compute (Frame.arg subst_x ρ :: π) ρ subst_f) v h_after_step h_suffix
  have h_arg_step : step (.ret (Frame.arg subst_x ρ :: π) v_f) =
      .compute (Frame.funV v_f :: π) ρ subst_x := rfl
  obtain ⟨q, hq⟩ := ih_x (Frame.funV v_f :: π)
  have h_err : steps (m₁ + 1 + q) (.compute (Frame.arg subst_x ρ :: π) ρ subst_f) = .error := by
    rw [show m₁ + 1 + q = m₁ + (1 + q) by omega, steps_trans, hm₁]
    rw [show 1 + q = 1 + q from rfl, steps_trans]; simp [steps, h_arg_step]; exact hq
  have h_err_full : steps (1 + (m₁ + 1 + q)) (.compute π ρ (.Apply subst_f subst_x)) = .error := by
    rw [steps_trans]; simp [steps, h1]; exact h_err
  have h_halt_full : steps n (.compute π ρ (.Apply subst_f subst_x)) = .halt v := hn
  exact absurd h_halt_full (by
    intro h; exact error_of_halt_then_error h h_err_full)

end ErrorPropagation

/-! ## Stack independence via StepLift -/

section StackIndependence

open Moist.CEK (State CekEnv CekValue Stack Frame step)
open Moist.Verified.Equivalence (Reaches steps)
open Moist.Verified.BetaValueRefines (steps_trans steps_error_fixed steps_halt_fixed)

private theorem steps_bridge : ∀ (n : Nat) (s : State),
    steps n s = Moist.Verified.Semantics.steps n s := by
  intro n; induction n with
  | zero => intro s; rfl
  | succ m ih => intro s; show steps m (step s) = _; rw [ih]; rfl

theorem error_on_all_stacks {ρ : CekEnv} {t : Term}
    (h_err : Reaches (.compute [] ρ t) .error) :
    ∀ π, Reaches (.compute π ρ t) .error := by
  intro π; obtain ⟨n, hn⟩ := h_err
  rw [steps_bridge] at hn
  have h_inact : ∃ k, k ≤ n ∧
      Moist.Verified.StepLift.isActive (Moist.Verified.Semantics.steps k (.compute [] ρ t)) = false :=
    ⟨n, Nat.le_refl _, by rw [hn]; rfl⟩
  obtain ⟨K, hK_le, hK_inact, hK_min⟩ :=
    Moist.Verified.StepLift.firstInactive _ n h_inact
  have h_comm := Moist.Verified.StepLift.steps_liftState π K _ hK_min
  have h_lift : Moist.Verified.StepLift.liftState π (.compute [] ρ t) = .compute π ρ t := by
    simp [Moist.Verified.StepLift.liftState]
  rw [h_lift] at h_comm
  cases h_st : Moist.Verified.Semantics.steps K (.compute [] ρ t) with
  | error =>
    rw [h_st] at h_comm; simp [Moist.Verified.StepLift.liftState] at h_comm
    exact ⟨K, by rw [steps_bridge]; exact h_comm⟩
  | halt w =>
    exfalso; rw [h_st] at h_comm; simp [Moist.Verified.StepLift.liftState] at h_comm
    have h_K_halt_on_π : Moist.Verified.Semantics.steps K (.compute π ρ t) = .ret π w := h_comm
    have : Moist.Verified.Semantics.steps n (.compute [] ρ t) = .halt w := by
      rw [show n = K + (n - K) by omega, Moist.Verified.Semantics.steps_trans, h_st,
          Moist.Verified.Semantics.steps_halt]
    rw [this] at hn; exact State.noConfusion hn
  | ret π' w =>
    cases π' with
    | nil =>
      exfalso
      by_cases hKn : K = n
      · subst hKn; rw [h_st] at hn; exact State.noConfusion hn
      · have hK_lt : K < n := by omega
        have h_next : Moist.Verified.Semantics.steps (K + 1) (.compute [] ρ t) = .halt w := by
          rw [Moist.Verified.Semantics.steps_trans, h_st]; rfl
        have : Moist.Verified.Semantics.steps n (.compute [] ρ t) = .halt w := by
          rw [show n = (K + 1) + (n - K - 1) by omega, Moist.Verified.Semantics.steps_trans,
              h_next, Moist.Verified.Semantics.steps_halt]
        rw [this] at hn; exact State.noConfusion hn
    | cons _ _ => rw [h_st] at hK_inact; simp [Moist.Verified.StepLift.isActive] at hK_inact
  | compute _ _ _ => rw [h_st] at hK_inact; simp [Moist.Verified.StepLift.isActive] at hK_inact

theorem ret_on_all_stacks {ρ : CekEnv} {t : Term} {v : CekValue} {n : Nat}
    (hn : steps n (.compute [] ρ t) = .ret [] v) :
    ∀ π, ∃ m, steps m (.compute π ρ t) = .ret π v := by
  intro π
  rw [steps_bridge] at hn
  have h_inact : ∃ k, k ≤ n ∧
      Moist.Verified.StepLift.isActive (Moist.Verified.Semantics.steps k (.compute [] ρ t)) = false :=
    ⟨n, Nat.le_refl _, by rw [hn]; rfl⟩
  obtain ⟨K, hK_le, hK_inact, hK_min⟩ :=
    Moist.Verified.StepLift.firstInactive _ n h_inact
  have h_comm := Moist.Verified.StepLift.steps_liftState π K _ hK_min
  have h_lift : Moist.Verified.StepLift.liftState π (.compute [] ρ t) = .compute π ρ t := by
    simp [Moist.Verified.StepLift.liftState]
  rw [h_lift] at h_comm
  cases h_st : Moist.Verified.Semantics.steps K (.compute [] ρ t) with
  | ret π' w =>
    cases π' with
    | nil =>
      have : w = v := by
        by_cases hKn : K = n
        · subst hKn; rw [h_st] at hn; cases hn; rfl
        · exfalso
          have h_next : Moist.Verified.Semantics.steps (K + 1) (.compute [] ρ t) = .halt w := by
            rw [Moist.Verified.Semantics.steps_trans, h_st]; rfl
          have : Moist.Verified.Semantics.steps n (.compute [] ρ t) = .halt w := by
            rw [show n = (K + 1) + (n - K - 1) by omega, Moist.Verified.Semantics.steps_trans,
                h_next, Moist.Verified.Semantics.steps_halt]
          rw [this] at hn; exact State.noConfusion hn
      subst this; rw [h_st, Moist.Verified.StepLift.liftState] at h_comm
      exact ⟨K, by rw [steps_bridge]; exact h_comm⟩
    | cons _ _ => rw [h_st] at hK_inact; simp [Moist.Verified.StepLift.isActive] at hK_inact
  | error =>
    exfalso
    have : Moist.Verified.Semantics.steps n (.compute [] ρ t) = .error := by
      rw [show n = K + (n - K) by omega, Moist.Verified.Semantics.steps_trans, h_st,
          Moist.Verified.Semantics.steps_error]
    rw [this] at hn; exact State.noConfusion hn
  | halt w =>
    exfalso; rw [h_st] at h_comm; simp [Moist.Verified.StepLift.liftState] at h_comm
    have : Moist.Verified.Semantics.steps n (.compute [] ρ t) = .halt w := by
      rw [show n = K + (n - K) by omega, Moist.Verified.Semantics.steps_trans, h_st,
          Moist.Verified.Semantics.steps_halt]
    rw [this] at hn; exact State.noConfusion hn
  | compute _ _ _ => rw [h_st] at hK_inact; simp [Moist.Verified.StepLift.isActive] at hK_inact

end StackIndependence

/-! ## Strict subst reaches error (main)

Combines `StrictSingleOcc`, error propagation helpers, and `renameRefinesR_shift1`
to push the error hypothesis under lambda binders for the `.let_body` case. -/

section StrictSubstErrorProp

open Moist.CEK (State CekEnv CekValue Stack Frame step)
open Moist.Verified.Equivalence (Reaches steps)
open Moist.Verified (closedAt closedAtList)
open Moist.Verified.BetaValueRefines (steps_trans steps_error_fixed
  steps_halt_fixed hasSuffix halt_descends_to_baseπ)

/-- Error on `t_rhs` under `ρ` lifts to error on the shifted term under the
    extended env `ρ.extend w`. Uses `renameRefinesR_shift1` on the empty
    stack and `error_on_all_stacks` to cover arbitrary stacks. -/
private theorem shift_rhs_reaches_error {d : Nat} {t_rhs : Term} {ρ : CekEnv}
    (hclosed : closedAt d t_rhs = true)
    (henv_wf : Moist.Verified.BetaValueRefines.EnvWellFormed d ρ)
    (h_err : ∀ π, Reaches (.compute π ρ t_rhs) .error) (w : CekValue) :
    ∀ π, Reaches (.compute π (ρ.extend w)
      (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_rhs)) .error := by
  obtain ⟨n, hn⟩ := h_err []
  have h_env_refl :
      Moist.Verified.Contextual.SoundnessRefines.EnvRefinesK n d ρ ρ :=
    Moist.Verified.BetaValueRefines.envRefinesK_refl henv_wf
  have h_rename :
      Moist.Verified.FundamentalRefines.RenameEnvRefR
        (Moist.Verified.shiftRename 1) n d ρ (ρ.extend w) :=
    Moist.Verified.FundamentalRefines.envRefinesK_to_renameEnvRefR_shift h_env_refl
  have h_stack_nil :
      Moist.Verified.Contextual.SoundnessRefines.StackRefK
        Moist.Verified.Contextual.SoundnessRefines.ValueRefinesK n [] [] :=
    Moist.Verified.Contextual.SoundnessRefines.stackRefK_nil n
  have h_obs : Moist.Verified.Equivalence.ObsRefinesK n
      (.compute [] ρ t_rhs)
      (.compute [] (ρ.extend w)
        (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_rhs)) :=
    Moist.Verified.FundamentalRefines.renameRefinesR_shift1 d t_rhs hclosed
      n n (Nat.le_refl _) ρ (ρ.extend w) h_rename
      n (Nat.le_refl _) [] [] h_stack_nil
  have h_err_nil : Reaches
      (.compute [] (ρ.extend w)
        (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_rhs))
      .error := h_obs.2 n (Nat.le_refl _) hn
  exact error_on_all_stacks h_err_nil

private theorem strict_subst_reaches_error_aux (sz : Nat) {pos : Nat} {t_rhs : Term}
    {d : Nat} {ρ : CekEnv} {t_body : Term}
    (h_sz : sizeOf t_body ≤ sz)
    (h_strict : StrictSingleOcc pos t_body)
    (hpos : 1 ≤ pos)
    (hposd : pos ≤ d + 1)
    (hclosed_body : closedAt (d + 1) t_body = true)
    (hclosed_rhs : closedAt d t_rhs = true)
    (henv_wf : Moist.Verified.BetaValueRefines.EnvWellFormed d ρ)
    (hlen : d ≤ ρ.length)
    (h_rhs_err : ∀ π, Reaches (.compute π ρ t_rhs) .error) :
    ∀ π, Reaches (.compute π ρ (substTerm pos t_rhs t_body)) .error := by
  induction sz generalizing pos t_rhs d ρ t_body with
  | zero =>
    exfalso; cases h_strict <;> simp [Term._sizeOf_inst] at h_sz
  | succ n ih =>
    intro π
    match h_strict with
    | .var =>
      simp [substTerm]; exact h_rhs_err π
    | .apply_l (f := f) (x := x) h_f _ =>
      have hsz : sizeOf f ≤ n := by
        have : sizeOf (Term.Apply f x) = 1 + sizeOf f + sizeOf x := rfl; omega
      have hclosed_f : closedAt (d + 1) f = true := by
        simp [closedAt] at hclosed_body; exact hclosed_body.1
      simp only [substTerm]
      apply reaches_error_of_step (apply_step π ρ _ _)
      exact ih hsz h_f hpos hposd hclosed_f hclosed_rhs henv_wf hlen h_rhs_err _
    | .apply_r (f := f) (x := x) h_free_f h_x =>
      have hsz : sizeOf x ≤ n := by
        have : sizeOf (Term.Apply f x) = 1 + sizeOf f + sizeOf x := rfl; omega
      have hclosed_x : closedAt (d + 1) x = true := by
        simp [closedAt] at hclosed_body; exact hclosed_body.2
      simp only [substTerm]
      exact apply_r_error_propagation h_free_f h_x h_rhs_err
        (ih hsz h_x hpos hposd hclosed_x hclosed_rhs henv_wf hlen h_rhs_err) π
    | .force (e := e) h_e =>
      have hsz : sizeOf e ≤ n := by
        have : sizeOf (Term.Force e) = 1 + sizeOf e := rfl; omega
      have hclosed_e : closedAt (d + 1) e = true := by
        simp [closedAt] at hclosed_body; exact hclosed_body
      simp only [substTerm]
      apply reaches_error_of_step (force_step π ρ _)
      exact ih hsz h_e hpos hposd hclosed_e hclosed_rhs henv_wf hlen h_rhs_err _
    | .constr (tag := tag) (args := t :: ts) h_args =>
      have h_args_sz : sizeOf t + sizeOf ts ≤ n := by
        have : sizeOf (Term.Constr tag (t :: ts)) =
            1 + sizeOf tag + (1 + sizeOf t + sizeOf ts) := by
          simp [Term._sizeOf_inst, instSizeOfNat, List._sizeOf_inst]
        omega
      have hclosed_args : closedAtList (d + 1) (t :: ts) = true := by
        simp [closedAt] at hclosed_body; exact hclosed_body
      simp only [substTerm, substTermList]
      apply reaches_error_of_step (constr_cons_step π ρ tag _ _)
      exact constrField_list_reaches_error h_args h_rhs_err hclosed_args
        (fun h_so hcl (h_esz : sizeOf _ < _) =>
          ih (show sizeOf _ ≤ n by omega) h_so hpos hposd hcl hclosed_rhs henv_wf hlen h_rhs_err)
        (show 1 + sizeOf t + sizeOf ts ≤ 1 + sizeOf t + sizeOf ts by omega) _
    | .case_scrut (scrut := scrut) (alts := alts) h_scrut _ =>
      have hsz : sizeOf scrut ≤ n := by
        have : sizeOf (Term.Case scrut alts) =
            1 + sizeOf scrut + sizeOf alts := by
          simp [Term._sizeOf_inst, List._sizeOf_inst]
        omega
      have hclosed_scrut : closedAt (d + 1) scrut = true := by
        simp [closedAt] at hclosed_body; exact hclosed_body.1
      simp only [substTerm]
      apply reaches_error_of_step (case_step π ρ _ _)
      exact ih hsz h_scrut hpos hposd hclosed_scrut hclosed_rhs henv_wf hlen h_rhs_err _
    | .let_body (body := body) (rhs := rhs_inner) h_body h_free =>
      -- t_body = Apply (Lam 0 body) rhs_inner
      -- After simp: Apply (Lam 0 subst_body) subst_rhs_inner
      -- where subst_body = substTerm (pos+1) (shifted t_rhs) body
      --       subst_rhs_inner = substTerm pos t_rhs rhs_inner
      have hsz_body : sizeOf body ≤ n := by
        have h_apply : sizeOf (Term.Apply (Term.Lam 0 body) rhs_inner) =
            1 + sizeOf (Term.Lam 0 body) + sizeOf rhs_inner := rfl
        have h_lam : sizeOf (Term.Lam 0 body) = 1 + sizeOf (0 : Nat) + sizeOf body := rfl
        have h_zero : sizeOf (0 : Nat) = 0 := rfl
        omega
      have hsz_rhs_inner : sizeOf rhs_inner ≤ n := by
        have h_apply : sizeOf (Term.Apply (Term.Lam 0 body) rhs_inner) =
            1 + sizeOf (Term.Lam 0 body) + sizeOf rhs_inner := rfl
        have h_lam_pos : sizeOf (Term.Lam 0 body) ≥ 1 := by
          have : sizeOf (Term.Lam 0 body) = 1 + sizeOf (0 : Nat) + sizeOf body := rfl
          omega
        omega
      have hclosed_body_body : closedAt (d + 2) body = true := by
        simp [closedAt] at hclosed_body; exact hclosed_body.1
      have hclosed_rhs_inner : closedAt (d + 1) rhs_inner = true := by
        simp [closedAt] at hclosed_body; exact hclosed_body.2
      -- Reduce arbitrary-stack goal to empty-stack case via error_on_all_stacks
      -- Show Reaches (compute [] ρ (substTerm ...)) .error first.
      suffices h_nil : Reaches
          (.compute ([] : Stack) ρ
            (substTerm pos t_rhs (Term.Apply (Term.Lam 0 body) rhs_inner))) .error by
        exact error_on_all_stacks h_nil π
      -- Unfold substTerm once on goal
      simp only [substTerm]
      -- Use budget_exhaustion: assume halts, derive contradiction
      apply Moist.Verified.budget_exhaustion
      intro v_final h_halt
      obtain ⟨N, hN⟩ := h_halt
      -- Define abbreviations
      let subst_body : Term := substTerm (pos + 1)
        (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_rhs) body
      let subst_rhs_inner : Term := substTerm pos t_rhs rhs_inner
      -- First 3 steps are deterministic
      have h3 : steps 3
          (.compute [] ρ (.Apply (.Lam 0 subst_body) subst_rhs_inner)) =
          .compute [Frame.funV (.VLam subst_body ρ)] ρ subst_rhs_inner := by
        simp [steps, step, subst_body, subst_rhs_inner]
      have hN_ge_3 : N ≥ 3 := by
        rcases N with _ | _ | _ | N''
        · simp only [steps] at hN; exact absurd hN State.noConfusion
        · simp only [steps, step] at hN; exact absurd hN State.noConfusion
        · simp only [steps, step] at hN; exact absurd hN State.noConfusion
        · omega
      have h_after_3 :
          steps (N - 3) (.compute [Frame.funV (.VLam subst_body ρ)] ρ subst_rhs_inner) =
            .halt v_final := by
        have heq : N = 3 + (N - 3) := by omega
        rw [heq, steps_trans] at hN
        rw [h3] at hN
        exact hN
      -- Extract intermediate ret on the base stack [funV ...]
      have h_suffix : hasSuffix [Frame.funV (.VLam subst_body ρ)]
          (.compute [Frame.funV (.VLam subst_body ρ)] ρ subst_rhs_inner) :=
        ⟨[], rfl⟩
      obtain ⟨m₁, hm₁_le, v_inner, hm₁⟩ :=
        halt_descends_to_baseπ (N - 3)
          (.compute [Frame.funV (.VLam subst_body ρ)] ρ subst_rhs_inner)
          v_final h_after_3 h_suffix
      -- closedness of shifted t_rhs
      have hclosed_shifted_t_rhs : closedAt (d + 1)
          (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_rhs) = true :=
        Moist.Verified.BetaValueRefines.closedAt_shift hclosed_rhs
      -- closedness of subst_body
      have hclosed_subst_body : closedAt (d + 1) subst_body = true :=
        Moist.Verified.BetaValueRefines.closedAt_substTerm
          (pos + 1) _ body (d + 1)
          (by omega) (by omega) hclosed_shifted_t_rhs hclosed_body_body
      -- VLam subst_body ρ is WellFormed
      have hvlam_wf : Moist.Verified.BetaValueRefines.ValueWellFormed
          (CekValue.VLam subst_body ρ) :=
        Moist.Verified.BetaValueRefines.ValueWellFormed.vlam henv_wf hlen hclosed_subst_body
      -- Stack [funV (VLam ...)] is WellFormed
      have hstack_wf :
          Moist.Verified.BetaValueRefines.StackWellFormed
            [Frame.funV (.VLam subst_body ρ)] :=
        Moist.Verified.BetaValueRefines.StackWellFormed.cons
          (Moist.Verified.BetaValueRefines.FrameWellFormed.funV hvlam_wf)
          Moist.Verified.BetaValueRefines.StackWellFormed.nil
      -- closedness of subst_rhs_inner
      have hclosed_subst_rhs_inner : closedAt d subst_rhs_inner = true :=
        Moist.Verified.BetaValueRefines.closedAt_substTerm
          pos t_rhs rhs_inner d hpos hposd hclosed_rhs hclosed_rhs_inner
      -- State at step 0 is WellFormed
      have hstate_wf : Moist.Verified.StepWellFormed.StateWellFormed
          (.compute [Frame.funV (.VLam subst_body ρ)] ρ subst_rhs_inner) :=
        Moist.Verified.StepWellFormed.StateWellFormed.compute hstack_wf henv_wf hlen
          hclosed_subst_rhs_inner
      -- v_inner is WellFormed (since the state hits halt via step m₁+1)
      have hv_inner_wf : Moist.Verified.BetaValueRefines.ValueWellFormed v_inner := by
        have h_after_m : Moist.Verified.StepWellFormed.StateWellFormed
            (steps m₁ (.compute [Frame.funV (.VLam subst_body ρ)] ρ subst_rhs_inner)) :=
          Moist.Verified.StepWellFormed.steps_preserves_wf m₁ _ hstate_wf
        rw [hm₁] at h_after_m
        cases h_after_m with
        | ret _ hv => exact hv
      -- One more step from hm₁: ret → compute (ρ.extend v_inner) subst_body on empty stack
      have h_funv_step :
          step (.ret [Frame.funV (.VLam subst_body ρ)] v_inner) =
            .compute [] (ρ.extend v_inner) subst_body := rfl
      -- m₁ < N - 3 (otherwise halt = ret, contradiction)
      have hm₁_lt : m₁ < N - 3 := by
        rcases Nat.lt_or_ge m₁ (N - 3) with hlt | hge
        · exact hlt
        · exfalso
          have hm₁_eq : m₁ = N - 3 := Nat.le_antisymm hm₁_le hge
          rw [hm₁_eq] at hm₁
          rw [hm₁] at h_after_3
          exact State.noConfusion h_after_3
      -- Remaining halt on compute subst_body under ρ.extend v_inner
      have h_remain_halt : steps ((N - 3) - m₁ - 1)
          (.compute [] (ρ.extend v_inner) subst_body) = .halt v_final := by
        have heq : N - 3 = m₁ + 1 + ((N - 3) - m₁ - 1) := by omega
        rw [heq, steps_trans, steps_trans, hm₁] at h_after_3
        simp only [steps, h_funv_step] at h_after_3
        exact h_after_3
      -- Derive error via IH
      have henv_wf' : Moist.Verified.BetaValueRefines.EnvWellFormed
          (d + 1) (ρ.extend v_inner) :=
        Moist.Verified.BetaValueRefines.envWellFormed_extend d henv_wf hlen hv_inner_wf
      have hlen' : d + 1 ≤ (ρ.extend v_inner).length := by
        show d + 1 ≤ ρ.length + 1
        omega
      have h_shifted_err :
          ∀ π', Reaches (.compute π' (ρ.extend v_inner)
              (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_rhs)) .error :=
        shift_rhs_reaches_error hclosed_rhs henv_wf h_rhs_err v_inner
      have h_body_err :
          ∀ π', Reaches (.compute π' (ρ.extend v_inner) subst_body) .error :=
        ih hsz_body h_body (by omega) (by omega)
          hclosed_body_body hclosed_shifted_t_rhs henv_wf' hlen' h_shifted_err
      obtain ⟨q, hq⟩ := h_body_err []
      exact error_of_halt_then_error h_remain_halt hq

theorem strict_subst_reaches_error {pos : Nat} {t_body t_rhs : Term}
    {d : Nat} {ρ : CekEnv}
    (h_strict : StrictSingleOcc pos t_body)
    (hpos : 1 ≤ pos)
    (hposd : pos ≤ d + 1)
    (hclosed_body : closedAt (d + 1) t_body = true)
    (hclosed_rhs : closedAt d t_rhs = true)
    (henv_wf : Moist.Verified.BetaValueRefines.EnvWellFormed d ρ)
    (hlen : d ≤ ρ.length)
    (h_rhs_err : ∀ π, Reaches (.compute π ρ t_rhs) .error) :
    ∀ π, Reaches (.compute π ρ (substTerm pos t_rhs t_body)) .error :=
  strict_subst_reaches_error_aux (sizeOf t_body) (Nat.le_refl _) h_strict hpos hposd
    hclosed_body hclosed_rhs henv_wf hlen h_rhs_err

end StrictSubstErrorProp

/-! ## Same-env ObsRefines: Apply vs substTerm

For the same env ρ and stack π, `Apply (Lam 0 t_body) t_rhs` ObsRefines
`substTerm 1 t_rhs t_body` when `StrictSingleOcc 1 t_body`. Uses stack
independence + budget_exhaustion + strict_subst_reaches_error. -/

section SameEnvBeta

open Moist.CEK (State CekEnv CekValue Stack Frame step)
open Moist.Verified.Equivalence (Reaches steps)
open Moist.Verified.BetaValueRefines (steps_trans steps_error_fixed steps_halt_fixed
  hasSuffix halt_descends_to_baseπ)

private theorem reaches_of_steps_reaches {s s' t : State} {m : Nat}
    (h_steps : steps m s = s') (h : Reaches s' t) : Reaches s t := by
  obtain ⟨n, hn⟩ := h; exact ⟨m + n, by rw [steps_trans, h_steps, hn]⟩

private theorem freeOf_obsRefines_fwd (sz : Nat) {sub t_rhs : Term}
    (_h_sz : sizeOf sub ≤ sz) (hfree : freeOf 1 sub = true)
    (hclosed_sub : closedAt (d + 1) sub = true) (hclosed_rhs : closedAt d t_rhs = true)
    {ρ : CekEnv} {v : CekValue}
    (henv_wf : Moist.Verified.BetaValueRefines.EnvWellFormed d ρ)
    (_hlen : d ≤ ρ.length)
    (_hvwf : Moist.Verified.BetaValueRefines.ValueWellFormed v) :
    ∀ k j, j ≤ k → ∀ i, i ≤ j → ∀ π₁ π₂,
      Moist.Verified.Contextual.SoundnessRefines.StackRefK
        Moist.Verified.Contextual.SoundnessRefines.ValueRefinesK i π₁ π₂ →
      Moist.Verified.Equivalence.ObsRefinesK i
        (.compute π₁ (ρ.extend v) sub)
        (.compute π₂ ρ (substTerm 1 t_rhs sub)) := by
  intro k j hj i hi π₁ π₂ hπ
  have h_closed_sub' : closedAt d (substTerm 1 t_rhs sub) = true :=
    Moist.Verified.BetaValueRefines.closedAt_substTerm 1 t_rhs sub d
      (by omega) (by omega) hclosed_rhs hclosed_sub
  have h_shift := freeOf_shift_substTerm (by omega : (1 : Nat) ≥ 1) hfree (r := t_rhs)
  conv at h_shift => lhs; rw [show shiftRename 1 = Moist.Verified.shiftRename 1 from rfl]
  have h_rename := Moist.Verified.FundamentalRefines.renameRefines_shift1 d
    (substTerm 1 t_rhs sub) h_closed_sub' k j hj (ρ.extend v) ρ
    (Moist.Verified.FundamentalRefines.envRefinesK_to_renameEnvRef_shift
      (Moist.Verified.BetaValueRefines.envRefinesK_refl henv_wf))
    i hi π₁ π₂ hπ
  rwa [h_shift] at h_rename

private theorem term_sizeOf_pos (t : Term) : sizeOf t ≥ 1 := by
  cases t <;> simp [Term._sizeOf_inst, instSizeOfNat] <;> omega

private theorem freeOfList_elem {pos : Nat} {ts : List Term}
    (h : freeOfList pos ts = true) {idx : Nat} (hidx : idx < ts.length) :
    freeOf pos (ts[idx]'hidx) = true := by
  induction ts generalizing idx with
  | nil => exact absurd hidx (Nat.not_lt_zero _)
  | cons a rest ih =>
    simp [freeOfList] at h
    cases idx with
    | zero => simp; exact h.1
    | succ k => exact ih h.2 (by simp at hidx; omega)

private theorem closedAtList_elem' {d : Nat} {ts : List Term}
    (h : Moist.Verified.closedAtList d ts = true) {idx : Nat} (hidx : idx < ts.length) :
    Moist.Verified.closedAt d (ts[idx]'hidx) = true := by
  induction ts generalizing idx with
  | nil => exact absurd hidx (Nat.not_lt_zero _)
  | cons a rest ih =>
    simp [Moist.Verified.closedAtList] at h
    cases idx with
    | zero => simp; exact h.1
    | succ k => exact ih h.2 (by simp at hidx; omega)

theorem SingleOccList.elem_singleOcc_or_freeOf
    {pos : Nat} {ts : List Term}
    (h : SingleOccList pos ts) (i : Nat) (hi : i < ts.length) :
    SingleOcc pos (ts[i]'hi) ∨ freeOf pos (ts[i]'hi) = true := by
  match ts, h with
  | _ :: _, .head ht hfree =>
    match i with
    | 0 => exact Or.inl ht
    | i' + 1 => exact Or.inr (freeOfList_elem hfree (by simp [List.length] at hi; omega))
  | _ :: _, .tail hfree hts =>
    match i with
    | 0 => exact Or.inr hfree
    | i' + 1 => exact hts.elem_singleOcc_or_freeOf i' (by simp [List.length] at hi; omega)

/-! ## Multi-shift rename: supports multi-level halt preservation

`multiShift K` shifts every positive index by `K`: `0 ↦ 0`, `n ↦ n + K` for
`n ≥ 1`. Equivalent to `(shiftRename 1)^K` as a function on `Nat`. Used to
lift halt hypotheses across multiple `extend`s from a WF base env. -/

def multiShift (K : Nat) : Nat → Nat :=
  fun n => if n = 0 then 0 else n + K

theorem multiShift_zero (n : Nat) : multiShift 0 n = n := by
  simp only [multiShift]; split <;> omega

theorem multiShift_id : multiShift 0 = id := by
  funext n; simp [multiShift_zero]

theorem multiShift_succ (K n : Nat) :
    multiShift (K + 1) n = Moist.Verified.shiftRename 1 (multiShift K n) := by
  simp only [multiShift]
  split
  · next hn => simp [Moist.Verified.shiftRename]
  · next hn =>
    have h1 : n + K ≥ 1 := by omega
    simp [Moist.Verified.shiftRename, h1]
    omega

/- Renaming composition helpers -/

/-- Liftings of 0-preserving functions commute with composition. -/
theorem liftRename_comp_of_0preserving
    {σ₁ σ₂ : Nat → Nat}
    (h₁ : Moist.Verified.FundamentalRefines.Is0Preserving σ₁) (n : Nat) :
    Moist.Verified.liftRename σ₂ (Moist.Verified.liftRename σ₁ n) =
    Moist.Verified.liftRename (σ₂ ∘ σ₁) n := by
  match n with
  | 0 => rfl
  | 1 => rfl
  | k + 2 =>
    have hk_pos : σ₁ (k + 1) ≥ 1 := h₁.2 (k + 1) (by omega)
    have h_lift1 : Moist.Verified.liftRename σ₁ (k + 2) = σ₁ (k + 1) + 1 := rfl
    have h_lift3 : Moist.Verified.liftRename (σ₂ ∘ σ₁) (k + 2) = σ₂ (σ₁ (k + 1)) + 1 := rfl
    rw [h_lift1, h_lift3]
    -- Goal: liftRename σ₂ (σ₁ (k+1) + 1) = σ₂ (σ₁ (k+1)) + 1
    obtain ⟨m, hm⟩ : ∃ m, σ₁ (k + 1) = m + 1 := by
      cases hσ : σ₁ (k + 1) with
      | zero => rw [hσ] at hk_pos; omega
      | succ m => exact ⟨m, rfl⟩
    rw [hm]
    rfl

/- Renaming composition: `renameTerm` commutes with function composition,
    when the inner rename is 0-preserving. -/
mutual
  theorem renameTerm_renameTerm (σ₁ σ₂ : Nat → Nat)
      (h₁ : Moist.Verified.FundamentalRefines.Is0Preserving σ₁) (t : Term) :
      Moist.Verified.renameTerm σ₂ (Moist.Verified.renameTerm σ₁ t) =
      Moist.Verified.renameTerm (σ₂ ∘ σ₁) t := by
    match t with
    | .Var n => simp [Moist.Verified.renameTerm, Function.comp]
    | .Constant _ | .Builtin _ | .Error => simp [Moist.Verified.renameTerm]
    | .Lam name body =>
      simp only [Moist.Verified.renameTerm]
      have hfun : Moist.Verified.liftRename σ₂ ∘ Moist.Verified.liftRename σ₁ =
          Moist.Verified.liftRename (σ₂ ∘ σ₁) := by
        funext n; exact liftRename_comp_of_0preserving h₁ n
      rw [renameTerm_renameTerm (Moist.Verified.liftRename σ₁)
          (Moist.Verified.liftRename σ₂)
          (Moist.Verified.FundamentalRefines.is0preserving_lift σ₁) body]
      rw [hfun]
    | .Apply f x =>
      simp only [Moist.Verified.renameTerm]
      rw [renameTerm_renameTerm σ₁ σ₂ h₁, renameTerm_renameTerm σ₁ σ₂ h₁]
    | .Force e =>
      simp only [Moist.Verified.renameTerm]
      rw [renameTerm_renameTerm σ₁ σ₂ h₁]
    | .Delay e =>
      simp only [Moist.Verified.renameTerm]
      rw [renameTerm_renameTerm σ₁ σ₂ h₁]
    | .Constr tag args =>
      simp only [Moist.Verified.renameTerm]
      rw [renameTermList_renameTermList σ₁ σ₂ h₁]
    | .Case scrut alts =>
      simp only [Moist.Verified.renameTerm]
      rw [renameTerm_renameTerm σ₁ σ₂ h₁, renameTermList_renameTermList σ₁ σ₂ h₁]
  termination_by sizeOf t

  theorem renameTermList_renameTermList (σ₁ σ₂ : Nat → Nat)
      (h₁ : Moist.Verified.FundamentalRefines.Is0Preserving σ₁) (ts : List Term) :
      Moist.Verified.renameTermList σ₂ (Moist.Verified.renameTermList σ₁ ts) =
      Moist.Verified.renameTermList (σ₂ ∘ σ₁) ts := by
    match ts with
    | [] => rfl
    | t :: rest =>
      simp only [Moist.Verified.renameTermList]
      rw [renameTerm_renameTerm σ₁ σ₂ h₁, renameTermList_renameTermList σ₁ σ₂ h₁]
  termination_by sizeOf ts
end

theorem is0preserving_multiShift (K : Nat) :
    Moist.Verified.FundamentalRefines.Is0Preserving (multiShift K) := by
  refine ⟨?_, ?_⟩
  · simp [multiShift]
  · intro n hn
    simp only [multiShift]
    split
    · omega
    · omega

-- Note: liftRename (multiShift K) ≠ multiShift K in general (they differ at n=1).
-- We don't need this identity directly; the iterShift rewrite uses a different path.

theorem renameTerm_multiShift_zero (t : Term) :
    Moist.Verified.renameTerm (multiShift 0) t = t := by
  rw [multiShift_id]; exact Moist.Verified.renameTerm_id t

/-- `iterShift K t = renameTerm (multiShift K) t` by induction on K, using
    composition of shiftRename with multiShift. -/
theorem iterShift_eq_renameTerm_multiShift (K : Nat) (t : Term) :
    Moist.Verified.SubstRefines.iterShift K t =
    Moist.Verified.renameTerm (multiShift K) t := by
  induction K generalizing t with
  | zero => simp [Moist.Verified.SubstRefines.iterShift, renameTerm_multiShift_zero]
  | succ m ih =>
    simp only [Moist.Verified.SubstRefines.iterShift]
    rw [ih]
    rw [renameTerm_renameTerm (multiShift m) (Moist.Verified.shiftRename 1)
        (is0preserving_multiShift m) t]
    congr 1
    funext n
    exact (multiShift_succ m n).symm

/-- `ShiftBisimEnv (multiShift K) d ρ ρ_K` for any WF `ρ` and any extension
    `ρ_K` whose top `K`-shifted positions match `ρ`'s. Proven by induction on
    the depth `d` using `shiftBisimValue_refl_id` at each value. -/
private theorem shiftBisimEnv_multiShift {d K : Nat} {ρ ρ_K : Moist.CEK.CekEnv}
    (hwf : Moist.Verified.BetaValueRefines.EnvWellFormed d ρ)
    (h_lookup : ∀ n, 0 < n → n ≤ d → ρ_K.lookup (n + K) = ρ.lookup n) :
    Moist.Verified.BetaValueRefines.ShiftBisimEnv (multiShift K) d ρ ρ_K := by
  induction d with
  | zero => exact Moist.Verified.BetaValueRefines.ShiftBisimEnv.zero
  | succ n ih =>
    cases hwf with
    | @succ _ _ v hrest _ hlookup_n hvwf =>
      have hrec := ih hrest (fun m hm hmd => h_lookup m hm (by omega))
      -- multiShift K (n + 1) = n + 1 + K
      have hms : multiShift K (n + 1) = n + 1 + K := by
        simp only [multiShift]; split
        · omega
        · rfl
      have hρK_at : ρ_K.lookup (n + 1 + K) = some v := by
        rw [h_lookup (n + 1) (by omega) (Nat.le_refl _)]; exact hlookup_n
      refine Moist.Verified.BetaValueRefines.ShiftBisimEnv.succ
        (v₁ := v) (v₂ := v) hrec hlookup_n ?_ ?_
      · rw [hms]; exact hρK_at
      · exact Moist.Verified.BetaValueRefines.shiftBisimValue_refl_id v hvwf

private theorem shifted_halt_extend_multi
    {t : Term} {v_ret : Moist.CEK.CekValue} {d K : Nat} {k : Nat}
    {ρ ρ_K : Moist.CEK.CekEnv}
    (hclosed : Moist.Verified.closedAt d t = true)
    (henv_wf : Moist.Verified.BetaValueRefines.EnvWellFormed d ρ)
    (h_ret : ∀ π, ∃ m, Moist.Verified.Equivalence.steps m (.compute π ρ t) = .ret π v_ret)
    (hvwf_ret : Moist.Verified.BetaValueRefines.ValueWellFormed v_ret)
    (h_ρK : ∀ n, 0 < n → n ≤ d → ρ_K.lookup (n + K) = ρ.lookup n) :
    ∀ π, ∃ m v',
      Moist.Verified.Equivalence.steps m (.compute π ρ_K
        (Moist.Verified.SubstRefines.iterShift K t)) = .ret π v' ∧
      Moist.Verified.Contextual.SoundnessRefines.ValueRefinesK k v_ret v' := by
  intro π
  obtain ⟨m, h_ret_orig⟩ := h_ret []
  have hshift_env : Moist.Verified.BetaValueRefines.ShiftBisimEnv
      (multiShift K) d ρ ρ_K :=
    shiftBisimEnv_multiShift henv_wf h_ρK
  rw [iterShift_eq_renameTerm_multiShift]
  have h_bisim_state : Moist.Verified.BetaValueRefines.ShiftBisimState
      (.compute [] ρ t)
      (.compute [] ρ_K
        (Moist.Verified.renameTerm (multiShift K) t)) :=
    Moist.Verified.BetaValueRefines.ShiftBisimState.compute
      (is0preserving_multiShift K)
      hshift_env hclosed Moist.Verified.BetaValueRefines.ShiftBisimStack.nil
  have h_after_m : Moist.Verified.BetaValueRefines.ShiftBisimState
      (Moist.Verified.Equivalence.steps m (.compute [] ρ t))
      (Moist.Verified.Equivalence.steps m
        (.compute [] ρ_K
          (Moist.Verified.renameTerm (multiShift K) t))) :=
    Moist.Verified.BetaValueRefines.shiftBisimState_steps_preserves m h_bisim_state
  rw [h_ret_orig] at h_after_m
  obtain ⟨π'', v_shift, h_shift_steps, h_bisim_v, h_bisim_π⟩ :=
    Moist.Verified.BetaValueRefines.shiftBisimState_ret_inv h_after_m
  cases h_bisim_π
  obtain ⟨q, hq⟩ := ret_on_all_stacks h_shift_steps π
  exact ⟨q, v_shift, hq,
    Moist.Verified.BetaValueRefines.valueRefinesK_of_shiftBisim_wf k v_ret v_shift hvwf_ret h_bisim_v⟩

/-! ## Bridge: SubstEnvRef to RenameEnvRef (shiftRename pos)

For a `SubstEnvRef pos v_rhs k (d+1) ρ₁ ρ₂`, the shift-pos rename relates
`ρ₁` and `ρ₂` at depth `d`. Used by `freeOf_obsRefines_fwd_gen`. -/

private theorem substEnvRef_to_renameEnvRef_shift {pos k d : Nat} {v_rhs : Moist.CEK.CekValue}
    {ρ₁ ρ₂ : Moist.CEK.CekEnv}
    (_hpos_ge : 1 ≤ pos)
    (h : Moist.Verified.BetaValueRefines.SubstEnvRef pos v_rhs k (d + 1) ρ₁ ρ₂) :
    Moist.Verified.FundamentalRefines.RenameEnvRef
      (Moist.Verified.shiftRename pos) k d ρ₁ ρ₂ := by
  intro n hn hnd
  by_cases h1 : n < pos
  · -- shiftRename pos n = n (since n < pos)
    have hsr : Moist.Verified.shiftRename pos n = n := by
      simp [Moist.Verified.shiftRename, show ¬(n ≥ pos) from by omega]
    rw [hsr]
    obtain ⟨v₁, v₂, hl₁, hl₂, hrel⟩ :=
      Moist.Verified.BetaValueRefines.substEnvRef_below_pos h hn (by omega) h1
    show match ρ₁.lookup n, ρ₂.lookup n with
         | some _, some _ => _ | none, none => True | _, _ => False
    rw [hl₁, hl₂]; exact hrel
  · -- n ≥ pos, so shiftRename pos n = n + 1
    have hsr : Moist.Verified.shiftRename pos n = n + 1 := by
      simp [Moist.Verified.shiftRename, show n ≥ pos from by omega]
    rw [hsr]
    -- n + 1 > pos. Apply substEnvRef_above_pos at index n+1.
    have h_gt : n + 1 > pos := by omega
    have hn1_pos : 0 < n + 1 := by omega
    have hn1_d : n + 1 ≤ d + 1 := by omega
    obtain ⟨v₁, v₂, hl₁, hl₂, hrel⟩ :=
      Moist.Verified.BetaValueRefines.substEnvRef_above_pos h hn1_pos hn1_d h_gt
    show match ρ₁.lookup (n + 1), ρ₂.lookup n with
         | some _, some _ => _ | none, none => True | _, _ => False
    -- n + 1 - 1 = n
    rw [show (n + 1 - 1 : Nat) = n from by omega] at hl₂
    rw [hl₁, hl₂]; exact hrel

/-! ## Generalized freeOf_obsRefines_fwd for arbitrary pos

For a `freeOf pos sub` term, substitution equals renaming, and evaluation
under `SubstEnvRef`-related envs is obsRefines-equivalent to evaluation
under the "shifted" env. Uses `renameRefines` with `shiftRename pos`. -/

private theorem freeOf_obsRefines_fwd_gen (sz : Nat) {pos d : Nat} {sub t_rhs : Term}
    (_h_sz : sizeOf sub ≤ sz)
    (hpos_ge : 1 ≤ pos) (hpos_d : pos ≤ d + 1)
    (hfree : freeOf pos sub = true)
    (hclosed_sub : Moist.Verified.closedAt (d + 1) sub = true)
    (hclosed_rhs : Moist.Verified.closedAt d t_rhs = true)
    {ρ₁ ρ₂ : Moist.CEK.CekEnv} {v_rhs : Moist.CEK.CekValue}
    {k_step : Nat}
    (henv : Moist.Verified.BetaValueRefines.SubstEnvRef pos v_rhs k_step (d + 1) ρ₁ ρ₂) :
    ∀ j, j ≤ k_step → ∀ i, i ≤ j → ∀ π₁ π₂,
      Moist.Verified.Contextual.SoundnessRefines.StackRefK
        Moist.Verified.Contextual.SoundnessRefines.ValueRefinesK i π₁ π₂ →
      Moist.Verified.Equivalence.ObsRefinesK i
        (.compute π₁ ρ₁ sub)
        (.compute π₂ ρ₂ (Moist.Verified.substTerm pos t_rhs sub)) := by
  intro j hj i hi π₁ π₂ hπ
  have h_closed_sub' : Moist.Verified.closedAt d (Moist.Verified.substTerm pos t_rhs sub) = true :=
    Moist.Verified.BetaValueRefines.closedAt_substTerm pos t_rhs sub d
      (by omega) (by omega) hclosed_rhs hclosed_sub
  have h_shift := freeOf_shift_substTerm hpos_ge hfree (r := t_rhs)
  have h_closed_sub'' : Moist.Verified.closedAt d (Moist.Verified.substTerm pos t_rhs sub) = true :=
    h_closed_sub'
  have henv_rename :
      Moist.Verified.FundamentalRefines.RenameEnvRef
        (Moist.Verified.shiftRename pos) j d ρ₁ ρ₂ := by
    apply Moist.Verified.FundamentalRefines.renameEnvRef_mono hj
    exact substEnvRef_to_renameEnvRef_shift hpos_ge henv
  have h_rename :=
    Moist.Verified.FundamentalRefines.renameRefines
      (Moist.Verified.shiftRename pos)
      (Moist.Verified.FundamentalRefines.is0preserving_shiftRename hpos_ge)
      d (Moist.Verified.substTerm pos t_rhs sub) h_closed_sub''
      j j (Nat.le_refl _) ρ₁ ρ₂ henv_rename i hi π₁ π₂ hπ
  rwa [h_shift] at h_rename

/-! ## Closedness preservation for iterExtend -/

-- Placeholder: closedness of t_rhs at d means iterShift n t_rhs is closed at d+n
-- (already provided by closedAt_iterShift in SubstRefines.lean).

open Moist.Verified.Contextual.SoundnessRefines
  (StackRefK ValueRefinesK stackRefK_mono valueRefinesK_mono
   evalBuiltin_compat_refines obsRefinesK_error listRel_valueRefinesK_mono
   applyArgFrames_stackRefK listRel_refl_vcon_refines) in
open Moist.Verified.Equivalence
  (ObsRefinesK obsRefinesK_mono obsRefinesK_of_step_compute
   obsRefinesK_zero_compute ListRel constToTagAndFields_fields_vcon) in
open Moist.Verified.BetaValueRefines
  (obsRefinesK_of_steps_left obsRefinesK_of_steps_right
   valueRefinesK_refl EnvWellFormed ValueWellFormed stackRefK_refl
   StackWellFormed substTermList_getElem) in
open Moist.Verified (substTermList_length closedAtList) in
private theorem body_subst_obsRefinesK_gen (sz : Nat) {d pos : Nat}
    {t_body t_rhs : Term}
    (h_sz : sizeOf t_body ≤ sz)
    (hpos_ge : 1 ≤ pos) (hpos_d : pos ≤ d + 1)
    (h_strict : SingleOcc pos t_body)
    (hclosed_body : closedAt (d + 1) t_body = true)
    (hclosed_rhs : closedAt d t_rhs = true)
    {ρ₁ ρ₂ : CekEnv} {v_rhs : CekValue}
    {k_step : Nat}
    (henv : Moist.Verified.BetaValueRefines.SubstEnvRef pos v_rhs k_step (d + 1) ρ₁ ρ₂)
    (hexact : ρ₁.lookup pos = some v_rhs)
    (h_r_halt_multi : ∀ (K : Nat) (ρ_ext : CekEnv),
        (∀ n, 0 < n → n ≤ d → ρ_ext.lookup (n + K) = ρ₂.lookup n) →
        ∀ π, ∃ m v',
          steps m (.compute π ρ_ext
            (Moist.Verified.SubstRefines.iterShift K t_rhs)) = .ret π v' ∧
          ValueRefinesK k_step v_rhs v')
    (hlen_L : d + 1 ≤ ρ₁.length)
    (hlen_R : d ≤ ρ₂.length)
    (hvwf : ValueWellFormed v_rhs)
    {i : Nat} (hi : i ≤ k_step) {π₁ π₂ : Stack}
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    ObsRefinesK i
      (.compute π₁ ρ₁ t_body)
      (.compute π₂ ρ₂ (substTerm pos t_rhs t_body)) := by
  induction sz generalizing t_body i π₁ π₂ with
  | zero => exfalso; cases h_strict <;> simp [Term._sizeOf_inst] at h_sz
  | succ n ih_sz =>
    match h_strict with
    | .var =>
      -- t_body = .Var pos. substTerm pos t_rhs (.Var pos) = t_rhs.
      simp only [substTerm, ite_true]
      have h_var_step : steps 1 (.compute π₁ ρ₁ (.Var pos)) = .ret π₁ v_rhs := by
        simp only [steps, step]
        show (match ρ₁.lookup pos with | some v => State.ret π₁ v | none => .error) = _
        rw [hexact]
      have h_r_halt_0 := h_r_halt_multi 0 ρ₂ (by intro n _ _; simp) π₂
      rw [Moist.Verified.SubstRefines.iterShift_zero] at h_r_halt_0
      obtain ⟨m, v_r, hm, hvr_rel⟩ := h_r_halt_0
      have hvr_mono : ValueRefinesK i v_rhs v_r :=
        valueRefinesK_mono hi v_rhs v_r hvr_rel
      exact obsRefinesK_of_steps_left h_var_step
        (obsRefinesK_of_steps_right hm
          (hπ i (Nat.le_refl _) v_rhs v_r hvr_mono))
    | .force (e := e) h_e =>
      have hsz_e : sizeOf e ≤ n := by
        have : sizeOf (Term.Force e) = 1 + sizeOf e := rfl; omega
      simp only [substTerm]
      have hclosed_e : closedAt (d + 1) e = true := by
        simp [closedAt] at hclosed_body; exact hclosed_body
      match i with
      | 0 => exact obsRefinesK_zero_compute
      | i' + 1 =>
        refine obsRefinesK_of_step_compute ?_
        simp only [step]
        have hπ_i' : StackRefK ValueRefinesK i' π₁ π₂ :=
          stackRefK_mono (Nat.le_succ i') hπ
        have hπ_force : StackRefK ValueRefinesK i' (Frame.force :: π₁) (Frame.force :: π₂) := by
          intro j hj v₁ v₂ hv
          match j with
          | 0 => exact Moist.Verified.Equivalence.obsRefinesK_zero_ret
          | j' + 1 =>
            have hπ_j' : StackRefK ValueRefinesK j' π₁ π₂ :=
              stackRefK_mono (show j' ≤ i' from by omega) hπ_i'
            refine Moist.Verified.Equivalence.obsRefinesK_of_step_ret ?_
            match v₁, v₂ with
            | .VDelay body₁ ρ₁', .VDelay body₂ ρ₂' =>
              simp only [step, ValueRefinesK] at hv ⊢
              exact hv j' (by omega) j' (Nat.le_refl _) π₁ π₂ hπ_j'
            | .VBuiltin b₁ args₁ ea₁, .VBuiltin b₂ args₂ ea₂ =>
              simp only [ValueRefinesK] at hv; obtain ⟨rfl, rfl, hargs⟩ := hv
              simp only [step]
              split
              · split
                · rename_i rest _
                  have hval : ValueRefinesK (j' + 1)
                      (.VBuiltin b₁ args₁ rest) (.VBuiltin b₁ args₂ rest) := by
                    simp only [ValueRefinesK]; exact ⟨trivial, trivial, hargs⟩
                  exact obsRefinesK_mono (Nat.le_succ j')
                    (hπ_i' (j' + 1) (by omega) _ _ hval)
                · exact evalBuiltin_compat_refines hargs hπ_j'
              · exact obsRefinesK_error _
            | .VCon _, .VCon _ | .VLam _ _, .VLam _ _ | .VConstr _ _, .VConstr _ _ =>
              simp only [step]; exact obsRefinesK_error _
            | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
            | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
            | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
            | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
            | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
            | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
            | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
            | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
            | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at hv
        exact ih_sz hsz_e h_e hclosed_e (by omega) hπ_force
    | .apply_l (f := f) (x := x) h_f h_free_x =>
      have hsz_f : sizeOf f ≤ n := by
        have : sizeOf (Term.Apply f x) = 1 + sizeOf f + sizeOf x := rfl; omega
      have hclosed_f : closedAt (d + 1) f = true := by
        simp [closedAt] at hclosed_body; exact hclosed_body.1
      have hclosed_x : closedAt (d + 1) x = true := by
        simp [closedAt] at hclosed_body; exact hclosed_body.2
      simp only [substTerm]
      match i with
      | 0 => exact obsRefinesK_zero_compute
      | i' + 1 =>
        refine obsRefinesK_of_step_compute ?_
        simp only [step]
        have hπ_arg : StackRefK ValueRefinesK i'
            (Frame.arg x ρ₁ :: π₁)
            (Frame.arg (substTerm pos t_rhs x) ρ₂ :: π₂) := by
          intro j hj w₁ w₂ hw
          match j with
          | 0 => exact Moist.Verified.Equivalence.obsRefinesK_zero_ret
          | j' + 1 =>
            refine Moist.Verified.Equivalence.obsRefinesK_of_step_ret ?_
            simp only [step]
            have hπ_funV : StackRefK ValueRefinesK j' (Frame.funV w₁ :: π₁) (Frame.funV w₂ :: π₂) := by
              intro j₂ hj₂ u₁ u₂ hu
              match j₂ with
              | 0 => exact Moist.Verified.Equivalence.obsRefinesK_zero_ret
              | j₃ + 1 =>
                have hπ_j₃ : StackRefK ValueRefinesK j₃ π₁ π₂ :=
                  stackRefK_mono (show j₃ ≤ i' + 1 by omega) hπ
                refine Moist.Verified.Equivalence.obsRefinesK_of_step_ret ?_
                match w₁, w₂ with
                | .VLam body₁ ρ₁', .VLam body₂ ρ₂' =>
                  simp only [step, ValueRefinesK] at hw ⊢
                  exact hw j₃ (by omega) u₁ u₂
                    (valueRefinesK_mono (Nat.le_succ j₃) u₁ u₂ hu)
                    j₃ (Nat.le_refl _) π₁ π₂ hπ_j₃
                | .VBuiltin b₁ args₁ ea₁, .VBuiltin b₂ args₂ ea₂ =>
                  simp only [ValueRefinesK] at hw; obtain ⟨rfl, rfl, hargs⟩ := hw
                  simp only [step]
                  split
                  · split
                    · rename_i rest _
                      have hval : ValueRefinesK (j₃ + 1)
                          (.VBuiltin b₁ (u₁ :: args₁) rest) (.VBuiltin b₁ (u₂ :: args₂) rest) := by
                        simp only [ValueRefinesK, ListRel]
                        exact ⟨trivial, trivial,
                          valueRefinesK_mono (Nat.le_succ j₃) u₁ u₂ hu,
                          listRel_valueRefinesK_mono (show j₃ ≤ j' from by omega) hargs⟩
                      have hπ_j₃₁ : StackRefK ValueRefinesK (j₃ + 1) π₁ π₂ :=
                        stackRefK_mono (show j₃ + 1 ≤ i' + 1 by omega) hπ
                      exact obsRefinesK_mono (Nat.le_succ j₃)
                        (hπ_j₃₁ (j₃ + 1) (Nat.le_refl _) _ _ hval)
                    · exact evalBuiltin_compat_refines
                        (by simp only [ListRel]
                            exact ⟨valueRefinesK_mono (Nat.le_succ j₃) u₁ u₂ hu,
                              listRel_valueRefinesK_mono (show j₃ ≤ j' from by omega) hargs⟩)
                        hπ_j₃
                  · exact obsRefinesK_error _
                | .VCon _, .VCon _ | .VDelay _ _, .VDelay _ _
                | .VConstr _ _, .VConstr _ _ =>
                  simp only [step]; exact obsRefinesK_error _
                | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
                | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
                | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
                | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
                | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
                | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
                | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
                | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
                | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at hw
            exact freeOf_obsRefines_fwd_gen (sizeOf x) (Nat.le_refl _) hpos_ge hpos_d h_free_x
              hclosed_x hclosed_rhs henv j' (by omega) j' (Nat.le_refl _)
              (Frame.funV w₁ :: π₁) (Frame.funV w₂ :: π₂) hπ_funV
        exact ih_sz hsz_f h_f hclosed_f (by omega) hπ_arg
    | .apply_r (f := f) (x := x) h_free_f h_x =>
      have hsz_x : sizeOf x ≤ n := by
        have : sizeOf (Term.Apply f x) = 1 + sizeOf f + sizeOf x := rfl; omega
      have hclosed_f : closedAt (d + 1) f = true := by
        simp [closedAt] at hclosed_body; exact hclosed_body.1
      have hclosed_x : closedAt (d + 1) x = true := by
        simp [closedAt] at hclosed_body; exact hclosed_body.2
      simp only [substTerm]
      match i with
      | 0 => exact obsRefinesK_zero_compute
      | i' + 1 =>
        refine obsRefinesK_of_step_compute ?_
        simp only [step]
        have hπ_arg : StackRefK ValueRefinesK i'
            (Frame.arg x ρ₁ :: π₁)
            (Frame.arg (substTerm pos t_rhs x) ρ₂ :: π₂) := by
          intro j hj w₁ w₂ hw
          match j with
          | 0 => exact Moist.Verified.Equivalence.obsRefinesK_zero_ret
          | j' + 1 =>
            refine Moist.Verified.Equivalence.obsRefinesK_of_step_ret ?_
            simp only [step]
            have hπ_funV : StackRefK ValueRefinesK j' (Frame.funV w₁ :: π₁) (Frame.funV w₂ :: π₂) := by
              intro j₂ hj₂ u₁ u₂ hu
              match j₂ with
              | 0 => exact Moist.Verified.Equivalence.obsRefinesK_zero_ret
              | j₃ + 1 =>
                have hπ_j₃ : StackRefK ValueRefinesK j₃ π₁ π₂ :=
                  stackRefK_mono (show j₃ ≤ i' + 1 by omega) hπ
                refine Moist.Verified.Equivalence.obsRefinesK_of_step_ret ?_
                match w₁, w₂ with
                | .VLam body₁ ρ₁', .VLam body₂ ρ₂' =>
                  simp only [step, ValueRefinesK] at hw ⊢
                  exact hw j₃ (by omega) u₁ u₂
                    (valueRefinesK_mono (Nat.le_succ j₃) u₁ u₂ hu)
                    j₃ (Nat.le_refl _) π₁ π₂ hπ_j₃
                | .VBuiltin b₁ args₁ ea₁, .VBuiltin b₂ args₂ ea₂ =>
                  simp only [ValueRefinesK] at hw; obtain ⟨rfl, rfl, hargs⟩ := hw
                  simp only [step]
                  split
                  · split
                    · rename_i rest _
                      have hval : ValueRefinesK (j₃ + 1)
                          (.VBuiltin b₁ (u₁ :: args₁) rest) (.VBuiltin b₁ (u₂ :: args₂) rest) := by
                        simp only [ValueRefinesK, ListRel]
                        exact ⟨trivial, trivial,
                          valueRefinesK_mono (Nat.le_succ j₃) u₁ u₂ hu,
                          listRel_valueRefinesK_mono (show j₃ ≤ j' from by omega) hargs⟩
                      have hπ_j₃₁ : StackRefK ValueRefinesK (j₃ + 1) π₁ π₂ :=
                        stackRefK_mono (show j₃ + 1 ≤ i' + 1 by omega) hπ
                      exact obsRefinesK_mono (Nat.le_succ j₃)
                        (hπ_j₃₁ (j₃ + 1) (Nat.le_refl _) _ _ hval)
                    · exact evalBuiltin_compat_refines
                        (by simp only [ListRel]
                            exact ⟨valueRefinesK_mono (Nat.le_succ j₃) u₁ u₂ hu,
                              listRel_valueRefinesK_mono (show j₃ ≤ j' from by omega) hargs⟩)
                        hπ_j₃
                  · exact obsRefinesK_error _
                | .VCon _, .VCon _ | .VDelay _ _, .VDelay _ _
                | .VConstr _ _, .VConstr _ _ =>
                  simp only [step]; exact obsRefinesK_error _
                | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
                | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
                | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
                | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
                | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
                | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
                | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
                | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
                | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at hw
            exact ih_sz hsz_x h_x hclosed_x (by omega) hπ_funV
        exact freeOf_obsRefines_fwd_gen (sizeOf f) (Nat.le_refl _) hpos_ge hpos_d h_free_f
          hclosed_f hclosed_rhs henv i' (by omega) i' (Nat.le_refl _)
          (Frame.arg x ρ₁ :: π₁)
          (Frame.arg (substTerm pos t_rhs x) ρ₂ :: π₂) hπ_arg
    | .case_scrut (scrut := scrut) (alts := alts) h_scrut h_free_alts =>
      have hsz_scrut : sizeOf scrut ≤ n := by
        have : sizeOf (Term.Case scrut alts) = 1 + sizeOf scrut + sizeOf alts := by
          simp [Term._sizeOf_inst, List._sizeOf_inst]
        omega
      have hclosed_scrut : closedAt (d + 1) scrut = true := by
        simp [closedAt] at hclosed_body; exact hclosed_body.1
      have hclosed_alts : closedAtList (d + 1) alts = true := by
        simp [closedAt] at hclosed_body; exact hclosed_body.2
      simp only [substTerm]
      match i with
      | 0 => exact obsRefinesK_zero_compute
      | i' + 1 =>
        refine obsRefinesK_of_step_compute ?_
        simp only [step]
        have h_subst_len : (substTermList pos t_rhs alts).length = alts.length :=
          substTermList_length pos t_rhs alts
        have hπ_case : StackRefK ValueRefinesK i'
            (Frame.caseScrutinee alts ρ₁ :: π₁)
            (Frame.caseScrutinee (substTermList pos t_rhs alts) ρ₂ :: π₂) := by
          intro j hj v₁ v₂ hv
          match j with
          | 0 => exact Moist.Verified.Equivalence.obsRefinesK_zero_ret
          | j' + 1 =>
            have hπ_j' : StackRefK ValueRefinesK j' π₁ π₂ :=
              stackRefK_mono (show j' ≤ i' + 1 by omega) hπ
            refine Moist.Verified.Equivalence.obsRefinesK_of_step_ret ?_
            match v₁, v₂ with
            | .VConstr tag₁ fields₁, .VConstr tag₂ fields₂ =>
              simp only [ValueRefinesK] at hv; obtain ⟨rfl, hfields_v⟩ := hv
              simp only [step]
              split
              · rename_i alt₁ halt₁
                have hsome₁ := List.getElem?_eq_some_iff.mp halt₁
                have hi₁ : tag₁ < alts.length := hsome₁.1
                have hi₂ : tag₁ < (substTermList pos t_rhs alts).length := by omega
                have halt₂ : (substTermList pos t_rhs alts)[tag₁]? =
                    some ((substTermList pos t_rhs alts)[tag₁]) :=
                  List.getElem?_eq_some_iff.mpr ⟨hi₂, rfl⟩
                rw [halt₂]; simp only []
                rw [substTermList_getElem pos t_rhs alts tag₁ hi₁,
                    show alt₁ = alts[tag₁] from hsome₁.2.symm]
                exact freeOf_obsRefines_fwd_gen (sizeOf alts[tag₁]) (Nat.le_refl _)
                  hpos_ge hpos_d (freeOfList_elem h_free_alts hi₁)
                  (closedAtList_elem' hclosed_alts hi₁)
                  hclosed_rhs henv j' (by omega) j' (Nat.le_refl _) _ _
                  (applyArgFrames_stackRefK
                    (Moist.Verified.Equivalence.listRel_mono
                      (fun a b h => valueRefinesK_mono (Nat.le_refl _) a b h) hfields_v)
                    hπ_j')
              · rename_i hnone₁
                have hnone₂ : (substTermList pos t_rhs alts)[tag₁]? = none := by
                  rw [List.getElem?_eq_none_iff] at hnone₁ ⊢; omega
                rw [hnone₂]; simp only []; exact obsRefinesK_error _
            | .VCon c₁, .VCon c₂ =>
              simp only [ValueRefinesK] at hv; subst hv
              simp only [step]
              split
              · rename_i tag numCtors fields htag
                split
                · rename_i h_check
                  have h_check_r : (decide (numCtors > 0) &&
                      decide ((substTermList pos t_rhs alts).length > numCtors)) = true := by
                    rw [h_subst_len]; exact h_check
                  simp only [h_check_r]; exact obsRefinesK_error _
                · rename_i h_check
                  have h_check_r : ¬(decide (numCtors > 0) &&
                      decide ((substTermList pos t_rhs alts).length > numCtors)) = true := by
                    rw [h_subst_len]; exact h_check
                  simp only [show (decide (numCtors > 0) &&
                      decide ((substTermList pos t_rhs alts).length > numCtors)) = false from
                    Bool.eq_false_iff.mpr h_check_r]
                  split
                  · rename_i alt₁ halt₁
                    have hsome₁ := List.getElem?_eq_some_iff.mp halt₁
                    have hi₁ : tag < alts.length := hsome₁.1
                    have hi₂ : tag < (substTermList pos t_rhs alts).length := by omega
                    have halt₂ : (substTermList pos t_rhs alts)[tag]? =
                        some ((substTermList pos t_rhs alts)[tag]) :=
                      List.getElem?_eq_some_iff.mpr ⟨hi₂, rfl⟩
                    rw [halt₂]; simp only []
                    rw [substTermList_getElem pos t_rhs alts tag hi₁,
                        show alt₁ = alts[tag] from hsome₁.2.symm]
                    have hfields_vcon := constToTagAndFields_fields_vcon c₁
                    rw [htag] at hfields_vcon
                    exact freeOf_obsRefines_fwd_gen (sizeOf alts[tag]) (Nat.le_refl _)
                      hpos_ge hpos_d (freeOfList_elem h_free_alts hi₁)
                      (closedAtList_elem' hclosed_alts hi₁)
                      hclosed_rhs henv j' (by omega) j' (Nat.le_refl _) _ _
                      (applyArgFrames_stackRefK
                        (listRel_refl_vcon_refines j' fields hfields_vcon)
                        hπ_j')
                  · rename_i hnone₁
                    have hnone₂ : (substTermList pos t_rhs alts)[tag]? = none := by
                      rw [List.getElem?_eq_none_iff] at hnone₁ ⊢; omega
                    rw [hnone₂]; simp only []; exact obsRefinesK_error _
              · exact obsRefinesK_error _
            | .VLam _ _, .VLam _ _ | .VDelay _ _, .VDelay _ _
            | .VBuiltin _ _ _, .VBuiltin _ _ _ =>
              simp only [step]; exact obsRefinesK_error _
            | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
            | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
            | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
            | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
            | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
            | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
            | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
            | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
            | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at hv
        exact ih_sz hsz_scrut h_scrut hclosed_scrut (by omega) hπ_case
    | .constr (tag := tag) (args := t :: ts) h_args =>
      simp only [substTerm]
      match i with
      | 0 => exact obsRefinesK_zero_compute
      | i' + 1 =>
        refine obsRefinesK_of_step_compute ?_
        simp only [step, substTermList]
        have hclosed_t : closedAt (d + 1) t = true := by
          simp [closedAt, closedAtList] at hclosed_body; exact hclosed_body.1
        have hclosed_ts : closedAtList (d + 1) ts = true := by
          simp [closedAt, closedAtList] at hclosed_body; exact hclosed_body.2
        have hsz_args : sizeOf t + sizeOf ts ≤ n := by
          have : sizeOf (Term.Constr tag (t :: ts)) =
              1 + sizeOf tag + (1 + sizeOf t + sizeOf ts) := by
            simp [Term._sizeOf_inst, instSizeOfNat, List._sizeOf_inst]
          omega
        have constrField_freeOf_stackRefK :
            ∀ (ms : List Term),
              freeOfList pos ms = true →
              closedAtList (d + 1) ms = true →
              1 + sizeOf ms ≤ n →
              ∀ {j_cf : Nat},
                j_cf ≤ i' →
                ∀ {done₁ done₂ : List CekValue},
                  ListRel (ValueRefinesK j_cf) done₁ done₂ →
                  StackRefK ValueRefinesK j_cf
                    (Frame.constrField tag done₁ ms ρ₁ :: π₁)
                    (Frame.constrField tag done₂ (substTermList pos t_rhs ms) ρ₂ :: π₂) := by
          intro ms
          induction ms with
          | nil =>
            intro _ _ _ j_cf hj_cf done₁ done₂ hdone
            intro j hj v₁ v₂ hv
            match j with
            | 0 => exact Moist.Verified.Equivalence.obsRefinesK_zero_ret
            | j' + 1 =>
              refine Moist.Verified.Equivalence.obsRefinesK_of_step_ret ?_
              simp only [substTermList, step]
              have hj'_le : j' ≤ i' + 1 :=
                Nat.le_succ_of_le (Nat.le_of_succ_le (Nat.le_trans hj hj_cf))
              have hπ_base : StackRefK ValueRefinesK j' π₁ π₂ :=
                stackRefK_mono hj'_le hπ
              have hrev : ListRel (ValueRefinesK j')
                  ((v₁ :: done₁).reverse) ((v₂ :: done₂).reverse) := by
                simp only [List.reverse_cons]
                exact Moist.Verified.Equivalence.listRel_append
                  (Moist.Verified.Equivalence.listRel_reverse
                    (Moist.Verified.Equivalence.listRel_mono
                      (fun a b h => valueRefinesK_mono (show j' ≤ j_cf by omega) a b h) hdone))
                  ⟨valueRefinesK_mono (Nat.le_succ j') v₁ v₂ hv, trivial⟩
              have hval : ValueRefinesK (j' + 1)
                  (.VConstr tag ((v₁ :: done₁).reverse))
                  (.VConstr tag ((v₂ :: done₂).reverse)) := by
                cases j' with
                | zero => simp only [ValueRefinesK]; exact ⟨trivial, hrev⟩
                | succ m => simp only [ValueRefinesK]; exact ⟨trivial, hrev⟩
              have hπ_j1 : StackRefK ValueRefinesK (j' + 1) π₁ π₂ :=
                stackRefK_mono (show j' + 1 ≤ i' + 1 from by
                  exact Nat.succ_le_succ (Nat.le_of_succ_le (Nat.le_trans hj hj_cf))) hπ
              exact obsRefinesK_mono (Nat.le_succ j')
                (hπ_j1 (j' + 1) (Nat.le_refl _) _ _ hval)
          | cons m ms' ih_ms =>
            intro hfree_ms hclosed_ms hsz_ms j_cf hj_cf done₁ done₂ hdone
            simp [freeOfList] at hfree_ms
            simp [closedAtList] at hclosed_ms
            intro j hj v₁ v₂ hv
            match j with
            | 0 => exact Moist.Verified.Equivalence.obsRefinesK_zero_ret
            | j' + 1 =>
              refine Moist.Verified.Equivalence.obsRefinesK_of_step_ret ?_
              simp only [substTermList, step]
              have hj'_le_jcf : j' ≤ j_cf :=
                Nat.le_of_lt (Nat.lt_of_succ_le hj)
              have hj'_le_i' : j' ≤ i' := Nat.le_trans hj'_le_jcf hj_cf
              have hdone' : ListRel (ValueRefinesK j') (v₁ :: done₁) (v₂ :: done₂) :=
                ⟨valueRefinesK_mono (Nat.le_succ j') v₁ v₂ hv,
                 Moist.Verified.Equivalence.listRel_mono
                   (fun a b h => valueRefinesK_mono hj'_le_jcf a b h) hdone⟩
              have hπ_next := ih_ms hfree_ms.2 hclosed_ms.2
                (show 1 + sizeOf ms' ≤ n by
                  have : sizeOf (m :: ms') ≥ 1 + sizeOf ms' := by simp
                  omega)
                hj'_le_i' hdone'
              exact freeOf_obsRefines_fwd_gen (sizeOf m) (Nat.le_refl _)
                hpos_ge hpos_d hfree_ms.1 hclosed_ms.1 hclosed_rhs henv
                j' (by omega) j' (Nat.le_refl _) _ _ hπ_next
        match h_args with
        | .head h_t h_free_ts =>
          have hπ_cf := constrField_freeOf_stackRefK ts h_free_ts hclosed_ts
            (show 1 + sizeOf ts ≤ n by have := term_sizeOf_pos t; omega)
            (Nat.le_refl i') (done₁ := []) (done₂ := []) (by simp [ListRel])
          exact ih_sz (show sizeOf t ≤ n by omega) h_t hclosed_t (by omega) hπ_cf
        | .tail h_free_t h_rest =>
          have constrField_occ_stackRefK :
              ∀ (ms : List Term),
                SingleOccList pos ms →
                closedAtList (d + 1) ms = true →
                1 + sizeOf ms ≤ n →
                ∀ {j_cf : Nat},
                  j_cf ≤ i' →
                  ∀ {done₁ done₂ : List CekValue},
                    ListRel (ValueRefinesK j_cf) done₁ done₂ →
                    StackRefK ValueRefinesK j_cf
                      (Frame.constrField tag done₁ ms ρ₁ :: π₁)
                      (Frame.constrField tag done₂ (substTermList pos t_rhs ms) ρ₂ :: π₂) := by
            intro ms
            induction ms with
            | nil => intro h_occ; exact absurd h_occ (by intro h; cases h)
            | cons m ms' ih_ms =>
              intro h_occ hclosed_ms hsz_ms j_cf hj_cf done₁ done₂ hdone
              simp [closedAtList] at hclosed_ms
              intro j hj v₁ v₂ hv
              match j with
              | 0 => exact Moist.Verified.Equivalence.obsRefinesK_zero_ret
              | j' + 1 =>
                refine Moist.Verified.Equivalence.obsRefinesK_of_step_ret ?_
                simp only [substTermList, step]
                have hj'_le_jcf : j' ≤ j_cf :=
                  Nat.le_of_lt (Nat.lt_of_succ_le hj)
                have hj'_le_i' : j' ≤ i' := Nat.le_trans hj'_le_jcf hj_cf
                have hdone' : ListRel (ValueRefinesK j') (v₁ :: done₁) (v₂ :: done₂) :=
                  ⟨valueRefinesK_mono (Nat.le_succ j') v₁ v₂ hv,
                   Moist.Verified.Equivalence.listRel_mono
                     (fun a b h => valueRefinesK_mono hj'_le_jcf a b h) hdone⟩
                match h_occ with
                | .head h_m h_free_ms' =>
                  have hπ_next := constrField_freeOf_stackRefK ms' h_free_ms' hclosed_ms.2
                    (show 1 + sizeOf ms' ≤ n by
                      have : sizeOf (m :: ms') ≥ 1 + sizeOf ms' := by simp
                      omega) hj'_le_i' hdone'
                  exact ih_sz (show sizeOf m ≤ n by
                    have : sizeOf (m :: ms') ≥ 1 + sizeOf m := by simp
                    omega) h_m hclosed_ms.1 (by omega) hπ_next
                | .tail h_free_m h_rest' =>
                  have hπ_next := ih_ms h_rest' hclosed_ms.2
                    (show 1 + sizeOf ms' ≤ n by
                      have : sizeOf (m :: ms') ≥ 1 + sizeOf ms' := by simp
                      omega) hj'_le_i' hdone'
                  exact freeOf_obsRefines_fwd_gen (sizeOf m) (Nat.le_refl _)
                    hpos_ge hpos_d h_free_m hclosed_ms.1 hclosed_rhs henv
                    j' (by omega) j' (Nat.le_refl _) _ _ hπ_next
          have hπ_cf := constrField_occ_stackRefK ts h_rest hclosed_ts
            (show 1 + sizeOf ts ≤ n by have := term_sizeOf_pos t; omega)
            (Nat.le_refl i') (done₁ := []) (done₂ := []) (by simp [ListRel])
          exact freeOf_obsRefines_fwd_gen (sizeOf t) (Nat.le_refl _)
            hpos_ge hpos_d h_free_t hclosed_t hclosed_rhs henv
            i' (by omega) i' (Nat.le_refl _) _ _ hπ_cf
    | .let_body (body := body) (rhs := rhs_inner) h_body h_free =>
      -- t_body = .Apply (.Lam 0 body) rhs_inner, with
      --   h_body : StrictSingleOcc 2 body
      --   h_free : freeOf 1 rhs_inner
      -- After `simp only [substTerm]`, RHS becomes:
      --   .Apply (.Lam 0 (substTerm 2 (shift t_rhs) body)) (substTerm pos t_rhs rhs_inner)
      -- Strategy:
      --   1. Advance both sides by 3 steps (Apply → arg frame → Lam → ret → funV).
      --   2. Apply `freeOf_obsRefines_fwd` to `rhs_inner` via funV-frame StackRefK.
      --   3. The funV-frame StackRefK reduces to VLam ValueRefinesK.
      --   4. For VLam ValueRefinesK, invoke `substRefinesR_body` at pos=2,
      --      constructing `RHaltsRelN (shift t_rhs) v_rhs _ (d+1)` from h_ret.
      simp only [substTerm]
      -- Sizes and closedness
      have hsz_rhs_inner : sizeOf rhs_inner ≤ n := by
        have h_apply : sizeOf (Term.Apply (Term.Lam 0 body) rhs_inner) =
            1 + sizeOf (Term.Lam 0 body) + sizeOf rhs_inner := rfl
        have h_lam_pos : sizeOf (Term.Lam 0 body) ≥ 1 := by
          have : sizeOf (Term.Lam 0 body) = 1 + sizeOf (0 : Nat) + sizeOf body := rfl
          omega
        omega
      have hclosed_body_body : Moist.Verified.closedAt (d + 2) body = true := by
        simp [Moist.Verified.closedAt] at hclosed_body; exact hclosed_body.1
      have hclosed_rhs_inner : Moist.Verified.closedAt (d + 1) rhs_inner = true := by
        simp [Moist.Verified.closedAt] at hclosed_body; exact hclosed_body.2
      -- Shorthand for the substituted body term (expanded form matches the goal)
      let subst_body_term : Term := Moist.Verified.substTerm (pos + 1)
          (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_rhs) body
      show ObsRefinesK i
          (.compute π₁ ρ₁ (.Apply (.Lam 0 body) rhs_inner))
          (.compute π₂ ρ₂
            (.Apply (.Lam 0 subst_body_term)
                    (Moist.Verified.substTerm pos t_rhs rhs_inner)))
      -- Advance each side by 3 steps
      have h_step_L : Moist.Verified.Equivalence.steps 3
          (.compute π₁ ρ₁ (.Apply (.Lam 0 body) rhs_inner)) =
          .compute (Frame.funV (.VLam body ρ₁) :: π₁)
            ρ₁ rhs_inner := by
        simp [Moist.Verified.Equivalence.steps, step]
      have h_step_R : Moist.Verified.Equivalence.steps 3
          (.compute π₂ ρ₂
            (.Apply (.Lam 0 subst_body_term)
                    (Moist.Verified.substTerm pos t_rhs rhs_inner))) =
          .compute (Frame.funV (.VLam subst_body_term ρ₂) :: π₂)
            ρ₂ (Moist.Verified.substTerm pos t_rhs rhs_inner) := by
        simp [Moist.Verified.Equivalence.steps, step]
      -- Use the lifts to reduce to the post-3-step obligation
      apply obsRefinesK_of_steps_left h_step_L
      apply obsRefinesK_of_steps_right h_step_R
      -- Now the goal is:
      --   ObsRefinesK i (compute (funV VLam_L :: π₁) ρ₁ rhs_inner)
      --                (compute (funV VLam_R :: π₂) ρ₂ (substTerm pos t_rhs rhs_inner))
      -- where VLam_L = VLam body ρ₁, VLam_R = VLam subst_body_term ρ.
      -- We use `freeOf_obsRefines_fwd` on `rhs_inner` with the funV-frame StackRefK.
      -- Construct the funV-frame StackRefK, which requires VLam ValueRefinesK.
      have hclosed_shifted_rhs :
          Moist.Verified.closedAt (d + 1)
            (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_rhs) = true :=
        Moist.Verified.BetaValueRefines.closedAt_shift hclosed_rhs
      have hsz_body : sizeOf body ≤ n := by
        have h_lam : sizeOf (Term.Lam 0 body) = 1 + sizeOf (0 : Nat) + sizeOf body := rfl
        have h_apply : sizeOf (Term.Apply (Term.Lam 0 body) rhs_inner) =
            1 + sizeOf (Term.Lam 0 body) + sizeOf rhs_inner := rfl
        omega
      -- Build the StackRefK ValueRefinesK on funV frames directly
      have hπ_funV : StackRefK ValueRefinesK i
          (Frame.funV (.VLam body ρ₁) :: π₁)
          (Frame.funV (.VLam subst_body_term ρ₂) :: π₂) := by
        intro j hj w₁ w₂ hw
        match j with
        | 0 => exact Moist.Verified.Equivalence.obsRefinesK_zero_ret
        | j' + 1 =>
          refine Moist.Verified.Equivalence.obsRefinesK_of_step_ret ?_
          simp only [step]
          -- hj : j'+1 ≤ i, hi : i ≤ k_step, so j' ≤ k_step
          have hj'_le_k : j' ≤ k_step := by omega
          -- Build SubstEnvRef (pos+1) v_rhs j' (d+2) (ρ₁.extend w₁) (ρ₂.extend w₂)
          have henv_ext :
              Moist.Verified.BetaValueRefines.SubstEnvRef (pos + 1) v_rhs j' (d + 2)
                (ρ₁.extend w₁) (ρ₂.extend w₂) :=
            Moist.Verified.BetaValueRefines.substEnvRef_extend hpos_ge
              (valueRefinesK_mono (Nat.le_succ j') w₁ w₂ hw)
              (Moist.Verified.BetaValueRefines.substEnvRef_mono hj'_le_k henv)
          -- Build (ρ₁.extend w₁).lookup (pos+1) = some v_rhs
          have hexact_ext : (ρ₁.extend w₁).lookup (pos + 1) = some v_rhs := by
            rw [Moist.Verified.BetaValueRefines.extend_lookup_succ ρ₁ w₁ pos hpos_ge]
            exact hexact
          -- Build h_r_halt_multi for the recursive call at d+1, ρ₂.extend w₂
          -- Key: iterShift K (shift t_rhs) = iterShift (K+1) t_rhs,
          -- and lookup conditions at d+1 on (ρ₂.extend w₂) reduce to d on ρ₂
          have h_r_halt_multi' : ∀ (K : Nat) (ρ_ext : CekEnv),
              (∀ n, 0 < n → n ≤ d + 1 → ρ_ext.lookup (n + K) = (ρ₂.extend w₂).lookup n) →
              ∀ π, ∃ m v',
              steps m (.compute π ρ_ext
                (Moist.Verified.SubstRefines.iterShift K
                  (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_rhs))) = .ret π v' ∧
              ValueRefinesK j' v_rhs v' := by
            intro K ρ_ext h_lookup π
            rw [Moist.Verified.SubstRefines.iterShift_shift]
            have h_lookup_base : ∀ n, 0 < n → n ≤ d →
                ρ_ext.lookup (n + (K + 1)) = ρ₂.lookup n := by
              intro n hn hnd
              have := h_lookup (n + 1) (by omega) (by omega)
              rw [Moist.Verified.BetaValueRefines.extend_lookup_succ ρ₂ w₂ n hn] at this
              rwa [show n + 1 + K = n + (K + 1) from by omega] at this
            obtain ⟨m, v', hm, hv'⟩ := h_r_halt_multi (K + 1) ρ_ext h_lookup_base π
            exact ⟨m, v', hm, valueRefinesK_mono hj'_le_k v_rhs v' hv'⟩
          -- Recurse on body with pos+1
          exact body_subst_obsRefinesK_gen n
            (d := d + 1) (pos := pos + 1)
            (t_body := body)
            (t_rhs := Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_rhs)
            (ρ₁ := ρ₁.extend w₁) (ρ₂ := ρ₂.extend w₂)
            (v_rhs := v_rhs) (k_step := j')
            hsz_body (by omega) (by omega) h_body
            hclosed_body_body hclosed_shifted_rhs
            henv_ext hexact_ext h_r_halt_multi'
            (by simp [CekEnv.extend, CekEnv.length]; omega)
            (by simp [CekEnv.extend, CekEnv.length]; omega)
            hvwf (Nat.le_refl j')
            (stackRefK_mono (show j' ≤ i by omega) hπ)
      -- Apply freeOf_obsRefines_fwd_gen on rhs_inner (freeOf pos rhs_inner)
      exact freeOf_obsRefines_fwd_gen (sizeOf rhs_inner) (Nat.le_refl _)
        hpos_ge hpos_d h_free hclosed_rhs_inner hclosed_rhs henv
        i (by omega) i (Nat.le_refl _) _ _ hπ_funV
    | .lam (name := name) (body := inner) h_inner =>
      simp only [substTerm]
      have hclosed_inner : closedAt (d + 2) inner = true := by
        simp [closedAt] at hclosed_body; exact hclosed_body
      match i with
      | 0 => exact obsRefinesK_zero_compute
      | i' + 1 =>
        refine obsRefinesK_of_step_compute ?_
        simp only [step]
        apply (stackRefK_mono (Nat.le_succ i') hπ) i' (Nat.le_refl _)
        match i' with
        | 0 => simp [ValueRefinesK]
        | i'' + 1 =>
          unfold ValueRefinesK
          intro j hj v₁ v₂ hv i_inner hi_inner π₁' π₂' hπ'
          have hj_le : j ≤ k_step := by omega
          have henv_ext := Moist.Verified.BetaValueRefines.substEnvRef_extend hpos_ge hv
            (Moist.Verified.BetaValueRefines.substEnvRef_mono (show j ≤ k_step by omega) henv)
          have hexact_ext : (ρ₁.extend v₁).lookup (pos + 1) = some v_rhs := by
            rw [Moist.Verified.BetaValueRefines.extend_lookup_succ ρ₁ v₁ pos (by omega), hexact]
          have h_r_halt_multi' : ∀ K ρ_ext,
              (∀ n, 0 < n → n ≤ d + 1 → ρ_ext.lookup (n + K) = (ρ₂.extend v₂).lookup n) →
              ∀ π, ∃ m v',
                steps m (.compute π ρ_ext
                  (Moist.Verified.SubstRefines.iterShift K
                    (renameTerm (shiftRename 1) t_rhs))) = .ret π v' ∧
                ValueRefinesK j v_rhs v' := by
            intro K ρ_ext h_lookup π
            have h_lookup_base : ∀ n, 0 < n → n ≤ d →
                ρ_ext.lookup (n + (K + 1)) = ρ₂.lookup n := by
              intro n hn hnd
              rw [show n + (K + 1) = (n + 1) + K from by omega,
                  h_lookup (n + 1) (by omega) (by omega),
                  Moist.Verified.BetaValueRefines.extend_lookup_succ ρ₂ v₂ n (by omega)]
            rw [Moist.Verified.SubstRefines.iterShift_shift]
            obtain ⟨m, v', hm, hv'⟩ := h_r_halt_multi (K + 1) ρ_ext h_lookup_base π
            exact ⟨m, v', hm, valueRefinesK_mono (show j ≤ k_step by omega) v_rhs v' hv'⟩
          exact body_subst_obsRefinesK_gen n
            (d := d + 1) (pos := pos + 1) (t_body := inner)
            (t_rhs := renameTerm (shiftRename 1) t_rhs)
            (ρ₁ := ρ₁.extend v₁) (ρ₂ := ρ₂.extend v₂)
            (v_rhs := v_rhs) (k_step := j)
            (by have : sizeOf (Term.Lam name inner) = 1 + sizeOf name + sizeOf inner := by
                  simp [Term._sizeOf_inst]
                omega)
            (by omega) (by omega) h_inner hclosed_inner
            (Moist.Verified.BetaValueRefines.closedAt_shift hclosed_rhs)
            henv_ext hexact_ext h_r_halt_multi'
            (by simp [CekEnv.extend, CekEnv.length]; omega)
            (by simp [CekEnv.extend, CekEnv.length]; omega)
            hvwf hi_inner hπ'
    | .delay (body := inner) h_inner =>
      simp only [substTerm]
      have hclosed_inner : closedAt (d + 1) inner = true := by
        simp [closedAt] at hclosed_body; exact hclosed_body
      match i with
      | 0 => exact obsRefinesK_zero_compute
      | i' + 1 =>
        refine obsRefinesK_of_step_compute ?_
        simp only [step]
        apply (stackRefK_mono (Nat.le_succ i') hπ) i' (Nat.le_refl _)
        match i' with
        | 0 => simp [ValueRefinesK]
        | i'' + 1 =>
          unfold ValueRefinesK
          intro j hj i_inner hi_inner π₁' π₂' hπ'
          exact body_subst_obsRefinesK_gen n
            (d := d) (pos := pos) (t_body := inner)
            (t_rhs := t_rhs) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
            (v_rhs := v_rhs) (k_step := j)
            (by have : sizeOf (Term.Delay inner) = 1 + sizeOf inner := by
                  simp [Term._sizeOf_inst]
                omega)
            hpos_ge hpos_d h_inner hclosed_inner hclosed_rhs
            (Moist.Verified.BetaValueRefines.substEnvRef_mono (show j ≤ k_step by omega) henv)
            hexact
            (fun K ρ_ext h_lookup π => by
              obtain ⟨m, v', hm, hv'⟩ := h_r_halt_multi K ρ_ext h_lookup π
              exact ⟨m, v', hm, valueRefinesK_mono (show j ≤ k_step by omega) v_rhs v' hv'⟩)
            hlen_L hlen_R hvwf hi_inner hπ'
    | .case_alt (scrut := scrut) (alts := alts) h_free_scrut h_alts =>
      have hsz_scrut : sizeOf scrut ≤ n := by
        have : sizeOf (Term.Case scrut alts) = 1 + sizeOf scrut + sizeOf alts := by
          simp [Term._sizeOf_inst, List._sizeOf_inst]
        omega
      have hclosed_scrut : closedAt (d + 1) scrut = true := by
        simp [closedAt] at hclosed_body; exact hclosed_body.1
      have hclosed_alts : closedAtList (d + 1) alts = true := by
        simp [closedAt] at hclosed_body; exact hclosed_body.2
      simp only [substTerm]
      match i with
      | 0 => exact obsRefinesK_zero_compute
      | i' + 1 =>
        refine obsRefinesK_of_step_compute ?_
        simp only [step]
        have h_subst_len : (substTermList pos t_rhs alts).length = alts.length :=
          substTermList_length pos t_rhs alts
        have alt_obsRefinesK (tag : Nat) (hi_tag : tag < alts.length)
            {j' : Nat} (hj'_le : j' ≤ i')
            {π₁' π₂' : Stack} (hπ' : StackRefK ValueRefinesK j' π₁' π₂') :
            ObsRefinesK j'
              (.compute π₁' ρ₁ (alts[tag]'hi_tag))
              (.compute π₂' ρ₂ (substTerm pos t_rhs (alts[tag]'hi_tag))) := by
          have h_elem := h_alts.elem_singleOcc_or_freeOf tag hi_tag
          have hclosed_elem := closedAtList_elem' hclosed_alts hi_tag
          cases h_elem with
          | inl h_occ =>
            have hsz_elem : sizeOf (alts[tag]'hi_tag) ≤ n := by
              have : sizeOf (alts[tag]'hi_tag) < 1 + sizeOf alts := by
                exact Nat.lt_of_lt_of_le (List.sizeOf_lt_of_mem (List.getElem_mem hi_tag)) (by omega)
              have : sizeOf (Term.Case scrut alts) = 1 + sizeOf scrut + sizeOf alts := by
                simp [Term._sizeOf_inst, List._sizeOf_inst]
              omega
            exact ih_sz hsz_elem h_occ hclosed_elem (by omega) hπ'
          | inr h_free =>
            exact freeOf_obsRefines_fwd_gen (sizeOf (alts[tag]'hi_tag)) (Nat.le_refl _)
              hpos_ge hpos_d h_free hclosed_elem hclosed_rhs henv
              j' (by omega) j' (Nat.le_refl _) _ _ hπ'
        have hπ_case : StackRefK ValueRefinesK i'
            (Frame.caseScrutinee alts ρ₁ :: π₁)
            (Frame.caseScrutinee (substTermList pos t_rhs alts) ρ₂ :: π₂) := by
          intro j hj v₁ v₂ hv
          match j with
          | 0 => exact Moist.Verified.Equivalence.obsRefinesK_zero_ret
          | j' + 1 =>
            have hπ_j' : StackRefK ValueRefinesK j' π₁ π₂ :=
              stackRefK_mono (show j' ≤ i' + 1 by omega) hπ
            refine Moist.Verified.Equivalence.obsRefinesK_of_step_ret ?_
            match v₁, v₂ with
            | .VConstr tag₁ fields₁, .VConstr tag₂ fields₂ =>
              simp only [ValueRefinesK] at hv; obtain ⟨rfl, hfields_v⟩ := hv
              simp only [step]
              split
              · rename_i alt₁ halt₁
                have hsome₁ := List.getElem?_eq_some_iff.mp halt₁
                have hi₁ : tag₁ < alts.length := hsome₁.1
                have hi₂ : tag₁ < (substTermList pos t_rhs alts).length := by omega
                have halt₂ : (substTermList pos t_rhs alts)[tag₁]? =
                    some ((substTermList pos t_rhs alts)[tag₁]) :=
                  List.getElem?_eq_some_iff.mpr ⟨hi₂, rfl⟩
                rw [halt₂]; simp only []
                rw [substTermList_getElem pos t_rhs alts tag₁ hi₁,
                    show alt₁ = alts[tag₁] from hsome₁.2.symm]
                exact alt_obsRefinesK tag₁ hi₁ (by omega)
                  (applyArgFrames_stackRefK
                    (Moist.Verified.Equivalence.listRel_mono
                      (fun a b h => valueRefinesK_mono (Nat.le_refl _) a b h) hfields_v)
                    hπ_j')
              · rename_i hnone₁
                have hnone₂ : (substTermList pos t_rhs alts)[tag₁]? = none := by
                  rw [List.getElem?_eq_none_iff] at hnone₁ ⊢; omega
                rw [hnone₂]; simp only []; exact obsRefinesK_error _
            | .VCon c₁, .VCon c₂ =>
              simp only [ValueRefinesK] at hv; subst hv
              simp only [step]
              split
              · rename_i tag numCtors fields htag
                split
                · rename_i h_check
                  have h_check_r : (decide (numCtors > 0) &&
                      decide ((substTermList pos t_rhs alts).length > numCtors)) = true := by
                    rw [h_subst_len]; exact h_check
                  simp only [h_check_r]; exact obsRefinesK_error _
                · rename_i h_check
                  have h_check_r : ¬(decide (numCtors > 0) &&
                      decide ((substTermList pos t_rhs alts).length > numCtors)) = true := by
                    rw [h_subst_len]; exact h_check
                  simp only [show (decide (numCtors > 0) &&
                      decide ((substTermList pos t_rhs alts).length > numCtors)) = false from
                    Bool.eq_false_iff.mpr h_check_r]
                  split
                  · rename_i alt₁ halt₁
                    have hsome₁ := List.getElem?_eq_some_iff.mp halt₁
                    have hi₁ : tag < alts.length := hsome₁.1
                    have hi₂ : tag < (substTermList pos t_rhs alts).length := by omega
                    have halt₂ : (substTermList pos t_rhs alts)[tag]? =
                        some ((substTermList pos t_rhs alts)[tag]) :=
                      List.getElem?_eq_some_iff.mpr ⟨hi₂, rfl⟩
                    rw [halt₂]; simp only []
                    rw [substTermList_getElem pos t_rhs alts tag hi₁,
                        show alt₁ = alts[tag] from hsome₁.2.symm]
                    have hfields_vcon := constToTagAndFields_fields_vcon c₁
                    rw [htag] at hfields_vcon
                    exact alt_obsRefinesK tag hi₁ (by omega)
                      (applyArgFrames_stackRefK
                        (listRel_refl_vcon_refines j' fields hfields_vcon)
                        hπ_j')
                  · rename_i hnone₁
                    have hnone₂ : (substTermList pos t_rhs alts)[tag]? = none := by
                      rw [List.getElem?_eq_none_iff] at hnone₁ ⊢; omega
                    rw [hnone₂]; simp only []; exact obsRefinesK_error _
              · exact obsRefinesK_error _
            | .VLam _ _, .VLam _ _ | .VDelay _ _, .VDelay _ _
            | .VBuiltin _ _ _, .VBuiltin _ _ _ =>
              simp only [step]; exact obsRefinesK_error _
            | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
            | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
            | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
            | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
            | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
            | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
            | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
            | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
            | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at hv
        exact freeOf_obsRefines_fwd_gen (sizeOf scrut) (Nat.le_refl _)
          hpos_ge hpos_d h_free_scrut hclosed_scrut hclosed_rhs henv
          i' (by omega) i' (Nat.le_refl _) _ _ hπ_case

open Moist.Verified.Contextual.SoundnessRefines
  (StackRefK ValueRefinesK stackRefK_mono valueRefinesK_mono
   evalBuiltin_compat_refines obsRefinesK_error listRel_valueRefinesK_mono
   applyArgFrames_stackRefK listRel_refl_vcon_refines) in
open Moist.Verified.Equivalence
  (ObsRefinesK obsRefinesK_mono obsRefinesK_of_step_compute
   obsRefinesK_zero_compute obsRefinesK_zero_ret ListRel constToTagAndFields_fields_vcon) in
open Moist.Verified.BetaValueRefines
  (obsRefinesK_of_steps_left obsRefinesK_of_steps_right
   valueRefinesK_refl EnvWellFormed ValueWellFormed stackRefK_refl
   StackWellFormed substTermList_getElem) in
open Moist.Verified (substTermList_length closedAtList) in
private theorem body_subst_multi_obsRefinesK_gen (sz : Nat) {d pos : Nat}
    {t_body t_rhs : Term}
    (h_sz : sizeOf t_body ≤ sz)
    (hpos_ge : 1 ≤ pos) (hpos_d : pos ≤ d + 1)
    (hclosed_body : closedAt (d + 1) t_body = true)
    (hclosed_rhs : closedAt d t_rhs = true)
    {ρ₁ ρ₂ : CekEnv} {v_rhs : CekValue}
    {k_step : Nat}
    (henv : Moist.Verified.BetaValueRefines.SubstEnvRef pos v_rhs k_step (d + 1) ρ₁ ρ₂)
    (hexact : ρ₁.lookup pos = some v_rhs)
    (h_r_halt_multi : ∀ (K : Nat) (ρ_ext : CekEnv),
        (∀ n, 0 < n → n ≤ d → ρ_ext.lookup (n + K) = ρ₂.lookup n) →
        ∀ π, ∃ m v',
          steps m (.compute π ρ_ext
            (Moist.Verified.SubstRefines.iterShift K t_rhs)) = .ret π v' ∧
          ValueRefinesK k_step v_rhs v')
    (hlen_L : d + 1 ≤ ρ₁.length)
    (hlen_R : d ≤ ρ₂.length)
    (hvwf : ValueWellFormed v_rhs)
    {i : Nat} (hi : i ≤ k_step) {π₁ π₂ : Stack}
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    ObsRefinesK i
      (.compute π₁ ρ₁ t_body)
      (.compute π₂ ρ₂ (substTerm pos t_rhs t_body)) := by
  match sz with
  | 0 => exfalso; cases t_body <;> simp [Term._sizeOf_inst] at h_sz
  | n + 1 =>
    have ih_sz {t'} (hs : sizeOf t' ≤ n) (hc : closedAt (d + 1) t' = true)
        {i'} (hi' : i' ≤ k_step) {π₁' π₂'} (hπ' : StackRefK ValueRefinesK i' π₁' π₂') :=
      body_subst_multi_obsRefinesK_gen n hs hpos_ge hpos_d hc hclosed_rhs henv hexact
        h_r_halt_multi hlen_L hlen_R hvwf hi' hπ'
    by_cases h_free : freeOf pos t_body = true
    · exact freeOf_obsRefines_fwd_gen (sizeOf t_body) (Nat.le_refl _)
        hpos_ge hpos_d h_free hclosed_body hclosed_rhs henv i hi i (Nat.le_refl _) _ _ hπ
    · match t_body with
      | .Var k =>
        have hk : k = pos := by simp [freeOf] at h_free; omega
        subst hk
        simp only [substTerm, ite_true]
        have h_var_step : steps 1 (.compute π₁ ρ₁ (.Var k)) = .ret π₁ v_rhs := by
          simp only [steps, step]
          show (match ρ₁.lookup k with | some v => State.ret π₁ v | none => .error) = _
          rw [hexact]
        have h_r_halt_0 := h_r_halt_multi 0 ρ₂ (by intro nn _ _; simp) π₂
        rw [Moist.Verified.SubstRefines.iterShift_zero] at h_r_halt_0
        obtain ⟨m, v_r, hm, hvr_rel⟩ := h_r_halt_0
        exact obsRefinesK_of_steps_left h_var_step
          (obsRefinesK_of_steps_right hm
            (hπ i (Nat.le_refl _) v_rhs v_r (valueRefinesK_mono hi v_rhs v_r hvr_rel)))
      | .Constant _ | .Builtin _ | .Error =>
        exfalso; simp [freeOf] at h_free
      | .Force e =>
        have hsz_e : sizeOf e ≤ n := by
          have : sizeOf (Term.Force e) = 1 + sizeOf e := rfl; omega
        have hclosed_e : closedAt (d + 1) e = true := by
          simp [closedAt] at hclosed_body; exact hclosed_body
        simp only [substTerm]
        match i with
        | 0 => exact obsRefinesK_zero_compute
        | i' + 1 =>
          refine obsRefinesK_of_step_compute ?_; simp only [step]
          have hπ_i' := stackRefK_mono (Nat.le_succ i') hπ
          have hπ_force : StackRefK ValueRefinesK i' (Frame.force :: π₁) (Frame.force :: π₂) := by
            intro j hj v₁ v₂ hv
            match j with
            | 0 => exact obsRefinesK_zero_ret
            | j' + 1 =>
              have hπ_j' := stackRefK_mono (show j' ≤ i' from by omega) hπ_i'
              refine Moist.Verified.Equivalence.obsRefinesK_of_step_ret ?_
              match v₁, v₂ with
              | .VDelay body₁ ρ₁', .VDelay body₂ ρ₂' =>
                simp only [step, ValueRefinesK] at hv ⊢
                exact hv j' (by omega) j' (Nat.le_refl _) π₁ π₂ hπ_j'
              | .VBuiltin b₁ args₁ ea₁, .VBuiltin b₂ args₂ ea₂ =>
                simp only [ValueRefinesK] at hv; obtain ⟨rfl, rfl, hargs⟩ := hv
                simp only [step]; split
                · split
                  · rename_i rest _
                    have hval : ValueRefinesK (j' + 1) (.VBuiltin b₁ args₁ rest) (.VBuiltin b₁ args₂ rest) := by
                      simp only [ValueRefinesK]; exact ⟨trivial, trivial, hargs⟩
                    exact obsRefinesK_mono (Nat.le_succ j') (hπ_i' (j' + 1) (by omega) _ _ hval)
                  · exact evalBuiltin_compat_refines hargs hπ_j'
                · exact obsRefinesK_error _
              | .VCon _, .VCon _ | .VLam _ _, .VLam _ _ | .VConstr _ _, .VConstr _ _ =>
                simp only [step]; exact obsRefinesK_error _
              | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
              | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
              | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
              | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
              | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
              | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
              | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
              | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
              | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at hv
          exact ih_sz hsz_e hclosed_e (by omega) hπ_force
      | .Lam name inner =>
        have hsz_i : sizeOf inner ≤ n := by
          have : sizeOf (Term.Lam name inner) ≥ 1 + sizeOf inner := by
            simp [Term._sizeOf_inst]
          omega
        have hclosed_inner : closedAt (d + 2) inner = true := by
          simp [closedAt] at hclosed_body; exact hclosed_body
        simp only [substTerm]
        match i with
        | 0 => exact obsRefinesK_zero_compute
        | i' + 1 =>
          refine obsRefinesK_of_step_compute ?_; simp only [step]
          apply (stackRefK_mono (Nat.le_succ i') hπ) i' (Nat.le_refl _)
          match i' with
          | 0 => simp [ValueRefinesK]
          | i'' + 1 =>
            unfold ValueRefinesK
            intro j hj v₁ v₂ hv i_inner hi_inner π₁' π₂' hπ'
            have henv_ext := Moist.Verified.BetaValueRefines.substEnvRef_extend hpos_ge hv
              (Moist.Verified.BetaValueRefines.substEnvRef_mono (show j ≤ k_step by omega) henv)
            have hexact_ext : (ρ₁.extend v₁).lookup (pos + 1) = some v_rhs := by
              rw [Moist.Verified.BetaValueRefines.extend_lookup_succ ρ₁ v₁ pos (by omega), hexact]
            have h_r_halt_multi' : ∀ K ρ_ext,
                (∀ n, 0 < n → n ≤ d + 1 → ρ_ext.lookup (n + K) = (ρ₂.extend v₂).lookup n) →
                ∀ π, ∃ m v',
                  steps m (.compute π ρ_ext
                    (Moist.Verified.SubstRefines.iterShift K
                      (renameTerm (shiftRename 1) t_rhs))) = .ret π v' ∧
                  ValueRefinesK j v_rhs v' := by
              intro K ρ_ext h_lookup π
              rw [Moist.Verified.SubstRefines.iterShift_shift]
              obtain ⟨m, v', hm, hv'⟩ := h_r_halt_multi (K + 1) ρ_ext (by
                intro nn hnn hnnd
                rw [show nn + (K + 1) = (nn + 1) + K from by omega,
                    h_lookup (nn + 1) (by omega) (by omega),
                    Moist.Verified.BetaValueRefines.extend_lookup_succ ρ₂ v₂ nn (by omega)]) π
              exact ⟨m, v', hm, valueRefinesK_mono (show j ≤ k_step by omega) v_rhs v' hv'⟩
            exact body_subst_multi_obsRefinesK_gen n
              hsz_i (by omega) (by omega) hclosed_inner
              (Moist.Verified.BetaValueRefines.closedAt_shift hclosed_rhs)
              henv_ext hexact_ext h_r_halt_multi'
              (by simp [CekEnv.extend, CekEnv.length]; omega)
              (by simp [CekEnv.extend, CekEnv.length]; omega)
              hvwf hi_inner hπ'
      | .Delay inner =>
        have hsz_i : sizeOf inner ≤ n := by
          have : sizeOf (Term.Delay inner) = 1 + sizeOf inner := rfl; omega
        have hclosed_inner : closedAt (d + 1) inner = true := by
          simp [closedAt] at hclosed_body; exact hclosed_body
        simp only [substTerm]
        match i with
        | 0 => exact obsRefinesK_zero_compute
        | i' + 1 =>
          refine obsRefinesK_of_step_compute ?_; simp only [step]
          apply (stackRefK_mono (Nat.le_succ i') hπ) i' (Nat.le_refl _)
          match i' with
          | 0 => simp [ValueRefinesK]
          | i'' + 1 =>
            unfold ValueRefinesK
            intro j hj i_inner hi_inner π₁' π₂' hπ'
            exact body_subst_multi_obsRefinesK_gen n
              hsz_i hpos_ge hpos_d hclosed_inner hclosed_rhs
              (Moist.Verified.BetaValueRefines.substEnvRef_mono (show j ≤ k_step by omega) henv)
              hexact
              (fun K ρ_ext h_lookup π => by
                obtain ⟨m, v', hm, hv'⟩ := h_r_halt_multi K ρ_ext h_lookup π
                exact ⟨m, v', hm, valueRefinesK_mono (show j ≤ k_step by omega) v_rhs v' hv'⟩)
              hlen_L hlen_R hvwf hi_inner hπ'
      | .Apply f x =>
        have hsz_f : sizeOf f ≤ n := by
          have : sizeOf (Term.Apply f x) = 1 + sizeOf f + sizeOf x := rfl; omega
        have hsz_x : sizeOf x ≤ n := by
          have : sizeOf (Term.Apply f x) = 1 + sizeOf f + sizeOf x := rfl; omega
        have hclosed_f : closedAt (d + 1) f = true := by
          simp [closedAt] at hclosed_body; exact hclosed_body.1
        have hclosed_x : closedAt (d + 1) x = true := by
          simp [closedAt] at hclosed_body; exact hclosed_body.2
        simp only [substTerm]
        match i with
        | 0 => exact obsRefinesK_zero_compute
        | i' + 1 =>
          refine obsRefinesK_of_step_compute ?_; simp only [step]
          have hπ_arg : StackRefK ValueRefinesK i'
              (Frame.arg x ρ₁ :: π₁)
              (Frame.arg (substTerm pos t_rhs x) ρ₂ :: π₂) := by
            intro j hj w₁ w₂ hw
            match j with
            | 0 => exact obsRefinesK_zero_ret
            | j' + 1 =>
              refine Moist.Verified.Equivalence.obsRefinesK_of_step_ret ?_; simp only [step]
              have hπ_funV : StackRefK ValueRefinesK j'
                  (Frame.funV w₁ :: π₁) (Frame.funV w₂ :: π₂) := by
                intro j₂ hj₂ u₁ u₂ hu
                match j₂ with
                | 0 => exact obsRefinesK_zero_ret
                | j₃ + 1 =>
                  have hπ_j₃ := stackRefK_mono (show j₃ ≤ i' + 1 by omega) hπ
                  refine Moist.Verified.Equivalence.obsRefinesK_of_step_ret ?_
                  match w₁, w₂ with
                  | .VLam body₁ ρ₁', .VLam body₂ ρ₂' =>
                    simp only [step, ValueRefinesK] at hw ⊢
                    exact hw j₃ (by omega) u₁ u₂
                      (valueRefinesK_mono (Nat.le_succ j₃) u₁ u₂ hu)
                      j₃ (Nat.le_refl _) π₁ π₂ hπ_j₃
                  | .VBuiltin b₁ args₁ ea₁, .VBuiltin b₂ args₂ ea₂ =>
                    simp only [ValueRefinesK] at hw; obtain ⟨rfl, rfl, hargs⟩ := hw
                    simp only [step]; split
                    · split
                      · rename_i rest _
                        have hval : ValueRefinesK (j₃ + 1)
                            (.VBuiltin b₁ (u₁ :: args₁) rest) (.VBuiltin b₁ (u₂ :: args₂) rest) := by
                          simp only [ValueRefinesK, ListRel]
                          exact ⟨trivial, trivial,
                            valueRefinesK_mono (Nat.le_succ j₃) u₁ u₂ hu,
                            listRel_valueRefinesK_mono (show j₃ ≤ j' from by omega) hargs⟩
                        exact obsRefinesK_mono (Nat.le_succ j₃)
                          ((stackRefK_mono (show j₃ + 1 ≤ i' + 1 by omega) hπ) (j₃ + 1) (Nat.le_refl _) _ _ hval)
                      · exact evalBuiltin_compat_refines
                          (by simp only [ListRel]; exact ⟨valueRefinesK_mono (Nat.le_succ j₃) u₁ u₂ hu,
                            listRel_valueRefinesK_mono (show j₃ ≤ j' from by omega) hargs⟩)
                          hπ_j₃
                    · exact obsRefinesK_error _
                  | .VCon _, .VCon _ | .VDelay _ _, .VDelay _ _ | .VConstr _ _, .VConstr _ _ =>
                    simp only [step]; exact obsRefinesK_error _
                  | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
                  | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
                  | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
                  | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
                  | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
                  | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
                  | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
                  | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
                  | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at hw
              exact ih_sz hsz_x hclosed_x (by omega) hπ_funV
          exact ih_sz hsz_f hclosed_f (by omega) hπ_arg
      | .Constr tag args =>
        match args with
        | [] =>
          simp only [substTerm]
          match i with
          | 0 => exact obsRefinesK_zero_compute
          | i' + 1 =>
            refine obsRefinesK_of_step_compute ?_
            simp [step, substTermList]
            have hval : ValueRefinesK i' (.VConstr tag []) (.VConstr tag []) := by
              cases i' with
              | zero => simp only [ValueRefinesK]
              | succ m =>
                simp only [ValueRefinesK, ListRel]
                exact ⟨trivial, trivial⟩
            exact hπ i' (by omega) _ _ hval
        | m :: ms =>
          have hclosed_m : closedAt (d + 1) m = true := by
            simp [closedAt, closedAtList] at hclosed_body
            exact hclosed_body.1
          have hclosed_ms : closedAtList (d + 1) ms = true := by
            simp [closedAt, closedAtList] at hclosed_body
            exact hclosed_body.2
          have hsize_constr : sizeOf (Term.Constr tag (m :: ms)) =
              1 + sizeOf tag + (1 + sizeOf m + sizeOf ms) := by
            simp [Term._sizeOf_inst, instSizeOfNat, List._sizeOf_inst]
          have hsz_m : sizeOf m ≤ n := by omega
          have hsz_ms : 1 + sizeOf ms ≤ n := by omega
          simp only [substTerm]
          match i with
          | 0 => exact obsRefinesK_zero_compute
          | i' + 1 =>
            refine obsRefinesK_of_step_compute ?_
            simp [step, substTermList]
            have constrField_stackRefK :
                ∀ (ms' : List Term),
                  closedAtList (d + 1) ms' = true →
                  1 + sizeOf ms' ≤ n →
                  ∀ {j_cf : Nat},
                    j_cf ≤ i' →
                    ∀ {done₁ done₂ : List CekValue},
                      ListRel (ValueRefinesK j_cf) done₁ done₂ →
                      StackRefK ValueRefinesK j_cf
                        (Frame.constrField tag done₁ ms' ρ₁ :: π₁)
                        (Frame.constrField tag done₂ (substTermList pos t_rhs ms') ρ₂ :: π₂) := by
              intro ms'
              induction ms' with
              | nil =>
                intro _ _ j_cf hj_cf done₁ done₂ hdone
                intro j hj v₁ v₂ hv
                match j with
                | 0 => exact Moist.Verified.Equivalence.obsRefinesK_zero_ret
                | j' + 1 =>
                  refine Moist.Verified.Equivalence.obsRefinesK_of_step_ret ?_
                  simp only [substTermList, step]
                  have hrev : ListRel (ValueRefinesK j')
                      ((v₁ :: done₁).reverse) ((v₂ :: done₂).reverse) := by
                    simp only [List.reverse_cons]
                    exact Moist.Verified.Equivalence.listRel_append
                      (Moist.Verified.Equivalence.listRel_reverse
                        (Moist.Verified.Equivalence.listRel_mono
                          (fun a b h => valueRefinesK_mono (show j' ≤ j_cf by omega) a b h) hdone))
                      ⟨valueRefinesK_mono (Nat.le_succ j') v₁ v₂ hv, trivial⟩
                  have hval : ValueRefinesK (j' + 1)
                      (.VConstr tag ((v₁ :: done₁).reverse))
                      (.VConstr tag ((v₂ :: done₂).reverse)) := by
                    cases j' with
                    | zero =>
                      simp only [ValueRefinesK]
                      exact ⟨trivial, hrev⟩
                    | succ m =>
                      simp only [ValueRefinesK]
                      exact ⟨trivial, hrev⟩
                  have hπ_j1 : StackRefK ValueRefinesK (j' + 1) π₁ π₂ :=
                    stackRefK_mono (show j' + 1 ≤ i' + 1 from by
                      exact Nat.succ_le_succ (Nat.le_of_succ_le (Nat.le_trans hj hj_cf))) hπ
                  exact obsRefinesK_mono (Nat.le_succ j')
                    (hπ_j1 (j' + 1) (Nat.le_refl _) _ _ hval)
              | cons u us ih_ms =>
                intro hclosed_us hsz_us j_cf hj_cf done₁ done₂ hdone
                simp [closedAtList] at hclosed_us
                intro j hj v₁ v₂ hv
                match j with
                | 0 => exact Moist.Verified.Equivalence.obsRefinesK_zero_ret
                | j' + 1 =>
                  refine Moist.Verified.Equivalence.obsRefinesK_of_step_ret ?_
                  simp only [substTermList, step]
                  have hj'_le_jcf : j' ≤ j_cf :=
                    Nat.le_of_lt (Nat.lt_of_succ_le hj)
                  have hj'_le_i' : j' ≤ i' := Nat.le_trans hj'_le_jcf hj_cf
                  have hdone' : ListRel (ValueRefinesK j') (v₁ :: done₁) (v₂ :: done₂) :=
                    ⟨valueRefinesK_mono (Nat.le_succ j') v₁ v₂ hv,
                     Moist.Verified.Equivalence.listRel_mono
                       (fun a b h => valueRefinesK_mono hj'_le_jcf a b h) hdone⟩
                  have hπ_next := ih_ms hclosed_us.2
                    (show 1 + sizeOf us ≤ n by
                      have : sizeOf (u :: us) ≥ 1 + sizeOf us := by simp
                      omega)
                    hj'_le_i' hdone'
                  exact ih_sz
                    (show sizeOf u ≤ n by
                      have : sizeOf (u :: us) ≥ 1 + sizeOf u := by simp
                      omega)
                    hclosed_us.1 (by omega) hπ_next
            have hπ_cf := constrField_stackRefK ms hclosed_ms hsz_ms
              (Nat.le_refl i') (done₁ := []) (done₂ := []) (by simp [ListRel])
            exact ih_sz hsz_m hclosed_m (by omega) hπ_cf
      | .Case scrut alts =>
        have hsz_scrut : sizeOf scrut ≤ n := by
          have : sizeOf (Term.Case scrut alts) = 1 + sizeOf scrut + sizeOf alts := by
            simp [Term._sizeOf_inst, List._sizeOf_inst]
          omega
        have hclosed_scrut : closedAt (d + 1) scrut = true := by
          simp [closedAt] at hclosed_body
          exact hclosed_body.1
        have hclosed_alts : closedAtList (d + 1) alts = true := by
          simp [closedAt] at hclosed_body
          exact hclosed_body.2
        simp only [substTerm]
        match i with
        | 0 => exact obsRefinesK_zero_compute
        | i' + 1 =>
          refine obsRefinesK_of_step_compute ?_
          simp only [step]
          have h_subst_len : (substTermList pos t_rhs alts).length = alts.length :=
            substTermList_length pos t_rhs alts
          have alt_obsRefinesK (tag : Nat) (hi_tag : tag < alts.length)
              {j' : Nat} (_hj'_le : j' ≤ i')
              {π₁' π₂' : Stack} (hπ' : StackRefK ValueRefinesK j' π₁' π₂') :
              ObsRefinesK j'
                (.compute π₁' ρ₁ (alts[tag]'hi_tag))
                (.compute π₂' ρ₂ (substTerm pos t_rhs (alts[tag]'hi_tag))) := by
            have hclosed_elem := closedAtList_elem' hclosed_alts hi_tag
            have hsz_elem : sizeOf (alts[tag]'hi_tag) ≤ n := by
              have : sizeOf (alts[tag]'hi_tag) < 1 + sizeOf alts := by
                exact Nat.lt_of_lt_of_le
                  (List.sizeOf_lt_of_mem (List.getElem_mem hi_tag)) (by omega)
              have : sizeOf (Term.Case scrut alts) = 1 + sizeOf scrut + sizeOf alts := by
                simp [Term._sizeOf_inst, List._sizeOf_inst]
              omega
            exact ih_sz hsz_elem hclosed_elem (by omega) hπ'
          have hπ_case : StackRefK ValueRefinesK i'
              (Frame.caseScrutinee alts ρ₁ :: π₁)
              (Frame.caseScrutinee (substTermList pos t_rhs alts) ρ₂ :: π₂) := by
            intro j hj v₁ v₂ hv
            match j with
            | 0 => exact Moist.Verified.Equivalence.obsRefinesK_zero_ret
            | j' + 1 =>
              have hπ_j' : StackRefK ValueRefinesK j' π₁ π₂ :=
                stackRefK_mono (show j' ≤ i' + 1 by omega) hπ
              refine Moist.Verified.Equivalence.obsRefinesK_of_step_ret ?_
              match v₁, v₂ with
              | .VConstr tag₁ fields₁, .VConstr tag₂ fields₂ =>
                simp only [ValueRefinesK] at hv
                obtain ⟨rfl, hfields_v⟩ := hv
                simp only [step]
                split
                · rename_i alt₁ halt₁
                  have hsome₁ := List.getElem?_eq_some_iff.mp halt₁
                  have hi₁ : tag₁ < alts.length := hsome₁.1
                  have hi₂ : tag₁ < (substTermList pos t_rhs alts).length := by omega
                  have halt₂ : (substTermList pos t_rhs alts)[tag₁]? =
                      some ((substTermList pos t_rhs alts)[tag₁]) :=
                    List.getElem?_eq_some_iff.mpr ⟨hi₂, rfl⟩
                  rw [halt₂]
                  simp only []
                  rw [substTermList_getElem pos t_rhs alts tag₁ hi₁,
                      show alt₁ = alts[tag₁] from hsome₁.2.symm]
                  exact alt_obsRefinesK tag₁ hi₁ (by omega)
                    (applyArgFrames_stackRefK
                      (Moist.Verified.Equivalence.listRel_mono
                        (fun a b h => valueRefinesK_mono (Nat.le_refl _) a b h) hfields_v)
                      hπ_j')
                · rename_i hnone₁
                  have hnone₂ : (substTermList pos t_rhs alts)[tag₁]? = none := by
                    rw [List.getElem?_eq_none_iff] at hnone₁ ⊢
                    omega
                  rw [hnone₂]
                  simp only []
                  exact obsRefinesK_error _
              | .VCon c₁, .VCon c₂ =>
                simp only [ValueRefinesK] at hv
                subst hv
                simp only [step]
                split
                · rename_i tag numCtors fields htag
                  split
                  · rename_i h_check
                    have h_check_r : (decide (numCtors > 0) &&
                        decide ((substTermList pos t_rhs alts).length > numCtors)) = true := by
                      rw [h_subst_len]
                      exact h_check
                    simp only [h_check_r]
                    exact obsRefinesK_error _
                  · rename_i h_check
                    have h_check_r : ¬(decide (numCtors > 0) &&
                        decide ((substTermList pos t_rhs alts).length > numCtors)) = true := by
                      rw [h_subst_len]
                      exact h_check
                    simp only [show (decide (numCtors > 0) &&
                        decide ((substTermList pos t_rhs alts).length > numCtors)) = false from
                      Bool.eq_false_iff.mpr h_check_r]
                    split
                    · rename_i alt₁ halt₁
                      have hsome₁ := List.getElem?_eq_some_iff.mp halt₁
                      have hi₁ : tag < alts.length := hsome₁.1
                      have hi₂ : tag < (substTermList pos t_rhs alts).length := by omega
                      have halt₂ : (substTermList pos t_rhs alts)[tag]? =
                          some ((substTermList pos t_rhs alts)[tag]) :=
                        List.getElem?_eq_some_iff.mpr ⟨hi₂, rfl⟩
                      rw [halt₂]
                      simp only []
                      rw [substTermList_getElem pos t_rhs alts tag hi₁,
                          show alt₁ = alts[tag] from hsome₁.2.symm]
                      have hfields_vcon := constToTagAndFields_fields_vcon c₁
                      rw [htag] at hfields_vcon
                      exact alt_obsRefinesK tag hi₁ (by omega)
                        (applyArgFrames_stackRefK
                          (listRel_refl_vcon_refines j' fields hfields_vcon)
                          hπ_j')
                    · rename_i hnone₁
                      have hnone₂ : (substTermList pos t_rhs alts)[tag]? = none := by
                        rw [List.getElem?_eq_none_iff] at hnone₁ ⊢
                        omega
                      rw [hnone₂]
                      simp only []
                      exact obsRefinesK_error _
                · exact obsRefinesK_error _
              | .VLam _ _, .VLam _ _ | .VDelay _ _, .VDelay _ _
              | .VBuiltin _ _ _, .VBuiltin _ _ _ =>
                simp only [step]
                exact obsRefinesK_error _
              | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
              | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
              | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
              | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
              | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
              | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
              | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
              | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
              | .VBuiltin _ _ _, .VConstr _ _ =>
                simp only [ValueRefinesK] at hv
          exact ih_sz hsz_scrut hclosed_scrut (by omega) hπ_case
termination_by sz

theorem body_subst_obsRefines {d : Nat} {t_body t_rhs : Term}
    (h_strict : StrictSingleOcc 1 t_body)
    (hclosed_body : closedAt (d + 1) t_body = true)
    (hclosed_rhs : closedAt d t_rhs = true)
    {ρ : CekEnv} {v_ret : CekValue}
    (h_ret : ∀ π, ∃ m, steps m (.compute π ρ t_rhs) = .ret π v_ret)
    (henv_wf : Moist.Verified.BetaValueRefines.EnvWellFormed d ρ)
    (hlen : d ≤ ρ.length)
    (hvwf : Moist.Verified.BetaValueRefines.ValueWellFormed v_ret)
    (hwf_π : Moist.Verified.BetaValueRefines.StackWellFormed π) :
    Moist.Verified.Contextual.ObsRefines
      (.compute π (ρ.extend v_ret) t_body)
      (.compute π ρ (substTerm 1 t_rhs t_body)) := by
  -- Build SubstEnvRef 1 v_ret n (d+1) (ρ.extend v_ret) ρ and invoke gen at pos=1.
  have henv_wf_L : Moist.Verified.BetaValueRefines.EnvWellFormed (d + 1) (ρ.extend v_ret) :=
    Moist.Verified.BetaValueRefines.envWellFormed_extend d henv_wf hlen hvwf
  have hlen_L : d + 1 ≤ (ρ.extend v_ret).length := by
    show d + 1 ≤ ρ.length + 1; omega
  have mk_multi (k : Nat) : ∀ (K : Nat) (ρ_ext : CekEnv),
      (∀ n, 0 < n → n ≤ d → ρ_ext.lookup (n + K) = ρ.lookup n) →
      ∀ π, ∃ m v',
        steps m (.compute π ρ_ext
          (Moist.Verified.SubstRefines.iterShift K t_rhs)) = .ret π v' ∧
        Moist.Verified.Contextual.SoundnessRefines.ValueRefinesK k v_ret v' :=
    fun K ρ_ext h_lookup π =>
      shifted_halt_extend_multi (k := k) hclosed_rhs henv_wf h_ret hvwf h_lookup π
  constructor
  · rintro ⟨v, n, hn⟩
    have hπ := Moist.Verified.BetaValueRefines.stackRefK_refl n π hwf_π
    have henv_refl := Moist.Verified.BetaValueRefines.envRefinesK_refl (k := n) henv_wf
    have hvrefl : Moist.Verified.Contextual.SoundnessRefines.ValueRefinesK n v_ret v_ret :=
      Moist.Verified.BetaValueRefines.valueRefinesK_refl n v_ret hvwf
    have hsubst_env :
        Moist.Verified.BetaValueRefines.SubstEnvRef 1 v_ret n (d + 1) (ρ.extend v_ret) ρ :=
      Moist.Verified.InlineSoundness.Beta.substEnvRef_of_envRefinesK_extend henv_refl hvrefl
    have hexact : (ρ.extend v_ret).lookup 1 = some v_ret :=
      Moist.Verified.BetaValueRefines.extend_lookup_one ρ v_ret
    have h := body_subst_obsRefinesK_gen (sizeOf t_body) (Nat.le_refl _)
      (by omega) (by omega) h_strict.toSingleOcc hclosed_body hclosed_rhs
      hsubst_env hexact (mk_multi n) hlen_L hlen hvwf
      (Nat.le_refl n) hπ
    exact h.1 v ⟨n, Nat.le_refl _, hn⟩
  · intro ⟨n, hn⟩
    have hπ := Moist.Verified.BetaValueRefines.stackRefK_refl n π hwf_π
    have henv_refl := Moist.Verified.BetaValueRefines.envRefinesK_refl (k := n) henv_wf
    have hvrefl : Moist.Verified.Contextual.SoundnessRefines.ValueRefinesK n v_ret v_ret :=
      Moist.Verified.BetaValueRefines.valueRefinesK_refl n v_ret hvwf
    have hsubst_env :
        Moist.Verified.BetaValueRefines.SubstEnvRef 1 v_ret n (d + 1) (ρ.extend v_ret) ρ :=
      Moist.Verified.InlineSoundness.Beta.substEnvRef_of_envRefinesK_extend henv_refl hvrefl
    have hexact : (ρ.extend v_ret).lookup 1 = some v_ret :=
      Moist.Verified.BetaValueRefines.extend_lookup_one ρ v_ret
    have h := body_subst_obsRefinesK_gen (sizeOf t_body) (Nat.le_refl _)
      (by omega) (by omega) h_strict.toSingleOcc hclosed_body hclosed_rhs
      hsubst_env hexact (mk_multi n) hlen_L hlen hvwf
      (Nat.le_refl n) hπ
    exact h.2 n (Nat.le_refl _) hn

theorem same_env_beta_obsRefines {d : Nat} {t_body t_rhs : Term}
    (h_strict : StrictSingleOcc 1 t_body)
    (hclosed_body : closedAt (d + 1) t_body = true)
    (hclosed_rhs : closedAt d t_rhs = true)
    (ρ : CekEnv) (π : Stack)
    (henv_wf : Moist.Verified.BetaValueRefines.EnvWellFormed d ρ)
    (hlen : d ≤ ρ.length)
    (hwf_π : Moist.Verified.BetaValueRefines.StackWellFormed π) :
    Moist.Verified.Contextual.ObsRefines
      (.compute π ρ (.Apply (.Lam 0 t_body) t_rhs))
      (.compute π ρ (substTerm 1 t_rhs t_body)) := by
  have h_rhs_fate := Moist.Verified.halt_or_error (.compute [] ρ t_rhs)
  cases h_rhs_fate with
  | inr h_rhs_err_empty =>
    have h_rhs_err_all := error_on_all_stacks h_rhs_err_empty
    constructor
    · rintro ⟨v, n, hn⟩
      exfalso
      have h3 : steps 3 (.compute π ρ (.Apply (.Lam 0 t_body) t_rhs)) =
          .compute (Frame.funV (.VLam t_body ρ) :: π) ρ t_rhs := by
        simp [steps, step]
      obtain ⟨n_err, hn_err⟩ := h_rhs_err_all (Frame.funV (.VLam t_body ρ) :: π)
      have h_apply_err : steps (3 + n_err) (.compute π ρ (.Apply (.Lam 0 t_body) t_rhs)) = .error := by
        rw [steps_trans, h3, hn_err]
      exact error_of_halt_then_error hn h_apply_err
    · intro h_err
      exact strict_subst_reaches_error h_strict (by omega : (1:Nat) ≤ 1) (by omega : (1:Nat) ≤ d + 1)
        hclosed_body hclosed_rhs henv_wf hlen h_rhs_err_all π
  | inl h_rhs_halt_ex =>
    obtain ⟨v_rhs, n_halt, hn_halt⟩ := h_rhs_halt_ex
    obtain ⟨m_ret, _, v_ret, hm_ret⟩ :=
      halt_descends_to_baseπ n_halt (.compute [] ρ t_rhs) v_rhs hn_halt ⟨[], rfl⟩
    have h_rhs_ret_all := ret_on_all_stacks hm_ret
    have hvwf : Moist.Verified.BetaValueRefines.ValueWellFormed v_ret := by
      obtain ⟨m, hm⟩ := h_rhs_ret_all []
      exact Moist.Verified.StepWellFormed.halt_value_wf
        (Moist.Verified.StepWellFormed.StateWellFormed.compute
          Moist.Verified.BetaValueRefines.StackWellFormed.nil henv_wf hlen hclosed_rhs)
        (show steps (m + 1) (.compute [] ρ t_rhs) = .halt v_ret by
          rw [steps_trans, hm]; rfl)
    have h_body_obs := body_subst_obsRefines h_strict hclosed_body hclosed_rhs
      h_rhs_ret_all henv_wf hlen hvwf hwf_π
    obtain ⟨m_rhs, hm_rhs⟩ := h_rhs_ret_all (Frame.funV (.VLam t_body ρ) :: π)
    have h3 : steps 3 (.compute π ρ (.Apply (.Lam 0 t_body) t_rhs)) =
        .compute (Frame.funV (.VLam t_body ρ) :: π) ρ t_rhs := by
      simp [steps, step]
    have h_funv_step : step (.ret (Frame.funV (.VLam t_body ρ) :: π) v_ret) =
        .compute π (ρ.extend v_ret) t_body := rfl
    let P := 3 + m_rhs + 1
    have h_prefix : steps P (.compute π ρ (.Apply (.Lam 0 t_body) t_rhs)) =
        .compute π (ρ.extend v_ret) t_body := by
      show steps (3 + m_rhs + 1) _ = _
      rw [show 3 + m_rhs + 1 = 3 + (m_rhs + 1) by omega, steps_trans, h3,
          show m_rhs + 1 = m_rhs + 1 from rfl, steps_trans, hm_rhs]
      exact h_funv_step
    constructor
    · rintro ⟨v, n, hn⟩
      exact h_body_obs.halt ⟨v, by
        by_cases hle : n ≤ P
        · exfalso
          have : P = n + (P - n) := by omega
          rw [this, steps_trans] at h_prefix
          have : steps n (.compute π ρ (.Apply (.Lam 0 t_body) t_rhs)) = .halt v := hn
          rw [this, steps_halt_fixed] at h_prefix
          exact State.noConfusion h_prefix
        · exact ⟨n - P, by
            rw [show n = P + (n - P) by omega, steps_trans, h_prefix] at hn
            exact hn⟩⟩
    · rintro ⟨n, hn⟩
      exact h_body_obs.error ⟨n - P, by
        by_cases hle : n ≤ P
        · exfalso
          have : P = n + (P - n) := by omega
          rw [this, steps_trans] at h_prefix
          rw [hn, steps_error_fixed] at h_prefix
          exact State.noConfusion h_prefix
        · rw [show n = P + (n - P) by omega, steps_trans, h_prefix] at hn
          exact hn⟩

theorem same_env_beta_single_obsRefines {d : Nat} {t_body t_rhs : Term}
    (h_single : SingleOcc 1 t_body)
    (hclosed_body : closedAt (d + 1) t_body = true)
    (hclosed_rhs : closedAt d t_rhs = true)
    (ρ : CekEnv) (π : Stack)
    (henv_wf : Moist.Verified.BetaValueRefines.EnvWellFormed d ρ)
    (hlen : d ≤ ρ.length)
    (hwf_π : Moist.Verified.BetaValueRefines.StackWellFormed π)
    (h_rhs_halts : ∀ π', ∃ (m : Nat) (v : CekValue),
      steps m (.compute π' ρ t_rhs) = .ret π' v ∧
      ∀ k ≤ m, steps k (.compute π' ρ t_rhs) ≠ .error) :
    Moist.Verified.Contextual.ObsRefines
      (.compute π ρ (.Apply (.Lam 0 t_body) t_rhs))
      (.compute π ρ (substTerm 1 t_rhs t_body)) := by
  have h_rhs_fate := Moist.Verified.halt_or_error (.compute [] ρ t_rhs)
  cases h_rhs_fate with
  | inr h_rhs_err_empty =>
    obtain ⟨m, v, hm, hne⟩ := h_rhs_halts []
    obtain ⟨n, hn⟩ := h_rhs_err_empty
    exfalso
    exact reaches_halt_not_error ⟨m + 1, by rw [steps_trans, hm]; rfl⟩ ⟨n, hn⟩
  | inl h_rhs_halt_ex =>
    obtain ⟨v_rhs, n_halt, hn_halt⟩ := h_rhs_halt_ex
    obtain ⟨m_ret, _, v_ret, hm_ret⟩ :=
      halt_descends_to_baseπ n_halt (.compute [] ρ t_rhs) v_rhs hn_halt ⟨[], rfl⟩
    have h_rhs_ret_all := ret_on_all_stacks hm_ret
    have hvwf : Moist.Verified.BetaValueRefines.ValueWellFormed v_ret := by
      obtain ⟨m, hm⟩ := h_rhs_ret_all []
      exact Moist.Verified.StepWellFormed.halt_value_wf
        (Moist.Verified.StepWellFormed.StateWellFormed.compute
          Moist.Verified.BetaValueRefines.StackWellFormed.nil henv_wf hlen hclosed_rhs)
        (show steps (m + 1) (.compute [] ρ t_rhs) = .halt v_ret by
          rw [steps_trans, hm]; rfl)
    have mk_multi (k : Nat) : ∀ (K : Nat) (ρ_ext : CekEnv),
        (∀ n, 0 < n → n ≤ d → ρ_ext.lookup (n + K) = ρ.lookup n) →
        ∀ π, ∃ m v',
          steps m (.compute π ρ_ext
            (Moist.Verified.SubstRefines.iterShift K t_rhs)) = .ret π v' ∧
          Moist.Verified.Contextual.SoundnessRefines.ValueRefinesK k v_ret v' :=
      fun K ρ_ext h_lookup π =>
        shifted_halt_extend_multi (k := k) hclosed_rhs henv_wf h_rhs_ret_all hvwf h_lookup π
    have h_body_obs : Moist.Verified.Contextual.ObsRefines
        (.compute π (ρ.extend v_ret) t_body)
        (.compute π ρ (substTerm 1 t_rhs t_body)) := by
      constructor
      · rintro ⟨v, n, hn⟩
        have hπk := Moist.Verified.BetaValueRefines.stackRefK_refl n π hwf_π
        have henv_refl := Moist.Verified.BetaValueRefines.envRefinesK_refl (k := n) henv_wf
        have hvrefl := Moist.Verified.BetaValueRefines.valueRefinesK_refl n v_ret hvwf
        have hsubst_env := Moist.Verified.InlineSoundness.Beta.substEnvRef_of_envRefinesK_extend henv_refl hvrefl
        have hexact := Moist.Verified.BetaValueRefines.extend_lookup_one ρ v_ret
        have h := body_subst_obsRefinesK_gen (sizeOf t_body) (Nat.le_refl _)
          (by omega) (by omega) h_single hclosed_body hclosed_rhs
          hsubst_env hexact (mk_multi n)
          (by simp [CekEnv.extend, CekEnv.length]; omega) hlen hvwf
          (Nat.le_refl n) hπk
        exact h.1 v ⟨n, Nat.le_refl _, hn⟩
      · rintro ⟨n, hn⟩
        have hπk := Moist.Verified.BetaValueRefines.stackRefK_refl n π hwf_π
        have henv_refl := Moist.Verified.BetaValueRefines.envRefinesK_refl (k := n) henv_wf
        have hvrefl := Moist.Verified.BetaValueRefines.valueRefinesK_refl n v_ret hvwf
        have hsubst_env := Moist.Verified.InlineSoundness.Beta.substEnvRef_of_envRefinesK_extend henv_refl hvrefl
        have hexact := Moist.Verified.BetaValueRefines.extend_lookup_one ρ v_ret
        have h := body_subst_obsRefinesK_gen (sizeOf t_body) (Nat.le_refl _)
          (by omega) (by omega) h_single hclosed_body hclosed_rhs
          hsubst_env hexact (mk_multi n)
          (by simp [CekEnv.extend, CekEnv.length]; omega) hlen hvwf
          (Nat.le_refl n) hπk
        exact h.2 n (Nat.le_refl _) hn
    obtain ⟨m_rhs, hm_rhs⟩ := h_rhs_ret_all (Frame.funV (.VLam t_body ρ) :: π)
    have h3 : steps 3 (.compute π ρ (.Apply (.Lam 0 t_body) t_rhs)) =
        .compute (Frame.funV (.VLam t_body ρ) :: π) ρ t_rhs := by
      simp [steps, step]
    have h_funv_step : step (.ret (Frame.funV (.VLam t_body ρ) :: π) v_ret) =
        .compute π (ρ.extend v_ret) t_body := rfl
    let P := 3 + m_rhs + 1
    have h_prefix : steps P (.compute π ρ (.Apply (.Lam 0 t_body) t_rhs)) =
        .compute π (ρ.extend v_ret) t_body := by
      show steps (3 + m_rhs + 1) _ = _
      rw [show 3 + m_rhs + 1 = 3 + (m_rhs + 1) by omega, steps_trans, h3,
          show m_rhs + 1 = m_rhs + 1 from rfl, steps_trans, hm_rhs]
      exact h_funv_step
    constructor
    · rintro ⟨v, n, hn⟩
      exact h_body_obs.halt ⟨v, by
        by_cases hle : n ≤ P
        · exfalso
          have : P = n + (P - n) := by omega
          rw [this, steps_trans] at h_prefix
          rw [hn, steps_halt_fixed] at h_prefix
          exact State.noConfusion h_prefix
        · exact ⟨n - P, by
            rw [show n = P + (n - P) by omega, steps_trans, h_prefix] at hn
            exact hn⟩⟩
    · rintro ⟨n, hn⟩
      exact h_body_obs.error ⟨n - P, by
        by_cases hle : n ≤ P
        · exfalso
          have : P = n + (P - n) := by omega
          rw [this, steps_trans] at h_prefix
          rw [hn, steps_error_fixed] at h_prefix
          exact State.noConfusion h_prefix
        · rw [show n = P + (n - P) by omega, steps_trans, h_prefix] at hn
          exact hn⟩

theorem same_env_beta_multi_obsRefines {d : Nat} {t_body t_rhs : Term}
    (hclosed_body : closedAt (d + 1) t_body = true)
    (hclosed_rhs : closedAt d t_rhs = true)
    (ρ : CekEnv) (π : Stack)
    (henv_wf : Moist.Verified.BetaValueRefines.EnvWellFormed d ρ)
    (hlen : d ≤ ρ.length)
    (hwf_π : Moist.Verified.BetaValueRefines.StackWellFormed π)
    (h_rhs_halts : ∀ π', ∃ (m : Nat) (v : CekValue),
      steps m (.compute π' ρ t_rhs) = .ret π' v ∧
      ∀ k ≤ m, steps k (.compute π' ρ t_rhs) ≠ .error) :
    Moist.Verified.Contextual.ObsRefines
      (.compute π ρ (.Apply (.Lam 0 t_body) t_rhs))
      (.compute π ρ (substTerm 1 t_rhs t_body)) := by
  have h_rhs_fate := Moist.Verified.halt_or_error (.compute [] ρ t_rhs)
  cases h_rhs_fate with
  | inr h_rhs_err_empty =>
    obtain ⟨m, v, hm, hne⟩ := h_rhs_halts []
    obtain ⟨n, hn⟩ := h_rhs_err_empty
    exfalso
    exact reaches_halt_not_error ⟨m + 1, by rw [steps_trans, hm]; rfl⟩ ⟨n, hn⟩
  | inl h_rhs_halt_ex =>
    obtain ⟨v_rhs, n_halt, hn_halt⟩ := h_rhs_halt_ex
    obtain ⟨m_ret, _, v_ret, hm_ret⟩ :=
      halt_descends_to_baseπ n_halt (.compute [] ρ t_rhs) v_rhs hn_halt ⟨[], rfl⟩
    have h_rhs_ret_all := ret_on_all_stacks hm_ret
    have hvwf : Moist.Verified.BetaValueRefines.ValueWellFormed v_ret := by
      obtain ⟨m, hm⟩ := h_rhs_ret_all []
      exact Moist.Verified.StepWellFormed.halt_value_wf
        (Moist.Verified.StepWellFormed.StateWellFormed.compute
          Moist.Verified.BetaValueRefines.StackWellFormed.nil henv_wf hlen hclosed_rhs)
        (show steps (m + 1) (.compute [] ρ t_rhs) = .halt v_ret by
          rw [steps_trans, hm]; rfl)
    have mk_multi (k : Nat) : ∀ (K : Nat) (ρ_ext : CekEnv),
        (∀ n, 0 < n → n ≤ d → ρ_ext.lookup (n + K) = ρ.lookup n) →
        ∀ π, ∃ m v',
          steps m (.compute π ρ_ext
            (Moist.Verified.SubstRefines.iterShift K t_rhs)) = .ret π v' ∧
          Moist.Verified.Contextual.SoundnessRefines.ValueRefinesK k v_ret v' :=
      fun K ρ_ext h_lookup π =>
        shifted_halt_extend_multi (k := k) hclosed_rhs henv_wf h_rhs_ret_all hvwf h_lookup π
    have h_body_obs : Moist.Verified.Contextual.ObsRefines
        (.compute π (ρ.extend v_ret) t_body)
        (.compute π ρ (substTerm 1 t_rhs t_body)) := by
      constructor
      · rintro ⟨v, n, hn⟩
        have hπk := Moist.Verified.BetaValueRefines.stackRefK_refl n π hwf_π
        have henv_refl := Moist.Verified.BetaValueRefines.envRefinesK_refl (k := n) henv_wf
        have hvrefl := Moist.Verified.BetaValueRefines.valueRefinesK_refl n v_ret hvwf
        have hsubst_env := Moist.Verified.InlineSoundness.Beta.substEnvRef_of_envRefinesK_extend henv_refl hvrefl
        have hexact := Moist.Verified.BetaValueRefines.extend_lookup_one ρ v_ret
        have h := body_subst_multi_obsRefinesK_gen (sizeOf t_body) (Nat.le_refl _)
          (by omega) (by omega) hclosed_body hclosed_rhs
          hsubst_env hexact (mk_multi n)
          (by simp [CekEnv.extend, CekEnv.length]; omega) hlen hvwf
          (Nat.le_refl n) hπk
        exact h.1 v ⟨n, Nat.le_refl _, hn⟩
      · rintro ⟨n, hn⟩
        have hπk := Moist.Verified.BetaValueRefines.stackRefK_refl n π hwf_π
        have henv_refl := Moist.Verified.BetaValueRefines.envRefinesK_refl (k := n) henv_wf
        have hvrefl := Moist.Verified.BetaValueRefines.valueRefinesK_refl n v_ret hvwf
        have hsubst_env := Moist.Verified.InlineSoundness.Beta.substEnvRef_of_envRefinesK_extend henv_refl hvrefl
        have hexact := Moist.Verified.BetaValueRefines.extend_lookup_one ρ v_ret
        have h := body_subst_multi_obsRefinesK_gen (sizeOf t_body) (Nat.le_refl _)
          (by omega) (by omega) hclosed_body hclosed_rhs
          hsubst_env hexact (mk_multi n)
          (by simp [CekEnv.extend, CekEnv.length]; omega) hlen hvwf
          (Nat.le_refl n) hπk
        exact h.2 n (Nat.le_refl _) hn
    obtain ⟨m_rhs, hm_rhs⟩ := h_rhs_ret_all (Frame.funV (.VLam t_body ρ) :: π)
    have h3 : steps 3 (.compute π ρ (.Apply (.Lam 0 t_body) t_rhs)) =
        .compute (Frame.funV (.VLam t_body ρ) :: π) ρ t_rhs := by
      simp [steps, step]
    have h_funv_step : step (.ret (Frame.funV (.VLam t_body ρ) :: π) v_ret) =
        .compute π (ρ.extend v_ret) t_body := rfl
    let P := 3 + m_rhs + 1
    have h_prefix : steps P (.compute π ρ (.Apply (.Lam 0 t_body) t_rhs)) =
        .compute π (ρ.extend v_ret) t_body := by
      show steps (3 + m_rhs + 1) _ = _
      rw [show 3 + m_rhs + 1 = 3 + (m_rhs + 1) by omega, steps_trans, h3,
          show m_rhs + 1 = m_rhs + 1 from rfl, steps_trans, hm_rhs]
      exact h_funv_step
    constructor
    · rintro ⟨v, n, hn⟩
      exact h_body_obs.halt ⟨v, by
        by_cases hle : n ≤ P
        · exfalso
          have : P = n + (P - n) := by omega
          rw [this, steps_trans] at h_prefix
          rw [hn, steps_halt_fixed] at h_prefix
          exact State.noConfusion h_prefix
        · exact ⟨n - P, by rw [show n = P + (n - P) by omega, steps_trans, h_prefix] at hn; exact hn⟩⟩
    · rintro ⟨n, hn⟩
      exact h_body_obs.error ⟨n - P, by
        by_cases hle : n ≤ P
        · exfalso
          have : P = n + (P - n) := by omega
          rw [this, steps_trans] at h_prefix
          rw [hn, steps_error_fixed] at h_prefix
          exact State.noConfusion h_prefix
        · rw [show n = P + (n - P) by omega, steps_trans, h_prefix] at hn; exact hn⟩

end SameEnvBeta

end Moist.Verified.InlineSoundness.StrictOcc
