import Moist.Verified.FailFastSoundness.Sink
import Moist.Verified.FloatOut.Lowering

variable [sv : Moist.CEK.SemVariant]

/-! # Evaluating a terminating binding first

  `let x = e in let y = c in B  ⊑  let y = c in let x = e in B`

when `c` halts or errors in every environment and neither right-hand side
mentions the other binder. If `e` errors, the target evaluates `c` first and
then errors in `c` or in `e`; if `e` diverges there is no obligation. When
both return, the body runs in the same environment up to the order of the two
binders, which the shift bisimulation relates.
-/

namespace Moist.Verified.FailFast

open Moist.CEK Moist.Plutus.Term
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FloatOut (swapRename is0preserving_swapRename)

omit sv in
theorem shiftBisimEnv_shift' {d : Nat} {ρ : CekEnv} (w : CekValue) :
    EnvWellFormed d ρ → ShiftBisimEnv (shiftRename 1) d ρ (ρ.extend w)
  | .zero => .zero
  | .succ (k := k) (v := v) hrest _ hl hv => by
    refine .succ (v₁ := v) (v₂ := v) (shiftBisimEnv_shift' w hrest) hl ?_ (shiftBisimValue_refl_id v hv)
    rw [shiftRename_ge (by omega)]
    exact hl

/-- The value a term returns, and the value its shift returns under an
    unused binder, are shift-bisimilar. -/
theorem halts_shift {d : Nat} {ρ : CekEnv} {t : Term} {w : CekValue} (u : CekValue)
    (henv : EnvWellFormed d ρ) (hclosed : closedAt d t = true) (h : Halts ρ t w) :
    ∃ w', Halts (ρ.extend u) (renameTerm (shiftRename 1) t) w' ∧ ShiftBisimValue w w' := by
  obtain ⟨n, hn⟩ := h
  have hb : ShiftBisimState (.compute [] ρ t) (.compute [] (ρ.extend u) (renameTerm (shiftRename 1) t)) :=
    .compute (FundamentalRefines.is0preserving_shiftRename (by omega)) (shiftBisimEnv_shift' u henv)
      hclosed .nil
  have := shiftBisimState_steps_preserves n hb
  rw [hn] at this
  generalize hs : steps n (.compute [] (ρ.extend u) (renameTerm (shiftRename 1) t)) = s at this
  cases this with
  | halt hv => exact ⟨_, ⟨n, hs⟩, hv⟩

omit sv in
theorem lookup_extend_two (ρ : CekEnv) (a b : CekValue) (n : Nat) :
    ((ρ.extend a).extend b).lookup (n + 3) = ρ.lookup (n + 1) := rfl

omit sv in
/-- The environments with the last two bindings exchanged. -/
theorem shiftBisimEnv_swap {ρ : CekEnv} {w w' v : CekValue} (hww : ShiftBisimValue w w')
    (hv : ValueWellFormed v) :
    ∀ {k : Nat}, EnvWellFormed k ρ →
      ShiftBisimEnv swapRename (k + 2) ((ρ.extend w).extend v) ((ρ.extend v).extend w')
  | 0, _ =>
    .succ (.succ .zero rfl rfl (shiftBisimValue_refl_id v hv)) rfl rfl hww
  | k + 1, .succ (v := u) hrest _ hl hu =>
    .succ (shiftBisimEnv_swap hww hv hrest) (by rw [lookup_extend_two]; exact hl)
      (by show ((ρ.extend v).extend w').lookup (k + 3) = some u
          rw [lookup_extend_two]; exact hl)
      (shiftBisimValue_refl_id u hu)

theorem factRefines_swapLet {d : Nat} {F : CekEnv → Prop} {te tc B : Term}
    (hte : closedAt d te = true) (hc : closedAt d tc = true) (hB : closedAt (d + 2) B = true)
    (hterm : TerminatesAt d tc) :
    FactRefines d F
      (.Apply (.Lam 0 (.Apply (.Lam 0 (renameTerm swapRename B)) (renameTerm (shiftRename 1) tc))) te)
      (.Apply (.Lam 0 (.Apply (.Lam 0 B) (renameTerm (shiftRename 1) te))) tc) := by
  intro ρ π henv hlen hπ _
  have hsrc : Reaches (.compute π ρ
      (.Apply (.Lam 0 (.Apply (.Lam 0 (renameTerm swapRename B)) (renameTerm (shiftRename 1) tc))) te))
      (.compute (.funV (.VLam (.Apply (.Lam 0 (renameTerm swapRename B))
        (renameTerm (shiftRename 1) tc)) ρ) :: π) ρ te) := reaches_of_steps 3 rfl
  -- after the first binding returns `v`, the shifted check runs
  have after : ∀ v, Reaches (.ret (.funV (.VLam (.Apply (.Lam 0 (renameTerm swapRename B))
        (renameTerm (shiftRename 1) tc)) ρ) :: π) v)
      (.compute (.funV (.VLam (renameTerm swapRename B) (ρ.extend v)) :: π) (ρ.extend v)
        (renameTerm (shiftRename 1) tc)) := fun _ => reaches_of_steps 4 rfl
  rcases hterm ρ henv hlen with herrs | ⟨w, hw⟩
  · refine obsRefines_of_left_no_halt ?_ ?_
    · rintro ⟨u, hu⟩
      have hu' := reaches_terminal_after (.inr ⟨u, rfl⟩) hsrc hu
      rcases sequence (.inr ⟨u, rfl⟩) hu' with ⟨_, h⟩ | ⟨v, hv, hrest⟩
      · cases h
      · have hrest' := reaches_terminal_after (.inr ⟨u, rfl⟩) (after v) hrest
        have hvwf := halts_wellFormed henv hlen hte hv
        have hframe : StackWellFormed (.funV (.VLam (renameTerm swapRename B) (ρ.extend v)) :: π) := by
          refine .cons (.funV (.vlam (envWellFormed_extend d henv hlen hvwf)
            (by simp [CekEnv.extend, CekEnv.length]; omega) ?_)) hπ
          exact closedAt_rename _ B (d + 2) (d + 1 + 1) hB fun n hn => by
            match n with
            | 0 => simp [swapRename]
            | 1 => simp [swapRename]
            | 2 => simp [swapRename]
            | n + 3 => simp [swapRename]; omega
        obtain ⟨u', hu''⟩ := (obsEq_shift v henv hframe hc).2.halt ⟨u, hrest'⟩
        exact halt_not_error hu'' (errs_on_stack herrs _)
    · exact reaches_trans (reaches_of_steps 3 rfl) (errs_on_stack herrs _)
  · have hwwf := halts_wellFormed henv hlen hc hw
    have henvw := envWellFormed_extend d henv hlen hwwf
    have hlenw : d + 1 ≤ (ρ.extend w).length := by simp [CekEnv.extend, CekEnv.length]; omega
    have htgt : Reaches (.compute π ρ (.Apply (.Lam 0 (.Apply (.Lam 0 B) (renameTerm (shiftRename 1) te))) tc))
        (.compute (.funV (.VLam B (ρ.extend w)) :: π) (ρ.extend w) (renameTerm (shiftRename 1) te)) :=
      reaches_trans (reaches_of_steps 3 rfl)
        (reaches_trans (halts_on_stack hw _) (reaches_of_steps 4 rfl))
    refine obsRefines_of_reaches hsrc htgt ?_
    have hframe : StackWellFormed (.funV (.VLam B (ρ.extend w)) :: π) :=
      .cons (.funV (.vlam henvw hlenw hB)) hπ
    refine obsRefines_trans ?_ (obsEq_shift w henv hframe hte).1
    apply obsRefines_of_continuation
    intro v hv
    have hvwf := halts_wellFormed henv hlen hte hv
    obtain ⟨w', hw', hww⟩ := halts_shift v henv hc hw
    refine obsRefines_of_reaches (reaches_trans (after v) (reaches_trans (halts_on_stack hw' _)
      (reaches_of_steps 1 rfl))) (reaches_of_steps 1 rfl) ?_
    exact (obsRefines_of_shiftBisim (.compute is0preserving_swapRename
      (shiftBisimEnv_swap hww hvwf henv) hB (shiftBisimStack_refl hπ))).2

end Moist.Verified.FailFast
