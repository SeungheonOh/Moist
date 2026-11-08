import Moist.Verified.TagGuardSoundness.Guard
import Moist.Verified.FailFastSoundness.Swap

variable [sv : Moist.CEK.SemVariant]

/-! # Pair cases on decoded constructors

`case (unConstrData e) [λt f. b]` binds the integer tag `t` and the field list
`f` of a decoded constructor. This file proves

* `factRefines_pairCase`: rewriting the body under the knowledge that the
  two new binders hold constants,
* `factRefines_sinkPair`: moving a binding `let x = r` in front of such a
  case into its alternative, when the decoded expression terminates.
-/

namespace Moist.Verified.TagGuard

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast
open Moist.Verified.FloatOut (LookupShift lowerTotalExpr_lookupShift)

/-- The environment of a pair alternative: the enclosing environment, which
    satisfies `F`, extended by an integer tag and a constant. -/
def PairExt (d : Nat) (F : CekEnv → Prop) (ρ₂ : CekEnv) : Prop :=
  ∃ (ρ : CekEnv) (n : Int) (c : Const), ρ₂ = (ρ.extend (.VCon (.Integer n))).extend (.VCon c) ∧ F ρ ∧
    EnvWellFormed d ρ ∧ d ≤ ρ.length

theorem unConstrData_value {ρ : CekEnv} {t : Term} {v : CekValue}
    (h : Halts ρ (.Apply (.Builtin .UnConstrData) t) v) :
    ∃ (n : Int) (c : Const), v = .VCon (.Pair (.Integer n, c)) := by
  obtain ⟨wf, wa, hwf, _, hrest⟩ := halts_apply h
  rw [halts_builtin_value hwf] at hrest
  rcases apply_reaches hrest with ⟨_, _, heq, _⟩ | ⟨b, args, ea, heq, _, htail⟩
  · cases heq
  · cases heq
    rcases htail with ⟨_, hr, _⟩ | ⟨_, hev⟩
    · simp [expectedArgs, ExpectedArgs.tail] at hr
    · obtain ⟨c, r, rfl, hc, rfl⟩ := evalBuiltin_single (by decide) hev
      cases c with
      | Data d =>
        cases d with
        | Constr tag fields => cases hc; exact ⟨_, _, rfl⟩
        | _ => cases hc
      | _ => cases hc

/-- The steps from a returned pair to the body of the pair alternative. -/
theorem pair_dispatch (ρ : CekEnv) (π : Stack) (b : Term) (n : Int) (c : Const) :
    Reaches (.ret (.caseScrutinee [.Lam 0 (.Lam 0 b)] ρ :: π) (.VCon (.Pair (.Integer n, c))))
      (.compute π ((ρ.extend (.VCon (.Integer n))).extend (.VCon c)) b) :=
  reaches_of_steps 5 rfl

theorem factRefines_pairCase {d : Nat} {F : CekEnv → Prop} {tE b b' : Term}
    (hE : closedAt d tE = true) (hb : FactRefines (d + 2) (PairExt d F) b b') :
    FactRefines d F (.Case (.Apply (.Builtin .UnConstrData) tE) [.Lam 0 (.Lam 0 b)])
      (.Case (.Apply (.Builtin .UnConstrData) tE) [.Lam 0 (.Lam 0 b')]) := by
  intro ρ π henv hlen hπ hF
  apply obsRefines_of_step
  show ObsRefines (.compute (.caseScrutinee [.Lam 0 (.Lam 0 b)] ρ :: π) ρ _)
    (.compute (.caseScrutinee [.Lam 0 (.Lam 0 b')] ρ :: π) ρ _)
  apply obsRefines_of_continuation
  intro v hv
  obtain ⟨n, c, rfl⟩ := unConstrData_value hv
  refine obsRefines_of_reaches (pair_dispatch ρ π b n c) (pair_dispatch ρ π b' n c) ?_
  have h1 := envWellFormed_extend d henv hlen (.vcon (.Integer n))
  have h2 := envWellFormed_extend (d + 1) h1 (by simp [CekEnv.extend, CekEnv.length]; omega)
    (.vcon c)
  exact hb _ π h2 (by simp [CekEnv.extend, CekEnv.length]; omega) hπ ⟨ρ, n, c, rfl, hF, henv, hlen⟩

/-! ## Moving a binding into a pair alternative -/

/-- Positions `1, 2, 3` of the body of `let x = r in case _ [λt f. b]` become
    positions `2, 3, 1` once the binding moves under `λt f`. -/
def rotRename : Nat → Nat
  | 0 => 0
  | 1 => 2
  | 2 => 3
  | 3 => 1
  | n + 4 => n + 4

theorem is0preserving_rotRename : FundamentalRefines.Is0Preserving rotRename := by
  refine ⟨rfl, fun n hn => ?_⟩
  match n, hn with
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | n + 4, _ => simp [rotRename]

theorem envLookupT_cons_self {a x : VarId} (h : (a == x) = true) (env : List VarId) :
    envLookupT (a :: env) x = some 0 := by
  simp only [envLookupT, envLookupT.go, h, if_true]

theorem lookupShift_rot {f t x : VarId} (hft : (f == t) = false) (hfx : (f == x) = false)
    (htx : (t == x) = false) (Γ : List VarId) :
    LookupShift rotRename (f :: t :: x :: Γ) (x :: f :: t :: Γ) := by
  intro z
  have tr := VarId.beq_trans
  cases hfz : (f == z) <;> cases htz : (t == z) <;> cases hxz : (x == z)
  · rw [envLookupT_cons_neq f z _ hfz, envLookupT_cons_neq t z _ htz, envLookupT_cons_neq x z _ hxz,
      envLookupT_cons_neq x z _ hxz, envLookupT_cons_neq f z _ hfz, envLookupT_cons_neq t z _ htz]
    cases envLookupT Γ z <;> rfl
  · rw [envLookupT_cons_neq f z _ hfz, envLookupT_cons_neq t z _ htz, envLookupT_cons_self hxz,
      envLookupT_cons_self hxz]
    rfl
  · rw [envLookupT_cons_neq f z _ hfz, envLookupT_cons_self htz, envLookupT_cons_neq x z _ hxz,
      envLookupT_cons_neq f z _ hfz, envLookupT_cons_self htz]
    rfl
  · have : (t == x) = true :=
      tr _ _ _ htz (by rw [Moist.Verified.InlineSoundness.Rename.beq_comm]; exact hxz)
    rw [htx] at this; cases this
  · rw [envLookupT_cons_self hfz, envLookupT_cons_neq x z _ hxz, envLookupT_cons_self hfz]
    rfl
  · have : (f == x) = true :=
      tr _ _ _ hfz (by rw [Moist.Verified.InlineSoundness.Rename.beq_comm]; exact hxz)
    rw [hfx] at this; cases this
  · have : (f == t) = true :=
      tr _ _ _ hfz (by rw [Moist.Verified.InlineSoundness.Rename.beq_comm]; exact htz)
    rw [hft] at this; cases this
  · have : (f == t) = true :=
      tr _ _ _ hfz (by rw [Moist.Verified.InlineSoundness.Rename.beq_comm]; exact htz)
    rw [hft] at this; cases this

theorem lowerTotalExpr_rot {f t x : VarId} (hft : (f == t) = false) (hfx : (f == x) = false)
    (htx : (t == x) = false) (Γ : List VarId) (e : Expr) :
    lowerTotalExpr (x :: f :: t :: Γ) e = (lowerTotalExpr (f :: t :: x :: Γ) e).map (renameTerm rotRename) :=
  lowerTotalExpr_lookupShift e (lookupShift_rot hft hfx htx Γ)

theorem lookup_extend_three (ρ : CekEnv) (a b c : CekValue) (n : Nat) :
    (((ρ.extend a).extend b).extend c).lookup (n + 4) = ρ.lookup (n + 1) := rfl

theorem shiftBisimEnv_rot {ρ : CekEnv} {vr vn vc : CekValue} (hvr : ValueWellFormed vr)
    (hvn : ValueWellFormed vn) (hvc : ValueWellFormed vc) :
    ∀ {k : Nat}, EnvWellFormed k ρ →
      ShiftBisimEnv rotRename (k + 3) (((ρ.extend vr).extend vn).extend vc)
        (((ρ.extend vn).extend vc).extend vr)
  | 0, _ =>
    .succ (.succ (.succ .zero rfl rfl (shiftBisimValue_refl_id vc hvc)) rfl rfl
      (shiftBisimValue_refl_id vn hvn)) rfl rfl (shiftBisimValue_refl_id vr hvr)
  | k + 1, .succ (v := u) hrest _ hl hu =>
    .succ (shiftBisimEnv_rot hvr hvn hvc hrest) (by rw [lookup_extend_three]; exact hl)
      (by show (((ρ.extend vn).extend vc).extend vr).lookup (k + 4) = some u
          rw [lookup_extend_three]; exact hl)
      (shiftBisimValue_refl_id u hu)

/-- The shift bisimulation preserves constants. -/
theorem shiftBisim_vcon {c : Const} {w : CekValue} (h : ShiftBisimValue (.VCon c) w) :
    w = .VCon c := by
  cases h; rfl

theorem closedAt_rot {d : Nat} {t : Term} (h : closedAt (d + 3) t = true) :
    closedAt (d + 3) (renameTerm rotRename t) = true :=
  closedAt_rename _ t (d + 3) (d + 3) h fun n hn => by
    match n with
    | 0 => simp [rotRename]
    | 1 => simp [rotRename]
    | 2 => simp [rotRename]
    | 3 => simp [rotRename]
    | n + 4 => simp [rotRename]; omega

theorem closedAt_shift1 {d : Nat} {t : Term} (h : closedAt d t = true) :
    closedAt (d + 1) (renameTerm (shiftRename 1) t) = true :=
  Moist.Verified.closedAt_renameTerm_shiftRename t d 1 (Nat.le_refl 1) (by omega) h

theorem factRefines_sinkPair {d : Nat} {F : CekEnv → Prop} {tr tE tB : Term}
    (hr : closedAt d tr = true) (hE : closedAt d tE = true) (hB : closedAt (d + 3) tB = true)
    (hterm : TerminatesAt d (.Apply (.Builtin .UnConstrData) tE)) :
    FactRefines d F
      (.Apply (.Lam 0 (.Case (.Apply (.Builtin .UnConstrData) (renameTerm (shiftRename 1) tE))
        [.Lam 0 (.Lam 0 tB)])) tr)
      (.Case (.Apply (.Builtin .UnConstrData) tE)
        [.Lam 0 (.Lam 0 (.Apply (.Lam 0 (renameTerm rotRename tB))
          (renameTerm (shiftRename 1) (renameTerm (shiftRename 1) tr))))]) := by
  intro ρ π henv hlen hπ _
  have hSC : closedAt d (.Apply (.Builtin .UnConstrData) tE) = true := by
    simp [closedAt, hE]
  have hsrc : Reaches (.compute π ρ (.Apply (.Lam 0 (.Case (.Apply (.Builtin .UnConstrData)
      (renameTerm (shiftRename 1) tE)) [.Lam 0 (.Lam 0 tB)])) tr))
      (.compute (.funV (.VLam (.Case (.Apply (.Builtin .UnConstrData) (renameTerm (shiftRename 1) tE))
        [.Lam 0 (.Lam 0 tB)]) ρ) :: π) ρ tr) := reaches_of_steps 3 rfl
  have after : ∀ v, Reaches (.ret (.funV (.VLam (.Case (.Apply (.Builtin .UnConstrData)
        (renameTerm (shiftRename 1) tE)) [.Lam 0 (.Lam 0 tB)]) ρ) :: π) v)
      (.compute (.caseScrutinee [.Lam 0 (.Lam 0 tB)] (ρ.extend v) :: π) (ρ.extend v)
        (renameTerm (shiftRename 1) (.Apply (.Builtin .UnConstrData) tE))) :=
    fun _ => reaches_of_steps 2 rfl
  have frameOK : ∀ v, ValueWellFormed v →
      StackWellFormed (.caseScrutinee [.Lam 0 (.Lam 0 tB)] (ρ.extend v) :: π) := fun v hv =>
    .cons (.caseScrutinee (envWellFormed_extend d henv hlen hv)
      (by simp [CekEnv.extend, CekEnv.length]; omega) (by simp [closedAtList, closedAt, hB])) hπ
  rcases hterm ρ henv hlen with herrs | ⟨w, hw⟩
  · refine obsRefines_of_left_no_halt ?_ ?_
    · rintro ⟨u, hu⟩
      have hu' := reaches_terminal_after (.inr ⟨u, rfl⟩) hsrc hu
      rcases sequence (.inr ⟨u, rfl⟩) hu' with ⟨_, h⟩ | ⟨v, hv, hrest⟩
      · cases h
      · have hrest' := reaches_terminal_after (.inr ⟨u, rfl⟩) (after v) hrest
        have hvwf := halts_wellFormed henv hlen hr hv
        obtain ⟨u', hu''⟩ := (obsEq_shift v henv (frameOK v hvwf) hSC).2.halt ⟨u, hrest'⟩
        exact halt_not_error hu'' (errs_on_stack herrs _)
    · exact reaches_trans (reaches_of_steps 1 rfl) (errs_on_stack herrs _)
  · obtain ⟨n, cc, rfl⟩ := unConstrData_value hw
    have hn := envWellFormed_extend d henv hlen (.vcon (.Integer n))
    have hlen1 : d + 1 ≤ (ρ.extend (.VCon (.Integer n))).length := by
      simp [CekEnv.extend, CekEnv.length]; omega
    have hnc := envWellFormed_extend (d + 1) hn hlen1 (.vcon cc)
    have hlen2 : d + 2 ≤ ((ρ.extend (.VCon (.Integer n))).extend (.VCon cc)).length := by
      simp [CekEnv.extend, CekEnv.length]; omega
    have htgt : Reaches (.compute π ρ (.Case (.Apply (.Builtin .UnConstrData) tE)
        [.Lam 0 (.Lam 0 (.Apply (.Lam 0 (renameTerm rotRename tB))
          (renameTerm (shiftRename 1) (renameTerm (shiftRename 1) tr))))]))
        (.compute (.funV (.VLam (renameTerm rotRename tB)
          ((ρ.extend (.VCon (.Integer n))).extend (.VCon cc))) :: π)
          ((ρ.extend (.VCon (.Integer n))).extend (.VCon cc))
          (renameTerm (shiftRename 1) (renameTerm (shiftRename 1) tr))) :=
      reaches_trans (reaches_of_steps 1 rfl) (reaches_trans (halts_on_stack hw _)
        (reaches_trans (pair_dispatch ρ π _ n cc) (reaches_of_steps 3 rfl)))
    refine obsRefines_of_reaches hsrc htgt ?_
    have hframe : StackWellFormed (.funV (.VLam (renameTerm rotRename tB)
        ((ρ.extend (.VCon (.Integer n))).extend (.VCon cc))) :: π) :=
      .cons (.funV (.vlam hnc hlen2 (by simpa using closedAt_rot hB))) hπ
    refine obsRefines_trans ?_ (obsRefines_trans (obsEq_shift _ henv hframe hr).1
      (obsEq_shift _ hn hframe (closedAt_shift1 hr)).1)
    apply obsRefines_of_continuation
    intro vr hvr
    have hvrwf := halts_wellFormed henv hlen hr hvr
    obtain ⟨w', hw', hww⟩ := halts_shift vr henv hSC hw
    have := shiftBisim_vcon hww
    subst this
    refine obsRefines_of_reaches (reaches_trans (after vr) (reaches_trans (halts_on_stack hw' _)
      (pair_dispatch _ π tB n cc))) (reaches_of_steps 1 rfl) ?_
    exact (obsRefines_of_shiftBisim (.compute is0preserving_rotRename
      (shiftBisimEnv_rot hvrwf (.vcon _) (.vcon _) henv) hB (shiftBisimStack_refl hπ))).1

end Moist.Verified.TagGuard
