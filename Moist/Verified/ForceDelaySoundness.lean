import Moist.Verified.MIR
import Moist.Verified.MIR.Congruence
import Moist.Verified.MIR.Hoist
import Moist.Verified.FundamentalRefines
import Moist.Verified.BetaValueRefines
import Moist.Verified.InlineSoundness.StrictOcc
import Moist.Verified.InlineSoundness.Rename
import Moist.Verified.MIR.Primitives.LetFlattenBody
import Moist.Verified.HygieneSoundness
import Moist.MIR.Optimize.ForceDelay

/-! # Soundness of force/delay cancellation

`forceDelay_refines : MIRCtxRefines e (forceDelay e).1` for every MIR
expression `e`.

UPLC core. `FDRel I p t t'` says `t'` is `t` with some occurrences of
`Force (Var p)` replaced by `I` shifted to the current depth, where position
`p` holds the thunk `VDelay I ρ₀`. Forcing that thunk evaluates `I` in `ρ₀`,
and the shifted copy evaluated in the current environment reads the same
values, so the replacement is an open refinement (`fd_openRefines`).

MIR side. `lower_replace` lowers `replaceForceVar v inner X` to an
`FDRel`-related term when no binder of `X` captures `v` or a free variable of
`inner` (the guard the pass checks). Direct `Force (Delay e)` cancellation is
`forceDelay_openRefines`; the traversal composes both with the congruences.
-/

namespace Moist.Verified.ForceDelaySoundness

open Moist.CEK
open Moist.Plutus.Term (Term)
open Moist.Verified (closedAt closedAtList renameTerm renameTermList)
open Moist.Verified.Equivalence
open Moist.Verified.Contextual.Guarded
open Moist.Verified.Contextual.SoundnessRefines
open Moist.Verified.FundamentalRefines
open Moist.Verified.InlineSoundness.StrictOcc (multiShift is0preserving_multiShift)

/-! ## The replacement relation -/

mutual
  inductive FDRel (I : Term) : Nat → Term → Term → Prop
    | refl (p : Nat) (t : Term) : FDRel I p t t
    | site (p : Nat) : FDRel I p (.Force (.Var p)) (renameTerm (multiShift p) I)
    | lam (p n : Nat) {b b' : Term} : FDRel I (p + 1) b b' → FDRel I p (.Lam n b) (.Lam n b')
    | app (p : Nat) {f f' x x' : Term} :
        FDRel I p f f' → FDRel I p x x' → FDRel I p (.Apply f x) (.Apply f' x')
    | force (p : Nat) {e e' : Term} : FDRel I p e e' → FDRel I p (.Force e) (.Force e')
    | delay (p : Nat) {e e' : Term} : FDRel I p e e' → FDRel I p (.Delay e) (.Delay e')
    | constr (p tag : Nat) {args args' : List Term} :
        FDRelList I p args args' → FDRel I p (.Constr tag args) (.Constr tag args')
    | case (p : Nat) {s s' : Term} {alts alts' : List Term} :
        FDRel I p s s' → FDRelList I p alts alts' → FDRel I p (.Case s alts) (.Case s' alts')

  inductive FDRelList (I : Term) : Nat → List Term → List Term → Prop
    | nil (p : Nat) : FDRelList I p [] []
    | cons (p : Nat) {t t' : Term} {ts ts' : List Term} :
        FDRel I p t t' → FDRelList I p ts ts' → FDRelList I p (t :: ts) (t' :: ts')
end

/-! ## Closedness -/

mutual
  theorem fd_closedAt {I : Term} {d : Nat} (hI : closedAt d I = true) :
      ∀ {p : Nat} {t t' : Term}, FDRel I p t t' → closedAt (d + p) t = true →
        closedAt (d + p) t' = true
    | _, _, _, .refl _ _, h => h
    | p, _, _, .site _, _ =>
      Moist.Verified.BetaValueRefines.closedAt_rename (multiShift p) I d (d + p) hI
        (fun n hn => by simp only [multiShift]; split <;> omega)
    | p, _, _, .lam _ _ hb, h => by
      simp only [closedAt] at h ⊢
      have := fd_closedAt hI hb (by rw [← Nat.add_assoc]; exact h)
      rwa [← Nat.add_assoc] at this
    | _, _, _, .app _ hf hx, h => by
      simp only [closedAt, Bool.and_eq_true] at h ⊢
      exact ⟨fd_closedAt hI hf h.1, fd_closedAt hI hx h.2⟩
    | _, _, _, .force _ he, h => by
      simp only [closedAt] at h ⊢; exact fd_closedAt hI he h
    | _, _, _, .delay _ he, h => by
      simp only [closedAt] at h ⊢; exact fd_closedAt hI he h
    | _, _, _, .constr _ _ hl, h => by
      simp only [closedAt] at h ⊢; exact fd_closedAtList hI hl h
    | _, _, _, .case _ hs hl, h => by
      simp only [closedAt, Bool.and_eq_true] at h ⊢
      exact ⟨fd_closedAt hI hs h.1, fd_closedAtList hI hl h.2⟩

  theorem fd_closedAtList {I : Term} {d : Nat} (hI : closedAt d I = true) :
      ∀ {p : Nat} {ts ts' : List Term}, FDRelList I p ts ts' →
        closedAtList (d + p) ts = true → closedAtList (d + p) ts' = true
    | _, _, _, .nil _, h => h
    | _, _, _, .cons _ ht hts, h => by
      simp only [closedAtList, Bool.and_eq_true] at h ⊢
      exact ⟨fd_closedAt hI ht h.1, fd_closedAtList hI hts h.2⟩
end

/-! ## Environments -/

/-- Invariant at `p` binders below the thunk: the environments are related on
    `1..d + p`, the left one holds `VDelay I ρ₀` at `p`, and `ρ₀` agrees with
    the right environment shifted by `p`. -/
def FDEnv (I : Term) (d p k : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  EnvRel Guard.trivial k (d + p) ρ₁ ρ₂ ∧
  ∃ ρ₀, ρ₁.lookup p = some (.VDelay I ρ₀) ∧
    RenameEnvRef2 (ValueRel Guard.trivial) id (multiShift p) k d ρ₀ ρ₂

theorem envRel_mono {j k d : Nat} (hjk : j ≤ k) {ρ₁ ρ₂ : CekEnv}
    (h : EnvRel Guard.trivial k d ρ₁ ρ₂) : EnvRel Guard.trivial j d ρ₁ ρ₂ := by
  intro n hn hnd
  obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := h n hn hnd
  exact ⟨v₁, v₂, h₁, h₂, valueRel_mono hjk hv⟩

theorem fdEnv_mono {I : Term} {d p j k : Nat} (hjk : j ≤ k) {ρ₁ ρ₂ : CekEnv}
    (h : FDEnv I d p k ρ₁ ρ₂) : FDEnv I d p j ρ₁ ρ₂ := by
  obtain ⟨henv, ρ₀, hlook, hren⟩ := h
  exact ⟨envRel_mono hjk henv, ρ₀, hlook,
    renameEnvRef2_map (fun _ _ h => valueRel_mono hjk h) hren⟩

private theorem lookup_zero (ρ : CekEnv) : ρ.lookup 0 = none := by
  cases ρ <;> rfl

theorem fdEnv_extend {I : Term} {d p k : Nat} {ρ₁ ρ₂ : CekEnv} {a₁ a₂ : CekValue}
    (h : FDEnv I d p k ρ₁ ρ₂) (ha : ValueRel Guard.trivial k a₁ a₂) :
    FDEnv I d (p + 1) k (ρ₁.extend a₁) (ρ₂.extend a₂) := by
  obtain ⟨henv, ρ₀, hlook, hren⟩ := h
  have hp : p ≠ 0 := by
    intro hp; subst hp; rw [lookup_zero] at hlook; exact Option.noConfusion hlook
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  refine ⟨fun n hn hnd => ?_, ρ₀, hlook, fun n hn hnd => ?_⟩
  · match n with
    | 1 => exact ⟨a₁, a₂, rfl, rfl, ha⟩
    | m + 2 =>
      obtain ⟨w₁, w₂, h₁, h₂, hw⟩ := henv (m + 1) (by omega) (by omega)
      exact ⟨w₁, w₂, h₁, h₂, hw⟩
  · have hms : multiShift (q + 1 + 1) n = multiShift (q + 1) n + 1 := by
      simp only [multiShift]; split <;> omega
    have hms' : multiShift (q + 1) n = (n + q) + 1 := by
      simp only [multiShift]; split <;> omega
    have := hren n hn hnd
    rw [hms, hms']
    rw [hms'] at this
    exact this

/-! ## The logical relation -/

private theorem eval_refl {d p k : Nat} {ρ₁ ρ₂ : CekEnv} {t : Term}
    (ht : closedAt (d + p) t = true) (henv : EnvRel Guard.trivial k (d + p) ρ₁ ρ₂) :
    Eval Guard.trivial k ρ₁ ρ₂ t t := by
  have h := renameRefinesG Guard.trivial id id is0preserving_id is0preserving_id (d + p) t ht k
    (renameEnvRef2_id henv)
  rwa [Moist.Verified.renameTerm_id] at h

mutual
  theorem fd_eval {I : Term} {d : Nat} (hI : closedAt d I = true) :
      ∀ {p : Nat} {t t' : Term}, FDRel I p t t' → closedAt (d + p) t = true →
        ∀ (k : Nat) {ρ₁ ρ₂ : CekEnv}, FDEnv I d p k ρ₁ ρ₂ →
          Eval Guard.trivial k ρ₁ ρ₂ t t'
    | _, _, _, .refl _ _, ht, k, _, _, henv => eval_refl ht henv.1
    | p, _, _, .site _, _, k, ρ₁, ρ₂, henv => by
      obtain ⟨_, ρ₀, hlook, hren⟩ := henv
      intro j hj π₁ π₂ hπ _ _
      have hsteps : steps 3 (.compute π₁ ρ₁ (.Force (.Var p))) = .compute π₁ ρ₀ I := by
        simp [steps, step, hlook]
      refine obsRefinesK_of_steps_left hsteps ?_
      have h := renameRefinesG Guard.trivial id (multiShift p) is0preserving_id
        (is0preserving_multiShift p) d I hI k hren
      rw [Moist.Verified.renameTerm_id] at h
      exact h j hj π₁ π₂ hπ trivial trivial
    | p, _, _, .lam _ _ hb, ht, k, ρ₁, ρ₂, henv => by
      simp only [closedAt] at ht
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      refine ret_obs (valueRel_lam (W := Guard.trivial) trivial trivial
        fun j' hj' a₁ a₂ ha _ _ => ?_) hst₁ hst₂ hπ
      exact fd_eval hI hb (by rw [← Nat.add_assoc]; exact ht) j'
        (fdEnv_extend (fdEnv_mono (by omega) henv) ha)
    | _, _, _, .app _ hf hx, ht, k, _, _, henv => by
      simp only [closedAt, Bool.and_eq_true] at ht
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      exact fd_eval hI hf ht.1 j (fdEnv_mono (by omega) henv) j (Nat.le_refl _) _ _
        (arg_stackRel (fd_eval hI hx ht.2 j (fdEnv_mono (by omega) henv))
          trivial trivial hπ) hst₁ hst₂
    | _, _, _, .force _ he, ht, k, _, _, henv => by
      simp only [closedAt] at ht
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      exact fd_eval hI he ht j (fdEnv_mono (by omega) henv) j (Nat.le_refl _) _ _
        (force_stackRel hπ) hst₁ hst₂
    | _, _, _, .delay _ he, ht, k, _, _, henv => by
      simp only [closedAt] at ht
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      exact ret_obs (valueRel_delay (W := Guard.trivial) trivial trivial
        fun j' hj' => fd_eval hI he ht j' (fdEnv_mono (by omega) henv)) hst₁ hst₂ hπ
    | _, _, _, .constr _ _ (.nil _), _, k, _, _, _ =>
      eval_of_step fun j _ _ _ hπ hst₁ hst₂ =>
        ret_obs (valueRel_constr (W := Guard.trivial) (k := j) trivial) hst₁ hst₂ hπ
    | _, _, _, .constr _ _ (.cons _ hm hms), ht, k, _, _, henv => by
      simp only [closedAt, closedAtList, Bool.and_eq_true] at ht
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      exact fd_eval hI hm ht.1 j (fdEnv_mono (by omega) henv) j (Nat.le_refl _) _ _
        (constrField_stackRel (fd_evalList hI hms ht.2 j (fdEnv_mono (by omega) henv))
          trivial trivial trivial hπ) hst₁ hst₂
    | _, _, _, .case _ hs halts, ht, k, _, _, henv => by
      simp only [closedAt, Bool.and_eq_true] at ht
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      exact fd_eval hI hs ht.1 j (fdEnv_mono (by omega) henv) j (Nat.le_refl _) _ _
        (case_stackRel (altsRel_of_listRel
            (fd_evalList hI halts ht.2 j (fdEnv_mono (by omega) henv)))
          trivial trivial hπ) hst₁ hst₂

  theorem fd_evalList {I : Term} {d : Nat} (hI : closedAt d I = true) :
      ∀ {p : Nat} {ts ts' : List Term}, FDRelList I p ts ts' → closedAtList (d + p) ts = true →
        ∀ (k : Nat) {ρ₁ ρ₂ : CekEnv}, FDEnv I d p k ρ₁ ρ₂ →
          ListRel (Eval Guard.trivial k ρ₁ ρ₂) ts ts'
    | _, _, _, .nil _, _, _, _, _, _ => trivial
    | _, _, _, .cons _ ht hts, h, k, _, _, henv => by
      simp only [closedAtList, Bool.and_eq_true] at h
      exact ⟨fd_eval hI ht h.1 k henv, fd_evalList hI hts h.2 k henv⟩
end

/-! ## The root redex -/

private theorem steps_apply_lam_delay (π : Stack) (ρ : CekEnv) (B I : Term) :
    steps 5 (.compute π ρ (.Apply (.Lam 0 B) (.Delay I))) =
      .compute π (ρ.extend (.VDelay I ρ)) B := by
  rfl

/-- Replacing forced occurrences of a delayed let binding by the delayed body
    is an open refinement. -/
theorem fd_openRefines {I B B' : Term} {d : Nat} (hI : closedAt d I = true)
    (hB : closedAt (d + 1) B = true) (h : FDRel I 1 B B') :
    OpenRefines d (.Apply (.Lam 0 B) (.Delay I)) (.Apply (.Lam 0 B') (.Delay I)) := by
  intro k j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  refine obsRefinesK_of_steps_left (steps_apply_lam_delay π₁ ρ₁ B I)
    (obsRefinesK_of_steps_right (steps_apply_lam_delay π₂ ρ₂ B' I) ?_)
  have henvI : EnvRel Guard.trivial i d ρ₁ ρ₂ := fun n hn hnd => by
    obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := henv n hn hnd
    exact ⟨v₁, v₂, h₁, h₂, (valueRel_trivial i v₁ v₂).mpr (valueRefinesK_mono hi _ _ hv)⟩
  have hdelay : ValueRel Guard.trivial i (.VDelay I ρ₁) (.VDelay I ρ₂) :=
    valueRel_delay trivial trivial fun j' hj' => by
      have h := renameRefinesG Guard.trivial id id is0preserving_id is0preserving_id d I hI j'
        (renameEnvRef2_id (envRel_mono (by omega) henvI))
      rwa [Moist.Verified.renameTerm_id] at h
  have hfd : FDEnv I d 1 i (ρ₁.extend (.VDelay I ρ₁)) (ρ₂.extend (.VDelay I ρ₂)) := by
    refine ⟨fun n hn hnd => ?_, ρ₁, rfl, fun n hn hnd => ?_⟩
    · match n with
      | 1 => exact ⟨_, _, rfl, rfl, hdelay⟩
      | m + 2 =>
        obtain ⟨w₁, w₂, h₁, h₂, hw⟩ := henvI (m + 1) (by omega) (by omega)
        exact ⟨w₁, w₂, h₁, h₂, hw⟩
    · obtain ⟨w₁, w₂, h₁, h₂, hw⟩ := henvI n hn hnd
      have hms : multiShift 1 n = n + 1 := by simp only [multiShift]; split <;> omega
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      show match ρ₁.lookup (m + 1), (ρ₂.extend _).lookup (multiShift 1 (m + 1)) with
        | some v₁, some v₂ => ValueRel Guard.trivial i v₁ v₂
        | none, none => True
        | _, _ => False
      rw [hms]
      show match ρ₁.lookup (m + 1), ρ₂.lookup (m + 1) with
        | some v₁, some v₂ => ValueRel Guard.trivial i v₁ v₂
        | none, none => True
        | _, _ => False
      rw [h₁, h₂]; exact hw
  exact fd_eval hI h hB i hfd i (Nat.le_refl _) π₁ π₂ (stackRefK_iff_stackRel.mp hπ)
    trivial trivial

/-- `Force (Delay t)` is refined by `t`. -/
theorem forceDelay_openRefines {t : Term} {d : Nat} (ht : closedAt d t = true) :
    OpenRefines d (.Force (.Delay t)) t := by
  intro k j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  have hsteps : steps 3 (.compute π₁ ρ₁ (.Force (.Delay t))) = .compute π₁ ρ₁ t := rfl
  exact obsRefinesK_of_steps_left hsteps (ftlr d t ht k j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ)

/-! ## Lowering the MIR replacement -/

section Lowering

open Moist.MIR (Expr VarId VarSet lowerTotalExpr lowerTotal freeVars envLookupT expandFix
  maxUidExpr fixLamWrapUplc isVarOf bindersAvoid bindersAvoidList bindersAvoidLet
  replaceForceVar replaceForceVarList replaceForceVarLet)
open Moist.Verified.MIR (lowerTotalExprList lowerTotalExprList_nil lowerTotalExprList_cons
  lowerTotalExpr_force lowerTotalExpr_delay lowerTotalExpr_lam lowerTotalExpr_app
  lowerTotalExpr_constr_of_list lowerTotalExpr_case_of_list lowerTotalExpr_fix_nonlam_none)
open Moist.Verified.InlineSoundness.StrictOcc (renameTerm_renameTerm multiShift_succ
  renameTerm_multiShift_zero)

theorem FDRel.cast {I : Term} {p q : Nat} {t t' : Term} (h : p = q) (r : FDRel I p t t') :
    FDRel I q t t' := h ▸ r

theorem FDRel.lam_inv {I : Term} {p n : Nat} {b t' : Term} (h : FDRel I p (.Lam n b) t') :
    ∃ b', t' = .Lam n b' ∧ FDRel I (p + 1) b b' := by
  cases h with
  | refl => exact ⟨b, rfl, .refl _ _⟩
  | lam _ _ hb => exact ⟨_, rfl, hb⟩

theorem fdRel_fixLamWrap {I : Term} {p : Nat} {B B' : Term} (h : FDRel I (p + 3) B B') :
    FDRel I p (fixLamWrapUplc B) (fixLamWrapUplc B') :=
  .app p (.refl _ _) (.lam p 0 (.app (p + 1) (.lam (p + 1) 0 (.lam (p + 2) 0 h)) (.refl _ _)))

/-- Lowering under binders that are not free shifts by their number. -/
theorem lowerTotalExpr_prepend_many (e : Expr) (env : List VarId) :
    ∀ ys : List VarId, (∀ y ∈ ys, (freeVars e).contains y = false) →
      lowerTotalExpr (ys ++ env) e = (lowerTotalExpr env e).map (renameTerm (multiShift ys.length))
  | [], _ => by
    cases h : lowerTotalExpr env e <;> simp [h, renameTerm_multiShift_zero]
  | y :: ys, h => by
    rw [List.cons_append, Moist.Verified.MIR.lowerTotalExpr_prepend_unused _ y _ (h y (.head _)),
      lowerTotalExpr_prepend_many e env ys (fun z hz => h z (.tail _ hz))]
    cases lowerTotalExpr env e with
    | none => rfl
    | some t =>
      simp only [Option.map_some, List.length_cons]
      rw [renameTerm_renameTerm _ _ (is0preserving_multiShift _)]
      congr 2
      funext n
      exact (multiShift_succ _ n).symm

private theorem beq_symm_false {a b : VarId} (h : (a == b) = false) : (b == a) = false := by
  cases hba : (b == a)
  · rfl
  · rw [Moist.MIR.VarId.beq_true_iff] at hba
    have : (a == b) = true := by
      rw [Moist.MIR.VarId.beq_true_iff]; exact ⟨hba.1.symm, hba.2.symm⟩
    rw [this] at h; exact absurd h (by simp)

private theorem beq_false_of_chain {x w v : VarId} (hwv : (w == v) = true) (hvx : (v == x) = false) :
    (x == w) = false := by
  cases hxw : (x == w)
  · rfl
  · rw [Moist.MIR.VarId.beq_true_iff] at hxw hwv
    have : (v == x) = true := by
      rw [Moist.MIR.VarId.beq_true_iff]
      exact ⟨(hxw.1.trans hwv.1).symm, (hxw.2.trans hwv.2).symm⟩
    rw [this] at hvx; exact absurd hvx (by simp)

theorem envLookupT_go_append_hit {w v : VarId} (env : List VarId) (hvw : (v == w) = true) :
    ∀ (xs : List VarId) (n : Nat), (∀ x ∈ xs, (x == w) = false) →
      envLookupT.go w (xs ++ v :: env) n = some (n + xs.length)
  | [], n, _ => by simp [envLookupT.go, hvw]
  | x :: xs, n, h => by
    simp only [List.cons_append, envLookupT.go, h x (.head _), Bool.false_eq_true, ↓reduceIte]
    rw [envLookupT_go_append_hit env hvw xs (n + 1) (fun y hy => h y (.tail _ hy))]
    simp only [List.length_cons]; congr 1; omega

/-- Avoiding `fv(inner) ∪ {v}`. -/
private theorem avoid_split {s : VarSet} {v x : VarId} (h : (s.insert v).contains x = false) :
    s.contains x = false ∧ (v == x) = false := by
  constructor
  · cases hc : s.contains x
    · rfl
    · have := (VarSet.contains_insert_elim s v x).mpr (.inl hc); rw [this] at h; exact absurd h (by simp)
  · cases hc : (v == x)
    · rfl
    · have := (VarSet.contains_insert_elim s v x).mpr (.inr hc); rw [this] at h; exact absurd h (by simp)

private theorem avoid_of_split {s : VarSet} {v x : VarId} (h₁ : s.contains x = false)
    (h₂ : (v == x) = false) : (s.insert v).contains x = false := by
  cases hc : (s.insert v).contains x
  · rfl
  · rcases (VarSet.contains_insert_elim s v x).mp hc with h | h
    · rw [h] at h₁; exact absurd h₁ (by simp)
    · rw [h] at h₂; exact absurd h₂ (by simp)

variable {v : VarId} {inner : Expr} {env : List VarId} {I : Term}

theorem lowerTotalExpr_inner_at (hI : lowerTotalExpr env inner = some I)
    (hv : (freeVars inner).contains v = false) {xs : List VarId}
    (hxs : ∀ x ∈ xs, ((freeVars inner).insert v).contains x = false) :
    lowerTotalExpr (xs ++ v :: env) inner = some (renameTerm (multiShift (xs.length + 1)) I) := by
  have h := lowerTotalExpr_prepend_many inner env (xs ++ [v]) (by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact (avoid_split (hxs y hy)).1
    · simp only [List.mem_singleton] at hy; subst hy; exact hv)
  rw [List.append_assoc, List.singleton_append, hI] at h
  simpa using h

theorem replaceForceVar_let_avoid {s : VarSet} (repl : Expr) (body : Expr) :
    ∀ (rest : List (VarId × Expr × Bool)), bindersAvoidLet (s.insert v) rest body = true →
      replaceForceVarLet v repl rest body =
        (rest.map fun (w, r, er) => (w, replaceForceVar v repl r, er), replaceForceVar v repl body)
  | [], _ => by simp [replaceForceVarLet]
  | (x, rhs, er) :: rest, h => by
    simp only [bindersAvoidLet, Bool.and_eq_true, Bool.not_eq_true'] at h
    have hxv : (x == v) = false := beq_symm_false (avoid_split h.1.1).2
    rw [replaceForceVarLet]
    simp only [hxv, Bool.false_eq_true, ↓reduceIte, List.map_cons]
    rw [replaceForceVar_let_avoid repl body rest h.2]

private theorem some_map_inv {α β : Type} {f : α → β} {o : Option α} {b : β}
    (h : o.map f = some b) : ∃ a, o = some a ∧ b = f a := by
  cases o with
  | none => simp at h
  | some a => simp at h; exact ⟨a, rfl, h.symm⟩

private theorem some_bind2_inv {α β γ : Type} {o₁ : Option α} {o₂ : Option β} {f : α → β → γ}
    {c : γ} (h : (do let a ← o₁; let b ← o₂; some (f a b)) = some c) :
    ∃ a b, o₁ = some a ∧ o₂ = some b ∧ c = f a b := by
  cases o₁ <;> cases o₂ <;> simp at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

mutual
  /-- Replacing `Force (Var v)` by `inner` in `X` lowers, under binders `xs`
      that avoid `fv(inner) ∪ {v}`, to an `FDRel`-related term. -/
  theorem lower_replace (hI : lowerTotalExpr env inner = some I)
      (hv : (freeVars inner).contains v = false) :
      ∀ (X : Expr) (xs : List VarId) (t : Term),
        bindersAvoid ((freeVars inner).insert v) X = true →
        (∀ x ∈ xs, ((freeVars inner).insert v).contains x = false) →
        lowerTotalExpr (xs ++ v :: env) X = some t →
        ∃ t', lowerTotalExpr (xs ++ v :: env) (replaceForceVar v inner X) = some t' ∧
          FDRel I (xs.length + 1) t t'
    | .Var w, xs, t, _, _, h => ⟨t, by rw [replaceForceVar]; exact h, .refl _ _⟩
    | .Lit c, xs, t, _, _, h => ⟨t, by rw [replaceForceVar]; exact h, .refl _ _⟩
    | .Builtin b, xs, t, _, _, h => ⟨t, by rw [replaceForceVar]; exact h, .refl _ _⟩
    | .Error, xs, t, _, _, h => ⟨t, by rw [replaceForceVar]; exact h, .refl _ _⟩
    | .Force e, xs, t, hav, hxs, h => by
      rw [bindersAvoid] at hav
      by_cases hvar : isVarOf v e = true
      · cases e with
        | Var w =>
          simp only [isVarOf] at hvar
          rw [replaceForceVar, if_pos (by simpa [isVarOf] using hvar)]
          have hlook : envLookupT (xs ++ v :: env) w = some xs.length := by
            have := envLookupT_go_append_hit env (w := w) (v := v)
              (by rw [Moist.MIR.VarId.beq_true_iff] at hvar ⊢; exact ⟨hvar.1.symm, hvar.2.symm⟩)
              xs 0 (fun x hx => beq_false_of_chain hvar (avoid_split (hxs x hx)).2)
            simpa [envLookupT] using this
          have ht : lowerTotalExpr (xs ++ v :: env) (.Force (.Var w)) =
              some (.Force (.Var (xs.length + 1))) := by
            simp [lowerTotalExpr, expandFix, lowerTotal, hlook]
          rw [ht] at h; cases h
          exact ⟨_, lowerTotalExpr_inner_at hI hv hxs, .site _⟩
        | _ => simp [isVarOf] at hvar
      · rw [replaceForceVar, if_neg hvar]
        rw [lowerTotalExpr_force] at h ⊢
        obtain ⟨te, hte, rfl⟩ := some_map_inv h
        obtain ⟨te', h', hrel⟩ := lower_replace hI hv e xs te hav hxs hte
        exact ⟨_, by rw [h']; rfl, .force _ hrel⟩
    | .Delay e, xs, t, hav, hxs, h => by
      rw [bindersAvoid] at hav
      rw [replaceForceVar, lowerTotalExpr_delay]
      rw [lowerTotalExpr_delay] at h
      obtain ⟨te, hte, rfl⟩ := some_map_inv h
      obtain ⟨te', h', hrel⟩ := lower_replace hI hv e xs te hav hxs hte
      exact ⟨_, by rw [h']; rfl, .delay _ hrel⟩
    | .Lam x b, xs, t, hav, hxs, h => by
      simp only [bindersAvoid, Bool.and_eq_true, Bool.not_eq_true'] at hav
      have hxv : (x == v) = false := beq_symm_false (avoid_split hav.1).2
      rw [replaceForceVar, if_neg (by simp [hxv]), lowerTotalExpr_lam]
      rw [lowerTotalExpr_lam] at h
      obtain ⟨tb, htb, rfl⟩ := some_map_inv h
      have hxs' : ∀ y ∈ x :: xs, ((freeVars inner).insert v).contains y = false := by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hav.1
        · exact hxs y hy
      obtain ⟨tb', h', hrel⟩ := lower_replace hI hv b (x :: xs) tb hav.2 hxs' htb
      exact ⟨_, by simp only [List.cons_append] at h'; rw [h']; rfl,
        .lam _ _ (hrel.cast (by simp))⟩
    | .Fix f body, xs, t, hav, hxs, h => by
      simp only [bindersAvoid, Bool.and_eq_true, Bool.not_eq_true'] at hav
      have hfv : (f == v) = false := beq_symm_false (avoid_split hav.1).2
      rw [replaceForceVar, if_neg (by simp [hfv])]
      let s : VarId := ⟨max (max (maxUidExpr (expandFix body))
        (maxUidExpr (expandFix (replaceForceVar v inner body))))
        (max (maxUidExpr inner) v.uid) + 1, .gen, "s"⟩
      have hs : ((freeVars inner).insert v).contains s = false :=
        avoid_of_split (Moist.MIR.maxUidExpr_fresh _ s (by simp [s]; omega))
          (by rw [Moist.MIR.VarId.beq_false_iff]; right; simp [s]; omega)
      have hxs' : ∀ y ∈ f :: s :: xs, ((freeVars inner).insert v).contains y = false := by
        intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | rfl | hy
        · exact hav.1
        · exact hs
        · exact hxs y hy
      have ih := fun tb hb => lower_replace hI hv body (f :: s :: xs) tb hav.2 hxs' hb
      by_cases hlam : ∃ x b, body = .Lam x b
      · obtain ⟨x, b, rfl⟩ := hlam
        have hav2 := hav.2
        simp only [bindersAvoid, Bool.and_eq_true, Bool.not_eq_true'] at hav2
        have hxv : (x == v) = false := beq_symm_false (avoid_split hav2.1).2
        have hrl : replaceForceVar v inner (.Lam x b) = .Lam x (replaceForceVar v inner b) := by
          rw [replaceForceVar, if_neg (by simp [hxv])]
        rw [hrl]
        rw [hrl] at ih
        have hs₁ : (freeVars (expandFix b)).contains s = false :=
          Moist.MIR.maxUidExpr_fresh _ s (by
            simp only [s, expandFix, maxUidExpr] at *; omega)
        have hs₂ : (freeVars (expandFix (replaceForceVar v inner b))).contains s = false :=
          Moist.MIR.maxUidExpr_fresh _ s (by
            simp only [s, hrl, expandFix, maxUidExpr] at *; omega)
        rw [Moist.MIR.lowerTotalExpr_fix_lam_with_fresh _ f x b s hs₁] at h
        rw [Moist.MIR.lowerTotalExpr_fix_lam_with_fresh _ f x _ s hs₂]
        obtain ⟨tb, htb, rfl⟩ := some_map_inv h
        have hlow : lowerTotalExpr ((f :: s :: xs) ++ v :: env) (.Lam x b) = some (.Lam 0 tb) := by
          simp only [List.cons_append]
          rw [lowerTotalExpr_lam]
          show (lowerTotalExpr (x :: f :: s :: (xs ++ v :: env)) b).map _ = _
          rw [show lowerTotalExpr (x :: f :: s :: (xs ++ v :: env)) b = some tb from htb]; rfl
        obtain ⟨tl', h', hrel⟩ := ih _ hlow
        simp only [List.cons_append] at h'
        rw [lowerTotalExpr_lam] at h'
        obtain ⟨tb', htb', rfl⟩ := some_map_inv h'
        obtain ⟨b', hb', hrelb⟩ := FDRel.lam_inv hrel
        cases hb'
        refine ⟨_, ?_, fdRel_fixLamWrap (hrelb.cast (by simp only [List.length_cons]))⟩
        show (lowerTotalExpr (x :: f :: s :: (xs ++ v :: env)) (replaceForceVar v inner b)).map
          fixLamWrapUplc = _
        rw [htb']; rfl
      · rw [lowerTotalExpr_fix_nonlam_none _ f body
          (fun x b hb => hlam ⟨x, b, hb⟩)] at h
        exact absurd h (by simp)
    | .App fn arg, xs, t, hav, hxs, h => by
      simp only [bindersAvoid, Bool.and_eq_true] at hav
      rw [replaceForceVar, lowerTotalExpr_app]
      rw [lowerTotalExpr_app] at h
      obtain ⟨tf, ta, htf, hta, rfl⟩ := some_bind2_inv h
      obtain ⟨tf', hf', hrelf⟩ := lower_replace hI hv fn xs tf hav.1 hxs htf
      obtain ⟨ta', ha', hrela⟩ := lower_replace hI hv arg xs ta hav.2 hxs hta
      exact ⟨_, by rw [hf', ha']; rfl, .app _ hrelf hrela⟩
    | .Constr tag args, xs, t, hav, hxs, h => by
      rw [bindersAvoid] at hav
      rw [replaceForceVar, lowerTotalExpr_constr_of_list]
      rw [lowerTotalExpr_constr_of_list] at h
      obtain ⟨ts, hts, rfl⟩ := some_map_inv h
      obtain ⟨ts', h', hrel⟩ := lower_replaceList hI hv args xs ts hav hxs hts
      exact ⟨_, by rw [h']; rfl, .constr _ _ hrel⟩
    | .Case scrut alts, xs, t, hav, hxs, h => by
      simp only [bindersAvoid, Bool.and_eq_true] at hav
      rw [replaceForceVar, lowerTotalExpr_case_of_list]
      rw [lowerTotalExpr_case_of_list] at h
      obtain ⟨ts, tas, hts, htas, rfl⟩ := some_bind2_inv h
      obtain ⟨ts', hs', hrels⟩ := lower_replace hI hv scrut xs ts hav.1 hxs hts
      obtain ⟨tas', has', hrela⟩ := lower_replaceList hI hv alts xs tas hav.2 hxs htas
      exact ⟨_, by rw [hs', has']; rfl, .case _ hrels hrela⟩
    | .Let [] body, xs, t, hav, hxs, h => by
      simp only [bindersAvoid, bindersAvoidLet] at hav
      rw [replaceForceVar]
      simp only [replaceForceVarLet]
      rw [Moist.Verified.MIR.lowerTotalExpr_let_nil_eq]
      rw [Moist.Verified.MIR.lowerTotalExpr_let_nil_eq] at h
      exact lower_replace hI hv body xs t hav hxs h
    | .Let ((x, rhs, er) :: rest) body, xs, t, hav, hxs, h => by
      simp only [bindersAvoid, bindersAvoidLet, Bool.and_eq_true, Bool.not_eq_true'] at hav
      have hxv : (x == v) = false := beq_symm_false (avoid_split hav.1.1).2
      have hunfold : replaceForceVar v inner (.Let ((x, rhs, er) :: rest) body) =
          .Let ((x, replaceForceVar v inner rhs, er) ::
            (replaceForceVarLet v inner rest body).1) (replaceForceVarLet v inner rest body).2 := by
        rw [replaceForceVar, replaceForceVarLet]
        simp [hxv]
      have hrest : replaceForceVar v inner (.Let rest body) =
          .Let (replaceForceVarLet v inner rest body).1 (replaceForceVarLet v inner rest body).2 := by
        rw [replaceForceVar]
      rw [hunfold, Moist.Verified.InlineSoundness.Rename.lowerTotalExpr_let_cons]
      rw [Moist.Verified.InlineSoundness.Rename.lowerTotalExpr_let_cons] at h
      obtain ⟨tr, tb, htr, htb, rfl⟩ := some_bind2_inv h
      have hxs' : ∀ y ∈ x :: xs, ((freeVars inner).insert v).contains y = false := by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hav.1.1
        · exact hxs y hy
      obtain ⟨tr', hr', hrelr⟩ := lower_replace hI hv rhs xs tr hav.1.2 hxs htr
      obtain ⟨tb', hb', hrelb⟩ := lower_replace hI hv (.Let rest body) (x :: xs) tb
        (by simp only [bindersAvoid]; exact hav.2) hxs' htb
      rw [hrest] at hb'
      simp only [List.cons_append] at hb'
      exact ⟨_, by rw [hr', hb']; rfl, .app _ (.lam _ _ (hrelb.cast (by simp))) hrelr⟩
  termination_by X => sizeOf X
  decreasing_by all_goals simp_wf <;> omega

  theorem lower_replaceList (hI : lowerTotalExpr env inner = some I)
      (hv : (freeVars inner).contains v = false) :
      ∀ (Xs : List Expr) (xs : List VarId) (ts : List Term),
        bindersAvoidList ((freeVars inner).insert v) Xs = true →
        (∀ x ∈ xs, ((freeVars inner).insert v).contains x = false) →
        lowerTotalExprList (xs ++ v :: env) Xs = some ts →
        ∃ ts', lowerTotalExprList (xs ++ v :: env) (replaceForceVarList v inner Xs) = some ts' ∧
          FDRelList I (xs.length + 1) ts ts'
    | [], xs, ts, _, _, h => by
      rw [lowerTotalExprList_nil] at h; cases h
      exact ⟨[], by rw [replaceForceVarList, lowerTotalExprList_nil], .nil _⟩
    | X :: Xs, xs, ts, hav, hxs, h => by
      simp only [bindersAvoidList, Bool.and_eq_true] at hav
      rw [lowerTotalExprList_cons] at h
      obtain ⟨t, ts₀, ht, hts, rfl⟩ := some_bind2_inv h
      obtain ⟨t', h', hrel⟩ := lower_replace hI hv X xs t hav.1 hxs ht
      obtain ⟨ts', hs', hrels⟩ := lower_replaceList hI hv Xs xs ts₀ hav.2 hxs hts
      exact ⟨_, by rw [replaceForceVarList, lowerTotalExprList_cons, h', hs']; rfl,
        .cons _ hrel hrels⟩
  termination_by Xs => sizeOf Xs
  decreasing_by all_goals simp_wf <;> omega
end

end Lowering

/-! ## MIR rules -/

section Rules

open Moist.MIR (Expr VarId VarSet lowerTotalExpr freeVars bindersAvoid bindersAvoidLet
  replaceForceVar replaceForceVarLet)
open Moist.Verified.MIR (MIRCtxRefines lowerTotalExpr_closedAt lowerTotalExpr_force
  lowerTotalExpr_delay ctxRefines_of_openRefines)

/-- `Force (Delay e)` is refined by `e`. -/
theorem mirCtxRefines_force_delay (e : Expr) : MIRCtxRefines (.Force (.Delay e)) e := by
  intro env
  rw [lowerTotalExpr_force, lowerTotalExpr_delay]
  cases h : lowerTotalExpr env e with
  | none => exact ⟨by simp, trivial⟩
  | some t =>
    refine ⟨fun _ => rfl, ?_⟩
    exact ctxRefines_of_openRefines (fun k hk => by simpa [closedAt] using hk)
      (forceDelay_openRefines (lowerTotalExpr_closedAt h))

/-- The through-let rule: with `v` bound to `Delay inner`, every
    `Force (Var v)` in the rest of the let may be replaced by `inner`, provided
    no binder in the rest captures `v` or a free variable of `inner`. -/
theorem mirCtxRefines_delay_let (v : VarId) (inner : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr)
    (hv : (freeVars inner).contains v = false)
    (hav : bindersAvoid ((freeVars inner).insert v) (.Let rest body) = true) :
    MIRCtxRefines (.Let ((v, .Delay inner, er) :: rest) body)
      (.Let ((v, .Delay inner, er) ::
          rest.map fun (w, r, er₂) => (w, replaceForceVar v inner r, er₂))
        (replaceForceVar v inner body)) := by
  intro env
  have hrepl : replaceForceVar v inner (.Let rest body) =
      .Let (rest.map fun (w, r, er₂) => (w, replaceForceVar v inner r, er₂))
        (replaceForceVar v inner body) := by
    rw [replaceForceVar]
    have hav' := hav
    simp only [bindersAvoid] at hav'
    rw [replaceForceVar_let_avoid inner body rest hav']
  rw [Moist.Verified.InlineSoundness.Rename.lowerTotalExpr_let_cons,
    Moist.Verified.InlineSoundness.Rename.lowerTotalExpr_let_cons, lowerTotalExpr_delay]
  cases hI : lowerTotalExpr env inner with
  | none => exact ⟨by simp, trivial⟩
  | some I =>
    cases hB : lowerTotalExpr (v :: env) (.Let rest body) with
    | none => exact ⟨by simp, trivial⟩
    | some B =>
      obtain ⟨B', hB', hrel⟩ := lower_replace (env := env) hI hv (.Let rest body) [] B hav
        (fun _ h => nomatch h) hB
      rw [hrepl] at hB'
      simp only [List.nil_append] at hB'
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, hB']
      refine ⟨fun _ => rfl, ?_⟩
      have hIc : closedAt env.length I = true := lowerTotalExpr_closedAt hI
      have hBc : closedAt (env.length + 1) B = true := by
        simpa using lowerTotalExpr_closedAt hB
      refine ctxRefines_of_openRefines (fun k hk => ?_) (fd_openRefines hIc hBc hrel)
      simp only [closedAt, Bool.and_eq_true] at hk ⊢
      exact ⟨fd_closedAt hk.2 hrel hk.1, hk.2⟩

end Rules

/-! ## The pass -/

section Pass

open Moist.MIR (Expr VarId lowerTotalExpr freeVars bindersAvoid processDelayBindings
  forceDelayCore forceDelayList forceDelayBinds forceDelay uniqueOptimizationBinders
  replaceForceVar)
open Moist.Verified.MIR (MIRCtxRefines mirCtxRefines_refl mirCtxRefines_trans
  mirCtxRefines_of_lowerEq mirCtxRefines_lam mirCtxRefines_fix_lam mirCtxRefines_fix_nonlam_lhs
  mirCtxRefines_app mirCtxRefines_delay mirCtxRefines_force mirCtxRefines_constr
  mirCtxRefines_case mirCtxRefines_let_body mirCtxRefines_let_binds_congr
  lowerTotalExpr_let_flatten_body)

theorem processDelayBindings_go_refines :
    ∀ (binds acc : List (VarId × Expr × Bool)) (body : Expr) (ch : Bool),
      MIRCtxRefines (.Let (acc.reverse ++ binds) body)
        (.Let (processDelayBindings.go binds acc body ch).1
          (processDelayBindings.go binds acc body ch).2.1)
  | [], acc, body, ch => by
    rw [processDelayBindings.go, List.append_nil]; exact mirCtxRefines_refl _
  | (v, rhs, er) :: rest, acc, body, ch => by
    have skip : ∀ ch',
        MIRCtxRefines (.Let (acc.reverse ++ (v, rhs, er) :: rest) body)
          (.Let (processDelayBindings.go rest ((v, rhs, er) :: acc) body ch').1
            (processDelayBindings.go rest ((v, rhs, er) :: acc) body ch').2.1) := by
      intro ch'
      have ih := processDelayBindings_go_refines rest ((v, rhs, er) :: acc) body ch'
      rwa [List.reverse_cons, List.append_assoc, List.singleton_append] at ih
    cases rhs with
    | Delay inner =>
      rw [processDelayBindings.go]
      split
      · rename_i hguard
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hguard
        obtain ⟨⟨⟨_, _⟩, hv⟩, hav'⟩ := hguard
        have ih := processDelayBindings_go_refines
          (rest.map fun (w, r, er₂) => (w, replaceForceVar v inner r, er₂))
          ((v, .Delay inner, er) :: acc) (replaceForceVar v inner body) true
        rw [List.reverse_cons, List.append_assoc, List.singleton_append] at ih
        refine mirCtxRefines_trans ?_ ih
        refine mirCtxRefines_trans
          (mirCtxRefines_of_lowerEq fun env => (lowerTotalExpr_let_flatten_body _ _ _ env).symm) ?_
        refine mirCtxRefines_trans ?_
          (mirCtxRefines_of_lowerEq fun env => lowerTotalExpr_let_flatten_body _ _ _ env)
        exact mirCtxRefines_let_body (mirCtxRefines_delay_let v inner er rest body hv hav')
      · exact skip ch
    | Var _ | Lit _ | Builtin _ | Error | Lam _ _ | Fix _ _ | App _ _ | Force _
    | Constr _ _ | Case _ _ | Let _ _ =>
      rw [processDelayBindings.go]
      · exact skip ch
      · intro _ h; cases h
  termination_by binds => binds.length

theorem processDelayBindings_refines (binds : List (VarId × Expr × Bool)) (body : Expr) :
    MIRCtxRefines (.Let binds body)
      (.Let (processDelayBindings binds body).1 (processDelayBindings binds body).2.1) := by
  simpa using processDelayBindings_go_refines binds [] body false

mutual
  theorem forceDelayCore_refines : ∀ e : Expr, MIRCtxRefines e (forceDelayCore e).1
    | .Var _ | .Lit _ | .Builtin _ | .Error => by
      rw [forceDelayCore]; exact mirCtxRefines_refl _
    | .Lam x body => by
      rw [forceDelayCore]; exact mirCtxRefines_lam (forceDelayCore_refines body)
    | .Fix f (.Lam x b) => by
      rw [forceDelayCore, forceDelayCore]
      exact mirCtxRefines_fix_lam (forceDelayCore_refines b)
    | .Fix f (.Var _) | .Fix f (.Lit _) | .Fix f (.Builtin _) | .Fix f .Error
    | .Fix f (.Fix _ _) | .Fix f (.App _ _) | .Fix f (.Force _) | .Fix f (.Delay _)
    | .Fix f (.Constr _ _) | .Fix f (.Case _ _) | .Fix f (.Let _ _) =>
      mirCtxRefines_fix_nonlam_lhs (fun _ _ h => by cases h)
    | .App fn arg => by
      rw [forceDelayCore]
      exact mirCtxRefines_app (forceDelayCore_refines fn) (forceDelayCore_refines arg)
    | .Delay inner => by
      rw [forceDelayCore]; exact mirCtxRefines_delay (forceDelayCore_refines inner)
    | .Force inner => by
      have ih := mirCtxRefines_force (forceDelayCore_refines inner)
      rw [forceDelayCore]
      split
      · rename_i e heq
        rw [heq] at ih
        exact mirCtxRefines_trans ih (mirCtxRefines_force_delay e)
      · exact ih
    | .Constr tag args => by
      rw [forceDelayCore]
      cases args with
      | nil => rw [forceDelayList]; exact mirCtxRefines_refl _
      | cons e rest =>
        rw [forceDelayList]
        exact mirCtxRefines_constr (forceDelayCore_refines e) (forceDelayList_refines rest)
    | .Case scrut alts => by
      rw [forceDelayCore]
      exact mirCtxRefines_case (forceDelayCore_refines scrut) (forceDelayList_refines alts)
    | .Let binds body => by
      rw [forceDelayCore]
      exact mirCtxRefines_trans
        (mirCtxRefines_let_binds_congr binds (forceDelayBinds binds).1 body
          (forceDelayBinds_refines binds))
        (mirCtxRefines_trans (mirCtxRefines_let_body (forceDelayCore_refines body))
          (processDelayBindings_refines _ _))
  termination_by e => sizeOf e
  decreasing_by all_goals simp_wf <;> omega

  theorem forceDelayList_refines : ∀ es : List Expr,
      ListRel MIRCtxRefines es (forceDelayList es).1
    | [] => by rw [forceDelayList]; exact trivial
    | e :: rest => by
      rw [forceDelayList]
      exact ⟨forceDelayCore_refines e, forceDelayList_refines rest⟩
  termination_by es => sizeOf es

  theorem forceDelayBinds_refines : ∀ binds : List (VarId × Expr × Bool),
      ListRel (fun b₁ b₂ => b₁.1 = b₂.1 ∧ b₁.2.2 = b₂.2.2 ∧ MIRCtxRefines b₁.2.1 b₂.2.1)
        binds (forceDelayBinds binds).1
    | [] => by rw [forceDelayBinds]; exact trivial
    | (v, rhs, er) :: rest => by
      rw [forceDelayBinds]
      exact ⟨⟨rfl, rfl, forceDelayCore_refines rhs⟩, forceDelayBinds_refines rest⟩
  termination_by binds => sizeOf binds
end

/-- Force/delay cancellation refines its input, for every MIR expression. -/
theorem forceDelay_refines (e : Expr) : MIRCtxRefines e (forceDelay e).1 :=
  mirCtxRefines_trans (Moist.Verified.MIR.Hygiene.uniqueOptimizationBinders_refines e)
    (forceDelayCore_refines _)

end Pass

end Moist.Verified.ForceDelaySoundness
