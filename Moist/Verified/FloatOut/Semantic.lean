import Moist.Verified.MIR.Hoist
import Moist.Verified.InlineSoundness.Totality

variable [sv : Moist.CEK.SemVariant]

/-! # Floating a total `let` out of a non-strict position

A `let` whose right-hand side is a `TotalTerm` (it returns a value in every
environment that defines its variables) may be evaluated earlier, before a
lambda is formed or before a case selects an alternative:

* `openRefines_floatLam`: `λ. (λ. b) ↑p ⊑ (λ. λ. swap b) p`
* `openRefines_floatCase`: `case s (… (λ. r) p …) ⊑ (λ. case ↑s (… r …)) p`

In both proofs the target evaluates `p` once to a value `w`. Where the source
later evaluates `p` (or its shift), the target is replayed through a virtual
state that evaluates `p` again: by determinism it returns the same `w`, so the
virtual state runs into the real target state (`obsRefinesK_of_prefix_right`).
-/

namespace Moist.Verified.FloatOut

open Moist.CEK
open Moist.Plutus.Term (Term)
open Moist.Verified (closedAt closedAtList renameTerm renameTermList shiftRename liftRename)
open Moist.Verified.Equivalence (ListRel ObsRefinesK steps steps_trans steps_halt steps_error
  obsRefinesK_of_steps_left obsRefinesK_of_steps_right obsRefinesK_zero_ret
  obsRefinesK_of_step_ret constToTagAndFields_fields_vcon Reaches)
open Moist.Verified.Contextual.SoundnessRefines (EnvRefinesK ValueRefinesK StackRefK OpenRefines
  valueRefinesK_mono stackRefK_mono obsRefinesK_error applyArgFrames_stackRefK
  listRel_refl_vcon_refines)
open Moist.Verified.FundamentalRefines (ftlr renameRefines renameRefinesR renameRefinesR_shift1
  Is0Preserving RenameEnvRefR envRefinesK_to_renameEnvRef_shift
  envRefinesK_to_renameEnvRefR_shift is0preserving_shiftRename)
open Moist.Verified.MIR (envRefinesK_mono envRefinesK_extend stackRefK_funV_top_aug)
open Moist.Verified.InlineSoundness.Totality (TotalTerm)
open Moist.Verified.InlineSoundness.StrictOcc (halt_on_all_stacks)

/-! ## Generic helpers -/

/-- A refinement into a state transfers to every state it runs into. -/
theorem obsRefinesK_of_prefix_right {k n : Nat} {s₁ s₂ s₂' : State}
    (h_steps : steps n s₂ = s₂') (h : ObsRefinesK k s₁ s₂) : ObsRefinesK k s₁ s₂' := by
  have reach : ∀ t, (t = .error ∨ ∃ v, t = .halt v) → Reaches s₂ t → Reaches s₂' t := by
    intro t ht ⟨q, hq⟩
    by_cases hqn : q ≤ n
    · refine ⟨0, ?_⟩
      have hn : steps n s₂ = t := by
        rw [show n = q + (n - q) by omega, steps_trans, hq]
        rcases ht with rfl | ⟨v, rfl⟩
        · exact steps_error _
        · exact steps_halt _ _
      rw [← h_steps, hn]; rfl
    · refine ⟨q - n, ?_⟩
      rw [← h_steps, ← steps_trans, show n + (q - n) = q by omega, hq]
  exact ⟨fun v hv => let ⟨v', hv'⟩ := h.1 v hv; ⟨v', reach _ (.inr ⟨v', rfl⟩) hv'⟩,
    fun m hm he => reach _ (.inl rfl) (h.2 m hm he)⟩

/-- A total term returns the same value on every stack. -/
theorem total_returns {d k : Nat} {P : Term} (hP : TotalTerm P) (hc : closedAt d P = true)
    {ρ₁ ρ₂ : CekEnv} (henv : EnvRefinesK k d ρ₁ ρ₂) :
    ∃ w, ∀ π, ∃ m, steps m (.compute π ρ₂ P) = .ret π w := by
  obtain ⟨w, hw⟩ := hP.halts d ρ₂ hc fun n hn hnd =>
    let ⟨_, v₂, _, h, _⟩ := henv n hn hnd; ⟨v₂, h⟩
  exact ⟨w, halt_on_all_stacks hw⟩

/-- Closures over the same body in related environments are related. -/
theorem valueRefinesK_lam {k d : Nat} {b : Term} (hb : closedAt (d + 1) b = true)
    {ρ₁ ρ₂ : CekEnv} (henv : EnvRefinesK k d ρ₁ ρ₂) :
    ValueRefinesK k (.VLam b ρ₁) (.VLam b ρ₂) := by
  cases k with
  | zero => simp only [ValueRefinesK]
  | succ k =>
    simp only [ValueRefinesK]
    intro j hj a₁ a₂ ha i hi π₁ π₂ hπ
    exact ftlr (d + 1) b hb j j (Nat.le_refl _) _ _
      (envRefinesK_extend (envRefinesK_mono (by omega) henv) ha) i hi π₁ π₂ hπ

/-! ## Swapping the two innermost binders -/

/-- Exchange de Bruijn positions 1 and 2. -/
def swapRename : Nat → Nat
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | n + 3 => n + 3

omit sv in
theorem is0preserving_swapRename : Is0Preserving swapRename := by
  refine ⟨rfl, fun n hn => ?_⟩
  match n, hn with
  | 1, _ => decide
  | 2, _ => decide
  | n + 3, _ => simp [swapRename]

theorem renameEnvRefR_swap {k d : Nat} {ρ₁ ρ₂ : CekEnv} {a₁ a₂ u₁ u₂ : CekValue}
    (henv : EnvRefinesK k d ρ₁ ρ₂) (ha : ValueRefinesK k a₁ a₂) (hu : ValueRefinesK k u₁ u₂) :
    RenameEnvRefR swapRename k (d + 2) ((ρ₁.extend a₁).extend u₁)
      ((ρ₂.extend u₂).extend a₂) := by
  intro n hn hnd
  match n, hn with
  | 1, _ => exact hu
  | 2, _ => exact ha
  | m + 3, _ =>
    obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := henv (m + 1) (by omega) (by omega)
    show match ((ρ₁.extend a₁).extend u₁).lookup (m + 3),
        ((ρ₂.extend u₂).extend a₂).lookup (m + 3) with
      | some v₁, some v₂ => ValueRefinesK k v₁ v₂
      | none, none => True
      | _, _ => False
    rw [show ((ρ₁.extend a₁).extend u₁).lookup (m + 3) = ρ₁.lookup (m + 1) from rfl,
      show ((ρ₂.extend u₂).extend a₂).lookup (m + 3) = ρ₂.lookup (m + 1) from rfl, h₁, h₂]
    exact hv

/-! ## Floating out of a lambda -/

/-- **Lambda float**: `λ. (λ. b) ↑p ⊑ (λ. λ. swap b) p` for a total `p`. -/
theorem openRefines_floatLam {d : Nat} {P B : Term} (hP : TotalTerm P)
    (hPc : closedAt d P = true) (hB : closedAt (d + 2) B = true) :
    OpenRefines d (.Lam 0 (.Apply (.Lam 0 B) (renameTerm (shiftRename 1) P)))
      (.Apply (.Lam 0 (.Lam 0 (renameTerm swapRename B))) P) := by
  intro k j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  obtain ⟨w, hw⟩ := total_returns hP hPc henv
  obtain ⟨m, hm⟩ := hw (.funV (.VLam (.Lam 0 (renameTerm swapRename B)) ρ₂) :: π₂)
  have hR : steps (3 + m + 2)
      (.compute π₂ ρ₂ (.Apply (.Lam 0 (.Lam 0 (renameTerm swapRename B))) P)) =
      .ret π₂ (.VLam (renameTerm swapRename B) (ρ₂.extend w)) := by
    rw [steps_trans, steps_trans]
    show steps 2 (steps m (.compute
      (.funV (.VLam (.Lam 0 (renameTerm swapRename B)) ρ₂) :: π₂) ρ₂ P)) = _
    rw [hm]; rfl
  refine obsRefinesK_of_steps_left (n := 1) rfl (obsRefinesK_of_steps_right hR ?_)
  refine hπ i (Nat.le_refl _) _ _ ?_
  cases i with
  | zero => simp only [ValueRefinesK]
  | succ n =>
    simp only [ValueRefinesK]
    intro j' hj' a₁ a₂ ha i' hi' π₁' π₂' hπ'
    obtain ⟨m', hm'⟩ := hw (.funV (.VLam (.Lam 0 (renameTerm swapRename B)) ρ₂) ::
      .applyArg a₂ :: π₂')
    have hV : steps (m' + 3) (.compute (.funV (.VLam (.Lam 0 (renameTerm swapRename B)) ρ₂) ::
        .applyArg a₂ :: π₂') ρ₂ P) =
        .compute π₂' ((ρ₂.extend w).extend a₂) (renameTerm swapRename B) := by
      rw [steps_trans, hm']; rfl
    refine obsRefinesK_of_steps_left (n := 3) rfl (obsRefinesK_of_prefix_right hV ?_)
    have henv' : EnvRefinesK i' d ρ₁ ρ₂ := envRefinesK_mono (by omega) henv
    refine renameRefines (shiftRename 1) (is0preserving_shiftRename (Nat.le_refl 1)) d P hPc
      i' i' (Nat.le_refl _) _ _ (envRefinesK_to_renameEnvRef_shift henv') i' (Nat.le_refl _)
      _ _ ?_
    intro j'' hj'' u₁ u₂ hu
    refine obsRefinesK_of_steps_left (n := 1) rfl (obsRefinesK_of_steps_right (n := 3) rfl ?_)
    exact renameRefinesR swapRename is0preserving_swapRename (d + 2) B hB j'' j''
      (Nat.le_refl _) _ _
      (renameEnvRefR_swap (envRefinesK_mono (by omega) henv)
        (valueRefinesK_mono (by omega) _ _ ha) hu)
      j'' (Nat.le_refl _) _ _ (stackRefK_mono hj'' hπ')

/-! ## Floating out of a case alternative -/

omit sv in
theorem listRel_getElem? {R : Term → Term → Prop} :
    ∀ {xs ys : List Term}, ListRel R xs ys →
      xs.length = ys.length ∧
        ∀ (n : Nat) (x y : Term), xs[n]? = some x → ys[n]? = some y → R x y
  | [], [], _ => ⟨rfl, fun n x y hx _ => by simp at hx⟩
  | [], _ :: _, h | _ :: _, [], h => absurd h id
  | x :: xs, y :: ys, ⟨hxy, h⟩ => by
    obtain ⟨hl, hn⟩ := listRel_getElem? h
    refine ⟨by simp [hl], fun n a b ha hb => ?_⟩
    cases n with
    | zero => simp at ha hb; subst ha; subst hb; exact hxy
    | succ n => exact hn n a b (by simpa using ha) (by simpa using hb)

omit sv in
theorem listRel_append {R : Term → Term → Prop} :
    ∀ {xs ys xs' ys' : List Term}, ListRel R xs ys → ListRel R xs' ys' →
      ListRel R (xs ++ xs') (ys ++ ys')
  | [], [], _, _, _, h' => h'
  | [], _ :: _, _, _, h, _ | _ :: _, [], _, _, h, _ => absurd h id
  | _ :: _, _ :: _, _, _, ⟨h, hs⟩, h' => ⟨h, listRel_append hs h'⟩

/-- A case frame on related stacks, given related alternatives. -/
theorem stackRefK_case_of_alts {i : Nat} {alts₁ alts₂ : List Term} {ρ₁ ρ₂ : CekEnv}
    {π₁ π₂ : Stack}
    (halts : ListRel (fun alt₁ alt₂ => ∀ m < i, ∀ fs₁ fs₂, ListRel (ValueRefinesK m) fs₁ fs₂ →
      ObsRefinesK m (.compute (fs₁.map Frame.applyArg ++ π₁) ρ₁ alt₁)
        (.compute (fs₂.map Frame.applyArg ++ π₂) ρ₂ alt₂)) alts₁ alts₂) :
    StackRefK ValueRefinesK i (.caseScrutinee alts₁ ρ₁ :: π₁) (.caseScrutinee alts₂ ρ₂ :: π₂) := by
  obtain ⟨hlen, hget⟩ := listRel_getElem? halts
  intro j hj v₁ v₂ hv
  match j with
  | 0 => exact obsRefinesK_zero_ret
  | m + 1 =>
  have halt : ∀ {n : Nat} {fs₁ fs₂ : List CekValue}, ListRel (ValueRefinesK m) fs₁ fs₂ →
      ObsRefinesK m (match alts₁[n]? with
          | some alt => .compute (fs₁.map Frame.applyArg ++ π₁) ρ₁ alt
          | none => .error)
        (match alts₂[n]? with
          | some alt => .compute (fs₂.map Frame.applyArg ++ π₂) ρ₂ alt
          | none => .error) := by
    intro n fs₁ fs₂ hfs
    cases h₁ : alts₁[n]? with
    | none =>
      have : alts₂[n]? = none := by
        rw [List.getElem?_eq_none_iff] at h₁ ⊢; omega
      rw [this]; exact obsRefinesK_error _
    | some alt₁ =>
      obtain ⟨alt₂, h₂⟩ : ∃ alt₂, alts₂[n]? = some alt₂ := by
        cases h : alts₂[n]? with
        | some a => exact ⟨a, rfl⟩
        | none =>
          rw [List.getElem?_eq_none_iff] at h
          obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp h₁
          omega
      rw [h₂]; exact hget n alt₁ alt₂ h₁ h₂ m (by omega) fs₁ fs₂ hfs
  refine obsRefinesK_of_step_ret ?_
  cases v₁ <;> cases v₂ <;> simp only [ValueRefinesK] at hv <;> try exact obsRefinesK_error _
  case VCon.VCon c _ =>
    subst hv
    have hvcon := constToTagAndFields_fields_vcon c
    simp only [step]
    cases hc : constToTagAndFields c with
    | none => exact obsRefinesK_error _
    | some r =>
      obtain ⟨tag, numCtors, fs⟩ := r
      rw [hc] at hvcon
      simp only [hlen]
      split
      · exact obsRefinesK_error _
      · exact halt (listRel_refl_vcon_refines m fs hvcon)
  case VConstr.VConstr tag fs₁ _ fs₂ =>
    obtain ⟨rfl, hfs⟩ := hv
    simp only [step]
    exact halt hfs

/-- **Case-alternative float**: `case s (… (λ. r) p …) ⊑ (λ. case ↑s (… r …)) p`
    for a total `p`. -/
theorem openRefines_floatCase {d : Nat} {S P R : Term} {pre post : List Term}
    (hP : TotalTerm P) (hPc : closedAt d P = true) (hS : closedAt d S = true)
    (hpre : closedAtList d pre = true) (hpost : closedAtList d post = true)
    (hR : closedAt (d + 1) R = true) :
    OpenRefines d (.Case S (pre ++ .Apply (.Lam 0 R) P :: post))
      (.Apply (.Lam 0 (.Case (renameTerm (shiftRename 1) S)
        (renameTermList (shiftRename 1) pre ++ R :: renameTermList (shiftRename 1) post))) P) := by
  intro k j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  obtain ⟨w, hw⟩ := total_returns hP hPc henv
  let alts₂ := renameTermList (shiftRename 1) pre ++ R :: renameTermList (shiftRename 1) post
  obtain ⟨m, hm⟩ := hw (.funV (.VLam (.Case (renameTerm (shiftRename 1) S) alts₂) ρ₂) :: π₂)
  have hR' : steps (3 + m + 2)
      (.compute π₂ ρ₂ (.Apply (.Lam 0 (.Case (renameTerm (shiftRename 1) S) alts₂)) P)) =
      .compute (.caseScrutinee alts₂ (ρ₂.extend w) :: π₂) (ρ₂.extend w)
        (renameTerm (shiftRename 1) S) := by
    rw [steps_trans, steps_trans]
    show steps 2 (steps m (.compute
      (.funV (.VLam (.Case (renameTerm (shiftRename 1) S) alts₂) ρ₂) :: π₂) ρ₂ P)) = _
    rw [hm]; rfl
  refine obsRefinesK_of_steps_left (n := 1) rfl (obsRefinesK_of_steps_right hR' ?_)
  have henvi : EnvRefinesK i d ρ₁ ρ₂ := envRefinesK_mono hi henv
  refine renameRefinesR_shift1 d S hS i i (Nat.le_refl _) _ _
    (envRefinesK_to_renameEnvRefR_shift henvi) i (Nat.le_refl _) _ _
    (stackRefK_case_of_alts ?_)
  have shifted : ∀ (ts : List Term), closedAtList d ts = true →
      ListRel (fun alt₁ alt₂ => ∀ m < i, ∀ fs₁ fs₂, ListRel (ValueRefinesK m) fs₁ fs₂ →
        ObsRefinesK m (.compute (fs₁.map Frame.applyArg ++ π₁) ρ₁ alt₁)
          (.compute (fs₂.map Frame.applyArg ++ π₂) (ρ₂.extend w) alt₂))
        ts (renameTermList (shiftRename 1) ts) := by
    intro ts hts
    induction ts with
    | nil => trivial
    | cons t ts ih =>
      simp only [closedAtList, Bool.and_eq_true] at hts
      refine ⟨fun m hm fs₁ fs₂ hfs => ?_, ih hts.2⟩
      exact renameRefinesR_shift1 d t hts.1 m m (Nat.le_refl _) ρ₁ (ρ₂.extend w)
        (envRefinesK_to_renameEnvRefR_shift (envRefinesK_mono (by omega) henvi))
        m (Nat.le_refl _) _ _ (applyArgFrames_stackRefK hfs (stackRefK_mono (by omega) hπ))
  refine listRel_append (shifted pre hpre) ⟨?_, shifted post hpost⟩
  intro m' hm' fs₁ fs₂ hfs
  obtain ⟨m'', hm''⟩ := hw (.funV (.VLam R ρ₂) :: (fs₂.map Frame.applyArg ++ π₂))
  have hV : steps (m'' + 1) (.compute (.funV (.VLam R ρ₂) :: (fs₂.map Frame.applyArg ++ π₂))
      ρ₂ P) = .compute (fs₂.map Frame.applyArg ++ π₂) (ρ₂.extend w) R := by
    rw [steps_trans, hm'']; rfl
  have henv' : EnvRefinesK m' d ρ₁ ρ₂ := envRefinesK_mono (by omega) henvi
  refine obsRefinesK_of_steps_left (n := 3) rfl (obsRefinesK_of_prefix_right hV ?_)
  exact ftlr d P hPc m' m' (Nat.le_refl _) _ _ henv' m' (Nat.le_refl _) _ _
    (stackRefK_funV_top_aug (valueRefinesK_lam hR henv')
      (applyArgFrames_stackRefK hfs (stackRefK_mono (by omega) hπ)))

/-! ## Contextual versions -/

open Moist.Verified.Contextual (CtxRefines Context fill ctxRefines_trans ctxRefines_fill
  closedAtList_append)
open Moist.Verified.MIR (ctxRefines_of_openRefines HoistFrame openRefines_hoist IsValueTerm)
open Moist.MIR (fixLamWrapUplc)

omit sv in
private theorem closedAt_shift_inv {k : Nat} {t : Term}
    (h : closedAt (k + 1) (renameTerm (shiftRename 1) t) = true) : closedAt k t = true :=
  Moist.Verified.closedAt_renameTerm_shiftRename_inv t k 1 (Nat.le_refl 1) (by omega) h

omit sv in
private theorem closedAt_shift {k : Nat} {t : Term} (h : closedAt k t = true) :
    closedAt (k + 1) (renameTerm (shiftRename 1) t) = true :=
  Moist.Verified.closedAt_renameTerm_shiftRename t k 1 (Nat.le_refl 1) (by omega) h

omit sv in
private theorem closedAtList_shift {k : Nat} {ts : List Term} (h : closedAtList k ts = true) :
    closedAtList (k + 1) (renameTermList (shiftRename 1) ts) = true :=
  Moist.Verified.closedAtList_renameTermList_shiftRename ts k 1 (Nat.le_refl 1) (by omega) h

omit sv in
theorem closedAt_swap {k : Nat} {t : Term} (h : closedAt (k + 2) t = true) :
    closedAt (k + 2) (renameTerm swapRename t) = true :=
  Moist.Verified.BetaValueRefines.closedAt_rename swapRename t (k + 2) (k + 2) h fun n hn => by
    match n with
    | 0 => simp [swapRename]
    | 1 => simp [swapRename]
    | 2 => simp [swapRename]
    | n + 3 => simp only [swapRename]; omega

theorem ctxRefines_floatLam {d : Nat} {P B : Term} (hP : TotalTerm P)
    (hPc : closedAt d P = true) (hB : closedAt (d + 2) B = true) :
    CtxRefines (.Lam 0 (.Apply (.Lam 0 B) (renameTerm (shiftRename 1) P)))
      (.Apply (.Lam 0 (.Lam 0 (renameTerm swapRename B))) P) := by
  refine ctxRefines_of_openRefines (fun k h => ?_) (openRefines_floatLam hP hPc hB)
  simp only [closedAt, Bool.and_eq_true] at h ⊢
  exact ⟨closedAt_swap h.1, closedAt_shift_inv h.2⟩

theorem ctxRefines_floatCase {d : Nat} {S P R : Term} {pre post : List Term}
    (hP : TotalTerm P) (hPc : closedAt d P = true) (hS : closedAt d S = true)
    (hpre : closedAtList d pre = true) (hpost : closedAtList d post = true)
    (hR : closedAt (d + 1) R = true) :
    CtxRefines (.Case S (pre ++ .Apply (.Lam 0 R) P :: post))
      (.Apply (.Lam 0 (.Case (renameTerm (shiftRename 1) S)
        (renameTermList (shiftRename 1) pre ++ R :: renameTermList (shiftRename 1) post))) P) := by
  refine ctxRefines_of_openRefines (fun k h => ?_)
    (openRefines_floatCase hP hPc hS hpre hpost hR)
  simp only [closedAt, Bool.and_eq_true, closedAtList_append, closedAtList] at h ⊢
  exact ⟨⟨closedAt_shift h.1, closedAtList_shift h.2.1, h.2.2.1.1, closedAtList_shift h.2.2.2⟩,
    h.2.2.1.2⟩

/-! ## Floating out of a recursive lambda

`fixLamWrapUplc` places its body under the self-application binder, the
recursive binder and the parameter. Floating out of it is a chain of three
lambda floats and two strict hoists. -/

private def zComb : Term := .Lam 0 (.Apply (.Var 1) (.Var 1))
private def selfApp : Term := .Lam 0 (.Apply (.Apply (.Var 2) (.Var 2)) (.Var 1))

/-- The renaming that moves position 1 below the three positions above it. -/
def rotRename (B : Term) : Term :=
  renameTerm (liftRename (liftRename swapRename))
    (renameTerm (liftRename swapRename) (renameTerm swapRename B))

omit sv in
private theorem total_shift {P : Term} (hP : TotalTerm P) :
    TotalTerm (renameTerm (shiftRename 1) P) :=
  hP.rename _ fun n hn => by rw [Moist.Verified.shiftRename_ge hn]; omega

private theorem ctxRefines_hoist (F : HoistFrame) {d : Nat} {tr tb : Term} (hF : F.WF d)
    (hr : closedAt d tr = true) (hb : closedAt (d + 1) tb = true) :
    CtxRefines (F.fill (.Apply (.Lam 0 tb) tr)) (.Apply (.Lam 0 (F.shift.fill tb)) tr) :=
  ctxRefines_of_openRefines (fun _ h => F.closedAt_hoist h) (openRefines_hoist F hF hr hb)

theorem ctxRefines_floatFix {d : Nat} {P B : Term} (hP : TotalTerm P)
    (hPc : closedAt d P = true) (hB : closedAt (d + 4) B = true) :
    CtxRefines
      (fixLamWrapUplc (.Apply (.Lam 0 B) (renameTerm (shiftRename 1)
        (renameTerm (shiftRename 1) (renameTerm (shiftRename 1) P)))))
      (.Apply (.Lam 0 (fixLamWrapUplc (rotRename B))) P) := by
  have hQ₂ := closedAt_shift hPc
  have hQ₁ := closedAt_shift hQ₂
  have hT₂ := total_shift hP
  have hT₁ := total_shift hT₂
  -- Float out of the parameter's lambda.
  have h₁ := ctxRefines_fill (ctxRefines_floatLam (d := d + 2) hT₁ hQ₁ hB)
    (.AppRight zComb (.Lam 0 (.AppLeft (.Lam 0 .Hole) selfApp)))
  -- Float out of the recursive binder's lambda.
  have hM : closedAt (d + 1 + 2) (.Lam 0 (renameTerm swapRename B)) = true := by
    simp only [closedAt]; exact closedAt_swap (k := d + 2) hB
  have h₂ := ctxRefines_fill (ctxRefines_floatLam (d := d + 1) hT₂ hQ₂ hM)
    (.AppRight zComb (.Lam 0 (.AppLeft .Hole selfApp)))
  -- Hoist out of the function position of the self application.
  have hN : closedAt (d + 1 + 1)
      (.Lam 0 (renameTerm swapRename (.Lam 0 (renameTerm swapRename B)))) := by
    simp only [closedAt]; exact closedAt_swap (k := d + 1) hM
  have hSA : closedAt (d + 1) selfApp = true := by
    simp only [selfApp, closedAt, decide_eq_true_eq, Bool.and_eq_true]; omega
  have h₃ := ctxRefines_fill (ctxRefines_hoist (.appFun selfApp) hSA hQ₂ hN)
    (.AppRight zComb (.Lam 0 .Hole))
  -- Float out of the self-application binder's lambda.
  have hK : closedAt (d + 2)
      (.Apply (.Lam 0 (renameTerm swapRename (.Lam 0 (renameTerm swapRename B))))
        (renameTerm (shiftRename 1) selfApp)) = true := by
    generalize Term.Lam 0 (renameTerm swapRename (.Lam 0 (renameTerm swapRename B))) = N at hN ⊢
    simp only [closedAt, Bool.and_eq_true]
    exact ⟨hN, closedAt_shift hSA⟩
  have h₄ := ctxRefines_fill (ctxRefines_floatLam (d := d) hP hPc hK) (.AppRight zComb .Hole)
  -- Hoist out of the argument position of the outer self application.
  have hZ : IsValueTerm d zComb := by
    simp only [IsValueTerm, zComb, closedAt, decide_eq_true_eq, Bool.and_eq_true]; omega
  have hL := closedAt_swap (k := d) hK
  have h₅ := ctxRefines_hoist (.appArg zComb) hZ hPc (tb := .Lam 0 _)
    (by simp only [closedAt]; exact hL)
  exact ctxRefines_trans h₁ (ctxRefines_trans h₂ (ctxRefines_trans h₃
    (ctxRefines_trans h₄ h₅)))

end Moist.Verified.FloatOut
