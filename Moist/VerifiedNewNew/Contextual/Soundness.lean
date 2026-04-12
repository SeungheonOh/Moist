import Moist.VerifiedNewNew.Contextual.Subst

/-! # Open-context CtxEq soundness via the `term_obsEq` semantic bridge

Phase 4 / 5 of the Path A plan (`Contextual-PathA-Plan.md`).

## Approach (refactored 2026-04-12 after blocker B1)

Rather than bridging the syntactic `Subst` family in `Subst.lean` to the
semantic biorthogonal family in `Equivalence.lean` (which deadlocked at the
mixed-state problem in B1), this file proves a single big theorem
`term_obsEq` that takes:

  * a *semantic* env relation (`AtLeastEnvEqK k`)
  * a *semantic* stack relation (`StackRelK ValueEqK k`)
  * a *syntactic* term relation (`TermSubst t₁ t₂`)

and concludes `ObsEqK k` of the corresponding compute states.

The proof is by strong induction on the step index `k`. At each level the
proof dispatches on the `TermSubst` constructor; at the `swap`/`swapInv`
constructors `OpenEq 0 t₁ t₂` is invoked directly (since `EnvEqK k 0` is
vacuous and we already have `StackRelK ValueEqK k`). At every other
constructor we step the CEK once and recurse with the IH at level `k-1`,
sometimes constructing `StackRelK` for newly-pushed frames inline.

The soundness theorem then composes `term_obsEq` with `fill_termSubst` and
the trivial fact that the empty stack is `StackRelK`-related to itself and
the empty env is `AtLeastEnvEqK`-related to itself.

**Why this avoids B1.** The blocker required converting `ValueSubst →
ValueEqK` at the `vLam` constructor, which produced mixed states (env with
both `EnvSubst` tail and `ValueEqK` extensions). Here we never construct
`ValueSubst` for runtime values — every value carried through the proof is
already in `ValueEqK` form, and the only `ValueSubst` that ever appears is
the trivially-`ValueEqK`-empty one for the initial state's empty env.
-/

namespace Moist.VerifiedNewNew.Contextual.Soundness

open Moist.CEK
open Moist.Plutus.Term
open Moist.VerifiedNewNew.Equivalence
open Moist.VerifiedNewNew.Contextual
open Moist.VerifiedNewNew.Contextual.Subst

--------------------------------------------------------------------------------
-- 1. AtLeastEnvEqK — a `EnvEqK k ∞` style env relation
--------------------------------------------------------------------------------

/-- Pointwise `ValueEqK` at every position of two CEK environments. Equivalent
    to `∀ d, EnvEqK k d ρ_l ρ_r`, but more direct. -/
def AtLeastEnvEqK (k : Nat) (ρ_l ρ_r : CekEnv) : Prop :=
  ∀ n, n > 0 →
    match ρ_l.lookup n, ρ_r.lookup n with
    | some v_l, some v_r => ValueEqK k v_l v_r
    | none, none => True
    | _, _ => False

/-- The empty env is `AtLeastEnvEqK`-related to itself at any level. -/
theorem atLeastEnvEqK_nil (k : Nat) : AtLeastEnvEqK k .nil .nil := by
  intro n _
  have : (CekEnv.nil).lookup n = none := by cases n <;> rfl
  rw [this]
  trivial

/-- `AtLeastEnvEqK` restricts to `EnvEqK k d` for any `d`. -/
theorem atLeastEnvEqK_to_envEqK {k d : Nat} {ρ_l ρ_r : CekEnv}
    (h : AtLeastEnvEqK k ρ_l ρ_r) : EnvEqK k d ρ_l ρ_r :=
  fun n hn _ => h n hn

/-- Monotonicity in the step index. -/
theorem atLeastEnvEqK_mono {j k : Nat} (hjk : j ≤ k) {ρ_l ρ_r : CekEnv}
    (h : AtLeastEnvEqK k ρ_l ρ_r) : AtLeastEnvEqK j ρ_l ρ_r := by
  intro n hn
  have := h n hn
  cases h_l : ρ_l.lookup n <;> cases h_r : ρ_r.lookup n <;>
    simp [h_l, h_r] at this ⊢
  exact valueEqK_mono hjk _ _ this

/-- Extending two `AtLeastEnvEqK`-related envs by two `ValueEqK`-related
    values gives an `AtLeastEnvEqK`-related extended pair. -/
theorem atLeastEnvEqK_extend {k : Nat} {ρ_l ρ_r : CekEnv} {v_l v_r : CekValue}
    (hρ : AtLeastEnvEqK k ρ_l ρ_r) (hv : ValueEqK k v_l v_r) :
    AtLeastEnvEqK k (ρ_l.extend v_l) (ρ_r.extend v_r) := by
  intro n hn
  match n, hn with
  | 1, _ => simp [CekEnv.extend, CekEnv.lookup]; exact hv
  | n + 2, _ =>
    have := hρ (n + 1) (by omega)
    simp [CekEnv.extend, CekEnv.lookup]
    exact this

--------------------------------------------------------------------------------
-- 2. ObsEqK helpers
--------------------------------------------------------------------------------

/-- For any value `v` and any `n`, `steps n (.halt v) = .halt v`. -/
theorem steps_halt (n : Nat) (v : CekValue) : steps n (.halt v) = .halt v := by
  induction n with
  | zero => rfl
  | succ m ih => show steps m (step (.halt v)) = .halt v; simp [step]; exact ih

/-- ObsEqK at any level for two halt states (always true; both terminate at
    step 0). -/
theorem obsEqK_halt (k : Nat) (v_l v_r : CekValue) :
    ObsEqK k (.halt v_l) (.halt v_r) := by
  refine ⟨?_, ?_⟩
  · rintro v ⟨n, _, hs⟩
    rw [steps_halt n v_l] at hs
    cases hs
    exact ⟨v_r, 0, rfl⟩
  · rintro v ⟨n, _, hs⟩
    rw [steps_halt n v_r] at hs
    cases hs
    exact ⟨v_l, 0, rfl⟩

--------------------------------------------------------------------------------
-- 3. The `term_obsEq` semantic bridge (Phase 4 main theorem)
--
-- Strong induction on the step index `k`. Inside, dispatch on the
-- `TermSubst` constructor:
--
--   * `swap`/`swapInv`: instantiate `OpenEq 0 t₁ t₂` directly.
--   * `varRefl`/`constRefl`/`builtinRefl`/`errorRefl`/`lam`/`delay`:
--     compute → ret in one step; fold the new value back through the
--     stack predicate at level k-1.
--   * `apply`/`force`/`constr`/`case`: compute → compute in one step;
--     recurse with `term_obsEq` at level k-1, having constructed a fresh
--     `StackRelK` for the new top frame inline.
--
-- The `lam`/`delay` cases additionally need to construct `ValueEqK k-1` of
-- a `VLam`/`VDelay` closure. The application property in `ValueEqK` is
-- proved inline using `term_obsEq` at level (k-2 or smaller).
--------------------------------------------------------------------------------

/-- `AtLeastEnvEqK` is symmetric: pointwise `ValueEqK` is symmetric. -/
theorem atLeastEnvEqK_symm {k : Nat} {ρ_l ρ_r : CekEnv}
    (h : AtLeastEnvEqK k ρ_l ρ_r) : AtLeastEnvEqK k ρ_r ρ_l := by
  intro n hn
  have h' := h n hn
  cases hl : ρ_l.lookup n <;> cases hr : ρ_r.lookup n <;>
    simp [hl, hr] at h' ⊢
  exact valueEqK_symm k _ _ h'

/-- `constrField` frame `StackRelK` constructor. Mirrors `constrField_stackRelK`
    from `Equivalence.lean` but parameterized over a `term_obsEq` IH that handles
    the head term evaluation at smaller levels. -/
private theorem constrField_helper {t₁ t₂ : Term} (_h_open : OpenEq 0 t₁ t₂)
    {tag : Nat} {k : Nat}
    (ih_te : ∀ i ≤ k, ∀ {ρ_l ρ_r : CekEnv} {π_l π_r : Stack} {tm_l tm_r : Term},
      AtLeastEnvEqK i ρ_l ρ_r → StackRelK ValueEqK i π_l π_r →
      TermSubst t₁ t₂ tm_l tm_r →
      ObsEqK i (.compute π_l ρ_l tm_l) (.compute π_r ρ_r tm_r)) :
    ∀ {ms_l ms_r : List Term}, TermListSubst t₁ t₂ ms_l ms_r →
    ∀ {j : Nat}, j ≤ k →
      ∀ {done_l done_r : List CekValue} {ρ_l ρ_r : CekEnv} {π_l π_r : Stack},
        AtLeastEnvEqK j ρ_l ρ_r →
        ListRel (ValueEqK j) done_l done_r →
        StackRelK ValueEqK j π_l π_r →
        StackRelK ValueEqK j (.constrField tag done_l ms_l ρ_l :: π_l)
                              (.constrField tag done_r ms_r ρ_r :: π_r) := by
  intro ms_l ms_r hms
  induction ms_l generalizing ms_r with
  | nil =>
    cases hms with
    | nil =>
      intro j _ done_l done_r ρ_l ρ_r π_l π_r _ h_done hπ
      intro j' hj'_j v_l v_r hv
      match j' with
      | 0 =>
        exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | n + 1 =>
        apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
        simp only [step]
        have hrev : ListRel (ValueEqK n) ((v_l :: done_l).reverse) ((v_r :: done_r).reverse) := by
          simp only [List.reverse_cons]
          exact listRel_append
            (listRel_reverse
              (listRel_mono (fun a b h => valueEqK_mono (by omega) a b h) h_done))
            ⟨valueEqK_mono (by omega) v_l v_r hv, trivial⟩
        have hval : ValueEqK (n + 1)
            (.VConstr tag ((v_l :: done_l).reverse))
            (.VConstr tag ((v_r :: done_r).reverse)) := by
          cases n with
          | zero => simp only [ValueEqK]; exact ⟨trivial, hrev⟩
          | succ _ => simp only [ValueEqK]; exact ⟨trivial, hrev⟩
        exact obsEqK_mono (by omega) (hπ (n + 1) (by omega) _ _ hval)
  | cons m ms_l_rest ih_ms =>
    cases hms with
    | cons hm hms_rest =>
      intro j hj_k done_l done_r ρ_l ρ_r π_l π_r hρ h_done hπ
      intro j' hj'_j v_l v_r hv
      match j' with
      | 0 =>
        exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | n + 1 =>
        apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
        simp only [step]
        apply ih_te n (by omega) (atLeastEnvEqK_mono (by omega) hρ) ?_ hm
        exact ih_ms hms_rest (by omega : n ≤ k) (atLeastEnvEqK_mono (by omega) hρ)
          (show ListRel (ValueEqK n) (v_l :: done_l) (v_r :: done_r) from
            ⟨valueEqK_mono (by omega) v_l v_r hv,
             listRel_mono (fun a b h => valueEqK_mono (by omega) a b h) h_done⟩)
          (stackRelK_mono (by omega) hπ)

theorem term_obsEq {t₁ t₂ : Term} (h_open : OpenEq 0 t₁ t₂) :
    ∀ (k : Nat) (i : Nat), i ≤ k →
      ∀ {ρ_l ρ_r : CekEnv} {π_l π_r : Stack} {tm_l tm_r : Term},
        AtLeastEnvEqK i ρ_l ρ_r →
        StackRelK ValueEqK i π_l π_r →
        TermSubst t₁ t₂ tm_l tm_r →
        ObsEqK i (.compute π_l ρ_l tm_l) (.compute π_r ρ_r tm_r) := by
  intro k
  induction k with
  | zero =>
    intro i hi
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    intros _ _ _ _ _ _ _ _ _
    exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
  | succ m ih =>
    intro i hi
    by_cases hi_m : i ≤ m
    · -- Use ih at level i ≤ m
      exact ih i hi_m
    · -- i = m + 1
      have hi_eq : i = m + 1 := by omega
      subst hi_eq
      intro hρ hπ htm
      rename_i ρ_l ρ_r π_l π_r tm_l tm_r
      cases htm with
      | swap =>
        -- Apply OpenEq 0 t₁ t₂ directly. EnvEqK k 0 is vacuous.
        exact h_open (m+1) (m+1) (Nat.le_refl _) ρ_l ρ_r
          (atLeastEnvEqK_to_envEqK hρ) (m+1) (Nat.le_refl _) π_l π_r hπ
      | swapInv =>
        -- Apply OpenEq 0 t₁ t₂ with sides swapped, then symmetrize.
        apply obsEqK_symm
        exact h_open (m+1) (m+1) (Nat.le_refl _) ρ_r ρ_l
          (atLeastEnvEqK_to_envEqK (atLeastEnvEqK_symm hρ))
          (m+1) (Nat.le_refl _) π_r π_l
          (stackRelK_symm_of (fun k' => valueEqK_symm k') hπ)
      | varRefl n =>
        -- compute → ret with lookup result, or error
        apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
        simp only [step]
        by_cases hn : n = 0
        · subst hn
          have hl : ρ_l.lookup 0 = none := by cases ρ_l <;> rfl
          have hr : ρ_r.lookup 0 = none := by cases ρ_r <;> rfl
          rw [hl, hr]
          exact obsEqK_error _
        · have hpos : n > 0 := Nat.pos_of_ne_zero hn
          have hlk := hρ n hpos
          cases hl : ρ_l.lookup n with
          | none =>
            cases hr : ρ_r.lookup n with
            | none => exact obsEqK_error _
            | some _ => rw [hl, hr] at hlk; exact absurd hlk id
          | some v_l =>
            cases hr : ρ_r.lookup n with
            | none => rw [hl, hr] at hlk; exact absurd hlk id
            | some v_r =>
              rw [hl, hr] at hlk
              -- hlk : ValueEqK (m+1) v_l v_r
              exact hπ m (Nat.le_succ m) v_l v_r
                (valueEqK_mono (Nat.le_succ m) v_l v_r hlk)
      | constRefl c =>
        -- compute → ret π (VCon c.fst); both sides identical
        apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
        simp only [step]
        obtain ⟨k, _⟩ := c
        -- Use stack relation at j = m with ValueEqK m of VCon (reflexive).
        apply hπ m (Nat.le_succ m) (.VCon k) (.VCon k)
        cases m with
        | zero => simp only [ValueEqK]
        | succ _ => simp only [ValueEqK]
      | builtinRefl b =>
        apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
        simp only [step]
        apply hπ m (Nat.le_succ m) (.VBuiltin b [] (expectedArgs b)) _
        cases m with
        | zero => simp only [ValueEqK]
        | succ _ => simp only [ValueEqK, ListRel]; exact ⟨trivial, trivial, trivial⟩
      | errorRefl =>
        apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
        simp only [step]
        exact obsEqK_error _
      | lam hb =>
        -- compute (.Lam x b) → ret π (VLam b ρ)
        apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
        simp only [step]
        -- Stack relation at j = m gives ObsEqK m of .ret if values are ValueEqK m.
        apply hπ m (Nat.le_succ m)
        -- Build ValueEqK m (VLam b_l ρ_l) (VLam b_r ρ_r) using ih at smaller levels.
        match m with
        | 0 => simp only [ValueEqK]
        | m' + 1 =>
          -- ValueEqK (m'+1) of VLam: application property at level m'
          simp only [ValueEqK]
          intro j hj_m' arg_l arg_r harg i hi π_l_app π_r_app hπ_app
          -- Need: ObsEqK i (compute π_l_app (ρ_l.extend arg_l) b_l)
          --                (compute π_r_app (ρ_r.extend arg_r) b_r)
          apply ih i (by omega)
          · -- AtLeastEnvEqK i (ρ_l.extend arg_l) (ρ_r.extend arg_r)
            apply atLeastEnvEqK_extend
            · exact atLeastEnvEqK_mono (by omega) hρ
            · exact valueEqK_mono hi _ _ harg
          · -- StackRelK ValueEqK i π_l_app π_r_app — exactly hπ_app
            exact hπ_app
          · exact hb
      | apply hf ha =>
        -- compute (Apply f a) → compute (.arg a ρ :: π) ρ f
        apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
        simp only [step]
        apply ih m (Nat.le_refl m) (atLeastEnvEqK_mono (Nat.le_succ m) hρ) ?_ hf
        -- StackRelK m of (.arg a_l ρ_l :: π_l) (.arg a_r ρ_r :: π_r)
        intro j hj_m vf_l vf_r hvf
        match j with
        | 0 =>
          exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
        | j' + 1 =>
          apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
          simp only [step]
          -- Stepped to compute (.funV vf :: π) ρ a. Use ih at level j'.
          apply ih j' (by omega) (atLeastEnvEqK_mono (by omega) hρ) ?_ ha
          -- StackRelK j' of (.funV vf_l :: π_l) (.funV vf_r :: π_r)
          intro j'' hj''_j' w_l w_r hw
          match j'' with
          | 0 =>
            exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
          | j''' + 1 =>
            apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
            -- Dispatch on vf
            match vf_l, vf_r with
            | .VCon _, .VCon _ => simp only [step]; exact obsEqK_error _
            | .VDelay _ _, .VDelay _ _ => simp only [step]; exact obsEqK_error _
            | .VConstr _ _, .VConstr _ _ => simp only [step]; exact obsEqK_error _
            | .VLam b_lv ρ_lv, .VLam b_rv ρ_rv =>
              -- ValueEqK (j'+1) of VLam vf gives application property at j'.
              simp only [step]
              simp only [ValueEqK] at hvf
              -- hvf : ∀ j_app ≤ j', ∀ args ValueEqK j_app, ∀ i ≤ j_app, ∀ π_app "stack pred i" →
              --       ObsEqK i (compute π_app (ρ_lv.extend arg₁) b_lv) (compute π_app (ρ_rv.extend arg₂) b_rv)
              -- Apply with arg = w, j_app = j''', i = j'''
              apply hvf j''' (by omega) w_l w_r
                (valueEqK_mono (Nat.le_succ _) _ _ hw)
                j''' (Nat.le_refl _) π_l π_r
              intro i' hi' x_l x_r hx
              exact hπ i' (by omega) x_l x_r hx
            | .VBuiltin b args_l ea, .VBuiltin _ args_r _ =>
              simp only [ValueEqK] at hvf
              obtain ⟨rfl, rfl, hargs_rel⟩ := hvf
              simp only [step]
              split
              · split
                · -- some rest
                  rename_i rest _
                  have hval : ValueEqK (j''' + 1)
                      (.VBuiltin b (w_l :: args_l) rest)
                      (.VBuiltin b (w_r :: args_r) rest) := by
                    simp only [ValueEqK]
                    refine ⟨trivial, trivial, ?_⟩
                    simp only [ListRel]
                    exact ⟨valueEqK_mono (by omega) w_l w_r hw,
                           listRel_mono (fun a b h => valueEqK_mono (by omega) a b h) hargs_rel⟩
                  exact obsEqK_mono (by omega : j''' ≤ j''' + 1)
                    (hπ (j''' + 1) (by omega) _ _ hval)
                · -- none: fully saturated
                  exact evalBuiltin_compat
                    (by simp only [ListRel]
                        exact ⟨valueEqK_mono (by omega) w_l w_r hw,
                               listRel_mono (fun a b h => valueEqK_mono (by omega) a b h) hargs_rel⟩)
                    (stackRelK_mono (by omega) hπ)
              · exact obsEqK_error _
            | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
            | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
            | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
            | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
            | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
            | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
            | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
            | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
            | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueEqK] at hvf
      | force he =>
        -- compute (.Force e) → compute (.force :: π) ρ e
        apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
        simp only [step]
        -- Apply ih m at the new compute state. Need StackRelK m of (.force :: π).
        apply ih m (Nat.le_refl m) (atLeastEnvEqK_mono (Nat.le_succ m) hρ) ?_ he
        -- Build StackRelK m of (.force :: π_l) (.force :: π_r) inline.
        intro j hj_m vf_l vf_r hvf
        match j with
        | 0 =>
          exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
        | j' + 1 =>
          apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
          -- Dispatch on vf_l/vf_r via ValueEqK (j'+1)
          match vf_l, vf_r with
          | .VCon _, .VCon _ => simp only [step]; exact obsEqK_error _
          | .VLam _ _, .VLam _ _ => simp only [step]; exact obsEqK_error _
          | .VConstr _ _, .VConstr _ _ => simp only [step]; exact obsEqK_error _
          | .VDelay b_lv ρ_lv, .VDelay b_rv ρ_rv =>
            -- ValueEqK (j'+1) of VDelay gives the application property at j'.
            simp only [step, ValueEqK] at hvf ⊢
            -- hvf : ∀ j'' ≤ j', ∀ i ≤ j'', ∀ π₁ π₂, "stack pred i" → ObsEqK i (compute π₁ ρ_lv b_lv) (compute π₂ ρ_rv b_rv)
            apply hvf j' (Nat.le_refl _) j' (Nat.le_refl _) π_l π_r
            -- Need: ∀ i' ≤ j', ∀ w_l w_r, ValueEqK i' w_l w_r → ObsEqK i' (.ret π_l w_l) (.ret π_r w_r)
            intro i' hi' w_l w_r hw
            exact hπ i' (by omega) w_l w_r hw
          | .VBuiltin b args_l ea, .VBuiltin _ args_r _ =>
            simp only [ValueEqK] at hvf
            obtain ⟨rfl, rfl, hargs_rel⟩ := hvf
            simp only [step]
            split
            · split
              · -- some rest
                rename_i rest _
                have hval : ValueEqK (j' + 1)
                    (.VBuiltin b args_l rest) (.VBuiltin b args_r rest) := by
                  simp only [ValueEqK]; exact ⟨trivial, trivial, hargs_rel⟩
                exact obsEqK_mono (by omega : j' ≤ j' + 1)
                  (hπ (j' + 1) (by omega) _ _ hval)
              · -- none: fully saturated
                exact evalBuiltin_compat hargs_rel (stackRelK_mono (by omega) hπ)
            · exact obsEqK_error _
          | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
          | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
          | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
          | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
          | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
          | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
          | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
          | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
          | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueEqK] at hvf
      | delay hb =>
        -- compute (.Delay b) → ret π (VDelay b ρ)
        apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
        simp only [step]
        apply hπ m (Nat.le_succ m)
        -- ValueEqK m (VDelay b_l ρ_l) (VDelay b_r ρ_r)
        match m with
        | 0 => simp only [ValueEqK]
        | m' + 1 =>
          simp only [ValueEqK]
          intro j hj_m' i hi π_l_app π_r_app hπ_app
          apply ih i (by omega)
          · exact atLeastEnvEqK_mono (by omega) hρ
          · exact hπ_app
          · exact hb
      | constr hms =>
        cases hms with
        | nil =>
          -- compute (Constr tag []) → ret π (VConstr tag [])
          apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
          simp only [step]
          apply hπ m (Nat.le_succ m) (.VConstr _ []) (.VConstr _ [])
          cases m with
          | zero => simp only [ValueEqK]
          | succ _ => simp only [ValueEqK, ListRel]; exact ⟨trivial, trivial⟩
        | cons hm hms_rest =>
          -- compute (Constr tag (m :: ms_rest))
          -- → compute (.constrField tag [] ms_rest ρ :: π) ρ m
          apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
          simp only [step]
          apply ih m (Nat.le_refl m) (atLeastEnvEqK_mono (Nat.le_succ m) hρ) ?_ hm
          -- Need StackRelK m of new constrField stack via constrField_helper
          exact constrField_helper h_open ih hms_rest (Nat.le_refl m)
            (atLeastEnvEqK_mono (Nat.le_succ m) hρ)
            (show ListRel (ValueEqK m) [] [] from trivial)
            (stackRelK_mono (Nat.le_succ m) hπ)
      | case hs has =>
        rename_i as_l as_r
        -- compute (.Case scrut alts) → compute (.caseScrutinee alts ρ :: π) ρ scrut
        apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
        simp only [step]
        apply ih m (Nat.le_refl m) (atLeastEnvEqK_mono (Nat.le_succ m) hρ) ?_ hs
        -- StackRelK m of (.caseScrutinee as_l ρ_l :: π_l) (.caseScrutinee as_r ρ_r :: π_r)
        intro j hj_m vf_l vf_r hvf
        match j with
        | 0 =>
          exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
        | j' + 1 =>
          apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
          match vf_l, vf_r with
          | .VConstr tag_l fields_l, .VConstr tag_r fields_r =>
            simp only [step]
            simp only [ValueEqK] at hvf
            obtain ⟨h_tag, h_fields⟩ := hvf
            subst h_tag
            -- Look up alts at tag_l on both sides
            have h_lk := termListSubst_getElem? has tag_l
            cases h_lk with
            | inl h =>
              obtain ⟨hl, hr⟩ := h
              rw [hl, hr]
              exact obsEqK_error _
            | inr h =>
              obtain ⟨alt_l, alt_r, hl, hr, halt⟩ := h
              rw [hl, hr]
              -- compute (fields.map .applyArg ++ π) ρ alt
              -- Use ih at level j'
              apply ih j' (by omega) (atLeastEnvEqK_mono (by omega) hρ) ?_ halt
              -- StackRelK j' of (fields_l.map .applyArg ++ π_l) ...
              exact applyArgFrames_stackRelK h_fields
                (stackRelK_mono (by omega) hπ)
          | .VCon c_l, .VCon c_r =>
            -- ValueEqK forces c_l = c_r
            simp only [ValueEqK] at hvf
            subst hvf
            simp only [step]
            -- Both sides do constToTagAndFields c_l
            have hlen := termListSubst_length_eq has
            -- Align alts_r.length with alts_l.length
            rw [show as_r.length = as_l.length from hlen.symm]
            cases h_const : constToTagAndFields c_l with
            | none => exact obsEqK_error _
            | some triple =>
              obtain ⟨tag, numCtors, fields⟩ := triple
              dsimp only []
              by_cases hcond : (decide (numCtors > 0) && decide (as_l.length > numCtors)) = true
              · rw [if_pos hcond, if_pos hcond]
                exact obsEqK_error _
              · rw [if_neg hcond, if_neg hcond]
                have h_lk := termListSubst_getElem? has tag
                cases h_lk with
                | inl h =>
                  obtain ⟨hl, hr⟩ := h
                  rw [hl, hr]
                  exact obsEqK_error _
                | inr h =>
                  obtain ⟨alt_l, alt_r, hl, hr, halt⟩ := h
                  rw [hl, hr]
                  apply ih j' (by omega) (atLeastEnvEqK_mono (by omega) hρ) ?_ halt
                  -- fields are reflexive VCon — use listRel_refl_vcon
                  have hfields_vcon := constToTagAndFields_fields_vcon c_l
                  rw [h_const] at hfields_vcon
                  exact applyArgFrames_stackRelK
                    (listRel_refl_vcon j' fields hfields_vcon)
                    (stackRelK_mono (by omega) hπ)
          | .VLam _ _, .VLam _ _ => simp only [step]; exact obsEqK_error _
          | .VDelay _ _, .VDelay _ _ => simp only [step]; exact obsEqK_error _
          | .VBuiltin _ _ _, .VBuiltin _ _ _ => simp only [step]; exact obsEqK_error _
          | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
          | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
          | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
          | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
          | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
          | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
          | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
          | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
          | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueEqK] at hvf

--------------------------------------------------------------------------------
-- 4. Soundness theorem (Phase 5)
--------------------------------------------------------------------------------

/-- Empty stack is `StackRelK`-related to itself at any level. The `.ret []`
    state is non-halt itself and steps to `.halt`, so the obsEqK condition is
    discharged via `obsEqK_of_step` + `obsEqK_halt`. -/
theorem stackRelK_nil (k : Nat) : StackRelK ValueEqK k [] [] := by
  intro j _ v_l v_r _
  cases j with
  | zero =>
    exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
  | succ j' =>
    apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
    simp only [step]
    exact obsEqK_halt j' v_l v_r

/-- The open-context soundness theorem: `OpenEq 0 t₁ t₂` implies that for any
    context `C`, the empty-state CEK runs of `fill C t₁` and `fill C t₂` are
    observationally equivalent. -/
theorem soundness {t₁ t₂ : Term} (h_open : OpenEq 0 t₁ t₂) :
    ∀ (C : Context),
      ObsEq (.compute [] .nil (fill C t₁)) (.compute [] .nil (fill C t₂)) := by
  intro C
  refine ⟨?_, ?_⟩
  · rintro ⟨v, n, hs⟩
    -- Use term_obsEq at level n with the initial state.
    have h_obs : ObsEqK n (.compute [] .nil (fill C t₁)) (.compute [] .nil (fill C t₂)) :=
      term_obsEq h_open n n (Nat.le_refl _)
        (atLeastEnvEqK_nil n) (stackRelK_nil n) (fill_termSubst C t₁ t₂)
    exact h_obs.1 v ⟨n, Nat.le_refl _, hs⟩
  · rintro ⟨v, n, hs⟩
    have h_obs : ObsEqK n (.compute [] .nil (fill C t₁)) (.compute [] .nil (fill C t₂)) :=
      term_obsEq h_open n n (Nat.le_refl _)
        (atLeastEnvEqK_nil n) (stackRelK_nil n) (fill_termSubst C t₁ t₂)
    exact h_obs.2 v ⟨n, Nat.le_refl _, hs⟩

end Moist.VerifiedNewNew.Contextual.Soundness
