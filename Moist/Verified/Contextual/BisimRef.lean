import Moist.Verified.Contextual

/-! # Locality bisimulation for CEK closed-term evaluation

Core *locality* lemma: two CEK states with the same term, same stack
structure, and environments that agree (modulo `LocalValue`) on a
common prefix of length `k` — running a term that is `closedAt k` —
produce identical halt/error observations.

The relation is **one-term, two-envs**: the terms/bodies/alts/todos
are syntactically the same on both sides, and environments differ only
on positions past the current closedness bound. Used by
`SoundnessRefines.lean` to downward-weaken `OpenRefines d` via env
padding (see "per-side padding" in the module's public interface).

All machinery is re-implemented within `Moist.Verified.*` — no
imports from `Moist.Verified.Bisim` — so we stay on
`Equivalence.steps` throughout.
-/

namespace Moist.Verified.Contextual.BisimRef

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified (closedAt closedAtList)
open Moist.Verified.Equivalence
open Moist.Verified.Contextual

--------------------------------------------------------------------------------
-- 1. Mutual bisim relations
--
-- `LocalEnv k ρ₁ ρ₂` — envs agree on first `k` positions *modulo LocalValue*.
-- `LocalValue`       — structurally identical runtime values, captured envs
--                      may differ but are `LocalEnv`-related at closure depth.
-- `LocalValueList`   — element-wise `LocalValue`.
-- `LocalState`       — machine states with same term/same stack structure.
-- `LocalStack`       — element-wise `LocalFrame`.
-- `LocalFrame`       — frames with same syntactic content, env-parts
--                      `LocalEnv`-related.
--------------------------------------------------------------------------------

mutual
inductive LocalState : State → State → Prop
  | compute : ∀ {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv} {t : Term} {k : Nat},
      LocalEnv k ρ₁ ρ₂ → closedAt k t = true → LocalStack π₁ π₂ →
      LocalState (.compute π₁ ρ₁ t) (.compute π₂ ρ₂ t)
  | ret : ∀ {π₁ π₂ : Stack} {v₁ v₂ : CekValue},
      LocalValue v₁ v₂ → LocalStack π₁ π₂ →
      LocalState (.ret π₁ v₁) (.ret π₂ v₂)
  | halt : ∀ {v₁ v₂ : CekValue}, LocalValue v₁ v₂ → LocalState (.halt v₁) (.halt v₂)
  | error : LocalState .error .error

inductive LocalEnv : Nat → CekEnv → CekEnv → Prop
  | zero : ∀ {ρ₁ ρ₂ : CekEnv}, LocalEnv 0 ρ₁ ρ₂
  | succ : ∀ {k : Nat} {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue},
      LocalEnv k ρ₁ ρ₂ →
      k + 1 ≤ ρ₁.length → k + 1 ≤ ρ₂.length →
      ρ₁.lookup (k + 1) = some v₁ → ρ₂.lookup (k + 1) = some v₂ →
      LocalValue v₁ v₂ →
      LocalEnv (k + 1) ρ₁ ρ₂

inductive LocalValue : CekValue → CekValue → Prop
  | vcon : ∀ (c : Const), LocalValue (.VCon c) (.VCon c)
  | vlam : ∀ {body : Term} {ρ₁ ρ₂ : CekEnv} {k : Nat},
      LocalEnv k ρ₁ ρ₂ → k ≤ ρ₁.length → k ≤ ρ₂.length →
      closedAt (k + 1) body = true →
      LocalValue (.VLam body ρ₁) (.VLam body ρ₂)
  | vdelay : ∀ {body : Term} {ρ₁ ρ₂ : CekEnv} {k : Nat},
      LocalEnv k ρ₁ ρ₂ → k ≤ ρ₁.length → k ≤ ρ₂.length →
      closedAt k body = true →
      LocalValue (.VDelay body ρ₁) (.VDelay body ρ₂)
  | vconstr : ∀ (tag : Nat) {fs₁ fs₂ : List CekValue},
      LocalValueList fs₁ fs₂ →
      LocalValue (.VConstr tag fs₁) (.VConstr tag fs₂)
  | vbuiltin : ∀ (b : BuiltinFun) (ea : ExpectedArgs) {args₁ args₂ : List CekValue},
      LocalValueList args₁ args₂ →
      LocalValue (.VBuiltin b args₁ ea) (.VBuiltin b args₂ ea)

inductive LocalValueList : List CekValue → List CekValue → Prop
  | nil : LocalValueList [] []
  | cons : ∀ {v₁ v₂ : CekValue} {vs₁ vs₂ : List CekValue},
      LocalValue v₁ v₂ → LocalValueList vs₁ vs₂ →
      LocalValueList (v₁ :: vs₁) (v₂ :: vs₂)

inductive LocalStack : Stack → Stack → Prop
  | nil : LocalStack [] []
  | cons : ∀ {f₁ f₂ : Frame} {π₁ π₂ : Stack},
      LocalFrame f₁ f₂ → LocalStack π₁ π₂ →
      LocalStack (f₁ :: π₁) (f₂ :: π₂)

inductive LocalFrame : Frame → Frame → Prop
  | force : LocalFrame .force .force
  | arg : ∀ {t : Term} {ρ₁ ρ₂ : CekEnv} {k : Nat},
      LocalEnv k ρ₁ ρ₂ → k ≤ ρ₁.length → k ≤ ρ₂.length →
      closedAt k t = true →
      LocalFrame (.arg t ρ₁) (.arg t ρ₂)
  | funV : ∀ {v₁ v₂ : CekValue},
      LocalValue v₁ v₂ → LocalFrame (.funV v₁) (.funV v₂)
  | applyArg : ∀ {v₁ v₂ : CekValue},
      LocalValue v₁ v₂ → LocalFrame (.applyArg v₁) (.applyArg v₂)
  | constrField : ∀ (tag : Nat) {done₁ done₂ : List CekValue}
      {todo : List Term} {ρ₁ ρ₂ : CekEnv} {k : Nat},
      LocalValueList done₁ done₂ →
      LocalEnv k ρ₁ ρ₂ → k ≤ ρ₁.length → k ≤ ρ₂.length →
      closedAtList k todo = true →
      LocalFrame (.constrField tag done₁ todo ρ₁) (.constrField tag done₂ todo ρ₂)
  | caseScrutinee : ∀ {alts : List Term} {ρ₁ ρ₂ : CekEnv} {k : Nat},
      LocalEnv k ρ₁ ρ₂ → k ≤ ρ₁.length → k ≤ ρ₂.length →
      closedAtList k alts = true →
      LocalFrame (.caseScrutinee alts ρ₁) (.caseScrutinee alts ρ₂)
end

--------------------------------------------------------------------------------
-- 2. LocalEnv helpers
--------------------------------------------------------------------------------

/-- `LocalEnv` always holds vacuously at depth 0 regardless of env lengths. -/
theorem localEnv_zero (ρ₁ ρ₂ : CekEnv) : LocalEnv 0 ρ₁ ρ₂ := LocalEnv.zero

/-- `LocalEnv` is preserved under narrowing to a smaller `k`.
    `induction` can't be used on `LocalEnv` (mutual), so we induct on `k`. -/
theorem localEnv_narrow : ∀ (k : Nat) {k' : Nat} {ρ₁ ρ₂ : CekEnv},
    LocalEnv k ρ₁ ρ₂ → k' ≤ k → LocalEnv k' ρ₁ ρ₂ := by
  intro k
  induction k with
  | zero =>
    intro k' _ _ _ hle
    have : k' = 0 := Nat.le_zero.mp hle
    subst this
    exact LocalEnv.zero
  | succ n ih =>
    intro k' _ _ h hle
    by_cases h_eq : k' = n + 1
    · subst h_eq; exact h
    · cases h with
      | succ h_rest _ _ _ _ _ =>
        exact ih h_rest (by omega)

/-- Lookups within `LocalEnv k` return matching `LocalValue`-related pairs. -/
theorem localEnv_lookup : ∀ (k : Nat) {ρ₁ ρ₂ : CekEnv},
    LocalEnv k ρ₁ ρ₂ → ∀ {n : Nat}, 0 < n → n ≤ k →
      ∃ v₁ v₂, ρ₁.lookup n = some v₁ ∧ ρ₂.lookup n = some v₂ ∧ LocalValue v₁ v₂ := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ hle; omega
  | succ n ih =>
    intro _ _ h m hm hle
    cases h with
    | succ h_rest _ _ hl₁ hl₂ h_v =>
      by_cases h_eq : m = n + 1
      · subst h_eq; exact ⟨_, _, hl₁, hl₂, h_v⟩
      · exact ih h_rest hm (by omega)

/-- `LocalEnv k` implies the envs have at least length `k`. -/
theorem localEnv_length : ∀ (k : Nat) {ρ₁ ρ₂ : CekEnv},
    LocalEnv k ρ₁ ρ₂ → k ≤ ρ₁.length ∧ k ≤ ρ₂.length := by
  intro k
  cases k with
  | zero => intro _ _ _; exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | succ n =>
    intro _ _ h
    cases h with
    | succ _ hlen₁ hlen₂ _ _ _ => exact ⟨hlen₁, hlen₂⟩

/-- Extending two `LocalEnv k`-related envs with `LocalValue`-related values
    preserves `LocalEnv (k + 1)` on the new envs. This is the key
    propagation step used in `step_preserves` for VLam application. -/
theorem localEnv_extend : ∀ (k : Nat) {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue},
    LocalEnv k ρ₁ ρ₂ → LocalValue v₁ v₂ →
    LocalEnv (k + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) := by
  intro k
  induction k with
  | zero =>
    intro ρ₁ ρ₂ _ _ _ h_v
    refine LocalEnv.succ LocalEnv.zero ?_ ?_ ?_ ?_ h_v
    · simp [CekEnv.extend, CekEnv.length]
    · simp [CekEnv.extend, CekEnv.length]
    · simp [CekEnv.extend, CekEnv.lookup]
    · simp [CekEnv.extend, CekEnv.lookup]
  | succ n ih =>
    intro ρ₁ ρ₂ _ _ h h_v
    cases h with
    | succ h_rest _ _ hl₁ hl₂ h_inner =>
      have ih' := ih h_rest h_v
      refine LocalEnv.succ ih' ?_ ?_ ?_ ?_ h_inner
      · simp [CekEnv.extend, CekEnv.length]; omega
      · simp [CekEnv.extend, CekEnv.length]; omega
      · show (CekEnv.cons _ ρ₁).lookup (n + 1 + 1) = _
        exact hl₁
      · show (CekEnv.cons _ ρ₂).lookup (n + 1 + 1) = _
        exact hl₂

--------------------------------------------------------------------------------
-- 3. Symmetry of the mutual bisim relations
--
-- `LocalValue`, `LocalEnv`, and `LocalValueList` are symmetric. Proved by
-- mutual structural recursion on the inductive proofs.
--------------------------------------------------------------------------------

mutual
def localValue_symm : ∀ {v₁ v₂ : CekValue}, LocalValue v₁ v₂ → LocalValue v₂ v₁
  | _, _, .vcon c => .vcon c
  | _, _, .vlam (k := _) hρ hl₁ hl₂ hb =>
      .vlam (localEnv_symm hρ) hl₂ hl₁ hb
  | _, _, .vdelay (k := _) hρ hl₁ hl₂ hb =>
      .vdelay (localEnv_symm hρ) hl₂ hl₁ hb
  | _, _, .vconstr tag h_fs => .vconstr tag (localValueList_symm h_fs)
  | _, _, .vbuiltin b ea h_args => .vbuiltin b ea (localValueList_symm h_args)

def localEnv_symm : ∀ {k : Nat} {ρ₁ ρ₂ : CekEnv}, LocalEnv k ρ₁ ρ₂ → LocalEnv k ρ₂ ρ₁
  | 0, _, _, .zero => .zero
  | _ + 1, _, _, .succ hr hl₁ hl₂ hk₁ hk₂ hv =>
      .succ (localEnv_symm hr) hl₂ hl₁ hk₂ hk₁ (localValue_symm hv)

def localValueList_symm : ∀ {xs ys : List CekValue},
    LocalValueList xs ys → LocalValueList ys xs
  | [], _, .nil => .nil
  | _ :: _, _, .cons hv hr => .cons (localValue_symm hv) (localValueList_symm hr)
end

/-- `LocalFrame` is symmetric. Non-mutual: only calls into the core mutual
    symms (`localEnv_symm`, `localValue_symm`, `localValueList_symm`). -/
def localFrame_symm : ∀ {f₁ f₂ : Frame}, LocalFrame f₁ f₂ → LocalFrame f₂ f₁
  | _, _, .force => .force
  | _, _, .arg hρ hl₁ hl₂ hc => .arg (localEnv_symm hρ) hl₂ hl₁ hc
  | _, _, .funV hv => .funV (localValue_symm hv)
  | _, _, .applyArg hv => .applyArg (localValue_symm hv)
  | _, _, .constrField tag h_done hρ hl₁ hl₂ h_todo =>
      .constrField tag (localValueList_symm h_done) (localEnv_symm hρ) hl₂ hl₁ h_todo
  | _, _, .caseScrutinee hρ hl₁ hl₂ h_alts =>
      .caseScrutinee (localEnv_symm hρ) hl₂ hl₁ h_alts

/-- `LocalStack` is symmetric. Structural recursion on stack length. -/
def localStack_symm : ∀ {π₁ π₂ : Stack}, LocalStack π₁ π₂ → LocalStack π₂ π₁
  | [], _, .nil => .nil
  | _ :: _, _, .cons hf hr => .cons (localFrame_symm hf) (localStack_symm hr)

/-- `LocalState` is symmetric. Dispatches on the constructor and uses the
    other symmetries. -/
def localState_symm : ∀ {s₁ s₂ : State}, LocalState s₁ s₂ → LocalState s₂ s₁
  | _, _, .compute hρ hc hπ => .compute (localEnv_symm hρ) hc (localStack_symm hπ)
  | _, _, .ret hv hπ => .ret (localValue_symm hv) (localStack_symm hπ)
  | _, _, .halt hv => .halt (localValue_symm hv)
  | _, _, .error => .error

--------------------------------------------------------------------------------
-- 4. LocalValueList structural helpers
--------------------------------------------------------------------------------

/-- Concatenating two pairs of `LocalValueList`-related lists preserves the
    relation. Structural induction on the first list. -/
theorem localValueList_append : ∀ (xs₁ : List CekValue) {xs₂ ys₁ ys₂ : List CekValue},
    LocalValueList xs₁ xs₂ → LocalValueList ys₁ ys₂ →
    LocalValueList (xs₁ ++ ys₁) (xs₂ ++ ys₂)
  | [], _, _, _, hxs, hys => by
    cases hxs
    exact hys
  | _ :: rest, _, _, _, hxs, hys => by
    cases hxs with
    | cons hv hrest =>
      exact LocalValueList.cons hv (localValueList_append rest hrest hys)

/-- `List.reverse` preserves `LocalValueList`. -/
theorem localValueList_reverse : ∀ (xs₁ : List CekValue) {xs₂ : List CekValue},
    LocalValueList xs₁ xs₂ → LocalValueList xs₁.reverse xs₂.reverse
  | [], _, hxs => by cases hxs; exact LocalValueList.nil
  | x :: rest, _, hxs => by
    cases hxs with
    | cons hv hrest =>
      simp only [List.reverse_cons]
      exact localValueList_append _ (localValueList_reverse rest hrest)
              (LocalValueList.cons hv LocalValueList.nil)

/-- Mapping `Frame.applyArg` over a `LocalValueList`-related pair produces
    a `LocalStack`-related pair; prepending to a `LocalStack`-related stack
    preserves the relation. -/
theorem localValueList_to_applyArg_stack : ∀ (fs₁ : List CekValue)
    {fs₂ : List CekValue} {π₁ π₂ : Stack},
    LocalValueList fs₁ fs₂ → LocalStack π₁ π₂ →
    LocalStack (fs₁.map Frame.applyArg ++ π₁) (fs₂.map Frame.applyArg ++ π₂)
  | [], _, _, _, hfs, hπ => by
    cases hfs
    exact hπ
  | _ :: rest, _, _, _, hfs, hπ => by
    cases hfs with
    | cons hv hrest =>
      exact LocalStack.cons (LocalFrame.applyArg hv)
              (localValueList_to_applyArg_stack rest hrest hπ)

/-- `closedAtList d alts → alts[n]? = some alt → closedAt d alt`.
    Extraction of per-element closedness from list closedness. -/
theorem closedAtList_get : ∀ (d : Nat) (alts : List Term) (n : Nat) (alt : Term),
    Moist.Verified.closedAtList d alts = true →
    alts[n]? = some alt →
    Moist.Verified.closedAt d alt = true
  | _, [], _, _, _, h => by simp at h
  | d, a :: rest, 0, _, h_cl, h_get => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h_get
    subst h_get
    simp only [Moist.Verified.closedAtList, Bool.and_eq_true] at h_cl
    exact h_cl.1
  | d, _ :: rest, n + 1, alt, h_cl, h_get => by
    simp only [List.getElem?_cons_succ] at h_get
    simp only [Moist.Verified.closedAtList, Bool.and_eq_true] at h_cl
    exact closedAtList_get d rest n alt h_cl.2 h_get

--------------------------------------------------------------------------------
-- 5. Inversion/destructuring lemmas for LocalValueList and LocalValue
--------------------------------------------------------------------------------

theorem localValueList_nil_inv : ∀ {xs : List CekValue},
    LocalValueList [] xs → xs = []
  | _, h => by cases h; rfl

theorem localValueList_cons_inv : ∀ {v : CekValue} {vs xs : List CekValue},
    LocalValueList (v :: vs) xs →
    ∃ w ws, xs = w :: ws ∧ LocalValue v w ∧ LocalValueList vs ws
  | _, _, _, h => by cases h with | cons hv hr => exact ⟨_, _, rfl, hv, hr⟩

theorem localValue_vcon_inv : ∀ {c : Const} {v : CekValue},
    LocalValue (.VCon c) v → v = .VCon c
  | _, _, h => by cases h; rfl

/-- `LocalValueList` has the same length on both sides. -/
theorem localValueList_length_eq : ∀ {xs₁ xs₂ : List CekValue},
    LocalValueList xs₁ xs₂ → xs₁.length = xs₂.length
  | [], _, h => by cases h; rfl
  | _ :: rest, _, h => by
    cases h with
    | cons _ hr => simp [localValueList_length_eq hr]

--------------------------------------------------------------------------------
-- 6. extractConsts equality under LocalValueList
--------------------------------------------------------------------------------

/-- Two `LocalValueList`-related argument lists produce equal `extractConsts`
    outputs: `LocalValue.vcon` forces literal equality of constants, and
    any non-VCon element makes extraction fail uniformly on both sides. -/
theorem localValueList_extractConsts : ∀ (args₁ : List CekValue) {args₂ : List CekValue},
    LocalValueList args₁ args₂ → extractConsts args₁ = extractConsts args₂ := by
  intro args₁
  induction args₁ with
  | nil =>
    intro args₂ h
    cases h
    rfl
  | cons v rest ih =>
    intro args₂ h
    obtain ⟨w, rest₂, heq, hv, hrest⟩ := localValueList_cons_inv h
    subst heq
    cases hv with
    | vcon c =>
      simp only [extractConsts]
      rw [ih hrest]
    | vlam _ _ _ _ => rfl
    | vdelay _ _ _ _ => rfl
    | vconstr _ _ => rfl
    | vbuiltin _ _ _ => rfl

--------------------------------------------------------------------------------
-- 7. evalBuiltinPassThrough bisim under LocalValueList
--------------------------------------------------------------------------------

/-- Forward-direction-only version of the pass-through bisim. Proved by
    brute-force case analysis on each pass-through builtin's arg shape. -/
theorem localValueList_evalBuiltinPassThrough_some : ∀ (b : BuiltinFun) {args₁ args₂ : List CekValue},
    LocalValueList args₁ args₂ →
    ∀ v₁, evalBuiltinPassThrough b args₁ = some v₁ →
      ∃ v₂, evalBuiltinPassThrough b args₂ = some v₂ ∧ LocalValue v₁ v₂ := by
  intro b args₁ args₂ h v₁ hv₁
  by_cases hb : b = .IfThenElse ∨ b = .ChooseUnit ∨ b = .Trace ∨
                b = .ChooseData ∨ b = .ChooseList ∨ b = .MkCons
  · rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    -- ==================== IfThenElse: [e, t, .VCon (.Bool cond)] ====================
    · match args₁, h, hv₁ with
      | [e₁, t₁, .VCon (.Bool cond)], h_args, hv₁ =>
        obtain ⟨e₂, _, he₁, h_e, hr⟩ := localValueList_cons_inv h_args
        obtain ⟨t₂, _, he₂, h_t, hr'⟩ := localValueList_cons_inv hr
        obtain ⟨w, _, he₃, h_w, hrn⟩ := localValueList_cons_inv hr'
        have hnil := localValueList_nil_inv hrn
        subst hnil he₁ he₂ he₃
        cases localValue_vcon_inv h_w
        simp only [evalBuiltinPassThrough, Option.some.injEq] at hv₁
        subst hv₁
        refine ⟨if cond then t₂ else e₂, rfl, ?_⟩
        by_cases hc : cond
        · subst hc; exact h_t
        · simp only [hc]; exact h_e
      | [], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.Integer _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.ByteString _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.String _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon .Unit], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.ConstList _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.ConstDataList _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.ConstPairDataList _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.Pair _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.PairData _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.Data _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.ConstArray _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon .Bls12_381_G1_element], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon .Bls12_381_G2_element], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon .Bls12_381_MlResult], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VDelay _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VLam _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VConstr _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VBuiltin _ _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | _ :: _ :: _ :: _ :: _, _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
    -- ==================== ChooseUnit: [r, .VCon .Unit] ====================
    · match args₁, h, hv₁ with
      | [r₁, .VCon .Unit], h_args, hv₁ =>
        obtain ⟨r₂, _, he₁, h_r, hr⟩ := localValueList_cons_inv h_args
        obtain ⟨w, _, he₂, h_w, hrn⟩ := localValueList_cons_inv hr
        have hnil := localValueList_nil_inv hrn
        subst hnil he₁ he₂
        cases localValue_vcon_inv h_w
        simp only [evalBuiltinPassThrough, Option.some.injEq] at hv₁
        subst hv₁
        exact ⟨r₂, rfl, h_r⟩
      | [], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.Integer _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.ByteString _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.String _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.Bool _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.ConstList _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.ConstDataList _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.ConstPairDataList _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.Pair _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.PairData _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.Data _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.ConstArray _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon .Bls12_381_G1_element], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon .Bls12_381_G2_element], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon .Bls12_381_MlResult], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VDelay _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VLam _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VConstr _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VBuiltin _ _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | _ :: _ :: _ :: _, _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
    -- ==================== Trace: [r, .VCon (.String _)] ====================
    · match args₁, h, hv₁ with
      | [r₁, .VCon (.String _)], h_args, hv₁ =>
        obtain ⟨r₂, _, he₁, h_r, hr⟩ := localValueList_cons_inv h_args
        obtain ⟨w, _, he₂, h_w, hrn⟩ := localValueList_cons_inv hr
        have hnil := localValueList_nil_inv hrn
        subst hnil he₁ he₂
        cases localValue_vcon_inv h_w
        simp only [evalBuiltinPassThrough, Option.some.injEq] at hv₁
        subst hv₁
        exact ⟨r₂, rfl, h_r⟩
      | [], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.Integer _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.ByteString _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon .Unit], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.Bool _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.ConstList _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.ConstDataList _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.ConstPairDataList _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.Pair _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.PairData _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.Data _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.ConstArray _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon .Bls12_381_G1_element], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon .Bls12_381_G2_element], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon .Bls12_381_MlResult], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VDelay _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VLam _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VConstr _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VBuiltin _ _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | _ :: _ :: _ :: _, _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
    -- ========= ChooseData: [b, i, l, m, c, .VCon (.Data d)] =========
    · match args₁, h, hv₁ with
      | [b₁, i₁, l₁, m₁, cr₁, .VCon (.Data d)], h_args, hv₁ =>
        obtain ⟨b₂, _, he₁, h_b, hr⟩ := localValueList_cons_inv h_args
        obtain ⟨i₂, _, he₂, h_i, hr₂⟩ := localValueList_cons_inv hr
        obtain ⟨l₂, _, he₃, h_l, hr₃⟩ := localValueList_cons_inv hr₂
        obtain ⟨m₂, _, he₄, h_m, hr₄⟩ := localValueList_cons_inv hr₃
        obtain ⟨cr₂, _, he₅, h_cr, hr₅⟩ := localValueList_cons_inv hr₄
        obtain ⟨w, _, he₆, h_w, hrn⟩ := localValueList_cons_inv hr₅
        have hnil := localValueList_nil_inv hrn
        subst hnil he₁ he₂ he₃ he₄ he₅ he₆
        cases localValue_vcon_inv h_w
        simp only [evalBuiltinPassThrough] at hv₁
        cases d with
        | Constr _ _ =>
          simp only [Option.some.injEq] at hv₁; subst hv₁
          exact ⟨cr₂, rfl, h_cr⟩
        | Map _ =>
          simp only [Option.some.injEq] at hv₁; subst hv₁
          exact ⟨m₂, rfl, h_m⟩
        | List _ =>
          simp only [Option.some.injEq] at hv₁; subst hv₁
          exact ⟨l₂, rfl, h_l⟩
        | I _ =>
          simp only [Option.some.injEq] at hv₁; subst hv₁
          exact ⟨i₂, rfl, h_i⟩
        | B _ =>
          simp only [Option.some.injEq] at hv₁; subst hv₁
          exact ⟨b₂, rfl, h_b⟩
      | [], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon (.Integer _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon (.ByteString _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon (.String _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon .Unit], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon (.Bool _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon (.ConstList _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon (.ConstDataList _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon (.ConstPairDataList _)], _, hv₁ =>
          simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon (.Pair _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon (.PairData _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon (.ConstArray _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon .Bls12_381_G1_element], _, hv₁ =>
          simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon .Bls12_381_G2_element], _, hv₁ =>
          simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon .Bls12_381_MlResult], _, hv₁ =>
          simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VDelay _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VLam _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VConstr _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VBuiltin _ _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
    -- ChooseList: [consC, nilC, .VCon (.ConstDataList l)] or [consC, nilC, .VCon (.ConstList l)]
    · match args₁, h, hv₁ with
      | [c₁, n₁, .VCon (.ConstDataList l)], h_args, hv₁ =>
        obtain ⟨c₂, _, he₁, h_c, hr⟩ := localValueList_cons_inv h_args
        obtain ⟨n₂, _, he₂, h_n, hr'⟩ := localValueList_cons_inv hr
        obtain ⟨w, _, he₃, h_w, hrn⟩ := localValueList_cons_inv hr'
        have hnil := localValueList_nil_inv hrn
        subst hnil he₁ he₂ he₃
        cases localValue_vcon_inv h_w
        simp only [evalBuiltinPassThrough, Option.some.injEq] at hv₁
        subst hv₁
        refine ⟨if l.isEmpty then n₂ else c₂, rfl, ?_⟩
        by_cases hl : l.isEmpty
        · simp [hl]; exact h_n
        · simp [hl]; exact h_c
      | [c₁, n₁, .VCon (.ConstList l)], h_args, hv₁ =>
        obtain ⟨c₂, _, he₁, h_c, hr⟩ := localValueList_cons_inv h_args
        obtain ⟨n₂, _, he₂, h_n, hr'⟩ := localValueList_cons_inv hr
        obtain ⟨w, _, he₃, h_w, hrn⟩ := localValueList_cons_inv hr'
        have hnil := localValueList_nil_inv hrn
        subst hnil he₁ he₂ he₃
        cases localValue_vcon_inv h_w
        simp only [evalBuiltinPassThrough, Option.some.injEq] at hv₁
        subst hv₁
        refine ⟨if l.isEmpty then n₂ else c₂, rfl, ?_⟩
        by_cases hl : l.isEmpty
        · simp [hl]; exact h_n
        · simp [hl]; exact h_c
      | [], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.Integer _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.ByteString _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.String _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon .Unit], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.Bool _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.ConstPairDataList _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.Pair _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.PairData _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.Data _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.ConstArray _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon .Bls12_381_G1_element], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon .Bls12_381_G2_element], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon .Bls12_381_MlResult], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VDelay _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VLam _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VConstr _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VBuiltin _ _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | _ :: _ :: _ :: _ :: _, _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
    -- MkCons: [.VCon (.ConstList tail), .VCon elem] → .VCon (.ConstList (elem :: tail))
    · match args₁, h, hv₁ with
      | [.VCon (.ConstList tail), .VCon c], h_args, hv₁ =>
        obtain ⟨w₁, _, he₁, h_w₁, hr⟩ := localValueList_cons_inv h_args
        obtain ⟨w₂, _, he₂, h_w₂, hrn⟩ := localValueList_cons_inv hr
        have hnil := localValueList_nil_inv hrn
        subst hnil he₁ he₂
        cases localValue_vcon_inv h_w₁
        cases localValue_vcon_inv h_w₂
        simp only [evalBuiltinPassThrough, Option.some.injEq] at hv₁
        subst hv₁
        exact ⟨.VCon (.ConstList (c :: tail)), rfl, LocalValue.vcon _⟩
      | [.VCon (.ConstList _), .VDelay _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon (.ConstList _), .VLam _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon (.ConstList _), .VConstr _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon (.ConstList _), .VBuiltin _ _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon (.Integer _), _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon (.ByteString _), _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon (.String _), _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon .Unit, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon (.Bool _), _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon (.ConstDataList _), _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon (.ConstPairDataList _), _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon (.Pair _), _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon (.PairData _), _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon (.Data _), _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon (.ConstArray _), _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon .Bls12_381_G1_element, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon .Bls12_381_G2_element, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon .Bls12_381_MlResult, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VDelay _ _, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VLam _ _, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VConstr _ _, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VBuiltin _ _ _, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | _ :: _ :: _ :: _, _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
  · -- Default case: b is not a pass-through builtin
    exfalso
    have h1 : b ≠ .IfThenElse := fun heq => hb (Or.inl heq)
    have h2 : b ≠ .ChooseUnit := fun heq => hb (Or.inr (Or.inl heq))
    have h3 : b ≠ .Trace := fun heq => hb (Or.inr (Or.inr (Or.inl heq)))
    have h4 : b ≠ .ChooseData := fun heq => hb (Or.inr (Or.inr (Or.inr (Or.inl heq))))
    have h5 : b ≠ .ChooseList :=
      fun heq => hb (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl heq)))))
    have h6 : b ≠ .MkCons :=
      fun heq => hb (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr heq)))))
    have h_none := evalBuiltinPassThrough_none_of_not_passthrough b args₁ ⟨h1, h2, h3, h4, h5, h6⟩
    rw [h_none] at hv₁
    exact Option.noConfusion hv₁

/-- `evalBuiltinPassThrough` is bisimulation-preserving under `LocalValueList`. -/
theorem localValueList_evalBuiltinPassThrough : ∀ (b : BuiltinFun) {args₁ args₂ : List CekValue},
    LocalValueList args₁ args₂ →
    (∀ v₁, evalBuiltinPassThrough b args₁ = some v₁ →
      ∃ v₂, evalBuiltinPassThrough b args₂ = some v₂ ∧ LocalValue v₁ v₂) ∧
    (evalBuiltinPassThrough b args₁ = none ↔ evalBuiltinPassThrough b args₂ = none) := by
  intro b args₁ args₂ h
  refine ⟨localValueList_evalBuiltinPassThrough_some b h, ?_, ?_⟩
  · intro hn
    cases heq : evalBuiltinPassThrough b args₂ with
    | none => rfl
    | some v₂ =>
      exfalso
      obtain ⟨v₁, hv₁, _⟩ :=
        localValueList_evalBuiltinPassThrough_some b (localValueList_symm h) v₂ heq
      rw [hn] at hv₁
      exact Option.noConfusion hv₁
  · intro hn
    cases heq : evalBuiltinPassThrough b args₁ with
    | none => rfl
    | some v₁ =>
      exfalso
      obtain ⟨v₂, hv₂, _⟩ :=
        localValueList_evalBuiltinPassThrough_some b h v₁ heq
      rw [hn] at hv₂
      exact Option.noConfusion hv₂

--------------------------------------------------------------------------------
-- 8. evalBuiltin bisim (combines pass-through and extractConsts paths)
--------------------------------------------------------------------------------

/-- `evalBuiltin` is bisimulation-preserving under `LocalValueList`. Required
    for the builtin-evaluation branches of `step_preserves`. -/
theorem localValueList_evalBuiltin : ∀ {b : BuiltinFun} {args₁ args₂ : List CekValue},
    LocalValueList args₁ args₂ →
    (∀ v₁, evalBuiltin b args₁ = some v₁ →
      ∃ v₂, evalBuiltin b args₂ = some v₂ ∧ LocalValue v₁ v₂) ∧
    (evalBuiltin b args₁ = none ↔ evalBuiltin b args₂ = none) := by
  intro b args₁ args₂ h
  have h_ext : extractConsts args₁ = extractConsts args₂ := localValueList_extractConsts _ h
  obtain ⟨h_pt_some, h_pt_iff⟩ := localValueList_evalBuiltinPassThrough b h
  refine ⟨?_, ?_⟩
  -- ========== SOME direction ==========
  · intro v₁ hv₁
    cases hpt₁ : evalBuiltinPassThrough b args₁ with
    | some v_pt =>
      obtain ⟨v₂, hpt₂, h_rel⟩ := h_pt_some v_pt hpt₁
      refine ⟨v₂, ?_, ?_⟩
      · simp only [evalBuiltin, hpt₂]
      · have heq : v₁ = v_pt := by
          have h1 : evalBuiltin b args₁ = some v_pt := by
            simp only [evalBuiltin, hpt₁]
          rw [hv₁] at h1
          exact Option.some.inj h1
        rw [heq]
        exact h_rel
    | none =>
      have hpt₂ : evalBuiltinPassThrough b args₂ = none := h_pt_iff.mp hpt₁
      cases hec₁ : extractConsts args₁ with
      | none =>
        exfalso
        have : evalBuiltin b args₁ = none := by
          simp only [evalBuiltin, hpt₁, hec₁]
        rw [hv₁] at this
        exact Option.noConfusion this
      | some cs =>
        have hec₂ : extractConsts args₂ = some cs := h_ext ▸ hec₁
        cases hbc : evalBuiltinConst b cs with
        | none =>
          exfalso
          have : evalBuiltin b args₁ = none := by
            simp only [evalBuiltin, hpt₁, hec₁, hbc]
          rw [hv₁] at this
          exact Option.noConfusion this
        | some c =>
          refine ⟨.VCon c, ?_, ?_⟩
          · simp only [evalBuiltin, hpt₂, hec₂, hbc]
          · have heq : v₁ = .VCon c := by
              have h1 : evalBuiltin b args₁ = some (.VCon c) := by
                simp only [evalBuiltin, hpt₁, hec₁, hbc]
              rw [hv₁] at h1
              exact Option.some.inj h1
            rw [heq]
            exact LocalValue.vcon c
  -- ========== NONE ↔ NONE direction ==========
  · constructor
    · intro hn
      cases hpt₁ : evalBuiltinPassThrough b args₁ with
      | some v =>
        exfalso
        have : evalBuiltin b args₁ = some v := by
          simp only [evalBuiltin, hpt₁]
        rw [hn] at this
        exact Option.noConfusion this
      | none =>
        have hpt₂ := h_pt_iff.mp hpt₁
        cases hec₁ : extractConsts args₁ with
        | none =>
          have hec₂ : extractConsts args₂ = none := h_ext ▸ hec₁
          simp only [evalBuiltin, hpt₂, hec₂]
        | some cs =>
          have hec₂ : extractConsts args₂ = some cs := h_ext ▸ hec₁
          cases hbc : evalBuiltinConst b cs with
          | none =>
            simp only [evalBuiltin, hpt₂, hec₂, hbc]
          | some c =>
            exfalso
            have : evalBuiltin b args₁ = some (.VCon c) := by
              simp only [evalBuiltin, hpt₁, hec₁, hbc]
            rw [hn] at this
            exact Option.noConfusion this
    · intro hn
      cases hpt₂ : evalBuiltinPassThrough b args₂ with
      | some v =>
        exfalso
        have : evalBuiltin b args₂ = some v := by
          simp only [evalBuiltin, hpt₂]
        rw [hn] at this
        exact Option.noConfusion this
      | none =>
        have hpt₁ := h_pt_iff.mpr hpt₂
        cases hec₂ : extractConsts args₂ with
        | none =>
          have hec₁ : extractConsts args₁ = none := by rw [h_ext]; exact hec₂
          simp only [evalBuiltin, hpt₁, hec₁]
        | some cs =>
          have hec₁ : extractConsts args₁ = some cs := by rw [h_ext]; exact hec₂
          cases hbc : evalBuiltinConst b cs with
          | none =>
            simp only [evalBuiltin, hpt₁, hec₁, hbc]
          | some c =>
            exfalso
            have : evalBuiltin b args₂ = some (.VCon c) := by
              simp only [evalBuiltin, hpt₂, hec₂, hbc]
            rw [hn] at this
            exact Option.noConfusion this

--------------------------------------------------------------------------------
-- 9. constToTagAndFields field-list is `LocalValueList`-reflexive
--
-- The fields returned by `constToTagAndFields` are always lists of `VCon`
-- values, so `LocalValueList fs fs` holds reflexively via `LocalValue.vcon`.
--------------------------------------------------------------------------------

/-- `constToTagAndFields c = some (tag, numCtors, fs)` implies `fs` is
    `LocalValueList`-reflexive. Case split on `c` exhaustively: in each
    successful case the fields are a literal list of `VCon` values. -/
theorem localValueList_constToTagAndFields_refl :
    ∀ {c : Const} {tag numCtors : Nat} {fs : List CekValue},
      constToTagAndFields c = some (tag, numCtors, fs) → LocalValueList fs fs := by
  intro c tag numCtors fs hc
  cases c with
  | Integer n =>
    simp only [constToTagAndFields] at hc
    split at hc
    · simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨_, _, hfs⟩ := hc
      subst hfs
      exact LocalValueList.nil
    · exact Option.noConfusion hc
  | ByteString _ => simp [constToTagAndFields] at hc
  | String _ => simp [constToTagAndFields] at hc
  | Unit =>
    simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨_, _, hfs⟩ := hc
    subst hfs
    exact LocalValueList.nil
  | Bool b =>
    cases b <;>
    · simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨_, _, hfs⟩ := hc
      subst hfs
      exact LocalValueList.nil
  | ConstList l =>
    cases l with
    | nil =>
      simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨_, _, hfs⟩ := hc
      subst hfs
      exact LocalValueList.nil
    | cons head tail =>
      simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨_, _, hfs⟩ := hc
      subst hfs
      exact LocalValueList.cons (LocalValue.vcon _)
              (LocalValueList.cons (LocalValue.vcon _) LocalValueList.nil)
  | ConstDataList l =>
    cases l with
    | nil =>
      simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨_, _, hfs⟩ := hc
      subst hfs
      exact LocalValueList.nil
    | cons head tail =>
      simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨_, _, hfs⟩ := hc
      subst hfs
      exact LocalValueList.cons (LocalValue.vcon _)
              (LocalValueList.cons (LocalValue.vcon _) LocalValueList.nil)
  | ConstPairDataList _ => simp [constToTagAndFields] at hc
  | Pair p =>
    obtain ⟨a, b⟩ := p
    simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨_, _, hfs⟩ := hc
    subst hfs
    exact LocalValueList.cons (LocalValue.vcon _)
            (LocalValueList.cons (LocalValue.vcon _) LocalValueList.nil)
  | PairData p =>
    obtain ⟨a, b⟩ := p
    simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨_, _, hfs⟩ := hc
    subst hfs
    exact LocalValueList.cons (LocalValue.vcon _)
            (LocalValueList.cons (LocalValue.vcon _) LocalValueList.nil)
  | Data _ => simp [constToTagAndFields] at hc
  | ConstArray _ => simp [constToTagAndFields] at hc
  | Bls12_381_G1_element => simp [constToTagAndFields] at hc
  | Bls12_381_G2_element => simp [constToTagAndFields] at hc
  | Bls12_381_MlResult => simp [constToTagAndFields] at hc

--------------------------------------------------------------------------------
-- 10. step_preserves — main bisimulation theorem
--------------------------------------------------------------------------------

/-- The bisimulation is preserved by one CEK step. -/
theorem step_preserves : ∀ {s₁ s₂ : State},
    LocalState s₁ s₂ → LocalState (step s₁) (step s₂) := by
  intro s₁ s₂ h
  cases h with
  | halt h_v => exact LocalState.halt h_v
  | error => exact LocalState.error
  | @compute π₁ π₂ ρ₁ ρ₂ t k hρ h_closed hπ =>
    cases t with
    | Var n =>
      by_cases hn : n = 0
      · subst hn
        have h1 : ρ₁.lookup 0 = none := by cases ρ₁ <;> rfl
        have h2 : ρ₂.lookup 0 = none := by cases ρ₂ <;> rfl
        show LocalState
          (match ρ₁.lookup 0 with | some v => .ret π₁ v | none => .error)
          (match ρ₂.lookup 0 with | some v => .ret π₂ v | none => .error)
        rw [h1, h2]
        exact LocalState.error
      · have hpos : 0 < n := Nat.pos_of_ne_zero hn
        have h_n_le_k : n ≤ k := by
          simp only [Moist.Verified.closedAt] at h_closed
          exact of_decide_eq_true h_closed
        obtain ⟨v₁, v₂, hl₁, hl₂, h_v⟩ := localEnv_lookup k hρ hpos h_n_le_k
        show LocalState
          (match ρ₁.lookup n with | some v => .ret π₁ v | none => .error)
          (match ρ₂.lookup n with | some v => .ret π₂ v | none => .error)
        rw [hl₁, hl₂]
        exact LocalState.ret h_v hπ
    | Constant p =>
      show LocalState (.ret π₁ (.VCon p.1)) (.ret π₂ (.VCon p.1))
      exact LocalState.ret (LocalValue.vcon p.1) hπ
    | Builtin b =>
      show LocalState (.ret π₁ (.VBuiltin b [] (expectedArgs b)))
                       (.ret π₂ (.VBuiltin b [] (expectedArgs b)))
      exact LocalState.ret (LocalValue.vbuiltin b (expectedArgs b) LocalValueList.nil) hπ
    | Lam _ body =>
      have h_len := localEnv_length k hρ
      have h_body : Moist.Verified.closedAt (k + 1) body = true := by
        simp only [Moist.Verified.closedAt] at h_closed; exact h_closed
      show LocalState (.ret π₁ (.VLam body ρ₁)) (.ret π₂ (.VLam body ρ₂))
      exact LocalState.ret (LocalValue.vlam hρ h_len.1 h_len.2 h_body) hπ
    | Delay body =>
      have h_len := localEnv_length k hρ
      have h_body : Moist.Verified.closedAt k body = true := by
        simp only [Moist.Verified.closedAt] at h_closed; exact h_closed
      show LocalState (.ret π₁ (.VDelay body ρ₁)) (.ret π₂ (.VDelay body ρ₂))
      exact LocalState.ret (LocalValue.vdelay hρ h_len.1 h_len.2 h_body) hπ
    | Force e =>
      have h_e : Moist.Verified.closedAt k e = true := by
        simp only [Moist.Verified.closedAt] at h_closed; exact h_closed
      show LocalState (.compute (.force :: π₁) ρ₁ e) (.compute (.force :: π₂) ρ₂ e)
      exact LocalState.compute hρ h_e (LocalStack.cons LocalFrame.force hπ)
    | Apply f x =>
      have h_fx : Moist.Verified.closedAt k f = true ∧
                  Moist.Verified.closedAt k x = true := by
        simp only [Moist.Verified.closedAt, Bool.and_eq_true] at h_closed; exact h_closed
      have h_len := localEnv_length k hρ
      show LocalState (.compute (.arg x ρ₁ :: π₁) ρ₁ f)
                       (.compute (.arg x ρ₂ :: π₂) ρ₂ f)
      exact LocalState.compute hρ h_fx.1
              (LocalStack.cons (LocalFrame.arg hρ h_len.1 h_len.2 h_fx.2) hπ)
    | Constr tag args =>
      cases args with
      | nil =>
        show LocalState (.ret π₁ (.VConstr tag [])) (.ret π₂ (.VConstr tag []))
        exact LocalState.ret (LocalValue.vconstr tag LocalValueList.nil) hπ
      | cons m ms =>
        have h_mms : Moist.Verified.closedAt k m = true ∧
                     Moist.Verified.closedAtList k ms = true := by
          simp only [Moist.Verified.closedAt, Moist.Verified.closedAtList,
                     Bool.and_eq_true] at h_closed
          exact h_closed
        have h_len := localEnv_length k hρ
        show LocalState (.compute (.constrField tag [] ms ρ₁ :: π₁) ρ₁ m)
                         (.compute (.constrField tag [] ms ρ₂ :: π₂) ρ₂ m)
        exact LocalState.compute hρ h_mms.1
                (LocalStack.cons
                  (LocalFrame.constrField tag LocalValueList.nil hρ h_len.1 h_len.2 h_mms.2)
                  hπ)
    | Case scrut alts =>
      have h_sa : Moist.Verified.closedAt k scrut = true ∧
                  Moist.Verified.closedAtList k alts = true := by
        simp only [Moist.Verified.closedAt, Bool.and_eq_true] at h_closed; exact h_closed
      have h_len := localEnv_length k hρ
      show LocalState (.compute (.caseScrutinee alts ρ₁ :: π₁) ρ₁ scrut)
                       (.compute (.caseScrutinee alts ρ₂ :: π₂) ρ₂ scrut)
      exact LocalState.compute hρ h_sa.1
              (LocalStack.cons
                (LocalFrame.caseScrutinee hρ h_len.1 h_len.2 h_sa.2)
                hπ)
    | Error => exact LocalState.error
  | @ret π₁ π₂ v₁ v₂ h_v hπ =>
    cases hπ with
    | nil => exact LocalState.halt h_v
    | @cons f₁ f₂ π₁' π₂' h_f h_rest =>
      cases h_f with
      | force =>
        cases h_v with
        | vcon c => exact LocalState.error
        | vlam _ _ _ _ => exact LocalState.error
        | @vdelay body ρ₁' ρ₂' k' hρ' hlen₁ hlen₂ h_body =>
          show LocalState (.compute π₁' ρ₁' body) (.compute π₂' ρ₂' body)
          exact LocalState.compute hρ' h_body h_rest
        | vconstr tag _ => exact LocalState.error
        | @vbuiltin b ea args₁ args₂ h_args =>
          -- force on VBuiltin: cases on ea to let step compute the branches
          cases ea with
          | one k =>
            cases k with
            | argV => exact LocalState.error
            | argQ =>
              -- step: match evalBuiltin b args with | some => ret | none => error
              have ⟨h_some, h_none⟩ :=
                @localValueList_evalBuiltin b args₁ args₂ h_args
              cases he₁ : evalBuiltin b args₁ with
              | some v₁ =>
                obtain ⟨v₂, he₂, h_v_rel⟩ := h_some v₁ he₁
                show LocalState
                  (match evalBuiltin b args₁ with | some v => .ret π₁' v | none => .error)
                  (match evalBuiltin b args₂ with | some v => .ret π₂' v | none => .error)
                rw [he₁, he₂]
                exact LocalState.ret h_v_rel h_rest
              | none =>
                have he₂ : evalBuiltin b args₂ = none := h_none.mp he₁
                show LocalState
                  (match evalBuiltin b args₁ with | some v => .ret π₁' v | none => .error)
                  (match evalBuiltin b args₂ with | some v => .ret π₂' v | none => .error)
                rw [he₁, he₂]
                exact LocalState.error
          | more k rest =>
            cases k with
            | argV => exact LocalState.error
            | argQ =>
              exact LocalState.ret
                (LocalValue.vbuiltin b rest h_args) h_rest
      | @arg t ρ₁' ρ₂' k' hρ' hlen₁ hlen₂ h_t =>
        show LocalState (.compute (.funV v₁ :: π₁') ρ₁' t)
                         (.compute (.funV v₂ :: π₂') ρ₂' t)
        exact LocalState.compute hρ' h_t
                (LocalStack.cons (LocalFrame.funV h_v) h_rest)
      | @funV v_f₁ v_f₂ h_vf =>
        -- stack value v_f, current value v = v_x (arg being applied)
        cases h_vf with
        | vcon _ => exact LocalState.error
        | @vlam body ρ₁' ρ₂' k' hρ' hlen₁ hlen₂ h_body =>
          show LocalState (.compute π₁' (ρ₁'.extend v₁) body)
                           (.compute π₂' (ρ₂'.extend v₂) body)
          have hρ'' := localEnv_extend k' hρ' h_v
          exact LocalState.compute hρ'' h_body h_rest
        | vdelay _ _ _ _ => exact LocalState.error
        | vconstr _ _ => exact LocalState.error
        | @vbuiltin b ea args₁ args₂ h_args =>
          -- funV (VBuiltin b args ea) with arg v being applied: extends args
          cases ea with
          | one k =>
            cases k with
            | argQ => exact LocalState.error
            | argV =>
              -- step: evalBuiltin b (v :: args)
              have h_args' : LocalValueList (v₁ :: args₁) (v₂ :: args₂) :=
                LocalValueList.cons h_v h_args
              have ⟨h_some, h_none⟩ :=
                @localValueList_evalBuiltin b (v₁ :: args₁) (v₂ :: args₂) h_args'
              cases he₁ : evalBuiltin b (v₁ :: args₁) with
              | some v_r₁ =>
                obtain ⟨v_r₂, he₂, h_v_rel⟩ := h_some v_r₁ he₁
                show LocalState
                  (match evalBuiltin b (v₁ :: args₁) with
                    | some v => .ret π₁' v | none => .error)
                  (match evalBuiltin b (v₂ :: args₂) with
                    | some v => .ret π₂' v | none => .error)
                rw [he₁, he₂]
                exact LocalState.ret h_v_rel h_rest
              | none =>
                have he₂ : evalBuiltin b (v₂ :: args₂) = none := h_none.mp he₁
                show LocalState
                  (match evalBuiltin b (v₁ :: args₁) with
                    | some v => .ret π₁' v | none => .error)
                  (match evalBuiltin b (v₂ :: args₂) with
                    | some v => .ret π₂' v | none => .error)
                rw [he₁, he₂]
                exact LocalState.error
          | more k rest =>
            cases k with
            | argQ => exact LocalState.error
            | argV =>
              exact LocalState.ret
                (LocalValue.vbuiltin b rest (LocalValueList.cons h_v h_args)) h_rest
      | @applyArg v_x₁ v_x₂ h_vx =>
        cases h_v with
        | vcon _ => exact LocalState.error
        | @vlam body ρ₁' ρ₂' k' hρ' hlen₁ hlen₂ h_body =>
          show LocalState (.compute π₁' (ρ₁'.extend v_x₁) body)
                           (.compute π₂' (ρ₂'.extend v_x₂) body)
          have hρ'' := localEnv_extend k' hρ' h_vx
          exact LocalState.compute hρ'' h_body h_rest
        | vdelay _ _ _ _ => exact LocalState.error
        | vconstr _ _ => exact LocalState.error
        | @vbuiltin b ea args₁ args₂ h_args =>
          -- applyArg vx with VBuiltin returning: extends args with vx
          cases ea with
          | one k =>
            cases k with
            | argQ => exact LocalState.error
            | argV =>
              have h_args' : LocalValueList (v_x₁ :: args₁) (v_x₂ :: args₂) :=
                LocalValueList.cons h_vx h_args
              have ⟨h_some, h_none⟩ :=
                @localValueList_evalBuiltin b (v_x₁ :: args₁) (v_x₂ :: args₂) h_args'
              cases he₁ : evalBuiltin b (v_x₁ :: args₁) with
              | some v_r₁ =>
                obtain ⟨v_r₂, he₂, h_v_rel⟩ := h_some v_r₁ he₁
                show LocalState
                  (match evalBuiltin b (v_x₁ :: args₁) with
                    | some v => .ret π₁' v | none => .error)
                  (match evalBuiltin b (v_x₂ :: args₂) with
                    | some v => .ret π₂' v | none => .error)
                rw [he₁, he₂]
                exact LocalState.ret h_v_rel h_rest
              | none =>
                have he₂ : evalBuiltin b (v_x₂ :: args₂) = none := h_none.mp he₁
                show LocalState
                  (match evalBuiltin b (v_x₁ :: args₁) with
                    | some v => .ret π₁' v | none => .error)
                  (match evalBuiltin b (v_x₂ :: args₂) with
                    | some v => .ret π₂' v | none => .error)
                rw [he₁, he₂]
                exact LocalState.error
          | more k rest =>
            cases k with
            | argQ => exact LocalState.error
            | argV =>
              exact LocalState.ret
                (LocalValue.vbuiltin b rest (LocalValueList.cons h_vx h_args)) h_rest
      | @constrField tag done₁ done₂ todo ρ₁' ρ₂' k' h_done hρ' hlen₁ hlen₂ h_todo =>
        cases todo with
        | nil =>
          -- step: .ret π ((v :: done).reverse)
          show LocalState (.ret π₁' (.VConstr tag ((v₁ :: done₁).reverse)))
                           (.ret π₂' (.VConstr tag ((v₂ :: done₂).reverse)))
          exact LocalState.ret
            (LocalValue.vconstr tag
              (localValueList_reverse _ (LocalValueList.cons h_v h_done))) h_rest
        | cons m ms =>
          -- step: .compute (.constrField tag (v :: done) ms ρ :: π) ρ m
          have h_mms : Moist.Verified.closedAt k' m = true ∧
                       Moist.Verified.closedAtList k' ms = true := by
            simp only [Moist.Verified.closedAtList, Bool.and_eq_true] at h_todo
            exact h_todo
          show LocalState (.compute (.constrField tag (v₁ :: done₁) ms ρ₁' :: π₁') ρ₁' m)
                           (.compute (.constrField tag (v₂ :: done₂) ms ρ₂' :: π₂') ρ₂' m)
          exact LocalState.compute hρ' h_mms.1
                  (LocalStack.cons
                    (LocalFrame.constrField tag
                      (LocalValueList.cons h_v h_done) hρ' hlen₁ hlen₂ h_mms.2)
                    h_rest)
      | @caseScrutinee alts ρ₁' ρ₂' k' hρ' hlen₁ hlen₂ h_alts =>
        -- branch on h_v: VConstr / VCon / other (error)
        cases h_v with
        | vcon c =>
          -- step: match constToTagAndFields c with ...
          show LocalState
            (match constToTagAndFields c with
              | some (tag, numCtors, fields) =>
                if numCtors > 0 && alts.length > numCtors then State.error
                else match alts[tag]? with
                  | some alt => State.compute (fields.map Frame.applyArg ++ π₁') ρ₁' alt
                  | none => State.error
              | none => State.error)
            (match constToTagAndFields c with
              | some (tag, numCtors, fields) =>
                if numCtors > 0 && alts.length > numCtors then State.error
                else match alts[tag]? with
                  | some alt => State.compute (fields.map Frame.applyArg ++ π₂') ρ₂' alt
                  | none => State.error
              | none => State.error)
          cases hc : constToTagAndFields c with
          | none => exact LocalState.error
          | some r =>
            obtain ⟨tag, numCtors, fields⟩ := r
            by_cases hnum : (numCtors > 0 && alts.length > numCtors) = true
            · simp only [hnum, if_true]
              exact LocalState.error
            · simp only [hnum, if_false, Bool.false_eq_true]
              cases ha : alts[tag]? with
              | none => exact LocalState.error
              | some alt =>
                have h_alt := closedAtList_get k' alts tag alt h_alts ha
                have h_fs_refl : LocalValueList fields fields :=
                  localValueList_constToTagAndFields_refl hc
                exact LocalState.compute hρ' h_alt
                        (localValueList_to_applyArg_stack fields h_fs_refl h_rest)
        | vlam _ _ _ _ => exact LocalState.error
        | vdelay _ _ _ _ => exact LocalState.error
        | @vconstr tag fs₁ fs₂ h_fs =>
          -- step: match alts[tag]? with | some alt => .compute ... | none => .error
          show LocalState
            (match alts[tag]? with
              | some alt => State.compute (fs₁.map Frame.applyArg ++ π₁') ρ₁' alt
              | none => State.error)
            (match alts[tag]? with
              | some alt => State.compute (fs₂.map Frame.applyArg ++ π₂') ρ₂' alt
              | none => State.error)
          cases ha : alts[tag]? with
          | none => exact LocalState.error
          | some alt =>
            have h_alt := closedAtList_get k' alts tag alt h_alts ha
            exact LocalState.compute hρ' h_alt
                    (localValueList_to_applyArg_stack fs₁ h_fs h_rest)
        | vbuiltin _ _ _ => exact LocalState.error

--------------------------------------------------------------------------------
-- 11. Iterated step preservation and halt/error inversion
--------------------------------------------------------------------------------

open Moist.Verified.Equivalence (steps)

/-- Iterated version of `step_preserves`: `LocalState` is preserved under
    any number of `step` calls. -/
theorem localState_preserves_steps : ∀ (n : Nat) {s₁ s₂ : State},
    LocalState s₁ s₂ → LocalState (steps n s₁) (steps n s₂) := by
  intro n
  induction n with
  | zero => intro _ _ h; exact h
  | succ m ih =>
    intro s₁ s₂ h
    show LocalState (steps m (step s₁)) (steps m (step s₂))
    exact ih (step_preserves h)

/-- If `LocalState (.halt v) s`, then `s` must be a halt state. -/
theorem localState_halt_inv : ∀ {v : CekValue} {s : State},
    LocalState (.halt v) s → ∃ v', s = .halt v'
  | _, _, .halt _ => ⟨_, rfl⟩

/-- If `LocalState s (.halt v)`, then `s` must be a halt state. -/
theorem localState_halt_inv' {v : CekValue} {s : State}
    (h : LocalState s (.halt v)) : ∃ v', s = .halt v' :=
  localState_halt_inv (localState_symm h)

/-- If `LocalState .error s`, then `s` must be the error state. -/
theorem localState_error_inv : ∀ {s : State},
    LocalState .error s → s = .error
  | _, .error => rfl

/-- If `LocalState s .error`, then `s` must be the error state. -/
theorem localState_error_inv' {s : State} (h : LocalState s .error) : s = .error :=
  localState_error_inv (localState_symm h)

end Moist.Verified.Contextual.BisimRef
