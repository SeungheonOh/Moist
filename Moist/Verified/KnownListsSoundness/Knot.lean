import Moist.Verified.KnownListsSoundness.Calls
import Moist.Verified.ShapeFacts.Evaluation
import Moist.Verified.InlineSoundness.SubstRefinesExt
import Moist.MIR.LowerTotal

/-! # Recursive functions called on lists

The lowered fixed point `fixLamWrapUplc tB` evaluates to a closure over the
environment `fixEnv tB ρ`, which binds the self-application wrapper and the
recursive function `recVal tB ρ`. The source body `T₁` and the target body
`T₂` are the bodies after the first `m` parameters.

`Knot P m … k` (`Φ`) states that the two bodies are related at step index
`k` in the environments of the two fixed points, for argument vectors
holding lists at the positions `P`. It is proved by strong induction on `k`:
the source body is first evaluated with the target's recursive function
(`calls_eval`, using the induction hypothesis for the recursive calls of the
source body, which only pass lists at `P`), then the source body is replaced
by the target body in the target environment (the unindexed body relation).

Applying the two fixed points to the same arguments in the same environment
then gives related observations (`fixApply_obs`).
-/

namespace Moist.Verified.KnownLists

open Moist.CEK Moist.Plutus.Term
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.Contextual.Guarded
open Moist.Verified.TermObsRefinesWF
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.StepWellFormed (StateWellFormed)

/-! ## Fixed-point values -/

def selfApp : Term := .Apply (.Apply (.Var 2) (.Var 2)) (.Var 1)

def selfVal (tB : Term) (ρ : CekEnv) : CekValue :=
  .VLam (.Apply (.Lam 0 (.Lam 0 tB)) (.Lam 0 selfApp)) ρ

def recVal (tB : Term) (ρ : CekEnv) : CekValue := .VLam selfApp (ρ.extend (selfVal tB ρ))

def fixEnv (tB : Term) (ρ : CekEnv) : CekEnv := (ρ.extend (selfVal tB ρ)).extend (recVal tB ρ)

def fixVal (tB : Term) (ρ : CekEnv) : CekValue := .VLam tB (fixEnv tB ρ)

theorem fix_steps (tB : Term) (π : Stack) (ρ : CekEnv) :
    steps 16 (.compute π ρ (Moist.MIR.fixLamWrapUplc tB)) = .ret π (fixVal tB ρ) := rfl

theorem rec_steps (tB : Term) (π : Stack) (ρ : CekEnv) (a : CekValue) :
    steps 16 (.ret (.funV (recVal tB ρ) :: π) a) = .compute π ((fixEnv tB ρ).extend a) tB := rfl

theorem fixVal_steps (tB : Term) (π : Stack) (ρ : CekEnv) (a : CekValue) :
    steps 1 (.ret (.funV (fixVal tB ρ) :: π) a) = .compute π ((fixEnv tB ρ).extend a) tB := rfl

/-! ## Lambda prefixes and argument vectors -/

def applyAllT : Term → List Term → Term
  | f, [] => f
  | f, a :: as => applyAllT (.Apply f a) as

def lams : Nat → Term → Term
  | 0, t => t
  | n + 1, t => .Lam 0 (lams n t)

def extendAll (σ : CekEnv) : List CekValue → CekEnv
  | [] => σ
  | a :: as => extendAll (σ.extend a) as

theorem extendAll_append (σ : CekEnv) (as bs : List CekValue) :
    extendAll σ (as ++ bs) = extendAll (extendAll σ as) bs := by
  induction as generalizing σ with
  | nil => rfl
  | cons a as ih => exact ih (σ.extend a)

theorem extendAll_snoc (σ : CekEnv) (as : List CekValue) (a : CekValue) :
    extendAll σ (as ++ [a]) = (extendAll σ as).extend a := by
  rw [extendAll_append]; rfl

theorem extendAll_length (σ : CekEnv) (as : List CekValue) :
    (extendAll σ as).length = σ.length + as.length := by
  induction as generalizing σ with
  | nil => rfl
  | cons a as ih =>
    simp only [extendAll, ih, List.length_cons, CekEnv.extend, CekEnv.length]; omega

theorem extendAll_lookup_high (σ : CekEnv) : ∀ (as : List CekValue) (n : Nat), as.length < n →
    (extendAll σ as).lookup n = σ.lookup (n - as.length)
  | [], n, _ => by simp [extendAll]
  | a :: as, n, h => by
    rw [show a :: as = [a] ++ as from rfl, extendAll_append,
      extendAll_lookup_high _ as n (by simp at h; omega)]
    simp only [extendAll]
    simp only [List.length_cons] at h
    rw [show n - as.length = (n - (as.length + 1)) + 1 by omega]
    exact lookup_extend_succ σ a _ (by omega)

theorem extendAll_lookup_low (σ : CekEnv) :
    ∀ (as : List CekValue) (n : Nat), 0 < n → n ≤ as.length →
      (extendAll σ as).lookup n = as[as.length - n]?
  | [], n, h₁, h₂ => by simp at h₂; omega
  | a :: as, n, h₁, h₂ => by
    rw [show a :: as = [a] ++ as from rfl, extendAll_append]
    by_cases hn : n ≤ as.length
    · rw [extendAll_lookup_low (extendAll σ [a]) as n h₁ hn]
      simp only [List.length_cons, List.cons_append, List.nil_append]
      rw [show as.length + 1 - n = (as.length - n) + 1 by omega]
      rfl
    · have : n = as.length + 1 := by simp at h₂; omega
      subst this
      rw [extendAll_lookup_high _ as (as.length + 1) (by omega)]
      simp [extendAll, CekEnv.extend, CekEnv.lookup]

theorem extendAll_wellFormed {d : Nat} {σ : CekEnv} (hσ : EnvWellFormed d σ) (hlen : d ≤ σ.length) :
    ∀ (as : List CekValue), (∀ a ∈ as, ValueWellFormed a) →
      EnvWellFormed (d + as.length) (extendAll σ as)
  | [], _ => by simpa using hσ
  | a :: as, h => by
    have h₁ := envWellFormed_extend d hσ hlen (h a (.head _))
    have := extendAll_wellFormed (d := d + 1) h₁ (by simp [CekEnv.extend, CekEnv.length]; omega) as
      (fun b hb => h b (.tail _ hb))
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

/-! ## Well-formedness of the fixed point -/

theorem selfApp_closed : closedAt 2 selfApp = true := by simp [closedAt, selfApp]

theorem selfVal_wf {d : Nat} {ρ : CekEnv} {tB : Term} (hρ : EnvWellFormed d ρ) (hlen : d ≤ ρ.length)
    (htB : closedAt (d + 3) tB = true) : ValueWellFormed (selfVal tB ρ) := by
  refine .vlam hρ hlen ?_
  have h3 : closedAt (d + 1 + 1 + 1) tB = true := by simpa [Nat.add_assoc] using htB
  simp only [closedAt, selfApp, Bool.and_eq_true, decide_eq_true_eq, h3]
  exact ⟨trivial, ⟨by omega, by omega⟩, by omega⟩

theorem fixEnv_wf {d : Nat} {ρ : CekEnv} {tB : Term} (hρ : EnvWellFormed d ρ) (hlen : d ≤ ρ.length)
    (htB : closedAt (d + 3) tB = true) :
    EnvWellFormed (d + 2) (fixEnv tB ρ) ∧ d + 2 ≤ (fixEnv tB ρ).length ∧
      ValueWellFormed (recVal tB ρ) := by
  have hs := selfVal_wf hρ hlen htB
  have h₁ := envWellFormed_extend d hρ hlen hs
  have hlen₁ : d + 1 ≤ (ρ.extend (selfVal tB ρ)).length := by
    simp [CekEnv.extend, CekEnv.length]; omega
  have hr : ValueWellFormed (recVal tB ρ) := by
    refine .vlam h₁ hlen₁ ?_
    simp only [closedAt, selfApp, Bool.and_eq_true, decide_eq_true_eq]; omega
  refine ⟨envWellFormed_extend (d + 1) h₁ hlen₁ hr, ?_, hr⟩
  simp [fixEnv, CekEnv.extend, CekEnv.length]; omega

theorem fixVal_wf {d : Nat} {ρ : CekEnv} {tB : Term} (hρ : EnvWellFormed d ρ) (hlen : d ≤ ρ.length)
    (htB : closedAt (d + 3) tB = true) : ValueWellFormed (fixVal tB ρ) := by
  obtain ⟨h₁, h₂, _⟩ := fixEnv_wf hρ hlen htB
  exact .vlam h₁ h₂ (by simpa [Nat.add_assoc] using htB)

theorem closedAt_lams : ∀ (n D : Nat) (T : Term), closedAt D (lams n T) = closedAt (D + n) T
  | 0, D, T => rfl
  | n + 1, D, T => by
    simp only [lams, closedAt]
    rw [closedAt_lams n (D + 1) T, show D + 1 + n = D + (n + 1) by omega]

theorem listRel_snoc {R : α → α → Prop} {xs ys : List α} {x y : α} (h : ListRel R xs ys)
    (hxy : R x y) : ListRel R (xs ++ [x]) (ys ++ [y]) :=
  listRel_append h ⟨hxy, trivial⟩

theorem listRel_valueRel_refl (k : Nat) :
    ∀ (as : List CekValue), (∀ a ∈ as, ValueWellFormed a) → ListRel (ValueRel wfGuard k) as as
  | [], _ => trivial
  | a :: as, h => ⟨valueRel_refl k a (h a (.head _)),
      listRel_valueRel_refl k as fun b hb => h b (.tail _ hb)⟩

theorem listRel_length' {R : α → α → Prop} :
    ∀ {xs ys : List α}, ListRel R xs ys → xs.length = ys.length
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h id
  | _ :: _, [], h => absurd h id
  | _ :: _, _ :: _, h => by simp [listRel_length' h.2]

theorem getElem?_snoc_of_lt {xs : List α} {x : α} {p : Nat} (h : p < xs.length) :
    (xs ++ [x])[p]? = xs[p]? := by
  rw [List.getElem?_append_left h]

theorem getElem?_snoc_last {xs : List α} {x : α} : (xs ++ [x])[xs.length]? = some x := by
  simp

/-! ## The knot -/

section Knot

variable (P : List Nat) (m : Nat) (Ls : List Nat) (tB₁ tB₂ T₁ T₂ : Term) (ρ : CekEnv)

/-- The two bodies are related at index `k` in the environments of the two
    fixed points, for arguments holding lists at the positions `P`. -/
def Knot (k : Nat) : Prop :=
  ∀ as₁ as₂ : List CekValue, as₁.length = m → ListRel (ValueRel wfGuard k) as₁ as₂ →
    (∀ a ∈ as₁, ValueWellFormed a) → (∀ a ∈ as₂, ValueWellFormed a) →
    (∀ p ∈ P, ∀ a, as₁[p]? = some a → ListValue a) →
    Eval wfGuard k (extendAll (fixEnv tB₁ ρ) as₁) (extendAll (fixEnv tB₂ ρ) as₂) T₁ T₂

/-- `G` applied to one more argument enters the body after the argument
    prefix `as`, with `r - 1` parameters still to bind. -/
def Applies (tB T : Term) (G : CekValue) (as : List CekValue) (r : Nat) : Prop :=
  ∃ n, ∀ (π : Stack) (a : CekValue), steps (n + 1) (.ret (.funV G :: π) a) =
    .compute π (extendAll (fixEnv tB ρ) (as ++ [a])) (lams (r - 1) T)

variable {P m Ls tB₁ tB₂ T₁ T₂ ρ}

theorem lists_snoc {as : List CekValue} {a : CekValue} {r : Nat}
    (hlen : as.length = m - r)
    (hlist : ∀ p ∈ P, ∀ b, as[p]? = some b → ListValue b) (ha : m - r ∈ P → ListValue a) :
    ∀ p ∈ P, ∀ b, (as ++ [a])[p]? = some b → ListValue b := by
  intro p hp b hb
  by_cases hlt : p < as.length
  · rw [getElem?_snoc_of_lt hlt] at hb; exact hlist p hp b hb
  · by_cases heq : p = as.length
    · subst heq
      rw [getElem?_snoc_last] at hb; cases hb
      exact ha (by rw [← hlen]; exact hp)
    · have : (as ++ [a])[p]? = none := by
        rw [List.getElem?_eq_none]; simp; omega
      rw [this] at hb; cases hb

theorem wf_snoc {as : List CekValue} {a : CekValue} (h : ∀ b ∈ as, ValueWellFormed b)
    (ha : ValueWellFormed a) : ∀ b ∈ as ++ [a], ValueWellFormed b := by
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact h b hb
  · simp at hb; subst hb; exact ha

theorem fixEnv_lookup_outer (tB : Term) (n : Nat) (hn : 0 < n) :
    (fixEnv tB ρ).lookup (n + 2) = ρ.lookup n := by
  rw [show n + 2 = (n + 1) + 1 by omega, fixEnv, lookup_extend_succ _ _ _ (by omega),
    lookup_extend_succ _ _ _ hn]

theorem rec_applies (tB T : Term) (hB : tB = lams (m - 1) T) :
    Applies ρ tB T (recVal tB ρ) [] m := ⟨15, fun π a => by
  rw [rec_steps, ← hB]; rfl⟩

theorem fixVal_applies (tB T : Term) (hB : tB = lams (m - 1) T) :
    Applies ρ tB T (fixVal tB ρ) [] m := ⟨0, fun π a => by
  rw [fixVal_steps, ← hB]; rfl⟩

section Partial

variable {d : Nat} (hρ : EnvWellFormed d ρ) (hlen : d ≤ ρ.length)
  (hT₁ : closedAt (d + 2 + m) T₁ = true) (hT₂ : closedAt (d + 2 + m) T₂ = true)
  (hB₁ : tB₁ = lams (m - 1) T₁) (hB₂ : tB₂ = lams (m - 1) T₂) (hm : 0 < m)
include hρ hlen hT₁ hT₂ hB₁ hB₂ hm

omit hρ hlen hT₂ hB₂ in
theorem tB_closed₁ : closedAt (d + 3) tB₁ = true := by
  rw [hB₁, closedAt_lams, show d + 3 + (m - 1) = d + 2 + m by omega]; exact hT₁

omit hρ hlen hT₁ hB₁ in
theorem tB_closed₂ : closedAt (d + 3) tB₂ = true := by
  rw [hB₂, closedAt_lams, show d + 3 + (m - 1) = d + 2 + m by omega]; exact hT₂

omit hT₁ hT₂ hB₁ hB₂ hm in
theorem prefixEnv_wf {tB : Term} (htB : closedAt (d + 3) tB = true) {as : List CekValue}
    (hw : ∀ a ∈ as, ValueWellFormed a) :
    EnvWellFormed (d + 2 + as.length) (extendAll (fixEnv tB ρ) as) ∧
      d + 2 + as.length ≤ (extendAll (fixEnv tB ρ) as).length := by
  obtain ⟨h₁, h₂, _⟩ := fixEnv_wf hρ hlen htB
  refine ⟨extendAll_wellFormed h₁ h₂ as hw, ?_⟩
  rw [extendAll_length]; omega

/-- Partial applications of the two recursive functions agree on list
    arguments, given the knot below `k`. -/
theorem partial_PR (k : Nat) (ih : ∀ j < k, Knot P m tB₁ tB₂ T₁ T₂ ρ j) :
    ∀ r, 0 < r → r ≤ m → ∀ k' ≤ k, ∀ as₁ as₂ : List CekValue, as₁.length = m - r →
      ListRel (ValueRel wfGuard k') as₁ as₂ → (∀ a ∈ as₁, ValueWellFormed a) →
      (∀ a ∈ as₂, ValueWellFormed a) → (∀ p ∈ P, ∀ a, as₁[p]? = some a → ListValue a) →
      ∀ G₁ G₂, Applies ρ tB₁ T₁ G₁ as₁ r → Applies ρ tB₂ T₂ G₂ as₂ r → PR P m r k' G₁ G₂ := by
  intro r
  induction r with
  | zero => intro h; omega
  | succ r ihr =>
  intro _ hrm k' hk' as₁ as₂ hlen₁ hrel hw₁ hw₂ hlist G₁ G₂ ⟨n₁, hs₁⟩ ⟨n₂, hs₂⟩
  have hlen₂ : as₂.length = m - (r + 1) := by rw [← listRel_length' hrel]; exact hlen₁
  rw [PR_succ]
  intro j hj a₁ a₂ ha wa₁ wa₂ hl π₁ π₂ hcont
  match j with
  | 0 => exact obsRefinesK_zero_ret
  | j + 1 =>
  apply obsRefinesK_of_step_ret
  refine obsRefinesK_of_steps_left (n := n₁) (hs₁ π₁ a₁)
    (obsRefinesK_of_steps_right (n := n₂) (hs₂ π₂ a₂) ?_)
  have hrel' : ListRel (ValueRel wfGuard j) (as₁ ++ [a₁]) (as₂ ++ [a₂]) :=
    listRel_snoc (listRel_valueRel_mono (by omega) hrel) (valueRel_mono (by omega) ha)
  have hw₁' := wf_snoc hw₁ wa₁
  have hw₂' := wf_snoc hw₂ wa₂
  have hlist' := lists_snoc (r := r + 1) hlen₁ hlist hl
  have henv₁ := prefixEnv_wf hρ hlen (tB_closed₁ hT₁ hB₁ hm) hw₁'
  have henv₂ := prefixEnv_wf hρ hlen (tB_closed₂ hT₂ hB₂ hm) hw₂'
  have hlenA₁ : (as₁ ++ [a₁]).length = m - r := by simp; omega
  have hlenA₂ : (as₂ ++ [a₂]).length = m - r := by simp; omega
  cases r with
  | zero =>
    simp only [lams]
    have hπ : StackRel wfGuard j π₁ π₂ := stackRel_mono (by omega) hcont
    have hm' : (as₁ ++ [a₁]).length = m := by rw [hlenA₁]; omega
    refine ih j (by omega) _ _ hm' hrel' hw₁' hw₂' hlist' j (Nat.le_refl _) π₁ π₂ hπ ?_ ?_
    · refine .compute hπ.1 henv₁.1 henv₁.2 ?_
      rw [hm']; simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hT₁
    · refine .compute hπ.2.1 henv₂.1 henv₂.2 ?_
      rw [show (as₂ ++ [a₂]).length = m by rw [hlenA₂]; omega]
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hT₂
  | succ r =>
    simp only [show r + 1 + 1 - 1 = r + 1 by omega, lams]
    refine obsRefinesK_of_steps_left (n := 1) rfl (obsRefinesK_of_steps_right (n := 1) rfl ?_)
    simp only [steps, step]
    have hclosed : ∀ (T : Term), closedAt (d + 2 + m) T = true →
        closedAt (d + 2 + (m - (r + 1)) + 1) (lams r T) = true := by
      intro T hT
      rw [closedAt_lams, show d + 2 + (m - (r + 1)) + 1 + r = d + 2 + m by omega]; exact hT
    have wfL₁ : ValueWellFormed (.VLam (lams r T₁) (extendAll (fixEnv tB₁ ρ) (as₁ ++ [a₁]))) :=
      .vlam henv₁.1 henv₁.2 (by rw [hlenA₁]; exact hclosed T₁ hT₁)
    have wfL₂ : ValueWellFormed (.VLam (lams r T₂) (extendAll (fixEnv tB₂ ρ) (as₂ ++ [a₂]))) :=
      .vlam henv₂.1 henv₂.2 (by rw [hlenA₂]; exact hclosed T₂ hT₂)
    refine hcont.2.2 j (by omega) _ _ ?_ wfL₁ wfL₂
    refine ihr (by omega) (by omega) j (by omega) _ _ hlenA₁ hrel' hw₁' hw₂' hlist' _ _
      ⟨0, fun π a => ?_⟩ ⟨0, fun π a => ?_⟩
    · simp only [steps, step, extendAll_snoc, show r + 1 - 1 = r by omega]
    · simp only [steps, step, extendAll_snoc, show r + 1 - 1 = r by omega]

/-- The knot at every index. -/
theorem knot (hcalls : Calls P m (m + 1) Ls T₁)
    (hLs : ∀ i ∈ Ls, (0 < i ∧ i ≤ m ∧ m - i ∈ P) ∨
      (m + 2 < i ∧ ∃ l, ρ.lookup (i - (m + 2)) = some l ∧ ListValue l))
    (hbody : ∀ as : List CekValue, as.length = m → (∀ a ∈ as, ValueWellFormed a) →
      (∀ p ∈ P, ∀ a, as[p]? = some a → ListValue a) → ∀ π, StackWellFormed π →
      ObsRefines (.compute π (extendAll (fixEnv tB₂ ρ) as) T₁)
        (.compute π (extendAll (fixEnv tB₂ ρ) as) T₂)) :
    ∀ k, Knot P m tB₁ tB₂ T₁ T₂ ρ k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro as₁ as₂ hlen₁ hrel hw₁ hw₂ hlist j hj π₁ π₂ hπ hst₁ hst₂
  have hlen₂ : as₂.length = m := by rw [← listRel_length' hrel]; exact hlen₁
  have htB₁ := tB_closed₁ hT₁ hB₁ hm
  have htB₂ := tB_closed₂ hT₂ hB₂ hm
  have henv₂ := prefixEnv_wf hρ hlen htB₂ hw₂
  rw [hlen₂] at henv₂
  have hlist₂ : ∀ p ∈ P, ∀ a, as₂[p]? = some a → ListValue a := by
    intro p hp a ha
    rcases listRel_getElem? hrel p with ⟨h₁, h₂⟩ | ⟨x, y, h₁, h₂, hxy⟩
    · rw [h₂] at ha; cases ha
    · rw [h₂] at ha; cases ha
      have hx := hlist p hp x h₁
      obtain ⟨c, rfl⟩ := listValue_vcon hx
      rw [valueRel_vcon_left hxy]; exact hx
  have hlookup_low : ∀ (σ : CekEnv) (as : List CekValue), as.length = m → ∀ n, 0 < n → n ≤ m →
      (extendAll σ as).lookup n = as[m - n]? := by
    intro σ as hl n hn hnm
    rw [extendAll_lookup_low σ as n hn (by omega), hl]
  have hlookup_high : ∀ (tB : Term) (as : List CekValue), as.length = m → ∀ n, m + 2 < n →
      (extendAll (fixEnv tB ρ) as).lookup n = ρ.lookup (n - (m + 2)) := by
    intro tB as hl n hn
    rw [extendAll_lookup_high _ as n (by omega), hl,
      show n - m = (n - (m + 2)) + 2 by omega, fixEnv_lookup_outer tB _ (by omega)]
  have hrec : ∀ (tB : Term) (as : List CekValue), as.length = m →
      (extendAll (fixEnv tB ρ) as).lookup (m + 1) = some (recVal tB ρ) := by
    intro tB as hl
    rw [extendAll_lookup_high _ as (m + 1) (by omega), hl, show m + 1 - m = 1 by omega]; rfl
  have henv : EnvOK P m k (d + 2 + m) (m + 1) Ls (extendAll (fixEnv tB₁ ρ) as₁)
      (extendAll (fixEnv tB₂ ρ) as₂) := by
    refine ⟨fun n hn hnd hF hS => ?_, fun i hi => ?_, ?_⟩
    · by_cases hnm : n ≤ m
      · rw [hlookup_low _ as₁ hlen₁ n hn hnm, hlookup_low _ as₂ hlen₂ n hn hnm]
        rcases listRel_getElem? hrel (m - n) with ⟨h₁, _⟩ | ⟨x, y, h₁, h₂, hxy⟩
        · rw [List.getElem?_eq_none_iff] at h₁; omega
        · exact ⟨x, y, h₁, h₂, hxy⟩
      · rw [hlookup_high _ as₁ hlen₁ n (by omega), hlookup_high _ as₂ hlen₂ n (by omega)]
        obtain ⟨v, hv, hwf⟩ := envWellFormed_lookup d hρ (n := n - (m + 2)) (by omega) (by omega)
        exact ⟨v, v, hv, hv, valueRel_refl k v hwf⟩
    · rcases hLs i hi with ⟨hi0, him, hp⟩ | ⟨hi2, l, hl, hlv⟩
      · rw [hlookup_low _ as₁ hlen₁ i hi0 him, hlookup_low _ as₂ hlen₂ i hi0 him]
        rcases listRel_getElem? hrel (m - i) with ⟨h₁, _⟩ | ⟨x, y, h₁, h₂, hxy⟩
        · rw [List.getElem?_eq_none_iff] at h₁; omega
        · have hx := hlist (m - i) hp x h₁
          obtain ⟨c, rfl⟩ := listValue_vcon hx
          rw [valueRel_vcon_left hxy] at h₂
          exact ⟨_, h₁, h₂, hx⟩
      · rw [hlookup_high _ as₁ hlen₁ i hi2, hlookup_high _ as₂ hlen₂ i hi2]
        exact ⟨l, hl, hl, hlv⟩
    · refine ⟨recVal tB₁ ρ, recVal tB₂ ρ, hrec _ _ hlen₁, hrec _ _ hlen₂, ?_,
        (fixEnv_wf hρ hlen htB₁).2.2, (fixEnv_wf hρ hlen htB₂).2.2⟩
      exact partial_PR hρ hlen hT₁ hT₂ hB₁ hB₂ hm k ih m hm (Nat.le_refl _) k (Nat.le_refl _) [] []
        (by simp) trivial (by simp) (by simp) (by simp) _ _ (rec_applies tB₁ T₁ hB₁)
        (rec_applies tB₂ T₂ hB₂)
  have hmid : wfGuard.St (.compute π₂ (extendAll (fixEnv tB₂ ρ) as₂) T₁) :=
    .compute hπ.2.1 henv₂.1 henv₂.2 (by simpa [Nat.add_assoc] using hT₁)
  exact InlineSoundness.SubstRefinesExt.obsRefinesK_compose_obsRefines_right
    (calls_eval hcalls hT₁ henv j hj π₁ π₂ hπ hst₁ hmid)
    (hbody as₂ hlen₂ hw₂ hlist₂ π₂ hπ.2.1)

omit hT₁ hT₂ hB₁ hB₂ hm in
theorem argFrames_wf {as : List Term} (hclosed : ∀ a ∈ as, closedAt d a = true) {π : Stack}
    (hπ : StackWellFormed π) : StackWellFormed (as.map (fun a => Frame.arg a ρ) ++ π) := by
  induction as with
  | nil => simpa using hπ
  | cons a as ih =>
    exact .cons (.arg hρ hlen (hclosed a (.head _))) (ih fun b hb => hclosed b (.tail _ hb))

/-- The two fixed points applied to the remaining arguments `rest`, with the
    argument values `as` already bound. -/
theorem fixApply_rest (hknot : ∀ k, Knot P m tB₁ tB₂ T₁ T₂ ρ k) :
    ∀ r, 0 < r → r ≤ m → ∀ as : List CekValue, as.length = m - r →
      (∀ a ∈ as, ValueWellFormed a) → (∀ p ∈ P, ∀ a, as[p]? = some a → ListValue a) →
      ∀ rest : List Term, r ≤ rest.length → (∀ a ∈ rest, closedAt d a = true) →
      (∀ i a, rest[i]? = some a → m - r + i ∈ P → ∀ v, Halts ρ a v → ListValue v) →
      ∀ π, StackWellFormed π → ∀ G₁ G₂, Applies ρ tB₁ T₁ G₁ as r → Applies ρ tB₂ T₂ G₂ as r →
      ObsRefines (.ret (rest.map (fun a => Frame.arg a ρ) ++ π) G₁)
        (.ret (rest.map (fun a => Frame.arg a ρ) ++ π) G₂) := by
  intro r
  induction r with
  | zero => intro h; omega
  | succ r ihr =>
  intro _ hrm as hlenA hw hlist rest hrest hclosed hrlist π hπ G₁ G₂ ⟨n₁, hs₁⟩ ⟨n₂, hs₂⟩
  match rest, hrest with
  | a :: rest', hrest' =>
  have hca : closedAt d a = true := hclosed a (.head _)
  have hclosed' : ∀ b ∈ rest', closedAt d b = true := fun b hb => hclosed b (.tail _ hb)
  have hπ' := argFrames_wf hρ hlen hclosed' hπ
  apply obsRefines_of_step
  simp only [List.map_cons, List.cons_append, step]
  apply obsRefines_of_continuation
  intro v hv
  have hwv := halts_wellFormed hρ hlen hca hv
  have hlv : m - (r + 1) ∈ P → ListValue v := fun hp =>
    hrlist 0 a rfl (by simpa using hp) v hv
  have hw' := wf_snoc hw hwv
  have hlist' := lists_snoc (r := r + 1) hlenA hlist hlv
  have hlenA' : (as ++ [v]).length = m - r := by simp; omega
  refine obsRefines_of_steps (n₁ + 1) (n₂ + 1) ?_
  rw [hs₁, hs₂]
  have htB₁ := tB_closed₁ hT₁ hB₁ hm
  have htB₂ := tB_closed₂ hT₂ hB₂ hm
  have henv₁ := prefixEnv_wf hρ hlen htB₁ hw'
  have henv₂ := prefixEnv_wf hρ hlen htB₂ hw'
  cases r with
  | zero =>
    simp only [lams]
    have hm' : (as ++ [v]).length = m := by rw [hlenA']; omega
    apply obsRefines_of_forall_k
    intro k
    refine hknot k _ _ hm' (listRel_valueRel_refl k _ hw') hw' hw' hlist' k (Nat.le_refl _) _ _
      (stackRel_refl k hπ') ?_ ?_
    · refine .compute hπ' henv₁.1 henv₁.2 ?_
      rw [hm']; simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hT₁
    · refine .compute hπ' henv₂.1 henv₂.2 ?_
      rw [hm']; simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hT₂
  | succ r =>
    simp only [show r + 1 + 1 - 1 = r + 1 by omega, lams]
    apply obsRefines_of_step
    simp only [step]
    refine ihr (by omega) (by omega) _ hlenA' hw' hlist' rest' (by simp only [List.length_cons] at hrest'; omega) hclosed'
      (fun i b hb hp => hrlist (i + 1) b (by simpa using hb) (by
        rw [show m - (r + 1 + 1) + (i + 1) = m - (r + 1) + i by omega]; exact hp)) π hπ _ _
      ⟨0, fun π a => ?_⟩ ⟨0, fun π a => ?_⟩
    · simp only [steps, step, extendAll_snoc, show r + 1 - 1 = r by omega]
    · simp only [steps, step, extendAll_snoc, show r + 1 - 1 = r by omega]

omit hρ hlen hT₁ hT₂ hB₁ hB₂ hm in
theorem applyAllT_steps : ∀ (args : List Term) (f : Term) (π : Stack),
    steps args.length (.compute π ρ (applyAllT f args)) =
      .compute (args.map (fun a => Frame.arg a ρ) ++ π) ρ f
  | [], f, π => rfl
  | a :: as, f, π => by
    simp only [applyAllT, List.length_cons]
    rw [steps_trans, applyAllT_steps as (.Apply f a) π]
    rfl

/-- The two fixed points applied to the same arguments in the same
    environment. -/
theorem fixApply_obs (hknot : ∀ k, Knot P m tB₁ tB₂ T₁ T₂ ρ k) (targs : List Term)
    (hn : m ≤ targs.length) (hclosed : ∀ a ∈ targs, closedAt d a = true)
    (hlist : ∀ p ∈ P, ∀ a, targs[p]? = some a → ∀ v, Halts ρ a v → ListValue v)
    (π : Stack) (hπ : StackWellFormed π) :
    ObsRefines (.compute π ρ (applyAllT (Moist.MIR.fixLamWrapUplc tB₁) targs))
      (.compute π ρ (applyAllT (Moist.MIR.fixLamWrapUplc tB₂) targs)) := by
  refine obsRefines_of_steps (targs.length + 16) (targs.length + 16) ?_
  rw [steps_trans, steps_trans, applyAllT_steps, applyAllT_steps, fix_steps, fix_steps]
  exact fixApply_rest hρ hlen hT₁ hT₂ hB₁ hB₂ hm hknot m hm (Nat.le_refl _) [] (by simp) (by simp)
    (by simp) targs hn hclosed (fun i a ha hp => hlist i (by simpa using hp) a ha) π hπ _ _
    (fixVal_applies tB₁ T₁ hB₁) (fixVal_applies tB₂ T₂ hB₂)

end Partial

end Knot

end Moist.Verified.KnownLists
