import Moist.Verified.ShapeFacts.Relation
import Moist.Verified.ShapeFacts.Values

variable [sv : Moist.CEK.SemVariant]

/-! # Calls of a recursive function on lists

`Calls P m F Ls t` states that in `t` the recursive function bound at index
`F` (its self-application wrapper sits at `F + 1`) occurs only at the head of
calls supplying its first `m` arguments, and that the arguments at the
positions `P` name slots of `Ls`, which hold lists. The function never
escapes, so `t` may be evaluated with two different recursive functions that
agree only on calls whose arguments at `P` are lists (`PR`), and the two
evaluations are related (`calls_eval`). Every other slot of the two
environments is related by the logical relation, and the slots of `Ls` hold
the same list.

`PR Q P m r k G₁ G₂` relates two functions still expecting the last `r` of the
`m` arguments: applied to related arguments, with a list at a position of
`P`, they return to stacks related as `ContOf r`, i.e. the stacks of the
remaining application (`r - 1` more arguments) or, after the last argument,
any related stacks.
-/

namespace Moist.Verified.KnownLists

open Moist.CEK Moist.Plutus.Term
open Moist.Verified Moist.Verified.Equivalence
open Moist.Verified.Contextual.Guarded
open Moist.Verified.TermObsRefinesWF
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts

/-! ## Families of list values

The relation is parametrized by a family of list values closed under taking
tails: every builtin list (`anyList`), or a narrower family such as the lists
of data pairs.
-/

structure ListFamily where
  mem : CekValue → Prop
  list : ∀ {v}, mem v → ListValue v
  tail : ∀ {ty : BuiltinType} {c : Const} {cs : List Const},
    mem (.VCon (.ConstList ty (c :: cs))) → mem (.VCon (.ConstList ty cs))

/-- Every builtin list. -/
def anyList : ListFamily := ⟨ListValue, id, fun _ => trivial⟩

variable {Q : ListFamily}

/-! ## The syntactic predicate -/

/-- An argument at a list position names a slot holding a list. -/
def ArgOK (P : List Nat) (Ls : List Nat) (position : Nat) (a : Term) : Prop :=
  position ∈ P → ∃ i, a = .Var i ∧ i ∈ Ls

def shiftLs (n : Nat) (Ls : List Nat) : List Nat := Ls.map (· + n)

mutual
  inductive Calls (P : List Nat) (m : Nat) : Nat → List Nat → List Nat → Term → Prop
    | var {F : Nat} {X Ls : List Nat} {i : Nat} : i ≠ F → i ∉ X → Calls P m F X Ls (.Var i)
    | constant {F : Nat} {X Ls : List Nat} {c : Const × BuiltinType} : Calls P m F X Ls (.Constant c)
    | builtin {F : Nat} {X Ls : List Nat} {b : BuiltinFun} : Calls P m F X Ls (.Builtin b)
    | error {F : Nat} {X Ls : List Nat} : Calls P m F X Ls .Error
    | lam {F : Nat} {X Ls : List Nat} {x : Nat} {b : Term} :
        Calls P m (F + 1) (shiftLs 1 X) (shiftLs 1 Ls) b → Calls P m F X Ls (.Lam x b)
    | apply {F : Nat} {X Ls : List Nat} {f a : Term} :
        Calls P m F X Ls f → Calls P m F X Ls a → Calls P m F X Ls (.Apply f a)
    | call {F : Nat} {X Ls : List Nat} {f a : Term} :
        Spine P m F X Ls 1 f → Calls P m F X Ls a → ArgOK P Ls (m - 1) a →
        Calls P m F X Ls (.Apply f a)
    | force {F : Nat} {X Ls : List Nat} {t : Term} : Calls P m F X Ls t → Calls P m F X Ls (.Force t)
    | delay {F : Nat} {X Ls : List Nat} {t : Term} : Calls P m F X Ls t → Calls P m F X Ls (.Delay t)
    | constr {F : Nat} {X Ls : List Nat} {tag : Nat} {ts : List Term} :
        CallsList P m F X Ls ts → Calls P m F X Ls (.Constr tag ts)
    | case {F : Nat} {X Ls : List Nat} {s : Term} {alts : List Term} :
        Calls P m F X Ls s → CallsList P m F X Ls alts → Calls P m F X Ls (.Case s alts)
    | listCase {F : Nat} {X Ls : List Nat} {z x y : Nat} {C : Term} {rest : List Term} :
        z ∈ Ls → Calls P m (F + 2) (shiftLs 2 X) (1 :: shiftLs 2 Ls) C → CallsList P m F X Ls rest →
        Calls P m F X Ls (.Case (.Var z) (.Lam x (.Lam y C) :: rest))

  /-- `Spine P m F X Ls r t`: `t` is the recursive function applied to its first
      `m - r` arguments. -/
  inductive Spine (P : List Nat) (m : Nat) : Nat → List Nat → List Nat → Nat → Term → Prop
    | head {F : Nat} {X Ls : List Nat} : Spine P m F X Ls m (.Var F)
    | arg {F : Nat} {X Ls : List Nat} {r : Nat} {f a : Term} :
        Spine P m F X Ls (r + 2) f → Calls P m F X Ls a → ArgOK P Ls (m - (r + 2)) a →
        Spine P m F X Ls (r + 1) (.Apply f a)

  inductive CallsList (P : List Nat) (m : Nat) : Nat → List Nat → List Nat → List Term → Prop
    | nil {F : Nat} {X Ls : List Nat} : CallsList P m F X Ls []
    | cons {F : Nat} {X Ls : List Nat} {t : Term} {ts : List Term} :
        Calls P m F X Ls t → CallsList P m F X Ls ts → CallsList P m F X Ls (t :: ts)
end

/-! ## Functions agreeing on list arguments -/

/-- `PR Q P m r k G₁ G₂`: `G₁` and `G₂` still expect the last `r` of `m`
    arguments and agree on calls passing lists at the positions `P`. -/
def PR (Q : ListFamily) (P : List Nat) (m : Nat) : Nat → Nat → CekValue → CekValue → Prop
  | 0, _, _, _ => True
  | r + 1, k, G₁, G₂ =>
    ∀ j ≤ k, ∀ a₁ a₂, ValueRel wfGuard j a₁ a₂ → ValueWellFormed a₁ → ValueWellFormed a₂ →
      (m - (r + 1) ∈ P → Q.mem a₁) →
      ∀ π₁ π₂,
        (match r with
          | 0 => StackRel wfGuard j π₁ π₂
          | r' + 1 => StackWellFormed π₁ ∧ StackWellFormed π₂ ∧
              ∀ j' ≤ j, ∀ H₁ H₂, PR Q P m (r' + 1) j' H₁ H₂ → ValueWellFormed H₁ →
                ValueWellFormed H₂ → ObsRefinesK j' (.ret π₁ H₁) (.ret π₂ H₂)) →
        ObsRefinesK j (.ret (.funV G₁ :: π₁) a₁) (.ret (.funV G₂ :: π₂) a₂)

/-- Stacks waiting for the result of a call still expecting `r` arguments. -/
def ContOf (Q : ListFamily) (P : List Nat) (m : Nat) : Nat → Nat → Stack → Stack → Prop
  | 0, j, π₁, π₂ => StackRel wfGuard j π₁ π₂
  | r + 1, j, π₁, π₂ => StackWellFormed π₁ ∧ StackWellFormed π₂ ∧
      ∀ j' ≤ j, ∀ H₁ H₂, PR Q P m (r + 1) j' H₁ H₂ → ValueWellFormed H₁ →
        ValueWellFormed H₂ → ObsRefinesK j' (.ret π₁ H₁) (.ret π₂ H₂)

theorem PR_succ {P : List Nat} {m r k : Nat} {G₁ G₂ : CekValue} :
    PR Q P m (r + 1) k G₁ G₂ ↔
      ∀ j ≤ k, ∀ a₁ a₂, ValueRel wfGuard j a₁ a₂ → ValueWellFormed a₁ → ValueWellFormed a₂ →
        (m - (r + 1) ∈ P → Q.mem a₁) →
        ∀ π₁ π₂, ContOf Q P m r j π₁ π₂ →
          ObsRefinesK j (.ret (.funV G₁ :: π₁) a₁) (.ret (.funV G₂ :: π₂) a₂) := by
  cases r <;> rfl

theorem PR_mono {P : List Nat} {m r j k : Nat} {G₁ G₂ : CekValue} (hjk : j ≤ k)
    (h : PR Q P m r k G₁ G₂) : PR Q P m r j G₁ G₂ := by
  cases r with
  | zero => trivial
  | succ r =>
    rw [PR_succ] at h ⊢
    exact fun i hi => h i (Nat.le_trans hi hjk)

theorem ContOf_mono {P : List Nat} {m r j k : Nat} {π₁ π₂ : Stack} (hjk : j ≤ k)
    (h : ContOf Q P m r k π₁ π₂) : ContOf Q P m r j π₁ π₂ := by
  cases r with
  | zero => exact stackRel_mono hjk h
  | succ r => exact ⟨h.1, h.2.1, fun i hi => h.2.2 i (Nat.le_trans hi hjk)⟩

theorem ContOf_wf {P : List Nat} {m r j : Nat} {π₁ π₂ : Stack} (h : ContOf Q P m r j π₁ π₂) :
    StackWellFormed π₁ ∧ StackWellFormed π₂ := by
  cases r with
  | zero => exact ⟨h.1, h.2.1⟩
  | succ r => exact ⟨h.1, h.2.1⟩

/-! ## Environments -/

structure EnvOK (Q : ListFamily) (P : List Nat) (m : Nat) (k D F : Nat) (X Ls : List Nat) (ρ₁ ρ₂ : CekEnv) : Prop where
  other : ∀ n, 0 < n → n ≤ D → n ≠ F → n ∉ X →
    ∃ v₁ v₂, ρ₁.lookup n = some v₁ ∧ ρ₂.lookup n = some v₂ ∧ ValueRel wfGuard k v₁ v₂
  lists : ∀ i ∈ Ls, ∃ l, ρ₁.lookup i = some l ∧ ρ₂.lookup i = some l ∧ Q.mem l
  recursive : ∃ r₁ r₂, ρ₁.lookup F = some r₁ ∧ ρ₂.lookup F = some r₂ ∧ PR Q P m m k r₁ r₂ ∧
    ValueWellFormed r₁ ∧ ValueWellFormed r₂

theorem EnvOK.mono {P : List Nat} {m j k D F : Nat} {X Ls : List Nat} {ρ₁ ρ₂ : CekEnv}
    (hjk : j ≤ k) (h : EnvOK Q P m k D F X Ls ρ₁ ρ₂) : EnvOK Q P m j D F X Ls ρ₁ ρ₂ := by
  refine ⟨fun n hn hnd h₁ h₂ => ?_, h.lists, ?_⟩
  · obtain ⟨v₁, v₂, e₁, e₂, hv⟩ := h.other n hn hnd h₁ h₂
    exact ⟨v₁, v₂, e₁, e₂, valueRel_mono hjk hv⟩
  · obtain ⟨r₁, r₂, e₁, e₂, hr, w₁, w₂⟩ := h.recursive
    exact ⟨r₁, r₂, e₁, e₂, PR_mono hjk hr, w₁, w₂⟩

omit sv in
theorem lookup_extend_succ (ρ : CekEnv) (v : CekValue) (n : Nat) (hn : 0 < n) :
    (ρ.extend v).lookup (n + 1) = ρ.lookup n := by
  match n, hn with
  | m + 1, _ => rfl

omit sv in
theorem lookup_extend_one (ρ : CekEnv) (v : CekValue) : (ρ.extend v).lookup 1 = some v := rfl

omit sv in
theorem mem_shiftLs {n i : Nat} {Ls : List Nat} : i ∈ shiftLs n Ls ↔ ∃ j ∈ Ls, i = j + n := by
  simp only [shiftLs, List.mem_map]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩

omit sv in
theorem shiftLs_shiftLs (a b : Nat) (X : List Nat) : shiftLs a (shiftLs b X) = shiftLs (b + a) X := by
  simp only [shiftLs, List.map_map]
  congr 1; funext x; simp [Nat.add_assoc]

theorem EnvOK.lists_pos {P : List Nat} {m k D F : Nat} {X Ls : List Nat} {ρ₁ ρ₂ : CekEnv}
    (h : EnvOK Q P m k D F X Ls ρ₁ ρ₂) : ∀ i ∈ Ls, 0 < i := by
  intro i hi
  obtain ⟨l, h₁, _, _⟩ := h.lists i hi
  cases i with
  | zero => cases ρ₁ <;> simp [CekEnv.lookup] at h₁
  | succ i => omega

theorem EnvOK.extend {P : List Nat} {m k D F : Nat} {X Ls : List Nat} {ρ₁ ρ₂ : CekEnv}
    {w₁ w₂ : CekValue} (h : EnvOK Q P m k D F X Ls ρ₁ ρ₂) (hw : ValueRel wfGuard k w₁ w₂) :
    EnvOK Q P m k (D + 1) (F + 1) (shiftLs 1 X) (shiftLs 1 Ls) (ρ₁.extend w₁) (ρ₂.extend w₂) := by
  have hpos := h.lists_pos
  refine ⟨fun n hn hnd h₁ h₂ => ?_, fun i hi => ?_, ?_⟩
  · by_cases h1 : n = 1
    · subst h1; exact ⟨w₁, w₂, rfl, rfl, hw⟩
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [lookup_extend_succ _ _ _ (by omega), lookup_extend_succ _ _ _ (by omega)]
      exact h.other n' (by omega) (by omega) (by omega)
        (fun hx => h₂ (mem_shiftLs.mpr ⟨n', hx, rfl⟩))
  · obtain ⟨j, hj, rfl⟩ := mem_shiftLs.mp hi
    rw [lookup_extend_succ _ _ _ (hpos j hj), lookup_extend_succ _ _ _ (hpos j hj)]
    exact h.lists j hj
  · obtain ⟨r₁, r₂, e₁, e₂, hr, v₁, v₂⟩ := h.recursive
    have hF : 0 < F := by
      cases F with
      | zero => cases ρ₁ <;> simp [CekEnv.lookup] at e₁
      | succ F => omega
    rw [lookup_extend_succ _ _ _ hF, lookup_extend_succ _ _ _ hF]
    exact ⟨r₁, r₂, e₁, e₂, hr, v₁, v₂⟩

omit sv in
theorem listValue_vcon {v : CekValue} (h : ListValue v) : ∃ c, v = .VCon c := by
  cases v with
  | VCon c => exact ⟨c, rfl⟩
  | _ => exact absurd h id

theorem valueRel_list {k : Nat} {v : CekValue} (h : ListValue v) : ValueRel wfGuard k v v := by
  obtain ⟨c, rfl⟩ := listValue_vcon h
  exact valueRel_vcon k c

/-- Entering the alternative of a list `case` that binds the head and tail. -/
theorem EnvOK.extendCons {P : List Nat} {m k D F : Nat} {X Ls : List Nat} {ρ₁ ρ₂ : CekEnv}
    {h t : CekValue} (henv : EnvOK Q P m k D F X Ls ρ₁ ρ₂) (hh : ValueRel wfGuard k h h)
    (ht : Q.mem t) :
    EnvOK Q P m k (D + 2) (F + 2) (shiftLs 2 X) (1 :: shiftLs 2 Ls) ((ρ₁.extend h).extend t)
      ((ρ₂.extend h).extend t) := by
  have h₁ := henv.extend hh
  have htt : ValueRel wfGuard k t t := by
    obtain ⟨c, rfl⟩ := listValue_vcon (Q.list ht)
    exact valueRel_vcon k c
  have h₂ := h₁.extend htt
  rw [shiftLs_shiftLs] at h₂
  refine ⟨h₂.other, fun i hi => ?_, h₂.recursive⟩
  rcases List.mem_cons.mp hi with rfl | hi
  · exact ⟨t, rfl, rfl, ht⟩
  · apply h₂.lists
    obtain ⟨j, hj, rfl⟩ := mem_shiftLs.mp hi
    exact mem_shiftLs.mpr ⟨j + 1, mem_shiftLs.mpr ⟨j, hj, rfl⟩, by omega⟩

/-! ## List values under a `case` -/

/-- A `case` on a list either passes a head and a list tail to its first
    alternative or selects its second alternative. -/
theorem listCase_dispatch {v : CekValue} (hv : Q.mem v) :
    (∃ c tl, Q.mem tl ∧ ∀ (π : Stack) (ρ : CekEnv) (alts : List Term),
      step (.ret (.caseScrutinee alts ρ :: π) v) =
        if alts.length > 2 then .error else
          match alts[0]? with
          | some alt => .compute ([Frame.applyArg (.VCon c), Frame.applyArg tl] ++ π) ρ alt
          | none => .error) ∨
    (∀ (π : Stack) (ρ : CekEnv) (alts : List Term),
      step (.ret (.caseScrutinee alts ρ :: π) v) =
        if alts.length > 2 then .error else
          match alts[1]? with
          | some alt => .compute π ρ alt
          | none => .error) := by
  obtain ⟨c, rfl⟩ := listValue_vcon (Q.list hv)
  cases c with
  | ConstList ty l =>
    cases l with
    | nil =>
      refine .inr fun π ρ alts => ?_
      cases e : alts[1]? <;> simp [step, constToTagAndFields, e]
    | cons h t =>
      refine .inl ⟨h, .VCon (.ConstList ty t), Q.tail hv, fun π ρ alts => ?_⟩
      cases e : alts[0]? <;> simp [step, constToTagAndFields, e]
  | _ => exact absurd (Q.list hv) id

/-! ## Evaluation -/

/-- Applying a partial call to one more argument. -/
theorem apply_spine {P : List Nat} {m F r k D : Nat} {X Ls : List Nat} {ρ₁ ρ₂ : CekEnv} {f a : Term}
    (henv : EnvOK Q P m k D F X Ls ρ₁ ρ₂)
    (hf : ∀ j ≤ k, ∀ π₁ π₂, ContOf Q P m (r + 1) j π₁ π₂ →
      wfGuard.St (.compute π₁ ρ₁ f) → wfGuard.St (.compute π₂ ρ₂ f) →
      ObsRefinesK j (.compute π₁ ρ₁ f) (.compute π₂ ρ₂ f))
    (ha : Eval wfGuard k ρ₁ ρ₂ a a) (hok : ArgOK P Ls (m - (r + 1)) a) :
    ∀ j ≤ k, ∀ π₁ π₂, ContOf Q P m r j π₁ π₂ →
      wfGuard.St (.compute π₁ ρ₁ (.Apply f a)) → wfGuard.St (.compute π₂ ρ₂ (.Apply f a)) →
      ObsRefinesK j (.compute π₁ ρ₁ (.Apply f a)) (.compute π₂ ρ₂ (.Apply f a)) := by
  intro j hj π₁ π₂ hπ hst₁ hst₂
  match j with
  | 0 => exact obsRefinesK_zero_compute
  | j + 1 =>
  apply obsRefinesK_of_step_compute
  have hs₁ := wfGuard.step hst₁
  have hs₂ := wfGuard.step hst₂
  simp only [step] at hs₁ hs₂ ⊢
  refine hf j (by omega) _ _ ⟨wfGuard.compute hs₁, wfGuard.compute hs₂,
    fun j' hj' H₁ H₂ hH hH₁ hH₂ => ?_⟩ hs₁ hs₂
  match j' with
  | 0 => exact obsRefinesK_zero_ret
  | j' + 1 =>
  apply obsRefinesK_of_step_ret
  have ha₁ := wfGuard.step (wfGuard.ret.mpr ⟨wfGuard.compute hs₁, hH₁⟩)
  have ha₂ := wfGuard.step (wfGuard.ret.mpr ⟨wfGuard.compute hs₂, hH₂⟩)
  simp only [step] at ha₁ ha₂ ⊢
  have hπ' := ContOf_mono (show j' ≤ j + 1 by omega) hπ
  rw [PR_succ] at hH
  by_cases hp : m - (r + 1) ∈ P
  · obtain ⟨i, rfl, hi⟩ := hok hp
    obtain ⟨l, e₁, e₂, hl⟩ := henv.lists i hi
    obtain ⟨c, rfl⟩ := listValue_vcon (Q.list hl)
    refine obsRefinesK_of_steps_left (n := 1) (s₁' := .ret (.funV H₁ :: π₁) (.VCon c))
      (by simp [steps, step, e₁])
      (obsRefinesK_of_steps_right (n := 1) (s₂' := .ret (.funV H₂ :: π₂) (.VCon c))
        (by simp [steps, step, e₂]) ?_)
    exact hH j' (by omega) _ _ (valueRel_vcon j' c) (.vcon c) (.vcon c) (fun _ => hl) π₁ π₂ hπ'
  · refine ha j' (by omega) _ _ ⟨.cons (.funV hH₁) (ContOf_wf hπ').1,
      .cons (.funV hH₂) (ContOf_wf hπ').2, fun i hi a₁ a₂ hrel ha₁' ha₂' => ?_⟩ ha₁ ha₂
    exact hH i (by omega) a₁ a₂ hrel ha₁' ha₂' (fun h => absurd h hp) π₁ π₂
      (ContOf_mono (by omega) hπ')

mutual
  theorem calls_eval {P : List Nat} {m F : Nat} {X Ls : List Nat} {t : Term}
      (h : Calls P m F X Ls t) {k D : Nat} {ρ₁ ρ₂ : CekEnv} (ht : closedAt D t = true)
      (henv : EnvOK Q P m k D F X Ls ρ₁ ρ₂) : Eval wfGuard k ρ₁ ρ₂ t t := by
    match h with
    | .var (i := n) hF hS =>
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      simp only [step] at hst₁ hst₂ ⊢
      simp [closedAt] at ht
      by_cases hn : n = 0
      · subst hn
        cases ρ₁ <;> cases ρ₂ <;> exact obsRefinesK_error_error j
      · obtain ⟨v₁, v₂, e₁, e₂, hv⟩ := henv.other n (by omega) ht hF hS
        simp only [e₁, e₂] at hst₁ hst₂ ⊢
        exact ret_obs (valueRel_mono (by omega) hv) hst₁ hst₂ hπ
    | .constant =>
      exact eval_of_step fun j _ _ _ hπ hst₁ hst₂ => ret_obs (valueRel_vcon j _) hst₁ hst₂ hπ
    | .builtin =>
      exact eval_of_step fun j _ _ _ hπ hst₁ hst₂ =>
        ret_obs (valueRel_builtin (k := j) trivial) hst₁ hst₂ hπ
    | .error => exact eval_of_step fun j _ _ _ _ _ _ => obsRefinesK_error_error j
    | .lam hb =>
      simp only [closedAt] at ht
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      refine ret_obs (valueRel_lam (wfGuard.ret.mp hst₁).2 (wfGuard.ret.mp hst₂).2
        fun j' hj' a₁ a₂ ha _ _ => ?_) hst₁ hst₂ hπ
      exact calls_eval hb ht ((henv.mono (by omega)).extend ha)
    | .apply hf ha =>
      simp only [closedAt, Bool.and_eq_true] at ht
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      exact calls_eval hf ht.1 (henv.mono (by omega)) j (Nat.le_refl _) _ _
        (arg_stackRel (calls_eval ha ht.2 (henv.mono (by omega)))
          (wfGuard.compute hst₁) (wfGuard.compute hst₂) hπ) hst₁ hst₂
    | .call hs ha hok =>
      simp only [closedAt, Bool.and_eq_true] at ht
      intro j hj π₁ π₂ hπ hst₁ hst₂
      exact apply_spine henv (fun j hj π₁ π₂ hπ hst₁ hst₂ =>
          spine_eval hs (by omega) ht.1 henv j hj π₁ π₂ hπ hst₁ hst₂)
        (calls_eval ha ht.2 henv) hok j hj π₁ π₂ hπ hst₁ hst₂
    | .force ht' =>
      simp only [closedAt] at ht
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      exact calls_eval ht' ht (henv.mono (by omega)) j (Nat.le_refl _) _ _
        (force_stackRel hπ) hst₁ hst₂
    | .delay ht' =>
      simp only [closedAt] at ht
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      exact ret_obs (valueRel_delay (wfGuard.ret.mp hst₁).2 (wfGuard.ret.mp hst₂).2
        fun j' hj' => calls_eval ht' ht (henv.mono (by omega))) hst₁ hst₂ hπ
    | .constr .nil =>
      exact eval_of_step fun j _ _ _ hπ hst₁ hst₂ =>
        ret_obs (valueRel_constr (k := j) trivial) hst₁ hst₂ hπ
    | .constr (.cons hm hms) =>
      simp only [closedAt, closedAtList, Bool.and_eq_true] at ht
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      exact calls_eval hm ht.1 (henv.mono (by omega)) j (Nat.le_refl _) _ _
        (constrField_stackRel (callsList_eval hms ht.2 (henv.mono (by omega)))
          trivial (wfGuard.compute hst₁) (wfGuard.compute hst₂) hπ) hst₁ hst₂
    | .case hs has =>
      simp only [closedAt, Bool.and_eq_true] at ht
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      exact calls_eval hs ht.1 (henv.mono (by omega)) j (Nat.le_refl _) _ _
        (case_stackRel (altsRel_of_listRel (callsList_eval has ht.2 (henv.mono (by omega))))
          (wfGuard.compute hst₁) (wfGuard.compute hst₂) hπ) hst₁ hst₂
    | .listCase (z := z) (C := C) (rest := rest) hz hC hrest =>
      simp only [closedAt, closedAtList, Bool.and_eq_true] at ht
      obtain ⟨_, ⟨htC, htrest⟩⟩ := ht
      have htC' : closedAt (D + 2) C = true := by simpa [Nat.add_assoc] using htC
      obtain ⟨l, e₁, e₂, hl⟩ := henv.lists z hz
      refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
      simp only [step] at hst₁ hst₂ ⊢
      match j with
      | 0 => exact obsRefinesK_zero_compute
      | j + 1 =>
      apply obsRefinesK_of_step_compute
      have hs₁ := wfGuard.step hst₁
      have hs₂ := wfGuard.step hst₂
      simp only [step, e₁, e₂] at hs₁ hs₂ ⊢
      match j with
      | 0 => exact obsRefinesK_zero_ret
      | j + 1 =>
      apply obsRefinesK_of_step_ret
      have hd₁ := wfGuard.step hs₁
      have hd₂ := wfGuard.step hs₂
      rcases listCase_dispatch hl with ⟨c, tl, htl, hdisp⟩ | hdisp
      · simp only [hdisp] at hd₁ hd₂ ⊢
        split
        · exact obsRefinesK_error_error j
        · rename_i hlen
          simp only [hlen, if_false, List.getElem?_cons_zero] at hd₁ hd₂
          simp only [List.getElem?_cons_zero]
          match j with
          | 0 => exact obsRefinesK_zero_compute
          | j + 1 =>
          apply obsRefinesK_of_step_compute
          have hc₁ := wfGuard.step hd₁
          have hc₂ := wfGuard.step hd₂
          simp only [step, List.cons_append, List.nil_append] at hc₁ hc₂ ⊢
          refine obsRefinesK_of_steps_left (n := 3) rfl
            (obsRefinesK_of_steps_right (n := 3) rfl ?_)
          have hb₁ : wfGuard.St (.compute π₁ ((ρ₁.extend (.VCon c)).extend tl) C) := by
            have := wfGuard.step (wfGuard.step (wfGuard.step hc₁))
            simpa [step] using this
          have hb₂ : wfGuard.St (.compute π₂ ((ρ₂.extend (.VCon c)).extend tl) C) := by
            have := wfGuard.step (wfGuard.step (wfGuard.step hc₂))
            simpa [step] using this
          exact calls_eval hC htC' ((henv.mono (by omega)).extendCons (valueRel_vcon j c) htl)
            j (Nat.le_refl _) π₁ π₂ (stackRel_mono (by omega) hπ) hb₁ hb₂
      · simp only [hdisp] at hd₁ hd₂ ⊢
        split
        · exact obsRefinesK_error_error j
        · rename_i hlen
          simp only [hlen, if_false, List.getElem?_cons_succ] at hd₁ hd₂
          simp only [List.getElem?_cons_succ]
          match hrest with
          | .nil => exact obsRefinesK_error_error j
          | .cons halt _ =>
            simp only [closedAtList, Bool.and_eq_true] at htrest
            simp only [List.getElem?_cons_zero] at hd₁ hd₂ ⊢
            exact calls_eval halt htrest.1 (henv.mono (by omega)) j (Nat.le_refl _) π₁ π₂
              (stackRel_mono (by omega) hπ) hd₁ hd₂

  theorem spine_eval {P : List Nat} {m F r : Nat} {X Ls : List Nat} {t : Term}
      (h : Spine P m F X Ls r t) (hr : 0 < r) {k D : Nat} {ρ₁ ρ₂ : CekEnv}
      (ht : closedAt D t = true) (henv : EnvOK Q P m k D F X Ls ρ₁ ρ₂) :
      ∀ j ≤ k, ∀ π₁ π₂, ContOf Q P m r j π₁ π₂ →
        wfGuard.St (.compute π₁ ρ₁ t) → wfGuard.St (.compute π₂ ρ₂ t) →
        ObsRefinesK j (.compute π₁ ρ₁ t) (.compute π₂ ρ₂ t) := by
    match h with
    | .head =>
      intro j hj π₁ π₂ hπ hst₁ hst₂
      obtain ⟨r₁, r₂, e₁, e₂, hrec, w₁, w₂⟩ := henv.recursive
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      match j with
      | 0 => exact obsRefinesK_zero_compute
      | j + 1 =>
      apply obsRefinesK_of_step_compute
      simp only [step, e₁, e₂]
      exact hπ.2.2 j (by omega) r₁ r₂ (PR_mono (by omega) hrec) w₁ w₂
    | .arg hs ha hok =>
      simp only [closedAt, Bool.and_eq_true] at ht
      exact apply_spine henv (fun j hj π₁ π₂ hπ hst₁ hst₂ =>
          spine_eval hs (by omega) ht.1 henv j hj π₁ π₂ hπ hst₁ hst₂)
        (calls_eval ha ht.2 henv) hok

  theorem callsList_eval {P : List Nat} {m F : Nat} {X Ls : List Nat} {ts : List Term}
      (h : CallsList P m F X Ls ts) {k D : Nat} {ρ₁ ρ₂ : CekEnv} (hts : closedAtList D ts = true)
      (henv : EnvOK Q P m k D F X Ls ρ₁ ρ₂) : ListRel (Eval wfGuard k ρ₁ ρ₂) ts ts := by
    match h with
    | .nil => exact trivial
    | .cons ht hts' =>
      simp only [closedAtList, Bool.and_eq_true] at hts
      exact ⟨calls_eval ht hts.1 henv, callsList_eval hts' hts.2 henv⟩
end

end Moist.Verified.KnownLists
