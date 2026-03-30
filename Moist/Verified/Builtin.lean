import Moist.Verified.ClosedAt
import Moist.CEK.Builtins

/-! # Per-builtin `ValueRelV` preservation lemmas

Each pass-through builtin gets its own `relV` lemma proving that
`ListValueRelV`-related argument lists produce `ValueRelV`-related
results (or both fail). The shared `valueRelV_vcon_or_not` helper
collapses the `ValueRelV` case split on condition arguments.

The main `evalBuiltin_passThrough_relV` theorem dispatches to these
per-builtin lemmas. -/

set_option linter.unusedSimpArgs false

namespace Moist.Verified.Builtin

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified.Semantics
open Moist.Verified

/-- Either both sides are the same `VCon`, or neither side is `VCon`. -/
theorem valueRelV_vcon_or_not (h : ValueRelV v₁ v₂) :
    (∃ c, v₁ = .VCon c ∧ v₂ = .VCon c) ∨ ((∀ c, v₁ ≠ .VCon c) ∧ (∀ c, v₂ ≠ .VCon c)) := by
  cases h with
  | vcon => exact .inl ⟨_, rfl, rfl⟩
  | refl =>
    cases v₁ with
    | VCon c => exact .inl ⟨c, rfl, rfl⟩
    | VLam _ _ => exact .inr ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
    | VDelay _ _ => exact .inr ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
    | VConstr _ _ => exact .inr ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
    | VBuiltin _ _ _ => exact .inr ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  | vlam _ _ _ _ => exact .inr ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  | vdelay _ _ _ _ => exact .inr ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  | vconstr _ _ => exact .inr ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  | vbuiltin _ _ _ => exact .inr ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩

/-- If `ValueRelV v₁ v₂` and `v₁ = VCon c`, then `v₂ = VCon c`. -/
private theorem valueRelV_vcon (h : ValueRelV v₁ v₂) (hv : v₁ = .VCon c) : v₂ = .VCon c := by
  subst hv; cases h with | vcon => rfl | refl => rfl

private theorem valueRelV_vcon_right (h : ValueRelV v₁ v₂) (hv : v₂ = .VCon c) : v₁ = .VCon c := by
  subst hv; cases h with | vcon => rfl | refl => rfl

/-- `ListValueRelV` where all elements are `VCon` implies the lists are equal. -/
private theorem listValueRelV_vcon_eq (h : ListValueRelV args₁ args₂)
    (hall : ∀ v ∈ args₁, ∃ c, v = .VCon c) : args₁ = args₂ := by
  cases h with
  | nil => rfl
  | cons hv hr =>
    have ⟨c, hc⟩ := hall _ (.head _)
    have := valueRelV_vcon hv hc
    subst hc; subst this
    congr 1
    exact listValueRelV_vcon_eq hr fun v hm => hall v (.tail _ hm)

private theorem evalBPT_MkCons_some {v₁ v₂ w : CekValue}
    (h : evalBuiltinPassThrough .MkCons [v₁, v₂] = some w) :
    (∃ c, v₁ = .VCon c) ∧ (∃ c, v₂ = .VCon c) := by
  cases v₁ with
  | VCon c1 =>
    refine ⟨⟨c1, rfl⟩, ?_⟩
    cases v₂ with
    | VCon c2 => exact ⟨c2, rfl⟩
    | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
      cases c1 <;> simp [evalBuiltinPassThrough] at h
  | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
    simp [evalBuiltinPassThrough] at h

/-! ### Per-builtin lemmas -/

private theorem ifThenElse_relV (args₁ args₂ : List CekValue)
    (hargs : ListValueRelV args₁ args₂) (h_ne : args₁ ≠ args₂) :
    match evalBuiltinPassThrough .IfThenElse args₁, evalBuiltinPassThrough .IfThenElse args₂ with
    | some v₁, some v₂ => ValueRelV v₁ v₂
    | none, none => True
    | _, _ => False := by
  cases hargs with
  | nil => exact absurd rfl h_ne
  | cons hv1 hr1 => cases hr1 with
    | nil => simp [evalBuiltinPassThrough]
    | cons hv2 hr2 => cases hr2 with
      | nil => simp [evalBuiltinPassThrough]
      | cons hv3 hr3 => cases hr3 with
        | cons _ _ => simp [evalBuiltinPassThrough]
        | nil =>
          rcases valueRelV_vcon_or_not hv3 with ⟨c, rfl, rfl⟩ | ⟨hne1, hne2⟩
          · cases c <;> simp [evalBuiltinPassThrough]
            rename_i cond; cases cond <;> simp [evalBuiltinPassThrough]
            · exact hv1
            · exact hv2
          · suffices ∀ a b (v : CekValue), (∀ c, v ≠ .VCon c) →
                evalBuiltinPassThrough .IfThenElse [a, b, v] = none by
              rw [this _ _ _ hne1, this _ _ _ hne2]; trivial
            intro a b v hv
            cases v with
            | VCon c => exact absurd rfl (hv c)
            | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => rfl

private theorem chooseUnit_relV (args₁ args₂ : List CekValue)
    (hargs : ListValueRelV args₁ args₂) (h_ne : args₁ ≠ args₂) :
    match evalBuiltinPassThrough .ChooseUnit args₁, evalBuiltinPassThrough .ChooseUnit args₂ with
    | some v₁, some v₂ => ValueRelV v₁ v₂
    | none, none => True
    | _, _ => False := by
  cases hargs with
  | nil => exact absurd rfl h_ne
  | cons hv1 hr1 => cases hr1 with
    | nil => simp [evalBuiltinPassThrough]
    | cons hv2 hr2 => cases hr2 with
      | cons _ _ => simp [evalBuiltinPassThrough]
      | nil =>
        rcases valueRelV_vcon_or_not hv2 with ⟨c, rfl, rfl⟩ | ⟨hne1, hne2⟩
        · cases c <;> simp [evalBuiltinPassThrough]
          exact hv1
        · suffices ∀ a (v : CekValue), (∀ c, v ≠ .VCon c) →
              evalBuiltinPassThrough .ChooseUnit [a, v] = none by
            rw [this _ _ hne1, this _ _ hne2]; trivial
          intro a v hv
          cases v with
          | VCon c => exact absurd rfl (hv c)
          | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => rfl

private theorem trace_relV (args₁ args₂ : List CekValue)
    (hargs : ListValueRelV args₁ args₂) (h_ne : args₁ ≠ args₂) :
    match evalBuiltinPassThrough .Trace args₁, evalBuiltinPassThrough .Trace args₂ with
    | some v₁, some v₂ => ValueRelV v₁ v₂
    | none, none => True
    | _, _ => False := by
  cases hargs with
  | nil => exact absurd rfl h_ne
  | cons hv1 hr1 => cases hr1 with
    | nil => simp [evalBuiltinPassThrough]
    | cons hv2 hr2 => cases hr2 with
      | cons _ _ => simp [evalBuiltinPassThrough]
      | nil =>
        rcases valueRelV_vcon_or_not hv2 with ⟨c, rfl, rfl⟩ | ⟨hne1, hne2⟩
        · cases c <;> simp [evalBuiltinPassThrough]
          exact hv1
        · suffices ∀ a (v : CekValue), (∀ c, v ≠ .VCon c) →
              evalBuiltinPassThrough .Trace [a, v] = none by
            rw [this _ _ hne1, this _ _ hne2]; trivial
          intro a v hv
          cases v with
          | VCon c => exact absurd rfl (hv c)
          | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => rfl

private theorem chooseData_relV (args₁ args₂ : List CekValue)
    (hargs : ListValueRelV args₁ args₂) (h_ne : args₁ ≠ args₂) :
    match evalBuiltinPassThrough .ChooseData args₁, evalBuiltinPassThrough .ChooseData args₂ with
    | some v₁, some v₂ => ValueRelV v₁ v₂
    | none, none => True
    | _, _ => False := by
  cases hargs with
  | nil => exact absurd rfl h_ne
  | cons hv1 hr1 => cases hr1 with
    | nil => simp [evalBuiltinPassThrough]
    | cons hv2 hr2 => cases hr2 with
      | nil => simp [evalBuiltinPassThrough]
      | cons hv3 hr3 => cases hr3 with
        | nil => simp [evalBuiltinPassThrough]
        | cons hv4 hr4 => cases hr4 with
          | nil => simp [evalBuiltinPassThrough]
          | cons hv5 hr5 => cases hr5 with
            | nil => simp [evalBuiltinPassThrough]
            | cons hv6 hr6 => cases hr6 with
              | cons _ _ => simp [evalBuiltinPassThrough]
              | nil =>
                rcases valueRelV_vcon_or_not hv6 with ⟨c, rfl, rfl⟩ | ⟨hne1, hne2⟩
                · cases c <;> simp [evalBuiltinPassThrough]
                  rename_i d; cases d <;> simp [evalBuiltinPassThrough]
                  · exact hv5
                  · exact hv4
                  · exact hv3
                  · exact hv2
                  · exact hv1
                · suffices ∀ a b c d e (v : CekValue), (∀ k, v ≠ .VCon k) →
                      evalBuiltinPassThrough .ChooseData [a, b, c, d, e, v] = none by
                    rw [this _ _ _ _ _ _ hne1, this _ _ _ _ _ _ hne2]; trivial
                  intro a b c d e v hv
                  cases v with
                  | VCon k => exact absurd rfl (hv k)
                  | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => rfl

private theorem chooseList_relV (args₁ args₂ : List CekValue)
    (hargs : ListValueRelV args₁ args₂) (h_ne : args₁ ≠ args₂) :
    match evalBuiltinPassThrough .ChooseList args₁, evalBuiltinPassThrough .ChooseList args₂ with
    | some v₁, some v₂ => ValueRelV v₁ v₂
    | none, none => True
    | _, _ => False := by
  cases hargs with
  | nil => exact absurd rfl h_ne
  | cons hv1 hr1 => cases hr1 with
    | nil => simp [evalBuiltinPassThrough]
    | cons hv2 hr2 => cases hr2 with
      | nil => simp [evalBuiltinPassThrough]
      | cons hv3 hr3 => cases hr3 with
        | cons _ _ => simp [evalBuiltinPassThrough]
        | nil =>
          rcases valueRelV_vcon_or_not hv3 with ⟨c, rfl, rfl⟩ | ⟨hne1, hne2⟩
          · cases c <;> simp [evalBuiltinPassThrough]
            · rename_i l; cases h : l.isEmpty <;> simp [evalBuiltinPassThrough, h]
              · exact hv1
              · exact hv2
            · rename_i l; cases h : l.isEmpty <;> simp [evalBuiltinPassThrough, h]
              · exact hv1
              · exact hv2
          · suffices ∀ a b (v : CekValue), (∀ c, v ≠ .VCon c) →
                evalBuiltinPassThrough .ChooseList [a, b, v] = none by
              rw [this _ _ _ hne1, this _ _ _ hne2]; trivial
            intro a b v hv
            cases v with
            | VCon c => exact absurd rfl (hv c)
            | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => rfl

private theorem mkCons_relV (args₁ args₂ : List CekValue)
    (hargs : ListValueRelV args₁ args₂) (h_ne : args₁ ≠ args₂) :
    match evalBuiltinPassThrough .MkCons args₁, evalBuiltinPassThrough .MkCons args₂ with
    | some v₁, some v₂ => ValueRelV v₁ v₂
    | none, none => True
    | _, _ => False := by
  -- MkCons: if either side returns some, all args are VCon → args equal → contradiction.
  cases hargs with
  | nil => exact absurd rfl h_ne
  | cons hv1 hr1 => cases hr1 with
    | nil => simp [evalBuiltinPassThrough]
    | cons hv2 hr2 => cases hr2 with
      | cons _ _ => simp [evalBuiltinPassThrough]
      | nil =>
        generalize h1 : evalBuiltinPassThrough .MkCons _ = r1
        generalize h2 : evalBuiltinPassThrough .MkCons _ = r2
        cases r1 with
        | some w1 =>
          have ⟨⟨c0, hc0⟩, ⟨c1, hc1⟩⟩ := evalBPT_MkCons_some h1
          subst hc0; subst hc1
          exact absurd (listValueRelV_vcon_eq (.cons hv1 (.cons hv2 .nil))
            (fun v hm => by
              simp [List.mem_cons] at hm
              rcases hm with rfl | rfl
              · exact ⟨c0, rfl⟩
              · exact ⟨c1, rfl⟩)) h_ne
        | none => cases r2 with
          | some w2 =>
            have ⟨⟨c0, hc0⟩, ⟨c1, hc1⟩⟩ := evalBPT_MkCons_some h2
            subst hc0; subst hc1
            have h1vcon := valueRelV_vcon_right hv1 rfl
            have h2vcon := valueRelV_vcon_right hv2 rfl
            subst h1vcon; subst h2vcon
            exact absurd rfl h_ne
          | none => trivial

/-! ### Composed theorem -/

/-- Pass-through builtins preserve `ValueRelV`. If both sides return
    `some`, the results are `ValueRelV`-related. If one returns `none`,
    both do. Dispatches to per-builtin lemmas. -/
theorem evalBuiltin_passThrough_relV (b : BuiltinFun) (args₁ args₂ : List CekValue)
    (hargs : ListValueRelV args₁ args₂) :
    match evalBuiltinPassThrough b args₁, evalBuiltinPassThrough b args₂ with
    | some v₁, some v₂ => ValueRelV v₁ v₂
    | none, none => True
    | _, _ => False := by
  by_cases h_eq : args₁ = args₂
  · subst h_eq
    cases evalBuiltinPassThrough b args₁ with
    | some v => exact .refl
    | none => trivial
  · by_cases hb : b = .IfThenElse ∨ b = .ChooseUnit ∨ b = .Trace ∨
                   b = .ChooseData ∨ b = .ChooseList ∨ b = .MkCons
    · rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ifThenElse_relV _ _ hargs h_eq
      · exact chooseUnit_relV _ _ hargs h_eq
      · exact trace_relV _ _ hargs h_eq
      · exact chooseData_relV _ _ hargs h_eq
      · exact chooseList_relV _ _ hargs h_eq
      · exact mkCons_relV _ _ hargs h_eq
    · have hb_not : b ≠ .IfThenElse ∧ b ≠ .ChooseUnit ∧ b ≠ .Trace ∧
                     b ≠ .ChooseData ∧ b ≠ .ChooseList ∧ b ≠ .MkCons :=
        ⟨fun h => hb (h ▸ .inl rfl), fun h => hb (h ▸ .inr (.inl rfl)),
         fun h => hb (h ▸ .inr (.inr (.inl rfl))),
         fun h => hb (h ▸ .inr (.inr (.inr (.inl rfl)))),
         fun h => hb (h ▸ .inr (.inr (.inr (.inr (.inl rfl))))),
         fun h => hb (h ▸ .inr (.inr (.inr (.inr (.inr rfl)))))⟩
      rw [evalBuiltinPassThrough_none_of_not_passthrough b args₁ hb_not,
          evalBuiltinPassThrough_none_of_not_passthrough b args₂ hb_not]; trivial

end Moist.Verified.Builtin
