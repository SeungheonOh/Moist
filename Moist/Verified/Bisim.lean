import Moist.Verified.ClosedAt
import Moist.CEK.Builtins

set_option linter.unusedSimpArgs false

namespace Moist.Verified.Bisim

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified.Semantics
open Moist.Verified
open Moist.Verified (renameTerm renameTermList liftRename liftRename_id renameTerm_id renameTermList_id renameTermList_length renameTermList_getElem)

/-! # CEK State Bisimulation

This module proves the central invariant: **`StateRel` is preserved by `step`**.

`step_preserves` is a single-step simulation theorem. Given
`StateRel s₁ s₂`, it shows `StateRel (step s₁) (step s₂)`. By iterating
this (`steps_preserves`), we get that `StateRel`-related states remain
related after any number of steps.

The main extraction theorems are:

- `bisim_reaches`: if `StateRel s₁ s₂` and both reach `halt`, the halted
  values are `ValueRelV`-related.
- `bisim_reaches_error`: if `StateRel s₁ s₂` and `s₁` reaches `error`,
  then `s₂` also reaches `error`.

The proof of `step_preserves` is a large case analysis — every combination
of `StateRel` constructor × term/frame variant must be handled. The most
intricate cases are builtins, where `evalBuiltin_relV` shows that
`ListValueRelV`-related argument lists produce `ValueRelV`-related results
(or both fail). This relies on the two-stage decomposition of `evalBuiltin`
into pass-through builtins and constant-extracting builtins.
-/

/-! ## Helper lemmas -/

private theorem lookup_zero (env : CekEnv) : env.lookup 0 = none := by
  cases env <;> simp [CekEnv.lookup]

/-- `ListValueRelV` is compatible with list append. -/
theorem listValueRelV_append (ha : ListValueRelV a₁ a₂) (hb : ListValueRelV b₁ b₂) :
    ListValueRelV (a₁ ++ b₁) (a₂ ++ b₂) := by
  cases ha with
  | nil => exact hb
  | cons hv hr => exact .cons hv (listValueRelV_append hr hb)

/-- `ListValueRelV` is compatible with list reverse. Used in the
    `constrField` frame case, where fields are accumulated in reverse. -/
theorem listValueRelV_reverse (h : ListValueRelV a₁ a₂) :
    ListValueRelV a₁.reverse a₂.reverse := by
  cases h with
  | nil => exact .nil
  | cons hv hr =>
    simp [List.reverse_cons]
    exact listValueRelV_append (listValueRelV_reverse hr) (.cons hv .nil)

theorem listValueRelV_cons_rev (hv : ValueRelV v₁ v₂)
    (hdone : ListValueRelV done₁ done₂) :
    ListValueRelV ((v₁ :: done₁).reverse) ((v₂ :: done₂).reverse) := by
  simp [List.reverse_cons]
  exact listValueRelV_append (listValueRelV_reverse hdone) (.cons hv .nil)

/-- `StackRel` is compatible with stack append. Used for `Case` and `Constr`
    frames that push multiple `applyArg` frames onto the stack at once. -/
theorem stackRel_append (hs : StackRel s₁ s₂) (ht : StackRel t1 t2) :
    StackRel (s₁ ++ t1) (s₂ ++ t2) := by
  cases hs with
  | nil => exact ht
  | cons hf hr => exact .cons hf (stackRel_append hr ht)

theorem listValueRelV_map_applyArg_stackRel (hfs : ListValueRelV fs₁ fs₂) :
    StackRel (fs₁.map Frame.applyArg) (fs₂.map Frame.applyArg) := by
  cases hfs with
  | nil => exact .nil
  | cons hv hr => exact .cons (.applyArg hv) (listValueRelV_map_applyArg_stackRel hr)

theorem listValueRelV_refl (vs : List CekValue) : ListValueRelV vs vs := by
  induction vs with
  | nil => exact .nil
  | cons v rest ih => exact .cons .refl ih

/-! ## evalBuiltin preservation

Builtins are the hardest part of the bisimulation because `evalBuiltin`
inspects values structurally. The approach is two-stage:

1. **Pass-through builtins** (`IfThenElse`, `ChooseUnit`, `Trace`,
   `ChooseData`, `ChooseList`, `MkCons`) select one of their arguments
   based on a condition value. If the condition is a `VCon` (which
   `ValueRelV` guarantees is identical on both sides), the same argument
   is selected. Since arguments are `ValueRelV`-related, the result is too.

2. **Constant builtins** (everything else) first extract all `VCon`
   payloads via `extractConsts`. `ListValueRelV` ensures the extracted
   constant lists are identical (since `ValueRelV` preserves `VCon`
   projection). Then `evalBuiltinConst` is a pure function on constants,
   so identical inputs produce identical outputs.

`evalBuiltin_relV` combines both stages. -/

theorem valueRelV_vcon_eq (h : ValueRelV v₁ v₂) (heq : v₁ = .VCon c) : v₂ = .VCon c := by
  subst heq; cases h with | vcon => rfl | refl => rfl

/-- If ValueRelV v₁ v₂ and v₁ = VCon c, then v₂ = VCon c. -/
private theorem valueRelV_vcon (h : ValueRelV v₁ v₂) (hv : v₁ = .VCon c) : v₂ = .VCon c := by
  subst hv; cases h with | vcon => rfl | refl => rfl

private theorem valueRelV_vcon_right (h : ValueRelV v₁ v₂) (hv : v₂ = .VCon c) : v₁ = .VCon c := by
  subst hv; cases h with | vcon => rfl | refl => rfl

/-- VCon projection: extracts the Const if VCon, otherwise none. -/
private def vconProj : CekValue → Option Const
  | .VCon c => some c
  | _ => none

/-- ValueRelV preserves VCon projection. -/
private theorem valueRelV_vconProj (h : ValueRelV v₁ v₂) : vconProj v₁ = vconProj v₂ := by
  cases h with
  | vcon => rfl
  | refl => rfl
  | vlam => rfl
  | vdelay => rfl
  | vconstr => rfl
  | vbuiltin => rfl

/-- ListValueRelV preserves the VCon skeleton (map of vconProj). -/
private theorem listValueRelV_vconSkel (h : ListValueRelV args₁ args₂) :
    args₁.map vconProj = args₂.map vconProj := by
  cases h with
  | nil => rfl
  | cons hv hr =>
    simp [List.map]
    exact ⟨valueRelV_vconProj hv, listValueRelV_vconSkel hr⟩


/-- ListValueRelV where all elements are VCon implies the lists are equal. -/
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

/-! ## Two-stage builtin bisimulation lemmas -/

theorem evalBuiltinConst_eq (b : BuiltinFun) (cs : List Const) :
    evalBuiltinConst b cs = evalBuiltinConst b cs := rfl

private theorem listValueRelV_length (h : ListValueRelV args₁ args₂) :
    args₁.length = args₂.length := by
  cases h with
  | nil => rfl
  | cons _ hr => simp [List.length_cons, listValueRelV_length hr]

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

/-- Pass-through builtins preserve `ValueRelV`. If both sides return
    `some`, the results are `ValueRelV`-related. If one returns `none`,
    both do. The proof exhaustively matches on argument list length and
    builtin identity (6 pass-through builtins × up to 6 args). -/
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
  · -- args1 ≠ args2 but ListValueRelV args1 args2.
    -- Split on whether b is one of the 6 pass-through builtins.
    by_cases hb : b = .IfThenElse ∨ b = .ChooseUnit ∨ b = .Trace ∨
                   b = .ChooseData ∨ b = .ChooseList ∨ b = .MkCons
    · -- Destructure list to determine length, then handle each pass-through builtin.
      cases hargs with
      | nil => exact absurd rfl h_eq
      | cons hv1 hr1 => cases hr1 with
        | nil => -- length 1: no pass-through pattern matches length 1
          rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [evalBuiltinPassThrough]
        | cons hv2 hr2 => cases hr2 with
          | nil => -- length 2: ChooseUnit [result, VCon Unit],
                   --           Trace [result, VCon (String _)],
                   --           MkCons [VCon (ConstList tail), elem]
            rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
            -- IfThenElse (length 3): no match
            · simp [evalBuiltinPassThrough]
            -- ChooseUnit [result, VCon Unit]: condition at pos 1
            · cases hv2 with
              | vcon =>
                cases ‹Const› <;> simp [evalBuiltinPassThrough]
                exact hv1
              | refl =>
                rename_i v_cond
                cases v_cond with
                | VCon c => cases c <;> simp [evalBuiltinPassThrough]; exact hv1
                | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
                  simp [evalBuiltinPassThrough]
              | vlam _ _ _ | vdelay _ _ _ | vconstr _ _ | vbuiltin _ _ _ =>
                simp [evalBuiltinPassThrough]
            -- Trace [result, VCon (String _)]: condition at pos 1
            · cases hv2 with
              | vcon =>
                cases ‹Const› <;> simp [evalBuiltinPassThrough]
                exact hv1
              | refl =>
                rename_i v_cond
                cases v_cond with
                | VCon c => cases c <;> simp [evalBuiltinPassThrough]; exact hv1
                | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
                  simp [evalBuiltinPassThrough]
              | vlam _ _ _ | vdelay _ _ _ | vconstr _ _ | vbuiltin _ _ _ =>
                simp [evalBuiltinPassThrough]
            -- ChooseData (length 6): no match
            · simp [evalBuiltinPassThrough]
            -- ChooseList (length 3): no match
            · simp [evalBuiltinPassThrough]
            -- MkCons: if either side returns some, all args are VCon → args equal → contradiction.
            · generalize h1 : evalBuiltinPassThrough .MkCons _ = r1
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
                    · exact ⟨c1, rfl⟩)) h_eq
              | none => cases r2 with
                | some w2 =>
                  have ⟨⟨c0, hc0⟩, ⟨c1, hc1⟩⟩ := evalBPT_MkCons_some h2
                  subst hc0; subst hc1
                  -- args2 all VCon; show args1 also all VCon via ValueRelV
                  have h1vcon := valueRelV_vcon_right hv1 rfl
                  have h2vcon := valueRelV_vcon_right hv2 rfl
                  subst h1vcon; subst h2vcon
                  exact absurd rfl h_eq
                | none => trivial
          | cons hv3 hr3 => cases hr3 with
            | nil => -- length 3: IfThenElse [elseV, thenV, VCon (Bool cond)],
                     --           ChooseList [consCase, nilCase, VCon (ConstDataList/ConstList l)]
              rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
              -- IfThenElse: condition at pos 2
              · cases hv3 with
                | vcon =>
                  cases ‹Const› <;> simp [evalBuiltinPassThrough]
                  rename_i cond; cases cond <;> simp [evalBuiltinPassThrough]
                  · exact hv1
                  · exact hv2
                | refl =>
                  rename_i v_cond
                  cases v_cond with
                  | VCon c =>
                    cases c <;> simp [evalBuiltinPassThrough]
                    rename_i cond; cases cond <;> simp [evalBuiltinPassThrough]
                    · exact hv1
                    · exact hv2
                  | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
                    simp [evalBuiltinPassThrough]
                | vlam _ _ _ | vdelay _ _ _ | vconstr _ _ | vbuiltin _ _ _ =>
                  simp [evalBuiltinPassThrough]
              -- ChooseUnit (length 2): no match
              · simp [evalBuiltinPassThrough]
              -- Trace (length 2): no match
              · simp [evalBuiltinPassThrough]
              -- ChooseData (length 6): no match
              · simp [evalBuiltinPassThrough]
              -- ChooseList: condition at pos 2
              · cases hv3 with
                | vcon =>
                  cases ‹Const› <;> simp [evalBuiltinPassThrough]
                  · rename_i l; cases h : l.isEmpty <;> simp [evalBuiltinPassThrough, h]
                    · exact hv1
                    · exact hv2
                  · rename_i l; cases h : l.isEmpty <;> simp [evalBuiltinPassThrough, h]
                    · exact hv1
                    · exact hv2
                | refl =>
                  rename_i v_cond
                  cases v_cond with
                  | VCon c =>
                    cases c <;> simp [evalBuiltinPassThrough]
                    · rename_i l; cases h : l.isEmpty <;> simp [evalBuiltinPassThrough, h]
                      · exact hv1
                      · exact hv2
                    · rename_i l; cases h : l.isEmpty <;> simp [evalBuiltinPassThrough, h]
                      · exact hv1
                      · exact hv2
                  | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
                    simp [evalBuiltinPassThrough]
                | vlam _ _ _ | vdelay _ _ _ | vconstr _ _ | vbuiltin _ _ _ =>
                  simp [evalBuiltinPassThrough]
              -- MkCons (length 2): no match
              · simp [evalBuiltinPassThrough]
            | cons hv4 hr4 => cases hr4 with
              | nil => -- length 4: no pass-through pattern
                rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [evalBuiltinPassThrough]
              | cons hv5 hr5 => cases hr5 with
                | nil => -- length 5: no pass-through pattern
                  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [evalBuiltinPassThrough]
                | cons hv6 hr6 => cases hr6 with
                  | nil => -- length 6: ChooseData
                    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
                    -- IfThenElse (length 3): no match
                    · simp [evalBuiltinPassThrough]
                    -- ChooseUnit (length 2): no match
                    · simp [evalBuiltinPassThrough]
                    -- Trace (length 2): no match
                    · simp [evalBuiltinPassThrough]
                    -- ChooseData: condition at pos 5
                    · cases hv6 with
                      | vcon =>
                        cases ‹Const› <;> simp [evalBuiltinPassThrough]
                        -- Data case: returns based on Data variant
                        rename_i d; cases d <;> simp [evalBuiltinPassThrough]
                        · exact hv5
                        · exact hv4
                        · exact hv3
                        · exact hv2
                        · exact hv1
                      | refl =>
                        rename_i v_cond
                        cases v_cond with
                        | VCon c =>
                          cases c <;> simp [evalBuiltinPassThrough]
                          rename_i d; cases d <;> simp [evalBuiltinPassThrough]
                          · exact hv5
                          · exact hv4
                          · exact hv3
                          · exact hv2
                          · exact hv1
                        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
                          simp [evalBuiltinPassThrough]
                      | vlam _ _ _ | vdelay _ _ _ | vconstr _ _ | vbuiltin _ _ _ =>
                        simp [evalBuiltinPassThrough]
                    -- ChooseList (length 3): no match
                    · simp [evalBuiltinPassThrough]
                    -- MkCons (length 2): no match
                    · simp [evalBuiltinPassThrough]
                  | cons _ _ => -- length 7+: no pass-through pattern
                    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [evalBuiltinPassThrough]
    · -- b is not a pass-through builtin: both sides return none
      have hb_not : b ≠ .IfThenElse ∧ b ≠ .ChooseUnit ∧ b ≠ .Trace ∧
                     b ≠ .ChooseData ∧ b ≠ .ChooseList ∧ b ≠ .MkCons :=
        ⟨fun h => hb (h ▸ .inl rfl), fun h => hb (h ▸ .inr (.inl rfl)),
         fun h => hb (h ▸ .inr (.inr (.inl rfl))),
         fun h => hb (h ▸ .inr (.inr (.inr (.inl rfl)))),
         fun h => hb (h ▸ .inr (.inr (.inr (.inr (.inl rfl))))),
         fun h => hb (h ▸ .inr (.inr (.inr (.inr (.inr rfl)))))⟩
      rw [evalBuiltinPassThrough_none_of_not_passthrough b args₁ hb_not,
          evalBuiltinPassThrough_none_of_not_passthrough b args₂ hb_not]; trivial

/-- ListValueRelV implies extractConsts agrees on both sides.
If both succeed, the constant lists are identical. If one fails, both fail. -/
private theorem extractConsts_relV (h : ListValueRelV args₁ args₂) :
    match Moist.CEK.extractConsts args₁, Moist.CEK.extractConsts args₂ with
    | some cs1, some cs2 => cs1 = cs2
    | none, none => True
    | _, _ => False := by
  -- Simple approach: both return the same because:
  -- Case 1: args1 = args2 → trivially same
  -- Case 2: args differ → at least one non-VCon entry →
  --          extractConsts fails → both return none
  -- But extractConsts might succeed if only the rest differs...
  -- Actually extractConsts just maps VCon→some, non-VCon→none, then sequence.
  -- If ListValueRelV and skeleton matches, extractConsts agrees.
  -- Structural proof by cases on ListValueRelV.
  -- VCon heads: recursion on tail. Non-VCon heads: extractConsts returns none.
  cases h with
  | nil => simp [extractConsts]
  | cons hv hr =>
    have ih := extractConsts_relV hr
    cases hv with
    | vcon =>
      simp only [extractConsts, bind, Option.bind]
      revert ih
      generalize extractConsts _ = r1
      generalize extractConsts _ = r2
      intro ih; cases r1 <;> cases r2 <;> simp_all
    | refl =>
      rename_i v _ _
      cases v with
      | VCon c =>
        simp only [extractConsts, bind, Option.bind]
        revert ih
        generalize extractConsts _ = r1
        generalize extractConsts _ = r2
        intro ih; cases r1 <;> cases r2 <;> simp_all
      | VLam _ _ => simp [extractConsts]
      | VDelay _ _ => simp [extractConsts]
      | VConstr _ _ => simp [extractConsts]
      | VBuiltin _ _ _ => simp [extractConsts]
    | vlam _ _ _ => simp [extractConsts]
    | vdelay _ _ _ => simp [extractConsts]
    | vconstr _ _ => simp [extractConsts]
    | vbuiltin _ _ _ => simp [extractConsts]

/-- **Core builtin preservation lemma.** If `ListValueRelV args₁ args₂`, then
    `evalBuiltin b` either succeeds on both with `ValueRelV`-related results,
    or fails on both. Combines the pass-through and constant-extraction stages. -/
theorem evalBuiltin_relV (b : BuiltinFun) (args₁ args₂ : List CekValue)
    (hargs : ListValueRelV args₁ args₂) :
    match evalBuiltin b args₁, evalBuiltin b args₂ with
    | some v₁, some v₂ => ValueRelV v₁ v₂
    | none, none => True
    | _, _ => False := by
  by_cases h_eq : args₁ = args₂
  · subst h_eq
    cases evalBuiltin b args₁ with
    | some v => exact .refl
    | none => trivial
  · -- args differ but ListValueRelV.
    -- evalBuiltin = try passThrough, then extractConsts + evalBuiltinConst
    have hpt := evalBuiltin_passThrough_relV b args₁ args₂ hargs
    have hec := extractConsts_relV hargs
    -- Unfold evalBuiltin using its definition
    show match evalBuiltin b args₁, evalBuiltin b args₂ with
         | some v₁, some v₂ => ValueRelV v₁ v₂ | none, none => True | _, _ => False
    -- Rewrite evalBuiltin in terms of passThrough + extractConsts
    simp only [evalBuiltin]
    generalize hp1 : evalBuiltinPassThrough b args₁ = r1
    generalize hp2 : evalBuiltinPassThrough b args₂ = r2
    rw [hp1, hp2] at hpt
    cases r1 with
    | some v1 => cases r2 with
      | some v2 => simp; exact hpt
      | none => simp at hpt
    | none => cases r2 with
      | some _ => simp at hpt
      | none =>
        simp only
        generalize he1 : extractConsts args₁ = e1
        generalize he2 : extractConsts args₂ = e2
        rw [he1, he2] at hec
        cases e1 with
        | some cs1 => cases e2 with
          | some cs2 =>
            have heq : cs1 = cs2 := hec
            subst heq; simp; cases evalBuiltinConst b cs1 with
            | some _ => exact .refl
            | none => trivial
          | none => simp at hec
        | none => cases e2 with
          | some _ => simp at hec
          | none => trivial

private theorem ret_evalBuiltin_relV
    {b : BuiltinFun} {args₁ args₂ : List CekValue}
    {s₁ s₂ : Stack}
    (hargs : ListValueRelV args₁ args₂)
    (hrest : StackRel s₁ s₂) :
    StateRel
      (match evalBuiltin b args₁ with | some v => .ret s₁ v | none => .error)
      (match evalBuiltin b args₂ with | some v => .ret s₂ v | none => .error) := by
  have h := evalBuiltin_relV b args₁ args₂ hargs
  generalize evalBuiltin b args₁ = r1 at h
  generalize evalBuiltin b args₂ = r2 at h
  cases r1 with
  | some v1 => cases r2 with
    | some v2 => exact .ret hrest h
    | none => exact absurd h id
  | none => cases r2 with
    | some _ => exact absurd h id
    | none => exact .error

/-! ## Refl case helpers

When ValueRelV.refl, both sides have the same value v. The step function
produces identical results on both sides (modulo the stack tail). -/

/-- Handle force + refl: step (ret (.force :: s) v) for a given v -/
private theorem stateRel_compute_refl {s₁ s₂ : Stack} (hs : StackRel s₁ s₂) (env : CekEnv) (t : Term) :
    StateRel (State.compute s₁ env t) (State.compute s₂ env t) := by
  have ⟨d, hd⟩ := closedAt_exists t
  have h := StateRel.compute hs id d (envRelV_refl d env) hd
  simp only [renameTerm_id] at h; exact h

private theorem step_force_refl {s₁ s₂ : Stack} (hrest : StackRel s₁ s₂) (v : CekValue) :
    StateRel (step (.ret (.force :: s₁) v)) (step (.ret (.force :: s₂) v)) := by
  simp only [step]
  cases v with
  | VDelay body env => exact stateRel_compute_refl hrest env body
  | VBuiltin b args ea =>
    cases h_head : ea.head with
    | argQ =>
      simp [h_head]
      cases h_tail : ea.tail with
      | some rest => simp [h_tail]; exact .ret hrest .refl
      | none =>
        simp [h_tail]
        cases evalBuiltin b args with
        | some v => exact .ret hrest .refl
        | none => exact .error
    | argV => simp [h_head]; exact .error
  | VLam _ _ => exact .error
  | VCon _ => exact .error
  | VConstr _ _ => exact .error

/-- Handle funV + refl: step (ret (.funV v :: s) vx) for a given v -/
private theorem step_funV_refl {s₁ s₂ : Stack} (hrest : StackRel s₁ s₂)
    (v : CekValue) {vx1 vx2 : CekValue} (hvx : ValueRelV vx1 vx2) :
    StateRel (step (.ret (.funV v :: s₁) vx1)) (step (.ret (.funV v :: s₂) vx2)) := by
  simp only [step]
  cases v with
  | VLam body env =>
    have ⟨d', hclosed⟩ := closedAt_exists body
    have h := StateRel.compute hrest (liftRename id) (d' + 1)
      (envRelV_extend id d' env env _ _ (envRelV_refl d' env) hvx)
      (closedAt_mono hclosed (by omega))
    simp only [renameTerm, liftRename_id, renameTerm_id] at h; exact h
  | VBuiltin b args ea =>
    cases h_head : ea.head with
    | argV =>
      simp [h_head]
      cases h_tail : ea.tail with
      | some rest =>
        simp [h_tail]
        exact .ret hrest (.vbuiltin rfl (.cons hvx (listValueRelV_refl args)) rfl)
      | none =>
        simp [h_tail]
        exact ret_evalBuiltin_relV (.cons hvx (listValueRelV_refl args)) hrest
    | argQ => simp [h_head]; exact .error
  | VCon _ => exact .error
  | VDelay _ _ => exact .error
  | VConstr _ _ => exact .error

/-- Handle applyArg + refl: step (ret (.applyArg vx :: s) v) for a given v -/
private theorem step_applyArg_refl {s₁ s₂ : Stack} (hrest : StackRel s₁ s₂)
    (v : CekValue) {vx1 vx2 : CekValue} (hvx : ValueRelV vx1 vx2) :
    StateRel (step (.ret (.applyArg vx1 :: s₁) v)) (step (.ret (.applyArg vx2 :: s₂) v)) := by
  simp only [step]
  cases v with
  | VLam body env =>
    have ⟨d', hclosed⟩ := closedAt_exists body
    have h := StateRel.compute hrest (liftRename id) (d' + 1)
      (envRelV_extend id d' env env _ _ (envRelV_refl d' env) hvx)
      (closedAt_mono hclosed (by omega))
    simp only [renameTerm, liftRename_id, renameTerm_id] at h; exact h
  | VBuiltin b args ea =>
    cases h_head : ea.head with
    | argV =>
      simp [h_head]
      cases h_tail : ea.tail with
      | some rest =>
        simp [h_tail]
        exact .ret hrest (.vbuiltin rfl (.cons hvx (listValueRelV_refl args)) rfl)
      | none =>
        simp [h_tail]
        exact ret_evalBuiltin_relV (.cons hvx (listValueRelV_refl args)) hrest
    | argQ => simp [h_head]; exact .error
  | VCon _ => exact .error
  | VDelay _ _ => exact .error
  | VConstr _ _ => exact .error

/-- Handle caseScrutinee + refl: same value on both sides, envs may differ by σ -/
private theorem step_case_refl {s₁ s₂ : Stack} (hrest : StackRel s₁ s₂)
    (v : CekValue) {σ' : Nat → Nat} {d' : Nat} {alts : List Term}
    (halts : closedAtList d' alts = true)
    {env₁ env₂ : CekEnv} (henv' : EnvRelV σ' d' env₁ env₂) :
    StateRel (step (.ret (.caseScrutinee alts env₁ :: s₁) v))
             (step (.ret (.caseScrutinee (renameTermList σ' alts) env₂ :: s₂) v)) := by
  cases v with
  | VConstr tag fields =>
    simp only [step]
    cases h_idx : alts[tag]? with
    | none =>
      have : (renameTermList σ' alts)[tag]? = none := by
        simp [List.getElem?_eq_none_iff, renameTermList_length] at h_idx ⊢; exact h_idx
      simp [h_idx, this]; exact .error
    | some alt =>
      have ⟨hi, heq_alt⟩ := List.getElem?_eq_some_iff.mp h_idx
      subst heq_alt
      have hi2 : tag < (renameTermList σ' alts).length := by rw [renameTermList_length]; exact hi
      have : (renameTermList σ' alts)[tag]? = some (renameTerm σ' alts[tag]) := by
        rw [List.getElem?_eq_some_iff]; exact ⟨hi2, renameTermList_getElem σ' alts tag hi⟩
      simp [h_idx, this]
      exact .compute (stackRel_append (listValueRelV_map_applyArg_stackRel (listValueRelV_refl fields)) hrest)
        σ' d' henv' (closedAtList_getElem halts hi)
  | VCon c =>
    simp only [step]
    cases h_ctf : constToTagAndFields c with
    | none => simp [h_ctf]; exact .error
    | some val =>
      obtain ⟨tag, numCtors, fields⟩ := val
      simp only [h_ctf]
      cases h_check : (decide (numCtors > 0) && decide (alts.length > numCtors)) with
      | true =>
        have : (decide (numCtors > 0) && decide ((renameTermList σ' alts).length > numCtors)) = true := by
          rw [renameTermList_length]; exact h_check
        simp [h_check, this]; exact .error
      | false =>
        have hcheck2 : (decide (numCtors > 0) && decide ((renameTermList σ' alts).length > numCtors)) = false := by
          rw [renameTermList_length]; exact h_check
        simp [h_check, hcheck2]
        cases h_idx : alts[tag]? with
        | none =>
          have : (renameTermList σ' alts)[tag]? = none := by
            simp [List.getElem?_eq_none_iff, renameTermList_length] at h_idx ⊢; exact h_idx
          simp [h_idx, this]; exact .error
        | some alt =>
          have ⟨hi, heq_alt⟩ := List.getElem?_eq_some_iff.mp h_idx
          subst heq_alt
          have hi2 : tag < (renameTermList σ' alts).length := by rw [renameTermList_length]; exact hi
          have : (renameTermList σ' alts)[tag]? = some (renameTerm σ' alts[tag]) := by
            rw [List.getElem?_eq_some_iff]; exact ⟨hi2, renameTermList_getElem σ' alts tag hi⟩
          simp [h_idx, this]
          exact .compute
            (stackRel_append (listValueRelV_map_applyArg_stackRel (listValueRelV_refl fields)) hrest)
            σ' d' henv' (closedAtList_getElem halts hi)
  | VDelay _ _ => show StateRel .error .error; exact .error
  | VLam _ _ => show StateRel .error .error; exact .error
  | VBuiltin _ _ _ => show StateRel .error .error; exact .error

/-! ## Step preservation theorem -/

/-- **The bisimulation invariant is preserved by `step`.**
    Given `StateRel s₁ s₂`, we have `StateRel (step s₁) (step s₂)`.

    This is the core of the entire verification: every possible CEK
    transition preserves the structural relation. The proof proceeds by
    cases on the `StateRel` constructor, then on the current term or
    frame. Key sub-cases:
    - `Var n`: use `envRelV_elim` to get matching lookups.
    - `Lam`/`Delay`: produce `ValueRelV.vlam`/`.vdelay` with the
      `closedAt` and `EnvRelV` witnesses from the hypothesis.
    - `Apply`/`Force`: push a related frame via `FrameRel`.
    - `ret` with `funV`/`applyArg` of a `VLam`: extend the environment
      using `envRelV_extend`.
    - `ret` with `funV`/`applyArg` of a `VBuiltin`: use `evalBuiltin_relV`.
    - `ret` with `caseScrutinee` of `VConstr`: index into alternatives
      using `closedAtList_getElem` and push `applyArg` frames. -/
theorem step_preserves {s₁ s₂ : State} (h : StateRel s₁ s₂) :
    StateRel (step s₁) (step s₂) := by
  cases h with
  | error => exact .error
  | halt hv => exact .halt hv
  | compute hs σ d henv ht =>
    cases ‹Term› with
    | Var n =>
      simp only [renameTerm, step]
      have hle := closedAt_var ht
      by_cases hn : n = 0
      · subst hn; rw [envRelV_zero henv]; simp [lookup_zero]; exact .error
      · have hpos : 0 < n := Nat.pos_of_ne_zero hn
        have hlr := envRelV_elim henv hpos hle
        generalize h1 : CekEnv.lookup _ n = r1
        generalize h2 : CekEnv.lookup _ (σ n) = r2
        rw [h1, h2] at hlr
        cases hlr with
        | bothNone => exact .error
        | bothSome hv => exact .ret hs hv
    | Constant p =>
      obtain ⟨c, ty⟩ := p; simp only [renameTerm, step]; exact .ret hs .vcon
    | Builtin b =>
      simp only [renameTerm, step]; exact .ret hs (.vbuiltin rfl .nil rfl)
    | Lam n body =>
      simp only [renameTerm, step]; exact .ret hs (.vlam σ d (closedAt_lam ht) henv)
    | Delay body =>
      simp only [renameTerm, step]; exact .ret hs (.vdelay σ d (closedAt_delay ht) henv)
    | Force e =>
      simp only [renameTerm, step]
      exact .compute (.cons .force hs) σ d henv (closedAt_force ht)
    | Apply f x =>
      simp only [renameTerm, step]
      have ⟨hf, hx⟩ := closedAt_apply ht
      exact .compute (.cons (.arg σ d henv hx) hs) σ d henv hf
    | Constr tag args =>
      simp only [renameTerm, step]
      cases args with
      | nil => exact .ret hs (.vconstr rfl .nil)
      | cons m ms =>
        have hargs := closedAt_constr ht
        have ⟨hm, hms⟩ := closedAt_constr_cons hargs
        exact .compute (.cons (.constrField σ d tag .nil hms henv) hs) σ d henv hm
    | Case scrut alts =>
      simp only [renameTerm, step]
      have ⟨hscrut, halts⟩ := closedAt_case ht
      exact .compute (.cons (.caseScrutinee σ d halts henv) hs) σ d henv hscrut
    | Error =>
      simp only [renameTerm, step]; exact .error

  | ret hs hv =>
    cases hs with
    | nil => simp only [step]; exact .halt hv
    | cons hf hrest =>
      cases hf with
      | force =>
        cases hv with
        | vdelay σ' d' hclosed henv' =>
          simp only [step]; exact .compute hrest σ' d' henv' hclosed
        | vbuiltin hb hargs hea =>
          subst hb; subst hea; simp only [step]
          cases h_head : ExpectedArgs.head ‹_› with
          | argQ =>
            simp [h_head]
            cases h_tail : ExpectedArgs.tail ‹_› with
            | some rest => simp [h_tail]; exact .ret hrest (.vbuiltin rfl hargs rfl)
            | none => simp [h_tail]; exact ret_evalBuiltin_relV hargs hrest
          | argV => simp [h_head]; exact .error
        | refl => exact step_force_refl hrest _
        | vlam _ _ _ _ => simp only [step]; exact .error
        | vcon => simp only [step]; exact .error
        | vconstr _ _ => simp only [step]; exact .error

      | arg σ' d' henv' hclosed =>
        simp only [step]
        exact .compute (.cons (.funV hv) hrest) σ' d' henv' hclosed

      | funV hv_fun =>
        cases hv_fun with
        | vlam σ' d' hclosed henv' =>
          simp only [step]
          exact .compute hrest (liftRename σ') (d' + 1) (envRelV_extend σ' d' _ _ _ _ henv' hv) hclosed
        | vbuiltin hb hargs hea =>
          subst hb; subst hea; simp only [step]
          cases h_head : ExpectedArgs.head ‹_› with
          | argV =>
            simp [h_head]
            cases h_tail : ExpectedArgs.tail ‹_› with
            | some rest => simp [h_tail]; exact .ret hrest (.vbuiltin rfl (.cons hv hargs) rfl)
            | none => simp [h_tail]; exact ret_evalBuiltin_relV (.cons hv hargs) hrest
          | argQ => simp [h_head]; exact .error
        | refl => exact step_funV_refl hrest _ hv
        | vcon => simp only [step]; exact .error
        | vconstr _ _ => simp only [step]; exact .error
        | vdelay _ _ _ _ => simp only [step]; exact .error

      | applyArg hv_arg =>
        cases hv with
        | vlam σ' d' hclosed henv' =>
          simp only [step]
          exact .compute hrest (liftRename σ') (d' + 1) (envRelV_extend σ' d' _ _ _ _ henv' hv_arg) hclosed
        | vbuiltin hb hargs hea =>
          subst hb; subst hea; simp only [step]
          cases h_head : ExpectedArgs.head ‹_› with
          | argV =>
            simp [h_head]
            cases h_tail : ExpectedArgs.tail ‹_› with
            | some rest => simp [h_tail]; exact .ret hrest (.vbuiltin rfl (.cons hv_arg hargs) rfl)
            | none => simp [h_tail]; exact ret_evalBuiltin_relV (.cons hv_arg hargs) hrest
          | argQ => simp [h_head]; exact .error
        | refl => exact step_applyArg_refl hrest _ hv_arg
        | vcon => simp only [step]; exact .error
        | vconstr _ _ => simp only [step]; exact .error
        | vdelay _ _ _ _ => simp only [step]; exact .error

      | constrField σ' d' tag hdone htodo henv' =>
        cases ‹List Term› with
        | cons m ms =>
          simp only [step]
          have ⟨hm, hms⟩ := closedAt_constr_cons htodo
          exact .compute (.cons (.constrField σ' d' tag (.cons hv hdone) hms henv') hrest) σ' d' henv' hm
        | nil =>
          simp only [step]
          exact .ret hrest (.vconstr rfl (listValueRelV_cons_rev hv hdone))

      | caseScrutinee σ' d' halts henv' =>
        -- LHS: step (.ret (.caseScrutinee alts env₁ :: s₁) v₁)
        -- RHS: step (.ret (.caseScrutinee (renameTermList σ' alts) env₂ :: s₂) v₂)
        cases hv with
        | vconstr htag hfs =>
          subst htag; simp only [step]
          rename_i tag _ _
          -- LHS matches on alts[tag]?, RHS on (renameTermList σ' alts)[tag]?
          cases h_idx : (‹List Term›)[tag]? with
          | none =>
            have h_idx2 : (renameTermList σ' ‹List Term›)[tag]? = none := by
              rw [List.getElem?_eq_none_iff, renameTermList_length]
              exact List.getElem?_eq_none_iff.mp h_idx
            simp [h_idx, h_idx2]; exact .error
          | some alt =>
            have ⟨hi, heq_alt⟩ := List.getElem?_eq_some_iff.mp h_idx
            subst heq_alt
            have hi2 : tag < (renameTermList σ' ‹List Term›).length := by rw [renameTermList_length]; exact hi
            have h_idx2 : (renameTermList σ' ‹List Term›)[tag]? = some (renameTerm σ' (‹List Term›[tag])) := by
              rw [List.getElem?_eq_some_iff]; exact ⟨hi2, renameTermList_getElem σ' _ tag hi⟩
            simp [h_idx, h_idx2]
            exact .compute (stackRel_append (listValueRelV_map_applyArg_stackRel hfs) hrest)
              σ' d' henv' (closedAtList_getElem halts hi)
        | vcon => exact step_case_refl hrest _ halts henv'
        | refl => exact step_case_refl hrest _ halts henv'
        | vlam _ _ _ _ => simp only [step]; exact .error
        | vdelay _ _ _ _ => simp only [step]; exact .error
        | vbuiltin _ _ _ => simp only [step]; exact .error

/-! ## Main bisimulation extraction -/

/-- Iterated step preservation: `StateRel` is maintained after `n` steps.
    Immediate by induction from `step_preserves`. -/
theorem steps_preserves (n : Nat) {s₁ s₂ : State} (h : StateRel s₁ s₂) :
    StateRel (steps n s₁) (steps n s₂) := by
  induction n generalizing s₁ s₂ with
  | zero => exact h
  | succ n ih => simp only [steps]; exact ih (step_preserves h)

/-- Extract the `ValueRelV` witness from a `StateRel` between two `halt` states. -/
theorem stateRel_halt_valueRelV {v₁ v₂ : CekValue}
    (h : StateRel (.halt v₁) (.halt v₂)) : ValueRelV v₁ v₂ := by
  cases h with | halt hv => exact hv

/-- **Value extraction from bisimulation**: if `StateRel s₁ s₂` and both
    sides reach `halt`, the halted values are `ValueRelV`-related.

    Proof: run `steps_preserves n1` on `s₁`'s witness. After `n1` steps,
    `s₁` is at `halt v₁` and `s₂` is at some state that is `StateRel`
    with `halt v₁` — which can only be `halt v₂'`. Then use `reaches_unique`
    to show `v₂' = v₂`. -/
theorem bisim_reaches {s₁ s₂ : State}
    (hrel : StateRel s₁ s₂)
    {v₁ v₂ : CekValue}
    (h₁ : Reaches s₁ (.halt v₁)) (h₂ : Reaches s₂ (.halt v₂)) :
    ValueRelV v₁ v₂ := by
  obtain ⟨n1, hn1⟩ := h₁
  obtain ⟨n2, hn2⟩ := h₂
  have hr1 := steps_preserves n1 hrel
  rw [hn1] at hr1
  generalize h_eq : steps n1 s₂ = s2_final at hr1
  cases s2_final with
  | halt v2' =>
    cases hr1 with | halt hv =>
    exact reaches_unique ⟨n2, hn2⟩ ⟨n1, h_eq⟩ ▸ hv
  | error => cases hr1
  | compute _ _ _ => cases hr1
  | ret _ _ => cases hr1

/-- **Error propagation from bisimulation**: if `StateRel s₁ s₂` and `s₁`
    reaches `error`, then `s₂` also reaches `error`. Same technique as
    `bisim_reaches` but matching on `error` instead of `halt`. -/
theorem bisim_reaches_error {s₁ s₂ : State}
    (hrel : StateRel s₁ s₂)
    (h₁ : Reaches s₁ .error) : Reaches s₂ .error := by
  obtain ⟨n, hn⟩ := h₁
  have hr := steps_preserves n hrel
  rw [hn] at hr
  -- StateRel .error (steps n s₂) — only .error matches
  generalize h_eq : steps n s₂ = s2f at hr
  cases s2f with
  | error => exact ⟨n, h_eq⟩
  | halt _ => cases hr
  | compute _ _ _ => cases hr
  | ret _ _ => cases hr

end Moist.Verified.Bisim
