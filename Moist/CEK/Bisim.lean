import Moist.CEK.ClosedAt
import Moist.CEK.Builtins

set_option linter.unusedSimpArgs false

namespace Moist.CEK.Bisim

open Moist.CEK
open Moist.Plutus.Term
open Moist.MIR.Semantics

/-! # CEK State Bisimulation -/

/-! ## Helper lemmas -/

private theorem lookup_zero (env : CekEnv) : env.lookup 0 = none := by
  cases env <;> simp [CekEnv.lookup]

theorem listValueRelV_append (ha : ListValueRelV a1 a2) (hb : ListValueRelV b1 b2) :
    ListValueRelV (a1 ++ b1) (a2 ++ b2) := by
  cases ha with
  | nil => exact hb
  | cons hv hr => exact .cons hv (listValueRelV_append hr hb)

theorem listValueRelV_reverse (h : ListValueRelV a1 a2) :
    ListValueRelV a1.reverse a2.reverse := by
  cases h with
  | nil => exact .nil
  | cons hv hr =>
    simp [List.reverse_cons]
    exact listValueRelV_append (listValueRelV_reverse hr) (.cons hv .nil)

theorem listValueRelV_cons_rev (hv : ValueRelV v1 v2)
    (hdone : ListValueRelV done1 done2) :
    ListValueRelV ((v1 :: done1).reverse) ((v2 :: done2).reverse) := by
  simp [List.reverse_cons]
  exact listValueRelV_append (listValueRelV_reverse hdone) (.cons hv .nil)

theorem stackRel_append (hs : StackRel s1 s2) (ht : StackRel t1 t2) :
    StackRel (s1 ++ t1) (s2 ++ t2) := by
  cases hs with
  | nil => exact ht
  | cons hf hr => exact .cons hf (stackRel_append hr ht)

theorem listValueRelV_map_applyArg_stackRel (hfs : ListValueRelV fs1 fs2) :
    StackRel (fs1.map Frame.applyArg) (fs2.map Frame.applyArg) := by
  cases hfs with
  | nil => exact .nil
  | cons hv hr => exact .cons (.applyArg hv) (listValueRelV_map_applyArg_stackRel hr)

theorem listValueRelV_refl (vs : List CekValue) : ListValueRelV vs vs := by
  induction vs with
  | nil => exact .nil
  | cons v rest ih => exact .cons .refl ih

/-! ## evalBuiltin preservation -/

theorem valueRelV_vcon_eq (h : ValueRelV v1 v2) (heq : v1 = .VCon c) : v2 = .VCon c := by
  subst heq; cases h with | vcon => rfl | refl => rfl

/-- If ValueRelV v1 v2 and v1 = VCon c, then v2 = VCon c. -/
private theorem valueRelV_vcon (h : ValueRelV v1 v2) (hv : v1 = .VCon c) : v2 = .VCon c := by
  subst hv; cases h with | vcon => rfl | refl => rfl

private theorem valueRelV_vcon_right (h : ValueRelV v1 v2) (hv : v2 = .VCon c) : v1 = .VCon c := by
  subst hv; cases h with | vcon => rfl | refl => rfl

/-- VCon projection: extracts the Const if VCon, otherwise none. -/
private def vconProj : CekValue → Option Const
  | .VCon c => some c
  | _ => none

/-- ValueRelV preserves VCon projection. -/
private theorem valueRelV_vconProj (h : ValueRelV v1 v2) : vconProj v1 = vconProj v2 := by
  cases h with
  | vcon => rfl
  | refl => rfl
  | vlam => rfl
  | vdelay => rfl
  | vconstr => rfl
  | vbuiltin => rfl

/-- ListValueRelV preserves the VCon skeleton (map of vconProj). -/
private theorem listValueRelV_vconSkel (h : ListValueRelV args1 args2) :
    args1.map vconProj = args2.map vconProj := by
  cases h with
  | nil => rfl
  | cons hv hr =>
    simp [List.map]
    exact ⟨valueRelV_vconProj hv, listValueRelV_vconSkel hr⟩


/-- ListValueRelV where all elements are VCon implies the lists are equal. -/
private theorem listValueRelV_vcon_eq (h : ListValueRelV args1 args2)
    (hall : ∀ v ∈ args1, ∃ c, v = .VCon c) : args1 = args2 := by
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

private theorem listValueRelV_length (h : ListValueRelV args1 args2) :
    args1.length = args2.length := by
  cases h with
  | nil => rfl
  | cons _ hr => simp [List.length_cons, listValueRelV_length hr]

private theorem evalBPT_MkCons_some {v1 v2 w : CekValue}
    (h : evalBuiltinPassThrough .MkCons [v1, v2] = some w) :
    (∃ c, v1 = .VCon c) ∧ (∃ c, v2 = .VCon c) := by
  cases v1 with
  | VCon c1 =>
    refine ⟨⟨c1, rfl⟩, ?_⟩
    cases v2 with
    | VCon c2 => exact ⟨c2, rfl⟩
    | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
      cases c1 <;> simp [evalBuiltinPassThrough] at h
  | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
    simp [evalBuiltinPassThrough] at h

theorem evalBuiltin_passThrough_relV (b : BuiltinFun) (args1 args2 : List CekValue)
    (hargs : ListValueRelV args1 args2) :
    match evalBuiltinPassThrough b args1, evalBuiltinPassThrough b args2 with
    | some v1, some v2 => ValueRelV v1 v2
    | none, none => True
    | _, _ => False := by
  by_cases h_eq : args1 = args2
  · subst h_eq
    cases evalBuiltinPassThrough b args1 with
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
      rw [evalBuiltinPassThrough_none_of_not_passthrough b args1 hb_not,
          evalBuiltinPassThrough_none_of_not_passthrough b args2 hb_not]; trivial

/-- ListValueRelV implies extractConsts agrees on both sides.
If both succeed, the constant lists are identical. If one fails, both fail. -/
private theorem extractConsts_relV (h : ListValueRelV args1 args2) :
    match Moist.CEK.extractConsts args1, Moist.CEK.extractConsts args2 with
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

/-- Core builtin lemma. Uses the two-stage decomposition:
evalBuiltinPassThrough preserves ValueRelV, and extractConsts + evalBuiltinConst
is deterministic on identical constant lists. -/
theorem evalBuiltin_relV (b : BuiltinFun) (args1 args2 : List CekValue)
    (hargs : ListValueRelV args1 args2) :
    match evalBuiltin b args1, evalBuiltin b args2 with
    | some v1, some v2 => ValueRelV v1 v2
    | none, none => True
    | _, _ => False := by
  by_cases h_eq : args1 = args2
  · subst h_eq
    cases evalBuiltin b args1 with
    | some v => exact .refl
    | none => trivial
  · -- args differ but ListValueRelV.
    -- evalBuiltin = try passThrough, then extractConsts + evalBuiltinConst
    have hpt := evalBuiltin_passThrough_relV b args1 args2 hargs
    have hec := extractConsts_relV hargs
    -- Unfold evalBuiltin using its definition
    show match evalBuiltin b args1, evalBuiltin b args2 with
         | some v1, some v2 => ValueRelV v1 v2 | none, none => True | _, _ => False
    -- Rewrite evalBuiltin in terms of passThrough + extractConsts
    simp only [evalBuiltin]
    generalize hp1 : evalBuiltinPassThrough b args1 = r1
    generalize hp2 : evalBuiltinPassThrough b args2 = r2
    rw [hp1, hp2] at hpt
    cases r1 with
    | some v1 => cases r2 with
      | some v2 => simp; exact hpt
      | none => simp at hpt
    | none => cases r2 with
      | some _ => simp at hpt
      | none =>
        simp only
        generalize he1 : extractConsts args1 = e1
        generalize he2 : extractConsts args2 = e2
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
    {b : BuiltinFun} {args1 args2 : List CekValue}
    {s1 s2 : Stack}
    (hargs : ListValueRelV args1 args2)
    (hrest : StackRel s1 s2) :
    StateRel
      (match evalBuiltin b args1 with | some v => .ret s1 v | none => .error)
      (match evalBuiltin b args2 with | some v => .ret s2 v | none => .error) := by
  have h := evalBuiltin_relV b args1 args2 hargs
  generalize evalBuiltin b args1 = r1 at h
  generalize evalBuiltin b args2 = r2 at h
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
private theorem step_force_refl {s1 s2 : Stack} (hrest : StackRel s1 s2) (v : CekValue) :
    StateRel (step (.ret (.force :: s1) v)) (step (.ret (.force :: s2) v)) := by
  simp only [step]
  cases v with
  | VDelay body env =>
    have ⟨d', hclosed⟩ := closedAt_exists body
    exact .compute hrest d' (envRelV_refl d' env) hclosed
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
private theorem step_funV_refl {s1 s2 : Stack} (hrest : StackRel s1 s2)
    (v : CekValue) {vx1 vx2 : CekValue} (hvx : ValueRelV vx1 vx2) :
    StateRel (step (.ret (.funV v :: s1) vx1)) (step (.ret (.funV v :: s2) vx2)) := by
  simp only [step]
  cases v with
  | VLam body env =>
    have ⟨d', hclosed⟩ := closedAt_exists body
    exact .compute hrest (d' + 1)
      (envRelV_extend d' env env _ _ (envRelV_refl d' env) hvx)
      (closedAt_mono hclosed (by omega))
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
private theorem step_applyArg_refl {s1 s2 : Stack} (hrest : StackRel s1 s2)
    (v : CekValue) {vx1 vx2 : CekValue} (hvx : ValueRelV vx1 vx2) :
    StateRel (step (.ret (.applyArg vx1 :: s1) v)) (step (.ret (.applyArg vx2 :: s2) v)) := by
  simp only [step]
  cases v with
  | VLam body env =>
    have ⟨d', hclosed⟩ := closedAt_exists body
    exact .compute hrest (d' + 1)
      (envRelV_extend d' env env _ _ (envRelV_refl d' env) hvx)
      (closedAt_mono hclosed (by omega))
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

/-- Handle caseScrutinee + refl -/
private theorem step_case_refl {s1 s2 : Stack} (hrest : StackRel s1 s2)
    (v : CekValue) {d' : Nat} {alts : List Term}
    (halts : closedAtList d' alts = true)
    {env1 env2 : CekEnv} (henv' : EnvRelV d' env1 env2) :
    StateRel (step (.ret (.caseScrutinee alts env1 :: s1) v))
             (step (.ret (.caseScrutinee alts env2 :: s2) v)) := by
  cases v with
  | VConstr tag fields =>
    -- step produces: match alts[tag]? with | some alt => compute (fields.map applyArg ++ s) env alt | none => error
    show StateRel
      (match alts[tag]? with
       | some alt => .compute (fields.map Frame.applyArg ++ s1) env1 alt
       | none => .error)
      (match alts[tag]? with
       | some alt => .compute (fields.map Frame.applyArg ++ s2) env2 alt
       | none => .error)
    cases h_idx : alts[tag]? with
    | none => exact .error
    | some alt =>
      have ⟨hi, heq_alt⟩ := List.getElem?_eq_some_iff.mp h_idx
      subst heq_alt
      exact .compute
        (stackRel_append (listValueRelV_map_applyArg_stackRel (listValueRelV_refl fields)) hrest)
        d' henv' (closedAtList_getElem halts hi)
  | VCon c =>
    show StateRel
      (match constToTagAndFields c with
       | some (tag, numCtors, fields) =>
         if numCtors > 0 && alts.length > numCtors then .error
         else match alts[tag]? with
           | some alt => .compute (fields.map Frame.applyArg ++ s1) env1 alt
           | none => .error
       | none => .error)
      (match constToTagAndFields c with
       | some (tag, numCtors, fields) =>
         if numCtors > 0 && alts.length > numCtors then .error
         else match alts[tag]? with
           | some alt => .compute (fields.map Frame.applyArg ++ s2) env2 alt
           | none => .error
       | none => .error)
    cases h_ctf : constToTagAndFields c with
    | none => simp [h_ctf]; exact .error
    | some val =>
      obtain ⟨tag, numCtors, fields⟩ := val
      simp only [h_ctf]
      cases h_check : (decide (numCtors > 0) && decide (alts.length > numCtors)) with
      | true => simp [h_check]; exact .error
      | false =>
        simp [h_check]
        cases h_idx : alts[tag]? with
        | none => simp [h_idx]; exact .error
        | some alt =>
          simp [h_idx]
          have ⟨hi, heq_alt⟩ := List.getElem?_eq_some_iff.mp h_idx
          subst heq_alt
          exact .compute
            (stackRel_append (listValueRelV_map_applyArg_stackRel (listValueRelV_refl fields)) hrest)
            d' henv' (closedAtList_getElem halts hi)
  | VDelay _ _ => show StateRel .error .error; exact .error
  | VLam _ _ => show StateRel .error .error; exact .error
  | VBuiltin _ _ _ => show StateRel .error .error; exact .error

/-! ## Step preservation theorem -/

theorem step_preserves {s1 s2 : State} (h : StateRel s1 s2) :
    StateRel (step s1) (step s2) := by
  cases h with
  | error => exact .error
  | halt hv => exact .halt hv
  | compute hs d henv ht =>
    cases ‹Term› with
    | Var n =>
      simp only [step]
      have hle := closedAt_var ht
      by_cases hn : n = 0
      · subst hn; simp [lookup_zero]; exact .error
      · have hpos : 0 < n := Nat.pos_of_ne_zero hn
        have hlr := envRelV_elim henv hpos hle
        generalize h1 : CekEnv.lookup _ n = r1
        generalize h2 : CekEnv.lookup _ n = r2
        rw [h1, h2] at hlr
        cases hlr with
        | bothNone => exact .error
        | bothSome hv => exact .ret hs hv
    | Constant p =>
      obtain ⟨c, ty⟩ := p; simp only [step]; exact .ret hs .vcon
    | Builtin b =>
      simp only [step]; exact .ret hs (.vbuiltin rfl .nil rfl)
    | Lam n body =>
      simp only [step]; exact .ret hs (.vlam d (closedAt_lam ht) henv)
    | Delay body =>
      simp only [step]; exact .ret hs (.vdelay d (closedAt_delay ht) henv)
    | Force e =>
      simp only [step]
      exact .compute (.cons .force hs) d henv (closedAt_force ht)
    | Apply f x =>
      simp only [step]
      have ⟨hf, hx⟩ := closedAt_apply ht
      exact .compute (.cons (.arg d x henv hx) hs) d henv hf
    | Constr tag args =>
      simp only [step]
      cases args with
      | nil => exact .ret hs (.vconstr rfl .nil)
      | cons m ms =>
        have hargs := closedAt_constr ht
        have ⟨hm, hms⟩ := closedAt_constr_cons hargs
        exact .compute (.cons (.constrField d tag .nil ms hms henv) hs) d henv hm
    | Case scrut alts =>
      simp only [step]
      have ⟨hscrut, halts⟩ := closedAt_case ht
      exact .compute (.cons (.caseScrutinee d alts halts henv) hs) d henv hscrut
    | Error =>
      simp only [step]; exact .error

  | ret hs hv =>
    cases hs with
    | nil => simp only [step]; exact .halt hv
    | cons hf hrest =>
      cases hf with
      | force =>
        cases hv with
        | vdelay d' hclosed henv' =>
          simp only [step]; exact .compute hrest d' henv' hclosed
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
        | vlam _ _ _ => simp only [step]; exact .error
        | vcon => simp only [step]; exact .error
        | vconstr _ _ => simp only [step]; exact .error

      | arg d' t henv' hclosed =>
        simp only [step]
        exact .compute (.cons (.funV hv) hrest) d' henv' hclosed

      | funV hv_fun =>
        cases hv_fun with
        | vlam d' hclosed henv' =>
          simp only [step]
          exact .compute hrest (d' + 1) (envRelV_extend d' _ _ _ _ henv' hv) hclosed
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
        | vdelay _ _ _ => simp only [step]; exact .error

      | applyArg hv_arg =>
        cases hv with
        | vlam d' hclosed henv' =>
          simp only [step]
          exact .compute hrest (d' + 1) (envRelV_extend d' _ _ _ _ henv' hv_arg) hclosed
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
        | vdelay _ _ _ => simp only [step]; exact .error

      | constrField d' tag hdone todo htodo henv' =>
        cases todo with
        | cons m ms =>
          simp only [step]
          have ⟨hm, hms⟩ := closedAt_constr_cons htodo
          exact .compute (.cons (.constrField d' tag (.cons hv hdone) ms hms henv') hrest) d' henv' hm
        | nil =>
          simp only [step]
          exact .ret hrest (.vconstr rfl (listValueRelV_cons_rev hv hdone))

      | caseScrutinee d' alts halts henv' =>
        cases hv with
        | vconstr htag hfs =>
          subst htag; simp only [step]
          rename_i tag _ _
          cases h_idx : alts[tag]? with
          | none => simp [h_idx]; exact .error
          | some alt =>
            simp [h_idx]
            have ⟨hi, heq_alt⟩ := List.getElem?_eq_some_iff.mp h_idx
            subst heq_alt
            exact .compute (stackRel_append (listValueRelV_map_applyArg_stackRel hfs) hrest)
              d' henv' (closedAtList_getElem halts hi)
        | vcon =>
          -- vcon: v1 = v2 = VCon c. Same c on both sides.
          -- step produces match on constToTagAndFields c.
          rename_i c
          show StateRel
            (match constToTagAndFields c with
             | some (tag, numCtors, fields) =>
               if numCtors > 0 && alts.length > numCtors then .error
               else match alts[tag]? with
                 | some alt =>
                   let fieldFrames := fields.map Frame.applyArg
                   .compute (fieldFrames ++ _) _ alt
                 | none => .error
             | none => .error)
            (match constToTagAndFields c with
             | some (tag, numCtors, fields) =>
               if numCtors > 0 && alts.length > numCtors then .error
               else match alts[tag]? with
                 | some alt =>
                   let fieldFrames := fields.map Frame.applyArg
                   .compute (fieldFrames ++ _) _ alt
                 | none => .error
             | none => .error)
          cases h_ctf : constToTagAndFields c with
          | none => simp [h_ctf]; exact .error
          | some val =>
            obtain ⟨tag, numCtors, fields⟩ := val
            simp only [h_ctf]
            cases h_check : (decide (numCtors > 0) && decide (alts.length > numCtors)) with
            | true => simp [h_check]; exact .error
            | false =>
              simp [h_check]
              cases h_idx : alts[tag]? with
              | none => simp [h_idx]; exact .error
              | some alt =>
                simp [h_idx]
                have ⟨hi, heq_alt⟩ := List.getElem?_eq_some_iff.mp h_idx
                subst heq_alt
                exact .compute
                  (stackRel_append (listValueRelV_map_applyArg_stackRel (listValueRelV_refl fields)) hrest)
                  d' henv' (closedAtList_getElem halts hi)
        | refl => exact step_case_refl hrest _ halts henv'
        | vlam _ _ _ => simp only [step]; exact .error
        | vdelay _ _ _ => simp only [step]; exact .error
        | vbuiltin _ _ _ => simp only [step]; exact .error

/-! ## Main bisimulation extraction -/

theorem steps_preserves (n : Nat) {s1 s2 : State} (h : StateRel s1 s2) :
    StateRel (steps n s1) (steps n s2) := by
  induction n generalizing s1 s2 with
  | zero => exact h
  | succ n ih => simp only [steps]; exact ih (step_preserves h)

theorem stateRel_halt_valueRelV {v1 v2 : CekValue}
    (h : StateRel (.halt v1) (.halt v2)) : ValueRelV v1 v2 := by
  cases h with | halt hv => exact hv

theorem bisim_reaches {s1 s2 : State}
    (hrel : StateRel s1 s2)
    {v1 v2 : CekValue}
    (h1 : Reaches s1 v1) (h2 : Reaches s2 v2) :
    ValueRelV v1 v2 := by
  obtain ⟨n1, hn1⟩ := h1
  obtain ⟨n2, hn2⟩ := h2
  have hr1 := steps_preserves n1 hrel
  rw [hn1] at hr1
  generalize h_eq : steps n1 s2 = s2_final at hr1
  cases s2_final with
  | halt v2' =>
    cases hr1 with | halt hv =>
    exact reaches_unique ⟨n2, hn2⟩ ⟨n1, h_eq⟩ ▸ hv
  | error => cases hr1
  | compute _ _ _ => cases hr1
  | ret _ _ => cases hr1

end Moist.CEK.Bisim
