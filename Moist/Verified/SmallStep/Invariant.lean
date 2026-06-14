import Moist.Verified.SmallStep.Closed
import Moist.Verified.SmallStep.ReflectBridge

/-! # The CEK state invariant preserved by `step`

`GoodValue`/`GoodEnv` combine the well-formedness (`WFValue`, builtin spines are
genuine `VBSpine`s) and closedness (`ClosedValue`) invariants into a single
predicate, with projections back to each.  `GoodState` lifts this to a whole CEK
state, additionally tracking that the control/stored terms are closed under
their environments.  The CEK `step` preserves `GoodState` (`step_preserves_good`),
and the initial state of a closed term is `Good` (`init_good`).

Maintaining both invariants in one pass is what lets the forward simulation use
`value_discharge` (needs `WFValue`), `discharge_closed`/`beta_discharge` (need
`ClosedValue`/`ClosedEnv`) and `bspine_discharge` (needs `VBSpine`) at every
reachable state.
-/

namespace Moist.Verified.SmallStep

open Moist.Plutus.Term (Term Const BuiltinFun)
open Moist.CEK
open Moist.Verified (closedAt closedAtList)

/-! ## The combined `Good` predicate -/

mutual
  /-- A CEK value that is simultaneously well-formed (builtin spines are genuine
      `VBSpine`s) and closed (closure bodies closed under their captured
      environment plus binder). -/
  inductive GoodValue : CekValue → Prop
    | vcon {c} : GoodValue (.VCon c)
    | vlam {body env} : closedAt (env.length + 1) body = true → GoodEnv env →
        GoodValue (.VLam body env)
    | vdelay {body env} : closedAt env.length body = true → GoodEnv env →
        GoodValue (.VDelay body env)
    | vconstr {tag fields} : GoodValueList fields → GoodValue (.VConstr tag fields)
    | vbuiltin {b vargs ea} : VBSpine b vargs ea → GoodValueList vargs →
        GoodValue (.VBuiltin b vargs ea)

  inductive GoodValueList : List CekValue → Prop
    | nil : GoodValueList []
    | cons {v vs} : GoodValue v → GoodValueList vs → GoodValueList (v :: vs)

  inductive GoodEnv : CekEnv → Prop
    | nil : GoodEnv .nil
    | cons {v rest} : GoodValue v → GoodEnv rest → GoodEnv (.cons v rest)
end

/-! ## Projections to `WFValue` and `ClosedValue` -/

mutual
  theorem good_wf : ∀ {v : CekValue}, GoodValue v → WFValue v
    | _, .vcon => .vcon
    | _, .vlam _ _ => .vlam
    | _, .vdelay _ _ => .vdelay
    | _, .vconstr hf => .vconstr (goodList_wf hf)
    | _, .vbuiltin hsp ha => .vbuiltin hsp (goodList_wf ha)
  theorem goodList_wf : ∀ {vs : List CekValue}, GoodValueList vs → WFValueList vs
    | _, .nil => .nil
    | _, .cons hv hvs => .cons (good_wf hv) (goodList_wf hvs)
end

mutual
  theorem good_closed : ∀ {v : CekValue}, GoodValue v → ClosedValue v
    | _, .vcon => .vcon
    | _, .vlam hb he => .vlam hb (goodEnv_closed he)
    | _, .vdelay hb he => .vdelay hb (goodEnv_closed he)
    | _, .vconstr hf => .vconstr (goodList_closed hf)
    | _, .vbuiltin _ ha => .vbuiltin (goodList_closed ha)
  theorem goodList_closed : ∀ {vs : List CekValue}, GoodValueList vs → ClosedValueList vs
    | _, .nil => .nil
    | _, .cons hv hvs => .cons (good_closed hv) (goodList_closed hvs)
  theorem goodEnv_closed : ∀ {env : CekEnv}, GoodEnv env → ClosedEnv env
    | _, .nil => .nil
    | _, .cons hv hrest => .cons (good_closed hv) (goodEnv_closed hrest)
end

/-- A closed value discharges to a closed term (via the `Good` projection). -/
theorem good_discharge_closed {v : CekValue} (h : GoodValue v) :
    closedAt 0 (discharge v) = true := discharge_closed (good_closed h)

theorem goodEnv_envDischargeClosed {env : CekEnv} (h : GoodEnv env) :
    EnvDischargeClosed env := closedEnv_envDischargeClosed (goodEnv_closed h)

/-! ## Environment lookup -/

theorem goodList_mem : ∀ {vs : List CekValue}, GoodValueList vs → ∀ {v}, v ∈ vs → GoodValue v
  | _, .nil, _, hmem => by cases hmem
  | _, .cons hv hvs, _, hmem => by
    cases hmem with
    | head => exact hv
    | tail _ h => exact goodList_mem hvs h

theorem goodEnv_lookup : ∀ {ρ : CekEnv} {n : Nat} {v : CekValue},
    GoodEnv ρ → ρ.lookup n = some v → GoodValue v
  | .nil, _, _, _, h => by simp [CekEnv.lookup] at h
  | .cons w rest, 0, _, _, h => by simp [CekEnv.lookup] at h
  | .cons w rest, 1, v, .cons hw _, h => by
    simp only [CekEnv.lookup, Option.some.injEq] at h; exact h ▸ hw
  | .cons w rest, n + 2, v, .cons _ hrest, h => by
    simp only [CekEnv.lookup] at h; exact goodEnv_lookup hrest h

/-! ## `GoodEnv` extension -/

theorem goodEnv_extend {ρ : CekEnv} {v : CekValue} (hρ : GoodEnv ρ) (hv : GoodValue v) :
    GoodEnv (ρ.extend v) := .cons hv hρ

/-! ## Builtin evaluation preserves `Good` -/

/-- A list of `VCon`s is `Good`. -/
theorem allVcon_good : (fields : List CekValue) → (∀ v ∈ fields, ∃ c, v = .VCon c) →
    GoodValueList fields
  | [], _ => .nil
  | v :: rest, h =>
    have ⟨_, hcv⟩ := h v (List.mem_cons_self)
    hcv ▸ .cons .vcon (allVcon_good rest (fun x hx => h x (List.mem_cons_of_mem v hx)))

/-- A constant's `case` fields are all `VCon` (pure re-proof of the
    `Equivalence` lemma, avoiding the heavier module). -/
theorem constToTagAndFields_fields_vcon (c : Const) :
    match constToTagAndFields c with
    | some (_, _, fields) => ∀ v ∈ fields, ∃ c, v = CekValue.VCon c
    | none => True := by
  cases c with
  | Bool b => cases b <;> simp [constToTagAndFields]
  | Unit => simp [constToTagAndFields]
  | Integer n => simp only [constToTagAndFields]; split <;> simp_all
  | ConstList l =>
    cases l with
    | nil => simp [constToTagAndFields]
    | cons h t =>
      simp only [constToTagAndFields]; intro v hv; simp at hv; rcases hv with rfl | rfl <;> exact ⟨_, rfl⟩
  | ConstDataList l =>
    cases l with
    | nil => simp [constToTagAndFields]
    | cons h t =>
      simp only [constToTagAndFields]; intro v hv; simp at hv; rcases hv with rfl | rfl <;> exact ⟨_, rfl⟩
  | Pair p =>
    obtain ⟨a, b⟩ := p
    simp only [constToTagAndFields]; intro v hv; simp at hv; rcases hv with rfl | rfl <;> exact ⟨_, rfl⟩
  | PairData p =>
    obtain ⟨a, b⟩ := p
    simp only [constToTagAndFields]; intro v hv; simp at hv; rcases hv with rfl | rfl <;> exact ⟨_, rfl⟩
  | _ => trivial

/-- A constant maps to value fields that are all `VCon` (hence `Good`). -/
theorem constToTagAndFields_fields_good {c : Const} {tag numCtors : Nat} {fields : List CekValue}
    (h : constToTagAndFields c = some (tag, numCtors, fields)) : GoodValueList fields := by
  have hvc := constToTagAndFields_fields_vcon c
  rw [h] at hvc
  exact allVcon_good fields hvc

theorem evalBuiltinPassThrough_preserves_good {b : BuiltinFun} {args : List CekValue}
    {v : CekValue} (heval : evalBuiltinPassThrough b args = some v) (hargs : GoodValueList args) :
    GoodValue v := by
  simp only [evalBuiltinPassThrough] at heval
  split at heval
  · -- IfThenElse
    split at heval
    · cases heval; cases hargs with | cons _ h2 => cases h2 with | cons h3 _ => exact h3
    · cases heval; cases hargs with | cons h1 _ => exact h1
  · -- ChooseUnit
    cases heval; cases hargs with | cons h1 _ => exact h1
  · -- Trace
    cases heval; cases hargs with | cons h1 _ => exact h1
  · -- ChooseData
    split at heval <;>
      · cases heval
        cases hargs with | cons h1 h2 =>
        cases h2 with | cons h3 h4 =>
        cases h4 with | cons h5 h6 =>
        cases h6 with | cons h7 h8 =>
        cases h8 with | cons h9 _ =>
        first | exact h9 | exact h7 | exact h5 | exact h3 | exact h1
  · -- ChooseList (ConstDataList)
    split at heval
    · cases heval; cases hargs with | cons _ h2 => cases h2 with | cons h3 _ => exact h3
    · cases heval; cases hargs with | cons h1 _ => exact h1
  · -- ChooseList (ConstList)
    split at heval
    · cases heval; cases hargs with | cons _ h2 => cases h2 with | cons h3 _ => exact h3
    · cases heval; cases hargs with | cons h1 _ => exact h1
  · -- MkCons
    split at heval
    · cases heval; exact .vcon
    · cases heval
  · -- catch-all
    cases heval

theorem evalBuiltin_preserves_good {b : BuiltinFun} {args : List CekValue} {v : CekValue}
    (heval : evalBuiltin b args = some v) (hargs : GoodValueList args) : GoodValue v := by
  simp only [evalBuiltin] at heval
  cases hpt : evalBuiltinPassThrough b args with
  | some w =>
    simp [hpt] at heval; cases heval
    exact evalBuiltinPassThrough_preserves_good hpt hargs
  | none =>
    simp [hpt] at heval
    cases hec : extractConsts args with
    | none => simp [hec] at heval
    | some consts =>
      simp [hec] at heval
      cases hbc : evalBuiltinConst b consts with
      | none => simp [hbc] at heval
      | some c => simp [hbc] at heval; cases heval; exact .vcon


/-! ## The state invariant -/

/-- A stack frame is `Good` when its stored values are `Good` and its stored
    terms are closed under their environments. -/
def GoodFrame : Frame → Prop
  | .force => True
  | .arg M ρ => closedAt ρ.length M = true ∧ GoodEnv ρ
  | .funV vf => GoodValue vf
  | .applyArg vx => GoodValue vx
  | .constrField _ done todo ρ =>
      GoodValueList done ∧ (∀ m ∈ todo, closedAt ρ.length m = true) ∧ GoodEnv ρ
  | .caseScrutinee alts ρ => (∀ m ∈ alts, closedAt ρ.length m = true) ∧ GoodEnv ρ

/-- Every frame on the stack is `Good`. -/
def GoodStack (π : Stack) : Prop := ∀ f ∈ π, GoodFrame f

/-- The whole-state invariant: control/stored terms closed under their
    environments, all stored values `Good`. -/
def GoodState : State → Prop
  | .compute π ρ M => closedAt ρ.length M = true ∧ GoodEnv ρ ∧ GoodStack π
  | .ret π v => GoodValue v ∧ GoodStack π
  | .halt v => GoodValue v
  | .error => True

theorem goodStack_nil : GoodStack [] := fun _ h => by cases h

theorem goodStack_cons {f : Frame} {π : Stack} (hf : GoodFrame f) (hπ : GoodStack π) :
    GoodStack (f :: π) := by
  intro g hg; rcases List.mem_cons.mp hg with rfl | hg
  · exact hf
  · exact hπ g hg

theorem goodStack_head {f : Frame} {π : Stack} (h : GoodStack (f :: π)) : GoodFrame f :=
  h f List.mem_cons_self

theorem goodStack_tail {f : Frame} {π : Stack} (h : GoodStack (f :: π)) : GoodStack π :=
  fun g hg => h g (List.mem_cons_of_mem f hg)

theorem goodValueList_mem_iff {l : List CekValue} : GoodValueList l ↔ ∀ v ∈ l, GoodValue v := by
  constructor
  · intro h v hv; exact goodList_mem h hv
  · intro h
    induction l with
    | nil => exact .nil
    | cons a as ih =>
      exact .cons (h a List.mem_cons_self) (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))

theorem goodValueList_reverse {l : List CekValue} (h : GoodValueList l) : GoodValueList l.reverse := by
  rw [goodValueList_mem_iff] at h ⊢; intro x hx; exact h x (by simpa using hx)

/-- The field-frames produced by a `case`-on-constructor form a `Good` stack. -/
theorem goodStack_applyArgFrames {fields : List CekValue} {s : Stack}
    (hf : GoodValueList fields) (hs : GoodStack s) :
    GoodStack (fields.map Frame.applyArg ++ s) := by
  intro g hg
  rw [List.mem_append] at hg
  rcases hg with hg | hg
  · rw [List.mem_map] at hg
    obtain ⟨v, hv, rfl⟩ := hg
    exact goodList_mem hf hv
  · exact hs g hg

/-! ## Closedness destructuring -/

private theorem closed_lookup_some {ρ : CekEnv} {n : Nat}
    (hM : closedAt ρ.length (.Var n) = true) (hn : 0 < n) : ∃ v, ρ.lookup n = some v := by
  simp only [closedAt, decide_eq_true_eq] at hM
  exact ρ.lookup_some_of_le_length n hn hM

/-! ## `step` preserves the invariant -/

set_option maxHeartbeats 1000000 in
/-- The CEK machine preserves the `Good` state invariant. -/
theorem step_preserves_good : ∀ {s : State}, GoodState s → GoodState (step s)
  | .error, _ => trivial
  | .halt v, h => h
  | .compute π ρ M, h => by
    obtain ⟨hM, hρ, hπ⟩ := h
    cases M with
    | Var n =>
      simp only [step]
      cases hl : ρ.lookup n with
      | none => trivial
      | some v => exact ⟨goodEnv_lookup hρ hl, hπ⟩
    | Constant c => exact ⟨.vcon, hπ⟩
    | Builtin b => exact ⟨.vbuiltin .base .nil, hπ⟩
    | Lam name body =>
      simp only [closedAt] at hM
      exact ⟨.vlam hM hρ, hπ⟩
    | Delay body =>
      simp only [closedAt] at hM
      exact ⟨.vdelay hM hρ, hπ⟩
    | Force e =>
      simp only [closedAt] at hM
      exact ⟨hM, hρ, goodStack_cons trivial hπ⟩
    | Apply f x =>
      simp only [closedAt, Bool.and_eq_true] at hM
      exact ⟨hM.1, hρ, goodStack_cons ⟨hM.2, hρ⟩ hπ⟩
    | Constr tag args =>
      cases args with
      | nil => exact ⟨.vconstr .nil, hπ⟩
      | cons m ms =>
        simp only [closedAt, closedAtList, Bool.and_eq_true] at hM
        refine ⟨hM.1, hρ, goodStack_cons ⟨.nil, ?_, hρ⟩ hπ⟩
        intro k hk; exact (closedAtList_forall hM.2 k hk)
    | Case scrut alts =>
      simp only [closedAt, Bool.and_eq_true] at hM
      refine ⟨hM.1, hρ, goodStack_cons ⟨?_, hρ⟩ hπ⟩
      intro m hm; exact closedAtList_forall hM.2 m hm
    | Error => trivial
  | .ret π v, h => by
    obtain ⟨hv, hπ⟩ := h
    cases π with
    | nil => exact hv
    | cons f s =>
      have hf := goodStack_head hπ
      have hs := goodStack_tail hπ
      cases f with
      | force =>
        cases v with
        | VDelay body ρ' =>
          cases hv with
          | vdelay hb he => simp only [step]; exact ⟨hb, he, hs⟩
        | VBuiltin b args ea =>
          cases hv with
          | vbuiltin hsp ha =>
            simp only [step]
            cases ea with
            | one k =>
              cases k with
              | argQ =>
                simp only [ExpectedArgs.head, ExpectedArgs.tail]
                cases hev : evalBuiltin b args with
                | none => trivial
                | some w => exact ⟨evalBuiltin_preserves_good hev ha, hs⟩
              | argV => trivial
            | more k rest =>
              cases k with
              | argQ =>
                simp only [ExpectedArgs.head, ExpectedArgs.tail]
                exact ⟨.vbuiltin (.force hsp) ha, hs⟩
              | argV => trivial
        | VCon c => trivial
        | VLam body ρ' => trivial
        | VConstr tag fields => trivial
      | arg M ρ' =>
        obtain ⟨hMc, hρ'⟩ := hf
        simp only [step]
        exact ⟨hMc, hρ', goodStack_cons hv hs⟩
      | funV vf =>
        cases vf with
        | VLam body ρ' =>
          cases hf with
          | vlam hb he => simp only [step]; exact ⟨hb, goodEnv_extend he hv, hs⟩
        | VBuiltin b args ea =>
          cases hf with
          | vbuiltin hsp ha =>
            simp only [step]
            cases ea with
            | one k =>
              cases k with
              | argV =>
                simp only [ExpectedArgs.head, ExpectedArgs.tail]
                cases hev : evalBuiltin b (v :: args) with
                | none => trivial
                | some w => exact ⟨evalBuiltin_preserves_good hev (.cons hv ha), hs⟩
              | argQ => trivial
            | more k rest =>
              cases k with
              | argV =>
                simp only [ExpectedArgs.head, ExpectedArgs.tail]
                exact ⟨.vbuiltin (.app hsp) (.cons hv ha), hs⟩
              | argQ => trivial
        | VCon c => simp only [step]; trivial
        | VDelay body ρ' => simp only [step]; trivial
        | VConstr tag fields => simp only [step]; trivial
      | applyArg vx =>
        cases v with
        | VLam body ρ' =>
          cases hv with
          | vlam hb he => simp only [step]; exact ⟨hb, goodEnv_extend he hf, hs⟩
        | VBuiltin b args ea =>
          cases hv with
          | vbuiltin hsp ha =>
            simp only [step]
            cases ea with
            | one k =>
              cases k with
              | argV =>
                simp only [ExpectedArgs.head, ExpectedArgs.tail]
                cases hev : evalBuiltin b (vx :: args) with
                | none => trivial
                | some w => exact ⟨evalBuiltin_preserves_good hev (.cons hf ha), hs⟩
              | argQ => trivial
            | more k rest =>
              cases k with
              | argV =>
                simp only [ExpectedArgs.head, ExpectedArgs.tail]
                exact ⟨.vbuiltin (.app hsp) (.cons hf ha), hs⟩
              | argQ => trivial
        | VCon c => simp only [step]; trivial
        | VDelay body ρ' => simp only [step]; trivial
        | VConstr tag fields => simp only [step]; trivial
      | constrField tag done todo ρ' =>
        obtain ⟨hdone, htodo, hρ'⟩ := hf
        cases todo with
        | nil =>
          simp only [step]
          exact ⟨.vconstr (goodValueList_reverse (.cons hv hdone)), hs⟩
        | cons m ms =>
          simp only [step]
          refine ⟨htodo m List.mem_cons_self, hρ', goodStack_cons ⟨.cons hv hdone, ?_, hρ'⟩ hs⟩
          intro k hk; exact htodo k (List.mem_cons_of_mem m hk)
      | caseScrutinee alts ρ' =>
        obtain ⟨halts, hρ'⟩ := hf
        cases v with
        | VConstr tag fields =>
          cases hv with
          | vconstr hfields =>
            simp only [step]
            cases halt : alts[tag]? with
            | none => trivial
            | some alt =>
              refine ⟨halts alt (List.mem_of_getElem? halt), hρ',
                goodStack_applyArgFrames hfields hs⟩
        | VCon c =>
          simp only [step]
          rcases hc : constToTagAndFields c with _ | ⟨tag, numCtors, fields⟩
          · trivial
          · rw [apply_ite GoodState]
            split
            · trivial
            · cases halt : alts[tag]? with
              | none => trivial
              | some alt =>
                exact ⟨halts alt (List.mem_of_getElem? halt), hρ',
                  goodStack_applyArgFrames (constToTagAndFields_fields_good hc) hs⟩
        | VLam body ρ'' => simp only [step]; trivial
        | VDelay body ρ'' => simp only [step]; trivial
        | VBuiltin b args ea => simp only [step]; trivial

/-- The initial state of a closed term satisfies the invariant. -/
theorem init_good {t : Term} (ht : closedAt 0 t = true) : GoodState (init t) := by
  refine ⟨?_, .nil, goodStack_nil⟩
  simpa [CekEnv.length] using ht

end Moist.Verified.SmallStep
