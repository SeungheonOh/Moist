import Moist.Verified.Semantics
import Moist.Verified.StepLift
import Moist.Verified.Congruence
import Moist.Verified.ClosedAt
import Moist.CEK.Builtins

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

/-! # CEK State Bisimulation with Structural Value Equivalence

Uses a structural `ValEqAll` relation (same body + structurally related
envs for closures) to break the circularity that arises with step-indexed
`ValueEq` in ret/halt states. `step_preserves` is purely structural.
Then `valEqAll_implies_valueEq` derives the step-indexed relation from
the already-proved simulation.
-/

namespace Moist.Verified.BisimEq

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified.Semantics
open Moist.Verified.StepLift

/-! ## Structural Value/Env Equivalence -/

mutual
  def ValEqAll : CekValue → CekValue → Prop
    | .VCon c1, .VCon c2 => c1 = c2
    | .VLam b1 e1, .VLam b2 e2 => b1 = b2 ∧ EnvEqAll e1 e2
    | .VDelay b1 e1, .VDelay b2 e2 => b1 = b2 ∧ EnvEqAll e1 e2
    | .VConstr t1 fs1, .VConstr t2 fs2 => t1 = t2 ∧ ListValEqAll fs1 fs2
    | .VBuiltin b1 a1 ea1, .VBuiltin b2 a2 ea2 => b1 = b2 ∧ ListValEqAll a1 a2 ∧ ea1 = ea2
    | _, _ => False

  def ListValEqAll : List CekValue → List CekValue → Prop
    | [], [] => True
    | a :: as, b :: bs => ValEqAll a b ∧ ListValEqAll as bs
    | _, _ => False

  def EnvEqAll : CekEnv → CekEnv → Prop
    | .nil, .nil => True
    | .cons v1 e1, .cons v2 e2 => ValEqAll v1 v2 ∧ EnvEqAll e1 e2
    | _, _ => False
end

/-! ## Reflexivity and symmetry -/

mutual
  theorem valEqAll_refl : ∀ (v : CekValue), ValEqAll v v
    | .VCon _ => by simp [ValEqAll]
    | .VLam _ e => by simp [ValEqAll]; exact envEqAll_refl e
    | .VDelay _ e => by simp [ValEqAll]; exact envEqAll_refl e
    | .VConstr _ fs => by simp [ValEqAll]; exact listValEqAll_refl fs
    | .VBuiltin _ args _ => by simp [ValEqAll]; exact listValEqAll_refl args

  theorem listValEqAll_refl : ∀ (vs : List CekValue), ListValEqAll vs vs
    | [] => by simp [ListValEqAll]
    | v :: vs => by simp [ListValEqAll]; exact ⟨valEqAll_refl v, listValEqAll_refl vs⟩

  theorem envEqAll_refl : ∀ (env : CekEnv), EnvEqAll env env
    | .nil => by simp [EnvEqAll]
    | .cons v e => by simp [EnvEqAll]; exact ⟨valEqAll_refl v, envEqAll_refl e⟩
end

mutual
  theorem valEqAll_symm : ∀ (v1 v2 : CekValue), ValEqAll v1 v2 → ValEqAll v2 v1
    | .VCon _, .VCon _, h => by simp [ValEqAll] at h ⊢; exact h.symm
    | .VLam _ _, .VLam _ _, h => by simp [ValEqAll] at h ⊢; exact ⟨h.1.symm, envEqAll_symm _ _ h.2⟩
    | .VDelay _ _, .VDelay _ _, h => by simp [ValEqAll] at h ⊢; exact ⟨h.1.symm, envEqAll_symm _ _ h.2⟩
    | .VConstr _ _, .VConstr _ _, h => by
        simp [ValEqAll] at h ⊢; exact ⟨h.1.symm, listValEqAll_symm _ _ h.2⟩
    | .VBuiltin _ _ _, .VBuiltin _ _ _, h => by
        simp [ValEqAll] at h ⊢; exact ⟨h.1.symm, listValEqAll_symm _ _ h.2.1, h.2.2.symm⟩
    | .VCon _, .VLam _ _, h => by simp [ValEqAll] at h
    | .VCon _, .VDelay _ _, h => by simp [ValEqAll] at h
    | .VCon _, .VConstr _ _, h => by simp [ValEqAll] at h
    | .VCon _, .VBuiltin _ _ _, h => by simp [ValEqAll] at h
    | .VLam _ _, .VCon _, h => by simp [ValEqAll] at h
    | .VLam _ _, .VDelay _ _, h => by simp [ValEqAll] at h
    | .VLam _ _, .VConstr _ _, h => by simp [ValEqAll] at h
    | .VLam _ _, .VBuiltin _ _ _, h => by simp [ValEqAll] at h
    | .VDelay _ _, .VCon _, h => by simp [ValEqAll] at h
    | .VDelay _ _, .VLam _ _, h => by simp [ValEqAll] at h
    | .VDelay _ _, .VConstr _ _, h => by simp [ValEqAll] at h
    | .VDelay _ _, .VBuiltin _ _ _, h => by simp [ValEqAll] at h
    | .VConstr _ _, .VCon _, h => by simp [ValEqAll] at h
    | .VConstr _ _, .VLam _ _, h => by simp [ValEqAll] at h
    | .VConstr _ _, .VDelay _ _, h => by simp [ValEqAll] at h
    | .VConstr _ _, .VBuiltin _ _ _, h => by simp [ValEqAll] at h
    | .VBuiltin _ _ _, .VCon _, h => by simp [ValEqAll] at h
    | .VBuiltin _ _ _, .VLam _ _, h => by simp [ValEqAll] at h
    | .VBuiltin _ _ _, .VDelay _ _, h => by simp [ValEqAll] at h
    | .VBuiltin _ _ _, .VConstr _ _, h => by simp [ValEqAll] at h

  theorem listValEqAll_symm : ∀ (vs1 vs2 : List CekValue),
      ListValEqAll vs1 vs2 → ListValEqAll vs2 vs1
    | [], [], _ => by simp [ListValEqAll]
    | _ :: _, _ :: _, h => by
        simp [ListValEqAll] at h ⊢; exact ⟨valEqAll_symm _ _ h.1, listValEqAll_symm _ _ h.2⟩
    | [], _ :: _, h => by simp [ListValEqAll] at h
    | _ :: _, [], h => by simp [ListValEqAll] at h

  theorem envEqAll_symm : ∀ (env1 env2 : CekEnv), EnvEqAll env1 env2 → EnvEqAll env2 env1
    | .nil, .nil, _ => by simp [EnvEqAll]
    | .cons _ _, .cons _ _, h => by
        simp [EnvEqAll] at h ⊢; exact ⟨valEqAll_symm _ _ h.1, envEqAll_symm _ _ h.2⟩
    | .nil, .cons _ _, h => by simp [EnvEqAll] at h
    | .cons _ _, .nil, h => by simp [EnvEqAll] at h
end

/-! ## Env operations -/

theorem envEqAll_extend {env1 env2 : CekEnv} {v1 v2 : CekValue}
    (he : EnvEqAll env1 env2) (hv : ValEqAll v1 v2) :
    EnvEqAll (env1.extend v1) (env2.extend v2) := by
  show EnvEqAll (.cons v1 env1) (.cons v2 env2)
  simp [EnvEqAll]; exact ⟨hv, he⟩

theorem envEqAll_lookup : ∀ {env1 env2 : CekEnv}, EnvEqAll env1 env2 → ∀ (n : Nat),
    match env1.lookup n, env2.lookup n with
    | some v1, some v2 => ValEqAll v1 v2
    | none, none => True
    | _, _ => False
  | .nil, .nil, _, n => by cases n <;> simp [CekEnv.lookup]
  | .nil, .cons _ _, h, _ => by simp [EnvEqAll] at h
  | .cons _ _, .nil, h, _ => by simp [EnvEqAll] at h
  | .cons v1 e1, .cons v2 e2, h, n => by
    simp [EnvEqAll] at h; obtain ⟨hv, he'⟩ := h
    match n with
    | 0 => simp [CekEnv.lookup]
    | 1 => simp [CekEnv.lookup]; exact hv
    | n + 2 => simp [CekEnv.lookup]; exact envEqAll_lookup he' (n + 1)

/-! ## Frame, Stack, State equivalence -/

inductive FrameEq : Frame → Frame → Prop
  | arg (t : Term) {env1 env2 : CekEnv} (h : EnvEqAll env1 env2) :
      FrameEq (.arg t env1) (.arg t env2)
  | funV {v1 v2 : CekValue} (h : ValEqAll v1 v2) :
      FrameEq (.funV v1) (.funV v2)
  | force : FrameEq .force .force
  | constrField (tag : Nat) {done1 done2 : List CekValue} (rest : List Term)
      {env1 env2 : CekEnv} (hd : ListValEqAll done1 done2) (he : EnvEqAll env1 env2) :
      FrameEq (.constrField tag done1 rest env1) (.constrField tag done2 rest env2)
  | caseScrutinee (alts : List Term) {env1 env2 : CekEnv} (h : EnvEqAll env1 env2) :
      FrameEq (.caseScrutinee alts env1) (.caseScrutinee alts env2)
  | applyArg {v1 v2 : CekValue} (h : ValEqAll v1 v2) :
      FrameEq (.applyArg v1) (.applyArg v2)

inductive StackEq : Stack → Stack → Prop
  | nil : StackEq [] []
  | cons {f1 f2 : Frame} {s1 s2 : Stack} (hf : FrameEq f1 f2) (hs : StackEq s1 s2) :
      StackEq (f1 :: s1) (f2 :: s2)

inductive StateEq : State → State → Prop
  | compute {stk1 stk2 : Stack} {env1 env2 : CekEnv} (t : Term)
      (hs : StackEq stk1 stk2) (he : EnvEqAll env1 env2) :
      StateEq (.compute stk1 env1 t) (.compute stk2 env2 t)
  | ret {stk1 stk2 : Stack} {v1 v2 : CekValue}
      (hs : StackEq stk1 stk2) (hv : ValEqAll v1 v2) :
      StateEq (.ret stk1 v1) (.ret stk2 v2)
  | halt {v1 v2 : CekValue} (hv : ValEqAll v1 v2) :
      StateEq (.halt v1) (.halt v2)
  | error : StateEq .error .error

/-! ## List/Stack helpers -/

theorem listValEqAll_append {a1 a2 b1 b2 : List CekValue}
    (ha : ListValEqAll a1 a2) (hb : ListValEqAll b1 b2) :
    ListValEqAll (a1 ++ b1) (a2 ++ b2) := by
  induction a1 generalizing a2 with
  | nil =>
    cases a2 with
    | nil => simp; exact hb
    | cons _ _ => simp [ListValEqAll] at ha
  | cons x xs ih =>
    cases a2 with
    | nil => simp [ListValEqAll] at ha
    | cons y ys =>
      simp [ListValEqAll] at ha ⊢; exact ⟨ha.1, ih ha.2⟩

theorem listValEqAll_reverse {a1 a2 : List CekValue}
    (h : ListValEqAll a1 a2) :
    ListValEqAll a1.reverse a2.reverse := by
  induction a1 generalizing a2 with
  | nil =>
    cases a2 with
    | nil => simp [ListValEqAll]
    | cons _ _ => simp [ListValEqAll] at h
  | cons x xs ih =>
    cases a2 with
    | nil => simp [ListValEqAll] at h
    | cons y ys =>
      simp [ListValEqAll] at h
      simp [List.reverse_cons]
      exact listValEqAll_append (ih h.2) ⟨h.1, by simp [ListValEqAll]⟩

theorem listValEqAll_cons_rev {v1 v2 : CekValue} {done1 done2 : List CekValue}
    (hv : ValEqAll v1 v2) (hd : ListValEqAll done1 done2) :
    ListValEqAll ((v1 :: done1).reverse) ((v2 :: done2).reverse) := by
  simp [List.reverse_cons]
  exact listValEqAll_append (listValEqAll_reverse hd) ⟨hv, by simp [ListValEqAll]⟩

theorem listValEqAll_map_applyArg {fs1 fs2 : List CekValue}
    (h : ListValEqAll fs1 fs2) :
    StackEq (fs1.map Frame.applyArg) (fs2.map Frame.applyArg) := by
  induction fs1 generalizing fs2 with
  | nil =>
    cases fs2 with
    | nil => exact .nil
    | cons _ _ => simp [ListValEqAll] at h
  | cons f1 fs1' ih =>
    cases fs2 with
    | nil => simp [ListValEqAll] at h
    | cons f2 fs2' =>
      simp [ListValEqAll] at h; exact .cons (.applyArg h.1) (ih h.2)

theorem stackEq_append : ∀ {s1 s2 t1 t2 : Stack},
    StackEq s1 s2 → StackEq t1 t2 → StackEq (s1 ++ t1) (s2 ++ t2)
  | [], [], _, _, .nil, ht => ht
  | _ :: _, _ :: _, _, _, .cons hf hs, ht => .cons hf (stackEq_append hs ht)

/-! ## evalBuiltin with ValEqAll -/

private theorem extractConsts_valEqAll {args1 args2 : List CekValue}
    (h : ListValEqAll args1 args2) :
    extractConsts args1 = extractConsts args2 := by
  induction args1 generalizing args2 with
  | nil =>
    cases args2 with
    | nil => rfl
    | cons _ _ => simp [ListValEqAll] at h
  | cons a1 as1 ih =>
    cases args2 with
    | nil => simp [ListValEqAll] at h
    | cons a2 as2 =>
      simp [ListValEqAll] at h; obtain ⟨ha, has⟩ := h
      have ih_eq := ih has
      cases a1 <;> cases a2 <;> simp_all [ValEqAll, extractConsts, bind, Option.bind]

/-- ListValEqAll implies equal length. -/
theorem listValEqAll_length : ∀ {l1 l2 : List CekValue},
    ListValEqAll l1 l2 → l1.length = l2.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp [ListValEqAll] at h; simp [List.length_cons]; exact listValEqAll_length h.2
  | [], _ :: _, h => by simp [ListValEqAll] at h
  | _ :: _, [], h => by simp [ListValEqAll] at h

/-- ValEqAll preserves the VCon "skeleton": both values are VCon with equal
    constants, or both are the same non-VCon constructor. -/
private theorem listValEqAll_all_vcon_eq : ∀ {args1 args2 : List CekValue},
    ListValEqAll args1 args2 →
    (∀ v ∈ args1, ∃ c, v = .VCon c) → args1 = args2
  | [], [], _, _ => rfl
  | a1 :: as1, a2 :: as2, h, hall => by
    simp [ListValEqAll] at h; obtain ⟨ha, has⟩ := h
    have ⟨c, hc⟩ := hall a1 (List.Mem.head _)
    subst hc; cases a2 <;> simp [ValEqAll] at ha
    subst ha; congr 1
    exact listValEqAll_all_vcon_eq has (fun v hm => hall v (List.Mem.tail _ hm))
  | [], _ :: _, h, _ => by simp [ListValEqAll] at h
  | _ :: _, [], h, _ => by simp [ListValEqAll] at h

private def isVCon : CekValue → Bool
  | .VCon _ => true
  | _ => false

private theorem valEqAll_isVCon {v1 v2 : CekValue} (h : ValEqAll v1 v2) :
    isVCon v1 = isVCon v2 := by
  cases v1 <;> cases v2 <;> simp_all [ValEqAll, isVCon]


-- Helper: extract ValEqAll from length-2 ListValEqAll.
private theorem listValEqAll_2_inv {a1 b1 a2 b2 : CekValue}
    (h : ListValEqAll [a1, b1] [a2, b2]) : ValEqAll a1 a2 ∧ ValEqAll b1 b2 := by
  simp [ListValEqAll] at h; exact ⟨h.1, h.2⟩

-- Helper: extract ValEqAll from length-3 ListValEqAll.
private theorem listValEqAll_3_inv {a1 b1 c1 a2 b2 c2 : CekValue}
    (h : ListValEqAll [a1, b1, c1] [a2, b2, c2]) :
    ValEqAll a1 a2 ∧ ValEqAll b1 b2 ∧ ValEqAll c1 c2 := by
  simp [ListValEqAll] at h; exact ⟨h.1, h.2.1, h.2.2⟩

-- Helper: extract ValEqAll from length-6 ListValEqAll.
private theorem listValEqAll_6_inv
    {a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 : CekValue}
    (h : ListValEqAll [a1, b1, c1, d1, e1, f1] [a2, b2, c2, d2, e2, f2]) :
    ValEqAll a1 a2 ∧ ValEqAll b1 b2 ∧ ValEqAll c1 c2 ∧
    ValEqAll d1 d2 ∧ ValEqAll e1 e2 ∧ ValEqAll f1 f2 := by
  simp [ListValEqAll] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

-- Helper to discharge a single-element ValEqAll match:
-- case-split both v1 and v2 on their constructor; mismatched → simp [ValEqAll] gives False.
-- matched, non-VCon → both evals return none → simp closes.
-- matched, VCon → same const → simp (with subst) closes or leaves a simple goal.

private theorem evalBuiltinPassThrough_coherent (b : BuiltinFun)
    {args1 args2 : List CekValue} (h : ListValEqAll args1 args2) :
    match evalBuiltinPassThrough b args1, evalBuiltinPassThrough b args2 with
    | some v1, some v2 => ValEqAll v1 v2
    | none, none => True
    | _, _ => False := by
  -- For all non-passthrough builtins, evalBuiltinPassThrough returns none → True.
  -- For the 6 passthrough builtins, we case-split on b, then on args1/args2 shapes.
  -- ListValEqAll forces same length and matching constructors at each position.
  -- After substing the condition element (c2 = c1), both evals reduce identically.
  cases b <;> simp only [evalBuiltinPassThrough] <;> try trivial
  -- Remaining 6 goals: IfThenElse, ChooseUnit, Trace, ChooseData, ChooseList, MkCons.
  case IfThenElse =>
    -- Pattern: [elseV, thenV, VCon (Bool cond)] → some (if cond then thenV else elseV)
    match args1, args2, h with
    | [], [], _ | [_], [_], _ | [_, _], [_, _], _ => trivial
    | [a1, b1, c1], [a2, b2, c2], h1 =>
      obtain ⟨ha, hb, hc⟩ := listValEqAll_3_inv h1
      cases c1 with
      | VCon cc1 =>
        cases c2 with
        | VCon cc2 =>
          simp only [ValEqAll] at hc; subst hc
          cases cc1 with
          | Bool cond => simp; cases cond <;> assumption
          | _ => simp
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
          simp [ValEqAll] at hc
      | VLam _ _ =>
        cases c2 with
        | VLam _ _ => simp
        | VCon _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => simp [ValEqAll] at hc
      | VDelay _ _ =>
        cases c2 with
        | VDelay _ _ => simp
        | VCon _ | VLam _ _ | VConstr _ _ | VBuiltin _ _ _ => simp [ValEqAll] at hc
      | VConstr _ _ =>
        cases c2 with
        | VConstr _ _ => simp
        | VCon _ | VLam _ _ | VDelay _ _ | VBuiltin _ _ _ => simp [ValEqAll] at hc
      | VBuiltin _ _ _ =>
        cases c2 with
        | VBuiltin _ _ _ => simp
        | VCon _ | VLam _ _ | VDelay _ _ | VConstr _ _ => simp [ValEqAll] at hc
    | _ :: _ :: _ :: _ :: _, _ :: _ :: _ :: _ :: _, _ => simp [evalBuiltinPassThrough]
    | [], _ :: _, h1 | _ :: _, [], h1 | [_], _ :: _ :: _, h1
    | _ :: _ :: _, [_], h1 | [_, _], _ :: _ :: _ :: _, h1
    | _ :: _ :: _ :: _, [_, _], h1 | [_, _, _], _ :: _ :: _ :: _ :: _, h1
    | _ :: _ :: _ :: _ :: _, [_, _, _], h1 => simp [ListValEqAll] at h1
  case ChooseUnit =>
    -- Pattern: [result, VCon Unit] → some result
    match args1, args2, h with
    | [], [], _ | [_], [_], _ => trivial
    | [a1, b1], [a2, b2], h1 =>
      obtain ⟨ha, hb⟩ := listValEqAll_2_inv h1
      cases b1 with
      | VCon cb1 =>
        cases b2 with
        | VCon cb2 =>
          simp only [ValEqAll] at hb; subst hb
          cases cb1 with
          | Unit => simp; exact ha
          | _ => simp
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
          simp [ValEqAll] at hb
      | VLam _ _ =>
        cases b2 with
        | VLam _ _ => simp
        | VCon _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => simp [ValEqAll] at hb
      | VDelay _ _ =>
        cases b2 with
        | VDelay _ _ => simp
        | VCon _ | VLam _ _ | VConstr _ _ | VBuiltin _ _ _ => simp [ValEqAll] at hb
      | VConstr _ _ =>
        cases b2 with
        | VConstr _ _ => simp
        | VCon _ | VLam _ _ | VDelay _ _ | VBuiltin _ _ _ => simp [ValEqAll] at hb
      | VBuiltin _ _ _ =>
        cases b2 with
        | VBuiltin _ _ _ => simp
        | VCon _ | VLam _ _ | VDelay _ _ | VConstr _ _ => simp [ValEqAll] at hb
    | _ :: _ :: _ :: _, _ :: _ :: _ :: _, _ => simp [evalBuiltinPassThrough]
    | [], _ :: _, h1 | _ :: _, [], h1 | [_], _ :: _ :: _, h1
    | _ :: _ :: _, [_], h1 => simp [ListValEqAll] at h1
  case Trace =>
    -- Pattern: [result, VCon (String s)] → some result
    match args1, args2, h with
    | [], [], _ | [_], [_], _ => trivial
    | [a1, b1], [a2, b2], h1 =>
      obtain ⟨ha, hb⟩ := listValEqAll_2_inv h1
      cases b1 with
      | VCon cb1 =>
        cases b2 with
        | VCon cb2 =>
          simp only [ValEqAll] at hb; subst hb
          cases cb1 with
          | String _ => simp; exact ha
          | _ => simp
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
          simp [ValEqAll] at hb
      | VLam _ _ =>
        cases b2 with
        | VLam _ _ => simp
        | VCon _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => simp [ValEqAll] at hb
      | VDelay _ _ =>
        cases b2 with
        | VDelay _ _ => simp
        | VCon _ | VLam _ _ | VConstr _ _ | VBuiltin _ _ _ => simp [ValEqAll] at hb
      | VConstr _ _ =>
        cases b2 with
        | VConstr _ _ => simp
        | VCon _ | VLam _ _ | VDelay _ _ | VBuiltin _ _ _ => simp [ValEqAll] at hb
      | VBuiltin _ _ _ =>
        cases b2 with
        | VBuiltin _ _ _ => simp
        | VCon _ | VLam _ _ | VDelay _ _ | VConstr _ _ => simp [ValEqAll] at hb
    | _ :: _ :: _ :: _, _ :: _ :: _ :: _, _ => simp [evalBuiltinPassThrough]
    | [], _ :: _, h1 | _ :: _, [], h1 | [_], _ :: _ :: _, h1
    | _ :: _ :: _, [_], h1 => simp [ListValEqAll] at h1
  case ChooseData =>
    -- Pattern: [bCase, iCase, listCase, mapCase, constrCase, VCon (Data d)]
    match args1, args2, h with
    | [], [], _ | [_], [_], _ | [_, _], [_, _], _
    | [_, _, _], [_, _, _], _ | [_, _, _, _], [_, _, _, _], _
    | [_, _, _, _, _], [_, _, _, _, _], _ => trivial
    | [a1, b1, c1, d1, e1, f1], [a2, b2, c2, d2, e2, f2], h1 =>
      obtain ⟨ha, hb, hc, hd, he, hf⟩ := listValEqAll_6_inv h1
      cases f1 with
      | VCon cf1 =>
        cases f2 with
        | VCon cf2 =>
          simp only [ValEqAll] at hf; subst hf
          cases cf1 with
          | Data dv => simp; cases dv <;> assumption
          | _ => simp
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
          simp [ValEqAll] at hf
      | VLam _ _ =>
        cases f2 with
        | VLam _ _ => simp
        | VCon _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => simp [ValEqAll] at hf
      | VDelay _ _ =>
        cases f2 with
        | VDelay _ _ => simp
        | VCon _ | VLam _ _ | VConstr _ _ | VBuiltin _ _ _ => simp [ValEqAll] at hf
      | VConstr _ _ =>
        cases f2 with
        | VConstr _ _ => simp
        | VCon _ | VLam _ _ | VDelay _ _ | VBuiltin _ _ _ => simp [ValEqAll] at hf
      | VBuiltin _ _ _ =>
        cases f2 with
        | VBuiltin _ _ _ => simp
        | VCon _ | VLam _ _ | VDelay _ _ | VConstr _ _ => simp [ValEqAll] at hf
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, _ =>
        simp [evalBuiltinPassThrough]
    | [], _ :: _, h1 | _ :: _, [], h1 | [_], _ :: _ :: _, h1
    | _ :: _ :: _, [_], h1 | [_, _], _ :: _ :: _ :: _, h1
    | _ :: _ :: _ :: _, [_, _], h1 | [_, _, _], _ :: _ :: _ :: _ :: _, h1
    | _ :: _ :: _ :: _ :: _, [_, _, _], h1 | [_, _, _, _], _ :: _ :: _ :: _ :: _ :: _, h1
    | _ :: _ :: _ :: _ :: _ :: _, [_, _, _, _], h1
    | [_, _, _, _, _], _ :: _ :: _ :: _ :: _ :: _ :: _, h1
    | _ :: _ :: _ :: _ :: _ :: _ :: _, [_, _, _, _, _], h1 => simp [ListValEqAll] at h1
  case ChooseList =>
    -- Patterns: [consCase, nilCase, VCon (ConstDataList l)] or [consCase, nilCase, VCon (ConstList l)]
    match args1, args2, h with
    | [], [], _ | [_], [_], _ | [_, _], [_, _], _ => trivial
    | [a1, b1, c1], [a2, b2, c2], h1 =>
      obtain ⟨ha, hb, hc⟩ := listValEqAll_3_inv h1
      cases c1 with
      | VCon cc1 =>
        cases c2 with
        | VCon cc2 =>
          simp only [ValEqAll] at hc; subst hc
          cases cc1 with
          | ConstDataList _ => simp; split <;> assumption
          | ConstList _ => simp; split <;> assumption
          | _ => simp
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
          simp [ValEqAll] at hc
      | VLam _ _ =>
        cases c2 with
        | VLam _ _ => simp
        | VCon _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => simp [ValEqAll] at hc
      | VDelay _ _ =>
        cases c2 with
        | VDelay _ _ => simp
        | VCon _ | VLam _ _ | VConstr _ _ | VBuiltin _ _ _ => simp [ValEqAll] at hc
      | VConstr _ _ =>
        cases c2 with
        | VConstr _ _ => simp
        | VCon _ | VLam _ _ | VDelay _ _ | VBuiltin _ _ _ => simp [ValEqAll] at hc
      | VBuiltin _ _ _ =>
        cases c2 with
        | VBuiltin _ _ _ => simp
        | VCon _ | VLam _ _ | VDelay _ _ | VConstr _ _ => simp [ValEqAll] at hc
    | _ :: _ :: _ :: _ :: _, _ :: _ :: _ :: _ :: _, _ => simp [evalBuiltinPassThrough]
    | [], _ :: _, h1 | _ :: _, [], h1 | [_], _ :: _ :: _, h1
    | _ :: _ :: _, [_], h1 | [_, _], _ :: _ :: _ :: _, h1
    | _ :: _ :: _ :: _, [_, _], h1 | [_, _, _], _ :: _ :: _ :: _ :: _, h1
    | _ :: _ :: _ :: _ :: _, [_, _, _], h1 => simp [ListValEqAll] at h1
  case MkCons =>
    -- Pattern: [VCon (ConstList tail), elem] with elem = VCon c → VCon (ConstList (c :: tail))
    match args1, args2, h with
    | [], [], _ => trivial
    | [_], [_], _ => simp [evalBuiltinPassThrough]
    | [a1, b1], [a2, b2], h1 =>
      obtain ⟨ha, hb⟩ := listValEqAll_2_inv h1
      cases a1 with
      | VCon ca1 =>
        cases a2 with
        | VCon ca2 =>
          simp only [ValEqAll] at ha; subst ha
          cases ca1 with
          | ConstList tail =>
            -- b1 must be VCon for the inner match
            cases b1 with
            | VCon cb1 =>
              cases b2 with
              | VCon cb2 =>
                simp only [ValEqAll] at hb; subst hb; simp [ValEqAll]
              | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
                simp [ValEqAll] at hb
            | VLam _ _ =>
              cases b2 with
              | VCon _ => simp [ValEqAll] at hb
              | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => simp [evalBuiltinPassThrough]
            | VDelay _ _ =>
              cases b2 with
              | VCon _ => simp [ValEqAll] at hb
              | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => simp [evalBuiltinPassThrough]
            | VConstr _ _ =>
              cases b2 with
              | VCon _ => simp [ValEqAll] at hb
              | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => simp [evalBuiltinPassThrough]
            | VBuiltin _ _ _ =>
              cases b2 with
              | VCon _ => simp [ValEqAll] at hb
              | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => simp [evalBuiltinPassThrough]
          | _ => simp
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
          simp [ValEqAll] at ha
      | VLam _ _ =>
        cases a2 with
        | VLam _ _ => simp [evalBuiltinPassThrough]
        | VCon _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => simp [ValEqAll] at ha
      | VDelay _ _ =>
        cases a2 with
        | VDelay _ _ => simp [evalBuiltinPassThrough]
        | VCon _ | VLam _ _ | VConstr _ _ | VBuiltin _ _ _ => simp [ValEqAll] at ha
      | VConstr _ _ =>
        cases a2 with
        | VConstr _ _ => simp [evalBuiltinPassThrough]
        | VCon _ | VLam _ _ | VDelay _ _ | VBuiltin _ _ _ => simp [ValEqAll] at ha
      | VBuiltin _ _ _ =>
        cases a2 with
        | VBuiltin _ _ _ => simp [evalBuiltinPassThrough]
        | VCon _ | VLam _ _ | VDelay _ _ | VConstr _ _ => simp [ValEqAll] at ha
    | _ :: _ :: _ :: _, _ :: _ :: _ :: _, _ => simp [evalBuiltinPassThrough]
    | [], _ :: _, h1 | _ :: _, [], h1 | [_], _ :: _ :: _, h1
    | _ :: _ :: _, [_], h1 => simp [ListValEqAll] at h1


/-- evalBuiltin congruence under ListValEqAll.
    If all args are VCon, they're equal on both sides → same result.
    Otherwise, uses pass-through coherence + extractConsts equality. -/
theorem evalBuiltin_valEqAll (b : BuiltinFun) {args1 args2 : List CekValue}
    (hargs : ListValEqAll args1 args2) :
    match evalBuiltin b args1, evalBuiltin b args2 with
    | some v1, some v2 => ValEqAll v1 v2
    | none, none => True
    | _, _ => False := by
  simp only [evalBuiltin]
  have hpt := evalBuiltinPassThrough_coherent b hargs
  have hec := extractConsts_valEqAll hargs
  generalize hp1 : evalBuiltinPassThrough b args1 = r1 at hpt
  generalize hp2 : evalBuiltinPassThrough b args2 = r2 at hpt
  cases r1 with
  | some v1 =>
    cases r2 with
    | some v2 => exact hpt
    | none => exact absurd hpt id
  | none =>
    cases r2 with
    | some _ => exact absurd hpt id
    | none =>
      -- Both pass-through returned none. Fall back to extractConsts path.
      generalize he1 : extractConsts args1 = ec1
      generalize he2 : extractConsts args2 = ec2
      have heq : ec1 = ec2 := by rw [← he1, ← he2]; exact hec
      subst heq
      cases ec1 with
      | none => dsimp
      | some cs =>
        dsimp
        cases evalBuiltinConst b cs with
        | none => dsimp
        | some c => dsimp; simp [ValEqAll]

private theorem ret_evalBuiltin_stateEq
    {b : BuiltinFun} {args1 args2 : List CekValue} {s1 s2 : Stack}
    (hargs : ListValEqAll args1 args2) (hrest : StackEq s1 s2) :
    StateEq
      (match evalBuiltin b args1 with | some v => .ret s1 v | none => .error)
      (match evalBuiltin b args2 with | some v => .ret s2 v | none => .error) := by
  have h := evalBuiltin_valEqAll b hargs
  generalize evalBuiltin b args1 = r1 at h
  generalize evalBuiltin b args2 = r2 at h
  cases r1 with
  | some v1 => cases r2 with
    | some v2 => exact .ret hrest h
    | none => exact absurd h id
  | none => cases r2 with
    | some _ => exact absurd h id
    | none => exact .error

/-! ## Step preservation -/

theorem step_preserves {s1 s2 : State} (h : StateEq s1 s2) :
    StateEq (step s1) (step s2) := by
  cases h with
  | error => exact .error
  | halt hv => exact .halt hv
  | compute t hs he =>
    cases t with
    | Var n =>
      simp only [step]
      have hlookup := envEqAll_lookup he n
      generalize h1 : CekEnv.lookup _ n = r1 at hlookup
      generalize h2 : CekEnv.lookup _ n = r2 at hlookup
      cases r1 with
      | some v1 => cases r2 with
        | some v2 => exact .ret hs hlookup
        | none => exact absurd hlookup id
      | none => cases r2 with
        | some _ => exact absurd hlookup id
        | none => exact .error
    | Constant p => obtain ⟨c, ty⟩ := p; simp only [step]; exact .ret hs (by simp [ValEqAll])
    | Builtin b => simp only [step]; exact .ret hs (by simp [ValEqAll, ListValEqAll])
    | Lam n body => simp only [step]; exact .ret hs ⟨rfl, he⟩
    | Delay body => simp only [step]; exact .ret hs ⟨rfl, he⟩
    | Force e => simp only [step]; exact .compute e (.cons .force hs) he
    | Apply f x => simp only [step]; exact .compute f (.cons (.arg x he) hs) he
    | Constr tag args =>
      simp only [step]
      cases args with
      | nil => exact .ret hs ⟨rfl, by simp [ListValEqAll]⟩
      | cons m ms =>
        exact .compute m (.cons (.constrField tag ms (by simp [ListValEqAll]) he) hs) he
    | Case scrut alts =>
      simp only [step]; exact .compute scrut (.cons (.caseScrutinee alts he) hs) he
    | Error => simp only [step]; exact .error

  | ret hs hv =>
    cases hs with
    | nil => simp only [step]; exact .halt hv
    | cons hf hrest =>
      cases hf with
      | force =>
        -- hv : ValEqAll v1 v2
        -- Use a helper to avoid `cases` on mutually-inductive CekValue
        exact step_ret_force hv hrest
      | arg t he' =>
        simp only [step]; exact .compute t (.cons (.funV hv) hrest) he'
      | funV hv_fun =>
        exact step_ret_funV hv_fun hv hrest
      | applyArg hv_arg =>
        exact step_ret_applyArg hv hv_arg hrest
      | constrField tag rest hd he' =>
        cases rest with
        | cons m ms =>
          simp only [step]
          exact .compute m (.cons (.constrField tag ms ⟨hv, hd⟩ he') hrest) he'
        | nil =>
          simp only [step]
          exact .ret hrest ⟨rfl, listValEqAll_cons_rev hv hd⟩
      | caseScrutinee alts he' =>
        exact step_ret_case hv he' hrest alts
where
  step_ret_force {v1 v2 : CekValue} {s1 s2 : Stack}
      (hv : ValEqAll v1 v2) (hrest : StackEq s1 s2) :
      StateEq (step (.ret (.force :: s1) v1)) (step (.ret (.force :: s2) v2)) := by
    cases v1 <;> cases v2 <;> simp_all [ValEqAll]
    · -- VCon, VCon
      simp only [step]; exact .error
    · -- VDelay, VDelay
      rename_i body1 env1 body2 env2
      obtain ⟨hb, henv⟩ := ‹_›; subst hb; simp only [step]; exact .compute body1 hrest henv
    · -- VLam, VLam
      simp only [step]; exact .error
    · -- VConstr, VConstr
      simp only [step]; exact .error
    · -- VBuiltin, VBuiltin
      rename_i b1 args1 ea1 b2 args2 ea2
      obtain ⟨hb, hargs, hea⟩ := ‹b1 = b2 ∧ _›; subst hb; subst hea
      simp only [step]
      cases h_head : ExpectedArgs.head ea1 with
      | argQ =>
        simp [h_head]; cases h_tail : ExpectedArgs.tail ea1 with
        | some rest => simp [h_tail]; exact .ret hrest ⟨rfl, hargs, rfl⟩
        | none => simp [h_tail]; exact ret_evalBuiltin_stateEq hargs hrest
      | argV => simp [h_head]; exact .error
  step_ret_funV {vfun1 vfun2 varg1 varg2 : CekValue} {s1 s2 : Stack}
      (hv_fun : ValEqAll vfun1 vfun2) (hv_arg : ValEqAll varg1 varg2)
      (hrest : StackEq s1 s2) :
      StateEq (step (.ret (.funV vfun1 :: s1) varg1))
              (step (.ret (.funV vfun2 :: s2) varg2)) := by
    cases vfun1 <;> cases vfun2 <;> simp_all [ValEqAll]
    · -- VCon, VCon
      simp only [step]; exact .error
    · -- VDelay, VDelay
      simp only [step]; exact .error
    · -- VLam, VLam
      rename_i body1 env1 body2 env2
      obtain ⟨hb, henv⟩ := ‹_›; subst hb
      simp only [step]; exact .compute body1 hrest (envEqAll_extend henv hv_arg)
    · -- VConstr, VConstr
      simp only [step]; exact .error
    · -- VBuiltin, VBuiltin
      rename_i b1 args1 ea1 b2 args2 ea2
      obtain ⟨hb, hargs, hea⟩ := ‹b1 = b2 ∧ _›; subst hb; subst hea
      simp only [step]
      cases h_head : ExpectedArgs.head ea1 with
      | argV =>
        simp [h_head]; cases h_tail : ExpectedArgs.tail ea1 with
        | some rest =>
          simp [h_tail]; exact .ret hrest ⟨rfl, ⟨hv_arg, hargs⟩, rfl⟩
        | none =>
          simp [h_tail]; exact ret_evalBuiltin_stateEq ⟨hv_arg, hargs⟩ hrest
      | argQ => simp [h_head]; exact .error
  step_ret_applyArg {v1 v2 varg1 varg2 : CekValue} {s1 s2 : Stack}
      (hv : ValEqAll v1 v2) (hv_arg : ValEqAll varg1 varg2)
      (hrest : StackEq s1 s2) :
      StateEq (step (.ret (.applyArg varg1 :: s1) v1))
              (step (.ret (.applyArg varg2 :: s2) v2)) := by
    cases v1 <;> cases v2 <;> simp_all [ValEqAll]
    · -- VCon, VCon
      simp only [step]; exact .error
    · -- VDelay, VDelay
      simp only [step]; exact .error
    · -- VLam, VLam
      rename_i body1 env1 body2 env2
      obtain ⟨hb, henv⟩ := ‹_›; subst hb
      simp only [step]; exact .compute body1 hrest (envEqAll_extend henv hv_arg)
    · -- VConstr, VConstr
      simp only [step]; exact .error
    · -- VBuiltin, VBuiltin
      rename_i b1 args1 ea1 b2 args2 ea2
      obtain ⟨hb, hargs, hea⟩ := ‹b1 = b2 ∧ _›; subst hb; subst hea
      simp only [step]
      cases h_head : ExpectedArgs.head ea1 with
      | argV =>
        simp [h_head]; cases h_tail : ExpectedArgs.tail ea1 with
        | some rest =>
          simp [h_tail]; exact .ret hrest ⟨rfl, ⟨hv_arg, hargs⟩, rfl⟩
        | none =>
          simp [h_tail]; exact ret_evalBuiltin_stateEq ⟨hv_arg, hargs⟩ hrest
      | argQ => simp [h_head]; exact .error
  step_ret_case {v1 v2 : CekValue} {env1 env2 : CekEnv} {s1 s2 : Stack}
      (hv : ValEqAll v1 v2) (he' : EnvEqAll env1 env2)
      (hrest : StackEq s1 s2) (alts : List Term) :
      StateEq (step (.ret (.caseScrutinee alts env1 :: s1) v1))
              (step (.ret (.caseScrutinee alts env2 :: s2) v2)) := by
    cases v1 <;> cases v2 <;> simp_all [ValEqAll]
    · -- VCon, VCon
      rename_i c1 c2; subst ‹c1 = c2›; simp only [step]
      cases h_ctf : constToTagAndFields c1 with
      | none => simp [h_ctf]; exact .error
      | some val =>
        obtain ⟨tag, numCtors, fields⟩ := val; simp only [h_ctf]
        cases h_check : (decide (numCtors > 0) && decide (alts.length > numCtors)) with
        | true => simp [h_check]; exact .error
        | false =>
          simp [h_check]
          cases h_idx : alts[tag]? with
          | none => simp [h_idx]; exact .error
          | some alt =>
            simp [h_idx]
            exact .compute alt
              (stackEq_append (listValEqAll_map_applyArg (listValEqAll_refl fields)) hrest) he'
    · -- VDelay, VDelay
      simp only [step]; exact .error
    · -- VLam, VLam
      simp only [step]; exact .error
    · -- VConstr, VConstr
      rename_i tag1 fs1 tag2 fs2
      obtain ⟨htag, hfs⟩ := ‹tag1 = tag2 ∧ _›; subst htag; simp only [step]
      cases h_idx : alts[tag1]? with
      | none => simp [h_idx]; exact .error
      | some alt =>
        simp [h_idx]
        exact .compute alt (stackEq_append (listValEqAll_map_applyArg hfs) hrest) he'
    · -- VBuiltin, VBuiltin
      simp only [step]; exact .error

/-! ## Multi-step preservation and extraction -/

theorem steps_preserves (N : Nat) {s1 s2 : State} (h : StateEq s1 s2) :
    StateEq (steps N s1) (steps N s2) := by
  induction N generalizing s1 s2 with
  | zero => simp [steps]; exact h
  | succ n ih => simp [steps]; exact ih (step_preserves h)

theorem stateEq_error_transfer {s1 s2 : State} (h : StateEq s1 s2)
    (herr : s1 = .error) : s2 = .error := by
  subst herr; cases h with | error => rfl

theorem stateEq_halt_transfer {s1 s2 : State} {v1 : CekValue} (h : StateEq s1 s2)
    (hhalt : s1 = .halt v1) : ∃ v2, s2 = .halt v2 ∧ ValEqAll v1 v2 := by
  subst hhalt; cases h with | halt hv => exact ⟨_, rfl, hv⟩

/-! ## ValEqAll implies ValueEq

The key conversion: structural equivalence implies behavioral equivalence.
Proved by induction on the step index `j`, using `step_preserves` for
the VLam/VDelay cases. -/

mutual
  theorem valEqAll_implies_valueEq : ∀ (j : Nat) (v1 v2 : CekValue),
      ValEqAll v1 v2 → ValueEq j v1 v2
    | 0, _, _, _ => by simp [ValueEq]
    | _ + 1, .VCon _, .VCon _, h => by simp [ValEqAll] at h; simp [ValueEq]; exact h
    | k + 1, .VLam body1 env1, .VLam body2 env2, h => by
      simp [ValEqAll] at h; obtain ⟨hb, henv⟩ := h; subst hb
      unfold ValueEq; intro arg1 arg2 hargs n hn
      -- Bisimulation: env1.extend(arg1) ↔ env2.extend(arg1)
      have he := envEqAll_extend henv (valEqAll_refl arg1)
      have hbisim := steps_preserves n (StateEq.compute body1 .nil he)
      have he' := envEqAll_extend (envEqAll_symm _ _ henv) (valEqAll_refl arg1)
      have hbisim' := steps_preserves n (StateEq.compute body1 .nil he')
      -- Arg variation via valueEq_refl for VLam at env2
      -- valueEq_refl (k+1) (.VLam body1 env2) : ValueEq (k+1) (.VLam body1 env2) (.VLam body1 env2)
      -- After unfolding, this gives ∀ a1 a2, ValueEq k a1 a2 → ∀ m ≤ k, triple
      have hvar : (steps n (.compute [] (env2.extend arg1) body1) = .error ↔
                   steps n (.compute [] (env2.extend arg2) body1) = .error) ∧
                  (∀ v1, steps n (.compute [] (env2.extend arg1) body1) = .halt v1 →
                    ∃ v2, steps n (.compute [] (env2.extend arg2) body1) = .halt v2 ∧ ValueEq k v1 v2) ∧
                  (∀ v2, steps n (.compute [] (env2.extend arg2) body1) = .halt v2 →
                    ∃ v1, steps n (.compute [] (env2.extend arg1) body1) = .halt v1 ∧ ValueEq k v1 v2) := by
        have hrefl := valueEq_refl (k + 1) (CekValue.VLam body1 env2)
        unfold ValueEq at hrefl
        exact hrefl arg1 arg2 hargs n hn
      obtain ⟨hvar_err, hvar_fwd, hvar_bwd⟩ := hvar
      -- Compose bisim + arg variation
      refine ⟨⟨fun h1 => ?_, fun h2 => ?_⟩, fun v1 hv1 => ?_, fun v2 hv2 => ?_⟩
      · exact hvar_err.mp (stateEq_error_transfer hbisim h1)
      · exact stateEq_error_transfer hbisim' (hvar_err.mpr h2)
      · obtain ⟨v_mid, hv_mid, hve_mid⟩ := stateEq_halt_transfer hbisim hv1
        obtain ⟨v2, hv2, hve2⟩ := hvar_fwd v_mid hv_mid
        exact ⟨v2, hv2, valueEq_trans k _ _ _ (valEqAll_implies_valueEq k _ _ hve_mid) hve2⟩
      · obtain ⟨v_mid, hv_mid, hve_mid⟩ := hvar_bwd v2 hv2
        obtain ⟨v1, hv1, hve1⟩ := stateEq_halt_transfer hbisim' hv_mid
        exact ⟨v1, hv1, valueEq_trans k _ _ _
          (valueEq_symm k _ _ (valEqAll_implies_valueEq k _ _ hve1)) hve_mid⟩
    | k + 1, .VDelay body1 env1, .VDelay body2 env2, h => by
      simp [ValEqAll] at h; obtain ⟨hb, henv⟩ := h; subst hb
      unfold ValueEq; intro n hn
      -- Bisimulation directly gives bounded agreement for same body, EnvEqAll envs
      have hbisim := steps_preserves n (.compute body1 .nil henv)
      have hbisim' := steps_preserves n (.compute body1 .nil (envEqAll_symm _ _ henv))
      refine ⟨⟨fun h1 => stateEq_error_transfer hbisim h1,
               fun h2 => stateEq_error_transfer hbisim' h2⟩,
              fun v1 hv1 => ?_, fun v2 hv2 => ?_⟩
      · obtain ⟨v2, hv2, hve⟩ := stateEq_halt_transfer hbisim hv1
        exact ⟨v2, hv2, valEqAll_implies_valueEq k _ _ hve⟩
      · obtain ⟨v1, hv1, hve⟩ := stateEq_halt_transfer hbisim' hv2
        exact ⟨v1, hv1, valueEq_symm k _ _ (valEqAll_implies_valueEq k _ _ hve)⟩
    | k + 1, .VConstr _ _, .VConstr _ _, h => by
      simp [ValEqAll] at h; unfold ValueEq
      exact ⟨h.1, listValEqAll_implies_listValueEq k _ _ h.2⟩
    | k + 1, .VBuiltin b1 args1 ea1, .VBuiltin b2 args2 ea2, h => by
      simp [ValEqAll] at h
      obtain ⟨hb, hargs, hea⟩ := h; subst hb; subst hea
      unfold ValueEq
      have hargs_ve := listValEqAll_implies_listValueEq k args1 args2 hargs
      have heb := evalBuiltin_valEqAll b1 hargs
      refine ⟨rfl, hargs_ve, rfl, ?_, ?_⟩
      · -- evalBuiltin none ↔ none
        generalize he1 : evalBuiltin b1 args1 = r1 at heb
        generalize he2 : evalBuiltin b1 args2 = r2 at heb
        cases r1 <;> cases r2 <;> simp_all
      · -- evalBuiltin some → ValueEq k
        intro r1 r2 h1 h2
        generalize he1 : evalBuiltin b1 args1 = r1' at heb
        generalize he2 : evalBuiltin b1 args2 = r2' at heb
        rw [h1] at he1; rw [h2] at he2; subst he1; subst he2
        exact valEqAll_implies_valueEq k r1 r2 heb
    -- Cross-constructor cases
    | _ + 1, .VCon _, .VLam _ _, h => by simp [ValEqAll] at h
    | _ + 1, .VCon _, .VDelay _ _, h => by simp [ValEqAll] at h
    | _ + 1, .VCon _, .VConstr _ _, h => by simp [ValEqAll] at h
    | _ + 1, .VCon _, .VBuiltin _ _ _, h => by simp [ValEqAll] at h
    | _ + 1, .VLam _ _, .VCon _, h => by simp [ValEqAll] at h
    | _ + 1, .VLam _ _, .VDelay _ _, h => by simp [ValEqAll] at h
    | _ + 1, .VLam _ _, .VConstr _ _, h => by simp [ValEqAll] at h
    | _ + 1, .VLam _ _, .VBuiltin _ _ _, h => by simp [ValEqAll] at h
    | _ + 1, .VDelay _ _, .VCon _, h => by simp [ValEqAll] at h
    | _ + 1, .VDelay _ _, .VLam _ _, h => by simp [ValEqAll] at h
    | _ + 1, .VDelay _ _, .VConstr _ _, h => by simp [ValEqAll] at h
    | _ + 1, .VDelay _ _, .VBuiltin _ _ _, h => by simp [ValEqAll] at h
    | _ + 1, .VConstr _ _, .VCon _, h => by simp [ValEqAll] at h
    | _ + 1, .VConstr _ _, .VLam _ _, h => by simp [ValEqAll] at h
    | _ + 1, .VConstr _ _, .VDelay _ _, h => by simp [ValEqAll] at h
    | _ + 1, .VConstr _ _, .VBuiltin _ _ _, h => by simp [ValEqAll] at h
    | _ + 1, .VBuiltin _ _ _, .VCon _, h => by simp [ValEqAll] at h
    | _ + 1, .VBuiltin _ _ _, .VLam _ _, h => by simp [ValEqAll] at h
    | _ + 1, .VBuiltin _ _ _, .VDelay _ _, h => by simp [ValEqAll] at h
    | _ + 1, .VBuiltin _ _ _, .VConstr _ _, h => by simp [ValEqAll] at h

  theorem listValEqAll_implies_listValueEq : ∀ (j : Nat) (vs1 vs2 : List CekValue),
      ListValEqAll vs1 vs2 → ListValueEq j vs1 vs2
    | _, [], [], _ => by simp [ListValueEq]
    | j, _ :: _, _ :: _, h => by
      simp [ListValEqAll] at h; simp [ListValueEq]
      exact ⟨valEqAll_implies_valueEq j _ _ h.1, listValEqAll_implies_listValueEq j _ _ h.2⟩
    | _, [], _ :: _, h => by simp [ListValEqAll] at h
    | _, _ :: _, [], h => by simp [ListValEqAll] at h
end

/-! ## Main theorem: same_term_env_variation -/

/-- Running the same body in structurally-equivalent closure envs with
    ValEqAll extension args produces equivalent results.
    This is the version taking `ValEqAll va va'`. -/
theorem same_term_env_variation (body : Term) (cenv : CekEnv)
    (va va' : CekValue) (hva : ValEqAll va va') :
    (Reaches (.compute [] (cenv.extend va) body) .error ↔
     Reaches (.compute [] (cenv.extend va') body) .error) ∧
    (Halts (.compute [] (cenv.extend va) body) ↔
     Halts (.compute [] (cenv.extend va') body)) ∧
    ∀ j v1 v2, Reaches (.compute [] (cenv.extend va) body) (.halt v1) →
                Reaches (.compute [] (cenv.extend va') body) (.halt v2) →
                ValueEq j v1 v2 := by
  have he : EnvEqAll (cenv.extend va) (cenv.extend va') := envEqAll_extend (envEqAll_refl cenv) hva
  have hinit : StateEq (.compute [] (cenv.extend va) body) (.compute [] (cenv.extend va') body) :=
    .compute body .nil he
  refine ⟨?_, ?_, ?_⟩
  · -- error↔
    constructor
    · intro ⟨N, hN⟩; exact ⟨N, stateEq_error_transfer (steps_preserves N hinit) hN⟩
    · intro ⟨N, hN⟩
      have he' := envEqAll_extend (envEqAll_refl cenv) (valEqAll_symm _ _ hva)
      have hinit' := StateEq.compute body .nil he'
      exact ⟨N, stateEq_error_transfer (steps_preserves N hinit') hN⟩
  · -- halts↔
    constructor
    · intro ⟨v, N, hN⟩
      have ⟨v', hv', _⟩ := stateEq_halt_transfer (steps_preserves N hinit) hN
      exact ⟨v', N, hv'⟩
    · intro ⟨v, N, hN⟩
      have he' := envEqAll_extend (envEqAll_refl cenv) (valEqAll_symm _ _ hva)
      have hinit' := StateEq.compute body .nil he'
      have ⟨v', hv', _⟩ := stateEq_halt_transfer (steps_preserves N hinit') hN
      exact ⟨v', N, hv'⟩
  · -- ValueEq j for halted values
    intro j v1 v2 ⟨N1, hN1⟩ ⟨N2, hN2⟩
    have h1 : steps (max N1 N2) (.compute [] (cenv.extend va) body) = .halt v1 := by
      rw [show max N1 N2 = N1 + (max N1 N2 - N1) from by omega, steps_trans, hN1, steps_halt]
    have hfinal := steps_preserves (max N1 N2) hinit; rw [h1] at hfinal
    have ⟨v2', hv2', hveq⟩ := stateEq_halt_transfer hfinal rfl
    have h2 : steps (max N1 N2) (.compute [] (cenv.extend va') body) = .halt v2 := by
      rw [show max N1 N2 = N2 + (max N1 N2 - N2) from by omega, steps_trans, hN2, steps_halt]
    rw [h2] at hv2'; injection hv2' with hv2'; subst hv2'
    exact valEqAll_implies_valueEq j v1 v2 hveq

/-! ## Phase 1: Error/Halts transfer for ValueEq envs

Given envs that agree via `∀ j, ValueEq j` at every position (not ValEqAll),
error and halts transfer. The proof is by step-count induction.

At each step, `ValueEq 1` gives matching constructors, which determines all
branching decisions in `step`. When a closure is applied, its body runs
in an env that still has `∀ j, ValueEq j` values — the invariant propagates.

We define `EnvBehEq` (behavioral env equivalence) and prove error/halts
transfer. This does NOT use ValEqAll at all. -/

/-- Behavioral env equivalence: same domain + ValueEq at all indices. -/
def EnvBehEq (env1 env2 : CekEnv) : Prop :=
  (∀ n, env1.lookup n = none ↔ env2.lookup n = none) ∧
  (∀ n v1 v2, env1.lookup n = some v1 → env2.lookup n = some v2 → ∀ j, ValueEq j v1 v2)

theorem envBehEq_refl (env : CekEnv) : EnvBehEq env env :=
  ⟨fun _ => Iff.rfl, fun _ _ _ h1 h2 _ => by rw [h1] at h2; injection h2 with h; subst h; exact valueEq_refl _ _⟩

/-- Extending EnvBehEq envs with `∀ j, ValueEq j` values preserves EnvBehEq.
    Proof: position 0 → none on both (CekEnv.lookup 0 = none).
    Position 1 → the new values (use hv). Position n+2 → delegate to he. -/
theorem envBehEq_extend {env1 env2 : CekEnv} {v1 v2 : CekValue}
    (he : EnvBehEq env1 env2) (hv : ∀ j, ValueEq j v1 v2) :
    EnvBehEq (env1.extend v1) (env2.extend v2) := by
  obtain ⟨hdom, hval⟩ := he
  show EnvBehEq (.cons v1 env1) (.cons v2 env2)
  constructor
  · -- domain agreement
    intro n
    match n with
    | 0 => simp [CekEnv.lookup]
    | 1 => simp [CekEnv.lookup]
    | n + 2 => simp [CekEnv.lookup]; exact hdom (n + 1)
  · -- value agreement
    intro n v1' v2'
    match n with
    | 0 => simp [CekEnv.lookup]
    | 1 =>
      simp [CekEnv.lookup]
      rintro rfl rfl
      exact hv
    | n + 2 =>
      simp [CekEnv.lookup]
      exact hval (n + 1) v1' v2'

/-- `ValueEq 1` implies matching constructors. Extract this fact. -/
private theorem valueEq1_constructor_match (v1 v2 : CekValue) (h : ValueEq 1 v1 v2) :
    (∃ c, v1 = .VCon c ∧ v2 = .VCon c) ∨
    (∃ b1 e1 b2 e2, v1 = .VLam b1 e1 ∧ v2 = .VLam b2 e2) ∨
    (∃ b1 e1 b2 e2, v1 = .VDelay b1 e1 ∧ v2 = .VDelay b2 e2) ∨
    (∃ t fs1 fs2, v1 = .VConstr t fs1 ∧ v2 = .VConstr t fs2) ∨
    (∃ b a1 a2 ea, v1 = .VBuiltin b a1 ea ∧ v2 = .VBuiltin b a2 ea) := by
  match v1, v2 with
  | .VCon c1, .VCon c2 =>
    simp [ValueEq] at h; subst h
    exact Or.inl ⟨c1, rfl, rfl⟩
  | .VLam b1 e1, .VLam b2 e2 =>
    exact Or.inr (Or.inl ⟨b1, e1, b2, e2, rfl, rfl⟩)
  | .VDelay b1 e1, .VDelay b2 e2 =>
    exact Or.inr (Or.inr (Or.inl ⟨b1, e1, b2, e2, rfl, rfl⟩))
  | .VConstr t1 fs1, .VConstr t2 fs2 =>
    simp [ValueEq] at h
    obtain ⟨ht, _⟩ := h; subst ht
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨t1, fs1, fs2, rfl, rfl⟩)))
  | .VBuiltin b1 a1 ea1, .VBuiltin b2 a2 ea2 =>
    simp [ValueEq] at h
    obtain ⟨hb, _, hea, _⟩ := h; subst hb; subst hea
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨b1, a1, a2, ea1, rfl, rfl⟩)))
  | .VCon _, .VLam _ _ => unfold ValueEq at h; exact h.elim
  | .VCon _, .VDelay _ _ => unfold ValueEq at h; exact h.elim
  | .VCon _, .VConstr _ _ => unfold ValueEq at h; exact h.elim
  | .VCon _, .VBuiltin _ _ _ => unfold ValueEq at h; exact h.elim
  | .VLam _ _, .VCon _ => unfold ValueEq at h; exact h.elim
  | .VLam _ _, .VDelay _ _ => unfold ValueEq at h; exact h.elim
  | .VLam _ _, .VConstr _ _ => unfold ValueEq at h; exact h.elim
  | .VLam _ _, .VBuiltin _ _ _ => unfold ValueEq at h; exact h.elim
  | .VDelay _ _, .VCon _ => unfold ValueEq at h; exact h.elim
  | .VDelay _ _, .VLam _ _ => unfold ValueEq at h; exact h.elim
  | .VDelay _ _, .VConstr _ _ => unfold ValueEq at h; exact h.elim
  | .VDelay _ _, .VBuiltin _ _ _ => unfold ValueEq at h; exact h.elim
  | .VConstr _ _, .VCon _ => unfold ValueEq at h; exact h.elim
  | .VConstr _ _, .VLam _ _ => unfold ValueEq at h; exact h.elim
  | .VConstr _ _, .VDelay _ _ => unfold ValueEq at h; exact h.elim
  | .VConstr _ _, .VBuiltin _ _ _ => unfold ValueEq at h; exact h.elim
  | .VBuiltin _ _ _, .VCon _ => unfold ValueEq at h; exact h.elim
  | .VBuiltin _ _ _, .VLam _ _ => unfold ValueEq at h; exact h.elim
  | .VBuiltin _ _ _, .VDelay _ _ => unfold ValueEq at h; exact h.elim
  | .VBuiltin _ _ _, .VConstr _ _ => unfold ValueEq at h; exact h.elim

/-- ValEqAll implies EnvBehEq (lifting the structural relation to behavioral). -/
theorem valEqAll_envBehEq {env1 env2 : CekEnv} (h : EnvEqAll env1 env2) :
    EnvBehEq env1 env2 := by
  constructor
  · -- domain agreement: env1.lookup n = none ↔ env2.lookup n = none
    intro n
    have hl := envEqAll_lookup h n
    generalize env1.lookup n = r1 at hl
    generalize env2.lookup n = r2 at hl
    cases r1 <;> cases r2 <;> simp_all
  · -- value agreement
    intro n w1 w2 h1 h2 j
    have hl := envEqAll_lookup h n
    rw [h1, h2] at hl
    exact valEqAll_implies_valueEq j w1 w2 hl

/-! ### Phase 1a: Single-step constructor matching

When envs are EnvBehEq, a single `step` on `compute stk env t` produces
states that are "structurally aligned": same term (for compute), or same
constructor (for ret/halt values). This is because `ValueEq 1` at each
env position gives matching constructors, which determines all branches
in the step function.

We prove this by showing `step` applied to EnvBehEq-related compute states
produces states where the values satisfy `∀ j, ValueEq j`. -/

-- For the step-count induction, we need that EnvBehEq envs extended with
-- the SAME value are still EnvBehEq. This is a special case of envBehEq_extend.
theorem envBehEq_extend_same (env1 env2 : CekEnv) (v : CekValue)
    (he : EnvBehEq env1 env2) : EnvBehEq (env1.extend v) (env2.extend v) :=
  envBehEq_extend he (fun _ => valueEq_refl _ v)

private abbrev ValEqInf (v1 v2 : CekValue) : Prop :=
  ∀ j, ValueEq j v1 v2

private abbrev ListValueEqInf (vs1 vs2 : List CekValue) : Prop :=
  ∀ j, ListValueEq j vs1 vs2

private def BehBundle (s1 s2 : State) : Prop :=
  (Reaches s1 .error ↔ Reaches s2 .error) ∧
  (Halts s1 ↔ Halts s2) ∧
  ∀ j v1 v2, Reaches s1 (.halt v1) → Reaches s2 (.halt v2) → ValueEq j v1 v2

private theorem behBundle_symm {s1 s2 : State} (h : BehBundle s1 s2) :
    BehBundle s2 s1 := by
  rcases h with ⟨herr, hhalt, hval⟩
  refine ⟨herr.symm, hhalt.symm, ?_⟩
  intro j v2 v1 hv2 hv1
  exact valueEq_symm j _ _ (hval j v1 v2 hv1 hv2)

private theorem behBundle_trans {s1 s2 s3 : State}
    (h12 : BehBundle s1 s2) (h23 : BehBundle s2 s3) :
    BehBundle s1 s3 := by
  rcases h12 with ⟨herr12, hhalt12, hval12⟩
  rcases h23 with ⟨herr23, hhalt23, hval23⟩
  refine ⟨herr12.trans herr23, hhalt12.trans hhalt23, ?_⟩
  intro j v1 v3 hv1 hv3
  obtain ⟨v2, hv2⟩ := hhalt12.mp ⟨v1, hv1⟩
  exact valueEq_trans j _ _ _ (hval12 j v1 v2 hv1 hv2) (hval23 j v2 v3 hv2 hv3)

private theorem firstInactiveBeh (s : State) (bound : Nat)
    (hex : ∃ k, k ≤ bound ∧ isActive (steps k s) = false) :
    ∃ K, K ≤ bound ∧ isActive (steps K s) = false ∧
         (∀ j, j < K → isActive (steps j s) = true) := by
  induction bound with
  | zero =>
    obtain ⟨k, hk, hinact⟩ := hex
    have : k = 0 := by omega
    subst this
    exact ⟨0, Nat.le_refl _, hinact, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ bound ih =>
    by_cases h : ∃ k, k ≤ bound ∧ isActive (steps k s) = false
    · obtain ⟨K, hK_le, hK_inact, hK_min⟩ := ih h
      exact ⟨K, by omega, hK_inact, hK_min⟩
    · have hall : ∀ j, j ≤ bound → isActive (steps j s) = true := by
        intro j hj
        by_cases heq : isActive (steps j s) = true
        · exact heq
        · exfalso
          apply h
          exact ⟨j, hj, by cases isActive (steps j s) <;> simp_all⟩
      obtain ⟨k, hk, hinact⟩ := hex
      have hk_eq : k = bound + 1 := by
        by_cases heq : k = bound + 1
        · exact heq
        · exfalso
          have hle : k ≤ bound := by omega
          have := hall k hle
          simp [hinact] at this
      subst hk_eq
      exact ⟨bound + 1, Nat.le_refl _, hinact, fun j hj => hall j (by omega)⟩

private theorem extractLiftedValue (base : Stack) (s : State) (K : Nat)
    (hK_inact : isActive (steps K s) = false)
    (h_not_error : steps K s ≠ .error) :
    ∃ ve, (steps K s = .halt ve ∨ steps K s = .ret [] ve) ∧
          liftState base (steps K s) = .ret base ve := by
  generalize h_sK : steps K s = sK at hK_inact h_not_error
  match sK with
  | .compute .. => simp [isActive] at hK_inact
  | .ret [] ve => exact ⟨ve, .inr rfl, by simp [liftState]⟩
  | .ret (_ :: _) _ => simp [isActive] at hK_inact
  | .halt ve => exact ⟨ve, .inl rfl, by simp [liftState]⟩
  | .error => exact absurd rfl h_not_error

private theorem not_error_before_halt_beh {s : State} {K Ke : Nat} {ve : CekValue}
    (hK_le : K ≤ Ke) (hKe : steps Ke s = .halt ve)
    (h : steps K s = .error) : False := by
  have : steps Ke s = .error := by
    have : Ke = K + (Ke - K) := by omega
    rw [this, steps_trans, h, steps_error]
  rw [hKe] at this
  exact absurd this (by simp)

private theorem halt_value_unique_beh {s : State} {K Ke : Nat} {ve ve' : CekValue}
    (hK_le : K ≤ Ke)
    (h_inner_eq : steps K s = .halt ve' ∨ steps K s = .ret [] ve')
    (hKe : steps Ke s = .halt ve) : ve' = ve := by
  have h_halt_ve' : steps (K + 1) s = .halt ve' := by
    cases h_inner_eq with
    | inl h => rw [steps_trans, h, steps_halt]
    | inr h => rw [steps_trans, h]; rfl
  by_cases hle : K + 1 ≤ Ke
  · have h_Ke_eq : steps Ke s = .halt ve' := by
      have : Ke = (K + 1) + (Ke - (K + 1)) := by omega
      rw [this, steps_trans, h_halt_ve', steps_halt]
    rw [hKe] at h_Ke_eq
    exact (State.halt.inj h_Ke_eq).symm
  · have hKeq : K = Ke := by omega
    rw [← hKeq] at hKe
    have : steps (K + 1) s = .halt ve := by
      rw [steps_trans, hKe]
      rfl
    rw [h_halt_ve'] at this
    exact State.halt.inj this

private theorem liftedHaltValueBeh (base : Stack) (s : State) (N : Nat) (v : CekValue)
    (hN : steps N (liftState base s) = .halt v) :
    ∃ K ve, K ≤ N ∧
      (∀ j, j < K → isActive (steps j s) = true) ∧
      (steps K s = .halt ve ∨ steps K s = .ret [] ve) ∧
      liftState base (steps K s) = .ret base ve ∧
      steps K (liftState base s) = .ret base ve ∧
      Reaches s (.halt ve) ∧
      steps (N - K) (.ret base ve) = .halt v := by
  have h_has_inactive : ∃ k, k ≤ N ∧ isActive (steps k s) = false := by
    exact Classical.byContradiction fun hall => by
      have hall' : ∀ j, j ≤ N → isActive (steps j s) = true := by
        intro j hj
        by_cases hact : isActive (steps j s) = true
        · exact hact
        · exfalso
          apply hall
          exact ⟨j, hj, by cases isActive (steps j s) <;> simp_all⟩
      have h_comm := steps_liftState base N s (fun j hj => hall' j (by omega))
      rw [hN] at h_comm
      exact absurd h_comm.symm (liftState_ne_halt _ _ v)
  obtain ⟨K, hK_le, hK_inact, hK_min⟩ := firstInactiveBeh s N h_has_inactive
  have h_comm : steps K (liftState base s) = liftState base (steps K s) :=
    steps_liftState base K s hK_min
  have h_not_error : steps K s ≠ .error := by
    intro herr
    have : steps (N - K) (liftState base .error) = .halt v := by
      have : N = K + (N - K) := by omega
      rw [this, steps_trans, h_comm, herr] at hN
      exact hN
    simp [liftState, steps_error] at this
  obtain ⟨ve, h_inner_eq, h_lifted_eq⟩ := extractLiftedValue base s K hK_inact h_not_error
  have h_reaches : Reaches s (.halt ve) := by
    cases h_inner_eq with
    | inl h => exact ⟨K, h⟩
    | inr h => exact ⟨K + 1, by rw [steps_trans, h]; rfl⟩
  have h_rest : steps (N - K) (.ret base ve) = .halt v := by
    have : N = K + (N - K) := by omega
    rw [this, steps_trans, h_comm, h_lifted_eq] at hN
    exact hN
  exact ⟨K, ve, hK_le, hK_min, h_inner_eq, h_lifted_eq, by rw [h_comm, h_lifted_eq],
    h_reaches, h_rest⟩

private theorem liftedErrorValueBeh (base : Stack) (s : State) (N : Nat)
    (hN : steps N (liftState base s) = .error) :
    ∃ K, K ≤ N ∧
      (∀ j, j < K → isActive (steps j s) = true) ∧
      steps K (liftState base s) = liftState base (steps K s) ∧
      (steps K s = .error ∨
        ∃ ve, (steps K s = .halt ve ∨ steps K s = .ret [] ve) ∧
              liftState base (steps K s) = .ret base ve ∧
              Reaches s (.halt ve) ∧
              steps (N - K) (.ret base ve) = .error) := by
  have h_has_inactive : ∃ k, k ≤ N ∧ isActive (steps k s) = false := by
    exact Classical.byContradiction fun hall => by
      have hall' : ∀ j, j ≤ N → isActive (steps j s) = true := by
        intro j hj
        by_cases hact : isActive (steps j s) = true
        · exact hact
        · exfalso
          apply hall
          exact ⟨j, hj, by cases isActive (steps j s) <;> simp_all⟩
      have h_comm := steps_liftState base N s (fun j hj => hall' j (by omega))
      rw [hN] at h_comm
      have h_inner_err := liftState_eq_error _ _ h_comm.symm
      have := hall' N (Nat.le_refl _)
      rw [h_inner_err] at this
      simp [isActive] at this
  obtain ⟨K, hK_le, hK_inact, hK_min⟩ := firstInactiveBeh s N h_has_inactive
  have h_comm : steps K (liftState base s) = liftState base (steps K s) :=
    steps_liftState base K s hK_min
  by_cases h_is_error : steps K s = .error
  · exact ⟨K, hK_le, hK_min, h_comm, .inl h_is_error⟩
  · obtain ⟨ve, h_inner_eq, h_lifted_eq⟩ := extractLiftedValue base s K hK_inact h_is_error
    have h_reaches : Reaches s (.halt ve) := by
      cases h_inner_eq with
      | inl h => exact ⟨K, h⟩
      | inr h => exact ⟨K + 1, by rw [steps_trans, h]; rfl⟩
    have h_rest : steps (N - K) (.ret base ve) = .error := by
      have : N = K + (N - K) := by omega
      rw [this, steps_trans, h_comm, h_lifted_eq] at hN
      exact hN
    exact ⟨K, hK_le, hK_min, h_comm, .inr ⟨ve, h_inner_eq, h_lifted_eq, h_reaches, h_rest⟩⟩

private theorem liftState_error_of_error (base : Stack) (s : State)
    (herr : Reaches s .error) :
    Reaches (liftState base s) .error := by
  obtain ⟨n, hn⟩ := herr
  have h_inner_err : isActive (steps n s) = false := by
    rw [hn]
    rfl
  obtain ⟨K, _, hK_inact, hK_min⟩ :=
    firstInactiveBeh s n ⟨n, Nat.le_refl _, h_inner_err⟩
  have h_comm := steps_liftState base K s hK_min
  generalize h_sK : steps K s = sK at hK_inact h_comm
  match sK with
  | .compute .. => simp [isActive] at hK_inact
  | .ret (_ :: _) _ => simp [isActive] at hK_inact
  | .error =>
    exact ⟨K, by rw [h_comm]; simp [liftState]⟩
  | .halt v =>
    exfalso
    have : steps n s = .halt v := by
      have : n = K + (n - K) := by omega
      rw [this, steps_trans, h_sK, steps_halt]
    rw [hn] at this
    simp at this
  | .ret [] v =>
    exfalso
    exact reaches_halt_not_error ⟨K + 1, by rw [steps_trans, h_sK]; rfl⟩ ⟨n, hn⟩

private theorem liftState_compose (base : Stack) (s t : State) (v : CekValue)
    (hs : Reaches s (.halt v)) (ht : Reaches (.ret base v) t) :
    Reaches (liftState base s) t := by
  obtain ⟨Ke, hKe⟩ := hs
  obtain ⟨Kt, hKt⟩ := ht
  have h_not_active_Ke : isActive (steps Ke s) = false := by
    rw [hKe]
    rfl
  obtain ⟨K, hK_le, hK_inact, hK_min⟩ :=
    firstInactiveBeh s Ke ⟨Ke, Nat.le_refl _, h_not_active_Ke⟩
  have h_comm : steps K (liftState base s) = liftState base (steps K s) :=
    steps_liftState base K s hK_min
  have h_not_error : steps K s ≠ .error := by
    intro herr
    exact not_error_before_halt_beh hK_le hKe herr
  obtain ⟨v', h_inner_eq, h_lifted_eq⟩ := extractLiftedValue base s K hK_inact h_not_error
  have hv_eq : v' = v := halt_value_unique_beh hK_le h_inner_eq hKe
  rw [hv_eq] at h_lifted_eq
  exact ⟨K + Kt, by
    have : K + Kt = K + Kt := rfl
    rw [this, steps_trans, h_comm, h_lifted_eq, hKt]⟩

private theorem active_not_error {s : State} (h : isActive s = true) :
    s ≠ .error := by
  cases s <;> simp [isActive] at h ⊢

private theorem active_not_halt {s : State} (h : isActive s = true) (v : CekValue) :
    s ≠ .halt v := by
  cases s <;> simp [isActive] at h ⊢

private theorem behBundle_of_step_active {s1 s2 : State}
    (hact1 : isActive s1 = true) (hact2 : isActive s2 = true)
    (hstep : BehBundle (step s1) (step s2)) :
    BehBundle s1 s2 := by
  rcases hstep with ⟨herr, hhalt, hval⟩
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · rintro ⟨N, hN⟩
      cases N with
      | zero =>
        exfalso
        exact active_not_error hact1 hN
      | succ N =>
        obtain ⟨M, hM⟩ := herr.mp ⟨N, hN⟩
        exact ⟨M + 1, by simpa [steps] using hM⟩
    · rintro ⟨N, hN⟩
      cases N with
      | zero =>
        exfalso
        exact active_not_error hact2 hN
      | succ N =>
        obtain ⟨M, hM⟩ := herr.mpr ⟨N, hN⟩
        exact ⟨M + 1, by simpa [steps] using hM⟩
  · constructor
    · rintro ⟨v, N, hN⟩
      cases N with
      | zero =>
        exfalso
        exact active_not_halt hact1 v hN
      | succ N =>
        obtain ⟨w, hw⟩ := hhalt.mp ⟨v, ⟨N, hN⟩⟩
        exact ⟨w, by
          rcases hw with ⟨M, hM⟩
          exact ⟨M + 1, by simpa [steps] using hM⟩⟩
    · rintro ⟨v, N, hN⟩
      cases N with
      | zero =>
        exfalso
        exact active_not_halt hact2 v hN
      | succ N =>
        obtain ⟨w, hw⟩ := hhalt.mpr ⟨v, ⟨N, hN⟩⟩
        exact ⟨w, by
          rcases hw with ⟨M, hM⟩
          exact ⟨M + 1, by simpa [steps] using hM⟩⟩
  · intro j v1 v2 hv1 hv2
    obtain ⟨N1, hN1⟩ := hv1
    obtain ⟨N2, hN2⟩ := hv2
    cases N1 with
    | zero => exfalso; exact active_not_halt hact1 v1 hN1
    | succ N1 =>
      cases N2 with
      | zero => exfalso; exact active_not_halt hact2 v2 hN2
      | succ N2 =>
        exact hval j v1 v2 ⟨N1, hN1⟩ ⟨N2, hN2⟩

inductive FrameBehEq : Frame → Frame → Prop
  | arg (t : Term) {env1 env2 : CekEnv} (h : EnvBehEq env1 env2) :
      FrameBehEq (.arg t env1) (.arg t env2)
  | funV {v1 v2 : CekValue} (h : ValEqInf v1 v2) :
      FrameBehEq (.funV v1) (.funV v2)
  | force : FrameBehEq .force .force
  | constrField (tag : Nat) {done1 done2 : List CekValue} (rest : List Term)
      {env1 env2 : CekEnv} (hd : ListValueEqInf done1 done2) (he : EnvBehEq env1 env2) :
      FrameBehEq (.constrField tag done1 rest env1) (.constrField tag done2 rest env2)
  | caseScrutinee (alts : List Term) {env1 env2 : CekEnv} (h : EnvBehEq env1 env2) :
      FrameBehEq (.caseScrutinee alts env1) (.caseScrutinee alts env2)
  | applyArg {v1 v2 : CekValue} (h : ValEqInf v1 v2) :
      FrameBehEq (.applyArg v1) (.applyArg v2)

inductive StackBehEq : Stack → Stack → Prop
  | nil : StackBehEq [] []
  | cons {f1 f2 : Frame} {s1 s2 : Stack} (hf : FrameBehEq f1 f2) (hs : StackBehEq s1 s2) :
      StackBehEq (f1 :: s1) (f2 :: s2)

private theorem listValueEqInf_refl (vs : List CekValue) : ListValueEqInf vs vs :=
  fun j => listValueEq_refl j vs

private theorem listValueEqInf_cons {v1 v2 : CekValue} {vs1 vs2 : List CekValue}
    (hv : ValEqInf v1 v2) (hvs : ListValueEqInf vs1 vs2) :
    ListValueEqInf (v1 :: vs1) (v2 :: vs2) := by
  intro j
  simp [ListValueEq, hv j, hvs j]

private theorem listValueEqInf_tail {v1 v2 : CekValue} {vs1 vs2 : List CekValue}
    (h : ListValueEqInf (v1 :: vs1) (v2 :: vs2)) :
    ListValueEqInf vs1 vs2 := by
  intro j
  have hj := h j
  simp [ListValueEq] at hj
  exact hj.2

private theorem listValueEqInf_append {a1 a2 b1 b2 : List CekValue}
    (ha : ListValueEqInf a1 a2) (hb : ListValueEqInf b1 b2) :
    ListValueEqInf (a1 ++ b1) (a2 ++ b2) := by
  induction a1 generalizing a2 with
  | nil =>
    cases a2 with
    | nil => simpa using hb
    | cons _ _ => have := ha 0; simp [ListValueEq] at this
  | cons x xs ih =>
    cases a2 with
    | nil => have := ha 0; simp [ListValueEq] at this
    | cons y ys =>
      have hhead : ValEqInf x y := by
        intro k; have hk := ha k; simp [ListValueEq] at hk; exact hk.1
      have htl : ListValueEqInf (xs ++ b1) (ys ++ b2) := ih (listValueEqInf_tail ha)
      exact listValueEqInf_cons hhead htl

private theorem listValueEqInf_reverse {a1 a2 : List CekValue}
    (h : ListValueEqInf a1 a2) :
    ListValueEqInf a1.reverse a2.reverse := by
  induction a1 generalizing a2 with
  | nil =>
    cases a2 with
    | nil => intro j; simp [ListValueEq]
    | cons _ _ => have := h 0; simp [ListValueEq] at this
  | cons x xs ih =>
    cases a2 with
    | nil => have := h 0; simp [ListValueEq] at this
    | cons y ys =>
      have hxs_ys : ListValueEqInf xs ys := listValueEqInf_tail h
      have hhead : ValEqInf x y := by
        intro k; have hk := h k; simp [ListValueEq] at hk; exact hk.1
      intro j; simp [List.reverse_cons]
      exact (listValueEqInf_append (ih hxs_ys)
        (listValueEqInf_cons hhead (listValueEqInf_refl []))) j

private theorem evalBuiltin_cong_full (k : Nat) (b : BuiltinFun)
    {args1 args2 : List CekValue} (hargs : ListValueEqInf args1 args2) :
    (Moist.CEK.evalBuiltin b args1 = none ↔
     Moist.CEK.evalBuiltin b args2 = none) ∧
    (∀ r1 r2, Moist.CEK.evalBuiltin b args1 = some r1 →
              Moist.CEK.evalBuiltin b args2 = some r2 →
              ValueEq k r1 r2) := by
  cases args1 with
  | nil =>
    cases args2 with
    | nil =>
      constructor
      · exact Iff.rfl
      · intro r1 r2 h1 h2
        rw [h1] at h2
        injection h2 with h
        subst h
        exact valueEq_refl k r1
    | cons _ _ =>
      have h0 := hargs 0
      simp [ListValueEq] at h0
  | cons a1 as1 =>
    cases args2 with
    | nil =>
      have h0 := hargs 0
      simp [ListValueEq] at h0
    | cons a2 as2 =>
      have hhead : ValEqInf a1 a2 := by
        intro j
        have hj := hargs j
        simp [ListValueEq] at hj
        exact hj.1
      have htail : ListValueEqInf as1 as2 := listValueEqInf_tail hargs
      have hmid := Moist.Verified.Congruence.evalBuiltin_cong k b a1 as1 as2 (htail (k + 1))
      have hlast := Moist.Verified.Congruence.evalBuiltin_cong_first k b a1 a2 as2 (hhead (k + 1))
      refine ⟨hmid.1.trans hlast.1, ?_⟩
      intro r1 r2 hr1 hr2
      cases hmidv : Moist.CEK.evalBuiltin b (a1 :: as2) with
      | none =>
        have : Moist.CEK.evalBuiltin b (a1 :: as1) = none := hmid.1.mpr hmidv
        rw [hr1] at this
        simp at this
      | some rm =>
        exact valueEq_trans k _ _ _
          (hmid.2 r1 rm hr1 hmidv)
          (hlast.2 rm r2 hmidv hr2)

private theorem builtin_cons_valueEqInf {b : BuiltinFun} {ea : ExpectedArgs}
    {a1 a2 : List CekValue} (hargs : ListValueEqInf a1 a2) :
    ValEqInf (.VBuiltin b a1 ea) (.VBuiltin b a2 ea) := by
  intro j
  cases j with
  | zero => simp [ValueEq]
  | succ k =>
    unfold ValueEq
    refine ⟨rfl, hargs k, rfl, ?_, ?_⟩
    · exact (evalBuiltin_cong_full k b hargs).1
    · intro r1 r2 h1 h2
      exact (evalBuiltin_cong_full k b hargs).2 r1 r2 h1 h2

private theorem stackBehEq_refl : ∀ (stk : Stack), StackBehEq stk stk
  | [] => .nil
  | .force :: stk => .cons .force (stackBehEq_refl stk)
  | .arg t env :: stk => .cons (.arg t (envBehEq_refl env)) (stackBehEq_refl stk)
  | .funV v :: stk => .cons (.funV (fun j => valueEq_refl j v)) (stackBehEq_refl stk)
  | .constrField tag done rest env :: stk =>
      .cons (.constrField tag rest (listValueEqInf_refl done) (envBehEq_refl env)) (stackBehEq_refl stk)
  | .caseScrutinee alts env :: stk =>
      .cons (.caseScrutinee alts (envBehEq_refl env)) (stackBehEq_refl stk)
  | .applyArg v :: stk => .cons (.applyArg (fun j => valueEq_refl j v)) (stackBehEq_refl stk)

private theorem listValueEqInf_map_applyArg {fs1 fs2 : List CekValue}
    (h : ListValueEqInf fs1 fs2) :
    StackBehEq (fs1.map Frame.applyArg) (fs2.map Frame.applyArg) := by
  induction fs1 generalizing fs2 with
  | nil =>
    cases fs2 with
    | nil => exact .nil
    | cons _ _ => have := h 0; simp [ListValueEq] at this
  | cons f1 fs1' ih =>
    cases fs2 with
    | nil =>
      have := h 0
      simp [ListValueEq] at this
    | cons f2 fs2' =>
      refine .cons (.applyArg ?_) ?_
      · intro j
        have hsucc : ListValueEq (j + 1) (f1 :: fs1') (f2 :: fs2') := h (j + 1)
        simp [ListValueEq] at hsucc
        exact Moist.Verified.Congruence.valueEq_mono j (j + 1) (Nat.le_succ j) _ _ hsucc.1
      · apply ih
        intro j
        have hj : ListValueEq j (f1 :: fs1') (f2 :: fs2') := h j
        simp [ListValueEq] at hj
        exact hj.2

private theorem stackBehEq_append : ∀ {s1 s2 t1 t2 : Stack},
    StackBehEq s1 s2 → StackBehEq t1 t2 → StackBehEq (s1 ++ t1) (s2 ++ t2)
  | [], [], _, _, .nil, ht => ht
  | _ :: _, _ :: _, _, _, .cons hf hs, ht => .cons hf (stackBehEq_append hs ht)

private theorem lift_behBundle_of_ret {base1 base2 : Stack}
    (hret : ∀ v1 v2, ValEqInf v1 v2 → BehBundle (.ret base1 v1) (.ret base2 v2))
    {s1 s2 : State} (h : BehBundle s1 s2) :
    BehBundle (liftState base1 s1) (liftState base2 s2) := by
  rcases h with ⟨herr, hhalt, hval⟩
  have hret_symm : ∀ v2 v1, ValEqInf v2 v1 → BehBundle (.ret base2 v2) (.ret base1 v1) := by
    intro v2 v1 hve
    apply behBundle_symm
    apply hret
    intro j
    exact valueEq_symm j _ _ (hve j)
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro herr1
      obtain ⟨N, hN⟩ := herr1
      obtain ⟨K, _, _, _, hcase⟩ := liftedErrorValueBeh base1 s1 N hN
      cases hcase with
      | inl hs1_err =>
        exact liftState_error_of_error base2 s2 (herr.mp ⟨K, hs1_err⟩)
      | inr hhaltcase =>
        rcases hhaltcase with ⟨ve1, _, _, hs1_halt, hret_err⟩
        obtain ⟨ve2, hs2_halt⟩ := hhalt.mp ⟨ve1, hs1_halt⟩
        have hve : ValEqInf ve1 ve2 := fun j => hval j ve1 ve2 hs1_halt hs2_halt
        exact liftState_compose base2 s2 .error ve2 hs2_halt ((hret ve1 ve2 hve).1.mp ⟨N - K, hret_err⟩)
    · intro herr2
      obtain ⟨N, hN⟩ := herr2
      obtain ⟨K, _, _, _, hcase⟩ := liftedErrorValueBeh base2 s2 N hN
      cases hcase with
      | inl hs2_err =>
        exact liftState_error_of_error base1 s1 (herr.mpr ⟨K, hs2_err⟩)
      | inr hhaltcase =>
        rcases hhaltcase with ⟨ve2, _, _, hs2_halt, hret_err⟩
        obtain ⟨ve1, hs1_halt⟩ := hhalt.mpr ⟨ve2, hs2_halt⟩
        have hve : ValEqInf ve2 ve1 := fun j => hval j ve1 ve2 hs1_halt hs2_halt |> valueEq_symm j _ _
        exact liftState_compose base1 s1 .error ve1 hs1_halt ((hret_symm ve2 ve1 hve).1.mp ⟨N - K, hret_err⟩)
  · constructor
    · intro hhalt1
      obtain ⟨w1, hw1⟩ := hhalt1
      obtain ⟨N1, hN1⟩ := hw1
      obtain ⟨K1, ve1, _, _, _, _, _, hs1_halt, hret_halt⟩ :=
        liftedHaltValueBeh base1 s1 N1 w1 hN1
      obtain ⟨ve2, hs2_halt⟩ := hhalt.mp ⟨ve1, hs1_halt⟩
      have hve : ValEqInf ve1 ve2 := fun j => hval j ve1 ve2 hs1_halt hs2_halt
      obtain ⟨w2, hret2_halt⟩ := (hret ve1 ve2 hve).2.1.mp ⟨w1, ⟨N1 - K1, hret_halt⟩⟩
      exact ⟨w2, liftState_compose base2 s2 (.halt w2) ve2 hs2_halt hret2_halt⟩
    · intro hhalt2
      obtain ⟨w2, hw2⟩ := hhalt2
      obtain ⟨N2, hN2⟩ := hw2
      obtain ⟨K2, ve2, _, _, _, _, _, hs2_halt, hret_halt⟩ :=
        liftedHaltValueBeh base2 s2 N2 w2 hN2
      obtain ⟨ve1, hs1_halt⟩ := hhalt.mpr ⟨ve2, hs2_halt⟩
      have hve : ValEqInf ve2 ve1 := fun j => hval j ve1 ve2 hs1_halt hs2_halt |> valueEq_symm j _ _
      obtain ⟨w1, hret1_halt⟩ := (hret_symm ve2 ve1 hve).2.1.mp ⟨w2, ⟨N2 - K2, hret_halt⟩⟩
      exact ⟨w1, liftState_compose base1 s1 (.halt w1) ve1 hs1_halt hret1_halt⟩
  · intro j w1 w2 hw1 hw2
    obtain ⟨N1, hN1⟩ := hw1
    obtain ⟨N2, hN2⟩ := hw2
    obtain ⟨K1, ve1, _, _, _, _, _, hs1_halt, hret1_halt⟩ :=
      liftedHaltValueBeh base1 s1 N1 w1 hN1
    obtain ⟨K2, ve2, _, _, _, _, _, hs2_halt, hret2_halt⟩ :=
      liftedHaltValueBeh base2 s2 N2 w2 hN2
    have hve : ValEqInf ve1 ve2 := fun i => hval i ve1 ve2 hs1_halt hs2_halt
    exact (hret ve1 ve2 hve).2.2 j w1 w2 ⟨N1 - K1, hret1_halt⟩ ⟨N2 - K2, hret2_halt⟩

/-! ### Phase 1b: Error transfer

If `compute [] env1 body` errors in N steps, and `EnvBehEq env1 env2`,
then `compute [] env2 body` also errors.

Proof by strong induction on N. At each step:
- Match on `body` to determine what `step` does.
- Var: lookup in env1/env2 both succeed or both fail (EnvBehEq domain agreement).
- Lam/Delay/Constant/Builtin: produce a value in 1-2 steps, never error from these.
- Error: both error.
- Apply/Force/Constr/Case: push a frame and evaluate a sub-term.
  The sub-term runs in the same env, with N' < N steps. By IH.
- When a closure is applied (in ret/funV/applyArg frames):
  VLam: body runs in closure_env.extend arg. Closure envs are EnvBehEq
  (they were captured from an EnvBehEq env). Args may differ but are ∀j ValueEq.
  So the extended env is EnvBehEq. By IH.
  VBuiltin: evalBuiltin depends on VCon constants (same by ValueEq 1) and
  pass-through returns (same constructor → same branch). By evalBuiltin
  agreement from ValueEq. -/

/-- BehBundle from ValEqInf for VLam closure application.
    If two VLam closures are ValEqInf and applied to ValEqInf args,
    the body computations are BehBundle related. -/
private theorem valEqInf_vlam_apply_behBundle
    (body1 body2 : Term) (cenv1 cenv2 : CekEnv) (arg1 arg2 : CekValue)
    (hclosure : ValEqInf (.VLam body1 cenv1) (.VLam body2 cenv2))
    (harg : ValEqInf arg1 arg2) :
    BehBundle (.compute [] (cenv1.extend arg1) body1)
              (.compute [] (cenv2.extend arg2) body2) := by
  refine ⟨⟨fun ⟨N, hN⟩ => ?_, fun ⟨N, hN⟩ => ?_⟩,
          ⟨fun ⟨v, N, hN⟩ => ?_, fun ⟨v, N, hN⟩ => ?_⟩,
          fun j v1 v2 ⟨N1, hN1⟩ ⟨N2, hN2⟩ => ?_⟩
  · -- error →: pick k = N, use ValueEq (N+1) for VLam
    have hve := hclosure (N + 1)
    unfold ValueEq at hve
    have ⟨herr, _, _⟩ := hve arg1 arg2 (harg N) N (Nat.le_refl N)
    exact ⟨N, herr.mp hN⟩
  · -- error ←
    have hve := hclosure (N + 1)
    unfold ValueEq at hve
    have ⟨herr, _, _⟩ := hve arg1 arg2 (harg N) N (Nat.le_refl N)
    exact ⟨N, herr.mpr hN⟩
  · -- halts →
    have hve := hclosure (N + 1)
    unfold ValueEq at hve
    have ⟨_, hfwd, _⟩ := hve arg1 arg2 (harg N) N (Nat.le_refl N)
    obtain ⟨v', hv', _⟩ := hfwd v hN
    exact ⟨v', N, hv'⟩
  · -- halts ←
    have hve := hclosure (N + 1)
    unfold ValueEq at hve
    have ⟨_, _, hbwd⟩ := hve arg1 arg2 (harg N) N (Nat.le_refl N)
    obtain ⟨v', hv', _⟩ := hbwd v hN
    exact ⟨v', N, hv'⟩
  · -- valueEq j
    -- Extend both to the same step count
    let M := max N1 N2
    have hM1 : steps M (.compute [] (cenv1.extend arg1) body1) = .halt v1 := by
      rw [show M = N1 + (M - N1) from by omega, steps_trans, hN1, steps_halt]
    have hM2 : steps M (.compute [] (cenv2.extend arg2) body2) = .halt v2 := by
      rw [show M = N2 + (M - N2) from by omega, steps_trans, hN2, steps_halt]
    have hve := hclosure (max M j + 1)
    unfold ValueEq at hve
    have hargs_k := harg (max M j)
    have ⟨_, hfwd, _⟩ := hve arg1 arg2 hargs_k M (by omega)
    obtain ⟨v2', hv2', hve'⟩ := hfwd v1 hM1
    rw [hM2] at hv2'; injection hv2' with hv2'; subst hv2'
    exact Moist.Verified.Congruence.valueEq_mono j (max M j) (by omega) _ _ hve'

/-- BehBundle from ValEqInf for VDelay forcing. -/
private theorem valEqInf_vdelay_force_behBundle
    (body1 body2 : Term) (env1 env2 : CekEnv)
    (hclosure : ValEqInf (.VDelay body1 env1) (.VDelay body2 env2)) :
    BehBundle (.compute [] env1 body1) (.compute [] env2 body2) := by
  refine ⟨⟨fun ⟨N, hN⟩ => ?_, fun ⟨N, hN⟩ => ?_⟩,
          ⟨fun ⟨v, N, hN⟩ => ?_, fun ⟨v, N, hN⟩ => ?_⟩,
          fun j v1 v2 ⟨N1, hN1⟩ ⟨N2, hN2⟩ => ?_⟩
  · have hve := hclosure (N + 1); unfold ValueEq at hve
    exact ⟨N, (hve N (Nat.le_refl N)).1.mp hN⟩
  · have hve := hclosure (N + 1); unfold ValueEq at hve
    exact ⟨N, (hve N (Nat.le_refl N)).1.mpr hN⟩
  · have hve := hclosure (N + 1); unfold ValueEq at hve
    obtain ⟨_, hfwd, _⟩ := hve N (Nat.le_refl N)
    obtain ⟨v', hv', _⟩ := hfwd v hN
    exact ⟨v', N, hv'⟩
  · have hve := hclosure (N + 1); unfold ValueEq at hve
    obtain ⟨_, _, hbwd⟩ := hve N (Nat.le_refl N)
    obtain ⟨v', hv', _⟩ := hbwd v hN
    exact ⟨v', N, hv'⟩
  · let M := max N1 N2
    have hM1 : steps M (.compute [] env1 body1) = .halt v1 := by
      rw [show M = N1 + (M - N1) from by omega, steps_trans, hN1, steps_halt]
    have hM2 : steps M (.compute [] env2 body2) = .halt v2 := by
      rw [show M = N2 + (M - N2) from by omega, steps_trans, hN2, steps_halt]
    have hve := hclosure (max M j + 1); unfold ValueEq at hve
    obtain ⟨_, hfwd, _⟩ := hve M (by omega)
    obtain ⟨v2', hv2', hve'⟩ := hfwd v1 hM1
    rw [hM2] at hv2'; injection hv2' with hv2'; subst hv2'
    exact Moist.Verified.Congruence.valueEq_mono j (max M j) (by omega) _ _ hve'

/-- Env relation at depth j: same domain, ValueEq j at each position.
    Weaker than EnvBehEq (which requires ValEqInf = ∀k ValueEq k). -/
private def EnvRelJ (j : Nat) (env1 env2 : CekEnv) : Prop :=
  (∀ n, env1.lookup n = none ↔ env2.lookup n = none) ∧
  (∀ n v1 v2, env1.lookup n = some v1 → env2.lookup n = some v2 → ValueEq j v1 v2)

private theorem envBehEq_to_envRelJ (j : Nat) {env1 env2 : CekEnv} (he : EnvBehEq env1 env2) :
    EnvRelJ j env1 env2 :=
  ⟨he.1, fun n v1 v2 h1 h2 => he.2 n v1 v2 h1 h2 j⟩

private theorem envRelJ_extend {j : Nat} {env1 env2 : CekEnv} {v1 v2 : CekValue}
    (he : EnvRelJ j env1 env2) (hv : ValueEq j v1 v2) :
    EnvRelJ j (env1.extend v1) (env2.extend v2) := by
  obtain ⟨hdom, hval⟩ := he
  constructor
  · intro n; match n with
    | 0 => simp [CekEnv.extend, CekEnv.lookup]
    | 1 => simp [CekEnv.extend, CekEnv.lookup]
    | n + 2 => simp [CekEnv.extend, CekEnv.lookup]; exact hdom (n + 1)
  · intro n w1 w2 h1 h2; match n with
    | 0 => simp [CekEnv.extend, CekEnv.lookup] at h1
    | 1 => simp [CekEnv.extend, CekEnv.lookup] at h1 h2; subst h1; subst h2; exact hv
    | n + 2 =>
      simp [CekEnv.extend, CekEnv.lookup] at h1 h2
      exact hval (n + 1) w1 w2 h1 h2

/-- Step-indexed stack relation: pointwise frame equivalence at depth j.
    Mirrors StackBehEq but uses ValueEq j instead of ValEqInf. -/
private inductive StackRelJ : Nat → Stack → Stack → Prop
  | nil : StackRelJ j [] []
  | force {s1 s2} (hs : StackRelJ j s1 s2) :
      StackRelJ j (.force :: s1) (.force :: s2)
  | arg {x env1 env2 s1 s2} (he : EnvRelJ j env1 env2) (hs : StackRelJ j s1 s2) :
      StackRelJ j (.arg x env1 :: s1) (.arg x env2 :: s2)
  | funVLam {body ρ1 ρ2 s1 s2} (he : EnvRelJ j ρ1 ρ2) (hs : StackRelJ j s1 s2) :
      StackRelJ j (.funV (.VLam body ρ1) :: s1) (.funV (.VLam body ρ2) :: s2)
  | funVBuiltin {b args1 args2 ea s1 s2}
      (hargs : ∀ k, k ≤ j → ListValueEq k args1 args2) (hs : StackRelJ j s1 s2) :
      StackRelJ j (.funV (.VBuiltin b args1 ea) :: s1) (.funV (.VBuiltin b args2 ea) :: s2)
  | constrField {tag done1 done2 todo env1 env2 s1 s2}
      (hdone : ∀ k, k ≤ j → ListValueEq k done1 done2)
      (he : EnvRelJ j env1 env2) (hs : StackRelJ j s1 s2) :
      StackRelJ j (.constrField tag done1 todo env1 :: s1) (.constrField tag done2 todo env2 :: s2)
  | caseScrutinee {alts env1 env2 s1 s2} (he : EnvRelJ j env1 env2) (hs : StackRelJ j s1 s2) :
      StackRelJ j (.caseScrutinee alts env1 :: s1) (.caseScrutinee alts env2 :: s2)
  | applyArg {v1 v2 s1 s2} (hv : ∀ k, k ≤ j → ValueEq k v1 v2)
      (hs : StackRelJ j s1 s2) :
      StackRelJ j (.applyArg v1 :: s1) (.applyArg v2 :: s2)
  | funVGeneral {v1 v2 s1 s2} (hv : ∀ k, k ≤ j → ValueEq k v1 v2) (hs : StackRelJ j s1 s2) :
      StackRelJ j (.funV v1 :: s1) (.funV v2 :: s2)

/-- Monotonicity of EnvRelJ: if j ≤ k then EnvRelJ k → EnvRelJ j. -/
private theorem envRelJ_mono {j k : Nat} (hjk : j ≤ k) {env1 env2 : CekEnv}
    (he : EnvRelJ k env1 env2) : EnvRelJ j env1 env2 :=
  ⟨he.1, fun n v1 v2 h1 h2 => Moist.Verified.Congruence.valueEq_mono j k hjk v1 v2 (he.2 n v1 v2 h1 h2)⟩

/-- Monotonicity of StackRelJ: if j ≤ k then StackRelJ k → StackRelJ j. -/
private theorem stackRelJ_mono {j k : Nat} (hjk : j ≤ k) {s1 s2 : Stack}
    (hs : StackRelJ k s1 s2) : StackRelJ j s1 s2 := by
  induction hs with
  | nil => exact .nil
  | force _ ih => exact .force ih
  | arg he _ ih => exact .arg (envRelJ_mono hjk he) ih
  | funVLam he _ ih => exact .funVLam (envRelJ_mono hjk he) ih
  | funVBuiltin hargs _ ih =>
    exact .funVBuiltin (fun k' hk' => hargs k' (by omega)) ih
  | constrField hdone he _ ih =>
    exact .constrField (fun k' hk' => hdone k' (by omega)) (envRelJ_mono hjk he) ih
  | caseScrutinee he _ ih => exact .caseScrutinee (envRelJ_mono hjk he) ih
  | applyArg hv _ ih =>
    exact .applyArg (fun k' hk' => hv k' (by omega)) ih
  | funVGeneral hv _ ih =>
    exact .funVGeneral (fun k' hk' => hv k' (by omega)) ih

/-- Abbreviation for the bounded triple proposition used throughout. -/
private abbrev BoundedTriple (j n : Nat) (s1 s2 : State) : Prop :=
  (s1 = .error ↔ s2 = .error) ∧
  (∀ v1, s1 = .halt v1 → ∃ v2, s2 = .halt v2 ∧ ValueEq j v1 v2) ∧
  (∀ v2, s2 = .halt v2 → ∃ v1, s1 = .halt v1 ∧ ValueEq j v1 v2)

/-- Helper: BoundedTriple is trivially true when neither state is error or halt. -/
private theorem boundedTriple_neither {j : Nat} {s1 s2 : State}
    (h1e : s1 ≠ .error) (h1h : ∀ v, s1 ≠ .halt v)
    (h2e : s2 ≠ .error) (h2h : ∀ v, s2 ≠ .halt v) :
    BoundedTriple j 0 s1 s2 :=
  ⟨⟨fun h => absurd h h1e, fun h => absurd h h2e⟩,
   fun v h => absurd h (h1h v),
   fun v h => absurd h (h2h v)⟩

/-- Helper: StackRelJ j for applyArg frames from lists with ListValueEq k for all k ≤ j. -/
private theorem stackRelJ_append_applyArg {j : Nat} {fs1 fs2 : List CekValue}
    {s1 s2 : Stack}
    (hfs : ∀ k, k ≤ j → ListValueEq k fs1 fs2) (hs : StackRelJ j s1 s2) :
    StackRelJ j (fs1.map Frame.applyArg ++ s1) (fs2.map Frame.applyArg ++ s2) := by
  induction fs1 generalizing fs2 with
  | nil =>
    cases fs2 with
    | nil => simp; exact hs
    | cons _ _ => have h0 := hfs 0; simp [ListValueEq] at h0
  | cons f1 fs1' ih =>
    cases fs2 with
    | nil => have h0 := hfs 0; simp [ListValueEq] at h0
    | cons f2 fs2' =>
      simp [List.map, List.append]
      have hhead : ∀ k, k ≤ j → ValueEq k f1 f2 := by
        intro k hk; have hk' := hfs k hk; simp [ListValueEq] at hk'; exact hk'.1
      have htail : ∀ k, k ≤ j → ListValueEq k fs1' fs2' := by
        intro k hk; have hk' := hfs k hk; simp [ListValueEq] at hk'; exact hk'.2
      exact .applyArg hhead (ih htail)

/-- ListValueEq k for appended lists. -/
private theorem listValueEq_append {k : Nat} {a1 a2 b1 b2 : List CekValue}
    (ha : ListValueEq k a1 a2) (hb : ListValueEq k b1 b2) :
    ListValueEq k (a1 ++ b1) (a2 ++ b2) := by
  induction a1 generalizing a2 with
  | nil =>
    cases a2 with
    | nil => simp; exact hb
    | cons _ _ => simp [ListValueEq] at ha
  | cons x xs ih =>
    cases a2 with
    | nil => simp [ListValueEq] at ha
    | cons y ys =>
      simp [ListValueEq] at ha ⊢; exact ⟨ha.1, ih ha.2⟩

/-- ListValueEq k for reversed lists. -/
private theorem listValueEq_reverse {k : Nat} {a1 a2 : List CekValue}
    (h : ListValueEq k a1 a2) :
    ListValueEq k a1.reverse a2.reverse := by
  induction a1 generalizing a2 with
  | nil =>
    cases a2 with
    | nil => simp [ListValueEq]
    | cons _ _ => simp [ListValueEq] at h
  | cons x xs ih =>
    cases a2 with
    | nil => simp [ListValueEq] at h
    | cons y ys =>
      simp [ListValueEq] at h
      simp [List.reverse_cons]
      exact listValueEq_append (ih h.2) (show ListValueEq k [x] [y] by simp [ListValueEq]; exact h.1)

/-- evalBuiltin congruence at specific index k from ListValueEq (k+1).
    Only needs ListValueEq at one level above the target. -/
private theorem evalBuiltin_cong_at (k : Nat) (b : BuiltinFun)
    {args1 args2 : List CekValue} (hargs : ListValueEq (k + 1) args1 args2) :
    (Moist.CEK.evalBuiltin b args1 = none ↔
     Moist.CEK.evalBuiltin b args2 = none) ∧
    (∀ r1 r2, Moist.CEK.evalBuiltin b args1 = some r1 →
              Moist.CEK.evalBuiltin b args2 = some r2 →
              ValueEq k r1 r2) := by
  cases args1 with
  | nil =>
    cases args2 with
    | nil => exact ⟨Iff.rfl, fun r1 r2 h1 h2 => by rw [h1] at h2; injection h2 with h; subst h; exact valueEq_refl k r1⟩
    | cons _ _ => simp [ListValueEq] at hargs
  | cons a1 as1 =>
    cases args2 with
    | nil => simp [ListValueEq] at hargs
    | cons a2 as2 =>
      simp [ListValueEq] at hargs
      have htail_hi := Moist.Verified.Congruence.listValueEq_mono (k + 1) (k + 1) (Nat.le_refl _) as1 as2 hargs.2
      have hmid := Moist.Verified.Congruence.evalBuiltin_cong k b a1 as1 as2 htail_hi
      have hlast := Moist.Verified.Congruence.evalBuiltin_cong_first k b a1 a2 as2 hargs.1
      refine ⟨hmid.1.trans hlast.1, ?_⟩
      intro r1 r2 hr1 hr2
      cases hmidv : Moist.CEK.evalBuiltin b (a1 :: as2) with
      | none =>
        have : Moist.CEK.evalBuiltin b (a1 :: as1) = none := hmid.1.mpr hmidv
        rw [hr1] at this; simp at this
      | some rm =>
        exact valueEq_trans k _ _ _ (hmid.2 r1 rm hr1 hmidv) (hlast.2 rm r2 hmidv hr2)

/-- Lift bounded triples through stacks.
    Given inner agreement at empty stacks and IH for ret processing,
    derive agreement for the lifted (stacked) computation. -/
private theorem bounded_lift_triple {j' : Nat} (m : Nat) (hm : m ≤ j')
    (stk1 stk2 : Stack) (hstk : StackRelJ (j' + 1) stk1 stk2)
    (s1 s2 : State)
    (hinner : ∀ n, n ≤ j' →
      (steps n s1 = .error ↔ steps n s2 = .error) ∧
      (∀ v1, steps n s1 = .halt v1 → ∃ v2, steps n s2 = .halt v2 ∧ ValueEq j' v1 v2) ∧
      (∀ v2, steps n s2 = .halt v2 → ∃ v1, steps n s1 = .halt v1 ∧ ValueEq j' v1 v2))
    (ihm : ∀ m', m' < m + 1 → m' ≤ j' + 1 →
      (∀ stk1' stk2' env1 env2 body, StackRelJ (j' + 1) stk1' stk2' → EnvRelJ (j' + 1) env1 env2 →
        BoundedTriple (j' + 1) m' (steps m' (.compute stk1' env1 body)) (steps m' (.compute stk2 env2 body))) ∧
      (∀ stk1' stk2' v1 v2, StackRelJ (j' + 1) stk1' stk2' → (∀ k, k ≤ j' + 1 → ValueEq k v1 v2) →
        BoundedTriple (j' + 1) m' (steps m' (.ret stk1' v1)) (steps m' (.ret stk2' v2)))) :
    BoundedTriple (j' + 1) 0 (steps m (liftState stk1 s1)) (steps m (liftState stk2 s2)) := by
  sorry /- NOTE: This has a fundamental issue. BoundedTriple requires EXACT step-count
  agreement (steps m s1 = halt ↔ steps m s2 = halt), but when inner computations
  (s1, s2) take different numbers of steps to halt, the total step counts for the
  lifted computations also differ. The halt case cannot guarantee steps m = halt
  on both sides simultaneously. The proof below documents the issue.
  The computation liftState stk s runs the inner computation s; when s becomes
  -- halt v or ret [] v, the lifted state becomes ret stk v; when s becomes error,
  -- the lifted state becomes error.
  -- We analyze what happens at step m.
  refine ⟨⟨fun herr => ?_, fun herr => ?_⟩, fun w1 hw1 => ?_, fun w2 hw2 => ?_⟩
  · -- error forward: steps m (liftState stk1 s1) = .error
    obtain ⟨K, hK_le, _, _, hcase⟩ := liftedErrorValueBeh stk1 s1 m herr
    cases hcase with
    | inl hs_err =>
      -- Inner errored at step K ≤ m ≤ j'
      have h2_err := (hinner K (by omega)).1.mp hs_err
      -- s2 also errors at step K, so liftState stk2 s2 errors
      have : isActive (steps K s2) = false := by rw [h2_err]; rfl
      obtain ⟨K2, _, hK2_inact, hK2_min⟩ := firstInactiveBeh s2 K ⟨K, Nat.le_refl _, this⟩
      have hcomm2 := steps_liftState stk2 K2 s2 hK2_min
      -- steps K2 s2 is inactive. It must be error (since steps K s2 = error, K2 ≤ K).
      -- Actually K2 might be < K, but steps K2 s2 is inactive and ≤ K steps s2 = error.
      -- If K2 = K, done. If K2 < K, steps K2 s2 is inactive: error, halt, or ret [].
      -- If halt or ret [], then steps K s2 would be halt (by forward propagation), not error. Contradiction.
      have hK2_err : steps K2 s2 = .error := by
        generalize h_sK2 : steps K2 s2 = sK2 at hK2_inact
        match sK2 with
        | .compute .. => simp [isActive] at hK2_inact
        | .ret (_ :: _) _ => simp [isActive] at hK2_inact
        | .error => rfl
        | .halt v =>
          exfalso
          have : steps K s2 = .halt v := by
            rw [show K = K2 + (K - K2) from by omega, steps_trans, h_sK2, steps_halt]
          rw [h2_err] at this; simp at this
        | .ret [] v =>
          exfalso
          have : steps (K2 + 1) s2 = .halt v := by rw [steps_trans, h_sK2]; rfl
          have : steps K s2 = .halt v := by
            rw [show K = (K2 + 1) + (K - (K2 + 1)) from by omega, steps_trans, this, steps_halt]
          rw [h2_err] at this; simp at this
      rw [hcomm2, hK2_err]; simp [liftState]
      exact ⟨K2, rfl⟩
    | inr ⟨ve1, _, _, hs1_halt, hret_err⟩ =>
      -- Inner halted at step K with value ve1. Then ret stk1 ve1 errored in m-K remaining steps.
      obtain ⟨K1, hK1⟩ := hs1_halt
      have hK1_le : K1 ≤ m := by omega
      obtain ⟨ve2, _, hve⟩ := (hinner K1 (by omega)).2.1 ve1 hK1
      -- ve2 exists, s2 halts with ve2
      -- Now build ValueEq k for all k ≤ j'+1
      have hvek : ∀ k, k ≤ j' + 1 → ValueEq k ve1 ve2 := by
        intro k hk
        cases k with
        | zero => simp [ValueEq]
        | succ k' =>
          exact Moist.Verified.Congruence.valueEq_mono (k' + 1) j' (by omega) _ _ hve
      -- Use ihm for the ret computation
      have hret_bt := (ihm (m - K) (by omega) (by omega)).2 stk1 stk2 ve1 ve2 hstk hvek
      -- hret_bt gives BoundedTriple for steps (m-K) (ret stk1 ve1) vs steps (m-K) (ret stk2 ve2)
      have hret1_err := hret_bt.1.mp hret_err
      -- Now compose: liftState stk2 s2 → ret stk2 ve2 → error
      exact liftState_compose stk2 s2 .error ve2 ⟨K1, (hinner K1 (by omega)).2.1 ve1 hK1 |>.choose_spec.1⟩
        ⟨m - K, hret1_err⟩
  · -- error backward: symmetric
    obtain ⟨K, hK_le, _, _, hcase⟩ := liftedErrorValueBeh stk2 s2 m herr
    cases hcase with
    | inl hs_err =>
      have h1_err := (hinner K (by omega)).1.mpr hs_err
      have : isActive (steps K s1) = false := by rw [h1_err]; rfl
      obtain ⟨K1, _, hK1_inact, hK1_min⟩ := firstInactiveBeh s1 K ⟨K, Nat.le_refl _, this⟩
      have hcomm1 := steps_liftState stk1 K1 s1 hK1_min
      have hK1_err : steps K1 s1 = .error := by
        generalize h_sK1 : steps K1 s1 = sK1 at hK1_inact
        match sK1 with
        | .compute .. => simp [isActive] at hK1_inact
        | .ret (_ :: _) _ => simp [isActive] at hK1_inact
        | .error => rfl
        | .halt v =>
          exfalso
          have : steps K s1 = .halt v := by
            rw [show K = K1 + (K - K1) from by omega, steps_trans, h_sK1, steps_halt]
          rw [h1_err] at this; simp at this
        | .ret [] v =>
          exfalso
          have : steps (K1 + 1) s1 = .halt v := by rw [steps_trans, h_sK1]; rfl
          have : steps K s1 = .halt v := by
            rw [show K = (K1 + 1) + (K - (K1 + 1)) from by omega, steps_trans, this, steps_halt]
          rw [h1_err] at this; simp at this
      rw [hcomm1, hK1_err]; simp [liftState]
      exact ⟨K1, rfl⟩
    | inr ⟨ve2, _, _, hs2_halt, hret_err⟩ =>
      obtain ⟨K2, hK2⟩ := hs2_halt
      obtain ⟨ve1, _, hve⟩ := (hinner K2 (by omega)).2.2 ve2 hK2
      have hvek : ∀ k, k ≤ j' + 1 → ValueEq k ve1 ve2 := by
        intro k hk; cases k with
        | zero => simp [ValueEq]
        | succ k' => exact Moist.Verified.Congruence.valueEq_mono (k' + 1) j' (by omega) _ _ hve
      have hret_bt := (ihm (m - K) (by omega) (by omega)).2 stk1 stk2 ve1 ve2 hstk hvek
      have hret1_err := hret_bt.1.mpr hret_err
      exact liftState_compose stk1 s1 .error ve1 ⟨K2, (hinner K2 (by omega)).2.2 ve2 hK2 |>.choose_spec.1⟩
        ⟨m - K, hret1_err⟩
  · -- halt forward: steps m (liftState stk1 s1) = .halt w1
    obtain ⟨K, ve1, hK_le, _, _, _, _, hs1_halt, hret_halt⟩ :=
      liftedHaltValueBeh stk1 s1 m w1 hw1
    obtain ⟨K1, hK1⟩ := hs1_halt
    obtain ⟨ve2, _, hve⟩ := (hinner K1 (by omega)).2.1 ve1 hK1
    have hvek : ∀ k, k ≤ j' + 1 → ValueEq k ve1 ve2 := by
      intro k hk; cases k with
      | zero => simp [ValueEq]
      | succ k' => exact Moist.Verified.Congruence.valueEq_mono (k' + 1) j' (by omega) _ _ hve
    have hret_bt := (ihm (m - K) (by omega) (by omega)).2 stk1 stk2 ve1 ve2 hstk hvek
    obtain ⟨w2, hw2_halt, hweq⟩ := hret_bt.2.1 w1 hret_halt
    -- Need to show steps m (liftState stk2 s2) = .halt w2
    -- We know s2 halts with ve2 at step K1, and ret stk2 ve2 halts with w2 in m-K steps.
    -- But we need to compose through liftState.
    have hs2_halt_reach : Reaches s2 (.halt ve2) :=
      ⟨K1, (hinner K1 (by omega)).2.1 ve1 hK1 |>.choose_spec.1⟩
    have hlifted := liftState_compose stk2 s2 (.halt w2) ve2 hs2_halt_reach ⟨m - K, hw2_halt⟩
    -- hlifted : Reaches (liftState stk2 s2) (.halt w2)
    -- But we need: steps m (liftState stk2 s2) = .halt w2, not just Reaches.
    -- Reaches only gives ∃ N, steps N ... = .halt w2. We need it at EXACTLY m steps.
    -- This doesn't directly give us that. We need a more careful argument.
    -- Actually, we need to track the exact step count. The inner takes K1 steps (or K steps
    -- if measured from the first inactive point), and the outer takes m-K steps.
    -- Total: K + (m-K) = m steps. But only if K1 = K.
    -- Actually K1 is from hs1_halt : Reaches s1 (.halt ve1), and K is from liftedHaltValueBeh.
    -- liftedHaltValueBeh gives K such that inner first becomes inactive at K.
    -- hs1_halt gives K1 such that steps K1 s1 = .halt ve1.
    -- K could differ from K1 (if inner becomes ret [] v at K, then halt at K+1 = K1).
    -- We need: steps m (liftState stk2 s2) = .halt w2.
    -- Key: K1 ≤ K and K ≤ m. The inner reaches halt at K1, the first inactive is at K.
    -- Actually, from liftedHaltValueBeh:
    --   K is the first inactive step, and steps K s1 = halt ve1 or ret [] ve1.
    --   liftState stk1 (steps K s1) = ret stk1 ve1.
    --   steps K (liftState stk1 s1) = ret stk1 ve1 (from the commutation).
    --   steps (m-K) (ret stk1 ve1) = halt w1.
    -- For s2: we need the inner to reach halt/ret[] at some step K', then the outer to take m-K' steps.
    -- But we don't control K'. The inner might take a different number of steps.
    -- PROBLEM: we can't guarantee that the total for s2 is exactly m steps.
    -- BoundedTriple only looks at EXACTLY m steps, not "within m steps".
    -- So this approach FAILS for the halt case when the inner computations take different numbers of steps.
    sorry
  · sorry -/

/-- Combined bounded bisimulation theorem. Proved by strong induction on j,
    then strong induction on n within each j. The gen (compute) and ret parts
    are proved together since they are mutually recursive through step. -/
private theorem bounded_bisim_combined :
    ∀ j n, n ≤ j →
    (∀ (stk1 stk2 : Stack) (env1 env2 : CekEnv) (body : Moist.Plutus.Term.Term),
      StackRelJ j stk1 stk2 → EnvRelJ j env1 env2 →
        BoundedTriple j n (steps n (.compute stk1 env1 body)) (steps n (.compute stk2 env2 body))) ∧
    (∀ (stk1 stk2 : Stack) (v1 v2 : CekValue),
      StackRelJ j stk1 stk2 → (∀ k, k ≤ j → ValueEq k v1 v2) →
        BoundedTriple j n (steps n (.ret stk1 v1)) (steps n (.ret stk2 v2))) := by
  -- Strong induction on j
  intro j
  induction j using Nat.strongRecOn with | _ j ihj => ?_
  -- Strong induction on n
  intro n
  induction n using Nat.strongRecOn with | _ n ihn => ?_
  intro hn
  -- Base case: n = 0
  cases n with
  | zero =>
    refine ⟨fun _ _ _ _ _ _ _ => ⟨⟨fun h => ?_, fun h => ?_⟩, fun _ h => ?_, fun _ h => ?_⟩,
            fun _ _ _ _ _ _ => ⟨⟨fun h => ?_, fun h => ?_⟩, fun _ h => ?_, fun _ h => ?_⟩⟩ <;> simp [steps] at h
  | succ m =>
  -- j must be > 0 for n = m+1 ≤ j
  cases j with
  | zero => omega
  | succ j' =>
  -- Now j = j'+1, n = m+1, m+1 ≤ j'+1 so m ≤ j'
  -- Inner IH on n: for step counts < m+1
  have ihm : ∀ m', m' < m + 1 → m' ≤ j' + 1 →
    (∀ stk1 stk2 env1 env2 body, StackRelJ (j' + 1) stk1 stk2 → EnvRelJ (j' + 1) env1 env2 →
      BoundedTriple (j' + 1) m' (steps m' (.compute stk1 env1 body)) (steps m' (.compute stk2 env2 body))) ∧
    (∀ stk1 stk2 v1 v2, StackRelJ (j' + 1) stk1 stk2 → (∀ k, k ≤ j' + 1 → ValueEq k v1 v2) →
      BoundedTriple (j' + 1) m' (steps m' (.ret stk1 v1)) (steps m' (.ret stk2 v2))) :=
    fun m' hm' hm'j => ihn m' hm' hm'j
  -- Outer IH on j: for all depths k' < j'+1 and any step count n' ≤ k'
  have ihj_at : ∀ k', k' < j' + 1 → ∀ n', n' ≤ k' →
    (∀ stk1 stk2 env1 env2 body, StackRelJ k' stk1 stk2 → EnvRelJ k' env1 env2 →
      BoundedTriple k' n' (steps n' (.compute stk1 env1 body)) (steps n' (.compute stk2 env2 body))) ∧
    (∀ stk1 stk2 v1 v2, StackRelJ k' stk1 stk2 → (∀ k, k ≤ k' → ValueEq k v1 v2) →
      BoundedTriple k' n' (steps n' (.ret stk1 v1)) (steps n' (.ret stk2 v2))) :=
    fun k' hk' n' hn' => ihj k' hk' n' hn'
  -- Error helper
  have err_bt : ∀ k, BoundedTriple (j' + 1) 0 (steps k .error) (steps k .error) := by
    intro k; simp [steps_error]; exact ⟨Iff.rfl, fun _ h => by simp at h, fun _ h => by simp at h⟩
  constructor
  · -- ===== Compute part (n = m+1, j = j'+1) =====
    intro stk1 stk2 env1 env2 body hstk henv
    change BoundedTriple _ _ (steps m (step (.compute stk1 env1 body))) (steps m (step (.compute stk2 env2 body)))
    cases body with
    | Error => exact err_bt m
    | Var idx =>
      show BoundedTriple _ _ (steps m (match env1.lookup idx with | some v => .ret stk1 v | none => .error))
                             (steps m (match env2.lookup idx with | some v => .ret stk2 v | none => .error))
      have ⟨hdom, hval⟩ := henv
      cases h1 : env1.lookup idx with
      | none => simp only [h1, (hdom idx).mp h1]; exact err_bt m
      | some v1 =>
        cases h2 : env2.lookup idx with
        | none => exact absurd ((hdom idx).mpr h2) (by simp [h1])
        | some v2 =>
          simp only [h1, h2]
          have hve := hval idx v1 v2 h1 h2
          exact (ihm m (by omega) (by omega)).2 stk1 stk2 v1 v2 hstk (fun k hk => by
            cases k with | zero => simp [ValueEq]
                         | succ k' => exact Moist.Verified.Congruence.valueEq_mono (k' + 1) (j' + 1) hk v1 v2 hve)
    | Apply f x =>
      show BoundedTriple _ _ (steps m (.compute (.arg x env1 :: stk1) env1 f))
                             (steps m (.compute (.arg x env2 :: stk2) env2 f))
      exact (ihm m (by omega) (by omega)).1 _ _ _ _ f (.arg henv hstk) henv
    | Force e =>
      show BoundedTriple _ _ (steps m (.compute (.force :: stk1) env1 e))
                             (steps m (.compute (.force :: stk2) env2 e))
      exact (ihm m (by omega) (by omega)).1 _ _ _ _ e (.force hstk) henv
    | Case scrut alts =>
      show BoundedTriple _ _ (steps m (.compute (.caseScrutinee alts env1 :: stk1) env1 scrut))
                             (steps m (.compute (.caseScrutinee alts env2 :: stk2) env2 scrut))
      exact (ihm m (by omega) (by omega)).1 _ _ _ _ scrut (.caseScrutinee henv hstk) henv
    | Constr tag args =>
      cases args with
      | nil =>
        show BoundedTriple _ _ (steps m (.ret stk1 (.VConstr tag [])))
                               (steps m (.ret stk2 (.VConstr tag [])))
        exact (ihm m (by omega) (by omega)).2 _ _ _ _ hstk (fun k _ => valueEq_refl k _)
      | cons a as =>
        show BoundedTriple _ _ (steps m (.compute (.constrField tag [] as env1 :: stk1) env1 a))
                               (steps m (.compute (.constrField tag [] as env2 :: stk2) env2 a))
        exact (ihm m (by omega) (by omega)).1 _ _ _ _ a
          (.constrField (fun _ _ => by simp [ListValueEq]) henv hstk) henv
    | Constant p =>
      obtain ⟨c, ty⟩ := p
      show BoundedTriple _ _ (steps m (.ret stk1 (.VCon c))) (steps m (.ret stk2 (.VCon c)))
      exact (ihm m (by omega) (by omega)).2 _ _ _ _ hstk (fun k _ => valueEq_refl k _)
    | Builtin b =>
      show BoundedTriple _ _ (steps m (.ret stk1 (.VBuiltin b [] (expectedArgs b))))
                             (steps m (.ret stk2 (.VBuiltin b [] (expectedArgs b))))
      exact (ihm m (by omega) (by omega)).2 _ _ _ _ hstk (fun k _ => valueEq_refl k _)
    | Lam _n body =>
      show BoundedTriple _ _ (steps m (.ret stk1 (.VLam body env1)))
                             (steps m (.ret stk2 (.VLam body env2)))
      have hvek : ∀ k, k ≤ j' + 1 → ValueEq k (.VLam body env1) (.VLam body env2) := by
        intro k hk; cases k with
        | zero => simp [ValueEq]
        | succ k' =>
          -- k' ≤ j', so k' < j'+1
          unfold ValueEq; intro arg1 arg2 hargs n' hn'
          -- Use outer IH at depth k' with EnvRelJ k' extended env
          have henv_k' := envRelJ_extend (envRelJ_mono (show k' ≤ j' + 1 by omega) henv) hargs
          exact (ihj_at k' (by omega) n' (by omega)).1 [] [] _ _ body .nil henv_k'
      exact (ihm m (by omega) (by omega)).2 _ _ _ _ hstk hvek
    | Delay body =>
      show BoundedTriple _ _ (steps m (.ret stk1 (.VDelay body env1)))
                             (steps m (.ret stk2 (.VDelay body env2)))
      have hvek : ∀ k, k ≤ j' + 1 → ValueEq k (.VDelay body env1) (.VDelay body env2) := by
        intro k hk; cases k with
        | zero => simp [ValueEq]
        | succ k' =>
          unfold ValueEq; intro n' hn'
          exact (ihj_at k' (by omega) n' (by omega)).1 [] [] _ _ body .nil (envRelJ_mono (by omega) henv)
      exact (ihm m (by omega) (by omega)).2 _ _ _ _ hstk hvek
  · -- ===== Ret part (n = m+1, j = j'+1) =====
    intro stk1 stk2 v1 v2 hstk hvek
    change BoundedTriple _ _ (steps m (step (.ret stk1 v1))) (steps m (step (.ret stk2 v2)))
    cases hstk with
    | nil =>
      show BoundedTriple _ _ (steps m (.halt v1)) (steps m (.halt v2))
      simp [steps_halt]
      exact ⟨⟨fun h => by simp at h, fun h => by simp at h⟩,
             fun w h => by injection h with h; subst h; exact ⟨v2, rfl, hvek (j' + 1) (Nat.le_refl _)⟩,
             fun w h => by injection h with h; subst h; exact ⟨v1, rfl, hvek (j' + 1) (Nat.le_refl _)⟩⟩
    | @arg x env1' env2' s1 s2 he' hs =>
      -- step: .compute (.funV v1 :: s1) env1' x and .compute (.funV v2 :: s2) env2' x
      show BoundedTriple _ _ (steps m (.compute (.funV v1 :: s1) env1' x))
                             (steps m (.compute (.funV v2 :: s2) env2' x))
      exact (ihm m (by omega) (by omega)).1 _ _ _ _ x (.funVGeneral hvek hs) he'
    | @funVLam body ρ1 ρ2 s1 s2 he' hs =>
      -- step: .compute s1 (ρ1.extend v1) body vs .compute s2 (ρ2.extend v2) body
      show BoundedTriple _ _ (steps m (.compute s1 (ρ1.extend v1) body))
                             (steps m (.compute s2 (ρ2.extend v2) body))
      exact (ihm m (by omega) (by omega)).1 _ _ _ _ body hs
        (envRelJ_extend he' (hvek (j' + 1) (Nat.le_refl _)))
    | @funVBuiltin b args1 args2 ea s1 s2 hargs' hs =>
      -- step: apply builtin
      show BoundedTriple _ _ (steps m (step (.ret (.funV (.VBuiltin b args1 ea) :: s1) v1)))
                             (steps m (step (.ret (.funV (.VBuiltin b args2 ea) :: s2) v2)))
      simp only [step]
      cases hhead : ea.head with
      | argV =>
        simp only [hhead]
        cases htail : ea.tail with
        | some rest =>
          simp only [htail]
          have hvek' : ∀ k, k ≤ j' + 1 → ValueEq k (.VBuiltin b (v1 :: args1) rest) (.VBuiltin b (v2 :: args2) rest) := by
            intro k hk; cases k with
            | zero => simp [ValueEq]
            | succ k' =>
              unfold ValueEq
              have hargs_k' : ListValueEq k' (v1 :: args1) (v2 :: args2) := by
                simp [ListValueEq]
                exact ⟨Moist.Verified.Congruence.valueEq_mono k' (j' + 1) (by omega) _ _ (hvek (j' + 1) (Nat.le_refl _)),
                       hargs' k' (by omega)⟩
              have ⟨hnone_k, hsome_k⟩ := evalBuiltin_cong_at k' b (by
                simp [ListValueEq]
                exact ⟨hvek (k' + 1) (by omega), Moist.Verified.Congruence.listValueEq_mono (k' + 1) (j' + 1) (by omega) _ _ (hargs' (j' + 1) (Nat.le_refl _))⟩)
              exact ⟨rfl, hargs_k', rfl, hnone_k, hsome_k⟩
          exact (ihm m (by omega) (by omega)).2 _ _ _ _ hs hvek'
        | none =>
          simp only [htail]
          -- evalBuiltin with (v :: args)
          have hargsfull : ∀ k, k ≤ j' + 1 → ListValueEq k (v1 :: args1) (v2 :: args2) := by
            intro k hk
            simp [ListValueEq]
            exact ⟨Moist.Verified.Congruence.valueEq_mono k (j' + 1) hk _ _ (hvek (j' + 1) (Nat.le_refl _)),
                   hargs' k hk⟩
          have ⟨hnone_iff, hsome_val⟩ := evalBuiltin_cong_at j' b (hargsfull (j' + 1) (Nat.le_refl _))
          cases hev1 : evalBuiltin b (v1 :: args1) with
          | none =>
            simp only [hev1]
            have hev2 : evalBuiltin b (v2 :: args2) = none := hnone_iff.mp hev1
            simp only [hev2]; exact err_bt m
          | some r1 =>
            simp only [hev1]
            cases hev2 : evalBuiltin b (v2 :: args2) with
            | none => exact absurd (hnone_iff.mpr hev2) (by simp [hev1])
            | some r2 =>
              simp only [hev2]
              have hvr : ∀ k, k ≤ j' + 1 → ValueEq k r1 r2 := by
                intro k hk
                cases k with
                | zero => simp [ValueEq]
                | succ k' =>
                  exact Moist.Verified.Congruence.valueEq_mono (k' + 1) j' (by omega) _ _ (hsome_val r1 r2 hev1 hev2)
              exact (ihm m (by omega) (by omega)).2 _ _ _ _ hs hvr
      | argQ =>
        simp only [hhead]; exact err_bt m
    | @constrField tag done1 done2 todo env1' env2' s1 s2 hdone he' hs =>
      cases todo with
      | cons m' ms =>
        show BoundedTriple _ _ (steps m (.compute (.constrField tag (v1 :: done1) ms env1' :: s1) env1' m'))
                               (steps m (.compute (.constrField tag (v2 :: done2) ms env2' :: s2) env2' m'))
        exact (ihm m (by omega) (by omega)).1 _ _ _ _ m'
          (.constrField (fun k hk => by simp [ListValueEq]; exact ⟨hvek k hk, hdone k hk⟩) he' hs) he'
      | nil =>
        show BoundedTriple _ _ (steps m (.ret s1 (.VConstr tag ((v1 :: done1).reverse))))
                               (steps m (.ret s2 (.VConstr tag ((v2 :: done2).reverse))))
        have hvek' : ∀ k, k ≤ j' + 1 → ValueEq k (.VConstr tag ((v1 :: done1).reverse)) (.VConstr tag ((v2 :: done2).reverse)) := by
          intro k hk; cases k with
          | zero => simp [ValueEq]
          | succ k' =>
            unfold ValueEq; constructor
            · rfl
            · exact listValueEq_reverse (by simp [ListValueEq]; exact ⟨hvek k' (by omega), hdone k' (by omega)⟩)
        exact (ihm m (by omega) (by omega)).2 _ _ _ _ hs hvek'
    | @caseScrutinee alts env1' env2' s1 s2 he' hs =>
      -- Case dispatch: case split on v1/v2 (scrutinee)
      have hv1' := hvek 1 (by omega)
      -- Match value constructors using ValueEq 1
      cases v1 with
      | VConstr tag1 fields1 =>
        cases v2 with
        | VConstr tag2 fields2 =>
          have hvj := hvek (j' + 1) (Nat.le_refl _); unfold ValueEq at hvj
          obtain ⟨htag, hfields⟩ := hvj; subst htag
          simp only [step]
          cases halt : alts[tag1]? with
          | none => simp only [halt]; exact err_bt m
          | some alt =>
            simp only [halt]
            have hfs_all : ∀ k, k ≤ j' + 1 → ListValueEq k fields1 fields2 :=
              fun k hk => Moist.Verified.Congruence.listValueEq_mono k j' (by omega) _ _ hfields
            exact (ihm m (by omega) (by omega)).1 _ _ _ _ alt
              (stackRelJ_append_applyArg hfs_all hs) he'
        | _ => simp [ValueEq] at hv1'
      | VCon c1 =>
        cases v2 with
        | VCon c2 =>
          have hceq := (hvek 1 (by omega) : ValueEq 1 (.VCon c1) (.VCon c2))
          simp [ValueEq] at hceq; subst hceq
          simp only [step]
          cases hctf : constToTagAndFields c1 with
          | none => simp only [hctf]; exact err_bt m
          | some tnf =>
            obtain ⟨tag, numCtors, fields⟩ := tnf; simp only [hctf]
            cases hguard : (decide (numCtors > 0) && decide (alts.length > numCtors)) with
            | true => simp only [hguard]; exact err_bt m
            | false =>
              simp only [hguard]
              cases halt : alts[tag]? with
              | none => simp only [halt]; exact err_bt m
              | some alt =>
                simp only [halt]
                exact (ihm m (by omega) (by omega)).1 _ _ _ _ alt
                  (stackRelJ_append_applyArg (fun k _ => listValueEq_refl k fields) hs) he'
        | _ => simp [ValueEq] at hv1'
      | VLam _ _ =>
        cases v2 with
        | VLam _ _ => simp only [step]; exact err_bt m
        | _ => simp [ValueEq] at hv1'
      | VDelay _ _ =>
        cases v2 with
        | VDelay _ _ => simp only [step]; exact err_bt m
        | _ => simp [ValueEq] at hv1'
      | VBuiltin _ _ _ =>
        cases v2 with
        | VBuiltin _ _ _ => simp only [step]; exact err_bt m
        | _ => simp [ValueEq] at hv1'
    | @force s1 s2 hs =>
      -- Force frame: case split on value being forced
      have hv1' := hvek 1 (by omega)
      cases v1 with
      | VDelay body1 env1' =>
        cases v2 with
        | VDelay body2 env2' =>
          -- Depth-dropping case: step to compute s env body
          -- Use outer IH at depth j' for the FULL computation
          show BoundedTriple _ _ (steps m (.compute s1 env1' body1)) (steps m (.compute s2 env2' body2))
          -- Get inner agreement at all depths ≤ j' from hvek
          have hinner : ∀ n, n ≤ j' →
            (steps n (.compute [] env1' body1) = .error ↔ steps n (.compute [] env2' body2) = .error) ∧
            (∀ w1, steps n (.compute [] env1' body1) = .halt w1 → ∃ w2, steps n (.compute [] env2' body2) = .halt w2 ∧ ValueEq j' w1 w2) ∧
            (∀ w2, steps n (.compute [] env2' body2) = .halt w2 → ∃ w1, steps n (.compute [] env1' body1) = .halt w1 ∧ ValueEq j' w1 w2) := by
            intro n hn
            exact hvek (j' + 1) (Nat.le_refl _) n hn
          -- Multi-depth inner agreement: for any d, hvek (d+1) gives ValueEq d on inner results
          have hinner_d : ∀ d n, d < j' + 1 → n ≤ d →
            (steps n (.compute [] env1' body1) = .error ↔ steps n (.compute [] env2' body2) = .error) ∧
            (∀ w1, steps n (.compute [] env1' body1) = .halt w1 → ∃ w2, steps n (.compute [] env2' body2) = .halt w2 ∧ ValueEq d w1 w2) ∧
            (∀ w2, steps n (.compute [] env2' body2) = .halt w2 → ∃ w1, steps n (.compute [] env1' body1) = .halt w1 ∧ ValueEq d w1 w2) := by
            intro d n hd hn
            exact hvek (d + 1) (by omega) n hn
          -- Use ihj at j' for the stacked (non-empty) computation
          -- The computation compute s env body = liftState s (compute [] env body)
          -- We prove BoundedTriple (j'+1) by proving error/halt agreement
          refine ⟨⟨fun herr => ?_, fun herr => ?_⟩, fun w1 hw1 => ?_, fun w2 hw2 => ?_⟩
          · -- Error forward
            -- steps m (compute s1 env1' body1) = error
            -- = steps m (liftState s1 (compute [] env1' body1)) = error
            have herr' : steps m (liftState s1 (.compute [] env1' body1)) = .error := by
              simp [liftState]; exact herr
            obtain ⟨K, hK_le, _, _, hcase⟩ := liftedErrorValueBeh s1 (.compute [] env1' body1) m herr'
            rcases hcase with hs1_err | ⟨ve1, _, _, hs1_halt, hret_err⟩
            · -- Inner errored at K
              have h2_err := (hinner K (by omega)).1.mp hs1_err
              exact liftState_error_of_error s2 (.compute [] env2' body2) ⟨K, h2_err⟩ |>.elim fun K2 hK2 => by
                simp [liftState] at hK2; exact ⟨K2, hK2⟩
            · -- Inner halted at K, ret errored
              obtain ⟨ve2, hve2_halt, hve⟩ := (hinner K (by omega)).2.1 ve1 (by
                obtain ⟨Ke, hKe⟩ := hs1_halt
                exact halt_value_unique_beh hK_le (by
                  cases (extractLiftedValue s1 (.compute [] env1' body1) K (by
                    obtain ⟨K', hK'_le, _, _, hcase'⟩ := liftedErrorValueBeh s1 (.compute [] env1' body1) m herr'
                    sorry) sorry).choose_spec with | inl h => exact h | inr h => exact (by rw [h]; rfl)) hKe ▸ hKe)
              sorry
          · sorry
          · sorry
          · sorry
        | _ => simp [ValueEq] at hv1'
      | VBuiltin b1 args1 ea1 =>
        cases v2 with
        | VBuiltin b2 args2 ea2 =>
          have hvj := hvek (j' + 1) (Nat.le_refl _); unfold ValueEq at hvj
          obtain ⟨hb, hargs, hea, hnone_iff, hsome_val⟩ := hvj; subst hb; subst hea
          show BoundedTriple _ _ (steps m (step (.ret (.force :: s1) (.VBuiltin b1 args1 ea1))))
                                 (steps m (step (.ret (.force :: s2) (.VBuiltin b1 args2 ea1))))
          simp only [step]
          cases hhead : ea1.head with
          | argQ =>
            simp only [hhead]
            cases htail : ea1.tail with
            | some rest =>
              simp only [htail]
              have hvek' : ∀ k, k ≤ j' + 1 → ValueEq k (.VBuiltin b1 args1 rest) (.VBuiltin b1 args2 rest) := by
                intro k hk; cases k with
                | zero => simp [ValueEq]
                | succ k' =>
                  unfold ValueEq
                  have hargs_k' := Moist.Verified.Congruence.listValueEq_mono k' j' (by omega) _ _ hargs
                  have ⟨hnone_k, hsome_k⟩ := evalBuiltin_cong_at k' b1 (by
                    exact Moist.Verified.Congruence.listValueEq_mono (k' + 1) j' (by omega) _ _ hargs)
                  exact ⟨rfl, hargs_k', rfl, hnone_k, hsome_k⟩
              exact (ihm m (by omega) (by omega)).2 _ _ _ _ hs hvek'
            | none =>
              simp only [htail]
              cases hev1 : evalBuiltin b1 args1 with
              | none => simp only [hev1, hnone_iff.mp hev1]; exact err_bt m
              | some r1 =>
                cases hev2 : evalBuiltin b1 args2 with
                | none => exact absurd (hnone_iff.mpr hev2) (by simp [hev1])
                | some r2 =>
                  simp only [hev1, hev2]
                  have hvr : ∀ k, k ≤ j' + 1 → ValueEq k r1 r2 := by
                    intro k hk; cases k with
                    | zero => simp [ValueEq]
                    | succ k' => exact Moist.Verified.Congruence.valueEq_mono (k' + 1) j' (by omega) _ _ (hsome_val r1 r2 hev1 hev2)
                  exact (ihm m (by omega) (by omega)).2 _ _ _ _ hs hvr
          | argV => simp only [hhead]; exact err_bt m
        | _ => simp [ValueEq] at hv1'
      | VCon _ => cases v2 with | VCon _ => exact err_bt m | _ => simp [ValueEq] at hv1'
      | VLam _ _ => cases v2 with | VLam _ _ => exact err_bt m | _ => simp [ValueEq] at hv1'
      | VConstr _ _ => cases v2 with | VConstr _ _ => exact err_bt m | _ => simp [ValueEq] at hv1'
    | @funVGeneral v_fun1 v_fun2 s1 s2 hv_fun hs =>
      -- funV with general values. Case split on function type.
      have hv_fun1 := hv_fun 1 (by omega)
      cases v_fun1 with
      | VLam body1 env1' =>
        cases v_fun2 with
        | VLam body2 env2' =>
          -- step: compute s (env.extend arg) body - depth-dropping case
          show BoundedTriple _ _ (steps m (.compute s1 (env1'.extend v1) body1))
                                 (steps m (.compute s2 (env2'.extend v2) body2))
          -- Use outer IH at depth j' via liftState decomposition
          have hinner : ∀ n, n ≤ j' →
            (steps n (.compute [] (env1'.extend v1) body1) = .error ↔ steps n (.compute [] (env2'.extend v2) body2) = .error) ∧
            (∀ w1, steps n (.compute [] (env1'.extend v1) body1) = .halt w1 → ∃ w2, steps n (.compute [] (env2'.extend v2) body2) = .halt w2 ∧ ValueEq j' w1 w2) ∧
            (∀ w2, steps n (.compute [] (env2'.extend v2) body2) = .halt w2 → ∃ w1, steps n (.compute [] (env1'.extend v1) body1) = .halt w1 ∧ ValueEq j' w1 w2) := by
            intro n hn
            have hvlam := hv_fun (j' + 1) (Nat.le_refl _)
            unfold ValueEq at hvlam
            exact hvlam v1 v2 (hvek j' (by omega)) n hn
          sorry -- depth-dropping VLam application in funVGeneral
        | _ => simp [ValueEq] at hv_fun1
      | VBuiltin b1 args1 ea1 =>
        cases v_fun2 with
        | VBuiltin b2 args2 ea2 =>
          have hvj := hv_fun (j' + 1) (Nat.le_refl _); unfold ValueEq at hvj
          obtain ⟨hb, hargs, hea, hnone_iff, hsome_val⟩ := hvj; subst hb; subst hea
          -- Same as funVBuiltin case
          show BoundedTriple _ _ (steps m (step (.ret (.funV (.VBuiltin b1 args1 ea1) :: s1) v1)))
                                 (steps m (step (.ret (.funV (.VBuiltin b1 args2 ea1) :: s2) v2)))
          simp only [step]
          cases hhead : ea1.head with
          | argV =>
            simp only [hhead]
            cases htail : ea1.tail with
            | some rest =>
              simp only [htail]
              have hvek' : ∀ k, k ≤ j' + 1 → ValueEq k (.VBuiltin b1 (v1 :: args1) rest) (.VBuiltin b1 (v2 :: args2) rest) := by
                intro k hk; cases k with
                | zero => simp [ValueEq]
                | succ k' =>
                  unfold ValueEq
                  exact ⟨rfl,
                    by simp [ListValueEq]; exact ⟨Moist.Verified.Congruence.valueEq_mono k' (j' + 1) (by omega) _ _ (hvek (j' + 1) (Nat.le_refl _)), hargs.mono_aux2 k'⟩,
                    rfl,
                    (evalBuiltin_cong_at k' b1 (by simp [ListValueEq]; exact ⟨hvek (k' + 1) (by omega), Moist.Verified.Congruence.listValueEq_mono (k' + 1) j' (by omega) _ _ hargs⟩)).1,
                    (evalBuiltin_cong_at k' b1 (by simp [ListValueEq]; exact ⟨hvek (k' + 1) (by omega), Moist.Verified.Congruence.listValueEq_mono (k' + 1) j' (by omega) _ _ hargs⟩)).2⟩
                  where
                    mono_aux2 {as1 as2 : List CekValue} (h : ListValueEq j' as1 as2) (k' : Nat) : ListValueEq k' as1 as2 :=
                      Moist.Verified.Congruence.listValueEq_mono k' j' (by omega) _ _ h
              exact (ihm m (by omega) (by omega)).2 _ _ _ _ hs hvek'
            | none =>
              simp only [htail]
              have hargsfull : ListValueEq (j' + 1) (v1 :: args1) (v2 :: args2) := by
                simp [ListValueEq]
                exact ⟨hvek (j' + 1) (Nat.le_refl _), Moist.Verified.Congruence.listValueEq_mono (j' + 1) j' (by omega) _ _ hargs⟩
              have ⟨hnone_iff2, hsome_val2⟩ := evalBuiltin_cong_at j' b1 hargsfull
              cases hev1 : evalBuiltin b1 (v1 :: args1) with
              | none =>
                simp only [hev1, hnone_iff2.mp hev1]; exact err_bt m
              | some r1 =>
                cases hev2 : evalBuiltin b1 (v2 :: args2) with
                | none => exact absurd (hnone_iff2.mpr hev2) (by simp [hev1])
                | some r2 =>
                  simp only [hev1, hev2]
                  have hvr : ∀ k, k ≤ j' + 1 → ValueEq k r1 r2 := by
                    intro k hk; cases k with
                    | zero => simp [ValueEq]
                    | succ k' => exact Moist.Verified.Congruence.valueEq_mono (k' + 1) j' (by omega) _ _ (hsome_val2 r1 r2 hev1 hev2)
                  exact (ihm m (by omega) (by omega)).2 _ _ _ _ hs hvr
          | argQ => simp only [hhead]; exact err_bt m
        | _ => simp [ValueEq] at hv_fun1
      | VCon _ => cases v_fun2 with | VCon _ => exact err_bt m | _ => simp [ValueEq] at hv_fun1
      | VDelay _ _ => cases v_fun2 with | VDelay _ _ => exact err_bt m | _ => simp [ValueEq] at hv_fun1
      | VConstr _ _ => cases v_fun2 with | VConstr _ _ => exact err_bt m | _ => simp [ValueEq] at hv_fun1
    | @applyArg va1 va2 s1 s2 hva hs =>
      -- applyArg: v1 is the function result, hva is stored argument
      have hv1' := hvek 1 (by omega)
      cases v1 with
      | VLam body1 env1' =>
        cases v2 with
        | VLam body2 env2' =>
          -- step: compute s (env.extend va) body - depth-dropping case
          show BoundedTriple _ _ (steps m (.compute s1 (env1'.extend va1) body1))
                                 (steps m (.compute s2 (env2'.extend va2) body2))
          have hinner : ∀ n, n ≤ j' →
            (steps n (.compute [] (env1'.extend va1) body1) = .error ↔ steps n (.compute [] (env2'.extend va2) body2) = .error) ∧
            (∀ w1, steps n (.compute [] (env1'.extend va1) body1) = .halt w1 → ∃ w2, steps n (.compute [] (env2'.extend va2) body2) = .halt w2 ∧ ValueEq j' w1 w2) ∧
            (∀ w2, steps n (.compute [] (env2'.extend va2) body2) = .halt w2 → ∃ w1, steps n (.compute [] (env1'.extend va1) body1) = .halt w1 ∧ ValueEq j' w1 w2) := by
            intro n hn
            have hvlam := hvek (j' + 1) (Nat.le_refl _)
            unfold ValueEq at hvlam
            exact hvlam va1 va2 (hva j' (by omega)) n hn
          sorry -- depth-dropping VLam application in applyArg
        | _ => simp [ValueEq] at hv1'
      | VBuiltin b1 args1 ea1 =>
        cases v2 with
        | VBuiltin b2 args2 ea2 =>
          have hvj := hvek (j' + 1) (Nat.le_refl _); unfold ValueEq at hvj
          obtain ⟨hb, hargs, hea, hnone_iff, hsome_val⟩ := hvj; subst hb; subst hea
          show BoundedTriple _ _ (steps m (step (.ret (.applyArg va1 :: s1) (.VBuiltin b1 args1 ea1))))
                                 (steps m (step (.ret (.applyArg va2 :: s2) (.VBuiltin b1 args2 ea1))))
          simp only [step]
          cases hhead : ea1.head with
          | argV =>
            simp only [hhead]
            cases htail : ea1.tail with
            | some rest =>
              simp only [htail]
              have hvek' : ∀ k, k ≤ j' + 1 → ValueEq k (.VBuiltin b1 (va1 :: args1) rest) (.VBuiltin b1 (va2 :: args2) rest) := by
                intro k hk; cases k with
                | zero => simp [ValueEq]
                | succ k' =>
                  unfold ValueEq
                  exact ⟨rfl,
                    by simp [ListValueEq]; exact ⟨hva k' (by omega), Moist.Verified.Congruence.listValueEq_mono k' j' (by omega) _ _ hargs⟩,
                    rfl,
                    (evalBuiltin_cong_at k' b1 (by simp [ListValueEq]; exact ⟨hva (k' + 1) (by omega), Moist.Verified.Congruence.listValueEq_mono (k' + 1) j' (by omega) _ _ hargs⟩)).1,
                    (evalBuiltin_cong_at k' b1 (by simp [ListValueEq]; exact ⟨hva (k' + 1) (by omega), Moist.Verified.Congruence.listValueEq_mono (k' + 1) j' (by omega) _ _ hargs⟩)).2⟩
              exact (ihm m (by omega) (by omega)).2 _ _ _ _ hs hvek'
            | none =>
              simp only [htail]
              have hargsfull : ListValueEq (j' + 1) (va1 :: args1) (va2 :: args2) := by
                simp [ListValueEq]
                exact ⟨hva (j' + 1) (Nat.le_refl _), Moist.Verified.Congruence.listValueEq_mono (j' + 1) j' (by omega) _ _ hargs⟩
              have ⟨hnone_iff2, hsome_val2⟩ := evalBuiltin_cong_at j' b1 hargsfull
              cases hev1 : evalBuiltin b1 (va1 :: args1) with
              | none =>
                simp only [hev1, hnone_iff2.mp hev1]; exact err_bt m
              | some r1 =>
                cases hev2 : evalBuiltin b1 (va2 :: args2) with
                | none => exact absurd (hnone_iff2.mpr hev2) (by simp [hev1])
                | some r2 =>
                  simp only [hev1, hev2]
                  have hvr : ∀ k, k ≤ j' + 1 → ValueEq k r1 r2 := by
                    intro k hk; cases k with
                    | zero => simp [ValueEq]
                    | succ k' => exact Moist.Verified.Congruence.valueEq_mono (k' + 1) j' (by omega) _ _ (hsome_val2 r1 r2 hev1 hev2)
                  exact (ihm m (by omega) (by omega)).2 _ _ _ _ hs hvr
          | argQ => simp only [hhead]; exact err_bt m
        | _ => simp [ValueEq] at hv1'
      | VCon _ => cases v2 with | VCon _ => exact err_bt m | _ => simp [ValueEq] at hv1'
      | VDelay _ _ => cases v2 with | VDelay _ _ => exact err_bt m | _ => simp [ValueEq] at hv1'
      | VConstr _ _ => cases v2 with | VConstr _ _ => exact err_bt m | _ => simp [ValueEq] at hv1'
    /-
      | VDelay body1 env1' =>
        cases v2 with
        | VDelay body2 env2' =>
          -- step: compute s1 env1' body1 vs compute s2 env2' body2
          -- = liftState s1 (compute [] env1' body1) vs liftState s2 (compute [] env2' body2)
          -- ValueEq (j'+1) VDelay gives bounded triple at empty stacks.
          -- Use ihm for ret part after inner computation halts.
          sorry -- VDelay force: uses bounded_lift_triple (which has a fundamental step-sync issue)
        | VCon _ => simp [ValueEq] at hv1
        | VLam _ _ => simp [ValueEq] at hv1
        | VConstr _ _ => simp [ValueEq] at hv1
        | VBuiltin _ _ _ => simp [ValueEq] at hv1
      | VBuiltin b1 args1 ea1 =>
        cases v2 with
        | VBuiltin b2 args2 ea2 =>
          have hvj := hvek (j' + 1) (Nat.le_refl _); unfold ValueEq at hvj
          obtain ⟨hb, hargs, hea, hnone_iff, hsome_val⟩ := hvj; subst hb; subst hea
          show BoundedTriple _ _ (steps m (step (.ret (.force :: _) (.VBuiltin b1 args1 ea1))))
                                 (steps m (step (.ret (.force :: _) (.VBuiltin b1 args2 ea1))))
          simp only [step]
          cases hhead : ea1.head with
          | argQ =>
            simp only [hhead]
            cases htail : ea1.tail with
            | some rest =>
              simp only [htail]
              have hvek' : ∀ k, k ≤ j' + 1 → ValueEq k (.VBuiltin b1 args1 rest) (.VBuiltin b1 args2 rest) := by
                intro k hk; cases k with
                | zero => simp [ValueEq]
                | succ k' =>
                  unfold ValueEq
                  have hargs_k' := Moist.Verified.Congruence.listValueEq_mono k' j' (by omega) _ _ hargs
                  have ⟨hnone_k, hsome_k⟩ := evalBuiltin_cong_at k' b1 (by
                    exact Moist.Verified.Congruence.listValueEq_mono (k' + 1) j' (by omega) _ _ hargs)
                  exact ⟨rfl, hargs_k', rfl, hnone_k, hsome_k⟩
              exact (ihm m (by omega) (by omega)).2 _ _ _ _ hs hvek'
            | none =>
              simp only [htail]
              cases hev1 : evalBuiltin b1 args1 with
              | none => simp only [hev1, hnone_iff.mp hev1]; exact err_bt m
              | some r1 =>
                cases hev2 : evalBuiltin b1 args2 with
                | none => exact absurd (hnone_iff.mpr hev2) (by simp [hev1])
                | some r2 =>
                  simp only [hev1, hev2]
                  have hvr : ∀ k, k ≤ j' + 1 → ValueEq k r1 r2 := by
                    intro k hk
                    cases k with
                    | zero => simp [ValueEq]
                    | succ k' =>
                      exact hsome_val r1 r2 hev1 hev2
                  exact (ihm m (by omega) (by omega)).2 _ _ _ _ hs hvr
          | argV => exact err_bt m
        | VCon _ => simp [ValueEq] at hv1
        | VLam _ _ => simp [ValueEq] at hv1
        | VConstr _ _ => simp [ValueEq] at hv1
        | VDelay _ _ => simp [ValueEq] at hv1
      | VCon _ =>
        cases v2 with
        | VCon _ => exact err_bt m
        | _ => simp [ValueEq] at hv1
      | VLam _ _ =>
        cases v2 with
        | VLam _ _ => exact err_bt m
        | _ => simp [ValueEq] at hv1
      | VConstr _ _ =>
        cases v2 with
        | VConstr _ _ => exact err_bt m
        | _ => simp [ValueEq] at hv1
    | @arg x env1' env2' s1 s2 he hs =>
      have hv1' := hvek 1 (by omega)
      cases v1 with
      | VLam body1 ρ1 =>
        cases v2 with
        | VLam body2 ρ2 => sorry -- VLam arg: needs body/env decomposition from ValueEq
        | _ => simp [ValueEq] at hv1'
      | VBuiltin b1 args1 ea1 =>
        cases v2 with
        | VBuiltin b2 args2 ea2 =>
          have hvj := hvek (j' + 1) (Nat.le_refl _); unfold ValueEq at hvj
          obtain ⟨hb, hargs, hea, _, _⟩ := hvj; subst hb; subst hea
          sorry -- VBuiltin in arg frame: StackRelJ depth mismatch
        | _ => simp [ValueEq] at hv1'
      | VCon _ =>
        cases v2 with
        | VCon _ => sorry -- VCon funV: error after next step
        | _ => simp [ValueEq] at hv1'
      | VDelay _ _ =>
        cases v2 with
        | VDelay _ _ => sorry
        | _ => simp [ValueEq] at hv1'
      | VConstr _ _ =>
        cases v2 with
        | VConstr _ _ => sorry
        | _ => simp [ValueEq] at hv1'
    | @funVLam body ρ1 ρ2 s1 s2 he hs =>
      show BoundedTriple _ _ (steps m (.compute s1 (ρ1.extend v1) body))
                             (steps m (.compute s2 (ρ2.extend v2) body))
      exact (ihm m (by omega) (by omega)).1 _ _ _ _ body hs
        (envRelJ_extend he (hvek (j' + 1) (Nat.le_refl _)))
    | @funVBuiltin b args1 args2 ea s1 s2 hargs hs =>
      show BoundedTriple _ _ (steps m (step (.ret (.funV (.VBuiltin b args1 ea) :: s1) v1)))
                             (steps m (step (.ret (.funV (.VBuiltin b args2 ea) :: s2) v2)))
      simp only [step]
      cases hhead : ea.head with
      | argV =>
        simp only [hhead]
        cases htail : ea.tail with
        | some rest => simp only [htail]; sorry -- VBuiltin funV tail some
        | none => simp only [htail]; sorry -- VBuiltin funV tail none: evalBuiltin
      | argQ => exact err_bt m
    | @constrField tag done1 done2 todo env1' env2' s1 s2 hdone he hs =>
      cases todo with
      | cons m' ms =>
        show BoundedTriple _ _ (steps m (.compute (.constrField tag (v1 :: done1) ms env1' :: s1) env1' m'))
                               (steps m (.compute (.constrField tag (v2 :: done2) ms env2' :: s2) env2' m'))
        exact (ihm m (by omega) (by omega)).1 _ _ _ _ m'
          (.constrField (fun k hk => by unfold ListValueEq; exact ⟨hvek k hk, hdone k hk⟩) he hs) he
      | nil =>
        show BoundedTriple _ _ (steps m (.ret s1 (.VConstr tag ((v1 :: done1).reverse))))
                               (steps m (.ret s2 (.VConstr tag ((v2 :: done2).reverse))))
        sorry -- VConstr ret: needs ListValueEq for reversed list
    | @caseScrutinee alts env1' env2' s1 s2 he hs =>
      sorry -- Case dispatch
    | @applyArg va1 va2 s1 s2 hva hs =>
      have hv1' := hvek 1 (by omega)
      cases v1 with
      | VLam body1 ρ1 =>
        cases v2 with
        | VLam body2 ρ2 => sorry -- VLam applyArg: needs body/env decomposition
        | _ => simp [ValueEq] at hv1'
      | VBuiltin b1 args1 ea1 =>
        cases v2 with
        | VBuiltin b2 args2 ea2 => sorry -- VBuiltin applyArg
        | _ => simp [ValueEq] at hv1'
      | VCon _ =>
        cases v2 with
        | VCon _ => exact err_bt m
        | _ => simp [ValueEq] at hv1'
      | VDelay _ _ =>
        cases v2 with
        | VDelay _ _ => exact err_bt m
        | _ => simp [ValueEq] at hv1'
      | VConstr _ _ =>
        cases v2 with
        | VConstr _ _ => exact err_bt m
        | _ => simp [ValueEq] at hv1' -/

/-- Generalized bounded-step agreement: same body in EnvRelJ j envs with
    StackRelJ j stacks. Extracted from the combined theorem. -/
private theorem bounded_bisim_gen :
    ∀ j n, n ≤ j →
      ∀ (stk1 stk2 : Stack) (env1 env2 : CekEnv) (body : Moist.Plutus.Term.Term),
        StackRelJ j stk1 stk2 → EnvRelJ j env1 env2 →
          (steps n (.compute stk1 env1 body) = .error ↔
           steps n (.compute stk2 env2 body) = .error) ∧
          (∀ v1, steps n (.compute stk1 env1 body) = .halt v1 →
            ∃ v2, steps n (.compute stk2 env2 body) = .halt v2 ∧ ValueEq j v1 v2) ∧
          (∀ v2, steps n (.compute stk2 env2 body) = .halt v2 →
            ∃ v1, steps n (.compute stk1 env1 body) = .halt v1 ∧ ValueEq j v1 v2) := by
  intro j n hn stk1 stk2 env1 env2 body hstk henv
  exact (bounded_bisim_combined j n hn).1 stk1 stk2 env1 env2 body hstk henv

/-- Bounded-step agreement for ret states. Extracted from the combined theorem. -/
private theorem bounded_bisim_ret :
    ∀ j n, n ≤ j →
      ∀ (stk1 stk2 : Stack) (v1 v2 : CekValue),
        StackRelJ j stk1 stk2 → (∀ k, k ≤ j → ValueEq k v1 v2) →
          (steps n (.ret stk1 v1) = .error ↔
           steps n (.ret stk2 v2) = .error) ∧
          (∀ w1, steps n (.ret stk1 v1) = .halt w1 →
            ∃ w2, steps n (.ret stk2 v2) = .halt w2 ∧ ValueEq j w1 w2) ∧
          (∀ w2, steps n (.ret stk2 v2) = .halt w2 →
            ∃ w1, steps n (.ret stk1 v1) = .halt w1 ∧ ValueEq j w1 w2) := by
  intro j n hn stk1 stk2 v1 v2 hstk hvek
  exact (bounded_bisim_combined j n hn).2 stk1 stk2 v1 v2 hstk hvek

private theorem bounded_bisim_aux :
    ∀ j, (∀ (body : Moist.Plutus.Term.Term) (env1 env2 : CekEnv), EnvRelJ j env1 env2 →
      ∀ n, n ≤ j →
        (steps n (.compute [] env1 body) = .error ↔
         steps n (.compute [] env2 body) = .error) ∧
        (∀ v1, steps n (.compute [] env1 body) = .halt v1 →
          ∃ v2, steps n (.compute [] env2 body) = .halt v2 ∧ ValueEq j v1 v2) ∧
        (∀ v2, steps n (.compute [] env2 body) = .halt v2 →
          ∃ v1, steps n (.compute [] env1 body) = .halt v1 ∧ ValueEq j v1 v2)) := by
  intro j body env1 env2 henv n hn
  exact bounded_bisim_gen j n hn [] [] env1 env2 body .nil henv

/-- EnvBehEq envs give ValEqInf for same-body VLam closures. -/
theorem envBehEq_vlam_valEqInf (body : Moist.Plutus.Term.Term) (env1 env2 : CekEnv)
    (he : EnvBehEq env1 env2) : ValEqInf (.VLam body env1) (.VLam body env2) := by
  intro j; cases j with
  | zero => simp [ValueEq]
  | succ k =>
    unfold ValueEq; intro arg1 arg2 hargs n hn
    -- Extended envs: EnvRelJ k from EnvBehEq prefix + ValueEq k args
    have he_ext := envRelJ_extend (envBehEq_to_envRelJ k he) hargs
    exact bounded_bisim_aux k body _ _ he_ext n hn

/-- Same as above for VDelay. -/
theorem envBehEq_vdelay_valEqInf (body : Moist.Plutus.Term.Term) (env1 env2 : CekEnv)
    (he : EnvBehEq env1 env2) : ValEqInf (.VDelay body env1) (.VDelay body env2) := by
  intro j; cases j with
  | zero => simp [ValueEq]
  | succ k =>
    unfold ValueEq; intro n hn
    exact bounded_bisim_aux k body env1 env2 (envBehEq_to_envRelJ k he) n hn

/-! ### Behavioral state relation and step-count induction for D, E -/

/-- State relation for behavioral env equivalence. Same body at compute states,
    ValEqInf at ret states, StackBehEq everywhere. -/
inductive StateBehRel : State → State → Prop
  | compute (body : Moist.Plutus.Term.Term) {stk1 stk2 : Stack} {env1 env2 : CekEnv}
      (hstk : StackBehEq stk1 stk2) (he : EnvBehEq env1 env2) :
      StateBehRel (.compute stk1 env1 body) (.compute stk2 env2 body)
  | ret {stk1 stk2 : Stack} {v1 v2 : CekValue}
      (hstk : StackBehEq stk1 stk2) (hv : ValEqInf v1 v2) :
      StateBehRel (.ret stk1 v1) (.ret stk2 v2)
  | error : StateBehRel .error .error
  | halt {v1 v2 : CekValue} (hv : ValEqInf v1 v2) :
      StateBehRel (.halt v1) (.halt v2)

/-- EnvBehEq lookup produces matching results with ValEqInf. -/
private theorem envBehEq_lookup_match {env1 env2 : CekEnv} (he : EnvBehEq env1 env2) (n : Nat) :
    match env1.lookup n, env2.lookup n with
    | some v1, some v2 => ValEqInf v1 v2
    | none, none => True
    | _, _ => False := by
  obtain ⟨hdom, hval⟩ := he
  cases h1 : env1.lookup n with
  | none =>
    have := (hdom n).mp h1
    rw [this]; trivial
  | some v1 =>
    cases h2 : env2.lookup n with
    | none =>
      have := (hdom n).mpr h2
      rw [h1] at this; simp at this
    | some v2 =>
      exact fun j => hval n v1 v2 h1 h2 j

/-- VConstr tag agreement from ValEqInf. -/
private theorem valEqInf_vconstr_tag {tag1 tag2 : Nat} {fs1 fs2 : List CekValue}
    (h : ValEqInf (.VConstr tag1 fs1) (.VConstr tag2 fs2)) : tag1 = tag2 := by
  have h1 := h 1; unfold ValueEq at h1; exact h1.1

/-- VConstr fields agreement from ValEqInf. -/
private theorem valEqInf_vconstr_fields {tag1 tag2 : Nat} {fs1 fs2 : List CekValue}
    (h : ValEqInf (.VConstr tag1 fs1) (.VConstr tag2 fs2)) : ListValueEqInf fs1 fs2 := by
  intro j; have hj := h (j + 1); unfold ValueEq at hj; exact hj.2

/-- VCon constant agreement from ValEqInf. -/
private theorem valEqInf_vcon_eq {c1 c2 : Const}
    (h : ValEqInf (.VCon c1) (.VCon c2)) : c1 = c2 := by
  have h1 := h 1; unfold ValueEq at h1; exact h1

/-- VBuiltin fields from ValEqInf. -/
private theorem valEqInf_vbuiltin {b1 b2 : BuiltinFun} {a1 a2 : List CekValue} {ea1 ea2 : ExpectedArgs}
    (h : ValEqInf (.VBuiltin b1 a1 ea1) (.VBuiltin b2 a2 ea2)) :
    b1 = b2 ∧ ListValueEqInf a1 a2 ∧ ea1 = ea2 := by
  have h1 := h 1; unfold ValueEq at h1
  refine ⟨h1.1, fun j => ?_, h1.2.2.1⟩
  have hj := h (j + 1); unfold ValueEq at hj
  exact hj.2.1

/-- ValEqInf for VDelay gives same-or-related bodies. -/
private theorem valEqInf_vdelay_info {b1 b2 : Moist.Plutus.Term.Term} {e1 e2 : CekEnv}
    (h : ValEqInf (.VDelay b1 e1) (.VDelay b2 e2)) :
    ValEqInf (.VDelay b1 e1) (.VDelay b2 e2) := h

/-- Helper: transfer error through a lifted computation given BehBundle for inner
    and IH for stack processing. -/
private theorem lifted_error_transfer
    (ih : ∀ m, m < M + 1 → ∀ s1 s2, StateBehRel s1 s2 → steps m s1 = .error → Reaches s2 .error)
    {base1 base2 : Stack} (hbase : StackBehEq base1 base2)
    {s1 s2 : State} (hbeh : BehBundle s1 s2)
    (herr : steps M (liftState base1 s1) = .error) :
    Reaches (liftState base2 s2) .error := by
  obtain ⟨K, hK_le, _, _, hcase⟩ := liftedErrorValueBeh base1 s1 M herr
  rcases hcase with hs1_err | ⟨ve1, _, _, hs1_halt, hret_err⟩
  · exact liftState_error_of_error base2 s2 (hbeh.1.mp ⟨K, hs1_err⟩)
  · obtain ⟨ve2, hs2_halt⟩ := hbeh.2.1.mp ⟨ve1, hs1_halt⟩
    have hve : ValEqInf ve1 ve2 := fun j => hbeh.2.2 j ve1 ve2 hs1_halt hs2_halt
    exact liftState_compose base2 s2 .error ve2 hs2_halt
      (ih (M - K) (by omega) _ _ (.ret hbase hve) hret_err)

/-- Helper: get ValEqInf for evalBuiltin results from ListValueEqInf args -/
private theorem evalBuiltin_valEqInf (b : BuiltinFun) {a1 a2 : List CekValue}
    (ha : ListValueEqInf a1 a2) :
    (evalBuiltin b a1 = none ↔ evalBuiltin b a2 = none) ∧
    ∀ r1 r2, evalBuiltin b a1 = some r1 → evalBuiltin b a2 = some r2 → ValEqInf r1 r2 := by
  constructor
  · exact (evalBuiltin_cong_full 0 b ha).1
  · intro r1 r2 h1 h2 j
    exact (evalBuiltin_cong_full j b ha).2 r1 r2 h1 h2

/-- Core error-transfer by strong induction on step count. Handles both
    compute (same body) and ret (ValEqInf) states. -/
private theorem stateBehRel_error_transfer :
    ∀ N s1 s2, StateBehRel s1 s2 → steps N s1 = .error → Reaches s2 .error := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro s1 s2 hrel herr
  cases N with
  | zero =>
    dsimp [steps] at herr; subst herr
    cases hrel with
    | error => exact ⟨0, rfl⟩
  | succ M =>
    simp only [steps] at herr
    cases hrel with
    | error => exact ⟨0, rfl⟩
    | halt => simp [step, steps_halt] at herr
    | compute body hstk he =>
      -- Each term case steps to a new StateBehRel state; apply IH at M < N
      cases body with
      | Error => exact ⟨1, by simp [steps, step]⟩
      | Var n =>
        simp only [step] at herr
        have ⟨hdom, hval⟩ := he
        generalize h1 : CekEnv.lookup _ n = r1 at herr
        cases r1 with
        | none =>
          have h2 := (hdom n).mp h1
          exact ⟨1, by show steps 1 (.compute _ _ (.Var n)) = .error; simp [steps, step, h2]⟩
        | some v1 =>
          cases h2 : CekEnv.lookup _ n with
          | none => exact absurd ((hdom n).mpr h2) (by rw [h1]; simp)
          | some v2 =>
            have hve : ValEqInf v1 v2 := fun j => hval n v1 v2 h1 h2 j
            have hreach := ih M (by omega) _ _ (.ret hstk hve) herr
            obtain ⟨K, hK⟩ := hreach
            exact ⟨K + 1, by simp [steps, step, h2]; exact hK⟩
      | Apply f x =>
        simp only [step] at herr
        have hstk' := StackBehEq.cons (.arg x he) hstk
        have hreach := ih M (by omega) _ _ (.compute f hstk' he) herr
        obtain ⟨K, hK⟩ := hreach
        exact ⟨K + 1, by simp [steps, step]; exact hK⟩
      | Force e =>
        simp only [step] at herr
        have hstk' := StackBehEq.cons .force hstk
        have hreach := ih M (by omega) _ _ (.compute e hstk' he) herr
        obtain ⟨K, hK⟩ := hreach
        exact ⟨K + 1, by simp [steps, step]; exact hK⟩
      | Case scrut alts =>
        simp only [step] at herr
        have hstk' := StackBehEq.cons (.caseScrutinee alts he) hstk
        have hreach := ih M (by omega) _ _ (.compute scrut hstk' he) herr
        obtain ⟨K, hK⟩ := hreach
        exact ⟨K + 1, by simp [steps, step]; exact hK⟩
      | Constr tag args =>
        cases args with
        | nil =>
          simp only [step] at herr
          have hve : ValEqInf (.VConstr tag []) (.VConstr tag []) := fun j => valueEq_refl j _
          have hreach := ih M (by omega) _ _ (.ret hstk hve) herr
          obtain ⟨K, hK⟩ := hreach
          exact ⟨K + 1, by simp [steps, step]; exact hK⟩
        | cons m ms =>
          simp only [step] at herr
          have hstk' := StackBehEq.cons (.constrField tag ms (listValueEqInf_refl []) he) hstk
          have hreach := ih M (by omega) _ _ (.compute m hstk' he) herr
          obtain ⟨K, hK⟩ := hreach
          exact ⟨K + 1, by simp [steps, step]; exact hK⟩
      | Constant p =>
        obtain ⟨c, ty⟩ := p; simp only [step] at herr
        have hve : ValEqInf (.VCon c) (.VCon c) := fun j => valueEq_refl j _
        have hreach := ih M (by omega) _ _ (.ret hstk hve) herr
        obtain ⟨K, hK⟩ := hreach; exact ⟨K + 1, by simp [steps, step]; exact hK⟩
      | Builtin b =>
        simp only [step] at herr
        have hve : ValEqInf (.VBuiltin b [] (expectedArgs b)) (.VBuiltin b [] (expectedArgs b)) :=
          fun j => valueEq_refl j _
        have hreach := ih M (by omega) _ _ (.ret hstk hve) herr
        obtain ⟨K, hK⟩ := hreach; exact ⟨K + 1, by simp [steps, step]; exact hK⟩
      | Lam _ body =>
        simp only [step] at herr
        have hve := envBehEq_vlam_valEqInf body _ _ he
        have hreach := ih M (by omega) _ _ (.ret hstk hve) herr
        obtain ⟨K, hK⟩ := hreach; exact ⟨K + 1, by simp [steps, step]; exact hK⟩
      | Delay body =>
        simp only [step] at herr
        have hve := envBehEq_vdelay_valEqInf body _ _ he
        have hreach := ih M (by omega) _ _ (.ret hstk hve) herr
        obtain ⟨K, hK⟩ := hreach; exact ⟨K + 1, by simp [steps, step]; exact hK⟩
    | ret hstk hv =>
      cases hstk with
      | nil => simp [step, steps_halt] at herr
      | cons hf hrest =>
        cases hf with
        | arg t he' =>
          simp only [step] at herr
          have hreach := ih M (by omega) _ _ (.compute t (.cons (.funV hv) hrest) he') herr
          obtain ⟨K, hK⟩ := hreach; exact ⟨K + 1, by simp [steps, step]; exact hK⟩
        | force =>
          -- Force: case split on the value being forced
          rename_i v1 v2 rest1 rest2
          cases v1 with
          | VDelay body1 env1 =>
            cases v2 with
            | VDelay body2 env2 =>
              -- step (.ret (.force :: rest1) (.VDelay body1 env1)) = compute rest1 env1 body1
              -- = liftState rest1 (compute [] env1 body1)
              simp only [step] at herr
              have hbeh := valEqInf_vdelay_force_behBundle body1 body2 env1 env2 hv
              -- herr : steps M (.compute rest1 env1 body1) = .error
              -- = steps M (liftState rest1 (.compute [] env1 body1)) = .error
              have herr' : steps M (liftState rest1 (.compute [] env1 body1)) = .error := by
                simp [liftState]; exact herr
              have hreach := lifted_error_transfer ih hrest hbeh herr'
              -- hreach : Reaches (liftState rest2 (.compute [] env2 body2)) .error
              -- = Reaches (.compute rest2 env2 body2) .error
              obtain ⟨K, hK⟩ := hreach
              exact ⟨K + 1, by simp [steps, step, liftState] at hK ⊢; exact hK⟩
            | VCon _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VLam _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VConstr _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VBuiltin _ _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
          | VBuiltin b1 args1 ea1 =>
            cases v2 with
            | VBuiltin b2 args2 ea2 =>
              have ⟨hb, hargs, hea⟩ := valEqInf_vbuiltin hv
              subst hb; subst hea
              simp only [step] at herr ⊢
              cases hhead : ea1.head with
              | argQ =>
                simp only [hhead] at herr ⊢
                cases htail : ea1.tail with
                | some rest =>
                  simp only [htail] at herr ⊢
                  have hve := builtin_cons_valueEqInf (b := b1) (ea := rest) hargs
                  have hreach := ih M (by omega) _ _ (.ret hrest hve) herr
                  obtain ⟨K, hK⟩ := hreach
                  exact ⟨K + 1, by simp [steps, step, hhead, htail]; exact hK⟩
                | none =>
                  simp only [htail] at herr ⊢
                  have ⟨hnone_iff, hsome_val⟩ := evalBuiltin_valEqInf b1 hargs
                  cases hev1 : evalBuiltin b1 args1 with
                  | none =>
                    simp only [hev1] at herr ⊢
                    exact ⟨1, by simp [steps, step, hhead, htail, hnone_iff.mp hev1]⟩
                  | some r1 =>
                    simp only [hev1] at herr ⊢
                    cases hev2 : evalBuiltin b1 args2 with
                    | none =>
                      have := hnone_iff.mpr hev2; rw [hev1] at this; simp at this
                    | some r2 =>
                      have hve := hsome_val r1 r2 hev1 hev2
                      have hreach := ih M (by omega) _ _ (.ret hrest hve) herr
                      obtain ⟨K, hK⟩ := hreach
                      exact ⟨K + 1, by simp [steps, step, hhead, htail, hev2]; exact hK⟩
              | argV =>
                simp only [hhead] at herr
                exact ⟨1, by simp [steps, step, hhead]⟩
            | VCon _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VLam _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VDelay _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VConstr _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
          | VCon _ =>
            cases v2 with
            | VCon _ => simp only [step] at herr; exact ⟨1, by simp [steps, step]⟩
            | VLam _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VDelay _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VConstr _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VBuiltin _ _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
          | VLam _ _ =>
            cases v2 with
            | VLam _ _ => simp only [step] at herr; exact ⟨1, by simp [steps, step]⟩
            | VCon _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VDelay _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VConstr _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VBuiltin _ _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
          | VConstr _ _ =>
            cases v2 with
            | VConstr _ _ => simp only [step] at herr; exact ⟨1, by simp [steps, step]⟩
            | VCon _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VLam _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VDelay _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VBuiltin _ _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
        | funV hv_fun =>
          -- funV: apply function (hv_fun) to argument (hv).
          rename_i v1 v2 rest1 rest2 vf1 vf2
          cases vf1 with
          | VLam body1 env1 =>
            cases vf2 with
            | VLam body2 env2 =>
              simp only [step] at herr
              have hbeh := valEqInf_vlam_apply_behBundle body1 body2 env1 env2 v1 v2 hv_fun hv
              have herr' : steps M (liftState rest1 (.compute [] (env1.extend v1) body1)) = .error := by
                simp [liftState]; exact herr
              have hreach := lifted_error_transfer ih hrest hbeh herr'
              obtain ⟨K, hK⟩ := hreach
              exact ⟨K + 1, by simp [steps, step, liftState] at hK ⊢; exact hK⟩
            | VCon _ => exact absurd (hv_fun 1) (by unfold ValueEq; exact id)
            | VDelay _ _ => exact absurd (hv_fun 1) (by unfold ValueEq; exact id)
            | VConstr _ _ => exact absurd (hv_fun 1) (by unfold ValueEq; exact id)
            | VBuiltin _ _ _ => exact absurd (hv_fun 1) (by unfold ValueEq; exact id)
          | VBuiltin b1 args1 ea1 =>
            cases vf2 with
            | VBuiltin b2 args2 ea2 =>
              have ⟨hb, hargs, hea⟩ := valEqInf_vbuiltin hv_fun
              subst hb; subst hea
              simp only [step] at herr ⊢
              cases hhead : ea1.head with
              | argV =>
                simp only [hhead] at herr ⊢
                cases htail : ea1.tail with
                | some rest =>
                  simp only [htail] at herr ⊢
                  have hve := builtin_cons_valueEqInf (b := b1) (ea := rest)
                    (listValueEqInf_cons hv hargs)
                  have hreach := ih M (by omega) _ _ (.ret hrest hve) herr
                  obtain ⟨K, hK⟩ := hreach
                  exact ⟨K + 1, by simp [steps, step, hhead, htail]; exact hK⟩
                | none =>
                  simp only [htail] at herr ⊢
                  have hargs' := listValueEqInf_cons hv hargs
                  have ⟨hnone_iff, hsome_val⟩ := evalBuiltin_valEqInf b1 hargs'
                  -- The arg values in evalBuiltin are (retval :: builtin_args)
                  generalize harg1def : evalBuiltin b1 (v1 :: args1) = ev1 at herr
                  cases ev1 with
                  | none =>
                    simp only at herr ⊢
                    have hev2 := hnone_iff.mp harg1def
                    exact ⟨1, by simp [steps, step, hhead, htail, hev2]⟩
                  | some r1 =>
                    simp only at herr ⊢
                    cases hev2 : evalBuiltin b1 (v2 :: args2) with
                    | none =>
                      have := hnone_iff.mpr hev2; rw [harg1def] at this; simp at this
                    | some r2 =>
                      have hve := hsome_val r1 r2 harg1def hev2
                      have hreach := ih M (by omega) _ _ (.ret hrest hve) herr
                      obtain ⟨K, hK⟩ := hreach
                      exact ⟨K + 1, by simp [steps, step, hhead, htail, hev2]; exact hK⟩
              | argQ =>
                simp only [hhead] at herr
                exact ⟨1, by simp [steps, step, hhead]⟩
            | VCon _ => exact absurd (hv_fun 1) (by unfold ValueEq; exact id)
            | VDelay _ _ => exact absurd (hv_fun 1) (by unfold ValueEq; exact id)
            | VLam _ _ => exact absurd (hv_fun 1) (by unfold ValueEq; exact id)
            | VConstr _ _ => exact absurd (hv_fun 1) (by unfold ValueEq; exact id)
          | VCon _ =>
            cases vf2 with
            | VCon _ => simp only [step] at herr; exact ⟨1, by simp [steps, step]⟩
            | VLam _ _ => exact absurd (hv_fun 1) (by unfold ValueEq; exact id)
            | VDelay _ _ => exact absurd (hv_fun 1) (by unfold ValueEq; exact id)
            | VConstr _ _ => exact absurd (hv_fun 1) (by unfold ValueEq; exact id)
            | VBuiltin _ _ _ => exact absurd (hv_fun 1) (by unfold ValueEq; exact id)
          | VDelay _ _ =>
            cases vf2 with
            | VDelay _ _ => simp only [step] at herr; exact ⟨1, by simp [steps, step]⟩
            | VCon _ => exact absurd (hv_fun 1) (by unfold ValueEq; exact id)
            | VLam _ _ => exact absurd (hv_fun 1) (by unfold ValueEq; exact id)
            | VConstr _ _ => exact absurd (hv_fun 1) (by unfold ValueEq; exact id)
            | VBuiltin _ _ _ => exact absurd (hv_fun 1) (by unfold ValueEq; exact id)
          | VConstr _ _ =>
            cases vf2 with
            | VConstr _ _ => simp only [step] at herr; exact ⟨1, by simp [steps, step]⟩
            | VCon _ => exact absurd (hv_fun 1) (by unfold ValueEq; exact id)
            | VLam _ _ => exact absurd (hv_fun 1) (by unfold ValueEq; exact id)
            | VDelay _ _ => exact absurd (hv_fun 1) (by unfold ValueEq; exact id)
            | VBuiltin _ _ _ => exact absurd (hv_fun 1) (by unfold ValueEq; exact id)
        | applyArg hv_arg =>
          -- applyArg: v1 is the function, hv_arg is the stored argument
          rename_i v1 v2 rest1 rest2 va1 va2
          cases v1 with
          | VLam body1 env1 =>
            cases v2 with
            | VLam body2 env2 =>
              -- step (.ret (.applyArg va1 :: rest1) (.VLam body1 env1)) = compute rest1 (env1.extend va1) body1
              simp only [step] at herr
              have hbeh := valEqInf_vlam_apply_behBundle body1 body2 env1 env2 va1 va2 hv hv_arg
              have herr' : steps M (liftState rest1 (.compute [] (env1.extend va1) body1)) = .error := by
                simp [liftState]; exact herr
              have hreach := lifted_error_transfer ih hrest hbeh herr'
              obtain ⟨K, hK⟩ := hreach
              exact ⟨K + 1, by simp [steps, step, liftState] at hK ⊢; exact hK⟩
            | VCon _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VDelay _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VConstr _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VBuiltin _ _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
          | VBuiltin b1 args1 ea1 =>
            cases v2 with
            | VBuiltin b2 args2 ea2 =>
              have ⟨hb, hargs, hea⟩ := valEqInf_vbuiltin hv
              subst hb; subst hea
              simp only [step] at herr ⊢
              cases hhead : ea1.head with
              | argV =>
                simp only [hhead] at herr ⊢
                cases htail : ea1.tail with
                | some rest =>
                  simp only [htail] at herr ⊢
                  have hve := builtin_cons_valueEqInf (b := b1) (ea := rest)
                    (listValueEqInf_cons hv_arg hargs)
                  have hreach := ih M (by omega) _ _ (.ret hrest hve) herr
                  obtain ⟨K, hK⟩ := hreach
                  exact ⟨K + 1, by simp [steps, step, hhead, htail]; exact hK⟩
                | none =>
                  simp only [htail] at herr ⊢
                  have hargs' := listValueEqInf_cons hv_arg hargs
                  have ⟨hnone_iff, hsome_val⟩ := evalBuiltin_valEqInf b1 hargs'
                  cases hev1 : evalBuiltin b1 (va1 :: args1) with
                  | none =>
                    simp only [hev1] at herr ⊢
                    exact ⟨1, by simp [steps, step, hhead, htail, hnone_iff.mp hev1]⟩
                  | some r1 =>
                    simp only [hev1] at herr ⊢
                    cases hev2 : evalBuiltin b1 (va2 :: args2) with
                    | none =>
                      have := hnone_iff.mpr hev2; rw [hev1] at this; simp at this
                    | some r2 =>
                      have hve := hsome_val r1 r2 hev1 hev2
                      have hreach := ih M (by omega) _ _ (.ret hrest hve) herr
                      obtain ⟨K, hK⟩ := hreach
                      exact ⟨K + 1, by simp [steps, step, hhead, htail, hev2]; exact hK⟩
              | argQ =>
                simp only [hhead] at herr
                exact ⟨1, by simp [steps, step, hhead]⟩
            | VCon _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VDelay _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VLam _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VConstr _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
          | VCon _ =>
            cases v2 with
            | VCon _ => simp only [step] at herr; exact ⟨1, by simp [steps, step]⟩
            | VLam _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VDelay _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VConstr _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VBuiltin _ _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
          | VDelay _ _ =>
            cases v2 with
            | VDelay _ _ => simp only [step] at herr; exact ⟨1, by simp [steps, step]⟩
            | VCon _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VLam _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VConstr _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VBuiltin _ _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
          | VConstr _ _ =>
            cases v2 with
            | VConstr _ _ => simp only [step] at herr; exact ⟨1, by simp [steps, step]⟩
            | VCon _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VLam _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VDelay _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VBuiltin _ _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
        | constrField tag rest' hd he' =>
          cases rest' with
          | cons m ms =>
            simp only [step] at herr
            have hstk' := StackBehEq.cons (.constrField tag ms (listValueEqInf_cons hv hd) he') hrest
            have hreach := ih M (by omega) _ _ (.compute m hstk' he') herr
            obtain ⟨K, hK⟩ := hreach; exact ⟨K + 1, by simp [steps, step]; exact hK⟩
          | nil =>
            simp only [step] at herr
            -- herr : steps M (.ret rest1 (.VConstr tag ((v1 :: done1).reverse))) = .error
            -- Need ValEqInf for the reversed constr
            have hcons := listValueEqInf_cons hv hd
            -- Build ValEqInf directly at the (v :: done).reverse level
            have hve : ValEqInf (.VConstr tag _) (.VConstr tag _) := fun j => by
              cases j with
              | zero => simp [ValueEq]
              | succ k =>
                unfold ValueEq; constructor
                · rfl
                · -- Need ListValueEq k (v1 :: done1).reverse (v2 :: done2).reverse
                  have := listValueEqInf_reverse hcons
                  exact this k
            have hreach := ih M (by omega) _ _ (StateBehRel.ret hrest hve) herr
            obtain ⟨K, hK⟩ := hreach
            exact ⟨K + 1, by simp only [steps, step]; exact hK⟩
        | caseScrutinee alts he' =>
          rename_i v1 v2 rest1 rest2 env1' env2'
          cases v1 with
          | VConstr tag1 fields1 =>
            cases v2 with
            | VConstr tag2 fields2 =>
              have htag := valEqInf_vconstr_tag hv; subst htag
              have hfields := valEqInf_vconstr_fields hv
              simp only [step] at herr ⊢
              cases halt : alts[tag1]? with
              | none =>
                simp only [halt] at herr ⊢
                exact ⟨1, by simp [steps, step, halt]⟩
              | some alt =>
                simp only [halt] at herr ⊢
                have hfstk := listValueEqInf_map_applyArg hfields
                have hstk' := stackBehEq_append hfstk hrest
                have hreach := ih M (by omega) _ _ (.compute alt hstk' he') herr
                obtain ⟨K, hK⟩ := hreach
                exact ⟨K + 1, by simp [steps, step, halt]; exact hK⟩
            | VCon _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VLam _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VDelay _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VBuiltin _ _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
          | VCon c1 =>
            cases v2 with
            | VCon c2 =>
              have hceq := valEqInf_vcon_eq hv; subst hceq
              simp only [step] at herr ⊢
              cases hctf : constToTagAndFields c1 with
              | none =>
                simp only [hctf] at herr ⊢
                exact ⟨1, by simp [steps, step, hctf]⟩
              | some tnf =>
                obtain ⟨tag, numCtors, fields⟩ := tnf
                simp only [hctf] at herr ⊢
                -- Same const, same constToTagAndFields, same branching
                cases hguard : (numCtors > 0 && alts.length > numCtors) with
                | true =>
                  simp only [hguard] at herr ⊢
                  exact ⟨1, by simp [steps, step, hctf, hguard]⟩
                | false =>
                  simp only [hguard] at herr ⊢
                  cases halt : alts[tag]? with
                  | none =>
                    simp only [halt] at herr ⊢
                    exact ⟨1, by simp [steps, step, hctf, hguard, halt]⟩
                  | some alt =>
                    simp only [halt] at herr ⊢
                    have hfstk := listValueEqInf_map_applyArg (listValueEqInf_refl fields)
                    have hstk' := stackBehEq_append hfstk hrest
                    have hreach := ih M (by omega) _ _ (.compute alt hstk' he') herr
                    obtain ⟨K, hK⟩ := hreach
                    exact ⟨K + 1, by simp [steps, step, hctf, hguard, halt]; exact hK⟩
            | VLam _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VDelay _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VConstr _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VBuiltin _ _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
          | VLam _ _ =>
            cases v2 with
            | VLam _ _ => simp only [step] at herr; exact ⟨1, by simp [steps, step]⟩
            | VCon _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VDelay _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VConstr _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VBuiltin _ _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
          | VDelay _ _ =>
            cases v2 with
            | VDelay _ _ => simp only [step] at herr; exact ⟨1, by simp [steps, step]⟩
            | VCon _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VLam _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VConstr _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VBuiltin _ _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
          | VBuiltin _ _ _ =>
            cases v2 with
            | VBuiltin _ _ _ => simp only [step] at herr; exact ⟨1, by simp [steps, step]⟩
            | VCon _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VLam _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VDelay _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)
            | VConstr _ _ => exact absurd (hv 1) (by unfold ValueEq; exact id)

/-- Error transfer for EnvBehEq envs: if one side errors, the other does too.
    This is Phase 1 of the fundamental lemma. -/
theorem envBehEq_error_transfer (body : Term) (env1 env2 : CekEnv)
    (he : EnvBehEq env1 env2) :
    Reaches (.compute [] env1 body) .error → Reaches (.compute [] env2 body) .error := by
  intro ⟨N, hN⟩
  exact stateBehRel_error_transfer N _ _ (.compute body .nil he) hN

/-- Halts transfer for EnvBehEq envs. -/
theorem envBehEq_halts_transfer (body : Term) (env1 env2 : CekEnv)
    (he : EnvBehEq env1 env2) :
    Halts (.compute [] env1 body) → Halts (.compute [] env2 body) := by
  -- TASK E: same structure as stateBehRel_error_transfer but for halt.
  -- Requires a stateBehRel_halts_transfer lemma proved by strong induction on N
  -- (the number of steps to reach .halt v), with the same case analysis as
  -- error_transfer. The key difference is using liftedHaltValueBeh instead of
  -- liftedErrorValueBeh for VLam/VDelay application cases, and extracting the
  -- halts↔ component from valEqInf_vlam_apply_behBundle /
  -- valEqInf_vdelay_force_behBundle (which give BehBundle including halts↔).
  sorry

theorem envBehEq_valueEq_at_halt (k : Nat) (body : Term) (env1 env2 : CekEnv)
    (he : EnvBehEq env1 env2)
    (v1 v2 : CekValue) (h1 : Reaches (.compute [] env1 body) (.halt v1))
    (h2 : Reaches (.compute [] env2 body) (.halt v2)) :
    ValueEq k v1 v2 := by
  sorry

/-! ### Main theorem combining Phase 1 and Phase 2 -/

/-- The full fundamental lemma for ValueEq env variation.
    Same body, same closure env, different extension args with ∀j ValueEq j.
    This fills the 4 sorry's in Congruence.lean. -/
theorem same_term_env_variation_valueEq (body : Term) (cenv : CekEnv)
    (va va' : CekValue) (hva : ∀ j, ValueEq j va va') :
    (Reaches (.compute [] (cenv.extend va) body) .error ↔
     Reaches (.compute [] (cenv.extend va') body) .error) ∧
    (Halts (.compute [] (cenv.extend va) body) ↔
     Halts (.compute [] (cenv.extend va') body)) ∧
    ∀ j v1 v2, Reaches (.compute [] (cenv.extend va) body) (.halt v1) →
                Reaches (.compute [] (cenv.extend va') body) (.halt v2) →
                ValueEq j v1 v2 := by
  have he : EnvBehEq (cenv.extend va) (cenv.extend va') :=
    envBehEq_extend (envBehEq_refl cenv) hva
  refine ⟨?_, ?_, ?_⟩
  · -- error↔: Phase 1
    constructor
    · exact envBehEq_error_transfer body _ _ he
    · have he' := envBehEq_extend (envBehEq_refl cenv) (fun j => valueEq_symm j _ _ (hva j))
      exact envBehEq_error_transfer body _ _ he'
  · -- halts↔: Phase 1
    constructor
    · exact envBehEq_halts_transfer body _ _ he
    · have he' := envBehEq_extend (envBehEq_refl cenv) (fun j => valueEq_symm j _ _ (hva j))
      exact envBehEq_halts_transfer body _ _ he'
  · -- ValueEq j: Phase 2
    -- For this specific case (same cenv, different extension), use structural bisim.
    -- Idea: va and va' might not be ValEqAll, but we can still get ValueEq for results.
    -- Use envBehEq_valueEq_at_halt.
    intro j v1 v2 h1 h2
    exact envBehEq_valueEq_at_halt j body _ _ he v1 v2 h1 h2

end Moist.Verified.BisimEq
