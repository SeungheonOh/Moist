import Moist.Verified.Semantics
import Moist.Verified.StepLift
import Moist.MIR.LowerTotal
import Moist.MIR.Optimize.Purity
import Moist.CEK.Builtins

set_option linter.unusedSimpArgs false

namespace Moist.Verified.Purity

open Moist.CEK
open Moist.Plutus.Term (Term Const BuiltinFun BuiltinType)
open Moist.MIR (Expr VarId lowerTotal lowerTotalList lowerTotalLet
                 isPure isPureList isPureBinds isForceable envLookupT)
open Moist.Verified.Semantics
open Moist.Verified.StepLift (liftState isActive liftState_ne_halt
  step_liftState_active steps_liftState beta_apply_from_inner)

/-! # isPure implies halting

If `isPure e = true` and `lowerTotal env e = some t` and the CEK runtime
environment is well-sized, then `t` halts and never errors.
-/

/-! ## Helper lemmas -/

private theorem force_delay_steps (ρ : CekEnv) (body' : Term) (n : Nat) :
    steps (3 + n) (.compute [] ρ (.Force (.Delay body'))) =
    steps n (.compute [] ρ body') := by
  rw [steps_trans]; rfl

private theorem no_builtin_one_argQ (b : BuiltinFun) : expectedArgs b ≠ .one .argQ := by
  cases b <;> (simp [expectedArgs]; try decide)

private theorem no_builtin_more_argQ_one_argQ (b : BuiltinFun) :
    expectedArgs b ≠ .more .argQ (.one .argQ) := by
  cases b <;> (simp [expectedArgs]; try decide)

/-! ## firstInactive (local copy since StepLift's is private) -/

private theorem firstInactive (s : State) (bound : Nat)
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
        · exfalso; apply h; exact ⟨j, hj, by cases isActive (steps j s) <;> simp_all⟩
      obtain ⟨k, hk, hinact⟩ := hex
      have hk_eq : k = bound + 1 := by
        by_cases heq : k = bound + 1
        · exact heq
        · exfalso; have hle : k ≤ bound := by omega
          have := hall k hle; simp [hinact] at this
      subst hk_eq
      exact ⟨bound + 1, Nat.le_refl _, hinact, fun j hj => hall j (by omega)⟩

/-! ## Generic liftState sub-computation embedding -/

theorem compute_to_ret_from_halt (ρ : CekEnv) (t : Term) (v : CekValue)
    (extra : Stack)
    (h : Reaches (.compute [] ρ t) (.halt v)) :
    Reaches (.compute extra ρ t) (.ret extra v) := by
  have horig := h
  obtain ⟨N, hN⟩ := h
  have h_not_active_N : isActive (steps N (.compute [] ρ t)) = false := by rw [hN]; rfl
  obtain ⟨K, hK_le, hK_inact, hK_min⟩ :=
    firstInactive (.compute [] ρ t) N ⟨N, Nat.le_refl _, h_not_active_N⟩
  have h_comm : steps K (liftState extra (.compute [] ρ t)) =
      liftState extra (steps K (.compute [] ρ t)) :=
    steps_liftState extra K (.compute [] ρ t) hK_min
  have h_not_error : steps K (.compute [] ρ t) ≠ .error := by
    intro herr
    have : steps N (.compute [] ρ t) = .error := by
      have : N = K + (N - K) := by omega
      rw [this, steps_trans, herr, steps_error]
    rw [hN] at this; simp at this
  have ⟨ve, h_inner_eq, h_lifted_eq⟩ :
      ∃ ve, (steps K (.compute [] ρ t) = .halt ve ∨
             steps K (.compute [] ρ t) = .ret [] ve) ∧
            liftState extra (steps K (.compute [] ρ t)) = .ret extra ve := by
    generalize h_sK : steps K (.compute [] ρ t) = sK at hK_inact h_not_error
    match sK with
    | .compute .. => simp [isActive] at hK_inact
    | .ret [] ve => exact ⟨ve, .inr rfl, by simp [liftState]⟩
    | .ret (_ :: _) _ => simp [isActive] at hK_inact
    | .halt ve => exact ⟨ve, .inl rfl, by simp [liftState]⟩
    | .error => exact absurd rfl h_not_error
  have h_ve_eq : ve = v := by
    have h_halt_ve : Reaches (.compute [] ρ t) (.halt ve) := by
      cases h_inner_eq with
      | inl heq => exact ⟨K, heq⟩
      | inr heq => exact ⟨K + 1, by rw [steps_trans, heq]; rfl⟩
    exact reaches_unique h_halt_ve horig
  subst h_ve_eq
  rw [show State.compute extra ρ t = liftState extra (.compute [] ρ t)
      from by simp [liftState]]
  exact ⟨K, h_comm ▸ h_lifted_eq⟩

/-! ## Constr field evaluation -/

private theorem constr_ret_done_halts (ρ : CekEnv) (tag : Nat)
    (done : List CekValue) (v : CekValue)
    (remaining : List Term) (s : Stack)
    (hhalts : ∀ t, t ∈ remaining → ∃ vt, Reaches (.compute [] ρ t) (.halt vt)) :
    ∃ vfinal, Reaches (.ret (.constrField tag done remaining ρ :: s) v) (.ret s vfinal) := by
  match remaining with
  | [] =>
    exact ⟨.VConstr tag ((v :: done).reverse), 1, by simp [steps, step]⟩
  | t :: ts =>
    have ⟨vt, ht_halts⟩ := hhalts t (List.Mem.head ts)
    have h_t_ret := compute_to_ret_from_halt ρ t vt
      (.constrField tag (v :: done) ts ρ :: s) ht_halts
    obtain ⟨Kt, hKt⟩ := h_t_ret
    have hhalts_ts : ∀ t', t' ∈ ts → ∃ vt, Reaches (.compute [] ρ t') (.halt vt) :=
      fun t' ht' => hhalts t' (List.mem_cons_of_mem t ht')
    have ⟨vfinal, Krest, hKrest⟩ := constr_ret_done_halts ρ tag (v :: done) vt ts s hhalts_ts
    exact ⟨vfinal, 1 + Kt + Krest, by
      have : 1 + Kt + Krest = 1 + (Kt + Krest) := by omega
      rw [this, steps_trans, show steps 1 (.ret (.constrField tag done (t :: ts) ρ :: s) v) =
        .compute (.constrField tag (v :: done) ts ρ :: s) ρ t from rfl,
        steps_trans, hKt, hKrest]⟩

private theorem constr_halts_of_all_halt (ρ : CekEnv) (tag : Nat) (terms : List Term)
    (hhalts : ∀ t, t ∈ terms → ∃ v, Reaches (.compute [] ρ t) (.halt v)) :
    ∃ v, Reaches (.compute [] ρ (.Constr tag terms)) (.halt v) := by
  match terms with
  | [] => exact ⟨.VConstr tag [], 2, rfl⟩
  | t :: ts =>
    have ⟨vt, ht_halts⟩ := hhalts t (List.Mem.head ts)
    have h_t_ret := compute_to_ret_from_halt ρ t vt
      [.constrField tag [] ts ρ] ht_halts
    obtain ⟨Kt, hKt⟩ := h_t_ret
    have hhalts_ts : ∀ t', t' ∈ ts → ∃ v, Reaches (.compute [] ρ t') (.halt v) :=
      fun t' ht' => hhalts t' (List.mem_cons_of_mem t ht')
    have ⟨vfinal, Krest, hKrest⟩ := constr_ret_done_halts ρ tag [] vt ts [] hhalts_ts
    exact ⟨vfinal, 1 + Kt + Krest + 1, by
      have : 1 + Kt + Krest + 1 = 1 + (Kt + (Krest + 1)) := by omega
      rw [this, steps_trans, show steps 1 (.compute [] ρ (.Constr tag (t :: ts))) =
        .compute [.constrField tag [] ts ρ] ρ t from rfl,
        steps_trans, hKt, steps_trans, hKrest]; rfl⟩

/-! ## Main theorem -/

mutual
  theorem isPure_halts (e : Expr) (t : Term) (env : List VarId) (ρ : CekEnv)
      (hpure : isPure e = true) (hlower : lowerTotal env e = some t)
      (hwf : WellSizedEnv env.length ρ) :
      ∃ v, Reaches (.compute [] ρ t) (.halt v) := by
    match e with
    -- Excluded by isPure = false
    | .Error => exact absurd hpure (by unfold isPure; decide)
    | .Fix _ _ => simp [lowerTotal] at hlower
    | .Case _ _ => exact absurd hpure (by unfold isPure; decide)
    | .App _ _ => exact absurd hpure (by unfold isPure; decide)
    -- Value forms: 2 steps each
    | .Var x =>
      simp only [lowerTotal.eq_1] at hlower
      split at hlower
      · rename_i idx hlook
        injection hlower with hlower; subst hlower
        have hbound := Moist.MIR.envLookupT_bound env x idx hlook
        have ⟨v, hv⟩ := hwf (idx + 1) (by omega) (by omega)
        exact ⟨v, 2, by simp [steps, step, hv]⟩
      · simp at hlower
    | .Lit (c, ty) =>
      simp [lowerTotal] at hlower; subst hlower
      exact ⟨.VCon c, 2, rfl⟩
    | .Builtin b =>
      simp [lowerTotal] at hlower; subst hlower
      exact ⟨.VBuiltin b [] (expectedArgs b), 2, rfl⟩
    | .Lam x body =>
      simp only [lowerTotal.eq_5, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlower
      obtain ⟨body', _, heq⟩ := hlower
      injection heq with heq; subst heq
      exact ⟨.VLam body' ρ, 2, rfl⟩
    | .Delay inner =>
      simp only [lowerTotal.eq_8, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlower
      obtain ⟨inner', _, heq⟩ := hlower
      injection heq with heq; subst heq
      exact ⟨.VDelay inner' ρ, 2, rfl⟩
    -- Force (Delay body): 3 setup steps + IH on body
    | .Force (.Delay body) =>
      have hpb : isPure body = true := by
        change isPure (.Force (.Delay body)) = true at hpure
        simp only [isPure] at hpure; exact hpure
      simp only [lowerTotal.eq_7, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlower
      obtain ⟨inner', hinner, heq⟩ := hlower
      injection heq with heq; subst heq
      simp only [lowerTotal.eq_8, Option.bind_eq_bind, Option.bind_eq_some_iff] at hinner
      obtain ⟨body', hbody, heq⟩ := hinner
      injection heq with heq; subst heq
      have ⟨v, n, hn⟩ := isPure_halts body body' env ρ hpb hbody hwf
      exact ⟨v, n + 3, by rw [show n + 3 = 3 + n from by omega]; exact force_delay_steps ρ body' n ▸ hn⟩
    -- Force (Builtin b): single type-force
    | .Force (.Builtin b) =>
      simp only [lowerTotal.eq_7, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlower
      obtain ⟨inner', hinner, heq⟩ := hlower
      injection heq with heq; subst heq
      simp [lowerTotal] at hinner; subst hinner
      have hhead : ((expectedArgs b).head == .argQ) = true := by
        simp only [isPure, isForceable, Bool.and_true, Bool.true_and] at hpure; exact hpure
      cases hea : expectedArgs b with
      | more k rest =>
        cases k with
        | argQ =>
          exact ⟨.VBuiltin b [] rest, 4, by
            simp [steps, step, hea, ExpectedArgs.head, ExpectedArgs.tail]⟩
        | argV =>
          exfalso; rw [hea] at hhead; simp [ExpectedArgs.head] at hhead
          exact absurd hhead (by native_decide)
      | one k =>
        cases k with
        | argQ => exfalso; exact no_builtin_one_argQ b hea
        | argV =>
          exfalso; rw [hea] at hhead; simp [ExpectedArgs.head] at hhead
          exact absurd hhead (by native_decide)
    -- Force (Force (Builtin b)): double type-force
    | .Force (.Force (.Builtin b)) =>
      simp [lowerTotal] at hlower; subst hlower
      have hfc : isForceable (.Force (.Builtin b)) = true := by
        simp only [isPure, Bool.and_eq_true] at hpure; exact hpure.1
      -- isForceable (.Force (.Builtin b)):
      --   match expectedArgs b with .more .argQ rest => rest.head == .argQ | _ => false
      have hfc' : (match expectedArgs b with
          | .more .argQ rest => rest.head == .argQ | _ => false) = true := by
        simp only [isForceable] at hfc; exact hfc
      cases hea : expectedArgs b with
      | more k rest =>
        cases k with
        | argQ =>
          rw [hea] at hfc'; simp at hfc'
          -- hfc' : rest.head == .argQ = true
          cases hrest : rest with
          | more k2 rest2 =>
            cases k2 with
            | argQ =>
              exact ⟨.VBuiltin b [] rest2, 6, by
                simp [steps, step, hea, hrest, ExpectedArgs.head, ExpectedArgs.tail]⟩
            | argV =>
              exfalso; rw [hrest] at hfc'; simp [ExpectedArgs.head] at hfc'
              exact absurd hfc' (by native_decide)
          | one k2 =>
            cases k2 with
            | argQ => exfalso; rw [hrest] at hea; exact no_builtin_more_argQ_one_argQ b hea
            | argV =>
              exfalso; rw [hrest] at hfc'; simp [ExpectedArgs.head] at hfc'
              exact absurd hfc' (by native_decide)
        | argV => rw [hea] at hfc'; simp at hfc'
      | one _ => rw [hea] at hfc'; simp at hfc'
    -- Force of other forms: excluded by isPure/isForceable = false
    | .Force (.Var _) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Lit _) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Lam _ _) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Fix _ _) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.App _ _) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Constr _ _) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Case _ _) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Let _ _) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force .Error => exact absurd hpure (by unfold isPure isForceable; simp)
    -- Force (Force (non-Builtin)): isForceable (.Force _) = false for non-Builtin inner
    | .Force (.Force (.Var _)) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Force (.Lit _)) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Force (.Lam _ _)) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Force (.Fix _ _)) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Force (.App _ _)) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Force (.Constr _ _)) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Force (.Case _ _)) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Force (.Let _ _)) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Force .Error) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Force (.Delay _)) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Force (.Force _)) => exact absurd hpure (by unfold isPure isForceable; simp)
    -- Constr with pure args
    | .Constr tag args =>
      have hpure' : isPureList args = true := by
        change isPure (.Constr tag args) = true at hpure
        simp only [isPure] at hpure; exact hpure
      simp only [lowerTotal.eq_9, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlower
      obtain ⟨args', hargs, heq⟩ := hlower
      injection heq with heq; subst heq
      exact constr_halts_of_all_halt ρ tag args'
        (isPureList_member_halts args args' env ρ hpure' hargs hwf)
    -- Let with pure bindings and body
    | .Let binds body =>
      have hpure' : isPureBinds binds = true ∧ isPure body = true := by
        change isPure (.Let binds body) = true at hpure
        simp only [isPure, Bool.and_eq_true] at hpure; exact hpure
      simp only [lowerTotal.eq_11] at hlower
      exact isPureBinds_halts binds body t env ρ hpure'.1 hpure'.2 hlower hwf
  termination_by sizeOf e

  /-- Each element of a pure list halts individually after lowering. -/
  theorem isPureList_member_halts (args : List Expr) (args' : List Term)
      (env : List VarId) (ρ : CekEnv)
      (hpure : isPureList args = true)
      (hlower : lowerTotalList env args = some args')
      (hwf : WellSizedEnv env.length ρ) :
      ∀ t, t ∈ args' → ∃ v, Reaches (.compute [] ρ t) (.halt v) := by
    match args with
    | [] =>
      simp [lowerTotalList] at hlower; subst hlower
      intro t ht; exact absurd ht List.not_mem_nil
    | a :: rest =>
      have hpure' : isPure a = true ∧ isPureList rest = true := by
        change isPureList (a :: rest) = true at hpure
        simp only [isPureList, Bool.and_eq_true] at hpure; exact hpure
      simp only [lowerTotalList.eq_2, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlower
      obtain ⟨ta, hta_lower, hrest⟩ := hlower
      obtain ⟨ts, hts_lower, heq⟩ := hrest
      injection heq with heq; subst heq
      intro t ht
      cases ht with
      | head => exact isPure_halts a ta env ρ hpure'.1 hta_lower hwf
      | tail _ hmem' =>
        exact isPureList_member_halts rest ts env ρ hpure'.2 hts_lower hwf t hmem'
  termination_by sizeOf args

  theorem isPureBinds_halts (binds : List (VarId × Expr × Bool)) (body : Expr)
      (t : Term) (env : List VarId) (ρ : CekEnv)
      (hpureBinds : isPureBinds binds = true) (hpureBody : isPure body = true)
      (hlower : lowerTotalLet env binds body = some t)
      (hwf : WellSizedEnv env.length ρ) :
      ∃ v, Reaches (.compute [] ρ t) (.halt v) := by
    match binds with
    | [] =>
      simp [lowerTotalLet] at hlower
      exact isPure_halts body t env ρ hpureBody hlower hwf
    | (x, rhs, _) :: rest =>
      have hpure' : isPure rhs = true ∧ isPureBinds rest = true := by
        change isPureBinds ((x, rhs, _) :: rest) = true at hpureBinds
        simp only [isPureBinds, Bool.and_eq_true] at hpureBinds; exact hpureBinds
      simp only [lowerTotalLet.eq_2, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlower
      obtain ⟨rhs', hrhs_lower, hrest⟩ := hlower
      obtain ⟨rest', hrest_lower, heq⟩ := hrest
      injection heq with heq; subst heq
      have ⟨vrhs, hrhs_halts⟩ := isPure_halts rhs rhs' env ρ hpure'.1 hrhs_lower hwf
      have ⟨vrest, hrest_halts⟩ :=
        isPureBinds_halts rest body rest' (x :: env) (ρ.extend vrhs)
          hpure'.2 hpureBody hrest_lower (wellSizedEnv_extend hwf vrhs)
      exact ⟨vrest, beta_apply_from_inner ρ rest' rhs' 0 vrhs (.halt vrest)
        hrhs_halts hrest_halts⟩
  termination_by sizeOf binds + sizeOf body
end

theorem isPure_no_error (e : Expr) (t : Term) (env : List VarId) (ρ : CekEnv)
    (hpure : isPure e = true) (hlower : lowerTotal env e = some t)
    (hwf : WellSizedEnv env.length ρ) :
    ¬ Reaches (.compute [] ρ t) .error := by
  intro herr
  have ⟨v, hv⟩ := isPure_halts e t env ρ hpure hlower hwf
  exact reaches_halt_not_error hv herr

end Moist.Verified.Purity
