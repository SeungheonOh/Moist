import Moist.Verified.SmallStep.Canon
import Moist.Verified.SmallStep.Determinism

/-! # Forward simulation: the CEK machine refines small-step reduction

The core result is `sim_step`: for a `Good`/`Canon` CEK state `s`, the discharged
term either reduces to the discharge of `step s` (administrative transitions take
0 steps, real βδ/case/builtin reductions take 1, error-propagation takes several),
or the CEK is about to `error` from a genuinely *stuck* configuration whose
discharge is a stuck normal form.
-/

namespace Moist.Verified.SmallStep

open Moist.Plutus.Term (Term)
open Moist.CEK
open Moist.Verified (substTerm substTermList renameTerm shiftRename closedAt)

/-! ## List/substitution helpers -/

theorem substTermList_eq_map (p : Nat) (r : Term) (ts : List Term) :
    substTermList p r ts = ts.map (substTerm p r ·) := by
  induction ts with
  | nil => simp [substTermList]
  | cons a as ih => simp only [substTermList, List.map_cons, ih]

/-! ## `dischargeEnv` distributes over term constructors -/

theorem dischargeEnv_closed_noop : ∀ (ρ : CekEnv) (d : Nat) {t : Term}, closedAt 0 t = true →
    dischargeEnv ρ d t = t
  | .nil, _, _, _ => by simp [dischargeEnv]
  | .cons v rest, d, t, ht => by
    simp only [dischargeEnv]
    rw [substTerm_closed ht (d + 1) (discharge v) (by omega)]
    exact dischargeEnv_closed_noop rest d ht

theorem dischargeEnv_force : ∀ (ρ : CekEnv) (d : Nat) (e : Term),
    dischargeEnv ρ d (.Force e) = .Force (dischargeEnv ρ d e)
  | .nil, _, _ => by simp [dischargeEnv]
  | .cons v rest, d, e => by
    simp only [dischargeEnv, substTerm]
    exact dischargeEnv_force rest d (substTerm (d + 1) (discharge v) e)

theorem dischargeEnv_delay : ∀ (ρ : CekEnv) (d : Nat) (e : Term),
    dischargeEnv ρ d (.Delay e) = .Delay (dischargeEnv ρ d e)
  | .nil, _, _ => by simp [dischargeEnv]
  | .cons v rest, d, e => by
    simp only [dischargeEnv, substTerm]
    exact dischargeEnv_delay rest d (substTerm (d + 1) (discharge v) e)

theorem dischargeEnv_apply : ∀ (ρ : CekEnv) (d : Nat) (f x : Term),
    dischargeEnv ρ d (.Apply f x) = .Apply (dischargeEnv ρ d f) (dischargeEnv ρ d x)
  | .nil, _, _, _ => by simp [dischargeEnv]
  | .cons v rest, d, f, x => by
    simp only [dischargeEnv, substTerm]
    exact dischargeEnv_apply rest d (substTerm (d + 1) (discharge v) f)
      (substTerm (d + 1) (discharge v) x)

theorem dischargeEnv_constant : ∀ (ρ : CekEnv) (d : Nat) (cb : Moist.Plutus.Term.Const × _),
    dischargeEnv ρ d (.Constant cb) = .Constant cb
  | .nil, _, _ => by simp [dischargeEnv]
  | .cons v rest, d, cb => by
    simp only [dischargeEnv, substTerm]; exact dischargeEnv_constant rest d cb

theorem dischargeEnv_builtin : ∀ (ρ : CekEnv) (d : Nat) (b : Moist.Plutus.Term.BuiltinFun),
    dischargeEnv ρ d (.Builtin b) = .Builtin b
  | .nil, _, _ => by simp [dischargeEnv]
  | .cons v rest, d, b => by
    simp only [dischargeEnv, substTerm]; exact dischargeEnv_builtin rest d b

theorem dischargeEnv_constr : ∀ (ρ : CekEnv) (d : Nat) (tag : Nat) (args : List Term),
    dischargeEnv ρ d (.Constr tag args) = .Constr tag (args.map (dischargeEnv ρ d ·))
  | .nil, _, _, args => by simp [dischargeEnv, List.map_id']
  | .cons v rest, d, tag, args => by
    simp only [dischargeEnv, substTerm, substTermList_eq_map]
    rw [dischargeEnv_constr rest d tag (args.map (substTerm (d + 1) (discharge v) ·)), List.map_map]
    rfl

theorem dischargeEnv_case : ∀ (ρ : CekEnv) (d : Nat) (s : Term) (alts : List Term),
    dischargeEnv ρ d (.Case s alts) = .Case (dischargeEnv ρ d s) (alts.map (dischargeEnv ρ d ·))
  | .nil, _, _, alts => by simp [dischargeEnv, List.map_id']
  | .cons v rest, d, s, alts => by
    simp only [dischargeEnv, substTerm, substTermList_eq_map]
    rw [dischargeEnv_case rest d (substTerm (d + 1) (discharge v) s)
          (alts.map (substTerm (d + 1) (discharge v) ·)), List.map_map]
    rfl

theorem dischargeEnv_lam : ∀ {ρ : CekEnv}, EnvDischargeClosed ρ → ∀ (d name : Nat) (body : Term),
    dischargeEnv ρ d (.Lam name body) = .Lam name (dischargeEnv ρ (d + 1) body)
  | .nil, _, _, _, _ => by simp [dischargeEnv]
  | .cons v rest, hρ, d, name, body => by
    simp only [dischargeEnv]
    rw [show substTerm (d + 1) (discharge v) (.Lam name body)
          = .Lam name (substTerm (d + 1 + 1) (discharge v) body) from by
        rw [substTerm]; rw [renameTerm_shift_closed hρ.1]]
    exact dischargeEnv_lam hρ.2 d name (substTerm (d + 1 + 1) (discharge v) body)

/-- Looking up a variable in a `Good` environment discharges to the discharge of
    the looked-up value. -/
theorem dischargeEnv_var_lookup : ∀ {ρ : CekEnv}, GoodEnv ρ → ∀ {n : Nat} {v : CekValue},
    ρ.lookup n = some v → dischargeEnv ρ 0 (.Var n) = discharge v
  | .nil, _, _, _, h => by simp [CekEnv.lookup] at h
  | .cons w rest, .cons hw _, 1, v, h => by
    simp only [CekEnv.lookup, Option.some.injEq] at h
    subst h
    simp only [dischargeEnv, substTerm, if_pos]
    exact dischargeEnv_closed_noop rest 0 (good_discharge_closed hw)
  | .cons w rest, .cons _ hrest, 0, v, h => by simp [CekEnv.lookup] at h
  | .cons w rest, .cons _ hrest, n + 2, v, h => by
    simp only [CekEnv.lookup] at h
    simp only [dischargeEnv]
    rw [substTerm_var, if_neg (by omega), if_pos (by omega),
      show n + 2 - 1 = n + 1 from by omega]
    exact dischargeEnv_var_lookup hrest h


/-! ## The discharged stack is an evaluation context -/

/-- `Good` frames/stacks are well-formed (project to `StackDischarge.WFStack`). -/
theorem goodFrame_wfFrame {f : Frame} (h : GoodFrame f) : WFFrame f := by
  cases f with
  | force => trivial
  | arg M ρ => trivial
  | funV vf => exact good_wf h
  | applyArg vx => exact good_wf h
  | constrField tag done todo ρ => exact goodList_wf h.1
  | caseScrutinee alts ρ => trivial

theorem goodStack_wfStack {π : Stack} (h : GoodStack π) : WFStack π :=
  fun f hf => goodFrame_wfFrame (h f hf)

theorem dischargeStack_append : ∀ (a b : Stack) (t : Term),
    dischargeStack (a ++ b) t = dischargeStack b (dischargeStack a t)
  | [], _, _ => by simp [dischargeStack]
  | f :: a, b, t => by
    simp only [List.cons_append, dischargeStack]
    exact dischargeStack_append a b (frameCtx f t)

/-- The field-frames produced by `case`-on-constructor build an application spine. -/
theorem dischargeStack_applyArgFrames : ∀ (fields : List CekValue) (t : Term),
    dischargeStack (fields.map Frame.applyArg) t = mkApps t (dischargeList fields)
  | [], t => by simp [dischargeStack, mkApps, dischargeList]
  | f :: fs, t => by
    simp only [List.map_cons, dischargeStack, frameCtx, dischargeList, mkApps, List.foldl_cons]
    exact dischargeStack_applyArgFrames fs (Term.Apply t (discharge f))

/-! ## Stuck non-`Error` terms remain stuck under a discharged stack -/

theorem frameCtx_ne_error (f : Frame) (t : Term) : frameCtx f t ≠ .Error := by
  cases f <;> simp [frameCtx]

theorem frameCtx_not_value {f : Frame} {t : Term} (hnv : ¬ Value t) : ¬ Value (frameCtx f t) := by
  cases f with
  | force => intro hv; obtain ⟨_, _, _, hsp⟩ := value_force_inv hv; exact hnv (.builtin hsp)
  | arg M ρ => intro hv; obtain ⟨_, _, _, hsp, _⟩ := value_apply_inv hv; exact hnv (.builtin hsp)
  | funV vf => intro hv; obtain ⟨_, _, _, _, hva⟩ := value_apply_inv hv; exact hnv hva
  | applyArg vx => intro hv; obtain ⟨_, _, _, hsp, _⟩ := value_apply_inv hv; exact hnv (.builtin hsp)
  | constrField tag done todo ρ =>
    intro hv
    cases hv with
    | constr hvl => exact hnv (valueList_mem hvl (by simp))
    | builtin hsp => cases hsp
  | caseScrutinee alts ρ => exact not_value_case

/-- Inversion for an `Apply` reduction (general arguments, to sidestep dependent
    elimination when the argument is a fixed compound term). -/
theorem step_apply_inv {f x c : Term} (h : Step (.Apply f x) c) :
    (∃ name M, f = .Lam name M ∧ Value x)
    ∨ (∃ b args, BSpine f b args (.one .argV) ∧ Value x)
    ∨ (f = .Error)
    ∨ (Value f ∧ x = .Error)
    ∨ (∃ f', Step f f')
    ∨ (Value f ∧ ∃ x', Step x x') := by
  cases h with
  | betaLam hv => exact Or.inl ⟨_, _, rfl, hv⟩
  | satApply hsp hv => exact Or.inr (Or.inl ⟨_, _, hsp, hv⟩)
  | errAppL => exact Or.inr (Or.inr (Or.inl rfl))
  | errAppR hv => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, rfl⟩)))
  | congAppL hs => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hs⟩))))
  | congAppR hv hs => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hv, _, hs⟩))))

/-- Inversion for a `Force` reduction (general subterm). -/
theorem step_force_inv {t c : Term} (h : Step (.Force t) c) :
    (∃ M, t = .Delay M) ∨ (∃ b args, BSpine t b args (.one .argQ)) ∨ (t = .Error)
    ∨ (∃ t', Step t t') := by
  cases h with
  | forceDelay => exact Or.inl ⟨_, rfl⟩
  | satForce hsp => exact Or.inr (Or.inl ⟨_, _, hsp⟩)
  | errForce => exact Or.inr (Or.inr (Or.inl rfl))
  | congForce hs => exact Or.inr (Or.inr (Or.inr ⟨_, hs⟩))

/-- Inversion for a `Case` reduction (general scrutinee). -/
theorem step_case_inv {scrut c : Term} {alts : List Term} (h : Step (.Case scrut alts) c) :
    (∃ i vs, scrut = .Constr i vs) ∨ (∃ cb, scrut = .Constant cb) ∨ (scrut = .Error)
    ∨ (∃ s', Step scrut s') := by
  cases h with
  | caseConstr _ _ => exact Or.inl ⟨_, _, rfl⟩
  | caseConst _ _ _ => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | errCase => exact Or.inr (Or.inr (Or.inl rfl))
  | congCase hs => exact Or.inr (Or.inr (Or.inr ⟨_, hs⟩))

/-- An application whose function is a value that cannot be applied (not a lambda,
    not a value-expecting builtin spine) is stuck. -/
theorem apply_fn_stuck {fn arg : Term} (hfn : Value fn) (harg : Value arg)
    (hnl : ∀ x M, fn ≠ .Lam x M)
    (hnsp : ∀ b args, ¬ BSpine fn b args (.one .argV))
    (hnsp' : ∀ b args rest, ¬ BSpine fn b args (.more .argV rest)) :
    Normal (.Apply fn arg) ∧ ¬ Value (.Apply fn arg) ∧ (Term.Apply fn arg) ≠ .Error := by
  refine ⟨?_, ?_, by simp⟩
  · rintro ⟨_, hst⟩
    rcases step_apply_inv hst with ⟨x, M, hfe, _⟩ | ⟨b, a, hsp, _⟩ | hfe | ⟨_, hxe⟩ | ⟨_, hsf⟩ | ⟨_, _, hsx⟩
    · exact hnl x M hfe
    · exact hnsp b a hsp
    · exact not_value_error (hfe ▸ hfn)
    · exact not_value_error (hxe ▸ harg)
    · exact value_normal hfn ⟨_, hsf⟩
    · exact value_normal harg ⟨_, hsx⟩
  · intro hval; obtain ⟨b, a, rest, hsp, _⟩ := value_apply_inv hval; exact hnsp' b a rest hsp

/-- A `case` whose scrutinee is a value that is neither a constructor nor a
    constant is stuck. -/
theorem case_scrut_stuck {scrut : Term} {alts : List Term} (hsv : Value scrut)
    (hnc : ∀ i vs, scrut ≠ .Constr i vs) (hncon : ∀ cb, scrut ≠ .Constant cb) :
    Normal (.Case scrut alts) ∧ ¬ Value (.Case scrut alts) ∧ (Term.Case scrut alts) ≠ .Error := by
  refine ⟨?_, not_value_case, by simp⟩
  rintro ⟨_, hst⟩
  rcases step_case_inv hst with ⟨i, vs, he⟩ | ⟨cb, he⟩ | he | ⟨_, hsc⟩
  · exact hnc i vs he
  · exact hncon cb he
  · exact not_value_error (he ▸ hsv)
  · exact value_normal hsv ⟨_, hsc⟩

theorem frameCtx_normal {f : Frame} (hf : WFFrame f) {t : Term}
    (hn : Normal t) (hnv : ¬ Value t) (hne : t ≠ .Error) : Normal (frameCtx f t) := by
  rintro ⟨t', hstep⟩
  cases f with
  | force =>
    cases hstep with
    | forceDelay => exact hnv .delay
    | satForce hsp => exact hnv (.builtin hsp)
    | errForce => exact hne rfl
    | congForce hs => exact hn ⟨_, hs⟩
  | arg M ρ =>
    rcases step_apply_inv hstep with ⟨_,_,hfe,_⟩|⟨_,_,hsp,_⟩|hfe|⟨hvf,_⟩|⟨_,hs⟩|⟨hvf,_,_⟩
    · exact hnv (hfe ▸ .lam)
    · exact hnv (.builtin hsp)
    · exact hne hfe
    · exact hnv hvf
    · exact hn ⟨_, hs⟩
    · exact hnv hvf
  | funV vf =>
    have hvalvf : Value (discharge vf) := value_discharge hf
    rcases step_apply_inv hstep with ⟨_,_,_,hvx⟩|⟨_,_,_,hvx⟩|hfe|⟨_,hxe⟩|⟨_,hs⟩|⟨_,_,hs⟩
    · exact hnv hvx
    · exact hnv hvx
    · exact not_value_error (hfe ▸ hvalvf)
    · exact hne hxe
    · exact value_normal hvalvf ⟨_, hs⟩
    · exact hn ⟨_, hs⟩
  | applyArg vx =>
    have hvalvx : Value (discharge vx) := value_discharge hf
    rcases step_apply_inv hstep with ⟨_,_,hfe,_⟩|⟨_,_,hsp,_⟩|hfe|⟨_,hxe⟩|⟨_,hs⟩|⟨hvf,_,_⟩
    · exact hnv (hfe ▸ .lam)
    · exact hnv (.builtin hsp)
    · exact hne hfe
    · exact not_value_error (hxe ▸ hvalvx)
    · exact hn ⟨_, hs⟩
    · exact hnv hvf
  | constrField tag done todo ρ =>
    have hvl : ValueList ((dischargeList done).reverse) := valueList_reverse (valueList_discharge hf)
    rcases step_constr_inv hstep with ⟨l2, r2, hvl2, heq, _⟩ | ⟨l2, m, m', r2, hvl2, hstep2, heq, _⟩
    · obtain ⟨_, hm, _⟩ := firstNonValue_unique hvl hnv hvl2 not_value_error heq
      exact hne hm
    · obtain ⟨_, hm, _⟩ := firstNonValue_unique hvl hnv hvl2 (step_not_value hstep2) heq
      exact hn ⟨_, hm ▸ hstep2⟩
  | caseScrutinee alts ρ =>
    cases hstep with
    | caseConstr hvl _ => exact hnv (.constr hvl)
    | caseConst _ _ _ => exact hnv .constant
    | errCase => exact hne rfl
    | congCase hs => exact hn ⟨_, hs⟩

/-- A non-`Error` stuck term remains stuck (and non-`Error`) under a `Good` stack. -/
theorem dischargeStack_stuck : ∀ {π : Stack}, GoodStack π → ∀ {t : Term},
    Normal t → ¬ Value t → t ≠ .Error →
    Normal (dischargeStack π t) ∧ ¬ Value (dischargeStack π t) ∧ dischargeStack π t ≠ .Error
  | [], _, _, hn, hnv, hne => by simp only [dischargeStack]; exact ⟨hn, hnv, hne⟩
  | f :: π, hπ, t, hn, hnv, hne => by
    simp only [dischargeStack]
    exact dischargeStack_stuck (goodStack_tail hπ)
      (frameCtx_normal (goodFrame_wfFrame (goodStack_head hπ)) hn hnv hne)
      (frameCtx_not_value hnv) (frameCtx_ne_error f t)



/-! ## Stuck leaves -/

theorem var_normal (n : Nat) : Normal (.Var n) := by rintro ⟨_, hs⟩; cases hs
theorem not_value_var (n : Nat) : ¬ Value (.Var n) := by
  intro hv; cases hv with | builtin hsp => cases hsp

/-! ## Forward simulation: `compute` transitions -/

set_option maxHeartbeats 2000000 in
theorem sim_step_compute (π : Stack) (ρ : CekEnv) (M : Term)
    (hg : GoodState (.compute π ρ M)) (hc : CanonState (.compute π ρ M)) :
    Steps (dischargeState (.compute π ρ M)) (dischargeState (step (.compute π ρ M)))
    ∨ (step (.compute π ρ M) = .error ∧ Stuck (dischargeState (.compute π ρ M))) := by
  obtain ⟨hMc, hρ, hπ⟩ := hg
  obtain ⟨hMcanon, _, _⟩ := hc
  have hπw := goodStack_wfStack hπ
  cases M with
  | Var n =>
    cases n with
    | zero =>
      -- `Var 0` never resolves: the CEK errors and the discharge is a stuck free variable.
      have h0 : ρ.lookup 0 = none := by cases ρ <;> rfl
      refine Or.inr ⟨by simp only [step, h0], ?_⟩
      have hvar : dischargeEnv ρ 0 (.Var 0) = .Var 0 :=
        dischargeEnv_closed_noop ρ 0 (by simp [closedAt])
      simp only [dischargeState, hvar]
      have := dischargeStack_stuck hπ (var_normal 0) (not_value_var 0) (by simp)
      exact ⟨this.1, this.2.1⟩
    | succ m =>
      have hn : m + 1 ≤ ρ.length := by simpa [closedAt] using hMc
      obtain ⟨v, hv⟩ := ρ.lookup_some_of_le_length (m + 1) (by omega) hn
      refine Or.inl ?_
      rw [show dischargeState (step (.compute π ρ (.Var (m + 1))))
            = dischargeState (.compute π ρ (.Var (m + 1))) from by
        simp only [step, hv, dischargeState, dischargeEnv_var_lookup hρ hv]]
      exact .refl
  | Constant cb =>
    obtain ⟨c, bt⟩ := cb
    refine Or.inl ?_
    have hbt : bt = Moist.Plutus.Term.constType c := by rw [Canonical] at hMcanon; exact hMcanon
    rw [show dischargeState (step (.compute π ρ (.Constant (c, bt))))
          = dischargeState (.compute π ρ (.Constant (c, bt))) from by
      simp only [step, dischargeState, dischargeEnv_constant, discharge, hbt]]
    exact .refl
  | Builtin b =>
    refine Or.inl ?_
    rw [show dischargeState (step (.compute π ρ (.Builtin b)))
          = dischargeState (.compute π ρ (.Builtin b)) from by
      simp only [step, dischargeState, dischargeEnv_builtin, discharge, dischargeList,
        consumedSteps_self, List.reverse_nil, dischargeSpine]]
    exact .refl
  | Lam name body =>
    refine Or.inl ?_
    have hname : name = 0 := by rw [Canonical] at hMcanon; exact hMcanon.1
    rw [show dischargeState (step (.compute π ρ (.Lam name body)))
          = dischargeState (.compute π ρ (.Lam name body)) from by
      simp only [step, dischargeState, dischargeEnv_lam (goodEnv_envDischargeClosed hρ), discharge, hname]]
    exact .refl
  | Delay body =>
    refine Or.inl ?_
    rw [show dischargeState (step (.compute π ρ (.Delay body)))
          = dischargeState (.compute π ρ (.Delay body)) from by
      simp only [step, dischargeState, dischargeEnv_delay, discharge]]
    exact .refl
  | Force e =>
    refine Or.inl ?_
    rw [show dischargeState (step (.compute π ρ (.Force e)))
          = dischargeState (.compute π ρ (.Force e)) from by
      simp only [step, dischargeState, dischargeStack, frameCtx, dischargeEnv_force]]
    exact .refl
  | Apply f x =>
    refine Or.inl ?_
    rw [show dischargeState (step (.compute π ρ (.Apply f x)))
          = dischargeState (.compute π ρ (.Apply f x)) from by
      simp only [step, dischargeState, dischargeStack, frameCtx, dischargeEnv_apply]]
    exact .refl
  | Constr tag args =>
    cases args with
    | nil =>
      refine Or.inl ?_
      rw [show dischargeState (step (.compute π ρ (.Constr tag [])))
            = dischargeState (.compute π ρ (.Constr tag [])) from by
        simp only [step, dischargeState, dischargeEnv_constr, discharge, dischargeList, List.map_nil]]
      exact .refl
    | cons m ms =>
      refine Or.inl ?_
      rw [show dischargeState (step (.compute π ρ (.Constr tag (m :: ms))))
            = dischargeState (.compute π ρ (.Constr tag (m :: ms))) from by
        simp only [step, dischargeState, dischargeStack, frameCtx, dischargeEnv_constr,
          dischargeList, List.reverse_nil, List.nil_append, List.map_cons]]
      exact .refl
  | Case scrut alts =>
    refine Or.inl ?_
    rw [show dischargeState (step (.compute π ρ (.Case scrut alts)))
          = dischargeState (.compute π ρ (.Case scrut alts)) from by
      simp only [step, dischargeState, dischargeStack, frameCtx, dischargeEnv_case]]
    exact .refl
  | Error =>
    refine Or.inl ?_
    have hbefore : dischargeState (.compute π ρ .Error) = dischargeStack π .Error := by
      simp only [dischargeState, dischargeEnv_error]
    have hafter : dischargeState (step (.compute π ρ .Error)) = .Error := by simp [step, dischargeState]
    rw [hbefore, hafter]
    exact dischargeStack_error hπw


/-! ## Forward simulation: `ret` transitions -/

set_option maxHeartbeats 4000000 in
theorem sim_step_ret (π : Stack) (v : CekValue)
    (hg : GoodState (.ret π v)) (hc : CanonState (.ret π v)) :
    Steps (dischargeState (.ret π v)) (dischargeState (step (.ret π v)))
    ∨ (step (.ret π v) = .error ∧ Stuck (dischargeState (.ret π v))) := by
  obtain ⟨hv, hπ⟩ := hg
  obtain ⟨hvc, hπc⟩ := hc
  cases π with
  | nil =>
    refine Or.inl ?_
    rw [show dischargeState (step (.ret [] v)) = dischargeState (.ret [] v) from by
      simp only [step, dischargeState, dischargeStack]]
    exact .refl
  | cons f s =>
    have hf := goodStack_head hπ
    have hs := goodStack_tail hπ
    have hsw := goodStack_wfStack hs
    -- helper to discharge `ret (f :: s) v` as `dischargeStack s (frameCtx f (discharge v))`
    have hbefore : dischargeState (.ret (f :: s) v) = dischargeStack s (frameCtx f (discharge v)) := by
      simp only [dischargeState, dischargeStack]
    cases f with
    | force =>
      cases v with
      | VDelay body ρ' =>
        refine Or.inl ?_
        rw [hbefore]
        rw [show frameCtx Frame.force (discharge (.VDelay body ρ'))
              = .Force (.Delay (dischargeEnv ρ' 0 body)) from by simp only [frameCtx, discharge]]
        rw [show dischargeState (step (.ret (.force :: s) (.VDelay body ρ')))
              = dischargeStack s (dischargeEnv ρ' 0 body) from by simp only [step, dischargeState]]
        exact Steps.single (dischargeStack_cong hsw Step.forceDelay)
      | VBuiltin b args ea =>
        cases hv with
        | vbuiltin hsp hargs =>
          have hbsp : BSpine (discharge (.VBuiltin b args ea)) b (dischargeList args).reverse ea :=
            bspine_discharge hsp (valueList_discharge (goodList_wf hargs))
          cases ea with
          | one k =>
            cases k with
            | argQ =>
              refine Or.inl ?_
              have hres : dischargeResult (evalBuiltin b ((reflectList ((dischargeList args).reverse)).reverse))
                  = dischargeResult (evalBuiltin b args) := by
                rw [reflectList_reverse_dischargeList]; exact evalBuiltin_rdv (goodList_wf hargs)
              rw [hbefore, show frameCtx Frame.force (discharge (.VBuiltin b args (.one .argQ)))
                    = .Force (discharge (.VBuiltin b args (.one .argQ))) from by simp only [frameCtx]]
              have hstep := Step.satForce hbsp
              rw [hres] at hstep
              cases hev : evalBuiltin b args with
              | some w =>
                rw [show dischargeState (step (.ret (.force :: s) (.VBuiltin b args (.one .argQ))))
                      = dischargeStack s (discharge w) from by
                    simp only [step, ExpectedArgs.head, ExpectedArgs.tail, hev, dischargeState]]
                rw [hev] at hstep; simp only [dischargeResult] at hstep
                exact Steps.single (dischargeStack_cong hsw hstep)
              | none =>
                rw [show dischargeState (step (.ret (.force :: s) (.VBuiltin b args (.one .argQ)))) = .Error from by
                    simp only [step, ExpectedArgs.head, ExpectedArgs.tail, hev, dischargeState]]
                rw [hev] at hstep; simp only [dischargeResult] at hstep
                exact Steps.trans (Steps.single (dischargeStack_cong hsw hstep)) (dischargeStack_error hsw)
            | argV =>
              -- force on a builtin still expecting a value: stuck
              refine Or.inr ⟨by simp only [step, ExpectedArgs.head], ?_⟩
              rw [hbefore, show frameCtx Frame.force (discharge (.VBuiltin b args (.one .argV)))
                    = .Force (discharge (.VBuiltin b args (.one .argV))) from by simp only [frameCtx]]
              have hnv : ¬ Value (.Force (discharge (.VBuiltin b args (.one .argV)))) := by
                intro hval; obtain ⟨b2, a2, r2, hsp2⟩ := value_force_inv hval
                obtain ⟨_, _, he⟩ := bspine_det hbsp hsp2; exact absurd he (by simp)
              have hn : Normal (.Force (discharge (.VBuiltin b args (.one .argV)))) := by
                rintro ⟨_, hst⟩
                rcases step_force_inv hst with ⟨M, hM⟩ | ⟨b2, a2, hsp2⟩ | hE | ⟨_, hst2⟩
                · rw [hM] at hbsp; cases hbsp
                · obtain ⟨_, _, he⟩ := bspine_det hbsp hsp2; exact absurd he (by simp)
                · rw [hE] at hbsp; cases hbsp
                · exact value_normal (.builtin hbsp) ⟨_, hst2⟩
              exact ⟨(dischargeStack_stuck hs hn hnv (by simp)).1, (dischargeStack_stuck hs hn hnv (by simp)).2.1⟩
          | more k rest =>
            cases k with
            | argQ =>
              refine Or.inl ?_
              rw [hbefore, show frameCtx Frame.force (discharge (.VBuiltin b args (.more .argQ rest)))
                    = .Force (discharge (.VBuiltin b args (.more .argQ rest))) from by simp only [frameCtx]]
              rw [show dischargeState (step (.ret (.force :: s) (.VBuiltin b args (.more .argQ rest))))
                    = dischargeStack s (discharge (.VBuiltin b args rest)) from by
                  simp only [step, ExpectedArgs.head, ExpectedArgs.tail, dischargeState]]
              rw [discharge_vbuiltin_force hsp]
              exact .refl
            | argV =>
              refine Or.inr ⟨by simp only [step, ExpectedArgs.head], ?_⟩
              rw [hbefore, show frameCtx Frame.force (discharge (.VBuiltin b args (.more .argV rest)))
                    = .Force (discharge (.VBuiltin b args (.more .argV rest))) from by simp only [frameCtx]]
              have hnv : ¬ Value (.Force (discharge (.VBuiltin b args (.more .argV rest)))) := by
                intro hval; obtain ⟨b2, a2, r2, hsp2⟩ := value_force_inv hval
                obtain ⟨_, _, he⟩ := bspine_det hbsp hsp2; exact absurd he (by simp)
              have hn : Normal (.Force (discharge (.VBuiltin b args (.more .argV rest)))) := by
                rintro ⟨_, hst⟩
                rcases step_force_inv hst with ⟨M, hM⟩ | ⟨b2, a2, hsp2⟩ | hE | ⟨_, hst2⟩
                · rw [hM] at hbsp; cases hbsp
                · obtain ⟨_, _, he⟩ := bspine_det hbsp hsp2; exact absurd he (by simp)
                · rw [hE] at hbsp; cases hbsp
                · exact value_normal (.builtin hbsp) ⟨_, hst2⟩
              exact ⟨(dischargeStack_stuck hs hn hnv (by simp)).1, (dischargeStack_stuck hs hn hnv (by simp)).2.1⟩
      | VCon c =>
        refine Or.inr ⟨by simp only [step], ?_⟩
        rw [hbefore]
        have hX : frameCtx Frame.force (discharge (.VCon c))
            = .Force (.Constant (c, Moist.Plutus.Term.constType c)) := by
          simp only [frameCtx, discharge]
        rw [hX]
        have hnv : ¬ Value (.Force (.Constant (c, Moist.Plutus.Term.constType c))) := by
          intro hval; obtain ⟨_, _, _, hsp2⟩ := value_force_inv hval; cases hsp2
        have hn : Normal (.Force (.Constant (c, Moist.Plutus.Term.constType c))) := by
          rintro ⟨_, hst⟩; cases hst with
          | satForce hsp2 => cases hsp2
          | congForce hst2 => cases hst2
        exact ⟨(dischargeStack_stuck hs hn hnv (by simp)).1, (dischargeStack_stuck hs hn hnv (by simp)).2.1⟩
      | VLam body ρ' =>
        refine Or.inr ⟨by simp only [step], ?_⟩
        rw [hbefore]
        rw [show frameCtx Frame.force (discharge (.VLam body ρ')) = .Force (.Lam 0 (dischargeEnv ρ' 1 body)) from by simp only [frameCtx, discharge]]
        have hnv : ¬ Value (.Force (.Lam 0 (dischargeEnv ρ' 1 body))) := by
          intro hval; obtain ⟨_, _, _, hsp2⟩ := value_force_inv hval; cases hsp2
        have hn : Normal (.Force (.Lam 0 (dischargeEnv ρ' 1 body))) := by
          rintro ⟨_, hst⟩; cases hst with
          | satForce hsp2 => cases hsp2
          | congForce hst2 => cases hst2
        exact ⟨(dischargeStack_stuck hs hn hnv (by simp)).1, (dischargeStack_stuck hs hn hnv (by simp)).2.1⟩
      | VConstr tag fields =>
        cases hv with
        | vconstr hfields =>
          refine Or.inr ⟨by simp only [step], ?_⟩
          rw [hbefore]
          rw [show frameCtx Frame.force (discharge (.VConstr tag fields)) = .Force (.Constr tag (dischargeList fields)) from by simp only [frameCtx, discharge]]
          have hvl : ValueList (dischargeList fields) := valueList_discharge (goodList_wf hfields)
          have hnv : ¬ Value (.Force (.Constr tag (dischargeList fields))) := by
            intro hval; obtain ⟨_, _, _, hsp2⟩ := value_force_inv hval; cases hsp2
          have hn : Normal (.Force (.Constr tag (dischargeList fields))) := by
            rintro ⟨_, hst⟩; cases hst with
            | satForce hsp2 => cases hsp2
            | congForce hst2 => exact value_normal (.constr hvl) ⟨_, hst2⟩
          exact ⟨(dischargeStack_stuck hs hn hnv (by simp)).1, (dischargeStack_stuck hs hn hnv (by simp)).2.1⟩
    | arg M ρ' =>
      refine Or.inl ?_
      rw [show dischargeState (step (.ret (.arg M ρ' :: s) v))
            = dischargeState (.ret (.arg M ρ' :: s) v) from by
        simp only [step, dischargeState, dischargeStack, frameCtx]]
      exact .refl
    | constrField tag done todo ρ' =>
      cases todo with
      | nil =>
        refine Or.inl ?_
        have hlist : List.map discharge (done.reverse ++ [v])
            = (List.map discharge done).reverse ++ [discharge v] := by
          simp [List.map_append, List.map_reverse]
        rw [show dischargeState (step (.ret (.constrField tag done [] ρ' :: s) v))
              = dischargeState (.ret (.constrField tag done [] ρ' :: s) v) from by
          simp only [step, dischargeState, dischargeStack, frameCtx, discharge,
            dischargeList_eq_map, List.reverse_cons, List.map_nil, hlist]]
        exact .refl
      | cons m ms =>
        refine Or.inl ?_
        rw [show dischargeState (step (.ret (.constrField tag done (m :: ms) ρ' :: s) v))
              = dischargeState (.ret (.constrField tag done (m :: ms) ρ' :: s) v) from by
          simp only [step, dischargeState, dischargeStack, frameCtx, dischargeList,
            List.reverse_cons, List.map_cons, List.append_assoc, List.cons_append, List.nil_append]]
        exact .refl
    | funV vf =>
      cases vf with
      | VLam body ρ' =>
        cases hf with
        | vlam _ heρ' =>
          refine Or.inl ?_
          rw [hbefore, show frameCtx (Frame.funV (.VLam body ρ')) (discharge v)
                = .Apply (.Lam 0 (dischargeEnv ρ' 1 body)) (discharge v) from by
              simp only [frameCtx, discharge]]
          rw [show dischargeState (step (.ret (.funV (.VLam body ρ') :: s) v))
                = dischargeStack s (dischargeEnv (ρ'.extend v) 0 body) from by
              simp only [step, dischargeState]]
          have hstep := @Step.betaLam 0 (dischargeEnv ρ' 1 body) (discharge v) (value_discharge (good_wf hv))
          rw [beta_discharge (good_discharge_closed hv) (goodEnv_envDischargeClosed heρ')] at hstep
          exact Steps.single (dischargeStack_cong hsw hstep)
      | VBuiltin b args ea =>
        cases hf with
        | vbuiltin hsp hargs =>
          have hbsp : BSpine (discharge (.VBuiltin b args ea)) b (dischargeList args).reverse ea :=
            bspine_discharge hsp (valueList_discharge (goodList_wf hargs))
          rw [hbefore, show frameCtx (Frame.funV (.VBuiltin b args ea)) (discharge v)
                = .Apply (discharge (.VBuiltin b args ea)) (discharge v) from by simp only [frameCtx]]
          cases ea with
          | one k => cases k with
            | argV =>
              refine Or.inl ?_
              have hres : dischargeResult (evalBuiltin b ((reflectList ((dischargeList args).reverse ++ [discharge v])).reverse)) = dischargeResult (evalBuiltin b (v :: args)) := by
                rw [reflectList_reverse_append]; exact evalBuiltin_rdv (.cons (good_wf hv) (goodList_wf hargs))
              have hstep := Step.satApply hbsp (value_discharge (good_wf hv))
              rw [hres] at hstep
              cases hev : evalBuiltin b (v :: args) with
              | some w =>
                rw [show dischargeState (step (.ret (.funV (.VBuiltin b args (.one .argV)) :: s) v)) = dischargeStack s (discharge w) from by simp only [step, ExpectedArgs.head, ExpectedArgs.tail, hev, dischargeState]]
                rw [hev] at hstep; simp only [dischargeResult] at hstep
                exact Steps.single (dischargeStack_cong hsw hstep)
              | none =>
                rw [show dischargeState (step (.ret (.funV (.VBuiltin b args (.one .argV)) :: s) v)) = .Error from by simp only [step, ExpectedArgs.head, ExpectedArgs.tail, hev, dischargeState]]
                rw [hev] at hstep; simp only [dischargeResult] at hstep
                exact Steps.trans (Steps.single (dischargeStack_cong hsw hstep)) (dischargeStack_error hsw)
            | argQ =>
              refine Or.inr ⟨by simp only [step, ExpectedArgs.head], ?_⟩
              have hst3 := apply_fn_stuck (Value.builtin hbsp) (value_discharge (good_wf hv))
                (by intro x M hfe; rw [hfe] at hbsp; cases hbsp)
                (by intro b' a' hsp'; obtain ⟨_, _, he⟩ := bspine_det hbsp hsp'; exact absurd he (by simp))
                (by intro b' a' r' hsp'; obtain ⟨_, _, he⟩ := bspine_det hbsp hsp'; exact absurd he (by simp))
              exact ⟨(dischargeStack_stuck hs hst3.1 hst3.2.1 hst3.2.2).1, (dischargeStack_stuck hs hst3.1 hst3.2.1 hst3.2.2).2.1⟩
          | more k rest => cases k with
            | argV =>
              refine Or.inl ?_
              rw [show dischargeState (step (.ret (.funV (.VBuiltin b args (.more .argV rest)) :: s) v)) = dischargeStack s (discharge (.VBuiltin b (v :: args) rest)) from by simp only [step, ExpectedArgs.head, ExpectedArgs.tail, dischargeState]]
              rw [discharge_vbuiltin_app hsp]
              exact .refl
            | argQ =>
              refine Or.inr ⟨by simp only [step, ExpectedArgs.head], ?_⟩
              have hst3 := apply_fn_stuck (Value.builtin hbsp) (value_discharge (good_wf hv))
                (by intro x M hfe; rw [hfe] at hbsp; cases hbsp)
                (by intro b' a' hsp'; obtain ⟨_, _, he⟩ := bspine_det hbsp hsp'; exact absurd he (by simp))
                (by intro b' a' r' hsp'; obtain ⟨_, _, he⟩ := bspine_det hbsp hsp'; exact absurd he (by simp))
              exact ⟨(dischargeStack_stuck hs hst3.1 hst3.2.1 hst3.2.2).1, (dischargeStack_stuck hs hst3.1 hst3.2.1 hst3.2.2).2.1⟩
      | VCon c =>
        refine Or.inr ⟨by simp only [step], ?_⟩
        rw [hbefore, show frameCtx (Frame.funV (.VCon c)) (discharge v) = .Apply (.Constant (c, Moist.Plutus.Term.constType c)) (discharge v) from by simp only [frameCtx, discharge]]
        have hst3 := apply_fn_stuck (fn := .Constant (c, Moist.Plutus.Term.constType c)) .constant (value_discharge (good_wf hv))
          (by intro x M; simp) (by intro b' a' hsp'; cases hsp') (by intro b' a' r' hsp'; cases hsp')
        exact ⟨(dischargeStack_stuck hs hst3.1 hst3.2.1 hst3.2.2).1, (dischargeStack_stuck hs hst3.1 hst3.2.1 hst3.2.2).2.1⟩
      | VDelay body ρ' =>
        refine Or.inr ⟨by simp only [step], ?_⟩
        rw [hbefore, show frameCtx (Frame.funV (.VDelay body ρ')) (discharge v) = .Apply (.Delay (dischargeEnv ρ' 0 body)) (discharge v) from by simp only [frameCtx, discharge]]
        have hst3 := apply_fn_stuck (fn := .Delay (dischargeEnv ρ' 0 body)) .delay (value_discharge (good_wf hv))
          (by intro x M; simp) (by intro b' a' hsp'; cases hsp') (by intro b' a' r' hsp'; cases hsp')
        exact ⟨(dischargeStack_stuck hs hst3.1 hst3.2.1 hst3.2.2).1, (dischargeStack_stuck hs hst3.1 hst3.2.1 hst3.2.2).2.1⟩
      | VConstr tag fields =>
        cases hf with
        | vconstr hfields =>
          refine Or.inr ⟨by simp only [step], ?_⟩
          rw [hbefore, show frameCtx (Frame.funV (.VConstr tag fields)) (discharge v) = .Apply (.Constr tag (dischargeList fields)) (discharge v) from by simp only [frameCtx, discharge]]
          have hst3 := apply_fn_stuck (fn := .Constr tag (dischargeList fields)) (.constr (valueList_discharge (goodList_wf hfields))) (value_discharge (good_wf hv))
            (by intro x M; simp) (by intro b' a' hsp'; cases hsp') (by intro b' a' r' hsp'; cases hsp')
          exact ⟨(dischargeStack_stuck hs hst3.1 hst3.2.1 hst3.2.2).1, (dischargeStack_stuck hs hst3.1 hst3.2.1 hst3.2.2).2.1⟩
    | applyArg vx =>
      cases v with
      | VLam body ρ' =>
        cases hv with
        | vlam _ heρ' =>
          refine Or.inl ?_
          rw [hbefore, show frameCtx (Frame.applyArg vx) (discharge (.VLam body ρ'))
                = .Apply (.Lam 0 (dischargeEnv ρ' 1 body)) (discharge vx) from by simp only [frameCtx, discharge]]
          rw [show dischargeState (step (.ret (.applyArg vx :: s) (.VLam body ρ')))
                = dischargeStack s (dischargeEnv (ρ'.extend vx) 0 body) from by simp only [step, dischargeState]]
          have hstep := @Step.betaLam 0 (dischargeEnv ρ' 1 body) (discharge vx) (value_discharge (good_wf hf))
          rw [beta_discharge (good_discharge_closed hf) (goodEnv_envDischargeClosed heρ')] at hstep
          exact Steps.single (dischargeStack_cong hsw hstep)
      | VBuiltin b args ea =>
        cases hv with
        | vbuiltin hsp hargs =>
          have hbsp : BSpine (discharge (.VBuiltin b args ea)) b (dischargeList args).reverse ea :=
            bspine_discharge hsp (valueList_discharge (goodList_wf hargs))
          rw [hbefore, show frameCtx (Frame.applyArg vx) (discharge (.VBuiltin b args ea))
                = .Apply (discharge (.VBuiltin b args ea)) (discharge vx) from by simp only [frameCtx]]
          cases ea with
          | one k => cases k with
            | argV =>
              refine Or.inl ?_
              have hres : dischargeResult (evalBuiltin b ((reflectList ((dischargeList args).reverse ++ [discharge vx])).reverse)) = dischargeResult (evalBuiltin b (vx :: args)) := by
                rw [reflectList_reverse_append]; exact evalBuiltin_rdv (.cons (good_wf hf) (goodList_wf hargs))
              have hstep := Step.satApply hbsp (value_discharge (good_wf hf))
              rw [hres] at hstep
              cases hev : evalBuiltin b (vx :: args) with
              | some w =>
                rw [show dischargeState (step (.ret (.applyArg vx :: s) (.VBuiltin b args (.one .argV)))) = dischargeStack s (discharge w) from by simp only [step, ExpectedArgs.head, ExpectedArgs.tail, hev, dischargeState]]
                rw [hev] at hstep; simp only [dischargeResult] at hstep
                exact Steps.single (dischargeStack_cong hsw hstep)
              | none =>
                rw [show dischargeState (step (.ret (.applyArg vx :: s) (.VBuiltin b args (.one .argV)))) = .Error from by simp only [step, ExpectedArgs.head, ExpectedArgs.tail, hev, dischargeState]]
                rw [hev] at hstep; simp only [dischargeResult] at hstep
                exact Steps.trans (Steps.single (dischargeStack_cong hsw hstep)) (dischargeStack_error hsw)
            | argQ =>
              refine Or.inr ⟨by simp only [step, ExpectedArgs.head], ?_⟩
              have hst3 := apply_fn_stuck (Value.builtin hbsp) (value_discharge (good_wf hf))
                (by intro x M hfe; rw [hfe] at hbsp; cases hbsp)
                (by intro b' a' hsp'; obtain ⟨_, _, he⟩ := bspine_det hbsp hsp'; exact absurd he (by simp))
                (by intro b' a' r' hsp'; obtain ⟨_, _, he⟩ := bspine_det hbsp hsp'; exact absurd he (by simp))
              exact ⟨(dischargeStack_stuck hs hst3.1 hst3.2.1 hst3.2.2).1, (dischargeStack_stuck hs hst3.1 hst3.2.1 hst3.2.2).2.1⟩
          | more k rest => cases k with
            | argV =>
              refine Or.inl ?_
              rw [show dischargeState (step (.ret (.applyArg vx :: s) (.VBuiltin b args (.more .argV rest)))) = dischargeStack s (discharge (.VBuiltin b (vx :: args) rest)) from by simp only [step, ExpectedArgs.head, ExpectedArgs.tail, dischargeState]]
              rw [discharge_vbuiltin_app hsp]
              exact .refl
            | argQ =>
              refine Or.inr ⟨by simp only [step, ExpectedArgs.head], ?_⟩
              have hst3 := apply_fn_stuck (Value.builtin hbsp) (value_discharge (good_wf hf))
                (by intro x M hfe; rw [hfe] at hbsp; cases hbsp)
                (by intro b' a' hsp'; obtain ⟨_, _, he⟩ := bspine_det hbsp hsp'; exact absurd he (by simp))
                (by intro b' a' r' hsp'; obtain ⟨_, _, he⟩ := bspine_det hbsp hsp'; exact absurd he (by simp))
              exact ⟨(dischargeStack_stuck hs hst3.1 hst3.2.1 hst3.2.2).1, (dischargeStack_stuck hs hst3.1 hst3.2.1 hst3.2.2).2.1⟩
      | VCon c =>
        refine Or.inr ⟨by simp only [step], ?_⟩
        rw [hbefore, show frameCtx (Frame.applyArg vx) (discharge (.VCon c)) = .Apply (.Constant (c, Moist.Plutus.Term.constType c)) (discharge vx) from by simp only [frameCtx, discharge]]
        have hst3 := apply_fn_stuck (fn := .Constant (c, Moist.Plutus.Term.constType c)) .constant (value_discharge (good_wf hf))
          (by intro x M; simp) (by intro b' a' hsp'; cases hsp') (by intro b' a' r' hsp'; cases hsp')
        exact ⟨(dischargeStack_stuck hs hst3.1 hst3.2.1 hst3.2.2).1, (dischargeStack_stuck hs hst3.1 hst3.2.1 hst3.2.2).2.1⟩
      | VDelay body ρ' =>
        refine Or.inr ⟨by simp only [step], ?_⟩
        rw [hbefore, show frameCtx (Frame.applyArg vx) (discharge (.VDelay body ρ')) = .Apply (.Delay (dischargeEnv ρ' 0 body)) (discharge vx) from by simp only [frameCtx, discharge]]
        have hst3 := apply_fn_stuck (fn := .Delay (dischargeEnv ρ' 0 body)) .delay (value_discharge (good_wf hf))
          (by intro x M; simp) (by intro b' a' hsp'; cases hsp') (by intro b' a' r' hsp'; cases hsp')
        exact ⟨(dischargeStack_stuck hs hst3.1 hst3.2.1 hst3.2.2).1, (dischargeStack_stuck hs hst3.1 hst3.2.1 hst3.2.2).2.1⟩
      | VConstr tag fields =>
        cases hv with
        | vconstr hfields =>
          refine Or.inr ⟨by simp only [step], ?_⟩
          rw [hbefore, show frameCtx (Frame.applyArg vx) (discharge (.VConstr tag fields)) = .Apply (.Constr tag (dischargeList fields)) (discharge vx) from by simp only [frameCtx, discharge]]
          have hst3 := apply_fn_stuck (fn := .Constr tag (dischargeList fields)) (.constr (valueList_discharge (goodList_wf hfields))) (value_discharge (good_wf hf))
            (by intro x M; simp) (by intro b' a' hsp'; cases hsp') (by intro b' a' r' hsp'; cases hsp')
          exact ⟨(dischargeStack_stuck hs hst3.1 hst3.2.1 hst3.2.2).1, (dischargeStack_stuck hs hst3.1 hst3.2.1 hst3.2.2).2.1⟩
    | caseScrutinee alts ρ' =>
      obtain ⟨halts, heρ'⟩ := hf
      cases v with
      | VConstr tag fields =>
        cases hv with
        | vconstr hfields =>
          have hvl : ValueList (dischargeList fields) := valueList_discharge (goodList_wf hfields)
          rw [hbefore, show frameCtx (Frame.caseScrutinee alts ρ') (discharge (.VConstr tag fields))
                = .Case (.Constr tag (dischargeList fields)) (alts.map (dischargeEnv ρ' 0 ·)) from by
              simp only [frameCtx, discharge]]
          cases halt : alts[tag]? with
          | some alt =>
            refine Or.inl ?_
            have hmap : (alts.map (dischargeEnv ρ' 0 ·))[tag]? = some (dischargeEnv ρ' 0 alt) := by
              rw [List.getElem?_map, halt]; rfl
            rw [show dischargeState (step (.ret (.caseScrutinee alts ρ' :: s) (.VConstr tag fields)))
                  = dischargeStack s (mkApps (dischargeEnv ρ' 0 alt) (dischargeList fields)) from by
                simp only [step, halt, dischargeState, dischargeStack_append, dischargeStack_applyArgFrames]]
            exact Steps.single (dischargeStack_cong hsw (Step.caseConstr hvl hmap))
          | none =>
            refine Or.inr ⟨by simp only [step, halt], ?_⟩
            have hmap : (alts.map (dischargeEnv ρ' 0 ·))[tag]? = none := by rw [List.getElem?_map, halt]; rfl
            have hn : Normal (.Case (.Constr tag (dischargeList fields)) (alts.map (dischargeEnv ρ' 0 ·))) := by
              rintro ⟨_, hst⟩
              cases hst with
              | caseConstr _ halt2 => rw [hmap] at halt2; cases halt2
              | congCase hst2 => exact value_normal (.constr hvl) ⟨_, hst2⟩
            exact ⟨(dischargeStack_stuck hs hn not_value_case (by simp)).1,
              (dischargeStack_stuck hs hn not_value_case (by simp)).2.1⟩
      | VCon c =>
        rw [hbefore, show frameCtx (Frame.caseScrutinee alts ρ') (discharge (.VCon c))
              = .Case (.Constant (c, Moist.Plutus.Term.constType c)) (alts.map (dischargeEnv ρ' 0 ·)) from by
            simp only [frameCtx, discharge]]
        rcases hcf : constToTagAndFields c with _ | ⟨tag, numCtors, fields⟩
        · refine Or.inr ⟨by simp only [step, hcf], ?_⟩
          have hn : Normal (.Case (.Constant (c, Moist.Plutus.Term.constType c)) (alts.map (dischargeEnv ρ' 0 ·))) := by
            rintro ⟨_, hst⟩
            cases hst with
            | caseConst hc2 _ _ => rw [hcf] at hc2; cases hc2
            | congCase hst2 => exact value_normal .constant ⟨_, hst2⟩
          exact ⟨(dischargeStack_stuck hs hn not_value_case (by simp)).1,
            (dischargeStack_stuck hs hn not_value_case (by simp)).2.1⟩
        · have hfgood := constToTagAndFields_fields_good hcf
          have hvl : ValueList (dischargeList fields) := valueList_discharge (goodList_wf hfgood)
          by_cases hchk : (numCtors > 0 && alts.length > numCtors) = true
          · refine Or.inr ⟨by simp only [step, hcf]; rw [if_pos hchk], ?_⟩
            have hchk' : numCtors > 0 ∧ alts.length > numCtors := by
              simpa [Bool.and_eq_true, decide_eq_true_eq] using hchk
            have hn : Normal (.Case (.Constant (c, Moist.Plutus.Term.constType c)) (alts.map (dischargeEnv ρ' 0 ·))) := by
              rintro ⟨_, hst⟩
              cases hst with
              | caseConst hc2 hchk2 _ =>
                rw [hcf] at hc2; obtain ⟨rfl, rfl, rfl⟩ := by simpa using hc2
                exact hchk2 (by rw [List.length_map]; exact hchk')
              | congCase hst2 => exact value_normal .constant ⟨_, hst2⟩
            exact ⟨(dischargeStack_stuck hs hn not_value_case (by simp)).1,
              (dischargeStack_stuck hs hn not_value_case (by simp)).2.1⟩
          · have hchk' : ¬ (numCtors > 0 ∧ alts.length > numCtors) := by
              simpa [Bool.and_eq_true, decide_eq_true_eq] using hchk
            cases halt : alts[tag]? with
            | some alt =>
              refine Or.inl ?_
              have hmap : (alts.map (dischargeEnv ρ' 0 ·))[tag]? = some (dischargeEnv ρ' 0 alt) := by
                rw [List.getElem?_map, halt]; rfl
              rw [show dischargeState (step (.ret (.caseScrutinee alts ρ' :: s) (.VCon c)))
                    = dischargeStack s (mkApps (dischargeEnv ρ' 0 alt) (dischargeList fields)) from by
                  simp only [step, hcf]; rw [if_neg hchk]
                  simp only [halt, dischargeState, dischargeStack_append, dischargeStack_applyArgFrames]]
              have hcaseconst := @Step.caseConst c (Moist.Plutus.Term.constType c) tag numCtors fields
                (alts.map (dischargeEnv ρ' 0 ·)) (dischargeEnv ρ' 0 alt) hcf
                (by rw [List.length_map]; exact hchk') hmap
              rw [show List.map discharge fields = dischargeList fields from (dischargeList_eq_map fields).symm] at hcaseconst
              exact Steps.single (dischargeStack_cong hsw hcaseconst)
            | none =>
              refine Or.inr ⟨by simp only [step, hcf]; rw [if_neg hchk]; simp only [halt], ?_⟩
              have hmap : (alts.map (dischargeEnv ρ' 0 ·))[tag]? = none := by rw [List.getElem?_map, halt]; rfl
              have hn : Normal (.Case (.Constant (c, Moist.Plutus.Term.constType c)) (alts.map (dischargeEnv ρ' 0 ·))) := by
                rintro ⟨_, hst⟩
                cases hst with
                | caseConst hc2 _ halt2 =>
                  rw [hcf] at hc2; obtain ⟨rfl, rfl, rfl⟩ := by simpa using hc2
                  rw [hmap] at halt2; cases halt2
                | congCase hst2 => exact value_normal .constant ⟨_, hst2⟩
              exact ⟨(dischargeStack_stuck hs hn not_value_case (by simp)).1,
                (dischargeStack_stuck hs hn not_value_case (by simp)).2.1⟩
      | VLam body ρ'' =>
        refine Or.inr ⟨by simp only [step], ?_⟩
        rw [hbefore, show frameCtx (Frame.caseScrutinee alts ρ') (discharge (.VLam body ρ''))
              = .Case (.Lam 0 (dischargeEnv ρ'' 1 body)) (alts.map (dischargeEnv ρ' 0 ·)) from by
            simp only [frameCtx, discharge]]
        have hst3 := case_scrut_stuck (scrut := .Lam 0 (dischargeEnv ρ'' 1 body))
          (alts := alts.map (dischargeEnv ρ' 0 ·)) Value.lam (by simp) (by simp)
        exact ⟨(dischargeStack_stuck hs hst3.1 hst3.2.1 hst3.2.2).1,
          (dischargeStack_stuck hs hst3.1 hst3.2.1 hst3.2.2).2.1⟩
      | VDelay body ρ'' =>
        refine Or.inr ⟨by simp only [step], ?_⟩
        rw [hbefore, show frameCtx (Frame.caseScrutinee alts ρ') (discharge (.VDelay body ρ''))
              = .Case (.Delay (dischargeEnv ρ'' 0 body)) (alts.map (dischargeEnv ρ' 0 ·)) from by
            simp only [frameCtx, discharge]]
        have hst3 := case_scrut_stuck (scrut := .Delay (dischargeEnv ρ'' 0 body))
          (alts := alts.map (dischargeEnv ρ' 0 ·)) Value.delay (by simp) (by simp)
        exact ⟨(dischargeStack_stuck hs hst3.1 hst3.2.1 hst3.2.2).1,
          (dischargeStack_stuck hs hst3.1 hst3.2.1 hst3.2.2).2.1⟩
      | VBuiltin b args ea =>
        cases hv with
        | vbuiltin hsp hargs =>
          have hbsp : BSpine (discharge (.VBuiltin b args ea)) b (dischargeList args).reverse ea :=
            bspine_discharge hsp (valueList_discharge (goodList_wf hargs))
          refine Or.inr ⟨by simp only [step], ?_⟩
          rw [hbefore, show frameCtx (Frame.caseScrutinee alts ρ') (discharge (.VBuiltin b args ea))
                = .Case (discharge (.VBuiltin b args ea)) (alts.map (dischargeEnv ρ' 0 ·)) from by
              simp only [frameCtx]]
          have hst3 := case_scrut_stuck (alts := alts.map (dischargeEnv ρ' 0 ·)) (Value.builtin hbsp)
            (by intro i vs he; rw [he] at hbsp; cases hbsp)
            (by intro cb he; rw [he] at hbsp; cases hbsp)
          exact ⟨(dischargeStack_stuck hs hst3.1 hst3.2.1 hst3.2.2).1,
            (dischargeStack_stuck hs hst3.1 hst3.2.1 hst3.2.2).2.1⟩


/-! ## The forward simulation -/

/-- **Forward simulation.** For a well-formed, canonical CEK state, the discharged
    term either reduces (in 0, 1, or several small steps) to the discharge of the
    next state, or the machine is about to `error` from a genuinely stuck
    configuration whose discharge is a stuck normal form. -/
theorem sim_step (s : State) (hg : GoodState s) (hc : CanonState s) :
    Steps (dischargeState s) (dischargeState (step s))
    ∨ (step s = .error ∧ Stuck (dischargeState s)) := by
  cases s with
  | compute π ρ M => exact sim_step_compute π ρ M hg hc
  | ret π v => exact sim_step_ret π v hg hc
  | halt v => exact Or.inl Steps.refl
  | error => exact Or.inl Steps.refl

end Moist.Verified.SmallStep
