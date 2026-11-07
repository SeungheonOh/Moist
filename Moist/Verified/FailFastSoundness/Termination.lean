import Moist.Verified.FailFastSoundness.Sink
import Moist.Verified.ShapeFacts.Known
import Moist.MIR.Optimize.Advanced.FailFast

/-! # Soundness of the termination analysis

`terminates e` implies that the lowering of `e` halts or errors in every
well-formed environment; `inert e` additionally guarantees that a returned
value is a constant or a constructor; `altSafe a` guarantees termination of
a case alternative applied to any number of fields; and `spineHead e`
tracks how many arguments of the head builtin a spine has consumed.
-/

namespace Moist.Verified.FailFast

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts

/-! ## Terminating states -/

def TermState (s : State) : Prop := Reaches s .error ∨ ∃ v, Reaches s (.halt v)

theorem termState_of_reaches {s s' : State} (h : Reaches s s') (h' : TermState s') : TermState s := by
  rcases h' with h' | ⟨v, h'⟩
  · exact .inl (reaches_trans h h')
  · exact .inr ⟨v, reaches_trans h h'⟩

theorem termState_error : TermState .error := .inl (reaches_refl _)

theorem termState_halt (v : CekValue) : TermState (.halt v) := .inr ⟨v, reaches_refl _⟩

theorem termState_ret_nil (v : CekValue) : TermState (.ret [] v) :=
  .inr ⟨v, reaches_of_steps 1 rfl⟩

/-- Evaluate `t`, then continue on the stack. -/
theorem termState_compute {π : Stack} {ρ : CekEnv} {t : Term}
    (ht : Errs ρ t ∨ ∃ v, Halts ρ t v) (hk : ∀ v, Halts ρ t v → TermState (.ret π v)) :
    TermState (.compute π ρ t) := by
  rcases ht with he | ⟨v, hv⟩
  · exact .inl (errs_on_stack he π)
  · exact termState_of_reaches (halts_on_stack hv π) (hk v hv)

theorem terminatesAt_of_termState {d : Nat} {t : Term}
    (h : ∀ ρ, EnvWellFormed d ρ → d ≤ ρ.length → TermState (.compute [] ρ t)) : TerminatesAt d t := by
  intro ρ henv hlen
  rcases h ρ henv hlen with he | hv
  · exact .inl he
  · exact .inr hv

/-! ## Inert values and the semantic predicates -/

def InertV : CekValue → Prop
  | .VCon _ => True
  | .VConstr _ _ => True
  | _ => False

def InertAt (d : Nat) (t : Term) : Prop :=
  ∀ ρ, EnvWellFormed d ρ → d ≤ ρ.length → Errs ρ t ∨ ∃ v, Halts ρ t v ∧ InertV v

def AltSafeAt (d : Nat) (t : Term) : Prop :=
  ∀ ρ, EnvWellFormed d ρ → d ≤ ρ.length → ∀ fields, ValueListWellFormed fields →
    TermState (.compute (fields.map Frame.applyArg) ρ t)

def SpineAt (d : Nat) (b : BuiltinFun) (n : Nat) (t : Term) : Prop :=
  ∀ ρ, EnvWellFormed d ρ → d ≤ ρ.length → Errs ρ t ∨ ∃ v, Halts ρ t v ∧
    (n < builtinArity b → ∃ args ea, v = .VBuiltin b args ea ∧ argCount ea + n = builtinArity b) ∧
    (n = builtinArity b → ∃ args, evalBuiltin b args = some v)

theorem InertAt.terminates {d : Nat} {t : Term} (h : InertAt d t) : TerminatesAt d t := by
  intro ρ henv hlen
  rcases h ρ henv hlen with he | ⟨v, hv, _⟩
  · exact .inl he
  · exact .inr ⟨v, hv⟩

theorem argCount_pos (ea : ExpectedArgs) : 0 < argCount ea := by
  cases ea <;> simp [argCount]

/-- Applying an inert value errors. -/
theorem inert_apply_errors {v : CekValue} (hv : InertV v) (f : CekValue) (π : Stack) :
    step (.ret (.applyArg f :: π) v) = .error := by
  cases v <;> simp_all [InertV, step]

/-- An inert result on the field-application stack terminates. -/
theorem termState_inert_fields {v : CekValue} (hv : InertV v) :
    ∀ (fields : List CekValue), TermState (.ret (fields.map Frame.applyArg) v)
  | [] => termState_ret_nil v
  | f :: _ => .inl (reaches_of_steps 1 (inert_apply_errors hv f _))

/-! ## Dispatch facts -/

theorem constToTagAndFields_wellFormed {c : Const} {tag numCtors : Nat} {fields : List CekValue}
    (h : constToTagAndFields c = some (tag, numCtors, fields)) : ValueListWellFormed fields := by
  have hvcon := constToTagAndFields_fields_vcon c
  rw [h] at hvcon
  simp only at hvcon
  clear h
  induction fields with
  | nil => exact .nil
  | cons f fs ih =>
    simp only [List.mem_cons] at hvcon
    obtain ⟨c', hc'⟩ := hvcon f (.inl rfl)
    subst hc'
    exact .cons (.vcon c') (ih fun v hv => hvcon v (.inr hv))

theorem dispatch_spec {alts : List Term} {v : CekValue} {alt : Term} {fields : List CekValue}
    (h : dispatch alts v = some (alt, fields)) (hv : ValueWellFormed v) :
    alt ∈ alts ∧ ValueListWellFormed fields := by
  cases v with
  | VConstr tag fs =>
    simp only [dispatch] at h
    cases hl : alts[tag]? with
    | none => rw [hl] at h; cases h
    | some a =>
      rw [hl] at h; cases h
      cases hv with
      | vconstr _ hfs => exact ⟨List.mem_of_getElem? hl, hfs⟩
  | VCon c =>
    simp only [dispatch] at h
    cases hc : constToTagAndFields c with
    | none => rw [hc] at h; cases h
    | some r =>
      obtain ⟨tag, numCtors, fs⟩ := r
      rw [hc] at h
      simp only at h
      split at h
      · cases h
      · cases hl : alts[tag]? with
        | none => rw [hl] at h; cases h
        | some a =>
          rw [hl] at h; cases h
          exact ⟨List.mem_of_getElem? hl, constToTagAndFields_wellFormed hc⟩
  | VLam _ _ => cases h
  | VDelay _ _ => cases h
  | VBuiltin _ _ _ => cases h

/-! ## Single CEK nodes -/

theorem halts_var_wf {d : Nat} {ρ : CekEnv} (henv : EnvWellFormed d ρ) {i : Nat} (hi : i < d) :
    ∃ v, Halts ρ (.Var (i + 1)) v := by
  obtain ⟨v, hl, _⟩ := envWellFormed_lookup d henv (n := i + 1) (by omega) (by omega)
  exact ⟨v, halts_var_of_lookup hl⟩

theorem envLookupT_lt {env : List VarId} {x : VarId} {i : Nat} (h : envLookupT env x = some i) :
    i < env.length := by
  have := envLookupT_bound env x i h
  omega

theorem envWellFormed_extend' {d : Nat} {ρ : CekEnv} {v : CekValue} (henv : EnvWellFormed d ρ)
    (hlen : d ≤ ρ.length) (hv : ValueWellFormed v) :
    EnvWellFormed (d + 1) (ρ.extend v) ∧ d + 1 ≤ (ρ.extend v).length :=
  ⟨envWellFormed_extend d henv hlen hv, by simp [CekEnv.extend, CekEnv.length]; omega⟩

/-- Constructor fields evaluated left to right. -/
theorem termState_constrField {d : Nat} {ρ : CekEnv} (henv : EnvWellFormed d ρ) (hlen : d ≤ ρ.length)
    (tag : Nat) : ∀ (ms : List Term) (m : Term) (done : List CekValue),
      TerminatesAt d m → (∀ t ∈ ms, TerminatesAt d t) →
      TermState (.compute [.constrField tag done ms ρ] ρ m)
  | [], _, _, hm, _ =>
    termState_compute (hm ρ henv hlen) fun _ _ =>
      termState_of_reaches (reaches_of_steps 1 rfl) (termState_ret_nil _)
  | m' :: ms, _, done, hm, hms =>
    termState_compute (hm ρ henv hlen) fun v _ =>
      termState_of_reaches (reaches_of_steps 1 rfl)
        (termState_constrField henv hlen tag ms m' (v :: done) (hms m' (.head _))
          fun t ht => hms t (.tail _ ht))

theorem halts_constrField_inert {ρ : CekEnv} {tag : Nat} {ms : List Term} {m : Term}
    {done : List CekValue} {u : CekValue}
    (h : Reaches (.compute [.constrField tag done ms ρ] ρ m) (.halt u)) : InertV u := by
  induction ms generalizing m done with
  | nil =>
    rcases sequence (.inr ⟨u, rfl⟩) h with ⟨_, he⟩ | ⟨v, _, hrest⟩
    · cases he
    · have : Reaches (.ret [.constrField tag done [] ρ] v) (.halt (.VConstr tag (v :: done).reverse)) :=
        reaches_of_steps 2 rfl
      cases terminal_unique (.inr ⟨_, rfl⟩) (.inr ⟨_, rfl⟩) this hrest
      trivial
  | cons m' ms ih =>
    rcases sequence (.inr ⟨u, rfl⟩) h with ⟨_, he⟩ | ⟨v, _, hrest⟩
    · cases he
    · have h1 : Reaches (.ret [.constrField tag done (m' :: ms) ρ] v)
          (.compute [.constrField tag (v :: done) ms ρ] ρ m') := reaches_of_steps 1 rfl
      exact ih (reaches_terminal_after (.inr ⟨u, rfl⟩) h1 hrest)

/-! ## Builtin spines -/

theorem spineAt_builtin (d : Nat) (b : BuiltinFun) : SpineAt d b 0 (.Builtin b) := by
  intro ρ _ _
  refine .inr ⟨_, reaches_of_steps 2 rfl, fun _ => ⟨[], expectedArgs b, rfl, by simp [builtinArity]⟩,
    fun h => ?_⟩
  have := argCount_pos (expectedArgs b)
  simp only [builtinArity] at h
  omega

/-- One more value argument for a builtin state. -/
theorem builtin_value_step {b : BuiltinFun} {args : List CekValue} {ea : ExpectedArgs} {n : Nat}
    {va : CekValue} (hcount : argCount ea + n = builtinArity b) :
    Reaches (.ret [.funV (.VBuiltin b args ea)] va) .error ∨ ∃ v,
      Reaches (.ret [.funV (.VBuiltin b args ea)] va) (.halt v) ∧
      (n + 1 < builtinArity b → ∃ args ea', v = .VBuiltin b args ea' ∧
        argCount ea' + (n + 1) = builtinArity b) ∧
      (n + 1 = builtinArity b → ∃ args, evalBuiltin b args = some v) := by
  cases ea with
  | one k =>
    cases k with
    | argQ => exact .inl (reaches_of_steps 1 rfl)
    | argV =>
      simp only [argCount] at hcount
      cases hev : evalBuiltin b (va :: args) with
      | none => exact .inl (reaches_of_steps 1 (by simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, hev]))
      | some v =>
        refine .inr ⟨v, reaches_of_steps 2 (by simp [steps, step, ExpectedArgs.head,
          ExpectedArgs.tail, hev]), fun h => absurd h (by omega), fun _ => ⟨_, hev⟩⟩
  | more k rest =>
    cases k with
    | argQ => exact .inl (reaches_of_steps 1 rfl)
    | argV =>
      simp only [argCount] at hcount
      refine .inr ⟨_, reaches_of_steps 2 rfl, fun _ => ⟨_, rest, rfl, by omega⟩,
        fun h => absurd h (by have := argCount_pos rest; omega)⟩

/-- One more type force for a builtin state. -/
theorem builtin_force_step {b : BuiltinFun} {args : List CekValue} {ea : ExpectedArgs} {n : Nat}
    (hcount : argCount ea + n = builtinArity b) :
    Reaches (.ret [.force] (.VBuiltin b args ea)) .error ∨ ∃ v,
      Reaches (.ret [.force] (.VBuiltin b args ea)) (.halt v) ∧
      (n + 1 < builtinArity b → ∃ args ea', v = .VBuiltin b args ea' ∧
        argCount ea' + (n + 1) = builtinArity b) ∧
      (n + 1 = builtinArity b → ∃ args, evalBuiltin b args = some v) := by
  cases ea with
  | one k =>
    cases k with
    | argV => exact .inl (reaches_of_steps 1 rfl)
    | argQ =>
      simp only [argCount] at hcount
      cases hev : evalBuiltin b args with
      | none => exact .inl (reaches_of_steps 1 (by simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, hev]))
      | some v =>
        refine .inr ⟨v, reaches_of_steps 2 (by simp [steps, step, ExpectedArgs.head,
          ExpectedArgs.tail, hev]), fun h => absurd h (by omega), fun _ => ⟨_, hev⟩⟩
  | more k rest =>
    cases k with
    | argV => exact .inl (reaches_of_steps 1 rfl)
    | argQ =>
      simp only [argCount] at hcount
      refine .inr ⟨_, reaches_of_steps 2 rfl, fun _ => ⟨_, rest, rfl, by omega⟩,
        fun h => absurd h (by have := argCount_pos rest; omega)⟩

theorem spineAt_apply {d : Nat} {b : BuiltinFun} {n : Nat} {tf ta : Term}
    (hn : n + 1 ≤ builtinArity b) (hf : SpineAt d b n tf) (ha : TerminatesAt d ta) :
    SpineAt d b (n + 1) (.Apply tf ta) := by
  intro ρ henv hlen
  have h1 : Reaches (.compute [] ρ (.Apply tf ta)) (.compute [.arg ta ρ] ρ tf) := reaches_of_steps 1 rfl
  rcases hf ρ henv hlen with he | ⟨vf, hvf, hlt, _⟩
  · exact .inl (reaches_trans h1 (errs_on_stack he _))
  obtain ⟨args, ea, rfl, hcount⟩ := hlt (by omega)
  have h2 : Reaches (.compute [] ρ (.Apply tf ta)) (.compute [.funV (.VBuiltin b args ea)] ρ ta) :=
    reaches_trans h1 (reaches_trans (halts_on_stack hvf _) (reaches_of_steps 1 rfl))
  rcases ha ρ henv hlen with he | ⟨va, hva⟩
  · exact .inl (reaches_trans h2 (errs_on_stack he _))
  have h3 := reaches_trans h2 (halts_on_stack hva _)
  rcases builtin_value_step (va := va) hcount with he | ⟨v, hv, hp⟩
  · exact .inl (reaches_trans h3 he)
  · exact .inr ⟨v, reaches_trans h3 hv, hp⟩

theorem spineAt_force {d : Nat} {b : BuiltinFun} {n : Nat} {t : Term}
    (hn : n + 1 ≤ builtinArity b) (hf : SpineAt d b n t) : SpineAt d b (n + 1) (.Force t) := by
  intro ρ henv hlen
  have h1 : Reaches (.compute [] ρ (.Force t)) (.compute [.force] ρ t) := reaches_of_steps 1 rfl
  rcases hf ρ henv hlen with he | ⟨vf, hvf, hlt, _⟩
  · exact .inl (reaches_trans h1 (errs_on_stack he _))
  obtain ⟨args, ea, rfl, hcount⟩ := hlt (by omega)
  have h2 := reaches_trans h1 (halts_on_stack hvf _)
  rcases builtin_force_step (args := args) hcount with he | ⟨v, hv, hp⟩
  · exact .inl (reaches_trans h2 he)
  · exact .inr ⟨v, reaches_trans h2 hv, hp⟩

theorem terminatesAt_of_spine {d : Nat} {b : BuiltinFun} {n : Nat} {t : Term} (h : SpineAt d b n t) :
    TerminatesAt d t := by
  intro ρ henv hlen
  rcases h ρ henv hlen with he | ⟨v, hv, _⟩
  · exact .inl he
  · exact .inr ⟨v, hv⟩

theorem passThrough_false_vcon {b : BuiltinFun} (hb : passThroughBuiltin b = false)
    {args : List CekValue} {v : CekValue} (h : evalBuiltin b args = some v) : InertV v := by
  have hnone : evalBuiltinPassThrough b args = none := by
    apply evalBuiltinPassThrough_none_of_not_passthrough
    cases b <;> simp_all [passThroughBuiltin]
  simp only [evalBuiltin, hnone] at h
  split at h
  · split at h
    · cases h; trivial
    · cases h
  · cases h

theorem inertAt_of_spine {d : Nat} {b : BuiltinFun} {n : Nat} {t : Term} (h : SpineAt d b n t)
    (hn : n = builtinArity b) (hb : passThroughBuiltin b = false) : InertAt d t := by
  intro ρ henv hlen
  rcases h ρ henv hlen with he | ⟨v, hv, _, hsat⟩
  · exact .inl he
  · obtain ⟨args, hargs⟩ := hsat hn
    exact .inr ⟨v, hv, passThrough_false_vcon hb hargs⟩

/-! ## Outcomes -/

/-- Evaluation errors, or halts with a value satisfying `Q`. -/
def Outcome (Q : CekValue → Prop) (ρ : CekEnv) (t : Term) : Prop :=
  Errs ρ t ∨ ∃ v, Halts ρ t v ∧ Q v

theorem termState_of_outcome {Q : CekValue → Prop} {ρ : CekEnv} {t : Term} (h : Outcome Q ρ t) :
    TermState (.compute [] ρ t) := by
  rcases h with he | ⟨v, hv, _⟩
  · exact .inl he
  · exact .inr ⟨v, hv⟩

/-- The empty-stack outcome of a computation reached from `compute [] ρ t`. -/
theorem outcome_of_reaches {Q : CekValue → Prop} {ρ : CekEnv} {t : Term} {s : State}
    (h : Reaches (.compute [] ρ t) s)
    (hs : Reaches s .error ∨ ∃ v, Reaches s (.halt v) ∧ Q v) : Outcome Q ρ t := by
  rcases hs with he | ⟨v, hv, hq⟩
  · exact .inl (reaches_trans h he)
  · exact .inr ⟨v, reaches_trans h hv, hq⟩

/-! ## `force (ifThenElse c (delay a) (delay b))` -/

theorem ite_select (ρ : CekEnv) (ta tb : Term) (vc : CekValue) :
    Reaches (.ret [.funV (.VBuiltin .IfThenElse [] (.more .argV (.more .argV (.one .argV)))),
        .arg (.Delay ta) ρ, .arg (.Delay tb) ρ, .force] vc) .error ∨
      Reaches (.ret [.funV (.VBuiltin .IfThenElse [] (.more .argV (.more .argV (.one .argV)))),
        .arg (.Delay ta) ρ, .arg (.Delay tb) ρ, .force] vc) (.compute [] ρ ta) ∨
      Reaches (.ret [.funV (.VBuiltin .IfThenElse [] (.more .argV (.more .argV (.one .argV)))),
        .arg (.Delay ta) ρ, .arg (.Delay tb) ρ, .force] vc) (.compute [] ρ tb) := by
  cases vc with
  | VCon c =>
    cases c with
    | Bool b =>
      cases b
      · exact .inr (.inr (reaches_of_steps 8 rfl))
      · exact .inr (.inl (reaches_of_steps 8 rfl))
    | _ => exact .inl (reaches_of_steps 7 rfl)
  | _ => exact .inl (reaches_of_steps 7 rfl)

theorem outcome_ite {Q : CekValue → Prop} {ρ : CekEnv} {tc ta tb : Term}
    (hc : Errs ρ tc ∨ ∃ v, Halts ρ tc v) (ha : Outcome Q ρ ta) (hb : Outcome Q ρ tb) :
    Outcome Q ρ (.Force (.Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse)) tc) (.Delay ta))
      (.Delay tb))) := by
  have h8 : Reaches (.compute [] ρ (.Force (.Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse)) tc)
      (.Delay ta)) (.Delay tb))))
      (.compute [.funV (.VBuiltin .IfThenElse [] (.more .argV (.more .argV (.one .argV)))),
        .arg (.Delay ta) ρ, .arg (.Delay tb) ρ, .force] ρ tc) := reaches_of_steps 8 rfl
  rcases hc with he | ⟨vc, hvc⟩
  · exact .inl (reaches_trans h8 (errs_on_stack he _))
  have h9 := reaches_trans h8 (halts_on_stack hvc _)
  rcases ite_select ρ ta tb vc with he | hsel | hsel
  · exact .inl (reaches_trans h9 he)
  · rcases ha with he | ⟨v, hv, hq⟩
    · exact .inl (reaches_trans h9 (reaches_trans hsel he))
    · exact .inr ⟨v, reaches_trans h9 (reaches_trans hsel hv), hq⟩
  · rcases hb with he | ⟨v, hv, hq⟩
    · exact .inl (reaches_trans h9 (reaches_trans hsel he))
    · exact .inr ⟨v, reaches_trans h9 (reaches_trans hsel hv), hq⟩

/-- `force (delay b)`. -/
theorem outcome_force_delay {Q : CekValue → Prop} {ρ : CekEnv} {tb : Term} (h : Outcome Q ρ tb) :
    Outcome Q ρ (.Force (.Delay tb)) := by
  have h3 : Reaches (.compute [] ρ (.Force (.Delay tb))) (.compute [] ρ tb) := reaches_of_steps 3 rfl
  rcases h with he | ⟨v, hv, hq⟩
  · exact .inl (reaches_trans h3 he)
  · exact .inr ⟨v, reaches_trans h3 hv, hq⟩

/-- A strict binding. -/
theorem outcome_let {Q : CekValue → Prop} {d : Nat} {ρ : CekEnv} {tr tb : Term}
    (henv : EnvWellFormed d ρ) (hlen : d ≤ ρ.length) (hclosed : closedAt d tr = true)
    (hr : Errs ρ tr ∨ ∃ v, Halts ρ tr v)
    (hb : ∀ ρ', EnvWellFormed (d + 1) ρ' → d + 1 ≤ ρ'.length → Outcome Q ρ' tb) :
    Outcome Q ρ (.Apply (.Lam 0 tb) tr) := by
  have h3 : Reaches (.compute [] ρ (.Apply (.Lam 0 tb) tr)) (.compute [.funV (.VLam tb ρ)] ρ tr) :=
    reaches_of_steps 3 rfl
  rcases hr with he | ⟨v, hv⟩
  · exact .inl (reaches_trans h3 (errs_on_stack he _))
  have h4 : Reaches (.compute [] ρ (.Apply (.Lam 0 tb) tr)) (.compute [] (ρ.extend v) tb) :=
    reaches_trans h3 (reaches_trans (halts_on_stack hv _) (reaches_of_steps 1 rfl))
  obtain ⟨henv', hlen'⟩ := envWellFormed_extend' henv hlen (halts_wellFormed henv hlen hclosed hv)
  exact outcome_of_reaches h4 (by
    rcases hb _ henv' hlen' with he | ⟨u, hu, hq⟩
    · exact .inl he
    · exact .inr ⟨u, hu, hq⟩)

/-- A case whose scrutinee terminates and whose alternatives terminate for
    any fields. -/
theorem terminates_case {d : Nat} {ρ : CekEnv} {ts : Term} {talts : List Term}
    (henv : EnvWellFormed d ρ) (hlen : d ≤ ρ.length) (hclosed : closedAt d ts = true)
    (hs : Errs ρ ts ∨ ∃ v, Halts ρ ts v) (halts : ∀ a ∈ talts, AltSafeAt d a) :
    TermState (.compute [] ρ (.Case ts talts)) := by
  refine termState_of_reaches (reaches_of_steps 1 rfl) (termState_compute hs fun w hw => ?_)
  refine termState_of_reaches (s' := step (.ret [.caseScrutinee talts ρ] w)) (reaches_of_steps 1 rfl) ?_
  rw [step_caseScrutinee]
  cases hd : dispatch talts w with
  | none => exact termState_error
  | some r =>
    obtain ⟨alt, fields⟩ := r
    obtain ⟨hmem, hfs⟩ := dispatch_spec hd (halts_wellFormed henv hlen hclosed hw)
    simpa using halts alt hmem ρ henv hlen fields hfs

/-- A case whose alternatives are inert. -/
theorem inert_case {d : Nat} {ρ : CekEnv} {ts : Term} {talts : List Term}
    (henv : EnvWellFormed d ρ) (hlen : d ≤ ρ.length)
    (hs : Errs ρ ts ∨ ∃ v, Halts ρ ts v) (halts : ∀ a ∈ talts, InertAt d a) :
    Outcome InertV ρ (.Case ts talts) := by
  have h1 : Reaches (.compute [] ρ (.Case ts talts)) (.compute [.caseScrutinee talts ρ] ρ ts) :=
    reaches_of_steps 1 rfl
  rcases hs with he | ⟨w, hw⟩
  · exact .inl (reaches_trans h1 (errs_on_stack he _))
  have h2 : Reaches (.compute [] ρ (.Case ts talts)) (step (.ret [.caseScrutinee talts ρ] w)) :=
    reaches_trans h1 (reaches_trans (halts_on_stack hw _) (reaches_of_steps 1 rfl))
  rw [step_caseScrutinee] at h2
  cases hd : dispatch talts w with
  | none => rw [hd] at h2; exact .inl h2
  | some r =>
    obtain ⟨alt, fields⟩ := r
    rw [hd] at h2
    have hmem : alt ∈ talts := by
      cases w with
      | VConstr tag fs =>
        simp only [dispatch] at hd
        cases hl : talts[tag]? with
        | none => rw [hl] at hd; cases hd
        | some a => rw [hl] at hd; cases hd; exact List.mem_of_getElem? hl
      | VCon c =>
        simp only [dispatch] at hd
        cases hc : constToTagAndFields c with
        | none => rw [hc] at hd; cases hd
        | some r =>
          obtain ⟨tag, numCtors, fs⟩ := r
          rw [hc] at hd
          simp only at hd
          split at hd
          · cases hd
          · cases hl : talts[tag]? with
            | none => rw [hl] at hd; cases hd
            | some a => rw [hl] at hd; cases hd; exact List.mem_of_getElem? hl
      | VLam _ _ => cases hd
      | VDelay _ _ => cases hd
      | VBuiltin _ _ _ => cases hd
    rcases halts alt hmem ρ henv hlen with he | ⟨v, hv, hq⟩
    · exact .inl (reaches_trans h2 (errs_on_stack he _))
    · refine outcome_of_reaches h2 ?_
      have hr := halts_on_stack hv (fields.map Frame.applyArg ++ [])
      cases fields with
      | nil => exact .inr ⟨v, reaches_trans hr (reaches_of_steps 1 rfl), hq⟩
      | cons f _ =>
        exact .inl (reaches_trans hr (reaches_of_steps 1 (inert_apply_errors hq f _)))

/-- A lambda alternative applied to fields. -/
theorem altSafeAt_lam {d : Nat} {tb : Term} (h : AltSafeAt (d + 1) tb) : AltSafeAt d (.Lam 0 tb) := by
  intro ρ henv hlen fields hfs
  cases fields with
  | nil => exact termState_of_reaches (reaches_of_steps 1 rfl) (termState_ret_nil _)
  | cons f fs =>
    cases hfs with
    | cons hf hfs =>
      obtain ⟨henv', hlen'⟩ := envWellFormed_extend' henv hlen hf
      exact termState_of_reaches (reaches_of_steps 2 rfl) (h _ henv' hlen' fs hfs)

theorem altSafeAt_of_inert {d : Nat} {t : Term} (h : InertAt d t) : AltSafeAt d t := by
  intro ρ henv hlen fields _
  rcases h ρ henv hlen with he | ⟨v, hv, hq⟩
  · exact .inl (errs_on_stack he _)
  · exact termState_of_reaches (halts_on_stack hv _) (termState_inert_fields hq fields)

/-! ## List predicates -/

theorem terminatesList_mem : ∀ {es : List Expr}, terminatesList es = true → ∀ e ∈ es, terminates e = true
  | [], _, _, h => by cases h
  | e :: rest, h, x, hx => by
    rw [terminatesList, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact terminatesList_mem h.2 x hx

theorem inertList_mem : ∀ {es : List Expr}, inertList es = true → ∀ e ∈ es, inert e = true
  | [], _, _, h => by cases h
  | e :: rest, h, x, hx => by
    rw [inertList, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact inertList_mem h.2 x hx

theorem altsSafe_mem : ∀ {es : List Expr}, altsSafe es = true → ∀ e ∈ es, altSafe e = true
  | [], _, _, h => by cases h
  | e :: rest, h, x, hx => by
    rw [altsSafe, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact altsSafe_mem h.2 x hx

theorem terminatesBinds_mem : ∀ {bs : List (VarId × Expr × Bool)}, terminatesBinds bs = true →
    ∀ b ∈ bs, terminates b.2.1 = true
  | [], _, _, h => by cases h
  | (x, r, er) :: rest, h, b, hb => by
    rw [terminatesBinds, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h.1
    · exact terminatesBinds_mem h.2 b hb

/-! ## Strict binding blocks -/

theorem terminatesAt_iff_outcome {d : Nat} {t : Term} :
    TerminatesAt d t ↔ ∀ ρ, EnvWellFormed d ρ → d ≤ ρ.length → Outcome (fun _ => True) ρ t := by
  constructor
  · intro h ρ henv hlen
    rcases h ρ henv hlen with he | ⟨v, hv⟩
    · exact .inl he
    · exact .inr ⟨v, hv, trivial⟩
  · intro h ρ henv hlen
    rcases h ρ henv hlen with he | ⟨v, hv, _⟩
    · exact .inl he
    · exact .inr ⟨v, hv⟩

theorem outcome_letBlock {Q : CekValue → Prop} :
    ∀ (bs : List (VarId × Expr × Bool)) (body : Expr),
      (∀ b ∈ bs, ∀ env t, lowerTotalExpr env b.2.1 = some t → TerminatesAt env.length t) →
      (∀ env t, lowerTotalExpr env body = some t →
        ∀ ρ, EnvWellFormed env.length ρ → env.length ≤ ρ.length → Outcome Q ρ t) →
      ∀ env t, lowerTotalExpr env (.Let bs body) = some t →
        ∀ ρ, EnvWellFormed env.length ρ → env.length ≤ ρ.length → Outcome Q ρ t
  | [], body, _, hbody, env, t, hlow => by
    rw [ShapeFacts.lowerTotalExpr_let_nil] at hlow
    exact hbody env t hlow
  | (x, r, er) :: rest, body, hbs, hbody, env, t, hlow => by
    rw [ShapeFacts.lowerTotalExpr_let_cons] at hlow
    obtain ⟨tr, tb, htr, htb, rfl⟩ := lowerTotalExpr_let_single_some hlow
    intro ρ henv hlen
    have hrest := outcome_letBlock rest body (fun b hb => hbs b (.tail _ hb)) hbody (x :: env) tb htb
    exact outcome_let henv hlen (MIR.lowerTotalExpr_closedAt htr)
      (hbs (x, r, er) (.head _) env tr htr ρ henv hlen) (by simpa using hrest)

/-! ## The analysis is sound -/

def Sound (e : Expr) : Prop :=
  (terminates e = true → ∀ env t, lowerTotalExpr env e = some t → TerminatesAt env.length t) ∧
  (inert e = true → ∀ env t, lowerTotalExpr env e = some t → InertAt env.length t) ∧
  (altSafe e = true → ∀ env t, lowerTotalExpr env e = some t → AltSafeAt env.length t) ∧
  (∀ b n, spineHead e = some (b, n) → n ≤ builtinArity b →
    ∀ env t, lowerTotalExpr env e = some t → SpineAt env.length b n t)

theorem inertAt_iff_outcome {d : Nat} {t : Term} :
    InertAt d t ↔ ∀ ρ, EnvWellFormed d ρ → d ≤ ρ.length → Outcome InertV ρ t := Iff.rfl

theorem sound_lt : ∀ (N : Nat) (e : Expr), sizeOf e < N → Sound e := by
  intro N
  induction N with
  | zero => intro e h; omega
  | succ N ih =>
  intro e hsize
  have ihs : ∀ e', sizeOf e' < sizeOf e → Sound e' := fun e' h => ih e' (by omega)
  -- the alternative component, which only needs the inert component of `e` itself
  have alt_of_inert : (inert e = true → ∀ env t, lowerTotalExpr env e = some t → InertAt env.length t) →
      altSafe e = true → ∀ env t, lowerTotalExpr env e = some t → AltSafeAt env.length t := by
    intro hinert h env t hlow
    cases e with
    | Lam x b =>
      rw [altSafe] at h
      obtain ⟨tb, htb, rfl⟩ := lowerTotalExpr_lam_some hlow
      have := (ihs b (by simp only [Expr.Lam.sizeOf_spec]; omega)).2.2.1 h (x :: env) tb htb
      exact altSafeAt_lam (by simpa using this)
    | _ =>
      rw [altSafe] at h
      all_goals first
        | exact altSafeAt_of_inert (hinert h env t hlow)
        | (intro x b hx; cases hx)
  have noInert : inert e = false → inert e = true → ∀ env t, lowerTotalExpr env e = some t →
      InertAt env.length t := fun h h' => by rw [h] at h'; cases h'
  have noSpine : spineHead e = none → ∀ b n, spineHead e = some (b, n) → n ≤ builtinArity b →
      ∀ env t, lowerTotalExpr env e = some t → SpineAt env.length b n t :=
    fun h b n h' => by rw [h] at h'; cases h'
  cases e with
  | Var x =>
    have hi : inert (.Var x) = false := by simp [inert]
    have hs : spineHead (.Var x) = none := by simp [spineHead]
    refine ⟨fun _ env t hlow => ?_, noInert hi, alt_of_inert (noInert hi), noSpine hs⟩
    obtain ⟨i, hi, rfl⟩ := lowerTotalExpr_var_some hlow
    intro ρ henv _
    exact .inr (halts_var_wf henv (envLookupT_lt hi))
  | Lit c =>
    obtain ⟨c, ty⟩ := c
    have hs : spineHead (.Lit (c, ty)) = none := by simp [spineHead]
    have hl : ∀ env t, lowerTotalExpr env (.Lit (c, ty)) = some t → ∀ ρ, Halts ρ t (.VCon c) := by
      intro env t hlow ρ
      rw [lowerTotalExpr_lit] at hlow; cases hlow
      exact reaches_of_steps 2 rfl
    have hin : inert (.Lit (c, ty)) = true → ∀ env t, lowerTotalExpr env (.Lit (c, ty)) = some t →
        InertAt env.length t :=
      fun _ env t hlow ρ _ _ => .inr ⟨_, hl env t hlow ρ, trivial⟩
    exact ⟨fun _ env t hlow ρ _ _ => .inr ⟨_, hl env t hlow ρ⟩, hin, alt_of_inert hin, noSpine hs⟩
  | Builtin b =>
    have hi : inert (.Builtin b) = false := by simp [inert]
    have hsp : ∀ b' n, spineHead (.Builtin b) = some (b', n) → n ≤ builtinArity b' →
        ∀ env t, lowerTotalExpr env (.Builtin b) = some t → SpineAt env.length b' n t := by
      intro b' n h _ env t hlow
      simp only [spineHead, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [lowerTotalExpr_builtin] at hlow; cases hlow
      exact spineAt_builtin _ _
    exact ⟨fun _ env t hlow => terminatesAt_of_spine (hsp b 0 (by simp [spineHead]) (Nat.zero_le _)
      env t hlow), noInert hi, alt_of_inert (noInert hi), hsp⟩
  | Error =>
    have hs : spineHead .Error = none := by simp [spineHead]
    have hin : inert .Error = true → ∀ env t, lowerTotalExpr env .Error = some t →
        InertAt env.length t := by
      intro _ env t hlow ρ _ _
      rw [lowerTotalExpr_error] at hlow; cases hlow
      exact .inl (reaches_of_steps 1 rfl)
    exact ⟨fun _ env t hlow => (hin (by simp [inert]) env t hlow).terminates, hin, alt_of_inert hin,
      noSpine hs⟩
  | Lam x body =>
    have hi : inert (.Lam x body) = false := by simp [inert]
    have hs : spineHead (.Lam x body) = none := by simp [spineHead]
    refine ⟨fun _ env t hlow => ?_, noInert hi, alt_of_inert (noInert hi), noSpine hs⟩
    obtain ⟨tb, _, rfl⟩ := lowerTotalExpr_lam_some hlow
    exact fun ρ _ _ => .inr ⟨_, reaches_of_steps 2 rfl⟩
  | Delay body =>
    have hi : inert (.Delay body) = false := by simp [inert]
    have hs : spineHead (.Delay body) = none := by simp [spineHead]
    refine ⟨fun _ env t hlow => ?_, noInert hi, alt_of_inert (noInert hi), noSpine hs⟩
    obtain ⟨tb, _, rfl⟩ := lowerTotalExpr_delay_some hlow
    exact fun ρ _ _ => .inr ⟨_, reaches_of_steps 2 rfl⟩
  | Fix f body =>
    have ht : terminates (.Fix f body) = false := by simp [terminates]
    have hi : inert (.Fix f body) = false := by simp [inert]
    have hs : spineHead (.Fix f body) = none := by simp [spineHead]
    exact ⟨(fun h => by rw [ht] at h; cases h), noInert hi, alt_of_inert (noInert hi), noSpine hs⟩
  | Constr tag fields =>
    have hmem : ∀ f ∈ fields, sizeOf f < sizeOf (Expr.Constr tag fields) := fun f hf => by
      have := List.sizeOf_lt_of_mem hf
      simp only [Expr.Constr.sizeOf_spec]; omega
    have core : terminatesList fields = true → ∀ env t, lowerTotalExpr env (.Constr tag fields) = some t →
        ∀ ρ, EnvWellFormed env.length ρ → env.length ≤ ρ.length → Outcome InertV ρ t := by
      intro h env t hlow ρ henv hlen
      rw [MIR.lowerTotalExpr_constr_of_list] at hlow
      cases hts : MIR.lowerTotalExprList env fields with
      | none => rw [hts] at hlow; cases hlow
      | some ts =>
        rw [hts] at hlow; cases hlow
        have hterm : ∀ t ∈ ts, TerminatesAt env.length t := by
          intro t ht
          obtain ⟨f, hf, hfl⟩ := lowerTotalExprList_mem hts t ht
          exact (ihs f (hmem f hf)).1 (terminatesList_mem h f hf) env t hfl
        cases ts with
        | nil => exact .inr ⟨_, reaches_of_steps 2 rfl, trivial⟩
        | cons m ms =>
          have hs := termState_constrField henv hlen tag ms m [] (hterm m (.head _))
            (fun t ht => hterm t (.tail _ ht))
          have h1 : Reaches (.compute [] ρ (.Constr tag (m :: ms)))
              (.compute [.constrField tag [] ms ρ] ρ m) := reaches_of_steps 1 rfl
          rcases hs with he | ⟨u, hu⟩
          · exact .inl (reaches_trans h1 he)
          · exact .inr ⟨u, reaches_trans h1 hu, halts_constrField_inert hu⟩
    have hin : inert (.Constr tag fields) = true → ∀ env t, lowerTotalExpr env (.Constr tag fields) = some t →
        InertAt env.length t := by
      intro h env t hlow
      rw [inert] at h
      exact core h env t hlow
    refine ⟨fun h env t hlow => ?_, hin, alt_of_inert hin, noSpine (by simp [spineHead])⟩
    rw [terminates] at h
    exact terminatesAt_iff_outcome.mpr fun ρ henv hlen => by
      rcases core h env t hlow ρ henv hlen with he | ⟨v, hv, _⟩
      · exact .inl he
      · exact .inr ⟨v, hv, trivial⟩
  | Case scrutinee alternatives =>
    have hss : sizeOf scrutinee < sizeOf (Expr.Case scrutinee alternatives) := by
      simp only [Expr.Case.sizeOf_spec]; omega
    have hmem : ∀ a ∈ alternatives, sizeOf a < sizeOf (Expr.Case scrutinee alternatives) := fun a ha => by
      have := List.sizeOf_lt_of_mem ha
      simp only [Expr.Case.sizeOf_spec]; omega
    have hin : inert (.Case scrutinee alternatives) = true → ∀ env t,
        lowerTotalExpr env (.Case scrutinee alternatives) = some t → InertAt env.length t := by
      intro h env t hlow ρ henv hlen
      rw [inert, Bool.and_eq_true] at h
      obtain ⟨ts, talts, hts, htalts, rfl⟩ := lowerTotalExpr_case_some hlow
      refine inert_case henv hlen ((ihs _ hss).1 h.1 env ts hts ρ henv hlen) fun a ha => ?_
      obtain ⟨alt, halt, hlowa⟩ := lowerTotalExprList_mem htalts a ha
      exact (ihs alt (hmem alt halt)).2.1 (inertList_mem h.2 alt halt) env a hlowa
    refine ⟨fun h env t hlow => ?_, hin, alt_of_inert hin, noSpine (by simp [spineHead])⟩
    rw [terminates, Bool.and_eq_true] at h
    obtain ⟨ts, talts, hts, htalts, rfl⟩ := lowerTotalExpr_case_some hlow
    intro ρ henv hlen
    have hs := terminates_case henv hlen (MIR.lowerTotalExpr_closedAt hts)
      ((ihs _ hss).1 h.1 env ts hts ρ henv hlen) fun a ha => by
        obtain ⟨alt, halt, hlowa⟩ := lowerTotalExprList_mem htalts a ha
        exact (ihs alt (hmem alt halt)).2.2.1 (altsSafe_mem h.2 alt halt) env a hlowa
    rcases hs with he | hv
    · exact .inl he
    · exact .inr hv
  | Let bindings body =>
    have hbody : sizeOf body < sizeOf (Expr.Let bindings body) := by
      simp only [Expr.Let.sizeOf_spec]; omega
    have hbinds : ∀ b ∈ bindings, sizeOf b.2.1 < sizeOf (Expr.Let bindings body) := fun b hb => by
      have := List.sizeOf_lt_of_mem hb
      obtain ⟨x, r, er⟩ := b
      simp only [Expr.Let.sizeOf_spec, Prod.mk.sizeOf_spec] at this ⊢; omega
    have hrhs : terminatesBinds bindings = true →
        ∀ b ∈ bindings, ∀ env t, lowerTotalExpr env b.2.1 = some t → TerminatesAt env.length t :=
      fun h b hb => (ihs _ (hbinds b hb)).1 (terminatesBinds_mem h b hb)
    have hin : inert (.Let bindings body) = true → ∀ env t,
        lowerTotalExpr env (.Let bindings body) = some t → InertAt env.length t := by
      intro h env t hlow
      rw [inert, Bool.and_eq_true] at h
      exact outcome_letBlock bindings body (hrhs h.1) ((ihs _ hbody).2.1 h.2) env t hlow
    refine ⟨fun h env t hlow => ?_, hin, alt_of_inert hin, noSpine (by simp [spineHead])⟩
    rw [terminates, Bool.and_eq_true] at h
    exact terminatesAt_iff_outcome.mpr (outcome_letBlock bindings body (hrhs h.1)
      (fun env t hl => terminatesAt_iff_outcome.mp ((ihs _ hbody).1 h.2 env t hl)) env t hlow)
  | Force inner =>
    have hsz : sizeOf inner < sizeOf (Expr.Force inner) := by
      simp only [Expr.Force.sizeOf_spec]; omega
    have hsp : ∀ b n, spineHead (.Force inner) = some (b, n) → n ≤ builtinArity b →
        ∀ env t, lowerTotalExpr env (.Force inner) = some t → SpineAt env.length b n t := by
      intro b n h hn env t hlow
      rw [spineHead] at h
      cases hi : spineHead inner with
      | none => rw [hi] at h; cases h
      | some r =>
        obtain ⟨b', n'⟩ := r
        rw [hi] at h; cases h
        obtain ⟨ti, hti, rfl⟩ := lowerTotalExpr_force_some hlow
        simp only at hn
        exact spineAt_force hn ((ihs _ hsz).2.2.2 b' n' hi (by omega) env ti hti)
    -- the three shapes of a forced expression
    have shapes : ∀ (Q : CekValue → Prop) (P : Expr → Bool),
        (∀ e', sizeOf e' < sizeOf (Expr.Force inner) → P e' = true → ∀ env t,
          lowerTotalExpr env e' = some t → ∀ ρ, EnvWellFormed env.length ρ → env.length ≤ ρ.length →
            Outcome Q ρ t) →
        ∀ env t, lowerTotalExpr env (.Force inner) = some t →
          ∀ ρ, EnvWellFormed env.length ρ → env.length ≤ ρ.length →
          ((∃ body, delayBody inner = some body ∧ P body = true) ∨
           (∃ c a b, iteView inner = some (c, a, b) ∧ terminates c = true ∧ P a = true ∧ P b = true)) →
          Outcome Q ρ t := by
      intro Q P hP env t hlow ρ henv hlen hshape
      obtain ⟨ti, hti, rfl⟩ := lowerTotalExpr_force_some hlow
      rcases hshape with ⟨body, hb, hP'⟩ | ⟨c, a, b, hv, hc, ha, hb⟩
      · have : inner = .Delay body := by
          unfold delayBody at hb; split at hb
          · cases hb; rfl
          · cases hb
        subst this
        obtain ⟨tb, htb, rfl⟩ := lowerTotalExpr_delay_some hti
        have hbs : sizeOf body < sizeOf (Expr.Force (.Delay body)) := by
          simp only [Expr.Force.sizeOf_spec, Expr.Delay.sizeOf_spec]; omega
        exact outcome_force_delay (hP body hbs hP' env tb htb ρ henv hlen)
      · have hsz' := iteView_sizeOf hv
        have := iteView_some hv
        subst this
        obtain ⟨t1, tbd, ht1, htbd, rfl⟩ := lowerTotalExpr_app_some hti
        obtain ⟨t2, tad, ht2, htad, rfl⟩ := lowerTotalExpr_app_some ht1
        obtain ⟨t3, tc, ht3, htc, rfl⟩ := lowerTotalExpr_app_some ht2
        obtain ⟨t4, ht4, rfl⟩ := lowerTotalExpr_force_some ht3
        rw [lowerTotalExpr_builtin] at ht4; cases ht4
        obtain ⟨ta, hta, rfl⟩ := lowerTotalExpr_delay_some htad
        obtain ⟨tb, htb, rfl⟩ := lowerTotalExpr_delay_some htbd
        have hcs : sizeOf c < sizeOf (Expr.Force (.App (.App (.App (.Force (.Builtin .IfThenElse)) c)
            (.Delay a)) (.Delay b))) := by simp only [Expr.Force.sizeOf_spec]; omega
        have has : sizeOf a < sizeOf (Expr.Force (.App (.App (.App (.Force (.Builtin .IfThenElse)) c)
            (.Delay a)) (.Delay b))) := by simp only [Expr.Force.sizeOf_spec]; omega
        have hbs : sizeOf b < sizeOf (Expr.Force (.App (.App (.App (.Force (.Builtin .IfThenElse)) c)
            (.Delay a)) (.Delay b))) := by simp only [Expr.Force.sizeOf_spec]; omega
        exact outcome_ite ((ihs c hcs).1 hc env tc htc ρ henv hlen) (hP a has ha env ta hta ρ henv hlen)
          (hP b hbs hb env tb htb ρ henv hlen)
    have hin : inert (.Force inner) = true → ∀ env t, lowerTotalExpr env (.Force inner) = some t →
        InertAt env.length t := by
      intro h env t hlow ρ henv hlen
      rw [inert] at h
      split at h
      · rename_i body hb
        exact shapes InertV inert (fun e' he' hi env t hl => (ihs e' he').2.1 hi env t hl) env t hlow
          ρ henv hlen (.inl ⟨body, hb, h⟩)
      · split at h
        · rename_i c a b hv
          simp only [Bool.and_eq_true] at h
          exact shapes InertV inert (fun e' he' hi env t hl => (ihs e' he').2.1 hi env t hl) env t hlow
            ρ henv hlen (.inr ⟨c, a, b, hv, h.1.1, h.1.2, h.2⟩)
        · unfold spineAccepts at h
          split at h
          · rename_i b n hs
            simp only [if_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
            have hsp' : spineHead (.Force inner) = some (b, n + 1) := by rw [spineHead, hs]; rfl
            exact inertAt_of_spine (hsp b (n + 1) hsp' (by omega) env t hlow) h.1 h.2 ρ henv hlen
          · cases h
    refine ⟨fun h env t hlow => ?_, hin, alt_of_inert hin, hsp⟩
    rw [terminates] at h
    split at h
    · rename_i body hb
      exact terminatesAt_iff_outcome.mpr fun ρ henv hlen =>
        shapes (fun _ => True) terminates (fun e' he' hi env t hl =>
          terminatesAt_iff_outcome.mp ((ihs e' he').1 hi env t hl)) env t hlow ρ henv hlen
          (.inl ⟨body, hb, h⟩)
    · split at h
      · rename_i c a b hv
        simp only [Bool.and_eq_true] at h
        exact terminatesAt_iff_outcome.mpr fun ρ henv hlen =>
          shapes (fun _ => True) terminates (fun e' he' hi env t hl =>
            terminatesAt_iff_outcome.mp ((ihs e' he').1 hi env t hl)) env t hlow ρ henv hlen
            (.inr ⟨c, a, b, hv, h.1.1, h.1.2, h.2⟩)
      · unfold spineAccepts at h
        split at h
        · rename_i b n hs
          simp only [Bool.false_eq_true, if_false, decide_eq_true_eq] at h
          have hsp' : spineHead (.Force inner) = some (b, n + 1) := by rw [spineHead, hs]; rfl
          exact terminatesAt_of_spine (hsp b (n + 1) hsp' h env t hlow)
        · cases h
  | App f a =>
    have hfs : sizeOf f < sizeOf (Expr.App f a) := by simp only [Expr.App.sizeOf_spec]; omega
    have has : sizeOf a < sizeOf (Expr.App f a) := by simp only [Expr.App.sizeOf_spec]; omega
    have hsp : ∀ b n, spineHead (.App f a) = some (b, n) → n ≤ builtinArity b →
        ∀ env t, lowerTotalExpr env (.App f a) = some t → SpineAt env.length b n t := by
      intro b n h hn env t hlow
      rw [spineHead] at h
      split at h
      · rename_i hta
        cases hi : spineHead f with
        | none => rw [hi] at h; cases h
        | some r =>
          obtain ⟨b', n'⟩ := r
          rw [hi] at h; cases h
          obtain ⟨tf, ta, htf, hta', rfl⟩ := lowerTotalExpr_app_some hlow
          simp only at hn
          exact spineAt_apply hn ((ihs _ hfs).2.2.2 b' n' hi (by omega) env tf htf)
            ((ihs _ has).1 hta env ta hta')
      · cases h
    have viaSpine : ∀ b n, terminates a = true → spineHead f = some (b, n) →
        spineHead (.App f a) = some (b, n + 1) := by
      intro b n ha hs
      rw [spineHead, if_pos ha, hs]; rfl
    have hin : inert (.App f a) = true → ∀ env t, lowerTotalExpr env (.App f a) = some t →
        InertAt env.length t := by
      intro h env t hlow
      rw [inert, Bool.and_eq_true] at h
      obtain ⟨ha, h⟩ := h
      unfold spineAccepts at h
      split at h
      · rename_i b n hs
        simp only [if_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
        exact inertAt_of_spine (hsp b (n + 1) (viaSpine b n ha hs) (by omega) env t hlow) h.1 h.2
      · cases h
    refine ⟨fun h env t hlow => ?_, hin, alt_of_inert hin, hsp⟩
    rw [terminates, Bool.and_eq_true] at h
    obtain ⟨ha, h⟩ := h
    unfold spineAccepts at h
    split at h
    · rename_i b n hs
      simp only [Bool.false_eq_true, if_false, decide_eq_true_eq] at h
      exact terminatesAt_of_spine (hsp b (n + 1) (viaSpine b n ha hs) h env t hlow)
    · cases h

theorem terminates_sound {e : Expr} (h : terminates e = true) {env : List VarId} {t : Term}
    (hlow : lowerTotalExpr env e = some t) : TerminatesAt env.length t :=
  (sound_lt (sizeOf e + 1) e (by omega)).1 h env t hlow

end Moist.Verified.FailFast
