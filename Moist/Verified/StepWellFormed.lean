import Moist.Verified.BetaValueRefines

/-! # Step preservation of well-formedness

The CEK `step` function preserves a state well-formedness invariant:
if the current term is `closedAt` relative to the environment depth,
the environment entries are well-formed, and the stack frames are
well-formed, then after one step all these properties still hold.

**Main result**: `step_preserves_wf` and its corollary `steps_preserves_wf`.
-/

namespace Moist.Verified.StepWellFormed

open Moist.CEK
open Moist.Plutus.Term (Term Const BuiltinFun)
open Moist.Verified
open Moist.Verified.BetaValueRefines
open Moist.Verified.Equivalence (steps constToTagAndFields_fields_vcon)

inductive StateWellFormed : State → Prop
  | compute : ∀ {π ρ t k},
      StackWellFormed π → EnvWellFormed k ρ → k ≤ ρ.length →
      closedAt k t = true →
      StateWellFormed (.compute π ρ t)
  | ret : ∀ {π v},
      StackWellFormed π → ValueWellFormed v →
      StateWellFormed (.ret π v)
  | error : StateWellFormed .error
  | halt : ∀ {v}, ValueWellFormed v → StateWellFormed (.halt v)

section Helpers

private theorem closedAtList_elem {d : Nat} {ts : List Term} {i : Nat}
    (h : closedAtList d ts = true) (hi : i < ts.length) :
    closedAt d ts[i] = true := by
  induction ts generalizing i with
  | nil => simp at hi
  | cons t rest ih =>
    simp [closedAtList] at h
    cases i with
    | zero => exact h.1
    | succ j => exact ih h.2 (by simp at hi; omega)

private theorem closedAtList_getElem? {d : Nat} {ts : List Term} {tag : Nat} {alt : Term}
    (h : closedAtList d ts = true) (hget : ts[tag]? = some alt) :
    closedAt d alt = true := by
  have hlt := List.getElem?_eq_some_iff.mp hget
  have := closedAtList_elem h hlt.1
  rw [hlt.2] at this
  exact this

private theorem closedAtList_head {d : Nat} {t : Term} {rest : List Term}
    (h : closedAtList d (t :: rest) = true) : closedAt d t = true := by
  simp [closedAtList] at h; exact h.1

private theorem closedAtList_tail {d : Nat} {t : Term} {rest : List Term}
    (h : closedAtList d (t :: rest) = true) : closedAtList d rest = true := by
  simp [closedAtList] at h; exact h.2

private theorem valueListWellFormed_cons {v : CekValue} {vs : List CekValue}
    (hv : ValueWellFormed v) (hvs : ValueListWellFormed vs) :
    ValueListWellFormed (v :: vs) :=
  ValueListWellFormed.cons hv hvs

private theorem valueListWellFormed_reverse :
    ∀ {vs : List CekValue}, ValueListWellFormed vs → ValueListWellFormed vs.reverse
  | [], _ => ValueListWellFormed.nil
  | v :: rest, h => by
    cases h with
    | cons hv hrest =>
      simp [List.reverse_cons]
      exact valueListWellFormed_append (valueListWellFormed_reverse hrest)
        (ValueListWellFormed.cons hv ValueListWellFormed.nil)
where
  valueListWellFormed_append :
      ∀ {xs ys : List CekValue},
        ValueListWellFormed xs → ValueListWellFormed ys →
        ValueListWellFormed (xs ++ ys)
    | [], _, _, h => h
    | _ :: _, _, ValueListWellFormed.cons hx hxs, hy =>
      ValueListWellFormed.cons hx (valueListWellFormed_append hxs hy)

private theorem stackWellFormed_append :
    ∀ {xs ys : Stack},
      StackWellFormed xs → StackWellFormed ys →
      StackWellFormed (xs ++ ys)
  | [], _, _, h => h
  | _ :: _, _, StackWellFormed.cons hf hxs, hy =>
    StackWellFormed.cons hf (stackWellFormed_append hxs hy)

private theorem stackWellFormed_applyArgFrames {fields : List CekValue} {π : Stack}
    (hfs : ValueListWellFormed fields) (hπ : StackWellFormed π) :
    StackWellFormed (fields.map Frame.applyArg ++ π) := by
  induction fields with
  | nil => simp; exact hπ
  | cons v rest ih =>
    cases hfs with
    | cons hv hrest =>
      simp [List.map, List.cons_append]
      exact StackWellFormed.cons (FrameWellFormed.applyArg hv) (ih hrest)

private def allVcon_wf :
    (fields : List CekValue) → (∀ v ∈ fields, ∃ c, v = .VCon c) → ValueListWellFormed fields
  | [], _ => .nil
  | v :: rest, h =>
    have ⟨cv, hcv⟩ := h v (.head rest)
    hcv ▸ .cons (.vcon cv) (allVcon_wf rest (fun x hx => h x (.tail v hx)))

private theorem constToTagAndFields_fields_wf (c : Const) :
    match constToTagAndFields c with
    | some (_, _, fields) => ValueListWellFormed fields
    | none => True := by
  have h := constToTagAndFields_fields_vcon c
  cases hc : constToTagAndFields c with
  | none => trivial
  | some val =>
    obtain ⟨tag, numCtors, fields⟩ := val
    simp [hc] at h
    exact allVcon_wf fields h

end Helpers

section EvalBuiltinWF

private theorem evalBuiltinPassThrough_preserves_wf {b : BuiltinFun}
    {args : List CekValue} {v : CekValue}
    (heval : evalBuiltinPassThrough b args = some v)
    (hargs : ValueListWellFormed args) :
    ValueWellFormed v := by
  simp only [evalBuiltinPassThrough] at heval
  split at heval
  · -- IfThenElse: some (if cond then thenV else elseV) = some v
    rename_i elseV thenV cond
    split at heval
    · cases heval
      cases hargs with | cons _ h2 => cases h2 with | cons h3 _ => exact h3
    · cases heval
      cases hargs with | cons h1 _ => exact h1
  · -- ChooseUnit: some result = some v
    cases heval
    cases hargs with | cons h1 _ => exact h1
  · -- Trace: some result = some v
    cases heval
    cases hargs with | cons h1 _ => exact h1
  · -- ChooseData: match d with ...
    split at heval <;> {
      cases heval
      cases hargs with | cons h1 h2 =>
      cases h2 with | cons h3 h4 =>
      cases h4 with | cons h5 h6 =>
      cases h6 with | cons h7 h8 =>
      cases h8 with | cons h9 _ =>
      first | exact h9 | exact h7 | exact h5 | exact h3 | exact h1
    }
  · -- ChooseList (ConstDataList): some (if ...) = some v
    split at heval
    · cases heval
      cases hargs with | cons _ h2 => cases h2 with | cons h3 _ => exact h3
    · cases heval
      cases hargs with | cons h1 _ => exact h1
  · -- ChooseList (ConstList): same
    split at heval
    · cases heval
      cases hargs with | cons _ h2 => cases h2 with | cons h3 _ => exact h3
    · cases heval
      cases hargs with | cons h1 _ => exact h1
  · -- MkCons: match elem with ...
    split at heval
    · cases heval; exact ValueWellFormed.vcon _
    · cases heval
  · -- catch-all: none = some v
    cases heval

theorem evalBuiltin_preserves_wf {b : BuiltinFun}
    {args : List CekValue} {v : CekValue}
    (heval : evalBuiltin b args = some v)
    (hargs : ValueListWellFormed args) :
    ValueWellFormed v := by
  simp only [evalBuiltin] at heval
  cases hpt : evalBuiltinPassThrough b args with
  | some w =>
    simp [hpt] at heval
    cases heval
    exact evalBuiltinPassThrough_preserves_wf hpt hargs
  | none =>
    simp [hpt] at heval
    cases hec : extractConsts args with
    | none => simp [hec] at heval
    | some consts =>
      simp [hec] at heval
      cases hbc : evalBuiltinConst b consts with
      | none => simp [hbc] at heval
      | some c =>
        simp [hbc] at heval
        cases heval
        exact ValueWellFormed.vcon c

end EvalBuiltinWF

section StepPreservation

private theorem valueWellFormed_of_frame_arg {t : Term} {ρ : CekEnv}
    (h : FrameWellFormed (.arg t ρ)) :
    ∃ k, EnvWellFormed k ρ ∧ k ≤ ρ.length ∧ closedAt k t = true := by
  cases h with
  | arg henv hlen hclosed => exact ⟨_, henv, hlen, hclosed⟩

private theorem valueWellFormed_of_frame_funV {v : CekValue}
    (h : FrameWellFormed (.funV v)) : ValueWellFormed v := by
  cases h with | funV hv => exact hv

private theorem valueWellFormed_of_frame_applyArg {v : CekValue}
    (h : FrameWellFormed (.applyArg v)) : ValueWellFormed v := by
  cases h with | applyArg hv => exact hv

private theorem valueWellFormed_of_frame_constrField
    {tag : Nat} {done : List CekValue} {todo : List Term} {ρ : CekEnv}
    (h : FrameWellFormed (.constrField tag done todo ρ)) :
    ValueListWellFormed done ∧ ∃ k, EnvWellFormed k ρ ∧ k ≤ ρ.length ∧ closedAtList k todo = true := by
  cases h with
  | constrField _ hdone henv hlen htodo => exact ⟨hdone, _, henv, hlen, htodo⟩

private theorem valueWellFormed_of_frame_caseScrutinee
    {alts : List Term} {ρ : CekEnv}
    (h : FrameWellFormed (.caseScrutinee alts ρ)) :
    ∃ k, EnvWellFormed k ρ ∧ k ≤ ρ.length ∧ closedAtList k alts = true := by
  cases h with
  | caseScrutinee henv hlen halts => exact ⟨_, henv, hlen, halts⟩

theorem step_preserves_wf : ∀ (s : State),
    StateWellFormed s → StateWellFormed (step s) := by
  intro s hs
  match s with
  | .error => exact StateWellFormed.error
  | .halt v =>
    cases hs with
    | halt hv => exact StateWellFormed.halt hv

  | .compute π ρ t =>
    cases hs with
    | compute hπ henv hlen hclosed =>
    match t with
    | .Var n =>
      simp [closedAt] at hclosed
      cases hlookup : ρ.lookup n with
      | none =>
        have : step (.compute π ρ (.Var n)) = .error := by simp [step, hlookup]
        rw [this]; exact StateWellFormed.error
      | some v =>
        have hstep : step (.compute π ρ (.Var n)) = .ret π v := by simp [step, hlookup]
        rw [hstep]
        have hn : 0 < n := by
          cases n with
          | zero => cases ρ <;> simp [CekEnv.lookup] at hlookup
          | succ => omega
        have ⟨v', hl', hv'⟩ := envWellFormed_lookup _ henv hn hclosed
        rw [hl'] at hlookup; cases hlookup
        exact StateWellFormed.ret hπ hv'
    | .Constant (c, ty) =>
      simp only [step]
      exact StateWellFormed.ret hπ (ValueWellFormed.vcon c)
    | .Builtin b =>
      simp only [step]
      exact StateWellFormed.ret hπ
        (ValueWellFormed.vbuiltin b (expectedArgs b) ValueListWellFormed.nil)
    | .Lam name body =>
      simp only [step]
      simp [closedAt] at hclosed
      exact StateWellFormed.ret hπ (ValueWellFormed.vlam henv hlen hclosed)
    | .Delay body =>
      simp only [step]
      simp [closedAt] at hclosed
      exact StateWellFormed.ret hπ (ValueWellFormed.vdelay henv hlen hclosed)
    | .Apply f x =>
      simp only [step]
      simp [closedAt] at hclosed
      exact StateWellFormed.compute
        (StackWellFormed.cons (FrameWellFormed.arg henv hlen hclosed.2) hπ)
        henv hlen hclosed.1
    | .Force e =>
      simp only [step]
      simp [closedAt] at hclosed
      exact StateWellFormed.compute
        (StackWellFormed.cons FrameWellFormed.force hπ) henv hlen hclosed
    | .Constr tag fields =>
      simp only [step]
      simp [closedAt] at hclosed
      cases fields with
      | nil =>
        exact StateWellFormed.ret hπ
          (ValueWellFormed.vconstr tag ValueListWellFormed.nil)
      | cons m ms =>
        have hm := closedAtList_head hclosed
        have hms := closedAtList_tail hclosed
        exact StateWellFormed.compute
          (StackWellFormed.cons
            (FrameWellFormed.constrField tag ValueListWellFormed.nil henv hlen hms) hπ)
          henv hlen hm
    | .Case scrut alts =>
      simp only [step]
      simp [closedAt] at hclosed
      exact StateWellFormed.compute
        (StackWellFormed.cons (FrameWellFormed.caseScrutinee henv hlen hclosed.2) hπ)
        henv hlen hclosed.1
    | .Error =>
      simp only [step]
      exact StateWellFormed.error

  | .ret π v =>
    cases hs with
    | ret hπ hv =>
    match π with
    | [] =>
      simp only [step]
      exact StateWellFormed.halt hv
    | f :: π_rest =>
      cases hπ with
      | cons hf hπ_rest =>
      match f, v with
      -- force + VDelay
      | .force, .VDelay body ρ =>
        simp only [step]
        cases hv with
        | vdelay henv_d hlen_d hclosed_d =>
          exact StateWellFormed.compute hπ_rest henv_d hlen_d hclosed_d

      -- force + VBuiltin
      | .force, .VBuiltin b args ea =>
        simp only [step]
        cases hv with
        | vbuiltin _ _ hargs_wf =>
          cases hh : ea.head with
          | argQ =>
            simp
            cases ht : ea.tail with
            | some rest =>
              simp
              exact StateWellFormed.ret hπ_rest
                (ValueWellFormed.vbuiltin b rest hargs_wf)
            | none =>
              simp
              cases heb : evalBuiltin b args with
              | none => exact StateWellFormed.error
              | some w =>
                exact StateWellFormed.ret hπ_rest
                  (evalBuiltin_preserves_wf heb hargs_wf)
          | argV =>
            simp
            exact StateWellFormed.error

      -- force + other values
      | .force, .VCon _ | .force, .VLam _ _
      | .force, .VConstr _ _ =>
        simp only [step]; exact StateWellFormed.error

      -- arg frame
      | .arg t ρ_arg, _ =>
        simp only [step]
        obtain ⟨k_arg, henv_arg, hlen_arg, hclosed_arg⟩ := valueWellFormed_of_frame_arg hf
        exact StateWellFormed.compute
          (StackWellFormed.cons (FrameWellFormed.funV hv) hπ_rest)
          henv_arg hlen_arg hclosed_arg

      -- funV (VLam)
      | .funV (.VLam body ρ_lam), vx =>
        simp only [step]
        have hvlam := valueWellFormed_of_frame_funV hf
        cases hvlam with
        | vlam henv_lam hlen_lam hclosed_lam =>
          have henv_ext := envWellFormed_extend _ henv_lam hlen_lam hv
          exact StateWellFormed.compute hπ_rest henv_ext
            (by simp [CekEnv.extend, CekEnv.length]; omega) hclosed_lam

      -- funV (VBuiltin)
      | .funV (.VBuiltin b args ea), vx =>
        simp only [step]
        have hvb := valueWellFormed_of_frame_funV hf
        cases hvb with
        | vbuiltin _ _ hargs_wf =>
          cases hh : ea.head with
          | argV =>
            simp
            cases ht : ea.tail with
            | some rest =>
              simp
              exact StateWellFormed.ret hπ_rest
                (ValueWellFormed.vbuiltin b rest
                  (ValueListWellFormed.cons hv hargs_wf))
            | none =>
              simp
              cases heb : evalBuiltin b (vx :: args) with
              | none => exact StateWellFormed.error
              | some w =>
                exact StateWellFormed.ret hπ_rest
                  (evalBuiltin_preserves_wf heb (ValueListWellFormed.cons hv hargs_wf))
          | argQ =>
            simp
            exact StateWellFormed.error

      -- funV + other values
      | .funV (.VCon _), _
      | .funV (.VDelay _ _), _
      | .funV (.VConstr _ _), _ =>
        simp only [step]; exact StateWellFormed.error

      -- constrField with remaining todo
      | .constrField tag done (m :: ms) ρ_cf, _ =>
        simp only [step]
        obtain ⟨hdone_wf, k_cf, henv_cf, hlen_cf, htodo⟩ :=
          valueWellFormed_of_frame_constrField hf
        have hm := closedAtList_head htodo
        have hms := closedAtList_tail htodo
        exact StateWellFormed.compute
          (StackWellFormed.cons
            (FrameWellFormed.constrField tag
              (ValueListWellFormed.cons hv hdone_wf)
              henv_cf hlen_cf hms)
            hπ_rest)
          henv_cf hlen_cf hm

      -- constrField with empty todo
      | .constrField tag done [] _, _ =>
        simp only [step]
        obtain ⟨hdone_wf, _, _, _, _⟩ := valueWellFormed_of_frame_constrField hf
        exact StateWellFormed.ret hπ_rest
          (ValueWellFormed.vconstr tag
            (valueListWellFormed_reverse
              (ValueListWellFormed.cons hv hdone_wf)))

      -- applyArg + VLam
      | .applyArg vx, .VLam body ρ_lam =>
        simp only [step]
        have hvx := valueWellFormed_of_frame_applyArg hf
        cases hv with
        | vlam henv_lam hlen_lam hclosed_lam =>
          have henv_ext := envWellFormed_extend _ henv_lam hlen_lam hvx
          exact StateWellFormed.compute hπ_rest henv_ext
            (by simp [CekEnv.extend, CekEnv.length]; omega) hclosed_lam

      -- applyArg + VBuiltin
      | .applyArg vx, .VBuiltin b args ea =>
        simp only [step]
        have hvx := valueWellFormed_of_frame_applyArg hf
        cases hv with
        | vbuiltin _ _ hargs_wf =>
          cases hh : ea.head with
          | argV =>
            simp
            cases ht : ea.tail with
            | some rest =>
              simp
              exact StateWellFormed.ret hπ_rest
                (ValueWellFormed.vbuiltin b rest
                  (ValueListWellFormed.cons hvx hargs_wf))
            | none =>
              simp
              cases heb : evalBuiltin b (vx :: args) with
              | none => exact StateWellFormed.error
              | some w =>
                exact StateWellFormed.ret hπ_rest
                  (evalBuiltin_preserves_wf heb (ValueListWellFormed.cons hvx hargs_wf))
          | argQ =>
            simp
            exact StateWellFormed.error

      -- applyArg + other values
      | .applyArg _, .VCon _
      | .applyArg _, .VDelay _ _
      | .applyArg _, .VConstr _ _ =>
        simp only [step]; exact StateWellFormed.error

      -- caseScrutinee + VConstr
      | .caseScrutinee alts ρ_cs, .VConstr tag fields =>
        simp only [step]
        obtain ⟨k_cs, henv_cs, hlen_cs, halts⟩ :=
          valueWellFormed_of_frame_caseScrutinee hf
        cases hv with
        | vconstr _ hfields_wf =>
          cases halt : alts[tag]? with
          | none => exact StateWellFormed.error
          | some alt =>
            have halt_closed := closedAtList_getElem? halts halt
            exact StateWellFormed.compute
              (stackWellFormed_applyArgFrames hfields_wf hπ_rest)
              henv_cs hlen_cs halt_closed

      -- caseScrutinee + VCon
      | .caseScrutinee alts ρ_cs, .VCon c =>
        simp only [step]
        obtain ⟨k_cs, henv_cs, hlen_cs, halts⟩ :=
          valueWellFormed_of_frame_caseScrutinee hf
        cases htag : constToTagAndFields c with
        | none => exact StateWellFormed.error
        | some val =>
          obtain ⟨tag, numCtors, fields⟩ := val
          simp
          split
          · exact StateWellFormed.error
          · cases halt : alts[tag]? with
            | none => exact StateWellFormed.error
            | some alt =>
              have halt_closed := closedAtList_getElem? halts halt
              have hfields_wf : ValueListWellFormed fields := by
                have := constToTagAndFields_fields_wf c
                rw [htag] at this; exact this
              exact StateWellFormed.compute
                (stackWellFormed_applyArgFrames hfields_wf hπ_rest)
                henv_cs hlen_cs halt_closed

      -- caseScrutinee + other values
      | .caseScrutinee _ _, .VLam _ _
      | .caseScrutinee _ _, .VDelay _ _
      | .caseScrutinee _ _, .VBuiltin _ _ _ =>
        simp only [step]; exact StateWellFormed.error

theorem steps_preserves_wf : ∀ (n : Nat) (s : State),
    StateWellFormed s → StateWellFormed (steps n s) := by
  intro n
  induction n with
  | zero => intro s hs; exact hs
  | succ m ih =>
    intro s hs
    simp [steps]
    exact ih (step s) (step_preserves_wf s hs)

theorem halt_value_wf {n : Nat} {s : State} {v : CekValue}
    (hs : StateWellFormed s) (hhalt : steps n s = .halt v) :
    ValueWellFormed v := by
  have := steps_preserves_wf n s hs
  rw [hhalt] at this
  cases this with
  | halt hv => exact hv

end StepPreservation

end Moist.Verified.StepWellFormed
