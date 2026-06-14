import Moist.Verified.SmallStep.Invariant

/-! # Canonicality of CEK values and the discharge

`discharge` *canonicalises* the decorative parts of a term that the CEK machine
discards: every `Lam`'s binder label becomes `0`, and every `Constant`'s type
annotation becomes the canonical `constType c`.  Consequently the discharge of a
CEK value is always in canonical form, and for the forward simulation's
administrative steps (`compute (con …) → ret`, `compute (lam …) → ret`) to
preserve the discharged term we need the *source* terms to be canonical too.

`Canonical`/`CanonValue` track exactly this, in parallel to closedness.  The CEK
preserves canonicality (`step_preserves_canon`), the initial state of a canonical
term is canonical (`init_canon`), and a canonical value discharges to a canonical
term (`discharge_canonical`).
-/

namespace Moist.Verified.SmallStep

open Moist.Plutus.Term (Term Const BuiltinFun constType)
open Moist.CEK
open Moist.Verified (substTerm renameTerm renameTermList substTermList shiftRename liftRename)

/-! ## The canonical-form predicate -/

mutual
  /-- A term is *canonical* when every `Lam` uses the canonical binder label `0`
      and every `Constant`'s annotation is `constType` of its value — exactly the
      normalisation `discharge` performs. -/
  def Canonical : Term → Prop
    | .Var _ => True
    | .Constant (c, bt) => bt = constType c
    | .Builtin _ => True
    | .Lam name body => name = 0 ∧ Canonical body
    | .Apply f x => Canonical f ∧ Canonical x
    | .Force e => Canonical e
    | .Delay e => Canonical e
    | .Constr _ args => CanonicalList args
    | .Case s alts => Canonical s ∧ CanonicalList alts
    | .Error => True
  termination_by t => sizeOf t

  def CanonicalList : List Term → Prop
    | [] => True
    | t :: ts => Canonical t ∧ CanonicalList ts
  termination_by ts => sizeOf ts
end

theorem canonicalList_forall : ∀ {ts : List Term}, CanonicalList ts → ∀ t ∈ ts, Canonical t
  | [], _, _, hmem => by cases hmem
  | t :: ts, h, u, hmem => by
    rw [CanonicalList] at h
    cases hmem with
    | head => exact h.1
    | tail _ h' => exact canonicalList_forall h.2 u h'

theorem forall_canonicalList : ∀ {ts : List Term}, (∀ t ∈ ts, Canonical t) → CanonicalList ts
  | [], _ => by rw [CanonicalList]; trivial
  | t :: ts, h => by
    rw [CanonicalList]
    exact ⟨h t List.mem_cons_self, forall_canonicalList (fun x hx => h x (List.mem_cons_of_mem t hx))⟩

/-! ## Canonicality under renaming and substitution -/

mutual
  theorem renameTerm_canonical : ∀ {σ : Nat → Nat} {t : Term}, Canonical t →
      Canonical (renameTerm σ t)
    | _, .Var _, _ => by simp only [renameTerm, Canonical]
    | _, .Constant _, h => by simp only [renameTerm]; exact h
    | _, .Builtin _, _ => by simp only [renameTerm, Canonical]
    | _, .Lam name body, h => by
      rw [Canonical] at h; rw [renameTerm, Canonical]; exact ⟨h.1, renameTerm_canonical h.2⟩
    | _, .Apply f x, h => by
      rw [Canonical] at h; rw [renameTerm, Canonical]
      exact ⟨renameTerm_canonical h.1, renameTerm_canonical h.2⟩
    | _, .Force e, h => by rw [Canonical] at h; rw [renameTerm, Canonical]; exact renameTerm_canonical h
    | _, .Delay e, h => by rw [Canonical] at h; rw [renameTerm, Canonical]; exact renameTerm_canonical h
    | _, .Constr _ args, h => by rw [Canonical] at h; rw [renameTerm, Canonical]; exact renameTermList_canonical h
    | _, .Case s alts, h => by
      rw [Canonical] at h; rw [renameTerm, Canonical]
      exact ⟨renameTerm_canonical h.1, renameTermList_canonical h.2⟩
    | _, .Error, _ => by simp only [renameTerm, Canonical]
  termination_by _ t _ => sizeOf t

  theorem renameTermList_canonical : ∀ {σ : Nat → Nat} {ts : List Term}, CanonicalList ts →
      CanonicalList (renameTermList σ ts)
    | _, [], _ => by rw [renameTermList]; trivial
    | _, t :: ts, h => by
      rw [CanonicalList] at h; rw [renameTermList, CanonicalList]
      exact ⟨renameTerm_canonical h.1, renameTermList_canonical h.2⟩
  termination_by _ ts _ => sizeOf ts
end

mutual
  theorem substTerm_canonical : ∀ {pos : Nat} {r t : Term}, Canonical r → Canonical t →
      Canonical (substTerm pos r t)
    | pos, r, .Var n, hr, _ => by
      rw [substTerm_var]
      by_cases h1 : n = pos
      · rw [if_pos h1]; exact hr
      · rw [if_neg h1]
        by_cases h2 : n > pos
        · rw [if_pos h2]; simp only [Canonical]
        · rw [if_neg h2]; simp only [Canonical]
    | _, _, .Constant _, _, h => by simp only [substTerm]; exact h
    | _, _, .Builtin _, _, _ => by simp only [substTerm, Canonical]
    | pos, r, .Lam name body, hr, h => by
      rw [Canonical] at h; rw [substTerm, Canonical]
      exact ⟨h.1, substTerm_canonical (renameTerm_canonical hr) h.2⟩
    | _, _, .Apply f x, hr, h => by
      rw [Canonical] at h; rw [substTerm, Canonical]
      exact ⟨substTerm_canonical hr h.1, substTerm_canonical hr h.2⟩
    | _, _, .Force e, hr, h => by rw [Canonical] at h; rw [substTerm, Canonical]; exact substTerm_canonical hr h
    | _, _, .Delay e, hr, h => by rw [Canonical] at h; rw [substTerm, Canonical]; exact substTerm_canonical hr h
    | _, _, .Constr _ args, hr, h => by
      rw [Canonical] at h; rw [substTerm, Canonical]; exact substTermList_canonical hr h
    | _, _, .Case s alts, hr, h => by
      rw [Canonical] at h; rw [substTerm, Canonical]
      exact ⟨substTerm_canonical hr h.1, substTermList_canonical hr h.2⟩
    | _, _, .Error, _, _ => by simp only [substTerm, Canonical]
  termination_by _ _ t _ _ => sizeOf t

  theorem substTermList_canonical : ∀ {pos : Nat} {r : Term} {ts : List Term}, Canonical r →
      CanonicalList ts → CanonicalList (substTermList pos r ts)
    | _, _, [], _, _ => by rw [substTermList]; trivial
    | _, _, t :: ts, hr, h => by
      rw [CanonicalList] at h; rw [substTermList, CanonicalList]
      exact ⟨substTerm_canonical hr h.1, substTermList_canonical hr h.2⟩
  termination_by _ _ ts _ _ => sizeOf ts
end

/-! ## Canonical CEK values -/

mutual
  /-- A CEK value whose closure bodies are canonical and whose stored values are
      canonical — equivalently, a value discharging to a canonical term. -/
  inductive CanonValue : CekValue → Prop
    | vcon {c} : CanonValue (.VCon c)
    | vlam {body env} : Canonical body → CanonEnv env → CanonValue (.VLam body env)
    | vdelay {body env} : Canonical body → CanonEnv env → CanonValue (.VDelay body env)
    | vconstr {tag fields} : CanonValueList fields → CanonValue (.VConstr tag fields)
    | vbuiltin {b vargs ea} : CanonValueList vargs → CanonValue (.VBuiltin b vargs ea)

  inductive CanonValueList : List CekValue → Prop
    | nil : CanonValueList []
    | cons {v vs} : CanonValue v → CanonValueList vs → CanonValueList (v :: vs)

  inductive CanonEnv : CekEnv → Prop
    | nil : CanonEnv .nil
    | cons {v rest} : CanonValue v → CanonEnv rest → CanonEnv (.cons v rest)
end

theorem canonList_mem : ∀ {vs : List CekValue}, CanonValueList vs → ∀ {v}, v ∈ vs → CanonValue v
  | _, .nil, _, hmem => by cases hmem
  | _, .cons hv hvs, _, hmem => by
    cases hmem with
    | head => exact hv
    | tail _ h => exact canonList_mem hvs h

theorem canonEnv_lookup : ∀ {ρ : CekEnv} {n : Nat} {v : CekValue},
    CanonEnv ρ → ρ.lookup n = some v → CanonValue v
  | .nil, _, _, _, h => by simp [CekEnv.lookup] at h
  | .cons w rest, 0, _, _, h => by simp [CekEnv.lookup] at h
  | .cons w rest, 1, v, .cons hw _, h => by
    simp only [CekEnv.lookup, Option.some.injEq] at h; exact h ▸ hw
  | .cons w rest, n + 2, v, .cons _ hrest, h => by
    simp only [CekEnv.lookup] at h; exact canonEnv_lookup hrest h

/-! ## Canonical values discharge to canonical terms -/

theorem dischargeSpine_canonical : ∀ {steps : List ArgKind} {dargs : List Term} {acc : Term},
    Canonical acc → (∀ t ∈ dargs, Canonical t) → Canonical (dischargeSpine acc steps dargs)
  | [], _, _, hacc, _ => by rw [dischargeSpine]; exact hacc
  | .argQ :: rest, dargs, acc, hacc, hd => by
    show Canonical (dischargeSpine (.Force acc) rest dargs)
    exact dischargeSpine_canonical (by rw [Canonical]; exact hacc) hd
  | .argV :: rest, [], acc, hacc, _ => by rw [dischargeSpine]; exact hacc
  | .argV :: rest, a :: as, acc, hacc, hd => by
    show Canonical (dischargeSpine (.Apply acc a) rest as)
    refine dischargeSpine_canonical ?_ (fun t ht => hd t (List.mem_cons_of_mem a ht))
    rw [Canonical]; exact ⟨hacc, hd a List.mem_cons_self⟩

mutual
  theorem discharge_canonical : ∀ {v : CekValue}, CanonValue v → Canonical (discharge v)
    | _, .vcon => by rw [discharge, Canonical]
    | _, .vlam hb he => by
      rw [discharge, Canonical]; exact ⟨rfl, dischargeEnv_canonical 1 he hb⟩
    | _, .vdelay hb he => by
      rw [discharge, Canonical]; exact dischargeEnv_canonical 0 he hb
    | _, .vconstr hf => by rw [discharge, Canonical]; exact dischargeList_canonical hf
    | _, .vbuiltin ha => by
      rw [discharge]
      refine dischargeSpine_canonical (by rw [Canonical]; trivial) (fun t ht => ?_)
      exact canonicalList_forall (dischargeList_canonical ha) t (List.mem_reverse.mp ht)

  theorem dischargeList_canonical : ∀ {vs : List CekValue}, CanonValueList vs →
      CanonicalList (dischargeList vs)
    | _, .nil => by rw [dischargeList, CanonicalList]; trivial
    | _, .cons hv hvs => by
      rw [dischargeList, CanonicalList]; exact ⟨discharge_canonical hv, dischargeList_canonical hvs⟩

  theorem dischargeEnv_canonical : ∀ (d : Nat) {env : CekEnv} {body : Term}, CanonEnv env →
      Canonical body → Canonical (dischargeEnv env d body)
    | _, _, _, .nil, hb => by rw [dischargeEnv]; exact hb
    | d, _, _, .cons hv hrest, hb => by
      rw [dischargeEnv]
      exact dischargeEnv_canonical d hrest (substTerm_canonical (discharge_canonical hv) hb)
end


/-! ## Builtin evaluation preserves canonicality -/

theorem allVcon_canon : (fields : List CekValue) → (∀ v ∈ fields, ∃ c, v = .VCon c) →
    CanonValueList fields
  | [], _ => .nil
  | v :: rest, h =>
    have ⟨_, hcv⟩ := h v (List.mem_cons_self)
    hcv ▸ .cons .vcon (allVcon_canon rest (fun x hx => h x (List.mem_cons_of_mem v hx)))

theorem constToTagAndFields_fields_canon {c : Const} {tag numCtors : Nat} {fields : List CekValue}
    (h : constToTagAndFields c = some (tag, numCtors, fields)) : CanonValueList fields := by
  have hvc := constToTagAndFields_fields_vcon c
  rw [h] at hvc
  exact allVcon_canon fields hvc

theorem evalBuiltinPassThrough_preserves_canon {b : BuiltinFun} {args : List CekValue}
    {v : CekValue} (heval : evalBuiltinPassThrough b args = some v) (hargs : CanonValueList args) :
    CanonValue v := by
  simp only [evalBuiltinPassThrough] at heval
  split at heval
  · split at heval
    · cases heval; cases hargs with | cons _ h2 => cases h2 with | cons h3 _ => exact h3
    · cases heval; cases hargs with | cons h1 _ => exact h1
  · cases heval; cases hargs with | cons h1 _ => exact h1
  · cases heval; cases hargs with | cons h1 _ => exact h1
  · split at heval <;>
      · cases heval
        cases hargs with | cons h1 h2 =>
        cases h2 with | cons h3 h4 =>
        cases h4 with | cons h5 h6 =>
        cases h6 with | cons h7 h8 =>
        cases h8 with | cons h9 _ =>
        first | exact h9 | exact h7 | exact h5 | exact h3 | exact h1
  · split at heval
    · cases heval; cases hargs with | cons _ h2 => cases h2 with | cons h3 _ => exact h3
    · cases heval; cases hargs with | cons h1 _ => exact h1
  · split at heval
    · cases heval; cases hargs with | cons _ h2 => cases h2 with | cons h3 _ => exact h3
    · cases heval; cases hargs with | cons h1 _ => exact h1
  · split at heval
    · cases heval; exact .vcon
    · cases heval
  · cases heval

theorem evalBuiltin_preserves_canon {b : BuiltinFun} {args : List CekValue} {v : CekValue}
    (heval : evalBuiltin b args = some v) (hargs : CanonValueList args) : CanonValue v := by
  simp only [evalBuiltin] at heval
  cases hpt : evalBuiltinPassThrough b args with
  | some w =>
    simp [hpt] at heval; cases heval
    exact evalBuiltinPassThrough_preserves_canon hpt hargs
  | none =>
    simp [hpt] at heval
    cases hec : extractConsts args with
    | none => simp [hec] at heval
    | some consts =>
      simp [hec] at heval
      cases hbc : evalBuiltinConst b consts with
      | none => simp [hbc] at heval
      | some c => simp [hbc] at heval; cases heval; exact .vcon

/-! ## The canonical-state invariant -/

def CanonFrame : Frame → Prop
  | .force => True
  | .arg M ρ => Canonical M ∧ CanonEnv ρ
  | .funV vf => CanonValue vf
  | .applyArg vx => CanonValue vx
  | .constrField _ done todo ρ => CanonValueList done ∧ (∀ m ∈ todo, Canonical m) ∧ CanonEnv ρ
  | .caseScrutinee alts ρ => (∀ m ∈ alts, Canonical m) ∧ CanonEnv ρ

def CanonStack (π : Stack) : Prop := ∀ f ∈ π, CanonFrame f

def CanonState : State → Prop
  | .compute π ρ M => Canonical M ∧ CanonEnv ρ ∧ CanonStack π
  | .ret π v => CanonValue v ∧ CanonStack π
  | .halt v => CanonValue v
  | .error => True

theorem canonStack_nil : CanonStack [] := fun _ h => by cases h

theorem canonStack_cons {f : Frame} {π : Stack} (hf : CanonFrame f) (hπ : CanonStack π) :
    CanonStack (f :: π) := by
  intro g hg; rcases List.mem_cons.mp hg with rfl | hg
  · exact hf
  · exact hπ g hg

theorem canonStack_head {f : Frame} {π : Stack} (h : CanonStack (f :: π)) : CanonFrame f :=
  h f List.mem_cons_self

theorem canonStack_tail {f : Frame} {π : Stack} (h : CanonStack (f :: π)) : CanonStack π :=
  fun g hg => h g (List.mem_cons_of_mem f hg)

theorem canonValueList_mem_iff {l : List CekValue} : CanonValueList l ↔ ∀ v ∈ l, CanonValue v := by
  constructor
  · intro h v hv; exact canonList_mem h hv
  · intro h
    induction l with
    | nil => exact .nil
    | cons a as ih =>
      exact .cons (h a List.mem_cons_self) (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))

theorem canonValueList_reverse {l : List CekValue} (h : CanonValueList l) :
    CanonValueList l.reverse := by
  rw [canonValueList_mem_iff] at h ⊢; intro x hx; exact h x (by simpa using hx)

theorem canonStack_applyArgFrames {fields : List CekValue} {s : Stack}
    (hf : CanonValueList fields) (hs : CanonStack s) :
    CanonStack (fields.map Frame.applyArg ++ s) := by
  intro g hg
  rw [List.mem_append] at hg
  rcases hg with hg | hg
  · rw [List.mem_map] at hg
    obtain ⟨v, hv, rfl⟩ := hg
    exact canonList_mem hf hv
  · exact hs g hg

/-! ## `step` preserves canonicality -/

set_option maxHeartbeats 1000000 in
theorem step_preserves_canon : ∀ {s : State}, CanonState s → CanonState (step s)
  | .error, _ => trivial
  | .halt v, h => h
  | .compute π ρ M, h => by
    obtain ⟨hM, hρ, hπ⟩ := h
    cases M with
    | Var n =>
      simp only [step]
      cases hl : ρ.lookup n with
      | none => trivial
      | some v => exact ⟨canonEnv_lookup hρ hl, hπ⟩
    | Constant c => exact ⟨.vcon, hπ⟩
    | Builtin b => exact ⟨.vbuiltin .nil, hπ⟩
    | Lam name body =>
      rw [Canonical] at hM
      exact ⟨.vlam hM.2 hρ, hπ⟩
    | Delay body =>
      rw [Canonical] at hM
      exact ⟨.vdelay hM hρ, hπ⟩
    | Force e =>
      rw [Canonical] at hM
      exact ⟨hM, hρ, canonStack_cons trivial hπ⟩
    | Apply f x =>
      rw [Canonical] at hM
      exact ⟨hM.1, hρ, canonStack_cons ⟨hM.2, hρ⟩ hπ⟩
    | Constr tag args =>
      cases args with
      | nil => exact ⟨.vconstr .nil, hπ⟩
      | cons m ms =>
        rw [Canonical, CanonicalList] at hM
        refine ⟨hM.1, hρ, canonStack_cons ⟨.nil, ?_, hρ⟩ hπ⟩
        intro k hk; exact canonicalList_forall hM.2 k hk
    | Case scrut alts =>
      rw [Canonical] at hM
      refine ⟨hM.1, hρ, canonStack_cons ⟨?_, hρ⟩ hπ⟩
      intro m hm; exact canonicalList_forall hM.2 m hm
    | Error => trivial
  | .ret π v, h => by
    obtain ⟨hv, hπ⟩ := h
    cases π with
    | nil => exact hv
    | cons f s =>
      have hf := canonStack_head hπ
      have hs := canonStack_tail hπ
      cases f with
      | force =>
        cases v with
        | VDelay body ρ' =>
          cases hv with
          | vdelay hb he => simp only [step]; exact ⟨hb, he, hs⟩
        | VBuiltin b args ea =>
          cases hv with
          | vbuiltin ha =>
            simp only [step]
            cases ea with
            | one k =>
              cases k with
              | argQ =>
                simp only [ExpectedArgs.head, ExpectedArgs.tail]
                cases hev : evalBuiltin b args with
                | none => trivial
                | some w => exact ⟨evalBuiltin_preserves_canon hev ha, hs⟩
              | argV => trivial
            | more k rest =>
              cases k with
              | argQ =>
                simp only [ExpectedArgs.head, ExpectedArgs.tail]
                exact ⟨.vbuiltin ha, hs⟩
              | argV => trivial
        | VCon c => trivial
        | VLam body ρ' => trivial
        | VConstr tag fields => trivial
      | arg M ρ' =>
        obtain ⟨hMc, hρ'⟩ := hf
        simp only [step]
        exact ⟨hMc, hρ', canonStack_cons hv hs⟩
      | funV vf =>
        cases vf with
        | VLam body ρ' =>
          cases hf with
          | vlam hb he => simp only [step]; exact ⟨hb, .cons hv he, hs⟩
        | VBuiltin b args ea =>
          cases hf with
          | vbuiltin ha =>
            simp only [step]
            cases ea with
            | one k =>
              cases k with
              | argV =>
                simp only [ExpectedArgs.head, ExpectedArgs.tail]
                cases hev : evalBuiltin b (v :: args) with
                | none => trivial
                | some w => exact ⟨evalBuiltin_preserves_canon hev (.cons hv ha), hs⟩
              | argQ => trivial
            | more k rest =>
              cases k with
              | argV =>
                simp only [ExpectedArgs.head, ExpectedArgs.tail]
                exact ⟨.vbuiltin (.cons hv ha), hs⟩
              | argQ => trivial
        | VCon c => simp only [step]; trivial
        | VDelay body ρ' => simp only [step]; trivial
        | VConstr tag fields => simp only [step]; trivial
      | applyArg vx =>
        cases v with
        | VLam body ρ' =>
          cases hv with
          | vlam hb he => simp only [step]; exact ⟨hb, .cons hf he, hs⟩
        | VBuiltin b args ea =>
          cases hv with
          | vbuiltin ha =>
            simp only [step]
            cases ea with
            | one k =>
              cases k with
              | argV =>
                simp only [ExpectedArgs.head, ExpectedArgs.tail]
                cases hev : evalBuiltin b (vx :: args) with
                | none => trivial
                | some w => exact ⟨evalBuiltin_preserves_canon hev (.cons hf ha), hs⟩
              | argQ => trivial
            | more k rest =>
              cases k with
              | argV =>
                simp only [ExpectedArgs.head, ExpectedArgs.tail]
                exact ⟨.vbuiltin (.cons hf ha), hs⟩
              | argQ => trivial
        | VCon c => simp only [step]; trivial
        | VDelay body ρ' => simp only [step]; trivial
        | VConstr tag fields => simp only [step]; trivial
      | constrField tag done todo ρ' =>
        obtain ⟨hdone, htodo, hρ'⟩ := hf
        cases todo with
        | nil =>
          simp only [step]
          exact ⟨.vconstr (canonValueList_reverse (.cons hv hdone)), hs⟩
        | cons m ms =>
          simp only [step]
          refine ⟨htodo m List.mem_cons_self, hρ', canonStack_cons ⟨.cons hv hdone, ?_, hρ'⟩ hs⟩
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
              exact ⟨halts alt (List.mem_of_getElem? halt), hρ',
                canonStack_applyArgFrames hfields hs⟩
        | VCon c =>
          simp only [step]
          rcases hc : constToTagAndFields c with _ | ⟨tag, numCtors, fields⟩
          · trivial
          · rw [apply_ite CanonState]
            split
            · trivial
            · cases halt : alts[tag]? with
              | none => trivial
              | some alt =>
                exact ⟨halts alt (List.mem_of_getElem? halt), hρ',
                  canonStack_applyArgFrames (constToTagAndFields_fields_canon hc) hs⟩
        | VLam body ρ'' => simp only [step]; trivial
        | VDelay body ρ'' => simp only [step]; trivial
        | VBuiltin b args ea => simp only [step]; trivial

theorem init_canon {t : Term} (ht : Canonical t) : CanonState (init t) :=
  ⟨ht, .nil, canonStack_nil⟩

end Moist.Verified.SmallStep
