import Moist.Verified.Definitions
import Moist.Verified.SmallStep.Adequacy

/-! # Big-step (definitional-interpreter) semantics for UPLC, proven ≡ CEK

An environment-based, fuel-bounded big-step evaluator over the de Bruijn
`Moist.Plutus.Term.Term`, using the *same* runtime values (`Moist.CEK.CekValue`),
environment (`CekEnv`), and builtin denotation (`evalBuiltin`) as the CEK machine.

Proven **equivalent in both directions** to `Moist.CEK.step` /
`Moist.Verified.Equivalence.steps` on the `Constr`/`Case`-free fragment (`PureTm`) — the
full λ-calculus-with-builtins every Plutus validator compiles into. All results are
axiom-clean (only Lean's standard `propext`/`Classical.choice`/`Quot.sound`):

* `bigEval_sound`    : whatever `bigEval` computes, the CEK halts at (all terms);
  the iterated forward simulation `evalFwd`/`applyFwd`/`forceFwd`.
* `bigEval_complete` : if the CEK halts at `v`, `bigEval` computes `v` (closed `PureTm`);
  via the CEK well-bracketing lemma `firstExit` (a computation under base stack `S`
  returns to `ret S vt` before popping below `S`), the backward simulation `evalBwd`
  (strong recursion on run length), value-purity preservation, and fuel monotonicity.
* `bigEval_iff_halt` : the full ↔, for closed `PureTm` terms.

Both `bigEval` and the CEK invoke the *same* `evalBuiltin`, so they agree on builtins
by construction. The builtin denotations are additionally exposed to Blaster as `@[simp]`
axioms (trusted denotations, à la `PlutusCore.Integer.addInteger_rfl`) so the optimizer
need not unfold the monolithic `evalBuiltin`; the `≡ CEK` results do NOT depend on them.
-/

namespace Moist.Verified.BigStep

open Moist.Plutus.Term (Term Const BuiltinType BuiltinFun)
open Moist.CEK
open Moist.Verified.Equivalence (steps Reaches)

/-! ## The evaluator (mutual, fuel-structural) -/

mutual
  /-- Big-step evaluation of `t` in environment `ρ`. `Constr`/`Case` are out of the
      covered fragment (return `none`). -/
  def bigEval : Nat → CekEnv → Term → Option CekValue
    | 0, _, _ => none
    | _ + 1, ρ, .Var k => ρ.lookup k
    | _ + 1, _, .Constant (c, _) => some (.VCon c)
    | _ + 1, _, .Builtin b => some (.VBuiltin b [] (expectedArgs b))
    | _ + 1, ρ, .Lam _ body => some (.VLam body ρ)
    | _ + 1, ρ, .Delay body => some (.VDelay body ρ)
    | n + 1, ρ, .Apply f a =>
        match bigEval n ρ f with
        | some vf => match bigEval n ρ a with
                     | some va => applyVal n vf va
                     | none => none
        | none => none
    | n + 1, ρ, .Force t =>
        match bigEval n ρ t with
        | some vt => forceVal n vt
        | none => none
    | _ + 1, _, .Constr _ _ => none
    | _ + 1, _, .Case _ _ => none
    | _ + 1, _, .Error => none
  termination_by n => n

  /-- Apply a runtime value to an argument value (β / builtin saturation). -/
  def applyVal : Nat → CekValue → CekValue → Option CekValue
    | 0, _, _ => none
    | n + 1, .VLam body ρ, va => bigEval n (ρ.extend va) body
    | _ + 1, .VBuiltin b args ea, va =>
        match ea.head with
        | .argV => match ea.tail with
                   | some rest => some (.VBuiltin b (va :: args) rest)
                   | none => evalBuiltin b (va :: args)
        | .argQ => none
    | _ + 1, _, _ => none
  termination_by n => n

  /-- Force a runtime value (delay / builtin force). -/
  def forceVal : Nat → CekValue → Option CekValue
    | 0, _ => none
    | n + 1, .VDelay body ρ => bigEval n ρ body
    | _ + 1, .VBuiltin b args ea =>
        match ea.head with
        | .argQ => match ea.tail with
                   | some rest => some (.VBuiltin b args rest)
                   | none => evalBuiltin b args
        | .argV => none
    | _ + 1, _ => none
  termination_by n => n
end

/-! ## Reachability plumbing for the CEK -/

theorem steps_succ (n : Nat) (s : State) : steps (n + 1) s = steps n (step s) := rfl

theorem steps_add (m n : Nat) (s : State) : steps (m + n) s = steps n (steps m s) := by
  induction m generalizing s with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih => rw [Nat.succ_add, steps_succ, steps_succ, ih]

theorem reaches_refl (s : State) : Reaches s s := ⟨0, rfl⟩

theorem reaches_step {s s' : State} (h : Reaches (step s) s') : Reaches s s' := by
  obtain ⟨n, hn⟩ := h; exact ⟨n + 1, by rw [steps]; exact hn⟩

theorem reaches_trans {a b c : State} (h1 : Reaches a b) (h2 : Reaches b c) : Reaches a c := by
  obtain ⟨m, hm⟩ := h1; obtain ⟨n, hn⟩ := h2
  exact ⟨m + n, by rw [steps_add, hm, hn]⟩

/-- A single CEK transition gives a one-step reachability. -/
theorem one_step {s0 s1 : State} (h : step s0 = s1) : Reaches s0 s1 := ⟨1, h⟩

/-- `steps 1` is one `step`. -/
theorem steps_one' {st st' : State} (h : step st = st') : steps 1 st = st' := by
  rw [steps_succ, steps]; exact h

/-! ## Forward simulation: big-step result ⟹ the CEK reaches it -/

mutual
  /-- If `bigEval` produces `v`, the CEK computing `t` (under any stack `s`)
      returns `v` to that stack. -/
  theorem evalFwd : ∀ {n : Nat} {ρ : CekEnv} {t : Term} {v : CekValue},
      bigEval n ρ t = some v → ∀ s, Reaches (.compute s ρ t) (.ret s v)
    | 0, _, _, _, h, _ => by simp [bigEval] at h
    | n + 1, ρ, .Var k, v, h, s => by
        have hl : ρ.lookup k = some v := by simpa [bigEval] using h
        exact one_step (by simp only [step, hl])
    | n + 1, ρ, .Constant cb, v, h, s => by
        obtain ⟨c, bt⟩ := cb
        have hv : (CekValue.VCon c) = v := by simpa [bigEval] using h
        subst hv; exact one_step rfl
    | n + 1, ρ, .Builtin b, v, h, s => by
        have hv : (CekValue.VBuiltin b [] (expectedArgs b)) = v := by simpa [bigEval] using h
        subst hv; exact one_step rfl
    | n + 1, ρ, .Lam name body, v, h, s => by
        have hv : (CekValue.VLam body ρ) = v := by simpa [bigEval] using h
        subst hv; exact one_step rfl
    | n + 1, ρ, .Delay body, v, h, s => by
        have hv : (CekValue.VDelay body ρ) = v := by simpa [bigEval] using h
        subst hv; exact one_step rfl
    | n + 1, ρ, .Apply f a, v, h, s => by
        cases hf : bigEval n ρ f with
        | none => simp [bigEval, hf] at h
        | some vf =>
          cases ha : bigEval n ρ a with
          | none => simp [bigEval, hf, ha] at h
          | some va =>
            simp only [bigEval, hf, ha] at h
            refine reaches_trans (one_step rfl) (reaches_trans (evalFwd hf (.arg a ρ :: s)) ?_)
            refine reaches_trans (one_step rfl) (reaches_trans (evalFwd ha (.funV vf :: s)) ?_)
            exact applyFwd h s
    | n + 1, ρ, .Force t, v, h, s => by
        cases ht : bigEval n ρ t with
        | none => simp [bigEval, ht] at h
        | some vt =>
          simp only [bigEval, ht] at h
          refine reaches_trans (one_step rfl) (reaches_trans (evalFwd ht (.force :: s)) ?_)
          exact forceFwd h s
    | n + 1, _, .Constr _ _, _, h, _ => by simp [bigEval] at h
    | n + 1, _, .Case _ _, _, h, _ => by simp [bigEval] at h
    | n + 1, _, .Error, _, h, _ => by simp [bigEval] at h
  termination_by n => n

  /-- Applying `vf` (held in a `funV` frame) to the returned `va`. -/
  theorem applyFwd : ∀ {n : Nat} {vf va v : CekValue},
      applyVal n vf va = some v → ∀ s, Reaches (.ret (.funV vf :: s) va) (.ret s v)
    | 0, _, _, _, h, _ => by simp [applyVal] at h
    | n + 1, vf, va, v, h, s => by
        cases vf with
        | VLam body ρ =>
          have hb : bigEval n (ρ.extend va) body = some v := by simpa [applyVal] using h
          exact reaches_trans (one_step rfl) (evalFwd hb s)
        | VBuiltin b args ea =>
          cases ea with
          | one k =>
            cases k with
            | argV =>
              have he : evalBuiltin b (va :: args) = some v := by
                simpa [applyVal, ExpectedArgs.head, ExpectedArgs.tail] using h
              exact one_step (by simp only [step, ExpectedArgs.head, ExpectedArgs.tail, he])
            | argQ => simp [applyVal, ExpectedArgs.head] at h
          | more k rest =>
            cases k with
            | argV =>
              have hv : (CekValue.VBuiltin b (va :: args) rest) = v := by
                simpa [applyVal, ExpectedArgs.head, ExpectedArgs.tail] using h
              subst hv
              exact one_step (by simp only [step, ExpectedArgs.head, ExpectedArgs.tail])
            | argQ => simp [applyVal, ExpectedArgs.head] at h
        | VCon _ => simp [applyVal] at h
        | VDelay _ _ => simp [applyVal] at h
        | VConstr _ _ => simp [applyVal] at h
  termination_by n => n

  /-- Forcing the value `vt` held in a `force` frame. -/
  theorem forceFwd : ∀ {n : Nat} {vt v : CekValue},
      forceVal n vt = some v → ∀ s, Reaches (.ret (.force :: s) vt) (.ret s v)
    | 0, _, _, h, _ => by simp [forceVal] at h
    | n + 1, vt, v, h, s => by
        cases vt with
        | VDelay body ρ =>
          have hb : bigEval n ρ body = some v := by simpa [forceVal] using h
          exact reaches_trans (one_step rfl) (evalFwd hb s)
        | VBuiltin b args ea =>
          cases ea with
          | one k =>
            cases k with
            | argQ =>
              have he : evalBuiltin b args = some v := by
                simpa [forceVal, ExpectedArgs.head, ExpectedArgs.tail] using h
              exact one_step (by simp only [step, ExpectedArgs.head, ExpectedArgs.tail, he])
            | argV => simp [forceVal, ExpectedArgs.head] at h
          | more k rest =>
            cases k with
            | argQ =>
              have hv : (CekValue.VBuiltin b args rest) = v := by
                simpa [forceVal, ExpectedArgs.head, ExpectedArgs.tail] using h
              subst hv
              exact one_step (by simp only [step, ExpectedArgs.head, ExpectedArgs.tail])
            | argV => simp [forceVal, ExpectedArgs.head] at h
        | VCon _ => simp [forceVal] at h
        | VLam _ _ => simp [forceVal] at h
        | VConstr _ _ => simp [forceVal] at h
  termination_by n => n
end

open Moist.Verified.SmallStep (init steps_error steps_halt)

/-- **Soundness.** Whatever `bigEval` computes for a closed term, the CEK halts at. -/
theorem bigEval_sound {fuel : Nat} {t : Term} {v : CekValue}
    (h : bigEval fuel CekEnv.nil t = some v) : Reaches (init t) (.halt v) :=
  reaches_trans (evalFwd h []) (one_step rfl)

/-! ## Completeness, part 1 — CEK well-bracketing (`firstExit`)

The stack-suffix invariant: while the CEK computes `t` under a base stack `Sf`, every
intermediate state keeps `Sf` as a stack suffix (and any `ret` strictly above `Sf`),
until `t` delivers its value as `ret Sf vt`. So a run that ever returns *below* `Sf`
must first pass through `ret Sf vt`. -/

/-- `Sfx a b`: `a` is a suffix of `b`. (Local, to avoid stdlib-name churn.) -/
def Sfx (a b : Stack) : Prop := ∃ p, p ++ a = b

theorem Sfx.rfl' (a : Stack) : Sfx a a := ⟨[], rfl⟩
theorem Sfx.cons {a b : Stack} (f : Frame) (h : Sfx a b) : Sfx a (f :: b) := by
  obtain ⟨p, hp⟩ := h; exact ⟨f :: p, by rw [List.cons_append, hp]⟩
theorem Sfx.append {a b : Stack} (pre : Stack) (h : Sfx a b) : Sfx a (pre ++ b) := by
  obtain ⟨p, hp⟩ := h; exact ⟨pre ++ p, by rw [List.append_assoc, hp]⟩
theorem Sfx.len_le {a b : Stack} (h : Sfx a b) : a.length ≤ b.length := by
  obtain ⟨p, hp⟩ := h; subst hp; simp [List.length_append]
theorem Sfx.self_or_lt {a b : Stack} (h : Sfx a b) : b = a ∨ a.length < b.length := by
  obtain ⟨p, hp⟩ := h
  cases p with
  | nil => exact Or.inl (by simpa using hp.symm)
  | cons x xs => exact Or.inr (by subst hp; simp [List.length_append]; omega)
theorem Sfx.pop {a : Stack} {f : Frame} {s' : Stack}
    (h : Sfx a (f :: s')) (hlen : a.length ≤ s'.length) : Sfx a s' := by
  obtain ⟨p, hp⟩ := h
  cases p with
  | nil => exfalso; have hh : a = f :: s' := by simpa using hp
           subst hh; simp at hlen; omega
  | cons x xs => exact ⟨xs, by have hh := hp; simp [List.cons_append] at hh; exact hh.2⟩

/-- The "computing `t` under base `Sf`, value not yet delivered" invariant. -/
def Inv (Sf : Stack) : State → Prop
  | .compute s _ _ => Sfx Sf s
  | .ret s _ => Sfx Sf s ∧ Sf.length < s.length
  | _ => False

/-- One CEK step from an `Inv` state either keeps `Inv`, exits at `ret Sf v`, or errors. -/
theorem inv_step (Sf : Stack) (st : State) (hinv : Inv Sf st) :
    Inv Sf (step st) ∨ (∃ v, step st = .ret Sf v) ∨ step st = .error := by
  have retOK : ∀ (s' : Stack) (w : CekValue), Sfx Sf s' →
      Inv Sf (.ret s' w) ∨ (∃ v, (State.ret s' w) = .ret Sf v) ∨ (State.ret s' w) = .error := by
    intro s' w hsf
    rcases hsf.self_or_lt with heq | hlt
    · exact Or.inr (Or.inl ⟨w, by rw [heq]⟩)
    · exact Or.inl ⟨hsf, hlt⟩
  cases st with
  | halt v => exact hinv.elim
  | error => exact hinv.elim
  | compute s ρ' t' =>
    have hsf : Sfx Sf s := hinv
    cases t' with
    | Var n =>
      simp only [step]
      cases hl : ρ'.lookup n with
      | none => exact Or.inr (Or.inr rfl)
      | some w => exact retOK s w hsf
    | Constant cb => obtain ⟨c, bt⟩ := cb; exact retOK s (.VCon c) hsf
    | Builtin b => exact retOK s (.VBuiltin b [] (expectedArgs b)) hsf
    | Lam nm body => exact retOK s (.VLam body ρ') hsf
    | Delay body => exact retOK s (.VDelay body ρ') hsf
    | Force e => exact Or.inl (show Sfx Sf (.force :: s) from hsf.cons _)
    | Apply f x => exact Or.inl (show Sfx Sf (.arg x ρ' :: s) from hsf.cons _)
    | Constr tag ms =>
      cases ms with
      | nil => exact retOK s (.VConstr tag []) hsf
      | cons m ms' => exact Or.inl (show Sfx Sf (.constrField tag [] ms' ρ' :: s) from hsf.cons _)
    | Case scrut alts =>
      exact Or.inl (show Sfx Sf (.caseScrutinee alts ρ' :: s) from hsf.cons _)
    | Error => exact Or.inr (Or.inr rfl)
  | ret s v' =>
    obtain ⟨hsf, hlt⟩ := hinv
    cases s with
    | nil => simp at hlt
    | cons f s' =>
      have hle : Sf.length ≤ s'.length := by simp [List.length] at hlt; omega
      have hsf' : Sfx Sf s' := hsf.pop hle
      cases f with
      | force =>
        cases v' with
        | VDelay body ρ'' => exact Or.inl (show Sfx Sf s' from hsf')
        | VBuiltin b args ea =>
          cases ea with
          | one k =>
            cases k with
            | argQ =>
              simp only [step, ExpectedArgs.head, ExpectedArgs.tail]
              cases he : evalBuiltin b args with
              | none => exact Or.inr (Or.inr rfl)
              | some w => exact retOK s' w hsf'
            | argV => exact Or.inr (Or.inr rfl)
          | more k rest =>
            cases k with
            | argQ =>
              simp only [step, ExpectedArgs.head, ExpectedArgs.tail]
              exact retOK s' (.VBuiltin b args rest) hsf'
            | argV => exact Or.inr (Or.inr rfl)
        | VCon _ => exact Or.inr (Or.inr rfl)
        | VLam _ _ => exact Or.inr (Or.inr rfl)
        | VConstr _ _ => exact Or.inr (Or.inr rfl)
      | arg m ρ'' => exact Or.inl (show Sfx Sf (.funV v' :: s') from hsf'.cons _)
      | funV vf =>
        cases vf with
        | VLam body ρ'' => exact Or.inl (show Sfx Sf s' from hsf')
        | VBuiltin b args ea =>
          cases ea with
          | one k =>
            cases k with
            | argV =>
              simp only [step, ExpectedArgs.head, ExpectedArgs.tail]
              cases he : evalBuiltin b (v' :: args) with
              | none => exact Or.inr (Or.inr rfl)
              | some w => exact retOK s' w hsf'
            | argQ => exact Or.inr (Or.inr rfl)
          | more k rest =>
            cases k with
            | argV =>
              simp only [step, ExpectedArgs.head, ExpectedArgs.tail]
              exact retOK s' (.VBuiltin b (v' :: args) rest) hsf'
            | argQ => exact Or.inr (Or.inr rfl)
        | VCon _ => exact Or.inr (Or.inr rfl)
        | VDelay _ _ => exact Or.inr (Or.inr rfl)
        | VConstr _ _ => exact Or.inr (Or.inr rfl)
      | constrField tag done ms ρ'' =>
        cases ms with
        | nil => exact retOK s' (.VConstr tag ((v' :: done).reverse)) hsf'
        | cons m ms'' =>
          exact Or.inl (show Sfx Sf (.constrField tag (v' :: done) ms'' ρ'' :: s') from hsf'.cons _)
      | caseScrutinee alts ρ'' =>
        cases v' with
        | VConstr tag fields =>
          simp only [step]
          cases ha : alts[tag]? with
          | none => exact Or.inr (Or.inr rfl)
          | some alt =>
            exact Or.inl (show Sfx Sf (fields.map Frame.applyArg ++ s') from hsf'.append _)
        | VCon c =>
          simp only [step]
          repeat' split
          all_goals first
            | exact Or.inr (Or.inr rfl)
            | exact Or.inl (show Sfx Sf _ from hsf'.append _)
        | VLam _ _ => exact Or.inr (Or.inr rfl)
        | VDelay _ _ => exact Or.inr (Or.inr rfl)
        | VBuiltin _ _ _ => exact Or.inr (Or.inr rfl)
      | applyArg vx =>
        cases v' with
        | VLam body ρ'' => exact Or.inl (show Sfx Sf s' from hsf')
        | VBuiltin b args ea =>
          cases ea with
          | one k =>
            cases k with
            | argV =>
              simp only [step, ExpectedArgs.head, ExpectedArgs.tail]
              cases he : evalBuiltin b (vx :: args) with
              | none => exact Or.inr (Or.inr rfl)
              | some w => exact retOK s' w hsf'
            | argQ => exact Or.inr (Or.inr rfl)
          | more k rest =>
            cases k with
            | argV =>
              simp only [step, ExpectedArgs.head, ExpectedArgs.tail]
              exact retOK s' (.VBuiltin b (vx :: args) rest) hsf'
            | argQ => exact Or.inr (Or.inr rfl)
        | VCon _ => exact Or.inr (Or.inr rfl)
        | VDelay _ _ => exact Or.inr (Or.inr rfl)
        | VConstr _ _ => exact Or.inr (Or.inr rfl)

/-- A `ret Sf _` state cannot satisfy `Inv Sf` (the strict-length guard fails). -/
theorem Inv_ret_self_absurd {Sf : Stack} {w : CekValue} (h : Inv Sf (.ret Sf w)) : False := by
  simp only [Inv] at h; exact absurd h.2 (Nat.lt_irrefl _)

/-- **Well-bracketing.** A run from an `Inv Sf` state that reaches `ret Sb _` with `Sb`
    strictly shorter than `Sf` must first pass through `ret Sf vt` — the value delivery. -/
theorem firstExit (Sf : Stack) :
    ∀ (k : Nat) (st : State) (vb : CekValue) (Sb : Stack),
      Inv Sf st → steps k st = .ret Sb vb → Sb.length < Sf.length →
      ∃ j vt, j ≤ k ∧ steps j st = .ret Sf vt ∧
        (∀ i, i < j → ∀ w, steps i st ≠ .ret Sf w) := by
  intro k
  induction k with
  | zero =>
    intro st vb Sb hinv hk hlen
    rw [steps] at hk; subst hk
    simp only [Inv] at hinv
    obtain ⟨hsf, hltSf⟩ := hinv
    have := hsf.len_le; omega
  | succ k ih =>
    intro st vb Sb hinv hk hlen
    rcases inv_step Sf st hinv with hInv' | ⟨v, hexit⟩ | herr
    · have hk' : steps k (step st) = .ret Sb vb := by rw [← steps_succ]; exact hk
      obtain ⟨j, vt, hj, hsteps, hno⟩ := ih (step st) vb Sb hInv' hk' hlen
      refine ⟨j + 1, vt, by omega, by rw [steps_succ]; exact hsteps, ?_⟩
      intro i hi w
      cases i with
      | zero =>
        rw [steps]; intro hcontra; subst hcontra
        exact Inv_ret_self_absurd hinv
      | succ i => rw [steps_succ]; exact hno i (by omega) w
    · refine ⟨1, v, by omega, by rw [steps_succ, steps]; exact hexit, ?_⟩
      intro i hi w
      have hi0 : i = 0 := by omega
      subst hi0
      rw [steps]; intro hcontra; subst hcontra
      exact Inv_ret_self_absurd hinv
    · exfalso
      have hcon : steps k (step st) = .ret Sb vb := by rw [← steps_succ]; exact hk
      rw [herr, steps_error] at hcon; exact State.noConfusion hcon

/-! ## Completeness, part 2 — the `Constr`/`Case`-free fragment and value purity

The covered fragment `PureTm` (no `Constr`/`Case`) is closed under the closures the CEK
builds; `PureVal`/`PureEnv` lift it to runtime values/environments. `bigEval` preserves it,
so when the backward proof recurses into a closure body that body is again `PureTm`. -/

/-- Terms in the covered fragment: full λ-calculus-with-builtins, no `Constr`/`Case`. -/
def PureTm : Term → Prop
  | .Var _ => True
  | .Constant _ => True
  | .Builtin _ => True
  | .Lam _ body => PureTm body
  | .Delay body => PureTm body
  | .Apply f a => PureTm f ∧ PureTm a
  | .Force e => PureTm e
  | .Constr _ _ => False
  | .Case _ _ => False
  | .Error => True

mutual
  /-- A runtime value is pure if every closure body it contains is `PureTm`. -/
  def PureVal : CekValue → Prop
    | .VCon _ => True
    | .VDelay body ρ => PureTm body ∧ PureEnv ρ
    | .VLam body ρ => PureTm body ∧ PureEnv ρ
    | .VConstr _ fields => PureValList fields
    | .VBuiltin _ args _ => PureValList args
  def PureValList : List CekValue → Prop
    | [] => True
    | v :: vs => PureVal v ∧ PureValList vs
  def PureEnv : CekEnv → Prop
    | .nil => True
    | .cons v ρ => PureVal v ∧ PureEnv ρ
end

theorem lookup_pure : ∀ {ρ : CekEnv} {n : Nat} {v : CekValue},
    PureEnv ρ → ρ.lookup n = some v → PureVal v
  | .nil, n, v, _, h => by cases n <;> simp [CekEnv.lookup] at h
  | .cons w rest, 0, v, _, h => by simp [CekEnv.lookup] at h
  | .cons w rest, 1, v, hpe, h => by
      simp only [CekEnv.lookup, Option.some.injEq] at h; subst h
      simp only [PureEnv] at hpe; exact hpe.1
  | .cons w rest, n + 2, v, hpe, h => by
      simp only [CekEnv.lookup] at h
      simp only [PureEnv] at hpe
      exact lookup_pure hpe.2 h

theorem mem_pureValList : ∀ {args : List CekValue} {w : CekValue},
    PureValList args → w ∈ args → PureVal w
  | [], w, _, hmem => by simp at hmem
  | a :: as, w, hpl, hmem => by
      simp only [PureValList] at hpl
      rcases List.mem_cons.mp hmem with h | h
      · subst h; exact hpl.1
      · exact mem_pureValList hpl.2 h

/-- Pass-through builtins return either one of their argument values or a `VCon`. -/
theorem passThrough_mem_or_con {b : BuiltinFun} {args : List CekValue} {w : CekValue}
    (h : evalBuiltinPassThrough b args = some w) : w ∈ args ∨ ∃ c, w = .VCon c := by
  unfold evalBuiltinPassThrough at h
  repeat' split at h
  all_goals first
    | simp only [reduceCtorEq] at h
    | (simp only [Option.some.injEq] at h; subst h; left; simp; done)
    | (simp only [Option.some.injEq] at h; subst h; right; exact ⟨_, rfl⟩)

/-- `evalBuiltin` preserves purity of its arguments. Only `evalBuiltinPassThrough`
    (tiny) is unfolded — `evalBuiltinConst` (the monolith) only ever yields a `VCon`. -/
theorem evalBuiltin_pure {b : BuiltinFun} {args : List CekValue} {w : CekValue}
    (hargs : PureValList args) (h : evalBuiltin b args = some w) : PureVal w := by
  rw [evalBuiltin] at h
  split at h
  · rename_i u hpt
    rw [Option.some.injEq] at h; subst h
    rcases passThrough_mem_or_con hpt with hmem | ⟨c, hc⟩
    · exact mem_pureValList hargs hmem
    · subst hc; exact True.intro
  · rename_i hpt
    split at h
    · rename_i consts he
      split at h
      · rename_i c hb
        rw [Option.some.injEq] at h; subst h; exact True.intro
      · rename_i hb; simp at h
    · rename_i he; simp at h

/- `bigEval`/`applyVal`/`forceVal` preserve purity (mutual induction on fuel). -/
mutual
  theorem bigEval_pure {f : Nat} {ρ : CekEnv} {t : Term} {v : CekValue}
      (ht : PureTm t) (hρ : PureEnv ρ) (h : bigEval f ρ t = some v) : PureVal v := by
    cases f with
    | zero => simp [bigEval] at h
    | succ f =>
      cases t with
      | Var n => exact lookup_pure hρ (by simpa [bigEval] using h)
      | Constant cb =>
        obtain ⟨c, bt⟩ := cb
        have hv : CekValue.VCon c = v := by simpa [bigEval] using h
        subst hv; exact True.intro
      | Builtin b =>
        have hv : CekValue.VBuiltin b [] (expectedArgs b) = v := by simpa [bigEval] using h
        subst hv; exact True.intro
      | Lam nm body =>
        have hv : CekValue.VLam body ρ = v := by simpa [bigEval] using h
        subst hv; exact ⟨ht, hρ⟩
      | Delay body =>
        have hv : CekValue.VDelay body ρ = v := by simpa [bigEval] using h
        subst hv; exact ⟨ht, hρ⟩
      | Apply f' a =>
        cases hf : bigEval f ρ f' with
        | none => simp [bigEval, hf] at h
        | some vf =>
          cases ha : bigEval f ρ a with
          | none => simp [bigEval, hf, ha] at h
          | some va =>
            simp only [bigEval, hf, ha] at h
            exact applyVal_pure (bigEval_pure ht.1 hρ hf) (bigEval_pure ht.2 hρ ha) h
      | Force e =>
        cases he : bigEval f ρ e with
        | none => simp [bigEval, he] at h
        | some vt =>
          simp only [bigEval, he] at h
          have hte : PureTm e := ht
          exact forceVal_pure (bigEval_pure hte hρ he) h
      | Constr tag ms => exact ht.elim
      | Case scrut alts => exact ht.elim
      | Error => simp [bigEval] at h
  termination_by f

  theorem applyVal_pure {f : Nat} {vf va v : CekValue}
      (hvf : PureVal vf) (hva : PureVal va) (h : applyVal f vf va = some v) : PureVal v := by
    cases f with
    | zero => simp [applyVal] at h
    | succ f =>
      cases vf with
      | VLam body ρ'' =>
        have hb : bigEval f (ρ''.extend va) body = some v := by simpa [applyVal] using h
        have hpe : PureEnv (ρ''.extend va) := ⟨hva, hvf.2⟩
        exact bigEval_pure hvf.1 hpe hb
      | VBuiltin b args ea =>
        cases ea with
        | one k =>
          cases k with
          | argV =>
            have he : evalBuiltin b (va :: args) = some v := by
              simpa [applyVal, ExpectedArgs.head, ExpectedArgs.tail] using h
            have hpl : PureValList (va :: args) := ⟨hva, hvf⟩
            exact evalBuiltin_pure hpl he
          | argQ => simp [applyVal, ExpectedArgs.head] at h
        | more k rest =>
          cases k with
          | argV =>
            have hv : CekValue.VBuiltin b (va :: args) rest = v := by
              simpa [applyVal, ExpectedArgs.head, ExpectedArgs.tail] using h
            subst hv; exact ⟨hva, hvf⟩
          | argQ => simp [applyVal, ExpectedArgs.head] at h
      | VCon _ => simp [applyVal] at h
      | VDelay _ _ => simp [applyVal] at h
      | VConstr _ _ => simp [applyVal] at h
  termination_by f

  theorem forceVal_pure {f : Nat} {vt v : CekValue}
      (hvt : PureVal vt) (h : forceVal f vt = some v) : PureVal v := by
    cases f with
    | zero => simp [forceVal] at h
    | succ f =>
      cases vt with
      | VDelay body ρ'' =>
        have hb : bigEval f ρ'' body = some v := by simpa [forceVal] using h
        exact bigEval_pure hvt.1 hvt.2 hb
      | VBuiltin b args ea =>
        cases ea with
        | one k =>
          cases k with
          | argQ =>
            have he : evalBuiltin b args = some v := by
              simpa [forceVal, ExpectedArgs.head, ExpectedArgs.tail] using h
            have hpl : PureValList args := hvt
            exact evalBuiltin_pure hpl he
          | argV => simp [forceVal, ExpectedArgs.head] at h
        | more k rest =>
          cases k with
          | argQ =>
            have hv : CekValue.VBuiltin b args rest = v := by
              simpa [forceVal, ExpectedArgs.head, ExpectedArgs.tail] using h
            subst hv; exact hvt
          | argV => simp [forceVal, ExpectedArgs.head] at h
      | VCon _ => simp [forceVal] at h
      | VLam _ _ => simp [forceVal] at h
      | VConstr _ _ => simp [forceVal] at h
  termination_by f
end

/-! ## Completeness, part 3 — fuel monotonicity -/

mutual
  theorem bigEval_mono {n : Nat} {ρ : CekEnv} {t : Term} {v : CekValue}
      (h : bigEval n ρ t = some v) : bigEval (n + 1) ρ t = some v := by
    cases n with
    | zero => simp [bigEval] at h
    | succ n =>
      cases t with
      | Var k => simpa [bigEval] using h
      | Constant cb => obtain ⟨c, bt⟩ := cb; simpa [bigEval] using h
      | Builtin b => simpa [bigEval] using h
      | Lam nm body => simpa [bigEval] using h
      | Delay body => simpa [bigEval] using h
      | Apply fn ar =>
        cases hf : bigEval n ρ fn with
        | none => simp [bigEval, hf] at h
        | some vf =>
          cases ha : bigEval n ρ ar with
          | none => simp [bigEval, hf, ha] at h
          | some va =>
            simp only [bigEval, hf, ha] at h
            simp only [bigEval, bigEval_mono hf, bigEval_mono ha]
            exact applyVal_mono h
      | Force e =>
        cases he : bigEval n ρ e with
        | none => simp [bigEval, he] at h
        | some vt =>
          simp only [bigEval, he] at h
          simp only [bigEval, bigEval_mono he]
          exact forceVal_mono h
      | Constr tag ms => simp [bigEval] at h
      | Case scrut alts => simp [bigEval] at h
      | Error => simp [bigEval] at h
  termination_by n

  theorem applyVal_mono {n : Nat} {vf va v : CekValue}
      (h : applyVal n vf va = some v) : applyVal (n + 1) vf va = some v := by
    cases n with
    | zero => simp [applyVal] at h
    | succ n =>
      cases vf with
      | VLam body ρ'' => simp only [applyVal] at h ⊢; exact bigEval_mono h
      | VBuiltin b args ea =>
        cases ea with
        | one k =>
          cases k with
          | argV => simpa [applyVal, ExpectedArgs.head, ExpectedArgs.tail] using h
          | argQ => simp [applyVal, ExpectedArgs.head] at h
        | more k rest =>
          cases k with
          | argV => simpa [applyVal, ExpectedArgs.head, ExpectedArgs.tail] using h
          | argQ => simp [applyVal, ExpectedArgs.head] at h
      | VCon _ => simp [applyVal] at h
      | VDelay _ _ => simp [applyVal] at h
      | VConstr _ _ => simp [applyVal] at h
  termination_by n

  theorem forceVal_mono {n : Nat} {vt v : CekValue}
      (h : forceVal n vt = some v) : forceVal (n + 1) vt = some v := by
    cases n with
    | zero => simp [forceVal] at h
    | succ n =>
      cases vt with
      | VDelay body ρ'' => simp only [forceVal] at h ⊢; exact bigEval_mono h
      | VBuiltin b args ea =>
        cases ea with
        | one k =>
          cases k with
          | argQ => simpa [forceVal, ExpectedArgs.head, ExpectedArgs.tail] using h
          | argV => simp [forceVal, ExpectedArgs.head] at h
        | more k rest =>
          cases k with
          | argQ => simpa [forceVal, ExpectedArgs.head, ExpectedArgs.tail] using h
          | argV => simp [forceVal, ExpectedArgs.head] at h
      | VCon _ => simp [forceVal] at h
      | VLam _ _ => simp [forceVal] at h
      | VConstr _ _ => simp [forceVal] at h
  termination_by n
end

theorem bigEval_mono_le {f f' : Nat} {ρ : CekEnv} {t : Term} {v : CekValue}
    (hle : f ≤ f') (h : bigEval f ρ t = some v) : bigEval f' ρ t = some v := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hle; clear hle
  induction d with
  | zero => simpa using h
  | succ d ih => rw [show f + (d + 1) = (f + d) + 1 from by omega]; exact bigEval_mono ih

theorem applyVal_mono_le {f f' : Nat} {vf va v : CekValue}
    (hle : f ≤ f') (h : applyVal f vf va = some v) : applyVal f' vf va = some v := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hle; clear hle
  induction d with
  | zero => simpa using h
  | succ d ih => rw [show f + (d + 1) = (f + d) + 1 from by omega]; exact applyVal_mono ih

/-! ## Completeness, part 4 — backward simulation and the full ↔ -/

theorem ret_cons_ne {f : Frame} {S : Stack} {vf v : CekValue} :
    (State.ret (f :: S) vf) ≠ .ret S v := by
  intro h; injection h with hs _
  have := congrArg List.length hs; simp only [List.length_cons] at this; omega

/-- Compose two runs. -/
theorem reach_comp {a b : Nat} {st0 st1 st2 : State}
    (h1 : steps a st0 = st1) (h2 : steps b st1 = st2) : steps (a + b) st0 = st2 := by
  rw [steps_add, h1]; exact h2

/-- Determinism splitting: peel a known prefix off a run. -/
theorem steps_split {K j : Nat} {st mid : State} {S : Stack} {v : CekValue}
    (hK : steps K st = .ret S v) (hj : steps j st = mid) (hle : j ≤ K) :
    steps (K - j) mid = .ret S v := by
  have h2 : steps (j + (K - j)) st = .ret S v := by rw [Nat.add_sub_cancel' hle]; exact hK
  rw [steps_add, hj] at h2; exact h2

/-- Shift a no-earlier-return certificate along a reached suffix. -/
theorem firstShift {o m k : Nat} {st0 st1 : State} {S : Stack}
    (hreach : steps o st0 = st1) (hk : o + m = k)
    (hfirst : ∀ i, i < k → ∀ w, steps i st0 ≠ .ret S w) :
    ∀ i, i < m → ∀ w, steps i st1 ≠ .ret S w := by
  intro i hi w hcontra
  have : steps (o + i) st0 = .ret S w := by rw [steps_add, hreach]; exact hcontra
  exact hfirst (o + i) (by omega) w this

/-- A value delivered to the base stack at-or-before the first return *is* the value. -/
theorem uniqueRet {p k : Nat} {S : Stack} {ρ : CekEnv} {t : Term} {w v : CekValue}
    (hp : steps p (.compute S ρ t) = .ret S w) (hk : steps k (.compute S ρ t) = .ret S v)
    (hfirst : ∀ i, i < k → ∀ w', steps i (.compute S ρ t) ≠ .ret S w') (hple : p ≤ k) : w = v := by
  rcases Nat.lt_or_eq_of_le hple with hlt | heq
  · exact absurd hp (hfirst p hlt w)
  · subst heq; rw [hp] at hk; rw [State.ret.injEq] at hk; exact hk.2

/-- Leaf terms (value formers) return in exactly one step. -/
theorem leaf_k1 {k : Nat} {S : Stack} {ρ : CekEnv} {t : Term} {v vval : CekValue}
    (hstep : step (.compute S ρ t) = .ret S vval)
    (hk : steps k (.compute S ρ t) = .ret S v)
    (hfirst : ∀ i, i < k → ∀ w, steps i (.compute S ρ t) ≠ .ret S w) : vval = v := by
  have hstep1 : steps 1 (.compute S ρ t) = .ret S vval := by rw [steps_succ, steps]; exact hstep
  have hk1 : k = 1 := by
    rcases Nat.lt_trichotomy k 1 with hlt | heq | hgt
    · exfalso; have hk0 : k = 0 := by omega
      subst hk0; rw [steps] at hk; exact absurd hk (by simp)
    · exact heq
    · exact absurd hstep1 (hfirst 1 hgt vval)
  subst hk1; rw [hstep1] at hk; rw [State.ret.injEq] at hk; exact hk.2

private theorem one_le_of_bigEval {f ρ t v} (h : bigEval f ρ t = some v) : 1 ≤ f := by
  cases f with
  | zero => simp [bigEval] at h
  | succ _ => omega

/-- **Backward simulation.** If the CEK computing `t` under `S` returns its value to `S`
    (as the first such return), `bigEval` computes that value. Strong recursion on the
    run length, dispatching sub-evaluations through the well-bracketing `firstExit`. -/
theorem evalBwd (k : Nat) (S : Stack) (ρ : CekEnv) (t : Term) (v : CekValue)
    (ht : PureTm t) (hρ : PureEnv ρ) (hk : steps k (.compute S ρ t) = .ret S v)
    (hfirst : ∀ i, i < k → ∀ w, steps i (.compute S ρ t) ≠ .ret S w) :
    ∃ f, bigEval f ρ t = some v := by
  cases t with
  | Var n =>
    cases hl : ρ.lookup n with
    | none =>
      exfalso; cases k with
      | zero => rw [steps] at hk; exact absurd hk (by simp)
      | succ k0 =>
        have he : steps (k0 + 1) (.compute S ρ (.Var n)) = .error := by
          rw [steps_succ]; simp only [step, hl]; exact steps_error k0
        rw [he] at hk; exact absurd hk (by simp)
    | some w0 =>
      have hw : w0 = v := leaf_k1 (by simp only [step, hl]) hk hfirst
      exact ⟨1, by simp [bigEval, hl, hw]⟩
  | Constant cb =>
    obtain ⟨c, bt⟩ := cb
    have hw : (CekValue.VCon c) = v := leaf_k1 (by simp only [step]) hk hfirst
    exact ⟨1, by simp [bigEval, hw]⟩
  | Builtin b =>
    have hw : (CekValue.VBuiltin b [] (expectedArgs b)) = v := leaf_k1 (by simp only [step]) hk hfirst
    exact ⟨1, by simp [bigEval, hw]⟩
  | Lam nm body =>
    have hw : (CekValue.VLam body ρ) = v := leaf_k1 (by simp only [step]) hk hfirst
    exact ⟨1, by simp [bigEval, hw]⟩
  | Delay body =>
    have hw : (CekValue.VDelay body ρ) = v := leaf_k1 (by simp only [step]) hk hfirst
    exact ⟨1, by simp [bigEval, hw]⟩
  | Error =>
    exfalso; cases k with
    | zero => rw [steps] at hk; exact absurd hk (by simp)
    | succ k0 =>
      have he : steps (k0 + 1) (.compute S ρ .Error) = .error := by
        rw [steps_succ]; simp only [step]; exact steps_error k0
      rw [he] at hk; exact absurd hk (by simp)
  | Constr tag ms => exact absurd ht (by simp [PureTm])
  | Case scrut alts => exact absurd ht (by simp [PureTm])
  | Force e =>
    have hte : PureTm e := ht
    cases k with
    | zero => exfalso; rw [steps] at hk; exact absurd hk (by simp)
    | succ k0 =>
      have hk0 : steps k0 (.compute (.force :: S) ρ e) = .ret S v := by
        have h' := hk; rw [steps_succ] at h'; exact h'
      obtain ⟨jf, vt, hjf, hes, heno⟩ :=
        firstExit (.force :: S) k0 (.compute (.force :: S) ρ e) v S (Sfx.rfl' _) hk0 (by simp)
      obtain ⟨fe, hbe⟩ := evalBwd jf (.force :: S) ρ e vt hte hρ hes heno
      have hpvt : PureVal vt := bigEval_pure hte hρ hbe
      have hsp : steps (k0 - jf) (.ret (.force :: S) vt) = .ret S v := steps_split hk0 hes hjf
      have hreach_v : steps (1 + jf) (.compute S ρ (.Force e)) = .ret (.force :: S) vt :=
        reach_comp (steps_one' rfl) hes
      cases hm : (k0 - jf) with
      | zero => exfalso; rw [hm, steps] at hsp; exact absurd hsp ret_cons_ne
      | succ m =>
        rw [hm, steps_succ] at hsp
        cases vt with
        | VDelay body ρ'' =>
          simp only [step] at hsp
          have hreach_body : steps (1 + jf + 1) (.compute S ρ (.Force e)) = .compute S ρ'' body :=
            reach_comp hreach_v (steps_one' rfl)
          have hbf : ∀ i, i < m → ∀ w, steps i (.compute S ρ'' body) ≠ .ret S w :=
            firstShift hreach_body (by omega) hfirst
          obtain ⟨fb, hbb⟩ := evalBwd m S ρ'' body v hpvt.1 hpvt.2 hsp hbf
          refine ⟨(max fe (fb + 1)) + 1, ?_⟩
          have hbe' : bigEval (max fe (fb + 1)) ρ e = some (CekValue.VDelay body ρ'') :=
            bigEval_mono_le (by omega) hbe
          have hfv : forceVal (max fe (fb + 1)) (CekValue.VDelay body ρ'') = some v := by
            obtain ⟨M', hM'⟩ : ∃ M', max fe (fb + 1) = M' + 1 := ⟨max fe (fb + 1) - 1, by omega⟩
            rw [hM']; simp only [forceVal]; exact bigEval_mono_le (by omega) hbb
          simp only [bigEval, hbe', hfv]
        | VBuiltin b args ea =>
          cases ea with
          | one k' =>
            cases k' with
            | argQ =>
              cases hev : evalBuiltin b args with
              | none =>
                exfalso
                simp only [step, ExpectedArgs.head, ExpectedArgs.tail, hev] at hsp
                rw [steps_error] at hsp; exact absurd hsp (by simp)
              | some w =>
                simp only [step, ExpectedArgs.head, ExpectedArgs.tail, hev] at hsp
                have hreach_w : steps (1 + jf + 1) (.compute S ρ (.Force e)) = .ret S w :=
                  reach_comp hreach_v
                    (steps_one' (by simp only [step, ExpectedArgs.head, ExpectedArgs.tail, hev]))
                have hwv : w = v := uniqueRet hreach_w hk hfirst (by omega)
                refine ⟨fe + 1, ?_⟩
                have hfv : forceVal fe (CekValue.VBuiltin b args (.one .argQ)) = some v := by
                  obtain ⟨M', hM'⟩ : ∃ M', fe = M' + 1 := ⟨fe - 1, by have := one_le_of_bigEval hbe; omega⟩
                  rw [hM']; simp only [forceVal, ExpectedArgs.head, ExpectedArgs.tail, hev, hwv]
                simp only [bigEval, hbe, hfv]
            | argV =>
              exfalso; simp only [step, ExpectedArgs.head] at hsp
              rw [steps_error] at hsp; exact absurd hsp (by simp)
          | more k' rest =>
            cases k' with
            | argQ =>
              simp only [step, ExpectedArgs.head, ExpectedArgs.tail] at hsp
              have hreach_w : steps (1 + jf + 1) (.compute S ρ (.Force e))
                  = .ret S (CekValue.VBuiltin b args rest) :=
                reach_comp hreach_v
                  (steps_one' (by simp only [step, ExpectedArgs.head, ExpectedArgs.tail]))
              have hwv : (CekValue.VBuiltin b args rest) = v := uniqueRet hreach_w hk hfirst (by omega)
              refine ⟨fe + 1, ?_⟩
              have hfv : forceVal fe (CekValue.VBuiltin b args (.more .argQ rest)) = some v := by
                obtain ⟨M', hM'⟩ : ∃ M', fe = M' + 1 := ⟨fe - 1, by have := one_le_of_bigEval hbe; omega⟩
                rw [hM']; simp only [forceVal, ExpectedArgs.head, ExpectedArgs.tail, hwv]
              simp only [bigEval, hbe, hfv]
            | argV =>
              exfalso; simp only [step, ExpectedArgs.head] at hsp
              rw [steps_error] at hsp; exact absurd hsp (by simp)
        | VCon _ =>
          exfalso; simp only [step] at hsp; rw [steps_error] at hsp; exact absurd hsp (by simp)
        | VLam _ _ =>
          exfalso; simp only [step] at hsp; rw [steps_error] at hsp; exact absurd hsp (by simp)
        | VConstr _ _ =>
          exfalso; simp only [step] at hsp; rw [steps_error] at hsp; exact absurd hsp (by simp)
  | Apply fn ar =>
    have htf : PureTm fn := ht.1
    have hta : PureTm ar := ht.2
    cases k with
    | zero => exfalso; rw [steps] at hk; exact absurd hk (by simp)
    | succ k0 =>
      have hk0 : steps k0 (.compute (.arg ar ρ :: S) ρ fn) = .ret S v := by
        have h' := hk; rw [steps_succ] at h'; exact h'
      obtain ⟨jf, vf, hjf, hfns, hfno⟩ :=
        firstExit (.arg ar ρ :: S) k0 (.compute (.arg ar ρ :: S) ρ fn) v S (Sfx.rfl' _) hk0 (by simp)
      obtain ⟨ff, hbf⟩ := evalBwd jf (.arg ar ρ :: S) ρ fn vf htf hρ hfns hfno
      have hpvf : PureVal vf := bigEval_pure htf hρ hbf
      have hsp1 : steps (k0 - jf) (.ret (.arg ar ρ :: S) vf) = .ret S v := steps_split hk0 hfns hjf
      have hreach_vf : steps (1 + jf) (.compute S ρ (.Apply fn ar)) = .ret (.arg ar ρ :: S) vf :=
        reach_comp (steps_one' rfl) hfns
      cases hm1 : (k0 - jf) with
      | zero => exfalso; rw [hm1, steps] at hsp1; exact absurd hsp1 ret_cons_ne
      | succ m1 =>
        rw [hm1, steps_succ] at hsp1; simp only [step] at hsp1
        obtain ⟨ja, va, hja, hans, hano⟩ :=
          firstExit (.funV vf :: S) m1 (.compute (.funV vf :: S) ρ ar) v S (Sfx.rfl' _) hsp1 (by simp)
        obtain ⟨fa, hba⟩ := evalBwd ja (.funV vf :: S) ρ ar va hta hρ hans hano
        have hpva : PureVal va := bigEval_pure hta hρ hba
        have hsp2 : steps (m1 - ja) (.ret (.funV vf :: S) va) = .ret S v := steps_split hsp1 hans hja
        have hreach_app : steps (1 + jf + 1 + ja) (.compute S ρ (.Apply fn ar)) = .ret (.funV vf :: S) va :=
          reach_comp (reach_comp hreach_vf (steps_one' rfl)) hans
        cases hm2 : (m1 - ja) with
        | zero => exfalso; rw [hm2, steps] at hsp2; exact absurd hsp2 ret_cons_ne
        | succ m2 =>
          rw [hm2, steps_succ] at hsp2
          cases vf with
          | VLam body ρ'' =>
            simp only [step] at hsp2
            have hreach_body : steps (1 + jf + 1 + ja + 1) (.compute S ρ (.Apply fn ar))
                = .compute S (ρ''.extend va) body :=
              reach_comp hreach_app (steps_one' rfl)
            have hbfst : ∀ i, i < m2 → ∀ w, steps i (.compute S (ρ''.extend va) body) ≠ .ret S w :=
              firstShift hreach_body (by omega) hfirst
            have hpe : PureEnv (ρ''.extend va) := ⟨hpva, hpvf.2⟩
            obtain ⟨fb, hbb⟩ := evalBwd m2 S (ρ''.extend va) body v hpvf.1 hpe hsp2 hbfst
            refine ⟨(max ff (max fa (fb + 1))) + 1, ?_⟩
            have hbf' : bigEval (max ff (max fa (fb + 1))) ρ fn = some (CekValue.VLam body ρ'') :=
              bigEval_mono_le (by omega) hbf
            have hba' : bigEval (max ff (max fa (fb + 1))) ρ ar = some va :=
              bigEval_mono_le (by omega) hba
            have hav : applyVal (max ff (max fa (fb + 1))) (CekValue.VLam body ρ'') va = some v := by
              obtain ⟨M', hM'⟩ : ∃ M', max ff (max fa (fb + 1)) = M' + 1 :=
                ⟨max ff (max fa (fb + 1)) - 1, by omega⟩
              rw [hM']; simp only [applyVal]; exact bigEval_mono_le (by omega) hbb
            simp only [bigEval, hbf', hba', hav]
          | VBuiltin b args ea =>
            cases ea with
            | one k' =>
              cases k' with
              | argV =>
                cases hev : evalBuiltin b (va :: args) with
                | none =>
                  exfalso
                  simp only [step, ExpectedArgs.head, ExpectedArgs.tail, hev] at hsp2
                  rw [steps_error] at hsp2; exact absurd hsp2 (by simp)
                | some w =>
                  simp only [step, ExpectedArgs.head, ExpectedArgs.tail, hev] at hsp2
                  have hreach_w : steps (1 + jf + 1 + ja + 1) (.compute S ρ (.Apply fn ar)) = .ret S w :=
                    reach_comp hreach_app
                      (steps_one' (by simp only [step, ExpectedArgs.head, ExpectedArgs.tail, hev]))
                  have hwv : w = v := uniqueRet hreach_w hk hfirst (by omega)
                  refine ⟨(max ff fa) + 1, ?_⟩
                  have hbf' : bigEval (max ff fa) ρ fn = some (CekValue.VBuiltin b args (.one .argV)) :=
                    bigEval_mono_le (by omega) hbf
                  have hba' : bigEval (max ff fa) ρ ar = some va := bigEval_mono_le (by omega) hba
                  have hav : applyVal (max ff fa) (CekValue.VBuiltin b args (.one .argV)) va = some v := by
                    obtain ⟨M', hM'⟩ : ∃ M', max ff fa = M' + 1 :=
                      ⟨max ff fa - 1, by have := one_le_of_bigEval hbf; omega⟩
                    rw [hM']; simp only [applyVal, ExpectedArgs.head, ExpectedArgs.tail, hev, hwv]
                  simp only [bigEval, hbf', hba', hav]
              | argQ =>
                exfalso; simp only [step, ExpectedArgs.head] at hsp2
                rw [steps_error] at hsp2; exact absurd hsp2 (by simp)
            | more k' rest =>
              cases k' with
              | argV =>
                simp only [step, ExpectedArgs.head, ExpectedArgs.tail] at hsp2
                have hreach_w : steps (1 + jf + 1 + ja + 1) (.compute S ρ (.Apply fn ar))
                    = .ret S (CekValue.VBuiltin b (va :: args) rest) :=
                  reach_comp hreach_app
                    (steps_one' (by simp only [step, ExpectedArgs.head, ExpectedArgs.tail]))
                have hwv : (CekValue.VBuiltin b (va :: args) rest) = v := uniqueRet hreach_w hk hfirst (by omega)
                refine ⟨(max ff fa) + 1, ?_⟩
                have hbf' : bigEval (max ff fa) ρ fn = some (CekValue.VBuiltin b args (.more .argV rest)) :=
                  bigEval_mono_le (by omega) hbf
                have hba' : bigEval (max ff fa) ρ ar = some va := bigEval_mono_le (by omega) hba
                have hav : applyVal (max ff fa) (CekValue.VBuiltin b args (.more .argV rest)) va = some v := by
                  obtain ⟨M', hM'⟩ : ∃ M', max ff fa = M' + 1 :=
                    ⟨max ff fa - 1, by have := one_le_of_bigEval hbf; omega⟩
                  rw [hM']; simp only [applyVal, ExpectedArgs.head, ExpectedArgs.tail, hwv]
                simp only [bigEval, hbf', hba', hav]
              | argQ =>
                exfalso; simp only [step, ExpectedArgs.head] at hsp2
                rw [steps_error] at hsp2; exact absurd hsp2 (by simp)
          | VCon _ =>
            exfalso; simp only [step] at hsp2; rw [steps_error] at hsp2; exact absurd hsp2 (by simp)
          | VDelay _ _ =>
            exfalso; simp only [step] at hsp2; rw [steps_error] at hsp2; exact absurd hsp2 (by simp)
          | VConstr _ _ =>
            exfalso; simp only [step] at hsp2; rw [steps_error] at hsp2; exact absurd hsp2 (by simp)
  termination_by k
  decreasing_by all_goals omega

/-- `steps` from the back: one more step is a `step` of the result. -/
theorem steps_succ_right (n : Nat) (s : State) : steps (n + 1) s = step (steps n s) := by
  induction n generalizing s with
  | zero => simp only [steps]
  | succ n ih => rw [steps_succ, ih, steps_succ]

/-- The only states that `step` to `halt v` are `ret [] v` (and `halt v` itself). -/
theorem step_pre_halt {st : State} {v : CekValue} (h : step st = .halt v) :
    st = .ret [] v ∨ st = .halt v := by
  cases st with
  | compute s ρ t' =>
    exfalso; cases t' <;> simp only [step] at h <;> (try repeat' split at h) <;> simp_all
  | ret s v' =>
    cases s with
    | nil => left; simp only [step] at h; injection h with hv; rw [hv]
    | cons f s' =>
      exfalso
      cases f <;> cases v' <;>
        simp only [step, ExpectedArgs.head, ExpectedArgs.tail] at h <;>
        (try repeat' split at h) <;> simp_all
  | halt v' => right; simp only [step] at h; exact h
  | error => exfalso; simp only [step] at h; exact absurd h (by simp)

/-- A halting run passes through `ret [] v`. -/
theorem exists_ret_nil {t : Term} {v : CekValue} :
    ∀ (N : Nat), steps N (init t) = .halt v → ∃ n, steps n (init t) = .ret [] v := by
  intro N
  induction N with
  | zero => intro hN; rw [steps] at hN; exact absurd hN (by simp [init])
  | succ N ih =>
    intro hN
    rw [steps_succ_right] at hN
    rcases step_pre_halt hN with hr | hh
    · exact ⟨N, hr⟩
    · exact ih hh

/-! ## The full equivalence -/

/-- **Completeness.** If the CEK halts at `v`, `bigEval` computes `v` (closed `PureTm`). -/
theorem bigEval_complete {t : Term} {v : CekValue} (ht : PureTm t)
    (h : Reaches (init t) (.halt v)) : ∃ f, bigEval f CekEnv.nil t = some v := by
  obtain ⟨N, hN⟩ := h
  obtain ⟨n0, hn0⟩ := exists_ret_nil N hN
  -- after `ret []` the machine halts forever, so this `ret []` is the *first* (and only) one
  have hno : ∀ i, i < n0 → ∀ w, steps i (init t) ≠ .ret [] w := by
    intro i hi w hcontra
    have hih : steps (i + 1) (init t) = .halt w := by
      rw [steps_succ_right, hcontra]; simp only [step]
    have hhalt : steps n0 (init t) = .halt w := by
      have h2 : steps ((i + 1) + (n0 - (i + 1))) (init t) = .halt w := by
        rw [steps_add, hih]; exact steps_halt _ w
      rwa [Nat.add_sub_cancel' (by omega)] at h2
    rw [hhalt] at hn0; exact absurd hn0 (by simp)
  exact evalBwd n0 [] CekEnv.nil t v ht True.intro hn0 hno

/-- **Big-step ≡ CEK.** For a closed `Constr`/`Case`-free term, `bigEval` computes `v`
    (at some fuel) iff the CEK machine halts at `v`. Axiom-clean. -/
theorem bigEval_iff_halt {t : Term} {v : CekValue} (ht : PureTm t) :
    (∃ f, bigEval f CekEnv.nil t = some v) ↔ Reaches (init t) (.halt v) := by
  constructor
  · rintro ⟨f, hf⟩; exact bigEval_sound hf
  · exact bigEval_complete ht

/-! ## Builtin denotation specs (Blaster optimization)

`Moist.CEK.evalBuiltin` is a monolithic dispatch that the SMT optimizer cannot
afford to unfold (it `whnf`-times-out even in Lean — the same blow-up Blaster hits;
cf. `docs/blaster-bench/VERDICT.md`).  Following what the Blaster-optimized CEK does
with builtins (per-builtin `@[simp] …_rfl` denotations), we expose the builtin
results as `@[simp]` axioms so the optimizer rewrites a builtin call straight to the
native `Int`/`Bool` operation.  These are *trusted denotations* (the analogue of
`PlutusCore.Integer.addInteger_rfl` / `Demo.lean`'s `opaque … := sorry`); they are
each true by `rfl` but stated as axioms only because reducing `evalBuiltin` is
prohibitively expensive.  **The `≡ CEK` results above do not depend on them** — both
`bigEval` and the CEK invoke the *same* `evalBuiltin`, so they agree on builtins by
construction (`#print axioms bigEval_sound` stays `propext`/`Quot.sound`/`Classical.choice`). -/

@[simp] axiom evalBuiltin_addInteger (x y : Int) :
    evalBuiltin .AddInteger [.VCon (.Integer y), .VCon (.Integer x)]
      = some (.VCon (.Integer (x + y)))
@[simp] axiom evalBuiltin_subtractInteger (x y : Int) :
    evalBuiltin .SubtractInteger [.VCon (.Integer y), .VCon (.Integer x)]
      = some (.VCon (.Integer (x - y)))
@[simp] axiom evalBuiltin_multiplyInteger (x y : Int) :
    evalBuiltin .MultiplyInteger [.VCon (.Integer y), .VCon (.Integer x)]
      = some (.VCon (.Integer (x * y)))
@[simp] axiom evalBuiltin_lessThanEqualsInteger (x y : Int) :
    evalBuiltin .LessThanEqualsInteger [.VCon (.Integer y), .VCon (.Integer x)]
      = some (.VCon (.Bool (x ≤ y)))
@[simp] axiom evalBuiltin_lessThanInteger (x y : Int) :
    evalBuiltin .LessThanInteger [.VCon (.Integer y), .VCon (.Integer x)]
      = some (.VCon (.Bool (x < y)))
@[simp] axiom evalBuiltin_equalsInteger (x y : Int) :
    evalBuiltin .EqualsInteger [.VCon (.Integer y), .VCon (.Integer x)]
      = some (.VCon (.Bool (x == y)))

end Moist.Verified.BigStep
