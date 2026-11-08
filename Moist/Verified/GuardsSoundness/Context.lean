import Moist.Verified.GuardsSoundness.Measure

variable [sv : Moist.CEK.SemVariant]

/-! # The invariant of the termination analysis

`Inv c env ρ` is what the analysis assumes about the environment: it is
well formed, every recorded fact describes the value of its name (`PF`:
the right-hand side produced it, in the environment of the binding, and
binds fresh names there), the recorded list names hold lists, and every
recursive function of `c.roles` is bound to a function whose calls
terminate when the shrinking argument is below some bound `m`, while the
base of the role is at most `m` and its smaller names are below `m`.
-/

namespace Moist.Verified.Guards

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast
open Moist.Verified.KnownLists

/-- A recorded right-hand side produced the value, and binds fresh names. -/
def PF (env : List VarId) (ρ : CekEnv) (rhs : Expr) (v : CekValue) : Prop :=
  Produces env ρ rhs v ∧ freshIn env rhs = true

theorem PF.produces {env : List VarId} {ρ : CekEnv} {rhs : Expr} {v : CekValue}
    (h : PF env ρ rhs v) : Produces env ρ rhs v := h.1

/-- The value bound to `x`, if `x` is bound, satisfies `Q`. -/
def BoundValue (env : List VarId) (ρ : CekEnv) (x : VarId) (Q : CekValue → Prop) : Prop :=
  ∀ i, envLookupT env x = some i → ∃ w, ρ.lookup (i + 1) = some w ∧ Q w

omit sv in
theorem BoundValue.extend {env : List VarId} {ρ : CekEnv} {x y : VarId} {Q : CekValue → Prop}
    (h : BoundValue env ρ y Q) (hxy : (x == y) = false) (w : CekValue) :
    BoundValue (x :: env) (ρ.extend w) y Q := by
  intro i hi
  rw [envLookupT_cons_neq x y env hxy] at hi
  cases hl : envLookupT env y with
  | none => rw [hl] at hi; cases hi
  | some j =>
    rw [hl] at hi; simp at hi; subst hi
    obtain ⟨u, hu, hq⟩ := h j hl
    exact ⟨u, by simpa [CekEnv.extend, CekEnv.lookup] using hu, hq⟩

omit sv in
theorem BoundValue.self {env : List VarId} {ρ : CekEnv} {x y : VarId} {Q : CekValue → Prop}
    {w : CekValue} (hxy : (x == y) = true) (hw : Q w) : BoundValue (x :: env) (ρ.extend w) y Q := by
  intro i hi
  rw [← envLookupT_congr hxy, MIR.envLookupT_cons_of_beq (varId_beq_self x) env] at hi
  cases hi
  exact ⟨w, rfl, hw⟩

omit sv in
theorem BoundValue.mono {env : List VarId} {ρ : CekEnv} {x : VarId} {Q R : CekValue → Prop}
    (h : BoundValue env ρ x Q) (hQR : ∀ w, Q w → R w) : BoundValue env ρ x R := by
  intro i hi
  obtain ⟨w, hw, hq⟩ := h i hi
  exact ⟨w, hw, hQR w hq⟩

omit sv in
theorem BoundValue.drop {env : List VarId} {ρ : CekEnv} {x : VarId} {Q : CekValue → Prop}
    (h : BoundValue env ρ x Q) (hd : EnvDistinct env) (j : Nat) :
    BoundValue (env.drop j) (dropEnv j ρ) x Q := by
  intro i hi
  have hi' := hd.drop_lookup j hi
  obtain ⟨v, hv, hq⟩ := h (i + j) hi'
  refine ⟨v, ?_, hq⟩
  rw [dropEnv_lookup j ρ _ (by omega), show i + 1 + j = i + j + 1 by omega]; exact hv

/-- Predicates on the arguments of a call of a role, for the bound `m`. -/
def rolePreds (r : Role) (m : Nat) : List (CekValue → Prop) :=
  (List.range r.arity).map fun i w => (i = r.index → vsize w < m) ∧ (r.lists.contains i → ListValue w)

def RoleHolds (env : List VarId) (ρ : CekEnv) (r : Role) : Prop :=
  ∃ m, BoundValue env ρ r.fn (CallsOK r.result (rolePreds r m)) ∧
    BoundValue env ρ r.base (fun w => vsize w ≤ m) ∧
    ∀ y, r.small.contains y = true → BoundValue env ρ y (fun w => vsize w < m)

/-- The names a role mentions. -/
def Role.mentions (r : Role) (x : VarId) : Bool :=
  (r.fn == x) || (r.base == x) || r.small.contains x

structure Inv (c : TCtx) (env : List VarId) (ρ : CekEnv) : Prop where
  wf : EnvWellFormed env.length ρ
  len : env.length ≤ ρ.length
  facts : FactsHold PF c.facts env ρ
  lists : ListsHold c.lists env ρ
  roles : ∀ r ∈ c.roles, RoleHolds env ρ r

omit sv in
theorem small_beq {L : List VarId} {x y : VarId} (h : L.contains y = true) (hx : L.contains x = false) :
    (x == y) = false := by
  cases hxy : (x == y)
  · rfl
  · exfalso
    have : L.contains x = L.contains y := by
      simp only [List.contains_eq_any_beq]
      congr 1; funext z
      exact beq_congr_left' hxy z
    rw [this, h] at hx; cases hx
where
  beq_congr_left' {x y : VarId} (hxy : (x == y) = true) (z : VarId) : (x == z) = (y == z) := by
    have h := (VarId.beq_true_iff x y).mp hxy
    show (x.origin == z.origin && x.uid == z.uid) = (y.origin == z.origin && y.uid == z.uid)
    rw [h.1, h.2]

omit sv in
theorem fresh_facts {c : TCtx} {x : VarId} (h : c.fresh x = true) :
    c.facts.find? (fun e => e.1 == x) = none := by
  unfold TCtx.fresh at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hf, _⟩, _⟩ := h
  rw [List.find?_eq_none]
  intro e he
  simp only [List.any_eq_false, Bool.not_eq_true] at hf
  simpa using hf e he

omit sv in
theorem fresh_lists {c : TCtx} {x : VarId} (h : c.fresh x = true) : c.lists.contains x = false := by
  unfold TCtx.fresh at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.1.2

omit sv in
theorem fresh_roles {c : TCtx} {x : VarId} (h : c.fresh x = true) :
    ∀ r ∈ c.roles, (r.fn == x) = false ∧ (r.base == x) = false ∧ r.small.contains x = false := by
  unfold TCtx.fresh at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  intro r hr
  have := h.2 r hr
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

omit sv in
theorem ListsHold.extend' {L env : List VarId} {ρ : CekEnv} {x : VarId} (h : ListsHold L env ρ)
    (hx : L.contains x = false) (w : CekValue) : ListsHold L (x :: env) (ρ.extend w) := by
  intro y hy i hi
  exact (BoundValue.extend (fun i hi => h y hy i hi) (small_beq hy hx) w) i hi

theorem RoleHolds.extend {env : List VarId} {ρ : CekEnv} {r : Role} {x : VarId} (h : RoleHolds env ρ r)
    (hfn : (r.fn == x) = false) (hb : (r.base == x) = false) (hs : r.small.contains x = false)
    (w : CekValue) : RoleHolds (x :: env) (ρ.extend w) r := by
  obtain ⟨m, hf, hbase, hsmall⟩ := h
  refine ⟨m, hf.extend (beq_false_symm hfn) w, hbase.extend (beq_false_symm hb) w, fun y hy => ?_⟩
  exact (hsmall y hy).extend (small_beq hy hs) w
where
  beq_false_symm {a b : VarId} (h : (a == b) = false) : (b == a) = false := by
    cases hba : (b == a)
    · rfl
    · rw [VarId.beq_true_iff] at hba
      have : (a == b) = true := by rw [VarId.beq_true_iff]; exact ⟨hba.1.symm, hba.2.symm⟩
      rw [h] at this; cases this

/-- A fresh binder with an arbitrary value. -/
theorem Inv.extend {c : TCtx} {env : List VarId} {ρ : CekEnv} {x : VarId} {w : CekValue}
    (h : Inv c env ρ) (hx : c.fresh x = true) (hw : ValueWellFormed w) :
    Inv c (x :: env) (ρ.extend w) where
  wf := (envWellFormed_extend' h.wf h.len hw).1
  len := by simpa using (envWellFormed_extend' h.wf h.len hw).2
  facts := h.facts.extend w (fresh_facts hx)
  lists := ListsHold.extend' h.lists (fresh_lists hx) w
  roles := fun r hr => by
    obtain ⟨h1, h2, h3⟩ := fresh_roles hx r hr
    exact (h.roles r hr).extend h1 h2 h3 w

/-- A fresh binder recorded with the right-hand side that produced it. -/
theorem Inv.push {c : TCtx} {env : List VarId} {ρ : CekEnv} {x : VarId} {r : Expr} {w : CekValue}
    (h : Inv c env ρ) (hx : c.fresh x = true) (hw : ValueWellFormed w) (hp : PF env ρ r w) :
    Inv (c.pushFact x r) (x :: env) (ρ.extend w) where
  wf := (h.extend hx hw).wf
  len := (h.extend hx hw).len
  facts := h.facts.push hp
  lists := (h.extend hx hw).lists
  roles := (h.extend hx hw).roles

end Moist.Verified.Guards
