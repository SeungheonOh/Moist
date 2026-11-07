import Moist.Verified.ShapeFacts.Delays
import Moist.Verified.ShapeFacts.Known
import Moist.Verified.ShapeFacts.Top

/-! # Boolean result summaries

`booleanResultCore` accepts expressions whose successful evaluations return
Boolean constants. Recursive functions are summarised by their arity; the
summary of a recursive function is justified by strong induction on the number
of machine steps its calls take. A budget assignment `β` records, for every
summarised name, how many steps of a call are covered by its summary.
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence

/-! ## Budgets and summaries -/

/-- The part of a name that `==` compares. -/
def varKey (x : VarId) : VarOrigin × Nat := (x.origin, x.uid)

theorem varKey_eq {x y : VarId} (h : (x == y) = true) : varKey x = varKey y := by
  rw [VarId.beq_true_iff] at h
  obtain ⟨h₁, h₂⟩ := h
  simp [varKey, h₁, h₂]

theorem beq_of_varKey {x y : VarId} (h : varKey x = varKey y) : (x == y) = true := by
  simp only [varKey, Prod.mk.injEq] at h
  rw [VarId.beq_true_iff]; exact ⟨h.1, h.2⟩

theorem varId_beq_trans {x y z : VarId} (h₁ : (x == y) = true) (h₂ : (y == z) = true) :
    (x == z) = true := beq_of_varKey ((varKey_eq h₁).trans (varKey_eq h₂))

/-- Step budgets of summarised names. -/
abbrev Budget := VarOrigin × Nat → Nat

/-- Applying `w` to `k` arguments and returning within `B` steps yields a
    Boolean constant. -/
def BoolFn (k B : Nat) (w : CekValue) : Prop :=
  ∀ vals : List CekValue, vals.length = k → ∀ m v, m ≤ B →
    steps m (.ret (vals.map Frame.applyArg) w) = .halt v → BoolValue v

theorem BoolFn.mono {k B B' : Nat} {w : CekValue} (h : BoolFn k B w) (hB : B' ≤ B) : BoolFn k B' w :=
  fun vals hlen m v hm hs => h vals hlen m v (by omega) hs

/-- Every summarised name bound in the environment holds a function whose
    calls of the summarised arity return Booleans within its budget. -/
def SummariesHold (S : List (VarId × Nat)) (env : List VarId) (ρ : CekEnv) (β : Budget) : Prop :=
  ∀ entry ∈ S, ∀ i, envLookupT env entry.1 = some i →
    ∀ w, ρ.lookup (i + 1) = some w → BoolFn entry.2 (β (varKey entry.1)) w

/-- A computation of `n` steps fits in the budget of every summarised name
    bound in the environment. -/
def WithinBudget (S : List (VarId × Nat)) (env : List VarId) (β : Budget) (n : Nat) : Prop :=
  ∀ entry ∈ S, (envLookupT env entry.1).isSome = true → n ≤ β (varKey entry.1)

/-- A fact whose value was produced by a counted evaluation that fits the
    budgets of the summaries. -/
def ProducesB (S : List (VarId × Nat)) (β : Budget) (env : List VarId) (ρ : CekEnv) (rhs : Expr)
    (v : CekValue) : Prop :=
  ∃ t m, lowerTotalExpr env rhs = some t ∧ HaltsIn ρ t m v ∧ WithinBudget S env β m ∧
    freshIn env rhs = true

theorem ProducesB.produces {S : List (VarId × Nat)} {β : Budget} {env : List VarId} {ρ : CekEnv}
    {rhs : Expr} {v : CekValue} (h : ProducesB S β env ρ rhs v) :
    Produces env ρ rhs v ∧ freshIn env rhs = true := by
  obtain ⟨t, m, ht, hm, _, hf⟩ := h
  exact ⟨⟨t, ht, hm.halts⟩, hf⟩

theorem WithinBudget.le {S : List (VarId × Nat)} {env : List VarId} {β : Budget} {n m : Nat}
    (h : WithinBudget S env β n) (hm : m ≤ n) : WithinBudget S env β m :=
  fun entry hmem hb => Nat.le_trans hm (h entry hmem hb)

theorem WithinBudget.sub {S S' : List (VarId × Nat)} {env : List VarId} {β : Budget} {n : Nat}
    (h : WithinBudget S env β n) (hS : ∀ entry ∈ S', entry ∈ S) : WithinBudget S' env β n :=
  fun entry hmem hb => h entry (hS entry hmem) hb

theorem SummariesHold.sub {S S' : List (VarId × Nat)} {env : List VarId} {ρ : CekEnv} {β : Budget}
    (h : SummariesHold S env ρ β) (hS : ∀ entry ∈ S', entry ∈ S) : SummariesHold S' env ρ β :=
  fun entry hmem => h entry (hS entry hmem)

theorem ProducesB.sub {S S' : List (VarId × Nat)} {β : Budget} {env : List VarId} {ρ : CekEnv}
    {rhs : Expr} {v : CekValue} (h : ProducesB S β env ρ rhs v) (hS : ∀ entry ∈ S', entry ∈ S) :
    ProducesB S' β env ρ rhs v := by
  obtain ⟨t, m, ht, hm, hb, hf⟩ := h
  exact ⟨t, m, ht, hm, hb.sub hS, hf⟩

theorem WithinBudget.drop {S : List (VarId × Nat)} {env : List VarId} {β : Budget} {n : Nat}
    (h : WithinBudget S env β n) (hd : EnvDistinct env) (j : Nat) :
    WithinBudget S (env.drop j) β n := by
  intro entry hmem hb
  cases hl : envLookupT (env.drop j) entry.1 with
  | none => rw [hl] at hb; cases hb
  | some i => exact h entry hmem (by rw [hd.drop_lookup j hl]; rfl)

theorem SummariesHold.drop {S : List (VarId × Nat)} {env : List VarId} {ρ : CekEnv} {β : Budget}
    (h : SummariesHold S env ρ β) (hd : EnvDistinct env) (j : Nat) :
    SummariesHold S (env.drop j) (dropEnv j ρ) β := by
  intro entry hmem i hl w hw
  rw [dropEnv_lookup j ρ (i + 1) (by omega)] at hw
  exact h entry hmem (i + j) (hd.drop_lookup j hl) w (by rw [← hw]; congr 1; omega)

theorem filter_mem {α : Type} {p : α → Bool} {l : List α} : ∀ x ∈ l.filter p, x ∈ l :=
  fun _ hx => (List.mem_filter.mp hx).1

theorem contains_congr {xs : List VarId} {x y : VarId} (h : (x == y) = true) :
    xs.contains x = xs.contains y := by
  induction xs with
  | nil => rfl
  | cons z zs ih =>
    simp only [List.contains_cons, ih]
    congr 1
    cases hxz : (x == z) with
    | true => exact (varId_beq_trans (varId_beq_symm h) hxz).symm
    | false =>
      cases hyz : (y == z) with
      | false => rfl
      | true => exact absurd (varId_beq_trans h hyz) (by simp [hxz])

theorem envLookupT_none_iff {l : List VarId} {y : VarId} :
    envLookupT l y = none ↔ ∀ z ∈ l, (z == y) = false := by
  induction l with
  | nil => simp [envLookupT, envLookupT.go]
  | cons z zs ih =>
    rw [envLookupT_cons]
    split
    · rename_i hz; simp only [reduceCtorEq, false_iff]; intro hall; simp [hall z (.head _)] at hz
    · rename_i hz
      simp only [Option.map_eq_none_iff, ih, List.mem_cons, forall_eq_or_imp]
      simp [hz]

theorem envLookupT_none_of_contains {l : List VarId} {y : VarId} (h : l.contains y = false) :
    envLookupT l y = none := by
  rw [envLookupT_none_iff]
  intro z hz
  cases hzy : (z == y) with
  | false => rfl
  | true =>
    have : l.contains y = true := List.contains_iff_exists_mem_beq.mpr ⟨z, hz, varId_beq_symm hzy⟩
    rw [h] at this; cases this

theorem envLookupT_append_of_none {l env : List VarId} {y : VarId} (h : envLookupT l y = none) :
    envLookupT (l ++ env) y = (envLookupT env y).map (· + l.length) := by
  induction l with
  | nil => simp
  | cons z zs ih =>
    rw [envLookupT_cons] at h
    split at h
    · cases h
    · rename_i hz
      rw [List.cons_append, envLookupT_cons, if_neg hz]
      cases hzs : envLookupT zs y with
      | some _ => rw [hzs] at h; cases h
      | none =>
        rw [ih hzs]
        cases envLookupT env y <;> simp; omega

/-! ## Extending environments by several values -/

def extendAll : CekEnv → List CekValue → CekEnv
  | ρ, [] => ρ
  | ρ, v :: vs => extendAll (ρ.extend v) vs

theorem dropEnv_extendAll : ∀ (ρ : CekEnv) (vals : List CekValue),
    dropEnv vals.length (extendAll ρ vals) = ρ
  | ρ, [] => rfl
  | ρ, v :: vs => by
    simp only [extendAll, List.length_cons]
    rw [← dropEnv_add, dropEnv_extendAll (ρ.extend v) vs]
    rfl

theorem lookup_extendAll (ρ : CekEnv) (vals : List CekValue) (n : Nat) (hn : 0 < n) :
    (extendAll ρ vals).lookup (n + vals.length) = ρ.lookup n := by
  have := dropEnv_lookup vals.length (extendAll ρ vals) n hn
  rw [dropEnv_extendAll] at this
  exact this.symm

theorem lookup_extendAll_lt : ∀ (ρ : CekEnv) (vals : List CekValue) (j : Nat), j < vals.length →
    (extendAll ρ vals).lookup (j + 1) = vals.reverse[j]?
  | ρ, [], j, h => by simp at h
  | ρ, v :: vs, j, h => by
    simp only [extendAll, List.reverse_cons]
    by_cases hj : j < vs.length
    · rw [lookup_extendAll_lt (ρ.extend v) vs j hj, List.getElem?_append_left (by simpa using hj)]
    · have hj' : j = vs.length := by simp at h; omega
      subst hj'
      rw [show vs.length + 1 = 1 + vs.length by omega, lookup_extendAll (ρ.extend v) vs 1 (by omega),
        List.getElem?_append_right (by simp)]
      simp
      rfl

/-! ## Facts and summaries in extended environments -/

theorem find?_zip_lookup {y : VarId} : ∀ (qs : List VarId) (bs : List Expr), qs.length = bs.length →
    ∀ entry, (qs.zip bs).find? (fun e => e.1 == y) = some entry →
      ∃ j, envLookupT qs y = some j ∧ bs[j]? = some entry.2
  | [], [], _, entry, h => by simp at h
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | q :: qs, b :: bs, hlen, entry, h => by
    rw [List.zip_cons_cons, List.find?_cons] at h
    rw [envLookupT_cons]
    cases hq : (q == y) with
    | true =>
      rw [hq] at h; cases h; exact ⟨0, by simp, rfl⟩
    | false =>
      rw [hq] at h
      obtain ⟨j, hj, hb⟩ := find?_zip_lookup qs bs (by simpa using hlen) entry h
      exact ⟨j + 1, by simp [hj], hb⟩

theorem find?_zip_none {y : VarId} : ∀ (qs : List VarId) (bs : List Expr), qs.length = bs.length →
    (qs.zip bs).find? (fun e => e.1 == y) = none → envLookupT qs y = none
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | q :: qs, b :: bs, hlen, h => by
    rw [List.zip_cons_cons, List.find?_cons] at h
    rw [envLookupT_cons]
    cases hq : (q == y) with
    | true => rw [hq] at h; cases h
    | false =>
      rw [hq] at h
      simp [find?_zip_none qs bs (by simpa using hlen) h]

theorem FactsHold.mono_suffix {P Q : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} {env : List VarId} {ρ : CekEnv} (h : FactsHold P Γ env ρ)
    (hPQ : ∀ k ρs rhs v, k ≤ env.length → P (env.drop k) ρs rhs v → Q (env.drop k) ρs rhs v) :
    FactsHold Q Γ env ρ := by
  intro x entry i hf hl
  obtain ⟨v, k, hik, hk, hv, hp⟩ := h x entry i hf hl
  exact ⟨v, k, hik, hk, hv, hPQ k _ _ _ hk hp⟩

/-- Binding values for several names whose facts are the expressions that
    produced the values in the outer environment. -/
theorem FactsHold.bind {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ₀ : List (VarId × Expr)} {env : List VarId} {ρ ρ' : CekEnv}
    (qs : List VarId) (bs : List Expr) (us : List CekValue)
    (h : FactsHold P Γ₀ env ρ) (hbs : qs.length = bs.length) (hus : us.length = qs.length)
    (hlook : ∀ j, j < qs.length → ρ'.lookup (j + 1) = us[j]?) (hdrop : dropEnv qs.length ρ' = ρ)
    (hP : ∀ (j : Nat) a u, bs[j]? = some a → us[j]? = some u → P env ρ a u) :
    FactsHold P (qs.zip bs ++ Γ₀) (qs ++ env) ρ' := by
  intro y entry i hf hl
  rw [List.find?_append] at hf
  cases hz : (qs.zip bs).find? (fun e => e.1 == y) with
  | some e =>
    rw [hz] at hf
    simp only [Option.some_or, Option.some.injEq] at hf
    subst hf
    obtain ⟨j₀, hj, hb⟩ := find?_zip_lookup qs bs hbs e hz
    rw [envLookupT_append_of_some hj] at hl
    cases hl
    have hjlt : i < qs.length := by
      have := (List.getElem?_eq_some_iff.mp hb).1; omega
    obtain ⟨u, hu⟩ : ∃ u, us[i]? = some u := by
      cases hu : us[i]? with
      | none => rw [List.getElem?_eq_none_iff] at hu; omega
      | some u => exact ⟨u, rfl⟩
    refine ⟨u, qs.length, hjlt, by simp, by rw [hlook i hjlt, hu], ?_⟩
    rw [List.drop_left, hdrop]
    exact hP i e.2 u hb hu
  | none =>
    rw [hz] at hf
    simp only [Option.none_or] at hf
    have hq := find?_zip_none qs bs hbs hz
    rw [envLookupT_append_of_none hq] at hl
    cases hl₀ : envLookupT env y with
    | none => rw [hl₀] at hl; cases hl
    | some i₀ =>
      rw [hl₀] at hl
      simp only [Option.map_some, Option.some.injEq] at hl
      subst hl
      obtain ⟨v, k, hik, hk, hv, hp⟩ := h y entry i₀ hf hl₀
      refine ⟨v, qs.length + k, by omega, by simp; omega, ?_, ?_⟩
      · have := dropEnv_lookup qs.length ρ' (i₀ + 1) (by omega)
        rw [hdrop] at this
        rw [show i₀ + qs.length + 1 = i₀ + 1 + qs.length by omega, ← this, hv]
      · rw [← List.drop_drop, List.drop_left, ← dropEnv_add, hdrop]
        exact hp

/-- Binding names that carry no facts. -/
theorem FactsHold.append_fresh {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ₀ : List (VarId × Expr)} {env : List VarId} {ρ ρ' : CekEnv} (qs : List VarId)
    (h : FactsHold P Γ₀ env ρ) (hkeys : ∀ entry ∈ Γ₀, envLookupT qs entry.1 = none)
    (hdrop : dropEnv qs.length ρ' = ρ) :
    FactsHold P Γ₀ (qs ++ env) ρ' := by
  intro y entry i hf hl
  have hmem := List.mem_of_find?_eq_some hf
  have hq : envLookupT qs y = none := by
    have hbeq : (entry.1 == y) = true := by simpa using List.find?_some hf
    rw [← envLookupT_congr hbeq qs]; exact hkeys entry hmem
  rw [envLookupT_append_of_none hq] at hl
  cases hl₀ : envLookupT env y with
  | none => rw [hl₀] at hl; cases hl
  | some i₀ =>
    rw [hl₀] at hl
    simp only [Option.map_some, Option.some.injEq] at hl
    subst hl
    obtain ⟨v, k, hik, hk, hv, hp⟩ := h y entry i₀ hf hl₀
    refine ⟨v, qs.length + k, by omega, by simp; omega, ?_, ?_⟩
    · have := dropEnv_lookup qs.length ρ' (i₀ + 1) (by omega)
      rw [hdrop] at this
      rw [show i₀ + qs.length + 1 = i₀ + 1 + qs.length by omega, ← this, hv]
    · rw [← List.drop_drop, List.drop_left, ← dropEnv_add, hdrop]
      exact hp

theorem SummariesHold.append {S : List (VarId × Nat)} {env : List VarId} {ρ ρ' : CekEnv} {β : Budget}
    (qs : List VarId) (h : SummariesHold S env ρ β)
    (hnames : ∀ entry ∈ S, envLookupT qs entry.1 = none) (hdrop : dropEnv qs.length ρ' = ρ) :
    SummariesHold S (qs ++ env) ρ' β := by
  intro entry hmem i hl w hw
  rw [envLookupT_append_of_none (hnames entry hmem)] at hl
  cases hl₀ : envLookupT env entry.1 with
  | none => rw [hl₀] at hl; cases hl
  | some i₀ =>
    rw [hl₀] at hl
    simp only [Option.map_some, Option.some.injEq] at hl
    subst hl
    refine h entry hmem i₀ hl₀ w ?_
    have := dropEnv_lookup qs.length ρ' (i₀ + 1) (by omega)
    rw [hdrop] at this
    rw [this, ← hw]; congr 1; omega

theorem WithinBudget.append {S : List (VarId × Nat)} {env : List VarId} {β : Budget} {n : Nat}
    (qs : List VarId) (h : WithinBudget S env β n)
    (hnames : ∀ entry ∈ S, envLookupT qs entry.1 = none) :
    WithinBudget S (qs ++ env) β n := by
  intro entry hmem hb
  rw [envLookupT_append_of_none (hnames entry hmem)] at hb
  apply h entry hmem
  cases hl₀ : envLookupT env entry.1 with
  | none => rw [hl₀] at hb; cases hb
  | some _ => rfl

/-! ## Lambda telescopes -/

def lams : List VarId → Expr → Expr
  | [], body => body
  | p :: ps, body => .Lam p (lams ps body)

def lamsT : Nat → Term → Term
  | 0, t => t
  | n + 1, t => .Lam 0 (lamsT n t)

theorem lams_resultParameters : ∀ e : Expr, lams (resultParameters e).1 (resultParameters e).2 = e
  | .Lam x b => by
    simp only [resultParameters, lams]
    rw [lams_resultParameters b]
  | .Var _ | .Lit _ | .Builtin _ | .Error | .Fix _ _ | .App _ _ | .Force _ | .Delay _
  | .Constr _ _ | .Case _ _ | .Let _ _ => rfl

theorem lower_lams : ∀ (ps : List VarId) (res : Expr) (env : List VarId) (t : Term),
    lowerTotalExpr env (lams ps res) = some t →
    ∃ tr, lowerTotalExpr (ps.reverse ++ env) res = some tr ∧ t = lamsT ps.length tr
  | [], res, env, t, h => ⟨t, by simpa [lams] using h, rfl⟩
  | p :: ps, res, env, t, h => by
    obtain ⟨t', ht', rfl⟩ := lowerTotalExpr_lam_some (by simpa [lams] using h)
    obtain ⟨tr, htr, rfl⟩ := lower_lams ps res (p :: env) t' ht'
    exact ⟨tr, by simpa using htr, rfl⟩

theorem fresh_lams : ∀ (ps : List VarId) (res : Expr) (env : List VarId),
    freshIn env (lams ps res) = true → EnvDistinct env →
    freshIn (ps.reverse ++ env) res = true ∧ EnvDistinct (ps.reverse ++ env)
  | [], res, env, h, hd => ⟨by simpa [lams] using h, hd⟩
  | p :: ps, res, env, h, hd => by
    simp only [lams, freshIn, Bool.and_eq_true] at h
    have := fresh_lams ps res (p :: env) h.2 (hd.cons h.1)
    simpa using this

theorem step_lam (π : Stack) (ρ : CekEnv) (b : Term) :
    step (.compute π ρ (.Lam 0 b)) = .ret π (.VLam b ρ) := rfl

theorem step_applyArg_lam (π : Stack) (ρ : CekEnv) (b : Term) (a : CekValue) :
    step (.ret (.applyArg a :: π) (.VLam b ρ)) = .compute π (ρ.extend a) b := rfl

/-- Running a telescope of lambdas against as many application frames
    evaluates its body in the extended environment. -/
theorem telescope_halts : ∀ (n : Nat) (tr : Term) (ρ : CekEnv) (vals : List CekValue) (N : Nat)
    (v : CekValue), vals.length = n →
    steps N (.compute (vals.map Frame.applyArg) ρ (lamsT n tr)) = .halt v →
    ∃ M, M ≤ N ∧ HaltsIn (extendAll ρ vals) tr M v
  | 0, tr, ρ, [], N, v, _, h => ⟨N, Nat.le_refl _, h⟩
  | n + 1, tr, ρ, a :: as, N, v, hlen, h => by
    obtain ⟨m₁, rfl, h₁⟩ := steps_succ_of h (by simp)
    simp only [List.map_cons, lamsT] at h₁
    rw [step_lam] at h₁
    obtain ⟨m₂, rfl, h₂⟩ := steps_succ_of h₁ (by simp)
    rw [step_applyArg_lam] at h₂
    obtain ⟨M, hM, hh⟩ := telescope_halts n tr (ρ.extend a) as m₂ v (by simpa using hlen) h₂
    exact ⟨M, by omega, hh⟩
  | 0, _, _, _ :: _, _, _, hlen, _ => by simp at hlen
  | _ + 1, _, _, [], _, _, hlen, _ => by simp at hlen

/-- Applying the closure of a telescope to as many arguments as it binds. -/
theorem closure_telescope_halts {n : Nat} {tr : Term} {ρ : CekEnv} {a : CekValue} {as : List CekValue}
    {N : Nat} {v : CekValue} (hlen : as.length = n)
    (h : steps N (.ret ((a :: as).map Frame.applyArg) (.VLam (lamsT n tr) ρ)) = .halt v) :
    ∃ M, M < N ∧ HaltsIn (extendAll ρ (a :: as)) tr M v := by
  obtain ⟨m, rfl, hm⟩ := steps_succ_of h (by simp)
  simp only [List.map_cons] at hm
  rw [step_applyArg_lam] at hm
  obtain ⟨M, hM, hh⟩ := telescope_halts n tr (ρ.extend a) as m v hlen hm
  exact ⟨M, by omega, hh⟩

/-! ## Application spines -/

theorem lowerTotalExprList_index {env : List VarId} :
    ∀ {as : List Expr} {ts : List Term}, MIR.lowerTotalExprList env as = some ts →
      ts.length = as.length ∧
        ∀ (i : Nat) a t, as[i]? = some a → ts[i]? = some t → lowerTotalExpr env a = some t
  | [], ts, h => by
    rw [MIR.lowerTotalExprList_nil] at h; cases h
    exact ⟨rfl, fun i a t ha _ => by simp at ha⟩
  | a :: as, ts, h => by
    rw [MIR.lowerTotalExprList_cons] at h
    cases ha : lowerTotalExpr env a with
    | none => rw [ha] at h; cases h
    | some ta =>
      cases has : MIR.lowerTotalExprList env as with
      | none => rw [ha, has] at h; cases h
      | some tas =>
        rw [ha, has] at h; cases h
        obtain ⟨hlen, hidx⟩ := lowerTotalExprList_index has
        refine ⟨by simp [hlen], ?_⟩
        intro i b t hb ht
        cases i with
        | zero => simp at hb ht; subst hb ht; exact ha
        | succ i => exact hidx i b t (by simpa using hb) (by simpa using ht)

theorem spine_lower {env : List VarId} : ∀ (e : Expr) (acc : List Expr) (te : Term) (tacc : List Term),
    lowerTotalExpr env e = some te → MIR.lowerTotalExprList env acc = some tacc →
    ∃ th targs, lowerTotalExpr env (applicationSpine.go e acc).1 = some th ∧
      MIR.lowerTotalExprList env (applicationSpine.go e acc).2 = some targs ∧
      applySpineT te tacc = applySpineT th targs
  | .App f a, acc, te, tacc, h, hacc => by
    obtain ⟨tf, ta, hf, ha, rfl⟩ := lowerTotalExpr_app_some h
    have hacc' : MIR.lowerTotalExprList env (a :: acc) = some (ta :: tacc) := by
      rw [MIR.lowerTotalExprList_cons, ha, hacc]; rfl
    exact spine_lower f (a :: acc) tf (ta :: tacc) hf hacc'
  | .Var _, _, te, tacc, h, hacc | .Lit _, _, te, tacc, h, hacc | .Builtin _, _, te, tacc, h, hacc
  | .Error, _, te, tacc, h, hacc | .Lam _ _, _, te, tacc, h, hacc | .Fix _ _, _, te, tacc, h, hacc
  | .Force _, _, te, tacc, h, hacc | .Delay _, _, te, tacc, h, hacc
  | .Constr _ _, _, te, tacc, h, hacc | .Case _ _, _, te, tacc, h, hacc
  | .Let _ _, _, te, tacc, h, hacc => ⟨te, tacc, h, hacc, rfl⟩

theorem spine_fresh {env : List VarId} : ∀ (e : Expr) (acc : List Expr),
    freshIn env e = true → freshInList env acc = true →
    freshIn env (applicationSpine.go e acc).1 = true ∧ freshInList env (applicationSpine.go e acc).2 = true
  | .App f a, acc, h, hacc => by
    simp only [freshIn, Bool.and_eq_true] at h
    exact spine_fresh f (a :: acc) h.1 (by simp [freshInList, h.2, hacc])
  | .Var _, _, h, hacc | .Lit _, _, h, hacc | .Builtin _, _, h, hacc
  | .Error, _, h, hacc | .Lam _ _, _, h, hacc | .Fix _ _, _, h, hacc
  | .Force _, _, h, hacc | .Delay _, _, h, hacc
  | .Constr _ _, _, h, hacc | .Case _ _, _, h, hacc
  | .Let _ _, _, h, hacc => ⟨h, hacc⟩

/-! ## Counted case analysis -/

theorem ret_nil_halts {w v : CekValue} {n : Nat} (h : steps n (.ret [] w) = .halt v) : v = w := by
  obtain ⟨m, rfl, hm⟩ := steps_succ_of h (by simp)
  change steps m (.halt w) = .halt v at hm
  rw [steps_halt] at hm; cases hm; rfl

private theorem alternative_counted {ρ : CekEnv} {alt : Term} {fields : List CekValue} {v : CekValue}
    {m : Nat} (Q : CekValue → Prop)
    (halt : ∀ M w, M ≤ m → HaltsIn ρ alt M w → ∃ c, w = .VCon c ∧ Q (.VCon c))
    (h : steps m (.compute (fields.map Frame.applyArg ++ []) ρ alt) = .halt v) : Q v := by
  obtain ⟨K, w, hK, hw, rest⟩ := counted_sequence h
  obtain ⟨c, rfl, hq⟩ := halt (K + 1) w (by omega) hw
  cases fields with
  | nil => rw [ret_nil_halts rest]; exact hq
  | cons f fs =>
    obtain ⟨j, hj, hjs⟩ := steps_succ_of rest (by simp)
    simp only [List.map_cons, List.cons_append, step] at hjs
    rw [steps_error] at hjs; cases hjs

theorem case_result_counted {ρ : CekEnv} {s : Term} {talts : List Term} {N : Nat} {v : CekValue}
    (Q : CekValue → Prop) (h : HaltsIn ρ (.Case s talts) N v)
    (halt : ∀ alt ∈ talts, ∀ M w, M ≤ N → HaltsIn ρ alt M w → ∃ c, w = .VCon c ∧ Q (.VCon c)) :
    Q v := by
  obtain ⟨Ns, w, Nr, _, hr, hsum⟩ := haltsIn_case h
  obtain ⟨m, rfl, r⟩ := steps_succ_of hr (by simp)
  cases w with
  | VConstr tag fields =>
    simp only [step] at r
    cases hget : talts[tag]? with
    | none => rw [hget, steps_error] at r; cases r
    | some alt =>
      rw [hget] at r
      exact alternative_counted Q (fun M w hM hw => halt alt (List.mem_of_getElem? hget) M w (by omega) hw) r
  | VCon c =>
    simp only [step] at r
    cases hc : constToTagAndFields c with
    | none => rw [hc, steps_error] at r; cases r
    | some triple =>
      obtain ⟨tag, numCtors, fields⟩ := triple
      rw [hc] at r
      simp only at r
      split at r
      · rw [steps_error] at r; cases r
      · cases hget : talts[tag]? with
        | none => rw [hget, steps_error] at r; cases r
        | some alt =>
          rw [hget] at r
          exact alternative_counted Q
            (fun M w hM hw => halt alt (List.mem_of_getElem? hget) M w (by omega) hw) r
  | VLam _ _ | VDelay _ _ | VBuiltin _ _ _ =>
    simp only [step] at r; rw [steps_error] at r; cases r

/-! ## The fixed-point encoding -/

/-- The functional of the fixed-point encoding, closed over the outer environment. -/
def fixW (tb : Term) (ρ : CekEnv) : CekValue :=
  .VLam (.Apply (.Lam 0 (.Lam 0 tb)) (.Lam 0 (.Apply (.Apply (.Var 2) (.Var 2)) (.Var 1)))) ρ

/-- The value bound to the recursive name. -/
def fixR (tb : Term) (ρ : CekEnv) : CekValue :=
  .VLam (.Apply (.Apply (.Var 2) (.Var 2)) (.Var 1)) (ρ.extend (fixW tb ρ))

/-- The environment of the recursive function's body. -/
def fixEnv (tb : Term) (ρ : CekEnv) : CekEnv := (ρ.extend (fixW tb ρ)).extend (fixR tb ρ)

/-- The value of the fixed point. -/
def fixF (tb : Term) (ρ : CekEnv) : CekValue := .VLam tb (fixEnv tb ρ)

theorem fix_halts (tb : Term) (ρ : CekEnv) : HaltsIn ρ (fixLamWrapUplc tb) 17 (fixF tb ρ) := rfl

theorem fixR_steps (tb : Term) (ρ : CekEnv) (a : CekValue) (π : Stack) :
    steps 16 (.ret (.applyArg a :: π) (fixR tb ρ)) = .compute π ((fixEnv tb ρ).extend a) tb := rfl

theorem fixF_steps (tb : Term) (ρ : CekEnv) (a : CekValue) (π : Stack) :
    steps 1 (.ret (.applyArg a :: π) (fixF tb ρ)) = .compute π ((fixEnv tb ρ).extend a) tb := rfl

/-- Calls through the recursive name take longer than direct calls. -/
theorem boolFn_fixR {k B : Nat} {tb : Term} {ρ : CekEnv} (hk : 0 < k) (h : BoolFn k B (fixF tb ρ)) :
    BoolFn k B (fixR tb ρ) := by
  intro vals hlen m v hm hs
  cases vals with
  | nil => simp at hlen; omega
  | cons a as =>
    simp only [List.map_cons] at hs
    have h16 : 16 ≤ m := by
      apply Classical.byContradiction
      intro hlt
      have := fixR_steps tb ρ a (as.map Frame.applyArg)
      rw [show 16 = m + (16 - m) by omega, steps_trans, hs, steps_halt] at this
      cases this
    have hrest : steps (m - 16) (.compute (as.map Frame.applyArg) ((fixEnv tb ρ).extend a) tb) = .halt v := by
      rw [← fixR_steps tb ρ a, ← steps_trans, show 16 + (m - 16) = m by omega]; exact hs
    refine h (a :: as) hlen (1 + (m - 16)) v (by omega) ?_
    simp only [List.map_cons]
    rw [steps_trans, fixF_steps]; exact hrest

/-! ## More bookkeeping -/

theorem zip_reverse {α β : Type} {l : List α} {l' : List β} (h : l.length = l'.length) :
    (l.zip l').reverse = l.reverse.zip l'.reverse := by
  have := List.reverse_zipWith (f := Prod.mk) h
  simpa [List.zip] using this

theorem SummariesHold.cons {S : List (VarId × Nat)} {env : List VarId} {ρ : CekEnv} {β : Budget}
    {entry : VarId × Nat}
    (hhead : ∀ i, envLookupT env entry.1 = some i → ∀ w, ρ.lookup (i + 1) = some w →
      BoolFn entry.2 (β (varKey entry.1)) w)
    (htail : SummariesHold S env ρ β) : SummariesHold (entry :: S) env ρ β := by
  intro e hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · exact hhead
  · exact htail e hmem

theorem SummariesHold.congr {S : List (VarId × Nat)} {env : List VarId} {ρ : CekEnv} {β β' : Budget}
    (h : SummariesHold S env ρ β) (hβ : ∀ entry ∈ S, β' (varKey entry.1) = β (varKey entry.1)) :
    SummariesHold S env ρ β' := by
  intro entry hmem i hl w hw
  rw [hβ entry hmem]; exact h entry hmem i hl w hw

theorem WithinBudget.congr {S : List (VarId × Nat)} {env : List VarId} {β β' : Budget} {n : Nat}
    (h : WithinBudget S env β n) (hβ : ∀ entry ∈ S, β' (varKey entry.1) = β (varKey entry.1)) :
    WithinBudget S env β' n := by
  intro entry hmem hb
  rw [hβ entry hmem]; exact h entry hmem hb

theorem le_envMax : ∀ {l : List VarId} {y : VarId}, y ∈ l → y.uid ≤ envMax l
  | x :: xs, y, h => by
    simp only [envMax]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := le_envMax h; omega

theorem beq_false_of_uid_ne {x y : VarId} (h : x.uid ≠ y.uid) : (x == y) = false := by
  cases hxy : (x == y) with
  | false => rfl
  | true => rw [VarId.beq_true_iff] at hxy; exact absurd hxy.2 h

/-- Names absent from a list by `contains` are absent from its lookups. -/
theorem forall_beq_false_of_contains {l : List VarId} {y : VarId} (h : l.contains y = false) :
    ∀ z ∈ l, (z == y) = false := by
  intro z hz
  cases hzy : (z == y) with
  | false => rfl
  | true =>
    have : l.contains y = true := List.contains_iff_exists_mem_beq.mpr ⟨z, hz, varId_beq_symm hzy⟩
    rw [h] at this; cases this

theorem not_contains_of_filter {α : Type} {l : List α} {keep : α → Bool} {x : α}
    (h : x ∈ l.filter keep) : keep x = true := (List.mem_filter.mp h).2

/-- The soundness statement of `booleanResultCore` at a given fuel. -/
def ResultSound (fuel : Nat) : Prop :=
  ∀ (Γ : List (VarId × Expr)) (S : List (VarId × Nat)) (e : Expr) (β : Budget) {env : List VarId}
    {ρ : CekEnv} {t : Term} {n : Nat} {v : CekValue},
    booleanResultCore fuel Γ S e = true → EnvDistinct env → FactsHold (ProducesB S β) Γ env ρ →
    SummariesHold S env ρ β → WithinBudget S env β n → freshIn env e = true →
    lowerTotalExpr env e = some t → HaltsIn ρ t n v → BoolValue v

theorem producesB_hP {S : List (VarId × Nat)} {β : Budget} :
    ∀ env ρ rhs v, ProducesB S β env ρ rhs v → Produces env ρ rhs v ∧ freshIn env rhs = true :=
  fun _ _ _ _ h => h.produces

/-! ## The `let` case -/

theorem let_case {fuel : Nat} (ih : ResultSound fuel) (S' : List (VarId × Nat)) (β : Budget)
    (bound : List VarId) (hS' : ∀ entry ∈ S', bound.contains entry.1 = false) (body : Expr) :
    ∀ (rest : List (VarId × Expr × Bool)), (∀ b ∈ rest, b.1 ∈ bound) →
    ∀ (Γ₀ : List (VarId × Expr)) {env : List VarId} {ρ : CekEnv} {t : Term} {n : Nat} {v : CekValue},
      booleanResultCore fuel (rest.foldl (fun available (binder, rhs, _) => (binder, rhs) :: available) Γ₀)
        S' body = true →
      EnvDistinct env → FactsHold (ProducesB S' β) Γ₀ env ρ → SummariesHold S' env ρ β →
      WithinBudget S' env β n → freshIn env (.Let rest body) = true →
      lowerTotalExpr env (.Let rest body) = some t → HaltsIn ρ t n v → BoolValue v
  | [], _, Γ₀, env, ρ, t, n, v, h, hd, hfacts, hsum, hbud, hfresh, hlow, hv => by
    rw [freshIn_let_nil] at hfresh
    rw [lowerTotalExpr_let_nil] at hlow
    exact ih Γ₀ S' body β h hd hfacts hsum hbud hfresh hlow hv
  | (x, r, er) :: rest, hbound, Γ₀, env, ρ, t, n, v, h, hd, hfacts, hsum, hbud, hfresh, hlow, hv => by
    rw [freshIn_let_cons] at hfresh
    simp only [freshIn, freshInLet, Bool.and_eq_true] at hfresh
    obtain ⟨⟨hfr, hx⟩, hrest⟩ := hfresh
    rw [lowerTotalExpr_let_cons] at hlow
    obtain ⟨tr, tb, htr, htb, rfl⟩ := lowerTotalExpr_let_single_some hlow
    obtain ⟨Nr, w, Nb, hr, hb, hsum'⟩ := haltsIn_let hv
    have hxS : ∀ entry ∈ S', envLookupT [x] entry.1 = none := by
      intro entry hmem
      rw [envLookupT_none_iff]
      intro z hz
      simp only [List.mem_singleton] at hz; subst hz
      exact forall_beq_false_of_contains (hS' entry hmem) _ (hbound _ (.head _))
    refine let_case ih S' β bound hS' body rest (fun b hb => hbound b (.tail _ hb)) ((x, r) :: Γ₀)
      (env := x :: env) (by simpa [List.foldl] using h) (hd.cons hx)
      (hfacts.push ⟨tr, Nr, htr, hr, hbud.le (by omega), hfr⟩)
      (SummariesHold.append [x] hsum hxS rfl) (WithinBudget.append [x] (hbud.le (by omega)) hxS)
      (by simpa [freshIn] using hrest) htb hb

/-! ## Applied lambda telescopes -/

theorem envLookupT_reverse_none {ps : List VarId} {y : VarId} (h : ps.contains y = false) :
    envLookupT ps.reverse y = none := by
  rw [envLookupT_none_iff]
  intro z hz
  exact forall_beq_false_of_contains h z (List.mem_reverse.mp hz)

theorem lam_case {fuel : Nat} (ih : ResultSound fuel) (Γ : List (VarId × Expr)) (S : List (VarId × Nat))
    (β : Budget) {env : List VarId} {ρ : CekEnv} (binder : VarId) (body₀ : Expr) (ps : List VarId)
    (res : Expr) (args : List Expr) (targs : List Term) (vals : List CekValue) {th : Term} {Nh Nc n : Nat}
    {wh v : CekValue}
    (hps : resultParameters (.Lam binder body₀) = (ps, res)) (hlen : ps.length = args.length)
    (h : booleanResultCore fuel ((ps.zip args).reverse ++ Γ.filter (fun entry => !ps.contains entry.1))
      (S.filter (fun entry => !ps.contains entry.1)) res = true)
    (hd : EnvDistinct env) (hfacts : FactsHold (ProducesB S β) Γ env ρ) (hsum : SummariesHold S env ρ β)
    (hbud : WithinBudget S env β n) (hfresh : freshIn env (.Lam binder body₀) = true)
    (hfargs : freshInList env args = true)
    (hlow : lowerTotalExpr env (.Lam binder body₀) = some th)
    (htargs : MIR.lowerTotalExprList env args = some targs)
    (hhead : HaltsIn ρ th Nh wh) (hvlen : vals.length = targs.length)
    (hargs : ∀ (i : Nat) (ta : Term) (va : CekValue), targs[i]? = some ta → vals[i]? = some va →
      ∃ m, m ≤ n ∧ HaltsIn ρ ta m va)
    (hchain : steps Nc (.ret (vals.map Frame.applyArg) wh) = .halt v) (hNc : Nc ≤ n) : BoolValue v := by
  have hlams : Expr.Lam binder body₀ = lams ps res := by
    rw [← lams_resultParameters (.Lam binder body₀), hps]
  obtain ⟨htlen, hidx⟩ := lowerTotalExprList_index htargs
  cases ps with
  | nil => simp [resultParameters] at hps
  | cons p ps' =>
    rw [hlams] at hlow hfresh
    obtain ⟨tr, htr, rfl⟩ := lower_lams (p :: ps') res env th hlow
    have hwh : wh = .VLam (lamsT ps'.length tr) ρ := halts_lam hhead.halts
    subst hwh
    cases vals with
    | nil => simp at hvlen hlen; omega
    | cons a₀ as =>
      obtain ⟨M, hM, hres⟩ := closure_telescope_halts (by simp at hvlen hlen; omega) hchain
      obtain ⟨hfr, hd'⟩ := fresh_lams (p :: ps') res env hfresh hd
      have hdrop : dropEnv (p :: ps').reverse.length (extendAll ρ (a₀ :: as)) = ρ := by
        have := dropEnv_extendAll ρ (a₀ :: as)
        rwa [show (a₀ :: as).length = (p :: ps').reverse.length by simp at hvlen hlen ⊢; omega] at this
      have hnames : ∀ entry ∈ S.filter (fun entry => !(p :: ps').contains entry.1),
          envLookupT (p :: ps').reverse entry.1 = none := by
        intro entry hmem
        exact envLookupT_reverse_none (by simpa using not_contains_of_filter hmem)
      have hΓ₀ : FactsHold (ProducesB (S.filter (fun entry => !(p :: ps').contains entry.1)) β)
          (Γ.filter (fun entry => !(p :: ps').contains entry.1)) env ρ :=
        (hfacts.filter (fun x => !(p :: ps').contains x)
          (fun x y hxy => by simp only [contains_congr hxy])).mono
          (fun _ _ _ _ hp => hp.sub filter_mem)
      have hbind := FactsHold.bind (p :: ps').reverse args.reverse (a₀ :: as).reverse hΓ₀
        (by simp only [List.length_reverse]; exact hlen) (by simp at hvlen hlen ⊢; omega)
        (fun j hj => lookup_extendAll_lt ρ (a₀ :: as) j (by simp at hj hvlen hlen ⊢; omega)) hdrop
        (by
          intro j a u ha hu
          have hj : j < args.length := by
            have := (List.getElem?_eq_some_iff.mp ha).1; simpa using this
          rw [List.getElem?_reverse (by simpa using hj)] at ha
          rw [List.getElem?_reverse (by simp at hvlen hlen ⊢; omega)] at hu
          have hvl : (a₀ :: as).length = args.length := by simp at hvlen hlen ⊢; omega
          rw [hvl] at hu
          obtain ⟨ta, hta⟩ : ∃ ta, targs[args.length - 1 - j]? = some ta := by
            cases hta : targs[args.length - 1 - j]? with
            | none => rw [List.getElem?_eq_none_iff] at hta; omega
            | some ta => exact ⟨ta, rfl⟩
          obtain ⟨m, hm, hhalt⟩ := hargs _ ta u hta hu
          exact ⟨ta, m, hidx _ a ta ha hta, hhalt, (hbud.sub filter_mem).le hm,
            freshInList_iff.mp hfargs a (List.mem_of_getElem? ha)⟩)
      rw [← zip_reverse hlen] at hbind
      exact ih _ _ res β h hd' hbind
        (SummariesHold.append (p :: ps').reverse (hsum.sub filter_mem) hnames hdrop)
        (WithinBudget.append (p :: ps').reverse ((hbud.sub filter_mem).le (by omega)) hnames)
        hfr htr hres

/-! ## Recursive functions -/

theorem EnvDistinct.append_lookup_none : ∀ {l : List VarId} {y : VarId} {rest : List VarId},
    EnvDistinct (l ++ y :: rest) → envLookupT l y = none
  | [], _, _, _ => rfl
  | z :: l, y, rest, hd => by
    have ih := EnvDistinct.append_lookup_none hd.2
    rw [envLookupT_cons]
    cases hzy : (z == y) with
    | true =>
      exfalso
      have h1 : envLookupT (l ++ y :: rest) z = none := hd.1
      have : envLookupT (l ++ y :: rest) z = envLookupT (l ++ y :: rest) y := envLookupT_congr hzy _
      rw [h1, envLookupT_append_of_none ih, envLookupT_cons, if_pos (varId_beq_self y)] at this
      cases this
    | false => simp [ih]

theorem avoids_insert (env : List VarId) (s : VarId) (bound : Nat) (hs : bound < s.uid) :
    Avoids env (s :: env) bound := by
  intro y hy
  rw [envLookupT_cons] at hy
  split at hy
  · rename_i hsy
    right
    rw [VarId.beq_true_iff] at hsy
    omega
  · left; simpa using hy

theorem fix_case {fuel : Nat} (ih : ResultSound fuel) (Γ : List (VarId × Expr)) (S : List (VarId × Nat))
    (β : Budget) {env : List VarId} {ρ : CekEnv} (rec : VarId) (body₀ : Expr) (ps : List VarId)
    (res : Expr) (args : List Expr) (vals : List CekValue) {th : Term} {Nh Nc n : Nat}
    {wh v : CekValue}
    (hps : resultParameters body₀ = (ps, res)) (hne : ps ≠ []) (hlen : ps.length = args.length)
    (h : booleanResultCore fuel (Γ.filter (fun entry => !(rec :: ps).contains entry.1))
      ((rec, ps.length) :: S.filter (fun entry => !(rec :: ps).contains entry.1)) res = true)
    (hd : EnvDistinct env) (hfacts : FactsHold (ProducesB S β) Γ env ρ) (hsum : SummariesHold S env ρ β)
    (hbud : WithinBudget S env β n) (hfresh : freshIn env (.Fix rec body₀) = true)
    (hlow : lowerTotalExpr env (.Fix rec body₀) = some th)
    (hhead : HaltsIn ρ th Nh wh) (hvlen : vals.length = args.length)
    (hchain : steps Nc (.ret (vals.map Frame.applyArg) wh) = .halt v) (hNc : Nc ≤ n) : BoolValue v := by
  have hlams : body₀ = lams ps res := by rw [← lams_resultParameters body₀, hps]
  cases ps with
  | nil => exact absurd rfl hne
  | cons x ps' =>
    subst hlams
    simp only [lams] at hlow hfresh
    simp only [freshIn, Bool.and_eq_true] at hfresh
    obtain ⟨hrec, hx, hfB⟩ := hfresh
    let B := lams ps' res
    let s : VarId := ⟨envMax env + envMax (Γ.map Prod.fst) + envMax (S.map Prod.fst) + maxUidExpr B +
      maxUidExpr (expandFix B) + rec.uid + x.uid + 1, .source, "s"⟩
    have hs_fv : (freeVars (expandFix B)).contains s = false := maxUidExpr_fresh _ _ (by simp [s]; omega)
    rw [lowerTotalExpr_fix_lam_with_fresh env rec x B s hs_fv] at hlow
    cases htb : lowerTotal (x :: rec :: s :: env) (expandFix B) with
    | none => rw [htb] at hlow; cases hlow
    | some tb =>
      rw [htb] at hlow; cases hlow
      have htbE : lowerTotalExpr (x :: rec :: s :: env) B = some tb := htb
      obtain ⟨tr, htr, htbeq⟩ := lower_lams ps' res (x :: rec :: s :: env) tb htbE
      have hwh : wh = fixF tb ρ := halts_unique hhead.halts (fix_halts tb ρ).halts
      subst hwh
      -- distinctness of the body environment
      have hs_env : envLookupT env s = none := envLookupT_none_of_gt env s (by simp [s]; omega)
      have hrec_env : envLookupT env rec = none := by simpa using hrec
      have hrec_s : envLookupT (s :: env) rec = none := by
        rw [envLookupT_cons, if_neg (by rw [beq_false_of_uid_ne (by simp [s]; omega)]; simp), hrec_env]
        rfl
      have hx' : envLookupT (rec :: env) x = none := by simpa using hx
      have hx_rs : envLookupT (rec :: s :: env) x = none := by
        rw [envLookupT_cons] at hx' ⊢
        split at hx'
        · cases hx'
        · rename_i hrx
          rw [if_neg hrx, envLookupT_cons, if_neg (by rw [beq_false_of_uid_ne (by simp [s]; omega)]; simp)]
          cases hxe : envLookupT env x with
          | none => rfl
          | some _ => rw [hxe] at hx'; cases hx'
      have hd₃ : EnvDistinct (x :: rec :: s :: env) := ⟨hx_rs, hrec_s, hs_env, hd⟩
      have hfB₃ : freshIn (x :: rec :: s :: env) B = true :=
        freshIn_avoids B hfB (((avoids_insert env s (maxUidExpr B) (by simp [s]; omega)).cons rec).cons x)
      obtain ⟨hfr, hd'⟩ := fresh_lams ps' res (x :: rec :: s :: env) hfB₃ hd₃
      have henv : ((x :: ps').reverse ++ [rec, s]) ++ env = ps'.reverse ++ x :: rec :: s :: env := by simp
      have hrec_ps : envLookupT (x :: ps').reverse rec = none := by
        have : EnvDistinct ((x :: ps').reverse ++ rec :: s :: env) := by simpa using hd'
        exact EnvDistinct.append_lookup_none this
      -- names hidden from the body
      let Γf := Γ.filter (fun entry => !(rec :: x :: ps').contains entry.1)
      let Sf := S.filter (fun entry => !(rec :: x :: ps').contains entry.1)
      have hkey_ne : ∀ entry ∈ Sf, varKey entry.1 ≠ varKey rec := by
        intro entry hmem heq
        have hc := not_contains_of_filter hmem
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hc
        have := forall_beq_false_of_contains hc rec (.head _)
        rw [beq_of_varKey heq.symm] at this; cases this
      have hfresh_names : ∀ y : VarId, (rec :: x :: ps').contains y = false → s.uid ≠ y.uid →
          envLookupT ((x :: ps').reverse ++ [rec, s]) y = none := by
        intro y hc hsy
        rw [envLookupT_none_iff]
        intro z hz
        simp only [List.mem_append, List.mem_reverse, List.mem_cons,
          List.not_mem_nil, or_false] at hz
        rcases hz with (hz | hz) | hz | hz
        · subst hz; exact forall_beq_false_of_contains hc _ (.tail _ (.head _))
        · exact forall_beq_false_of_contains hc z (.tail _ (.tail _ hz))
        · subst hz; exact forall_beq_false_of_contains hc _ (.head _)
        · subst hz; exact beq_false_of_uid_ne hsy
      have hkeys : ∀ entry ∈ Γf, envLookupT ((x :: ps').reverse ++ [rec, s]) entry.1 = none := by
        intro entry hmem
        have hc := not_contains_of_filter hmem
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hc
        refine hfresh_names entry.1 hc ?_
        have : entry.1.uid ≤ envMax (Γ.map Prod.fst) :=
          le_envMax (List.mem_map.mpr ⟨entry, filter_mem entry hmem, rfl⟩)
        simp [s]; omega
      have hnames : ∀ entry ∈ Sf, envLookupT ((x :: ps').reverse ++ [rec, s]) entry.1 = none := by
        intro entry hmem
        have hc := not_contains_of_filter hmem
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hc
        refine hfresh_names entry.1 hc ?_
        have : entry.1.uid ≤ envMax (S.map Prod.fst) :=
          le_envMax (List.mem_map.mpr ⟨entry, filter_mem entry hmem, rfl⟩)
        simp [s]; omega
      have hΓf : FactsHold (ProducesB S β) Γf env ρ :=
        hfacts.filter (fun y => !(rec :: x :: ps').contains y) (fun a b hab => by simp only [contains_congr hab])
      -- the summary of the recursive function, by strong induction on the budget
      have key : ∀ B₀, B₀ ≤ n → BoolFn (x :: ps').length B₀ (fixF tb ρ) := by
        intro B₀
        induction B₀ using Nat.strongRecOn with
        | ind B₀ IH =>
          intro hBn vals' hlen' m v' hm hs
          cases vals' with
          | nil => simp at hlen'
          | cons a₀ as =>
            subst htbeq
            obtain ⟨M, hM, hres⟩ := closure_telescope_halts (n := ps'.length) (by simpa using hlen') hs
            let β' : Budget := fun key => if key = varKey rec then M else β key
            have hβ : ∀ entry ∈ Sf, β' (varKey entry.1) = β (varKey entry.1) := by
              intro entry hmem; simp only [β']; rw [if_neg (hkey_ne entry hmem)]
            have hdropAll : dropEnv ((x :: ps').reverse ++ [rec, s]).length
                (extendAll (fixEnv (lamsT ps'.length tr) ρ) (a₀ :: as)) = ρ := by
              rw [show ((x :: ps').reverse ++ [rec, s]).length = (a₀ :: as).length + 2 by
                simp at hlen' ⊢; omega, ← dropEnv_add, dropEnv_extendAll]
              rfl
            have h1 : FactsHold (ProducesB ((rec, (x :: ps').length) :: Sf) β') Γf env ρ := by
              refine hΓf.mono_suffix (fun k ρs rhs w _ hp => ?_)
              obtain ⟨t', m', ht', hm', hb, hf⟩ := hp
              refine ⟨t', m', ht', hm', ?_, hf⟩
              intro entry hmem hbs
              rcases List.mem_cons.mp hmem with rfl | hmem
              · cases hl : envLookupT (env.drop k) rec with
                | none => rw [hl] at hbs; cases hbs
                | some i => rw [hd.drop_lookup k hl] at hrec_env; cases hrec_env
              · rw [hβ entry hmem]; exact hb entry (filter_mem entry hmem) hbs
            have h2 := FactsHold.append_fresh ((x :: ps').reverse ++ [rec, s]) h1 hkeys hdropAll
            have hsums : SummariesHold ((rec, (x :: ps').length) :: Sf)
                (((x :: ps').reverse ++ [rec, s]) ++ env) (extendAll (fixEnv (lamsT ps'.length tr) ρ) (a₀ :: as)) β' := by
              refine SummariesHold.cons ?_ (SummariesHold.append _ ((hsum.sub filter_mem).congr hβ) hnames hdropAll)
              intro i hl w hw
              rw [envLookupT_append_of_some (show envLookupT ((x :: ps').reverse ++ [rec, s]) rec = some (x :: ps').length by
                rw [envLookupT_append_of_none hrec_ps, envLookupT_cons, if_pos (varId_beq_self rec)]
                simp)] at hl
              cases hl
              have hlk := lookup_extendAll (fixEnv (lamsT ps'.length tr) ρ) (a₀ :: as) 1 (by omega)
              rw [show 1 + (a₀ :: as).length = (x :: ps').length + 1 by simp at hlen' ⊢; omega] at hlk
              rw [hlk] at hw
              change some (fixR (lamsT ps'.length tr) ρ) = some w at hw
              cases hw
              simp only [β', if_pos rfl]
              exact boolFn_fixR (by simp) (IH M (by omega) (by omega))
            have hbuds : WithinBudget ((rec, (x :: ps').length) :: Sf) (((x :: ps').reverse ++ [rec, s]) ++ env) β' M := by
              intro entry hmem hb
              rcases List.mem_cons.mp hmem with rfl | hmem
              · simp [β']
              · exact (WithinBudget.append _ (((hbud.sub filter_mem).le (by omega)).congr hβ) hnames)
                  entry hmem hb
            rw [henv] at h2 hsums hbuds
            exact ih Γf _ res β' h hd' h2 hsums hbuds hfr htr hres
      subst htbeq
      exact key n (Nat.le_refl _) vals (by simpa [hlen] using hvlen) Nc v hNc hchain

/-! ## Soundness of Boolean result summaries -/

theorem force_suspension {fuel : Nat} (ih : ResultSound fuel) {Γ : List (VarId × Expr)}
    {S : List (VarId × Nat)} {β : Budget} {env : List VarId} {ρ : CekEnv} {d : Expr} {w v : CekValue}
    {n Nr : Nat} (h : booleanResultCore fuel Γ S d = true) (hd : EnvDistinct env)
    (hsum : SummariesHold S env ρ β) (hbud : WithinBudget S env β n)
    (hsusp : SuspensionOf (ProducesB S β) Γ env ρ d w)
    (hr : steps Nr (.ret [.force] w) = .halt v) (hNr : Nr ≤ n) : BoolValue v := by
  obtain ⟨k, dt, _, hdt, rfl, hfd, hfacts', hd'⟩ := hsusp
  obtain ⟨m, rfl, hm⟩ := steps_succ_of hr (by simp)
  exact ih Γ S d β h hd' hfacts' (hsum.drop hd k) ((hbud.drop hd k).le (by omega)) hfd hdt hm

theorem booleanResultCore_sound : ∀ fuel, ResultSound fuel := by
  intro fuel
  induction fuel with
  | zero => intro Γ S e β env ρ t n v h; simp [booleanResultCore] at h
  | succ fuel ih =>
    intro Γ S e β env ρ t n v h hd hfacts hsum hbud hfresh hlow hv
    cases e with
    | Lit lit =>
      obtain ⟨c, ty⟩ := lit
      rw [lowerTotalExpr_lit] at hlow; cases hlow
      rw [halts_constant hv.halts]
      cases c <;> simp [booleanResultCore] at h
      exact ⟨_, rfl⟩
    | Error =>
      rw [lowerTotalExpr_error] at hlow; cases hlow
      exact absurd hv.halts not_halts_error
    | Var x =>
      simp only [booleanResultCore] at h
      cases hf : Γ.find? (fun entry => entry.1 == x) with
      | none => rw [hf] at h; cases h
      | some entry =>
        rw [hf] at h
        obtain ⟨i, hi, rfl⟩ := lowerTotalExpr_var_some hlow
        obtain ⟨w, k, _, _, hw, hp⟩ := hfacts x entry i hf hi
        have := halts_var hv.halts
        rw [hw] at this; cases this
        obtain ⟨t', m, ht', hm, hbud', hfr'⟩ := hp
        exact ih Γ S entry.2 β (by simpa using h) (hd.drop k) (hfacts.drop hd k) (hsum.drop hd k)
          hbud' hfr' ht' hm
    | Let bs body =>
      simp only [booleanResultCore] at h
      let bound := bs.map (·.1)
      have hS' : ∀ entry ∈ S.filter (fun entry => !bound.contains entry.1),
          bound.contains entry.1 = false := by
        intro entry hmem; simpa using not_contains_of_filter hmem
      exact let_case ih _ β bound hS' body bs (fun b hb => List.mem_map.mpr ⟨b, hb, rfl⟩) Γ h hd
        (hfacts.mono (fun _ _ _ _ hp => hp.sub filter_mem)) (hsum.sub filter_mem)
        (hbud.sub filter_mem) hfresh hlow hv
    | Case scrut alts =>
      simp only [booleanResultCore, Bool.and_eq_true, List.all_eq_true] at h
      obtain ⟨_, hall⟩ := h
      obtain ⟨ts, talts, _, htalts, rfl⟩ := lowerTotalExpr_case_some hlow
      simp only [freshIn, Bool.and_eq_true] at hfresh
      refine case_result_counted BoolValue hv ?_
      intro alt hmem M w hM hw
      obtain ⟨a', ha, hlowa⟩ := lowerTotalExprList_mem htalts alt hmem
      obtain ⟨c, rfl⟩ := ih Γ S a' β (hall a' ha) hd hfacts hsum (hbud.le hM)
        (freshInList_iff.mp hfresh.2 a' ha) hlowa hw
      exact ⟨_, rfl, c, rfl⟩
    | Force body =>
      simp only [booleanResultCore] at h
      obtain ⟨tb, htb, rfl⟩ := lowerTotalExpr_force_some hlow
      obtain ⟨Nt, w, Nr, hNt, hr, hsum'⟩ := haltsIn_force hv
      simp only [freshIn] at hfresh
      split at h
      · rename_i delayed heq
        exact force_suspension ih h hd hsum hbud
          (resolveHead_delay producesB_hP fuel Γ body heq hfacts hd hfresh htb hNt.halts) hr (by omega)
      · rename_i selector _ first second heq
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨hsel, hfirst⟩, hsecond⟩ := h
        rcases resolveHead_select producesB_hP fuel Γ body heq (beq_selector hsel) hfacts hd hfresh htb
          hNt.halts with hs | hs
        · exact force_suspension ih hfirst hd hsum hbud hs hr (by omega)
        · exact force_suspension ih hsecond hd hsum hbud hs hr (by omega)
      · cases h
    | App f a =>
      simp only [booleanResultCore] at h
      split at h
      · rename_i hbr
        obtain ⟨tf, ta, htf, hta, rfl⟩ := lowerTotalExpr_app_some hlow
        obtain ⟨wf, wa, hwf, hwa, rest⟩ := halts_apply hv.halts
        cases hp : builtinProtocolAfterSuccess (resolveHead fuel Γ f) with
        | none => rw [hp] at hbr; cases hbr
        | some pr =>
          obtain ⟨b, rem⟩ := pr
          rw [hp] at hbr
          simp only [Option.any_some, Bool.and_eq_true] at hbr
          obtain ⟨⟨hhead, hfinal⟩, hb⟩ := hbr
          have hrem : rem = .one .argV := by
            cases rem with
            | one k =>
              simp only [ExpectedArgs.head] at hhead
              cases k
              · rfl
              · exact absurd hhead (by decide)
            | more _ _ => simp [ExpectedArgs.isFinal] at hfinal
          subst hrem
          have hstate := resolveHead_protocol (fun _ _ _ _ hp => (producesB_hP _ _ _ _ hp).1) fuel Γ f hp
            hfacts hd htf hwf
          obtain ⟨args, hlen, heval⟩ := saturated_apply hstate rest
          exact booleanBuiltin_result hb hlen heval
      · have hsp : applicationSpine (f.App a) = applicationSpine.go (f.App a) [] := rfl
        obtain ⟨th, targs, hth, htargs, happ⟩ :=
          spine_lower (env := env) (f.App a) [] t [] hlow (MIR.lowerTotalExprList_nil env)
        obtain ⟨hfh, hfargs⟩ := spine_fresh (env := env) (f.App a) [] hfresh (by simp [freshInList])
        rw [← hsp] at hth htargs hfh hfargs
        generalize applicationSpine (f.App a) = sp at h hth htargs hfh hfargs
        obtain ⟨head, args⟩ := sp
        simp only at h hth htargs hfh hfargs
        change HaltsIn ρ (applySpineT t []) n v at hv
        rw [happ] at hv
        obtain ⟨Nh, wh, vals, Nc, hhead, hvlen, hargs, hchain, hNs⟩ := haltsIn_spine targs th hv
        have hNh : 1 ≤ Nh := by
          cases Nh with
          | zero => cases hhead
          | succ _ => omega
        obtain ⟨htlen, _⟩ := lowerTotalExprList_index htargs
        cases head with
        | Var binder =>
          simp only at h
          cases hf : S.find? (fun entry => entry.1 == binder) with
          | none => rw [hf] at h; cases h
          | some entry =>
            rw [hf] at h
            simp only [Option.any_some, beq_iff_eq] at h
            obtain ⟨i, hi, rfl⟩ := lowerTotalExpr_var_some hth
            have hlk := halts_var hhead.halts
            have hmem := List.mem_of_find?_eq_some hf
            have hbeq : (entry.1 == binder) = true := by simpa using List.find?_some hf
            have hi' : envLookupT env entry.1 = some i := by rw [envLookupT_congr hbeq]; exact hi
            exact hsum entry hmem i hi' wh hlk vals (by omega) Nc v
              (Nat.le_trans (by omega) (hbud entry hmem (by rw [hi']; rfl))) hchain
        | Fix recursive body =>
          simp only at h
          simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, beq_iff_eq] at h
          obtain ⟨⟨hne, hlen⟩, hres⟩ := h
          exact fix_case ih Γ S β recursive body _ _ args vals rfl hne hlen hres hd hfacts hsum hbud hfh hth
            hhead (by omega) hchain (by omega)
        | Lam binder body =>
          simp only at h
          simp only [Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨hlen, hres⟩ := h
          exact lam_case ih Γ S β binder body _ _ args targs vals rfl hlen hres hd hfacts hsum hbud hfh
            hfargs hth htargs hhead hvlen hargs hchain (by omega)
        | _ => simp at h
    | _ => simp [booleanResultCore] at h

theorem producesB_nil {P : List VarId → CekEnv → Expr → CekValue → Prop}
    (hP : ∀ env ρ rhs v, P env ρ rhs v → Produces env ρ rhs v ∧ freshIn env rhs = true) (β : Budget) :
    ∀ env ρ rhs v, P env ρ rhs v → ProducesB [] β env ρ rhs v := by
  intro env ρ rhs v hp
  obtain ⟨⟨t, ht, hh⟩, hf⟩ := hP env ρ rhs v hp
  obtain ⟨m, hm⟩ := hh
  refine ⟨t, m, ht, hm, ?_, hf⟩
  intro e he
  cases he

/-- An expression accepted by `knownBoolean` returns a Boolean constant
    whenever it returns. -/
theorem knownBoolean_sound {P : List VarId → CekEnv → Expr → CekValue → Prop}
    (hP : ∀ env ρ rhs v, P env ρ rhs v → Produces env ρ rhs v ∧ freshIn env rhs = true)
    (n : Nat) (Γ : List (VarId × Expr)) (e : Expr) {env : List VarId} {ρ : CekEnv} {t : Term}
    {v : CekValue} (h : knownBoolean n Γ e = true) (hfacts : FactsHold P Γ env ρ) (hd : EnvDistinct env)
    (hfresh : freshIn env e = true) (hlow : lowerTotalExpr env e = some t) (hv : Halts ρ t v) :
    BoolValue v := by
  simp only [knownBoolean, Bool.or_eq_true] at h
  rcases h with h | h
  · exact knownBooleanLocal_sound (fun _ _ _ _ hp => (hP _ _ _ _ hp).1) n Γ e h hfacts hd hlow hv
  · obtain ⟨m, hm⟩ := hv
    exact booleanResultCore_sound n Γ [] e (fun _ => 0) h hd (hfacts.mono (producesB_nil hP _))
      (fun _ he => by cases he) (fun _ he => by cases he) hfresh hlow hm

end Moist.Verified.ShapeFacts
