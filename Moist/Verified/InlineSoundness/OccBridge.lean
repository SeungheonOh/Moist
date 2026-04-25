import Moist.Verified.InlineSoundness.StrictOcc

/-! # Bridge: MIR occurrence analysis → UPLC StrictSingleOcc

This module proves that MIR-level occurrence analysis (`countOccurrences`,
`occursInDeferred`) corresponds to UPLC-level structural predicates
(`freeOf`, `StrictSingleOcc`) after compilation via `lowerTotal`.

## Architecture

The proof has three layers:

### Layer 1: Core bridge on Fix-free MIR expressions
Mutual induction on MIR expressions, simultaneously unfolding `lowerTotal`
and `countOccurrences`/`occursInDeferredAux`. Generalized over the de Bruijn
position `pos` to handle the shift under `Lam`/`Let` binders.

- `freeOf_lowerTotal_gen`: countOccurrences v e = 0 → freeOf pos t
- `strictSingleOcc_lowerTotal_gen`: count = 1 ∧ ¬deferred → StrictSingleOcc pos t
- List variants for Constr/Case arms

The `Fix` case is vacuous: `lowerTotal` returns `none` for Fix, contradicting
the compilation hypothesis.

### Layer 2: expandFix preservation
Show that `expandFix` preserves `countOccurrences` and `occursInDeferred`
for a variable `v` when `v` doesn't appear inside Fix bodies (guaranteed by
`countOccurrences = 0` or `¬occursInDeferred`).

### Layer 3: Public theorems
Compose layers 1 and 2 to get the final theorems used by `InlineSoundness`.

## Key invariants

- `envLookupT (env₁ ++ v :: env₂) v = some (env₁.length)` when `v ∉ env₁`
  (v maps to de Bruijn index `env₁.length + 1`)
- Under `Lam x body`: env grows by `x` at front, so v's position increases by 1,
  and `freeOf pos` shifts to `freeOf (pos + 1)` — these align.
- Under `Let (x, rhs, _) :: rest body`: similar shift via `lowerTotalLet`.
- `countOccurrences v (.Lam x body) = if x == v then 0 else countOccurrences v body`:
  binder shadowing stops counting, and `envLookupT` with shadowed v returns the
  binder's position instead — but since count = 0 under shadowing, freeOf holds
  vacuously for the shadowed de Bruijn index.
-/

namespace Moist.Verified.InlineSoundness.OccBridge

open Moist.CEK
open Moist.MIR (VarId Expr lowerTotal lowerTotalList lowerTotalLet
  expandFix expandFixBinds expandFixList
  countOccurrences countOccurrencesList countOccurrencesLet
  occursInDeferredAux occursInDeferredListAux occursInDeferredLetAux
  occursInDeferred envLookupT distinctBinders)
open Moist.Plutus.Term (Term)
open Moist.Verified.InlineSoundness.StrictOcc
  (freeOf freeOfList StrictSingleOcc StrictSingleOccList)

/-! ## VarId BEq helpers -/

private theorem varid_beq_refl (v : VarId) : (v == v) = true := by
  show (v.origin == v.origin && v.uid == v.uid) = true
  rw [Bool.and_eq_true]
  exact ⟨by cases v.origin <;> rfl, by simp [BEq.beq]⟩

/-! ## envLookupT lemmas -/

private theorem envLookupT_head (v : VarId) (env : List VarId) :
    envLookupT (v :: env) v = some 0 := by
  show envLookupT.go v (v :: env) 0 = some 0
  simp [envLookupT.go, varid_beq_refl]

private theorem envLookupT_cons_ne (x v : VarId) (env : List VarId)
    (hne : (x == v) = false) :
    envLookupT (x :: env) v = (envLookupT env v).map (· + 1) :=
  Moist.MIR.envLookupT_cons_neq x v env hne

/-! ## Layer 1: Core bridge (Fix-free, generalized position)

The generalized statement uses `env` and position `k`:
if every variable mapping to position `k` has zero occurrences
(resp. one strict occurrence) in `e`, then the compiled UPLC term
satisfies `freeOf (k+1)` (resp. `StrictSingleOcc (k+1)`).

This formulation handles binder shadowing uniformly: under `Lam x body`,
`env' = x :: env` and `k' = k + 1`. If `x == v`, then `envLookupT env' v = some 0 ≠ some (k+1)`,
so the hypothesis holds vacuously for the shadowed variable.
-/

section CoreBridge

/-! ### VarId BEq transitivity -/

private theorem varid_beq_symm {a b : VarId}
    (h : (a == b) = true) : (b == a) = true := by
  have h' : (a.origin == b.origin && a.uid == b.uid) = true := h
  rw [Bool.and_eq_true] at h'
  show (b.origin == a.origin && b.uid == a.uid) = true
  rw [Bool.and_eq_true]
  constructor
  · revert h'; cases a.origin <;> cases b.origin <;> simp [BEq.beq]
  · exact beq_iff_eq.mpr (beq_iff_eq.mp h'.2).symm

private theorem envLookupT_head_beq (v y : VarId) (env : List VarId)
    (hlu : envLookupT (v :: env) y = some 0) : (v == y) = true := by
  unfold envLookupT at hlu; simp [envLookupT.go] at hlu
  by_cases hvy : (v == y) = true
  · exact hvy
  · have hvyf : (v == y) = false := by cases h : (v == y) <;> simp_all
    rw [hvyf] at hlu; simp at hlu
    have := Moist.MIR.envLookupT.go_bound y env 1 0 hlu
    omega

private theorem varid_beq_congr {v w : VarId} (hvw : (v == w) = true)
    (x : VarId) : (x == v) = (x == w) := by
  have h : (v.origin == w.origin && v.uid == w.uid) = true := hvw
  rw [Bool.and_eq_true] at h
  have ho : v.origin = w.origin := by
    revert h; cases v.origin <;> cases w.origin <;> simp [BEq.beq]
  have hu : v.uid = w.uid := beq_iff_eq.mp h.2
  show (x.origin == v.origin && x.uid == v.uid) = (x.origin == w.origin && x.uid == w.uid)
  rw [ho, hu]

mutual
private theorem countOcc_beq_eq (v w : VarId) (e : Expr)
    (hvw : (v == w) = true) : countOccurrences v e = countOccurrences w e := by
  cases e with
  | Var x => simp [countOccurrences, varid_beq_congr hvw]
  | Lit _ | Builtin _ | Error => simp [countOccurrences]
  | Lam x body =>
    simp only [countOccurrences]; rw [varid_beq_congr hvw x]
    split
    · rfl
    · exact countOcc_beq_eq v w body hvw
  | Fix f body =>
    simp only [countOccurrences]; rw [varid_beq_congr hvw f]
    split
    · rfl
    · exact countOcc_beq_eq v w body hvw
  | App f x =>
    simp only [countOccurrences]
    rw [countOcc_beq_eq v w f hvw, countOcc_beq_eq v w x hvw]
  | Force e | Delay e =>
    simp only [countOccurrences]; exact countOcc_beq_eq v w e hvw
  | Constr _ args =>
    simp only [countOccurrences]; exact countOccList_beq_eq v w args hvw
  | Case scrut alts =>
    simp only [countOccurrences]
    rw [countOcc_beq_eq v w scrut hvw, countOccList_beq_eq v w alts hvw]
  | Let binds body =>
    simp only [countOccurrences]; exact countOccLet_beq_eq v w binds body hvw
termination_by sizeOf e

private theorem countOccList_beq_eq (v w : VarId) (es : List Expr)
    (hvw : (v == w) = true) : countOccurrencesList v es = countOccurrencesList w es := by
  cases es with
  | nil => simp [countOccurrencesList]
  | cons e rest =>
    simp only [countOccurrencesList]
    rw [countOcc_beq_eq v w e hvw, countOccList_beq_eq v w rest hvw]
termination_by sizeOf es

private theorem countOccLet_beq_eq (v w : VarId) (binds : List (VarId × Expr × Bool))
    (body : Expr) (hvw : (v == w) = true) :
    countOccurrencesLet v binds body = countOccurrencesLet w binds body := by
  cases binds with
  | nil => simp only [countOccurrencesLet]; exact countOcc_beq_eq v w body hvw
  | cons head rest =>
    obtain ⟨x, rhs, er⟩ := head
    simp only [countOccurrencesLet]; rw [varid_beq_congr hvw x, countOcc_beq_eq v w rhs hvw]
    split
    · rfl
    · rw [countOccLet_beq_eq v w rest body hvw]
termination_by sizeOf binds + sizeOf body
end

/-! ### freeOf bridge -/

private theorem envLookupT_cons_succ_inv {x y : VarId} {env : List VarId} {k : Nat}
    (hlu : envLookupT (x :: env) y = some (k + 1)) :
    (x == y) = false ∧ envLookupT env y = some k := by
  have hxy : (x == y) = false := by
    by_cases h : (x == y) = true
    · unfold envLookupT at hlu; simp [envLookupT.go, h] at hlu
    · exact Bool.eq_false_iff.mpr h
  exact ⟨hxy, by rw [envLookupT_cons_ne x y env hxy] at hlu; simp at hlu; exact hlu⟩

mutual
theorem freeOf_lowerTotal (env : List VarId) (k : Nat) (e : Expr) (t : Term)
    (hcomp : lowerTotal env e = some t)
    (hno_use : ∀ y, envLookupT env y = some k → countOccurrences y e = 0) :
    freeOf (k + 1) t = true := by
  match e with
  | .Var x =>
    rw [lowerTotal.eq_1] at hcomp
    cases hlu : envLookupT env x with
    | none => simp [hlu] at hcomp
    | some idx =>
      simp [hlu] at hcomp; subst hcomp; simp only [freeOf, bne_iff_ne, ne_eq]
      intro h
      have heq : idx = k := by omega
      subst heq
      have := hno_use x hlu; simp [countOccurrences, varid_beq_refl] at this
  | .Lit _ => rw [lowerTotal.eq_2] at hcomp; cases hcomp; simp [freeOf]
  | .Builtin _ => rw [lowerTotal.eq_3] at hcomp; cases hcomp; simp [freeOf]
  | .Error => rw [lowerTotal.eq_4] at hcomp; cases hcomp; simp [freeOf]
  | .Fix _ _ => rw [lowerTotal.eq_12] at hcomp; exact absurd hcomp (by simp)
  | .Lam x body =>
    rw [lowerTotal.eq_5] at hcomp
    match hb : lowerTotal (x :: env) body with
    | none => simp [hb] at hcomp
    | some body' =>
      simp [hb] at hcomp; subst hcomp; simp only [freeOf]
      exact freeOf_lowerTotal (x :: env) (k + 1) body body' hb (by
        intro y hlu'
        have ⟨hxy, hlu⟩ := envLookupT_cons_succ_inv hlu'
        have h := hno_use y hlu
        simp only [countOccurrences, hxy] at h; exact h)
  | .App f x =>
    rw [lowerTotal.eq_6] at hcomp
    match hf : lowerTotal env f, hx : lowerTotal env x with
    | some f', some x' =>
      simp [hf, hx] at hcomp; subst hcomp
      simp only [freeOf, Bool.and_eq_true]
      exact ⟨freeOf_lowerTotal env k f f' hf (fun y h => by
              have := hno_use y h; simp [countOccurrences] at this; exact this.1),
             freeOf_lowerTotal env k x x' hx (fun y h => by
              have := hno_use y h; simp [countOccurrences] at this; exact this.2)⟩
    | none, _ => simp [hf] at hcomp
    | some _, none => simp [hf, hx] at hcomp
  | .Force inner =>
    rw [lowerTotal.eq_7] at hcomp
    match hi : lowerTotal env inner with
    | none => simp [hi] at hcomp
    | some inner' =>
      simp [hi] at hcomp; subst hcomp; simp only [freeOf]
      exact freeOf_lowerTotal env k inner inner' hi (fun y h => by
        have := hno_use y h; simp [countOccurrences] at this; exact this)
  | .Delay inner =>
    rw [lowerTotal.eq_8] at hcomp
    match hi : lowerTotal env inner with
    | none => simp [hi] at hcomp
    | some inner' =>
      simp [hi] at hcomp; subst hcomp; simp only [freeOf]
      exact freeOf_lowerTotal env k inner inner' hi (fun y h => by
        have := hno_use y h; simp [countOccurrences] at this; exact this)
  | .Constr tag args =>
    rw [lowerTotal.eq_9] at hcomp
    match ha : lowerTotalList env args with
    | none => simp [ha] at hcomp
    | some args' =>
      simp [ha] at hcomp; subst hcomp; simp only [freeOf]
      exact freeOfList_lowerTotal env k args args' ha (fun y h => by
        have := hno_use y h; simp [countOccurrences] at this; exact this)
  | .Case scrut alts =>
    rw [lowerTotal.eq_10] at hcomp
    match hs : lowerTotal env scrut, ha : lowerTotalList env alts with
    | some s', some a' =>
      simp [hs, ha] at hcomp; subst hcomp
      simp only [freeOf, Bool.and_eq_true]
      exact ⟨freeOf_lowerTotal env k scrut s' hs (fun y h => by
              have := hno_use y h; simp [countOccurrences] at this; exact this.1),
             freeOfList_lowerTotal env k alts a' ha (fun y h => by
              have := hno_use y h; simp [countOccurrences] at this; exact this.2)⟩
    | none, _ => simp [hs] at hcomp
    | some _, none => simp [hs, ha] at hcomp
  | .Let binds body =>
    rw [lowerTotal.eq_11] at hcomp
    exact freeOf_lowerTotalLet env k binds body t hcomp (fun y h => by
      have := hno_use y h; simp [countOccurrences] at this; exact this)
termination_by sizeOf e

theorem freeOfList_lowerTotal (env : List VarId) (k : Nat)
    (es : List Expr) (ts : List Term)
    (hcomp : lowerTotalList env es = some ts)
    (hno_use : ∀ y, envLookupT env y = some k → countOccurrencesList y es = 0) :
    freeOfList (k + 1) ts = true := by
  match es with
  | [] => rw [lowerTotalList.eq_1] at hcomp; cases hcomp; simp [freeOfList]
  | e :: rest =>
    rw [lowerTotalList.eq_2] at hcomp
    match he : lowerTotal env e, hr : lowerTotalList env rest with
    | some t', some ts' =>
      simp [he, hr] at hcomp; subst hcomp
      simp only [freeOfList, Bool.and_eq_true]
      exact ⟨freeOf_lowerTotal env k e t' he (fun y h => by
              have := hno_use y h; simp [countOccurrencesList] at this; exact this.1),
             freeOfList_lowerTotal env k rest ts' hr (fun y h => by
              have := hno_use y h; simp [countOccurrencesList] at this; exact this.2)⟩
    | none, _ => simp [he] at hcomp
    | some _, none => simp [he, hr] at hcomp
termination_by sizeOf es

theorem freeOf_lowerTotalLet (env : List VarId) (k : Nat)
    (binds : List (VarId × Expr × Bool)) (body : Expr) (t : Term)
    (hcomp : lowerTotalLet env binds body = some t)
    (hno_use : ∀ y, envLookupT env y = some k → countOccurrencesLet y binds body = 0) :
    freeOf (k + 1) t = true := by
  match binds with
  | [] =>
    rw [lowerTotalLet.eq_1] at hcomp
    exact freeOf_lowerTotal env k body t hcomp (fun y h => by
      have := hno_use y h; simp [countOccurrencesLet] at this; exact this)
  | (x, rhs, er) :: rest =>
    rw [lowerTotalLet.eq_2] at hcomp
    match hr : lowerTotal env rhs, hrest : lowerTotalLet (x :: env) rest body with
    | some rhs', some rest' =>
      simp [hr, hrest] at hcomp; subst hcomp
      show freeOf (k + 1) (.Apply (.Lam 0 rest') rhs') = true
      simp only [freeOf, Bool.and_eq_true]
      constructor
      · exact freeOf_lowerTotalLet (x :: env) (k + 1) rest body rest' hrest (by
          intro y hlu'
          have ⟨hxy, hlu⟩ := envLookupT_cons_succ_inv hlu'
          have h := hno_use y hlu
          show countOccurrencesLet y rest body = 0
          simp only [countOccurrencesLet, hxy] at h
          exact Nat.eq_zero_of_add_eq_zero h |>.2)
      · exact freeOf_lowerTotal env k rhs rhs' hr (fun y h => by
          have := hno_use y h
          simp only [countOccurrencesLet] at this
          by_cases hxy : (x == y) = true
          · simp [hxy] at this; exact this
          · have hxyf : (x == y) = false := Bool.eq_false_iff.mpr hxy
            simp [hxyf] at this; exact this.1)
    | none, _ => simp [hr] at hcomp
    | some _, none => simp [hr, hrest] at hcomp
termination_by sizeOf binds + sizeOf body
end

/-! ### Connecting env-split formulation to env/k formulation -/

private theorem envLookupT_at_pos_match (envL : List VarId) (v : VarId) (envR : List VarId)
    (y : VarId)
    (hlu : envLookupT (envL ++ v :: envR) y = some envL.length) :
    (v == y) = true := by
  unfold envLookupT at hlu
  induction envL with
  | nil =>
    simp only [List.nil_append, List.length_nil] at hlu
    simp only [envLookupT.go] at hlu
    split at hlu
    · next h => exact h
    · next h => exfalso; have := Moist.MIR.envLookupT.go_bound y envR 1 0 hlu; omega
  | cons x envL' ih =>
    simp only [List.cons_append, List.length_cons] at hlu
    simp only [envLookupT.go] at hlu
    split at hlu
    · next h => simp only [Option.some.injEq] at hlu; omega
    · next h =>
      have hshift := Moist.MIR.envLookupT.go_shift y (envL' ++ v :: envR) 0 1
      simp only [Nat.zero_add] at hshift; rw [hshift] at hlu
      cases hbase : envLookupT.go y (envL' ++ v :: envR) 0 with
      | none => simp [hbase] at hlu
      | some idx =>
        simp [hbase] at hlu
        have : idx = envL'.length := by omega
        exact ih (by show envLookupT.go y (envL' ++ v :: envR) 0 = some envL'.length; rw [hbase, this])

private theorem hno_use_of_countOcc_zero {v : VarId} {envL envR : List VarId}
    {get_count : VarId → Nat}
    (hcount : get_count v = 0)
    (hbeq_eq : ∀ w, (v == w) = true → get_count v = get_count w) :
    ∀ y, envLookupT (envL ++ v :: envR) y = some envL.length → get_count y = 0 := by
  intro y hlu
  have hvy := envLookupT_at_pos_match envL v envR y hlu
  rw [← hbeq_eq y hvy]; exact hcount

/-! ### StrictSingleOcc bridge -/

private theorem freeOf_lowerTotal_of_countOcc_zero (v : VarId) (envL envR : List VarId)
    (e : Expr) (t : Term)
    (hcomp : lowerTotal (envL ++ v :: envR) e = some t)
    (hcount : countOccurrences v e = 0) :
    freeOf (envL.length + 1) t = true :=
  freeOf_lowerTotal _ _ _ _ hcomp
    (hno_use_of_countOcc_zero hcount (fun w h => countOcc_beq_eq v w e h))

private theorem freeOfList_lowerTotal_of_countOcc_zero (v : VarId) (envL envR : List VarId)
    (es : List Expr) (ts : List Term)
    (hcomp : lowerTotalList (envL ++ v :: envR) es = some ts)
    (hcount : countOccurrencesList v es = 0) :
    freeOfList (envL.length + 1) ts = true :=
  freeOfList_lowerTotal _ _ _ _ hcomp
    (hno_use_of_countOcc_zero hcount (fun w h => countOccList_beq_eq v w es h))

end CoreBridge

/-! ## Layer 2: expandFix preserves occurrence structure

When `countOccurrences v e = 0`, variable `v` doesn't appear free in `e`,
so `expandFix` (which only introduces fresh `.gen` binders) preserves this.

When `occursInDeferred v e = false` and `countOccurrences v e = 1`, variable
`v` doesn't appear inside any Fix body (Fix body is a deferred position), so
`expandFix` doesn't affect `v`'s occurrence.
-/

section ExpandFixPreservation

private theorem if_neg_beq {a b : VarId} (h : ¬(a == b) = true) :
    ((a == b) = true) = False := by
  have : (a == b) = false := by cases hb : (a == b) <;> simp_all
  simp [this]

mutual
private theorem occDefAux_false_of_countZero (w : VarId) (d : Bool) (e : Expr)
    (h : countOccurrences w e = 0) : occursInDeferredAux w d e = false := by
  match e with
  | .Var x =>
    simp only [countOccurrences] at h
    have hne : (x == w) = false := by
      by_cases hxw : (x == w) = true <;> simp_all
    simp [occursInDeferredAux, hne]
  | .Lit _ | .Builtin _ | .Error => simp [occursInDeferredAux]
  | .Lam x body =>
    simp only [occursInDeferredAux]
    by_cases hxw : (x == w) = true
    · simp [hxw]
    · have hxwf : (x == w) = false := by cases hb : (x == w) <;> simp_all
      simp only [hxwf]
      exact occDefAux_false_of_countZero w true body (by simp [countOccurrences, hxwf] at h; exact h)
  | .Fix f body =>
    simp only [occursInDeferredAux]
    by_cases hfw : (f == w) = true
    · simp [hfw]
    · have hfwf : (f == w) = false := by cases hb : (f == w) <;> simp_all
      simp only [hfwf]
      exact occDefAux_false_of_countZero w true body (by simp [countOccurrences, hfwf] at h; exact h)
  | .App f x =>
    simp only [countOccurrences, Nat.add_eq_zero] at h
    simp [occursInDeferredAux, occDefAux_false_of_countZero w d f h.1,
      occDefAux_false_of_countZero w d x h.2]
  | .Force e' =>
    simp only [countOccurrences] at h
    simp [occursInDeferredAux, occDefAux_false_of_countZero w d e' h]
  | .Delay e' =>
    simp only [countOccurrences] at h
    simp [occursInDeferredAux, occDefAux_false_of_countZero w true e' h]
  | .Constr _ args =>
    simp only [countOccurrences] at h
    simp [occursInDeferredAux, occDefListAux_false_of_countListZero w d args h]
  | .Case scrut alts =>
    simp only [countOccurrences, Nat.add_eq_zero] at h
    simp [occursInDeferredAux, occDefAux_false_of_countZero w d scrut h.1,
      occDefListAux_false_of_countListZero w true alts h.2]
  | .Let binds body =>
    simp only [countOccurrences] at h
    simp [occursInDeferredAux, occDefLetAux_false_of_countLetZero w d binds body h]
termination_by sizeOf e

private theorem occDefListAux_false_of_countListZero (w : VarId) (d : Bool)
    (es : List Expr) (h : countOccurrencesList w es = 0) :
    occursInDeferredListAux w d es = false := by
  match es with
  | [] => simp [occursInDeferredListAux]
  | e :: rest =>
    simp [countOccurrencesList] at h
    simp [occursInDeferredListAux, occDefAux_false_of_countZero w d e h.1,
      occDefListAux_false_of_countListZero w d rest h.2]
termination_by sizeOf es

private theorem occDefLetAux_false_of_countLetZero (w : VarId) (d : Bool)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (h : countOccurrencesLet w binds body = 0) :
    occursInDeferredLetAux w d binds body = false := by
  match binds with
  | [] => simp [countOccurrencesLet] at h; simp [occursInDeferredLetAux, occDefAux_false_of_countZero w d body h]
  | (x, rhs, _) :: rest =>
    simp only [countOccurrencesLet] at h
    simp only [occursInDeferredLetAux]
    by_cases hxw : (x == w) = true
    · simp only [hxw, ↓reduceIte]
      rw [Bool.or_eq_false_iff]
      constructor
      · exact occDefAux_false_of_countZero w d rhs (by simp [hxw] at h; exact h)
      · simp
    · simp only [show ¬((x == w) = true) from hxw] at h ⊢
      rw [Bool.or_eq_false_iff]
      have hrhs : countOccurrences w rhs = 0 := Nat.eq_zero_of_add_eq_zero h |>.1
      have hrest : countOccurrencesLet w rest body = 0 := Nat.eq_zero_of_add_eq_zero h |>.2
      exact ⟨occDefAux_false_of_countZero w d rhs hrhs,
             occDefLetAux_false_of_countLetZero w d rest body hrest⟩
termination_by sizeOf binds + sizeOf body
end

mutual
private theorem countZero_of_occDefAux_true (w : VarId) (e : Expr)
    (h : occursInDeferredAux w true e = false) : countOccurrences w e = 0 := by
  match e with
  | .Var x => simp [occursInDeferredAux] at h; simp [countOccurrences, h]
  | .Lit _ | .Builtin _ | .Error => simp [countOccurrences]
  | .Lam x body =>
    simp only [occursInDeferredAux] at h; simp only [countOccurrences]
    by_cases hxw : (x == w) = true <;> simp_all [countZero_of_occDefAux_true w body]
  | .Fix f body =>
    simp only [occursInDeferredAux] at h; simp only [countOccurrences]
    by_cases hfw : (f == w) = true <;> simp_all [countZero_of_occDefAux_true w body]
  | .App f x =>
    simp [occursInDeferredAux, Bool.or_eq_false_iff] at h
    simp [countOccurrences, countZero_of_occDefAux_true w f h.1, countZero_of_occDefAux_true w x h.2]
  | .Force e' => simp [occursInDeferredAux] at h; simp [countOccurrences, countZero_of_occDefAux_true w e' h]
  | .Delay e' => simp [occursInDeferredAux] at h; simp [countOccurrences, countZero_of_occDefAux_true w e' h]
  | .Constr _ args => simp [occursInDeferredAux] at h; simp [countOccurrences, countListZero_of_occDefListAux_true w args h]
  | .Case scrut alts =>
    simp [occursInDeferredAux, Bool.or_eq_false_iff] at h
    simp [countOccurrences, countZero_of_occDefAux_true w scrut h.1, countListZero_of_occDefListAux_true w alts h.2]
  | .Let binds body => simp [occursInDeferredAux] at h; simp [countOccurrences, countLetZero_of_occDefLetAux_true w binds body h]
termination_by sizeOf e

private theorem countListZero_of_occDefListAux_true (w : VarId) (es : List Expr)
    (h : occursInDeferredListAux w true es = false) : countOccurrencesList w es = 0 := by
  match es with
  | [] => simp [countOccurrencesList]
  | e :: rest =>
    simp [occursInDeferredListAux, Bool.or_eq_false_iff] at h
    simp [countOccurrencesList, countZero_of_occDefAux_true w e h.1, countListZero_of_occDefListAux_true w rest h.2]
termination_by sizeOf es

private theorem countLetZero_of_occDefLetAux_true (w : VarId)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (h : occursInDeferredLetAux w true binds body = false) :
    countOccurrencesLet w binds body = 0 := by
  match binds with
  | [] => simp [occursInDeferredLetAux] at h; simp [countOccurrencesLet, countZero_of_occDefAux_true w body h]
  | (x, rhs, _) :: rest =>
    by_cases hxw : (x == w) = true
    · show countOccurrencesLet w ((x, rhs, _) :: rest) body = 0
      simp only [countOccurrencesLet, hxw, ↓reduceIte]
      simp only [occursInDeferredLetAux, hxw, ↓reduceIte, Bool.or_eq_false_iff] at h
      exact countZero_of_occDefAux_true w rhs h.1
    · show countOccurrencesLet w ((x, rhs, _) :: rest) body = 0
      have hne : ¬ ((x == w) = true) := hxw
      simp only [countOccurrencesLet, if_neg hne]
      simp only [occursInDeferredLetAux, if_neg hne, Bool.or_eq_false_iff] at h
      have hrhs := countZero_of_occDefAux_true w rhs h.1
      have hrest := countLetZero_of_occDefLetAux_true w rest body h.2
      omega
termination_by sizeOf binds + sizeOf body
end

private theorem countOcc_expandFix_fix_zero_shadow (w f : VarId) (body : Expr)
    (hfw : (f == w) = true) :
    countOccurrences w (expandFix (.Fix f body)) = 0 :=
  match body with
  | .Lam x innerBody => by
    simp only [expandFix, countOccurrences]
    by_cases hz : (({ uid := Moist.MIR.maxUidExpr (expandFix innerBody) + 1 + 2, origin := .gen, hint := "z" : VarId}) == w) = true <;>
    by_cases hs : (({ uid := Moist.MIR.maxUidExpr (expandFix innerBody) + 1, origin := .gen, hint := "s" : VarId}) == w) = true <;>
    by_cases hx' : (x == w) = true <;>
    by_cases hv : (({ uid := Moist.MIR.maxUidExpr (expandFix innerBody) + 1 + 1, origin := .gen, hint := "v" : VarId}) == w) = true <;>
    simp (config := { decide := true }) only [*, ↓reduceIte] at * <;> omega
  | .Var _ | .Lit _ | .Builtin _ | .Error | .App _ _ | .Force _ | .Delay _
  | .Constr _ _ | .Case _ _ | .Let _ _ | .Fix _ _ => by
    simp only [expandFix, countOccurrences, hfw, ↓reduceIte]

private theorem countOcc_expandFix_fix_zero (w f : VarId) (body : Expr)
    (hbody0 : countOccurrences w body = 0)
    (hbody'0 : countOccurrences w (expandFix body) = 0) :
    countOccurrences w (expandFix (.Fix f body)) = 0 :=
  match body with
  | .Lam x innerBody => by
    show countOccurrences w (expandFix (.Fix f (.Lam x innerBody))) = 0
    unfold expandFix
    simp only [countOccurrences]
    have hinner'0 : ¬ (x == w) = true → countOccurrences w (expandFix innerBody) = 0 := by
      intro hxw; have h := hbody'0; simp only [expandFix, countOccurrences] at h
      simp only [show ¬((x == w) = true) from hxw] at h; exact h
    by_cases hx' : (x == w) = true
    · by_cases hz : (({ uid := Moist.MIR.maxUidExpr (expandFix innerBody) + 1 + 2, origin := .gen, hint := "z" : VarId}) == w) = true <;>
      by_cases hs : (({ uid := Moist.MIR.maxUidExpr (expandFix innerBody) + 1, origin := .gen, hint := "s" : VarId}) == w) = true <;>
      by_cases hf' : (f == w) = true <;>
      by_cases hv : (({ uid := Moist.MIR.maxUidExpr (expandFix innerBody) + 1 + 1, origin := .gen, hint := "v" : VarId}) == w) = true <;>
      simp (config := { decide := true }) only [*, ↓reduceIte] at * <;> omega
    · have h0 := hinner'0 hx'
      by_cases hz : (({ uid := Moist.MIR.maxUidExpr (expandFix innerBody) + 1 + 2, origin := .gen, hint := "z" : VarId}) == w) = true <;>
      by_cases hs : (({ uid := Moist.MIR.maxUidExpr (expandFix innerBody) + 1, origin := .gen, hint := "s" : VarId}) == w) = true <;>
      by_cases hf' : (f == w) = true <;>
      by_cases hv : (({ uid := Moist.MIR.maxUidExpr (expandFix innerBody) + 1 + 1, origin := .gen, hint := "v" : VarId}) == w) = true <;>
      simp (config := { decide := true }) only [*, ↓reduceIte] at * <;> omega
  | .Var _ | .Lit _ | .Builtin _ | .Error | .App _ _ | .Force _ | .Delay _
  | .Constr _ _ | .Case _ _ | .Let _ _ | .Fix _ _ => by
    by_cases hfw : (f == w) = true
    · simp (config := { decide := true }) only [expandFix, countOccurrences, hfw, ↓reduceIte]
    · simp only [expandFix, countOccurrences, show ¬((f == w) = true) from hfw] at hbody'0 ⊢
      first | exact hbody'0 | simp (config := { decide := true }) only [*]

mutual
theorem countOcc_expandFix_of_zero (w : VarId) (e : Expr)
    (h : countOccurrences w e = 0) :
    countOccurrences w (expandFix e) = 0 := by
  match e with
  | .Var _ | .Lit _ | .Builtin _ | .Error => simpa [expandFix] using h
  | .Lam x body =>
    simp only [expandFix, countOccurrences]
    by_cases hxw : (x == w) = true
    · simp only [hxw, ↓reduceIte]
    · simp only [show ¬((x == w) = true) from hxw]
      exact countOcc_expandFix_of_zero w body (by
        simp only [countOccurrences, show ¬((x == w) = true) from hxw] at h; exact h)
  | .Fix f body =>
    by_cases hfw : (f == w) = true
    · show countOccurrences w (expandFix (.Fix f body)) = 0
      exact countOcc_expandFix_fix_zero_shadow w f body hfw
    · have hbody0 : countOccurrences w body = 0 := by
        simp only [countOccurrences, show ¬((f == w) = true) from hfw] at h; exact h
      have hbody'0 := countOcc_expandFix_of_zero w body hbody0
      exact countOcc_expandFix_fix_zero w f body hbody0 hbody'0
  | .App f x =>
    simp [countOccurrences] at h
    simp [expandFix, countOccurrences, countOcc_expandFix_of_zero w f h.1, countOcc_expandFix_of_zero w x h.2]
  | .Force e' => simp [countOccurrences] at h; simp [expandFix, countOccurrences, countOcc_expandFix_of_zero w e' h]
  | .Delay e' => simp [countOccurrences] at h; simp [expandFix, countOccurrences, countOcc_expandFix_of_zero w e' h]
  | .Constr _ args => simp [countOccurrences] at h; simp [expandFix, countOccurrences, countOccList_expandFixList_of_zero w args h]
  | .Case scrut alts =>
    simp [countOccurrences] at h
    simp [expandFix, countOccurrences, countOcc_expandFix_of_zero w scrut h.1, countOccList_expandFixList_of_zero w alts h.2]
  | .Let binds body =>
    simp [countOccurrences] at h
    simp [expandFix, countOccurrences, countOccLet_expandFixBinds_of_zero w binds body h]
termination_by sizeOf e

private theorem countOccList_expandFixList_of_zero (w : VarId) (es : List Expr)
    (h : countOccurrencesList w es = 0) :
    countOccurrencesList w (expandFixList es) = 0 := by
  match es with
  | [] => simp [expandFixList, countOccurrencesList]
  | e :: rest =>
    simp [countOccurrencesList] at h
    simp [expandFixList, countOccurrencesList, countOcc_expandFix_of_zero w e h.1,
      countOccList_expandFixList_of_zero w rest h.2]
termination_by sizeOf es

private theorem countOccLet_expandFixBinds_of_zero (w : VarId)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (h : countOccurrencesLet w binds body = 0) :
    countOccurrencesLet w (expandFixBinds binds) (expandFix body) = 0 := by
  match binds with
  | [] => simp [expandFixBinds, countOccurrencesLet]; exact countOcc_expandFix_of_zero w body (by simp [countOccurrencesLet] at h; exact h)
  | (x, rhs, _) :: rest =>
    simp only [expandFixBinds, countOccurrencesLet]
    by_cases hxw : (x == w) = true
    · simp only [hxw, ↓reduceIte]
      have : countOccurrences w rhs = 0 := by
        simp only [countOccurrencesLet, hxw, ↓reduceIte] at h; exact h
      exact countOcc_expandFix_of_zero w rhs this
    · have hne := hxw
      simp only [if_neg hne]
      simp only [countOccurrencesLet, if_neg hne] at h
      have hrhs : countOccurrences w rhs = 0 := Nat.eq_zero_of_add_eq_zero h |>.1
      have hrest : countOccurrencesLet w rest body = 0 := Nat.eq_zero_of_add_eq_zero h |>.2
      have := countOcc_expandFix_of_zero w rhs hrhs
      have := countOccLet_expandFixBinds_of_zero w rest body hrest
      omega
termination_by sizeOf binds + sizeOf body
end

mutual
private theorem countOcc_pos_le_maxUid (w : VarId) (e : Expr)
    (h : countOccurrences w e > 0) :
    w.uid ≤ Moist.MIR.maxUidExpr e := by
  match e with
  | .Var x =>
    simp only [countOccurrences] at h
    by_cases hxw : (x == w) = true
    · rw [Moist.MIR.VarId.beq_true_iff] at hxw
      simp [Moist.MIR.maxUidExpr]
      omega
    · simp [hxw] at h
  | .Lit _ | .Builtin _ | .Error =>
    simp [countOccurrences] at h
  | .Lam x body =>
    by_cases hxw : (x == w) = true
    · simp [countOccurrences, hxw] at h
    · have hbody : countOccurrences w body > 0 := by
        simp [countOccurrences, hxw] at h
        exact h
      have ih := countOcc_pos_le_maxUid w body hbody
      simp [Moist.MIR.maxUidExpr]
      omega
  | .Fix f body =>
    by_cases hfw : (f == w) = true
    · simp [countOccurrences, hfw] at h
    · have hbody : countOccurrences w body > 0 := by
        simp [countOccurrences, hfw] at h
        exact h
      have ih := countOcc_pos_le_maxUid w body hbody
      simp [Moist.MIR.maxUidExpr]
      omega
  | .App f x =>
    have hf_or_hx : countOccurrences w f > 0 ∨ countOccurrences w x > 0 := by
      simp [countOccurrences] at h
      omega
    rcases hf_or_hx with hf | hx
    · have ih := countOcc_pos_le_maxUid w f hf
      simp [Moist.MIR.maxUidExpr]
      omega
    · have ih := countOcc_pos_le_maxUid w x hx
      simp [Moist.MIR.maxUidExpr]
      omega
  | .Force e' | .Delay e' =>
    have ih := countOcc_pos_le_maxUid w e' (by simpa [countOccurrences] using h)
    simpa [Moist.MIR.maxUidExpr]
  | .Constr _ args =>
    have ih := countOccList_pos_le_maxUid w args (by simpa [countOccurrences] using h)
    simpa [Moist.MIR.maxUidExpr]
  | .Case scrut alts =>
    have hs_or_ha : countOccurrences w scrut > 0 ∨ countOccurrencesList w alts > 0 := by
      simp [countOccurrences] at h
      omega
    rcases hs_or_ha with hs | ha
    · have ih := countOcc_pos_le_maxUid w scrut hs
      simp [Moist.MIR.maxUidExpr]
      omega
    · have ih := countOccList_pos_le_maxUid w alts ha
      simp [Moist.MIR.maxUidExpr]
      omega
  | .Let binds body =>
    have ih := countOccLet_pos_le_maxUid w binds body (by simpa [countOccurrences] using h)
    simpa [Moist.MIR.maxUidExpr] using ih
termination_by sizeOf e

private theorem countOccList_pos_le_maxUid (w : VarId) (es : List Expr)
    (h : countOccurrencesList w es > 0) :
    w.uid ≤ Moist.MIR.maxUidExprList es := by
  match es with
  | [] =>
    simp [countOccurrencesList] at h
  | e :: rest =>
    have he_or_hr : countOccurrences w e > 0 ∨ countOccurrencesList w rest > 0 := by
      simp [countOccurrencesList] at h
      omega
    rcases he_or_hr with he | hr
    · have ih := countOcc_pos_le_maxUid w e he
      simp [Moist.MIR.maxUidExprList]
      omega
    · have ih := countOccList_pos_le_maxUid w rest hr
      simp [Moist.MIR.maxUidExprList]
      omega
termination_by sizeOf es

private theorem countOccLet_pos_le_maxUid (w : VarId)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (h : countOccurrencesLet w binds body > 0) :
    w.uid ≤ max (Moist.MIR.maxUidExprBinds binds) (Moist.MIR.maxUidExpr body) := by
  match binds with
  | [] =>
    have ih := countOcc_pos_le_maxUid w body (by simpa [countOccurrencesLet] using h)
    simpa [Moist.MIR.maxUidExprBinds]
  | (x, rhs, er) :: rest =>
    by_cases hxw : (x == w) = true
    · have hrhs : countOccurrences w rhs > 0 := by
        simpa [countOccurrencesLet, hxw] using h
      have ih := countOcc_pos_le_maxUid w rhs hrhs
      simp [Moist.MIR.maxUidExprBinds]
      omega
    · have hrhs_or_hrest : countOccurrences w rhs > 0 ∨ countOccurrencesLet w rest body > 0 := by
        simp [countOccurrencesLet, hxw] at h
        omega
      rcases hrhs_or_hrest with hrhs | hrest
      · have ih := countOcc_pos_le_maxUid w rhs hrhs
        simp [Moist.MIR.maxUidExprBinds]
        omega
      · have ih := countOccLet_pos_le_maxUid w rest body hrest
        simp [Moist.MIR.maxUidExprBinds]
        omega
termination_by sizeOf binds + sizeOf body
end

mutual
theorem countOcc_expandFix_general (w : VarId) (e : Expr) :
    countOccurrences w (expandFix e) = countOccurrences w e := by
  match e with
  | .Var _ | .Lit _ | .Builtin _ | .Error => simp [expandFix]
  | .Lam x body =>
    simp only [expandFix, countOccurrences]
    by_cases hxw : (x == w) = true
    · simp [hxw]
    · simp [hxw, countOcc_expandFix_general w body]
  | .Fix f body =>
    by_cases hfw : (f == w) = true
    · have h0 := countOcc_expandFix_fix_zero_shadow w f body hfw
      simp only [countOccurrences, hfw, ↓reduceIte]; omega
    · simp only [countOccurrences, show ¬((f == w) = true) from hfw]
      by_cases hb0 : countOccurrences w body = 0
      · rw [hb0, countOcc_expandFix_fix_zero w f body hb0 (countOcc_expandFix_of_zero w body hb0)]
        simp
      · cases body with
        | Lam x inner =>
          have hxw : (x == w) = false := by
            cases hxeq : (x == w) with
            | false => rfl
            | true =>
              exfalso
              apply hb0
              simp [countOccurrences, hxeq]
          have hinner_ne_zero : countOccurrences w inner ≠ 0 := by
            intro hinner0
            apply hb0
            simp [countOccurrences, hxw, hinner0]
          have hinner_pos : countOccurrences w inner > 0 :=
            Nat.pos_of_ne_zero hinner_ne_zero
          have hinner_exp_pos : countOccurrences w (expandFix inner) > 0 := by
            rw [countOcc_expandFix_general w inner]
            exact hinner_pos
          have hwuid : w.uid ≤ Moist.MIR.maxUidExpr (expandFix inner) :=
            countOcc_pos_le_maxUid w (expandFix inner) hinner_exp_pos
          have hs_uid_gt :
              Moist.MIR.maxUidExpr (expandFix inner) + 1 > w.uid := by
            omega
          have hv_uid_gt :
              Moist.MIR.maxUidExpr (expandFix inner) + 2 > w.uid := by
            omega
          have hz_uid_gt :
              Moist.MIR.maxUidExpr (expandFix inner) + 3 > w.uid := by
            omega
          have hs_ne :
              ({ uid := Moist.MIR.maxUidExpr (expandFix inner) + 1
               , origin := .gen, hint := "s" : VarId } == w) = false := by
            rw [Moist.MIR.VarId.beq_false_iff]
            exact Or.inr (Nat.ne_of_gt hs_uid_gt)
          have hv_ne :
              ({ uid := Moist.MIR.maxUidExpr (expandFix inner) + 2
               , origin := .gen, hint := "v" : VarId } == w) = false := by
            rw [Moist.MIR.VarId.beq_false_iff]
            exact Or.inr (Nat.ne_of_gt hv_uid_gt)
          have hz_ne :
              ({ uid := Moist.MIR.maxUidExpr (expandFix inner) + 3
               , origin := .gen, hint := "z" : VarId } == w) = false := by
            rw [Moist.MIR.VarId.beq_false_iff]
            exact Or.inr (Nat.ne_of_gt hz_uid_gt)
          simp [expandFix, countOccurrences, hfw, hxw, hs_ne, hv_ne, hz_ne,
            countOcc_expandFix_general w inner]
        | Var _ =>
          simp [expandFix, countOccurrences, hfw]
        | Lit _ =>
          simp [expandFix, countOccurrences, hfw]
        | Builtin _ =>
          simp [expandFix, countOccurrences, hfw]
        | Error =>
          simp [expandFix, countOccurrences, hfw]
        | Fix g inner =>
          simpa [expandFix, countOccurrences, hfw] using
            countOcc_expandFix_general w (.Fix g inner)
        | App fn arg =>
          simp [expandFix, countOccurrences, hfw, countOcc_expandFix_general w fn,
            countOcc_expandFix_general w arg]
        | Force inner =>
          simp [expandFix, countOccurrences, hfw, countOcc_expandFix_general w inner]
        | Delay inner =>
          simp [expandFix, countOccurrences, hfw, countOcc_expandFix_general w inner]
        | Constr tag args =>
          simp [expandFix, countOccurrences, hfw, countOccList_expandFixList_general w args]
        | Case scrut alts =>
          simp [expandFix, countOccurrences, hfw, countOcc_expandFix_general w scrut,
            countOccList_expandFixList_general w alts]
        | Let binds inner =>
          simp [expandFix, countOccurrences, hfw, countOccLet_expandFixBinds_general w binds inner]
  | .Delay inner => simp [expandFix, countOccurrences, countOcc_expandFix_general w inner]
  | .App f x => simp [expandFix, countOccurrences, countOcc_expandFix_general w f, countOcc_expandFix_general w x]
  | .Force inner => simp [expandFix, countOccurrences, countOcc_expandFix_general w inner]
  | .Constr _ args => simp [expandFix, countOccurrences, countOccList_expandFixList_general w args]
  | .Case scrut alts =>
    simp [expandFix, countOccurrences, countOcc_expandFix_general w scrut, countOccList_expandFixList_general w alts]
  | .Let binds body =>
    simp [expandFix, countOccurrences, countOccLet_expandFixBinds_general w binds body]
termination_by sizeOf e

theorem countOccList_expandFixList_general (w : VarId) (es : List Expr) :
    countOccurrencesList w (expandFixList es) = countOccurrencesList w es := by
  match es with
  | [] => simp [expandFixList, countOccurrencesList]
  | e :: rest =>
    simp [expandFixList, countOccurrencesList, countOcc_expandFix_general w e,
      countOccList_expandFixList_general w rest]
termination_by sizeOf es

theorem countOccLet_expandFixBinds_general (w : VarId)
    (binds : List (VarId × Expr × Bool)) (body : Expr) :
    countOccurrencesLet w (expandFixBinds binds) (expandFix body) =
      countOccurrencesLet w binds body := by
  match binds with
  | [] => simp [expandFixBinds, countOccurrencesLet, countOcc_expandFix_general w body]
  | (x, rhs, er) :: rest =>
    simp only [expandFixBinds, countOccurrencesLet]
    by_cases hxw : (x == w) = true
    · rw [if_pos hxw, if_pos hxw, countOcc_expandFix_general w rhs]
    · rw [if_neg hxw, if_neg hxw, countOcc_expandFix_general w rhs,
          countOccLet_expandFixBinds_general w rest body]
termination_by sizeOf binds + sizeOf body
end

mutual
theorem countOcc_expandFix_of_not_deferred (w : VarId) (e : Expr)
    (hcount : countOccurrences w e = 1)
    (hnotdef : occursInDeferred w e = false) :
    countOccurrences w (expandFix e) = 1 := by
  match e with
  | .Var x =>
    simp [expandFix, countOccurrences] at hcount ⊢; exact hcount
  | .Lit _ | .Builtin _ | .Error => simp [countOccurrences] at hcount
  | .Lam x body =>
    simp only [countOccurrences] at hcount; simp only [occursInDeferred, occursInDeferredAux] at hnotdef
    by_cases hxw : (x == w) = true
    · simp only [hxw, ↓reduceIte] at hcount; omega
    · simp only [if_neg hxw] at hcount hnotdef; have := countZero_of_occDefAux_true w body hnotdef; omega
  | .Fix f body =>
    simp only [countOccurrences] at hcount; simp only [occursInDeferred, occursInDeferredAux] at hnotdef
    by_cases hfw : (f == w) = true
    · simp only [hfw, ↓reduceIte] at hcount; omega
    · simp only [if_neg hfw] at hcount hnotdef; have := countZero_of_occDefAux_true w body hnotdef; omega
  | .App f x =>
    simp [countOccurrences] at hcount
    simp [occursInDeferred, occursInDeferredAux, Bool.or_eq_false_iff] at hnotdef
    simp only [expandFix, countOccurrences]
    by_cases hf0 : countOccurrences w f = 0
    · have hx1 : countOccurrences w x = 1 := by omega
      rw [countOcc_expandFix_of_zero w f hf0,
          countOcc_expandFix_of_not_deferred w x hx1 (by show occursInDeferred w x = false; simp [occursInDeferred]; exact hnotdef.2)]
    · have hf1 : countOccurrences w f = 1 := by omega
      have hx0 : countOccurrences w x = 0 := by omega
      rw [countOcc_expandFix_of_not_deferred w f hf1 (by show occursInDeferred w f = false; simp [occursInDeferred]; exact hnotdef.1),
          countOcc_expandFix_of_zero w x hx0]
  | .Force e' =>
    simp [countOccurrences] at hcount; simp [occursInDeferred, occursInDeferredAux] at hnotdef
    simp [expandFix, countOccurrences, countOcc_expandFix_of_not_deferred w e' hcount (by simp [occursInDeferred]; exact hnotdef)]
  | .Delay e' =>
    simp [countOccurrences] at hcount; simp [occursInDeferred, occursInDeferredAux] at hnotdef
    have := countZero_of_occDefAux_true w e' hnotdef; omega
  | .Constr _ args =>
    simp [countOccurrences] at hcount; simp [occursInDeferred, occursInDeferredAux] at hnotdef
    simp [expandFix, countOccurrences, countOccList_expandFixList_of_not_deferred w args hcount hnotdef]
  | .Case scrut alts =>
    simp [countOccurrences] at hcount
    simp [occursInDeferred, occursInDeferredAux, Bool.or_eq_false_iff] at hnotdef
    have halt0 : countOccurrencesList w alts = 0 := countListZero_of_occDefListAux_true w alts hnotdef.2
    have hscrut1 : countOccurrences w scrut = 1 := by omega
    simp only [expandFix, countOccurrences]
    rw [countOcc_expandFix_of_not_deferred w scrut hscrut1 (by simp [occursInDeferred]; exact hnotdef.1),
        countOccList_expandFixList_of_zero w alts halt0]
  | .Let binds body =>
    simp only [countOccurrences] at hcount
    simp only [occursInDeferred, occursInDeferredAux] at hnotdef
    simp only [expandFix, countOccurrences]
    exact countOccLet_expandFixBinds_of_not_deferred w binds body hcount hnotdef
termination_by sizeOf e

private theorem countOccList_expandFixList_of_not_deferred (w : VarId) (es : List Expr)
    (hcount : countOccurrencesList w es = 1)
    (hnotdef : occursInDeferredListAux w false es = false) :
    countOccurrencesList w (expandFixList es) = 1 := by
  match es with
  | [] => simp [countOccurrencesList] at hcount
  | e :: rest =>
    simp [countOccurrencesList] at hcount
    simp [occursInDeferredListAux, Bool.or_eq_false_iff] at hnotdef
    simp only [expandFixList, countOccurrencesList]
    by_cases he0 : countOccurrences w e = 0
    · have hr1 : countOccurrencesList w rest = 1 := by omega
      rw [countOcc_expandFix_of_zero w e he0, countOccList_expandFixList_of_not_deferred w rest hr1 hnotdef.2]
    · have he1 : countOccurrences w e = 1 := by omega
      have hr0 : countOccurrencesList w rest = 0 := by omega
      rw [countOcc_expandFix_of_not_deferred w e he1 (by simp [occursInDeferred]; exact hnotdef.1),
          countOccList_expandFixList_of_zero w rest hr0]
termination_by sizeOf es

private theorem countOccLet_expandFixBinds_of_not_deferred (w : VarId)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (hcount : countOccurrencesLet w binds body = 1)
    (hnotdef : occursInDeferredLetAux w false binds body = false) :
    countOccurrencesLet w (expandFixBinds binds) (expandFix body) = 1 := by
  match binds with
  | [] =>
    simp [expandFixBinds, countOccurrencesLet, occursInDeferredLetAux] at *
    exact countOcc_expandFix_of_not_deferred w body hcount (by simp [occursInDeferred]; exact hnotdef)
  | (x, rhs, er) :: rest =>
    simp only [expandFixBinds, countOccurrencesLet]
    simp only [countOccurrencesLet] at hcount
    simp only [occursInDeferredLetAux] at hnotdef
    by_cases hxw : (x == w) = true
    · rw [if_pos hxw] at hcount ⊢
      rw [if_pos hxw, Bool.or_false] at hnotdef
      exact countOcc_expandFix_of_not_deferred w rhs hcount (by simp [occursInDeferred]; exact hnotdef)
    · rw [if_neg hxw] at hcount ⊢
      rw [if_neg hxw, Bool.or_eq_false_iff] at hnotdef
      by_cases hr0 : countOccurrences w rhs = 0
      · have hrest1 : countOccurrencesLet w rest body = 1 := by omega
        rw [countOcc_expandFix_of_zero w rhs hr0, countOccLet_expandFixBinds_of_not_deferred w rest body hrest1 hnotdef.2]
      · have hr1 : countOccurrences w rhs = 1 := by omega
        have hrest0 : countOccurrencesLet w rest body = 0 := by omega
        rw [countOcc_expandFix_of_not_deferred w rhs hr1 (by simp [occursInDeferred]; exact hnotdef.1),
            countOccLet_expandFixBinds_of_zero w rest body hrest0]
termination_by sizeOf binds + sizeOf body
end

mutual
theorem occursInDeferred_expandFix_of_not_deferred (w : VarId) (e : Expr)
    (hnotdef : occursInDeferred w e = false) :
    occursInDeferredAux w false (expandFix e) = false := by
  match e with
  | .Var _ | .Lit _ | .Builtin _ | .Error => simpa [expandFix] using hnotdef
  | .Lam x body =>
    simp only [occursInDeferred, occursInDeferredAux] at hnotdef
    simp only [expandFix, occursInDeferredAux]
    by_cases hxw : (x == w) = true <;> simp_all
    have := countZero_of_occDefAux_true w body hnotdef
    exact occDefAux_false_of_countZero w true (expandFix body) (countOcc_expandFix_of_zero w body this)
  | .Fix f body =>
    simp only [occursInDeferred, occursInDeferredAux] at hnotdef
    by_cases hfw : (f == w) = true
    · exact occDefAux_false_of_countZero w false (expandFix (.Fix f body))
        (countOcc_expandFix_fix_zero_shadow w f body hfw)
    · rw [if_neg hfw] at hnotdef
      have hbody0 := countZero_of_occDefAux_true w body hnotdef
      have hbody'0 := countOcc_expandFix_of_zero w body hbody0
      exact occDefAux_false_of_countZero w false (expandFix (.Fix f body))
        (countOcc_expandFix_fix_zero w f body hbody0 hbody'0)
  | .App f x =>
    simp [occursInDeferred, occursInDeferredAux, Bool.or_eq_false_iff] at hnotdef
    simp [expandFix, occursInDeferredAux, occursInDeferred_expandFix_of_not_deferred w f (by simp [occursInDeferred]; exact hnotdef.1),
      occursInDeferred_expandFix_of_not_deferred w x (by simp [occursInDeferred]; exact hnotdef.2)]
  | .Force e' =>
    simp [occursInDeferred, occursInDeferredAux] at hnotdef
    simp [expandFix, occursInDeferredAux, occursInDeferred_expandFix_of_not_deferred w e' (by simp [occursInDeferred]; exact hnotdef)]
  | .Delay e' =>
    simp [occursInDeferred, occursInDeferredAux] at hnotdef
    have := countZero_of_occDefAux_true w e' hnotdef
    exact occDefAux_false_of_countZero w false (expandFix (.Delay e')) (by simp [expandFix, countOccurrences, countOcc_expandFix_of_zero w e' this])
  | .Constr _ args =>
    simp [occursInDeferred, occursInDeferredAux] at hnotdef
    simp [expandFix, occursInDeferredAux, occDefListAux_expandFixList_of_not_deferred w args hnotdef]
  | .Case scrut alts =>
    simp [occursInDeferred, occursInDeferredAux, Bool.or_eq_false_iff] at hnotdef
    have alts_zero := countListZero_of_occDefListAux_true w alts hnotdef.2
    simp [expandFix, occursInDeferredAux,
      occursInDeferred_expandFix_of_not_deferred w scrut (by simp [occursInDeferred]; exact hnotdef.1),
      occDefListAux_false_of_countListZero w true (expandFixList alts) (countOccList_expandFixList_of_zero w alts alts_zero)]
  | .Let binds body =>
    simp [occursInDeferred, occursInDeferredAux] at hnotdef
    simp [expandFix, occursInDeferredAux, occDefLetAux_expandFixBinds_of_not_deferred w binds body hnotdef]
termination_by sizeOf e

private theorem occDefListAux_expandFixList_of_not_deferred (w : VarId) (es : List Expr)
    (hnotdef : occursInDeferredListAux w false es = false) :
    occursInDeferredListAux w false (expandFixList es) = false := by
  match es with
  | [] => simp [expandFixList, occursInDeferredListAux]
  | e :: rest =>
    simp [occursInDeferredListAux, Bool.or_eq_false_iff] at hnotdef
    simp [expandFixList, occursInDeferredListAux,
      occursInDeferred_expandFix_of_not_deferred w e (by simp [occursInDeferred]; exact hnotdef.1),
      occDefListAux_expandFixList_of_not_deferred w rest hnotdef.2]
termination_by sizeOf es

private theorem occDefLetAux_expandFixBinds_of_not_deferred (w : VarId)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (hnotdef : occursInDeferredLetAux w false binds body = false) :
    occursInDeferredLetAux w false (expandFixBinds binds) (expandFix body) = false := by
  match binds with
  | [] =>
    simp [expandFixBinds, occursInDeferredLetAux] at *
    exact occursInDeferred_expandFix_of_not_deferred w body (by simp [occursInDeferred]; exact hnotdef)
  | (x, rhs, er) :: rest =>
    simp only [expandFixBinds, occursInDeferredLetAux]
    simp only [occursInDeferredLetAux] at hnotdef
    by_cases hxw : (x == w) = true
    · rw [if_pos hxw]
      rw [if_pos hxw, Bool.or_false] at hnotdef
      rw [Bool.or_eq_false_iff]
      exact ⟨occursInDeferred_expandFix_of_not_deferred w rhs (by simp [occursInDeferred]; exact hnotdef), by rfl⟩
    · rw [if_neg hxw]
      rw [if_neg hxw, Bool.or_eq_false_iff] at hnotdef
      rw [Bool.or_eq_false_iff]
      exact ⟨occursInDeferred_expandFix_of_not_deferred w rhs (by simp [occursInDeferred]; exact hnotdef.1),
             occDefLetAux_expandFixBinds_of_not_deferred w rest body hnotdef.2⟩
termination_by sizeOf binds + sizeOf body
end

end ExpandFixPreservation

/-! ### StrictSingleOcc bridge helpers -/

private theorem envLookupT_go_beq_congr (x v : VarId) (env : List VarId) (k : Nat)
    (hxv : (x == v) = true) :
    envLookupT.go x env k = envLookupT.go v env k := by
  induction env generalizing k with
  | nil => rfl
  | cons h rest ih =>
    simp only [envLookupT.go]
    have : (h == x) = (h == v) := (varid_beq_congr (varid_beq_symm hxv) h).symm
    rw [this]
    split
    · rfl
    · exact ih (k + 1)

private theorem envLookupT_split_beq (envL : List VarId) (v : VarId) (envR : List VarId)
    (x : VarId) (hxv : (x == v) = true)
    (hv_notin : envL.findIdx? (· == v) = none) :
    envLookupT (envL ++ v :: envR) x = some envL.length := by
  show envLookupT.go x (envL ++ v :: envR) 0 = some envL.length
  rw [envLookupT_go_beq_congr x v _ 0 hxv]
  rw [List.findIdx?_eq_none_iff] at hv_notin
  induction envL with
  | nil => simp [envLookupT.go, varid_beq_refl]
  | cons y envL' ih =>
    have hyv : (y == v) = false := hv_notin y List.mem_cons_self
    simp only [List.cons_append, envLookupT.go, show ¬((y == v) = true) from by simp [hyv]]
    have hshift := Moist.MIR.envLookupT.go_shift v (envL' ++ v :: envR) 0 1
    simp only [Nat.zero_add] at hshift
    rw [hshift, ih (fun z hz => hv_notin z (List.mem_cons_of_mem _ hz))]
    simp

/-! ### Layer 1b: StrictSingleOcc bridge (Fix-free, generalized position) -/

mutual
theorem strictSingleOcc_lowerTotal (v : VarId) (envL envR : List VarId)
    (e : Expr) (t : Term)
    (hcomp : lowerTotal (envL ++ v :: envR) e = some t)
    (hcount : countOccurrences v e = 1)
    (hnotdef : occursInDeferredAux v false e = false)
    (hv_notin : envL.findIdx? (· == v) = none) :
    StrictSingleOcc (envL.length + 1) t := by
  match e with
  | .Var x =>
    rw [lowerTotal.eq_1] at hcomp
    simp only [countOccurrences] at hcount
    have hxv : (x == v) = true := by
      by_cases h : (x == v) = true <;> simp_all
    cases hlu : envLookupT (envL ++ v :: envR) x with
    | none => simp [hlu] at hcomp
    | some idx =>
      simp [hlu] at hcomp; subst hcomp
      have : idx = envL.length := by
        have := envLookupT_split_beq envL v envR x hxv hv_notin
        rw [hlu] at this; exact Option.some.inj this
      subst this; exact StrictSingleOcc.var
  | .Lit _ => simp [countOccurrences] at hcount
  | .Builtin _ => simp [countOccurrences] at hcount
  | .Error => simp [countOccurrences] at hcount
  | .Fix _ _ => rw [lowerTotal.eq_12] at hcomp; exact absurd hcomp (by simp)
  | .Lam x body =>
    simp only [countOccurrences, occursInDeferredAux] at hcount hnotdef
    by_cases hxv : (x == v) = true
    · simp [hxv] at hcount
    · exfalso
      rw [if_neg hxv] at hcount hnotdef
      have h0 : countOccurrences v body = 0 := countZero_of_occDefAux_true v body hnotdef
      omega
  | .Delay inner =>
    simp only [countOccurrences, occursInDeferredAux] at hcount hnotdef
    exfalso
    have h0 : countOccurrences v inner = 0 := countZero_of_occDefAux_true v inner hnotdef
    omega
  | .App f x =>
    rw [lowerTotal.eq_6] at hcomp
    simp only [countOccurrences] at hcount
    simp only [occursInDeferredAux, Bool.or_eq_false_iff] at hnotdef
    match hf : lowerTotal (envL ++ v :: envR) f, hx : lowerTotal (envL ++ v :: envR) x with
    | some f', some x' =>
      simp [hf, hx] at hcomp; subst hcomp
      by_cases hf0 : countOccurrences v f = 0
      · exact StrictSingleOcc.apply_r
          (freeOf_lowerTotal_of_countOcc_zero v envL envR f f' hf hf0)
          (strictSingleOcc_lowerTotal v envL envR x x' hx (by omega) hnotdef.2 hv_notin)
      · exact StrictSingleOcc.apply_l
          (strictSingleOcc_lowerTotal v envL envR f f' hf (by omega) hnotdef.1 hv_notin)
          (freeOf_lowerTotal_of_countOcc_zero v envL envR x x' hx (by omega))
    | none, _ => simp [hf] at hcomp
    | some _, none => simp [hf, hx] at hcomp
  | .Force inner =>
    rw [lowerTotal.eq_7] at hcomp
    simp only [countOccurrences] at hcount
    simp only [occursInDeferredAux] at hnotdef
    match hi : lowerTotal (envL ++ v :: envR) inner with
    | none => simp [hi] at hcomp
    | some inner' =>
      simp [hi] at hcomp; subst hcomp
      exact StrictSingleOcc.force
        (strictSingleOcc_lowerTotal v envL envR inner inner' hi hcount hnotdef hv_notin)
  | .Constr tag args =>
    rw [lowerTotal.eq_9] at hcomp
    simp only [countOccurrences] at hcount
    simp only [occursInDeferredAux] at hnotdef
    match ha : lowerTotalList (envL ++ v :: envR) args with
    | none => simp [ha] at hcomp
    | some args' =>
      simp [ha] at hcomp; subst hcomp
      exact StrictSingleOcc.constr
        (strictSingleOccList_lowerTotal v envL envR args args' ha hcount hnotdef hv_notin)
  | .Case scrut alts =>
    rw [lowerTotal.eq_10] at hcomp
    simp only [countOccurrences] at hcount
    simp only [occursInDeferredAux, Bool.or_eq_false_iff] at hnotdef
    match hs : lowerTotal (envL ++ v :: envR) scrut,
          ha : lowerTotalList (envL ++ v :: envR) alts with
    | some s', some a' =>
      simp [hs, ha] at hcomp; subst hcomp
      have halt0 := countListZero_of_occDefListAux_true v alts hnotdef.2
      exact StrictSingleOcc.case_scrut
        (strictSingleOcc_lowerTotal v envL envR scrut s' hs (by omega) hnotdef.1 hv_notin)
        (freeOfList_lowerTotal_of_countOcc_zero v envL envR alts a' ha halt0)
    | none, _ => simp [hs] at hcomp
    | some _, none => simp [hs, ha] at hcomp
  | .Let binds body =>
    rw [lowerTotal.eq_11] at hcomp
    simp only [countOccurrences] at hcount
    simp only [occursInDeferredAux] at hnotdef
    exact strictSingleOcc_lowerTotalLet v envL envR binds body t hcomp hcount hnotdef hv_notin
termination_by sizeOf e

theorem strictSingleOccList_lowerTotal (v : VarId) (envL envR : List VarId)
    (es : List Expr) (ts : List Term)
    (hcomp : lowerTotalList (envL ++ v :: envR) es = some ts)
    (hcount_total : countOccurrencesList v es = 1)
    (hnotdef : occursInDeferredListAux v false es = false)
    (hv_notin : envL.findIdx? (· == v) = none) :
    StrictSingleOccList (envL.length + 1) ts := by
  match es with
  | [] => simp [countOccurrencesList] at hcount_total
  | e :: rest =>
    rw [lowerTotalList.eq_2] at hcomp
    simp only [countOccurrencesList] at hcount_total
    simp only [occursInDeferredListAux, Bool.or_eq_false_iff] at hnotdef
    match he : lowerTotal (envL ++ v :: envR) e,
          hr : lowerTotalList (envL ++ v :: envR) rest with
    | some t', some ts' =>
      simp [he, hr] at hcomp; subst hcomp
      by_cases he0 : countOccurrences v e = 0
      · exact StrictSingleOccList.tail
          (freeOf_lowerTotal_of_countOcc_zero v envL envR e t' he he0)
          (strictSingleOccList_lowerTotal v envL envR rest ts' hr (by omega) hnotdef.2 hv_notin)
      · exact StrictSingleOccList.head
          (strictSingleOcc_lowerTotal v envL envR e t' he (by omega) hnotdef.1 hv_notin)
          (freeOfList_lowerTotal_of_countOcc_zero v envL envR rest ts' hr (by omega))
    | none, _ => simp [he] at hcomp
    | some _, none => simp [he, hr] at hcomp
termination_by sizeOf es

theorem strictSingleOcc_lowerTotalLet (v : VarId) (envL envR : List VarId)
    (binds : List (VarId × Expr × Bool)) (body : Expr) (t : Term)
    (hcomp : lowerTotalLet (envL ++ v :: envR) binds body = some t)
    (hcount : countOccurrencesLet v binds body = 1)
    (hnotdef : occursInDeferredLetAux v false binds body = false)
    (hv_notin : envL.findIdx? (· == v) = none) :
    StrictSingleOcc (envL.length + 1) t := by
  match binds with
  | [] =>
    rw [lowerTotalLet.eq_1] at hcomp
    simp only [countOccurrencesLet] at hcount
    simp only [occursInDeferredLetAux] at hnotdef
    exact strictSingleOcc_lowerTotal v envL envR body t hcomp hcount hnotdef hv_notin
  | (x, rhs, er) :: rest =>
    rw [lowerTotalLet.eq_2] at hcomp
    match hrhs : lowerTotal (envL ++ v :: envR) rhs,
          hrest : lowerTotalLet (x :: (envL ++ v :: envR)) rest body with
    | some rhs', some rest' =>
      simp [hrhs, hrest] at hcomp; subst hcomp
      simp only [countOccurrencesLet] at hcount
      simp only [occursInDeferredLetAux] at hnotdef
      by_cases hxv : (x == v) = true
      · -- x shadows v: occurrence must be in rhs
        rw [if_pos hxv] at hcount
        rw [if_pos hxv, Bool.or_false] at hnotdef
        exact StrictSingleOcc.apply_r
          (show freeOf (envL.length + 1) (.Lam 0 rest') = true by
            simp only [freeOf]
            show freeOf (envL.length + 1 + 1) rest' = true
            rw [show envL.length + 1 + 1 = (envL.length + 1) + 1 from by omega]
            exact freeOf_lowerTotalLet (x :: (envL ++ v :: envR)) (envL.length + 1)
              rest body rest' hrest (fun y hlu => by
              exfalso
              rw [show x :: (envL ++ v :: envR) = (x :: envL) ++ v :: envR from by simp] at hlu
              have hvy := envLookupT_at_pos_match (x :: envL) v envR y hlu
              have hxy : (x == y) = true := by
                rw [← (varid_beq_congr (varid_beq_symm hvy) x).symm]; exact hxv
              have hlookup0 : envLookupT ((x :: envL) ++ v :: envR) y = some 0 := by
                show envLookupT.go y ((x :: envL) ++ v :: envR) 0 = some 0
                rw [envLookupT_go_beq_congr y x _ 0 (varid_beq_symm hxy)]
                exact envLookupT_head x ((envL ++ v :: envR))
              rw [hlookup0] at hlu; simp at hlu))
          (strictSingleOcc_lowerTotal v envL envR rhs rhs' hrhs hcount hnotdef hv_notin)
      · -- x doesn't shadow v
        have hxvf : (x == v) = false := by
          cases h : (x == v) with | true => exact absurd h hxv | false => rfl
        rw [if_neg hxv] at hcount
        have hnotdef_rhs : occursInDeferredAux v false rhs = false := by
          have h := hnotdef; rw [if_neg hxv] at h
          exact (Bool.or_eq_false_iff.mp h).1
        have hnotdef_rest : occursInDeferredLetAux v false rest body = false := by
          have h := hnotdef; rw [if_neg hxv] at h
          exact (Bool.or_eq_false_iff.mp h).2
        have hv_notin' : (x :: envL).findIdx? (· == v) = none := by
          rw [List.findIdx?_eq_none_iff]
          rw [List.findIdx?_eq_none_iff] at hv_notin
          intro z hz; cases List.mem_cons.mp hz with
          | inl h => subst h; exact hxvf
          | inr h => exact hv_notin z h
        by_cases hrhs0 : countOccurrences v rhs = 0
        · -- Occurrence in rest/body: use let_body
          exact StrictSingleOcc.let_body
            (show StrictSingleOcc (envL.length + 1 + 1) rest' from by
              rw [show envL.length + 1 + 1 = (x :: envL).length + 1 from by simp]
              exact strictSingleOcc_lowerTotalLet v (x :: envL) envR rest body rest'
                (by rwa [show x :: (envL ++ v :: envR) = (x :: envL) ++ v :: envR from by simp]
                    at hrest)
                (by omega) hnotdef_rest hv_notin')
            (freeOf_lowerTotal_of_countOcc_zero v envL envR rhs rhs' hrhs hrhs0)
        · -- Occurrence in rhs: use apply_r
          exact .apply_r
            (show freeOf (envL.length + 1) (.Lam 0 rest') = true by
              simp only [freeOf]
              show freeOf (envL.length + 1 + 1) rest' = true
              rw [show envL.length + 1 + 1 = ((x :: envL).length) + 1 from by simp]
              exact freeOf_lowerTotalLet (x :: (envL ++ v :: envR)) ((x :: envL).length)
                rest body rest' hrest (by
                rw [show x :: (envL ++ v :: envR) = (x :: envL) ++ v :: envR from by simp]
                exact hno_use_of_countOcc_zero
                  (show countOccurrencesLet v rest body = 0 by omega)
                  (fun w hvw => countOccLet_beq_eq v w rest body hvw)))
            (strictSingleOcc_lowerTotal v envL envR rhs rhs' hrhs (by omega)
              hnotdef_rhs hv_notin)
    | none, _ => simp [hrhs] at hcomp
    | some _, none => simp [hrhs, hrest] at hcomp
termination_by sizeOf binds + sizeOf body
end

/-! ## Layer 3: Public theorems

These are the theorems consumed by `InlineSoundness.lean`. They compose
layers 1 and 2: first show `expandFix` preserves the MIR-level properties,
then apply the core bridge on the expanded (Fix-free) expression.
-/

theorem lowerTotal_freeOf_of_countOcc_zero
    (v : VarId) (env : List VarId) (e : Expr) (t : Term)
    (hcomp : lowerTotal (v :: env) (expandFix e) = some t)
    (hcount : countOccurrences v e = 0) :
    freeOf 1 t = true := by
  have hcount' := countOcc_expandFix_of_zero v e hcount
  exact freeOf_lowerTotal (v :: env) 0 (expandFix e) t hcomp (by
    intro y hlu
    have hvy := envLookupT_head_beq v y env hlu
    rw [← countOcc_beq_eq v y (expandFix e) hvy]; exact hcount')

theorem lowerTotal_strictSingleOcc_of_inlineGate
    (v : VarId) (env : List VarId) (body : Expr) (t : Term)
    (hcomp : lowerTotal (v :: env) (expandFix body) = some t)
    (hcount : countOccurrences v body = 1)
    (hnotdeferred : occursInDeferred v body = false) :
    StrictSingleOcc 1 t := by
  have hcount' := countOcc_expandFix_of_not_deferred v body hcount hnotdeferred
  have hnotdef' := occursInDeferred_expandFix_of_not_deferred v body hnotdeferred
  exact strictSingleOcc_lowerTotal v [] env (expandFix body) t
    (by simpa using hcomp) hcount' hnotdef' (by rfl)

private theorem foldl_add_shift {α : Type} (f : α → Nat) (l : List α) (a : Nat) :
    l.foldl (fun n x => n + f x) a = a + l.foldl (fun n x => n + f x) 0 := by
  induction l generalizing a with
  | nil => simp [List.foldl]
  | cons x rest ih =>
    simp only [List.foldl]
    rw [ih (a + f x), ih (0 + f x)]
    omega

private theorem foldl_eq_countOccLet (v : VarId)
    (rest : List (VarId × Expr × Bool)) (body : Expr)
    (hno_shadow : ∀ b ∈ rest, (b.1 == v) = false) :
    countOccurrencesLet v rest body = countOccurrences v body +
      rest.foldl (fun n (x : VarId × Expr × Bool) => n + countOccurrences v x.2.1) 0 := by
  induction rest with
  | nil => simp [countOccurrencesLet, List.foldl]
  | cons bind rest' ih =>
    obtain ⟨x, rhs, er⟩ := bind
    have hxv : (x == v) = false := hno_shadow ⟨x, rhs, er⟩ List.mem_cons_self
    have hno_shadow' : ∀ b ∈ rest', (b.1 == v) = false :=
      fun b hb => hno_shadow b (List.mem_cons_of_mem _ hb)
    simp only [countOccurrencesLet]
    rw [if_neg (by simp [hxv]), ih hno_shadow']
    simp only [List.foldl]
    rw [foldl_add_shift (fun x => countOccurrences v x.2.1) rest' (0 + countOccurrences v rhs)]
    omega

private theorem any_eq_occDefLetAux (v : VarId)
    (rest : List (VarId × Expr × Bool)) (body : Expr)
    (hno_shadow : ∀ b ∈ rest, (b.1 == v) = false) :
    occursInDeferredLetAux v false rest body = (occursInDeferred v body ||
      rest.any (fun (x : VarId × Expr × Bool) => occursInDeferred v x.2.1)) := by
  induction rest with
  | nil => simp [occursInDeferredLetAux, occursInDeferred, List.any]
  | cons bind rest' ih =>
    obtain ⟨x, rhs, er⟩ := bind
    have hxv : (x == v) = false := hno_shadow ⟨x, rhs, er⟩ List.mem_cons_self
    have hno_shadow' : ∀ b ∈ rest', (b.1 == v) = false :=
      fun b hb => hno_shadow b (List.mem_cons_of_mem _ hb)
    simp only [occursInDeferredLetAux]
    rw [if_neg (by simp [hxv])]
    rw [ih hno_shadow']
    simp only [List.any, occursInDeferred]
    cases occursInDeferredAux v false rhs <;> cases occursInDeferredAux v false body <;> simp

theorem distinctBinders_head_notin {v : VarId} {rhs : Expr} {er : Bool}
    {rest : List (VarId × Expr × Bool)}
    (hd : Moist.MIR.distinctBinders ((v, rhs, er) :: rest) = true) :
    ∀ b ∈ rest, (b.1 == v) = false := by
  simp only [Moist.MIR.distinctBinders, Bool.and_eq_true, List.all_eq_true] at hd
  intro ⟨x, r, e⟩ hmem
  have := hd.1 ⟨x, r, e⟩ hmem
  simp only [Bool.not_eq_true'] at this
  exact this

theorem lowerTotalLet_strictSingleOcc_of_inlineGate
    (v : VarId) (env : List VarId)
    (rest : List (VarId × Moist.MIR.Expr × Bool)) (body : Expr) (t : Term)
    (hcomp : lowerTotalLet (v :: env) (expandFixBinds rest) (expandFix body) = some t)
    (hocc : countOccurrences v body +
      rest.foldl (fun n (x : VarId × Expr × Bool) => n + countOccurrences v x.2.1) 0 = 1)
    (hnotdef : (Moist.MIR.occursInDeferred v body ||
      rest.any (fun (x : VarId × Expr × Bool) => Moist.MIR.occursInDeferred v x.2.1)) = false)
    (distinct_binders : Moist.MIR.distinctBinders ((v, rhs, er) :: rest) = true) :
    StrictSingleOcc 1 t := by
  have hno_shadow : ∀ b ∈ rest, (b.1 == v) = false := distinctBinders_head_notin distinct_binders
  have hcount : countOccurrencesLet v rest body = 1 := by
    rw [foldl_eq_countOccLet v rest body hno_shadow]; exact hocc
  have hnotdef' : occursInDeferredLetAux v false rest body = false := by
    rw [any_eq_occDefLetAux v rest body hno_shadow]; exact hnotdef
  have hcount_post := countOccLet_expandFixBinds_of_not_deferred v rest body hcount hnotdef'
  have hnotdef_post := occDefLetAux_expandFixBinds_of_not_deferred v rest body hnotdef'
  exact strictSingleOcc_lowerTotalLet v [] env (expandFixBinds rest) (expandFix body) t
    (by simpa using hcomp) hcount_post hnotdef_post (by rfl)

open Moist.Verified.InlineSoundness.StrictOcc (SingleOcc SingleOccList) in
theorem lowerTotalLet_singleOcc_of_occ_one
    (v : VarId) (env : List VarId)
    (rest : List (VarId × Moist.MIR.Expr × Bool)) (body : Expr) (t : Term)
    (hcomp : lowerTotalLet (v :: env) (expandFixBinds rest) (expandFix body) = some t)
    (hocc : countOccurrences v body +
      rest.foldl (fun n (x : VarId × Expr × Bool) => n + countOccurrences v x.2.1) 0 = 1)
    (distinct_binders : Moist.MIR.distinctBinders ((v, rhs, er) :: rest) = true) :
    SingleOcc 1 t := by
  by_cases hnotdef : (Moist.MIR.occursInDeferred v body ||
      rest.any (fun (x : VarId × Expr × Bool) => Moist.MIR.occursInDeferred v x.2.1)) = false
  · exact (lowerTotalLet_strictSingleOcc_of_inlineGate v env rest body t hcomp hocc hnotdef
      distinct_binders).toSingleOcc
  · have hno_shadow : ∀ b ∈ rest, (b.1 == v) = false := distinctBinders_head_notin distinct_binders
    have hcount : countOccurrencesLet v rest body = 1 := by
      rw [foldl_eq_countOccLet v rest body hno_shadow]; exact hocc
    have hcount_post : countOccurrencesLet v (expandFixBinds rest) (expandFix body) = 1 := by
      rw [countOccLet_expandFixBinds_general v rest body]; exact hcount
    exact singleOcc_lowerTotalLet v [] env (expandFixBinds rest) (expandFix body) t
      (by simpa using hcomp) hcount_post (by rfl)
where
  singleOcc_lowerTotal (v : VarId) (envL envR : List VarId)
      (e : Expr) (t : Term)
      (hcomp : lowerTotal (envL ++ v :: envR) e = some t)
      (hcount : countOccurrences v e = 1)
      (hv_notin : envL.findIdx? (· == v) = none) :
      Moist.Verified.InlineSoundness.StrictOcc.SingleOcc (envL.length + 1) t := by
    by_cases hnotdef : occursInDeferredAux v false e = false
    · exact (strictSingleOcc_lowerTotal v envL envR e t hcomp hcount hnotdef hv_notin).toSingleOcc
    · match e with
      | .Var _ => exfalso; simp [occursInDeferredAux] at hnotdef
      | .Lit _ | .Builtin _ | .Error => simp [countOccurrences] at hcount
      | .Fix _ _ => rw [lowerTotal.eq_12] at hcomp; exact absurd hcomp (by simp)
      | .Lam x body =>
        simp only [countOccurrences] at hcount
        by_cases hxv : (x == v) = true
        · simp [hxv] at hcount
        · rw [if_neg hxv] at hcount
          rw [lowerTotal.eq_5] at hcomp
          match hb : lowerTotal (x :: (envL ++ v :: envR)) body with
          | none => simp [hb] at hcomp
          | some body' =>
            simp [hb] at hcomp; subst hcomp
            have hv_notin' : (x :: envL).findIdx? (· == v) = none := by
              rw [List.findIdx?_eq_none_iff]
              rw [List.findIdx?_eq_none_iff] at hv_notin
              intro z hz; cases List.mem_cons.mp hz with
              | inl h => subst h; exact Bool.eq_false_iff.mpr hxv
              | inr h => exact hv_notin z h
            exact .lam (singleOcc_lowerTotal v (x :: envL) envR body body'
              (by rwa [show (x :: envL) ++ v :: envR = x :: (envL ++ v :: envR) from by simp])
              hcount hv_notin')
      | .Delay inner =>
        simp only [countOccurrences] at hcount
        rw [lowerTotal.eq_8] at hcomp
        match hi : lowerTotal (envL ++ v :: envR) inner with
        | none => simp [hi] at hcomp
        | some inner' =>
          simp [hi] at hcomp; subst hcomp
          exact .delay (singleOcc_lowerTotal v envL envR inner inner' hi hcount hv_notin)
      | .App f x =>
        rw [lowerTotal.eq_6] at hcomp
        simp only [countOccurrences] at hcount
        match hf : lowerTotal (envL ++ v :: envR) f, hx : lowerTotal (envL ++ v :: envR) x with
        | some f', some x' =>
          simp [hf, hx] at hcomp; subst hcomp
          by_cases hf0 : countOccurrences v f = 0
          · exact .apply_r
              (freeOf_lowerTotal_of_countOcc_zero v envL envR f f' hf hf0)
              (singleOcc_lowerTotal v envL envR x x' hx (by omega) hv_notin)
          · exact .apply_l
              (singleOcc_lowerTotal v envL envR f f' hf (by omega) hv_notin)
              (freeOf_lowerTotal_of_countOcc_zero v envL envR x x' hx (by omega))
        | none, _ => simp [hf] at hcomp
        | some _, none => simp [hf, hx] at hcomp
      | .Force inner =>
        rw [lowerTotal.eq_7] at hcomp
        simp only [countOccurrences] at hcount
        match hi : lowerTotal (envL ++ v :: envR) inner with
        | none => simp [hi] at hcomp
        | some inner' =>
          simp [hi] at hcomp; subst hcomp
          exact .force (singleOcc_lowerTotal v envL envR inner inner' hi hcount hv_notin)
      | .Constr tag args =>
        rw [lowerTotal.eq_9] at hcomp
        simp only [countOccurrences] at hcount
        match ha : lowerTotalList (envL ++ v :: envR) args with
        | none => simp [ha] at hcomp
        | some args' =>
          simp [ha] at hcomp; subst hcomp
          exact .constr
            (singleOccList_lowerTotal v envL envR args args' ha hcount hv_notin)
      | .Case scrut alts =>
        rw [lowerTotal.eq_10] at hcomp
        simp only [countOccurrences] at hcount
        match hs : lowerTotal (envL ++ v :: envR) scrut,
              ha : lowerTotalList (envL ++ v :: envR) alts with
        | some s', some a' =>
          simp [hs, ha] at hcomp; subst hcomp
          by_cases hs0 : countOccurrences v scrut = 0
          · exact .case_alt
              (freeOf_lowerTotal_of_countOcc_zero v envL envR scrut s' hs hs0)
              (singleOccList_lowerTotal v envL envR alts a' ha (by omega) hv_notin)
          · exact .case_scrut
              (singleOcc_lowerTotal v envL envR scrut s' hs (by omega) hv_notin)
              (freeOfList_lowerTotal_of_countOcc_zero v envL envR alts a' ha (by omega))
        | none, _ => simp [hs] at hcomp
        | some _, none => simp [hs, ha] at hcomp
      | .Let binds body =>
        rw [lowerTotal.eq_11] at hcomp
        simp only [countOccurrences] at hcount
        exact singleOcc_lowerTotalLet v envL envR binds body t hcomp hcount hv_notin
  termination_by sizeOf e
  singleOccList_lowerTotal (v : VarId) (envL envR : List VarId)
      (es : List Expr) (ts : List Term)
      (hcomp : lowerTotalList (envL ++ v :: envR) es = some ts)
      (hcount_total : countOccurrencesList v es = 1)
      (hv_notin : envL.findIdx? (· == v) = none) :
      Moist.Verified.InlineSoundness.StrictOcc.SingleOccList (envL.length + 1) ts := by
    match es with
    | [] => simp [countOccurrencesList] at hcount_total
    | e :: rest =>
      rw [lowerTotalList.eq_2] at hcomp
      simp only [countOccurrencesList] at hcount_total
      match he : lowerTotal (envL ++ v :: envR) e,
            hr : lowerTotalList (envL ++ v :: envR) rest with
      | some t', some ts' =>
        simp [he, hr] at hcomp; subst hcomp
        by_cases he0 : countOccurrences v e = 0
        · exact .tail
            (freeOf_lowerTotal_of_countOcc_zero v envL envR e t' he he0)
            (singleOccList_lowerTotal v envL envR rest ts' hr (by omega) hv_notin)
        · exact .head
            (singleOcc_lowerTotal v envL envR e t' he (by omega) hv_notin)
            (freeOfList_lowerTotal_of_countOcc_zero v envL envR rest ts' hr (by omega))
      | none, _ => simp [he] at hcomp
      | some _, none => simp [he, hr] at hcomp
  termination_by sizeOf es
  singleOcc_lowerTotalLet (v : VarId) (envL envR : List VarId)
      (binds : List (VarId × Expr × Bool)) (body : Expr) (t : Term)
      (hcomp : lowerTotalLet (envL ++ v :: envR) binds body = some t)
      (hcount : countOccurrencesLet v binds body = 1)
      (hv_notin : envL.findIdx? (· == v) = none) :
      Moist.Verified.InlineSoundness.StrictOcc.SingleOcc (envL.length + 1) t := by
    match binds with
    | [] =>
      rw [lowerTotalLet.eq_1] at hcomp
      simp only [countOccurrencesLet] at hcount
      exact singleOcc_lowerTotal v envL envR body t hcomp hcount hv_notin
    | (x, rhs_b, er_b) :: rest =>
      rw [lowerTotalLet.eq_2] at hcomp
      match hrhs : lowerTotal (envL ++ v :: envR) rhs_b,
            hrest : lowerTotalLet (x :: (envL ++ v :: envR)) rest body with
      | some rhs', some rest' =>
        simp [hrhs, hrest] at hcomp; subst hcomp
        simp only [countOccurrencesLet] at hcount
        by_cases hxv : (x == v) = true
        · rw [if_pos hxv] at hcount
          exact .apply_r
            (show freeOf (envL.length + 1) (.Lam 0 rest') = true by
              simp only [freeOf]
              show freeOf (envL.length + 1 + 1) rest' = true
              rw [show envL.length + 1 + 1 = (envL.length + 1) + 1 from by omega]
              exact freeOf_lowerTotalLet (x :: (envL ++ v :: envR)) (envL.length + 1)
                rest body rest' hrest (fun y hlu => by
                exfalso
                rw [show x :: (envL ++ v :: envR) = (x :: envL) ++ v :: envR from by simp] at hlu
                have hvy := envLookupT_at_pos_match (x :: envL) v envR y hlu
                have hxy : (x == y) = true := by
                  rw [← (varid_beq_congr (varid_beq_symm hvy) x).symm]; exact hxv
                have hlookup0 : envLookupT ((x :: envL) ++ v :: envR) y = some 0 := by
                  show envLookupT.go y ((x :: envL) ++ v :: envR) 0 = some 0
                  rw [envLookupT_go_beq_congr y x _ 0 (varid_beq_symm hxy)]
                  exact envLookupT_head x ((envL ++ v :: envR))
                rw [hlookup0] at hlu; simp at hlu))
            (singleOcc_lowerTotal v envL envR rhs_b rhs' hrhs hcount hv_notin)
        · rw [if_neg hxv] at hcount
          by_cases hr0 : countOccurrences v rhs_b = 0
          · have hv_notin' : (x :: envL).findIdx? (· == v) = none := by
              rw [List.findIdx?_eq_none_iff]
              rw [List.findIdx?_eq_none_iff] at hv_notin
              intro z hz; cases List.mem_cons.mp hz with
              | inl h => subst h; exact Bool.eq_false_iff.mpr hxv
              | inr h => exact hv_notin z h
            exact .let_body
              (singleOcc_lowerTotalLet v (x :: envL) envR rest body rest'
                (by rwa [show (x :: envL) ++ v :: envR = x :: (envL ++ v :: envR) from by simp])
                (by omega)
                hv_notin')
              (freeOf_lowerTotal_of_countOcc_zero v envL envR rhs_b rhs' hrhs hr0)
          · exact .apply_r
              (show freeOf (envL.length + 1) (.Lam 0 rest') = true by
                simp only [freeOf]
                show freeOf (envL.length + 1 + 1) rest' = true
                rw [show envL.length + 1 + 1 = ((x :: envL).length) + 1 from by simp]
                exact freeOf_lowerTotalLet (x :: (envL ++ v :: envR)) ((x :: envL).length)
                  rest body rest' hrest (by
                  rw [show x :: (envL ++ v :: envR) = (x :: envL) ++ v :: envR from by simp]
                  exact hno_use_of_countOcc_zero
                    (show countOccurrencesLet v rest body = 0 by omega)
                    (fun w hvw => countOccLet_beq_eq v w rest body hvw)))
              (singleOcc_lowerTotal v envL envR rhs_b rhs' hrhs (by omega) hv_notin)
      | none, _ => simp [hrhs] at hcomp
      | some _, none => simp [hrhs, hrest] at hcomp
  termination_by sizeOf binds + sizeOf body

end Moist.Verified.InlineSoundness.OccBridge
