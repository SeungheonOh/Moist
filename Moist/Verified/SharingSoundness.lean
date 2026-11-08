import Moist.Verified.SharedLets
import Moist.Verified.MIR.AlphaEqBool
import Moist.Verified.BuiltinStateSoundness
import Moist.Verified.InlineSoundness.Rename
import Moist.MIR.Optimize.Advanced.Sharing

variable [sv : Moist.CEK.SemVariant]

/-! # Soundness of closed-subterm sharing

`shareClosed` binds closed candidates at the top and replaces every
alpha-equal occurrence by the bound variable. With `R` the replacement list
and `vs` its binders, lowering the replaced body under `vs` gives a term that
is `Shared` with the original lowering (`replace_lower`): free variables move
past the new bindings, replaced occurrences become pinned variables. The new
binders have uids above every uid of the expression, so they neither capture
nor are captured. `SharedLets.shared_lets_ctxRefines` then gives contextual
refinement whenever every candidate is closed and halts.

Certificates: `shareClosed_refines`, `hoistBuiltinStates_refines`,
`poolConstants_refines`. -/

namespace Moist.Verified.Sharing

open Moist.MIR Moist.MIR.Advanced
open Moist.Plutus.Term (Term)
open Moist.Verified.MIR (lowerTotalExprList lowerTotalExprList_nil lowerTotalExprList_cons
  lowerTotalExpr_lam lowerTotalExpr_app lowerTotalExpr_force lowerTotalExpr_delay
  lowerTotalExpr_constr_of_list lowerTotalExpr_case_of_list)
open Moist.Verified.SharedLets

/-! ## Environment lookups -/

omit sv in
theorem envLookupT_go_append (x : VarId) :
    ∀ (bs rest : List VarId) (n : Nat),
      envLookupT.go x (bs ++ rest) n =
        match envLookupT.go x bs n with
        | some i => some i
        | none => envLookupT.go x rest (n + bs.length)
  | [], rest, n => by simp [envLookupT.go]
  | b :: bs, rest, n => by
    simp only [List.cons_append, envLookupT.go]
    split
    · rfl
    · rw [envLookupT_go_append x bs rest (n + 1)]
      simp only [List.length_cons, Nat.add_assoc, Nat.add_comm 1]

omit sv in
theorem envLookupT_append (bs rest : List VarId) (x : VarId) :
    envLookupT (bs ++ rest) x =
      match envLookupT bs x with
      | some i => some i
      | none => (envLookupT rest x).map (· + bs.length) := by
  unfold envLookupT
  rw [envLookupT_go_append, Nat.zero_add, show bs.length = 0 + bs.length by omega,
    envLookupT.go_shift]
  simp only [Nat.zero_add]

omit sv in
theorem envLookupT_none_of_ne : ∀ (bs : List VarId) (x : VarId),
    (∀ b ∈ bs, (b == x) = false) → envLookupT bs x = none
  | [], _, _ => rfl
  | b :: bs, x, h => by
    rw [envLookupT_cons_neq b x bs (h b (.head _)),
      envLookupT_none_of_ne bs x (fun b' hb' => h b' (.tail _ hb'))]
    rfl

omit sv in
theorem envLookupT_go_getElem : ∀ (L : List VarId) (i n : Nat) (hi : i < L.length),
    (∀ i' (h' : i' < i), (L[i']'(by omega) == L[i]) = false) →
      envLookupT.go L[i] L n = some (n + i)
  | [], _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | b :: L, 0, n, _, _ => by
    have : (b == b) = true := by rw [VarId.beq_true_iff]; exact ⟨rfl, rfl⟩
    simp [envLookupT.go, this]
  | b :: L, i + 1, n, hi, h => by
    have hne := h 0 (by omega)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hne
    simp only [List.getElem_cons_succ, envLookupT.go, hne]
    rw [envLookupT_go_getElem L i (n + 1) (by simp at hi; omega) (fun i' h' => by
      have := h (i' + 1) (by omega)
      simpa using this)]
    simp only [Bool.false_eq_true, if_false]
    congr 1; omega

omit sv in
theorem beq_false_of_uid_ne {a b : VarId} (h : a.uid ≠ b.uid) : (a == b) = false :=
  (VarId.beq_false_iff a b).mpr (.inr h)

/-! ## Closed expressions -/

/-- No free variables. -/
def Closed (e : Expr) : Prop := ∀ x, (freeVars e).contains x = false

omit sv in
theorem lowerTotalExpr_closed {e : Expr} (hc : Closed e) (env : List VarId) :
    lowerTotalExpr env e = lowerTotalExpr [] e := by
  unfold lowerTotalExpr
  have hfix : ∀ x, (freeVars (expandFix e)).contains x = false :=
    fun x => expandFix_freeVars_not_contains e x (hc x)
  obtain ⟨l, rfl⟩ : ∃ l, env = l.reverse := ⟨env.reverse, by simp⟩
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.reverse_cons, lowerTotal_append_unused l.reverse x _ (hfix x), ih]

omit sv in
theorem closed_of_isEmpty {e : Expr} (h : (freeVars e).data.isEmpty = true) : Closed e := by
  intro x
  unfold VarSet.contains
  rw [Array.isEmpty_iff] at h
  rw [h]
  rfl

omit sv in
theorem alphaEq_lam_false {c : Expr} (hc : ∀ x b, c ≠ .Lam x b) (x : VarId) (b : Expr) :
    alphaEq c (.Lam x b) = false := by
  cases c with
  | Lam y b' => exact absurd rfl (hc _ _)
  | _ => unfold alphaEq alphaEqAux; rfl

omit sv in
theorem fresh_left {a b c : Nat} (h : max a b < c) : a < c := by omega
omit sv in
theorem fresh_right {a b c : Nat} (h : max a b < c) : b < c := by omega

/-! ## Replacement setup -/

/-- The replacement list `R` with the lowerings `ts` of its candidates. -/
structure Setup (R : List (Expr × VarId)) (ts : List Term) : Prop where
  length : ts.length = R.length
  lower : ∀ j (h : j < R.length), lowerTotalExpr [] R[j].1 = some (ts[j]'(by omega))
  closed : ∀ entry ∈ R, Closed entry.1
  distinct : ∀ a b (ha : a < R.length) (hb : b < R.length), (R[a].2 == R[b].2) = true → a = b

/-- The new binders as they appear in the lowering environment, innermost
    first. -/
def binders (R : List (Expr × VarId)) : List VarId := (R.map Prod.snd).reverse

/-- A bound on the uids of the new binders. -/
def uidBound : List (Expr × VarId) → Nat
  | [] => 0
  | entry :: rest => entry.2.uid + uidBound rest

omit sv in
theorem le_uidBound : ∀ {R : List (Expr × VarId)} {entry : Expr × VarId}, entry ∈ R →
    entry.2.uid ≤ uidBound R
  | _ :: _, _, .head _ => by simp only [uidBound]; omega
  | _ :: _, _, .tail _ h => by have := le_uidBound h; simp only [uidBound]; omega

section
variable {R : List (Expr × VarId)} {ts : List Term}

omit sv in
theorem binders_length : (binders R).length = R.length := by simp [binders]

omit sv in
theorem binders_lookup (S : Setup R ts) {j : Nat} (hj : j < R.length) :
    envLookupT (binders R) R[j].2 = some (R.length - 1 - j) := by
  have hi : R.length - 1 - j < (binders R).length := by rw [binders_length]; omega
  have hget : (binders R)[R.length - 1 - j]'hi = R[j].2 := by
    simp only [binders, List.getElem_reverse, List.getElem_map, List.length_map]
    have : R.length - 1 - (R.length - 1 - j) = j := by omega
    simp only [this]
  rw [← hget]
  unfold envLookupT
  rw [envLookupT_go_getElem (binders R) _ 0 hi (fun i' h' => ?_)]
  · simp
  · cases hb : ((binders R)[i']'(by omega) == (binders R)[R.length - 1 - j]'hi) with
    | false => rfl
    | true =>
      exfalso
      rw [hget] at hb
      have hget' : (binders R)[i']'(by omega) = R[R.length - 1 - i'].2 := by
        simp only [binders, List.getElem_reverse, List.getElem_map, List.length_map]
      rw [hget'] at hb
      have := S.distinct _ _ (by omega) hj hb
      omega

omit sv in
theorem binders_lookup_none {x : VarId} (hx : ∀ entry ∈ R, (entry.2 == x) = false) :
    envLookupT (binders R) x = none := by
  apply envLookupT_none_of_ne
  intro b hb
  simp only [binders, List.mem_reverse, List.mem_map] at hb
  obtain ⟨entry, he, rfl⟩ := hb
  exact hx entry he

theorem pin_case (S : Setup R ts) (env bs : List VarId) (e : Expr) (t : Term) (c : Expr)
    (v : VarId) (hfind : R.find? (fun entry => alphaEq entry.1 e) = some (c, v))
    (hbs : ∀ b ∈ bs, ∀ entry ∈ R, (b == entry.2) = false)
    (h : lowerTotalExpr (bs ++ env) e = some t) :
    ∃ u, lowerTotalExpr (bs ++ binders R ++ env) (replaceMatches R e) = some u ∧
      Shared ts.length (BindingPins ts) bs.length t u := by
  have hmem := List.mem_of_find?_eq_some hfind
  have halpha : alphaEq c e = true := by simpa using List.find?_some hfind
  obtain ⟨j, hj, hRj⟩ := List.mem_iff_getElem.mp hmem
  have hrep : replaceMatches R e = .Var v := by rw [replaceMatches.eq_def, hfind]
  rw [← Moist.Verified.MIR.alphaEq_lowerTotalExpr_eq halpha, lowerTotalExpr_closed (S.closed _ hmem)] at h
  have hlow := S.lower j hj
  rw [hRj, h] at hlow
  cases hlow
  have hbv : envLookupT bs v = none :=
    envLookupT_none_of_ne bs v (fun b hb => hbs b hb (c, v) hmem)
  have hv : envLookupT (binders R) v = some (R.length - 1 - j) := by
    have := binders_lookup S hj
    rwa [hRj] at this
  refine ⟨.Var (ts.length - j + bs.length), ?_, Shared.pin ⟨j, by rw [S.length]; exact hj, rfl, rfl⟩⟩
  rw [hrep, Moist.Verified.InlineSoundness.Rename.lowerTotalExpr_var, List.append_assoc,
    envLookupT_append, hbv]
  simp only [envLookupT_append, hv, Option.map_some]
  congr 2
  have := S.length
  omega

omit sv in
theorem fixLamWrap_shared {K : Nat} {P : Term → Nat → Prop} {d : Nat} {t u : Term}
    (h : Shared K P (d + 1 + 1 + 1) t u) :
    Shared K P d (fixLamWrapUplc t) (fixLamWrapUplc u) := by
  unfold fixLamWrapUplc
  exact .apply (.lam (.apply (Shared.var_le (by omega)) (Shared.var_le (by omega))))
    (.lam (.apply (.lam (.lam h))
      (.lam (.apply (.apply (Shared.var_le (by omega)) (Shared.var_le (by omega)))
        (Shared.var_le (by omega))))))

omit sv in
theorem lowerTotalExpr_let_eq (env : List VarId) (binds : List (VarId × Expr × Bool))
    (body : Expr) :
    lowerTotalExpr env (.Let binds body) = lowerTotalLet env (expandFixBinds binds) (expandFix body) := by
  simp only [lowerTotalExpr, expandFix, lowerTotal]

omit sv in
theorem fresh_binder {x : VarId} {bound : Nat} (hx : x.uid ≤ bound)
    (hfresh : ∀ entry ∈ R, bound < entry.2.uid) : ∀ entry ∈ R, (x == entry.2) = false :=
  fun entry he => beq_false_of_uid_ne (by have := hfresh entry he; omega)

omit sv in
theorem cons_binders {x : VarId} {bs : List VarId} (hx : ∀ entry ∈ R, (x == entry.2) = false)
    (hbs : ∀ b ∈ bs, ∀ entry ∈ R, (b == entry.2) = false) :
    ∀ b ∈ x :: bs, ∀ entry ∈ R, (b == entry.2) = false := by
  intro b hb
  cases hb with
  | head => exact hx
  | tail _ hb => exact hbs b hb

mutual
  theorem replace_lower (S : Setup R ts) (env : List VarId) :
      ∀ (e : Expr) (bs : List VarId) (t : Term),
        (∀ b ∈ bs, ∀ entry ∈ R, (b == entry.2) = false) →
        (∀ entry ∈ R, maxUidExpr e < entry.2.uid) →
        lowerTotalExpr (bs ++ env) e = some t →
        ∃ u, lowerTotalExpr (bs ++ binders R ++ env) (replaceMatches R e) = some u ∧
          Shared ts.length (BindingPins ts) bs.length t u
    | e, bs, t, hbs, hfresh, h => by
      cases hfind : R.find? (fun entry => alphaEq entry.1 e) with
      | some entry => exact pin_case S env bs e t entry.1 entry.2 hfind hbs h
      | none =>
      match e, hfind, hfresh, h with
      | .Var y, hfind, hfresh, h =>
        have hrep : replaceMatches R (.Var y) = .Var y := by rw [replaceMatches.eq_def, hfind]
        rw [hrep]
        rw [Moist.Verified.InlineSoundness.Rename.lowerTotalExpr_var] at h ⊢
        have hy : ∀ entry ∈ R, (entry.2 == y) = false := fun entry he =>
          beq_false_of_uid_ne (by have := hfresh entry he; simp only [maxUidExpr] at this; omega)
        rw [envLookupT_append] at h
        rw [List.append_assoc, envLookupT_append, envLookupT_append (binders R) env,
          binders_lookup_none hy]
        cases hb : envLookupT bs y with
        | some i =>
          simp only [hb, Option.map_some, Option.some.injEq] at h ⊢
          subst h
          have := envLookupT_bound bs y i hb
          exact ⟨_, rfl, Shared.var_le (by omega)⟩
        | none =>
          cases he : envLookupT env y with
          | none => simp [hb, he] at h
          | some i =>
            simp only [hb, he, Option.map_some, Option.some.injEq] at h ⊢
            subst h
            refine ⟨_, rfl, ?_⟩
            have hv := Shared.var (K := ts.length) (P := BindingPins ts) bs.length
              (i + bs.length + 1)
            rw [show shareShift bs.length ts.length (i + bs.length + 1) =
                i + (binders R).length + bs.length + 1 by
              rw [binders_length, ← S.length]; unfold shareShift; rw [if_neg (by omega)]
              omega] at hv
            exact hv
      | .Lit (c, ty), hfind, _, h =>
        have hrep : replaceMatches R (.Lit (c, ty)) = .Lit (c, ty) := by
          rw [replaceMatches.eq_def, hfind]
        rw [hrep]
        simp only [lowerTotalExpr, expandFix, lowerTotal, Option.some.injEq] at h ⊢
        subst h
        exact ⟨_, rfl, .constant _ _⟩
      | .Builtin b, hfind, _, h =>
        have hrep : replaceMatches R (.Builtin b) = .Builtin b := by
          rw [replaceMatches.eq_def, hfind]
        rw [hrep]
        simp only [lowerTotalExpr, expandFix, lowerTotal, Option.some.injEq] at h ⊢
        subst h
        exact ⟨_, rfl, .builtin _ _⟩
      | .Error, hfind, _, h =>
        have hrep : replaceMatches R .Error = .Error := by rw [replaceMatches.eq_def, hfind]
        rw [hrep]
        simp only [lowerTotalExpr, expandFix, lowerTotal, Option.some.injEq] at h ⊢
        subst h
        exact ⟨_, rfl, .error _⟩
      | .Lam x body, hfind, hfresh, h =>
        have hrep : replaceMatches R (.Lam x body) = .Lam x (replaceMatches R body) := by
          rw [replaceMatches.eq_def, hfind]
        rw [hrep, lowerTotalExpr_lam]
        rw [lowerTotalExpr_lam] at h
        cases hb : lowerTotalExpr (x :: (bs ++ env)) body with
        | none => simp [hb] at h
        | some tb =>
          simp only [hb, Option.map_some, Option.some.injEq] at h
          subst h
          have hfresh' : ∀ entry ∈ R, max x.uid (maxUidExpr body) < entry.2.uid := by
            intro entry he; have := hfresh entry he; simp only [maxUidExpr] at this; exact this
          obtain ⟨u, hu, hrel⟩ := replace_lower S env body (x :: bs) tb
            (cons_binders (fresh_binder (Nat.le_max_left _ _) hfresh') hbs)
            (fun entry he => fresh_right (hfresh' entry he)) hb
          refine ⟨.Lam 0 u, ?_, .lam hrel⟩
          rw [show x :: (bs ++ binders R ++ env) = (x :: bs) ++ binders R ++ env from rfl, hu]
          rfl
      | .Fix f body, hfind, hfresh, h =>
        match body, hfind, hfresh, h with
        | .Lam x inner, hfind, hfresh, h =>
          have hrep : replaceMatches R (.Fix f (.Lam x inner)) =
              .Fix f (.Lam x (replaceMatches R inner)) := by
            rw [replaceMatches.eq_def, hfind]
          rw [hrep]
          let s : VarId := ⟨maxUidExpr (expandFix inner) +
            maxUidExpr (expandFix (replaceMatches R inner)) + uidBound R + 1, .gen, "s"⟩
          have hs₁ : (freeVars (expandFix inner)).contains s = false :=
            maxUidExpr_fresh _ s (by simp only [s]; omega)
          have hs₂ : (freeVars (expandFix (replaceMatches R inner))).contains s = false :=
            maxUidExpr_fresh _ s (by simp only [s]; omega)
          rw [lowerTotalExpr_fix_lam_with_fresh _ f x inner s hs₁] at h
          rw [lowerTotalExpr_fix_lam_with_fresh _ f x _ s hs₂]
          cases hb : lowerTotal (x :: f :: s :: (bs ++ env)) (expandFix inner) with
          | none => simp [hb] at h
          | some tb =>
            simp only [hb, Option.map_some, Option.some.injEq] at h
            subst h
            have hfresh' : ∀ entry ∈ R, max f.uid (max x.uid (maxUidExpr inner)) < entry.2.uid := by
              intro entry he; have := hfresh entry he; simp only [maxUidExpr] at this; exact this
            have hs : ∀ entry ∈ R, (s == entry.2) = false := fun entry he =>
              beq_false_of_uid_ne (by have := le_uidBound he; simp only [s]; omega)
            obtain ⟨u, hu, hrel⟩ := replace_lower S env inner (x :: f :: s :: bs) tb
              (cons_binders (fresh_binder (by omega) hfresh')
                (cons_binders (fresh_binder (Nat.le_max_left _ _) hfresh')
                  (cons_binders hs hbs)))
              (fun entry he => by have := hfresh' entry he; omega) hb
            refine ⟨fixLamWrapUplc u, ?_, fixLamWrap_shared hrel⟩
            have hu' : lowerTotal (x :: f :: s :: (bs ++ binders R ++ env))
                (expandFix (replaceMatches R inner)) = some u := hu
            rw [hu']
            rfl
        | .Var _, _, _, h | .Lit _, _, _, h | .Builtin _, _, _, h | .Error, _, _, h
        | .Fix _ _, _, _, h | .App _ _, _, _, h | .Force _, _, _, h | .Delay _, _, _, h
        | .Constr _ _, _, _, h | .Case _ _, _, _, h | .Let _ _, _, _, h =>
          rw [Moist.Verified.MIR.lowerTotalExpr_fix_nonlam_none _ _ _
            (fun _ _ hne => Expr.noConfusion hne)] at h
          cases h
      | .App fn arg, hfind, hfresh, h =>
        have hrep : replaceMatches R (.App fn arg) =
            .App (replaceMatches R fn) (replaceMatches R arg) := by
          rw [replaceMatches.eq_def, hfind]
        rw [hrep, lowerTotalExpr_app]
        rw [lowerTotalExpr_app] at h
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨tf, hf, ta, ha, rfl⟩ := h
        have hfresh' : ∀ entry ∈ R, max (maxUidExpr fn) (maxUidExpr arg) < entry.2.uid := by
          intro entry he; have := hfresh entry he; simp only [maxUidExpr] at this; exact this
        obtain ⟨uf, huf, hrelf⟩ := replace_lower S env fn bs tf hbs
          (fun entry he => fresh_left (hfresh' entry he)) hf
        obtain ⟨ua, hua, hrela⟩ := replace_lower S env arg bs ta hbs
          (fun entry he => fresh_right (hfresh' entry he)) ha
        refine ⟨.Apply uf ua, ?_, .apply hrelf hrela⟩
        rw [huf, hua]; rfl
      | .Force inner, hfind, hfresh, h =>
        have hrep : replaceMatches R (.Force inner) = .Force (replaceMatches R inner) := by
          rw [replaceMatches.eq_def, hfind]
        rw [hrep, lowerTotalExpr_force]
        rw [lowerTotalExpr_force] at h
        cases hb : lowerTotalExpr (bs ++ env) inner with
        | none => simp [hb] at h
        | some tb =>
          simp only [hb, Option.map_some, Option.some.injEq] at h
          subst h
          obtain ⟨u, hu, hrel⟩ := replace_lower S env inner bs tb hbs
            (fun entry he => by have := hfresh entry he; simp only [maxUidExpr] at this; exact this) hb
          exact ⟨.Force u, by rw [hu]; rfl, .force hrel⟩
      | .Delay inner, hfind, hfresh, h =>
        have hrep : replaceMatches R (.Delay inner) = .Delay (replaceMatches R inner) := by
          rw [replaceMatches.eq_def, hfind]
        rw [hrep, lowerTotalExpr_delay]
        rw [lowerTotalExpr_delay] at h
        cases hb : lowerTotalExpr (bs ++ env) inner with
        | none => simp [hb] at h
        | some tb =>
          simp only [hb, Option.map_some, Option.some.injEq] at h
          subst h
          obtain ⟨u, hu, hrel⟩ := replace_lower S env inner bs tb hbs
            (fun entry he => by have := hfresh entry he; simp only [maxUidExpr] at this; exact this) hb
          exact ⟨.Delay u, by rw [hu]; rfl, .delay hrel⟩
      | .Constr tag fields, hfind, hfresh, h =>
        have hrep : replaceMatches R (.Constr tag fields) =
            .Constr tag (replaceMatchesList R fields) := by
          rw [replaceMatches.eq_def, hfind]
        rw [hrep, lowerTotalExpr_constr_of_list]
        rw [lowerTotalExpr_constr_of_list] at h
        cases hb : lowerTotalExprList (bs ++ env) fields with
        | none => simp [hb] at h
        | some tb =>
          simp only [hb, Option.map_some, Option.some.injEq] at h
          subst h
          obtain ⟨u, hu, hrel⟩ := replace_lowerList S env fields bs tb hbs
            (fun entry he => by have := hfresh entry he; simp only [maxUidExpr] at this; exact this) hb
          exact ⟨.Constr tag u, by rw [hu]; rfl, .constr hrel⟩
      | .Case scrut alts, hfind, hfresh, h =>
        have hrep : replaceMatches R (.Case scrut alts) =
            .Case (replaceMatches R scrut) (replaceMatchesList R alts) := by
          rw [replaceMatches.eq_def, hfind]
        rw [hrep, lowerTotalExpr_case_of_list]
        rw [lowerTotalExpr_case_of_list] at h
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨ts', hs, tas, ha, rfl⟩ := h
        have hfresh' : ∀ entry ∈ R, max (maxUidExpr scrut) (maxUidExprList alts) < entry.2.uid := by
          intro entry he; have := hfresh entry he; simp only [maxUidExpr] at this; exact this
        obtain ⟨us, hus, hrels⟩ := replace_lower S env scrut bs ts' hbs
          (fun entry he => fresh_left (hfresh' entry he)) hs
        obtain ⟨ua, hua, hrela⟩ := replace_lowerList S env alts bs tas hbs
          (fun entry he => fresh_right (hfresh' entry he)) ha
        refine ⟨.Case us ua, ?_, .case hrels hrela⟩
        rw [hus, hua]; rfl
      | .Let binds body, hfind, hfresh, h =>
        have hrep : replaceMatches R (.Let binds body) =
            .Let (replaceMatchesBinds R binds) (replaceMatches R body) := by
          rw [replaceMatches.eq_def, hfind]
        rw [hrep, lowerTotalExpr_let_eq]
        rw [lowerTotalExpr_let_eq] at h
        exact replace_lowerLet S env binds body bs t hbs
          (fun entry he => by have := hfresh entry he; simp only [maxUidExpr] at this; exact this) h
  termination_by e => sizeOf e

  theorem replace_lowerList (S : Setup R ts) (env : List VarId) :
      ∀ (es : List Expr) (bs : List VarId) (ts' : List Term),
        (∀ b ∈ bs, ∀ entry ∈ R, (b == entry.2) = false) →
        (∀ entry ∈ R, maxUidExprList es < entry.2.uid) →
        lowerTotalExprList (bs ++ env) es = some ts' →
        ∃ us, lowerTotalExprList (bs ++ binders R ++ env) (replaceMatchesList R es) = some us ∧
          SharedList ts.length (BindingPins ts) bs.length ts' us
    | [], bs, ts', _, _, h => by
      rw [lowerTotalExprList_nil] at h
      cases h
      exact ⟨[], by simp only [replaceMatchesList]; exact lowerTotalExprList_nil _, .nil _⟩
    | e :: rest, bs, ts', hbs, hfresh, h => by
      rw [lowerTotalExprList_cons] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨t₁, h₁, ts₁, h₂, rfl⟩ := h
      have hfresh' : ∀ entry ∈ R, max (maxUidExpr e) (maxUidExprList rest) < entry.2.uid := by
        intro entry he; have := hfresh entry he; simp only [maxUidExprList] at this; exact this
      obtain ⟨u, hu, hrel⟩ := replace_lower S env e bs t₁ hbs
        (fun entry he => fresh_left (hfresh' entry he)) h₁
      obtain ⟨us, hus, hrels⟩ := replace_lowerList S env rest bs ts₁ hbs
        (fun entry he => fresh_right (hfresh' entry he)) h₂
      refine ⟨u :: us, ?_, .cons hrel hrels⟩
      simp only [replaceMatchesList]
      rw [lowerTotalExprList_cons, hu, hus]; rfl
  termination_by es => sizeOf es

  theorem replace_lowerLet (S : Setup R ts) (env : List VarId) :
      ∀ (binds : List (VarId × Expr × Bool)) (body : Expr) (bs : List VarId) (t : Term),
        (∀ b ∈ bs, ∀ entry ∈ R, (b == entry.2) = false) →
        (∀ entry ∈ R, max (maxUidExprBinds binds) (maxUidExpr body) < entry.2.uid) →
        lowerTotalLet (bs ++ env) (expandFixBinds binds) (expandFix body) = some t →
        ∃ u, lowerTotalLet (bs ++ binders R ++ env) (expandFixBinds (replaceMatchesBinds R binds))
            (expandFix (replaceMatches R body)) = some u ∧
          Shared ts.length (BindingPins ts) bs.length t u
    | [], body, bs, t, hbs, hfresh, h => by
      simp only [expandFixBinds, replaceMatchesBinds, lowerTotalLet] at h ⊢
      exact replace_lower S env body bs t hbs (fun entry he => fresh_right (hfresh entry he)) h
    | (x, rhs, er) :: rest, body, bs, t, hbs, hfresh, h => by
      simp only [expandFixBinds, replaceMatchesBinds, lowerTotalLet, Option.bind_eq_bind,
        Option.bind_eq_some_iff, Option.some.injEq] at h ⊢
      obtain ⟨r, hr, b, hb, rfl⟩ := h
      have hfresh' : ∀ entry ∈ R,
          max (max x.uid (max (maxUidExpr rhs) (maxUidExprBinds rest))) (maxUidExpr body) <
            entry.2.uid := by
        intro entry he; have := hfresh entry he; simp only [maxUidExprBinds] at this; exact this
      obtain ⟨ur, hur, hrelr⟩ := replace_lower S env rhs bs r hbs
        (fun entry he => by have := hfresh' entry he; omega) hr
      obtain ⟨ub, hub, hrelb⟩ := replace_lowerLet S env rest body (x :: bs) b
        (cons_binders (fresh_binder (bound := max (max x.uid (max (maxUidExpr rhs)
          (maxUidExprBinds rest))) (maxUidExpr body)) (by omega) hfresh') hbs)
        (fun entry he => by have := hfresh' entry he; omega) hb
      exact ⟨_, ⟨ur, hur, ub, hub, rfl⟩, .apply (.lam hrelb) hrelr⟩
  termination_by binds body => sizeOf binds + sizeOf body
end

end

/-! ## The bindings -/

omit sv in
theorem lowerTotalExpr_shared_lets (R : List (Expr × VarId)) (body : Expr)
    (hclosed : ∀ entry ∈ R, Closed entry.1)
    (hlow : ∀ entry ∈ R, (lowerTotalExpr [] entry.1).isSome) :
    ∀ env : List VarId,
      lowerTotalExpr env (.Let (R.map fun (rhs, binder) => (binder, rhs, false)) body) =
        (lowerTotalExpr (binders R ++ env) body).map
          (mkLets (R.map fun entry => (lowerTotalExpr [] entry.1).getD .Error)) := by
  induction R with
  | nil =>
    intro env
    simp only [List.map_nil, Moist.Verified.InlineSoundness.Rename.lowerTotalExpr_let_nil,
      binders, List.reverse_nil, List.nil_append]
    cases lowerTotalExpr env body <;> rfl
  | cons entry rest ih =>
    intro env
    obtain ⟨c, v⟩ := entry
    have hc := hclosed (c, v) (.head _)
    obtain ⟨tc, htc⟩ := Option.isSome_iff_exists.mp (hlow (c, v) (.head _))
    simp only [List.map_cons, Moist.Verified.InlineSoundness.Rename.lowerTotalExpr_let_cons,
      lowerTotalExpr_closed hc env, htc, Option.bind_eq_bind, Option.bind_some]
    rw [ih (fun e he => hclosed e (.tail _ he)) (fun e he => hlow e (.tail _ he)) (v :: env)]
    have hb : binders ((c, v) :: rest) ++ env = binders rest ++ v :: env := by
      simp [binders]
    rw [hb]
    cases lowerTotalExpr (binders rest ++ v :: env) body <;> simp [mkLets]

/-- Binding closed, halting candidates and replacing their alpha-equal
    occurrences by fresh variables is a refinement. -/
theorem share_refines (R : List (Expr × VarId)) (e : Expr)
    (hclosed : ∀ entry ∈ R, Closed entry.1)
    (hdistinct : ∀ a b (ha : a < R.length) (hb : b < R.length),
      (R[a].2 == R[b].2) = true → a = b)
    (hfresh : ∀ entry ∈ R, maxUidExpr e < entry.2.uid)
    (hhalts : ∀ entry ∈ R, ∀ t, lowerTotalExpr [] entry.1 = some t → Halts t)
    (hlower : ∀ env t, lowerTotalExpr env e = some t →
      ∀ entry ∈ R, (lowerTotalExpr [] entry.1).isSome) :
    Moist.Verified.MIR.MIRCtxRefines e
      (.Let (R.map fun (rhs, binder) => (binder, rhs, false)) (replaceMatches R e)) := by
  intro env
  cases h : lowerTotalExpr env e with
  | none => exact ⟨by simp, trivial⟩
  | some t =>
    have hlow := hlower env t h
    let ts := R.map fun entry => (lowerTotalExpr [] entry.1).getD .Error
    have hget : ∀ entry ∈ R, lowerTotalExpr [] entry.1 =
        some ((lowerTotalExpr [] entry.1).getD .Error) := fun entry he =>
      (Option.getD_of_ne_none (by
        intro hn; have := hlow entry he; rw [hn] at this; cases this) _).symm
    have S : Setup R ts := {
      length := by simp [ts]
      lower := fun j hj => by
        simp only [ts, List.getElem_map]
        exact hget _ (List.getElem_mem hj)
      closed := hclosed
      distinct := hdistinct }
    obtain ⟨u, hu, hrel⟩ := replace_lower S env e [] t (by simp) hfresh h
    have hts : ∀ c ∈ ts, Moist.Verified.closedAt 0 c = true ∧ Halts c := by
      intro c hc
      simp only [ts, List.mem_map] at hc
      obtain ⟨entry, he, rfl⟩ := hc
      have := hget entry he
      exact ⟨Moist.Verified.MIR.lowerTotalExpr_closedAt this, hhalts entry he _ this⟩
    have htarget : lowerTotalExpr env
        (.Let (R.map fun (rhs, binder) => (binder, rhs, false)) (replaceMatches R e)) =
        some (mkLets ts u) := by
      rw [lowerTotalExpr_shared_lets R _ hclosed hlow env]
      have hu' : lowerTotalExpr (binders R ++ env) (replaceMatches R e) = some u := hu
      rw [hu']
      rfl
    rw [htarget]
    exact ⟨fun _ => rfl, shared_lets_ctxRefines hts (Moist.Verified.MIR.lowerTotalExpr_closedAt h) hrel⟩

/-! ## Candidates -/

section Collect
variable (predicate : Expr → Bool)

/-- What `collectMatches` returns for a rejected expression. -/
def collectChildren : Expr → List Expr
  | .Lam _ body | .Fix _ body | .Force body | .Delay body => collectMatches predicate body
  | .App function argument =>
    collectMatches predicate function ++ collectMatches predicate argument
  | .Constr _ fields => collectMatchesList predicate fields
  | .Case scrutinee alternatives =>
    collectMatches predicate scrutinee ++ collectMatchesList predicate alternatives
  | .Let bindings body => collectMatchesBinds predicate bindings ++ collectMatches predicate body
  | _ => []

omit sv in
theorem collect_cases {e c : Expr} (hc : c ∈ collectMatches predicate e) :
    (c = e ∧ predicate e = true) ∨ c ∈ collectChildren predicate e := by
  rw [collectMatches.eq_def] at hc
  by_cases hp : predicate e = true
  · rw [if_pos hp] at hc
    exact .inl ⟨List.mem_singleton.mp hc, hp⟩
  · rw [if_neg hp] at hc
    right
    cases e <;> exact hc

mutual
  theorem collectMatches_pred :
      ∀ (e : Expr), ∀ c ∈ collectMatches predicate e, predicate c = true
    | e, c, hc => by
      rcases collect_cases predicate hc with ⟨rfl, hp⟩ | hc'
      · exact hp
      clear hc
      match he : e, hc' with
      | .Lam _ body, hc | .Fix _ body, hc | .Force body, hc | .Delay body, hc =>
        exact collectMatches_pred body c hc
      | .App f a, hc =>
        rcases List.mem_append.mp hc with hc | hc
        · exact collectMatches_pred f c hc
        · exact collectMatches_pred a c hc
      | .Constr _ fields, hc => exact collectMatchesList_pred fields c hc
      | .Case s alts, hc =>
        rcases List.mem_append.mp hc with hc | hc
        · exact collectMatches_pred s c hc
        · exact collectMatchesList_pred alts c hc
      | .Let binds body, hc =>
        rcases List.mem_append.mp hc with hc | hc
        · exact collectMatchesBinds_pred binds c hc
        · exact collectMatches_pred body c hc
      | .Var _, hc | .Lit _, hc | .Builtin _, hc | .Error, hc => simp [collectChildren] at hc
  termination_by e => sizeOf e
  decreasing_by all_goals (simp_wf; (try subst_vars); (try simp); try omega)

  theorem collectMatchesList_pred :
      ∀ (es : List Expr), ∀ c ∈ collectMatchesList predicate es, predicate c = true
    | [], c, hc => by simp [collectMatchesList] at hc
    | e :: rest, c, hc => by
      simp only [collectMatchesList, List.mem_append] at hc
      rcases hc with hc | hc
      · exact collectMatches_pred e c hc
      · exact collectMatchesList_pred rest c hc
  termination_by es => sizeOf es

  theorem collectMatchesBinds_pred :
      ∀ (binds : List (VarId × Expr × Bool)), ∀ c ∈ collectMatchesBinds predicate binds,
        predicate c = true
    | [], c, hc => by simp [collectMatchesBinds] at hc
    | (_, rhs, _) :: rest, c, hc => by
      simp only [collectMatchesBinds, List.mem_append] at hc
      rcases hc with hc | hc
      · exact collectMatches_pred rhs c hc
      · exact collectMatchesBinds_pred rest c hc
  termination_by binds => sizeOf binds
end

/-- Every collected candidate of a lowering expression lowers somewhere. -/
def LowersSomewhere (c : Expr) : Prop := ∃ env t, lowerTotalExpr env c = some t

mutual
  theorem collectMatches_lowers :
      ∀ (e : Expr) (env : List VarId) (t : Term), lowerTotalExpr env e = some t →
        ∀ c ∈ collectMatches predicate e, LowersSomewhere c
    | e, env, t, h, c, hc => by
      rcases collect_cases predicate hc with ⟨rfl, _⟩ | hc'
      · exact ⟨env, t, h⟩
      clear hc
      match he : e, h, hc' with
      | .Lam x body, h, hc =>
        rw [lowerTotalExpr_lam] at h
        cases hb : lowerTotalExpr (x :: env) body with
        | none => simp [hb] at h
        | some tb => exact collectMatches_lowers body (x :: env) tb hb c hc
      | .Fix f body, h, hc =>
        match hb₀ : body, h, hc with
        | .Lam x inner, h, hc =>
          rw [lowerTotalExpr_fix_lam_canonical] at h
          cases hb : lowerTotal (x :: f :: ⟨maxUidExpr (expandFix inner) + 1, .gen, "s"⟩ :: env)
              (expandFix inner) with
          | none => simp [hb] at h
          | some tb =>
            refine collectMatches_lowers (.Lam x inner)
              (f :: ⟨maxUidExpr (expandFix inner) + 1, .gen, "s"⟩ :: env) (.Lam 0 tb) ?_ c hc
            rw [lowerTotalExpr_lam]
            have hb' : lowerTotalExpr
                (x :: f :: ⟨maxUidExpr (expandFix inner) + 1, .gen, "s"⟩ :: env) inner =
                some tb := hb
            rw [hb']; rfl
        | .Var _, h, _ | .Lit _, h, _ | .Builtin _, h, _ | .Error, h, _
        | .Fix _ _, h, _ | .App _ _, h, _ | .Force _, h, _ | .Delay _, h, _
        | .Constr _ _, h, _ | .Case _ _, h, _ | .Let _ _, h, _ =>
          rw [Moist.Verified.MIR.lowerTotalExpr_fix_nonlam_none _ _ _
            (fun _ _ hne => Expr.noConfusion hne)] at h
          cases h
      | .Force inner, h, hc =>
        rw [lowerTotalExpr_force] at h
        cases hb : lowerTotalExpr env inner with
        | none => simp [hb] at h
        | some tb => exact collectMatches_lowers inner env tb hb c hc
      | .Delay inner, h, hc =>
        rw [lowerTotalExpr_delay] at h
        cases hb : lowerTotalExpr env inner with
        | none => simp [hb] at h
        | some tb => exact collectMatches_lowers inner env tb hb c hc
      | .App f a, h, hc =>
        rw [lowerTotalExpr_app] at h
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨tf, hf, ta, ha, _⟩ := h
        rcases List.mem_append.mp hc with hc | hc
        · exact collectMatches_lowers f env tf hf c hc
        · exact collectMatches_lowers a env ta ha c hc
      | .Constr _ fields, h, hc =>
        rw [lowerTotalExpr_constr_of_list] at h
        cases hb : lowerTotalExprList env fields with
        | none => simp [hb] at h
        | some tb => exact collectMatchesList_lowers fields env tb hb c hc
      | .Case s alts, h, hc =>
        rw [lowerTotalExpr_case_of_list] at h
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨ts', hs, tas, ha, _⟩ := h
        rcases List.mem_append.mp hc with hc | hc
        · exact collectMatches_lowers s env ts' hs c hc
        · exact collectMatchesList_lowers alts env tas ha c hc
      | .Let binds body, h, hc =>
        rw [lowerTotalExpr_let_eq] at h
        exact collectMatchesBinds_lowers binds body env t h c hc
      | .Var _, _, hc | .Lit _, _, hc | .Builtin _, _, hc | .Error, _, hc =>
        simp [collectChildren] at hc
  termination_by e => sizeOf e
  decreasing_by all_goals (simp_wf; (try subst_vars); (try simp); try omega)

  theorem collectMatchesList_lowers :
      ∀ (es : List Expr) (env : List VarId) (ts : List Term), lowerTotalExprList env es = some ts →
        ∀ c ∈ collectMatchesList predicate es, LowersSomewhere c
    | [], _, _, _, c, hc => by simp [collectMatchesList] at hc
    | e :: rest, env, ts, h, c, hc => by
      rw [lowerTotalExprList_cons] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨t₁, h₁, ts₁, h₂, _⟩ := h
      simp only [collectMatchesList, List.mem_append] at hc
      rcases hc with hc | hc
      · exact collectMatches_lowers e env t₁ h₁ c hc
      · exact collectMatchesList_lowers rest env ts₁ h₂ c hc
  termination_by es => sizeOf es

  theorem collectMatchesBinds_lowers :
      ∀ (binds : List (VarId × Expr × Bool)) (body : Expr) (env : List VarId) (t : Term),
        lowerTotalLet env (expandFixBinds binds) (expandFix body) = some t →
        ∀ c ∈ collectMatchesBinds predicate binds ++ collectMatches predicate body,
          LowersSomewhere c
    | [], body, env, t, h, c, hc => by
      simp only [collectMatchesBinds, List.nil_append] at hc
      simp only [expandFixBinds, lowerTotalLet] at h
      exact collectMatches_lowers body env t h c hc
    | (x, rhs, _) :: rest, body, env, t, h, c, hc => by
      simp only [expandFixBinds, lowerTotalLet, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at h
      obtain ⟨r, hr, b, hb, _⟩ := h
      simp only [collectMatchesBinds, List.mem_append] at hc
      rcases hc with (hc | hc) | hc
      · exact collectMatches_lowers rhs env r hr c hc
      · exact collectMatchesBinds_lowers rest body (x :: env) b hb c (List.mem_append_left _ hc)
      · exact collectMatchesBinds_lowers rest body (x :: env) b hb c (List.mem_append_right _ hc)
  termination_by binds body => sizeOf binds + sizeOf body
end

end Collect

omit sv in
theorem mem_dedup : ∀ (l acc : List Expr) (x : Expr),
    x ∈ l.foldl (fun result candidate =>
      if result.any (alphaEq candidate) then result else result ++ [candidate]) acc →
    x ∈ acc ∨ x ∈ l
  | [], _, _, h => .inl h
  | c :: rest, acc, x, h => by
    simp only [List.foldl_cons] at h
    rcases mem_dedup rest _ x h with h | h
    · split at h
      · exact .inl h
      · rcases List.mem_append.mp h with h | h
        · exact .inl h
        · simp only [List.mem_singleton] at h; subst h; exact .inr (.head _)
    · exact .inr (.tail _ h)

/-- Candidates the sharing pass may bind. -/
structure Shareable (c : Expr) : Prop where
  closed : Closed c
  halts : ∀ t, lowerTotalExpr [] c = some t → Halts t

theorem share_selected_refines (predicate : Expr → Bool) (e : Expr)
    (hpred : ∀ c, predicate c = true → Shareable c)
    (selected : List Expr) (hsel : ∀ c ∈ selected, c ∈ collectMatches predicate e)
    (start : Nat) (hstart : maxUidExpr e < start) :
    Moist.Verified.MIR.MIRCtxRefines e
      (.Let ((selected.zipIdx.map fun (candidate, index) =>
          (candidate, ({ uid := start + index, origin := .gen, hint := "shared" } : VarId))).map
          fun (rhs, binder) => (binder, rhs, false))
        (replaceMatches (selected.zipIdx.map fun (candidate, index) =>
          (candidate, ({ uid := start + index, origin := .gen, hint := "shared" } : VarId))) e)) := by
  have hget : ∀ j (h : j < (selected.zipIdx.map fun (candidate, index) =>
      (candidate, ({ uid := start + index, origin := .gen, hint := "shared" } : VarId))).length),
      (selected.zipIdx.map fun (candidate, index) =>
        (candidate, ({ uid := start + index, origin := .gen, hint := "shared" } : VarId)))[j] =
      (selected[j]'(by simpa using h),
        ({ uid := start + j, origin := .gen, hint := "shared" } : VarId)) := by
    intro j h
    simp [List.getElem_map, List.getElem_zipIdx]
  have hmem : ∀ entry ∈ (selected.zipIdx.map fun (candidate, index) =>
      (candidate, ({ uid := start + index, origin := .gen, hint := "shared" } : VarId))),
      entry.1 ∈ selected ∧ start ≤ entry.2.uid := by
    intro entry he
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp he
    rw [hget j hj]
    exact ⟨List.getElem_mem _, by simp⟩
  have hshare : ∀ entry ∈ (selected.zipIdx.map fun (candidate, index) =>
      (candidate, ({ uid := start + index, origin := .gen, hint := "shared" } : VarId))),
      Shareable entry.1 := fun entry he =>
    hpred _ (collectMatches_pred predicate e _ (hsel _ (hmem entry he).1))
  apply share_refines
  · exact fun entry he => (hshare entry he).closed
  · intro a b ha hb hab
    rw [hget a ha, hget b hb, VarId.beq_true_iff] at hab
    simp only at hab
    omega
  · exact fun entry he => by have := (hmem entry he).2; omega
  · exact fun entry he => (hshare entry he).halts
  · intro env t h entry he
    obtain ⟨env', t', h'⟩ := collectMatches_lowers predicate e env t h entry.1 (hsel _ (hmem entry he).1)
    rw [lowerTotalExpr_closed (hshare entry he).closed] at h'
    rw [h']; rfl

/-- `shareClosed` is a refinement for any predicate accepting only closed
    candidates whose lowering halts. -/
theorem shareClosed_refines (predicate : Expr → Bool) (minimumUses : Nat) (e : Expr)
    (hpred : ∀ c, predicate c = true → Shareable c) :
    Moist.Verified.MIR.MIRCtxRefines e (shareClosed predicate minimumUses e) := by
  unfold shareClosed shareReplacements
  dsimp only
  split
  · exact Moist.Verified.MIR.mirCtxRefines_refl e
  · refine share_selected_refines predicate e hpred _ (fun c hc => ?_) _ (Nat.lt_succ_self _)
    rcases mem_dedup _ [] c (List.mem_filter.mp hc).1 with h | h
    · cases h
    · exact h

/-! ## The two sharing passes -/

theorem hoistBuiltinStates_refines (minimumUses : Nat) (e : Expr) :
    Moist.Verified.MIR.MIRCtxRefines e (hoistBuiltinStates minimumUses e) := by
  apply shareClosed_refines
  intro c hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨_, hfv⟩, hrem⟩ := hc
  obtain ⟨remaining, hr⟩ := Option.isSome_iff_exists.mp hrem
  refine ⟨closed_of_isEmpty hfv, ?_⟩
  · intro t ht ρ
    exact Moist.Verified.BuiltinState.builtinRemainder_halts (expandFix c) [] t remaining
      (Moist.Verified.BuiltinState.builtinRemainder_expandFix c remaining hr) ht ρ
      (fun n hn hle => absurd hle (by simp; omega))

theorem poolConstants_refines (minimumBytes : Nat) (e : Expr) :
    Moist.Verified.MIR.MIRCtxRefines e (poolConstants minimumBytes e) := by
  apply shareClosed_refines
  intro c hc
  cases c with
  | Lit literal =>
    obtain ⟨constant, type⟩ := literal
    refine ⟨fun x => by simp [freeVars, VarSet.contains, VarSet.empty], ?_⟩
    intro t ht ρ
    simp only [lowerTotalExpr, expandFix, lowerTotal, Option.some.injEq] at ht
    subst ht
    exact ⟨_, 2, rfl⟩
  | _ => simp at hc

end Moist.Verified.Sharing
