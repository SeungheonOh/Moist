import Moist.Verified.FixLowering
import Moist.Verified.MIR
import Moist.Verified.InlineSoundness.Rename
import Moist.Verified.AdvancedRefinement
import Moist.MIR.Lower
import Moist.MIR.FromUPLC
import Moist.MIR.Compile

/-! # Production lowering and re-lifting

* `lower_correct`: the executable `lower` succeeds exactly when
  `lowerTotalExpr` does, and the two results are contextually equivalent
  (`CtxRefines` both ways). They differ only in the encoding of recursive
  lambdas: `lowerTotalExpr` keeps the redex `(λf. λx. B) (λv. s s v)`, the
  production lowering substitutes the self application `s s` for `f`, so
  recursive calls run `[[s s] a]` (`FixLowering`). That needs `B` not to use
  the slot of `s`, which lowering leaves shadowed (`lower_freeOf`).
* `liftUPLC_lowerTotal`: lowering a lifted closed UPLC term gives back the term
  up to binder names and the meaningless index `0` (`canon`), which is
  contextually equivalent to it and the identity on lowering output.
-/

namespace Moist.Verified.LoweringSoundness

open Moist.CEK
open Moist.Plutus.Term (Term)
open Moist.MIR (Expr VarId lower lowerList lowerLet lowerExpr lowerTotal lowerTotalExpr
  envLookupT expandFix maxUidExpr fixLamWrap fixLamWrapUplc fixSelfCall)
open Moist.Verified (closedAt closedAtList substTerm substTermList renameTerm renameTermList)
open Moist.Verified.Contextual
open Moist.Verified.Equivalence (ListRel)
open Moist.Verified.InlineSoundness.StrictOcc (freeOf freeOfList)
open Moist.Verified.FixLowering (selfCallAt substTerm_selfCallAt_lam)
open Moist.Verified.MIR (lowerTotalExprList lowerTotalExpr_lam lowerTotalExpr_app
  lowerTotalExpr_force lowerTotalExpr_delay lowerTotalExpr_constr_of_list
  lowerTotalExpr_case_of_list lowerTotalExprList_nil lowerTotalExprList_cons
  lowerTotalExpr_fix_nonlam_none lowerTotalExpr_closedAt)

/-! ## Contextual equivalence -/

/-- Contextual refinement in both directions. -/
def CtxEquiv (a b : Term) : Prop := CtxRefines a b ∧ CtxRefines b a

theorem CtxEquiv.refl (t : Term) : CtxEquiv t t := ⟨ctxRefines_refl t, ctxRefines_refl t⟩

theorem CtxEquiv.symm {a b : Term} (h : CtxEquiv a b) : CtxEquiv b a := ⟨h.2, h.1⟩

theorem CtxEquiv.trans {a b c : Term} (h₁ : CtxEquiv a b) (h₂ : CtxEquiv b c) :
    CtxEquiv a c := ⟨ctxRefines_trans h₁.1 h₂.1, ctxRefines_trans h₂.2 h₁.2⟩

theorem CtxEquiv.fill {a b : Term} (h : CtxEquiv a b) (C : Context) :
    CtxEquiv (Contextual.fill C a) (Contextual.fill C b) :=
  ⟨ctxRefines_fill h.1 C, ctxRefines_fill h.2 C⟩

theorem CtxEquiv.lam {a b : Term} (name : Nat) (h : CtxEquiv a b) :
    CtxEquiv (.Lam name a) (.Lam name b) := h.fill (.Lam name .Hole)

theorem CtxEquiv.force {a b : Term} (h : CtxEquiv a b) : CtxEquiv (.Force a) (.Force b) :=
  h.fill (.Force .Hole)

theorem CtxEquiv.delay {a b : Term} (h : CtxEquiv a b) : CtxEquiv (.Delay a) (.Delay b) :=
  h.fill (.Delay .Hole)

theorem CtxEquiv.app {f₁ f₂ a₁ a₂ : Term} (hf : CtxEquiv f₁ f₂) (ha : CtxEquiv a₁ a₂) :
    CtxEquiv (.Apply f₁ a₁) (.Apply f₂ a₂) :=
  (hf.fill (.AppLeft .Hole a₁)).trans (ha.fill (.AppRight f₂ .Hole))

private theorem constr_from (tag : Nat) :
    ∀ (pre as bs : List Term), ListRel CtxEquiv as bs →
      CtxEquiv (.Constr tag (pre ++ as)) (.Constr tag (pre ++ bs))
  | _, [], [], _ => CtxEquiv.refl _
  | pre, a :: as, b :: bs, ⟨hab, hrest⟩ => by
    have step : CtxEquiv (.Constr tag (pre ++ a :: as)) (.Constr tag (pre ++ b :: as)) := by
      have := hab.fill (.Constr tag pre .Hole as)
      simpa [Contextual.fill] using this
    have rest := constr_from tag (pre ++ [b]) as bs hrest
    simp only [List.append_assoc, List.singleton_append] at rest
    exact step.trans rest
  | _, [], _ :: _, h => absurd h id
  | _, _ :: _, [], h => absurd h id

theorem CtxEquiv.constr {tag : Nat} {as bs : List Term} (h : ListRel CtxEquiv as bs) :
    CtxEquiv (.Constr tag as) (.Constr tag bs) := constr_from tag [] as bs h

private theorem case_from (scrut : Term) :
    ∀ (pre as bs : List Term), ListRel CtxEquiv as bs →
      CtxEquiv (.Case scrut (pre ++ as)) (.Case scrut (pre ++ bs))
  | _, [], [], _ => CtxEquiv.refl _
  | pre, a :: as, b :: bs, ⟨hab, hrest⟩ => by
    have step : CtxEquiv (.Case scrut (pre ++ a :: as)) (.Case scrut (pre ++ b :: as)) := by
      have := hab.fill (.CaseAlt scrut pre .Hole as)
      simpa [Contextual.fill] using this
    have rest := case_from scrut (pre ++ [b]) as bs hrest
    simp only [List.append_assoc, List.singleton_append] at rest
    exact step.trans rest
  | _, [], _ :: _, h => absurd h id
  | _, _ :: _, [], h => absurd h id

theorem CtxEquiv.case {s₁ s₂ : Term} {as bs : List Term} (hs : CtxEquiv s₁ s₂)
    (h : ListRel CtxEquiv as bs) : CtxEquiv (.Case s₁ as) (.Case s₂ bs) :=
  (hs.fill (.Case .Hole as)).trans (case_from s₂ [] as bs h)

/-- `n` nested binders around the hole. -/
def lams : Nat → Context
  | 0 => .Hole
  | n + 1 => .Lam 0 (lams n)

theorem lams_binders : ∀ n, (lams n).binders = n
  | 0 => rfl
  | n + 1 => by simp [lams, Context.binders, lams_binders n]

theorem lams_closedAt : ∀ n d, (lams n).closedAt d = true
  | 0, _ => rfl
  | n + 1, d => by simp [lams, Context.closedAt, lams_closedAt n (d + 1)]

/-- Contextual refinement preserves closedness at every depth. -/
theorem closedAt_of_ctxRefines {a b : Term} (h : CtxRefines a b) {d : Nat}
    (ha : closedAt d a = true) : closedAt d b = true := by
  have hfill : closedAt 0 (Contextual.fill (lams d) a) = true := by
    rw [fill_closedAt_iff]; exact ⟨lams_closedAt d 0, by rw [lams_binders]; simpa using ha⟩
  have := ((fill_closedAt_iff (lams d) b 0).mp (h (lams d) hfill).1).2
  rwa [lams_binders, Nat.zero_add] at this

/-! ## Recursive lambdas -/

theorem fixLamWrap_ctxEquiv {d : Nat} {B : Term} (hB : closedAt (d + 3) B = true)
    (hfree : freeOf 3 B = true) : CtxEquiv (fixLamWrapUplc B) (fixLamWrap B) :=
  ⟨FixLowering.fixLamWrap_forward d B hB hfree, FixLowering.fixLamWrap_backward d B hB hfree⟩

/-- `fixLamWrapUplc` is a context around its body. -/
def fixLamWrapContext : Context :=
  .AppRight (.Lam 0 (.Apply (.Var 1) (.Var 1)))
    (.Lam 0 (.AppLeft (.Lam 0 (.Lam 0 .Hole))
      (.Lam 0 (.Apply (.Apply (.Var 2) (.Var 2)) (.Var 1)))))

theorem fixLamWrapUplc_fill (B : Term) :
    fixLamWrapUplc B = Contextual.fill fixLamWrapContext B := rfl

/-! ## Production lowering against `lowerTotalExpr` -/

/-- Both lowerings fail, or both succeed with contextually equivalent terms. -/
def LowerRel : Except String Term → Option Term → Prop
  | .ok t, some t₀ => CtxEquiv t₀ t
  | .error _, none => True
  | _, _ => False

def LowerListRel : Except String (List Term) → Option (List Term) → Prop
  | .ok ts, some ts₀ => ListRel CtxEquiv ts₀ ts
  | .error _, none => True
  | _, _ => False

/-- A lookup slot shadowed by an earlier entry is never reached. -/
theorem lowerTotalExpr_shadow_slot (env : List VarId) (f x : VarId) (body : Expr) (s : VarId)
    (hs : maxUidExpr body < s.uid) :
    lowerTotalExpr (x :: f :: s :: env) body = lowerTotalExpr (x :: f :: x :: env) body := by
  apply Moist.Verified.InlineSoundness.Rename.lowerTotalExpr_agree
  intro z hz
  unfold envLookupT
  simp only [envLookupT.go]
  by_cases hx : (x == z) = true
  · simp [hx]
  · by_cases hf : (f == z) = true
    · simp [hx, hf]
    · have hsz : (s == z) = false := by
        rw [Moist.MIR.VarId.beq_false_iff]; exact Or.inr (by omega)
      simp [hx, hf, hsz]

theorem lowerTotalExpr_fix_lam_shadow (env : List VarId) (f x : VarId) (body : Expr) :
    lowerTotalExpr env (.Fix f (.Lam x body)) =
      (lowerTotalExpr (x :: f :: x :: env) body).map fixLamWrapUplc := by
  let s : VarId := ⟨max (maxUidExpr (expandFix body)) (maxUidExpr body) + 1, .gen, "s"⟩
  rw [Moist.Verified.InlineSoundness.Rename.lowerTotalExpr_fix_lam env f x body s
      (by show _ < max _ _ + 1; omega),
    lowerTotalExpr_shadow_slot env f x body s (by show _ < max _ _ + 1; omega)]

theorem fix_lowerRel {env : List VarId} {r : Except String Term} {o : Option Term}
    (h : LowerRel r o) (hlen : ∀ t₀, o = some t₀ → closedAt (env.length + 3) t₀ = true)
    (hfree : ∀ t, r = .ok t → freeOf 3 t = true) :
    LowerRel (r.map fixLamWrap) (o.map fixLamWrapUplc) := by
  cases r <;> cases o <;> simp only [LowerRel, Except.map, Option.map] at h hfree ⊢
  rename_i t t₀
  have hc₀ := hlen t₀ rfl
  have hc := closedAt_of_ctxRefines h.1 hc₀
  exact (h.fill fixLamWrapContext).trans (fixLamWrap_ctxEquiv hc (hfree t rfl))

theorem lower_fix_lam (env : List VarId) (f x : VarId) (body : Expr) :
    lower env (.Fix f (.Lam x body)) = (lower (x :: f :: x :: env) body).map fixLamWrap := by
  simp only [lower]; cases lower (x :: f :: x :: env) body <;> rfl

theorem lower_fix_nonlam (env : List VarId) (f : VarId) (body : Expr)
    (h : ∀ x inner, body ≠ .Lam x inner) : ∃ msg, lower env (.Fix f body) = .error msg := by
  cases body with
  | Lam x inner => exact absurd rfl (h x inner)
  | _ => simp only [lower]; exact ⟨_, rfl⟩

/-! ## Lowering never uses a shadowed slot -/

theorem envLookupT_go_ge (v : VarId) :
    ∀ (env : List VarId) (n m : Nat), envLookupT.go v env n = some m → n ≤ m
  | [], _, _, h => by simp [envLookupT.go] at h
  | x :: xs, n, m, h => by
    simp only [envLookupT.go] at h
    split at h
    · cases h; exact Nat.le_refl _
    · exact Nat.le_of_succ_le (envLookupT_go_ge v xs (n + 1) m h)

/-- A name resolved at the position of `y` equals `y` and no earlier binder. -/
theorem envLookupT_go_at (v y : VarId) (rest : List VarId) :
    ∀ (pre : List VarId) (n : Nat), envLookupT.go v (pre ++ y :: rest) n = some (n + pre.length) →
      (y == v) = true ∧ ∀ p ∈ pre, (p == v) = false
  | [], n, h => by
    simp only [List.nil_append, envLookupT.go, List.length_nil, Nat.add_zero] at h
    split at h
    · rename_i hyv
      exact ⟨hyv, fun _ hp => absurd hp List.not_mem_nil⟩
    · have := envLookupT_go_ge v rest (n + 1) n h
      omega
  | q :: qs, n, h => by
    simp only [List.cons_append, envLookupT.go, List.length_cons] at h
    split at h
    · rename_i hqv
      have := Option.some.inj h
      omega
    · rename_i hqv
      obtain ⟨hy, hqs⟩ := envLookupT_go_at v y rest qs (n + 1)
        (by rw [h]; congr 1; omega)
      refine ⟨hy, fun p hp => ?_⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · simpa using hqv
      · exact hqs p hp

/-- A binder shadowed by an earlier one never resolves a name. -/
theorem envLookupT_ne_shadowed {pre : List VarId} {y : VarId} (rest : List VarId)
    (hy : pre.any (· == y) = true) (v : VarId) :
    envLookupT (pre ++ y :: rest) v ≠ some pre.length := by
  intro h
  obtain ⟨hyv, hpre⟩ := envLookupT_go_at v y rest pre 0 (by rw [Nat.zero_add]; exact h)
  obtain ⟨p, hp, hpy⟩ := List.any_eq_true.mp hy
  have := VarId.beq_trans p y v hpy hyv
  rw [hpre p hp] at this
  cases this

mutual
  theorem freeOf_substTerm_selfCall : ∀ (p m : Nat) (t : Term), 1 ≤ p → p < m →
      freeOf (m + 1) t = true → freeOf m (substTerm p (selfCallAt p) t) = true
    | p, m, .Var n, hp, hpm, ht => by
      simp only [freeOf, bne_iff_ne, ne_eq] at ht
      simp only [substTerm]
      by_cases hn : n = p
      · simp only [hn, if_true, selfCallAt, freeOf, bne_iff_ne, ne_eq, Bool.and_eq_true]
        omega
      · by_cases hgt : n > p
        · simp only [hn, hgt, if_true, if_false, freeOf, bne_iff_ne, ne_eq]; omega
        · simp only [hn, hgt, if_false, freeOf, bne_iff_ne, ne_eq]; omega
    | p, m, .Lam nm body, hp, hpm, ht => by
      simp only [freeOf] at ht
      rw [substTerm_selfCallAt_lam hp]
      simp only [freeOf]
      exact freeOf_substTerm_selfCall (p + 1) (m + 1) body (by omega) (by omega) ht
    | p, m, .Apply f x, hp, hpm, ht => by
      simp only [freeOf, Bool.and_eq_true] at ht
      simp only [substTerm, freeOf, Bool.and_eq_true]
      exact ⟨freeOf_substTerm_selfCall p m f hp hpm ht.1,
        freeOf_substTerm_selfCall p m x hp hpm ht.2⟩
    | p, m, .Force e, hp, hpm, ht => by
      simp only [freeOf] at ht
      simp only [substTerm, freeOf]
      exact freeOf_substTerm_selfCall p m e hp hpm ht
    | p, m, .Delay e, hp, hpm, ht => by
      simp only [freeOf] at ht
      simp only [substTerm, freeOf]
      exact freeOf_substTerm_selfCall p m e hp hpm ht
    | p, m, .Constr _ args, hp, hpm, ht => by
      simp only [freeOf] at ht
      simp only [substTerm, freeOf]
      exact freeOfList_substTermList_selfCall p m args hp hpm ht
    | p, m, .Case sc alts, hp, hpm, ht => by
      simp only [freeOf, Bool.and_eq_true] at ht
      simp only [substTerm, freeOf, Bool.and_eq_true]
      exact ⟨freeOf_substTerm_selfCall p m sc hp hpm ht.1,
        freeOfList_substTermList_selfCall p m alts hp hpm ht.2⟩
    | _, _, .Constant _, _, _, _ => by simp [substTerm, freeOf]
    | _, _, .Builtin _, _, _, _ => by simp [substTerm, freeOf]
    | _, _, .Error, _, _, _ => by simp [substTerm, freeOf]
  termination_by _ _ t => sizeOf t

  theorem freeOfList_substTermList_selfCall : ∀ (p m : Nat) (ts : List Term), 1 ≤ p → p < m →
      freeOfList (m + 1) ts = true → freeOfList m (substTermList p (selfCallAt p) ts) = true
    | _, _, [], _, _, _ => by simp [substTermList, freeOfList]
    | p, m, t :: ts, hp, hpm, ht => by
      simp only [freeOfList, Bool.and_eq_true] at ht
      simp only [substTermList, freeOfList, Bool.and_eq_true]
      exact ⟨freeOf_substTerm_selfCall p m t hp hpm ht.1,
        freeOfList_substTermList_selfCall p m ts hp hpm ht.2⟩
  termination_by _ _ ts => sizeOf ts
end

theorem freeOf_fixLamWrap {n : Nat} {B : Term} (h : freeOf (n + 4) B = true) :
    freeOf (n + 1) (fixLamWrap B) = true := by
  have hs := freeOf_substTerm_selfCall 2 (n + 3) B (by omega) (by omega) h
  simp only [fixLamWrap, freeOf, Bool.and_eq_true, bne_iff_ne, ne_eq]
  exact ⟨by omega, hs⟩

theorem any_cons_of {x y : VarId} {pre : List VarId} (h : pre.any (· == y) = true) :
    (x :: pre).any (· == y) = true := by simp [List.any_cons, h]

mutual
  /-- Lowering under an environment whose binder `y` is shadowed by an earlier
      one never refers to the slot of `y`. -/
  theorem lower_freeOf (pre : List VarId) (y : VarId) (rest : List VarId)
      (hy : pre.any (· == y) = true) (e : Expr) (t : Term)
      (h : lower (pre ++ y :: rest) e = .ok t) : freeOf (pre.length + 1) t = true := by
    match e with
    | .Var x =>
      simp only [lower] at h
      cases hl : envLookupT (pre ++ y :: rest) x <;> simp [hl] at h
      subst h
      rename_i idx
      simp only [freeOf, bne_iff_ne, ne_eq]
      intro heq
      exact envLookupT_ne_shadowed rest hy x (by rw [hl]; congr 1; omega)
    | .Lit (c, ty) => simp only [lower, Except.ok.injEq] at h; subst h; simp [freeOf]
    | .Builtin b => simp only [lower, Except.ok.injEq] at h; subst h; simp [freeOf]
    | .Error => simp only [lower, Except.ok.injEq] at h; subst h; simp [freeOf]
    | .Lam x body =>
      simp only [lower] at h
      cases hb : lower (x :: (pre ++ y :: rest)) body <;>
        simp [hb, bind, Except.bind, pure, Except.pure] at h
      subst h
      have := lower_freeOf (x :: pre) y rest (any_cons_of hy) body _ hb
      simp only [List.length_cons] at this
      simp [freeOf, this]
    | .App f a =>
      simp only [lower] at h
      cases hf : lower (pre ++ y :: rest) f <;> cases ha : lower (pre ++ y :: rest) a <;>
        simp [hf, ha, bind, Except.bind, pure, Except.pure] at h
      subst h
      simp [freeOf, lower_freeOf pre y rest hy f _ hf, lower_freeOf pre y rest hy a _ ha]
    | .Force inner =>
      simp only [lower] at h
      cases hi : lower (pre ++ y :: rest) inner <;>
        simp [hi, bind, Except.bind, pure, Except.pure] at h
      subst h
      simp [freeOf, lower_freeOf pre y rest hy inner _ hi]
    | .Delay inner =>
      simp only [lower] at h
      cases hi : lower (pre ++ y :: rest) inner <;>
        simp [hi, bind, Except.bind, pure, Except.pure] at h
      subst h
      simp [freeOf, lower_freeOf pre y rest hy inner _ hi]
    | .Constr tag args =>
      simp only [lower] at h
      cases ha : lowerList (pre ++ y :: rest) args <;>
        simp [ha, bind, Except.bind, pure, Except.pure] at h
      subst h
      simp [freeOf, lowerList_freeOf pre y rest hy args _ ha]
    | .Case scrut alts =>
      simp only [lower] at h
      cases hs : lower (pre ++ y :: rest) scrut <;> cases ha : lowerList (pre ++ y :: rest) alts <;>
        simp [hs, ha, bind, Except.bind, pure, Except.pure] at h
      subst h
      simp [freeOf, lower_freeOf pre y rest hy scrut _ hs,
        lowerList_freeOf pre y rest hy alts _ ha]
    | .Let binds body =>
      simp only [lower] at h
      exact lowerLet_freeOf pre y rest hy binds body t h
    | .Fix f (.Lam x body) =>
      rw [lower_fix_lam] at h
      cases hb : lower (x :: f :: x :: (pre ++ y :: rest)) body <;> simp [hb, Except.map] at h
      subst h
      have := lower_freeOf (x :: f :: x :: pre) y rest
        (any_cons_of (any_cons_of (any_cons_of hy))) body _ hb
      simp only [List.length_cons] at this
      exact freeOf_fixLamWrap this
    | .Fix f (.Var _) | .Fix f (.Lit _) | .Fix f (.Builtin _) | .Fix f .Error
    | .Fix f (.Fix _ _) | .Fix f (.App _ _) | .Fix f (.Force _) | .Fix f (.Delay _)
    | .Fix f (.Constr _ _) | .Fix f (.Case _ _) | .Fix f (.Let _ _) =>
      simp [lower] at h
  termination_by sizeOf e

  theorem lowerList_freeOf (pre : List VarId) (y : VarId) (rest : List VarId)
      (hy : pre.any (· == y) = true) (es : List Expr) (ts : List Term)
      (h : lowerList (pre ++ y :: rest) es = .ok ts) : freeOfList (pre.length + 1) ts = true := by
    match es with
    | [] => simp only [lowerList, Except.ok.injEq] at h; subst h; simp [freeOfList]
    | e :: es =>
      simp only [lowerList] at h
      cases he : lower (pre ++ y :: rest) e <;> cases hr : lowerList (pre ++ y :: rest) es <;>
        simp [he, hr, bind, Except.bind, pure, Except.pure] at h
      subst h
      simp [freeOfList, lower_freeOf pre y rest hy e _ he, lowerList_freeOf pre y rest hy es _ hr]
  termination_by sizeOf es

  theorem lowerLet_freeOf (pre : List VarId) (y : VarId) (rest : List VarId)
      (hy : pre.any (· == y) = true) (binds : List (VarId × Expr × Bool)) (body : Expr)
      (t : Term) (h : lowerLet (pre ++ y :: rest) binds body = .ok t) :
      freeOf (pre.length + 1) t = true := by
    match binds with
    | [] => simp only [lowerLet] at h; exact lower_freeOf pre y rest hy body t h
    | (x, rhs, _) :: bs =>
      simp only [lowerLet] at h
      cases hr : lower (pre ++ y :: rest) rhs <;>
        cases hb : lowerLet (x :: (pre ++ y :: rest)) bs body <;>
        simp [hr, hb, bind, Except.bind, pure, Except.pure] at h
      subst h
      have := lowerLet_freeOf (x :: pre) y rest (any_cons_of hy) bs body _ hb
      simp only [List.length_cons] at this
      simp [freeOf, this, lower_freeOf pre y rest hy rhs _ hr]
  termination_by sizeOf binds + sizeOf body
end

/-- The slot of `s` in the body of a recursive lambda is never used. -/
theorem lower_fix_body_freeOf {env : List VarId} {f x : VarId} {body : Expr} {t : Term}
    (h : lower (x :: f :: x :: env) body = .ok t) : freeOf 3 t = true :=
  lower_freeOf [x, f] x env (by simp [List.any_cons, (VarId.beq_true_iff x x).mpr ⟨rfl, rfl⟩])
    body t h

mutual
  theorem lower_correct (env : List VarId) (e : Expr) :
      LowerRel (lower env e) (lowerTotalExpr env e) := by
    match e with
    | .Var x =>
      rw [Moist.Verified.InlineSoundness.Rename.lowerTotalExpr_var]
      simp only [lower]
      cases envLookupT env x <;> simp [LowerRel, CtxEquiv.refl]
    | .Lit (c, ty) =>
      simp [lower, lowerTotalExpr, expandFix, lowerTotal, LowerRel, CtxEquiv.refl]
    | .Builtin b =>
      simp [lower, lowerTotalExpr, expandFix, lowerTotal, LowerRel, CtxEquiv.refl]
    | .Error =>
      simp [lower, lowerTotalExpr, expandFix, lowerTotal, LowerRel, CtxEquiv.refl]
    | .Lam x body =>
      have ih := lower_correct (x :: env) body
      rw [lowerTotalExpr_lam]
      simp only [lower]
      revert ih
      cases lower (x :: env) body <;> cases lowerTotalExpr (x :: env) body <;>
        simp [LowerRel, bind, Except.bind, pure, Except.pure]
      exact fun h => h.lam 0
    | .App f a =>
      have ihf := lower_correct env f
      have iha := lower_correct env a
      rw [lowerTotalExpr_app]
      simp only [lower]
      revert ihf iha
      cases lower env f <;> cases lowerTotalExpr env f <;>
        cases lower env a <;> cases lowerTotalExpr env a <;>
        simp [LowerRel, bind, Except.bind, pure, Except.pure]
      exact fun hf ha => hf.app ha
    | .Force inner =>
      have ih := lower_correct env inner
      rw [lowerTotalExpr_force]
      simp only [lower]
      revert ih
      cases lower env inner <;> cases lowerTotalExpr env inner <;>
        simp [LowerRel, bind, Except.bind, pure, Except.pure]
      exact fun h => h.force
    | .Delay inner =>
      have ih := lower_correct env inner
      rw [lowerTotalExpr_delay]
      simp only [lower]
      revert ih
      cases lower env inner <;> cases lowerTotalExpr env inner <;>
        simp [LowerRel, bind, Except.bind, pure, Except.pure]
      exact fun h => h.delay
    | .Constr tag args =>
      have ih := lowerList_correct env args
      rw [lowerTotalExpr_constr_of_list]
      simp only [lower]
      revert ih
      cases lowerList env args <;> cases lowerTotalExprList env args <;>
        simp [LowerRel, LowerListRel, bind, Except.bind, pure, Except.pure]
      exact fun h => CtxEquiv.constr h
    | .Case scrut alts =>
      have ihs := lower_correct env scrut
      have iha := lowerList_correct env alts
      rw [lowerTotalExpr_case_of_list]
      simp only [lower]
      revert ihs iha
      cases lower env scrut <;> cases lowerTotalExpr env scrut <;>
        cases lowerList env alts <;> cases lowerTotalExprList env alts <;>
        simp [LowerRel, LowerListRel, bind, Except.bind, pure, Except.pure]
      exact fun hs ha => CtxEquiv.case hs ha
    | .Let binds body =>
      simp only [lower]
      exact lowerLet_correct env binds body
    | .Fix f (.Lam x body) =>
      rw [lower_fix_lam, lowerTotalExpr_fix_lam_shadow]
      exact fix_lowerRel (lower_correct (x :: f :: x :: env) body)
        (fun t₀ h => by simpa [Nat.add_assoc] using lowerTotalExpr_closedAt h)
        (fun t h => lower_fix_body_freeOf h)
    | .Fix f (.Var y) | .Fix f (.Lit _) | .Fix f (.Builtin _) | .Fix f .Error
    | .Fix f (.Fix _ _) | .Fix f (.App _ _) | .Fix f (.Force _) | .Fix f (.Delay _)
    | .Fix f (.Constr _ _) | .Fix f (.Case _ _) | .Fix f (.Let _ _) =>
      rw [lowerTotalExpr_fix_nonlam_none _ _ _ (by intro _ _ h; cases h)]
      simp only [lower, LowerRel]
  termination_by sizeOf e

  theorem lowerList_correct (env : List VarId) (es : List Expr) :
      LowerListRel (lowerList env es) (lowerTotalExprList env es) := by
    match es with
    | [] => simp [lowerList, lowerTotalExprList_nil, LowerListRel, ListRel]
    | e :: rest =>
      have ih := lower_correct env e
      have ihr := lowerList_correct env rest
      rw [lowerTotalExprList_cons]
      simp only [lowerList]
      revert ih ihr
      cases lower env e <;> cases lowerTotalExpr env e <;>
        cases lowerList env rest <;> cases lowerTotalExprList env rest <;>
        simp [LowerRel, LowerListRel, ListRel, bind, Except.bind, pure, Except.pure]
      exact fun h hr => ⟨h, hr⟩
  termination_by sizeOf es

  theorem lowerLet_correct (env : List VarId) (binds : List (VarId × Expr × Bool))
      (body : Expr) :
      LowerRel (lowerLet env binds body) (lowerTotalExpr env (.Let binds body)) := by
    match binds with
    | [] =>
      rw [Moist.Verified.InlineSoundness.Rename.lowerTotalExpr_let_nil]
      simp only [lowerLet]
      exact lower_correct env body
    | (x, rhs, er) :: rest =>
      have ihr := lower_correct env rhs
      have ihb := lowerLet_correct (x :: env) rest body
      rw [Moist.Verified.InlineSoundness.Rename.lowerTotalExpr_let_cons]
      simp only [lowerLet]
      revert ihr ihb
      cases lower env rhs <;> cases lowerTotalExpr env rhs <;>
        cases lowerLet (x :: env) rest body <;> cases lowerTotalExpr (x :: env) (.Let rest body) <;>
        simp [LowerRel, bind, Except.bind, pure, Except.pure]
      exact fun hr hb => (hb.lam 0).app hr
  termination_by sizeOf binds + sizeOf body
end

/-- Production lowering in any environment: success, failure and the result up
    to contextual equivalence agree with `lowerTotalExpr`. -/
theorem lower_sound {env : List VarId} {e : Expr} {t : Term} (h : lower env e = .ok t) :
    ∃ t₀, lowerTotalExpr env e = some t₀ ∧ CtxRefines t₀ t ∧ CtxRefines t t₀ := by
  have hrel := lower_correct env e
  rw [h] at hrel
  cases ho : lowerTotalExpr env e with
  | none => rw [ho] at hrel; exact absurd hrel id
  | some t₀ => rw [ho] at hrel; exact ⟨t₀, rfl, hrel.1, hrel.2⟩

theorem lower_complete {env : List VarId} {e : Expr} {t₀ : Term}
    (h : lowerTotalExpr env e = some t₀) :
    ∃ t, lower env e = .ok t ∧ CtxRefines t₀ t ∧ CtxRefines t t₀ := by
  have hrel := lower_correct env e
  rw [h] at hrel
  cases hl : lower env e with
  | error _ => rw [hl] at hrel; exact absurd hrel id
  | ok t => rw [hl] at hrel; exact ⟨t, rfl, hrel.1, hrel.2⟩

theorem lower_error_iff (env : List VarId) (e : Expr) :
    (∃ msg, lower env e = .error msg) ↔ lowerTotalExpr env e = none := by
  have hrel := lower_correct env e
  cases hl : lower env e <;> cases ho : lowerTotalExpr env e <;>
    rw [hl, ho] at hrel <;> simp_all [LowerRel]

/-- **(a)** Executable lowering is sound and complete for `lowerTotalExpr`. -/
theorem lowerExpr_sound {e : Expr} {n : Nat} {t : Term} (h : lowerExpr e n = .ok t) :
    ∃ t₀, lowerTotalExpr [] e = some t₀ ∧ CtxRefines t₀ t ∧ CtxRefines t t₀ :=
  lower_sound h

theorem lowerExpr_complete {e : Expr} {t₀ : Term} (h : lowerTotalExpr [] e = some t₀)
    (n : Nat) : ∃ t, lowerExpr e n = .ok t ∧ CtxRefines t₀ t ∧ CtxRefines t t₀ :=
  lower_complete h

theorem lowerExpr_error_iff (e : Expr) (n : Nat) :
    (∃ msg, lowerExpr e n = .error msg) ↔ lowerTotalExpr [] e = none :=
  lower_error_iff [] e

/-! ## Failure is exactly input validation failure -/

open Moist.MIR (validateCompilationInput validateCompilationList validateCompilationBindings)

theorem envLookupT_go_isSome (v : VarId) :
    ∀ (env : List VarId) (n : Nat), (envLookupT.go v env n).isSome = env.any (· == v)
  | [], _ => rfl
  | x :: xs, n => by
    simp only [envLookupT.go, List.any_cons]
    cases x == v
    · simpa using envLookupT_go_isSome v xs (n + 1)
    · rfl

theorem envLookupT_isSome (env : List VarId) (v : VarId) :
    (envLookupT env v).isSome = env.any (· == v) := envLookupT_go_isSome v env 0

/-- Same outcome and, on failure, the same message. -/
def SameOutcome : Except String Term → Except String Unit → Prop
  | .ok _, .ok () => True
  | .error m₁, .error m₂ => m₁ = m₂
  | _, _ => False

def SameOutcomeList : Except String (List Term) → Except String Unit → Prop
  | .ok _, .ok () => True
  | .error m₁, .error m₂ => m₁ = m₂
  | _, _ => False

/-- Environments that bind the same names. -/
def SameNames (env env' : List VarId) : Prop := ∀ v, env.any (· == v) = env'.any (· == v)

theorem SameNames.cons {env env' : List VarId} (h : SameNames env env') (x : VarId) :
    SameNames (x :: env) (x :: env') := fun v => by simp only [List.any_cons, h v]

mutual
  theorem lower_validate (env env' : List VarId) (h : SameNames env env') (e : Expr) :
      SameOutcome (lower env e) (validateCompilationInput env' e) := by
    match e with
    | .Var x =>
      simp only [lower, validateCompilationInput]
      have hx : env'.any (· == x) = (envLookupT env x).isSome := by
        rw [envLookupT_isSome, h x]
      cases hl : envLookupT env x <;> rw [hl] at hx <;> rw [hx] <;>
        simp [SameOutcome, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
    | .Lit (c, ty) => simp [lower, validateCompilationInput, SameOutcome, pure, Except.pure]
    | .Builtin _ => simp [lower, validateCompilationInput, SameOutcome, pure, Except.pure]
    | .Error => simp [lower, validateCompilationInput, SameOutcome, pure, Except.pure]
    | .Lam x body =>
      have ih := lower_validate (x :: env) (x :: env') (h.cons x) body
      simp only [lower, validateCompilationInput]
      revert ih
      cases lower (x :: env) body <;> cases validateCompilationInput (x :: env') body <;>
        simp [SameOutcome, bind, Except.bind, pure, Except.pure]
    | .App f a =>
      have ihf := lower_validate env env' h f
      have iha := lower_validate env env' h a
      simp only [lower, validateCompilationInput]
      revert ihf iha
      cases lower env f <;> cases validateCompilationInput env' f <;>
        cases lower env a <;> cases validateCompilationInput env' a <;>
        simp [SameOutcome, bind, Except.bind, pure, Except.pure]
      all_goals exact fun h _ => h
    | .Force inner =>
      have ih := lower_validate env env' h inner
      simp only [lower, validateCompilationInput]
      revert ih
      cases lower env inner <;> cases validateCompilationInput env' inner <;>
        simp [SameOutcome, bind, Except.bind, pure, Except.pure]
    | .Delay inner =>
      have ih := lower_validate env env' h inner
      simp only [lower, validateCompilationInput]
      revert ih
      cases lower env inner <;> cases validateCompilationInput env' inner <;>
        simp [SameOutcome, bind, Except.bind, pure, Except.pure]
    | .Constr tag args =>
      have ih := lowerList_validate env env' h args
      simp only [lower, validateCompilationInput]
      revert ih
      cases lowerList env args <;> cases validateCompilationList env' args <;>
        simp [SameOutcome, SameOutcomeList, bind, Except.bind, pure, Except.pure]
    | .Case scrut alts =>
      have ihs := lower_validate env env' h scrut
      have iha := lowerList_validate env env' h alts
      simp only [lower, validateCompilationInput]
      revert ihs iha
      cases lower env scrut <;> cases validateCompilationInput env' scrut <;>
        cases lowerList env alts <;> cases validateCompilationList env' alts <;>
        simp [SameOutcome, SameOutcomeList, bind, Except.bind, pure, Except.pure]
      all_goals exact fun h _ => h
    | .Let binds body =>
      simp only [lower, validateCompilationInput]
      exact lowerLet_validate env env' h binds body
    | .Fix f (.Lam x body) =>
      have hn : SameNames (x :: f :: x :: env) (x :: f :: env') := fun v => by
        simp only [List.any_cons, h v]; cases x == v <;> simp
      have ih := lower_validate (x :: f :: x :: env) (x :: f :: env') hn body
      rw [lower_fix_lam]
      simp only [validateCompilationInput]
      revert ih
      cases lower (x :: f :: x :: env) body <;> cases validateCompilationInput (x :: f :: env') body <;>
        simp [SameOutcome, Except.map]
    | .Fix f (.Var y) | .Fix f (.Lit _) | .Fix f (.Builtin _) | .Fix f .Error
    | .Fix f (.Fix _ _) | .Fix f (.App _ _) | .Fix f (.Force _) | .Fix f (.Delay _)
    | .Fix f (.Constr _ _) | .Fix f (.Case _ _) | .Fix f (.Let _ _) =>
      simp [lower, validateCompilationInput, SameOutcome, throw, throwThe, MonadExceptOf.throw]
  termination_by sizeOf e

  theorem lowerList_validate (env env' : List VarId) (h : SameNames env env') (es : List Expr) :
      SameOutcomeList (lowerList env es) (validateCompilationList env' es) := by
    match es with
    | [] => simp [lowerList, validateCompilationList, SameOutcomeList, pure, Except.pure]
    | e :: rest =>
      have ih := lower_validate env env' h e
      have ihr := lowerList_validate env env' h rest
      simp only [lowerList, validateCompilationList]
      revert ih ihr
      cases lower env e <;> cases validateCompilationInput env' e <;>
        cases lowerList env rest <;> cases validateCompilationList env' rest <;>
        simp [SameOutcome, SameOutcomeList, bind, Except.bind, pure, Except.pure]
      all_goals exact fun h _ => h
  termination_by sizeOf es

  theorem lowerLet_validate (env env' : List VarId) (h : SameNames env env')
      (binds : List (VarId × Expr × Bool)) (body : Expr) :
      SameOutcome (lowerLet env binds body) (validateCompilationBindings env' binds body) := by
    match binds with
    | [] =>
      simp only [lowerLet, validateCompilationBindings]
      exact lower_validate env env' h body
    | (x, rhs, er) :: rest =>
      have ihr := lower_validate env env' h rhs
      have ihb := lowerLet_validate (x :: env) (x :: env') (h.cons x) rest body
      simp only [lowerLet, validateCompilationBindings]
      revert ihr ihb
      cases lower env rhs <;> cases validateCompilationInput env' rhs <;>
        cases lowerLet (x :: env) rest body <;>
        cases validateCompilationBindings (x :: env') rest body <;>
        simp [SameOutcome, bind, Except.bind, pure, Except.pure]
      all_goals exact fun h _ => h
  termination_by sizeOf binds + sizeOf body
end

/-- `lowerExpr` fails exactly when input validation fails, with the same
    message; equivalently, exactly when `lowerTotalExpr` returns `none`. -/
theorem lowerExpr_validate (e : Expr) (n : Nat) :
    SameOutcome (lowerExpr e n) (validateCompilationInput [] e) :=
  lower_validate [] [] (fun _ => rfl) e

theorem validate_ok_lowerTotalExpr {e : Expr}
    (h : validateCompilationInput [] e = .ok ()) : ∃ t₀, lowerTotalExpr [] e = some t₀ := by
  have hs := lowerExpr_validate e 0
  rw [h] at hs
  cases hl : lowerExpr e 0 with
  | error _ => rw [hl] at hs; exact absurd hs id
  | ok t => obtain ⟨t₀, ht₀, _⟩ := lowerExpr_sound hl; exact ⟨t₀, ht₀⟩

theorem lowerTotalExpr_validate_ok {e : Expr} {t₀ : Term}
    (h : lowerTotalExpr [] e = some t₀) : validateCompilationInput [] e = .ok () := by
  obtain ⟨t, ht, _⟩ := lowerExpr_complete h 0
  have hs := lowerExpr_validate e 0
  rw [ht] at hs
  cases hv : validateCompilationInput [] e with
  | error _ => rw [hv] at hs; exact absurd hs id
  | ok u => cases u; rfl

/-! ## Canonical terms

Lowering emits `Lam 0` binders and never the index `0`. `canon` puts any
term into that form: binder names are erased and `Var 0`, which always
fails, becomes `Error`. -/

mutual
  def canon : Term → Term
    | .Var 0 => .Error
    | .Var (n + 1) => .Var (n + 1)
    | .Constant c => .Constant c
    | .Builtin b => .Builtin b
    | .Error => .Error
    | .Lam _ b => .Lam 0 (canon b)
    | .Apply f x => .Apply (canon f) (canon x)
    | .Delay e => .Delay (canon e)
    | .Force e => .Force (canon e)
    | .Constr tag args => .Constr tag (canonList args)
    | .Case s alts => .Case (canon s) (canonList alts)
  termination_by t => sizeOf t

  def canonList : List Term → List Term
    | [] => []
    | t :: ts => canon t :: canonList ts
  termination_by ts => sizeOf ts
end

mutual
  def Canonical : Term → Bool
    | .Var n => decide (0 < n)
    | .Lam n b => decide (n = 0) && Canonical b
    | .Apply f x => Canonical f && Canonical x
    | .Delay e => Canonical e
    | .Force e => Canonical e
    | .Constr _ args => CanonicalList args
    | .Case s alts => Canonical s && CanonicalList alts
    | .Constant _ | .Builtin _ | .Error => true
  termination_by t => sizeOf t

  def CanonicalList : List Term → Bool
    | [] => true
    | t :: ts => Canonical t && CanonicalList ts
  termination_by ts => sizeOf ts
end

mutual
  theorem canon_of_canonical : ∀ (t : Term), Canonical t = true → canon t = t
    | .Var 0, h => by simp [Canonical] at h
    | .Var (n + 1), _ => by simp [canon]
    | .Constant _, _ => by simp [canon]
    | .Builtin _, _ => by simp [canon]
    | .Error, _ => by simp [canon]
    | .Lam n b, h => by
      simp only [Canonical, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨rfl, hb⟩ := h
      simp only [canon, canon_of_canonical b hb]
    | .Apply f x, h => by
      simp only [Canonical, Bool.and_eq_true] at h
      simp only [canon, canon_of_canonical f h.1, canon_of_canonical x h.2]
    | .Delay e, h => by
      simp only [Canonical] at h; simp only [canon, canon_of_canonical e h]
    | .Force e, h => by
      simp only [Canonical] at h; simp only [canon, canon_of_canonical e h]
    | .Constr tag args, h => by
      simp only [Canonical] at h; simp only [canon, canonList_of_canonical args h]
    | .Case sc alts, h => by
      simp only [Canonical, Bool.and_eq_true] at h
      simp only [canon, canon_of_canonical sc h.1, canonList_of_canonical alts h.2]
  termination_by t => sizeOf t

  theorem canonList_of_canonical : ∀ (ts : List Term), CanonicalList ts = true → canonList ts = ts
    | [], _ => by simp [canonList]
    | t :: ts, h => by
      simp only [CanonicalList, Bool.and_eq_true] at h
      simp only [canonList, canon_of_canonical t h.1, canonList_of_canonical ts h.2]
  termination_by ts => sizeOf ts
end

mutual
  theorem canonical_renameTerm (σ : Nat → Nat) (hσ : FundamentalRefines.Is0Preserving σ) :
      ∀ (t : Term), Canonical t = true → Canonical (renameTerm σ t) = true
    | .Var n, h => by
      simp only [Canonical, decide_eq_true_eq] at h
      simp only [renameTerm, Canonical, decide_eq_true_eq]
      have := hσ.2 n h; omega
    | .Constant _, _ => by simp [renameTerm, Canonical]
    | .Builtin _, _ => by simp [renameTerm, Canonical]
    | .Error, _ => by simp [renameTerm, Canonical]
    | .Lam n b, h => by
      simp only [Canonical, Bool.and_eq_true] at h
      simp only [renameTerm, Canonical, Bool.and_eq_true]
      exact ⟨h.1, canonical_renameTerm _ (FundamentalRefines.is0preserving_lift σ) b h.2⟩
    | .Apply f x, h => by
      simp only [Canonical, Bool.and_eq_true] at h
      simp only [renameTerm, Canonical, Bool.and_eq_true]
      exact ⟨canonical_renameTerm σ hσ f h.1, canonical_renameTerm σ hσ x h.2⟩
    | .Delay e, h => by
      simp only [Canonical] at h; simp only [renameTerm, Canonical]
      exact canonical_renameTerm σ hσ e h
    | .Force e, h => by
      simp only [Canonical] at h; simp only [renameTerm, Canonical]
      exact canonical_renameTerm σ hσ e h
    | .Constr _ args, h => by
      simp only [Canonical] at h; simp only [renameTerm, Canonical]
      exact canonicalList_renameTermList σ hσ args h
    | .Case sc alts, h => by
      simp only [Canonical, Bool.and_eq_true] at h
      simp only [renameTerm, Canonical, Bool.and_eq_true]
      exact ⟨canonical_renameTerm σ hσ sc h.1, canonicalList_renameTermList σ hσ alts h.2⟩
  termination_by t => sizeOf t

  theorem canonicalList_renameTermList (σ : Nat → Nat)
      (hσ : FundamentalRefines.Is0Preserving σ) :
      ∀ (ts : List Term), CanonicalList ts = true → CanonicalList (renameTermList σ ts) = true
    | [], _ => by simp [renameTermList, CanonicalList]
    | t :: ts, h => by
      simp only [CanonicalList, Bool.and_eq_true] at h
      simp only [renameTermList, CanonicalList, Bool.and_eq_true]
      exact ⟨canonical_renameTerm σ hσ t h.1, canonicalList_renameTermList σ hσ ts h.2⟩
  termination_by ts => sizeOf ts
end

mutual
  theorem canonical_substTerm : ∀ (pos : Nat) (r : Term) (t : Term), 1 ≤ pos →
      Canonical r = true → Canonical t = true → Canonical (substTerm pos r t) = true
    | pos, r, .Var n, hpos, hr, ht => by
      simp only [Canonical, decide_eq_true_eq] at ht
      simp only [substTerm]
      by_cases hn : n = pos
      · simp [hn, hr]
      · by_cases hgt : n > pos
        · simp only [hn, hgt, if_true, if_false, Canonical, decide_eq_true_eq]; omega
        · simp only [hn, hgt, if_false, Canonical, decide_eq_true_eq]; omega
    | _, _, .Constant _, _, _, _ => by simp [substTerm, Canonical]
    | _, _, .Builtin _, _, _, _ => by simp [substTerm, Canonical]
    | _, _, .Error, _, _, _ => by simp [substTerm, Canonical]
    | pos, r, .Lam n b, hpos, hr, ht => by
      simp only [Canonical, Bool.and_eq_true] at ht
      simp only [substTerm, Canonical, Bool.and_eq_true]
      exact ⟨ht.1, canonical_substTerm (pos + 1) _ b (by omega)
        (canonical_renameTerm _ (FundamentalRefines.is0preserving_shiftRename (by omega)) r hr)
        ht.2⟩
    | pos, r, .Apply f x, hpos, hr, ht => by
      simp only [Canonical, Bool.and_eq_true] at ht
      simp only [substTerm, Canonical, Bool.and_eq_true]
      exact ⟨canonical_substTerm pos r f hpos hr ht.1, canonical_substTerm pos r x hpos hr ht.2⟩
    | pos, r, .Delay e, hpos, hr, ht => by
      simp only [Canonical] at ht; simp only [substTerm, Canonical]
      exact canonical_substTerm pos r e hpos hr ht
    | pos, r, .Force e, hpos, hr, ht => by
      simp only [Canonical] at ht; simp only [substTerm, Canonical]
      exact canonical_substTerm pos r e hpos hr ht
    | pos, r, .Constr _ args, hpos, hr, ht => by
      simp only [Canonical] at ht; simp only [substTerm, Canonical]
      exact canonicalList_substTermList pos r args hpos hr ht
    | pos, r, .Case sc alts, hpos, hr, ht => by
      simp only [Canonical, Bool.and_eq_true] at ht
      simp only [substTerm, Canonical, Bool.and_eq_true]
      exact ⟨canonical_substTerm pos r sc hpos hr ht.1,
        canonicalList_substTermList pos r alts hpos hr ht.2⟩
  termination_by _ _ t => sizeOf t

  theorem canonicalList_substTermList : ∀ (pos : Nat) (r : Term) (ts : List Term), 1 ≤ pos →
      Canonical r = true → CanonicalList ts = true →
      CanonicalList (substTermList pos r ts) = true
    | _, _, [], _, _, _ => by simp [substTermList, CanonicalList]
    | pos, r, t :: ts, hpos, hr, ht => by
      simp only [CanonicalList, Bool.and_eq_true] at ht
      simp only [substTermList, CanonicalList, Bool.and_eq_true]
      exact ⟨canonical_substTerm pos r t hpos hr ht.1,
        canonicalList_substTermList pos r ts hpos hr ht.2⟩
  termination_by _ _ ts => sizeOf ts
end

theorem canonical_fixLamWrap {B : Term} (h : Canonical B = true) :
    Canonical (fixLamWrap B) = true := by
  have hs := canonical_substTerm 2 fixSelfCall B (by omega) (by simp [fixSelfCall, Canonical]) h
  simp [fixLamWrap, Canonical, hs]

mutual
  theorem lower_canonical (env : List VarId) (e : Expr) (t : Term)
      (h : lower env e = .ok t) : Canonical t = true := by
    match e with
    | .Var x =>
      simp only [lower] at h
      cases hl : envLookupT env x <;> simp [hl] at h
      subst h; simp [Canonical]
    | .Lit (c, ty) => simp only [lower, Except.ok.injEq] at h; subst h; simp [Canonical]
    | .Builtin b => simp only [lower, Except.ok.injEq] at h; subst h; simp [Canonical]
    | .Error => simp only [lower, Except.ok.injEq] at h; subst h; simp [Canonical]
    | .Lam x body =>
      simp only [lower] at h
      cases hb : lower (x :: env) body <;>
        simp [hb, bind, Except.bind, pure, Except.pure] at h
      subst h
      simp [Canonical, lower_canonical (x :: env) body _ hb]
    | .App f a =>
      simp only [lower] at h
      cases hf : lower env f <;> cases ha : lower env a <;>
        simp [hf, ha, bind, Except.bind, pure, Except.pure] at h
      subst h
      simp [Canonical, lower_canonical env f _ hf, lower_canonical env a _ ha]
    | .Force inner =>
      simp only [lower] at h
      cases hi : lower env inner <;> simp [hi, bind, Except.bind, pure, Except.pure] at h
      subst h
      simp [Canonical, lower_canonical env inner _ hi]
    | .Delay inner =>
      simp only [lower] at h
      cases hi : lower env inner <;> simp [hi, bind, Except.bind, pure, Except.pure] at h
      subst h
      simp [Canonical, lower_canonical env inner _ hi]
    | .Constr tag args =>
      simp only [lower] at h
      cases ha : lowerList env args <;> simp [ha, bind, Except.bind, pure, Except.pure] at h
      subst h
      simp [Canonical, lowerList_canonical env args _ ha]
    | .Case scrut alts =>
      simp only [lower] at h
      cases hs : lower env scrut <;> cases ha : lowerList env alts <;>
        simp [hs, ha, bind, Except.bind, pure, Except.pure] at h
      subst h
      simp [Canonical, lower_canonical env scrut _ hs, lowerList_canonical env alts _ ha]
    | .Let binds body =>
      simp only [lower] at h
      exact lowerLet_canonical env binds body t h
    | .Fix f (.Lam x body) =>
      rw [lower_fix_lam] at h
      cases hb : lower (x :: f :: x :: env) body <;> simp [hb, Except.map] at h
      subst h
      exact canonical_fixLamWrap (lower_canonical _ body _ hb)
    | .Fix f (.Var y) | .Fix f (.Lit _) | .Fix f (.Builtin _) | .Fix f .Error
    | .Fix f (.Fix _ _) | .Fix f (.App _ _) | .Fix f (.Force _) | .Fix f (.Delay _)
    | .Fix f (.Constr _ _) | .Fix f (.Case _ _) | .Fix f (.Let _ _) =>
      simp [lower] at h
  termination_by sizeOf e

  theorem lowerList_canonical (env : List VarId) (es : List Expr) (ts : List Term)
      (h : lowerList env es = .ok ts) : CanonicalList ts = true := by
    match es with
    | [] => simp only [lowerList, Except.ok.injEq] at h; subst h; simp [CanonicalList]
    | e :: rest =>
      simp only [lowerList] at h
      cases he : lower env e <;> cases hr : lowerList env rest <;>
        simp [he, hr, bind, Except.bind, pure, Except.pure] at h
      subst h
      simp [CanonicalList, lower_canonical env e _ he, lowerList_canonical env rest _ hr]
  termination_by sizeOf es

  theorem lowerLet_canonical (env : List VarId) (binds : List (VarId × Expr × Bool))
      (body : Expr) (t : Term) (h : lowerLet env binds body = .ok t) : Canonical t = true := by
    match binds with
    | [] => simp only [lowerLet] at h; exact lower_canonical env body t h
    | (x, rhs, _) :: rest =>
      simp only [lowerLet] at h
      cases hr : lower env rhs <;> cases hb : lowerLet (x :: env) rest body <;>
        simp [hr, hb, bind, Except.bind, pure, Except.pure] at h
      subst h
      simp [Canonical, lower_canonical env rhs _ hr, lowerLet_canonical (x :: env) rest body _ hb]
  termination_by sizeOf binds + sizeOf body
end

mutual
  theorem exists_closedAt : ∀ (t : Term), ∃ d, closedAt d t = true
    | .Var n => ⟨n, by simp [closedAt]⟩
    | .Constant _ => ⟨0, by simp [closedAt]⟩
    | .Builtin _ => ⟨0, by simp [closedAt]⟩
    | .Error => ⟨0, by simp [closedAt]⟩
    | .Lam _ b => by
      obtain ⟨d, h⟩ := exists_closedAt b
      exact ⟨d, by simp only [closedAt]; exact Contextual.closedAt_mono h (by omega)⟩
    | .Apply f x => by
      obtain ⟨d₁, h₁⟩ := exists_closedAt f
      obtain ⟨d₂, h₂⟩ := exists_closedAt x
      exact ⟨max d₁ d₂, by
        simp only [closedAt, Bool.and_eq_true]
        exact ⟨Contextual.closedAt_mono h₁ (by omega), Contextual.closedAt_mono h₂ (by omega)⟩⟩
    | .Delay e => by
      obtain ⟨d, h⟩ := exists_closedAt e; exact ⟨d, by simpa [closedAt] using h⟩
    | .Force e => by
      obtain ⟨d, h⟩ := exists_closedAt e; exact ⟨d, by simpa [closedAt] using h⟩
    | .Constr _ args => by
      obtain ⟨d, h⟩ := exists_closedAtList args; exact ⟨d, by simpa [closedAt] using h⟩
    | .Case sc alts => by
      obtain ⟨d₁, h₁⟩ := exists_closedAt sc
      obtain ⟨d₂, h₂⟩ := exists_closedAtList alts
      exact ⟨max d₁ d₂, by
        simp only [closedAt, Bool.and_eq_true]
        exact ⟨Contextual.closedAt_mono h₁ (by omega), Contextual.closedAtList_mono h₂ (by omega)⟩⟩
  termination_by t => sizeOf t

  theorem exists_closedAtList : ∀ (ts : List Term), ∃ d, closedAtList d ts = true
    | [] => ⟨0, by simp [closedAtList]⟩
    | t :: ts => by
      obtain ⟨d₁, h₁⟩ := exists_closedAt t
      obtain ⟨d₂, h₂⟩ := exists_closedAtList ts
      exact ⟨max d₁ d₂, by
        simp only [closedAtList, Bool.and_eq_true]
        exact ⟨Contextual.closedAt_mono h₁ (by omega), Contextual.closedAtList_mono h₂ (by omega)⟩⟩
  termination_by ts => sizeOf ts
end

/-- Binder names carry no meaning. -/
theorem lam_name_ctxEquiv (n m : Nat) (b : Term) : CtxEquiv (.Lam n b) (.Lam m b) := by
  obtain ⟨d, hd⟩ := exists_closedAt b
  have closed : ∀ k (n m : Nat), closedAt k (.Lam n b) = true → closedAt k (.Lam m b) = true :=
    fun _ _ _ h => by simpa [closedAt] using h
  exact ⟨AdvancedRefinement.contextual_of_uniform_join (depth := d)
      (by simp only [closedAt]; exact Contextual.closedAt_mono hd (by omega))
      (fun k => closed k n m) (fun _ _ => ⟨1, 1, rfl⟩),
    AdvancedRefinement.contextual_of_uniform_join (depth := d)
      (by simp only [closedAt]; exact Contextual.closedAt_mono hd (by omega))
      (fun k => closed k m n) (fun _ _ => ⟨1, 1, rfl⟩)⟩

/-- Index `0` is never bound: looking it up fails like `Error`. -/
theorem var_zero_ctxEquiv : CtxEquiv (.Var 0) .Error := by
  have join : ∀ (ρ : CekEnv) (π : Moist.CEK.Stack),
      AdvancedRedexes.advance 1 (.compute π ρ (.Var 0)) =
        AdvancedRedexes.advance 1 (.compute π ρ .Error) := fun ρ π => by
    simp [AdvancedRedexes.advance, step, FixLowering.lookup_zero]
  exact ⟨AdvancedRefinement.contextual_of_uniform_join (depth := 0) (by simp [closedAt])
      (fun _ _ => by simp [closedAt]) (fun ρ π => ⟨1, 1, join ρ π⟩),
    AdvancedRefinement.contextual_of_uniform_join (depth := 0) (by simp [closedAt])
      (fun _ _ => by simp [closedAt]) (fun ρ π => ⟨1, 1, (join ρ π).symm⟩)⟩

mutual
  theorem canon_ctxEquiv : ∀ (t : Term), CtxEquiv t (canon t)
    | .Var 0 => by simp only [canon]; exact var_zero_ctxEquiv
    | .Var (n + 1) => by simp only [canon]; exact CtxEquiv.refl _
    | .Constant _ => by simp only [canon]; exact CtxEquiv.refl _
    | .Builtin _ => by simp only [canon]; exact CtxEquiv.refl _
    | .Error => by simp only [canon]; exact CtxEquiv.refl _
    | .Lam n b => by
      simp only [canon]
      exact ((canon_ctxEquiv b).lam n).trans (lam_name_ctxEquiv n 0 _)
    | .Apply f x => by simp only [canon]; exact (canon_ctxEquiv f).app (canon_ctxEquiv x)
    | .Delay e => by simp only [canon]; exact (canon_ctxEquiv e).delay
    | .Force e => by simp only [canon]; exact (canon_ctxEquiv e).force
    | .Constr _ args => by simp only [canon]; exact CtxEquiv.constr (canonList_ctxEquiv args)
    | .Case sc alts => by
      simp only [canon]; exact (canon_ctxEquiv sc).case (canonList_ctxEquiv alts)
  termination_by t => sizeOf t

  theorem canonList_ctxEquiv : ∀ (ts : List Term), ListRel CtxEquiv ts (canonList ts)
    | [] => by simp [canonList, ListRel]
    | t :: ts => by
      simp only [canonList, ListRel]; exact ⟨canon_ctxEquiv t, canonList_ctxEquiv ts⟩
  termination_by ts => sizeOf ts
end

/-! ## Re-lifting UPLC -/

open Moist.MIR (fromUPLC fromUPLCList liftUPLC liftedVar lowerTotalList lowerTotalLet
  fixCount fixCountList fixCountBinds)

/-- Decompiler environments: each binder is found at its own position, and all
    uids are below the next fresh uid. -/
structure LiftEnv (env : List VarId) (next : Nat) : Prop where
  lookup : ∀ (i : Nat) (h : i < env.length), envLookupT env env[i] = some i
  below : ∀ w ∈ env, w.uid < next

theorem LiftEnv.nil (next : Nat) : LiftEnv [] next :=
  ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h List.not_mem_nil⟩

theorem LiftEnv.mono {env : List VarId} {next next' : Nat} (h : LiftEnv env next)
    (hle : next ≤ next') : LiftEnv env next' :=
  ⟨h.lookup, fun w hw => Nat.lt_of_lt_of_le (h.below w hw) hle⟩

theorem LiftEnv.cons {env : List VarId} {next next' : Nat} (h : LiftEnv env next)
    (hlt : next < next') : LiftEnv (liftedVar next :: env) next' := by
  refine ⟨fun i hi => ?_, fun w hw => ?_⟩
  · match i with
    | 0 => exact Moist.MIR.envLookupT_cons_self _ env
    | j + 1 =>
      have hj : j < env.length := by simp at hi; omega
      have hne : (liftedVar next == env[j]) = false := by
        rw [Moist.MIR.VarId.beq_false_iff]
        exact Or.inr (by have := h.below env[j] (List.getElem_mem hj); simp [liftedVar]; omega)
      simp only [List.getElem_cons_succ]
      rw [Moist.MIR.envLookupT_cons_neq _ _ env hne, h.lookup j hj]; rfl
  · rcases List.mem_cons.mp hw with rfl | hw
    · simp [liftedVar]; exact hlt
    · exact Nat.lt_trans (h.below w hw) hlt

theorem fromUPLC_app_nonlam (env : List VarId) (next : Nat) (f x : Term)
    (hf : ∀ n b, f ≠ .Lam n b) :
    fromUPLC env next (.Apply f x) =
      (.App (fromUPLC env next f).1 (fromUPLC env (fromUPLC env next f).2 x).1,
       (fromUPLC env (fromUPLC env next f).2 x).2) := by
  cases f with
  | Lam n b => exact absurd rfl (hf n b)
  | _ => simp only [fromUPLC]

mutual
  theorem fromUPLC_spec : ∀ (t : Term) (env : List VarId) (next : Nat),
      closedAt env.length t = true → LiftEnv env next →
      lowerTotal env (fromUPLC env next t).1 = some (canon t) ∧
        fixCount (fromUPLC env next t).1 = 0 ∧ next ≤ (fromUPLC env next t).2
    | .Var 0, env, next, _, _ => by simp [fromUPLC, lowerTotal, canon, fixCount]
    | .Var (k + 1), env, next, ht, hl => by
      simp only [closedAt, decide_eq_true_eq] at ht
      have hk : k < env.length := by omega
      simp only [fromUPLC, List.getElem?_eq_getElem hk]
      simp [lowerTotal, hl.lookup k hk, canon, fixCount]
    | .Constant (c, ty), env, next, _, _ => by simp [fromUPLC, lowerTotal, canon, fixCount]
    | .Builtin b, env, next, _, _ => by simp [fromUPLC, lowerTotal, canon, fixCount]
    | .Error, env, next, _, _ => by simp [fromUPLC, lowerTotal, canon, fixCount]
    | .Lam n body, env, next, ht, hl => by
      simp only [closedAt] at ht
      obtain ⟨h₁, h₂, h₃⟩ := fromUPLC_spec body (liftedVar next :: env) (next + 1)
        (by simpa using ht) (hl.cons (Nat.lt_succ_self _))
      simp only [fromUPLC]
      refine ⟨?_, by simp only [fixCount]; exact h₂, by omega⟩
      simp [lowerTotal, h₁, canon]
    | .Apply f x, env, next, ht, hl => by
      simp only [closedAt, Bool.and_eq_true] at ht
      by_cases hlam : ∃ n b, f = .Lam n b
      · obtain ⟨n, b, rfl⟩ := hlam
        simp only [closedAt] at ht
        obtain ⟨a₁, a₂, a₃⟩ := fromUPLC_spec x env (next + 1) ht.2 (hl.mono (by omega))
        obtain ⟨b₁, b₂, b₃⟩ := fromUPLC_spec b (liftedVar next :: env)
          (fromUPLC env (next + 1) x).2 (by simpa using ht.1) (hl.cons (by omega))
        simp only [fromUPLC]
        refine ⟨?_, by simp only [fixCount, fixCountBinds]; omega, by omega⟩
        simp [lowerTotal, lowerTotalLet, a₁, b₁, canon]
      · have hf : ∀ n b, f ≠ .Lam n b := fun n b h => hlam ⟨n, b, h⟩
        obtain ⟨a₁, a₂, a₃⟩ := fromUPLC_spec f env next ht.1 hl
        obtain ⟨b₁, b₂, b₃⟩ := fromUPLC_spec x env (fromUPLC env next f).2 ht.2
          (hl.mono a₃)
        rw [fromUPLC_app_nonlam env next f x hf]
        refine ⟨?_, by simp only [fixCount]; omega, by simp only; omega⟩
        cases f <;> first
          | exact absurd rfl (hf _ _)
          | simp [lowerTotal, a₁, b₁, canon]
    | .Delay e, env, next, ht, hl => by
      simp only [closedAt] at ht
      obtain ⟨h₁, h₂, h₃⟩ := fromUPLC_spec e env next ht hl
      simp only [fromUPLC]
      exact ⟨by simp [lowerTotal, h₁, canon], by simp only [fixCount]; exact h₂, h₃⟩
    | .Force e, env, next, ht, hl => by
      simp only [closedAt] at ht
      obtain ⟨h₁, h₂, h₃⟩ := fromUPLC_spec e env next ht hl
      simp only [fromUPLC]
      exact ⟨by simp [lowerTotal, h₁, canon], by simp only [fixCount]; exact h₂, h₃⟩
    | .Constr tag args, env, next, ht, hl => by
      simp only [closedAt] at ht
      obtain ⟨h₁, h₂, h₃⟩ := fromUPLCList_spec args env next ht hl
      simp only [fromUPLC]
      exact ⟨by simp [lowerTotal, h₁, canon], by simp only [fixCount]; exact h₂, h₃⟩
    | .Case sc alts, env, next, ht, hl => by
      simp only [closedAt, Bool.and_eq_true] at ht
      obtain ⟨a₁, a₂, a₃⟩ := fromUPLC_spec sc env next ht.1 hl
      obtain ⟨b₁, b₂, b₃⟩ := fromUPLCList_spec alts env (fromUPLC env next sc).2 ht.2
        (hl.mono a₃)
      simp only [fromUPLC]
      refine ⟨?_, by simp only [fixCount]; omega, by omega⟩
      simp [lowerTotal, a₁, b₁, canon]
  termination_by t => sizeOf t

  theorem fromUPLCList_spec : ∀ (ts : List Term) (env : List VarId) (next : Nat),
      closedAtList env.length ts = true → LiftEnv env next →
      lowerTotalList env (fromUPLCList env next ts).1 = some (canonList ts) ∧
        fixCountList (fromUPLCList env next ts).1 = 0 ∧ next ≤ (fromUPLCList env next ts).2
    | [], env, next, _, _ => by simp [fromUPLCList, lowerTotalList, canonList, fixCountList]
    | t :: ts, env, next, ht, hl => by
      simp only [closedAtList, Bool.and_eq_true] at ht
      obtain ⟨a₁, a₂, a₃⟩ := fromUPLC_spec t env next ht.1 hl
      obtain ⟨b₁, b₂, b₃⟩ := fromUPLCList_spec ts env (fromUPLC env next t).2 ht.2
        (hl.mono a₃)
      simp only [fromUPLCList]
      refine ⟨?_, by simp only [fixCountList]; omega, by omega⟩
      simp [lowerTotalList, a₁, b₁, canonList]
  termination_by ts => sizeOf ts
end

/-- **(b)** Lowering a lifted closed UPLC term gives back the term up to
    binder names and the failing index `0`. -/
theorem liftUPLC_lowerTotal (t : Term) (n : Nat) (h : closedAt 0 t = true) :
    lowerTotalExpr [] (liftUPLC t n) = some (canon t) := by
  obtain ⟨h₁, h₂, _⟩ := fromUPLC_spec t [] n h (LiftEnv.nil n)
  simp only [liftUPLC, lowerTotalExpr, Moist.MIR.expandFix_id _ h₂]
  exact h₁

theorem liftUPLC_refines (t : Term) (n : Nat) (h : closedAt 0 t = true) :
    ∃ t', lowerTotalExpr [] (liftUPLC t n) = some t' ∧ CtxRefines t t' ∧ CtxRefines t' t :=
  ⟨canon t, liftUPLC_lowerTotal t n h, (canon_ctxEquiv t).1, (canon_ctxEquiv t).2⟩

/-- Production lowering output is a fixed point of lifting and lowering. -/
theorem liftUPLC_lowerExpr {e : Expr} {m : Nat} {t : Term} (h : lowerExpr e m = .ok t)
    (n : Nat) : lowerTotalExpr [] (liftUPLC t n) = some t := by
  obtain ⟨t₀, ht₀, h₁, _⟩ := lowerExpr_sound h
  have hc₀ : closedAt 0 t₀ = true := by simpa using lowerTotalExpr_closedAt ht₀
  rw [liftUPLC_lowerTotal t n (closedAt_of_ctxRefines h₁ hc₀),
    canon_of_canonical t (lower_canonical [] e t h)]

end Moist.Verified.LoweringSoundness
