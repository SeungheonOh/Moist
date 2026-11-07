import Moist.Verified.InlineSoundness.Rename
import Moist.MIR.Optimize.CSE

/-! # Lowering a merged variable

CSE drops `let v = rhs` and renames `v` to an earlier `w` in the rest of the
block. When `w` is not rebound there, lowering the renamed block is the
lowering of the original block (with `v` bound) followed by the de Bruijn
renaming that sends `v` to `w` and closes the gap left by `v`
(`lowerTotalExpr_merge`). -/

namespace Moist.Verified.CSE

open Moist.MIR
open Moist.Plutus.Term (Term)
open Moist.Verified (renameTerm renameTermList liftRename)
open Moist.Verified.MIR (lowerTotalExprList lowerTotalExprList_nil lowerTotalExprList_cons
  lowerTotalExpr_lam lowerTotalExpr_app lowerTotalExpr_force lowerTotalExpr_delay
  lowerTotalExpr_constr_of_list lowerTotalExpr_case_of_list)
open Moist.Verified.InlineSoundness.Rename (lowerTotalExpr_var lowerTotalExpr_let_nil
  lowerTotalExpr_let_cons lowerTotalExpr_fix_lam beq_false_of_uid beq_comm beq_false_of_beq)

/-! ## Environment renamings -/

/-- `z` resolves in `E₂` at the position `τ` sends its `E₁` position to. -/
def LookupRename (τ : Nat → Nat) (E₁ E₂ : List VarId) (z : VarId) : Prop :=
  (envLookupT E₂ z).map (· + 1) = (envLookupT E₁ z).map (fun n => τ (n + 1))

theorem envLookupT_cons_self' {y z : VarId} (E : List VarId) (h : (y == z) = true) :
    envLookupT (y :: E) z = some 0 := by
  simp [envLookupT, envLookupT.go, h]

theorem lookupRename_cons {τ : Nat → Nat} {E₁ E₂ : List VarId} (y z : VarId)
    (h : (y == z) = false → LookupRename τ E₁ E₂ z) :
    LookupRename (liftRename τ) (y :: E₁) (y :: E₂) z := by
  cases hyz : (y == z) with
  | true =>
    simp only [LookupRename, envLookupT_cons_self' E₁ hyz, envLookupT_cons_self' E₂ hyz]
    rfl
  | false =>
    have h' := h hyz
    simp only [LookupRename] at h' ⊢
    rw [envLookupT_cons_neq y z _ hyz, envLookupT_cons_neq y z _ hyz]
    cases h₁ : envLookupT E₁ z <;> cases h₂ : envLookupT E₂ z <;>
      simp_all [liftRename]

theorem envLookupT_go_beq {x v : VarId} (h : (x == v) = true) :
    ∀ (E : List VarId) (n : Nat), envLookupT.go x E n = envLookupT.go v E n := by
  intro E
  induction E with
  | nil => intro n; rfl
  | cons y rest ih =>
    intro n
    simp only [envLookupT.go]
    cases hyx : (y == x) with
    | true => rw [VarId.beq_trans y x v hyx h]; rfl
    | false =>
      have hyv : (y == v) = false := by
        cases hyv : (y == v)
        · rfl
        · rw [VarId.beq_trans y v x hyv (by rw [beq_comm]; exact h)] at hyx; cases hyx
      rw [hyv]
      exact ih (n + 1)

theorem envLookupT_beq {x v : VarId} (h : (x == v) = true) (E : List VarId) :
    envLookupT E x = envLookupT E v :=
  envLookupT_go_beq h E 0

theorem renameTerm_fixLamWrapUplc (τ : Nat → Nat) (t : Term) :
    renameTerm τ (fixLamWrapUplc t) =
      fixLamWrapUplc (renameTerm (liftRename (liftRename (liftRename τ))) t) := by
  simp [fixLamWrapUplc, renameTerm, liftRename]

/-! ## Lowering in renamed environments -/

mutual
  theorem lowerTotalExpr_renameEnv (τ : Nat → Nat) : ∀ (e : Expr) (E₁ E₂ : List VarId),
      (∀ z, LookupRename τ E₁ E₂ z) →
      lowerTotalExpr E₂ e = (lowerTotalExpr E₁ e).map (renameTerm τ)
    | .Var x, E₁, E₂, h => by
      have hx := h x
      simp only [LookupRename] at hx
      rw [lowerTotalExpr_var, lowerTotalExpr_var]
      cases h₁ : envLookupT E₁ x <;> cases h₂ : envLookupT E₂ x <;> simp_all [renameTerm]
    | .Lit (_, _), _, _, _ | .Builtin _, _, _, _ | .Error, _, _, _ => by
      simp [lowerTotalExpr, expandFix, lowerTotal, renameTerm]
    | .Lam x body, E₁, E₂, h => by
      rw [lowerTotalExpr_lam, lowerTotalExpr_lam,
        lowerTotalExpr_renameEnv (liftRename τ) body (x :: E₁) (x :: E₂)
          fun z => lookupRename_cons x z fun _ => h z]
      cases lowerTotalExpr (x :: E₁) body <;> simp [renameTerm]
    | .Fix f body, E₁, E₂, h => by
      cases body with
      | Lam p inner =>
        let s : VarId := ⟨maxUidExpr (expandFix inner) + 1, .gen, "s"⟩
        rw [lowerTotalExpr_fix_lam E₁ f p inner s (Nat.lt_succ_self _),
          lowerTotalExpr_fix_lam E₂ f p inner s (Nat.lt_succ_self _),
          lowerTotalExpr_renameEnv _ inner (p :: f :: s :: E₁) (p :: f :: s :: E₂)
            fun z => lookupRename_cons p z fun _ => lookupRename_cons f z fun _ =>
              lookupRename_cons s z fun _ => h z]
        cases lowerTotalExpr (p :: f :: s :: E₁) inner <;> simp [renameTerm_fixLamWrapUplc]
      | _ => simp [lowerTotalExpr, expandFix, lowerTotal]
    | .App f a, E₁, E₂, h => by
      rw [lowerTotalExpr_app, lowerTotalExpr_app, lowerTotalExpr_renameEnv τ f E₁ E₂ h,
        lowerTotalExpr_renameEnv τ a E₁ E₂ h]
      cases lowerTotalExpr E₁ f <;> cases lowerTotalExpr E₁ a <;> simp [renameTerm]
    | .Force e, E₁, E₂, h => by
      rw [lowerTotalExpr_force, lowerTotalExpr_force, lowerTotalExpr_renameEnv τ e E₁ E₂ h]
      cases lowerTotalExpr E₁ e <;> simp [renameTerm]
    | .Delay e, E₁, E₂, h => by
      rw [lowerTotalExpr_delay, lowerTotalExpr_delay, lowerTotalExpr_renameEnv τ e E₁ E₂ h]
      cases lowerTotalExpr E₁ e <;> simp [renameTerm]
    | .Constr tag args, E₁, E₂, h => by
      rw [lowerTotalExpr_constr_of_list, lowerTotalExpr_constr_of_list,
        lowerTotalExprList_renameEnv τ args E₁ E₂ h]
      cases lowerTotalExprList E₁ args <;> simp [renameTerm]
    | .Case scrut alts, E₁, E₂, h => by
      rw [lowerTotalExpr_case_of_list, lowerTotalExpr_case_of_list,
        lowerTotalExpr_renameEnv τ scrut E₁ E₂ h, lowerTotalExprList_renameEnv τ alts E₁ E₂ h]
      cases lowerTotalExpr E₁ scrut <;> cases lowerTotalExprList E₁ alts <;> simp [renameTerm]
    | .Let [] body, E₁, E₂, h => by
      rw [lowerTotalExpr_let_nil, lowerTotalExpr_let_nil, lowerTotalExpr_renameEnv τ body E₁ E₂ h]
    | .Let ((x, rhs, er) :: rest) body, E₁, E₂, h => by
      rw [lowerTotalExpr_let_cons, lowerTotalExpr_let_cons,
        lowerTotalExpr_renameEnv τ rhs E₁ E₂ h,
        lowerTotalExpr_renameEnv (liftRename τ) (.Let rest body) (x :: E₁) (x :: E₂)
          fun z => lookupRename_cons x z fun _ => h z]
      cases lowerTotalExpr E₁ rhs <;> cases lowerTotalExpr (x :: E₁) (.Let rest body) <;>
        simp [renameTerm]
  termination_by e => sizeOf e

  theorem lowerTotalExprList_renameEnv (τ : Nat → Nat) : ∀ (es : List Expr) (E₁ E₂ : List VarId),
      (∀ z, LookupRename τ E₁ E₂ z) →
      lowerTotalExprList E₂ es = (lowerTotalExprList E₁ es).map (renameTermList τ)
    | [], _, _, _ => by rw [lowerTotalExprList_nil, lowerTotalExprList_nil]; rfl
    | e :: es, E₁, E₂, h => by
      rw [lowerTotalExprList_cons, lowerTotalExprList_cons, lowerTotalExpr_renameEnv τ e E₁ E₂ h,
        lowerTotalExprList_renameEnv τ es E₁ E₂ h]
      cases lowerTotalExpr E₁ e <;> cases lowerTotalExprList E₁ es <;> simp [renameTermList]
  termination_by es => sizeOf es
end

/-! ## Merging `v` into `w` -/

/-- `E₂` resolves every variable but `v` as `τ` says, and resolves `w` where
    `τ` sends `v`. -/
def MergeEnv (v w : VarId) (τ : Nat → Nat) (E₁ E₂ : List VarId) : Prop :=
  (∀ z, (z == v) = false → LookupRename τ E₁ E₂ z) ∧
    (envLookupT E₂ w).map (· + 1) = (envLookupT E₁ v).map (fun n => τ (n + 1))

theorem MergeEnv.cons {v w y : VarId} {τ : Nat → Nat} {E₁ E₂ : List VarId}
    (h : MergeEnv v w τ E₁ E₂) (hyv : (y == v) = false) (hyw : (y == w) = false) :
    MergeEnv v w (liftRename τ) (y :: E₁) (y :: E₂) := by
  refine ⟨fun z hz => lookupRename_cons y z fun _ => h.1 z hz, ?_⟩
  have h₂ := h.2
  rw [envLookupT_cons_neq y w _ hyw, envLookupT_cons_neq y v _ hyv]
  cases h₁ : envLookupT E₁ v <;> cases h₃ : envLookupT E₂ w <;> simp_all [liftRename]

theorem MergeEnv.shadow {v w y : VarId} {τ : Nat → Nat} {E₁ E₂ : List VarId}
    (h : MergeEnv v w τ E₁ E₂) (hyv : (y == v) = true) :
    ∀ z, LookupRename (liftRename τ) (y :: E₁) (y :: E₂) z :=
  fun z => lookupRename_cons y z fun hyz => h.1 z (by rw [beq_comm]; exact beq_false_of_beq hyv hyz)

private theorem rename_let (v w : VarId) (binds : List (VarId × Expr × Bool)) (body : Expr) :
    rename v w (.Let binds body) =
      .Let (renameLet v w binds body).1 (renameLet v w binds body).2 := by
  simp only [rename]

private theorem renameLet_cons (v w y : VarId) (rhs : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) :
    renameLet v w ((y, rhs, er) :: rest) body =
      if (y == v) = true then ((y, rename v w rhs, er) :: rest, body)
      else ((y, rename v w rhs, er) :: (renameLet v w rest body).1,
        (renameLet v w rest body).2) := by
  rw [renameLet]

private theorem or_false {a b : Bool} (h : (a || b) = false) : a = false ∧ b = false := by
  cases a <;> cases b <;> simp_all

theorem lowerTotalExpr_var_rename {τ : Nat → Nat} {E₁ E₂ : List VarId} {x : VarId}
    (hx : LookupRename τ E₁ E₂ x) :
    lowerTotalExpr E₂ (.Var x) = (lowerTotalExpr E₁ (.Var x)).map (renameTerm τ) := by
  simp only [LookupRename] at hx
  rw [lowerTotalExpr_var, lowerTotalExpr_var]
  cases h₁ : envLookupT E₁ x <;> cases h₂ : envLookupT E₂ x <;> simp_all [renameTerm]

mutual
  theorem lowerTotalExpr_merge (v w : VarId) (τ : Nat → Nat) : ∀ (e : Expr) (E₁ E₂ : List VarId),
      bindsVar w e = false → MergeEnv v w τ E₁ E₂ →
      lowerTotalExpr E₂ (rename v w e) = (lowerTotalExpr E₁ e).map (renameTerm τ)
    | .Var x, E₁, E₂, _, h => by
      simp only [rename]
      split
      · rename_i hxv
        have h₂ := h.2
        rw [lowerTotalExpr_var, lowerTotalExpr_var, envLookupT_beq hxv E₁]
        cases h₁ : envLookupT E₁ v <;> cases h₃ : envLookupT E₂ w <;> simp_all [renameTerm]
      · rename_i hxv
        exact lowerTotalExpr_var_rename (h.1 x (by simpa using hxv))
    | .Lit (_, _), _, _, _, _ | .Builtin _, _, _, _, _ | .Error, _, _, _, _ => by
      simp [rename, lowerTotalExpr, expandFix, lowerTotal, renameTerm]
    | .Lam y body, E₁, E₂, hw, h => by
      simp only [bindsVar] at hw
      have ⟨hyw, hbody⟩ := or_false hw
      simp only [rename]
      split
      · rename_i hyv
        rw [lowerTotalExpr_lam, lowerTotalExpr_lam,
          lowerTotalExpr_renameEnv (liftRename τ) body (y :: E₁) (y :: E₂) (h.shadow hyv)]
        cases lowerTotalExpr (y :: E₁) body <;> simp [renameTerm]
      · rename_i hyv
        rw [lowerTotalExpr_lam, lowerTotalExpr_lam,
          lowerTotalExpr_merge v w (liftRename τ) body (y :: E₁) (y :: E₂) hbody
            (h.cons (by simpa using hyv) hyw)]
        cases lowerTotalExpr (y :: E₁) body <;> simp [renameTerm]
    | .Fix f body, E₁, E₂, hw, h => by
      simp only [bindsVar] at hw
      have ⟨hfw, hbody⟩ := or_false hw
      cases body with
      | Lam p inner =>
        simp only [bindsVar] at hbody
        have ⟨hpw, hinner⟩ := or_false hbody
        let s : VarId := ⟨maxUidExpr (expandFix inner) + maxUidExpr (expandFix (rename v w inner)) +
          v.uid + w.uid + 1, .gen, "s"⟩
        have sFresh₁ : maxUidExpr (expandFix inner) < s.uid := by simp only [s]; omega
        have sFresh₂ : maxUidExpr (expandFix (rename v w inner)) < s.uid := by simp only [s]; omega
        have hsv : (s == v) = false := beq_false_of_uid (by simp only [s]; omega)
        have hsw : (s == w) = false := beq_false_of_uid (by simp only [s]; omega)
        simp only [rename]
        split
        · rename_i hfv
          rw [lowerTotalExpr_fix_lam E₁ f p inner s sFresh₁, lowerTotalExpr_fix_lam E₂ f p inner s sFresh₁,
            lowerTotalExpr_renameEnv _ inner (p :: f :: s :: E₁) (p :: f :: s :: E₂)
              fun z => lookupRename_cons p z fun _ => lookupRename_cons f z fun hfz =>
                lookupRename_cons s z fun _ =>
                  h.1 z (by rw [beq_comm]; exact beq_false_of_beq hfv hfz)]
          cases lowerTotalExpr (p :: f :: s :: E₁) inner <;> simp [renameTerm_fixLamWrapUplc]
        · rename_i hfv
          split
          · rename_i hpv
            rw [lowerTotalExpr_fix_lam E₁ f p inner s sFresh₁,
              lowerTotalExpr_fix_lam E₂ f p inner s sFresh₁,
              lowerTotalExpr_renameEnv _ inner (p :: f :: s :: E₁) (p :: f :: s :: E₂)
                fun z => lookupRename_cons p z fun hpz => lookupRename_cons f z fun _ =>
                  lookupRename_cons s z fun _ =>
                    h.1 z (by rw [beq_comm]; exact beq_false_of_beq hpv hpz)]
            cases lowerTotalExpr (p :: f :: s :: E₁) inner <;> simp [renameTerm_fixLamWrapUplc]
          · rename_i hpv
            rw [lowerTotalExpr_fix_lam E₁ f p inner s sFresh₁,
              lowerTotalExpr_fix_lam E₂ f p _ s sFresh₂,
              lowerTotalExpr_merge v w _ inner (p :: f :: s :: E₁) (p :: f :: s :: E₂) hinner
                (((h.cons hsv hsw).cons (by simpa using hfv) hfw).cons (by simpa using hpv) hpw)]
            cases lowerTotalExpr (p :: f :: s :: E₁) inner <;> simp [renameTerm_fixLamWrapUplc]
      | _ =>
        simp only [rename]
        split <;> (try split) <;> simp [lowerTotalExpr, expandFix, lowerTotal]
    | .App f a, E₁, E₂, hw, h => by
      simp only [bindsVar] at hw
      have ⟨hf, ha⟩ := or_false hw
      simp only [rename]
      rw [lowerTotalExpr_app, lowerTotalExpr_app, lowerTotalExpr_merge v w τ f E₁ E₂ hf h,
        lowerTotalExpr_merge v w τ a E₁ E₂ ha h]
      cases lowerTotalExpr E₁ f <;> cases lowerTotalExpr E₁ a <;> simp [renameTerm]
    | .Force e, E₁, E₂, hw, h => by
      simp only [bindsVar] at hw
      simp only [rename]
      rw [lowerTotalExpr_force, lowerTotalExpr_force, lowerTotalExpr_merge v w τ e E₁ E₂ hw h]
      cases lowerTotalExpr E₁ e <;> simp [renameTerm]
    | .Delay e, E₁, E₂, hw, h => by
      simp only [bindsVar] at hw
      simp only [rename]
      rw [lowerTotalExpr_delay, lowerTotalExpr_delay, lowerTotalExpr_merge v w τ e E₁ E₂ hw h]
      cases lowerTotalExpr E₁ e <;> simp [renameTerm]
    | .Constr tag args, E₁, E₂, hw, h => by
      simp only [bindsVar] at hw
      simp only [rename]
      rw [lowerTotalExpr_constr_of_list, lowerTotalExpr_constr_of_list,
        lowerTotalExprList_merge v w τ args E₁ E₂ hw h]
      cases lowerTotalExprList E₁ args <;> simp [renameTerm]
    | .Case scrut alts, E₁, E₂, hw, h => by
      simp only [bindsVar] at hw
      have ⟨hs, ha⟩ := or_false hw
      simp only [rename]
      rw [lowerTotalExpr_case_of_list, lowerTotalExpr_case_of_list,
        lowerTotalExpr_merge v w τ scrut E₁ E₂ hs h, lowerTotalExprList_merge v w τ alts E₁ E₂ ha h]
      cases lowerTotalExpr E₁ scrut <;> cases lowerTotalExprList E₁ alts <;> simp [renameTerm]
    | .Let binds body, E₁, E₂, hw, h => by
      simp only [bindsVar] at hw
      rw [rename_let]
      exact lowerTotalExprLet_merge v w τ binds body E₁ E₂ hw h
  termination_by e => sizeOf e

  theorem lowerTotalExprList_merge (v w : VarId) (τ : Nat → Nat) :
      ∀ (es : List Expr) (E₁ E₂ : List VarId), bindsVarList w es = false → MergeEnv v w τ E₁ E₂ →
      lowerTotalExprList E₂ (renameList v w es) = (lowerTotalExprList E₁ es).map (renameTermList τ)
    | [], _, _, _, _ => by simp only [renameList]; rw [lowerTotalExprList_nil, lowerTotalExprList_nil]; rfl
    | e :: es, E₁, E₂, hw, h => by
      simp only [bindsVarList] at hw
      have ⟨he, hes⟩ := or_false hw
      simp only [renameList]
      rw [lowerTotalExprList_cons, lowerTotalExprList_cons, lowerTotalExpr_merge v w τ e E₁ E₂ he h,
        lowerTotalExprList_merge v w τ es E₁ E₂ hes h]
      cases lowerTotalExpr E₁ e <;> cases lowerTotalExprList E₁ es <;> simp [renameTermList]
  termination_by es => sizeOf es

  theorem lowerTotalExprLet_merge (v w : VarId) (τ : Nat → Nat) :
      ∀ (binds : List (VarId × Expr × Bool)) (body : Expr) (E₁ E₂ : List VarId),
      bindsVarLet w binds body = false → MergeEnv v w τ E₁ E₂ →
      lowerTotalExpr E₂ (.Let (renameLet v w binds body).1 (renameLet v w binds body).2) =
        (lowerTotalExpr E₁ (.Let binds body)).map (renameTerm τ)
    | [], body, E₁, E₂, hw, h => by
      simp only [bindsVarLet] at hw
      simp only [renameLet]
      rw [lowerTotalExpr_let_nil, lowerTotalExpr_let_nil, lowerTotalExpr_merge v w τ body E₁ E₂ hw h]
    | (y, rhs, er) :: rest, body, E₁, E₂, hw, h => by
      simp only [bindsVarLet] at hw
      have ⟨hyrhs, hrest⟩ := or_false hw
      have ⟨hyw, hrhs⟩ := or_false hyrhs
      rw [renameLet_cons]
      split
      · rename_i hyv
        simp only
        rw [lowerTotalExpr_let_cons, lowerTotalExpr_let_cons, lowerTotalExpr_merge v w τ rhs E₁ E₂ hrhs h,
          lowerTotalExpr_renameEnv (liftRename τ) (.Let rest body) (y :: E₁) (y :: E₂) (h.shadow hyv)]
        cases lowerTotalExpr E₁ rhs <;> cases lowerTotalExpr (y :: E₁) (.Let rest body) <;>
          simp [renameTerm]
      · rename_i hyv
        rw [lowerTotalExpr_let_cons, lowerTotalExpr_let_cons, lowerTotalExpr_merge v w τ rhs E₁ E₂ hrhs h,
          lowerTotalExprLet_merge v w (liftRename τ) rest body (y :: E₁) (y :: E₂) hrest
            (h.cons (by simpa using hyv) hyw)]
        cases lowerTotalExpr E₁ rhs <;> cases lowerTotalExpr (y :: E₁) (.Let rest body) <;>
          simp [renameTerm]
  termination_by binds body => sizeOf binds + sizeOf body
end

end Moist.Verified.CSE
