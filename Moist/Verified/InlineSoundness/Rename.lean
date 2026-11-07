import Moist.Verified.MIR
import Moist.MIR.Optimize.Inline

/-! # Lowering is insensitive to fresh renaming

`lowerTotalExpr` maps names to de Bruijn indices, so it only depends on how
the environment resolves the variables of the expression
(`lowerTotalExpr_agree`), and renaming a binder to a name that does not occur
in its scope does not change the lowering (`lowerTotalExpr_rename`). These are
what make the capture-avoiding branches of `subst` invisible after lowering. -/

namespace Moist.Verified.InlineSoundness.Rename

open Moist.MIR
open Moist.Plutus.Term (Term)
open Moist.Verified.MIR (lowerTotalExprList lowerTotalExprList_nil lowerTotalExprList_cons
  lowerTotalExpr_lam lowerTotalExpr_app lowerTotalExpr_force lowerTotalExpr_delay
  lowerTotalExpr_constr_of_list lowerTotalExpr_case_of_list)

/-! ## Structural lowering equations -/

theorem lowerTotalExpr_var (env : List VarId) (x : VarId) :
    lowerTotalExpr env (.Var x) = (envLookupT env x).map (fun i => .Var (i + 1)) := by
  simp only [lowerTotalExpr, expandFix, lowerTotal]
  cases envLookupT env x <;> rfl

theorem lowerTotalExpr_let_nil (env : List VarId) (body : Expr) :
    lowerTotalExpr env (.Let [] body) = lowerTotalExpr env body := by
  simp only [lowerTotalExpr, expandFix, expandFixBinds, lowerTotal, lowerTotalLet]

theorem lowerTotalExpr_let_cons (env : List VarId) (x : VarId) (rhs : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) :
    lowerTotalExpr env (.Let ((x, rhs, er) :: rest) body) = (do
      let r ← lowerTotalExpr env rhs
      let b ← lowerTotalExpr (x :: env) (.Let rest body)
      some (Term.Apply (.Lam 0 b) r)) := by
  simp only [lowerTotalExpr, expandFix, expandFixBinds, lowerTotal, lowerTotalLet,
    Option.bind_eq_bind]

theorem lowerTotalExpr_fix_nonlam (env : List VarId) (f : VarId) (body : Expr)
    (h : ∀ x inner, body ≠ .Lam x inner) : lowerTotalExpr env (.Fix f body) = none := by
  cases body with
  | Lam x inner => exact absurd rfl (h x inner)
  | _ => simp [lowerTotalExpr, expandFix, lowerTotal]

/-- A recursive lambda lowers through its body under any name for the
    self-application binder that is fresh for the body. -/
theorem lowerTotalExpr_fix_lam (env : List VarId) (f x : VarId) (inner : Expr)
    (s : VarId) (fresh : maxUidExpr (expandFix inner) < s.uid) :
    lowerTotalExpr env (.Fix f (.Lam x inner)) =
      (lowerTotalExpr (x :: f :: s :: env) inner).map fixLamWrapUplc :=
  lowerTotalExpr_fix_lam_with_fresh env f x inner s (maxUidExpr_fresh _ s fresh)

/-! ## Environment agreement -/

private theorem lookup_cons_agree {l₁ l₂ : List VarId} {z : VarId} (y : VarId)
    (h : envLookupT l₁ z = envLookupT l₂ z) :
    envLookupT (y :: l₁) z = envLookupT (y :: l₂) z := by
  cases hyz : (y == z) with
  | true => simp [envLookupT, envLookupT.go, hyz]
  | false => rw [envLookupT_cons_neq y z l₁ hyz, envLookupT_cons_neq y z l₂ hyz, h]

/-- Lookups that skip the two candidates for one position agree. -/
theorem lookup_middle_agree (ys : List VarId) (a b z : VarId) (Q : List VarId)
    (ha : (a == z) = false) (hb : (b == z) = false) :
    envLookupT (ys ++ a :: Q) z = envLookupT (ys ++ b :: Q) z := by
  induction ys with
  | nil => simp only [List.nil_append]; rw [envLookupT_cons_neq a z Q ha, envLookupT_cons_neq b z Q hb]
  | cons y ys ih => exact lookup_cons_agree y ih

theorem maxUid_let_cons (x : VarId) (rhs : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) :
    maxUidExpr (.Let ((x, rhs, er) :: rest) body) =
      max x.uid (max (maxUidExpr rhs) (maxUidExpr (.Let rest body))) := by
  simp only [maxUidExpr, maxUidExprBinds]; omega

theorem maxUid_list_cons (e : Expr) (es : List Expr) :
    maxUidExprList (e :: es) = max (maxUidExpr e) (maxUidExprList es) := by
  simp only [maxUidExprList]

mutual
  /-- Lowering only depends on how the environment resolves the variables of
      the expression. -/
  theorem lowerTotalExpr_agree : ∀ (e : Expr) (l₁ l₂ : List VarId),
      (∀ z : VarId, z.uid ≤ maxUidExpr e → envLookupT l₁ z = envLookupT l₂ z) →
      lowerTotalExpr l₁ e = lowerTotalExpr l₂ e
    | .Var x, l₁, l₂, h => by
      rw [lowerTotalExpr_var, lowerTotalExpr_var, h x (by simp [maxUidExpr])]
    | .Lit (_, _), _, _, _ | .Builtin _, _, _, _ | .Error, _, _, _ => by
      simp [lowerTotalExpr, expandFix, lowerTotal]
    | .Lam x body, l₁, l₂, h => by
      rw [lowerTotalExpr_lam, lowerTotalExpr_lam, lowerTotalExpr_agree body (x :: l₁) (x :: l₂)
        fun z hz => lookup_cons_agree x (h z (by simp only [maxUidExpr]; omega))]
    | .Fix f body, l₁, l₂, h => by
      cases body with
      | Lam x inner =>
        let s : VarId := ⟨maxUidExpr (expandFix inner) + 1, .gen, "s"⟩
        rw [lowerTotalExpr_fix_lam l₁ f x inner s (Nat.lt_succ_self _),
          lowerTotalExpr_fix_lam l₂ f x inner s (Nat.lt_succ_self _),
          lowerTotalExpr_agree inner (x :: f :: s :: l₁) (x :: f :: s :: l₂)
            fun z hz => lookup_cons_agree x <| lookup_cons_agree f <| lookup_cons_agree s <|
              h z (by simp only [maxUidExpr]; omega)]
      | _ => simp [lowerTotalExpr, expandFix, lowerTotal]
    | .App f a, l₁, l₂, h => by
      rw [lowerTotalExpr_app, lowerTotalExpr_app,
        lowerTotalExpr_agree f l₁ l₂ fun z hz => h z (by simp only [maxUidExpr]; omega),
        lowerTotalExpr_agree a l₁ l₂ fun z hz => h z (by simp only [maxUidExpr]; omega)]
    | .Force e, l₁, l₂, h => by
      rw [lowerTotalExpr_force, lowerTotalExpr_force,
        lowerTotalExpr_agree e l₁ l₂ fun z hz => h z (by simpa only [maxUidExpr] using hz)]
    | .Delay e, l₁, l₂, h => by
      rw [lowerTotalExpr_delay, lowerTotalExpr_delay,
        lowerTotalExpr_agree e l₁ l₂ fun z hz => h z (by simpa only [maxUidExpr] using hz)]
    | .Constr tag args, l₁, l₂, h => by
      rw [lowerTotalExpr_constr_of_list, lowerTotalExpr_constr_of_list,
        lowerTotalExprList_agree args l₁ l₂ fun z hz => h z (by simpa only [maxUidExpr] using hz)]
    | .Case scrut alts, l₁, l₂, h => by
      rw [lowerTotalExpr_case_of_list, lowerTotalExpr_case_of_list,
        lowerTotalExpr_agree scrut l₁ l₂ fun z hz => h z (by simp only [maxUidExpr]; omega),
        lowerTotalExprList_agree alts l₁ l₂ fun z hz => h z (by simp only [maxUidExpr]; omega)]
    | .Let [] body, l₁, l₂, h => by
      rw [lowerTotalExpr_let_nil, lowerTotalExpr_let_nil,
        lowerTotalExpr_agree body l₁ l₂ fun z hz => h z (by simp only [maxUidExpr, maxUidExprBinds]; omega)]
    | .Let ((x, rhs, er) :: rest) body, l₁, l₂, h => by
      have bound := maxUid_let_cons x rhs er rest body
      rw [lowerTotalExpr_let_cons, lowerTotalExpr_let_cons,
        lowerTotalExpr_agree rhs l₁ l₂ fun z hz => h z (by omega),
        lowerTotalExpr_agree (.Let rest body) (x :: l₁) (x :: l₂)
          fun z hz => lookup_cons_agree x (h z (by omega))]
  termination_by e => sizeOf e

  theorem lowerTotalExprList_agree : ∀ (es : List Expr) (l₁ l₂ : List VarId),
      (∀ z : VarId, z.uid ≤ maxUidExprList es → envLookupT l₁ z = envLookupT l₂ z) →
      lowerTotalExprList l₁ es = lowerTotalExprList l₂ es
    | [], l₁, l₂, _ => by rw [lowerTotalExprList_nil, lowerTotalExprList_nil]
    | e :: es, l₁, l₂, h => by
      rw [lowerTotalExprList_cons, lowerTotalExprList_cons,
        lowerTotalExpr_agree e l₁ l₂ fun z hz => h z (by rw [maxUid_list_cons]; omega),
        lowerTotalExprList_agree es l₁ l₂ fun z hz => h z (by rw [maxUid_list_cons]; omega)]
  termination_by es => sizeOf es
end

/-! ## Fresh renaming -/

theorem beq_false_of_uid {a b : VarId} (h : a.uid ≠ b.uid) : (a == b) = false :=
  (VarId.beq_false_iff a b).mpr (.inr h)

theorem beq_comm {a b : VarId} : (a == b) = (b == a) := by
  cases h : (a == b) <;> cases h' : (b == a) <;> try rfl
  · have := (VarId.beq_true_iff b a).mp h'
    rw [(VarId.beq_true_iff a b).mpr ⟨this.1.symm, this.2.symm⟩] at h; cases h
  · have := (VarId.beq_true_iff a b).mp h
    rw [(VarId.beq_true_iff b a).mpr ⟨this.1.symm, this.2.symm⟩] at h'; cases h'

theorem beq_false_of_beq {a b c : VarId} (hab : (a == b) = true) (hac : (a == c) = false) :
    (b == c) = false := by
  cases h : (b == c)
  · rfl
  · rw [VarId.beq_trans a b c hab h] at hac; cases hac

/-- The middle binder resolves every name equal to it. -/
theorem lookup_at_middle (ys : List VarId) (a z : VarId) (Q : List VarId)
    (haz : (a == z) = true) (hys : ∀ y ∈ ys, (y == z) = false) :
    envLookupT (ys ++ a :: Q) z = some ys.length := by
  induction ys with
  | nil => simp [envLookupT, envLookupT.go, haz]
  | cons y ys ih =>
    rw [List.cons_append, envLookupT_cons_neq y z _ (hys y (.head _)),
      ih fun y' hy' => hys y' (.tail _ hy')]
    rfl

/-- Under a binder equal to the renamed name, both environments agree. -/
private theorem shadow_agree (ys Q : List VarId) (x x' y z : VarId) (hyx : (y == x) = true)
    (hz : z.uid < x'.uid) :
    envLookupT (y :: (ys ++ x' :: Q)) z = envLookupT (y :: (ys ++ x :: Q)) z := by
  cases hyz : (y == z) with
  | true => simp [envLookupT, envLookupT.go, hyz]
  | false =>
    rw [envLookupT_cons_neq y z _ hyz, envLookupT_cons_neq y z _ hyz,
      lookup_middle_agree ys x' x z Q (beq_false_of_uid (by omega))
        (beq_false_of_beq hyx hyz)]

private theorem rename_let (x x' : VarId) (binds : List (VarId × Expr × Bool)) (body : Expr) :
    rename x x' (.Let binds body) =
      .Let (renameLet x x' binds body).1 (renameLet x x' binds body).2 := by
  simp only [rename]

private theorem renameLet_cons (x x' y : VarId) (rhs : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) :
    renameLet x x' ((y, rhs, er) :: rest) body =
      if (y == x) = true then ((y, rename x x' rhs, er) :: rest, body)
      else ((y, rename x x' rhs, er) :: (renameLet x x' rest body).1,
        (renameLet x x' rest body).2) := by
  rw [renameLet]

mutual
  /-- Renaming `x` to a name `x'` that is fresh for the expression and is not
      shadowed by `ys` leaves the lowering unchanged. -/
  theorem lowerTotalExpr_rename (x x' : VarId) : ∀ (e : Expr) (ys Q : List VarId),
      maxUidExpr e < x'.uid → (∀ y ∈ ys, (y == x) = false ∧ (y == x') = false) →
      lowerTotalExpr (ys ++ x' :: Q) (rename x x' e) = lowerTotalExpr (ys ++ x :: Q) e
    | .Var z, ys, Q, fresh, hys => by
      simp only [maxUidExpr] at fresh
      simp only [rename]
      split
      · rename_i hzx
        rw [lowerTotalExpr_var, lowerTotalExpr_var,
          lookup_at_middle ys x' x' Q ((VarId.beq_true_iff _ _).mpr ⟨rfl, rfl⟩) fun y hy => (hys y hy).2,
          lookup_at_middle ys x z Q (by rw [beq_comm]; exact hzx) fun y hy => by
            rw [beq_comm]
            exact beq_false_of_beq (by rw [beq_comm]; exact hzx) (by rw [beq_comm]; exact (hys y hy).1)]
      · rename_i hzx
        rw [lowerTotalExpr_var, lowerTotalExpr_var,
          lookup_middle_agree ys x' x z Q (beq_false_of_uid (by omega)) (by
            rw [beq_comm]; simpa using hzx)]
    | .Lit (_, _), _, _, _, _ | .Builtin _, _, _, _, _ | .Error, _, _, _, _ => by
      simp [rename, lowerTotalExpr, expandFix, lowerTotal]
    | .Lam y body, ys, Q, fresh, hys => by
      simp only [maxUidExpr] at fresh
      simp only [rename]
      split
      · rename_i hyx
        rw [lowerTotalExpr_lam, lowerTotalExpr_lam, lowerTotalExpr_agree body _ _ fun z hz =>
          shadow_agree ys Q x x' y z hyx (by omega)]
      · rename_i hyx
        rw [lowerTotalExpr_lam, lowerTotalExpr_lam]
        have := lowerTotalExpr_rename x x' body (y :: ys) Q (by omega) fun y' hy' => by
          cases hy' with
          | head => exact ⟨by simpa using hyx, beq_false_of_uid (by omega)⟩
          | tail _ hy' => exact hys y' hy'
        rw [List.cons_append, List.cons_append] at this
        rw [this]
    | .Fix f body, ys, Q, fresh, hys => by
      simp only [maxUidExpr] at fresh
      cases body with
      | Lam p inner =>
        simp only [maxUidExpr] at fresh
        let s : VarId := ⟨maxUidExpr (expandFix inner) + maxUidExpr (expandFix (rename x x' inner)) +
          x.uid + x'.uid + 1, .gen, "s"⟩
        have sFresh₁ : maxUidExpr (expandFix inner) < s.uid := by simp only [s]; omega
        have sFresh₂ : maxUidExpr (expandFix (rename x x' inner)) < s.uid := by simp only [s]; omega
        simp only [rename]
        split
        · rename_i hfx
          rw [lowerTotalExpr_fix_lam _ f p inner s sFresh₁, lowerTotalExpr_fix_lam _ f p inner s sFresh₁,
            lowerTotalExpr_agree inner _ _ fun z hz => ?_]
          apply lookup_cons_agree
          cases hfz : (f == z) with
          | true => simp [envLookupT, envLookupT.go, hfz]
          | false =>
            rw [envLookupT_cons_neq f z _ hfz, envLookupT_cons_neq f z _ hfz]
            exact congrArg _ (lookup_cons_agree s (lookup_middle_agree ys x' x z Q
              (beq_false_of_uid (by omega)) (beq_false_of_beq hfx hfz)))
        · rename_i hfx
          split
          · rename_i hpx
            rw [lowerTotalExpr_fix_lam _ f p inner s sFresh₁, lowerTotalExpr_fix_lam _ f p inner s sFresh₁,
              lowerTotalExpr_agree inner _ _ fun z hz => ?_]
            cases hpz : (p == z) with
            | true => simp [envLookupT, envLookupT.go, hpz]
            | false =>
              rw [envLookupT_cons_neq p z _ hpz, envLookupT_cons_neq p z _ hpz]
              exact congrArg _ (lookup_cons_agree f (lookup_cons_agree s (lookup_middle_agree ys x' x z Q
                (beq_false_of_uid (by omega)) (beq_false_of_beq hpx hpz))))
          · rename_i hpx
            rw [lowerTotalExpr_fix_lam _ f p _ s sFresh₂, lowerTotalExpr_fix_lam _ f p inner s sFresh₁]
            have := lowerTotalExpr_rename x x' inner (p :: f :: s :: ys) Q (by omega) fun y hy => by
              cases hy with
              | head => exact ⟨by simpa using hpx, beq_false_of_uid (by omega)⟩
              | tail _ hy =>
                cases hy with
                | head => exact ⟨by simpa using hfx, beq_false_of_uid (by omega)⟩
                | tail _ hy =>
                  cases hy with
                  | head => exact ⟨beq_false_of_uid (by simp only [s]; omega),
                      beq_false_of_uid (by simp only [s]; omega)⟩
                  | tail _ hy => exact hys y hy
            simp only [List.cons_append] at this
            rw [this]
      | _ =>
        simp only [rename]
        split <;> (try split) <;> simp [lowerTotalExpr, expandFix, lowerTotal]
    | .App f a, ys, Q, fresh, hys => by
      simp only [maxUidExpr] at fresh
      simp only [rename]
      rw [lowerTotalExpr_app, lowerTotalExpr_app,
        lowerTotalExpr_rename x x' f ys Q (by omega) hys,
        lowerTotalExpr_rename x x' a ys Q (by omega) hys]
    | .Force e, ys, Q, fresh, hys => by
      simp only [maxUidExpr] at fresh
      simp only [rename]
      rw [lowerTotalExpr_force, lowerTotalExpr_force, lowerTotalExpr_rename x x' e ys Q fresh hys]
    | .Delay e, ys, Q, fresh, hys => by
      simp only [maxUidExpr] at fresh
      simp only [rename]
      rw [lowerTotalExpr_delay, lowerTotalExpr_delay, lowerTotalExpr_rename x x' e ys Q fresh hys]
    | .Constr tag args, ys, Q, fresh, hys => by
      simp only [maxUidExpr] at fresh
      simp only [rename]
      rw [lowerTotalExpr_constr_of_list, lowerTotalExpr_constr_of_list,
        lowerTotalExprList_rename x x' args ys Q fresh hys]
    | .Case scrut alts, ys, Q, fresh, hys => by
      simp only [maxUidExpr] at fresh
      simp only [rename]
      rw [lowerTotalExpr_case_of_list, lowerTotalExpr_case_of_list,
        lowerTotalExpr_rename x x' scrut ys Q (by omega) hys,
        lowerTotalExprList_rename x x' alts ys Q (by omega) hys]
    | .Let binds body, ys, Q, fresh, hys => by
      rw [rename_let]
      exact lowerTotalExprLet_rename x x' binds body ys Q fresh hys
  termination_by e => sizeOf e

  theorem lowerTotalExprList_rename (x x' : VarId) : ∀ (es : List Expr) (ys Q : List VarId),
      maxUidExprList es < x'.uid → (∀ y ∈ ys, (y == x) = false ∧ (y == x') = false) →
      lowerTotalExprList (ys ++ x' :: Q) (renameList x x' es) = lowerTotalExprList (ys ++ x :: Q) es
    | [], _, _, _, _ => by simp only [renameList]; rw [lowerTotalExprList_nil, lowerTotalExprList_nil]
    | e :: es, ys, Q, fresh, hys => by
      rw [maxUid_list_cons] at fresh
      simp only [renameList]
      rw [lowerTotalExprList_cons, lowerTotalExprList_cons,
        lowerTotalExpr_rename x x' e ys Q (by omega) hys,
        lowerTotalExprList_rename x x' es ys Q (by omega) hys]
  termination_by es => sizeOf es

  theorem lowerTotalExprLet_rename (x x' : VarId) :
      ∀ (binds : List (VarId × Expr × Bool)) (body : Expr) (ys Q : List VarId),
      maxUidExpr (.Let binds body) < x'.uid → (∀ y ∈ ys, (y == x) = false ∧ (y == x') = false) →
      lowerTotalExpr (ys ++ x' :: Q)
          (.Let (renameLet x x' binds body).1 (renameLet x x' binds body).2) =
        lowerTotalExpr (ys ++ x :: Q) (.Let binds body)
    | [], body, ys, Q, fresh, hys => by
      simp only [renameLet]
      rw [lowerTotalExpr_let_nil, lowerTotalExpr_let_nil,
        lowerTotalExpr_rename x x' body ys Q (by simp only [maxUidExpr, maxUidExprBinds] at fresh; omega) hys]
    | (y, rhs, er) :: rest, body, ys, Q, fresh, hys => by
      rw [maxUid_let_cons] at fresh
      rw [renameLet_cons]
      split
      · rename_i hyx
        simp only
        rw [lowerTotalExpr_let_cons, lowerTotalExpr_let_cons,
          lowerTotalExpr_rename x x' rhs ys Q (by omega) hys,
          lowerTotalExpr_agree (.Let rest body) _ _ fun z hz => shadow_agree ys Q x x' y z hyx (by omega)]
      · rename_i hyx
        rw [lowerTotalExpr_let_cons, lowerTotalExpr_let_cons,
          lowerTotalExpr_rename x x' rhs ys Q (by omega) hys]
        have := lowerTotalExprLet_rename x x' rest body (y :: ys) Q (by omega) fun y' hy' => by
          cases hy' with
          | head => exact ⟨by simpa using hyx, beq_false_of_uid (by omega)⟩
          | tail _ hy' => exact hys y' hy'
        simp only [List.cons_append] at this
        rw [this]
  termination_by binds body => sizeOf binds + sizeOf body
end

end Moist.Verified.InlineSoundness.Rename
