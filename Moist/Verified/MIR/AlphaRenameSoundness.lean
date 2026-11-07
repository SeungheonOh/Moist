import Moist.MIR.AlphaRename
import Moist.MIR.LowerTotal
import Moist.Verified.Definitions.MIR
import Moist.Verified.MIR.Congruence

/-! # Alpha-renaming preserves lowering

`alphaRenameTop e K` renames every `let` binder of `e` to a fresh uid
(numbered from `K`, above `maxUidExpr e`). Lowering only looks at binding
positions, so the result lowers exactly like `e`
(`alphaRenameTop_lowerTotalExpr_eq`, for `Fix`-free `e`). -/

namespace Moist.Verified.MIR

open Moist.MIR

/-! ## Substitutions -/

theorem substLookup_cons (old new : VarId) (rest : List (VarId × VarId)) (v : VarId) :
    substLookup ((old, new) :: rest) v = if (old == v) = true then new else substLookup rest v :=
  rfl

theorem substShadow_cons (old new : VarId) (rest : List (VarId × VarId)) (v : VarId) :
    substShadow ((old, new) :: rest) v =
      if (old == v) = true then substShadow rest v else (old, new) :: substShadow rest v :=
  rfl

theorem substShadow_mem_iff {σ : List (VarId × VarId)} {v : VarId} {p : VarId × VarId} :
    p ∈ substShadow σ v ↔ p ∈ σ ∧ (p.1 == v) = false := by
  induction σ with
  | nil => simp [substShadow]
  | cons q rest ih =>
    obtain ⟨old, new⟩ := q
    rw [substShadow_cons]
    by_cases hov : (old == v) = true
    · rw [if_pos hov, ih, List.mem_cons]
      constructor
      · exact fun ⟨hm, hne⟩ => ⟨.inr hm, hne⟩
      · rintro ⟨rfl | hm, hne⟩
        · rw [hov] at hne; cases hne
        · exact ⟨hm, hne⟩
    · rw [if_neg hov, List.mem_cons, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨hm, hne⟩)
        · exact ⟨.inl rfl, by simpa using hov⟩
        · exact ⟨.inr hm, hne⟩
      · rintro ⟨rfl | hm, hne⟩
        · exact .inl rfl
        · exact .inr ⟨hm, hne⟩

theorem substLookup_identity_of_no_match (σ : List (VarId × VarId)) (w : VarId)
    (hnone : ∀ p ∈ σ, (p.1 == w) = false) : substLookup σ w = w := by
  induction σ with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨old, new⟩ := p
    rw [substLookup_cons, if_neg (by simp [hnone _ List.mem_cons_self])]
    exact ih fun q hq => hnone q (List.mem_cons_of_mem _ hq)

theorem substLookup_result_in_image_or_self (σ : List (VarId × VarId)) (w : VarId) :
    substLookup σ w = w ∨ ∃ p ∈ σ, substLookup σ w = p.2 := by
  induction σ with
  | nil => exact .inl rfl
  | cons p rest ih =>
    obtain ⟨old, new⟩ := p
    rw [substLookup_cons]
    split
    · exact .inr ⟨(old, new), List.mem_cons_self, rfl⟩
    · rcases ih with heq | ⟨q, hq, hqeq⟩
      · exact .inl heq
      · exact .inr ⟨q, List.mem_cons_of_mem _ hq, hqeq⟩

theorem substLookup_substShadow_neq (σ : List (VarId × VarId)) (v w : VarId)
    (h : (v == w) = false) : substLookup (substShadow σ v) w = substLookup σ w := by
  induction σ with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨old, new⟩ := p
    rw [substShadow_cons, substLookup_cons]
    by_cases hov : (old == v) = true
    · have how : ¬(old == w) = true := fun how => by
        rw [VarId.beq_true_iff] at hov how
        have := (VarId.beq_true_iff v w).mpr ⟨hov.1.symm.trans how.1, hov.2.symm.trans how.2⟩
        rw [h] at this; cases this
      rw [if_pos hov, if_neg how, ih]
    · rw [if_neg hov, substLookup_cons, ih]

theorem envLookupT_cons_same_uid (v w : VarId) (env : List VarId)
    (ho : v.origin = w.origin) (h : v.uid = w.uid) : envLookupT (v :: env) w = some 0 := by
  show (if (v == w) = true then some 0 else envLookupT.go w env (0 + 1)) = some 0
  rw [if_pos ((VarId.beq_true_iff v w).mpr ⟨ho, h⟩)]

/-! ## Unfolding -/

section
variable (σ : List (VarId × VarId)) (s : FreshState)

private theorem alphaRename_lam_eq (v : VarId) (body : Expr) :
    alphaRename σ (.Lam v body) s =
      (.Lam v (alphaRename (substShadow σ v) body s).1, (alphaRename (substShadow σ v) body s).2) :=
  rfl

private theorem alphaRename_fix_eq (v : VarId) (body : Expr) :
    alphaRename σ (.Fix v body) s =
      (.Fix v (alphaRename (substShadow σ v) body s).1, (alphaRename (substShadow σ v) body s).2) :=
  rfl

private theorem alphaRename_app_eq (f x : Expr) :
    alphaRename σ (.App f x) s =
      (.App (alphaRename σ f s).1 (alphaRename σ x (alphaRename σ f s).2).1,
       (alphaRename σ x (alphaRename σ f s).2).2) := rfl

private theorem alphaRename_case_eq (scrut : Expr) (alts : List Expr) :
    alphaRename σ (.Case scrut alts) s =
      (.Case (alphaRename σ scrut s).1 (alphaRenameList σ alts (alphaRename σ scrut s).2).1,
       (alphaRenameList σ alts (alphaRename σ scrut s).2).2) := rfl

private theorem alphaRename_let_eq (binds : List (VarId × Expr × Bool)) (body : Expr) :
    alphaRename σ (.Let binds body) s =
      (.Let (alphaRenameBinds σ binds s).1.1
        (alphaRename (alphaRenameBinds σ binds s).1.2 body (alphaRenameBinds σ binds s).2).1,
       (alphaRename (alphaRenameBinds σ binds s).1.2 body (alphaRenameBinds σ binds s).2).2) := rfl

private theorem alphaRenameList_cons_eq (e : Expr) (rest : List Expr) :
    alphaRenameList σ (e :: rest) s =
      ((alphaRename σ e s).1 :: (alphaRenameList σ rest (alphaRename σ e s).2).1,
       (alphaRenameList σ rest (alphaRename σ e s).2).2) := rfl

/-- The binder `v` is renamed to `fresh σ rhs s v`. -/
private abbrev fresh (rhs : Expr) (v : VarId) : VarId :=
  ⟨(alphaRename σ rhs s).2.next, .gen, v.hint⟩

private theorem alphaRenameBinds_cons_eq (v : VarId) (rhs : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) :
    alphaRenameBinds σ ((v, rhs, er) :: rest) s =
      let r := alphaRenameBinds ((v, fresh σ s rhs v) :: σ) rest ⟨(alphaRename σ rhs s).2.next + 1⟩
      (((fresh σ s rhs v, (alphaRename σ rhs s).1, er) :: r.1.1, r.1.2), r.2) := rfl

end

/-! ## Lowering is preserved -/

/-- `env1` and `env2` agree on every `w` with `w.uid ≤ B`, up to `σ`. -/
private def Compat (σ : List (VarId × VarId)) (env1 env2 : List VarId) (B : Nat) : Prop :=
  ∀ w, w.uid ≤ B → envLookupT env1 w = envLookupT env2 (substLookup σ w)

/-- Renamed-to uids lie strictly between `B` and `s.next`. -/
private def SubstFreshAbove (σ : List (VarId × VarId)) (s : FreshState) (B : Nat) : Prop :=
  ∀ p ∈ σ, B < p.2.uid ∧ p.2.uid < s.next

private theorem SubstFreshAbove.mono {σ : List (VarId × VarId)} {s s' : FreshState} {B : Nat}
    (h : SubstFreshAbove σ s B) (hs : s.next ≤ s'.next) : SubstFreshAbove σ s' B :=
  fun p hp => ⟨(h p hp).1, Nat.lt_of_lt_of_le (h p hp).2 hs⟩

/-- `Compat` under a `Lam`/`Fix` binder, which is kept but shadows `σ`. -/
private theorem Compat_lam (σ : List (VarId × VarId)) (env1 env2 : List VarId) (B : Nat)
    (v : VarId) (hv : v.uid ≤ B) (hcompat : Compat σ env1 env2 B)
    (hsubst_lo : ∀ p ∈ σ, B < p.2.uid) :
    Compat (substShadow σ v) (v :: env1) (v :: env2) B := by
  intro w hw
  by_cases hvw : (v == w) = true
  · have ⟨ho, hu⟩ := (VarId.beq_true_iff v w).mp hvw
    have hshad : substLookup (substShadow σ v) w = w := by
      apply substLookup_identity_of_no_match
      intro q hq
      rw [substShadow_mem_iff] at hq
      cases hqw : (q.1 == w)
      · rfl
      · have ⟨ho', hu'⟩ := (VarId.beq_true_iff q.1 w).mp hqw
        have := (VarId.beq_true_iff q.1 v).mpr ⟨ho'.trans ho.symm, hu'.trans hu.symm⟩
        rw [this] at hq; cases hq.2
    rw [envLookupT_cons_same_uid v w env1 ho hu, hshad, envLookupT_cons_same_uid v w env2 ho hu]
  · have hvw : (v == w) = false := by simpa using hvw
    have hv_ne : (v == substLookup σ w) = false := by
      rcases substLookup_result_in_image_or_self σ w with heq | ⟨p, hp, hpeq⟩
      · rw [heq]; exact hvw
      · rw [hpeq, VarId.beq_false_iff]; have := hsubst_lo p hp; omega
    rw [envLookupT_cons_neq v w env1 hvw, substLookup_substShadow_neq σ v w hvw,
      envLookupT_cons_neq v _ env2 hv_ne, hcompat w hw]

/-- `Compat` under a `Let` binder, renamed from `v` to a fresh `v'`. -/
private theorem Compat_let (σ : List (VarId × VarId)) (env1 env2 : List VarId) (B : Nat)
    (s : FreshState) (hs : B < s.next) (v v' : VarId) (hv'_uid : v'.uid = s.next)
    (hcompat : Compat σ env1 env2 B) (hsubst : SubstFreshAbove σ s B) :
    Compat ((v, v') :: σ) (v :: env1) (v' :: env2) B := by
  intro w hw
  rw [substLookup_cons]
  by_cases hvw : (v == w) = true
  · have ⟨ho, hu⟩ := (VarId.beq_true_iff v w).mp hvw
    rw [if_pos hvw, envLookupT_cons_same_uid v w env1 ho hu,
      envLookupT_cons_same_uid v' v' env2 rfl rfl]
  · have hvw : (v == w) = false := by simpa using hvw
    have hv'_ne : (v' == substLookup σ w) = false := by
      rw [VarId.beq_false_iff]; refine .inr ?_
      rcases substLookup_result_in_image_or_self σ w with heq | ⟨p, hp, hpeq⟩
      · rw [heq]; omega
      · rw [hpeq]; have := (hsubst p hp).2; omega
    rw [if_neg (by simp [hvw]), envLookupT_cons_neq v w env1 hvw,
      envLookupT_cons_neq v' _ env2 hv'_ne, hcompat w hw]

mutual

theorem alphaRename_lowerTotal_eq (B : Nat) (e : Expr) (σ : List (VarId × VarId))
    (s : FreshState) (env1 env2 : List VarId) (he : maxUidExpr e ≤ B) (hs : B < s.next)
    (hsubst : SubstFreshAbove σ s B) (hcompat : Compat σ env1 env2 B) :
    lowerTotal env1 e = lowerTotal env2 (alphaRename σ e s).1 ∧
    s.next ≤ (alphaRename σ e s).2.next := by
  have hlo : ∀ p ∈ σ, B < p.2.uid := fun p hp => (hsubst p hp).1
  match e with
  | .Var v =>
    simp only [maxUidExpr] at he
    refine ⟨?_, Nat.le_refl _⟩
    show lowerTotal env1 (.Var v) = lowerTotal env2 (.Var (substLookup σ v))
    simp only [lowerTotal, hcompat v he]
  | .Lit (c, ty) =>
    exact ⟨by show lowerTotal env1 (.Lit (c, ty)) = lowerTotal env2 (.Lit (c, ty)); simp [lowerTotal],
      Nat.le_refl _⟩
  | .Builtin b =>
    exact ⟨by show lowerTotal env1 (.Builtin b) = lowerTotal env2 (.Builtin b); simp [lowerTotal],
      Nat.le_refl _⟩
  | .Error =>
    exact ⟨by show lowerTotal env1 .Error = lowerTotal env2 .Error; simp [lowerTotal], Nat.le_refl _⟩
  | .Lam v body =>
    simp only [maxUidExpr] at he
    rw [alphaRename_lam_eq]
    have ⟨ih, hm⟩ := alphaRename_lowerTotal_eq B body (substShadow σ v) s (v :: env1) (v :: env2)
      (by omega) hs (fun p hp => hsubst p (substShadow_mem_iff.mp hp).1)
      (Compat_lam σ env1 env2 B v (by omega) hcompat hlo)
    exact ⟨by simp only [lowerTotal, ih], hm⟩
  | .Fix v body =>
    simp only [maxUidExpr] at he
    rw [alphaRename_fix_eq]
    have ⟨_, hm⟩ := alphaRename_lowerTotal_eq B body (substShadow σ v) s (v :: env1) (v :: env2)
      (by omega) hs (fun p hp => hsubst p (substShadow_mem_iff.mp hp).1)
      (Compat_lam σ env1 env2 B v (by omega) hcompat hlo)
    exact ⟨by simp only [lowerTotal], hm⟩
  | .App f x =>
    simp only [maxUidExpr] at he
    rw [alphaRename_app_eq]
    have ⟨ihf, hmf⟩ := alphaRename_lowerTotal_eq B f σ s env1 env2 (by omega) hs hsubst hcompat
    have ⟨ihx, hmx⟩ := alphaRename_lowerTotal_eq B x σ _ env1 env2 (by omega) (by omega)
      (hsubst.mono hmf) hcompat
    exact ⟨by simp only [lowerTotal, ihf, ihx], Nat.le_trans hmf hmx⟩
  | .Force e =>
    simp only [maxUidExpr] at he
    have ⟨ih, hm⟩ := alphaRename_lowerTotal_eq B e σ s env1 env2 he hs hsubst hcompat
    exact ⟨by show _ = lowerTotal env2 (.Force _); simp only [lowerTotal, ih], hm⟩
  | .Delay e =>
    simp only [maxUidExpr] at he
    have ⟨ih, hm⟩ := alphaRename_lowerTotal_eq B e σ s env1 env2 he hs hsubst hcompat
    exact ⟨by show _ = lowerTotal env2 (.Delay _); simp only [lowerTotal, ih], hm⟩
  | .Constr tag args =>
    simp only [maxUidExpr] at he
    have ⟨ih, hm⟩ := alphaRenameList_lowerTotalList_eq B args σ s env1 env2 he hs hsubst hcompat
    exact ⟨by show _ = lowerTotal env2 (.Constr tag _); simp only [lowerTotal, ih], hm⟩
  | .Case scrut alts =>
    simp only [maxUidExpr] at he
    rw [alphaRename_case_eq]
    have ⟨ihs, hms⟩ := alphaRename_lowerTotal_eq B scrut σ s env1 env2 (by omega) hs hsubst hcompat
    have ⟨iha, hma⟩ := alphaRenameList_lowerTotalList_eq B alts σ _ env1 env2 (by omega)
      (by omega) (hsubst.mono hms) hcompat
    exact ⟨by simp only [lowerTotal, ihs, iha], Nat.le_trans hms hma⟩
  | .Let binds body =>
    simp only [maxUidExpr] at he
    rw [alphaRename_let_eq]
    have ⟨ih, hm⟩ := alphaRenameBinds_lowerTotalLet_eq B binds body σ s env1 env2 (by omega)
      (by omega) hs hsubst hcompat
    exact ⟨by simp only [lowerTotal, ih], hm⟩
termination_by sizeOf e

theorem alphaRenameList_lowerTotalList_eq (B : Nat) (es : List Expr) (σ : List (VarId × VarId))
    (s : FreshState) (env1 env2 : List VarId) (he : maxUidExprList es ≤ B) (hs : B < s.next)
    (hsubst : SubstFreshAbove σ s B) (hcompat : Compat σ env1 env2 B) :
    lowerTotalList env1 es = lowerTotalList env2 (alphaRenameList σ es s).1 ∧
    s.next ≤ (alphaRenameList σ es s).2.next := by
  match es with
  | [] =>
    exact ⟨by show lowerTotalList env1 [] = lowerTotalList env2 []; simp [lowerTotalList],
      Nat.le_refl _⟩
  | e :: rest =>
    simp only [maxUidExprList] at he
    rw [alphaRenameList_cons_eq]
    have ⟨ihe, hme⟩ := alphaRename_lowerTotal_eq B e σ s env1 env2 (by omega) hs hsubst hcompat
    have ⟨ihr, hmr⟩ := alphaRenameList_lowerTotalList_eq B rest σ _ env1 env2 (by omega)
      (by omega) (hsubst.mono hme) hcompat
    exact ⟨by simp only [lowerTotalList, ihe, ihr], Nat.le_trans hme hmr⟩
termination_by sizeOf es

/-- `body` is renamed under the substitution produced by the bindings. -/
theorem alphaRenameBinds_lowerTotalLet_eq (B : Nat) (binds : List (VarId × Expr × Bool))
    (body : Expr) (σ : List (VarId × VarId)) (s : FreshState) (env1 env2 : List VarId)
    (hb : maxUidExprBinds binds ≤ B) (hbody : maxUidExpr body ≤ B) (hs : B < s.next)
    (hsubst : SubstFreshAbove σ s B) (hcompat : Compat σ env1 env2 B) :
    lowerTotalLet env1 binds body =
      lowerTotalLet env2 (alphaRenameBinds σ binds s).1.1
        (alphaRename (alphaRenameBinds σ binds s).1.2 body (alphaRenameBinds σ binds s).2).1 ∧
    s.next ≤ (alphaRename (alphaRenameBinds σ binds s).1.2 body
      (alphaRenameBinds σ binds s).2).2.next := by
  match binds with
  | [] =>
    have ⟨ih, hm⟩ := alphaRename_lowerTotal_eq B body σ s env1 env2 hbody hs hsubst hcompat
    exact ⟨by
      show lowerTotalLet env1 [] body = lowerTotalLet env2 [] (alphaRename σ body s).1
      simp only [lowerTotalLet, ih], hm⟩
  | (v, rhs, er) :: rest =>
    simp only [maxUidExprBinds] at hb
    rw [alphaRenameBinds_cons_eq]; dsimp only
    have ⟨ihr, hmr⟩ := alphaRename_lowerTotal_eq B rhs σ s env1 env2 (by omega) hs hsubst hcompat
    have ⟨ih, hm⟩ := alphaRenameBinds_lowerTotalLet_eq B rest body
      ((v, fresh σ s rhs v) :: σ) ⟨(alphaRename σ rhs s).2.next + 1⟩ (v :: env1)
      (fresh σ s rhs v :: env2) (by omega) hbody (by show B < _ + 1; omega)
      (fun q hq => by
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨by show B < (alphaRename σ rhs s).2.next; omega, Nat.lt_succ_self _⟩
        · exact ⟨(hsubst q hq).1, by show _ < _ + 1; have := (hsubst q hq).2; omega⟩)
      (Compat_let σ env1 env2 B (alphaRename σ rhs s).2 (by omega) v _ rfl hcompat
        (hsubst.mono hmr))
    exact ⟨by simp only [lowerTotalLet, ihr, ih],
      Nat.le_trans hmr (Nat.le_trans (Nat.le_succ _) hm)⟩
termination_by sizeOf binds + sizeOf body

end

/-! ## `Fix`-freedom is preserved -/

mutual

theorem alphaRename_fixCount_zero (σ : List (VarId × VarId)) (e : Expr) (s : FreshState)
    (hfc : fixCount e = 0) : fixCount (alphaRename σ e s).1 = 0 := by
  match e with
  | .Var _ | .Lit _ | .Builtin _ | .Error => simp [alphaRename, pure, StateT.pure, fixCount]
  | .Lam v body =>
    simp only [fixCount] at hfc
    rw [alphaRename_lam_eq]; simp only [fixCount]
    exact alphaRename_fixCount_zero _ body s hfc
  | .Fix _ _ => simp only [fixCount] at hfc; omega
  | .App f x =>
    simp only [fixCount] at hfc
    rw [alphaRename_app_eq]; simp only [fixCount]
    have := alphaRename_fixCount_zero σ f s (by omega)
    have := alphaRename_fixCount_zero σ x (alphaRename σ f s).2 (by omega)
    omega
  | .Force e =>
    simp only [fixCount] at hfc
    show fixCount (.Force _) = 0; simp only [fixCount]
    exact alphaRename_fixCount_zero σ e s hfc
  | .Delay e =>
    simp only [fixCount] at hfc
    show fixCount (.Delay _) = 0; simp only [fixCount]
    exact alphaRename_fixCount_zero σ e s hfc
  | .Constr tag args =>
    simp only [fixCount] at hfc
    show fixCount (.Constr tag _) = 0; simp only [fixCount]
    exact alphaRenameList_fixCountList_zero σ args s hfc
  | .Case scrut alts =>
    simp only [fixCount] at hfc
    rw [alphaRename_case_eq]; simp only [fixCount]
    have := alphaRename_fixCount_zero σ scrut s (by omega)
    have := alphaRenameList_fixCountList_zero σ alts (alphaRename σ scrut s).2 (by omega)
    omega
  | .Let binds body =>
    simp only [fixCount] at hfc
    rw [alphaRename_let_eq]; simp only [fixCount]
    have := alphaRenameBinds_fixCountBinds_zero σ binds s (by omega)
    have := alphaRename_fixCount_zero (alphaRenameBinds σ binds s).1.2 body
      (alphaRenameBinds σ binds s).2 (by omega)
    omega
termination_by sizeOf e

theorem alphaRenameList_fixCountList_zero (σ : List (VarId × VarId)) (es : List Expr)
    (s : FreshState) (hfc : fixCountList es = 0) :
    fixCountList (alphaRenameList σ es s).1 = 0 := by
  match es with
  | [] => exact hfc
  | e :: rest =>
    simp only [fixCountList] at hfc
    rw [alphaRenameList_cons_eq]; simp only [fixCountList]
    have := alphaRename_fixCount_zero σ e s (by omega)
    have := alphaRenameList_fixCountList_zero σ rest (alphaRename σ e s).2 (by omega)
    omega
termination_by sizeOf es

theorem alphaRenameBinds_fixCountBinds_zero (σ : List (VarId × VarId))
    (binds : List (VarId × Expr × Bool)) (s : FreshState) (hfc : fixCountBinds binds = 0) :
    fixCountBinds (alphaRenameBinds σ binds s).1.1 = 0 := by
  match binds with
  | [] => exact hfc
  | (v, rhs, er) :: rest =>
    simp only [fixCountBinds] at hfc
    rw [alphaRenameBinds_cons_eq]; dsimp only; simp only [fixCountBinds]
    have := alphaRename_fixCount_zero σ rhs s (by omega)
    have := alphaRenameBinds_fixCountBinds_zero ((v, fresh σ s rhs v) :: σ) rest
      ⟨(alphaRename σ rhs s).2.next + 1⟩ (by omega)
    omega
termination_by sizeOf binds

end

/-! ## Top level -/

theorem alphaRenameTop_lowerTotal_eq (e : Expr) (K : Moist.MIR.FreshState)
    (hK : maxUidExpr e < K.next) (env : List VarId) :
    lowerTotal env e = lowerTotal env (Moist.MIR.alphaRenameTop e K).1 :=
  (alphaRename_lowerTotal_eq (maxUidExpr e) e [] K env env (Nat.le_refl _) hK
    (fun _ hp => absurd hp List.not_mem_nil) (fun _ _ => rfl)).1

theorem alphaRenameTop_lowerTotalExpr_eq (e : Expr) (K : Moist.MIR.FreshState)
    (hK : maxUidExpr e < K.next) (hFixFree : fixCount e = 0) (env : List VarId) :
    lowerTotalExpr env e = lowerTotalExpr env (Moist.MIR.alphaRenameTop e K).1 := by
  rw [lowerTotalExpr_eq_lowerTotal env e hFixFree, lowerTotalExpr_eq_lowerTotal env
    (alphaRenameTop e K).1 (alphaRename_fixCount_zero [] e K hFixFree)]
  exact alphaRenameTop_lowerTotal_eq e K hK env

end Moist.Verified.MIR
