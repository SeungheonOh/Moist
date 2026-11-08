import Moist.Verified.StaticArguments.Semantics
import Moist.Verified.HygieneSoundness
import Moist.Verified.AdvancedTraversal
import Moist.Verified.MIR.Hoist
import Moist.MIR.Optimize.Advanced.Recursion

variable [sv : Moist.CEK.SemVariant]

/-! # Soundness of the static argument transformation

`Fix r (λp. λn. body) ⊑ λp. Fix r (λn. body')`, where `body'` drops the first
argument of every recursive call. `lower_rel` shows the two worker lowerings
are related by `StaticArguments.Rel`; `openRefines_static` supplies the
semantics. The bottom-up driver is certified by fuel induction.
-/

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced
open Moist.Plutus.Term (Term)
open Moist.Verified (closedAt)
open Moist.Verified.StaticArguments (Rel RelList openRefines_static)

namespace StaticArguments

/-! ## Variable lookups -/

omit sv in
theorem envLookupT_append (bs rest : List VarId) (x : VarId) :
    envLookupT (bs ++ rest) x =
      match envLookupT bs x with
      | some i => some i
      | none => (envLookupT rest x).map (· + bs.length) := by
  induction bs with
  | nil =>
    simp only [List.nil_append, envLookupT, envLookupT.go, List.length_nil]
    cases envLookupT.go x rest 0 <;> rfl
  | cons b bs ih =>
    simp only [envLookupT, List.cons_append, envLookupT.go] at ih ⊢
    split
    · rfl
    · have h₁ := envLookupT.go_shift x (bs ++ rest) 0 1
      have h₂ := envLookupT.go_shift x bs 0 1
      simp only [Nat.zero_add] at h₁ h₂
      rw [h₁, h₂, ih]
      cases envLookupT.go x bs 0 <;> cases envLookupT.go x rest 0 <;>
        simp [List.length_cons] <;> omega

omit sv in
theorem beq_symm {a b : VarId} (h : (a == b) = true) : (b == a) = true := by
  rw [VarId.beq_true_iff] at h ⊢
  exact ⟨h.1.symm, h.2.symm⟩

omit sv in
theorem beq_false_of_uid {a b : VarId} (h : a.uid ≠ b.uid) : (a == b) = false :=
  (VarId.beq_false_iff a b).mpr (.inr h)

omit sv in
theorem lookup_none_of_avoid {bs : List VarId} {x z : VarId}
    (hbs : ∀ y ∈ bs, (y == z) = false) (hxz : (x == z) = true) : envLookupT bs x = none := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    unfold envLookupT envLookupT.go
    have hb : (b == x) = false := by
      cases h : (b == x)
      · rfl
      · have := VarId.beq_trans b x z h hxz
        rw [(hbs b (.head _))] at this
        exact absurd this (by simp)
    simp only [hb]
    have := envLookupT.go_shift x bs 0 1
    simp only [Nat.zero_add] at this
    rw [this]
    have h' := ih (fun y hy => hbs y (.tail _ hy))
    unfold envLookupT at h'
    rw [h']
    rfl

omit sv in
/-- A variable that is not the recursive name lowers to related indices. -/
theorem lower_var (r p σ : VarId) (env bs : List VarId) (x : VarId) (idx : Nat)
    (hx : (x == r) = false) (hσx : x.uid < σ.uid)
    (h : envLookupT (bs ++ p :: r :: σ :: env) x = some idx) :
    ∃ idx', envLookupT (bs ++ r :: σ :: p :: env) x = some idx' ∧
      Rel env.length bs.length (.Var (idx + 1)) (.Var (idx' + 1)) := by
  rw [envLookupT_append] at h ⊢
  cases hb : envLookupT bs x with
  | some i =>
    rw [hb] at h
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, .varLow (by have := envLookupT_bound bs x _ hb; omega)⟩
  | none =>
    rw [hb] at h
    simp only at h ⊢
    have hσx' : (σ == x) = false := beq_false_of_uid (by omega)
    have hrx : (r == x) = false := by
      cases h' : (r == x)
      · rfl
      · rw [beq_symm h'] at hx; exact absurd hx (by simp)
    by_cases hpx : (p == x) = true
    · simp only [envLookupT, envLookupT.go, hpx, if_true, Option.map_some] at h
      cases h
      refine ⟨2 + bs.length, ?_, ?_⟩
      · simp only [envLookupT, envLookupT.go, hrx, hσx', hpx]
        simp
      · rw [show 0 + bs.length + 1 = bs.length + 1 by omega,
          show 2 + bs.length + 1 = bs.length + 3 by omega]
        exact .varParam
    · simp only [Bool.not_eq_true] at hpx
      have hgo : ∀ (l : List VarId), envLookupT.go x l 3 = (envLookupT l x).map (· + 3) := by
        intro l
        have := envLookupT.go_shift x l 0 3
        simp only [Nat.zero_add] at this
        exact this
      simp only [envLookupT, envLookupT.go, hpx, hrx, hσx', Bool.false_eq_true, if_false] at h ⊢
      have h3 := hgo env
      unfold envLookupT at h3
      rw [h3] at h ⊢
      cases he : envLookupT.go x env 0 with
      | none => rw [he] at h; cases h
      | some j =>
        rw [he] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        have hj : j < env.length := envLookupT_bound env x j he
        refine ⟨j + 3 + bs.length, rfl, .varHigh (by omega) (by omega)⟩

omit sv in
/-- A recursive call `r p` lowers to the call pattern of `Rel`. -/
theorem lower_call (r p σ : VarId) (env bs : List VarId) (b a : VarId) (ts : Term)
    (hbr : (b == r) = true) (hap : (a == p) = true) (hpr : (p == r) = false)
    (hbs : ∀ y ∈ bs, (y == r) = false ∧ (y == p) = false)
    (h : lowerTotalExpr (bs ++ p :: r :: σ :: env) (.App (.Var b) (.Var a)) = some ts) :
    lowerTotalExpr (bs ++ r :: σ :: p :: env) (.Var b) = some (.Var (bs.length + 1)) ∧
      ts = .Apply (.Var (bs.length + 2)) (.Var (bs.length + 1)) := by
  have hb := lookup_none_of_avoid (fun y hy => (hbs y hy).1) hbr
  have ha := lookup_none_of_avoid (fun y hy => (hbs y hy).2) hap
  have hpb : (p == b) = false := by
    cases h' : (p == b)
    · rfl
    · rw [VarId.beq_trans p b r h' hbr] at hpr; exact absurd hpr (by simp)
  have hrb : (r == b) = true := beq_symm hbr
  have hpa : (p == a) = true := beq_symm hap
  simp only [lowerTotalExpr, expandFix, lowerTotal, Option.bind_eq_bind, envLookupT_append, hb,
    ha] at h ⊢
  simp only [envLookupT, envLookupT.go, hpb, hrb, hpa, Bool.false_eq_true, if_false, if_true,
    Option.map_some, Option.bind_some, Option.some.injEq] at h ⊢
  refine ⟨by congr 2; omega, ?_⟩
  rw [← h]
  congr 2 <;> omega

/-! ## Equations for applications whose head is not a variable -/

omit sv in
theorem invariantUses_app_nonvar (r p : VarId) {f a : Expr} (hf : ∀ b, f ≠ .Var b) :
    invariantUses r p (.App f a) = (invariantUses r p f && invariantUses r p a) := by
  cases f <;> first | exact absurd rfl (hf _) | simp only [invariantUses]

omit sv in
theorem removeArgument_app_nonvar (r : VarId) {f a : Expr} (hf : ∀ b, f ≠ .Var b) :
    removeArgument r (.App f a) = .App (removeArgument r f) (removeArgument r a) := by
  cases f <;> first | exact absurd rfl (hf _) | simp only [removeArgument]

omit sv in
theorem invariantUses_app_var (r p b : VarId) (a : Expr) (hbr : (b == r) = false) :
    invariantUses r p (.App (.Var b) a) = invariantUses r p a := by
  cases a <;> simp [invariantUses, hbr]

omit sv in
theorem removeArgument_app_var (r b : VarId) (a : Expr) (hbr : (b == r) = false) :
    removeArgument r (.App (.Var b) a) = .App (.Var b) (removeArgument r a) := by
  cases a <;> simp [removeArgument, hbr]

omit sv in
/-- The fixed-point wrapper preserves `Rel`. -/
theorem rel_wrap {e d : Nat} {B₁ B₂ : Term} (h : Rel e (d + 3) B₁ B₂) :
    Rel e d (fixLamWrapUplc B₁) (fixLamWrapUplc B₂) :=
  .apply (.lam (.apply (.varLow (by omega)) (.varLow (by omega))))
    (.lam (.apply (.lam (.lam h))
      (.lam (.apply (.apply (.varLow (by omega)) (.varLow (by omega))) (.varLow (by omega))))))

/-! ## Lowering the worker -/

omit sv in
theorem avoid_cons {r p x : VarId} {bs : List VarId}
    (hx : (x == r) = false ∧ (x == p) = false)
    (hbs : ∀ y ∈ bs, (y == r) = false ∧ (y == p) = false) :
    ∀ y ∈ x :: bs, (y == r) = false ∧ (y == p) = false := by
  intro y hy
  cases hy with
  | head => exact hx
  | tail _ hy => exact hbs y hy

omit sv in
theorem not_bne {a b : VarId} (h : (a != b) = true) : (a == b) = false := by
  simpa [bne] using h

mutual
  /-- The source worker lowered under `bs, p, r, σ, env` and the target worker
      lowered under `bs, r, σ, p, env` are related by `Rel`. -/
  theorem lower_rel (r p σ : VarId) (env : List VarId) (hpr : (p == r) = false)
      (e : Expr) (bs : List VarId) (ts : Term)
      (hinv : invariantUses r p e = true) (huid : maxUidExpr e < σ.uid)
      (hbs : ∀ y ∈ bs, (y == r) = false ∧ (y == p) = false)
      (hlow : lowerTotalExpr (bs ++ p :: r :: σ :: env) e = some ts) :
      ∃ tt, lowerTotalExpr (bs ++ r :: σ :: p :: env) (removeArgument r e) = some tt ∧
        Rel env.length bs.length ts tt := by
    match e with
    | .Var x =>
      have hx : (x == r) = false := not_bne (by simpa only [invariantUses] using hinv)
      simp only [maxUidExpr] at huid
      simp only [lowerTotalExpr, expandFix, lowerTotal] at hlow
      cases hl : envLookupT (bs ++ p :: r :: σ :: env) x with
      | none => rw [hl] at hlow; cases hlow
      | some idx =>
        rw [hl] at hlow
        cases hlow
        obtain ⟨idx', h', hrel⟩ := lower_var r p σ env bs x idx hx huid hl
        refine ⟨_, ?_, hrel⟩
        simp only [removeArgument, lowerTotalExpr, expandFix, lowerTotal, h']
    | .Lit ⟨c, ty⟩ =>
      simp only [lowerTotalExpr, expandFix, lowerTotal, Option.some.injEq] at hlow
      subst hlow
      exact ⟨_, by simp only [removeArgument, lowerTotalExpr, expandFix, lowerTotal], .constant⟩
    | .Builtin b =>
      simp only [lowerTotalExpr, expandFix, lowerTotal, Option.some.injEq] at hlow
      subst hlow
      exact ⟨_, by simp only [removeArgument, lowerTotalExpr, expandFix, lowerTotal], .builtin⟩
    | .Error =>
      simp only [lowerTotalExpr, expandFix, lowerTotal, Option.some.injEq] at hlow
      subst hlow
      exact ⟨_, by simp only [removeArgument, lowerTotalExpr, expandFix, lowerTotal], .error⟩
    | .Lam x b =>
      simp only [invariantUses, Bool.and_eq_true] at hinv
      simp only [maxUidExpr] at huid
      rw [lowerTotalExpr_lam] at hlow
      obtain ⟨tb, htb, rfl⟩ := Option.map_eq_some_iff.mp hlow
      obtain ⟨tt, htt, hrel⟩ := lower_rel r p σ env hpr b (x :: bs) tb hinv.2 (by omega)
        (avoid_cons ⟨not_bne hinv.1.1, not_bne hinv.1.2⟩ hbs) htb
      refine ⟨.Lam 0 tt, ?_, .lam hrel⟩
      simp only [removeArgument, lowerTotalExpr_lam]
      rw [List.cons_append] at htt
      rw [htt]; rfl
    | .Fix f body =>
      by_cases hl : ∃ x b, body = .Lam x b
      · obtain ⟨x, b, rfl⟩ := hl
        simp only [invariantUses, Bool.and_eq_true] at hinv
        simp only [maxUidExpr] at huid
        let s : VarId := ⟨maxUidExpr (expandFix b) + maxUidExpr (expandFix (removeArgument r b)) +
          r.uid + p.uid + 1, .gen, "s"⟩
        have hs₁ : (freeVars (expandFix b)).contains s = false :=
          maxUidExpr_fresh _ s (by simp only [s]; omega)
        have hs₂ : (freeVars (expandFix (removeArgument r b))).contains s = false :=
          maxUidExpr_fresh _ s (by simp only [s]; omega)
        have hsr : (s == r) = false := beq_false_of_uid (by simp only [s]; omega)
        have hsp : (s == p) = false := beq_false_of_uid (by simp only [s]; omega)
        rw [lowerTotalExpr_fix_lam_with_fresh _ f x b s hs₁] at hlow
        obtain ⟨tb, htb, rfl⟩ := Option.map_eq_some_iff.mp hlow
        obtain ⟨tt, htt, hrel⟩ := lower_rel r p σ env hpr b (x :: f :: s :: bs) tb hinv.2.2
          (by omega)
          (avoid_cons ⟨not_bne hinv.2.1.1, not_bne hinv.2.1.2⟩
            (avoid_cons ⟨not_bne hinv.1.1, not_bne hinv.1.2⟩ (avoid_cons ⟨hsr, hsp⟩ hbs))) htb
        refine ⟨fixLamWrapUplc tt, ?_, rel_wrap hrel⟩
        simp only [removeArgument]
        rw [lowerTotalExpr_fix_lam_with_fresh _ f x _ s hs₂]
        simp only [List.cons_append] at htt
        simp only [lowerTotalExpr] at htt
        rw [htt]; rfl
      · rw [lowerTotalExpr_fix_nonlam_none _ f body (fun x b h => hl ⟨x, b, h⟩)] at hlow
        cases hlow
    | .App f a =>
      simp only [maxUidExpr] at huid
      by_cases hf : ∃ b, f = .Var b
      · obtain ⟨b, rfl⟩ := hf
        simp only [maxUidExpr] at huid
        by_cases hbr : (b == r) = true
        · cases a with
          | Var a' =>
            simp only [invariantUses, hbr, if_true] at hinv
            obtain ⟨h₁, h₂⟩ := lower_call r p σ env bs b a' ts hbr hinv hpr hbs hlow
            subst h₂
            refine ⟨_, ?_, .call⟩
            simp only [removeArgument, hbr, if_true]
            exact h₁
          | _ => simp [invariantUses, hbr] at hinv
        · simp only [Bool.not_eq_true] at hbr
          have hinv' : invariantUses r p a = true := by
            rwa [invariantUses_app_var r p b a hbr] at hinv
          rw [lowerTotalExpr_app] at hlow
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hlow
          obtain ⟨f', hf', a', ha', rfl⟩ := hlow
          obtain ⟨tf, htf, hrf⟩ := lower_rel r p σ env hpr (.Var b) bs f'
            (by simp only [invariantUses, bne, hbr, Bool.not_false]) (by simp only [maxUidExpr]; omega)
            hbs hf'
          obtain ⟨ta, hta, hra⟩ := lower_rel r p σ env hpr a bs a' hinv' (by omega) hbs ha'
          refine ⟨.Apply tf ta, ?_, .apply hrf hra⟩
          simp only [removeArgument] at htf
          rw [removeArgument_app_var r b a hbr, lowerTotalExpr_app, htf, hta]; rfl
      · have hf' : ∀ b, f ≠ .Var b := fun b h => hf ⟨b, h⟩
        rw [invariantUses_app_nonvar r p hf', Bool.and_eq_true] at hinv
        rw [lowerTotalExpr_app] at hlow
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hlow
        obtain ⟨f₁, hf₁, a₁, ha₁, rfl⟩ := hlow
        obtain ⟨tf, htf, hrf⟩ := lower_rel r p σ env hpr f bs f₁ hinv.1 (by omega) hbs hf₁
        obtain ⟨ta, hta, hra⟩ := lower_rel r p σ env hpr a bs a₁ hinv.2 (by omega) hbs ha₁
        refine ⟨.Apply tf ta, ?_, .apply hrf hra⟩
        rw [removeArgument_app_nonvar r hf', lowerTotalExpr_app, htf, hta]; rfl
    | .Force t =>
      simp only [invariantUses] at hinv
      simp only [maxUidExpr] at huid
      rw [lowerTotalExpr_force] at hlow
      obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp hlow
      obtain ⟨tt, htt, hrel⟩ := lower_rel r p σ env hpr t bs t₁ hinv huid hbs ht₁
      refine ⟨.Force tt, ?_, .force hrel⟩
      simp only [removeArgument, lowerTotalExpr_force, htt]; rfl
    | .Delay t =>
      simp only [invariantUses] at hinv
      simp only [maxUidExpr] at huid
      rw [lowerTotalExpr_delay] at hlow
      obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp hlow
      obtain ⟨tt, htt, hrel⟩ := lower_rel r p σ env hpr t bs t₁ hinv huid hbs ht₁
      refine ⟨.Delay tt, ?_, .delay hrel⟩
      simp only [removeArgument, lowerTotalExpr_delay, htt]; rfl
    | .Constr tag args =>
      simp only [invariantUses] at hinv
      simp only [maxUidExpr] at huid
      rw [lowerTotalExpr_constr_of_list] at hlow
      obtain ⟨ts₁, hts₁, rfl⟩ := Option.map_eq_some_iff.mp hlow
      obtain ⟨tt, htt, hrel⟩ := lowerList_rel r p σ env hpr args bs ts₁ hinv huid hbs hts₁
      refine ⟨.Constr tag tt, ?_, .constr hrel⟩
      simp only [removeArgument, lowerTotalExpr_constr_of_list, htt]; rfl
    | .Case scrut alts =>
      simp only [invariantUses, Bool.and_eq_true] at hinv
      simp only [maxUidExpr] at huid
      rw [lowerTotalExpr_case_of_list] at hlow
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hlow
      obtain ⟨s₁, hs₁, as₁, has₁, rfl⟩ := hlow
      obtain ⟨st, hst, hrs⟩ := lower_rel r p σ env hpr scrut bs s₁ hinv.1 (by omega) hbs hs₁
      obtain ⟨at', hat, hra⟩ := lowerList_rel r p σ env hpr alts bs as₁ hinv.2 (by omega) hbs has₁
      refine ⟨.Case st at', ?_, .case hrs hra⟩
      simp only [removeArgument]
      rw [lowerTotalExpr_case_of_list, hst, hat]; rfl
    | .Let binds body =>
      simp only [invariantUses] at hinv
      simp only [maxUidExpr] at huid
      rw [lowerTotalExpr_let] at hlow
      obtain ⟨tt, htt, hrel⟩ := lowerLet_rel r p σ env hpr binds body bs ts hinv (by omega)
        (by omega) hbs hlow
      refine ⟨tt, ?_, hrel⟩
      simp only [removeArgument]
      rw [lowerTotalExpr_let]; exact htt
  termination_by sizeOf e

  theorem lowerList_rel (r p σ : VarId) (env : List VarId) (hpr : (p == r) = false)
      (es : List Expr) (bs : List VarId) (ts : List Term)
      (hinv : invariantUsesList r p es = true) (huid : maxUidExprList es < σ.uid)
      (hbs : ∀ y ∈ bs, (y == r) = false ∧ (y == p) = false)
      (hlow : lowerTotalExprList (bs ++ p :: r :: σ :: env) es = some ts) :
      ∃ tt, lowerTotalExprList (bs ++ r :: σ :: p :: env) (removeArgumentList r es) = some tt ∧
        RelList env.length bs.length ts tt := by
    match es with
    | [] =>
      rw [lowerTotalExprList_nil] at hlow
      cases hlow
      exact ⟨[], by simp only [removeArgumentList, lowerTotalExprList_nil], .nil⟩
    | e :: rest =>
      simp only [invariantUsesList, Bool.and_eq_true] at hinv
      simp only [maxUidExprList] at huid
      rw [lowerTotalExprList_cons] at hlow
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hlow
      obtain ⟨t₁, ht₁, ts₁, hts₁, rfl⟩ := hlow
      obtain ⟨tt, htt, hrel⟩ := lower_rel r p σ env hpr e bs t₁ hinv.1 (by omega) hbs ht₁
      obtain ⟨tts, htts, hrels⟩ := lowerList_rel r p σ env hpr rest bs ts₁ hinv.2 (by omega) hbs hts₁
      refine ⟨tt :: tts, ?_, .cons hrel hrels⟩
      simp only [removeArgumentList]
      rw [lowerTotalExprList_cons, htt, htts]; rfl
  termination_by sizeOf es

  theorem lowerLet_rel (r p σ : VarId) (env : List VarId) (hpr : (p == r) = false)
      (binds : List (VarId × Expr × Bool)) (body : Expr) (bs : List VarId) (ts : Term)
      (hinv : invariantUsesLet r p binds body = true) (hbinds : maxUidExprBinds binds < σ.uid)
      (hbody : maxUidExpr body < σ.uid)
      (hbs : ∀ y ∈ bs, (y == r) = false ∧ (y == p) = false)
      (hlow : lowerTotalLet (bs ++ p :: r :: σ :: env) (expandFixBinds binds) (expandFix body) =
        some ts) :
      ∃ tt, lowerTotalLet (bs ++ r :: σ :: p :: env) (expandFixBinds (removeArgumentBinds r binds))
          (expandFix (removeArgument r body)) = some tt ∧
        Rel env.length bs.length ts tt := by
    match binds with
    | [] =>
      simp only [invariantUsesLet] at hinv
      simp only [expandFixBinds, lowerTotalLet] at hlow
      obtain ⟨tt, htt, hrel⟩ := lower_rel r p σ env hpr body bs ts hinv hbody hbs hlow
      exact ⟨tt, by simpa only [removeArgumentBinds, expandFixBinds, lowerTotalLet] using htt, hrel⟩
    | (x, rhs, erased) :: rest =>
      simp only [invariantUsesLet, Bool.and_eq_true] at hinv
      simp only [maxUidExprBinds] at hbinds
      simp only [expandFixBinds, lowerTotalLet, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at hlow
      obtain ⟨r₁, hr₁, rest₁, hrest₁, rfl⟩ := hlow
      obtain ⟨tr, htr, hrr⟩ := lower_rel r p σ env hpr rhs bs r₁ hinv.1.2 (by omega) hbs hr₁
      obtain ⟨trest, htrest, hrrest⟩ := lowerLet_rel r p σ env hpr rest body (x :: bs) rest₁
        hinv.2 (by omega) hbody (avoid_cons ⟨not_bne hinv.1.1.1, not_bne hinv.1.1.2⟩ hbs) hrest₁
      refine ⟨.Apply (.Lam 0 trest) tr, ?_, .apply (.lam hrrest) hrr⟩
      simp only [removeArgumentBinds, expandFixBinds, lowerTotalLet]
      simp only [List.cons_append] at htrest
      simp only [lowerTotalExpr] at htr
      rw [htr, htrest]; rfl
  termination_by sizeOf binds + sizeOf body
end

end StaticArguments

open StaticArguments

/-! ## The local rewrite -/

/-- Moving an invariant leading parameter out of a recursive worker. -/
theorem staticArgument_local (r p n : VarId) (body : Expr) (hpr : (p == r) = false)
    (hinv : invariantUses r p (.Lam n body) = true) :
    MIRCtxRefines (.Fix r (.Lam p (.Lam n body)))
      (.Lam p (.Fix r (removeArgument r (.Lam n body)))) := by
  intro env
  let σ : VarId := ⟨maxUidExpr (expandFix body) + maxUidExpr (expandFix (removeArgument r body)) +
    maxUidExpr body + n.uid + p.uid + 1, .gen, "s"⟩
  have hs₁ : (freeVars (expandFix (.Lam n body))).contains σ = false :=
    maxUidExpr_fresh _ σ (by simp only [expandFix, maxUidExpr, σ]; omega)
  have hs₂ : (freeVars (expandFix (removeArgument r body))).contains σ = false :=
    maxUidExpr_fresh _ σ (by simp only [σ]; omega)
  have hsrc : lowerTotalExpr env (.Fix r (.Lam p (.Lam n body))) =
      (lowerTotalExpr (p :: r :: σ :: env) (.Lam n body)).map fixLamWrapUplc :=
    lowerTotalExpr_fix_lam_with_fresh env r p (.Lam n body) σ hs₁
  have htgt : lowerTotalExpr env (.Lam p (.Fix r (removeArgument r (.Lam n body)))) =
      ((lowerTotalExpr (n :: r :: σ :: p :: env) (removeArgument r body)).map
        fixLamWrapUplc).map (.Lam 0) := by
    rw [lowerTotalExpr_lam]
    simp only [removeArgument]
    rw [lowerTotalExpr_fix_lam_with_fresh (p :: env) r n _ σ hs₂]
    rfl
  rw [hsrc, htgt]
  cases hW : lowerTotalExpr (p :: r :: σ :: env) (.Lam n body) with
  | none => exact ⟨fun h => absurd h (by simp), trivial⟩
  | some ts =>
    obtain ⟨tt, htt, hrel⟩ := lower_rel r p σ env hpr (.Lam n body) [] ts hinv
      (by simp only [maxUidExpr, σ]; omega) (fun _ h => absurd h List.not_mem_nil) hW
    rw [lowerTotalExpr_lam] at hW
    obtain ⟨bodyS, -, rfl⟩ := Option.map_eq_some_iff.mp hW
    simp only [List.nil_append, removeArgument, lowerTotalExpr_lam] at htt
    obtain ⟨bodyT, hbodyT, rfl⟩ := Option.map_eq_some_iff.mp htt
    cases hrel with
    | lam hbody =>
    rw [hbodyT]
    simp only [Option.map_some, Option.isSome_some]
    refine ⟨fun _ => trivial, ?_⟩
    refine ctxRefines_of_openRefines (fun k hk => ?_) (openRefines_static hbody)
    simp only [fixLamWrapUplc, closedAt, Bool.and_eq_true, decide_eq_true_eq] at hk ⊢
    refine ⟨⟨by omega, by omega⟩, ?_, ⟨by omega, by omega⟩, by omega⟩
    have hidx : ([] : List VarId).length + 1 + 3 + k = k + 1 + 1 + 1 + 1 := by
      simp only [List.length_nil]; omega
    have := hbody.closedAt k (by rw [hidx]; exact hk.2.1)
    rwa [hidx] at this

/-! ## The traversal -/

theorem staticArgumentsRoot_refines (recurse : Expr → Expr)
    (sound : ∀ expression, MIRCtxRefines expression (recurse expression)) (expression : Expr) :
    MIRCtxRefines expression (staticArgumentsRoot recurse expression) := by
  unfold staticArgumentsRoot
  split
  · rename_i r p n body
    dsimp only
    split
    · rename_i guard
      simp only [Bool.and_eq_true] at guard
      exact mirCtxRefines_trans (staticArgument_local r p n body (not_bne guard.1.1) guard.2)
        (mirCtxRefines_lam (sound _))
    · exact mirCtxRefines_refl _
  · exact mirCtxRefines_refl _

theorem staticArgumentsFuel_refines (fuel : Nat) (expression : Expr) :
    MIRCtxRefines expression (staticArgumentsFuel fuel expression) := by
  induction fuel using Nat.strongRecOn generalizing expression with
  | ind fuel ih =>
    cases fuel with
    | zero => exact mirCtxRefines_refl expression
    | succ fuel =>
      refine mirCtxRefines_trans
        (mapChildren_refines _ expression (fun child _ => ih fuel (by omega) child) ?_)
        (staticArgumentsRoot_refines _ (ih fuel (by omega)) _)
      intro binder body _
      cases fuel with
      | zero => exact ⟨body, rfl, mirCtxRefines_refl body⟩
      | succ remaining => exact ⟨_, rfl, ih remaining (by omega) body⟩

theorem staticArgumentsCore_refines (expression : Expr) :
    MIRCtxRefines expression (staticArgumentsCore expression) :=
  staticArgumentsFuel_refines _ expression

/-- Whole-pass certificate for the static argument transformation. -/
theorem staticArguments_refines (expression : Expr) :
    MIRCtxRefines expression (staticArguments expression) :=
  mirCtxRefines_trans (Hygiene.uniqueOptimizationBinders_refines expression)
    (staticArgumentsCore_refines _)

end Moist.Verified.MIR
