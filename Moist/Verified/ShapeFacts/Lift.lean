import Moist.Verified.ShapeFacts.Fresh
import Moist.Verified.ShapeFacts.Decompose

/-! # Refinement of MIR expressions under facts

`FactRel G P Γ e e'` lifts `FactRefines` to MIR: in every distinct lowering
environment of names satisfying `G` that avoids the binders of `e` and binds
the recorded names, if
`e` lowers then so does `e'`, and the lowerings refine each other in every
runtime environment realizing `Γ`. The congruences below let a walk carry
its facts through every node it does not rewrite.
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.BetaValueRefines

/-- Every recorded binder bound in `env` has a right-hand side that lowers in
    an older suffix. -/
def FactsScoped (Γ : List (VarId × Expr)) (env : List VarId) : Prop :=
  ∀ x entry i, Γ.find? (fun e => e.1 == x) = some entry → envLookupT env x = some i →
    ∃ k, i < k ∧ k ≤ env.length ∧ (lowerTotalExpr (env.drop k) entry.2).isSome

/-- Every recorded name is bound. -/
def KeysBound (Γ : List (VarId × Expr)) (env : List VarId) : Prop :=
  ∀ entry ∈ Γ, (envLookupT env entry.1).isSome = true

def FactRel (G : VarId → Prop) (P : List VarId → CekEnv → Expr → CekValue → Prop)
    (Γ : List (VarId × Expr)) (e e' : Expr) : Prop :=
  ∀ env t, (∀ y ∈ env, G y) → EnvDistinct env → freshIn env e = true → KeysBound Γ env →
    FactsScoped Γ env →
    lowerTotalExpr env e = some t →
    ∃ t', lowerTotalExpr env e' = some t' ∧ FactRefines env.length (FactsHold P Γ env) t t'

theorem FactRel.refl (G : VarId → Prop) (P : List VarId → CekEnv → Expr → CekValue → Prop)
    (Γ : List (VarId × Expr)) (e : Expr) : FactRel G P Γ e e :=
  fun _ t _ _ _ _ _ h => ⟨t, h, FactRefines.refl _ _ _⟩

theorem FactRel.of_lowerEq {G : VarId → Prop} {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} {e e' : Expr}
    (h : ∀ env, lowerTotalExpr env e' = lowerTotalExpr env e) : FactRel G P Γ e e' :=
  fun env t _ _ _ _ _ he => ⟨t, by rw [h, he], FactRefines.refl _ _ _⟩

theorem FactRel.of_mirCtxRefines_lower {G : VarId → Prop} {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} {e e' : Expr}
    (h : ∀ env t, lowerTotalExpr env e = some t → ∃ t', lowerTotalExpr env e' = some t' ∧
      FactRefines env.length (fun _ => True) t t') : FactRel G P Γ e e' := by
  intro env t _ _ _ _ _ he
  obtain ⟨t', ht', hr⟩ := h env t he
  exact ⟨t', ht', hr.mono fun _ _ => trivial⟩

/-! ## Environment invariants under binders -/

theorem KeysBound.cons {Γ : List (VarId × Expr)} {env : List VarId} (h : KeysBound Γ env)
    (x : VarId) : KeysBound Γ (x :: env) := by
  intro entry hmem
  rw [envLookupT_cons]
  split
  · rfl
  · simpa using h entry hmem

theorem find?_none_of_unbound {Γ : List (VarId × Expr)} {env : List VarId} {x : VarId}
    (hk : KeysBound Γ env) (hx : (envLookupT env x).isNone = true) :
    Γ.find? (fun e => e.1 == x) = none := by
  cases hf : Γ.find? (fun e => e.1 == x) with
  | none => rfl
  | some entry =>
    have hmem := List.mem_of_find?_eq_some hf
    have hkey : (entry.1 == x) = true := by simpa using List.find?_some hf
    have := hk entry hmem
    rw [envLookupT_congr hkey] at this
    simp [Option.isSome_iff_ne_none, Option.isNone_iff_eq_none] at this hx
    exact absurd hx this

theorem FactsScoped.extend {Γ : List (VarId × Expr)} {env : List VarId} {x : VarId}
    (h : FactsScoped Γ env) (hx : Γ.find? (fun e => e.1 == x) = none) :
    FactsScoped Γ (x :: env) := by
  intro y entry i hf hl
  by_cases hxy : (x == y) = true
  · have : Γ.find? (fun e => e.1 == x) = Γ.find? (fun e => e.1 == y) := by
      congr 1; funext e
      have h1 := (VarId.beq_true_iff x y).mp hxy
      show (e.1.origin == x.origin && e.1.uid == x.uid) = (e.1.origin == y.origin && e.1.uid == y.uid)
      rw [h1.1, h1.2]
    rw [this, hf] at hx; cases hx
  · have hxy' : (x == y) = false := by simpa using hxy
    rw [envLookupT_cons_neq x y env hxy'] at hl
    cases hl' : envLookupT env y with
    | none => rw [hl'] at hl; cases hl
    | some i' =>
      rw [hl'] at hl; simp at hl; subst hl
      obtain ⟨k, hik, hk, hs⟩ := h y entry i' hf hl'
      exact ⟨k + 1, by omega, by simp; omega, by simpa using hs⟩

theorem FactsScoped.push {Γ : List (VarId × Expr)} {env : List VarId} {x : VarId} {rhs : Expr}
    (h : FactsScoped Γ env) (hrhs : (lowerTotalExpr env rhs).isSome = true) :
    FactsScoped ((x, rhs) :: Γ) (x :: env) := by
  intro y entry i hf hl
  by_cases hxy : (x == y) = true
  · simp only [List.find?_cons, hxy] at hf
    cases hf
    rw [MIR.envLookupT_cons_of_beq hxy env] at hl
    cases hl
    exact ⟨1, by omega, by simp, by simpa using hrhs⟩
  · have hxy' : (x == y) = false := by simpa using hxy
    simp only [List.find?_cons, hxy'] at hf
    rw [envLookupT_cons_neq x y env hxy'] at hl
    cases hl' : envLookupT env y with
    | none => rw [hl'] at hl; cases hl
    | some i' =>
      rw [hl'] at hl; simp at hl; subst hl
      obtain ⟨k, hik, hk, hs⟩ := h y entry i' hf hl'
      exact ⟨k + 1, by omega, by simp; omega, by simpa using hs⟩

/-- The invariants of a walk after entering the scope of a binder without a fact. -/
theorem enter_binder {Γ : List (VarId × Expr)} {env : List VarId} {x : VarId}
    (hd : EnvDistinct env) (hk : KeysBound Γ env) (hs : FactsScoped Γ env)
    (hx : (envLookupT env x).isNone = true) :
    EnvDistinct (x :: env) ∧ KeysBound Γ (x :: env) ∧ FactsScoped Γ (x :: env) ∧
      Γ.find? (fun e => e.1 == x) = none :=
  ⟨hd.cons hx, hk.cons x, hs.extend (find?_none_of_unbound hk hx), find?_none_of_unbound hk hx⟩

theorem allG_cons {G : VarId → Prop} {x : VarId} {env : List VarId} (hx : G x)
    (h : ∀ y ∈ env, G y) : ∀ y ∈ x :: env, G y := by
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact hx
  · exact h y hy

/-! ## Congruences -/

theorem FactRel.lam {G : VarId → Prop} {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} {x : VarId} {b b' : Expr} (hGx : G x) (h : FactRel G P Γ b b') :
    FactRel G P Γ (.Lam x b) (.Lam x b') := by
  intro env t hG hd hfresh hk hs hlow
  simp only [freshIn, Bool.and_eq_true] at hfresh
  obtain ⟨hd', hk', hs', hnone⟩ := enter_binder hd hk hs hfresh.1
  obtain ⟨tb, htb, rfl⟩ := lowerTotalExpr_lam_some hlow
  obtain ⟨tb', htb', hr⟩ := h (x :: env) tb (allG_cons hGx hG) hd' hfresh.2 hk' hs' htb
  refine ⟨.Lam 0 tb', by rw [MIR.lowerTotalExpr_lam, htb']; rfl, ?_⟩
  exact factRefines_lam 0 0 (by simpa using MIR.lowerTotalExpr_closedAt htb)
    (by simpa using MIR.lowerTotalExpr_closedAt htb')
    (fun ρ v hF => FactsHold.extend v hF hnone) (by simpa using hr)

theorem FactRel.delay {G : VarId → Prop} {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} {b b' : Expr} (h : FactRel G P Γ b b') :
    FactRel G P Γ (.Delay b) (.Delay b') := by
  intro env t hG hd hfresh hk hs hlow
  simp only [freshIn] at hfresh
  obtain ⟨tb, htb, rfl⟩ := lowerTotalExpr_delay_some hlow
  obtain ⟨tb', htb', hr⟩ := h env tb hG hd hfresh hk hs htb
  refine ⟨.Delay tb', by rw [MIR.lowerTotalExpr_delay, htb']; rfl, ?_⟩
  exact factRefines_delay (MIR.lowerTotalExpr_closedAt htb) (MIR.lowerTotalExpr_closedAt htb') hr

theorem FactRel.force {G : VarId → Prop} {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} {b b' : Expr} (h : FactRel G P Γ b b') :
    FactRel G P Γ (.Force b) (.Force b') := by
  intro env t hG hd hfresh hk hs hlow
  simp only [freshIn] at hfresh
  obtain ⟨tb, htb, rfl⟩ := lowerTotalExpr_force_some hlow
  obtain ⟨tb', htb', hr⟩ := h env tb hG hd hfresh hk hs htb
  exact ⟨.Force tb', by rw [MIR.lowerTotalExpr_force, htb']; rfl, factRefines_force hr⟩

theorem FactRel.app {G : VarId → Prop} {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} {f f' a a' : Expr} (hf : FactRel G P Γ f f') (ha : FactRel G P Γ a a') :
    FactRel G P Γ (.App f a) (.App f' a') := by
  intro env t hG hd hfresh hk hs hlow
  simp only [freshIn, Bool.and_eq_true] at hfresh
  obtain ⟨tf, ta, htf, hta, rfl⟩ := lowerTotalExpr_app_some hlow
  obtain ⟨tf', htf', hrf⟩ := hf env tf hG hd hfresh.1 hk hs htf
  obtain ⟨ta', hta', hra⟩ := ha env ta hG hd hfresh.2 hk hs hta
  refine ⟨.Apply tf' ta', by rw [MIR.lowerTotalExpr_app, htf', hta']; rfl, ?_⟩
  exact factRefines_apply hrf hra (MIR.lowerTotalExpr_closedAt htf') (MIR.lowerTotalExpr_closedAt hta)

theorem lowerTotalExprList_closedAtList {env : List VarId} {es : List Expr} {ts : List Term}
    (h : MIR.lowerTotalExprList env es = some ts) : closedAtList env.length ts = true :=
  MIR.lowerTotalList_closedAtList env _ ts h

theorem FactRel.list {G : VarId → Prop} {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} :
    ∀ {es es' : List Expr}, ListRel (FactRel G P Γ) es es' →
      ∀ env ts, (∀ y ∈ env, G y) → EnvDistinct env → freshInList env es = true → KeysBound Γ env →
        FactsScoped Γ env → MIR.lowerTotalExprList env es = some ts →
        ∃ ts', MIR.lowerTotalExprList env es' = some ts' ∧
          ListRel (FactRefines env.length (FactsHold P Γ env)) ts ts'
  | [], [], _, env, ts, _, _, _, _, _, h => by
    rw [MIR.lowerTotalExprList_nil] at h; cases h
    exact ⟨[], MIR.lowerTotalExprList_nil env, trivial⟩
  | [], _ :: _, h, _, _, _, _, _, _, _, _ => absurd h id
  | _ :: _, [], h, _, _, _, _, _, _, _, _ => absurd h id
  | e :: es, e' :: es', h, env, ts, hG, hd, hfresh, hk, hs, hlow => by
    simp only [freshInList, Bool.and_eq_true] at hfresh
    rw [MIR.lowerTotalExprList_cons] at hlow
    cases he : lowerTotalExpr env e with
    | none => rw [he] at hlow; cases hlow
    | some te =>
      cases hes : MIR.lowerTotalExprList env es with
      | none => rw [he, hes] at hlow; cases hlow
      | some tes =>
        rw [he, hes] at hlow; cases hlow
        obtain ⟨te', hte', hr⟩ := h.1 env te hG hd hfresh.1 hk hs he
        obtain ⟨tes', htes', hrs⟩ := FactRel.list h.2 env tes hG hd hfresh.2 hk hs hes
        refine ⟨te' :: tes', by rw [MIR.lowerTotalExprList_cons, hte', htes']; rfl, hr, hrs⟩

theorem FactRel.constr {G : VarId → Prop} {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} {tag : Nat} {es es' : List Expr} (h : ListRel (FactRel G P Γ) es es') :
    FactRel G P Γ (.Constr tag es) (.Constr tag es') := by
  intro env t hG hd hfresh hk hs hlow
  simp only [freshIn] at hfresh
  rw [MIR.lowerTotalExpr_constr_of_list] at hlow
  cases hes : MIR.lowerTotalExprList env es with
  | none => rw [hes] at hlow; cases hlow
  | some ts =>
    rw [hes] at hlow; cases hlow
    obtain ⟨ts', hts', hr⟩ := FactRel.list h env ts hG hd hfresh hk hs hes
    refine ⟨.Constr tag ts', by rw [MIR.lowerTotalExpr_constr_of_list, hts']; rfl, ?_⟩
    exact factRefines_constr hr (lowerTotalExprList_closedAtList hes)
      (lowerTotalExprList_closedAtList hts')

theorem FactRel.case {G : VarId → Prop} {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} {s s' : Expr} {alts alts' : List Expr}
    (hs : FactRel G P Γ s s') (halts : ListRel (FactRel G P Γ) alts alts') :
    FactRel G P Γ (.Case s alts) (.Case s' alts') := by
  intro env t hG hd hfresh hk hsc hlow
  simp only [freshIn, Bool.and_eq_true] at hfresh
  obtain ⟨ts, talts, hts, htalts, rfl⟩ := lowerTotalExpr_case_some hlow
  obtain ⟨ts', hts', hr⟩ := hs env ts hG hd hfresh.1 hk hsc hts
  obtain ⟨talts', htalts', hra⟩ := FactRel.list halts env talts hG hd hfresh.2 hk hsc htalts
  refine ⟨.Case ts' talts', by rw [MIR.lowerTotalExpr_case_of_list, hts', htalts']; rfl, ?_⟩
  exact factRefines_case hr hra (MIR.lowerTotalExpr_closedAt hts')
    (lowerTotalExprList_closedAtList htalts)

/-! ## Recursive functions -/

/-- A name with a larger identifier than every name of a list. -/
def envMax : List VarId → Nat
  | [] => 0
  | x :: xs => max x.uid (envMax xs)

theorem envLookupT_none_of_gt : ∀ (env : List VarId) (y : VarId), envMax env < y.uid →
    envLookupT env y = none
  | [], _, _ => rfl
  | x :: xs, y, h => by
    simp only [envMax] at h
    rw [envLookupT_cons]
    have hxy : (x == y) = false := by
      rw [VarId.beq_false_iff]; right; omega
    simp only [hxy, Bool.false_eq_true, if_false]
    rw [envLookupT_none_of_gt xs y (by omega)]; rfl

theorem fixLamWrapUplc_factRefines {d : Nat} {F : CekEnv → Prop} {b b' : Term}
    (closedB : closedAt (d + 1 + 1 + 1) b = true) (closedB' : closedAt (d + 1 + 1 + 1) b' = true)
    (h : FactRefines (d + 1 + 1 + 1)
      (fun ρ => ∃ ρ₀ v₁ v₂ v₃, F ρ₀ ∧ ρ = ((ρ₀.extend v₁).extend v₂).extend v₃) b b') :
    FactRefines d F (fixLamWrapUplc b) (fixLamWrapUplc b') := by
  have selfApp : closedAt (d + 1) (.Lam 0 (.Apply (.Apply (.Var 2) (.Var 2)) (.Var 1))) = true := by
    simp only [closedAt, Bool.and_eq_true, decide_eq_true_eq]; omega
  have inner : ∀ c, closedAt (d + 1 + 1 + 1) c = true →
      closedAt (d + 1) (.Apply (.Lam 0 (.Lam 0 c)) (.Lam 0 (.Apply (.Apply (.Var 2) (.Var 2)) (.Var 1)))) = true := by
    intro c hc
    simp only [closedAt, Bool.and_eq_true] at selfApp ⊢
    exact ⟨hc, selfApp⟩
  unfold fixLamWrapUplc
  refine factRefines_apply (FactRefines.refl _ _ _) ?_
    (by simp [closedAt]) (by rw [closedAt]; exact inner b closedB)
  refine factRefines_lam 0 0 (inner b closedB) (inner b' closedB')
    (G := fun ρ => ∃ ρ₀ v₁, F ρ₀ ∧ ρ = ρ₀.extend v₁) (fun ρ v hF => ⟨ρ, v, hF, rfl⟩) ?_
  refine factRefines_apply ?_ (FactRefines.refl _ _ _) (by simp only [closedAt]; exact closedB') selfApp
  refine factRefines_lam 0 0 (by simp only [closedAt]; exact closedB) (by simp only [closedAt]; exact closedB')
    (G := fun ρ => ∃ ρ₀ v₁ v₂, F ρ₀ ∧ ρ = (ρ₀.extend v₁).extend v₂)
    (fun ρ v ⟨ρ₀, v₁, hF, hρ⟩ => ⟨ρ₀, v₁, v, hF, by rw [hρ]⟩) ?_
  exact factRefines_lam 0 0 closedB closedB'
    (G := fun ρ => ∃ ρ₀ v₁ v₂ v₃, F ρ₀ ∧ ρ = ((ρ₀.extend v₁).extend v₂).extend v₃)
    (fun ρ v ⟨ρ₀, v₁, v₂, hF, hρ⟩ => ⟨ρ₀, v₁, v₂, v, hF, by rw [hρ]⟩) h

theorem FactRel.fix_lam {G : VarId → Prop} {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} {f x : VarId} {b b' : Expr} (hGf : G f) (hGx : G x)
    (hGs : ∀ y : VarId, y.origin = .source → G y) (h : FactRel G P Γ b b') :
    FactRel G P Γ (.Fix f (.Lam x b)) (.Fix f (.Lam x b')) := by
  intro env t hG hd hfresh hk hsc hlow
  simp only [freshIn, Bool.and_eq_true] at hfresh
  obtain ⟨hf, hx, hb⟩ := hfresh
  let s : VarId := ⟨envMax env + maxUidExpr b + maxUidExpr (expandFix b) +
    maxUidExpr (expandFix b') + f.uid + x.uid + 1, .source, "s"⟩
  have hs_env : envLookupT env s = none := envLookupT_none_of_gt env s (by simp [s]; omega)
  have hs_b : (freeVars (expandFix b)).contains s = false := maxUidExpr_fresh _ _ (by simp [s]; omega)
  have hs_b' : (freeVars (expandFix b')).contains s = false := maxUidExpr_fresh _ _ (by simp [s]; omega)
  rw [lowerTotalExpr_fix_lam_with_fresh env f x b s hs_b] at hlow
  cases htb : lowerTotal (x :: f :: s :: env) (expandFix b) with
  | none => rw [htb] at hlow; cases hlow
  | some tb =>
    rw [htb] at hlow; cases hlow
    have hfs : (f == s) = false := by rw [VarId.beq_false_iff]; right; simp [s]; omega
    have hxs : (x == s) = false := by rw [VarId.beq_false_iff]; right; simp [s]; omega
    have hf' : (envLookupT (s :: env) f).isNone = true := by
      rw [envLookupT_cons]
      have : (s == f) = false := by
        cases h : (s == f)
        · rfl
        · exact absurd (varId_beq_symm h) (by simp [hfs])
      simp only [this, Bool.false_eq_true, if_false]; simpa using hf
    have hx' : (envLookupT (f :: s :: env) x).isNone = true := by
      have hsx : (s == x) = false := by
        cases h : (s == x)
        · rfl
        · exact absurd (varId_beq_symm h) (by simp [hxs])
      have hx2 := hx
      rw [envLookupT_cons] at hx2 ⊢
      split
      · rename_i hfx; simp [hfx] at hx2
      · rename_i hfx
        simp only [hfx, Bool.false_eq_true, if_false, Option.isNone_map] at hx2 ⊢
        rw [envLookupT_cons]
        simp only [hsx, Bool.false_eq_true, if_false, Option.isNone_map]; exact hx2
    obtain ⟨hd₁, hk₁, hs₁, hn₁⟩ := enter_binder (x := s) hd hk hsc (by simp [hs_env])
    obtain ⟨hd₂, hk₂, hs₂, hn₂⟩ := enter_binder hd₁ hk₁ hs₁ hf'
    obtain ⟨hd₃, hk₃, hs₃, hn₃⟩ := enter_binder hd₂ hk₂ hs₂ hx'
    have hfresh₃ : freshIn (x :: f :: s :: env) b = true := by
      refine freshIn_avoids b hb ?_
      intro y hy
      rw [envLookupT_cons] at hy ⊢
      split
      · simp
      · rename_i hxy
        simp only [hxy, Bool.false_eq_true, if_false, Option.isSome_map] at hy ⊢
        rw [envLookupT_cons] at hy ⊢
        split
        · simp
        · rename_i hfy
          simp only [hfy, Bool.false_eq_true, if_false, Option.isSome_map] at hy ⊢
          rw [envLookupT_cons] at hy
          split at hy
          · rename_i hsy
            right
            have := (VarId.beq_true_iff s y).mp hsy
            simp [s] at this; omega
          · left; simpa using hy
    obtain ⟨tb', htb', hr⟩ := h (x :: f :: s :: env) tb
      (allG_cons hGx (allG_cons hGf (allG_cons (hGs s rfl) hG))) hd₃ hfresh₃ hk₃ hs₃ htb
    refine ⟨fixLamWrapUplc tb', ?_, ?_⟩
    · rw [lowerTotalExpr_fix_lam_with_fresh env f x b' s hs_b']
      change (lowerTotalExpr (x :: f :: s :: env) b').map fixLamWrapUplc = _
      rw [htb']; rfl
    · have cb := MIR.lowerTotalExpr_closedAt htb
      have cb' := MIR.lowerTotalExpr_closedAt htb'
      simp only [List.length_cons] at cb cb'
      apply fixLamWrapUplc_factRefines (by simpa [Nat.add_assoc] using cb)
        (by simpa [Nat.add_assoc] using cb')
      simp only [List.length_cons] at hr
      apply hr.mono
      rintro ρ ⟨ρ₀, v₁, v₂, v₃, hF, rfl⟩
      exact FactsHold.extend v₃ (FactsHold.extend v₂ (FactsHold.extend v₁ hF hn₁) hn₂) hn₃

/-! ## Bindings -/

theorem lowerTotalExpr_let_single (env : List VarId) (x : VarId) (r b : Expr) (er : Bool) :
    lowerTotalExpr env (.Let [(x, r, er)] b) =
      (do let tr ← lowerTotalExpr env r
          let tb ← lowerTotalExpr (x :: env) b
          some (.Apply (.Lam 0 tb) tr)) := by
  simp only [lowerTotalExpr, expandFix, expandFixBinds, lowerTotal, lowerTotalLet]

theorem lowerTotalExpr_let_single_some {env : List VarId} {x : VarId} {r b : Expr} {er : Bool}
    {t : Term} (h : lowerTotalExpr env (.Let [(x, r, er)] b) = some t) :
    ∃ tr tb, lowerTotalExpr env r = some tr ∧ lowerTotalExpr (x :: env) b = some tb ∧
      t = .Apply (.Lam 0 tb) tr := by
  rw [lowerTotalExpr_let_single] at h
  cases hr : lowerTotalExpr env r with
  | none => rw [hr] at h; cases h
  | some tr =>
    cases hb : lowerTotalExpr (x :: env) b with
    | none => rw [hr, hb] at h; cases h
    | some tb => rw [hr, hb] at h; cases h; exact ⟨tr, tb, rfl, rfl, rfl⟩

theorem freshIn_let_single {avoid : List VarId} {x : VarId} {r b : Expr} {er : Bool} :
    freshIn avoid (.Let [(x, r, er)] b) =
      (freshIn avoid r && (envLookupT avoid x).isNone && freshIn (x :: avoid) b) := by
  simp only [freshIn, freshInLet]

/-- A single binding. The body may use a fact recording either the original
    or the refined right-hand side for the bound value. -/
theorem FactRel.let_single {G : VarId → Prop} {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} {x : VarId} {r r' b b' : Expr} {er : Bool} (rf : Expr) (hGx : G x)
    (hrf : rf = r ∨ rf = r')
    (hr : FactRel G P Γ r r') (hb : FactRel G P ((x, rf) :: Γ) b b')
    (hpush : ∀ env ρ v, EnvDistinct env → freshIn env r = true → Produces env ρ rf v → P env ρ rf v) :
    FactRel G P Γ (.Let [(x, r, er)] b) (.Let [(x, r', er)] b') := by
  intro env t hG hd hfresh hk hsc hlow
  rw [freshIn_let_single] at hfresh
  simp only [Bool.and_eq_true] at hfresh
  obtain ⟨⟨hfr, hx⟩, hfb⟩ := hfresh
  obtain ⟨tr, tb, htr, htb, rfl⟩ := lowerTotalExpr_let_single_some hlow
  obtain ⟨tr', htr', hrr⟩ := hr env tr hG hd hfr hk hsc htr
  have hnone := find?_none_of_unbound hk hx
  have hrf_low : ∃ trf, lowerTotalExpr env rf = some trf ∧ (trf = tr ∨ trf = tr') := by
    rcases hrf with rfl | rfl
    · exact ⟨tr, htr, .inl rfl⟩
    · exact ⟨tr', htr', .inr rfl⟩
  obtain ⟨trf, htrf, htrf_eq⟩ := hrf_low
  have hk' : KeysBound ((x, rf) :: Γ) (x :: env) := by
    intro entry hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · simp [envLookupT_cons, varId_beq_self]
    · exact hk.cons x entry hmem
  have hs' : FactsScoped ((x, rf) :: Γ) (x :: env) := hsc.push (by simp [htrf])
  obtain ⟨tb', htb', hrb⟩ := hb (x :: env) tb (allG_cons hGx hG) (hd.cons hx) hfb hk' hs' htb
  refine ⟨.Apply (.Lam 0 tb') tr', by rw [lowerTotalExpr_let_single, htr', htb']; rfl, ?_⟩
  have closedTr := MIR.lowerTotalExpr_closedAt htr
  have closedTr' := MIR.lowerTotalExpr_closedAt htr'
  have closedTb := MIR.lowerTotalExpr_closedAt htb
  have closedTb' := MIR.lowerTotalExpr_closedAt htb'
  simp only [List.length_cons] at closedTb closedTb' hrb
  have body : ∀ tr₀, lowerTotalExpr env rf = some tr₀ → closedAt env.length tr₀ = true →
      FactRefines env.length (FactsHold P Γ env) (.Apply (.Lam 0 tb) tr₀) (.Apply (.Lam 0 tb') tr₀) := by
    intro tr₀ htr₀ closed₀
    apply factRefines_let 0 0 closed₀ _ hrb
    intro ρ v hF hv
    exact FactsHold.push hF (hpush env ρ v hd hfr ⟨tr₀, htr₀, hv⟩)
  have rhs : ∀ tb₀, closedAt (env.length + 1) tb₀ = true →
      FactRefines env.length (FactsHold P Γ env) (.Apply (.Lam 0 tb₀) tr) (.Apply (.Lam 0 tb₀) tr') :=
    fun tb₀ c₀ => factRefines_apply (FactRefines.refl _ _ _) hrr (by simp [closedAt, c₀]) closedTr
  rcases htrf_eq with rfl | rfl
  · exact (body trf htrf closedTr).trans (rhs tb' closedTb')
  · exact (rhs tb closedTb).trans (body trf htrf closedTr')

theorem lowerTotalExpr_let_cons (env : List VarId) (binding : VarId × Expr × Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) :
    lowerTotalExpr env (.Let (binding :: rest) body) =
      lowerTotalExpr env (.Let [binding] (.Let rest body)) := by
  obtain ⟨x, r, er⟩ := binding
  simp only [lowerTotalExpr, expandFix, expandFixBinds, lowerTotal, lowerTotalLet]

theorem freshIn_let_cons (avoid : List VarId) (binding : VarId × Expr × Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) :
    freshIn avoid (.Let (binding :: rest) body) = freshIn avoid (.Let [binding] (.Let rest body)) := by
  obtain ⟨x, r, er⟩ := binding
  simp only [freshIn, freshInLet]

theorem lowerTotalExpr_let_nil (env : List VarId) (body : Expr) :
    lowerTotalExpr env (.Let [] body) = lowerTotalExpr env body := by
  simp only [lowerTotalExpr, expandFix, expandFixBinds, lowerTotal, lowerTotalLet]

theorem freshIn_let_nil (avoid : List VarId) (body : Expr) :
    freshIn avoid (.Let [] body) = freshIn avoid body := by
  simp only [freshIn, freshInLet]

/-- Replace the source by one with the same lowerings and freshness. -/
theorem FactRel.congr_left {G : VarId → Prop} {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} {e₀ e e' : Expr} (h : FactRel G P Γ e₀ e')
    (hlow : ∀ env, lowerTotalExpr env e = lowerTotalExpr env e₀)
    (hfresh : ∀ avoid, freshIn avoid e = freshIn avoid e₀) : FactRel G P Γ e e' := by
  intro env t hG hd hf hk hs ht
  rw [hfresh] at hf; rw [hlow] at ht
  exact h env t hG hd hf hk hs ht

theorem FactRel.congr_right {G : VarId → Prop} {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} {e e₀ e' : Expr} (h : FactRel G P Γ e e₀)
    (hlow : ∀ env, lowerTotalExpr env e' = lowerTotalExpr env e₀) : FactRel G P Γ e e' := by
  intro env t hG hd hf hk hs ht
  obtain ⟨t', ht', hr⟩ := h env t hG hd hf hk hs ht
  exact ⟨t', by rw [hlow]; exact ht', hr⟩

end Moist.Verified.ShapeFacts
