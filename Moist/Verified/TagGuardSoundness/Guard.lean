import Moist.Verified.TagGuardSoundness.Abstract
import Moist.Verified.ShapesSoundness.Choices

/-! # Soundness of guard trees

A guard tree `case x [λtag fields. case tag [t₀ … tₙ]]` that `guardOK`
accepts fails only where the guarded expression cannot halt, and returns the
unit constant otherwise, provided every variable it inspects holds a pair
whose first component is an integer (the result of `unConstrData`).
-/

namespace Moist.Verified.TagGuard

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast

/-- `x` is bound in `env` to `v` at runtime. -/
def ValIn (env : List VarId) (ρ : CekEnv) (x : VarId) (v : CekValue) : Prop :=
  ∃ i, envLookupT env x = some i ∧ ρ.lookup (i + 1) = some v

/-! ## Updating hypotheses -/

theorem replaceFirst_map_fst (x : VarId) (a : AVal) :
    ∀ (L : List (VarId × AVal)), (replaceFirst x a L).map Prod.fst = L.map Prod.fst
  | [] => rfl
  | (y, b) :: L => by
    simp only [replaceFirst]
    split
    · rfl
    · simp [replaceFirst_map_fst x a L]

theorem replaceFirst_length (x : VarId) (a : AVal) (L : List (VarId × AVal)) :
    (replaceFirst x a L).length = L.length := by
  have := congrArg List.length (replaceFirst_map_fst x a L)
  simpa using this

theorem replaceFirst_get (x : VarId) (a : AVal) :
    ∀ (L : List (VarId × AVal)) {j : Nat}, envLookupT (L.map Prod.fst) x = some j →
      ∀ k (hk : k < L.length),
        ((replaceFirst x a L)[k]'(by rw [replaceFirst_length]; exact hk)).2 =
          if k = j then a else (L[k]).2
  | [], _, h, _, hk => by simp at hk
  | (y, b) :: L, j, h, k, hk => by
    rw [List.map_cons, envLookupT_cons] at h
    by_cases hyx : (y == x) = true
    · rw [if_pos hyx] at h; cases h
      simp only [replaceFirst, hyx, if_true]
      cases k with
      | zero => simp
      | succ k => simp
    · rw [if_neg hyx] at h
      cases hl : envLookupT (L.map Prod.fst) x with
      | none => rw [hl] at h; cases h
      | some j' =>
        rw [hl] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
        simp only [replaceFirst, hyx, Bool.false_eq_true, if_false]
        cases k with
        | zero => simp
        | succ k =>
          simp only [List.getElem_cons_succ]
          rw [replaceFirst_get x a L hl k (by simp at hk; omega)]
          simp

theorem lookupAVal_cons_self {x : VarId} {a : AVal} {H : List (VarId × AVal)} {y : VarId}
    (h : (x == y) = true) : lookupAVal ((x, a) :: H) y = some a := by
  simp [lookupAVal, List.find?_cons, h]

theorem lookupAVal_cons_other {x : VarId} {a : AVal} {H : List (VarId × AVal)} {y : VarId}
    (h : (x == y) = false) : lookupAVal ((x, a) :: H) y = lookupAVal H y := by
  simp [lookupAVal, List.find?_cons, h]

theorem Ctx.assume {Γ : List (VarId × Expr)} {H L : List (VarId × AVal)} {outer : List VarId}
    {ρ : CekEnv} (hctx : Ctx Γ H L outer ρ) {x : VarId} {a : AVal} {v : CekValue}
    (hv : ValIn (L.map Prod.fst ++ outer) ρ x v) (ha : a.Holds v) :
    Ctx Γ (assume H L x a).1 (assume H L x a).2 outer ρ := by
  obtain ⟨i, hi, hvi⟩ := hv
  unfold Moist.MIR.Advanced.assume
  split
  · rename_i hany
    obtain ⟨j, hj⟩ : ∃ j, envLookupT (L.map Prod.fst) x = some j := by
      cases hl : envLookupT (L.map Prod.fst) x with
      | some j => exact ⟨j, rfl⟩
      | none =>
        exfalso
        obtain ⟨e, he, hex⟩ := List.any_eq_true.mp hany
        have hmem : e.1 ∈ L.map Prod.fst := List.mem_map_of_mem he
        have := envLookupT_none_iff.mp hl e.1 hmem
        rw [this] at hex; cases hex
    rw [envLookupT_append_of_some hj] at hi; cases hi
    refine ⟨hctx.distinct, by simpa [replaceFirst_length] using hctx.facts,
      by simpa [replaceFirst_length] using hctx.hyps, fun k hk => ?_⟩
    have hk' : k < L.length := by rw [replaceFirst_length] at hk; exact hk
    rw [replaceFirst_get x a L hj k hk']
    split
    · rename_i hkj; subst hkj; exact ⟨v, hvi, ha⟩
    · exact hctx.locals k hk'
  · rename_i hany
    have hnone : envLookupT (L.map Prod.fst) x = none := by
      cases hl : envLookupT (L.map Prod.fst) x with
      | none => rfl
      | some j =>
        exfalso
        simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at hany
        obtain ⟨y, hy, hyx⟩ := envLookupT_mem hl
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
        rw [hany e he] at hyx; cases hyx
    rw [envLookupT_append_of_none hnone] at hi
    cases hio : envLookupT outer x with
    | none => rw [hio] at hi; cases hi
    | some i' =>
      rw [hio] at hi
      simp only [Option.map_some, Option.some.injEq, List.length_map] at hi
      subst hi
      refine ⟨hctx.distinct, hctx.facts, ?_, hctx.locals⟩
      intro y b hb k hk
      by_cases hxy : (x == y) = true
      · rw [lookupAVal_cons_self hxy] at hb; cases hb
        rw [← envLookupT_congr hxy outer, hio] at hk
        cases hk
        refine ⟨v, ?_, ha⟩
        rw [dropEnv_lookup _ ρ _ (by omega), show i' + 1 + L.length = i' + L.length + 1 by omega]
        exact hvi
      · rw [lookupAVal_cons_other (by simpa using hxy)] at hb
        exact hctx.hyps y b hb k hk

/-! ## Guard trees -/

theorem lowerTotalExprList_getElem?' {env : List VarId} :
    ∀ {es : List Expr} {ts : List Term}, MIR.lowerTotalExprList env es = some ts →
      ∀ n : Nat, (∃ e t, es[n]? = some e ∧ ts[n]? = some t ∧ lowerTotalExpr env e = some t) ∨
        (es[n]? = none ∧ ts[n]? = none)
  | [], ts, h, n => by rw [MIR.lowerTotalExprList_nil] at h; cases h; exact .inr ⟨rfl, rfl⟩
  | e :: es, ts, h, n => by
    rw [MIR.lowerTotalExprList_cons] at h
    cases he : lowerTotalExpr env e <;> cases hes : MIR.lowerTotalExprList env es <;>
      simp [he, hes] at h
    subst h
    cases n with
    | zero => exact .inl ⟨e, _, rfl, rfl, he⟩
    | succ n => simpa using lowerTotalExprList_getElem?' hes n

def IntVal (v : CekValue) : Prop := ∃ n : Int, v = .VCon (.Integer n)

mutual
  def gAllVars (P : VarId → Prop) : GuardTree → Prop
    | .split x alternatives => P x ∧ gAllVarsList P alternatives
    | _ => True

  def gAllVarsList (P : VarId → Prop) : List GuardTree → Prop
    | [] => True
    | t :: rest => gAllVars P t ∧ gAllVarsList P rest
end

theorem gAllVarsList_get {P : VarId → Prop} :
    ∀ {ts : List GuardTree}, gAllVarsList P ts → ∀ k (h : k < ts.length), gAllVars P ts[k]
  | [], _, _, h => by simp at h
  | t :: rest, ⟨ht, hrest⟩, k, h => by
    cases k with
    | zero => exact ht
    | succ k => exact gAllVarsList_get hrest k (by simp at h; omega)

theorem guardOKList_get {fuel : Nat} {Γ : List (VarId × Expr)} {M : Expr}
    {H L : List (VarId × AVal)} {x : VarId} :
    ∀ {m : Nat} {ts : List GuardTree}, guardOKList fuel Γ M H L x m ts = true →
      ∀ k (h : k < ts.length),
        guardOK fuel Γ M (assume H L x (.int (.exact (Int.ofNat (m + k))))).1
          (assume H L x (.int (.exact (Int.ofNat (m + k))))).2 ts[k] = true
  | m, [], _, k, h => by simp at h
  | m, t :: rest, hok, k, h => by
    rw [guardOKList, Bool.and_eq_true] at hok
    cases k with
    | zero => simpa using hok.1
    | succ k =>
      have := guardOKList_get hok.2 k (by simp at h; omega)
      simpa [show m + 1 + k = m + (k + 1) by omega] using this

theorem tagRange_mem {n : Int} {count : Nat} : n ∈ tagRange count ↔ 0 ≤ n ∧ n < count := by
  simp only [tagRange, List.mem_map, List.mem_range, Int.ofNat_eq_coe]
  constructor
  · rintro ⟨k, hk, rfl⟩; omega
  · intro h; exact ⟨n.toNat, by omega, by omega⟩

theorem assume_map_fst (H L : List (VarId × AVal)) (x : VarId) (a : AVal) :
    (assume H L x a).2.map Prod.fst = L.map Prod.fst := by
  unfold Moist.MIR.Advanced.assume; split
  · exact replaceFirst_map_fst x _ L
  · rfl

/-- A guard tree fails only where `M` cannot halt, and otherwise returns unit. -/
theorem guard_sound {fuel : Nat} {Γ : List (VarId × Expr)} {M : Expr} {outer : List VarId}
    {ρ : CekEnv} {tM : Term} :
    ∀ (N : Nat) (T : GuardTree) (H L : List (VarId × AVal)), sizeOf T < N →
      lowerTotalExpr (L.map Prod.fst ++ outer) M = some tM →
      guardOK fuel Γ M H L T = true → Ctx Γ H L outer ρ →
      gAllVars (fun x => ∃ v, ValIn (L.map Prod.fst ++ outer) ρ x v ∧ IntVal v) T →
      ∀ tT, lowerTotalExpr (L.map Prod.fst ++ outer) T.toExpr = some tT →
        (Errs ρ tT → ¬ ∃ v, Halts ρ tM v) ∧ (∀ w, Halts ρ tT w → w = .VCon .Unit)
  | 0, _, _, _, h, _, _, _, _ => absurd h (by omega)
  | N + 1, T, H, L, hsize, hM, hok, hctx, hvars => by
    intro tT hlow
    cases T with
    | ok =>
      rw [GuardTree.toExpr, unitExpr, lowerTotalExpr_lit] at hlow; cases hlow
      refine ⟨fun he => absurd he (fun he => halt_not_error (reaches_of_steps 2 rfl) he), fun w hw => ?_⟩
      exact halts_constant hw
    | fail =>
      rw [GuardTree.toExpr, lowerTotalExpr_error] at hlow; cases hlow
      refine ⟨fun _ => ?_, fun w hw => absurd hw not_halts_error⟩
      rw [guardOK, Option.isNone_iff_eq_none] at hok
      have := (aeval_sound Γ H fuel M).1 L outer ρ tM hctx hM
      rw [hok] at this
      exact this
    | split x ts =>
      obtain ⟨⟨vx, hvx, n, rfl⟩, hvarsList⟩ := hvars
      rw [guardOK, Bool.and_eq_true] at hok
      obtain ⟨hnotin, hlist⟩ := hok
      simp only [GuardTree.toExpr] at hlow
      obtain ⟨tsc, talts, htsc, htalts, rfl⟩ := lowerTotalExpr_case_some hlow
      obtain ⟨i, hi, rfl⟩ := lowerTotalExpr_var_some htsc
      have hlook : ρ.lookup (i + 1) = some (.VCon (.Integer n)) := by
        obtain ⟨i', hi', hl'⟩ := hvx
        rw [hi] at hi'; cases hi'; exact hl'
      have hreach : Reaches (.compute [] ρ (.Case (.Var (i + 1)) talts))
          (step (.ret [.caseScrutinee talts ρ] (.VCon (.Integer n)))) := by
        have h2 : Reaches (.compute [] ρ (.Case (.Var (i + 1)) talts))
            (.ret [.caseScrutinee talts ρ] (.VCon (.Integer n))) :=
          reaches_of_steps 2 (by simp [steps, step, hlook])
        exact reaches_trans h2 (reaches_of_steps 1 rfl)
      rw [step_caseScrutinee, dispatch_int] at hreach
      have hmap : ts.attach.map (fun ⟨t, _⟩ => t.toExpr) = ts.map GuardTree.toExpr := by simp
      rw [hmap] at htalts
      have hlenT := lowerTotalExprList_len htalts
      simp only [List.length_map] at hlenT
      by_cases hin : 0 ≤ n ∧ n < ts.length
      · rw [if_neg (by omega)] at hreach
        have hk : n.toNat < ts.length := by omega
        obtain ⟨ta, hta, hlta⟩ : ∃ ta, talts[n.toNat]? = some ta ∧
            lowerTotalExpr (L.map Prod.fst ++ outer) ts[n.toNat].toExpr = some ta := by
          rcases lowerTotalExprList_getElem?' htalts n.toNat with ⟨e', t', he', ht', hl'⟩ | ⟨he', _⟩
          · rw [List.getElem?_map, List.getElem?_eq_getElem hk] at he'
            cases he'
            exact ⟨t', ht', hl'⟩
          · rw [List.getElem?_map, List.getElem?_eq_getElem hk] at he'; cases he'
        rw [hta] at hreach
        simp only [Option.map_some, List.map_nil, List.nil_append] at hreach
        have hctx' := hctx.assume (a := .int (.exact n)) hvx rfl
        have hn' : Int.ofNat (0 + n.toNat) = n := by
          rw [Nat.zero_add, Int.ofNat_eq_coe, Int.toNat_of_nonneg (by omega)]
        have hok' := guardOKList_get hlist n.toNat hk
        rw [hn'] at hok'
        have hmapL := assume_map_fst H L x (.int (.exact n))
        have hsz : sizeOf ts[n.toNat] < N := by
          have := List.sizeOf_lt_of_mem (List.getElem_mem hk)
          simp only [GuardTree.split.sizeOf_spec] at hsize; omega
        have ih := guard_sound N ts[n.toNat] _ _ hsz (by rw [hmapL]; exact hM) hok' hctx'
          (by rw [hmapL]; exact gAllVarsList_get hvarsList _ hk) ta (by rw [hmapL]; exact hlta)
        refine ⟨fun he => ih.1 (reaches_terminal_after (.inl rfl) hreach he), fun w hw => ?_⟩
        exact ih.2 w (reaches_terminal_after (.inr ⟨w, rfl⟩) hreach hw)
      · have hnot : ¬ ∃ v, Halts ρ tM v := by
          have hctx' := hctx.assume (a := .int (.notIn (tagRange ts.length))) hvx
            ⟨n, rfl, fun hm => hin ((tagRange_mem).mp hm)⟩
          have hmapL := assume_map_fst H L x (.int (.notIn (tagRange ts.length)))
          have := (aeval_sound Γ _ fuel M).1 _ outer ρ tM hctx' (by rw [hmapL]; exact hM)
          simp only [Option.isNone_iff_eq_none] at hnotin
          rw [hnotin] at this
          exact this
        have herr : Reaches (.compute [] ρ (.Case (.Var (i + 1)) talts)) .error := by
          by_cases hneg : n < 0
          · rw [if_pos hneg] at hreach; exact hreach
          · rw [if_neg hneg] at hreach
            cases hta : talts[n.toNat]? with
            | none => rw [hta] at hreach; exact hreach
            | some _ =>
              exfalso
              have h1 := (List.getElem?_eq_some_iff.mp hta).1
              exact hin ⟨by omega, by omega⟩
        exact ⟨fun _ => hnot, fun w hw => absurd hw (fun hw => halt_not_error hw herr)⟩

end Moist.Verified.TagGuard
