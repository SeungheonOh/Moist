import Moist.Verified.RecordsSoundness.Replace

variable [sv : Moist.CEK.SemVariant]

/-! # Entering several binders with facts

Binding the names `qs` (newest first) in front of an environment, with the
facts `qs.zip bs` recorded in the outer environment, preserves the
invariants of `FactRel` (`KeysBound.bind`, `FactsScoped.bind`). A term that
does not mention the new names evaluates alike before and after them
(`obsRefines_bind_unused`).
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.BetaValueRefines
open Moist.Verified.Contextual

omit sv in
theorem envLookupT_append_isSome {env : List VarId} {x : VarId} (h : (envLookupT env x).isSome = true) :
    ∀ (names : List VarId), (envLookupT (names ++ env) x).isSome = true
  | [] => by simpa using h
  | y :: ys => by
    rw [List.cons_append, envLookupT_cons]
    split
    · rfl
    · simpa using envLookupT_append_isSome h ys

omit sv in
theorem KeysBound.bind {Γ₀ : List (VarId × Expr)} {env : List VarId} (qs : List VarId) (bs : List Expr)
    (hk : KeysBound Γ₀ env) : KeysBound (qs.zip bs ++ Γ₀) (qs ++ env) := by
  intro entry hmem
  rcases List.mem_append.mp hmem with hz | hΓ
  · have hq := List.of_mem_zip hz
    obtain ⟨j, hj, hjx⟩ := List.mem_iff_getElem.mp hq.1
    have : (envLookupT qs entry.1).isSome = true := by
      cases hl : envLookupT qs entry.1 with
      | some _ => rfl
      | none =>
        rw [envLookupT_none_iff] at hl
        have := hl qs[j] (List.getElem_mem hj)
        rw [hjx, varId_beq_self] at this; cases this
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp this
    rw [envLookupT_append_of_some hi]; rfl
  · exact envLookupT_append_isSome (hk entry hΓ) qs

omit sv in
theorem FactsScoped.bind {Γ₀ : List (VarId × Expr)} {env : List VarId} (qs : List VarId) (bs : List Expr)
    (h : FactsScoped Γ₀ env) (hbs : qs.length = bs.length)
    (hlow : ∀ b ∈ bs, (lowerTotalExpr env b).isSome = true) :
    FactsScoped (qs.zip bs ++ Γ₀) (qs ++ env) := by
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
    refine ⟨qs.length, hjlt, by simp, ?_⟩
    rw [List.drop_left]
    exact hlow e.2 (List.mem_of_getElem? hb)
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
      obtain ⟨k, hik, hk, hs⟩ := h y entry i₀ hf hl₀
      refine ⟨qs.length + k, by omega, by simp; omega, ?_⟩
      rw [← List.drop_drop, List.drop_left]
      exact hs

omit sv in
theorem zip_map_self (names : List VarId) (f : VarId → Expr) :
    names.zip (names.map f) = names.map fun y => (y, f y) := by
  induction names with
  | nil => rfl
  | cons y ys ih => simp [ih]

omit sv in
theorem EnvDistinct.append : ∀ {names env : List VarId}, NamesDistinct names → EnvDistinct env →
    (∀ y ∈ names, envLookupT env y = none) → EnvDistinct (names ++ env)
  | [], env, _, hd, _ => hd
  | y :: ys, env, hn, hd, hout => by
    rw [List.cons_append]
    apply EnvDistinct.cons (EnvDistinct.append hn.tail hd fun z hz => hout z (.tail _ hz))
    rw [envLookupT_append_of_none]
    · rw [hout y (.head _)]; rfl
    · rw [envLookupT_none_iff]
      intro z hz
      cases hzy : (z == y) with
      | false => rfl
      | true =>
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hz
        have := hn (j + 1) 0 ys[j] y (by simp [hj]) rfl hzy
        omega

omit sv in
/-- Binders of a lambda telescope that is fresh for an environment are distinct. -/
theorem lambdas_distinct {binders : List VarId} {body : Expr} {env : List VarId}
    (h : freshIn env (lambdas binders body) = true) : NamesDistinct binders := by
  obtain ⟨hall, _⟩ := (freshIn_lambdas binders body env).mp h
  intro i j a b ha hb hab
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · exfalso
    have := hall j b hb
    rw [Option.isNone_iff_eq_none, envLookupT_none_iff] at this
    have hmem : a ∈ (binders.take j).reverse ++ env := by
      apply List.mem_append_left
      rw [List.mem_reverse, List.mem_iff_getElem?]
      exact ⟨i, by rw [List.getElem?_take, if_pos hij]; exact ha⟩
    rw [this a hmem] at hab; cases hab
  · rfl
  · exfalso
    have := hall i a ha
    rw [Option.isNone_iff_eq_none, envLookupT_none_iff] at this
    have hmem : b ∈ (binders.take i).reverse ++ env := by
      apply List.mem_append_left
      rw [List.mem_reverse, List.mem_iff_getElem?]
      exact ⟨j, by rw [List.getElem?_take, if_pos hij]; exact hb⟩
    have hba := this b hmem
    rw [varId_beq_symm hab] at hba
    cases hba

omit sv in
theorem lambdas_outside {binders : List VarId} {body : Expr} {env : List VarId}
    (h : freshIn env (lambdas binders body) = true) : ∀ y ∈ binders, envLookupT env y = none := by
  obtain ⟨hall, _⟩ := (freshIn_lambdas binders body env).mp h
  intro y hy
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
  have := hall j binders[j] (by simp [hj])
  rw [Option.isNone_iff_eq_none, envLookupT_none_iff] at this
  rw [envLookupT_none_iff]
  intro z hz
  exact this z (List.mem_append_right _ hz)

omit sv in
/-- A telescope of fresh, distinct binders is fresh. -/
theorem freshIn_lambdas_of {binders : List VarId} {body : Expr} {env : List VarId}
    (hd : NamesDistinct binders) (hout : ∀ y ∈ binders, envLookupT env y = none)
    (hbody : freshIn (binders.reverse ++ env) body = true) : freshIn env (lambdas binders body) = true := by
  refine (freshIn_lambdas binders body env).mpr ⟨?_, hbody⟩
  intro j x hx
  rw [Option.isNone_iff_eq_none, envLookupT_none_iff]
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · cases hzx : (z == x) with
    | false => rfl
    | true =>
      rw [List.mem_reverse, List.mem_iff_getElem?] at hz
      obtain ⟨i, hi⟩ := hz
      rw [List.getElem?_take] at hi
      split at hi
      · have := hd i j z x hi hx hzx; omega
      · cases hi
  · have hxenv := hout x (List.mem_of_getElem? hx)
    rw [envLookupT_none_iff] at hxenv
    exact hxenv z hz |> fun h => by
      cases hzx : (z == x) with
      | false => rfl
      | true => rw [h] at hzx; cases hzx

/-- A term that does not mention the new binders evaluates alike after them. -/
theorem obsRefines_bind_unused : ∀ (names : List VarId) (fields : List CekValue) {env : List VarId}
    {ρ : CekEnv} {π : Stack} {e : Expr} {t t' : Term},
    fields.length = names.length → (∀ y ∈ names, (freeVars e).contains y = false) →
    lowerTotalExpr env e = some t → lowerTotalExpr (names.reverse ++ env) e = some t' →
    EnvWellFormed env.length ρ → env.length ≤ ρ.length → ValueListWellFormed fields →
    StackWellFormed π → ObsRefines (.compute π ρ t) (.compute π (extendAll ρ fields) t')
  | [], [], env, ρ, π, e, t, t', _, _, ht, ht', _, _, _, _ => by
    simp only [List.reverse_nil, List.nil_append] at ht'
    rw [ht] at ht'; cases ht'
    exact obsRefines_refl _
  | y :: ys, f :: fs, env, ρ, π, e, t, t', hlen, hfree, ht, ht', henv, hlenv, .cons hf hfs, hπ => by
    have hy := hfree y (.head _)
    have hty : lowerTotalExpr (y :: env) e = some (renameTerm (shiftRename 1) t) := by
      rw [MIR.lowerTotalExpr_prepend_unused _ y e hy, ht]; rfl
    have closedT := MIR.lowerTotalExpr_closedAt ht
    refine obsRefines_trans (obsEq_shift f henv hπ closedT).1 ?_
    simp only [extendAll]
    exact obsRefines_bind_unused ys fs (env := y :: env) (by simpa using hlen)
      (fun z hz => hfree z (.tail _ hz)) hty (by simpa using ht')
      (envWellFormed_extend env.length henv hlenv hf) (by simp [CekEnv.extend, CekEnv.length]; omega)
      hfs hπ
  | [], _ :: _, _, _, _, _, _, _, hlen, _, _, _, _, _, _, _ => by simp at hlen
  | _ :: _, [], _, _, _, _, _, _, hlen, _, _, _, _, _, _, _ => by simp at hlen

end Moist.Verified.ShapeFacts
