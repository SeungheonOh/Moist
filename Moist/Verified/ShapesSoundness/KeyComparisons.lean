import Moist.Verified.ShapesSoundness.KeyGuards
import Moist.Verified.ShapesSoundness.Choices

variable [sv : Moist.CEK.SemVariant]

/-! # Comparisons against guarded keys

`keyComparison` replaces `case (equalsData d x) [miss, hit]`, where the facts
record the guards of `d` (`keyGuardFor`), by the guarded comparison of `x`
with the bytes of `d`. Under facts that hold, the guards hold the values
`KeyGuards` computes (`keyGuard_values`), so the guarded comparison selects
the alternative `equalsData` selects, or fails where `equalsData` fails
(`keyComparison_factRel`).
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines

/-! ## Recorded bindings -/

omit sv in
theorem bindingOf_some {Γ : List (VarId × Expr)} {x : VarId} {rhs : Expr} (h : bindingOf Γ x = some rhs) :
    ∃ x', Γ.find? (fun entry => entry.1 == x) = some (x', rhs) := by
  unfold bindingOf at h
  cases hf : Γ.find? (fun entry => entry.1 == x) with
  | none => rw [hf] at h; cases h
  | some entry =>
    rw [hf] at h
    obtain ⟨x', r⟩ := entry
    cases h
    exact ⟨x', rfl⟩

omit sv in
theorem bindingOf_bound {Γ : List (VarId × Expr)} {env : List VarId} {x : VarId} {rhs : Expr}
    (h : bindingOf Γ x = some rhs) (hk : KeysBound Γ env) : ∃ i, envLookupT env x = some i := by
  obtain ⟨x', hf⟩ := bindingOf_some h
  have hmem := List.mem_of_find?_eq_some hf
  have hbeq : (x' == x) = true := by simpa using List.find?_some hf
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (hk _ hmem)
  exact ⟨i, by rw [← envLookupT_congr hbeq]; exact hi⟩

/-- The value of a binder recorded with `rhs`, and `rhs` returning it where it
    was evaluated. -/
theorem binding_value {Γ : List (VarId × Expr)} {env : List VarId} {ρ : CekEnv} {x : VarId}
    {rhs : Expr} {ix : Nat} (hF : FactsHold Produces Γ env ρ) (hb : bindingOf Γ x = some rhs)
    (hx : envLookupT env x = some ix) :
    ∃ v j, ρ.lookup (ix + 1) = some v ∧ ix < j ∧ j ≤ env.length ∧
      Produces (env.drop j) (dropEnv j ρ) rhs v := by
  obtain ⟨x', hf⟩ := bindingOf_some hb
  obtain ⟨v, j, hij, hj, hv, hp⟩ := hF x (x', rhs) ix hf hx
  exact ⟨v, j, hv, hij, hj, hp⟩

/-- A variable of an older suffix holds the value it holds in the whole
    environment. -/
theorem drop_var {env : List VarId} {ρ : CekEnv} {j : Nat} {y : VarId} {i : Nat}
    (hd : EnvDistinct env) (hi : envLookupT (env.drop j) y = some i) :
    envLookupT env y = some (i + j) ∧ (dropEnv j ρ).lookup (i + 1) = ρ.lookup (i + j + 1) := by
  refine ⟨hd.drop_lookup j hi, ?_⟩
  rw [dropEnv_lookup j ρ _ (by omega)]
  congr 1; omega

/-- A unary builtin applied to a variable returns the builtin's result on the
    variable's value. -/
theorem unary_var_produces {env : List VarId} {ρ : CekEnv} {b : BuiltinFun} {y : VarId} {v : CekValue}
    (hb : expectedArgs b = .one .argV)
    (h : Produces env ρ (.App (.Builtin b) (.Var y)) v) :
    ∃ i vy, envLookupT env y = some i ∧ ρ.lookup (i + 1) = some vy ∧ evalBuiltin b [vy] = some v := by
  obtain ⟨t, ht, hv⟩ := h
  obtain ⟨tf, ta, htf, hta, rfl⟩ := lowerTotalExpr_app_some ht
  rw [lowerTotalExpr_builtin] at htf; cases htf
  obtain ⟨i, hi, rfl⟩ := lowerTotalExpr_var_some hta
  obtain ⟨wf, wa, hwf, hwa, rest⟩ := halts_apply hv
  rw [halts_builtin hwf] at rest
  have hva := halts_var hwa
  refine ⟨i, wa, hi, hva, ?_⟩
  rw [hb] at rest
  obtain ⟨args, hlen, heval⟩ := saturated_apply ⟨[], rfl, by rw [hb]; rfl⟩ rest
  have h1 : valueArity (expectedArgs b) = 1 := by rw [hb]; rfl
  rw [h1] at hlen
  have : args = [] := by
    cases args with
    | nil => rfl
    | cons _ _ => simp at hlen
  subst this
  exact heval

theorem unBData_result {w v : CekValue} (h : evalBuiltin .UnBData [w] = some v) :
    ∃ kb, w = .VCon (.Data (.B kb)) ∧ v = .VCon (.ByteString kb) := by
  obtain ⟨c, r, rfl, hc, rfl⟩ := evalBuiltin_single (by decide) h
  cases c with
  | Data dd =>
    cases dd
    all_goals first | (cases hc; done) | exact ⟨_, rfl, by cases hc; rfl⟩
  | _ => cases hc

omit sv in
theorem otherLengthTest_some {rhs : Expr} {lt : VarId} (h : otherLengthTest rhs = some lt) :
    ∃ e z, rhs = .Case (.App (.Var lt) (.Lit (.Integer 0, .AtomicType .TypeInteger)))
      [.Lit (.Data (.B e), .AtomicType .TypeData), .Lit (.Data (.B z), .AtomicType .TypeData)] ∧
      e.size = 0 ∧ z.size = 1 := by
  unfold otherLengthTest at h
  split at h
  · rename_i lt' e z
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨e, z, rfl, hc.1, hc.2⟩
    · cases h
  · cases h

omit sv in
theorem lengthTestKey_some {Γ : List (VarId × Expr)} {lt k : VarId} (h : lengthTestKey Γ lt = some k) :
    bindingOf Γ lt = some (.App (.Builtin .EqualsInteger) (.App (.Builtin .LengthOfByteString) (.Var k))) := by
  unfold lengthTestKey at h
  split at h
  · rename_i hb; cases h; exact hb
  · cases h

omit sv in
theorem keySource_some {Γ : List (VarId × Expr)} {k src : VarId} (h : keySource Γ k = some src) :
    bindingOf Γ k = some (.App (.Builtin .UnBData) (.Var src)) := by
  unfold keySource at h
  split at h
  · rename_i hb; cases h; exact hb
  · cases h

omit sv in
theorem keyGuardFor_spec {Γ : List (VarId × Expr)} {source lt cmp oth : VarId}
    (h : keyGuardFor Γ source = some (lt, cmp, oth)) :
    ∃ e z k src rhsC,
      bindingOf Γ oth = some (.Case (.App (.Var lt) (.Lit (.Integer 0, .AtomicType .TypeInteger)))
        [.Lit (.Data (.B e), .AtomicType .TypeData), .Lit (.Data (.B z), .AtomicType .TypeData)]) ∧
      e.size = 0 ∧ z.size = 1 ∧
      bindingOf Γ lt = some (.App (.Builtin .EqualsInteger) (.App (.Builtin .LengthOfByteString) (.Var k))) ∧
      bindingOf Γ k = some (.App (.Builtin .UnBData) (.Var src)) ∧ (src == source) = true ∧
      bindingOf Γ cmp = some rhsC ∧ isGuardCompare source k rhsC = true := by
  unfold keyGuardFor at h
  obtain ⟨entry, _, hentry⟩ := List.exists_of_findSome?_eq_some h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hentry
  obtain ⟨rhsN, hN, lt', hlt', k, hk, src, hsrc, hrest⟩ := hentry
  split at hrest
  · rename_i hss
    simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hrest
    obtain ⟨cand, hcand, rfl, rfl, rfl⟩ := hrest
    obtain ⟨e, z, rfl, he, hz⟩ := otherLengthTest_some hlt'
    have hc := List.find?_some hcand
    simp only [Option.any_eq_true] at hc
    obtain ⟨rhsC, hbc, hgc⟩ := hc
    exact ⟨e, z, k, src, rhsC, hN, he, hz, lengthTestKey_some hk, keySource_some hsrc, hss, hbc, hgc⟩
  · cases hrest

omit sv in
theorem beq_false_congr {a b c : VarId} (hab : (a == b) = true) (hc : (c == a) = false) :
    (c == b) = false := by
  rw [VarId.beq_true_iff] at hab
  rw [VarId.beq_false_iff] at hc ⊢
  rcases hc with h | h
  · exact .inl (by rw [← hab.1]; exact h)
  · exact .inr (by rw [← hab.2]; exact h)

omit sv in
theorem isGuardCompare_spec {source k : VarId} {rhs : Expr} (h : isGuardCompare source k rhs = true) :
    ∃ lk ety units cty hb tb ck y cs y',
      rhs = .Case (.App (.App (.Force (.Builtin .DropList)) (.App (.Builtin .LengthOfByteString) (.Var lk)))
          (.Lit (.ConstList ety units, cty)))
        [.Lam hb (.Lam tb (.App (.Builtin .EqualsByteString) (.Var ck))),
         .Lam y (.App (.App (.Builtin .EqualsData) (.Var cs)) (.App (.Builtin .BData) (.Var y')))] ∧
      (lk == k) = true ∧ (ck == k) = true ∧ (cs == source) = true ∧ (y' == y) = true ∧
      (hb == k) = false ∧ (tb == k) = false ∧ (y == source) = false ∧ units.length ≤ keyGuardBound := by
  unfold isGuardCompare at h
  split at h
  · rename_i lk ety units cty hb tb ck y cs y'
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
    exact ⟨lk, ety, units, cty, hb, tb, ck, y, cs, y', rfl, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · cases h

omit sv in
/-- The lowering of a recorded comparison. -/
theorem lower_compareShape {env : List VarId} {k source lk ck cs hb tb y y' : VarId} {ety cty : BuiltinType}
    {units : List Const} {ik is : Nat} (hk : envLookupT env k = some ik)
    (hs : envLookupT env source = some is)
    (hlk : (lk == k) = true) (hck : (ck == k) = true) (hcs : (cs == source) = true) (hy : (y' == y) = true)
    (hhb : (hb == k) = false) (htb : (tb == k) = false) (hys : (y == source) = false) :
    lowerTotalExpr env (.Case (.App (.App (.Force (.Builtin .DropList)) (.App (.Builtin .LengthOfByteString)
        (.Var lk))) (.Lit (.ConstList ety units, cty)))
      [.Lam hb (.Lam tb (.App (.Builtin .EqualsByteString) (.Var ck))),
       .Lam y (.App (.App (.Builtin .EqualsData) (.Var cs)) (.App (.Builtin .BData) (.Var y')))]) =
      some (compareTermWith (.ConstList ety units, cty) ik is) := by
  have hlk' : envLookupT env lk = some ik := by rw [envLookupT_congr hlk]; exact hk
  have hck₂ : envLookupT (tb :: hb :: env) ck = some (ik + 2) := by
    rw [envLookupT_congr hck, envLookupT_cons_neq tb k _ htb, envLookupT_cons_neq hb k env hhb, hk]; rfl
  have hcs₁ : envLookupT (y :: env) cs = some (is + 1) := by
    rw [envLookupT_congr hcs, envLookupT_cons_neq y source env hys, hs]; rfl
  have hy₁ : envLookupT (y :: env) y' = some 0 := by
    rw [envLookupT_congr hy, envLookupT_cons]; simp [varId_beq_self]
  simp [compareTermWith, slowBody, MIR.lowerTotalExpr_app, MIR.lowerTotalExpr_case_of_list,
    MIR.lowerTotalExprList_cons, MIR.lowerTotalExprList_nil, MIR.lowerTotalExpr_lam, MIR.lowerTotalExpr_force,
    lowerTotalExpr_builtin, lowerTotalExpr_var, lowerTotalExpr_lit, hlk', hck₂, hcs₁, hy₁]

omit sv in
theorem lower_length_some {env : List VarId} {k : VarId} {t : Term}
    (h : lowerTotalExpr env (.App (.Builtin .EqualsInteger) (.App (.Builtin .LengthOfByteString) (.Var k))) =
      some t) : ∃ ik, envLookupT env k = some ik ∧ t = lengthTerm ik := by
  obtain ⟨tf, ta, htf, hta, rfl⟩ := lowerTotalExpr_app_some h
  rw [lowerTotalExpr_builtin] at htf; cases htf
  obtain ⟨tg, tb, htg, htb, rfl⟩ := lowerTotalExpr_app_some hta
  rw [lowerTotalExpr_builtin] at htg; cases htg
  obtain ⟨ik, hik, rfl⟩ := lowerTotalExpr_var_some htb
  exact ⟨ik, hik, rfl⟩

omit sv in
theorem lower_other_some {env : List VarId} {lt : VarId} {e z : ByteArray} {t : Term}
    (h : lowerTotalExpr env (.Case (.App (.Var lt) (.Lit (.Integer 0, .AtomicType .TypeInteger)))
      [.Lit (.Data (.B e), .AtomicType .TypeData), .Lit (.Data (.B z), .AtomicType .TypeData)]) = some t) :
    ∃ il, envLookupT env lt = some il ∧ t = otherTermWith e z il := by
  obtain ⟨ts, talts, hts, htalts, rfl⟩ := lowerTotalExpr_case_some h
  obtain ⟨tf, ta, htf, hta, rfl⟩ := lowerTotalExpr_app_some hts
  obtain ⟨il, hil, rfl⟩ := lowerTotalExpr_var_some htf
  rw [lowerTotalExpr_lit] at hta; cases hta
  simp [MIR.lowerTotalExprList_cons, MIR.lowerTotalExprList_nil, lowerTotalExpr_lit] at htalts
  subst htalts
  exact ⟨il, hil, rfl⟩

omit sv in
theorem lower_compare_bound {env : List VarId} {lk ck cs hb tb y y' : VarId} {ety cty : BuiltinType}
    {units : List Const} {t : Term} (hys : (y == cs) = false)
    (h : lowerTotalExpr env (.Case (.App (.App (.Force (.Builtin .DropList)) (.App (.Builtin .LengthOfByteString)
        (.Var lk))) (.Lit (.ConstList ety units, cty)))
      [.Lam hb (.Lam tb (.App (.Builtin .EqualsByteString) (.Var ck))),
       .Lam y (.App (.App (.Builtin .EqualsData) (.Var cs)) (.App (.Builtin .BData) (.Var y')))]) = some t) :
    (∃ ik, envLookupT env lk = some ik) ∧ (∃ is, envLookupT env cs = some is) := by
  obtain ⟨ts, talts, hts, htalts, rfl⟩ := lowerTotalExpr_case_some h
  obtain ⟨tf, ta, htf, hta, rfl⟩ := lowerTotalExpr_app_some hts
  obtain ⟨tg, tl, htg, htl, rfl⟩ := lowerTotalExpr_app_some htf
  obtain ⟨tlb, tlv, htlb, htlv, rfl⟩ := lowerTotalExpr_app_some htl
  obtain ⟨ik, hik, rfl⟩ := lowerTotalExpr_var_some htlv
  refine ⟨⟨ik, hik⟩, ?_⟩
  rw [MIR.lowerTotalExprList_cons] at htalts
  cases h1 : lowerTotalExpr env (.Lam hb (.Lam tb (.App (.Builtin .EqualsByteString) (.Var ck)))) with
  | none => rw [h1] at htalts; cases htalts
  | some t1 =>
    rw [h1] at htalts
    rw [MIR.lowerTotalExprList_cons] at htalts
    cases h2 : lowerTotalExpr env
        (.Lam y (.App (.App (.Builtin .EqualsData) (.Var cs)) (.App (.Builtin .BData) (.Var y')))) with
    | none => rw [h2] at htalts; cases htalts
    | some t2 =>
      obtain ⟨tb2, htb2, rfl⟩ := lowerTotalExpr_lam_some h2
      obtain ⟨tq, _, htq, _, rfl⟩ := lowerTotalExpr_app_some htb2
      obtain ⟨_, tc, _, htc, rfl⟩ := lowerTotalExpr_app_some htq
      obtain ⟨ic, hic, rfl⟩ := lowerTotalExpr_var_some htc
      rw [envLookupT_cons_neq y cs env hys] at hic
      cases hcs : envLookupT env cs with
      | none => rw [hcs] at hic; cases hic
      | some is => exact ⟨is, rfl⟩

/-- Under facts that hold, the guards of a key hold the values that compare
    with its bytes. -/
theorem keyGuard_values {Γ : List (VarId × Expr)} {env : List VarId} {ρ : CekEnv}
    {source lt cmp oth : VarId} {isrc ilt icmp io : Nat}
    (h : keyGuardFor Γ source = some (lt, cmp, oth)) (hF : FactsHold Produces Γ env ρ)
    (hd : EnvDistinct env) (hk : KeysBound Γ env) (hsrc : envLookupT env source = some isrc)
    (hlt : envLookupT env lt = some ilt) (hcmp : envLookupT env cmp = some icmp)
    (hoth : envLookupT env oth = some io) :
    ∃ kb, ρ.lookup (isrc + 1) = some (.VCon (.Data (.B kb))) ∧
      ρ.lookup (ilt + 1) = some (lengthValue kb.size) ∧
      (∃ cv, ρ.lookup (icmp + 1) = some cv ∧ CompareSpec cv kb) ∧
      (∃ ob, ρ.lookup (io + 1) = some (.VCon (.Data (.B ob))) ∧ ob.size ≠ kb.size) := by
  obtain ⟨e, z, k, src, rhsC, hbN, he, hz, hbL, hbK, hss, hbC, hgc⟩ := keyGuardFor_spec h
  obtain ⟨ik, hik⟩ := bindingOf_bound hbK hk
  -- the key bytes and the key
  obtain ⟨vk, jk, hvk, _, _, hpk⟩ := binding_value hF hbK hik
  obtain ⟨is', vs, his', hvs, hev⟩ := unary_var_produces rfl hpk
  obtain ⟨kb, rfl, rfl⟩ := unBData_result hev
  obtain ⟨hsrcE, hlook⟩ := drop_var (ρ := ρ) hd his'
  rw [envLookupT_congr hss, hsrc] at hsrcE
  cases hsrcE
  rw [hlook] at hvs
  have hlength : ρ.lookup (ilt + 1) = some (lengthValue kb.size) := by
    obtain ⟨vl, jl, hvl, _, _, ⟨tl, htl, hhl⟩⟩ := binding_value hF hbL hlt
    obtain ⟨ik', hik', rfl⟩ := lower_length_some htl
    obtain ⟨hikE, hlookK⟩ := drop_var (ρ := ρ) hd hik'
    rw [hik] at hikE; cases hikE
    rw [← hlookK] at hvk
    rw [hvl, halts_unique hhl (lengthTerm_halts hvk)]
  refine ⟨kb, hvs, hlength, ?_, ?_⟩
  · -- the comparison
    obtain ⟨vc, jc, hvc, _, _, ⟨tc, htc, hhc⟩⟩ := binding_value hF hbC hcmp
    obtain ⟨lk, ety, units, cty, hb, tb, ck, y, cs, y', rfl, hlk, hck, hcs, hy, hhb, htb, hys, hunits⟩ :=
      isGuardCompare_spec hgc
    obtain ⟨⟨ik', hik'⟩, ⟨is'', his''⟩⟩ := lower_compare_bound (beq_false_congr (varId_beq_symm hcs) hys) htc
    rw [envLookupT_congr hlk] at hik'
    rw [envLookupT_congr hcs] at his''
    rw [lower_compareShape hik' his'' hlk hck hcs hy hhb htb hys] at htc
    cases htc
    · 
      obtain ⟨hikE, hlookK⟩ := drop_var (ρ := ρ) hd hik'
      rw [hik] at hikE; cases hikE
      obtain ⟨hisE, hlookS⟩ := drop_var (ρ := ρ) hd his''
      have heq : is'' + jc = is' + jk := by
        rw [envLookupT_congr hss] at his'
        have := hd.drop_lookup jk his'
        rw [this] at hisE; exact (Option.some.inj hisE).symm
      rw [heq] at hlookS
      rw [← hlookK] at hvk
      rw [← hlookS] at hvs
      refine ⟨vc, hvc, ?_⟩
      rw [halts_unique hhc (compareTermWith_halts hunits hvk)]
      exact compareValue_spec hunits hvs
  · -- the other `B` value
    obtain ⟨vo, jo, hvo, _, _, ⟨to, hto, hho⟩⟩ := binding_value hF hbN hoth
    obtain ⟨il, hil, rfl⟩ := lower_other_some hto
    obtain ⟨hilE, hlookL⟩ := drop_var (ρ := ρ) hd hil
    rw [hlt] at hilE; cases hilE
    rw [← hlookL] at hlength
    rw [halts_unique hho (otherTermWith_halts hlength)] at hvo
    exact ⟨_, hvo, otherBytesWith_size_ne he hz _⟩

/-! ## Evaluation of the source comparison -/

theorem data_beq_B_comm (kb : ByteArray) (dx : Moist.Plutus.Data) :
    (dx == Moist.Plutus.Data.B kb) = (Moist.Plutus.Data.B kb == dx) := by
  cases dx with
  | B b => exact byteArray_beq_comm' b kb
  | _ => rfl
where
  byteArray_beq_comm' (a b : ByteArray) : (a == b) = (b == a) := by
    show (a.data == b.data) = (b.data == a.data)
    cases h : (a.data == b.data) <;> cases h' : (b.data == a.data) <;> simp_all

theorem equalsData_eval_data (a b : Moist.Plutus.Data) :
    evalBuiltin .EqualsData [.VCon (.Data b), .VCon (.Data a)] = some (.VCon (.Bool (a == b))) := rfl

theorem equalsData_eval_none_left {vb : CekValue} {dk : Moist.Plutus.Data}
    (h : ∀ d, vb ≠ .VCon (.Data d)) : evalBuiltin .EqualsData [vb, .VCon (.Data dk)] = none := by
  cases vb with
  | VCon c =>
    cases c
    all_goals first | (exact absurd rfl (h _)) | rfl
  | _ => rfl

theorem equalsData_eval_none_right {va : CekValue} {dk : Moist.Plutus.Data}
    (h : ∀ d, va ≠ .VCon (.Data d)) : evalBuiltin .EqualsData [.VCon (.Data dk), va] = none := by
  cases va with
  | VCon c =>
    cases c
    all_goals first | (exact absurd rfl (h _)) | rfl
  | _ => rfl

/-- The source comparison after its operand returned `vx`: the alternative
    `equalsData` selects, or failure. -/
def SourceStep (kb : ByteArray) (vx : CekValue) (s : State) (π : Stack) (ρ : CekEnv)
    (miss hit : Term) : Prop :=
  (∀ dx, vx = .VCon (.Data dx) →
    Reaches s (.compute π ρ (if (Moist.Plutus.Data.B kb == dx) then hit else miss))) ∧
  ((∀ d, vx ≠ .VCon (.Data d)) → Reaches s .error)

theorem halts_lam_of (ρ : CekEnv) (b : Term) : Halts ρ (.Lam 0 b) (.VLam b ρ) := ⟨2, rfl⟩

theorem reaches_apply_arg {ρ : CekEnv} {s : Stack} {f a : Term} {vf : CekValue} (hf : Halts ρ f vf) :
    Reaches (.compute s ρ (.Apply f a)) (.compute (.funV vf :: s) ρ a) :=
  reaches_trans (reaches_of_steps 1 rfl) (reaches_trans (halts_on_stack hf _) (reaches_of_steps 1 rfl))

/-- The key first: `case (equalsData d x) [miss, hit]` evaluates `x` after the
    partial application to the key. -/
theorem source_first {ρ : CekEnv} {π : Stack} {isrc : Nat} {top tm th : Term} {kb : ByteArray}
    (hsrc : ρ.lookup (isrc + 1) = some (.VCon (.Data (.B kb)))) :
    Reaches (.compute π ρ (.Case (.Apply (.Apply (.Builtin .EqualsData) (.Var (isrc + 1))) top) [tm, th]))
      (.compute (.funV (.VBuiltin .EqualsData [.VCon (.Data (.B kb))] (.one .argV)) ::
        .caseScrutinee [tm, th] ρ :: π) ρ top) ∧
    ∀ vx, SourceStep kb vx
      (.ret (.funV (.VBuiltin .EqualsData [.VCon (.Data (.B kb))] (.one .argV)) ::
        .caseScrutinee [tm, th] ρ :: π) vx) π ρ tm th := by
  refine ⟨reaches_trans (reaches_of_steps 1 rfl) (reaches_apply_arg (halts_apply_intro (halts_builtin_of ρ _)
    (halts_var_of_lookup hsrc) (builtin_partial_reaches rfl rfl))), fun vx => ⟨?_, ?_⟩⟩
  · intro dx hdx; subst hdx
    refine reaches_trans (reaches_of_steps 1 (s' := .ret (.caseScrutinee [tm, th] ρ :: π)
      (.VCon (.Bool (Moist.Plutus.Data.B kb == dx)))) (by simp [steps, step, ExpectedArgs.head,
        ExpectedArgs.tail, equalsData_eval_data])) ?_
    refine ⟨1, ?_⟩
    cases (Moist.Plutus.Data.B kb == dx) <;> rfl
  · intro hnot
    exact ⟨1, by simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, equalsData_eval_none_left hnot]⟩

/-- The key second: the operand is evaluated first. -/
theorem source_second {ρ : CekEnv} {π : Stack} {isrc : Nat} {top tm th : Term} {kb : ByteArray}
    (hsrc : ρ.lookup (isrc + 1) = some (.VCon (.Data (.B kb)))) :
    Reaches (.compute π ρ (.Case (.Apply (.Apply (.Builtin .EqualsData) top) (.Var (isrc + 1))) [tm, th]))
      (.compute (.funV (.VBuiltin .EqualsData [] (expectedArgs .EqualsData)) ::
        .arg (.Var (isrc + 1)) ρ :: .caseScrutinee [tm, th] ρ :: π) ρ top) ∧
    ∀ vx, SourceStep kb vx
      (.ret (.funV (.VBuiltin .EqualsData [] (expectedArgs .EqualsData)) ::
        .arg (.Var (isrc + 1)) ρ :: .caseScrutinee [tm, th] ρ :: π) vx) π ρ tm th := by
  refine ⟨reaches_trans (reaches_of_steps 2 rfl) (reaches_apply_arg (halts_builtin_of ρ _)), fun vx => ⟨?_, ?_⟩⟩
  · intro dx hdx; subst hdx
    refine reaches_trans (reaches_of_steps 2 (s' := .compute (.funV (.VBuiltin .EqualsData
      [.VCon (.Data dx)] (.one .argV)) :: .caseScrutinee [tm, th] ρ :: π) ρ (.Var (isrc + 1))) rfl) ?_
    refine reaches_trans (halts_on_stack (halts_var_of_lookup hsrc) _) ?_
    refine reaches_trans (reaches_of_steps 1 (s' := .ret (.caseScrutinee [tm, th] ρ :: π)
      (.VCon (.Bool (dx == Moist.Plutus.Data.B kb)))) (by simp [steps, step, ExpectedArgs.head,
        ExpectedArgs.tail, equalsData_eval_data])) ?_
    rw [data_beq_B_comm]
    refine ⟨1, ?_⟩
    cases (Moist.Plutus.Data.B kb == dx) <;> rfl
  · intro hnot
    refine reaches_trans (reaches_of_steps 2 (s' := .compute (.funV (.VBuiltin .EqualsData
      [vx] (.one .argV)) :: .caseScrutinee [tm, th] ρ :: π) ρ (.Var (isrc + 1))) rfl) ?_
    refine reaches_trans (halts_on_stack (halts_var_of_lookup hsrc) _) ?_
    exact ⟨1, by simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, equalsData_eval_none_right hnot]⟩

/-! ## Relating the source and the guarded comparison -/

theorem obs_of_sourceSteps {s t : State} {kb : ByteArray} {vx : CekValue} {π : Stack} {ρ : CekEnv}
    {tm th : Term} (hs : SourceStep kb vx s π ρ tm th) (ht : SourceStep kb vx t π ρ tm th) :
    ObsRefines s t := by
  by_cases hdata : ∃ dx, vx = .VCon (.Data dx)
  · obtain ⟨dx, hdx⟩ := hdata
    exact obsRefines_of_reaches (hs.1 dx hdx) (ht.1 dx hdx) (obsRefines_refl _)
  · have hnot : ∀ d, vx ≠ .VCon (.Data d) := fun d h => hdata ⟨d, h⟩
    exact obsRefines_of_reaches (hs.2 hnot) (ht.2 hnot) (obsRefines_refl _)

theorem obs_of_sourceSteps_shift {s t : State} {kb : ByteArray} {vx w : CekValue} {π : Stack}
    {ρ : CekEnv} {d : Nat} {tm th : Term} (henv : EnvWellFormed d ρ) (hπ : StackWellFormed π)
    (ctm : closedAt d tm = true) (cth : closedAt d th = true)
    (hs : SourceStep kb vx s π ρ tm th)
    (ht : SourceStep kb vx t π (ρ.extend w) (renameTerm (shiftRename 1) tm) (renameTerm (shiftRename 1) th)) :
    ObsRefines s t := by
  by_cases hdata : ∃ dx, vx = .VCon (.Data dx)
  · obtain ⟨dx, hdx⟩ := hdata
    refine obsRefines_of_reaches (hs.1 dx hdx) (ht.1 dx hdx) ?_
    split
    · exact (obsEq_shift w henv hπ cth).1
    · exact (obsEq_shift w henv hπ ctm).1
  · have hnot : ∀ d, vx ≠ .VCon (.Data d) := fun d h => hdata ⟨d, h⟩
    exact obsRefines_of_reaches (hs.2 hnot) (ht.2 hnot) (obsRefines_refl _)

theorem target_step {ρ : CekEnv} {π : Stack} {head miss hit : Term} {ilt icmp io ix : Nat}
    {kb : ByteArray} {vx : CekValue}
    (hh : Halts ρ head (.VBuiltin .ChooseData [] chooseRest))
    (hlt : ρ.lookup (ilt + 1) = some (lengthValue kb.size))
    (hcmp : ∃ cv, ρ.lookup (icmp + 1) = some cv ∧ CompareSpec cv kb)
    (hoth : ∃ ob, ρ.lookup (io + 1) = some (.VCon (.Data (.B ob))) ∧ ob.size ≠ kb.size)
    (hx : ρ.lookup (ix + 1) = some vx) :
    SourceStep kb vx (.compute π ρ (guardedTerm head ilt icmp io ix miss hit)) π ρ miss hit := by
  obtain ⟨cv, hcv, hspec⟩ := hcmp
  obtain ⟨ob, hob, hobs⟩ := hoth
  refine ⟨fun dx hdx => ?_, fun hnot => guarded_other hh hlt hob hx hnot⟩
  subst hdx
  exact guarded_data hh hlt hcv hspec hob hobs hx

/-! ## The forced `chooseData` -/

omit sv in
theorem isForcedChooseData_true {o : Option Expr} (h : isForcedChooseData o = true) :
    o = some (.Force (.Builtin .ChooseData)) := by
  unfold isForcedChooseData at h
  split at h
  · rfl
  · cases h

omit sv in
theorem chooseHead_cases (Γ : List (VarId × Expr)) :
    (∃ ch, chooseHead Γ = .Var ch ∧ bindingOf Γ ch = some (.Force (.Builtin .ChooseData))) ∨
      chooseHead Γ = .Force (.Builtin .ChooseData) := by
  unfold chooseHead
  split
  · rename_i entry h
    have hp := List.find?_some h
    simp only at hp
    exact .inl ⟨entry.1, rfl, isForcedChooseData_true hp⟩
  · exact .inr rfl

/-- The lowered head, in an environment and below one more binder. -/
theorem chooseHead_lower {Γ : List (VarId × Expr)} {env : List VarId} (hk : KeysBound Γ env) :
    ∃ head, lowerTotalExpr env (chooseHead Γ) = some head ∧
      (∀ (x : VarId), (∀ ch, chooseHead Γ = .Var ch → (x == ch) = false) →
        lowerTotalExpr (x :: env) (chooseHead Γ) = some (renameTerm (shiftRename 1) head)) ∧
      ∀ ρ, FactsHold Produces Γ env ρ → Halts ρ head (.VBuiltin .ChooseData [] chooseRest) ∧
        ∀ w, Halts (ρ.extend w) (renameTerm (shiftRename 1) head) (.VBuiltin .ChooseData [] chooseRest) := by
  rcases chooseHead_cases Γ with ⟨ch, hch, hb⟩ | hch
  · obtain ⟨ich, hich⟩ := bindingOf_bound hb hk
    refine ⟨.Var (ich + 1), by rw [hch, lowerTotalExpr_var, hich]; rfl, ?_, ?_⟩
    · intro x hx
      rw [hch, lowerTotalExpr_var, envLookupT_cons_neq x ch env (hx ch hch), hich]
      simp [renameTerm, shiftRename]
    · intro ρ hF
      obtain ⟨v, j, hv, _, _, ⟨t, ht, hh⟩⟩ := binding_value hF hb hich
      rw [MIR.lowerTotalExpr_force, lowerTotalExpr_builtin] at ht; cases ht
      rw [halts_unique hh (choose_halts _)] at hv
      refine ⟨halts_var_of_lookup hv, fun w => ?_⟩
      have : (ρ.extend w).lookup (ich + 2) = some (.VBuiltin .ChooseData [] chooseRest) := by
        simpa [CekEnv.extend, CekEnv.lookup] using hv
      simpa [renameTerm, shiftRename] using halts_var_of_lookup this
  · refine ⟨.Force (.Builtin .ChooseData), by rw [hch, MIR.lowerTotalExpr_force, lowerTotalExpr_builtin]; rfl,
      fun x _ => by rw [hch, MIR.lowerTotalExpr_force, lowerTotalExpr_builtin]; rfl,
      fun ρ _ => ⟨choose_halts ρ, fun w => by simpa [renameTerm] using choose_halts (ρ.extend w)⟩⟩

/-! ## Lowering of the guarded comparison -/

omit sv in
theorem lower_guarded {env : List VarId} {head : Expr} {lt cmp oth x : VarId} {miss hit : Expr}
    {headT tm th : Term} {ilt icmp io ix : Nat} (hh : lowerTotalExpr env head = some headT)
    (hlt : envLookupT env lt = some ilt) (hcmp : envLookupT env cmp = some icmp)
    (hoth : envLookupT env oth = some io) (hx : envLookupT env x = some ix)
    (hm : lowerTotalExpr env miss = some tm) (hhit : lowerTotalExpr env hit = some th) :
    lowerTotalExpr env (guardedComparison head lt cmp oth x miss hit) =
      some (guardedTerm headT ilt icmp io ix tm th) := by
  simp [guardedComparison, guardedTerm, chooseWith, chooseApply, MIR.lowerTotalExpr_app,
    MIR.lowerTotalExpr_case_of_list, MIR.lowerTotalExprList_cons, MIR.lowerTotalExprList_nil,
    lowerTotalExpr_builtin, lowerTotalExpr_var, hh, hlt, hcmp, hoth, hx, hm, hhit]

omit sv in
theorem keyedOperands_spec {Γ : List (VarId × Expr)} {first second operand : Expr} {source : VarId}
    (h : keyedOperands Γ first second = some (source, operand)) :
    (first = .Var source ∧ operand = second) ∨ (second = .Var source ∧ operand = first) := by
  unfold keyedOperands at h
  split at h
  · split at h
    · cases h; exact .inl ⟨rfl, rfl⟩
    · split at h
      · split at h
        · cases h; exact .inr ⟨rfl, rfl⟩
        · cases h
      · cases h
  · split at h
    · split at h
      · cases h; exact .inr ⟨rfl, rfl⟩
      · cases h
    · cases h

/-! ## The rewrite -/

theorem sourceStep_of_reaches {s s' : State} {kb : ByteArray} {vx : CekValue} {π : Stack} {ρ : CekEnv}
    {tm th : Term} (hr : Reaches s s') (h : SourceStep kb vx s' π ρ tm th) : SourceStep kb vx s π ρ tm th :=
  ⟨fun dx hdx => reaches_trans hr (h.1 dx hdx), fun hnot => reaches_trans hr (h.2 hnot)⟩

omit sv in
theorem fresh_ne_bound {base : Nat} {env : List VarId} {x v : VarId} {i : Nat}
    (hG : ∀ y ∈ env, GenSafe base y) (hv : envLookupT env v = some i) (hbase : base ≤ x.uid)
    (hgen : x.origin = .gen) : (x == v) = false := by
  cases hxv : (x == v)
  · rfl
  · have hnone := lookup_none_of_not_G hG (not_genSafe hbase hgen)
    rw [envLookupT_congr hxv, hv] at hnone
    cases hnone

theorem keyComparison_factRel {base : Nat} {Γ : List (VarId × Expr)} {x y : Expr}
    (h : keyComparison base Γ x = some y) : FactRel (GenSafe base) PF Γ x y := by
  unfold keyComparison at h
  split at h
  · rename_i first second miss hit
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨source, operand⟩, hops, ⟨lt, cmp, oth⟩, hguard, hy⟩ := h
    intro env t hG hd hfresh hk hsc hlow
    obtain ⟨ts, tm, th, hts, htm, hth, rfl⟩ := lowerTotalExpr_case2_some hlow
    obtain ⟨tf, tsecond, htf, htsecond, rfl⟩ := lowerTotalExpr_app_some hts
    obtain ⟨tq, tfirst, htq, htfirst, rfl⟩ := lowerTotalExpr_app_some htf
    rw [lowerTotalExpr_builtin] at htq; cases htq
    obtain ⟨e, z, k, src, rhsC, hbN, _, _, hbL, _, _, hbC, _⟩ := keyGuardFor_spec hguard
    obtain ⟨ilt, hilt⟩ := bindingOf_bound hbL hk
    obtain ⟨icmp, hicmp⟩ := bindingOf_bound hbC hk
    obtain ⟨io, hio⟩ := bindingOf_bound hbN hk
    obtain ⟨headT, hheadT, hheadShift, hheadHalts⟩ := chooseHead_lower hk
    have ctm := MIR.lowerTotalExpr_closedAt htm
    have cth := MIR.lowerTotalExpr_closedAt hth
    have hP : ∀ ρ, FactsHold PF Γ env ρ → FactsHold Produces Γ env ρ :=
      fun ρ hF => hF.mono fun _ _ _ _ hp => hp.1
    -- a fresh operand binder is distinct from every bound name
    have hchBound : ∀ (xf : VarId), base ≤ xf.uid → xf.origin = .gen →
        ∀ ch, chooseHead Γ = .Var ch → (xf == ch) = false := by
      intro xf hbase hgen ch hch
      rcases chooseHead_cases Γ with ⟨ch', hch', hb'⟩ | hch'
      · rw [hch] at hch'; cases hch'
        obtain ⟨ich, hich⟩ := bindingOf_bound hb' hk
        exact fresh_ne_bound hG hich hbase hgen
      · rw [hch] at hch'; cases hch'
    have shifted : ∀ {ρ : CekEnv} {w : CekValue} {i : Nat} {v : CekValue},
        ρ.lookup (i + 1) = some v → (ρ.extend w).lookup (i + 1 + 1) = some v := by
      intro ρ w i v h; simpa [CekEnv.extend, CekEnv.lookup] using h
    rcases keyedOperands_spec hops with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- the key first
      obtain ⟨isrc, hisrc, rfl⟩ := lowerTotalExpr_var_some htfirst
      split at hy
      · -- a variable operand
        rename_i xv hxv
        subst hxv
        cases hy
        obtain ⟨ix, hix, rfl⟩ := lowerTotalExpr_var_some htsecond
        refine ⟨_, lower_guarded hheadT hilt hicmp hio hix htm hth, ?_⟩
        intro ρ π henv hlen hπ hF
        obtain ⟨kb, hsrc, hlt, hcmp, hoth⟩ := keyGuard_values hguard (hP ρ hF) hd hk hisrc hilt hicmp hio
        obtain ⟨vx, hvx, _⟩ := envWellFormed_lookup env.length henv (n := ix + 1) (by omega)
          (by have := envLookupT_bound env xv ix hix; omega)
        have hsrcStep := source_first (π := π) (top := .Var (ix + 1)) (tm := tm) (th := th) hsrc
        exact obs_of_sourceSteps
          (sourceStep_of_reaches (reaches_trans hsrcStep.1 (halts_on_stack (halts_var_of_lookup hvx) _))
            (hsrcStep.2 vx))
          (target_step (hheadHalts ρ (hP ρ hF)).1 hlt hcmp hoth hvx)
      · -- a general operand, bound first
        cases hy
        generalize hxf : ({ uid := max base (max (maxUidExpr operand) (max (maxUidExpr miss)
          (maxUidExpr hit)) + 1), origin := .gen, hint := "compared" } : VarId) = xf
        have hbase : base ≤ xf.uid := by rw [← hxf]; simp only; omega
        have hgen : xf.origin = .gen := by rw [← hxf]
        have hmiss : maxUidExpr miss < xf.uid := by rw [← hxf]; simp; omega
        have hhit : maxUidExpr hit < xf.uid := by rw [← hxf]; simp; omega
        have hm' : lowerTotalExpr (xf :: env) miss = some (renameTerm (shiftRename 1) tm) := by
          rw [MIR.lowerTotalExpr_prepend_unused env xf miss (maxUidExpr_fresh _ _ hmiss), htm]; rfl
        have hh' : lowerTotalExpr (xf :: env) hit = some (renameTerm (shiftRename 1) th) := by
          rw [MIR.lowerTotalExpr_prepend_unused env xf hit (maxUidExpr_fresh _ _ hhit), hth]; rfl
        have hx0 : envLookupT (xf :: env) xf = some 0 := by rw [envLookupT_cons]; simp [varId_beq_self]
        have hlt1 : envLookupT (xf :: env) lt = some (ilt + 1) := by
          rw [envLookupT_cons_neq xf lt env (fresh_ne_bound hG hilt hbase hgen), hilt]; rfl
        have hcmp1 : envLookupT (xf :: env) cmp = some (icmp + 1) := by
          rw [envLookupT_cons_neq xf cmp env (fresh_ne_bound hG hicmp hbase hgen), hicmp]; rfl
        have hoth1 : envLookupT (xf :: env) oth = some (io + 1) := by
          rw [envLookupT_cons_neq xf oth env (fresh_ne_bound hG hio hbase hgen), hio]; rfl
        refine ⟨.Apply (.Lam 0 (guardedTerm (renameTerm (shiftRename 1) headT) (ilt + 1) (icmp + 1) (io + 1) 0
          (renameTerm (shiftRename 1) tm) (renameTerm (shiftRename 1) th))) tsecond, ?_, ?_⟩
        · rw [lowerTotalExpr_let_single, htsecond,
            lower_guarded (hheadShift xf (hchBound xf hbase hgen)) hlt1 hcmp1 hoth1 hx0 hm' hh']
          rfl
        · intro ρ π henv hlen hπ hF
          obtain ⟨kb, hsrc, hlt, ⟨cv, hcv, hspec⟩, ⟨ob, hob, hobs⟩⟩ :=
            keyGuard_values hguard (hP ρ hF) hd hk hisrc hilt hicmp hio
          have hsrcStep := source_first (π := π) (top := tsecond) (tm := tm) (th := th) hsrc
          refine obsRefines_of_reaches hsrcStep.1 (reaches_apply_arg (halts_lam_of ρ _)) ?_
          apply obsRefines_of_continuation
          intro vx _
          exact obs_of_sourceSteps_shift henv hπ ctm cth (hsrcStep.2 vx)
            (sourceStep_of_reaches (reaches_of_steps 1 rfl)
              (target_step ((hheadHalts ρ (hP ρ hF)).2 vx) (shifted hlt) ⟨cv, shifted hcv, hspec⟩
                ⟨ob, shifted hob, hobs⟩ rfl))
    · -- the key second
      obtain ⟨isrc, hisrc, rfl⟩ := lowerTotalExpr_var_some htsecond
      split at hy
      · rename_i xv hxv
        subst hxv
        cases hy
        obtain ⟨ix, hix, rfl⟩ := lowerTotalExpr_var_some htfirst
        refine ⟨_, lower_guarded hheadT hilt hicmp hio hix htm hth, ?_⟩
        intro ρ π henv hlen hπ hF
        obtain ⟨kb, hsrc, hlt, hcmp, hoth⟩ := keyGuard_values hguard (hP ρ hF) hd hk hisrc hilt hicmp hio
        obtain ⟨vx, hvx, _⟩ := envWellFormed_lookup env.length henv (n := ix + 1) (by omega)
          (by have := envLookupT_bound env xv ix hix; omega)
        have hsrcStep := source_second (π := π) (top := .Var (ix + 1)) (tm := tm) (th := th) hsrc
        exact obs_of_sourceSteps
          (sourceStep_of_reaches (reaches_trans hsrcStep.1 (halts_on_stack (halts_var_of_lookup hvx) _))
            (hsrcStep.2 vx))
          (target_step (hheadHalts ρ (hP ρ hF)).1 hlt hcmp hoth hvx)
      · cases hy
        generalize hxf : ({ uid := max base (max (maxUidExpr operand) (max (maxUidExpr miss)
          (maxUidExpr hit)) + 1), origin := .gen, hint := "compared" } : VarId) = xf
        have hbase : base ≤ xf.uid := by rw [← hxf]; simp only; omega
        have hgen : xf.origin = .gen := by rw [← hxf]
        have hmiss : maxUidExpr miss < xf.uid := by rw [← hxf]; simp; omega
        have hhit : maxUidExpr hit < xf.uid := by rw [← hxf]; simp; omega
        have hm' : lowerTotalExpr (xf :: env) miss = some (renameTerm (shiftRename 1) tm) := by
          rw [MIR.lowerTotalExpr_prepend_unused env xf miss (maxUidExpr_fresh _ _ hmiss), htm]; rfl
        have hh' : lowerTotalExpr (xf :: env) hit = some (renameTerm (shiftRename 1) th) := by
          rw [MIR.lowerTotalExpr_prepend_unused env xf hit (maxUidExpr_fresh _ _ hhit), hth]; rfl
        have hx0 : envLookupT (xf :: env) xf = some 0 := by rw [envLookupT_cons]; simp [varId_beq_self]
        have hlt1 : envLookupT (xf :: env) lt = some (ilt + 1) := by
          rw [envLookupT_cons_neq xf lt env (fresh_ne_bound hG hilt hbase hgen), hilt]; rfl
        have hcmp1 : envLookupT (xf :: env) cmp = some (icmp + 1) := by
          rw [envLookupT_cons_neq xf cmp env (fresh_ne_bound hG hicmp hbase hgen), hicmp]; rfl
        have hoth1 : envLookupT (xf :: env) oth = some (io + 1) := by
          rw [envLookupT_cons_neq xf oth env (fresh_ne_bound hG hio hbase hgen), hio]; rfl
        refine ⟨.Apply (.Lam 0 (guardedTerm (renameTerm (shiftRename 1) headT) (ilt + 1) (icmp + 1) (io + 1) 0
          (renameTerm (shiftRename 1) tm) (renameTerm (shiftRename 1) th))) tfirst, ?_, ?_⟩
        · rw [lowerTotalExpr_let_single, htfirst,
            lower_guarded (hheadShift xf (hchBound xf hbase hgen)) hlt1 hcmp1 hoth1 hx0 hm' hh']
          rfl
        · intro ρ π henv hlen hπ hF
          obtain ⟨kb, hsrc, hlt, ⟨cv, hcv, hspec⟩, ⟨ob, hob, hobs⟩⟩ :=
            keyGuard_values hguard (hP ρ hF) hd hk hisrc hilt hicmp hio
          have hsrcStep := source_second (π := π) (top := tfirst) (tm := tm) (th := th) hsrc
          refine obsRefines_of_reaches hsrcStep.1 (reaches_apply_arg (halts_lam_of ρ _)) ?_
          apply obsRefines_of_continuation
          intro vx _
          exact obs_of_sourceSteps_shift henv hπ ctm cth (hsrcStep.2 vx)
            (sourceStep_of_reaches (reaches_of_steps 1 rfl)
              (target_step ((hheadHalts ρ (hP ρ hF)).2 vx) (shifted hlt) ⟨cv, shifted hcv, hspec⟩
                ⟨ob, shifted hob, hobs⟩ rfl))
  · cases h

omit sv in
theorem guarded_fresh {env : List VarId} {Γ : List (VarId × Expr)} {lt cmp oth x : VarId}
    {miss hit : Expr} (hm : freshIn env miss = true) (hh : freshIn env hit = true) :
    freshIn env (guardedComparison (chooseHead Γ) lt cmp oth x miss hit) = true := by
  have hhead : freshIn env (chooseHead Γ) = true := by
    rcases chooseHead_cases Γ with ⟨ch, hch, _⟩ | hch <;> rw [hch] <;> simp [freshIn]
  simp [guardedComparison, chooseWith, freshIn, freshInList, hm, hh, hhead]

theorem keyComparison_fresh {base : Nat} {Γ : List (VarId × Expr)} {x y : Expr} {env : List VarId}
    (hG : ∀ v ∈ env, GenSafe base v) (hx : freshIn env x = true) (h : keyComparison base Γ x = some y) :
    freshIn env y = true := by
  unfold keyComparison at h
  split at h
  · rename_i first second miss hit
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨source, operand⟩, hops, ⟨lt, cmp, oth⟩, _, hy⟩ := h
    simp only [freshIn, freshInList, Bool.and_eq_true, Bool.and_true] at hx
    obtain ⟨⟨⟨_, hfirst⟩, hsecond⟩, hm, hh⟩ := hx
    have hop : freshIn env operand = true := by
      rcases keyedOperands_spec hops with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact hsecond
      · exact hfirst
    split at hy
    · cases hy; exact guarded_fresh hm hh
    · cases hy
      rw [freshIn_let_single]
      simp only [Bool.and_eq_true]
      refine ⟨⟨hop, ?_⟩, ?_⟩
      · rw [lookup_none_of_not_G hG (not_genSafe (by simp only; omega) rfl)]; rfl
      · apply guarded_fresh
        · exact freshIn_cons_of_big hm (by simp only; omega)
        · exact freshIn_cons_of_big hh (by simp only; omega)
  · cases h

end Moist.Verified.ShapeFacts
