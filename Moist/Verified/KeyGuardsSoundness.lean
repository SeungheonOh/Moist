import Moist.MIR.Optimize.Advanced.DataShapes
import Moist.Verified.ShapesSoundness.KeyGuards
import Moist.Verified.ShapesSoundness.Choices
import Moist.Verified.AdvancedTraversal

variable [sv : Moist.CEK.SemVariant]

/-! # Inserting key guards

`insertKeyGuards` binds, right after `k = unBData d`, the length test, the
comparison, the other `B` value and the forced `chooseData` that the guarded
comparisons of `d` use. Every one of these bindings returns on every path,
since `k` holds bytes, and the scope does not mention them
(`insertKeyGuards_refines`).
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines Moist.Verified.MIR

def shift1 (t : Term) : Term := renameTerm (shiftRename 1) t

theorem unBData_produces_bytes {env : List VarId} {ρ : CekEnv} {d : VarId} {v : CekValue}
    (h : Produces env ρ (.App (.Builtin .UnBData) (.Var d)) v) : ∃ kb, v = .VCon (.ByteString kb) := by
  obtain ⟨t, ht, hv⟩ := h
  obtain ⟨tf, ta, htf, _, rfl⟩ := lowerTotalExpr_app_some ht
  rw [lowerTotalExpr_builtin] at htf; cases htf
  obtain ⟨wf, wa, hwf, _, rest⟩ := halts_apply hv
  rw [halts_builtin hwf] at rest
  obtain ⟨args, hlen, heval⟩ := saturated_apply ⟨[], rfl, rfl⟩ rest
  have h1 : valueArity (expectedArgs .UnBData) = 1 := rfl
  rw [h1] at hlen
  have : args = [] := by
    cases args with
    | nil => rfl
    | cons _ _ => simp at hlen
  subst this
  obtain ⟨c, r, rfl, hc, rfl⟩ := evalBuiltin_single (by decide) heval
  obtain ⟨kb, rfl, rfl⟩ : ∃ kb, c = .Data (.B kb) ∧ r = .ByteString kb := by
    cases c with
    | Data dd =>
      cases dd
      all_goals first | (cases hc; done) | exact ⟨_, rfl, (Option.some.inj hc).symm⟩
    | _ => cases hc
  exact ⟨_, rfl⟩

/-- Four bindings that return on every path, inserted before a body that
    mentions none of them. -/
theorem guards_factRefines {d : Nat} {F : CekEnv → Prop} {t : Term} {ik id : Nat}
    (closedT : closedAt d t = true) (hik : ik < d) (hid : id < d)
    (hkey : ∀ ρ, F ρ → ∃ kb, ρ.lookup (ik + 1) = some (.VCon (.ByteString kb))) :
    FactRefines d F t
      (.Apply (.Lam 0 (.Apply (.Lam 0 (.Apply (.Lam 0 (.Apply (.Lam 0
        (shift1 (shift1 (shift1 (shift1 t))))) (.Force (.Builtin .ChooseData)))) (otherTerm 1)))
        (compareTerm (ik + 1) (id + 1)))) (lengthTerm ik)) := by
  have c1 := closedAt_shift closedT
  have c2 := closedAt_shift c1
  have c3 := closedAt_shift c2
  -- the innermost binding: the forced builtin
  have h3 : FactRefines (d + 3) (fun _ => True) (shift1 (shift1 (shift1 t)))
      (.Apply (.Lam 0 (shift1 (shift1 (shift1 (shift1 t))))) (.Force (.Builtin .ChooseData))) :=
    factRefines_add_let 0 c3 (fun ρ _ _ _ => ⟨_, choose_halts ρ⟩)
  -- the other `B` value
  let G2 : CekEnv → Prop := fun ρ => ∃ n, ρ.lookup 2 = some (lengthValue n)
  have h2 : FactRefines (d + 2) G2 (shift1 (shift1 t))
      (.Apply (.Lam 0 (.Apply (.Lam 0 (shift1 (shift1 (shift1 (shift1 t))))) (.Force (.Builtin .ChooseData))))
        (otherTerm 1)) := by
    refine (factRefines_add_let (r := otherTerm 1) 0 c2 ?_).trans ?_
    · intro ρ hG _ _
      obtain ⟨n, hn⟩ := hG
      exact otherTerm_halts hn
    · refine factRefines_let 0 0 (by simp [otherTerm, otherTermWith, closedAt, closedAtList]) (fun _ _ _ _ => trivial) h3
  -- the comparison
  let G1 : CekEnv → Prop := fun ρ => ∃ kb, ρ.lookup (ik + 2) = some (.VCon (.ByteString kb)) ∧
    ρ.lookup 1 = some (lengthValue kb.size)
  have h1 : FactRefines (d + 1) G1 (shift1 t)
      (.Apply (.Lam 0 (.Apply (.Lam 0 (.Apply (.Lam 0 (shift1 (shift1 (shift1 (shift1 t)))))
        (.Force (.Builtin .ChooseData)))) (otherTerm 1))) (compareTerm (ik + 1) (id + 1))) := by
    refine (factRefines_add_let (r := compareTerm (ik + 1) (id + 1)) 0 c1 ?_).trans ?_
    · intro ρ hG _ _
      obtain ⟨kb, hk, _⟩ := hG
      exact ⟨_, compareTerm_halts hk⟩
    · refine factRefines_let 0 0 ?_ ?_ h2
      · simp [compareTerm, compareTermWith, slowBody, closedAt, closedAtList, unitListConst]; omega
      · intro ρ v hG _
        obtain ⟨kb, _, hl⟩ := hG
        exact ⟨kb.size, by simpa [CekEnv.extend, CekEnv.lookup] using hl⟩
  refine (factRefines_add_let (r := lengthTerm ik) 0 closedT ?_).trans ?_
  · intro ρ hF _ _
    obtain ⟨kb, hk⟩ := hkey ρ hF
    exact ⟨_, lengthTerm_halts hk⟩
  · refine factRefines_let 0 0 (by simp [lengthTerm, closedAt]; omega) ?_ h1
    intro ρ v hF hv
    obtain ⟨kb, hk⟩ := hkey ρ hF
    rw [halts_unique hv (lengthTerm_halts hk)]
    exact ⟨kb, by simpa [CekEnv.extend, CekEnv.lookup] using hk, rfl⟩

theorem bound_some' {env : List VarId} {x : VarId} (h : (envLookupT env x).isSome = true) :
    ∃ i, envLookupT env x = some i := Option.isSome_iff_exists.mp h

/-- Binding the guards of `d` after `k = unBData d`, before a scope that
    mentions none of them. -/
theorem insertGuards_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)}
    {k d lt cmp oth hb tb yb ch : VarId} {S : Expr}
    (hflt : (freeVars S).contains lt = false) (hfcmp : (freeVars S).contains cmp = false)
    (hfoth : (freeVars S).contains oth = false) (hfch : (freeVars S).contains ch = false)
    (hltk : (lt == k) = false) (hltd : (lt == d) = false) (hcmplt : (cmp == lt) = false)
    (hhk : (hb == k) = false) (htk : (tb == k) = false) (hyd : (yb == d) = false) :
    FactRel G PF ((k, .App (.Builtin .UnBData) (.Var d)) :: Γ) S
      (.Let [(lt, guardLength k, false)] (.Let [(cmp, guardCompare d k hb tb yb, false)]
        (.Let [(oth, guardOther lt, false)] (.Let [(ch, .Force (.Builtin .ChooseData), false)] S)))) := by
  intro env t _ hd _ hkeys hsc hlow
  obtain ⟨ik, hik⟩ := bound_some' (hkeys _ (.head _))
  have hlk : lowerTotalExpr env (.Var k) = some (.Var (ik + 1)) := by rw [lowerTotalExpr_var, hik]; rfl
  have hres : resolveHead 64 ((k, .App (.Builtin .UnBData) (.Var d)) :: Γ) (.Var k) =
      .App (.Builtin .UnBData) (.Var d) := by
    simp [resolveHead, varId_beq_self]
  obtain ⟨id, hid⟩ := bound_some' (resolveHead_app_var_bound 64 _ (.Var k) hres hsc hd (by rw [hlk]; rfl))
  -- the scope under the four new binders
  have hS1 : lowerTotalExpr (lt :: env) S = some (shift1 t) := by
    rw [MIR.lowerTotalExpr_prepend_unused env lt S hflt, hlow]; rfl
  have hS2 : lowerTotalExpr (cmp :: lt :: env) S = some (shift1 (shift1 t)) := by
    rw [MIR.lowerTotalExpr_prepend_unused _ cmp S hfcmp, hS1]; rfl
  have hS3 : lowerTotalExpr (oth :: cmp :: lt :: env) S = some (shift1 (shift1 (shift1 t))) := by
    rw [MIR.lowerTotalExpr_prepend_unused _ oth S hfoth, hS2]; rfl
  have hS4 : lowerTotalExpr (ch :: oth :: cmp :: lt :: env) S =
      some (shift1 (shift1 (shift1 (shift1 t)))) := by
    rw [MIR.lowerTotalExpr_prepend_unused _ ch S hfch, hS3]; rfl
  have hk1 : envLookupT (lt :: env) k = some (ik + 1) := by
    rw [envLookupT_cons_neq lt k env hltk, hik]; rfl
  have hd1 : envLookupT (lt :: env) d = some (id + 1) := by
    rw [envLookupT_cons_neq lt d env hltd, hid]; rfl
  have hlt2 : envLookupT (cmp :: lt :: env) lt = some 1 := by
    rw [envLookupT_cons_neq cmp lt _ hcmplt, envLookupT_cons]; simp [varId_beq_self]
  refine ⟨_, ?_, guards_factRefines (MIR.lowerTotalExpr_closedAt hlow) (envLookupT_bound env k ik hik)
    (envLookupT_bound env d id hid) ?_⟩
  · simp only [lowerTotalExpr_let_single, lower_guardLength hik, lower_guardCompare hk1 hd1 hhk htk hyd,
      lower_guardOther hlt2, MIR.lowerTotalExpr_force, lowerTotalExpr_builtin, hS4]
    rfl
  · intro ρ hF
    obtain ⟨v, j, _, _, hv, hp⟩ := hF k (k, .App (.Builtin .UnBData) (.Var d)) ik
      (by simp [varId_beq_self]) hik
    obtain ⟨kb, rfl⟩ := unBData_produces_bytes hp.1
    exact ⟨kb, hv⟩

/-! ## The insertion walk -/

omit sv in
theorem unBDataSource_spec {e : Expr} {d : VarId} (h : unBDataSource e = some d) :
    e = .App (.Builtin .UnBData) (.Var d) := by
  unfold unBDataSource at h
  split at h
  · cases h; rfl
  · cases h

omit sv in
theorem keyGuardBindings_cons (base : Nat) (k : VarId) (rhs : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) :
    keyGuardBindings base ((k, rhs, er) :: rest) body =
      let processed := keyGuardBindings base rest body
      let rhs' := keyGuardWalk base rhs
      let scope := Expr.Let processed.1 processed.2
      match unBDataSource rhs' with
      | some d =>
        if anyExpr (comparesKey d) (exprSize scope) scope &&
            !anyExpr (isLengthOf k) (exprSize scope) scope then
          let first := max base (max k.uid (max (maxUidExpr rhs') (maxUidExpr scope)) + 1)
          let lengthTest : VarId := { uid := first, origin := .gen, hint := "keyLength" }
          let compare : VarId := { uid := first + 1, origin := .gen, hint := "keyCompare" }
          let other : VarId := { uid := first + 2, origin := .gen, hint := "otherKey" }
          let headBinder : VarId := { uid := first + 3, origin := .gen, hint := "unit" }
          let tailBinder : VarId := { uid := first + 4, origin := .gen, hint := "units" }
          let bytes : VarId := { uid := first + 5, origin := .gen, hint := "bytes" }
          let choose : VarId := { uid := first + 6, origin := .gen, hint := "chooseData" }
          ((k, rhs', er) :: (lengthTest, guardLength k, false) ::
            (compare, guardCompare d k headBinder tailBinder bytes, false) ::
            (other, guardOther lengthTest, false) ::
            (choose, .Force (.Builtin .ChooseData), false) :: processed.1, processed.2)
        else ((k, rhs', er) :: processed.1, processed.2)
      | none => ((k, rhs', er) :: processed.1, processed.2) := by
  rw [keyGuardBindings]; rfl

omit sv in
theorem envLookupT_cons_uid_ne {x y : VarId} {env : List VarId} (h : x.uid ≠ y.uid) :
    envLookupT (x :: env) y = (envLookupT env y).map (· + 1) :=
  envLookupT_cons_neq x y env ((VarId.beq_false_iff x y).mpr (.inr h))

omit sv in
theorem lookup_cons_none' {env : List VarId} {x y : VarId} (hxy : x.uid ≠ y.uid)
    (hy : envLookupT env y = none) : envLookupT (x :: env) y = none := by
  rw [envLookupT_cons_uid_ne hxy, hy]; rfl

omit sv in
theorem maxUidExprBinds_mem' : ∀ {b : VarId × Expr × Bool} {bs : List (VarId × Expr × Bool)}, b ∈ bs →
    b.1.uid ≤ maxUidExprBinds bs ∧ maxUidExpr b.2.1 ≤ maxUidExprBinds bs
  | _, (x, r, er) :: rest, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp only [maxUidExprBinds]; omega
    · have := maxUidExprBinds_mem' h
      simp only [maxUidExprBinds]; omega

/-- The guard bindings keep a scope fresh when their binders are new and
    larger than every name of the scope. -/
theorem guards_fresh {E : List VarId} {S : Expr} {k d : VarId} {u : Nat}
    (hS : freshIn E S = true) (hu : maxUidExpr S < u)
    (hname : ∀ (x : VarId) i, i < 7 → x.uid = u + i → x.origin = .gen →
      envLookupT E x = none) :
    freshIn E (.Let [({ uid := u, origin := .gen, hint := "keyLength" }, guardLength k, false)]
      (.Let [({ uid := u + 1, origin := .gen, hint := "keyCompare" },
          guardCompare d k { uid := u + 3, origin := .gen, hint := "unit" }
            { uid := u + 4, origin := .gen, hint := "units" } { uid := u + 5, origin := .gen, hint := "bytes" },
          false)]
        (.Let [({ uid := u + 2, origin := .gen, hint := "otherKey" },
            guardOther { uid := u, origin := .gen, hint := "keyLength" }, false)]
          (.Let [({ uid := u + 6, origin := .gen, hint := "chooseData" }, .Force (.Builtin .ChooseData), false)]
            S)))) = true := by
  have n0 := hname { uid := u, origin := .gen, hint := "keyLength" } 0 (by omega) rfl rfl
  have n1 := hname { uid := u + 1, origin := .gen, hint := "keyCompare" } 1 (by omega) rfl rfl
  have n2 := hname { uid := u + 2, origin := .gen, hint := "otherKey" } 2 (by omega) rfl rfl
  have n3 := hname { uid := u + 3, origin := .gen, hint := "unit" } 3 (by omega) rfl rfl
  have n4 := hname { uid := u + 4, origin := .gen, hint := "units" } 4 (by omega) rfl rfl
  have n5 := hname { uid := u + 5, origin := .gen, hint := "bytes" } 5 (by omega) rfl rfl
  have n6 := hname { uid := u + 6, origin := .gen, hint := "chooseData" } 6 (by omega) rfl rfl
  simp only [freshIn_let_single, guardLength, guardCompare, guardOther, lengthApp, unitListLiteral,
    integerConstant, emptyBytesData, zeroBytesData, freshIn, freshInList, Bool.and_eq_true,
    Bool.and_true, Bool.true_and]
  simp (disch := simp) only [envLookupT_cons_uid_ne, n0, n1, n2, n3, n4, n5, n6, Option.map_none,
    Option.isNone_none, true_and, and_true]
  refine freshIn_cons_of_big (freshIn_cons_of_big (freshIn_cons_of_big (freshIn_cons_of_big hS ?_) ?_) ?_) ?_
  all_goals simp; omega

omit sv in
theorem freshIn_let_four (avoid : List VarId) (a b c e : VarId × Expr × Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) :
    freshIn avoid (.Let (a :: b :: c :: e :: rest) body) =
      freshIn avoid (.Let [a] (.Let [b] (.Let [c] (.Let [e] (.Let rest body))))) := by
  obtain ⟨_, _, _⟩ := a; obtain ⟨_, _, _⟩ := b; obtain ⟨_, _, _⟩ := c; obtain ⟨_, _, _⟩ := e
  simp only [freshIn, freshInLet]

omit sv in
theorem lowerTotalExpr_let_four (env : List VarId) (a b c e : VarId × Expr × Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) :
    lowerTotalExpr env (.Let (a :: b :: c :: e :: rest) body) =
      lowerTotalExpr env (.Let [a] (.Let [b] (.Let [c] (.Let [e] (.Let rest body))))) := by
  obtain ⟨_, _, _⟩ := a; obtain ⟨_, _, _⟩ := b; obtain ⟨_, _, _⟩ := c; obtain ⟨_, _, _⟩ := e
  simp only [lowerTotalExpr, expandFix, expandFixBinds, lowerTotal, lowerTotalLet]

theorem keyGuardBindings_fresh (base : Nat) (body : Expr)
    (hb : ∀ env, (∀ y ∈ env, GenSafe base y) → freshIn env body = true →
      freshIn env (keyGuardWalk base body) = true) :
    ∀ (binds : List (VarId × Expr × Bool)),
      (∀ b ∈ binds, b.1.uid < base) →
      (∀ b ∈ binds, ∀ env, (∀ y ∈ env, GenSafe base y) →
        freshIn env b.2.1 = true → freshIn env (keyGuardWalk base b.2.1) = true) →
      ∀ env, (∀ y ∈ env, GenSafe base y) → freshIn env (.Let binds body) = true →
        freshIn env (.Let (keyGuardBindings base binds body).1 (keyGuardBindings base binds body).2) = true
  | [], _, _, env, hG, hf => by
    rw [keyGuardBindings.eq_1]
    rw [freshIn_let_nil] at hf ⊢
    exact hb env hG hf
  | (k, r, er) :: rest, hx, hr, env, hG, hf => by
    rw [keyGuardBindings_cons]
    rw [freshIn_let_cons, freshIn_let_single] at hf
    simp only [Bool.and_eq_true] at hf
    obtain ⟨⟨hfr, hke⟩, hfrest⟩ := hf
    have hk : k.uid < base := hx _ (.head _)
    have ih := keyGuardBindings_fresh base body hb rest (fun b hb' => hx b (.tail _ hb'))
      (fun b hb' => hr b (.tail _ hb')) (k :: env) (allG_cons (.inl hk) hG) hfrest
    have hr' := hr _ (.head _) env hG hfr
    have plain : freshIn env (.Let ((k, keyGuardWalk base r, er) ::
        (keyGuardBindings base rest body).1) (keyGuardBindings base rest body).2) = true := by
      rw [freshIn_let_cons, freshIn_let_single]
      simp only [Bool.and_eq_true]
      exact ⟨⟨hr', hke⟩, ih⟩
    simp only []
    split
    · split
      · generalize hS : Expr.Let (keyGuardBindings base rest body).1
          (keyGuardBindings base rest body).2 = S at ih
        generalize hu : max base (max k.uid (max (maxUidExpr (keyGuardWalk base r)) (maxUidExpr S)) + 1) = u
        have hbase : base ≤ u := by omega
        have hbig : maxUidExpr S < u := by omega
        rw [freshIn_let_cons, freshIn_let_single]
        simp only [Bool.and_eq_true]
        refine ⟨⟨hr', hke⟩, ?_⟩
        rw [freshIn_let_four, hS]
        refine guards_fresh (k := k) ih hbig ?_
        intro x i hi hxu hxg
        have hxk : k.uid ≠ x.uid := by omega
        rw [envLookupT_cons_uid_ne hxk]
        rw [lookup_none_of_not_G hG (not_genSafe (by omega) hxg)]; rfl
      · exact plain
    · exact plain

theorem keyGuardWalk_fresh (base : Nat) :
    ∀ (e : Expr) (env : List VarId), (∀ y ∈ env, GenSafe base y) →
      maxUidExpr e < base → freshIn env e = true →
      freshIn env (keyGuardWalk base e) = true
  | .Let binds body, env, hG, hmax, hf => by
    rw [keyGuardWalk.eq_1]
    simp only [maxUidExpr] at hmax
    exact keyGuardBindings_fresh base body
      (fun env' hG' hf' => keyGuardWalk_fresh base body env' hG' (by omega) hf')
      binds (fun b hb => by have := (maxUidExprBinds_mem' hb).1; omega)
      (fun b hb env' hG' hf' => keyGuardWalk_fresh base b.2.1 env' hG'
        (by have := (maxUidExprBinds_mem' hb).2; omega) hf') env hG hf
  | .Lam x b, env, hG, hmax, hf => by
    rw [keyGuardWalk.eq_2]
    simp only [maxUidExpr] at hmax
    simp only [freshIn, Bool.and_eq_true] at hf ⊢
    exact ⟨hf.1, keyGuardWalk_fresh base b (x :: env) (allG_cons (.inl (by omega)) hG)
      (by omega) hf.2⟩
  | .Fix x b, env, hG, hmax, hf => by
    rw [keyGuardWalk.eq_3]
    simp only [maxUidExpr] at hmax
    simp only [freshIn, Bool.and_eq_true] at hf ⊢
    exact ⟨hf.1, keyGuardWalk_fresh base b (x :: env) (allG_cons (.inl (by omega)) hG)
      (by omega) hf.2⟩
  | .App f a, env, hG, hmax, hf => by
    rw [keyGuardWalk.eq_4]
    simp only [maxUidExpr] at hmax
    simp only [freshIn, Bool.and_eq_true] at hf ⊢
    exact ⟨keyGuardWalk_fresh base f env hG (by omega) hf.1,
      keyGuardWalk_fresh base a env hG (by omega) hf.2⟩
  | .Force b, env, hG, hmax, hf => by
    rw [keyGuardWalk.eq_5]
    simp only [maxUidExpr] at hmax
    simp only [freshIn] at hf ⊢
    exact keyGuardWalk_fresh base b env hG (by omega) hf
  | .Delay b, env, hG, hmax, hf => by
    rw [keyGuardWalk.eq_6]
    simp only [maxUidExpr] at hmax
    simp only [freshIn] at hf ⊢
    exact keyGuardWalk_fresh base b env hG (by omega) hf
  | .Constr tag fields, env, hG, hmax, hf => by
    rw [keyGuardWalk.eq_7]
    simp only [maxUidExpr] at hmax
    simp only [freshIn] at hf ⊢
    rw [freshInList_iff] at hf ⊢
    intro y hy
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    have := maxUidExpr_le_maxUidExprList_of_mem hc
    exact keyGuardWalk_fresh base c env hG (by omega) (hf c hc)
  | .Case scrut alts, env, hG, hmax, hf => by
    rw [keyGuardWalk.eq_8]
    simp only [maxUidExpr] at hmax
    simp only [freshIn, Bool.and_eq_true] at hf ⊢
    refine ⟨keyGuardWalk_fresh base scrut env hG (by omega) hf.1, ?_⟩
    have hf2 := hf.2
    rw [freshInList_iff] at hf2 ⊢
    intro y hy
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    have := maxUidExpr_le_maxUidExprList_of_mem hc
    exact keyGuardWalk_fresh base c env hG (by omega) (hf2 c hc)
  | .Var _, env, _, _, hf => by rw [keyGuardWalk.eq_9]; exact hf
  | .Lit _, env, _, _, hf => by rw [keyGuardWalk.eq_10]; exact hf
  | .Builtin _, env, _, _, hf => by rw [keyGuardWalk.eq_11]; exact hf
  | .Error, env, _, _, hf => by rw [keyGuardWalk.eq_12]; exact hf
termination_by e => exprSize e
decreasing_by
  all_goals first
    | (subst_vars; simp only [exprSize]; omega)
    | (simp only [exprSize]; have := exprSize_pos body; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)
    | (have := exprSizeBinds_mem_lt (by assumption); simp only [exprSize]; have := exprSize_pos body; omega)

theorem keyGuardBindings_factRel (base : Nat) (body : Expr)
    (hb : ∀ Γ : List (VarId × Expr), FactRel (GenSafe base) PF Γ body (keyGuardWalk base body))
    (hbf : ∀ env, (∀ y ∈ env, GenSafe base y) → freshIn env body = true →
      freshIn env (keyGuardWalk base body) = true) :
    ∀ (binds : List (VarId × Expr × Bool)),
      (∀ b ∈ binds, b.1.uid < base) →
      (∀ b ∈ binds, ∀ Γ : List (VarId × Expr),
        FactRel (GenSafe base) PF Γ b.2.1 (keyGuardWalk base b.2.1)) →
      (∀ b ∈ binds, ∀ env, (∀ y ∈ env, GenSafe base y) →
        freshIn env b.2.1 = true → freshIn env (keyGuardWalk base b.2.1) = true) →
      ∀ Γ : List (VarId × Expr),
        FactRel (GenSafe base) PF Γ (.Let binds body)
          (.Let (keyGuardBindings base binds body).1 (keyGuardBindings base binds body).2)
  | [], _, _, _, Γ => by
    rw [keyGuardBindings.eq_1]
    exact ((hb Γ).congr_left (fun env => lowerTotalExpr_let_nil env body)
      (fun avoid => freshIn_let_nil avoid body)).congr_right
      (fun env => lowerTotalExpr_let_nil env _)
  | (k, r, er) :: rest, hx, hr, hrf, Γ => by
    rw [keyGuardBindings_cons]
    have hk : k.uid < base := hx _ (.head _)
    have ih := fun Γ' => keyGuardBindings_factRel base body hb hbf rest
      (fun b hb' => hx b (.tail _ hb')) (fun b hb' => hr b (.tail _ hb'))
      (fun b hb' => hrf b (.tail _ hb')) Γ'
    have hrestf := keyGuardBindings_fresh base body hbf rest (fun b hb' => hx b (.tail _ hb'))
      (fun b hb' => hrf b (.tail _ hb'))
    have hpush : ∀ env ρ v, (∀ y ∈ env, GenSafe base y) → EnvDistinct env → freshIn env r = true →
        Produces env ρ (keyGuardWalk base r) v → PF env ρ (keyGuardWalk base r) v :=
      fun env ρ v hG _ hfr hp => ⟨hp, hrf _ (.head _) env hG hfr⟩
    have plain : FactRel (GenSafe base) PF Γ (.Let ((k, r, er) :: rest) body)
        (.Let ((k, keyGuardWalk base r, er) :: (keyGuardBindings base rest body).1)
          (keyGuardBindings base rest body).2) :=
      ((FactRel.let_single (er := er) (keyGuardWalk base r) (.inl hk) (.inr rfl)
        (hr _ (.head _) Γ) (ih _) hpush).congr_left
        (fun env => lowerTotalExpr_let_cons env _ _ _) (fun avoid => freshIn_let_cons avoid _ _ _)).congr_right
        (fun env => lowerTotalExpr_let_cons env _ _ _)
    simp only []
    split
    · rename_i d hd
      split
      · have hrd := unBDataSource_spec hd
        generalize hS : Expr.Let (keyGuardBindings base rest body).1
          (keyGuardBindings base rest body).2 = S at ih hrestf
        generalize hu : max base (max k.uid (max (maxUidExpr (keyGuardWalk base r)) (maxUidExpr S)) + 1) = u
        have hbig : maxUidExpr S < u := by omega
        have hdu : d.uid < u := by
          have : d.uid ≤ maxUidExpr (keyGuardWalk base r) := by rw [hrd]; simp [maxUidExpr]
          omega
        have hins := insertGuards_factRel (G := GenSafe base) (Γ := Γ) (k := k) (d := d) (S := S)
          (lt := { uid := u, origin := .gen, hint := "keyLength" })
          (cmp := { uid := u + 1, origin := .gen, hint := "keyCompare" })
          (oth := { uid := u + 2, origin := .gen, hint := "otherKey" })
          (hb := { uid := u + 3, origin := .gen, hint := "unit" })
          (tb := { uid := u + 4, origin := .gen, hint := "units" })
          (yb := { uid := u + 5, origin := .gen, hint := "bytes" })
          (ch := { uid := u + 6, origin := .gen, hint := "chooseData" })
          (maxUidExpr_fresh S _ hbig) (maxUidExpr_fresh S _ (by simp; omega))
          (maxUidExpr_fresh S _ (by simp; omega)) (maxUidExpr_fresh S _ (by simp; omega))
          ((VarId.beq_false_iff _ _).mpr (.inr (by simp; omega)))
          ((VarId.beq_false_iff _ _).mpr (.inr (by simp; omega)))
          ((VarId.beq_false_iff _ _).mpr (.inr (by simp)))
          ((VarId.beq_false_iff _ _).mpr (.inr (by simp; omega)))
          ((VarId.beq_false_iff _ _).mpr (.inr (by simp; omega)))
          ((VarId.beq_false_iff _ _).mpr (.inr (by simp; omega)))
        rw [← hrd] at hins
        have hinner := (ih ((k, keyGuardWalk base r) :: Γ)).trans hins
          (fun env hG hf => hrestf env hG hf)
        refine ((FactRel.let_single (er := er) (keyGuardWalk base r) (.inl hk) (.inr rfl)
          (hr _ (.head _) Γ) hinner hpush).congr_left
          (fun env => lowerTotalExpr_let_cons env _ _ _)
          (fun avoid => freshIn_let_cons avoid _ _ _)).congr_right ?_
        intro env
        dsimp only
        rw [lowerTotalExpr_let_cons, lowerTotalExpr_let_single, lowerTotalExpr_let_single,
          lowerTotalExpr_let_four, hS]
      · exact plain
    · exact plain

theorem keyGuardWalk_factRel (base : Nat) :
    ∀ (e : Expr) (Γ : List (VarId × Expr)), maxUidExpr e < base →
      FactRel (GenSafe base) PF Γ e (keyGuardWalk base e)
  | .Let binds body, Γ, hmax => by
    rw [keyGuardWalk.eq_1]
    simp only [maxUidExpr] at hmax
    exact keyGuardBindings_factRel base body
      (fun Γ' => keyGuardWalk_factRel base body Γ' (by omega))
      (fun env' hG' hf' => keyGuardWalk_fresh base body env' hG' (by omega) hf')
      binds (fun b hb => by have := (maxUidExprBinds_mem' hb).1; omega)
      (fun b hb Γ' => keyGuardWalk_factRel base b.2.1 Γ'
        (by have := (maxUidExprBinds_mem' hb).2; omega))
      (fun b hb env' hG' hf' => keyGuardWalk_fresh base b.2.1 env' hG'
        (by have := (maxUidExprBinds_mem' hb).2; omega) hf') Γ
  | .Lam x b, Γ, hmax => by
    rw [keyGuardWalk.eq_2]
    simp only [maxUidExpr] at hmax
    exact (keyGuardWalk_factRel base b Γ (by omega)).lam (.inl (by omega))
  | .Fix f b, Γ, hmax => by
    rw [keyGuardWalk.eq_3]
    simp only [maxUidExpr] at hmax
    cases b with
    | Lam x inner =>
      rw [keyGuardWalk.eq_2]
      simp only [maxUidExpr] at hmax
      exact (keyGuardWalk_factRel base inner Γ (by omega)).fix_lam (.inl (by omega))
        (.inl (by omega)) (fun y hy => .inr (by rw [hy]; simp))
    | _ =>
      intro env t _ _ _ _ _ hlow
      rw [MIR.lowerTotalExpr_fix_nonlam_none env f _ (by intros; simp)] at hlow
      cases hlow
  | .App f a, Γ, hmax => by
    rw [keyGuardWalk.eq_4]
    simp only [maxUidExpr] at hmax
    exact (keyGuardWalk_factRel base f Γ (by omega)).app (keyGuardWalk_factRel base a Γ (by omega))
  | .Force b, Γ, hmax => by
    rw [keyGuardWalk.eq_5]
    simp only [maxUidExpr] at hmax
    exact (keyGuardWalk_factRel base b Γ (by omega)).force
  | .Delay b, Γ, hmax => by
    rw [keyGuardWalk.eq_6]
    simp only [maxUidExpr] at hmax
    exact (keyGuardWalk_factRel base b Γ (by omega)).delay
  | .Constr tag fields, Γ, hmax => by
    rw [keyGuardWalk.eq_7]
    simp only [maxUidExpr] at hmax
    exact FactRel.constr (listRel_attach_map fields _ fun c hc => keyGuardWalk_factRel base c Γ
      (by have := maxUidExpr_le_maxUidExprList_of_mem hc; omega))
  | .Case scrut alts, Γ, hmax => by
    rw [keyGuardWalk.eq_8]
    simp only [maxUidExpr] at hmax
    exact FactRel.case (keyGuardWalk_factRel base scrut Γ (by omega))
      (listRel_attach_map alts _ fun c hc => keyGuardWalk_factRel base c Γ
        (by have := maxUidExpr_le_maxUidExprList_of_mem hc; omega))
  | .Var _, Γ, _ => by rw [keyGuardWalk.eq_9]; exact FactRel.refl _ _ _ _
  | .Lit _, Γ, _ => by rw [keyGuardWalk.eq_10]; exact FactRel.refl _ _ _ _
  | .Builtin _, Γ, _ => by rw [keyGuardWalk.eq_11]; exact FactRel.refl _ _ _ _
  | .Error, Γ, _ => by rw [keyGuardWalk.eq_12]; exact FactRel.refl _ _ _ _
termination_by e => exprSize e
decreasing_by
  all_goals first
    | (subst_vars; simp only [exprSize]; omega)
    | (simp only [exprSize]; have := exprSize_pos body; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)
    | (have := exprSizeBinds_mem_lt (by assumption); simp only [exprSize]; have := exprSize_pos body; omega)

end Moist.Verified.ShapeFacts

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced Moist.Verified.ShapeFacts

theorem insertKeyGuards_refines (e : Expr) : MIRCtxRefines e (insertKeyGuards e) := by
  unfold insertKeyGuards
  simp only
  split
  · rename_i hws
    refine mirCtxRefines_trans (Hygiene.uniqueOptimizationBinders_refines e) ?_
    exact mirCtxRefines_of_factRel hws
      (fun y hy => .inl (by have := freeVars_uid_lt hy; omega))
      (fun y hy => .inr (by rw [hy]; simp))
      (keyGuardWalk_factRel _ _ [] (by omega))
  · exact Hygiene.uniqueOptimizationBinders_refines e

end Moist.Verified.MIR
