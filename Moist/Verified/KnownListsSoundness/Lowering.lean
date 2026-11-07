import Moist.Verified.KnownListsSoundness.Rewrites

/-! # Lowering checked calls

A body accepted by `listCallsOK f m P names` lowers to a term satisfying
`Calls P m F Ls`, where `F` is the index of `f`, the self-application
wrapper of the fixed point sits at `F + 1` (its name `σ` is larger than
every name of the body), and `Ls` contains the indices of the names known to
hold lists.
-/

namespace Moist.Verified.KnownLists

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.ShapeFacts

theorem envLookupT_inj : ∀ (env : List VarId) {x y : VarId} {i : Nat},
    envLookupT env x = some i → envLookupT env y = some i → (x == y) = true
  | [], x, y, i, hx, _ => by simp [envLookupT, envLookupT.go] at hx
  | z :: env, x, y, i, hx, hy => by
    rw [envLookupT_cons] at hx hy
    split at hx
    · rename_i hzx
      cases hx
      split at hy
      · rename_i hzy
        exact VarId.beq_trans x z y (varId_beq_symm hzx) hzy
      · cases h : envLookupT env y with
        | none => rw [h] at hy; cases hy
        | some j => rw [h] at hy; simp at hy
    · split at hy
      · cases hy
        cases h : envLookupT env x with
        | none => rw [h] at hx; cases hx
        | some j => rw [h] at hx; simp at hx
      · cases hx' : envLookupT env x with
        | none => rw [hx'] at hx; cases hx
        | some j =>
          cases hy' : envLookupT env y with
          | none => rw [hy'] at hy; cases hy
          | some j' =>
            rw [hx'] at hx; rw [hy'] at hy
            simp at hx hy
            subst hx
            exact envLookupT_inj env hx' (by rw [hy']; congr 1; omega)

/-- The lowering environment of a checked body. -/
structure CheckCtx (f σ : VarId) (names env : List VarId) (F : Nat) (Ls : List Nat) : Prop where
  recur : envLookupT env f = some (F - 1)
  pos : 0 < F
  self : envLookupT env σ = some F
  lists : ∀ y, names.contains y = true → ∃ i, envLookupT env y = some i ∧ i + 1 ∈ Ls

theorem lookup_shift {env : List VarId} {x y : VarId} {i : Nat}
    (hx : (envLookupT env x).isNone = true) (hy : envLookupT env y = some i) :
    envLookupT (x :: env) y = some (i + 1) := by
  have hxy : (x == y) = false := by
    cases h : (x == y)
    · rfl
    · rw [envLookupT_congr h, hy] at hx; cases hx
  rw [envLookupT_cons_neq x y env hxy, hy]; rfl

theorem CheckCtx.cons {f σ : VarId} {names env : List VarId} {F : Nat} {Ls : List Nat}
    (h : CheckCtx f σ names env F Ls) (x : VarId) (hx : (envLookupT env x).isNone = true) :
    CheckCtx f σ names (x :: env) (F + 1) (shiftLs 1 Ls) := by
  refine ⟨?_, by omega, lookup_shift hx h.self, fun y hy => ?_⟩
  · rw [lookup_shift hx h.recur]; congr 1; have := h.pos; omega
  · obtain ⟨i, hi, hLs⟩ := h.lists y hy
    exact ⟨i + 1, lookup_shift hx hi, mem_shiftLs.mpr ⟨i + 1, hLs, rfl⟩⟩

theorem CheckCtx.tail {f σ : VarId} {names env : List VarId} {F : Nat} {Ls : List Nat}
    (h : CheckCtx f σ names env F Ls) (hd t : VarId) (hh : (envLookupT env hd).isNone = true)
    (ht : (envLookupT (hd :: env) t).isNone = true) :
    CheckCtx f σ (t :: names) (t :: hd :: env) (F + 2) (1 :: shiftLs 2 Ls) := by
  have h₂ := (h.cons hd hh).cons t ht
  refine ⟨h₂.recur, h₂.pos, h₂.self, fun y hy => ?_⟩
  simp only [List.contains_cons, Bool.or_eq_true] at hy
  rcases hy with hy | hy
  · refine ⟨0, ?_, .head _⟩
    rw [← envLookupT_congr (varId_beq_symm hy), MIR.envLookupT_cons_of_beq (varId_beq_self t)]
  · obtain ⟨i, hi, hLs⟩ := h₂.lists y hy
    refine ⟨i, hi, .tail _ ?_⟩
    obtain ⟨j, hj, hij⟩ := mem_shiftLs.mp hLs
    obtain ⟨j', hj', hjj⟩ := mem_shiftLs.mp hj
    exact mem_shiftLs.mpr ⟨j', hj', by omega⟩

/-! ## Equations of the check -/

theorem listCallsOK_var {f : VarId} {m : Nat} {P : List Nat} {names : List VarId} {x : VarId} :
    listCallsOK f m P names (.Var x) = !(x == f) := by
  rw [listCallsOK]

theorem listCallsOK_lam {f : VarId} {m : Nat} {P : List Nat} {names : List VarId} {x : VarId}
    {b : Expr} : listCallsOK f m P names (.Lam x b) = listCallsOK f m P names b := by
  rw [listCallsOK]

theorem listCallsOK_fix {f : VarId} {m : Nat} {P : List Nat} {names : List VarId} {x : VarId}
    {b : Expr} : listCallsOK f m P names (.Fix x b) = listCallsOK f m P names b := by
  rw [listCallsOK]

theorem listCallsOK_app {f : VarId} {m : Nat} {P : List Nat} {names : List VarId} {g a : Expr} :
    listCallsOK f m P names (.App g a) =
      (listCallSpine f m P names m g a ||
        (listCallsOK f m P names g && listCallsOK f m P names a)) := by
  rw [listCallsOK]

theorem listCallsOK_force {f : VarId} {m : Nat} {P : List Nat} {names : List VarId} {b : Expr} :
    listCallsOK f m P names (.Force b) = listCallsOK f m P names b := by
  rw [listCallsOK]

theorem listCallsOK_delay {f : VarId} {m : Nat} {P : List Nat} {names : List VarId} {b : Expr} :
    listCallsOK f m P names (.Delay b) = listCallsOK f m P names b := by
  rw [listCallsOK]

theorem listCallsOK_constr {f : VarId} {m : Nat} {P : List Nat} {names : List VarId} {tag : Nat}
    {fs : List Expr} :
    listCallsOK f m P names (.Constr tag fs) = listCallsOKList f m P names fs := by
  rw [listCallsOK]

theorem listCallsOK_let {f : VarId} {m : Nat} {P : List Nat} {names : List VarId}
    {bs : List (VarId × Expr × Bool)} {b : Expr} :
    listCallsOK f m P names (.Let bs b) =
      (listCallsOKBinds f m P names bs && listCallsOK f m P names b) := by
  rw [listCallsOK]

theorem listCallsOK_case {f : VarId} {m : Nat} {P : List Nat} {names : List VarId} {s : Expr}
    {alts : List Expr} (h : listCallsOK f m P names (.Case s alts) = true) :
    (∃ z hd t C rest, s = .Var z ∧ alts = .Lam hd (.Lam t C) :: rest ∧ names.contains z = true ∧
      listCallsOK f m P (t :: names) C = true ∧ listCallsOKList f m P names rest = true) ∨
    (listCallsOK f m P names s = true ∧ listCallsOKList f m P names alts = true) := by
  unfold listCallsOK at h
  split at h
  · rename_i z hd t C rest
    split at h
    · rename_i hz
      simp only [Bool.and_eq_true] at h
      exact .inl ⟨z, hd, t, C, rest, rfl, rfl, hz, h.1, h.2⟩
    · simp only [Bool.and_eq_true] at h
      exact .inr h
  · simp only [Bool.and_eq_true] at h
    exact .inr h

theorem listCallSpine_succ {f : VarId} {m : Nat} {P : List Nat} {names : List VarId} {r : Nat}
    {g a : Expr} :
    listCallSpine f m P names (r + 1) g a =
      (listArgument names P r a && listCallsOK f m P names a &&
        listCallHead f m P names r g) := by
  rw [listCallSpine]

theorem listCallSpine_zero {f : VarId} {m : Nat} {P : List Nat} {names : List VarId} {g a : Expr} :
    listCallSpine f m P names 0 g a = false := by
  rw [listCallSpine]

theorem listCallHead_eq {f : VarId} {m : Nat} {P : List Nat} {names : List VarId} {r : Nat}
    {e : Expr} (h : listCallHead f m P names r e = true) :
    (r = 0 ∧ ∃ b, e = .Var b ∧ (b == f) = true) ∨
      (∃ r' g a, r = r' + 1 ∧ e = .App g a ∧ listCallSpine f m P names (r' + 1) g a = true) := by
  unfold listCallHead at h
  split at h
  · exact .inl ⟨rfl, _, rfl, h⟩
  · exact .inr ⟨_, _, _, rfl, rfl, h⟩
  · cases h

theorem listCallsOKList_cons {f : VarId} {m : Nat} {P : List Nat} {names : List VarId} {e : Expr}
    {es : List Expr} :
    listCallsOKList f m P names (e :: es) =
      (listCallsOK f m P names e && listCallsOKList f m P names es) := by
  rw [listCallsOKList]

theorem listCallsOKBinds_cons {f : VarId} {m : Nat} {P : List Nat} {names : List VarId}
    {x : VarId} {r : Expr} {er : Bool} {bs : List (VarId × Expr × Bool)} :
    listCallsOKBinds f m P names ((x, r, er) :: bs) =
      (listCallsOK f m P names r && listCallsOKBinds f m P names bs) := by
  rw [listCallsOKBinds]

theorem listCallsOKBinds_nil {f : VarId} {m : Nat} {P : List Nat} {names : List VarId} :
    listCallsOKBinds f m P names [] = true := by
  rw [listCallsOKBinds]

theorem argOK_of_listArgument {f σ : VarId} {names env : List VarId} {F : Nat} {Ls : List Nat}
    {P : List Nat} {p : Nat} {a : Expr} {ta : Term} (hc : CheckCtx f σ names env F Ls)
    (h : listArgument names P p a = true) (hlow : lowerTotalExpr env a = some ta) :
    ArgOK P Ls p ta := by
  intro hp
  unfold listArgument at h
  have hp' : P.contains p = true := by simpa using hp
  simp only [hp', Bool.not_true, Bool.false_or] at h
  match a, h with
  | .Var y, h =>
    obtain ⟨i, hi, rfl⟩ := lowerTotalExpr_var_some hlow
    obtain ⟨i', hi', hLs⟩ := hc.lists y h
    rw [hi] at hi'; cases hi'
    exact ⟨i + 1, rfl, hLs⟩

/-- The self-application wrapper of a nested fixed point. -/
theorem calls_wrap {P : List Nat} {m F : Nat} {Ls : List Nat} {tb : Term} (hF : 0 < F)
    (h : Calls P m (F + 1 + 1 + 1) (shiftLs 1 (shiftLs 1 (shiftLs 1 Ls))) tb) :
    Calls P m F Ls (fixLamWrapUplc tb) :=
  .apply (.lam (.apply (.var (by omega) (by omega)) (.var (by omega) (by omega))))
    (.lam (.apply (.lam (.lam h))
      (.lam (.apply (.apply (.var (by omega) (by omega)) (.var (by omega) (by omega)))
        (.var (by omega) (by omega))))))

theorem freshIn_fix_body {env : List VarId} {g y s : VarId} {b : Expr}
    (hb : freshIn (y :: g :: env) b = true) (hsb : maxUidExpr b < s.uid) :
    freshIn (y :: g :: s :: env) b = true := by
  refine freshIn_avoids b hb ?_
  intro z hz
  rw [envLookupT_cons] at hz ⊢
  split
  · simp
  · rename_i hyz
    simp only [hyz, Bool.false_eq_true, if_false, Option.isSome_map] at hz ⊢
    rw [envLookupT_cons] at hz ⊢
    split
    · simp
    · rename_i hgz
      simp only [hgz, Bool.false_eq_true, if_false, Option.isSome_map] at hz ⊢
      rw [envLookupT_cons] at hz
      split at hz
      · rename_i hsz
        right
        have := (VarId.beq_true_iff s z).mp hsz
        omega
      · left; simpa using hz

mutual
  theorem lower_calls {f σ : VarId} {m : Nat} {P : List Nat} :
      ∀ (e : Expr) {names env : List VarId} {F : Nat} {Ls : List Nat} {t : Term},
        CheckCtx f σ names env F Ls → maxUidExpr e < σ.uid → freshIn env e = true →
        listCallsOK f m P names e = true → lowerTotalExpr env e = some t → Calls P m F Ls t
    | .Var x, names, env, F, Ls, t, hc, hu, _, hok, hlow => by
      obtain ⟨i, hi, rfl⟩ := lowerTotalExpr_var_some hlow
      rw [listCallsOK_var] at hok
      refine .var (fun h => ?_) (fun h => ?_)
      · have hf : envLookupT env f = some i := by rw [hc.recur]; congr 1; omega
        have := envLookupT_inj env hi hf
        simp [this] at hok
      · have hs : envLookupT env σ = some i := by rw [hc.self]; congr 1; omega
        have := (VarId.beq_true_iff x σ).mp (envLookupT_inj env hi hs)
        simp only [maxUidExpr] at hu
        omega
    | .Lit (c, ty), _, env, _, _, t, _, _, _, _, hlow => by
      rw [lowerTotalExpr_lit] at hlow; cases hlow; exact .constant
    | .Builtin b, _, env, _, _, t, _, _, _, _, hlow => by
      rw [lowerTotalExpr_builtin] at hlow; cases hlow; exact .builtin
    | .Error, _, env, _, _, t, _, _, _, _, hlow => by
      rw [lowerTotalExpr_error] at hlow; cases hlow; exact .error
    | .Lam x b, names, env, F, Ls, t, hc, hu, hfresh, hok, hlow => by
      simp only [freshIn, Bool.and_eq_true] at hfresh
      rw [listCallsOK_lam] at hok
      obtain ⟨tb, htb, rfl⟩ := lowerTotalExpr_lam_some hlow
      exact .lam (lower_calls b (hc.cons x hfresh.1) (by simp only [maxUidExpr] at hu; omega)
        hfresh.2 hok htb)
    | .Fix g body, names, env, F, Ls, t, hc, hu, hfresh, hok, hlow => by
      match body with
      | .Lam y b =>
        simp only [freshIn, Bool.and_eq_true] at hfresh
        obtain ⟨hg, hy, hb⟩ := hfresh
        rw [listCallsOK_fix, listCallsOK_lam] at hok
        simp only [maxUidExpr] at hu
        let s : VarId := ⟨envMax env + maxUidExpr (expandFix b) + maxUidExpr b + σ.uid + 1, .gen, "s"⟩
        have hs_env : envLookupT env s = none := envLookupT_none_of_gt env s (by simp [s]; omega)
        have hs_b : (freeVars (expandFix b)).contains s = false :=
          maxUidExpr_fresh _ _ (by simp [s]; omega)
        rw [lowerTotalExpr_fix_lam_with_fresh env g y b s hs_b] at hlow
        obtain ⟨tb, htb, rfl⟩ := Option.map_eq_some_iff.mp hlow
        have hgs : (envLookupT (s :: env) g).isNone = true := by
          rw [envLookupT_cons]
          have : (s == g) = false := by
            rw [VarId.beq_false_iff]; right; simp [s]; omega
          simp only [this, Bool.false_eq_true, if_false]; simpa using hg
        have hys : (envLookupT (g :: s :: env) y).isNone = true := by
          have hsy : (s == y) = false := by
            rw [VarId.beq_false_iff]; right; simp [s]; omega
          have hy2 := hy
          rw [envLookupT_cons] at hy2 ⊢
          split
          · rename_i hgy; simp [hgy] at hy2
          · rename_i hgy
            simp only [hgy, Bool.false_eq_true, if_false, Option.isNone_map] at hy2 ⊢
            rw [envLookupT_cons]
            simp only [hsy, Bool.false_eq_true, if_false, Option.isNone_map]; exact hy2
        have hc' := ((hc.cons s (by simp [hs_env])).cons g hgs).cons y hys
        have hb' := freshIn_fix_body (s := s) hb (by simp [s]; omega)
        exact calls_wrap hc.pos (lower_calls b hc' (by omega) hb' hok htb)
      | .Var _ | .Lit _ | .Builtin _ | .Error | .Fix _ _ | .App _ _ | .Force _ | .Delay _
      | .Constr _ _ | .Case _ _ | .Let _ _ =>
        rw [Moist.Verified.MIR.lowerTotalExpr_fix_nonlam_none env g _ (by intros; simp)] at hlow
        cases hlow
    | .App g a, names, env, F, Ls, t, hc, hu, hfresh, hok, hlow => by
      simp only [freshIn, Bool.and_eq_true] at hfresh
      simp only [maxUidExpr] at hu
      obtain ⟨tg, ta, htg, hta, rfl⟩ := lowerTotalExpr_app_some hlow
      rw [listCallsOK_app, Bool.or_eq_true] at hok
      rcases hok with hsp | hok
      · cases m with
        | zero => rw [listCallSpine_zero] at hsp; cases hsp
        | succ k =>
          rw [listCallSpine_succ] at hsp
          simp only [Bool.and_eq_true] at hsp
          obtain ⟨⟨harg, ha⟩, hhead⟩ := hsp
          have hspine := lower_spine k g (by omega) hc (by omega) hfresh.1 hhead htg
          rw [show k + 1 - k = 1 by omega] at hspine
          exact .call hspine (lower_calls a hc (by omega) hfresh.2 ha hta)
            (by simpa using argOK_of_listArgument hc harg hta)
      · simp only [Bool.and_eq_true] at hok
        exact .apply (lower_calls g hc (by omega) hfresh.1 hok.1 htg)
          (lower_calls a hc (by omega) hfresh.2 hok.2 hta)
    | .Force b, names, env, F, Ls, t, hc, hu, hfresh, hok, hlow => by
      simp only [freshIn] at hfresh
      rw [listCallsOK_force] at hok
      obtain ⟨tb, htb, rfl⟩ := lowerTotalExpr_force_some hlow
      exact .force (lower_calls b hc (by simp only [maxUidExpr] at hu; omega) hfresh hok htb)
    | .Delay b, names, env, F, Ls, t, hc, hu, hfresh, hok, hlow => by
      simp only [freshIn] at hfresh
      rw [listCallsOK_delay] at hok
      obtain ⟨tb, htb, rfl⟩ := lowerTotalExpr_delay_some hlow
      exact .delay (lower_calls b hc (by simp only [maxUidExpr] at hu; omega) hfresh hok htb)
    | .Constr tag fs, names, env, F, Ls, t, hc, hu, hfresh, hok, hlow => by
      simp only [freshIn] at hfresh
      rw [listCallsOK_constr] at hok
      rw [MIR.lowerTotalExpr_constr_of_list] at hlow
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp hlow
      exact .constr (lower_callsList fs hc (by simp only [maxUidExpr] at hu; omega) hfresh hok hts)
    | .Case sc alts, names, env, F, Ls, t, hc, hu, hfresh, hok, hlow => by
      simp only [freshIn, Bool.and_eq_true] at hfresh
      simp only [maxUidExpr] at hu
      obtain ⟨ts, talts, hts, htalts, rfl⟩ := lowerTotalExpr_case_some hlow
      rcases listCallsOK_case hok with ⟨z, hd, tl, C, rest, rfl, rfl, hz, hC, hrest⟩ | ⟨hs, halts⟩
      · obtain ⟨iz, hiz, rfl⟩ := lowerTotalExpr_var_some hts
        obtain ⟨iz', hiz', hLs⟩ := hc.lists z hz
        rw [hiz] at hiz'; cases hiz'
        simp only [freshInList, freshIn, Bool.and_eq_true] at hfresh
        obtain ⟨_, ⟨hh, ht, hfC⟩, hfrest⟩ := hfresh
        rw [MIR.lowerTotalExprList_cons] at htalts
        cases hA : lowerTotalExpr env (.Lam hd (.Lam tl C)) with
        | none => rw [hA] at htalts; cases htalts
        | some tA =>
        cases hR : MIR.lowerTotalExprList env rest with
        | none => rw [hA, hR] at htalts; cases htalts
        | some tR =>
        rw [hA, hR] at htalts; cases htalts
        obtain ⟨tC, htC, rfl⟩ := lowerTotalExpr_consAlt hA
        simp only [maxUidExprList, maxUidExpr] at hu
        exact .listCase hLs (lower_calls C (hc.tail hd tl hh ht) (by omega) hfC hC htC)
          (lower_callsList rest hc (by omega) hfrest hrest hR)
      · exact .case (lower_calls sc hc (by omega) hfresh.1 hs hts)
          (lower_callsList alts hc (by omega) hfresh.2 halts htalts)
    | .Let bs body, names, env, F, Ls, t, hc, hu, hfresh, hok, hlow => by
      match bs with
      | [] =>
        rw [lowerTotalExpr_let_nil] at hlow
        rw [freshIn_let_nil] at hfresh
        rw [listCallsOK_let, listCallsOKBinds_nil, Bool.true_and] at hok
        simp only [maxUidExpr, maxUidExprBinds] at hu
        exact lower_calls body hc (by omega) hfresh hok hlow
      | (x, r, er) :: rest =>
        rw [lowerTotalExpr_let_cons] at hlow
        rw [freshIn_let_cons, freshIn_let_single] at hfresh
        simp only [Bool.and_eq_true] at hfresh
        obtain ⟨⟨hfr, hx⟩, hfb⟩ := hfresh
        rw [listCallsOK_let, listCallsOKBinds_cons] at hok
        simp only [Bool.and_eq_true] at hok
        obtain ⟨⟨hr, hrest⟩, hbody⟩ := hok
        obtain ⟨tr, tb, htr, htb, rfl⟩ := lowerTotalExpr_let_single_some hlow
        have hu' := hu
        simp only [maxUidExpr, maxUidExprBinds] at hu'
        have hokb : listCallsOK f m P names (.Let rest body) = true := by
          rw [listCallsOK_let, hrest, hbody]; rfl
        exact .apply (.lam (lower_calls (.Let rest body) (hc.cons x hx)
            (by simp only [maxUidExpr]; omega) hfb hokb htb))
          (lower_calls r hc (by omega) hfr hr htr)
  termination_by e => sizeOf e

  theorem lower_callsList {f σ : VarId} {m : Nat} {P : List Nat} :
      ∀ (es : List Expr) {names env : List VarId} {F : Nat} {Ls : List Nat} {ts : List Term},
        CheckCtx f σ names env F Ls → maxUidExprList es < σ.uid → freshInList env es = true →
        listCallsOKList f m P names es = true → MIR.lowerTotalExprList env es = some ts →
        CallsList P m F Ls ts
    | [], _, env, _, _, ts, _, _, _, _, hlow => by
      rw [MIR.lowerTotalExprList_nil] at hlow; cases hlow; exact .nil
    | e :: es, names, env, F, Ls, ts, hc, hu, hfresh, hok, hlow => by
      simp only [freshInList, Bool.and_eq_true] at hfresh
      rw [listCallsOKList_cons, Bool.and_eq_true] at hok
      simp only [maxUidExprList] at hu
      rw [MIR.lowerTotalExprList_cons] at hlow
      cases he : lowerTotalExpr env e with
      | none => rw [he] at hlow; cases hlow
      | some te =>
        cases hes : MIR.lowerTotalExprList env es with
        | none => rw [he, hes] at hlow; cases hlow
        | some tes =>
          rw [he, hes] at hlow; cases hlow
          exact .cons (lower_calls e hc (by omega) hfresh.1 hok.1 he)
            (lower_callsList es hc (by omega) hfresh.2 hok.2 hes)
  termination_by es => sizeOf es

  theorem lower_spine {f σ : VarId} {m : Nat} {P : List Nat} :
      ∀ (k : Nat) (e : Expr) {names env : List VarId} {F : Nat} {Ls : List Nat} {t : Term},
        k < m → CheckCtx f σ names env F Ls → maxUidExpr e < σ.uid → freshIn env e = true →
        listCallHead f m P names k e = true → lowerTotalExpr env e = some t →
        Spine P m F Ls (m - k) t
    | k, e, names, env, F, Ls, t, hk, hc, hu, hfresh, hh, hlow => by
      rcases listCallHead_eq hh with ⟨rfl, b, rfl, hb⟩ | ⟨k', g, a, rfl, rfl, hsp⟩
      · obtain ⟨i, hi, rfl⟩ := lowerTotalExpr_var_some hlow
        rw [envLookupT_congr hb, hc.recur] at hi
        cases hi
        rw [show F - 1 + 1 = F by have := hc.pos; omega, Nat.sub_zero]
        exact .head
      · simp only [freshIn, Bool.and_eq_true] at hfresh
        simp only [maxUidExpr] at hu
        obtain ⟨tg, ta, htg, hta, rfl⟩ := lowerTotalExpr_app_some hlow
        rw [listCallSpine_succ] at hsp
        simp only [Bool.and_eq_true] at hsp
        obtain ⟨⟨harg, ha⟩, hhead⟩ := hsp
        have hspine := lower_spine k' g (by omega) hc (by omega) hfresh.1 hhead htg
        obtain ⟨r, hr⟩ : ∃ r, m - (k' + 1) = r + 1 := ⟨m - (k' + 1) - 1, by omega⟩
        rw [hr]
        rw [show m - k' = r + 2 by omega] at hspine
        exact .arg hspine (lower_calls a hc (by omega) hfresh.2 ha hta)
          (by rw [show m - (r + 2) = k' by omega]; exact argOK_of_listArgument hc harg hta)
  termination_by _ e => sizeOf e
end

end Moist.Verified.KnownLists
