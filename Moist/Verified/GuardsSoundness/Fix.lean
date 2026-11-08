import Moist.Verified.GuardsSoundness.Calls

variable [sv : Moist.CEK.SemVariant]

/-! # Calls of recursive functions terminate by induction on the shrinking argument -/

namespace Moist.Verified.Guards

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast
open Moist.Verified.KnownLists

/-! ## Names bound in a block -/

omit sv in
theorem beq_false_symm {a b : VarId} (h : (a == b) = false) : (b == a) = false := by
  cases hba : (b == a)
  · rfl
  · rw [VarId.beq_true_iff] at hba
    have : (a == b) = true := by rw [VarId.beq_true_iff]; exact ⟨hba.1.symm, hba.2.symm⟩
    rw [h] at this; cases this

omit sv in
/-- A name outside a block keeps its value across the block. -/
theorem bound_transport {y : VarId} {Q : CekValue → Prop} :
    ∀ (bs : List VarId) (fs : List CekValue) {env : List VarId} {ρ : CekEnv},
      fs.length = bs.length → (∀ b ∈ bs, (b == y) = false) → BoundValue env ρ y Q →
      BoundValue (bs.reverse ++ env) (extendAll ρ fs) y Q
  | [], [], _, _, _, _, h => h
  | b :: bs, f :: fs, env, ρ, hl, hne, h => by
    have := bound_transport bs fs (env := b :: env) (ρ := ρ.extend f) (by simpa using hl)
      (fun b' hb' => hne b' (.tail _ hb')) (h.extend (hne b (.head _)) f)
    simpa [extendAll] using this
  | [], _ :: _, _, _, h, _, _ | _ :: _, [], _, _, h, _, _ => by simp at h

omit sv in
theorem envDistinct_prefix : ∀ (pre : List VarId) {y : VarId} {env : List VarId},
    EnvDistinct (pre ++ y :: env) → ∀ x ∈ pre, (x == y) = false
  | [], _, _, _, _, hx => by cases hx
  | z :: pre, y, env, hd, x, hx => by
    obtain ⟨hz, hd'⟩ := hd
    rcases List.mem_cons.mp hx with rfl | hx
    · cases hxy : (x == y)
      · rfl
      · exfalso
        have : (envLookupT (pre ++ y :: env) x).isSome = true := by
          rw [envLookupT_congr hxy]
          exact envLookupT_append_isSome pre (by simp [envLookupT_cons_self])
        rw [show pre.append (y :: env) = pre ++ y :: env from rfl] at hz
        rw [hz] at this; cases this
    · exact envDistinct_prefix pre hd' x hx

/-- In a block of distinct names, each name holds its own value. -/
theorem extendAll_bound : ∀ (bs : List VarId) (fs : List CekValue) {env : List VarId} {ρ : CekEnv},
    fs.length = bs.length → EnvDistinct (bs.reverse ++ env) →
    ∀ (i : Nat) (b : VarId) (f : CekValue), bs[i]? = some b → fs[i]? = some f →
      BoundValue (bs.reverse ++ env) (extendAll ρ fs) b (· = f)
  | b :: bs, f :: fs, env, ρ, hl, hd, i, x, w, hb, hf => by
    have hd' : EnvDistinct (bs.reverse ++ b :: env) := by simpa using hd
    cases i with
    | zero =>
      have hb' : x = b := by simpa using hb.symm
      have hf' : w = f := by simpa using hf.symm
      rw [hb', hf']
      have := bound_transport bs fs (env := b :: env) (ρ := ρ.extend f) (by simpa using hl)
        (fun z hz => envDistinct_prefix bs.reverse hd' z (List.mem_reverse.mpr hz))
        (BoundValue.self (varId_beq_self b) (rfl : f = f))
      have h2 := this.mono (R := fun u => u = f) (fun u hu => hu.symm)
      simpa [extendAll] using h2
    | succ i =>
      simpa [extendAll] using extendAll_bound bs fs (env := b :: env) (ρ := ρ.extend f)
        (by simpa using hl) hd' i x w (by simpa using hb) (by simpa using hf)
  | [], _, _, _, _, _, _, _, _, hb, _ => by simp at hb
  | _ :: _, [], _, _, hl, _, _, _, _, _, _ => by simp at hl

/-! ## A name not used anywhere -/

def pickFresh (names : List VarId) (k : Nat) : VarId := ⟨(names.map VarId.uid).sum + k + 1, .gen, "s"⟩

omit sv in
theorem uid_le_sum : ∀ {names : List VarId} {y : VarId}, y ∈ names → y.uid ≤ (names.map VarId.uid).sum
  | _ :: _, _, .head _ => by simp
  | _ :: _, _, .tail _ h => by have := uid_le_sum h; simp; omega

omit sv in
theorem pickFresh_ne {names : List VarId} {k : Nat} {y : VarId} (hy : y ∈ names) :
    (pickFresh names k == y) = false := by
  rw [VarId.beq_false_iff]
  right
  have := uid_le_sum hy
  simp [pickFresh]; omega

omit sv in
theorem pickFresh_uid (names : List VarId) (k : Nat) : k < (pickFresh names k).uid := by
  simp [pickFresh]; omega

omit sv in
theorem envLookupT_none_of_ne : ∀ {env : List VarId} {s : VarId}, (∀ y ∈ env, (s == y) = false) →
    envLookupT env s = none
  | [], _, _ => rfl
  | y :: env, s, h => by
    rw [envLookupT_cons_neq y s env (beq_false_symm (h y (.head _)))]
    rw [envLookupT_none_of_ne (fun z hz => h z (.tail _ hz))]; rfl

/-- The names a context mentions. -/
def ctxNames (c : TCtx) : List VarId :=
  c.facts.map (·.1) ++ c.lists ++ c.roles.flatMap fun r => r.fn :: r.base :: r.small

omit sv in
theorem fresh_of_ne {c : TCtx} {s : VarId} (h : ∀ y ∈ ctxNames c, (s == y) = false) : c.fresh s = true := by
  have hn : ∀ y ∈ ctxNames c, (y == s) = false := fun y hy => beq_false_symm (h y hy)
  unfold TCtx.fresh
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [List.any_eq_false]
    intro e he
    simpa using hn e.1 (by simp [ctxNames]; exact .inl ⟨e.2, he⟩)
  · rw [List.contains_eq_any_beq, List.any_eq_false]
    intro y hy
    simpa using h y (by simp [ctxNames, hy])
  · intro r hr
    have mem : ∀ y, (y = r.fn ∨ y = r.base ∨ y ∈ r.small) → y ∈ ctxNames c := by
      intro y hy
      simp only [ctxNames, List.mem_append, List.mem_flatMap, List.mem_cons]
      exact .inr ⟨r, hr, hy⟩
    refine ⟨⟨by simpa using hn r.fn (mem _ (.inl rfl)), by simpa using hn r.base (mem _ (.inr (.inl rfl)))⟩, ?_⟩
    rw [List.contains_eq_any_beq, List.any_eq_false]
    intro y hy
    simpa using h y (mem y (.inr (.inr hy)))

theorem Inv.addLists' {c : TCtx} {env : List VarId} {ρ : CekEnv} (h : Inv c env ρ) :
    ∀ (xs : List VarId), (∀ x ∈ xs, BoundValue env ρ x ListValue) → Inv (c.addLists xs) env ρ
  | [], _ => by simpa [TCtx.addLists] using h
  | x :: xs, hx => by
    have := (Inv.addLists' h xs (fun y hy => hx y (.tail _ hy))).addList (hx x (.head _))
    simpa [TCtx.addLists] using this

omit sv in
theorem rolePreds_length (r : Role) (m : Nat) : (rolePreds r m).length = r.arity := by
  simp [rolePreds]

omit sv in
theorem rolePreds_get {r : Role} {m i : Nat} {P : CekValue → Prop} (h : (rolePreds r m)[i]? = some P) :
    i < r.arity ∧ P = fun w => (i = r.index → vsize w < m) ∧ (r.lists.contains i → ListValue w) := by
  simp only [rolePreds, List.getElem?_map] at h
  rcases Nat.lt_or_ge i r.arity with hi | hi
  · rw [List.getElem?_eq_getElem (by simpa using hi), List.getElem_range] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨hi, h.symm⟩
  · rw [List.getElem?_eq_none (by simpa using hi)] at h; simp at h

omit sv in
theorem fresh_restrict {c : TCtx} {roles : List Role} (hsub : ∀ r ∈ roles, r ∈ c.roles) {x : VarId}
    (h : c.fresh x = true) : ({ c with roles := roles } : TCtx).fresh x = true := by
  unfold TCtx.fresh at h ⊢
  simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨h.1, fun r hr => h.2 r (hsub r hr)⟩

theorem Inv.restrict {c : TCtx} {roles : List Role} {env : List VarId} {ρ : CekEnv} (h : Inv c env ρ)
    (hroles : ∀ r ∈ roles, RoleHolds env ρ r) : Inv { c with roles := roles } env ρ :=
  ⟨h.wf, h.len, h.facts, h.lists, hroles⟩

/-- The calls of a recursive function whose body was checked with its role. -/
theorem fix_calls {n : Nat} (IH : ChkSound n) {c : TCtx} {roles : List Role} {res : VMode}
    {f p : VarId} {body : Expr} {positions : List Nat} {j : Nat} {base : VarId}
    (hbase : (p :: (lamSpine body).1)[j]? = some base)
    (hchk : chk n (TCtx.mk c.facts (argListParams positions (p :: (lamSpine body).1) ++ c.lists)
        (⟨f, (p :: (lamSpine body).1).length, j, base, [], positions, res⟩ :: roles))
        res false (lamSpine body).2 = true)
    (hff : c.fresh f = true) (hpf : ∀ q ∈ p :: (lamSpine body).1, c.fresh q = true)
    {env : List VarId} {ρ : CekEnv} (hρ : Inv c env ρ) (hroles : ∀ r ∈ roles, RoleHolds env ρ r)
    (hsub : ∀ r ∈ roles, r ∈ c.roles)
    (hd : EnvDistinct env) (hfr : freshIn env (.Fix f (.Lam p body)) = true)
    {t : Term} (hlow : lowerTotalExpr env (.Fix f (.Lam p body)) = some t) :
    ∃ tB, Halts ρ t (fixVal tB ρ) ∧
      ∀ m, CallsOK res
        (rolePreds ⟨f, (p :: (lamSpine body).1).length, j, base, [], positions, res⟩ m) (fixVal tB ρ) := by
  generalize hr : (⟨f, (p :: (lamSpine body).1).length, j, base, [], positions, res⟩ : Role) = r at hchk ⊢
  generalize hps : (lamSpine body).1 = ps at hbase hchk hpf hr
  generalize hin : (lamSpine body).2 = inner at hchk
  have hbody : body = Advanced.lams ps inner := by rw [← hps, ← hin, lamSpine_spec]
  let c0 : TCtx := { c with roles := roles }
  have hρ0 : Inv c0 env ρ := hρ.restrict hroles
  -- a fresh name for the self-application binder
  let s := pickFresh (env ++ ctxNames c ++ (f :: p :: ps)) (max (maxUidExpr body) (maxUidExpr (expandFix body)))
  have hsne : ∀ y ∈ env ++ ctxNames c ++ (f :: p :: ps), (s == y) = false := fun y hy => pickFresh_ne hy
  have hsuid : max (maxUidExpr body) (maxUidExpr (expandFix body)) < s.uid :=
    pickFresh_uid (env ++ ctxNames c ++ (f :: p :: ps)) (max (maxUidExpr body) (maxUidExpr (expandFix body)))
  have hpuid : p.uid < s.uid := by
    have hle := uid_le_sum (names := env ++ ctxNames c ++ (f :: p :: ps)) (y := p) (by simp)
    show p.uid < ((env ++ ctxNames c ++ (f :: p :: ps)).map VarId.uid).sum +
      max (maxUidExpr body) (maxUidExpr (expandFix body)) + 1
    omega
  have hs_free : (freeVars (expandFix body)).contains s = false :=
    maxUidExpr_fresh _ _ (by omega)
  rw [lowerTotalExpr_fix_lam_with_fresh env f p body s hs_free] at hlow
  cases hb : lowerTotal (p :: f :: s :: env) (expandFix body) with
  | none => rw [hb] at hlow; cases hlow
  | some tb =>
  rw [hb] at hlow; cases hlow
  have htb : lowerTotalExpr (p :: f :: s :: env) body = some tb := hb
  rw [hbody] at htb
  obtain ⟨ti, hti, htbe⟩ := lower_lams ps inner htb
  refine ⟨tb, reaches_trans ⟨16, fix_steps tb [] ρ⟩ (reaches_of_steps 1 rfl), ?_⟩
  -- facts about the environment of the body
  have hclosed : closedAt (env.length + 3) tb = true := by
    simpa using MIR.lowerTotalExpr_closedAt htb
  obtain ⟨hfixwf, hfixlen, hrecwf⟩ := fixEnv_wf hρ.wf hρ.len hclosed
  have hselfwf := selfVal_wf hρ.wf hρ.len hclosed
  have hsfresh : c0.fresh s = true :=
    fresh_restrict hsub (fresh_of_ne fun y hy => hsne y (by simp [hy]))
  have hρ1 : Inv c0 (s :: env) (ρ.extend (selfVal tb ρ)) := hρ0.extend hsfresh hselfwf
  have hρ2 : Inv c0 (f :: s :: env) (fixEnv tb ρ) := hρ1.extend (fresh_restrict hsub hff) hrecwf
  simp only [freshIn, Bool.and_eq_true] at hfr
  obtain ⟨hfnone, hpnone, hbfresh⟩ := hfr
  have hsenv : envLookupT env s = none := envLookupT_none_of_ne fun y hy => hsne y (by simp [hy])
  have hd2 : EnvDistinct (f :: s :: env) := by
    refine ⟨?_, hsenv, hd⟩
    rw [envLookupT_cons_neq s f env (hsne f (by simp))]
    simp only [Option.isNone_iff_eq_none] at hfnone
    rw [hfnone]; rfl
  have hfr2 : freshIn (f :: s :: env) (Advanced.lams (p :: ps) inner) = true := by
    rw [lams_cons, ← hbody]
    refine freshIn_avoids (.Lam p body) (avoid := f :: env) ?_ ?_
    · simp only [freshIn, Bool.and_eq_true]; exact ⟨hpnone, hbfresh⟩
    · intro y hy
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
          have hy : y.uid = s.uid := this.2.symm
          simp only [maxUidExpr]; omega
        · left; simpa using hy
  intro m
  induction m using Nat.strongRecOn with
  | _ m ihm =>
  have hfv : fixVal tb ρ = .VLam (lamChain ps ti) (fixEnv tb ρ) := by
    show CekValue.VLam tb (fixEnv tb ρ) = _
    rw [show lamChain ps ti = tb from htbe.symm]
  have hrl : (rolePreds r m).length = ps.length + 1 := by rw [rolePreds_length, ← hr]; rfl
  rw [hfv]
  refine callsOK_lams ps _ ti (fixEnv tb ρ) hrl ?_
  intro ws hl hws hP
  have hlen' : ws.length = (p :: ps).length := by rw [hl, hrl]; rfl
  obtain ⟨h1, h2, h3, _, _⟩ := bind_fields (p :: ps) inner ws hρ2 hd2 hfr2
    (fun q hq => fresh_restrict hsub (hpf q hq)) hws hlen'
  have hti' : lowerTotalExpr ((p :: ps).reverse ++ f :: s :: env) inner = some ti := by simpa using hti
  have hargP : ∀ i w, ws[i]? = some w → (i = j → vsize w < m) ∧ (positions.contains i = true → ListValue w) := by
    intro i w hw
    have hi : i < (rolePreds r m).length := by rw [← hl]; exact (List.getElem?_eq_some_iff.mp hw).1
    have hP' : (rolePreds r m)[i]? = some (rolePreds r m)[i] := List.getElem?_eq_getElem hi
    have := hP i w _ hw hP'
    obtain ⟨_, heq⟩ := rolePreds_get hP'
    rw [heq] at this
    subst hr; exact this
  have hbound := extendAll_bound (p :: ps) ws (env := f :: s :: env) (ρ := fixEnv tb ρ) hlen' h2
  have hjlt : j < ws.length := by rw [hlen']; exact (List.getElem?_eq_some_iff.mp hbase).1
  obtain ⟨wj, hwj⟩ : ∃ w, ws[j]? = some w := ⟨_, List.getElem?_eq_getElem hjlt⟩
  have hL := h1.addLists' (argListParams positions (p :: ps)) (by
    intro x hx
    simp only [argListParams, List.mem_filterMap] at hx
    obtain ⟨i, hi, hix⟩ := hx
    have hilt : i < ws.length := by rw [hlen']; exact (List.getElem?_eq_some_iff.mp hix).1
    have hwi : ws[i]? = some ws[i] := List.getElem?_eq_getElem hilt
    refine (hbound i x _ hix hwi).mono fun u hu => ?_
    subst hu
    exact (hargP i _ hwi).2 (List.contains_iff_mem.mpr hi))
  have hnotf : ∀ q ∈ p :: ps, (q == f) = false := fun q hq =>
    envDistinct_prefix (p :: ps).reverse h2 q (List.mem_reverse.mpr hq)
  have hrole : RoleHolds ((p :: ps).reverse ++ f :: s :: env) (extendAll (fixEnv tb ρ) ws) r := by
    refine ⟨vsize wj, ?_, ?_, ?_⟩
    · rw [← hr]
      have hself : BoundValue (f :: s :: env) (fixEnv tb ρ) f (· = recVal tb ρ) :=
        BoundValue.self (varId_beq_self f) rfl
      refine (bound_transport (p :: ps) ws hlen' hnotf hself).mono fun u hu => ?_
      subst hu
      have hlt : vsize wj < m := (hargP j wj hwj).1 rfl
      have hfix := ihm (vsize wj) hlt
      obtain ⟨P, Ps, hPs⟩ : ∃ P Ps, rolePreds r (vsize wj) = P :: Ps := by
        cases hc : rolePreds r (vsize wj) with
        | nil => have := rolePreds_length r (vsize wj); rw [hc, ← hr] at this; simp at this
        | cons P Ps => exact ⟨P, Ps, rfl⟩
      rw [← hr] at hPs hfix
      rw [hPs] at hfix ⊢
      exact callsOK_transfer (f := fixVal tb ρ) (fun w => ⟨_, ⟨16, rec_steps tb [] ρ w⟩,
        reaches_of_steps 1 (fixVal_steps tb [] ρ w),
        fun T hT hreach => reaches_terminal_after hT (reaches_of_steps 1 (fixVal_steps tb [] ρ w)) hreach⟩) hfix
    · rw [← hr]
      exact (hbound j base wj hbase hwj).mono fun u hu => by subst hu; exact Nat.le_refl _
    · intro y hy; rw [← hr] at hy; simp at hy
  have hInv : Inv (TCtx.mk c.facts (argListParams positions (p :: ps) ++ c.lists) (r :: roles))
      ((p :: ps).reverse ++ f :: s :: env) (extendAll (fixEnv tb ρ) ws) :=
    ⟨hL.wf, hL.len, hL.facts, hL.lists, fun r' hr' => by
      rcases List.mem_cons.mp hr' with rfl | hr'
      · exact hrole
      · exact hL.roles r' hr'⟩
  exact IH _ res false inner hchk _ ti h2 h3 hti' _ hInv [] .nil (fun _ => rfl)

end Moist.Verified.Guards
