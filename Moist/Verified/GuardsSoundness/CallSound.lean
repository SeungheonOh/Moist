import Moist.Verified.GuardsSoundness.Fix

variable [sv : Moist.CEK.SemVariant]

/-! # Soundness of `callOK` -/

namespace Moist.Verified.Guards

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast
open Moist.Verified.KnownLists

omit sv in
theorem fixOK_spec {rec : Chk} {c : TCtx} {roles : List Role} {v : VMode} {f p : VarId} {body : Expr}
    {args : List Expr} (h : fixOK rec c roles v f p body args = true) :
    (p :: (lamSpine body).1).length = args.length ∧ c.fresh f = true ∧
      (∀ q ∈ p :: (lamSpine body).1, c.fresh q = true) ∧
      ∃ positions j result base,
        (∀ i ∈ positions, ∃ a, args[i]? = some a ∧ knownListValue kindFuel c.facts c.lists a = true) ∧
        result.covers v = true ∧ (p :: (lamSpine body).1)[j]? = some base ∧
        rec (TCtx.mk c.facts (argListParams positions (p :: (lamSpine body).1) ++ c.lists)
          (⟨f, (p :: (lamSpine body).1).length, j, base, [], positions, result⟩ :: roles))
          result false (lamSpine body).2 = true := by
  simp only [fixOK, Bool.and_eq_true, List.any_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hlen, hf⟩, hps⟩, positions, _, hpos, j, _, result, _, hcov, hrec⟩ := h
  refine ⟨hlen, hf, hps, positions, j, result, ?_⟩
  split at hrec
  · rename_i base hbase
    refine ⟨base, fun i hi => ?_, hcov, hbase, hrec⟩
    have := hpos i hi
    split at this
    · rename_i a ha; exact ⟨a, ha, this⟩
    · cases this
  · cases hrec

/-- Arguments that are known lists, and nothing else, for the call of a recursive function. -/
def listPreds (k : Nat) (positions : List Nat) : List (CekValue → Prop) :=
  (List.range k).map fun i w => positions.contains i = true → ListValue w

omit sv in
theorem listPreds_get {k : Nat} {positions : List Nat} {i : Nat} {P : CekValue → Prop}
    (h : (listPreds k positions)[i]? = some P) :
    i < k ∧ P = fun w => positions.contains i = true → ListValue w := by
  simp only [listPreds, List.getElem?_map] at h
  rcases Nat.lt_or_ge i k with hi | hi
  · rw [List.getElem?_eq_getElem (by simpa using hi), List.getElem_range] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨hi, h.symm⟩
  · rw [List.getElem?_eq_none (by simpa using hi)] at h; simp at h

/-- All bounds at once: a recursive function's calls with list arguments terminate. -/
theorem fix_calls_unbounded {res : VMode} {f : VarId} {k j : Nat} {base : VarId} {positions : List Nat}
    {fv : CekValue} (h : ∀ m, CallsOK res (rolePreds ⟨f, k, j, base, [], positions, res⟩ m) fv) :
    CallsOK res (listPreds k positions) fv := by
  refine callsOK_relax _ _ fv (fun m => by simp [rolePreds_length, listPreds]) ?_ h
  intro i Q hQ w hq
  obtain ⟨_, rfl⟩ := listPreds_get hQ
  refine ⟨vsize w + 1, fun m hm P hP => ?_⟩
  obtain ⟨_, rfl⟩ := rolePreds_get hP
  exact ⟨fun _ => by simp only at *; omega, hq⟩

/-- An argument a role accepts as shrinking is below the role's bound. -/
theorem shrinks_sound {c : TCtx} {env : List VarId} {ρ : CekEnv} (hρ : Inv c env ρ) (hd : EnvDistinct env)
    {r : Role} {m : Nat} (hbase : BoundValue env ρ r.base (fun w => vsize w ≤ m))
    (hsmall : ∀ y, r.small.contains y = true → BoundValue env ρ y (fun w => vsize w < m))
    {a : Expr} (h : r.shrinks c.facts a = true) {ta : Term} (hta : lowerTotalExpr env a = some ta)
    {w : CekValue} (hw : Halts ρ ta w) : vsize w < m := by
  unfold Role.shrinks at h
  split at h
  · rename_i y
    obtain ⟨j, hj, rfl⟩ := lowerTotalExpr_var_some hta
    obtain ⟨u, hu, hlt⟩ := hsmall y h j hj
    rw [halts_var hw] at hu; cases hu; exact hlt
  · rename_i g z
    simp only [Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨hg, hz⟩ := h
    split at hg
    · rename_i hgt
      obtain ⟨tg, tz, htg, htz, rfl⟩ := lowerTotalExpr_app_some hta
      obtain ⟨wg, wz, hwg, hwz, rest⟩ := halts_apply hw
      have hp : builtinProtocolAfterSuccess (resolveHead kindFuel c.facts g) =
          some (.TailList, .one .argV) := by rw [hgt]; rfl
      have hstate := resolveHead_protocol pf_produces _ _ _ hp hρ.facts hd htg hwg
      obtain ⟨args, hlen, heval⟩ := saturated_apply hstate rest
      have h1 : valueArity (expectedArgs .TailList) = 1 := rfl
      rw [h1] at hlen
      have hargs : args = [] := by
        cases args with
        | nil => rfl
        | cons _ _ => simp at hlen
      subst hargs
      have hsm := tailList_smaller heval
      obtain ⟨j, hj, rfl⟩ := lowerTotalExpr_var_some htz
      have hzv := halts_var hwz
      rcases hz with hz | hz
      · obtain ⟨u, hu, hle⟩ := hbase j (by rw [← envLookupT_congr hz]; exact hj)
        rw [hzv] at hu; cases hu; omega
      · obtain ⟨u, hu, hlt⟩ := hsmall z hz j hj
        rw [hzv] at hu; cases hu; omega
    · cases hg
  · cases h

theorem knownList_arg {c : TCtx} {env : List VarId} {ρ : CekEnv} (hρ : Inv c env ρ) (hd : EnvDistinct env)
    {a : Expr} (h : knownListValue kindFuel c.facts c.lists a = true) {ta : Term}
    (hta : lowerTotalExpr env a = some ta) {w : CekValue} (hw : Halts ρ ta w) : ListValue w :=
  knownListValue_sound _ _ _ _ h hρ.produces hρ.lists hd hta hw

omit sv in
theorem VMode.covers_refl : ∀ (m : VMode), m.covers m = true
  | .term => rfl
  | .inert => rfl
  | .bool => rfl
  | .constrs ks => by simp [VMode.covers]

/-- The invariant without roles, in the environment where a recorded value was produced. -/
theorem Inv.dropRoles {c : TCtx} {env : List VarId} {ρ : CekEnv} (h : Inv c env ρ) (hd : EnvDistinct env)
    {k : Nat} (hk : k ≤ env.length) (hf : FactsHold PF c.facts (env.drop k) (dropEnv k ρ)) :
    Inv { c with roles := [] } (env.drop k) (dropEnv k ρ) where
  wf := by simpa using envWellFormed_dropEnv h.wf k
  len := by have := h.len; simp [dropEnv_length]; omega
  facts := hf
  lists := ListsHold.drop h.lists hd k
  roles := fun _ hr => by cases hr

omit sv in
theorem fresh_noRoles {c : TCtx} {x : VarId} (h : c.fresh x = true) :
    ({ c with roles := [] } : TCtx).fresh x = true := fresh_restrict (fun _ hr => by cases hr) h

/-- The calls `callOK` accepts return in the requested mode. -/
theorem callOK_sound {n : Nat} (IH : ChkSound n) {c : TCtx} {v : VMode} {e : Expr}
    (hcall : callOK (chk n) c v (appSpine e).1 (appSpine e).2 = true)
    (hargs : (appSpine e).2.all (chk n c .term false) = true)
    {env : List VarId} {t : Term} (hd : EnvDistinct env) (hfr : freshIn env e = true)
    (hlow : lowerTotalExpr env e = some t) {ρ : CekEnv} (hρ : Inv c env ρ) :
    Errs ρ t ∨ ∃ r, Halts ρ t r ∧ ModeV v r := by
  obtain ⟨th, targs, hth, htargs, hreach⟩ := appSpine_lower e hlow
  obtain ⟨hfh, hfa⟩ := appSpine_fresh e hfr
  have hlenA := lowerList_len htargs
  have hreach' : Reaches (.compute [] ρ t) (.compute (targs.map (fun ta => Frame.arg ta ρ)) ρ th) := by
    simpa using hreach ρ []
  -- every argument terminates
  have harg : ∀ (i : Nat) (ta : Term), targs[i]? = some ta → ∃ a, (appSpine e).2[i]? = some a ∧
      lowerTotalExpr env a = some ta ∧ (Errs ρ ta ∨ ∃ w, Halts ρ ta w ∧ ValueWellFormed w) := by
    intro i ta hi
    obtain ⟨a, hai, hla⟩ := lowerList_elem htargs hi
    refine ⟨a, hai, hla, ?_⟩
    have hca := List.all_eq_true.mp hargs a (List.mem_of_getElem? hai)
    rcases (IH c .term false a hca env ta hd (hfa a (List.mem_of_getElem? hai)) hla).term hρ with he | ⟨w, hw⟩
    · exact .inl he
    · exact .inr ⟨w, hw, halts_wellFormed hρ.wf hρ.len (MIR.lowerTotalExpr_closedAt hla) hw⟩
  -- a call given the head's value and per-argument facts
  have finish : ∀ (f : CekValue) (Ps : List (CekValue → Prop)) (m : VMode), Halts ρ th f →
      CallsOK m Ps f → Ps.length = (appSpine e).2.length → m.covers v = true →
      (∀ (i : Nat) (a : Expr) (P : CekValue → Prop), (appSpine e).2[i]? = some a → Ps[i]? = some P →
        ∀ (ta : Term) (w : CekValue),
        lowerTotalExpr env a = some ta → Halts ρ ta w → P w) →
      Errs ρ t ∨ ∃ r, Halts ρ t r ∧ ModeV v r := by
    intro f Ps m hf hc hl hcov hP
    rcases call_ends hreach' hf hc (by rw [hlenA, hl]) (fun i ta P hi hPi => by
      obtain ⟨a, hai, hla, hterm⟩ := harg i ta hi
      rcases hterm with he | ⟨w, hw, hwf⟩
      · exact .inl he
      · exact .inr ⟨w, hw, hwf, hP i a P hai hPi ta w hla hw⟩) with he | ⟨r, hr, hm⟩
    · exact .inl he
    · exact .inr ⟨r, hr, VMode.covers_sound hcov hm⟩
  -- the per-argument fact for known-list positions
  have listArg : ∀ (positions : List Nat),
      (∀ i ∈ positions, ∃ a, (appSpine e).2[i]? = some a ∧ knownListValue kindFuel c.facts c.lists a = true) →
      ∀ (i : Nat) (a : Expr), (appSpine e).2[i]? = some a → positions.contains i = true →
        ∀ (ta : Term) (w : CekValue), lowerTotalExpr env a = some ta → Halts ρ ta w → ListValue w := by
    intro positions hpos i a hai hi ta w hta hw
    obtain ⟨a', hai', hk⟩ := hpos i (List.contains_iff_mem.mp hi)
    rw [hai] at hai'; cases hai'
    exact knownList_arg hρ hd hk hta hw
  generalize hH : (appSpine e).1 = h at hcall hth hfh
  unfold callOK at hcall
  split at hcall
  · rename_i x
    obtain ⟨i, hi, rfl⟩ := lowerTotalExpr_var_some hth
    obtain ⟨fv, hfv⟩ := halts_var_wf hρ.wf (envLookupT_lt hi)
    split at hcall
    · rename_i r hr
      have hrmem := List.mem_of_find?_eq_some hr
      have hfx : (r.fn == x) = true := by have := List.find?_some hr; simpa using this
      obtain ⟨m, hfn, hbase, hsmall⟩ := hρ.roles r hrmem
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hcall
      obtain ⟨⟨⟨hlen, hidx⟩, hlists⟩, hcov⟩ := hcall
      obtain ⟨fv', hfv', hcalls⟩ := hfn i (by rw [envLookupT_congr hfx]; exact hi)
      rw [halts_var hfv] at hfv'; cases hfv'
      refine finish fv (rolePreds r m) r.result hfv hcalls (by rw [rolePreds_length]; exact hlen.symm) hcov ?_
      intro k a P hak hPk ta w hta hw
      obtain ⟨_, rfl⟩ := rolePreds_get hPk
      refine ⟨fun hk => ?_, fun hk => ?_⟩
      · subst hk
        rw [hak] at hidx
        exact shrinks_sound hρ hd hbase hsmall hidx hta hw
      · have := hlists k (List.contains_iff_mem.mp hk)
        rw [hak] at this
        exact knownList_arg hρ hd this hta hw
    · split at hcall
      · rename_i y rhs hfact
        obtain ⟨k, hk, hpf, hfacts', hd'⟩ := fact_of_var hρ.facts hd hfact (by rw [lowerTotalExpr_var, hi]; rfl) hfv
        obtain ⟨⟨trhs, htrhs, hhalt⟩, hfrr⟩ := hpf
        have hρk := hρ.dropRoles hd hk hfacts'
        split at hcall
        · rename_i g q bd
          obtain ⟨hlen, hgf, hqf, positions, j, result, base, hpos, hcov, hbase, hrec⟩ := fixOK_spec hcall
          obtain ⟨tB, hhaltfix, hcalls⟩ := fix_calls (c := { c with roles := [] }) (roles := []) IH hbase hrec
            (fresh_noRoles hgf) (fun q' hq' => fresh_noRoles (hqf q' hq')) hρk (fun _ hr => by cases hr)
            (fun _ hr => by cases hr) hd' hfrr htrhs
          rw [halts_unique hhalt hhaltfix] at hfv
          refine finish _ (listPreds (q :: (lamSpine bd).1).length positions) result hfv
            (fix_calls_unbounded hcalls) (by simp [listPreds, hlen]) hcov ?_
          intro i' a P hai hPi ta w hta hw
          obtain ⟨_, rfl⟩ := listPreds_get hPi
          exact fun hc => listArg positions hpos i' a hai hc ta w hta hw
        · rename_i hnotfix
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hcall
          obtain ⟨⟨⟨hlen, hpos0⟩, hpf⟩, hbody⟩ := hcall
          have hrhs : rhs = Advanced.lams (lamSpine rhs).1 (lamSpine rhs).2 := (lamSpine_spec rhs).symm
          obtain ⟨tbody, htbody, htr⟩ := lower_lams _ _ (by rw [← hrhs]; exact htrhs)
          cases hps : (lamSpine rhs).1 with
          | nil => rw [hps] at hpos0; simp at hpos0
          | cons p1 ps =>
          rw [hps] at htr
          rw [htr] at hhalt
          have hfeq : fv = .VLam (lamChain ps tbody) (dropEnv k ρ) := halts_lam hhalt
          let positions := argListPositions c (appSpine e).2
          have hcalls : CallsOK v (listPreds (p1 :: ps).length positions) fv := by
            rw [hfeq]
            refine callsOK_lams ps _ tbody _ (by simp [listPreds]) ?_
            intro ws hl hws hP
            have hlw : ws.length = (p1 :: ps).length := by rw [hl]; simp [listPreds]
            obtain ⟨h1, h2, h3, _, _⟩ := bind_fields (p1 :: ps) (lamSpine rhs).2 ws hρk hd'
              (by rw [← hps, ← hrhs]; exact hfrr) (fun q hq => fresh_noRoles (hpf q (by rw [hps]; exact hq)))
              hws hlw
            have hbound := extendAll_bound (p1 :: ps) ws (ρ := dropEnv k ρ) hlw h2
            have hL := h1.addLists' (argListParams positions (p1 :: ps)) (by
              intro z hz
              simp only [argListParams, List.mem_filterMap] at hz
              obtain ⟨i', hi', hiz⟩ := hz
              have hilt : i' < ws.length := by rw [hlw]; exact (List.getElem?_eq_some_iff.mp hiz).1
              have hwi : ws[i']? = some ws[i'] := List.getElem?_eq_getElem hilt
              refine (hbound i' z _ hiz hwi).mono fun u hu => ?_
              subst hu
              have hPi : (listPreds (p1 :: ps).length positions)[i']? =
                  some (fun w => positions.contains i' = true → ListValue w) := by
                simp only [listPreds, List.getElem?_map]
                rw [List.getElem?_eq_getElem (by simpa [← hlw] using hilt), List.getElem_range]; rfl
              exact hP i' _ _ hwi hPi (List.contains_iff_mem.mpr hi'))
            have hbody' : chk n (({ c with roles := [] } : TCtx).addLists (argListParams positions (p1 :: ps)))
                v false (lamSpine rhs).2 = true := by
              rw [← hps]; exact hbody
            exact IH _ v false _ hbody' _ tbody h2 h3 (by rw [← hps]; exact htbody) _ hL [] .nil (fun _ => rfl)
          refine finish fv _ v hfv hcalls (by simp only [listPreds, List.length_map, List.length_range]; rw [← hps]; exact hlen) (VMode.covers_refl v) ?_
          intro i' a P hai hPi ta w hta hw
          obtain ⟨_, rfl⟩ := listPreds_get hPi
          intro hc
          have hpos : ∀ i ∈ positions, ∃ a, (appSpine e).2[i]? = some a ∧
              knownListValue kindFuel c.facts c.lists a = true := by
            intro i hi
            simp only [positions, argListPositions, List.mem_filter, List.mem_range] at hi
            obtain ⟨hlt, hk⟩ := hi
            split at hk
            · rename_i a' ha'; exact ⟨a', ha', hk⟩
            · cases hk
          exact listArg positions hpos i' a hai hc ta w hta hw
      · cases hcall
  · rename_i g q bd
    obtain ⟨hlen, hgf, hqf, positions, j, result, base, hpos, hcov, hbase, hrec⟩ := fixOK_spec hcall
    have hrec' : chk n (TCtx.mk c.facts (argListParams positions (q :: (lamSpine bd).1) ++ c.lists)
        (⟨g, (q :: (lamSpine bd).1).length, j, base, [], positions, result⟩ :: c.roles))
        result false (lamSpine bd).2 = true := hrec
    obtain ⟨tB, hhaltfix, hcalls⟩ := fix_calls (roles := c.roles) IH hbase hrec' hgf hqf hρ hρ.roles
      (fun _ hr => hr) hd hfh hth
    refine finish _ (listPreds (q :: (lamSpine bd).1).length positions) result hhaltfix
      (fix_calls_unbounded hcalls) (by simp [listPreds, hlen]) hcov ?_
    intro i' a P hai hPi ta w hta hw
    obtain ⟨_, rfl⟩ := listPreds_get hPi
    exact fun hc => listArg positions hpos i' a hai hc ta w hta hw
  · cases hcall

end Moist.Verified.Guards
