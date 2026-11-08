import Moist.Verified.GuardsSoundness.Leaves

/-! # `chk` on cases -/

namespace Moist.Verified.Guards

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast
open Moist.Verified.KnownLists

theorem valueList_take : ∀ {vs : List CekValue} (k : Nat), ValueListWellFormed vs →
    ValueListWellFormed (vs.take k)
  | [], _, _ => by simpa using ValueListWellFormed.nil
  | _ :: _, 0, _ => by simpa using ValueListWellFormed.nil
  | _ :: vs, k + 1, .cons h hs => by simpa using ValueListWellFormed.cons h (valueList_take k hs)

theorem valueList_drop : ∀ {vs : List CekValue} (k : Nat), ValueListWellFormed vs →
    ValueListWellFormed (vs.drop k)
  | [], _, _ => by simpa using ValueListWellFormed.nil
  | _ :: _, 0, h => by simpa using h
  | _ :: vs, k + 1, .cons _ hs => by simpa using valueList_drop k hs

/-- The scrutinee of a successful `nullList` names a list. -/
theorem nullFlow_inv {c : TCtx} {env : List VarId} {ρ : CekEnv} {s : Expr} (h : Inv c env ρ)
    (hx : ∀ f x, s = .App f (.Var x) → resolveHead kindFuel c.facts f = .Force (.Builtin .NullList) →
      BoundValue env ρ x ListValue) :
    Inv (c.nullFlow s) env ρ := by
  unfold TCtx.nullFlow
  split
  · rename_i f x
    split
    · rename_i hf
      exact h.addList (hx f x rfl hf)
    · exact h
  · exact h

/-- The argument of a `nullList` scrutinee that returned. -/
theorem nullFlow_list {c : TCtx} {env : List VarId} {ρ : CekEnv} (hρ : Inv c env ρ)
    (hd : EnvDistinct env) {f : Expr} {x : VarId} {ts : Term} {w : CekValue}
    (hf : resolveHead kindFuel c.facts f = .Force (.Builtin .NullList))
    (hts : lowerTotalExpr env (.App f (.Var x)) = some ts) (hw : Halts ρ ts w) :
    BoundValue env ρ x ListValue := by
  obtain ⟨tf, tx, htf, htx, rfl⟩ := lowerTotalExpr_app_some hts
  obtain ⟨wf, wx, hwf, hwx, rest⟩ := halts_apply hw
  have hp : builtinProtocolAfterSuccess (resolveHead kindFuel c.facts f) =
      some (.NullList, .one .argV) := by rw [hf]; rfl
  have hstate := resolveHead_protocol pf_produces _ _ _ hp hρ.facts hd htf hwf
  obtain ⟨args, hlen, heval⟩ := saturated_apply hstate rest
  have h1 : valueArity (expectedArgs .NullList) = 1 := rfl
  rw [h1] at hlen
  have hargs : args = [] := by
    cases args with
    | nil => rfl
    | cons _ _ => simp at hlen
  subst hargs
  have hlist := nullList_arg heval
  obtain ⟨j, hj, rfl⟩ := lowerTotalExpr_var_some htx
  intro i hi
  rw [hj] at hi; cases hi
  exact ⟨wx, halts_var hwx, hlist⟩

theorem envLookupT_append_isSome : ∀ (pre : List VarId) {env : List VarId} {z : VarId},
    (envLookupT env z).isSome = true → (envLookupT (pre ++ env) z).isSome = true
  | [], _, _, h => h
  | y :: pre, env, z, h => by
    have ih := envLookupT_append_isSome pre h
    cases hyz : (y == z)
    · rw [List.cons_append, envLookupT_cons_neq y z _ hyz]; simpa using ih
    · rw [List.cons_append, ← envLookupT_congr hyz, MIR.envLookupT_cons_of_beq (varId_beq_self y)]
      rfl

/-- The value of a name whose lowering returned `w`. -/
theorem var_value {env : List VarId} {ρ : CekEnv} {z : VarId} {ts : Term} {w : CekValue}
    (hts : lowerTotalExpr env (.Var z) = some ts) (hw : Halts ρ ts w) :
    BoundValue env ρ z (· = w) ∧ (envLookupT env z).isSome = true := by
  obtain ⟨j, hj, rfl⟩ := lowerTotalExpr_var_some hts
  refine ⟨fun i hi => ?_, by simp [hj]⟩
  rw [hj] at hi; cases hi
  exact ⟨w, halts_var hw, rfl⟩

theorem Inv.addKindLists {c : TCtx} {env : List VarId} {ρ : CekEnv} {kind : Kind} {i : Nat}
    {bs : List VarId} {gs : List CekValue} (h : Inv c (bs.reverse ++ env) (extendAll ρ gs))
    (hkf : KindFields kind i gs) (hlen : gs.length = bs.length) :
    Inv (c.addLists (kindLists kind i bs)) (bs.reverse ++ env) (extendAll ρ gs) := by
  have keep : Inv (c.addLists []) (bs.reverse ++ env) (extendAll ρ gs) := by
    simpa [TCtx.addLists] using h
  unfold kindLists
  split
  · rename_i hd t
    obtain ⟨g0, g1, rfl, hl⟩ := hkf
    refine h.addList ?_
    exact BoundValue.self (varId_beq_self t) hl
  · rename_i hd t
    obtain ⟨g0, g1, rfl, hl⟩ := hkf
    refine h.addList ?_
    exact BoundValue.self (varId_beq_self t) hl
  · exact keep

/-- Running the selected alternative of a non-applied case. -/
theorem caseAlts_sound {n : Nat} (IH : ChkSound n) {c : TCtx} {v : VMode} {s : Expr} {kind : Kind}
    {alts : List Expr} (h : caseAlts (chk n) c (c.nullFlow s) v s kind alts = true)
    {env : List VarId} {ts : Term} {talts : List Term} (hd : EnvDistinct env)
    (hfalts : freshInList env alts = true) (hts : lowerTotalExpr env s = some ts)
    (htalts : MIR.lowerTotalExprList env alts = some talts)
    {ρ : CekEnv} (hρ : Inv c env ρ) {w : CekValue} (hw : Halts ρ ts w) (hkind : KindV kind w)
    (hlen : ∀ ks, kind = .constrs ks → ks.length = talts.length)
    {ta : Term} {gs : List CekValue} (hdisp : dispatch talts w = some (ta, gs)) :
    Ends v (.compute (gs.map Frame.applyArg) ρ ta) := by
  obtain ⟨i, hi, hfi, hkf⟩ := dispatch_kind hkind hlen hdisp
  obtain ⟨a, hai, hla⟩ := lowerList_elem htalts hi
  have hmem : (a, i) ∈ alts.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr hai
  unfold caseAlts at h
  have ha := List.all_eq_true.mp h (a, i) hmem
  simp only at ha
  have hfa := freshInList_get hfalts hai
  have hwwf := halts_wellFormed hρ.wf hρ.len (MIR.lowerTotalExpr_closedAt hts) hw
  have hgs := (dispatch_spec hdisp hwwf).2
  have hsmall := dispatch_smaller hdisp
  -- what binding the fields to fresh names gives
  have bind : ∀ (bs : List VarId) (body : Expr) (fs : List CekValue), a = Advanced.lams bs body →
      (∀ b ∈ bs, c.fresh b = true) → ValueListWellFormed fs → fs.length = bs.length →
      (∀ u ∈ fs, u ∈ gs) →
      ∃ tb, lowerTotalExpr (bs.reverse ++ env) body = some tb ∧
        ta = (bs.map fun _ => ()).foldr (fun _ acc => .Lam 0 acc) tb ∧
        EnvDistinct (bs.reverse ++ env) ∧ freshIn (bs.reverse ++ env) body = true ∧
        Inv ((c.nullFlow s).descend s bs) (bs.reverse ++ env) (extendAll ρ fs) := by
    intro bs body fs hab hfresh hfs hlen' hsub
    subst hab
    obtain ⟨tb, htb, hta⟩ := lower_lams bs body hla
    obtain ⟨h1, h2, h3, h4, h5⟩ := bind_fields bs body fs hρ hd hfa hfresh hfs hlen'
    refine ⟨tb, htb, hta, h2, h3, ?_⟩
    refine Inv.descend (nullFlow_inv h1 ?_) ?_
    · intro f x hs hf
      subst hs
      have := nullFlow_list hρ hd hf hts hw
      obtain ⟨_, tx, _, htx, _⟩ := lowerTotalExpr_app_some hts
      obtain ⟨j, hj, _⟩ := lowerTotalExpr_var_some htx
      exact h5 x (by simp [hj]) _ this
    · intro z hs
      subst hs
      obtain ⟨hz, hzs⟩ := var_value hts hw
      exact ⟨w, h5 z hzs _ hz, envLookupT_append_isSome bs.reverse hzs,
        fun b hb => (h4 b hb).mono fun u hu => hsmall u (hsub u hu)⟩
  -- the alternative applied to more fields than it binds
  have more : ∀ (bs : List VarId) (body : Expr), a = Advanced.lams bs body → bs.length ≤ gs.length →
      (∀ b ∈ bs, c.fresh b = true) → chk n ((c.nullFlow s).descend s bs) v true body = true →
      Ends v (.compute (gs.map Frame.applyArg) ρ ta) := by
    intro bs body hab hle hfresh hbody
    obtain ⟨tb, htb, hta, hd', hfr', hinv⟩ := bind bs body (gs.take bs.length) hab hfresh
      (valueList_take _ hgs) (by simp; omega) (fun u hu => List.mem_of_mem_take hu)
    subst hta
    have hr := lams_steps_more bs tb gs ρ [] hle
    simp only [List.append_nil] at hr
    refine Ends.of_reaches hr ?_
    simpa using IH _ v true body hbody _ tb hd' hfr' htb _ hinv _ (valueList_drop _ hgs) (fun h => by cases h)
  split at ha
  · rename_i k hk
    have hkg : k = gs.length := by
      rcases hfi with hu | hf
      · subst hu; simp [Kind.fields] at hk
      · rw [hf] at hk; cases hk; rfl
    subst hkg
    split at ha
    · rename_i bs body hpeel
      simp only [Bool.and_eq_true, List.all_eq_true] at ha
      obtain ⟨hfresh, hbody⟩ := ha
      obtain ⟨hab, hbl⟩ := peelLams_spec _ a hpeel
      obtain ⟨tb, htb, hta, hd', hfr', hinv⟩ := bind bs body gs hab hfresh hgs hbl.symm (fun u hu => hu)
      subst hta
      have hr := lams_steps bs tb gs ρ [] hbl.symm
      simp only [List.append_nil] at hr
      refine Ends.of_reaches hr ?_
      exact IH _ v false body hbody _ tb hd' hfr' htb _ (hinv.addKindLists hkf hbl.symm) [] .nil
        (fun _ => rfl)
    · rename_i hpeel
      simp only [Bool.and_eq_true, List.all_eq_true] at ha
      exact more _ _ (lamSpine_spec a).symm (Nat.le_of_lt (peelLams_lt _ a hpeel)) ha.1 ha.2
  · rename_i hk
    have hu : kind = .unknown := by
      rcases hfi with h | h
      · exact h
      · rw [hk] at h; cases h
    subst hu
    simp only [beq_self_eq_true, if_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      List.isEmpty_iff, List.all_eq_true] at ha
    obtain ⟨⟨hmode, hfresh⟩, hbody⟩ := ha
    by_cases hlt : gs.length < (lamSpine a).1.length
    · obtain ⟨tb, _, hta⟩ := lower_lams _ _ (by rw [lamSpine_spec]; exact hla)
      subst hta
      obtain ⟨r, hr⟩ := lams_halts_fewer _ tb gs ρ hlt
      refine .inr ⟨r, hr, ?_⟩
      rcases hmode with rfl | he
      · trivial
      · rw [he] at hlt; simp at hlt
    · exact more _ _ (lamSpine_spec a).symm (by omega) hfresh hbody

theorem good_case {n : Nat} (IH : ChkSound n) {c : TCtx} {v : VMode} {alt : Bool} {s : Expr}
    {alts : List Expr} (h : chk (n + 1) c v alt (.Case s alts) = true) {env : List VarId} {t : Term}
    (hd : EnvDistinct env) (hfr : freshIn env (.Case s alts) = true)
    (hlow : lowerTotalExpr env (.Case s alts) = some t) : Good c v alt env t := by
  simp only [chk, Bool.and_eq_true] at h
  obtain ⟨hs, hrest⟩ := h
  obtain ⟨ts, talts, hts, htalts, rfl⟩ := lowerTotalExpr_case_some hlow
  simp only [freshIn, Bool.and_eq_true] at hfr
  obtain ⟨hfs, hfalts⟩ := hfr
  have hsG := IH c .term false s hs env ts hd hfs hts
  intro ρ hρ fields hfields hf
  refine Ends.of_reaches (reaches_of_steps 1 rfl) ?_
  rcases hsG.term hρ with he | ⟨w, hw⟩
  · exact .inl (errs_on_stack he _)
  refine Ends.of_reaches (halts_on_stack hw _) ?_
  refine Ends.of_reaches (s' := step (.ret (.caseScrutinee talts ρ :: fields.map Frame.applyArg) w))
    (reaches_of_steps 1 rfl) ?_
  rw [step_caseScrutinee]
  cases hdisp : dispatch talts w with
  | none => exact Ends.error v
  | some r =>
    obtain ⟨ta, gs⟩ := r
    simp only
    have hwwf := halts_wellFormed hρ.wf hρ.len (MIR.lowerTotalExpr_closedAt hts) hw
    obtain ⟨hmem, hgs⟩ := dispatch_spec hdisp hwwf
    cases alt with
    | true =>
      simp only [if_true, List.all_eq_true] at hrest
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hmem
      obtain ⟨a, hai, hla⟩ := lowerList_elem htalts hi
      have hall : ValueListWellFormed (gs ++ fields) := by
        clear hdisp hmem
        induction gs with
        | nil => simpa using hfields
        | cons g gs ih => cases hgs with | cons hg hrest' => exact .cons hg (ih hrest')
      simpa [List.map_append] using IH c v true a (hrest a (List.mem_of_getElem? hai)) env ta hd
        (freshInList_get hfalts hai) hla ρ hρ (gs ++ fields) hall (fun h => by cases h)
    | false =>
      rw [hf rfl]
      simp only [Bool.false_eq_true, if_false] at hrest
      simp only [List.map_nil, List.append_nil]
      refine caseAlts_sound IH hrest hd hfalts hts htalts hρ hw ?_ ?_ hdisp
      · unfold caseKind
        simp only
        split
        · exact scrutineeKind_sound hρ hd hts hw
        split
        · rename_i hb
          rcases (IH c .bool false s hb env ts hd hfs hts).run hρ with he | ⟨r, hr, hm⟩
          · exact absurd hw (fun hw' => halt_not_error hw' he)
          · rw [halts_unique hw hr]; exact hm
        split
        · rename_i _ hcs
          rcases (IH c _ false s hcs env ts hd hfs hts).run hρ with he | ⟨r, hr, hm⟩
          · exact absurd hw (fun hw' => halt_not_error hw' he)
          · rw [halts_unique hw hr]; exact hm
        · exact scrutineeKind_sound hρ hd hts hw
      · intro ks hks
        unfold caseKind at hks
        simp only at hks
        split at hks
        · rename_i h₁
          exfalso
          have : scrutineeKind c.facts c.lists s = .constrs ks := hks
          unfold scrutineeKind at this
          split at this <;> (try cases this)
          split at this <;> (try cases this)
          split at this <;> (try cases this)
          split at this <;> cases this
        split at hks
        · cases hks
        split at hks
        · cases hks; simp [lowerList_len htalts]
        · exfalso
          have : scrutineeKind c.facts c.lists s = .constrs ks := hks
          unfold scrutineeKind at this
          split at this <;> (try cases this)
          split at this <;> (try cases this)
          split at this <;> (try cases this)
          split at this <;> cases this

end Moist.Verified.Guards
