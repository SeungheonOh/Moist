import Moist.Verified.GuardsSoundness.UnitSwap

variable [sv : Moist.CEK.SemVariant]

/-! # The three kinds of strict steps -/

namespace Moist.Verified.Guards

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast

/-! ## Bindings -/

def bindUnit : SemUnit where
  arity := 1
  plug tE b := .Apply (.Lam 0 b) tE
  frames ρ b := [.funV (.VLam b ρ)]
  ok _ := True
  out w := some [w]
  run _ _ _ _ := reaches_of_steps 3 rfl
  stop _ _ _ _ _ h := by cases h
  go _ _ _ _ _ _ h := by cases h; exact reaches_of_steps 1 rfl
  len _ _ _ h := by cases h; rfl
  wf _ _ _ hw h := by cases h; exact .cons hw .nil
  framesWF _ _ _ _ henv hlen hb hπ := .cons (.funV (.vlam henv hlen (by simpa using hb))) hπ

/-! ## Checks -/

def iteState : CekValue := .VBuiltin .IfThenElse [] (.more .argV (.more .argV (.one .argV)))

def iteOut : CekValue → Option (List CekValue)
  | .VCon (.Bool true) => some []
  | _ => none

def iteUnit : SemUnit where
  arity := 0
  plug tE b := .Force (.Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse)) tE) (.Delay b)) (.Delay .Error))
  frames ρ b := [.funV iteState, .arg (.Delay b) ρ, .arg (.Delay .Error) ρ, .force]
  ok _ := True
  out := iteOut
  run _ _ _ _ := reaches_of_steps 8 rfl
  stop π ρ b w _ h := by
    cases w with
    | VCon c =>
      cases c with
      | Bool x =>
        cases x
        · exact reaches_of_steps 9 rfl
        · simp [iteOut] at h
      | _ => exact reaches_of_steps 7 rfl
    | _ => exact reaches_of_steps 7 rfl
  go π ρ b w fs _ h := by
    cases w with
    | VCon c =>
      cases c with
      | Bool x =>
        cases x
        · simp [iteOut] at h
        · simp [iteOut] at h; subst h; exact reaches_of_steps 8 rfl
      | _ => simp [iteOut] at h
    | _ => simp [iteOut] at h
  len w fs _ h := by
    cases w with
    | VCon c =>
      cases c with
      | Bool x => cases x <;> simp [iteOut] at h; subst h; rfl
      | _ => simp [iteOut] at h
    | _ => simp [iteOut] at h
  wf w fs _ _ h := by
    cases w with
    | VCon c =>
      cases c with
      | Bool x => cases x <;> simp [iteOut] at h; subst h; exact .nil
      | _ => simp [iteOut] at h
    | _ => simp [iteOut] at h
  framesWF _ _ _ _ henv hlen hb hπ :=
    .cons (.funV (.vbuiltin _ _ .nil)) (.cons (.arg henv hlen (by simpa [closedAt] using hb))
      (.cons (.arg henv hlen (by simp [closedAt])) (.cons .force hπ)))

/-! ## Cases with one continuing alternative -/

def lamN : Nat → Term → Term
  | 0, t => t
  | n + 1, t => .Lam 0 (lamN n t)

theorem lamN_steps : ∀ (n : Nat) (tb : Term) (fs : List CekValue) (ρ : CekEnv) (π : Stack),
    fs.length = n →
    Reaches (.compute (fs.map Frame.applyArg ++ π) ρ (lamN n tb)) (.compute π (extendAll ρ fs) tb)
  | 0, tb, [], ρ, π, _ => reaches_refl _
  | n + 1, tb, f :: fs, ρ, π, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    exact reaches_trans (reaches_of_steps 2 rfl) (lamN_steps n tb fs (ρ.extend f) π h)
  | 0, _, _ :: _, _, _, h | _ + 1, _, [], _, _, h => by simp at h

omit sv in
theorem closedAt_lamN : ∀ (n d : Nat) (t : Term), closedAt d (lamN n t) = closedAt (d + n) t
  | 0, _, _ => rfl
  | n + 1, d, t => by
    simp only [lamN, closedAt]
    rw [closedAt_lamN n (d + 1) t]
    congr 1; omega

/-- The alternative and fields a dispatch selects, by position. -/
def dispatchIdx (len : Nat) : CekValue → Option (Nat × List CekValue)
  | .VConstr tag fs => if tag < len then some (tag, fs) else none
  | .VCon c =>
    match constToTagAndFields c with
    | some (tag, n, fs) => if n > 0 && len > n then none else if tag < len then some (tag, fs) else none
    | none => none
  | _ => none

omit sv in
theorem dispatch_idx (alts : List Term) (w : CekValue) :
    dispatch alts w = (dispatchIdx alts.length w).bind fun r => alts[r.1]?.map fun a => (a, r.2) := by
  cases w with
  | VConstr tag fs =>
    simp only [dispatch, dispatchIdx]
    split
    · rfl
    · rw [List.getElem?_eq_none (by omega)]; rfl
  | VCon c =>
    simp only [dispatch, dispatchIdx]
    cases constToTagAndFields c with
    | none => rfl
    | some r =>
      obtain ⟨tag, n, fs⟩ := r
      simp only
      split
      · rfl
      · split
        · rfl
        · rw [List.getElem?_eq_none (by omega)]; rfl
  | VLam _ _ => rfl
  | VDelay _ _ => rfl
  | VBuiltin _ _ _ => rfl

/-- An alternative that fails after taking `m` fields. -/
def ErrorAlt (m : Nat) (a : Term) : Prop := a = lamN m .Error

/-- A case on a scrutinee of shape `k` whose alternatives other than the one at
    `before.length` fail after taking the fields of their tag. -/
structure CaseShape where
  kind : Kind
  before : List Term
  after : List Term
  arity : Nat
  hkind : kind = .bool ∨ kind = .int ∨ kind = .list ∨ kind = .pair
  hcont : kind.fields before.length = some arity
  hbefore : ∀ j a, before[j]? = some a → ∃ m, kind.fields j = some m ∧ ErrorAlt m a
  hafter : ∀ j a, after[j]? = some a → ∃ m, ErrorAlt m a ∧
    ∀ m', kind.fields (j + before.length + 1) = some m' → m' = m

def CaseShape.alts (S : CaseShape) (b : Term) : List Term := S.before ++ [lamN S.arity b] ++ S.after

omit sv in
theorem CaseShape.alts_length (S : CaseShape) (b : Term) :
    (S.alts b).length = S.before.length + 1 + S.after.length := by
  simp [CaseShape.alts]; omega

def CaseShape.out (S : CaseShape) (w : CekValue) : Option (List CekValue) :=
  match dispatchIdx (S.before.length + 1 + S.after.length) w with
  | some (i, fs) => if i = S.before.length then some fs else none
  | none => none

omit sv in
theorem CaseShape.get_alt (S : CaseShape) (b : Term) (i : Nat) :
    (S.alts b)[i]? =
      if i < S.before.length then S.before[i]?
      else if i = S.before.length then some (lamN S.arity b)
      else S.after[i - S.before.length - 1]? := by
  unfold CaseShape.alts
  split
  · rw [List.append_assoc, List.getElem?_append_left (by omega)]
  · split
    · subst_vars
      rw [List.getElem?_append_left (by simp), List.getElem?_append_right (by omega)]
      simp
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_append, List.length_cons, List.length_nil]
      congr 1

omit sv in
/-- The fields of the selected tag are those its shape announces. -/
theorem dispatchIdx_kind {k : Kind} (hk : k = .bool ∨ k = .int ∨ k = .list ∨ k = .pair) {w : CekValue}
    (hkv : KindV k w) {len i : Nat} {fs : List CekValue} (h : dispatchIdx len w = some (i, fs)) :
    k.fields i = some fs.length := by
  have vcon : ∀ c, w = .VCon c → ∀ tag n gs, constToTagAndFields c = some (tag, n, gs) →
      k.fields tag = some gs.length → k.fields i = some fs.length := by
    intro c hw tag n gs hc hf
    subst hw
    simp only [dispatchIdx, hc] at h
    split at h
    · cases h
    · split at h
      · cases h; exact hf
      · cases h
  rcases hk with rfl | rfl | rfl | rfl
  · obtain ⟨x, rfl⟩ := hkv
    cases x
    · exact vcon _ rfl 0 2 [] rfl rfl
    · exact vcon _ rfl 1 2 [] rfl rfl
  · obtain ⟨n, rfl⟩ := hkv
    by_cases hn : n ≥ 0
    · exact vcon _ rfl n.toNat 0 [] (by simp [constToTagAndFields, hn]) rfl
    · simp [dispatchIdx, constToTagAndFields, hn] at h
  · cases w with
    | VCon c =>
      cases c <;> simp only [KindV, ListValue] at hkv
      all_goals
        rename_i l
        cases l
        · exact vcon _ rfl 1 2 [] rfl rfl
        · exact vcon _ rfl 0 2 _ rfl rfl
    | _ => simp [KindV, ListValue] at hkv
  · obtain ⟨n, xs, rfl⟩ := hkv
    exact vcon _ rfl 0 1 _ rfl rfl

omit sv in
theorem CaseShape.select (S : CaseShape) {b : Term} {w : CekValue} {alt : Term} {fs : List CekValue}
    (h : dispatch (S.alts b) w = some (alt, fs)) :
    ∃ i, dispatchIdx (S.before.length + 1 + S.after.length) w = some (i, fs) ∧ (S.alts b)[i]? = some alt := by
  rw [dispatch_idx, S.alts_length] at h
  cases hd : dispatchIdx (S.before.length + 1 + S.after.length) w with
  | none => rw [hd] at h; cases h
  | some r =>
    obtain ⟨i, gs⟩ := r
    rw [hd] at h
    simp only [Option.bind_some] at h
    cases ha : (S.alts b)[i]? with
    | none => rw [ha] at h; cases h
    | some a => rw [ha] at h; cases h; exact ⟨i, rfl, ha⟩

theorem lamN_error_fails (m : Nat) (fs : List CekValue) (ρ : CekEnv) (π : Stack) (h : fs.length = m) :
    Reaches (.compute (fs.map Frame.applyArg ++ π) ρ (lamN m .Error)) .error :=
  reaches_trans (lamN_steps m _ fs ρ π h) (reaches_of_steps 1 rfl)

omit sv in
theorem closedAtList_of_forall {d : Nat} : ∀ (ts : List Term), (∀ t ∈ ts, closedAt d t = true) →
    closedAtList d ts = true
  | [], _ => by simp [closedAtList]
  | t :: ts, h => by
    simp only [closedAtList, Bool.and_eq_true]
    exact ⟨h t (.head _), closedAtList_of_forall ts fun t' ht' => h t' (.tail _ ht')⟩

def caseUnit (S : CaseShape) : SemUnit where
  arity := S.arity
  plug tE b := .Case tE (S.alts b)
  frames ρ b := [.caseScrutinee (S.alts b) ρ]
  ok := KindV S.kind
  out := S.out
  run _ _ _ _ := reaches_of_steps 1 rfl
  stop π ρ b w hok hout := by
    refine reaches_trans (s₂ := step (.ret (.caseScrutinee (S.alts b) ρ :: π) w)) (reaches_of_steps 1 rfl) ?_
    rw [step_caseScrutinee]
    cases hdisp : dispatch (S.alts b) w with
    | none => exact reaches_refl _
    | some r =>
      obtain ⟨alt, fs⟩ := r
      simp only
      obtain ⟨i, hd, hai⟩ := S.select hdisp
      have hfi := dispatchIdx_kind S.hkind hok hd
      unfold CaseShape.out at hout
      rw [hd] at hout
      simp only at hout
      split at hout
      · cases hout
      rename_i hne
      rw [S.get_alt b i] at hai
      split at hai
      · obtain ⟨m, hm, rfl⟩ := S.hbefore i alt hai
        rw [hfi] at hm; cases hm
        exact lamN_error_fails _ fs ρ π rfl
      · obtain ⟨m, rfl, hm⟩ := S.hafter _ alt hai
        have := hm fs.length (by rw [show i - S.before.length - 1 + S.before.length + 1 = i by omega]; exact hfi)
        exact lamN_error_fails _ fs ρ π this
  go π ρ b w fs hok hout := by
    refine reaches_trans (s₂ := step (.ret (.caseScrutinee (S.alts b) ρ :: π) w)) (reaches_of_steps 1 rfl) ?_
    rw [step_caseScrutinee]
    unfold CaseShape.out at hout
    cases hd : dispatchIdx (S.before.length + 1 + S.after.length) w with
    | none => rw [hd] at hout; cases hout
    | some r =>
      obtain ⟨i, gs⟩ := r
      rw [hd] at hout
      simp only at hout
      split at hout
      · rename_i hi
        cases hout
        subst hi
        have hfi := dispatchIdx_kind S.hkind hok hd
        rw [S.hcont] at hfi
        have hdisp : dispatch (S.alts b) w = some (lamN S.arity b, fs) := by
          rw [dispatch_idx, S.alts_length, hd]
          simp only [Option.bind_some]
          rw [S.get_alt b]; simp
        rw [hdisp]
        exact lamN_steps _ _ fs ρ π (Option.some.inj hfi).symm
      · cases hout
  len w fs hok hout := by
    unfold CaseShape.out at hout
    cases hd : dispatchIdx (S.before.length + 1 + S.after.length) w with
    | none => rw [hd] at hout; cases hout
    | some r =>
      obtain ⟨i, gs⟩ := r
      rw [hd] at hout
      simp only at hout
      split at hout
      · rename_i hi
        cases hout
        subst hi
        have hfi := dispatchIdx_kind S.hkind hok hd
        rw [S.hcont] at hfi
        exact (Option.some.inj hfi).symm
      · cases hout
  wf w fs hok hw hout := by
    unfold CaseShape.out at hout
    cases hd : dispatchIdx (S.before.length + 1 + S.after.length) w with
    | none => rw [hd] at hout; cases hout
    | some r =>
      obtain ⟨i, gs⟩ := r
      rw [hd] at hout
      simp only at hout
      split at hout
      · rename_i hi
        cases hout
        have hd' : dispatch (S.alts .Error) w = some (lamN S.arity .Error, fs) := by
          rw [dispatch_idx, S.alts_length, hd]
          simp only [Option.bind_some]
          rw [S.get_alt, hi]; simp
        exact (dispatch_spec hd' hw).2
      · cases hout
  framesWF d ρ b π henv hlen hb hπ := by
    refine .cons (.caseScrutinee henv hlen ?_) hπ
    have hmem : ∀ t ∈ S.alts b, closedAt d t = true := by
      intro t ht
      simp only [CaseShape.alts, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at ht
      rcases ht with (ht | rfl) | ht
      · obtain ⟨j, hj⟩ := List.getElem?_of_mem ht
        obtain ⟨m, _, rfl⟩ := S.hbefore j t hj
        rw [closedAt_lamN]; simp [closedAt]
      · rw [closedAt_lamN]; exact hb
      · obtain ⟨j, hj⟩ := List.getElem?_of_mem ht
        obtain ⟨m, rfl, _⟩ := S.hafter j t hj
        rw [closedAt_lamN]; simp [closedAt]
    exact closedAtList_of_forall _ hmem

end Moist.Verified.Guards
