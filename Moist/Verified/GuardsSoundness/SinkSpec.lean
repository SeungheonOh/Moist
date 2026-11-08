import Moist.Verified.GuardsSoundness.FreshExtend

variable [sv : Moist.CEK.SemVariant]

/-! # The strict steps `unitView` finds, and their semantics -/

namespace Moist.Verified.Guards

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast

omit sv in
theorem lamChain_eq_lamN : ∀ (bs : List VarId) (tb : Term), lamChain bs tb = lamN bs.length tb
  | [], _ => rfl
  | _ :: bs, tb => by
    show Term.Lam 0 (lamChain bs tb) = Term.Lam 0 (lamN bs.length tb)
    rw [lamChain_eq_lamN bs tb]

omit sv in
theorem lower_lams_of {bs : List VarId} {e : Expr} {env : List VarId} {tb : Term}
    (h : lowerTotalExpr (bs.reverse ++ env) e = some tb) :
    lowerTotalExpr env (Advanced.lams bs e) = some (lamN bs.length tb) := by
  induction bs generalizing env with
  | nil => simpa [Advanced.lams] using h
  | cons b bs ih =>
    rw [lams_cons, MIR.lowerTotalExpr_lam, ih (by simpa using h)]
    rfl

theorem lower_lams_iff (bs : List VarId) (e : Expr) (env : List VarId) :
    lowerTotalExpr env (Advanced.lams bs e) = (lowerTotalExpr (bs.reverse ++ env) e).map (lamN bs.length) := by
  cases h : lowerTotalExpr (bs.reverse ++ env) e with
  | some tb => exact lower_lams_of h
  | none =>
    cases h' : lowerTotalExpr env (Advanced.lams bs e) with
    | none => rfl
    | some t =>
      obtain ⟨tb, htb, _⟩ := lower_lams bs e h'
      rw [h] at htb; cases htb

omit sv in
theorem isErrorExpr_eq' {a : Expr} (h : isErrorExpr a = true) : a = .Error := by
  cases a <;> simp_all [isErrorExpr]

/-- An exact error alternative lowers to the same failing chain everywhere. -/
theorem exactError_lower {kind : Kind} {i : Nat} {a : Expr} (h : exactError kind i a = true) :
    ∃ m, (∀ env, lowerTotalExpr env a = some (lamN m .Error)) ∧
      ∀ m', kind.fields i = some m' → m' = m := by
  unfold exactError at h
  split at h
  · rename_i n hn
    split at h
    · rename_i bs b hp
      have hb := isErrorExpr_eq' h
      subst hb
      obtain ⟨rfl, hl⟩ := peelLams_spec n a hp
      refine ⟨bs.length, fun env => ?_, fun m' hm => ?_⟩
      · exact lower_lams_of (by rw [lowerTotalExpr_error])
      · rw [hn] at hm; cases hm; exact hl.symm
    · cases h
  · rename_i hn
    unfold isErrorAlt at h
    have hb := isErrorExpr_eq' h
    obtain ⟨bs, hbs⟩ : ∃ bs, a = Advanced.lams bs .Error := ⟨(lamSpine a).1, by rw [← hb, lamSpine_spec]⟩
    subst hbs
    exact ⟨bs.length, fun env => lower_lams_of (by rw [lowerTotalExpr_error]),
      fun m' hm => by rw [hn] at hm; cases hm⟩

omit sv in
theorem continuing_spec {kind : Kind} {before : List Expr} {alt : Expr} {bs : List VarId} {body : Expr}
    (h : continuing kind before alt = some (bs, body)) :
    alt = Advanced.lams bs body ∧ kind.fields before.length = some bs.length ∧
      (kind = .bool ∨ kind = .int ∨ kind = .list ∨ kind = .pair) := by
  unfold continuing at h
  split at h
  · cases h; exact ⟨rfl, rfl, by simp⟩
  · cases h; exact ⟨rfl, rfl, by simp⟩
  · rename_i hl; cases h; exact ⟨rfl, by simp [Kind.fields, hl], by simp⟩
  · rename_i hl; cases h; exact ⟨rfl, by simp [Kind.fields, hl], by simp⟩
  · rename_i hl; cases h; exact ⟨rfl, by simp [Kind.fields, hl], by simp⟩
  · cases h

omit sv in
theorem lowerList_append {env : List VarId} :
    ∀ (xs ys : List Expr), MIR.lowerTotalExprList env (xs ++ ys) =
      (MIR.lowerTotalExprList env xs).bind fun txs => (MIR.lowerTotalExprList env ys).map (txs ++ ·)
  | [], ys => by
    rw [List.nil_append, MIR.lowerTotalExprList_nil]
    cases MIR.lowerTotalExprList env ys <;> rfl
  | x :: xs, ys => by
    rw [List.cons_append, MIR.lowerTotalExprList_cons, MIR.lowerTotalExprList_cons,
      lowerList_append xs ys]
    cases lowerTotalExpr env x <;> cases MIR.lowerTotalExprList env xs <;>
      cases MIR.lowerTotalExprList env ys <;> rfl

/-- A list of exact error alternatives lowers to the same list everywhere. -/
theorem errorAlts_lower {kind : Kind} (off : Nat) :
    ∀ (as : List Expr), (as.zipIdx.all fun (a, i) => exactError kind (i + off) a) = true →
      ∃ ts : List Term, (∀ env, MIR.lowerTotalExprList env as = some ts) ∧ ts.length = as.length ∧
        ∀ j t, ts[j]? = some t → ∃ m, t = lamN m .Error ∧ ∀ m', kind.fields (j + off) = some m' → m' = m
  | [], _ => ⟨[], fun _ => MIR.lowerTotalExprList_nil _, rfl, fun _ _ h => by simp at h⟩
  | a :: as, h => by
    simp only [List.zipIdx_cons, List.all_cons, Bool.and_eq_true, Nat.zero_add] at h
    obtain ⟨ha, hrest⟩ := h
    obtain ⟨m, hm, hmf⟩ := exactError_lower ha
    have hrest' : (as.zipIdx.all fun (a, i) => exactError kind (i + (off + 1)) a) = true := by
      rw [← hrest, List.zipIdx_succ]; simp [List.all_map, Function.comp_def, Nat.add_assoc, Nat.add_comm 1]
    obtain ⟨ts, hts, hl, hspec⟩ := errorAlts_lower (off + 1) as hrest'
    refine ⟨lamN m .Error :: ts, fun env => ?_, by simp [hl], fun j t hj => ?_⟩
    · rw [MIR.lowerTotalExprList_cons, hm, hts]; rfl
    · cases j with
      | zero => simp at hj; subst hj; exact ⟨m, rfl, by simpa using hmf⟩
      | succ j =>
        obtain ⟨m', h1, h2⟩ := hspec j t (by simpa using hj)
        exact ⟨m', h1, fun m'' hm'' => h2 m'' (by rw [show j + (off + 1) = j + 1 + off by omega]; exact hm'')⟩

end Moist.Verified.Guards
