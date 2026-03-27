import Moist.CEK.Machine
import Moist.MIR.Semantics

namespace Moist.CEK

open Moist.Plutus.Term
open Moist.MIR.Semantics

/-! # closedAt, ValueRelV, EnvRelV — shared definitions for bisimulation proofs -/

/-! ## closedAt: de Bruijn depth-bounded closed term predicate -/

mutual
  def closedAt (d : Nat) (t : Term) : Bool := match t with
    | .Var n => decide (n ≤ d)
    | .Lam _ body => closedAt (d + 1) body
    | .Apply f x => closedAt d f && closedAt d x
    | .Force e | .Delay e => closedAt d e
    | .Constr _ args => closedAtList d args
    | .Case scrut alts => closedAt d scrut && closedAtList d alts
    | .Constant _ | .Builtin _ | .Error => true
  termination_by sizeOf t
  def closedAtList (d : Nat) (ts : List Term) : Bool := match ts with
    | [] => true
    | t :: rest => closedAt d t && closedAtList d rest
  termination_by sizeOf ts
end

/-! ## closedAt equation helpers -/

theorem closedAt_var {d n} (h : closedAt d (.Var n) = true) : n ≤ d := by
  rw [closedAt.eq_1] at h; exact of_decide_eq_true h

theorem closedAt_apply {d f x} (h : closedAt d (.Apply f x) = true) :
    closedAt d f = true ∧ closedAt d x = true := by
  rw [closedAt.eq_3] at h; exact Bool.and_eq_true_iff.mp h

theorem closedAt_force {d e} (h : closedAt d (.Force e) = true) :
    closedAt d e = true := by rw [closedAt.eq_4] at h; exact h

theorem closedAt_delay {d e} (h : closedAt d (.Delay e) = true) :
    closedAt d e = true := by rw [closedAt.eq_5] at h; exact h

theorem closedAt_lam {d n body} (h : closedAt d (.Lam n body) = true) :
    closedAt (d + 1) body = true := by rw [closedAt.eq_2] at h; exact h

theorem closedAt_constr {d tag args} (h : closedAt d (.Constr tag args) = true) :
    closedAtList d args = true := by rw [closedAt.eq_6] at h; exact h

theorem closedAt_constr_cons {d m ms} (h : closedAtList d (m :: ms) = true) :
    closedAt d m = true ∧ closedAtList d ms = true := by
  rw [closedAtList.eq_2] at h; exact Bool.and_eq_true_iff.mp h

theorem closedAt_case {d scrut alts} (h : closedAt d (.Case scrut alts) = true) :
    closedAt d scrut = true ∧ closedAtList d alts = true := by
  rw [closedAt.eq_7] at h; exact Bool.and_eq_true_iff.mp h

/-! ## closedAt monotonicity -/

mutual
  theorem closedAt_mono {d d' : Nat} {t : Term} (h : closedAt d t = true) (hle : d ≤ d') :
      closedAt d' t = true := by
    cases t with
    | Var n =>
      rw [closedAt.eq_1] at h ⊢; exact decide_eq_true (Nat.le_trans (of_decide_eq_true h) hle)
    | Lam _ body =>
      rw [closedAt.eq_2] at h ⊢; exact closedAt_mono h (by omega)
    | Apply f x =>
      rw [closedAt.eq_3] at h ⊢; have ⟨hf, hx⟩ := Bool.and_eq_true_iff.mp h
      exact Bool.and_eq_true_iff.mpr ⟨closedAt_mono hf hle, closedAt_mono hx hle⟩
    | Force e =>
      rw [closedAt.eq_4] at h ⊢; exact closedAt_mono h hle
    | Delay e =>
      rw [closedAt.eq_5] at h ⊢; exact closedAt_mono h hle
    | Constr _ args =>
      rw [closedAt.eq_6] at h ⊢; exact closedAtList_mono h hle
    | Case scrut alts =>
      rw [closedAt.eq_7] at h ⊢; have ⟨hs, ha⟩ := Bool.and_eq_true_iff.mp h
      exact Bool.and_eq_true_iff.mpr ⟨closedAt_mono hs hle, closedAtList_mono ha hle⟩
    | Constant _ => simp [closedAt]
    | Builtin _ => simp [closedAt]
    | Error => simp [closedAt]
  termination_by sizeOf t
  theorem closedAtList_mono {d d' : Nat} {ts : List Term}
      (h : closedAtList d ts = true) (hle : d ≤ d') :
      closedAtList d' ts = true := by
    cases ts with
    | nil => simp [closedAtList]
    | cons t rest =>
      rw [closedAtList.eq_2] at h ⊢; have ⟨ht, hr⟩ := Bool.and_eq_true_iff.mp h
      exact Bool.and_eq_true_iff.mpr ⟨closedAt_mono ht hle, closedAtList_mono hr hle⟩
  termination_by sizeOf ts
end

/-! ## closedAt existence: every term is closed at some depth -/

mutual
  theorem closedAt_exists (t : Term) : ∃ d, closedAt d t = true := by
    cases t with
    | Var n => exact ⟨n, by rw [closedAt.eq_1]; exact decide_eq_true (Nat.le_refl n)⟩
    | Lam _ body =>
      have ⟨d, hd⟩ := closedAt_exists body
      exact ⟨d, by rw [closedAt.eq_2]; exact closedAt_mono hd (by omega)⟩
    | Apply f x =>
      have ⟨df, hf⟩ := closedAt_exists f; have ⟨dx, hx⟩ := closedAt_exists x
      refine ⟨max df dx, ?_⟩
      rw [closedAt.eq_3]
      exact Bool.and_eq_true_iff.mpr
        ⟨closedAt_mono hf (Nat.le_max_left df dx), closedAt_mono hx (Nat.le_max_right df dx)⟩
    | Force e =>
      have ⟨d, hd⟩ := closedAt_exists e; exact ⟨d, by rw [closedAt.eq_4]; exact hd⟩
    | Delay e =>
      have ⟨d, hd⟩ := closedAt_exists e; exact ⟨d, by rw [closedAt.eq_5]; exact hd⟩
    | Constr _ args =>
      have ⟨d, hd⟩ := closedAtList_exists args
      exact ⟨d, by rw [closedAt.eq_6]; exact hd⟩
    | Case scrut alts =>
      have ⟨ds, hs⟩ := closedAt_exists scrut
      have ⟨da, ha⟩ := closedAtList_exists alts
      refine ⟨max ds da, ?_⟩
      rw [closedAt.eq_7]
      exact Bool.and_eq_true_iff.mpr
        ⟨closedAt_mono hs (Nat.le_max_left ds da), closedAtList_mono ha (Nat.le_max_right ds da)⟩
    | Constant _ => exact ⟨0, by simp [closedAt]⟩
    | Builtin _ => exact ⟨0, by simp [closedAt]⟩
    | Error => exact ⟨0, by simp [closedAt]⟩
  termination_by sizeOf t
  theorem closedAtList_exists (ts : List Term) : ∃ d, closedAtList d ts = true := by
    cases ts with
    | nil => exact ⟨0, by simp [closedAtList]⟩
    | cons t rest =>
      have ⟨dt, ht⟩ := closedAt_exists t
      have ⟨dr, hr⟩ := closedAtList_exists rest
      refine ⟨max dt dr, ?_⟩
      rw [closedAtList.eq_2]
      exact Bool.and_eq_true_iff.mpr
        ⟨closedAt_mono ht (Nat.le_max_left dt dr), closedAtList_mono hr (Nat.le_max_right dt dr)⟩
  termination_by sizeOf ts
end

/-! ## closedAtList element access -/

theorem closedAtList_getElem {d : Nat} {ts : List Term} {i : Nat}
    (h : closedAtList d ts = true) (hi : i < ts.length) :
    closedAt d (ts[i]) = true := by
  induction ts generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons t rest ih =>
    have ⟨ht, hr⟩ := closedAt_constr_cons h
    cases i with
    | zero => simp; exact ht
    | succ j =>
      simp
      exact ih hr (by simp at hi; omega)

/-! ## ValueRelV, ListValueRelV, EnvRelV: mutual structural relations

`EnvRelV d env1 env2` says that for positions 1..d, either both lookups
fail or both succeed with `ValueRelV`-related values. This is weaker than
literal equality (`EnvEq`) and is preserved when extending envs with
`ValueRelV`-related argument values during lambda application. -/

mutual
  inductive ValueRelV : CekValue → CekValue → Prop where
    | vcon : ValueRelV (.VCon c) (.VCon c)
    | vlam (d : Nat) (hclosed : closedAt (d + 1) body = true)
        (henv : EnvRelV d env1 env2) :
        ValueRelV (.VLam body env1) (.VLam body env2)
    | vdelay (d : Nat) (hclosed : closedAt d body = true)
        (henv : EnvRelV d env1 env2) :
        ValueRelV (.VDelay body env1) (.VDelay body env2)
    | vconstr (htag : tag1 = tag2) (hfs : ListValueRelV fs1 fs2) :
        ValueRelV (.VConstr tag1 fs1) (.VConstr tag2 fs2)
    | vbuiltin (hb : b1 = b2) (hargs : ListValueRelV args1 args2) (hea : ea1 = ea2) :
        ValueRelV (.VBuiltin b1 args1 ea1) (.VBuiltin b2 args2 ea2)
    | refl : ValueRelV v v
  inductive ListValueRelV : List CekValue → List CekValue → Prop where
    | nil : ListValueRelV [] []
    | cons (hv : ValueRelV v1 v2) (hrs : ListValueRelV rest1 rest2) :
        ListValueRelV (v1 :: rest1) (v2 :: rest2)
  /-- Per-position lookup relation: both none, or both some with ValueRelV. -/
  inductive LookupRelV : Option CekValue → Option CekValue → Prop where
    | bothNone : LookupRelV none none
    | bothSome (hv : ValueRelV v1 v2) : LookupRelV (some v1) (some v2)
  /-- Environment relation: positions 1..d have matching lookups. -/
  inductive EnvRelV : Nat → CekEnv → CekEnv → Prop where
    | mk : (∀ n, 0 < n → n ≤ d →
              LookupRelV (env1.lookup n) (env2.lookup n)) →
            EnvRelV d env1 env2
end

/-! ## EnvRelV lemmas -/

theorem envRelV_elim {d : Nat} {env1 env2 : CekEnv} (h : EnvRelV d env1 env2)
    {n : Nat} (hn : 0 < n) (hle : n ≤ d) :
    LookupRelV (env1.lookup n) (env2.lookup n) :=
  match h with | .mk f => f n hn hle

theorem envRelV_refl (d : Nat) (env : CekEnv) : EnvRelV d env env := by
  exact .mk fun n _ _ =>
    match h : env.lookup n with
    | none => h ▸ .bothNone
    | some v => h ▸ .bothSome .refl

theorem envRelV_extend (d : Nat) (env1 env2 : CekEnv) (v1 v2 : CekValue)
    (henv : EnvRelV d env1 env2) (hv : ValueRelV v1 v2) :
    EnvRelV (d + 1) (env1.extend v1) (env2.extend v2) := by
  constructor; intro n hn hle
  cases n with
  | zero => omega
  | succ m =>
    cases m with
    | zero =>
      show LookupRelV (some v1) (some v2)
      exact .bothSome hv
    | succ m' =>
      show LookupRelV (env1.lookup (m' + 1)) (env2.lookup (m' + 1))
      exact envRelV_elim henv (by omega) (by omega)

/-! ## Frame, Stack, State relations

`FrameRel` and `StackRel` are depth-independent: each frame that carries
an environment bundles its own depth witness. This lets closures at
different depths coexist on a single stack. -/

inductive FrameRel : Frame → Frame → Prop where
  | force : FrameRel .force .force
  | arg (d : Nat) (t : Term) (henv : EnvRelV d env1 env2) (hclosed : closedAt d t = true) :
      FrameRel (.arg t env1) (.arg t env2)
  | funV (hv : ValueRelV v1 v2) : FrameRel (.funV v1) (.funV v2)
  | applyArg (hv : ValueRelV v1 v2) : FrameRel (.applyArg v1) (.applyArg v2)
  | constrField (d : Nat) (tag : Nat) (hdone : ListValueRelV done1 done2)
      (todo : List Term) (htodo : closedAtList d todo = true)
      (henv : EnvRelV d env1 env2) :
      FrameRel (.constrField tag done1 todo env1) (.constrField tag done2 todo env2)
  | caseScrutinee (d : Nat) (alts : List Term) (halts : closedAtList d alts = true)
      (henv : EnvRelV d env1 env2) :
      FrameRel (.caseScrutinee alts env1) (.caseScrutinee alts env2)

inductive StackRel : Stack → Stack → Prop where
  | nil : StackRel [] []
  | cons (hf : FrameRel f1 f2) (hrs : StackRel s1 s2) :
      StackRel (f1 :: s1) (f2 :: s2)

inductive StateRel : State → State → Prop where
  | compute (hs : StackRel s1 s2) (d : Nat) (henv : EnvRelV d env1 env2)
      (ht : closedAt d t = true) :
      StateRel (.compute s1 env1 t) (.compute s2 env2 t)
  | ret (hs : StackRel s1 s2) (hv : ValueRelV v1 v2) :
      StateRel (.ret s1 v1) (.ret s2 v2)
  | error : StateRel .error .error
  | halt (hv : ValueRelV v1 v2) :
      StateRel (.halt v1) (.halt v2)

end Moist.CEK
