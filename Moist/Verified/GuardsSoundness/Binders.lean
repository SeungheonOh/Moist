import Moist.Verified.GuardsSoundness.Steps

variable [sv : Moist.CEK.SemVariant]

/-! # Alternatives that bind fields -/

namespace Moist.Verified.Guards

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast
open Moist.Verified.KnownLists

def extendAll (ρ : CekEnv) : List CekValue → CekEnv
  | [] => ρ
  | f :: fs => extendAll (ρ.extend f) fs

omit sv in
theorem lams_cons (x : VarId) (xs : List VarId) (b : Expr) :
    Advanced.lams (x :: xs) b = .Lam x (Advanced.lams xs b) := rfl

omit sv in
theorem lamSpine_spec : ∀ (e : Expr), Advanced.lams (lamSpine e).1 (lamSpine e).2 = e
  | .Lam x b => by
    have := lamSpine_spec b
    simp only [lamSpine, lams_cons]; rw [this]
  | .Var _ | .Lit _ | .Builtin _ | .Error | .Fix _ _ | .App _ _ | .Force _ | .Delay _
  | .Constr _ _ | .Case _ _ | .Let _ _ => rfl

omit sv in
theorem lamSpine_body_not_lam : ∀ (e : Expr) (x : VarId) (b : Expr), (lamSpine e).2 ≠ .Lam x b
  | .Lam y c, x, b => by simp only [lamSpine]; exact lamSpine_body_not_lam c x b
  | .Var _, _, _ | .Lit _, _, _ | .Builtin _, _, _ | .Error, _, _ | .Fix _ _, _, _ | .App _ _, _, _
  | .Force _, _, _ | .Delay _, _, _ | .Constr _ _, _, _ | .Case _ _, _, _ | .Let _ _, _, _ => by
    simp [lamSpine]

omit sv in
theorem peelLams_spec : ∀ (k : Nat) (e : Expr) {bs : List VarId} {body : Expr},
    peelLams k e = some (bs, body) → e = Advanced.lams bs body ∧ bs.length = k
  | 0, e, bs, body, h => by
    simp only [peelLams, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | k + 1, .Lam x b, bs, body, h => by
    simp only [peelLams] at h
    cases hp : peelLams k b with
    | none => rw [hp] at h; cases h
    | some r =>
      obtain ⟨xs, bd⟩ := r
      rw [hp] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, hl⟩ := peelLams_spec k b hp
      exact ⟨rfl, by simp [hl]⟩
  | _ + 1, .Var _, _, _, h | _ + 1, .Lit _, _, _, h | _ + 1, .Builtin _, _, _, h
  | _ + 1, .Error, _, _, h | _ + 1, .Fix _ _, _, _, h | _ + 1, .App _ _, _, _, h
  | _ + 1, .Force _, _, _, h | _ + 1, .Delay _, _, _, h | _ + 1, .Constr _ _, _, _, h
  | _ + 1, .Case _ _, _, _, h | _ + 1, .Let _ _, _, _, h => by simp [peelLams] at h

omit sv in
theorem peelLams_lt : ∀ (k : Nat) (e : Expr), peelLams k e = none → (lamSpine e).1.length < k
  | 0, e, h => by simp [peelLams] at h
  | k + 1, .Lam x b, h => by
    simp only [peelLams] at h
    cases hp : peelLams k b with
    | none => have := peelLams_lt k b hp; simp only [lamSpine, List.length_cons]; omega
    | some r => rw [hp] at h; cases h
  | _ + 1, .Var _, _ | _ + 1, .Lit _, _ | _ + 1, .Builtin _, _
  | _ + 1, .Error, _ | _ + 1, .Fix _ _, _ | _ + 1, .App _ _, _
  | _ + 1, .Force _, _ | _ + 1, .Delay _, _ | _ + 1, .Constr _ _, _
  | _ + 1, .Case _ _, _ | _ + 1, .Let _ _, _ => by simp [lamSpine]

omit sv in
/-- Lowering a lambda prefix. -/
theorem lower_lams : ∀ (bs : List VarId) (body : Expr) {env : List VarId} {t : Term},
    lowerTotalExpr env (Advanced.lams bs body) = some t →
    ∃ tb, lowerTotalExpr (bs.reverse ++ env) body = some tb ∧ t = (bs.map fun _ => ()).foldr (fun _ acc => .Lam 0 acc) tb
  | [], body, env, t, h => ⟨t, by simpa [Advanced.lams] using h, rfl⟩
  | x :: xs, body, env, t, h => by
    rw [lams_cons] at h
    obtain ⟨t', ht', rfl⟩ := lowerTotalExpr_lam_some h
    obtain ⟨tb, htb, rfl⟩ := lower_lams xs body ht'
    exact ⟨tb, by simpa using htb, rfl⟩

/-- Exactly as many fields as lambdas: the body runs in the extended environment. -/
theorem lams_steps : ∀ (bs : List VarId) (tb : Term) (fs : List CekValue) (ρ : CekEnv) (π : Stack),
    fs.length = bs.length →
    Reaches (.compute (fs.map Frame.applyArg ++ π) ρ
        ((bs.map fun _ => ()).foldr (fun _ acc => .Lam 0 acc) tb))
      (.compute π (extendAll ρ fs) tb)
  | [], tb, [], ρ, π, _ => reaches_refl _
  | _ :: bs, tb, f :: fs, ρ, π, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    refine reaches_trans (reaches_of_steps 2 rfl) ?_
    exact lams_steps bs tb fs (ρ.extend f) π h
  | [], _, _ :: _, _, _, h | _ :: _, _, [], _, _, h => by simp at h

/-- More fields than lambdas: the body runs with the remaining fields. -/
theorem lams_steps_more : ∀ (bs : List VarId) (tb : Term) (fs : List CekValue) (ρ : CekEnv) (π : Stack),
    bs.length ≤ fs.length →
    Reaches (.compute (fs.map Frame.applyArg ++ π) ρ
        ((bs.map fun _ => ()).foldr (fun _ acc => .Lam 0 acc) tb))
      (.compute ((fs.drop bs.length).map Frame.applyArg ++ π) (extendAll ρ (fs.take bs.length)) tb)
  | [], tb, fs, ρ, π, _ => by simpa [extendAll] using reaches_refl _
  | _ :: bs, tb, f :: fs, ρ, π, h => by
    simp only [List.length_cons, Nat.add_le_add_iff_right] at h
    refine reaches_trans (reaches_of_steps 2 rfl) ?_
    simpa [extendAll] using lams_steps_more bs tb fs (ρ.extend f) π h
  | _ :: _, _, [], _, _, h => by simp at h

/-- Fewer fields than lambdas: the alternative returns a closure. -/
theorem lams_halts_fewer : ∀ (bs : List VarId) (tb : Term) (fs : List CekValue) (ρ : CekEnv),
    fs.length < bs.length →
    ∃ r, Reaches (.compute (fs.map Frame.applyArg) ρ
        ((bs.map fun _ => ()).foldr (fun _ acc => .Lam 0 acc) tb)) (.halt r)
  | _ :: bs, tb, [], ρ, _ => ⟨_, reaches_of_steps 2 rfl⟩
  | _ :: bs, tb, f :: fs, ρ, h => by
    simp only [List.length_cons, Nat.add_lt_add_iff_right] at h
    obtain ⟨r, hr⟩ := lams_halts_fewer bs tb fs (ρ.extend f) h
    exact ⟨r, reaches_trans (reaches_of_steps 2 rfl) hr⟩
  | [], _, _, _, h => by simp at h

/-- Binding fresh names to fields keeps the invariant; each name holds one
    of the fields. -/
theorem bind_fields : ∀ (bs : List VarId) (body : Expr) (fs : List CekValue) {c : TCtx}
    {env : List VarId} {ρ : CekEnv},
    Inv c env ρ → EnvDistinct env → freshIn env (Advanced.lams bs body) = true → (∀ b ∈ bs, c.fresh b = true) →
    ValueListWellFormed fs → fs.length = bs.length →
    Inv c (bs.reverse ++ env) (extendAll ρ fs) ∧ EnvDistinct (bs.reverse ++ env) ∧
      freshIn (bs.reverse ++ env) body = true ∧
      (∀ b ∈ bs, BoundValue (bs.reverse ++ env) (extendAll ρ fs) b (fun u => u ∈ fs)) ∧
      (∀ y, (envLookupT env y).isSome = true → ∀ Q, BoundValue env ρ y Q →
        BoundValue (bs.reverse ++ env) (extendAll ρ fs) y Q)
  | [], body, [], c, env, ρ, hρ, hd, hfr, _, _, _ =>
    ⟨hρ, hd, by simpa [Advanced.lams] using hfr, fun _ h => by simp at h, fun _ _ _ h => h⟩
  | x :: xs, body, f :: fs, c, env, ρ, hρ, hd, hfr, hfresh, hfs, hlen => by
    rw [lams_cons] at hfr
    simp only [freshIn, Bool.and_eq_true] at hfr
    obtain ⟨hx, hfr'⟩ := hfr
    cases hfs with
    | cons hf hfs' =>
    have hlen' : fs.length = xs.length := by simpa using hlen
    have hρ' := hρ.extend (hfresh x (.head _)) hf
    obtain ⟨h1, h2, h3, h4, h5⟩ := bind_fields xs body fs hρ' (hd.cons hx) hfr'
      (fun b hb => hfresh b (.tail _ hb)) hfs' hlen'
    refine ⟨by simpa using h1, by simpa using h2, by simpa using h3, ?_, ?_⟩
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · have := h5 b (by simp [envLookupT_cons_self]) (fun u => u = f)
          (BoundValue.self (varId_beq_self b) rfl)
        simpa [extendAll] using this.mono (fun u hu => by subst hu; exact .inl rfl)
      · simpa [extendAll] using (h4 b hb).mono (fun u hu => List.mem_cons_of_mem f hu)
    · intro y hy Q hQ
      have hxy : (x == y) = false := by
        cases hxy : (x == y)
        · rfl
        · exfalso
          rw [← envLookupT_congr hxy env] at hy
          simp only [Option.isNone_iff_eq_none] at hx
          rw [hx] at hy; cases hy
      have := h5 y (by rw [envLookupT_cons_neq x y env hxy]; simpa using hy) Q (hQ.extend hxy f)
      simpa [extendAll] using this
  | [], _, _ :: _, _, _, _, _, _, _, _, _, h | _ :: _, _, [], _, _, _, _, _, _, _, _, h => by simp at h

/-! ## Gained facts -/

theorem Inv.addList {c : TCtx} {env : List VarId} {ρ : CekEnv} {x : VarId} (h : Inv c env ρ)
    (hx : BoundValue env ρ x ListValue) : Inv (c.addLists [x]) env ρ where
  wf := h.wf
  len := h.len
  facts := h.facts
  lists := by
    show ListsHold anyList ([x] ++ c.lists) env ρ
    exact ListsHold.add h.lists hx
  roles := h.roles

theorem Role.descend_holds {env : List VarId} {ρ : CekEnv} {r : Role} {z : VarId} {bs : List VarId}
    {w : CekValue} (h : RoleHolds env ρ r) (hz : BoundValue env ρ z (· = w))
    (hzb : (envLookupT env z).isSome = true)
    (hbs : ∀ b ∈ bs, BoundValue env ρ b (fun u => vsize u < vsize w)) :
    RoleHolds env ρ (r.descend z bs) := by
  unfold Role.descend
  split
  · rename_i hcond
    obtain ⟨m, hf, hbase, hsmall⟩ := h
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hzb
    obtain ⟨w', hw', rfl⟩ := hz i hi
    have hwm : vsize w' < m + 1 := by
      simp only [Bool.or_eq_true] at hcond
      rcases hcond with hc | hc
      · obtain ⟨u, hu, hle⟩ := hbase i (by rw [← envLookupT_congr hc]; exact hi)
        rw [hw'] at hu; cases hu; omega
      · obtain ⟨u, hu, hlt⟩ := hsmall z hc i hi
        rw [hw'] at hu; cases hu; omega
    refine ⟨m, hf, hbase, fun y hy => ?_⟩
    simp only [List.contains_append, Bool.or_eq_true] at hy
    rcases hy with hy | hy
    · obtain ⟨b, hb, hby⟩ := List.contains_iff_exists_mem_beq.mp hy
      intro j hj
      rw [envLookupT_congr hby] at hj
      obtain ⟨u, hu, hlt⟩ := hbs b hb j hj
      refine ⟨u, hu, ?_⟩
      simp only [Bool.or_eq_true] at hcond
      rcases hcond with hc | hc
      · obtain ⟨u', hu', hle⟩ := hbase i (by rw [← envLookupT_congr hc]; exact hi)
        rw [hw'] at hu'; cases hu'; omega
      · obtain ⟨u', hu', hlt'⟩ := hsmall z hc i hi
        rw [hw'] at hu'; cases hu'; omega
    · exact hsmall y hy
  · exact h

theorem Inv.descend {c : TCtx} {env : List VarId} {ρ : CekEnv} {s : Expr} {bs : List VarId}
    (h : Inv c env ρ)
    (hs : ∀ z, s = .Var z → ∃ w, BoundValue env ρ z (· = w) ∧ (envLookupT env z).isSome = true ∧
      ∀ b ∈ bs, BoundValue env ρ b (fun u => vsize u < vsize w)) :
    Inv (c.descend s bs) env ρ := by
  cases s with
  | Var z =>
    obtain ⟨w, hz, hzb, hbs⟩ := hs z rfl
    exact { wf := h.wf, len := h.len, facts := h.facts, lists := h.lists,
            roles := fun r hr => by
              simp only [TCtx.descend, List.mem_map] at hr
              obtain ⟨r', hr', rfl⟩ := hr
              exact Role.descend_holds (h.roles r' hr') hz hzb hbs }
  | _ => exact h

end Moist.Verified.Guards
