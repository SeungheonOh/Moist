import Moist.Verified.ShapesSoundness.Rewrites
import Moist.Verified.TagChainsSoundness.Tests

/-! # Comparisons with a key of known bytes

`dataComparison` replaces `equalsData d x`, where the facts make `d` the `B`
value of the bytes `k` (`k = unBData d`) and `o` the `B` value of `p ++ k` for
a nonempty `p`, by

```
equalsByteString k (unBData (chooseData x o o o o x))
```

When `x` is a `B` value, `chooseData` returns it and both sides compare its
bytes with `k`. Otherwise both sides return `False`: the bytes of `o` differ
from `k`. When `x` is not a `Data` value both sides fail.
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.TagChains (Binary Atomic resolve_partial resolve_saturated halts_var_drop
  envWellFormed_drop)

/-! ## Evaluation pieces -/

theorem errs_apply_intro {ρ : CekEnv} {tf ta : Term} {wf wa : CekValue} (hf : Halts ρ tf wf)
    (ha : Halts ρ ta wa) (h : Reaches (.ret [.funV wf] wa) .error) : Errs ρ (.Apply tf ta) :=
  reaches_trans (reaches_of_steps 1 rfl) (reaches_trans (halts_on_stack hf _)
    (reaches_trans (reaches_of_steps 1 rfl) (reaches_trans (halts_on_stack ha _) h)))

theorem errs_apply_arg {ρ : CekEnv} {tf ta : Term} {wf : CekValue} (hf : Halts ρ tf wf)
    (ha : Errs ρ ta) : Errs ρ (.Apply tf ta) :=
  reaches_trans (reaches_of_steps 1 rfl) (reaches_trans (halts_on_stack hf _)
    (reaches_trans (reaches_of_steps 1 rfl) (errs_on_stack ha _)))

theorem builtin_final_errs {b : BuiltinFun} {args : List CekValue} {ea : ExpectedArgs}
    {wa : CekValue} (hhead : ea.head = .argV) (htail : ea.tail = none)
    (h : evalBuiltin b (wa :: args) = none) :
    Reaches (.ret [.funV (.VBuiltin b args ea)] wa) .error := by
  refine ⟨1, ?_⟩
  show step (.ret [.funV (.VBuiltin b args ea)] wa) = _
  simp only [step, hhead, htail, h]

theorem halts_builtin_of (ρ : CekEnv) (b : BuiltinFun) :
    Halts ρ (.Builtin b) (.VBuiltin b [] (expectedArgs b)) := ⟨2, rfl⟩

/-- The `chooseData s a b c d` state awaiting its last branch. -/
theorem halts_choose_partial {ρ : CekEnv} {s a b c d : Term} {vs va vb vc vd : CekValue}
    (hs : Halts ρ s vs) (ha : Halts ρ a va) (hb : Halts ρ b vb) (hc : Halts ρ c vc)
    (hd : Halts ρ d vd) :
    Halts ρ (.Apply (.Apply (.Apply (.Apply (.Apply (.Force (.Builtin .ChooseData)) s) a) b) c) d)
      (.VBuiltin .ChooseData [vd, vc, vb, va, vs] (.one .argV)) := by
  have h0 : Halts ρ (.Force (.Builtin .ChooseData))
      (.VBuiltin .ChooseData []
        (.more .argV (.more .argV (.more .argV (.more .argV (.more .argV (.one .argV))))))) :=
    ⟨4, rfl⟩
  exact halts_apply_intro (halts_apply_intro (halts_apply_intro (halts_apply_intro
    (halts_apply_intro h0 hs (builtin_partial_reaches rfl rfl)) ha (builtin_partial_reaches rfl rfl))
    hb (builtin_partial_reaches rfl rfl)) hc (builtin_partial_reaches rfl rfl)) hd
    (builtin_partial_reaches rfl rfl)

def bytesOr (d : Moist.Plutus.Data) (other : ByteArray) : ByteArray :=
  match d with
  | .B bytes => bytes
  | _ => other

theorem chooseData_eval (d : Moist.Plutus.Data) (ob : ByteArray) :
    evalBuiltin .ChooseData [.VCon (.Data d), .VCon (.Data (.B ob)), .VCon (.Data (.B ob)),
      .VCon (.Data (.B ob)), .VCon (.Data (.B ob)), .VCon (.Data d)] =
      some (.VCon (.Data (.B (bytesOr d ob)))) := by
  cases d <;> rfl

theorem chooseData_eval_none {vb w : CekValue}
    (h : ∀ d, vb ≠ .VCon (.Data d)) : evalBuiltin .ChooseData [vb, w, w, w, w, vb] = none := by
  cases vb with
  | VCon c =>
    cases c
    all_goals first | (exact absurd rfl (h _)) | (cases w <;> rfl)
  | _ => cases w <;> rfl

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

/-- Prefixing a nonempty byte string changes the bytes. -/
theorem bytes_ne_prefixed {pb : ByteArray} (hp : pb.size ≠ 0) (kb : ByteArray) :
    (kb == (pb ++ kb)) = false := by
  cases h : (kb == (pb ++ kb))
  · rfl
  · exfalso
    have h' : kb.data = (pb ++ kb).data := by
      have : (kb.data == (pb ++ kb).data) = true := h
      simpa using this
    have := congrArg Array.size h'
    simp only [HAppend.hAppend, Append.append, ByteArray.append, ByteArray.copySlice] at this
    simp only [ByteArray.size] at this hp
    simp at this
    rw [this] at hp
    exact hp rfl

theorem byteArray_beq_comm (a b : ByteArray) : (a == b) = (b == a) := by
  show (a.data == b.data) = (b.data == a.data)
  cases h : (a.data == b.data) <;> cases h' : (b.data == a.data) <;> simp_all

/-- `equalsData` against `B k` is the comparison of `k` with the bytes picked
    by `chooseData`, when the other bytes differ from `k`. -/
theorem keyed_equals {kb ob : ByteArray} (hne : (kb == ob) = false) (d : Moist.Plutus.Data) :
    (Moist.Plutus.Data.B kb == d) = (kb == bytesOr d ob) ∧
      (d == Moist.Plutus.Data.B kb) = (kb == bytesOr d ob) := by
  cases d with
  | B b =>
    refine ⟨rfl, ?_⟩
    show (b == kb) = (kb == b)
    exact byteArray_beq_comm b kb
  | _ => exact ⟨hne.symm, hne.symm⟩

/-! ## The rewritten comparison -/

def chooseTerm (s a : Term) : Term :=
  .Apply (.Apply (.Apply (.Apply (.Apply (.Apply (.Force (.Builtin .ChooseData)) s) a) a) a) a) s

def compareTerm (ik io ix : Nat) : Term :=
  .Apply (.Apply (.Builtin .EqualsByteString) (.Var (ik + 1)))
    (.Apply (.Builtin .UnBData) (chooseTerm (.Var (ix + 1)) (.Var (io + 1))))

theorem lower_bytesComparison {env : List VarId} {key other x : VarId} {ik io ix : Nat}
    (hk : envLookupT env key = some ik) (ho : envLookupT env other = some io)
    (hx : envLookupT env x = some ix) :
    lowerTotalExpr env (bytesComparison (.Var key) (.Var other) x) = some (compareTerm ik io ix) := by
  simp [bytesComparison, chooseDataApp, compareTerm, chooseTerm, MIR.lowerTotalExpr_app,
    MIR.lowerTotalExpr_force, lowerTotalExpr_var, lowerTotalExpr_builtin, hk, ho, hx]

theorem compareTerm_data {ρ : CekEnv} {π : Stack} {ik io ix : Nat} {kb ob : ByteArray}
    {d : Moist.Plutus.Data}
    (hk : ρ.lookup (ik + 1) = some (.VCon (.ByteString kb)))
    (ho : ρ.lookup (io + 1) = some (.VCon (.Data (.B ob))))
    (hx : ρ.lookup (ix + 1) = some (.VCon (.Data d))) :
    Reaches (.compute π ρ (compareTerm ik io ix)) (.ret π (.VCon (.Bool (kb == bytesOr d ob)))) := by
  apply halts_on_stack
  have hvo := halts_var_of_lookup (ρ := ρ) ho
  have hvx := halts_var_of_lookup (ρ := ρ) hx
  have hchoose : Halts ρ (chooseTerm (.Var (ix + 1)) (.Var (io + 1))) (.VCon (.Data (.B (bytesOr d ob)))) :=
    halts_apply_intro (halts_choose_partial hvx hvo hvo hvo hvo) hvx
      (builtin_final_reaches rfl rfl (chooseData_eval d ob))
  have hun : Halts ρ (.Apply (.Builtin .UnBData) (chooseTerm (.Var (ix + 1)) (.Var (io + 1))))
      (.VCon (.ByteString (bytesOr d ob))) :=
    halts_apply_intro (halts_builtin_of ρ _) hchoose (builtin_final_reaches rfl rfl rfl)
  have hpart : Halts ρ (.Apply (.Builtin .EqualsByteString) (.Var (ik + 1)))
      (.VBuiltin .EqualsByteString [.VCon (.ByteString kb)] (.one .argV)) :=
    halts_apply_intro (halts_builtin_of ρ _) (halts_var_of_lookup hk) (builtin_partial_reaches rfl rfl)
  exact halts_apply_intro hpart hun (builtin_final_reaches rfl rfl rfl)

theorem compareTerm_other {ρ : CekEnv} {π : Stack} {ik io ix : Nat} {kb ob : ByteArray}
    {vx : CekValue}
    (hk : ρ.lookup (ik + 1) = some (.VCon (.ByteString kb)))
    (ho : ρ.lookup (io + 1) = some (.VCon (.Data (.B ob))))
    (hx : ρ.lookup (ix + 1) = some vx) (hnot : ∀ d, vx ≠ .VCon (.Data d)) :
    Reaches (.compute π ρ (compareTerm ik io ix)) .error := by
  apply errs_on_stack
  have hvo := halts_var_of_lookup (ρ := ρ) ho
  have hvx := halts_var_of_lookup (ρ := ρ) hx
  have hchoose : Errs ρ (chooseTerm (.Var (ix + 1)) (.Var (io + 1))) :=
    errs_apply_intro (halts_choose_partial hvx hvo hvo hvo hvo) hvx
      (builtin_final_errs rfl rfl (chooseData_eval_none hnot))
  have hun : Errs ρ (.Apply (.Builtin .UnBData) (chooseTerm (.Var (ix + 1)) (.Var (io + 1)))) :=
    errs_apply_arg (halts_builtin_of ρ _) hchoose
  have hpart : Halts ρ (.Apply (.Builtin .EqualsByteString) (.Var (ik + 1)))
      (.VBuiltin .EqualsByteString [.VCon (.ByteString kb)] (.one .argV)) :=
    halts_apply_intro (halts_builtin_of ρ _) (halts_var_of_lookup hk) (builtin_partial_reaches rfl rfl)
  exact errs_apply_arg hpart hun

/-! ## Values established by the key facts -/

theorem lookup_of_bound {env : List VarId} {ρ : CekEnv} {x : VarId} {i : Nat}
    (henv : EnvWellFormed env.length ρ) (hi : envLookupT env x = some i) :
    ∃ v, ρ.lookup (i + 1) = some v :=
  let ⟨v, hv, _⟩ := envWellFormed_lookup env.length henv (n := i + 1) (by omega)
    (by have := envLookupT_bound env x i hi; omega)
  ⟨v, hv⟩

theorem bound_some {env : List VarId} {x : VarId} (h : (envLookupT env x).isSome = true) :
    ∃ i, envLookupT env x = some i := Option.isSome_iff_exists.mp h

/-- Under the facts recorded for `other`, the key `k` holds bytes `kb`, `d`
    holds `B kb`, and `other` holds `B (pb ++ kb)` with `pb` nonempty. -/
theorem otherKey_values {Γ : List (VarId × Expr)} {d other key : VarId} {env : List VarId}
    {ρ : CekEnv} {io : Nat} (hok : otherKeyFor Γ d other = some (key, other))
    (hF : FactsHold Produces Γ env ρ) (hd : EnvDistinct env) (henv : EnvWellFormed env.length ρ)
    (hio : envLookupT env other = some io) :
    ∃ ik id kb pb, envLookupT env key = some ik ∧ envLookupT env d = some id ∧ pb.size ≠ 0 ∧
      ρ.lookup (ik + 1) = some (.VCon (.ByteString kb)) ∧
      ρ.lookup (id + 1) = some (.VCon (.Data (.B kb))) ∧
      ρ.lookup (io + 1) = some (.VCon (.Data (.B (pb ++ kb)))) := by
  unfold otherKeyFor at hok
  split at hok
  case h_2 => cases hok
  rename_i bytes hres_o
  split at hok
  case h_2 => cases hok
  rename_i pb ty key' hres_b
  split at hok
  case isFalse => cases hok
  rename_i hsize
  split at hok
  case h_2 => cases hok
  rename_i src hres_k
  split at hok
  case isFalse => cases hok
  rename_i hsrc
  cases hok
  have hsc := FactsScoped.ofFactsHold hF
  have hlo : lowerTotalExpr env (.Var other) = some (.Var (io + 1)) := by
    rw [lowerTotalExpr_var, hio]; rfl
  obtain ⟨ib, hib⟩ := bound_some (resolveHead_app_var_bound 64 Γ (.Var other) hres_o hsc hd (by rw [hlo]; rfl))
  have hlb : lowerTotalExpr env (.Var bytes) = some (.Var (ib + 1)) := by
    rw [lowerTotalExpr_var, hib]; rfl
  obtain ⟨ik, hik⟩ := bound_some (resolveHead_app_var_bound 64 Γ (.Var bytes) hres_b hsc hd (by rw [hlb]; rfl))
  have hlk : lowerTotalExpr env (.Var key) = some (.Var (ik + 1)) := by
    rw [lowerTotalExpr_var, hik]; rfl
  obtain ⟨isrc, hisrc⟩ := bound_some (resolveHead_app_var_bound 64 Γ (.Var key) hres_k hsc hd (by rw [hlk]; rfl))
  obtain ⟨vsrc, hvsrc⟩ := lookup_of_bound henv hisrc
  obtain ⟨vk, hvk⟩ := lookup_of_bound henv hik
  obtain ⟨vb, hvb⟩ := lookup_of_bound henv hib
  obtain ⟨vo, hvo⟩ := lookup_of_bound henv hio
  -- the key
  have hkey := (resolveHead_unary 64 Γ (.Var key) hres_k (b := .UnBData) rfl hF hd hlk hisrc hvsrc).1 vk
  have hunb := hkey.mp (halts_var_of_lookup hvk)
  obtain ⟨c, r, rfl, hc, rfl⟩ := evalBuiltin_single (by decide) hunb
  obtain ⟨kb, rfl, rfl⟩ : ∃ kb, c = .Data (.B kb) ∧ r = .ByteString kb := by
    cases c <;> (try cases hc)
    rename_i dd
    cases dd <;> cases hc
    exact ⟨_, rfl, rfl⟩
  -- the prefixed bytes
  obtain ⟨kX, tX, vX, kY, tY, vY, _, _, htX, hvX, htY, hvY, hr⟩ :=
    resolve_saturated (b := .AppendByteString) rfl 64 Γ (.Var bytes) hres_b (.inr ⟨_, rfl⟩)
      (.inl ⟨_, rfl⟩) hF hd henv hlb
  rw [lowerTotalExpr_lit] at htX; cases htX
  rw [halts_constant hvX] at hr
  obtain ⟨iY, hiY, hvY'⟩ := halts_var_drop hd htY hvY
  rw [hik] at hiY; cases hiY
  rw [hvk] at hvY'; cases hvY'
  have hbytes := halts_var (hr _ rfl)
  rw [hvb] at hbytes; cases hbytes
  -- the other key
  have hoth := (resolveHead_unary 64 Γ (.Var other) hres_o (b := .BData) rfl hF hd hlo hib hvb).1 vo
  have hbd := hoth.mp (halts_var_of_lookup hvo)
  have hcomp : evalBuiltin .BData [.VCon (.ByteString (pb ++ kb))] =
      some (.VCon (.Data (.B (pb ++ kb)))) := rfl
  have hvo' : vo = .VCon (.Data (.B (pb ++ kb))) := by
    rw [hcomp] at hbd; cases hbd; rfl
  subst hvo'
  refine ⟨ik, isrc, kb, pb, hik, ?_, by simpa using hsize, hvk, hvsrc, hvo⟩
  rw [envLookupT_congr hsrc env] at hisrc
  exact hisrc

/-- The names the key facts mention are bound. -/
theorem otherKey_bound {Γ : List (VarId × Expr)} {d other key : VarId} {env : List VarId}
    {io : Nat} (hok : otherKeyFor Γ d other = some (key, other))
    (hsc : FactsScoped Γ env) (hd : EnvDistinct env) (hio : envLookupT env other = some io) :
    ∃ ik, envLookupT env key = some ik := by
  unfold otherKeyFor at hok
  split at hok
  case h_2 => cases hok
  rename_i bytes hres_o
  split at hok
  case h_2 => cases hok
  rename_i pb ty key' hres_b
  split at hok
  case isFalse => cases hok
  split at hok
  case h_2 => cases hok
  split at hok
  case isFalse => cases hok
  cases hok
  have hlo : lowerTotalExpr env (.Var other) = some (.Var (io + 1)) := by
    rw [lowerTotalExpr_var, hio]; rfl
  obtain ⟨ib, hib⟩ := bound_some (resolveHead_app_var_bound 64 Γ (.Var other) hres_o hsc hd (by rw [hlo]; rfl))
  have hlb : lowerTotalExpr env (.Var bytes) = some (.Var (ib + 1)) := by
    rw [lowerTotalExpr_var, hib]; rfl
  exact bound_some (resolveHead_app_var_bound 64 Γ (.Var bytes) hres_b hsc hd (by rw [hlb]; rfl))

/-- The source application and the rewritten comparison agree on every value
    of the compared variable. -/
theorem comparison_obs {ρ : CekEnv} {π : Stack} {tf : Term} {ib ik io ix : Nat}
    {va vb vx : CekValue} {kb ob : ByteArray}
    (hf : Halts ρ tf (.VBuiltin .EqualsData [va] (.one .argV)))
    (hvb : ρ.lookup (ib + 1) = some vb)
    (hvk : ρ.lookup (ik + 1) = some (.VCon (.ByteString kb)))
    (hvo : ρ.lookup (io + 1) = some (.VCon (.Data (.B ob))))
    (hvx : ρ.lookup (ix + 1) = some vx)
    (hval : ∀ dx, vx = .VCon (.Data dx) →
      evalBuiltin .EqualsData [vb, va] = some (.VCon (.Bool (kb == bytesOr dx ob))))
    (hnone : (∀ d, vx ≠ .VCon (.Data d)) → evalBuiltin .EqualsData [vb, va] = none) :
    ObsRefines (.compute π ρ (.Apply tf (.Var (ib + 1)))) (.compute π ρ (compareTerm ik io ix)) := by
  by_cases hdata : ∃ dx, vx = .VCon (.Data dx)
  · obtain ⟨dx, rfl⟩ := hdata
    refine obsRefines_of_reaches (halts_on_stack ?_ π) (compareTerm_data hvk hvo hvx) (obsRefines_refl _)
    exact halts_apply_intro hf (halts_var_of_lookup hvb) (builtin_final_reaches rfl rfl (hval dx rfl))
  · have hnot : ∀ d, vx ≠ .VCon (.Data d) := fun d h => hdata ⟨d, h⟩
    refine obsRefines_of_reaches (errs_on_stack ?_ π) (compareTerm_other hvk hvo hvx hnot)
      (obsRefines_refl _)
    exact errs_apply_intro hf (halts_var_of_lookup hvb) (builtin_final_errs rfl rfl (hnone hnot))

/-- `equalsData a b` with key facts for `a` (when `first`) or for `b`. -/
theorem keyed_comparison_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {f : Expr}
    {a b key other : VarId} (first : Bool)
    (hres : resolveHead 64 Γ f = .App (.Builtin .EqualsData) (.Var a))
    (hok : otherKeyFor Γ (if first then a else b) other = some (key, other))
    (hmem : ∃ entry ∈ Γ, entry.1 = other) :
    FactRel G PF Γ (.App f (.Var b))
      (bytesComparison (.Var key) (.Var other) (if first then b else a)) := by
  intro env t hG hd hfresh hk hsc hlow
  obtain ⟨tf, tb, htf, htb, rfl⟩ := lowerTotalExpr_app_some hlow
  obtain ⟨ib, hib, rfl⟩ := lowerTotalExpr_var_some htb
  obtain ⟨entry, hentry, rfl⟩ := hmem
  obtain ⟨io, hio⟩ := bound_some (hk entry hentry)
  obtain ⟨ik, hik⟩ := otherKey_bound hok hsc hd hio
  obtain ⟨ia, hia⟩ := bound_some (resolveHead_app_var_bound 64 Γ f hres hsc hd (by rw [htf]; rfl))
  obtain ⟨ix, hix, hxv⟩ : ∃ ix, envLookupT env (if first then b else a) = some ix ∧
      ix = (if first then ib else ia) := by
    cases first
    · exact ⟨ia, hia, rfl⟩
    · exact ⟨ib, hib, rfl⟩
  refine ⟨compareTerm ik io ix, lower_bytesComparison hik hio hix, ?_⟩
  intro ρ π henv _ _ hF
  have hP := hF.mono PF_produces
  obtain ⟨ik', id, kb, pb, hik', hid, hpb, hvk, hvd, hvo⟩ := otherKey_values hok hP hd henv hio
  rw [hik] at hik'; cases hik'
  obtain ⟨k, tX, vX, _, htX, hvX, hfv⟩ :=
    resolve_partial (b := .EqualsData) rfl 64 Γ f hres (.inl ⟨a, rfl⟩) hP hd henv htf
  obtain ⟨ia', hia', hva⟩ := halts_var_drop hd htX hvX
  rw [hia] at hia'; cases hia'
  obtain ⟨vb, hvb⟩ := lookup_of_bound henv hib
  have hne := bytes_ne_prefixed hpb kb
  cases first
  · -- the key is `b`
    simp only [Bool.false_eq_true, ↓reduceIte] at hid hxv
    rw [hib] at hid; cases hid
    rw [hvb] at hvd; cases hvd
    subst hxv
    refine comparison_obs hfv hvb hvk hvo hva ?_ ?_
    · intro dx hdx; subst hdx
      show some (CekValue.VCon (.Bool (dx == .B kb))) = _
      rw [(keyed_equals hne dx).2]
    · exact equalsData_eval_none_right
  · -- the key is `a`
    simp only [↓reduceIte] at hid hxv
    rw [hia] at hid; cases hid
    rw [hva] at hvd; cases hvd
    subst hxv
    refine comparison_obs hfv hvb hvk hvo hvb ?_ ?_
    · intro dx hdx; subst hdx
      show some (CekValue.VCon (.Bool (.B kb == dx))) = _
      rw [(keyed_equals hne dx).1]
    · exact equalsData_eval_none_left

theorem otherKeyFor_snd {Γ : List (VarId × Expr)} {d o key o' : VarId}
    (h : otherKeyFor Γ d o = some (key, o')) : o' = o := by
  unfold otherKeyFor at h
  repeat' split at h
  all_goals first | (cases h; rfl) | cases h

theorem keyBytesFact_spec {Γ : List (VarId × Expr)} {d key other : VarId}
    (h : keyBytesFact Γ d = some (key, other)) :
    otherKeyFor Γ d other = some (key, other) ∧ ∃ entry ∈ Γ, entry.1 = other := by
  obtain ⟨entry, hmem, hentry⟩ := List.exists_of_findSome?_eq_some h
  have := otherKeyFor_snd hentry
  subst this
  exact ⟨hentry, entry, hmem, rfl⟩

theorem dataComparison_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {x y : Expr}
    (h : dataComparison Γ x = some y) : FactRel G PF Γ x y := by
  unfold dataComparison at h
  split at h
  · rename_i a b hops
    unfold equalsDataOperands at hops
    split at hops
    · rename_i f arg
      split at hops
      · rename_i first hres
        simp only [Option.some.injEq, Prod.mk.injEq] at hops
        obtain ⟨rfl, rfl⟩ := hops
        split at h
        · rename_i key other hkey
          cases h
          obtain ⟨hok, hmem⟩ := keyBytesFact_spec hkey
          exact keyed_comparison_factRel true hres hok hmem
        · split at h
          · rename_i key other hkey
            cases h
            obtain ⟨hok, hmem⟩ := keyBytesFact_spec hkey
            exact keyed_comparison_factRel false hres hok hmem
          · cases h
      · cases hops
    · cases hops
  · cases h

theorem dataComparison_fresh {Γ : List (VarId × Expr)} {x y : Expr} {env : List VarId}
    (h : dataComparison Γ x = some y) : freshIn env y = true := by
  unfold dataComparison at h
  split at h
  · split at h
    · cases h; simp [bytesComparison, chooseDataApp, freshIn]
    · split at h
      · cases h; simp [bytesComparison, chooseDataApp, freshIn]
      · cases h
  · cases h

/-! ## Map and list round trips -/

def PairDataListValue (v : CekValue) : Prop := ∃ ps, v = .VCon (.ConstPairDataList ps)

def DataListValue (v : CekValue) : Prop := ∃ ds, v = .VCon (.ConstDataList ds)

theorem knownPairDataList_sound (hP : ∀ env ρ rhs v, P env ρ rhs v → Produces env ρ rhs v) :
    ∀ (n : Nat) (Γ : List (VarId × Expr)) (e : Expr) {env : List VarId} {ρ : CekEnv}
      {t : Term} {v : CekValue},
      knownPairDataList n Γ e = true → FactsHold P Γ env ρ → EnvDistinct env →
      lowerTotalExpr env e = some t → Halts ρ t v → PairDataListValue v := by
  intro n
  induction n with
  | zero => intro Γ e env ρ t v h; simp [knownPairDataList] at h
  | succ n ih =>
    intro Γ e env ρ t v h hfacts hd hlow hv
    cases e with
    | Var x =>
      simp only [knownPairDataList] at h
      cases hf : Γ.find? (fun entry => entry.1 == x) with
      | none => rw [hf] at h; cases h
      | some entry =>
        rw [hf] at h
        obtain ⟨k, _, hp, hfacts', hd'⟩ := fact_of_var hfacts hd hf hlow hv
        obtain ⟨t', ht', hv'⟩ := hP _ _ _ _ hp
        exact ih Γ entry.2 (by simpa using h) hfacts' hd' ht' hv'
    | Lit lit =>
      obtain ⟨c, ty⟩ := lit
      rw [lowerTotalExpr_lit] at hlow; cases hlow
      rw [halts_constant hv]
      cases c <;> simp [knownPairDataList] at h
      exact ⟨_, rfl⟩
    | App f a =>
      simp only [knownPairDataList] at h
      obtain ⟨tf, ta, htf, hta, rfl⟩ := lowerTotalExpr_app_some hlow
      obtain ⟨wf, wa, hwf, hwa, rest⟩ := halts_apply hv
      split at h
      · rename_i hhead
        have hstate := resolveHead_protocol hP n Γ f (b := .UnMapData) (by rw [hhead]; rfl)
          hfacts hd htf hwf
        obtain ⟨args, hlen, heval⟩ := saturated_apply hstate rest
        have h1 : valueArity (expectedArgs .UnMapData) = 1 := rfl
        rw [h1] at hlen
        obtain ⟨w, hw⟩ : ∃ w, wa :: args = [w] := by
          cases args with
          | nil => exact ⟨wa, rfl⟩
          | cons _ _ => simp at hlen
        rw [hw] at heval
        obtain ⟨c, r, rfl, hc, rfl⟩ := evalBuiltin_single (by decide) heval
        cases c with
        | Data dd =>
          cases dd
          all_goals first | (cases hc; done) | exact ⟨_, by cases hc; rfl⟩
        | _ => cases hc
      · cases h
    | _ => simp [knownPairDataList] at h

theorem knownDataList_sound (hP : ∀ env ρ rhs v, P env ρ rhs v → Produces env ρ rhs v) :
    ∀ (n : Nat) (Γ : List (VarId × Expr)) (e : Expr) {env : List VarId} {ρ : CekEnv}
      {t : Term} {v : CekValue},
      knownDataList n Γ e = true → FactsHold P Γ env ρ → EnvDistinct env →
      lowerTotalExpr env e = some t → Halts ρ t v → DataListValue v := by
  intro n
  induction n with
  | zero => intro Γ e env ρ t v h; simp [knownDataList] at h
  | succ n ih =>
    intro Γ e env ρ t v h hfacts hd hlow hv
    cases e with
    | Var x =>
      simp only [knownDataList] at h
      cases hf : Γ.find? (fun entry => entry.1 == x) with
      | none => rw [hf] at h; cases h
      | some entry =>
        rw [hf] at h
        obtain ⟨k, _, hp, hfacts', hd'⟩ := fact_of_var hfacts hd hf hlow hv
        obtain ⟨t', ht', hv'⟩ := hP _ _ _ _ hp
        exact ih Γ entry.2 (by simpa using h) hfacts' hd' ht' hv'
    | Lit lit =>
      obtain ⟨c, ty⟩ := lit
      rw [lowerTotalExpr_lit] at hlow; cases hlow
      rw [halts_constant hv]
      cases c <;> simp [knownDataList] at h
      exact ⟨_, rfl⟩
    | App f a =>
      simp only [knownDataList] at h
      obtain ⟨tf, ta, htf, hta, rfl⟩ := lowerTotalExpr_app_some hlow
      obtain ⟨wf, wa, hwf, hwa, rest⟩ := halts_apply hv
      split at h
      · rename_i hhead
        have hstate := resolveHead_protocol hP n Γ f (b := .UnListData) (by rw [hhead]; rfl)
          hfacts hd htf hwf
        obtain ⟨args, hlen, heval⟩ := saturated_apply hstate rest
        have h1 : valueArity (expectedArgs .UnListData) = 1 := rfl
        rw [h1] at hlen
        obtain ⟨w, hw⟩ : ∃ w, wa :: args = [w] := by
          cases args with
          | nil => exact ⟨wa, rfl⟩
          | cons _ _ => simp at hlen
        rw [hw] at heval
        obtain ⟨c, r, rfl, hc, rfl⟩ := evalBuiltin_single (by decide) heval
        cases c with
        | Data dd =>
          cases dd
          all_goals first | (cases hc; done) | exact ⟨_, by cases hc; rfl⟩
        | _ => cases hc
      · cases h
    | _ => simp [knownDataList] at h

theorem roundTrip_UnMapData {vo wc : CekValue} (hq : PairDataListValue vo)
    (h : evalBuiltin .MapData [vo] = some wc) : evalBuiltin .UnMapData [wc] = some vo := by
  obtain ⟨ps, rfl⟩ := hq
  have : evalBuiltin .MapData [.VCon (.ConstPairDataList ps)] = some (.VCon (.Data (.Map ps))) := rfl
  rw [this] at h; cases h; rfl

theorem roundTrip_UnListData {vo wc : CekValue} (hq : DataListValue vo)
    (h : evalBuiltin .ListData [vo] = some wc) : evalBuiltin .UnListData [wc] = some vo := by
  obtain ⟨ds, rfl⟩ := hq
  have : evalBuiltin .ListData [.VCon (.ConstDataList ds)] = some (.VCon (.Data (.List ds))) := rfl
  rw [this] at h; cases h; rfl

/-- A builtin undoing the conversion that produced a checked value returns the
    original value, given the shape of the original value. -/
theorem roundTrip_shape_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {outer inner : BuiltinFun}
    {c o : VarId} {Q : CekValue → Prop}
    (hres : resolveHead 64 Γ (.Var c) = .App (.Builtin inner) (.Var o))
    (hinner : expectedArgs inner = .one .argV) (houter : expectedArgs outer = .one .argV)
    (hshape : ∀ {env : List VarId} {ρ : CekEnv} {t : Term} {v : CekValue},
      FactsHold PF Γ env ρ → EnvDistinct env → lowerTotalExpr env (.Var o) = some t → Halts ρ t v → Q v)
    (hrt : ∀ vo wc, Q vo → evalBuiltin inner [vo] = some wc → evalBuiltin outer [wc] = some vo) :
    FactRel G PF Γ (.App (.Builtin outer) (.Var c)) (.Var o) := by
  intro env t hG hd hfresh hk hsc hlow
  obtain ⟨tb, tc, htb, htc, rfl⟩ := lowerTotalExpr_app_some hlow
  rw [lowerTotalExpr_builtin] at htb; cases htb
  obtain ⟨ic, hic, rfl⟩ := lowerTotalExpr_var_some htc
  have hob := resolveHead_app_var_bound 64 Γ (.Var c) hres hsc hd (by rw [htc]; rfl)
  obtain ⟨io, hio⟩ := Option.isSome_iff_exists.mp hob
  refine ⟨.Var (io + 1), by rw [lowerTotalExpr_var, hio]; rfl, ?_⟩
  intro ρ π henv hlen hπ hF
  obtain ⟨wc, hwc, _⟩ := envWellFormed_lookup env.length henv (n := ic + 1) (by omega)
    (by have := envLookupT_bound env c ic hic; omega)
  obtain ⟨vo, hvo, _⟩ := envWellFormed_lookup env.length henv (n := io + 1) (by omega)
    (by have := envLookupT_bound env o io hio; omega)
  have hun := (resolveHead_unary 64 Γ (.Var c) hres (b := inner) (by simp [forcedBuiltin, hinner])
    (hF.mono PF_produces) hd htc hio hvo).1 wc
  have hq : Q vo := hshape hF hd (by rw [lowerTotalExpr_var, hio]; rfl) (halts_var_of_lookup hvo)
  have heval := hrt vo wc hq (hun.mp (halts_var_of_lookup hwc))
  have hsrc : Reaches (.compute π ρ (.Apply (.Builtin outer) (.Var (ic + 1)))) (.ret π vo) := by
    have h4 : steps 4 (.compute π ρ (.Apply (.Builtin outer) (.Var (ic + 1)))) =
        .ret (.funV (.VBuiltin outer [] (expectedArgs outer)) :: π) wc := by
      simp [steps, step, hwc]
    refine reaches_trans (reaches_of_steps 4 h4) ⟨1, ?_⟩
    simp [steps, step, houter, heval, ExpectedArgs.head, ExpectedArgs.tail]
  exact obsRefines_of_reaches hsrc (reaches_of_steps 1 (by simp [steps, step, hvo]))
    (obsRefines_refl _)

theorem roundTripInverse_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {outer inner : BuiltinFun}
    {c o : VarId} (hres : resolveHead 64 Γ (.Var c) = .App (.Builtin inner) (.Var o))
    (hinv : roundTripInverse Γ outer inner o = true) :
    FactRel G PF Γ (.App (.Builtin outer) (.Var c)) (.Var o) := by
  unfold roundTripInverse at hinv
  split at hinv
  · exact roundTrip_factRel hres rfl rfl roundTrip_IData
  · exact roundTrip_factRel hres rfl rfl roundTrip_UnIData
  · exact roundTrip_factRel hres rfl rfl roundTrip_BData
  · exact roundTrip_factRel hres rfl rfl roundTrip_UnBData
  · exact roundTrip_factRel hres rfl rfl roundTrip_ListData
  · exact roundTrip_factRel hres rfl rfl roundTrip_MapData
  · exact roundTrip_shape_factRel hres rfl rfl
      (fun hF hd hl hv => knownPairDataList_sound PF_produces 64 Γ _ hinv hF hd hl hv)
      (fun _ _ hq h => roundTrip_UnMapData hq h)
  · exact roundTrip_shape_factRel hres rfl rfl
      (fun hF hd hl hv => knownDataList_sound PF_produces 64 Γ _ hinv hF hd hl hv)
      (fun _ _ hq h => roundTrip_UnListData hq h)
  · cases hinv

end Moist.Verified.ShapeFacts
