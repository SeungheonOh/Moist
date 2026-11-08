import Moist.Verified.ShapesSoundness.Rewrites
import Moist.Verified.TagChainsSoundness.Tests

variable [sv : Moist.CEK.SemVariant]

/-! # Evaluation pieces and data round trips

Evaluation lemmas for builtin applications that fail, and the soundness of the
map and list round trips (`unMapData (mapData m) = m` when `m` is known to be a
list of data pairs, and likewise for lists).

(The former `dataComparison` rewrite of `equalsData` into `equalsByteString` is
not sound under builtin semantics variant E, which rejects bytestrings longer
than 65536 bytes in `equalsByteString`; it was removed.)
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

/-! ## Map and list round trips -/

def PairDataListValue (v : CekValue) : Prop := ∃ ps, v = .VCon (.pairDataList ps)

def DataListValue (v : CekValue) : Prop := ∃ ds, v = .VCon (.dataList ds)

omit sv in
theorem pairData_items {items : List Const} (h : items.all isPairDataConst = true) :
    ∃ ps : List (Moist.Plutus.Data × Moist.Plutus.Data), items = ps.map Const.pairData := by
  induction items with
  | nil => exact ⟨[], rfl⟩
  | cons c rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hc, hr⟩ := h
    obtain ⟨ps, rfl⟩ := ih hr
    cases c <;> simp [isPairDataConst] at hc
    rename_i p
    obtain ⟨a, b⟩ := p
    cases a <;> cases b <;> simp [isPairDataConst] at hc
    exact ⟨(_, _) :: ps, rfl⟩

omit sv in
theorem data_items {items : List Const} (h : items.all isDataConst = true) :
    ∃ ds : List Moist.Plutus.Data, items = ds.map Const.Data := by
  induction items with
  | nil => exact ⟨[], rfl⟩
  | cons c rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hc, hr⟩ := h
    obtain ⟨ds, rfl⟩ := ih hr
    cases c <;> simp [isDataConst] at hc
    exact ⟨_ :: ds, rfl⟩

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
      obtain ⟨rfl, hall⟩ := h
      obtain ⟨ps, rfl⟩ := pairData_items (List.all_eq_true.mpr hall)
      exact ⟨ps, rfl⟩
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
      obtain ⟨rfl, hall⟩ := h
      obtain ⟨ds, rfl⟩ := data_items (List.all_eq_true.mpr hall)
      exact ⟨ds, rfl⟩
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
  rw [evalBuiltin_mapData_pairDataList] at h; cases h; rfl

theorem roundTrip_UnListData {vo wc : CekValue} (hq : DataListValue vo)
    (h : evalBuiltin .ListData [vo] = some wc) : evalBuiltin .UnListData [wc] = some vo := by
  obtain ⟨ds, rfl⟩ := hq
  rw [evalBuiltin_listData_dataList] at h; cases h; rfl

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
