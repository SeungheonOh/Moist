import Moist.Verified.FailFastSoundness.Termination
import Moist.Verified.ShapeFacts.Values
import Moist.Verified.ShapeFacts.Results
import Moist.MIR.Optimize.Advanced.TagGuard

/-! # Soundness of the abstract interpreter of the tag prechecks

`aeval fuel Γ H L e = none` implies that the lowering of `e` does not halt,
and `aeval fuel Γ H L e = some a` that every value it halts with is described
by `a`, in every runtime environment where

* the innermost bindings, named by `L`, hold values described by `L`,
* the hypotheses `H` hold for the enclosing (distinct) environment, and
* the enclosing bindings produced their values from the right-hand sides
  recorded in `Γ`.
-/

namespace Moist.Verified.TagGuard

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast

/-! ## Meaning of abstract values -/

def IntHolds : IntInfo → CekValue → Prop
  | .exact n, v => v = .VCon (.Integer n)
  | .notIn s, v => ∃ n, v = .VCon (.Integer n) ∧ n ∉ s

def PairHolds : IntInfo → CekValue → Prop
  | .exact n, v => ∃ d, v = .VCon (.Pair (.Integer n, d))
  | .notIn s, v => ∃ n d, v = .VCon (.Pair (.Integer n, d)) ∧ n ∉ s

def _root_.Moist.MIR.Advanced.AVal.Holds : AVal → CekValue → Prop
  | .top, _ => True
  | .int i, v => IntHolds i v
  | .bool b, v => v = .VCon (.Bool b)
  | .pair i, v => PairHolds i v
  | .constr tag arity, v => ∃ fs, v = .VConstr tag fs ∧ fs.length = arity
  | .fstPairFn, v => v = .VBuiltin .FstPair [] (.one .argV)
  | .eqIntFn i, v => ∃ a, v = .VBuiltin .EqualsInteger [a] (.one .argV) ∧ IntHolds i a

/-- What an abstract result says about a state. -/
def Result (r : Option AVal) (s : State) : Prop :=
  match r with
  | none => ¬ ∃ v, Reaches s (.halt v)
  | some a => ∀ v, Reaches s (.halt v) → a.Holds v

theorem result_top (s : State) : Result (some .top) s := fun _ _ => trivial

theorem result_of_reaches {r : Option AVal} {s s' : State} (h : Reaches s s') (h' : Result r s') :
    Result r s := by
  cases r with
  | none => exact fun ⟨v, hv⟩ => h' ⟨v, reaches_terminal_after (.inr ⟨v, rfl⟩) h hv⟩
  | some a => exact fun v hv => h' v (reaches_terminal_after (.inr ⟨v, rfl⟩) h hv)

/-- A computation that does not halt on the empty stack halts on no stack. -/
theorem no_halt_on_stack {ρ : CekEnv} {t : Term} (h : ¬ ∃ v, Halts ρ t v) (π : Stack) :
    ¬ ∃ v, Reaches (.compute π ρ t) (.halt v) := by
  rintro ⟨v, hv⟩
  rcases sequence (.inr ⟨v, rfl⟩) hv with ⟨_, he⟩ | ⟨w, hw, _⟩
  · cases he
  · exact h ⟨w, hw⟩

theorem result_none_of_sub {ρ : CekEnv} {t : Term} {π : Stack} {s : State}
    (hsub : Reaches s (.compute π ρ t)) (h : Result none (.compute [] ρ t)) : Result none s :=
  result_of_reaches hsub (no_halt_on_stack h π)

/-! ## Environments -/

def LocalsHold (L : List (VarId × AVal)) (ρ : CekEnv) : Prop :=
  ∀ i (h : i < L.length), ∃ v, ρ.lookup (i + 1) = some v ∧ (L[i].2).Holds v

def HypHold (H : List (VarId × AVal)) (env : List VarId) (ρ : CekEnv) : Prop :=
  ∀ x a, lookupAVal H x = some a → ∀ i, envLookupT env x = some i →
    ∃ v, ρ.lookup (i + 1) = some v ∧ a.Holds v

structure Ctx (Γ : List (VarId × Expr)) (H L : List (VarId × AVal)) (outer : List VarId)
    (ρ : CekEnv) : Prop where
  distinct : EnvDistinct outer
  facts : FactsHold Produces Γ outer (dropEnv L.length ρ)
  hyps : HypHold H outer (dropEnv L.length ρ)
  locals : LocalsHold L ρ

theorem LocalsHold.cons {L : List (VarId × AVal)} {ρ : CekEnv} {x : VarId} {a : AVal} {v : CekValue}
    (h : LocalsHold L ρ) (hv : a.Holds v) : LocalsHold ((x, a) :: L) (ρ.extend v) := by
  intro i hi
  cases i with
  | zero => exact ⟨v, rfl, hv⟩
  | succ i =>
    obtain ⟨w, hw, hh⟩ := h i (by simp at hi; omega)
    exact ⟨w, hw, by simpa using hh⟩

theorem Ctx.extend {Γ : List (VarId × Expr)} {H L : List (VarId × AVal)} {outer : List VarId}
    {ρ : CekEnv} (h : Ctx Γ H L outer ρ) {x : VarId} {a : AVal} {v : CekValue} (hv : a.Holds v) :
    Ctx Γ H ((x, a) :: L) outer (ρ.extend v) :=
  ⟨h.distinct, by simpa using h.facts, by simpa using h.hyps, h.locals.cons hv⟩

theorem HypHold.drop {H : List (VarId × AVal)} {env : List VarId} {ρ : CekEnv}
    (h : HypHold H env ρ) (hd : EnvDistinct env) (k : Nat) :
    HypHold H (env.drop k) (dropEnv k ρ) := by
  intro x a ha i hi
  obtain ⟨v, hv, hh⟩ := h x a ha (i + k) (hd.drop_lookup k hi)
  refine ⟨v, ?_, hh⟩
  rw [dropEnv_lookup k ρ (i + 1) (by omega), show i + 1 + k = i + k + 1 by omega]
  exact hv

/-- A local lookup is the first matching binder of the local block. -/
theorem lookupAVal_some : ∀ {L : List (VarId × AVal)} {x : VarId} {a : AVal},
    lookupAVal L x = some a →
      ∃ i, ∃ h : i < L.length, envLookupT (L.map Prod.fst) x = some i ∧ (L[i].2) = a
  | [], _, _, h => by simp [lookupAVal] at h
  | (y, b) :: L, x, a, h => by
    simp only [lookupAVal, List.find?_cons] at h
    by_cases hyx : (y == x) = true
    · simp only [hyx] at h
      cases h
      exact ⟨0, by simp, by simp [envLookupT_cons, hyx], rfl⟩
    · simp only [hyx, Bool.false_eq_true] at h
      obtain ⟨i, hi, hl, ha⟩ := lookupAVal_some (L := L) (by simpa [lookupAVal] using h)
      refine ⟨i + 1, by simp; omega, ?_, by simpa using ha⟩
      rw [List.map_cons, envLookupT_cons, if_neg hyx, hl]; rfl

theorem lookupAVal_none : ∀ {L : List (VarId × AVal)} {x : VarId},
    lookupAVal L x = none → envLookupT (L.map Prod.fst) x = none
  | [], _, _ => by simp [envLookupT, envLookupT.go]
  | (y, b) :: L, x, h => by
    simp only [lookupAVal, List.find?_cons] at h
    by_cases hyx : (y == x) = true
    · simp [hyx] at h
    · simp only [hyx, Bool.false_eq_true] at h
      have := lookupAVal_none (L := L) (by simpa [lookupAVal] using h)
      rw [List.map_cons, envLookupT_cons, if_neg hyx, this]; rfl

/-! ## Builtins -/

theorem evalBuiltin_fstPair {w v : CekValue} (h : evalBuiltin .FstPair [w] = some v) :
    (∃ c d, w = .VCon (.Pair (c, d)) ∧ v = .VCon c) ∨
    (∃ a b, w = .VCon (.PairData (a, b)) ∧ v = .VCon (.Data a)) := by
  obtain ⟨c, r, rfl, hc, rfl⟩ := evalBuiltin_single (by decide) h
  cases c with
  | Pair p =>
    obtain ⟨a, b⟩ := p
    cases hc
    exact .inl ⟨_, _, rfl, rfl⟩
  | PairData p =>
    obtain ⟨a, b⟩ := p
    cases hc
    exact .inr ⟨_, _, rfl, rfl⟩
  | _ => cases hc

theorem evalBuiltin_eqInt {k : Int} {a v : CekValue}
    (h : evalBuiltin .EqualsInteger [.VCon (.Integer k), a] = some v) :
    ∃ n, a = .VCon (.Integer n) ∧ v = .VCon (.Bool (n == k)) := by
  obtain ⟨cs, c, hlen, hc, rfl⟩ := evalBuiltin_const (by decide) h
  cases a with
  | VCon ca =>
    have hcs : extractConsts [.VCon (.Integer k), .VCon ca] = some [.Integer k, ca] := rfl
    simp only [evalBuiltin, evalBuiltinPassThrough_none_of_not_passthrough .EqualsInteger _
      (by decide), hcs] at h
    cases ca with
    | Integer n =>
      have : evalBuiltinConst .EqualsInteger [.Integer k, .Integer n] = some (.Bool (n == k)) := rfl
      rw [this] at h
      cases h
      exact ⟨n, rfl, rfl⟩
    | _ => cases h
  | _ =>
    simp only [evalBuiltin, evalBuiltinPassThrough_none_of_not_passthrough .EqualsInteger _
      (by decide), extractConsts] at h
    cases h

/-! ## Decomposing halting evaluations -/

theorem ite_select' (ρ : CekEnv) (ta tb : Term) (vc : CekValue) :
    (vc = .VCon (.Bool true) ∧
      Reaches (.ret [.funV (.VBuiltin .IfThenElse [] (.more .argV (.more .argV (.one .argV)))),
        .arg (.Delay ta) ρ, .arg (.Delay tb) ρ, .force] vc) (.compute [] ρ ta)) ∨
    (vc = .VCon (.Bool false) ∧
      Reaches (.ret [.funV (.VBuiltin .IfThenElse [] (.more .argV (.more .argV (.one .argV)))),
        .arg (.Delay ta) ρ, .arg (.Delay tb) ρ, .force] vc) (.compute [] ρ tb)) ∨
    Reaches (.ret [.funV (.VBuiltin .IfThenElse [] (.more .argV (.more .argV (.one .argV)))),
        .arg (.Delay ta) ρ, .arg (.Delay tb) ρ, .force] vc) .error := by
  cases vc with
  | VCon c =>
    cases c with
    | Bool b =>
      cases b
      · exact .inr (.inl ⟨rfl, reaches_of_steps 8 rfl⟩)
      · exact .inl ⟨rfl, reaches_of_steps 8 rfl⟩
    | _ => exact .inr (.inr (reaches_of_steps 7 rfl))
  | _ => exact .inr (.inr (reaches_of_steps 7 rfl))

theorem halts_ite {ρ : CekEnv} {tc ta tb : Term} {v : CekValue}
    (h : Halts ρ (.Force (.Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse)) tc) (.Delay ta))
      (.Delay tb))) v) :
    ∃ vc, Halts ρ tc vc ∧ ((vc = .VCon (.Bool true) ∧ Halts ρ ta v) ∨
      (vc = .VCon (.Bool false) ∧ Halts ρ tb v)) := by
  have h8 : Reaches (.compute [] ρ (.Force (.Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse)) tc)
      (.Delay ta)) (.Delay tb))))
      (.compute [.funV (.VBuiltin .IfThenElse [] (.more .argV (.more .argV (.one .argV)))),
        .arg (.Delay ta) ρ, .arg (.Delay tb) ρ, .force] ρ tc) := reaches_of_steps 8 rfl
  have h' := reaches_terminal_after (.inr ⟨v, rfl⟩) h8 h
  rcases sequence (.inr ⟨v, rfl⟩) h' with ⟨_, he⟩ | ⟨vc, hvc, hrest⟩
  · cases he
  · refine ⟨vc, hvc, ?_⟩
    rcases ite_select' ρ ta tb vc with ⟨rfl, hs⟩ | ⟨rfl, hs⟩ | he
    · exact .inl ⟨rfl, reaches_terminal_after (.inr ⟨v, rfl⟩) hs hrest⟩
    · exact .inr ⟨rfl, reaches_terminal_after (.inr ⟨v, rfl⟩) hs hrest⟩
    · exact absurd he (fun he => halt_not_error hrest he)

theorem halts_constrField {ρ : CekEnv} {tag : Nat} :
    ∀ (ms : List Term) {m : Term} {done : List CekValue} {u : CekValue},
      Reaches (.compute [.constrField tag done ms ρ] ρ m) (.halt u) →
      (∀ t ∈ m :: ms, ∃ w, Halts ρ t w) ∧
        ∃ vs, u = .VConstr tag vs ∧ vs.length = done.length + 1 + ms.length
  | [], m, done, u, h => by
    rcases sequence (.inr ⟨u, rfl⟩) h with ⟨_, he⟩ | ⟨v, hv, hrest⟩
    · cases he
    · have : Reaches (.ret [.constrField tag done [] ρ] v) (.halt (.VConstr tag (v :: done).reverse)) :=
        reaches_of_steps 2 rfl
      cases terminal_unique (.inr ⟨_, rfl⟩) (.inr ⟨_, rfl⟩) this hrest
      refine ⟨fun t ht => ?_, _, rfl, by simp⟩
      simp only [List.mem_singleton] at ht
      subst ht; exact ⟨v, hv⟩
  | m' :: ms, m, done, u, h => by
    rcases sequence (.inr ⟨u, rfl⟩) h with ⟨_, he⟩ | ⟨v, hv, hrest⟩
    · cases he
    · have h1 : Reaches (.ret [.constrField tag done (m' :: ms) ρ] v)
          (.compute [.constrField tag (v :: done) ms ρ] ρ m') := reaches_of_steps 1 rfl
      obtain ⟨hall, vs, rfl, hlen⟩ :=
        halts_constrField ms (reaches_terminal_after (.inr ⟨u, rfl⟩) h1 hrest)
      refine ⟨fun t ht => ?_, vs, rfl, by simp at hlen ⊢; omega⟩
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨v, hv⟩
      · exact hall t ht

theorem halts_constr {ρ : CekEnv} {tag : Nat} {ts : List Term} {v : CekValue}
    (h : Halts ρ (.Constr tag ts) v) :
    (∀ t ∈ ts, ∃ w, Halts ρ t w) ∧ ∃ vs, v = .VConstr tag vs ∧ vs.length = ts.length := by
  cases ts with
  | nil =>
    have : Halts ρ (.Constr tag []) (.VConstr tag []) := reaches_of_steps 2 rfl
    cases halts_unique h this
    exact ⟨(fun _ h => by cases h), [], rfl, rfl⟩
  | cons m ms =>
    have h1 : Reaches (.compute [] ρ (.Constr tag (m :: ms))) (.compute [.constrField tag [] ms ρ] ρ m) :=
      reaches_of_steps 1 rfl
    obtain ⟨hall, vs, rfl, hlen⟩ := halts_constrField ms (reaches_terminal_after (.inr ⟨v, rfl⟩) h1 h)
    exact ⟨hall, vs, rfl, by simp at hlen ⊢; omega⟩

/-! ## Case dispatch on known values -/

theorem dispatch_bool (alts : List Term) (b : Bool) :
    dispatch alts (.VCon (.Bool b)) =
      if alts.length > 2 then none else alts[if b then 1 else 0]?.map fun a => (a, []) := by
  cases b <;> simp [dispatch, constToTagAndFields]

theorem dispatch_constr (alts : List Term) (tag : Nat) (fs : List CekValue) :
    dispatch alts (.VConstr tag fs) = alts[tag]?.map fun a => (a, fs) := rfl

theorem dispatch_int (alts : List Term) (n : Int) :
    dispatch alts (.VCon (.Integer n)) =
      if n < 0 then none else alts[n.toNat]?.map fun a => (a, []) := by
  by_cases hn : n < 0
  · have : ¬ (0 ≤ n) := by omega
    simp [dispatch, constToTagAndFields, hn, this]
  · have : 0 ≤ n := by omega
    simp [dispatch, constToTagAndFields, hn, this]

theorem dispatch_pair (alts : List Term) (a b : Const) :
    dispatch alts (.VCon (.Pair (a, b))) =
      if alts.length > 1 then none else alts[0]?.map fun t => (t, [.VCon a, .VCon b]) := by
  simp [dispatch, constToTagAndFields]

theorem dispatch_mem {alts : List Term} {w : CekValue} {a : Term} {fs : List CekValue}
    (h : dispatch alts w = some (a, fs)) : a ∈ alts := by
  cases w with
  | VConstr tag fs' =>
    rw [dispatch_constr] at h
    cases hl : alts[tag]? with
    | none => rw [hl] at h; cases h
    | some a' => rw [hl] at h; cases h; exact List.mem_of_getElem? hl
  | VCon c =>
    simp only [dispatch] at h
    cases hc : constToTagAndFields c with
    | none => rw [hc] at h; cases h
    | some r =>
      obtain ⟨tag, numCtors, fs'⟩ := r
      rw [hc] at h
      simp only at h
      split at h
      · cases h
      · cases hl : alts[tag]? with
        | none => rw [hl] at h; cases h
        | some a' => rw [hl] at h; cases h; exact List.mem_of_getElem? hl
  | VLam _ _ => cases h
  | VDelay _ _ => cases h
  | VBuiltin _ _ _ => cases h

/-- After a case returns `w`, the state the dispatch selects. -/
theorem case_after {ρ : CekEnv} {ts : Term} {talts : List Term} {v : CekValue}
    (h : Halts ρ (.Case ts talts) v) :
    ∃ w, Halts ρ ts w ∧ ∃ a fs, dispatch talts w = some (a, fs) ∧
      Reaches (.compute (fs.map Frame.applyArg) ρ a) (.halt v) := by
  obtain ⟨w, hw, hrest⟩ := halts_case h
  have h1 : Reaches (.ret [.caseScrutinee talts ρ] w) (step (.ret [.caseScrutinee talts ρ] w)) :=
    reaches_of_steps 1 rfl
  have h2 := reaches_terminal_after (.inr ⟨v, rfl⟩) h1 hrest
  rw [step_caseScrutinee] at h2
  cases hd : dispatch talts w with
  | none => rw [hd] at h2; exact absurd h2 (fun h => halt_not_error h (reaches_refl _))
  | some r =>
    obtain ⟨a, fs⟩ := r
    rw [hd] at h2
    exact ⟨w, hw, a, fs, hd, by simpa using h2⟩

/-! ## Alternatives -/

theorem selectAlt_spec {fuel : Nat} {Γ : List (VarId × Expr)} {H L : List (VarId × AVal)}
    {env : List VarId} :
    ∀ (alts : List Expr) (talts : List Term), MIR.lowerTotalExprList env alts = some talts →
      ∀ (n : Nat) (arity : List AVal),
        (talts[n]? = none ∧ selectAlt fuel Γ H L alts n arity = none) ∨
        ∃ a ta, a ∈ alts ∧ talts[n]? = some ta ∧ lowerTotalExpr env a = some ta ∧
          selectAlt fuel Γ H L alts n arity = applyAlt fuel Γ H L a arity
  | [], talts, h, n, arity => by
    rw [MIR.lowerTotalExprList_nil] at h; cases h
    exact .inl ⟨rfl, by rw [selectAlt]⟩
  | a :: alts, talts, h, n, arity => by
    rw [MIR.lowerTotalExprList_cons] at h
    cases ha : lowerTotalExpr env a with
    | none => rw [ha] at h; cases h
    | some ta =>
      cases has : MIR.lowerTotalExprList env alts with
      | none => rw [ha, has] at h; cases h
      | some tas =>
        rw [ha, has] at h; cases h
        cases n with
        | zero => exact .inr ⟨a, ta, .head _, rfl, ha, by rw [selectAlt]⟩
        | succ n =>
          rcases selectAlt_spec (fuel := fuel) (Γ := Γ) (H := H) (L := L) alts tas has n arity with
            ⟨hn, hs⟩ | ⟨b, tb, hb, hn, hlb, hs⟩
          · exact .inl ⟨by simpa using hn, by rw [selectAlt]; exact hs⟩
          · exact .inr ⟨b, tb, .tail _ hb, by simpa using hn, hlb, by rw [selectAlt]; exact hs⟩

theorem fieldsHalt_false {fuel : Nat} {Γ : List (VarId × Expr)} {H L : List (VarId × AVal)} :
    ∀ {fields : List Expr}, fieldsHalt fuel Γ H L fields = false →
      ∃ f ∈ fields, aeval fuel Γ H L f = none
  | [], h => by rw [fieldsHalt] at h; cases h
  | f :: rest, h => by
    rw [fieldsHalt, Bool.and_eq_false_iff] at h
    rcases h with h | h
    · exact ⟨f, .head _, by simpa using h⟩
    · obtain ⟨g, hg, hn⟩ := fieldsHalt_false h
      exact ⟨g, .tail _ hg, hn⟩

theorem allAltsFail_mem {fuel : Nat} {Γ : List (VarId × Expr)} {H L : List (VarId × AVal)} :
    ∀ {alts : List Expr}, allAltsFail fuel Γ H L alts = true → ∀ a ∈ alts, aeval fuel Γ H L a = none
  | [], _, _, h => by cases h
  | a :: rest, h, b, hb => by
    cases a with
    | Lam _ _ => rw [allAltsFail] at h; cases h
    | _ =>
      rw [allAltsFail] at h
      all_goals first
        | (simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h
           rcases List.mem_cons.mp hb with rfl | hb
           · exact h.1
           · exact allAltsFail_mem h.2 b hb)
        | (intro _ _ hx; cases hx)

/-! ## The main induction -/

def GoodE (fuel : Nat) (Γ : List (VarId × Expr)) (H : List (VarId × AVal)) (e : Expr) : Prop :=
  ∀ L outer ρ t, Ctx Γ H L outer ρ → lowerTotalExpr (L.map Prod.fst ++ outer) e = some t →
    Result (aeval fuel Γ H L e) (.compute [] ρ t)

def HoldsAll : List AVal → List CekValue → Prop
  | [], [] => True
  | a :: as, v :: vs => a.Holds v ∧ HoldsAll as vs
  | _, _ => False

theorem holdsAll_replicate_top : ∀ (fs : List CekValue), HoldsAll (List.replicate fs.length .top) fs
  | [] => trivial
  | _ :: fs => ⟨trivial, holdsAll_replicate_top fs⟩

def GoodA (fuel : Nat) (Γ : List (VarId × Expr)) (H : List (VarId × AVal)) (e : Expr) : Prop :=
  ∀ L outer ρ t (fas : List AVal) (fs : List CekValue), HoldsAll fas fs → Ctx Γ H L outer ρ →
    lowerTotalExpr (L.map Prod.fst ++ outer) e = some t →
    Result (applyAlt fuel Γ H L e fas) (.compute (fs.map Frame.applyArg) ρ t)

/-- The value of a variable. -/
theorem varAVal_sound {fuel : Nat} {Γ : List (VarId × Expr)} {H : List (VarId × AVal)}
    (prev : ∀ f, fuel = f + 1 → ∀ e, GoodE f Γ H e)
    {L : List (VarId × AVal)} {outer : List VarId} {ρ : CekEnv} {x : VarId} {t : Term}
    (hctx : Ctx Γ H L outer ρ) (hlow : lowerTotalExpr (L.map Prod.fst ++ outer) (.Var x) = some t) :
    Result (some (varAVal fuel Γ H L x)) (.compute [] ρ t) := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := lowerTotalExpr_var_some hlow
  have hlook := halts_var hv
  unfold varAVal
  cases hL : lookupAVal L x with
  | some a =>
    obtain ⟨j, hj, hlj, ha⟩ := lookupAVal_some hL
    have hij : i = j := by
      rw [envLookupT_append_of_some hlj] at hi; exact (Option.some.inj hi).symm
    subst hij
    obtain ⟨w, hw, hh⟩ := hctx.locals i hj
    rw [hw] at hlook; cases hlook
    simpa [ha] using hh
  | none =>
    have hnone := lookupAVal_none hL
    rw [envLookupT_append_of_none hnone] at hi
    cases hio : envLookupT outer x with
    | none => rw [hio] at hi; cases hi
    | some i' =>
      rw [hio] at hi
      simp only [Option.map_some, Option.some.injEq, List.length_map] at hi
      subst hi
      have hρo : (dropEnv L.length ρ).lookup (i' + 1) = some v := by
        rw [dropEnv_lookup _ ρ _ (by omega), show i' + 1 + L.length = i' + L.length + 1 by omega]
        exact hlook
      cases hH : lookupAVal H x with
      | some a =>
        obtain ⟨w, hw, hh⟩ := hctx.hyps x a hH i' hio
        rw [hρo] at hw; cases hw
        exact hh
      | none =>
        cases fuel with
        | zero => trivial
        | succ f =>
          simp only []
          cases hf : Γ.find? (fun entry => entry.1 == x) with
          | none => trivial
          | some entry =>
            obtain ⟨y, rhs⟩ := entry
            simp only []
            obtain ⟨w, k, _, hk, hw, hp⟩ := hctx.facts x (y, rhs) i' hf hio
            rw [hρo] at hw; cases hw
            obtain ⟨trhs, htrhs, hhalt⟩ := hp
            have hctx' : Ctx Γ H [] (outer.drop k) (dropEnv k (dropEnv L.length ρ)) :=
              ⟨hctx.distinct.drop k, by simpa using hctx.facts.drop hctx.distinct k,
                by simpa using hctx.hyps.drop hctx.distinct k, fun i h => absurd h (by simp)⟩
            have := prev f rfl rhs [] (outer.drop k) _ trhs hctx' (by simpa using htrhs)
            cases hr : aeval f Γ H [] rhs with
            | none => rw [hr] at this; exact absurd ⟨v, hhalt⟩ this
            | some a => rw [hr] at this; exact this v hhalt

/-! ## Small facts used by the induction -/

theorem result_via {r : Option AVal} {s s' : State}
    (h : ∀ v, Reaches s (.halt v) → Reaches s' (.halt v)) (h' : Result r s') : Result r s := by
  cases r with
  | none => exact fun ⟨v, hv⟩ => h' ⟨v, h v hv⟩
  | some a => exact fun v hv => h' v (h v hv)

theorem result_of_no_halt {r : Option AVal} {s : State} (h : ¬ ∃ v, Reaches s (.halt v)) :
    Result r s := by
  cases r with
  | none => exact h
  | some a => exact fun v hv => absurd ⟨v, hv⟩ h

theorem lowerTotalExprList_mem' {env : List VarId} :
    ∀ {es : List Expr} {ts : List Term}, MIR.lowerTotalExprList env es = some ts →
      ∀ e ∈ es, ∃ t ∈ ts, lowerTotalExpr env e = some t
  | [], ts, _, e, he => by cases he
  | a :: as, ts, h, e, he => by
    rw [MIR.lowerTotalExprList_cons] at h
    cases ha : lowerTotalExpr env a with
    | none => rw [ha] at h; cases h
    | some ta =>
      cases has : MIR.lowerTotalExprList env as with
      | none => rw [ha, has] at h; cases h
      | some tas =>
        rw [ha, has] at h; cases h
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨ta, .head _, ha⟩
        · obtain ⟨t, ht, hl⟩ := lowerTotalExprList_mem' has e he
          exact ⟨t, .tail _ ht, hl⟩

theorem lowerTotalExprList_len {env : List VarId} :
    ∀ {es : List Expr} {ts : List Term}, MIR.lowerTotalExprList env es = some ts → ts.length = es.length
  | [], ts, h => by rw [MIR.lowerTotalExprList_nil] at h; cases h; rfl
  | a :: as, ts, h => by
    rw [MIR.lowerTotalExprList_cons] at h
    cases ha : lowerTotalExpr env a with
    | none => rw [ha] at h; cases h
    | some ta =>
      cases has : MIR.lowerTotalExprList env as with
      | none => rw [ha, has] at h; cases h
      | some tas =>
        rw [ha, has] at h; cases h
        simp [lowerTotalExprList_len has]

theorem applyAVal_cases (vf va : AVal) :
    applyAVal vf va = .top ∨ (∃ i, vf = .fstPairFn ∧ va = .pair i ∧ applyAVal vf va = .int i) ∨
      (∃ i k, vf = .eqIntFn i ∧ va = .int (.exact k) ∧ applyAVal vf va = i.eqLit k) := by
  cases vf <;> cases va <;> simp [applyAVal]
  all_goals rename_i i; cases i <;> simp [applyAVal]

theorem halts_fstPair_fn {ρ : CekEnv} {v : CekValue}
    (h : Halts ρ (.Force (.Force (.Builtin .FstPair))) v) : v = .VBuiltin .FstPair [] (.one .argV) :=
  halts_unique h (reaches_of_steps 6 rfl)

theorem halts_builtin_value {ρ : CekEnv} {b : BuiltinFun} {v : CekValue}
    (h : Halts ρ (.Builtin b) v) : v = .VBuiltin b [] (expectedArgs b) :=
  halts_unique h (reaches_of_steps 2 rfl)

/-! ## The abstract interpreter is sound -/

theorem goodA_of_goodE {fuel : Nat} {Γ : List (VarId × Expr)} {H : List (VarId × AVal)} {e : Expr}
    (he : GoodE fuel Γ H e) (hbody : ∀ x b, e = .Lam x b → GoodA fuel Γ H b) : GoodA fuel Γ H e := by
  intro L outer ρ t fas fs hall hctx hlow
  cases fas with
  | nil =>
    cases fs with
    | cons _ _ => exact absurd hall id
    | nil =>
    simp only [List.map_nil]
    rw [applyAlt]
    exact he L outer ρ t hctx hlow
  | cons fa fas =>
    cases fs with
    | nil => exact absurd hall id
    | cons f fs =>
    obtain ⟨hfa, hall'⟩ := hall
    simp only [List.map_cons]
    rw [applyAlt]
    cases e with
    | Lam x b =>
      rw [applyAltSucc]
      obtain ⟨tb, htb, rfl⟩ := lowerTotalExpr_lam_some hlow
      have hr := hbody x b rfl ((x, fa) :: L) outer (ρ.extend f) tb fas fs hall' (hctx.extend hfa)
        (by simpa using htb)
      exact result_of_reaches (reaches_of_steps 2 rfl) hr
    | _ =>
      simp only [applyAltSucc]
      have hr := he L outer ρ t hctx hlow
      cases hae : aeval fuel Γ H L _ with
      | none =>
        rw [hae] at hr
        exact no_halt_on_stack (fun ⟨v, hv⟩ => hr ⟨v, hv⟩) _
      | some a => exact result_top _

theorem aeval_sound_at (Γ : List (VarId × Expr)) (H : List (VarId × AVal)) (fuel : Nat)
    (prev : ∀ f, fuel = f + 1 → ∀ e, GoodE f Γ H e) :
    ∀ (N : Nat) (e : Expr), sizeOf e < N → GoodE fuel Γ H e ∧ GoodA fuel Γ H e := by
  intro N
  induction N with
  | zero => intro e h; omega
  | succ N ih =>
  intro e hsize
  have ihs : ∀ e', sizeOf e' < sizeOf e → GoodE fuel Γ H e' ∧ GoodA fuel Γ H e' :=
    fun e' h => ih e' (by omega)
  have hE : GoodE fuel Γ H e := by
    intro L outer ρ t hctx hlow
    cases e with
    | Var x =>
      rw [aeval]; exact varAVal_sound prev hctx hlow
    | Lit lit =>
      obtain ⟨c, ty⟩ := lit
      rw [lowerTotalExpr_lit] at hlow; cases hlow
      rw [aeval]
      intro v hv
      rw [halts_constant hv]
      cases c <;> simp [litAVal, AVal.Holds, IntHolds]
    | Builtin _ => rw [aeval]; exact result_top _
    | Lam _ _ => rw [aeval]; exact result_top _
    | Delay _ => rw [aeval]; exact result_top _
    | Fix _ _ => rw [aeval]; exact result_top _
    | Error =>
      rw [lowerTotalExpr_error] at hlow; cases hlow
      rw [aeval]
      exact fun ⟨v, hv⟩ => not_halts_error hv
    | Constr tag fields =>
      rw [MIR.lowerTotalExpr_constr_of_list] at hlow
      cases hts : MIR.lowerTotalExprList (L.map Prod.fst ++ outer) fields with
      | none => rw [hts] at hlow; cases hlow
      | some ts =>
        rw [hts] at hlow; cases hlow
        rw [aeval]
        split
        · intro v hv
          obtain ⟨_, vs, rfl, hlen⟩ := halts_constr hv
          exact ⟨vs, rfl, by rw [hlen, lowerTotalExprList_len hts]⟩
        · rename_i hfh
          obtain ⟨f, hf, hnone⟩ := fieldsHalt_false (by simpa using hfh)
          rintro ⟨v, hv⟩
          obtain ⟨hall, _⟩ := halts_constr hv
          obtain ⟨tf, htf, hlf⟩ := lowerTotalExprList_mem' hts f hf
          obtain ⟨w, hw⟩ := hall tf htf
          have hsz : sizeOf f < sizeOf (Expr.Constr tag fields) := by
            have := List.sizeOf_lt_of_mem hf
            simp only [Expr.Constr.sizeOf_spec]; omega
          have := (ihs f hsz).1 L outer ρ tf hctx hlf
          rw [hnone] at this
          exact this ⟨w, hw⟩
    | Case scrutinee alternatives =>
      obtain ⟨ts, talts, hts, htalts, rfl⟩ := lowerTotalExpr_case_some hlow
      have hss : sizeOf scrutinee < sizeOf (Expr.Case scrutinee alternatives) := by
        simp only [Expr.Case.sizeOf_spec]; omega
      have hmem : ∀ a ∈ alternatives, sizeOf a < sizeOf (Expr.Case scrutinee alternatives) := fun a ha => by
        have := List.sizeOf_lt_of_mem ha
        simp only [Expr.Case.sizeOf_spec]; omega
      have hsr := (ihs scrutinee hss).1 L outer ρ ts hctx hts
      have hlenA := lowerTotalExprList_len htalts
      -- the alternative selected by a known dispatch
      have select : ∀ (n : Nat) (fas : List AVal) (fs : List CekValue), HoldsAll fas fs →
          (∀ v, Halts ρ (.Case ts talts) v → ∃ a', talts[n]? = some a' ∧
            Reaches (.compute (fs.map Frame.applyArg) ρ a') (.halt v)) →
          Result (selectAlt fuel Γ H L alternatives n fas) (.compute [] ρ (.Case ts talts)) := by
        intro n fas fs hall hsel
        rcases selectAlt_spec (fuel := fuel) (Γ := Γ) (H := H) (L := L) alternatives talts htalts n
            fas with ⟨hn, hs⟩ | ⟨am, ta, ham, hn, hla, hs⟩
        · rw [hs]
          rintro ⟨v, hv⟩
          obtain ⟨a', ha', _⟩ := hsel v hv
          rw [hn] at ha'; cases ha'
        · rw [hs]
          refine result_via (s' := .compute (fs.map Frame.applyArg) ρ ta) (fun v hv => ?_)
            ((ihs am (hmem am ham)).2 L outer ρ ta fas fs hall hctx hla)
          obtain ⟨a', ha', hr⟩ := hsel v hv
          rw [hn] at ha'; cases ha'; exact hr
      have fallback : Result (if allAltsFail fuel Γ H L alternatives = true then none else some AVal.top)
          (.compute [] ρ (.Case ts talts)) := by
        split
        · rename_i hfail
          rintro ⟨v, hv⟩
          obtain ⟨w, hw, a', fs, hd, hr⟩ := case_after hv
          obtain ⟨am, ham, hla⟩ := lowerTotalExprList_mem htalts a' (dispatch_mem hd)
          have := (ihs am (hmem am ham)).1 L outer ρ a' hctx hla
          rw [allAltsFail_mem hfail am ham] at this
          exact no_halt_on_stack this _ ⟨v, hr⟩
        · exact result_top _
      rw [aeval]
      cases hsa : aeval fuel Γ H L scrutinee with
      | none =>
        rw [hsa] at hsr
        rintro ⟨v, hv⟩
        obtain ⟨w, hw, _⟩ := halts_case hv
        exact hsr ⟨w, hw⟩
      | some a =>
        rw [hsa] at hsr
        cases a with
        | bool b =>
          try dsimp only
          split
          · rename_i hlen
            rintro ⟨v, hv⟩
            obtain ⟨w, hw, a', fs, hd, _⟩ := case_after hv
            have hwb := hsr w hw
            simp only [AVal.Holds] at hwb
            subst hwb
            rw [dispatch_bool, if_pos (by omega)] at hd
            cases hd
          · rename_i hlen
            refine select (if b then 1 else 0) [] [] trivial fun v hv => ?_
            obtain ⟨w, hw, a', fs, hd, hr⟩ := case_after hv
            have hwb := hsr w hw
            simp only [AVal.Holds] at hwb
            subst hwb
            rw [dispatch_bool, if_neg (by omega)] at hd
            cases hl : talts[if b then 1 else 0]? with
            | none => rw [hl] at hd; cases hd
            | some a'' => rw [hl] at hd; cases hd; exact ⟨_, rfl, hr⟩
        | constr tag arity =>
          try dsimp only
          rcases Classical.em (∃ v, Halts ρ (.Case ts talts) v) with ⟨v₀, hv₀⟩ | hno
          · obtain ⟨w₀, hw₀, _, fs₀, _, _⟩ := case_after hv₀
            obtain ⟨fs₁, hfs₁, hlen₁⟩ := hsr w₀ hw₀
            rw [← hlen₁]
            refine select tag _ fs₁ (holdsAll_replicate_top fs₁) fun v hv => ?_
            obtain ⟨w, hw, a', fs, hd, hr⟩ := case_after hv
            have hww := halts_unique hw hw₀
            subst hww
            rw [hfs₁, dispatch_constr] at hd
            cases hl : talts[tag]? with
            | none => rw [hl] at hd; cases hd
            | some a'' => rw [hl] at hd; cases hd; exact ⟨_, rfl, hr⟩
          · exact result_of_no_halt hno
        | int i =>
          cases i with
          | exact n =>
            try dsimp only
            split
            · rename_i hn
              rintro ⟨v, hv⟩
              obtain ⟨w, hw, a', fs, hd, _⟩ := case_after hv
              have hwn := hsr w hw
              simp only [AVal.Holds, IntHolds] at hwn
              subst hwn
              rw [dispatch_int, if_pos hn] at hd
              cases hd
            · rename_i hn
              refine select n.toNat [] [] trivial fun v hv => ?_
              obtain ⟨w, hw, a', fs, hd, hr⟩ := case_after hv
              have hwn := hsr w hw
              simp only [AVal.Holds, IntHolds] at hwn
              subst hwn
              rw [dispatch_int, if_neg hn] at hd
              cases hl : talts[n.toNat]? with
              | none => rw [hl] at hd; cases hd
              | some a'' => rw [hl] at hd; cases hd; exact ⟨_, rfl, hr⟩
          | notIn s =>
            show Result (if ((List.range alternatives.length).all fun k => s.contains (Int.ofNat k)) = true
              then none else if allAltsFail fuel Γ H L alternatives = true then none else some AVal.top) _
            split
            · rename_i hall
              rintro ⟨v, hv⟩
              obtain ⟨w, hw, a', fs, hd, _⟩ := case_after hv
              obtain ⟨n, rfl, hns⟩ := hsr w hw
              rw [dispatch_int] at hd
              split at hd
              · cases hd
              · rename_i hn
                cases hl : talts[n.toNat]? with
                | none => rw [hl] at hd; cases hd
                | some _ =>
                  have hlt : n.toNat < alternatives.length := by
                    rw [← hlenA]; exact (List.getElem?_eq_some_iff.mp hl).1
                  have := List.all_eq_true.mp hall n.toNat (List.mem_range.mpr hlt)
                  have hmem := List.contains_iff_mem.mp this
                  rw [Int.ofNat_eq_coe, Int.toNat_of_nonneg (by omega)] at hmem
                  exact hns hmem
            · exact fallback
        | top => exact fallback
        | pair i =>
          try dsimp only
          split
          · rename_i hlen
            rintro ⟨v, hv⟩
            obtain ⟨w, hw, a', fs, hd, _⟩ := case_after hv
            obtain ⟨n, d, rfl⟩ : ∃ (n : Int) (d : Const), w = .VCon (.Pair (.Integer n, d)) := by
              have := hsr w hw
              cases i with
              | exact n => obtain ⟨d, h⟩ := this; exact ⟨n, d, h⟩
              | notIn s => obtain ⟨n, d, h, _⟩ := this; exact ⟨n, d, h⟩
            rw [dispatch_pair, if_pos (by omega)] at hd
            cases hd
          · rename_i hlen
            rcases Classical.em (∃ v, Halts ρ (.Case ts talts) v) with ⟨v₀, hv₀⟩ | hno
            · obtain ⟨w₀, hw₀, _, _, _, _⟩ := case_after hv₀
              have hw₀' := hsr w₀ hw₀
              obtain ⟨n, d, rfl, hn⟩ : ∃ (n : Int) (d : Const), w₀ = .VCon (.Pair (.Integer n, d)) ∧
                  IntHolds i (.VCon (.Integer n)) := by
                cases i with
                | exact n => obtain ⟨d, h⟩ := hw₀'; exact ⟨n, d, h, rfl⟩
                | notIn s => obtain ⟨n, d, h, hs⟩ := hw₀'; exact ⟨n, d, h, n, rfl, hs⟩
              refine select 0 [.int i, .top] [.VCon (.Integer n), .VCon d] ⟨hn, trivial, trivial⟩
                fun v hv => ?_
              obtain ⟨w, hw, a', fs, hd, hr⟩ := case_after hv
              have hww := halts_unique hw hw₀
              subst hww
              rw [dispatch_pair, if_neg (by omega)] at hd
              cases hl : talts[0]? with
              | none => rw [hl] at hd; cases hd
              | some a'' => rw [hl] at hd; cases hd; exact ⟨_, rfl, hr⟩
            · exact result_of_no_halt hno
        | fstPairFn => exact fallback
        | eqIntFn _ => exact fallback
    | Let bindings body =>
      have hbody : sizeOf body < sizeOf (Expr.Let bindings body) := by
        simp only [Expr.Let.sizeOf_spec]; omega
      have hbinds : ∀ b ∈ bindings, sizeOf b.2.1 < sizeOf (Expr.Let bindings body) := fun b hb => by
        have := List.sizeOf_lt_of_mem hb
        obtain ⟨x, r, er⟩ := b
        simp only [Expr.Let.sizeOf_spec, Prod.mk.sizeOf_spec] at this ⊢; omega
      rw [aeval]
      suffices key : ∀ (bs : List (VarId × Expr × Bool)), (∀ b ∈ bs, b ∈ bindings) →
          ∀ L ρ t, Ctx Γ H L outer ρ → lowerTotalExpr (L.map Prod.fst ++ outer) (.Let bs body) = some t →
            Result (aevalLet fuel Γ H L bs body) (.compute [] ρ t) from
        key bindings (fun _ h => h) L ρ t hctx hlow
      intro bs
      induction bs with
      | nil =>
        intro _ L ρ t hctx hlow
        rw [lowerTotalExpr_let_nil] at hlow
        rw [aevalLet]
        exact (ihs body hbody).1 L outer ρ t hctx hlow
      | cons b rest ihb =>
        obtain ⟨x, r, er⟩ := b
        intro hsub L ρ t hctx hlow
        rw [lowerTotalExpr_let_cons] at hlow
        obtain ⟨tr, tb, htr, htb, rfl⟩ := lowerTotalExpr_let_single_some hlow
        have hrr := (ihs r (hbinds _ (hsub _ (.head _)))).1 L outer ρ tr hctx htr
        rw [aevalLet]
        cases har : aeval fuel Γ H L r with
        | none =>
          rw [har] at hrr
          rintro ⟨v, hv⟩
          obtain ⟨_, wa, _, hwa, _⟩ := halts_apply hv
          exact hrr ⟨wa, hwa⟩
        | some a =>
          rw [har] at hrr
          rcases Classical.em (∃ wa, Halts ρ tr wa) with ⟨wa, hwa⟩ | hno
          · refine result_via (s' := .compute [] (ρ.extend wa) tb) (fun v hv => ?_)
              (ihb (fun b hb => hsub b (.tail _ hb)) ((x, a) :: L) (ρ.extend wa) tb
                (hctx.extend (hrr wa hwa)) (by simpa using htb))
            obtain ⟨wf, wa', hwf, hwa', hrest⟩ := halts_apply hv
            have := halts_unique hwa' hwa
            subst this
            rw [halts_lam hwf] at hrest
            rcases apply_reaches hrest with ⟨body', ρ', heq, hb⟩ | ⟨_, _, _, heq, _⟩
            · cases heq; exact hb
            · cases heq
          · exact result_of_no_halt fun ⟨v, hv⟩ => by
              obtain ⟨_, wa, _, hwa, _⟩ := halts_apply hv
              exact hno ⟨wa, hwa⟩
    | Force inner =>
      obtain ⟨ti, hti, rfl⟩ := lowerTotalExpr_force_some hlow
      have hsz : sizeOf inner < sizeOf (Expr.Force inner) := by
        simp only [Expr.Force.sizeOf_spec]; omega
      rw [aeval]
      split
      · rename_i hfp
        have : inner = .Force (.Builtin .FstPair) := by
          unfold isForcedFstPair at hfp
          split at hfp
          · rfl
          · cases hfp
        subst this
        obtain ⟨t2, ht2, rfl⟩ := lowerTotalExpr_force_some hti
        rw [lowerTotalExpr_builtin] at ht2; cases ht2
        intro v hv
        exact halts_fstPair_fn hv
      · split
        · rename_i c a b hv
          have hsz' := iteView_sizeOf hv
          have := iteView_some hv
          subst this
          obtain ⟨t1, tbd, ht1, htbd, rfl⟩ := lowerTotalExpr_app_some hti
          obtain ⟨t2, tad, ht2, htad, rfl⟩ := lowerTotalExpr_app_some ht1
          obtain ⟨t3, tc, ht3, htc, rfl⟩ := lowerTotalExpr_app_some ht2
          obtain ⟨t4, ht4, rfl⟩ := lowerTotalExpr_force_some ht3
          rw [lowerTotalExpr_builtin] at ht4; cases ht4
          obtain ⟨ta, hta, rfl⟩ := lowerTotalExpr_delay_some htad
          obtain ⟨tb, htb, rfl⟩ := lowerTotalExpr_delay_some htbd
          have hcs : sizeOf c < sizeOf (Expr.Force (.App (.App (.App (.Force (.Builtin .IfThenElse)) c)
              (.Delay a)) (.Delay b))) := by simp only [Expr.Force.sizeOf_spec]; omega
          have has : sizeOf a < sizeOf (Expr.Force (.App (.App (.App (.Force (.Builtin .IfThenElse)) c)
              (.Delay a)) (.Delay b))) := by simp only [Expr.Force.sizeOf_spec]; omega
          have hbs : sizeOf b < sizeOf (Expr.Force (.App (.App (.App (.Force (.Builtin .IfThenElse)) c)
              (.Delay a)) (.Delay b))) := by simp only [Expr.Force.sizeOf_spec]; omega
          have hc := (ihs c hcs).1 L outer ρ tc hctx htc
          have ha := (ihs a has).1 L outer ρ ta hctx hta
          have hb := (ihs b hbs).1 L outer ρ tb hctx htb
          cases hac : aeval fuel Γ H L c with
          | none =>
            rw [hac] at hc
            rintro ⟨v, hv⟩
            obtain ⟨vc, hvc, _⟩ := halts_ite hv
            exact hc ⟨vc, hvc⟩
          | some ac =>
            rw [hac] at hc
            have generic : Result (match aeval fuel Γ H L a, aeval fuel Γ H L b with
                | none, none => none
                | _, _ => some AVal.top)
                (.compute [] ρ (.Force (.Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse)) tc)
                  (.Delay ta)) (.Delay tb)))) := by
              cases haa : aeval fuel Γ H L a <;> cases hab : aeval fuel Γ H L b
              · rw [haa] at ha; rw [hab] at hb
                rintro ⟨v, hv⟩
                obtain ⟨vc, _, ⟨_, hta'⟩ | ⟨_, htb'⟩⟩ := halts_ite hv
                · exact ha ⟨v, hta'⟩
                · exact hb ⟨v, htb'⟩
              all_goals exact result_top _
            cases ac with
            | bool bb =>
              cases bb with
              | true =>
                refine result_via (s' := .compute [] ρ ta) (fun v hv => ?_) ha
                obtain ⟨vc, hvc, ⟨_, hta'⟩ | ⟨rfl, _⟩⟩ := halts_ite hv
                · exact hta'
                · have := hc _ hvc; simp [AVal.Holds] at this
              | false =>
                refine result_via (s' := .compute [] ρ tb) (fun v hv => ?_) hb
                obtain ⟨vc, hvc, ⟨rfl, _⟩ | ⟨_, htb'⟩⟩ := halts_ite hv
                · have := hc _ hvc; simp [AVal.Holds] at this
                · exact htb'
            | _ => exact generic
        · have hi := (ihs inner hsz).1 L outer ρ ti hctx hti
          cases hai : aeval fuel Γ H L inner with
          | none =>
            rw [hai] at hi
            rintro ⟨v, hv⟩
            obtain ⟨w, hw, _⟩ := halts_force hv
            exact hi ⟨w, hw⟩
          | some _ => exact result_top _
    | App f a =>
      obtain ⟨tf, ta, htf, hta, rfl⟩ := lowerTotalExpr_app_some hlow
      have hfs : sizeOf f < sizeOf (Expr.App f a) := by simp only [Expr.App.sizeOf_spec]; omega
      have has : sizeOf a < sizeOf (Expr.App f a) := by simp only [Expr.App.sizeOf_spec]; omega
      have hf := (ihs f hfs).1 L outer ρ tf hctx htf
      have ha := (ihs a has).1 L outer ρ ta hctx hta
      rw [aeval]
      have noF : aeval fuel Γ H L f = none → ¬ ∃ v, Halts ρ (.Apply tf ta) v := by
        intro haf ⟨v, hv⟩
        rw [haf] at hf
        obtain ⟨wf, _, hwf, _⟩ := halts_apply hv
        exact hf ⟨wf, hwf⟩
      have noA : aeval fuel Γ H L a = none → ¬ ∃ v, Halts ρ (.Apply tf ta) v := by
        intro haa ⟨v, hv⟩
        rw [haa] at ha
        obtain ⟨_, wa, _, hwa, _⟩ := halts_apply hv
        exact ha ⟨wa, hwa⟩
      cases haf : aeval fuel Γ H L f with
      | none =>
        cases aeval fuel Γ H L a <;> exact noF haf
      | some vf =>
        cases haa : aeval fuel Γ H L a with
        | none => exact noA haa
        | some va =>
          rw [haf] at hf; rw [haa] at ha
          show Result (some _) _
          intro v hv
          obtain ⟨wf, wa, hwf, hwa, hrest⟩ := halts_apply hv
          split
          · rename_i heq
            have : f = .Builtin .EqualsInteger := by
              unfold isEqualsInteger at heq
              split at heq
              · rfl
              · cases heq
            subst this
            rw [lowerTotalExpr_builtin] at htf; cases htf
            rw [halts_builtin_value hwf] at hrest
            rcases apply_reaches hrest with ⟨_, _, h, _⟩ | ⟨b, args, ea, h, _, htail⟩
            · cases h
            · cases h
              rcases htail with ⟨rest, hrest', rfl⟩ | ⟨hnone, _⟩
              · simp only [expectedArgs, ExpectedArgs.tail, Option.some.injEq] at hrest'
                subst hrest'
                cases va with
                | int i => exact ⟨wa, rfl, ha wa hwa⟩
                | _ => trivial
              · simp [expectedArgs, ExpectedArgs.tail] at hnone
          · split
            · rename_i hucd
              have : f = .Builtin .UnConstrData := by
                unfold isUnConstrData at hucd
                split at hucd
                · rfl
                · cases hucd
              subst this
              rw [lowerTotalExpr_builtin] at htf; cases htf
              rw [halts_builtin_value hwf] at hrest
              rcases apply_reaches hrest with ⟨_, _, h, _⟩ | ⟨b, args, ea, h, _, htail⟩
              · cases h
              · cases h
                rcases htail with ⟨_, hr', _⟩ | ⟨_, hev⟩
                · simp [expectedArgs, ExpectedArgs.tail] at hr'
                · obtain ⟨c, r, rfl, hc, rfl⟩ := evalBuiltin_single (by decide) hev
                  cases c with
                  | Data dd =>
                    cases dd with
                    | Constr tag fields => cases hc; exact ⟨_, _, rfl, by simp⟩
                    | _ => cases hc
                  | _ => cases hc
            rcases applyAVal_cases vf va with htop | ⟨i, rfl, rfl, heq⟩ | ⟨i, k, rfl, rfl, heq⟩
            · rw [htop]; trivial
            · rw [heq]
              have hwf' : wf = .VBuiltin .FstPair [] (.one .argV) := hf wf hwf
              subst hwf'
              rcases apply_reaches hrest with ⟨_, _, h, _⟩ | ⟨b, args, ea, h, _, htail⟩
              · cases h
              · cases h
                rcases htail with ⟨_, hrest', _⟩ | ⟨_, hev⟩
                · simp [ExpectedArgs.tail] at hrest'
                · have hpair := ha wa hwa
                  rcases evalBuiltin_fstPair hev with ⟨c, d, rfl, rfl⟩ | ⟨x, y, rfl, rfl⟩
                  · cases i with
                    | exact n =>
                      obtain ⟨d', hd'⟩ := hpair
                      cases hd'
                      rfl
                    | notIn s =>
                      obtain ⟨n, d', hd', hn⟩ := hpair
                      cases hd'
                      exact ⟨n, rfl, hn⟩
                  · cases i with
                    | exact n =>
                      obtain ⟨d', hd'⟩ := hpair
                      cases hd'
                    | notIn s =>
                      obtain ⟨n, d', hd', hn⟩ := hpair
                      cases hd'
            · rw [heq]
              obtain ⟨a0, rfl, ha0⟩ := hf wf hwf
              have hwk : wa = .VCon (.Integer k) := ha wa hwa
              subst hwk
              rcases apply_reaches hrest with ⟨_, _, h, _⟩ | ⟨b, args, ea, h, _, htail⟩
              · cases h
              · cases h
                rcases htail with ⟨_, hrest', _⟩ | ⟨_, hev⟩
                · simp [ExpectedArgs.tail] at hrest'
                · obtain ⟨n, rfl, rfl⟩ := evalBuiltin_eqInt hev
                  cases i with
                  | exact n' =>
                    have : n = n' := by
                      simp only [IntHolds, CekValue.VCon.injEq, Const.Integer.injEq] at ha0
                      exact ha0
                    subst this
                    rfl
                  | notIn s =>
                    simp only [IntInfo.eqLit]
                    split
                    · rename_i hk
                      have hnk : n ≠ k := by
                        intro hnk; subst hnk
                        obtain ⟨m, hm, hms⟩ := ha0
                        cases hm
                        exact hms (List.contains_iff_mem.mp hk)
                      simp [AVal.Holds, hnk]
                    · trivial
  refine ⟨hE, goodA_of_goodE hE fun x b hx => ?_⟩
  subst hx
  exact (ihs b (by simp only [Expr.Lam.sizeOf_spec]; omega)).2

theorem aeval_sound (Γ : List (VarId × Expr)) (H : List (VarId × AVal)) :
    ∀ (fuel : Nat) (e : Expr), GoodE fuel Γ H e ∧ GoodA fuel Γ H e := by
  intro fuel
  induction fuel with
  | zero => exact fun e => aeval_sound_at Γ H 0 (fun f h => absurd h (by omega)) _ e (Nat.lt_succ_self _)
  | succ f ihf =>
    exact fun e => aeval_sound_at Γ H (f + 1) (fun f' h e' => by cases h; exact (ihf e').1) _ e
      (Nat.lt_succ_self _)

end Moist.Verified.TagGuard
