import Moist.Verified.ProductsSoundness.Replace
import Moist.Verified.CSE.Lowering

/-! # Unboxing known pairs

`let x = r in S` becomes `case r [λf s. S[fstPair x := f, sndPair x := s]]`
when `r` is known to return a builtin pair and every occurrence of `x` in `S`
is a projection (`unbox_factRel`). Both forms evaluate `r` first, in the same
environment and with the same failure. On a pair, the source continues with
`x` bound to the pair; adding the component bindings, replacing the
projections and dropping the now unused `x` relate it to the target, which
binds exactly those components.

A projection `fstPair r` (resp. `sndPair r`) of a known pair similarly
becomes `case r [λf s. f]` (resp. `s`) (`project_factRel`).
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines

theorem beq_false_symm {a b : VarId} (h : (a == b) = false) : (b == a) = false := by
  cases hc : (b == a)
  · rfl
  · rw [varId_beq_symm hc] at h; cases h

/-! ## Dropping the pair binder below the component binders -/

/-- The de Bruijn renaming that skips the third binder. -/
def skipThird : Nat → Nat := liftRename (liftRename (shiftRename 1))

theorem is0Preserving_skipThird : FundamentalRefines.Is0Preserving skipThird := by
  refine ⟨rfl, fun n hn => ?_⟩
  match n, hn with
  | 1, _ => decide
  | n + 2, _ => simp [skipThird, liftRename]

theorem lowerTotalExpr_skipThird {env : List VarId} {x f s : VarId} {e : Expr}
    (hx : (freeVars e).contains x = false) :
    lowerTotalExpr (s :: f :: x :: env) e =
      (lowerTotalExpr (s :: f :: env) e).map (renameTerm skipThird) := by
  have hagree : lowerTotalExpr (s :: f :: x :: env) e = lowerTotalExpr (s :: f :: s :: env) e := by
    apply lowerTotalExpr_agree
    intro v hv
    have hxv : (x == v) = false := by
      cases hc : (x == v)
      · rfl
      · rw [varSet_contains_congr _ hc] at hx; rw [hx] at hv; cases hv
    rw [envLookupT_cons s v (f :: x :: env), envLookupT_cons s v (f :: s :: env)]
    split
    · rfl
    · rename_i hsv
      rw [envLookupT_cons f v (x :: env), envLookupT_cons f v (s :: env)]
      split
      · rfl
      · rw [envLookupT_cons_neq x v env hxv, envLookupT_cons_neq s v env (by simpa using hsv)]
  rw [hagree]
  exact CSE.lowerTotalExpr_renameEnv _ e _ _ fun z =>
    CSE.lookupRename_cons s z fun hsz => CSE.lookupRename_cons f z fun _ => by
      simp only [CSE.LookupRename]
      rw [envLookupT_cons_neq s z env hsz]
      cases envLookupT env z <;> simp [shiftRename]

theorem shiftBisimEnv_of_lookup {σ : Nat → Nat} {ρ₁ ρ₂ : CekEnv} :
    ∀ d, (∀ n, 0 < n → n ≤ d → ∃ w, ρ₁.lookup n = some w ∧ ρ₂.lookup (σ n) = some w ∧
      ValueWellFormed w) → ShiftBisimEnv σ d ρ₁ ρ₂
  | 0, _ => .zero
  | d + 1, h => by
    obtain ⟨w, h₁, h₂, hw⟩ := h (d + 1) (by omega) (by omega)
    exact .succ (shiftBisimEnv_of_lookup d fun n hn hnd => h n hn (by omega)) h₁ h₂
      (shiftBisimValue_refl_id w hw)

/-- The target body, after the source body has dropped the pair binder. -/
theorem obsRefines_skipThird {d : Nat} {ρ : CekEnv} {π : Stack} {t : Term} {v a b : CekValue}
    (henv : EnvWellFormed d ρ) (ha : ValueWellFormed a)
    (hb : ValueWellFormed b) (hπ : StackWellFormed π) (hclosed : closedAt (d + 2) t = true) :
    ObsRefines (.compute π (((ρ.extend v).extend a).extend b) (renameTerm skipThird t))
      (.compute π ((ρ.extend a).extend b) t) := by
  refine (obsRefines_of_shiftBisim (.compute is0Preserving_skipThird ?_ hclosed
    (shiftBisimStack_refl hπ))).2
  apply shiftBisimEnv_of_lookup
  intro n hn hnd
  match n, hn with
  | 1, _ => exact ⟨b, rfl, rfl, hb⟩
  | 2, _ => exact ⟨a, rfl, rfl, ha⟩
  | m + 3, _ =>
    obtain ⟨w, hw, hwf⟩ := envWellFormed_lookup d henv (n := m + 1) (by omega) (by omega)
    refine ⟨w, ?_, ?_, hwf⟩
    · simpa [CekEnv.extend, CekEnv.lookup] using hw
    · simpa [skipThird, liftRename, shiftRename, CekEnv.extend, CekEnv.lookup] using hw

/-! ## Unboxing a binding -/

theorem lowerTotalExpr_unboxed {env : List VarId} {r : Expr} {f s : VarId} {B : Expr}
    {tr tB : Term} (hr : lowerTotalExpr env r = some tr)
    (hB : lowerTotalExpr (s :: f :: env) B = some tB) :
    lowerTotalExpr env (.Case r [.Lam f (.Lam s B)]) = some (.Case tr [.Lam 0 (.Lam 0 tB)]) := by
  rw [MIR.lowerTotalExpr_case_of_list, hr, MIR.lowerTotalExprList_cons, MIR.lowerTotalExpr_lam,
    MIR.lowerTotalExpr_lam, hB, MIR.lowerTotalExprList_nil]
  rfl

theorem unbox_factRel {G G' : VarId → Prop} {Γ : List (VarId × Expr)} {x f s : VarId}
    {r r' S S'' : Expr} {er : Bool}
    (hGG : ∀ y, G y → G' y) (hGf : G' f) (hGs : G' s)
    (hf : ∀ y, (y == f) = true → ¬ G y) (hs : ∀ y, (y == s) = true → ¬ G y)
    (hfs : (f == s) = false) (hxf : (x == f) = false) (hxs : (x == s) = false)
    (hbig : maxUidExpr S < f.uid ∧ maxUidExpr S < s.uid)
    (hr : FactRel G Produces Γ r r') (hknown : knownProduct Γ r' = true)
    (hproj : projectionOnly ((s, sndApp x) :: (f, fstApp x) :: (x, r') :: Γ) x S = true)
    (hS : FactRel G' Produces Γ
      (replaceProjections ((s, sndApp x) :: (f, fstApp x) :: (x, r') :: Γ) x f s S) S'') :
    FactRel G Produces Γ (.Let [(x, r, er)] S) (.Case r' [.Lam f (.Lam s S'')]) := by
  intro env t₀ hG hd hfresh hk hsc hlow
  rw [freshIn_let_single] at hfresh
  simp only [Bool.and_eq_true] at hfresh
  obtain ⟨⟨hfr, hx⟩, hfS⟩ := hfresh
  obtain ⟨tr, tS, htr, htS, rfl⟩ := lowerTotalExpr_let_single_some hlow
  obtain ⟨tr', htr', hrr⟩ := hr env tr hG hd hfr hk hsc htr
  have hfenv : envLookupT env f = none := lookup_none_of_not_G hG hf
  have hsenv : envLookupT env s = none := lookup_none_of_not_G hG hs
  have hsf := beq_false_symm hfs
  -- the source environment with the component binders
  have hd₁ : EnvDistinct (x :: env) := hd.cons hx
  have hd₂ : EnvDistinct (f :: x :: env) :=
    hd₁.cons (by rw [envLookupT_cons_neq x f env hxf, hfenv]; rfl)
  have hd₃ : EnvDistinct (s :: f :: x :: env) :=
    hd₂.cons (by rw [envLookupT_cons_neq f s _ hfs, envLookupT_cons_neq x s env hxs, hsenv]; rfl)
  have hSf : (freeVars S).contains f = false := maxUidExpr_fresh _ _ (by omega)
  have hSs : (freeVars S).contains s = false := maxUidExpr_fresh _ _ (by omega)
  have htS₂ : lowerTotalExpr (f :: x :: env) S = some (renameTerm (shiftRename 1) tS) := by
    rw [MIR.lowerTotalExpr_prepend_unused _ f S hSf, htS]; rfl
  have htS₃ : lowerTotalExpr (s :: f :: x :: env) S =
      some (renameTerm (shiftRename 1) (renameTerm (shiftRename 1) tS)) := by
    rw [MIR.lowerTotalExpr_prepend_unused _ s S hSs, htS₂]; rfl
  have hxx : envLookupT (x :: env) x = some 0 := by simp [envLookupT_cons, varId_beq_self]
  have hfxx : envLookupT (f :: x :: env) x = some 1 := by
    rw [envLookupT_cons_neq f x _ (beq_false_symm hxf), hxx]; rfl
  have hlowFst : lowerTotalExpr (x :: env) (fstApp x) =
      some (.Apply (.Force (.Force (.Builtin .FstPair))) (.Var 1)) := by
    simp only [fstApp, MIR.lowerTotalExpr_app, MIR.lowerTotalExpr_force, lowerTotalExpr_builtin,
      lowerTotalExpr_var, hxx]; rfl
  have hlowSnd : lowerTotalExpr (f :: x :: env) (sndApp x) =
      some (.Apply (.Force (.Force (.Builtin .SndPair))) (.Var 2)) := by
    simp only [sndApp, MIR.lowerTotalExpr_app, MIR.lowerTotalExpr_force, lowerTotalExpr_builtin,
      lowerTotalExpr_var, hfxx]; rfl
  let Γ₃ : List (VarId × Expr) := (s, sndApp x) :: (f, fstApp x) :: (x, r') :: Γ
  have hk₃ : KeysBound Γ₃ (s :: f :: x :: env) := by
    intro entry hmem
    simp only [Γ₃, List.mem_cons] at hmem
    rcases hmem with rfl | rfl | rfl | hmem
    · simp [envLookupT_cons, varId_beq_self]
    · rw [envLookupT_cons]; split
      · rfl
      · simp [envLookupT_cons, varId_beq_self]
    · rw [envLookupT_cons]; split
      · rfl
      · rw [envLookupT_cons]; split
        · simp
        · simp [envLookupT_cons, varId_beq_self]
    · exact ((hk.cons x).cons f).cons s entry hmem
  have hs₃ : FactsScoped Γ₃ (s :: f :: x :: env) :=
    ((hsc.push (x := x) (by simp [htr'])).push (by simp [hlowFst])).push (by simp [hlowSnd])
  have hff : Γ₃.find? (fun e => e.1 == f) = some (f, fstApp x) := by
    simp [Γ₃, varId_beq_self, hsf]
  have hfs₃ : Γ₃.find? (fun e => e.1 == s) = some (s, sndApp x) := by
    simp [Γ₃, varId_beq_self]
  have hfresh₃ : freshIn (s :: f :: x :: env) S = true :=
    freshIn_cons_of_big (freshIn_cons_of_big hfS hbig.1) hbig.2
  obtain ⟨tX, htX, hrX⟩ := replaceProjections_factRel x f s (f, fstApp x) (s, sndApp x) rfl rfl S Γ₃
    hbig hff hfs₃ (s :: f :: x :: env) _ (fun _ _ => trivial) hd₃ hfresh₃ hk₃ hs₃ htS₃
  -- the replaced body no longer mentions the pair binder
  have hnotfree := replaceProjections_not_free Γ₃ x f s (beq_false_symm hxf) (beq_false_symm hxs) S hproj
  rw [lowerTotalExpr_skipThird hnotfree] at htX
  obtain ⟨tY, htY, rfl⟩ : ∃ tY, lowerTotalExpr (s :: f :: env) (replaceProjections Γ₃ x f s S) = some tY ∧
      tX = renameTerm skipThird tY := by
    cases h : lowerTotalExpr (s :: f :: env) (replaceProjections Γ₃ x f s S) with
    | none => rw [h] at htX; cases htX
    | some tY => rw [h] at htX; cases htX; exact ⟨tY, rfl, rfl⟩
  -- the target environment
  obtain ⟨hdf, hkf, hscf, hnf⟩ := enter_binder hd hk hsc (x := f) (by simp [hfenv])
  obtain ⟨hdsf, hksf, hscsf, hns⟩ := enter_binder hdf hkf hscf (x := s)
    (by rw [envLookupT_cons_neq f s env hfs, hsenv]; rfl)
  have hfreshY : freshIn (s :: f :: env) (replaceProjections Γ₃ x f s S) = true := by
    refine freshIn_replaceProjections Γ₃ x f s S _ (freshIn_avoids S hfS ?_)
    intro y hy
    rw [envLookupT_cons] at hy
    split at hy
    · rename_i hsy; right; rw [VarId.beq_true_iff] at hsy; omega
    · rw [envLookupT_cons] at hy
      simp only [Option.isSome_map] at hy
      split at hy
      · rename_i hfy; right; rw [VarId.beq_true_iff] at hfy; omega
      · left
        rw [envLookupT_cons]
        split
        · rfl
        · simpa using hy
  obtain ⟨tY', htY', hrY⟩ := hS (s :: f :: env) tY
    (allG_cons hGs (allG_cons hGf fun y hy => hGG y (hG y hy))) hdsf hfreshY hksf hscsf htY
  refine ⟨.Case tr' [.Lam 0 (.Lam 0 tY')], lowerTotalExpr_unboxed htr' htY', ?_⟩
  -- the runtime argument
  have closedTr := MIR.lowerTotalExpr_closedAt htr
  have closedTr' := MIR.lowerTotalExpr_closedAt htr'
  have closedTS := MIR.lowerTotalExpr_closedAt htS
  have closedTS₂ := MIR.lowerTotalExpr_closedAt htS₂
  have closedTY := MIR.lowerTotalExpr_closedAt htY
  simp only [List.length_cons] at closedTS closedTS₂ closedTY hrX hrY
  intro ρ π henv hlen hπ hF
  refine obsRefines_trans (factRefines_apply (FactRefines.refl _ _ (.Lam 0 tS)) hrr
    (by simp [closedAt, closedTS]) closedTr ρ π henv hlen hπ hF) ?_
  refine obsRefines_of_reaches (s₁' := .compute (.funV (.VLam tS ρ) :: π) ρ tr')
    (s₂' := .compute (.caseScrutinee [.Lam 0 (.Lam 0 tY')] ρ :: π) ρ tr')
    (reaches_of_steps 3 rfl) (reaches_of_steps 1 rfl) ?_
  apply obsRefines_of_continuation
  intro v hv
  have hprod := knownProduct_sound hknown hF hd htr' hv
  obtain ⟨a, b, hcase, hfst, hsnd⟩ := product_components hprod
  have hvwf := halts_wellFormed henv hlen closedTr' hv
  refine obsRefines_of_reaches (reaches_of_steps 1 rfl) (hcase π ρ tY') ?_
  have hlen₁ : env.length + 1 ≤ (ρ.extend v).length := by
    simp [CekEnv.extend, CekEnv.length]; omega
  have henv₁ := envWellFormed_extend env.length henv hlen hvwf
  have hlen₂ : env.length + 1 + 1 ≤ ((ρ.extend v).extend (.VCon a)).length := by
    simp [CekEnv.extend, CekEnv.length]; omega
  have henv₂ := envWellFormed_extend (env.length + 1) henv₁ hlen₁ (.vcon a)
  have hlen₃ : env.length + 1 + 1 + 1 ≤ (((ρ.extend v).extend (.VCon a)).extend (.VCon b)).length := by
    simp [CekEnv.extend, CekEnv.length]; omega
  have henv₃ := envWellFormed_extend (env.length + 1 + 1) henv₂ hlen₂ (.vcon b)
  have hlenT : env.length + 1 + 1 ≤ ((ρ.extend (.VCon a)).extend (.VCon b)).length := by
    simp [CekEnv.extend, CekEnv.length]; omega
  have henvT := envWellFormed_extend (env.length + 1)
    (envWellFormed_extend env.length henv hlen (.vcon a))
    (by simp [CekEnv.extend, CekEnv.length]; omega) (.vcon b)
  have hfstHalts : Halts (ρ.extend v) (.Apply (.Force (.Force (.Builtin .FstPair))) (.Var 1)) (.VCon a) :=
    builtin_app_halts (forced_pair_halts _ (.inl rfl)) rfl hfst
  have hsndHalts : Halts ((ρ.extend v).extend (.VCon a))
      (.Apply (.Force (.Force (.Builtin .SndPair))) (.Var 2)) (.VCon b) :=
    builtin_app_halts (forced_pair_halts _ (.inr rfl)) rfl hsnd
  have hF₃ : FactsHold Produces Γ₃ (s :: f :: x :: env)
      (((ρ.extend v).extend (.VCon a)).extend (.VCon b)) :=
    ((hF.push ⟨tr', htr', hv⟩).push ⟨_, hlowFst, hfstHalts⟩).push ⟨_, hlowSnd, hsndHalts⟩
  have hFT : FactsHold Produces Γ (s :: f :: env) ((ρ.extend (.VCon a)).extend (.VCon b)) :=
    FactsHold.extend _ (FactsHold.extend _ hF hnf) hns
  refine obsRefines_trans (obsEq_shift (.VCon a) henv₁ hπ closedTS).1 ?_
  refine obsRefines_trans (obsEq_shift (.VCon b) henv₂ hπ closedTS₂).1 ?_
  refine obsRefines_trans (hrX _ π henv₃ hlen₃ hπ hF₃) ?_
  refine obsRefines_trans ?_ (hrY _ π henvT hlenT hπ hFT)
  exact obsRefines_skipThird henv (.vcon a) (.vcon b) hπ closedTY

/-! ## Unboxing a bound projection

`let t = fn r in S`, with `fn` resolving to a pair projection and `r` known
to return a pair, becomes `case r [λf s. let t = c in S]` with `c` the
selected component (`unboxProjection_factRel`). Both forms evaluate `r` first;
the projection function is a value and the projection is total on a pair. The
body then runs with `t` bound to the same component, below two binders it does
not mention.
-/

/-- The de Bruijn renaming that skips the second and third binders. -/
def skipTwo : Nat → Nat := liftRename (fun n => shiftRename 1 (shiftRename 1 n))

theorem is0Preserving_skipTwo : FundamentalRefines.Is0Preserving skipTwo := by
  refine ⟨rfl, fun n hn => ?_⟩
  match n, hn with
  | 1, _ => decide
  | n + 2, _ => simp [skipTwo, liftRename]

theorem lowerTotalExpr_skipTwo {env : List VarId} {t f s : VarId} {e : Expr}
    (hf : (freeVars e).contains f = false) (hs : (freeVars e).contains s = false) :
    lowerTotalExpr (t :: s :: f :: env) e =
      (lowerTotalExpr (t :: env) e).map (renameTerm skipTwo) := by
  have hagree : lowerTotalExpr (t :: s :: f :: env) e = lowerTotalExpr (t :: t :: t :: env) e := by
    apply lowerTotalExpr_agree
    intro v hv
    have hfv : (f == v) = false := by
      cases hc : (f == v)
      · rfl
      · rw [varSet_contains_congr _ hc] at hf; rw [hf] at hv; cases hv
    have hsv : (s == v) = false := by
      cases hc : (s == v)
      · rfl
      · rw [varSet_contains_congr _ hc] at hs; rw [hs] at hv; cases hv
    rw [envLookupT_cons t v (s :: f :: env), envLookupT_cons t v (t :: t :: env)]
    split
    · rfl
    · rename_i htv
      rw [envLookupT_cons_neq s v _ hsv, envLookupT_cons_neq f v env hfv,
        envLookupT_cons_neq t v _ (by simpa using htv), envLookupT_cons_neq t v env (by simpa using htv)]
  rw [hagree]
  exact CSE.lowerTotalExpr_renameEnv _ e _ _ fun z =>
    CSE.lookupRename_cons t z fun htz => by
      simp only [CSE.LookupRename]
      rw [envLookupT_cons_neq t z _ htz, envLookupT_cons_neq t z env htz]
      cases envLookupT env z <;> simp [shiftRename]

/-- The body after two binders it does not mention. -/
theorem obsRefines_skipTwo {d : Nat} {ρ : CekEnv} {π : Stack} {t : Term} {a b w : CekValue}
    (henv : EnvWellFormed d ρ) (hw : ValueWellFormed w) (hπ : StackWellFormed π)
    (hclosed : closedAt (d + 1) t = true) :
    ObsRefines (.compute π (ρ.extend w) t)
      (.compute π (((ρ.extend a).extend b).extend w) (renameTerm skipTwo t)) := by
  refine (obsRefines_of_shiftBisim (.compute is0Preserving_skipTwo ?_ hclosed
    (shiftBisimStack_refl hπ))).1
  apply shiftBisimEnv_of_lookup
  intro n hn hnd
  match n, hn with
  | 1, _ => exact ⟨w, rfl, rfl, hw⟩
  | m + 2, _ =>
    obtain ⟨v, hv, hvwf⟩ := envWellFormed_lookup d henv (n := m + 1) (by omega) (by omega)
    refine ⟨v, ?_, ?_, hvwf⟩
    · simpa [CekEnv.extend, CekEnv.lookup] using hv
    · simpa [skipTwo, liftRename, shiftRename, CekEnv.extend, CekEnv.lookup] using hv

theorem unboxProjection_factRel {G G' : VarId → Prop} {Γ : List (VarId × Expr)} {x f s c : VarId}
    {fn a a' S S'' : Expr} {er k : Bool}
    (hGG : ∀ y, G y → G' y) (hGf : G' f) (hGs : G' s)
    (hf : ∀ y, (y == f) = true → ¬ G y) (hs : ∀ y, (y == s) = true → ¬ G y)
    (hfs : (f == s) = false) (hxf : (x == f) = false) (hxs : (x == s) = false)
    (hbig : maxUidExpr S < f.uid ∧ maxUidExpr S < s.uid)
    (hc : c = if k then f else s) (hkind : projectionKind Γ fn = some k)
    (ha : FactRel G Produces Γ a a') (hknown : knownProduct Γ a' = true)
    (hS : FactRel G' Produces Γ (.Let [(x, .Var c, er)] S) S'') :
    FactRel G Produces Γ (.Let [(x, .App fn a, er)] S) (.Case a' [.Lam f (.Lam s S'')]) := by
  intro env t₀ hG hd hfresh hk hsc hlow
  rw [freshIn_let_single] at hfresh
  simp only [freshIn, Bool.and_eq_true] at hfresh
  obtain ⟨⟨⟨hffn, hfa⟩, hx⟩, hfS⟩ := hfresh
  obtain ⟨tr, tS, htr, htS, rfl⟩ := lowerTotalExpr_let_single_some hlow
  obtain ⟨tfn, ta, htfn, hta, rfl⟩ := lowerTotalExpr_app_some htr
  obtain ⟨ta', hta', hra⟩ := ha env ta hG hd hfa hk hsc hta
  have hfenv : envLookupT env f = none := lookup_none_of_not_G hG hf
  have hsenv : envLookupT env s = none := lookup_none_of_not_G hG hs
  have hSf : (freeVars S).contains f = false := maxUidExpr_fresh _ _ (by omega)
  have hSs : (freeVars S).contains s = false := maxUidExpr_fresh _ _ (by omega)
  -- the target environment
  obtain ⟨hdf, hkf, hscf, hnf⟩ := enter_binder hd hk hsc (x := f) (by simp [hfenv])
  obtain ⟨hdsf, hksf, hscsf, hns⟩ := enter_binder hdf hkf hscf (x := s)
    (by rw [envLookupT_cons_neq f s env hfs, hsenv]; rfl)
  have hsf := beq_false_symm hfs
  have hxenv : envLookupT (s :: f :: env) x = none := by
    rw [envLookupT_cons_neq s x _ (beq_false_symm hxs), envLookupT_cons_neq f x _ (beq_false_symm hxf)]
    simpa using hx
  have hcidx : ∃ i, envLookupT (s :: f :: env) c = some i ∧ (i = 1 ∧ k = true ∨ i = 0 ∧ k = false) := by
    subst hc
    cases k
    · exact ⟨0, by simp [envLookupT_cons, varId_beq_self], .inr ⟨rfl, rfl⟩⟩
    · refine ⟨1, ?_, .inl ⟨rfl, rfl⟩⟩
      rw [if_pos rfl, envLookupT_cons_neq s f _ hsf, envLookupT_cons f f env, if_pos (varId_beq_self f)]
      rfl
  obtain ⟨ci, hci, hcik⟩ := hcidx
  have htS₂ : lowerTotalExpr (x :: s :: f :: env) S = some (renameTerm skipTwo tS) := by
    rw [lowerTotalExpr_skipTwo hSf hSs, htS]; rfl
  have hlowAlias : lowerTotalExpr (s :: f :: env) (.Let [(x, .Var c, er)] S) =
      some (.Apply (.Lam 0 (renameTerm skipTwo tS)) (.Var (ci + 1))) := by
    rw [lowerTotalExpr_let_single, lowerTotalExpr_var, hci, htS₂]; rfl
  have hfreshAlias : freshIn (s :: f :: env) (.Let [(x, .Var c, er)] S) = true := by
    rw [freshIn_let_single]
    simp only [freshIn, Bool.true_and, Bool.and_eq_true]
    refine ⟨by simp [hxenv], freshIn_avoids S hfS ?_⟩
    intro y hy
    rw [envLookupT_cons] at hy
    split at hy
    · left; rename_i hxy; rw [envLookupT_cons, if_pos hxy]; rfl
    · rename_i hxy
      rw [envLookupT_cons] at hy
      simp only [Option.isSome_map] at hy
      split at hy
      · rename_i hsy; right; rw [VarId.beq_true_iff] at hsy; omega
      · rw [envLookupT_cons] at hy
        simp only [Option.isSome_map] at hy
        split at hy
        · rename_i hfy; right; rw [VarId.beq_true_iff] at hfy; omega
        · left
          rw [envLookupT_cons, if_neg hxy]
          simpa using hy
  obtain ⟨tY', htY', hrY⟩ := hS (s :: f :: env) _
    (allG_cons hGs (allG_cons hGf fun y hy => hGG y (hG y hy))) hdsf hfreshAlias hksf hscsf hlowAlias
  refine ⟨.Case ta' [.Lam 0 (.Lam 0 tY')], lowerTotalExpr_unboxed hta' htY', ?_⟩
  have closedTfn := MIR.lowerTotalExpr_closedAt htfn
  have closedTa := MIR.lowerTotalExpr_closedAt hta
  have closedTa' := MIR.lowerTotalExpr_closedAt hta'
  have closedTS := MIR.lowerTotalExpr_closedAt htS
  simp only [List.length_cons] at closedTS hrY
  intro ρ π henv hlen hπ hF
  -- the source now evaluates the target's scrutinee
  have congruence : FactRefines env.length (FactsHold Produces Γ env) (.Apply (.Lam 0 tS) (.Apply tfn ta))
      (.Apply (.Lam 0 tS) (.Apply tfn ta')) :=
    factRefines_apply (FactRefines.refl _ _ _)
      (factRefines_apply (FactRefines.refl _ _ _) hra closedTfn closedTa)
      (by simp [closedAt, closedTS]) (by simp [closedAt, closedTfn, closedTa])
  refine obsRefines_trans (congruence ρ π henv hlen hπ hF) ?_
  have hres := projectionKind_some hkind
  have hfb : forcedBuiltin (.Force (.Force (.Builtin (if k then .FstPair else .SndPair)))) =
      some ((if k then .FstPair else .SndPair), .one .argV) := by cases k <;> rfl
  have hfnHalts := resolveHead_forced_halts 64 Γ fn hres hfb hF hd htfn
  refine obsRefines_of_reaches
    (s₁' := .compute (.funV (.VBuiltin (if k then .FstPair else .SndPair) [] (.one .argV)) ::
      .funV (.VLam tS ρ) :: π) ρ ta')
    (s₂' := .compute (.caseScrutinee [.Lam 0 (.Lam 0 tY')] ρ :: π) ρ ta')
    (reaches_trans (reaches_of_steps 4 rfl)
      (reaches_trans (halts_on_stack hfnHalts _) (reaches_of_steps 1 rfl)))
    (reaches_of_steps 1 rfl) ?_
  apply obsRefines_of_continuation
  intro v hv
  obtain ⟨pa, pb, hcase, hfst, hsnd⟩ := product_components (knownProduct_sound hknown hF hd hta' hv)
  let w : CekValue := if k then .VCon pa else .VCon pb
  have heval : evalBuiltin (if k then .FstPair else .SndPair) [v] = some w := by
    cases k
    · exact hsnd
    · exact hfst
  have hwwf : ValueWellFormed w := by cases k <;> exact .vcon _
  refine obsRefines_of_reaches (s₁' := .compute π (ρ.extend w) tS)
    (reaches_of_steps 2 (by simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, heval]))
    (hcase π ρ tY') ?_
  have henvT := envWellFormed_extend (env.length + 1)
    (envWellFormed_extend env.length henv hlen (.vcon pa))
    (by simp [CekEnv.extend, CekEnv.length]; omega) (.vcon pb)
  have hlenT : env.length + 1 + 1 ≤ ((ρ.extend (.VCon pa)).extend (.VCon pb)).length := by
    simp [CekEnv.extend, CekEnv.length]; omega
  have hFT : FactsHold Produces Γ (s :: f :: env) ((ρ.extend (.VCon pa)).extend (.VCon pb)) :=
    FactsHold.extend _ (FactsHold.extend _ hF hnf) hns
  refine obsRefines_trans (obsRefines_skipTwo (a := .VCon pa) (b := .VCon pb) henv hwwf hπ closedTS) ?_
  refine obsRefines_trans ?_ (hrY _ π henvT hlenT hπ hFT)
  refine obsRefines_of_reaches (reaches_of_steps 0 rfl) (reaches_of_steps 5 ?_) (obsRefines_refl _)
  rcases hcik with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · rfl

/-! ## Projections of a known pair -/

theorem project_obs {ρ : CekEnv} {π : Stack} {t : Term} {bf : BuiltinFun} {k : Nat}
    (hbf : bf = .FstPair ∨ bf = .SndPair)
    (hcomp : ∀ v, Halts ρ t v → ∃ w, evalBuiltin bf [v] = some w ∧
      Reaches (.ret (.caseScrutinee [.Lam 0 (.Lam 0 (.Var k))] ρ :: π) v) (.ret π w)) :
    ObsRefines (.compute π ρ (.Apply (.Force (.Force (.Builtin bf))) t))
      (.compute π ρ (.Case t [.Lam 0 (.Lam 0 (.Var k))])) := by
  refine obsRefines_of_reaches
    (reaches_trans (reaches_of_steps 1 rfl) (reaches_trans
      (halts_on_stack (forced_pair_halts ρ hbf) _) (reaches_of_steps 1 rfl)))
    (reaches_of_steps 1 rfl) ?_
  apply obsRefines_of_continuation
  intro v hv
  obtain ⟨w, heval, hreach⟩ := hcomp v hv
  refine obsRefines_of_reaches (s₁' := .ret π w) ?_ hreach (obsRefines_refl _)
  exact ⟨1, by simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, heval]⟩

theorem project_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {fn a a' : Expr}
    {bf : BuiltinFun} {f s c : VarId}
    (hbf : (bf = .FstPair ∧ c = f) ∨ (bf = .SndPair ∧ c = s)) (hsf : (s == f) = false)
    (hfn : FactRel G Produces Γ fn (.Force (.Force (.Builtin bf))))
    (ha : FactRel G Produces Γ a a') (hknown : knownProduct Γ a' = true) :
    FactRel G Produces Γ (.App fn a) (.Case a' [.Lam f (.Lam s (.Var c))]) := by
  intro env t hG hd hfresh hk hsc hlow
  simp only [freshIn, Bool.and_eq_true] at hfresh
  obtain ⟨tf, ta, htf, hta, rfl⟩ := lowerTotalExpr_app_some hlow
  obtain ⟨tf', htf', hrf⟩ := hfn env tf hG hd hfresh.1 hk hsc htf
  obtain ⟨ta', hta', hra⟩ := ha env ta hG hd hfresh.2 hk hsc hta
  simp only [MIR.lowerTotalExpr_force, lowerTotalExpr_builtin, Option.map_some] at htf'
  cases htf'
  have hff : envLookupT (s :: f :: env) f = some 1 := by
    rw [envLookupT_cons_neq s f _ hsf, envLookupT_cons f f env, if_pos (varId_beq_self f)]; rfl
  have hss : envLookupT (s :: f :: env) s = some 0 := by
    rw [envLookupT_cons s s _, if_pos (varId_beq_self s)]
  have congruence : FactRefines env.length (FactsHold Produces Γ env) (.Apply tf ta)
      (.Apply (.Force (.Force (.Builtin bf))) ta') :=
    factRefines_apply hrf hra (by simp [closedAt]) (MIR.lowerTotalExpr_closedAt hta)
  rcases hbf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨_, lowerTotalExpr_unboxed hta' (by rw [lowerTotalExpr_var, hff]; rfl), ?_⟩
    refine congruence.trans fun ρ π henv hlen hπ hF => project_obs (.inl rfl) fun v hv => ?_
    obtain ⟨a, b, hcase, hfst, _⟩ := product_components (knownProduct_sound hknown hF hd hta' hv)
    exact ⟨_, hfst, reaches_trans (hcase π ρ _) (reaches_of_steps 1 rfl)⟩
  · refine ⟨_, lowerTotalExpr_unboxed hta' (by rw [lowerTotalExpr_var, hss]; rfl), ?_⟩
    refine congruence.trans fun ρ π henv hlen hπ hF => project_obs (.inr rfl) fun v hv => ?_
    obtain ⟨a, b, hcase, _, hsnd⟩ := product_components (knownProduct_sound hknown hF hd hta' hv)
    exact ⟨_, hsnd, reaches_trans (hcase π ρ _) (reaches_of_steps 1 rfl)⟩

end Moist.Verified.ShapeFacts
