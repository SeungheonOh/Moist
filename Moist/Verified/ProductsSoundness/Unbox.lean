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
    (hproj : projectionOnly x S = true)
    (hS : FactRel G' Produces Γ (replaceProjections x f s S) S'') :
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
  have hnotfree := replaceProjections_not_free x f s (beq_false_symm hxf) (beq_false_symm hxs) S hproj
  rw [lowerTotalExpr_skipThird hnotfree] at htX
  obtain ⟨tY, htY, rfl⟩ : ∃ tY, lowerTotalExpr (s :: f :: env) (replaceProjections x f s S) = some tY ∧
      tX = renameTerm skipThird tY := by
    cases h : lowerTotalExpr (s :: f :: env) (replaceProjections x f s S) with
    | none => rw [h] at htX; cases htX
    | some tY => rw [h] at htX; cases htX; exact ⟨tY, rfl, rfl⟩
  -- the target environment
  obtain ⟨hdf, hkf, hscf, hnf⟩ := enter_binder hd hk hsc (x := f) (by simp [hfenv])
  obtain ⟨hdsf, hksf, hscsf, hns⟩ := enter_binder hdf hkf hscf (x := s)
    (by rw [envLookupT_cons_neq f s env hfs, hsenv]; rfl)
  have hfreshY : freshIn (s :: f :: env) (replaceProjections x f s S) = true := by
    rw [freshIn_replaceProjections]
    refine freshIn_avoids S hfS ?_
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
