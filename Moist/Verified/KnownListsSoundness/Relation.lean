import Moist.Verified.CheckedBranchesSoundness.Relation
import Moist.MIR.Optimize.Advanced.KnownLists

variable [sv : Moist.CEK.SemVariant]

/-! # Refinement under list facts

`KnownRel Γ L e e'` is `FactRel` with an additional set `L` of names known to
hold lists (plain, data or data-pair): in every distinct lowering environment
that binds every name of `L`, the lowerings refine each other in every
runtime environment realizing both the binding facts `Γ` and the list facts
of `L` (`KnownFacts`). Binders of a well-scoped program never shadow a name
of `L`, so a list fact survives every binder below the point that
established it.
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.BetaValueRefines

/-- Every listed name bound in `env` holds a list in `ρ`. -/
def ListsHold (L : List VarId) (env : List VarId) (ρ : CekEnv) : Prop :=
  ∀ x, L.contains x = true → ∀ i, envLookupT env x = some i →
    ∃ v, ρ.lookup (i + 1) = some v ∧ ListValue v

def KnownFacts (Γ : List (VarId × Expr)) (L : List VarId) (env : List VarId) (ρ : CekEnv) : Prop :=
  FactsHold Produces Γ env ρ ∧ ListsHold L env ρ

def KnownRel (Γ : List (VarId × Expr)) (L : List VarId) (e e' : Expr) : Prop :=
  ∀ env t, EnvDistinct env → freshIn env e = true → KeysBound Γ env → FactsScoped Γ env →
    NamesBound L env → lowerTotalExpr env e = some t →
    ∃ t', lowerTotalExpr env e' = some t' ∧ FactRefines env.length (KnownFacts Γ L env) t t'

/-! ## List facts under binders -/

omit sv in
theorem ListsHold.nil (env : List VarId) (ρ : CekEnv) : ListsHold [] env ρ := by
  intro y hy; simp at hy

omit sv in
theorem ListsHold.extend {L env : List VarId} {ρ : CekEnv} {x : VarId} (w : CekValue)
    (h : ListsHold L env ρ) (hb : NamesBound L env) (hx : (envLookupT env x).isNone = true) :
    ListsHold L (x :: env) (ρ.extend w) := by
  intro y hy i hl
  rw [envLookupT_cons_neq x y env (hb.fresh hx y hy)] at hl
  cases hl' : envLookupT env y with
  | none => rw [hl'] at hl; cases hl
  | some i' =>
    rw [hl'] at hl; simp at hl; subst hl
    exact h y hy i' hl'

omit sv in
/-- A list fact for a name bound in the current environment. -/
theorem ListsHold.add {L env : List VarId} {ρ : CekEnv} {l : VarId} (h : ListsHold L env ρ)
    (hl : ∀ i, envLookupT env l = some i → ∃ v, ρ.lookup (i + 1) = some v ∧ ListValue v) :
    ListsHold (l :: L) env ρ := by
  intro y hy i hi
  simp only [List.contains_cons, Bool.or_eq_true] at hy
  rcases hy with hy | hy
  · rw [envLookupT_congr hy] at hi; exact hl i hi
  · exact h y hy i hi

omit sv in
/-- A new binder holding a list. -/
theorem ListsHold.push {L env : List VarId} {ρ : CekEnv} {x : VarId} {w : CekValue}
    (h : ListsHold L env ρ) (hb : NamesBound L env) (hx : (envLookupT env x).isNone = true)
    (hw : ListValue w) : ListsHold (x :: L) (x :: env) (ρ.extend w) := by
  refine (h.extend w hb hx).add ?_
  intro i hi
  rw [MIR.envLookupT_cons_of_beq (varId_beq_self x) env] at hi
  cases hi
  exact ⟨w, rfl, hw⟩

omit sv in
/-- List facts survive moving to an older suffix of a distinct environment. -/
theorem ListsHold.drop {L env : List VarId} {ρ : CekEnv} (h : ListsHold L env ρ)
    (hd : EnvDistinct env) (j : Nat) : ListsHold L (env.drop j) (dropEnv j ρ) := by
  intro y hy i hi
  have hi' := hd.drop_lookup j hi
  obtain ⟨v, hv, hlv⟩ := h y hy (i + j) hi'
  refine ⟨v, ?_, hlv⟩
  rw [dropEnv_lookup j ρ _ (by omega), show i + 1 + j = i + j + 1 by omega]; exact hv

omit sv in
theorem ListsHold.append {L L' env : List VarId} {ρ : CekEnv} (h : ListsHold L env ρ)
    (h' : ListsHold L' env ρ) : ListsHold (L' ++ L) env ρ := by
  intro y hy i hi
  simp only [List.contains_append, Bool.or_eq_true] at hy
  rcases hy with hy | hy
  · exact h' y hy i hi
  · exact h y hy i hi

theorem KnownFacts.extend {Γ : List (VarId × Expr)} {L env : List VarId} {ρ : CekEnv} {x : VarId}
    (w : CekValue) (h : KnownFacts Γ L env ρ) (hb : NamesBound L env)
    (hx : (envLookupT env x).isNone = true) (hnone : Γ.find? (fun e => e.1 == x) = none) :
    KnownFacts Γ L (x :: env) (ρ.extend w) :=
  ⟨FactsHold.extend w h.1 hnone, h.2.extend w hb hx⟩

/-! ## Basic properties -/

theorem KnownRel.refl (Γ : List (VarId × Expr)) (L : List VarId) (e : Expr) : KnownRel Γ L e e :=
  fun _ t _ _ _ _ _ h => ⟨t, h, FactRefines.refl _ _ _⟩

theorem KnownRel.of_factRel {Γ : List (VarId × Expr)} {L : List VarId} {e e' : Expr}
    (h : FactRel (fun _ => True) Produces Γ e e') : KnownRel Γ L e e' := by
  intro env t hd hf hk hs _ hlow
  obtain ⟨t', ht', hr⟩ := h env t (fun _ _ => trivial) hd hf hk hs hlow
  exact ⟨t', ht', hr.mono fun _ hF => hF.1⟩

theorem KnownRel.to_factRel {Γ : List (VarId × Expr)} {e e' : Expr}
    (h : KnownRel Γ [] e e') : FactRel (fun _ => True) Produces Γ e e' := by
  intro env t _ hd hf hk hs hlow
  obtain ⟨t', ht', hr⟩ := h env t hd hf hk hs (NamesBound.nil env) hlow
  exact ⟨t', ht', hr.mono fun ρ hF => ⟨hF, ListsHold.nil env ρ⟩⟩

theorem KnownRel.congr_left {Γ : List (VarId × Expr)} {L : List VarId} {e₀ e e' : Expr}
    (h : KnownRel Γ L e₀ e') (hlow : ∀ env, lowerTotalExpr env e = lowerTotalExpr env e₀)
    (hfresh : ∀ avoid, freshIn avoid e = freshIn avoid e₀) : KnownRel Γ L e e' := by
  intro env t hd hf hk hs hn ht
  rw [hfresh] at hf; rw [hlow] at ht
  exact h env t hd hf hk hs hn ht

theorem KnownRel.congr_right {Γ : List (VarId × Expr)} {L : List VarId} {e e₀ e' : Expr}
    (h : KnownRel Γ L e e₀) (hlow : ∀ env, lowerTotalExpr env e' = lowerTotalExpr env e₀) :
    KnownRel Γ L e e' := by
  intro env t hd hf hk hs hn ht
  obtain ⟨t', ht', hr⟩ := h env t hd hf hk hs hn ht
  exact ⟨t', by rw [hlow]; exact ht', hr⟩

/-! ## Congruences -/

theorem KnownRel.lam {Γ : List (VarId × Expr)} {L : List VarId} {x : VarId} {b b' : Expr}
    (h : KnownRel Γ L b b') : KnownRel Γ L (.Lam x b) (.Lam x b') := by
  intro env t hd hfresh hk hs hn hlow
  simp only [freshIn, Bool.and_eq_true] at hfresh
  obtain ⟨hd', hk', hs', hnone⟩ := enter_binder hd hk hs hfresh.1
  obtain ⟨tb, htb, rfl⟩ := lowerTotalExpr_lam_some hlow
  obtain ⟨tb', htb', hr⟩ := h (x :: env) tb hd' hfresh.2 hk' hs' (hn.cons x) htb
  refine ⟨.Lam 0 tb', by rw [MIR.lowerTotalExpr_lam, htb']; rfl, ?_⟩
  exact factRefines_lam 0 0 (by simpa using MIR.lowerTotalExpr_closedAt htb)
    (by simpa using MIR.lowerTotalExpr_closedAt htb')
    (fun ρ v hF => hF.extend v hn hfresh.1 hnone) (by simpa using hr)

theorem KnownRel.delay {Γ : List (VarId × Expr)} {L : List VarId} {b b' : Expr}
    (h : KnownRel Γ L b b') : KnownRel Γ L (.Delay b) (.Delay b') := by
  intro env t hd hfresh hk hs hn hlow
  simp only [freshIn] at hfresh
  obtain ⟨tb, htb, rfl⟩ := lowerTotalExpr_delay_some hlow
  obtain ⟨tb', htb', hr⟩ := h env tb hd hfresh hk hs hn htb
  refine ⟨.Delay tb', by rw [MIR.lowerTotalExpr_delay, htb']; rfl, ?_⟩
  exact factRefines_delay (MIR.lowerTotalExpr_closedAt htb) (MIR.lowerTotalExpr_closedAt htb') hr

theorem KnownRel.force {Γ : List (VarId × Expr)} {L : List VarId} {b b' : Expr}
    (h : KnownRel Γ L b b') : KnownRel Γ L (.Force b) (.Force b') := by
  intro env t hd hfresh hk hs hn hlow
  simp only [freshIn] at hfresh
  obtain ⟨tb, htb, rfl⟩ := lowerTotalExpr_force_some hlow
  obtain ⟨tb', htb', hr⟩ := h env tb hd hfresh hk hs hn htb
  exact ⟨.Force tb', by rw [MIR.lowerTotalExpr_force, htb']; rfl, factRefines_force hr⟩

theorem KnownRel.app {Γ : List (VarId × Expr)} {L : List VarId} {f f' a a' : Expr}
    (hf : KnownRel Γ L f f') (ha : KnownRel Γ L a a') :
    KnownRel Γ L (.App f a) (.App f' a') := by
  intro env t hd hfresh hk hs hn hlow
  simp only [freshIn, Bool.and_eq_true] at hfresh
  obtain ⟨tf, ta, htf, hta, rfl⟩ := lowerTotalExpr_app_some hlow
  obtain ⟨tf', htf', hrf⟩ := hf env tf hd hfresh.1 hk hs hn htf
  obtain ⟨ta', hta', hra⟩ := ha env ta hd hfresh.2 hk hs hn hta
  refine ⟨.Apply tf' ta', by rw [MIR.lowerTotalExpr_app, htf', hta']; rfl, ?_⟩
  exact factRefines_apply hrf hra (MIR.lowerTotalExpr_closedAt htf') (MIR.lowerTotalExpr_closedAt hta)

theorem KnownRel.list {Γ : List (VarId × Expr)} {L : List VarId} :
    ∀ {es es' : List Expr}, ListRel (KnownRel Γ L) es es' →
      ∀ env ts, EnvDistinct env → freshInList env es = true → KeysBound Γ env →
        FactsScoped Γ env → NamesBound L env → MIR.lowerTotalExprList env es = some ts →
        ∃ ts', MIR.lowerTotalExprList env es' = some ts' ∧
          ListRel (FactRefines env.length (KnownFacts Γ L env)) ts ts'
  | [], [], _, env, ts, _, _, _, _, _, h => by
    rw [MIR.lowerTotalExprList_nil] at h; cases h
    exact ⟨[], MIR.lowerTotalExprList_nil env, trivial⟩
  | [], _ :: _, h, _, _, _, _, _, _, _, _ => absurd h id
  | _ :: _, [], h, _, _, _, _, _, _, _, _ => absurd h id
  | e :: es, e' :: es', h, env, ts, hd, hfresh, hk, hs, hn, hlow => by
    simp only [freshInList, Bool.and_eq_true] at hfresh
    rw [MIR.lowerTotalExprList_cons] at hlow
    cases he : lowerTotalExpr env e with
    | none => rw [he] at hlow; cases hlow
    | some te =>
      cases hes : MIR.lowerTotalExprList env es with
      | none => rw [he, hes] at hlow; cases hlow
      | some tes =>
        rw [he, hes] at hlow; cases hlow
        obtain ⟨te', hte', hr⟩ := h.1 env te hd hfresh.1 hk hs hn he
        obtain ⟨tes', htes', hrs⟩ := KnownRel.list h.2 env tes hd hfresh.2 hk hs hn hes
        refine ⟨te' :: tes', by rw [MIR.lowerTotalExprList_cons, hte', htes']; rfl, hr, hrs⟩

theorem KnownRel.constr {Γ : List (VarId × Expr)} {L : List VarId} {tag : Nat} {es es' : List Expr}
    (h : ListRel (KnownRel Γ L) es es') : KnownRel Γ L (.Constr tag es) (.Constr tag es') := by
  intro env t hd hfresh hk hs hn hlow
  simp only [freshIn] at hfresh
  rw [MIR.lowerTotalExpr_constr_of_list] at hlow
  cases hes : MIR.lowerTotalExprList env es with
  | none => rw [hes] at hlow; cases hlow
  | some ts =>
    rw [hes] at hlow; cases hlow
    obtain ⟨ts', hts', hr⟩ := KnownRel.list h env ts hd hfresh hk hs hn hes
    refine ⟨.Constr tag ts', by rw [MIR.lowerTotalExpr_constr_of_list, hts']; rfl, ?_⟩
    exact factRefines_constr hr (lowerTotalExprList_closedAtList hes)
      (lowerTotalExprList_closedAtList hts')

theorem KnownRel.case {Γ : List (VarId × Expr)} {L : List VarId} {s s' : Expr}
    {alts alts' : List Expr} (hs : KnownRel Γ L s s') (halts : ListRel (KnownRel Γ L) alts alts') :
    KnownRel Γ L (.Case s alts) (.Case s' alts') := by
  intro env t hd hfresh hk hsc hn hlow
  simp only [freshIn, Bool.and_eq_true] at hfresh
  obtain ⟨ts, talts, hts, htalts, rfl⟩ := lowerTotalExpr_case_some hlow
  obtain ⟨ts', hts', hr⟩ := hs env ts hd hfresh.1 hk hsc hn hts
  obtain ⟨talts', htalts', hra⟩ := KnownRel.list halts env talts hd hfresh.2 hk hsc hn htalts
  refine ⟨.Case ts' talts', by rw [MIR.lowerTotalExpr_case_of_list, hts', htalts']; rfl, ?_⟩
  exact factRefines_case hr hra (MIR.lowerTotalExpr_closedAt hts')
    (lowerTotalExprList_closedAtList htalts)

theorem listRel_known_attach_map {Γ : List (VarId × Expr)} {L : List VarId}
    (children : List Expr) (f : Expr → Expr) (h : ∀ c ∈ children, KnownRel Γ L c (f c)) :
    ListRel (KnownRel Γ L) children (children.attach.map fun ⟨c, _⟩ => f c) := by
  induction children with
  | nil => trivial
  | cons c cs ih =>
    simp only [List.attach_cons, List.map_cons, List.map_map]
    refine ⟨h c (.head _), ?_⟩
    have := ih (fun c' hc' => h c' (.tail _ hc'))
    simpa [Function.comp_def] using this

theorem KnownRel.fix_lam {Γ : List (VarId × Expr)} {L : List VarId} {f x : VarId} {b b' : Expr}
    (h : KnownRel Γ L b b') : KnownRel Γ L (.Fix f (.Lam x b)) (.Fix f (.Lam x b')) := by
  intro env t hd hfresh hk hsc hn hlow
  simp only [freshIn, Bool.and_eq_true] at hfresh
  obtain ⟨hf, hx, hb⟩ := hfresh
  let s : VarId := ⟨envMax env + maxUidExpr b + maxUidExpr (expandFix b) +
    maxUidExpr (expandFix b') + f.uid + x.uid + 1, .source, "s"⟩
  have hs_env : envLookupT env s = none := envLookupT_none_of_gt env s (by simp [s]; omega)
  have hs_b : (freeVars (expandFix b)).contains s = false := maxUidExpr_fresh _ _ (by simp [s]; omega)
  have hs_b' : (freeVars (expandFix b')).contains s = false := maxUidExpr_fresh _ _ (by simp [s]; omega)
  rw [lowerTotalExpr_fix_lam_with_fresh env f x b s hs_b] at hlow
  cases htb : lowerTotal (x :: f :: s :: env) (expandFix b) with
  | none => rw [htb] at hlow; cases hlow
  | some tb =>
    rw [htb] at hlow; cases hlow
    have hfs : (f == s) = false := by rw [VarId.beq_false_iff]; right; simp [s]; omega
    have hxs : (x == s) = false := by rw [VarId.beq_false_iff]; right; simp [s]; omega
    have hf' : (envLookupT (s :: env) f).isNone = true := by
      rw [envLookupT_cons]
      have : (s == f) = false := by
        cases h : (s == f)
        · rfl
        · exact absurd (varId_beq_symm h) (by simp [hfs])
      simp only [this, Bool.false_eq_true, if_false]; simpa using hf
    have hx' : (envLookupT (f :: s :: env) x).isNone = true := by
      have hsx : (s == x) = false := by
        cases h : (s == x)
        · rfl
        · exact absurd (varId_beq_symm h) (by simp [hxs])
      have hx2 := hx
      rw [envLookupT_cons] at hx2 ⊢
      split
      · rename_i hfx; simp [hfx] at hx2
      · rename_i hfx
        simp only [hfx, Bool.false_eq_true, if_false, Option.isNone_map] at hx2 ⊢
        rw [envLookupT_cons]
        simp only [hsx, Bool.false_eq_true, if_false, Option.isNone_map]; exact hx2
    have hs_none : (envLookupT env s).isNone = true := by simp [hs_env]
    obtain ⟨hd₁, hk₁, hs₁, hn₁⟩ := enter_binder (x := s) hd hk hsc hs_none
    obtain ⟨hd₂, hk₂, hs₂, hn₂⟩ := enter_binder hd₁ hk₁ hs₁ hf'
    obtain ⟨hd₃, hk₃, hs₃, hn₃⟩ := enter_binder hd₂ hk₂ hs₂ hx'
    have hN₁ := hn.cons s
    have hN₂ := hN₁.cons f
    have hN₃ := hN₂.cons x
    have hfresh₃ : freshIn (x :: f :: s :: env) b = true := by
      refine freshIn_avoids b hb ?_
      intro y hy
      rw [envLookupT_cons] at hy ⊢
      split
      · simp
      · rename_i hxy
        simp only [hxy, Bool.false_eq_true, if_false, Option.isSome_map] at hy ⊢
        rw [envLookupT_cons] at hy ⊢
        split
        · simp
        · rename_i hfy
          simp only [hfy, Bool.false_eq_true, if_false, Option.isSome_map] at hy ⊢
          rw [envLookupT_cons] at hy
          split at hy
          · rename_i hsy
            right
            have := (VarId.beq_true_iff s y).mp hsy
            simp [s] at this; omega
          · left; simpa using hy
    obtain ⟨tb', htb', hr⟩ := h (x :: f :: s :: env) tb hd₃ hfresh₃ hk₃ hs₃ hN₃ htb
    refine ⟨fixLamWrapUplc tb', ?_, ?_⟩
    · rw [lowerTotalExpr_fix_lam_with_fresh env f x b' s hs_b']
      change (lowerTotalExpr (x :: f :: s :: env) b').map fixLamWrapUplc = _
      rw [htb']; rfl
    · have cb := MIR.lowerTotalExpr_closedAt htb
      have cb' := MIR.lowerTotalExpr_closedAt htb'
      simp only [List.length_cons] at cb cb'
      apply fixLamWrapUplc_factRefines (by simpa [Nat.add_assoc] using cb)
        (by simpa [Nat.add_assoc] using cb')
      simp only [List.length_cons] at hr
      apply hr.mono
      rintro ρ ⟨ρ₀, v₁, v₂, v₃, hF, rfl⟩
      exact ((hF.extend v₁ hn hs_none hn₁).extend v₂ hN₁ hf' hn₂).extend v₃ hN₂ hx' hn₃


/-! ## Bindings -/

theorem KnownRel.let_single {Γ : List (VarId × Expr)} {L : List VarId} {x : VarId}
    {r r' b b' : Expr} {er : Bool} (rf : Expr) (hrf : rf = r ∨ rf = r')
    (hr : KnownRel Γ L r r') (hb : KnownRel ((x, rf) :: Γ) L b b') :
    KnownRel Γ L (.Let [(x, r, er)] b) (.Let [(x, r', er)] b') := by
  intro env t hd hfresh hk hsc hn hlow
  rw [freshIn_let_single] at hfresh
  simp only [Bool.and_eq_true] at hfresh
  obtain ⟨⟨hfr, hx⟩, hfb⟩ := hfresh
  obtain ⟨tr, tb, htr, htb, rfl⟩ := lowerTotalExpr_let_single_some hlow
  obtain ⟨tr', htr', hrr⟩ := hr env tr hd hfr hk hsc hn htr
  have hrf_low : ∃ trf, lowerTotalExpr env rf = some trf ∧ (trf = tr ∨ trf = tr') := by
    rcases hrf with rfl | rfl
    · exact ⟨tr, htr, .inl rfl⟩
    · exact ⟨tr', htr', .inr rfl⟩
  obtain ⟨trf, htrf, htrf_eq⟩ := hrf_low
  have hk' : KeysBound ((x, rf) :: Γ) (x :: env) := by
    intro entry hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · simp [envLookupT_cons, varId_beq_self]
    · exact hk.cons x entry hmem
  have hs' : FactsScoped ((x, rf) :: Γ) (x :: env) := hsc.push (by simp [htrf])
  obtain ⟨tb', htb', hrb⟩ := hb (x :: env) tb (hd.cons hx) hfb hk' hs' (hn.cons x) htb
  refine ⟨.Apply (.Lam 0 tb') tr', by rw [lowerTotalExpr_let_single, htr', htb']; rfl, ?_⟩
  have closedTr := MIR.lowerTotalExpr_closedAt htr
  have closedTr' := MIR.lowerTotalExpr_closedAt htr'
  have closedTb := MIR.lowerTotalExpr_closedAt htb
  have closedTb' := MIR.lowerTotalExpr_closedAt htb'
  simp only [List.length_cons] at closedTb closedTb' hrb
  have body : ∀ tr₀, lowerTotalExpr env rf = some tr₀ → closedAt env.length tr₀ = true →
      FactRefines env.length (KnownFacts Γ L env) (.Apply (.Lam 0 tb) tr₀) (.Apply (.Lam 0 tb') tr₀) := by
    intro tr₀ htr₀ closed₀
    apply factRefines_let 0 0 closed₀ _ hrb
    intro ρ v hF hv
    exact ⟨FactsHold.push hF.1 ⟨tr₀, htr₀, hv⟩, hF.2.extend v hn hx⟩
  have rhs : ∀ tb₀, closedAt (env.length + 1) tb₀ = true →
      FactRefines env.length (KnownFacts Γ L env) (.Apply (.Lam 0 tb₀) tr) (.Apply (.Lam 0 tb₀) tr') :=
    fun tb₀ c₀ => factRefines_apply (FactRefines.refl _ _ _) hrr (by simp [closedAt, c₀]) closedTr
  rcases htrf_eq with rfl | rfl
  · exact (body trf htrf closedTr).trans (rhs tb' closedTb')
  · exact (rhs tb closedTb).trans (body trf htrf closedTr')

end Moist.Verified.ShapeFacts
