import Moist.MIR.Optimize.Inline
import Moist.MIR.LowerTotal
import Moist.Verified.InlineSoundness.SubstCommute
import Moist.Verified.InlineSoundness.WellScoped

/-! # Preservation theorems for the inlining pass -/

namespace Moist.Verified.InlineSoundness.Preservation

open Moist.MIR (Expr VarId VarSet freeVars freeVarsList freeVarsLet
  inlinePass inlinePassList inlineBindings inlineLetBindings inlineLetGo
  betaReduce substInBindings subst substList substLet expandFix
  shouldInline countOccurrences wellScoped
  rename renameList renameLet renameBinds freshVar)
open Moist.MIR.VarSet (contains_union_left contains_union_right)
open Moist.Verified.InlineSoundness.SubstCommute
  (noCaptureFrom noCaptureFromList noCaptureFromLet
   noCaptureFrom_lam noCaptureFrom_fix noCaptureFrom_app
   noCaptureFrom_force noCaptureFrom_delay
   noCaptureFrom_constr noCaptureFrom_case noCaptureFrom_let
   noCaptureFromList_cons noCaptureFromLet_cons
   freeVars_subst_not_contains)
open Moist.Verified.InlineSoundness.WellScoped
  (noCaptureFrom_mono noCaptureFrom_subst noCaptureFrom_union
   wellScoped_noCaptureFrom wellScoped_let_noCaptureFrom wellScoped_let_peel
   wellScoped_sub_lam wellScoped_sub_fix wellScoped_sub_app
   wellScoped_sub_force wellScoped_sub_delay wellScoped_sub_constr
   wellScoped_sub_case wellScoped_sub_let wellScoped_app_lam_noCaptureFrom
   wellScoped_let_cross_nc)

abbrev NC (fv : VarSet) (e : Expr) : Prop := noCaptureFrom fv e = true
abbrev FVSub (fv : VarSet) (e : Expr) : Prop :=
  ∀ w, (freeVars e).contains w = true → fv.contains w = true

private theorem fv_subst_bound (v : VarId) (rhs e : Expr) (s : Moist.MIR.FreshState)
    (h_nc : noCaptureFrom (freeVars rhs) e = true)
    (w : VarId) (hw : (freeVars (subst v rhs e s).1).contains w = true) :
    (freeVars e).contains w = true ∨ (freeVars rhs).contains w = true := by
  cases h1 : (freeVars e).contains w with
  | true => exact Or.inl rfl
  | false =>
    cases h2 : (freeVars rhs).contains w with
    | true => exact Or.inr rfl
    | false =>
      have := freeVars_subst_not_contains v rhs e w s h_nc h1 h2
      exact absurd hw (by simp [this])

theorem nc_subst_via_bound (v : VarId) (rhs target e_src : Expr)
    (s_target s_src : Moist.MIR.FreshState)
    (h_nc_1 : noCaptureFrom (freeVars e_src) target = true)
    (h_nc_2 : noCaptureFrom (freeVars rhs) target = true)
    (h_nc_1r : noCaptureFrom (freeVars e_src) rhs = true)
    (h_nc_2r : noCaptureFrom (freeVars rhs) rhs = true)
    (h_no_rename_t : noCaptureFrom (freeVars rhs) target = true)
    (h_no_rename_s : noCaptureFrom (freeVars rhs) e_src = true) :
    noCaptureFrom (freeVars (subst v rhs e_src s_src).1)
      (subst v rhs target s_target).1 = true := by
  apply noCaptureFrom_mono ((freeVars e_src).union (freeVars rhs))
  · exact noCaptureFrom_subst _ v rhs target s_target
      (noCaptureFrom_union _ _ target h_nc_1 h_nc_2)
      (noCaptureFrom_union _ _ rhs h_nc_1r h_nc_2r)
      h_no_rename_t
  · intro w hw
    rcases fv_subst_bound v rhs e_src s_src h_no_rename_s w hw with h | h
    · exact contains_union_left _ _ _ h
    · exact contains_union_right _ _ _ h

--------------------------------------------------------------------------------
-- PairwiseNC: condition 3 uses plain freeVars (not expandFix)
--------------------------------------------------------------------------------

def PairwiseNC : List (VarId × Expr × Bool) → Expr → Prop
  | [], _ => True
  | (_, rhs, _) :: rest, body =>
    noCaptureFrom (freeVars rhs) body = true ∧
    rest.all (fun b => noCaptureFrom (freeVars rhs) b.2.1) = true ∧
    rest.all (fun b => !(freeVars rhs).contains b.1) = true ∧
    PairwiseNC rest body

theorem pairwiseNC_tail {v : VarId} {rhs : Expr} {er : Bool}
    {rest : List (VarId × Expr × Bool)} {body : Expr}
    (h : PairwiseNC ((v, rhs, er) :: rest) body) :
    PairwiseNC rest body := h.2.2.2

theorem pairwiseNC_expandFix {v : VarId} {rhs : Expr} {er : Bool}
    {rest : List (VarId × Expr × Bool)} {body : Expr}
    (h : PairwiseNC ((v, rhs, er) :: rest) body) :
    rest.all (fun b => !(freeVars (expandFix rhs)).contains b.1) = true := by
  have ⟨_, _, h_names, _⟩ := h
  rw [List.all_eq_true] at h_names ⊢
  intro b hb; simp only [Bool.not_eq_true'] at *
  exact Moist.MIR.expandFix_freeVars_not_contains rhs b.1 (h_names b hb)

private theorem noCaptureFromLet_implies_names_local (fv : VarSet)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (h : noCaptureFromLet fv binds body = true) :
    ∀ b ∈ binds, fv.contains b.1 = false := by
  induction binds with
  | nil => intro b hb; exact absurd hb (by simp)
  | cons bd rest ih =>
    intro b hb; rcases List.mem_cons.mp hb with rfl | hb
    · exact (noCaptureFromLet_cons h).1
    · exact ih (noCaptureFromLet_cons h).2.2 b hb

theorem pairwiseNC_of_wellScoped
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (h : wellScoped (.Let binds body) = true) :
    PairwiseNC binds body := by
  induction binds with
  | nil => exact True.intro
  | cons bd rest ih =>
    obtain ⟨v, rhs, er⟩ := bd
    have ⟨hnr_body, hnr_rest_all, _⟩ := wellScoped_let_noCaptureFrom h
    have hrest := (wellScoped_let_peel h).2
    have hnc_let := noCaptureFrom_let (wellScoped_noCaptureFrom h)
    simp only [Moist.MIR.freeVars] at hnc_let
    have hnames := noCaptureFromLet_implies_names_local _ _ body hnc_let
    refine ⟨hnr_body, hnr_rest_all, ?_, ih hrest⟩
    rw [List.all_eq_true]; intro b hb; simp only [Bool.not_eq_true']
    have hfv := hnames b (List.mem_cons_of_mem _ hb)
    rw [Moist.MIR.freeVarsLet.eq_2] at hfv
    exact (Moist.MIR.VarSet.union_not_contains' _ _ _ hfv).1

--------------------------------------------------------------------------------
-- PairwiseNC preservation through substitution
--------------------------------------------------------------------------------

private theorem substInBindings_all_nc (v : VarId) (rhs e_src : Expr)
    (rest : List (VarId × Expr × Bool)) (s_src s₀ : Moist.MIR.FreshState)
    (h_nc_src : ∀ b ∈ rest, noCaptureFrom (freeVars e_src) b.2.1 = true)
    (h_nc_rhs_rest : ∀ b ∈ rest, noCaptureFrom (freeVars rhs) b.2.1 = true)
    (h_rev_src : noCaptureFrom (freeVars e_src) rhs = true)
    (h_nc_rhs_self : noCaptureFrom (freeVars rhs) rhs = true)
    (h_no_rename_src : noCaptureFrom (freeVars rhs) e_src = true) :
    (substInBindings v rhs rest s₀).1.val.all
      (fun b => noCaptureFrom (freeVars (subst v rhs e_src s_src).1) b.2.1) = true := by
  rw [List.all_eq_true]
  intro b hb
  induction rest generalizing s₀ with
  | nil => simp only [substInBindings, pure, StateT.pure] at hb; exact absurd hb (by simp)
  | cons bd rest_tail ih =>
    obtain ⟨w', rhs', er'⟩ := bd
    simp only [substInBindings, bind, StateT.bind] at hb
    rcases List.mem_cons.mp hb with rfl | hb_tail
    · exact nc_subst_via_bound v rhs rhs' e_src _ s_src
        (h_nc_src (w', rhs', er') (List.mem_cons_self ..))
        (h_nc_rhs_rest (w', rhs', er') (List.mem_cons_self ..))
        h_rev_src h_nc_rhs_self
        (h_nc_rhs_rest (w', rhs', er') (List.mem_cons_self ..))
        h_no_rename_src
    · exact ih _
               (fun b hb => h_nc_src b (List.mem_cons_of_mem _ hb))
               (fun b hb => h_nc_rhs_rest b (List.mem_cons_of_mem _ hb))
               hb_tail

private theorem substInBindings_all_name_fresh (v : VarId) (rhs e_src : Expr)
    (rest : List (VarId × Expr × Bool)) (s_src s₀ : Moist.MIR.FreshState)
    (h_names_src : ∀ b ∈ rest, (freeVars e_src).contains b.1 = false)
    (h_names_rhs : ∀ b ∈ rest, (freeVars rhs).contains b.1 = false)
    (h_no_rename : noCaptureFrom (freeVars rhs) e_src = true) :
    (substInBindings v rhs rest s₀).1.val.all
      (fun b => !(freeVars (subst v rhs e_src s_src).1).contains b.1) = true := by
  rw [List.all_eq_true]
  intro b hb; simp only [Bool.not_eq_true']
  induction rest generalizing s₀ with
  | nil => simp only [substInBindings, pure, StateT.pure] at hb; exact absurd hb (by simp)
  | cons bd rest_tail ih =>
    obtain ⟨w', rhs', er'⟩ := bd
    simp only [substInBindings, bind, StateT.bind] at hb
    rcases List.mem_cons.mp hb with rfl | hb_tail
    · exact freeVars_subst_not_contains v rhs e_src w' s_src h_no_rename
        (h_names_src (w', rhs', er') (List.mem_cons_self ..))
        (h_names_rhs (w', rhs', er') (List.mem_cons_self ..))
    · exact ih _
               (fun b hb => h_names_src b (List.mem_cons_of_mem _ hb))
               (fun b hb => h_names_rhs b (List.mem_cons_of_mem _ hb))
               hb_tail

private theorem pairwiseNC_subst_aux (v : VarId) (rhs : Expr)
    (rest : List (VarId × Expr × Bool)) (body : Expr)
    (s s₀ : Moist.MIR.FreshState)
    (h_nc_body : noCaptureFrom (freeVars rhs) body = true)
    (h_nc_rest : ∀ b ∈ rest, noCaptureFrom (freeVars rhs) b.2.1 = true)
    (h_names : ∀ b ∈ rest, (freeVars rhs).contains b.1 = false)
    (hpc_rest : PairwiseNC rest body)
    (h_nc_rhs_self : noCaptureFrom (freeVars rhs) rhs = true)
    (h_nc_rhs_rev : ∀ b ∈ rest, noCaptureFrom (freeVars b.2.1) rhs = true) :
    PairwiseNC
      (substInBindings v rhs rest s₀).1.val
      (subst v rhs body s).1 := by
  induction rest generalizing s₀ with
  | nil => simp only [substInBindings, pure, StateT.pure]; exact True.intro
  | cons bd rest_tail ih =>
    obtain ⟨w, rhs_w, er_w⟩ := bd
    simp only [substInBindings, bind, StateT.bind]
    have h_nc_rhs_w := h_nc_rest (w, rhs_w, er_w) (List.mem_cons_self ..)
    have h_rev_w := h_nc_rhs_rev (w, rhs_w, er_w) (List.mem_cons_self ..)
    obtain ⟨h_nc_body_w, h_nc_rest_w, h_names_w, hpc_tail⟩ := hpc_rest
    rw [List.all_eq_true] at h_nc_rest_w h_names_w
    refine ⟨?_, ?_, ?_, ih (subst v rhs rhs_w s₀).2
      (fun b hb => h_nc_rest b (List.mem_cons_of_mem _ hb))
      (fun b hb => h_names b (List.mem_cons_of_mem _ hb))
      hpc_tail
      (fun b hb => h_nc_rhs_rev b (List.mem_cons_of_mem _ hb))⟩
    · exact nc_subst_via_bound v rhs body rhs_w s s₀
        h_nc_body_w h_nc_body h_rev_w h_nc_rhs_self h_nc_body h_nc_rhs_w
    · exact substInBindings_all_nc v rhs rhs_w rest_tail s₀ _
        h_nc_rest_w
        (fun b hb => h_nc_rest b (List.mem_cons_of_mem _ hb))
        h_rev_w h_nc_rhs_self h_nc_rhs_w
    · exact substInBindings_all_name_fresh v rhs rhs_w rest_tail s₀ _
        (fun b hb => by have := h_names_w b hb; simp only [Bool.not_eq_true'] at this; exact this)
        (fun b hb => h_names b (List.mem_cons_of_mem _ hb))
        h_nc_rhs_w

theorem pairwiseNC_subst (v : VarId) (rhs : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr)
    (s s₀ : Moist.MIR.FreshState)
    (hpc : PairwiseNC ((v, rhs, er) :: rest) body)
    (h_nc_rhs_self : noCaptureFrom (freeVars rhs) rhs = true)
    (h_nc_rhs_rev : ∀ b ∈ rest, noCaptureFrom (freeVars b.2.1) rhs = true) :
    PairwiseNC
      (substInBindings v rhs rest s₀).1.val
      (subst v rhs body s).1 := by
  obtain ⟨h_nc_body, h_nc_rest_all, h_names_all, hpc_rest⟩ := hpc
  rw [List.all_eq_true] at h_nc_rest_all h_names_all
  exact pairwiseNC_subst_aux v rhs rest body s s₀
    h_nc_body h_nc_rest_all
    (fun b hb => by have := h_names_all b hb; simp only [Bool.not_eq_true'] at this; exact this)
    hpc_rest h_nc_rhs_self h_nc_rhs_rev

--------------------------------------------------------------------------------
-- Free variables never increase through inlinePass
--------------------------------------------------------------------------------

-- Local helper: union-contains elimination
private theorem contains_union_elim {s₁ s₂ : Moist.MIR.VarSet} {w : VarId}
    (h : (s₁.union s₂).contains w = true) :
    s₁.contains w = true ∨ s₂.contains w = true := by
  cases h₁ : s₁.contains w
  · cases h₂ : s₂.contains w
    · exact absurd h (by rw [Moist.MIR.VarSet.union_not_contains_fwd s₁ s₂ w h₁ h₂]; decide)
    · exact Or.inr rfl
  · exact Or.inl rfl

-- Local helper: erase preserves membership (monotone backward)
private theorem contains_of_contains_erase {s : Moist.MIR.VarSet} {v w : VarId}
    (h : (s.erase v).contains w = true) : s.contains w = true := by
  cases hsx : s.contains w
  · exact absurd h (by rw [Moist.MIR.VarSet.erase_not_contains_fwd s v w hsx]; decide)
  · rfl

-- Local VarId beq helpers
private theorem varid_beq_symm {a b : VarId} (h : (a == b) = true) : (b == a) = true := by
  rw [Moist.MIR.VarId.beq_true_iff] at h ⊢
  exact ⟨h.1.symm, h.2.symm⟩

private theorem varid_beq_trans {a b c : VarId}
    (h1 : (a == b) = true) (h2 : (b == c) = true) : (a == c) = true := by
  rw [Moist.MIR.VarId.beq_true_iff] at h1 h2 ⊢
  exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

-- Local helper: if v == w then (s.erase v).contains w = false
private theorem erase_contains_beq_false (s : Moist.MIR.VarSet) (v w : VarId)
    (hvw : (v == w) = true) : (s.erase v).contains w = false := by
  cases hcw : (s.erase v).contains w with
  | false => rfl
  | true =>
    -- (s.erase v).contains w = true means there exists a ∈ s.data with a != v and a == w
    -- but v == w, so a == w and w == v (by beq_symm) gives a == v (by beq_trans), contradiction
    have h_self := Moist.MIR.VarSet.contains_erase_self s v
    -- w == v by symmetry
    have hwv := varid_beq_symm hvw
    -- s.erase v contains w, and w == v, so s.erase v contains v by contains_of_beq-like reasoning
    -- But contains_erase_self says it doesn't. Contradiction.
    simp only [Moist.MIR.VarSet.erase, Moist.MIR.VarSet.contains, Array.any_filter] at hcw h_self
    rw [Array.any_eq_true] at hcw
    obtain ⟨i, hi, hprop⟩ := hcw
    rw [Bool.and_eq_true] at hprop
    obtain ⟨hne_v, haw⟩ := hprop
    -- haw: s.data[i] == w = true, hvw: v == w = true
    -- so s.data[i] == v = true by transitivity with beq_symm
    have h_av : (s.data[i] == v) = true := varid_beq_trans haw (varid_beq_symm hvw)
    -- but hne_v: s.data[i] != v = true, i.e. !(s.data[i] == v) = true
    simp [bne] at hne_v
    rw [h_av] at hne_v; exact Bool.noConfusion hne_v

-- Local helper: erase is monotone
private theorem erase_mono {s₁ s₂ : Moist.MIR.VarSet} {v : VarId}
    (hmono : ∀ w, s₁.contains w = true → s₂.contains w = true)
    (w : VarId) (h : (s₁.erase v).contains w = true) :
    (s₂.erase v).contains w = true := by
  have hw : s₁.contains w = true := contains_of_contains_erase h
  have hne : (v == w) = false := by
    cases hvw : (v == w) with
    | false => rfl
    | true =>
      rw [erase_contains_beq_false s₁ v w hvw] at h
      exact Bool.noConfusion h
  exact Moist.MIR.VarSet.contains_erase_ne s₂ v w hne (hmono w hw)

-- Local helper: union is monotone
private theorem union_mono {s₁ s₂ t₁ t₂ : Moist.MIR.VarSet}
    (h₁ : ∀ w, s₁.contains w = true → t₁.contains w = true)
    (h₂ : ∀ w, s₂.contains w = true → t₂.contains w = true)
    (w : VarId) (h : (s₁.union s₂).contains w = true) :
    (t₁.union t₂).contains w = true := by
  rcases contains_union_elim h with h | h
  · exact contains_union_left _ _ _ (h₁ w h)
  · exact contains_union_right _ _ _ (h₂ w h)

--------------------------------------------------------------------------------
-- freeVars(rename old new e) ⊆ (freeVars e \ {old}) ∪ {new}
-- Auxiliary: w ∈ freeVars e → (old == w) = false → w ∈ (freeVars e).erase old
--------------------------------------------------------------------------------

private theorem erase_contains_ne_of_contains {s : Moist.MIR.VarSet} {v w : VarId}
    (h : s.contains w = true) (hne : (v == w) = false) : (s.erase v).contains w = true :=
  Moist.MIR.VarSet.contains_erase_ne s v w hne h

set_option maxHeartbeats 800000 in
mutual
private theorem freeVars_rename_bound_core (old new_ : VarId) (e : Expr) (w : VarId)
    (hw : (freeVars (rename old new_ e)).contains w = true) :
    ((freeVars e).erase old).contains w = true ∨ (w == new_) = true := by
  match e with
  | .Var x =>
    have h_ren : rename old new_ (.Var x) = if x == old then .Var new_ else .Var x := by
      simp only [rename]
    rw [h_ren] at hw
    split at hw
    · -- x == old: result = .Var new_
      rw [Moist.MIR.freeVars.eq_1, Moist.MIR.VarSet.singleton_contains'] at hw
      exact Or.inr (varid_beq_symm hw)
    · -- x != old: result = .Var x
      rename_i hxo
      rw [Moist.MIR.freeVars.eq_1, Moist.MIR.VarSet.singleton_contains'] at hw
      have hne_ow : (old == w) = false := by
        cases h : (old == w); rfl
        exact absurd (varid_beq_trans hw (varid_beq_symm h)) hxo
      exact Or.inl (erase_contains_ne_of_contains
        (by rw [Moist.MIR.freeVars.eq_1, Moist.MIR.VarSet.singleton_contains']; exact hw) hne_ow)
  | .Lit _ | .Builtin _ | .Error =>
    simp only [rename, freeVars] at hw
    exact absurd hw (by simp [Moist.MIR.VarSet.contains_empty])
  | .Lam x body =>
    have h_ren : rename old new_ (.Lam x body) =
        if x == old then .Lam x body else .Lam x (rename old new_ body) := by
      simp only [rename]
    rw [h_ren] at hw
    split at hw
    · -- x == old: body untouched
      rename_i hxo
      -- hw : (freeVars (.Lam x body)).contains w = true
      -- = ((freeVars body).erase x).contains w = true
      -- Need: ((freeVars body).erase x).erase old .contains w
      -- Since x == old, erase x already does what erase old would do
      rw [Moist.MIR.freeVars.eq_5] at hw ⊢
      have hne : (old == w) = false := by
        cases h' : (old == w); rfl
        rw [erase_contains_beq_false _ x w (varid_beq_trans hxo h')] at hw
        exact Bool.noConfusion hw
      exact Or.inl (erase_contains_ne_of_contains hw hne)
    · -- x != old
      rw [Moist.MIR.freeVars.eq_5] at hw ⊢
      have hw_body := contains_of_contains_erase hw
      have hne_xw : (x == w) = false := by
        cases h : (x == w); rfl
        rw [erase_contains_beq_false _ x w h] at hw; exact Bool.noConfusion hw
      rcases freeVars_rename_bound_core old new_ body w hw_body with h | h
      · -- h : ((freeVars body).erase old).contains w = true
        -- Need: ((freeVars body).erase x).erase old .contains w
        -- From h: (freeVars body).contains w and (old == w) = false
        have hne_ow : (old == w) = false := by
          cases h' : (old == w); rfl
          rw [erase_contains_beq_false _ old w h'] at h; exact Bool.noConfusion h
        exact Or.inl (erase_contains_ne_of_contains
          (erase_contains_ne_of_contains (contains_of_contains_erase h) hne_xw) hne_ow)
      · exact Or.inr h
  | .Fix f body =>
    have h_ren : rename old new_ (.Fix f body) =
        if f == old then .Fix f body else .Fix f (rename old new_ body) := by
      simp only [rename]
    rw [h_ren] at hw
    split at hw
    · rename_i hfo
      rw [Moist.MIR.freeVars.eq_6] at hw ⊢
      have hne : (old == w) = false := by
        cases h' : (old == w); rfl
        rw [erase_contains_beq_false _ f w (varid_beq_trans hfo h')] at hw
        exact Bool.noConfusion hw
      exact Or.inl (erase_contains_ne_of_contains hw hne)
    · rw [Moist.MIR.freeVars.eq_6] at hw ⊢
      have hw_body := contains_of_contains_erase hw
      have hne_fw : (f == w) = false := by
        cases h : (f == w); rfl
        rw [erase_contains_beq_false _ f w h] at hw; exact Bool.noConfusion hw
      rcases freeVars_rename_bound_core old new_ body w hw_body with h | h
      · have hne_ow : (old == w) = false := by
          cases h' : (old == w); rfl
          rw [erase_contains_beq_false _ old w h'] at h; exact Bool.noConfusion h
        exact Or.inl (erase_contains_ne_of_contains
          (erase_contains_ne_of_contains (contains_of_contains_erase h) hne_fw) hne_ow)
      · exact Or.inr h
  | .App f x =>
    have h_ren : rename old new_ (.App f x) =
        .App (rename old new_ f) (rename old new_ x) := by simp only [rename]
    rw [h_ren, Moist.MIR.freeVars.eq_7] at hw; rw [Moist.MIR.freeVars.eq_7]
    rcases contains_union_elim hw with h | h
    · rcases freeVars_rename_bound_core old new_ f w h with h | h
      · exact Or.inl (erase_mono (fun w h => contains_union_left _ _ _ h) w h)
      · exact Or.inr h
    · rcases freeVars_rename_bound_core old new_ x w h with h | h
      · exact Or.inl (erase_mono (fun w h => contains_union_right _ _ _ h) w h)
      · exact Or.inr h
  | .Force e' =>
    have h_ren : rename old new_ (.Force e') = .Force (rename old new_ e') := by
      simp only [rename]
    rw [h_ren, Moist.MIR.freeVars.eq_8] at hw; rw [Moist.MIR.freeVars.eq_8]
    exact freeVars_rename_bound_core old new_ e' w hw
  | .Delay e' =>
    have h_ren : rename old new_ (.Delay e') = .Delay (rename old new_ e') := by
      simp only [rename]
    rw [h_ren, Moist.MIR.freeVars.eq_9] at hw; rw [Moist.MIR.freeVars.eq_9]
    exact freeVars_rename_bound_core old new_ e' w hw
  | .Constr tag args =>
    have h_ren : rename old new_ (.Constr tag args) = .Constr tag (renameList old new_ args) := by
      simp only [rename]
    rw [h_ren, Moist.MIR.freeVars.eq_10] at hw; rw [Moist.MIR.freeVars.eq_10]
    exact freeVarsList_rename_bound_core old new_ args w hw
  | .Case scrut alts =>
    have h_ren : rename old new_ (.Case scrut alts) =
        .Case (rename old new_ scrut) (renameList old new_ alts) := by
      simp only [rename]
    rw [h_ren, Moist.MIR.freeVars.eq_11] at hw; rw [Moist.MIR.freeVars.eq_11]
    rcases contains_union_elim hw with h | h
    · rcases freeVars_rename_bound_core old new_ scrut w h with h | h
      · exact Or.inl (erase_mono (fun w h => contains_union_left _ _ _ h) w h)
      · exact Or.inr h
    · rcases freeVarsList_rename_bound_core old new_ alts w h with h | h
      · exact Or.inl (erase_mono (fun w h => contains_union_right _ _ _ h) w h)
      · exact Or.inr h
  | .Let binds body =>
    rw [show rename old new_ (.Let binds body) =
        .Let (renameLet old new_ binds body).1 (renameLet old new_ binds body).2 from by
      unfold rename; exact Prod.casesOn (renameLet old new_ binds body) (fun _ _ => rfl),
      Moist.MIR.freeVars.eq_12] at hw; rw [Moist.MIR.freeVars.eq_12]
    exact freeVarsLet_rename_bound_core old new_ binds body w hw
termination_by sizeOf e

private theorem freeVarsList_rename_bound_core (old new_ : VarId) (es : List Expr) (w : VarId)
    (hw : (freeVarsList (renameList old new_ es)).contains w = true) :
    ((freeVarsList es).erase old).contains w = true ∨ (w == new_) = true := by
  match es with
  | [] =>
    have : renameList old new_ [] = [] := by simp only [renameList]
    rw [this, Moist.MIR.freeVarsList.eq_1] at hw
    exact absurd hw (by simp [Moist.MIR.VarSet.contains_empty])
  | e :: rest =>
    have h_ren : renameList old new_ (e :: rest) =
        rename old new_ e :: renameList old new_ rest := by simp only [renameList]
    rw [h_ren, Moist.MIR.freeVarsList.eq_2] at hw; rw [Moist.MIR.freeVarsList.eq_2]
    rcases contains_union_elim hw with h | h
    · rcases freeVars_rename_bound_core old new_ e w h with h | h
      · exact Or.inl (erase_mono (fun w h => contains_union_left _ _ _ h) w h)
      · exact Or.inr h
    · rcases freeVarsList_rename_bound_core old new_ rest w h with h | h
      · exact Or.inl (erase_mono (fun w h => contains_union_right _ _ _ h) w h)
      · exact Or.inr h
termination_by sizeOf es

private theorem freeVarsLet_rename_bound_core (old new_ : VarId)
    (binds : List (VarId × Expr × Bool)) (body : Expr) (w : VarId)
    (hw : (freeVarsLet (renameLet old new_ binds body).1
                       (renameLet old new_ binds body).2).contains w = true) :
    ((freeVarsLet binds body).erase old).contains w = true ∨ (w == new_) = true := by
  match binds with
  | [] =>
    have : renameLet old new_ [] body = ([], rename old new_ body) := by simp only [renameLet]
    rw [show (renameLet old new_ [] body).1 = [] from congrArg Prod.fst this,
        show (renameLet old new_ [] body).2 = rename old new_ body from congrArg Prod.snd this] at hw
    rw [Moist.MIR.freeVarsLet.eq_1] at hw ⊢
    exact freeVars_rename_bound_core old new_ body w hw
  | (x, rhs, er) :: rest =>
    by_cases hxo : (x == old) = true
    · -- x == old: rename stops
      have h_rl : (renameLet old new_ ((x, rhs, er) :: rest) body).1 =
          (x, rename old new_ rhs, er) :: rest := by
        simp only [renameLet, hxo, if_true]
      have h_rl2 : (renameLet old new_ ((x, rhs, er) :: rest) body).2 = body := by
        simp only [renameLet, hxo, if_true]
      rw [h_rl, h_rl2] at hw
      rw [Moist.MIR.freeVarsLet.eq_2] at hw ⊢
      rcases contains_union_elim hw with h | h
      · rcases freeVars_rename_bound_core old new_ rhs w h with h | h
        · exact Or.inl (erase_mono (fun w h => contains_union_left _ _ _ h) w h)
        · exact Or.inr h
      · -- w ∈ (freeVarsLet rest body).erase x, and x == old
        have hne : (old == w) = false := by
          cases h' : (old == w); rfl
          rw [erase_contains_beq_false _ x w (varid_beq_trans hxo h')] at h
          exact Bool.noConfusion h
        exact Or.inl (erase_contains_ne_of_contains (contains_union_right _ _ _ h) hne)
    · -- x != old
      have hne_xo : (x == old) = false := by
        cases h : (x == old); rfl; exact absurd h hxo
      have h_rl : (renameLet old new_ ((x, rhs, er) :: rest) body).1 =
          (x, rename old new_ rhs, er) :: (renameLet old new_ rest body).1 := by
        simp only [renameLet, hne_xo]; rfl
      have h_rl2 : (renameLet old new_ ((x, rhs, er) :: rest) body).2 =
          (renameLet old new_ rest body).2 := by
        simp only [renameLet, hne_xo]; rfl
      rw [h_rl, h_rl2] at hw
      rw [Moist.MIR.freeVarsLet.eq_2] at hw ⊢
      rcases contains_union_elim hw with h | h
      · rcases freeVars_rename_bound_core old new_ rhs w h with h | h
        · exact Or.inl (erase_mono (fun w h => contains_union_left _ _ _ h) w h)
        · exact Or.inr h
      · have hw_inner := contains_of_contains_erase h
        have hne_xw : (x == w) = false := by
          cases h' : (x == w); rfl
          rw [erase_contains_beq_false _ x w h'] at h; exact Bool.noConfusion h
        rcases freeVarsLet_rename_bound_core old new_ rest body w hw_inner with h' | h'
        · exact Or.inl (erase_contains_ne_of_contains
            (contains_union_right _ _ _ (erase_contains_ne_of_contains
              (contains_of_contains_erase h') hne_xw))
            (by cases h'' : (old == w); rfl
                rw [erase_contains_beq_false _ old w h''] at h'; exact Bool.noConfusion h'))
        · exact Or.inr h'
termination_by sizeOf binds + sizeOf body
end

--------------------------------------------------------------------------------
-- freeVars(renameBinds old new bs) + freeVars(rename old new body) bound
--------------------------------------------------------------------------------

private theorem freeVarsLet_renameBinds_bound_core (old new_ : VarId)
    (binds : List (VarId × Expr × Bool)) (body : Expr) (w : VarId)
    (hw : (freeVarsLet (renameBinds old new_ binds) (rename old new_ body)).contains w = true) :
    ((freeVarsLet binds body).erase old).contains w = true ∨ (w == new_) = true := by
  induction binds with
  | nil =>
    rw [show renameBinds old new_ [] = ([] : List (VarId × Expr × Bool)) from rfl] at hw
    rw [Moist.MIR.freeVarsLet.eq_1] at hw ⊢
    exact freeVars_rename_bound_core old new_ body w hw
  | cons bd rest ih =>
    obtain ⟨x, rhs, er⟩ := bd
    rw [show renameBinds old new_ ((x, rhs, er) :: rest) =
        (x, rename old new_ rhs, er) :: renameBinds old new_ rest from rfl] at hw
    rw [Moist.MIR.freeVarsLet.eq_2] at hw ⊢
    rcases contains_union_elim hw with h | h
    · rcases freeVars_rename_bound_core old new_ rhs w h with h | h
      · exact Or.inl (erase_mono (fun w h => contains_union_left _ _ _ h) w h)
      · exact Or.inr h
    · have hw_inner := contains_of_contains_erase h
      have hne_xw : (x == w) = false := by
        cases h' : (x == w); rfl
        rw [erase_contains_beq_false _ x w h'] at h; exact Bool.noConfusion h
      rcases ih hw_inner with h' | h'
      · exact Or.inl (erase_contains_ne_of_contains
          (contains_union_right _ _ _ (erase_contains_ne_of_contains
            (contains_of_contains_erase h') hne_xw))
          (by cases h'' : (old == w); rfl
              rw [erase_contains_beq_false _ old w h''] at h'; exact Bool.noConfusion h'))
      · exact Or.inr h'

--------------------------------------------------------------------------------
-- Free variables of subst are bounded by (freeVars e \ {v}) ∪ freeVars rhs.
--------------------------------------------------------------------------------

set_option maxHeartbeats 800000 in
mutual
private theorem freeVars_subst_tight (v : VarId) (rhs e : Expr)
    (s : Moist.MIR.FreshState) (w : VarId)
    (hw : (freeVars (subst v rhs e s).1).contains w = true) :
    ((freeVars e).erase v).contains w = true ∨ (freeVars rhs).contains w = true := by
  match e with
  | .Var x =>
    simp only [subst, pure, StateT.pure] at hw
    split at hw
    · exact Or.inr hw
    · rename_i hxv
      -- x != v, result = .Var x
      rw [Moist.MIR.freeVars.eq_1, Moist.MIR.VarSet.singleton_contains'] at hw
      have hne_vw : (v == w) = false := by
        cases h : (v == w); rfl
        exact absurd (varid_beq_trans hw (varid_beq_symm h)) hxv
      exact Or.inl (Moist.MIR.VarSet.contains_erase_ne _ v w hne_vw
        (by rw [Moist.MIR.freeVars.eq_1, Moist.MIR.VarSet.singleton_contains']; exact hw))
  | .Lit _ =>
    simp only [subst, pure, StateT.pure, freeVars] at hw
    exact absurd hw (by simp [Moist.MIR.VarSet.contains_empty])
  | .Builtin _ =>
    simp only [subst, pure, StateT.pure, freeVars] at hw
    exact absurd hw (by simp [Moist.MIR.VarSet.contains_empty])
  | .Error =>
    simp only [subst, pure, StateT.pure, freeVars] at hw
    exact absurd hw (by simp [Moist.MIR.VarSet.contains_empty])
  | .Lam x body =>
    by_cases hxv : (x == v) = true
    · -- x == v: identity, result = .Lam x body
      have h_sub : (subst v rhs (.Lam x body) s).1 = .Lam x body := by
        simp only [subst, hxv, if_true, pure, StateT.pure]
      rw [h_sub] at hw; rw [Moist.MIR.freeVars.eq_5] at hw ⊢
      have hne : (v == w) = false := by
        cases h : (v == w); rfl
        rw [erase_contains_beq_false _ x w (varid_beq_trans hxv h)] at hw
        exact Bool.noConfusion hw
      exact Or.inl (erase_contains_ne_of_contains hw hne)
    · have hne_xv : (x == v) = false := by
        cases h : (x == v); rfl; exact absurd h hxv
      by_cases hfv : (freeVars rhs).contains x = true
      · -- alpha-rename case
        have h_sub : (subst v rhs (.Lam x body) s).1 =
            .Lam (freshVar x.hint s).1
              (subst v rhs (rename x (freshVar x.hint s).1 body) (freshVar x.hint s).2).1 := by
          simp only [subst, hne_xv, hfv, if_true, bind, pure]; rfl
        rw [h_sub, Moist.MIR.freeVars.eq_5] at hw; rw [Moist.MIR.freeVars.eq_5]
        have hw_inner := contains_of_contains_erase hw
        have hne_x'w : ((freshVar x.hint s).1 == w) = false := by
          cases h : ((freshVar x.hint s).1 == w); rfl
          rw [erase_contains_beq_false _ (freshVar x.hint s).1 w h] at hw
          exact Bool.noConfusion hw
        rcases freeVars_subst_tight v rhs (rename x (freshVar x.hint s).1 body)
            (freshVar x.hint s).2 w hw_inner with h_ren | h_rhs
        · have hw_ren_inner := contains_of_contains_erase h_ren
          have hne_vw : (v == w) = false := by
            cases h : (v == w); rfl
            rw [erase_contains_beq_false _ v w h] at h_ren; exact Bool.noConfusion h_ren
          rcases freeVars_rename_bound_core x (freshVar x.hint s).1 body w hw_ren_inner
              with h_body | h_eq
          · exact Or.inl (erase_contains_ne_of_contains h_body hne_vw)
          · exact absurd (varid_beq_symm h_eq) (by simp [hne_x'w])
        · exact Or.inr h_rhs
      · -- simple case: no alpha-rename
        have hfv_f : (freeVars rhs).contains x = false := by
          cases h : (freeVars rhs).contains x; rfl; exact absurd h hfv
        have h_sub : (subst v rhs (.Lam x body) s).1 =
            .Lam x (subst v rhs body s).1 := by
          simp only [subst, hne_xv, hfv_f, bind, pure]; rfl
        rw [h_sub, Moist.MIR.freeVars.eq_5] at hw; rw [Moist.MIR.freeVars.eq_5]
        have hw_inner := contains_of_contains_erase hw
        have hne_xw : (x == w) = false := by
          cases h : (x == w); rfl
          rw [erase_contains_beq_false _ x w h] at hw; exact Bool.noConfusion hw
        rcases freeVars_subst_tight v rhs body _ w hw_inner with h | h
        · have hne_vw : (v == w) = false := by
            cases h' : (v == w); rfl
            rw [erase_contains_beq_false _ v w h'] at h; exact Bool.noConfusion h
          exact Or.inl (erase_contains_ne_of_contains
            (erase_contains_ne_of_contains (contains_of_contains_erase h) hne_xw) hne_vw)
        · exact Or.inr h
  | .Fix f body =>
    by_cases hfv : (f == v) = true
    · -- f == v: identity
      have h_sub : (subst v rhs (.Fix f body) s).1 = .Fix f body := by
        simp only [subst, hfv, if_true, pure, StateT.pure]
      rw [h_sub, Moist.MIR.freeVars.eq_6] at hw; rw [Moist.MIR.freeVars.eq_6]
      have hne : (v == w) = false := by
        cases h : (v == w); rfl
        rw [erase_contains_beq_false _ f w (varid_beq_trans hfv h)] at hw
        exact Bool.noConfusion hw
      exact Or.inl (erase_contains_ne_of_contains hw hne)
    · have hne_fv : (f == v) = false := by
        cases h : (f == v); rfl; exact absurd h hfv
      by_cases hfv_rhs : (freeVars rhs).contains f = true
      · -- alpha-rename case
        have h_sub : (subst v rhs (.Fix f body) s).1 =
            .Fix (freshVar f.hint s).1
              (subst v rhs (rename f (freshVar f.hint s).1 body) (freshVar f.hint s).2).1 := by
          simp only [subst, hne_fv, hfv_rhs, if_true, bind, pure]; rfl
        rw [h_sub, Moist.MIR.freeVars.eq_6] at hw; rw [Moist.MIR.freeVars.eq_6]
        have hw_inner := contains_of_contains_erase hw
        have hne_f'w : ((freshVar f.hint s).1 == w) = false := by
          cases h : ((freshVar f.hint s).1 == w); rfl
          rw [erase_contains_beq_false _ (freshVar f.hint s).1 w h] at hw
          exact Bool.noConfusion hw
        rcases freeVars_subst_tight v rhs (rename f (freshVar f.hint s).1 body)
            (freshVar f.hint s).2 w hw_inner with h_ren | h_rhs
        · have hw_ren_inner := contains_of_contains_erase h_ren
          have hne_vw : (v == w) = false := by
            cases h : (v == w); rfl
            rw [erase_contains_beq_false _ v w h] at h_ren; exact Bool.noConfusion h_ren
          rcases freeVars_rename_bound_core f (freshVar f.hint s).1 body w hw_ren_inner
              with h_body | h_eq
          · exact Or.inl (erase_contains_ne_of_contains h_body hne_vw)
          · exact absurd (varid_beq_symm h_eq) (by simp [hne_f'w])
        · exact Or.inr h_rhs
      · -- simple case
        have hfv_f : (freeVars rhs).contains f = false := by
          cases h : (freeVars rhs).contains f; rfl; exact absurd h hfv_rhs
        have h_sub : (subst v rhs (.Fix f body) s).1 =
            .Fix f (subst v rhs body s).1 := by
          simp only [subst, hne_fv, hfv_f, bind, pure]; rfl
        rw [h_sub, Moist.MIR.freeVars.eq_6] at hw; rw [Moist.MIR.freeVars.eq_6]
        have hw_inner := contains_of_contains_erase hw
        have hne_fw : (f == w) = false := by
          cases h : (f == w); rfl
          rw [erase_contains_beq_false _ f w h] at hw; exact Bool.noConfusion hw
        rcases freeVars_subst_tight v rhs body _ w hw_inner with h | h
        · have hne_vw : (v == w) = false := by
            cases h' : (v == w); rfl
            rw [erase_contains_beq_false _ v w h'] at h; exact Bool.noConfusion h
          exact Or.inl (erase_contains_ne_of_contains
            (erase_contains_ne_of_contains (contains_of_contains_erase h) hne_fw) hne_vw)
        · exact Or.inr h
  | .App f x =>
    have h_sub : (subst v rhs (.App f x) s).1 =
        .App (subst v rhs f s).1 (subst v rhs x (subst v rhs f s).2).1 := by
      simp only [subst, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub] at hw; simp only [freeVars] at hw ⊢
    rcases contains_union_elim hw with h | h
    · rcases freeVars_subst_tight v rhs f s w h with h | h
      · exact Or.inl (erase_mono (fun w h => contains_union_left _ _ _ h) w h)
      · exact Or.inr h
    · rcases freeVars_subst_tight v rhs x _ w h with h | h
      · exact Or.inl (erase_mono (fun w h => contains_union_right _ _ _ h) w h)
      · exact Or.inr h
  | .Force e' =>
    have h_sub : (subst v rhs (.Force e') s).1 = .Force (subst v rhs e' s).1 := by
      simp only [subst, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub] at hw; simp only [freeVars] at hw ⊢
    exact freeVars_subst_tight v rhs e' s w hw
  | .Delay e' =>
    have h_sub : (subst v rhs (.Delay e') s).1 = .Delay (subst v rhs e' s).1 := by
      simp only [subst, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub] at hw; simp only [freeVars] at hw ⊢
    exact freeVars_subst_tight v rhs e' s w hw
  | .Constr tag args =>
    have h_sub : (subst v rhs (.Constr tag args) s).1 =
        .Constr tag (substList v rhs args s).1 := by
      simp only [subst, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub] at hw; simp only [freeVars] at hw ⊢
    exact freeVarsList_substList_tight v rhs args s w hw
  | .Case scrut alts =>
    have h_sub : (subst v rhs (.Case scrut alts) s).1 =
        .Case (subst v rhs scrut s).1 (substList v rhs alts (subst v rhs scrut s).2).1 := by
      simp only [subst, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub] at hw; simp only [freeVars] at hw ⊢
    rcases contains_union_elim hw with h | h
    · rcases freeVars_subst_tight v rhs scrut s w h with h | h
      · exact Or.inl (erase_mono (fun w h => contains_union_left _ _ _ h) w h)
      · exact Or.inr h
    · rcases freeVarsList_substList_tight v rhs alts _ w h with h | h
      · exact Or.inl (erase_mono (fun w h => contains_union_right _ _ _ h) w h)
      · exact Or.inr h
  | .Let binds body =>
    have h_sub : (subst v rhs (.Let binds body) s).1 =
        .Let (substLet v rhs (freeVars rhs) binds body s).1.1
             (substLet v rhs (freeVars rhs) binds body s).1.2 := by
      simp only [subst, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub] at hw; simp only [freeVars] at hw ⊢
    exact freeVarsLet_substLet_tight v rhs binds body s w hw
termination_by e.nodes

private theorem freeVarsList_substList_tight (v : VarId) (rhs : Expr) (es : List Expr)
    (s : Moist.MIR.FreshState) (w : VarId)
    (hw : (freeVarsList (substList v rhs es s).1).contains w = true) :
    ((freeVarsList es).erase v).contains w = true ∨ (freeVars rhs).contains w = true := by
  match es with
  | [] =>
    simp only [substList, pure, StateT.pure, freeVarsList] at hw
    exact absurd hw (by simp [Moist.MIR.VarSet.contains_empty])
  | e :: rest =>
    have h_sub : (substList v rhs (e :: rest) s).1 =
        (subst v rhs e s).1 :: (substList v rhs rest (subst v rhs e s).2).1 := by
      simp only [substList, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub] at hw; simp only [freeVarsList] at hw ⊢
    rcases contains_union_elim hw with h | h
    · rcases freeVars_subst_tight v rhs e s w h with h | h
      · exact Or.inl (erase_mono (fun w h => contains_union_left _ _ _ h) w h)
      · exact Or.inr h
    · rcases freeVarsList_substList_tight v rhs rest _ w h with h | h
      · exact Or.inl (erase_mono (fun w h => contains_union_right _ _ _ h) w h)
      · exact Or.inr h
termination_by Moist.MIR.Expr.nodesList es

private theorem freeVarsLet_substLet_tight (v : VarId) (rhs : Expr)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (s : Moist.MIR.FreshState) (w : VarId)
    (hw : (freeVarsLet (substLet v rhs (freeVars rhs) binds body s).1.1
                       (substLet v rhs (freeVars rhs) binds body s).1.2).contains w = true) :
    ((freeVarsLet binds body).erase v).contains w = true ∨ (freeVars rhs).contains w = true := by
  match binds with
  | [] =>
    have h_form : (substLet v rhs (freeVars rhs) [] body s).1 =
        ([], (subst v rhs body s).1) := by
      simp only [substLet, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [show (substLet v rhs (freeVars rhs) [] body s).1.1 = []
            from congrArg Prod.fst h_form,
        show (substLet v rhs (freeVars rhs) [] body s).1.2 = (subst v rhs body s).1
            from congrArg Prod.snd h_form] at hw
    simp only [freeVarsLet] at hw ⊢
    exact freeVars_subst_tight v rhs body s w hw
  | (x, rhs_h, er) :: rest =>
    by_cases hxv : (x == v) = true
    · have h_form : (substLet v rhs (freeVars rhs) ((x, rhs_h, er) :: rest) body s).1 =
          ((x, (subst v rhs rhs_h s).1, er) :: rest, body) := by
        simp only [substLet, hxv, if_true, bind, StateT.bind, pure, StateT.pure]; rfl
      rw [show (substLet v rhs (freeVars rhs) ((x, rhs_h, er) :: rest) body s).1.1 =
               (x, (subst v rhs rhs_h s).1, er) :: rest from congrArg Prod.fst h_form,
          show (substLet v rhs (freeVars rhs) ((x, rhs_h, er) :: rest) body s).1.2 = body
              from congrArg Prod.snd h_form] at hw
      simp only [freeVarsLet] at hw ⊢
      rcases contains_union_elim hw with h | h
      · rcases freeVars_subst_tight v rhs rhs_h s w h with h | h
        · exact Or.inl (erase_mono (fun w h => contains_union_left _ _ _ h) w h)
        · exact Or.inr h
      · have hne : (v == w) = false := by
          cases h' : (v == w); rfl
          rw [erase_contains_beq_false _ x w (varid_beq_trans hxv h')] at h
          exact Bool.noConfusion h
        exact Or.inl (erase_contains_ne_of_contains (contains_union_right _ _ _ h) hne)
    · have hne : (x == v) = false := by cases h : (x == v); rfl; exact absurd h hxv
      by_cases hfv : (freeVars rhs).contains x = true
      · -- alpha-rename case for Let binder
        -- Abbreviations for the fresh variable and post-state
        -- x' = (freshVar x.hint (subst v rhs rhs_h s).2).1
        -- s1 = (freshVar x.hint (subst v rhs rhs_h s).2).2
        have h_form1 : (substLet v rhs (freeVars rhs) ((x, rhs_h, er) :: rest) body s).1.1 =
            ((freshVar x.hint (subst v rhs rhs_h s).2).1, (subst v rhs rhs_h s).1, er) ::
            (substLet v rhs (freeVars rhs)
              (renameBinds x (freshVar x.hint (subst v rhs rhs_h s).2).1 rest)
              (rename x (freshVar x.hint (subst v rhs rhs_h s).2).1 body)
              (freshVar x.hint (subst v rhs rhs_h s).2).2).1.1 := by
          simp only [substLet, hne, hfv, if_true, bind, pure]; rfl
        have h_form2 : (substLet v rhs (freeVars rhs) ((x, rhs_h, er) :: rest) body s).1.2 =
            (substLet v rhs (freeVars rhs)
              (renameBinds x (freshVar x.hint (subst v rhs rhs_h s).2).1 rest)
              (rename x (freshVar x.hint (subst v rhs rhs_h s).2).1 body)
              (freshVar x.hint (subst v rhs rhs_h s).2).2).1.2 := by
          simp only [substLet, hne, hfv, if_true, bind, pure]; rfl
        rw [h_form1, h_form2, Moist.MIR.freeVarsLet.eq_2] at hw
        rw [Moist.MIR.freeVarsLet.eq_2]
        rcases contains_union_elim hw with h | h
        · rcases freeVars_subst_tight v rhs rhs_h s w h with h | h
          · exact Or.inl (erase_mono (fun w h => contains_union_left _ _ _ h) w h)
          · exact Or.inr h
        · have hw_inner := contains_of_contains_erase h
          have hne_x'w : ((freshVar x.hint (subst v rhs rhs_h s).2).1 == w) = false := by
            cases h' : ((freshVar x.hint (subst v rhs rhs_h s).2).1 == w); rfl
            rw [erase_contains_beq_false _ _ w h'] at h; exact Bool.noConfusion h
          rcases freeVarsLet_substLet_tight v rhs
              (renameBinds x (freshVar x.hint (subst v rhs rhs_h s).2).1 rest)
              (rename x (freshVar x.hint (subst v rhs rhs_h s).2).1 body)
              (freshVar x.hint (subst v rhs rhs_h s).2).2 w hw_inner with h' | h'
          · have hw_rl := contains_of_contains_erase h'
            have hne_vw : (v == w) = false := by
              cases h'' : (v == w); rfl
              rw [erase_contains_beq_false _ v w h''] at h'; exact Bool.noConfusion h'
            rcases freeVarsLet_renameBinds_bound_core x
                (freshVar x.hint (subst v rhs rhs_h s).2).1 rest body w hw_rl with h_orig | h_eq
            · exact Or.inl (erase_contains_ne_of_contains
                (contains_union_right _ _ _ h_orig) hne_vw)
            · exact absurd (varid_beq_symm h_eq) (by simp [hne_x'w])
          · exact Or.inr h'
      · -- simple case
        have hfv_f : (freeVars rhs).contains x = false := by
          cases h : (freeVars rhs).contains x; rfl; exact absurd h hfv
        have h1 : (substLet v rhs (freeVars rhs) ((x, rhs_h, er) :: rest) body s).1.1 =
            (x, (subst v rhs rhs_h s).1, er) ::
            (substLet v rhs (freeVars rhs) rest body (subst v rhs rhs_h s).2).1.1 := by
          simp only [substLet, hne, hfv_f, bind, StateT.bind, pure, StateT.pure,
                     Bool.false_eq_true, ↓reduceIte]; rfl
        have h2 : (substLet v rhs (freeVars rhs) ((x, rhs_h, er) :: rest) body s).1.2 =
            (substLet v rhs (freeVars rhs) rest body (subst v rhs rhs_h s).2).1.2 := by
          simp only [substLet, hne, hfv_f, bind, StateT.bind, pure, StateT.pure,
                     Bool.false_eq_true, ↓reduceIte]; rfl
        rw [h1, h2] at hw
        simp only [freeVarsLet] at hw ⊢
        rcases contains_union_elim hw with h | h
        · rcases freeVars_subst_tight v rhs rhs_h s w h with h | h
          · exact Or.inl (erase_mono (fun w h => contains_union_left _ _ _ h) w h)
          · exact Or.inr h
        · have hw_inner := contains_of_contains_erase h
          have hne_xw : (x == w) = false := by
            cases h' : (x == w); rfl
            rw [erase_contains_beq_false _ x w h'] at h; exact Bool.noConfusion h
          rcases freeVarsLet_substLet_tight v rhs rest body _ w hw_inner with h' | h'
          · have hne_vw : (v == w) = false := by
              cases h'' : (v == w); rfl
              rw [erase_contains_beq_false _ v w h''] at h'; exact Bool.noConfusion h'
            exact Or.inl (erase_contains_ne_of_contains
              (contains_union_right _ _ _ (erase_contains_ne_of_contains
                (contains_of_contains_erase h') hne_xw)) hne_vw)
          · exact Or.inr h'
termination_by Moist.MIR.Expr.nodesBinds binds + body.nodes
end

-- Inlining equations (local copies from InlineSoundness)
private theorem inlinePass_leaf_eq {e : Expr}
    (hlet : ∀ bs b, e ≠ .Let bs b)
    (hlam : ∀ x b, e ≠ .Lam x b)
    (hfix : ∀ f b, e ≠ .Fix f b)
    (happ : ∀ f x, e ≠ .App f x)
    (hforce : ∀ inner, e ≠ .Force inner)
    (hdelay : ∀ inner, e ≠ .Delay inner)
    (hconstr : ∀ t args, e ≠ .Constr t args)
    (hcase : ∀ sc alts, e ≠ .Case sc alts)
    (s : Moist.MIR.FreshState) :
    inlinePass e s = ((e, false), s) := by
  rw [Moist.MIR.inlinePass.eq_9 e
        (fun bs b heq => hlet bs b heq)
        (fun x b heq => hlam x b heq)
        (fun f b heq => hfix f b heq)
        (fun f x heq => happ f x heq)
        (fun inner heq => hforce inner heq)
        (fun inner heq => hdelay inner heq)
        (fun t args heq => hconstr t args heq)
        (fun sc alts heq => hcase sc alts heq)]
  rfl


-- betaReduce freeVars bound
private theorem betaReduce_fv_sub (f' x' : Expr) (s : Moist.MIR.FreshState) (w : VarId)
    (h : (freeVars (Moist.MIR.betaReduce f' x' s).1.1).contains w = true) :
    (freeVars (.App f' x')).contains w = true := by
  unfold Moist.MIR.betaReduce at h
  match f' with
  | .Lam param body =>
    simp only at h
    split at h
    · -- x'.isAtom = true, beta case: result = subst param x' body
      rename_i hatom
      simp only [pure, StateT.pure, bind, StateT.bind] at h
      rcases freeVars_subst_tight param x' body s w h with h_body | h_x'
      · rw [Moist.MIR.freeVars.eq_7]
        have : freeVars (.Lam param body) = (freeVars body).erase param := by
          simp only [freeVars]
        exact contains_union_left _ _ _ (this ▸ h_body)
      · rw [Moist.MIR.freeVars.eq_7]
        exact contains_union_right _ _ _ h_x'
    · -- non-atom case: result = App f' x'
      simp only [pure, StateT.pure] at h; exact h
  | .Var _ | .Lit _ | .Builtin _ | .Error | .Fix _ _ | .App _ _ | .Force _ |
    .Delay _ | .Constr _ _ | .Case _ _ | .Let _ _ =>
    simp only [pure, StateT.pure] at h; exact h

--------------------------------------------------------------------------------
-- Helper: erase commutativity
--------------------------------------------------------------------------------

private theorem erase_erase_comm (s : Moist.MIR.VarSet) (v w x : VarId)
    (h : ((s.erase v).erase w).contains x = true) :
    ((s.erase w).erase v).contains x = true := by
  -- x ∈ s.erase(v).erase(w) means x ∈ s, x != v, x != w
  have hx_s : s.contains x = true := contains_of_contains_erase (contains_of_contains_erase h)
  have hne_wx : (w == x) = false := by
    cases hc : (w == x); rfl
    rw [erase_contains_beq_false _ w x hc] at h; exact Bool.noConfusion h
  have hne_vx : (v == x) = false := by
    have h' := contains_of_contains_erase h
    cases hc : (v == x); rfl
    rw [erase_contains_beq_false _ v x hc] at h'; exact Bool.noConfusion h'
  exact Moist.MIR.VarSet.contains_erase_ne _ v x hne_vx
    (Moist.MIR.VarSet.contains_erase_ne _ w x hne_wx hx_s)

--------------------------------------------------------------------------------
-- Helper: union-erase subset bound
-- (A.erase v ∪ B) contains w → (A ∪ B).erase v contains w ∨ B contains w
-- Actually we just need: if w ∈ A.erase v, then w ∈ (A ∪ C).erase v
--------------------------------------------------------------------------------

private theorem erase_union_left_mono (a c : Moist.MIR.VarSet) (v w : VarId)
    (h : (a.erase v).contains w = true) :
    ((a.union c).erase v).contains w = true := by
  have hne : (v == w) = false := by
    cases hc : (v == w); rfl
    rw [erase_contains_beq_false _ v w hc] at h; exact Bool.noConfusion h
  exact Moist.MIR.VarSet.contains_erase_ne _ v w hne
    (contains_union_left _ _ _ (contains_of_contains_erase h))

private theorem erase_union_right_mono (a c : Moist.MIR.VarSet) (v w : VarId)
    (h : (c.erase v).contains w = true) :
    ((a.union c).erase v).contains w = true := by
  have hne : (v == w) = false := by
    cases hc : (v == w); rfl
    rw [erase_contains_beq_false _ v w hc] at h; exact Bool.noConfusion h
  exact Moist.MIR.VarSet.contains_erase_ne _ v w hne
    (contains_union_right _ _ _ (contains_of_contains_erase h))

--------------------------------------------------------------------------------
-- substInline_freeVarsLet_bound:
-- After inlining v→rhs in rest and body,
-- freeVarsLet rest' body' ⊆ freeVars rhs ∪ (freeVarsLet rest body).erase v
--------------------------------------------------------------------------------

private theorem substInline_freeVarsLet_bound
    (v : VarId) (rhs : Expr) (rest : List (VarId × Expr × Bool))
    (body : Expr) (s_body s_rest : Moist.MIR.FreshState) (w : VarId)
    (hw : (freeVarsLet (substInBindings v rhs rest s_rest).1.val
                       (subst v rhs body s_body).1).contains w = true) :
    ((freeVars rhs).union ((freeVarsLet rest body).erase v)).contains w = true := by
  induction rest generalizing s_rest body s_body with
  | nil =>
    simp only [substInBindings, pure, StateT.pure] at hw
    -- freeVarsLet [] (subst v rhs body s_body).1 = freeVars (subst v rhs body s_body).1
    rw [Moist.MIR.freeVarsLet.eq_1] at hw
    rcases freeVars_subst_tight v rhs body s_body w hw with h | h
    · -- w ∈ (freeVars body).erase v
      rw [Moist.MIR.freeVarsLet.eq_1]
      exact contains_union_right _ _ _ h
    · -- w ∈ freeVars rhs
      exact contains_union_left _ _ _ h
  | cons bd rest_tail ih =>
    obtain ⟨x, e_x, er_x⟩ := bd
    -- Unfold substInBindings: result = (x, (subst v rhs e_x s_rest).1, er_x) :: tail
    have h_form : (substInBindings v rhs ((x, e_x, er_x) :: rest_tail) s_rest).1.val =
        (x, (subst v rhs e_x s_rest).1, er_x) ::
        (substInBindings v rhs rest_tail (subst v rhs e_x s_rest).2).1.val := by
      simp only [substInBindings, bind, StateT.bind]; rfl
    rw [h_form, Moist.MIR.freeVarsLet.eq_2] at hw
    rcases contains_union_elim hw with h_rhs_part | h_inner_part
    · -- w ∈ freeVars (subst v rhs e_x s_rest).1
      rcases freeVars_subst_tight v rhs e_x s_rest w h_rhs_part with h | h
      · -- w ∈ (freeVars e_x).erase v → w ∈ (freeVarsLet rest body).erase v
        rw [Moist.MIR.freeVarsLet.eq_2]
        exact contains_union_right _ _ _
          (erase_union_left_mono _ _ v w h)
      · -- w ∈ freeVars rhs
        exact contains_union_left _ _ _ h
    · -- w ∈ (freeVarsLet rest_tail' body').erase x
      have hw_inner := contains_of_contains_erase h_inner_part
      have hne_xw : (x == w) = false := by
        cases hc : (x == w); rfl
        rw [erase_contains_beq_false _ x w hc] at h_inner_part
        exact Bool.noConfusion h_inner_part
      -- By IH: w ∈ freeVars rhs ∪ (freeVarsLet rest_tail body).erase v
      have ih_result := ih body s_body (subst v rhs e_x s_rest).2 hw_inner
      rcases contains_union_elim ih_result with h | h
      · -- w ∈ freeVars rhs
        exact contains_union_left _ _ _ h
      · -- w ∈ (freeVarsLet rest_tail body).erase v
        -- Need: w ∈ (freeVarsLet (x,e_x,er_x)::rest_tail body).erase v
        -- = ((freeVars e_x).union ((freeVarsLet rest_tail body).erase x)).erase v
        rw [Moist.MIR.freeVarsLet.eq_2]
        exact contains_union_right _ _ _
          (erase_union_right_mono _ _ v w
            (erase_erase_comm _ v x w
              (Moist.MIR.VarSet.contains_erase_ne _ x w hne_xw h)))

--------------------------------------------------------------------------------
-- freeVarsLet_suffix_mono: monotonicity of freeVarsLet in its suffix
-- If freeVarsLet b1 body1 ⊆ freeVarsLet b2 body2,
-- then freeVarsLet (a ++ b1) body1 ⊆ freeVarsLet (a ++ b2) body2
--------------------------------------------------------------------------------

private theorem freeVarsLet_suffix_mono
    (a b1 b2 : List (VarId × Expr × Bool)) (body1 body2 : Expr)
    (h : ∀ w, (freeVarsLet b1 body1).contains w = true →
              (freeVarsLet b2 body2).contains w = true) :
    ∀ w, (freeVarsLet (a ++ b1) body1).contains w = true →
         (freeVarsLet (a ++ b2) body2).contains w = true := by
  induction a with
  | nil => simp only [List.nil_append]; exact h
  | cons bd a_tail ih =>
    obtain ⟨x, rhs_a, er_a⟩ := bd
    intro w hw
    rw [List.cons_append] at hw ⊢
    rw [Moist.MIR.freeVarsLet.eq_2] at hw ⊢
    exact union_mono (fun w h => h) (fun w h => erase_mono ih w h) w hw

--------------------------------------------------------------------------------
-- inlineLetGo_fv_bound:
-- freeVars (inlineLetGo binds acc body changed s).1.1 ⊆
--   freeVarsLet (acc.reverse ++ binds) body
--------------------------------------------------------------------------------

private theorem inlineLetGo_fv_bound
    (binds : List (VarId × Expr × Bool))
    (acc : List (VarId × Expr × Bool))
    (body : Expr) (changed : Bool) (s : Moist.MIR.FreshState) (w : VarId)
    (hw : (freeVars (inlineLetGo binds acc body changed s).1.1).contains w = true) :
    (freeVarsLet (acc.reverse ++ binds) body).contains w = true := by
  match binds with
  | [] =>
    rw [Moist.MIR.inlineLetGo.eq_1] at hw
    simp only [List.append_nil]
    cases hacc : acc.reverse with
    | nil =>
      rw [hacc] at hw; simp only [pure, StateT.pure] at hw
      rw [Moist.MIR.freeVarsLet.eq_1]; exact hw
    | cons s' rest' =>
      rw [hacc] at hw; simp only [pure, StateT.pure] at hw
      rw [Moist.MIR.freeVars.eq_12] at hw; exact hw
  | (v, rhs, er) :: rest =>
    rw [Moist.MIR.inlineLetGo.eq_2] at hw
    simp only [bind, StateT.bind] at hw
    by_cases hinline : (shouldInline rhs
        (countOccurrences v body +
          rest.foldl (fun n (_, e, _) => n + countOccurrences v e) 0)
        (Moist.MIR.occursUnderFix v body ||
          rest.any (fun (_, e, _) => Moist.MIR.occursUnderFix v e))
        (Moist.MIR.occursInDeferred v body ||
          rest.any (fun (_, e, _) => Moist.MIR.occursInDeferred v e))) = true
    · -- Inline case
      simp only [hinline, ↓reduceIte] at hw
      -- body' = (subst v rhs body s).1
      -- rest' = (substInBindings v rhs rest (subst v rhs body s).2).1.val
      have hdec : (substInBindings v rhs rest (subst v rhs body s).2).1.val.length <
          ((v, rhs, er) :: rest).length := by
        simp only [List.length_cons,
          (substInBindings v rhs rest (subst v rhs body s).2).1.property]; omega
      -- IH: freeVars result ⊆ freeVarsLet (acc.rev ++ rest') body'
      have ih := inlineLetGo_fv_bound
        (substInBindings v rhs rest (subst v rhs body s).2).1.val
        acc
        (subst v rhs body s).1
        true
        (substInBindings v rhs rest (subst v rhs body s).2).2
        w hw
      -- Now chain: acc.rev ++ rest' ⊆ acc.rev ++ (v,rhs,er)::rest
      -- via substInline_freeVarsLet_bound
      apply freeVarsLet_suffix_mono acc.reverse _ _ _ _ _ w ih
      intro w' hw'
      -- Need: freeVarsLet rest' body' ⊆ freeVarsLet ((v,rhs,er)::rest) body
      rw [Moist.MIR.freeVarsLet.eq_2]
      exact substInline_freeVarsLet_bound v rhs rest body s
        (subst v rhs body s).2 w' hw'
    · -- Keep case
      have hinline' : (shouldInline rhs
          (countOccurrences v body +
            rest.foldl (fun n (_, e, _) => n + countOccurrences v e) 0)
          (Moist.MIR.occursUnderFix v body ||
            rest.any (fun (_, e, _) => Moist.MIR.occursUnderFix v e))
          (Moist.MIR.occursInDeferred v body ||
            rest.any (fun (_, e, _) => Moist.MIR.occursInDeferred v e))) = false := by
        cases h : shouldInline rhs _ _ _ with | true => exact absurd h hinline | false => rfl
      simp only [hinline', Bool.false_eq_true, ↓reduceIte] at hw
      -- IH: freeVars result ⊆ freeVarsLet (((v,rhs,er)::acc).rev ++ rest) body
      have ih := inlineLetGo_fv_bound rest ((v, rhs, er) :: acc) body changed s w hw
      -- ((v,rhs,er)::acc).reverse ++ rest = acc.reverse ++ [(v,rhs,er)] ++ rest
      --   = acc.reverse ++ (v,rhs,er)::rest
      rw [List.reverse_cons, List.append_assoc] at ih
      exact ih
  termination_by binds.length

--------------------------------------------------------------------------------
-- inlineLetBindings_fv_bound: specialization with acc = []
--------------------------------------------------------------------------------

private theorem inlineLetBindings_fv_bound
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (s : Moist.MIR.FreshState) (w : VarId)
    (hw : (freeVars (inlineLetBindings binds body s).1.1).contains w = true) :
    (freeVarsLet binds body).contains w = true := by
  unfold inlineLetBindings at hw
  have := inlineLetGo_fv_bound binds [] body false s w hw
  simpa using this

mutual
theorem freeVars_nonincreasing (e : Expr) (s : Moist.MIR.FreshState) :
    ∀ w, (freeVars (inlinePass e s).1.1).contains w = true →
         (freeVars e).contains w = true := by
  intro w hw
  match e with
  | .Var v =>
    rw [inlinePass_leaf_eq (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)] at hw
    exact hw
  | .Lit c =>
    rw [inlinePass_leaf_eq (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)] at hw
    exact hw
  | .Builtin b =>
    rw [inlinePass_leaf_eq (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)] at hw
    exact hw
  | .Error =>
    rw [inlinePass_leaf_eq (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)] at hw
    exact hw
  | .Lam x body =>
    have heq : (inlinePass (.Lam x body) s).1.1 = .Lam x (inlinePass body s).1.1 := by
      simp only [Moist.MIR.inlinePass.eq_2]; rfl
    rw [heq] at hw; rw [Moist.MIR.freeVars.eq_5] at hw; rw [Moist.MIR.freeVars.eq_5]
    exact erase_mono (freeVars_nonincreasing body s) w hw
  | .Fix f body =>
    have heq : (inlinePass (.Fix f body) s).1.1 = .Fix f (inlinePass body s).1.1 := by
      simp only [Moist.MIR.inlinePass.eq_3]; rfl
    rw [heq] at hw; rw [Moist.MIR.freeVars.eq_6] at hw; rw [Moist.MIR.freeVars.eq_6]
    exact erase_mono (freeVars_nonincreasing body s) w hw
  | .Force inner =>
    have heq : (inlinePass (.Force inner) s).1.1 = .Force (inlinePass inner s).1.1 := by
      simp only [Moist.MIR.inlinePass.eq_5]; rfl
    rw [heq] at hw; rw [Moist.MIR.freeVars.eq_8] at hw; rw [Moist.MIR.freeVars.eq_8]
    exact freeVars_nonincreasing inner s w hw
  | .Delay inner =>
    have heq : (inlinePass (.Delay inner) s).1.1 = .Delay (inlinePass inner s).1.1 := by
      simp only [Moist.MIR.inlinePass.eq_6]; rfl
    rw [heq] at hw; rw [Moist.MIR.freeVars.eq_9] at hw; rw [Moist.MIR.freeVars.eq_9]
    exact freeVars_nonincreasing inner s w hw
  | .Constr tag args =>
    have heq : (inlinePass (.Constr tag args) s).1.1 = .Constr tag (inlinePassList args s).1.1 := by
      simp only [Moist.MIR.inlinePass.eq_7]; rfl
    rw [heq] at hw; rw [Moist.MIR.freeVars.eq_10] at hw; rw [Moist.MIR.freeVars.eq_10]
    exact freeVarsList_nonincreasing args s w hw
  | .Case scrut alts =>
    have heq : (inlinePass (.Case scrut alts) s).1.1 =
      .Case (inlinePass scrut s).1.1
            (inlinePassList alts (inlinePass scrut s).2).1.1 := by
      simp only [Moist.MIR.inlinePass.eq_8]; rfl
    rw [heq] at hw
    rw [Moist.MIR.freeVars.eq_11] at hw
    rw [Moist.MIR.freeVars.eq_11]
    exact union_mono
      (freeVars_nonincreasing scrut s)
      (freeVarsList_nonincreasing alts (inlinePass scrut s).2)
      w hw
  | .App f x =>
    have heq : (inlinePass (.App f x) s).1.1 =
      (Moist.MIR.betaReduce (inlinePass f s).1.1
        (inlinePass x (inlinePass f s).2).1.1
        (inlinePass x (inlinePass f s).2).2).1.1 := by
      simp only [Moist.MIR.inlinePass.eq_4]; rfl
    rw [heq] at hw
    rw [Moist.MIR.freeVars.eq_7]
    have hbeta := betaReduce_fv_sub
      (inlinePass f s).1.1
      (inlinePass x (inlinePass f s).2).1.1
      (inlinePass x (inlinePass f s).2).2
      w hw
    rw [Moist.MIR.freeVars.eq_7] at hbeta
    exact union_mono
      (freeVars_nonincreasing f s)
      (freeVars_nonincreasing x (inlinePass f s).2)
      w hbeta
  | .Let binds body =>
    have heq : (inlinePass (.Let binds body) s).1.1 =
      (Moist.MIR.inlineLetBindings (inlineBindings binds s).1.1
        (inlinePass body (inlineBindings binds s).2).1.1
        (inlinePass body (inlineBindings binds s).2).2).1.1 := by
      simp only [Moist.MIR.inlinePass.eq_1]; rfl
    rw [heq] at hw
    -- Goal: w ∈ freeVars (.Let binds body)
    -- hw: w ∈ freeVars (inlineLetBindings binds' body' s')
    -- Strategy: freeVars result ⊆ freeVarsLet binds' body' ⊆ freeVarsLet binds body
    -- Step 2: freeVarsLet binds' body' ⊆ freeVarsLet binds body
    -- This follows from IH on body + IH on each binding RHS
    have h_body_mono := freeVars_nonincreasing body (inlineBindings binds s).2
    -- Step 1: freeVars (inlineLetBindings ...) ⊆ freeVarsLet binds' body'
    have h_step1 := inlineLetBindings_fv_bound
      (inlineBindings binds s).1.1
      (inlinePass body (inlineBindings binds s).2).1.1
      (inlinePass body (inlineBindings binds s).2).2
      w hw
    -- Step 2: freeVarsLet binds' body' ⊆ freeVarsLet binds body (via mutual IH)
    rw [Moist.MIR.freeVars.eq_12]
    exact inlineBindings_freeVarsLet_mono binds s
      (inlinePass body (inlineBindings binds s).2).1.1 body h_body_mono w h_step1
termination_by sizeOf e

theorem freeVarsList_nonincreasing (es : List Expr) (s : Moist.MIR.FreshState) :
    ∀ w, (freeVarsList (inlinePassList es s).1.1).contains w = true →
         (freeVarsList es).contains w = true := by
  intro w hw
  match es with
  | [] =>
    rw [Moist.MIR.inlinePassList.eq_1] at hw; exact hw
  | e :: rest =>
    have heq : (inlinePassList (e :: rest) s).1.1 =
      (inlinePass e s).1.1 :: (inlinePassList rest (inlinePass e s).2).1.1 := by
      simp only [Moist.MIR.inlinePassList.eq_2]; rfl
    rw [heq] at hw
    rw [Moist.MIR.freeVarsList.eq_2] at hw
    rw [Moist.MIR.freeVarsList.eq_2]
    exact union_mono
      (freeVars_nonincreasing e s)
      (freeVarsList_nonincreasing rest (inlinePass e s).2)
      w hw
termination_by sizeOf es

theorem freeVarsBindings_nonincreasing (binds : List (VarId × Expr × Bool))
    (s : Moist.MIR.FreshState) :
    ∀ b ∈ (inlineBindings binds s).1.1, ∀ w,
      (freeVars b.2.1).contains w = true →
      ∃ b' ∈ binds, (freeVars b'.2.1).contains w = true := by
  intro b hb w hw
  match binds with
  | [] =>
    have heq : (inlineBindings ([] : List (VarId × Expr × Bool)) s).1.1 = [] := by
      rw [Moist.MIR.inlineBindings.eq_1]; rfl
    rw [heq] at hb; exact absurd hb (by simp)
  | (v, rhs, er) :: rest =>
    have heq : (inlineBindings ((v, rhs, er) :: rest) s).1.1 =
      (v, (inlinePass rhs s).1.1, er) :: (inlineBindings rest (inlinePass rhs s).2).1.1 := by
      simp only [Moist.MIR.inlineBindings.eq_2]; rfl
    rw [heq] at hb
    rcases List.mem_cons.mp hb with rfl | hb_rest
    · -- b = (v, (inlinePass rhs s).1.1, er)
      simp only at hw
      have := freeVars_nonincreasing rhs s w hw
      exact ⟨(v, rhs, er), List.mem_cons_self .., this⟩
    · -- b ∈ inlineBindings rest
      have ⟨b', hb'mem, hb'w⟩ := freeVarsBindings_nonincreasing rest (inlinePass rhs s).2
        b hb_rest w hw
      exact ⟨b', List.mem_cons_of_mem _ hb'mem, hb'w⟩
termination_by sizeOf binds

theorem inlineBindings_freeVarsLet_mono (binds : List (VarId × Expr × Bool))
    (s : Moist.MIR.FreshState) (body' body : Expr)
    (h_body : ∀ w, (freeVars body').contains w = true → (freeVars body).contains w = true) :
    ∀ w, (freeVarsLet (inlineBindings binds s).1.1 body').contains w = true →
         (freeVarsLet binds body).contains w = true := by
  match binds with
  | [] =>
    intro w hw
    have heq : (inlineBindings ([] : List (VarId × Expr × Bool)) s).1.1 = [] := by
      rw [Moist.MIR.inlineBindings.eq_1]; rfl
    rw [heq, Moist.MIR.freeVarsLet.eq_1] at hw
    rw [Moist.MIR.freeVarsLet.eq_1]
    exact h_body w hw
  | (v, rhs, er) :: rest =>
    intro w hw
    have heq : (inlineBindings ((v, rhs, er) :: rest) s).1.1 =
      (v, (inlinePass rhs s).1.1, er) :: (inlineBindings rest (inlinePass rhs s).2).1.1 := by
      simp only [Moist.MIR.inlineBindings.eq_2]; rfl
    rw [heq, Moist.MIR.freeVarsLet.eq_2] at hw
    rw [Moist.MIR.freeVarsLet.eq_2]
    exact union_mono
      (freeVars_nonincreasing rhs s)
      (fun w h => erase_mono
        (inlineBindings_freeVarsLet_mono rest (inlinePass rhs s).2 body' body h_body) w h)
      w hw
termination_by sizeOf binds
end

theorem inlinePass_fvsub (fv : VarSet) (e : Expr) (s : Moist.MIR.FreshState)
    (hfv : FVSub fv e) : FVSub fv (inlinePass e s).1.1 :=
  fun w hw => hfv w (freeVars_nonincreasing e s w hw)

theorem inlineBindings_fvsub (fv : VarSet) (binds : List (VarId × Expr × Bool))
    (s : Moist.MIR.FreshState) (hfv : ∀ b ∈ binds, FVSub fv b.2.1) :
    ∀ b ∈ (inlineBindings binds s).1.1, FVSub fv b.2.1 := by
  intro b hb w hw
  have ⟨b', hb'mem, hb'w⟩ := freeVarsBindings_nonincreasing binds s b hb w hw
  exact hfv b' hb'mem w hb'w

--------------------------------------------------------------------------------
-- NC preservation through inlinePass
--------------------------------------------------------------------------------

-- NC of App from components (reverse of noCaptureFrom_app)
private theorem noCaptureFrom_mk_app (fv : VarSet) (f x : Expr)
    (hf : noCaptureFrom fv f = true) (hx : noCaptureFrom fv x = true) :
    noCaptureFrom fv (.App f x) = true := by
  simp only [noCaptureFrom, Bool.and_eq_true]; exact ⟨hf, hx⟩

-- betaReduce NC helper
private theorem betaReduce_nc (fv : VarSet) (f x : Expr) (s : Moist.MIR.FreshState)
    (hnc_f : NC fv f) (hnc_x : NC fv x)
    (h_nr : noCaptureFrom (Moist.MIR.freeVars x) f = true) :
    NC fv (betaReduce f x s).1.1 := by
  -- Show that betaReduce either returns subst result or App f x
  -- In either case, NC fv is preserved
  have h_app : noCaptureFrom fv (.App f x) = true :=
    noCaptureFrom_mk_app fv f x hnc_f hnc_x
  unfold betaReduce
  match f with
  | .Lam param body =>
    simp only []
    by_cases hatom : x.isAtom = true
    · simp only [hatom, ite_true, bind, StateT.bind, pure, StateT.pure]
      have ⟨_, h_body⟩ := noCaptureFrom_lam hnc_f
      have ⟨_, h_nr_body⟩ := noCaptureFrom_lam h_nr
      exact noCaptureFrom_subst fv param x body s h_body hnc_x h_nr_body
    · simp only [Bool.not_eq_true] at hatom
      simp only [hatom, pure]
      exact h_app
  | .Var _ => exact h_app
  | .Lit _ => exact h_app
  | .Builtin _ => exact h_app
  | .Error => exact h_app
  | .Fix _ _ => exact h_app
  | .App _ _ => exact h_app
  | .Force _ => exact h_app
  | .Delay _ => exact h_app
  | .Constr _ _ => exact h_app
  | .Case _ _ => exact h_app
  | .Let _ _ => exact h_app

-- noCaptureFromLet decomposition (needed before the mutual block)
private theorem noCaptureFromLet_implies_body' (fv : VarSet)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (h : noCaptureFromLet fv binds body = true) : NC fv body := by
  induction binds with
  | nil => unfold noCaptureFromLet at h; exact h
  | cons b rest ih => exact ih (noCaptureFromLet_cons h).2.2

private theorem noCaptureFromLet_implies_rhss' (fv : VarSet)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (h : noCaptureFromLet fv binds body = true) :
    ∀ b ∈ binds, NC fv b.2.1 := by
  induction binds with
  | nil => intro b hb; exact absurd hb (by simp)
  | cons bd rest ih =>
    intro b hb; rcases List.mem_cons.mp hb with rfl | hb
    · exact (noCaptureFromLet_cons h).2.1
    · exact ih (noCaptureFromLet_cons h).2.2 b hb

private theorem noCaptureFromLet_implies_names' (fv : VarSet)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (h : noCaptureFromLet fv binds body = true) :
    ∀ b ∈ binds, fv.contains b.1 = false :=
  noCaptureFromLet_implies_names_local fv binds body h

-- Binding names preserved through inlineBindings (needed before the mutual block)
private theorem inlineBindings_names' (_fv : VarSet)
    (binds : List (VarId × Expr × Bool)) (s : Moist.MIR.FreshState)
    (hnames : ∀ b ∈ binds, _fv.contains b.1 = false) :
    ∀ b ∈ (inlineBindings binds s).1.1, _fv.contains b.1 = false := by
  induction binds generalizing s with
  | nil => intro b hb; simp only [inlineBindings, pure, StateT.pure, List.not_mem_nil] at hb
  | cons bd rest ih =>
    obtain ⟨w, e, er⟩ := bd
    intro b hb; simp only [inlineBindings, bind, StateT.bind] at hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hnames (w, e, er) (List.mem_cons_self ..)
    · exact ih (inlinePass e s).2
              (fun b' hb' => hnames b' (List.mem_cons_of_mem _ hb')) b hb

-- substInBindings preserves NC and names (needed before the mutual block)
private theorem substInBindings_nc_names' (fv : VarSet) (v : VarId) (rhs : Expr)
    (binds : List (VarId × Expr × Bool)) (s : Moist.MIR.FreshState)
    (hnc_rhs : NC fv rhs) (hnc_binds : ∀ b ∈ binds, NC fv b.2.1)
    (hnames : ∀ b ∈ binds, fv.contains b.1 = false)
    (hnr : ∀ b ∈ binds, noCaptureFrom (freeVars rhs) b.2.1 = true) :
    (∀ b ∈ (substInBindings v rhs binds s).1.val, NC fv b.2.1) ∧
    (∀ b ∈ (substInBindings v rhs binds s).1.val, fv.contains b.1 = false) := by
  induction binds generalizing s with
  | nil =>
    simp only [substInBindings, pure, StateT.pure]
    exact ⟨fun b hb => absurd hb (by simp), fun b hb => absurd hb (by simp)⟩
  | cons bd rest ih =>
    obtain ⟨w, e, er⟩ := bd
    simp only [substInBindings, bind, StateT.bind]
    have ⟨ih_nc, ih_names⟩ := ih (subst v rhs e s).2
      (fun b hb => hnc_binds b (List.mem_cons_of_mem _ hb))
      (fun b hb => hnames b (List.mem_cons_of_mem _ hb))
      (fun b hb => hnr b (List.mem_cons_of_mem _ hb))
    exact ⟨fun b hb => by
        rcases List.mem_cons.mp hb with rfl | hb
        · exact noCaptureFrom_subst fv v rhs e s
            (hnc_binds (w,e,er) (List.mem_cons_self ..)) hnc_rhs
            (hnr (w,e,er) (List.mem_cons_self ..))
        · exact ih_nc b hb,
      fun b hb => by
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hnames (w, e, er) (List.mem_cons_self ..)
        · exact ih_names b hb⟩

-- NC reconstruction for Let
private theorem noCaptureFrom_mk_let (fv : VarSet)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (h_body : NC fv body) (h_rhss : ∀ b ∈ binds, NC fv b.2.1)
    (h_names : ∀ b ∈ binds, fv.contains b.1 = false) :
    noCaptureFromLet fv binds body = true := by
  induction binds with
  | nil => simp only [noCaptureFromLet]; exact h_body
  | cons bd rest ih =>
    obtain ⟨v, rhs, er⟩ := bd
    simp only [noCaptureFromLet, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨⟨h_names (v, rhs, er) (List.mem_cons_self ..),
            h_rhss (v, rhs, er) (List.mem_cons_self ..)⟩,
           ih (fun b hb => h_rhss b (List.mem_cons_of_mem _ hb))
              (fun b hb => h_names b (List.mem_cons_of_mem _ hb))⟩

-- substInBindings reverse NC and cross-NC (copies needed before inlineLetGo_nc)
private theorem substInBindings_all_nc_rev_pre (v : VarId) (rhs e_tgt : Expr)
    (rest : List (VarId × Expr × Bool)) (s_tgt s₀ : Moist.MIR.FreshState)
    (h_nc_tgt : ∀ b ∈ rest, noCaptureFrom (freeVars b.2.1) e_tgt = true)
    (h_nc_rhs_rest : ∀ b ∈ rest, noCaptureFrom (freeVars rhs) b.2.1 = true)
    (h_rest_rev : ∀ b ∈ rest, noCaptureFrom (freeVars b.2.1) rhs = true)
    (h_nc_rhs_self : noCaptureFrom (freeVars rhs) rhs = true)
    (h_no_rename_tgt : noCaptureFrom (freeVars rhs) e_tgt = true) :
    ∀ b ∈ (substInBindings v rhs rest s₀).1.val,
      noCaptureFrom (freeVars b.2.1) (subst v rhs e_tgt s_tgt).1 = true := by
  intro b hb
  induction rest generalizing s₀ with
  | nil => simp only [substInBindings, pure, StateT.pure] at hb; exact absurd hb (by simp)
  | cons bd rest_tail ih =>
    obtain ⟨w', rhs', er'⟩ := bd
    simp only [substInBindings, bind, StateT.bind] at hb
    rcases List.mem_cons.mp hb with rfl | hb_tail
    · exact nc_subst_via_bound v rhs e_tgt rhs' s_tgt _
        (h_nc_tgt (w', rhs', er') (List.mem_cons_self ..))
        h_no_rename_tgt
        (h_rest_rev (w', rhs', er') (List.mem_cons_self ..))
        h_nc_rhs_self h_no_rename_tgt
        (h_nc_rhs_rest (w', rhs', er') (List.mem_cons_self ..))
    · exact ih _ (fun b hb => h_nc_tgt b (List.mem_cons_of_mem _ hb))
               (fun b hb => h_nc_rhs_rest b (List.mem_cons_of_mem _ hb))
               (fun b hb => h_rest_rev b (List.mem_cons_of_mem _ hb)) hb_tail

private theorem substInBindings_cross_nc_pre (v : VarId) (rhs : Expr)
    (binds : List (VarId × Expr × Bool)) (s : Moist.MIR.FreshState)
    (h_cross : ∀ b₁ ∈ binds, ∀ b₂ ∈ binds, noCaptureFrom (freeVars b₁.2.1) b₂.2.1 = true)
    (h_rhs_self : noCaptureFrom (freeVars rhs) rhs = true)
    (h_rhs_cross : ∀ b ∈ binds, noCaptureFrom (freeVars rhs) b.2.1 = true)
    (h_rhs_rev : ∀ b ∈ binds, noCaptureFrom (freeVars b.2.1) rhs = true) :
    ∀ b₁ ∈ (substInBindings v rhs binds s).1.val,
      ∀ b₂ ∈ (substInBindings v rhs binds s).1.val,
        noCaptureFrom (freeVars b₁.2.1) b₂.2.1 = true := by
  intro b₁ hb₁ b₂ hb₂
  induction binds generalizing s with
  | nil => simp only [substInBindings, pure, StateT.pure] at hb₁; exact absurd hb₁ (by simp)
  | cons bd rest ih =>
    obtain ⟨w, e, er⟩ := bd
    simp only [substInBindings, bind, StateT.bind] at hb₁ hb₂
    have h_nc_e := h_rhs_cross (w, e, er) (List.mem_cons_self ..)
    have h_rev_e := h_rhs_rev (w, e, er) (List.mem_cons_self ..)
    rcases List.mem_cons.mp hb₁ with rfl | hb₁_tail <;>
      rcases List.mem_cons.mp hb₂ with rfl | hb₂_tail
    · exact nc_subst_via_bound v rhs e e s s
        (h_cross (w,e,er) (List.mem_cons_self ..) (w,e,er) (List.mem_cons_self ..))
        h_nc_e h_rev_e h_rhs_self h_nc_e h_nc_e
    · have hall := substInBindings_all_nc v rhs e rest s (subst v rhs e s).2
        (fun b hb => h_cross (w,e,er) (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb))
        (fun b hb => h_rhs_cross b (List.mem_cons_of_mem _ hb))
        h_rev_e h_rhs_self h_nc_e
      rw [List.all_eq_true] at hall; exact hall b₂ hb₂_tail
    · exact substInBindings_all_nc_rev_pre v rhs e rest s _
        (fun b hb => h_cross b (List.mem_cons_of_mem _ hb) (w,e,er) (List.mem_cons_self ..))
        (fun b hb => h_rhs_cross b (List.mem_cons_of_mem _ hb))
        (fun b hb => h_rhs_rev b (List.mem_cons_of_mem _ hb))
        h_rhs_self h_nc_e b₁ hb₁_tail
    · exact ih _ (fun b₁ hb₁ b₂ hb₂ =>
          h_cross b₁ (List.mem_cons_of_mem _ hb₁) b₂ (List.mem_cons_of_mem _ hb₂))
        (fun b hb => h_rhs_cross b (List.mem_cons_of_mem _ hb))
        (fun b hb => h_rhs_rev b (List.mem_cons_of_mem _ hb))
        hb₁_tail hb₂_tail

-- inlineLetGo NC preservation
private theorem inlineLetGo_nc (fv : VarSet)
    (binds : List (VarId × Expr × Bool))
    (acc : List (VarId × Expr × Bool))
    (body : Expr) (changed : Bool) (s : Moist.MIR.FreshState)
    (h_body : NC fv body)
    (h_binds : ∀ b ∈ binds, NC fv b.2.1)
    (h_acc : ∀ b ∈ acc, NC fv b.2.1)
    (h_names_binds : ∀ b ∈ binds, fv.contains b.1 = false)
    (h_names_acc : ∀ b ∈ acc, fv.contains b.1 = false)
    (h_nr : ∀ b ∈ binds, noCaptureFrom (Moist.MIR.freeVars b.2.1) body = true)
    (h_nr_binds : ∀ b₁ ∈ binds, ∀ b₂ ∈ binds,
      noCaptureFrom (Moist.MIR.freeVars b₁.2.1) b₂.2.1 = true) :
    NC fv (inlineLetGo binds acc body changed s).1.1 := by
  match binds with
  | [] =>
    rw [Moist.MIR.inlineLetGo.eq_1]
    cases hacc : acc.reverse with
    | nil => simp only [pure, StateT.pure]; exact h_body
    | cons s' rest' =>
      simp only [pure, StateT.pure]
      show noCaptureFrom fv (.Let (s' :: rest') body) = true
      simp only [noCaptureFrom]
      have hmem : ∀ b ∈ s' :: rest', b ∈ acc := by
        intro b hb
        have h1 : b ∈ (s' :: rest') := hb
        have h2 : (s' :: rest') = acc.reverse := hacc.symm
        rw [h2] at h1; exact List.mem_reverse.mp h1
      have h_rev_acc : ∀ b ∈ s' :: rest', NC fv b.2.1 :=
        fun b hb => h_acc b (hmem b hb)
      have h_rev_names : ∀ b ∈ s' :: rest', fv.contains b.1 = false :=
        fun b hb => h_names_acc b (hmem b hb)
      exact noCaptureFrom_mk_let fv (s' :: rest') body h_body h_rev_acc h_rev_names
  | (v, rhs, er) :: rest =>
    rw [Moist.MIR.inlineLetGo.eq_2]
    simp only [bind, StateT.bind]
    have h_nc_rhs := h_binds (v, rhs, er) (List.mem_cons_self ..)
    have h_name_v := h_names_binds (v, rhs, er) (List.mem_cons_self ..)
    have h_nr_body := h_nr (v, rhs, er) (List.mem_cons_self ..)
    have h_nc_rest := fun b hb => h_binds b (List.mem_cons_of_mem _ hb)
    have h_names_rest := fun b hb => h_names_binds b (List.mem_cons_of_mem _ hb)
    have h_nr_rest := fun b hb => h_nr b (List.mem_cons_of_mem _ hb)
    have h_nr_binds_rest := fun b₁ hb₁ b₂ hb₂ =>
      h_nr_binds b₁ (List.mem_cons_of_mem _ hb₁) b₂ (List.mem_cons_of_mem _ hb₂)
    by_cases hinline : (shouldInline rhs
        (Moist.MIR.countOccurrences v body +
          rest.foldl (fun n (_, e, _) => n + Moist.MIR.countOccurrences v e) 0)
        (Moist.MIR.occursUnderFix v body ||
          rest.any (fun (_, e, _) => Moist.MIR.occursUnderFix v e))
        (Moist.MIR.occursInDeferred v body ||
          rest.any (fun (_, e, _) => Moist.MIR.occursInDeferred v e))) = true
    · -- Inline case: substitute rhs for v in body and rest
      simp only [hinline, ↓reduceIte]
      have h_nr_rest_all : ∀ b ∈ rest, noCaptureFrom (freeVars rhs) b.2.1 = true :=
        fun b hb => h_nr_binds (v, rhs, er) (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb)
      have h_nc_rhs_self := h_nr_binds (v, rhs, er) (List.mem_cons_self ..) (v, rhs, er) (List.mem_cons_self ..)
      have h_body' := noCaptureFrom_subst fv v rhs body s h_body h_nc_rhs h_nr_body
      have ⟨h_rest_nc, h_rest_names⟩ := substInBindings_nc_names' fv v rhs rest
        (subst v rhs body s).2 h_nc_rhs h_nc_rest h_names_rest h_nr_rest_all
      have h_rev_rest : ∀ b ∈ rest, noCaptureFrom (freeVars b.2.1) rhs = true :=
        fun b hb => h_nr_binds b (List.mem_cons_of_mem _ hb) (v, rhs, er) (List.mem_cons_self ..)
      have h_nr_body' := substInBindings_all_nc_rev_pre
          v rhs body rest s (subst v rhs body s).2
          (fun b hb => h_nr b (List.mem_cons_of_mem _ hb))
          h_nr_rest_all h_rev_rest h_nc_rhs_self h_nr_body
      have h_cross' := substInBindings_cross_nc_pre
          v rhs rest (subst v rhs body s).2
          h_nr_binds_rest h_nc_rhs_self h_nr_rest_all h_rev_rest
      have hdec : (substInBindings v rhs rest (subst v rhs body s).2).1.val.length <
          ((v, rhs, er) :: rest).length := by
        simp only [List.length_cons, (substInBindings v rhs rest (subst v rhs body s).2).1.property]; omega
      exact inlineLetGo_nc fv _ acc _ true _ h_body' h_rest_nc h_acc h_rest_names h_names_acc
        h_nr_body' h_cross'
    · -- Keep case: move binding to acc
      have hinline' : (shouldInline rhs
          (Moist.MIR.countOccurrences v body +
            rest.foldl (fun n (_, e, _) => n + Moist.MIR.countOccurrences v e) 0)
          (Moist.MIR.occursUnderFix v body ||
            rest.any (fun (_, e, _) => Moist.MIR.occursUnderFix v e))
          (Moist.MIR.occursInDeferred v body ||
            rest.any (fun (_, e, _) => Moist.MIR.occursInDeferred v e))) = false := by
        cases h : shouldInline rhs _ _ _ with | true => exact absurd h hinline | false => rfl
      simp only [hinline', Bool.false_eq_true, ↓reduceIte]
      exact inlineLetGo_nc fv rest ((v, rhs, er) :: acc) body changed s h_body
        h_nc_rest
        (fun b hb => by rcases List.mem_cons.mp hb with rfl | hb
                        · exact h_nc_rhs
                        · exact h_acc b hb)
        h_names_rest
        (fun b hb => by rcases List.mem_cons.mp hb with rfl | hb
                        · exact h_name_v
                        · exact h_names_acc b hb)
        h_nr_rest h_nr_binds_rest
  termination_by binds.length

-- inlineLetBindings NC preservation
private theorem inlineLetBindings_nc (fv : VarSet)
    (binds : List (VarId × Expr × Bool)) (body : Expr) (s : Moist.MIR.FreshState)
    (h_body : NC fv body)
    (h_binds : ∀ b ∈ binds, NC fv b.2.1)
    (h_names : ∀ b ∈ binds, fv.contains b.1 = false)
    (h_nr : ∀ b ∈ binds, noCaptureFrom (Moist.MIR.freeVars b.2.1) body = true)
    (h_nr_binds : ∀ b₁ ∈ binds, ∀ b₂ ∈ binds,
      noCaptureFrom (Moist.MIR.freeVars b₁.2.1) b₂.2.1 = true) :
    NC fv (inlineLetBindings binds body s).1.1 := by
  unfold inlineLetBindings
  exact inlineLetGo_nc fv binds [] body false s h_body h_binds
    (fun _ hb => by simp at hb)
    h_names
    (fun _ hb => by simp at hb)
    h_nr h_nr_binds

mutual
theorem inlinePass_nc (fv : VarSet) (e : Expr) (s : Moist.MIR.FreshState)
    (hnc : NC fv e) (hws : wellScoped e = true) :
    NC fv (inlinePass e s).1.1 := by
  match e with
  | .Var v =>
    rw [inlinePass_leaf_eq (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)]
    exact hnc
  | .Lit c =>
    rw [inlinePass_leaf_eq (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)]
    exact hnc
  | .Builtin b =>
    rw [inlinePass_leaf_eq (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)]
    exact hnc
  | .Error =>
    rw [inlinePass_leaf_eq (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)
      (by intros; intro h; cases h) (by intros; intro h; cases h)]
    exact hnc
  | .Lam x body =>
    have heq : (inlinePass (.Lam x body) s).1.1 = .Lam x (inlinePass body s).1.1 := by
      simp only [Moist.MIR.inlinePass.eq_2]; rfl
    rw [heq]; show noCaptureFrom fv (.Lam x (inlinePass body s).1.1) = true
    have ⟨hx, hbody⟩ := noCaptureFrom_lam hnc
    have hws_body := wellScoped_sub_lam hws
    simp only [noCaptureFrom, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨hx, inlinePass_nc fv body s hbody hws_body⟩
  | .Fix f body =>
    have heq : (inlinePass (.Fix f body) s).1.1 = .Fix f (inlinePass body s).1.1 := by
      simp only [Moist.MIR.inlinePass.eq_3]; rfl
    rw [heq]; show noCaptureFrom fv (.Fix f (inlinePass body s).1.1) = true
    have ⟨hf, hbody⟩ := noCaptureFrom_fix hnc
    have hws_body := wellScoped_sub_fix hws
    simp only [noCaptureFrom, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨hf, inlinePass_nc fv body s hbody hws_body⟩
  | .Force inner =>
    have heq : (inlinePass (.Force inner) s).1.1 = .Force (inlinePass inner s).1.1 := by
      simp only [Moist.MIR.inlinePass.eq_5]; rfl
    rw [heq]; show noCaptureFrom fv (.Force (inlinePass inner s).1.1) = true
    have h_inner := noCaptureFrom_force hnc
    have hws_inner := wellScoped_sub_force hws
    simp only [noCaptureFrom]
    exact inlinePass_nc fv inner s h_inner hws_inner
  | .Delay inner =>
    have heq : (inlinePass (.Delay inner) s).1.1 = .Delay (inlinePass inner s).1.1 := by
      simp only [Moist.MIR.inlinePass.eq_6]; rfl
    rw [heq]; show noCaptureFrom fv (.Delay (inlinePass inner s).1.1) = true
    have h_inner := noCaptureFrom_delay hnc
    have hws_inner := wellScoped_sub_delay hws
    simp only [noCaptureFrom]
    exact inlinePass_nc fv inner s h_inner hws_inner
  | .Constr tag args =>
    have heq : (inlinePass (.Constr tag args) s).1.1 =
      .Constr tag (inlinePassList args s).1.1 := by
      simp only [Moist.MIR.inlinePass.eq_7]; rfl
    rw [heq]; show noCaptureFrom fv (.Constr tag (inlinePassList args s).1.1) = true
    have h_args := noCaptureFrom_constr hnc
    have ⟨_, hws_args⟩ := wellScoped_sub_constr hws
    simp only [noCaptureFrom]
    exact inlinePassList_nc fv args s h_args hws_args
  | .Case scrut alts =>
    have heq : (inlinePass (.Case scrut alts) s).1.1 =
      .Case (inlinePass scrut s).1.1
            (inlinePassList alts (inlinePass scrut s).2).1.1 := by
      simp only [Moist.MIR.inlinePass.eq_8]; rfl
    rw [heq]
    show noCaptureFrom fv (.Case (inlinePass scrut s).1.1
      (inlinePassList alts (inlinePass scrut s).2).1.1) = true
    have ⟨hnc_s, hnc_a⟩ := noCaptureFrom_case hnc
    have ⟨hws_s, _, hws_a⟩ := wellScoped_sub_case hws
    simp only [noCaptureFrom, Bool.and_eq_true]
    exact ⟨inlinePass_nc fv scrut s hnc_s hws_s,
           inlinePassList_nc fv alts (inlinePass scrut s).2 hnc_a hws_a⟩
  | .App f x =>
    have heq : (inlinePass (.App f x) s).1.1 =
      (betaReduce (inlinePass f s).1.1
        (inlinePass x (inlinePass f s).2).1.1
        (inlinePass x (inlinePass f s).2).2).1.1 := by
      simp only [Moist.MIR.inlinePass.eq_4]; rfl
    rw [heq]
    have ⟨hnc_f, hnc_x⟩ := noCaptureFrom_app hnc
    have ⟨hws_f, hws_x⟩ := wellScoped_sub_app hws
    -- NC fv for the inlined sub-expressions
    have ih_f := inlinePass_nc fv f s hnc_f hws_f
    have ih_x := inlinePass_nc fv x (inlinePass f s).2 hnc_x hws_x
    -- NC (freeVars x) for f, from wellScoped: freeVars x ⊆ freeVars (.App f x)
    -- and NC (freeVars (.App f x)) f
    have h_ws_nc := wellScoped_noCaptureFrom hws
    have h_nc_fvx_f : noCaptureFrom (Moist.MIR.freeVars x) f = true :=
      noCaptureFrom_mono (Moist.MIR.freeVars (.App f x)) (Moist.MIR.freeVars x) f
        (noCaptureFrom_app h_ws_nc).1
        (fun w hw => by rw [Moist.MIR.freeVars.eq_7]; exact contains_union_right _ _ _ hw)
    -- IH: NC (freeVars x) on the inlined f
    have ih_fvx_f := inlinePass_nc (Moist.MIR.freeVars x) f s h_nc_fvx_f hws_f
    -- freeVars of inlined x ⊆ freeVars of original x
    have h_fv_mono := freeVars_nonincreasing x (inlinePass f s).2
    -- NC (freeVars x') f' by monotonicity
    have h_nr : noCaptureFrom (Moist.MIR.freeVars (inlinePass x (inlinePass f s).2).1.1)
        (inlinePass f s).1.1 = true :=
      noCaptureFrom_mono (Moist.MIR.freeVars x)
        (Moist.MIR.freeVars (inlinePass x (inlinePass f s).2).1.1)
        (inlinePass f s).1.1 ih_fvx_f h_fv_mono
    exact betaReduce_nc fv _ _ _ ih_f ih_x h_nr
  | .Let binds body =>
    have heq : (inlinePass (.Let binds body) s).1.1 =
      (inlineLetBindings (inlineBindings binds s).1.1
        (inlinePass body (inlineBindings binds s).2).1.1
        (inlinePass body (inlineBindings binds s).2).2).1.1 := by
      simp only [Moist.MIR.inlinePass.eq_1]; rfl
    rw [heq]
    have h_let_nc := noCaptureFrom_let hnc
    have h_body_nc := noCaptureFromLet_implies_body' fv binds body h_let_nc
    have h_rhss_nc := noCaptureFromLet_implies_rhss' fv binds body h_let_nc
    have h_names := noCaptureFromLet_implies_names' fv binds body h_let_nc
    have ⟨hws_body, _, hws_binds⟩ := wellScoped_sub_let hws
    have h_body'_nc := inlinePass_nc fv body (inlineBindings binds s).2 h_body_nc hws_body
    have h_binds'_nc := inlineBindings_nc fv binds s h_rhss_nc hws_binds
    have h_names' := inlineBindings_names' fv binds s h_names
    have hpc_orig := pairwiseNC_of_wellScoped binds body hws
    have hnc_ws := wellScoped_noCaptureFrom hws
    have h_fvlet := noCaptureFrom_let hnc_ws
    simp only [Moist.MIR.freeVars] at h_fvlet
    have h_fv_names := noCaptureFromLet_implies_names_local _ _ body h_fvlet
    have h_fv_rhss := noCaptureFromLet_implies_rhss' _ _ body h_fvlet
    have h_nr : ∀ b ∈ (inlineBindings binds s).1.1,
        noCaptureFrom (Moist.MIR.freeVars b.2.1)
          (inlinePass body (inlineBindings binds s).2).1.1 = true := by
      intro b hb
      suffices ∀ (bs : List (VarId × Expr × Bool)) (s₀ : Moist.MIR.FreshState),
          (∀ b ∈ bs, noCaptureFrom (Moist.MIR.freeVars b.2.1) body = true) →
          (∀ b ∈ bs, wellScoped b.2.1 = true) →
          b ∈ (inlineBindings bs s₀).1.1 →
          noCaptureFrom (Moist.MIR.freeVars b.2.1) (inlinePass body (inlineBindings binds s).2).1.1 = true from
        this binds s
          (fun b hb => by
            have hpc_unf := hpc_orig
            suffices ∀ (bs : List _), PairwiseNC bs body → b ∈ bs →
                noCaptureFrom (Moist.MIR.freeVars b.2.1) body = true from
              this binds hpc_unf hb
            intro bs hpc hbm
            induction bs with
            | nil => exact absurd hbm (by simp)
            | cons _ _ ih => rcases List.mem_cons.mp hbm with rfl | h
                             · exact hpc.1
                             · exact ih hpc.2.2.2 h)
          hws_binds hb
      intro bs s₀ h_nc_bs hws_bs hb_bs
      induction bs generalizing s₀ with
      | nil => simp only [inlineBindings, pure, StateT.pure] at hb_bs; exact absurd hb_bs (by simp)
      | cons bd rest ih =>
        obtain ⟨w, rhs_w, er_w⟩ := bd
        simp only [inlineBindings, bind, StateT.bind] at hb_bs
        rcases List.mem_cons.mp hb_bs with rfl | hb_rest
        · exact noCaptureFrom_mono _ _ _ (inlinePass_nc _ body _
            (h_nc_bs (w, rhs_w, er_w) (List.mem_cons_self ..)) hws_body)
            (freeVars_nonincreasing rhs_w s₀)
        · exact ih _ (fun b hb => h_nc_bs b (List.mem_cons_of_mem _ hb))
                   (fun b hb => hws_bs b (List.mem_cons_of_mem _ hb)) hb_rest
    have h_orig_cross := wellScoped_let_cross_nc hws
    -- For each b₁ in processed bindings, NC (freeVars b₁.2.1) b₂.2.1:
    -- Use inlineBindings_nc (mutual) with freeVars of the ORIGINAL b₁ RHS,
    -- then mono down using freeVars_nonincreasing.
    -- The key: inlineBindings_nc gives NC for any fv, including freeVars of any original RHS.
    -- We derive the original RHS's freeVars condition from h_orig_cross.
    have h_cross : ∀ b₁ ∈ (inlineBindings binds s).1.1,
        ∀ b₂ ∈ (inlineBindings binds s).1.1,
          noCaptureFrom (freeVars b₁.2.1) b₂.2.1 = true := by
      -- For every original b_orig ∈ binds, NC (freeVars b_orig.2.1) b₂.2.1 for all b₂ in output
      have h_all_nc : ∀ b_orig ∈ binds, ∀ b₂ ∈ (inlineBindings binds s).1.1,
          noCaptureFrom (Moist.MIR.freeVars b_orig.2.1) b₂.2.1 = true :=
        fun b_orig hb_orig => inlineBindings_nc (Moist.MIR.freeVars b_orig.2.1) binds s
          (fun b hb => h_orig_cross b_orig hb_orig b hb) hws_binds
      -- For each b₁ in output, freeVars b₁.2.1 ⊆ freeVars of its original (by freeVars_nonincreasing)
      -- Use induction on binds to match b₁ with its original
      intro b₁ hb₁ b₂ hb₂
      suffices ∀ (bs : List _) (s₀ : Moist.MIR.FreshState),
          (∀ b_orig ∈ bs, ∀ b₂ ∈ (inlineBindings binds s).1.1,
            noCaptureFrom (Moist.MIR.freeVars b_orig.2.1) b₂.2.1 = true) →
          b₁ ∈ (inlineBindings bs s₀).1.1 →
          noCaptureFrom (freeVars b₁.2.1) b₂.2.1 = true from
        this binds s (fun b_orig hb => h_all_nc b_orig hb) hb₁
      intro bs s₀ h_all hb₁_bs
      induction bs generalizing s₀ with
      | nil => simp only [inlineBindings, pure, StateT.pure] at hb₁_bs; exact absurd hb₁_bs (by simp)
      | cons bd rest ih =>
        obtain ⟨w, rhs_w, er_w⟩ := bd
        simp only [inlineBindings, bind, StateT.bind] at hb₁_bs
        rcases List.mem_cons.mp hb₁_bs with rfl | hb₁_rest
        · -- b₁ = processed head: freeVars b₁.2.1 ⊆ freeVars rhs_w (by freeVars_nonincreasing)
          exact noCaptureFrom_mono _ _ _
            (h_all (w, rhs_w, er_w) (List.mem_cons_self ..) b₂ hb₂)
            (freeVars_nonincreasing rhs_w s₀)
        · exact ih _ (fun b_orig hb => h_all b_orig (List.mem_cons_of_mem _ hb)) hb₁_rest
    exact inlineLetBindings_nc fv _ _ _ h_body'_nc h_binds'_nc h_names' h_nr h_cross
termination_by sizeOf e
theorem inlinePassList_nc (fv : VarSet) (es : List Expr) (s : Moist.MIR.FreshState)
    (hnc : noCaptureFromList fv es = true) (hws : ∀ e ∈ es, wellScoped e = true) :
    noCaptureFromList fv (inlinePassList es s).1.1 = true := by
  match es with
  | [] =>
    have heq : (inlinePassList ([] : List Expr) s).1.1 = [] := by
      rw [Moist.MIR.inlinePassList.eq_1]; rfl
    rw [heq]; simp only [noCaptureFromList]
  | e :: rest =>
    have heq : (inlinePassList (e :: rest) s).1.1 =
      (inlinePass e s).1.1 :: (inlinePassList rest (inlinePass e s).2).1.1 := by
      simp only [Moist.MIR.inlinePassList.eq_2]; rfl
    rw [heq]
    have ⟨hnc_e, hnc_rest⟩ := noCaptureFromList_cons hnc
    show noCaptureFromList fv ((inlinePass e s).1.1 ::
      (inlinePassList rest (inlinePass e s).2).1.1) = true
    simp only [noCaptureFromList, Bool.and_eq_true]
    exact ⟨inlinePass_nc fv e s hnc_e (hws e (List.mem_cons_self ..)),
           inlinePassList_nc fv rest (inlinePass e s).2 hnc_rest
             (fun e' he' => hws e' (List.mem_cons_of_mem _ he'))⟩
termination_by sizeOf es
theorem inlineBindings_nc (fv : VarSet) (binds : List (VarId × Expr × Bool))
    (s : Moist.MIR.FreshState) (hnc : ∀ b ∈ binds, NC fv b.2.1)
    (hws : ∀ b ∈ binds, wellScoped b.2.1 = true) :
    ∀ b ∈ (inlineBindings binds s).1.1, NC fv b.2.1 := by
  match binds with
  | [] =>
    have heq : (inlineBindings ([] : List (VarId × Expr × Bool)) s).1.1 = [] := by
      rw [Moist.MIR.inlineBindings.eq_1]; rfl
    rw [heq]
    intro b hb; simp at hb
  | (v, rhs, er) :: rest =>
    have heq : (inlineBindings ((v, rhs, er) :: rest) s).1.1 =
      (v, (inlinePass rhs s).1.1, er) ::
        (inlineBindings rest (inlinePass rhs s).2).1.1 := by
      simp only [Moist.MIR.inlineBindings.eq_2]; rfl
    rw [heq]
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb_rest
    · exact inlinePass_nc fv rhs s
        (hnc (v, rhs, er) (List.mem_cons_self ..))
        (hws (v, rhs, er) (List.mem_cons_self ..))
    · exact inlineBindings_nc fv rest (inlinePass rhs s).2
        (fun b' hb' => hnc b' (List.mem_cons_of_mem _ hb'))
        (fun b' hb' => hws b' (List.mem_cons_of_mem _ hb'))
        b hb_rest
termination_by sizeOf binds
end

--------------------------------------------------------------------------------
-- Binding names preserved through inlineBindings
--------------------------------------------------------------------------------

theorem inlineBindings_names (_fv : VarSet) (binds : List (VarId × Expr × Bool))
    (s : Moist.MIR.FreshState) (hnames : ∀ b ∈ binds, _fv.contains b.1 = false) :
    ∀ b ∈ (inlineBindings binds s).1.1, _fv.contains b.1 = false := by
  induction binds generalizing s with
  | nil => intro b hb; simp only [inlineBindings, pure, StateT.pure, List.not_mem_nil] at hb
  | cons bd rest ih =>
    obtain ⟨w, e, er⟩ := bd
    intro b hb; simp only [inlineBindings, bind, StateT.bind] at hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hnames (w, e, er) (List.mem_cons_self ..)
    · exact ih (inlinePass e s).2
              (fun b' hb' => hnames b' (List.mem_cons_of_mem _ hb')) b hb

--------------------------------------------------------------------------------
-- substInBindings preserves NC and names
--------------------------------------------------------------------------------

theorem substInBindings_nc_names (fv : VarSet) (v : VarId) (rhs : Expr)
    (binds : List (VarId × Expr × Bool)) (s : Moist.MIR.FreshState)
    (hnc_rhs : NC fv rhs) (hnc_binds : ∀ b ∈ binds, NC fv b.2.1)
    (hnames : ∀ b ∈ binds, fv.contains b.1 = false)
    (hnr : ∀ b ∈ binds, noCaptureFrom (freeVars rhs) b.2.1 = true) :
    (∀ b ∈ (substInBindings v rhs binds s).1.val, NC fv b.2.1) ∧
    (∀ b ∈ (substInBindings v rhs binds s).1.val, fv.contains b.1 = false) := by
  induction binds generalizing s with
  | nil =>
    simp only [substInBindings, pure, StateT.pure]
    exact ⟨fun b hb => absurd hb (by simp), fun b hb => absurd hb (by simp)⟩
  | cons bd rest ih =>
    obtain ⟨w, e, er⟩ := bd
    simp only [substInBindings, bind, StateT.bind]
    have ⟨ih_nc, ih_names⟩ := ih (subst v rhs e s).2
      (fun b hb => hnc_binds b (List.mem_cons_of_mem _ hb))
      (fun b hb => hnames b (List.mem_cons_of_mem _ hb))
      (fun b hb => hnr b (List.mem_cons_of_mem _ hb))
    exact ⟨fun b hb => by
        rcases List.mem_cons.mp hb with rfl | hb
        · exact noCaptureFrom_subst fv v rhs e s
            (hnc_binds (w,e,er) (List.mem_cons_self ..)) hnc_rhs
            (hnr (w,e,er) (List.mem_cons_self ..))
        · exact ih_nc b hb,
      fun b hb => by
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hnames (w, e, er) (List.mem_cons_self ..)
        · exact ih_names b hb⟩

--------------------------------------------------------------------------------
-- noCaptureFromLet decomposition helpers
--------------------------------------------------------------------------------

theorem noCaptureFromLet_implies_body (fv : VarSet) (binds : List (VarId × Expr × Bool))
    (body : Expr) (h : noCaptureFromLet fv binds body = true) : NC fv body := by
  induction binds with
  | nil => unfold noCaptureFromLet at h; exact h
  | cons b rest ih => exact ih (noCaptureFromLet_cons h).2.2

theorem noCaptureFromLet_implies_rhss (fv : VarSet) (binds : List (VarId × Expr × Bool))
    (body : Expr) (h : noCaptureFromLet fv binds body = true) :
    ∀ b ∈ binds, NC fv b.2.1 := by
  induction binds with
  | nil => intro b hb; exact absurd hb (by simp)
  | cons bd rest ih =>
    intro b hb; rcases List.mem_cons.mp hb with rfl | hb
    · exact (noCaptureFromLet_cons h).2.1
    · exact ih (noCaptureFromLet_cons h).2.2 b hb

theorem noCaptureFromLet_implies_names (fv : VarSet) (binds : List (VarId × Expr × Bool))
    (body : Expr) (h : noCaptureFromLet fv binds body = true) :
    ∀ b ∈ binds, fv.contains b.1 = false :=
  noCaptureFromLet_implies_names_local fv binds body h

--------------------------------------------------------------------------------
-- Cross-NC preservation through substInBindings
--------------------------------------------------------------------------------

private theorem substInBindings_all_nc_rev (v : VarId) (rhs e_tgt : Expr)
    (rest : List (VarId × Expr × Bool)) (s_tgt s₀ : Moist.MIR.FreshState)
    (h_nc_tgt : ∀ b ∈ rest, noCaptureFrom (freeVars b.2.1) e_tgt = true)
    (h_nc_rhs_rest : ∀ b ∈ rest, noCaptureFrom (freeVars rhs) b.2.1 = true)
    (h_rest_rev : ∀ b ∈ rest, noCaptureFrom (freeVars b.2.1) rhs = true)
    (h_nc_rhs_self : noCaptureFrom (freeVars rhs) rhs = true)
    (h_no_rename_tgt : noCaptureFrom (freeVars rhs) e_tgt = true) :
    ∀ b ∈ (substInBindings v rhs rest s₀).1.val,
      noCaptureFrom (freeVars b.2.1) (subst v rhs e_tgt s_tgt).1 = true := by
  intro b hb
  induction rest generalizing s₀ with
  | nil => simp only [substInBindings, pure, StateT.pure] at hb; exact absurd hb (by simp)
  | cons bd rest_tail ih =>
    obtain ⟨w', rhs', er'⟩ := bd
    simp only [substInBindings, bind, StateT.bind] at hb
    rcases List.mem_cons.mp hb with rfl | hb_tail
    · exact nc_subst_via_bound v rhs e_tgt rhs' s_tgt _
        (h_nc_tgt (w', rhs', er') (List.mem_cons_self ..))
        h_no_rename_tgt
        (h_rest_rev (w', rhs', er') (List.mem_cons_self ..))
        h_nc_rhs_self h_no_rename_tgt
        (h_nc_rhs_rest (w', rhs', er') (List.mem_cons_self ..))
    · exact ih _
               (fun b hb => h_nc_tgt b (List.mem_cons_of_mem _ hb))
               (fun b hb => h_nc_rhs_rest b (List.mem_cons_of_mem _ hb))
               (fun b hb => h_rest_rev b (List.mem_cons_of_mem _ hb))
               hb_tail

theorem substInBindings_cross_nc (v : VarId) (rhs : Expr)
    (binds : List (VarId × Expr × Bool)) (s : Moist.MIR.FreshState)
    (h_cross : ∀ b₁ ∈ binds, ∀ b₂ ∈ binds,
      noCaptureFrom (freeVars b₁.2.1) b₂.2.1 = true)
    (h_rhs_self : noCaptureFrom (freeVars rhs) rhs = true)
    (h_rhs_cross : ∀ b ∈ binds, noCaptureFrom (freeVars rhs) b.2.1 = true)
    (h_rhs_rev : ∀ b ∈ binds, noCaptureFrom (freeVars b.2.1) rhs = true) :
    ∀ b₁ ∈ (substInBindings v rhs binds s).1.val,
      ∀ b₂ ∈ (substInBindings v rhs binds s).1.val,
        noCaptureFrom (freeVars b₁.2.1) b₂.2.1 = true := by
  intro b₁ hb₁ b₂ hb₂
  induction binds generalizing s with
  | nil => simp only [substInBindings, pure, StateT.pure] at hb₁; exact absurd hb₁ (by simp)
  | cons bd rest ih =>
    obtain ⟨w, e, er⟩ := bd
    simp only [substInBindings, bind, StateT.bind] at hb₁ hb₂
    have h_nc_e := h_rhs_cross (w, e, er) (List.mem_cons_self ..)
    have h_rev_e := h_rhs_rev (w, e, er) (List.mem_cons_self ..)
    rcases List.mem_cons.mp hb₁ with rfl | hb₁_tail <;>
      rcases List.mem_cons.mp hb₂ with rfl | hb₂_tail
    · exact nc_subst_via_bound v rhs e e s s
        (h_cross (w,e,er) (List.mem_cons_self ..) (w,e,er) (List.mem_cons_self ..))
        h_nc_e h_rev_e h_rhs_self h_nc_e h_nc_e
    · have hall := substInBindings_all_nc v rhs e rest s (subst v rhs e s).2
        (fun b hb => h_cross (w,e,er) (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb))
        (fun b hb => h_rhs_cross b (List.mem_cons_of_mem _ hb))
        h_rev_e h_rhs_self h_nc_e
      rw [List.all_eq_true] at hall; exact hall b₂ hb₂_tail
    · exact substInBindings_all_nc_rev v rhs e rest s _
        (fun b hb => h_cross b (List.mem_cons_of_mem _ hb) (w,e,er) (List.mem_cons_self ..))
        (fun b hb => h_rhs_cross b (List.mem_cons_of_mem _ hb))
        (fun b hb => h_rhs_rev b (List.mem_cons_of_mem _ hb))
        h_rhs_self h_nc_e b₁ hb₁_tail
    · exact ih _
        (fun b₁ hb₁ b₂ hb₂ =>
          h_cross b₁ (List.mem_cons_of_mem _ hb₁) b₂ (List.mem_cons_of_mem _ hb₂))
        (fun b hb => h_rhs_cross b (List.mem_cons_of_mem _ hb))
        (fun b hb => h_rhs_rev b (List.mem_cons_of_mem _ hb))
        hb₁_tail hb₂_tail

--------------------------------------------------------------------------------
-- Inline-pass preservation of PairwiseNC + cross-NC
--------------------------------------------------------------------------------

theorem inlinePass_pairwiseNC_cross
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (s : Moist.MIR.FreshState)
    (hws : wellScoped (.Let binds body) = true) :
    let binds' := (inlineBindings binds s).1.1
    let body' := (inlinePass body (inlineBindings binds s).2).1.1
    PairwiseNC binds' body' ∧
    (∀ b₁ ∈ binds', ∀ b₂ ∈ binds',
      noCaptureFrom (freeVars b₁.2.1) b₂.2.1 = true) := by
  have ⟨hws_body, _, hws_binds⟩ := wellScoped_sub_let hws
  have hpc_orig := pairwiseNC_of_wellScoped binds body hws
  have h_orig_cross := wellScoped_let_cross_nc hws
  constructor
  · -- PairwiseNC
    suffices ∀ (bs : List _) (s₀ : Moist.MIR.FreshState),
        PairwiseNC bs body → (∀ b ∈ bs, wellScoped b.2.1 = true) →
        PairwiseNC (inlineBindings bs s₀).1.1 (inlinePass body (inlineBindings binds s).2).1.1 from
      this binds s hpc_orig hws_binds
    intro bs s₀ hpc hws_bs
    induction bs generalizing s₀ with
    | nil => simp only [inlineBindings, pure, StateT.pure]; exact True.intro
    | cons bd rest ih =>
      obtain ⟨w, rhs_w, er_w⟩ := bd
      simp only [inlineBindings, bind, StateT.bind]
      refine ⟨?_, ?_, ?_, ih _ (pairwiseNC_tail hpc) (fun b hb => hws_bs b (List.mem_cons_of_mem _ hb))⟩
      · exact noCaptureFrom_mono _ _ _
          (inlinePass_nc _ body _ hpc.1 hws_body) (freeVars_nonincreasing rhs_w s₀)
      · rw [List.all_eq_true]; intro b hb
        exact noCaptureFrom_mono _ _ _
          (inlineBindings_nc (Moist.MIR.freeVars rhs_w) rest (inlinePass rhs_w s₀).2
            (fun b hb => by have ⟨_, h, _, _⟩ := hpc; rw [List.all_eq_true] at h; exact h b hb)
            (fun b hb => hws_bs b (List.mem_cons_of_mem _ hb)) b hb)
          (freeVars_nonincreasing rhs_w s₀)
      · rw [List.all_eq_true]; intro b hb; simp only [Bool.not_eq_true']
        have ⟨_, _, h_names_pc, _⟩ := hpc
        rw [List.all_eq_true] at h_names_pc
        -- h_names_pc is for original rest, but hb is for inlineBindings rest
        -- Use inlineBindings_names' to transfer
        have h_names_processed := inlineBindings_names' (Moist.MIR.freeVars rhs_w) rest
          (inlinePass rhs_w s₀).2
          (fun b' hb' => by have := h_names_pc b' hb'; simp only [Bool.not_eq_true'] at this; exact this)
        have h_name := h_names_processed b hb
        cases h_new : (Moist.MIR.freeVars (inlinePass rhs_w s₀).1.1).contains b.1
        · rfl
        · exact absurd (freeVars_nonincreasing rhs_w s₀ b.1 (show _ = true from h_new))
            (by simp [h_name])
  · -- Cross-NC: same proof as the Let case of inlinePass_nc
    have h_all_nc : ∀ b_orig ∈ binds, ∀ b₂ ∈ (inlineBindings binds s).1.1,
        noCaptureFrom (Moist.MIR.freeVars b_orig.2.1) b₂.2.1 = true :=
      fun b_orig hb_orig => inlineBindings_nc (Moist.MIR.freeVars b_orig.2.1) binds s
        (fun b hb => h_orig_cross b_orig hb_orig b hb) hws_binds
    intro b₁ hb₁ b₂ hb₂
    suffices ∀ (bs : List _) (s₀ : Moist.MIR.FreshState),
        (∀ b_orig ∈ bs, ∀ b₂ ∈ (inlineBindings binds s).1.1,
          noCaptureFrom (Moist.MIR.freeVars b_orig.2.1) b₂.2.1 = true) →
        b₁ ∈ (inlineBindings bs s₀).1.1 →
        noCaptureFrom (freeVars b₁.2.1) b₂.2.1 = true from
      this binds s (fun b_orig hb => h_all_nc b_orig hb) hb₁
    intro bs s₀ h_all hb₁_bs
    induction bs generalizing s₀ with
    | nil => simp only [inlineBindings, pure, StateT.pure] at hb₁_bs; exact absurd hb₁_bs (by simp)
    | cons bd rest ih =>
      obtain ⟨w, rhs_w, er_w⟩ := bd
      simp only [inlineBindings, bind, StateT.bind] at hb₁_bs
      rcases List.mem_cons.mp hb₁_bs with rfl | hb₁_rest
      · exact noCaptureFrom_mono _ _ _
          (h_all (w, rhs_w, er_w) (List.mem_cons_self ..) b₂ hb₂)
          (freeVars_nonincreasing rhs_w s₀)
      · exact ih _ (fun b_orig hb => h_all b_orig (List.mem_cons_of_mem _ hb)) hb₁_rest

--------------------------------------------------------------------------------
-- Helpers used by InlineSoundness.lean
--------------------------------------------------------------------------------

theorem nc_wellScoped_app (f x : Expr) (hws : wellScoped (.App f x) = true) :
    NC (freeVars (.App f x)) f ∧ NC (freeVars (.App f x)) x :=
  noCaptureFrom_app (wellScoped_noCaptureFrom hws)

theorem fvSub_app_left (f x : Expr) : FVSub (freeVars (.App f x)) f :=
  fun w hw => by rw [Moist.MIR.freeVars.eq_7]; exact contains_union_left _ _ _ hw

theorem fvSub_app_right (f x : Expr) : FVSub (freeVars (.App f x)) x :=
  fun w hw => by rw [Moist.MIR.freeVars.eq_7]; exact contains_union_right _ _ _ hw

end Moist.Verified.InlineSoundness.Preservation
