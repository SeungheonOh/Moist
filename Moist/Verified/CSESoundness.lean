import Moist.Verified.CSE.Reuse
import Moist.Verified.CSE.Lowering
import Moist.Verified.HygieneSoundness
import Moist.Verified.MIR.AlphaEqBool
import Moist.Verified.MIR.Hoist

/-! # Soundness of common sub-expression elimination

`cse_refines : MIRCtxRefines e (cse [] e).1` for every MIR expression `e`.

The seen map of `cse` lists bindings `(e, w)` that dominate the current
position. The proof relates terms under every UPLC context that actually
evaluates the lowering of `e` into `w` above the hole (`Avail`): under such
contexts, re-evaluating `e` may be replaced by `w` (`obsUnder_reuse`, from the
UPLC rule `reuse_ctxRefines`). The relation is closed under composition and
under the contexts of every MIR constructor, provided the seen map is
filtered as `cse` does when it passes a binder, so the whole traversal is
proved by induction on the node count. With an empty seen map every context
qualifies, which is contextual refinement. -/

namespace Moist.Verified.CSE

open Moist.CEK
open Moist.Plutus.Term (Term)
open Moist.MIR
open Moist.Verified (closedAt closedAtList renameTerm)
open Moist.Verified.Equivalence (ListRel)
open Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines (iterShift)
open Moist.Verified.MIR (lowerTotalExprList lowerTotalExprList_nil lowerTotalExprList_cons
  lowerTotalExpr_lam lowerTotalExpr_app lowerTotalExpr_force lowerTotalExpr_delay
  lowerTotalExpr_constr_of_list lowerTotalExpr_case_of_list lowerTotalExpr_prepend_unused
  MIRCtxRefines)
open Moist.Verified.InlineSoundness.Rename (lowerTotalExpr_let_nil lowerTotalExpr_let_cons
  lowerTotalExpr_fix_lam beq_false_of_uid beq_comm)

/-! ## Contexts -/

theorem Context.compose_assoc (A B D : Context) :
    (A.compose B).compose D = A.compose (B.compose D) := by
  induction A with
  | Hole => rfl
  | Lam x C ih => simp [Context.compose, ih]
  | AppLeft C e ih => simp [Context.compose, ih]
  | AppRight e C ih => simp [Context.compose, ih]
  | Delay C ih => simp [Context.compose, ih]
  | Force C ih => simp [Context.compose, ih]
  | Constr tag lefts C rights ih => simp [Context.compose, ih]
  | Case C alts ih => simp [Context.compose, ih]
  | CaseAlt scrut lefts C rights ih => simp [Context.compose, ih]

theorem Context.binders_compose (A D : Context) :
    (A.compose D).binders = A.binders + D.binders := by
  induction A with
  | Hole => simp [Context.compose, Context.binders]
  | Lam x C ih => simp [Context.compose, Context.binders, ih]; omega
  | AppLeft C e ih => simp [Context.compose, Context.binders, ih]
  | AppRight e C ih => simp [Context.compose, Context.binders, ih]
  | Delay C ih => simp [Context.compose, Context.binders, ih]
  | Force C ih => simp [Context.compose, Context.binders, ih]
  | Constr tag lefts C rights ih => simp [Context.compose, Context.binders, ih]
  | Case C alts ih => simp [Context.compose, Context.binders, ih]
  | CaseAlt scrut lefts C rights ih => simp [Context.compose, Context.binders, ih]

/-! ## Available bindings -/

/-- The context `C₀[(λ. C₁) t₀]` evaluates `t₀` into the variable `w`, `i`
    binders above the hole, and `e` lowers at the hole to the shifted `t₀`. -/
def AvailEntry (C : Context) (env : List VarId) (e : Expr) (w : VarId) : Prop :=
  ∃ (i : Nat) (t₀ : Term) (C₀ C₁ : Context), envLookupT env w = some i ∧ C₁.binders = i ∧
    C = C₀.compose (.AppLeft (.Lam 0 C₁) t₀) ∧
    lowerTotalExpr env e = some (iterShift (i + 1) t₀)

def Avail (C : Context) (env : List VarId) (seen : List (Expr × VarId)) : Prop :=
  ∀ p ∈ seen, AvailEntry C env p.1 p.2

/-- Observational refinement under every context making `seen` available. -/
def ObsUnder (seen : List (Expr × VarId)) (env : List VarId) (t t' : Term) : Prop :=
  ∀ C, Avail C env seen → closedAt 0 (fill C t) = true →
    closedAt 0 (fill C t') = true ∧
      ObsRefines (.compute [] .nil (fill C t)) (.compute [] .nil (fill C t'))

def Scoped (seen : List (Expr × VarId)) (env : List VarId) : Prop :=
  ∀ p ∈ seen, ∃ i, envLookupT env p.2 = some i

/-- The relation proved for `cse`: lowering is preserved and the lowered
    terms are related under contexts making `seen` available. -/
def CseRel (seen : List (Expr × VarId)) (env : List VarId) (m m' : Expr) : Prop :=
  Scoped seen env → ∀ t, lowerTotalExpr env m = some t →
    ∃ t', lowerTotalExpr env m' = some t' ∧ ObsUnder seen env t t'

def CseRelList (seen : List (Expr × VarId)) (env : List VarId) (ms ms' : List Expr) : Prop :=
  Scoped seen env → ∀ ts, lowerTotalExprList env ms = some ts →
    ∃ ts', lowerTotalExprList env ms' = some ts' ∧ ListRel (ObsUnder seen env) ts ts'

theorem obsRefines_trans {s₁ s₂ s₃ : State} (h₁ : ObsRefines s₁ s₂) (h₂ : ObsRefines s₂ s₃) :
    ObsRefines s₁ s₃ :=
  ⟨fun h => h₂.halt (h₁.halt h), fun h => h₂.error (h₁.error h)⟩

theorem ObsUnder.refl {seen : List (Expr × VarId)} {env : List VarId} (t : Term) :
    ObsUnder seen env t t :=
  fun _ _ h => ⟨h, ⟨id, id⟩⟩

theorem ObsUnder.trans {seen : List (Expr × VarId)} {env : List VarId} {t₁ t₂ t₃ : Term}
    (h₁ : ObsUnder seen env t₁ t₂) (h₂ : ObsUnder seen env t₂ t₃) : ObsUnder seen env t₁ t₃ := by
  intro C hC hc
  obtain ⟨hc₂, ho₁⟩ := h₁ C hC hc
  obtain ⟨hc₃, ho₂⟩ := h₂ C hC hc₂
  exact ⟨hc₃, obsRefines_trans ho₁ ho₂⟩

theorem ObsUnder.of_ctxRefines {seen : List (Expr × VarId)} {env : List VarId} {t t' : Term}
    (h : CtxRefines t t') : ObsUnder seen env t t' :=
  fun C _ hc => h C hc

theorem CseRel.refl {seen : List (Expr × VarId)} {env : List VarId} (m : Expr) :
    CseRel seen env m m :=
  fun _ t ht => ⟨t, ht, ObsUnder.refl t⟩

theorem CseRel.trans {seen : List (Expr × VarId)} {env : List VarId} {m₁ m₂ m₃ : Expr}
    (h₁ : CseRel seen env m₁ m₂) (h₂ : CseRel seen env m₂ m₃) : CseRel seen env m₁ m₃ := by
  intro hs t ht
  obtain ⟨t₂, ht₂, ho₁⟩ := h₁ hs t ht
  obtain ⟨t₃, ht₃, ho₂⟩ := h₂ hs t₂ ht₂
  exact ⟨t₃, ht₃, ho₁.trans ho₂⟩

theorem CseRel.of_lower_eq {seen : List (Expr × VarId)} {env : List VarId} {m m' : Expr}
    (h : lowerTotalExpr env m' = lowerTotalExpr env m) : CseRel seen env m m' :=
  fun _ t ht => ⟨t, h.trans ht, ObsUnder.refl t⟩

theorem CseRel.of_lower_eq_left {seen : List (Expr × VarId)} {env : List VarId} {m₁ m₂ m₃ : Expr}
    (h : lowerTotalExpr env m₂ = lowerTotalExpr env m₁) (h₂ : CseRel seen env m₂ m₃) :
    CseRel seen env m₁ m₃ :=
  (CseRel.of_lower_eq h).trans h₂

/-! ## Moving into a context -/

theorem obsUnder_fill {seen seen' : List (Expr × VarId)} {env env' : List VarId} (D : Context)
    (transport : ∀ C, Avail C env seen → Avail (C.compose D) env' seen')
    {t t' : Term} (h : ObsUnder seen' env' t t') :
    ObsUnder seen env (fill D t) (fill D t') := by
  intro C hC hc
  rw [← fill_compose] at hc ⊢
  rw [← fill_compose]
  exact h (C.compose D) (transport C hC) hc

theorem envLookupT_append (ys env : List VarId) (w : VarId) (i : Nat)
    (hys : ∀ y ∈ ys, (y == w) = false) (hw : envLookupT env w = some i) :
    envLookupT (ys ++ env) w = some (i + ys.length) := by
  induction ys with
  | nil => simpa using hw
  | cons y ys ih =>
    rw [List.cons_append, envLookupT_cons_neq y w _ (hys y (.head _)),
      ih fun y' hy' => hys y' (.tail _ hy')]
    simp only [Option.map_some, List.length_cons, Option.some.injEq]
    omega

theorem lowerTotalExpr_append_unused (ys env : List VarId) (e : Expr) (n : Nat) (t₀ : Term)
    (hys : ∀ y ∈ ys, (freeVars e).contains y = false)
    (he : lowerTotalExpr env e = some (iterShift n t₀)) :
    lowerTotalExpr (ys ++ env) e = some (iterShift (n + ys.length) t₀) := by
  induction ys with
  | nil => simpa using he
  | cons y ys ih =>
    rw [List.cons_append, lowerTotalExpr_prepend_unused _ y e (hys y (.head _)),
      ih fun y' hy' => hys y' (.tail _ hy')]
    rfl

/-- Passing `|ys|` binders keeps every entry whose variable and free
    variables are not among them. -/
theorem avail_compose {C D : Context} {env : List VarId} {seen seen' : List (Expr × VarId)}
    (ys : List VarId) (hD : D.binders = ys.length)
    (hsub : ∀ p ∈ seen', p ∈ seen ∧
      ∀ y ∈ ys, (y == p.2) = false ∧ (freeVars p.1).contains y = false)
    (hC : Avail C env seen) : Avail (C.compose D) (ys ++ env) seen' := by
  intro p hp
  obtain ⟨hmem, hfresh⟩ := hsub p hp
  obtain ⟨i, t₀, C₀, C₁, hw, hb, rfl, he⟩ := hC p hmem
  refine ⟨i + ys.length, t₀, C₀, C₁.compose D,
    envLookupT_append ys env p.2 i (fun y hy => (hfresh y hy).1) hw, ?_, ?_, ?_⟩
  · rw [Context.binders_compose, hb, hD]
  · rw [Context.compose_assoc]; rfl
  · have := lowerTotalExpr_append_unused ys env p.1 (i + 1) t₀ (fun y hy => (hfresh y hy).2) he
    rw [this]
    congr 2
    omega

theorem avail_compose_flat {C D : Context} {env : List VarId} {seen : List (Expr × VarId)}
    (hD : D.binders = 0) (hC : Avail C env seen) : Avail (C.compose D) env seen :=
  avail_compose [] hD (fun _ hp => ⟨hp, fun _ h => nomatch h⟩) hC

theorem scoped_append {seen seen' : List (Expr × VarId)} {env : List VarId} (ys : List VarId)
    (hsub : ∀ p ∈ seen', p ∈ seen ∧ ∀ y ∈ ys, (y == p.2) = false)
    (hs : Scoped seen env) : Scoped seen' (ys ++ env) := by
  intro p hp
  obtain ⟨hmem, hfresh⟩ := hsub p hp
  obtain ⟨i, hi⟩ := hs p hmem
  exact ⟨_, envLookupT_append ys env p.2 i hfresh hi⟩

/-! ## The seen map -/

theorem mem_filterSeen {x : VarId} {seen : List (Expr × VarId)} {p : Expr × VarId}
    (h : p ∈ filterSeen x seen) :
    p ∈ seen ∧ (x == p.2) = false ∧ (freeVars p.1).contains x = false := by
  simp only [filterSeen, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨h.1, ?_, h.2.2⟩
  rw [beq_comm]
  simpa [bne] using h.2.1


theorem avail_filterSeen {C D : Context} {env : List VarId} {seen : List (Expr × VarId)}
    (x : VarId) (hD : D.binders = 1) (hC : Avail C env seen) :
    Avail (C.compose D) (x :: env) (filterSeen x seen) :=
  avail_compose [x] hD (fun _ hp =>
    let ⟨hm, hx, hfv⟩ := mem_filterSeen hp
    ⟨hm, fun y hy => by cases List.mem_singleton.mp hy; exact ⟨hx, hfv⟩⟩) hC

theorem scoped_filterSeen {env : List VarId} {seen : List (Expr × VarId)} (x : VarId)
    (hs : Scoped seen env) : Scoped (filterSeen x seen) (x :: env) :=
  scoped_append [x] (fun _ hp =>
    let ⟨hm, hx, _⟩ := mem_filterSeen hp
    ⟨hm, fun y hy => by cases List.mem_singleton.mp hy; exact hx⟩) hs

theorem avail_extendSeen {C : Context} {env : List VarId} {seen : List (Expr × VarId)}
    {v : VarId} {rhs : Expr} {t_rhs : Term} (hrhs : lowerTotalExpr env rhs = some t_rhs)
    (hC : Avail C env seen) :
    Avail (C.compose (.AppLeft (.Lam 0 .Hole) t_rhs)) (v :: env) (extendSeen seen v rhs) := by
  have filtered := avail_filterSeen v (D := .AppLeft (.Lam 0 .Hole) t_rhs) rfl hC
  unfold extendSeen
  split
  · exact filtered
  · rename_i hv
    intro p hp
    cases hp with
    | head =>
      refine ⟨0, t_rhs, C, .Hole, envLookupT_cons_self v env, rfl, rfl, ?_⟩
      rw [lowerTotalExpr_prepend_unused env v rhs (by simpa using hv), hrhs]
      rfl
    | tail _ hp => exact filtered p hp

theorem scoped_extendSeen {env : List VarId} {seen : List (Expr × VarId)} {v : VarId}
    {rhs : Expr} (hs : Scoped seen env) : Scoped (extendSeen seen v rhs) (v :: env) := by
  have filtered := scoped_filterSeen v hs
  unfold extendSeen
  split
  · exact filtered
  · intro p hp
    cases hp with
    | head => exact ⟨0, envLookupT_cons_self v env⟩
    | tail _ hp => exact filtered p hp

/-- A bound on every uid in the seen map. -/
def seenBound : List (Expr × VarId) → Nat
  | [] => 0
  | (e, w) :: rest => maxUidExpr e + w.uid + 1 + seenBound rest

theorem seenBound_mem {seen : List (Expr × VarId)} {p : Expr × VarId} (h : p ∈ seen) :
    maxUidExpr p.1 < seenBound seen ∧ p.2.uid < seenBound seen := by
  induction seen with
  | nil => cases h
  | cons q rest ih =>
    obtain ⟨e, w⟩ := q
    simp only [seenBound]
    cases h with
    | head => show maxUidExpr e < _ ∧ w.uid < _; omega
    | tail _ h => have := ih h; omega

/-! ## Reusing an available binding -/

theorem lookupStructEq_some {seen : List (Expr × VarId)} {t : Expr} {w : VarId}
    (h : lookupStructEq seen t = some w) : ∃ e, (e, w) ∈ seen ∧ alphaEq e t = true := by
  induction seen with
  | nil => simp [lookupStructEq] at h
  | cons q rest ih =>
    obtain ⟨e, x⟩ := q
    simp only [lookupStructEq] at h
    split at h
    · rename_i halpha
      cases h
      exact ⟨e, .head _, halpha⟩
    · obtain ⟨e', hm, ha⟩ := ih h
      exact ⟨e', .tail _ hm, ha⟩

theorem reusableBinding_some {seen : List (Expr × VarId)} {rhs : Expr}
    {rest : List (VarId × Expr × Bool)} {body : Expr} {w : VarId}
    (h : reusableBinding seen rhs rest body = some w) :
    (∃ e, (e, w) ∈ seen ∧ alphaEq e rhs = true) ∧ bindsVarLet w rest body = false := by
  unfold reusableBinding at h
  split at h
  · split at h
    · rename_i w' hl
      split at h
      · cases h
      · cases h
        rename_i hb
        exact ⟨lookupStructEq_some hl, by simpa using hb⟩
    · cases h
  · cases h

/-- Under a context that evaluates `e` into `w`, the binding `(λ. body) e`
    refines `body` reading `w`. -/
theorem obsUnder_reuse {seen : List (Expr × VarId)} {env : List VarId} {e : Expr} {w : VarId}
    {t_e t_R : Term} {i : Nat} (hmem : (e, w) ∈ seen) (he : lowerTotalExpr env e = some t_e)
    (hw : envLookupT env w = some i) :
    ObsUnder seen env (.Apply (.Lam 0 t_R) t_e) (renameTerm (mergeRename i) t_R) := by
  intro C hC hc
  obtain ⟨i', t₀, C₀, C₁, hw', hb, hCeq, he'⟩ := hC (e, w) hmem
  rw [hw] at hw'
  cases hw'
  rw [he] at he'
  cases he'
  subst hCeq
  have hfill : ∀ x, fill (C₀.compose (.AppLeft (.Lam 0 C₁) t₀)) x =
      fill C₀ (.Apply (.Lam 0 (fill C₁ x)) t₀) := fun x => by rw [fill_compose]; rfl
  rw [hfill] at hc ⊢
  rw [hfill]
  have hcl := ((fill_closedAt_iff C₀ _ 0).mp hc).2
  exact reuse_ctxRefines C₁ t₀ t_R i (0 + C₀.binders) hb hcl C₀ hc

/-! ## Congruences -/

theorem lowerTotalExpr_lam_some {env : List VarId} {x : VarId} {body : Expr} {t : Term}
    (h : lowerTotalExpr env (.Lam x body) = some t) :
    ∃ tb, lowerTotalExpr (x :: env) body = some tb ∧ t = .Lam 0 tb := by
  rw [lowerTotalExpr_lam] at h
  obtain ⟨tb, htb, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨tb, htb, rfl⟩

theorem cseRel_lam {seen : List (Expr × VarId)} {env : List VarId} {x : VarId} {body body' : Expr}
    (h : CseRel (filterSeen x seen) (x :: env) body body') :
    CseRel seen env (.Lam x body) (.Lam x body') := by
  intro hs t ht
  obtain ⟨tb, htb, rfl⟩ := lowerTotalExpr_lam_some ht
  obtain ⟨tb', htb', ho⟩ := h (scoped_filterSeen x hs) tb htb
  refine ⟨.Lam 0 tb', by rw [lowerTotalExpr_lam, htb']; rfl, ?_⟩
  exact obsUnder_fill (.Lam 0 .Hole) (fun _ hC => avail_filterSeen x rfl hC) ho

theorem cseRel_force {seen : List (Expr × VarId)} {env : List VarId} {a a' : Expr}
    (h : CseRel seen env a a') : CseRel seen env (.Force a) (.Force a') := by
  intro hs t ht
  rw [lowerTotalExpr_force] at ht
  obtain ⟨ta, hta, rfl⟩ := Option.map_eq_some_iff.mp ht
  obtain ⟨ta', hta', ho⟩ := h hs ta hta
  refine ⟨.Force ta', by rw [lowerTotalExpr_force, hta']; rfl, ?_⟩
  exact obsUnder_fill (.Force .Hole) (fun _ hC => avail_compose_flat rfl hC) ho

theorem cseRel_delay {seen : List (Expr × VarId)} {env : List VarId} {a a' : Expr}
    (h : CseRel seen env a a') : CseRel seen env (.Delay a) (.Delay a') := by
  intro hs t ht
  rw [lowerTotalExpr_delay] at ht
  obtain ⟨ta, hta, rfl⟩ := Option.map_eq_some_iff.mp ht
  obtain ⟨ta', hta', ho⟩ := h hs ta hta
  refine ⟨.Delay ta', by rw [lowerTotalExpr_delay, hta']; rfl, ?_⟩
  exact obsUnder_fill (.Delay .Hole) (fun _ hC => avail_compose_flat rfl hC) ho

theorem cseRel_app {seen : List (Expr × VarId)} {env : List VarId} {f f' a a' : Expr}
    (hf : CseRel seen env f f') (ha : CseRel seen env a a') :
    CseRel seen env (.App f a) (.App f' a') := by
  intro hs t ht
  rw [lowerTotalExpr_app] at ht
  cases hf0 : lowerTotalExpr env f with
  | none => simp [hf0] at ht
  | some tf =>
    cases ha0 : lowerTotalExpr env a with
    | none => simp [hf0, ha0] at ht
    | some ta =>
      simp [hf0, ha0] at ht
      subst ht
      obtain ⟨tf', htf', hof⟩ := hf hs tf hf0
      obtain ⟨ta', hta', hoa⟩ := ha hs ta ha0
      refine ⟨.Apply tf' ta', by rw [lowerTotalExpr_app, htf', hta']; rfl, ?_⟩
      exact (obsUnder_fill (.AppLeft .Hole ta) (fun _ hC => avail_compose_flat rfl hC) hof).trans
        (obsUnder_fill (.AppRight tf' .Hole) (fun _ hC => avail_compose_flat rfl hC) hoa)

theorem obsUnder_constr_aux {seen : List (Expr × VarId)} {env : List VarId} (tag : Nat) :
    ∀ (pre ts ts' : List Term), ListRel (ObsUnder seen env) ts ts' →
      ObsUnder seen env (.Constr tag (pre ++ ts)) (.Constr tag (pre ++ ts'))
  | _, [], [], _ => ObsUnder.refl _
  | _, [], _ :: _, h | _, _ :: _, [], h => absurd h id
  | pre, a :: as, b :: bs, h => by
    have step : ObsUnder seen env (.Constr tag (pre ++ [a] ++ as)) (.Constr tag (pre ++ [b] ++ as)) :=
      obsUnder_fill (.Constr tag pre .Hole as) (fun _ hC => avail_compose_flat rfl hC) h.1
    have rest := obsUnder_constr_aux tag (pre ++ [b]) as bs h.2
    simp only [List.append_assoc, List.singleton_append] at step rest
    exact step.trans rest

theorem obsUnder_caseAlts_aux {seen : List (Expr × VarId)} {env : List VarId} (scrut : Term) :
    ∀ (pre ts ts' : List Term), ListRel (ObsUnder seen env) ts ts' →
      ObsUnder seen env (.Case scrut (pre ++ ts)) (.Case scrut (pre ++ ts'))
  | _, [], [], _ => ObsUnder.refl _
  | _, [], _ :: _, h | _, _ :: _, [], h => absurd h id
  | pre, a :: as, b :: bs, h => by
    have step : ObsUnder seen env (.Case scrut (pre ++ [a] ++ as)) (.Case scrut (pre ++ [b] ++ as)) :=
      obsUnder_fill (.CaseAlt scrut pre .Hole as) (fun _ hC => avail_compose_flat rfl hC) h.1
    have rest := obsUnder_caseAlts_aux scrut (pre ++ [b]) as bs h.2
    simp only [List.append_assoc, List.singleton_append] at step rest
    exact step.trans rest

theorem cseRel_constr {seen : List (Expr × VarId)} {env : List VarId} {tag : Nat}
    {args args' : List Expr} (h : CseRelList seen env args args') :
    CseRel seen env (.Constr tag args) (.Constr tag args') := by
  intro hs t ht
  rw [lowerTotalExpr_constr_of_list] at ht
  obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp ht
  obtain ⟨ts', hts', ho⟩ := h hs ts hts
  refine ⟨.Constr tag ts', by rw [lowerTotalExpr_constr_of_list, hts']; rfl, ?_⟩
  exact obsUnder_constr_aux tag [] ts ts' ho

theorem cseRel_case {seen : List (Expr × VarId)} {env : List VarId} {scrut scrut' : Expr}
    {alts alts' : List Expr} (hs' : CseRel seen env scrut scrut') (ha : CseRelList seen env alts alts') :
    CseRel seen env (.Case scrut alts) (.Case scrut' alts') := by
  intro hs t ht
  rw [lowerTotalExpr_case_of_list] at ht
  cases h0 : lowerTotalExpr env scrut with
  | none => simp [h0] at ht
  | some ts =>
    cases h1 : lowerTotalExprList env alts with
    | none => simp [h0, h1] at ht
    | some tas =>
      simp [h0, h1] at ht
      subst ht
      obtain ⟨ts', hts', hos⟩ := hs' hs ts h0
      obtain ⟨tas', htas', hoa⟩ := ha hs tas h1
      refine ⟨.Case ts' tas', by rw [lowerTotalExpr_case_of_list, hts', htas']; rfl, ?_⟩
      exact (obsUnder_fill (.Case .Hole tas) (fun _ hC => avail_compose_flat rfl hC) hos).trans
        (obsUnder_caseAlts_aux ts' [] tas tas' hoa)

theorem cseRelList_nil {seen : List (Expr × VarId)} {env : List VarId} :
    CseRelList seen env [] [] := by
  intro _ ts hts
  rw [lowerTotalExprList_nil] at hts
  cases hts
  exact ⟨[], lowerTotalExprList_nil env, trivial⟩

theorem cseRelList_cons {seen : List (Expr × VarId)} {env : List VarId} {a a' : Expr}
    {as as' : List Expr} (ha : CseRel seen env a a') (has : CseRelList seen env as as') :
    CseRelList seen env (a :: as) (a' :: as') := by
  intro hs ts hts
  rw [lowerTotalExprList_cons] at hts
  cases h0 : lowerTotalExpr env a with
  | none => simp [h0] at hts
  | some t =>
    cases h1 : lowerTotalExprList env as with
    | none => simp [h0, h1] at hts
    | some rest =>
      simp [h0, h1] at hts
      subst hts
      obtain ⟨t', ht', ho⟩ := ha hs t h0
      obtain ⟨rest', hrest', hos⟩ := has hs rest h1
      exact ⟨t' :: rest', by rw [lowerTotalExprList_cons, ht', hrest']; rfl, ho, hos⟩

/-! ## Let blocks -/

theorem lowerTotalExpr_let_cons_some {env : List VarId} {v : VarId} {rhs : Expr} {er : Bool}
    {rest : List (VarId × Expr × Bool)} {body : Expr} {t : Term}
    (h : lowerTotalExpr env (.Let ((v, rhs, er) :: rest) body) = some t) :
    ∃ r b, lowerTotalExpr env rhs = some r ∧ lowerTotalExpr (v :: env) (.Let rest body) = some b ∧
      t = .Apply (.Lam 0 b) r := by
  rw [lowerTotalExpr_let_cons] at h
  cases h0 : lowerTotalExpr env rhs with
  | none => simp [h0] at h
  | some r =>
    cases h1 : lowerTotalExpr (v :: env) (.Let rest body) with
    | none => simp [h0, h1] at h
    | some b =>
      simp [h0, h1] at h
      exact ⟨r, b, rfl, rfl, h.symm⟩

theorem lowerTotalExpr_let_cons_of {env : List VarId} {v : VarId} {rhs : Expr} {er : Bool}
    {rest : List (VarId × Expr × Bool)} {body : Expr} {r b : Term}
    (hr : lowerTotalExpr env rhs = some r) (hb : lowerTotalExpr (v :: env) (.Let rest body) = some b) :
    lowerTotalExpr env (.Let ((v, rhs, er) :: rest) body) = some (.Apply (.Lam 0 b) r) := by
  rw [lowerTotalExpr_let_cons, hr, hb]; rfl

theorem cseRel_let_rhs {seen : List (Expr × VarId)} {env : List VarId} {v : VarId}
    {rhs rhs' : Expr} {er : Bool} {rest : List (VarId × Expr × Bool)} {body : Expr}
    (h : CseRel seen env rhs rhs') :
    CseRel seen env (.Let ((v, rhs, er) :: rest) body) (.Let ((v, rhs', er) :: rest) body) := by
  intro hs t ht
  obtain ⟨r, b, hr, hb, rfl⟩ := lowerTotalExpr_let_cons_some ht
  obtain ⟨r', hr', ho⟩ := h hs r hr
  exact ⟨_, lowerTotalExpr_let_cons_of hr' hb,
    obsUnder_fill (.AppRight (.Lam 0 b) .Hole) (fun _ hC => avail_compose_flat rfl hC) ho⟩

theorem cseRel_let_body {seen : List (Expr × VarId)} {env : List VarId} {v : VarId}
    {rhs : Expr} {er : Bool} {rest rest' : List (VarId × Expr × Bool)} {body body' : Expr}
    (h : CseRel (extendSeen seen v rhs) (v :: env) (.Let rest body) (.Let rest' body')) :
    CseRel seen env (.Let ((v, rhs, er) :: rest) body) (.Let ((v, rhs, er) :: rest') body') := by
  intro hs t ht
  obtain ⟨r, b, hr, hb, rfl⟩ := lowerTotalExpr_let_cons_some ht
  obtain ⟨b', hb', ho⟩ := h (scoped_extendSeen hs) b hb
  exact ⟨_, lowerTotalExpr_let_cons_of hr hb',
    obsUnder_fill (.AppLeft (.Lam 0 .Hole) r) (fun _ hC => avail_extendSeen hr hC) ho⟩

theorem mergeEnv_top {v w : VarId} {env : List VarId} {i : Nat} (hw : envLookupT env w = some i) :
    MergeEnv v w (mergeRename i) (v :: env) env := by
  refine ⟨fun z hz => ?_, ?_⟩
  · simp only [LookupRename]
    rw [envLookupT_cons_neq v z env (by rw [beq_comm]; exact hz)]
    cases envLookupT env z <;> simp [mergeRename]
  · rw [hw, envLookupT_cons_self]
    simp [mergeRename]

theorem cseRel_reuse {seen : List (Expr × VarId)} {env : List VarId} {v w : VarId} {e rhs : Expr}
    {er : Bool} {rest : List (VarId × Expr × Bool)} {body : Expr}
    (hmem : (e, w) ∈ seen) (halpha : alphaEq e rhs = true) (hguard : bindsVarLet w rest body = false) :
    CseRel seen env (.Let ((v, rhs, er) :: rest) body)
      (.Let (renameLet v w rest body).1 (renameLet v w rest body).2) := by
  intro hs t ht
  obtain ⟨i, hw⟩ := hs (e, w) hmem
  obtain ⟨r, b, hr, hb, rfl⟩ := lowerTotalExpr_let_cons_some ht
  refine ⟨renameTerm (mergeRename i) b, ?_, ?_⟩
  · rw [lowerTotalExprLet_merge v w (mergeRename i) rest body (v :: env) env hguard
      (mergeEnv_top hw), hb]
    rfl
  · exact obsUnder_reuse hmem ((Moist.Verified.MIR.alphaEq_lowerTotalExpr_eq halpha env).trans hr) hw

/-! ## Recursive lambdas -/

/-- The context of the Z-combinator wrapper of a recursive lambda. -/
def fixContext : Context :=
  .AppRight (.Lam 0 (.Apply (.Var 1) (.Var 1)))
    (.Lam 0 (.AppLeft (.Lam 0 (.Lam 0 .Hole)) (.Lam 0 (.Apply (.Apply (.Var 2) (.Var 2)) (.Var 1)))))

theorem fill_fixContext (t : Term) : fill fixContext t = fixLamWrapUplc t := rfl

theorem uniqueOptimizationBinders_lam (p : VarId) (inner : Expr) :
    ∃ p' inner', uniqueOptimizationBinders (.Lam p inner) = .Lam p' inner' := by
  unfold uniqueOptimizationBinders
  split
  · exact ⟨p, inner, rfl⟩
  · exact ⟨_, _, rfl⟩

/-- `Fix f (Lam p inner)` against the same recursive lambda with a related body. -/
theorem cseRel_fix {seen : List (Expr × VarId)} {env : List VarId} {f p : VarId}
    {inner inner' : Expr}
    (h : ∀ s : VarId, seenBound seen < s.uid →
      CseRel (filterSeen p (filterSeen f seen)) (p :: f :: s :: env) inner inner') :
    CseRel seen env (.Fix f (.Lam p inner)) (.Fix f (.Lam p inner')) := by
  intro hs t ht
  let s : VarId := ⟨maxUidExpr (expandFix inner) + maxUidExpr (expandFix inner') +
    seenBound seen + 1, .gen, "s"⟩
  have sFresh₁ : maxUidExpr (expandFix inner) < s.uid := by simp only [s]; omega
  have sFresh₂ : maxUidExpr (expandFix inner') < s.uid := by simp only [s]; omega
  have sBound : seenBound seen < s.uid := by simp only [s]; omega
  rw [lowerTotalExpr_fix_lam env f p inner s sFresh₁] at ht
  obtain ⟨ti, hti, rfl⟩ := Option.map_eq_some_iff.mp ht
  have hsub : ∀ q ∈ filterSeen p (filterSeen f seen), q ∈ seen ∧
      ∀ y ∈ [p, f, s], (y == q.2) = false ∧ (freeVars q.1).contains y = false := by
    intro q hq
    obtain ⟨hq₁, hp, hpfv⟩ := mem_filterSeen hq
    obtain ⟨hq₂, hf, hffv⟩ := mem_filterSeen hq₁
    have hb := seenBound_mem hq₂
    refine ⟨hq₂, fun y hy => ?_⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact ⟨hp, hpfv⟩
    · exact ⟨hf, hffv⟩
    · exact ⟨beq_false_of_uid (by omega), maxUidExpr_fresh _ _ (by omega)⟩
  have hscoped : Scoped (filterSeen p (filterSeen f seen)) (p :: f :: s :: env) :=
    scoped_append [p, f, s] (fun q hq => ⟨(hsub q hq).1, fun y hy => ((hsub q hq).2 y hy).1⟩) hs
  obtain ⟨ti', hti', ho⟩ := h s sBound hscoped ti hti
  refine ⟨fixLamWrapUplc ti', by rw [lowerTotalExpr_fix_lam env f p inner' s sFresh₂, hti']; rfl, ?_⟩
  exact obsUnder_fill fixContext (fun _ hC => avail_compose [p, f, s] rfl hsub hC) ho

/-! ## Equations of the traversal -/

section Equations

variable {seen : List (Expr × VarId)} {e : Expr}

theorem cse_let_lower {binds : List (VarId × Expr × Bool)} {body : Expr} (env : List VarId)
    (h : uniqueOptimizationBinders e = .Let binds body) :
    lowerTotalExpr env (cse seen e).1 =
      lowerTotalExpr env (.Let (cseBinds seen binds body).1 (cseBinds seen binds body).2.1) := by
  rw [cse]
  split
  next binds' body' heq =>
    rw [h] at heq
    injection heq with h₁ h₂
    subst h₁ h₂
    cases cseBinds seen binds body with
    | mk kept rest =>
      cases rest with
      | mk b c =>
        cases kept with
        | nil => simp [lowerTotalExpr_let_nil]
        | cons k ks => rfl
  all_goals simp_all

theorem cse_lam {x : VarId} {body : Expr} (h : uniqueOptimizationBinders e = .Lam x body) :
    (cse seen e).1 = .Lam x (cse (filterSeen x seen) body).1 := by
  rw [cse]; split <;> simp_all

theorem cse_fix {f : VarId} {body : Expr} (h : uniqueOptimizationBinders e = .Fix f body) :
    (cse seen e).1 = .Fix f (cse (filterSeen f seen) body).1 := by
  rw [cse]; split <;> simp_all

theorem cse_app {f a : Expr} (h : uniqueOptimizationBinders e = .App f a) :
    (cse seen e).1 = .App (cse seen f).1 (cse seen a).1 := by
  rw [cse]; split <;> simp_all

theorem cse_force {a : Expr} (h : uniqueOptimizationBinders e = .Force a) :
    (cse seen e).1 = .Force (cse seen a).1 := by
  rw [cse]; split <;> simp_all

theorem cse_delay {a : Expr} (h : uniqueOptimizationBinders e = .Delay a) :
    (cse seen e).1 = .Delay (cse seen a).1 := by
  rw [cse]; split <;> simp_all

theorem cse_constr {tag : Nat} {args : List Expr} (h : uniqueOptimizationBinders e = .Constr tag args) :
    (cse seen e).1 = .Constr tag (cseList seen args).1 := by
  rw [cse]; split <;> simp_all

theorem cse_case {scrut : Expr} {alts : List Expr}
    (h : uniqueOptimizationBinders e = .Case scrut alts) :
    (cse seen e).1 = .Case (cse seen scrut).1 (cseList seen alts).1 := by
  rw [cse]; split <;> simp_all

theorem cse_var {x : VarId} (h : uniqueOptimizationBinders e = .Var x) : (cse seen e).1 = .Var x := by
  rw [cse]; split <;> simp_all

theorem cse_lit {l : Moist.Plutus.Term.Const × Moist.Plutus.Term.BuiltinType}
    (h : uniqueOptimizationBinders e = .Lit l) : (cse seen e).1 = .Lit l := by
  rw [cse]; split <;> simp_all

theorem cse_builtin {b : Moist.Plutus.Term.BuiltinFun}
    (h : uniqueOptimizationBinders e = .Builtin b) : (cse seen e).1 = .Builtin b := by
  rw [cse]; split <;> simp_all

theorem cse_error (h : uniqueOptimizationBinders e = .Error) : (cse seen e).1 = .Error := by
  rw [cse]; split <;> simp_all

theorem cseList_nil : (cseList seen []).1 = [] := by
  rw [cseList]

theorem cseList_cons (a : Expr) (rest : List Expr) :
    (cseList seen (a :: rest)).1 = (cse seen a).1 :: (cseList seen rest).1 := by
  rw [cseList]

theorem cseBinds_nil (body : Expr) :
    (cseBinds seen [] body).1 = [] ∧ (cseBinds seen [] body).2.1 = (cse seen body).1 := by
  rw [cseBinds]
  cases cse seen body
  exact ⟨rfl, rfl⟩

theorem cseBinds_hit {v w : VarId} {rhs : Expr} {er : Bool} {rest : List (VarId × Expr × Bool)}
    {body : Expr} (h : reusableBinding seen (cse seen rhs).1 rest body = some w) :
    (cseBinds seen ((v, rhs, er) :: rest) body).1 =
        (cseBinds seen (renameLet v w rest body).1 (renameLet v w rest body).2).1 ∧
      (cseBinds seen ((v, rhs, er) :: rest) body).2.1 =
        (cseBinds seen (renameLet v w rest body).1 (renameLet v w rest body).2).2.1 := by
  rw [cseBinds]
  cases hc : cse seen rhs with
  | mk r c =>
    rw [hc] at h
    simp only [h]
    cases cseBinds seen (renameLet v w rest body).1 (renameLet v w rest body).2 with
    | mk k rest' => cases rest'; simp

theorem cseBinds_miss {v : VarId} {rhs : Expr} {er : Bool} {rest : List (VarId × Expr × Bool)}
    {body : Expr} (h : reusableBinding seen (cse seen rhs).1 rest body = none) :
    (cseBinds seen ((v, rhs, er) :: rest) body).1 =
        (v, (cse seen rhs).1, er) :: (cseBinds (extendSeen seen v (cse seen rhs).1) rest body).1 ∧
      (cseBinds seen ((v, rhs, er) :: rest) body).2.1 =
        (cseBinds (extendSeen seen v (cse seen rhs).1) rest body).2.1 := by
  rw [cseBinds]
  cases hc : cse seen rhs with
  | mk r c =>
    rw [hc] at h
    simp only [h]
    cases cseBinds (extendSeen seen v r) rest body with
    | mk k rest' => cases rest'; simp

end Equations

/-! ## The traversal -/

theorem lowerTotalExpr_fix_uob {env : List VarId} {f p p' : VarId} {inner inner' : Expr}
    (hb : uniqueOptimizationBinders (.Lam p inner) = .Lam p' inner') :
    lowerTotalExpr env (.Fix f (.Lam p' inner')) = lowerTotalExpr env (.Fix f (.Lam p inner)) := by
  have H := Moist.Verified.MIR.Hygiene.uniqueOptimizationBinders_lower (f :: env) (.Lam p inner)
  rw [hb, lowerTotalExpr_lam, lowerTotalExpr_lam] at H
  have H' : lowerTotalExpr (p' :: f :: env) inner' = lowerTotalExpr (p :: f :: env) inner := by
    cases h₁ : lowerTotalExpr (p' :: f :: env) inner' <;>
      cases h₂ : lowerTotalExpr (p :: f :: env) inner <;> simp_all
  rw [Moist.Verified.MIR.lowerTotalExpr_fix_lam_shift, Moist.Verified.MIR.lowerTotalExpr_fix_lam_shift, H']

theorem cse_sound : ∀ n,
    (∀ seen e env, e.nodes < n → CseRel seen env e (cse seen e).1) ∧
    (∀ seen es env, Expr.nodesList es < n → CseRelList seen env es (cseList seen es).1) ∧
    (∀ seen binds body env, Expr.nodesBinds binds + body.nodes < n →
      CseRel seen env (.Let binds body)
        (.Let (cseBinds seen binds body).1 (cseBinds seen binds body).2.1))
  | 0 => ⟨fun _ _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨ih₁, ih₂, ih₃⟩ := cse_sound n
    refine ⟨?_, ?_, ?_⟩
    · intro seen e env hn
      have hsize := uniqueOptimizationBinders_nodes e
      refine CseRel.of_lower_eq_left (Moist.Verified.MIR.Hygiene.uniqueOptimizationBinders_lower env e) ?_
      cases hu : uniqueOptimizationBinders e with
      | Var x => rw [cse_var hu]; exact CseRel.refl _
      | Lit l => rw [cse_lit hu]; exact CseRel.refl _
      | Builtin b => rw [cse_builtin hu]; exact CseRel.refl _
      | Error => rw [cse_error hu]; exact CseRel.refl _
      | Lam x body =>
        rw [hu] at hsize; simp only [Expr.nodes.eq_5] at hsize
        rw [cse_lam hu]
        exact cseRel_lam (ih₁ _ _ _ (by omega))
      | Fix f body =>
        rw [hu] at hsize; simp only [Expr.nodes.eq_6] at hsize
        rw [cse_fix hu]
        cases body with
        | Lam p inner =>
          obtain ⟨p', inner', hb⟩ := uniqueOptimizationBinders_lam p inner
          have hsize' := uniqueOptimizationBinders_nodes (.Lam p inner)
          rw [hb] at hsize'; simp only [Expr.nodes.eq_5] at hsize hsize'
          rw [cse_lam hb]
          exact CseRel.of_lower_eq_left (lowerTotalExpr_fix_uob hb)
            (cseRel_fix fun _ _ => ih₁ _ _ _ (by omega))
        | _ =>
          intro _ t ht
          rw [Moist.Verified.InlineSoundness.Rename.lowerTotalExpr_fix_nonlam _ _ _
            (fun _ _ h => by cases h)] at ht
          cases ht
      | App f a =>
        rw [hu] at hsize; simp only [Expr.nodes.eq_7] at hsize
        rw [cse_app hu]
        exact cseRel_app (ih₁ _ _ _ (by omega)) (ih₁ _ _ _ (by omega))
      | Force a =>
        rw [hu] at hsize; simp only [Expr.nodes.eq_8] at hsize
        rw [cse_force hu]
        exact cseRel_force (ih₁ _ _ _ (by omega))
      | Delay a =>
        rw [hu] at hsize; simp only [Expr.nodes.eq_9] at hsize
        rw [cse_delay hu]
        exact cseRel_delay (ih₁ _ _ _ (by omega))
      | Constr tag args =>
        rw [hu] at hsize; simp only [Expr.nodes.eq_10] at hsize
        rw [cse_constr hu]
        exact cseRel_constr (ih₂ _ _ _ (by omega))
      | Case scrut alts =>
        rw [hu] at hsize; simp only [Expr.nodes.eq_11] at hsize
        rw [cse_case hu]
        exact cseRel_case (ih₁ _ _ _ (by omega)) (ih₂ _ _ _ (by omega))
      | Let binds body =>
        rw [hu] at hsize; simp only [Expr.nodes.eq_12] at hsize
        exact (ih₃ _ _ _ _ (by omega)).trans (CseRel.of_lower_eq (cse_let_lower env hu))
    · intro seen es env hn
      cases es with
      | nil => rw [cseList_nil]; exact cseRelList_nil
      | cons a rest =>
        simp only [Expr.nodesList.eq_2] at hn
        rw [cseList_cons]
        exact cseRelList_cons (ih₁ _ _ _ (by omega)) (ih₂ _ _ _ (by omega))
    · intro seen binds body env hn
      cases binds with
      | nil =>
        simp only [Expr.nodesBinds.eq_1] at hn
        obtain ⟨h₁, h₂⟩ := cseBinds_nil (seen := seen) body
        rw [h₁, h₂]
        intro hs t ht
        rw [lowerTotalExpr_let_nil] at ht
        obtain ⟨t', ht', ho⟩ := ih₁ seen body env (by omega) hs t ht
        exact ⟨t', by rw [lowerTotalExpr_let_nil]; exact ht', ho⟩
      | cons bind rest =>
        obtain ⟨v, rhs, er⟩ := bind
        simp only [Expr.nodesBinds.eq_2] at hn
        have hrhs := cseRel_let_rhs (v := v) (er := er) (rest := rest) (body := body)
          (ih₁ seen rhs env (by omega))
        cases hr : reusableBinding seen (cse seen rhs).1 rest body with
        | some w =>
          obtain ⟨h₁, h₂⟩ := cseBinds_hit (v := v) (er := er) hr
          rw [h₁, h₂]
          obtain ⟨⟨e', hmem, halpha⟩, hguard⟩ := reusableBinding_some hr
          have hrename := Expr.nodesBinds_renameLet v w rest body
          exact (hrhs.trans (cseRel_reuse hmem halpha hguard)).trans
            (ih₃ _ _ _ _ (by omega))
        | none =>
          obtain ⟨h₁, h₂⟩ := cseBinds_miss (v := v) (er := er) hr
          rw [h₁, h₂]
          exact hrhs.trans (cseRel_let_body (ih₃ _ _ _ _ (by omega)))

end Moist.Verified.CSE

namespace Moist.Verified.MIR

open Moist.MIR

/-- Common sub-expression elimination refines its input. -/
theorem cse_refines (e : Expr) : MIRCtxRefines e (cse [] e).1 := by
  intro env
  have h := (Moist.Verified.CSE.cse_sound (e.nodes + 1)).1 [] e env (Nat.lt_succ_self _)
    (fun _ h => nomatch h)
  constructor
  · intro hs
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨t', ht', _⟩ := h t ht
    rw [ht']; rfl
  · cases ht : lowerTotalExpr env e with
    | none => trivial
    | some t =>
      obtain ⟨t', ht', ho⟩ := h t ht
      rw [ht']
      exact fun C hc => ho C (fun _ h => nomatch h) hc

end Moist.Verified.MIR
