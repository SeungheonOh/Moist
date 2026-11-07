import Moist.Verified.MIR.Primitives.LetFlattenBody

/-! # Hoisting a `let` out of an evaluation frame

The ANF primitives all have the same shape: a single-binding `let` sits in
the first-evaluated position of some frame `F`, and is moved outside it:

  `F[let v = rhs in body]  ⊑  let v = rhs in F[body]`   (v fresh for `F`).

At the UPLC level this is `F[(λ.b) r] ⊑ (λ. F↑[b]) r`, where `F↑` is `F`
with every subterm shifted past the new binder. This file proves that once,
for every frame `HoistFrame`, and lifts it to MIR through `MFrame`.

* `mirCtxRefines_of_shape` — the generic MIR → UPLC bridge: two expressions
  whose lowerings factor through a common `Option α` refine each other when
  the factored terms are open-refining and closedness is preserved.
* `HoistFrame` / `openRefines_hoist` — the UPLC hoist for one frame.
* `MFrame` / `mirCtxRefines_hoist` — the MIR hoist for one binding, and
  `mirCtxRefines_hoist_wrapLet` for a whole `wrapLet` binding list.
-/

namespace Moist.Verified.MIR

open Moist.CEK
open Moist.Plutus.Term (Term)
open Moist.MIR
open Moist.Verified (closedAt closedAtList renameTerm renameTermList shiftRename liftRename)
open Moist.Verified.Equivalence (ListRel ObsRefinesK steps listRel_mono listRel_reverse
  obsRefinesK_zero_ret obsRefinesK_of_step_compute obsRefinesK_of_step_ret
  constToTagAndFields_fields_vcon)
open Moist.Verified.Contextual (Context CtxRefines fill fill_closedAt_iff fill_compose
  closedAtList_append)
open Moist.Verified.Contextual.BisimRef (closedAtList_get)
open Moist.Verified.Contextual.SoundnessRefines (EnvRefinesK ValueRefinesK StackRefK
  OpenRefines valueRefinesK_mono stackRefK_mono obsRefinesK_error applyArgFrames_stackRefK
  listRel_refl_vcon_refines obsRefines_of_openRefines)
open Moist.Verified.FundamentalRefines (ftlr renameRefinesR renameRefinesR_shift1 RenameEnvRefR
  renameEnvRefR_extend envRefinesK_to_renameEnvRefR_shift is0preserving_lift
  is0preserving_shiftRename)

/-! ## MIR → UPLC bridge -/

/-- `OpenRefines` plus syntactic closedness preservation gives `CtxRefines`. -/
theorem ctxRefines_of_openRefines {d : Nat} {t₁ t₂ : Term}
    (hcl : ∀ k, closedAt k t₁ = true → closedAt k t₂ = true)
    (h : OpenRefines d t₁ t₂) : CtxRefines t₁ t₂ := by
  intro C hC₁
  obtain ⟨hC, ht⟩ := (fill_closedAt_iff C t₁ 0).mp hC₁
  have hC₂ := (fill_closedAt_iff C t₂ 0).mpr ⟨hC, hcl _ ht⟩
  exact ⟨hC₂, obsRefines_of_openRefines h C hC₁ hC₂⟩

/-- Two expressions whose lowerings factor through a common `P env` refine
    each other when the factored UPLC terms do. -/
theorem mirCtxRefines_of_shape {α : Type} {m₁ m₂ : Expr}
    (P : List VarId → Option α) (T₁ T₂ : List VarId → α → Term)
    (h₁ : ∀ env, lowerTotalExpr env m₁ = (P env).map (T₁ env))
    (h₂ : ∀ env, lowerTotalExpr env m₂ = (P env).map (T₂ env))
    (hcl : ∀ env a k, closedAt k (T₁ env a) = true → closedAt k (T₂ env a) = true)
    (hsem : ∀ env a, P env = some a → OpenRefines env.length (T₁ env a) (T₂ env a)) :
    MIRCtxRefines m₁ m₂ := by
  intro env
  rw [h₁, h₂]
  cases hP : P env with
  | none => exact ⟨id, trivial⟩
  | some a => exact ⟨fun _ => rfl, ctxRefines_of_openRefines (hcl env a) (hsem env a hP)⟩

/-! ## Lowering -/

/-- Prepending a variable that is not free in `e` shifts the lowering of `e`. -/
theorem lowerTotalExpr_prepend_unused (env : List VarId) (v : VarId) (e : Expr)
    (h : (freeVars e).contains v = false) :
    lowerTotalExpr (v :: env) e = (lowerTotalExpr env e).map (renameTerm (shiftRename 1)) := by
  have h' := expandFix_freeVars_not_contains e v h
  cases hl : lowerTotalExpr env e with
  | none => exact lowerTotal_prepend_unused_none env v _ h' hl
  | some t => exact lowerTotal_prepend_unused env v _ h' t hl

theorem lowerTotalExprList_prepend_unused (env : List VarId) (v : VarId) :
    ∀ (es : List Expr), (∀ e ∈ es, (freeVars e).contains v = false) →
      lowerTotalExprList (v :: env) es =
        (lowerTotalExprList env es).map (renameTermList (shiftRename 1))
  | [], _ => by simp [lowerTotalExprList_nil, renameTermList]
  | e :: es, h => by
    rw [lowerTotalExprList_cons, lowerTotalExprList_cons,
      lowerTotalExpr_prepend_unused env v e (h e (.head _)),
      lowerTotalExprList_prepend_unused env v es (fun e he => h e (.tail _ he))]
    cases lowerTotalExpr env e <;> cases lowerTotalExprList env es <;> rfl

theorem lowerTotalExprList_append (env : List VarId) (pre post : List Expr) :
    lowerTotalExprList env (pre ++ post) =
      (lowerTotalExprList env pre).bind fun pre' =>
        (lowerTotalExprList env post).map fun post' => pre' ++ post' := by
  induction pre with
  | nil => simp [lowerTotalExprList_nil]
  | cons e pre ih =>
    rw [List.cons_append, lowerTotalExprList_cons, lowerTotalExprList_cons, ih]
    cases lowerTotalExpr env e <;> cases lowerTotalExprList env pre <;>
      cases lowerTotalExprList env post <;> rfl

theorem lowerTotalExpr_let_single (env : List VarId) (v : VarId) (rhs body : Expr) (er : Bool) :
    lowerTotalExpr env (.Let [(v, rhs, er)] body) =
      (lowerTotalExpr env rhs).bind fun tr =>
        (lowerTotalExpr (v :: env) body).map fun tb => .Apply (.Lam 0 tb) tr := by
  simp only [lowerTotalExpr, expandFix, expandFixBinds, lowerTotal, lowerTotalLet]
  cases lowerTotal env (expandFix rhs) <;> cases lowerTotal (v :: env) (expandFix body) <;> rfl

theorem lowerTotalExpr_wrapLet (bs : List (VarId × Expr × Bool)) (body : Expr)
    (env : List VarId) : lowerTotalExpr env (wrapLet bs body) = lowerTotalExpr env (.Let bs body) := by
  cases bs with
  | nil => simp only [wrapLet, lowerTotalExpr, expandFix, expandFixBinds, lowerTotal, lowerTotalLet]
  | cons _ _ => rfl

theorem lowerTotalExpr_wrapLet_append (bs₁ bs₂ : List (VarId × Expr × Bool)) (body : Expr)
    (env : List VarId) :
    lowerTotalExpr env (wrapLet (bs₁ ++ bs₂) body) =
      lowerTotalExpr env (wrapLet bs₁ (wrapLet bs₂ body)) := by
  cases bs₂ with
  | nil => simp only [List.append_nil, wrapLet]
  | cons _ _ =>
    rw [lowerTotalExpr_wrapLet, lowerTotalExpr_wrapLet bs₁, ← lowerTotalExpr_let_flatten_body]; rfl

theorem freeVarsLet_not_contains_of_fresh (rest : List (VarId × Expr × Bool)) (body : Expr)
    (y : VarId) (hrest : ∀ r ∈ rest, (freeVars r.2.1).contains y = false)
    (hbody : (freeVars body).contains y = false) :
    (freeVarsLet rest body).contains y = false := by
  induction rest with
  | nil => rw [freeVarsLet]; exact hbody
  | cons r rest ih =>
    rw [freeVarsLet]
    exact VarSet.union_not_contains_fwd _ _ _ (hrest r (.head _))
      (VarSet.erase_not_contains_fwd _ _ _ (ih fun r hr => hrest r (.tail _ hr)))

/-! ## Value terms

Terms in an already-evaluated frame position (`g` in `g □`, the prefix of a
`Constr`) must be values that step in one CEK transition. -/

/-- Terms that evaluate in one CEK step without touching the stack.
    `Var 0` is excluded: lowering never produces it, and it errors. -/
def IsValueTerm (d : Nat) : Term → Prop
  | .Var n => 0 < n ∧ n ≤ d
  | .Constant _ => True
  | .Builtin _ => True
  | .Lam _ b => closedAt (d + 1) b = true
  | _ => False

/-- The value a value term steps to (junk outside `IsValueTerm`). -/
def valueOf (ρ : CekEnv) : Term → CekValue
  | .Var n => (ρ.lookup n).getD (.VCon .Unit)
  | .Constant (c, _) => .VCon c
  | .Builtin b => .VBuiltin b [] (expectedArgs b)
  | .Lam _ b => .VLam b ρ
  | _ => .VCon .Unit

theorem lookup_extend_succ (ρ : CekEnv) (w : CekValue) {n : Nat} (hn : 0 < n) :
    (ρ.extend w).lookup (n + 1) = ρ.lookup n := by
  match n, hn with
  | k + 1, _ => rfl

/-- A value term steps to its value on the left, its shift steps to a related
    value under one extra binder on the right. -/
theorem valueTerm_rel {d i : Nat} {t : Term} (ht : IsValueTerm d t)
    {ρ₁ ρ₂ : CekEnv} (w : CekValue) (henv : EnvRefinesK i d ρ₁ ρ₂) :
    (∀ π, step (.compute π ρ₁ t) = .ret π (valueOf ρ₁ t)) ∧
    (∀ π, step (.compute π (ρ₂.extend w) (renameTerm (shiftRename 1) t)) =
      .ret π (valueOf (ρ₂.extend w) (renameTerm (shiftRename 1) t))) ∧
    ValueRefinesK i (valueOf ρ₁ t) (valueOf (ρ₂.extend w) (renameTerm (shiftRename 1) t)) := by
  match t, ht with
  | .Var n, ⟨hn, hnd⟩ =>
    obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := henv n hn hnd
    have h₂' : (ρ₂.extend w).lookup (shiftRename 1 n) = some v₂ := by
      rw [Moist.Verified.shiftRename_ge hn, lookup_extend_succ ρ₂ w hn, h₂]
    refine ⟨fun π => ?_, fun π => ?_, ?_⟩
    · simp only [valueOf, step, h₁, Option.getD_some]
    · simp only [renameTerm, valueOf, step, h₂', Option.getD_some]
    · simpa only [renameTerm, valueOf, h₁, h₂', Option.getD_some] using hv
  | .Constant (c, _), _ =>
    refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
    cases i <;> simp [renameTerm, valueOf, ValueRefinesK]
  | .Builtin b, _ =>
    refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
    cases i <;> simp [renameTerm, valueOf, ValueRefinesK, ListRel]
  | .Lam x b, hb =>
    refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
    cases i with
    | zero => simp [renameTerm, valueOf, ValueRefinesK]
    | succ k =>
      simp only [renameTerm, valueOf, ValueRefinesK]
      intro j hj a₁ a₂ ha i' hi' π₁ π₂ hπ
      exact renameRefinesR (liftRename (shiftRename 1)) (is0preserving_lift _) (d + 1) b hb
        j j (Nat.le_refl _) _ _
        (renameEnvRefR_extend (is0preserving_shiftRename (Nat.le_refl 1))
          (envRefinesK_to_renameEnvRefR_shift (envRefinesK_mono (by omega) henv)) ha)
        i' hi' π₁ π₂ hπ

/-- The shape of a lowered MIR atom: `Var n` (`n ≥ 1`), a constant, or a builtin. -/
def isLeafAtomTerm (t : Term) : Prop :=
  (∃ n, n ≥ 1 ∧ t = .Var n) ∨ (∃ ct, t = .Constant ct) ∨ (∃ b, t = .Builtin b)

/-- For atom MIR expressions, the lowering produces a leaf term. -/
theorem lowerTotal_atom_isLeafAtom :
    ∀ (env : List VarId) (g : Expr) (t_g : Term),
      g.isAtom = true →
      lowerTotal env (expandFix g) = some t_g →
      isLeafAtomTerm t_g := by
  intro env g t_g hatom hlow
  cases g with
  | Var x =>
    simp only [expandFix, lowerTotal] at hlow
    cases h : envLookupT env x with
    | none => rw [h] at hlow; simp at hlow
    | some idx =>
      rw [h] at hlow; simp at hlow; subst hlow
      exact .inl ⟨idx + 1, Nat.succ_le_succ (Nat.zero_le _), rfl⟩
  | Lit p =>
    obtain ⟨c, ty⟩ := p
    simp only [expandFix, lowerTotal] at hlow
    cases hlow
    exact .inr (.inl ⟨(c, ty), rfl⟩)
  | Builtin b =>
    simp only [expandFix, lowerTotal] at hlow
    cases hlow
    exact .inr (.inr ⟨b, rfl⟩)
  | _ => simp [Expr.isAtom] at hatom

theorem lowerTotalExpr_atom_valueTerm {env : List VarId} {g : Expr} {t : Term}
    (hg : g.isAtom = true) (ht : lowerTotalExpr env g = some t) : IsValueTerm env.length t := by
  have hc := lowerTotalExpr_closedAt ht
  rcases lowerTotal_atom_isLeafAtom env _ _ hg ht with ⟨n, hn, rfl⟩ | ⟨c, rfl⟩ | ⟨b, rfl⟩
  · simp only [closedAt, decide_eq_true_eq] at hc; exact ⟨hn, hc⟩
  · trivial
  · trivial

theorem lowerTotalExprList_valueTerms {env : List VarId} :
    ∀ {es : List Expr} {ts : List Term}, (∀ a ∈ es, a.isAtom = true) →
      lowerTotalExprList env es = some ts → ∀ t ∈ ts, IsValueTerm env.length t
  | [], _, _, h => by simp [lowerTotalExprList_nil] at h; subst h; simp
  | e :: es, ts, hA, h => by
    rw [lowerTotalExprList_cons] at h
    cases he : lowerTotalExpr env e <;> cases hes : lowerTotalExprList env es <;>
      simp [he, hes] at h
    subst h
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact lowerTotalExpr_atom_valueTerm (hA e (.head _)) he
    · exact lowerTotalExprList_valueTerms (fun a ha => hA a (.tail _ ha)) hes t ht

/-! ## Hoist frames -/

/-- A single-hole UPLC evaluation frame, the hole being evaluated first among
    the not-yet-evaluated positions. -/
inductive HoistFrame where
  | force
  | appFun (arg : Term)
  | appArg (fn : Term)
  | case (alts : List Term)
  | constr (tag : Nat) (pre post : List Term)

namespace HoistFrame

def fill : HoistFrame → Term → Term
  | force, t => .Force t
  | appFun x, t => .Apply t x
  | appArg g, t => .Apply g t
  | case alts, t => .Case t alts
  | constr tag pre post, t => .Constr tag (pre ++ t :: post)

/-- The frame seen from under one extra binder. -/
def shift : HoistFrame → HoistFrame
  | force => force
  | appFun x => appFun (renameTerm (shiftRename 1) x)
  | appArg g => appArg (renameTerm (shiftRename 1) g)
  | case alts => case (renameTermList (shiftRename 1) alts)
  | constr tag pre post =>
    constr tag (renameTermList (shiftRename 1) pre) (renameTermList (shiftRename 1) post)

/-- Subterms closed at depth `d`; already-evaluated positions are values. -/
def WF (d : Nat) : HoistFrame → Prop
  | force => True
  | appFun x => closedAt d x = true
  | appArg g => IsValueTerm d g
  | case alts => closedAtList d alts = true
  | constr _ pre post => (∀ p ∈ pre, IsValueTerm d p) ∧ closedAtList d post = true

/-- The stack on which the hole is evaluated. -/
def push (ρ : CekEnv) : HoistFrame → Stack → Stack
  | force, π => .force :: π
  | appFun x, π => .arg x ρ :: π
  | appArg g, π => .funV (valueOf ρ g) :: π
  | case alts, π => .caseScrutinee alts ρ :: π
  | constr tag pre post, π => .constrField tag (pre.map (valueOf ρ)).reverse post ρ :: π

end HoistFrame

theorem renameTermList_eq_map (σ : Nat → Nat) :
    ∀ (ts : List Term), renameTermList σ ts = ts.map (renameTerm σ)
  | [] => rfl
  | t :: ts => by rw [renameTermList, List.map_cons, renameTermList_eq_map σ ts]

theorem getElem?_renameTermList (σ : Nat → Nat) (ts : List Term) (n : Nat) :
    (renameTermList σ ts)[n]? = ts[n]?.map (renameTerm σ) := by
  rw [renameTermList_eq_map, List.getElem?_map]

/-- `arg` frame against its shift. -/
theorem stackRefK_arg_shift {i d : Nat} {x : Term} {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv}
    {w : CekValue} (hx : closedAt d x = true) (henv : EnvRefinesK i d ρ₁ ρ₂)
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i (.arg x ρ₁ :: π₁)
      (.arg (renameTerm (shiftRename 1) x) (ρ₂.extend w) :: π₂) := by
  intro j hj v₁ v₂ hv
  exact obsRefinesK_of_steps_left (n := 1) rfl <| obsRefinesK_of_steps_right (n := 1) rfl <|
    renameRefinesR_shift1 d x hx j j (Nat.le_refl _) ρ₁ (ρ₂.extend w)
      (envRefinesK_to_renameEnvRefR_shift (envRefinesK_mono hj henv)) j (Nat.le_refl _) _ _
      (stackRefK_funV_top_aug hv (stackRefK_mono hj hπ))

/-- `caseScrutinee` frame against its shift. -/
theorem stackRefK_case_shift {i d : Nat} {alts : List Term} {π₁ π₂ : Stack}
    {ρ₁ ρ₂ : CekEnv} {w : CekValue} (halts : closedAtList d alts = true)
    (henv : EnvRefinesK i d ρ₁ ρ₂) (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i (.caseScrutinee alts ρ₁ :: π₁)
      (.caseScrutinee (renameTermList (shiftRename 1) alts) (ρ₂.extend w) :: π₂) := by
  intro j hj v₁ v₂ hv
  match j with
  | 0 => exact obsRefinesK_zero_ret
  | m + 1 =>
  have halt : ∀ {n alt fs₁ fs₂}, alts[n]? = some alt → ListRel (ValueRefinesK m) fs₁ fs₂ →
      ObsRefinesK m (.compute (fs₁.map Frame.applyArg ++ π₁) ρ₁ alt)
        (.compute (fs₂.map Frame.applyArg ++ π₂) (ρ₂.extend w)
          (renameTerm (shiftRename 1) alt)) := fun hn hfs =>
    renameRefinesR_shift1 d _ (closedAtList_get d alts _ _ halts hn) m m (Nat.le_refl _) ρ₁
      (ρ₂.extend w) (envRefinesK_to_renameEnvRefR_shift (envRefinesK_mono (by omega) henv))
      m (Nat.le_refl _) _ _ (applyArgFrames_stackRefK hfs (stackRefK_mono (by omega) hπ))
  refine obsRefinesK_of_step_ret ?_
  cases v₁ <;> cases v₂ <;> simp only [ValueRefinesK] at hv <;> try exact obsRefinesK_error _
  case VCon.VCon c _ =>
    subst hv
    have hvcon := constToTagAndFields_fields_vcon c
    simp only [step, getElem?_renameTermList, Moist.Verified.renameTermList_length]
    cases hc : constToTagAndFields c with
    | none => exact obsRefinesK_error _
    | some r =>
      obtain ⟨tag, numCtors, fs⟩ := r
      rw [hc] at hvcon
      simp only []
      split
      · exact obsRefinesK_error _
      · cases h : alts[tag]? with
        | none => exact obsRefinesK_error _
        | some alt => exact halt h (listRel_refl_vcon_refines m fs hvcon)
  case VConstr.VConstr tag fs₁ _ fs₂ =>
    obtain ⟨rfl, hfs⟩ := hv
    simp only [step, getElem?_renameTermList]
    cases h : alts[tag]? with
    | none => exact obsRefinesK_error _
    | some alt => exact halt h hfs

/-- `constrField` frame against its shift. -/
theorem stackRefK_constrField_shift {d tag : Nat} :
    ∀ (post : List Term), closedAtList d post = true →
    ∀ {i : Nat} {done₁ done₂ : List CekValue} {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv} {w : CekValue},
      ListRel (ValueRefinesK i) done₁ done₂ → EnvRefinesK i d ρ₁ ρ₂ →
      StackRefK ValueRefinesK i π₁ π₂ →
      StackRefK ValueRefinesK i (.constrField tag done₁ post ρ₁ :: π₁)
        (.constrField tag done₂ (renameTermList (shiftRename 1) post) (ρ₂.extend w) :: π₂)
  | [], _, _, done₁, done₂, _, _, _, _, _, hdone, _, hπ => by
    intro j hj v₁ v₂ hv
    match j with
    | 0 => exact obsRefinesK_zero_ret
    | m + 1 =>
    refine obsRefinesK_of_step_ret ?_
    refine hπ m (by omega) _ _ ?_
    have hl : ListRel (ValueRefinesK m) (v₁ :: done₁) (v₂ :: done₂) :=
      ⟨valueRefinesK_mono (by omega) _ _ hv,
       listRel_mono (fun _ _ h => valueRefinesK_mono (by omega) _ _ h) hdone⟩
    cases m with
    | zero => simp only [ValueRefinesK]
    | succ m =>
      simp only [ValueRefinesK]
      exact ⟨trivial, listRel_reverse
        (listRel_mono (fun _ _ h => valueRefinesK_mono (by omega) _ _ h) hl)⟩
  | p :: ps, hcl, _, done₁, done₂, _, _, _, _, _, hdone, henv, hπ => by
    simp only [closedAtList, Bool.and_eq_true] at hcl
    intro j hj v₁ v₂ hv
    match j with
    | 0 => exact obsRefinesK_zero_ret
    | m + 1 =>
    refine obsRefinesK_of_step_ret ?_
    have henv' := envRefinesK_mono (Nat.le_trans (Nat.le_succ m) hj) henv
    exact renameRefinesR_shift1 d p hcl.1 m m (Nat.le_refl _) _ _
      (envRefinesK_to_renameEnvRefR_shift henv') m (Nat.le_refl _) _ _
      (stackRefK_constrField_shift ps hcl.2
        ⟨valueRefinesK_mono (by omega) _ _ hv,
         listRel_mono (fun _ _ h => valueRefinesK_mono (by omega) _ _ h) hdone⟩
        henv' (stackRefK_mono (by omega) hπ))

/-- Evaluating the value-term prefix of a `Constr` that is already under way. -/
private theorem steps_constrField {tag : Nat} {post : List Term} {ρ : CekEnv} {π : Stack}
    {t : Term} : ∀ (ps : List Term), (∀ p ∈ ps, ∀ π, step (.compute π ρ p) = .ret π (valueOf ρ p)) →
    ∀ (done : List CekValue) (v : CekValue),
      steps (2 * ps.length + 1) (.ret (.constrField tag done (ps ++ t :: post) ρ :: π) v) =
        .compute (.constrField tag ((ps.map (valueOf ρ)).reverse ++ v :: done) post ρ :: π) ρ t
  | [], _, _, _ => rfl
  | p :: ps, hps, done, v => by
    have h2 : steps 2 (.ret (.constrField tag done (p :: (ps ++ t :: post)) ρ :: π) v) =
        .ret (.constrField tag (v :: done) (ps ++ t :: post) ρ :: π) (valueOf ρ p) :=
      hps p (.head _) _
    rw [show 2 * (p :: ps).length + 1 = 2 + (2 * ps.length + 1) by simp; omega, steps_trans,
      List.cons_append, h2, steps_constrField ps (fun q hq => hps q (.tail _ hq))]
    simp

/-- Evaluating a `Constr` up to the first non-value position. -/
private theorem steps_constr {tag : Nat} {pre post : List Term} {ρ : CekEnv} {π : Stack}
    (hpre : ∀ p ∈ pre, ∀ π, step (.compute π ρ p) = .ret π (valueOf ρ p)) (t : Term) :
    steps (2 * pre.length + 1) (.compute π ρ (.Constr tag (pre ++ t :: post))) =
      .compute (.constrField tag (pre.map (valueOf ρ)).reverse post ρ :: π) ρ t := by
  cases pre with
  | nil => rfl
  | cons p ps =>
    have h2 : steps 2 (.compute π ρ (.Constr tag (p :: (ps ++ t :: post)))) =
        .ret (.constrField tag [] (ps ++ t :: post) ρ :: π) (valueOf ρ p) :=
      hpre p (.head _) _
    rw [show 2 * (p :: ps).length + 1 = 2 + (2 * ps.length + 1) by simp; omega, steps_trans,
      List.cons_append, h2, steps_constrField ps (fun q hq => hpre q (.tail _ hq))]
    simp

namespace HoistFrame

/-- Both sides reach the hole, and the stacks they reach it on are related. -/
theorem rel (F : HoistFrame) {d i : Nat} (hF : F.WF d) {ρ₁ ρ₂ : CekEnv} {π₁ π₂ : Stack}
    (w : CekValue) (henv : EnvRefinesK i d ρ₁ ρ₂) (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    (∃ n, ∀ t, steps n (.compute π₁ ρ₁ (F.fill t)) = .compute (F.push ρ₁ π₁) ρ₁ t) ∧
    (∃ n, ∀ t, steps n (.compute π₂ (ρ₂.extend w) (F.shift.fill t)) =
      .compute (F.shift.push (ρ₂.extend w) π₂) (ρ₂.extend w) t) ∧
    StackRefK ValueRefinesK i (F.push ρ₁ π₁) (F.shift.push (ρ₂.extend w) π₂) := by
  cases F with
  | force => exact ⟨⟨1, fun _ => rfl⟩, ⟨1, fun _ => rfl⟩, stackRefK_force_augment hπ⟩
  | appFun x => exact ⟨⟨1, fun _ => rfl⟩, ⟨1, fun _ => rfl⟩, stackRefK_arg_shift hF henv hπ⟩
  | appArg g =>
    obtain ⟨h₁, h₂, hv⟩ := valueTerm_rel hF w henv
    exact ⟨⟨3, fun t => congrArg (steps 1) (h₁ _)⟩, ⟨3, fun t => congrArg (steps 1) (h₂ _)⟩,
      stackRefK_funV_top_aug hv hπ⟩
  | case alts => exact ⟨⟨1, fun _ => rfl⟩, ⟨1, fun _ => rfl⟩, stackRefK_case_shift hF henv hπ⟩
  | constr tag pre post =>
    obtain ⟨hpre, hpost⟩ := hF
    have hrel := fun p hp => valueTerm_rel (hpre p hp) w henv
    have hl : ListRel (ValueRefinesK i) (pre.map (valueOf ρ₁))
        ((renameTermList (shiftRename 1) pre).map (valueOf (ρ₂.extend w))) := by
      clear hpost
      induction pre with
      | nil => trivial
      | cons p ps ih =>
        exact ⟨(hrel p (.head _)).2.2, ih (fun q hq => hpre q (.tail _ hq))
          (fun q hq => hrel q (.tail _ hq))⟩
    refine ⟨⟨_, steps_constr fun p hp => (hrel p hp).1⟩, ⟨_, steps_constr ?_⟩,
      stackRefK_constrField_shift post hpost (listRel_reverse hl) henv hπ⟩
    intro p' hp'
    rw [renameTermList_eq_map] at hp'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hp'
    exact (hrel p hp).2.1

theorem closedAt_hoist (F : HoistFrame) {k : Nat} {tb tr : Term}
    (h : closedAt k (F.fill (.Apply (.Lam 0 tb) tr)) = true) :
    closedAt k (.Apply (.Lam 0 (F.shift.fill tb)) tr) = true := by
  have sh := fun t => Moist.Verified.closedAt_renameTerm_shiftRename t k 1 (Nat.le_refl 1) (by omega)
  have shl := fun ts =>
    Moist.Verified.closedAtList_renameTermList_shiftRename ts k 1 (Nat.le_refl 1) (by omega)
  cases F with
  | constr tag pre post =>
    simp only [fill, shift, closedAt, closedAtList_append, closedAtList, Bool.and_eq_true] at h ⊢
    exact ⟨⟨shl _ h.1, h.2.1.1, shl _ h.2.2⟩, h.2.1.2⟩
  | _ =>
    simp only [fill, shift, closedAt, Bool.and_eq_true] at h ⊢
    first
    | exact ⟨h.1, h.2⟩
    | exact ⟨⟨h.1.1, sh _ h.2⟩, h.1.2⟩
    | exact ⟨⟨sh _ h.1, h.2.1⟩, h.2.2⟩
    | exact ⟨⟨h.1.1, shl _ h.2⟩, h.1.2⟩

end HoistFrame

/-- **Let-hoisting through a frame**: `F[(λ.b) r] ⊑ (λ. F↑[b]) r`. -/
theorem openRefines_hoist (F : HoistFrame) {d : Nat} {tr tb : Term} (hF : F.WF d)
    (hr : closedAt d tr = true) (hb : closedAt (d + 1) tb = true) :
    OpenRefines d (F.fill (.Apply (.Lam 0 tb) tr)) (.Apply (.Lam 0 (F.shift.fill tb)) tr) := by
  intro k j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  obtain ⟨⟨n₁, hn₁⟩, -, -⟩ := F.rel hF (.VCon .Unit) (envRefinesK_mono hi henv) hπ
  have hL : steps (n₁ + 3) (.compute π₁ ρ₁ (F.fill (.Apply (.Lam 0 tb) tr))) =
      .compute (.funV (.VLam tb ρ₁) :: F.push ρ₁ π₁) ρ₁ tr := by
    rw [steps_trans, hn₁]; rfl
  refine obsRefinesK_of_steps_left hL <| obsRefinesK_of_steps_right (n := 3) rfl <|
    ftlr d tr hr j j (Nat.le_refl _) ρ₁ ρ₂ henv i hi _ _ ?_
  intro j' hj' v₁ v₂ hv
  have henv' := envRefinesK_mono (Nat.le_trans hj' hi) henv
  obtain ⟨-, ⟨n₂, hn₂⟩, hstk⟩ := F.rel hF v₂ henv' (stackRefK_mono hj' hπ)
  have hR : steps (1 + n₂) (.ret (.funV (.VLam (F.shift.fill tb) ρ₂) :: π₂) v₂) =
      .compute (F.shift.push (ρ₂.extend v₂) π₂) (ρ₂.extend v₂) tb := by
    rw [steps_trans]; exact hn₂ tb
  exact obsRefinesK_of_steps_left (n := 1) rfl <| obsRefinesK_of_steps_right hR <|
    ftlr (d + 1) tb hb j' j' (Nat.le_refl _) _ _ (envRefinesK_extend henv' hv)
      j' (Nat.le_refl _) _ _ hstk

theorem ctxRefines_fill (C : Context) {t₁ t₂ : Term} (h : CtxRefines t₁ t₂) :
    CtxRefines (fill C t₁) (fill C t₂) := by
  intro C' hC'
  simp only [← fill_compose] at hC' ⊢
  exact h _ hC'

def HoistFrame.toContext : HoistFrame → Context
  | .force => .Force .Hole
  | .appFun x => .AppLeft .Hole x
  | .appArg g => .AppRight g .Hole
  | .case alts => .Case .Hole alts
  | .constr tag pre post => .Constr tag pre .Hole post

theorem HoistFrame.fill_eq (F : HoistFrame) (t : Term) :
    F.fill t = Moist.Verified.Contextual.fill F.toContext t := by
  cases F <;> simp [HoistFrame.fill, HoistFrame.toContext, Moist.Verified.Contextual.fill]

/-! ## MIR frames -/

/-- A MIR evaluation frame; `fill` places an expression in its hole. -/
inductive MFrame where
  | force
  | appFun (arg : Expr)
  | appArg (fn : Expr)
  | case (alts : List Expr)
  | constr (tag : Nat) (pre post : List Expr)
  | letRhs (x : VarId) (er : Bool) (rest : List (VarId × Expr × Bool)) (body : Expr)

namespace MFrame

def fill : MFrame → Expr → Expr
  | force, e => .Force e
  | appFun x, e => .App e x
  | appArg g, e => .App g e
  | case alts, e => .Case e alts
  | constr tag pre post, e => .Constr tag (pre ++ e :: post)
  | letRhs x er rest body, e => .Let ((x, e, er) :: rest) body

/-- `v` is not free in the frame's own subexpressions. -/
def Fresh (v : VarId) : MFrame → Prop
  | force => True
  | appFun x => (freeVars x).contains v = false
  | appArg g => (freeVars g).contains v = false
  | case alts => ∀ a ∈ alts, (freeVars a).contains v = false
  | constr _ pre post => ∀ a ∈ pre ++ post, (freeVars a).contains v = false
  | letRhs _ _ rest body =>
    (∀ r ∈ rest, (freeVars r.2.1).contains v = false) ∧ (freeVars body).contains v = false

/-- Positions evaluated before the hole hold atoms. -/
def Atomic : MFrame → Prop
  | appArg g => g.isAtom = true
  | constr _ pre _ => ∀ a ∈ pre, a.isAtom = true
  | _ => True

def lower (env : List VarId) : MFrame → Option HoistFrame
  | force => some .force
  | appFun x => (lowerTotalExpr env x).map .appFun
  | appArg g => (lowerTotalExpr env g).map .appArg
  | case alts => (lowerTotalExprList env alts).map .case
  | constr tag pre post =>
    (lowerTotalExprList env pre).bind fun pre' =>
      (lowerTotalExprList env post).map fun post' => .constr tag pre' post'
  | letRhs x _ rest body =>
    (lowerTotalLet (x :: env) (expandFixBinds rest) (expandFix body)).map
      fun t => .appArg (.Lam 0 t)

theorem lowerTotalExpr_fill (F : MFrame) (env : List VarId) (e : Expr) :
    lowerTotalExpr env (F.fill e) =
      (lowerTotalExpr env e).bind fun t => (F.lower env).map (·.fill t) := by
  cases F with
  | force =>
    rw [fill, lower, lowerTotalExpr_force]; cases lowerTotalExpr env e <;> rfl
  | appFun x =>
    rw [fill, lower, lowerTotalExpr_app]
    cases lowerTotalExpr env e <;> cases lowerTotalExpr env x <;> rfl
  | appArg g =>
    rw [fill, lower, lowerTotalExpr_app]
    cases lowerTotalExpr env e <;> cases lowerTotalExpr env g <;> rfl
  | case alts =>
    rw [fill, lower, lowerTotalExpr_case_of_list]
    cases lowerTotalExpr env e <;> cases lowerTotalExprList env alts <;> rfl
  | constr tag pre post =>
    rw [fill, lower, lowerTotalExpr_constr_of_list, lowerTotalExprList_append,
      lowerTotalExprList_cons]
    cases lowerTotalExpr env e <;> cases lowerTotalExprList env pre <;>
      cases lowerTotalExprList env post <;> rfl
  | letRhs x er rest body =>
    simp only [fill, lower, lowerTotalExpr, expandFix, expandFixBinds, lowerTotal, lowerTotalLet]
    cases lowerTotal env (expandFix e) <;>
      cases lowerTotalLet (x :: env) (expandFixBinds rest) (expandFix body) <;> rfl

theorem lower_cons (F : MFrame) {v : VarId} (hv : F.Fresh v) (env : List VarId) :
    F.lower (v :: env) = (F.lower env).map HoistFrame.shift := by
  cases F with
  | force => rfl
  | appFun x =>
    simp only [lower, lowerTotalExpr_prepend_unused env v x hv]
    cases lowerTotalExpr env x <;> rfl
  | appArg g =>
    simp only [lower, lowerTotalExpr_prepend_unused env v g hv]
    cases lowerTotalExpr env g <;> rfl
  | case alts =>
    simp only [lower, lowerTotalExprList_prepend_unused env v alts hv]
    cases lowerTotalExprList env alts <;> rfl
  | constr tag pre post =>
    simp only [lower,
      lowerTotalExprList_prepend_unused env v pre (fun a ha => hv a (List.mem_append_left _ ha)),
      lowerTotalExprList_prepend_unused env v post (fun a ha => hv a (List.mem_append_right _ ha))]
    cases lowerTotalExprList env pre <;> cases lowerTotalExprList env post <;> rfl
  | letRhs x er rest body =>
    have hfv := expandFixBinds_freeVars_not_contains rest body v
      (freeVarsLet_not_contains_of_fresh rest body v hv.1 hv.2)
    simp only [lower]
    cases h : lowerTotalLet (x :: env) (expandFixBinds rest) (expandFix body) with
    | none =>
      simpa using lowerTotalLet_prepend_unused_none_gen [x] env v _ _ (.inl hfv) h
    | some t =>
      have h' := lowerTotalLet_prepend_unused_gen [x] env v _ _ (.inl hfv) t h
      simp only [List.cons_append, List.nil_append, List.length_singleton] at h'
      simp only [h', Option.map_some, HoistFrame.shift, renameTerm,
        Moist.Verified.liftRename_shiftRename (Nat.le_refl 1)]

theorem lower_wf (F : MFrame) (hA : F.Atomic) {env : List VarId} {H : HoistFrame}
    (h : F.lower env = some H) : H.WF env.length := by
  cases F with
  | force => cases h; trivial
  | appFun x =>
    cases hx : lowerTotalExpr env x <;> simp [lower, hx] at h
    subst h; exact lowerTotalExpr_closedAt hx
  | appArg g =>
    cases hg : lowerTotalExpr env g <;> simp [lower, hg] at h
    subst h; exact lowerTotalExpr_atom_valueTerm hA hg
  | case alts =>
    cases ha : lowerTotalExprList env alts <;> simp [lower, ha] at h
    subst h; exact lowerTotalList_closedAtList env _ _ ha
  | constr tag pre post =>
    cases hp : lowerTotalExprList env pre <;> cases hq : lowerTotalExprList env post <;>
      simp [lower, hp, hq] at h
    subst h
    exact ⟨lowerTotalExprList_valueTerms hA hp, lowerTotalList_closedAtList env _ _ hq⟩
  | letRhs x er rest body =>
    cases ht : lowerTotalLet (x :: env) (expandFixBinds rest) (expandFix body) <;>
      simp [lower, ht] at h
    subst h
    simpa using lowerTotalLet_closedAt (x :: env) _ _ _ ht

end MFrame

/-- **Single-binding let-hoist** out of any MIR frame. -/
theorem mirCtxRefines_hoist (F : MFrame) (hA : F.Atomic) {v : VarId} (hv : F.Fresh v)
    (rhs body : Expr) (er : Bool) :
    MIRCtxRefines (F.fill (.Let [(v, rhs, er)] body)) (.Let [(v, rhs, er)] (F.fill body)) := by
  refine mirCtxRefines_of_shape
    (fun env => (lowerTotalExpr env rhs).bind fun tr =>
      (lowerTotalExpr (v :: env) body).bind fun tb => (F.lower env).map fun H => (tr, tb, H))
    (fun _ a => a.2.2.fill (.Apply (.Lam 0 a.2.1) a.1))
    (fun _ a => .Apply (.Lam 0 (a.2.2.shift.fill a.2.1)) a.1)
    (fun env => ?_) (fun env => ?_) (fun _ a _ h => a.2.2.closedAt_hoist h) ?_
  · rw [F.lowerTotalExpr_fill, lowerTotalExpr_let_single]
    dsimp only
    cases lowerTotalExpr env rhs <;> cases lowerTotalExpr (v :: env) body <;>
      cases F.lower env <;> rfl
  · rw [lowerTotalExpr_let_single, F.lowerTotalExpr_fill, F.lower_cons hv]
    dsimp only
    cases lowerTotalExpr env rhs <;> cases lowerTotalExpr (v :: env) body <;>
      cases F.lower env <;> rfl
  · intro env ⟨tr, tb, H⟩ h
    cases hr : lowerTotalExpr env rhs <;> cases hb : lowerTotalExpr (v :: env) body <;>
      cases hH : F.lower env <;> simp [hr, hb, hH] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact openRefines_hoist _ (F.lower_wf hA hH) (lowerTotalExpr_closedAt hr)
      (by simpa using lowerTotalExpr_closedAt hb)

theorem mirCtxRefines_fill (F : MFrame) {a b : Expr} (h : MIRCtxRefines a b) :
    MIRCtxRefines (F.fill a) (F.fill b) := by
  intro env
  obtain ⟨hs, hc⟩ := h env
  rw [F.lowerTotalExpr_fill, F.lowerTotalExpr_fill]
  cases ha : lowerTotalExpr env a with
  | none => exact ⟨by simp, trivial⟩
  | some ta =>
    rw [ha] at hs hc
    cases hb : lowerTotalExpr env b with
    | none => rw [hb] at hs; simp at hs
    | some tb =>
      rw [hb] at hc
      cases F.lower env with
      | none => exact ⟨by simp, trivial⟩
      | some H =>
        refine ⟨fun _ => rfl, ?_⟩
        simp only [Option.bind_some, Option.map_some]
        rw [H.fill_eq, H.fill_eq]
        exact ctxRefines_fill _ hc

theorem mirCtxRefines_wrapLet_body {bs : List (VarId × Expr × Bool)} {b₁ b₂ : Expr}
    (h : MIRCtxRefines b₁ b₂) : MIRCtxRefines (wrapLet bs b₁) (wrapLet bs b₂) := by
  cases bs with
  | nil => exact h
  | cons _ _ => exact mirCtxRefines_let_body h

/-- **Let-hoist** of a whole `wrapLet` binding list out of a MIR frame. -/
theorem mirCtxRefines_hoist_wrapLet (F : MFrame) (hA : F.Atomic) :
    ∀ (bs : List (VarId × Expr × Bool)) (body : Expr), (∀ b ∈ bs, F.Fresh b.1) →
      MIRCtxRefines (F.fill (wrapLet bs body)) (wrapLet bs (F.fill body))
  | [], _, _ => mirCtxRefines_refl _
  | (v, rhs, er) :: bs, body, hfresh =>
    mirCtxRefines_trans (mirCtxRefines_of_lowerEq fun env => by
        rw [F.lowerTotalExpr_fill, F.lowerTotalExpr_fill,
          show (v, rhs, er) :: bs = [(v, rhs, er)] ++ bs from rfl, lowerTotalExpr_wrapLet_append]
        rfl) <|
    mirCtxRefines_trans (mirCtxRefines_hoist F hA (hfresh _ (.head _)) rhs (wrapLet bs body) er) <|
    mirCtxRefines_trans (mirCtxRefines_let_body
      (mirCtxRefines_hoist_wrapLet F hA bs body fun b hb => hfresh b (.tail _ hb))) <|
    mirCtxRefines_of_lowerEq fun env =>
      (lowerTotalExpr_wrapLet_append [(v, rhs, er)] bs (F.fill body) env).symm

end Moist.Verified.MIR
