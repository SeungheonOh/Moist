import Moist.Verified.MIR
import Moist.Verified.MIR.Congruence
import Moist.Verified.MIR.Primitives.Iterated
import Moist.Verified.DCESoundness
import Moist.Verified.DeadLet
import Moist.MIR.Canonicalize
import Moist.MIR.Optimize.Inline
import Moist.Verified.InlineSoundness.SubstCommute
import Moist.Verified.InlineSoundness.WellScoped
import Moist.Verified.InlineSoundness.Preservation
import Moist.Verified.InlineSoundness.FrontierError

variable [sv : Moist.CEK.SemVariant]

/-! # Soundness of the MIR inlining pass

`inline_refines : MIRCtxRefines e (inlinePassWithCanon e s).1.1` for every
MIR expression `e` and fresh-name state `s`.

Every inlining step is a UPLC beta reduction: lowering the substituted let
gives the contractum of lowering the original let (`SubstCommute`), so each
branch of `shouldInline` is an instance of the frontier beta rule
(`Frontier.beta_ctxRefines_of_errorFrontier`). Pure right-hand sides are
total, recursive lambdas halt, and impure ones sit on the evaluation frontier.

The recursive worker needs three invariants: the input is well scoped (so
every let has distinct binders that are not free in it), every uid is below
the fresh-name counter (which `inlinePassWithCanon` reserves), and later let
binders are not free in earlier right-hand sides (`Preservation.NamesFresh`). -/

namespace Moist.Verified.MIR

open Moist.CEK
open Moist.Plutus.Term (Term)
open Moist.MIR
  (Expr VarId VarSet FreshState inlinePass inlinePassList inlineBindings
   inlineLetBindings inlineLetGo betaReduce substInBindings
   shouldInline lowerTotalExpr lowerTotal freeVars freeVarsLet subst
   canonicalize wellScoped maxUidExpr maxUidExprBinds distinctBinders)
open Moist.Verified.InlineSoundness.WellScoped
open Moist.Verified.InlineSoundness.Preservation
open Moist.Verified.InlineSoundness.Rename (maxUid_let_cons maxUid_list_cons)
open Moist.Verified.Contextual (CtxRefines ctxRefines_refl)
open Moist.Verified.Equivalence (ListRel)

omit sv in
theorem InlineGate_impure_frontier (binder : VarId) (rhs body : Expr)
    (rest : List (VarId × Expr × Bool))
    (notAtomic : rhs.isAtom = false) (notValue : rhs.isValue = false)
    (notPure : Moist.MIR.isPure rhs = false)
    (accepted : InlineGate binder rhs body rest = true) :
    Moist.MIR.firstEvaluationUse binder (.Let rest body) = true := by
  cases frontier : Moist.MIR.firstEvaluationUse binder (.Let rest body) with
  | true => rfl
  | false => simp [InlineGate, shouldInline, notAtomic, notValue, notPure, frontier] at accepted

/-- Inlining the head binding of a let, as `inlineLetGo` does, is sound
    whenever `shouldInline` accepted it. -/
theorem substInBindings_body_inline_mirCtxRefines (v : VarId) (rhs body : Expr)
    (er : Bool) (rest : List (VarId × Expr × Bool)) (s : FreshState)
    (hgate : InlineGate v rhs body rest = true)
    (distinct : distinctBinders ((v, rhs, er) :: rest) = true)
    (names : ∀ b ∈ rest, (freeVars rhs).contains b.1 = false)
    (fresh : maxUidExpr (.Let ((v, rhs, er) :: rest) body) < s.next) :
    MIRCtxRefines
      (.Let ((v, rhs, er) :: rest) body)
      (.Let (substInBindings v rhs rest (subst v rhs body s).2).1.val (subst v rhs body s).1) := by
  intro env
  cases hlhs : lowerTotalExpr env (.Let ((v, rhs, er) :: rest) body) with
  | none => exact ⟨by simp, trivial⟩
  | some t =>
    obtain ⟨t_rhs, t_rest, ht_rhs, ht_rest, rfl, hlower⟩ :=
      Moist.Verified.InlineSoundness.SubstCommute.inline_head_lower distinct names fresh hlhs
    refine ⟨fun _ => by rw [hlower]; rfl, ?_⟩
    rw [hlower]
    have hclosed_rhs : closedAt env.length t_rhs = true := lowerTotal_closedAt env _ t_rhs ht_rhs
    have hclosed_rest : closedAt (env.length + 1) t_rest = true := by
      simpa using lowerTotal_closedAt (v :: env) _ t_rest ht_rest
    have ht_rhs' : lowerTotal env (Moist.MIR.expandFix rhs) = some t_rhs := ht_rhs
    -- Pure (including atomic) right-hand sides are total; non-pure values are
    -- recursive lambdas; anything else passed the evaluation-frontier gate.
    by_cases hpure : Moist.MIR.isPure rhs = true
    · exact Moist.Verified.InlineSoundness.Frontier.beta_total_ctxRefines
        (Moist.Verified.InlineSoundness.Totality.lowerTotal_total _ env t_rhs
          (Moist.Verified.Purity.isPure_expandFix rhs hpure) ht_rhs')
        hclosed_rest hclosed_rhs
    have hatom : rhs.isAtom = false := by
      cases rhs <;> simp_all [Moist.MIR.Expr.isAtom, Moist.MIR.isPure]
    by_cases hval : rhs.isValue = true
    · have h_canon : ∃ body_l, t_rhs = Moist.MIR.fixLamWrapUplc body_l := by
        cases rhs with
        | Fix f_id fix_body =>
          cases fix_body with
          | Lam x_id inner =>
            have := Moist.MIR.lowerTotalExpr_fix_lam_canonical env f_id x_id inner
            rw [ht_rhs] at this
            revert this
            cases lowerTotal _ (Moist.MIR.expandFix inner) with
            | none => simp
            | some bl => simp; intro h; exact ⟨bl, h⟩
          | _ => exfalso; revert ht_rhs'; simp [Moist.MIR.expandFix, lowerTotal]
        | _ => simp_all [Moist.MIR.Expr.isValue, Moist.MIR.isPure]
      obtain ⟨body_l, rfl⟩ := h_canon
      exact Moist.Verified.InlineSoundness.Frontier.beta_ctxRefines_of_halts
        hclosed_rest hclosed_rhs fun ρ _ _ =>
          Moist.Verified.InlineSoundness.SubstCommute.fixLamWrapUplc_halts body_l ρ
    unfold InlineGate shouldInline at hgate
    simp only [hatom, hval, hpure, Bool.false_eq_true, Bool.or_false, ↓reduceIte,
      Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.or_eq_false_iff] at hgate
    exact Moist.Verified.InlineSoundness.Frontier.beta_evaluationPath_refines
      (Moist.Verified.InlineSoundness.Frontier.inlineGate_evaluationPath
        v env rest body t_rest (by simpa [lowerTotalExpr, Moist.MIR.expandFix, lowerTotal] using ht_rest)
        (by simpa using hgate.2.2))
      hclosed_rest hclosed_rhs

/-- `.App (.Lam p body) x` and `.Let [(p, x, false)] body` lower identically. -/
theorem mirCtxRefines_app_lam_to_let (p : VarId) (body x : Expr) :
    MIRCtxRefines (.App (.Lam p body) x) (.Let [(p, x, false)] body) := by
  intro env
  have heq : lowerTotalExpr env (.App (.Lam p body) x) =
             lowerTotalExpr env (.Let [(p, x, false)] body) := by
    simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.expandFixBinds,
      Moist.MIR.lowerTotal, Moist.MIR.lowerTotalLet]
    cases lowerTotal (p :: env) (Moist.MIR.expandFix body) <;>
      cases lowerTotal env (Moist.MIR.expandFix x) <;> simp
  rw [heq]
  refine ⟨id, ?_⟩
  cases lowerTotalExpr env (.Let [(p, x, false)] body) with
  | none => trivial
  | some t => exact ctxRefines_refl t

/-- Beta reduction with an atomic argument is a let inlining of an atom. -/
theorem betaReduce_soundness (f x : Expr) (s : FreshState)
    (freshF : maxUidExpr f < s.next) (freshX : maxUidExpr x < s.next) :
    MIRCtxRefines (.App f x) (betaReduce f x s).1.1 := by
  cases f with
  | Lam param body =>
    rw [betaReduce_lam]
    split
    · rename_i hatom
      have step := substInBindings_body_inline_mirCtxRefines param x body false [] s
        (by simp [InlineGate, shouldInline, hatom]) (by simp [distinctBinders])
        (fun _ h => nomatch h)
        (by simp only [maxUidExpr] at freshF; simp only [maxUid_let_cons, maxUidExpr, maxUidExprBinds]; omega)
      rw [show (substInBindings param x [] (subst param x body s).2).1.val = [] from rfl] at step
      exact mirCtxRefines_trans (mirCtxRefines_app_lam_to_let param body x)
        (mirCtxRefines_trans step mirCtxRefines_let_nil)
    · exact mirCtxRefines_refl _
  | _ => rw [betaReduce_other _ _ _ (by intros; simp)]; exact mirCtxRefines_refl _

/-! ## The let-inlining loop -/

omit sv in
private theorem lowerTotalExpr_let_split (env : List VarId)
    (binds₁ binds₂ : List (VarId × Expr × Bool)) (body : Expr) :
    lowerTotalExpr env (.Let (binds₁ ++ binds₂) body) =
    lowerTotalExpr env (.Let binds₁ (.Let binds₂ body)) := by
  induction binds₁ generalizing env with
  | nil => simp [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.expandFixBinds,
      Moist.MIR.lowerTotal, Moist.MIR.lowerTotalLet]
  | cons b rest ih =>
    obtain ⟨y, rhs, er⟩ := b
    rw [List.cons_append, Moist.Verified.InlineSoundness.Rename.lowerTotalExpr_let_cons,
      Moist.Verified.InlineSoundness.Rename.lowerTotalExpr_let_cons, ih]

omit sv in
private theorem distinctBinders_of_map_fst_eq
    {binds binds' : List (VarId × Expr × Bool)}
    (heq : binds'.map (·.1) = binds.map (·.1))
    (hd : distinctBinders binds = true) : distinctBinders binds' = true := by
  induction binds generalizing binds' with
  | nil => cases binds' with | nil => rfl | cons _ _ => simp at heq
  | cons b rest ih =>
    cases binds' with
    | nil => simp at heq
    | cons b' rest' =>
      simp only [List.map, List.cons.injEq] at heq
      simp only [distinctBinders, Bool.and_eq_true, List.all_eq_true] at hd ⊢
      refine ⟨fun c hc => ?_, ih heq.2 hd.2⟩
      obtain ⟨c', hc', hname⟩ := List.mem_map.mp (heq.2 ▸ List.mem_map.mpr ⟨c, hc, rfl⟩)
      rw [heq.1, ← hname]; exact hd.1 c' hc'

omit sv in
private theorem substInBindings_map_fst (v : VarId) (repl : Expr) :
    ∀ (binds : List (VarId × Expr × Bool)) (s : FreshState),
      (substInBindings v repl binds s).1.val.map (·.1) = binds.map (·.1)
  | [], _ => rfl
  | (w, e, er) :: rest, s => by
    rw [Moist.Verified.InlineSoundness.SubstCommute.substInBindings_cons_val]
    simp only [List.map, substInBindings_map_fst v repl rest]

omit sv in
private theorem inlineBindings_map_fst :
    ∀ (binds : List (VarId × Expr × Bool)) (s : FreshState),
      (inlineBindings binds s).1.1.map (·.1) = binds.map (·.1)
  | [], s => by rw [inlineBindings_nil]
  | (w, e, er) :: rest, s => by
    rw [(inlineBindings_cons s w e er rest).1]
    simp only [List.map, inlineBindings_map_fst rest]

private theorem inlineLetGo_soundness :
    ∀ (binds acc : List (VarId × Expr × Bool)) (body : Expr) (changed : Bool) (s : FreshState),
      distinctBinders binds = true → NamesFresh binds →
      maxUidExpr (.Let binds body) < s.next →
      MIRCtxRefines (.Let (acc.reverse ++ binds) body) (inlineLetGo binds acc body changed s).1.1
  | [], acc, body, changed, s, _, _, _ => by
    rw [inlineLetGo_nil, List.append_nil]
    cases acc.reverse with
    | nil => exact mirCtxRefines_let_nil
    | cons _ _ => exact mirCtxRefines_refl _
  | (v, rhs, er) :: rest, acc, body, changed, s, hdist, ⟨names, namesRest⟩, fresh => by
    rw [inlineLetGo_cons]
    have hdistRest : distinctBinders rest = true := by
      simp only [distinctBinders, Bool.and_eq_true] at hdist; exact hdist.2
    split
    · rename_i hgate
      have := (substInBindings v rhs rest (subst v rhs body s).2).1.property
      have freshUid := maxUid_let_cons v rhs er rest body ▸ fresh
      simp only [maxUidExpr] at freshUid
      have fs₁ := Moist.Verified.InlineSoundness.SubstCommute.subst_fresh v rhs body s (by omega) (by omega)
      have fs₂ := Moist.Verified.InlineSoundness.SubstCommute.substInBindings_fresh v rhs rest
        (subst v rhs body s).2 (by omega) (by omega)
      have ih := inlineLetGo_soundness (substInBindings v rhs rest (subst v rhs body s).2).1.val
        acc (subst v rhs body s).1 true (substInBindings v rhs rest (subst v rhs body s).2).2
        (distinctBinders_of_map_fst_eq (substInBindings_map_fst v rhs rest _) hdistRest)
        (namesFresh_substInBindings v rhs rest _ names namesRest)
        (by simp only [maxUidExpr]; omega)
      have step := substInBindings_body_inline_mirCtxRefines v rhs body er rest s hgate hdist names fresh
      exact mirCtxRefines_trans
        (mirCtxRefines_of_lowerEq (lowerTotalExpr_let_split · acc.reverse _ body))
        (mirCtxRefines_trans (mirCtxRefines_let_body (binds := acc.reverse) step)
          (mirCtxRefines_trans
            (mirCtxRefines_of_lowerEq fun env => (lowerTotalExpr_let_split env acc.reverse _ _).symm)
            ih))
    · have ih := inlineLetGo_soundness rest ((v, rhs, er) :: acc) body changed s hdistRest namesRest
        (by have := maxUid_let_cons v rhs er rest body; omega)
      rwa [List.reverse_cons, List.append_assoc, List.singleton_append] at ih
  termination_by binds => binds.length
  decreasing_by all_goals simp_wf; all_goals omega

theorem inlineLetBindings_soundness (binds : List (VarId × Expr × Bool)) (body : Expr)
    (s : FreshState) (hdist : distinctBinders binds = true) (names : NamesFresh binds)
    (fresh : maxUidExpr (.Let binds body) < s.next) :
    MIRCtxRefines (.Let binds body) (inlineLetBindings binds body s).1.1 := by
  simpa using inlineLetGo_soundness binds [] body false s hdist names fresh

/-! ## The pass -/

mutual
  theorem inline_soundness_aux : (e : Expr) → (s : FreshState) →
      wellScoped e = true → maxUidExpr e < s.next →
      MIRCtxRefines e (inlinePass e s).1.1
    | .Var _, s, _, _ | .Lit _, s, _, _ | .Builtin _, s, _, _ | .Error, s, _, _ => by
      rw [inlinePass_leaf s _ trivial]; exact mirCtxRefines_refl _
    | .Lam x body, s, hws, fresh => by
      simp only [maxUidExpr] at fresh
      rw [(inlinePass_lam s x body).1]
      exact mirCtxRefines_lam (inline_soundness_aux body s (wellScoped_sub_lam hws) (by omega))
    | .Fix f body, s, hws, fresh => by
      simp only [maxUidExpr] at fresh
      rw [(inlinePass_fix s f body).1]
      cases body with
      | Lam x inner =>
        simp only [maxUidExpr] at fresh
        rw [(inlinePass_lam s x inner).1]
        exact mirCtxRefines_fix_lam
          (inline_soundness_aux inner s (wellScoped_sub_lam (wellScoped_sub_fix hws)) (by omega))
      | _ => exact mirCtxRefines_fix_nonlam_lhs (by intros; simp)
    | .App f x, s, hws, fresh => by
      simp only [maxUidExpr] at fresh
      rw [(inlinePass_app s f x).1]
      have ⟨hws_f, hws_x⟩ := wellScoped_sub_app hws
      have ff := inlinePass_fresh f s (by omega)
      have fx := inlinePass_fresh x (inlinePass f s).2 (by omega)
      exact mirCtxRefines_trans
        (mirCtxRefines_app (inline_soundness_aux f s hws_f (by omega))
          (inline_soundness_aux x _ hws_x (by omega)))
        (betaReduce_soundness _ _ _ (by omega) fx.1)
    | .Force e, s, hws, fresh => by
      simp only [maxUidExpr] at fresh
      rw [(inlinePass_force s e).1]
      exact mirCtxRefines_force (inline_soundness_aux e s (wellScoped_sub_force hws) fresh)
    | .Delay e, s, hws, fresh => by
      simp only [maxUidExpr] at fresh
      rw [(inlinePass_delay s e).1]
      exact mirCtxRefines_delay (inline_soundness_aux e s (wellScoped_sub_delay hws) fresh)
    | .Constr tag args, s, hws, fresh => by
      simp only [maxUidExpr] at fresh
      rw [(inlinePass_constr s tag args).1]
      have hws_args := wellScoped_sub_constr hws
      cases args with
      | nil => rw [inlinePassList_nil]; exact mirCtxRefines_refl _
      | cons e rest =>
        rw [maxUid_list_cons] at fresh
        rw [(inlinePassList_cons s e rest).1]
        have := inlinePass_fresh e s (by omega)
        exact mirCtxRefines_constr
          (inline_soundness_aux e s (hws_args e (.head _)) (by omega))
          (inlinePassList_listRel rest _ (fun e' he' => hws_args e' (.tail _ he')) (by omega))
    | .Case scrut alts, s, hws, fresh => by
      simp only [maxUidExpr] at fresh
      rw [(inlinePass_case s scrut alts).1]
      have ⟨hws_scrut, hws_alts⟩ := wellScoped_sub_case hws
      have := inlinePass_fresh scrut s (by omega)
      exact mirCtxRefines_case (inline_soundness_aux scrut s hws_scrut (by omega))
        (inlinePassList_listRel alts _ hws_alts (by omega))
    | .Let binds body, s, hws, fresh => by
      simp only [maxUidExpr] at fresh
      rw [(inlinePass_let s binds body).1]
      have ⟨hws_body, hws_binds⟩ := wellScoped_sub_let hws
      have fb := inlineBindings_fresh binds s (by omega)
      have fbody := inlinePass_fresh body (inlineBindings binds s).2 (by omega)
      have h_binds := inlineBindings_listRel binds s hws_binds (by omega)
      have h_body := inline_soundness_aux body (inlineBindings binds s).2 hws_body (by omega)
      have names := namesFresh_inlineBindings binds s
        (namesFresh_of_distinct binds body (wellScoped_distinctBinders hws) (wellScoped_let_names hws))
      exact mirCtxRefines_trans
        (mirCtxRefines_let_binds_congr binds (inlineBindings binds s).1.1 body h_binds)
        (mirCtxRefines_trans (mirCtxRefines_let_body h_body)
          (inlineLetBindings_soundness _ _ _
            (distinctBinders_of_map_fst_eq (inlineBindings_map_fst binds s)
              (wellScoped_distinctBinders hws))
            names (by simp only [maxUidExpr]; omega)))

  theorem inlinePassList_listRel : (es : List Expr) → (s : FreshState) →
      (∀ e ∈ es, wellScoped e = true) → Moist.MIR.maxUidExprList es < s.next →
      ListRel MIRCtxRefines es (inlinePassList es s).1.1
    | [], s, _, _ => by rw [inlinePassList_nil]; exact True.intro
    | e :: rest, s, hws, fresh => by
      rw [maxUid_list_cons] at fresh
      rw [(inlinePassList_cons s e rest).1]
      have := inlinePass_fresh e s (by omega)
      exact ⟨inline_soundness_aux e s (hws e (.head _)) (by omega),
        inlinePassList_listRel rest _ (fun e' he' => hws e' (.tail _ he')) (by omega)⟩

  theorem inlineBindings_listRel : (binds : List (VarId × Expr × Bool)) → (s : FreshState) →
      (∀ b ∈ binds, wellScoped b.2.1 = true) → maxUidExprBinds binds < s.next →
      ListRel (fun b₁ b₂ => b₁.1 = b₂.1 ∧ b₁.2.2 = b₂.2.2 ∧ MIRCtxRefines b₁.2.1 b₂.2.1)
        binds (inlineBindings binds s).1.1
    | [], s, _, _ => by rw [inlineBindings_nil]; exact True.intro
    | (v, rhs, er) :: rest, s, hws, fresh => by
      simp only [maxUidExprBinds] at fresh
      rw [(inlineBindings_cons s v rhs er rest).1]
      have := inlinePass_fresh rhs s (by omega)
      exact ⟨⟨rfl, rfl, inline_soundness_aux rhs s (hws _ (.head _)) (by omega)⟩,
        inlineBindings_listRel rest _ (fun b hb => hws b (.tail _ hb)) (by omega)⟩
end

theorem inline_refines (e : Expr) (s : FreshState) :
    MIRCtxRefines e (Moist.MIR.inlinePassWithCanon e s).1.1 := by
  by_cases hscoped : wellScoped e = true
  · simpa [Moist.MIR.inlinePassWithCanon, hscoped, Moist.MIR.reserveFreshFor,
      bind, pure, StateT.bind, StateT.pure, modify, modifyGet, StateT.modifyGet] using
      inline_soundness_aux e { next := max s.next (maxUidExpr e + 1) } hscoped
        (by show maxUidExpr e < max s.next (maxUidExpr e + 1); omega)
  · let reserved : FreshState :=
      { next := max s.next (maxUidExpr (canonicalize e) + 1) }
    have result := mirCtxRefines_trans
      (mirCtxRefines_of_lowerEq (fun env => (Moist.MIR.lowerTotalExpr_canonicalize env e).symm))
      (inline_soundness_aux (canonicalize e) reserved (wellScoped_canonicalize e)
        (by show maxUidExpr (canonicalize e) < max s.next (maxUidExpr (canonicalize e) + 1); omega))
    simpa [Moist.MIR.inlinePassWithCanon, hscoped, Moist.MIR.reserveFreshFor,
      bind, pure, StateT.bind, StateT.pure, modify, modifyGet, StateT.modifyGet] using result

end Moist.Verified.MIR
