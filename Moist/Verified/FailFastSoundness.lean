import Moist.Verified.FailFastSoundness.Termination
import Moist.Verified.MIR.Hoist
import Moist.Verified.HygieneSoundness
import Moist.Verified.PreLowerSoundness
import Moist.MIR.Optimize.Advanced.Products

/-! # Soundness of fail-fast reordering

`failFast_refines`: for every MIR expression `e`, `e ⊑Ctxᴹ failFast e`.

`sinkInto_lowering` certifies the rewrite of one binding at the level of
lowerings: whenever `let x = rhs in body` lowers, `sinkInto x rhs er body`
lowers to a term that refines it in the same environment. The walk is then
certified with the `FactRel` congruences, post-composing the rewrite at every
binding it moves.
-/

namespace Moist.Verified.FailFast

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts

/-- `sinkInto x rhs er body` refines `let x = rhs in body` once lowered. -/
def SinkOK (x : VarId) (rhs : Expr) (er : Bool) (body : Expr) : Prop :=
  ∀ env tr tb, lowerTotalExpr env rhs = some tr → lowerTotalExpr (x :: env) body = some tb →
    ∃ t', lowerTotalExpr env (sinkInto x rhs er body) = some t' ∧
      ∀ F, FactRefines env.length F (.Apply (.Lam 0 tb) tr) t'

theorem lowerTotalExpr_consLet' (env : List VarId) (binding : VarId × Expr × Bool) (e : Expr) :
    lowerTotalExpr env (consLet binding e) = lowerTotalExpr env (.Let [binding] e) := by
  unfold consLet
  split
  · exact lowerTotalExpr_let_cons env _ _ _
  · rfl

theorem isErrorExpr_eq {a : Expr} (h : isErrorExpr a = true) : a = .Error := by
  cases a <;> simp_all [isErrorExpr]

theorem closedAtList_map_let {d : Nat} {tr : Term} (htr : closedAt d tr = true) :
    ∀ {ts : List Term}, closedAtList (d + 1) ts = true →
      closedAtList d (ts.map fun a => .Apply (.Lam 0 a) tr) = true
  | [], _ => by simp [closedAtList]
  | t :: ts, h => by
    simp only [closedAtList, Bool.and_eq_true] at h
    simp only [List.map_cons, closedAtList, closedAt, h.1, htr, Bool.and_self, Bool.true_and]
    exact closedAtList_map_let htr h.2

/-- The alternatives of a moved binding, one by one. -/
theorem sink_alternatives {x : VarId} {rhs : Expr} {er : Bool} {env : List VarId} {tr : Term}
    (htr : lowerTotalExpr env rhs = some tr) :
    ∀ (alts : List Expr), (∀ a ∈ alts, SinkOK x rhs er a) →
      ∀ talts, MIR.lowerTotalExprList (x :: env) alts = some talts →
      ∃ talts', MIR.lowerTotalExprList env
          (alts.map fun a => if isErrorExpr a then .Error else sinkInto x rhs er a) = some talts' ∧
        ∀ F, ListRel (FactRefines env.length F) (talts.map fun a => .Apply (.Lam 0 a) tr) talts'
  | [], _, talts, h => by
    rw [MIR.lowerTotalExprList_nil] at h; cases h
    exact ⟨[], MIR.lowerTotalExprList_nil env, fun _ => trivial⟩
  | a :: alts, hok, talts, h => by
    rw [MIR.lowerTotalExprList_cons] at h
    cases ha : lowerTotalExpr (x :: env) a with
    | none => rw [ha] at h; cases h
    | some ta =>
      cases has : MIR.lowerTotalExprList (x :: env) alts with
      | none => rw [ha, has] at h; cases h
      | some tas =>
        rw [ha, has] at h; cases h
        obtain ⟨tas', htas', hrel⟩ := sink_alternatives htr alts (fun b hb => hok b (.tail _ hb)) tas has
        by_cases herr : isErrorExpr a = true
        · have := isErrorExpr_eq herr
          subst this
          rw [lowerTotalExpr_error] at ha; cases ha
          refine ⟨.Error :: tas', ?_, fun F => ⟨factRefines_letError, hrel F⟩⟩
          rw [List.map_cons, if_pos herr, MIR.lowerTotalExprList_cons, lowerTotalExpr_error, htas']
          rfl
        · obtain ⟨t', ht', hr⟩ := hok a (.head _) env tr ta htr ha
          refine ⟨t' :: tas', ?_, fun F => ⟨hr F, hrel F⟩⟩
          rw [List.map_cons, if_neg herr, MIR.lowerTotalExprList_cons, ht', htas']
          rfl

theorem sinkCheck_spec {x : VarId} {rhs c : Expr} {alts : List Expr}
    (h : sinkCheck x rhs c alts = true) :
    (freeVars c).contains x = false ∧ terminates c = true := by
  simp only [sinkCheck, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.1.1.1.1.1

theorem sinkInto_ok : ∀ (N : Nat) (body : Expr), sizeOf body < N →
    ∀ x rhs er, SinkOK x rhs er body := by
  intro N
  induction N with
  | zero => intro _ h; omega
  | succ N ih =>
  intro body hsize x rhs er env tr tb htr htb
  have hrefl : lowerTotalExpr env (.Let [(x, rhs, er)] body) = some (.Apply (.Lam 0 tb) tr) := by
    rw [lowerTotalExpr_let_single, htr, htb]; rfl
  cases body with
  | Case c alts =>
    rw [sinkInto]
    split
    · rename_i hcheck
      obtain ⟨hx, hterm⟩ := sinkCheck_spec hcheck
      obtain ⟨tc', talts, htc', htalts, rfl⟩ := lowerTotalExpr_case_some htb
      rw [MIR.lowerTotalExpr_prepend_unused env x c hx] at htc'
      cases htc : lowerTotalExpr env c with
      | none => rw [htc] at htc'; cases htc'
      | some tc =>
        rw [htc] at htc'; cases htc'
        have hok : ∀ a ∈ alts, SinkOK x rhs er a := fun a ha =>
          ih a (by have := List.sizeOf_lt_of_mem ha; simp only [Expr.Case.sizeOf_spec] at hsize; omega)
            x rhs er
        obtain ⟨talts', htalts', hrel⟩ := sink_alternatives htr alts hok talts htalts
        refine ⟨.Case tc talts', ?_, fun F => ?_⟩
        · have hmap := productList_attach_map alts
            (fun a => if isErrorExpr a = true then Expr.Error else sinkInto x rhs er a)
          simp only [hmap, MIR.lowerTotalExpr_case_of_list, htc, htalts']; rfl
        · have closedR := MIR.lowerTotalExpr_closedAt htr
          have closedC := MIR.lowerTotalExpr_closedAt htc
          have closedA : closedAtList (env.length + 1) talts = true := by
            simpa using lowerTotalExprList_closedAtList htalts
          exact (factRefines_sinkCase closedR closedC closedA (terminates_sound hterm htc)).trans
            (factRefines_case (FactRefines.refl _ _ _) (hrel F) closedC
              (closedAtList_map_let closedR closedA))
    · exact ⟨_, hrefl, fun _ => FactRefines.refl _ _ _⟩
  | _ =>
    rw [sinkInto]
    all_goals first
      | exact ⟨_, hrefl, fun _ => FactRefines.refl _ _ _⟩
      | (intro _ _ h; cases h)

/-! ## The walk -/

theorem FactRel.post {G : VarId → Prop} {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} {e e₁ e₂ : Expr} (h : FactRel G P Γ e e₁)
    (h₂ : ∀ env t₁, lowerTotalExpr env e₁ = some t₁ → ∃ t₂, lowerTotalExpr env e₂ = some t₂ ∧
      ∀ F, FactRefines env.length F t₁ t₂) : FactRel G P Γ e e₂ := by
  intro env t hG hd hf hk hs ht
  obtain ⟨t₁, ht₁, hr⟩ := h env t hG hd hf hk hs ht
  obtain ⟨t₂, ht₂, hr₂⟩ := h₂ env t₁ ht₁
  exact ⟨t₂, ht₂, hr.trans (hr₂ _)⟩

abbrev AnyName : VarId → Prop := fun _ => True

theorem listRel_factRel_of {Γ : List (VarId × Expr)} :
    ∀ {es : List Expr}, (∀ e ∈ es, FactRel AnyName Produces Γ e (failFastWalk e)) →
      ListRel (FactRel AnyName Produces Γ) es (es.map failFastWalk)
  | [], _ => trivial
  | e :: _, h => ⟨h e (.head _), listRel_factRel_of fun e' he' => h e' (.tail _ he')⟩

theorem failFastWalk_factRel : ∀ (N : Nat) (e : Expr), exprSize e < N →
    ∀ Γ, FactRel AnyName Produces Γ e (failFastWalk e) := by
  intro N
  induction N with
  | zero => intro _ h; omega
  | succ N ih =>
  intro e hsize Γ
  match e with
  | .Let [] body =>
    rw [failFastWalk]
    simp only [exprSize, exprSizeBinds] at hsize
    exact (ih body (by omega) Γ).congr_left (fun env => lowerTotalExpr_let_nil env body)
      (fun avoid => freshIn_let_nil avoid body)
  | .Let ((x, r, er) :: rest) body =>
    rw [failFastWalk]
    simp only [exprSize, exprSizeBinds] at hsize
    have ihr := ih r (by omega)
    have ihb := ih (.Let rest body) (by have := exprSize_pos r; simp only [exprSize]; omega)
    have hlet : FactRel AnyName Produces Γ (.Let ((x, r, er) :: rest) body)
        (.Let [(x, failFastWalk r, er)] (failFastWalk (.Let rest body))) :=
      (FactRel.let_single (er := er) r trivial (.inl rfl) (ihr Γ) (ihb ((x, r) :: Γ))
        (fun _ _ _ _ _ _ hp => hp)).congr_left
        (fun env => lowerTotalExpr_let_cons env _ _ _) (fun avoid => freshIn_let_cons avoid _ _ _)
    split
    · refine FactRel.post hlet fun env t₁ ht₁ => ?_
      obtain ⟨tr, tb, htr, htb, rfl⟩ := lowerTotalExpr_let_single_some ht₁
      exact sinkInto_ok _ _ (Nat.lt_succ_self _) x _ er env tr tb htr htb
    · exact hlet.congr_right fun env => lowerTotalExpr_consLet' env _ _
  | .Lam x b =>
    rw [failFastWalk]
    simp only [exprSize] at hsize
    exact (ih b (by omega) Γ).lam trivial
  | .Fix f b =>
    rw [failFastWalk]
    simp only [exprSize] at hsize
    cases hb : b with
    | Lam x inner =>
      subst hb
      rw [failFastWalk]
      simp only [exprSize] at hsize
      exact (ih inner (by omega) Γ).fix_lam trivial trivial (fun _ _ => trivial)
    | _ =>
      intro env t _ _ _ _ _ hlow
      rw [MIR.lowerTotalExpr_fix_nonlam_none env f _ (by intros; simp)] at hlow
      cases hlow
  | .App f a =>
    rw [failFastWalk]
    simp only [exprSize] at hsize
    exact (ih f (by omega) Γ).app (ih a (by omega) Γ)
  | .Force b =>
    rw [failFastWalk]
    simp only [exprSize] at hsize
    exact (ih b (by omega) Γ).force
  | .Delay b =>
    rw [failFastWalk]
    simp only [exprSize] at hsize
    exact (ih b (by omega) Γ).delay
  | .Constr tag fields =>
    rw [failFastWalk, productList_attach_map]
    simp only [exprSize] at hsize
    exact FactRel.constr (listRel_factRel_of fun e he =>
      ih e (by have := exprSize_lt_of_mem he; omega) Γ)
  | .Case s alts =>
    rw [failFastWalk, productList_attach_map]
    simp only [exprSize] at hsize
    exact FactRel.case (ih s (by omega) Γ) (listRel_factRel_of fun e he =>
      ih e (by have := exprSize_lt_of_mem he; omega) Γ)
  | .Var _ | .Lit _ | .Builtin _ | .Error =>
    rw [failFastWalk]; exact FactRel.refl _ _ _ _

end Moist.Verified.FailFast

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced Moist.Verified.ShapeFacts Moist.Verified.FailFast

/-- Fail-fast reordering refines its input. -/
theorem failFast_refines (e : Expr) : MIRCtxRefines e (Advanced.failFast e) := by
  unfold Advanced.failFast
  simp only
  refine mirCtxRefines_trans (Hygiene.uniqueOptimizationBinders_refines e) ?_
  split
  · rename_i hws
    exact mirCtxRefines_of_factRel hws (fun _ _ => trivial) (fun _ _ => trivial)
      (failFastWalk_factRel _ _ (Nat.lt_succ_self _) [])
  · exact mirCtxRefines_refl _

end Moist.Verified.MIR
