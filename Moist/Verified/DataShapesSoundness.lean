import Moist.MIR.Optimize.Advanced.DataShapes
import Moist.Verified.ShapesSoundness.Simplify
import Moist.Verified.AdvancedTraversal

variable [sv : Moist.CEK.SemVariant]

/-! # Kind guards and key bytes

`specializeDataChecks` replaces a kind guard

```
force (ifThenElse (chooseData x c₀ … c₄) (delay x) (delay error))
```

whose single `True` branch selects one `Data` kind by `let _ = unK x in x`, where
`unK` is the unData builtin of that kind: both fail unless `x` is a `Data`
value of that kind and otherwise return `x` (`specializeDataChecks_refines`).

`insertKeyBytes` binds, right after `k = unBData d`, the bytes `#00 ++ k` and
their `B` value. Both bindings return on every path, since `k` holds bytes, and
the scope does not mention them (`insertKeyBytes_refines`).
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines Moist.Verified.MIR

/-! ## Evaluation of a kind guard -/

theorem errs_apply_fun {ρ : CekEnv} {tf ta : Term} (hf : Errs ρ tf) : Errs ρ (.Apply tf ta) :=
  reaches_trans (reaches_of_steps 1 rfl) (errs_on_stack hf _)

theorem errs_force {ρ : CekEnv} {t : Term} (h : Errs ρ t) : Errs ρ (.Force t) :=
  reaches_trans (reaches_of_steps 1 rfl) (errs_on_stack h _)

def kindOf : Moist.Plutus.Data → Nat
  | .Constr _ _ => 0
  | .Map _ => 1
  | .List _ => 2
  | .I _ => 3
  | .B _ => 4

def selectKind (bs : List Bool) (d : Moist.Plutus.Data) : Bool := bs.getD (kindOf d) false

theorem chooseData_bools (b₀ b₁ b₂ b₃ b₄ : Bool) (d : Moist.Plutus.Data) :
    evalBuiltin .ChooseData [.VCon (.Bool b₄), .VCon (.Bool b₃), .VCon (.Bool b₂),
      .VCon (.Bool b₁), .VCon (.Bool b₀), .VCon (.Data d)] =
      some (.VCon (.Bool (selectKind [b₀, b₁, b₂, b₃, b₄] d))) := by
  cases d <;> rfl

theorem chooseData_bools_none (b₀ b₁ b₂ b₃ b₄ : Bool) {vx : CekValue}
    (h : ∀ d, vx ≠ .VCon (.Data d)) :
    evalBuiltin .ChooseData [.VCon (.Bool b₄), .VCon (.Bool b₃), .VCon (.Bool b₂),
      .VCon (.Bool b₁), .VCon (.Bool b₀), vx] = none := by
  cases vx with
  | VCon c =>
    cases c
    all_goals first | (exact absurd rfl (h _)) | rfl
  | _ => rfl

/-- The unData builtin of the selected kind succeeds exactly on that kind. -/
theorem kindChecker_spec {b₀ b₁ b₂ b₃ b₄ : Bool} {checker : BuiltinFun}
    (h : kindChecker [b₀, b₁, b₂, b₃, b₄] = some checker) :
    expectedArgs checker = .one .argV ∧
      (∀ d, selectKind [b₀, b₁, b₂, b₃, b₄] d = true →
        ∃ r, evalBuiltin checker [.VCon (.Data d)] = some r) ∧
      (∀ d, selectKind [b₀, b₁, b₂, b₃, b₄] d = false →
        evalBuiltin checker [.VCon (.Data d)] = none) ∧
      (∀ vx, (∀ d, vx ≠ .VCon (.Data d)) → evalBuiltin checker [vx] = none) := by
  cases b₀ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;> simp [kindChecker] at h <;> subst h
  all_goals refine ⟨rfl, fun d hd => ?_, fun d hd => ?_, fun vx hvx => ?_⟩
  all_goals first
    | (cases d <;> first | exact ⟨_, rfl⟩ | rfl | (exfalso; simp [selectKind, kindOf] at hd))
    | (cases vx with
       | VCon c =>
         cases c
         all_goals first | (exact absurd rfl (hvx _)) | rfl
       | _ => rfl)

theorem kindGuard_spec {condition : Expr} {y : VarId} {checker : BuiltinFun}
    (h : kindGuard condition = some (y, checker)) :
    ∃ b₀ b₁ b₂ b₃ b₄ t₀ t₁ t₂ t₃ t₄,
      condition = .App (.App (.App (.App (.App (.App (.Force (.Builtin .ChooseData)) (.Var y))
        (.Lit (.Bool b₀, t₀))) (.Lit (.Bool b₁, t₁))) (.Lit (.Bool b₂, t₂))) (.Lit (.Bool b₃, t₃)))
        (.Lit (.Bool b₄, t₄)) ∧
      kindChecker [b₀, b₁, b₂, b₃, b₄] = some checker := by
  unfold kindGuard at h
  split at h
  · rename_i x c₀ c₁ c₂ c₃ c₄
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨b₀, h₀, b₁, h₁, b₂, h₂, b₃, h₃, b₄, h₄, k, hk, rfl, rfl⟩ := h
    cases c₀ <;> simp [boolLiteral?] at h₀
    cases c₁ <;> simp [boolLiteral?] at h₁
    cases c₂ <;> simp [boolLiteral?] at h₂
    cases c₃ <;> simp [boolLiteral?] at h₃
    cases c₄ <;> simp [boolLiteral?] at h₄
    rename_i l₀ l₁ l₂ l₃ l₄
    obtain ⟨c₀, t₀⟩ := l₀; obtain ⟨c₁, t₁⟩ := l₁; obtain ⟨c₂, t₂⟩ := l₂
    obtain ⟨c₃, t₃⟩ := l₃; obtain ⟨c₄, t₄⟩ := l₄
    cases c₀ <;> simp at h₀
    cases c₁ <;> simp at h₁
    cases c₂ <;> simp at h₂
    cases c₃ <;> simp at h₃
    cases c₄ <;> simp at h₄
    subst h₀ h₁ h₂ h₃ h₄
    exact ⟨_, _, _, _, _, t₀, t₁, t₂, t₃, t₄, rfl, hk⟩
  · cases h

theorem halts_delay_of {ρ : CekEnv} (body : Term) : Halts ρ (.Delay body) (.VDelay body ρ) :=
  ⟨2, rfl⟩

def guardTerm (ix : Nat) (b₀ b₁ b₂ b₃ b₄ : Bool) (t₀ t₁ t₂ t₃ t₄ : BuiltinType) : Term :=
  .Force (.Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse))
    (.Apply (.Apply (.Apply (.Apply (.Apply (.Apply (.Force (.Builtin .ChooseData)) (.Var (ix + 1)))
      (.Constant (.Bool b₀, t₀))) (.Constant (.Bool b₁, t₁))) (.Constant (.Bool b₂, t₂)))
      (.Constant (.Bool b₃, t₃))) (.Constant (.Bool b₄, t₄))))
    (.Delay (.Var (ix + 1)))) (.Delay .Error))

def checkTerm (ix : Nat) (checker : BuiltinFun) : Term :=
  .Apply (.Lam 0 (.Var (ix + 2))) (.Apply (.Builtin checker) (.Var (ix + 1)))

theorem guard_obs {ρ : CekEnv} {π : Stack} {ix : Nat} {vx : CekValue}
    {b₀ b₁ b₂ b₃ b₄ : Bool} {t₀ t₁ t₂ t₃ t₄ : BuiltinType} {checker : BuiltinFun}
    (hk : kindChecker [b₀, b₁, b₂, b₃, b₄] = some checker)
    (hvx : ρ.lookup (ix + 1) = some vx) :
    ObsRefines (.compute π ρ (guardTerm ix b₀ b₁ b₂ b₃ b₄ t₀ t₁ t₂ t₃ t₄))
      (.compute π ρ (checkTerm ix checker)) := by
  obtain ⟨hargs, hsome, hnone, hother⟩ := kindChecker_spec hk
  have hx := halts_var_of_lookup (ρ := ρ) hvx
  have hc : ∀ (b : Bool) (t : BuiltinType), Halts ρ (.Constant (.Bool b, t)) (.VCon (.Bool b)) :=
    fun b t => halts_constant_of _ _
  have hite : Halts ρ (.Force (.Builtin .IfThenElse))
      (.VBuiltin .IfThenElse [] (.more .argV (.more .argV (.one .argV)))) := ⟨4, rfl⟩
  have hpart := halts_choose_partial hx (hc b₀ t₀) (hc b₁ t₁) (hc b₂ t₂) (hc b₃ t₃)
  have hlam : Halts ρ (.Lam 0 (.Var (ix + 2))) (.VLam (.Var (ix + 2)) ρ) := ⟨2, rfl⟩
  by_cases hdata : ∃ d, vx = .VCon (.Data d)
  · obtain ⟨d, rfl⟩ := hdata
    have hcond := halts_apply_intro hpart (hc b₄ t₄)
      (builtin_final_reaches rfl rfl (chooseData_bools b₀ b₁ b₂ b₃ b₄ d))
    generalize hsel : selectKind [b₀, b₁, b₂, b₃, b₄] d = sel at hcond
    have hinner := halts_apply_intro (halts_apply_intro
      (halts_apply_intro hite hcond (builtin_partial_reaches rfl rfl))
      (halts_delay_of (ρ := ρ) (.Var (ix + 1))) (builtin_partial_reaches rfl rfl))
      (halts_delay_of (ρ := ρ) .Error)
      (builtin_final_reaches (args := [.VDelay (.Var (ix + 1)) ρ, .VCon (.Bool sel)]) rfl rfl rfl)
    have hsrc : Reaches (.compute π ρ (guardTerm ix b₀ b₁ b₂ b₃ b₄ t₀ t₁ t₂ t₃ t₄))
        (.compute π ρ (if sel then .Var (ix + 1) else .Error)) := by
      refine reaches_trans (reaches_of_steps 1 rfl) (reaches_trans (halts_on_stack hinner _) ?_)
      refine reaches_of_steps 1 ?_
      cases sel <;> rfl
    cases sel
    · refine obsRefines_of_reaches (reaches_trans hsrc ⟨1, rfl⟩) (errs_on_stack ?_ π)
        (obsRefines_refl _)
      exact errs_apply_arg hlam (errs_apply_intro (halts_builtin_of ρ _) hx
        (builtin_final_errs (by rw [hargs]; rfl) (by rw [hargs]; rfl) (hnone d hsel)))
    · obtain ⟨r, hr⟩ := hsome d hsel
      refine obsRefines_of_reaches (reaches_trans hsrc (halts_on_stack hx π)) (halts_on_stack ?_ π)
        (obsRefines_refl _)
      refine halts_apply_intro hlam (halts_apply_intro (halts_builtin_of ρ _) hx
        (builtin_final_reaches (by rw [hargs]; rfl) (by rw [hargs]; rfl) hr)) ?_
      refine ⟨3, ?_⟩
      show step (step (step (.ret [.funV (.VLam (.Var (ix + 2)) ρ)] r))) = _
      simp [step, CekEnv.extend, CekEnv.lookup, hvx]
  · have hnot : ∀ d, vx ≠ .VCon (.Data d) := fun d h => hdata ⟨d, h⟩
    have hcond : Errs ρ _ := errs_apply_intro hpart (hc b₄ t₄)
      (builtin_final_errs rfl rfl (chooseData_bools_none b₀ b₁ b₂ b₃ b₄ hnot))
    refine obsRefines_of_reaches (errs_on_stack ?_ π) (errs_on_stack ?_ π) (obsRefines_refl _)
    · exact errs_force (errs_apply_fun (errs_apply_fun (errs_apply_arg hite hcond)))
    · exact errs_apply_arg hlam (errs_apply_intro (halts_builtin_of ρ _) hx
        (builtin_final_errs (by rw [hargs]; rfl) (by rw [hargs]; rfl) (hother vx hnot)))

theorem checkedBinder_ne (x : VarId) : (checkedBinder x == x) = false := by
  cases h : (checkedBinder x == x)
  · rfl
  · rw [VarId.beq_true_iff] at h
    simp [checkedBinder] at h

theorem kindGuard_refines {condition : Expr} {x y : VarId} {checker : BuiltinFun}
    (hg : kindGuard condition = some (y, checker)) (hxy : (y == x) = true) :
    MIRCtxRefines
      (.Force (.App (.App (.App (.Force (.Builtin .IfThenElse)) condition) (.Delay (.Var x)))
        (.Delay .Error)))
      (.Let [(checkedBinder x, .App (.Builtin checker) (.Var x), false)] (.Var x)) := by
  obtain ⟨b₀, b₁, b₂, b₃, b₄, t₀, t₁, t₂, t₃, t₄, rfl, hk⟩ := kindGuard_spec hg
  intro env
  have hyx := envLookupT_congr hxy env
  cases hx : envLookupT env x with
  | none =>
    have : lowerTotalExpr env (.Force (.App (.App (.App (.Force (.Builtin .IfThenElse))
        (.App (.App (.App (.App (.App (.App (.Force (.Builtin .ChooseData)) (.Var y))
          (.Lit (.Bool b₀, t₀))) (.Lit (.Bool b₁, t₁))) (.Lit (.Bool b₂, t₂))) (.Lit (.Bool b₃, t₃)))
          (.Lit (.Bool b₄, t₄)))) (.Delay (.Var x))) (.Delay .Error))) = none := by
      simp [MIR.lowerTotalExpr_app, MIR.lowerTotalExpr_force, MIR.lowerTotalExpr_delay,
        lowerTotalExpr_var, lowerTotalExpr_builtin, lowerTotalExpr_lit, hyx, hx]
    rw [this]
    refine ⟨fun h => ?_, ?_⟩
    · simp at h
    · simp
  | some ix =>
    have hsrc : lowerTotalExpr env (.Force (.App (.App (.App (.Force (.Builtin .IfThenElse))
        (.App (.App (.App (.App (.App (.App (.Force (.Builtin .ChooseData)) (.Var y))
          (.Lit (.Bool b₀, t₀))) (.Lit (.Bool b₁, t₁))) (.Lit (.Bool b₂, t₂))) (.Lit (.Bool b₃, t₃)))
          (.Lit (.Bool b₄, t₄)))) (.Delay (.Var x))) (.Delay .Error))) =
        some (guardTerm ix b₀ b₁ b₂ b₃ b₄ t₀ t₁ t₂ t₃ t₄) := by
      simp [guardTerm, MIR.lowerTotalExpr_app, MIR.lowerTotalExpr_force, MIR.lowerTotalExpr_delay,
        lowerTotalExpr_var, lowerTotalExpr_builtin, lowerTotalExpr_lit, lowerTotalExpr_error, hyx, hx]
    have htgt : lowerTotalExpr env
        (.Let [(checkedBinder x, .App (.Builtin checker) (.Var x), false)] (.Var x)) =
        some (checkTerm ix checker) := by
      rw [lowerTotalExpr_let_single]
      simp [checkTerm, MIR.lowerTotalExpr_app, lowerTotalExpr_var, lowerTotalExpr_builtin, hx,
        envLookupT_cons_neq _ _ _ (checkedBinder_ne x)]
    rw [hsrc, htgt]
    refine ⟨fun _ => rfl, ?_⟩
    have hclosed := MIR.lowerTotalExpr_closedAt hsrc
    apply ctxRefines_of_factRefines hclosed
    · intro k hk'
      simp [guardTerm, closedAt] at hk'
      simp [checkTerm, closedAt]
      omega
    · intro ρ π henv _ _ _
      have hbound := envLookupT_bound env x ix hx
      obtain ⟨vx, hvx, _⟩ := envWellFormed_lookup env.length henv (n := ix + 1) (by omega) (by omega)
      exact guard_obs hk hvx

theorem dataCheckRewrite_refines (e : Expr) : MIRCtxRefines e (dataCheckRewrite e) := by
  unfold dataCheckRewrite
  split
  · rename_i condition x
    split
    · rename_i y checker hg
      split
      · rename_i hxy
        exact kindGuard_refines hg hxy
      · exact mirCtxRefines_refl _
    · exact mirCtxRefines_refl _
  · exact mirCtxRefines_refl _

/-! ## Key bytes -/

theorem unBData_produces_bytes {env : List VarId} {ρ : CekEnv} {d : VarId} {v : CekValue}
    (h : Produces env ρ (.App (.Builtin .UnBData) (.Var d)) v) : ∃ kb, v = .VCon (.ByteString kb) := by
  obtain ⟨t, ht, hv⟩ := h
  obtain ⟨tf, ta, htf, _, rfl⟩ := lowerTotalExpr_app_some ht
  rw [lowerTotalExpr_builtin] at htf; cases htf
  obtain ⟨wf, wa, hwf, _, rest⟩ := halts_apply hv
  rw [halts_builtin hwf] at rest
  obtain ⟨args, hlen, heval⟩ := saturated_apply ⟨[], rfl, rfl⟩ rest
  have h1 : valueArity (expectedArgs .UnBData) = 1 := rfl
  rw [h1] at hlen
  have : args = [] := by
    cases args with
    | nil => rfl
    | cons _ _ => simp at hlen
  subst this
  obtain ⟨c, r, rfl, hc, rfl⟩ := evalBuiltin_single (by decide) heval
  obtain ⟨kb, rfl, rfl⟩ : ∃ kb, c = .Data (.B kb) ∧ r = .ByteString kb := by
    cases c with
    | Data dd =>
      cases dd
      all_goals first | (cases hc; done) | exact ⟨_, rfl, (Option.some.inj hc).symm⟩
    | _ => cases hc
  exact ⟨_, rfl⟩

def prefixTerm (ik : Nat) : Term :=
  .Apply (.Apply (.Builtin .AppendByteString) (.Constant (.ByteString zeroByte, .AtomicType .TypeByteString)))
    (.Var (ik + 1))

theorem halts_prefix {ρ : CekEnv} {ik : Nat} {kb : ByteArray}
    (hk : ρ.lookup (ik + 1) = some (.VCon (.ByteString kb))) :
    Halts ρ (prefixTerm ik) (.VCon (.ByteString (zeroByte ++ kb))) :=
  halts_apply_intro (halts_apply_intro (halts_builtin_of ρ _) (halts_constant_of _ _)
    (builtin_partial_reaches rfl rfl)) (halts_var_of_lookup hk) (builtin_final_reaches rfl rfl rfl)

/-- Binding `#00 ++ k` and its `B` value after `k = unBData d`, before a scope
    that mentions neither. -/
theorem insertKey_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {k d bytes other : VarId}
    {S : Expr} (hfb : (freeVars S).contains bytes = false) (hfo : (freeVars S).contains other = false) :
    FactRel G PF ((k, .App (.Builtin .UnBData) (.Var d)) :: Γ) S
      (.Let [(bytes, prefixedKey k, false)]
        (.Let [(other, .App (.Builtin .BData) (.Var bytes), false)] S)) := by
  intro env t _ _ _ hkeys _ hlow
  obtain ⟨ik, hik⟩ := bound_some (hkeys _ (.head _))
  have hS1 : lowerTotalExpr (bytes :: env) S = some (renameTerm (shiftRename 1) t) := by
    rw [MIR.lowerTotalExpr_prepend_unused env bytes S hfb, hlow]; rfl
  have hS2 : lowerTotalExpr (other :: bytes :: env) S =
      some (renameTerm (shiftRename 1) (renameTerm (shiftRename 1) t)) := by
    rw [MIR.lowerTotalExpr_prepend_unused (bytes :: env) other S hfo, hS1]; rfl
  have hbytes : envLookupT (bytes :: env) bytes = some 0 := by
    rw [envLookupT_cons]; simp [varId_beq_self]
  refine ⟨.Apply (.Lam 0 (.Apply (.Lam 0 (renameTerm (shiftRename 1) (renameTerm (shiftRename 1) t)))
      (.Apply (.Builtin .BData) (.Var 1)))) (prefixTerm ik), ?_, ?_⟩
  · rw [lowerTotalExpr_let_single, lowerTotalExpr_let_single]
    simp [prefixedKey, zeroByteLiteral, prefixTerm, MIR.lowerTotalExpr_app, lowerTotalExpr_builtin,
      lowerTotalExpr_lit, lowerTotalExpr_var, hik, hbytes, hS2]
  · have closedT := MIR.lowerTotalExpr_closedAt hlow
    have closed1 := closedAt_shift closedT
    -- the key holds bytes
    have hkey : ∀ ρ, FactsHold PF ((k, .App (.Builtin .UnBData) (.Var d)) :: Γ) env ρ →
        ∃ kb, ρ.lookup (ik + 1) = some (.VCon (.ByteString kb)) := by
      intro ρ hF
      obtain ⟨v, j, _, _, hv, hp⟩ := hF k (k, .App (.Builtin .UnBData) (.Var d)) ik
        (by simp [varId_beq_self]) hik
      obtain ⟨kb, rfl⟩ := unBData_produces_bytes hp.1
      exact ⟨kb, hv⟩
    let F' : CekEnv → Prop := fun ρ => ∃ bs, ρ.lookup 1 = some (.VCon (.ByteString bs))
    have hinner : FactRefines (env.length + 1) F' (renameTerm (shiftRename 1) t)
        (.Apply (.Lam 0 (renameTerm (shiftRename 1) (renameTerm (shiftRename 1) t)))
          (.Apply (.Builtin .BData) (.Var 1))) := by
      apply factRefines_add_let 0 closed1
      intro ρ ⟨bs, hbs⟩ _ _
      exact ⟨_, halts_apply_intro (halts_builtin_of ρ _) (halts_var_of_lookup hbs)
        (builtin_final_reaches rfl rfl rfl)⟩
    have hclosedP : closedAt env.length (prefixTerm ik) = true := by
      have := envLookupT_bound env k ik hik
      simp [prefixTerm, closedAt]; omega
    have hmid := factRefines_let (F := FactsHold PF ((k, .App (.Builtin .UnBData) (.Var d)) :: Γ) env)
      (G := F') (d := env.length) (r := prefixTerm ik) 0 0 hclosedP
      (fun ρ v hF hv => by
        obtain ⟨kb, hk⟩ := hkey ρ hF
        rw [halts_unique hv (halts_prefix hk)]
        exact ⟨_, rfl⟩) hinner
    refine FactRefines.trans ?_ hmid
    apply factRefines_add_let 0 closedT
    intro ρ hF _ _
    obtain ⟨kb, hk⟩ := hkey ρ hF
    exact ⟨_, halts_prefix hk⟩

/-! ## The insertion walk -/

theorem unBDataSource_spec {e : Expr} {d : VarId} (h : unBDataSource e = some d) :
    e = .App (.Builtin .UnBData) (.Var d) := by
  unfold unBDataSource at h
  split at h
  · cases h; rfl
  · cases h

theorem keyBytesBindings_cons (base : Nat) (bindings : List (VarId × Expr)) (k : VarId) (rhs : Expr)
    (er : Bool) (rest : List (VarId × Expr × Bool)) (body : Expr) :
    keyBytesBindings base bindings ((k, rhs, er) :: rest) body =
      let processed := keyBytesBindings base bindings rest body
      let rhs' := keyBytesWalk base bindings rhs
      let scope := Expr.Let processed.1 processed.2
      match unBDataSource rhs' with
      | some d =>
        if anyExpr (comparesKey bindings d) (exprSize scope) scope &&
            !anyExpr (isPrefixedKey bindings k) (exprSize scope) scope then
          let bytes : VarId :=
            { uid := max base (max k.uid (maxUidExpr scope) + 1), origin := .gen, hint := "keyBytes" }
          let other : VarId := { uid := bytes.uid + 1, origin := .gen, hint := "otherKey" }
          ((k, rhs', er) :: (bytes, prefixedKey k, false) ::
            (other, .App (.Builtin .BData) (.Var bytes), false) :: processed.1, processed.2)
        else ((k, rhs', er) :: processed.1, processed.2)
      | none => ((k, rhs', er) :: processed.1, processed.2) := by
  rw [keyBytesBindings]; rfl

theorem beq_false_of_uid {x y : VarId} (h : x.uid ≠ y.uid) : (x == y) = false := by
  cases hb : (x == y)
  · rfl
  · exact absurd ((VarId.beq_true_iff x y).mp hb).2 h

theorem lookup_cons_none {env : List VarId} {x y : VarId} (hxy : x.uid ≠ y.uid)
    (hy : envLookupT env y = none) : (envLookupT (x :: env) y).isNone = true := by
  rw [envLookupT_cons_neq x y env (beq_false_of_uid hxy), hy]; rfl

theorem keyBindings_fresh (base : Nat) (bindings : List (VarId × Expr)) (body : Expr)
    (hb : ∀ env, (∀ y ∈ env, GenSafe base y) → freshIn env body = true →
      freshIn env (keyBytesWalk base bindings body) = true) :
    ∀ (binds : List (VarId × Expr × Bool)),
      (∀ b ∈ binds, b.1.uid < base) →
      (∀ b ∈ binds, ∀ env, (∀ y ∈ env, GenSafe base y) →
        freshIn env b.2.1 = true → freshIn env (keyBytesWalk base bindings b.2.1) = true) →
      ∀ env, (∀ y ∈ env, GenSafe base y) → freshIn env (.Let binds body) = true →
        freshIn env (.Let (keyBytesBindings base bindings binds body).1
          (keyBytesBindings base bindings binds body).2) = true
  | [], _, _, env, hG, hf => by
    rw [keyBytesBindings.eq_1]
    rw [freshIn_let_nil] at hf ⊢
    exact hb env hG hf
  | (k, r, er) :: rest, hx, hr, env, hG, hf => by
    rw [keyBytesBindings_cons]
    rw [freshIn_let_cons, freshIn_let_single] at hf
    simp only [Bool.and_eq_true] at hf
    obtain ⟨⟨hfr, hke⟩, hfrest⟩ := hf
    have hk : k.uid < base := hx _ (.head _)
    have ih := keyBindings_fresh base bindings body hb rest (fun b hb' => hx b (.tail _ hb'))
      (fun b hb' => hr b (.tail _ hb')) (k :: env) (allG_cons (.inl hk) hG) hfrest
    have hr' := hr _ (.head _) env hG hfr
    have plain : freshIn env (.Let ((k, keyBytesWalk base bindings r, er) ::
        (keyBytesBindings base bindings rest body).1) (keyBytesBindings base bindings rest body).2) = true := by
      rw [freshIn_let_cons, freshIn_let_single]
      simp only [Bool.and_eq_true]
      exact ⟨⟨hr', hke⟩, ih⟩
    simp only []
    split
    · split
      · generalize hS : Expr.Let (keyBytesBindings base bindings rest body).1
          (keyBytesBindings base bindings rest body).2 = S at ih
        have hbig : maxUidExpr S < max base (max k.uid (maxUidExpr S) + 1) := by omega
        rw [freshIn_let_cons, freshIn_let_single, freshIn_let_cons, freshIn_let_single,
          freshIn_let_cons, freshIn_let_single, hS]
        simp only [Bool.and_eq_true]
        refine ⟨⟨hr', hke⟩, ⟨by simp [prefixedKey, zeroByteLiteral, freshIn], ?_⟩,
          ⟨by simp [freshIn], ?_⟩, ?_⟩
        · exact lookup_cons_none (by simp; omega)
            (lookup_none_of_not_G hG (not_genSafe (by simp only []; omega) rfl))
        · rw [envLookupT_cons_neq _ _ _ (beq_false_of_uid (by simp))]
          simp only [Option.isNone_map]
          exact lookup_cons_none (by simp; omega)
            (lookup_none_of_not_G hG (not_genSafe (by simp; omega) rfl))
        · exact freshIn_cons_of_big (freshIn_cons_of_big ih hbig) (by simp; omega)
      · exact plain
    · exact plain

theorem keyBytesWalk_fresh (base : Nat) (bindings : List (VarId × Expr)) :
    ∀ (e : Expr) (env : List VarId), (∀ y ∈ env, GenSafe base y) →
      maxUidExpr e < base → freshIn env e = true →
      freshIn env (keyBytesWalk base bindings e) = true
  | .Let binds body, env, hG, hmax, hf => by
    rw [keyBytesWalk.eq_1]
    simp only [maxUidExpr] at hmax
    exact keyBindings_fresh base bindings body
      (fun env' hG' hf' => keyBytesWalk_fresh base bindings body env' hG' (by omega) hf')
      binds (fun b hb => by have := (maxUidExprBinds_mem hb).1; omega)
      (fun b hb env' hG' hf' => keyBytesWalk_fresh base bindings b.2.1 env' hG'
        (by have := (maxUidExprBinds_mem hb).2; omega) hf') env hG hf
  | .Lam x b, env, hG, hmax, hf => by
    rw [keyBytesWalk.eq_2]
    simp only [maxUidExpr] at hmax
    simp only [freshIn, Bool.and_eq_true] at hf ⊢
    exact ⟨hf.1, keyBytesWalk_fresh base bindings b (x :: env) (allG_cons (.inl (by omega)) hG)
      (by omega) hf.2⟩
  | .Fix x b, env, hG, hmax, hf => by
    rw [keyBytesWalk.eq_3]
    simp only [maxUidExpr] at hmax
    simp only [freshIn, Bool.and_eq_true] at hf ⊢
    exact ⟨hf.1, keyBytesWalk_fresh base bindings b (x :: env) (allG_cons (.inl (by omega)) hG)
      (by omega) hf.2⟩
  | .App f a, env, hG, hmax, hf => by
    rw [keyBytesWalk.eq_4]
    simp only [maxUidExpr] at hmax
    simp only [freshIn, Bool.and_eq_true] at hf ⊢
    exact ⟨keyBytesWalk_fresh base bindings f env hG (by omega) hf.1,
      keyBytesWalk_fresh base bindings a env hG (by omega) hf.2⟩
  | .Force b, env, hG, hmax, hf => by
    rw [keyBytesWalk.eq_5]
    simp only [maxUidExpr] at hmax
    simp only [freshIn] at hf ⊢
    exact keyBytesWalk_fresh base bindings b env hG (by omega) hf
  | .Delay b, env, hG, hmax, hf => by
    rw [keyBytesWalk.eq_6]
    simp only [maxUidExpr] at hmax
    simp only [freshIn] at hf ⊢
    exact keyBytesWalk_fresh base bindings b env hG (by omega) hf
  | .Constr tag fields, env, hG, hmax, hf => by
    rw [keyBytesWalk.eq_7]
    simp only [maxUidExpr] at hmax
    simp only [freshIn] at hf ⊢
    rw [freshInList_iff] at hf ⊢
    intro y hy
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    have := maxUidExpr_le_maxUidExprList_of_mem hc
    exact keyBytesWalk_fresh base bindings c env hG (by omega) (hf c hc)
  | .Case scrut alts, env, hG, hmax, hf => by
    rw [keyBytesWalk.eq_8]
    simp only [maxUidExpr] at hmax
    simp only [freshIn, Bool.and_eq_true] at hf ⊢
    refine ⟨keyBytesWalk_fresh base bindings scrut env hG (by omega) hf.1, ?_⟩
    have hf2 := hf.2
    rw [freshInList_iff] at hf2 ⊢
    intro y hy
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    have := maxUidExpr_le_maxUidExprList_of_mem hc
    exact keyBytesWalk_fresh base bindings c env hG (by omega) (hf2 c hc)
  | .Var _, env, _, _, hf => by rw [keyBytesWalk.eq_9]; exact hf
  | .Lit _, env, _, _, hf => by rw [keyBytesWalk.eq_10]; exact hf
  | .Builtin _, env, _, _, hf => by rw [keyBytesWalk.eq_11]; exact hf
  | .Error, env, _, _, hf => by rw [keyBytesWalk.eq_12]; exact hf
termination_by e => exprSize e
decreasing_by
  all_goals first
    | (subst_vars; simp only [exprSize, exprSizeList]; omega)
    | (simp only [exprSize]; have := exprSize_pos body; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)
    | (have := exprSizeBinds_mem_lt (by assumption); simp only [exprSize]; have := exprSize_pos body; omega)

theorem lowerTotalExpr_let_three (env : List VarId) (a b c : VarId × Expr × Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) :
    lowerTotalExpr env (.Let (a :: b :: c :: rest) body) =
      lowerTotalExpr env (.Let [a] (.Let [b] (.Let [c] (.Let rest body)))) := by
  obtain ⟨x, r, er⟩ := a
  obtain ⟨y, s, es⟩ := b
  obtain ⟨z, u, eu⟩ := c
  simp only [lowerTotalExpr, expandFix, expandFixBinds, lowerTotal, lowerTotalLet]

theorem keyBindings_factRel (base : Nat) (bindings : List (VarId × Expr)) (body : Expr)
    (hb : ∀ Γ : List (VarId × Expr), FactRel (GenSafe base) PF Γ body (keyBytesWalk base bindings body))
    (hbf : ∀ env, (∀ y ∈ env, GenSafe base y) → freshIn env body = true →
      freshIn env (keyBytesWalk base bindings body) = true) :
    ∀ (binds : List (VarId × Expr × Bool)),
      (∀ b ∈ binds, b.1.uid < base) →
      (∀ b ∈ binds, ∀ Γ : List (VarId × Expr),
        FactRel (GenSafe base) PF Γ b.2.1 (keyBytesWalk base bindings b.2.1)) →
      (∀ b ∈ binds, ∀ env, (∀ y ∈ env, GenSafe base y) →
        freshIn env b.2.1 = true → freshIn env (keyBytesWalk base bindings b.2.1) = true) →
      ∀ Γ : List (VarId × Expr),
        FactRel (GenSafe base) PF Γ (.Let binds body)
          (.Let (keyBytesBindings base bindings binds body).1
            (keyBytesBindings base bindings binds body).2)
  | [], _, _, _, Γ => by
    rw [keyBytesBindings.eq_1]
    exact ((hb Γ).congr_left (fun env => lowerTotalExpr_let_nil env body)
      (fun avoid => freshIn_let_nil avoid body)).congr_right
      (fun env => lowerTotalExpr_let_nil env _)
  | (k, r, er) :: rest, hx, hr, hrf, Γ => by
    rw [keyBytesBindings_cons]
    have hk : k.uid < base := hx _ (.head _)
    have ih := fun Γ' => keyBindings_factRel base bindings body hb hbf rest
      (fun b hb' => hx b (.tail _ hb')) (fun b hb' => hr b (.tail _ hb'))
      (fun b hb' => hrf b (.tail _ hb')) Γ'
    have hrestf := keyBindings_fresh base bindings body hbf rest (fun b hb' => hx b (.tail _ hb'))
      (fun b hb' => hrf b (.tail _ hb'))
    have hpush : ∀ env ρ v, (∀ y ∈ env, GenSafe base y) → EnvDistinct env → freshIn env r = true →
        Produces env ρ (keyBytesWalk base bindings r) v → PF env ρ (keyBytesWalk base bindings r) v :=
      fun env ρ v hG _ hfr hp => ⟨hp, hrf _ (.head _) env hG hfr⟩
    have plain : FactRel (GenSafe base) PF Γ (.Let ((k, r, er) :: rest) body)
        (.Let ((k, keyBytesWalk base bindings r, er) :: (keyBytesBindings base bindings rest body).1)
          (keyBytesBindings base bindings rest body).2) :=
      ((FactRel.let_single (er := er) (keyBytesWalk base bindings r) (.inl hk) (.inr rfl)
        (hr _ (.head _) Γ) (ih _) hpush).congr_left
        (fun env => lowerTotalExpr_let_cons env _ _ _) (fun avoid => freshIn_let_cons avoid _ _ _)).congr_right
        (fun env => lowerTotalExpr_let_cons env _ _ _)
    simp only []
    split
    · rename_i d hd
      split
      · have hrd := unBDataSource_spec hd
        generalize hS : Expr.Let (keyBytesBindings base bindings rest body).1
          (keyBytesBindings base bindings rest body).2 = S at ih hrestf
        have hbig : maxUidExpr S < max base (max k.uid (maxUidExpr S) + 1) := by omega
        have hins := insertKey_factRel (G := GenSafe base) (Γ := Γ) (k := k) (d := d)
          (bytes := { uid := max base (max k.uid (maxUidExpr S) + 1), origin := .gen, hint := "keyBytes" })
          (other := { uid := max base (max k.uid (maxUidExpr S) + 1) + 1, origin := .gen, hint := "otherKey" })
          (S := S)
          (maxUidExpr_fresh S _ hbig) (maxUidExpr_fresh S _ (by simp only []; omega))
        rw [← hrd] at hins
        have hinner := (ih ((k, keyBytesWalk base bindings r) :: Γ)).trans hins
          (fun env hG hf => hrestf env hG hf)
        refine ((FactRel.let_single (er := er) (keyBytesWalk base bindings r) (.inl hk) (.inr rfl)
          (hr _ (.head _) Γ) hinner hpush).congr_left
          (fun env => lowerTotalExpr_let_cons env _ _ _)
          (fun avoid => freshIn_let_cons avoid _ _ _)).congr_right ?_
        intro env
        subst hS
        exact lowerTotalExpr_let_three env _ _ _ _ _
      · exact plain
    · exact plain

theorem keyBytesWalk_factRel (base : Nat) (bindings : List (VarId × Expr)) :
    ∀ (e : Expr) (Γ : List (VarId × Expr)), maxUidExpr e < base →
      FactRel (GenSafe base) PF Γ e (keyBytesWalk base bindings e)
  | .Let binds body, Γ, hmax => by
    rw [keyBytesWalk.eq_1]
    simp only [maxUidExpr] at hmax
    exact keyBindings_factRel base bindings body
      (fun Γ' => keyBytesWalk_factRel base bindings body Γ' (by omega))
      (fun env' hG' hf' => keyBytesWalk_fresh base bindings body env' hG' (by omega) hf')
      binds (fun b hb => by have := (maxUidExprBinds_mem hb).1; omega)
      (fun b hb Γ' => keyBytesWalk_factRel base bindings b.2.1 Γ'
        (by have := (maxUidExprBinds_mem hb).2; omega))
      (fun b hb env' hG' hf' => keyBytesWalk_fresh base bindings b.2.1 env' hG'
        (by have := (maxUidExprBinds_mem hb).2; omega) hf') Γ
  | .Lam x b, Γ, hmax => by
    rw [keyBytesWalk.eq_2]
    simp only [maxUidExpr] at hmax
    exact (keyBytesWalk_factRel base bindings b Γ (by omega)).lam (.inl (by omega))
  | .Fix f b, Γ, hmax => by
    rw [keyBytesWalk.eq_3]
    simp only [maxUidExpr] at hmax
    cases b with
    | Lam x inner =>
      rw [keyBytesWalk.eq_2]
      simp only [maxUidExpr] at hmax
      exact (keyBytesWalk_factRel base bindings inner Γ (by omega)).fix_lam (.inl (by omega))
        (.inl (by omega)) (fun y hy => .inr (by rw [hy]; simp))
    | _ =>
      intro env t _ _ _ _ _ hlow
      rw [MIR.lowerTotalExpr_fix_nonlam_none env f _ (by intros; simp)] at hlow
      cases hlow
  | .App f a, Γ, hmax => by
    rw [keyBytesWalk.eq_4]
    simp only [maxUidExpr] at hmax
    exact (keyBytesWalk_factRel base bindings f Γ (by omega)).app
      (keyBytesWalk_factRel base bindings a Γ (by omega))
  | .Force b, Γ, hmax => by
    rw [keyBytesWalk.eq_5]
    simp only [maxUidExpr] at hmax
    exact (keyBytesWalk_factRel base bindings b Γ (by omega)).force
  | .Delay b, Γ, hmax => by
    rw [keyBytesWalk.eq_6]
    simp only [maxUidExpr] at hmax
    exact (keyBytesWalk_factRel base bindings b Γ (by omega)).delay
  | .Constr tag fields, Γ, hmax => by
    rw [keyBytesWalk.eq_7]
    simp only [maxUidExpr] at hmax
    exact FactRel.constr (listRel_attach_map fields _ fun c hc => keyBytesWalk_factRel base bindings c Γ
      (by have := maxUidExpr_le_maxUidExprList_of_mem hc; omega))
  | .Case scrut alts, Γ, hmax => by
    rw [keyBytesWalk.eq_8]
    simp only [maxUidExpr] at hmax
    exact FactRel.case (keyBytesWalk_factRel base bindings scrut Γ (by omega))
      (listRel_attach_map alts _ fun c hc => keyBytesWalk_factRel base bindings c Γ
        (by have := maxUidExpr_le_maxUidExprList_of_mem hc; omega))
  | .Var _, Γ, _ => by rw [keyBytesWalk.eq_9]; exact FactRel.refl _ _ _ _
  | .Lit _, Γ, _ => by rw [keyBytesWalk.eq_10]; exact FactRel.refl _ _ _ _
  | .Builtin _, Γ, _ => by rw [keyBytesWalk.eq_11]; exact FactRel.refl _ _ _ _
  | .Error, Γ, _ => by rw [keyBytesWalk.eq_12]; exact FactRel.refl _ _ _ _
termination_by e => exprSize e
decreasing_by
  all_goals first
    | (subst_vars; simp only [exprSize, exprSizeList]; omega)
    | (simp only [exprSize]; have := exprSize_pos body; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)
    | (have := exprSizeBinds_mem_lt (by assumption); simp only [exprSize]; have := exprSize_pos body; omega)

end Moist.Verified.ShapeFacts

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced

theorem specializeDataChecks_refines (e : Expr) : MIRCtxRefines e (specializeDataChecks e) := by
  unfold specializeDataChecks
  apply rewriteBottomUp_refines dataCheckRewrite ShapeFacts.dataCheckRewrite_refines
  intro binder body
  simp [dataCheckRewrite]

open Moist.Verified.ShapeFacts in
theorem insertKeyBytes_refines (e : Expr) : MIRCtxRefines e (insertKeyBytes e) := by
  unfold insertKeyBytes
  simp only
  split
  · rename_i hws
    refine mirCtxRefines_trans (Hygiene.uniqueOptimizationBinders_refines e) ?_
    exact mirCtxRefines_of_factRel hws
      (fun y hy => .inl (by have := freeVars_uid_lt hy; omega))
      (fun y hy => .inr (by rw [hy]; simp))
      (keyBytesWalk_factRel _ _ _ [] (by omega))
  · exact Hygiene.uniqueOptimizationBinders_refines e

end Moist.Verified.MIR
