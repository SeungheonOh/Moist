import Moist.Verified.HygieneSoundness

/-! # Soundness of the Boolean alpha-equivalence checker

`Moist.MIR.alphaEq` is used as a guard by passes that replace one
expression by an alpha-equivalent one. Alpha-equal expressions have the
same total lowering in every environment, hence refine each other.
-/

namespace Moist.Verified.MIR

open Moist.MIR
open Moist.Plutus (Data ByteString)
open Moist.Plutus.Term (Term Const BuiltinType BuiltinFun AtomicType TypeOperator)

/-! ## Lawfulness of the literal comparisons -/

theorem atomicType_eq_of_beq {a b : AtomicType} (h : (a == b) = true) : a = b := by
  have hidx : a.ctorIdx = b.ctorIdx := by
    simpa [BEq.beq, Moist.Plutus.Term.instBEqAtomicType.beq] using h
  have := congrArg AtomicType.ofNat hidx
  rwa [AtomicType.ofNat_ctorIdx, AtomicType.ofNat_ctorIdx] at this

theorem builtinFun_eq_of_beq {a b : BuiltinFun} (h : (a == b) = true) : a = b := by
  have hidx : a.ctorIdx = b.ctorIdx := by
    simpa [BEq.beq, Moist.Plutus.Term.instBEqBuiltinFun.beq] using h
  have := congrArg BuiltinFun.ofNat hidx
  rwa [BuiltinFun.ofNat_ctorIdx, BuiltinFun.ofNat_ctorIdx] at this

theorem byteString_eq_of_beq {a b : ByteString} (h : (a == b) = true) : a = b :=
  ByteArray.ext (Array.eq_of_isEqv a.data b.data h)

mutual
  theorem builtinType_eq_of_builtinTypeEq :
      ∀ {a b : BuiltinType}, builtinTypeEq a b = true → a = b
    | .AtomicType a, .AtomicType b, h => by
      simp only [builtinTypeEq] at h
      rw [atomicType_eq_of_beq h]
    | .TypeOperator a, .TypeOperator b, h => by
      simp only [builtinTypeEq] at h
      rw [typeOperator_eq_of_typeOperatorEq h]
    | .AtomicType _, .TypeOperator _, h => by
      simp only [builtinTypeEq, Bool.false_eq_true] at h
    | .TypeOperator _, .AtomicType _, h => by
      simp only [builtinTypeEq, Bool.false_eq_true] at h

  theorem typeOperator_eq_of_typeOperatorEq :
      ∀ {a b : TypeOperator}, typeOperatorEq a b = true → a = b
    | .TypeList a, .TypeList b, h => by
      simp only [typeOperatorEq] at h
      rw [builtinType_eq_of_builtinTypeEq h]
    | .TypePair a1 a2, .TypePair b1 b2, h => by
      simp only [typeOperatorEq, Bool.and_eq_true] at h
      rw [builtinType_eq_of_builtinTypeEq h.1, builtinType_eq_of_builtinTypeEq h.2]
    | .TypeList _, .TypePair _ _, h | .TypeList _, .TypeArray _, h
    | .TypePair _ _, .TypeList _, h | .TypePair _ _, .TypeArray _, h
    | .TypeArray _, .TypeList _, h | .TypeArray _, .TypePair _ _, h
    | .TypeArray _, .TypeArray _, h => by
      simp only [typeOperatorEq, Bool.false_eq_true] at h
end

mutual
  theorem data_eq_of_dataEq : ∀ {a b : Data}, dataEq a b = true → a = b
    | .Constr i1 a1, .Constr i2 a2, h => by
      simp only [dataEq, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1, dataList_eq_of_dataEqList h.2]
    | .Map m1, .Map m2, h => by
      simp only [dataEq] at h
      rw [dataPairs_eq_of_dataEqPairs h]
    | .List l1, .List l2, h => by
      simp only [dataEq] at h
      rw [dataList_eq_of_dataEqList h]
    | .I i1, .I i2, h => by
      simp only [dataEq, beq_iff_eq] at h
      rw [h]
    | .B b1, .B b2, h => by
      simp only [dataEq] at h
      rw [byteString_eq_of_beq h]
    | .Constr _ _, .Map _, h | .Constr _ _, .List _, h | .Constr _ _, .I _, h
    | .Constr _ _, .B _, h | .Map _, .Constr _ _, h | .Map _, .List _, h
    | .Map _, .I _, h | .Map _, .B _, h | .List _, .Constr _ _, h
    | .List _, .Map _, h | .List _, .I _, h | .List _, .B _, h
    | .I _, .Constr _ _, h | .I _, .Map _, h | .I _, .List _, h | .I _, .B _, h
    | .B _, .Constr _ _, h | .B _, .Map _, h | .B _, .List _, h | .B _, .I _, h => by
      simp only [dataEq, Bool.false_eq_true] at h

  theorem dataList_eq_of_dataEqList : ∀ {a b : List Data}, dataEqList a b = true → a = b
    | [], [], _ => rfl
    | x :: xs, y :: ys, h => by
      simp only [dataEqList, Bool.and_eq_true] at h
      rw [data_eq_of_dataEq h.1, dataList_eq_of_dataEqList h.2]
    | [], _ :: _, h | _ :: _, [], h => by
      simp only [dataEqList, Bool.false_eq_true] at h

  theorem dataPairs_eq_of_dataEqPairs :
      ∀ {a b : List (Data × Data)}, dataEqPairs a b = true → a = b
    | [], [], _ => rfl
    | (x1, x2) :: xs, (y1, y2) :: ys, h => by
      simp only [dataEqPairs, Bool.and_eq_true] at h
      rw [data_eq_of_dataEq h.1.1, data_eq_of_dataEq h.1.2, dataPairs_eq_of_dataEqPairs h.2]
    | [], _ :: _, h | _ :: _, [], h => by
      simp only [dataEqPairs, Bool.false_eq_true] at h
end

mutual
  theorem const_eq_of_constEq : ∀ {a b : Const}, constEq a b = true → a = b
    | a, b, h => by
      cases a <;> cases b <;> simp only [constEq, Bool.false_eq_true] at h
      · simp only [beq_iff_eq] at h; rw [h]
      · rw [byteString_eq_of_beq h]
      · simp only [beq_iff_eq] at h; rw [h]
      · rfl
      · simp only [beq_iff_eq] at h; rw [h]
      · rw [constList_eq_of_constEqList h]
      · rw [dataList_eq_of_dataEqList h]
      · rw [dataPairs_eq_of_dataEqPairs h]
      · rename_i p q
        obtain ⟨p1, p2⟩ := p
        obtain ⟨q1, q2⟩ := q
        simp only [Bool.and_eq_true] at h
        rw [const_eq_of_constEq h.1, const_eq_of_constEq h.2]
      · rename_i p q
        obtain ⟨p1, p2⟩ := p
        obtain ⟨q1, q2⟩ := q
        simp only [Bool.and_eq_true] at h
        rw [data_eq_of_dataEq h.1, data_eq_of_dataEq h.2]
      · rw [data_eq_of_dataEq h]
      · rfl
      · rfl
      · rfl

  theorem constList_eq_of_constEqList : ∀ {a b : List Const}, constEqList a b = true → a = b
    | [], [], _ => rfl
    | x :: xs, y :: ys, h => by
      simp only [constEqList, Bool.and_eq_true] at h
      rw [const_eq_of_constEq h.1, constList_eq_of_constEqList h.2]
    | [], _ :: _, h | _ :: _, [], h => by
      simp only [constEqList, Bool.false_eq_true] at h
end

theorem lit_eq_of_litEq {a b : Const × BuiltinType} (h : litEq a b = true) : a = b := by
  obtain ⟨c1, t1⟩ := a
  obtain ⟨c2, t2⟩ := b
  simp only [litEq, Bool.and_eq_true] at h
  rw [const_eq_of_constEq h.1, builtinType_eq_of_builtinTypeEq h.2]

/-! ## Variable lookups -/

theorem envLookupT_go_eq_findIdx? (v : VarId) :
    ∀ (env : List VarId) (n : Nat),
      envLookupT.go v env n = (env.findIdx? (· == v)).map (· + n)
  | [], n => by simp [envLookupT.go]
  | x :: xs, n => by
    simp only [envLookupT.go, List.findIdx?_cons]
    split <;> simp [envLookupT_go_eq_findIdx? v xs, Option.map_map, Function.comp_def,
      Nat.add_comm, Nat.add_left_comm]

theorem envLookupT_eq_findIdx? (env : List VarId) (v : VarId) :
    envLookupT env v = env.findIdx? (· == v) := by
  simpa [envLookupT] using envLookupT_go_eq_findIdx? v env 0

theorem alphaEqAux_var_eq (A1 A2 : List VarId) (x y : VarId) :
    alphaEqAux A1 A2 (.Var x) (.Var y) =
      (match envLookupT A1 x, envLookupT A2 y with
       | some i, some j => i == j
       | none, none => x == y
       | _, _ => false) := by
  rw [alphaEqAux.eq_1, lookupIdx_eq_findIdx?, lookupIdx_eq_findIdx?,
    envLookupT_eq_findIdx?, envLookupT_eq_findIdx?]
  rfl

theorem envLookupT_go_congr {x y : VarId} (h : (x == y) = true) :
    ∀ (env : List VarId) (n : Nat), envLookupT.go x env n = envLookupT.go y env n
  | [], _ => rfl
  | z :: zs, n => by
    have hxy := (VarId.beq_true_iff x y).mp h
    have hz : (z == x) = (z == y) := by
      show (z.origin == x.origin && z.uid == x.uid) = (z.origin == y.origin && z.uid == y.uid)
      rw [hxy.1, hxy.2]
    simp only [envLookupT.go, hz, envLookupT_go_congr h zs (n + 1)]

theorem envLookupT_cons_of_beq {a x : VarId} (h : (a == x) = true) (env : List VarId) :
    envLookupT (a :: env) x = some 0 := by
  simp only [envLookupT, envLookupT.go, h, if_true]

/-- Lowering environments `L1`, `L2` resolve every pair of variables that the
checker identifies under the alpha environments `A1`, `A2` to the same index. -/
def VarRel (A1 A2 L1 L2 : List VarId) : Prop :=
  ∀ x y, alphaEqAux A1 A2 (.Var x) (.Var y) = true → envLookupT L1 x = envLookupT L2 y

theorem VarRel.nil (L : List VarId) : VarRel [] [] L L := by
  intro x y h
  rw [alphaEqAux_var_eq] at h
  simp only [envLookupT, envLookupT.go] at h
  simp only [envLookupT]
  exact envLookupT_go_congr h L 0

theorem VarRel.cons {A1 A2 L1 L2 : List VarId} (hR : VarRel A1 A2 L1 L2) (a b : VarId) :
    VarRel (a :: A1) (b :: A2) (a :: L1) (b :: L2) := by
  intro x y h
  rw [alphaEqAux_var_eq] at h
  cases ha : (a == x) <;> cases hb : (b == y)
  · rw [envLookupT_cons_neq _ _ _ ha, envLookupT_cons_neq _ _ _ hb] at h
    rw [envLookupT_cons_neq _ _ _ ha, envLookupT_cons_neq _ _ _ hb]
    have hinner : alphaEqAux A1 A2 (.Var x) (.Var y) = true := by
      rw [alphaEqAux_var_eq]
      cases e1 : envLookupT A1 x <;> cases e2 : envLookupT A2 y <;>
        simp_all
    rw [hR x y hinner]
  · rw [envLookupT_cons_neq _ _ _ ha, envLookupT_cons_of_beq hb] at h
    cases e1 : envLookupT A1 x <;> simp_all
  · rw [envLookupT_cons_of_beq ha, envLookupT_cons_neq _ _ _ hb] at h
    cases e2 : envLookupT A2 y <;> simp_all
  · rw [envLookupT_cons_of_beq ha, envLookupT_cons_of_beq hb]

/-! ## Fix with a non-lambda body -/

theorem lowerTotalExpr_fix_nonLam (L : List VarId) (f : VarId) (body : Expr)
    (h : ∀ x inner, body ≠ .Lam x inner) : lowerTotalExpr L (.Fix f body) = none := by
  cases body with
  | Lam x inner => exact absurd rfl (h x inner)
  | _ => simp [lowerTotalExpr, expandFix, lowerTotal]

theorem alphaEqAux_lam_left {A1 A2 : List VarId} {x : VarId} {c b : Expr}
    (h : alphaEqAux A1 A2 (.Lam x c) b = true) :
    ∃ y d, b = .Lam y d ∧ alphaEqAux (x :: A1) (y :: A2) c d = true := by
  cases b <;> simp only [alphaEqAux, Bool.false_eq_true] at h
  exact ⟨_, _, rfl, h⟩

theorem alphaEqAux_lam_right {A1 A2 : List VarId} {y : VarId} {a d : Expr}
    (h : alphaEqAux A1 A2 a (.Lam y d) = true) :
    ∃ x c, a = .Lam x c ∧ alphaEqAux (x :: A1) (y :: A2) c d = true := by
  cases a <;> simp only [alphaEqAux, Bool.false_eq_true] at h
  exact ⟨_, _, rfl, h⟩

/-! ## Main theorem -/

mutual
  theorem alphaEqAux_lowerTotalExpr_eq {A1 A2 L1 L2 : List VarId}
      (hR : VarRel A1 A2 L1 L2) {a b : Expr} (h : alphaEqAux A1 A2 a b = true) :
      lowerTotalExpr L1 a = lowerTotalExpr L2 b := by
    cases a <;> cases b <;>
      first
        | (simp only [alphaEqAux, Bool.false_eq_true] at h; done)
        | skip
    case Var.Var x y =>
      simp only [lowerTotalExpr, expandFix, lowerTotal, hR x y h]
    case Lit.Lit c d =>
      simp only [alphaEqAux] at h
      rw [lit_eq_of_litEq h]
      obtain ⟨c0, t0⟩ := d
      simp [lowerTotalExpr, expandFix, lowerTotal]
    case Builtin.Builtin p q =>
      simp only [alphaEqAux] at h
      rw [builtinFun_eq_of_beq h]
      simp [lowerTotalExpr, expandFix, lowerTotal]
    case Error.Error => simp [lowerTotalExpr, expandFix, lowerTotal]
    case Lam.Lam x body1 y body2 =>
      simp only [alphaEqAux] at h
      rw [lowerTotalExpr_lam, lowerTotalExpr_lam,
        alphaEqAux_lowerTotalExpr_eq (hR.cons x y) h]
    case Fix.Fix f body1 g body2 =>
      simp only [alphaEqAux] at h
      by_cases hl : ∃ x c, body1 = .Lam x c
      · obtain ⟨x, c, rfl⟩ := hl
        obtain ⟨y, d, rfl, hcd⟩ := alphaEqAux_lam_left h
        rw [lowerTotalExpr_fix_lam_shift, lowerTotalExpr_fix_lam_shift,
          alphaEqAux_lowerTotalExpr_eq ((hR.cons f g).cons x y) hcd]
      · have hl2 : ¬ ∃ y d, body2 = .Lam y d := by
          rintro ⟨y, d, rfl⟩
          obtain ⟨x, c, rfl, _⟩ := alphaEqAux_lam_right h
          exact hl ⟨x, c, rfl⟩
        rw [lowerTotalExpr_fix_nonLam _ _ _ (fun x c he => hl ⟨x, c, he⟩),
          lowerTotalExpr_fix_nonLam _ _ _ (fun y d he => hl2 ⟨y, d, he⟩)]
    case App.App f1 x1 f2 x2 =>
      simp only [alphaEqAux, Bool.and_eq_true] at h
      rw [lowerTotalExpr_app, lowerTotalExpr_app,
        alphaEqAux_lowerTotalExpr_eq hR h.1, alphaEqAux_lowerTotalExpr_eq hR h.2]
    case Force.Force e1 e2 =>
      simp only [alphaEqAux] at h
      rw [lowerTotalExpr_force, lowerTotalExpr_force, alphaEqAux_lowerTotalExpr_eq hR h]
    case Delay.Delay e1 e2 =>
      simp only [alphaEqAux] at h
      rw [lowerTotalExpr_delay, lowerTotalExpr_delay, alphaEqAux_lowerTotalExpr_eq hR h]
    case Constr.Constr t1 args1 t2 args2 =>
      simp only [alphaEqAux, Bool.and_eq_true, beq_iff_eq] at h
      rw [lowerTotalExpr_constr_of_list, lowerTotalExpr_constr_of_list, h.1,
        alphaEqAuxList_lowerTotalExprList_eq hR h.2]
    case Case.Case s1 alts1 s2 alts2 =>
      simp only [alphaEqAux, Bool.and_eq_true] at h
      rw [lowerTotalExpr_case_of_list, lowerTotalExpr_case_of_list,
        alphaEqAux_lowerTotalExpr_eq hR h.1, alphaEqAuxList_lowerTotalExprList_eq hR h.2]
    case Let.Let binds1 body1 binds2 body2 =>
      simp only [alphaEqAux] at h
      exact alphaEqLet_lowerTotalExpr_eq hR h
  termination_by sizeOf a

  theorem alphaEqAuxList_lowerTotalExprList_eq {A1 A2 L1 L2 : List VarId}
      (hR : VarRel A1 A2 L1 L2) {as bs : List Expr}
      (h : alphaEqAuxList A1 A2 as bs = true) :
      lowerTotalExprList L1 as = lowerTotalExprList L2 bs := by
    cases as <;> cases bs <;> simp only [alphaEqAuxList, Bool.false_eq_true] at h
    case nil.nil => rw [lowerTotalExprList_nil, lowerTotalExprList_nil]
    case cons.cons a as b bs =>
      simp only [Bool.and_eq_true] at h
      rw [lowerTotalExprList_cons, lowerTotalExprList_cons,
        alphaEqAux_lowerTotalExpr_eq hR h.1, alphaEqAuxList_lowerTotalExprList_eq hR h.2]
  termination_by sizeOf as

  theorem alphaEqLet_lowerTotalExpr_eq {A1 A2 L1 L2 : List VarId}
      (hR : VarRel A1 A2 L1 L2) {binds1 binds2 : List (VarId × Expr × Bool)}
      {body1 body2 : Expr} (h : alphaEqLet A1 A2 binds1 binds2 body1 body2 = true) :
      lowerTotalExpr L1 (.Let binds1 body1) = lowerTotalExpr L2 (.Let binds2 body2) := by
    match binds1, binds2, h with
    | [], [], h =>
      simp only [alphaEqLet] at h
      rw [lowerTotalExpr_let_nil_eq, lowerTotalExpr_let_nil_eq]
      exact alphaEqAux_lowerTotalExpr_eq hR h
    | (x, rhs1, er1) :: rest1, (y, rhs2, er2) :: rest2, h =>
      simp only [alphaEqLet, Bool.and_eq_true] at h
      rw [lowerTotalExpr_let_cons_eq, lowerTotalExpr_let_cons_eq,
        alphaEqAux_lowerTotalExpr_eq hR h.1,
        alphaEqLet_lowerTotalExpr_eq (hR.cons x y) h.2]
    | [], _ :: _, h | _ :: _, [], h =>
      simp only [alphaEqLet, Bool.false_eq_true] at h
  termination_by sizeOf binds1 + sizeOf body1
end

theorem alphaEq_lowerTotalExpr_eq {a b : Expr} (h : alphaEq a b = true) (env : List VarId) :
    lowerTotalExpr env a = lowerTotalExpr env b :=
  alphaEqAux_lowerTotalExpr_eq (VarRel.nil env) h

theorem alphaEq_mirCtxRefines {a b : Expr} (h : alphaEq a b = true) : MIRCtxRefines a b :=
  mirCtxRefines_of_lowerEq (fun env => alphaEq_lowerTotalExpr_eq h env)

end Moist.Verified.MIR
