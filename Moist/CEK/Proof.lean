import Moist.MIR.Semantics
import Moist.Plutus.DecidableEq

namespace Moist.CEK.Proof

open Moist.CEK
open Moist.Plutus.Term
open Moist.MIR
open Moist.MIR.Semantics

/-! # Proof: `BehEqClosed mirLhs mirRhs`

`mirLhs = \x -> let foo = 1+2 in 10`
`mirRhs = \x -> 10`

No sorry. Lowering verified by `native_decide`.
CEK stepping verified by `rfl` on each transition.
-/

private def x : VarId := ⟨1, "x"⟩
private def foo : VarId := ⟨2, "foo"⟩
private abbrev intLit (i : Int) : Expr :=
  .Lit (.Integer i, .AtomicType .TypeInteger)

def mirLhs : Expr :=
  .Lam x (.Let [(foo, .App (.App (.Builtin .AddInteger) (intLit 1)) (intLit 2), false)]
           (intLit 10))

def mirRhs : Expr := .Lam x (intLit 10)

private abbrev C (i : Int) : Term := .Constant (.Integer i, .AtomicType .TypeInteger)
private def lhsBody : Term := .Apply (.Lam 0 (C 10)) (.Apply (.Apply (.Builtin .AddInteger) (C 1)) (C 2))
private def rhsBody : Term := C 10

/-! ## Lowering correctness — proved by native_decide -/

theorem lower_lhs : lowerTotal [] mirLhs = some (.Lam 0 lhsBody) := by native_decide
theorem lower_rhs : lowerTotal [] mirRhs = some (.Lam 0 rhsBody) := by native_decide

/-! ## CEK stepping: lhsBody reaches VCon 10 in 15 steps -/

private abbrev E (a : CekValue) := CekEnv.cons a .nil
private abbrev addE := Term.Apply (.Apply (.Builtin .AddInteger) (C 1)) (C 2)

private abbrev lhs0 (a : CekValue) := State.compute [] (E a) lhsBody
private abbrev lhs1 (a : CekValue) := State.compute [.arg addE (E a)] (E a) (.Lam 0 (C 10))
private abbrev lhs2 (a : CekValue) := State.ret [.arg addE (E a)] (.VLam (C 10) (E a))
private abbrev lhs3 (a : CekValue) := State.compute [.funV (.VLam (C 10) (E a))] (E a) addE
private abbrev lhs4 (a : CekValue) := State.compute [.arg (C 2) (E a), .funV (.VLam (C 10) (E a))] (E a) (.Apply (.Builtin .AddInteger) (C 1))
private abbrev lhs5 (a : CekValue) := State.compute [.arg (C 1) (E a), .arg (C 2) (E a), .funV (.VLam (C 10) (E a))] (E a) (.Builtin .AddInteger)
private abbrev lhs6 (a : CekValue) := State.ret [.arg (C 1) (E a), .arg (C 2) (E a), .funV (.VLam (C 10) (E a))] (.VBuiltin .AddInteger [] (.more .argV (.one .argV)))
private abbrev lhs7 (a : CekValue) := State.compute [.funV (.VBuiltin .AddInteger [] (.more .argV (.one .argV))), .arg (C 2) (E a), .funV (.VLam (C 10) (E a))] (E a) (C 1)
private abbrev lhs8 (a : CekValue) := State.ret [.funV (.VBuiltin .AddInteger [] (.more .argV (.one .argV))), .arg (C 2) (E a), .funV (.VLam (C 10) (E a))] (.VCon (.Integer 1))
private abbrev lhs9 (a : CekValue) := State.ret [.arg (C 2) (E a), .funV (.VLam (C 10) (E a))] (.VBuiltin .AddInteger [.VCon (.Integer 1)] (.one .argV))
private abbrev lhs10 (a : CekValue) := State.compute [.funV (.VBuiltin .AddInteger [.VCon (.Integer 1)] (.one .argV)), .funV (.VLam (C 10) (E a))] (E a) (C 2)
private abbrev lhs11 (a : CekValue) := State.ret [.funV (.VBuiltin .AddInteger [.VCon (.Integer 1)] (.one .argV)), .funV (.VLam (C 10) (E a))] (.VCon (.Integer 2))
private abbrev lhs12 (a : CekValue) := State.ret [.funV (.VLam (C 10) (E a))] (.VCon (.Integer 3))
private abbrev lhs13 (a : CekValue) := State.compute [] (.cons (.VCon (.Integer 3)) (E a)) (C 10)
private abbrev lhs14 (_ : CekValue) := State.ret [] (.VCon (.Integer 10))
private abbrev lhs15 (_ : CekValue) := State.halt (.VCon (.Integer 10))

private theorem t0  (a) : step (lhs0 a) = lhs1 a := rfl
private theorem t1  (a) : step (lhs1 a) = lhs2 a := rfl
private theorem t2  (a) : step (lhs2 a) = lhs3 a := rfl
private theorem t3  (a) : step (lhs3 a) = lhs4 a := rfl
private theorem t4  (a) : step (lhs4 a) = lhs5 a := rfl
private theorem t5  (a) : step (lhs5 a) = lhs6 a := rfl
private theorem t6  (a) : step (lhs6 a) = lhs7 a := rfl
private theorem t7  (a) : step (lhs7 a) = lhs8 a := rfl
private theorem t8  (a) : step (lhs8 a) = lhs9 a := rfl
private theorem t9  (a) : step (lhs9 a) = lhs10 a := rfl
private theorem t10 (a) : step (lhs10 a) = lhs11 a := rfl
private theorem t11 (a) : step (lhs11 a) = lhs12 a := rfl
private theorem t12 (a) : step (lhs12 a) = lhs13 a := rfl
private theorem t13 (a) : step (lhs13 a) = lhs14 a := rfl
private theorem t14 (a) : step (lhs14 a) = lhs15 a := rfl

theorem lhsBody_halts (a : CekValue) : steps 15 (lhs0 a) = lhs15 a := by
  unfold steps; rw [t0]; unfold steps; rw [t1]; unfold steps; rw [t2]
  unfold steps; rw [t3]; unfold steps; rw [t4]; unfold steps; rw [t5]
  unfold steps; rw [t6]; unfold steps; rw [t7]; unfold steps; rw [t8]
  unfold steps; rw [t9]; unfold steps; rw [t10]; unfold steps; rw [t11]
  unfold steps; rw [t12]; unfold steps; rw [t13]; unfold steps; rw [t14]; rfl

theorem rhsBody_halts (a : CekValue) :
    steps 2 (.compute [] (E a) rhsBody) = .halt (.VCon (.Integer 10)) := rfl

private theorem eval_lam_lhs :
    Reaches (.compute [] .nil (.Lam 0 lhsBody)) (.VLam lhsBody .nil) := ⟨2, rfl⟩
private theorem eval_lam_rhs :
    Reaches (.compute [] .nil (.Lam 0 rhsBody)) (.VLam rhsBody .nil) := ⟨2, rfl⟩

/-! ## Main theorem -/

/-- **`\x -> let foo = 1+2 in 10`  ≡  `\x -> 10`**

Stated as `BehEqClosed mirLhs mirRhs`. No sorry. -/
theorem dead_let_example : BehEqClosed mirLhs mirRhs := by
  unfold BehEqClosed
  rw [lower_lhs, lower_rhs]
  intro k v1 v2 hv1 hv2
  have := reaches_unique hv1 eval_lam_lhs; subst this
  have := reaches_unique hv2 eval_lam_rhs; subst this
  cases k with
  | zero => unfold ValueEq; trivial
  | succ k =>
    unfold ValueEq
    intro arg w1 w2 hw1 hw2
    have := reaches_unique hw1 ⟨15, lhsBody_halts arg⟩; subst this
    have := reaches_unique hw2 ⟨2, rhsBody_halts arg⟩; subst this
    cases k with
    | zero => unfold ValueEq; trivial
    | succ _ => unfold ValueEq; rfl

end Moist.CEK.Proof
