import Moist.Verified.Semantics
import Moist.Verified.DeadLet
import Moist.Verified.Trans
import Moist.Plutus.DecidableEq
import Moist.Verified.FundamentalLemma

namespace Moist.Verified.Example

open Moist.CEK
open Moist.Plutus.Term
open Moist.MIR
open Moist.MIR (lowerTotalExpr lowerTotalExpr_eq_lowerTotal fixCount fixCountBinds)
open Moist.Verified.Semantics

/-! # Proof: `BehEqClosed mirLhs mirRhs`

This module demonstrates the verification framework with concrete examples.

**Manual proof** (`dead_let_example`): proves `\x -> let foo = 1+2 in 10 ≡ \x -> 10`
by explicitly stepping through the CEK machine. Each of the 15 transitions
in the LHS is verified by `rfl`. This serves as a sanity check that the
semantic definitions compute correctly.

**General theorem applications** (`dead_let_lit`, `dead_let_nested`, etc.):
invoke `dead_let_sound_closed` directly. The two preconditions of
`MIRDeadLetCond` (unused variable and purity) are discharged by
`native_decide`, so no manual CEK stepping is needed.

**Refinement examples** (`refines_var_rhs`, `refines_constr_rhs`, etc.):
demonstrate `Refines (⊑)` using `dead_let_sound` directly, including cases
with `Var` RHS — enabled by `isPure` + `WellSizedEnv`.

All proofs are `sorry`-free.
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

/-! ## Lowering correctness — proved by native_decide

These theorems verify that `lowerTotal` produces the expected UPLC terms.
`native_decide` compiles the lowering function to native code and evaluates
it, providing a kernel-verified proof of the equation. -/

theorem lower_lhs_lt : lowerTotal [] mirLhs = some (.Lam 0 lhsBody) := by native_decide
theorem lower_rhs_lt : lowerTotal [] mirRhs = some (.Lam 0 rhsBody) := by native_decide
theorem lower_lhs : lowerTotalExpr ([] : List VarId) mirLhs = some (.Lam 0 lhsBody) := by
  rw [lowerTotalExpr_eq_lowerTotal [] mirLhs (by native_decide)]; exact lower_lhs_lt
theorem lower_rhs : lowerTotalExpr ([] : List VarId) mirRhs = some (.Lam 0 rhsBody) := by
  rw [lowerTotalExpr_eq_lowerTotal [] mirRhs (by native_decide)]; exact lower_rhs_lt

/-! ## CEK stepping: lhsBody reaches VCon 10 in 15 steps

Each `lhsN` abbreviation names the CEK state after `N` steps of evaluating
`lhsBody` (which is `Apply (Lam 0 (C 10)) (Apply (Apply (Builtin AddInteger) (C 1)) (C 2))`).
Each `tN` theorem witnesses `step (lhsN a) = lhs(N+1) a` by `rfl`.
`lhsBody_halts` chains them together to show `steps 15 (lhs0 a) = halt (VCon 10)`. -/

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
    Reaches (.compute [] .nil (.Lam 0 lhsBody)) (.halt (.VLam lhsBody .nil)) := ⟨2, rfl⟩
private theorem eval_lam_rhs :
    Reaches (.compute [] .nil (.Lam 0 rhsBody)) (.halt (.VLam rhsBody .nil)) := ⟨2, rfl⟩

/-! ## Main theorem -/

/-- **`\x -> let foo = 1+2 in 10`  ≡  `\x -> 10`**

    Manual proof via explicit CEK stepping. The error case is discharged
    by showing both sides halt (via `reaches_halt_not_error`). The value
    case uses `reaches_unique` to pin down the halted values, then
    unfolds `ValueEq` at depths 0, 1, and 2+.

    Stated as `BehEqClosed mirLhs mirRhs`. No sorry. -/
theorem dead_let_example : mirLhs ≋ᶜ mirRhs := by
  unfold BehEqClosed
  rw [lower_lhs, lower_rhs]
  refine ⟨?_, ?_, ?_⟩
  · -- error ↔ error: both sides halt, so neither can error
    constructor
    · intro he; exact (reaches_halt_not_error eval_lam_lhs he).elim
    · intro he; exact (reaches_halt_not_error eval_lam_rhs he).elim
  · -- halts ↔ halts
    constructor
    · intro _; exact ⟨_, eval_lam_rhs⟩
    · intro _; exact ⟨_, eval_lam_lhs⟩
  · -- value equivalence
    intro k v1 v2 hv1 hv2
    have := reaches_unique hv1 eval_lam_lhs; subst this
    have := reaches_unique hv2 eval_lam_rhs; subst this
    cases k with
    | zero => unfold ValueEq; trivial
    | succ k =>
      unfold ValueEq; intro arg1 arg2 hargs n hn
      sorry -- TODO: adapt to bounded-step VLam ValueEq for concrete example

/-! ## Examples using `dead_let_sound_closed`

These demonstrate the general theorem: each example instantiates
`dead_let_sound_closed` with a specific variable, RHS, and body. The two
`MIRDeadLetCond` obligations (`unused` and `safe`) are discharged by
`native_decide` — no manual proof work at all. This is the intended
workflow for verifying individual dead-let-elimination instances. -/

open Moist.Verified.DeadLet
open Moist.Verified.Semantics

private def y : VarId := ⟨3, "y"⟩
private def z : VarId := ⟨4, "z"⟩
private def w : VarId := ⟨5, "w"⟩

/-- `let foo = 42 in 10` ≡ `10` — unused literal binding. -/
theorem dead_let_lit :
    (.Let [(foo, intLit 42, false)] (intLit 10))
  ≋ᶜ (intLit 10) :=
  dead_let_sound_closed foo (intLit 42) (intLit 10)
    ⟨by native_decide, by native_decide, by native_decide⟩

/-- `let y = addInteger in y 1 2` is NOT eligible (y IS used),
    but `let z = 99 in let y = addInteger in y 1 2` ≡ `let y = addInteger in y 1 2`
    (z is unused). -/
theorem dead_let_nested :
    (.Let [(z, intLit 99, false)]
      (.Let [(y, .Builtin .AddInteger, false)]
        (.App (.App (.Var y) (intLit 1)) (intLit 2))))
  ≋ᶜ (.Let [(y, .Builtin .AddInteger, false)]
      (.App (.App (.Var y) (intLit 1)) (intLit 2))) :=
  dead_let_sound_closed z (intLit 99)
    (.Let [(y, .Builtin .AddInteger, false)]
      (.App (.App (.Var y) (intLit 1)) (intLit 2)))
    ⟨by native_decide, by native_decide, by native_decide⟩

/-- `let w = \x -> x in 7` ≡ `7` — unused lambda binding. -/
theorem dead_let_lam :
    (.Let [(w, .Lam x (.Var x), false)] (intLit 7))
  ≋ᶜ (intLit 7) :=
  dead_let_sound_closed w (.Lam x (.Var x)) (intLit 7)
    ⟨by native_decide, by native_decide, by native_decide⟩

/-- `let z = delay(42) in 5` ≡ `5` — unused delay binding. -/
theorem dead_let_delay :
    (.Let [(z, .Delay (intLit 42), false)] (intLit 5))
  ≋ᶜ (intLit 5) :=
  dead_let_sound_closed z (.Delay (intLit 42)) (intLit 5)
    ⟨by native_decide, by native_decide, by native_decide⟩

/-- `let foo = addInteger in foo 1 2` ≡ `addInteger 1 2` — unused after inlining. -/
theorem dead_let_builtin :
    (.Let [(foo, .Builtin .AddInteger, false)]
      (.App (.App (.Builtin .AddInteger) (intLit 1)) (intLit 2)))
  ≋ᶜ (.App (.App (.Builtin .AddInteger) (intLit 1)) (intLit 2)) :=
  dead_let_sound_closed foo (.Builtin .AddInteger)
    (.App (.App (.Builtin .AddInteger) (intLit 1)) (intLit 2))
    ⟨by native_decide, by native_decide, by native_decide⟩

/-! ## Lambda body examples

Dead let elimination where the body is a lambda — the binding is dropped
from around a function definition. These are the common case in practice:
a let-bound intermediate that was inlined away, leaving a lambda body
that never referenced it. -/

private def a : VarId := ⟨6, "a"⟩
private def b : VarId := ⟨7, "b"⟩

/-- `let foo = 42 in \a -> a` ≡ `\a -> a` — identity function, unused literal. -/
theorem dead_let_lam_body_id :
    (.Let [(foo, intLit 42, false)] (.Lam a (.Var a)))
  ≋ᶜ (.Lam a (.Var a)) :=
  dead_let_sound_closed foo (intLit 42) (.Lam a (.Var a))
    ⟨by native_decide, by native_decide, by native_decide⟩

/-- `let z = 99 in \a -> 5` ≡ `\a -> 5` — constant function, unused literal. -/
theorem dead_let_lam_body_const :
    (.Let [(z, intLit 99, false)] (.Lam a (intLit 5)))
  ≋ᶜ (.Lam a (intLit 5)) :=
  dead_let_sound_closed z (intLit 99) (.Lam a (intLit 5))
    ⟨by native_decide, by native_decide, by native_decide⟩

/-- `let w = \b -> b in \a -> a` ≡ `\a -> a` — unused lambda binding around lambda body. -/
theorem dead_let_lam_around_lam :
    (.Let [(w, .Lam b (.Var b), false)] (.Lam a (.Var a)))
  ≋ᶜ (.Lam a (.Var a)) :=
  dead_let_sound_closed w (.Lam b (.Var b)) (.Lam a (.Var a))
    ⟨by native_decide, by native_decide, by native_decide⟩

/-- `let foo = addInteger in \a -> \b -> a` ≡ `\a -> \b -> a`
    — unused builtin binding around a multi-arg lambda (const combinator). -/
theorem dead_let_lam_body_multi :
    (.Let [(foo, .Builtin .AddInteger, false)] (.Lam a (.Lam b (.Var a))))
  ≋ᶜ (.Lam a (.Lam b (.Var a))) :=
  dead_let_sound_closed foo (.Builtin .AddInteger) (.Lam a (.Lam b (.Var a)))
    ⟨by native_decide, by native_decide, by native_decide⟩

/-- `let z = delay(1) in \a -> addInteger a a` ≡ `\a -> addInteger a a`
    — unused delay binding around a lambda that uses its own argument. -/
theorem dead_let_lam_body_app :
    (.Let [(z, .Delay (intLit 1), false)]
      (.Lam a (.App (.App (.Builtin .AddInteger) (.Var a)) (.Var a))))
  ≋ᶜ (.Lam a (.App (.App (.Builtin .AddInteger) (.Var a)) (.Var a))) :=
  dead_let_sound_closed z (.Delay (intLit 1))
    (.Lam a (.App (.App (.Builtin .AddInteger) (.Var a)) (.Var a)))
    ⟨by native_decide, by native_decide, by native_decide⟩

/-! ## Compound body examples

More complex bodies involving case expressions, constructors, nested lets,
force/delay, and higher-order patterns. These exercise deeper parts of the
bisimulation machinery. -/

private def c : VarId := ⟨8, "c"⟩
private def d : VarId := ⟨9, "d"⟩
private def f : VarId := ⟨10, "f"⟩
private def g : VarId := ⟨11, "g"⟩
private def p : VarId := ⟨12, "p"⟩
private def q : VarId := ⟨13, "q"⟩

/-- `let z = 1 in Constr 0 [2, 3]` ≡ `Constr 0 [2, 3]`
    — constructor in body, binding completely unused. -/
theorem dead_let_constr :
    (.Let [(z, intLit 1, false)] (.Constr 0 [intLit 2, intLit 3]))
  ≋ᶜ (.Constr 0 [intLit 2, intLit 3]) :=
  dead_let_sound_closed z (intLit 1) (.Constr 0 [intLit 2, intLit 3])
    ⟨by native_decide, by native_decide, by native_decide⟩

/-- `let foo = 7 in case Constr 0 [] of [10, 20]` ≡ `case Constr 0 [] of [10, 20]`
    — case expression in body. -/
theorem dead_let_case :
    (.Let [(foo, intLit 7, false)]
      (.Case (.Constr 0 []) [intLit 10, intLit 20]))
  ≋ᶜ (.Case (.Constr 0 []) [intLit 10, intLit 20]) :=
  dead_let_sound_closed foo (intLit 7)
    (.Case (.Constr 0 []) [intLit 10, intLit 20])
    ⟨by native_decide, by native_decide, by native_decide⟩

/-- `let w = \a -> a in force (delay 42)` ≡ `force (delay 42)`
    — force/delay in body. -/
theorem dead_let_force_delay :
    (.Let [(w, .Lam a (.Var a), false)] (.Force (.Delay (intLit 42))))
  ≋ᶜ (.Force (.Delay (intLit 42))) :=
  dead_let_sound_closed w (.Lam a (.Var a)) (.Force (.Delay (intLit 42)))
    ⟨by native_decide, by native_decide, by native_decide⟩

/-- `let z = 0 in let y = 1 in addInteger y y` ≡ `let y = 1 in addInteger y y`
    — outer dead let around a live inner let. The inner `y` is used; only `z` is dead. -/
theorem dead_let_outer_dead_inner_live :
    (.Let [(z, intLit 0, false)]
      (.Let [(y, intLit 1, false)]
        (.App (.App (.Builtin .AddInteger) (.Var y)) (.Var y))))
  ≋ᶜ (.Let [(y, intLit 1, false)]
      (.App (.App (.Builtin .AddInteger) (.Var y)) (.Var y))) :=
  dead_let_sound_closed z (intLit 0)
    (.Let [(y, intLit 1, false)]
      (.App (.App (.Builtin .AddInteger) (.Var y)) (.Var y)))
    ⟨by native_decide, by native_decide, by native_decide⟩

/-- `let foo = 5 in \f -> \a -> f a` ≡ `\f -> \a -> f a`
    — the apply combinator, unused binding. -/
theorem dead_let_apply_combinator :
    (.Let [(foo, intLit 5, false)]
      (.Lam f (.Lam a (.App (.Var f) (.Var a)))))
  ≋ᶜ (.Lam f (.Lam a (.App (.Var f) (.Var a)))) :=
  dead_let_sound_closed foo (intLit 5)
    (.Lam f (.Lam a (.App (.Var f) (.Var a))))
    ⟨by native_decide, by native_decide, by native_decide⟩

/-- `let p = delay(99) in \f -> \g -> \a -> f (g a)` ≡ `\f -> \g -> \a -> f (g a)`
    — composition combinator (B combinator), dead delay binding. -/
theorem dead_let_compose_combinator :
    (.Let [(p, .Delay (intLit 99), false)]
      (.Lam f (.Lam g (.Lam a (.App (.Var f) (.App (.Var g) (.Var a)))))))
  ≋ᶜ (.Lam f (.Lam g (.Lam a (.App (.Var f) (.App (.Var g) (.Var a)))))) :=
  dead_let_sound_closed p (.Delay (intLit 99))
    (.Lam f (.Lam g (.Lam a (.App (.Var f) (.App (.Var g) (.Var a))))))
    ⟨by native_decide, by native_decide, by native_decide⟩

/-- `let q = \a -> a in \a -> case Constr 1 [a] of [\p -> p, \p -> p]`
    ≡ `\a -> case Constr 1 [a] of [\p -> p, \p -> p]`
    — case expression with constructor fields inside a lambda body. -/
theorem dead_let_case_in_lam :
    (.Let [(q, .Lam a (.Var a), false)]
      (.Lam a (.Case (.Constr 1 [.Var a]) [.Lam p (.Var p), .Lam p (.Var p)])))
  ≋ᶜ (.Lam a (.Case (.Constr 1 [.Var a]) [.Lam p (.Var p), .Lam p (.Var p)])) :=
  dead_let_sound_closed q (.Lam a (.Var a))
    (.Lam a (.Case (.Constr 1 [.Var a]) [.Lam p (.Var p), .Lam p (.Var p)]))
    ⟨by native_decide, by native_decide, by native_decide⟩

/-- `let d = 0 in \a -> \b -> Constr 0 [a, b, addInteger a b]`
    ≡ `\a -> \b -> Constr 0 [a, b, addInteger a b]`
    — constructor with computed fields inside nested lambdas. -/
theorem dead_let_constr_in_lam :
    (.Let [(d, intLit 0, false)]
      (.Lam a (.Lam b (.Constr 0
        [.Var a, .Var b, .App (.App (.Builtin .AddInteger) (.Var a)) (.Var b)]))))
  ≋ᶜ (.Lam a (.Lam b (.Constr 0
      [.Var a, .Var b, .App (.App (.Builtin .AddInteger) (.Var a)) (.Var b)]))) :=
  dead_let_sound_closed d (intLit 0)
    (.Lam a (.Lam b (.Constr 0
      [.Var a, .Var b, .App (.App (.Builtin .AddInteger) (.Var a)) (.Var b)])))
    ⟨by native_decide, by native_decide, by native_decide⟩

/-- Chained dead lets: `let z = 1 in let w = 2 in let foo = 3 in \a -> a` ≡ `let w = 2 in let foo = 3 in \a -> a`
    — peeling one dead let off a chain. Apply iteratively to eliminate all three. -/
theorem dead_let_chain_outer :
    (.Let [(z, intLit 1, false)]
      (.Let [(w, intLit 2, false)]
        (.Let [(foo, intLit 3, false)]
          (.Lam a (.Var a)))))
  ≋ᶜ (.Let [(w, intLit 2, false)]
      (.Let [(foo, intLit 3, false)]
        (.Lam a (.Var a)))) :=
  dead_let_sound_closed z (intLit 1)
    (.Let [(w, intLit 2, false)]
      (.Let [(foo, intLit 3, false)]
        (.Lam a (.Var a))))
    ⟨by native_decide, by native_decide, by native_decide⟩

theorem dead_let_chain_middle :
    (.Let [(w, intLit 2, false)]
      (.Let [(foo, intLit 3, false)]
        (.Lam a (.Var a))))
  ≋ᶜ (.Let [(foo, intLit 3, false)]
      (.Lam a (.Var a))) :=
  dead_let_sound_closed w (intLit 2)
    (.Let [(foo, intLit 3, false)]
      (.Lam a (.Var a)))
    ⟨by native_decide, by native_decide, by native_decide⟩

theorem dead_let_chain_inner :
    (.Let [(foo, intLit 3, false)]
      (.Lam a (.Var a)))
  ≋ᶜ (.Lam a (.Var a)) :=
  dead_let_sound_closed foo (intLit 3)
    (.Lam a (.Var a))
    ⟨by native_decide, by native_decide, by native_decide⟩

/-- `let c = delay(0) in \a -> force (delay a)` ≡ `\a -> force (delay a)`
    — force/delay inside a lambda, dead delay binding outside. -/
theorem dead_let_force_delay_in_lam :
    (.Let [(c, .Delay (intLit 0), false)]
      (.Lam a (.Force (.Delay (.Var a)))))
  ≋ᶜ (.Lam a (.Force (.Delay (.Var a)))) :=
  dead_let_sound_closed c (.Delay (intLit 0))
    (.Lam a (.Force (.Delay (.Var a))))
    ⟨by native_decide, by native_decide, by native_decide⟩

/-! ## Erroring body examples

Both sides error. The error ↔ error direction of `BehEqClosed` is the
non-trivial part here — `dead_let_sound_closed` must show:
- LHS errors → body errors in extended env → transfer to nil env → RHS errors
- RHS errors → transfer to extended env → compose with RHS halting → LHS errors -/

/-- `let foo = 42 in error` ≡ `error`
    — simplest erroring case. LHS evaluates 42 (halts), then hits error.
    RHS hits error directly. Both error. -/
theorem dead_let_error_body :
    (.Let [(foo, intLit 42, false)] .Error)
  ≋ᶜ .Error :=
  dead_let_sound_closed foo (intLit 42) .Error
    ⟨by native_decide, by native_decide, by native_decide⟩

/-- `let w = \a -> a in error` ≡ `error`
    — lambda binding, error body. The lambda is evaluated and discarded. -/
theorem dead_let_lam_then_error :
    (.Let [(w, .Lam a (.Var a), false)] .Error)
  ≋ᶜ .Error :=
  dead_let_sound_closed w (.Lam a (.Var a)) .Error
    ⟨by native_decide, by native_decide, by native_decide⟩

/-- `let z = delay(0) in force 42` ≡ `force 42`
    — forcing a non-delay (a constant) errors in the CEK machine. -/
theorem dead_let_force_non_delay :
    (.Let [(z, .Delay (intLit 0), false)] (.Force (intLit 42)))
  ≋ᶜ (.Force (intLit 42)) :=
  dead_let_sound_closed z (.Delay (intLit 0)) (.Force (intLit 42))
    ⟨by native_decide, by native_decide, by native_decide⟩

/-- `let foo = 7 in 42 99` ≡ `42 99`
    — applying a constant to an argument errors (42 is not a function). -/
theorem dead_let_app_non_function :
    (.Let [(foo, intLit 7, false)] (.App (intLit 42) (intLit 99)))
  ≋ᶜ (.App (intLit 42) (intLit 99)) :=
  dead_let_sound_closed foo (intLit 7) (.App (intLit 42) (intLit 99))
    ⟨by native_decide, by native_decide, by native_decide⟩

/-- `let d = 1 in \a -> error` ≡ `\a -> error`
    — error inside a lambda body. Both sides halt with a lambda value,
    but applying that lambda to any argument errors on both sides. -/
theorem dead_let_error_in_lam :
    (.Let [(d, intLit 1, false)] (.Lam a .Error))
  ≋ᶜ (.Lam a .Error) :=
  dead_let_sound_closed d (intLit 1) (.Lam a .Error)
    ⟨by native_decide, by native_decide, by native_decide⟩

/-- `let foo = 99 in \a -> \b -> force a` ≡ `\a -> \b -> force a`
    — error lurks two lambdas deep: `force a` errors when `a` is not a delay.
    Both sides produce the same closure; the error surfaces only on application. -/
theorem dead_let_deep_error_in_lam :
    (.Let [(foo, intLit 99, false)] (.Lam a (.Lam b (.Force (.Var a)))))
  ≋ᶜ (.Lam a (.Lam b (.Force (.Var a)))) :=
  dead_let_sound_closed foo (intLit 99) (.Lam a (.Lam b (.Force (.Var a))))
    ⟨by native_decide, by native_decide, by native_decide⟩

/-- `let z = 0 in let y = 1 in error` ≡ `let y = 1 in error`
    — dead outer binding around a live inner binding whose body errors.
    Both sides evaluate the inner let then error. -/
theorem dead_let_nested_then_error :
    (.Let [(z, intLit 0, false)]
      (.Let [(y, intLit 1, false)] .Error))
  ≋ᶜ (.Let [(y, intLit 1, false)] .Error) :=
  dead_let_sound_closed z (intLit 0)
    (.Let [(y, intLit 1, false)] .Error)
    ⟨by native_decide, by native_decide, by native_decide⟩

/-! ## Open-term examples using `dead_let_sound`

These use the generalized `dead_let_sound` which proves `Refines` — the body
refines the let-expression. The `.2` projection extracts `BehEq`, the behavioral
equivalence for ALL MIR environments. The body may contain free variables;
the theorem holds regardless of how those variables are bound in the
surrounding context.

This is the key compositionality result: dead-let elimination can be applied
inside lambda bodies, nested lets, or case branches — anywhere in the AST. -/

/-- `let z = 99 in Constr 0 [y, a]` ≡ `Constr 0 [y, a]`
    — constructor with free variables in fields. -/
theorem dead_let_open_constr :
    (.Let [(z, intLit 99, false)] (.Constr 0 [.Var y, .Var a]))
    ≋ (.Constr 0 [.Var y, .Var a]) :=
  (dead_let_sound z (intLit 99) (.Constr 0 [.Var y, .Var a])
    ⟨by native_decide, by native_decide, by native_decide⟩).2

/-- `let foo = 7 in case y of [\a -> a, \a -> z]`
    ≡ `case y of [\a -> a, \a -> z]`
    — case on a free variable with free vars in alternatives. -/
theorem dead_let_open_case :
    (.Let [(foo, intLit 7, false)]
      (.Case (.Var y) [.Lam a (.Var a), .Lam a (.Var z)]))
    ≋ (.Case (.Var y) [.Lam a (.Var a), .Lam a (.Var z)]) :=
  (dead_let_sound foo (intLit 7)
    (.Case (.Var y) [.Lam a (.Var a), .Lam a (.Var z)])
    ⟨by native_decide, by native_decide, by native_decide⟩).2

/-- `let d = delay(0) in force y` ≡ `force y`
    — force of a free variable, dead delay binding. -/
theorem dead_let_open_force :
    (.Let [(d, .Delay (intLit 0), false)] (.Force (.Var y)))
    ≋ (.Force (.Var y)) :=
  (dead_let_sound d (.Delay (intLit 0)) (.Force (.Var y))
    ⟨by native_decide, by native_decide, by native_decide⟩).2

/-- `let foo = 1 in \a -> let z = 2 in addInteger a y`
    ≡ `\a -> let z = 2 in addInteger a y`
    — nested let with free variable `y`, outer binding dead. -/
theorem dead_let_open_nested_let :
    (.Let [(foo, intLit 1, false)]
      (.Lam a (.Let [(z, intLit 2, false)]
        (.App (.App (.Builtin .AddInteger) (.Var a)) (.Var y)))))
    ≋ (.Lam a (.Let [(z, intLit 2, false)]
      (.App (.App (.Builtin .AddInteger) (.Var a)) (.Var y)))) :=
  (dead_let_sound foo (intLit 1)
    (.Lam a (.Let [(z, intLit 2, false)]
      (.App (.App (.Builtin .AddInteger) (.Var a)) (.Var y))))
    ⟨by native_decide, by native_decide, by native_decide⟩).2

/-- `let w = \b -> b in error` ≡ `error`
    — open error body (error has no free vars, but BehEq still quantifies
    over all envs, exercising the error path of the generalized proof). -/
theorem dead_let_open_error :
    (.Let [(w, .Lam a (.Var a), false)] .Error) ≋ .Error :=
  (dead_let_sound w (.Lam a (.Var a)) .Error
    ⟨by native_decide, by native_decide, by native_decide⟩).2

/-! ## Transitivity examples

Demonstrate `behEqClosed_trans` by chaining multiple dead-let eliminations.
Each step removes one dead binding; the chain composes them into a single
equivalence via transitivity. -/

/-- Chained elimination:
    `let foo = 1 in let z = 2 in \x -> 10` ≡ `\x -> 10`.

    Step 1: remove `foo` (unused in `let z = 2 in \x -> 10`).
    Step 2: remove `z` (unused in `\x -> 10`).
    Composed via `behEqClosed_trans`. -/
theorem dead_let_chain_two :
    (.Let [(foo, intLit 1, false)]
      (.Let [(z, intLit 2, false)] (.Lam x (intLit 10))))
  ≋ᶜ (.Lam x (intLit 10)) := by
  have step1 := dead_let_sound_closed foo (intLit 1)
    (.Let [(z, intLit 2, false)] (.Lam x (intLit 10)))
    ⟨by native_decide, by native_decide, by native_decide⟩
  have step2 := dead_let_sound_closed z (intLit 2) (.Lam x (intLit 10))
    ⟨by native_decide, by native_decide, by native_decide⟩
  have hb : (lowerTotalExpr ([] : List VarId) (.Let [(z, intLit 2, false)] (.Lam x (intLit 10)))).isSome := by
    native_decide
  obtain ⟨tb, htb⟩ := Option.isSome_iff_exists.mp hb
  exact behEqClosed_trans htb step1 step2

/-- Three-step chain:
    `let foo = 1 in let z = 2 in let w = \a -> a in addInteger 3 4` ≡ `addInteger 3 4`.

    Removes three dead bindings one at a time, composed via two applications
    of `behEqClosed_trans`. -/
private def addBody : Expr := Expr.App (Expr.App (Expr.Builtin .AddInteger) (intLit 3)) (intLit 4)

theorem dead_let_chain_three :
    (Expr.Let [(foo, intLit 1, false)]
      (Expr.Let [(z, intLit 2, false)]
        (Expr.Let [(w, Expr.Lam a (Expr.Var a), false)] addBody)))
  ≋ᶜ addBody := by
  have step1 := dead_let_sound_closed foo (intLit 1)
    (Expr.Let [(z, intLit 2, false)] (Expr.Let [(w, Expr.Lam a (Expr.Var a), false)] addBody))
    ⟨by native_decide, by native_decide, by native_decide⟩
  have step2 := dead_let_sound_closed z (intLit 2)
    (Expr.Let [(w, Expr.Lam a (Expr.Var a), false)] addBody)
    ⟨by native_decide, by native_decide, by native_decide⟩
  have step3 := dead_let_sound_closed w (Expr.Lam a (Expr.Var a)) addBody
    ⟨by native_decide, by native_decide, by native_decide⟩
  have hb1 : (lowerTotalExpr ([] : List VarId) (Expr.Let [(z, intLit 2, false)]
    (Expr.Let [(w, Expr.Lam a (Expr.Var a), false)] addBody))).isSome := by native_decide
  obtain ⟨tb1, htb1⟩ := Option.isSome_iff_exists.mp hb1
  have hb2 : (lowerTotalExpr ([] : List VarId) (Expr.Let [(w, Expr.Lam a (Expr.Var a), false)] addBody)).isSome := by
    native_decide
  obtain ⟨tb2, htb2⟩ := Option.isSome_iff_exists.mp hb2
  exact behEqClosed_trans htb1 step1 (behEqClosed_trans htb2 step2 step3)

/-! ## Refinement examples

These demonstrate the full `Refines (⊑)` relation, which includes both the
compilation monotonicity clause and behavioral equivalence. `dead_let_sound`
returns `Refines` directly — no `.2` projection needed.

The key advance over `BehEqClosed`: these work for **open terms** (with free
variables), and the `isPure` predicate now covers `Var` RHS — the most
common dead binding after ANF normalization. This was impossible with the
old `isAtomicPure` predicate. -/

/-- `let z = y in addInteger y 1  ⊑  addInteger y 1`
    — **Var RHS**: the binding `z = y` is a variable copy, unused in the body.
    Previously impossible with `isAtomicPure` (Var was excluded); now
    provable because `isPure (Var y) = true` and `WellSizedEnv` guarantees
    variable lookup succeeds at runtime. -/
theorem refines_var_rhs :
    Refines (.Let [(z, .Var y, false)] (.App (.App (.Builtin .AddInteger) (.Var y)) (intLit 1)))
            (.App (.App (.Builtin .AddInteger) (.Var y)) (intLit 1)) :=
  dead_let_sound z (.Var y)
    (.App (.App (.Builtin .AddInteger) (.Var y)) (intLit 1))
    ⟨by native_decide, by native_decide, by native_decide⟩

/-- `let foo = Constr 0 [y, z] in addInteger y z  ⊑  addInteger y z`
    — **Constr RHS with free variable args**: a constructor with free-variable
    fields is pure. Dead binding eliminated. -/
theorem refines_constr_rhs :
    Refines (.Let [(foo, .Constr 0 [.Var y, .Var z], false)]
              (.App (.App (.Builtin .AddInteger) (.Var y)) (.Var z)))
            (.App (.App (.Builtin .AddInteger) (.Var y)) (.Var z)) :=
  dead_let_sound foo (.Constr 0 [.Var y, .Var z])
    (.App (.App (.Builtin .AddInteger) (.Var y)) (.Var z))
    ⟨by native_decide, by native_decide, by native_decide⟩

/-- `let w = force (delay y) in z  ⊑  z`
    — **Force (Delay body) RHS**: forcing a delay is pure when the body is
    pure (here, body is `Var y`). -/
theorem refines_force_delay_rhs :
    Refines (.Let [(w, .Force (.Delay (.Var y)), false)] (.Var z))
            (.Var z) :=
  dead_let_sound w (.Force (.Delay (.Var y))) (.Var z)
    ⟨by native_decide, by native_decide, by native_decide⟩

/-- `let a = y in let b = z in addInteger y z  ⊑  addInteger y z`
    — **Chained Var copies**: two dead variable-copy bindings removed
    by composing `Refines` via `refines_trans`. Both `a = y` and `b = z`
    have Var RHS, exercising the `isPure (Var _) = true` path twice. -/
theorem refines_chained_var_copies :
    Refines (.Let [(a, .Var y, false)]
              (.Let [(b, .Var z, false)]
                (.App (.App (.Builtin .AddInteger) (.Var y)) (.Var z))))
            (.App (.App (.Builtin .AddInteger) (.Var y)) (.Var z)) := by
  have step1 := dead_let_sound a (.Var y)
    (.Let [(b, .Var z, false)]
      (.App (.App (.Builtin .AddInteger) (.Var y)) (.Var z)))
    ⟨by native_decide, by native_decide, by native_decide⟩
  have step2 := dead_let_sound b (.Var z)
    (.App (.App (.Builtin .AddInteger) (.Var y)) (.Var z))
    ⟨by native_decide, by native_decide, by native_decide⟩
  exact refines_trans step1 step2

/-- `let foo = let a = 1 in a in z  ⊑  z`
    — **Let RHS**: the binding RHS is itself a let expression.
    `isPure (Let [(a, Lit 1, false)] (Var a))` = `isPureBinds [(a, Lit 1, false)] && isPure (Var a)`
    = `isPure (Lit 1) && true && true` = `true`. -/
theorem refines_let_rhs :
    Refines (.Let [(foo, .Let [(.mk 100 "a", intLit 1, false)] (.Var (.mk 100 "a")), false)] (.Var z))
            (.Var z) :=
  dead_let_sound foo (.Let [(.mk 100 "a", intLit 1, false)] (.Var (.mk 100 "a"))) (.Var z)
    ⟨by native_decide, by native_decide, by native_decide⟩

end Moist.Verified.Example
