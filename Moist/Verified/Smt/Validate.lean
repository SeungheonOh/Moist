import Moist.Verified.Smt.Denote
import Moist.Verified.Smt.EvalLemmas

/-! # Stage 2 — foundation validation lemmas

Self-contained checks that the encode → `evalDyn` → `decode` pipeline round-trips.
These exercise the full denotation stack (`constToSExpr`/`dataToSExpr` → `evalDyn` →
`Dyn` projection → `decodeV`/`decodeD`) and reduce by definitional unfolding (`rfl`),
confirming the term-model semantics lines up arm-for-arm with the SMT constructors.

They are the first of the Stage-2c per-builtin/per-constant obligations: if any were
false the soundness theorem would be too, so they double as a smoke test of the design.

Still owed (Stage 2c, not provable here without unfolding the CEK builtin monolith /
needing induction on the carrier):
* `smt{Fdiv,Fmod,Qdiv,Qrem}` ≡ the CEK's Haskell floor / truncating div&mod on `b ≠ 0`
  (the zero divisor is guarded into `err`);
* the `ByteString`/`Data`-with-bytes round-trip `bytesToBA ∘ (Seq.ofBytes)= id`
  (induction on the byte list);
* per-builtin agreement `decodeV (symBuiltin b …).val = evalBuiltinConst b …`.
-/

namespace Moist.Verified.Smt

open Moist.Symbolic
open Moist.Plutus.Term (Const)

/-! ## `evalApp` head reductions (each is the first/early match arm, so `rfl`). -/

theorem evalApp_VInt  (d : Dyn) : evalApp "VInt"  [d] = .v (.int d.toInt)  := rfl
theorem evalApp_VBool (d : Dyn) : evalApp "VBool" [d] = .v (.bool d.toBool) := rfl
theorem evalApp_VData (d : Dyn) : evalApp "VData" [d] = .v (.data d.toD)   := rfl
theorem evalApp_eq    (a b : Dyn) : evalApp "=" [a, b] = .b (decide (a = b)) := rfl
theorem evalApp_add   (a b : Dyn) : evalApp "+" [a, b] = .i (a.toInt + b.toInt) := rfl
theorem evalApp_ite_t (t e : Dyn) : evalApp "ite" [.b true, t, e]  = t := rfl
theorem evalApp_ite_f (t e : Dyn) : evalApp "ite" [.b false, t, e] = e := rfl

/-! ## Scalar constant round-trips: `decodeV ∘ evalDyn ∘ constToSExpr = VCon`. -/

theorem eval_const_int (M : Model) (n : Int) :
    decodeV (evalDyn M (constToSExpr (.Integer n))).toV = .VCon (.Integer n) := rfl

theorem eval_const_bool (M : Model) (b : Bool) :
    decodeV (evalDyn M (constToSExpr (.Bool b))).toV = .VCon (.Bool b) := rfl

theorem eval_const_unit (M : Model) :
    decodeV (evalDyn M (constToSExpr .Unit)).toV = .VCon .Unit := rfl

theorem eval_const_str (M : Model) (s : String) :
    decodeV (evalDyn M (constToSExpr (.String s))).toV = .VCon (.String s) := rfl

/-! ## `Data` path round-trips (constructors recurse through `decodeD`). -/

theorem eval_data_I (M : Model) (n : Int) :
    decodeV (evalDyn M (constToSExpr (.Data (.I n)))).toV = .VCon (.Data (.I n)) := rfl

theorem eval_data_constr0 (M : Model) (n : Int) :
    decodeV (evalDyn M (constToSExpr (.Data (.Constr n [])))).toV
      = .VCon (.Data (.Constr n [])) := rfl

/-! ## Equality-of-equal-decodings: structural `Dyn` `=` agrees with `Const` equality
on integers (the `EqualsInteger` value shape). -/

theorem eq_int_decode (x y : Int) :
    (evalApp "=" [Dyn.i x, Dyn.i y]).toBool = (x == y) := by
  by_cases h : x = y <;> simp [evalApp_eq, Dyn.toBool, h]

end Moist.Verified.Smt
