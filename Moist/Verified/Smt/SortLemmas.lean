import Moist.Verified.Smt.EvalLemmas

/-! # Stage 2b — well-sortedness reduction lemmas (Layer B)

With `vConName`/`VL.sIsNil`/`DL.sIsNil` made arity-faithful in `Symbolic/Value.lean`
(matched per-constructor at the correct arity), the type-discriminators evaluate to the
*actual* constructor head of the value — no well-sortedness invariant needed:

* `vConName_eval` : `vConName e = some c → (evalDyn M e).toV.conName = c`;
* `sIsCon_*` : the six type-guards (`gInt`/`gBool`/`gBS`/`gStr`/`gData`/`gUnit` use these);
* `VL.sIsNil`/`DL.sIsNil` evaluate to the semantic `isNil`.
-/

namespace Moist.Verified.Smt

open Moist.Symbolic

/-! ## Atom reductions -/

@[simp] theorem evalDyn_atom (M : Model) (a : String) : evalDyn M (.atom a) = evalAtom M a := rfl
@[simp] theorem evalAtom_VUnit (M : Model) : evalAtom M "VUnit" = .v .unit := rfl
@[simp] theorem evalAtom_vnil (M : Model) : evalAtom M "vnil" = .vl .nil := rfl
@[simp] theorem evalAtom_dnil (M : Model) : evalAtom M "dnil" = .dl .nil := rfl
@[simp] theorem evalAtom_mnil (M : Model) : evalAtom M "mnil" = .dm .nil := rfl

/-! ## `vConName` is faithful to evaluation -/

theorem vConName_eval (M : Model) {e : SExpr} {c : String} (h : V.vConName e = some c) :
    (evalDyn M e).toV.conName = c := by
  unfold V.vConName at h
  split at h
  all_goals first
    | (rw [Option.some.injEq] at h; subst h; rfl)
    | (exact absurd h (by simp))

/-! ## Type discriminators (`sIsCon`) — used by the builtin type-guards -/

@[simp] theorem sIsCon_VInt (M : Model) (e : SExpr) :
    (evalDyn M (V.sIsCon "VInt" e)).toBool = ((evalDyn M e).toV.conName == "VInt") := by
  unfold V.sIsCon; split
  · next c hvc => rw [vConName_eval M hvc]; simp
  · show (evalDyn M (.app "is-VInt" [e])).toBool = _; simp

@[simp] theorem sIsCon_VBool (M : Model) (e : SExpr) :
    (evalDyn M (V.sIsCon "VBool" e)).toBool = ((evalDyn M e).toV.conName == "VBool") := by
  unfold V.sIsCon; split
  · next c hvc => rw [vConName_eval M hvc]; simp
  · show (evalDyn M (.app "is-VBool" [e])).toBool = _; simp

@[simp] theorem sIsCon_VBS (M : Model) (e : SExpr) :
    (evalDyn M (V.sIsCon "VBS" e)).toBool = ((evalDyn M e).toV.conName == "VBS") := by
  unfold V.sIsCon; split
  · next c hvc => rw [vConName_eval M hvc]; simp
  · show (evalDyn M (.app "is-VBS" [e])).toBool = _; simp

@[simp] theorem sIsCon_VStr (M : Model) (e : SExpr) :
    (evalDyn M (V.sIsCon "VStr" e)).toBool = ((evalDyn M e).toV.conName == "VStr") := by
  unfold V.sIsCon; split
  · next c hvc => rw [vConName_eval M hvc]; simp
  · show (evalDyn M (.app "is-VStr" [e])).toBool = _; simp

@[simp] theorem sIsCon_VData (M : Model) (e : SExpr) :
    (evalDyn M (V.sIsCon "VData" e)).toBool = ((evalDyn M e).toV.conName == "VData") := by
  unfold V.sIsCon; split
  · next c hvc => rw [vConName_eval M hvc]; simp
  · show (evalDyn M (.app "is-VData" [e])).toBool = _; simp

@[simp] theorem sIsCon_VUnit (M : Model) (e : SExpr) :
    (evalDyn M (V.sIsCon "VUnit" e)).toBool = ((evalDyn M e).toV.conName == "VUnit") := by
  unfold V.sIsCon; split
  · next c hvc => rw [vConName_eval M hvc]; simp
  · show (evalDyn M (.app "is-VUnit" [e])).toBool = _; simp

/-! ## List emptiness discriminators -/

@[simp] theorem evalDyn_vlSIsNil (M : Model) (e : SExpr) :
    (evalDyn M (VL.sIsNil e)).toBool = (evalDyn M e).toVL.isNil := by
  unfold VL.sIsNil; split <;> simp_all [VL.isNil, SemVL.isNil]

@[simp] theorem evalDyn_dlSIsNil (M : Model) (e : SExpr) :
    (evalDyn M (DL.sIsNil e)).toBool = (evalDyn M e).toDL.isNil := by
  unfold DL.sIsNil; split <;> simp_all [DL.isNil, SemDL.isNil]

end Moist.Verified.Smt
