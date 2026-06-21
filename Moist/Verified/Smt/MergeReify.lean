import Moist.Verified.Smt.SortLemmas
import Moist.Verified.Smt.Denote

/-! # Stage 2 — `mergeVal` / `symMerge` / `reifyFO` denotation lemmas (Layer C-prep)

How the symbolic merge (`choice` distribution) and the first-order reification denote:
`mergeVal`/`symMerge` are model `ite`s, and `reifyFO v` (when its non-first-order flag is
false) decodes to `denoteSymV M v`. These feed the `Apply`/`Force`/`Case`/builtin cases of
the main simulation. -/

namespace Moist.Verified.Smt

open Moist.Symbolic
open Moist.CEK

/-! ## `mergeVal` / `mergeValList` denote to model `ite` -/

mutual
theorem denoteSymV_mergeVal (M : Model) (c : SExpr) :
    ∀ (x y : SymV), denoteSymV M (mergeVal c x y)
      = if (evalDyn M c).toBool then denoteSymV M x else denoteSymV M y
  | .fo a, .fo b => by
      simp only [mergeVal, denoteSymV, evalDyn_sIte]
      by_cases hc : (evalDyn M c).toBool <;> simp [hc]
  | .constr t1 fs1, .constr t2 fs2 => by
      simp only [mergeVal]
      by_cases hcond : (t1 == t2 && fs1.length == fs2.length) = true
      · rw [if_pos hcond]
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        obtain ⟨ht, hl⟩ := hcond; subst ht
        simp only [denoteSymV]
        rw [denoteSymList_mergeValList M c fs1 fs2 hl]
        by_cases hc : (evalDyn M c).toBool <;> simp [hc]
      · rw [if_neg hcond]; simp only [denoteSymV]
  | .fo _, .lam _ _ | .fo _, .delay _ _ | .fo _, .constr _ _ | .fo _, .builtin _ _ _ | .fo _, .choice _ _ _
  | .lam _ _, _ | .delay _ _, _ | .builtin _ _ _, _ | .choice _ _ _, _
  | .constr _ _, .fo _ | .constr _ _, .lam _ _ | .constr _ _, .delay _ _ | .constr _ _, .builtin _ _ _ | .constr _ _, .choice _ _ _ =>
      by simp only [mergeVal, denoteSymV]
termination_by x _ => sizeOf x
theorem denoteSymList_mergeValList (M : Model) (c : SExpr) :
    ∀ (xs ys : List SymV), xs.length = ys.length →
      denoteSymList M (mergeValList c xs ys)
        = if (evalDyn M c).toBool then denoteSymList M xs else denoteSymList M ys
  | [], [], _ => by simp only [mergeValList, denoteSymList]; by_cases hc : (evalDyn M c).toBool <;> simp [hc]
  | x :: xs, y :: ys, h => by
      simp only [mergeValList, denoteSymList]
      rw [denoteSymV_mergeVal M c x y, denoteSymList_mergeValList M c xs ys (by simpa using h)]
      by_cases hc : (evalDyn M c).toBool <;> simp [hc]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
termination_by xs _ => sizeOf xs
end

/-! ## `symMerge` denotes componentwise -/

theorem denoteInc_symMerge (M : Model) (c : SExpr) (x y : SymR) :
    denoteInc M (symMerge c x y) = if (evalDyn M c).toBool then denoteInc M x else denoteInc M y := by
  simp only [denoteInc, symMerge, evalDyn_sIte]
  by_cases hc : (evalDyn M c).toBool <;> simp [hc]

theorem denoteErr_symMerge (M : Model) (c : SExpr) (x y : SymR) :
    denoteErr M (symMerge c x y) = if (evalDyn M c).toBool then denoteErr M x else denoteErr M y := by
  simp only [denoteErr, symMerge, evalDyn_sIte]
  by_cases hc : (evalDyn M c).toBool <;> simp [hc]

theorem denoteVal_symMerge (M : Model) (c : SExpr) (x y : SymR) :
    denoteVal M (symMerge c x y) = if (evalDyn M c).toBool then denoteVal M x else denoteVal M y := by
  simp only [denoteVal, symMerge]; exact denoteSymV_mergeVal M c x.val y.val

/-! ## `reifyFO` decodes to the value's denotation (when first-order) -/

theorem decodeVL_ofList (M : Model) : ∀ (es : List SExpr),
    decodeVL (evalDyn M (VL.ofList es)).toVL = es.map (fun e => decodeV (evalDyn M e).toV)
  | [] => rfl
  | e :: es => by
      simp only [VL.ofList, VL.cons, evalDyn_app, evalDynList, ea_vcons, toVL_vl, decodeVL,
        List.map, decodeVL_ofList M es]

mutual
/-- When a symbolic value is first-order (`reifyFO`'s flag is `false`), its reified `V`
expression decodes to its denotation. -/
theorem reifyFO_denote (M : Model) : ∀ (v : SymV), ¬(evalDyn M (reifyFO v).1).toBool →
    decodeV (evalDyn M (reifyFO v).2).toV = denoteSymV M v
  | .fo _, _ => rfl
  | .lam _ _, h => by simp [reifyFO] at h
  | .delay _ _, h => by simp [reifyFO] at h
  | .builtin _ _ _, h => by simp [reifyFO] at h
  | .constr t fs, h => by
      simp only [reifyFO] at h ⊢
      simp only [V.constr, evalDyn_app, evalDynList, ea_VConstr, toV_v, Int.toNat_ofNat]
      simp only [decodeV]
      rw [decodeVL_ofList, reifyFOList_denote M fs h]
      simp [denoteSymV, Int.toNat_ofNat]
  | .choice c a b, h => by
      simp only [reifyFO, evalDyn_sIte] at h ⊢
      simp only [denoteSymV]
      by_cases hc : (evalDyn M c).toBool
      · simp only [hc, if_true] at h ⊢
        exact reifyFO_denote M a h
      · simp only [hc, if_false, Bool.false_eq_true] at h ⊢
        exact reifyFO_denote M b h
theorem reifyFOList_denote (M : Model) : ∀ (fs : List SymV), ¬(evalDyn M (reifyFOList fs).1).toBool →
    (reifyFOList fs).2.map (fun e => decodeV (evalDyn M e).toV) = denoteSymList M fs
  | [], _ => rfl
  | v :: vs, h => by
      simp only [reifyFOList, evalDyn_sOr, Bool.not_eq_true, Bool.or_eq_false_iff] at h
      obtain ⟨h1, h2⟩ := h
      show List.map _ ((reifyFO v).2 :: (reifyFOList vs).2) = _
      simp only [List.map, denoteSymList]
      rw [reifyFO_denote M v (by simp [h1]), reifyFOList_denote M vs (by simp [h2])]
end

end Moist.Verified.Smt
