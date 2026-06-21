import Moist.Verified.Smt.MergeReify

/-! # Stage 2 — builtin-agreement scaffolding (Layer C)

Per-argument bridges between a value's denotation (`CekValue`) and its reified `SemV`
shape, used to prove `evalBuiltin b (denoted args) = SymOut (symSaturate b args)`:

* `nfErr_notVCon` : a non-first-order arg does not decode to a `VCon` (so `extractConsts`
  fails — matching the symbolic `nfErr`);
* `dV_*` : `decodeV` is injective per `Const` constructor (read the `SemV` from the value);
* `denote_*` : from `denoteSymV M v = VCon X` recover `¬nfErr` and the reified `SemV` shape
  (so the symbolic guards/projectors `gInt`/`sAsInt`/… line up with the `Const`).

The per-builtin agreement proofs and the matched-fuel simulation that consume these are
the remaining work (`Simulation.lean`'s three lemmas). -/

namespace Moist.Verified.Smt

open Moist.Symbolic Moist.CEK
open Moist.Plutus (Data)
open Moist.Plutus.Term (Const BuiltinFun)

/-! ## Non-first-order args don't decode to a constant -/

theorem nfErr_notVCon (M : Model) : ∀ (v : SymV), (evalDyn M (reifyFO v).1).toBool = true →
    ∀ c, denoteSymV M v ≠ .VCon c
  | .fo _, h, _ => by simp [reifyFO] at h
  | .lam _ _, _, _ => by simp [denoteSymV]
  | .delay _ _, _, _ => by simp [denoteSymV]
  | .builtin _ _ _, _, _ => by simp [denoteSymV]
  | .constr _ _, _, _ => by simp [denoteSymV]
  | .choice c a b, h, k => by
      simp only [reifyFO, evalDyn_sIte] at h
      simp only [denoteSymV]
      by_cases hc : (evalDyn M c).toBool
      · simp only [hc, if_true] at h ⊢; exact nfErr_notVCon M a h k
      · simp only [hc, if_false, Bool.false_eq_true] at h ⊢; exact nfErr_notVCon M b h k

mutual
theorem reifyFO_wf (M : Model) : ∀ (v : SymV),
    WFSymVal M v → (evalDyn M (reifyFO v).1).toBool = false →
    WFV (evalDyn M (reifyFO v).2).toV
  | .fo e, hwf, _ => WFV_toV_of_WFDyn hwf
  | .lam _ _, _, h => by simp [reifyFO] at h
  | .delay _ _, _, h => by simp [reifyFO] at h
  | .builtin _ _ _, _, h => by simp [reifyFO] at h
  | .constr _ fs, hwf, h => by
      simp only [reifyFO] at h ⊢
      simp only [V.constr, evalDyn_app, evalDynList, ea_VConstr, toV_v, WFV]
      exact reifyFOList_wf M fs hwf h
  | .choice c a b, hwf, h => by
      simp only [reifyFO, evalDyn_sIte] at h ⊢
      simp only [WFSymVal] at hwf
      by_cases hc : (evalDyn M c).toBool
      · simp only [hc, if_true] at h hwf ⊢
        exact reifyFO_wf M a hwf h
      · simp only [hc, if_false] at h hwf ⊢
        exact reifyFO_wf M b hwf h
theorem reifyFOList_wf (M : Model) : ∀ (vs : List SymV),
    WFSymList M vs → (evalDyn M (reifyFOList vs).1).toBool = false →
    WFVL (evalDyn M (VL.ofList (reifyFOList vs).2)).toVL
  | [], _, _ => by
      change WFVL SemVL.nil
      trivial
  | v :: vs, hwf, h => by
      simp only [WFSymList] at hwf
      simp only [reifyFOList, evalDyn_sOr, Bool.or_eq_false_iff] at h
      change WFV (evalDyn M (reifyFO v).2).toV ∧
        WFVL (evalDyn M (VL.ofList (reifyFOList vs).2)).toVL
      exact ⟨reifyFO_wf M v hwf.1 h.1, reifyFOList_wf M vs hwf.2 h.2⟩
end

mutual
theorem reifyFO_val_wf (M : Model) : ∀ (v : SymV),
    WFSymVal M v → WFV (evalDyn M (reifyFO v).2).toV
  | .fo e, hwf => WFV_toV_of_WFDyn hwf
  | .lam _ _, _ => by simp [reifyFO, V.unit, WFV]
  | .delay _ _, _ => by simp [reifyFO, V.unit, WFV]
  | .builtin _ _ _, _ => by simp [reifyFO, V.unit, WFV]
  | .constr _ fs, hwf => by
      simp only [reifyFO]
      simp only [V.constr, evalDyn_app, evalDynList, ea_VConstr, toV_v, WFV]
      exact reifyFOList_val_wf M fs hwf
  | .choice c a b, hwf => by
      simp only [reifyFO, evalDyn_sIte]
      simp only [WFSymVal] at hwf
      by_cases hc : (evalDyn M c).toBool
      · simp only [hc, if_true] at hwf ⊢
        exact reifyFO_val_wf M a hwf
      · simp only [hc, if_false] at hwf ⊢
        exact reifyFO_val_wf M b hwf
theorem reifyFOList_val_wf (M : Model) : ∀ (vs : List SymV),
    WFSymList M vs → WFVL (evalDyn M (VL.ofList (reifyFOList vs).2)).toVL
  | [], _ => by
      change WFVL SemVL.nil
      trivial
  | v :: vs, hwf => by
      simp only [WFSymList] at hwf
      change WFV (evalDyn M (reifyFO v).2).toV ∧
        WFVL (evalDyn M (VL.ofList (reifyFOList vs).2)).toVL
      exact ⟨reifyFO_val_wf M v hwf.1, reifyFOList_val_wf M vs hwf.2⟩
end

theorem constSem_of_wfv_not_constr (sv : SemV) (hwf : WFV sv)
    (hcon : sv.conName ≠ "VConstr") : ConstSemV sv := by
  cases sv <;> simp [WFV, ConstSemV, SemV.conName] at hwf hcon ⊢
  · exact hwf.2
  · exact ⟨hwf.2.2.1, hwf.2.2.2⟩
  · exact hwf.2

/-! ## `decodeV` is injective per `Const` constructor -/

theorem dV_int (sv : SemV) (n : Int) : decodeV sv = .VCon (.Integer n) ↔ sv = .int n := by
  cases sv <;> simp [decodeV]
theorem dV_bool (sv : SemV) (b : Bool) : decodeV sv = .VCon (.Bool b) ↔ sv = .bool b := by
  cases sv <;> simp [decodeV]
theorem dV_unit (sv : SemV) : decodeV sv = .VCon .Unit ↔ sv = .unit := by
  cases sv <;> simp [decodeV]
theorem dV_str (sv : SemV) (s : String) : decodeV sv = .VCon (.String s) ↔ sv = .str s := by
  cases sv <;> simp [decodeV]
theorem dV_bs (sv : SemV) (ba : ByteArray) :
    decodeV sv = .VCon (.ByteString ba) ↔ ∃ s, sv = .bs s ∧ bytesToBA s = ba := by
  cases sv <;> simp [decodeV]
theorem dV_data (sv : SemV) (d : Data) :
    decodeV sv = .VCon (.Data d) ↔ ∃ d', sv = .data d' ∧ decodeD d' = d := by
  cases sv <;> simp [decodeV]

/-! ## From `denoteSymV M v = VCon X` to the reified `SemV` shape -/

theorem denote_int (M : Model) (v : SymV) (n : Int) (h : denoteSymV M v = .VCon (.Integer n)) :
    (evalDyn M (reifyFO v).1).toBool = false ∧ (evalDyn M (reifyFO v).2).toV = .int n := by
  by_cases hnf : (evalDyn M (reifyFO v).1).toBool
  · exact absurd h (nfErr_notVCon M v hnf _)
  · exact ⟨by simpa using hnf, (dV_int _ n).mp (by rw [reifyFO_denote M v (by simp [hnf]), h])⟩

theorem denote_bool (M : Model) (v : SymV) (b : Bool) (h : denoteSymV M v = .VCon (.Bool b)) :
    (evalDyn M (reifyFO v).1).toBool = false ∧ (evalDyn M (reifyFO v).2).toV = .bool b := by
  by_cases hnf : (evalDyn M (reifyFO v).1).toBool
  · exact absurd h (nfErr_notVCon M v hnf _)
  · exact ⟨by simpa using hnf, (dV_bool _ b).mp (by rw [reifyFO_denote M v (by simp [hnf]), h])⟩

theorem denote_unit (M : Model) (v : SymV) (h : denoteSymV M v = .VCon .Unit) :
    (evalDyn M (reifyFO v).1).toBool = false ∧ (evalDyn M (reifyFO v).2).toV = .unit := by
  by_cases hnf : (evalDyn M (reifyFO v).1).toBool
  · exact absurd h (nfErr_notVCon M v hnf _)
  · exact ⟨by simpa using hnf, (dV_unit _).mp (by rw [reifyFO_denote M v (by simp [hnf]), h])⟩

theorem denote_str (M : Model) (v : SymV) (s : String) (h : denoteSymV M v = .VCon (.String s)) :
    (evalDyn M (reifyFO v).1).toBool = false ∧ (evalDyn M (reifyFO v).2).toV = .str s := by
  by_cases hnf : (evalDyn M (reifyFO v).1).toBool
  · exact absurd h (nfErr_notVCon M v hnf _)
  · exact ⟨by simpa using hnf, (dV_str _ s).mp (by rw [reifyFO_denote M v (by simp [hnf]), h])⟩

/-! ## `evalBuiltin` characterization via `rfl`

KEY TECHNIQUE: `evalBuiltin`/`evalBuiltinConst` are huge matches that `simp`/`whnf` cannot
unfold (times out — this is why `BigStep` resorted to trusted `@[simp] axiom`s). But the
**kernel** reduces them on *concrete* argument shapes in ms, so a per-builtin
characterization by `cases args <;> rfl` is fast and **axiom-free**. The same holds for the
symbolic `symBuiltin`/`symSaturate` (project `.inc`/`.err`/`.val` and they reduce by `rfl`).
This is the recipe for every precise builtin's agreement lemma. -/

/-- A `SemV` whose `conName` is `"VInt"` is an integer. -/
theorem conName_eq_VInt {sv : SemV} (h : sv.conName = "VInt") : ∃ n, sv = .int n := by
  cases sv <;> simp_all [SemV.conName]

/-- `evalBuiltin .AddInteger` is `some (x+y)` on two integers, `none` otherwise — proven
axiom-free by kernel reduction on the (cased) argument shapes. Template for the other
precise builtins. -/
theorem eb_add_char (v w : CekValue) :
    evalBuiltin .AddInteger [w, v] = match v, w with
      | .VCon (.Integer x), .VCon (.Integer y) => some (.VCon (.Integer (x + y)))
      | _, _ => none := by
  cases v with
  | VCon cv => cases w with
    | VCon cw => cases cv <;> cases cw <;> rfl
    | _ => cases cv <;> rfl
  | _ => cases w <;> rfl

/-! ## The per-argument integer guard bridge

`gInt (reifyFO v).2` (the symbolic "not an integer" guard) denotes to `false` exactly when
`v`'s denotation is a `VCon (Integer _)`. This is the heart of the type-guard correspondence
for every integer builtin (the analogue holds per sort). -/

/-- A reified value evaluating to an integer cannot be non-first-order. -/
theorem sva_int_nfErr (M : Model) : ∀ (v : SymV) (n : Int),
    (evalDyn M (reifyFO v).2).toV = .int n → (evalDyn M (reifyFO v).1).toBool = false
  | .fo _, _, _ => rfl
  | .lam _ _, _, h => by simp [reifyFO, V.unit] at h
  | .delay _ _, _, h => by simp [reifyFO, V.unit] at h
  | .builtin _ _ _, _, h => by simp [reifyFO, V.unit] at h
  | .constr _ _, _, h => by simp [reifyFO, V.constr] at h
  | .choice c a b, n, h => by
      simp only [reifyFO, evalDyn_sIte] at h ⊢
      by_cases hc : (evalDyn M c).toBool
      · simp only [hc, if_true] at h ⊢; exact sva_int_nfErr M a n h
      · simp only [hc, if_false, Bool.false_eq_true] at h ⊢; exact sva_int_nfErr M b n h

theorem gInt_false_iff (M : Model) (v : SymV) :
    (evalDyn M (gInt (reifyFO v).2)).toBool = false ↔ ∃ n, denoteSymV M v = .VCon (.Integer n) := by
  simp only [gInt, evalDyn_sNot, Bool.not_eq_false', sIsCon_VInt, beq_iff_eq]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := conName_eq_VInt h
    exact ⟨n, by rw [← reifyFO_denote M v (by simp [sva_int_nfErr M v n hn]), hn]; rfl⟩
  · rintro ⟨n, hn⟩; rw [(denote_int M v n hn).2]; rfl

/-- A non-first-order arg makes the integer guard fire (so `nfErr` is absorbed by `gInt`). -/
theorem nfErr_imp_gInt (M : Model) (v : SymV) (h : (evalDyn M (reifyFO v).1).toBool = true) :
    (evalDyn M (gInt (reifyFO v).2)).toBool = true := by
  cases hb : (evalDyn M (gInt (reifyFO v).2)).toBool with
  | false =>
    obtain ⟨n, hn⟩ := (gInt_false_iff M v).mp hb
    exact absurd hn (nfErr_notVCon M v h (.Integer n))
  | true => rfl

/-- The integer guard fires on any non-integer-valued arg. -/
theorem gInt_true_of_not_int (M : Model) (v : SymV)
    (h : ∀ n, denoteSymV M v ≠ .VCon (.Integer n)) :
    (evalDyn M (gInt (reifyFO v).2)).toBool = true := by
  cases hb : (evalDyn M (gInt (reifyFO v).2)).toBool with
  | false => obtain ⟨n, hn⟩ := (gInt_false_iff M v).mp hb; exact absurd hn (h n)
  | true => rfl

/-! ## Generic binary integer-guarded builtin agreement

All the binary integer builtins (`Add`/`Sub`/`Mul`/`Equals`/`LessThan`/`LessThanEquals`)
share: `symBuiltin b [a,b'] = foGuard (gInt a ∨ gInt b') (W (op a b'))`, so `symSaturate`'s
err is `(reifyFO-flags) ∨ gInt a ∨ gInt b'`. Given the `evalBuiltin` characterization
(`hchar`) and the value form (`hvalform`), the agreement follows uniformly. -/

theorem binIntGuard_agrees (M : Model) (b : BuiltinFun) (vy vx : SymV) (res : Int → Int → Const)
    (hchar : ∀ (v w : CekValue), evalBuiltin b [w, v] = match v, w with
       | .VCon (.Integer x), .VCon (.Integer y) => some (.VCon (res x y)) | _, _ => none)
    (herrform : (symSaturate b [vy, vx]).err = SExpr.sOr (sOrs [(reifyFO vx).1, (reifyFO vy).1])
       (SExpr.sOr (gInt (reifyFO vx).2) (gInt (reifyFO vy).2)))
    (hvalform : ∀ xi yi, (evalDyn M (reifyFO vx).2).toV = .int xi → (evalDyn M (reifyFO vy).2).toV = .int yi →
       denoteVal M (symSaturate b [vy, vx]) = .VCon (res xi yi)) :
    evalBuiltin b (denoteSymList M [vy, vx])
      = if denoteErr M (symSaturate b [vy, vx]) then none else some (denoteVal M (symSaturate b [vy, vx])) := by
  show evalBuiltin b [denoteSymV M vy, denoteSymV M vx] = _
  by_cases hx : ∃ n, denoteSymV M vx = .VCon (.Integer n)
  · obtain ⟨xi, hx⟩ := hx; obtain ⟨hnfx, hsvax⟩ := denote_int M vx xi hx
    by_cases hy : ∃ n, denoteSymV M vy = .VCon (.Integer n)
    · obtain ⟨yi, hy⟩ := hy; obtain ⟨hnfy, hsvby⟩ := denote_int M vy yi hy
      have hL : evalBuiltin b [denoteSymV M vy, denoteSymV M vx] = some (.VCon (res xi yi)) := by
        rw [hchar, hx, hy]
      have herr : denoteErr M (symSaturate b [vy, vx]) = false := by
        simp only [denoteErr, herrform, evalDyn_sOr, evalDyn_sOrs, hnfx, hnfy,
          (gInt_false_iff M vx).mpr ⟨xi, hx⟩, (gInt_false_iff M vy).mpr ⟨yi, hy⟩, Bool.or_self,
          Bool.or_false, List.foldr]
      rw [hL, herr, hvalform xi yi hsvax hsvby]; rfl
    · have hy' : ∀ n, denoteSymV M vy ≠ .VCon (.Integer n) := fun n h => hy ⟨n, h⟩
      have herr : denoteErr M (symSaturate b [vy, vx]) = true := by
        simp only [denoteErr, herrform, evalDyn_sOr, gInt_true_of_not_int M vy hy', Bool.or_true]
      rw [herr]; simp only [if_true, hchar, hx]
      cases hvy : denoteSymV M vy with
      | VCon cw => cases cw <;> first | rfl | exact absurd hvy (hy' _)
      | _ => rfl
  · have hx' : ∀ n, denoteSymV M vx ≠ .VCon (.Integer n) := fun n h => hx ⟨n, h⟩
    have herr : denoteErr M (symSaturate b [vy, vx]) = true := by
      simp only [denoteErr, herrform, evalDyn_sOr, gInt_true_of_not_int M vx hx', Bool.or_true,
        Bool.true_or]
    rw [herr]; simp only [if_true, hchar]
    cases hvx : denoteSymV M vx with
    | VCon cv => cases cv <;> first | rfl | exact absurd hvx (hx' _)
    | _ => rfl

/-! ### The six binary integer builtins -/

theorem eb_sub_char (v w : CekValue) : evalBuiltin .SubtractInteger [w, v] = match v, w with
    | .VCon (.Integer x), .VCon (.Integer y) => some (.VCon (.Integer (x - y))) | _, _ => none := by
  cases v with
  | VCon cv => cases w with
    | VCon cw => cases cv <;> cases cw <;> rfl
    | _ => cases cv <;> rfl
  | _ => cases w <;> rfl
theorem eb_mul_char (v w : CekValue) : evalBuiltin .MultiplyInteger [w, v] = match v, w with
    | .VCon (.Integer x), .VCon (.Integer y) => some (.VCon (.Integer (x * y))) | _, _ => none := by
  cases v with
  | VCon cv => cases w with
    | VCon cw => cases cv <;> cases cw <;> rfl
    | _ => cases cv <;> rfl
  | _ => cases w <;> rfl
theorem eb_eq_char (v w : CekValue) : evalBuiltin .EqualsInteger [w, v] = match v, w with
    | .VCon (.Integer x), .VCon (.Integer y) => some (.VCon (.Bool (x == y))) | _, _ => none := by
  cases v with
  | VCon cv => cases w with
    | VCon cw => cases cv <;> cases cw <;> rfl
    | _ => cases cv <;> rfl
  | _ => cases w <;> rfl
theorem eb_lt_char (v w : CekValue) : evalBuiltin .LessThanInteger [w, v] = match v, w with
    | .VCon (.Integer x), .VCon (.Integer y) => some (.VCon (.Bool (decide (x < y)))) | _, _ => none := by
  cases v with
  | VCon cv => cases w with
    | VCon cw => cases cv <;> cases cw <;> rfl
    | _ => cases cv <;> rfl
  | _ => cases w <;> rfl
theorem eb_le_char (v w : CekValue) : evalBuiltin .LessThanEqualsInteger [w, v] = match v, w with
    | .VCon (.Integer x), .VCon (.Integer y) => some (.VCon (.Bool (decide (x ≤ y)))) | _, _ => none := by
  cases v with
  | VCon cv => cases w with
    | VCon cw => cases cv <;> cases cw <;> rfl
    | _ => cases cv <;> rfl
  | _ => cases w <;> rfl

theorem add_agrees (M : Model) (vy vx : SymV) :
    evalBuiltin .AddInteger (denoteSymList M [vy, vx])
      = if denoteErr M (symSaturate .AddInteger [vy, vx]) then none
        else some (denoteVal M (symSaturate .AddInteger [vy, vx])) := by
  apply binIntGuard_agrees M .AddInteger vy vx (fun x y => .Integer (x + y)) eb_add_char rfl
  intro xi yi hsvax hsvby
  simp only [denoteVal, show (symSaturate .AddInteger [vy, vx]).val =
    .fo (V.int (Op.add (V.sAsInt (reifyFO vx).2) (V.sAsInt (reifyFO vy).2))) from rfl,
    denoteSymV, V.int, Op.add, evalDyn_sAsInt, evalDyn_app, evalDynList, ea_VInt, ea_add,
    toV_v, hsvax, hsvby, SemV.getInt, toInt_i, decodeV]

theorem sub_agrees (M : Model) (vy vx : SymV) :
    evalBuiltin .SubtractInteger (denoteSymList M [vy, vx])
      = if denoteErr M (symSaturate .SubtractInteger [vy, vx]) then none
        else some (denoteVal M (symSaturate .SubtractInteger [vy, vx])) := by
  apply binIntGuard_agrees M .SubtractInteger vy vx (fun x y => .Integer (x - y)) eb_sub_char rfl
  intro xi yi hsvax hsvby
  simp only [denoteVal, show (symSaturate .SubtractInteger [vy, vx]).val =
    .fo (V.int (Op.sub (V.sAsInt (reifyFO vx).2) (V.sAsInt (reifyFO vy).2))) from rfl,
    denoteSymV, V.int, Op.sub, evalDyn_sAsInt, evalDyn_app, evalDynList, ea_VInt, ea_sub,
    toV_v, hsvax, hsvby, SemV.getInt, toInt_i, decodeV]

theorem mul_agrees (M : Model) (vy vx : SymV) :
    evalBuiltin .MultiplyInteger (denoteSymList M [vy, vx])
      = if denoteErr M (symSaturate .MultiplyInteger [vy, vx]) then none
        else some (denoteVal M (symSaturate .MultiplyInteger [vy, vx])) := by
  apply binIntGuard_agrees M .MultiplyInteger vy vx (fun x y => .Integer (x * y)) eb_mul_char rfl
  intro xi yi hsvax hsvby
  simp only [denoteVal, show (symSaturate .MultiplyInteger [vy, vx]).val =
    .fo (V.int (Op.mul (V.sAsInt (reifyFO vx).2) (V.sAsInt (reifyFO vy).2))) from rfl,
    denoteSymV, V.int, Op.mul, evalDyn_sAsInt, evalDyn_app, evalDynList, ea_VInt, ea_mul,
    toV_v, hsvax, hsvby, SemV.getInt, toInt_i, decodeV]

theorem eq_agrees (M : Model) (vy vx : SymV) :
    evalBuiltin .EqualsInteger (denoteSymList M [vy, vx])
      = if denoteErr M (symSaturate .EqualsInteger [vy, vx]) then none
        else some (denoteVal M (symSaturate .EqualsInteger [vy, vx])) := by
  apply binIntGuard_agrees M .EqualsInteger vy vx (fun x y => .Bool (x == y)) eb_eq_char rfl
  intro xi yi hsvax hsvby
  simp only [denoteVal, show (symSaturate .EqualsInteger [vy, vx]).val =
    .fo (V.bool (SExpr.sEq (V.sAsInt (reifyFO vx).2) (V.sAsInt (reifyFO vy).2))) from rfl,
    denoteSymV, V.bool, evalDyn_app, evalDynList, ea_VBool, evalDyn_sEq, evalDyn_sAsInt,
    hsvax, hsvby, SemV.getInt, toV_v, toBool_b, decodeV, Dyn.i.injEq]
  rfl

theorem lt_agrees (M : Model) (vy vx : SymV) :
    evalBuiltin .LessThanInteger (denoteSymList M [vy, vx])
      = if denoteErr M (symSaturate .LessThanInteger [vy, vx]) then none
        else some (denoteVal M (symSaturate .LessThanInteger [vy, vx])) := by
  apply binIntGuard_agrees M .LessThanInteger vy vx (fun x y => .Bool (decide (x < y))) eb_lt_char rfl
  intro xi yi hsvax hsvby
  simp only [denoteVal, show (symSaturate .LessThanInteger [vy, vx]).val =
    .fo (V.bool (Op.lt (V.sAsInt (reifyFO vx).2) (V.sAsInt (reifyFO vy).2))) from rfl,
    denoteSymV, V.bool, Op.lt, evalDyn_sAsInt, evalDyn_app, evalDynList, ea_VBool, ea_lt,
    hsvax, hsvby, SemV.getInt, toV_v, toBool_b, toInt_i, decodeV]

theorem le_agrees (M : Model) (vy vx : SymV) :
    evalBuiltin .LessThanEqualsInteger (denoteSymList M [vy, vx])
      = if denoteErr M (symSaturate .LessThanEqualsInteger [vy, vx]) then none
        else some (denoteVal M (symSaturate .LessThanEqualsInteger [vy, vx])) := by
  apply binIntGuard_agrees M .LessThanEqualsInteger vy vx (fun x y => .Bool (decide (x ≤ y))) eb_le_char rfl
  intro xi yi hsvax hsvby
  simp only [denoteVal, show (symSaturate .LessThanEqualsInteger [vy, vx]).val =
    .fo (V.bool (Op.le (V.sAsInt (reifyFO vx).2) (V.sAsInt (reifyFO vy).2))) from rfl,
    denoteSymV, V.bool, Op.le, evalDyn_sAsInt, evalDyn_app, evalDynList, ea_VBool, ea_le,
    hsvax, hsvby, SemV.getInt, toV_v, toBool_b, toInt_i, decodeV]

theorem eb_headList_char (v : CekValue) :
    evalBuiltin .HeadList [v] =
      match v with
      | .VCon (.ConstDataList (h :: _)) => some (.VCon (.Data h))
      | .VCon (.ConstDataList []) => none
      | .VCon (.ConstList (h :: _)) => some (.VCon h)
      | .VCon (.ConstList []) => none
      | _ => none := by
  cases v with
  | VCon c =>
      cases c <;> try rfl
      · rename_i xs; cases xs <;> rfl
      · rename_i xs; cases xs <;> rfl
  | VLam _ _ => rfl
  | VDelay _ _ => rfl
  | VBuiltin _ _ _ => rfl
  | VConstr _ _ => rfl

theorem eb_tailList_char (v : CekValue) :
    evalBuiltin .TailList [v] =
      match v with
      | .VCon (.ConstDataList (_ :: t)) => some (.VCon (.ConstDataList t))
      | .VCon (.ConstDataList []) => none
      | .VCon (.ConstList (_ :: t)) => some (.VCon (.ConstList t))
      | .VCon (.ConstList []) => none
      | _ => none := by
  cases v with
  | VCon c =>
      cases c <;> try rfl
      · rename_i xs; cases xs <;> rfl
      · rename_i xs; cases xs <;> rfl
  | VLam _ _ => rfl
  | VDelay _ _ => rfl
  | VBuiltin _ _ _ => rfl
  | VConstr _ _ => rfl

theorem eb_nullList_char (v : CekValue) :
    evalBuiltin .NullList [v] =
      match v with
      | .VCon (.ConstDataList xs) => some (.VCon (.Bool xs.isEmpty))
      | .VCon (.ConstList xs) => some (.VCon (.Bool xs.isEmpty))
      | _ => none := by
  cases v with
  | VCon c => cases c <;> rfl
  | VLam _ _ => rfl
  | VDelay _ _ => rfl
  | VBuiltin _ _ _ => rfl
  | VConstr _ _ => rfl

theorem eb_mkCons_char (tail head : CekValue) :
    evalBuiltin .MkCons [tail, head] =
      match tail, head with
      | .VCon (.ConstDataList xs), .VCon (.Data h) => some (.VCon (.ConstDataList (h :: xs)))
      | .VCon (.ConstList xs), .VCon h => some (.VCon (.ConstList (h :: xs)))
      | _, _ => none := by
  cases tail with
  | VCon ct =>
      cases head with
      | VCon ch => cases ct <;> cases ch <;> rfl
      | VLam _ _ => cases ct <;> rfl
      | VDelay _ _ => cases ct <;> rfl
      | VBuiltin _ _ _ => cases ct <;> rfl
      | VConstr _ _ => cases ct <;> rfl
  | VLam _ _ => cases head <;> rfl
  | VDelay _ _ => cases head <;> rfl
  | VBuiltin _ _ _ => cases head <;> rfl
  | VConstr _ _ => cases head <;> rfl

theorem eb_fstPair_char (v : CekValue) :
    evalBuiltin .FstPair [v] =
      match v with
      | .VCon (.PairData (a, _)) => some (.VCon (.Data a))
      | .VCon (.Pair (a, _)) => some (.VCon a)
      | _ => none := by
  cases v with
  | VCon c => cases c <;> rfl
  | VLam _ _ => rfl
  | VDelay _ _ => rfl
  | VBuiltin _ _ _ => rfl
  | VConstr _ _ => rfl

theorem eb_iData_char (v : CekValue) :
    evalBuiltin .IData [v] =
      match v with
      | .VCon (.Integer i) => some (.VCon (.Data (.I i)))
      | _ => none := by
  cases v with
  | VCon c => cases c <;> rfl
  | VLam _ _ => rfl
  | VDelay _ _ => rfl
  | VBuiltin _ _ _ => rfl
  | VConstr _ _ => rfl

theorem eb_bData_char (v : CekValue) :
    evalBuiltin .BData [v] =
      match v with
      | .VCon (.ByteString bs) => some (.VCon (.Data (.B bs)))
      | _ => none := by
  cases v with
  | VCon c => cases c <;> rfl
  | VLam _ _ => rfl
  | VDelay _ _ => rfl
  | VBuiltin _ _ _ => rfl
  | VConstr _ _ => rfl

theorem eb_mkNilData_char (v : CekValue) :
    evalBuiltin .MkNilData [v] =
      match v with
      | .VCon .Unit => some (.VCon (.ConstDataList []))
      | _ => none := by
  cases v with
  | VCon c => cases c <;> rfl
  | VLam _ _ => rfl
  | VDelay _ _ => rfl
  | VBuiltin _ _ _ => rfl
  | VConstr _ _ => rfl

theorem eb_mkNilPairData_char (v : CekValue) :
    evalBuiltin .MkNilPairData [v] =
      match v with
      | .VCon .Unit => some (.VCon (.ConstPairDataList []))
      | _ => none := by
  cases v with
  | VCon c => cases c <;> rfl
  | VLam _ _ => rfl
  | VDelay _ _ => rfl
  | VBuiltin _ _ _ => rfl
  | VConstr _ _ => rfl

theorem eb_sndPair_char (v : CekValue) :
    evalBuiltin .SndPair [v] =
      match v with
      | .VCon (.PairData (_, b)) => some (.VCon (.Data b))
      | .VCon (.Pair (_, b)) => some (.VCon b)
      | _ => none := by
  cases v with
  | VCon c => cases c <;> rfl
  | VLam _ _ => rfl
  | VDelay _ _ => rfl
  | VBuiltin _ _ _ => rfl
  | VConstr _ _ => rfl

private theorem symBuiltin_headList_eq (e : SExpr) :
    symBuiltin .HeadList [e] =
      onList e
        (fun dl => foGuard (DL.sIsNil dl) (V.data (DL.sHd dl)))
        (fun vl => foGuard (VL.sIsNil vl) (VL.sHd vl)) := rfl

private theorem symSaturate_headList_eq (v : SymV) :
    symSaturate .HeadList [v] =
      let reified := ([v].reverse).map reifyFO
      let nfErr := sOrs (reified.map Prod.fst)
      let r := symBuiltin .HeadList (reified.map Prod.snd)
      ⟨r.inc, SExpr.sOr nfErr r.err, r.val⟩ := rfl

private theorem symBuiltin_tailList_eq (e : SExpr) :
    symBuiltin .TailList [e] =
      onList e
        (fun dl => foGuard (DL.sIsNil dl) (V.dlist (DL.sTl dl)))
        (fun vl => foGuard (VL.sIsNil vl) (V.list (VL.sTl vl))) := rfl

private theorem symSaturate_tailList_eq (v : SymV) :
    symSaturate .TailList [v] =
      let reified := ([v].reverse).map reifyFO
      let nfErr := sOrs (reified.map Prod.fst)
      let r := symBuiltin .TailList (reified.map Prod.snd)
      ⟨r.inc, SExpr.sOr nfErr r.err, r.val⟩ := rfl

private theorem symBuiltin_nullList_eq (e : SExpr) :
    symBuiltin .NullList [e] =
      onList e
        (fun dl => okFO (V.bool (DL.sIsNil dl)))
        (fun vl => okFO (V.bool (VL.sIsNil vl))) := rfl

private theorem symSaturate_nullList_eq (v : SymV) :
    symSaturate .NullList [v] =
      let reified := ([v].reverse).map reifyFO
      let nfErr := sOrs (reified.map Prod.fst)
      let r := symBuiltin .NullList (reified.map Prod.snd)
      ⟨r.inc, SExpr.sOr nfErr r.err, r.val⟩ := rfl

private theorem symBuiltin_iData_eq (e : SExpr) :
    symBuiltin .IData [e] =
      foGuard (gInt e) (V.data (D.i (V.sAsInt e))) := rfl

private theorem symSaturate_iData_eq (v : SymV) :
    symSaturate .IData [v] =
      let reified := ([v].reverse).map reifyFO
      let nfErr := sOrs (reified.map Prod.fst)
      let r := symBuiltin .IData (reified.map Prod.snd)
      ⟨r.inc, SExpr.sOr nfErr r.err, r.val⟩ := rfl

private theorem symBuiltin_bData_eq (e : SExpr) :
    symBuiltin .BData [e] =
      foGuard (gBS e) (V.data (D.b (V.sAsBS e))) := rfl

private theorem symSaturate_bData_eq (v : SymV) :
    symSaturate .BData [v] =
      let reified := ([v].reverse).map reifyFO
      let nfErr := sOrs (reified.map Prod.fst)
      let r := symBuiltin .BData (reified.map Prod.snd)
      ⟨r.inc, SExpr.sOr nfErr r.err, r.val⟩ := rfl

private theorem symBuiltin_mkNilData_eq (e : SExpr) :
    symBuiltin .MkNilData [e] =
      foGuard (gUnit e) (V.dlist DL.nil) := rfl

private theorem symSaturate_mkNilData_eq (v : SymV) :
    symSaturate .MkNilData [v] =
      let reified := ([v].reverse).map reifyFO
      let nfErr := sOrs (reified.map Prod.fst)
      let r := symBuiltin .MkNilData (reified.map Prod.snd)
      ⟨r.inc, SExpr.sOr nfErr r.err, r.val⟩ := rfl

private theorem symBuiltin_mkNilPairData_eq (e : SExpr) :
    symBuiltin .MkNilPairData [e] =
      foGuard (gUnit e) (V.pdlist DM.nil) := rfl

private theorem symSaturate_mkNilPairData_eq (v : SymV) :
    symSaturate .MkNilPairData [v] =
      let reified := ([v].reverse).map reifyFO
      let nfErr := sOrs (reified.map Prod.fst)
      let r := symBuiltin .MkNilPairData (reified.map Prod.snd)
      ⟨r.inc, SExpr.sOr nfErr r.err, r.val⟩ := rfl

private theorem symBuiltin_mkCons_eq (h t : SExpr) :
    symBuiltin .MkCons [h, t] =
      symMerge (V.sIsCon "VDList" t)
        (foGuard (gData h) (V.dlist (DL.cons (V.sAsData h) (V.sAsDL t))))
        (symMerge (V.sIsCon "VList" t)
          (foGuard (V.sIsCon "VConstr" h) (V.list (VL.cons h (V.sAsList t))))
          errR) := rfl

private theorem symSaturate_mkCons_eq (tail head : SymV) :
    symSaturate .MkCons [tail, head] =
      let reified := ([tail, head].reverse).map reifyFO
      let nfErr := sOrs (reified.map Prod.fst)
      let r := symBuiltin .MkCons (reified.map Prod.snd)
      ⟨r.inc, SExpr.sOr nfErr r.err, r.val⟩ := rfl

private theorem symBuiltin_fstPair_eq (e : SExpr) :
    symBuiltin .FstPair [e] =
      symMerge (V.sIsCon "VPairD" e) (okFO (V.data (V.sFstD e)))
        (symMerge (V.sIsCon "VPair" e) (okFO (V.sFst e)) errR) := rfl

private theorem symSaturate_fstPair_eq (v : SymV) :
    symSaturate .FstPair [v] =
      let reified := ([v].reverse).map reifyFO
      let nfErr := sOrs (reified.map Prod.fst)
      let r := symBuiltin .FstPair (reified.map Prod.snd)
      ⟨r.inc, SExpr.sOr nfErr r.err, r.val⟩ := rfl

private theorem symBuiltin_sndPair_eq (e : SExpr) :
    symBuiltin .SndPair [e] =
      symMerge (V.sIsCon "VPairD" e) (okFO (V.data (V.sSndD e)))
        (symMerge (V.sIsCon "VPair" e) (okFO (V.sSnd e)) errR) := rfl

private theorem symSaturate_sndPair_eq (v : SymV) :
    symSaturate .SndPair [v] =
      let reified := ([v].reverse).map reifyFO
      let nfErr := sOrs (reified.map Prod.fst)
      let r := symBuiltin .SndPair (reified.map Prod.snd)
      ⟨r.inc, SExpr.sOr nfErr r.err, r.val⟩ := rfl

private theorem evalDyn_symMerge_err (M : Model) (c : SExpr) (x y : SymR) :
    (evalDyn M (symMerge c x y).err).toBool =
      if (evalDyn M c).toBool then denoteErr M x else denoteErr M y :=
  denoteErr_symMerge M c x y

private theorem denoteSymV_symMerge_val (M : Model) (c : SExpr) (x y : SymR) :
    denoteSymV M (symMerge c x y).val =
      if (evalDyn M c).toBool then denoteVal M x else denoteVal M y :=
  denoteVal_symMerge M c x y

theorem headList_agrees (M : Model) (v : SymV) (hwf : WFSymVal M v) :
    evalBuiltin .HeadList (denoteSymList M [v])
      = if denoteErr M (symSaturate .HeadList [v]) then none
        else some (denoteVal M (symSaturate .HeadList [v])) := by
  show evalBuiltin .HeadList [denoteSymV M v] = _
  by_cases hnf : (evalDyn M (reifyFO v).1).toBool
  · have hnot := nfErr_notVCon M v hnf
    have hEval : evalBuiltin .HeadList [denoteSymV M v] = none := by
      rw [eb_headList_char]
      cases hv : denoteSymV M v with
      | VCon c => exact False.elim ((hnot c) hv)
      | VLam _ _ => rfl
      | VDelay _ _ => rfl
      | VBuiltin _ _ _ => rfl
      | VConstr _ _ => rfl
    have herr : denoteErr M (symSaturate .HeadList [v]) = true := by
      simp [symSaturate_headList_eq, symBuiltin_headList_eq, onList, denoteErr,
        evalDyn_symMerge_err, hnf, evalDyn_sOr, evalDyn_sOrs]
    rw [hEval, herr]
    rfl
  · have hden := reifyFO_denote M v (by simpa using hnf)
    have hwfr := reifyFO_wf M v hwf (by simpa using hnf)
    cases hsv : (evalDyn M (reifyFO v).2).toV with
    | dlist dl =>
        rw [eb_headList_char, ← hden]
        cases dl <;>
          simp [symSaturate_headList_eq, symBuiltin_headList_eq, onList, denoteErr, denoteVal,
            evalDyn_symMerge_err, denoteSymV_symMerge_val, evalDyn_sOr, hnf, hsv, decodeV,
            evalDyn_sOrs, foGuard, errR', denoteSymV, V.data, evalDyn_sAsDL,
            SemV.conName, SemV.getDList, SemDL.isNil, SemDL.hd, decodeDL]
    | list vl =>
        rw [eb_headList_char, ← hden]
        have hwfl : WFVL vl ∧ ConstSemVL vl := by
          simpa [hsv, WFV] using hwfr
        cases vl with
        | nil =>
            simp [symSaturate_headList_eq, symBuiltin_headList_eq, onList, denoteErr, denoteVal,
              evalDyn_symMerge_err, denoteSymV_symMerge_val, evalDyn_sOr, hnf, hsv, decodeV,
              evalDyn_sOrs, foGuard, errR', denoteSymV, evalDyn_sAsList,
              SemV.conName, SemV.getList, SemVL.isNil, SemVL.hd, decodeVL]
        | cons h t =>
            have hcs : ConstSemV h := by
              simpa [ConstSemVL] using hwfl.2.1
            have hdec := decodeV_constSem h hcs
            rw [hsv]
            simp only [decodeV, decodeVL, List.map_cons, List.map_nil]
            have herr : denoteErr M (symSaturate .HeadList [v]) = false := by
              simp [symSaturate_headList_eq, symBuiltin_headList_eq, onList, denoteErr,
                evalDyn_symMerge_err, evalDyn_sOr, hnf, hsv, foGuard, errR', evalDyn_sAsList,
                SemV.conName, SemV.getList, SemVL.isNil, evalDyn_sOrs]
            have hval : denoteVal M (symSaturate .HeadList [v]) = decodeV h := by
              simp [symSaturate_headList_eq, symBuiltin_headList_eq, onList, denoteVal,
                denoteSymV_symMerge_val, evalDyn_sOr, hnf, hsv, foGuard, errR', denoteSymV,
                evalDyn_sAsList, SemV.conName, SemV.getList, SemVL.hd, evalDyn_sOrs]
            rw [herr, hval, ← hdec]
            simp
    | int n | bs s | bool b | unit | str s | data d | pdlist dm | pair a b | pairD a b
    | arr vl | constr tag fs | g1 | g2 | ml =>
        rw [eb_headList_char, ← hden]
        simp [symSaturate_headList_eq, symBuiltin_headList_eq, onList, denoteErr,
          evalDyn_symMerge_err, denoteSymV_symMerge_val, evalDyn_sOr, hnf, hsv,
          decodeV, evalDyn_sOrs, foGuard, errR', denoteSymV,
          SemV.conName]

theorem tailList_agrees (M : Model) (v : SymV) (hwf : WFSymVal M v) :
    evalBuiltin .TailList (denoteSymList M [v])
      = if denoteErr M (symSaturate .TailList [v]) then none
        else some (denoteVal M (symSaturate .TailList [v])) := by
  show evalBuiltin .TailList [denoteSymV M v] = _
  by_cases hnf : (evalDyn M (reifyFO v).1).toBool
  · have hnot := nfErr_notVCon M v hnf
    have hEval : evalBuiltin .TailList [denoteSymV M v] = none := by
      rw [eb_tailList_char]
      cases hv : denoteSymV M v with
      | VCon c => exact False.elim ((hnot c) hv)
      | VLam _ _ => rfl
      | VDelay _ _ => rfl
      | VBuiltin _ _ _ => rfl
      | VConstr _ _ => rfl
    have herr : denoteErr M (symSaturate .TailList [v]) = true := by
      simp [symSaturate_tailList_eq, symBuiltin_tailList_eq, onList, denoteErr,
        evalDyn_symMerge_err, hnf, evalDyn_sOr, evalDyn_sOrs]
    rw [hEval, herr]
    rfl
  · have hden := reifyFO_denote M v (by simpa using hnf)
    have hwfr := reifyFO_wf M v hwf (by simpa using hnf)
    cases hsv : (evalDyn M (reifyFO v).2).toV with
    | dlist dl =>
        rw [eb_tailList_char, ← hden]
        cases dl <;>
          simp [symSaturate_tailList_eq, symBuiltin_tailList_eq, onList, denoteErr, denoteVal,
            evalDyn_symMerge_err, denoteSymV_symMerge_val, evalDyn_sOr, hnf, hsv, decodeV,
            evalDyn_sOrs, foGuard, errR', denoteSymV, V.dlist, evalDyn_sAsDL,
            SemV.conName, SemV.getDList, SemDL.isNil, SemDL.tl, decodeDL]
    | list vl =>
        rw [eb_tailList_char, ← hden]
        have hwfl : WFVL vl ∧ ConstSemVL vl := by
          simpa [hsv, WFV] using hwfr
        cases vl with
        | nil =>
            simp [symSaturate_tailList_eq, symBuiltin_tailList_eq, onList, denoteErr, denoteVal,
              evalDyn_symMerge_err, denoteSymV_symMerge_val, evalDyn_sOr, hnf, hsv, decodeV,
              evalDyn_sOrs, foGuard, errR', denoteSymV, V.list, evalDyn_sAsList,
              SemV.conName, SemV.getList, SemVL.isNil, SemVL.tl, decodeVL]
        | cons h t =>
            rw [hsv]
            simp only [decodeV, decodeVL, List.map_cons]
            have herr : denoteErr M (symSaturate .TailList [v]) = false := by
              simp [symSaturate_tailList_eq, symBuiltin_tailList_eq, onList, denoteErr,
                evalDyn_symMerge_err, evalDyn_sOr, hnf, hsv, foGuard, errR',
                evalDyn_sAsList, SemV.conName, SemV.getList, SemVL.isNil, evalDyn_sOrs]
            have hval : denoteVal M (symSaturate .TailList [v])
                = .VCon (.ConstList ((decodeVL t).map cekToConst)) := by
              simp [symSaturate_tailList_eq, symBuiltin_tailList_eq, onList, denoteVal,
                denoteSymV_symMerge_val, hnf, hsv, foGuard, errR', denoteSymV,
                V.list, evalDyn_sAsList, SemV.conName, SemV.getList, SemVL.tl,
                decodeV, decodeVL]
            rw [herr, hval]
            simp
    | int n | bs s | bool b | unit | str s | data d | pdlist dm | pair a b | pairD a b
    | arr vl | constr tag fs | g1 | g2 | ml =>
        rw [eb_tailList_char, ← hden]
        simp [symSaturate_tailList_eq, symBuiltin_tailList_eq, onList, denoteErr,
          evalDyn_symMerge_err, denoteSymV_symMerge_val, evalDyn_sOr, hnf, hsv,
          decodeV, evalDyn_sOrs, foGuard, errR', denoteSymV,
          SemV.conName]

theorem nullList_agrees (M : Model) (v : SymV) :
    evalBuiltin .NullList (denoteSymList M [v])
      = if denoteErr M (symSaturate .NullList [v]) then none
        else some (denoteVal M (symSaturate .NullList [v])) := by
  show evalBuiltin .NullList [denoteSymV M v] = _
  by_cases hnf : (evalDyn M (reifyFO v).1).toBool
  · have hnot := nfErr_notVCon M v hnf
    have hEval : evalBuiltin .NullList [denoteSymV M v] = none := by
      rw [eb_nullList_char]
      cases hv : denoteSymV M v with
      | VCon c => exact False.elim ((hnot c) hv)
      | VLam _ _ => rfl
      | VDelay _ _ => rfl
      | VBuiltin _ _ _ => rfl
      | VConstr _ _ => rfl
    have herr : denoteErr M (symSaturate .NullList [v]) = true := by
      simp [symSaturate_nullList_eq, symBuiltin_nullList_eq, onList, denoteErr,
        evalDyn_symMerge_err, hnf, evalDyn_sOr, evalDyn_sOrs]
    rw [hEval, herr]
    rfl
  · have hden := reifyFO_denote M v (by simpa using hnf)
    cases hsv : (evalDyn M (reifyFO v).2).toV with
    | dlist dl =>
        rw [eb_nullList_char, ← hden]
        cases dl <;>
          simp [symSaturate_nullList_eq, symBuiltin_nullList_eq, onList, denoteErr, denoteVal,
            evalDyn_symMerge_err, denoteSymV_symMerge_val, evalDyn_sOr, hnf, hsv, decodeV,
            evalDyn_sOrs, foGuard, okFO, errR', denoteSymV, V.bool, evalDyn_sAsDL,
            evalDyn_app, evalDynList, ea_VBool, toV_v, toBool_b,
            SemV.conName, SemV.getDList, SemDL.isNil, decodeDL]
    | list vl =>
        rw [eb_nullList_char, ← hden]
        cases vl <;>
          simp [symSaturate_nullList_eq, symBuiltin_nullList_eq, onList, denoteErr, denoteVal,
            evalDyn_symMerge_err, denoteSymV_symMerge_val, evalDyn_sOr, hnf, hsv, decodeV,
            evalDyn_sOrs, foGuard, okFO, errR', denoteSymV, V.bool, evalDyn_sAsList,
            evalDyn_app, evalDynList, ea_VBool, toV_v, toBool_b,
            SemV.conName, SemV.getList, SemVL.isNil, decodeVL]
    | int n | bs s | bool b | unit | str s | data d | pdlist dm | pair a b | pairD a b
    | arr vl | constr tag fs | g1 | g2 | ml =>
        rw [eb_nullList_char, ← hden]
        simp [symSaturate_nullList_eq, symBuiltin_nullList_eq, onList, denoteErr,
          evalDyn_symMerge_err, denoteSymV_symMerge_val, evalDyn_sOr, hnf, hsv,
          decodeV, evalDyn_sOrs, foGuard, errR', denoteSymV,
          SemV.conName]

theorem fstPair_agrees (M : Model) (v : SymV) (hwf : WFSymVal M v) :
    evalBuiltin .FstPair (denoteSymList M [v])
      = if denoteErr M (symSaturate .FstPair [v]) then none
        else some (denoteVal M (symSaturate .FstPair [v])) := by
  show evalBuiltin .FstPair [denoteSymV M v] = _
  by_cases hnf : (evalDyn M (reifyFO v).1).toBool
  · have hnot := nfErr_notVCon M v hnf
    have hEval : evalBuiltin .FstPair [denoteSymV M v] = none := by
      rw [eb_fstPair_char]
      cases hv : denoteSymV M v with
      | VCon c => exact False.elim ((hnot c) hv)
      | VLam _ _ => rfl
      | VDelay _ _ => rfl
      | VBuiltin _ _ _ => rfl
      | VConstr _ _ => rfl
    have herr : denoteErr M (symSaturate .FstPair [v]) = true := by
      simp [symSaturate_fstPair_eq, symBuiltin_fstPair_eq, denoteErr,
        evalDyn_symMerge_err, hnf, evalDyn_sOr, evalDyn_sOrs, errR]
    rw [hEval, herr]
    rfl
  · have hden := reifyFO_denote M v (by simpa using hnf)
    have hwfr := reifyFO_wf M v hwf (by simpa using hnf)
    cases hsv : (evalDyn M (reifyFO v).2).toV with
    | pair a b =>
        rw [eb_fstPair_char, ← hden]
        have hwfp : WFV a ∧ WFV b ∧ ConstSemV a ∧ ConstSemV b := by
          simpa [hsv, WFV] using hwfr
        have hda := decodeV_constSem a hwfp.2.2.1
        rw [hsv]
        simp only [decodeV]
        have herr : denoteErr M (symSaturate .FstPair [v]) = false := by
          simp [symSaturate_fstPair_eq, symBuiltin_fstPair_eq, denoteErr,
            evalDyn_symMerge_err, evalDyn_sOr, hnf, hsv, okFO, errR, SemV.conName, evalDyn_sOrs]
        have hval : denoteVal M (symSaturate .FstPair [v]) = decodeV a := by
          simp [symSaturate_fstPair_eq, symBuiltin_fstPair_eq, denoteVal,
            denoteSymV_symMerge_val, hnf, hsv, okFO, errR, denoteSymV, evalDyn_sFst,
            SemV.conName, SemV.pFst]
        rw [herr, hval, ← hda]
        simp
    | pairD a b =>
        rw [eb_fstPair_char, ← hden]
        simp [symSaturate_fstPair_eq, symBuiltin_fstPair_eq, denoteErr, denoteVal,
          evalDyn_symMerge_err, denoteSymV_symMerge_val, evalDyn_sOr, hnf, hsv, decodeV,
          evalDyn_sOrs, okFO, errR, denoteSymV, V.data, evalDyn_sFstD,
          evalDyn_app, evalDynList, ea_VData, toV_v,
          SemV.conName, SemV.pdFst]
    | int n | bs s | bool b | unit | str s | data d | list vl | dlist dl | pdlist dm
    | arr vl | constr tag fs | g1 | g2 | ml =>
        rw [eb_fstPair_char, ← hden]
        simp [symSaturate_fstPair_eq, symBuiltin_fstPair_eq, denoteErr,
          evalDyn_symMerge_err, denoteSymV_symMerge_val, evalDyn_sOr, hnf, hsv,
          decodeV, evalDyn_sOrs, errR, denoteSymV, SemV.conName]

theorem sndPair_agrees (M : Model) (v : SymV) (hwf : WFSymVal M v) :
    evalBuiltin .SndPair (denoteSymList M [v])
      = if denoteErr M (symSaturate .SndPair [v]) then none
        else some (denoteVal M (symSaturate .SndPair [v])) := by
  show evalBuiltin .SndPair [denoteSymV M v] = _
  by_cases hnf : (evalDyn M (reifyFO v).1).toBool
  · have hnot := nfErr_notVCon M v hnf
    have hEval : evalBuiltin .SndPair [denoteSymV M v] = none := by
      rw [eb_sndPair_char]
      cases hv : denoteSymV M v with
      | VCon c => exact False.elim ((hnot c) hv)
      | VLam _ _ => rfl
      | VDelay _ _ => rfl
      | VBuiltin _ _ _ => rfl
      | VConstr _ _ => rfl
    have herr : denoteErr M (symSaturate .SndPair [v]) = true := by
      simp [symSaturate_sndPair_eq, symBuiltin_sndPair_eq, denoteErr,
        evalDyn_symMerge_err, hnf, evalDyn_sOr, evalDyn_sOrs, errR]
    rw [hEval, herr]
    rfl
  · have hden := reifyFO_denote M v (by simpa using hnf)
    have hwfr := reifyFO_wf M v hwf (by simpa using hnf)
    cases hsv : (evalDyn M (reifyFO v).2).toV with
    | pair a b =>
        rw [eb_sndPair_char, ← hden]
        have hwfp : WFV a ∧ WFV b ∧ ConstSemV a ∧ ConstSemV b := by
          simpa [hsv, WFV] using hwfr
        have hdb := decodeV_constSem b hwfp.2.2.2
        rw [hsv]
        simp only [decodeV]
        have herr : denoteErr M (symSaturate .SndPair [v]) = false := by
          simp [symSaturate_sndPair_eq, symBuiltin_sndPair_eq, denoteErr,
            evalDyn_symMerge_err, evalDyn_sOr, hnf, hsv, okFO, errR, SemV.conName, evalDyn_sOrs]
        have hval : denoteVal M (symSaturate .SndPair [v]) = decodeV b := by
          simp [symSaturate_sndPair_eq, symBuiltin_sndPair_eq, denoteVal,
            denoteSymV_symMerge_val, hnf, hsv, okFO, errR, denoteSymV, evalDyn_sSnd,
            SemV.conName, SemV.pSnd]
        rw [herr, hval, ← hdb]
        simp
    | pairD a b =>
        rw [eb_sndPair_char, ← hden]
        simp [symSaturate_sndPair_eq, symBuiltin_sndPair_eq, denoteErr, denoteVal,
          evalDyn_symMerge_err, denoteSymV_symMerge_val, evalDyn_sOr, hnf, hsv, decodeV,
          evalDyn_sOrs, okFO, errR, denoteSymV, V.data, evalDyn_sSndD,
          evalDyn_app, evalDynList, ea_VData, toV_v,
          SemV.conName, SemV.pdSnd]
    | int n | bs s | bool b | unit | str s | data d | list vl | dlist dl | pdlist dm
    | arr vl | constr tag fs | g1 | g2 | ml =>
        rw [eb_sndPair_char, ← hden]
        simp [symSaturate_sndPair_eq, symBuiltin_sndPair_eq, denoteErr,
          evalDyn_symMerge_err, denoteSymV_symMerge_val, evalDyn_sOr, hnf, hsv,
          decodeV, evalDyn_sOrs, errR, denoteSymV, SemV.conName]

theorem iData_agrees (M : Model) (v : SymV) (_hwf : WFSymVal M v) :
    evalBuiltin .IData (denoteSymList M [v])
      = if denoteErr M (symSaturate .IData [v]) then none
        else some (denoteVal M (symSaturate .IData [v])) := by
  show evalBuiltin .IData [denoteSymV M v] = _
  by_cases hnf : (evalDyn M (reifyFO v).1).toBool
  · have hnot := nfErr_notVCon M v hnf
    have hEval : evalBuiltin .IData [denoteSymV M v] = none := by
      rw [eb_iData_char]
      cases hv : denoteSymV M v with
      | VCon c => exact False.elim ((hnot c) hv)
      | VLam _ _ => rfl
      | VDelay _ _ => rfl
      | VBuiltin _ _ _ => rfl
      | VConstr _ _ => rfl
    have herr : denoteErr M (symSaturate .IData [v]) = true := by
      simp [symSaturate_iData_eq, symBuiltin_iData_eq, denoteErr,
        evalDyn_sOr, hnf, evalDyn_sOrs, errR]
    rw [hEval, herr]
    rfl
  · have hden := reifyFO_denote M v (by simpa using hnf)
    cases hsv : (evalDyn M (reifyFO v).2).toV with
    | int n =>
        rw [eb_iData_char, ← hden]
        simp [symSaturate_iData_eq, symBuiltin_iData_eq, denoteErr, denoteVal, evalDyn_sOr, hnf, hsv,
          decodeV, evalDyn_sOrs, foGuard, gInt, evalDyn_sNot, denoteSymV,
          V.data, D.i, evalDyn_sAsInt, evalDyn_app, evalDynList, ea_VData, ea_DI,
          toV_v, SemV.conName, SemV.getInt, decodeD]
    | bs s | bool b | unit | str s | data d | list vl | dlist dl | pdlist dm
    | pair a b | pairD a b | arr vl | constr tag fs | g1 | g2 | ml =>
        rw [eb_iData_char, ← hden]
        simp [symSaturate_iData_eq, symBuiltin_iData_eq, denoteErr, evalDyn_sOr, hnf, hsv,
          decodeV, evalDyn_sOrs, foGuard, gInt, evalDyn_sNot, errR, denoteSymV,
          SemV.conName]

theorem bData_agrees (M : Model) (v : SymV) (_hwf : WFSymVal M v) :
    evalBuiltin .BData (denoteSymList M [v])
      = if denoteErr M (symSaturate .BData [v]) then none
        else some (denoteVal M (symSaturate .BData [v])) := by
  show evalBuiltin .BData [denoteSymV M v] = _
  by_cases hnf : (evalDyn M (reifyFO v).1).toBool
  · have hnot := nfErr_notVCon M v hnf
    have hEval : evalBuiltin .BData [denoteSymV M v] = none := by
      rw [eb_bData_char]
      cases hv : denoteSymV M v with
      | VCon c => exact False.elim ((hnot c) hv)
      | VLam _ _ => rfl
      | VDelay _ _ => rfl
      | VBuiltin _ _ _ => rfl
      | VConstr _ _ => rfl
    have herr : denoteErr M (symSaturate .BData [v]) = true := by
      simp [symSaturate_bData_eq, symBuiltin_bData_eq, denoteErr,
        evalDyn_sOr, hnf, evalDyn_sOrs, errR]
    rw [hEval, herr]
    rfl
  · have hden := reifyFO_denote M v (by simpa using hnf)
    cases hsv : (evalDyn M (reifyFO v).2).toV with
    | bs s =>
        rw [eb_bData_char, ← hden]
        simp [symSaturate_bData_eq, symBuiltin_bData_eq, denoteErr, denoteVal, evalDyn_sOr, hnf, hsv,
          decodeV, evalDyn_sOrs, foGuard, gBS, evalDyn_sNot, denoteSymV,
          V.data, D.b, evalDyn_sAsBS, evalDyn_app, evalDynList, ea_VData, ea_DB,
          toV_v, SemV.conName, SemV.getSeq, decodeD]
    | int n | bool b | unit | str s | data d | list vl | dlist dl | pdlist dm
    | pair a b | pairD a b | arr vl | constr tag fs | g1 | g2 | ml =>
        rw [eb_bData_char, ← hden]
        simp [symSaturate_bData_eq, symBuiltin_bData_eq, denoteErr, evalDyn_sOr, hnf, hsv,
          decodeV, evalDyn_sOrs, foGuard, gBS, evalDyn_sNot, errR, denoteSymV,
          SemV.conName]

theorem mkNilData_agrees (M : Model) (v : SymV) (_hwf : WFSymVal M v) :
    evalBuiltin .MkNilData (denoteSymList M [v])
      = if denoteErr M (symSaturate .MkNilData [v]) then none
        else some (denoteVal M (symSaturate .MkNilData [v])) := by
  show evalBuiltin .MkNilData [denoteSymV M v] = _
  by_cases hnf : (evalDyn M (reifyFO v).1).toBool
  · have hnot := nfErr_notVCon M v hnf
    have hEval : evalBuiltin .MkNilData [denoteSymV M v] = none := by
      rw [eb_mkNilData_char]
      cases hv : denoteSymV M v with
      | VCon c => exact False.elim ((hnot c) hv)
      | VLam _ _ => rfl
      | VDelay _ _ => rfl
      | VBuiltin _ _ _ => rfl
      | VConstr _ _ => rfl
    have herr : denoteErr M (symSaturate .MkNilData [v]) = true := by
      simp [symSaturate_mkNilData_eq, symBuiltin_mkNilData_eq, denoteErr,
        evalDyn_sOr, hnf, evalDyn_sOrs, errR]
    rw [hEval, herr]
    rfl
  · have hden := reifyFO_denote M v (by simpa using hnf)
    cases hsv : (evalDyn M (reifyFO v).2).toV with
    | unit =>
        rw [eb_mkNilData_char, ← hden]
        simp [symSaturate_mkNilData_eq, symBuiltin_mkNilData_eq, denoteErr, denoteVal, evalDyn_sOr, hnf, hsv,
          decodeV, evalDyn_sOrs, foGuard, gUnit, evalDyn_sNot, denoteSymV,
          V.dlist, DL.nil, evalDyn_app, evalDynList, ea_VDList, toV_v,
          SemV.conName, decodeDL]
    | int n | bs s | bool b | str s | data d | list vl | dlist dl | pdlist dm
    | pair a b | pairD a b | arr vl | constr tag fs | g1 | g2 | ml =>
        rw [eb_mkNilData_char, ← hden]
        simp [symSaturate_mkNilData_eq, symBuiltin_mkNilData_eq, denoteErr, evalDyn_sOr, hnf, hsv,
          decodeV, evalDyn_sOrs, foGuard, gUnit, evalDyn_sNot, errR, denoteSymV,
          SemV.conName]

theorem mkNilPairData_agrees (M : Model) (v : SymV) (_hwf : WFSymVal M v) :
    evalBuiltin .MkNilPairData (denoteSymList M [v])
      = if denoteErr M (symSaturate .MkNilPairData [v]) then none
        else some (denoteVal M (symSaturate .MkNilPairData [v])) := by
  show evalBuiltin .MkNilPairData [denoteSymV M v] = _
  by_cases hnf : (evalDyn M (reifyFO v).1).toBool
  · have hnot := nfErr_notVCon M v hnf
    have hEval : evalBuiltin .MkNilPairData [denoteSymV M v] = none := by
      rw [eb_mkNilPairData_char]
      cases hv : denoteSymV M v with
      | VCon c => exact False.elim ((hnot c) hv)
      | VLam _ _ => rfl
      | VDelay _ _ => rfl
      | VBuiltin _ _ _ => rfl
      | VConstr _ _ => rfl
    have herr : denoteErr M (symSaturate .MkNilPairData [v]) = true := by
      simp [symSaturate_mkNilPairData_eq, symBuiltin_mkNilPairData_eq, denoteErr,
        evalDyn_sOr, hnf, evalDyn_sOrs, errR]
    rw [hEval, herr]
    rfl
  · have hden := reifyFO_denote M v (by simpa using hnf)
    cases hsv : (evalDyn M (reifyFO v).2).toV with
    | unit =>
        rw [eb_mkNilPairData_char, ← hden]
        simp [symSaturate_mkNilPairData_eq, symBuiltin_mkNilPairData_eq, denoteErr, denoteVal, evalDyn_sOr, hnf, hsv,
          decodeV, evalDyn_sOrs, foGuard, gUnit, evalDyn_sNot, denoteSymV,
          V.pdlist, DM.nil, evalDyn_app, evalDynList, ea_VPDList, toV_v,
          SemV.conName, decodeDM]
    | int n | bs s | bool b | str s | data d | list vl | dlist dl | pdlist dm
    | pair a b | pairD a b | arr vl | constr tag fs | g1 | g2 | ml =>
        rw [eb_mkNilPairData_char, ← hden]
        simp [symSaturate_mkNilPairData_eq, symBuiltin_mkNilPairData_eq, denoteErr, evalDyn_sOr, hnf, hsv,
          decodeV, evalDyn_sOrs, foGuard, gUnit, evalDyn_sNot, errR, denoteSymV,
          SemV.conName]

theorem mkCons_agrees (M : Model) (tail head : SymV)
    (hwft : WFSymVal M tail) (hwfh : WFSymVal M head) :
    evalBuiltin .MkCons (denoteSymList M [tail, head])
      = if denoteErr M (symSaturate .MkCons [tail, head]) then none
        else some (denoteVal M (symSaturate .MkCons [tail, head])) := by
  show evalBuiltin .MkCons [denoteSymV M tail, denoteSymV M head] = _
  by_cases hnft : (evalDyn M (reifyFO tail).1).toBool
  · have hnot := nfErr_notVCon M tail hnft
    have hEval : evalBuiltin .MkCons [denoteSymV M tail, denoteSymV M head] = none := by
      rw [eb_mkCons_char]
      cases hv : denoteSymV M tail with
      | VCon c => exact False.elim ((hnot c) hv)
      | VLam _ _ => cases denoteSymV M head <;> rfl
      | VDelay _ _ => cases denoteSymV M head <;> rfl
      | VBuiltin _ _ _ => cases denoteSymV M head <;> rfl
      | VConstr _ _ => cases denoteSymV M head <;> rfl
    have herr : denoteErr M (symSaturate .MkCons [tail, head]) = true := by
      simp [symSaturate_mkCons_eq, symBuiltin_mkCons_eq, denoteErr,
        evalDyn_symMerge_err, evalDyn_sOr, hnft, evalDyn_sOrs, errR]
    rw [hEval, herr]
    rfl
  · by_cases hnfh : (evalDyn M (reifyFO head).1).toBool
    · have hnot := nfErr_notVCon M head hnfh
      have hEval : evalBuiltin .MkCons [denoteSymV M tail, denoteSymV M head] = none := by
        rw [eb_mkCons_char]
        cases hvh : denoteSymV M head with
        | VCon c => exact False.elim ((hnot c) hvh)
        | VLam _ _ =>
            cases denoteSymV M tail <;> try rfl
            rename_i ct
            cases ct <;> rfl
        | VDelay _ _ =>
            cases denoteSymV M tail <;> try rfl
            rename_i ct
            cases ct <;> rfl
        | VBuiltin _ _ _ =>
            cases denoteSymV M tail <;> try rfl
            rename_i ct
            cases ct <;> rfl
        | VConstr _ _ =>
            cases denoteSymV M tail <;> try rfl
            rename_i ct
            cases ct <;> rfl
      have herr : denoteErr M (symSaturate .MkCons [tail, head]) = true := by
        simp [symSaturate_mkCons_eq, symBuiltin_mkCons_eq, denoteErr,
          evalDyn_symMerge_err, evalDyn_sOr, hnft, hnfh, evalDyn_sOrs, errR]
      rw [hEval, herr]
      rfl
    · have hdent := reifyFO_denote M tail (by simpa using hnft)
      have hdenh := reifyFO_denote M head (by simpa using hnfh)
      have hwfrt := reifyFO_wf M tail hwft (by simpa using hnft)
      have hwfrh := reifyFO_wf M head hwfh (by simpa using hnfh)
      cases htv : (evalDyn M (reifyFO tail).2).toV with
      | dlist dl =>
          rw [eb_mkCons_char, ← hdent, ← hdenh]
          cases hhv : (evalDyn M (reifyFO head).2).toV with
          | data d =>
              simp [symSaturate_mkCons_eq, symBuiltin_mkCons_eq, denoteErr, denoteVal,
                evalDyn_symMerge_err, denoteSymV_symMerge_val, evalDyn_sOr, hnft, hnfh,
                htv, hhv, decodeV, evalDyn_sOrs, foGuard, errR, denoteSymV, V.dlist,
                gData, evalDyn_sNot,
                evalDyn_sAsDL, evalDyn_sAsData, evalDyn_app, evalDynList, ea_VDList,
                ea_dcons, DL.cons, toV_v, SemV.conName, SemV.getDList, SemV.getData,
                decodeDL]
          | int n | bs s | bool b | unit | str s | list vl | dlist dl2 | pdlist dm
          | pair a b | pairD a b | arr vl | constr tag fs | g1 | g2 | ml =>
              simp [symSaturate_mkCons_eq, symBuiltin_mkCons_eq, denoteErr,
                evalDyn_symMerge_err, denoteSymV_symMerge_val, evalDyn_sOr, hnft, hnfh,
                htv, hhv, decodeV, evalDyn_sOrs, foGuard, errR, denoteSymV,
                gData, evalDyn_sNot,
                SemV.conName]
      | list vl =>
          rw [eb_mkCons_char, ← hdent, ← hdenh]
          have hwfl : WFVL vl ∧ ConstSemVL vl := by
            simpa [htv, WFV] using hwfrt
          cases hhv : (evalDyn M (reifyFO head).2).toV with
          | constr tag fs =>
              simp [symSaturate_mkCons_eq, symBuiltin_mkCons_eq, denoteErr,
                evalDyn_symMerge_err, denoteSymV_symMerge_val, evalDyn_sOr, hnft, hnfh,
                htv, hhv, decodeV, evalDyn_sOrs, foGuard, errR, denoteSymV,
                SemV.conName]
          | int n | bs s | bool b | unit | str s | data d | list vl2 | dlist dl | pdlist dm
          | pair a b | pairD a b | arr vl2 | g1 | g2 | ml =>
              have hcs : ConstSemV (evalDyn M (reifyFO head).2).toV :=
                constSem_of_wfv_not_constr _ hwfrh (by simp [hhv, SemV.conName])
              have hdec := decodeV_constSem _ hcs
              rw [hhv] at hdec
              simp [decodeV, cekToConst] at hdec
              have herr : denoteErr M (symSaturate .MkCons [tail, head]) = false := by
                simp [symSaturate_mkCons_eq, symBuiltin_mkCons_eq, denoteErr,
                  evalDyn_symMerge_err, evalDyn_sOr, hnft, hnfh, htv, hhv,
                  foGuard, errR, SemV.conName, evalDyn_sOrs]
              have hval : denoteVal M (symSaturate .MkCons [tail, head])
                  = .VCon (.ConstList (cekToConst (decodeV (evalDyn M (reifyFO head).2).toV) ::
                      (decodeVL vl).map cekToConst)) := by
                simp [symSaturate_mkCons_eq, symBuiltin_mkCons_eq, denoteVal,
                  denoteSymV_symMerge_val, hnft, hnfh, htv, hhv, foGuard, errR, denoteSymV,
                  V.list, evalDyn_sAsList, evalDyn_app, evalDynList, ea_VList, toV_v,
                  ea_vcons, VL.cons, SemV.conName, SemV.getList, decodeV, decodeVL]
              rw [herr, hval]
              rw [htv, hhv]
              simp [decodeV, decodeVL, cekToConst, hdec]
      | int n | bs s | bool b | unit | str s | data d | pdlist dm | pair a b | pairD a b
      | arr vl | constr tag fs | g1 | g2 | ml =>
          rw [eb_mkCons_char, ← hdent, ← hdenh]
          cases hhv : (evalDyn M (reifyFO head).2).toV <;>
            simp [symSaturate_mkCons_eq, symBuiltin_mkCons_eq, denoteErr,
              evalDyn_symMerge_err, denoteSymV_symMerge_val, evalDyn_sOr, hnft, hnfh,
              htv, hhv, decodeV, evalDyn_sOrs, foGuard, errR, denoteSymV,
              SemV.conName]

end Moist.Verified.Smt
