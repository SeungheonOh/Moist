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

end Moist.Verified.Smt
