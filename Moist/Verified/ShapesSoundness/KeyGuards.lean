import Moist.Verified.ShapesSoundness.DataComparisons

variable [sv : Moist.CEK.SemVariant]

/-! # Guards of keys of known bytes

`insertKeyGuards` binds, after `k = unBData d`, the length test
`equalsInteger (lengthOfByteString k)`, the comparison `case (dropList
(lengthOfByteString k) units) [λ_ _. equalsByteString k, λy. equalsData d
(bData y)]`, the other `B` value `case (lengthTest 0) [B #, B #00]` and the
forced `chooseData`. This file evaluates their lowerings: each returns on every
path once `k` holds bytes (`lengthTerm_halts`, `compareTerm_halts`,
`otherTerm_halts`), and the values they return compare with the key as
`equalsData` does (`compareValue_apply`). Only `equalsInteger`,
`lengthOfByteString` and `dropList` act on lengths, and they accept every
integer; `equalsByteString` runs on keys shorter than `keyGuardBound` only.
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines

/-! ## Lowered guards -/

def unitListConst : Const := .ConstList (.AtomicType .TypeUnit) (List.replicate keyGuardBound .Unit)

def unitListType : BuiltinType := .TypeOperator (.TypeList (.AtomicType .TypeUnit))

/-- `equalsInteger (lengthOfByteString k)` with `k` at index `ik`. -/
def lengthTerm (ik : Nat) : Term :=
  .Apply (.Builtin .EqualsInteger) (.Apply (.Builtin .LengthOfByteString) (.Var (ik + 1)))

def slowBody (id : Nat) : Term :=
  .Apply (.Apply (.Builtin .EqualsData) (.Var (id + 2))) (.Apply (.Builtin .BData) (.Var 1))

/-- The comparison with `k` at index `ik` and `d` at index `id`, dropping the
    length of `k` from the list constant `units`. -/
def compareTermWith (units : Const × BuiltinType) (ik id : Nat) : Term :=
  .Case (.Apply (.Apply (.Force (.Builtin .DropList)) (.Apply (.Builtin .LengthOfByteString) (.Var (ik + 1))))
      (.Constant units))
    [.Lam 0 (.Lam 0 (.Apply (.Builtin .EqualsByteString) (.Var (ik + 3)))), .Lam 0 (slowBody id)]

def compareTerm (ik id : Nat) : Term := compareTermWith (unitListConst, unitListType) ik id

def emptyBytes : ByteArray := ByteArray.empty

def zeroBytes : ByteArray := ⟨#[0]⟩

/-- The other `B` value with the length test at index `il`, choosing between
    the bytes `e` and `z`. -/
def otherTermWith (e z : ByteArray) (il : Nat) : Term :=
  .Case (.Apply (.Var (il + 1)) (.Constant (.Integer 0, .AtomicType .TypeInteger)))
    [.Constant (.Data (.B e), .AtomicType .TypeData), .Constant (.Data (.B z), .AtomicType .TypeData)]

def otherTerm (il : Nat) : Term := otherTermWith emptyBytes zeroBytes il

omit sv in
theorem lower_guardLength {env : List VarId} {k : VarId} {ik : Nat} (hk : envLookupT env k = some ik) :
    lowerTotalExpr env (guardLength k) = some (lengthTerm ik) := by
  simp [guardLength, lengthApp, lengthTerm, MIR.lowerTotalExpr_app, lowerTotalExpr_builtin,
    lowerTotalExpr_var, hk]

omit sv in
theorem lower_guardCompare {env : List VarId} {d k h t y : VarId} {ik id : Nat}
    (hk : envLookupT env k = some ik) (hd : envLookupT env d = some id)
    (hhk : (h == k) = false) (htk : (t == k) = false) (hyd : (y == d) = false) :
    lowerTotalExpr env (guardCompare d k h t y) = some (compareTerm ik id) := by
  have hk₂ : envLookupT (t :: h :: env) k = some (ik + 2) := by
    rw [envLookupT_cons_neq t k _ htk, envLookupT_cons_neq h k env hhk, hk]; rfl
  have hd₁ : envLookupT (y :: env) d = some (id + 1) := by
    rw [envLookupT_cons_neq y d env hyd, hd]; rfl
  have hy : envLookupT (y :: env) y = some 0 := by
    rw [envLookupT_cons]; simp [varId_beq_self]
  simp [guardCompare, compareTerm, compareTermWith, slowBody, lengthApp, unitListLiteral, unitListConst, unitListType,
    MIR.lowerTotalExpr_app, MIR.lowerTotalExpr_case_of_list, MIR.lowerTotalExprList_cons,
    MIR.lowerTotalExprList_nil, MIR.lowerTotalExpr_lam, MIR.lowerTotalExpr_force,
    lowerTotalExpr_builtin, lowerTotalExpr_var, lowerTotalExpr_lit, hk, hk₂, hd₁, hy]

omit sv in
theorem lower_guardOther {env : List VarId} {l : VarId} {il : Nat} (hl : envLookupT env l = some il) :
    lowerTotalExpr env (guardOther l) = some (otherTerm il) := by
  simp [guardOther, otherTerm, otherTermWith, integerConstant, emptyBytesData, zeroBytesData, emptyBytes, zeroBytes,
    MIR.lowerTotalExpr_app, MIR.lowerTotalExpr_case_of_list, MIR.lowerTotalExprList_cons,
    MIR.lowerTotalExprList_nil, lowerTotalExpr_var, lowerTotalExpr_lit, hl]

/-! ## Values of the guards -/

def lengthValue (n : Nat) : CekValue :=
  .VBuiltin .EqualsInteger [.VCon (.Integer (Int.ofNat n))] (.one .argV)

def compareValueWith (m : Nat) (kb : ByteArray) (id : Nat) (ρ : CekEnv) : CekValue :=
  if kb.size < m then .VBuiltin .EqualsByteString [.VCon (.ByteString kb)] (.one .argV)
  else .VLam (slowBody id) ρ

def compareValue (kb : ByteArray) (id : Nat) (ρ : CekEnv) : CekValue :=
  compareValueWith keyGuardBound kb id ρ

def otherBytesWith (e z : ByteArray) (n : Nat) : ByteArray := if n = 0 then z else e

theorem otherBytesWith_size_ne {e z : ByteArray} (he : e.size = 0) (hz : z.size = 1) (n : Nat) :
    (otherBytesWith e z n).size ≠ n := by
  unfold otherBytesWith
  split
  · subst_vars; omega
  · omega

theorem lengthTerm_halts {ρ : CekEnv} {ik : Nat} {kb : ByteArray}
    (hk : ρ.lookup (ik + 1) = some (.VCon (.ByteString kb))) :
    Halts ρ (lengthTerm ik) (lengthValue kb.size) :=
  halts_apply_intro (halts_builtin_of ρ _)
    (halts_apply_intro (halts_builtin_of ρ _) (halts_var_of_lookup hk) (builtin_final_reaches rfl rfl rfl))
    (builtin_partial_reaches rfl rfl)

theorem dropList_const (ty : BuiltinType) (l : List Const) (m : Int) :
    evalBuiltinConst .DropList [Const.ConstList ty l, .Integer m] =
      (if m < 0 then some (.ConstList ty l)
       else if m < ((2 ^ 63 : Nat) : Int) then some (.ConstList ty (l.drop m.toNat))
       else if l.length ≤ 2 ^ 63 - 1 then some (.ConstList ty [])
       else none) := by
  unfold evalBuiltinConst; rfl

theorem dropList_eval (ty : BuiltinType) (l : List Const) (n : Nat) (hl : l.length ≤ 2 ^ 63 - 1) :
    evalBuiltin .DropList [.VCon (.ConstList ty l), .VCon (.Integer (Int.ofNat n))] =
      some (.VCon (.ConstList ty
        (if (Int.ofNat n) < ((2 ^ 63 : Nat) : Int) then l.drop n else []))) := by
  rw [show [CekValue.VCon (.ConstList ty l), .VCon (.Integer (Int.ofNat n))] =
    [Const.ConstList ty l, .Integer (Int.ofNat n)].map CekValue.VCon from rfl,
    evalBuiltin_consts _ _ rfl, dropList_const]
  have h0 : ¬ (Int.ofNat n < 0) := Int.not_lt.mpr (Int.natCast_nonneg n)
  rw [if_neg h0]
  by_cases h : (Int.ofNat n) < ((2 ^ 63 : Nat) : Int)
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h, if_pos hl]; rfl

theorem drop_cons_of_lt {l : List Const} {n : Nat} (h : n < l.length) :
    ∃ c rest, l.drop n = c :: rest := by
  cases hd : l.drop n with
  | nil => simp at hd; omega
  | cons c rest => exact ⟨c, rest, rfl⟩

theorem compareTermWith_halts {ρ : CekEnv} {ik id : Nat} {kb : ByteArray} {ety cty : BuiltinType}
    {units : List Const} (hunits : units.length ≤ keyGuardBound)
    (hk : ρ.lookup (ik + 1) = some (.VCon (.ByteString kb))) :
    Halts ρ (compareTermWith (.ConstList ety units, cty) ik id) (compareValueWith units.length kb id ρ) := by
  have hl63 : units.length ≤ 2 ^ 63 - 1 := by simp [keyGuardBound] at hunits; omega
  have hdrop : Halts ρ (.Apply (.Apply (.Force (.Builtin .DropList))
      (.Apply (.Builtin .LengthOfByteString) (.Var (ik + 1)))) (.Constant (.ConstList ety units, cty)))
      (.VCon (.ConstList ety
        (if (Int.ofNat kb.size) < ((2 ^ 63 : Nat) : Int) then units.drop kb.size else []))) := by
    have hf : Halts ρ (.Force (.Builtin .DropList)) (.VBuiltin .DropList [] (.more .argV (.one .argV))) :=
      forced_builtin_halts ρ .DropList rfl
    have hl : Halts ρ (.Apply (.Builtin .LengthOfByteString) (.Var (ik + 1)))
        (.VCon (.Integer (Int.ofNat kb.size))) :=
      halts_apply_intro (halts_builtin_of ρ _) (halts_var_of_lookup hk) (builtin_final_reaches rfl rfl rfl)
    exact halts_apply_intro (halts_apply_intro hf hl (builtin_partial_reaches rfl rfl))
      (halts_constant_of _ _) (builtin_final_reaches rfl rfl (dropList_eval ety units kb.size hl63))
  unfold compareValueWith
  split
  · rename_i hlt
    have h63 : (Int.ofNat kb.size) < ((2 ^ 63 : Nat) : Int) := by
      simp [keyGuardBound] at hunits ⊢; omega
    obtain ⟨c, rest, hrest⟩ := drop_cons_of_lt hlt
    rw [if_pos h63, hrest] at hdrop
    refine reaches_trans (reaches_of_steps 1 rfl) (reaches_trans (halts_on_stack hdrop _) ?_)
    have hk3 : ((ρ.extend (.VCon c)).extend (.VCon (.ConstList ety rest))).lookup
        (ik + 3) = some (.VCon (.ByteString kb)) := by
      simp only [CekEnv.extend, CekEnv.lookup]; exact hk
    refine reaches_trans (reaches_of_steps 1 (s' := .compute
      [.applyArg (.VCon c), .applyArg (.VCon (.ConstList ety rest))] ρ
      (.Lam 0 (.Lam 0 (.Apply (.Builtin .EqualsByteString) (.Var (ik + 3))))))
      (by simp [steps, step, constToTagAndFields])) ?_
    refine reaches_trans (reaches_of_steps 4 rfl) ?_
    exact halts_apply_intro (halts_builtin_of _ _) (halts_var_of_lookup hk3)
      (builtin_partial_reaches rfl rfl)
  · rename_i hge
    have hnil : (if (Int.ofNat kb.size) < ((2 ^ 63 : Nat) : Int) then units.drop kb.size else []) = [] := by
      split
      · simp; omega
      · rfl
    rw [hnil] at hdrop
    refine reaches_trans (reaches_of_steps 1 rfl) (reaches_trans (halts_on_stack hdrop _) ?_)
    exact ⟨4, by simp [steps, step, constToTagAndFields]⟩

theorem compareTerm_halts {ρ : CekEnv} {ik id : Nat} {kb : ByteArray}
    (hk : ρ.lookup (ik + 1) = some (.VCon (.ByteString kb))) :
    Halts ρ (compareTerm ik id) (compareValue kb id ρ) := by
  have := compareTermWith_halts (ety := .AtomicType .TypeUnit) (cty := unitListType)
    (units := List.replicate keyGuardBound Const.Unit) (by simp) (id := id) hk
  simpa [compareValue, compareTerm, unitListConst] using this

theorem otherTermWith_halts {ρ : CekEnv} {il n : Nat} {e z : ByteArray}
    (hl : ρ.lookup (il + 1) = some (lengthValue n)) :
    Halts ρ (otherTermWith e z il) (.VCon (.Data (.B (otherBytesWith e z n)))) := by
  have hs : Halts ρ (.Apply (.Var (il + 1)) (.Constant (.Integer 0, .AtomicType .TypeInteger)))
      (.VCon (.Bool (Int.ofNat n == 0))) :=
    halts_apply_intro (halts_var_of_lookup hl) (halts_constant_of _ _) (builtin_final_reaches rfl rfl rfl)
  refine reaches_trans (case_bool_steps hs) ?_
  by_cases h : n = 0
  · subst h; exact halts_constant_of _ _
  · have : (Int.ofNat n == 0) = false := by simp; omega
    rw [this]
    simp only [Bool.false_eq_true, if_false, otherBytesWith, h]
    exact halts_constant_of _ _

theorem otherTerm_halts {ρ : CekEnv} {il n : Nat} (hl : ρ.lookup (il + 1) = some (lengthValue n)) :
    ∃ v, Halts ρ (otherTerm il) v :=
  ⟨_, otherTermWith_halts hl⟩

theorem choose_halts (ρ : CekEnv) :
    Halts ρ (.Force (.Builtin .ChooseData)) (.VBuiltin .ChooseData []
      (.more .argV (.more .argV (.more .argV (.more .argV (.more .argV (.one .argV))))))) :=
  forced_builtin_halts ρ .ChooseData rfl

/-! ## The guarded comparison -/

def bytesOr (d : Moist.Plutus.Data) (other : ByteArray) : ByteArray :=
  match d with
  | .B bytes => bytes
  | _ => other

def chooseRest : ExpectedArgs :=
  .more .argV (.more .argV (.more .argV (.more .argV (.more .argV (.one .argV)))))

theorem chooseData_eval (d : Moist.Plutus.Data) (ob : ByteArray) :
    evalBuiltin .ChooseData [.VCon (.Data d), .VCon (.Data (.B ob)), .VCon (.Data (.B ob)),
      .VCon (.Data (.B ob)), .VCon (.Data (.B ob)), .VCon (.Data d)] =
      some (.VCon (.Data (.B (bytesOr d ob)))) := by
  cases d <;> rfl

theorem chooseData_eval_none {vb w : CekValue}
    (h : ∀ d, vb ≠ .VCon (.Data d)) : evalBuiltin .ChooseData [vb, w, w, w, w, vb] = none := by
  cases vb with
  | VCon c =>
    cases c
    all_goals first | (exact absurd rfl (h _)) | (cases w <;> rfl)
  | _ => cases w <;> rfl

/-- `chooseData x n n n n x` with the forced builtin `head`. -/
def chooseApply (head : Term) (ix io : Nat) : Term :=
  .Apply (.Apply (.Apply (.Apply (.Apply (.Apply head (.Var (ix + 1))) (.Var (io + 1))) (.Var (io + 1)))
    (.Var (io + 1))) (.Var (io + 1))) (.Var (ix + 1))

theorem chooseApply_partial {ρ : CekEnv} {head : Term} {ix io : Nat} {vx vo : CekValue}
    (hh : Halts ρ head (.VBuiltin .ChooseData [] chooseRest))
    (hx : ρ.lookup (ix + 1) = some vx) (ho : ρ.lookup (io + 1) = some vo) :
    Halts ρ (.Apply (.Apply (.Apply (.Apply (.Apply head (.Var (ix + 1))) (.Var (io + 1))) (.Var (io + 1)))
      (.Var (io + 1))) (.Var (io + 1))) (.VBuiltin .ChooseData [vo, vo, vo, vo, vx] (.one .argV)) := by
  have hvx := halts_var_of_lookup (ρ := ρ) hx
  have hvo := halts_var_of_lookup (ρ := ρ) ho
  exact halts_apply_intro (halts_apply_intro (halts_apply_intro (halts_apply_intro
    (halts_apply_intro hh hvx (builtin_partial_reaches rfl rfl)) hvo (builtin_partial_reaches rfl rfl))
    hvo (builtin_partial_reaches rfl rfl)) hvo (builtin_partial_reaches rfl rfl)) hvo
    (builtin_partial_reaches rfl rfl)

/-- What a comparison value does with bytes as long as the key `kb`. -/
def CompareSpec (cv : CekValue) (kb : ByteArray) : Prop :=
  ∀ b : ByteArray, b.size = kb.size →
    Reaches (.ret [.funV cv] (.VCon (.ByteString b))) (.halt (.VCon (.Bool (kb == b))))

/-- The guarded comparison of `x` (index `ix`) with the length test `ilt`,
    comparison `icmp` and other `B` value `io`. -/
def guardedTerm (head : Term) (ilt icmp io ix : Nat) (miss hit : Term) : Term :=
  .Case (.Apply (.Var (ilt + 1)) (.Apply (.Builtin .LengthOfByteString)
      (.Apply (.Builtin .UnBData) (chooseApply head ix io))))
    [miss, .Case (.Apply (.Var (icmp + 1)) (.Apply (.Builtin .UnBData) (.Var (ix + 1)))) [miss, hit]]

theorem bytes_ne_of_size {a b : ByteArray} (h : a.size ≠ b.size) : (a == b) = false := by
  cases hab : (a == b)
  · rfl
  · exfalso
    have : a.data = b.data := by
      have : (a.data == b.data) = true := hab
      simpa using this
    exact h (by simp [ByteArray.size, this])

theorem guarded_data {ρ : CekEnv} {π : Stack} {head miss hit : Term} {ilt icmp io ix : Nat}
    {kb ob : ByteArray} {cv : CekValue} {dx : Moist.Plutus.Data}
    (hh : Halts ρ head (.VBuiltin .ChooseData [] chooseRest))
    (hlt : ρ.lookup (ilt + 1) = some (lengthValue kb.size))
    (hcmp : ρ.lookup (icmp + 1) = some cv) (hspec : CompareSpec cv kb)
    (ho : ρ.lookup (io + 1) = some (.VCon (.Data (.B ob)))) (hob : ob.size ≠ kb.size)
    (hx : ρ.lookup (ix + 1) = some (.VCon (.Data dx))) :
    Reaches (.compute π ρ (guardedTerm head ilt icmp io ix miss hit))
      (.compute π ρ (if (Moist.Plutus.Data.B kb == dx) then hit else miss)) := by
  have hch : Halts ρ (chooseApply head ix io) (.VCon (.Data (.B (bytesOr dx ob)))) :=
    halts_apply_intro (chooseApply_partial hh hx ho) (halts_var_of_lookup hx)
      (builtin_final_reaches rfl rfl (chooseData_eval dx ob))
  have hun : Halts ρ (.Apply (.Builtin .UnBData) (chooseApply head ix io)) (.VCon (.ByteString (bytesOr dx ob))) :=
    halts_apply_intro (halts_builtin_of ρ _) hch (builtin_final_reaches rfl rfl rfl)
  have hlen : Halts ρ (.Apply (.Builtin .LengthOfByteString) (.Apply (.Builtin .UnBData) (chooseApply head ix io)))
      (.VCon (.Integer (Int.ofNat (bytesOr dx ob).size))) :=
    halts_apply_intro (halts_builtin_of ρ _) hun (builtin_final_reaches rfl rfl rfl)
  have hg := halts_apply_intro (halts_var_of_lookup hlt) hlen
    (builtin_final_reaches (r := .VCon (.Bool (Int.ofNat kb.size == Int.ofNat (bytesOr dx ob).size)))
      rfl rfl rfl)
  refine reaches_trans (case_bool_steps hg) ?_
  by_cases hsz : (bytesOr dx ob).size = kb.size
  · have hdx : ∃ b, dx = .B b := by
      cases dx with
      | B b => exact ⟨b, rfl⟩
      | _ => exact absurd hsz (by simpa [bytesOr] using hob)
    obtain ⟨b, rfl⟩ := hdx
    have htrue : (Int.ofNat kb.size == Int.ofNat (bytesOr (.B b) ob).size) = true := by
      simp [bytesOr] at hsz ⊢; omega
    rw [htrue]
    simp only [if_true]
    have hE : Halts ρ (.Apply (.Var (icmp + 1)) (.Apply (.Builtin .UnBData) (.Var (ix + 1))))
        (.VCon (.Bool (kb == b))) :=
      halts_apply_intro (halts_var_of_lookup hcmp)
        (halts_apply_intro (halts_builtin_of ρ _) (halts_var_of_lookup hx) (builtin_final_reaches rfl rfl rfl))
        (hspec b (by simpa [bytesOr] using hsz))
    refine reaches_trans (case_bool_steps hE) ?_
    have : (Moist.Plutus.Data.B kb == Moist.Plutus.Data.B b) = (kb == b) := rfl
    rw [this]
    exact reaches_refl _
  · have hfalse : (Int.ofNat kb.size == Int.ofNat (bytesOr dx ob).size) = false := by
      simp; omega
    rw [hfalse]
    simp only [Bool.false_eq_true, if_false]
    have : (Moist.Plutus.Data.B kb == dx) = false := by
      cases dx with
      | B b =>
        show (kb == b) = false
        exact bytes_ne_of_size (by simpa [bytesOr] using (Ne.symm hsz))
      | _ => rfl
    rw [this]
    exact reaches_refl _

theorem guarded_other {ρ : CekEnv} {π : Stack} {head miss hit : Term} {ilt icmp io ix : Nat}
    {vl vo vx : CekValue}
    (hh : Halts ρ head (.VBuiltin .ChooseData [] chooseRest)) (hlt : ρ.lookup (ilt + 1) = some vl)
    (ho : ρ.lookup (io + 1) = some vo) (hx : ρ.lookup (ix + 1) = some vx)
    (hnot : ∀ d, vx ≠ .VCon (.Data d)) :
    Reaches (.compute π ρ (guardedTerm head ilt icmp io ix miss hit)) .error := by
  apply case_errs_of_scrutinee
  have hch : Errs ρ (chooseApply head ix io) :=
    errs_apply_intro (chooseApply_partial hh hx ho) (halts_var_of_lookup hx)
      (builtin_final_errs rfl rfl (chooseData_eval_none hnot))
  exact errs_apply_arg (halts_var_of_lookup hlt) (errs_apply_arg (halts_builtin_of ρ _)
    (errs_apply_arg (halts_builtin_of ρ _) hch))

theorem cByteStringOk_of_small (b : ByteArray) (h : b.size < keyGuardBound) : cByteStringOk sv b = true := by
  cases sv
  · rfl
  · simp [cByteStringOk, SemVariant.ensurable, maxBoundByteString]
    simp [keyGuardBound] at h; omega

theorem equalsByteString_const (a b : ByteArray) :
    evalBuiltinConst .EqualsByteString [.ByteString b, .ByteString a] =
      if cByteStringOk sv a && cByteStringOk sv b then some (.Bool (a == b)) else none := by
  unfold evalBuiltinConst; rfl

theorem compareValue_spec {m : Nat} (hm : m ≤ keyGuardBound) {kb : ByteArray} {id : Nat} {ρ : CekEnv}
    (hd : ρ.lookup (id + 1) = some (.VCon (.Data (.B kb)))) : CompareSpec (compareValueWith m kb id ρ) kb := by
  intro b hb
  unfold compareValueWith
  split
  · rename_i hsmall
    apply builtin_final_reaches rfl rfl
    have h1 := cByteStringOk_of_small kb (by omega)
    have h2 := cByteStringOk_of_small b (by omega)
    rw [show [CekValue.VCon (.ByteString b), .VCon (.ByteString kb)] =
      [Const.ByteString b, .ByteString kb].map CekValue.VCon from rfl, evalBuiltin_consts _ _ rfl]
    rw [equalsByteString_const, h1, h2]; rfl
  · refine reaches_trans (reaches_of_steps 1 rfl) ?_
    have hd2 : (ρ.extend (.VCon (.ByteString b))).lookup (id + 2) = some (.VCon (.Data (.B kb))) := by
      simpa [CekEnv.extend, CekEnv.lookup] using hd
    have hb1 : (ρ.extend (.VCon (.ByteString b))).lookup 1 = some (.VCon (.ByteString b)) := rfl
    have hbd : Halts (ρ.extend (.VCon (.ByteString b))) (.Apply (.Builtin .BData) (.Var 1))
        (.VCon (.Data (.B b))) :=
      halts_apply_intro (halts_builtin_of _ _) (halts_var_of_lookup hb1) (builtin_final_reaches rfl rfl rfl)
    exact halts_apply_intro (halts_apply_intro (halts_builtin_of _ _) (halts_var_of_lookup hd2)
      (builtin_partial_reaches rfl rfl)) hbd (builtin_final_reaches rfl rfl rfl)

end Moist.Verified.ShapeFacts
