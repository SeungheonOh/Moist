import Moist.SMT.Soundness.BuiltinSuccess

namespace Moist.SMT.UPLC.Soundness

open Moist.Plutus.Term
open Moist.Verified.BigStep
open Moist.CEK (ArgKind ExpectedArgs expectedArgs CekEnv CekValue)

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_AddInteger_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .AddInteger cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_AddInteger_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .AddInteger args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_AddInteger_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_AddInteger_none_of_pair_not_ints {b a : CekValue}
    (h : ∀ ib ia, ¬ (b = .VCon (.Integer ib) ∧ a = .VCon (.Integer ia))) :
    Moist.CEK.evalBuiltin .AddInteger [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_SubtractInteger_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .SubtractInteger cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_SubtractInteger_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .SubtractInteger args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_SubtractInteger_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_SubtractInteger_none_of_pair_not_ints {b a : CekValue}
    (h : ∀ ib ia, ¬ (b = .VCon (.Integer ib) ∧ a = .VCon (.Integer ia))) :
    Moist.CEK.evalBuiltin .SubtractInteger [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_MultiplyInteger_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .MultiplyInteger cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_MultiplyInteger_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .MultiplyInteger args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_MultiplyInteger_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_MultiplyInteger_none_of_pair_not_ints {b a : CekValue}
    (h : ∀ ib ia, ¬ (b = .VCon (.Integer ib) ∧ a = .VCon (.Integer ia))) :
    Moist.CEK.evalBuiltin .MultiplyInteger [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_EqualsInteger_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .EqualsInteger cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_EqualsInteger_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .EqualsInteger args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_EqualsInteger_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_EqualsInteger_none_of_pair_not_ints {b a : CekValue}
    (h : ∀ ib ia, ¬ (b = .VCon (.Integer ib) ∧ a = .VCon (.Integer ia))) :
    Moist.CEK.evalBuiltin .EqualsInteger [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_LessThanInteger_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .LessThanInteger cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_LessThanInteger_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .LessThanInteger args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_LessThanInteger_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_LessThanInteger_none_of_pair_not_ints {b a : CekValue}
    (h : ∀ ib ia, ¬ (b = .VCon (.Integer ib) ∧ a = .VCon (.Integer ia))) :
    Moist.CEK.evalBuiltin .LessThanInteger [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_LessThanEqualsInteger_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .LessThanEqualsInteger cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_LessThanEqualsInteger_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .LessThanEqualsInteger args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_LessThanEqualsInteger_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_LessThanEqualsInteger_none_of_pair_not_ints {b a : CekValue}
    (h : ∀ ib ia, ¬ (b = .VCon (.Integer ib) ∧ a = .VCon (.Integer ia))) :
    Moist.CEK.evalBuiltin .LessThanEqualsInteger [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_DivideInteger_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .DivideInteger cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_DivideInteger_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .DivideInteger args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_DivideInteger_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_DivideInteger_none_of_pair_not_ints {b a : CekValue}
    (h : ∀ ib ia, ¬ (b = .VCon (.Integer ib) ∧ a = .VCon (.Integer ia))) :
    Moist.CEK.evalBuiltin .DivideInteger [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

theorem evalBuiltin_DivideInteger_none_of_divisor_zero {a b : Int}
    (hb : b = 0) :
    Moist.CEK.evalBuiltin .DivideInteger [.VCon (.Integer b), .VCon (.Integer a)] = none := by
  subst b
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_QuotientInteger_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .QuotientInteger cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_QuotientInteger_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .QuotientInteger args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_QuotientInteger_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_QuotientInteger_none_of_pair_not_ints {b a : CekValue}
    (h : ∀ ib ia, ¬ (b = .VCon (.Integer ib) ∧ a = .VCon (.Integer ia))) :
    Moist.CEK.evalBuiltin .QuotientInteger [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

theorem evalBuiltin_QuotientInteger_none_of_divisor_zero {a b : Int}
    (hb : b = 0) :
    Moist.CEK.evalBuiltin .QuotientInteger [.VCon (.Integer b), .VCon (.Integer a)] = none := by
  subst b
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_RemainderInteger_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .RemainderInteger cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_RemainderInteger_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .RemainderInteger args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_RemainderInteger_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_RemainderInteger_none_of_pair_not_ints {b a : CekValue}
    (h : ∀ ib ia, ¬ (b = .VCon (.Integer ib) ∧ a = .VCon (.Integer ia))) :
    Moist.CEK.evalBuiltin .RemainderInteger [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

theorem evalBuiltin_RemainderInteger_none_of_divisor_zero {a b : Int}
    (hb : b = 0) :
    Moist.CEK.evalBuiltin .RemainderInteger [.VCon (.Integer b), .VCon (.Integer a)] = none := by
  subst b
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_ModInteger_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .ModInteger cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_ModInteger_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .ModInteger args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_ModInteger_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_ModInteger_none_of_pair_not_ints {b a : CekValue}
    (h : ∀ ib ia, ¬ (b = .VCon (.Integer ib) ∧ a = .VCon (.Integer ia))) :
    Moist.CEK.evalBuiltin .ModInteger [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

theorem evalBuiltin_ModInteger_none_of_divisor_zero {a b : Int}
    (hb : b = 0) :
    Moist.CEK.evalBuiltin .ModInteger [.VCon (.Integer b), .VCon (.Integer a)] = none := by
  subst b
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_AppendByteString_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .AppendByteString cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_EqualsByteString_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .EqualsByteString cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_LessThanByteString_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .LessThanByteString cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_LessThanEqualsByteString_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .LessThanEqualsByteString cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_AppendByteString_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .AppendByteString args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_AppendByteString_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_EqualsByteString_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .EqualsByteString args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_EqualsByteString_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_LessThanByteString_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .LessThanByteString args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_LessThanByteString_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_LessThanEqualsByteString_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .LessThanEqualsByteString args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_LessThanEqualsByteString_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_AppendByteString_none_of_pair_not_bytes {b a : CekValue}
    (h : ∀ bs2 bs1, ¬ (b = .VCon (.ByteString bs2) ∧ a = .VCon (.ByteString bs1))) :
    Moist.CEK.evalBuiltin .AppendByteString [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_EqualsByteString_none_of_pair_not_bytes {b a : CekValue}
    (h : ∀ bs2 bs1, ¬ (b = .VCon (.ByteString bs2) ∧ a = .VCon (.ByteString bs1))) :
    Moist.CEK.evalBuiltin .EqualsByteString [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_LessThanByteString_none_of_pair_not_bytes {b a : CekValue}
    (h : ∀ bs2 bs1, ¬ (b = .VCon (.ByteString bs2) ∧ a = .VCon (.ByteString bs1))) :
    Moist.CEK.evalBuiltin .LessThanByteString [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_LessThanEqualsByteString_none_of_pair_not_bytes {b a : CekValue}
    (h : ∀ bs2 bs1, ¬ (b = .VCon (.ByteString bs2) ∧ a = .VCon (.ByteString bs1))) :
    Moist.CEK.evalBuiltin .LessThanEqualsByteString [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_ConsByteString_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .ConsByteString cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_SliceByteString_none_of_length_ne_three {cs : List Const}
    (h : cs.length ≠ 3) :
    Moist.CEK.evalBuiltinConst .SliceByteString cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => cases c <;> cases c2 <;> rfl
          | cons c3 rest3 =>
              cases rest3 with
              | nil => exact False.elim (h rfl)
              | cons c4 rest4 =>
                  cases c <;> cases c2 <;> cases c3 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_IndexByteString_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .IndexByteString cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_ConsByteString_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .ConsByteString args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_ConsByteString_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_SliceByteString_none_of_length_ne_three {args : List CekValue}
    (h : args.length ≠ 3) :
    Moist.CEK.evalBuiltin .SliceByteString args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 3 := by
        intro hcs3
        apply h
        omega
      have hnone := evalBuiltinConst_SliceByteString_none_of_length_ne_three hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_IndexByteString_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .IndexByteString args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_IndexByteString_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_ConsByteString_none_of_pair_not_byte_int {bs n : CekValue}
    (h : ∀ bytes i, ¬ (bs = .VCon (.ByteString bytes) ∧ n = .VCon (.Integer i))) :
    Moist.CEK.evalBuiltin .ConsByteString [bs, n] = none := by
  cases bs with
  | VCon cbs =>
      cases n with
      | VCon cn =>
          cases cbs <;> cases cn <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cbs <;> rfl
      | VDelay body ρ => cases cbs <;> rfl
      | VConstr tag fields => cases cbs <;> rfl
      | VBuiltin fn args expected => cases cbs <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

theorem evalBuiltin_ConsByteString_none_of_byte_out_of_range {bs : ByteArray} {n : Int}
    (h : n < 0 ∨ 255 < n) :
    Moist.CEK.evalBuiltin .ConsByteString [.VCon (.ByteString bs), .VCon (.Integer n)] = none := by
  rcases h with hlt | hgt
  · simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
      Moist.CEK.extractConsts, Moist.CEK.evalBuiltinConst, hlt]
  · have hnlt : ¬ n < 0 := by omega
    simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
      Moist.CEK.extractConsts, Moist.CEK.evalBuiltinConst, hnlt, hgt]

set_option maxHeartbeats 0 in
theorem evalBuiltin_SliceByteString_none_of_triple_not_byte_int_int
    {bs len start : CekValue}
    (h : ∀ bytes l s,
      ¬ (bs = .VCon (.ByteString bytes) ∧
        len = .VCon (.Integer l) ∧ start = .VCon (.Integer s))) :
    Moist.CEK.evalBuiltin .SliceByteString [bs, len, start] = none := by
  cases bs with
  | VCon cbs =>
      cases len with
      | VCon clen =>
          cases start with
          | VCon cstart =>
              cases cbs <;> cases clen <;> cases cstart <;> try rfl
              exact False.elim (h _ _ _ ⟨rfl, rfl, rfl⟩)
          | VLam body ρ => cases cbs <;> cases clen <;> rfl
          | VDelay body ρ => cases cbs <;> cases clen <;> rfl
          | VConstr tag fields => cases cbs <;> cases clen <;> rfl
          | VBuiltin fn args expected => cases cbs <;> cases clen <;> rfl
      | VLam body ρ => cases cbs <;> rfl
      | VDelay body ρ => cases cbs <;> rfl
      | VConstr tag fields => cases cbs <;> rfl
      | VBuiltin fn args expected => cases cbs <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_IndexByteString_none_of_pair_not_int_byte {idx bs : CekValue}
    (h : ∀ i bytes, ¬ (idx = .VCon (.Integer i) ∧ bs = .VCon (.ByteString bytes))) :
    Moist.CEK.evalBuiltin .IndexByteString [idx, bs] = none := by
  cases idx with
  | VCon cidx =>
      cases bs with
      | VCon cbs =>
          cases cidx <;> cases cbs <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cidx <;> rfl
      | VDelay body ρ => cases cidx <;> rfl
      | VConstr tag fields => cases cidx <;> rfl
      | VBuiltin fn args expected => cases cidx <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

theorem evalBuiltin_IndexByteString_none_of_negative {bs : ByteArray} {idx : Int}
    (hidx : idx < 0) :
    Moist.CEK.evalBuiltin .IndexByteString [.VCon (.Integer idx), .VCon (.ByteString bs)] = none := by
  simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
    Moist.CEK.extractConsts, Moist.CEK.evalBuiltinConst, hidx]

theorem evalBuiltin_IndexByteString_none_of_nonnegative_out_of_range
    {bs : ByteArray} {idx : Int}
    (hidx : 0 ≤ idx) (hout : Int.ofNat bs.size ≤ idx) :
    Moist.CEK.evalBuiltin .IndexByteString [.VCon (.Integer idx), .VCon (.ByteString bs)] = none := by
  have hnlt : ¬ idx < 0 := by omega
  have hout' : (↑(ByteArray.size bs) : Int) ≤ idx := by simpa using hout
  simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
    Moist.CEK.extractConsts, Moist.CEK.evalBuiltinConst, hnlt]
  rw [if_pos hout']

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_LengthOfArray_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .LengthOfArray cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_ListToArray_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .ListToArray cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> rfl

theorem evalBuiltin_LengthOfArray_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .LengthOfArray args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_LengthOfArray_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_ListToArray_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .ListToArray args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_ListToArray_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_LengthOfArray_none_of_single_not_array {cv : CekValue}
    (h : ∀ cs, cv ≠ .VCon (.ConstArray cs)) :
    Moist.CEK.evalBuiltin .LengthOfArray [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | ConstArray cs => exact False.elim (h cs rfl)
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Data d => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

theorem evalBuiltin_ListToArray_none_of_single_not_list {cv : CekValue}
    (h : ∀ cs, cv ≠ .VCon (.ConstList cs)) :
    Moist.CEK.evalBuiltin .ListToArray [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | ConstList cs => exact False.elim (h cs rfl)
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Data d => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstArray xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_MkNilData_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .MkNilData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_MkNilPairData_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .MkNilPairData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> rfl

theorem evalBuiltin_MkNilData_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .MkNilData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_MkNilData_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_MkNilPairData_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .MkNilPairData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_MkNilPairData_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_MkNilData_none_of_single_not_unit {cv : CekValue}
    (h : cv ≠ .VCon .Unit) :
    Moist.CEK.evalBuiltin .MkNilData [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Unit => exact False.elim (h rfl)
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Bool b => rfl
      | Data d => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

theorem evalBuiltin_MkNilPairData_none_of_single_not_unit {cv : CekValue}
    (h : cv ≠ .VCon .Unit) :
    Moist.CEK.evalBuiltin .MkNilPairData [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Unit => exact False.elim (h rfl)
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Bool b => rfl
      | Data d => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_LengthOfByteString_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .LengthOfByteString cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> rfl

theorem evalBuiltin_LengthOfByteString_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .LengthOfByteString args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_LengthOfByteString_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_LengthOfByteString_none_of_single_not_bytes {cv : CekValue}
    (h : ∀ bs, cv ≠ .VCon (.ByteString bs)) :
    Moist.CEK.evalBuiltin .LengthOfByteString [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | ByteString bs => exact False.elim (h bs rfl)
      | Integer i => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Data d => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_IData_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .IData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_BData_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .BData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> rfl

theorem evalBuiltin_IData_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .IData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_IData_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_BData_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .BData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_BData_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_IData_none_of_single_not_int {cv : CekValue}
    (h : ∀ i, cv ≠ .VCon (.Integer i)) :
    Moist.CEK.evalBuiltin .IData [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Integer i => exact False.elim (h i rfl)
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Data d => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

theorem evalBuiltin_BData_none_of_single_not_bytes {cv : CekValue}
    (h : ∀ bs, cv ≠ .VCon (.ByteString bs)) :
    Moist.CEK.evalBuiltin .BData [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | ByteString bs => exact False.elim (h bs rfl)
      | Integer i => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Data d => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_MapData_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .MapData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_ListData_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .ListData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> rfl

theorem evalBuiltin_MapData_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .MapData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_MapData_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_ListData_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .ListData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_ListData_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_MapData_none_of_single_not_pair_data_list {cv : CekValue}
    (h : ∀ ps, cv ≠ .VCon (.ConstPairDataList ps)) :
    Moist.CEK.evalBuiltin .MapData [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | ConstPairDataList ps => exact False.elim (h ps rfl)
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Data d => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

theorem evalBuiltin_ListData_none_of_single_not_data_list {cv : CekValue}
    (h : ∀ ds, cv ≠ .VCon (.ConstDataList ds)) :
    Moist.CEK.evalBuiltin .ListData [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | ConstDataList ds => exact False.elim (h ds rfl)
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Data d => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_UnConstrData_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .UnConstrData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> try rfl
          case Data d => cases d <;> cases c2 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_UnMapData_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .UnMapData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> try rfl
          case Data d => cases d <;> cases c2 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_UnListData_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .UnListData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> try rfl
          case Data d => cases d <;> cases c2 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_UnIData_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .UnIData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> try rfl
          case Data d => cases d <;> cases c2 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_UnBData_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .UnBData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest =>
          cases c <;> try rfl
          case Data d => cases d <;> cases c2 <;> rfl

theorem evalBuiltin_UnConstrData_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .UnConstrData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_UnConstrData_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_UnMapData_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .UnMapData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_UnMapData_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_UnListData_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .UnListData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_UnListData_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_UnIData_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .UnIData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_UnIData_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_UnBData_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .UnBData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_UnBData_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_SerializeData_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .SerializeData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest2 =>
          cases c <;> rfl

theorem evalBuiltin_SerializeData_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .SerializeData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_SerializeData_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_SerializeData_none_of_single_not_data {cv : CekValue}
    (h : ∀ d, cv ≠ .VCon (.Data d)) :
    Moist.CEK.evalBuiltin .SerializeData [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | Data d => exact False.elim (h d rfl)
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_ComplementByteString_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .ComplementByteString cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest2 =>
          cases c <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_CountSetBits_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .CountSetBits cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest2 =>
          cases c <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_FindFirstSetBit_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .FindFirstSetBit cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest2 =>
          cases c <;> rfl

theorem evalBuiltin_ComplementByteString_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .ComplementByteString args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_ComplementByteString_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_CountSetBits_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .CountSetBits args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_CountSetBits_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_FindFirstSetBit_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .FindFirstSetBit args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_FindFirstSetBit_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_ComplementByteString_none_of_single_not_bytes {cv : CekValue}
    (h : ∀ bs, cv ≠ .VCon (.ByteString bs)) :
    Moist.CEK.evalBuiltin .ComplementByteString [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Integer i => rfl
      | ByteString bs => exact False.elim (h bs rfl)
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | Data d => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_CountSetBits_none_of_single_not_bytes {cv : CekValue}
    (h : ∀ bs, cv ≠ .VCon (.ByteString bs)) :
    Moist.CEK.evalBuiltin .CountSetBits [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Integer i => rfl
      | ByteString bs => exact False.elim (h bs rfl)
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | Data d => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_FindFirstSetBit_none_of_single_not_bytes {cv : CekValue}
    (h : ∀ bs, cv ≠ .VCon (.ByteString bs)) :
    Moist.CEK.evalBuiltin .FindFirstSetBit [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Integer i => rfl
      | ByteString bs => exact False.elim (h bs rfl)
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | Data d => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

theorem evalBuiltin_UnConstrData_none_of_single_not_constr {cv : CekValue}
    (h : ∀ tag fields, cv ≠ .VCon (.Data (.Constr tag fields))) :
    Moist.CEK.evalBuiltin .UnConstrData [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Data d =>
          cases d with
          | Constr tag fields => exact False.elim (h tag fields rfl)
          | Map ps => rfl
          | List xs => rfl
          | I i => rfl
          | B bs => rfl
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

theorem evalBuiltin_UnMapData_none_of_single_not_map {cv : CekValue}
    (h : ∀ ps, cv ≠ .VCon (.Data (.Map ps))) :
    Moist.CEK.evalBuiltin .UnMapData [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Data d =>
          cases d with
          | Constr tag fields => rfl
          | Map ps => exact False.elim (h ps rfl)
          | List xs => rfl
          | I i => rfl
          | B bs => rfl
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

theorem evalBuiltin_UnListData_none_of_single_not_list {cv : CekValue}
    (h : ∀ xs, cv ≠ .VCon (.Data (.List xs))) :
    Moist.CEK.evalBuiltin .UnListData [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Data d =>
          cases d with
          | Constr tag fields => rfl
          | Map ps => rfl
          | List xs => exact False.elim (h xs rfl)
          | I i => rfl
          | B bs => rfl
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

theorem evalBuiltin_UnIData_none_of_single_not_i {cv : CekValue}
    (h : ∀ i, cv ≠ .VCon (.Data (.I i))) :
    Moist.CEK.evalBuiltin .UnIData [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Data d =>
          cases d with
          | Constr tag fields => rfl
          | Map ps => rfl
          | List xs => rfl
          | I i => exact False.elim (h i rfl)
          | B bs => rfl
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

theorem evalBuiltin_UnBData_none_of_single_not_b {cv : CekValue}
    (h : ∀ bs, cv ≠ .VCon (.Data (.B bs))) :
    Moist.CEK.evalBuiltin .UnBData [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Data d =>
          cases d with
          | Constr tag fields => rfl
          | Map ps => rfl
          | List xs => rfl
          | I i => rfl
          | B bs => exact False.elim (h bs rfl)
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_AppendString_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .AppendString cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_EqualsString_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .EqualsString cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_AppendString_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .AppendString args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_AppendString_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_EqualsString_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .EqualsString args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_EqualsString_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_EncodeUtf8_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .EncodeUtf8 cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest2 =>
          cases c <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_DecodeUtf8_none_of_length_ne_one {cs : List Const}
    (h : cs.length ≠ 1) :
    Moist.CEK.evalBuiltinConst .DecodeUtf8 cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => exact False.elim (h rfl)
      | cons c2 rest2 =>
          cases c <;> rfl

theorem evalBuiltin_EncodeUtf8_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .EncodeUtf8 args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_EncodeUtf8_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_DecodeUtf8_none_of_length_ne_one {args : List CekValue}
    (h : args.length ≠ 1) :
    Moist.CEK.evalBuiltin .DecodeUtf8 args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 1 := by
        intro hcs1
        apply h
        omega
      have hnone := evalBuiltinConst_DecodeUtf8_none_of_length_ne_one hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_EncodeUtf8_none_of_single_not_string {cv : CekValue}
    (h : ∀ s, cv ≠ .VCon (.String s)) :
    Moist.CEK.evalBuiltin .EncodeUtf8 [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Integer i => rfl
      | ByteString bs => rfl
      | String s => exact False.elim (h s rfl)
      | Unit => rfl
      | Bool b => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | Data d => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_DecodeUtf8_none_of_single_not_bytes {cv : CekValue}
    (h : ∀ bs, cv ≠ .VCon (.ByteString bs)) :
    Moist.CEK.evalBuiltin .DecodeUtf8 [cv] = none := by
  cases cv with
  | VCon c =>
      cases c with
      | Integer i => rfl
      | ByteString bs => exact False.elim (h bs rfl)
      | String s => rfl
      | Unit => rfl
      | Bool b => rfl
      | Pair p => rfl
      | PairData p => rfl
      | ConstList xs => rfl
      | Data d => rfl
      | ConstDataList xs => rfl
      | ConstPairDataList xs => rfl
      | ConstArray xs => rfl
      | Bls12_381_G1_element => rfl
      | Bls12_381_G2_element => rfl
      | Bls12_381_MlResult => rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin b args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_DecodeUtf8_none_of_invalid {bs : ByteArray}
    (h : ¬ String.validateUTF8 bs) :
    Moist.CEK.evalBuiltin .DecodeUtf8 [.VCon (.ByteString bs)] = none := by
  change (match (if h' : String.validateUTF8 bs then
      some (Const.String (String.fromUTF8 bs h')) else none) with
    | some c => some (CekValue.VCon c)
    | none => none) = none
  by_cases hv : String.validateUTF8 bs
  · exact False.elim (h hv)
  · simp [hv]

set_option maxHeartbeats 0 in
theorem evalBuiltin_AppendString_none_of_pair_not_strings {b a : CekValue}
    (h : ∀ sb sa, ¬ (b = .VCon (.String sb) ∧ a = .VCon (.String sa))) :
    Moist.CEK.evalBuiltin .AppendString [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_EqualsString_none_of_pair_not_strings {b a : CekValue}
    (h : ∀ sb sa, ¬ (b = .VCon (.String sb) ∧ a = .VCon (.String sa))) :
    Moist.CEK.evalBuiltin .EqualsString [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_ConstrData_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .ConstrData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_EqualsData_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .EqualsData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_MkPairData_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .MkPairData cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_ConstrData_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .ConstrData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_ConstrData_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_EqualsData_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .EqualsData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_EqualsData_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

theorem evalBuiltin_MkPairData_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .MkPairData args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_MkPairData_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_ConstrData_none_of_pair_not_supported {fields tag : CekValue}
    (h : ∀ ds i,
      ¬ (fields = .VCon (.ConstDataList ds) ∧ tag = .VCon (.Integer i))) :
    Moist.CEK.evalBuiltin .ConstrData [fields, tag] = none := by
  cases fields with
  | VCon cfields =>
      cases tag with
      | VCon ctag =>
          cases cfields <;> cases ctag <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cfields <;> rfl
      | VDelay body ρ => cases cfields <;> rfl
      | VConstr ctag cfields' => cases cfields <;> rfl
      | VBuiltin fn args expected => cases cfields <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr ctag cfields' => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_EqualsData_none_of_pair_not_data {b a : CekValue}
    (h : ∀ db da, ¬ (b = .VCon (.Data db) ∧ a = .VCon (.Data da))) :
    Moist.CEK.evalBuiltin .EqualsData [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_MkPairData_none_of_pair_not_data {b a : CekValue}
    (h : ∀ db da, ¬ (b = .VCon (.Data db) ∧ a = .VCon (.Data da))) :
    Moist.CEK.evalBuiltin .MkPairData [b, a] = none := by
  cases b with
  | VCon cb =>
      cases a with
      | VCon ca =>
          cases cb <;> cases ca <;> try rfl
          exact False.elim (h _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases cb <;> rfl
      | VDelay body ρ => cases cb <;> rfl
      | VConstr tag fields => cases cb <;> rfl
      | VBuiltin fn args expected => cases cb <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

theorem evalBuiltinConst_IfThenElse_none {cs : List Const} :
    Moist.CEK.evalBuiltinConst .IfThenElse cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => rfl
          | cons c3 rest3 => rfl

theorem evalBuiltinConst_ChooseUnit_none {cs : List Const} :
    Moist.CEK.evalBuiltinConst .ChooseUnit cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => rfl
          | cons c3 rest3 => rfl

theorem evalBuiltinConst_Trace_none {cs : List Const} :
    Moist.CEK.evalBuiltinConst .Trace cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => rfl
          | cons c3 rest3 => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltin_IfThenElse_none_of_length_ne_three {args : List CekValue}
    (h : args.length ≠ 3) :
    Moist.CEK.evalBuiltin .IfThenElse args = none := by
  have hpass : Moist.CEK.evalBuiltinPassThrough .IfThenElse args = none := by
    cases args with
    | nil => rfl
    | cons elseV rest =>
        cases rest with
        | nil => rfl
        | cons thenV rest2 =>
            cases rest2 with
            | nil => rfl
            | cons cond rest3 =>
                cases rest3 with
                | nil => exact False.elim (h rfl)
                | cons extra rest4 =>
                    simp [Moist.CEK.evalBuiltinPassThrough]
  simp [Moist.CEK.evalBuiltin, hpass]
  cases hconst : Moist.CEK.extractConsts args <;>
    simp [hconst, evalBuiltinConst_IfThenElse_none]

set_option maxHeartbeats 0 in
theorem evalBuiltin_ChooseUnit_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .ChooseUnit args = none := by
  have hpass : Moist.CEK.evalBuiltinPassThrough .ChooseUnit args = none := by
    cases args with
    | nil => rfl
    | cons result rest =>
        cases rest with
        | nil => rfl
        | cons unitV rest2 =>
            cases rest2 with
            | nil => exact False.elim (h rfl)
            | cons extra rest3 =>
                simp [Moist.CEK.evalBuiltinPassThrough]
  simp [Moist.CEK.evalBuiltin, hpass]
  cases hconst : Moist.CEK.extractConsts args <;>
    simp [hconst, evalBuiltinConst_ChooseUnit_none]

set_option maxHeartbeats 0 in
theorem evalBuiltin_Trace_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .Trace args = none := by
  have hpass : Moist.CEK.evalBuiltinPassThrough .Trace args = none := by
    cases args with
    | nil => rfl
    | cons result rest =>
        cases rest with
        | nil => rfl
        | cons msg rest2 =>
            cases rest2 with
            | nil => exact False.elim (h rfl)
            | cons extra rest3 =>
                simp [Moist.CEK.evalBuiltinPassThrough]
  simp [Moist.CEK.evalBuiltin, hpass]
  cases hconst : Moist.CEK.extractConsts args <;>
    simp [hconst, evalBuiltinConst_Trace_none]

set_option maxHeartbeats 0 in
theorem evalBuiltin_IfThenElse_none_of_cond_not_bool {elseV thenV cond : CekValue}
    (h : ∀ b, cond ≠ .VCon (.Bool b)) :
    Moist.CEK.evalBuiltin .IfThenElse [elseV, thenV, cond] = none := by
  have hpass : Moist.CEK.evalBuiltinPassThrough .IfThenElse [elseV, thenV, cond] = none := by
    cases cond with
    | VCon c =>
        cases c with
        | Bool b => exact False.elim (h b rfl)
        | Integer i => rfl
        | ByteString bs => rfl
        | String s => rfl
        | Unit => rfl
        | Data d => rfl
        | Pair p => rfl
        | PairData p => rfl
        | ConstList xs => rfl
        | ConstDataList xs => rfl
        | ConstPairDataList xs => rfl
        | ConstArray xs => rfl
        | Bls12_381_G1_element => rfl
        | Bls12_381_G2_element => rfl
        | Bls12_381_MlResult => rfl
    | VLam body ρ => rfl
    | VDelay body ρ => rfl
    | VConstr tag fields => rfl
    | VBuiltin b args expected => rfl
  simp [Moist.CEK.evalBuiltin, hpass]
  cases hconst : Moist.CEK.extractConsts [elseV, thenV, cond] <;>
    simp [hconst, evalBuiltinConst_IfThenElse_none]

set_option maxHeartbeats 0 in
theorem evalBuiltin_ChooseUnit_none_of_unit_not_unit {result unitV : CekValue}
    (h : unitV ≠ .VCon .Unit) :
    Moist.CEK.evalBuiltin .ChooseUnit [result, unitV] = none := by
  have hpass : Moist.CEK.evalBuiltinPassThrough .ChooseUnit [result, unitV] = none := by
    cases unitV with
    | VCon c =>
        cases c with
        | Unit => exact False.elim (h rfl)
        | Integer i => rfl
        | ByteString bs => rfl
        | String s => rfl
        | Bool b => rfl
        | Data d => rfl
        | Pair p => rfl
        | PairData p => rfl
        | ConstList xs => rfl
        | ConstDataList xs => rfl
        | ConstPairDataList xs => rfl
        | ConstArray xs => rfl
        | Bls12_381_G1_element => rfl
        | Bls12_381_G2_element => rfl
        | Bls12_381_MlResult => rfl
    | VLam body ρ => rfl
    | VDelay body ρ => rfl
    | VConstr tag fields => rfl
    | VBuiltin b args expected => rfl
  simp [Moist.CEK.evalBuiltin, hpass]
  cases hconst : Moist.CEK.extractConsts [result, unitV] <;>
    simp [hconst, evalBuiltinConst_ChooseUnit_none]

set_option maxHeartbeats 0 in
theorem evalBuiltin_Trace_none_of_msg_not_string {result msg : CekValue}
    (h : ∀ s, msg ≠ .VCon (.String s)) :
    Moist.CEK.evalBuiltin .Trace [result, msg] = none := by
  have hpass : Moist.CEK.evalBuiltinPassThrough .Trace [result, msg] = none := by
    cases msg with
    | VCon c =>
        cases c with
        | String s => exact False.elim (h s rfl)
        | Integer i => rfl
        | ByteString bs => rfl
        | Unit => rfl
        | Bool b => rfl
        | Data d => rfl
        | Pair p => rfl
        | PairData p => rfl
        | ConstList xs => rfl
        | ConstDataList xs => rfl
        | ConstPairDataList xs => rfl
        | ConstArray xs => rfl
        | Bls12_381_G1_element => rfl
        | Bls12_381_G2_element => rfl
        | Bls12_381_MlResult => rfl
    | VLam body ρ => rfl
    | VDelay body ρ => rfl
    | VConstr tag fields => rfl
    | VBuiltin b args expected => rfl
  simp [Moist.CEK.evalBuiltin, hpass]
  cases hconst : Moist.CEK.extractConsts [result, msg] <;>
    simp [hconst, evalBuiltinConst_Trace_none]

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_DropList_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .DropList cs = none := by
  cases cs with
  | nil =>
      rfl
  | cons c rest =>
      cases rest with
      | nil =>
          cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_DropList_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .DropList args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_DropList_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_DropList_none_of_pair_not_supported {a b : CekValue}
    (hlist : ∀ cs i, ¬ (a = .VCon (.ConstList cs) ∧ b = .VCon (.Integer i)))
    (hdata : ∀ ds i, ¬ (a = .VCon (.ConstDataList ds) ∧ b = .VCon (.Integer i))) :
    Moist.CEK.evalBuiltin .DropList [a, b] = none := by
  cases a with
  | VCon ca =>
      cases b with
      | VCon cb =>
          cases ca <;> cases cb <;> try rfl
          · exact False.elim (hlist _ _ ⟨rfl, rfl⟩)
          · exact False.elim (hdata _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases ca <;> rfl
      | VDelay body ρ => cases ca <;> rfl
      | VConstr tag fields => cases ca <;> rfl
      | VBuiltin fn args expected => cases ca <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_IndexArray_none_of_length_ne_two {cs : List Const}
    (h : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst .IndexArray cs = none := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      cases rest with
      | nil => cases c <;> rfl
      | cons c2 rest2 =>
          cases rest2 with
          | nil => exact False.elim (h rfl)
          | cons c3 rest3 =>
              cases c <;> cases c2 <;> rfl

theorem evalBuiltin_IndexArray_none_of_length_ne_two {args : List CekValue}
    (h : args.length ≠ 2) :
    Moist.CEK.evalBuiltin .IndexArray args = none := by
  cases hconst : Moist.CEK.extractConsts args with
  | none =>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst]
  | some cs =>
      have hlen := extractConsts_length hconst
      have hcs : cs.length ≠ 2 := by
        intro hcs2
        apply h
        omega
      have hnone := evalBuiltinConst_IndexArray_none_of_length_ne_two hcs
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough, hconst, hnone]

set_option maxHeartbeats 0 in
theorem evalBuiltin_IndexArray_none_of_pair_not_supported {a b : CekValue}
    (hshape : ∀ i cs, ¬ (a = .VCon (.Integer i) ∧ b = .VCon (.ConstArray cs))) :
    Moist.CEK.evalBuiltin .IndexArray [a, b] = none := by
  cases a with
  | VCon ca =>
      cases b with
      | VCon cb =>
          cases ca <;> cases cb <;> try rfl
          exact False.elim (hshape _ _ ⟨rfl, rfl⟩)
      | VLam body ρ => cases ca <;> rfl
      | VDelay body ρ => cases ca <;> rfl
      | VConstr tag fields => cases ca <;> rfl
      | VBuiltin fn args expected => cases ca <;> rfl
  | VLam body ρ => rfl
  | VDelay body ρ => rfl
  | VConstr tag fields => rfl
  | VBuiltin fn args expected => rfl

theorem evalBuiltin_IndexArray_none_of_negative {cs : List Const} {i : Int}
    (hneg : i < 0) :
    Moist.CEK.evalBuiltin .IndexArray [.VCon (.Integer i), .VCon (.ConstArray cs)] = none := by
  change
    (match (if i < 0 then none else cs[i.toNat]?) with
    | some c => some (CekValue.VCon c)
    | none => none) = none
  simp [hneg]

theorem evalBuiltin_IndexArray_none_of_nonnegative_get_none {cs : List Const} {i : Int}
    (hge : 0 ≤ i) (hget : cs[i.toNat]? = none) :
    Moist.CEK.evalBuiltin .IndexArray [.VCon (.Integer i), .VCon (.ConstArray cs)] = none := by
  have hnlt : ¬ i < 0 := (Int.not_lt).mpr hge
  change
    (match (if i < 0 then none else cs[i.toNat]?) with
    | some c => some (CekValue.VCon c)
    | none => none) = none
  simp [hnlt, hget]
end Moist.SMT.UPLC.Soundness
