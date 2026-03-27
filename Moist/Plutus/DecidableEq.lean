import Moist.Plutus.Term

/-! # DecidableEq instances for Plutus Term types

Provides DecidableEq for the full type hierarchy needed to decide Term equality:
AtomicType, BuiltinFun, BuiltinType/TypeOperator, Data, Const, Term.
-/

namespace Moist.Plutus.Term

open Moist.Plutus (Data ByteString)

-- Simple enums: deriving works directly
deriving instance DecidableEq for AtomicType
deriving instance DecidableEq for BuiltinFun

-- BuiltinType / TypeOperator: mutual inductive
mutual
  private def decEqBuiltinType : (a b : BuiltinType) → Decidable (a = b)
    | .AtomicType x, .AtomicType y =>
      if h : x = y then isTrue (by subst h; rfl)
      else isFalse (by intro hc; cases hc; contradiction)
    | .TypeOperator x, .TypeOperator y =>
      match decEqTypeOperator x y with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro hc; cases hc; contradiction)
    | .AtomicType _, .TypeOperator _ => isFalse (by intro h; cases h)
    | .TypeOperator _, .AtomicType _ => isFalse (by intro h; cases h)

  private def decEqTypeOperator : (a b : TypeOperator) → Decidable (a = b)
    | .TypeList x, .TypeList y =>
      match decEqBuiltinType x y with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro hc; cases hc; contradiction)
    | .TypePair x1 x2, .TypePair y1 y2 =>
      match decEqBuiltinType x1 y1, decEqBuiltinType x2 y2 with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro hc; cases hc; contradiction)
      | _, isFalse h => isFalse (by intro hc; cases hc; contradiction)
    | .TypeArray x, .TypeArray y =>
      match decEqBuiltinType x y with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro hc; cases hc; contradiction)
    | .TypeList _, .TypePair _ _ => isFalse (by intro h; cases h)
    | .TypeList _, .TypeArray _ => isFalse (by intro h; cases h)
    | .TypePair _ _, .TypeList _ => isFalse (by intro h; cases h)
    | .TypePair _ _, .TypeArray _ => isFalse (by intro h; cases h)
    | .TypeArray _, .TypeList _ => isFalse (by intro h; cases h)
    | .TypeArray _, .TypePair _ _ => isFalse (by intro h; cases h)
end

instance : DecidableEq BuiltinType := decEqBuiltinType
instance : DecidableEq TypeOperator := decEqTypeOperator

-- Data: recursive with List Data and List (Data × Data)
mutual
  private def decEqData : (a b : Data) → Decidable (a = b)
    | .Constr i1 l1, .Constr i2 l2 =>
      if h1 : i1 = i2 then
        match decEqDataList l1 l2 with
        | isTrue h2 => isTrue (by subst h1; subst h2; rfl)
        | isFalse h2 => isFalse (by intro hc; cases hc; contradiction)
      else isFalse (by intro hc; cases hc; contradiction)
    | .Map m1, .Map m2 =>
      match decEqDataPairList m1 m2 with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro hc; cases hc; contradiction)
    | .List l1, .List l2 =>
      match decEqDataList l1 l2 with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro hc; cases hc; contradiction)
    | .I i1, .I i2 =>
      if h : i1 = i2 then isTrue (by subst h; rfl)
      else isFalse (by intro hc; cases hc; contradiction)
    | .B b1, .B b2 =>
      if h : b1 = b2 then isTrue (by subst h; rfl)
      else isFalse (by intro hc; cases hc; contradiction)
    | .Constr _ _, .Map _ => isFalse (by intro h; cases h)
    | .Constr _ _, .List _ => isFalse (by intro h; cases h)
    | .Constr _ _, .I _ => isFalse (by intro h; cases h)
    | .Constr _ _, .B _ => isFalse (by intro h; cases h)
    | .Map _, .Constr _ _ => isFalse (by intro h; cases h)
    | .Map _, .List _ => isFalse (by intro h; cases h)
    | .Map _, .I _ => isFalse (by intro h; cases h)
    | .Map _, .B _ => isFalse (by intro h; cases h)
    | .List _, .Constr _ _ => isFalse (by intro h; cases h)
    | .List _, .Map _ => isFalse (by intro h; cases h)
    | .List _, .I _ => isFalse (by intro h; cases h)
    | .List _, .B _ => isFalse (by intro h; cases h)
    | .I _, .Constr _ _ => isFalse (by intro h; cases h)
    | .I _, .Map _ => isFalse (by intro h; cases h)
    | .I _, .List _ => isFalse (by intro h; cases h)
    | .I _, .B _ => isFalse (by intro h; cases h)
    | .B _, .Constr _ _ => isFalse (by intro h; cases h)
    | .B _, .Map _ => isFalse (by intro h; cases h)
    | .B _, .List _ => isFalse (by intro h; cases h)
    | .B _, .I _ => isFalse (by intro h; cases h)

  private def decEqDataList : (a b : List Data) → Decidable (a = b)
    | [], [] => isTrue rfl
    | x :: xs, y :: ys =>
      match decEqData x y, decEqDataList xs ys with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro hc; cases hc; contradiction)
      | _, isFalse h => isFalse (by intro hc; cases hc; contradiction)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)

  private def decEqDataPairList : (a b : List (Data × Data)) → Decidable (a = b)
    | [], [] => isTrue rfl
    | (x1, x2) :: xs, (y1, y2) :: ys =>
      match decEqData x1 y1, decEqData x2 y2, decEqDataPairList xs ys with
      | isTrue h1, isTrue h2, isTrue h3 => isTrue (by subst h1; subst h2; subst h3; rfl)
      | isFalse h, _, _ => isFalse (by intro hc; cases hc; contradiction)
      | _, isFalse h, _ => isFalse (by intro hc; cases hc; contradiction)
      | _, _, isFalse h => isFalse (by intro hc; cases hc; contradiction)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
end

instance : DecidableEq Data := decEqData

-- Const: recursive with List Const, references Data (already has DecidableEq)
mutual
  private def decEqConst : (a b : Const) → Decidable (a = b)
    | .Integer i1, .Integer i2 =>
      if h : i1 = i2 then isTrue (by subst h; rfl)
      else isFalse (by intro hc; cases hc; contradiction)
    | .ByteString b1, .ByteString b2 =>
      if h : b1 = b2 then isTrue (by subst h; rfl)
      else isFalse (by intro hc; cases hc; contradiction)
    | .String s1, .String s2 =>
      if h : s1 = s2 then isTrue (by subst h; rfl)
      else isFalse (by intro hc; cases hc; contradiction)
    | .Unit, .Unit => isTrue rfl
    | .Bool b1, .Bool b2 =>
      if h : b1 = b2 then isTrue (by subst h; rfl)
      else isFalse (by intro hc; cases hc; contradiction)
    | .ConstList l1, .ConstList l2 =>
      match decEqConstList l1 l2 with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro hc; cases hc; contradiction)
    | .ConstDataList l1, .ConstDataList l2 =>
      if h : l1 = l2 then isTrue (by subst h; rfl)
      else isFalse (by intro hc; cases hc; contradiction)
    | .ConstPairDataList l1, .ConstPairDataList l2 =>
      if h : l1 = l2 then isTrue (by subst h; rfl)
      else isFalse (by intro hc; cases hc; contradiction)
    | .Pair p1, .Pair p2 =>
      match decEqConst p1.1 p2.1, decEqConst p1.2 p2.2 with
      | isTrue h1, isTrue h2 => isTrue (by cases p1; cases p2; simp at h1 h2; subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro hc; cases hc; contradiction)
      | _, isFalse h => isFalse (by intro hc; cases hc; contradiction)
    | .PairData p1, .PairData p2 =>
      if h : p1 = p2 then isTrue (by subst h; rfl)
      else isFalse (by intro hc; cases hc; contradiction)
    | .Data d1, .Data d2 =>
      if h : d1 = d2 then isTrue (by subst h; rfl)
      else isFalse (by intro hc; cases hc; contradiction)
    | .ConstArray l1, .ConstArray l2 =>
      match decEqConstList l1 l2 with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro hc; cases hc; contradiction)
    | .Bls12_381_G1_element, .Bls12_381_G1_element => isTrue rfl
    | .Bls12_381_G2_element, .Bls12_381_G2_element => isTrue rfl
    | .Bls12_381_MlResult, .Bls12_381_MlResult => isTrue rfl
    -- Cross-constructor cases: all 15 constructors
    | .Integer _, .ByteString _ => isFalse (by intro h; cases h)
    | .Integer _, .String _ => isFalse (by intro h; cases h)
    | .Integer _, .Unit => isFalse (by intro h; cases h)
    | .Integer _, .Bool _ => isFalse (by intro h; cases h)
    | .Integer _, .ConstList _ => isFalse (by intro h; cases h)
    | .Integer _, .ConstDataList _ => isFalse (by intro h; cases h)
    | .Integer _, .ConstPairDataList _ => isFalse (by intro h; cases h)
    | .Integer _, .Pair _ => isFalse (by intro h; cases h)
    | .Integer _, .PairData _ => isFalse (by intro h; cases h)
    | .Integer _, .Data _ => isFalse (by intro h; cases h)
    | .Integer _, .ConstArray _ => isFalse (by intro h; cases h)
    | .Integer _, .Bls12_381_G1_element => isFalse (by intro h; cases h)
    | .Integer _, .Bls12_381_G2_element => isFalse (by intro h; cases h)
    | .Integer _, .Bls12_381_MlResult => isFalse (by intro h; cases h)
    | .ByteString _, .Integer _ => isFalse (by intro h; cases h)
    | .ByteString _, .String _ => isFalse (by intro h; cases h)
    | .ByteString _, .Unit => isFalse (by intro h; cases h)
    | .ByteString _, .Bool _ => isFalse (by intro h; cases h)
    | .ByteString _, .ConstList _ => isFalse (by intro h; cases h)
    | .ByteString _, .ConstDataList _ => isFalse (by intro h; cases h)
    | .ByteString _, .ConstPairDataList _ => isFalse (by intro h; cases h)
    | .ByteString _, .Pair _ => isFalse (by intro h; cases h)
    | .ByteString _, .PairData _ => isFalse (by intro h; cases h)
    | .ByteString _, .Data _ => isFalse (by intro h; cases h)
    | .ByteString _, .ConstArray _ => isFalse (by intro h; cases h)
    | .ByteString _, .Bls12_381_G1_element => isFalse (by intro h; cases h)
    | .ByteString _, .Bls12_381_G2_element => isFalse (by intro h; cases h)
    | .ByteString _, .Bls12_381_MlResult => isFalse (by intro h; cases h)
    | .String _, .Integer _ => isFalse (by intro h; cases h)
    | .String _, .ByteString _ => isFalse (by intro h; cases h)
    | .String _, .Unit => isFalse (by intro h; cases h)
    | .String _, .Bool _ => isFalse (by intro h; cases h)
    | .String _, .ConstList _ => isFalse (by intro h; cases h)
    | .String _, .ConstDataList _ => isFalse (by intro h; cases h)
    | .String _, .ConstPairDataList _ => isFalse (by intro h; cases h)
    | .String _, .Pair _ => isFalse (by intro h; cases h)
    | .String _, .PairData _ => isFalse (by intro h; cases h)
    | .String _, .Data _ => isFalse (by intro h; cases h)
    | .String _, .ConstArray _ => isFalse (by intro h; cases h)
    | .String _, .Bls12_381_G1_element => isFalse (by intro h; cases h)
    | .String _, .Bls12_381_G2_element => isFalse (by intro h; cases h)
    | .String _, .Bls12_381_MlResult => isFalse (by intro h; cases h)
    | .Unit, .Integer _ => isFalse (by intro h; cases h)
    | .Unit, .ByteString _ => isFalse (by intro h; cases h)
    | .Unit, .String _ => isFalse (by intro h; cases h)
    | .Unit, .Bool _ => isFalse (by intro h; cases h)
    | .Unit, .ConstList _ => isFalse (by intro h; cases h)
    | .Unit, .ConstDataList _ => isFalse (by intro h; cases h)
    | .Unit, .ConstPairDataList _ => isFalse (by intro h; cases h)
    | .Unit, .Pair _ => isFalse (by intro h; cases h)
    | .Unit, .PairData _ => isFalse (by intro h; cases h)
    | .Unit, .Data _ => isFalse (by intro h; cases h)
    | .Unit, .ConstArray _ => isFalse (by intro h; cases h)
    | .Unit, .Bls12_381_G1_element => isFalse (by intro h; cases h)
    | .Unit, .Bls12_381_G2_element => isFalse (by intro h; cases h)
    | .Unit, .Bls12_381_MlResult => isFalse (by intro h; cases h)
    | .Bool _, .Integer _ => isFalse (by intro h; cases h)
    | .Bool _, .ByteString _ => isFalse (by intro h; cases h)
    | .Bool _, .String _ => isFalse (by intro h; cases h)
    | .Bool _, .Unit => isFalse (by intro h; cases h)
    | .Bool _, .ConstList _ => isFalse (by intro h; cases h)
    | .Bool _, .ConstDataList _ => isFalse (by intro h; cases h)
    | .Bool _, .ConstPairDataList _ => isFalse (by intro h; cases h)
    | .Bool _, .Pair _ => isFalse (by intro h; cases h)
    | .Bool _, .PairData _ => isFalse (by intro h; cases h)
    | .Bool _, .Data _ => isFalse (by intro h; cases h)
    | .Bool _, .ConstArray _ => isFalse (by intro h; cases h)
    | .Bool _, .Bls12_381_G1_element => isFalse (by intro h; cases h)
    | .Bool _, .Bls12_381_G2_element => isFalse (by intro h; cases h)
    | .Bool _, .Bls12_381_MlResult => isFalse (by intro h; cases h)
    | .ConstList _, .Integer _ => isFalse (by intro h; cases h)
    | .ConstList _, .ByteString _ => isFalse (by intro h; cases h)
    | .ConstList _, .String _ => isFalse (by intro h; cases h)
    | .ConstList _, .Unit => isFalse (by intro h; cases h)
    | .ConstList _, .Bool _ => isFalse (by intro h; cases h)
    | .ConstList _, .ConstDataList _ => isFalse (by intro h; cases h)
    | .ConstList _, .ConstPairDataList _ => isFalse (by intro h; cases h)
    | .ConstList _, .Pair _ => isFalse (by intro h; cases h)
    | .ConstList _, .PairData _ => isFalse (by intro h; cases h)
    | .ConstList _, .Data _ => isFalse (by intro h; cases h)
    | .ConstList _, .ConstArray _ => isFalse (by intro h; cases h)
    | .ConstList _, .Bls12_381_G1_element => isFalse (by intro h; cases h)
    | .ConstList _, .Bls12_381_G2_element => isFalse (by intro h; cases h)
    | .ConstList _, .Bls12_381_MlResult => isFalse (by intro h; cases h)
    | .ConstDataList _, .Integer _ => isFalse (by intro h; cases h)
    | .ConstDataList _, .ByteString _ => isFalse (by intro h; cases h)
    | .ConstDataList _, .String _ => isFalse (by intro h; cases h)
    | .ConstDataList _, .Unit => isFalse (by intro h; cases h)
    | .ConstDataList _, .Bool _ => isFalse (by intro h; cases h)
    | .ConstDataList _, .ConstList _ => isFalse (by intro h; cases h)
    | .ConstDataList _, .ConstPairDataList _ => isFalse (by intro h; cases h)
    | .ConstDataList _, .Pair _ => isFalse (by intro h; cases h)
    | .ConstDataList _, .PairData _ => isFalse (by intro h; cases h)
    | .ConstDataList _, .Data _ => isFalse (by intro h; cases h)
    | .ConstDataList _, .ConstArray _ => isFalse (by intro h; cases h)
    | .ConstDataList _, .Bls12_381_G1_element => isFalse (by intro h; cases h)
    | .ConstDataList _, .Bls12_381_G2_element => isFalse (by intro h; cases h)
    | .ConstDataList _, .Bls12_381_MlResult => isFalse (by intro h; cases h)
    | .ConstPairDataList _, .Integer _ => isFalse (by intro h; cases h)
    | .ConstPairDataList _, .ByteString _ => isFalse (by intro h; cases h)
    | .ConstPairDataList _, .String _ => isFalse (by intro h; cases h)
    | .ConstPairDataList _, .Unit => isFalse (by intro h; cases h)
    | .ConstPairDataList _, .Bool _ => isFalse (by intro h; cases h)
    | .ConstPairDataList _, .ConstList _ => isFalse (by intro h; cases h)
    | .ConstPairDataList _, .ConstDataList _ => isFalse (by intro h; cases h)
    | .ConstPairDataList _, .Pair _ => isFalse (by intro h; cases h)
    | .ConstPairDataList _, .PairData _ => isFalse (by intro h; cases h)
    | .ConstPairDataList _, .Data _ => isFalse (by intro h; cases h)
    | .ConstPairDataList _, .ConstArray _ => isFalse (by intro h; cases h)
    | .ConstPairDataList _, .Bls12_381_G1_element => isFalse (by intro h; cases h)
    | .ConstPairDataList _, .Bls12_381_G2_element => isFalse (by intro h; cases h)
    | .ConstPairDataList _, .Bls12_381_MlResult => isFalse (by intro h; cases h)
    | .Pair _, .Integer _ => isFalse (by intro h; cases h)
    | .Pair _, .ByteString _ => isFalse (by intro h; cases h)
    | .Pair _, .String _ => isFalse (by intro h; cases h)
    | .Pair _, .Unit => isFalse (by intro h; cases h)
    | .Pair _, .Bool _ => isFalse (by intro h; cases h)
    | .Pair _, .ConstList _ => isFalse (by intro h; cases h)
    | .Pair _, .ConstDataList _ => isFalse (by intro h; cases h)
    | .Pair _, .ConstPairDataList _ => isFalse (by intro h; cases h)
    | .Pair _, .PairData _ => isFalse (by intro h; cases h)
    | .Pair _, .Data _ => isFalse (by intro h; cases h)
    | .Pair _, .ConstArray _ => isFalse (by intro h; cases h)
    | .Pair _, .Bls12_381_G1_element => isFalse (by intro h; cases h)
    | .Pair _, .Bls12_381_G2_element => isFalse (by intro h; cases h)
    | .Pair _, .Bls12_381_MlResult => isFalse (by intro h; cases h)
    | .PairData _, .Integer _ => isFalse (by intro h; cases h)
    | .PairData _, .ByteString _ => isFalse (by intro h; cases h)
    | .PairData _, .String _ => isFalse (by intro h; cases h)
    | .PairData _, .Unit => isFalse (by intro h; cases h)
    | .PairData _, .Bool _ => isFalse (by intro h; cases h)
    | .PairData _, .ConstList _ => isFalse (by intro h; cases h)
    | .PairData _, .ConstDataList _ => isFalse (by intro h; cases h)
    | .PairData _, .ConstPairDataList _ => isFalse (by intro h; cases h)
    | .PairData _, .Pair _ => isFalse (by intro h; cases h)
    | .PairData _, .Data _ => isFalse (by intro h; cases h)
    | .PairData _, .ConstArray _ => isFalse (by intro h; cases h)
    | .PairData _, .Bls12_381_G1_element => isFalse (by intro h; cases h)
    | .PairData _, .Bls12_381_G2_element => isFalse (by intro h; cases h)
    | .PairData _, .Bls12_381_MlResult => isFalse (by intro h; cases h)
    | .Data _, .Integer _ => isFalse (by intro h; cases h)
    | .Data _, .ByteString _ => isFalse (by intro h; cases h)
    | .Data _, .String _ => isFalse (by intro h; cases h)
    | .Data _, .Unit => isFalse (by intro h; cases h)
    | .Data _, .Bool _ => isFalse (by intro h; cases h)
    | .Data _, .ConstList _ => isFalse (by intro h; cases h)
    | .Data _, .ConstDataList _ => isFalse (by intro h; cases h)
    | .Data _, .ConstPairDataList _ => isFalse (by intro h; cases h)
    | .Data _, .Pair _ => isFalse (by intro h; cases h)
    | .Data _, .PairData _ => isFalse (by intro h; cases h)
    | .Data _, .ConstArray _ => isFalse (by intro h; cases h)
    | .Data _, .Bls12_381_G1_element => isFalse (by intro h; cases h)
    | .Data _, .Bls12_381_G2_element => isFalse (by intro h; cases h)
    | .Data _, .Bls12_381_MlResult => isFalse (by intro h; cases h)
    | .ConstArray _, .Integer _ => isFalse (by intro h; cases h)
    | .ConstArray _, .ByteString _ => isFalse (by intro h; cases h)
    | .ConstArray _, .String _ => isFalse (by intro h; cases h)
    | .ConstArray _, .Unit => isFalse (by intro h; cases h)
    | .ConstArray _, .Bool _ => isFalse (by intro h; cases h)
    | .ConstArray _, .ConstList _ => isFalse (by intro h; cases h)
    | .ConstArray _, .ConstDataList _ => isFalse (by intro h; cases h)
    | .ConstArray _, .ConstPairDataList _ => isFalse (by intro h; cases h)
    | .ConstArray _, .Pair _ => isFalse (by intro h; cases h)
    | .ConstArray _, .PairData _ => isFalse (by intro h; cases h)
    | .ConstArray _, .Data _ => isFalse (by intro h; cases h)
    | .ConstArray _, .Bls12_381_G1_element => isFalse (by intro h; cases h)
    | .ConstArray _, .Bls12_381_G2_element => isFalse (by intro h; cases h)
    | .ConstArray _, .Bls12_381_MlResult => isFalse (by intro h; cases h)
    | .Bls12_381_G1_element, .Integer _ => isFalse (by intro h; cases h)
    | .Bls12_381_G1_element, .ByteString _ => isFalse (by intro h; cases h)
    | .Bls12_381_G1_element, .String _ => isFalse (by intro h; cases h)
    | .Bls12_381_G1_element, .Unit => isFalse (by intro h; cases h)
    | .Bls12_381_G1_element, .Bool _ => isFalse (by intro h; cases h)
    | .Bls12_381_G1_element, .ConstList _ => isFalse (by intro h; cases h)
    | .Bls12_381_G1_element, .ConstDataList _ => isFalse (by intro h; cases h)
    | .Bls12_381_G1_element, .ConstPairDataList _ => isFalse (by intro h; cases h)
    | .Bls12_381_G1_element, .Pair _ => isFalse (by intro h; cases h)
    | .Bls12_381_G1_element, .PairData _ => isFalse (by intro h; cases h)
    | .Bls12_381_G1_element, .Data _ => isFalse (by intro h; cases h)
    | .Bls12_381_G1_element, .ConstArray _ => isFalse (by intro h; cases h)
    | .Bls12_381_G1_element, .Bls12_381_G2_element => isFalse (by intro h; cases h)
    | .Bls12_381_G1_element, .Bls12_381_MlResult => isFalse (by intro h; cases h)
    | .Bls12_381_G2_element, .Integer _ => isFalse (by intro h; cases h)
    | .Bls12_381_G2_element, .ByteString _ => isFalse (by intro h; cases h)
    | .Bls12_381_G2_element, .String _ => isFalse (by intro h; cases h)
    | .Bls12_381_G2_element, .Unit => isFalse (by intro h; cases h)
    | .Bls12_381_G2_element, .Bool _ => isFalse (by intro h; cases h)
    | .Bls12_381_G2_element, .ConstList _ => isFalse (by intro h; cases h)
    | .Bls12_381_G2_element, .ConstDataList _ => isFalse (by intro h; cases h)
    | .Bls12_381_G2_element, .ConstPairDataList _ => isFalse (by intro h; cases h)
    | .Bls12_381_G2_element, .Pair _ => isFalse (by intro h; cases h)
    | .Bls12_381_G2_element, .PairData _ => isFalse (by intro h; cases h)
    | .Bls12_381_G2_element, .Data _ => isFalse (by intro h; cases h)
    | .Bls12_381_G2_element, .ConstArray _ => isFalse (by intro h; cases h)
    | .Bls12_381_G2_element, .Bls12_381_G1_element => isFalse (by intro h; cases h)
    | .Bls12_381_G2_element, .Bls12_381_MlResult => isFalse (by intro h; cases h)
    | .Bls12_381_MlResult, .Integer _ => isFalse (by intro h; cases h)
    | .Bls12_381_MlResult, .ByteString _ => isFalse (by intro h; cases h)
    | .Bls12_381_MlResult, .String _ => isFalse (by intro h; cases h)
    | .Bls12_381_MlResult, .Unit => isFalse (by intro h; cases h)
    | .Bls12_381_MlResult, .Bool _ => isFalse (by intro h; cases h)
    | .Bls12_381_MlResult, .ConstList _ => isFalse (by intro h; cases h)
    | .Bls12_381_MlResult, .ConstDataList _ => isFalse (by intro h; cases h)
    | .Bls12_381_MlResult, .ConstPairDataList _ => isFalse (by intro h; cases h)
    | .Bls12_381_MlResult, .Pair _ => isFalse (by intro h; cases h)
    | .Bls12_381_MlResult, .PairData _ => isFalse (by intro h; cases h)
    | .Bls12_381_MlResult, .Data _ => isFalse (by intro h; cases h)
    | .Bls12_381_MlResult, .ConstArray _ => isFalse (by intro h; cases h)
    | .Bls12_381_MlResult, .Bls12_381_G1_element => isFalse (by intro h; cases h)
    | .Bls12_381_MlResult, .Bls12_381_G2_element => isFalse (by intro h; cases h)

  private def decEqConstList : (a b : List Const) → Decidable (a = b)
    | [], [] => isTrue rfl
    | x :: xs, y :: ys =>
      match decEqConst x y, decEqConstList xs ys with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro hc; cases hc; contradiction)
      | _, isFalse h => isFalse (by intro hc; cases hc; contradiction)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
end

instance : DecidableEq Const := decEqConst

-- Term: recursive with List Term
mutual
  private def decEqTerm : (a b : Term) → Decidable (a = b)
    | .Var n1, .Var n2 =>
      if h : n1 = n2 then isTrue (by subst h; rfl)
      else isFalse (by intro hc; cases hc; contradiction)
    | .Constant c1, .Constant c2 =>
      if h : c1 = c2 then isTrue (by subst h; rfl)
      else isFalse (by intro hc; cases hc; contradiction)
    | .Builtin b1, .Builtin b2 =>
      if h : b1 = b2 then isTrue (by subst h; rfl)
      else isFalse (by intro hc; cases hc; contradiction)
    | .Lam n1 t1, .Lam n2 t2 =>
      if h1 : n1 = n2 then
        match decEqTerm t1 t2 with
        | isTrue h2 => isTrue (by subst h1; subst h2; rfl)
        | isFalse h2 => isFalse (by intro hc; cases hc; contradiction)
      else isFalse (by intro hc; cases hc; contradiction)
    | .Apply f1 a1, .Apply f2 a2 =>
      match decEqTerm f1 f2, decEqTerm a1 a2 with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro hc; cases hc; contradiction)
      | _, isFalse h => isFalse (by intro hc; cases hc; contradiction)
    | .Delay t1, .Delay t2 =>
      match decEqTerm t1 t2 with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro hc; cases hc; contradiction)
    | .Force t1, .Force t2 =>
      match decEqTerm t1 t2 with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro hc; cases hc; contradiction)
    | .Constr n1 l1, .Constr n2 l2 =>
      if h1 : n1 = n2 then
        match decEqTermList l1 l2 with
        | isTrue h2 => isTrue (by subst h1; subst h2; rfl)
        | isFalse h2 => isFalse (by intro hc; cases hc; contradiction)
      else isFalse (by intro hc; cases hc; contradiction)
    | .Case s1 l1, .Case s2 l2 =>
      match decEqTerm s1 s2, decEqTermList l1 l2 with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro hc; cases hc; contradiction)
      | _, isFalse h => isFalse (by intro hc; cases hc; contradiction)
    | .Error, .Error => isTrue rfl
    -- Cross-constructor cases: all 10 constructors
    | .Var _, .Constant _ => isFalse (by intro h; cases h)
    | .Var _, .Builtin _ => isFalse (by intro h; cases h)
    | .Var _, .Lam _ _ => isFalse (by intro h; cases h)
    | .Var _, .Apply _ _ => isFalse (by intro h; cases h)
    | .Var _, .Delay _ => isFalse (by intro h; cases h)
    | .Var _, .Force _ => isFalse (by intro h; cases h)
    | .Var _, .Constr _ _ => isFalse (by intro h; cases h)
    | .Var _, .Case _ _ => isFalse (by intro h; cases h)
    | .Var _, .Error => isFalse (by intro h; cases h)
    | .Constant _, .Var _ => isFalse (by intro h; cases h)
    | .Constant _, .Builtin _ => isFalse (by intro h; cases h)
    | .Constant _, .Lam _ _ => isFalse (by intro h; cases h)
    | .Constant _, .Apply _ _ => isFalse (by intro h; cases h)
    | .Constant _, .Delay _ => isFalse (by intro h; cases h)
    | .Constant _, .Force _ => isFalse (by intro h; cases h)
    | .Constant _, .Constr _ _ => isFalse (by intro h; cases h)
    | .Constant _, .Case _ _ => isFalse (by intro h; cases h)
    | .Constant _, .Error => isFalse (by intro h; cases h)
    | .Builtin _, .Var _ => isFalse (by intro h; cases h)
    | .Builtin _, .Constant _ => isFalse (by intro h; cases h)
    | .Builtin _, .Lam _ _ => isFalse (by intro h; cases h)
    | .Builtin _, .Apply _ _ => isFalse (by intro h; cases h)
    | .Builtin _, .Delay _ => isFalse (by intro h; cases h)
    | .Builtin _, .Force _ => isFalse (by intro h; cases h)
    | .Builtin _, .Constr _ _ => isFalse (by intro h; cases h)
    | .Builtin _, .Case _ _ => isFalse (by intro h; cases h)
    | .Builtin _, .Error => isFalse (by intro h; cases h)
    | .Lam _ _, .Var _ => isFalse (by intro h; cases h)
    | .Lam _ _, .Constant _ => isFalse (by intro h; cases h)
    | .Lam _ _, .Builtin _ => isFalse (by intro h; cases h)
    | .Lam _ _, .Apply _ _ => isFalse (by intro h; cases h)
    | .Lam _ _, .Delay _ => isFalse (by intro h; cases h)
    | .Lam _ _, .Force _ => isFalse (by intro h; cases h)
    | .Lam _ _, .Constr _ _ => isFalse (by intro h; cases h)
    | .Lam _ _, .Case _ _ => isFalse (by intro h; cases h)
    | .Lam _ _, .Error => isFalse (by intro h; cases h)
    | .Apply _ _, .Var _ => isFalse (by intro h; cases h)
    | .Apply _ _, .Constant _ => isFalse (by intro h; cases h)
    | .Apply _ _, .Builtin _ => isFalse (by intro h; cases h)
    | .Apply _ _, .Lam _ _ => isFalse (by intro h; cases h)
    | .Apply _ _, .Delay _ => isFalse (by intro h; cases h)
    | .Apply _ _, .Force _ => isFalse (by intro h; cases h)
    | .Apply _ _, .Constr _ _ => isFalse (by intro h; cases h)
    | .Apply _ _, .Case _ _ => isFalse (by intro h; cases h)
    | .Apply _ _, .Error => isFalse (by intro h; cases h)
    | .Delay _, .Var _ => isFalse (by intro h; cases h)
    | .Delay _, .Constant _ => isFalse (by intro h; cases h)
    | .Delay _, .Builtin _ => isFalse (by intro h; cases h)
    | .Delay _, .Lam _ _ => isFalse (by intro h; cases h)
    | .Delay _, .Apply _ _ => isFalse (by intro h; cases h)
    | .Delay _, .Force _ => isFalse (by intro h; cases h)
    | .Delay _, .Constr _ _ => isFalse (by intro h; cases h)
    | .Delay _, .Case _ _ => isFalse (by intro h; cases h)
    | .Delay _, .Error => isFalse (by intro h; cases h)
    | .Force _, .Var _ => isFalse (by intro h; cases h)
    | .Force _, .Constant _ => isFalse (by intro h; cases h)
    | .Force _, .Builtin _ => isFalse (by intro h; cases h)
    | .Force _, .Lam _ _ => isFalse (by intro h; cases h)
    | .Force _, .Apply _ _ => isFalse (by intro h; cases h)
    | .Force _, .Delay _ => isFalse (by intro h; cases h)
    | .Force _, .Constr _ _ => isFalse (by intro h; cases h)
    | .Force _, .Case _ _ => isFalse (by intro h; cases h)
    | .Force _, .Error => isFalse (by intro h; cases h)
    | .Constr _ _, .Var _ => isFalse (by intro h; cases h)
    | .Constr _ _, .Constant _ => isFalse (by intro h; cases h)
    | .Constr _ _, .Builtin _ => isFalse (by intro h; cases h)
    | .Constr _ _, .Lam _ _ => isFalse (by intro h; cases h)
    | .Constr _ _, .Apply _ _ => isFalse (by intro h; cases h)
    | .Constr _ _, .Delay _ => isFalse (by intro h; cases h)
    | .Constr _ _, .Force _ => isFalse (by intro h; cases h)
    | .Constr _ _, .Case _ _ => isFalse (by intro h; cases h)
    | .Constr _ _, .Error => isFalse (by intro h; cases h)
    | .Case _ _, .Var _ => isFalse (by intro h; cases h)
    | .Case _ _, .Constant _ => isFalse (by intro h; cases h)
    | .Case _ _, .Builtin _ => isFalse (by intro h; cases h)
    | .Case _ _, .Lam _ _ => isFalse (by intro h; cases h)
    | .Case _ _, .Apply _ _ => isFalse (by intro h; cases h)
    | .Case _ _, .Delay _ => isFalse (by intro h; cases h)
    | .Case _ _, .Force _ => isFalse (by intro h; cases h)
    | .Case _ _, .Constr _ _ => isFalse (by intro h; cases h)
    | .Case _ _, .Error => isFalse (by intro h; cases h)
    | .Error, .Var _ => isFalse (by intro h; cases h)
    | .Error, .Constant _ => isFalse (by intro h; cases h)
    | .Error, .Builtin _ => isFalse (by intro h; cases h)
    | .Error, .Lam _ _ => isFalse (by intro h; cases h)
    | .Error, .Apply _ _ => isFalse (by intro h; cases h)
    | .Error, .Delay _ => isFalse (by intro h; cases h)
    | .Error, .Force _ => isFalse (by intro h; cases h)
    | .Error, .Constr _ _ => isFalse (by intro h; cases h)
    | .Error, .Case _ _ => isFalse (by intro h; cases h)

  private def decEqTermList : (a b : List Term) → Decidable (a = b)
    | [], [] => isTrue rfl
    | x :: xs, y :: ys =>
      match decEqTerm x y, decEqTermList xs ys with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro hc; cases hc; contradiction)
      | _, isFalse h => isFalse (by intro hc; cases hc; contradiction)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
end

instance : DecidableEq Term := decEqTerm

end Moist.Plutus.Term
