import Moist.CEK.Value
import Moist.CEK.Machine
import Moist.Plutus.DecidableEq

/-! # DecidableEq instances for CEK runtime values

Provides DecidableEq for the mutual `CekValue` / `CekEnv` hierarchy and,
building on that, the `Frame` / `State` types from `Moist.CEK.Machine`.
`ArgKind` and `ExpectedArgs` already derive DecidableEq in `Moist.CEK.Value`;
`Const`, `Term`, and `BuiltinFun` are handled in `Moist.Plutus.DecidableEq`.
-/

namespace Moist.CEK

open Moist.Plutus.Term (Term Const BuiltinFun)

mutual
  private def decEqCekValue : (a b : CekValue) → Decidable (a = b)
    | .VCon c1, .VCon c2 =>
      if h : c1 = c2 then isTrue (by subst h; rfl)
      else isFalse (by intro hc; cases hc; contradiction)
    | .VDelay t1 e1, .VDelay t2 e2 =>
      if h1 : t1 = t2 then
        match decEqCekEnv e1 e2 with
        | isTrue h2 => isTrue (by subst h1; subst h2; rfl)
        | isFalse h2 => isFalse (by intro hc; cases hc; contradiction)
      else isFalse (by intro hc; cases hc; contradiction)
    | .VLam t1 e1, .VLam t2 e2 =>
      if h1 : t1 = t2 then
        match decEqCekEnv e1 e2 with
        | isTrue h2 => isTrue (by subst h1; subst h2; rfl)
        | isFalse h2 => isFalse (by intro hc; cases hc; contradiction)
      else isFalse (by intro hc; cases hc; contradiction)
    | .VConstr n1 l1, .VConstr n2 l2 =>
      if h1 : n1 = n2 then
        match decEqCekValueList l1 l2 with
        | isTrue h2 => isTrue (by subst h1; subst h2; rfl)
        | isFalse h2 => isFalse (by intro hc; cases hc; contradiction)
      else isFalse (by intro hc; cases hc; contradiction)
    | .VBuiltin b1 l1 e1, .VBuiltin b2 l2 e2 =>
      if hb : b1 = b2 then
        if he : e1 = e2 then
          match decEqCekValueList l1 l2 with
          | isTrue hl => isTrue (by subst hb; subst he; subst hl; rfl)
          | isFalse hl => isFalse (by intro hc; cases hc; contradiction)
        else isFalse (by intro hc; cases hc; contradiction)
      else isFalse (by intro hc; cases hc; contradiction)
    -- Cross-constructor cases (5 constructors → 20 off-diagonal pairs)
    | .VCon _, .VDelay _ _ => isFalse (by intro h; cases h)
    | .VCon _, .VLam _ _ => isFalse (by intro h; cases h)
    | .VCon _, .VConstr _ _ => isFalse (by intro h; cases h)
    | .VCon _, .VBuiltin _ _ _ => isFalse (by intro h; cases h)
    | .VDelay _ _, .VCon _ => isFalse (by intro h; cases h)
    | .VDelay _ _, .VLam _ _ => isFalse (by intro h; cases h)
    | .VDelay _ _, .VConstr _ _ => isFalse (by intro h; cases h)
    | .VDelay _ _, .VBuiltin _ _ _ => isFalse (by intro h; cases h)
    | .VLam _ _, .VCon _ => isFalse (by intro h; cases h)
    | .VLam _ _, .VDelay _ _ => isFalse (by intro h; cases h)
    | .VLam _ _, .VConstr _ _ => isFalse (by intro h; cases h)
    | .VLam _ _, .VBuiltin _ _ _ => isFalse (by intro h; cases h)
    | .VConstr _ _, .VCon _ => isFalse (by intro h; cases h)
    | .VConstr _ _, .VDelay _ _ => isFalse (by intro h; cases h)
    | .VConstr _ _, .VLam _ _ => isFalse (by intro h; cases h)
    | .VConstr _ _, .VBuiltin _ _ _ => isFalse (by intro h; cases h)
    | .VBuiltin _ _ _, .VCon _ => isFalse (by intro h; cases h)
    | .VBuiltin _ _ _, .VDelay _ _ => isFalse (by intro h; cases h)
    | .VBuiltin _ _ _, .VLam _ _ => isFalse (by intro h; cases h)
    | .VBuiltin _ _ _, .VConstr _ _ => isFalse (by intro h; cases h)

  private def decEqCekValueList : (a b : List CekValue) → Decidable (a = b)
    | [], [] => isTrue rfl
    | x :: xs, y :: ys =>
      match decEqCekValue x y, decEqCekValueList xs ys with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro hc; cases hc; contradiction)
      | _, isFalse h => isFalse (by intro hc; cases hc; contradiction)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)

  private def decEqCekEnv : (a b : CekEnv) → Decidable (a = b)
    | .nil, .nil => isTrue rfl
    | .cons v1 r1, .cons v2 r2 =>
      match decEqCekValue v1 v2, decEqCekEnv r1 r2 with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro hc; cases hc; contradiction)
      | _, isFalse h => isFalse (by intro hc; cases hc; contradiction)
    | .nil, .cons _ _ => isFalse (by intro h; cases h)
    | .cons _ _, .nil => isFalse (by intro h; cases h)
end

instance : DecidableEq CekValue := decEqCekValue
instance : DecidableEq CekEnv := decEqCekEnv

deriving instance DecidableEq for Frame
deriving instance DecidableEq for State

end Moist.CEK
