import Moist.CEK.Machine
import Moist.CEK.Readback
import Moist.Plutus.Term
import Moist.VerifiedNewNew.Definitions
import Moist.VerifiedNewNew.Rename

/-! # Step-indexed logical-relation definitions

The two parallel towers:

* **Eq tower** (`Moist.VerifiedNewNew.Equivalence` namespace):
  `ObsRefinesK`, `ObsEqK`, `StackRelK`, `BehEqK`, `ValueEqK`, `EnvEqK`,
  `OpenEqK`, `OpenEq`.

* **Refines tower** (`Moist.VerifiedNewNew.Contextual.SoundnessRefines`
  namespace): `ValueRefinesK`, `StackRefK`, `BehRefinesK`, `EnvRefinesK`,
  `OpenRefinesK`, `OpenRefines`.

Note that `ObsRefinesK` is shared between the towers (it's a
one-directional halt/error statement on a pair of CEK states) and lives in
the Eq tower's namespace since the Eq tower was defined first.
-/

namespace Moist.VerifiedNewNew.Equivalence

open Moist.CEK
open Moist.Plutus.Term

/-! ## Step-indexed observations -/

/-- One-way step-indexed observation: halt preservation within k steps and
    error preservation within k steps (including n = 0, i.e. `s₁ = .error`).
    Building block for `ObsEqK` (two-way) and
    `Contextual.SoundnessRefines.ObsRefinesK`. -/
def ObsRefinesK (k : Nat) (s₁ s₂ : State) : Prop :=
  (∀ v, (∃ n ≤ k, steps n s₁ = .halt v) → ∃ v', Reaches s₂ (.halt v')) ∧
  (∀ n ≤ k, steps n s₁ = .error → Reaches s₂ .error)

/-- Bounded observation: both halt (within k steps) and error (within k
    positive steps) behavior preserved in both directions. -/
def ObsEqK (k : Nat) (s₁ s₂ : State) : Prop :=
  ObsRefinesK k s₁ s₂ ∧ ObsRefinesK k s₂ s₁

/-! ## Kripke-monotone lifting operators (Eq tower) -/

def StackRelK (V : Nat → CekValue → CekValue → Prop) (k : Nat) (π₁ π₂ : Stack) : Prop :=
  ∀ j ≤ k, ∀ v₁ v₂, V j v₁ v₂ → ObsEqK j (.ret π₁ v₁) (.ret π₂ v₂)

def BehEqK (V : Nat → CekValue → CekValue → Prop) (k : Nat)
    (ρ₁ ρ₂ : CekEnv) (t₁ t₂ : Term) : Prop :=
  ∀ j ≤ k, ∀ π₁ π₂, StackRelK V j π₁ π₂ →
    ObsEqK j (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂)

/-! ## ValueEqK — the step-indexed value relation

At level 0 we enforce shape matching and VCon content equality —
otherwise `evalBuiltin_compat` at `k = 0` would not hold, because
level-0 args carrying no information would fail to force matching
`extractConsts`/`evalBuiltinConst` outputs on both sides. -/
def ValueEqK : Nat → CekValue → CekValue → Prop
  | 0, .VCon c₁, .VCon c₂ => c₁ = c₂
  | 0, .VLam _ _, .VLam _ _ => True
  | 0, .VDelay _ _, .VDelay _ _ => True
  | 0, .VConstr tag₁ _, .VConstr tag₂ _ => tag₁ = tag₂
  | 0, .VBuiltin b₁ _ exp₁, .VBuiltin b₂ _ exp₂ => b₁ = b₂ ∧ exp₁ = exp₂
  | _ + 1, .VCon c₁, .VCon c₂ => c₁ = c₂
  | k + 1, .VLam b₁ ρ₁, .VLam b₂ ρ₂ =>
      ∀ j ≤ k, ∀ arg₁ arg₂, ValueEqK j arg₁ arg₂ →
        ∀ i ≤ j, ∀ π₁ π₂,
          (∀ i' ≤ i, ∀ w₁ w₂, ValueEqK i' w₁ w₂ → ObsEqK i' (.ret π₁ w₁) (.ret π₂ w₂)) →
          ObsEqK i (.compute π₁ (ρ₁.extend arg₁) b₁) (.compute π₂ (ρ₂.extend arg₂) b₂)
  | k + 1, .VDelay b₁ ρ₁, .VDelay b₂ ρ₂ =>
      ∀ j ≤ k,
        ∀ i ≤ j, ∀ π₁ π₂,
          (∀ i' ≤ i, ∀ w₁ w₂, ValueEqK i' w₁ w₂ → ObsEqK i' (.ret π₁ w₁) (.ret π₂ w₂)) →
          ObsEqK i (.compute π₁ ρ₁ b₁) (.compute π₂ ρ₂ b₂)
  | k + 1, .VConstr tag₁ fields₁, .VConstr tag₂ fields₂ =>
      tag₁ = tag₂ ∧ ListRel (ValueEqK k) fields₁ fields₂
  | k + 1, .VBuiltin b₁ args₁ exp₁, .VBuiltin b₂ args₂ exp₂ =>
      b₁ = b₂ ∧ exp₁ = exp₂ ∧ ListRel (ValueEqK k) args₁ args₂
  | _, _, _ => False

/-! ## Open-term Eq tower -/

/-- **Strict** environment equivalence: every position `1..d` resolves to a
    `some` pair of `ValueEqK`-related values. No `(none, none)` ghost branch.
    The length is implied — `lookup n = some _` at every `n ≤ d` forces
    `d ≤ ρ.length` — but we don't fix `length = d` exactly, which would over-
    constrain the soundness bridge when the context has more binders than
    `d` above the hole. This preserves the wellsizedness intent without
    coupling `d` to the CEK path depth. -/
def EnvEqK (k d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d →
    ∃ v₁ v₂, ρ₁.lookup n = some v₁ ∧
             ρ₂.lookup n = some v₂ ∧
             ValueEqK k v₁ v₂

def OpenEqK (k d : Nat) (t₁ t₂ : Term) : Prop :=
  ∀ j ≤ k, ∀ ρ₁ ρ₂, EnvEqK j d ρ₁ ρ₂ → BehEqK ValueEqK j ρ₁ ρ₂ t₁ t₂

def OpenEq (d : Nat) (t₁ t₂ : Term) : Prop := ∀ k, OpenEqK k d t₁ t₂

end Moist.VerifiedNewNew.Equivalence

namespace Moist.VerifiedNewNew.Contextual.SoundnessRefines

open Moist.CEK
open Moist.Plutus.Term
open Moist.VerifiedNewNew.Equivalence

/-! ## ValueRefinesK — `ValueEqK` recast with `ObsRefinesK` outputs

Unidirectional value relation. Mirrors `ValueEqK`'s structure but all
observation goals use `ObsRefinesK` instead of `ObsEqK`. Level 0 enforces
shape matching (and VCon content equality) so that error-preservation is
provable for `evalBuiltin_compat_refines` at k=0. -/
def ValueRefinesK : Nat → CekValue → CekValue → Prop
  | 0, .VCon c₁, .VCon c₂ => c₁ = c₂
  | 0, .VLam _ _, .VLam _ _ => True
  | 0, .VDelay _ _, .VDelay _ _ => True
  | 0, .VConstr tag₁ _, .VConstr tag₂ _ => tag₁ = tag₂
  | 0, .VBuiltin b₁ _ exp₁, .VBuiltin b₂ _ exp₂ => b₁ = b₂ ∧ exp₁ = exp₂
  | _ + 1, .VCon c₁, .VCon c₂ => c₁ = c₂
  | k + 1, .VLam b₁ ρ₁, .VLam b₂ ρ₂ =>
      ∀ j ≤ k, ∀ arg₁ arg₂, ValueRefinesK j arg₁ arg₂ →
        ∀ i ≤ j, ∀ π₁ π₂,
          (∀ i' ≤ i, ∀ w₁ w₂, ValueRefinesK i' w₁ w₂ →
            ObsRefinesK i' (.ret π₁ w₁) (.ret π₂ w₂)) →
          ObsRefinesK i (.compute π₁ (ρ₁.extend arg₁) b₁)
                        (.compute π₂ (ρ₂.extend arg₂) b₂)
  | k + 1, .VDelay b₁ ρ₁, .VDelay b₂ ρ₂ =>
      ∀ j ≤ k,
        ∀ i ≤ j, ∀ π₁ π₂,
          (∀ i' ≤ i, ∀ w₁ w₂, ValueRefinesK i' w₁ w₂ →
            ObsRefinesK i' (.ret π₁ w₁) (.ret π₂ w₂)) →
          ObsRefinesK i (.compute π₁ ρ₁ b₁) (.compute π₂ ρ₂ b₂)
  | k + 1, .VConstr tag₁ fields₁, .VConstr tag₂ fields₂ =>
      tag₁ = tag₂ ∧ ListRel (ValueRefinesK k) fields₁ fields₂
  | k + 1, .VBuiltin b₁ args₁ exp₁, .VBuiltin b₂ args₂ exp₂ =>
      b₁ = b₂ ∧ exp₁ = exp₂ ∧ ListRel (ValueRefinesK k) args₁ args₂
  | _, _, _ => False

/-! ## Kripke-monotone lifting operators (Refines tower) -/

/-- Unidirectional stack relation. -/
def StackRefK (V : Nat → CekValue → CekValue → Prop) (k : Nat) (π₁ π₂ : Stack) : Prop :=
  ∀ j ≤ k, ∀ v₁ v₂, V j v₁ v₂ → ObsRefinesK j (.ret π₁ v₁) (.ret π₂ v₂)

/-- Unidirectional behaviour relation. -/
def BehRefinesK (V : Nat → CekValue → CekValue → Prop) (k : Nat)
    (ρ₁ ρ₂ : CekEnv) (t₁ t₂ : Term) : Prop :=
  ∀ j ≤ k, ∀ π₁ π₂, StackRefK V j π₁ π₂ →
    ObsRefinesK j (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂)

/-! ## Open-term Refines tower -/

/-- Unidirectional env relation: mirrors the relaxed `EnvEqK` — strict
    some/some match within `1..d` but no length equality. -/
def EnvRefinesK (k d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d →
    ∃ v₁ v₂, ρ₁.lookup n = some v₁ ∧
             ρ₂.lookup n = some v₂ ∧
             ValueRefinesK k v₁ v₂

/-- Unidirectional open term relation at fixed step index. -/
def OpenRefinesK (k d : Nat) (t₁ t₂ : Term) : Prop :=
  ∀ j ≤ k, ∀ ρ₁ ρ₂, EnvRefinesK j d ρ₁ ρ₂ → BehRefinesK ValueRefinesK j ρ₁ ρ₂ t₁ t₂

/-- Unidirectional open term relation at unbounded step index. -/
def OpenRefines (d : Nat) (t₁ t₂ : Term) : Prop := ∀ k, OpenRefinesK k d t₁ t₂

end Moist.VerifiedNewNew.Contextual.SoundnessRefines
