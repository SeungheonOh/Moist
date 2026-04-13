import Moist.CEK.Machine
import Moist.CEK.Readback
import Moist.Plutus.Term

/-! # Core semantic primitives shared across all VerifiedNewNew modules

This file hosts the three primitive definitions used everywhere:

* `steps` — n-step CEK execution.
* `Reaches` — unbounded reachability on CEK states.
* `ListRel` — pointwise lift of a binary relation to lists.

Namespace `Moist.VerifiedNewNew.Equivalence` is retained for historical
compatibility — callers doing `open Moist.VerifiedNewNew.Equivalence` still
find these names.
-/

namespace Moist.VerifiedNewNew.Equivalence

open Moist.CEK
open Moist.Plutus.Term

/-- n-step CEK execution. -/
def steps : Nat → State → State
  | 0, s => s
  | n + 1, s => steps n (step s)

/-- Reachability: `s` can reach `s'` in some finite number of CEK steps. -/
def Reaches (s s' : State) : Prop := ∃ n : Nat, steps n s = s'

/-- Pointwise lift of a binary relation to lists. -/
def ListRel (R : α → α → Prop) : List α → List α → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ ListRel R as bs
  | _, _ => False

end Moist.VerifiedNewNew.Equivalence
