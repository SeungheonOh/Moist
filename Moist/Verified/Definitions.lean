import Moist.CEK.Machine
import Moist.CEK.Readback
import Moist.Plutus.Term

/-! # Core semantic primitives shared across all Verified modules

This file hosts the three primitive definitions used everywhere:

* `steps` — n-step CEK execution.
* `Reaches` — unbounded reachability on CEK states.
* `ListRel` — pointwise lift of a binary relation to lists.

Namespace `Moist.Verified.Equivalence` is retained for historical
compatibility — callers doing `open Moist.Verified.Equivalence` still
find these names.
-/

namespace Moist.Verified.Equivalence

open Moist.CEK
open Moist.Plutus.Term

/-- n-step CEK execution. -/
def steps : Nat → State → State
  | 0, s => s
  | n + 1, s => steps n (step s)

/-- Reachability: `s` can reach `s'` in some finite number of CEK steps. -/
def Reaches (s s' : State) : Prop := ∃ n : Nat, steps n s = s'

theorem steps_error : ∀ n, steps n .error = .error
  | 0 => rfl
  | n + 1 => steps_error n

theorem steps_halt : ∀ n (v : CekValue), steps n (.halt v) = .halt v
  | 0, _ => rfl
  | n + 1, v => steps_halt n v

/-- Step counts compose. Protected: several proof files carry a local
    `steps_trans` and open this namespace. -/
protected theorem steps_trans (m n : Nat) (s : State) :
    steps (m + n) s = steps n (steps m s) := by
  induction m generalizing s with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih => rw [Nat.succ_add]; exact ih (step s)

/-- Pointwise lift of a binary relation to lists. -/
def ListRel (R : α → α → Prop) : List α → List α → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ ListRel R as bs
  | _, _ => False

end Moist.Verified.Equivalence
