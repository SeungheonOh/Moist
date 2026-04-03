import Moist.Verified.FundamentalLemma

/-! # Transitivity of Behavioral Equivalence and Refinement

All transitivity theorems (`valueEq_trans`, `behEqClosed_trans`, `behEq_trans`,
`refines_trans`) are now in `Moist.Verified.FundamentalLemma`.

This file re-exports them in the `Moist.Verified.Trans` namespace for backward
compatibility. -/

namespace Moist.Verified.Trans

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified.Semantics

export Moist.Verified.Semantics (valueEq_trans listValueEq_trans
  behEqClosed_trans behEq_trans refines_trans)

end Moist.Verified.Trans
