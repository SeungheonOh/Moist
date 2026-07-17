import Moist.SMT.Soundness.BigEvalEndpoints

/-!
Internal proof aggregation for SMT soundness.

The implementation is split by dependency and proof responsibility:

* `Foundations` — models, value decoding, guards, and shared lemmas;
* `BuiltinSuccess` — successful builtin outcome proofs;
* `BuiltinFailureLemmas` — concrete CEK builtin rejection lemmas;
* `BuiltinFailureProofs` — symbolic builtin error soundness;
* `Simulation` — mutually dependent successful and failing symbolic evaluator
  simulations; and
* `BigEvalEndpoints` — internal big-step endpoints and regression examples.
-/
