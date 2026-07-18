import Moist.SMT.Soundness.FalsePathPruning

namespace Moist.SMT.UPLC.Soundness

#check bindOut_anyOkOutcome_eq_unpruned
#check bindOut_anyErrorOutcome_eq_unpruned
#check bindOut_anyTimeoutOutcome_eq_unpruned

#guard (carryError (.bool false)).isEmpty
#guard (carryTimeout (.bool false)).isEmpty
#guard match carryError (.bool true) with
  | [Outcome.error (.bool true)] => true
  | _ => false
#guard match carryTimeout (.bool true) with
  | [Outcome.timeout (.bool true)] => true
  | _ => false

end Moist.SMT.UPLC.Soundness
