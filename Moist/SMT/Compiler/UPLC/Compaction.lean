import Moist.SMT.Compiler.UPLC.SymbolicValue

/-!
# UPLC compiler outcome compaction

Executable joining and pruning of path-conditioned symbolic outcomes.
Soundness certificates for these transformations live outside the compiler.
-/

namespace Moist.SMT.UPLC

/-! ## Outcome compaction

Lazy UPLC conditionals select delays and are forced immediately by compiled
programs.  Without compaction, every force materializes one outcome for every
symbolic branch and later continuations duplicate once for each of them.

Successful values of the same first-order representation are packed with
nested `ite`s, guarded by the disjunction of their path conditions.  Native
list sorts remain native instead of being round-tripped through the generic
`Val` datatype.  Non-encodable (higher-order) values are left untouched.
Error and timeout paths carry no value and are coalesced by disjunction.
-/

abbrev EncodedOk := SExpr × SExpr

/-- The first-order representations that can be compacted at a force join.
Keeping their SMT sorts separate is operationally important: a list
that is packed through the generic `Val` datatype must otherwise be tested and
projected again at every subsequent list builtin.  The same native-sort rule
lets recursive predicates and folds join Boolean and integer branches without
rebuilding an exponentially large `List Outcome`. -/
inductive CompactKind where
  | integer
  | bool
  | unit
  | bytes
  | string
  | data
  | constList
  | dataList
  | pairDataList
  | array
  | dyn
deriving Repr, BEq

namespace CompactKind

def encode? : CompactKind → SymVal → Option SExpr
  | .integer, .const (.integer i) => some i
  | .bool, .const (.bool b) => some b
  | .unit, .const .unit => some .trueE
  | .bytes, .const (.bytes b) => some b
  | .string, .const (.string s) => some s
  | .data, .const (.data d) => some d
  | .constList, .const (.constList xs _) => some xs
  | .dataList, .const (.dataList xs) => some xs
  | .pairDataList, .const (.pairDataList xs) => some xs
  | .array, .const (.array xs) => some xs
  | .dyn, .dyn e => some e
  | _, _ => none

def decode : CompactKind → SExpr → SymVal
  | .integer, e => .const (.integer e)
  | .bool, e => .const (.bool e)
  | .unit, _ => .const .unit
  | .bytes, e => .const (.bytes e)
  | .string, e => .const (.string e)
  | .data, e => .const (.data e)
  | .constList, e => .const (.constList e .unknown)
  | .dataList, e => .const (.dataList e)
  | .pairDataList, e => .const (.pairDataList e)
  | .array, e => .const (.array e)
  | .dyn, e => .dyn e

end CompactKind

def compactKind? : SymVal → Option CompactKind
  | .const (.integer _) => some .integer
  | .const (.bool _) => some .bool
  | .const .unit => some .unit
  | .const (.bytes _) => some .bytes
  | .const (.string _) => some .string
  | .const (.data _) => some .data
  | .const (.constList _ _) => some .constList
  | .const (.dataList _) => some .dataList
  | .const (.pairDataList _) => some .pairDataList
  | .const (.array _) => some .array
  | .dyn _ => some .dyn
  | _ => none

def encodedOks (kind : CompactKind) : List Outcome → List EncodedOk
  | [] => []
  | .ok pc v :: outs =>
      match kind.encode? v with
      | some e => (pc, e) :: encodedOks kind outs
      | none => encodedOks kind outs
  | _ :: outs => encodedOks kind outs

def nonEncodedOks : List Outcome → List Outcome
  | [] => []
  | out@(.ok _ v) :: outs =>
      match compactKind? v with
      | some _ => nonEncodedOks outs
      | none => out :: nonEncodedOks outs
  | _ :: outs => nonEncodedOks outs

def errorPcs : List Outcome → List SExpr
  | [] => []
  | .error pc :: outs => pc :: errorPcs outs
  | _ :: outs => errorPcs outs

def timeoutPcs : List Outcome → List SExpr
  | [] => []
  | .timeout pc :: outs => pc :: timeoutPcs outs
  | _ :: outs => timeoutPcs outs

/-- Merge encoded successful outcomes.  The merged path says that at least one
source path is active; the nested `ite` picks the first active source value. -/
def mergeEncodedOks : List EncodedOk → Option EncodedOk
  | [] => none
  | (pc, value) :: oks =>
      match mergeEncodedOks oks with
      | none => some (pc, value)
      | some (restPc, restValue) =>
          -- Keep the merged path and value on the same lazy discriminator.
          -- This avoids observing underspecified values in inactive selector
          -- branches in the executable SMT semantics.  If both branches are
          -- the same atomic expression, retain it directly: selecting between
          -- identical values only grows the SMT decision tree.
          some (SExpr.ite pc SExpr.trueE restPc,
            if SExpr.sameAtom value restValue then value
            else SExpr.ite pc value restValue)

structure EncodedConstListOk where
  pc : SExpr
  value : SExpr
  hint : ConstListLengthHint
deriving Repr

namespace EncodedConstListOk

def erase (ok : EncodedConstListOk) : EncodedOk := (ok.pc, ok.value)

end EncodedConstListOk

def encodedConstListOks : List Outcome → List EncodedConstListOk
  | [] => []
  | .ok pc (.const (.constList value hint)) :: outs =>
      ⟨pc, value, hint⟩ :: encodedConstListOks outs
  | _ :: outs => encodedConstListOks outs

/-- Merge constant-list outcomes while joining their cached length hints.  A
hint survives exactly when both sides report the same length; it is still
structurally rechecked before it can prune a later `ChooseList`. -/
def mergeEncodedConstListOks :
    List EncodedConstListOk → Option EncodedConstListOk
  | [] => none
  | ok :: oks =>
      match mergeEncodedConstListOks oks with
      | none => some ok
      | some rest =>
          if SExpr.sameAtom ok.value rest.value then
            some {
              pc := SExpr.ite ok.pc SExpr.trueE rest.pc
              value := ok.value
              hint := ok.hint
            }
          else
            some {
              pc := SExpr.ite ok.pc SExpr.trueE rest.pc
              value := .ite ok.pc ok.value rest.value
              hint := .ite ok.pc ok.hint rest.hint
            }

/-- Decode the merged representation with the same single dispatcher used by
the compaction certificate.  Keeping one implementation prevents the
executable join and its proof-facing decoder from drifting apart when a new
native compact kind is added. -/
def mergedDecode (kind : CompactKind) (e : SExpr) : SymVal :=
  kind.decode e

def mergedOkOutcome (kind : CompactKind) (outs : List Outcome) : List Outcome :=
  match kind with
  | .constList =>
      match mergeEncodedConstListOks (encodedConstListOks outs) with
      | none => []
      | some ok => [.ok ok.pc (.const (.constList ok.value ok.hint))]
  | kind =>
      match mergeEncodedOks (encodedOks kind outs) with
      | none => []
      | some (pc, value) => [.ok pc (mergedDecode kind value)]

def compactKinds : List CompactKind :=
  [.integer, .bool, .unit, .bytes, .string, .data, .constList, .dataList,
   .pairDataList, .array, .dyn]

def compactedOkOutcomes (outs : List Outcome) : List Outcome :=
  compactKinds.flatMap (fun kind => mergedOkOutcome kind outs) ++
    nonEncodedOks outs

def mergedErrorOutcome (outs : List Outcome) : List Outcome :=
  match errorPcs outs with
  | [] => []
  | pcs => [.error (SExpr.any pcs)]

def mergedTimeoutOutcome (outs : List Outcome) : List Outcome :=
  match timeoutPcs outs with
  | [] => []
  | pcs => [.timeout (SExpr.any pcs)]

/-- Remove outcomes whose path condition is syntactically false before a join.
Such an outcome can never be active in any SMT model, while retaining its
value would make `mergeEncodedOks` embed that dead value into an `ite` branch. -/
def pruneFalseOutcomes (outs : List Outcome) : List Outcome :=
  outs.filter fun out => !out.pc.isFalse

/-- Collapse redundant first-order branches while retaining every higher-order
branch.  This is applied at both semantic join points: `Force` for compiled
lazy `if`s and `Case` for constructor/tag alternatives. -/
def compactOutcomes (outs : List Outcome) : List Outcome :=
  let live := pruneFalseOutcomes outs
  compactedOkOutcomes live ++
    mergedErrorOutcome live ++ mergedTimeoutOutcome live


end Moist.SMT.UPLC

