import Test.MIR.Opt.Soundness
import Moist.MIR.Compile
import Moist.MIR.Optimize.Advanced.KnownLists

namespace Test.MIR.Opt.KnownLists

open Moist.MIR Moist.Plutus.Term Test.MIR Test.Framework

private def input := sourceVar 870
private def list := sourceVar 871
private def headBinder := sourceVar 872
private def tailBinder := sourceVar 873
private def recursive := sourceVar 874
private def accumulator := sourceVar 875
private def other := sourceVar 876
private def escape := sourceVar 877
private def bound := sourceVar 878

private def trace (message : String) (body : Expr) : Expr :=
  .App (.App (.Force (.Builtin .Trace)) (.Lit (.String message,.AtomicType .TypeString))) body

private def null (value : Expr) : Expr := .App (.Force (.Builtin .NullList)) value
private def add (a b : Expr) : Expr := .App (.App (.Builtin .AddInteger) a) b
private def unI (value : Expr) : Expr := .App (.Builtin .UnIData) value
private def unList (value : Expr) : Expr := .App (.Builtin .UnListData) value
private def unMap (value : Expr) : Expr := .App (.Builtin .UnMapData) value
private def fstPair (value : Expr) : Expr := .App (.Force (.Force (.Builtin .FstPair))) value

/-- The checked list match produced by `optimizeCheckedBranches`. -/
private def listMatch (scrutinee : VarId) (cons empty : Expr) : Expr :=
  .Case (null (.Var scrutinee))
    [.Case (.Var scrutinee) [.Lam headBinder (.Lam tailBinder cons)], empty]

private def dataList (items : List Moist.Plutus.Data) : Expr :=
  .Lit (.Data (.List items),.AtomicType .TypeData)

private def inputs : List Expr :=
  [intLit 0,intLit 3,boolLit false,.Lit (.Data (.I 3),.AtomicType .TypeData),
   .Lit (.Data (.Constr 0 []),.AtomicType .TypeData),
   .Lit (.Data (.Map [(.I 1,.I 2),(.I 3,.I 4)]),.AtomicType .TypeData),
   .Lit (.Data (.Map []),.AtomicType .TypeData),
   .Constr 0 [],.Lam escape (.Var escape)] ++
  ((List.range 6).map fun count => dataList ((List.range count).map fun n => .I (Int.ofNat n))) ++
  [dataList [.I 1,.B ByteArray.empty,.I 2]]

private def requireTerm (result : Except String Term) : IO Term :=
  match result with
  | .ok term => pure term
  | .error message => throw (IO.userError message)

private def observe (term : Term) : IO String := do
  match ← Moist.Plutus.Eval.evalTerm term
      Moist.Plutus.Eval.defaultCpuBudget Moist.Plutus.Eval.defaultMemBudget with
  | .ok result => return Moist.Plutus.Pretty.prettyTerm result.term
  | .error (kind,_,message) =>
    match kind with
    | .outOfBudget | .outOfMemory | .decodeError | .encodeError | .unboundVariable =>
      throw (IO.userError s!"Invalid observation: {kind}: {message}")
    | _ => return "failure"

private partial def countNull : Expr → Nat
  | .Builtin .NullList => 1
  | .Lam _ body | .Fix _ body | .Force body | .Delay body => countNull body
  | .App f a => countNull f + countNull a
  | .Constr _ fields => (fields.map countNull).foldl (· + ·) 0
  | .Case s alts => countNull s + (alts.map countNull).foldl (· + ·) 0
  | .Let bindings body => (bindings.map fun (_, rhs, _) => countNull rhs).foldl (· + ·) 0 + countNull body
  | _ => 0

/-- Source and optimized programs agree, including traces, on every input. -/
private def compare (label : String) (script : Expr) (arguments : List Expr := inputs) : IO Unit := do
  let raw ← requireTerm (lowerExpr script)
  let candidates ← [Advanced.fuseKnownListCases,Advanced.structural].mapM fun transform =>
    requireTerm (lowerExpr (transform script))
  let compiled ← requireTerm (compileOptimized script)
  let sizeCompiled ← requireTerm (compileOptimized script 0 0
    { shareBuiltinStates := true, poolConstants := true })
  for (argument,index) in arguments.zipIdx do
    let value ← requireTerm (lowerExpr argument)
    let original := Term.Apply raw value
    let expected ← observe original
    let expectedTrace ← Soundness.tracedObservation (liftUPLC original)
    for (candidate,variant) in (candidates ++ [compiled,sizeCompiled]).zipIdx do
      let applied := Term.Apply candidate value
      checkEq s!"{label}/{index}/{variant}/native" (← observe applied) expected
      check s!"{label}/{index}/{variant}/trace"
        ((← Soundness.tracedObservation (liftUPLC applied)) == expectedTrace)

private def fused (script : Expr) : Bool := countNull (Advanced.fuseKnownListCases script) == 0
private def kept (script : Expr) : Bool :=
  countNull (Advanced.fuseKnownListCases script) == countNull script

/-- `sum`: a recursive walker over the list of a Data argument. -/
private def sumWalker (call : Expr → Expr) (argument : Expr) : Expr :=
  .App (.Fix recursive (.Lam list (listMatch list
    (add (unI (.Var headBinder)) (call (.Var tailBinder))) (intLit 0)))) argument

def tests : TestTree := suite "known-lists" do
  test "recursive_parameters" do
    let script := Expr.Lam input (sumWalker (.App (.Var recursive)) (unList (.Var input)))
    check "single parameter fused" (fused script)
    compare "single parameter" script
    let accumulating := Expr.Lam input (.App (.App (.Fix recursive (.Lam accumulator (.Lam list
      (listMatch list (.App (.App (.Var recursive) (add (.Var accumulator) (unI (.Var headBinder))))
        (.Var tailBinder)) (.Var accumulator))))) (intLit 0)) (unList (.Var input)))
    check "accumulator then list fused" (fused accumulating)
    compare "accumulator then list" accumulating
    let listFirst := Expr.Lam input (.App (.App (.Fix recursive (.Lam list (.Lam accumulator
      (listMatch list (.App (.App (.Var recursive) (.Var tailBinder))
        (add (.Var accumulator) (unI (.Var headBinder)))) (.Var accumulator))))) (unList (.Var input)))
      (intLit 0))
    check "list then accumulator fused" (fused listFirst)
    compare "list then accumulator" listFirst
    let pairs := Expr.Lam input (.App (.Fix recursive (.Lam list (listMatch list
      (add (unI (fstPair (.Var headBinder))) (.App (.Var recursive) (.Var tailBinder))) (intLit 0))))
      (unMap (.Var input)))
    check "map entries fused" (fused pairs)
    compare "map entries" pairs
  test "let_bound_and_tail_facts" do
    let script := Expr.Lam input (.Let [(bound,unList (.Var input),false)]
      (listMatch bound (.Case (null (.Var tailBinder))
        [.Case (.Var tailBinder) [.Lam escape (.Lam other (unI (.Var escape)))],intLit 1]) (intLit 0)))
    check "let-bound list and its tail fused" (fused script)
    compare "let-bound list and tail" script
  test "unknown_or_escaping_parameters_kept" do
    let unknown := Expr.Lam input (sumWalker (.App (.Var recursive)) (.Var input))
    check "unknown external argument kept" (kept unknown)
    compare "unknown external argument" unknown
    let badCall := Expr.Lam input (sumWalker (fun _ => .App (.Var recursive) (intLit 0))
      (unList (.Var input)))
    check "non-list recursive argument kept" (kept badCall)
    compare "non-list recursive argument" badCall
    let escaping := Expr.Lam input (.App (.Fix recursive (.Lam list (listMatch list
      (.App (.Lam escape (.App (.Var escape) (.Var tailBinder))) (.Var recursive)) (intLit 0))))
      (unList (.Var input)))
    check "escaping recursive binder kept" (kept escaping)
    compare "escaping recursive binder" escaping
    let partialCall := Expr.Lam input (.App (.App (.Fix recursive (.Lam accumulator (.Lam list
      (listMatch list (.App (.Lam escape (.App (.Var escape) (.Var tailBinder)))
        (.App (.Var recursive) (.Var accumulator))) (.Var accumulator))))) (intLit 0))
      (unList (.Var input)))
    check "partially applied recursive binder kept" (kept partialCall)
    compare "partially applied recursive binder" partialCall
  test "effects_and_nested_walkers" do
    let traced := Expr.Lam input (.App (.Fix recursive (.Lam list (.Case (null (.Var list))
      [.Case (.Var list) [.Lam headBinder (.Lam tailBinder
        (trace "cons" (.App (.Var recursive) (.Var tailBinder))))], trace "nil" (intLit 0)])))
      (unList (.Var input)))
    check "traced walker fused" (fused traced)
    compare "traced walker" traced
    let nested := Expr.Lam input (.App (.Fix recursive (.Lam list (listMatch list
      (.App (.Fix other (.Lam accumulator (.Case (null (.Var accumulator))
        [.Case (.Var accumulator) [.Lam escape (.Lam bound (.App (.Var other) (.Var bound)))],
          .App (.Var recursive) (.Var tailBinder)]))) (.Var tailBinder)) (intLit 0))))
      (unList (.Var input)))
    check "nested walkers fused" (fused nested)
    compare "nested walkers" nested

end Test.MIR.Opt.KnownLists
