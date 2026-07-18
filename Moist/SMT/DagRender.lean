import Moist.SMT.Render
import Std.Data.HashMap
import Std.Data.HashSet

namespace Moist.SMT

/-!
# Shared SMT rendering

`Expr.render` is the small, transparent reference renderer.  This module adds
an operational renderer for large generated expressions.  It follows the
sharing already present in Lean's immutable expression graph and emits each
repeated non-atomic node once through nested SMT-LIB `let` bindings.

The pointer identities below are used only to recover that runtime DAG while
printing.  They do not participate in symbolic execution or in its soundness
proofs, and the original expression remains reachable throughout traversal.
-/

namespace Expr

structure DagRenderResult where
  text : String
  bindings : Nat
deriving Repr

private inductive DagWork where
  | visit : Expr → DagWork
  | finish : Expr → DagWork

private structure DagBinding where
  name : String
  rhs : String

private def isCompound : Expr → Bool
  | .app _ (_ :: _) | .ite .. => true
  | _ => false

private def children : Expr → List Expr
  | .app _ args => args
  | .ite c t e => [c, t, e]
  | _ => []

private unsafe def scanLoop (todo : List Expr) (seen : Std.HashSet USize)
    (refs : Std.HashMap USize Nat) (names : Std.HashSet String) :
    Std.HashMap USize Nat × Std.HashSet String :=
  match todo with
  | [] => (refs, names)
  | e :: todo =>
      let address := ptrAddrUnsafe e
      let refs := refs.insert address (refs[address]?.getD 0 + 1)
      if seen.contains address then
        scanLoop todo seen refs names
      else
        let seen := seen.insert address
        match e with
        | .sym name => scanLoop todo seen refs (names.insert name)
        | .app fn args => scanLoop (args ++ todo) seen refs (names.insert fn)
        | .ite c t f => scanLoop (c :: t :: f :: todo) seen refs names
        | _ => scanLoop todo seen refs names

private unsafe def scan (root : Expr) : Std.HashMap USize Nat × Std.HashSet String :=
  scanLoop [root] {} {} {}

private def bareDagName (id : Nat) : String := s!"moist.dag.{id}"

private def quotedDagName (id : Nat) : String := s!"|{bareDagName id}|"

private def nameAvailable (used : Std.HashSet String) (id : Nat) : Bool :=
  !used.contains (bareDagName id) && !used.contains (quotedDagName id)

/-- Find a fresh quoted SMT symbol.  The bounded search always has a spare
candidate: each rejected candidate accounts for a distinct member of `used`. -/
private def freshDagName (used : Std.HashSet String) (next : Nat) : String × Nat :=
  let offset := (List.range (used.size + 1)).find? fun offset =>
    nameAvailable used (next + offset)
  let id := next + offset.getD 0
  (quotedDagName id, id + 1)

private unsafe def shouldBind (refs : Std.HashMap USize Nat) (e : Expr) : Bool :=
  isCompound e && refs[ptrAddrUnsafe e]?.getD 0 > 1

private unsafe def renderShared (ids : Std.HashMap USize String)
    (refs : Std.HashMap USize Nat) (mayReference : Bool) (e : Expr) : String :=
  if mayReference && shouldBind refs e then
    ids[ptrAddrUnsafe e]?.getD e.render
  else
    match e with
    | .app fn [] => fn
    | .app fn args =>
        "(" ++ fn ++ " " ++
          String.intercalate " " (args.map (renderShared ids refs true)) ++ ")"
    | .ite c t f =>
        "(ite " ++ renderShared ids refs true c ++ " " ++
          renderShared ids refs true t ++ " " ++ renderShared ids refs true f ++ ")"
    | e => e.render

private unsafe def buildDagLoop (work : List DagWork)
    (refs : Std.HashMap USize Nat) (ids : Std.HashMap USize String)
    (used : Std.HashSet String) (next : Nat)
    (bindings : Array DagBinding) : Std.HashMap USize String × Array DagBinding :=
  match work with
  | [] => (ids, bindings)
  | .visit e :: work =>
      if !isCompound e then
        buildDagLoop work refs ids used next bindings
      else
        let address := ptrAddrUnsafe e
        if ids.contains address then
          buildDagLoop work refs ids used next bindings
        else if !shouldBind refs e then
          buildDagLoop ((children e).map DagWork.visit ++ work)
            refs ids used next bindings
        else
          buildDagLoop ((children e).map DagWork.visit ++ .finish e :: work)
            refs ids used next bindings
  | .finish e :: work =>
      let address := ptrAddrUnsafe e
      if ids.contains address then
        buildDagLoop work refs ids used next bindings
      else
        let (name, next) := freshDagName used next
        let used := used.insert name
        let binding : DagBinding := ⟨name, renderShared ids refs false e⟩
        buildDagLoop work refs (ids.insert address name) used next (bindings.push binding)

/--
Render an expression as a maximally shared SMT-LIB DAG.

Repeated subexpressions are bound; nodes with one incoming reference remain
inline.  The bindings are nested one at a time because SMT-LIB bindings in a single
`let` are simultaneous; nesting lets each parent refer to already emitted
children.  `bindings` is useful for regression and performance tests.
-/
unsafe def renderDagResult (expr : Expr) : DagRenderResult :=
  let root := expr
  let (refs, used) := scan root
  let (ids, bindings) := buildDagLoop [.visit root] refs {} used 0 #[]
  let opens := bindings.toList.map fun binding =>
    "(let ((" ++ binding.name ++ " " ++ binding.rhs ++ ")) "
  let closes := List.replicate bindings.size ")"
  ⟨String.join (opens ++ [renderShared ids refs false root] ++ closes), bindings.size⟩

unsafe def renderDag (expr : Expr) : String :=
  expr.renderDagResult.text

end Expr

namespace Command

/-- Render expression-bearing commands with `Expr.renderDag`. -/
unsafe def renderDag : Command → String
  | .defineFun name args ret body =>
      "(define-fun " ++ name ++ " (" ++
        String.intercalate " " (args.map renderBinder) ++ ") " ++
        ret.render ++ " " ++ body.renderDag ++ ")"
  | .assert e => "(assert " ++ e.renderDag ++ ")"
  | .getValue es =>
      "(get-value (" ++ String.intercalate " " (es.map Expr.renderDag) ++ "))"
  | command => command.render

end Command

namespace Script

/-- Render a script while sharing duplicate expression subtrees within each
command.  SMT command boundaries are kept intact. -/
unsafe def renderDag (script : Script) : String :=
  String.intercalate "\n" (script.commands.map Command.renderDag) ++ "\n"

end Script

end Moist.SMT
