import Moist.Onchain
import Moist.Plutus.Eval
import Moist.Plutus.Pretty
import Test.Framework

namespace Test.RecursiveEncoding

open Moist.Plutus (Data)
open Moist.Onchain Moist.Onchain.Prelude
open Moist.Plutus.Term
open Test.Framework

@[plutus_data] inductive Tree where
  | leaf : Int → Tree
  | branch : List Tree → Tree
  | unary : Tree → Tree
deriving Inhabited

partial def encodeTree : Tree → Data
  | .leaf value => .Constr 0 [.I value]
  | .branch children => .Constr 1 [.List (children.map encodeTree)]
  | .unary child => .Constr 2 [encodeTree child]

partial def decodeTree : Data → Option Tree
  | .Constr 0 [.I value] => some (.leaf value)
  | .Constr 1 [.List children] => Tree.branch <$> children.mapM decodeTree
  | .Constr 2 [child] => Tree.unary <$> decodeTree child
  | _ => none

def total (tree : Tree) : Int :=
  match tree with
  | .leaf value => value
  | .branch children => (children.map total).foldl addInteger 0
  | .unary child => total child
termination_by sizeOf tree

@[onchain] def decodeTotal (datum : Data) : Int := total (PlutusData.unsafeFromData datum)
@[onchain] def wrapTree (datum : Data) : Data :=
  let tree : Tree := PlutusData.unsafeFromData datum
  PlutusData.toData (Tree.branch [tree, .leaf 5])

private def totalScript := compile! decodeTotal
private def wrapScript := compile! wrapTree

open Lean Elab Term in
elab "recursiveRaw! " target:ident : term => do
  let name ← resolveGlobalConstNoOverload target
  let info ← getConstInfo name
  let some body := info.value? | throwError "Expected a definition"
  let expression ← Moist.Onchain.translateDefByName name body
  match Moist.MIR.lowerExpr expression with
  | .error message => throwError message
  | .ok script => return Moist.Onchain.ToExprInstances.uplcTermToExpr script

private def totalRaw := recursiveRaw! decodeTotal
private def wrapRaw := recursiveRaw! wrapTree

private def check (script : Term) (input : Data) (expected : Term) : IO Unit := do
  match ← Moist.Plutus.Eval.evalTerm (.Apply script (.Constant (.Data input, .AtomicType .TypeData))) with
  | .error error => throw (IO.userError s!"Recursive codec evaluation failed on {input}: {repr error}")
  | .ok result => unless Moist.Plutus.Pretty.prettyTerm result.term == Moist.Plutus.Pretty.prettyTerm expected do
      throw (IO.userError "Recursive codec result mismatch")

def tests : TestTree := suite "recursive_encoding" do
  test "recursive_schema_native_codec_and_compiled_traversal" do
    for depth in List.range 12 do
      let tree := (List.range depth).foldl (fun tree _ => Tree.branch [.leaf 1, .unary tree, .branch []]) (.leaf 7)
      let encoded := encodeTree tree
      unless PlutusData.toData tree == encoded do throw (IO.userError "Derived recursive encoder mismatch")
      match PlutusData.fromData encoded with
      | none => throw (IO.userError "Derived recursive decoder failed")
      | some (decoded : Tree) => unless encodeTree decoded == encoded do throw (IO.userError "Derived recursive decoder mismatch")
      match decodeTree encoded with
      | none => throw (IO.userError "Recursive native roundtrip failed")
      | some decoded => unless encodeTree decoded == encoded do throw (IO.userError "Recursive wire layout mismatch")
      for script in [totalRaw, totalScript] do
        check script encoded (.Constant (.Integer ((depth : Int) + 7), .AtomicType .TypeInteger))
      for script in [wrapRaw, wrapScript] do
        check script encoded (.Constant (.Data (.Constr 1 [.List [encoded, .Constr 0 [.I 5]]]), .AtomicType .TypeData))
  test "recursive_schema_native_decoder_rejects_bad_children" do
    for input in [Data.Constr 0 [], .Constr 1 [.List [.B ByteArray.empty]], .Constr 2 []] do
      unless (decodeTree input).isNone do throw (IO.userError "Malformed recursive schema accepted")
      unless (PlutusData.fromData input : Option Tree).isNone do
        throw (IO.userError "Derived recursive decoder accepted malformed children")

end Test.RecursiveEncoding
