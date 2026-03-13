import Moist.MIR.Expr
import Moist.MIR.Analysis

namespace Moist.MIR

/-! # ANF Normalization

Transforms arbitrary MIR into A-Normal Form by inserting Let bindings
for non-atomic sub-expressions in argument positions.

Produces maximally flat Let blocks: bindings from nested Lets are hoisted
to a single flat binding list wherever scoping allows.
-/

def anfAtom (e : Expr) : FreshM (Expr × List (VarId × Expr × Bool)) := do
  if e.isAtom then
    pure (e, [])
  else
    match e with
    | .Let binds body =>
      if body.isAtom then
        pure (body, binds)
      else
        let v ← freshVar "anf"
        pure (.Var v, binds ++ [(v, body, false)])
    | _ =>
      let v ← freshVar "anf"
      pure (.Var v, [(v, e, false)])

private def wrapLet (binds : List (VarId × Expr × Bool)) (body : Expr) : Expr :=
  match binds with
  | [] => body
  | _ => .Let binds body

private def flattenLetBinds (normalized : List (VarId × Expr × Bool)) : List (VarId × Expr × Bool) :=
  normalized.foldl (fun acc (v, e', er) =>
    match e' with
    | .Let innerBinds innerBody => acc ++ innerBinds ++ [(v, innerBody, er)]
    | _ => acc ++ [(v, e', er)]) []

private def flattenLetBody (binds : List (VarId × Expr × Bool)) (body : Expr) : Expr :=
  match body with
  | .Let innerBinds innerBody => .Let (binds ++ innerBinds) innerBody
  | _ => .Let binds body

partial def anfNormalize : Expr → FreshM Expr
  | .App f x => do
    let f' ← anfNormalize f
    let x' ← anfNormalize x
    let (fAtom, fBinds) ← anfAtom f'
    let (xAtom, xBinds) ← anfAtom x'
    pure (wrapLet (fBinds ++ xBinds) (.App fAtom xAtom))

  | .Force e => do
    let e' ← anfNormalize e
    let (atom, binds) ← anfAtom e'
    pure (wrapLet binds (.Force atom))

  | .Case scrut alts => do
    let scrut' ← anfNormalize scrut
    let (atom, binds) ← anfAtom scrut'
    let alts' ← alts.mapM anfNormalize
    pure (wrapLet binds (.Case atom alts'))

  | .Constr tag args => do
    let args' ← args.mapM anfNormalize
    let results ← args'.mapM anfAtom
    let atoms := results.map Prod.fst
    let allBinds := results.foldl (fun acc (_, bs) => acc ++ bs) []
    pure (wrapLet allBinds (.Constr tag atoms))

  | .Let binds body => do
    let normalized ← binds.mapM fun (v, e, er) => do
      let e' ← anfNormalize e
      pure (v, e', er)
    let flatBinds := flattenLetBinds normalized
    let body' ← anfNormalize body
    pure (flattenLetBody flatBinds body')

  | .Fix f body => do
    let body' ← anfNormalize body
    pure (.Fix f body')

  | .Lam x body => do
    let body' ← anfNormalize body
    pure (.Lam x body')

  | .Delay e => do
    let e' ← anfNormalize e
    pure (.Delay e')

  | e => pure e

def anfNormalizeProof (e : Expr) : FreshM ANFExpr := do
  let normalized ← anfNormalize e
  match normalized.toANF? with
  | some anf => pure anf
  | none => panic! "anfNormalize bug: output is not ANF"

end Moist.MIR
