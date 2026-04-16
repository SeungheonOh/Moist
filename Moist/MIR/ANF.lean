import Moist.MIR.Expr
import Moist.MIR.Analysis
import Moist.MIR.AlphaRename
import Moist.MIR.LowerTotal

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
    let v ← freshVar "anf"
    pure (.Var v, [(v, e, false)])

/-- Process a list of expressions through `anfAtom`, returning the list of
    atoms and the concatenation of all generated bindings. Structural
    recursion (avoids `mapM`/`foldl` for cleaner reasoning). -/
def anfAtomList : List Expr → FreshM (List Expr × List (VarId × Expr × Bool))
  | [] => pure ([], [])
  | e :: rest => do
    let (atom, binds) ← anfAtom e
    let (atoms, restBinds) ← anfAtomList rest
    pure (atom :: atoms, binds ++ restBinds)

def wrapLet (binds : List (VarId × Expr × Bool)) (body : Expr) : Expr :=
  match binds with
  | [] => body
  | _ => .Let binds body

/-- Step function for `flattenLetBinds`: hoist one binding's `.Let`-valued
    RHS (if any) into the accumulator. -/
def flattenLetBindsStep (b : VarId × Expr × Bool)
    (rest : List (VarId × Expr × Bool)) : List (VarId × Expr × Bool) :=
  match b.2.1 with
  | .Let innerBinds innerBody => innerBinds ++ (b.1, innerBody, b.2.2) :: rest
  | _ => b :: rest

/-- Hoist nested `.Let`-valued RHSs out of a binding list so the whole
    thing is flat. For each entry `(v, .Let innerBinds innerBody, er)`,
    the inner bindings are prepended and the outer variable `v` is
    rebound to the inner head. Binding entries with non-`.Let` RHSs are
    copied through unchanged. -/
def flattenLetBinds :
    List (VarId × Expr × Bool) → List (VarId × Expr × Bool)
  | [] => []
  | b :: rest => flattenLetBindsStep b (flattenLetBinds rest)

def flattenLetBody (binds : List (VarId × Expr × Bool)) (body : Expr) : Expr :=
  match body with
  | .Let innerBinds innerBody => .Let (binds ++ innerBinds) innerBody
  | _ => .Let binds body

mutual

def anfNormalizeCore : Expr → FreshM Expr
  | .App f x => do
    let f' ← anfNormalizeCore f
    let x' ← anfNormalizeCore x
    let (fAtom, fBinds) ← anfAtom f'
    let (xAtom, xBinds) ← anfAtom x'
    pure (wrapLet (fBinds ++ xBinds) (.App fAtom xAtom))

  | .Force e => do
    let e' ← anfNormalizeCore e
    let (atom, binds) ← anfAtom e'
    pure (wrapLet binds (.Force atom))

  | .Case scrut alts => do
    let scrut' ← anfNormalizeCore scrut
    let (atom, binds) ← anfAtom scrut'
    let alts' ← anfNormalizeListCore alts
    pure (wrapLet binds (.Case atom alts'))

  | .Constr tag args => do
    let args' ← anfNormalizeListCore args
    let (atoms, allBinds) ← anfAtomList args'
    pure (wrapLet allBinds (.Constr tag atoms))

  | .Let binds body => do
    let normalized ← anfNormalizeBindsCore binds
    let body' ← anfNormalizeCore body
    pure (flattenLetBody normalized body')

  | .Fix f body => do
    let body' ← anfNormalizeCore body
    pure (.Fix f body')

  | .Lam x body => do
    let body' ← anfNormalizeCore body
    pure (.Lam x body')

  | .Delay e => do
    let e' ← anfNormalizeCore e
    pure (.Delay e')

  | e => pure e

def anfNormalizeListCore : List Expr → FreshM (List Expr)
  | [] => pure []
  | e :: rest => do
    let e' ← anfNormalizeCore e
    let rest' ← anfNormalizeListCore rest
    pure (e' :: rest')

def anfNormalizeBindsCore :
    List (VarId × Expr × Bool) → FreshM (List (VarId × Expr × Bool))
  | [] => pure []
  | (v, e, er) :: rest => do
    let e' ← anfNormalizeCore e
    let rest' ← anfNormalizeBindsCore rest
    pure ((v, e', er) :: rest')

end

def anfNormalizeProof (e : Expr) : FreshM ANFExpr := do
  let normalized ← anfNormalizeCore e
  match normalized.toANF? with
  | some anf => pure anf
  | none => panic! "anfNormalizeCore bug: output is not ANF"

/-! ## Alpha-rename + ANF + flatten pipeline

`anfNormalizeFlat` first alpha-renames all `.Let` binders to fresh uids
(so that `flattenLetBinds` can be applied without variable capture),
then runs ANF normalization (in a new fresh supply), and finally
applies `flattenLetBinds` at the top-level `.Let` *provided* a runtime
`FlattenReady` check passes. The runtime check is always expected to
succeed on pipeline outputs (because alpha-rename establishes the
unique-binder invariant), but performing it makes the soundness proof
self-contained. -/

/-- Bool-valued `FlattenReady` check, mirroring the inductive
    `FlattenReady` from `Verified/MIR/Primitives`. -/
def flattenReadyCheck (body : Expr) : List (VarId × Expr × Bool) → Bool
  | [] => true
  | (_, e, _) :: rest =>
    match e with
    | .Let ibs _ =>
      ibs.all (fun ib => !((freeVars body).contains ib.1)) &&
      ibs.all (fun ib => rest.all (fun r => !((freeVars r.2.1).contains ib.1))) &&
      flattenReadyCheck body rest
    | _ => flattenReadyCheck body rest

/-- Apply `flattenLetBinds` to a top-level `.Let` *iff* `flattenReadyCheck`
    passes. No-op otherwise. -/
def topFlatten : Expr → Expr
  | .Let binds body =>
    if flattenReadyCheck body binds then .Let (flattenLetBinds binds) body
    else .Let binds body
  | e => e

/-! ## Recursive flatten pass

`flattenAll` walks the expression and applies `topFlatten` at *every*
`.Let` node, not just the outermost. It also recurses into bindings'
RHSs so nested Lets (introduced by ANF normalisation) get flattened.

Single-pass `flattenLetBinds` leaves hoisted inner bindings unflattened
when they themselves had Let RHSs; `flattenAll` threads the flatten
through the whole tree, guarded by `flattenReadyCheck` at every Let
(so soundness is unconditional). -/

mutual

def flattenAll (e : Expr) : Expr :=
  match e with
  | .Var v => .Var v
  | .Lit lit => .Lit lit
  | .Builtin b => .Builtin b
  | .Error => .Error
  | .Lam x body => .Lam x (flattenAll body)
  | .Fix f body => .Fix f (flattenAll body)
  | .App f x => .App (flattenAll f) (flattenAll x)
  | .Force inner => .Force (flattenAll inner)
  | .Delay inner => .Delay (flattenAll inner)
  | .Constr tag args => .Constr tag (flattenAllList args)
  | .Case scrut alts => .Case (flattenAll scrut) (flattenAllList alts)
  | .Let binds body =>
    let binds' := flattenAllBinds binds
    let body' := flattenAll body
    if flattenReadyCheck body' binds' then
      .Let (flattenLetBinds binds') body'
    else
      .Let binds' body'
termination_by sizeOf e

def flattenAllList (es : List Expr) : List Expr :=
  match es with
  | [] => []
  | e :: rest => flattenAll e :: flattenAllList rest
termination_by sizeOf es

def flattenAllBinds (binds : List (VarId × Expr × Bool)) :
    List (VarId × Expr × Bool) :=
  match binds with
  | [] => []
  | (v, e, er) :: rest => (v, flattenAll e, er) :: flattenAllBinds rest
termination_by sizeOf binds

end

/-- Full pipeline: alpha-rename + ANF + recursive flatten (guarded
    by `flattenReadyCheck` at every `.Let`).

    Alpha-rename only fires when `fixCount e = 0` — alpha-rename's
    soundness proof is phrased at the `lowerTotal` level, which for
    Fix-containing expressions disagrees with `lowerTotalExpr` via the
    `expandFix` wrapper. For Fix-containing input the alpha-rename step
    is a no-op (identity), and correctness falls out of the
    ANF + flatten composition. -/
def anfNormalizeFlat (e : Expr) : Expr :=
  let renamed :=
    if fixCount e = 0 then runFresh (alphaRenameTop e) (maxUidExpr e + 1)
    else e
  let normalized := runFresh (anfNormalizeCore renamed) (maxUidExpr renamed + 1)
  flattenAll normalized

/-- **Main `anfNormalize` entry point** — the full
    alpha-rename + core ANF + flatten pipeline exposed as a `FreshM`
    computation so it can be used inside monadic optimization passes.

    The pipeline is self-contained (uses its own fresh supplies for
    alpha-rename and ANF), and we bump the caller's fresh state past
    the output's max uid so any subsequent pass sees a state that
    doesn't collide with uids introduced by this pipeline. -/
def anfNormalize (e : Expr) : FreshM Expr := do
  let result := anfNormalizeFlat e
  let s ← get
  set ({ next := max s.next (maxUidExpr result + 1) } : FreshState)
  pure result

end Moist.MIR
