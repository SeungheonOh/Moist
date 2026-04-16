import Moist.MIR.Expr
import Moist.MIR.Analysis

namespace Moist.MIR

/-! # Alpha renaming pass

Renames every `.Let` binder to a freshly generated uid from the
`FreshM` supply, so no two `.Let` binders in the whole expression
share a uid. `.Lam` / `.Fix` binders are left alone — ANF + flatten
only needs `.Let` binders to be unique, and keeping `.Lam`/`.Fix`
untouched keeps the soundness proof tractable (no interaction with
`expandFix`, no duplicated freshness accounting).

Correctness preconditions at the top level (`alphaRenameTop`):

* `s.next > maxUidExpr e` — the fresh supply is initialised strictly
  above every uid in `e`, so freshly generated uids never collide
  with existing ones.

The substitution map `subst : List (VarId × VarId)` associates an
*old* `.Let` binder uid to its *new* uid. When we traverse a `.Var w`
use site we call `substLookup subst w`, which returns the renamed
variable iff `w.uid` matches some entry. Entries are matched in
left-to-right order, so a later (inner) `.Let` binding shadows any
earlier entry with the same uid.

When we enter a `.Lam`/`.Fix` binder we do *not* rename it, but we
*do* shadow the substitution with `substShadow subst v` — this drops
any entry whose old uid equals `v.uid`, so uses of `v.uid` inside the
body are not erroneously renamed to an outer `.Let`'s target name.
-/

/-- Look up `v` in the substitution list, returning the renamed
    variable if present or `v` itself otherwise. -/
def substLookup : List (VarId × VarId) → VarId → VarId
  | [], v => v
  | (old, new) :: rest, v =>
    if old.uid = v.uid then new else substLookup rest v

/-- Remove any mapping for `v.uid` from the substitution. Used when a
    binder shadows an outer variable with the same uid. Recursive
    form (not `List.filter`) so that soundness proofs can do direct
    structural induction. -/
def substShadow : List (VarId × VarId) → VarId → List (VarId × VarId)
  | [], _ => []
  | (old, new) :: rest, v =>
    if old.uid = v.uid then substShadow rest v
    else (old, new) :: substShadow rest v

mutual

/-- Alpha-rename `e` under the current substitution. -/
def alphaRename (subst : List (VarId × VarId)) : Expr → FreshM Expr
  | .Var v => pure (.Var (substLookup subst v))
  | .Lit lit => pure (.Lit lit)
  | .Builtin b => pure (.Builtin b)
  | .Error => pure .Error
  | .Lam v body => do
    let body' ← alphaRename (substShadow subst v) body
    pure (.Lam v body')
  | .Fix v body => do
    let body' ← alphaRename (substShadow subst v) body
    pure (.Fix v body')
  | .App f x => do
    let f' ← alphaRename subst f
    let x' ← alphaRename subst x
    pure (.App f' x')
  | .Force e => do
    let e' ← alphaRename subst e
    pure (.Force e')
  | .Delay e => do
    let e' ← alphaRename subst e
    pure (.Delay e')
  | .Constr tag args => do
    let args' ← alphaRenameList subst args
    pure (.Constr tag args')
  | .Case scrut alts => do
    let scrut' ← alphaRename subst scrut
    let alts' ← alphaRenameList subst alts
    pure (.Case scrut' alts')
  | .Let binds body => do
    let (binds', subst') ← alphaRenameBinds subst binds
    let body' ← alphaRename subst' body
    pure (.Let binds' body')

def alphaRenameList (subst : List (VarId × VarId)) :
    List Expr → FreshM (List Expr)
  | [] => pure []
  | e :: rest => do
    let e' ← alphaRename subst e
    let rest' ← alphaRenameList subst rest
    pure (e' :: rest')

/-- Alpha-rename each binding in a `.Let`, returning the new binding
    list and the extended substitution (so the body can be renamed in
    the extended scope). Binding RHSs are renamed in the *current*
    substitution (before the binder itself is added), matching the
    sequential semantics of `.Let` (non-recursive bindings). -/
def alphaRenameBinds (subst : List (VarId × VarId)) :
    List (VarId × Expr × Bool) →
    FreshM (List (VarId × Expr × Bool) × List (VarId × VarId))
  | [] => pure ([], subst)
  | (v, rhs, er) :: rest => do
    let rhs' ← alphaRename subst rhs
    let v' ← freshVar v.hint
    let (rest', subst') ← alphaRenameBinds ((v, v') :: subst) rest
    pure ((v', rhs', er) :: rest', subst')

end

/-- Entry point: alpha-rename with an empty substitution. Free
    variables are preserved exactly, every binder gets a fresh uid. -/
def alphaRenameTop (e : Expr) : FreshM Expr := alphaRename [] e

end Moist.MIR
