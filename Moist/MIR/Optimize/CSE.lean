import Moist.MIR.Expr
import Moist.MIR.Analysis
import Moist.MIR.Optimize.Safety

namespace Moist.MIR

/-! # Common Sub-Expression Elimination

CSE reuses an earlier, dominating let-bound result when the expressions are
alpha-equivalent and reevaluation cannot emit observable trace messages.
Potential failure does not by itself prohibit reuse: a failed first
evaluation prevents reaching the duplicate. Trace, however, is observable
despite the absence of mutable state.

isRepeatable follows available function/thunk aliases conservatively.
Known nonlogging builtin calls and safe allocations remain eligible;
unknown calls, unknown forces, and potentially logging computations do not.

The seen map flows into nested scopes but never out of conditional or
deferred scopes. Entries are invalidated when their result or a free
dependency is rebound. Public traversal first establishes globally unique
binders, so replacement and later scope movement cannot capture variables.
The explicit seen argument is an internal environment of dominating bindings.

For example, repeated addInteger applications may share their result;
repeated calls to an unknown f must remain separate because f may trace.
-/

/-! ## Structural Equality

Exact structural comparison of two expression trees. Two expressions
are structurally equal iff they have identical constructors, identical
VarIds (not just alpha-equivalent), identical literals, and recursively
equal sub-expressions.

```
exprStructEq (Var x) (Var x)                     = true
exprStructEq (Var x) (Var y)                      = false  (different VarId)
exprStructEq (Lam x (Var x)) (Lam y (Var y))     = false  (different binder names)
exprStructEq (App (Var f) (Var x)) (App (Var f) (Var x))  = true
exprStructEq (Lit (Integer 1, t)) (Lit (Integer 1, t))    = true
```
-/

mutual
  def exprStructEq : Expr → Expr → Bool
    | .Var a, .Var b => a == b
    | .Lit a, .Lit b => litEq a b
    | .Builtin a, .Builtin b => a == b
    | .Error, .Error => true
    | .Lam x1 body1, .Lam x2 body2 =>
      x1 == x2 && exprStructEq body1 body2
    | .Fix f1 body1, .Fix f2 body2 =>
      f1 == f2 && exprStructEq body1 body2
    | .App f1 x1, .App f2 x2 =>
      exprStructEq f1 f2 && exprStructEq x1 x2
    | .Force e1, .Force e2 => exprStructEq e1 e2
    | .Delay e1, .Delay e2 => exprStructEq e1 e2
    | .Constr t1 args1, .Constr t2 args2 =>
      t1 == t2 && exprStructEqList args1 args2
    | .Case s1 alts1, .Case s2 alts2 =>
      exprStructEq s1 s2 && exprStructEqList alts1 alts2
    | .Let binds1 body1, .Let binds2 body2 =>
      exprStructEqBinds binds1 binds2 && exprStructEq body1 body2
    | _, _ => false
  termination_by a _ => sizeOf a

  def exprStructEqList : List Expr → List Expr → Bool
    | [], [] => true
    | a :: as_, b :: bs => exprStructEq a b && exprStructEqList as_ bs
    | _, _ => false
  termination_by as_ _ => sizeOf as_

  def exprStructEqBinds : List (VarId × Expr × Bool) → List (VarId × Expr × Bool) → Bool
    | [], [] => true
    | (x, rhs1, _) :: rest1, (y, rhs2, _) :: rest2 =>
      x == y && exprStructEq rhs1 rhs2 && exprStructEqBinds rest1 rest2
    | _, _ => false
  termination_by bs _ => sizeOf bs
end

/-- Look up an expression in the seen-map by alpha-equivalence.
Returns the variable of the first matching entry, if any.

```
lookupStructEq [(App f x, v1), (Lit 1, v2)] (Lit 1) = some v2
lookupStructEq [(App f x, v1)] (App f y)             = none
```
-/
def lookupStructEq (seen : List (Expr × VarId)) (target : Expr)
    : Option VarId :=
  match seen with
  | [] => none
  | (expr, var) :: rest =>
    if alphaEq expr target then some var
    else lookupStructEq rest target

/-! ## Seen Map Filtering

When entering a new binder scope (Lam x or Fix f), entries in the seen
map may become invalid:

1. An entry whose mapped variable equals the binder would be shadowed.
2. An entry whose RHS contains the binder as a free variable would refer
   to a different binding in the new scope.

Both cases are removed to prevent incorrect deduplication.
-/

/-- Filter the seen map when entering a Lam/Fix scope with binder `v`.
Removes entries where `v` is the mapped variable (shadowed) or appears
free in the RHS expression (would refer to a different binding). -/
def filterSeen (binder : VarId) (seen : List (Expr × VarId))
    : List (Expr × VarId) :=
  seen.filter fun (rhs, v) => v != binder && !(freeVars rhs).contains binder

/-! ## Binder Occurrence

Replacing `v` by an earlier `w` is a plain rename, so `w` must not be
rebound anywhere in the renamed scope. Binder uniqueness makes this hold
for every input the pipeline produces; the check keeps the rewrite sound
on arbitrary input. -/

mutual
  def bindsVar (w : VarId) : Expr → Bool
    | .Var _ | .Lit _ | .Builtin _ | .Error => false
    | .Lam x body | .Fix x body => x == w || bindsVar w body
    | .App f x => bindsVar w f || bindsVar w x
    | .Force e | .Delay e => bindsVar w e
    | .Constr _ args => bindsVarList w args
    | .Case scrut alts => bindsVar w scrut || bindsVarList w alts
    | .Let binds body => bindsVarLet w binds body
  termination_by e => sizeOf e

  def bindsVarList (w : VarId) : List Expr → Bool
    | [] => false
    | e :: rest => bindsVar w e || bindsVarList w rest
  termination_by es => sizeOf es

  def bindsVarLet (w : VarId) : List (VarId × Expr × Bool) → Expr → Bool
    | [], body => bindsVar w body
    | (x, rhs, _) :: rest, body => x == w || bindsVar w rhs || bindsVarLet w rest body
  termination_by binds body => sizeOf binds + sizeOf body
end

/-! ## Termination

Freshening only renames binders, so it preserves the node count that
bounds the traversal. -/

mutual
  theorem freshenBinders_nodes (environment : List (VarId × VarId)) (expression : Expr)
      (state : FreshState) : (freshenBinders environment expression state).1.nodes = expression.nodes := by
    match expression with
    | .Var _ => show (Expr.Var _).nodes = _; simp only [Expr.nodes.eq_1]
    | .Lit _ => rfl
    | .Builtin _ => rfl
    | .Error => rfl
    | .Lam binder body =>
      show (Expr.Lam _ (freshenBinders _ body _).1).nodes = _
      have inner := freshenBinders_nodes ((binder, ⟨state.next, .gen, binder.hint⟩) :: environment)
        body ⟨state.next + 1⟩
      simp only [Expr.nodes.eq_5]
      exact congrArg (1 + ·) inner
    | .Fix binder body =>
      show (Expr.Fix _ (freshenBinders _ body _).1).nodes = _
      have inner := freshenBinders_nodes ((binder, ⟨state.next, .gen, binder.hint⟩) :: environment)
        body ⟨state.next + 1⟩
      simp only [Expr.nodes.eq_6]
      exact congrArg (1 + ·) inner
    | .App function argument =>
      show (Expr.App (freshenBinders _ function _).1
        (freshenBinders _ argument (freshenBinders environment function state).2).1).nodes = _
      have first := freshenBinders_nodes environment function state
      have second := freshenBinders_nodes environment argument
        (freshenBinders environment function state).2
      simp only [Expr.nodes.eq_7]
      omega
    | .Force inner =>
      show (Expr.Force (freshenBinders _ inner _).1).nodes = _
      have result := freshenBinders_nodes environment inner state
      simp only [Expr.nodes.eq_8]
      omega
    | .Delay inner =>
      show (Expr.Delay (freshenBinders _ inner _).1).nodes = _
      have result := freshenBinders_nodes environment inner state
      simp only [Expr.nodes.eq_9]
      omega
    | .Constr tag fields =>
      show (Expr.Constr tag (freshenList _ fields _).1).nodes = _
      have result := freshenList_nodes environment fields state
      simp only [Expr.nodes.eq_10]
      omega
    | .Case scrutinee alternatives =>
      show (Expr.Case (freshenBinders _ scrutinee _).1
        (freshenList _ alternatives (freshenBinders environment scrutinee state).2).1).nodes = _
      have first := freshenBinders_nodes environment scrutinee state
      have second := freshenList_nodes environment alternatives
        (freshenBinders environment scrutinee state).2
      simp only [Expr.nodes.eq_11]
      omega
    | .Let bindings body =>
      show (Expr.Let (freshenBindings _ bindings _).1.1
        (freshenBinders (freshenBindings environment bindings state).1.2 body
          (freshenBindings environment bindings state).2).1).nodes = _
      have first := freshenBindings_nodes environment bindings state
      have second := freshenBinders_nodes (freshenBindings environment bindings state).1.2 body
        (freshenBindings environment bindings state).2
      simp only [Expr.nodes.eq_12]
      omega
  termination_by sizeOf expression

  theorem freshenList_nodes (environment : List (VarId × VarId)) (expressions : List Expr)
      (state : FreshState) :
      Expr.nodesList (freshenList environment expressions state).1 = Expr.nodesList expressions := by
    match expressions with
    | [] => rfl
    | expression :: rest =>
      show Expr.nodesList ((freshenBinders _ expression _).1 ::
        (freshenList _ rest (freshenBinders environment expression state).2).1) = _
      have first := freshenBinders_nodes environment expression state
      have second := freshenList_nodes environment rest (freshenBinders environment expression state).2
      simp only [Expr.nodesList.eq_2]
      omega
  termination_by sizeOf expressions

  theorem freshenBindings_nodes (environment : List (VarId × VarId))
      (bindings : List (VarId × Expr × Bool)) (state : FreshState) :
      Expr.nodesBinds (freshenBindings environment bindings state).1.1 = Expr.nodesBinds bindings := by
    match bindings with
    | [] => rfl
    | (binder, rhs, erased) :: rest =>
      show Expr.nodesBinds ((_, (freshenBinders _ rhs _).1, erased) ::
        (freshenBindings ((binder, ⟨(freshenBinders environment rhs state).2.next, .gen, binder.hint⟩) ::
          environment) rest ⟨(freshenBinders environment rhs state).2.next + 1⟩).1.1) = _
      have first := freshenBinders_nodes environment rhs state
      have second := freshenBindings_nodes
        ((binder, ⟨(freshenBinders environment rhs state).2.next, .gen, binder.hint⟩) :: environment)
        rest ⟨(freshenBinders environment rhs state).2.next + 1⟩
      simp only [Expr.nodesBinds.eq_2]
      omega
  termination_by sizeOf bindings
end

theorem uniqueOptimizationBinders_nodes (expression : Expr) :
    (uniqueOptimizationBinders expression).nodes = expression.nodes := by
  unfold uniqueOptimizationBinders
  split
  · rfl
  · exact freshenBinders_nodes [] expression _

/-! ## CSE Pass

`cse` performs scope-aware common sub-expression elimination over the
expression tree. The `seen` parameter carries bindings from enclosing
scopes. Returns the transformed expression paired with a flag indicating
whether any elimination was performed.

At each `Let` block, bindings are processed left-to-right: the RHS is
first CSE'd (exposing nested optimization opportunities), then checked
against the accumulated seen map. The body is processed last with the
full seen map, enabling cross-scope deduplication into case alternatives,
lambda bodies, and other nested expressions.
-/

/-- The earlier binding that a processed right-hand side can reuse, if any:
an alpha-equivalent dominating entry whose variable is not rebound in the
rest of the block. -/
def reusableBinding (seen : List (Expr × VarId)) (rhs : Expr)
    (rest : List (VarId × Expr × Bool)) (body : Expr) : Option VarId :=
  if isRepeatable seen rhs then
    match lookupStructEq seen rhs with
    | some w => if bindsVarLet w rest body then none else some w
    | none => none
  else none

/-- The seen map after keeping the binding `v = rhs`. -/
def extendSeen (seen : List (Expr × VarId)) (v : VarId) (rhs : Expr) : List (Expr × VarId) :=
  let available := filterSeen v seen
  if (freeVars rhs).contains v then available else (rhs, v) :: available

mutual
  def cse (seen : List (Expr × VarId)) (expression : Expr) : Expr × Bool :=
    match _unique : uniqueOptimizationBinders expression with
    | .Let binds body =>
      let (kept, body', changed) := cseBinds seen binds body
      match kept with
      | [] => (body', changed)
      | _ => (.Let kept body', changed)

    | .Lam x body =>
      let seen' := filterSeen x seen
      let (body', changed) := cse seen' body
      (.Lam x body', changed)

    | .Fix f body =>
      let seen' := filterSeen f seen
      let (body', changed) := cse seen' body
      (.Fix f body', changed)

    | .App f x =>
      let (f', c1) := cse seen f
      let (x', c2) := cse seen x
      (.App f' x', c1 || c2)

    | .Force e =>
      let (e', c) := cse seen e
      (.Force e', c)

    | .Delay e =>
      let (e', c) := cse seen e
      (.Delay e', c)

    | .Constr tag args =>
      let (args', c) := cseList seen args
      (.Constr tag args', c)

    | .Case scrut alts =>
      let (scrut', c1) := cse seen scrut
      let (alts', c2) := cseList seen alts
      (.Case scrut' alts', c1 || c2)

    | e => (e, false)
  termination_by expression.nodes
  decreasing_by
    all_goals
      have size := uniqueOptimizationBinders_nodes expression
      rw [_unique] at size
      simp only [Expr.nodes.eq_5, Expr.nodes.eq_6, Expr.nodes.eq_7, Expr.nodes.eq_8,
        Expr.nodes.eq_9, Expr.nodes.eq_10, Expr.nodes.eq_11, Expr.nodes.eq_12] at size
      omega

  def cseList (seen : List (Expr × VarId)) (es : List Expr) : List Expr × Bool :=
    match es with
    | [] => ([], false)
    | e :: rest =>
      let (e', c) := cse seen e
      let (rest', c') := cseList seen rest
      (e' :: rest', c || c')
  termination_by Expr.nodesList es
  decreasing_by all_goals (simp only [Expr.nodesList.eq_2]; omega)

  /-- Process the bindings of a Let block with scope-aware deduplication.

  Walks bindings left-to-right. For each binding:
  1. CSE the RHS with the current seen map (outer + previous bindings).
  2. Check if the CSE'd RHS matches any entry in the seen map.
  3. If duplicate found: rename the binding variable to the earlier one,
     drop the binding.
  4. If new: add to the seen map, keep the binding.

  After all bindings, CSE the body with the full accumulated seen map.
  This allows nested expressions (e.g. inside case alternatives) to
  deduplicate against bindings from enclosing let blocks. Returns the kept
  bindings, the processed body and the change flag. -/
  def cseBinds (seen : List (Expr × VarId)) (binds : List (VarId × Expr × Bool)) (body : Expr) :
      List (VarId × Expr × Bool) × Expr × Bool :=
    match binds with
    | [] =>
      let (body', bodyChanged) := cse seen body
      ([], body', bodyChanged)
    | (v, rhs, er) :: rest =>
      -- CSE nested expressions within the RHS
      let (rhs', rhsChanged) := cse seen rhs
      -- Check if the processed RHS matches something already seen
      match reusableBinding seen rhs' rest body with
      | some w =>
        have _size := Expr.nodesBinds_renameLet v w rest body
        let (kept, body', _) :=
          cseBinds seen (renameLet v w rest body).1 (renameLet v w rest body).2
        (kept, body', true)
      | none =>
        let (kept, body', changed) := cseBinds (extendSeen seen v rhs') rest body
        ((v, rhs', er) :: kept, body', rhsChanged || changed)
  termination_by Expr.nodesBinds binds + body.nodes
  decreasing_by all_goals (try simp only [Expr.nodesBinds.eq_1, Expr.nodesBinds.eq_2] at *); all_goals omega
end

/-- Process a whole Let block. -/
def cseLetBlock (outerSeen : List (Expr × VarId))
    (binds : List (VarId × Expr × Bool)) (body : Expr) : Expr × Bool :=
  let (kept, body', changed) := cseBinds outerSeen binds body
  match kept with
  | [] => (body', changed)
  | _ => (.Let kept body', changed)

end Moist.MIR
