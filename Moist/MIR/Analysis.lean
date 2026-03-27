import Moist.MIR.Expr

namespace Moist.MIR

open Moist.Plutus.Term
open Moist.Plutus (Data ByteString)

/-! # MIR Analysis Functions -/

/-! ## Variable Set -/

structure VarSet where
  data : Array VarId := #[]
deriving Inhabited

namespace VarSet

def empty : VarSet := ⟨#[]⟩
def contains (s : VarSet) (v : VarId) : Bool := s.data.any (· == v)
def insert (s : VarSet) (v : VarId) : VarSet :=
  if s.contains v then s else ⟨s.data.push v⟩
def erase (s : VarSet) (v : VarId) : VarSet := ⟨s.data.filter (· != v)⟩
def union (s1 s2 : VarSet) : VarSet :=
  s2.data.foldl (init := s1) fun acc v => acc.insert v
def singleton (v : VarId) : VarSet := ⟨#[v]⟩
def toList (s : VarSet) : List VarId := s.data.toList

end VarSet

/-! ## Equality Helpers -/

partial def dataEq : Data → Data → Bool
  | .Constr i1 args1, .Constr i2 args2 =>
    i1 == i2 && args1.length == args2.length &&
    (args1.zip args2).all fun (a, b) => dataEq a b
  | .Map m1, .Map m2 =>
    m1.length == m2.length &&
    (m1.zip m2).all fun ((a1, b1), (a2, b2)) => dataEq a1 a2 && dataEq b1 b2
  | .List l1, .List l2 =>
    l1.length == l2.length && (l1.zip l2).all fun (a, b) => dataEq a b
  | .I i1, .I i2 => i1 == i2
  | .B b1, .B b2 => b1 == b2
  | _, _ => false

mutual
  def builtinTypeEq : BuiltinType → BuiltinType → Bool
    | .AtomicType a, .AtomicType b => a == b
    | .TypeOperator a, .TypeOperator b => typeOperatorEq a b
    | _, _ => false
  def typeOperatorEq : TypeOperator → TypeOperator → Bool
    | .TypeList a, .TypeList b => builtinTypeEq a b
    | .TypePair a1 a2, .TypePair b1 b2 => builtinTypeEq a1 b1 && builtinTypeEq a2 b2
    | _, _ => false
end

partial def constEq : Const → Const → Bool
  | .Integer a, .Integer b => a == b
  | .ByteString a, .ByteString b => a == b
  | .String a, .String b => a == b
  | .Unit, .Unit => true
  | .Bool a, .Bool b => a == b
  | .ConstList a, .ConstList b =>
    a.length == b.length && (a.zip b).all fun (x, y) => constEq x y
  | .ConstDataList a, .ConstDataList b =>
    a.length == b.length && (a.zip b).all fun (x, y) => dataEq x y
  | .ConstPairDataList a, .ConstPairDataList b =>
    a.length == b.length &&
    (a.zip b).all fun ((a1, a2), (b1, b2)) => dataEq a1 a2 && dataEq b1 b2
  | .Pair (a1, a2), .Pair (b1, b2) => constEq a1 b1 && constEq a2 b2
  | .PairData (a1, a2), .PairData (b1, b2) => dataEq a1 a2 && dataEq b1 b2
  | .Data a, .Data b => dataEq a b
  | .Bls12_381_G1_element, .Bls12_381_G1_element => true
  | .Bls12_381_G2_element, .Bls12_381_G2_element => true
  | .Bls12_381_MlResult, .Bls12_381_MlResult => true
  | _, _ => false

def litEq (a b : Const × BuiltinType) : Bool :=
  constEq a.1 b.1 && builtinTypeEq a.2 b.2

/-! ## Free Variables -/

mutual
  def freeVars (e : Expr) : VarSet :=
    match e with
    | .Var x => VarSet.singleton x
    | .Lit _ | .Builtin _ | .Error => VarSet.empty
    | .Lam x body => (freeVars body).erase x
    | .Fix f body => (freeVars body).erase f
    | .App f x => (freeVars f).union (freeVars x)
    | .Force e | .Delay e => freeVars e
    | .Constr _ args => freeVarsList args
    | .Case scrut alts =>
      (freeVars scrut).union (freeVarsList alts)
    | .Let binds body => freeVarsLet binds body
  termination_by sizeOf e

  def freeVarsList (es : List Expr) : VarSet :=
    match es with
    | [] => VarSet.empty
    | e :: rest => (freeVars e).union (freeVarsList rest)
  termination_by sizeOf es

  def freeVarsLet (binds : List (VarId × Expr × Bool)) (body : Expr) : VarSet :=
    match binds with
    | [] => freeVars body
    | (x, rhs, _) :: rest =>
      (freeVars rhs).union ((freeVarsLet rest body).erase x)
  termination_by sizeOf binds + sizeOf body
end

/-! ## No-Self-Reference Check -/

def noSelfRef (binds : List (VarId × Expr × Bool)) : Bool :=
  binds.all fun (x, rhs, _) => !(freeVars rhs).contains x

/-! ## Occurrence Counting -/

mutual
  partial def countOccurrences (v : VarId) : Expr → Nat
    | .Var x => if x == v then 1 else 0
    | .Lit _ | .Builtin _ | .Error => 0
    | .Lam x body => if x == v then 0 else countOccurrences v body
    | .Fix f body => if f == v then 0 else countOccurrences v body
    | .App f x => countOccurrences v f + countOccurrences v x
    | .Force e => countOccurrences v e
    | .Delay e => countOccurrences v e
    | .Constr _ args => args.foldl (init := 0) fun acc e => acc + countOccurrences v e
    | .Case scrut alts =>
      countOccurrences v scrut + alts.foldl (init := 0) fun acc e => acc + countOccurrences v e
    | .Let binds body => countOccurrencesLet v binds body

  partial def countOccurrencesLet (v : VarId) : List (VarId × Expr × Bool) → Expr → Nat
    | [], body => countOccurrences v body
    | (x, rhs, _) :: rest, body =>
      let rhsCount := countOccurrences v rhs
      if x == v then rhsCount
      else rhsCount + countOccurrencesLet v rest body
end

/-! ## Expression Size -/

partial def exprSize : Expr → Nat
  | .Var _ | .Lit _ | .Builtin _ | .Error => 1
  | .Lam _ body => 1 + exprSize body
  | .Fix _ body => 1 + exprSize body
  | .App f x => 1 + exprSize f + exprSize x
  | .Force e => 1 + exprSize e
  | .Delay e => 1 + exprSize e
  | .Constr _ args => 1 + args.foldl (init := 0) fun acc e => acc + exprSize e
  | .Case scrut alts =>
    1 + exprSize scrut + alts.foldl (init := 0) fun acc e => acc + exprSize e
  | .Let binds body =>
    1 + binds.foldl (init := 0) (fun acc (_, e, _) => acc + exprSize e) + exprSize body

/-! ## Node Count (rename-invariant termination measure) -/

mutual
  def Expr.nodes (e : Expr) : Nat :=
    match e with
    | .Var _ | .Lit _ | .Builtin _ | .Error => 1
    | .Lam _ body | .Fix _ body => 1 + body.nodes
    | .App f x => 1 + f.nodes + x.nodes
    | .Force e | .Delay e => 1 + e.nodes
    | .Constr _ args => 1 + Expr.nodesList args
    | .Case scrut alts => 1 + scrut.nodes + Expr.nodesList alts
    | .Let binds body => 1 + Expr.nodesBinds binds + body.nodes
  termination_by sizeOf e

  def Expr.nodesList (es : List Expr) : Nat :=
    match es with
    | [] => 1
    | e :: rest => 1 + e.nodes + Expr.nodesList rest
  termination_by sizeOf es

  def Expr.nodesBinds (binds : List (VarId × Expr × Bool)) : Nat :=
    match binds with
    | [] => 1
    | (_, rhs, _) :: rest => 1 + rhs.nodes + Expr.nodesBinds rest
  termination_by sizeOf binds
end

attribute [simp] Expr.nodes.eq_1 Expr.nodes.eq_2 Expr.nodes.eq_3 Expr.nodes.eq_4
  Expr.nodes.eq_5 Expr.nodes.eq_6 Expr.nodes.eq_7 Expr.nodes.eq_8 Expr.nodes.eq_9
  Expr.nodes.eq_10 Expr.nodes.eq_11 Expr.nodes.eq_12
  Expr.nodesList.eq_1 Expr.nodesList.eq_2
  Expr.nodesBinds.eq_1 Expr.nodesBinds.eq_2

/-! ## Simple Rename -/

mutual
  def rename (old new_ : VarId) (e : Expr) : Expr :=
    match e with
    | .Var x => if x == old then .Var new_ else .Var x
    | .Lit c => .Lit c
    | .Builtin b => .Builtin b
    | .Error => .Error
    | .Lam x body =>
      if x == old then .Lam x body
      else .Lam x (rename old new_ body)
    | .Fix f body =>
      if f == old then .Fix f body
      else .Fix f (rename old new_ body)
    | .App f x => .App (rename old new_ f) (rename old new_ x)
    | .Force e => .Force (rename old new_ e)
    | .Delay e => .Delay (rename old new_ e)
    | .Constr tag args => .Constr tag (renameList old new_ args)
    | .Case scrut alts => .Case (rename old new_ scrut) (renameList old new_ alts)
    | .Let binds body =>
      let (binds', body') := renameLet old new_ binds body
      .Let binds' body'
  termination_by sizeOf e

  def renameList (old new_ : VarId) (es : List Expr) : List Expr :=
    match es with
    | [] => []
    | e :: rest => rename old new_ e :: renameList old new_ rest
  termination_by sizeOf es

  def renameLet (old new_ : VarId) (binds : List (VarId × Expr × Bool)) (body : Expr)
      : List (VarId × Expr × Bool) × Expr :=
    match binds with
    | [] => ([], rename old new_ body)
    | (x, rhs, er) :: rest =>
      let rhs' := rename old new_ rhs
      if x == old then ((x, rhs', er) :: rest, body)
      else
        let (rest', body') := renameLet old new_ rest body
        ((x, rhs', er) :: rest', body')
  termination_by sizeOf binds + sizeOf body
end

def renameBinds (old new_ : VarId) : List (VarId × Expr × Bool) → List (VarId × Expr × Bool)
  | [] => []
  | (x, rhs, er) :: rest => (x, rename old new_ rhs, er) :: renameBinds old new_ rest

/-! ## Rename preserves node count -/

mutual
  @[simp] theorem Expr.nodes_rename (old new_ : VarId) (e : Expr) :
      (rename old new_ e).nodes = e.nodes := by
    match e with
    | .Var x => simp [rename, Expr.nodes]; split <;> simp [Expr.nodes]
    | .Lit _ => simp [rename]
    | .Builtin _ => simp [rename]
    | .Error => simp [rename]
    | .Lam x body =>
      simp only [rename]; split
      · rfl
      · simp [Expr.nodes, Expr.nodes_rename old new_ body]
    | .Fix f body =>
      simp only [rename]; split
      · rfl
      · simp [Expr.nodes, Expr.nodes_rename old new_ body]
    | .App f x =>
      simp [rename, Expr.nodes, Expr.nodes_rename old new_ f, Expr.nodes_rename old new_ x]
    | .Force e' => simp [rename, Expr.nodes, Expr.nodes_rename old new_ e']
    | .Delay e' => simp [rename, Expr.nodes, Expr.nodes_rename old new_ e']
    | .Constr tag args =>
      simp [rename, Expr.nodes, Expr.nodesList_rename old new_ args]
    | .Case scrut alts =>
      simp [rename, Expr.nodes, Expr.nodes_rename old new_ scrut,
            Expr.nodesList_rename old new_ alts]
    | .Let binds body =>
      simp only [rename]
      have ⟨h1, h2⟩ := Expr.nodesBinds_renameLet old new_ binds body
      revert h1 h2
      cases renameLet old new_ binds body with
      | mk b bo => simp_all [Expr.nodes]
  termination_by sizeOf e

  @[simp] theorem Expr.nodesList_rename (old new_ : VarId) (es : List Expr) :
      Expr.nodesList (renameList old new_ es) = Expr.nodesList es := by
    unfold renameList
    split
    · rfl
    · rename_i e rest
      simp [Expr.nodes_rename old new_ e, Expr.nodesList_rename old new_ rest]
  termination_by sizeOf es

  theorem Expr.nodesBinds_renameLet (old new_ : VarId)
      (binds : List (VarId × Expr × Bool)) (body : Expr) :
      Expr.nodesBinds (renameLet old new_ binds body).1 = Expr.nodesBinds binds ∧
      (renameLet old new_ binds body).2.nodes = body.nodes := by
    unfold renameLet
    split
    · simp [Expr.nodes_rename old new_ body]
    · rename_i x rhs er rest
      split
      · simp [Expr.nodes_rename old new_ rhs]
      · have ⟨ih1, ih2⟩ := Expr.nodesBinds_renameLet old new_ rest body
        simp [Expr.nodes_rename old new_ rhs, ih1, ih2]
  termination_by sizeOf binds + sizeOf body
end

@[simp] theorem Expr.nodesBinds_renameBinds (old new_ : VarId)
    (binds : List (VarId × Expr × Bool)) :
    Expr.nodesBinds (renameBinds old new_ binds) = Expr.nodesBinds binds := by
  induction binds with
  | nil => simp [renameBinds]
  | cons b rest ih => obtain ⟨x, rhs, er⟩ := b; simp [renameBinds, ih]

/-! ## Capture-Avoiding Substitution -/

mutual
  def subst (v : VarId) (repl : Expr) (e : Expr) : FreshM Expr :=
    match e with
    | .Var x => pure (if x == v then repl else .Var x)
    | .Lit c => pure (.Lit c)
    | .Builtin b => pure (.Builtin b)
    | .Error => pure .Error
    | .Lam x body =>
      if x == v then pure (.Lam x body)
      else if (freeVars repl).contains x then do
        let x' ← freshVar x.hint
        let body' := rename x x' body
        let body'' ← subst v repl body'
        pure (.Lam x' body'')
      else do
        let body' ← subst v repl body
        pure (.Lam x body')
    | .Fix f body =>
      if f == v then pure (.Fix f body)
      else if (freeVars repl).contains f then do
        let f' ← freshVar f.hint
        let body' := rename f f' body
        let body'' ← subst v repl body'
        pure (.Fix f' body'')
      else do
        let body' ← subst v repl body
        pure (.Fix f body')
    | .App f x => do
      let f' ← subst v repl f
      let x' ← subst v repl x
      pure (.App f' x')
    | .Force e => do
      let e' ← subst v repl e
      pure (.Force e')
    | .Delay e => do
      let e' ← subst v repl e
      pure (.Delay e')
    | .Constr tag args => do
      let args' ← substList v repl args
      pure (.Constr tag args')
    | .Case scrut alts => do
      let scrut' ← subst v repl scrut
      let alts' ← substList v repl alts
      pure (.Case scrut' alts')
    | .Let binds body =>
      substLet v repl (freeVars repl) binds body >>= fun (b, bo) =>
      pure (.Let b bo)
  termination_by e.nodes
  decreasing_by all_goals (simp_wf; try (first | omega | (simp_all; done)))

  def substList (v : VarId) (repl : Expr) (es : List Expr) : FreshM (List Expr) :=
    match es with
    | [] => pure []
    | e :: rest => do
      let e' ← subst v repl e
      let rest' ← substList v repl rest
      pure (e' :: rest')
  termination_by Expr.nodesList es
  decreasing_by all_goals (simp_wf; try (first | omega | (simp_all; done)))

  def substLet (v : VarId) (repl : Expr) (replFV : VarSet)
      (binds : List (VarId × Expr × Bool)) (body : Expr)
      : FreshM (List (VarId × Expr × Bool) × Expr) :=
    match binds with
    | [] =>
      subst v repl body >>= fun b => pure ([], b)
    | (x, rhs, er) :: rest => do
      let rhs' ← subst v repl rhs
      if x == v then
        pure ((x, rhs', er) :: rest, body)
      else if replFV.contains x then do
        let x' ← freshVar x.hint
        let rest' := renameBinds x x' rest
        let body' := rename x x' body
        substLet v repl replFV rest' body' >>= fun (r, b) =>
        pure ((x', rhs', er) :: r, b)
      else
        substLet v repl replFV rest body >>= fun (r, b) =>
        pure ((x, rhs', er) :: r, b)
  termination_by Expr.nodesBinds binds + body.nodes
  decreasing_by all_goals (simp_wf; try (first | omega | (simp_all; done)))
end

/-! ## Alpha-Equivalence -/

private def lookupIdx (env : List VarId) (v : VarId) : Option Nat :=
  go env 0
where
  go : List VarId → Nat → Option Nat
    | [], _ => none
    | x :: xs, idx => if x == v then some idx else go xs (idx + 1)

mutual
  partial def alphaEqAux (env1 env2 : List VarId) : Expr → Expr → Bool
    | .Var x, .Var y =>
      match lookupIdx env1 x, lookupIdx env2 y with
      | some i, some j => i == j
      | none, none => x == y
      | _, _ => false
    | .Lit a, .Lit b => litEq a b
    | .Builtin a, .Builtin b => a == b
    | .Error, .Error => true
    | .Lam x body1, .Lam y body2 =>
      alphaEqAux (x :: env1) (y :: env2) body1 body2
    | .Fix f1 body1, .Fix f2 body2 =>
      alphaEqAux (f1 :: env1) (f2 :: env2) body1 body2
    | .App f1 x1, .App f2 x2 =>
      alphaEqAux env1 env2 f1 f2 && alphaEqAux env1 env2 x1 x2
    | .Force e1, .Force e2 => alphaEqAux env1 env2 e1 e2
    | .Delay e1, .Delay e2 => alphaEqAux env1 env2 e1 e2
    | .Constr t1 args1, .Constr t2 args2 =>
      t1 == t2 && args1.length == args2.length &&
      (args1.zip args2).all fun (a, b) => alphaEqAux env1 env2 a b
    | .Case s1 alts1, .Case s2 alts2 =>
      alphaEqAux env1 env2 s1 s2 && alts1.length == alts2.length &&
      (alts1.zip alts2).all fun (a, b) => alphaEqAux env1 env2 a b
    | .Let binds1 body1, .Let binds2 body2 =>
      binds1.length == binds2.length &&
      alphaEqLet env1 env2 binds1 binds2 body1 body2
    | _, _ => false

  partial def alphaEqLet (env1 env2 : List VarId)
      : List (VarId × Expr × Bool) → List (VarId × Expr × Bool) → Expr → Expr → Bool
    | [], [], body1, body2 => alphaEqAux env1 env2 body1 body2
    | (x, rhs1, _) :: rest1, (y, rhs2, _) :: rest2, body1, body2 =>
      alphaEqAux env1 env2 rhs1 rhs2 &&
      alphaEqLet (x :: env1) (y :: env2) rest1 rest2 body1 body2
    | _, _, _, _ => false
end

def alphaEq (e1 e2 : Expr) : Bool :=
  alphaEqAux [] [] e1 e2

/-! ## Helpers -/

def uncurryApp : Expr → Expr × List Expr
  | .App f x =>
    let (head, args) := uncurryApp f
    (head, args ++ [x])
  | e => (e, [])

def isClosed (e : Expr) : Bool := (freeVars e).data.isEmpty

def fixIsRecursive (f : VarId) (body : Expr) : Bool := (freeVars body).contains f

/-! ## Deferred Position Detection -/

mutual
  /-- Return `true` when variable `v` has at least one free occurrence in a
  deferred evaluation position in `e`. Deferred positions are:

  - `Lam` body (evaluated per-call, not at definition time)
  - `Fix` body (evaluated on each recursive call)
  - `Delay` body (evaluated when forced, not at definition time)
  - `Case` alternatives (only one is selected; others are not evaluated)

  The `Case` scrutinee, `App` arguments, `Force` arguments, `Constr` arguments,
  and `Let` binding RHSs are all in strict (non-deferred) position.

  Used by inlining passes to prevent moving non-value computations into
  positions where their evaluation is not guaranteed or changes multiplicity. -/
  partial def occursInDeferredAux (v : VarId) (deferred : Bool) : Expr → Bool
    | .Var x => deferred && x == v
    | .Lit _ | .Builtin _ | .Error => false
    | .Lam x body =>
      if x == v then false
      else occursInDeferredAux v true body
    | .Fix f body =>
      if f == v then false
      else occursInDeferredAux v true body
    | .Delay e => occursInDeferredAux v true e
    | .App f x =>
      occursInDeferredAux v deferred f || occursInDeferredAux v deferred x
    | .Force e => occursInDeferredAux v deferred e
    | .Constr _ args => args.any (occursInDeferredAux v deferred)
    | .Case scrut alts =>
      occursInDeferredAux v deferred scrut ||
      alts.any (occursInDeferredAux v true)
    | .Let binds body => occursInDeferredLetAux v deferred binds body

  partial def occursInDeferredLetAux (v : VarId) (deferred : Bool)
      : List (VarId × Expr × Bool) → Expr → Bool
    | [], body => occursInDeferredAux v deferred body
    | (x, rhs, _) :: rest, body =>
      occursInDeferredAux v deferred rhs ||
      (if x == v then false else occursInDeferredLetAux v deferred rest body)
end

/-- Return `true` when variable `v` has at least one free occurrence in a
deferred evaluation position (Lam body, Fix body, Delay body, or Case
alternative) in `e`. See `occursInDeferredAux` for details. -/
def occursInDeferred (v : VarId) (e : Expr) : Bool :=
  occursInDeferredAux v false e

/-! ## ANF Predicate and Subtype -/

partial def Expr.isANF : Expr → Bool
  | .Var _ | .Lit _ | .Builtin _ | .Error => true
  | .Lam _ body => body.isANF
  | .Fix _ body => body.isANF
  | .Delay e => e.isANF
  | .Let binds body =>
    noSelfRef binds && binds.all (fun (_, rhs, _) => rhs.isANF) && body.isANF
  | .App f x => f.isAtom && x.isAtom
  | .Force e => e.isAtom
  | .Constr _ args => args.all (·.isAtom)
  | .Case scrut alts => scrut.isAtom && alts.all (·.isANF)

abbrev ANFExpr := { e : Expr // e.isANF = true }

instance : Inhabited ANFExpr where
  default := ⟨.Error, sorry⟩

def Expr.toANF? (e : Expr) : Option ANFExpr :=
  if h : e.isANF then some ⟨e, h⟩ else none

def ANFExpr.toExpr (e : ANFExpr) : Expr := e.val

end Moist.MIR
