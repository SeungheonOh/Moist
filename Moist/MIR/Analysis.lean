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
  partial def freeVars : Expr → VarSet
    | .Var x => VarSet.singleton x
    | .Lit _ | .Builtin _ | .Error => VarSet.empty
    | .Lam x body => (freeVars body).erase x
    | .Fix f body => (freeVars body).erase f
    | .App f x => (freeVars f).union (freeVars x)
    | .Force e => freeVars e
    | .Delay e => freeVars e
    | .Constr _ args => args.foldl (init := VarSet.empty) fun acc e => acc.union (freeVars e)
    | .Case scrut alts =>
      (freeVars scrut).union (alts.foldl (init := VarSet.empty) fun acc e => acc.union (freeVars e))
    | .Let binds body => freeVarsLet binds body

  partial def freeVarsLet : List (VarId × Expr × Bool) → Expr → VarSet
    | [], body => freeVars body
    | (x, rhs, _) :: rest, body =>
      let rhsFV := freeVars rhs
      let restFV := (freeVarsLet rest body).erase x
      rhsFV.union restFV
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

/-! ## Simple Rename -/

mutual
  partial def rename (old new_ : VarId) : Expr → Expr
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
    | .Constr tag args => .Constr tag (args.map (rename old new_))
    | .Case scrut alts => .Case (rename old new_ scrut) (alts.map (rename old new_))
    | .Let binds body => renameLet old new_ binds [] body

  partial def renameLet (old new_ : VarId)
      : List (VarId × Expr × Bool) → List (VarId × Expr × Bool) → Expr → Expr
    | [], acc, body => .Let acc.reverse (rename old new_ body)
    | (x, rhs, er) :: rest, acc, body =>
      let rhs' := rename old new_ rhs
      if x == old then
        .Let (acc.reverse ++ [(x, rhs', er)] ++ rest) body
      else
        renameLet old new_ rest ((x, rhs', er) :: acc) body
end

/-! ## Capture-Avoiding Substitution -/

mutual
  partial def subst (v : VarId) (repl : Expr) : Expr → FreshM Expr
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
      let args' ← args.mapM (subst v repl)
      pure (.Constr tag args')
    | .Case scrut alts => do
      let scrut' ← subst v repl scrut
      let alts' ← alts.mapM (subst v repl)
      pure (.Case scrut' alts')
    | .Let binds body => substLet v repl (freeVars repl) binds [] body

  partial def substLet (v : VarId) (repl : Expr) (replFV : VarSet)
      : List (VarId × Expr × Bool) → List (VarId × Expr × Bool) → Expr → FreshM Expr
    | [], acc, body => do
      let body' ← subst v repl body
      pure (.Let acc.reverse body')
    | (x, rhs, er) :: rest, acc, body => do
      let rhs' ← subst v repl rhs
      if x == v then
        pure (.Let (acc.reverse ++ [(x, rhs', er)] ++ rest) body)
      else if replFV.contains x then do
        let x' ← freshVar x.hint
        let rest' := rest.map fun (y, e, er2) => (y, rename x x' e, er2)
        let body' := rename x x' body
        substLet v repl replFV rest' ((x', rhs', er) :: acc) body'
      else
        substLet v repl replFV rest ((x, rhs', er) :: acc) body
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
