import Moist.MIR.Optimize.Advanced.FailFast

namespace Moist.MIR.Advanced

open Moist.Plutus.Term

/-! # Constructor-tag prechecks

Decoders of `Data` dispatch on `fstPair (unConstrData d)`. When the rest of a
program fails for some combinations of the tags of two decoded values, a
cheap check of those tags can run before the expensive decoding:

  `let p = unConstrData d in REST
     ⟶  let p = unConstrData d in let q = unConstrData r in
          case (case p [λtp _. case tp [case q [λtq _. case tq [() | error …]] …]]) [REST']`

`q` is the first later binding of the same chain that decodes a constructor;
it moves up past the bindings between (`terminates`, trace-free, no mutual
references). A tag combination gets an `error` leaf only when the abstract
interpreter `aeval` proves that `REST'` cannot halt once `p` and `q` carry
those tags; an out-of-range tag makes the integer `case` fail, so the check
is only built when `REST'` also cannot halt for every tag outside the range.
The check never errors where the program could halt, and it terminates, so
the rewrite is a halting/error refinement. `REST'` must not contain `Trace`.
A check is only inserted when some tag of `p` admits some but not all tags
of `q`: single unknown tags already fail early in the decoders.

`aeval` tracks integers, Booleans, pairs with a known first component,
constructors with their arity, `fstPair` and `equalsInteger` partial
applications, through bindings, cases on known values, and the
`force (ifThenElse …)` idiom. `none` means "does not halt".
-/

inductive IntInfo where
  | exact (n : Int)
  | notIn (s : List Int)
  deriving Inhabited

inductive AVal where
  | top
  | int (i : IntInfo)
  | bool (b : Bool)
  | pair (i : IntInfo)
  | constr (tag arity : Nat)
  | fstPairFn
  | eqIntFn (i : IntInfo)
  deriving Inhabited

def IntInfo.eqLit : IntInfo → Int → AVal
  | .exact n, k => .bool (n == k)
  | .notIn s, k => if s.contains k then .bool false else .top

def litAVal : Const → AVal
  | .Integer n => .int (.exact n)
  | .Bool b => .bool b
  | _ => .top

def applyAVal : AVal → AVal → AVal
  | .fstPairFn, .pair i => .int i
  | .eqIntFn i, .int (.exact k) => i.eqLit k
  | _, _ => .top

def eqIntPartial : AVal → AVal
  | .int i => .eqIntFn i
  | _ => .top

def isForcedFstPair : Expr → Bool
  | .Force (.Builtin .FstPair) => true
  | _ => false

def isEqualsInteger : Expr → Bool
  | .Builtin .EqualsInteger => true
  | _ => false

def lookupAVal (L : List (VarId × AVal)) (x : VarId) : Option AVal :=
  (L.find? fun entry => entry.1 == x).map (·.2)

mutual
  /-- Abstract value of a variable: local bindings, then hypotheses, then the
      right-hand side recorded for an enclosing binding. -/
  def varAVal (fuel : Nat) (Γ : List (VarId × Expr)) (H L : List (VarId × AVal)) (x : VarId) : AVal :=
    match lookupAVal L x with
    | some a => a
    | none =>
      match lookupAVal H x with
      | some a => a
      | none =>
        match fuel with
        | 0 => .top
        | fuel + 1 =>
          match Γ.find? (fun entry => entry.1 == x) with
          | some (_, rhs) => (aeval fuel Γ H [] rhs).getD .top
          | none => .top
  termination_by (fuel, 0, 0)

  /-- `none`: evaluation does not halt. `some a`: a returned value is in `a`. -/
  def aeval (fuel : Nat) (Γ : List (VarId × Expr)) (H L : List (VarId × AVal)) (e : Expr) : Option AVal :=
    match e with
    | .Var x => some (varAVal fuel Γ H L x)
    | .Lit (c, _) => some (litAVal c)
    | .Builtin _ | .Lam _ _ | .Delay _ | .Fix _ _ => some .top
    | .Error => none
    | .Force inner =>
      if isForcedFstPair inner then some .fstPairFn else
      match _h : iteView inner with
      | some (c, a, b) =>
        match aeval fuel Γ H L c with
        | none => none
        | some (.bool true) => aeval fuel Γ H L a
        | some (.bool false) => aeval fuel Γ H L b
        | some _ =>
          match aeval fuel Γ H L a, aeval fuel Γ H L b with
          | none, none => none
          | _, _ => some .top
      | none => (aeval fuel Γ H L inner).map fun _ => .top
    | .App f a =>
      match aeval fuel Γ H L f, aeval fuel Γ H L a with
      | none, _ => none
      | _, none => none
      | some vf, some va => some (if isEqualsInteger f then eqIntPartial va else applyAVal vf va)
    | .Constr tag fields => if fieldsHalt fuel Γ H L fields then some (.constr tag fields.length) else none
    | .Case scrutinee alternatives =>
      match aeval fuel Γ H L scrutinee with
      | none => none
      | some (.bool b) =>
        if alternatives.length > 2 then none
        else selectAlt fuel Γ H L alternatives (if b then 1 else 0) 0
      | some (.constr tag arity) => selectAlt fuel Γ H L alternatives tag arity
      | some (.int (.exact n)) =>
        if n < 0 then none else selectAlt fuel Γ H L alternatives n.toNat 0
      | some _ => if allAltsFail fuel Γ H L alternatives then none else some .top
    | .Let bindings body => aevalLet fuel Γ H L bindings body
  termination_by (fuel, sizeOf e, 1)
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (have := iteView_sizeOf _h
         apply Prod.Lex.right; apply Prod.Lex.left
         simp only [Expr.Force.sizeOf_spec]; omega)

  /-- The alternative a case selects, applied to `arity` unknown fields. -/
  def selectAlt (fuel : Nat) (Γ : List (VarId × Expr)) (H L : List (VarId × AVal)) :
      List Expr → Nat → Nat → Option AVal
    | [], _, _ => none
    | a :: _, 0, arity => applyAlt fuel Γ H L a arity
    | _ :: rest, n + 1, arity => selectAlt fuel Γ H L rest n arity
  termination_by alts => (fuel, sizeOf alts, 2)

  def applyAlt (fuel : Nat) (Γ : List (VarId × Expr)) (H L : List (VarId × AVal)) (a : Expr) :
      Nat → Option AVal
    | 0 => aeval fuel Γ H L a
    | arity + 1 => applyAltSucc fuel Γ H L a arity
  termination_by (fuel, sizeOf a, 3)

  def applyAltSucc (fuel : Nat) (Γ : List (VarId × Expr)) (H L : List (VarId × AVal)) :
      Expr → Nat → Option AVal
    | .Lam x body, arity => applyAlt fuel Γ H ((x, .top) :: L) body arity
    | a, _ => (aeval fuel Γ H L a).map fun _ => .top
  termination_by a => (fuel, sizeOf a, 2)

  def allAltsFail (fuel : Nat) (Γ : List (VarId × Expr)) (H L : List (VarId × AVal)) :
      List Expr → Bool
    | [] => true
    | .Lam _ _ :: _ => false
    | a :: rest => (aeval fuel Γ H L a).isNone && allAltsFail fuel Γ H L rest
  termination_by alts => (fuel, sizeOf alts, 2)

  def fieldsHalt (fuel : Nat) (Γ : List (VarId × Expr)) (H L : List (VarId × AVal)) :
      List Expr → Bool
    | [] => true
    | e :: rest => (aeval fuel Γ H L e).isSome && fieldsHalt fuel Γ H L rest
  termination_by fields => (fuel, sizeOf fields, 2)

  def aevalLet (fuel : Nat) (Γ : List (VarId × Expr)) (H L : List (VarId × AVal)) :
      List (VarId × Expr × Bool) → Expr → Option AVal
    | [], body => aeval fuel Γ H L body
    | (x, rhs, _) :: rest, body =>
      match aeval fuel Γ H L rhs with
      | none => none
      | some a => aevalLet fuel Γ H ((x, a) :: L) rest body
  termination_by bindings body => (fuel, sizeOf bindings + sizeOf body, 2)
end

/-! ## Guard trees -/

inductive GuardTree where
  | ok
  | fail
  | split (x : VarId) (alternatives : List GuardTree)

def unitExpr : Expr := .Lit (.Unit, .AtomicType .TypeUnit)

/-- `case x [λtag fields. case tag alternatives]`: a pair case binds the
    constructor tag without a `fstPair` call. Binders are numbered from
    `base`, above every name the guard mentions. -/
def GuardTree.toExpr (base : Nat) : GuardTree → Expr
  | .ok => unitExpr
  | .fail => .Error
  | .split x alternatives =>
    let tag : VarId := { uid := base, origin := .gen, hint := "tag" }
    let fields : VarId := { uid := base + 1, origin := .gen, hint := "fields" }
    .Case (.Var x) [.Lam tag (.Lam fields (.Case (.Var tag)
      (alternatives.attach.map fun ⟨t, _⟩ => t.toExpr (base + 2))))]

def GuardTree.isFail : GuardTree → Bool
  | .fail => true
  | _ => false

def GuardTree.isOk : GuardTree → Bool
  | .ok => true
  | _ => false

/-- Some tag of the first value admits only some tags of the second: the
    combination, not either tag alone, is checked. Decoders already reject
    unknown tags of a single value early. -/
def GuardTree.mixedInner : GuardTree → Bool
  | .split _ alternatives => alternatives.any fun
    | .split _ inner => inner.any GuardTree.isFail && inner.any GuardTree.isOk
    | _ => false
  | _ => false

def tagRange (count : Nat) : List Int := (List.range count).map Int.ofNat

/-- Replace the hypothesis about `x`: in the local block if `x` is bound
    there, otherwise among the outer hypotheses. -/
def replaceFirst (x : VarId) (a : AVal) : List (VarId × AVal) → List (VarId × AVal)
  | [] => []
  | entry :: rest => if entry.1 == x then (entry.1, a) :: rest else entry :: replaceFirst x a rest

def assume (H L : List (VarId × AVal)) (x : VarId) (a : AVal) :
    List (VarId × AVal) × List (VarId × AVal) :=
  if L.any (fun entry => entry.1 == x) then (H, replaceFirst x a L)
  else ((x, a) :: H, L)

mutual
  /-- Every way a guard can fail is a way the guarded expression cannot halt. -/
  def guardOK (fuel : Nat) (Γ : List (VarId × Expr)) (M : Expr) :
      List (VarId × AVal) → List (VarId × AVal) → GuardTree → Bool
    | _, _, .ok => true
    | H, L, .fail => (aeval fuel Γ H L M).isNone
    | H, L, .split x alternatives =>
      (let (H', L') := assume H L x (.pair (.notIn (tagRange alternatives.length)))
       (aeval fuel Γ H' L' M).isNone) &&
      guardOKList fuel Γ M H L x 0 alternatives

  def guardOKList (fuel : Nat) (Γ : List (VarId × Expr)) (M : Expr)
      (H L : List (VarId × AVal)) (x : VarId) : Nat → List GuardTree → Bool
    | _, [] => true
    | n, t :: rest =>
      (let (H', L') := assume H L x (.pair (.exact (Int.ofNat n)))
       guardOK fuel Γ M H' L' t) && guardOKList fuel Γ M H L x (n + 1) rest
end

def guardFuel : Nat := 64

def maxTag : Nat := 16

/-- The smallest tag range outside of which `M` cannot halt. -/
def tagCount (Γ : List (VarId × Expr)) (M : Expr) (H L : List (VarId × AVal)) (x : VarId) :
    Option Nat :=
  ((List.range maxTag).find? fun k =>
    let (H', L') := assume H L x (.pair (.notIn (tagRange (k + 1))))
    (aeval guardFuel Γ H' L' M).isNone).map (· + 1)

def leaf (Γ : List (VarId × Expr)) (M : Expr) (H L : List (VarId × AVal)) : GuardTree :=
  if (aeval guardFuel Γ H L M).isNone then .fail else .ok

def splitOn (Γ : List (VarId × Expr)) (M : Expr) (x : VarId)
    (inner : List (VarId × AVal) → List (VarId × AVal) → GuardTree)
    (H L : List (VarId × AVal)) : GuardTree :=
  match tagCount Γ M H L x with
  | none => leaf Γ M H L
  | some count =>
    .split x ((List.range count).map fun (n : Nat) =>
      let (H', L') := assume H L x (.pair (.exact (Int.ofNat n)))
      inner H' L')

/-! ## Moving a decoding binding up -/

def nestLets : List (VarId × Expr × Bool) → Expr → Expr
  | [], body => body
  | binding :: rest, body => .Let [binding] (nestLets rest body)

def isConstrDecode : Expr → Bool
  | .App (.Builtin .UnConstrData) _ => true
  | _ => false

/-- The first later binding of a single-binding chain that decodes a
    constructor and may move to the front of the chain. -/
def findDecode : Expr → List (VarId × Expr × Bool) →
    Option (List (VarId × Expr × Bool) × (VarId × Expr × Bool) × Expr)
  | .Let [(y, rhs, er)] rest, before =>
    if isConstrDecode rhs && terminates rhs && traceFree rhs &&
        before.all (fun b => !(freeVars rhs).contains b.1 && !(freeVars b.2.1).contains y &&
          !(b.1 == y) && traceFree b.2.1) then
      some (before.reverse, (y, rhs, er), rest)
    else findDecode rest ((y, rhs, er) :: before)
  | _, _ => none

/-- Insert a guard for the decoded `p` (and the next decoded `q`) in front of
    `chain`, the scope of `p`. -/
def guardChain (Γ : List (VarId × Expr)) (p : VarId) (chain : Expr) : Option Expr :=
  let (hoisted, M, L) :=
    match findDecode chain [] with
    | some (before, (q, rq, er), rest) => (some (q, rq, er), nestLets before rest, [(q, AVal.top)])
    | none => (none, chain, [])
  let tree := splitOn Γ M p (fun H L' =>
      match hoisted with
      | some (q, _, _) => splitOn Γ M q (leaf Γ M) H L'
      | none => leaf Γ M H L') [] L
  let G := tree.toExpr (maxUidExpr chain + p.uid + 1)
  if tree.mixedInner && terminates G && traceFree M && guardOK guardFuel Γ M [] L tree then
    let guarded := Expr.Case G [M]
    some (match hoisted with
      | some binding => .Let [binding] guarded
      | none => guarded)
  else none

/-- Bottom-up walk; each constructor decoding tries to guard its scope. The
    facts record the rewritten right-hand side of every enclosing binding. -/
def tagGuardWalk (Γ : List (VarId × Expr)) (expression : Expr) : Expr :=
  match expression with
  | .Let [] body => tagGuardWalk Γ body
  | .Let ((x, rhs, erased) :: rest) body =>
    let rhs' := tagGuardWalk Γ rhs
    let body' := tagGuardWalk ((x, rhs') :: Γ) (.Let rest body)
    if isConstrDecode rhs' then
      match guardChain ((x, rhs') :: Γ) x body' with
      | some guarded => .Let [(x, rhs', erased)] guarded
      | none => .Let [(x, rhs', erased)] body'
    else .Let [(x, rhs', erased)] body'
  | .Lam x body => .Lam x (tagGuardWalk Γ body)
  | .Fix f body => .Fix f (tagGuardWalk Γ body)
  | .App f a => .App (tagGuardWalk Γ f) (tagGuardWalk Γ a)
  | .Force body => .Force (tagGuardWalk Γ body)
  | .Delay body => .Delay (tagGuardWalk Γ body)
  | .Constr tag fields => .Constr tag (fields.attach.map fun ⟨field, _⟩ => tagGuardWalk Γ field)
  | .Case scrutinee alternatives =>
    .Case (tagGuardWalk Γ scrutinee) (alternatives.attach.map fun ⟨a, _⟩ => tagGuardWalk Γ a)
  | .Var _ | .Lit _ | .Builtin _ | .Error => expression
termination_by exprSize expression
decreasing_by
  all_goals first
    | (simp only [exprSize]; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)
    | (simp only [exprSize, exprSizeBinds]; have := exprSize_pos rhs; omega)

def tagGuards (expression : Expr) : Expr :=
  let prepared := uniqueOptimizationBinders expression
  if wellScoped prepared then tagGuardWalk [] prepared else prepared

end Moist.MIR.Advanced
