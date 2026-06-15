import PlutusCore.UPLC.CekMachine
import PlutusCore.Integer.Lemmas
import PlutusCore.Bool.Lemmas
import Blaster

open PlutusCore.UPLC.Term PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue PlutusCore.Integer

abbrev cI (n : Int) : Term := .Const (.Integer n)
abbrev vr (s : String) : Term := .Var s
abbrev b2 (op : BuiltinFun) (a c : Term) : Term := .Apply (.Apply (.Builtin op) a) c
def lt (a b : Term) := b2 .LessThanInteger a b
def le (a b : Term) := b2 .LessThanEqualsInteger a b
def add (a b : Term) := b2 .AddInteger a b
def sub (a b : Term) := b2 .SubtractInteger a b
def ite3 (c t e : Term) : Term := .Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse)) c) t) e

-- 0 ≤ |x|, computed with strict IfThenElse
def vite : Term := .Lam "x" (le (cI 0) (ite3 (lt (vr "x") (cI 0)) (sub (cI 0) (vr "x")) (vr "x")))
-- nested: classify sign into {-1,0,1} then check it is ≤ 1
def vsign : Term := .Lam "x"
  (le (ite3 (lt (vr "x") (cI 0)) (sub (cI 0) (cI 1)) (ite3 (lt (cI 0) (vr "x")) (cI 1) (cI 0))) (cI 1))

abbrev exec (t : Term) (ps : List Term) (n : Nat) : State := cekExecuteProgram (.Program (.Version 1 1 0) t) ps n
def resBool : State → Bool | .Halt (.VCon (.Bool b)) => b | _ => false

mutual
def subst (x : String) (v : Term) : Term → Term
  | .Var y => if x == y then v else .Var y
  | .Lam y b => if x == y then .Lam y b else .Lam y (subst x v b)
  | .Apply f a => .Apply (subst x v f) (subst x v a)
  | .Force t => .Force (subst x v t)
  | .Delay t => .Delay (subst x v t)
  | .Case s alts => .Case (subst x v s) (substL x v alts)
  | .Constr i ts => .Constr i (substL x v ts)
  | t => t
def substL (x : String) (v : Term) : List Term → List Term
  | [] => []
  | t :: ts => subst x v t :: substL x v ts
end
def evalB2 : BuiltinFun → Const → Const → Option Const
  | .AddInteger,            .Integer x, .Integer y => some (.Integer (addInteger x y))
  | .SubtractInteger,       .Integer x, .Integer y => some (.Integer (subtractInteger x y))
  | .MultiplyInteger,       .Integer x, .Integer y => some (.Integer (multiplyInteger x y))
  | .LessThanInteger,       .Integer x, .Integer y => some (.Bool (lessThanInteger x y))
  | .LessThanEqualsInteger, .Integer x, .Integer y => some (.Bool (lessThanEqualsInteger x y))
  | _, _, _ => none
def lamBody? : Term → Option (String × Term) | .Lam x b => some (x, b) | _ => none
def spine1? : Term → Option (BuiltinFun × Const) | .Apply (.Builtin op) (.Const c1) => some (op, c1) | _ => none
def iteHead2? : Term → Option (Term × Term)
  | .Apply (.Apply (.Force (.Builtin .IfThenElse)) c) t => some (c, t) | _ => none

mutual
/-- value recogniser, incl. partial ITE spines (force ITE + ≤2 value args). -/
def isValue : Term → Bool
  | .Const _ | .Lam _ _ | .Builtin _ | .Delay _ => true
  | .Force (.Builtin .IfThenElse) => true
  | .Apply f a => ((match f with | .Builtin _ => true | _ => false) && isValue a) || (iteVal f && isValue a)
  | _ => false
/-- t is an ITE spine to which one more value-arg keeps it a partial value (≤2 args). -/
def iteVal : Term → Bool
  | .Force (.Builtin .IfThenElse) => true
  | .Apply (.Force (.Builtin .IfThenElse)) c => isValue c
  | _ => false
end

def sstep : Term → Option Term
  | .Apply f a =>
    if isValue f then
      if isValue a then
        match lamBody? f with
        | some (x, body) => some (subst x a body)
        | none => match iteHead2? f with
          | some (c, t) => (match c with | .Const (.Bool b) => some (if b then t else a) | _ => none)
          | none => match spine1? f, a with
            | some (op, c1), .Const c2 => (match evalB2 op c1 c2 with | some r => some (.Const r) | none => none)
            | _, _ => none
      else (match sstep a with | some a' => some (.Apply f a') | none => none)
    else (match sstep f with | some f' => some (.Apply f' a) | none => none)
  | .Force t =>
    if isValue t then (match t with | .Delay m => some m | _ => none)
    else (match sstep t with | some t' => some (.Force t') | none => none)
  | _ => none
termination_by t => sizeOf t
def seval : Nat → Term → Term
  | 0, t => t
  | n + 1, t => match sstep t with | some t' => seval n t' | none => t
def sapp (t : Term) (ps : List Term) : Term := ps.foldl Term.Apply t
def sresBool : Term → Bool | .Const (.Bool b) => b | _ => false

#eval resBool  (exec  vite [cI (-3)] 200)            -- true
#eval sresBool (seval 60 (sapp vite [cI (-3)]))      -- true
#eval sresBool (seval 60 (sapp vite [cI 9]))         -- true
#eval sresBool (seval 60 (sapp vsign [cI (-3)]))     -- true

-- vite: 0 ≤ |x|
#blaster (unfold-depth: 300) (timeout: 120) (verbose: 1)
  [∀ (x : Int), resBool (exec vite [cI x] 150) = true]
#blaster (unfold-depth: 200) (timeout: 120) (verbose: 1)
  [∀ (x : Int), sresBool (seval 60 (sapp vite [cI x])) = true]
-- vsign: nested ITE, sign ∈ {-1,0,1} ≤ 1
#blaster (unfold-depth: 300) (timeout: 120) (verbose: 1)
  [∀ (x : Int), resBool (exec vsign [cI x] 150) = true]
#blaster (unfold-depth: 200) (timeout: 120) (verbose: 1)
  [∀ (x : Int), sresBool (seval 60 (sapp vsign [cI x])) = true]
