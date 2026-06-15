import PlutusCore.UPLC.CekMachine
import PlutusCore.Integer.Lemmas
import PlutusCore.Bool.Lemmas
import Blaster

open PlutusCore.UPLC.Term PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue PlutusCore.Integer

abbrev cI (n : Int) : Term := .Const (.Integer n)
abbrev vr (s : String) : Term := .Var s
abbrev b2 (op : BuiltinFun) (a c : Term) : Term := .Apply (.Apply (.Builtin op) a) c
def add (a b : Term) := b2 .AddInteger a b
def sub (a b : Term) := b2 .SubtractInteger a b
def mul (a b : Term) := b2 .MultiplyInteger a b
def le  (a b : Term) := b2 .LessThanEqualsInteger a b
def lt  (a b : Term) := b2 .LessThanInteger a b
def divI (a b : Term) := b2 .DivideInteger a b
def modI (a b : Term) := b2 .ModInteger a b
def eqI (a b : Term) := b2 .EqualsInteger a b
def ite3 (c t e : Term) : Term := .Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse)) c) t) e

-- A. Euclidean identity:  (x / 7)*7 + (x % 7) = x      (div + mod operators)
def vdivmod : Term := .Lam "x" (eqI (add (mul (divI (vr "x") (cI 7)) (cI 7)) (modI (vr "x") (cI 7))) (vr "x"))
-- B. modulo range:  0 ≤ x % 5   (mod operator; floor mod follows divisor sign)
def vmod : Term := .Lam "x" (le (cI 0) (modI (vr "x") (cI 5)))
-- C. mod with SYMBOLIC divisor under a hypothesis (guard becomes symbolic)
def vmodSym : Term := .Lam "x" (.Lam "d" (le (cI 0) (modI (vr "x") (vr "d"))))

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
  | .DivideInteger,         .Integer x, .Integer y => if y == 0 then none else some (.Integer (Int.fdiv x y))
  | .ModInteger,            .Integer x, .Integer y => if y == 0 then none else some (.Integer (Int.fmod x y))
  | .EqualsInteger,         .Integer x, .Integer y => some (.Bool (x == y))
  | .LessThanInteger,       .Integer x, .Integer y => some (.Bool (lessThanInteger x y))
  | .LessThanEqualsInteger, .Integer x, .Integer y => some (.Bool (lessThanEqualsInteger x y))
  | _, _, _ => none
def lamBody? : Term → Option (String × Term) | .Lam x b => some (x, b) | _ => none
def spine1? : Term → Option (BuiltinFun × Const) | .Apply (.Builtin op) (.Const c1) => some (op, c1) | _ => none
def iteHead2? : Term → Option (Term × Term)
  | .Apply (.Apply (.Force (.Builtin .IfThenElse)) c) t => some (c, t) | _ => none
mutual
def isValue : Term → Bool
  | .Const _ | .Lam _ _ | .Builtin _ | .Delay _ => true
  | .Force (.Builtin .IfThenElse) => true
  | .Apply f a => ((match f with | .Builtin _ => true | _ => false) && isValue a) || (iteVal f && isValue a)
  | _ => false
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
def seval : Nat → Term → Term | 0, t => t | n + 1, t => match sstep t with | some t' => seval n t' | none => t
def sapp (t : Term) (ps : List Term) : Term := ps.foldl Term.Apply t
def sresBool : Term → Bool | .Const (.Bool b) => b | _ => false

#eval resBool (exec vdivmod [cI 23] 200)              -- true (3*7+2=23)
#eval sresBool (seval 60 (sapp vdivmod [cI 23]))      -- true
#eval resBool (exec vmod [cI (-3)] 200)               -- true (-3 mod 5 = 2)
#eval sresBool (seval 60 (sapp vmod [cI (-3)]))       -- true

-- A. div/mod Euclidean identity  (operators: div, mod)
#blaster (unfold-depth: 250) (timeout: 120) (dump-smt-lib: 1) (verbose: 1)
  [∀ (x : Int), resBool (exec vdivmod [cI x] 150) = true]
#blaster (unfold-depth: 200) (timeout: 120) (dump-smt-lib: 1) (verbose: 1)
  [∀ (x : Int), sresBool (seval 60 (sapp vdivmod [cI x])) = true]
-- B. mod range (operator: mod)
#blaster (unfold-depth: 250) (timeout: 120) (dump-smt-lib: 1) (verbose: 1)
  [∀ (x : Int), resBool (exec vmod [cI x] 150) = true]
#blaster (unfold-depth: 200) (timeout: 120) (dump-smt-lib: 1) (verbose: 1)
  [∀ (x : Int), sresBool (seval 60 (sapp vmod [cI x])) = true]
-- C. SYMBOLIC divisor with guard (d>0 hypothesis) — guard handling may differ
#blaster (unfold-depth: 250) (timeout: 120) (dump-smt-lib: 1) (verbose: 1)
  [∀ (x d : Int), 0 < d → resBool (exec vmodSym [cI x, cI d] 150) = true]
#blaster (unfold-depth: 200) (timeout: 120) (dump-smt-lib: 1) (verbose: 1)
  [∀ (x d : Int), 0 < d → sresBool (seval 60 (sapp vmodSym [cI x, cI d])) = true]
