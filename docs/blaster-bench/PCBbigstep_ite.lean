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
def sub (a b : Term) := b2 .SubtractInteger a b
def ite3 (c t e : Term) : Term := .Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse)) c) t) e
def vite : Term := .Lam "x" (le (cI 0) (ite3 (lt (vr "x") (cI 0)) (sub (cI 0) (vr "x")) (vr "x")))
def vsign : Term := .Lam "x"
  (le (ite3 (lt (vr "x") (cI 0)) (sub (cI 0) (cI 1)) (ite3 (lt (cI 0) (vr "x")) (cI 1) (cI 0))) (cI 1))
abbrev exec (t : Term) (ps : List Term) (n : Nat) : State := cekExecuteProgram (.Program (.Version 1 1 0) t) ps n
def resBool : State → Bool | .Halt (.VCon (.Bool b)) => b | _ => false
def subst (x : String) (v : Term) : Term → Term
  | .Var y => if x == y then v else .Var y
  | .Lam y b => if x == y then .Lam y b else .Lam y (subst x v b)
  | .Apply f a => .Apply (subst x v f) (subst x v a)
  | .Force t => .Force (subst x v t) | .Delay t => .Delay (subst x v t) | t => t
def evalB2 : BuiltinFun → Const → Const → Option Const
  | .SubtractInteger, .Integer x, .Integer y => some (.Integer (subtractInteger x y))
  | .LessThanInteger, .Integer x, .Integer y => some (.Bool (lessThanInteger x y))
  | .LessThanEqualsInteger, .Integer x, .Integer y => some (.Bool (lessThanEqualsInteger x y))
  | _, _, _ => none
def lamBody? : Term → Option (String × Term) | .Lam x b => some (x, b) | _ => none
def spine1? : Term → Option (BuiltinFun × Const) | .Apply (.Builtin op) (.Const c1) => some (op, c1) | _ => none
def iteHead2? : Term → Option (Term × Term)
  | .Apply (.Apply (.Force (.Builtin .IfThenElse)) c) t => some (c, t) | _ => none
def beval : Nat → Term → Term
  | 0, t => t
  | n+1, .Force t => match beval n t with | .Delay d => beval n d | v => .Force v
  | n+1, .Apply f a =>
      let fv := beval n f; let av := beval n a
      match lamBody? fv with
      | some (x, body) => beval n (subst x av body)
      | none => match iteHead2? fv with
        | some (cnd, thn) => (match cnd with | .Const (.Bool b) => (if b then thn else av) | _ => .Apply fv av)
        | none => match spine1? fv, av with
          | some (op,c1), .Const c2 => (match evalB2 op c1 c2 with | some r => .Const r | none => .Apply fv av)
          | _,_ => .Apply fv av
  | _+1, t => t
termination_by n _ => n
def app (t : Term) (ps : List Term) : Term := ps.foldl Term.Apply t
def bresBool : Term → Bool | .Const (.Bool b) => b | _ => false
#eval resBool (exec vite [cI (-7)] 200)            -- true
#eval bresBool (beval 60 (app vite [cI (-7)]))     -- true (0 ≤ |-7|)
#eval bresBool (beval 60 (app vsign [cI 5]))       -- true
-- 0 ≤ |x| via strict IfThenElse: CEK vs big-step
#blaster (unfold-depth: 300) (timeout: 90) (verbose: 1) [∀ x:Int, resBool (exec vite [cI x] 200) = true]
#blaster (unfold-depth: 250) (timeout: 90) (verbose: 1) [∀ x:Int, bresBool (beval 60 (app vite [cI x])) = true]
-- nested-ITE sign ≤ 1
#blaster (unfold-depth: 350) (timeout: 90) (verbose: 1) [∀ x:Int, resBool (exec vsign [cI x] 250) = true]
#blaster (unfold-depth: 300) (timeout: 90) (verbose: 1) [∀ x:Int, bresBool (beval 70 (app vsign [cI x])) = true]
