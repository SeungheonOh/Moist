import PlutusCore.UPLC.CekMachine
import PlutusCore.Integer.Lemmas
import Blaster
open PlutusCore.UPLC.Term PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue PlutusCore.Integer
abbrev cI (n : Int) : Term := .Const (.Integer n)
abbrev vr (s : String) : Term := .Var s
abbrev b2 (op : BuiltinFun) (a c : Term) : Term := .Apply (.Apply (.Builtin op) a) c
def add (a b : Term) := b2 .AddInteger a b
def mul (a b : Term) := b2 .MultiplyInteger a b
def le  (a b : Term) := b2 .LessThanEqualsInteger a b
def sumSq (k : Nat) : Term :=
  .Lam "x" (le (cI 0) ((List.range k).foldl (fun acc _ => add acc (mul (vr "x") (vr "x"))) (mul (vr "x") (vr "x"))))
abbrev exec (t : Term) (ps : List Term) (n : Nat) : State := cekExecuteProgram (.Program (.Version 1 1 0) t) ps n
def resBool : State → Bool | .Halt (.VCon (.Bool b)) => b | _ => false
def subst (x : String) (v : Term) : Term → Term
  | .Var y => if x == y then v else .Var y
  | .Lam y b => if x == y then .Lam y b else .Lam y (subst x v b)
  | .Apply f a => .Apply (subst x v f) (subst x v a)
  | .Force t => .Force (subst x v t) | .Delay t => .Delay (subst x v t) | t => t
def evalB2 : BuiltinFun → Const → Const → Option Const
  | .AddInteger, .Integer x, .Integer y => some (.Integer (addInteger x y))
  | .MultiplyInteger, .Integer x, .Integer y => some (.Integer (multiplyInteger x y))
  | .LessThanEqualsInteger, .Integer x, .Integer y => some (.Bool (lessThanEqualsInteger x y))
  | _, _, _ => none
def lamBody? : Term → Option (String × Term) | .Lam x b => some (x, b) | _ => none
def spine1? : Term → Option (BuiltinFun × Const) | .Apply (.Builtin op) (.Const c1) => some (op, c1) | _ => none
def beval : Nat → Term → Term
  | 0, t => t
  | n+1, .Force t => match beval n t with | .Delay d => beval n d | v => .Force v
  | n+1, .Apply f a =>
      let fv := beval n f; let av := beval n a
      match lamBody? fv with
      | some (x, body) => beval n (subst x av body)
      | none => match spine1? fv, av with
        | some (op,c1), .Const c2 => (match evalB2 op c1 c2 with | some r => .Const r | none => .Apply fv av)
        | _,_ => .Apply fv av
  | _+1, t => t
termination_by n _ => n
def app (t : Term) (ps : List Term) : Term := ps.foldl Term.Apply t
def bresBool : Term → Bool | .Const (.Bool b) => b | _ => false
#eval bresBool (beval 80 (app (sumSq 8) [cI 3]))  -- true
#blaster (unfold-depth: 300) (timeout: 90) (verbose: 1) [∀ x:Int, resBool (exec (sumSq 1) [cI x] 200) = true]
#blaster (unfold-depth: 250) (timeout: 90) (verbose: 1) [∀ x:Int, bresBool (beval 60 (app (sumSq 1) [cI x])) = true]
#blaster (unfold-depth: 300) (timeout: 90) (verbose: 1) [∀ x:Int, resBool (exec (sumSq 2) [cI x] 200) = true]
#blaster (unfold-depth: 250) (timeout: 90) (verbose: 1) [∀ x:Int, bresBool (beval 60 (app (sumSq 2) [cI x])) = true]
#blaster (unfold-depth: 350) (timeout: 90) (verbose: 1) [∀ x:Int, resBool (exec (sumSq 4) [cI x] 250) = true]
#blaster (unfold-depth: 300) (timeout: 90) (verbose: 1) [∀ x:Int, bresBool (beval 70 (app (sumSq 4) [cI x])) = true]
#blaster (unfold-depth: 450) (timeout: 90) (verbose: 1) [∀ x:Int, resBool (exec (sumSq 8) [cI x] 350) = true]
#blaster (unfold-depth: 400) (timeout: 90) (verbose: 1) [∀ x:Int, bresBool (beval 90 (app (sumSq 8) [cI x])) = true]
