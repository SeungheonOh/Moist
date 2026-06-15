import PlutusCore.UPLC.CekMachine
import PlutusCore.Integer.Lemmas
import Blaster

open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.Integer

/-! ## Term DSL incl. control flow -/
abbrev cI (n : Int) : Term := .Const (.Integer n)
abbrev vr (s : String) : Term := .Var s
abbrev b2 (op : BuiltinFun) (a c : Term) : Term := .Apply (.Apply (.Builtin op) a) c
def add (a b : Term) := b2 .AddInteger a b
def sub (a b : Term) := b2 .SubtractInteger a b
def mul (a b : Term) := b2 .MultiplyInteger a b
def le  (a b : Term) := b2 .LessThanEqualsInteger a b
def lt  (a b : Term) := b2 .LessThanInteger a b
def caseB (scrut t e : Term) : Term := .Case scrut [t, e]   -- PCB: false→[0], true→[1]
def lams (xs : List String) (body : Term) : Term := xs.foldr Term.Lam body

/-! ## Control-flow validators -/
-- 0 ≤ |x| via case on (x<0)
def vabs : Term := lams ["x"] (caseB (lt (vr "x") (cI 0)) (le (cI 0) (vr "x")) (le (cI 0) (sub (cI 0) (vr "x"))))
-- same, but with the real lazy pattern: force (case … [delay …, delay …])
def vabsLazy : Term := lams ["x"]
  (.Force (caseB (lt (vr "x") (cI 0)) (.Delay (le (cI 0) (vr "x"))) (.Delay (le (cI 0) (sub (cI 0) (vr "x"))))))
-- x ≤ max(x,y), with case nested inside a builtin argument
def vmax : Term := lams ["x","y"] (le (vr "x") (caseB (le (vr "x") (vr "y")) (vr "x") (vr "y")))

/-! ## CEK baseline -/
abbrev exec (t : Term) (ps : List Term) (n : Nat) : State :=
  cekExecuteProgram (.Program (.Version 1 1 0) t) ps n
def resBool : State → Bool | .Halt (.VCon (.Bool b)) => b | _ => false

/-! ## Optimized small-step with control flow (Force/Delay/Case-on-Bool) -/
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
def isValue : Term → Bool
  | .Const _ | .Lam _ _ | .Builtin _ | .Delay _ => true
  | t => (spine1? t).isSome
def sstep : Term → Option Term
  | .Apply f a =>
    if isValue f then
      if isValue a then
        match lamBody? f with
        | some (x, body) => some (subst x a body)
        | none => match spine1? f, a with
          | some (op, c1), .Const c2 => (match evalB2 op c1 c2 with | some r => some (.Const r) | none => none)
          | _, _ => none
      else (match sstep a with | some a' => some (.Apply f a') | none => none)
    else (match sstep f with | some f' => some (.Apply f' a) | none => none)
  | .Force t =>
    if isValue t then (match t with | .Delay m => some m | _ => none)
    else (match sstep t with | some t' => some (.Force t') | none => none)
  | .Case scrut alts =>
    if isValue scrut then
      match scrut, alts with
      | .Const (.Bool b), [m0, m1] => some (if b then m1 else m0)
      | _, _ => none
    else (match sstep scrut with | some s' => some (.Case s' alts) | none => none)
  | _ => none
termination_by t => sizeOf t
def seval : Nat → Term → Term
  | 0, t => t
  | n + 1, t => match sstep t with | some t' => seval n t' | none => t
def sapp (t : Term) (ps : List Term) : Term := ps.foldl Term.Apply t
def sresBool : Term → Bool | .Const (.Bool b) => b | _ => false

-- sanity (concrete)
#eval resBool  (exec  vabs [cI (-7)] 200)            -- true
#eval sresBool (seval 80 (sapp vabs [cI (-7)]))      -- true
#eval sresBool (seval 80 (sapp vabsLazy [cI 9]))     -- true
#eval sresBool (seval 80 (sapp vmax [cI 3, cI 8]))   -- true

/-! ## Control-flow proofs (symbolic ⇒ Blaster must split on the branch condition). -/

-- 1. 0 ≤ |x|   (case on x<0)
#blaster (unfold-depth: 300) (timeout: 120) (verbose: 1)
  [∀ (x : Int), resBool (exec vabs [cI x] 200) = true]
#blaster (unfold-depth: 250) (timeout: 120) (verbose: 1)
  [∀ (x : Int), sresBool (seval 80 (sapp vabs [cI x])) = true]

-- 2. lazy: force (case … [delay, delay])
#blaster (unfold-depth: 300) (timeout: 120) (verbose: 1)
  [∀ (x : Int), resBool (exec vabsLazy [cI x] 200) = true]
#blaster (unfold-depth: 250) (timeout: 120) (verbose: 1)
  [∀ (x : Int), sresBool (seval 80 (sapp vabsLazy [cI x])) = true]

-- 3. x ≤ max(x,y)   (case nested in a builtin arg)
#blaster (unfold-depth: 300) (timeout: 120) (dump-smt-lib: 1) (verbose: 1)
  [∀ (x y : Int), resBool (exec vmax [cI x, cI y] 200) = true]
#blaster (unfold-depth: 250) (timeout: 120) (dump-smt-lib: 1) (verbose: 1)
  [∀ (x y : Int), sresBool (seval 80 (sapp vmax [cI x, cI y])) = true]
