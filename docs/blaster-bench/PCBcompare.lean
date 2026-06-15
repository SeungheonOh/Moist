import PlutusCore.UPLC.CekMachine
import PlutusCore.Integer.Lemmas
import Blaster

open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.Integer

/-! ## Term DSL -/
abbrev cI (n : Int) : Term := .Const (.Integer n)
abbrev vr (s : String) : Term := .Var s
abbrev b2 (op : BuiltinFun) (a c : Term) : Term := .Apply (.Apply (.Builtin op) a) c
def add (a b : Term) := b2 .AddInteger a b
def sub (a b : Term) := b2 .SubtractInteger a b
def mul (a b : Term) := b2 .MultiplyInteger a b
def le  (a b : Term) := b2 .LessThanEqualsInteger a b
def lams (xs : List String) (body : Term) : Term := xs.foldr Term.Lam body

/-! ## Validators (more involved: multi-arg, nonlinear) -/

-- AM-GM:  2xy ≤ x²+y²
def amgm : Term := lams ["x","y"]
  (le (mul (mul (cI 2) (vr "x")) (vr "y")) (add (mul (vr "x") (vr "x")) (mul (vr "y") (vr "y"))))
-- constant-product swap:  xy ≤ (x+dx)(y-dy)
def vswap : Term := lams ["x","y","dx","dy"]
  (le (mul (vr "x") (vr "y")) (mul (add (vr "x") (vr "dx")) (sub (vr "y") (vr "dy"))))
-- composed swap:  xy ≤ (x+dx1+dx2)(y-dy1-dy2)
def vcomp : Term := lams ["x","y","dx1","dy1","dx2","dy2"]
  (le (mul (vr "x") (vr "y"))
      (mul (add (add (vr "x") (vr "dx1")) (vr "dx2")) (sub (sub (vr "y") (vr "dy1")) (vr "dy2"))))
-- multiplicative monotonicity:  x ≤ x*y
def vmono : Term := lams ["x","y"] (le (vr "x") (mul (vr "x") (vr "y")))

/-! ## Baseline: PCB Blaster-optimized CEK -/
abbrev exec (t : Term) (ps : List Term) (n : Nat) : State :=
  cekExecuteProgram (.Program (.Version 1 1 0) t) ps n
def resBool : State → Bool | .Halt (.VCon (.Bool b)) => b | _ => false

/-! ## Optimized small-step (same Term + builtins, no closures / reflect / discharge) -/
def subst (x : String) (v : Term) : Term → Term
  | .Var y => if x == y then v else .Var y
  | .Lam y b => if x == y then .Lam y b else .Lam y (subst x v b)
  | .Apply f a => .Apply (subst x v f) (subst x v a)
  | .Force t => .Force (subst x v t)
  | .Delay t => .Delay (subst x v t)
  | t => t
def evalB2 : BuiltinFun → Const → Const → Option Const
  | .AddInteger,            .Integer x, .Integer y => some (.Integer (addInteger x y))
  | .SubtractInteger,       .Integer x, .Integer y => some (.Integer (subtractInteger x y))
  | .MultiplyInteger,       .Integer x, .Integer y => some (.Integer (multiplyInteger x y))
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
  | _ => none
termination_by t => sizeOf t
def seval : Nat → Term → Term
  | 0, t => t
  | n + 1, t => match sstep t with | some t' => seval n t' | none => t
def sapp (t : Term) (ps : List Term) : Term := ps.foldl Term.Apply t
def sresBool : Term → Bool | .Const (.Bool b) => b | _ => false

-- sanity
#eval resBool  (exec  amgm [cI 3, cI 5] 200)              -- true (30 ≤ 34)
#eval sresBool (seval 100 (sapp amgm [cI 3, cI 5]))       -- true
#eval resBool  (exec  vcomp [cI 100,cI 100,cI 10,cI 9,cI 5,cI 4] 300)  -- true

/-! ## Involved proofs — CEK then optimized small-step, per validator. -/

-- 1. AM-GM (unconditional nonlinear): 2xy ≤ x²+y²
#blaster (unfold-depth: 300) (timeout: 120) (verbose: 1)
  [∀ (x y : Int), resBool (exec amgm [cI x, cI y] 200) = true]
#blaster (unfold-depth: 250) (timeout: 120) (verbose: 1)
  [∀ (x y : Int), sresBool (seval 80 (sapp amgm [cI x, cI y])) = true]

-- 2. swap, strict ⇒ nonstrict hypothesis
#blaster (unfold-depth: 300) (timeout: 120) (verbose: 1)
  [∀ (x y dx dy : Int), x*y < (x+dx)*(y-dy) → resBool (exec vswap [cI x,cI y,cI dx,cI dy] 300) = true]
#blaster (unfold-depth: 250) (timeout: 120) (verbose: 1)
  [∀ (x y dx dy : Int), x*y < (x+dx)*(y-dy) → sresBool (seval 100 (sapp vswap [cI x,cI y,cI dx,cI dy])) = true]

-- 3. swap composition (transitivity, 6 vars, 2 hyps)
#blaster (unfold-depth: 400) (timeout: 120) (dump-smt-lib: 1) (verbose: 1)
  [∀ (x y dx1 dy1 dx2 dy2 : Int),
     x*y ≤ (x+dx1)*(y-dy1) → (x+dx1)*(y-dy1) ≤ (x+dx1+dx2)*(y-dy1-dy2) →
     resBool (exec vcomp [cI x,cI y,cI dx1,cI dy1,cI dx2,cI dy2] 400) = true]
#blaster (unfold-depth: 350) (timeout: 120) (dump-smt-lib: 1) (verbose: 1)
  [∀ (x y dx1 dy1 dx2 dy2 : Int),
     x*y ≤ (x+dx1)*(y-dy1) → (x+dx1)*(y-dy1) ≤ (x+dx1+dx2)*(y-dy1-dy2) →
     sresBool (seval 140 (sapp vcomp [cI x,cI y,cI dx1,cI dy1,cI dx2,cI dy2])) = true]

-- 4. multiplicative monotonicity: 0≤x, 1≤y ⇒ x ≤ x*y
#blaster (unfold-depth: 300) (timeout: 120) (verbose: 1)
  [∀ (x y : Int), 0 ≤ x → 1 ≤ y → resBool (exec vmono [cI x, cI y] 200) = true]
#blaster (unfold-depth: 250) (timeout: 120) (verbose: 1)
  [∀ (x y : Int), 0 ≤ x → 1 ≤ y → sresBool (seval 80 (sapp vmono [cI x, cI y])) = true]
