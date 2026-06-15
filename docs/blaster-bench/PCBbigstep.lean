import PlutusCore.UPLC.CekMachine
import PlutusCore.Integer.Lemmas
import Blaster

open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.Integer

/-! # Big-step vs CEK (vs small-step) under Blaster

Same `Term`, same builtins (`@[simp]` denotations), same Blaster + Z3 — isolates the
evaluation strategy. Big-step = environment-free recursive descent to values (CEK minus
the defunctionalized continuation; small-step minus the re-traversal-per-redex). -/

/-! ## Term DSL -/
abbrev cI (n : Int) : Term := .Const (.Integer n)
abbrev vr (s : String) : Term := .Var s
abbrev b2 (op : BuiltinFun) (a c : Term) : Term := .Apply (.Apply (.Builtin op) a) c
def add (a b : Term) := b2 .AddInteger a b
def sub (a b : Term) := b2 .SubtractInteger a b
def mul (a b : Term) := b2 .MultiplyInteger a b
def le  (a b : Term) := b2 .LessThanEqualsInteger a b
def lams (xs : List String) (body : Term) : Term := xs.foldr Term.Lam body

/-! ## Validators -/
def amgm : Term := lams ["x","y"]
  (le (mul (mul (cI 2) (vr "x")) (vr "y")) (add (mul (vr "x") (vr "x")) (mul (vr "y") (vr "y"))))
def vswap : Term := lams ["x","y","dx","dy"]
  (le (mul (vr "x") (vr "y")) (mul (add (vr "x") (vr "dx")) (sub (vr "y") (vr "dy"))))
def vcomp : Term := lams ["x","y","dx1","dy1","dx2","dy2"]
  (le (mul (vr "x") (vr "y"))
      (mul (add (add (vr "x") (vr "dx1")) (vr "dx2")) (sub (sub (vr "y") (vr "dy1")) (vr "dy2"))))
def vmono : Term := lams ["x","y"] (le (vr "x") (mul (vr "x") (vr "y")))
-- scaling: 0 ≤ x*x + ... (n squares)
def sumSq (k : Nat) : Term :=
  lams ["x"] (le (cI 0) ((List.range k).foldl (fun acc _ => add acc (mul (vr "x") (vr "x"))) (mul (vr "x") (vr "x"))))

/-! ## Baseline: PCB Blaster-optimized CEK -/
abbrev exec (t : Term) (ps : List Term) (n : Nat) : State :=
  cekExecuteProgram (.Program (.Version 1 1 0) t) ps n
def resBool : State → Bool | .Halt (.VCon (.Bool b)) => b | _ => false

/-! ## Shared builtin denotation + substitution (Blaster-friendly: native Int ops) -/
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
def spine1? : Term → Option (BuiltinFun × Const)
  | .Apply (.Builtin op) (.Const c1) => some (op, c1) | _ => none

/-! ## Optimized small-step (one redex per `sstep`, looped) -/
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
def sresBool : Term → Bool | .Const (.Bool b) => b | _ => false

/-! ## Big-step: recursive descent to values (no frames, no re-traversal) -/
def beval : Nat → Term → Term
  | 0, t => t
  | n + 1, .Force t =>
      match beval n t with
      | .Delay d => beval n d
      | v => .Force v
  | n + 1, .Apply f a =>
      let fv := beval n f
      let av := beval n a
      match lamBody? fv with
      | some (x, body) => beval n (subst x av body)
      | none =>
        match spine1? fv, av with
        | some (op, c1), .Const c2 => (match evalB2 op c1 c2 with | some r => .Const r | none => .Apply fv av)
        | _, _ => .Apply fv av
  | _ + 1, t => t
termination_by n _ => n
def app (t : Term) (ps : List Term) : Term := ps.foldl Term.Apply t
def bresBool : Term → Bool | .Const (.Bool b) => b | _ => false

/-! ## Sanity -/
#eval resBool  (exec  amgm [cI 3, cI 5] 200)                 -- true
#eval sresBool (seval 100 (app amgm [cI 3, cI 5]))           -- true
#eval bresBool (beval 60  (app amgm [cI 3, cI 5]))           -- true
#eval bresBool (beval 60  (app vcomp [cI 100,cI 100,cI 10,cI 9,cI 5,cI 4]))  -- true
#eval bresBool (beval 60  (app vmono [cI 3, cI 4]))          -- true
#eval bresBool (beval 80  (app (sumSq 4) [cI 7]))            -- true

/-! ## Comparison: CEK vs small-step vs big-step, per validator -/

-- AM-GM: 2xy ≤ x²+y²
#blaster (unfold-depth: 300) (timeout: 120) (verbose: 1)
  [∀ (x y : Int), resBool (exec amgm [cI x, cI y] 200) = true]
#blaster (unfold-depth: 250) (timeout: 120) (verbose: 1)
  [∀ (x y : Int), sresBool (seval 80 (app amgm [cI x, cI y])) = true]
#blaster (unfold-depth: 250) (timeout: 120) (dump-smt-lib: 1) (verbose: 1)
  [∀ (x y : Int), bresBool (beval 60 (app amgm [cI x, cI y])) = true]

-- swap (1 hyp)
#blaster (unfold-depth: 300) (timeout: 120) (verbose: 1)
  [∀ (x y dx dy : Int), x*y < (x+dx)*(y-dy) → resBool (exec vswap [cI x,cI y,cI dx,cI dy] 300) = true]
#blaster (unfold-depth: 250) (timeout: 120) (verbose: 1)
  [∀ (x y dx dy : Int), x*y < (x+dx)*(y-dy) → sresBool (seval 100 (app vswap [cI x,cI y,cI dx,cI dy])) = true]
#blaster (unfold-depth: 250) (timeout: 120) (verbose: 1)
  [∀ (x y dx dy : Int), x*y < (x+dx)*(y-dy) → bresBool (beval 60 (app vswap [cI x,cI y,cI dx,cI dy])) = true]

-- swap composition (6 vars, 2 hyps, transitivity)
#blaster (unfold-depth: 400) (timeout: 120) (verbose: 1)
  [∀ (x y dx1 dy1 dx2 dy2 : Int),
     x*y ≤ (x+dx1)*(y-dy1) → (x+dx1)*(y-dy1) ≤ (x+dx1+dx2)*(y-dy1-dy2) →
     resBool (exec vcomp [cI x,cI y,cI dx1,cI dy1,cI dx2,cI dy2] 400) = true]
#blaster (unfold-depth: 350) (timeout: 120) (verbose: 1)
  [∀ (x y dx1 dy1 dx2 dy2 : Int),
     x*y ≤ (x+dx1)*(y-dy1) → (x+dx1)*(y-dy1) ≤ (x+dx1+dx2)*(y-dy1-dy2) →
     sresBool (seval 140 (app vcomp [cI x,cI y,cI dx1,cI dy1,cI dx2,cI dy2])) = true]
#blaster (unfold-depth: 350) (timeout: 120) (verbose: 1)
  [∀ (x y dx1 dy1 dx2 dy2 : Int),
     x*y ≤ (x+dx1)*(y-dy1) → (x+dx1)*(y-dy1) ≤ (x+dx1+dx2)*(y-dy1-dy2) →
     bresBool (beval 80 (app vcomp [cI x,cI y,cI dx1,cI dy1,cI dx2,cI dy2])) = true]

-- monotonicity (2 hyps)
#blaster (unfold-depth: 300) (timeout: 120) (verbose: 1)
  [∀ (x y : Int), 0 ≤ x → 1 ≤ y → resBool (exec vmono [cI x, cI y] 200) = true]
#blaster (unfold-depth: 250) (timeout: 120) (verbose: 1)
  [∀ (x y : Int), 0 ≤ x → 1 ≤ y → bresBool (beval 60 (app vmono [cI x, cI y])) = true]
