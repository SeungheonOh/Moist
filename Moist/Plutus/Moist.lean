import Lean.Meta
import Lean.Elab
import Lean

import Moist.Plutus.Term
import Moist.Plutus.Encode

namespace Moist.Plutus.Moist

open Moist.Plutus.Term
open Moist.Plutus.Encode
open Lean.Meta
open Lean.Elab
open Lean.Elab.Tactic
open Moist.Plutus (Integer)

--inductive MTerm
universe u v

inductive PTerm' (t : Type) : Type where
  | toTerm : (Nat → Option Term) → PTerm' t

class PlutusType (t : Type) where
  PInner : Type
  pcon' : t → PTerm' PInner
  pmatch' : PTerm' PInner → (t → PTerm' r) → PTerm' r

--abbrev PInner (C) [PlutusType C] := PlutusType.PInner C
@[reducible]def PInner (C : Type) [PlutusType C] := PlutusType.PInner C
-- TIL @[reducible]def ∼ abbrev

def PTerm (t :Type) [PlutusType t] : Type :=
  PTerm' t

def runPTerm [PlutusType a] (n : Nat) (x : PTerm a) : Option Term :=
  match x with
  | PTerm'.toTerm f => f n

namespace PTerm
def compile [PlutusType a] (t : PTerm a) : Option Term.Program :=
  .Program (.Version 1 1 0) <$> runPTerm 0 t

def compile! [PlutusType a] (t : PTerm a) : Term.Program :=
  match t.compile with
  | .none => panic! "compilation failed"
  | .some a => a
end PTerm

instance [PlutusType a] : Repr (PTerm a) where
  reprPrec x n := reprPrec x.compile! n

#check List.get!

def punsafeCoerce [PlutusType a] [PlutusType b] (x : PTerm a) : PTerm b :=
  match x with
  | PTerm'.toTerm f => PTerm'.toTerm f

def punsafeBuiltin [PlutusType b] (bf : BuiltinFun) : PTerm b :=
  PTerm'.toTerm (fun _ => Term.Builtin bf)

def pcon [PlutusType t] [PlutusType (PInner t)] (x : t) : PTerm t :=
  punsafeCoerce (PlutusType.pcon' x)

def pmatch [PlutusType t] [PlutusType (PInner t)] [PlutusType r]
  (x : PTerm t) (f : t → PTerm r) : PTerm r :=
  PlutusType.pmatch' (punsafeCoerce x : PTerm (PInner t)) f



inductive Opaque
  | mk : Opaque

inductive Maybe a
  | nothing : Maybe a
  | just : a → Maybe a

instance PlutusType_PInner [PlutusType a] : PlutusType (PInner a) where
  PInner := PInner a
  pcon' m := PTerm'.toTerm (fun n => none)
  pmatch' m f := PTerm'.toTerm (fun n => none)

instance PlutusType_Opaque : PlutusType Opaque where
  PInner := Opaque
  pcon' m := PTerm'.toTerm (fun _ => none)
  pmatch' m f := PTerm'.toTerm (fun _ => none)

instance PlutusType_Maybe (a : Type) [PlutusType a] : PlutusType (Maybe a) where
  PInner := Opaque
  pcon' m := PTerm'.toTerm (fun _ => none)
  pmatch' m f := PTerm'.toTerm (fun _ => none)

instance PlutusType_Nat : PlutusType Nat where
  PInner := Int
  pcon' m := PTerm'.toTerm (fun _ => none)
  pmatch' m f := PTerm'.toTerm (fun _ => none)

instance PlutusType_Integer : PlutusType Integer where
  PInner := Opaque
  pcon' m := PTerm'.toTerm (fun _ => none)
  pmatch' m f := PTerm'.toTerm (fun _ => none)

instance PlutusType_Arrow [PlutusType a] [PlutusType b] : PlutusType (a → b) where
  PInner := Opaque
  pcon' m := PTerm'.toTerm (fun _ => none)
  pmatch' m f := PTerm'.toTerm (fun _ => none)

def padd : PTerm (Integer → Integer → Integer) :=
  punsafeBuiltin BuiltinFun.AddInteger

def plam' [PlutusType a] [PlutusType b] (f: PTerm a → PTerm b) : PTerm (a → b) :=
  PTerm'.toTerm (λ i =>
    let v : PTerm a := PTerm'.toTerm (λ j => .some (.Var (j - i)))
    .Lam 0 <$> runPTerm (i+1) (f v)
  )

def papp' [PlutusType a] [PlutusType b] (f : PTerm (a → b)) (x : PTerm a) : PTerm b :=
  PTerm'.toTerm (λ i =>
    match runPTerm i f, runPTerm i x with
    | .some f', .some x' => .some (.Apply f' x')
    | _, _ => none
  )

def perror {r : Type} [PlutusType r]: PTerm r :=
  PTerm'.toTerm (λ _ => .some Term.Error)

class Foo (a : Type u) where
  foo : Type u

instance [PlutusType a] : Foo (PTerm a) where
  foo := a

instance [PlutusType a] [PlutusType b] : Foo (PTerm a → PTerm b) where
  foo := a → b


#reduce (types := true) Foo.foo (PTerm Nat → PTerm Opaque)

infixl:60 " ⊕ " => fun l r => (!l && r) || (l && !r)

def mytermValues := [1, 2]

infixl:80 " # "  => papp'
infixr:0  " #$ " => papp'
infix:10  " #+ " => padd

def IsPTerm (e : Lean.Expr) : Bool :=
  match e with
    | .app (.app (.const ``PTerm ..) ..) .. => true
    | .app (.const ``PTerm' ..) .. => true
    | _ => false

elab "plam" lam:term : term => do
  let ty ← Lean.Meta.inferType (← Lean.Elab.Term.elabTerm lam none)
  forallTelescope ty fun argTs _resultTy => -- check returnTy
    match argTs.toList with
    | [] => throwError "plam: expected at least one argument"
    | ts => do
      let ids ← ts.foldrM (λ t r => do
        let argTy ← whnf (← Lean.Meta.inferType t)
        if IsPTerm argTy
        then return (← Lean.Elab.Term.mkFreshIdent (Lean.mkIdent `x)) :: r
        else throwError "plam: all argument types and return type must be PTerm"
        ) []
      let apps ← ids.foldlM (λ r (x : Lean.Ident) => `($r $x)) lam
      let lams ← ids.foldrM (λ (x : Lean.Ident) r => `(plam' λ $x => $r)) apps
      Lean.Elab.Term.elabTerm lams none



#check Lean.mkApp
#check Lean.mkLambdaEx
#check Lean.Meta.withLocalDecl
#check Repr

#check PTerm Unit

#check `(λ x => x)

def myFunc (x : Integer) := x + 1

def foo := 1
def bar (x : Nat) : Nat := x + 1
def baz (_x : PTerm Integer) : PTerm Integer := perror
def bob (a b c : PTerm Integer) : PTerm Integer :=
  padd # a #$ padd # b # c

#eval (plam bob).compile!.encode.toHexString

#eval plam bob

#check plam bob

#eval (plam bob).compile!













#check  plam' λ b => plam' λ a => (λ (x : PTerm Nat) (y : PTerm Nat) => pcon (42 : Nat)) a b

#eval mkAppM ``List.get! #[.const ``mytermValues [], Lean.mkNatLit 1]
#eval `(λ x => x)
#eval do Lean.Elab.Term.elabTerm (← `(λ x => x)) none

#check Lean.Elab.Term.elabTermEnsuringType


#check plam' (λ (_ : PTerm Nat) => @perror Opaque _)

#eval! runPTerm 0 (plam' (λ (x : PTerm Nat) => plam' (λ (y : PTerm Nat) => plam' (λ (z : PTerm Nat) => papp' (@perror (Nat → Opaque) _) z))))

#reduce (types := true) PInner (PInner (PInner (Opaque)))

#reduce PInner

#reduce (types := true) PlutusType.PInner Nat



end Moist.Plutus.Moist
