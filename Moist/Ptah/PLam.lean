import Moist.Ptah.Term
import Lean

namespace Moist.Ptah

open Moist.MIR (Expr FreshM freshVar)

def plam' [PType a] [PType b] (f : Term a → Term b) : Term (a → b) := ⟨do
  let v ← freshVar "x"
  let body ← (f ⟨pure (.Var v)⟩).build
  pure (.Lam v body)
⟩

def papp [PType a] [PType b] (f : Term (a → b)) (x : Term a) : Term b := ⟨do
  let f' ← f.build
  let x' ← x.build
  pure (.App f' x')
⟩

infixl:80 " # " => papp
infixr:0 " #$ " => papp

def plet [PType a] [PType b] (x : Term a) (f : Term a → Term b) : Term b := ⟨do
  let v ← freshVar "let"
  let rhs ← x.build
  let body ← (f ⟨pure (.Var v)⟩).build
  pure (.Let [(v, rhs, false)] body)
⟩

def pdelay [PType a] (x : Term a) : Term (PDelayed a) := ⟨do
  let e ← x.build
  pure (.Delay e)
⟩

def pforce [PType a] (x : Term (PDelayed a)) : Term a := ⟨do
  let e ← x.build
  pure (.Force e)
⟩

def pfix [PType a] [PType b] (f : Term (a → b) → Term a → Term b) : Term (a → b) := ⟨do
  let vself ← freshVar "self"
  let varg ← freshVar "x"
  let body ← (f ⟨pure (.Var vself)⟩ ⟨pure (.Var varg)⟩).build
  pure (.Fix vself (.Lam varg body))
⟩

private def isTerm (e : Lean.Expr) : Bool :=
  e.isAppOf ``Term

open Lean Meta Elab Term in
elab "plam" f:term : term => do
  let expr ← elabTerm f none
  let ty ← inferType expr
  forallTelescope ty fun argTs _ =>
    match argTs.toList with
    | [] => throwError "plam: expected at least one argument"
    | ts => do
      let ids ← ts.foldrM (fun t r => do
        let argTy ← whnf (← inferType t)
        if isTerm argTy
        then return (← mkFreshIdent (mkIdent `x)) :: r
        else throwError "plam: all arguments must have type `Term _`, got {argTy}"
      ) []
      let plam'Id := mkIdent ``plam'
      let apps ← ids.foldlM (fun r (x : Ident) => `($r $x)) f
      let lams ← ids.foldrM (fun (x : Ident) r => `($plam'Id fun $x => $r)) apps
      elabTerm lams none

end Moist.Ptah
