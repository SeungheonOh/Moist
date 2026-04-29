import Moist.MIR.Expr
import Moist.Plutus.Term

/-! # UPLC → MIR Decompiler

Lifts a UPLC `Term` (de Bruijn indexed) into an MIR `Expr` (named variables).
MIR is a strict superset of UPLC, so the translation is direct.

The decompiler recognizes the common `(λ. body) arg` pattern and compiles
it to `let x = arg in body`, recovering the let-binding structure that
the inlining pass can optimize.
-/

namespace Moist.MIR

open Moist.Plutus.Term (Term)

private def mkVar (uid : Nat) : VarId :=
  { uid := uid, origin := .source, hint := s!"x{uid}" }

mutual
  partial def fromUPLC (env : List VarId) (nextUid : Nat) : Term → Expr × Nat
    | .Var n =>
      match env[n - 1]? with
      | some v => (.Var v, nextUid)
      | none   => (.Var (mkVar 0), nextUid)
    | .Constant c  => (.Lit c, nextUid)
    | .Builtin b   => (.Builtin b, nextUid)
    | .Error       => (.Error, nextUid)
    | .Apply (.Lam _ body) arg =>
      let v := mkVar nextUid
      let (arg', uid1) := fromUPLC env (nextUid + 1) arg
      let (body', uid2) := fromUPLC (v :: env) uid1 body
      (.Let [(v, arg', false)] body', uid2)
    | .Lam _ body  =>
      let v := mkVar nextUid
      let (body', uid') := fromUPLC (v :: env) (nextUid + 1) body
      (.Lam v body', uid')
    | .Apply f x =>
      let (f', uid1) := fromUPLC env nextUid f
      let (x', uid2) := fromUPLC env uid1 x
      (.App f' x', uid2)
    | .Delay e =>
      let (e', uid') := fromUPLC env nextUid e
      (.Delay e', uid')
    | .Force e =>
      let (e', uid') := fromUPLC env nextUid e
      (.Force e', uid')
    | .Constr tag args =>
      let (args', uid') := fromUPLCList env nextUid args
      (.Constr tag args', uid')
    | .Case scrut alts =>
      let (scrut', uid1) := fromUPLC env nextUid scrut
      let (alts', uid2) := fromUPLCList env uid1 alts
      (.Case scrut' alts', uid2)

  partial def fromUPLCList (env : List VarId) (nextUid : Nat) : List Term → List Expr × Nat
    | [] => ([], nextUid)
    | t :: ts =>
      let (e, uid1) := fromUPLC env nextUid t
      let (es, uid2) := fromUPLCList env uid1 ts
      (e :: es, uid2)
end

def liftUPLC (t : Term) (freshStart : Nat := 1) : Expr :=
  (fromUPLC [] freshStart t).1

end Moist.MIR
