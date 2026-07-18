import Moist.SMT.Compiler.UPLC.SymbolicValue

/-!
# UPLC compiler declarations

Proof-free symbolic input declarations, mandatory assumptions, and conversion
to the compiler environment and typed SMT command AST.
-/

namespace Moist.SMT.UPLC

def symDeclRequired? (name : String) (sort : Moist.SMT.SSort)
    (value : SymVal) : Option (List SExpr) :=
  match sort, value with
  | .int, .const (.integer (.sym n)) =>
      if n == name then some [] else none
  | .bool, .const (.bool (.sym n)) =>
      if n == name then some [] else none
  | .bytes, .const (.bytes (.sym n)) =>
      if n == name then some [.app "bytes_valid" [.sym n]] else none
  | .string, .const (.string (.sym n)) =>
      if n == name then some [.app "ustring_valid" [.sym n]] else none
  | .data, .const (.data (.sym n)) =>
      if n == name then some [.app "data_valid" [.sym n]] else none
  | .val, .dyn (.sym n) =>
      if n == name then some [.app "val_valid" [.sym n]] else none
  | .int, .constr (.sym n) _ =>
      if n == name then some [SExpr.ge (.sym n) (.int 0)] else none
  | _, _ => none

/-- Proof-free symbolic input declaration.

The production boundary validates the relationship between these four fields
computationally.  Keeping this record free of erased Lean evidence makes its
runtime representation and trust boundary directly portable to other
languages. -/
structure SymDecl where
  name : String
  sort : Moist.SMT.SSort
  value : SymVal
  assumptions : List SExpr := []
deriving Repr

namespace SymDecl

/-- Add user constraints without removing existing mandatory assumptions.
The complete declaration is revalidated by the production input gate. -/
def withAssumptions (d : SymDecl) (extra : List SExpr) : SymDecl :=
  { name := d.name
    sort := d.sort
    value := d.value
    assumptions := d.assumptions ++ extra }

end SymDecl

def symInt (name : String) : SymDecl :=
  let n := Moist.SMT.sanitize name
  ⟨n, .int, .const (.integer (.sym n)), []⟩

def symBool (name : String) : SymDecl :=
  let n := Moist.SMT.sanitize name
  ⟨n, .bool, .const (.bool (.sym n)), []⟩

def symBytes (name : String) : SymDecl :=
  let n := Moist.SMT.sanitize name
  ⟨n, .bytes, .const (.bytes (.sym n)), [.app "bytes_valid" [.sym n]]⟩

def symString (name : String) : SymDecl :=
  let n := Moist.SMT.sanitize name
  ⟨n, .string, .const (.string (.sym n)), [.app "ustring_valid" [.sym n]]⟩

def symData (name : String) : SymDecl :=
  let n := Moist.SMT.sanitize name
  ⟨n, .data, .const (.data (.sym n)), [.app "data_valid" [.sym n]]⟩

def symVal (name : String) : SymDecl :=
  let n := Moist.SMT.sanitize name
  ⟨n, .val, .dyn (.sym n), [.app "val_valid" [.sym n]]⟩

def symConstr (name : String) (fields : List SymVal := []) : SymDecl :=
  let n := Moist.SMT.sanitize name
  ⟨n, .int, .constr (.sym n) fields, [SExpr.ge (.sym n) (.int 0)]⟩

/-- Build the symbolic environment in declaration order.  UPLC variables are
one-based, so `Var 1` denotes the first declaration, `Var 2` the second, and
so on; callers must not reverse this list as they would a stack of nested
lambda binders. -/
def envOf (decls : List SymDecl) : List SymVal :=
  decls.map SymDecl.value

def declCommands (decls : List SymDecl) : List Moist.SMT.Command :=
  decls.map (fun d => .declareConst d.name d.sort)

def assumptionCommands (decls : List SymDecl) : List Moist.SMT.Command :=
  decls.flatMap fun d => d.assumptions.map Moist.SMT.Command.assert


end Moist.SMT.UPLC
