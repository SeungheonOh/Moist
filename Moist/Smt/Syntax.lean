/-! # Deep-embedded SMT-LIB expression syntax (`SmtExpr`)

The target of the UPLC→SMT denotational compiler.  This is a *deep* embedding: an
`SmtExpr` is a first-order term whose **Lean meaning** is given by `Moist.Smt.evalSmt`
(`Moist/Smt/Semantics.lean`) and whose **SMT-LIB rendering** is given by
`Moist.Smt.toSMTLIB` (`Moist/Smt/Print.lean`).  Trust is split exactly here: the Lean
meaning is what every theorem is stated against; the SMT-LIB rendering plus z3's verdict
is the `z3_sound` axiom (the accepted compromise).

This is the **v0 fragment**: base sorts `int`/`bool` only — sufficient for the
straight-line / arithmetic validator class (the benchmarked validators).  `Data` and
bytestrings extend `SmtSort`/`SmtExpr` in later stages (§10 of the plan); the AST is kept
deliberately small so the meaning function and the adequacy proof stay tractable.

Design notes
* The AST is **untyped** (sorts are not enforced by construction); a separate `sortOf`
  classifier recovers the sort (or `none` if ill-sorted).  `evalSmt` is nonetheless
  *total* — ill-sorted nodes evaluate to a dedicated junk value `SVal.bad` — which keeps
  the concretization `γ` total and the adequacy proof an honest equation rather than an
  `Option`-juggling exercise.  Everything the compiler emits is well-sorted by
  construction (`sortOf … = some _`), so the junk branch is never reached on real output;
  that fact is what differential testing (§9) checks.
-/

namespace Moist.Smt

/-- Base SMT sorts.  `int`/`bool` are the v0 core; `data` (Plutus `Data`, an SMT recursive
    datatype) and `bytes` (Plutus `ByteString`) are the v1/v2 extensions for real validators. -/
inductive SmtSort
  | int
  | bool
  | data
  | bytes
  -- Polymorphic builtin types: `BuiltinList a` and `BuiltinPair a b` (Plutus higher-order
  -- builtin types).  E.g. `unConstrData : Data → pair int (list data)`,
  -- `unListData : Data → list data`, `unMapData : Data → list (pair data data)`.
  | list : SmtSort → SmtSort
  | pair : SmtSort → SmtSort → SmtSort
deriving Repr, DecidableEq, BEq, Inhabited

/-- Binary operators.  Integer arithmetic is total in the embedding — the partiality of
    `divide`/`modulo` (division by zero) is carried *separately* as a definedness guard
    (`SymOut.defined`), never as a partial `evalSmt`.  Division/modulo come in two flavours
    matching Plutus: `fdiv`/`fmod` are **floored** (`Int.fdiv`/`Int.fmod`, used by
    `DivideInteger`/`ModInteger`); `tdiv`/`tmod` **truncate** toward zero
    (`Int.tdiv`/`Int.tmod`, used by `QuotientInteger`/`RemainderInteger`). -/
inductive BinOp
  -- int × int → int
  | add | sub | mul | fdiv | fmod | tdiv | tmod
  -- int × int → bool
  | le | lt
  -- α × α → bool   (same-sort equality; here int or bool)
  | eq
  -- bool × bool → bool
  | and_ | or_
deriving Repr, DecidableEq, BEq, Inhabited

/-- Unary operators over `data`/`bytes`: Plutus `Data` injection/projection, constructor
    testers, and `lengthOfByteString`.  Testers drive `chooseData` dispatch and the
    definedness guards of the partial projections (`unIData` is defined iff `isI`, …). -/
inductive UnOp
  | iData | bData                      -- inject:  int→data, bytes→data
  | unIData | unBData | constrTag      -- project: data→int, data→bytes, data→int (Constr tag)
  | lenBytes                           -- bytes → int
  | isI | isB | isConstr | isList | isMap   -- data → bool (constructor testers)
  -- Data → structured (the `list`-yielding projections of `Data`'s constructors):
  | dArgs                              -- data → list data        (a `Constr`'s fields)
  | dItems                            -- data → list data        (a `List`'s items; `unListData`)
  | dEntries                          -- data → list (pair data data)  (a `Map`'s entries; `unMapData`)
deriving Repr, DecidableEq, BEq, Inhabited

/-- Deep-embedded SMT expressions over `int`/`bool`/`data`/`bytes`. -/
inductive SmtExpr
  | var  : String → SmtSort → SmtExpr          -- a free SMT variable (a symbolic input)
  | litI : Int → SmtExpr
  | litB : Bool → SmtExpr
  | neg  : SmtExpr → SmtExpr                    -- integer negation
  | not  : SmtExpr → SmtExpr                    -- boolean negation
  | bin  : BinOp → SmtExpr → SmtExpr → SmtExpr
  | uop  : UnOp → SmtExpr → SmtExpr             -- data/bytes unary op
  | ite  : SmtExpr → SmtExpr → SmtExpr → SmtExpr  -- (cond, then, else); polymorphic result
  -- Polymorphic builtin Pair / List operations (sorts computed from operands, see `sortOf`):
  | mkpair : SmtExpr → SmtExpr → SmtExpr        -- a → b → pair a b
  | fstP   : SmtExpr → SmtExpr                  -- pair a b → a
  | sndP   : SmtExpr → SmtExpr                  -- pair a b → b
  | nilL   : SmtSort → SmtExpr                  -- (element sort) → list elt   (typed empty list)
  | consL  : SmtExpr → SmtExpr → SmtExpr        -- a → list a → list a
  | headL  : SmtSort → SmtExpr → SmtExpr        -- (element sort) → list a → a  (junk-of-sort if empty)
  | tailL  : SmtExpr → SmtExpr                  -- list a → list a
  | nullL  : SmtExpr → SmtExpr                  -- list a → bool
deriving Repr, DecidableEq, BEq, Inhabited

/-- Result sort of a binary operator given its operand sort (`none` if inapplicable). -/
def BinOp.resultSort : BinOp → SmtSort → Option SmtSort
  | .add, .int | .sub, .int | .mul, .int
  | .fdiv, .int | .fmod, .int | .tdiv, .int | .tmod, .int => some .int
  | .le, .int | .lt, .int => some .bool
  -- equality is over the *scalar* sorts only (int/bool/data/bytes); structured equality is
  -- not a supported builtin, and `evalBin .eq` is junk on `pair`/`list`.
  | .eq, .int | .eq, .bool | .eq, .data | .eq, .bytes => some .bool
  | .and_, .bool | .or_, .bool => some .bool
  | _, _ => none

/-- Operand sort and result sort of a unary operator. -/
def UnOp.sorts : UnOp → SmtSort × SmtSort
  | .iData => (.int, .data)     | .bData => (.bytes, .data)
  | .unIData => (.data, .int)   | .unBData => (.data, .bytes)
  | .constrTag => (.data, .int) | .lenBytes => (.bytes, .int)
  | .isI => (.data, .bool)      | .isB => (.data, .bool)
  | .isConstr => (.data, .bool) | .isList => (.data, .bool) | .isMap => (.data, .bool)
  | .dArgs => (.data, .list .data) | .dItems => (.data, .list .data)
  | .dEntries => (.data, .list (.pair .data .data))

namespace SmtExpr

/-! ## Smart constructors (readability for the builtins table / property encoder) -/

@[inline] def trueE  : SmtExpr := .litB true
@[inline] def falseE : SmtExpr := .litB false
@[inline] def andE (a b : SmtExpr) : SmtExpr := .bin .and_ a b
@[inline] def orE  (a b : SmtExpr) : SmtExpr := .bin .or_ a b
@[inline] def eqE  (a b : SmtExpr) : SmtExpr := .bin .eq a b
@[inline] def impE (a b : SmtExpr) : SmtExpr := .bin .or_ (.not a) b
@[inline] def neZeroE (e : SmtExpr) : SmtExpr := .not (.bin .eq e (.litI 0))

/-- Conjoin a list of definedness guards. -/
def conj : List SmtExpr → SmtExpr
  | []      => trueE
  | [e]     => e
  | e :: es => andE e (conj es)

/-! ## Sort classification

`sortOf e = some s` certifies that `e` is well-sorted with sort `s`; `none` flags an
ill-sorted node.  Used by the printer (Int vs Bool context) and as the `WellSorted`
sanity predicate that differential testing checks on compiler output. -/

def sortOf : SmtExpr → Option SmtSort
  | .var _ s => some s
  | .litI _  => some .int
  | .litB _  => some .bool
  | .neg e   => match sortOf e with | some .int => some .int | _ => none
  | .not e   => match sortOf e with | some .bool => some .bool | _ => none
  | .bin op a b =>
    match sortOf a, sortOf b with
    | some sa, some sb => if sa = sb then BinOp.resultSort op sa else none
    | _, _ => none
  | .uop op e =>
    match sortOf e with
    | some s => if s = (UnOp.sorts op).1 then some (UnOp.sorts op).2 else none
    | none => none
  | .ite c a b =>
    match sortOf c, sortOf a, sortOf b with
    | some .bool, some sa, some sb => if sa = sb then some sa else none
    | _, _, _ => none
  | .mkpair a b =>
    match sortOf a, sortOf b with
    | some sa, some sb => some (.pair sa sb)
    | _, _ => none
  | .fstP e => match sortOf e with | some (.pair sa _) => some sa | _ => none
  | .sndP e => match sortOf e with | some (.pair _ sb) => some sb | _ => none
  | .nilL s => some (.list s)
  | .consL h t =>
    match sortOf h, sortOf t with
    | some sh, some (.list st) => if sh = st then some (.list sh) else none
    | _, _ => none
  | .headL s e => match sortOf e with | some (.list s') => if s = s' then some s else none | _ => none
  | .tailL e => match sortOf e with | some (.list s) => some (.list s) | _ => none
  | .nullL e => match sortOf e with | some (.list _) => some .bool | _ => none

/-- A `Bool`-sorted expression (used for definedness flags and properties). -/
@[inline] def WellSortedBool (e : SmtExpr) : Prop := sortOf e = some .bool

end SmtExpr

end Moist.Smt
