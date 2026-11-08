import Moist.MIR.Expr
import Moist.Plutus.Term

/-! # Typed random MIR programs for differential testing on the real machine

Programs are closed `λ p₁ … pₙ. body` terms over Data, integer and list
parameters, written in the shapes the onchain translator emits: constructor
decoding through `unConstrData`/`fstPair`/`sndPair` with integer tag chains,
field access through `headList`/`tailList`, list recursion through
`chooseList` or `nullList` cases, map lookups comparing keys with
`equalsData`, Boolean conditions through `ifThenElse` or Boolean cases, record
getters, pairs and options as constructors, traces, errors, let sharing,
partial applications and higher-order helpers.

Every parameter has a Data shape, so the arguments can be valid instances of
it (the program then mostly halts) or mutations of one (the program then
mostly fails), and recursion always shrinks a list or a counter.
-/

namespace Test.MIR.FuzzReal

open Moist.MIR
open Moist.Plutus (Data)
open Moist.Plutus.Term

/-! ## Random source -/

structure GenState where
  seed : UInt64
  next : Nat := 0
  /-- Whether the program may contain `Trace` (several passes skip traced code). -/
  traces : Bool := true
  /-- Whether an expression may occasionally have the wrong type. -/
  confused : Bool := false

abbrev Gen := StateM GenState

def nextWord : Gen UInt64 := do
  let s ← get
  let x := s.seed + 0x9E3779B97F4A7C15
  set { s with seed := x }
  let z := (x ^^^ (x >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  return z ^^^ (z >>> 31)

/-- Uniform in `[0, n)`; `0` when `n = 0`. -/
def rand (n : Nat) : Gen Nat := do
  if n == 0 then return 0
  return ((← nextWord).toNat % n)

def chance (percent : Nat) : Gen Bool := do return (← rand 100) < percent

def pick [Inhabited α] (xs : List α) : Gen α := do
  return xs[← rand xs.length]!

/-- Weighted choice among the alternatives with positive weight. -/
def weighted [Inhabited α] (alternatives : List (Nat × Gen α)) : Gen α := do
  let live := alternatives.filter (·.1 > 0)
  let total := live.foldl (· + ·.1) 0
  let mut point ← rand total
  for (weight, action) in live do
    if point < weight then return ← action
    point := point - weight
  match live.head? with
  | some (_, action) => action
  | none => return default

/-! ## Shapes and types -/

inductive Shape where
  | int
  | bytes
  | any
  | list (element : Shape)
  | map (key value : Shape)
  | constr (alternatives : List (List Shape))
  deriving Repr, BEq, Inhabited

inductive Ty where
  | int
  | bool
  | bytes
  | unit
  | data (shape : Shape)
  | list (shape : Shape)
  | pairs (key value : Shape)
  | pair (key value : Shape)
  | tuple (first second : Ty)
  | opt (value : Ty)
  | fn (argument result : Ty)
  deriving Repr, BEq, Inhabited

abbrev Env := List (VarId × Ty)

instance : Inhabited BuiltinFun := ⟨.AddInteger⟩

def fresh (hint : String) : Gen VarId := do
  let s ← get
  set { s with next := s.next + 1 }
  return { uid := s.next, origin := .source, hint }

/-- A binder, occasionally shadowing a variable already in scope. -/
def binder (env : Env) (hint : String) : Gen VarId := do
  if !env.isEmpty && (← chance 4) then
    let (old, _) ← pick env
    return old
  fresh hint

def extend (env : Env) (name : VarId) (ty : Ty) : Env :=
  (name, ty) :: env.filter (fun (other, _) => !(other == name))

partial def genShape (depth : Nat) : Gen Shape := do
  if depth == 0 then
    return ← pick [Shape.int, .int, .bytes, .any]
  weighted [
    (4, pure .int), (2, pure .bytes), (1, pure .any),
    (2, do return .list (← genShape (depth - 1))),
    (1, do return .map (← pick [Shape.int, .bytes]) (← genShape (depth - 1))),
    (4, do
      let count ← weighted [(6, do return 1 + (← rand 3)), (2, do return 4 + (← rand 6))]
      let alternatives ← (List.range count).mapM fun _ => do
        let fields ← rand 4
        (List.range fields).mapM fun _ => genShape (depth - 1)
      return .constr alternatives)]

/-! ## Data instances -/

def smallInts : List Int := [0, 1, 2, 3, -1, 5, 7, 10, 42, -7, 100, 1000000, 2 ^ 70, -(2 ^ 64)]

def genInt : Gen Int := do
  weighted [(5, do return Int.ofNat (← rand 6)), (3, pick smallInts),
            (1, do return Int.ofNat (← rand 300) - 150)]

def genBytes : Gen ByteArray := do
  let length ← pick [0, 1, 1, 2, 3, 4, 28, 32]
  let palette ← pick [[0], [0, 1], [0xaa, 0xbb, 1, 2], [7]]
  let bytes ← (List.range length).mapM fun _ => do return (← pick palette).toUInt8
  return ⟨bytes.toArray⟩

partial def genAnyData (depth : Nat) : Gen Data := do
  if depth == 0 then
    weighted [(2, do return .I (← genInt)), (1, do return .B (← genBytes))]
  else
    weighted [
      (2, do return .I (← genInt)), (1, do return .B (← genBytes)),
      (1, do return .List (← (List.range (← rand 3)).mapM fun _ => genAnyData (depth - 1))),
      (1, do return .Map (← (List.range (← rand 3)).mapM fun _ => do
        return (← genAnyData 0, ← genAnyData (depth - 1)))),
      (2, do
        return .Constr (Int.ofNat (← rand 4))
          (← (List.range (← rand 3)).mapM fun _ => genAnyData (depth - 1)))]

def keyPool (shape : Shape) : Gen Data := do
  match shape with
  | .bytes => return .B ⟨#[(← pick [0xaa, 0xbb, 0x01]).toUInt8]⟩
  | _ => return .I (Int.ofNat (← rand 4))

partial def genData (shape : Shape) : Gen Data := do
  match shape with
  | .int => return .I (← genInt)
  | .bytes => return .B (← genBytes)
  | .any => genAnyData 2
  | .list element =>
    let count ← weighted [(2, pure 0), (5, do return 1 + (← rand 3)), (1, do return 4 + (← rand 4))]
    return .List (← (List.range count).mapM fun _ => genData element)
  | .map key value =>
    let count ← weighted [(1, pure 0), (4, do return 1 + (← rand 4))]
    return .Map (← (List.range count).mapM fun _ => do return (← keyPool key, ← genData value))
  | .constr alternatives =>
    let tag ← rand alternatives.length
    let fields := alternatives[tag]!
    return .Constr (Int.ofNat tag) (← fields.mapM genData)

/-- A value that breaks the shape somewhere: a different kind, a tag out of
    range, a missing or extra field, a mutated nested value. -/
partial def mutateData (shape : Shape) (value : Data) : Gen Data := do
  let wrongKind : Gen Data := do
    pick [Data.I 7, .B ⟨#[1, 2]⟩, .Constr 0 [], .List [], .Map []]
  match shape, value with
  | .constr alternatives, .Constr tag fields =>
    weighted [
      (2, wrongKind),
      (2, do return .Constr (Int.ofNat alternatives.length + Int.ofNat (← rand 2)) fields),
      (2, do return .Constr tag (fields.dropLast)),
      (1, do return .Constr tag (fields ++ [.I 0])),
      (3, do
        if fields.isEmpty then wrongKind else
        let index ← rand fields.length
        let fieldShapes := alternatives[tag.toNat]!
        let mutated ← mutateData (fieldShapes[index]!) fields[index]!
        return .Constr tag (fields.set index mutated))]
  | .list element, .List items =>
    weighted [
      (2, wrongKind),
      (2, do return .List (items ++ [.B ⟨#[5]⟩])),
      (3, do
        if items.isEmpty then return .List [.Constr 9 []] else
        let index ← rand items.length
        return .List (items.set index (← mutateData element items[index]!)))]
  | .map key valueShape, .Map entries =>
    weighted [
      (2, wrongKind),
      (2, do return .Map (entries ++ [(.Constr 0 [], .I 1)])),
      (3, do
        if entries.isEmpty then return .Map [(← keyPool key, .Constr 9 [])] else
        let index ← rand entries.length
        let (k, v) := entries[index]!
        return .Map (entries.set index (k, ← mutateData valueShape v)))]
  | _, _ => wrongKind

/-! ## Expression helpers (translator idioms) -/

def lit (c : Const) (ty : BuiltinType) : Expr := .Lit (c, ty)
def intE (value : Int) : Expr := lit (.Integer value) (.AtomicType .TypeInteger)
def boolE (value : Bool) : Expr := lit (.Bool value) (.AtomicType .TypeBool)
def unitE : Expr := lit .Unit (.AtomicType .TypeUnit)
def bytesE (value : ByteArray) : Expr := lit (.ByteString value) (.AtomicType .TypeByteString)
def dataE (value : Data) : Expr := lit (.Data value) (.AtomicType .TypeData)
def stringE (value : String) : Expr := lit (.String value) (.AtomicType .TypeString)
def dataListType : BuiltinType := .TypeOperator (.TypeList (.AtomicType .TypeData))
def dataListE (values : List Data) : Expr := lit (.ConstDataList values) dataListType

def app1 (b : BuiltinFun) (x : Expr) : Expr := .App (.Builtin b) x
def app2 (b : BuiltinFun) (x y : Expr) : Expr := .App (.App (.Builtin b) x) y
def force1 (b : BuiltinFun) (x : Expr) : Expr := .App (.Force (.Builtin b)) x
def force2 (b : BuiltinFun) (x : Expr) : Expr := .App (.Force (.Force (.Builtin b))) x
def headE (x : Expr) : Expr := force1 .HeadList x
def tailE (x : Expr) : Expr := force1 .TailList x
def nullE (x : Expr) : Expr := force1 .NullList x
def fstE (x : Expr) : Expr := force2 .FstPair x
def sndE (x : Expr) : Expr := force2 .SndPair x
def consE (x xs : Expr) : Expr := .App (force1 .MkCons x) xs
def traceE (message : String) (body : Expr) : Expr :=
  .App (.App (.Force (.Builtin .Trace)) (stringE message)) body

/-- `traceE` when the program may trace, the body alone otherwise. -/
def maybeTrace (message : String) (body : Expr) : Gen Expr := do
  return if (← get).traces then traceE message body else body

/-- `if c then a else b` as the translator writes it. -/
def iteDelay (c a b : Expr) : Expr :=
  .Force (.App (.App (.App (.Force (.Builtin .IfThenElse)) c) (.Delay a)) (.Delay b))
/-- `if c then a else b` as a Boolean case. -/
def iteCase (c a b : Expr) : Expr := .Case c [b, a]
/-- Strict `ifThenElse`: both branches are evaluated. -/
def iteStrict (c a b : Expr) : Expr :=
  .App (.App (.App (.Force (.Builtin .IfThenElse)) c) a) b

def lets (bindings : List (VarId × Expr)) (body : Expr) : Expr :=
  if bindings.isEmpty then body else .Let (bindings.map fun (v, e) => (v, e, false)) body

def apps (f : Expr) (args : List Expr) : Expr := args.foldl .App f

/-- Decode a Data value of a shape into the type the program works with. -/
def decodeTy : Shape → Ty
  | .int => .int
  | .bytes => .bytes
  | .list element => .list element
  | .map key value => .pairs key value
  | shape => .data shape

def decodeE : Shape → Expr → Expr
  | .int, e => app1 .UnIData e
  | .bytes, e => app1 .UnBData e
  | .list _, e => app1 .UnListData e
  | .map _ _, e => app1 .UnMapData e
  | _, e => e

def encodeE : Shape → Expr → Expr
  | .int, e => app1 .IData e
  | .bytes, e => app1 .BData e
  | .list _, e => app1 .ListData e
  | .map _ _, e => app1 .MapData e
  | _, e => e

/-! ## Typed expression generator -/

def varsOf (env : Env) (ty : Ty) : List VarId :=
  env.filterMap fun (v, t) => if t == ty then some v else none

def dataVars (env : Env) : List (VarId × Shape) :=
  env.filterMap fun (v, t) => match t with | .data s => some (v, s) | _ => none

def listVars (env : Env) : List (VarId × Shape) :=
  env.filterMap fun (v, t) => match t with | .list s => some (v, s) | _ => none

def pairsVars (env : Env) : List (VarId × Shape × Shape) :=
  env.filterMap fun (v, t) => match t with | .pairs k s => some (v, k, s) | _ => none

def fnVars (env : Env) (result : Ty) : List (VarId × Ty) :=
  env.filterMap fun (v, t) => match t with
    | .fn a r => if r == result then some (v, a) else none
    | _ => none

def simpleTy : Gen Ty := do
  weighted [(4, pure .int), (3, pure .bool), (1, pure .bytes),
            (1, pure (.data .any)), (1, pure (.list .int)), (1, pure (.tuple .int .bool)),
            (1, pure (.opt .int))]

def messages : List String := ["a", "b", "check", "loop", "field"]

mutual

/-- A small closed or env-based expression of a type. -/
partial def leaf (ty : Ty) (env : Env) : Gen Expr := do
  let vars := varsOf env ty
  if !vars.isEmpty && (← chance 70) then
    return .Var (← pick vars)
  match ty with
  | .int => return intE (← genInt)
  | .bool => return boolE (← chance 50)
  | .bytes => return bytesE (← genBytes)
  | .unit => return unitE
  | .data shape => return dataE (← genData shape)
  | .list shape => return dataListE (← (List.range (← rand 3)).mapM fun _ => genData shape)
  | .pairs key value =>
    let entries ← (List.range (← rand 3)).mapM fun _ => do return (← keyPool key, ← genData value)
    return lit (.ConstPairDataList entries) (.TypeOperator (.TypeList
      (.TypeOperator (.TypePair (.AtomicType .TypeData) (.AtomicType .TypeData)))))
  | .pair key value =>
    return lit (.PairData (← keyPool key, ← genData value))
      (.TypeOperator (.TypePair (.AtomicType .TypeData) (.AtomicType .TypeData)))
  | .tuple a b => return .Constr 0 [← leaf a env, ← leaf b env]
  | .opt a => if ← chance 40 then return .Constr 0 [] else return .Constr 1 [← leaf a env]
  | .fn a r =>
    if a == .int && r == .int && (← chance 40) then
      return .App (.Builtin (← pick [.AddInteger, .MultiplyInteger, .SubtractInteger])) (intE (← genInt))
    let x ← binder env "x"
    return .Lam x (← leaf r (extend env x a))

/-- An expression of type `ty`. -/
partial def gen (ty : Ty) (depth : Nat) (env : Env) : Gen Expr := do
  if depth == 0 then return ← leaf ty env
  let d := depth - 1
  let hasData := !(dataVars env).isEmpty
  let hasList := !(listVars env).isEmpty
  let hasPairs := !(pairsVars env).isEmpty
  let hasFn := !(fnVars env ty).isEmpty
  let hasProjection := env.any fun (_, t) => match t with
    | .tuple a b => a == ty || b == ty
    | _ => false
  let confused := (← get).confused
  weighted [
    (if confused then 1 else 0, do gen (← simpleTy) d env),
    (2, leaf ty env),
    (5, typed ty d env),
    (2, letShare ty d env),
    (2, branchIte ty d env),
    (1, do maybeTrace (← pick messages) (← gen ty d env)),
    (1, guardError ty d env),
    (if hasData then 8 else 0, decodeData ty d env),
    (if hasData then 2 else 0, decodeTwo ty d env),
    (if ty == .unit || ty == .bool then 4 else 1, checks ty d env),
    (if hasList then 6 else 0, listFold ty d env),
    (if hasPairs then 4 else 0, mapLookup ty d env),
    (if hasFn then 2 else 0, call ty d env),
    (if hasProjection then 3 else 0, project ty env),
    (1, recordShare ty d env),
    (1, helper ty d env),
    (1, tupleCase ty d env),
    (1, optCase ty d env),
    (if hasData then 1 else 0, recordGetter ty d env),
    (1, counterLoop ty d env)]

/-- Operations producing a specific type. -/
partial def typed (ty : Ty) (d : Nat) (env : Env) : Gen Expr := do
  match ty with
  | .int => weighted [
      (4, do
        return app2 (← pick [.AddInteger, .SubtractInteger, .MultiplyInteger])
          (← gen .int d env) (← gen .int d env)),
      (1, do
        return app2 (← pick [.DivideInteger, .ModInteger, .QuotientInteger, .RemainderInteger])
          (← gen .int d env) (← gen .int d env)),
      (2, do return app1 .UnIData (← gen (.data (← pick [.int, .int, .any])) d env)),
      (1, do return app1 .LengthOfByteString (← gen .bytes d env)),
      (1, do return fstE (app1 .UnConstrData (← gen (.data .any) d env)))]
  | .bool => weighted [
      (4, do
        return app2 (← pick [.EqualsInteger, .LessThanInteger, .LessThanEqualsInteger])
          (← gen .int d env) (← gen .int d env)),
      (1, do return app2 .EqualsByteString (← gen .bytes d env) (← gen .bytes d env)),
      (2, do
        let shape ← match dataVars env with
          | [] => pure Shape.int
          | vars => (·.2) <$> pick vars
        return app2 .EqualsData (← gen (.data shape) d env) (← gen (.data shape) d env)),
      (2, do return nullE (← gen (.list (← pick [.int, .any])) d env)),
      (1, do let b ← gen .bool d env; return .Case b [boolE true, boolE false]),
      (1, do return iteDelay (← gen .bool d env) (← gen .bool d env) (boolE false)),
      (1, do return iteDelay (← gen .bool d env) (boolE true) (← gen .bool d env))]
  | .bytes => weighted [
      (2, do return app2 .AppendByteString (← gen .bytes d env) (← gen .bytes d env)),
      (2, do return app1 .UnBData (← gen (.data (← pick [.bytes, .any])) d env))]
  | .unit => weighted [
      (3, do return iteDelay (← gen .bool d env) unitE .Error),
      (1, do return iteDelay (← gen .bool d env) unitE (← maybeTrace "rejected" .Error)),
      (1, do return .Force (.App (.App (.Force (.Builtin .ChooseUnit)) unitE) (.Delay (← gen .unit d env))))]
  | .data shape => weighted [
      (2, do return encodeE shape (← gen (decodeTy shape) d env)),
      (2, do return headE (← gen (.list shape) d env)),
      (1, do
        match shape with
        | .constr alternatives =>
          let tag ← rand alternatives.length
          let fields ← (alternatives[tag]!).mapM fun s => gen (.data s) d env
          let list := fields.foldr consE (app1 .MkNilData unitE)
          return app2 .ConstrData (intE (Int.ofNat tag)) list
        | _ => leaf ty env),
      (1, do return sndE (headE (app1 .UnMapData (← gen (.data (.map .int shape)) d env)))),
      (1, do
        -- a kind guard: chooseData selects True for exactly one kind
        let x ← gen ty d env
        let v ← fresh "checked"
        let kind ← rand 5
        let flags := (List.range 5).map fun k => boolE (k == kind)
        let guard := apps (.Force (.Builtin .ChooseData)) (.Var v :: flags)
        return lets [(v, x)] (iteDelay guard (.Var v) .Error))]
  | .list shape => weighted [
      (2, do return app1 .UnListData (← gen (.data (.list shape)) d env)),
      (2, do return tailE (← gen (.list shape) d env)),
      (2, do return consE (← gen (.data shape) d env) (← gen (.list shape) d env)),
      (1, do return app1 .MkNilData unitE)]
  | .pairs key value => weighted [
      (2, do return app1 .UnMapData (← gen (.data (.map key value)) d env)),
      (1, do return tailE (← gen (.pairs key value) d env))]
  | .pair key value => do return headE (← gen (.pairs key value) d env)
  | .tuple a b => do return .Constr 0 [← gen a d env, ← gen b d env]
  | .opt a => weighted [(1, pure (.Constr 0 [])), (2, do return .Constr 1 [← gen a d env])]
  | .fn a r =>
    let x ← binder env "x"
    return .Lam x (← gen r d (extend env x a))

/-- `let x = e in body`, with `x` usable (possibly several times) in `body`. -/
partial def letShare (ty : Ty) (d : Nat) (env : Env) : Gen Expr := do
  let count ← weighted [(3, pure 1), (1, pure 2), (1, pure 3)]
  let mut bindings : List (VarId × Expr) := []
  let mut scope := env
  for _ in List.range count do
    let t ← simpleTy
    let rhs ← gen t d scope
    let x ← binder scope "v"
    bindings := bindings ++ [(x, rhs)]
    scope := extend scope x t
  return lets bindings (← gen ty d scope)

partial def branchIte (ty : Ty) (d : Nat) (env : Env) : Gen Expr := do
  let c ← gen .bool d env
  let a ← gen ty d env
  let b ← gen ty d env
  weighted [(4, pure (iteDelay c a b)), (4, pure (iteCase c a b)), (1, pure (iteStrict c a b))]

/-- A condition that must hold, as validators write it. -/
partial def guardError (ty : Ty) (d : Nat) (env : Env) : Gen Expr := do
  let c ← gen .bool d env
  let body ← gen ty d env
  weighted [
    (3, pure (iteDelay c body .Error)),
    (2, do return iteCase c body (← maybeTrace "guard" .Error)),
    (1, pure (.Case c [.Error, body])),
    (1, do return lets [(← fresh "check", iteDelay c unitE .Error)] body)]

/-- Decode a prefix of the fields of a constructor (the list `fields`), then
    continue with them in scope. -/
partial def fieldBranch (fields : VarId) (fieldShapes : List Shape) (env : Env)
    (continuation : Env → Gen Expr) : Gen Expr := do
  let mut bindings : List (VarId × Expr) := []
  let mut scope := env
  let mut rest : Expr := .Var fields
  let used ← rand (fieldShapes.length + 1)
  for (shape, position) in (fieldShapes.take (max used 1)).zipIdx do
    let a ← fresh s!"f{position}"
    bindings := bindings ++ [(a, decodeE shape (headE rest))]
    scope := extend scope a (decodeTy shape)
    if position + 1 < fieldShapes.length then
      let r ← fresh s!"rest{position}"
      bindings := bindings ++ [(r, tailE rest)]
      rest := .Var r
  if fieldShapes.isEmpty then bindings := []
  return lets bindings (← continuation scope)

/-- Decode two constructor values up front, as a validator decodes its datum
    and redeemer, then dispatch on both tags; some tag combinations fail. -/
partial def decodeTwo (ty : Ty) (d : Nat) (env : Env) : Gen Expr := do
  let constrs := (dataVars env).filterMap fun (v, s) => match s with
    | .constr alternatives => some (v, alternatives)
    | _ => none
  match constrs with
  | (v1, alts1) :: (v2, alts2) :: _ =>
    let p1 ← fresh "pair"; let t1 ← fresh "tag"; let f1 ← fresh "fields"
    let p2 ← fresh "pair"; let t2 ← fresh "tag"; let f2 ← fresh "fields"
    let (v1, alts1, v2, alts2) ← if ← chance 50 then pure (v1, alts1, v2, alts2)
      else pure (v2, alts2, v1, alts1)
    let inner (i : Nat) : Gen Expr := do
      let outer ← (List.range alts2.length).foldrM (fun j otherwise => do
        let leafB ← weighted [(2, pure Expr.Error),
          (3, fieldBranch f1 (alts1[i]!) env fun scope => fieldBranch f2 (alts2[j]!) scope (gen ty d))]
        return iteCase (app2 .EqualsInteger (.Var t2) (intE (Int.ofNat j))) leafB otherwise) Expr.Error
      return outer
    let chain ← (List.range alts1.length).foldrM (fun i otherwise => do
      return iteCase (app2 .EqualsInteger (.Var t1) (intE (Int.ofNat i))) (← inner i) otherwise) Expr.Error
    let early ← chance 50
    let decode1 := [(p1, app1 .UnConstrData (.Var v1)), (t1, fstE (.Var p1)), (f1, sndE (.Var p1))]
    let decode2 := [(p2, app1 .UnConstrData (.Var v2)), (t2, fstE (.Var p2)), (f2, sndE (.Var p2))]
    if early then return lets (decode1 ++ decode2) chain
    -- the second decode after some unrelated work
    let w ← fresh "work"
    let work ← gen (← simpleTy) d env
    return lets (decode1 ++ [(w, work)] ++ decode2) chain
  | _ => decodeData ty d env

/-- Validator-style checks: some bindings, then a conjunction of conditions
    that mention only some of them, asserted with `if … then () else error`. -/
partial def checks (ty : Ty) (d : Nat) (env : Env) : Gen Expr := do
  let count ← weighted [(2, pure 1), (2, pure 2), (1, pure 3)]
  let mut bindings : List (VarId × Expr) := []
  let mut scope := env
  for _ in List.range count do
    let t ← weighted [(3, pure Ty.int), (2, pure .bool), (1, pure (.list .int)), (1, pure (.data .any))]
    let rhs ← gen t d scope
    let x ← fresh "w"
    bindings := bindings ++ [(x, rhs)]
    scope := extend scope x t
  -- conditions that do not need the bindings let fail-fast move them
  let conditionScope ← weighted [(1, pure scope), (1, pure env)]
  let conditions ← (List.range (1 + (← rand 3))).mapM fun _ => gen .bool d conditionScope
  let conjunction := conditions.foldr (fun c rest => iteDelay c rest (boolE false)) (boolE true)
  let final ← if ty == .unit && (← chance 60) then pure unitE else gen ty d scope
  let body ← weighted [
    (3, pure (iteDelay conjunction final .Error)),
    (2, pure (conditions.foldr (fun c rest => iteDelay c rest .Error) final)),
    (1, pure (iteCase conjunction final .Error))]
  return lets bindings body

/-- Decode a Data variable by its shape, then continue with the parts in scope. -/
partial def decodeData (ty : Ty) (d : Nat) (env : Env) : Gen Expr := do
  let (v, shape) ← pick (dataVars env)
  match shape with
  | .constr alternatives =>
    let pair ← fresh "pair"
    let tag ← fresh "tag"
    let fields ← fresh "fields"
    let branch (index : Nat) : Gen Expr :=
      fieldBranch fields (alternatives[index]!) env (gen ty d)
    let order ← weighted [(3, pure (List.range alternatives.length)),
      (1, do return (List.range alternatives.length).reverse),
      (1, do return (List.range alternatives.length).take (1 + (← rand alternatives.length)))]
    let default ← weighted [(3, pure Expr.Error), (1, gen ty d env), (1, maybeTrace "no match" .Error)]
    let style ← rand 4
    let chain ← order.foldrM (fun index otherwise => do
      let matched ← branch index
      let test := app2 .EqualsInteger (.Var tag) (intE (Int.ofNat index))
      return if style == 0 then iteDelay test matched otherwise else iteCase test matched otherwise)
      default
    let chain ← if alternatives.length == 1 && (← chance 50) then
        -- a single constructor: an unchecked or an explicitly checked decode
        if ← chance 50 then branch 0
        else pure (iteCase (app2 .EqualsInteger (.Var tag) (intE 0)) (← branch 0) .Error)
      else pure chain
    return lets [(pair, app1 .UnConstrData (.Var v)), (tag, fstE (.Var pair)),
      (fields, sndE (.Var pair))] chain
  | .int =>
    let n ← fresh "n"
    if ← chance 40 then
      -- an integer used as a tag
      let cases ← (List.range (1 + (← rand 4))).mapM fun k => do return (Int.ofNat k, ← gen ty d env)
      let default ← weighted [(1, pure Expr.Error), (1, gen ty d env)]
      let chain := cases.foldr (fun (k, branch) otherwise =>
        iteCase (app2 .EqualsInteger (.Var n) (intE k)) branch otherwise) default
      return lets [(n, app1 .UnIData (.Var v))] chain
    return lets [(n, app1 .UnIData (.Var v))] (← gen ty d (extend env n .int))
  | .bytes =>
    let b ← fresh "b"
    return lets [(b, app1 .UnBData (.Var v))] (← gen ty d (extend env b .bytes))
  | .list element =>
    let l ← fresh "items"
    return lets [(l, app1 .UnListData (.Var v))] (← gen ty d (extend env l (.list element)))
  | .map key value =>
    let m ← fresh "entries"
    return lets [(m, app1 .UnMapData (.Var v))] (← gen ty d (extend env m (.pairs key value)))
  | .any =>
    -- chooseData on the kind of the value
    let constrB ← gen ty d env
    let mapB ← gen ty d env
    let listB ← gen ty d env
    let n ← fresh "n"
    let intB ← gen ty d (extend env n .int)
    let bytesB ← gen ty d env
    let intB := lets [(n, app1 .UnIData (.Var v))] intB
    return .Force (apps (.Force (.Builtin .ChooseData)) [.Var v, .Delay constrB, .Delay mapB,
      .Delay listB, .Delay intB, .Delay bytesB])

/-- Match a list as the translator does: `chooseList` with head and tail
    passed to a lambda, or a `nullList` Boolean case. -/
partial def listMatch (scrutinee : Expr) (nilBranch : Expr) (head tail : VarId)
    (consBranch : Expr) : Gen Expr := do
  let ls ← fresh "ls"
  weighted [
    (3, pure (lets [(ls, scrutinee)] (.Force (apps (.Force (.Force (.Builtin .ChooseList)))
      [.Var ls, .Delay nilBranch,
       .Delay (apps (.Lam head (.Lam tail consBranch)) [headE (.Var ls), tailE (.Var ls)])])))),
    (2, pure (lets [(ls, scrutinee)] (.Case (nullE (.Var ls))
      [lets [(head, headE (.Var ls)), (tail, tailE (.Var ls))] consBranch, nilBranch]))),
    (1, pure (.Force (apps (.Force (.Force (.Builtin .ChooseList)))
      [scrutinee, .Delay nilBranch,
       .Delay (lets [(head, headE scrutinee), (tail, tailE scrutinee)] consBranch)])))]

/-- Recursion over a builtin list of Data. -/
partial def listFold (ty : Ty) (d : Nat) (env : Env) : Gen Expr := do
  let (l, shape) ← pick (listVars env)
  let go ← fresh "go"
  let xs ← fresh "xs"
  let h ← fresh "h"
  let t ← fresh "t"
  let elemTy := Ty.data shape
  let extra ← chance 35
  let k ← fresh "k"
  let kTy ← simpleTy
  let kArg ← if extra then gen kTy d env else pure unitE
  let withK (body : Expr) : Expr := if extra then .Lam k body else body
  let callK (f : Expr) : Expr := if extra then .App f (.Var k) else f
  let applyK (f : Expr) : Expr := if extra then .App f kArg else f
  let scope0 := if extra then extend env k kTy else env
  let flavor ← weighted [
    (3, pure 0),
    (3, pure 1),
    (if ty == .bool then 3 else 0, pure 2),
    (if (match ty with | .list _ => true | _ => false) then 3 else 0, pure 3),
    (if ty == .int then 2 else 0, pure 4),
    (if (match ty with | .opt (.data _) => true | _ => false) then 2 else 0, pure 5)]
  match flavor with
  | 0 =>
    -- tail recursion with an accumulator
    let acc ← fresh "acc"
    let scope := extend (extend (extend scope0 acc ty) h elemTy) t (.list shape)
    let step ← gen ty d scope
    let consB := apps (callK (.Var go)) [step, .Var t]
    let body ← listMatch (.Var xs) (.Var acc) h t consB
    let init ← gen ty d env
    return apps (applyK (.Fix go (withK (.Lam acc (.Lam xs body))))) [init, .Var l]
  | 1 =>
    -- right fold: combine the head with the recursive result
    let r ← fresh "r"
    let scope := extend (extend (extend scope0 h elemTy) t (.list shape)) r ty
    let combine ← gen ty d scope
    let recursive := .App (callK (.Var go)) (.Var t)
    let consB ← weighted [(2, pure (lets [(r, recursive)] combine)),
      (1, pure (.App (.Lam r combine) recursive))]
    let base ← gen ty d scope0
    let body ← listMatch (.Var xs) base h t consB
    return .App (applyK (.Fix go (withK (.Lam xs body)))) (.Var l)
  | 2 =>
    -- any / all with short-circuit
    let scope := extend (extend scope0 h elemTy) t (.list shape)
    let test ← gen .bool d scope
    let recursive := .App (callK (.Var go)) (.Var t)
    let isAny ← chance 50
    let consB ← if isAny then
        pick [iteDelay test (boolE true) recursive, iteCase test (boolE true) recursive]
      else pick [iteDelay test recursive (boolE false), iteCase test recursive (boolE false)]
    let body ← listMatch (.Var xs) (boolE !isAny) h t consB
    return .App (applyK (.Fix go (withK (.Lam xs body)))) (.Var l)
  | 3 =>
    -- map / filter
    let outShape := match ty with | .list s => s | _ => .any
    let scope := extend (extend scope0 h elemTy) t (.list shape)
    let recursive := .App (callK (.Var go)) (.Var t)
    let consB ← if (outShape == shape) && (← chance 50) then do
        let test ← gen .bool d scope
        pure (iteDelay test (consE (.Var h) recursive) recursive)
      else do
        let mapped ← gen (.data outShape) d scope
        pure (consE mapped recursive)
    let body ← listMatch (.Var xs) (app1 .MkNilData unitE) h t consB
    return .App (applyK (.Fix go (withK (.Lam xs body)))) (.Var l)
  | 4 =>
    -- length / count
    let scope := extend (extend scope0 h elemTy) t (.list shape)
    let recursive := .App (callK (.Var go)) (.Var t)
    let consB ← if ← chance 50 then pure (app2 .AddInteger (intE 1) recursive)
      else do
        let test ← gen .bool d scope
        pure (iteCase test (app2 .AddInteger (intE 1) recursive) recursive)
    let body ← listMatch (.Var xs) (intE 0) h t consB
    return .App (applyK (.Fix go (withK (.Lam xs body)))) (.Var l)
  | _ =>
    -- find
    let scope := extend (extend scope0 h elemTy) t (.list shape)
    let test ← gen .bool d scope
    let recursive := .App (callK (.Var go)) (.Var t)
    let found := match ty with
      | .opt (.data s) => if s == shape then Expr.Var h else dataE (.I 0)
      | _ => dataE (.I 0)
    let consB := iteDelay test (.Constr 1 [found]) recursive
    let body ← listMatch (.Var xs) (.Constr 0 []) h t consB
    return .App (applyK (.Fix go (withK (.Lam xs body)))) (.Var l)

/-- Look a key up in a builtin list of Data pairs, comparing with `equalsData`
    (or bytes of `unBData` keys). -/
partial def mapLookup (ty : Ty) (d : Nat) (env : Env) : Gen Expr := do
  let (m, key, value) ← pick (pairsVars env)
  let go ← fresh "lookup"
  let ps ← fresh "ps"
  let h ← fresh "entry"
  let t ← fresh "more"
  let wanted ← gen (.data key) d env
  let w ← fresh "key"
  let found ← fresh "found"
  -- the key as a parameter of the loop (static argument) or captured
  let keyParam ← chance 35
  let kv ← fresh "k"
  let keyRef : Expr := if keyParam then .Var kv else .Var w
  let test ← if key == .bytes && (← chance 50) then
      pure (app2 .EqualsByteString (app1 .UnBData (fstE (.Var h))) (app1 .UnBData keyRef))
    else pure (app2 .EqualsData (fstE (.Var h)) keyRef)
  let missing ← weighted [(2, pure Expr.Error), (1, pure (.Constr 0 [])), (1, maybeTrace "missing" .Error)]
  let usesOpt := match missing with | .Constr _ _ => true | _ => false
  let hit := if usesOpt then Expr.Constr 1 [sndE (.Var h)] else sndE (.Var h)
  let recurse : Expr := if keyParam then apps (.Var go) [.Var kv, .Var t] else .App (.Var go) (.Var t)
  let consB ← pick [iteDelay test hit recurse, iteCase test hit recurse]
  let body ← listMatch (.Var ps) missing h t consB
  let function := if keyParam then Expr.Fix go (.Lam kv (.Lam ps body)) else .Fix go (.Lam ps body)
  let call (f : Expr) : Expr := if keyParam then apps f [.Var w, .Var m] else .App f (.Var m)
  let letBound ← chance 35
  let lf ← fresh "lookupFn"
  let lookup := if letBound then lets [(lf, function)] (call (.Var lf)) else call function
  -- a dominating `unBData` of a bytes key, as decoded map keys have
  let keyBytes ← if key == .bytes && (← chance 60) then do
      let kb ← fresh "keyBytes"
      pure [(kb, app1 .UnBData (.Var w))]
    else pure []
  let wanted := wanted
  let scope := extend env found (.data value)
  if usesOpt then
    let x ← fresh "x"
    let someB ← gen ty d (extend env x (.data value))
    let noneB ← gen ty d env
    return lets ([(w, wanted)] ++ keyBytes) (.Case lookup [noneB, .Lam x someB])
  return lets ([(w, wanted)] ++ keyBytes ++ [(found, lookup)]) (← gen ty d scope)

/-- A field read `case r [λa b. a]` of a tuple variable. -/
partial def project (ty : Ty) (env : Env) : Gen Expr := do
  let candidates := env.filterMap fun (v, t) => match t with
    | .tuple a b => if a == ty then some (v, 0, a, b) else if b == ty then some (v, 1, a, b) else none
    | _ => none
  let (r, index, _, _) ← pick candidates
  let x ← fresh "fa"
  let y ← fresh "fb"
  return .Case (.Var r) [.Lam x (.Lam y (.Var (if index == 0 then x else y)))]

partial def call (ty : Ty) (d : Nat) (env : Env) : Gen Expr := do
  let (f, argTy) ← pick (fnVars env ty)
  return .App (.Var f) (← gen argTy d env)

/-- A let-bound helper function, used once or several times, or passed on. -/
partial def helper (ty : Ty) (d : Nat) (env : Env) : Gen Expr := do
  let argTy ← simpleTy
  let resTy ← weighted [(2, pure ty), (2, simpleTy)]
  let f ← fresh "helper"
  let x ← binder env "arg"
  let body ← gen resTy d (extend env x argTy)
  let twoArgs ← chance 30
  let y ← fresh "arg2"
  let fnExpr := if twoArgs then .Lam x (.Lam y body) else .Lam x body
  let fTy := if twoArgs then Ty.fn argTy (.fn .int resTy) else .fn argTy resTy
  let scope := extend env f fTy
  -- partial applications of a two-argument helper are in scope too
  let scope ← if twoArgs then do
      let p ← fresh "partial"
      let partialArg ← gen argTy d env
      pure (extend scope p (.fn .int resTy), some (p, partialArg))
    else pure (scope, none)
  let (scope, partialBinding) := scope
  let rest ← gen ty d scope
  let bindings := [(f, fnExpr)] ++ match partialBinding with
    | some (p, argument) => [(p, .App (.Var f) argument)]
    | none => []
  return lets bindings rest

/-- A record bound once and read several times. -/
partial def recordShare (ty : Ty) (d : Nat) (env : Env) : Gen Expr := do
  let a ← simpleTy
  let b ← weighted [(1, pure ty), (2, simpleTy)]
  let r ← fresh "record"
  let value ← gen (.tuple a b) d env
  return lets [(r, value)] (← gen ty d (extend env r (.tuple a b)))

partial def tupleCase (ty : Ty) (d : Nat) (env : Env) : Gen Expr := do
  let a ← simpleTy
  let b ← simpleTy
  let scrutinee ← gen (.tuple a b) d env
  let x ← fresh "first"
  let y ← fresh "second"
  let body ← gen ty d (extend (extend env x a) y b)
  weighted [
    (3, pure (.Case scrutinee [.Lam x (.Lam y body)])),
    (1, do
      let p ← fresh "tuple"
      return lets [(p, scrutinee)] (.Case (.Var p) [.Lam x (.Lam y body)]))]

partial def optCase (ty : Ty) (d : Nat) (env : Env) : Gen Expr := do
  let a ← simpleTy
  let scrutinee ← gen (.opt a) d env
  let x ← fresh "some"
  let noneB ← gen ty d env
  let someB ← gen ty d (extend env x a)
  return .Case scrutinee [noneB, .Lam x someB]

/-- A record field getter `(λself. let pair = unConstrData self … in fK) item`. -/
partial def recordGetter (ty : Ty) (d : Nat) (env : Env) : Gen Expr := do
  let (v, shape) ← pick (dataVars env)
  let fieldShapes := match shape with
    | .constr alternatives => alternatives.headD []
    | _ => [Shape.int]
  if fieldShapes.isEmpty then return ← gen ty d env
  let index ← rand fieldShapes.length
  let self ← fresh "self"
  let pair ← fresh "pair"
  let fields ← fresh "fields"
  let mut bindings : List (VarId × Expr) := [(pair, app1 .UnConstrData (.Var self)),
    (fields, sndE (.Var pair))]
  let mut rest : Expr := .Var fields
  for position in List.range index do
    let r ← fresh s!"rest{position}"
    bindings := bindings ++ [(r, tailE rest)]
    rest := .Var r
  let out ← fresh s!"f{index}"
  let fieldShape := fieldShapes[index]!
  bindings := bindings ++ [(out, decodeE fieldShape (headE rest))]
  let getter := Expr.Lam self (lets bindings (.Var out))
  let value ← fresh "field"
  let shared ← chance 40
  let g ← fresh "getter"
  let scope := extend env value (decodeTy fieldShape)
  let body ← gen ty d scope
  if shared then
    return lets [(g, getter), (value, .App (.Var g) (.Var v))] body
  return lets [(value, .App getter (.Var v))] body

/-- Recursion on a non-negative counter derived from the inputs. -/
partial def counterLoop (ty : Ty) (d : Nat) (env : Env) : Gen Expr := do
  let go ← fresh "count"
  let n ← fresh "n"
  let acc ← fresh "acc"
  let limit ← gen .int d env
  let bounded := Expr.Case (app2 .LessThanInteger (intE 12) limit) [limit, intE 12]
  let init ← gen ty d env
  let step ← gen ty d (extend (extend env acc ty) n .int)
  let body := iteCase (app2 .LessThanEqualsInteger (.Var n) (intE 0)) (.Var acc)
    (apps (.Var go) [step, app2 .SubtractInteger (.Var n) (intE 1)])
  return apps (.Fix go (.Lam acc (.Lam n body))) [init, bounded]

end

/-! ## Programs -/

structure Param where
  var : VarId
  ty : Ty
  shape : Shape
  deriving Inhabited

structure Program where
  params : List Param
  result : Ty
  body : Expr

def Program.expr (program : Program) : Expr :=
  program.params.foldr (fun p body => .Lam p.var body) program.body

def genProgram (depth : Nat) : Gen Program := do
  let traces ← chance 40
  let confused ← chance 25
  modify fun s => { s with traces, confused }
  let count ← weighted [(3, pure 1), (3, pure 2), (1, pure 3)]
  let params ← (List.range count).mapM fun index => do
    let shape ← genShape 2
    let kind ← weighted [(8, pure 0), (1, pure 1), (1, pure 2)]
    let v ← fresh s!"p{index}"
    match kind with
    | 1 => return { var := v, ty := .int, shape := .int : Param }
    | 2 => return { var := v, ty := .list shape, shape := shape : Param }
    | _ => return { var := v, ty := .data shape, shape := shape : Param }
  let env : Env := params.reverse.map fun p => (p.var, p.ty)
  let result ← weighted [(4, pure Ty.int), (3, pure .bool), (3, pure .unit),
    (1, pure (.data .any)), (1, pure (.list .int)), (1, pure (.tuple .int .bool)),
    (1, pure (.opt .int)), (1, pure (.fn .int .int)), (1, pure .bytes)]
  -- decode the Data parameters first, as validators do
  let body ← if !(dataVars env).isEmpty && (← chance 75) then
      if ← chance 30 then decodeTwo result depth env else decodeData result depth env
    else gen result depth env
  return { params, result, body }

/-- A closing argument for a parameter: a valid instance of its shape, a
    mutation of one, or arbitrary Data. -/
def genArgument (p : Param) : Gen Expr := do
  match p.ty with
  | .int => return intE (← genInt)
  | .list shape =>
    let items ← (List.range (← rand 4)).mapM fun _ => genData shape
    if ← chance 15 then
      return dataListE (items ++ [← genAnyData 1])
    return dataListE items
  | _ =>
    let valid ← genData p.shape
    weighted [(7, pure (dataE valid)), (2, do return dataE (← mutateData p.shape valid)),
      (1, do return dataE (← genAnyData 2))]

/-- The arguments of one run: one per parameter, plus one for a function result. -/
def genArguments (program : Program) : Gen (List Expr) := do
  let base ← program.params.mapM genArgument
  match program.result with
  | .fn _ _ => return base ++ [intE (← genInt)]
  | _ => return base

partial def exprSize : Expr → Nat
  | .Lam _ body | .Fix _ body | .Force body | .Delay body => 1 + exprSize body
  | .App f x => 1 + exprSize f + exprSize x
  | .Let bindings body => 1 + exprSize body + bindings.foldl (fun n (_, e, _) => n + exprSize e) 0
  | .Constr _ fields => 1 + fields.foldl (fun n e => n + exprSize e) 0
  | .Case scrutinee alternatives =>
    1 + exprSize scrutinee + alternatives.foldl (fun n e => n + exprSize e) 0
  | _ => 1

/-- Programs larger than this many MIR nodes are regenerated. -/
def maximumSize : Nat := 700

def generate (seed : Nat) (depth : Nat) (inputs : Nat) : Program × List (List Expr) :=
  let action : Gen (Program × List (List Expr)) := do
    let mut program ← genProgram depth
    for attempt in List.range 8 do
      if exprSize program.expr <= maximumSize then break
      program ← genProgram (if attempt < 4 then depth else depth - 1)
    let arguments ← (List.range inputs).mapM fun _ => genArguments program
    return (program, arguments)
  (action.run { seed := seed.toUInt64 * 0x2545F4914F6CDD1D + 17 }).1

end Test.MIR.FuzzReal

/-! ## Mutants of existing programs

Local edits of a program that keep it well scoped: other integer, Boolean
and Data literals, swapped Boolean alternatives and `ifThenElse` branches,
other comparison builtins, an alternative or argument replaced by `error`,
an `error` replaced by unit. Mutants of the validators keep the shapes the
optimizer was written for while changing which paths halt. -/

namespace Test.MIR.FuzzReal.Mutate

open Moist.MIR
open Moist.Plutus.Term
open Test.MIR.FuzzReal

def comparisons : List BuiltinFun :=
  [.EqualsInteger, .LessThanInteger, .LessThanEqualsInteger]

/-- One edit of a node, if one applies to it. -/
def editNode (e : Expr) : Gen (Option Expr) := do
  match e with
  | .Lit (.Integer n, ty) =>
    return some (.Lit (.Integer (← pick [n + 1, n - 1, 0, -n, n * 2 + 1]), ty))
  | .Lit (.Bool b, ty) => return some (.Lit (.Bool !b, ty))
  | .Lit (.Data value, ty) =>
    match value with
    | .I n => return some (.Lit (.Data (.I (n + 1)), ty))
    | .B bytes => return some (.Lit (.Data (.B (bytes.push 0)), ty))
    | _ => return some (.Lit (.Data (.I 0), ty))
  | .Lit (.ByteString bytes, ty) =>
    return some (.Lit (.ByteString (if bytes.size > 0 && (← chance 50) then bytes.extract 1 bytes.size else bytes.push 1), ty))
  | .Case s [a, b] =>
    weighted [(3, pure (some (.Case s [b, a]))),
      (1, do return match a with | .Lam _ _ => none | _ => some (.Case s [.Error, b])),
      (1, do return match b with | .Lam _ _ => none | _ => some (.Case s [a, .Error]))]
  | .Force (.App (.App (.App (.Force (.Builtin .IfThenElse)) c) (.Delay a)) (.Delay b)) =>
    weighted [(3, pure (some (iteDelay c b a))), (1, pure (some (iteDelay c a .Error))),
      (1, pure (some (iteDelay c .Error b)))]
  | .App (.App (.Builtin builtin) x) y =>
    if comparisons.contains builtin then
      let other ← pick (comparisons.filter (· != builtin))
      weighted [(2, pure (some (.App (.App (.Builtin other) x) y))),
        (1, pure (some (.App (.App (.Builtin builtin) y) x)))]
    else return none
  | .Error => return some unitE
  | _ => return none

partial def countNodes : Expr → Nat
  | .Lam _ body | .Fix _ body | .Force body | .Delay body => 1 + countNodes body
  | .App f x => 1 + countNodes f + countNodes x
  | .Let bindings body => 1 + countNodes body + bindings.foldl (fun n (_, e, _) => n + countNodes e) 0
  | .Constr _ fields => 1 + fields.foldl (fun n e => n + countNodes e) 0
  | .Case scrutinee alternatives =>
    1 + countNodes scrutinee + alternatives.foldl (fun n e => n + countNodes e) 0
  | _ => 1

/-- Apply `f` at the `target`-th node in preorder. -/
partial def atNode (target : Nat) (f : Expr → Gen (Option Expr)) (e : Expr) :
    StateT Nat Gen (Option Expr) := do
  let index ← get
  set (index + 1)
  if index == target then return ← (f e : Gen (Option Expr))
  let rec list (es : List Expr) : StateT Nat Gen (Option (List Expr)) := do
    match es with
    | [] => return none
    | x :: rest =>
      match ← atNode target f x with
      | some x' => return some (x' :: rest)
      | none => return (← list rest).map (x :: ·)
  match e with
  | .Lam v body => return (← atNode target f body).map (.Lam v)
  | .Fix v body => return (← atNode target f body).map (.Fix v)
  | .Force body => return (← atNode target f body).map .Force
  | .Delay body => return (← atNode target f body).map .Delay
  | .App g x =>
    match ← atNode target f g with
    | some g' => return some (.App g' x)
    | none => return (← atNode target f x).map (.App g)
  | .Constr tag fields => return (← list fields).map (.Constr tag)
  | .Case s alts =>
    match ← atNode target f s with
    | some s' => return some (.Case s' alts)
    | none => return (← list alts).map (.Case s)
  | .Let bindings body =>
    let rec binds (bs : List (VarId × Expr × Bool)) : StateT Nat Gen (Option (List (VarId × Expr × Bool))) := do
      match bs with
      | [] => return none
      | (v, rhs, flag) :: rest =>
        match ← atNode target f rhs with
        | some rhs' => return some ((v, rhs', flag) :: rest)
        | none => return (← binds rest).map ((v, rhs, flag) :: ·)
    match ← binds bindings with
    | some bindings' => return some (.Let bindings' body)
    | none => return (← atNode target f body).map (.Let bindings)
  | _ => return none

/-- A mutant with `edits` edits (fewer when no edit applies after many tries). -/
def mutant (program : Expr) (edits : Nat) : Gen Expr := do
  let size := countNodes program
  let mut current := program
  for _ in List.range edits do
    for _ in List.range 50 do
      let target ← rand size
      match (← (atNode target editNode current).run' 0) with
      | some next =>
        current := next
        break
      | none => pure ()
  return current

end Test.MIR.FuzzReal.Mutate
