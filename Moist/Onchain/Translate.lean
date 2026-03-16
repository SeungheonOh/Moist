import Lean
import Moist.MIR.Expr
import Moist.MIR.Analysis
import Moist.Onchain.Builtins
import Moist.Onchain.Repr

namespace Moist.Onchain

open Lean Meta
open Moist.Plutus.Term (BuiltinFun Const BuiltinType AtomicType)

/-! # Lean Expr → MIR Translation

Translates Lean kernel expressions to MIR.
Type and proof arguments are detected and skipped during translation.
Constants are resolved via the builtin map or unfolded transitively.
-/

/-- Wrap a builtin in the required number of Force nodes. -/
private def mkBuiltin (b : BuiltinFun) : MIR.Expr :=
  Nat.repeat MIR.Expr.Force (builtinForceCount b) (.Builtin b)

/-- `Force (IfThenElse scrut (Delay trueAlt) (Delay falseAlt))` -/
private def mkBoolBranch (scrut trueAlt falseAlt : MIR.Expr) : MIR.Expr :=
  .Force (.App (.App (.App (mkBuiltin .IfThenElse) scrut)
    (.Delay trueAlt)) (.Delay falseAlt))

/-- UPLC has builtin representations for certain Lean inductives.
    When classified as a builtin type, constructors and eliminators
    bypass SOP/Data encoding and use UPLC builtins directly. -/
inductive BuiltinTypeKind | bool | unit | list | pair
  deriving BEq, DecidableEq

/-- Classify a Lean inductive as a UPLC builtin type, if applicable. -/
def builtinTypeKind (typeName : Name) : Option BuiltinTypeKind :=
  if typeName == ``Bool then some .bool
  else if typeName == ``Unit || typeName == ``PUnit then some .unit
  else if typeName == ``List then some .list
  else if typeName == ``Prod then some .pair
  -- PProd intentionally NOT a builtin pair: it wraps arbitrary types
  -- (used by brecOn) and needs SOP encoding (Constr/Case), not Data pairs.
  else none

/-- Map a Lean type expression to a UPLC BuiltinType (for constant typing). -/
private partial def leanTypeToBuiltinType (e : Lean.Expr) : MetaM (Option BuiltinType) := do
  match e with
  | .const n _ =>
    if n == ``Int || n == ``Moist.Plutus.Integer then
      return some (.AtomicType .TypeInteger)
    else if n == ``Bool then return some (.AtomicType .TypeBool)
    else if n == ``String then return some (.AtomicType .TypeString)
    else if n == ``Unit || n == ``PUnit then return some (.AtomicType .TypeUnit)
    else if n == ``Moist.Plutus.Data then return some (.AtomicType .TypeData)
    else if n == ``Moist.Plutus.ByteString || n == ``ByteArray then
      return some (.AtomicType .TypeByteString)
    else
      -- Try resolving abbreviations via whnf
      if !e.hasLooseBVars then
        let e' ← whnf e
        if e' != e then return ← leanTypeToBuiltinType e'
      return none
  | .app (.const ``List _) elemTy => do
    let some et ← leanTypeToBuiltinType elemTy | return none
    return some (.TypeOperator (.TypeList et))
  | .app (.app (.const ``Prod _) aTy) bTy => do
    let some a ← leanTypeToBuiltinType aTy | return none
    let some b ← leanTypeToBuiltinType bTy | return none
    return some (.TypeOperator (.TypePair a b))
  | _ =>
    if !e.hasLooseBVars then
      let e' ← whnf e
      if e' != e then return ← leanTypeToBuiltinType e'
    return none

/-- Emit an empty list constant with the correct element type. -/
private def emptyListLit (elemType : BuiltinType) : MIR.Expr :=
  let listType := BuiltinType.TypeOperator (.TypeList elemType)
  match elemType with
  | .AtomicType .TypeData => .Lit (.ConstDataList [], listType)
  | _ => .Lit (.ConstList [], listType)

/-- Try to fold List.cons into a constant list node.
    Returns `some folded` if both head and tail are constants. -/
private def foldListCons (head tail : MIR.Expr) : Option MIR.Expr :=
  match head, tail with
  | .Lit (.Data d, _), .Lit (.ConstDataList ds, ty) =>
    some (.Lit (.ConstDataList (d :: ds), ty))
  | .Lit (hc, _), .Lit (.ConstList cs, ty) =>
    some (.Lit (.ConstList (hc :: cs), ty))
  | _, _ => none

structure TranslateState where
  nextFresh : Nat := 0

structure TranslateCtx where
  locals : List MIR.VarId := []
  unfolding : NameSet := {}
  maxDepth : Nat := 200
  selfName : Option Name := none
  selfVar : Option MIR.VarId := none
  /-- When inside WellFounded.fix, the MIR VarId of the recursive function.
      Used to strip proof arguments from recursive calls. -/
  recFnVar : Option MIR.VarId := none

abbrev TranslateM := ReaderT TranslateCtx (StateRefT TranslateState MetaM)

private def freshVarId (hint : String := "") : TranslateM MIR.VarId := do
  let s ← get
  set { s with nextFresh := s.nextFresh + 1 }
  pure ⟨s.nextFresh, hint⟩

private def withLocal (v : MIR.VarId) (m : TranslateM α) : TranslateM α :=
  withReader (fun ctx => { ctx with locals := v :: ctx.locals }) m

private def withUnfolding (name : Name) (m : TranslateM α) : TranslateM α :=
  withReader (fun ctx => { ctx with
    unfolding := ctx.unfolding.insert name
    maxDepth := ctx.maxDepth - 1
  }) m

/-- Check if a type is a type family (a function ending in Sort). -/
private def isTypeFamily : Lean.Expr → Bool
  | .sort _ => true
  | .forallE _ _ body _ => isTypeFamily body
  | _ => false

/-- Check if a lambda binder should be erased.
    Erase if: the param type is a Sort (argument is a type),
    the param type is a type family (e.g. motives: Bool → Sort u),
    the param type is a Prop (argument is a proof),
    or the binder is a typeclass instance. -/
private def isErasableBinder (paramTy : Lean.Expr) (bi : BinderInfo) : MetaM Bool := do
  -- Instance parameter: always erase
  if bi == .instImplicit then return true
  -- Type parameter: paramTy is Sort u, meaning the argument will be a type
  if paramTy.isSort then return true
  -- Type family: paramTy is a function ending in Sort (e.g. match motives)
  if isTypeFamily paramTy then return true
  -- Proof parameter: paramTy is a proposition (guard against ill-typed exprs)
  if !paramTy.hasLooseBVars then
    try
      if ← isProp paramTy then return true
    catch _ => pure ()
  return false

private def shouldEraseArg (f : Lean.Expr) : TranslateM Bool := do
  -- Can't call inferType on expressions with loose bvars (MetaM panics)
  if f.hasLooseBVars then return false
  try
    let fTy ← inferType f
    match fTy with
    | .forallE _ paramTy _ bi => isErasableBinder paramTy bi
    | _ => pure false
  catch _ => pure false

private def uncurryApp (e : Lean.Expr) : Lean.Expr × Array Lean.Expr :=
  go e #[]
where
  go : Lean.Expr → Array Lean.Expr → Lean.Expr × Array Lean.Expr
    | .app f a, args => go f (args.push a)
    | f, args => (f, args.reverse)

private def isCasesOn (name : Name) : Bool :=
  match name with
  | .str _ "casesOn" => true
  | _ => false

private def isRec (name : Name) : Bool :=
  match name with
  | .str _ "rec" => true
  | .str _ "recOn" => true
  | _ => false

private def isBrecOn (name : Name) : Bool :=
  match name with
  | .str _ "brecOn" => true
  | _ => false

private def explicitRecursorName? (e : Lean.Expr) : Option Name :=
  match e.find? fun
      | .const n _ => isRec n || isBrecOn n
      | _ => false with
  | some (.const n _) => some n
  | _ => none

private def smartUnfoldingValue? (env : Environment) (name : Name) : Option Lean.Expr :=
  match env.find? (name ++ `_sunfold) with
  | some ci => ci.value?
  | none => none

private def explicitRecursorCompileError (owner recursor : Name) : MessageData :=
  m!"cannot compile {owner}: explicit recursor {recursor} is unsupported in `compile!` when Lean did not generate {(owner ++ `_sunfold)}; write recursive equations and let Lean generate `_sunfold`, or use well-founded recursion"

private def explicitRecursorExprError (recursor : Name) : MessageData :=
  m!"explicit recursor {recursor} is unsupported; write recursive equations and let Lean generate `_sunfold`, or use well-founded recursion"

/-- Check if an expression syntactically references a constant name. -/
private def exprContainsConst (e : Lean.Expr) (name : Name) : Bool :=
  Option.isSome <| e.find? fun
    | .const n _ => n == name
    | _ => false

/-- Evaluate a Nat expression to a literal value (handles .lit, Nat.zero, Nat.succ). -/
private partial def evalNatLit (e : Lean.Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | .const n _ => if n == ``Nat.zero then some 0 else none
  | .app fn arg =>
    let (head, args) := uncurryApp (.app fn arg)
    match head with
    | .const n _ =>
      if n == ``Nat.succ && args.size == 1 then
        (evalNatLit args[0]!).map (· + 1)
      else none
    | _ => none
  | _ => none

/-- Evaluate a closed ByteArray expression to a concrete value.
    Uses `evalExpr` to handle all forms of construction (string coercion, array literals, etc.). -/
private unsafe def evalByteArrayLitImpl (e : Lean.Expr) : MetaM (Option ByteArray) := do
  try
    let ba ← Lean.Meta.evalExpr ByteArray (mkConst ``ByteArray) e
    return some ba
  catch _ => return none

@[implemented_by evalByteArrayLitImpl]
private opaque evalByteArrayLit (e : Lean.Expr) : MetaM (Option ByteArray)

/-- Get the non-erased field types for a constructor, substituting type parameters
    with the actual type arguments from the constructor/casesOn application.
    This gives concrete field types that can be resolved by `resolveDataCodec`. -/
private def getCtorFieldTypesWithArgs (env : Environment) (ctorName : Name) (numParams : Nat)
    (typeArgs : Array Lean.Expr := #[]) : MetaM (Array Lean.Expr) := do
  match env.find? ctorName with
  | some (.ctorInfo cval) =>
    let mut fields : Array Lean.Expr := #[]
    let mut ty := cval.type
    let mut paramIdx := 0
    while ty.isForall do
      match ty with
      | .forallE _ dom body bi =>
        if paramIdx < numParams then
          let subst := if h : paramIdx < typeArgs.size then typeArgs[paramIdx]
                       else .const ``Unit.unit []
          ty := body.instantiate1 subst
          paramIdx := paramIdx + 1
        else
          let erase ← isErasableBinder dom bi
          if !erase then
            fields := fields.push dom
          ty := body.instantiate1 (.const ``Unit.unit [])
      | _ => break
    pure fields
  | _ => pure #[]

/-- Build a Data list from field values: mkCons f0 (mkCons f1 ... []) -/
private def mkDataList (fields : List MIR.Expr) : MIR.Expr :=
  fields.foldr (init := .Lit (.ConstDataList [], .TypeOperator (.TypeList (.AtomicType .TypeData))))
    fun f acc => .App (.App (mkBuiltin .MkCons) f) acc

/-- Reduce a single projection by whnf-ing only the struct part. -/
private partial def reduceProj (e : Lean.Expr) : TranslateM (Option Lean.Expr) := do
  match e with
  | .proj typeName idx struct =>
    if !struct.hasLooseBVars then
      let struct' ← whnf struct
      match struct'.getAppFn with
      | .const _ _ =>
        let env ← getEnv
        -- .proj index is relative to fields (after params), but getAppArgs includes params
        let numParams := match env.find? typeName with
          | some (.inductInfo iv) => iv.numParams
          | _ => 0
        let args := struct'.getAppArgs
        let adjustedIdx := numParams + idx
        if h : adjustedIdx < args.size then
          return some args[adjustedIdx]
        else return none
      | _ => return none
    else return none
  | _ => return none

/-- Resolve a bvar-free expression to a known builtin by iteratively
    unfolding definitions and resolving projections. Stops as soon as
    the head becomes a builtin name. -/
private partial def resolveToBuiltin (e : Lean.Expr) (fuel : Nat) : TranslateM (Option Lean.Expr) := do
  if fuel == 0 then return none
  let (head, headArgs) := uncurryApp e
  let headName := head.constName?
  if let .const name _ := head then
    if isBuiltinName name then return some e
  -- If head is a lambda, beta-reduce with available args
  if head.isLambda then
    let e' := e.headBeta
    if e' != e then
      return ← resolveToBuiltin e' (fuel - 1)
    -- Lambda with no args: peel lambdas and resolve bvar-free prefix of body.
    -- E.g. fun a b => Add.add Int inst a b → resolve Add.add Int inst → Int.add
    -- → return fun a b => Int.add a b
    let mut body := head
    let mut binders : Array (Name × Lean.Expr × BinderInfo) := #[]
    while body.isLambda do
      match body with
      | .lam n ty b bi => binders := binders.push (n, ty, bi); body := b
      | _ => break
    let (innerFn, innerArgs) := uncurryApp body
    let mut innerPrefix := innerFn
    let mut innerConsumed : Nat := 0
    for arg in innerArgs do
      let candidate := Lean.Expr.app innerPrefix arg
      if candidate.hasLooseBVars then break
      innerPrefix := candidate
      innerConsumed := innerConsumed + 1
    if innerConsumed > 0 && !innerPrefix.hasLooseBVars then
      let innerResolved ← resolveToBuiltin innerPrefix (fuel - 1)
      if let some builtin := innerResolved then
        -- Reconstruct: resolved prefix + remaining inner args, re-wrapped in lambdas
        let innerRemaining := innerArgs.extract innerConsumed innerArgs.size
        let mut newBody := innerRemaining.foldl (init := builtin) fun acc a => .app acc a
        for i in [:binders.size] do
          let (n, ty, bi) := binders[binders.size - 1 - i]!
          newBody := .lam n ty newBody bi
        return some newBody
    return none
  -- If head is a projection, try to reduce it
  if head.isProj then
    let some head' ← reduceProj head | return none
    let e' := headArgs.foldl (init := head') fun acc a => .app acc a
    return ← resolveToBuiltin e' (fuel - 1)
  -- Try unfolding the head constant one step
  let some e' ← try unfoldDefinition? e catch _ => pure none
    | return none
  let e'' := e'.headBeta
  let (head', _) := uncurryApp e''
  if let .const name' _ := head' then
    if isBuiltinName name' then return some e''
  if head'.constName? != headName || head'.isProj then
    resolveToBuiltin e'' (fuel - 1)
  else
    return none

/-- Peel leading Lam binders from a MIR expression, up to `n` layers. -/
private def peelLambdas (e : MIR.Expr) (n : Nat) : Array MIR.VarId × MIR.Expr :=
  go e n #[]
where
  go : MIR.Expr → Nat → Array MIR.VarId → Array MIR.VarId × MIR.Expr
    | .Lam x body, n+1, acc => go body n (acc.push x)
    | e, _, acc => (acc, e)

/-- Encode a MIR expression to Data according to a DataCodec plan. -/
private partial def encodeToData (codec : DataCodec) (val : MIR.Expr) : TranslateM MIR.Expr := do
  match codec with
  | .param idx => throwError "BUG: unresolved type parameter codec (.param {idx}) in encodeToData"
  | .identity | .constrData _ => return val
  | .iData => return .App (mkBuiltin .IData) val
  | .bData => return .App (mkBuiltin .BData) val
  | .listData elemCodec =>
    if elemCodec.isIdentity then
      return .App (mkBuiltin .ListData) val
    else
      let mapF ← freshVarId "mapEnc"
      let xs ← freshVarId "xs"
      let headExpr := MIR.Expr.App (mkBuiltin .HeadList) (.Var xs)
      let encodedHead ← encodeToData elemCodec headExpr
      let tailExpr := MIR.Expr.App (mkBuiltin .TailList) (.Var xs)
      let recurse := MIR.Expr.App (.Var mapF) tailExpr
      let cons := MIR.Expr.App (.App (mkBuiltin .MkCons) encodedHead) recurse
      let nil := MIR.Expr.Lit (.ConstDataList [], .TypeOperator (.TypeList (.AtomicType .TypeData)))
      let consH ← freshVarId "enc_cons"
      let nilH ← freshVarId "enc_nil"
      let mapBody := MIR.Expr.Let [(consH, .Delay cons, false), (nilH, .Delay nil, false)]
        (.Case (.App (mkBuiltin .NullList) (.Var xs))
          [.Force (.Var consH), .Force (.Var nilH)])
      let mapFn := MIR.Expr.Fix mapF (.Lam xs mapBody)
      return .App (mkBuiltin .ListData) (.App mapFn val)
  | .mapData keyCodec valCodec =>
    if keyCodec.isIdentity && valCodec.isIdentity then
      return .App (mkBuiltin .MapData) val
    else
      let mapF ← freshVarId "mapEnc"
      let xs ← freshVarId "xs"
      let pair ← freshVarId "pair"
      let rawKey := MIR.Expr.App (mkBuiltin .FstPair) (.Var pair)
      let rawVal := MIR.Expr.App (mkBuiltin .SndPair) (.Var pair)
      let encodedKey ← encodeToData keyCodec rawKey
      let encodedVal ← encodeToData valCodec rawVal
      let newPair := MIR.Expr.App (.App (mkBuiltin .MkPairData) encodedKey) encodedVal
      let tailExpr := MIR.Expr.App (mkBuiltin .TailList) (.Var xs)
      let recurse := MIR.Expr.App (.Var mapF) tailExpr
      -- Bind `pair = headList xs` inside the delayed cons branch
      -- so headList is only called when the list is non-empty
      let consBody := MIR.Expr.App (.App (mkBuiltin .MkCons) newPair) recurse
      let cons := MIR.Expr.Let [(pair, .App (mkBuiltin .HeadList) (.Var xs), false)] consBody
      let nil := MIR.Expr.Lit
        (.ConstPairDataList [], .TypeOperator (.TypeList
          (.TypeOperator (.TypePair (.AtomicType .TypeData) (.AtomicType .TypeData)))))
      let consH ← freshVarId "enc_cons"
      let nilH ← freshVarId "enc_nil"
      let mapBody := MIR.Expr.Let
        [(consH, .Delay cons, false), (nilH, .Delay nil, false)]
        (.Case (.App (mkBuiltin .NullList) (.Var xs))
          [.Force (.Var consH), .Force (.Var nilH)])
      let mapFn := MIR.Expr.Fix mapF (.Lam xs mapBody)
      return .App (mkBuiltin .MapData) (.App mapFn val)

/-- Decode a MIR expression from Data according to a DataCodec plan. -/
private partial def decodeFromData (codec : DataCodec) (val : MIR.Expr) : TranslateM MIR.Expr := do
  match codec with
  | .param idx => throwError "BUG: unresolved type parameter codec (.param {idx}) in decodeFromData"
  | .identity | .constrData _ => return val
  | .iData => return .App (mkBuiltin .UnIData) val
  | .bData => return .App (mkBuiltin .UnBData) val
  | .listData _elemCodec => return .App (mkBuiltin .UnListData) val
    -- if elemCodec.isIdentity then
    --   return .App (mkBuiltin .UnListData) val
    -- else
    --   let unlistedV ← freshVarId "unlisted"
    --   let mapF ← freshVarId "mapDec"
    --   let xs ← freshVarId "xs"
    --   let headExpr := MIR.Expr.App (mkBuiltin .HeadList) (.Var xs)
    --   let decodedHead ← decodeFromData elemCodec headExpr
    --   let tailExpr := MIR.Expr.App (mkBuiltin .TailList) (.Var xs)
    --   let recurse := MIR.Expr.App (.Var mapF) tailExpr
    --   let cons := MIR.Expr.App (.App (mkBuiltin .MkCons) decodedHead) recurse
    --   let nil := MIR.Expr.Lit (.ConstDataList [], .TypeOperator (.TypeList (.AtomicType .TypeData)))
    --   let consH ← freshVarId "dec_cons"
    --   let nilH ← freshVarId "dec_nil"
    --   let mapBody := MIR.Expr.Let [(consH, .Delay cons), (nilH, .Delay nil)]
    --     (.Case (.App (mkBuiltin .NullList) (.Var xs))
    --       [.Force (.Var consH), .Force (.Var nilH)])
    --   let mapFn := MIR.Expr.Fix mapF (.Lam xs mapBody)
    --   return .Let [(unlistedV, .App (mkBuiltin .UnListData) val)]
    --     (.App mapFn (.Var unlistedV))
  | .mapData _keyCodec _valCodec => return .App (mkBuiltin .UnMapData) val
    -- if keyCodec.isIdentity && valCodec.isIdentity then
    --   return .App (mkBuiltin .UnMapData) val
    -- else
    --   let unmappedV ← freshVarId "unmapped"
    --   let mapF ← freshVarId "mapDec"
    --   let xs ← freshVarId "xs"
    --   let pair ← freshVarId "pair"
    --   let rawKey := MIR.Expr.App (mkBuiltin .FstPair) (.Var pair)
    --   let rawVal := MIR.Expr.App (mkBuiltin .SndPair) (.Var pair)
    --   let decodedKey ← decodeFromData keyCodec rawKey
    --   let decodedVal ← decodeFromData valCodec rawVal
    --   let newPair := MIR.Expr.App (.App (mkBuiltin .MkPairData) decodedKey) decodedVal
    --   let tailExpr := MIR.Expr.App (mkBuiltin .TailList) (.Var xs)
    --   let recurse := MIR.Expr.App (.Var mapF) tailExpr
    --   let cons := MIR.Expr.App (.App (mkBuiltin .MkCons) newPair) recurse
    --   let nil := MIR.Expr.Lit
    --     (.ConstPairDataList [], .TypeOperator (.TypeList
    --       (.TypeOperator (.TypePair (.AtomicType .TypeData) (.AtomicType .TypeData)))))
    --   let consH ← freshVarId "dec_cons"
    --   let nilH ← freshVarId "dec_nil"
    --   let mapBody := MIR.Expr.Let
    --     [(pair, .App (mkBuiltin .HeadList) (.Var xs)),
    --      (consH, .Delay cons), (nilH, .Delay nil)]
    --     (.Case (.App (mkBuiltin .NullList) (.Var xs))
    --       [.Force (.Var consH), .Force (.Var nilH)])
    --   let mapFn := MIR.Expr.Fix mapF (.Lam xs mapBody)
    --   return .Let [(unmappedV, .App (mkBuiltin .UnMapData) val)]
    --     (.App mapFn (.Var unmappedV))

/-- Resolve field types to DataCodec plans. Fails with an error for unsupported types. -/
private def resolveFieldCodecs (fieldTypes : Array Lean.Expr) (context : String)
    : TranslateM (Array DataCodec) := do
  let mut codecs : Array DataCodec := #[]
  for i in [:fieldTypes.size] do
    match ← resolveDataCodec fieldTypes[i]! with
    | .ok codec => codecs := codecs.push codec
    | .error e =>
      throwError "@[plutus_data] {context} field {i}: {formatDataCompatError e}"
  return codecs

mutual
  partial def translateExpr (e : Lean.Expr) : TranslateM MIR.Expr := do
    let ctx ← read
    if ctx.maxDepth == 0 then
      throwError "translation depth exceeded (probable infinite unfolding)"
    match e with
    | .bvar i =>
      match ctx.locals[i]? with
      | some vid => pure (.Var vid)
      | none => throwError "unbound de Bruijn index {i}"

    | .fvar _ => throwError "unexpected free variable in kernel expression"
    | .mvar _ => throwError "unexpected metavariable in kernel expression"
    | .sort _ => pure .Error
    | .forallE _ _ _ _ => pure .Error
    | .mdata _ e => translateExpr e

    | .lam name ty body bi => do
      if ← isErasableBinder ty bi then
        let body' := body.instantiate1 (.const ``Unit.unit [])
        translateExpr body'
      else
        let v ← freshVarId name.toString
        let body' ← withLocal v (translateExpr body)
        pure (.Lam v body')

    | .letE _name ty val body _ => do
      let tyIsProp ← if ty.hasLooseBVars then pure false
        else try isProp ty catch _ => pure false
      if ty.isSort || tyIsProp then
        let body' := body.instantiate1 (.const ``Unit.unit [])
        translateExpr body'
      else
        let v ← freshVarId _name.toString
        let val' ← translateExpr val
        let body' ← withLocal v (translateExpr body)
        pure (.Let [(v, val', false)] body')

    | .lit (.natVal n) =>
      pure (.Lit (.Integer n, .AtomicType .TypeInteger))

    | .lit (.strVal s) =>
      pure (.Lit (.String s, .AtomicType .TypeString))

    | .proj typeName idx struct => do
      if !e.hasLooseBVars then
        let e' ← whnf e
        if e' != e then return ← translateExpr e'
      -- Translate projection directly: extract field `idx` from struct
      translateProj typeName idx struct

    | .const name _ => translateConst name

    | .app _ _ => translateApp e

  partial def translateApp (e : Lean.Expr) : TranslateM MIR.Expr := do
    -- Check for casesOn/rec patterns before whnf
    let (fn, args) := uncurryApp e
    if let .const name _ := fn then
      if isCasesOn name then
        return ← translateCasesOn name args
      -- Int.ofNat n → integer literal
      if name == ``Int.ofNat then
        return ← translateIntOfNat args
      -- Int.negSucc n → negative integer literal
      if name == ``Int.negSucc then
        return ← translateIntNegSucc args
      if name == ``WellFounded.fix then
        return ← translateWellFoundedFix fn args
      -- ite: `if b then t else f` where b : Bool
      -- Lean elaborates this as @ite α (@Eq Bool b Bool.true) inst t f
      if name == ``ite && args.size >= 5 then
        let prop := args[1]!
        let (propFn, propArgs) := uncurryApp prop
        if propFn.isConstOf ``Eq && propArgs.size >= 3 && propArgs[0]!.isConstOf ``Bool then
          let boolExpr := propArgs[1]!
          let scrut ← translateExpr boolExpr
          let trueAlt ← translateExpr args[3]!
          let falseAlt ← translateExpr args[4]!
          return ← applyOverArgs (mkBoolBranch scrut trueAlt falseAlt) args 5
      if isRec name then
        throwError (explicitRecursorExprError name)
      -- PlutusData.toData on @[plutus_data] types: identity
      if name == `Moist.Onchain.PlutusData.toData && args.size >= 3 then
        let ty' ← whnf args[0]!
        let typeName := ty'.getAppFn.constName?.getD Name.anonymous
        let env ← getEnv
        if plutusDataAttr.hasTag env typeName || typeName == ``Moist.Plutus.Data then
          return ← translateExpr args[2]!
      -- PlutusData.unsafeFromData on @[plutus_data] types: identity
      if name == `Moist.Onchain.PlutusData.unsafeFromData && args.size >= 3 then
        let ty' ← whnf args[0]!
        let typeName := ty'.getAppFn.constName?.getD Name.anonymous
        let env ← getEnv
        if plutusDataAttr.hasTag env typeName || typeName == ``Moist.Plutus.Data then
          return ← translateExpr args[2]!
      -- ByteArray/ByteString literal: evaluate to concrete bytes
      if name == ``ByteArray.mk && !e.hasLooseBVars then
        if let some ba ← evalByteArrayLit e then
          return .Lit (.ByteString ba, .AtomicType .TypeByteString)

    -- Try whnf to reduce the expression
    if !e.hasLooseBVars then
      let e' ← whnf e
      if !e'.isApp then
        return ← translateExpr e'
      let headChanged := e'.getAppFn.constName? != e.getAppFn.constName?
      if headChanged then
        return ← translateExpr e'
    else
      -- Expression has loose bvars — whnf on the full expr would panic.
      -- Try unfolding match auxiliary functions and beta-reducing.
      -- This handles `aaa.match_1 T x body_fn` by inlining the match_1
      -- definition and beta-reducing to expose the casesOn with the actual
      -- match body, enabling unused wildcard field detection.
      if let .const headName _ := fn then
        -- Only unfold match auxiliary functions (last name component starts with "match_")
        let isMatchAux := match headName with
          | .str _ s => s.startsWith "match_"
          | _ => false
        if isMatchAux then
          let env ← getEnv
          if let some ci := env.find? headName then
            if let some headVal := ci.value? then
              let fullApp := args.foldl (init := headVal) fun acc a => .app acc a
              let reduced := fullApp.headBeta
              let newFn := reduced.getAppFn
              if newFn.constName? != some headName then
                return ← translateExpr reduced
      -- Try whnf on the longest bvar-free prefix (e.g. HAdd.hAdd Int Int Int inst)
      -- to resolve typeclass methods to concrete implementations.
      let mut prefixExpr := fn
      let mut nConsumed : Nat := 0
      for arg in args do
        let candidate := Lean.Expr.app prefixExpr arg
        if candidate.hasLooseBVars then break
        prefixExpr := candidate
        nConsumed := nConsumed + 1
      if nConsumed > 0 && !prefixExpr.hasLooseBVars then
        -- Try resolveToBuiltin first — handles simple cases (e.g. HAdd.hAdd → Int.add)
        let resolved ← resolveToBuiltin prefixExpr 20
        if let some reduced := resolved then
          if reduced != prefixExpr then
            let remainingArgs := args.extract nConsumed args.size
            let fullReduced := remainingArgs.foldl (init := reduced) fun acc a => .app acc a
            return ← translateExpr fullReduced.headBeta
        -- Fallback: whnf for compound typeclass methods (e.g. BEq.beq → fun a b => equalsData ...)
        let whnfResult ← whnf prefixExpr
        if whnfResult != prefixExpr then
          let remainingArgs := args.extract nConsumed args.size
          let fullReduced := remainingArgs.foldl (init := whnfResult) fun acc a => .app acc a
          return ← translateExpr fullReduced.headBeta
    -- Translate directly
    translateAppDirect e

  /-- Translate a structure projection `struct.fieldN` directly to MIR.
      For @[plutus_data]: UnConstrData → SndPair → walk list → decode field.
      For SOP: Case → extract field from the single constructor branch. -/
  partial def translateProj (typeName : Name) (idx : Nat) (struct : Lean.Expr)
      : TranslateM MIR.Expr := do
    let env ← getEnv
    match env.find? typeName with
    | some (.inductInfo iv) =>
      if iv.ctors.length != 1 then
        throwError "projection on multi-constructor type {typeName} not supported"
      let ctorName := iv.ctors[0]!
      let np := iv.numParams
      -- Get type args from the struct's type if possible
      let typeArgs ← do
        if !struct.hasLooseBVars then
          let ty ← inferType struct
          let ty' ← whnf ty
          pure (ty'.getAppArgs.extract 0 np)
        else
          pure #[]
      -- Check for builtin pair type first (Prod)
      if let some .pair := builtinTypeKind typeName then
        let scrut ← translateExpr struct
        if idx == 0 then return .App (mkBuiltin .FstPair) scrut
        else return .App (mkBuiltin .SndPair) scrut
      let fieldTypes ← getCtorFieldTypesWithArgs env ctorName np typeArgs
      let scrut ← translateExpr struct
      let repr := getPlutusRepr env typeName
      if repr == .data then
        -- @[plutus_data]: UnConstrData → SndPair → walk to field idx → decode
        let fieldCodecs ← resolveFieldCodecs fieldTypes s!"projection on '{typeName}'"
        if idx >= fieldCodecs.size then
          throwError "projection index {idx} out of range for {typeName} ({fieldCodecs.size} fields)"
        let pairV ← freshVarId "pair"
        let fieldsV ← freshVarId "fields"
        let mut currentList : MIR.Expr := .Var fieldsV
        let mut bindings : Array (MIR.VarId × MIR.Expr) := #[
          (pairV, .App (mkBuiltin .UnConstrData) scrut),
          (fieldsV, .App (mkBuiltin .SndPair) (.Var pairV))
        ]
        -- Walk to field idx
        for i in [:idx] do
          let tailV ← freshVarId s!"rest{i}"
          bindings := bindings.push (tailV, .App (mkBuiltin .TailList) currentList)
          currentList := .Var tailV
        -- Extract and decode the field
        let fieldV ← freshVarId s!"f{idx}"
        let rawHead := MIR.Expr.App (mkBuiltin .HeadList) currentList
        let decoded ← decodeFromData fieldCodecs[idx]! rawHead
        bindings := bindings.push (fieldV, decoded)
        -- Wrap in let bindings
        let mut result : MIR.Expr := .Var fieldV
        for i in [:bindings.size] do
          let (v, val) := bindings[bindings.size - 1 - i]!
          result := .Let [(v, val, false)] result
        pure result
      else
        -- SOP: Case with single branch, extract field positionally
        let numFields := fieldTypes.size
        if idx >= numFields then
          throwError "projection index {idx} out of range for {typeName} ({numFields} fields)"
        -- Transparent newtype: single-constructor, single-value-field, no explicit @[plutus_sop] → identity
        let numCtors := match env.find? typeName with
          | some (.inductInfo iv) => iv.ctors.length
          | _ => 0
        if numCtors == 1 && numFields == 1 && idx == 0 && !plutusSopAttr.hasTag env typeName then
          return scrut
        -- Build a lambda that ignores all fields except idx
        let mut vars : Array MIR.VarId := #[]
        for i in [:numFields] do
          vars := vars.push (← freshVarId s!"sf{i}")
        let body : MIR.Expr := .Var vars[idx]!
        let mut alt := body
        for i in [:numFields] do
          alt := .Lam vars[numFields - 1 - i]! alt
        pure (.Case scrut [alt])
    | _ => throwError "projection on unknown type {typeName}"

  /-- Apply over-applied args beyond the casesOn alternatives.
      When WellFounded.fix threads the recursive function through a match,
      the casesOn result is a function and extra args must be applied. -/
  private partial def applyOverArgs (result : MIR.Expr) (args : Array Lean.Expr)
      (startIdx : Nat) : TranslateM MIR.Expr := do
    if startIdx ≥ args.size then return result
    let mut r := result
    for i in [startIdx : args.size] do
      let arg := args[i]!
      let erase ← if arg.hasLooseBVars then pure false
        else try
          let argTy ← inferType arg
          if argTy.isSort then pure true
          else if isTypeFamily argTy then pure true
          else if ← isProp argTy then pure true
          else pure false
        catch _ => pure false
      if !erase then
        let arg' ← translateExpr arg
        r := .App r arg'
    return r

  partial def translateCasesOn (caseName : Name) (args : Array Lean.Expr)
      : TranslateM MIR.Expr := do
    let typeName := caseName.getPrefix
    let env ← getEnv
    match env.find? typeName with
    | some (.inductInfo iv) =>
      let np := iv.numParams
      -- casesOn layout: [params...] [motive] [scrutinee] [alts...]
      let scrutIdx := np + 1
      if h : scrutIdx < args.size then
        let altsStart := scrutIdx + 1
        let numAlts := iv.ctors.length
        let expectedEnd := altsStart + numAlts

        -- Check for UPLC builtin types first
        if let some kind := builtinTypeKind typeName then
          let scrut ← translateExpr args[scrutIdx]
          match kind with
          | .bool =>
            -- Bool.casesOn scrut false_alt true_alt
            -- → Force (IfThenElse scrut (Delay true_alt) (Delay false_alt))
            -- Note: casesOn alts are [cidx=0=false, cidx=1=true],
            --        IfThenElse returns arg2 on True, arg3 on False.
            if h2 : altsStart + 1 < args.size then
              let falseAlt ← translateExpr args[altsStart]
              let trueAlt ← translateExpr args[altsStart + 1]
              return ← applyOverArgs (mkBoolBranch scrut trueAlt falseAlt) args expectedEnd
            else throwError "Bool.casesOn: not enough alternatives"
          | .unit =>
            -- Unit.casesOn scrut alt → alt (unit carries no information)
            if h2 : altsStart < args.size then
              let core ← translateExpr args[altsStart]
              return ← applyOverArgs core args expectedEnd
            else throwError "Unit.casesOn: not enough alternatives"
          | .list =>
            -- List.casesOn scrut nil_alt cons_alt
            -- cons_alt is a lambda: λ head. λ tail. body
            -- → let s = scrut in
            --   Force (ChooseList s (Delay nil_alt)
            --     (Delay (cons_alt (Force HeadList s) (Force TailList s))))
            if h2 : altsStart + 1 < args.size then
              let nilAlt ← translateExpr args[altsStart]
              let consAlt ← translateExpr args[altsStart + 1]
              let s ← freshVarId "ls"
              let hd := MIR.Expr.App (mkBuiltin .HeadList) (.Var s)
              let tl := MIR.Expr.App (mkBuiltin .TailList) (.Var s)
              let consBody := MIR.Expr.App (.App consAlt hd) tl
              let core := MIR.Expr.Let [(s, scrut, false)]
                (.Force (.App (.App (.App (mkBuiltin .ChooseList) (.Var s))
                  (.Delay nilAlt)) (.Delay consBody)))
              return ← applyOverArgs core args expectedEnd
            else throwError "List.casesOn: not enough alternatives"
          | .pair =>
            -- Prod.casesOn scrut (λ fst snd => body)
            -- → let s = scrut in alt (Force (Force FstPair) s) (Force (Force SndPair) s)
            if h2 : altsStart < args.size then
              let alt ← translateExpr args[altsStart]
              let s ← freshVarId "pr"
              let fst := MIR.Expr.App (mkBuiltin .FstPair) (.Var s)
              let snd := MIR.Expr.App (mkBuiltin .SndPair) (.Var s)
              let core := MIR.Expr.Let [(s, scrut, false)]
                (.App (.App alt fst) snd)
              return ← applyOverArgs core args expectedEnd
            else throwError "Prod.casesOn: not enough alternatives"
        else
          -- Non-builtin: SOP or Data encoding
          let scrut ← translateExpr args[scrutIdx]
          let repr := getPlutusRepr env typeName
          if repr == .sop then
            -- SOP encoding: emit direct Constr/Case.
            let mut alts : Array MIR.Expr := #[]
            for i in [:numAlts] do
              if h2 : altsStart + i < args.size then
                let alt ← translateExpr args[altsStart + i]
                alts := alts.push alt
              else
                throwError "casesOn for {typeName}: not enough alternatives"
            let core := MIR.Expr.Case scrut alts.toList
            return ← applyOverArgs core args expectedEnd
          else
            -- Data encoding: unConstrData + tag dispatch + field extraction
            let typeArgs := args.extract 0 np
            let core ← translateDataCasesOn env iv np typeArgs scrut args altsStart numAlts
            return ← applyOverArgs core args expectedEnd
      else
        throwError "casesOn for {typeName}: not enough arguments (need scrutinee)"
    | _ =>
      -- Not an inductive — try unfolding via whnf
      let e := args.foldl (init := Lean.Expr.const caseName []) fun acc arg => .app acc arg
      if !e.hasLooseBVars then
        let e' ← whnf e
        if e' != e then
          return ← translateExpr e'
      throwError "casesOn for unknown type {typeName}"

  /-- Handle casesOn for @[plutus_data] types using unConstrData + field extraction. -/
  partial def translateDataCasesOn (env : Environment) (iv : InductiveVal)
      (numParams : Nat) (typeArgs : Array Lean.Expr) (scrut : MIR.Expr)
      (args : Array Lean.Expr) (altsStart : Nat) (numAlts : Nat)
      : TranslateM MIR.Expr := do
    -- let pair = unConstrData scrut
    let pairV ← freshVarId "pair"
    -- let tag = fstPair pair
    let tagV ← freshVarId "tag"
    -- let fieldList = sndPair pair
    let fieldsV ← freshVarId "fields"
    -- Build each alternative body with field extraction
    let mut altBodies : Array MIR.Expr := #[]
    for i in [:numAlts] do
      if h : altsStart + i < args.size then
        let altExpr := args[altsStart + i]
        let ctorName := iv.ctors[i]!
        let fieldTypes ← getCtorFieldTypesWithArgs env ctorName numParams typeArgs
        let fieldCodecs ← resolveFieldCodecs fieldTypes s!"match on '{iv.name}', constructor '{ctorName}'"
        let body ←
          match ← translateAltBodyWithFieldLocals fieldCodecs altExpr (.Var fieldsV) with
          | some directBody => pure directBody
          | none =>
            let altMir ← translateExpr altExpr
            -- Fallback for unexpected branch shapes: translate the whole
            -- alternative and re-apply the extracted fields.
            buildFieldExtraction fieldCodecs altMir (.Var fieldsV)
        altBodies := altBodies.push body
      else
        throwError "data casesOn for {iv.name}: not enough alternatives"
    -- Build tag dispatch: chain of equalsInteger checks
    let dispatch ← buildTagDispatch (.Var tagV) altBodies 0
    -- Wrap in let bindings
    pure (.Let [(pairV, .App (mkBuiltin .UnConstrData) scrut, true)]
      (.Let [(tagV, .App (mkBuiltin .FstPair) (.Var pairV), true)]
        (.Let [(fieldsV, .App (mkBuiltin .SndPair) (.Var pairV), true)]
          dispatch)))

  /-- Extract fields from a Data list and apply them to an alternative lambda.
      The alt should be a multi-arg lambda (Lam v1 (Lam v2 ... body)).
      Skips extraction for fields whose corresponding lambda parameter is unused
      (wildcards), avoiding unnecessary headList/unIData calls in the output.

      For `| .foo a _ _ d => body` with 4 fields, produces:
        let f0 = unIData (headList fields)
        let rest0 = tailList fields
        let rest1 = tailList rest0
        let f3 = unIData (headList rest1)
        in (λa d. body) f0 f3
      instead of extracting all 4 fields. -/
  partial def buildFieldExtraction (fieldCodecs : Array DataCodec)
      (alt : MIR.Expr) (fieldList : MIR.Expr) : TranslateM MIR.Expr := do
    if fieldCodecs.size == 0 then return alt
    -- Peel lambda binders to detect which fields are actually used
    let (params, innerBody) := peelLambdas alt fieldCodecs.size
    -- If we can't peel the expected number of lambdas, fall back to extracting all
    if params.size != fieldCodecs.size then
      return ← buildFieldExtractionAll fieldCodecs alt fieldList
    -- Determine which fields are used in the body
    let usedMask : Array Bool := params.map fun p =>
      MIR.countOccurrences p innerBody > 0
    -- Find the last used field index (to know how far to traverse the list)
    let mut lastUsed? : Option Nat := none
    for i in [:fieldCodecs.size] do
      if usedMask[i]! then lastUsed? := some i
    -- If no fields are used, return just the inner body
    let some lastUsed := lastUsed? | return innerBody
    -- Build field extraction bindings, skipping unused fields
    let mut bindings : Array (MIR.VarId × MIR.Expr × Bool) := #[]
    let mut usedFieldVars : Array MIR.VarId := #[]
    let mut currentList := fieldList
    for i in [:lastUsed + 1] do
      if usedMask[i]! then
        let headV ← freshVarId s!"f{i}"
        let rawHead := MIR.Expr.App (mkBuiltin .HeadList) currentList
        let field ← decodeFromData fieldCodecs[i]! rawHead
        bindings := bindings.push (headV, field, true)
        usedFieldVars := usedFieldVars.push headV
      -- Advance list pointer if not at the last needed position
      if i < lastUsed then
        let tailV ← freshVarId s!"rest{i}"
        let tailExpr := MIR.Expr.App (mkBuiltin .TailList) currentList
        bindings := bindings.push (tailV, tailExpr, true)
        currentList := .Var tailV
    -- Re-wrap body with only used params as lambdas (innermost first)
    let mut wrappedBody := innerBody
    for i in [:params.size] do
      let idx := params.size - 1 - i
      if usedMask[idx]! then
        wrappedBody := .Lam params[idx]! wrappedBody
    -- Apply used field vars
    let mut applied := wrappedBody
    for v in usedFieldVars do
      applied := .App applied (.Var v)
    -- Wrap with let bindings (outside in)
    let mut result := applied
    for i in [:bindings.size] do
      let (v, val, er) := bindings[bindings.size - 1 - i]!
      result := .Let [(v, val, er)] result
    pure result

  /-- Translate a branch body directly with constructor fields bound as MIR
      locals, avoiding the reconstruct-and-apply artifact from elaborated
      wildcard branches like `fun a b => (fun _ => False) (Ctor a b)`.

      Returns `none` when the branch does not expose the expected number of
      value lambdas, allowing the caller to fall back to the older
      translate-then-apply path. -/
  partial def translateAltBodyWithFieldLocals (fieldCodecs : Array DataCodec)
      (altExpr : Lean.Expr) (fieldList : MIR.Expr) : TranslateM (Option MIR.Expr) := do
    let some (fieldVars, bodyMir) ← peelAltFieldLambdas fieldCodecs.size altExpr #[]
      | return none
    let bodyMir := simplifyDeadCtorApps bodyMir
    let body ← buildFieldBindingsForBody fieldCodecs fieldVars bodyMir fieldList
    return some body

  /-- Peel exactly `remaining` non-erased lambda binders from a branch
      alternative, binding them to fresh MIR locals. Erased binders are
      instantiated away. Returns the translated body under those locals. -/
  partial def peelAltFieldLambdas (remaining : Nat) (e : Lean.Expr)
      (fieldVars : Array MIR.VarId) : TranslateM (Option (Array MIR.VarId × MIR.Expr)) := do
    if remaining == 0 then
      let bodyExpr ← normalizeAltBodyExpr e
      return some (fieldVars, ← translateExpr bodyExpr)
    match e with
    | .lam name ty body bi =>
      if ← isErasableBinder ty bi then
        peelAltFieldLambdas remaining (body.instantiate1 (.const ``Unit.unit [])) fieldVars
      else
        let fieldV ← freshVarId name.toString
        withLocal fieldV do
          peelAltFieldLambdas (remaining - 1) body (fieldVars.push fieldV)
    | _ => pure none

  /-- Normalize a branch body enough to expose obvious dead beta-redexes and
      unfolded match helpers even when the expression still contains bound
      field variables. This is the key step that turns elaborated wildcard
      branches like `(fun _ => False) (Ctor a b)` into just `False` before
      MIR translation. -/
  partial def normalizeAltBodyExpr (e : Lean.Expr) : TranslateM Lean.Expr := do
    let e' := e.headBeta
    if e' != e then
      return ← normalizeAltBodyExpr e'
    let e'' ← peelTypeLambdas e'
    if e'' != e' then
      return ← normalizeAltBodyExpr e''
    let (fn, args) := uncurryApp e''
    if let .const headName _ := fn then
      let isMatchAux := match headName with
        | .str _ s => s.startsWith "match_"
        | _ => false
      if isMatchAux then
        let env ← getEnv
        if let some ci := env.find? headName then
          if let some headVal := ci.value? then
            let fullApp := args.foldl (init := headVal) fun acc arg => .app acc arg
            let reduced := fullApp.headBeta
            if reduced != e'' then
              return ← normalizeAltBodyExpr reduced
    if !e''.hasLooseBVars then
      let whnfExpr ← whnf e''
      if whnfExpr != e'' then
        return ← normalizeAltBodyExpr whnfExpr
    pure e''

  /-- Bind only the constructor fields actually referenced by `body`.
      This is the direct-body counterpart to `buildFieldExtraction`, but the
      branch body already refers to the target field variables directly, so no
      lambda re-wrapping or field application is needed. -/
  partial def buildFieldBindingsForBody (fieldCodecs : Array DataCodec)
      (fieldVars : Array MIR.VarId) (body : MIR.Expr) (fieldList : MIR.Expr)
      : TranslateM MIR.Expr := do
    if fieldCodecs.size == 0 then return body
    let usedMask : Array Bool := fieldVars.map fun v =>
      MIR.countOccurrences v body > 0
    let mut lastUsed? : Option Nat := none
    for i in [:fieldCodecs.size] do
      if usedMask[i]! then
        lastUsed? := some i
    let some lastUsed := lastUsed? | return body
    let mut bindings : Array (MIR.VarId × MIR.Expr × Bool) := #[]
    let mut currentList := fieldList
    for i in [:lastUsed + 1] do
      if usedMask[i]! then
        let rawHead := MIR.Expr.App (mkBuiltin .HeadList) currentList
        let field ← decodeFromData fieldCodecs[i]! rawHead
        bindings := bindings.push (fieldVars[i]!, field, true)
      if i < lastUsed then
        let tailV ← freshVarId s!"rest{i}"
        let tailExpr := MIR.Expr.App (mkBuiltin .TailList) currentList
        bindings := bindings.push (tailV, tailExpr, true)
        currentList := .Var tailV
    let mut result := body
    for i in [:bindings.size] do
      let (v, val, er) := bindings[bindings.size - 1 - i]!
      result := .Let [(v, val, er)] result
    pure result

  /-- Extract the builtin head from an application spine, ignoring `force`. -/
  private partial def extractBuiltinHead : MIR.Expr → Option BuiltinFun
    | .Builtin b => some b
    | .Force e => extractBuiltinHead e
    | _ => none

  /-- Recognize the narrow class of constructor-building expressions we can
      safely discard when they are passed to an unused lambda parameter in the
      direct data-match branch path. -/
  private partial def isCtorBuilderExpr : MIR.Expr → Bool
    | .Var _ | .Lit _ => true
    | .Constr _ args => args.all isCtorBuilderExpr
    | e =>
      let (head, args) := countAppArgs e
      match extractBuiltinHead head with
      | some .ConstrData => args.length == 2 && args.all isCtorBuilderExpr
      | some .IData | some .BData => args.length == 1 && args.all isCtorBuilderExpr
      | some .MkCons => args.length == 2 && args.all isCtorBuilderExpr
      | _ => false
  where
    countAppArgs : MIR.Expr → MIR.Expr × List MIR.Expr
      | .App f x =>
        let (head, args) := countAppArgs f
        (head, args ++ [x])
      | e => (e, [])

  /-- Simplify dead lambda applications that only rebuild constructors.
      This complements the direct branch-body translation by removing the
      residual artifact from elaborated wildcard branches before we decide
      which extracted fields are actually needed. -/
  private partial def simplifyDeadCtorApps : MIR.Expr → MIR.Expr
    | .App f x =>
      let f' := simplifyDeadCtorApps f
      let x' := simplifyDeadCtorApps x
      match f' with
      | .Lam v body =>
        let body' := simplifyDeadCtorApps body
        if MIR.countOccurrences v body' == 0 && isCtorBuilderExpr x' then
          body'
        else
          .App f' x'
      | _ => .App f' x'
    | .Lam v body => .Lam v (simplifyDeadCtorApps body)
    | .Fix v body => .Fix v (simplifyDeadCtorApps body)
    | .Force e => .Force (simplifyDeadCtorApps e)
    | .Delay e => .Delay (simplifyDeadCtorApps e)
    | .Constr tag args => .Constr tag (args.map simplifyDeadCtorApps)
    | .Case scrut alts => .Case (simplifyDeadCtorApps scrut) (alts.map simplifyDeadCtorApps)
    | .Let binds body =>
      .Let (binds.map fun (v, rhs, er) => (v, simplifyDeadCtorApps rhs, er))
        (simplifyDeadCtorApps body)
    | e => e

  /-- Fallback: extract all fields unconditionally.
      Used when the alt doesn't have the expected number of lambda binders. -/
  private partial def buildFieldExtractionAll (fieldCodecs : Array DataCodec)
      (alt : MIR.Expr) (fieldList : MIR.Expr) : TranslateM MIR.Expr := do
    let mut bindings : Array (MIR.VarId × MIR.Expr × Bool) := #[]
    let mut fieldVars : Array MIR.VarId := #[]
    let mut currentList := fieldList
    for i in [:fieldCodecs.size] do
      let headV ← freshVarId s!"f{i}"
      let rawHead := MIR.Expr.App (mkBuiltin .HeadList) currentList
      let field ← decodeFromData fieldCodecs[i]! rawHead
      bindings := bindings.push (headV, field, true)
      fieldVars := fieldVars.push headV
      if i + 1 < fieldCodecs.size then
        let tailV ← freshVarId s!"rest{i}"
        let tailExpr := MIR.Expr.App (mkBuiltin .TailList) currentList
        bindings := bindings.push (tailV, tailExpr, true)
        currentList := .Var tailV
    let mut body := alt
    for v in fieldVars do
      body := .App body (.Var v)
    let mut result := body
    for i in [:bindings.size] do
      let (v, val, er) := bindings[bindings.size - 1 - i]!
      result := .Let [(v, val, er)] result
    pure result

  /-- Build a chain of equalsInteger tag checks to dispatch to the right alternative. -/
  partial def buildTagDispatch (tag : MIR.Expr) (alts : Array MIR.Expr) (idx : Nat)
      : TranslateM MIR.Expr := do
    if alts.size == 0 then
      return .Error
    if alts.size == 1 then
      return alts[0]!
    if idx >= alts.size - 1 then
      return alts[alts.size - 1]!
    -- Case (equalsInteger tag idx) [restDispatch, alts[idx]]
    -- Bool.casesOn: [false, true] = [index 0, index 1]
    -- equalsInteger returns true (constr 1) when equal
    let rest ← buildTagDispatch tag alts (idx + 1)
    let check := MIR.Expr.App (.App (mkBuiltin .EqualsInteger) tag)
      (.Lit (.Integer idx, .AtomicType .TypeInteger))
    -- Case dispatch: [false branch = rest, true branch = current alt]
    pure (.Case check [rest, alts[idx]!])

  partial def translateIntOfNat (args : Array Lean.Expr) : TranslateM MIR.Expr := do
    if args.size == 0 then
      throwError "Int.ofNat: expected argument"
    let natArg := args[args.size - 1]!
    -- Try to evaluate as a Nat literal
    if let some n := evalNatLit natArg then
      return .Lit (.Integer n, .AtomicType .TypeInteger)
    -- Try whnf
    if !natArg.hasLooseBVars then
      let natVal ← whnf natArg
      if let some n := evalNatLit natVal then
        return .Lit (.Integer n, .AtomicType .TypeInteger)
    -- Dynamic case: Nat and Int are both Integer in Plutus
    translateExpr natArg

  partial def translateIntNegSucc (args : Array Lean.Expr) : TranslateM MIR.Expr := do
    if args.size == 0 then
      throwError "Int.negSucc: expected argument"
    let natArg := args[args.size - 1]!
    if let some n := evalNatLit natArg then
      return .Lit (.Integer (-(↑n + 1 : Int)), .AtomicType .TypeInteger)
    if !natArg.hasLooseBVars then
      let natVal ← whnf natArg
      if let some n := evalNatLit natVal then
        return .Lit (.Integer (-(↑n + 1 : Int)), .AtomicType .TypeInteger)
    -- Dynamic negSucc: subtractInteger (negate x) 1
    let x ← translateExpr natArg
    pure (.App (.App (mkBuiltin .SubtractInteger)
      (.App (.App (mkBuiltin .SubtractInteger) (.Lit (.Integer 0, .AtomicType .TypeInteger))) x))
      (.Lit (.Integer 1, .AtomicType .TypeInteger)))

  /-- Peel type-level lambdas from an expression, erasing them. -/
  partial def peelTypeLambdas (e : Lean.Expr) : TranslateM Lean.Expr := do
    match e with
    | .lam _ ty body bi =>
      if ← isErasableBinder ty bi then
        peelTypeLambdas (body.instantiate1 (.const ``Unit.unit []))
      else pure e
    | _ => pure e

  /-- Handle WellFounded.fix for recursive definitions.
      Extracts the body function F, sets up Fix node, and strips proof
      arguments from recursive calls. -/
  partial def translateWellFoundedFix (fnHead : Lean.Expr) (args : Array Lean.Expr) : TranslateM MIR.Expr := do
    -- Collect non-erased args from WellFounded.fix application
    let mut relevantArgs : Array Lean.Expr := #[]
    let mut currentFn := fnHead
    for arg in args do
      let erase ← if currentFn.hasLooseBVars then pure false
        else try
          let fTy ← inferType currentFn
          match fTy with
          | .forallE _ paramTy _ bi => isErasableBinder paramTy bi
          | _ => pure false
        catch _ => pure false
      if !erase then
        relevantArgs := relevantArgs.push arg
      currentFn := .app currentFn arg

    if relevantArgs.size == 0 then
      throwError "WellFounded.fix: no body function found"

    -- First relevant arg is F (the body function)
    let bodyFn := relevantArgs[0]!

    -- Peel type-level lambdas from F
    let bodyFnStripped ← peelTypeLambdas bodyFn

    -- F should be: fun n a => body
    -- n = value parameter, a = recursive function
    match bodyFnStripped with
    | .lam name1 _ty1 inner _bi1 =>
      match inner with
      | .lam _name2 _ty2 body _bi2 =>
        let nVar ← freshVarId name1.toString
        let recVar ← freshVarId "rec"
        -- Translate body with recFnVar set to strip proof args from recursive calls
        let body' ← withReader (fun ctx => { ctx with recFnVar := some recVar })
          (withLocal nVar (withLocal recVar (translateExpr body)))
        let mut result := MIR.Expr.Fix recVar (.Lam nVar body')
        -- Apply remaining args (if WellFounded.fix was fully applied)
        for i in [1:relevantArgs.size] do
          let argMir ← translateExpr relevantArgs[i]!
          result := .App result argMir
        pure result
      | _ =>
        throwError "WellFounded.fix: body function needs at least two lambdas"
    | _ =>
      throwError "WellFounded.fix: expected lambda body function"

  partial def translateAppDirect (e : Lean.Expr) : TranslateM MIR.Expr := do
    let (fn, args) := uncurryApp e
    let env ← getEnv

    -- Special case: constructor application with arguments
    if let .const name _ := fn then
      if let some (.ctorInfo cval) := env.find? name then
        -- Skip Int constructors (handled in translateApp)
        unless name == ``Int.ofNat || name == ``Int.negSucc do
          -- UPLC builtin type constructors bypass SOP/Data encoding
          if let some kind := builtinTypeKind cval.induct then
            -- Collect non-erased arguments (but keep raw args for type inspection)
            -- Pre-compute erasure mask from the constructor's declared type
            -- (avoids shouldEraseArg failures when currentFn has loose bvars)
            let mut eraseMask : Array Bool := #[]
            let mut ctorTy := cval.type
            for _ in args do
              match ctorTy with
              | .forallE _ paramTy body bi =>
                eraseMask := eraseMask.push (← isErasableBinder paramTy bi)
                ctorTy := body
              | _ => eraseMask := eraseMask.push false
            let mut valueArgs : Array MIR.Expr := #[]
            for i in [:args.size] do
              let erase := if h : i < eraseMask.size then eraseMask[i] else false
              if !erase then
                valueArgs := valueArgs.push (← translateExpr args[i]!)

            match kind with
            | .bool =>
              return .Lit (.Bool (cval.cidx == 1), .AtomicType .TypeBool)
            | .unit =>
              return .Lit (.Unit, .AtomicType .TypeUnit)
            | .list =>
              if cval.cidx == 0 then
                -- List.nil → constant empty list with correct element type
                let elemType ← if args.size > 0 then
                  match ← leanTypeToBuiltinType args[0]! with
                  | some bt => pure bt
                  | none => pure (.AtomicType .TypeData)
                else pure (.AtomicType .TypeData)
                return emptyListLit elemType
              else
                -- List.cons head tail → try constant folding, else MkCons
                if valueArgs.size == 2 then
                  match foldListCons valueArgs[0]! valueArgs[1]! with
                  | some folded => return folded
                  | none => return .App (.App (mkBuiltin .MkCons) valueArgs[0]!) valueArgs[1]!
                else
                  throwError "List.cons: expected 2 value arguments, got {valueArgs.size}"
            | .pair =>
              -- Prod.mk fst snd → try constant folding, else MkPairData
              if valueArgs.size == 2 then
                return .App (.App (.Builtin .MkPairData) valueArgs[0]!) valueArgs[1]!
              else
                throwError "Prod.mk: expected 2 value arguments, got {valueArgs.size}"
          let repr := getPlutusRepr env cval.induct
          let mut valueArgs : Array MIR.Expr := #[]
          let mut valueArgExprs : Array Lean.Expr := #[]
          let mut currentFn := fn
          for arg in args do
            let erase ← shouldEraseArg currentFn
            if !erase then
              let arg' ← translateExpr arg
              valueArgs := valueArgs.push arg'
              valueArgExprs := valueArgExprs.push arg
            currentFn := .app currentFn arg
          if repr == .sop then
            -- Transparent newtype: single-constructor, single-value-field,
            -- no explicit @[plutus_sop] → erase the wrapper
            let numCtors := match env.find? cval.induct with
              | some (.inductInfo iv) => iv.ctors.length
              | _ => 0
            if numCtors == 1 && valueArgs.size == 1 && !plutusSopAttr.hasTag env cval.induct then
              return valueArgs[0]!
            return .Constr cval.cidx valueArgs.toList
          else
            -- Data encoding: constrData tag (mkCons (toData f0) (mkCons (toData f1) ... mkNilData))
            let numParams := match env.find? cval.induct with
              | some (.inductInfo iv) => iv.numParams
              | _ => 0
            let typeArgs := args.extract 0 numParams
            let fieldTypes ← getCtorFieldTypesWithArgs env name numParams typeArgs
            let fieldCodecs ← resolveFieldCodecs fieldTypes s!"constructor '{name}'"
            let mut wrappedArgs : List MIR.Expr := []
            for i in [:valueArgs.size] do
              let codec := if h : i < fieldCodecs.size then fieldCodecs[i] else .identity
              wrappedArgs := wrappedArgs ++ [← encodeToData codec valueArgs[i]!]
            let dataList := mkDataList wrappedArgs
            return .App (.App (mkBuiltin .ConstrData)
              (.Lit (.Integer cval.cidx, .AtomicType .TypeInteger))) dataList

    -- Collect non-erased arguments
    let mut relevantArgs : Array Lean.Expr := #[]
    let mut currentFn := fn
    for arg in args do
      let mut erase ← shouldEraseArg currentFn
      -- Fallback: when shouldEraseArg fails (function has loose bvars),
      -- check if the argument's head constant is a proof (type is Prop).
      -- This catches proof args threaded through WellFounded.fix match branches.
      if !erase then
        let head := arg.getAppFn
        if let .const _ _ := head then
          if !head.hasLooseBVars then
            erase ← try
              let headTy ← inferType head
              isProp headTy
            catch _ => pure false
      if !erase then
        relevantArgs := relevantArgs.push arg
      currentFn := .app currentFn arg

    -- Translate the function
    let fn' ← translateExpr fn

    -- Check for recursive call (strip proof args from WellFounded.fix rec fn)
    let ctx ← read
    if let some recV := ctx.recFnVar then
      if let .Var v := fn' then
        if v == recV then
          -- Recursive call: keep only the first relevant arg (value), drop proofs
          if relevantArgs.size >= 1 then
            let arg' ← translateExpr relevantArgs[0]!
            return .App fn' arg'
          else
            return fn'

    -- Translate relevant args and fold into applications
    let mut result := fn'
    for arg in relevantArgs do
      let arg' ← translateExpr arg
      result := .App result arg'
    pure result

  partial def translateConst (name : Name) : TranslateM MIR.Expr := do
    let ctx ← read
    -- 1. Check builtin map
    if let some b := lookupBuiltin name then
      return mkBuiltin b
    -- 2. Check for self-recursive reference
    if ctx.unfolding.contains name then
      if ctx.selfName == some name then
        match ctx.selfVar with
        | some v => return .Var v
        | none => throwError "recursive reference to {name} but no Fix binder"
      else
        throwError "mutually recursive constant {name} detected (not yet supported)"
    -- 3. Look up and unfold
    let env ← getEnv
    match env.find? name with
    | some ci =>
      match ci.value? with
      | some val =>
        if let some sunfoldVal := smartUnfoldingValue? env name then
          let fVar ← freshVarId name.toString
          let body ← withReader (fun ctx => { ctx with
            unfolding := ctx.unfolding.insert name
            selfName := some name
            selfVar := some fVar
            maxDepth := ctx.maxDepth - 1
          }) (translateExpr sunfoldVal)
          pure (.Fix fVar body)
        else if let some recName := explicitRecursorName? val then
          throwError (explicitRecursorCompileError name recName)
        else
          if exprContainsConst val name then
            -- Check if this definition is self-recursive.
            -- Set up Fix for recursive definition.
            let fVar ← freshVarId name.toString
            let body ← withReader (fun ctx => { ctx with
              unfolding := ctx.unfolding.insert name
              selfName := some name
              selfVar := some fVar
              maxDepth := ctx.maxDepth - 1
            }) (translateExpr val)
            pure (.Fix fVar body)
          else
            withUnfolding name (translateExpr val)
      | none =>
        -- Constructor?
        if let some (.ctorInfo cval) := env.find? name then
          -- UPLC builtin type constructors (nullary: Bool, Unit, List.nil)
          if let some kind := builtinTypeKind cval.induct then
            match kind with
            | .bool => return .Lit (.Bool (cval.cidx == 1), .AtomicType .TypeBool)
            | .unit => return .Lit (.Unit, .AtomicType .TypeUnit)
            | .list =>
              if cval.cidx == 0 then  -- nil (no type info → default to list data)
                return emptyListLit (.AtomicType .TypeData)
              else  -- cons without args: return partially-applied MkCons
                return mkBuiltin .MkCons
            | .pair => return mkBuiltin .MkPairData  -- partial application
          let repr := getPlutusRepr env cval.induct
          if repr == .sop then
            pure (.Constr cval.cidx [])
          else
            -- Data encoding: constrData tag []
            pure (.App (.App (mkBuiltin .ConstrData)
              (.Lit (.Integer cval.cidx, .AtomicType .TypeInteger)))
              (.Lit (.ConstDataList [], .TypeOperator (.TypeList (.AtomicType .TypeData)))))
        else
          -- Check if this is an inductive type name (should have been erased as a type)
          if let some (.inductInfo _) := env.find? name then
            return .Error
          else if let some (.recInfo _) := env.find? name then
            -- Explicit recursors are rejected before translation reaches here.
            return .Error
          else
            throwError "cannot compile {name}: no definition body (axiom or opaque)"
    | none => throwError "unknown constant: {name}"
end

/-- Run the translation on a definition's body. -/
def translateDef (val : Lean.Expr) (freshStart : Nat := 0) : MetaM MIR.Expr := do
  let ctx : TranslateCtx := {
    locals := []
    unfolding := {}
    maxDepth := 200
  }
  let state : TranslateState := { nextFresh := freshStart }
  let (result, _) ← (translateExpr val).run ctx |>.run state
  pure result

/-- Translate a named definition. Prefer the smart-unfolding equation when Lean
    generated one; otherwise reject explicit recursors and compile the body
    directly. -/
def translateDefByName (name : Name) (val : Lean.Expr)
    (freshStart : Nat := 0) : MetaM MIR.Expr := do
  let env ← getEnv
  let selfVar : MIR.VarId := ⟨freshStart, name.toString⟩
  let namedCtx : TranslateCtx := {
    locals := []
    unfolding := .insert {} name
    maxDepth := 200
    selfName := some name
    selfVar := some selfVar
  }
  if let some sunfoldVal := smartUnfoldingValue? env name then
    let state : TranslateState := { nextFresh := freshStart + 1 }
    let (body, _) ← (translateExpr sunfoldVal).run namedCtx |>.run state
    return .Fix selfVar body
  if let some recName := explicitRecursorName? val then
    throwError (explicitRecursorCompileError name recName)
  translateDef val freshStart

end Moist.Onchain
