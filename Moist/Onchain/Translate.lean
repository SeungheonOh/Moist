import Lean
import Moist.MIR.Expr
import Moist.MIR.Analysis
import Moist.Onchain.Builtins
import Moist.Onchain.Attribute

namespace Moist.Onchain

open Lean Meta
open Moist.Plutus.Term (BuiltinFun Const BuiltinType AtomicType)

/-! # Lean Expr → MIR Translation

Translates Lean kernel expressions to MIR.
Type and proof arguments are detected and skipped during translation.
Constants are resolved via the builtin map or unfolded transitively.
-/

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

/-- Determine how to wrap a value as Data based on its Lean type name.
    Returns the BuiltinFun to apply, or none if the value is already Data. -/
private def toDataWrapper (env : Environment) (ty : Lean.Expr) : Option BuiltinFun :=
  match ty with
  | .const n _ =>
    if n == ``Int then some .IData
    else if n == ``PlutusCore.ByteString.ByteString then some .BData
    else if n == ``PlutusCore.Data.Data then none
    else if plutusDataAttr.hasTag env n then none  -- already Data
    else none  -- default: assume Data
  | .app (.const ``List _) (.const ``PlutusCore.Data.Data _) => some .ListData
  | _ => none

/-- Determine how to unwrap a Data value to a field type.
    Returns the BuiltinFun to apply, or none if identity. -/
private def fromDataWrapper (env : Environment) (ty : Lean.Expr) : Option BuiltinFun :=
  match ty with
  | .const n _ =>
    if n == ``Int then some .UnIData
    else if n == ``PlutusCore.ByteString.ByteString then some .UnBData
    else if n == ``PlutusCore.Data.Data then none
    else if plutusDataAttr.hasTag env n then none
    else none
  | .app (.const ``List _) (.const ``PlutusCore.Data.Data _) => some .UnListData
  | _ => none

/-- Get the non-erased field types for a constructor.
    Skips numParams parameters and returns remaining non-erasable field types. -/
private def getCtorFieldTypes (env : Environment) (ctorName : Name) (numParams : Nat)
    : MetaM (Array Lean.Expr) := do
  match env.find? ctorName with
  | some (.ctorInfo cval) =>
    let mut fields : Array Lean.Expr := #[]
    let mut ty := cval.type
    let mut paramIdx := 0
    -- Skip through all forallE binders
    while ty.isForall do
      match ty with
      | .forallE _ dom body bi =>
        if paramIdx < numParams then
          -- Parameter: skip
          ty := body.instantiate1 (.const ``Unit.unit [])
          paramIdx := paramIdx + 1
        else
          let erase ← isErasableBinder dom bi
          if !erase then
            fields := fields.push dom
          ty := body.instantiate1 (.const ``Unit.unit [])
      | _ => break
    pure fields
  | _ => pure #[]

/-- Wrap a MIR expression in a Data encoder if needed. -/
private def wrapToData (env : Environment) (fieldTy : Lean.Expr) (val : MIR.Expr) : MIR.Expr :=
  match toDataWrapper env fieldTy with
  | some b => .App (.Builtin b) val
  | none => val

/-- Wrap a MIR expression in a Data decoder if needed. -/
private def wrapFromData (env : Environment) (fieldTy : Lean.Expr) (val : MIR.Expr) : MIR.Expr :=
  match fromDataWrapper env fieldTy with
  | some b => .App (.Builtin b) val
  | none => val

/-- Build a Data list from field values: mkCons f0 (mkCons f1 ... mkNilData) -/
private def mkDataList (fields : List MIR.Expr) : MIR.Expr :=
  fields.foldr (init := .App (.Builtin .MkNilData) (.Lit (.Integer 0, .AtomicType .TypeInteger)))
    fun f acc => .App (.App (.Builtin .MkCons) f) acc

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

/-- Eta-reduce a Lean casesOn alternative expression.
    Detects `fun a b c d => f a b c d` (where f doesn't reference a,b,c,d)
    and reduces it to `f`. This exposes the actual match body to
    `buildFieldExtraction` so it can detect unused wildcard fields.

    In de Bruijn notation with n lambda binders, the full eta pattern is:
      `lam. lam. ... lam. (bvar n) (bvar (n-1)) ... (bvar 0)`
    where the head bvar n refers to the outer scope. After eta reduction,
    this becomes `bvar 0` (shifted down by n). -/
private def etaReduceLeanAlt (e : Lean.Expr) : Lean.Expr :=
  -- Peel all leading lambda binders
  let rec peelLam (e : Lean.Expr) (n : Nat) : Nat × Lean.Expr :=
    match e with
    | .lam _ _ body _ => peelLam body (n + 1)
    | _ => (n, e)
  let (nLams, body) := peelLam e 0
  if nLams == 0 then e
  else
  -- Check if body is `head (bvar (n-1)) (bvar (n-2)) ... (bvar 0)`
  let rec peelTrailingBvars (e : Lean.Expr) (expected : Nat) : Option (Lean.Expr × Nat) :=
    match e with
    | .app fn (.bvar i) =>
      if i == expected then peelTrailingBvars fn (expected + 1)
      else some (e, expected)
    | _ => some (e, expected)
  match peelTrailingBvars body 0 with
  | some (head, nEta) =>
    if nEta != nLams then e
    else
    -- Full eta: fun x0 ... x_{n-1} => head x0 ... x_{n-1}
    -- head must not reference any lambda-bound var (bvar indices 0..n-1).
    -- Since we're inside n lambdas, outer refs have index >= n.
    -- After removing the lambdas, we shift all bvar indices down by n.
    if !head.hasLooseBVars then
      -- head is closed (e.g. a const) — safe to eta-reduce
      head
    else
      -- Check all bvars in head are >= nLams (outer scope only)
      let range := head.looseBVarRange
      if range <= nLams then
        -- looseBVarRange <= nLams means max bvar < nLams, so head DOES
        -- reference lambda-bound vars — can't eta-reduce
        e
      else
        -- All bvars >= nLams. Shift down by nLams.
        -- But we need to verify NO bvar < nLams exists. looseBVarRange only
        -- gives the max. For safety, only handle the common case: head is
        -- a single bvar.
        match head with
        | .bvar i =>
          if i >= nLams then .bvar (i - nLams)
          else e
        | _ =>
          -- General case: use Lean's lowerLooseBVars
          -- lowerLooseBVars s n subtracts n from all bvars >= s
          -- We want to subtract nLams from all bvars >= nLams
          head.lowerLooseBVars nLams nLams
  | none => e

/-- Peel leading Lam binders from a MIR expression, up to `n` layers. -/
private def peelLambdas (e : MIR.Expr) (n : Nat) : Array MIR.VarId × MIR.Expr :=
  go e n #[]
where
  go : MIR.Expr → Nat → Array MIR.VarId → Array MIR.VarId × MIR.Expr
    | .Lam x body, n+1, acc => go body n (acc.push x)
    | e, _, acc => (acc, e)

mutual
  partial def translateExpr (e : Lean.Expr) : TranslateM MIR.Expr := do
    let ctx ← read
    if ctx.maxDepth == 0 then
      throwError "translation depth exceeded (probable infinite unfolding)"
    match e with
    | .bvar i =>
      match ctx.locals.get? i with
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
        pure (.Let [(v, val')] body')

    | .lit (.natVal n) =>
      pure (.Lit (.Integer n, .AtomicType .TypeInteger))

    | .lit (.strVal s) =>
      pure (.Lit (.String s, .AtomicType .TypeString))

    | .proj _typeName _idx _struct => do
      if e.hasLooseBVars then
        throwError "cannot translate projection with loose bvars: {e}"
      let e' ← whnf e
      if e' != e then translateExpr e'
      else throwError "cannot translate projection: {e}"

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
        let resolved ← resolveToBuiltin prefixExpr 20
        if let some reduced := resolved then
          -- Only use the result if it actually changed the expression
          if reduced != prefixExpr then
            let remainingArgs := args.extract nConsumed args.size
            let fullReduced := remainingArgs.foldl (init := reduced) fun acc a => .app acc a
            return ← translateExpr fullReduced.headBeta
    -- Translate directly
    translateAppDirect e

  partial def translateCasesOn (caseName : Name) (args : Array Lean.Expr)
      : TranslateM MIR.Expr := do
    let typeName := caseName.getPrefix
    let env ← getEnv
    match env.find? typeName with
    | some (.inductInfo iv) =>
      let repr := getPlutusRepr env typeName
      let np := iv.numParams
      -- casesOn layout: [params...] [motive] [scrutinee] [alts...]
      let scrutIdx := np + 1
      if h : scrutIdx < args.size then
        let scrut ← translateExpr args[scrutIdx]
        let altsStart := scrutIdx + 1
        let numAlts := iv.ctors.length
        if repr == .sop then
          -- SOP encoding: direct Constr/Case
          let mut alts : List MIR.Expr := []
          for i in [:numAlts] do
            if h2 : altsStart + i < args.size then
              let alt ← translateExpr args[altsStart + i]
              alts := alts ++ [alt]
            else
              throwError "casesOn for {typeName}: not enough alternatives"
          pure (.Case scrut alts)
        else
          -- Data encoding: unConstrData + tag dispatch + field extraction
          translateDataCasesOn env iv np scrut args altsStart numAlts
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
      (numParams : Nat) (scrut : MIR.Expr)
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
        let altExpr := etaReduceLeanAlt (args[altsStart + i])
        let ctorName := iv.ctors[i]!
        let fieldTypes ← getCtorFieldTypes env ctorName numParams
        let altMir ← translateExpr altExpr
        -- Extract fields from fieldList and apply to altMir
        let body ← buildFieldExtraction env fieldTypes altMir (.Var fieldsV)
        altBodies := altBodies.push body
      else
        throwError "data casesOn for {iv.name}: not enough alternatives"
    -- Build tag dispatch: chain of equalsInteger checks
    let dispatch ← buildTagDispatch (.Var tagV) altBodies 0
    -- Wrap in let bindings
    pure (.Let [(pairV, .App (.Builtin .UnConstrData) scrut)]
      (.Let [(tagV, .App (.Builtin .FstPair) (.Var pairV))]
        (.Let [(fieldsV, .App (.Builtin .SndPair) (.Var pairV))]
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
  partial def buildFieldExtraction (env : Environment) (fieldTypes : Array Lean.Expr)
      (alt : MIR.Expr) (fieldList : MIR.Expr) : TranslateM MIR.Expr := do
    if fieldTypes.size == 0 then return alt
    -- Peel lambda binders to detect which fields are actually used
    let (params, innerBody) := peelLambdas alt fieldTypes.size
    -- If we can't peel the expected number of lambdas, fall back to extracting all
    if params.size != fieldTypes.size then
      return ← buildFieldExtractionAll env fieldTypes alt fieldList
    -- Determine which fields are used in the body
    let usedMask : Array Bool := params.map fun p =>
      MIR.countOccurrences p innerBody > 0
    -- Find the last used field index (to know how far to traverse the list)
    let mut lastUsed? : Option Nat := none
    for i in [:fieldTypes.size] do
      if usedMask[i]! then lastUsed? := some i
    -- If no fields are used, return just the inner body
    let some lastUsed := lastUsed? | return innerBody
    -- Build field extraction bindings, skipping unused fields
    let mut bindings : Array (MIR.VarId × MIR.Expr) := #[]
    let mut usedFieldVars : Array MIR.VarId := #[]
    let mut currentList := fieldList
    for i in [:lastUsed + 1] do
      if usedMask[i]! then
        let headV ← freshVarId s!"f{i}"
        let rawHead := MIR.Expr.App (.Builtin .HeadList) currentList
        let field := wrapFromData env fieldTypes[i]! rawHead
        bindings := bindings.push (headV, field)
        usedFieldVars := usedFieldVars.push headV
      -- Advance list pointer if not at the last needed position
      if i < lastUsed then
        let tailV ← freshVarId s!"rest{i}"
        let tailExpr := MIR.Expr.App (.Builtin .TailList) currentList
        bindings := bindings.push (tailV, tailExpr)
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
      let (v, val) := bindings[bindings.size - 1 - i]!
      result := .Let [(v, val)] result
    pure result

  /-- Fallback: extract all fields unconditionally.
      Used when the alt doesn't have the expected number of lambda binders. -/
  private partial def buildFieldExtractionAll (env : Environment) (fieldTypes : Array Lean.Expr)
      (alt : MIR.Expr) (fieldList : MIR.Expr) : TranslateM MIR.Expr := do
    let mut bindings : Array (MIR.VarId × MIR.Expr) := #[]
    let mut fieldVars : Array MIR.VarId := #[]
    let mut currentList := fieldList
    for i in [:fieldTypes.size] do
      let headV ← freshVarId s!"f{i}"
      let rawHead := MIR.Expr.App (.Builtin .HeadList) currentList
      let field := wrapFromData env fieldTypes[i]! rawHead
      bindings := bindings.push (headV, field)
      fieldVars := fieldVars.push headV
      if i + 1 < fieldTypes.size then
        let tailV ← freshVarId s!"rest{i}"
        let tailExpr := MIR.Expr.App (.Builtin .TailList) currentList
        bindings := bindings.push (tailV, tailExpr)
        currentList := .Var tailV
    let mut body := alt
    for v in fieldVars do
      body := .App body (.Var v)
    let mut result := body
    for i in [:bindings.size] do
      let (v, val) := bindings[bindings.size - 1 - i]!
      result := .Let [(v, val)] result
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
    let check := MIR.Expr.App (.App (.Builtin .EqualsInteger) tag)
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
    pure (.App (.App (.Builtin .SubtractInteger)
      (.App (.App (.Builtin .SubtractInteger) (.Lit (.Integer 0, .AtomicType .TypeInteger))) x))
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
            return .Constr cval.cidx valueArgs.toList
          else
            -- Data encoding: constrData tag (mkCons (toData f0) (mkCons (toData f1) ... mkNilData))
            let fieldTypes ← getCtorFieldTypes env name
              (match env.find? cval.induct with
               | some (.inductInfo iv) => iv.numParams
               | _ => 0)
            let mut wrappedArgs : List MIR.Expr := []
            for i in [:valueArgs.size] do
              let fieldTy := if h : i < fieldTypes.size then fieldTypes[i] else default
              wrappedArgs := wrappedArgs ++ [wrapToData env fieldTy valueArgs[i]!]
            let dataList := mkDataList wrappedArgs
            return .App (.App (.Builtin .ConstrData)
              (.Lit (.Integer cval.cidx, .AtomicType .TypeInteger))) dataList

    -- Collect non-erased arguments
    let mut relevantArgs : Array Lean.Expr := #[]
    let mut currentFn := fn
    for arg in args do
      let erase ← shouldEraseArg currentFn
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
      return .Builtin b
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
        -- Check if this definition is self-recursive
        if exprContainsConst val name then
          -- Set up Fix for recursive definition
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
          let repr := getPlutusRepr env cval.induct
          if repr == .sop then
            pure (.Constr cval.cidx [])
          else
            -- Data encoding: constrData tag mkNilData
            pure (.App (.App (.Builtin .ConstrData)
              (.Lit (.Integer cval.cidx, .AtomicType .TypeInteger)))
              (.App (.Builtin .MkNilData) (.Lit (.Integer 0, .AtomicType .TypeInteger))))
        else
          throwError "cannot compile {name}: no definition body (axiom or opaque)"
    | none => throwError "unknown constant: {name}"
end

/-- Run the translation on a definition's body. -/
def translateDef (val : Lean.Expr) (freshStart : Nat := 0) : MetaM MIR.Expr := do
  let ctx : TranslateCtx := { locals := [], unfolding := {}, maxDepth := 200 }
  let state : TranslateState := { nextFresh := freshStart }
  let (result, _) ← (translateExpr val).run ctx |>.run state
  pure result

end Moist.Onchain
