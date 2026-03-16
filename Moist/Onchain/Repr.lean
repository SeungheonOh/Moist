import Lean
import Moist.Plutus.Types
import Moist.Onchain.PlutusData

namespace Moist.Onchain

open Lean Meta

/-! # Representation Resolution

Systematic resolution of Lean types to Plutus Data codec plans.
Includes declaration-time validation for @[plutus_data] types.
-/

/-- Whether an inductive uses SOP or Data encoding. -/
inductive PlutusRepr
  | sop
  | data
deriving Repr, BEq, DecidableEq, Inhabited

/-- How a value is encoded into / decoded from Data. -/
inductive DataCodec where
  | identity                         -- already Data
  | iData                            -- Int via IData/UnIData
  | bData                            -- ByteString via BData/UnBData
  | listData (elem : DataCodec)      -- List α via ListData/UnListData + element codec
  | mapData (key : DataCodec) (value : DataCodec) -- AssocMap via MapData/UnMapData + key/value codecs
  | constrData (typeName : Name)     -- @[plutus_data] type (already Data at runtime)
  | param (idx : Nat)                -- type parameter placeholder (resolved at instantiation)
deriving Repr, BEq, Inhabited

/-- Returns true if encoding/decoding is a no-op (value is already Data). -/
def DataCodec.isIdentity : DataCodec → Bool
  | .identity | .constrData _ => true
  | _ => false

/-- Why a type cannot be embedded in Data. -/
inductive DataCompatError where
  | sopType (typeName : Name)
  | functionType
  | boolType
  | unknownType (desc : String)
  | nestedError (context : String) (inner : DataCompatError)
deriving Repr

/-- Format a DataCompatError as a user-friendly message. -/
def formatDataCompatError : DataCompatError → String
  | .sopType n =>
    s!"type '{n}' uses SOP encoding and cannot be embedded in Data. \
       Hint: mark it with @[plutus_data]"
  | .functionType => "function types cannot be embedded in Data"
  | .boolType =>
    "Bool is not data-compatible. Define a @[plutus_data] inductive type instead"
  | .unknownType desc => s!"unknown type '{desc}' is not data-compatible"
  | .nestedError ctx inner => s!"{ctx}: {formatDataCompatError inner}"

/-! ## Param markers for parametric type validation -/

/-- Create a synthetic name used as a placeholder for type parameter `idx`. -/
private def mkParamMarkerName (idx : Nat) : Name :=
  .mkNum (.mkStr .anonymous "_moist_param") idx

/-- Detect a param marker name and return its index. -/
private def isParamMarker (n : Name) : Option Nat :=
  match n with
  | .num (.str .anonymous "_moist_param") idx => some idx
  | _ => none

/-! ## Forward reference for @[plutus_data] tag check

We use an IO.Ref to break the initialization cycle:
  resolveDataCodec needs plutusDataAttr.hasTag
  validatePlutusDataInductive needs resolveDataCodec
  plutusDataAttr validate callback needs validatePlutusDataInductive
-/

private initialize plutusDataTagRef : IO.Ref (Environment → Name → Bool) ←
  IO.mkRef (fun _ _ => false)

/-! ## Helper: type family detection -/

private def isTypeFamily : Lean.Expr → Bool
  | .sort _ => true
  | .forallE _ _ body _ => isTypeFamily body
  | _ => false

/-! ## Codec resolution -/

/-- Resolve the Data codec for a Lean type expression.
    Uses whnf to see through abbreviations (Lovelace → Int, PubKeyHash → ByteString, etc.).
    Fails with a structured error for unsupported types. -/
partial def resolveDataCodec (ty : Lean.Expr) : MetaM (Except DataCompatError DataCodec) := do
  let env ← getEnv
  let isPlutusData ← plutusDataTagRef.get
  let ty' ← whnf ty
  match ty' with
  | .const n _ =>
    if let some idx := isParamMarker n then return .ok (.param idx)
    else if n == ``Moist.Plutus.Data then return .ok .identity
    else if n == ``Int then return .ok .iData
    else if n == ``ByteArray then return .ok .bData
    else if isPlutusData env n then return .ok (.constrData n)
    else if n == ``Bool then return .error .boolType
    else
      match env.find? n with
      | some (.inductInfo _) => return .error (.sopType n)
      | _ => return .error (.unknownType (toString n))
  | .app _ _ =>
    let head := ty'.getAppFn
    let args := ty'.getAppArgs
    match head with
    | .const n _ =>
      if n == ``List then
        if h : 0 < args.size then
          match ← resolveDataCodec args[0] with
          | .ok elemCodec => return .ok (.listData elemCodec)
          | .error e => return .error (.nestedError "List element" e)
        else
          return .error (.unknownType "List with no type argument")
      else if n == ``Moist.Plutus.AssocMap then
        if h : 1 < args.size then
          match ← resolveDataCodec args[0], ← resolveDataCodec args[1] with
          | .ok keyCodec, .ok valCodec => return .ok (.mapData keyCodec valCodec)
          | .error e, _ => return .error (.nestedError "AssocMap key" e)
          | _, .error e => return .error (.nestedError "AssocMap value" e)
        else
          return .error (.unknownType "AssocMap with missing type arguments")
      else if isPlutusData env n then
        return .ok (.constrData n)
      else
        return .error (.unknownType (toString ty'))
    | _ => return .error (.unknownType (toString ty'))
  | .forallE _ _ _ _ => return .error .functionType
  | _ => return .error (.unknownType (toString ty'))

/-! ## Codec plans and caching -/

/-- Codec plan for a single constructor. -/
structure CtorCodecPlan where
  ctorName : Name
  tag : Nat
  fieldCodecs : Array DataCodec
deriving Repr, BEq, Inhabited

/-- Codec plan for an entire @[plutus_data] inductive. -/
structure InductiveCodecPlan where
  typeName : Name
  numParams : Nat
  ctors : Array CtorCodecPlan
deriving Repr, BEq, Inhabited

/-- Persistent extension caching validated codec plans. -/
initialize codecPlanExt : SimplePersistentEnvExtension (Name × InductiveCodecPlan)
    (NameMap InductiveCodecPlan) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, plan) => m.insert n plan
    addImportedFn := fun arrays =>
      arrays.foldl (init := {}) fun m a =>
        a.foldl (init := m) fun m (n, plan) => m.insert n plan
  }

/-- Look up a cached codec plan. -/
def getCodecPlan? (env : Environment) (typeName : Name) : Option InductiveCodecPlan :=
  (codecPlanExt.getState env).find? typeName

/-- Validate a @[plutus_data] inductive type and produce a codec plan.
    Type parameters are represented as `.param` markers in the plan. -/
def validatePlutusDataInductive (iv : InductiveVal) : MetaM InductiveCodecPlan := do
  let env ← getEnv
  let numParams := iv.numParams
  let mut ctorPlans : Array CtorCodecPlan := #[]
  for ctorName in iv.ctors do
    match env.find? ctorName with
    | some (.ctorInfo cval) =>
      let mut ty := cval.type
      let mut paramIdx := 0
      let mut fieldCodecs : Array DataCodec := #[]
      while ty.isForall do
        match ty with
        | .forallE _ dom body bi =>
          if paramIdx < numParams then
            ty := body.instantiate1 (.const (mkParamMarkerName paramIdx) [])
            paramIdx := paramIdx + 1
          else
            let erasable :=
              bi == .instImplicit || dom.isSort || isTypeFamily dom
            let erasable ← if erasable then pure true
              else if !dom.hasLooseBVars then
                try pure (← isProp dom) catch _ => pure false
              else pure false
            if !erasable then
              match ← resolveDataCodec dom with
              | .ok codec => fieldCodecs := fieldCodecs.push codec
              | .error e =>
                throwError "@[plutus_data] type '{iv.name}', constructor '{cval.name}' \
                  field {fieldCodecs.size}: {formatDataCompatError e}"
            ty := body.instantiate1 (.const ``Unit.unit [])
        | _ => break
      ctorPlans := ctorPlans.push {
        ctorName := ctorName
        tag := cval.cidx
        fieldCodecs := fieldCodecs
      }
    | _ => throwError "@[plutus_data] type '{iv.name}': constructor '{ctorName}' not found"
  return {
    typeName := iv.name
    numParams := numParams
    ctors := ctorPlans
  }

/-! ## PlutusData auto-derivation

Generate `PlutusData` and `BEq` instances from the codec plan.
Uses MetaM term construction which bypasses the `private mk` on PlutusData.
-/

open Moist.Plutus (Data ByteString)

/-- Encode a field value to a Data expression based on its codec. -/
private partial def mkEncodeFieldExpr (codec : DataCodec) (val : Lean.Expr) : MetaM Lean.Expr := do
  match codec with
  | .iData => pure <| mkApp (mkConst ``Data.I []) val
  | .bData => pure <| mkApp (mkConst ``Data.B []) val
  | .identity => pure val
  | .constrData _ | .param _ => mkAppM ``PlutusData.toData #[val]
  | .listData elemCodec =>
    if elemCodec.isIdentity then
      pure <| mkApp (mkConst ``Data.List []) val
    else
      -- Data.List (val.map (fun x => encodeField elemCodec x))
      let elemTy ← do
        let listTy ← inferType val
        let listTy' ← whnf listTy
        match listTy'.getAppArgs with
        | #[t] => pure t
        | _ => throwError "expected List type, got {listTy'}"
      withLocalDecl `x .default elemTy fun x => do
        let body ← mkEncodeFieldExpr elemCodec x
        let mapFn ← mkLambdaFVars #[x] body
        let mapped ← mkAppM ``List.map #[mapFn, val]
        pure <| mkApp (mkConst ``Data.List []) mapped
  | .mapData keyCodec valCodec =>
    if keyCodec.isIdentity && valCodec.isIdentity then
      -- AssocMap already has toList : List (k × v), just need Data.Map
      let pairs ← mkAppM ``Moist.Plutus.AssocMap.toList #[val]
      pure <| mkApp (mkConst ``Data.Map []) pairs
    else
      let pairList ← mkAppM ``Moist.Plutus.AssocMap.toList #[val]
      let pairListTy' ← inferType pairList
      let pairListTy'' ← whnf pairListTy'
      let pairTy ← match pairListTy''.getAppArgs with
        | #[t] => pure t
        | _ => throwError "expected List type from AssocMap.toList"
      let pairTy' ← whnf pairTy
      let (_, _) ← match pairTy'.getAppArgs with
        | #[k, v] => pure (k, v)
        | _ => throwError "expected Prod type, got {pairTy'}"
      withLocalDecl `p .default pairTy fun p => do
        let k ← mkAppM ``Prod.fst #[p]
        let v ← mkAppM ``Prod.snd #[p]
        let kEnc ← mkEncodeFieldExpr keyCodec k
        let vEnc ← mkEncodeFieldExpr valCodec v
        let pair ← mkAppM ``Prod.mk #[kEnc, vEnc]
        let mapFn ← mkLambdaFVars #[p] pair
        let mapped ← mkAppM ``List.map #[mapFn, pairList]
        pure <| mkApp (mkConst ``Data.Map []) mapped

/-- Decode a Data expression to a field value based on its codec.
    Uses `unsafeFromData` since we are inside a tag-matched constructor
    where the data shape is known to be valid.
    `targetTy` is the expected Lean type of the decoded value. -/
private partial def mkDecodeFieldExpr (codec : DataCodec) (val : Lean.Expr)
    (targetTy : Lean.Expr) : MetaM Lean.Expr := do
  match codec with
  | .identity => pure val
  | _ => mkAppOptM ``PlutusData.unsafeFromData #[some targetTy, none, some val]

/-- Build a Lean List Data expression from an array of Data expressions. -/
private def mkDataListExpr (elems : Array Lean.Expr) : MetaM Lean.Expr := do
  let dataTy := mkConst ``Data []
  let mut result := mkApp (mkConst ``List.nil [.zero]) dataTy
  for i in [:elems.size] do
    let idx := elems.size - 1 - i
    result ← mkAppM ``List.cons #[elems[idx]!, result]
  pure result

/-- Check if a codec references a given type parameter index. -/
private def usesParamCodec (idx : Nat) : DataCodec → Bool
  | .param i => i == idx
  | .listData c => usesParamCodec idx c
  | .mapData k v => usesParamCodec idx k || usesParamCodec idx v
  | _ => false

/-- Introduce `[PlutusData αᵢ]` instance constraints for type parameters
    used in `.param` codecs, then run `k` with the constraint fvars. -/
private def withParamConstraints [Inhabited α] (plan : InductiveCodecPlan)
    (paramFVars : Array Lean.Expr) (k : Array Lean.Expr → MetaM α)
    : MetaM α := do
  let mut instDecls : Array (Name × BinderInfo × (Array Lean.Expr → MetaM Lean.Expr)) := #[]
  for i in [:plan.numParams] do
    let needs := plan.ctors.any fun c =>
      c.fieldCodecs.any fun codec => usesParamCodec i codec
    if needs then
      let paramTy := paramFVars[i]!
      instDecls := instDecls.push
        (Name.mkNum `inst i, BinderInfo.instImplicit, fun _ => mkAppM ``PlutusData #[paramTy])
  if instDecls.isEmpty then k #[]
  else withLocalDecls instDecls k

/-- Get the non-erased field names for a structure constructor. -/
private def getStructFieldNames (env : Environment) (ctorName : Name)
    (numParams : Nat) : MetaM (Array Name) := do
  let some (.ctorInfo cval) := env.find? ctorName
    | throwError "constructor not found: {ctorName}"
  let mut names : Array Name := #[]
  let mut ty := cval.type
  let mut pIdx := 0
  while ty.isForall do
    match ty with
    | .forallE n dom body bi =>
      if pIdx < numParams then
        ty := body.instantiate1 (.const ``Unit.unit [])
        pIdx := pIdx + 1
      else
        let erasable := bi == .instImplicit || dom.isSort || isTypeFamily dom
        let erasable ← if erasable then pure true
          else if !dom.hasLooseBVars then
            try pure (← isProp dom) catch _ => pure false
          else pure false
        if !erasable then
          names := names.push n
        ty := body.instantiate1 (.const ``Unit.unit [])
    | _ => break
  return names

/-- Build the toData function body for a codec plan.
    Returns a lambda `α → Data`. -/
private def mkToDataBody (iv : InductiveVal) (plan : InductiveCodecPlan) : MetaM Lean.Expr := do
  let env ← getEnv
  let typeLvls := iv.levelParams.map Level.param
  let isStruct := iv.ctors.length == 1 && isStructure env iv.name

  forallBoundedTelescope iv.type plan.numParams fun paramFVars _ => do
    withParamConstraints plan paramFVars fun instFVars => do
      let indTyApp := mkAppN (mkConst iv.name typeLvls) paramFVars
      withLocalDecl `x .default indTyApp fun x => do
        let body ← if isStruct then
          -- Structure: use field projections directly
          let ctorPlan := plan.ctors[0]!
          let fieldNames ← getStructFieldNames env ctorPlan.ctorName plan.numParams
          let mut encodedFields : Array Lean.Expr := #[]
          for i in [:ctorPlan.fieldCodecs.size] do
            let projName := iv.name ++ fieldNames[i]!
            let proj := mkAppN (mkConst projName typeLvls) (paramFVars.push x)
            let encoded ← mkEncodeFieldExpr ctorPlan.fieldCodecs[i]! proj
            encodedFields := encodedFields.push encoded
          let tag := mkApp (mkConst ``Int.ofNat []) (mkNatLit ctorPlan.tag)
          let fieldList ← mkDataListExpr encodedFields
          pure <| mkApp2 (mkConst ``Data.Constr []) tag fieldList
        else do
          -- Multi-constructor inductive: use casesOn
          let dataTy := mkConst ``Data []
          let motive ← mkLambdaFVars #[x] dataTy
          let mut altExprs : Array Lean.Expr := #[]
          for ctorPlan in plan.ctors do
            let some (.ctorInfo cval) := env.find? ctorPlan.ctorName
              | throwError "constructor not found: {ctorPlan.ctorName}"
            let mut fieldTypes : Array Lean.Expr := #[]
            let mut ty := cval.type
            let mut pIdx := 0
            while ty.isForall do
              match ty with
              | .forallE _ dom body bi =>
                if pIdx < plan.numParams then
                  ty := body.instantiate1 paramFVars[pIdx]!
                  pIdx := pIdx + 1
                else
                  let erasable := bi == .instImplicit || dom.isSort || isTypeFamily dom
                  let erasable ← if erasable then pure true
                    else if !dom.hasLooseBVars then
                      try pure (← isProp dom) catch _ => pure false
                    else pure false
                  if !erasable then
                    fieldTypes := fieldTypes.push dom
                  ty := body.instantiate1 (.const ``Unit.unit [])
              | _ => break
            let mut decls : Array (Name × BinderInfo × (Array Lean.Expr → MetaM Lean.Expr)) := #[]
            for i in [:fieldTypes.size] do
              let fty := fieldTypes[i]!
              decls := decls.push (Name.mkNum `f i, BinderInfo.default, fun _ => pure fty)
            let altBody ← withLocalDecls decls fun fvars => do
              let mut encodedFields : Array Lean.Expr := #[]
              for i in [:fvars.size] do
                let codec := ctorPlan.fieldCodecs[i]!
                let encoded ← mkEncodeFieldExpr codec fvars[i]!
                encodedFields := encodedFields.push encoded
              let tag := mkApp (mkConst ``Int.ofNat []) (mkNatLit ctorPlan.tag)
              let fieldList ← mkDataListExpr encodedFields
              let constrExpr := mkApp2 (mkConst ``Data.Constr []) tag fieldList
              mkLambdaFVars fvars constrExpr
            altExprs := altExprs.push altBody
          let casesOnName := iv.name ++ `casesOn
          let casesOnLvls := (Level.succ .zero) :: typeLvls
          let mut casesOnArgs : Array Lean.Expr := #[]
          for p in paramFVars do casesOnArgs := casesOnArgs.push p
          casesOnArgs := casesOnArgs.push motive
          casesOnArgs := casesOnArgs.push x
          for alt in altExprs do casesOnArgs := casesOnArgs.push alt
          pure <| mkAppN (mkConst casesOnName casesOnLvls) casesOnArgs
        let lam ← mkLambdaFVars #[x] body
        mkLambdaFVars (paramFVars ++ instFVars) lam

/-- Build a fromData/unsafeFromData function body for a codec plan.
    Uses tag dispatch: match d with | Data.Constr tag fields => dispatch by tag.
    When `safe = true`, returns `Data → Option α` (wraps in `some`, defaults to `none`).
    When `safe = false`, returns `Data → α` (no wrapping, defaults to `Inhabited.default`/`sorry`). -/
private def mkFromDataBody (iv : InductiveVal) (plan : InductiveCodecPlan)
    (safe : Bool := true) : MetaM Lean.Expr := do
  let env ← getEnv
  let typeLvls := iv.levelParams.map Level.param

  forallBoundedTelescope iv.type plan.numParams fun paramFVars _ => do
    withParamConstraints plan paramFVars fun instFVars => do
      let indTyApp := mkAppN (mkConst iv.name typeLvls) paramFVars
      let retTy ← if safe then mkAppM ``Option #[indTyApp] else pure indTyApp
      let dataTy := mkConst ``Data []
      withLocalDecl `d .default dataTy fun d => do
        withLocalDecl `tag .default (mkConst ``Int []) fun tagVar =>
        withLocalDecl `fields .default (mkApp (mkConst ``List [.zero]) dataTy) fun fieldsVar => do
          let defaultExpr ← if safe then
            mkAppOptM ``Option.none #[some indTyApp]
          else
            mkUnsafeDefault indTyApp

          let mut dispatchBody := defaultExpr
          for i' in [:plan.ctors.size] do
            let i := plan.ctors.size - 1 - i'
            let ctorPlan := plan.ctors[i]!
            let some (.ctorInfo cval) := env.find? ctorPlan.ctorName
              | throwError "constructor not found: {ctorPlan.ctorName}"

            let mut fieldTypes : Array Lean.Expr := #[]
            let mut cty := cval.type
            let mut pIdx := 0
            while cty.isForall do
              match cty with
              | .forallE _ dom body bi =>
                if pIdx < plan.numParams then
                  cty := body.instantiate1 paramFVars[pIdx]!
                  pIdx := pIdx + 1
                else
                  let erasable := bi == .instImplicit || dom.isSort || isTypeFamily dom
                  let erasable ← if erasable then pure true
                    else if !dom.hasLooseBVars then
                      try pure (← isProp dom) catch _ => pure false
                    else pure false
                  if !erasable then
                    fieldTypes := fieldTypes.push dom
                  cty := body.instantiate1 (.const ``Unit.unit [])
              | _ => break

            let defaultData := mkApp (mkConst ``Data.I []) (mkApp (mkConst ``Int.ofNat []) (mkNatLit 0))
            let mut fieldExprs : Array Lean.Expr := #[]
            for j in [:ctorPlan.fieldCodecs.size] do
              let idx := mkNatLit j
              let rawField ← mkAppOptM ``List.getD #[some dataTy, some fieldsVar, some idx, some defaultData]
              let decoded ← mkDecodeFieldExpr ctorPlan.fieldCodecs[j]! rawField fieldTypes[j]!
              fieldExprs := fieldExprs.push decoded

            let mut ctorApp := mkConst ctorPlan.ctorName typeLvls
            for p in paramFVars do ctorApp := mkApp ctorApp p
            for fe in fieldExprs do ctorApp := mkApp ctorApp fe

            -- Wrap in `some` for safe mode
            let result ← if safe then
              mkAppM ``Option.some #[ctorApp]
            else pure ctorApp

            let tagLit := mkApp (mkConst ``Int.ofNat []) (mkNatLit ctorPlan.tag)
            let cond ← mkAppM ``BEq.beq #[tagVar, tagLit]
            dispatchBody ← mkAppM ``cond #[cond, result, dispatchBody]

          let constrBranch ← mkLambdaFVars #[tagVar, fieldsVar] dispatchBody
          let mapDummy ← withLocalDecl `m .default (mkApp (mkConst ``List [.zero])
              (mkApp2 (mkConst ``Prod [.zero, .zero]) dataTy dataTy)) fun v =>
            mkLambdaFVars #[v] defaultExpr
          let listDummy ← withLocalDecl `l .default (mkApp (mkConst ``List [.zero]) dataTy) fun v =>
            mkLambdaFVars #[v] defaultExpr
          let iDummy ← withLocalDecl `i .default (mkConst ``Int []) fun v =>
            mkLambdaFVars #[v] defaultExpr
          let bDummy ← withLocalDecl `b .default (mkConst ``Moist.Plutus.ByteString []) fun v =>
            mkLambdaFVars #[v] defaultExpr

          let motive ← mkLambdaFVars #[d] retTy
          let casesOnLvls := [Level.succ .zero]
          let body := mkAppN (mkConst ``Data.casesOn casesOnLvls)
            #[motive, d, constrBranch, mapDummy, listDummy, iDummy, bDummy]
          let lam ← mkLambdaFVars #[d] body
          mkLambdaFVars (paramFVars ++ instFVars) lam
where
  mkUnsafeDefault (ty : Lean.Expr) : MetaM Lean.Expr := do
    try
      mkAppOptM ``Inhabited.default #[some ty, none]
    catch _ =>
      mkSorry ty false

/-- Derive and register a PlutusData instance for the given inductive type. -/
def derivePlutusDataInstance (iv : InductiveVal) (plan : InductiveCodecPlan) : MetaM Unit := do
  let typeLvls := iv.levelParams.map Level.param
  let lvlParams := iv.levelParams

  forallBoundedTelescope iv.type plan.numParams fun paramFVars _ => do
    withParamConstraints plan paramFVars fun instFVars => do
      let indTyApp := mkAppN (mkConst iv.name typeLvls) paramFVars
      let allFVars := paramFVars ++ instFVars

      -- Generate Inhabited instance (needed for unsafeFromData fallback)
      let inhabInstName := iv.name ++ `instInhabited
      let hasInhabited ← try
        let _ ← mkAppOptM ``Inhabited.default #[some indTyApp, none]
        pure true
      catch _ => pure false
      if !hasInhabited then do
        -- Build default from first constructor using Inhabited.default for each field
        let firstCtor := plan.ctors[0]!
        let env ← getEnv
        let some (.ctorInfo cval) := env.find? firstCtor.ctorName
          | throwError "constructor not found: {firstCtor.ctorName}"
        let mut inhabBody := mkConst firstCtor.ctorName typeLvls
        for p in paramFVars do inhabBody := mkApp inhabBody p
        let mut cty := cval.type
        let mut pIdx := 0
        while cty.isForall do
          match cty with
          | .forallE _ dom body bi =>
            if pIdx < plan.numParams then
              cty := body.instantiate1 paramFVars[pIdx]!
              pIdx := pIdx + 1
            else
              let erasable := bi == .instImplicit || dom.isSort || isTypeFamily dom
              let erasable ← if erasable then pure true
                else if !dom.hasLooseBVars then
                  try pure (← isProp dom) catch _ => pure false
                else pure false
              if !erasable then
                let fieldDefault ← mkAppOptM ``Inhabited.default #[some dom, none]
                inhabBody := mkApp inhabBody fieldDefault
              cty := body.instantiate1 (.const ``Unit.unit [])
          | _ => break
        let inhabInstVal ← mkAppOptM ``Inhabited.mk #[some indTyApp, some inhabBody]
        let inhabInstBody ← mkLambdaFVars allFVars inhabInstVal
        let inhabType ← mkAppM ``Inhabited #[indTyApp]
        let inhabTypeForall ← mkForallFVars allFVars inhabType
        let inhabDecl := Declaration.defnDecl {
          name := inhabInstName
          levelParams := lvlParams
          type := inhabTypeForall
          value := inhabInstBody
          hints := .regular 0
          safety := .safe
        }
        addAndCompile inhabDecl
        Lean.Meta.addInstance inhabInstName .global 100

      -- Generate toData, fromData (safe → Option α), and unsafeFromData (→ α)
      let toDataBody ← mkToDataBody iv plan
      let toDataBodyApplied := mkAppN toDataBody allFVars

      let fromDataBody ← mkFromDataBody iv plan (safe := true)
      let fromDataBodyApplied := mkAppN fromDataBody allFVars

      let unsafeFromDataBody ← mkFromDataBody iv plan (safe := false)
      let unsafeFromDataBodyApplied := mkAppN unsafeFromDataBody allFVars

      -- Create the PlutusData instance value
      let env ← getEnv
      let some (.inductInfo pdInfo) := env.find? ``PlutusData
        | throwError "PlutusData inductive not found"
      let pdCtorName := pdInfo.ctors[0]!
      let instVal := mkAppN (mkConst pdCtorName [])
        #[indTyApp, toDataBodyApplied, fromDataBodyApplied, unsafeFromDataBodyApplied]

      let instBody ← mkLambdaFVars allFVars instVal
      let instType ← mkAppM ``PlutusData #[indTyApp]
      let instTypeForall ← mkForallFVars allFVars instType

      let instName := iv.name ++ `instPlutusData
      let decl := Declaration.defnDecl {
        name := instName
        levelParams := lvlParams
        type := instTypeForall
        value := instBody
        hints := .regular 0
        safety := .safe
      }
      addAndCompile decl
      Lean.Meta.addInstance instName .global 100

      -- Also generate BEq instance via equalsData ∘ toData
      let beqInstName := iv.name ++ `instBEq
      let beqBody ← do
        withLocalDecl `a .default indTyApp fun a =>
        withLocalDecl `b .default indTyApp fun b => do
          let aData ← mkAppM ``PlutusData.toData #[a]
          let bData ← mkAppM ``PlutusData.toData #[b]
          let body ← mkAppM ``Moist.Onchain.Prelude.equalsData #[aData, bData]
          let lam ← mkLambdaFVars #[a, b] body
          let beqInst ← mkAppOptM ``BEq.mk #[some indTyApp, some lam]
          mkLambdaFVars allFVars beqInst
      let beqType ← do
        let ty ← mkAppM ``BEq #[indTyApp]
        mkForallFVars allFVars ty
      let beqDecl := Declaration.defnDecl {
        name := beqInstName
        levelParams := lvlParams
        type := beqType
        value := beqBody
        hints := .regular 0
        safety := .safe
      }
      addAndCompile beqDecl
      Lean.Meta.addInstance beqInstName .global 100

/-! ## @[plutus_data] attribute with validation -/

initialize plutusDataAttr : TagAttribute ← do
  let attr ← registerTagAttribute `plutus_data
    "Use Data encoding (ConstrData/UnConstrData) for this inductive type"
    (validate := fun name => do
      let env ← getEnv
      match env.find? name with
      | some (.inductInfo iv) =>
        let plan ← Lean.Meta.MetaM.run' (validatePlutusDataInductive iv)
        modifyEnv fun env => codecPlanExt.addEntry env (name, plan)
        try Lean.Meta.MetaM.run' (derivePlutusDataInstance iv plan)
        catch e => Lean.logWarning m!"PlutusData auto-derivation failed for {name}: {e.toMessageData}"
      | some (.ctorInfo _) => pure ()
      | _ => throwError "@[plutus_data] can only be applied to inductive types, \
          but '{name}' is not an inductive type")
  plutusDataTagRef.set attr.hasTag
  return attr

/-- Determine the Plutus representation for a type name. -/
def getPlutusRepr (env : Environment) (typeName : Name) : PlutusRepr :=
  if plutusDataAttr.hasTag env typeName then .data else .sop

/-! ## Param resolution at instantiation time -/

/-- Substitute `.param` entries in a codec with concrete codecs
    based on actual type arguments at the use site. -/
partial def resolveParamCodec (codec : DataCodec) (typeArgs : Array Lean.Expr)
    : MetaM DataCodec := do
  match codec with
  | .param idx =>
    if h : idx < typeArgs.size then
      match ← resolveDataCodec typeArgs[idx] with
      | .ok c => return c
      | .error e =>
        throwError "type parameter {idx}: {formatDataCompatError e}"
    else return .identity
  | .listData elem =>
    let elem' ← resolveParamCodec elem typeArgs
    return .listData elem'
  | .mapData key value =>
    let key' ← resolveParamCodec key typeArgs
    let value' ← resolveParamCodec value typeArgs
    return .mapData key' value'
  | other => return other

end Moist.Onchain
