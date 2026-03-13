import Lean
import Moist.Plutus.Types

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
