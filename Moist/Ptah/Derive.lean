import Lean
import Moist.Ptah.Term
import Moist.Ptah.PlutusType
import Moist.Ptah.PLam
import Moist.Ptah.PLift
import Moist.Ptah.IsData

namespace Moist.Ptah

open Lean Meta Elab Command

private def elabCodeBlock (s : String) (tag : String := "derive") : CommandElabM Unit := do
  let env ← getEnv
  let stx ← match Parser.runParserCategory env `command s s!"<{tag}>" with
    | .ok stx => pure stx
    | .error e => throwError "{tag}: parse error:\n{e}\n\nGenerated code:\n{s}"
  elabCommand stx

private def getParamNames (indType : Expr) : MetaM (Array Name) :=
  forallTelescope indType fun args _ =>
    args.mapM fun arg => arg.fvarId!.getUserName

private structure CtorInfo where
  tag : Nat
  fullName : Name
  shortName : String
  numFields : Nat
deriving Inhabited

private def getCtorInfos (env : Environment) (ctors : List Name) : Array CtorInfo := Id.run do
  let mut result := #[]
  let mut tag := 0
  for ctorName in ctors do
    let numFields := match env.find? ctorName with
      | some (.ctorInfo ci) => ci.numFields
      | _ => 0
    result := result.push { tag, fullName := ctorName, shortName := ctorName.getString!, numFields }
    tag := tag + 1
  result

private def getIndInfo (name : Name) : CommandElabM (InductiveVal × Array Name × Array CtorInfo) := do
  let env ← getEnv
  let some indVal := (do
    let ci ← env.find? name
    match ci with | .inductInfo v => some v | _ => none)
    | throwError "{name} is not an inductive type"
  let paramNames ← liftTermElabM <| getParamNames indVal.type
  let ctors := getCtorInfos env indVal.ctors
  pure (indVal, paramNames, ctors)

private def genBindings (paramNames : Array Name) : String :=
  paramNames.toList.map (s!"[Moist.Ptah.PType {·}]") |>.intersperse " " |> String.join

private def genApp (typeName : Name) (paramNames : Array Name) : String :=
  paramNames.foldl (fun acc p => s!"{acc} {p}") (toString typeName)

private def genPTypeInst (typeName : Name) (paramNames : Array Name) : String :=
  s!"instance {genBindings paramNames} : Moist.Ptah.PType ({genApp typeName paramNames}) where"

/-! ## Common Constr/Case generation -/

private def genConstrPconArm (ci : CtorInfo) (wrapField : String → String := id) : String :=
  let fields := (List.range ci.numFields).map (s!"x{·}")
  let pat := if fields.isEmpty then s!".{ci.shortName}" else s!".{ci.shortName} {" ".intercalate fields}"
  if fields.isEmpty then
    s!"    | {pat} => ⟨pure (.Constr {ci.tag} [])⟩"
  else
    let builds := ", ".intercalate (fields.map fun f => s!"← ({wrapField f}).build")
    s!"    | {pat} => ⟨do pure (.Constr {ci.tag} [{builds}])⟩"

private def genCasePmatchAlt (ci : CtorInfo) (unwrapField : String → String := id) : String × String :=
  let vars := (List.range ci.numFields).map (s!"v{ci.tag}_{·}")
  let freshBinds := "\n".intercalate (vars.map (s!"    let {·} ← Moist.MIR.freshVar \"x\""))
  let ctorApp := if vars.isEmpty
    then s!".{ci.shortName}"
    else s!".{ci.shortName} " ++ (" ".intercalate (vars.map fun v => unwrapField s!"⟨pure (.Var {v})⟩"))
  let innerExpr := s!"(f ({ctorApp})).build"
  let altName := s!"alt{ci.tag}"
  let altBind := if vars.isEmpty then
    s!"    let {altName} ← {innerExpr}"
  else
    let wrapped := vars.foldr (fun v acc => s!"Moist.MIR.Expr.Lam {v} ({acc})") s!"← {innerExpr}"
    s!"    let {altName} := {wrapped}"
  let fullBlock := if freshBinds.isEmpty then altBind else s!"{freshBinds}\n{altBind}"
  (altName, fullBlock)

private def genPlutusTypeBody (typeName : Name) (paramNames : Array Name) (ctors : Array CtorInfo)
    (wrapField : String → String) (unwrapField : String → String) (extra : String) : String :=
  let pconArms := "\n".intercalate (ctors.toList.map (genConstrPconArm · wrapField))
  let altParts := ctors.toList.map (genCasePmatchAlt · unwrapField)
  let altBinds := "\n".intercalate (altParts.map (·.2))
  let altList := ", ".intercalate (altParts.map (·.1))
  s!"{genBindings paramNames} {extra}".trim ++ s!" : Moist.Ptah.PlutusType" ++
  s!" ({genApp typeName paramNames}) where
  toPType := inferInstance
  PInner := Moist.Ptah.POpaque
  innerPType := inferInstance
  pcon' := fun
{pconArms}
  pmatch' := fun inner f => ⟨do
    let scrut ← inner.build
{altBinds}
    pure (.Case scrut [{altList}])
  ⟩"

/-! ## Scott encoding (derive_plutustype) — fields stored directly -/

elab "derive_plutustype" id:ident : command => do
  let name ← liftCoreM <| resolveGlobalConstNoOverload id
  let (_, paramNames, ctors) ← getIndInfo name
  elabCodeBlock (genPTypeInst name paramNames) "derive_plutustype"
  let body := genPlutusTypeBody name paramNames ctors (fun x => x) (fun x => x) ""
  elabCodeBlock s!"instance {body}" "derive_plutustype"

/-! ## Data encoding (derive_plutusdata) — fields encoded via PIsData, native Constr/Case -/

private def genIsDataPconArm (ci : CtorInfo) : String :=
  let fields := (List.range ci.numFields).map (s!"f{·}")
  let pat := if fields.isEmpty then s!"{ci.fullName}" else s!"{ci.fullName} {" ".intercalate fields}"
  let dataList := fields.foldr (fun f acc =>
    s!"(pmkCons # (PIsData.pdataImpl {f}) # {acc})"
  ) "(pmkNilData # punit)"
  s!"    | {pat} => pconstrData # ({ci.tag} : Term PInteger) # {dataList}"

private def genIsDataPfromDataBranch (ci : CtorInfo) : String := Id.run do
  if ci.numFields == 0 then
    return s!"pcon {ci.fullName}"
  let mut s := ""
  let mut cur := "flds"
  for i in List.range ci.numFields do
    s := s ++ s!"plet (pheadList # {cur}) fun d{i} =>\n            "
    if i < ci.numFields - 1 then
      s := s ++ s!"plet (ptailList # {cur}) fun rest{i} =>\n            "
      cur := s!"rest{i}"
  let fieldApps := " ".intercalate ((List.range ci.numFields).map (s!"(PIsData.pfromDataImpl d{·})"))
  s := s ++ s!"pcon ({ci.fullName} {fieldApps})"
  s

private def genIsDataPdataArm (ci : CtorInfo) (wrapList : String → String) : String :=
  let fields := (List.range ci.numFields).map (s!"f{·}")
  let pat := if fields.isEmpty then s!".{ci.shortName}" else s!".{ci.shortName} {" ".intercalate fields}"
  let dataList := fields.foldr (fun f acc =>
    s!"(pmkCons # (PIsData.pdataImpl {f}) # {acc})"
  ) "(pmkNilData # punit)"
  s!"      | {pat} => {wrapList dataList}"

private def genIsDataInst (typeName : Name) (paramNames : Array Name) (ctors : Array CtorInfo)
    (extra : String) (useList : Bool := false) : String :=
  let app := genApp typeName paramNames
  let pfromBody := if useList then
    let decode := genIsDataPfromDataBranch ctors[0]!
    s!"fun d =>\n      plet (punListData # d) fun flds =>\n        {decode}"
  else
    let branches := ctors.toList.foldr (fun ci acc =>
      let decode := genIsDataPfromDataBranch ci
      s!"pif (pequalsInteger # tag # ({ci.tag} : Term PInteger))\n            ({decode})\n            ({acc})"
    ) "perror"
    s!"fun d =>\n      plet (punConstrData # d) fun pair =>\n        plet (pfstPair # pair) fun tag =>\n          plet (psndPair # pair) fun flds =>\n            {branches}"
  let pdataArmsFixed : List String := Id.run do
    let mut result := []
    let mut tag := 0
    for ci in ctors.toList do
      if useList then
        result := result ++ [genIsDataPdataArm ci (s!"plistData # {·}")]
      else
        result := result ++ [genIsDataPdataArm ci (fun dl => s!"pconstrData # ({tag} : Term PInteger) # {dl}")]
      tag := tag + 1
    result
  let pdataBody := "\n".intercalate pdataArmsFixed
  s!"open Moist.Ptah in
instance {genBindings paramNames} {extra} : Moist.Ptah.PIsData ({app}) where
  pdataImpl x := pmatch x fun
{pdataBody}
  pfromDataImpl := {pfromBody}"

elab "derive_plutusdata" id:ident : command => do
  let name ← liftCoreM <| resolveGlobalConstNoOverload id
  let (_, paramNames, ctors) ← getIndInfo name
  let hasDataFields := ctors.any (·.numFields > 0)
  let extra := if hasDataFields then
    paramNames.toList.map (s!"[Moist.Ptah.PIsData {·}]") |>.intersperse " " |> String.join
  else ""
  elabCodeBlock (genPTypeInst name paramNames) "derive_plutusdata"
  let wrap (f : String) := s!"(Moist.Ptah.PIsData.pdataImpl {f})"
  let unwrap (f : String) := s!"(Moist.Ptah.PIsData.pfromDataImpl {f})"
  let body := genPlutusTypeBody name paramNames ctors wrap unwrap extra
  elabCodeBlock s!"instance {body}" "derive_plutusdata"
  elabCodeBlock (genIsDataInst name paramNames ctors extra) "derive_plutusdata"

/-! ## Data.List encoding (derive_plutusdata_list) — single ctor, List on-chain -/

elab "derive_plutusdata_list" id:ident : command => do
  let name ← liftCoreM <| resolveGlobalConstNoOverload id
  let (_, paramNames, ctors) ← getIndInfo name
  unless ctors.size == 1 do
    throwError "derive_plutusdata_list: {name} must have exactly one constructor, got {ctors.size}"
  let hasDataFields := ctors[0]!.numFields > 0
  let extra := if hasDataFields then
    paramNames.toList.map (s!"[Moist.Ptah.PIsData {·}]") |>.intersperse " " |> String.join
  else ""
  elabCodeBlock (genPTypeInst name paramNames) "derive_plutusdata_list"
  let wrap (f : String) := s!"(Moist.Ptah.PIsData.pdataImpl {f})"
  let unwrap (f : String) := s!"(Moist.Ptah.PIsData.pfromDataImpl {f})"
  let body := genPlutusTypeBody name paramNames ctors wrap unwrap extra
  elabCodeBlock s!"instance {body}" "derive_plutusdata_list"
  elabCodeBlock (genIsDataInst name paramNames ctors extra (useList := true)) "derive_plutusdata_list"

end Moist.Ptah
