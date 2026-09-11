import Moist.MIR.Optimize.Safety
import Moist.CEK.Machine

namespace Moist.MIR

/-! # Known-constructor case simplification

A branch's leading lambdas do not determine the scrutinee's runtime field
count. Only literal constructors and already-evaluated constructor bindings
supply constructor facts. Alternatives receive exactly those fields through
ordinary applications, preserving partial and over-application behavior.
All constructor fields are evaluated before selecting or applying a branch.
List cases with extra alternatives are retained: the native evaluator accepts
them while the Lean CEK rejects them. Folding either outcome would change the
other evaluator's semantics.
-/

def renameMany (pairs : List (VarId × VarId)) (expression : Expr) : Expr :=
  let start := pairs.foldl (fun next (old, replacement) =>
    max next (max old.uid replacement.uid + 1)) (maxUidExpr expression + 1)
  runFresh (do
    let mut result := expression
    let mut replacements := []
    for (old, replacement) in pairs do
      let temporary ← freshVar "rename"
      result ← subst old (.Var temporary) result
      replacements := replacements ++ [(temporary, replacement)]
    for (temporary, replacement) in replacements do
      result ← subst temporary (.Var replacement) result
    return result) start

private structure KnownCtor where
  tag : Nat
  constructorCount : Nat
  fields : List Expr
  listValue : Bool := false

private abbrev KnownCtors := List (VarId × KnownCtor)

private def knownConstructor (environment : KnownCtors) : Expr → Option KnownCtor
  | .Var identifier => (environment.find? (fun entry => entry.1 == identifier)).map Prod.snd
  | .Constr tag fields =>
    if fields.all (·.isAtom) then some ⟨tag, 0, fields, false⟩ else none
  | .Lit (constant, annotation) => do
    let (tag, constructorCount, values) ← Moist.CEK.constToTagAndFields constant
    let fieldTypes ← match values, annotation with
      | [], _ => some []
      | [_, _], .TypeOperator (.TypeList element) => some [element, annotation]
      | [_, _], .TypeOperator (.TypePair first second) => some [first, second]
      | _, _ => none
    let fields ← (values.zip fieldTypes).mapM fun
      | (.VCon field, fieldType) => some (Expr.Lit (field, fieldType))
      | _ => none
    let listValue := match constant with
      | .ConstList _ | .ConstDataList _ => true
      | _ => false
    return ⟨tag, constructorCount, fields, listValue⟩
  | _ => none

private def filterKnown (binder : VarId) (environment : KnownCtors) : KnownCtors :=
  environment.filter fun (identifier, info) =>
    identifier != binder && !(freeVarsList info.fields).contains binder

private def selectAlternative (tag constructorCount : Nat) (fields alternatives : List Expr) : Expr :=
  if constructorCount > 0 && alternatives.length > constructorCount then .Error
  else match alternatives[tag]? with
    | some alternative => fields.foldl Expr.App alternative
    | none => .Error

private def reduceConstructorCase (tag : Nat) (fields alternatives : List Expr) : Expr :=
  runFresh (do
    let mut bindings := []
    let mut arguments := []
    for field in fields do
      if field.isAtom then
        arguments := arguments ++ [field]
      else
        let identifier ← freshVar "field"
        bindings := bindings ++ [(identifier, field, false)]
        arguments := arguments ++ [.Var identifier]
    let result := selectAlternative tag 0 arguments alternatives
    return if bindings.isEmpty then result else .Let bindings result)
    (maxUidExpr (.Case (.Constr tag fields) alternatives) + 1)

mutual
  private partial def caseMerge (environment : KnownCtors) : Expr → Expr × Bool
    | .Let bindings body =>
      let (bindings', environment', changedBindings) := caseMergeBinds environment bindings
      let (body', changedBody) := caseMerge environment' body
      (.Let bindings' body', changedBindings || changedBody)
    | .Case scrutinee alternatives =>
      let (scrutinee', changedScrutinee) := caseMerge environment scrutinee
      let (alternatives', changedAlternatives) := caseMergeList environment alternatives
      match scrutinee' with
      | .Constr tag fields => (reduceConstructorCase tag fields alternatives', true)
      | _ => match knownConstructor environment scrutinee' with
        | some info =>
          if info.listValue && alternatives'.length > 2 then
            (.Case scrutinee' alternatives', changedScrutinee || changedAlternatives)
          else
            (selectAlternative info.tag info.constructorCount info.fields alternatives', true)
        | none => (.Case scrutinee' alternatives', changedScrutinee || changedAlternatives)
    | .Lam binder body =>
      let (body', changed) := caseMerge (filterKnown binder environment) body
      (.Lam binder body', changed)
    | .Fix binder body =>
      let (body', changed) := caseMerge (filterKnown binder environment) body
      (.Fix binder body', changed)
    | .App function argument =>
      let (function', changedFunction) := caseMerge environment function
      let (argument', changedArgument) := caseMerge environment argument
      (.App function' argument', changedFunction || changedArgument)
    | .Force expression =>
      let (expression', changed) := caseMerge environment expression
      (.Force expression', changed)
    | .Delay expression =>
      let (expression', changed) := caseMerge environment expression
      (.Delay expression', changed)
    | .Constr tag fields =>
      let (fields', changed) := caseMergeList environment fields
      (.Constr tag fields', changed)
    | expression => (expression, false)

  private partial def caseMergeList (environment : KnownCtors) (expressions : List Expr) :
      List Expr × Bool :=
    let results := expressions.map (caseMerge environment)
    (results.map Prod.fst, results.any Prod.snd)

  private partial def caseMergeBinds (environment : KnownCtors) :
      List (VarId × Expr × Bool) → List (VarId × Expr × Bool) × KnownCtors × Bool
    | [] => ([], environment, false)
    | (binder, expression, erased) :: rest =>
      let (expression', changedExpression) := caseMerge environment expression
      let shadowed := filterKnown binder environment
      let environment' := match knownConstructor environment expression' with
        | some info =>
          if (freeVarsList info.fields).contains binder then shadowed
          else (binder, info) :: shadowed
        | none => shadowed
      let (rest', finalEnvironment, changedRest) := caseMergeBinds environment' rest
      ((binder, expression', erased) :: rest', finalEnvironment, changedExpression || changedRest)
end

def caseMergePass (expression : Expr) : Expr × Bool :=
  let (result, changed) := caseMerge [] (uniqueOptimizationBinders expression)
  (uniqueOptimizationBinders result, changed)

end Moist.MIR
