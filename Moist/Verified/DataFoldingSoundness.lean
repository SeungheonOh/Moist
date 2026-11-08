import Moist.MIR.Optimize.Advanced.Constants
import Moist.Verified.AdvancedTraversal
import Moist.Verified.AdvancedRefinement

variable [sv : Moist.CEK.SemVariant]

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced Moist.Plutus.Term Moist.CEK
open Moist.Verified.Contextual Moist.Verified.AdvancedRedexes

theorem literal_join_refines (expression : Expr) (literal : Const × BuiltinType)
    (term : Term)
    (lowering : ∀ environment, lowerTotalExpr environment expression = some term)
    (closed : Moist.Verified.closedAt 0 term = true)
    (joined : ∀ environment stack, ∃ fuel,
      advance fuel (.compute stack environment term) = .ret stack (.VCon literal.1)) :
    MIRCtxRefines expression (.Lit literal) := by
  obtain ⟨constant, annotation⟩ := literal
  intro environment
  rw [lowering]
  simp only [lowerTotalExpr, expandFix, lowerTotal, Option.isSome_some]
  refine ⟨fun _ => True.intro, ?_⟩
  apply AdvancedRefinement.contextual_of_uniform_join closed (by intros; simp [Moist.Verified.closedAt])
  intro environment stack
  obtain ⟨fuel, reaches⟩ := joined environment stack
  exact ⟨fuel, 1, reaches⟩

omit sv in
private theorem literalData_spec {expression : Expr} {datum : Moist.Plutus.Data}
    (accepted : literalData expression = some datum) :
    expression = .Lit (.Data datum, .AtomicType .TypeData) := by
  unfold literalData at accepted
  split at accepted
  · simp_all
  · contradiction

omit sv in
private theorem data_mapM_spec (values : List Const) (data : List Moist.Plutus.Data)
    (accepted : values.mapM (fun value => match value with
      | .Data datum => some datum
      | _ => none) = some data) : values = data.map Const.Data := by
  induction values generalizing data with
  | nil => simpa using accepted.symm
  | cons value rest inductionHypothesis =>
    cases value <;> simp [Option.bind_eq_bind, Option.bind_eq_some_iff] at accepted
    rename_i datum
    obtain ⟨tail, acceptedTail, rfl⟩ := accepted
    simp [inductionHypothesis tail acceptedTail]

omit sv in
private theorem literalDataList_spec {expression : Expr} {data : List Moist.Plutus.Data}
    (accepted : literalDataList expression = some data) :
    ∃ annotation, expression = .Lit (.ConstList (.AtomicType .TypeData) (data.map Const.Data), annotation) := by
  unfold literalDataList at accepted
  split at accepted
  · rename_i elementType values annotation
    split at accepted
    · rename_i guard
      simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
      obtain ⟨_, rfl⟩ := guard
      have equal := data_mapM_spec values data accepted
      subst values
      exact ⟨annotation, rfl⟩
    · contradiction
  · contradiction

private theorem constrData_evaluates (tag : Int) (data : List Moist.Plutus.Data)
    (tagRange : ¬(tag < 0 ∨ tag ≥ 2 ^ 64)) :
    evalBuiltin .ConstrData [.VCon (.ConstList (.AtomicType .TypeData) (data.map Const.Data)),
      .VCon (.Integer tag)] = some (.VCon (.Data (.Constr tag data))) := by
  have word : word64Ok tag = true := by
    simp only [word64Ok, Bool.and_eq_true, decide_eq_true_eq]
    have : ((2 ^ 64 : Nat) : Int) = 2 ^ 64 := by norm_cast
    omega
  rw [show [CekValue.VCon (.ConstList (.AtomicType .TypeData) (data.map Const.Data)),
      .VCon (.Integer tag)] = [Const.ConstList (.AtomicType .TypeData) (data.map Const.Data),
      .Integer tag].map CekValue.VCon from rfl, evalBuiltin_consts _ _ rfl]
  change (if (decide (BuiltinType.AtomicType .TypeData = dataType) && (!sv.ensurable || word64Ok tag)) = true
    then (constListToData (data.map Const.Data)).bind (fun values => some (Const.Data (.Constr tag values)))
    else none).map CekValue.VCon = _
  rw [word, constListToData_map]
  simp [dataType]

theorem foldedDataConstructor_refines (expression : Expr) (literal : Const × BuiltinType)
    (folded : foldedDataConstructor expression = some literal) :
    MIRCtxRefines expression (.Lit literal) := by
  unfold foldedDataConstructor at folded
  split at folded
  · rename_i number
    cases folded
    apply literal_join_refines _ _
      (.Apply (.Builtin .IData) (.Constant (.Integer number, .AtomicType .TypeInteger)))
    · intro environment; simp [lowerTotalExpr, expandFix, lowerTotal]
    · simp [Moist.Verified.closedAt]
    · intro environment stack; exact ⟨5, rfl⟩
  · rename_i bytes
    cases folded
    apply literal_join_refines _ _
      (.Apply (.Builtin .BData) (.Constant (.ByteString bytes, .AtomicType .TypeByteString)))
    · intro environment; simp [lowerTotalExpr, expandFix, lowerTotal]
    · simp [Moist.Verified.closedAt]
    · intro environment stack; exact ⟨5, rfl⟩
  · cases folded
    apply literal_join_refines _ _
      (.Apply (.Builtin .MkNilData) (.Constant (.Unit, .AtomicType .TypeUnit)))
    · intro environment; simp [lowerTotalExpr, expandFix, lowerTotal]
    · simp [Moist.Verified.closedAt]
    · intro environment stack; exact ⟨5, rfl⟩
  · rename_i head tail
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at folded
    obtain ⟨headData, acceptedHead, tailData, acceptedTail, result⟩ := folded
    have headEqual := literalData_spec acceptedHead
    subst head
    obtain ⟨annotation, tailEqual⟩ := literalDataList_spec acceptedTail
    subst tail
    simp only [pure, Option.some.injEq] at result
    subst literal
    apply literal_join_refines _ _
      (.Apply (.Apply (.Force (.Builtin .MkCons))
        (.Constant (.Data headData, .AtomicType .TypeData)))
        (.Constant (.ConstList (.AtomicType .TypeData) (tailData.map Const.Data), annotation)))
    · intro environment; simp [lowerTotalExpr, expandFix, lowerTotal]
    · simp [Moist.Verified.closedAt]
    · intro environment stack; exact ⟨11, rfl⟩
  · rename_i fields
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at folded
    obtain ⟨data, accepted, result⟩ := folded
    simp only [pure, Option.some.injEq] at result
    subst literal
    obtain ⟨annotation, equal⟩ := literalDataList_spec accepted
    subst fields
    apply literal_join_refines _ _
      (.Apply (.Builtin .ListData)
        (.Constant (.ConstList (.AtomicType .TypeData) (data.map Const.Data), annotation)))
    · intro environment; simp [lowerTotalExpr, expandFix, lowerTotal]
    · simp [Moist.Verified.closedAt]
    · intro environment stack
      refine ⟨5, ?_⟩
      change (match evalBuiltin .ListData
          [.VCon (.ConstList (.AtomicType .TypeData) (data.map Const.Data))] with
        | some value => State.ret stack value
        | none => .error) = .ret stack (.VCon (.Data (.List data)))
      have evaluated : evalBuiltin .ListData
          [.VCon (.ConstList (.AtomicType .TypeData) (data.map Const.Data))] =
          some (.VCon (.Data (.List data))) := by
        rw [show [CekValue.VCon (.ConstList (.AtomicType .TypeData) (data.map Const.Data))] =
          [Const.ConstList (.AtomicType .TypeData) (data.map Const.Data)].map CekValue.VCon from rfl,
          evalBuiltin_consts _ _ rfl]
        change ((constListToData (data.map Const.Data)).bind
          (fun values => some (Const.Data (.List values)))).map CekValue.VCon = _
        rw [constListToData_map]; rfl
      rw [evaluated]
  · rename_i tag fields
    split at folded
    · contradiction
    · rename_i tagRange
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at folded
      obtain ⟨data, accepted, result⟩ := folded
      simp only [pure, Option.some.injEq] at result
      subst literal
      obtain ⟨annotation, equal⟩ := literalDataList_spec accepted
      subst fields
      apply literal_join_refines _ _
        (.Apply (.Apply (.Builtin .ConstrData)
          (.Constant (.Integer tag, .AtomicType .TypeInteger)))
          (.Constant (.ConstList (.AtomicType .TypeData) (data.map Const.Data), annotation)))
      · intro environment; simp [lowerTotalExpr, expandFix, lowerTotal]
      · simp [Moist.Verified.closedAt]
      · intro environment stack
        refine ⟨9, ?_⟩
        change (match evalBuiltin .ConstrData
            [.VCon (.ConstList (.AtomicType .TypeData) (data.map Const.Data)), .VCon (.Integer tag)] with
          | some value => State.ret stack value
          | none => .error) = .ret stack (.VCon (.Data (.Constr tag data)))
        rw [constrData_evaluates tag data (by simpa using tagRange)]
  · contradiction

theorem foldDataConstructor_refines (expression : Expr) :
    MIRCtxRefines expression (foldDataConstructor expression) := by
  unfold foldDataConstructor
  split
  · rename_i literal accepted
    split
    · exact foldedDataConstructor_refines expression literal accepted
    · exact mirCtxRefines_refl expression
  · exact mirCtxRefines_refl expression

theorem foldDataConstructors_refines (expression : Expr) :
    MIRCtxRefines expression (foldDataConstructors expression) := by
  apply rewriteBottomUp_refines foldDataConstructor foldDataConstructor_refines
  intro binder body
  simp [foldDataConstructor, foldedDataConstructor]

end Moist.Verified.MIR
