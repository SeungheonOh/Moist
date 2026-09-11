import Moist.MIR.Optimize.Advanced.Constants
import Moist.Verified.AdvancedTraversal
import Moist.Verified.AdvancedRefinement

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

private theorem literalData_spec {expression : Expr} {datum : Moist.Plutus.Data}
    (accepted : literalData expression = some datum) :
    expression = .Lit (.Data datum, .AtomicType .TypeData) := by
  unfold literalData at accepted
  split at accepted
  · simp_all
  · contradiction

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

private theorem literalDataList_spec {expression : Expr} {data : List Moist.Plutus.Data}
    (accepted : literalDataList expression = some data) :
    ∃ annotation, expression = .Lit (.ConstDataList data, annotation) ∨
      expression = .Lit (.ConstList (data.map Const.Data), annotation) := by
  unfold literalDataList at accepted
  split at accepted
  · rename_i values annotation
    split at accepted
    · cases accepted
      exact ⟨annotation, .inl rfl⟩
    · contradiction
  · rename_i values annotation
    split at accepted
    · have equal := data_mapM_spec values data accepted
      subst values
      exact ⟨annotation, .inr rfl⟩
    · contradiction
  · contradiction

private theorem constListToData_map (data : List Moist.Plutus.Data) :
    constListToData (data.map Const.Data) = some data := by
  induction data with
  | nil => rfl
  | cons head tail inductionHypothesis =>
    simp [constListToData, inductionHypothesis]

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
    obtain ⟨annotation, tailEqual | tailEqual⟩ := literalDataList_spec acceptedTail
    · subst tail
      simp only [pure, Option.some.injEq] at result
      subst literal
      apply literal_join_refines _ _
        (.Apply (.Apply (.Force (.Builtin .MkCons))
          (.Constant (.Data headData, .AtomicType .TypeData)))
          (.Constant (.ConstDataList tailData, annotation)))
      · intro environment; simp [lowerTotalExpr, expandFix, lowerTotal]
      · simp [Moist.Verified.closedAt]
      · intro environment stack; exact ⟨11, rfl⟩
    · subst tail
      simp only [pure, Option.some.injEq] at result
      subst literal
      apply literal_join_refines _ _
        (.Apply (.Apply (.Force (.Builtin .MkCons))
          (.Constant (.Data headData, .AtomicType .TypeData)))
          (.Constant (.ConstList (tailData.map Const.Data), annotation)))
      · intro environment; simp [lowerTotalExpr, expandFix, lowerTotal]
      · simp [Moist.Verified.closedAt]
      · intro environment stack; exact ⟨11, rfl⟩
  · rename_i fields
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at folded
    obtain ⟨data, accepted, result⟩ := folded
    simp only [pure, Option.some.injEq] at result
    subst literal
    obtain ⟨annotation, equal | equal⟩ := literalDataList_spec accepted
    · subst fields
      apply literal_join_refines _ _
        (.Apply (.Builtin .ListData) (.Constant (.ConstDataList data, annotation)))
      · intro environment; simp [lowerTotalExpr, expandFix, lowerTotal]
      · simp [Moist.Verified.closedAt]
      · intro environment stack; exact ⟨5, rfl⟩
    · subst fields
      apply literal_join_refines _ _
        (.Apply (.Builtin .ListData) (.Constant (.ConstList (data.map Const.Data), annotation)))
      · intro environment; simp [lowerTotalExpr, expandFix, lowerTotal]
      · simp [Moist.Verified.closedAt]
      · intro environment stack
        refine ⟨5, ?_⟩
        change (match evalBuiltin .ListData [.VCon (.ConstList (data.map Const.Data))] with
          | some value => State.ret stack value
          | none => .error) = .ret stack (.VCon (.Data (.List data)))
        have evaluated : evalBuiltin .ListData [.VCon (.ConstList (data.map Const.Data))] =
            some (.VCon (.Data (.List data))) := by
          have constantResult : evalBuiltinConst .ListData [.ConstList (data.map Const.Data)] =
              some (.Data (.List data)) := by
            change (constListToData (data.map Const.Data) >>= fun values => some (Const.Data (.List values))) = _
            rw [constListToData_map]; rfl
          change (match evalBuiltinConst .ListData [.ConstList (data.map Const.Data)] with
            | some constant => some (CekValue.VCon constant)
            | none => none) = _
          rw [constantResult]
        rw [evaluated]
  · rename_i tag fields
    split at folded
    · contradiction
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at folded
      obtain ⟨data, accepted, result⟩ := folded
      simp only [pure, Option.some.injEq] at result
      subst literal
      obtain ⟨annotation, equal | equal⟩ := literalDataList_spec accepted
      · subst fields
        apply literal_join_refines _ _
          (.Apply (.Apply (.Builtin .ConstrData)
            (.Constant (.Integer tag, .AtomicType .TypeInteger)))
            (.Constant (.ConstDataList data, annotation)))
        · intro environment; simp [lowerTotalExpr, expandFix, lowerTotal]
        · simp [Moist.Verified.closedAt]
        · intro environment stack; exact ⟨9, rfl⟩
      · subst fields
        apply literal_join_refines _ _
          (.Apply (.Apply (.Builtin .ConstrData)
            (.Constant (.Integer tag, .AtomicType .TypeInteger)))
            (.Constant (.ConstList (data.map Const.Data), annotation)))
        · intro environment; simp [lowerTotalExpr, expandFix, lowerTotal]
        · simp [Moist.Verified.closedAt]
        · intro environment stack
          refine ⟨9, ?_⟩
          change (match evalBuiltin .ConstrData [.VCon (.ConstList (data.map Const.Data)), .VCon (.Integer tag)] with
            | some value => State.ret stack value
            | none => .error) = .ret stack (.VCon (.Data (.Constr tag data)))
          have evaluated : evalBuiltin .ConstrData [.VCon (.ConstList (data.map Const.Data)), .VCon (.Integer tag)] =
              some (.VCon (.Data (.Constr tag data))) := by
            have constantResult : evalBuiltinConst .ConstrData [.ConstList (data.map Const.Data), .Integer tag] =
                some (.Data (.Constr tag data)) := by
              change (constListToData (data.map Const.Data) >>= fun values => some (Const.Data (.Constr tag values))) = _
              rw [constListToData_map]; rfl
            change (match evalBuiltinConst .ConstrData [.ConstList (data.map Const.Data), .Integer tag] with
              | some constant => some (CekValue.VCon constant)
              | none => none) = _
            rw [constantResult]
          rw [evaluated]
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
