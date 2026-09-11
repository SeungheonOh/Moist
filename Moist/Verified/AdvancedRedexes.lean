import Moist.CEK.Machine

namespace Moist.Verified.AdvancedRedexes

open Moist.CEK
open Moist.Plutus.Term

/-! Kernel-checked CEK joins for the new local rewrite schemas.

The stack and environment remain arbitrary, so these equalities retain the
entire continuation rather than only a top-level return value. They do not
constitute a proof of the MIR analyses, traversal, lowering, or whole pipeline.
This module does not import the legacy budget-exhaustion axiom.
-/

def advance : Nat → State → State
  | 0, state => state
  | fuel + 1, state => advance fuel (step state)

theorem force_case_delay (condition : Bool) (whenFalse whenTrue : Term)
    (environment : CekEnv) (stack : Stack) :
    advance 6 (.compute stack environment
      (.Force (.Case (.Constant (.Bool condition, .AtomicType .TypeBool))
        [.Delay whenFalse, .Delay whenTrue]))) =
    advance 3 (.compute stack environment
      (.Case (.Constant (.Bool condition, .AtomicType .TypeBool)) [whenFalse, whenTrue])) := by
  cases condition <;> rfl

theorem boolean_choice (condition : Bool) (whenFalse whenTrue : Term)
    (environment : CekEnv) (stack : Stack) :
    advance 17 (.compute stack environment
      (.Force (.Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse))
        (.Constant (.Bool condition, .AtomicType .TypeBool))) (.Delay whenTrue))
        (.Delay whenFalse)))) =
    advance 3 (.compute stack environment
      (.Case (.Constant (.Bool condition, .AtomicType .TypeBool)) [whenFalse, whenTrue])) := by
  cases condition <;> rfl

private def separateListProjections (body : Term) : Term :=
  .Apply (.Lam 0 (.Apply (.Lam 0 body)
    (.Apply (.Force (.Builtin .TailList)) (.Var 2))))
    (.Apply (.Force (.Builtin .HeadList)) (.Var 1))

private def fusedListProjections (body : Term) : Term :=
  .Case (.Var 1) [.Lam 0 (.Lam 0 body), .Error]

theorem list_cons_fusion (head : Moist.Plutus.Data) (tail : List Moist.Plutus.Data)
    (body : Term) (environment : CekEnv) (stack : Stack) :
    advance 22 (.compute stack (.cons (.VCon (.ConstDataList (head :: tail))) environment)
      (separateListProjections body)) =
    advance 7 (.compute stack (.cons (.VCon (.ConstDataList (head :: tail))) environment)
      (fusedListProjections body)) := by
  rfl

theorem list_nil_fusion (body : Term) (environment : CekEnv) (stack : Stack) :
    advance 10 (.compute stack (.cons (.VCon (.ConstDataList [])) environment)
      (separateListProjections body)) =
    advance 4 (.compute stack (.cons (.VCon (.ConstDataList [])) environment)
      (fusedListProjections body)) := by
  rfl

theorem pack_three_literal_arguments (first second third : Const × BuiltinType)
    (body : Term) (environment : CekEnv) (stack : Stack) :
    advance 15 (.compute stack environment
      (.Apply (.Apply (.Apply (.Lam 0 (.Lam 0 (.Lam 0 body))) (.Constant first))
        (.Constant second)) (.Constant third))) =
    advance 15 (.compute stack environment
      (.Case (.Constr 0 [.Constant first, .Constant second, .Constant third])
        [.Lam 0 (.Lam 0 (.Lam 0 body))])) := by
  rfl

theorem fold_binary_builtin (builtin : BuiltinFun) (first second result : Const)
    (firstType secondType resultType : BuiltinType)
    (environment : CekEnv) (stack : Stack)
    (signature : expectedArgs builtin = .more .argV (.one .argV))
    (evaluated : evalBuiltin builtin [.VCon second, .VCon first] = some (.VCon result)) :
    advance 9 (.compute stack environment
      (.Apply (.Apply (.Builtin builtin) (.Constant (first, firstType)))
        (.Constant (second, secondType)))) =
    advance 1 (.compute stack environment (.Constant (result, resultType))) := by
  simp [advance, step, signature, ExpectedArgs.head, ExpectedArgs.tail, evaluated]

theorem add_integer_zero (number : Int) (environment : CekEnv) (stack : Stack) :
    advance 9 (.compute stack (.cons (.VCon (.Integer number)) environment)
      (.Apply (.Apply (.Builtin .AddInteger) (.Var 1))
        (.Constant (.Integer 0, .AtomicType .TypeInteger)))) =
    advance 1 (.compute stack (.cons (.VCon (.Integer number)) environment) (.Var 1)) := by
  change State.ret stack (.VCon (.Integer (number + 0))) = State.ret stack (.VCon (.Integer number))
  rw [Int.add_zero]

theorem multiply_integer_one (number : Int) (environment : CekEnv) (stack : Stack) :
    advance 9 (.compute stack (.cons (.VCon (.Integer number)) environment)
      (.Apply (.Apply (.Builtin .MultiplyInteger) (.Var 1))
        (.Constant (.Integer 1, .AtomicType .TypeInteger)))) =
    advance 1 (.compute stack (.cons (.VCon (.Integer number)) environment) (.Var 1)) := by
  change State.ret stack (.VCon (.Integer (number * 1))) = State.ret stack (.VCon (.Integer number))
  rw [Int.mul_one]

theorem checked_integer_round_trip (number : Int) (environment : CekEnv) (stack : Stack) :
    advance 5 (.compute stack
      (.cons (.VCon (.Integer number)) (.cons (.VCon (.Data (.I number))) environment))
      (.Apply (.Builtin .IData) (.Var 1))) =
    advance 1 (.compute stack
      (.cons (.VCon (.Integer number)) (.cons (.VCon (.Data (.I number))) environment))
      (.Var 2)) := by
  rfl

theorem checked_bytes_round_trip (bytes : ByteArray) (environment : CekEnv) (stack : Stack) :
    advance 5 (.compute stack
      (.cons (.VCon (.ByteString bytes)) (.cons (.VCon (.Data (.B bytes))) environment))
      (.Apply (.Builtin .BData) (.Var 1))) =
    advance 1 (.compute stack
      (.cons (.VCon (.ByteString bytes)) (.cons (.VCon (.Data (.B bytes))) environment))
      (.Var 2)) := by
  rfl

theorem checked_list_round_trip (fields : List Moist.Plutus.Data)
    (environment : CekEnv) (stack : Stack) :
    advance 5 (.compute stack
      (.cons (.VCon (.ConstDataList fields)) (.cons (.VCon (.Data (.List fields))) environment))
      (.Apply (.Builtin .ListData) (.Var 1))) =
    advance 1 (.compute stack
      (.cons (.VCon (.ConstDataList fields)) (.cons (.VCon (.Data (.List fields))) environment))
      (.Var 2)) := by
  rfl

theorem checked_map_round_trip (fields : List (Moist.Plutus.Data × Moist.Plutus.Data))
    (environment : CekEnv) (stack : Stack) :
    advance 5 (.compute stack
      (.cons (.VCon (.ConstPairDataList fields)) (.cons (.VCon (.Data (.Map fields))) environment))
      (.Apply (.Builtin .MapData) (.Var 1))) =
    advance 1 (.compute stack
      (.cons (.VCon (.ConstPairDataList fields)) (.cons (.VCon (.Data (.Map fields))) environment))
      (.Var 2)) := by
  rfl

theorem repeated_boolean_case (condition : Bool) (whenFalse whenTrue unreachable : Term)
    (environment : CekEnv) (stack : Stack) :
    advance 6 (.compute stack (.cons (.VCon (.Bool condition)) environment)
      (.Case (.Var 1) [.Case (.Var 1) [whenFalse, unreachable],
        .Case (.Var 1) [unreachable, whenTrue]])) =
    advance 3 (.compute stack (.cons (.VCon (.Bool condition)) environment)
      (.Case (.Var 1) [whenFalse, whenTrue])) := by
  cases condition <;> rfl

theorem native_pair_first (first second : Const) (environment : CekEnv) (stack : Stack) :
    advance 9 (.compute stack (.cons (.VCon (.Pair (first, second))) environment)
      (.Apply (.Force (.Force (.Builtin .FstPair))) (.Var 1))) =
    advance 8 (.compute stack (.cons (.VCon (.Pair (first, second))) environment)
      (.Case (.Var 1) [.Lam 0 (.Lam 0 (.Var 2))])) := by
  rfl

theorem native_pair_second (first second : Const) (environment : CekEnv) (stack : Stack) :
    advance 9 (.compute stack (.cons (.VCon (.Pair (first, second))) environment)
      (.Apply (.Force (.Force (.Builtin .SndPair))) (.Var 1))) =
    advance 8 (.compute stack (.cons (.VCon (.Pair (first, second))) environment)
      (.Case (.Var 1) [.Lam 0 (.Lam 0 (.Var 1))])) := by
  rfl

theorem list_choice_cons (head : Moist.Plutus.Data) (tail : List Moist.Plutus.Data)
    (body empty : Term) (environment : CekEnv) (stack : Stack) :
    advance 31 (.compute stack (.cons (.VCon (.ConstDataList (head :: tail))) environment)
      (.Case (.Apply (.Force (.Builtin .NullList)) (.Var 1))
        [separateListProjections body, empty])) =
    advance 7 (.compute stack (.cons (.VCon (.ConstDataList (head :: tail))) environment)
      (.Case (.Var 1) [.Lam 0 (.Lam 0 body), empty])) := by
  rfl

theorem list_choice_nil (body empty : Term) (environment : CekEnv) (stack : Stack) :
    advance 9 (.compute stack (.cons (.VCon (.ConstDataList [])) environment)
      (.Case (.Apply (.Force (.Builtin .NullList)) (.Var 1))
        [body, empty])) =
    advance 3 (.compute stack (.cons (.VCon (.ConstDataList [])) environment)
      (.Case (.Var 1) [.Lam 0 (.Lam 0 body), empty])) := by
  rfl

theorem delayed_data_list_choice (fields : List Moist.Plutus.Data)
    (nonempty empty : Term) (environment : CekEnv) (stack : Stack) :
    advance 19 (.compute stack (.cons (.VCon (.ConstDataList fields)) environment)
      (.Force (.Apply (.Apply (.Apply (.Force (.Force (.Builtin .ChooseList)))
        (.Var 1)) (.Delay empty)) (.Delay nonempty)))) =
    advance 9 (.compute stack (.cons (.VCon (.ConstDataList fields)) environment)
      (.Case (.Apply (.Force (.Builtin .NullList)) (.Var 1)) [nonempty, empty])) := by
  cases fields <;> rfl

theorem delayed_generic_list_choice (fields : List Const)
    (nonempty empty : Term) (environment : CekEnv) (stack : Stack) :
    advance 19 (.compute stack (.cons (.VCon (.ConstList fields)) environment)
      (.Force (.Apply (.Apply (.Apply (.Force (.Force (.Builtin .ChooseList)))
        (.Var 1)) (.Delay empty)) (.Delay nonempty)))) =
    advance 9 (.compute stack (.cons (.VCon (.ConstList fields)) environment)
      (.Case (.Apply (.Force (.Builtin .NullList)) (.Var 1)) [nonempty, empty])) := by
  cases fields <;> rfl

theorem delayed_list_choice_value (value : CekValue)
    (nonempty empty : Term) (environment : CekEnv) (stack : Stack) :
    advance 19 (.compute stack (.cons value environment)
      (.Force (.Apply (.Apply (.Apply (.Force (.Force (.Builtin .ChooseList)))
        (.Var 1)) (.Delay empty)) (.Delay nonempty)))) =
    advance 9 (.compute stack (.cons value environment)
      (.Case (.Apply (.Force (.Builtin .NullList)) (.Var 1)) [nonempty, empty])) := by
  cases value with
  | VCon constant =>
    cases constant <;> first | rfl | (rename_i fields; cases fields <;> rfl)
  | _ => rfl

theorem checked_nonempty_list_fusion (head : Const) (tail : List Const)
    (body : Term) (environment : CekEnv) (stack : Stack) :
    advance 22 (.compute stack (.cons (.VCon (.ConstList (head :: tail))) environment)
      (separateListProjections body)) =
    advance 7 (.compute stack (.cons (.VCon (.ConstList (head :: tail))) environment)
      (.Case (.Var 1) [.Lam 0 (.Lam 0 body)])) := by
  rfl

end Moist.Verified.AdvancedRedexes
