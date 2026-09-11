import Moist.Verified.ContinuationRefinement
import Moist.Verified.InlineSoundness.Totality
import Moist.Verified.AdvancedTraversal
import Moist.MIR.Optimize.Advanced.Allocations

namespace Moist.Verified.ApplicationPacking

open Moist.CEK Moist.Plutus.Term
open Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ContinuationRefinement
open Moist.Verified.InlineSoundness.Totality

def Returns (environment : CekEnv) (term : Term) (value : CekValue) : Prop :=
  ∀ stack, ∃ fuel, steps fuel (.compute stack environment term) = .ret stack value

def ArgumentsReturn (environment : CekEnv) : List Term → List CekValue → Prop
  | [], [] => True
  | term :: terms, value :: values => Returns environment term value ∧ ArgumentsReturn environment terms values
  | _, _ => False

theorem apply_argument (sourceStack targetStack : Stack)
    (continuations : ∀ value, TerminalRefines (.ret sourceStack value) (.ret targetStack value))
    (function argument : CekValue) :
    TerminalRefines (.ret (.funV function :: sourceStack) argument)
      (.ret (.applyArg argument :: targetStack) function) := by
  apply TerminalRefines.prefix 1 1
  cases function with
  | VLam body environment => exact compute_of_returns _ _ continuations (environment.extend argument) body
  | VBuiltin builtin arguments remaining =>
    simp only [steps, step]
    split
    · split
      · exact continuations _
      · split
        · exact continuations _
        · exact TerminalRefines.refl _
    · exact TerminalRefines.refl _
  | VCon _ | VDelay _ _ | VConstr _ _ => exact TerminalRefines.refl _

theorem argument_frames (environment : CekEnv) (terms : List Term) (values : List CekValue)
    (returns : ArgumentsReturn environment terms values) (stack : Stack) (function : CekValue) :
    TerminalRefines (.ret (terms.map (fun term => Frame.arg term environment) ++ stack) function)
      (.ret (values.map Frame.applyArg ++ stack) function) := by
  induction terms generalizing values function with
  | nil => cases values <;> simp_all [ArgumentsReturn, TerminalRefines.refl]
  | cons term terms inductionHypothesis =>
    cases values with
    | nil => cases returns
    | cons value values =>
      obtain ⟨headReturns, tailReturns⟩ := returns
      simp only [List.map_cons, List.cons_append]
      apply TerminalRefines.prefix 1 0
      change TerminalRefines (.compute (.funV function :: _) environment term) _
      obtain ⟨fuel, returned⟩ := headReturns (.funV function :: _)
      apply TerminalRefines.prefix fuel 0
      rw [returned]
      exact apply_argument _ _ (fun result => inductionHypothesis values tailReturns result) function value

theorem application_spine_steps (environment : CekEnv) (arguments : List Term)
    (function : Term) (stack : Stack) :
    steps arguments.length (.compute stack environment (arguments.foldl Term.Apply function)) =
      .compute (arguments.map (fun term => Frame.arg term environment) ++ stack) environment function := by
  induction arguments generalizing function stack with
  | nil => rfl
  | cons argument arguments inductionHypothesis =>
    simp only [List.foldl_cons, List.length_cons]
    rw [steps_trans, inductionHypothesis]
    rfl

theorem constructor_tail_returns (environment : CekEnv) (terms : List Term) (values : List CekValue)
    (returns : ArgumentsReturn environment terms values) (tag : Nat) (done : List CekValue)
    (value : CekValue) (stack : Stack) :
    ∃ fuel, steps fuel (.ret (.constrField tag done terms environment :: stack) value) =
      .ret stack (.VConstr tag ((value :: done).reverse ++ values)) := by
  induction terms generalizing values done value with
  | nil =>
    cases values with
    | nil => exact ⟨1, by simp [steps, step]⟩
    | cons _ _ => cases returns
  | cons term terms inductionHypothesis =>
    cases values with
    | nil => cases returns
    | cons head values =>
      obtain ⟨headReturns, tailReturns⟩ := returns
      obtain ⟨headFuel, headReturns⟩ := headReturns (.constrField tag (value :: done) terms environment :: stack)
      obtain ⟨tailFuel, tailReturns⟩ := inductionHypothesis values tailReturns (value :: done) head
      refine ⟨1 + (headFuel + tailFuel), ?_⟩
      rw [steps_trans]
      change steps (headFuel + tailFuel) (.compute (.constrField tag (value :: done) terms environment :: stack)
        environment term) = _
      rw [steps_trans, headReturns, tailReturns]
      simp [List.reverse_cons, List.append_assoc]

theorem constructor_returns (environment : CekEnv) (terms : List Term) (values : List CekValue)
    (returns : ArgumentsReturn environment terms values) (tag : Nat) :
    Returns environment (.Constr tag terms) (.VConstr tag values) := by
  intro stack
  cases terms with
  | nil =>
    cases values with
    | nil => exact ⟨1, rfl⟩
    | cons _ _ => cases returns
  | cons term terms =>
    cases values with
    | nil => cases returns
    | cons value values =>
      obtain ⟨headReturns, tailReturns⟩ := returns
      obtain ⟨headFuel, headReturns⟩ := headReturns (.constrField tag [] terms environment :: stack)
      obtain ⟨tailFuel, tailReturns⟩ := constructor_tail_returns environment terms values tailReturns tag [] value stack
      refine ⟨1 + (headFuel + tailFuel), ?_⟩
      rw [steps_trans]
      change steps (headFuel + tailFuel) (.compute (.constrField tag [] terms environment :: stack)
        environment term) = _
      rw [steps_trans, headReturns, tailReturns]
      rfl

theorem pack_returns (environment : CekEnv) (arguments : List Term) (values : List CekValue)
    (returns : ArgumentsReturn environment arguments values) (function : Term) (stack : Stack) :
    TerminalRefines (.compute stack environment (arguments.foldl Term.Apply function))
      (.compute stack environment (.Case (.Constr 0 arguments) [function])) := by
  obtain ⟨fuel, constructorReturns⟩ := constructor_returns environment arguments values returns 0
    (.caseScrutinee [function] environment :: stack)
  apply TerminalRefines.prefix arguments.length (1 + (fuel + 1))
  rw [application_spine_steps]
  rw [steps_trans]
  change TerminalRefines _ (steps (fuel + 1) (.compute (.caseScrutinee [function] environment :: stack)
    environment (.Constr 0 arguments)))
  rw [steps_trans, constructorReturns]
  change TerminalRefines _ (.compute (values.map Frame.applyArg ++ stack) environment function)
  exact compute_of_returns _ _ (argument_frames environment arguments values returns stack) environment function

theorem total_arguments_return (environment : CekEnv) (depth : Nat) (arguments : List Term)
    (total : TotalTerms arguments) (closed : closedAtList depth arguments = true)
    (sized : Semantics.WellSizedEnv depth environment) :
    ∃ values, ArgumentsReturn environment arguments values := by
  induction arguments with
  | nil => exact ⟨[], trivial⟩
  | cons argument arguments inductionHypothesis =>
    cases total with
    | cons headTotal tailTotal =>
      simp only [closedAtList, Bool.and_eq_true] at closed
      obtain ⟨values, tailReturns⟩ := inductionHypothesis tailTotal closed.2
      obtain ⟨value, halts⟩ := headTotal.halts depth environment closed.1 sized
      refine ⟨value :: values, ?_, tailReturns⟩
      intro stack
      obtain ⟨fuel, returns⟩ := Purity.compute_to_ret_from_halt environment argument value stack halts
      refine ⟨fuel, ?_⟩
      have bridge : ∀ fuel state, steps fuel state = Semantics.steps fuel state := by
        intro fuel state
        induction fuel generalizing state with
        | zero => rfl
        | succ fuel inductionHypothesis => exact inductionHypothesis (step state)
      rw [bridge]
      exact returns

theorem closedAt_spine (depth : Nat) (function : Term) (arguments : List Term) :
    closedAt depth (arguments.foldl Term.Apply function) =
      (closedAt depth function && closedAtList depth arguments) := by
  induction arguments generalizing function with
  | nil => simp [closedAtList]
  | cons argument arguments inductionHypothesis =>
    simp [List.foldl, inductionHypothesis, closedAt, closedAtList, Bool.and_assoc]

theorem pack_contextual (depth : Nat) (function : Term) (arguments : List Term)
    (functionClosed : closedAt depth function = true)
    (argumentsClosed : closedAtList depth arguments = true) (total : TotalTerms arguments) :
    CtxRefines (arguments.foldl Term.Apply function) (.Case (.Constr 0 arguments) [function]) := by
  apply TermObsRefinesWF.soundness_refinesWF (d := depth)
  · intro budget index indexBound leftEnv rightEnv environments leftWellFormed leftLength
      rightWellFormed rightLength observation observationBound leftStack rightStack
      leftStackWellFormed rightStackWellFormed stacks
    have sourceClosed : closedAt depth (arguments.foldl Term.Apply function) = true := by
      rw [closedAt_spine, functionClosed, argumentsClosed]; rfl
    have selfRefinement := FundamentalRefinesWF.ftlr_wf depth _ sourceClosed
      budget index indexBound leftEnv rightEnv environments leftWellFormed leftLength
      rightWellFormed rightLength observation observationBound leftStack rightStack
      leftStackWellFormed rightStackWellFormed stacks
    have sized : Semantics.WellSizedEnv depth rightEnv := by
      intro position positive bound
      obtain ⟨value, lookup, _⟩ := BetaValueRefines.envWellFormed_lookup depth rightWellFormed positive bound
      exact ⟨value, lookup⟩
    obtain ⟨values, returns⟩ := total_arguments_return rightEnv depth arguments total argumentsClosed sized
    exact InlineSoundness.SubstRefinesExt.obsRefinesK_compose_obsRefines_right selfRefinement
      (pack_returns rightEnv arguments values returns function rightStack).obs
  · intro context sourceClosed
    obtain ⟨contextClosed, termClosed⟩ := (fill_closedAt_iff context _ 0).mp sourceClosed
    apply (fill_closedAt_iff context _ 0).mpr
    refine ⟨contextClosed, ?_⟩
    simpa [closedAt_spine, closedAt, closedAtList, Bool.and_comm] using termClosed

end Moist.Verified.ApplicationPacking

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced Moist.Plutus.Term
open Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.InlineSoundness.Totality

theorem lowerTotalExpr_spine (environment : List VarId) (function : Expr) (arguments : List Expr) :
    lowerTotalExpr environment (arguments.foldl Expr.App function) = (do
      let functionTerm ← lowerTotalExpr environment function
      let argumentTerms ← lowerTotalExprList environment arguments
      pure (argumentTerms.foldl Term.Apply functionTerm)) := by
  induction arguments generalizing function with
  | nil => simp [lowerTotalExprList_nil]
  | cons argument arguments inductionHypothesis =>
    simp only [List.foldl_cons, inductionHypothesis, lowerTotalExpr_app,
      lowerTotalExprList_cons, Option.bind_eq_bind]
    cases lowerTotalExpr environment function <;>
      cases lowerTotalExpr environment argument <;>
      cases lowerTotalExprList environment arguments <;> rfl

theorem lowerTotalExprList_total (environment : List VarId) (arguments : List Expr) (terms : List Term)
    (pure : arguments.all isPure = true) (lowered : lowerTotalExprList environment arguments = some terms) :
    TotalTerms terms := by
  induction arguments generalizing terms with
  | nil => simp [lowerTotalExprList, expandFixList, lowerTotalList] at lowered; subst terms; exact .nil
  | cons argument arguments inductionHypothesis =>
    simp only [List.all_cons, Bool.and_eq_true] at pure
    simp only [lowerTotalExprList, expandFixList, lowerTotalList, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at lowered
    obtain ⟨term, headLowered, terms, tailLowered, equal⟩ := lowered
    cases equal
    exact .cons (lowerTotal_total (expandFix argument) environment term
      (Purity.isPure_expandFix argument pure.1) headLowered)
      (inductionHypothesis terms pure.2 tailLowered)

theorem packApplicationSpine_refines (function : Expr) (arguments : List Expr)
    (pure : arguments.all isPure = true) :
    MIRCtxRefines (arguments.foldl Expr.App function) (.Case (.Constr 0 arguments) [function]) := by
  intro environment
  rw [lowerTotalExpr_spine, lowerTotalExpr_case_of_list, lowerTotalExpr_constr_of_list]
  simp only [lowerTotalExprList_cons, lowerTotalExprList_nil, Option.bind_eq_bind]
  cases functionLowered : lowerTotalExpr environment function with
  | none => simp
  | some functionTerm =>
    cases argumentsLowered : lowerTotalExprList environment arguments with
    | none => simp
    | some argumentTerms =>
      simp only [Option.bind_some, Option.map_some, Pure.pure]
      refine ⟨fun _ => rfl, ?_⟩
      exact ApplicationPacking.pack_contextual environment.length functionTerm argumentTerms
        (lowerTotalExpr_closedAt functionLowered)
        (lowerTotalList_closedAtList environment _ _ argumentsLowered)
        (lowerTotalExprList_total environment arguments argumentTerms pure argumentsLowered)

theorem applicationSpine_go_rebuild (expression : Expr) (arguments : List Expr) :
    (applicationSpine.go expression arguments).2.foldl Expr.App
      (applicationSpine.go expression arguments).1 = arguments.foldl Expr.App expression := by
  cases expression <;> try rfl
  case App function argument =>
    simpa only [applicationSpine.go, List.foldl_cons] using
      applicationSpine_go_rebuild function (argument :: arguments)
termination_by sizeOf expression

theorem applicationSpine_rebuild (expression : Expr) :
    (applicationSpine expression).2.foldl Expr.App (applicationSpine expression).1 = expression :=
  applicationSpine_go_rebuild expression []

theorem applicationSpine_go_size (expression : Expr) (arguments : List Expr) :
    exprSize (applicationSpine.go expression arguments).1 +
      exprSizeList (applicationSpine.go expression arguments).2 +
      (applicationSpine.go expression arguments).2.length =
    exprSize expression + exprSizeList arguments + arguments.length := by
  cases expression <;> try rfl
  case App function argument =>
    have previous := applicationSpine_go_size function (argument :: arguments)
    simp only [applicationSpine.go, exprSize, exprSizeList, List.length_cons] at *
    omega
termination_by sizeOf expression

theorem applicationSpine_go_nonempty (expression : Expr) (argument : Expr) (arguments : List Expr) :
    (applicationSpine.go expression (argument :: arguments)).2 ≠ [] := by
  cases expression <;> try simp [applicationSpine.go]
  case App function inner => exact applicationSpine_go_nonempty function inner (argument :: arguments)
termination_by sizeOf expression

theorem applicationSpine_smaller (function argument : Expr) :
    exprSize (applicationSpine (.App function argument)).1 < exprSize (.App function argument) ∧
      ∀ child ∈ (applicationSpine (.App function argument)).2, exprSize child < exprSize (.App function argument) := by
  have total := applicationSpine_go_size (.App function argument) []
  simp only [exprSizeList, List.length_nil, Nat.add_zero] at total
  change exprSize (applicationSpine (.App function argument)).1 +
    exprSizeList (applicationSpine (.App function argument)).2 +
    (applicationSpine (.App function argument)).2.length = exprSize (.App function argument) at total
  have nonempty : (applicationSpine (.App function argument)).2 ≠ [] :=
    applicationSpine_go_nonempty function argument []
  have positive := List.length_pos_iff.mpr nonempty
  constructor
  · omega
  · intro child member
    have bound := exprSize_member_le member
    omega

theorem spine_map_refines (transform : Expr → Expr)
    (sound : ∀ expression, MIRCtxRefines expression (transform expression))
    (function : Expr) (arguments : List Expr) :
    MIRCtxRefines (arguments.foldl Expr.App function)
      ((arguments.map transform).foldl Expr.App (transform function)) := by
  have general : ∀ (arguments : List Expr) (first second : Expr), MIRCtxRefines first second →
      MIRCtxRefines (arguments.foldl Expr.App first)
        ((arguments.map transform).foldl Expr.App second) := by
    intro arguments
    induction arguments with
    | nil => intros; assumption
    | cons argument arguments inductionHypothesis =>
      intro first second related
      exact inductionHypothesis _ _ (mirCtxRefines_app related (sound argument))
  exact general arguments function (transform function) (sound function)

theorem packApplicationsFuel_refines (minimum fuel : Nat) (expression : Expr) :
    MIRCtxRefines expression (packApplicationsFuel minimum fuel expression) := by
  induction fuel using Nat.strongRecOn generalizing expression with
  | ind fuel inductionHypothesis =>
    cases fuel with
    | zero => exact mirCtxRefines_refl _
    | succ fuel =>
      have childrenSound := inductionHypothesis fuel (by omega)
      cases expression with
      | App function argument =>
        let spine := applicationSpine (.App function argument)
        have rebuilt := applicationSpine_rebuild (.App function argument)
        apply mirCtxRefines_trans (m₂ := (spine.2.map (packApplicationsFuel minimum fuel)).foldl Expr.App
          (packApplicationsFuel minimum fuel spine.1))
        · rw [← rebuilt]
          exact spine_map_refines _ childrenSound spine.1 spine.2
        · simp only [packApplicationsFuel]
          split
          · rename_i accepted
            simp only [Bool.and_eq_true] at accepted
            exact packApplicationSpine_refines _ _ accepted.2
          · exact mirCtxRefines_refl _
      | Var _ | Lit _ | Builtin _ | Error => exact mirCtxRefines_refl _
      | Lam binder body => exact mirCtxRefines_lam (childrenSound body)
      | Force body => exact mirCtxRefines_force (childrenSound body)
      | Delay body => exact mirCtxRefines_delay (childrenSound body)
      | Constr tag fields =>
        cases fields with
        | nil => exact mirCtxRefines_refl _
        | cons field rest =>
          exact mirCtxRefines_constr (childrenSound field)
            (listRel_map_refines _ childrenSound rest)
      | Case scrutinee alternatives =>
        exact mirCtxRefines_case (childrenSound scrutinee)
          (listRel_map_refines _ childrenSound alternatives)
      | Let bindings body =>
        exact mirCtxRefines_trans
          (mirCtxRefines_let_binds_congr bindings _ body (bindings_map_refines _ childrenSound bindings))
          (mirCtxRefines_let_body (childrenSound body))
      | Fix binder body =>
        cases body with
        | Lam parameter inner =>
          cases fuel with
          | zero => exact mirCtxRefines_refl _
          | succ remaining => exact mirCtxRefines_fix_lam (inductionHypothesis remaining (by omega) inner)
        | Var _ | Lit _ | Builtin _ | Error | Fix _ _ | App _ _ | Force _ | Delay _
        | Constr _ _ | Case _ _ | Let _ _ =>
          exact fix_nonlam_refines (by intros; intro impossible; cases impossible)

theorem packApplications_refines (minimum : Nat) (expression : Expr) :
    MIRCtxRefines expression (packApplications minimum expression) :=
  packApplicationsFuel_refines minimum (exprSize expression) expression

def packApplicationsStep (minimum : Nat) (transform : Expr → Expr) (expression : Expr) : Expr :=
  match expression with
  | .App _ _ =>
    let (function, arguments) := applicationSpine expression
    let function' := transform function
    let arguments' := arguments.map transform
    if arguments'.length >= minimum && arguments'.all isPure then
      .Case (.Constr 0 arguments') [function']
    else arguments'.foldl Expr.App function'
  | _ => mapChildren transform expression

theorem packApplicationsFuel_succ (minimum fuel : Nat) (expression : Expr) :
    packApplicationsFuel minimum (fuel + 1) expression =
      packApplicationsStep minimum (packApplicationsFuel minimum fuel) expression := by
  cases expression <;> rfl

theorem packApplicationsStep_congr (minimum : Nat) (left right : Expr → Expr) (expression : Expr)
    (agree : ∀ child, exprSize child < exprSize expression → left child = right child) :
    packApplicationsStep minimum left expression = packApplicationsStep minimum right expression := by
  cases expression with
  | App function argument =>
    have bounds := applicationSpine_smaller function argument
    have heads := agree _ bounds.1
    have arguments : (applicationSpine (.App function argument)).2.map left =
        (applicationSpine (.App function argument)).2.map right := by
      apply List.map_congr_left
      intro child member
      exact agree child (bounds.2 child member)
    simp only [packApplicationsStep, heads, arguments]
  | _ => exact mapChildren_congr_size left right _ agree

theorem packApplicationsFuel_irrel (minimum : Nat) (expression : Expr)
    (leftFuel rightFuel : Nat) (leftBound : exprSize expression ≤ leftFuel)
    (rightBound : exprSize expression ≤ rightFuel) :
    packApplicationsFuel minimum leftFuel expression = packApplicationsFuel minimum rightFuel expression := by
  cases leftFuel with
  | zero => have positive := exprSize_positive expression; omega
  | succ leftFuel =>
    cases rightFuel with
    | zero => have positive := exprSize_positive expression; omega
    | succ rightFuel =>
      rw [packApplicationsFuel_succ, packApplicationsFuel_succ]
      apply packApplicationsStep_congr
      intro child smaller
      exact packApplicationsFuel_irrel minimum child leftFuel rightFuel (by omega) (by omega)
termination_by exprSize expression

theorem packApplications_recursive_eq (minimum : Nat) (expression : Expr) :
    packApplications minimum expression = packApplicationsStep minimum (packApplications minimum) expression := by
  unfold packApplications
  cases sizeEqual : exprSize expression with
  | zero => have positive := exprSize_positive expression; omega
  | succ fuel =>
    rw [packApplicationsFuel_succ]
    apply packApplicationsStep_congr
    intro child smaller
    exact packApplicationsFuel_irrel minimum child fuel (exprSize child) (by omega) (Nat.le_refl _)

theorem packApplications_unique (minimum : Nat) (candidate : Expr → Expr)
    (equation : ∀ expression, candidate expression = packApplicationsStep minimum candidate expression)
    (expression : Expr) : packApplications minimum expression = candidate expression := by
  rw [packApplications_recursive_eq, equation expression]
  apply packApplicationsStep_congr
  intro child smaller
  exact packApplications_unique minimum candidate equation child
termination_by exprSize expression

end Moist.Verified.MIR
