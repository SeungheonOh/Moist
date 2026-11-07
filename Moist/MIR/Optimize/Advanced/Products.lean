import Moist.MIR.Optimize.Advanced.Facts
import Moist.MIR.Optimize.Advanced.Shapes
import Moist.MIR.Optimize.PreLower

namespace Moist.MIR.Advanced

open Moist.Plutus.Term

/-! Lower projections of positively known builtin pairs to native Case.
Projection-only bindings are unboxed once for their entire lexical scope.
A projection is an application whose function resolves, through the
let-bound facts of the walk, to forced `fstPair` or `sndPair`; this sees
through projection functions already shared by CSE. Unknown source
parameters never supply pair evidence. The producer remains strict, and fresh
component binders cannot capture deferred uses; bindings of projections
become aliases of the component binders, which pre-lowering then substitutes.
Whole-pair unboxing requires a projection on the first evaluation frontier.
A binding of a projection of a known pair, `let t = fst r`, is unboxed the
same way, with `t` an alias of the selected component. Unbound projections are
lowered to `case` only for literal projection heads: through a shared
projection function the `case` form saves a builtin call but takes two more
machine steps, so it costs more memory than the shared call.
Component binders are numbered from a counter above every identifier of the
program, threaded through the walk in evaluation order. The walk is skipped
when the freshened program is not well scoped.
-/

def knownProduct (environment : List (VarId × Expr)) (expression : Expr) : Bool :=
  match resolveHead 64 environment expression with
  | .App (.Builtin .UnConstrData) _ | .App (.App (.Builtin .MkPairData) _) _ => true
  | _ => false

def fstApp (x : VarId) : Expr := .App (.Force (.Force (.Builtin .FstPair))) (.Var x)
def sndApp (x : VarId) : Expr := .App (.Force (.Force (.Builtin .SndPair))) (.Var x)

/-- The pair projection a function resolves to: `true` for `fstPair`, `false`
    for `sndPair`. -/
def projectionKind (environment : List (VarId × Expr)) (function : Expr) : Option Bool :=
  match resolveHead 64 environment function with
  | .Force (.Force (.Builtin .FstPair)) => some true
  | .Force (.Force (.Builtin .SndPair)) => some false
  | _ => none

/-- `function argument` projects `binder`. -/
def projectsBinder (environment : List (VarId × Expr)) (binder : VarId) (function argument : Expr) :
    Bool :=
  match argument with
  | .Var other => other == binder && (projectionKind environment function).isSome
  | _ => false

/-- Every occurrence of `binder` is the argument of a pair projection. Let
    bindings extend the environment the projections are resolved in. -/
def projectionOnly (environment : List (VarId × Expr)) (binder : VarId) (expression : Expr) : Bool :=
  match expression with
  | .App function argument =>
    projectsBinder environment binder function argument ||
      (projectionOnly environment binder function && projectionOnly environment binder argument)
  | .Var other => binder != other
  | .Lam _ body => projectionOnly environment binder body
  | .Fix _ body => projectionOnly environment binder body
  | .Force body => projectionOnly environment binder body
  | .Delay body => projectionOnly environment binder body
  | .Constr _ fields => fields.attach.all fun ⟨field, _⟩ => projectionOnly environment binder field
  | .Case scrutinee alternatives =>
    projectionOnly environment binder scrutinee &&
      alternatives.attach.all fun ⟨alternative, _⟩ => projectionOnly environment binder alternative
  | .Let [] body => projectionOnly environment binder body
  | .Let ((name, rhs, _) :: rest) body =>
    projectionOnly environment binder rhs &&
      projectionOnly ((name, rhs) :: environment) binder (.Let rest body)
  | .Lit _ | .Builtin _ | .Error => true
termination_by exprSize expression
decreasing_by
  all_goals first
    | (simp only [exprSize, exprSizeBinds]; omega)
    | (simp only [exprSize, exprSizeBinds]; have := exprSize_pos rhs; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)

/-- Prepend a binding to a let, keeping multi-binding lets flat. -/
def consLet (binding : VarId × Expr × Bool) (expression : Expr) : Expr :=
  match expression with
  | .Let bindings body => .Let (binding :: bindings) body
  | other => .Let [binding] other

def replaceProjections (environment : List (VarId × Expr)) (binder first second : VarId)
    (expression : Expr) : Expr :=
  match expression with
  | .App function argument =>
    if projectsBinder environment binder function argument then
      if projectionKind environment function == some true then .Var first else .Var second
    else
      .App (replaceProjections environment binder first second function)
        (replaceProjections environment binder first second argument)
  | .Lam name body => .Lam name (replaceProjections environment binder first second body)
  | .Fix name body => .Fix name (replaceProjections environment binder first second body)
  | .Force body => .Force (replaceProjections environment binder first second body)
  | .Delay body => .Delay (replaceProjections environment binder first second body)
  | .Constr tag fields =>
    .Constr tag (fields.attach.map fun ⟨field, _⟩ =>
      replaceProjections environment binder first second field)
  | .Case scrutinee alternatives =>
    .Case (replaceProjections environment binder first second scrutinee)
      (alternatives.attach.map fun ⟨alternative, _⟩ =>
        replaceProjections environment binder first second alternative)
  | .Let [] body => .Let [] (replaceProjections environment binder first second body)
  | .Let ((name, rhs, erased) :: rest) body =>
    consLet (name, replaceProjections environment binder first second rhs, erased)
      (replaceProjections ((name, rhs) :: environment) binder first second (.Let rest body))
  | .Var _ | .Lit _ | .Builtin _ | .Error => expression
termination_by exprSize expression
decreasing_by
  all_goals first
    | (simp only [exprSize, exprSizeBinds]; omega)
    | (simp only [exprSize, exprSizeBinds]; have := exprSize_pos rhs; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)

/-! ## Size of the replaced suffix -/

theorem productList_attach_map (children : List Expr) (transform : Expr → Expr) :
    (children.attach.map fun ⟨child, _⟩ => transform child) = children.map transform := by
  induction children with
  | nil => rfl
  | cons child rest inductionHypothesis =>
    simp only [List.attach_cons, List.map_cons, List.map_map]
    congr 1

theorem productBinds_attach_map (bindings : List (VarId × Expr × Bool)) (transform : Expr → Expr) :
    (bindings.attach.map fun ⟨(name, rhs, erased), _⟩ => (name, transform rhs, erased)) =
      bindings.map fun (name, rhs, erased) => (name, transform rhs, erased) := by
  induction bindings with
  | nil => rfl
  | cons binding rest inductionHypothesis =>
    obtain ⟨name, rhs, erased⟩ := binding
    simp only [List.attach_cons, List.map_cons, List.map_map]
    congr 1

theorem exprSizeList_map_le (children : List Expr) (transform : Expr → Expr)
    (bound : ∀ child ∈ children, exprSize (transform child) ≤ exprSize child) :
    exprSizeList (children.map transform) ≤ exprSizeList children := by
  induction children with
  | nil => simp [exprSizeList]
  | cons child rest inductionHypothesis =>
    simp only [List.map_cons, exprSizeList]
    have head := bound child (.head _)
    have tail := inductionHypothesis fun c hc => bound c (.tail _ hc)
    omega

theorem exprSizeBinds_map_le (bindings : List (VarId × Expr × Bool)) (transform : Expr → Expr)
    (bound : ∀ binding ∈ bindings, exprSize (transform binding.2.1) ≤ exprSize binding.2.1) :
    exprSizeBinds (bindings.map fun (name, rhs, erased) => (name, transform rhs, erased)) ≤
      exprSizeBinds bindings := by
  induction bindings with
  | nil => simp [exprSizeBinds]
  | cons binding rest inductionHypothesis =>
    obtain ⟨name, rhs, erased⟩ := binding
    have head := bound (name, rhs, erased) (.head _)
    have tail := inductionHypothesis fun c hc => bound c (.tail _ hc)
    simp only [List.map_cons, exprSizeBinds] at head tail ⊢
    omega

theorem replaceProjections_let_shape (binder first second : VarId) :
    ∀ (bindings : List (VarId × Expr × Bool)) (body : Expr) (environment : List (VarId × Expr)),
      ∃ bindings' body', replaceProjections environment binder first second (.Let bindings body) =
        .Let bindings' body'
  | [], body, environment => ⟨[], _, by rw [replaceProjections]⟩
  | (name, rhs, erased) :: rest, body, environment => by
    obtain ⟨bindings', body', h⟩ :=
      replaceProjections_let_shape binder first second rest body ((name, rhs) :: environment)
    rw [replaceProjections, h]
    exact ⟨_, _, rfl⟩

theorem exprSize_replaceProjections (environment : List (VarId × Expr)) (binder first second : VarId)
    (expression : Expr) :
    exprSize (replaceProjections environment binder first second expression) ≤ exprSize expression := by
  unfold replaceProjections
  split
  · rename_i function argument
    split
    · split <;> simp [exprSize] <;> omega
    · have := exprSize_replaceProjections environment binder first second function
      have := exprSize_replaceProjections environment binder first second argument
      simp only [exprSize]; omega
  · rename_i name body
    have := exprSize_replaceProjections environment binder first second body
    simp only [exprSize]; omega
  · rename_i name body
    have := exprSize_replaceProjections environment binder first second body
    simp only [exprSize]; omega
  · rename_i body
    have := exprSize_replaceProjections environment binder first second body
    simp only [exprSize]; omega
  · rename_i body
    have := exprSize_replaceProjections environment binder first second body
    simp only [exprSize]; omega
  · rename_i tag fields
    have := exprSizeList_map_le fields (replaceProjections environment binder first second)
      fun child _ => exprSize_replaceProjections environment binder first second child
    rw [productList_attach_map]
    simp only [exprSize]; omega
  · rename_i scrutinee alternatives
    have := exprSize_replaceProjections environment binder first second scrutinee
    have := exprSizeList_map_le alternatives (replaceProjections environment binder first second)
      fun child _ => exprSize_replaceProjections environment binder first second child
    rw [productList_attach_map]
    simp only [exprSize]; omega
  · rename_i body
    have := exprSize_replaceProjections environment binder first second body
    simp only [exprSize, exprSizeBinds]; omega
  · rename_i name rhs erased rest body
    have hr := exprSize_replaceProjections environment binder first second rhs
    have hpos := exprSize_pos rhs
    have hs := exprSize_replaceProjections ((name, rhs) :: environment) binder first second
      (.Let rest body)
    obtain ⟨bindings', body', h⟩ :=
      replaceProjections_let_shape binder first second rest body ((name, rhs) :: environment)
    rw [h] at hs ⊢
    simp only [consLet, exprSize, exprSizeBinds] at hs ⊢
    omega
  all_goals exact Nat.le_refl _
termination_by exprSize expression
decreasing_by
  all_goals first
    | (subst_vars; simp only [exprSize, exprSizeBinds]; omega)
    | (subst_vars; simp only [exprSize, exprSizeBinds]; have := exprSize_pos rhs; omega)
    | (subst_vars; have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)

/-- The argument of a projection, and whether the projection is `fstPair`. -/
def projectedArgument (environment : List (VarId × Expr)) : Expr → Option (Expr × Bool)
  | .App function argument => (projectionKind environment function).map (argument, ·)
  | _ => none

theorem projectedArgument_some {environment : List (VarId × Expr)} {rhs argument : Expr}
    {isFirst : Bool} (h : projectedArgument environment rhs = some (argument, isFirst)) :
    ∃ function, rhs = .App function argument ∧ projectionKind environment function = some isFirst := by
  cases rhs with
  | App function argument' =>
    simp only [projectedArgument, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨k, hk, rfl, rfl⟩ := h
    exact ⟨function, rfl, hk⟩
  | _ => simp [projectedArgument] at h

/-! ## The walk

`productWalk environment expression next` returns the rewritten expression and
the next unused component identifier. -/

mutual
  def productWalk (environment : List (VarId × Expr)) (expression : Expr) (next : Nat) : Expr × Nat :=
    match expression with
    | .Let [] body => productWalk environment body next
    | .Let ((binder, rhs, erased) :: rest) body =>
      let rhs' := productWalk environment rhs next
      let first : VarId := { uid := rhs'.2, origin := .gen, hint := "first" }
      let second : VarId := { uid := rhs'.2 + 1, origin := .gen, hint := "second" }
      let components := (second, sndApp binder) :: (first, fstApp binder) :: (binder, rhs'.1) ::
        environment
      if knownProduct environment rhs'.1 && firstEvaluationUse binder (.Let rest body) &&
          projectionOnly components binder (.Let rest body) then
        let suffix' := productWalk environment
          (replaceProjections components binder first second (.Let rest body)) (rhs'.2 + 2)
        (.Case rhs'.1 [.Lam first (.Lam second suffix'.1)], suffix'.2)
      else
        match hprojected : projectedArgument environment rhs with
        | some (argument, isFirst) =>
          let argument' := productWalk environment argument next
          if knownProduct environment argument'.1 then
            let first : VarId := { uid := argument'.2, origin := .gen, hint := "first" }
            let second : VarId := { uid := argument'.2 + 1, origin := .gen, hint := "second" }
            let suffix' := productWalk environment
              (.Let ((binder, .Var (if isFirst then first else second), erased) :: rest) body)
              (argument'.2 + 2)
            (.Case argument'.1 [.Lam first (.Lam second suffix'.1)], suffix'.2)
          else
            let suffix' := productWalk ((binder, rhs'.1) :: environment) (.Let rest body) rhs'.2
            (.Let [(binder, rhs'.1, erased)] suffix'.1, suffix'.2)
        | none =>
          let suffix' := productWalk ((binder, rhs'.1) :: environment) (.Let rest body) rhs'.2
          (.Let [(binder, rhs'.1, erased)] suffix'.1, suffix'.2)
    | .Lam binder body =>
      let body' := productWalk environment body next
      (.Lam binder body'.1, body'.2)
    | .Fix binder body =>
      let body' := productWalk environment body next
      (.Fix binder body'.1, body'.2)
    | .App function argument =>
      let function' := productWalk environment function next
      let argument' := productWalk environment argument function'.2
      let first : VarId := { uid := argument'.2, origin := .gen, hint := "first" }
      let second : VarId := { uid := argument'.2 + 1, origin := .gen, hint := "second" }
      match function'.1 with
      | .Force (.Force (.Builtin .FstPair)) =>
        if knownProduct environment argument'.1 then
          (.Case argument'.1 [.Lam first (.Lam second (.Var first))], argument'.2 + 2)
        else (.App function'.1 argument'.1, argument'.2)
      | .Force (.Force (.Builtin .SndPair)) =>
        if knownProduct environment argument'.1 then
          (.Case argument'.1 [.Lam first (.Lam second (.Var second))], argument'.2 + 2)
        else (.App function'.1 argument'.1, argument'.2)
      | _ => (.App function'.1 argument'.1, argument'.2)
    | .Force body =>
      let body' := productWalk environment body next
      (.Force body'.1, body'.2)
    | .Delay body =>
      let body' := productWalk environment body next
      (.Delay body'.1, body'.2)
    | .Constr tag fields =>
      let fields' := productWalkList environment fields next
      (.Constr tag fields'.1, fields'.2)
    | .Case scrutinee alternatives =>
      let scrutinee' := productWalk environment scrutinee next
      let alternatives' := productWalkList environment alternatives scrutinee'.2
      (.Case scrutinee'.1 alternatives'.1, alternatives'.2)
    | .Var _ | .Lit _ | .Builtin _ | .Error => (expression, next)
  termination_by 2 * exprSize expression
  decreasing_by
    all_goals first
      | (simp only [exprSize, exprSizeBinds]; omega)
      | (simp only [exprSize, exprSizeBinds]; have := exprSize_pos rhs; omega)
      | (obtain ⟨function, rfl, _⟩ := projectedArgument_some hprojected
         simp only [exprSize, exprSizeBinds]; have := exprSize_pos function; omega)
      | (apply Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 (exprSize_replaceProjections _ _ _ _ _))
         simp only [exprSize, exprSizeBinds]; have := exprSize_pos rhs; omega)

  def productWalkList (environment : List (VarId × Expr)) (expressions : List Expr) (next : Nat) :
      List Expr × Nat :=
    match expressions with
    | [] => ([], next)
    | expression :: rest =>
      let expression' := productWalk environment expression next
      let rest' := productWalkList environment rest expression'.2
      (expression'.1 :: rest'.1, rest'.2)
  termination_by 2 * exprSizeList expressions + 1
  decreasing_by
    all_goals (simp only [exprSizeList]; have := exprSize_pos expression; omega)
end

def destructureProducts (expression : Expr) : Expr :=
  let prepared := uniqueOptimizationBinders expression
  preLowerInlineExpr
    (if wellScoped prepared then (productWalk [] prepared (maxUidExpr prepared + 1)).1 else prepared)

end Moist.MIR.Advanced
