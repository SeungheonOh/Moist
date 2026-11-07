import Moist.MIR.Optimize.Advanced.Products

namespace Moist.MIR.Advanced

open Moist.Plutus.Term

/-! # Unpacking records once

A field read of an SOP record is `case r [λf₁…fₙ. fᵢ]`. When `r` is read
several times, the reads are replaced by the field binders of one
`case r [λy₁…yₙ. body]` placed at the lowest node that holds all of them.

Unpacking early is only sound when `r` is known to be constructor `0` with
exactly `n` fields: a constructor with fewer fields gives a partial
application rather than an error, and integer, Boolean, unit, list and pair
constants also select the first alternative. Field reads therefore never
justify the rewrite on their own; `shapeOf` supplies the shape.

`shapeOf` describes what an expression returns whenever it returns: an
error returns nothing, a constructor returns its tag and the shapes of its
fields, a binding is resolved through the recorded right-hand sides, a
`case` returns what its alternatives return (a field binder of a constructor
whose arity at that tag is known returns that field), and a forced
`ifThenElse` or `chooseList` returns one of its delayed arguments.

The walk records the right-hand side of every binding it enters, and the
binders of a `case` alternative whose scrutinee has a known arity at that
tag as projections of the scrutinee. Field binders are numbered above every
identifier of the program and recorded as the fields they hold.
-/

inductive Shape where
  | any
  | none
  | constr (tag : Nat) (fields : List Shape)
  | union (left right : Shape)
  deriving Inhabited

/-- What a shape says about the fields of one constructor tag. -/
inductive TagFields where
  | unknown
  | unreachable
  | fields (shapes : List Shape)

def TagFields.merge : TagFields → TagFields → TagFields
  | .unknown, _ => .unknown
  | .unreachable, .unknown => .unknown
  | .unreachable, other => other
  | .fields _, .unknown => .unknown
  | .fields left, .unreachable => .fields left
  | .fields left, .fields right =>
    if left.length == right.length then .fields (List.zipWith .union left right) else .unknown

def Shape.atTag (tag : Nat) : Shape → TagFields
  | .any => .unknown
  | .none => .unreachable
  | .constr other fields => if other == tag then .fields fields else .unreachable
  | .union left right => (left.atTag tag).merge (right.atTag tag)

def Shape.tagZeroOnly : Shape → Bool
  | .any => false
  | .none => true
  | .constr tag _ => tag == 0
  | .union left right => left.tagZeroOnly && right.tagZeroOnly

/-- Every value of the shape is constructor `0` with exactly `arity` fields. -/
def Shape.isRecord (arity : Nat) (shape : Shape) : Bool :=
  shape.tagZeroOnly && match shape.atTag 0 with
    | .fields shapes => shapes.length == arity
    | .unreachable => true
    | .unknown => false

/-- `count` leading lambdas: their binders and the body below them. -/
def stripLams : Nat → Expr → Option (List VarId × Expr)
  | 0, body => some ([], body)
  | count + 1, .Lam binder body =>
    (stripLams count body).map fun (binders, inner) => (binder :: binders, inner)
  | _ + 1, _ => none

def lambdas : List VarId → Expr → Expr
  | [], body => body
  | binder :: binders, body => .Lam binder (lambdas binders body)

/-- The field bound to `x` by `λ binders. …`, counted from the outermost. -/
def fieldOf (binders : List VarId) (x : VarId) : Option Nat :=
  (envLookupT binders.reverse x).map fun index => binders.length - 1 - index

def hideBinders (binders : List VarId) (facts : List (VarId × Expr)) : List (VarId × Expr) :=
  facts.filter fun entry => !binders.contains entry.1

/-- An alternative that is not a lambda returns its own value, or fails
    when that value is a constructor applied to fields. -/
def plainAlternativeShape (recur : List (VarId × Expr) → Expr → Shape)
    (facts : List (VarId × Expr)) (alternative : Expr) : Shape :=
  match alternative with
  | .Lam _ _ => .any
  | _ => recur facts alternative

/-- What one alternative returns, given the shape of the scrutinee. -/
def alternativeShape (recur : List (VarId × Expr) → Expr → Shape) (listScrutinee : Bool)
    (facts : List (VarId × Expr)) (scrutinee : Shape) (tag : Nat) (alternative : Expr) : Shape :=
  match scrutinee.atTag tag with
  | .unreachable => .none
  | .fields shapes =>
    match stripLams shapes.length alternative with
    | some (binders, body) =>
      match body with
      | .Var x =>
        match fieldOf binders x with
        | some field => shapes.getD field .any
        | none => recur (hideBinders binders facts) body
      | _ => recur (hideBinders binders facts) body
    | none => plainAlternativeShape recur facts alternative
  | .unknown =>
    match alternative with
    | .Lam head (.Lam tail body) =>
      if listScrutinee && tag == 0 then recur (hideBinders [head, tail] facts) body else .any
    | _ => plainAlternativeShape recur facts alternative

def alternativesShape (recur : List (VarId × Expr) → Expr → Shape) (listScrutinee : Bool)
    (facts : List (VarId × Expr)) (scrutinee : Shape) : Nat → List Expr → Shape
  | _, [] => .none
  | tag, alternative :: rest =>
    .union (alternativeShape recur listScrutinee facts scrutinee tag alternative)
      (alternativesShape recur listScrutinee facts scrutinee (tag + 1) rest)

/-- The shape of whatever `expression` returns. `depth` bounds how many
    constructor levels record field shapes. -/
def shapeOf : Nat → Nat → List (VarId × Expr) → Expr → Shape
  | 0, _, _, _ => .any
  | fuel + 1, depth, facts, expression =>
    match expression with
    | .Error => .none
    | .Constr tag fields =>
      match depth with
      | 0 => .constr tag (fields.map fun _ => .any)
      | depth' + 1 => .constr tag (fields.map (shapeOf fuel depth' facts))
    | .Var x =>
      match facts.find? (fun entry => entry.1 == x) with
      | some entry => shapeOf fuel depth facts entry.2
      | none => .any
    | .Let bindings body =>
      shapeOf fuel depth
        (bindings.foldl (fun available (binder, rhs, _) => (binder, rhs) :: available) facts) body
    | .Case scrutinee alternatives =>
      alternativesShape (shapeOf fuel depth) (knownList fuel facts scrutinee) facts
        (shapeOf fuel depth facts scrutinee) 0 alternatives
    | .Force body =>
      match resolveHead fuel facts body with
      | .Delay delayed => shapeOf fuel depth facts delayed
      | .App (.App (.App selector _) (.Delay first)) (.Delay second) =>
        if selector == .Force (.Builtin .IfThenElse) ||
            selector == .Force (.Force (.Builtin .ChooseList)) then
          .union (shapeOf fuel depth facts first) (shapeOf fuel depth facts second)
        else .any
      | _ => .any
    | _ => .any

def recordFuel : Nat := 64
def recordDepth : Nat := 2

def knownRecord (facts : List (VarId × Expr)) (record : VarId) (arity : Nat) : Bool :=
  0 < arity && (shapeOf recordFuel recordDepth facts (.Var record)).isRecord arity

/-! ## Field reads -/

/-- `case record [λ binders. x]`: the record, the arity and the field read. -/
def fieldRead : Expr → Option (VarId × Nat × Nat)
  | .Case (.Var record) [alternative] =>
    match resultParameters alternative with
    | (binders, .Var x) =>
      if binders.isEmpty then none
      else (fieldOf binders x).map fun field => (record, binders.length, field)
    | _ => none
  | _ => none

/-- The field of `record` read by `expression`, at the given arity. -/
def readOf (record : VarId) (arity : Nat) (expression : Expr) : Option Nat :=
  match fieldRead expression with
  | some (other, count, field) => if other == record && count == arity then some field else none
  | none => none

def countReads (record : VarId) (arity : Nat) (expression : Expr) : Nat :=
  match readOf record arity expression with
  | some _ => 1
  | none =>
    match expression with
    | .Lam _ body | .Fix _ body | .Force body | .Delay body => countReads record arity body
    | .App function argument => countReads record arity function + countReads record arity argument
    | .Constr _ fields => (fields.attach.map fun ⟨field, _⟩ => countReads record arity field).sum
    | .Case scrutinee alternatives =>
      countReads record arity scrutinee +
        (alternatives.attach.map fun ⟨alternative, _⟩ => countReads record arity alternative).sum
    | .Let bindings body =>
      (bindings.attach.map fun ⟨(_, rhs, _), _⟩ => countReads record arity rhs).sum +
        countReads record arity body
    | .Var _ | .Lit _ | .Builtin _ | .Error => 0
termination_by exprSize expression
decreasing_by
  all_goals first
    | (simp only [exprSize]; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)
    | (have := exprSizeBinds_mem_lt (by assumption)
       simp only [exprSize] at *; omega)

/-- The arity of the first field read of `record`. -/
def readArity (record : VarId) (expression : Expr) : Option Nat :=
  match fieldRead expression with
  | some (other, count, _) => if other == record then some count else none
  | none =>
    match expression with
    | .Lam _ body | .Fix _ body | .Force body | .Delay body => readArity record body
    | .App function argument => (readArity record function).or (readArity record argument)
    | .Constr _ fields => fields.attach.findSome? fun ⟨field, _⟩ => readArity record field
    | .Case scrutinee alternatives =>
      (readArity record scrutinee).or
        (alternatives.attach.findSome? fun ⟨alternative, _⟩ => readArity record alternative)
    | .Let bindings body =>
      (bindings.attach.findSome? fun ⟨(_, rhs, _), _⟩ => readArity record rhs).or
        (readArity record body)
    | .Var _ | .Lit _ | .Builtin _ | .Error => none
termination_by exprSize expression
decreasing_by
  all_goals first
    | (simp only [exprSize]; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)
    | (have := exprSizeBinds_mem_lt (by assumption)
       simp only [exprSize] at *; omega)

/-- Replace every read of `record` at arity `fields.length` by its field binder. -/
def replaceReads (record : VarId) (fields : List VarId) (expression : Expr) : Expr :=
  match expression with
  | .Case scrutinee alternatives =>
    match readOf record fields.length expression with
    | some field => .Var (fields.getD field record)
    | none =>
      .Case (replaceReads record fields scrutinee)
        (alternatives.attach.map fun ⟨alternative, _⟩ => replaceReads record fields alternative)
  | .Lam binder body => .Lam binder (replaceReads record fields body)
  | .Fix binder body => .Fix binder (replaceReads record fields body)
  | .Force body => .Force (replaceReads record fields body)
  | .Delay body => .Delay (replaceReads record fields body)
  | .App function argument =>
    .App (replaceReads record fields function) (replaceReads record fields argument)
  | .Constr tag fieldExprs =>
    .Constr tag (fieldExprs.attach.map fun ⟨field, _⟩ => replaceReads record fields field)
  | .Let bindings body =>
    .Let (bindings.attach.map fun ⟨(binder, rhs, erased), _⟩ =>
        (binder, replaceReads record fields rhs, erased))
      (replaceReads record fields body)
  | .Var _ | .Lit _ | .Builtin _ | .Error => expression
termination_by exprSize expression
decreasing_by
  all_goals first
    | (simp only [exprSize]; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)
    | (have := exprSizeBinds_mem_lt (by assumption)
       simp only [exprSize] at *; omega)

theorem exprSize_replaceReads (record : VarId) (fields : List VarId) (expression : Expr) :
    exprSize (replaceReads record fields expression) ≤ exprSize expression := by
  unfold replaceReads
  split
  · rename_i scrutinee alternatives
    split
    · simp only [exprSize]; omega
    · have := exprSize_replaceReads record fields scrutinee
      have := exprSizeList_map_le alternatives (replaceReads record fields)
        fun child _ => exprSize_replaceReads record fields child
      rw [productList_attach_map]
      simp only [exprSize]; omega
  · rename_i binder body
    have := exprSize_replaceReads record fields body
    simp only [exprSize]; omega
  · rename_i binder body
    have := exprSize_replaceReads record fields body
    simp only [exprSize]; omega
  · rename_i body
    have := exprSize_replaceReads record fields body
    simp only [exprSize]; omega
  · rename_i body
    have := exprSize_replaceReads record fields body
    simp only [exprSize]; omega
  · rename_i function argument
    have := exprSize_replaceReads record fields function
    have := exprSize_replaceReads record fields argument
    simp only [exprSize]; omega
  · rename_i tag fieldExprs
    have := exprSizeList_map_le fieldExprs (replaceReads record fields)
      fun child _ => exprSize_replaceReads record fields child
    rw [productList_attach_map]
    simp only [exprSize]; omega
  · rename_i bindings body
    have := exprSize_replaceReads record fields body
    have := exprSizeBinds_map_le bindings (replaceReads record fields)
      fun binding _ => exprSize_replaceReads record fields binding.2.1
    rw [productBinds_attach_map]
    simp only [exprSize] at *; omega
  all_goals exact Nat.le_refl _
termination_by exprSize expression
decreasing_by
  all_goals first
    | (subst_vars; simp only [exprSize]; omega)
    | (subst_vars; have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)
    | (subst_vars; have := exprSizeBinds_mem_lt (by assumption); simp only [exprSize] at *; omega)

theorem stripLams_size : ∀ (count : Nat) (expression : Expr) (binders : List VarId) (body : Expr),
    stripLams count expression = some (binders, body) →
      binders.length = count ∧ exprSize body + count ≤ exprSize expression
  | 0, expression, binders, body, h => by
    simp only [stripLams, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | count + 1, .Lam binder inner, binders, body, h => by
    simp only [stripLams] at h
    cases hs : stripLams count inner with
    | none => rw [hs] at h; cases h
    | some result =>
      obtain ⟨binders', body'⟩ := result
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hlen, hsize⟩ := stripLams_size count inner binders' body' hs
      simp only [List.length_cons, exprSize]
      omega
  | _ + 1, .Var _, _, _, h | _ + 1, .Lit _, _, _, h | _ + 1, .Builtin _, _, _, h
  | _ + 1, .Error, _, _, h | _ + 1, .Fix _ _, _, _, h | _ + 1, .App _ _, _, _, h
  | _ + 1, .Force _, _, _, h | _ + 1, .Delay _, _, _, h | _ + 1, .Constr _ _, _, _, h
  | _ + 1, .Case _ _, _, _, h | _ + 1, .Let _ _, _, _, h => by simp [stripLams] at h

/-! ## Recorded facts -/

/-- `n` field binders numbered from `next`. -/
def freshFields (next count : Nat) : List VarId :=
  (List.range count).map fun index => { uid := next + index, origin := .gen, hint := "field" }

/-- The field held by `field`: an expression that returns it exactly when
    `record` is a constructor `0` (or a constant selecting the first
    alternative) with as many fields as `fields`. -/
def fieldProjection (record : VarId) (fields : List VarId) (field : VarId) : Expr :=
  .Case (.Case (.Var record) [lambdas fields (.Constr 0 [.Var field])]) [.Lam field (.Var field)]

def fieldFacts (record : VarId) (fields : List VarId) : List (VarId × Expr) :=
  fields.reverse.map fun field => (field, fieldProjection record fields field)

/-- The binder `x` of alternative `tag`, as a projection of the scrutinee. -/
def alternativeProjection (scrutinee : Expr) (tag : Nat) (binders : List VarId) (x : VarId) : Expr :=
  .Case scrutinee (List.replicate tag .Error ++ [lambdas binders (.Var x)])

def alternativeFacts (scrutinee : Expr) (tag : Nat) (binders : List VarId) : List (VarId × Expr) :=
  binders.reverse.map fun x => (x, alternativeProjection scrutinee tag binders x)

/-! ## Candidates and placement -/

/-- A binder read at least twice whose recorded shape is a record. -/
def recordCandidate (facts : List (VarId × Expr)) (binder : VarId) (scope : Expr) :
    List (VarId × Nat) :=
  match readArity binder scope with
  | some arity =>
    if 2 ≤ countReads binder arity scope && knownRecord facts binder arity then [(binder, arity)] else []
  | none => []

def recordCandidates (facts : List (VarId × Expr)) (binders : List VarId) (scope : Expr) :
    List (VarId × Nat) :=
  binders.flatMap fun binder => recordCandidate facts binder scope

def readChildren : Expr → List Expr
  | .Let [] body => [body]
  | .Let ((_, rhs, _) :: rest) body => [rhs, .Let rest body]
  | .Lam _ body | .Fix _ body | .Force body | .Delay body => [body]
  | .App function argument => [function, argument]
  | .Constr _ fields => fields
  | .Case scrutinee alternatives => scrutinee :: alternatives
  | .Var _ | .Lit _ | .Builtin _ | .Error => []

/-- The reads of a candidate are spread over several children. -/
def splitsAt (expression : Expr) (candidate : VarId × Nat) : Bool :=
  2 ≤ ((readChildren expression).filter fun child => countReads candidate.1 candidate.2 child != 0).length

/-- The candidates still read at least twice inside `child`. -/
def keepFor (candidates : List (VarId × Nat)) (child : Expr) : List (VarId × Nat) :=
  candidates.filter fun candidate => 2 ≤ countReads candidate.1 candidate.2 child

/-! ## The walk -/

mutual
  def recordWalk (facts : List (VarId × Expr)) (candidates : List (VarId × Nat)) (expression : Expr)
      (next : Nat) : Expr × Nat :=
    recordUnpack facts (candidates.filter (splitsAt expression))
      (candidates.filter fun candidate => !splitsAt expression candidate) expression next
  termination_by (exprSize expression, 2, 0)

  def recordUnpack (facts : List (VarId × Expr)) (todo candidates : List (VarId × Nat))
      (expression : Expr) (next : Nat) : Expr × Nat :=
    match todo with
    | [] => recordDescend facts candidates expression next
    | (record, arity) :: rest =>
      if knownRecord facts record arity then
        let fields := freshFields next arity
        let inner := recordUnpack (fieldFacts record fields ++ facts) rest candidates
          (replaceReads record fields expression) (next + arity)
        (.Case (.Var record) [lambdas fields inner.1], inner.2)
      else recordUnpack facts rest candidates expression next
  termination_by (exprSize expression, 1, todo.length)
  decreasing_by
    all_goals first
      | (have := exprSize_replaceReads record (freshFields next arity) expression
         rcases Nat.lt_or_eq_of_le this with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (Prod.Lex.right _ (by simp)))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by simp))
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))

  def recordDescend (facts : List (VarId × Expr)) (candidates : List (VarId × Nat)) (expression : Expr)
      (next : Nat) : Expr × Nat :=
    match expression with
    | .Let [] body => recordWalk facts (keepFor candidates body) body next
    | .Let ((binder, rhs, erased) :: rest) body =>
      let rhs' := recordWalk facts (keepFor candidates rhs) rhs next
      let facts' := (binder, rhs) :: facts
      let scope := Expr.Let rest body
      let rest' := recordWalk facts'
        (recordCandidate facts' binder scope ++ keepFor candidates scope) scope rhs'.2
      (.Let [(binder, rhs'.1, erased)] rest'.1, rest'.2)
    | .Lam binder body =>
      let body' := recordWalk facts (keepFor candidates body) body next
      (.Lam binder body'.1, body'.2)
    | .Fix binder body =>
      let body' := recordWalk facts (keepFor candidates body) body next
      (.Fix binder body'.1, body'.2)
    | .Force body =>
      let body' := recordWalk facts (keepFor candidates body) body next
      (.Force body'.1, body'.2)
    | .Delay body =>
      let body' := recordWalk facts (keepFor candidates body) body next
      (.Delay body'.1, body'.2)
    | .App function argument =>
      let function' := recordWalk facts (keepFor candidates function) function next
      let argument' := recordWalk facts (keepFor candidates argument) argument function'.2
      (.App function'.1 argument'.1, argument'.2)
    | .Constr tag fields =>
      let fields' := recordWalkList facts candidates fields next
      (.Constr tag fields'.1, fields'.2)
    | .Case scrutinee alternatives =>
      let scrutinee' := recordWalk facts (keepFor candidates scrutinee) scrutinee next
      let alternatives' := recordAlternatives facts candidates scrutinee
        (shapeOf recordFuel recordDepth facts scrutinee) 0 alternatives scrutinee'.2
      (.Case scrutinee'.1 alternatives'.1, alternatives'.2)
    | .Var _ | .Lit _ | .Builtin _ | .Error => (expression, next)
  termination_by (exprSize expression, 0, 0)
  decreasing_by
    all_goals first
      | (apply Prod.Lex.left; simp only [exprSize, exprSizeBinds]; omega)
      | (apply Prod.Lex.left; simp only [exprSize, exprSizeBinds]; have := exprSize_pos rhs; omega)

  def recordWalkList (facts : List (VarId × Expr)) (candidates : List (VarId × Nat))
      (expressions : List Expr) (next : Nat) : List Expr × Nat :=
    match expressions with
    | [] => ([], next)
    | expression :: rest =>
      have hsize : exprSize expression ≤ exprSizeList (expression :: rest) := by
        simp only [exprSizeList]; omega
      have hrest : exprSizeList rest < exprSizeList (expression :: rest) := by
        simp only [exprSizeList]; have := exprSize_pos expression; omega
      let expression' := recordWalk facts (keepFor candidates expression) expression next
      let rest' := recordWalkList facts candidates rest expression'.2
      (expression'.1 :: rest'.1, rest'.2)
  termination_by (exprSizeList expressions, 3, 0)
  decreasing_by
    all_goals first
      | exact Prod.Lex.left _ _ hrest
      | (rcases Nat.lt_or_eq_of_le hsize with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega)))

  def recordAlternatives (facts : List (VarId × Expr)) (candidates : List (VarId × Nat))
      (scrutinee : Expr) (shape : Shape) (tag : Nat) (alternatives : List Expr) (next : Nat) :
      List Expr × Nat :=
    match alternatives with
    | [] => ([], next)
    | alternative :: rest =>
      have hsize : exprSize alternative ≤ exprSizeList (alternative :: rest) := by
        simp only [exprSizeList]; omega
      have hrest : exprSizeList rest < exprSizeList (alternative :: rest) := by
        simp only [exprSizeList]; have := exprSize_pos alternative; omega
      let alternative' := recordAlternative facts candidates scrutinee shape tag alternative next
      let rest' := recordAlternatives facts candidates scrutinee shape (tag + 1) rest alternative'.2
      (alternative'.1 :: rest'.1, rest'.2)
  termination_by (exprSizeList alternatives, 4, 0)
  decreasing_by
    all_goals first
      | exact Prod.Lex.left _ _ hrest
      | (rcases Nat.lt_or_eq_of_le hsize with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega)))

  def recordAlternative (facts : List (VarId × Expr)) (candidates : List (VarId × Nat))
      (scrutinee : Expr) (shape : Shape) (tag : Nat) (alternative : Expr) (next : Nat) : Expr × Nat :=
    match shape.atTag tag with
    | .fields shapes =>
      match hstrip : stripLams shapes.length alternative with
      | some (binders, body) =>
        if 0 < shapes.length then
          let facts' := alternativeFacts scrutinee tag binders ++ facts
          let body' := recordWalk facts'
            (recordCandidates facts' binders body ++ keepFor candidates body) body next
          (lambdas binders body'.1, body'.2)
        else recordWalk facts (keepFor candidates alternative) alternative next
      | none => recordWalk facts (keepFor candidates alternative) alternative next
    | _ => recordWalk facts (keepFor candidates alternative) alternative next
  termination_by (exprSize alternative, 3, 0)
  decreasing_by
    all_goals first
      | (apply Prod.Lex.left
         have := (stripLams_size _ _ _ _ hstrip).2
         omega)
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
end

/-- Unpack every record read at least twice, once, at the lowest node that
    holds all of its reads. -/
def unpackRecords (expression : Expr) : Expr :=
  let prepared := uniqueOptimizationBinders expression
  preLowerInlineExpr
    (if wellScoped prepared then (recordWalk [] [] prepared (maxUidExpr prepared + 1)).1 else prepared)

end Moist.MIR.Advanced
