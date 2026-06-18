import Moist.Compile.Builtins
import Moist.CEK.Builtins

/-! # The symbolic evaluator `symEval` — `bigEval` over the symbolic value domain

`symEval` is `Moist.Verified.BigStep.bigEval` with the value domain swapped for `SymVal`
(carrying `SmtExpr`).  **Same recursion, same fuel, same five mutual functions, same
termination measure** — only three deltas (§4.2):

* **constants / builtins** produce `sCon (SmtExpr …)` (via `constToSmt`) instead of `VCon c`,
  and builtin saturation goes through `symEvalBuiltin`, conjoining a definedness guard;
* **`Apply`/`Force`/`Lam`/`Delay`/`Constr`** are *identical* to `bigEval` (defunctionalized
  closures) — all higher-order structure is eliminated at compile time;
* **`Case`** dispatches concretely on a statically-known constructor (`sConstr`), exactly
  like `bigEval`; a symbolic-`Data` scrutinee is the v1 symbolic-dispatch case (refused here).

Because the structure is a one-for-one mirror, the adequacy proof (`Compile/Adequacy.lean`)
is a tight fuel-induction simulation against `bigEval` rather than a from-scratch
denotational argument.  `symEval` returning `none` is always **sound refusal** (fuel
exhausted, an unsupported construct, or a genuine static UPLC error) — never a silent
under-approximation.

The `SymOut.defined` field accumulates (by conjunction) every partiality guard encountered,
so the top-level `defined` is `true` at a model `σ` **iff** the concrete UPLC evaluation on
the `σ`-instantiated inputs does not error.
-/

namespace Moist.Compile

open Moist.Plutus.Term (Term Const BuiltinType BuiltinFun)
open Moist.CEK (ExpectedArgs expectedArgs)
open Moist.Smt (SmtExpr)
open Moist.Smt.SmtExpr (andE trueE)

/-- Translate a UPLC constant to a *symbolic-capable* `SmtExpr` denotation: integers and
    booleans (which can combine with symbolic values via arithmetic/comparison).  Every other
    constant type is carried concretely as `sConst` (see `constToSym`). -/
def constToSmt : Const → Option SmtExpr
  | .Integer n => some (.litI n)
  | .Bool b    => some (.litB b)
  | _          => none

mutual
  /-- Translate a concrete `Plutus.Data` into the SMT `Data` term that denotes it — the
      *constructor* counterpart of `unConstrData`/`dArgs`/… so that a `con data …` literal
      becomes a first-order `sCon` that composes with the symbolic builtins (rather than an
      opaque `sConst`).  `I`/`B` inject via `iData`/`bData` (the `B` leaf via the `litBS`
      bytes literal); `Constr`/`List`/`Map` recurse through `mkConstrD`/`mkDList`/`mkMap`
      over lists built with `consL`/`nilL`. -/
  def dataToExpr : Moist.Plutus.Data → SmtExpr
    | .I n        => .uop .iData (.litI n)
    | .B b        => .uop .bData (.litBS b)
    | .Constr t f => .mkConstrD (.litI t) (dataListToExpr f)
    | .List ds    => .uop .mkDList (dataListToExpr ds)
    | .Map ps     => .uop .mkMap (dataPairListToExpr ps)
  /-- A `List Data` as an SMT `(Lst Data)` term (`lcons …/lnil`). -/
  def dataListToExpr : List Moist.Plutus.Data → SmtExpr
    | []      => .nilL .data
    | d :: ds => .consL (dataToExpr d) (dataListToExpr ds)
  /-- A `List (Data × Data)` as an SMT `(Lst (Pair Data Data))` term. -/
  def dataPairListToExpr : List (Moist.Plutus.Data × Moist.Plutus.Data) → SmtExpr
    | []           => .nilL (.pair .data .data)
    | (a, b) :: ps => .consL (.mkpair (dataToExpr a) (dataToExpr b)) (dataPairListToExpr ps)
end

/-- Translate *any* UPLC constant to a symbolic value.  `Integer`/`Bool`/`ByteString` ↦
    arithmetic / bytes `sCon` literals; `Data`/builtin lists ↦ first-order `sCon` SMT terms
    (so literals compose with the symbolic builtins — `mkCons (iData x) (con (list data) [])`,
    `equalsByteString (sha2_256 x) (con bytestring …)` etc.); every other constant type ↦
    `sConst`.  `γ σ (constToSym c) = VCon c` in all cases. -/
def constToSym (c : Const) : SymVal :=
  match c with
  | .Integer n    => .sCon (.litI n)
  | .Bool b       => .sCon (.litB b)
  | .ByteString b => .sCon (.litBS b)
  | .Data d       => .sCon (dataToExpr d)
  | .ConstDataList ds => .sCon (dataListToExpr ds)
  | _ => .sConst c

/-- Combine the two forced branches of a deferred `sIte` into an SMT `ite`.  A branch that
    failed (fuel exhausted, or not first-order) makes *that path* undefined — `ite cond … false`
    in the definedness flag — which is exactly what bounds the recursion unrolling soundly:
    inputs whose computation fits in the unrolled depth get a real value + `defined`; deeper
    inputs get `defined = false` (no claim). -/
def combineIte (cond : SmtExpr) : Option SymOut → Option SymOut → Option SymOut
  | some ⟨.sCon aE, aDef⟩, some ⟨.sCon bE, bDef⟩ =>
      some ⟨.sCon (.ite cond aE bE), .ite cond aDef bDef⟩            -- both first-order ⇒ SMT `ite`
  | some ⟨va, aDef⟩, some ⟨vb, bDef⟩ =>
      some ⟨.sIte cond va vb, .ite cond aDef bDef⟩                   -- non-first-order ⇒ keep the choice
  | some ⟨va, aDef⟩, none => some ⟨va, .ite cond aDef .falseE⟩       -- only the `then` path reached
  | none, some ⟨vb, bDef⟩ => some ⟨vb, .ite cond .falseE bDef⟩       -- only the `else` path reached
  | none, none => none

/-- Symbolic analogue of `Moist.CEK.constToTagAndFields`: a builtin constant scrutinee of a
    `Case` is dispatched as a sum-of-products value `(tag, #ctors, fields)`.  `VCon x` fields
    become `sConst x` (so `γ (sConst x) = VCon x` pointwise — the agreement is definitional).
    Mirrors the CEK table exactly (Bool: False=0/True=1; Unit=0; Integer n≥0 = tag n with 0
    ctors = unbounded; list Cons=0/Nil=1; Pair=0). -/
def symConstToTagFields : Const → Option (Nat × Nat × List SymVal)
  | .Bool false => some (0, 2, [])
  | .Bool true  => some (1, 2, [])
  | .Unit       => some (0, 1, [])
  | .Integer n  => if n ≥ 0 then some (n.toNat, 0, []) else none
  | .ConstList []          => some (1, 2, [])
  | .ConstList (h :: t)     => some (0, 2, [.sConst h, .sConst (.ConstList t)])
  | .ConstDataList []       => some (1, 2, [])
  | .ConstDataList (h :: t) => some (0, 2, [.sConst (.Data h), .sConst (.ConstDataList t)])
  | .Pair (a, b)     => some (0, 1, [.sConst a, .sConst b])
  | .PairData (a, b) => some (0, 1, [.sConst (.Data a), .sConst (.Data b)])
  | _ => none

mutual
  /-- Symbolic big-step evaluation of `t` in symbolic environment `ρ`.  Mirrors `bigEval`. -/
  def symEval : Nat → SymEnv → Term → Option SymOut
    | 0, _, _ => none
    | _ + 1, ρ, .Var k => (SymEnv.lookup ρ k).map (fun v => ⟨v, trueE⟩)
    | _ + 1, _, .Constant (c, _) => some ⟨constToSym c, trueE⟩
    | _ + 1, _, .Builtin b => some ⟨.sBuiltin b [] (expectedArgs b), trueE⟩
    | _ + 1, ρ, .Lam _ body => some ⟨.sLam body ρ, trueE⟩
    | _ + 1, ρ, .Delay body => some ⟨.sDelay body ρ, trueE⟩
    | n + 1, ρ, .Apply f a =>
        match symEval n ρ f with
        | some of =>
          match symEval n ρ a with
          | some oa =>
            match symApply n of.value oa.value with
            | some oap => some ⟨oap.value, andE of.defined (andE oa.defined oap.defined)⟩
            | none => none
          | none => none
        | none => none
    | n + 1, ρ, .Force t =>
        match symEval n ρ t with
        | some ot =>
          match symForce n ot.value with
          | some ofo => some ⟨ofo.value, andE ot.defined ofo.defined⟩
          | none => none
        | none => none
    | n + 1, ρ, .Constr tag ms =>
        match symEvalList n ρ ms with
        | some (vs, d) => some ⟨.sConstr tag vs, d⟩
        | none => none
    | n + 1, ρ, .Case scrut alts =>
        match symEval n ρ scrut with
        | some osc =>
          match osc.value with
          | .sConstr tag fields =>
            match alts[tag]? with
            | some alt =>
              match symEval n ρ alt with
              | some oalt =>
                match symApplyList n oalt.value fields with
                | some oap => some ⟨oap.value, andE osc.defined (andE oalt.defined oap.defined)⟩
                | none => none
              | none => none
            | none => none
          | .sIte _ _ _ =>
            -- scrutinee is a symbolic *choice* of constructors ⇒ distribute `Case` through it
            match symCase n ρ osc.value alts with
            | some oc => some ⟨oc.value, andE osc.defined oc.defined⟩
            | none => none
          | .sConst _ =>
            -- `Case` on a builtin *constant* (Bool/Unit/Integer/list/pair) — SOP dispatch
            match symCase n ρ osc.value alts with
            | some oc => some ⟨oc.value, andE osc.defined oc.defined⟩
            | none => none
          | .sCon _ =>
            -- `Case` on a (possibly symbolic) Bool/Integer scrutinee — `ite`-combination
            match symCase n ρ osc.value alts with
            | some oc => some ⟨oc.value, andE osc.defined oc.defined⟩
            | none => none
          | _ => none   -- a closure scrutinee ⇒ genuinely ill-typed ⇒ refuse
        | none => none
    | _ + 1, _, .Error => none
  termination_by n _ t => (n, sizeOf t)

  /-- Apply a symbolic value to an argument (β / builtin saturation).  Mirrors `applyVal`. -/
  def symApply : Nat → SymVal → SymVal → Option SymOut
    | 0, _, _ => none
    | n + 1, .sLam body ρ, va => symEval n (SymEnv.extend ρ va) body
    | _ + 1, .sBuiltin b args ea, va =>
        match ea.head with
        | .argV =>
          match ea.tail with
          | some rest => some ⟨.sBuiltin b (va :: args) rest, trueE⟩
          | none => symEvalBuiltin b (va :: args)
        | .argQ => none
    -- applying a symbolic *choice of functions* distributes: `(if c then f else g) a`
    -- ≡ `if c then (f a) else (g a)` (the `symApply` analogue of `symCase`)
    | n + 1, .sIte cond a b, va => combineIte cond (symApply n a va) (symApply n b va)
    | _ + 1, _, _ => none
  termination_by n _ _ => (n, 0)

  /-- Force a symbolic value (delay / builtin force).  Mirrors `forceVal`. -/
  def symForce : Nat → SymVal → Option SymOut
    | 0, _ => none
    | n + 1, .sDelay body ρ => symEval n ρ body
    | _ + 1, .sBuiltin b args ea =>
        match ea.head with
        | .argQ =>
          match ea.tail with
          | some rest => some ⟨.sBuiltin b args rest, trueE⟩
          | none => symEvalBuiltin b args
        | .argV => none
    -- forcing a deferred symbolic choice: evaluate BOTH branches, emit an SMT `ite`
    | n + 1, .sIte cond a b => combineIte cond (symForce n a) (symForce n b)
    | _ + 1, _ => none
  termination_by n _ => (n, 0)

  /-- Evaluate constructor fields left-to-right, conjoining their definedness.  Mirrors
      `bigEvalList`. -/
  def symEvalList : Nat → SymEnv → List Term → Option (List SymVal × SmtExpr)
    | _, _, [] => some ([], trueE)
    | n, ρ, t :: ts =>
        match symEval n ρ t with
        | some o =>
          match symEvalList n ρ ts with
          | some (vs, d) => some (o.value :: vs, andE o.defined d)
          | none => none
        | none => none
  termination_by n _ ts => (n, sizeOf ts)

  /-- Apply `vf` to a list of already-evaluated arguments left-to-right (a `Case` branch
      applied to the scrutinee's fields).  Mirrors `applyValList`. -/
  def symApplyList : Nat → SymVal → List SymVal → Option SymOut
    | _, vf, [] => some ⟨vf, trueE⟩
    | n, vf, a :: as =>
        match symApply n vf a with
        | some o =>
          match symApplyList n o.value as with
          | some o' => some ⟨o'.value, andE o.defined o'.defined⟩
          | none => none
        | none => none
  termination_by n _ vs => (n, sizeOf vs)

  /-- Dispatch a `Case` over a (possibly symbolic-choice) scrutinee value.  A concrete
      `sConstr` selects its alternative and applies it to the fields (as the inline `Case`
      clause does); a deferred `sIte` choice **distributes** — `Case (ite c x y) ≡
      ite c (Case x) (Case y)` — recursing to the concrete leaves and merging with
      `combineIte`.  Any other value (a symbolic constant, a closure) ⇒ refuse. -/
  def symCase : Nat → SymEnv → SymVal → List Term → Option SymOut
    | 0, _, _, _ => none
    | n + 1, ρ, .sConstr tag fields, alts =>
        match alts[tag]? with
        | some alt =>
          match symEval n ρ alt with
          | some oalt =>
            match symApplyList n oalt.value fields with
            | some oap => some ⟨oap.value, andE oalt.defined oap.defined⟩
            | none => none
          | none => none
        | none => none
    | n + 1, ρ, .sIte cond va vb, alts =>
        combineIte cond (symCase (n + 1) ρ va alts) (symCase (n + 1) ρ vb alts)
    | n + 1, ρ, .sConst c, alts =>
        -- builtin-constant scrutinee: SOP dispatch via `symConstToTagFields` (mirrors `bigEval`)
        match symConstToTagFields c with
        | some (tag, numCtors, fields) =>
            if numCtors > 0 && alts.length > numCtors then none
            else match alts[tag]? with
                 | some alt =>
                   match symEval n ρ alt with
                   | some oalt =>
                     match symApplyList n oalt.value fields with
                     | some oap => some ⟨oap.value, andE oalt.defined oap.defined⟩
                     | none => none
                   | none => none
                 | none => none
        | none => none
    | n + 1, ρ, .sCon e, alts =>
        match SmtExpr.sortOf e with
        | some .bool =>
            -- Bool scrutinee: False=tag 0, True=tag 1 (2 ctors, no fields) ⇒ `ite e alt₁ alt₀`
            if alts.length > 2 then none
            else combineIte e (match alts[1]? with | some a => symEval n ρ a | none => none)
                              (match alts[0]? with | some a => symEval n ρ a | none => none)
        | some .int =>
            -- Integer scrutinee: tag = the value (unbounded), no fields ⇒ nested `ite (e==i) altᵢ …`
            symCaseInt n ρ e 0 alts
        | some (.list .data) =>
            -- builtin list scrutinee: Cons=tag 0 (fields head/tail), Nil=tag 1 (no fields)
            if alts.length > 2 then none
            else combineIte (.nullL e)
                   (match alts[1]? with | some a => symEval n ρ a | none => none)   -- nil ⇒ tag 1
                   (match alts[0]? with                                              -- cons ⇒ tag 0
                    | some a =>
                      match symEval n ρ a with
                      | some oa =>
                        match symApplyList n oa.value [.sCon (.headL .data e), .sCon (.tailL e)] with
                        | some oap => some ⟨oap.value, andE oa.defined oap.defined⟩
                        | none => none
                      | none => none
                    | none => none)
        | some (.pair _ _) =>
            -- builtin pair scrutinee: a single ctor (tag 0) with fields fst/snd
            if alts.length > 1 then none
            else match alts[0]? with
                 | some a =>
                   match symEval n ρ a with
                   | some oa =>
                     match symApplyList n oa.value [.sCon (.fstP e), .sCon (.sndP e)] with
                     | some oap => some ⟨oap.value, andE oa.defined oap.defined⟩
                     | none => none
                   | none => none
                 | none => none
        | _ => none
    | _ + 1, _, _, _ => none
  termination_by n _ v _ => (n, sizeOf v)

  /-- The nested `ite` for a symbolic-integer `Case`: `ite (e == i) altᵢ (… (e == i+1) …)`,
      bottoming out at the empty alt-list as undefined (an out-of-range / negative tag makes no
      claim).  Mirrors `bigEval`'s `Integer` dispatch (`alts[n]?`, `n < 0` ⇒ none). -/
  def symCaseInt : Nat → SymEnv → SmtExpr → Nat → List Term → Option SymOut
    | _, _, _, _, [] => none
    | n, ρ, e, i, alt :: rest =>
        combineIte (.bin .eq e (.litI (Int.ofNat i))) (symEval n ρ alt) (symCaseInt n ρ e (i + 1) rest)
  termination_by n _ _ _ alts => (n, sizeOf alts)
end

/-- Extract the top-level **success formula** of a compiled validator whose result is a
    boolean: `defined ∧ value`.  Requires the result value to be a first-order `sCon`
    (a `Bool`-sorted `SmtExpr`); otherwise `none`.  `evalSmt σ (extract o) = .B true` is
    exactly "at model `σ`, the validator is defined and returns `true`". -/
def extract : SymOut → Option SmtExpr
  | ⟨.sCon e, d⟩ => some (andE d e)
  | _ => none

end Moist.Compile
