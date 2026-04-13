import Moist.CEK.Machine
import Moist.CEK.Readback
import Moist.Plutus.Term
import Moist.Verified.Definitions
import Moist.Verified.ClosedAt

/-! # Contextual-tower definitions

* `ObsEq` / `ObsRefines` — observational equivalence / refinement of
  closed CEK states. (`ObsEq` is retained in the legacy
  `Moist.Verified.Equivalence` namespace for historical compatibility;
  `ObsRefines` lives in the `Contextual` namespace.)
* `Context` / `fill` / `Context.binders` / `Context.closedAt` /
  `Context.compose` — program contexts and their operations.
* `CtxEq` / `CtxRefines` — contextual equivalence / refinement.
-/

namespace Moist.Verified.Equivalence

open Moist.CEK
open Moist.Plutus.Term

/-- Full observational equivalence: both halt AND error behavior preserved.
    Using a `structure` instead of `And ... ∧ ...` sidesteps Lean's anonymous-
    constructor flattening: `⟨h, e⟩` and `h.halt`/`h.error` remain unambiguous
    no matter how the inner `Iff`s look. -/
structure ObsEq (c₁ c₂ : State) : Prop where
  halt : (∃ v₁, Reaches c₁ (.halt v₁)) ↔ (∃ v₂, Reaches c₂ (.halt v₂))
  error : Reaches c₁ .error ↔ Reaches c₂ .error

end Moist.Verified.Equivalence

namespace Moist.Verified.Contextual

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified (closedAt closedAtList)
open Moist.Verified.Equivalence

/-! ## Syntactic contexts -/

/--
  A program context: an AST with exactly one `Hole`.
  This mirrors the `Term` inductive type.
-/
inductive Context
  | Hole : Context
  | Lam : Nat → Context → Context
  | AppLeft : Context → Term → Context
  | AppRight : Term → Context → Context
  | Delay : Context → Context
  | Force : Context → Context
  | Constr : Nat → List Term → Context → List Term → Context
  | Case : Context → List Term → Context
  /-- Hole inside a single alt of a `Case`.
      `CaseAlt scrut lefts C rights` places the hole at slot `|lefts|` of
      `Case scrut (lefts ++ [HOLE] ++ rights)`. -/
  | CaseAlt : Term → List Term → Context → List Term → Context
  -- NOTE: No `Builtin` constructor: `Term.Builtin : BuiltinFun → Term` is nullary;
  -- builtin arguments are introduced via `Apply`, so the `AppLeft`/`AppRight` cases
  -- already cover holes inside builtin applications.

/-- Plugs a term into the context hole. Variable capture is strictly
    permitted to simulate adversarial environments. -/
def fill : Context → Term → Term
  | .Hole, t => t
  | .Lam x C, t => .Lam x (fill C t)
  | .AppLeft C e, t => .Apply (fill C t) e
  | .AppRight e C, t => .Apply e (fill C t)
  | .Delay C, t => .Delay (fill C t)
  | .Force C, t => .Force (fill C t)
  | .Constr tag lefts C rights, t => .Constr tag (lefts ++ [fill C t] ++ rights)
  | .Case C alts, t => .Case (fill C t) alts
  | .CaseAlt scrut lefts C rights, t => .Case scrut (lefts ++ [fill C t] ++ rights)

/-- Number of binders the context introduces above the hole. -/
def Context.binders : Context → Nat
  | .Hole => 0
  | .Lam _ C => C.binders + 1
  | .AppLeft C _ | .AppRight _ C
  | .Delay C    | .Force C
  | .Constr _ _ C _ | .Case C _
  | .CaseAlt _ _ C _ => C.binders

/-- `C.closedAt d` asserts that every non-hole sibling term embedded in `C` is
    closed at the depth at which it sits inside the context, when `C` itself is
    interpreted at root depth `d`. Lambdas in the context bump the depth by one
    for everything beneath them. -/
def Context.closedAt : Nat → Context → Bool
  | _, .Hole => true
  | d, .Lam _ C => Context.closedAt (d + 1) C
  | d, .AppLeft C e => Context.closedAt d C && Moist.Verified.closedAt d e
  | d, .AppRight e C => Moist.Verified.closedAt d e && Context.closedAt d C
  | d, .Delay C => Context.closedAt d C
  | d, .Force C => Context.closedAt d C
  | d, .Constr _ lefts C rights =>
      Moist.Verified.closedAtList d lefts && Context.closedAt d C
        && Moist.Verified.closedAtList d rights
  | d, .Case C alts =>
      Context.closedAt d C && Moist.Verified.closedAtList d alts
  | d, .CaseAlt scrut lefts C rights =>
      Moist.Verified.closedAt d scrut
        && Moist.Verified.closedAtList d lefts && Context.closedAt d C
        && Moist.Verified.closedAtList d rights

/-- Plug `inner` into the hole of `outer`. Standard context composition. -/
def Context.compose : Context → Context → Context
  | .Hole, inner => inner
  | .Lam x C, inner => .Lam x (Context.compose C inner)
  | .AppLeft C e, inner => .AppLeft (Context.compose C inner) e
  | .AppRight e C, inner => .AppRight e (Context.compose C inner)
  | .Delay C, inner => .Delay (Context.compose C inner)
  | .Force C, inner => .Force (Context.compose C inner)
  | .Constr tag lefts C rights, inner =>
      .Constr tag lefts (Context.compose C inner) rights
  | .Case C alts, inner => .Case (Context.compose C inner) alts
  | .CaseAlt scrut lefts C rights, inner =>
      .CaseAlt scrut lefts (Context.compose C inner) rights

/-! ## Contextual equivalence -/

/-- **Guarded** contextual equivalence: `t₁ ≈ t₂` iff for every context `C`
    that fully closes both `fill C t₁` and `fill C t₂` at depth 0, the empty-
    state CEK runs are observationally equivalent. The closedness premises
    ensure that during CEK evaluation we never reach the hole with missing
    bindings — the context supplies exactly the right number of binders,
    which lets us bake `ρ.length = d` into `EnvEqK`. Without this guard, we'd
    have to accept ghost `(none, none)` lookups and the soundness bridge
    would have no way to discharge the purity obligations that strict-error
    refinement demands. -/
def CtxEq (t₁ t₂ : Term) : Prop :=
  ∀ (C : Context),
    closedAt 0 (fill C t₁) = true →
    closedAt 0 (fill C t₂) = true →
    ObsEq (.compute [] .nil (fill C t₁))
          (.compute [] .nil (fill C t₂))

/-! ## Contextual refinement -/

/-- Observational refinement: `c₂` refines `c₁`'s halt AND error behavior.
    This prevents unsound transforms like `Let x = Error in 10 ⊑ 10`.
    Defined as a `structure` for the same reason `ObsEq` is — unambiguous
    destructuring/construction with `.halt`/`.error`/`ObsRefines.mk`. -/
structure ObsRefines (c₁ c₂ : State) : Prop where
  halt : (∃ v₁, Reaches c₁ (.halt v₁)) → (∃ v₂, Reaches c₂ (.halt v₂))
  error : Reaches c₁ .error → Reaches c₂ .error

/-- **Strict** contextual refinement: `t₁ ⊑ t₂` iff for every context `C`
    that closes `fill C t₁` at depth 0, `fill C t₂` is *also* closed at
    depth 0 (the optimizer doesn't invent fresh free variables) AND the
    empty-state CEK run of `fill C t₁` halt/error-refines that of
    `fill C t₂`.

    By bundling closedness preservation INTO the refinement relation,
    transitivity is direct — no middle-term closedness side condition
    needed, since `h12 C hC1` hands us both `hC2` and the refinement, and
    `h23 C hC2` then hands us `hC3` and the composed refinement. -/
def CtxRefines (t₁ t₂ : Term) : Prop :=
  ∀ (C : Context),
    closedAt 0 (fill C t₁) = true →
    closedAt 0 (fill C t₂) = true ∧
    ObsRefines (.compute [] .nil (fill C t₁))
               (.compute [] .nil (fill C t₂))

@[inherit_doc] scoped infix:50 " ⊑Ctx " => CtxRefines

end Moist.Verified.Contextual
