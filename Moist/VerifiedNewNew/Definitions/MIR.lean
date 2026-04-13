import Moist.MIR.Expr
import Moist.MIR.LowerTotal
import Moist.VerifiedNewNew.Definitions
import Moist.VerifiedNewNew.Definitions.Contextual
import Moist.VerifiedNewNew.Definitions.StepIndexed

/-! # MIR-level relations

* `MIROpenRefK` / `MIROpenRef` — step-indexed / step-index-free open
  refinement. Built on the UPLC refinement tower: for every env of the
  right length, the lowered terms are in `BehRefinesK ValueRefinesK`.
* `MIRRefines` — compile preservation + `MIROpenRef` at every depth.
* `MIRCtxEq` / `MIRCtxRefines` — MIR contextual equivalence / refinement,
  built on the UPLC contextual tower via `lowerTotalExpr`.
-/

namespace Moist.VerifiedNewNew.MIR

open Moist.CEK
open Moist.Plutus.Term (Term)
open Moist.MIR (Expr VarId lowerTotalExpr)
open Moist.VerifiedNewNew.Contextual (CtxEq CtxRefines)
open Moist.VerifiedNewNew.Contextual.SoundnessRefines
  (BehRefinesK ValueRefinesK EnvRefinesK)

/-! ## MIR open refinement (step-indexed via the Refines tower) -/

/-- Open MIR refinement at step-index `k` and depth `d`. Quantifies over *all*
    `EnvRefinesK`-related environments (no `WellSizedEnv` guard) and uses the
    unidirectional `BehRefinesK ValueRefinesK` from `SoundnessRefines`. -/
def MIROpenRefK (k d : Nat) (m₁ m₂ : Expr) : Prop :=
  ∀ (env : List VarId), env.length = d →
    match lowerTotalExpr env m₁, lowerTotalExpr env m₂ with
    | some t₁, some t₂ =>
      ∀ j ≤ k, ∀ ρ₁ ρ₂, EnvRefinesK j d ρ₁ ρ₂ →
        BehRefinesK ValueRefinesK j ρ₁ ρ₂ t₁ t₂
    | _, _ => True

/-- Step-index-free open refinement: holds at every step index. -/
def MIROpenRef (d : Nat) (m₁ m₂ : Expr) : Prop :=
  ∀ k, MIROpenRefK k d m₁ m₂

/-- MIR-level refinement: compile preservation + `MIROpenRef` at every depth. -/
def MIRRefines (m₁ m₂ : Expr) : Prop :=
  (∀ env, (lowerTotalExpr env m₁).isSome → (lowerTotalExpr env m₂).isSome) ∧
  ∀ d, MIROpenRef d m₁ m₂

@[inherit_doc]
scoped infix:50 " ⊑ᴹ " => MIRRefines

/-! ## MIR contextual equivalence / refinement -/

/-- Contextual equivalence of MIR expressions: for every variable
    environment `env`, the two expressions have the same compile status,
    and (when both compile) their lowered UPLC terms are in the `CtxEq`
    relation. The observation clause uses the *same* `env` as the
    compile-status clause — the lowering is sensitive to the env, so
    pinning to `[]` would miss equivalences that only hold under
    non-empty envs. -/
def MIRCtxEq (m₁ m₂ : Expr) : Prop :=
  ∀ (env : List VarId),
    ((lowerTotalExpr env m₁).isSome ↔ (lowerTotalExpr env m₂).isSome) ∧
    match lowerTotalExpr env m₁, lowerTotalExpr env m₂ with
    | some t₁, some t₂ => CtxEq t₁ t₂
    | _, _ => True

scoped infix:50 " ≈Ctxᴹ " => MIRCtxEq

/-- Contextual refinement of MIR expressions: for every variable
    environment `env`, compile status is preserved (left compiles → right
    compiles), and (when both compile) the lowered UPLC terms are in the
    strict `CtxRefines` relation (closedness preservation + halt/error
    refinement bundled). -/
def MIRCtxRefines (m₁ m₂ : Expr) : Prop :=
  ∀ (env : List VarId),
    ((lowerTotalExpr env m₁).isSome → (lowerTotalExpr env m₂).isSome) ∧
    match lowerTotalExpr env m₁, lowerTotalExpr env m₂ with
    | some t₁, some t₂ => CtxRefines t₁ t₂
    | _, _ => True

scoped infix:50 " ⊑Ctxᴹ " => MIRCtxRefines

end Moist.VerifiedNewNew.MIR
