import Moist.Verified.SmallStep.Value
import Moist.Verified.SmallStep.Discharge

/-! # Small-step contextual reduction for UPLC

Ports the contextual/reduction-frame semantics of the Plutus Core
specification (`untyped-reduction.tex`, Fig. `fig:untyped-reduction`) to the
de Bruijn `Moist.Plutus.Term.Term`.

The spec's reduction frames

```
f ::= [_ M] | [V _] | (force _) | (constr i V⃗ _ M⃗) | (case _ M⃗)
```

together with the "always use the first applicable rule" convention define a
left-to-right call-by-value strategy.  We encode this directly as an inductive
relation `Step` whose congruence rules are guarded by `Value`, so reduction
descends only into the *active* subterm (the unique decomposition point).  This
is the standard, provably-equivalent presentation of the frame semantics.

Differences from the bare spec figure, all deliberate (see
`docs/SmallStep-CEK-Equivalence-Plan.md`):

* Unsaturated partial builtin applications are **values** (`Value.builtin`),
  not self-looping redexes.
* Builtin saturation routes through the shared `Moist.CEK.evalBuiltin`
  (= spec `Eval`) via `reflect`/`discharge`.
* `case` on builtin constants is supported (`caseConst`), mirroring the CEK's
  `constToTagAndFields`.
-/

namespace Moist.Verified.SmallStep

open Moist.Plutus.Term (Term)
open Moist.CEK (evalBuiltin constToTagAndFields)
open Moist.Verified (substTerm)

/-- Iterated left-associated application `[f a₁ … aₙ]`. -/
def mkApps (f : Term) (args : List Term) : Term := args.foldl Term.Apply f

/-- One step of contextual reduction. -/
inductive Step : Term → Term → Prop
  -- ── Head reductions ──
  /-- β: `[(lam x M) V] → [V/x]M`. -/
  | betaLam {x M v} : Value v → Step (.Apply (.Lam x M) v) (substTerm 1 v M)
  /-- `force (delay M) → M`. -/
  | forceDelay {M} : Step (.Force (.Delay M)) M
  /-- `case (constr i V⃗) (U⃗) → [U_{i+1} V⃗]`. -/
  | caseConstr {i vs alts alt} :
      ValueList vs → alts[i]? = some alt →
      Step (.Case (.Constr i vs) alts) (mkApps alt vs)
  /-- `case` on a builtin constant (CEK extension, mirrors
      `constToTagAndFields`): productive only when a branch is selected and the
      branch-count check passes; all failure modes are left stuck. -/
  | caseConst {c bt tag numCtors fields alts alt} :
      constToTagAndFields c = some (tag, numCtors, fields) →
      ¬ (numCtors > 0 ∧ alts.length > numCtors) →
      alts[tag]? = some alt →
      Step (.Case (.Constant (c, bt)) alts) (mkApps alt (fields.map discharge))
  /-- Saturated builtin application `[A V]`: evaluate via the shared
      `evalBuiltin` on the discharged-then-reflected value arguments. -/
  | satApply {t b args v} :
      BSpine t b args (.one .argV) → Value v →
      Step (.Apply t v)
        (dischargeResult (evalBuiltin b ((reflectList (args ++ [v])).reverse)))
  /-- Saturated builtin force `(force A)`. -/
  | satForce {t b args} :
      BSpine t b args (.one .argQ) →
      Step (.Force t)
        (dischargeResult (evalBuiltin b ((reflectList args).reverse)))
  -- ── Error propagation: `f[error] → error` ──
  | errAppL {N} : Step (.Apply .Error N) .Error
  | errAppR {v} : Value v → Step (.Apply v .Error) .Error
  | errForce : Step (.Force .Error) .Error
  | errCase {alts} : Step (.Case .Error alts) .Error
  | errConstr {i lefts rights} :
      ValueList lefts → Step (.Constr i (lefts ++ .Error :: rights)) .Error
  -- ── Congruence (call-by-value, left-to-right) ──
  | congAppL {f f' N} : Step f f' → Step (.Apply f N) (.Apply f' N)
  | congAppR {v N N'} : Value v → Step N N' → Step (.Apply v N) (.Apply v N')
  | congForce {t t'} : Step t t' → Step (.Force t) (.Force t')
  | congCase {s s' alts} : Step s s' → Step (.Case s alts) (.Case s' alts)
  | congConstr {i lefts m m' rights} :
      ValueList lefts → Step m m' →
      Step (.Constr i (lefts ++ m :: rights)) (.Constr i (lefts ++ m' :: rights))

/-- Reflexive-transitive closure of `Step` (hand-rolled; no Mathlib). -/
inductive Steps : Term → Term → Prop
  | refl {t} : Steps t t
  | step {t u w} : Step t u → Steps u w → Steps t w

/-- A term is in normal form when no `Step` applies. -/
def Normal (t : Term) : Prop := ¬ ∃ t', Step t t'

/-- A *stuck* term: a normal form that is not a value (includes `Error` and
    ill-typed configurations the CEK maps to its error state). -/
def Stuck (t : Term) : Prop := Normal t ∧ ¬ Value t

end Moist.Verified.SmallStep
