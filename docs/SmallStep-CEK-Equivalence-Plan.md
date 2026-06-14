# Small-step UPLC semantics ↔ CEK machine: port & equivalence plan

## Goal

Port the UPLC spec's small-step **contextual reduction** semantics
(`~/io/plutus/doc/plutus-core-spec/untyped-reduction.tex`, Fig. `fig:untyped-reduction`,
with values from `untyped-values.tex`) into this repo over the existing de Bruijn
`Moist.Plutus.Term.Term`, and prove it **operationally adequate** with respect to the
existing CEK machine (`Moist.CEK.step` / `Reaches`).

## Confirmed decisions

```mermaid
graph TD
  A[Representation] --> A1[de Bruijn over existing Term<br>reuse RenameBase.substTerm]
  B[Partial builtin apps] --> B1[Treated as VALUES<br>no literal self-loops<br>Step stays productive]
  C[Equivalence form] --> C1[Operational adequacy via discharge]
  D[case on constants] --> D1[Extend Step to mirror constToTagAndFields<br>full adequacy, no domain restriction]
```

## Key reused machinery (already in repo)

- `Moist.CEK.step : State → State` (pure, total), `Reaches`, determinism
  (`reaches_unique`, `steps_trans`), terminal `halt`/`error`.
- `Moist.Verified.RenameBase.substTerm` — total open/decrementing β-substitution;
  `renameTerm`, `shiftRename`; `closedAt` + `closedAt_substTerm`.
- `Moist.Verified.BetaValueRefines` / `SubstRefines` — substitution ≈ CEK env-extend
  (`SubstEnvRef`, `substRefinesR_body`, `value_stack_poly`, `halt_descends_to_baseπ`).
  Backbone for the small-step → CEK direction at β.
- `Moist.CEK.evalBuiltin : BuiltinFun → List CekValue → Option CekValue` (args reversed,
  most-recent-first), `expectedArgs` = spec arity α(b). Single source of truth for builtins.

## New modules (`Moist/Verified/SmallStep/`)

```mermaid
graph LR
  Term[Plutus.Term] --> Value
  CEKVal[CEK.Value] --> Value
  Term --> Discharge
  CEKMach[CEK.Machine] --> Discharge
  RB[RenameBase] --> Discharge
  Value --> Step
  Discharge --> Step
  Builtins[CEK.Builtins] --> Step
  Step --> Sim[Simulation]
  Discharge --> Sim
  Value --> Sim
  CEKMach --> Sim
  Sim --> Adequacy
  SubstRefines --> Adequacy
```

### 1. `Value.lean` — value predicate (spec `V` + well-formed partial apps `A`)

- `BSpine : Term → BuiltinFun → List Term → ExpectedArgs → Prop` — a well-formed *partial*
  builtin spine for `b` with applied arg-terms (application order) and **non-empty remaining**
  `ExpectedArgs`. Mirrors `CekValue.VBuiltin b args ea` (ea always non-empty by type).
  - `builtin : BSpine (.Builtin b) b [] (expectedArgs b)`
  - `app : BSpine t b args (.more .argV rest) → Value v → BSpine (.Apply t v) b (args++[v]) rest`
  - `force : BSpine t b args (.more .argQ rest) → BSpine (.Force t) b args rest`
- `Value : Term → Prop` (mutual with `ValueList`):
  `Constant`, `Delay`, `Lam`, `Constr i args` (all args values), and
  `∃ b args ea, BSpine t b args ea`.

Saturating cases (`ea = .one _`) are deliberately **excluded** from `Value` — they are the
builtin redexes handled in `Step`. Disjointness (`.more` vs `.one`) gives determinism.

### 2. `Discharge.lean` — total discharge + reflect (proof-grade `readback`)

- `discharge : CekValue → Term`, `dischargeEnv`/iterated subst over env (via `substTerm`),
  mutual with list. Total analogue of `readbackValue`.
- `reflect : Term → CekValue` — interpret a value-term as a `CekValue` (empty envs for
  closed closures; spine parse for builtins). Junk on non-values.
- `dischargeResult : Option CekValue → Term := fun | some v => discharge v | none => .Error`.
- Round-trip lemma **`reflect_discharge : reflect (discharge v) = v`** (the builtin bridge).
- `value_discharge : Value (discharge v)` for every `CekValue v`.

### 3. `Step.lean` — small-step relation + closure

`Step : Term → Term → Prop` faithful to `fig:untyped-reduction` (CBV congruence = the
reduction frames + "first applicable rule"):

- **β**: `Value v → Step (.Apply (.Lam x M) v) (substTerm 1 v M)`
- **force/delay**: `Step (.Force (.Delay M)) M`
- **case/constr**: `i < alts.length → ValueList vs → Step (.Case (.Constr i vs) alts) (vs.foldl .Apply alts[i])`
- **case/const** (CEK extension): mirror `constToTagAndFields`.
- **builtin apply (saturating)**: `BSpine t b args (.one .argV) → Value v →
  Step (.Apply t v) (dischargeResult (evalBuiltin b ((args++[v]).reverse.map reflect)))`
- **builtin force (saturating)**: `BSpine t b args (.one .argQ) →
  Step (.Force t) (dischargeResult (evalBuiltin b (args.reverse.map reflect)))`
- **error frames** (`f[error] → error`): one rule per frame (App-left, App-right of value,
  Force, Constr field, Case scrut).
- **congruence** (CBV order): App (fn then arg, arg guarded by `Value`), Force, Constr
  (fields L→R, prefix guarded by `ValueList`), Case (scrutinee only).

`Steps := ReflTransGen Step` (hand-rolled; no Mathlib). Plus `Normal t := ¬∃t', Step t t'`,
`Stuck t := Normal t ∧ ¬ Value t`.

Lemmas: `value_normal : Value t → Normal t`; **determinism** `Step t a → Step t b → a = b`.

### 4. `Simulation.lean` — forward simulation CEK ⇒ small-step

- `dischargeState : State → Term` — discharge a whole CEK state (plug discharged value into
  discharged stack). `compute`/`ret` administrative transitions discharge to **0** small-steps;
  real reductions to **1**.
- `step_simulates : reachable/closed s → Steps (dischargeState s) (dischargeState (step s))`.
- Corollaries: CEK halt ⇒ small-step reaches that value; CEK error ⇒ small-step reaches a
  stuck normal form.

### 5. `Adequacy.lean` — main theorem

For closed `t`, with `init t := State.compute [] .nil t`:

- **`adequacy_halt`**: `Reaches (init t) (.halt v) ↔ Steps t (discharge v) ∧ Value (discharge v)`
- **`adequacy_error`**: `Reaches (init t) .error ↔ ∃ w, Steps t w ∧ Stuck w`

Forward (CEK ⇒ small-step) from `Simulation` + determinism. Backward (small-step ⇒ CEK)
from determinism of both systems + `SubstRefines` backbone + the fact the CEK never gets
stuck except at `halt`/`error` (progress for the CEK).

## Faithfulness notes

- "First applicable rule" / reduction frames ⇒ encoded as value-guarded inductive congruence
  (standard, provably equivalent unique-decomposition CBV).
- Spec `Eval'` multi-return branch `(V|V⃗′)` is vacuous here (`evalBuiltin` returns a single
  value), so omitted; documented.
- CEK conflates genuine `(error)` with stuck ill-typed configs (spec gets stuck), hence the
  error arm targets non-value normal forms rather than literal `Error`.

## Working agreement

All Lean proofs done inline, one lemma at a time, building after each step. No subagents.
Never revert WIP proofs; clank through errors one by one.
