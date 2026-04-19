# Analysis: Inline Soundness Proof Strategy

## Goal

`inline_soundness : ∀ e s, MIRCtxRefines e (inlinePass e s).1.1`

## Proof Chain (Top-Down)

```
inline_soundness                                          [MIRCtxRefines level]
  ↓ (via inline_soundness_aux + induction on e)
Let case → inlineLetBindings_soundness                   [MIRCtxRefines]
  ↓
inlineLetGo_soundness (inline branch)                    [MIRCtxRefines]
  ↓
inline_step_mirCtxRefines                                [MIRCtxRefines]
  ↓
substInBindings_body_inline_mirCtxRefines (THE CORE)     [MIRCtxRefines]
  ↓ (unfolds via lowerTotal)
CtxRefines (Apply (Lam 0 body_lowered) rhs_lowered)      [UPLC-level CtxRefines]
           body_substituted_lowered
```

The core unresolved fact is the **UPLC β-substitution refinement**.

## User's Key Insight

`ctxRefines_trans` (Contextual.lean:324) has **no side conditions**:
```
ctxRefines_trans : CtxRefines t₁ t₂ → CtxRefines t₂ t₃ → CtxRefines t₁ t₃
```

By contrast, `ValueRefinesK` transitivity in general requires self-refl
on closure args (which requires `ValueWellFormed` on arbitrary args —
not provided in the ∀-unfolded closure relation).

**Implication**: If we can discharge facts AT THE CtxRefines LEVEL early,
we can compose them freely via `ctxRefines_trans` without step-indexed
transitivity pain.

## Key Tools Available

- **ShiftBisim** (my contribution this session): `ShiftBisimState s₁ s₂`
  captures observational equivalence between state `s₁` and its shifted
  counterpart `s₂ = shift s₁ by one binder`. `step_preserves`, halt/error
  inversions, reflexivity at identity σ are all proven.

- **DeadLet** (existing): proves `MIRRefines (let x = e in body) body`
  when `x ∉ freeVars(body) ∧ isPure e` via state-level simulation.
  Pattern: extract halt/error witnesses, bridge via `value_stack_poly`
  + `halt_descends_to_baseπ`.

- **FundamentalRefines** (existing): `renameRefines` / `renameRefinesR`
  give ObsRefinesK between `t` and `rename σ t` under
  `RenameEnvRef[R] σ`.

- **MIR Congruence** (existing): `mirCtxRefines_let_body`, `_rhs_head`,
  `_binds_congr`, `_let_nil`, etc. Compose via `mirCtxRefines_trans`.

## What the Core Fact Actually Requires

The UPLC β-substitution refinement
`CtxRefines (Apply (Lam 0 body) rhs) (substTerm 1 rhs body)`
captures the observational equivalence between:
- **LHS**: evaluates `rhs` once, binds result at position 1 of env, runs body.
- **RHS**: runs body directly, with each occurrence of var 1 replaced by `rhs`
  (re-evaluated at each use; by determinism same result).

This is **NOT a shift transformation** (which is `add an unused binder`).
It's the **INVERSE of shift+value-at-position-1**: eliminating a binder by
substituting its value throughout the body.

Shift bisim handles: `t ↔ shift t` under `ρ ↔ ρ.extend v0` (add dummy).
β-substitution handles: `body in ρ.extend v ↔ substTerm 1 rhs body in ρ`
when `v = eval(rhs)` (collapse env position via substitution).

## Viability of "Bisim → CtxRefines → Transitivity" Path

### Option A: Use shift bisim's output for β-substitution

**Does not directly apply.** The shift bisim proves a relation between
`(t, ρ)` and `(shift t, ρ.extend v0)`. For β-substitution we need a
relation between `(body, ρ.extend v_rhs)` and `(substTerm 1 rhs body, ρ)`.
These are different transformations — shift bisim doesn't encode
substitution semantics.

### Option B: Build a separate "substitution bisim"

**Viable but substantial.** A new mutual inductive `SubstBisim{State,Env,Value,...}`
parameterized by a substitution position + replacement term + its cached
value. `step_preserves` proven similarly to shift bisim (~400-600 lines).
Then `SubstBisimState → ObsRefines → CtxRefines` via standard lifting.

Estimated: 800-1200 lines of parallel infrastructure to shift bisim.

### Option C: Complete step-indexed path (current)

**Status**: 95% complete. Blocks on `valueRefinesK_trans_shiftBisim` VLam/VDelay
closure cases (3 sorries in current committed state).

Resolutions:
- **C1**: Add `ValueWellFormed` hypothesis to transitivity, then use
  `valueRefinesK_refl` for self-refl on args. ~300-500 lines, reorganizes
  the signature chain.
- **C2**: Use `ObsEqK` (bidirectional, IS reflexive on well-formed) instead
  of `ValueRefinesK`. Requires minor refactor of how heval expresses the
  halt-value relation.

## Assessment

The user's insight (lift to CtxRefines for transitivity) works for the
**OUTER composition chain** (combining multiple CtxRefines facts). But
the **INNER core fact** (β-substitution) still requires proving either:
1. Step-indexed via logical relations (current path, blocked on trans), or
2. State-level via a substitution-bisim (Option B, parallel work to shift).

Both routes require substantial work beyond what shift bisim provides.

## Recommendation

**Option C1**: Strengthen `valueRefinesK_trans_shiftBisim` with
`ValueWellFormed` hypotheses on the middle value (which `rHalts_shift_WF`
can provide since `RHaltsRelWF`'s `hm_wf` gives `ValueWellFormed v_rhs'`).
Then close the 3 remaining sorries.

This path:
- Leverages all committed shift-bisim infrastructure.
- Requires ~300-500 new lines (transitivity + composition).
- Stays within step-indexed reasoning but uses well-formedness to unblock.
- Compatible with the existing `rHalts_shift_WF_cond` + `ValueShiftsPreserve`
  structure.

**Next step**: refactor `valueRefinesK_trans_shiftBisim` to take
`ValueWellFormed v_b` as precondition, derive self-refl on args via
`valueRefinesK_refl`, close the closure cases, and complete
`rHalts_shift_WF` via `rHalts_shift_WF_cond`.
