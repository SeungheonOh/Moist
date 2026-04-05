# Plan: Mutual block to eliminate all sorrys in SameBodyAdequacy

## Current sorry inventory (10 total)

```
622:  evalBuiltin_agree_head non-VCon cases
662:  funV_frame_beh VLam (needs sameBody_adequacy)
1244: funV_same_arg_error_transfer VBuiltin saturated
1316: funV_same_arg_halts_transfer VBuiltin saturated
1366: funV_same_arg_valueEq VBuiltin
2105: sameBody_adequacy Case dispatch error (scrutinee halts, left)
2116: sameBody_adequacy Case dispatch error (scrutinee halts, right)
2127: sameBody_adequacy Case dispatch halts (left → right)
2136: sameBody_adequacy Case dispatch halts (right → left)
2139: sameBody_adequacy Case dispatch ValueEq
```

## Dependency analysis

### Category A: Mutual dependency (1 sorry)

**Line 662**: `funV_frame_beh` VLam case needs `sameBody_adequacy` (defined
later). `sameBody_adequacy` Apply case needs `funV_frame_beh`. This is a
genuine mutual recursion.

### Category B: evalBuiltin extensionality (4 sorrys)

**Lines 622, 1244, 1316, 1366**: All need `evalBuiltin` agreement when
argument lists differ. Two sub-cases:

- **Line 622** (`evalBuiltin_agree_head`): Lists differ in HEAD only.
  `(vx :: args)` vs `(vx' :: args)` where `∀ k, ValueEq k vx vx'` and
  `args` is shared. Non-VCon head case.

- **Lines 1244, 1316, 1366** (`funV_same_arg_*` VBuiltin): Lists differ
  in TAIL only. `(vx :: a1)` vs `(vx :: a2)` where `vx` is shared and
  `ListValueEq k a1 a2`. Need `evalBuiltin` agreement.

### Category C: Case dispatch (5 sorrys)

**Lines 2105-2139**: After scrutinee halts with `∀ k, ValueEq k`-related
values, the case dispatch selects the same alternative (same tag) and
applies fields via `applyArg` frames. Need to compose through the dispatch.

## Plan

### Step 1: Prove `evalBuiltin` extensionality (Category B)

Add a general `evalBuiltin_agree` lemma that handles both head-differing
and tail-differing cases.

**Key insight**: `evalBuiltin` = `evalBuiltinPassThrough` then
`extractConsts → evalBuiltinConst`. For `extractConsts`: if any non-VCon
in the list, returns `none`. Since `∀ k, ValueEq k` at `k = 1` gives same
constructor, both lists have non-VCon at the same positions.

**Sub-lemma 1**: `extractConsts_agree`
```
∀ k, ListValueEq k args₁ args₂ →
    extractConsts args₁ = extractConsts args₂
```

Proof: by induction on the lists. At each position, `ValueEq 1` gives
same constructor. VCon: same constant (from `ValueEq 1`). Non-VCon: both
fail at the same position. Matching constants → same extractConsts result.

Note: actually needs `∀ k, ListValueEq k` (not a fixed k), because we
use `k = 1` for constructor matching. The caller has this: either `∀ k`
from `EnvValueEqAll` or from the `∀ k` in the specific hypotheses.

Wait, for the tail-differing case (lines 1244, 1316, 1366), we have
`ListValueEq k a1 a2` at a FIXED `k` (from `ValueEq (k+1)` on VBuiltin).
Not `∀ k`. So `extractConsts_agree` needs `ListValueEq 1` (not `∀ k`).

Actually `ListValueEq k` for `k ≥ 1` gives `ValueEq k` on heads. At `k ≥ 1`,
VCon values have `c₁ = c₂`. Non-VCon values have matching constructors.
So `ListValueEq 1` suffices for `extractConsts_agree`.

But we have `ListValueEq k` where `k` comes from the outer `ValueEq (k+1)`.
By `listValueEq_mono`, `ListValueEq k → ListValueEq 1` when `k ≥ 1`.
At `k = 0`, `ListValueEq 0` is `True` — can't extract constructor info.

So we need `k ≥ 1` or handle `k = 0` separately.

For the `funV_same_arg_*` cases: we have `ValueEq (k+1)` on VBuiltin,
which gives `ListValueEq k` on args. At `k ≥ 1`: `ListValueEq k → ListValueEq 1`
by mono. At `k = 0`: `ListValueEq 0 = True` but we're inside
`ValueEq (k+1) = ValueEq 1` on VBuiltin which already gives
`ListValueEq 0` on args and `evalBuiltin b a1 = none ↔ evalBuiltin b a2 = none`.
So the none↔ is already provided.

Hmm, this is getting complicated. Let me think more carefully.

**For line 1244** (`funV_same_arg_error_transfer` VBuiltin saturated none case):
We have:
- `hve : ValueEq (k+1) (VBuiltin b a1 ea) (VBuiltin b a2 ea)`
- From unfolding: `heval_none : evalBuiltin b a1 = none ↔ evalBuiltin b a2 = none`
- `heval : evalBuiltin b (vx :: a1) = none`
- Need: `evalBuiltin b (vx :: a2) = none`

The key: `heval_none` is about `a1` vs `a2`, but we need about `(vx :: a1)` vs `(vx :: a2)`.
These are DIFFERENT lists. `evalBuiltin b (vx :: a1)` is NOT the same as `evalBuiltin b a1`.

So `heval_none` is NOT directly useful. We need a separate argument that
`evalBuiltin b (vx :: a1) = none → evalBuiltin b (vx :: a2) = none`.

For this: `evalBuiltin b (vx :: a1) = none` means either:
- `evalBuiltinPassThrough b (vx :: a1) = none` AND `extractConsts (vx :: a1) = none`
  (or extractConsts succeeds but evalBuiltinConst fails)

Since `vx` is the SAME on both sides, and `a1` vs `a2` are `ListValueEq k`-related:
- `extractConsts (vx :: a1)` vs `extractConsts (vx :: a2)`: head is same (`vx`),
  tails are `ListValueEq k` at `k ≥ 1` → same VCon skeleton → same extractConsts.
- `evalBuiltinPassThrough`: patterns match on `(b, vx :: a1)` vs `(b, vx :: a2)`.
  If the pattern binds position 0 as wildcard (most do), the match depends on
  `a1` vs `a2`. But `a1` and `a2` have same VCon values at VCon positions...

Actually I think the cleanest proof for ALL of these is:

**Core lemma**: For lists where corresponding elements have the same VCon
skeleton (same constructor, VCon elements have same constant):

```lean
theorem evalBuiltin_agree_skeleton (b : BuiltinFun) (args₁ args₂ : List CekValue)
    (hlen : args₁.length = args₂.length)
    (hskel : ∀ i, i < args₁.length →
      match args₁[i]!, args₂[i]! with
      | .VCon c₁, .VCon c₂ => c₁ = c₂
      | .VCon _, _ => False
      | _, .VCon _ => False
      | _, _ => True) :
    (extractConsts args₁ = extractConsts args₂) ∧
    (∀ v₁ v₂,
      evalBuiltinPassThrough b args₁ = some v₁ →
      evalBuiltinPassThrough b args₂ = some v₂ →
      v₁ = v₂ ∨ ∃ i, v₁ = args₁[i]! ∧ v₂ = args₂[i]!)
```

This is too complex. Let me just directly prove what's needed.

**Simplest approach for ALL builtin sorrys**:

Prove one lemma:
```lean
private theorem evalBuiltin_agree_lists (b : BuiltinFun)
    (args₁ args₂ : List CekValue) (h : ∀ k, ListValueEq k args₁ args₂) :
    match evalBuiltin b args₁, evalBuiltin b args₂ with
    | some v₁, some v₂ => ∀ k, ValueEq k v₁ v₂
    | none, none => True
    | _, _ => False
```

This single lemma covers ALL cases. Proof:
1. `extractConsts_agree`: mutual induction on lists, using `ValueEq 1` for
   VCon matching.
2. If extractConsts both succeed with same constants → `evalBuiltinConst`
   gives same result → `∀ k, ValueEq k (VCon c) (VCon c)`.
3. If extractConsts both fail → `evalBuiltinPassThrough` only. Case-split
   on the 6 pass-through builtins. For each, the pattern depends on VCon
   condition values (same on both sides) and the result is either from
   shared VCon positions (same) or from differing positions (`∀ k, ValueEq k`).
4. For non-pass-through builtins: both `none`.

**Then use this lemma to fill ALL 4 builtin sorrys:**

- Line 622: `evalBuiltin_agree_head` delegates to `evalBuiltin_agree_lists`
  with `h = fun k => ⟨hx k, listValueEq_refl k args⟩`.
- Lines 1244, 1316: need `evalBuiltin b (vx :: a1) = none ↔ evalBuiltin b (vx :: a2) = none`.
  From `evalBuiltin_agree_lists` with lists `(vx :: a1)` and `(vx :: a2)`:
  need `∀ k, ListValueEq k (vx :: a1) (vx :: a2)`, which is
  `∀ k, ValueEq k vx vx ∧ ListValueEq k a1 a2` = `valueEq_refl k vx ∧ ...`.
  But we have `ListValueEq k a1 a2` at a FIXED k, not ∀ k.

  **Problem**: We DON'T have `∀ k, ListValueEq k a1 a2`. We only have it
  at one specific `k`.

  **Resolution**: The `funV_same_arg_*` lemmas are about `ValueEq (k+1)`
  on VBuiltin values. In the Apply case of `sameBody_adequacy`, we actually
  have `∀ j, ValueEq j vf₁ vf₂` (from `EnvValueEqAll`). So `∀ j, ValueEq j`
  on VBuiltin gives `∀ j, ListValueEq (j-1) a1 a2`. This IS `∀ k, ListValueEq k`.

  So: change the `funV_same_arg_*` lemmas to take `∀ k, ValueEq k` on the
  functions (not a fixed `k+1`), matching what the Apply case actually has.

  OR: just avoid the `funV_same_arg_*` lemmas entirely and inline the logic
  using `evalBuiltin_agree_lists`.

### Step 2: Restructure for mutual block (Category A)

The constraint: Lean `mutual` blocks can only contain theorem/def declarations,
no intermediate private helpers.

**Solution**: Extract ALL private helpers out of the range between
`funV_frame_beh` and `sameBody_adequacy`. Then the mutual block contains
ONLY these two theorems.

Current structure:
```
Section 3 helpers (lines 451-623)
funV_frame_beh (lines 624-763)           ← MUTUAL
Section 3b-3e helpers (lines 764-1674)
sameBody_adequacy (lines 1679-2140)      ← MUTUAL
funV_frame_beh_vlam (lines 2144-2177)    ← DELETE (absorbed)
```

Target structure:
```
Section 3 helpers (lines 451-623)        ← KEEP
Section 3b-3e helpers (lines 764-1674)   ← MOVE BEFORE funV_frame_beh
mutual
  funV_frame_beh                         ← VLam case uses sameBody_adequacy
  sameBody_adequacy                      ← Apply case uses funV_frame_beh
end
```

This means:
1. Move Section 3b-3e (lines 764-1674) to BEFORE `funV_frame_beh` (after line 623).
2. Wrap `funV_frame_beh` + `sameBody_adequacy` in `mutual ... end`.
3. Fill VLam case of `funV_frame_beh` with `sameBody_adequacy` call.
4. Delete `funV_frame_beh_vlam`.

The move is ~900 lines. The `funV_frame_beh` and `sameBody_adequacy`
can reference each other inside the `mutual` block.

**Potential issue**: `funV_frame_beh` uses helpers like `error_in_one_step_reaches_error`,
`reaches_of_step_reaches`, `valueEq_vbuiltin`, `evalBuiltin_agree_head`.
These are defined in Section 3 (before `funV_frame_beh`). After the move,
they'll still be before `funV_frame_beh`. Good.

`sameBody_adequacy` uses helpers from Sections 3b-3e. After the move,
these are ALSO before the mutual block. Good.

**Potential issue**: `sameBody_adequacy` uses `funV_same_arg_error_transfer`,
`funV_same_arg_halts_transfer`, `funV_same_arg_valueEq` from Section 3b.
These are private. They also have sorrys (the VBuiltin cases). After
the builtin extensionality fix (Step 1), these sorrys should be gone.

### Step 3: Case dispatch (Category C)

After the case dispatch scrutinee halts with `∀ k, ValueEq k vs₁ vs₂`:

At `k = 1`, `ValueEq 1` on VConstr gives: `tag₁ = tag₂` and
`ListValueEq 0 fields₁ fields₂` (which is `True`). At higher k, the tags
are the same and fields are pointwise related. So both dispatch to the
same alternative (same tag).

The pattern:
```
ret [caseScrutinee alts ρ] (VConstr tag fields) →
  match alts[tag]? with
  | some alt => compute (fields.map Frame.applyArg ++ []) ρ alt
  | none => error
```

Both sides have the same tag → same `alts[tag]?` → same alternative `alt`.
Then `fields₁.map Frame.applyArg` vs `fields₂.map Frame.applyArg` with
`∀ k, ValueEq k` on corresponding fields.

The field application through `applyArg` frames is similar to
`funV_frame_beh` but for `applyArg` instead of `funV`. Each `applyArg`
frame applies a field value as an argument to the alternative.

This requires composing through a chain of `applyArg` frames, which is
essentially what `constrField_iter_adequacy` does but in reverse.

For the VCon scrutinee case: `constToTagAndFields` decomposes the constant,
and if both scrutinees are `VCon c` (same constant from `∀ k, ValueEq k`),
the decomposition gives the same tag and fields. Both dispatch identically.

## Execution plan

### Phase 1: evalBuiltin extensionality

1. Prove `extractConsts_agree`: if `∀ k, ListValueEq k args₁ args₂`,
   then `extractConsts args₁ = extractConsts args₂`.

2. Prove `evalBuiltinPassThrough_agree`: if `∀ k, ListValueEq k args₁ args₂`,
   then evalBuiltinPassThrough agrees (none/none or related some/some).

3. Compose into `evalBuiltin_agree_lists`.

4. Use to fill sorrys at lines 622, 1244, 1316, 1366.

### Phase 2: Case dispatch

5. Prove `case_dispatch_agree`: when scrutinee values are
   `∀ k, ValueEq k`-related VConstr/VCon, the case dispatch produces
   agreeing results.

6. Use to fill sorrys at lines 2105-2139.

### Phase 3: Restructure into mutual block

7. Move Sections 3b-3e (lines 764-1674) to before `funV_frame_beh`.
8. Wrap `funV_frame_beh` + `sameBody_adequacy` in `mutual ... end`.
9. Fill VLam case of `funV_frame_beh` with `sameBody_adequacy` call.
10. Delete `funV_frame_beh_vlam`.
11. Verify build.

### Estimated effort

- Phase 1: ~150 lines of new lemmas. Medium difficulty.
- Phase 2: ~100 lines. Medium difficulty (case dispatch pattern match).
- Phase 3: ~50 lines of edits (mostly structural moves). Easy.
- Total: ~300 new lines, ~900 moved lines.
