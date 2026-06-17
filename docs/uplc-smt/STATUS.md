# STATUS — verified UPLC→SMT-LIB denotational compiler

**The compiler now symbolically executes essentially everything the (pure-Lean) CEK can
decide**, with a tiny fixed trusted base.  Built in stages, each verified and validated:

- **v0** — λ-calculus + integer/boolean arithmetic, concrete control flow.
- **Phase A** — *all* constant types + *full* builtin coverage on concrete arguments
  (axiom-free, by deferring to the real `evalBuiltinConst`).
- **Phase B** — symbolic `Data` and `ByteString`: injection/projection/equality, the SMT
  `Data` recursive datatype (axiom-free).

Recursion through a **symbolic** guard is handled by **bounded unrolling** (`sIte`): the
evaluator unfolds the recursion to whatever depth the fuel allows, emitting nested SMT `ite`s,
and gates every fuel-exhausted path with `defined = false` so it makes no claim past the
unrolled frontier.  Cranking the fuel unrolls arbitrarily deep — this is sound bounded model
checking.  *Unbounded* verification (a property at **every** depth, i.e. k-induction /
invariants) remains out of scope (R2); everything `symEval` returns `none` on is a sound
refusal, never a mis-compile.

Branch `sho/smallstep`. ~1800 lines of library Lean + 4 test modules. Pure-core direct-`lean`
build (no `lake`/Blaster/FFI); z3 via `nix`.

## Supported fragment (what `symEval` handles)

* **All UPLC term forms** — `Var`/`Constant`/`Builtin`/`Lam`/`Apply`/`Delay`/`Force`/
  `Constr`/`Case`/`Error`.
* **All constant types** — `Integer`/`Bool` symbolic-capable (`sCon`), every other type
  (`ByteString`, `Data`, `Unit`, lists, pairs, …) carried concretely (`sConst`).
* **94 of the 101 builtins** — 89 via the concrete fold (real `evalBuiltinConst`, **axiom-free**)
  + 5 pass-through (`IfThenElse`/`ChooseUnit`/`Trace`/`ChooseData`/`ChooseList`/`MkCons`).  The
  only gap is the 7 `Value` builtins (CIP-0138), deliberately unsupported — see below.
* **All cryptography axiomatized** — the 6 hashes, 3 signature verifiers, `SerializeData`, and
  all 19 BLS12-381 ops are **uninterpreted** (`opaque` Lean functions ⇒ uninterpreted SMT
  functions; BLS elements modelled by their compressed `ByteString`).  z3 reasons about them
  abstractly; **zero new axioms** (the trust folds into `z3_sound`).  Equality/`finalVerify` are
  *structural* (reflexive).  `Test/Compile/Crypto.lean`.
* **Symbolic `Integer`/`Bool`** — `add/sub/mul`, floored & truncated `div/mod`,
  `=`/`<`/`≤`, with the division-by-zero definedness guard.
* **Symbolic `Data`** — `iData`/`bData` (inject), `unIData`/`unBData` (project, guarded by
  `isI`/`isB`), `equalsData`; emitted as an SMT recursive datatype.
* **Symbolic `Data` destructuring with polymorphic builtin `Pair`/`List`** (WI-2) — `SmtSort`
  gains `pair a b`/`list a`; `unConstrData : Data → pair int (list data)` (proper Plutus
  semantics — first the Integer tag, second the field list), `unListData : Data → list data`,
  `fstPair`/`sndPair`, `headList`/`tailList`/`nullList` (on `list data`, guarded non-empty).
  Emitted over parametric SMT `(Pair A B)`/`(Lst A)` datatypes; **axiom-free** (denotations via
  `evalBuiltin_concrete`).  The CEK's `unConstrData` was corrected to `Pair Integer (List Data)`
  to match `Ptah/Data.lean`'s type.  `Test/Compile/DataDestructure.lean`.
* **Symbolic `ByteString`** — `equalsByteString`, `lengthOfByteString` (SMT `String`).
* **`IfThenElse`** — concrete condition picks the branch; symbolic boolean condition with
  first-order branches becomes an SMT `ite`; symbolic condition with **lazy** (`delay`)
  branches defers a `sIte` (see next item).
* **`Case`** dispatch — on a statically-known `Constr`, *and* on a **symbolic choice** of
  constructors (`Case (if b then Constr i.. else Constr j..) alts`): the `Case` distributes
  through the deferred `sIte` (`Case (ite c x y) ≡ ite c (Case x) (Case y)`), dispatching each
  concrete leaf and merging into an SMT `ite` (`symCase`, proven `symCase_adequate`).
  `Test/Compile/SymCase.lean`.
* **`Case` on a builtin constant** — UPLC `case` can scrutinize a builtin value (not only a
  `Constr`), per the CEK's `constToTagAndFields`.  All such types are handled and proven:
  **Bool** (False=0/True=1, symbolic ⇒ `combineIte`), **Integer** (tag = the value; symbolic ⇒
  the nested `ite (x==i) altᵢ …`, `symCaseInt`, defined on `0 ≤ x < len`), **builtin List**
  (Cons=0 with head/tail fields via `headL`/`tailL`, Nil=1, symbolic ⇒ `nullL`+`combineIte`),
  **Pair** (one ctor, `fstP`/`sndP` fields), **Unit** (singleton).  Concrete constants dispatch
  deterministically (`symConstToTagFields`).  `Test/Compile/CaseConst.lean`.
* **A symbolic choice distributes through *every* elimination form** — `force` (`combineIte`),
  `Case` (`symCase`), **and `Apply`** (`symApply` over `sIte`: `(if c then f else g) a ≡
  if c then (f a) else (g a)`).  So `\x -> force ((if x==0 then (\_->delay error) else
  (\_->delay 42)) 1)` compiles to value `42` with `defined = (x ≠ 0)` — z3 flags `x=0` as the
  error input (proven `symApply_adequate`, axiom-clean).
* **Bounded recursion / model checking** — a recursion guarded by a *symbolic* boolean with
  lazy branches defers a `sIte` deferred choice; forcing it (`symForce`) unrolls **both**
  branches to the fuel depth (`combineIte`), emitting nested SMT `ite`s.  Reached-base-case
  paths are `defined`; fuel-exhausted paths are gated `defined = false` (no claim).  More fuel
  = deeper unroll = larger verified domain (`Test/Compile/BoundedRec.lean`).

**Sound refusals (R1/R2):** symbolic choice of a *function*, symbolic-`Data`/`chooseData`
into non-first-order branches, unbounded symbolic recursion.

## Proven (headline theorems, `#print axioms` checked)

- **`symEval_adequate`** (`Adequacy.lean`) — `symEval` interpreted at a model `σ` via the
  concretization `γ` agrees with `bigEval` on the σ-instantiated inputs.  Forward/soundness
  direction, by fuel-induction simulation mirroring `bigEval` (the same five mutual functions
  and `(fuel, sizeOf)` measure as `evalFwd`).  The `sIte` bounded-unrolling case is part of
  this proof: `γ σ (sIte cond a b)` selects `a`/`b` by `cond` at `σ` (matching the CEK's
  concrete `ifThenElse`), and `combineIte_some` shows forcing a deferred choice agrees with
  `forceVal` of the selected branch whenever its `defined` conjunct holds — so the unrolled
  SMT `ite` is faithful exactly on the `defined` frontier.
- **`validator_sound`** (`Reflect.lean`) — from z3's `unsat` on `encodeProperty P e`, *for
  every input assignment satisfying `P`, the CEK evaluating the validator on those inputs
  halts at `true`.*  Composes adequacy with the existing `bigEval ≡ CEK` and `z3_sound`.

### Trusted Computing Base (small, fixed across all stages)

`#print axioms validator_sound` =
`propext, Classical.choice, Quot.sound` (kernel) + **`z3_sound`** (the one accepted axiom) +
the **11 `evalBuiltin_*` integer denotations** (the `#eval`-validated R3 item).  **No
`sorry`/`admit`.**  Crucially, **Phases A and B added *zero* new axioms** — the concrete fold
and all `Data`/`ByteString` builtins are proved via `evalBuiltin_concrete` (which holds
because `evalBuiltinConst` reduces, unlike the `evalBuiltin` monolith).

## Why it stays tractable (design)

1. **`symEval` mirrors `bigEval`** structurally ⇒ adequacy is a simulation, not denotational
   adequacy.
2. **Defunctionalized closures** ⇒ `γ` is a structural function, no higher-order relation.
3. **Typed `Model`** (`ints`/`bools`/`datas`/`bytess` selected by a variable's sort) ⇒
   `evalSmt_sort` holds for *every* model with no side condition; the builtin agreements need
   no model hypotheses.
4. **`evalSmt` total** (junk for ill-sorted / wrong-constructor projections) ⇒ `γ` is a
   function; partiality (div-by-zero, `unIData` of a non-`I`) is carried by the separate
   `defined` flag, which the forward proof destructures with no well-sortedness.
5. **Sort-guarded builtins** ⇒ a light sound type check that discharges the agreements.
6. **`Data`/`ByteString` computed concretely in `evalSmt`** (the model assigns the variable a
   concrete `Plutus.Data`/`ByteString`) ⇒ the SMT recursive-datatype complexity lives only in
   the *printer*, validated by differential testing, while the proof side stays structural.

## Validation (live, under `nix-shell -p z3`)

`Test/Compile/Diff.lean`: §9.1 `symEval` vs `bigEval` **832/832** (incl. division & guards),
§9.2 `evalSmt` vs z3 on ground division **40/40** (validates `moist_fdiv/fmod/tdiv/tmod`).

`Test/Compile/EndToEnd.lean` (arithmetic): `0≤x²`, `(x-1)²≥0`, `0≤|x|` (`IfThenElse`) →
`unsat`; `x<5` → `sat` + replay; `(x*y)/y=x` → `unsat` under `y≠0`.

Symbolic-`Data` validators (live): `equalsData d d` → `unsat`; `unIData d == unIData d`
under `isI d` → `unsat`; `equalsData d (iData 42)` → `sat` with `(= d (mkI 42))` and verified
`bigEval` replay (d=7 → false, d=42 → true).

`Test/Compile/BoundedRec.lean` (bounded model checking, live): `sum i = if i≤0 then 0 else
i + sum (i-1)` built with the call-by-value Z combinator, symbolic `i`.  Unrolling frontier
tracks the fuel exactly — F=40 ⇒ `defined` on i∈[0,3], F=80 ⇒ i∈[0,8] — and the SMT value
equals the `bigEval` ground truth `i(i+1)/2` wherever `defined`.  z3: `0≤sum(i)` is `unsat`
(proven) under `0≤i≤3` (within depth), and `sat` (no claim) under unbounded `0≤i`.

## Module layout

```
Moist/Smt/Syntax.lean        -- SmtSort (int/bool/data/bytes), BinOp, UnOp, SmtExpr, sortOf
Moist/Smt/Semantics.lean     -- typed Model, total evalSmt (+ evalUop), Unsat, evalSmt_sort
Moist/Smt/Print.lean         -- toSMTLIB (+ Data datatype, division define-funs), z3_sound, z3 IO
Moist/Compile/SymValue.lean  -- SymVal (sCon/sConst/…/sIte deferred choice), SymEnv, SymOut
Moist/Compile/Builtins.lean  -- smtBuiltin, concrete fold, pass-through (IfThenElse→sIte), symEvalBuiltin
Moist/Compile/Compile.lean   -- symEval (mirror of bigEval), combineIte (sIte unroll), extract
Moist/Compile/Adequacy.lean  -- γ, the agreements, symEval_adequate     ← the core proof
Moist/Compile/Reflect.lean   -- encodeProperty, validator_sound          ← the product
Test/Compile/{Smoke,Diff,EndToEnd,DataEndToEnd,BoundedRec}.lean
```

## Remaining (genuinely open / out of decidable scope)

- The **7 `Value` builtins** (`InsertCoin`/`LookupCoin`/`ScaleValue`/`UnionValue`/
  `ValueContains`/`ValueData`/`UnValueData`, CIP-0138) — the vendored CEK *stubs* them (no
  `evalBuiltinConst` clause), so there is no trusted reference semantics.  Unlike crypto they
  have definite computational meaning and cannot be soundly modelled as uninterpreted;
  fabricating a semantics would corrupt the TCB.  They refuse soundly (CEK refuses ⇒ symbolic
  refuses).  Supporting them requires first giving the reference CEK a faithful Value semantics.
- `unMapData` (→ `list (pair data data)`) and the builtin *constructors*
  (`constrData`/`mkPairData`) — deferred (the empty-list reconstruction is sort-ambiguous under
  the sort-erased `svalToConst`; a sort-tagged `L`/`Model` lifts this later).
- Symbolic-`Data` `Case`/`chooseData` into *lazy* (function) branches — R1, refused.
- *Unbounded* verification — proving a property at **every** recursion depth (not just up to
  the unrolled fuel) needs k-induction / loop invariants — R2, a separate effort.  Bounded
  unrolling (above) covers verification and bug-finding up to any chosen depth.
- Crypto/hashes — the pure-Lean `evalBuiltinConst` doesn't implement them, so there is no
  CEK behaviour to agree with (both refuse); modelling them as uninterpreted functions would
  require a separate, weaker spec.
```
