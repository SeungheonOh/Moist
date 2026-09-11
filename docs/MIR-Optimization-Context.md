# MIR optimization: execution and invariant map

Historical source map from the initial audit; line references and pass details
may have changed. See [MIR optimization maintenance](MIR-Optimization.md) for
the maintained entry points and invariants.

This is the source-level context record for the optimization audit. Findings,
regressions, proof limitations, and implementation proposals are maintained
separately in `docs/MIR-Optimization-Audit.md:1`.

## Boundary and shared assumptions

The callers are `Moist/Onchain/Compile.lean:40` and
`Moist/Ptah/Compile.lean:18`. They translate to MIR, optimize, perform
pre-lowering cleanup, and lower to UPLC. Public MIR entry points also accept
hand-built expressions; optimizer analyses cannot assume frontend typing.

Every function record below inherits these five assumptions unless explicitly
strengthened. They are semantic preconditions, not conclusions from a test run.

- A1: input expressions are finite MIR trees. Runtime argument shapes and
  applications need not be type-correct; failed applications are observations.
- A2: free variables, when present, are supplied by a lexical environment of
  already-evaluated values. An unbound reference instead fails lowering.
- A3: VarId identity includes both origin and UID; hints are diagnostic.
  Source and generated identifiers sharing a UID are different variables.
- A4: Let bindings are sequential and nonrecursive. A binder scopes over the
  remaining bindings and body, not its own RHS. Valid Fix has an outer Lam.
- A5: execution is call-by-value and left-to-right. Results, errors, divergence,
  and logging are distinct concerns; resource costs require a separate budget
  model rather than an assumption about unbounded reachability.

MIR rewrites return immutable trees. Only FreshM computations update a local
fresh counter; none of these passes performs network calls, persistent writes,
or runtime logging. Returned `changed` flags describe rewrite activity, not
semantic equivalence or budget improvement.

Three external-boundary considerations apply throughout:

- The pure Lean CEK and pinned Zig evaluator are separate implementations;
  agreement on one fixture is not a proof that their builtin semantics match.
- The pure CEK step relation omits an execution budget and does not accumulate
  Trace messages. The test harness observes actual Trace execution separately.
- Foreign evaluators, readback, and golden costs are test oracles with their own
  assumptions. No optimizer theorem is inferred merely from a successful FFI
  call or a changed snapshot.

## 1. Identity, scope, and substitution

**Purpose:** `Expr.alphaEq` supports fixed-point comparison without treating
fresh spelling as a change. `subst` and `renameLet` implement lexical replacement
used by beta reduction, inlining, recursion lowering, and simultaneous renaming.

**Inputs & assumptions:** expression pairs or a target VarId, replacement Expr,
and expression; A1–A5; substitution additionally needs a fresh supply disjoint
from identifiers in both input and replacement. Simple `rename` requires the
replacement name not to capture another binder.

**Outputs & effects:** Boolean equality, or a replacement tree and updated fresh
state; no evaluation of the replacement; free identities outside the target
remain lexical references.

**Blocks and ordering:**
- Alpha comparison enters paired binders before their bodies, but compares Let
  RHSs before extending environments. First principles: lexical depth, not UID
  equality, distinguishes bound occurrences from free ones.
- Substitution replaces a matching Var; leaves atoms unchanged; recursively
  visits strict and deferred children without evaluating them. Why recurse into
  delays? Their future environment still determines replacement semantics.
- A binder equal to the target stops descent into its scope. If it intersects
  replacement free variables, allocate a fresh binder before recursing. How is
  capture avoided? Rename the original scope, not the replacement's variables.
- For Let, substitute the current RHS first; then stop, rename, or recurse based
  on binder identity and capture. `renameLet` threads the suffix and body together
  and stops at a later rebinding. Why not map RHSs independently? Their scopes
  differ at each sequential binder.
- `renameMany` first maps free sources to fresh temporaries, then temporaries to
  destinations. How are swaps preserved? The second phase cannot rewrite an
  original source occurrence belonging to another pair.

**Invariants:** nearest-binder lookup; nonrecursive RHS scope; no accidental
capture when the freshness precondition holds.

**Dependencies:** `Moist/MIR/Expr.lean:176`,
`Moist/MIR/Analysis.lean:416`, `Moist/MIR/Analysis.lean:530`,
`Moist/MIR/Optimize/CaseMerge.lean:15`; freeVars supplies capture checks,
freshVar supplies names, and node-count lemmas justify recursive substitution.

## 2. Binder preparation and fresh state

**Purpose:** `uniqueOptimizationBinders` establishes the global binder convention
needed when scopes move or a suffix is processed as separate expressions.
`reserveFreshFor` ensures later monadic allocation cannot reuse an existing UID.

**Inputs & assumptions:** Expr and, for reservation, FreshState; A1–A5; a local
renaming environment represents only dominating lexical binders.

**Outputs & effects:** an alpha-renamed tree or the original tree; a monotone
fresh counter for reservation; no changes to free identifiers or Let flags.

**Blocks and ordering:**
- `wellScoped` checks all binders against previous binders and root free names.
  A passing tree is returned unchanged. First principles: freshness is an
  identity property, not a claim that a program is closed or well-typed.
- Otherwise, freshening starts above the maximum UID. Lambda/Fix binders extend
  the renaming environment only for their bodies. How are mixed origins handled?
  Source lookup uses full VarId equality; newly allocated names are generated.
- Let freshening transforms the RHS under the old environment, allocates the
  binder, then transforms the suffix. Why this order? A Let is not recursive.
- Reservation takes the maximum of the existing counter and input maximum plus
  one. Why preserve the existing counter? Other allocated names may not occur
  in the current subtree. How does this compose? Callers reserve prepared trees,
  not only their pre-renaming inputs.

**Invariants:** free identities preserved; unique output binders; reserved
state never moves backward.

**Dependencies:** `Moist/MIR/Optimize/Safety.lean:24`; wellScoped/freeVars,
maxUidExpr, and freshVar; scope-moving entry points and lowerExpr consume these
invariants. Replacing an expression can duplicate binders, so later boundaries
check again rather than assuming uniqueness forever.

## 3. Purity and builtin value protocol

**Purpose:** `isPure` recognizes guaranteed successful, nonlogging evaluation
under A2. `builtinRemainder` and `isCallableValue` establish the more specific
value-shape evidence needed by eta and CSE without changing purity's contract.

**Inputs & assumptions:** Expr and the checked-in expectedArgs table; A1–A5;
type-force and term-argument positions are distinct states of builtin evaluation.

**Outputs & effects:** Bool or optional remaining argument protocol; no fresh
allocation, program execution, or change to the expression.

**Blocks and ordering:**
- Atoms, lambdas, and delays are pure allocations/lookups. Error is not pure;
  App, Case, and Fix are conservatively rejected. First principles: syntactic
  construction and execution of a closure are different operations.
- Let and Constr require every evaluated child to be pure. How are failures
  retained? Any unproved child rejects the whole purity claim.
- Force of Delay checks the body; other forces check both forceability and
  evaluation purity. Why both? A value can exist without being forceable.
- builtinRemainder accepts a builtin, consumes Force only at argQ, and consumes
  App only at argV with a pure argument. The final argument has no remaining
  protocol. Why distinguish saturation? Builtin execution can fail on types.
- isCallableValue accepts a Lam or an unsaturated builtin expecting argV.
  How are unknown variables handled? They remain unknown, even when their
  spelling resembles a function or their frontend source type was functional.

**Invariants:** purity implies no modeled failure/logging; every consumed
protocol step matches its kind; callable evidence excludes delays and unknowns.

**Dependencies:** `Moist/MIR/Optimize/Purity.lean:33`,
`Moist/MIR/Optimize/Safety.lean:9`, `Moist/CEK/Builtins.lean:28`;
DCE/FloatOut/Inline consume purity, eta consumes callable evidence, CSE consumes
the protocol plus logging information.

## 4. Evaluation frontier

**Purpose:** `firstEvaluationUse` determines whether evaluation reaches a target
occurrence before any unproved computation. Its result complements occurrence
counting: unique use alone says nothing about when that use occurs.

**Inputs & assumptions:** target VarId and Expr; A1–A5; callers separately check
single occurrence and their binder convention.

**Outputs & effects:** Bool; no rewriting, state change, or evaluation; false
means no established frontier fact, not proof that the variable is unused.

**Blocks and ordering:**
- A matching Var succeeds. App first checks its function; it checks the argument
  only when the function is pure. First principles: function evaluation precedes
  argument evaluation, but application itself follows both.
- Force follows its operand, and Case follows only its scrutinee. Why not an
  alternative? Selection and field application intervene before branch uses.
- Constr scans fields left-to-right, proceeding only past pure fields. How are
  traces ordered? A possibly logging earlier field stops the scan.
- Let checks the current RHS, then proceeds only across a pure RHS and a
  nonshadowing binder. Why inspect RHS before the binder? Its scope is older.
- Deferred nodes and unrelated leaves return false. How is a delayed use
  distinguished? The traversal never crosses Lam, Fix, or Delay boundaries.

**Invariants:** no unknown computation crossed; no deferred occurrence accepted;
sequential shadowing respected.

**Dependencies:** `Moist/MIR/Optimize/Safety.lean:108`; isPure establishes safe
predecessors, countOccurrences supplies multiplicity, and Inline/PreLower use
the result only with their other guards.

## 5. ANF normalization and flattening

**Purpose:** ANF gives evaluated non-atomic operands names so subsequent passes
can reason about sharing and strict order. Flattening exposes nested strict Lets
without making their private names capture later expressions.

**Inputs & assumptions:** Expr, and FreshState for the public wrapper; A1–A5;
the core worker needs a disjoint fresh supply, supplied by anfNormalizeFlat.

**Outputs & effects:** normalized Expr; the public wrapper advances its caller's
counter; no evaluator calls or runtime effects.

**Blocks and ordering:**
- App normalizes function then argument and emits their bindings in that order.
  Force names its operand; Case names the scrutinee but keeps alternatives
  inside Case. First principles: only selected alternatives execute.
- Constr processes fields in order. Let normalizes RHSs before its body; Lam,
  Fix, and Delay recurse structurally without moving work across their wrappers.
  How is strictness retained? Generated Let bindings stand at the original
  operand's evaluation position.
- The flat wrapper alpha-renames Lets for Fix-free input; otherwise that step
  is skipped. Core normalization uses a new supply above the resulting tree.
  Why not trust the caller's seed? Existing identifiers may be larger.
- flattenReadyCheck tests hoisted names against the body and later RHSs.
  flattenAll checks every Let before hoisting. How is flattening bounded?
  Structural recursion handles the input tree; a failed guard preserves the Let.
- anfNormalize raises the caller's state above its output. Why synchronize?
  Its internally allocated names must be reserved for the following pass.

**Invariants:** operand evaluation order; no unconditional alternative
evaluation; flattening requires a passed scope check.

**Dependencies:** `Moist/MIR/ANF.lean:61`, `Moist/MIR/ANF.lean:218`;
alphaRenameTop, maxUidExpr, and freeVars; optimize and verifiedOptimize both
call the public self-contained wrapper.

## 6. Beta reduction

**Purpose:** `betaReducePass` exposes immediately applied lambdas as substitution
or strict Let bindings. It prepares work for ANF without assuming a non-atomic
argument is duplicable or safe to skip.

**Inputs & assumptions:** Expr and FreshState; A1–A5; entry preparation supplies
the binder and freshness conditions required by substitution.

**Outputs & effects:** Expr/change flag and advanced state; non-atomic argument
evaluation remains explicit; no runtime evaluation is performed by the pass.

**Blocks and ordering:**
- Prepare binders and reserve the prepared maximum before descending. Why
  reserve after preparation? Preparation may create larger identifiers.
- For App, transform both children, then inspect the function shape. First
  principles: only an actual Lam is a syntactic beta redex in untyped MIR.
- An atomic argument is substituted. A non-atom becomes a one-binding Let.
  How is an unused error preserved? The Let still evaluates its RHS.
- All other compound forms rebuild transformed children in original order;
  leaves are unchanged. Why bottom-up? Inner redexes can expose a Lam head.

**Invariants:** one evaluation of non-atomic arguments; lambda body scope
retained; no beta rewrite of an unknown function.

**Dependencies:** `Moist/MIR/Optimize/BetaReduce.lean:46`; Safety prepares names,
subst performs replacement, ANF exposes resulting Lets to later passes.

## 7. Float-out

**Purpose:** `floatOut` moves independent pure allocations outside repeated
lambda execution and exposes allocations from alternatives to later sharing.
It changes where work is allocated, not the order of impure computations.

**Inputs & assumptions:** Expr; A1–A5; the public wrapper supplies globally
unique binders, and isPure supplies safe speculation evidence.

**Outputs & effects:** Expr/change flag; pure bindings may run more eagerly;
runtime CPU/memory costs can therefore change even when values do not.

**Blocks and ordering:**
- Partition each binding list left-to-right into float and stay sets. A binding
  floats only if pure and independent of crossed binders and earlier stay names.
  First principles: a definition cannot move outside a dependency's scope.
- Lam crosses its parameter; valid Fix crosses both function and parameter
  while retaining the outer Lam. How is recursion scope retained? References
  to either crossed name force the binding to stay.
- Case recursively processes alternatives and collects only exposed leading
  pure Lets. Why only their heads? Parameter-dependent work remains under Lam.
- Let flattens a transformed body using the established name convention.
  Delay recursively optimizes its body without moving bindings outside Delay.
  How are deferred effects retained? No Delay-boundary hoist is performed.
- Other nodes preserve shape and evaluation order. Why traverse bottom-up?
  Independent bindings can emerge one lexical level at a time.

**Invariants:** purity at every hoist; no dependency on trapped binders;
mandatory Fix lambda retained.

**Dependencies:** `Moist/MIR/Optimize/FloatOut.lean:218`; partitionBindings,
freeVars, isPure, and uniqueOptimizationBinders; CSE may reuse hoisted results,
but a cost model must assess the extra speculation separately.

## 8. Known-constructor case specialization

**Purpose:** `caseMergePass` replaces a Case only when it knows the scrutinee's
actual constructor representation. Constructor facts are derived from values,
not inferred from the number of lambda parameters in an alternative.

**Inputs & assumptions:** Expr and an internal list of dominating constructor
facts; A1–A5; CEK constant decomposition defines tag, fields, and constructor
count restrictions for constant cases.

**Outputs & effects:** Expr/change flag; field evaluation can become explicit
Lets; entry and exit restore binder uniqueness without executing a constructor.

**Blocks and ordering:**
- knownConstructor accepts an available Var fact, atomic-field Constr, or
  decomposable literal. Other forms give no fact. Why atomic fields for facts?
  A dominating binding has already evaluated them to values.
- Direct Constr cases bind every non-atomic field before choosing the result,
  even when selection yields Error. First principles: field evaluation precedes
  case selection in CEK.
- selectAlternative checks constant constructor-count limits and tag presence,
  then applies exactly the field list with ordinary App. How is arity handled?
  Under- and over-application follow normal machine behavior.
- Let facts flow left-to-right; Lam/Fix and new Let binders invalidate facts
  depending on rebound names. Why invalidate dependencies as well as result
  names? A stored field reference must retain its original environment.
- Alternatives receive the same incoming facts but do not export new ones.
  How is dominance retained? Conditional bindings never enter a sibling's map.

**Invariants:** factual tag/field evidence; all strict fields retained; no
constructor fact survives a changed lexical dependency.

**Dependencies:** `Moist/MIR/Optimize/CaseMerge.lean:31`,
`Moist/CEK/Machine.lean:78`; constType reifies fields, Safety prepares names,
normal App lowering supplies field application semantics.

## 9. Repeatability and CSE

**Purpose:** `isRepeatable` distinguishes computations whose reevaluation cannot
log from those whose effects are unknown. CSE uses that evidence to replace an
alpha-equivalent expression with a previously evaluated dominating result.

**Inputs & assumptions:** Expr and seen expression/result pairs; A1–A5; seen
entries must dominate the current point, and public traversal establishes the
global name convention used by replacement.

**Outputs & effects:** Bool analysis or Expr/change flag; duplicate bindings can
disappear; unknown calls and forces remain explicit without runtime execution.

**Blocks and ordering:**
- availableHead follows aliases with fuel and preserves App/Force spine shape.
  Why fuel? Malformed or externally supplied maps must not loop the analysis.
- Values and explicit Error are repeatable; Constr/Let require all evaluated
  pieces repeatable. First principles: if the first evaluation errors, execution
  cannot reach a sequential duplicate; logging is different.
- Force accepts a known Delay body only if its execution is repeatable, or a
  proven pure builtin force. App requires a repeatable argument and either a
  known lambda with pure body or correctly staged non-Trace builtin head.
  How are aliases of logging code treated? Shape resolution cannot bypass the
  body/protocol and Trace checks; unresolved heads are rejected.
- CSE recursively processes an RHS before lookup. A passing repeatability check
  permits alpha-equivalent lookup; success replaces uses and drops the duplicate.
  Why lookup after recursion? Child sharing may expose a duplicate.
- Otherwise register the RHS only when it does not depend on its own binder;
  invalidate shadowed results/dependencies. Nested scopes inherit filtered maps
  but never export conditional or deferred bindings. How is dominance retained?
  Maps flow inward and sequentially, never from one branch to another.

**Invariants:** matching expression plus repeatability required; reused result
dominates every replacement; changed dependencies invalidate entries.

**Dependencies:** `Moist/MIR/Optimize/Safety.lean:65`,
`Moist/MIR/Optimize/CSE.lean:139`; alphaEq compares binding structure,
rename relies on prepared names, and the builtin protocol/logging classification
is tied to the selected CEK implementation.

## 10. Dead-code elimination

**Purpose:** DCE removes unused bindings only when evaluating their RHS is known
to succeed without logging. It exposes transitive dead chains by considering
the already-filtered suffix rather than the original suffix.

**Inputs & assumptions:** Expr, binding list, and body; A1–A5; isPure is a
conservative totality/effect predicate, not merely absence of mutable state.

**Outputs & effects:** Expr/change flag; removed pure allocations need not run;
all impure bindings retain their original order, with no fresh allocation.

**Blocks and ordering:**
- dce recursively simplifies children before handling a Let list. Why bottom-up?
  Removing an inner dead use can make an outer binding dead.
- filterBindings recursively filters the tail, then computes its free variables.
  First principles: only uses in surviving code keep a definition live.
- Keep a binding when live or impure; otherwise omit it. How are transitive
  dependencies preserved? A retained impure RHS contributes free uses to earlier
  decisions, while a dropped pure RHS does not.
- Rebuild a nonempty list or unwrap an empty Let. Why preserve list order?
  Evaluation order is part of the contract. How is shadowing handled? freeVars
  uses sequential scope, rather than summing raw name occurrences.

**Invariants:** no impure binding removed; live dependencies retained; surviving
bindings keep relative order.

**Dependencies:** `Moist/MIR/Optimize/DCE.lean:71`; freeVarsLet handles scope,
isPure supplies erasure evidence, ANF supplies named opportunities. Recomputing
suffix free variables affects compiler complexity, not this semantic criterion.

## 11. Inlining

**Purpose:** `inlinePassWithCanon` exposes a safe entry around an invariant-based
recursive worker. `shouldInline` separates semantic eligibility from size and
recursive-growth heuristics.

**Inputs & assumptions:** Expr/FreshState, or worker binding list, retained
prefix, body, and changed flag; A1–A5; raw workers require unique binders and a
fresh supply covering both the original tree and inserted replacements.

**Outputs & effects:** Expr/change flag and state; eligible bindings are
substituted into the suffix/body; no runtime execution or trace emission.

**Blocks and ordering:**
- The entry preserves an already wellScoped tree, otherwise canonicalizes it,
  then reserves its maximum. How does split suffix processing remain lexical?
  It relies on this established global binder convention.
- The recursive worker simplifies RHSs and the body before inlineLetGo walks
  bindings left-to-right. First principles: the later code used for decisions
  must be the same code that receives substitution.
- Atoms are eligible without a size limit. Values/pure expressions use the
  threshold or unique-use/nonrecursive condition. Why allow deferred pure uses?
  Pure evaluation has no error or logging outcome to postpone.
- Impure non-values require exactly one occurrence, no deferred occurrence,
  and firstEvaluationUse. How is ordering preserved? Potentially effectful
  predecessors reject eligibility rather than merely checking strictness.
- On acceptance, substitute body and remaining RHSs, retaining prefix order;
  otherwise retain the binding. Atomic beta reduction follows transformed App
  children. Why not substitute arbitrary beta arguments here? That could change
  multiplicity or defer argument evaluation.

**Invariants:** worker name preconditions established at entry; impure work has
one frontier occurrence; retained bindings maintain strict order.

**Dependencies:** `Moist/MIR/Optimize/Inline.lean:188`,
`Moist/MIR/Optimize/Inline.lean:254`,
`Moist/MIR/Optimize/Inline.lean:344`; countOccurrences/occursInDeferred,
firstEvaluationUse, subst, and canonicalize are coupled. The proof-facing worker
and production entry have different preconditions.

## 12. Eta reduction

**Purpose:** Eta removes a lambda layer whose only action is forwarding its
argument to a proven callable value. It does not assume arbitrary untyped heads
are functions or that their evaluation is effect-free.

**Inputs & assumptions:** Expr; A1–A5; isCallableValue establishes the relevant
head shape and successful allocation protocol.

**Outputs & effects:** Expr/change flag; no fresh names; an eligible wrapper is
removed without evaluating unknown or saturated heads.

**Blocks and ordering:**
- Recursively transform a lambda body, then match exactly `Lam x (App f (Var x))`.
  First principles: a forwarding layer passes that argument in that position.
- Require x absent from f and f callable; otherwise retain the wrapper. Why the
  free-variable guard? Removing x's binder must not free a captured occurrence.
- Revisit a reduced result for further eligible layers. How is argument order
  retained? Each layer consumes one syntactically matching trailing application,
  rather than reversing a collected parameter list.
- Valid Fix traverses beneath its outer Lam without eta-reducing that mandatory
  wrapper. Why a separate case? Lowering's recursive representation requires it.
- Other constructors retain their wrappers and recurse. How is forcing behavior
  retained? A Delay or unknown Var never substitutes for a Lam under this gate.

**Invariants:** matching argument identity; free-variable exclusion; callable
head and Fix shape requirements.

**Dependencies:** `Moist/MIR/Optimize/EtaReduce.lean:21`; freeVars,
isCallableValue, and alphaEq; lowerFix consumes the retained Lam structure.

## 13. Force-delay cancellation

**Purpose:** ForceDelay removes explicit thunk creation/forcing pairs and follows
let-bound delays when every use is a force. It preserves the number and locations
of executions of the delayed body.

**Inputs & assumptions:** Expr; A1–A5; the entry establishes unique binders for
the raw replacement helper, whose free variables must not be captured.

**Outputs & effects:** Expr/change flag; delay bindings can become dead for DCE;
replacements can duplicate syntax but are not evaluated by the compiler.

**Blocks and ordering:**
- A direct Force(Delay body) returns the recursively transformed body. First
  principles: constructing a delay is distinct from executing its body once.
- Other Force operands recurse first, then retry the direct shape. Why retry?
  A child transformation may expose a Delay.
- Let recursively processes RHSs and body before scanning delay bindings.
  It requires a real occurrence and allUsesAreForce on the remaining scope.
  How are bare values retained? Any bare use rejects through-let cancellation.
- replaceForceVar substitutes only Force(Var target), stopping at shadowing
  binders; the public convention prevents other binders capturing the body.
  Why retain the original binding? DCE removes it only after all uses disappear.
- All other forms preserve structural order. How is repeated forcing handled?
  Each original force site receives one body copy, not one shared evaluation.

**Invariants:** only actual force sites execute substituted bodies; no bare use
loses its Delay; lexical closure environment preserved.

**Dependencies:** `Moist/MIR/Optimize/ForceDelay.lean:88`; allUsesAreForce,
replaceForceVar, countOccurrences, and uniqueOptimizationBinders; DCE cleans dead
bindings and subsequent boundaries recheck names after syntax duplication.

## 14. Pre-lowering cleanup

**Purpose:** PreLower removes administrative bindings and selected beta redexes
immediately before structural UPLC translation. It deliberately retains strict
bindings when moving their RHS would cross potentially effectful computation.

**Inputs & assumptions:** Expr and optional starting index; A1–A5; its public
wrapper establishes name/fresh-state preconditions for recursive substitution.

**Outputs & effects:** Expr; an internal advanced fresh state is discarded by
the wrapper; no evaluator or external effects.

**Blocks and ordering:**
- The wrapper prepares names and takes the maximum of requested start and input
  maximum plus one. Why seed after preparation? Freshened binders also reserve UIDs.
- App transforms children and considers Lam beta reduction only at zero/one
  use. Zero use drops only pure arguments; one use accepts values, pure arguments,
  or a frontier use. First principles: deleting a binding must not delete its
  argument's observable execution.
- Let atoms substitute unconditionally, zero-use pure RHSs drop, and single-use
  non-atoms require value/pure/frontier evidence. Otherwise keep the binding.
  How is sequential shadowing checked? usesInScope wraps the entire suffix/body.
- Substitution recurses into the resulting tree; other nodes rebuild children.
  Why revisit? One redex can expose another. How are duplicate effects avoided?
  Multi-use non-atoms do not enter this substitution path.

**Invariants:** impure evaluation not deleted; single-use movement remains at
the evaluation frontier; multi-use non-atoms retain sharing.

**Dependencies:** `Moist/MIR/Optimize/PreLower.lean:57`; subst, countOccurrences,
isPure, and firstEvaluationUse; compile callers lower this result directly.

## 15. Driver, fixed point, and trace

**Purpose:** The optimizer composes local passes in an order that exposes
opportunities without relying on their changed flags as a proof. The trace
driver records the same transformations for inspection.

**Inputs & assumptions:** Expr/FreshState, loop fuel, and optional seed; A1–A5;
individual pass preconditions must be reestablished when earlier passes duplicate
binders or allocate names.

**Outputs & effects:** Expr and updated state, or an array of pass snapshots;
bounded iteration; no actual CEK execution or Trace logging.

**Blocks and ordering:**
- optimize reserves input, floats, beta-reduces, normalizes to ANF, then floats
  again. Why a second float? ANF introduces new explicit allocations.
- simplifyOnce runs hygienic ANF, known-constructor cases, CSE, DCE, safe inlining,
  beta, eta, and ForceDelay. First principles: each new expression is the input
  to the next pass, so local name and effect invariants must compose.
- simplifyLoop returns immediately at zero fuel. Otherwise it compares the
  result by origin-aware alpha equivalence and recurses only on structural change.
  Why not OR changed flags? Flags may report preparatory activity or omit mere
  renaming. How is nonconvergence bounded? maxOptIterations is 20.
- optimizeTrace mirrors this order and records snapshots and reported flags.
  How is diagnostic parity checked? A regression compares its final expression
  against optimizeExpr, modulo alpha equivalence.
- optimizeDebugBeta intentionally stops after initial beta/ANF; convenience
  wrappers merely seed FreshM. Why distinguish it? It is not full optimization.

**Invariants:** declared pass order; nondecreasing fresh state; bounded outer
iteration independent of changed flags.

**Dependencies:** `Moist/MIR/Optimize.lean:50`,
`Moist/MIR/Optimize.lean:80`, `Moist/MIR/Optimize.lean:124`; all pass entries,
Expr.alphaEq, and ANF state synchronization; compiler callers add PreLower/Lower.

## 16. Lowering and semantic oracles

**Purpose:** lowerExpr converts named lexical MIR into de Bruijn UPLC and exposes
unbound-variable or invalid-Fix failures. The audit evaluates that UPLC rather
than inventing a second MIR semantics shaped around the rewrites.

**Inputs & assumptions:** Expr, requested seed, and recursive lexical environment;
A1–A5; the environment order is nearest binder first and UPLC indices are one-based.

**Outputs & effects:** Except String Term; local fresh state for Fix expansion;
no UPLC execution until a separate evaluator is invoked.

**Blocks and ordering:**
- Var searches the lexical environment and fails if absent; Lam extends it;
  ordinary constructors recursively translate without reordering. First
  principles: named shadowing must become nearest de Bruijn lookup.
- Let translates its RHS under the old environment and the suffix under the new
  binder, emitting Apply(Lam suffix, RHS). Why this encoding? CEK argument
  evaluation preserves the strict nonrecursive binding.
- Fix requires Lam, allocates Z-combinator support names, substitutes recursive
  calls, and lowers the expansion. How are captured outer variables protected?
  lowerExpr seeds above all input UIDs and subst handles lexical scope.
- CEK Case decomposes actual constructor values/constants and pushes field
  application frames; builtin application checks its remaining protocol.
  Why inspect these callees? They determine arity and strictness, not MIR types.
- Tests step the pure CEK and record actual final Trace invocation frames.
  How are timeouts treated? They fail bounded tests, rather than becoming an
  asserted semantic error. The separate cycle theorem reasons about every step.

**Invariants:** nearest-binder indexing; strict Let encoding; actual runtime
constructor/builtin protocol determines application behavior.

**Dependencies:** `Moist/MIR/Lower.lean:38`, `Moist/CEK/Machine.lean:93`,
`Test/MIR/Opt/Soundness.lean:31`; subst expands Fix, CEK builtins define primitive
execution, readback exposes values. Foreign evaluator and resource-model limits
remain the external-boundary considerations listed at the beginning.

## Model corrections retained during the audit

- `wellScoped` means the global binder convention, not merely lexical validity
  or absence of free variables. This distinction determines which raw helpers
  need preparation and which can directly handle shadowing.
- ANF's public entry is already self-seeding and synchronizes the caller's
  counter. Freshness analysis must inspect that wrapper, not just anfAtom.
- isPure is more conservative than several historical comments and tests:
  applications and cases are rejected, irrespective of builtin names.
- Case fields are runtime values supplied through ordinary application. Branch
  lambda count is not a constructor declaration.
- The proof relation and executable budgeted evaluators describe different
  state spaces. Proof dependencies and budget behavior are assessed separately
  in the findings report.
