import Test.MIR.FuzzReal.Run

/-! # Shrinking a discrepancy on the real machine

Given a program, one argument list and the name of a variant whose result
disagrees with the unoptimized `base` lowering on the plutus-core machine,
greedily replace subterms (by `error`, unit, `0`, `False`, or one of their
own children) and drop let bindings while the disagreement persists, and
report the smallest program found together with the first pipeline stage
(`pipe/*`) that shows the disagreement. -/

namespace Test.MIR.FuzzReal.Shrink

open Moist.MIR
open Moist.Plutus.Term
open Test.MIR.FuzzReal

def harness : IO String := do
  return (← IO.getEnv "CROSS_BENCH").getD
    "/Users/sho/fun/plinth-plutarch-comparison/dist-newstyle/build/aarch64-osx/ghc-9.6.6/plinth-plutarch-paper-code-0.1.0.0/x/cross-bench/opt/build/cross-bench/cross-bench"

/-- Outcome and canonical value of terms on the real machine. -/
def runReal (semantics : String) (jobs : List (String × Term × List Argument)) :
    IO (List (String × String × String)) := do
  let input := String.join (jobs.map fun (id, term, arguments) =>
    s!"{id}\t{flatHex term}\t{",".intercalate (arguments.map (·.field))}\n")
  let limits : Limits := {}
  let output ← IO.Process.output {
    cmd := ← harness, args := #["batch", "--semantics", semantics, "--cpu", toString limits.cpu,
      "--mem", toString limits.mem] } (some input)
  return output.stdout.splitOn "\n" |>.filterMap fun line =>
    match line.splitOn "\t" with
    | id :: outcome :: _ :: _ :: result :: _ => some (id, outcome, result)
    | _ => none

/-- A deliberately unsound transformation (every `error` becomes unit), the
    variant `selftest`, to check the shrinker itself. -/
partial def errorsToUnit : Expr → Expr
  | .Error => unitE
  | .Lam v body => .Lam v (errorsToUnit body)
  | .Fix v body => .Fix v (errorsToUnit body)
  | .Force body => .Force (errorsToUnit body)
  | .Delay body => .Delay (errorsToUnit body)
  | .App f x => .App (errorsToUnit f) (errorsToUnit x)
  | .Constr tag fields => .Constr tag (fields.map errorsToUnit)
  | .Case s alts => .Case (errorsToUnit s) (alts.map errorsToUnit)
  | .Let bindings body => .Let (bindings.map fun (v, e, f) => (v, errorsToUnit e, f)) (errorsToUnit body)
  | e => e

/-- `some description` when `variant` breaks the contract against `base`. -/
def disagreement (semantics : String) (program : Expr) (arguments : List Argument)
    (variant : String) : IO (Option String) := do
  let thunks := variantThunks program ++
    [("selftest", fun (_ : Unit) => lowerExpr (errorsToUnit program))]
  let some (_, baseThunk) := thunks.find? (·.1 == "base") | return none
  let some (_, variantThunk) := thunks.find? (·.1 == variant) | return none
  let .ok base := baseThunk () | return none
  match variantThunk () with
  | .error message => return some s!"compile error: {message}"
  | .ok term =>
    let results ← runReal semantics [("base", base, arguments), ("variant", term, arguments)]
    let some (_, baseOutcome, baseValue) := results.find? (·.1 == "base") | return none
    let some (_, outcome, value) := results.find? (·.1 == "variant") | return none
    if baseOutcome == "OK" && (outcome != "OK" || value != baseValue) then
      return some s!"base OK {baseValue}, {variant} {outcome} {value}"
    if baseOutcome == "FAIL" && outcome != "FAIL" then
      return some s!"base FAIL, {variant} {outcome} {value}"
    return none

/-- Every one-step reduction of the node at preorder index `target`. -/
def reductions (e : Expr) : List Expr :=
  let children : List Expr := match e with
    | .Lam _ body | .Fix _ body | .Force body | .Delay body => [body]
    | .App f x => [f, x]
    | .Constr _ fields => fields
    | .Case s alts => s :: alts
    | .Let bindings body => body :: bindings.map (·.2.1)
    | _ => []
  let dropped : List Expr := match e with
    | .Let bindings body =>
      (List.range bindings.length).map fun i =>
        let rest := bindings.eraseIdx i
        if rest.isEmpty then body else .Let rest body
    | .Case s alts => if alts.length > 1 then [.Case s alts.dropLast] else []
    | _ => []
  let leaves : List Expr := match e with
    | .Error => []
    | .Lit _ => [.Error]
    | _ => [.Error, unitE, intE 0, boolE false]
  dropped ++ children ++ leaves

partial def replaceAt (target : Nat) (replacement : Expr) (e : Expr) : StateM Nat Expr := do
  let index ← get
  set (index + 1)
  if index == target then return replacement
  match e with
  | .Lam v body => return .Lam v (← replaceAt target replacement body)
  | .Fix v body => return .Fix v (← replaceAt target replacement body)
  | .Force body => return .Force (← replaceAt target replacement body)
  | .Delay body => return .Delay (← replaceAt target replacement body)
  | .App f x => return .App (← replaceAt target replacement f) (← replaceAt target replacement x)
  | .Constr tag fields => return .Constr tag (← fields.mapM (replaceAt target replacement))
  | .Case s alts => return .Case (← replaceAt target replacement s) (← alts.mapM (replaceAt target replacement))
  | .Let bindings body =>
    let bindings ← bindings.mapM fun (v, rhs, flag) => do return (v, ← replaceAt target replacement rhs, flag)
    return .Let bindings (← replaceAt target replacement body)
  | e => return e

partial def nodeAt (target : Nat) (e : Expr) : StateM Nat (Option Expr) := do
  let index ← get
  set (index + 1)
  if index == target then return some e
  let children : List Expr := match e with
    | .Lam _ body | .Fix _ body | .Force body | .Delay body => [body]
    | .App f x => [f, x]
    | .Constr _ fields => fields
    | .Case s alts => s :: alts
    | .Let bindings body => bindings.map (·.2.1) ++ [body]
    | _ => []
  for child in children do
    if let some found ← nodeAt target child then return some found
  return none

/-- Greedy shrinking; returns the smallest program and its disagreement. -/
partial def shrink (semantics : String) (program : Expr) (arguments : List Argument)
    (variant : String) (description : String) : IO (Expr × String) := do
  let mut current := program
  let mut current_description := description
  let mut progress := true
  while progress do
    progress := false
    let size := Mutate.countNodes current
    for target in List.range size do
      let some node := ((nodeAt target current).run' 0) | continue
      for candidate in reductions node do
        let next := (replaceAt target candidate current).run' 0
        if Mutate.countNodes next >= Mutate.countNodes current then continue
        if (lowerTotalExpr [] next).isNone then continue
        if let some found ← disagreement semantics next arguments variant then
          current := next
          current_description := found
          progress := true
          break
      if progress then break
  return (current, current_description)

/-- Shrink, then report the stages of the production pipeline that disagree. -/
def report (semantics : String) (program : Expr) (arguments : List Argument) (variant : String) :
    IO Unit := do
  let some description ← disagreement semantics program arguments variant | do
    IO.println s!"no disagreement of {variant} under semantics {semantics}"
  IO.println s!"disagreement: {description}"
  let (small, smallDescription) ← shrink semantics program arguments variant description
  IO.println s!"shrunk ({Mutate.countNodes program} -> {Mutate.countNodes small} nodes): {smallDescription}"
  IO.println (pretty small)
  IO.println s!"arguments: {arguments.map (·.shown)}"
  IO.println s!"repr: {repr small}"
  for (name, _) in variantThunks small do
    if name != "base" then
      if let some found ← disagreement semantics small arguments name then
        IO.println s!"  {name}: {found}"

end Test.MIR.FuzzReal.Shrink
