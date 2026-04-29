import Lean

open Lean

def parseName (s : String) : Name :=
  s.splitOn "." |>.foldl (init := Name.anonymous) Name.str

def constNames (env : Environment) : Std.HashSet Name :=
  env.constants.fold (init := {}) fun s n _ => s.insert n

def isDirectChildOf (parent n : Name) : Bool :=
  let ps := parent.components
  let ns := n.components
  ns.length == ps.length + 1 && ps.isPrefixOf ns

def looksInternal (n : Name) : Bool :=
  let cs := n.components.map Name.toString
  cs.any fun s =>
    s.startsWith "_private"
    || s.startsWith "_aux"
    || s.startsWith "match_"
    || s.startsWith "proof_"

def main (args : List String) : IO Unit := do
  let [targetStr] := args
    | throw <| IO.userError
        "usage: lake env lean --run Moist/Verified/Test.lean Moist.Verified.Foo"

  let target := parseName targetStr

  let baseEnv ← importModules #[] {}
  let baseNames := constNames baseEnv
  let env ← importModules #[target] {}

  for (name, constInfo) in env.constants.toList do
    if !baseNames.contains name
       && isDirectChildOf target name
       && !looksInternal name then
      match constInfo with
      | .thmInfo info =>
          IO.println s!"{name} : {info.type}"
      | _ => pure ()
