import Lean

/-!
For `check_lean_public_imports.py`: the modules whose declarations each given
module's declarations use, as Lean sees them.

  lake env lean --run ../ci/lean_module_uses.lean (public | private | names) MOD...

`public`: what Lean checks as public uses, which need a `public import`: the
statements of the declarations an importer sees, and the bodies of exposed
definitions, followed into the auxiliary declarations elaboration splits off
them (a proof field becomes a private `_proof_N`). `lake shake` reads only the
exported data, where those proofs are references to the auxiliary
declarations, and so counts their uses as private. `private`: every
declaration, proofs of theorems too. Prints one JSON object, module ->
modules used (its own declarations' modules left out). `names`: each module's
exported declarations' names, read from its `.olean` alone.
-/

open Lean

def valueOf? : ConstantInfo → Option Expr
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/-- The constants `ci`'s type uses, and its value's if `body`. -/
def usedBy (ci : ConstantInfo) (body : Bool) : Array Name :=
  ci.type.getUsedConstants ++ (if body then ((valueOf? ci).map (·.getUsedConstants)).getD #[] else #[])

/-- The modules each of `mods`' own declarations use: at the private level,
every declaration in full; for `publicView`, what Lean checks as public (see
above). All of `mods` are loaded together, once per level. -/
unsafe def usesOf (mods : Array Name) (publicView : Bool) : IO (Array (Name × Array String)) := do
  let imports := mods.map ({ module := · })
  -- The importer's view: which declarations are exported, and which with a
  -- body. Each module's own exported `.olean` says it: read just those, not
  -- their imports.
  let mut exported : Std.HashMap Name (Array (Name × Bool)) := {}
  if publicView then
    for mod in mods do
      let (data, region) ← readModuleData (← findOLean mod)
      exported := exported.insert mod <| data.constants.map fun ci =>
        (ci.name, (valueOf? ci).isSome && !ci.isTheorem)
      region.free
  let env ← importModules imports {} (level := .private)
  try
    let mut result := #[]
    for mod in mods do
      let some idx := env.getModuleIdx? mod | throw <| IO.userError s!"{mod} was not loaded"
      let exp := exported.getD mod #[]
      let exportedNames : Std.HashSet Name := exp.foldl (fun s (c, _) => s.insert c) {}
      -- Declarations to read, and whether their body counts.
      let mut todo : Array (Name × Bool) :=
        if publicView then exp else env.header.moduleData[idx.toNat]!.constNames.map (·, true)
      let mut seen : Std.HashSet Name := {}
      let mut out : Std.HashSet Name := {}
      while h : 0 < todo.size do
        let (c, body) := todo.back
        todo := todo.pop
        if seen.contains c then continue
        seen := seen.insert c
        let some ci := env.find? c | continue
        for u in usedBy ci body do
          let some j := env.getModuleIdxFor? u | continue
          if j != idx then
            out := out.insert env.header.moduleNames[j.toNat]!
          else if publicView && body && (u.isInternal || !exportedNames.contains u) then
            -- An auxiliary declaration of `mod` that an exposed body was split
            -- into (`_proof_N`, exported as a statement only, or not at all):
            -- Lean checked it as part of that body, so it counts in full. A
            -- theorem of its own (not internal) has a private proof.
            todo := todo.push (u, true)
      result := result.push (mod, out.toArray.map toString |>.qsort (· < ·))
    return result
  finally
    env.freeRegions

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  if args.head? == some "names" then
    let mut out : Array (String × Json) := #[]
    for m in args.tail do
      let (data, region) ← readModuleData (← findOLean m.toName)
      out := out.push (m, toJson (data.constNames.map toString))
      region.free
    IO.println (Json.mkObj out.toList).compress
    return 0
  let publicView ← match args.head? with
    | some "public" => pure true
    | some "private" => pure false
    | _ => throw <| IO.userError "usage: lean_module_uses.lean (public | private | names) MOD..."
  let res ← usesOf (args.tail.toArray.map String.toName) publicView
  IO.println (Json.mkObj (res.toList.map fun (m, us) => (m.toString, toJson us))).compress
  return 0
